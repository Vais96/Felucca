/* SPDX-License-Identifier: GPL-3.0-only
 * Copyright (C) 2026 Leo Kuroshita (@kurogedelic), Hügelton Instruments */
/* Felucca 1.2: the SEQ TOOLS layer's actions (ui_layer.c: SEQ held, on every page). Included by ui_layer.c. The white
 * keys from F3 (TL_*):
 *   F3 CLEAR  G3 REVERSE  A3 SHIFT <  B3 SHIFT >       the whole sequence
 *   C4 RANDOM D4 COOK     E4 BOOM BAP     F4 EUCLID      new / a little changed (EUCLID: 1.5.5, BOOM BAP: below)
 *   G4 CLEAR  A4 REVERSE  B4 FILL  C5 RANDOM             the selected lane (DRUM: ui.lane, black keys 1..8 pick it)
 *   D5 DOUBLE E5 HALF                                    LEN x2 / half (1.5.5, below)
 * Each works on the selected track's steps 1..LEN (the steps past LEN stay) and is one undo: SAVE held swaps back
 * the copy taken just before it (ui.c undo, UNDO_PAT; unlike a load the track's automation stays), so after a few
 * COOKs SAVE held takes back the last one only; the layer's OCT- puts back the track as the layer opened (tl_open).
 * A step that held something and is empty after loses its locks (as EDIT's step clear); REVERSE and SHIFT move the
 * steps' automation and locks with them. RANDOM and COOK draw from libc.c rng(): no seed is kept, each press
 * differs. A sequence of ties reversed keeps its note first: N T T -> N T T at the mirrored place */
enum { TL_CLEAR, TL_REV, TL_LEFT, TL_RIGHT, TL_RANDOM, TL_COOK, TL_BEAT, TL_EUCLID, TL_LCLR, TL_LREV, TL_LFILL, TL_LRND,
       TL_DOUBLE, TL_HALF, TL_N };

/* the track as the layer opened (OCT-): in the pool (RAM's .bss is tight), taken by layer_opened */
static struct { step_t step[NSTEP]; motion_store_t mo; } tl_open __attribute__((section(".pool")));

static uint32_t tl_len(const track_t *t) { return (uint32_t)clamp(t->p[P_SLEN], 1, NSTEP); }
static uint32_t tl_rnd(uint32_t n) { return n ? rng() % n : 0u; }
static int tl_gate(const step_t *s) { return s->time == ST_NOTE && s->n; }
static uint32_t tl_lane(const step_t *s, uint32_t l) { return (step_lanes(s) >> l) & 1u; }
/* place p's action is there for this track (the lane row and BEAT: DRUM only) */
static int tl_cell(const track_t *t, uint32_t p)
{
    return p < TL_N && (p <= TL_EUCLID || p >= TL_DOUBLE || drum_track(t));
}

/* the undo copy of t as it is now (ui.c load_begin, but the automation is copied and stays): one action */
static void tl_undo_take(track_t *t)
{
    uint32_t i = trk_index(t);
    undo.trk = (uint8_t)(i + 1u);
    undo.what = UNDO_PAT;
    undo.keep = 0;                                      /* (the next load or action takes its own copy) */
    undo.eng = t->eng_req;
    undo.preset = t->preset;
    undo.user = t->user;
    memcpy(undo.p, t->p, sizeof undo.p);
    memcpy(undo.step, t->step, sizeof undo.step);
    memcpy(undo.fm6, fm6_patch[i], FP_SIZE);
    undo.fm6_slot = fm6_slot[i];
    undo.pat = pat_sig[i];
    undo.from = pat_from[i];
    undo.from_h = pat_from_h[i];
    undo.patn = pat_last[i];
    motion_snapshot_track(t, &undo.motion_backup);
}

/* steps 1..len of t that are not empty (a REST); after the action the ones emptied lose their locks */
static uint64_t tl_used_of(const step_t *s, uint32_t len)
{
    uint64_t m = 0;
    uint32_t i;
    for (i = 0; i < len; i++)
        if (s[i].time != ST_REST)
            m |= (uint64_t)1 << i;
    return m;
}
static uint64_t tl_used(const track_t *t, uint32_t len) { return tl_used_of(t->step, len); }
static void tl_unlock(track_t *t, uint64_t was, uint32_t len)
{
    uint32_t i;
    for (i = 0; i < len; i++)
        if (((was >> i) & 1u) && t->step[i].time == ST_REST)
            (void)motion_clear_locks(t, i);
}

/* step j of t becomes the undo copy's step src[j] (taken just before), its automation and locks with it */
static void tl_order(track_t *t, uint32_t len, const uint8_t *src)
{
    uint8_t to[NSTEP];
    uint32_t j, k = trk_index(t), f;
    for (j = 0; j < len; j++) {
        t->step[j] = undo.step[src[j]];
        to[src[j]] = (uint8_t)j;
    }
    f = motion_guard();
    for (j = 0; j < motion.count; j++) {
        motion_event_t *e = &motion.event[j];
        if ((e->place >> 6) == k && (e->place & 63u) < len)
            e->place = (uint8_t)(k << 6 | to[e->place & 63u]);
    }
    motion_unguard(f);
}

/* REVERSE: the mirror order; a note's ties (after it) would come before it, so the note goes first again */
static void tl_reverse(track_t *t, uint32_t len)
{
    uint8_t src[NSTEP], h;
    uint32_t j, e, x;
    for (j = 0; j < len; j++)
        src[j] = (uint8_t)(len - 1u - j);
    for (j = 0; j < len; j++) {
        for (e = j; e < len && undo.step[src[e]].time == ST_TIE; e++)
            ;
        if (e == j)
            continue;
        if (e < len && undo.step[src[e]].time == ST_NOTE) {   /* ties j .. e - 1, their note at e: the note to j */
            for (h = src[e], x = e; x > j; x--)
                src[x] = src[x - 1u];
            src[j] = h;
        }
        j = e;                                          /* (past the run and its note) */
    }
    tl_order(t, len, src);
}

/* SHIFT: rotated by one step inside LEN, d = 1 later (>), len - 1 earlier (<) */
static void tl_shift(track_t *t, uint32_t len, uint32_t d)
{
    uint8_t src[NSTEP];
    uint32_t j;
    for (j = 0; j < len; j++)
        src[j] = (uint8_t)((j + len - d) % len);
    tl_order(t, len, src);
}

/* ------------------------------------------------------------- drums --- */
/* hits per 16 steps -> per len (at least one when any) */
static uint32_t tl_per(uint32_t k16, uint32_t len) { return !k16 ? 0u : k16 * len < 16u ? 1u : (k16 * len + 8u) / 16u; }
/* k hits spread evenly over len steps (euclidean: the first on step rot; mir: mirrored around it) into lane l */
static void tl_euclid(track_t *t, uint32_t len, uint32_t l, uint32_t k, uint32_t rot, uint32_t mir)
{
    uint32_t i;
    for (i = 0; k && i < len; i++)
        if ((i * k) % len < k)
            grid_hit(t, ((mir ? len - i : i) + rot) % len, l, 1);
}
static void tl_lane_clear(track_t *t, uint32_t len, uint32_t l)
{
    uint32_t i;
    for (i = 0; i < len; i++)
        grid_hit(t, i, l, 0);
}
/* lane l at random, the drum machine way: the kick 3..5 a bar (one on step 1), the snare on beats 2 and 4, the
 * closed hat 8..12, the others sparse (any: they may stay empty, RANDOM; else at least one hit, RANDOM LANE) */
static void tl_lane_rnd(track_t *t, uint32_t len, uint32_t l, int any)
{
    tl_lane_clear(t, len, l);
    if (l == DV_KICK)
        tl_euclid(t, len, l, tl_per(3u + tl_rnd(3), len), 0, tl_rnd(2));
    else if (l == DV_SNARE)
        tl_euclid(t, len, l, tl_per(2, len), 4u % len, 0);
    else if (l == DV_HATC)
        tl_euclid(t, len, l, tl_per(8u + tl_rnd(5), len), tl_rnd(2), 0);
    else if (!any || !tl_rnd(l == DV_HATO ? 2u : 3u))
        tl_euclid(t, len, l, tl_per(1u + tl_rnd(2), len), l == DV_HATO ? (2u + 4u * tl_rnd(4)) % len : tl_rnd(len), 0);
    if (l == DV_SNARE && !tl_rnd(3))
        grid_hit(t, tl_rnd(len), l, 1);                 /* (a ghost snare now and then) */
}

/* the lane hits of steps 1..len (n-th: its step and lane), the kick on step 1 not counted (it stays) */
static uint32_t tl_hit_nth(const track_t *t, uint32_t len, uint32_t n, uint32_t *ip, uint32_t *lp)
{
    uint32_t i, l, c = 0;
    for (i = 0; i < len; i++)
        for (l = 0; l < NLANE; l++)
            if (tl_lane(&t->step[i], l) && (i || l != DV_KICK) && c++ == n) {
                *ip = i;
                *lp = l;
                return 1;
            }
    return c;
}
static uint32_t tl_lane_hits(const track_t *t, uint32_t len, uint32_t l)
{
    uint32_t i, c = 0;
    for (i = 0; i < len; i++)
        c += tl_lane(&t->step[i], l);
    return c;
}
/* COOK on drums: 10..20 % of the hits (at least one) moved a step, or one added on a lane in use, or one taken
 * away (never a lane's last, never the kick on step 1). A try that cannot (the step taken, a lane's last hit) does
 * not count: another one is made (at most a few times as many) */
static uint32_t tl_cook_hit(track_t *t, uint32_t len)
{
    uint32_t i = 0, l = 0, j, r = tl_rnd(4), n = tl_hit_nth(t, len, ~0u, &i, &l);   /* (n: the count) */
    if (r == 2u || !n) {                                /* add: on a lane in use (none: the closed hat) */
        uint32_t used = 0;
        for (j = 0; j < len; j++)
            used |= step_lanes(&t->step[j]);
        for (l = DV_HATC, j = tl_rnd(NLANE); used && j < 2u * NLANE; j++)
            if ((used >> (j % NLANE)) & 1u) {
                l = j % NLANE;
                break;
            }
        j = tl_rnd(len);
        if (tl_lane(&t->step[j], l))
            return 0;
        grid_hit(t, j, l, 1);
        return 1;
    }
    tl_hit_nth(t, len, tl_rnd(n), &i, &l);
    if (r == 3u) {                                      /* take one away */
        if (tl_lane_hits(t, len, l) < 2u)
            return 0;
        grid_hit(t, i, l, 0);
        return 1;
    }
    j = (i + (tl_rnd(2) ? 1u : len - 1u)) % len;        /* move one a step on (or back) */
    if (tl_lane(&t->step[j], l))
        return 0;
    r = (step_accents(&t->step[i]) >> l) & 1u;
    grid_hit(t, i, l, 0);
    grid_hit(t, j, l, 1);
    if (r)
        grid_acc(t, j, l, 1);
    return 1;
}
static void tl_cook_drum(track_t *t, uint32_t len, uint32_t hits)
{
    uint32_t m = hits * (10u + tl_rnd(11)) / 100u, n, sig = steps_sig(t);
    for (m = m ? m : 1u, n = 4u * m + 64u; n; n--) {
        if (tl_cook_hit(t, len) && m)
            m--;
        if (!m && steps_sig(t) != sig)                  /* (a hit moved there and back: one more) */
            break;
    }
}

/* FILL LANE: each press the next of every step, every 2nd, every 4th, none (anything else: every step).
 * Returns the division now (0: cleared) */
static uint32_t tl_fill(track_t *t, uint32_t len, uint32_t l)
{
    static const uint8_t E[3] = {1, 2, 4};
    uint32_t e, i, now = 0;
    for (e = 0; e < 3u && !now; e++) {
        for (i = 0; i < len && tl_lane(&t->step[i], l) == (i % E[e] == 0u); i++)
            ;
        if (i == len)
            now = e + 1u;
    }
    e = now == 3u ? 0u : E[now % 3u];
    for (i = 0; i < len; i++)
        grid_hit(t, i, l, e && i % e == 0u);
    return e;
}

/* ----------------------------------------------------------- melodic --- */
static int32_t tl_in_scale(const track_t *t, int32_t n) { return (int32_t)((scale_mask(t) >> (uint32_t)((n - t->p[P_ROOT] + 120) % 12)) & 1u); }
/* the next note of the scale above (d 1) or below (d -1) n */
static int32_t tl_neigh(const track_t *t, int32_t n, int32_t d)
{
    uint32_t g = 12;
    do
        n += d;
    while (g-- && !tl_in_scale(t, n));
    return clamp(n, 0, 127);
}
/* RANDOM on a melodic track: the rhythm stays (the NOTE steps, their ties, accents and chance), the notes are new: a
 * walk through the track's scale (ROOT, SCL) 9 semitones either side of the pattern's middle (an empty pattern:
 * around the root near C4, on an 8th-note rhythm with some rests). A chord keeps its shape, each note snapped
 * down into the scale */
static void tl_random_notes(track_t *t, uint32_t len)
{
    uint8_t deg[20];
    int32_t c = 0, lo, d, x;
    uint32_t i, k, g = 0, nd = 0, at;
    for (i = 0; i < len; i++)
        if (tl_gate(&t->step[i])) {
            c += t->step[i].note[0];
            g++;
        }
    if (g) {
        c /= (int32_t)g;
    } else {                                            /* no rhythm: 8ths, a few rests, always step 1 */
        c = 60 + t->p[P_ROOT] % 12;
        c -= c > 66 ? 12 : 0;
        for (i = 0; i < len; i++) {
            step_clear(&t->step[i]);
            if (i % 2u == 0u && (!i || tl_rnd(4))) {
                t->step[i].time = ST_NOTE;
                t->step[i].n = 1;
                t->step[i].vel = 96;
            }
        }
    }
    for (lo = clamp(c - 9, 12, 100), x = lo; x <= lo + 18 && nd < sizeof deg; x++)
        if (tl_in_scale(t, x))
            deg[nd++] = (uint8_t)x;
    if (!nd)
        return;
    at = nd / 2u + tl_rnd(5);
    at = at >= 2u ? at - 2u : 0u;
    for (i = 0; i < len; i++) {
        step_t *s = &t->step[i];
        if (!tl_gate(s))
            continue;
        at = at >= nd ? nd - 1u : at;
        d = (int32_t)deg[at] - s->note[0];
        s->note[0] = deg[at];
        for (k = 1; k < s->n && k < 4u; k++) {
            x = clamp(s->note[k] + d, 1, 127);
            while (!tl_in_scale(t, x) && x > 1)
                x--;
            s->note[k] = (uint8_t)x;
        }
        if (!tl_rnd(6)) {                               /* a leap now and then, else a step or two */
            at = tl_rnd(nd);
        } else {
            x = (int32_t)at + (int32_t)tl_rnd(5) - 2;
            at = (uint32_t)(x < 0 ? -x : x >= (int32_t)nd ? 2 * ((int32_t)nd - 1) - x : x);
        }
    }
}

/* COOK on a melodic track: 15..25 % of the NOTE steps (at least one; more when they undid each other): a note to the
 * next scale note up or down (mostly) or an octave, an accent on / off, a chance of 50 / 75 % or back to 100 */
static void tl_cook_notes(track_t *t, uint32_t len, uint32_t g)
{
    uint32_t m = g * (15u + tl_rnd(11)) / 100u, i, k, r, n, sig = steps_sig(t), tries = 64;
    for (m = m ? m : 1u; tries-- && (m || steps_sig(t) == sig); m -= m != 0u) {   /* (undone again: one more) */
        step_t *s;
        n = tl_rnd(g);
        for (i = 0; i < len && (!tl_gate(&t->step[i]) || n--); i++)
            ;
        s = &t->step[i % NSTEP];
        r = tl_rnd(8);
        if (r == 6u) {
            s->flags ^= SF_ACCENT;
        } else if (r == 7u) {
            if (!step_cond(s))                          /* (1.5.5: a condition stays) */
                step_set_chance(s, step_chance(s) < 100u ? 100u : tl_rnd(2) ? 75u : 50u);
        } else {
            int32_t d = tl_rnd(2) ? 1 : -1, o = r == 5u ? d * 12 : 0;
            for (k = 0; k < s->n && k < 4u; k++)       /* (an octave out of 24 .. 108: a scale step instead) */
                if (s->note[k] + o < 24 || s->note[k] + o > 108)
                    o = 0;
            for (k = 0; k < s->n && k < 4u; k++)
                s->note[k] = (uint8_t)(o ? s->note[k] + o : tl_neigh(t, s->note[k], d));
        }
    }
}

/* ------------------------------------------------------------ EUCLID --- */
/* 1.5.5 (#186): F4 EUCLID: HITS spread as evenly as they go over a cycle of STEPS, turned by ROT, repeated through
 * 1..LEN. F4 opens it on the selected track: the undo copy is taken (one undo for all of it) and the pattern is written
 * at once (heard while playing); KNOB 1..3 HITS (0..STEPS) STEPS (1..LEN) ROT (0..STEPS - 1) rewrite it from that copy.
 * OCT+ (or F4 again, another tool, the layer let go) applies it, OCT- cancels it (the steps as they were; the layer's
 * own OCT- after that puts back the track as the layer opened). DRUM: the selected lane's hits (black keys 1..8 move it
 * to another lane), the other lanes and the step's own fields stay. Melodic: a hit keeps the step's own note (a NOTE
 * step as it is: its chord, accent, CHANCE, RATCH ..; a TIE: the note it holds), else the root (ROOT, near C4); the
 * other steps are emptied, but a TIE that holds a note on (its note's ties: the note keeps its length); the emptied
 * steps lose their locks when it is applied. The values stay for the next one (until the power goes). The track's steps
 * as it opened are its own copy (eu_from; the undo copy is the next load's, a MIDI Program Change or the editor's on
 * another track meanwhile), and it stays on the track it opened on */
static struct { uint8_t on, hits, steps, rot, trk; } eu;
static step_t eu_from[NSTEP] __attribute__((section(".pool")));   /* the steps as EUCLID opened (the pool: .bss is tight) */
static track_t *eu_track(void) { return &trk[eu.trk % NTRK]; }
static int eu_hit(uint32_t i)                           /* step i (0..) of the cycle repeated, turned by rot */
{
    uint32_t n = eu.steps ? eu.steps : 1u, p = (i + n - eu.rot % n) % n;
    return (p * eu.hits) % n < eu.hits;
}
/* the note a hit on step i plays: the NOTE step there, or the note a TIE there holds (its NOTE before it), else none */
static const step_t *eu_src(uint32_t i)
{
    uint32_t j = i;
    while (j && eu_from[j].time == ST_TIE)
        j--;
    return eu_from[j].time == ST_NOTE && eu_from[j].n && (j == i || eu_from[i].time == ST_TIE) ? &eu_from[j] : 0;
}
static void eu_render(track_t *t)                       /* (t: ignored, EUCLID's own track) */
{
    t = eu_track();
    uint32_t len = tl_len(t), i, l = ui.lane % NLANE;
    memcpy(t->step, eu_from, sizeof t->step);
    if (drum_track(t)) {
        for (i = 0; i < len; i++)
            grid_hit(t, i, l, eu_hit(i));
        return;
    }
    for (i = 0; i < len; i++) {
        step_t *s = &t->step[i];
        const step_t *o = eu_src(i);
        if (eu_hit(i)) {
            if (o != &eu_from[i]) {                   /* (a REST, an empty step, a TIE: a NOTE of its own) */
                int32_t r = 60 + t->p[P_ROOT] % 12;
                step_clear(s);
                s->time = ST_NOTE;
                if (o)
                    memcpy(s->note, o->note, sizeof s->note), s->n = o->n;
                else
                    s->note[0] = (uint8_t)(r > 66 ? r - 12 : r), s->n = 1;
            }
        } else if (!(s->time == ST_TIE && i && (t->step[i - 1u].time == ST_TIE || (t->step[i - 1u].time == ST_NOTE &&
                                                                                    t->step[i - 1u].n)))) {
            step_clear(s);
        }
    }
}
static void eu_fit(const track_t *t)                    /* the values inside LEN */
{
    uint32_t len = tl_len(t);
    if (!eu.steps || eu.steps > len)
        eu.steps = (uint8_t)(len < 16u ? len : 16u);
    if (eu.hits > eu.steps)
        eu.hits = eu.steps;
    eu.rot = (uint8_t)(eu.rot % eu.steps);
}
static void eu_say(void)                               /* "EUCLID 5/16" ("+2": turned) */
{
    char b[24], n[4];
    str_cpy(b, "EUCLID ", sizeof b);
    fmt_int(n, eu.hits);
    str_cpy(b + str_len(b), n, sizeof b - str_len(b));
    str_cpy(b + str_len(b), "/", sizeof b - str_len(b));
    fmt_int(n, eu.steps);
    str_cpy(b + str_len(b), n, sizeof b - str_len(b));
    if (eu.rot) {
        str_cpy(b + str_len(b), " +", sizeof b - str_len(b));
        fmt_int(n, eu.rot);
        str_cpy(b + str_len(b), n, sizeof b - str_len(b));
    }
    ui_message(b);
}
static void eu_open(track_t *t)
{
    tl_undo_take(t);
    memcpy(eu_from, t->step, sizeof eu_from);
    eu.trk = (uint8_t)trk_index(t);
    if (!eu.steps) {                                    /* (the first since the power came: 4 / 16) */
        eu.hits = 4;
        eu.rot = 0;
    }
    eu_fit(t);
    eu.on = 1;
    eu_render(t);
    eu_say();
}
static void eu_knob(track_t *t, uint32_t k, int32_t s)
{
    t = eu_track();
    if (k == 0u)
        eu.hits = (uint8_t)clamp((int32_t)eu.hits + s, 0, eu.steps);
    else if (k == 1u)
        eu.steps = (uint8_t)clamp((int32_t)eu.steps + s, 1, (int32_t)tl_len(t));
    else if (k == 2u)
        eu.rot = (uint8_t)(((int32_t)eu.rot + s % (int32_t)eu.steps + (int32_t)eu.steps) % (int32_t)eu.steps);
    else
        return;
    eu_fit(t);
    eu_render(t);
    eu_say();
}
static void eu_lane(track_t *t)                         /* DRUM: the lane moved (black keys 1..8): on that lane now */
{
    (void)t;
    if (eu.on)
        eu_render(t);
}
/* OCT+ (apply: the emptied steps lose their locks) or OCT- (cancel: the steps of the copy back) */
static void eu_close(track_t *t, int apply)
{
    uint32_t len;
    if (!eu.on)
        return;
    t = eu_track();
    len = tl_len(t);
    eu.on = 0;
    if (apply) {
        tl_unlock(t, tl_used_of(eu_from, len), len);
        return;
    }
    memcpy(t->step, eu_from, sizeof t->step);
}

/* ------------------------------------------------------- DOUBLE, HALF --- */
/* 1.5.5 (#85): D5 DOUBLE: steps 1..LEN once more after them (LEN + 1 .. 2 x LEN, at most the 64 steps: from LEN 33 on
 * only the first 64 - LEN steps fit) and LEN x2, the steps whole (notes, ties, hits, accents, CHANCE / conditions, RATCH,
 * NUDGE, VEL) with their automation and locks (a copy each; what was stored past LEN where the copy goes is replaced).
 * A note tied over the loop's end ties into the copy as it tied into step 1. E5 HALF: LEN / 2 (rounded down), the steps
 * of the second half cleared with their automation and locks (a note tied into it ends at the new LEN). Both one undo
 * (SAVE held: the steps, LEN and the automation back). DOUBLE at 64 steps and HALF at 1 do nothing (said why); DOUBLE
 * with too few of the 128 records left for the copies: AUTOMATION FULL, nothing done */
static motion_store_t tl_mo __attribute__((section(".pool")));   /* the track's records as they will be */
/* tl_mo = track t's records with steps lo..hi-1 dropped, those of steps 0..cn-1 copied by `by` steps (cn 0: none);
 * 0 = they do not fit the MOTION_MAX */
static int tl_motion_plan(track_t *t, uint32_t lo, uint32_t hi, uint32_t cn, uint32_t by)
{
    uint32_t k = trk_index(t), i, f, n = 0, ok = 1;
    f = motion_guard();
    memset(&tl_mo, 0, sizeof tl_mo);
    tl_mo.on = motion.on & (uint8_t)(1u << k);
    for (i = 0; i < motion.count; i++) {
        const motion_event_t *e = &motion.event[i];
        uint32_t s = e->place & 63u;
        if ((e->place >> 6) != k || (s >= lo && s < hi))
            continue;
        if (n < MOTION_MAX) tl_mo.event[n] = *e;
        n++;
        if (s < cn) {
            if (n < MOTION_MAX) {
                tl_mo.event[n] = *e;
                tl_mo.event[n].place = (uint8_t)(k << 6 | (s + by));
            }
            n++;
        }
    }
    if (motion.count - motion_count(t) + n > MOTION_MAX)
        ok = 0;
    tl_mo.count = (uint8_t)(n < MOTION_MAX ? n : MOTION_MAX);
    motion_unguard(f);
    return ok;
}
static uint32_t tl_nl(uint32_t len) { return 2u * len < NSTEP ? 2u * len : NSTEP; }   /* DOUBLE's LEN */
/* 0 = it cannot (said why): before the undo copy is taken */
static int tl_resize_ok(track_t *t, uint32_t p, uint32_t len)
{
    if (p == TL_DOUBLE && len >= NSTEP) {
        ui_message("64 STEPS: NO ROOM");
        return 0;
    }
    if (p == TL_HALF && len < 2u) {
        ui_message("1 STEP: NO HALF");
        return 0;
    }
    if (p == TL_DOUBLE && !tl_motion_plan(t, len, tl_nl(len), tl_nl(len) - len, len)) {
        ui_message("AUTOMATION FULL");
        return 0;
    }
    return 1;
}
static uint32_t tl_double(track_t *t, uint32_t len)      /* the new LEN */
{
    uint32_t nl = tl_nl(len), i;
    for (i = len; i < nl; i++)
        t->step[i] = t->step[i - len];
    (void)tl_motion_plan(t, len, nl, nl - len, len);
    (void)motion_replace_track(t, &tl_mo);
    t->p[P_SLEN] = (int16_t)nl;
    return nl;
}
static uint32_t tl_half(track_t *t, uint32_t len)
{
    uint32_t h = len / 2u, i;
    for (i = h; i < len; i++)
        step_clear(&t->step[i]);
    (void)tl_motion_plan(t, h, len, 0, 0);
    (void)motion_replace_track(t, &tl_mo);
    t->p[P_SLEN] = (int16_t)h;
    return h;
}

/* ---------------------------------------------------------- BOOM BAP --- */
/* E4 BOOM BAP (in BEAT's place), CRATE's: a boom-bap part on the selected track with its sound, another each press
 * (one undo: the steps, the sound and the track's values). The part is the track's number's (a DRUM track: drums):
 *   1 BASS    808 BASS (PHASE), LEN 64: on the DRUM track's kicks, each note the root of the chord the CHORDS track
 *             plays there, held to the next one, an octave up now and then, and a slide into a new bar's root from a
 *             step below.
 *   2 CHORDS  DUSTY EP (FM6), LEN 64, a new key (ROOT, MIN or now and then DOR): seventh chords on one of BB_PROG, a
 *             bar each (the last bar's second half now and then a turnaround), each voiced nearest the one before,
 *             held, stabbed or pushed (a 16th early).
 *   3 MELODY  VIBES (FM6) or FLUTE (SAMPLE), LEN 64: a one-bar motif of chord tones on one of BB_RHY,
 *             played on each bar's chord: A A B A (B: its first half and a new answer; now and then bar 2 left empty
 *             for a voice), the last note the root, held.
 *   4 DRUMS   BOOM KIT, LEN 32: two bars of BB_KICK's kicks, the snare on 2 and 4 laid back (QUANTIZE OFF, NUDGE +2)
 *             and accented, 1..2 ghost snares at 50 %, 8th hats of uneven velocity and timing, in bar 2 a hat roll
 *             (RATCH x3) and now and then an open hat, a clap on 4 or toms at the end; SWING 30..45.
 * The melodic parts take the CHORDS track's key and the DRUM track's SWING: drums, chords, then bass and melody. Each
 * part's LEVEL is BB_LEVEL's (the mix measured: the 808 held under the drums, the melody over the chords) */
enum { BB_BASS, BB_CHORDS, BB_MELODY, BB_DRUMS };
static const uint16_t BB_KICK[] = {0x0481, 0x0409, 0x0501, 0x2481, 0x0605, 0x0285};   /* bit i: a kick on step i + 1 */
static const uint16_t BB_RHY[] = {0x1249, 0x0494, 0x4141, 0x0889, 0x0A44};             /* a motif's onsets */
static const uint8_t BB_PROG[][4] = {{0, 5, 2, 6}, {0, 3, 6, 2}, {0, 0, 5, 4}, {1, 4, 0, 0}, {0, 6, 5, 4}, {5, 4, 0, 0},
                                     {0, 3, 0, 4}};                                    /* scale degrees, a bar each */
static uint8_t bb_prog;                                 /* the progression the last chords took (RAM only) */
static const uint8_t BB_LEVEL[4] = {100, 104, 0, 108};     /* LEVEL by part: -6, -4 dB, (the melody's sound's), -2 dB */
typedef struct { int32_t root; uint32_t mask; } bb_key_t;

static bb_key_t bb_key(void)                            /* the CHORDS track's key (CHR: minor) */
{
    bb_key_t k = {trk[BB_CHORDS].p[P_ROOT], scale_mask(&trk[BB_CHORDS])};
    if (k.mask == 0xFFFu)
        k.mask = SCALE_MASK[2];
    return k;
}
static int32_t bb_deg(bb_key_t k, int32_t d)            /* scale degree d (0.., any octave) -> semitones above ROOT */
{
    uint32_t c[12], n = 0, i;
    int32_t o;
    for (i = 0; i < 12u; i++)
        if ((k.mask >> i) & 1u)
            c[n++] = i;
    o = d >= 0 ? d / (int32_t)n : -((-d + (int32_t)n - 1) / (int32_t)n);
    return (int32_t)c[d - o * (int32_t)n] + 12 * o;
}
static const track_t *bb_drum(void)                     /* the first DRUM track, 0 none */
{
    uint32_t i;
    for (i = 0; i < NTRK; i++)
        if (drum_track(&trk[i]))
            return &trk[i];
    return 0;
}
/* t to engine e's preset `name` (inside the action's undo copy: tl_do holds undo_depth) */
static void bb_sound(track_t *t, const engine_t *e, const char *name)
{
    uint32_t ei, i;
    for (ei = 0; ei < NENGINES && ENGINES[ei] != e; ei++)
        ;
    for (i = 0; ei < NENGINES && i < e->npresets && !str_eq(e->presets[i].name, name); i++)
        ;
    if (ei == NENGINES || i == e->npresets)
        return;
    if (t->eng_req != ei)
        set_engine_of(t, ei);
    apply_preset_to(t, i);
}
/* the chord on step i: the notes of the CHORDS track sounding there (its NOTE before, LEN wrapping), else the
 * progression's -> out (low first), their number */
static uint32_t bb_harm(uint32_t i, uint8_t *out)
{
    const track_t *c = &trk[BB_CHORDS];
    uint32_t j, k, n, cl = tl_len(c);
    bb_key_t key;
    for (j = 0; !drum_track(c) && j < cl; j++) {
        const step_t *s = &c->step[(i % cl + cl - j) % cl];
        if (s->time == ST_NOTE && s->n) {
            n = s->n < 4u ? s->n : 4u;
            for (k = 0; k < n; k++) {                   /* (sorted: a hand-made chord may be any order) */
                uint8_t x = s->note[k];
                int32_t m = (int32_t)k - 1;
                for (; m >= 0 && out[m] > x; m--)
                    out[m + 1] = out[m];
                out[m + 1] = x;
            }
            return n;
        }
    }
    key = bb_key();
    for (n = 0; n < 4u; n++)
        out[n] = (uint8_t)(48 + key.root + bb_deg(key, BB_PROG[bb_prog][(i / 16u) % 4u] + 2 * (int32_t)n));
    return 4;
}
/* step i a NOTE of n notes held len steps (TIEs after it, inside 64) */
static void bb_put(track_t *t, uint32_t i, const int32_t *note, uint32_t n, uint32_t len, uint32_t vel)
{
    uint32_t k;
    step_t *s = &t->step[i % NSTEP];
    step_clear(s);
    s->time = ST_NOTE;
    s->n = (uint8_t)n;
    for (k = 0; k < n; k++)
        s->note[k] = (uint8_t)clamp(note[k], 1, 127);
    s->vel = (uint8_t)vel;
    for (k = 1; k < len && i + k < NSTEP; k++) {
        step_clear(&t->step[i + k]);
        t->step[i + k].time = ST_TIE;
    }
}
static void bb_clear(track_t *t, uint32_t len)
{
    uint32_t i;
    for (i = 0; i < NSTEP; i++)
        step_clear(&t->step[i]);
    t->p[P_SLEN] = (int16_t)len;
}

static void bb_drums(track_t *t)
{
    static const uint8_t GHOST[] = {7, 9, 11, 15};      /* off 16ths without a hat */
    uint32_t nk = NELEM(BB_KICK), k0 = tl_rnd(nk), k1 = (k0 + 1u + tl_rnd(nk - 1u)) % nk, ghost = 0, i;
    uint32_t clap = !tl_rnd(3), toms = !tl_rnd(3), roll = 0;
    bb_sound(t, &ENG_DRUM, "BOOM KIT");
    bb_clear(t, 32);
    t->p[P_SQNT] = 0;                                   /* QUANTIZE OFF: the NUDGEs play */
    t->p[P_SSWING] = (int16_t)(30u + tl_rnd(16));
    for (i = 0; i < 2u; i++)
        ghost |= 1u << GHOST[tl_rnd(sizeof GHOST)];
    for (i = 0; i < 32u; i++) {
        uint32_t b = i % 16u, bar = i / 16u, kb = BB_KICK[bar ? k1 : k0] | 1u, kick = (kb >> b) & 1u;
        step_t *s = &t->step[i];
        if (kick)
            grid_acc(t, i, DV_KICK, 1);
        if (b == 4u || b == 12u) {
            grid_acc(t, i, DV_SNARE, 1);
            if (clap && b == 12u)
                grid_hit(t, i, DV_CLAP, 1);
        }
        if (b % 2u == 0u)
            grid_hit(t, i, bar && b == 14u && !tl_rnd(2) ? DV_HATO : DV_HATC, 1);
        if ((ghost >> b) & 1u && !kick) {
            grid_hit(t, i, DV_SNARE, 1);
            step_set_chance(s, 50);
        }
        if (bar && toms && (b == 13u || b == 15u) && !kick)
            grid_hit(t, i, DV_TOM, 1);
        if (bar && !roll && (b == 10u || b == 6u) && !kick) {
            step_set_ratchet(s, 3);                     /* a hat roll before the turn */
            roll = 1;
        }
        if (s->time == ST_NOTE) {
            s->vel = (uint8_t)(b % 4u == 0u ? 72u + tl_rnd(14) : 50u + tl_rnd(22));
            step_set_nudge(s, b == 4u || b == 12u ? 2 : (b & 1u) ? 1 : kick ? 0 : (int32_t)tl_rnd(3) - 1);
        }
    }
}

static void bb_chords(track_t *t)
{
    int32_t prev[4] = {0, 0, 0, 0}, tone[4], best[4], c[4], cost, bc, v, o, m, x;
    uint32_t style = tl_rnd(3), split = !tl_rnd(2), ev, k;
    bb_key_t key;
    bb_sound(t, &ENG_FM6, "DUSTY EP");
    bb_clear(t, 64);
    t->p[P_ROOT] = (int16_t)tl_rnd(12);
    t->p[P_SCALE] = (int16_t)(tl_rnd(3) ? 2 : 3);       /* MIN, now and then DOR */
    bb_prog = (uint8_t)tl_rnd(NELEM(BB_PROG));
    key = bb_key();
    for (ev = 0; ev < 5u; ev++) {                       /* a chord a bar, the 5th: bar 4's second half */
        uint32_t at = 16u * ev, len = 16, deg;
        if (ev == 4u && !split)
            break;
        if (ev == 4u) {
            at = 56;
            len = 8;
            deg = BB_PROG[bb_prog][3] == 4u ? 6u : 4u;  /* the turnaround: v (or VII after a v) */
        } else {
            deg = BB_PROG[bb_prog][ev];
            if (ev == 3u && split)
                len = 8;
        }
        for (m = 0; m < 4; m++)
            tone[m] = 48 + key.root + bb_deg(key, (int32_t)deg + 2 * m);
        for (bc = 1 << 30, v = 0; v < 4; v++)           /* the inversion and octave nearest the chord before */
            for (o = -12; o <= 0; o += 12) {
                for (m = 0; m < 4; m++)
                    c[m] = tone[m] + o + (m < v ? 12 : 0);
                for (m = 1; m < 4; m++)                 /* (low first) */
                    for (x = m; x > 0 && c[x - 1] > c[x]; x--) { int32_t y = c[x]; c[x] = c[x - 1]; c[x - 1] = y; }
                if (c[0] < 50 || c[3] > 79)
                    continue;
                for (cost = 0, m = 0; m < 4; m++)
                    cost += ev ? (c[m] > prev[m] ? c[m] - prev[m] : prev[m] - c[m]) : (c[0] > 55 ? c[0] - 55 : 55 - c[0]);
                if (cost < bc) {
                    bc = cost;
                    memcpy(best, c, sizeof best);
                }
            }
        memcpy(prev, best, sizeof prev);
        if (style == 0u) {                              /* held, the last 8th of it resting */
            bb_put(t, at, best, 4, len - 2u, 92);
        } else if (style == 1u) {                       /* stabs */
            static const uint8_t AT[] = {0, 6, 10};
            for (k = 0; k < 3u && AT[k] < len; k++)
                bb_put(t, at + AT[k], best, 4, 2, k ? 78u + tl_rnd(12) : 96u);
        } else {                                        /* pushed: a 16th early (the first on its 1) */
            bb_put(t, at ? at - 1u : 0u, best, 4, len - 3u, 90);
        }
        t->step[at ? (style == 2u ? at - 1u : at) : 0u].flags |= SF_ACCENT;
    }
}

static void bb_bass(track_t *t)
{
    const track_t *d = bb_drum();
    uint32_t dl = d ? tl_len(d) : 16u, kicks = 0, i, j, hit[64];
    bb_sound(t, &ENG_PHASE, "808 BASS");
    bb_clear(t, 64);
    t->p[P_GLIDE] = 22;                                 /* (the slides' glide) */
    for (i = 0; d && i < dl; i++)
        kicks |= (step_lanes(&d->step[i]) >> DV_KICK) & 1u;
    for (i = 0; i < 64u; i++)
        hit[i] = kicks ? (step_lanes(&d->step[i % dl]) >> DV_KICK) & 1u : (BB_KICK[0] >> (i % 16u)) & 1u;
    for (i = 0; i < 64u; i++) {
        uint8_t ch[4];
        int32_t note;
        uint32_t next, vel = i % 16u ? 92u + tl_rnd(14) : 118u;
        if (!hit[i])
            continue;
        for (next = i + 1u; next < 64u && !hit[next]; next++)
            ;
        bb_harm(i, ch);
        note = 36 + ch[0] % 12;
        if (i % 16u >= 8u && !tl_rnd(4))
            note += 12;                                 /* an octave up now and then */
        if (next < 64u && next / 16u != i / 16u && next - i <= 6u && !tl_rnd(2)) {
            bb_harm(next, ch);                          /* the last before a new bar: a step below its root, sliding up */
            note = 36 + ch[0] % 12 - (tl_rnd(2) ? 1 : 2);
            note += note < 36 ? 12 : 0;
            bb_put(t, i, &note, 1, next - i, vel);
            t->step[i].flags |= SF_SLIDE;
            continue;
        }
        j = next - i < 8u ? next - i : 8u;              /* held to the next one (an 808) */
        bb_put(t, i, &note, 1, j, vel);
    }
}

static void bb_melody(track_t *t)
{
    static const char *const SND[2] = {"VIBES", "FLUTE"};
    static const engine_t *const ENG[2] = {&ENG_FM6, &ENG_SAMPLE};
    static const uint8_t LVL[2] = {120, 106};           /* (+4, -3 dB: FLUTE sounds 7 dB over VIBES) */
    uint32_t rhy = BB_RHY[tl_rnd(NELEM(BB_RHY))], nb = 0, on[16], bar, k, rest2 = !tl_rnd(2), r = tl_rnd(2);
    int32_t mot[16], ans[16], m = 2 + (int32_t)tl_rnd(3);
    bb_sound(t, ENG[r], SND[r]);
    bb_clear(t, 64);
    t->p[P_LEVEL] = LVL[r];
    for (k = 0; k < 16u; k++)
        if ((rhy >> k) & 1u)
            on[nb++] = k;
    for (k = 0; k < nb; k++) {                          /* the motif: chord tones (index 0..6: tone k % 4, k / 4 up) */
        mot[k] = m;
        ans[k] = clamp(m + (int32_t)tl_rnd(5) - 2, 0, 6);
        m = clamp(m + (int32_t)tl_rnd(5) - 2, 0, 6);
    }
    for (bar = 0; bar < 4u; bar++) {
        if (bar == 1u && rest2)
            continue;                                   /* room for a voice */
        for (k = 0; k < nb; k++) {
            uint8_t ch[4];
            uint32_t at = 16u * bar + on[k], end = bar == 3u && k + 1u == nb;
            uint32_t len = (k + 1u < nb ? on[k + 1] : 16u) - on[k];
            int32_t idx = end ? 4 : bar == 2u && k >= nb / 2u ? ans[k] : mot[k], note;   /* (the end: the root, up) */
            bb_harm(at, ch);
            note = 60 + ch[idx % 4] % 12;
            note += (note < 65 ? 12 : 0) + 12 * (idx / 4);
            bb_put(t, at, &note, 1, end || len <= 3u ? len : 3u, 84u + tl_rnd(20));
        }
    }
}

static const char *bb_do(track_t *t)
{
    const track_t *d = bb_drum();
    uint32_t role = drum_track(t) ? (uint32_t)BB_DRUMS : trk_index(t) % 4u;
    static const char *const MSG[4] = {"BOOM BAP BASS", "BOOM BAP CHORDS", "BOOM BAP MELODY", "BOOM BAP DRUMS"};
    if (role == BB_DRUMS)
        bb_drums(t);
    else if (role == BB_CHORDS)
        bb_chords(t);
    else if (role == BB_BASS)
        bb_bass(t);
    else
        bb_melody(t);
    if (role != BB_DRUMS && d)
        t->p[P_SSWING] = d->p[P_SSWING];
    if (role != BB_MELODY)
        t->p[P_LEVEL] = BB_LEVEL[role];
    return MSG[role];
}

/* ------------------------------------------------------------ actions --- */
/* the action of place p on track t (lane l): its message; 0 = nothing done (said why) */
static const char *tl_do(track_t *t, uint32_t p, uint32_t l)
{
    static char b[24];
    uint32_t len = tl_len(t), i, n = 0;
    uint64_t was = tl_used(t, len);
    int drum = drum_track(t);
    const char *msg = 0;
    l %= NLANE;
    if ((p == TL_DOUBLE || p == TL_HALF) && !tl_resize_ok(t, p, len))
        return 0;
    if (p == TL_COOK) {                                 /* (nothing there: nothing to cook, no undo copy) */
        for (i = 0; i < len; i++)
            n += drum ? (uint32_t)__builtin_popcount(step_lanes(&t->step[i])) : (uint32_t)tl_gate(&t->step[i]);
        if (!n) {
            ui_message("NOTHING TO COOK");
            return 0;
        }
    }
    tl_undo_take(t);
    switch (p) {
    case TL_CLEAR:
        for (i = 0; i < len; i++)
            step_clear(&t->step[i]);
        msg = "SEQUENCE CLEARED";
        break;
    case TL_REV: tl_reverse(t, len); msg = "REVERSED"; break;
    case TL_LEFT: tl_shift(t, len, len - 1u); msg = "SHIFTED LEFT"; break;
    case TL_RIGHT: tl_shift(t, len, 1u); msg = "SHIFTED RIGHT"; break;
    case TL_RANDOM:
        if (drum) {
            for (i = 0; i < len; i++)
                step_clear(&t->step[i]);
            for (i = 0; i < NLANE; i++)
                tl_lane_rnd(t, len, i, 1);
            msg = "RANDOM BEAT";
        } else {
            tl_random_notes(t, len);
            msg = "RANDOM NOTES";
        }
        break;
    case TL_COOK:
        if (drum)
            tl_cook_drum(t, len, n);
        else
            tl_cook_notes(t, len, n);
        msg = "COOKED";
        break;
    case TL_DOUBLE:
    case TL_HALF:
        str_cpy(b, p == TL_DOUBLE ? "DOUBLED: " : "HALVED: ", sizeof b);
        fmt_int(b + str_len(b), (int32_t)(p == TL_DOUBLE ? tl_double(t, len) : tl_half(t, len)));
        str_cpy(b + str_len(b), " STEPS", sizeof b - str_len(b));
        return b;                                       /* (nothing emptied inside the new LEN: no unlock) */
    case TL_BEAT:                                       /* (the sound loads inside this undo copy) */
        undo.what |= UNDO_SOUND;
        undo_depth++;
        msg = bb_do(t);
        undo_depth--;
        break;
    default:                                            /* the lane's */
        str_cpy(b, drum_lane_name(t, l), sizeof b);
        if (p == TL_LCLR) {
            tl_lane_clear(t, len, l);
            msg = " CLEARED";
        } else if (p == TL_LREV) {
            for (i = 0; i < len; i++) {
                const step_t *s = &undo.step[len - 1u - i];
                grid_hit(t, i, l, tl_lane(s, l));
                if (tl_lane(s, l))
                    grid_acc(t, i, l, (step_accents(s) >> l) & 1u);
            }
            msg = " REVERSED";
        } else if (p == TL_LFILL) {
            n = tl_fill(t, len, l);
            msg = n == 1u ? " EVERY STEP" : n == 2u ? " EVERY 2ND" : n ? " EVERY 4TH" : " CLEARED";
        } else {
            tl_lane_rnd(t, len, l, 0);
            msg = " RANDOM";
        }
        str_cpy(b + str_len(b), msg, sizeof b - str_len(b));
        msg = b;
        break;
    }
    tl_unlock(t, was, len);
    return msg;
}
