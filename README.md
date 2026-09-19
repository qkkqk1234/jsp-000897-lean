# JSP-000897 — Lean 4 formalization

**Problem.** At the corresponding Turán edge threshold, must some vertex
neighbourhood contain sufficiently many edges? (Erdős' problem **#1079**; Erdős:
*"if true this would be a nice generalisation of Turán's theorem"*.)

**Result formalized.** For every finite simple graph, every `n` and every `r ≥ 1`:
if `e(G) > ex(n; K_{r+2})` then some vertex `v` has

* `n · d(v) > 2 · ex(n; K_{r+2})` — the `d ≫_r n` of the original phrasing — and
* more than `ex(d(v); K_{r+1})` edges inside its neighbourhood,

and `v` may be taken of maximum degree (Bondy's refinement).

The recorded question's literal `≥`/`≥` reading is covered too
(`JSP897.dense_neighbourhood_maxDegree_ge`: at least `ex(n;K_{r+2})` edges gives a
maximum-degree vertex with at least `ex(d;K_{r+1})` edges in its neighbourhood).

**Not formalized.** One thing: the uniqueness clause — that the only graph with
`e(G) = ex(n; K_{r+2})` and every neighbourhood at its threshold is the Turán graph
`T_{r+1}(n)`. See `STATEMENT.md`.

## Headline theorem

`JSP897.dense_neighbourhood_large_degree` (`JSP897/Headline.lean`):

```lean
theorem dense_neighbourhood_large_degree (r : ℕ) (hr : 0 < r)
    (hm : turanNumber (Fintype.card V) (r + 1) < #G.edgeFinset) :
    ∃ v : V, 2 * turanNumber (Fintype.card V) (r + 1) < Fintype.card V * G.degree v ∧
      turanNumber (G.degree v) r < #((G.induce (G.neighborSet v)).edgeFinset)
```

`mathlib`'s `turanNumber n r` is `ex(n; K_{r+1})`, so the formal `r` is the recorded
`r` minus `2`; `r = 1` is Mantel's theorem (`JSP897.dense_neighbourhood_one`).

## Two routes

| Route | File | Generality |
|---|---|---|
| maximum-degree argument (strategy credited to Bondy; the proof here is **our reconstruction** — his paper was not consulted, see `STATEMENT.md`) | `JSP897/Bondy.lean` | all `n`, all `r` — this is the headline result |
| Goodman counting (Erdős–Sós 1983, read in the original) | `JSP897/Main.lean` | partial: `r ≤ 6` (at most seven parts), or `r + 1 ∣ n` |

The second route is partial, and shares the counting core with the first; it is
included because it is the one proof we have a source for.

## Layout

| File | Contents |
|---|---|
| `JSP897/Arithmetic.lean` | `2 p · ex(n;p) + s (p-s) = (p-1) n²` |
| `JSP897/Counting.lean` | ordered-triangle counting (shared with the JSP-000840 development) |
| `JSP897/Neighbourhood.lean` | handshake inside a set; Goodman's bound |
| `JSP897/Join.lean` | `T_r(d)` joined to `k` independent vertices: `(r+1)`-colourable, hence `ex(d;K_{r+1}) + d k ≤ ex(d+k;K_{r+2})` |
| `JSP897/Bondy.lean` | the maximum-degree argument |
| `JSP897/Main.lean` | the Erdős–Sós counting route |
| `JSP897/Headline.lean` | the headline statements |
| `JSP897/Audit.lean` | kernel cross-checks, non-vacuity witness, axiom audit |

## Verification

```
lake exe cache get
lake build JSP897
```

Pinned: Lean `v4.34.0`; `mathlib` `5ed2965256430c3649e86755f9576b54eca72435`
(tag `v4.34.0`), all transitive revisions in `lake-manifest.json`.

`scripts/verify.sh` runs a clean build, greps the sources for `sorry`, `admit`,
`native_decide`, `unsafe`, `implemented_by` and custom `axiom` declarations, and
re-runs the axiom audit. Every theorem in the development depends on exactly
`[propext, Classical.choice, Quot.sound]`. `evidence/verify.log` is the unedited
transcript of one such run; the two "not found in the cache" lines it contains are
`lake exe cache get` reporting two uncached mathlib oleans out of 8906, which the
build then compiles — they do not affect the pinned revisions.

## Submitter

GitHub: [@qkkqk1234](https://github.com/qkkqk1234)
