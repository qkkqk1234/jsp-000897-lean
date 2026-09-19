# Statement fidelity — JSP-000897

## The problem as recorded

> At the corresponding Turán edge threshold, must some vertex neighbourhood contain
> sufficiently many edges?

This is Erdős' problem **#1079**, stated there as:

> Let `r ≥ 4`. If `G` is a graph on `n` vertices with at least `ex(n; K_r)` edges,
> must `G` contain a vertex with degree `d ≫_r n` whose neighbourhood contains at
> least `ex(d; K_{r-1})` edges?

with solution credited to

> B. Bollobás, A. Thomason, *Dense neighbourhoods and Turán's theorem*,
> J. Combin. Theory Ser. B **31** (1981), 111–114,

independently to Erdős–Sós, and with the refinement

> J. A. Bondy, *Large dense neighbourhoods and Turán's theorem*,
> J. Combin. Theory Ser. B **34** (1983), 109–111,

that the vertex may be taken of maximum degree. Erdős: *"if true this would be a
nice generalisation of Turán's theorem."*

## Formal statement

`JSP897.dense_neighbourhood_large_degree` in `JSP897/Headline.lean`:

```lean
theorem dense_neighbourhood_large_degree (r : ℕ) (hr : 0 < r)
    (hm : turanNumber (Fintype.card V) (r + 1) < #G.edgeFinset) :
    ∃ v : V, 2 * turanNumber (Fintype.card V) (r + 1) < Fintype.card V * G.degree v ∧
      turanNumber (G.degree v) r < #((G.induce (G.neighborSet v)).edgeFinset)
```

and Bondy's refinement, `JSP897.dense_neighbourhood_maxDegree`:

```lean
theorem dense_neighbourhood_maxDegree (r : ℕ) (hr : 0 < r) (v : V)
    (hv : ∀ w : V, G.degree w ≤ G.degree v)
    (hm : turanNumber (Fintype.card V) (r + 1) < #G.edgeFinset) :
    turanNumber (G.degree v) r < #((G.induce (G.neighborSet v)).edgeFinset)
```

The recorded statement's literal `≥`/`≥` reading is
`JSP897.dense_neighbourhood_maxDegree_ge`:

```lean
theorem dense_neighbourhood_maxDegree_ge (r : ℕ) (hr : 0 < r) (v : V)
    (hv : ∀ w : V, G.degree w ≤ G.degree v)
    (hm : turanNumber (Fintype.card V) (r + 1) ≤ #G.edgeFinset) :
    turanNumber (G.degree v) r ≤ #((G.induce (G.neighborSet v)).edgeFinset)
```

(with existential form `JSP897.dense_neighbourhood_ge`). All of these hold for
**every** finite simple graph, every `n`, and every `r ≥ 1`.

### Index dictionary

`mathlib`'s `turanNumber n r` is the number of edges of the `r`-partite Turán graph
`T_r(n)`, i.e. `ex(n; K_{r+1})`. So the recorded `ex(n; K_r)` is `turanNumber n (r-1)`
and `ex(d; K_{r-1})` is `turanNumber d (r-2)`: the formal `r` above is the recorded
`r` minus `2`. The recorded range `r ≥ 4` is the formal `r ≥ 2`; the formal
statement additionally covers `r = 1`, where it *is* Mantel's theorem
(`JSP897.dense_neighbourhood_one`).

### The `d ≫_r n` clause

The witness is a vertex of maximum degree, and
`2 * turanNumber n (r+1) < n * d(v)` is proved for it — i.e. `d(v) > 2 ex(n;K_{r+2})/n`,
which is `(1 - 1/(r+1) + o(1)) n`. That is the `d ≫_r n` of the recorded statement,
in explicit form.

## What is **not** formalized

Exactly one thing: the **uniqueness clause**. Erdős–Sós also prove that the *only*
graph with `e(G) = ex(n; K_{r+2})` and every neighbourhood at its threshold is the
Turán graph `T_{r+1}(n)`. That is not formalized.

Both readings of the recorded question *are* covered: the strict form
(`dense_neighbourhood`, matching the displayed theorem of Erdős–Sós) and the literal
`≥`/`≥` form (`dense_neighbourhood_maxDegree_ge`). Under the `≥` reading the Turán
graph is simply the equality case, so the recorded exception "unless `G` is the
Turán graph" is not needed.

The commentary's sharper form — `e(G) ≥ ex(n; K_{r+2})` implies *either* `G` is the
Turán graph *or* some neighbourhood is strictly above its threshold — is equivalent
to the uniqueness clause and is **likewise not formalized**.

## Provenance of the two routes

Two arguments are formalized; the first gives the theorem, the second is partial.

1. `JSP897/Bondy.lean` — the **maximum-degree argument**, which gives the theorem in
   full generality. Every edge lies inside `N(v)` or meets its complement, so
   `e(G) ≤ e(G[N(v)]) + ∑_{x ∉ N(v)} d(x) ≤ e(G[N(v)]) + (n - Δ) Δ`; the hypothesis
   bounds `e(G[N(v)])` by `ex(Δ; K_{r+1})`; and `turanNumber_add_mul_le` — the Turán
   graph on `Δ` vertices joined to `n - Δ` independent vertices is `K_{r+2}`-free,
   so `ex(Δ; K_{r+1}) + Δ (n - Δ) ≤ ex(n; K_{r+2})` — closes it.

   **Provenance note, stated plainly.** This is the strategy credited to Bondy
   [Bo83b]. **We did not consult that paper.** Attempts to fetch it from the
   publisher were refused, and we did not pursue library access; only its abstract
   was read, which states the same theorem ("*more than `t_r(n)` edges … any vertex
   of maximum degree `m` … `G[N(v)]` has more than `t_{r-1}(m)` edges*"). The
   argument formalized here was therefore **reconstructed, not transcribed**, and is
   machine-checked rather than quoted. Read it as "a proof of the theorem", not as
   "Bondy's proof".

2. `JSP897/Main.lean` — the **counting argument of Erdős–Sós**, read in the original
   (*On a generalization of Turán's graph-theorem*, Studies in Pure Mathematics, 1983,
   181–185; open access at the Hungarian Academy repository). `∑ e_i = 3T` and
   Goodman's `3T ≥ ∑ d_i² - e n` give `∑ d_i² ≤ e n + ∑ ex(d_i; K_{p+1})`; the Turán
   number identity `2 p · ex(d; K_{p+1}) + s (p - s) = (p-1) d²` (with `s = d % p`)
   and Cauchy–Schwarz then give `2 (p+1) e ≤ p n²`.

   This route is formalized as published, but the published proof closes the gap
   between `2 (p+1) e ≤ p n²` and `e ≤ ex(n; K_{p+2})` by a degree-sequence
   optimisation whose printed formulas are inconsistent in the scan we read (the
   paper writes `f(d_i; k-2)` where the theorem requires `f(d_i; k-1)`, and the index
   ranges in (9)–(10) do not match `n = (k-1)t + r`). Rather than guess, the
   formalization of this route stops at the point where integrality closes the gap
   unaided: `JSP897.card_edgeFinset_le_turanNumber` needs `q (p+1-q) < 2 (p+1)` for
   `q = n % (p+1)` — i.e. at most seven parts (`p ≤ 6`) for every `n`, or
   `(p+1) ∣ n` for every `p`. That restriction is intrinsic to this route, not an
   artefact of the formalization: at `p = 7` and `n ≡ 4 (mod 8)` the density bound
   `2 (p+1) e ≤ p n²` permits `e = ex(n; K_9) + 1`, one too many. The
   full-generality statement comes from route 1.

## Cross-checks

`JSP897/Audit.lean`: `turanNumber 4 3 = 5`, `turanNumber 3 2 = 2`, `turanNumber 6 2 = 9`
and `#(⊤ : SimpleGraph (Fin 4)).edgeFinset = 6` are all closed by `decide`; the
theorem is instantiated at `K₄` with `r = 2` (`6 > 5 = ex(4;K₄)`, so some neighbourhood
beats `ex(3;K₃) = 2`), both through the existence form and through Bondy's
max-degree form. `join_bound_tight` checks that `turanNumber_add_mul_le` is tight:
`ex(4;K₃) + 4·2 = 12 = ex(6;K₄)`.

## Encoding choices

* "edges inside the neighbourhood" is `#((G.induce (G.neighborSet v)).edgeFinset)` —
  `mathlib`'s induced subgraph on `N(v)`, not a hand-rolled count. The bridge to the
  codegree sums used in the proofs is `JSP897.sum_card_inter`, a handshake lemma for
  induced subgraphs.
* "Turán threshold" is `mathlib`'s `SimpleGraph.turanNumber`, defined as the edge
  count of `turanGraph n r`; no closed form is assumed, and the identity used,
  `2 p · ex(n; K_{p+1}) + s (p - s) = (p-1) n²` with `s = n % p`, is proved here
  (`JSP897.two_mul_turanNumber`).
* No hypothesis on `V` beyond `Fintype` and `DecidableEq`; the theorem is not
  restricted to `Fin n`.
