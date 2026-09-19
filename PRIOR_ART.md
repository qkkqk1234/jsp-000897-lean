# Prior art and attribution

## The mathematics is not ours

The problem is Erdős' #1079, posed in

> P. Erdős, *Some recent progress on extremal problems in graph theory*,
> Congr. Numer. (1975), 3–14.

It was solved by

> B. Bollobás, A. Thomason, *Dense neighbourhoods and Turán's theorem*,
> J. Combin. Theory Ser. B **31** (1981), 111–114,

and independently by

> P. Erdős, V. T. Sós, *On a generalization of Turán's graph-theorem*,
> Studies in Pure Mathematics (To the memory of Paul Turán), 1983, 181–185.
> Open access: <https://real.mtak.hu/110556/1/1983-10.pdf>

with the maximum-degree refinement due to

> J. A. Bondy, *Large dense neighbourhoods and Turán's theorem*,
> J. Combin. Theory Ser. B **34** (1983), 109–111.

The Erdős–Sós paper's "added in proof" also credits Bollobás and Eldridge with the
same result.

The counting identity behind route 2 is

> A. W. Goodman, *On sets of acquaintances and strangers at any party*,
> Amer. Math. Monthly **66** (1959), 778–783.

## What is ours

Only the Lean 4 formalization: the statement encoding, the `mathlib` development,
and the verification artifacts here.

One caveat, stated plainly: **the maximum-degree proof in `Bondy.lean` is a
reconstruction.** We did not consult Bondy's paper — publisher fetches were refused
and we did not pursue library access — so the argument formalized there is our own
reconstruction of the strategy credited to him, verified by the Lean kernel rather
than checked against his text. Only his abstract was read, and it states the same
theorem. The counting proof in `Main.lean` follows the Erdős–Sós paper, which we did
read in the original scan.

Submitted as a **formalization** contribution, not as a solver contribution.

## Independence

At the time of submission no Lean formalization of JSP-000897 was present in this
repository. `mathlib` has Turán's theorem
(`Combinatorics/SimpleGraph/Extremal/Turan.lean`, including the extremal
characterisation and the closed form `turanNumber_eq`) but no dense-neighbourhood
result, no Goodman counting, and no supersaturation material.

## Submitter

GitHub: [@qkkqk1234](https://github.com/qkkqk1234)
