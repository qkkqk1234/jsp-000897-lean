/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP897.Headline

/-!
# JSP-000897 — audit

Kernel cross-checks on small cases, a non-vacuity witness, and the axiom audit.
-/

open Finset SimpleGraph

namespace JSP897Audit

open JSP897

/-! ### Turán numbers, checked against the definition -/

theorem turanNumber_4_3 : turanNumber 4 3 = 5 := by decide
theorem turanNumber_3_2 : turanNumber 3 2 = 2 := by decide
theorem turanNumber_6_2 : turanNumber 6 2 = 9 := by decide

/-! ### Non-vacuity: `K₄` at `r = 2`

`K₄` has `6 > 5 = ex(4; K₄)` edges, so some vertex must have more than
`ex(3; K₃) = 2` edges inside its neighbourhood — and indeed every neighbourhood is
a triangle. -/

theorem card_edgeFinset_top_four : #(⊤ : SimpleGraph (Fin 4)).edgeFinset = 6 := by decide

theorem witness :
    ∃ v : Fin 4, turanNumber ((⊤ : SimpleGraph (Fin 4)).degree v) 2
      < #(((⊤ : SimpleGraph (Fin 4)).induce
          ((⊤ : SimpleGraph (Fin 4)).neighborSet v)).edgeFinset) :=
  dense_neighbourhood _ 2 (by norm_num) (by decide)

/-- The same witness through Bondy's refinement, at a vertex of maximum degree. -/
theorem witness_maxDegree :
    turanNumber ((⊤ : SimpleGraph (Fin 4)).degree 0) 2
      < #(((⊤ : SimpleGraph (Fin 4)).induce
          ((⊤ : SimpleGraph (Fin 4)).neighborSet 0)).edgeFinset) :=
  dense_neighbourhood_maxDegree _ 2 (by norm_num) 0 (by decide) (by decide)

/-! ### The join bound, checked numerically

`ex(4; K₃) + 4·2 = 4 + 8 = 12 ≤ 12 = ex(6; K₄)`: tight, as it must be at a Turán
degree. -/

theorem join_bound_tight : turanNumber 4 2 + 4 * 2 = turanNumber 6 3 := by decide

theorem join_bound_check : turanNumber 4 2 + 4 * 2 ≤ turanNumber (4 + 2) (2 + 1) :=
  turanNumber_add_mul_le 4 2 2 (by norm_num)

end JSP897Audit

-- Arithmetic
#print axioms JSP897.two_mul_turanNumber

-- Counting core (shared with JSP-000840)
#print axioms JSP897.card_orderedTriangles_le
#print axioms JSP897.card_orderedTriangles_eq_sum
#print axioms JSP897.two_mul_sum_degree_sq_le
#print axioms JSP897.sq_two_mul_card_edgeFinset_le
#print axioms JSP897.moon_moser

-- Neighbourhoods
#print axioms JSP897.degree_induce
#print axioms JSP897.sum_card_inter
#print axioms JSP897.twoNbhdEdges_eq
#print axioms JSP897.goodman

-- The join construction
#print axioms JSP897.joinGraph_cliqueFree
#print axioms JSP897.card_edgeFinset_joinGraph
#print axioms JSP897.turanNumber_add_mul_le

-- The maximum-degree argument
#print axioms JSP897.card_inter_add_card_compl_inter
#print axioms JSP897.cross_symm
#print axioms JSP897.card_edgeFinset_le
#print axioms JSP897.card_edgeFinset_le_turanNumber_of_maxDegree

-- Headline
#print axioms JSP897.dense_neighbourhood
#print axioms JSP897.dense_neighbourhood_maxDegree
#print axioms JSP897.dense_neighbourhood_one
#print axioms JSP897.two_mul_card_edgeFinset_le_card_mul_degree
#print axioms JSP897.dense_neighbourhood_large_degree
#print axioms JSP897.dense_neighbourhood_maxDegree_ge
#print axioms JSP897.dense_neighbourhood_ge

-- The Erdős–Sós counting route
#print axioms JSP897.two_mul_card_edgeFinset_le
#print axioms JSP897.card_edgeFinset_le_turanNumber
#print axioms JSP897.exists_dense_neighbourhood
#print axioms JSP897.exists_dense_neighbourhood_of_le_six
#print axioms JSP897.exists_dense_neighbourhood_of_dvd

-- Audit
#print axioms JSP897Audit.witness
#print axioms JSP897Audit.witness_maxDegree
#print axioms JSP897Audit.join_bound_tight
