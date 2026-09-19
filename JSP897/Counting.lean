/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib

/-!
# JSP-000897 — the Goodman counting core (shared with the JSP-000840 development)

Double counting of ordered triangles.  The output used downstream is
`two_mul_sum_degree_sq_le` together with `card_orderedTriangles_le`, i.e. Goodman's
`∑ d v ^ 2 ≤ m n + 3 k₃`; `moon_moser` is the classical corollary.
-/

open Finset SimpleGraph

namespace JSP897

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered triangles of `G`: triples of pairwise adjacent vertices. -/
def orderedTriangles : Finset (V × V × V) :=
  {p ∈ (univ : Finset (V × V × V)) | G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2}

omit [DecidableEq V] in
@[simp] lemma mem_orderedTriangles {p : V × V × V} :
    p ∈ orderedTriangles G ↔ G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2 := by
  simp [orderedTriangles]

private lemma card_six_le {α : Type*} [DecidableEq α] (p₁ p₂ p₃ p₄ p₅ p₆ : α) :
    #({p₁, p₂, p₃, p₄, p₅, p₆} : Finset α) ≤ 6 := by
  refine (card_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((card_insert_le _ _).trans ?_) 1
  simp

/-- Each unordered triangle arises from at most six ordered triangles. -/
theorem card_orderedTriangles_le : #(orderedTriangles G) ≤ 6 * #(G.cliqueFinset 3) := by
  classical
  have himg : (orderedTriangles G).image (fun p : V × V × V => ({p.1, p.2.1, p.2.2} : Finset V))
      ⊆ G.cliqueFinset 3 := by
    intro s hs
    simp only [mem_image, mem_orderedTriangles] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact mem_cliqueFinset_iff.2 (is3Clique_triple_iff.2 ⟨hp.1, hp.2.1, hp.2.2⟩)
  refine le_trans (card_le_mul_card_image _ 6 ?_) (Nat.mul_le_mul_left 6 (card_le_card himg))
  intro s hs
  simp only [mem_image, mem_orderedTriangles] at hs
  obtain ⟨⟨a, b, c⟩, hp, rfl⟩ := hs
  obtain ⟨hab, hac, hbc⟩ := hp
  refine le_trans (card_le_card ?_) (card_six_le (a, b, c) (a, c, b) (b, a, c) (b, c, a)
    (c, a, b) (c, b, a))
  intro q hq
  simp only [mem_filter, mem_orderedTriangles] at hq
  obtain ⟨⟨h12, h13, h23⟩, hq⟩ := hq
  obtain ⟨x, y, z⟩ := q
  simp only at h12 h13 h23 hq
  have m1 : x ∈ ({a, b, c} : Finset V) := by rw [← hq]; simp
  have m2 : y ∈ ({a, b, c} : Finset V) := by rw [← hq]; simp
  have m3 : z ∈ ({a, b, c} : Finset V) := by rw [← hq]; simp
  have e12 := h12.ne
  have e13 := h13.ne
  have e23 := h23.ne
  simp only [mem_insert, mem_singleton] at m1 m2 m3
  rcases m1 with rfl | rfl | rfl <;> rcases m2 with rfl | rfl | rfl <;>
    rcases m3 with rfl | rfl | rfl <;> simp_all

/-- Ordered triangles counted by summing codegrees over ordered adjacent pairs. -/
theorem card_orderedTriangles_eq_sum :
    #(orderedTriangles G) =
      ∑ u : V, ∑ v ∈ G.neighborFinset u, #(G.neighborFinset u ∩ G.neighborFinset v) := by
  classical
  have hinter : ∀ u v : V, G.neighborFinset u ∩ G.neighborFinset v
      = {w ∈ (univ : Finset V) | G.Adj u w ∧ G.Adj v w} := by
    intro u v
    ext w
    simp [mem_neighborFinset]
  rw [orderedTriangles, card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_prod_type, ← sum_filter_add_sum_filter_not univ (fun v => G.Adj u v)]
  have h₂ : ∑ v ∈ {v ∈ univ | ¬ G.Adj u v},
      ∑ w : V, (if G.Adj u v ∧ G.Adj u w ∧ G.Adj v w then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    simp only [mem_filter] at hv
    simp [hv.2]
  rw [h₂, add_zero, ← neighborFinset_eq_filter]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [mem_neighborFinset] at hv
  rw [hinter, card_filter]
  exact Finset.sum_congr rfl fun w _ => by simp [hv]

/-- Two adjacent vertices have at least `d u + d v - n` common neighbours. -/
theorem degree_add_degree_le {u v : V} :
    G.degree u + G.degree v ≤ Fintype.card V + #(G.neighborFinset u ∩ G.neighborFinset v) := by
  classical
  have h := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h2 : #(G.neighborFinset u ∪ G.neighborFinset v) ≤ Fintype.card V := by
    simpa using Finset.card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)
  simp only [card_neighborFinset_eq_degree] at h
  omega

omit [DecidableEq V] in
/-- Swapping the order of summation over ordered adjacent pairs. -/
theorem sum_sum_degree :
    ∑ u : V, ∑ v ∈ G.neighborFinset u, G.degree v = ∑ v : V, G.degree v ^ 2 := by
  classical
  have h : ∀ u : V, ∑ v ∈ G.neighborFinset u, G.degree v
      = ∑ v : V, if G.Adj u v then G.degree v else 0 := by
    intro u
    rw [neighborFinset_eq_filter, sum_filter]
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have : ∑ u : V, (if G.Adj u v then G.degree v else 0)
      = ∑ u ∈ {u ∈ (univ : Finset V) | G.Adj v u}, G.degree v := by
    rw [sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : G.Adj u v
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  rw [this, ← neighborFinset_eq_filter, Finset.sum_const, card_neighborFinset_eq_degree,
    smul_eq_mul, sq]

omit [DecidableEq V] in
/-- Sum of `d u` over ordered adjacent pairs. -/
theorem sum_sum_const (c : ℕ) :
    ∑ u : V, ∑ _v ∈ G.neighborFinset u, c = 2 * #G.edgeFinset * c := by
  simp_rw [Finset.sum_const, card_neighborFinset_eq_degree, smul_eq_mul]
  rw [← Finset.sum_mul, sum_degrees_eq_twice_card_edges]

omit [DecidableEq V] in
/-- The key counting step: `2 ∑ d v ^ 2 ≤ 2 m n + (ordered triangles)`. -/
theorem two_mul_sum_degree_sq_le :
    2 * ∑ v : V, G.degree v ^ 2
      ≤ 2 * #G.edgeFinset * Fintype.card V + #(orderedTriangles G) := by
  classical
  have key : ∑ u : V, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
      ≤ ∑ u : V, ∑ v ∈ G.neighborFinset u,
          (Fintype.card V + #(G.neighborFinset u ∩ G.neighborFinset v)) := by
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    exact degree_add_degree_le G
  have hleft : ∑ u : V, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
      = 2 * ∑ v : V, G.degree v ^ 2 := by
    have : ∀ u : V, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v)
        = G.degree u ^ 2 + ∑ v ∈ G.neighborFinset u, G.degree v := by
      intro u
      rw [Finset.sum_add_distrib, Finset.sum_const, card_neighborFinset_eq_degree, smul_eq_mul, sq]
    simp_rw [this]
    rw [Finset.sum_add_distrib, sum_sum_degree]
    ring
  have hright : ∑ u : V, ∑ v ∈ G.neighborFinset u,
      (Fintype.card V + #(G.neighborFinset u ∩ G.neighborFinset v))
      = 2 * #G.edgeFinset * Fintype.card V + #(orderedTriangles G) := by
    simp_rw [Finset.sum_add_distrib]
    rw [sum_sum_const, card_orderedTriangles_eq_sum]
  rw [hleft, hright] at key
  exact key

omit [DecidableEq V] in
/-- Cauchy–Schwarz for degrees: `(2m) ^ 2 ≤ n * ∑ d v ^ 2`. -/
theorem sq_two_mul_card_edgeFinset_le :
    (2 * #G.edgeFinset) ^ 2 ≤ Fintype.card V * ∑ v : V, G.degree v ^ 2 := by
  have h := _root_.sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := fun v => G.degree v)
  rw [sum_degrees_eq_twice_card_edges] at h
  simpa using h

/-- **Moon–Moser supersaturation.**  For every finite graph,
`4 m ^ 2 ≤ m n ^ 2 + 3 n k₃`, where `m` is the number of edges, `n` the number of
vertices and `k₃` the number of triangles. -/
theorem moon_moser :
    4 * #G.edgeFinset ^ 2
      ≤ #G.edgeFinset * Fintype.card V ^ 2 + 3 * Fintype.card V * #(G.cliqueFinset 3) := by
  have h1 := sq_two_mul_card_edgeFinset_le G
  have h2 := two_mul_sum_degree_sq_le G
  have h3 := card_orderedTriangles_le G
  have h4 : 2 * ((2 * #G.edgeFinset) ^ 2)
      ≤ Fintype.card V * (2 * #G.edgeFinset * Fintype.card V + 6 * #(G.cliqueFinset 3)) := by
    calc 2 * ((2 * #G.edgeFinset) ^ 2)
        ≤ 2 * (Fintype.card V * ∑ v : V, G.degree v ^ 2) := by
          exact Nat.mul_le_mul_left 2 h1
      _ = Fintype.card V * (2 * ∑ v : V, G.degree v ^ 2) := by ring
      _ ≤ Fintype.card V * (2 * #G.edgeFinset * Fintype.card V + 6 * #(G.cliqueFinset 3)) := by
          refine Nat.mul_le_mul_left _ (le_trans h2 ?_)
          omega
  nlinarith [h4]

end JSP897
