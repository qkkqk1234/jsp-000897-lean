/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP897.Neighbourhood
import JSP897.Join

/-!
# JSP-000897 — the maximum-degree argument

Every edge either lies inside a set `A` or meets its complement, so
`e(G) ≤ e(G[A]) + ∑_{x ∉ A} d(x)`.  Taking `A = N(v)` for a vertex `v` of maximum
degree `Δ` and using `d(x) ≤ Δ` gives `e(G) ≤ e(G[N(v)]) + Δ (n - Δ)`, and
`turanNumber_add_mul_le` finishes.

This is the strategy credited to Bondy, *Large dense neighbourhoods and Turán's
theorem*, J. Combin. Theory Ser. B **34** (1983), 109–111.  **That paper was not
consulted**: the argument below is a reconstruction, checked by the Lean kernel, not
a transcription.  Only Bondy's abstract was read, and it states the same theorem.
-/

open Finset SimpleGraph

namespace JSP897

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Splitting a degree across a set and its complement. -/
theorem card_inter_add_card_compl_inter (A : Finset V) (x : V) :
    #(A ∩ G.neighborFinset x) + #(Aᶜ ∩ G.neighborFinset x) = G.degree x := by
  classical
  rw [← card_neighborFinset_eq_degree, Finset.inter_comm A, Finset.inter_comm Aᶜ,
    ← Finset.sdiff_eq_inter_compl, Nat.add_comm]
  exact Finset.card_sdiff_add_card_inter _ _

/-- The number of edges between `A` and its complement, counted from either side. -/
theorem cross_symm (A : Finset V) :
    ∑ x ∈ A, #(Aᶜ ∩ G.neighborFinset x) = ∑ y ∈ Aᶜ, #(A ∩ G.neighborFinset y) := by
  classical
  have key : ∀ (S T : Finset V), ∑ x ∈ S, #(T ∩ G.neighborFinset x)
      = ∑ x ∈ S, ∑ y ∈ T, (if G.Adj x y then 1 else 0) := by
    intro S T
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter (fun y => G.Adj x y) T |>.symm]
    · congr 1
      ext y
      simp [mem_neighborFinset]
  rw [key, key, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by
    by_cases h : G.Adj x y
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

/-- **Edges inside a set plus degrees outside it bound all edges.** -/
theorem card_edgeFinset_le (s : Set V) [Fintype s] :
    #G.edgeFinset ≤ #((G.induce s).edgeFinset) + ∑ x ∈ s.toFinsetᶜ, G.degree x := by
  classical
  set A : Finset V := s.toFinset with hA
  have hhand : ∑ x : V, G.degree x = 2 * #G.edgeFinset := sum_degrees_eq_twice_card_edges G
  have hsplit : ∑ x : V, G.degree x = ∑ x ∈ A, G.degree x + ∑ x ∈ Aᶜ, G.degree x := by
    rw [← Finset.sum_add_sum_compl A]
  have hA : ∑ x ∈ A, G.degree x
      = ∑ x ∈ A, #(A ∩ G.neighborFinset x) + ∑ x ∈ A, #(Aᶜ ∩ G.neighborFinset x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => (card_inter_add_card_compl_inter G A x).symm
  have hinside : ∑ x ∈ A, #(A ∩ G.neighborFinset x)
      = 2 * #((G.induce s).edgeFinset) := sum_card_inter G s
  have hcross : ∑ x ∈ A, #(Aᶜ ∩ G.neighborFinset x) ≤ ∑ y ∈ Aᶜ, G.degree y := by
    rw [cross_symm]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_le_card Finset.inter_subset_right
  omega

omit [DecidableEq V] in
/-- **The maximum-degree bound** (the theorem credited to Bondy; proof reconstructed,
see the module docstring).  If the neighbourhood of a vertex of maximum degree spans
at most `ex(Δ; K_{r+1})` edges, then `G` has at most `ex(n; K_{r+2})` edges. -/
theorem card_edgeFinset_le_turanNumber_of_maxDegree (r : ℕ) (hr : 0 < r) (v : V)
    (hv : ∀ w : V, G.degree w ≤ G.degree v)
    (h : #((G.induce (G.neighborSet v)).edgeFinset) ≤ turanNumber (G.degree v) r) :
    #G.edgeFinset ≤ turanNumber (Fintype.card V) (r + 1) := by
  classical
  set d := G.degree v with hd
  set n := Fintype.card V with hn
  have hdn : d ≤ n := by
    rw [hd, hn, ← card_neighborFinset_eq_degree]
    simpa using Finset.card_le_univ (G.neighborFinset v)
  have hbound := card_edgeFinset_le G (G.neighborSet v)
  have hcompl : #(G.neighborSet v).toFinsetᶜ = n - d := by
    rw [Finset.card_compl, ← neighborFinset_def, card_neighborFinset_eq_degree, hn]
  have houtside : ∑ x ∈ (G.neighborSet v).toFinsetᶜ, G.degree x ≤ (n - d) * d := by
    calc ∑ x ∈ (G.neighborSet v).toFinsetᶜ, G.degree x
        ≤ ∑ _x ∈ (G.neighborSet v).toFinsetᶜ, d := Finset.sum_le_sum fun x _ => hv x
      _ = (n - d) * d := by rw [Finset.sum_const, hcompl, smul_eq_mul]
  have hinduce : #((G.induce (G.neighborSet v)).edgeFinset) ≤ turanNumber d r := h
  have hjoin : turanNumber d r + d * (n - d) ≤ turanNumber (d + (n - d)) (r + 1) :=
    turanNumber_add_mul_le d (n - d) r hr
  have hdn' : d + (n - d) = n := by omega
  rw [hdn'] at hjoin
  have hmul : (n - d) * d = d * (n - d) := Nat.mul_comm _ _
  omega

end JSP897
