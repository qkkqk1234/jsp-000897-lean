/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP897.Counting

/-!
# JSP-000897 — edges inside neighbourhoods

`twoNbhdEdges G v` is twice the number of edges of `G` inside `N(v)`, written as a
sum of codegrees.  `twoNbhdEdges_eq` identifies it with the edge count of the
induced subgraph `G.induce (G.neighborSet v)`, and `goodman` is the Goodman bound
in the form the Erdős–Sós argument uses.
-/

open Finset SimpleGraph

namespace JSP897

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Twice the number of edges of `G` lying inside the neighbourhood of `v`. -/
def twoNbhdEdges (v : V) : ℕ :=
  ∑ x ∈ G.neighborFinset v, #(G.neighborFinset v ∩ G.neighborFinset x)

/-- Degrees in an induced subgraph. -/
theorem degree_induce (s : Set V) [Fintype s] (x : V) (hx : x ∈ s) :
    (G.induce s).degree ⟨x, hx⟩ = #(s.toFinset ∩ G.neighborFinset x) := by
  classical
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun y _ => (y : V)) ?_ ?_ ?_
  · intro y hy
    rw [mem_neighborFinset, induce_adj] at hy
    simp only [Finset.mem_inter, mem_neighborFinset]
    exact ⟨Set.mem_toFinset.mpr y.2, hy⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro b hb
    simp only [Finset.mem_inter, mem_neighborFinset] at hb
    refine ⟨⟨b, by simpa using hb.1⟩, ?_, rfl⟩
    rw [mem_neighborFinset, induce_adj]
    exact hb.2

/-- Handshake inside a set: the codegree sum over `s` is twice the number of edges
of `G` inside `s`. -/
theorem sum_card_inter (s : Set V) [Fintype s] :
    ∑ x ∈ s.toFinset, #(s.toFinset ∩ G.neighborFinset x)
      = 2 * #((G.induce s).edgeFinset) := by
  classical
  rw [← sum_degrees_eq_twice_card_edges,
    Finset.sum_subtype (p := (· ∈ s)) s.toFinset (fun _ => Set.mem_toFinset)
      (fun x => #(s.toFinset ∩ G.neighborFinset x))]
  exact Fintype.sum_congr _ _ fun x => (degree_induce G s x.1 x.2).symm

/-- `twoNbhdEdges` is twice the number of edges induced on the neighbourhood. -/
theorem twoNbhdEdges_eq (v : V) :
    twoNbhdEdges G v = 2 * #((G.induce (G.neighborSet v)).edgeFinset) := by
  classical
  rw [twoNbhdEdges, neighborFinset_def]
  exact sum_card_inter G (G.neighborSet v)

/-- The neighbourhood sums recover the ordered-triangle count. -/
theorem sum_twoNbhdEdges : ∑ v : V, twoNbhdEdges G v = #(orderedTriangles G) :=
  (card_orderedTriangles_eq_sum G).symm

/-- **Goodman's bound**, in the form used by Erdős–Sós:
`∑ d v ^ 2 ≤ m n + ∑ (edges inside N v)`, all doubled to stay in `ℕ`. -/
theorem goodman :
    2 * ∑ v : V, G.degree v ^ 2
      ≤ 2 * #G.edgeFinset * Fintype.card V + ∑ v : V, twoNbhdEdges G v := by
  rw [sum_twoNbhdEdges]
  exact two_mul_sum_degree_sq_le G

end JSP897
