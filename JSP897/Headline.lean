/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP897.Bondy
import JSP897.Main

/-!
# JSP-000897 — the dense-neighbourhood theorem

**Erdős' problem 1079.**  If an `n`-vertex graph has more edges than the Turán
number `ex(n; K_{r+2})`, then some vertex `v` has more than `ex(d(v); K_{r+1})`
edges inside its neighbourhood — and `v` may be taken of maximum degree.

`dense_neighbourhood` is the headline statement; `dense_neighbourhood_maxDegree`
is the refinement attributed to Bondy.
-/

open Finset SimpleGraph

namespace JSP897

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **Bondy's refinement**: the dense neighbourhood can be taken at a vertex of
maximum degree. -/
theorem dense_neighbourhood_maxDegree (r : ℕ) (hr : 0 < r) (v : V)
    (hv : ∀ w : V, G.degree w ≤ G.degree v)
    (hm : turanNumber (Fintype.card V) (r + 1) < #G.edgeFinset) :
    turanNumber (G.degree v) r < #((G.induce (G.neighborSet v)).edgeFinset) := by
  by_contra hcon
  push Not at hcon
  exact absurd (card_edgeFinset_le_turanNumber_of_maxDegree G r hr v hv hcon) (by omega)

omit [DecidableEq V] in
/-- **The dense-neighbourhood theorem (Erdős' problem 1079).**  Above the Turán
threshold, some neighbourhood is itself above the Turán threshold. -/
theorem dense_neighbourhood (r : ℕ) (hr : 0 < r)
    (hm : turanNumber (Fintype.card V) (r + 1) < #G.edgeFinset) :
    ∃ v : V, turanNumber (G.degree v) r < #((G.induce (G.neighborSet v)).edgeFinset) := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exfalso
    have h0 : Fintype.card V = 0 := Fintype.card_eq_zero
    have h1 : #G.edgeFinset ≤ (Fintype.card V).choose 2 := card_edgeFinset_le_card_choose_two
    have h2 : (0 : ℕ).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by norm_num)
    rw [h0, h2] at h1
    omega
  obtain ⟨v, hv⟩ := Finite.exists_max fun w : V => G.degree w
  exact ⟨v, dense_neighbourhood_maxDegree G r hr v hv hm⟩

omit [DecidableEq V] in
/-- **The recorded statement, verbatim (`≥` / `≥`).**  If `G` has *at least*
`ex(n; K_{r+2})` edges then a vertex `v` of maximum degree has *at least*
`ex(d(v); K_{r+1})` edges inside its neighbourhood.  (The Turán graph itself is the
equality case, so no exception is needed in this reading.) -/
theorem dense_neighbourhood_maxDegree_ge (r : ℕ) (hr : 0 < r) (v : V)
    (hv : ∀ w : V, G.degree w ≤ G.degree v)
    (hm : turanNumber (Fintype.card V) (r + 1) ≤ #G.edgeFinset) :
    turanNumber (G.degree v) r ≤ #((G.induce (G.neighborSet v)).edgeFinset) := by
  classical
  by_contra hcon
  push Not at hcon
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
  have hjoin : turanNumber d r + d * (n - d) ≤ turanNumber (d + (n - d)) (r + 1) :=
    turanNumber_add_mul_le d (n - d) r hr
  have hdn' : d + (n - d) = n := by omega
  rw [hdn'] at hjoin
  have hmul : (n - d) * d = d * (n - d) := Nat.mul_comm _ _
  omega

omit [DecidableEq V] in
/-- The existential form of the recorded statement (`≥` / `≥`). -/
theorem dense_neighbourhood_ge (r : ℕ) (hr : 0 < r) [Nonempty V]
    (hm : turanNumber (Fintype.card V) (r + 1) ≤ #G.edgeFinset) :
    ∃ v : V, turanNumber (G.degree v) r ≤ #((G.induce (G.neighborSet v)).edgeFinset) := by
  obtain ⟨v, hv⟩ := Finite.exists_max fun w : V => G.degree w
  exact ⟨v, dense_neighbourhood_maxDegree_ge G r hr v hv hm⟩

omit [DecidableEq V] in
/-- A maximum-degree vertex has degree at least the average: `2 m ≤ n Δ`.  Combined
with `m > ex(n; K_{r+2})` this is the `d ≫_r n` demanded in Erdős' phrasing. -/
theorem two_mul_card_edgeFinset_le_card_mul_degree (v : V) (hv : ∀ w : V, G.degree w ≤ G.degree v) :
    2 * #G.edgeFinset ≤ Fintype.card V * G.degree v := by
  rw [← sum_degrees_eq_twice_card_edges]
  calc ∑ w : V, G.degree w ≤ ∑ _w : V, G.degree v := Finset.sum_le_sum fun w _ => hv w
    _ = Fintype.card V * G.degree v := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq V] in
/-- **Erdős' problem 1079, as asked**: above the Turán threshold there is a vertex
whose degree is large (`n d ≥ 2 m > 2 ex(n; K_{r+2})`) *and* whose neighbourhood
spans more than `ex(d; K_{r+1})` edges. -/
theorem dense_neighbourhood_large_degree (r : ℕ) (hr : 0 < r)
    (hm : turanNumber (Fintype.card V) (r + 1) < #G.edgeFinset) :
    ∃ v : V, 2 * turanNumber (Fintype.card V) (r + 1) < Fintype.card V * G.degree v ∧
      turanNumber (G.degree v) r < #((G.induce (G.neighborSet v)).edgeFinset) := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exfalso
    have h0 : Fintype.card V = 0 := Fintype.card_eq_zero
    have h1 : #G.edgeFinset ≤ (Fintype.card V).choose 2 := card_edgeFinset_le_card_choose_two
    have h2 : (0 : ℕ).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by norm_num)
    rw [h0, h2] at h1
    omega
  obtain ⟨v, hv⟩ := Finite.exists_max fun w : V => G.degree w
  refine ⟨v, ?_, dense_neighbourhood_maxDegree G r hr v hv hm⟩
  have := two_mul_card_edgeFinset_le_card_mul_degree G v hv
  omega

omit [DecidableEq V] in
/-- Specialisation to `r = 1`: Mantel's theorem.  More than `⌊n²/4⌋` edges force a
vertex whose neighbourhood contains an edge, i.e. a triangle. -/
theorem dense_neighbourhood_one
    (hm : turanNumber (Fintype.card V) 2 < #G.edgeFinset) :
    ∃ v : V, 0 < #((G.induce (G.neighborSet v)).edgeFinset) := by
  obtain ⟨v, hv⟩ := dense_neighbourhood G 1 one_pos hm
  refine ⟨v, ?_⟩
  have : turanNumber (G.degree v) 1 = 0 := by
    rw [turanNumber_eq]
    simp [Nat.mod_one]
  omega

end JSP897
