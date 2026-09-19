/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP897.Neighbourhood
import JSP897.Arithmetic

/-!
# JSP-000897 — the Erdős–Sós argument

If every neighbourhood of `G` spans at most `ex(d(v); K_{p+1})` edges, then `G` has
at most `ex(n; K_{p+2})` edges — a strengthening of Turán's theorem, conjectured by
Erdős and proved by Bollobás–Thomason and, independently, by Erdős–Sós.

Here the parameter `p` is the number of parts of the *neighbourhood's* Turán graph:
the hypothesis is `e(G[N v]) ≤ ex(d v; K_{p+1})` and the conclusion
`e(G) ≤ ex(n; K_{p+2})`.  This route covers `p ≤ 6` (at most seven parts) or
`(p+1) ∣ n`; the general case is in `JSP897/Bondy.lean`.

The chain is: Goodman's inequality bounds `∑ d v ^ 2` by `m n` plus the edges inside
neighbourhoods; the hypothesis bounds those by Turán numbers; the Turán number
identity turns that into `(p+1) ∑ d v ^ 2 ≤ 2 p m n`; and Cauchy–Schwarz
(`(2m)^2 ≤ n ∑ d v ^ 2`) closes it to `2 (p+1) m ≤ p n ^ 2`.
-/

open Finset SimpleGraph

namespace JSP897

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **The density bound.**  If every neighbourhood spans at most `ex(d v; K_{p+1})`
edges, then `2 (p+1) m ≤ p n²`. -/
theorem two_mul_card_edgeFinset_le (p : ℕ) (hp : 1 ≤ p)
    (h : ∀ v : V, #((G.induce (G.neighborSet v)).edgeFinset) ≤ turanNumber (G.degree v) p) :
    2 * (p + 1) * #G.edgeFinset ≤ p * Fintype.card V ^ 2 := by
  classical
  set n := Fintype.card V with hn
  set m := #G.edgeFinset with hm
  set S := ∑ v : V, G.degree v ^ 2 with hS
  -- Goodman, with the hypothesis substituted
  have hgood : 2 * S ≤ 2 * (m * n) + 2 * ∑ v : V, turanNumber (G.degree v) p := by
    have h0 := goodman G
    have h1 : ∑ v : V, twoNbhdEdges G v ≤ 2 * ∑ v : V, turanNumber (G.degree v) p := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [twoNbhdEdges_eq]
      exact Nat.mul_le_mul_left 2 (h v)
    have h2 : 2 * #G.edgeFinset * Fintype.card V = 2 * (m * n) := by rw [hm, hn]; ring
    omega
  have hgood' : S ≤ m * n + ∑ v : V, turanNumber (G.degree v) p := by omega
  -- feed in the Turán number identity
  have hturan : 2 * p * ∑ v : V, turanNumber (G.degree v) p ≤ (p - 1) * S := by
    rw [Finset.mul_sum, hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => mul_turanNumber_le
  have hkey : (p + 1) * S ≤ 2 * p * (m * n) := by
    have h1 : 2 * p * S ≤ 2 * p * (m * n) + 2 * p * ∑ v : V, turanNumber (G.degree v) p := by
      calc 2 * p * S ≤ 2 * p * (m * n + ∑ v : V, turanNumber (G.degree v) p) :=
            Nat.mul_le_mul_left _ hgood'
        _ = 2 * p * (m * n) + 2 * p * ∑ v : V, turanNumber (G.degree v) p := by ring
    have h2 : 2 * p * S ≤ 2 * p * (m * n) + (p - 1) * S := le_trans h1 (by omega)
    have hp1 : (p - 1) + (p + 1) = 2 * p := by omega
    nlinarith [h2, hp1, Nat.sub_add_cancel hp]
  -- Cauchy–Schwarz
  have hcs : (2 * m) ^ 2 ≤ n * S := sq_two_mul_card_edgeFinset_le G
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · simp [hm0]
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 * m by omega)
  calc 2 * m * (2 * (p + 1) * m)
      = (p + 1) * (2 * m) ^ 2 := by ring
    _ ≤ (p + 1) * (n * S) := Nat.mul_le_mul_left _ hcs
    _ = n * ((p + 1) * S) := by ring
    _ ≤ n * (2 * p * (m * n)) := Nat.mul_le_mul_left _ hkey
    _ = 2 * m * (p * n ^ 2) := by ring

omit [DecidableEq V] in
/-- **Erdős–Sós / Bollobás–Thomason, for the residues where the density bound
suffices.**  If every neighbourhood spans at most `ex(d v; K_{p+1})` edges, and the
residue `q = n % (p+1)` satisfies `q (p+1-q) < 2 (p+1)`, then `m ≤ ex(n; K_{p+2})`. -/
theorem card_edgeFinset_le_turanNumber (p : ℕ) (hp : 1 ≤ p)
    (h : ∀ v : V, #((G.induce (G.neighborSet v)).edgeFinset) ≤ turanNumber (G.degree v) p)
    (hres : (Fintype.card V % (p + 1)) * ((p + 1) - Fintype.card V % (p + 1)) < 2 * (p + 1)) :
    #G.edgeFinset ≤ turanNumber (Fintype.card V) (p + 1) := by
  have hA := two_mul_card_edgeFinset_le G p hp h
  have hid := two_mul_turanNumber (p + 1) (Fintype.card V)
  simp only [Nat.add_sub_cancel] at hid
  have expand : (2 * (p + 1)) * (turanNumber (Fintype.card V) (p + 1) + 1)
      = 2 * (p + 1) * turanNumber (Fintype.card V) (p + 1) + 2 * (p + 1) := by ring
  have hlt : (2 * (p + 1)) * #G.edgeFinset
      < (2 * (p + 1)) * (turanNumber (Fintype.card V) (p + 1) + 1) := by omega
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hlt)

omit [DecidableEq V] in
/-- **The dense-neighbourhood theorem** (Erdős' problem 1079), in the range of
residues covered here: above the Turán threshold some neighbourhood is itself above
the Turán threshold. -/
theorem exists_dense_neighbourhood (p : ℕ) (hp : 1 ≤ p)
    (hres : (Fintype.card V % (p + 1)) * ((p + 1) - Fintype.card V % (p + 1)) < 2 * (p + 1))
    (hm : turanNumber (Fintype.card V) (p + 1) < #G.edgeFinset) :
    ∃ v : V, turanNumber (G.degree v) p < #((G.induce (G.neighborSet v)).edgeFinset) := by
  by_contra hcon
  push Not at hcon
  exact absurd (card_edgeFinset_le_turanNumber G p hp hcon hres) (by omega)

/-- The residue condition holds automatically when `r ≤ 7`: `q (r - q) ≤ r²/4 < 2r`. -/
theorem residue_lt_of_le_seven {r q : ℕ} (hr2 : 2 ≤ r) (hr : r ≤ 7) (hq : q < r) :
    q * (r - q) < 2 * r := by
  obtain ⟨j, hj⟩ : ∃ j, r = q + j := ⟨r - q, by omega⟩
  have hsub : r - q = j := by omega
  rw [hsub]
  have key : 4 * (q * j) ≤ (q + j) ^ 2 := by
    zify
    nlinarith [sq_nonneg ((q : ℤ) - j)]
  have hsq : r ^ 2 ≤ 7 * r := by nlinarith
  rw [← hj] at key
  omega

omit [DecidableEq V] in
/-- **Erdős' problem 1079 for at most seven parts** (`p ≤ 6`).  If an `n`-vertex graph has more than
`ex(n; K_{p+2})` edges then some vertex `v` has more than `ex(d v; K_{p+1})` edges
inside its neighbourhood. -/
theorem exists_dense_neighbourhood_of_le_six (p : ℕ) (hp : 1 ≤ p) (hp6 : p ≤ 6)
    (hm : turanNumber (Fintype.card V) (p + 1) < #G.edgeFinset) :
    ∃ v : V, turanNumber (G.degree v) p < #((G.induce (G.neighborSet v)).edgeFinset) := by
  refine exists_dense_neighbourhood G p hp ?_ hm
  exact residue_lt_of_le_seven (by omega) (by omega) (Nat.mod_lt _ (by omega))

omit [DecidableEq V] in
/-- **Erdős' problem 1079 when the number of parts divides `n`.** -/
theorem exists_dense_neighbourhood_of_dvd (p : ℕ) (hp : 1 ≤ p)
    (hdvd : (p + 1) ∣ Fintype.card V)
    (hm : turanNumber (Fintype.card V) (p + 1) < #G.edgeFinset) :
    ∃ v : V, turanNumber (G.degree v) p < #((G.induce (G.neighborSet v)).edgeFinset) := by
  refine exists_dense_neighbourhood G p hp ?_ hm
  obtain ⟨c, hc⟩ := hdvd
  have h0 : Fintype.card V % (p + 1) = 0 := by rw [hc, Nat.mul_mod_right]
  rw [h0]
  omega

end JSP897
