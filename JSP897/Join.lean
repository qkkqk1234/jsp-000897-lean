/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib

/-!
# JSP-000897 — joining a Turán graph to an independent set

`joinGraph d k r` is the Turán graph `T_r(d)` joined completely to an independent
set of size `k`.  It is `(r+1)`-colourable, hence `K_{r+2}`-free, so Turán's
theorem bounds its edge count.  The consequence used downstream is the arithmetic
inequality `ex(d; K_{r+1}) + d k ≤ ex(d + k; K_{r+2})`.
-/

open Finset SimpleGraph

namespace JSP897

/-- The Turán graph `T_r(d)` joined completely to `k` independent vertices. -/
def joinGraph (d k r : ℕ) : SimpleGraph (Fin d ⊕ Fin k) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inl j => (turanGraph d r).Adj i j
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    rintro (i | i) (j | j) h
    exacts [h.symm, trivial, trivial, h]⟩
  loopless := ⟨by
    rintro (i | i) h
    exacts [h.ne rfl, h]⟩

variable (d k r : ℕ)

@[simp] lemma joinGraph_adj_inl_inl (i j : Fin d) :
    (joinGraph d k r).Adj (Sum.inl i) (Sum.inl j) ↔ (turanGraph d r).Adj i j := Iff.rfl

@[simp] lemma joinGraph_adj_inl_inr (i : Fin d) (j : Fin k) :
    (joinGraph d k r).Adj (Sum.inl i) (Sum.inr j) ↔ True := Iff.rfl

@[simp] lemma joinGraph_adj_inr_inl (i : Fin k) (j : Fin d) :
    (joinGraph d k r).Adj (Sum.inr i) (Sum.inl j) ↔ True := Iff.rfl

@[simp] lemma joinGraph_adj_inr_inr (i j : Fin k) :
    (joinGraph d k r).Adj (Sum.inr i) (Sum.inr j) ↔ False := Iff.rfl

instance : DecidableRel (joinGraph d k r).Adj := fun x y => by
  cases x <;> cases y <;>
    · unfold joinGraph
      simp only
      infer_instance

/-- `joinGraph d k r` is `(r+1)`-colourable: the Turán part uses `r` colours and the
independent part one more. -/
def joinColoring (hr : 0 < r) : (joinGraph d k r).Coloring (Fin (r + 1)) :=
  SimpleGraph.Coloring.mk
    (fun x => match x with
      | Sum.inl i => ⟨(i : ℕ) % r, by have := Nat.mod_lt (i : ℕ) hr; omega⟩
      | Sum.inr _ => ⟨r, by omega⟩)
    (by
      rintro (i | i) (j | j) h
      · simp only [joinGraph_adj_inl_inl, turanGraph_adj] at h
        simpa using h
      · simp only [ne_eq, Fin.mk.injEq]
        have := Nat.mod_lt (i : ℕ) hr
        omega
      · simp only [ne_eq, Fin.mk.injEq]
        have := Nat.mod_lt (j : ℕ) hr
        omega
      · exact absurd h (by simp))

theorem joinGraph_cliqueFree (hr : 0 < r) : (joinGraph d k r).CliqueFree (r + 2) := by
  have hc : (joinGraph d k r).Colorable (r + 1) := by
    simpa using (joinColoring d k r hr).colorable
  exact hc.cliqueFree (by omega)

/-- Degrees of the Turán side. -/
lemma degree_joinGraph_inl (i : Fin d) :
    (joinGraph d k r).degree (Sum.inl i) = (turanGraph d r).degree i + k := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    neighborFinset_eq_filter, neighborFinset_eq_filter, card_filter, card_filter,
    Fintype.sum_sum_type]
  simp

/-- Degrees of the independent side. -/
lemma degree_joinGraph_inr (j : Fin k) :
    (joinGraph d k r).degree (Sum.inr j) = d := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter,
    Fintype.sum_sum_type]
  simp

theorem card_edgeFinset_joinGraph :
    #(joinGraph d k r).edgeFinset = turanNumber d r + d * k := by
  classical
  have h := sum_degrees_eq_twice_card_edges (joinGraph d k r)
  rw [Fintype.sum_sum_type] at h
  simp only [degree_joinGraph_inl, degree_joinGraph_inr] at h
  rw [Finset.sum_add_distrib, sum_degrees_eq_twice_card_edges] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have hcomm : k * d = d * k := Nat.mul_comm _ _
  have hturan : turanNumber d r = #(turanGraph d r).edgeFinset := rfl
  omega

/-- **The arithmetic inequality behind the maximum-degree argument**: a Turán graph on `d`
vertices joined to `k` independent vertices cannot beat the Turán graph on `d + k`
vertices. -/
theorem turanNumber_add_mul_le (hr : 0 < r) :
    turanNumber d r + d * k ≤ turanNumber (d + k) (r + 1) := by
  have hcf := joinGraph_cliqueFree d k r hr
  have := SimpleGraph.CliqueFree.card_edgeFinset_le (r := r + 1) hcf
  rwa [card_edgeFinset_joinGraph, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at this

end JSP897
