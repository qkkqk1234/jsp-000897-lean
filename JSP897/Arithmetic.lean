/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib

/-!
# JSP-000897 — arithmetic of the Turán number

The single identity the Erdős–Sós argument needs:
`2 p · ex(n; p) + s (p - s) = (p - 1) n²`, where `s = n % p`.
-/

open Finset SimpleGraph

namespace JSP897

private lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

/-- **Exact form of the Turán number.**  With `s = n % p`,
`2 p · turanNumber n p + s (p - s) = (p - 1) n ^ 2`.

Read without subtraction: `2 p` times the Turán number is `(p-1) n²` less the
defect `s (p - s)` contributed by the unbalanced parts. -/
theorem two_mul_turanNumber (p : ℕ) : ∀ n : ℕ,
    2 * p * turanNumber n p + (n % p) * (p - n % p) = (p - 1) * n ^ 2 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · intro n; simp
  obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n (P + 1) with hn | hn
    · -- `n < p`: the Turán graph on `n` vertices is complete
      have hmod : n % (P + 1) = n := Nat.mod_eq_of_lt hn
      have hturan : turanNumber n (P + 1) = n.choose 2 := by
        rw [turanNumber_eq, hmod]; simp
      obtain ⟨k, rfl⟩ : ∃ k, P = n + k := ⟨P - n, by omega⟩
      rw [hturan, hmod]
      have hsub : n + k + 1 - n = k + 1 := by omega
      rw [hsub, show 2 * (n + k + 1) * n.choose 2 = (n + k + 1) * (2 * n.choose 2) by ring,
        two_mul_choose_two]
      cases n with
      | zero => simp
      | succ j => simp only [Nat.succ_sub_one]; ring
    · -- `n ≥ p`: step down by `p`
      obtain ⟨m, rfl⟩ : ∃ m, n = m + (P + 1) := ⟨n - (P + 1), by omega⟩
      have hmod : (m + (P + 1)) % (P + 1) = m % (P + 1) := Nat.add_mod_right m (P + 1)
      rw [turanNumber_add, hmod]
      have IH := ih m (by omega)
      have hchoose : 2 * (P + 1) * (P + 1).choose 2 = (P + 1) * ((P + 1) * P) := by
        rw [show 2 * (P + 1) * (P + 1).choose 2 = (P + 1) * (2 * (P + 1).choose 2) by ring,
          two_mul_choose_two]
        simp
      have expand : 2 * (P + 1) * (turanNumber m (P + 1) + m * (P + 1 - 1) + (P + 1).choose 2)
          + m % (P + 1) * (P + 1 - m % (P + 1))
          = (2 * (P + 1) * turanNumber m (P + 1) + m % (P + 1) * (P + 1 - m % (P + 1)))
            + 2 * (P + 1) * (m * P) + 2 * (P + 1) * (P + 1).choose 2 := by
        simp only [Nat.add_sub_cancel]
        ring
      rw [expand, IH, hchoose]
      simp only [Nat.add_sub_cancel]
      ring

end JSP897
