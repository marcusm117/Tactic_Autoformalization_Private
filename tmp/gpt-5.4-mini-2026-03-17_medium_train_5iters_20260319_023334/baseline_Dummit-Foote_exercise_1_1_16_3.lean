import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_16 {G : Type*} [Group G]
  (x : G) : x ^ 2 = 1 ↔ (orderOf x = 1 ∨ orderOf x = 2) := by
  constructor
  · intro h
    have hdiv : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rcases hdiv with ⟨k, hk⟩
    cases h0 : orderOf x with
    | zero =>
        exact False.elim (by simpa [h0] using hk)
    | succ n =>
        cases n with
        | zero =>
            left
            simpa [h0]
        | succ m =>
            have hle : Nat.succ (Nat.succ m) ≤ 2 := by
              have hle0 : orderOf x ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdiv
              simpa [h0] using hle0
            have hcontra : False := by omega
            exact False.elim hcontra
  · intro h
    rcases h with h | h
    · have hx : x = 1 := (orderOf_eq_one_iff.mp h)
      simp [hx]
    · simpa [h] using pow_orderOf_eq_one x
