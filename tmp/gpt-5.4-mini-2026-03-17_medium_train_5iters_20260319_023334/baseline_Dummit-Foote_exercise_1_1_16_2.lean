import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_16 {G : Type*} [Group G]
  (x : G) : x ^ 2 = 1 ↔ (orderOf x = 1 ∨ orderOf x = 2) := by
  constructor
  · intro h
    have hdiv : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rcases hdiv with ⟨k, hk⟩
    cases hox : orderOf x with
    | zero =>
        simp [hox] at hk
        exact False.elim hk
    | succ n =>
        cases n with
        | zero =>
            left
            exact hox
        | succ m =>
            cases m with
            | zero =>
                right
                exact hox
            | succ m' =>
                cases k with
                | zero =>
                    simp [hox] at hk
                    exact False.elim hk
                | succ k' =>
                    have hge : 3 ≤ Nat.succ (Nat.succ (Nat.succ m')) := by omega
                    have h1 : Nat.succ (Nat.succ (Nat.succ m')) ≤ Nat.succ (Nat.succ (Nat.succ m')) * Nat.succ k' := by
                      have hk1 : 1 ≤ Nat.succ k' := Nat.succ_le_succ (Nat.zero_le k')
                      simpa using (Nat.mul_le_mul_left' hk1 (Nat.succ (Nat.succ (Nat.succ m'))))
                    have h3 : 3 ≤ Nat.succ (Nat.succ (Nat.succ m')) * Nat.succ k' := le_trans hge h1
                    have hle : 3 ≤ 2 := by
                      simpa [hk] using h3
                    have hnot : ¬ 3 ≤ 2 := by decide
                    exact hnot hle
  · intro h
    rcases h with h | h
    · have hx : x = 1 := (orderOf_eq_one_iff.mp h)
      simp [hx]
    · simpa [h] using pow_orderOf_eq_one x
