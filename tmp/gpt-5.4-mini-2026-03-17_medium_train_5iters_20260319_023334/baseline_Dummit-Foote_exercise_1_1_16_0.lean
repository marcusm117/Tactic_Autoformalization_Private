import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_16 {G : Type*} [Group G]
  (x : G) : x ^ 2 = 1 ↔ (orderOf x = 1 ∨ orderOf x = 2) := by
  constructor
  · intro h
    have hdiv : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have h' := Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 2) hdiv
    simpa [eq_comm] using h'
  · intro h
    rcases h with h | h
    · have hx : x = 1 := (orderOf_eq_one_iff.mp h)
      simp [hx]
    · simpa [h] using pow_orderOf_eq_one x
