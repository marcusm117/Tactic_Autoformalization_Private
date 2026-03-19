import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_16 {G : Type*} [Group G]
  (x : G) : x ^ 2 = 1 ↔ (orderOf x = 1 ∨ orderOf x = 2) := by
  constructor
  · intro h
    have hdiv : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have hpos : 0 < orderOf x := orderOf_pos x
    rcases Nat.eq_or_lt_of_le hle with hEq | hLt
    · right
      exact hEq
    · left
      have : orderOf x = 1 := by omega
      exact this
  · intro h
    rcases h with h | h
    · have hx : x = 1 := (orderOf_eq_one_iff.mp h)
      simp [hx]
    · simpa [h] using pow_orderOf_eq_one x
