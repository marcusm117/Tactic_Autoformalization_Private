import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by
  have hconj : ∀ n : ℕ, a⁻¹ * (a * b)^n * a = (b * a)^n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        simp [pow_succ, mul_assoc, ih]
  have hconj' : ∀ n : ℕ, b⁻¹ * (b * a)^n * b = (a * b)^n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        simp [pow_succ, mul_assoc, ih]
  have hdiv1 : orderOf (a * b) ∣ orderOf (b * a) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    calc
      (a * b) ^ orderOf (b * a) = b⁻¹ * (b * a) ^ orderOf (b * a) * b := by
        symm
        exact hconj' (orderOf (b * a))
      _ = 1 := by simp [pow_orderOf_eq_one]
  have hdiv2 : orderOf (b * a) ∣ orderOf (a * b) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    calc
      (b * a) ^ orderOf (a * b) = a⁻¹ * (a * b) ^ orderOf (a * b) * a := by
        symm
        exact hconj (orderOf (a * b))
      _ = 1 := by simp [pow_orderOf_eq_one]
  exact Nat.dvd_antisymm hdiv1 hdiv2
