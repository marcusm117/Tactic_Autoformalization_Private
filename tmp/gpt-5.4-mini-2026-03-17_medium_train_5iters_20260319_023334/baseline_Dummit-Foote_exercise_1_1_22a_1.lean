import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_22a {G : Type*} [Group G] (x g : G) :
  orderOf x = orderOf (g⁻¹ * x * g) := by
  let y : G := g⁻¹ * x * g
  have hpow : ∀ n : ℕ, y ^ n = g⁻¹ * x ^ n * g := by
    intro n
    induction n with
    | zero =>
        simp [y]
    | succ n ih =>
        rw [pow_succ, ih, pow_succ]
        simp [y, mul_assoc]
  have hxy : orderOf y ∣ orderOf x := by
    apply (pow_eq_one_iff_dvd_orderOf).2
    calc
      y ^ orderOf x = g⁻¹ * x ^ orderOf x * g := hpow _
      _ = 1 := by simp [pow_orderOf_eq_one, y]
  have hyx : orderOf x ∣ orderOf y := by
    apply (pow_eq_one_iff_dvd_orderOf).2
    calc
      x ^ orderOf y = 1 := by simp [pow_orderOf_eq_one]
      _ = g * y ^ orderOf y * g⁻¹ := by simp [y]
  exact Nat.dvd_antisymm hxy hyx
