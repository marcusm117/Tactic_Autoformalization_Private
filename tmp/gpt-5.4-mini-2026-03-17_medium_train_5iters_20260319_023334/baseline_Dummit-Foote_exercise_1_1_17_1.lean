import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  have hpow : x ^ (n : ℕ) = 1 := by
    simpa [hxn] using (pow_orderOf_eq_one x)
  have hsucc : ((n : ℕ) - 1) + 1 = n := by
    simpa [Nat.pred_eq_sub_one] using (Nat.succ_pred_eq_of_pos n.2)
  have hmul : x * x ^ (n - 1 : ℕ) = 1 := by
    calc
      x * x ^ (n - 1 : ℕ) = x ^ (((n : ℕ) - 1) + 1) := by
        rw [← pow_succ']
      _ = x ^ (n : ℕ) := by rw [hsucc]
      _ = 1 := hpow
  have hleft : x * x⁻¹ = 1 := by simp
  have hEq : x * x⁻¹ = x * x ^ (n - 1 : ℕ) := by
    rw [hleft, hmul]
  exact mul_left_cancel hEq
