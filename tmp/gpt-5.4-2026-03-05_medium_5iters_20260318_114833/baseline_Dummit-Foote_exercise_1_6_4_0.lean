import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  classical
  refine ⟨?_⟩
  intro e
  let x : ℝ := e.symm Complex.I
  have hx : e x = Complex.I := by
    simp [x]
  have hx4 : x ^ 4 = 1 := by
    apply e.injective
    calc
      e (x ^ 4) = (e x) ^ 4 := by simp
      _ = Complex.I ^ 4 := by simp [hx]
      _ = 1 := by norm_num
      _ = e 1 := by simp
  have hfac : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
    nlinarith [hx4]
  have hplus : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hx2 : x ^ 2 = 1 := by
    have hminus : x ^ 2 - 1 = 0 := (mul_eq_zero.mp hfac).resolve_right hplus
    nlinarith
  have hI2 : Complex.I ^ 2 = 1 := by
    calc
      Complex.I ^ 2 = (e x) ^ 2 := by simpa [hx]
      _ = e (x ^ 2) := by simp
      _ = e 1 := by simp [hx2]
      _ = 1 := by simp
  norm_num at hI2
