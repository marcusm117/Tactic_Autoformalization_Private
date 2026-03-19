import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  refine ⟨?_⟩
  intro e
  let x : Multiplicative ℝ := e.symm Complex.I
  have hx : e x = Complex.I := by
    simp [x]
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by
    simpa using Complex.sq_I
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hI2]
    norm_num
  have hx4 : x ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, hx, hI4]
    simp
  have hx4r : (x : ℝ) ^ 4 = 1 := by
    simpa using hx4
  have hx2sq : ((x : ℝ) ^ 2) ^ 2 = 1 := by
    calc
      ((x : ℝ) ^ 2) ^ 2 = (x : ℝ) ^ (2 * 2) := by rw [← pow_mul]
      _ = 1 := by simpa using hx4r
  have hx2r : (x : ℝ) ^ 2 = 1 := by
    nlinarith [hx2sq, sq_nonneg (x : ℝ)]
  have hx2 : x ^ 2 = 1 := by
    simpa using hx2r
  have hI2x : e (x ^ 2) = -1 := by
    rw [map_pow, hx]
    simpa using Complex.sq_I
  have hEq : (1 : ℂ) = -1 := by
    calc
      (1 : ℂ) = e (x ^ 2) := by simpa [hx2]
      _ = -1 := hI2x
  have hEq' : (1 : ℝ) = -1 := by
    exact congrArg Complex.re hEq
  norm_num at hEq'
