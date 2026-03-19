import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  classical
  intro e
  let x : Multiplicative ℝ := e.symm Complex.I
  have hx : e x = Complex.I := by
    simp [x]
  have hx4 : x ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, hx]
    norm_num [Complex.sq_I]
  have hx4R : ((x : ℝ) ^ (2 * 2)) = 1 := by
    simpa using hx4
  have hx2sq : ((x : ℝ) ^ 2) ^ 2 = 1 := by
    calc
      ((x : ℝ) ^ 2) ^ 2 = (x : ℝ) ^ (2 * 2) := by rw [pow_mul]
      _ = 1 := hx4R
  have hx2ge : 0 ≤ (x : ℝ) ^ 2 := sq_nonneg _
  have hx2 : (x : ℝ) ^ 2 = 1 := by
    nlinarith
  have hx2wrap : x ^ 2 = 1 := by
    simpa using hx2
  have hI2 : (Complex.I : ℂ) ^ 2 = 1 := by
    calc
      (Complex.I : ℂ) ^ 2 = e (x ^ 2) := by simp [hx]
      _ = 1 := by simp [hx2wrap]
  have hI2ne : (Complex.I : ℂ) ^ 2 ≠ 1 := by
    intro h
    have h' : (1 : ℂ) = -1 := by
      calc
        (1 : ℂ) = (Complex.I : ℂ) ^ 2 := by symm; exact h
        _ = -1 := by simpa using Complex.sq_I
    norm_num at h'
  exact hI2ne hI2
