import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  intro e
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by
    ext <;> simp [pow_two]
  have hI2ne : (Complex.I : ℂ) ^ 2 ≠ 1 := by
    intro h
    have : (1 : ℂ) = -1 := by
      simpa [h] using hI2
    norm_num at this
  let x : Multiplicative ℝ := e.symm (Complex.I)
  have hx4 : x ^ 4 = 1 := by
    have hx : e (x ^ (2 * 2)) = 1 := by
      simp [x, pow_mul, hI2]
    have hx' := e.injective hx
    simpa using hx'
  have hx2sq : (x ^ 2) ^ 2 = 1 := by
    have hx4' : x ^ (2 * 2) = 1 := by
      simpa using hx4
    simpa [pow_mul] using hx4'
  have hx2cases : x ^ 2 = 1 ∨ x ^ 2 = -1 := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).1 hx2sq
  have hx2 : x ^ 2 = 1 := by
    rcases hx2cases with hx2 | hx2
    · exact hx2
    · have hnonneg : (0 : ℝ) ≤ x ^ 2 := sq_nonneg _
      linarith
  have hmap : e (x ^ 2) = (Complex.I : ℂ) ^ 2 := by
    simp [x]
  have hmap' : (Complex.I : ℂ) ^ 2 = 1 := by
    simpa [hx2] using hmap.symm
  exact hI2ne hmap'
