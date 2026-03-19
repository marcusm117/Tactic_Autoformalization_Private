import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  refine ⟨?_⟩
  intro e
  let x : Multiplicative ℝ := e.symm Complex.I
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by
    simpa using Complex.sq_I
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hI2]
    norm_num
  have hx4 : x ^ 4 = 1 := by
    apply e.injective
    simp [x, hI4]
  have hsq : (x ^ 2) ^ 2 = (1 : ℝ) ^ 2 := by
    calc
      (x ^ 2) ^ 2 = x ^ (2 * 2) := by rw [← pow_mul]
      _ = 1 := by simpa using hx4
  have hx2cases : x ^ 2 = 1 ∨ x ^ 2 = -1 := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).1 hsq
  have hx2 : x ^ 2 = 1 := by
    rcases hx2cases with hx2 | hx2
    · exact hx2
    · have hnonneg : 0 ≤ x ^ 2 := sq_nonneg x
      linarith
  have hx : x = 1 ∨ x = -1 := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).1 (by simpa using hx2)
  have hxe : e x = Complex.I := by
    simp [x]
  have hi1 : (Complex.I : ℂ) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
    exact h'
  have hiNeg1 : (Complex.I : ℂ) ≠ -1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
    exact h'
  rcases hx with rfl | rfl
  · have h : (1 : ℂ) = Complex.I := by simpa using hxe
    exact hi1 h.symm
  · have h : ((-1 : ℝ) : ℂ) = Complex.I := by simpa using hxe
    exact hiNeg1 h.symm
