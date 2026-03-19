import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  refine ⟨?_⟩
  intro e
  let x : ℝ := e.symm Complex.I
  have hx : e x = Complex.I := by
    dsimp [x]
    exact e.apply_symm_apply Complex.I
  have hx4image : e (x ^ 4) = 1 := by
    calc
      e (x ^ 4) = (e x) ^ 4 := by
        simpa using e.map_pow x 4
      _ = Complex.I ^ 4 := by
        rw [hx]
      _ = 1 := by
        norm_num [Complex.I_sq]
  have hx4 : x ^ 4 = 1 := by
    apply e.injective
    rw [e.map_one]
    exact hx4image
  have hfac : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
    nlinarith [hx4]
  have hpos : 0 < x ^ 2 + 1 := by
    nlinarith [sq_nonneg x]
  have hplus : x ^ 2 + 1 ≠ 0 := ne_of_gt hpos
  have hx2sub : x ^ 2 - 1 = 0 := by
    exact (mul_eq_zero.mp hfac).resolve_right hplus
  have hx2 : x ^ 2 = 1 := by
    nlinarith [hx2sub]
  have hI2 : Complex.I ^ 2 = 1 := by
    calc
      Complex.I ^ 2 = (e x) ^ 2 := by
        rw [hx]
      _ = e (x ^ 2) := by
        symm
        simpa using e.map_pow x 2
      _ = e 1 := by
        rw [hx2]
      _ = 1 := by
        exact e.map_one
  have hIneq : Complex.I ^ 2 ≠ (1 : ℂ) := by
    norm_num [Complex.I_sq]
  exact hIneq hI2
