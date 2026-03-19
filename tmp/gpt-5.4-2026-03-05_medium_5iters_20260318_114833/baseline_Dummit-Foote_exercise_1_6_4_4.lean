import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  refine ⟨?_⟩
  intro e
  let x : Multiplicative ℝ := e.symm (Complex.I : Multiplicative ℂ)
  have hx : e x = (Complex.I : Multiplicative ℂ) := by
    dsimp [x]
    exact e.apply_symm_apply (Complex.I : Multiplicative ℂ)
  have hI4 : (Complex.I : Multiplicative ℂ) ^ 4 = 1 := by
    norm_num [pow_two, Complex.I_sq]
  have hx4 : x ^ 4 = 1 := by
    apply e.injective
    calc
      e (x ^ 4) = (e x) ^ 4 := by
        simpa using e.toMonoidHom.map_pow x 4
      _ = (Complex.I : Multiplicative ℂ) ^ 4 := by rw [hx]
      _ = 1 := hI4
  have hfac : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
    nlinarith [hx4]
  have hplus : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hx2sub : x ^ 2 - 1 = 0 := by
    exact (mul_eq_zero.mp hfac).resolve_right hplus
  have hx2 : x ^ 2 = 1 := by
    nlinarith [hx2sub]
  have hI2 : (Complex.I : Multiplicative ℂ) ^ 2 = 1 := by
    calc
      (Complex.I : Multiplicative ℂ) ^ 2 = (e x) ^ 2 := by rw [hx]
      _ = e (x ^ 2) := by
        symm
        simpa using e.toMonoidHom.map_pow x 2
      _ = e 1 := by rw [hx2]
      _ = 1 := e.map_one
  have hI2' : (Complex.I : ℂ) ^ 2 = (1 : ℂ) := by
    simpa using hI2
  have hne : (Complex.I : ℂ) ^ 2 ≠ (1 : ℂ) := by
    norm_num [Complex.I_sq]
  exact hne hI2'
