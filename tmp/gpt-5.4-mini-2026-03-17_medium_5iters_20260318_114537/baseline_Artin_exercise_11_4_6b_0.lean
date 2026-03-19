import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6b {F : Type*} [Field F] [Fintype F] (hF : card F = 7) :
  Irreducible (X ^ 2 + 1 : Polynomial F) := by
  classical
  have hroot : ∀ a : F, ¬ IsRoot (X ^ 2 + 1 : Polynomial F) a := by
    intro a ha
    have hzero : a ≠ 0 := by
      intro h
      simp [h] at ha
    have hpow : a ^ 6 = 1 := by
      simpa [hF] using pow_card_sub_one_eq_one hzero
    have h2 : a ^ 2 = -1 := by
      linarith [ha]
    have hpow2 : a ^ 6 = -1 := by
      calc
        a ^ 6 = a ^ (2 * 3) := by norm_num
        _ = (a ^ 2) ^ 3 := by rw [pow_mul]
        _ = (-1) ^ 3 := by rw [h2]
        _ = -1 := by norm_num
    have h1 : (1 : F) = -1 := by
      simpa [hpow] using hpow2
    have h2zero : (2 : F) = 0 := by
      linarith
    have h7zero : (7 : F) = 0 := by
      have h := Fintype.card_nsmul_eq_zero (1 : F)
      simpa [hF] using h
    have h7one : (7 : F) = 1 := by
      norm_num [h2zero]
    have h01 : (0 : F) = 1 := by
      linarith [h7zero, h7one]
    exact zero_ne_one h01
  have hdeg : natDegree (X ^ 2 + 1 : Polynomial F) = 2 := by
    simp
  exact Polynomial.irreducible_of_natDegree_eq_two hdeg hroot
