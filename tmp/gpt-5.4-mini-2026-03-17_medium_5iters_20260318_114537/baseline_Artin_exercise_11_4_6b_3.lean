import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6b {F : Type*} [Field F] [Fintype F] (hF : card F = 7) :
  Irreducible (X ^ 2 + 1 : Polynomial F) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  haveI : CharP F 7 := charP_of_card_eq_prime hF
  have hroot : ∀ a : F, ¬ IsRoot (X ^ 2 + 1 : Polynomial F) a := by
    intro a ha
    have hEq : a ^ 2 + 1 = 0 := by
      simpa using ha
    have hsq : a ^ 2 = -1 := by
      linarith
    have hpow7 : a ^ 7 = a := by
      simpa [hF] using (pow_card a)
    have h6 : a ^ 6 = -1 := by
      calc
        a ^ 6 = (a ^ 2) ^ 3 := by rw [pow_mul]
        _ = (-1) ^ 3 := by rw [hsq]
        _ = -1 := by norm_num
    have h7neg : a ^ 7 = -a := by
      calc
        a ^ 7 = a ^ 6 * a := by rw [pow_succ]
        _ = -1 * a := by rw [h6]
        _ = -a := by simp
    have hEq2 : a = -a := by
      exact hpow7.symm.trans h7neg
    have hsum : a + a = 0 := by
      linarith
    have h2a : (2 : F) * a = 0 := by
      simpa [two_mul] using hsum
    have h2ne : (2 : F) ≠ 0 := by
      norm_num
    have ha0 : a = 0 := by
      exact (mul_eq_zero.mp h2a).resolve_left h2ne
    have : (1 : F) = 0 := by
      simpa [ha0] using hEq
    exact one_ne_zero this
  have hdeg : degree (X ^ 2 + 1 : Polynomial F) = 2 := by
    simp
  exact Polynomial.irreducible_of_degree_eq_two hdeg hroot
