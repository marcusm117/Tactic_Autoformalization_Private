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
      rw [eq_neg_iff_add_eq_zero]
      exact hEq
    have hzero : a ≠ 0 := by
      intro h0
      have : (1 : F) = 0 := by
        simpa [h0] using hEq
      exact one_ne_zero this
    have hpow : a ^ 6 = 1 := by
      have h := FiniteField.pow_card_sub_one_eq_one (K := F) a hzero
      simpa [hF] using h
    have h4 : a ^ 4 = 1 := by
      calc
        a ^ 4 = a ^ (2 * 2) := by norm_num
        _ = (a ^ 2) ^ 2 := by rw [pow_mul]
        _ = (-1) ^ 2 := by rw [hsq]
        _ = 1 := by norm_num
    have h2eq1 : a ^ 2 = 1 := by
      have h26 : a ^ 6 = a ^ 2 := by
        calc
          a ^ 6 = a ^ (2 + 4) := by norm_num
          _ = a ^ 2 * a ^ 4 := by rw [pow_add]
          _ = a ^ 2 := by rw [h4, mul_one]
      exact h26.symm.trans hpow
    have h1 : (1 : F) = -1 := by
      calc
        (1 : F) = a ^ 2 := by symm; exact h2eq1
        _ = -1 := hsq
    have h2ne : (2 : F) ≠ 0 := by
      norm_num
    have h2zero : (2 : F) = 0 := by
      have h := congrArg (fun x : F => x + 1) h1
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using h
    exact h2ne h2zero
  have hdeg : degree (X ^ 2 + 1 : Polynomial F) = 2 := by
    simp
  exact Polynomial.irreducible_of_degree_eq_two hdeg hroot
