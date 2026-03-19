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
    have hzero : a ≠ 0 := by
      intro h
      have : (1 : F) = 0 := by
        simpa [h] using ha
      exact one_ne_zero this
    have hpow : a ^ 6 = 1 := by
      simpa [hF] using Fintype.pow_card_sub_one_eq_one hzero
    have hEq : a ^ 2 = -1 := by
      have hrootEq : a ^ 2 + 1 = 0 := by
        simpa using ha
      linarith
    have hpow2 : a ^ 6 = -1 := by
      calc
        a ^ 6 = (a ^ 2) ^ 3 := by rw [pow_mul]
        _ = (-1) ^ 3 := by rw [hEq]
        _ = -1 := by norm_num
    have h1 : (1 : F) = -1 := by
      simpa [hpow] using hpow2
    have h2 : (2 : F) = 0 := by
      have := congrArg (fun x : F => x + 1) h1
      simpa using this
    have hneq : (2 : F) ≠ 0 := by
      norm_num
    exact hneq h2
  have hdeg : natDegree (X ^ 2 + 1 : Polynomial F) = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · simpa using (Polynomial.natDegree_X_pow (R := F) 2)
    · simp
  exact Polynomial.irreducible_of_natDegree_eq_two hdeg hroot
