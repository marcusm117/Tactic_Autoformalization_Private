import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hP : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 by norm_num)]
    norm_num
  have hdeg_le : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).natDegree ≤ 4 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 ?_
    intro n hn
    have h4 : 4 ≠ n := by omega
    have h3 : 3 ≠ n := by omega
    have h0 : 0 ≠ n := by omega
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, h4, h3, h0]
  have hcoeff4 : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).coeff 4 = 1 := by
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
  have hcoeff4_ne : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).coeff 4 ≠ 0 := by
    rw [hcoeff4]
    norm_num
  have hdeg : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).natDegree = 4 := by
    exact le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero hcoeff4_ne)
  have hp_ne : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ) ≠ 0 := by
    intro h
    have := congrArg (fun p : Polynomial ℤ => p.coeff 4) h
    simpa [hcoeff4] using this
  have hdegree : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).degree = 4 := by
    rw [Polynomial.degree_eq_natDegree hp_ne, hdeg]
  have hlc : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).leadingCoeff = 1 := by
    rw [← Polynomial.coeff_natDegree, hdeg]
    exact hcoeff4
  refine Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span ({(2 : ℤ)} : Set ℤ)) hP ?_ ?_ ?_ ?_ ?_
  · simpa [hlc, Ideal.mem_span_singleton] using (show ¬ ((2 : ℤ) ∣ 1) by norm_num)
  · intro n hn
    have hn4 : n < 4 := by
      rw [hdegree] at hn
      simpa using hn
    interval_cases n <;> norm_num [Ideal.mem_span_singleton, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  · rw [hdegree]
    norm_num
  · simpa [pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton,
      Polynomial.coeff_X_pow, Polynomial.coeff_C] using
      (show ¬ ((4 : ℤ) ∣ 6) by norm_num)
  · simpa [hlc] using (isUnit_one : IsUnit (1 : ℤ))
