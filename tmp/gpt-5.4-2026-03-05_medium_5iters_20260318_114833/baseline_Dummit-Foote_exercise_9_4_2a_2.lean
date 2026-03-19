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
    have hne0 : 0 ≠ n := by omega
    have hne3 : 3 ≠ n := by omega
    have hne4 : 4 ≠ n := by omega
    simp [hne0, hne3, hne4]
  have hcoeff4 : ((X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).coeff 4) ≠ 0 := by
    simp
  have hdeg : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).natDegree = 4 := by
    exact le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero hcoeff4)
  have hlc : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_eq_coeff_natDegree, hdeg]
    simp
  have hmonic : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).Monic := by
    show (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).leadingCoeff = 1
    exact hlc
  refine Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span ({(2 : ℤ)} : Set ℤ)) hP ?_ ?_ ?_ ?_ ?_
  · simpa [hlc, Ideal.mem_span_singleton] using (show ¬ ((2 : ℤ) ∣ 1) by norm_num)
  · intro n hn
    have hn4 : n < 4 := lt_of_lt_of_le hn hdeg_le
    interval_cases n <;> norm_num [Ideal.mem_span_singleton]
  · simpa [pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] using
      (show ¬ ((4 : ℤ) ∣ 6) by norm_num)
  · have h4le :
      (4 : WithBot ℕ) ≤ (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).degree :=
      Polynomial.le_degree_of_ne_zero hcoeff4
    exact lt_of_lt_of_le (by norm_num) h4le
  · exact hmonic.isPrimitive
