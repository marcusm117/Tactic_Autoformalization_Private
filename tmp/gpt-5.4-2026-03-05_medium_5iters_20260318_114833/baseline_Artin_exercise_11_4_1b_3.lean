import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  let P : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hP : P.IsPrime := by
    rw [P, Ideal.span_singleton_prime (show (3 : ℤ) ≠ 0 by norm_num)]
    norm_num
  have hdeg : (12 + 6 * X + X ^ 3 : Polynomial ℤ).natDegree = 3 := by
    have hlt : ((12 + 6 * X : Polynomial ℤ)).natDegree < (X ^ 3 : Polynomial ℤ).natDegree := by
      simp
    calc
      (12 + 6 * X + X ^ 3 : Polynomial ℤ).natDegree
          = ((12 + 6 * X : Polynomial ℤ) + X ^ 3).natDegree := rfl
      _ = (X ^ 3 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
      _ = 3 := by simp
  have hmZ : (12 + 6 * X + X ^ 3 : Polynomial ℤ).Monic := by
    rw [Polynomial.monic, Polynomial.leadingCoeff_eq_coeff_natDegree, hdeg]
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  have hZ : Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
    refine Polynomial.irreducible_of_eisenstein_criterion (P := P) hP ?_ ?_ ?_ ?_ ?_
    · simpa [P, Ideal.mem_span_singleton, hmZ.leadingCoeff] using
        (show ¬ ((3 : ℤ) ∣ 1) by norm_num)
    · intro i hi
      have hi' : i < 3 := by simpa [hdeg] using hi
      interval_cases i
      · simpa [P, Ideal.mem_span_singleton, Polynomial.coeff_add, Polynomial.coeff_X,
          Polynomial.coeff_X_pow] using (show (3 : ℤ) ∣ 12 by norm_num)
      · simpa [P, Ideal.mem_span_singleton, Polynomial.coeff_add, Polynomial.coeff_X,
          Polynomial.coeff_X_pow] using (show (3 : ℤ) ∣ 6 by norm_num)
      · simpa [P, Ideal.mem_span_singleton, Polynomial.coeff_add, Polynomial.coeff_X,
          Polynomial.coeff_X_pow] using (show (3 : ℤ) ∣ 0 by norm_num)
    · rw [Polynomial.degree_eq_natDegree hmZ.ne_zero, hdeg]
      norm_num
    · simpa [P, pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton,
        Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_X_pow] using
        (show ¬ ((9 : ℤ) ∣ 12) by norm_num)
    · simpa [hmZ.leadingCoeff] using (isUnit_one : IsUnit (1 : ℤ))
  simpa using (hmZ.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).1 hZ
