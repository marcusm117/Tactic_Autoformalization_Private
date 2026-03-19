import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  let P : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hP : P.IsPrime := by
    simpa [P] using (Ideal.span_singleton_prime (show Prime (3 : ℤ) by norm_num))
  have hmZ : (12 + 6 * X + X ^ 3 : Polynomial ℤ).Monic := by
    decide
  have hdeg : (12 + 6 * X + X ^ 3 : Polynomial ℤ).natDegree = 3 := by
    decide
  have hZ : Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
    refine Polynomial.irreducible_of_eisenstein_criterion (P := P) hP ?_ ?_ ?_ ?_ ?_
    · simpa [P, Ideal.mem_span_singleton, hmZ.leadingCoeff] using
        (show ¬ ((3 : ℤ) ∣ 1) by norm_num)
    · intro i hi
      have hi' : i < 3 := by
        simpa [hdeg] using hi
      interval_cases i
      · change (12 : ℤ) ∈ P
        rw [P, Ideal.mem_span_singleton]
        norm_num
      · change (6 : ℤ) ∈ P
        rw [P, Ideal.mem_span_singleton]
        norm_num
      · change (0 : ℤ) ∈ P
        rw [P, Ideal.mem_span_singleton]
        norm_num
    · rw [Polynomial.degree_eq_natDegree hmZ.ne_zero, hdeg]
      norm_num
    · change ¬ ((12 : ℤ) ∈ P ^ 2)
      rw [P, pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton]
      norm_num
    · simpa [hmZ.leadingCoeff]
  simpa using (hmZ.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hZ
