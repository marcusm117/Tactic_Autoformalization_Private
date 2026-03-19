import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  let P : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hP : P.IsPrime := by
    simpa [P] using (Ideal.span_singleton_prime.mpr (show Prime (3 : ℤ) by norm_num))
  have hmZ : (12 + 6 * X + X ^ 3 : Polynomial ℤ).Monic := by
    change (12 + 6 * X + X ^ 3 : Polynomial ℤ).leadingCoeff = 1
    simp
  have hdeg : (12 + 6 * X + X ^ 3 : Polynomial ℤ).natDegree = 3 := by
    simp
  have hZ : Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
    refine Polynomial.irreducible_of_eisenstein_criterion (P := P) hP ?_ ?_ ?_ ?_ ?_
    · simpa [P, Ideal.mem_span_singleton] using (show ¬ ((3 : ℤ) ∣ 1) by norm_num)
    · intro i hi
      have hi' : i < 3 := by simpa [hdeg] using hi
      interval_cases i
      · simpa [P, Ideal.mem_span_singleton] using (show ((3 : ℤ) ∣ 12) by norm_num)
      · simpa [P, Ideal.mem_span_singleton] using (show ((3 : ℤ) ∣ 6) by norm_num)
      · simpa [P, Ideal.mem_span_singleton] using (show ((3 : ℤ) ∣ 0) by norm_num)
    · simpa [P, pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] using
        (show ¬ ((3 * 3 : ℤ) ∣ 12) by norm_num)
    · simp
    · simp
  simpa using (hmZ.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hZ
