import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  have hmZ : (12 + 6 * X + X ^ 3 : Polynomial ℤ).Monic := by
    native_decide
  have hdeg : (12 + 6 * X + X ^ 3 : Polynomial ℤ).natDegree = 3 := by
    native_decide
  have hZ : Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
    refine
      Polynomial.irreducible_of_eisenstein_criterion
        (f := (12 + 6 * X + X ^ 3 : Polynomial ℤ)) (p := (3 : ℤ)) hmZ.isPrimitive
        ?_ ?_ ?_ ?_
    · decide
    · intro n hn
      have hn' : n < 3 := by
        simpa [hdeg] using hn
      interval_cases n <;> native_decide
    · native_decide
    · native_decide
  simpa using (hmZ.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).1 hZ
