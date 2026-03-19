import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_1b :
  Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℚ) := by
  have hZ : Irreducible (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
    apply Polynomial.irreducible_of_eisenstein (p := 3)
    · norm_num
    · intro n hn
      fin_cases n <;> norm_num
    · norm_num
    · norm_num
  have hmono : Monic (12 + 6 * X + X ^ 3 : Polynomial ℤ) := by
    simp
  have hQ : Irreducible ((12 + 6 * X + X ^ 3 : Polynomial ℤ).map (Int.castRingHom ℚ)) := by
    exact (Polynomial.irreducible_iff_irreducible_map hmono).2 hZ
  simpa using hQ
