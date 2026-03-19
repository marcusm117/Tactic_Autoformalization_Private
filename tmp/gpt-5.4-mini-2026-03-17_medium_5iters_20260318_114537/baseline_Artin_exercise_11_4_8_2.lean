import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_8 (p : ℕ) (hp : Prime p) (n : ℕ) (hn : n > 0) :
  Irreducible (X ^ n - (p : Polynomial ℚ) : Polynomial ℚ) := by
  have hZ : Irreducible (X ^ n - (p : Polynomial ℤ)) := by
    simpa using
      (Polynomial.isEisenstein_X_pow_sub_C (R := ℤ) (p := (p : ℤ)) hp.cast_prime hn).irreducible
  exact hZ.map (Polynomial.map (Int.castRingHom ℚ)) (Polynomial.map_injective Int.cast_injective)
