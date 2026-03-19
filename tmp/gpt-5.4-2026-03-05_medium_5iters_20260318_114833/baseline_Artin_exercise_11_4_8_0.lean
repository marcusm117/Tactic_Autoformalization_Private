import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_8 (p : ℕ) (hp : Prime p) (n : ℕ) (hn : n > 0) :
  Irreducible (X ^ n - (p : Polynomial ℚ) : Polynomial ℚ) := by
  have hpz : Prime (p : ℤ) := by
    exact Int.prime_iff_natAbs_prime.2 (by simpa using hp)
  have h : Irreducible (X ^ n - C ((p : ℤ) : ℚ) : Polynomial ℚ) := by
    refine Polynomial.irreducible_X_pow_sub_C (R := ℤ) (p := (p : ℤ)) (n := n) ?_ ?_
    all_goals
      first
      | exact hpz
      | exact hn
      | exact Nat.ne_of_gt hn
  simpa using h
