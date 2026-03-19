import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_8 (p : ℕ) (hp : Prime p) (n : ℕ) (hn : n > 0) :
  Irreducible (X ^ n - (p : Polynomial ℚ) : Polynomial ℚ) := by
  have hpn : Nat.Prime p := by
    simpa [Nat.prime_iff] using hp
  have hpz : Prime (p : ℤ) := by
    exact Int.prime_iff_natAbs_prime.2 (by simpa using hpn)
  simpa using hpz.irreducible_X_pow_sub_C (K := ℚ) (n := n) (Nat.ne_of_gt hn)
