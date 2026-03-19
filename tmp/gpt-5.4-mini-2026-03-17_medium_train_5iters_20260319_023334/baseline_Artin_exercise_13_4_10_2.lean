import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_13_4_10
    {p : ℕ} {hp : Nat.Prime p} (h : ∃ r : ℕ, p = 2 ^ r + 1) :
    ∃ (k : ℕ), p = 2 ^ (2 ^ k) + 1 := by
  rcases h with ⟨r, hr⟩
  cases r with
  | zero =>
      have hp2 : p = 2 := by simpa using hr
      subst hp2
      refine ⟨0, by norm_num⟩
  | succ r =>
      rcases Nat.exists_eq_pow_two_of_ne_zero (by
        intro hr0
        subst hr0
        norm_num at hr) with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      subst hk
      simpa [Nat.pow_succ] using hr
