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
      exact False.elim (by
        norm_num at hr)
  | succ r =>
      rcases Nat.exists_eq_pow_two_mul_odd (r + 1) with ⟨m, n, hmn, hodd⟩
      cases n with
      | zero =>
          simp at hmn
      | succ n =>
          refine ⟨m, ?_⟩
          simpa [hr, hmn] using hr
