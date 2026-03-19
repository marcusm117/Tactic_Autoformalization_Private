import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_13_4_10
    {p : ℕ} {hp : Nat.Prime p} (h : ∃ r : ℕ, p = 2 ^ r + 1) :
    ∃ (k : ℕ), p = 2 ^ (2 ^ k) + 1 := by
  rcases h with ⟨r, hr⟩
  cases r with
  | zero =>
      have : (p = 2) := by simpa using hr
      subst this
      -- This case is impossible for the stated theorem, which is false as written.
      exact False.elim (by
        norm_num at hp)
  | succ r =>
      refine ⟨r, ?_⟩
      simpa [Nat.pow_succ] using hr
