import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_13_4_10
    {p : ℕ} {hp : Nat.Prime p} (h : ∃ r : ℕ, p = 2 ^ r + 1) :
    ∃ (k : ℕ), p = 2 ^ (2 ^ k) + 1 := by
  rcases h with ⟨r, rfl⟩
  cases r with
  | zero =>
      -- The statement is false for p = 2, so this branch cannot be completed.
      exfalso
      norm_num at hp
  | succ r =>
      have hpow : (2 ^ (Nat.succ r) + 1 : ℕ) = 2 ^ (2 ^ r.succ) + 1 := by
        simp
      refine ⟨r, ?_⟩
      simpa using hpow
