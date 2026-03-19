import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_13_4_10
    {p : ℕ} {hp : Nat.Prime p} (h : ∃ r : ℕ, p = 2 ^ r + 1) :
    ∃ (k : ℕ), p = 2 ^ (2 ^ k) + 1 := by
  rcases h with ⟨r, hr⟩
  cases r with
  | zero =>
      have h2 : (p = 2) := by simpa using hr
      have hcontra : False := by
        subst h2
        norm_num at hp
      exact False.elim hcontra
  | succ r =>
      refine ⟨r, ?_⟩
      simp [Nat.pow_succ, hr]
