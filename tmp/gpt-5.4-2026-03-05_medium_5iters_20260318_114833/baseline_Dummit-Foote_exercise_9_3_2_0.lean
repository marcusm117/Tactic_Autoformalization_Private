import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_3_2 {f g : Polynomial ℚ} (i j : ℕ)
  (hfg : ∀ n : ℕ, ∃ a : ℤ, (f*g).coeff = a) :
  ∃ a : ℤ, f.coeff i * g.coeff j = a := by
  have hfg' : ∀ n : ℕ, IsInteger ((f * g).coeff n) := by
    intro n
    rcases hfg n with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  rcases Polynomial.isInteger_coeff_mul (f := f) (g := g) i j hfg' with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩
