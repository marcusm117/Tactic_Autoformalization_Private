import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_3_2 {f g : Polynomial ℚ} (i j : ℕ)
  (hfg : ∀ n : ℕ, ∃ a : ℤ, (f*g).coeff = a) :
  ∃ a : ℤ, f.coeff i * g.coeff j = a := by
  rcases hfg (i + j) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa using ha
