import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  classical
  have hcard : Cardinal.mk (Fin n → ℝ) = Cardinal.mk ℝ := by
    simp
  exact Module.Free.nonempty_linearEquiv_of_card_eq (R := ℚ) (M := Fin n → ℝ) (N := ℝ) hcard
