import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  classical
  have h∞ : Cardinal.aleph0 ≤ Cardinal.mk ℝ := by
    simpa using (Cardinal.aleph0_le_mk (α := ℝ))
  have hcard : Cardinal.mk (Fin n → ℝ) = Cardinal.mk ℝ := by
    simpa using (Cardinal.power_nat_eq h∞ n)
  exact Module.Free.nonemptyLinearEquivOfCardEq (R := ℚ) (M := Fin n → ℝ) (N := ℝ) hcard
