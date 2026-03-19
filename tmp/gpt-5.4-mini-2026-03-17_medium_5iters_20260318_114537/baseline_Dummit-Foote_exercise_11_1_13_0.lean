import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  classical
  refine ⟨Module.Free.linearEquiv (R := ℚ) (M := Fin n → ℝ) (N := ℝ) ?_⟩
  have h1 : Cardinal.lift (Module.rank ℚ (Fin n → ℝ)) = Cardinal.mk (Fin n → ℝ) := by
    simpa using (Cardinal.lift_rank_eq (K := ℚ) (M := Fin n → ℝ))
  have h2 : Cardinal.lift (Module.rank ℚ ℝ) = Cardinal.mk ℝ := by
    simpa using (Cardinal.lift_rank_eq (K := ℚ) (M := ℝ))
  have hcard : Cardinal.mk (Fin n → ℝ) = Cardinal.mk ℝ := by
    simp [Cardinal.mk_fun]
  have h : Cardinal.lift (Module.rank ℚ (Fin n → ℝ)) = Cardinal.lift (Module.rank ℚ ℝ) := by
    rw [h1, h2, hcard]
  exact Cardinal.lift_injective h
