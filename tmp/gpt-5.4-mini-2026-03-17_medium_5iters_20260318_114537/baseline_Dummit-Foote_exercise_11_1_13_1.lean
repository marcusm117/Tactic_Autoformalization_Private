import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  classical
  have hcard : Cardinal.mk (Fin n → ℝ) = Cardinal.mk ℝ := by
    simpa [Cardinal.mk_fun]
  have hlift : Cardinal.lift (Module.rank ℚ (Fin n → ℝ)) = Cardinal.lift (Module.rank ℚ ℝ) := by
    rw [Cardinal.lift_rank_eq (K := ℚ) (M := Fin n → ℝ), hcard, ← Cardinal.lift_rank_eq (K := ℚ) (M := ℝ)]
  have hrank : Module.rank ℚ (Fin n → ℝ) = Module.rank ℚ ℝ :=
    Cardinal.lift_injective hlift
  exact ⟨Module.Free.equiv (R := ℚ) (M := Fin n → ℝ) (N := ℝ) hrank⟩
