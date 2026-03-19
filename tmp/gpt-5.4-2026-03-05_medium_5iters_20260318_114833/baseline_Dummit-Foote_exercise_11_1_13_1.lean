import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  classical
  refine ⟨LinearEquiv.ofLiftRankEq (R := ℚ) (M := Fin n → ℝ) (M' := ℝ) ?_⟩
  have hmul : (((n : ℕ) : Cardinal) * Cardinal.continuum) = Cardinal.continuum := by
    have hle : (((n : ℕ) : Cardinal)) ≤ Cardinal.continuum := by
      exact le_trans (le_of_lt (Cardinal.nat_lt_aleph0 _)) Cardinal.aleph0_le_continuum
    have hpos : (1 : Cardinal) ≤ (((n : ℕ) : Cardinal)) := by
      exact_mod_cast n.pos
    apply le_antisymm
    · calc
        (((n : ℕ) : Cardinal) * Cardinal.continuum) ≤ Cardinal.continuum * Cardinal.continuum := by
          exact Cardinal.mul_le_mul' hle le_rfl
        _ = Cardinal.continuum := by
          simpa using (Cardinal.mul_eq_self Cardinal.aleph0_le_continuum)
    · calc
        Cardinal.continuum = (1 : Cardinal) * Cardinal.continuum := by simp
        _ ≤ (((n : ℕ) : Cardinal) * Cardinal.continuum) := by
          exact Cardinal.mul_le_mul' hpos le_rfl
  have hrank : Module.rank ℚ (Fin n → ℝ) = Module.rank ℚ ℝ := by
    rw [Module.rank_fintype_fun, Module.rank_rat_real]
    simpa [Fintype.card_fin, mul_comm] using hmul
  simpa using congrArg Cardinal.lift hrank
