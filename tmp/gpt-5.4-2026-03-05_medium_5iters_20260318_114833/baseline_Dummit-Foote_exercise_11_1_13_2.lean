import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  classical
  have hpair : Nonempty ((ℝ × ℝ) ≃ₗ[ℚ] ℝ) := by
    refine ⟨LinearEquiv.ofLiftRankEq (R := ℚ) (M := ℝ × ℝ) (M' := ℝ) ?_⟩
    have hrank : Module.rank ℚ (ℝ × ℝ) = Module.rank ℚ ℝ := by
      rw [Module.rank_prod, Module.rank_rat_real, Module.rank_rat_real,
        Cardinal.add_eq_self Cardinal.aleph0_le_continuum]
    simpa using congrArg Cardinal.lift hrank
  let e₂ : (ℝ × ℝ) ≃ₗ[ℚ] ℝ := Classical.choice hpair
  have hsplit : ∀ m : ℕ, (Fin (m + 1) → ℝ) ≃ₗ[ℚ] (ℝ × (Fin m → ℝ)) := by
    intro m
    refine
      { toFun := fun f => (Fin.head f, Fin.tail f)
        invFun := fun p => Fin.cons p.1 p.2
        map_add' := by
          intro f g
          ext <;> simp
        map_smul' := by
          intro a f
          ext <;> simp
        left_inv := by
          intro f
          simpa using Fin.cons_head_tail f
        right_inv := by
          intro p
          rcases p with ⟨x, f⟩
          ext <;> simp }
  have hrec : ∀ m : ℕ, Nonempty ((Fin (m + 1) → ℝ) ≃ₗ[ℚ] ℝ) := by
    intro m
    induction m with
    | zero =>
        simpa using (LinearEquiv.funUnique (R := ℚ) (M := ℝ) (α := Fin 1))
    | succ m ihm =>
        rcases ihm with ⟨e⟩
        refine ⟨?_⟩
        simpa [Nat.add_assoc] using
          (hsplit (m + 1)).trans (((LinearEquiv.refl ℝ).prodCongr e).trans e₂)
  let m : ℕ := (n : ℕ) - 1
  have hm : m + 1 = (n : ℕ) := by
    dsimp [m]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)
  change Nonempty ((Fin ((n : ℕ)) → ℝ) ≃ₗ[ℚ] ℝ)
  rw [← hm]
  exact hrec m
