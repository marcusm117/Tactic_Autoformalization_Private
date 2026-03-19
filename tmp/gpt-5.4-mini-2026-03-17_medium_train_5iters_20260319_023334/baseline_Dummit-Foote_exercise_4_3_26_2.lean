import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_3_26 {α : Type*} [Fintype α] (ha : card α > 1)
  (h_tran : ∀ a b: α, ∃ σ : Equiv.Perm α, σ a = b) :
  ∃ σ : Equiv.Perm α, ∀ a : α, σ a ≠ a := by
  classical
  have h0 : Fintype.card α ≠ 0 := by
    omega
  rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, hm⟩
  let e : Fin (m + 1) ≃ α := by
    simpa [hm] using (Fintype.equivFin α).symm
  let τ : Equiv.Perm (Fin (m + 1)) := Fin.rotate
  have hτ : ∀ x : Fin (m + 1), τ x ≠ x := by
    intro x
    cases x using Fin.cases with
    | zero =>
        simp [τ]
    | succ i =>
        simp [τ]
  let σ : Equiv.Perm α := e.symm.trans τ.trans e
  refine ⟨σ, ?_⟩
  intro a
  intro hfix
  have hfix' : τ (e.symm a) = e.symm a := by
    have := congrArg e.symm hfix
    simpa [σ, Equiv.trans_apply] using this
  exact hτ (e.symm a) hfix'
