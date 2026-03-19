import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_3_26 {α : Type*} [Fintype α] (ha : card α > 1)
  (h_tran : ∀ a b: α, ∃ σ : Equiv.Perm α, σ a = b) :
  ∃ σ : Equiv.Perm α, ∀ a : α, σ a ≠ a := by
  classical
  let n : ℕ := Fintype.card α
  have hn : 1 < n := by
    simpa [n] using ha
  letI : Fact (1 < n) := ⟨hn⟩
  let e : α ≃ Fin n := by
    simpa [n] using (Fintype.equivFin α)
  let τ : Equiv.Perm (Fin n) := Equiv.addRight (1 : Fin n)
  have hτ : ∀ x : Fin n, τ x ≠ x := by
    intro x hx
    have hval : (1 : Fin n).val = 1 := by
      simp
    have hne : (1 : Fin n) ≠ 0 := by
      intro h
      have hNat : (1 : Nat) = 0 := by
        simpa [hval] using congrArg Fin.val h
      omega
    have hx' : x + (1 : Fin n) = x := by
      simpa [τ] using hx
    have h' : x + (1 : Fin n) = x + 0 := by
      simpa using hx'
    have h2 : (1 : Fin n) = 0 := by
      exact add_left_cancel h'
    exact hne h2
  let σ : Equiv.Perm α := e.symm.trans (τ.trans e)
  refine ⟨σ, ?_⟩
  intro a
  intro hfix
  have hfix' : τ (e a) = e a := by
    simpa [σ, τ] using congrArg e hfix
  exact hτ (e a) hfix'
