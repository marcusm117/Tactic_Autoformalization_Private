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
  let e : α ≃ Fin n := by
    simpa [n] using (Fintype.equivFin α)
  let τ : Equiv.Perm (Fin n) := Equiv.addRight (1 : Fin n)
  have hτ : ∀ x : Fin n, τ x ≠ x := by
    intro x hx
    have h1 : x + (1 : Fin n) = x := by
      simpa [τ] using hx
    have h2 : x + (1 : Fin n) = x + 0 := by
      simpa using h1
    have hzero : (1 : Fin n) = 0 := by
      exact add_left_cancel h2
    have hnat : (1 : Nat) = 0 := by
      have hval := congrArg Fin.val hzero
      simpa [Nat.mod_eq_of_lt hn] using hval
    exact Nat.succ_ne_zero 0 hnat
  let σ : Equiv.Perm α := e.trans (τ.trans e.symm)
  refine ⟨σ, ?_⟩
  intro a
  intro hfix
  have hfix' : τ (e a) = e a := by
    have := congrArg e hfix
    simpa [σ, Equiv.trans_apply] using this
  exact hτ (e a) hfix'
