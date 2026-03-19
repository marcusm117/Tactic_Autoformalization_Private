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
  have h0 : 0 < n := lt_trans Nat.zero_lt_one hn
  letI : Fact (0 < n) := ⟨h0⟩
  let e : α ≃ Fin n := by
    simpa [n] using (Fintype.equivFin α)
  let τ : Equiv.Perm (Fin n) := Equiv.addRight (1 : Fin n)
  have hτ : ∀ x : Fin n, τ x ≠ x := by
    intro x hx
    have hx' : x + (1 : Fin n) = x + 0 := by
      simpa [τ] using hx
    have hzero : (1 : Fin n) = 0 := by
      exact add_left_cancel hx'
    have hne : (1 : Fin n) ≠ 0 := by
      intro h
      have hNat : (1 : Nat) = 0 := by
        have := congrArg Fin.val h
        simpa [n, hn] using this
      omega
    exact hne hzero
  let σ : Equiv.Perm α := e.trans (τ.trans e.symm)
  refine ⟨σ, ?_⟩
  intro a hfix
  have hfix' : τ (e a) = e a := by
    have := congrArg e hfix
    simpa [σ, Equiv.trans_apply] using this
  exact hτ (e a) hfix'
