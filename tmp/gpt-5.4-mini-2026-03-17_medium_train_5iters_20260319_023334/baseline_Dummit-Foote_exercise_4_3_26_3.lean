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
  have hn0 : 0 < n := by
    omega
  let e : α ≃ Fin n := by
    simpa [n] using (Fintype.equivFin α)
  let f : Fin n → Fin n := fun x => ⟨(x.val + 1) % n, Nat.mod_lt _ hn0⟩
  let g : Fin n → Fin n := fun x => ⟨(x.val + (n - 1)) % n, Nat.mod_lt _ hn0⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    ext
    dsimp [f, g]
    by_cases hx : x.val + 1 < n
    · have h1 : (x.val + 1) % n = x.val + 1 := Nat.mod_eq_of_lt hx
      have hn1 : n - 1 < n := by omega
      have h2 : (n - 1) % n = n - 1 := Nat.mod_eq_of_lt hn1
      have hEq : x.val + 1 + (n - 1) = x.val + n := by omega
      rw [h1, h2, hEq, Nat.add_mod_right_right]
      exact Nat.mod_eq_of_lt x.2
    · have hxeq : x.val + 1 = n := by omega
      have hn1 : n - 1 < n := by omega
      rw [hxeq, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hn1]
      omega
  have hgf : Function.RightInverse g f := by
    intro x
    ext
    dsimp [f, g]
    by_cases hx0 : x.val = 0
    · subst hx0
      have hn1 : n - 1 < n := by omega
      rw [Nat.mod_eq_of_lt hn1]
      have hsum : n - 1 + 1 = n := by omega
      rw [hsum, Nat.mod_self]
    · have hxpos : 0 < x.val := Nat.pos_of_ne_zero hx0
      have hsum : x.val + (n - 1) = (x.val - 1) + n := by omega
      have hlt : x.val - 1 < n := by omega
      rw [hsum, Nat.add_mod_right_right, Nat.mod_eq_of_lt hlt]
      have hsucc : x.val - 1 + 1 = x.val := by omega
      rw [hsucc, Nat.mod_eq_of_lt x.2]
  let τ : Equiv.Perm (Fin n) :=
    { toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf }
  let σ : Equiv.Perm α := e.trans (τ.trans e.symm)
  refine ⟨σ, ?_⟩
  intro a
  intro hfix
  have hfix' : τ (e a) = e a := by
    have := congrArg e hfix
    simpa [σ, Equiv.trans_apply] using this
  exact by
    have := hfix' 
    exact hfg (e a) this
