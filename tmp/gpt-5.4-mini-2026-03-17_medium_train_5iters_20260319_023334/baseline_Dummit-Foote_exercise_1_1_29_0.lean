import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_29 {A B : Type*} [Group A] [Group B] :
  (∀ x y : A × B, x*y = y*x) ↔ (∀ x y : A, x*y = y*x) ∧
  (∀ x y : B, x*y = y*x) := by
  constructor
  · intro h
    constructor
    · intro x y
      have h' := h (x, 1) (y, 1)
      simpa using congrArg Prod.fst h'
    · intro x y
      have h' := h (1, x) (1, y)
      simpa using congrArg Prod.snd h'
  · intro h
    intro x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    rcases h with ⟨ha, hb⟩
    ext <;> simp [ha a c, hb b d]
