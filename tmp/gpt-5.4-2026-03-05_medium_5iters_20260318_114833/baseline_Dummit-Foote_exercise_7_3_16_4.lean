import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := by
  rintro s ⟨z, hz, rfl⟩
  rw [Set.mem_center_iff] at hz ⊢
  intro x
  rcases hf x with ⟨y, rfl⟩
  simpa [map_mul] using congrArg φ (hz y)
