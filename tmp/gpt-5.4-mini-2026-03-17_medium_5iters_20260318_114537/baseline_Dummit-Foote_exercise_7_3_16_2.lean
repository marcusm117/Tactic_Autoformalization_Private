import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  rw [Set.mem_center_iff] at hz ⊢
  change ∀ s : S, s * φ z = φ z * s
  intro s
  rcases hf s with ⟨r, rfl⟩
  calc
    φ r * φ z = φ (r * z) := by rw [map_mul]
    _ = φ (z * r) := by rw [hz r]
    _ = φ z * φ r := by rw [map_mul]
