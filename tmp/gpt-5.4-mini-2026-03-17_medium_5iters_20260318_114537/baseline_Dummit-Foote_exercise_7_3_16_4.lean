import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  rw [Set.mem_center_iff] at hz ⊢
  intro s
  rcases hf s with ⟨r, rfl⟩
  calc
    φ z * φ r = φ (z * r) := by rw [map_mul]
    _ = φ (r * z) := by rw [hz r]
    _ = φ r * φ z := by rw [map_mul]
