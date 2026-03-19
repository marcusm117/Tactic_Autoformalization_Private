import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  refine (Set.mem_center_iff).2 ?_
  constructor
  intro s
  rcases hf s with ⟨r, rfl⟩
  have hz' : IsMulCentral z := Set.mem_center_iff.mp hz
  calc
    φ r * φ z = φ (r * z) := by rw [map_mul]
    _ = φ (z * r) := by rw [hz'.mul_comm r]
    _ = φ z * φ r := by rw [map_mul]
