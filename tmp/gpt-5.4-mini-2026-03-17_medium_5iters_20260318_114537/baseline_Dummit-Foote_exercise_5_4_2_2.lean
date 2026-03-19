import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_5_4_2 {G : Type*} [Group G] (H : Subgroup G) :
  H.Normal ↔ ⁅(⊤ : Subgroup G), H⁆ ≤ H := by
  constructor
  · intro hN
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have hgh : g * h * g⁻¹ ∈ H := hN.conj_mem (g := g) hh
    simpa [mul_assoc] using H.mul_mem hgh hh.inv_mem
  · intro hcomm
    rw [Subgroup.commutator_le] at hcomm
    refine ⟨?_⟩
    intro g hg h hh
    have hgh : g * h * g⁻¹ * h⁻¹ ∈ H := by
      simpa [mul_assoc] using hcomm g hg h hh
    have := H.mul_mem hgh hh
    simpa [mul_assoc] using this
