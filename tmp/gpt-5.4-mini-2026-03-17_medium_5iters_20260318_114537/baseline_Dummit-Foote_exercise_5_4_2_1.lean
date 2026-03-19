import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_5_4_2 {G : Type*} [Group G] (H : Subgroup G) :
  H.Normal ↔ ⁅(⊤ : Subgroup G), H⁆ ≤ H := by
  constructor
  · intro hN
    rw [Subgroup.commutator_le]
    intro g _ h hh
    have hconj : g⁻¹ * h⁻¹ * g ∈ H := by
      simpa using hN.conj_mem (g := g⁻¹) hh.inv_mem
    have hprod : g⁻¹ * h⁻¹ * g * h ∈ H := H.mul_mem hconj hh
    simpa [mul_assoc] using hprod
  · intro hcomm
    rw [Subgroup.commutator_le] at hcomm
    refine ⟨?_⟩
    intro g h hh
    have hc : g * h * g⁻¹ * h⁻¹ ∈ H := by
      simpa [mul_assoc] using hcomm (g := g⁻¹) (by simp) (h := h⁻¹) hh.inv_mem
    have h1 : g * h * g⁻¹ ∈ H := by
      have := H.mul_mem hc hh
      simpa [mul_assoc] using this
    simpa using h1
