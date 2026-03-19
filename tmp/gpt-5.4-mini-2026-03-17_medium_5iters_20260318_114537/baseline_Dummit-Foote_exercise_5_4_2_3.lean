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
      simpa [mul_assoc] using hN.conj_mem g⁻¹ (H.inv_mem hh)
    have hprod : g⁻¹ * h⁻¹ * g * h ∈ H := H.mul_mem hconj hh
    simpa [mul_assoc] using hprod
  · intro hcomm
    rw [Subgroup.commutator_le] at hcomm
    refine ⟨?_⟩
    have hc : h * g * h⁻¹ * g⁻¹ ∈ H := by
      simpa [mul_assoc] using hcomm h⁻¹ (by simp) g⁻¹ (H.inv_mem hg)
    have h1 : h * g * h⁻¹ ∈ H := by
      have := H.mul_mem hc hg
      simpa [mul_assoc] using this
    simpa using h1
