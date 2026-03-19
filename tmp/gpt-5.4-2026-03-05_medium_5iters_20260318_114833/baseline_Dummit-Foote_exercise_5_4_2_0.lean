import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_5_4_2 {G : Type*} [Group G] (H : Subgroup G) :
  H.Normal ↔ ⁅(⊤ : Subgroup G), H⁆ ≤ H := by
  constructor
  · intro hN
    rw [Subgroup.commutator_le]
    intro g _ h hh
    first
      | change g * h * g⁻¹ * h⁻¹ ∈ H
        simpa [mul_assoc] using H.mul_mem (hN.conj_mem hh g) (H.inv_mem hh)
      | change g⁻¹ * h⁻¹ * g * h ∈ H
        simpa [mul_assoc] using H.mul_mem (hN.conj_mem (H.inv_mem hh) g⁻¹) hh
      | change h⁻¹ * g⁻¹ * h * g ∈ H
        simpa [mul_assoc] using H.mul_mem (H.inv_mem hh) (hN.conj_mem hh g⁻¹)
      | change h * g * h⁻¹ * g⁻¹ ∈ H
        simpa [mul_assoc] using H.mul_mem hh (hN.conj_mem (H.inv_mem hh) g)
  · intro hcomm
    refine ⟨?_⟩
    intro h hh g
    have hc := (Subgroup.commutator_le.mp hcomm) g (by simp) h hh
    have hc' := (Subgroup.commutator_le.mp hcomm) g (by simp) h⁻¹ (H.inv_mem hh)
    have hc₁ := (Subgroup.commutator_le.mp hcomm) g⁻¹ (by simp) h hh
    have hc₁' := (Subgroup.commutator_le.mp hcomm) g⁻¹ (by simp) h⁻¹ (H.inv_mem hh)
    first
      | change g * h * g⁻¹ ∈ H
        simpa [mul_assoc] using H.mul_mem hc hh
      | change g * h * g⁻¹ ∈ H
        simpa [mul_assoc] using H.mul_mem hc₁' hh
      | change g⁻¹ * h * g ∈ H
        simpa [mul_assoc] using H.mul_mem hc₁ hh
      | change g⁻¹ * h * g ∈ H
        simpa [mul_assoc] using H.mul_mem hc' hh
