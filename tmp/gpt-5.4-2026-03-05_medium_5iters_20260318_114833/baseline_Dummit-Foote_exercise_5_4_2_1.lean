import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_5_4_2 {G : Type*} [Group G] (H : Subgroup G) :
  H.Normal ↔ ⁅(⊤ : Subgroup G), H⁆ ≤ H := by
  constructor
  · intro hN
    rw [Subgroup.commutator_le]
    intro g _ h hh
    change g * h * g⁻¹ * h⁻¹ ∈ H
    exact H.mul_mem (hN.conj_mem hh g) (H.inv_mem hh)
  · intro hcomm
    refine ⟨?_⟩
    intro h hh g
    have hc : ⁅g, h⁆ ∈ H := (Subgroup.commutator_le.mp hcomm) g (by simp) h hh
    simpa [mul_assoc] using H.mul_mem hc hh
