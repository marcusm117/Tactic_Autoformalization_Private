import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators

theorem exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ := by
  intro a b h
  by_contra hne
  have h0 : φ (a - b) = 0 := by
    rw [map_sub, h, sub_self]
  have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hunit : φ (a - b) * φ ((a - b)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel hne', map_one]
    rfl
  rw [h0, zero_mul] at hunit
  exact zero_ne_one hunit
