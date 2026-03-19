import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators

theorem exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ := by
  intro a b h
  have hsub : φ (a - b) = 0 := by
    rw [map_sub, h, sub_self]
  by_cases hzero : a - b = 0
  · exact sub_eq_zero.mp hzero
  · exfalso
    have hne' : a - b ≠ 0 := hzero
    have h1 : φ (a - b) * φ ((a - b)⁻¹) = 1 := by
      calc
        φ (a - b) * φ ((a - b)⁻¹) = φ ((a - b) * (a - b)⁻¹) := by rw [map_mul]
        _ = 1 := by rw [mul_inv_cancel₀ hne', map_one]
    rw [hsub, zero_mul] at h1
    exact zero_ne_one h1
