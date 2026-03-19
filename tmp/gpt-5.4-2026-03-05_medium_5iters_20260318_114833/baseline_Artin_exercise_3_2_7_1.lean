import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators

theorem exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ := by
  intro a b h
  by_contra hne
  have hsub : φ (a - b) = 0 := by
    rw [map_sub, h, sub_self]
  have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hmul : φ (a - b) * φ ((a - b)⁻¹) = 1 := by
    calc
      φ (a - b) * φ ((a - b)⁻¹) = φ ((a - b) * (a - b)⁻¹) := by
        rw [map_mul]
      _ = φ 1 := by
        rw [mul_inv_cancel₀ hne']
      _ = 1 := by
        rw [map_one]
  rw [hsub, zero_mul] at hmul
  exact zero_ne_one hmul
