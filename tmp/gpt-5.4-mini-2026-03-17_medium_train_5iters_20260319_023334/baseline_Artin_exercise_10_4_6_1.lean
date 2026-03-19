import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_4_6 {R : Type*} [CommRing R]
  (I J : Ideal R) (x : ↑(I ⊓ J)) :
  IsNilpotent ((Ideal.Quotient.mk (I*J)) x) := by
  refine ⟨2, ?_⟩
  rw [pow_two, ← map_mul]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mul_mem_mul x.property.left x.property.right)
