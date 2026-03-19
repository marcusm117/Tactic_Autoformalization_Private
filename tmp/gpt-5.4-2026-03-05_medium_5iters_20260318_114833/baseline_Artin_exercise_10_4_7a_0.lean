import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_4_7a {R : Type*} [CommRing R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J := by
  apply le_antisymm
  · exact Ideal.mul_le_inf
  · intro x hx
    have hxI : x ∈ I := hx.1
    have hxJ : x ∈ J := hx.2
    have h1 : (1 : R) ∈ I + J := by
      rw [hIJ]
      simp
    rcases Ideal.mem_sup.mp h1 with ⟨i, hi, j, hj, hij⟩
    have hxeq : x = i * x + x * j := by
      calc
        x = 1 * x := by simp
        _ = (i + j) * x := by rw [← hij]
        _ = i * x + j * x := by rw [add_mul]
        _ = i * x + x * j := by rw [mul_comm j x]
    rw [hxeq]
    exact Ideal.add_mem (I * J) (Ideal.mul_mem_mul hi hxJ) (Ideal.mul_mem_mul hxI hj)
