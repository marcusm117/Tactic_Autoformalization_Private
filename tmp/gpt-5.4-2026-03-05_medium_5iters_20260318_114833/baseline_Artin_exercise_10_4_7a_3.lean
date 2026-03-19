import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_4_7a {R : Type*} [CommRing R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J := by
  apply _root_.le_antisymm
  · exact Ideal.mul_le_inf
  · intro x hx
    have hxI : x ∈ I := hx.1
    have hxJ : x ∈ J := hx.2
    have h1 : (1 : R) ∈ (I + J : Ideal R) := by
      simpa [hIJ]
    have h1' : (1 : R) ∈ ((I : Submodule R R) ⊔ (J : Submodule R R)) := by
      simpa using h1
    rcases Submodule.mem_sup.mp h1' with ⟨i, hi, j, hj, hij⟩
    have hiI : i ∈ I := hi
    have hjJ : j ∈ J := hj
    have hxeq : x = i * x + x * j := by
      calc
        x = (1 : R) * x := by simp
        _ = (i + j) * x := by rw [← hij]
        _ = i * x + j * x := by rw [add_mul]
        _ = i * x + x * j := by rw [mul_comm j x]
    rw [hxeq]
    exact Ideal.add_mem (I * J) (Ideal.mul_mem_mul hiI hxJ) (Ideal.mul_mem_mul hxI hjJ)
