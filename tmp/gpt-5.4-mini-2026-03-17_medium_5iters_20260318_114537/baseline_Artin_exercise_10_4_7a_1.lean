import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_4_7a {R : Type*} [CommRing R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨Ideal.mul_le_left hx, Ideal.mul_le_right hx⟩
  · intro x hx
    have hxIJ : x ∈ I ∧ x ∈ J := by simpa using hx
    rcases hxIJ with ⟨hxI, hxJ⟩
    have h1 : (1 : R) ∈ I + J := by
      simpa [hIJ]
    rcases Ideal.mem_sup.mp h1 with ⟨a, ha, b, hb, hab⟩
    have hxEq : x = a * x + b * x := by
      calc
        x = (1 : R) * x := by simp
        _ = (a + b) * x := by rw [← hab]
        _ = a * x + b * x := by rw [add_mul]
    rw [hxEq]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul ha hxJ) (by simpa [mul_comm] using Ideal.mul_mem_mul hxI hb)
