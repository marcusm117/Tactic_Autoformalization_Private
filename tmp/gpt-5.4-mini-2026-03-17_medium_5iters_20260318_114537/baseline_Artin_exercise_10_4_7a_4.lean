import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_4_7a {R : Type*} [CommRing R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨Ideal.mul_le_right hx, Ideal.mul_le_left hx⟩
  · intro x hx
    have hxI : x ∈ I := hx.1
    have hxJ : x ∈ J := hx.2
    have h1 : (1 : R) ∈ I + J := by
      rw [hIJ]
      simp
    rcases Ideal.mem_sup.mp h1 with ⟨a, ha, b, hb, hab⟩
    have hax : a * x ∈ I * J := Ideal.mul_mem_mul ha hxJ
    have hbx : b * x ∈ I * J := by
      simpa [mul_comm] using (Ideal.mul_mem_mul hxI hb)
    have hxEq : x = a * x + b * x := by
      calc
        x = (1 : R) * x := by simp
        _ = (a + b) * x := by rw [← hab]
        _ = a * x + b * x := by rw [add_mul]
    rw [hxEq]
    exact (I * J).add_mem hax hbx
