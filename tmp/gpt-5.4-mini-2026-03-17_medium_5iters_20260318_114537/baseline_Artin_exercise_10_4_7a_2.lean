import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_4_7a {R : Type*} [CommRing R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J := by
  ext x
  constructor
  · intro hx
    exact ⟨Ideal.mul_le_left hx, Ideal.mul_le_right hx⟩
  · intro hx
    have hxIJ : x ∈ I ∧ x ∈ J := by simpa using hx
    rcases hxIJ with ⟨hxI, hxJ⟩
    have h1 : (1 : R) ∈ I + J := by
      rw [hIJ]
      simp
    rcases Ideal.mem_add.mp h1 with ⟨a, ha, b, hb, hab⟩
    have hax : a * x ∈ I * J := Ideal.mul_mem_mul ha hxJ
    have hbx : b * x ∈ I * J := by
      simpa [mul_comm] using (Ideal.mul_mem_mul hxI hb)
    have hxEq : x = a * x + b * x := by
      calc
        x = (1 : R) * x := by simp
        _ = (a + b) * x := by rw [← hab]
        _ = a * x + b * x := by rw [add_mul]
    simpa [hxEq] using (I * J).add_mem hax hbx
