import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_4_7a {R : Type*} [CommRing R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨(Ideal.mul_le_left : I * J ≤ I) hx, (Ideal.mul_le_right : I * J ≤ J) hx⟩
  · intro x hx
    have hxI : x ∈ I := (inf_le_left : I ⊓ J ≤ I) hx
    have hxJ : x ∈ J := (inf_le_right : I ⊓ J ≤ J) hx
    have h1 : (1 : R) ∈ I + J := by
      have htop : (1 : R) ∈ (⊤ : Ideal R) := by simp
      simpa [hIJ] using htop
    rcases Ideal.mem_add.mp h1 with ⟨a, ha, b, hb, hab⟩
    have hxEq : x = a * x + b * x := by
      calc
        x = (1 : R) * x := by simp
        _ = (a + b) * x := by rw [← hab]
        _ = a * x + b * x := by rw [add_mul]
    rw [hxEq]
    exact (I * J).add_mem (Ideal.mul_mem_mul ha hxJ) (by
      simpa [mul_comm] using (Ideal.mul_mem_mul hxI hb))
