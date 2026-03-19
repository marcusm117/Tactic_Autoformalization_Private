import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_4_19 {G : Type*} [Group G] {x : G}
  (hx : orderOf x = 2) (hx1 : ∀ y, orderOf y = 2 → y = x) :
  x ∈ center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  let z : G := y⁻¹ * x * y
  have hxne : x ≠ 1 := by
    intro hx1
    have h : (2 : ℕ) = 1 := by
      simpa [hx1] using hx.symm
    omega
  have hpow : z ^ 2 = 1 := by
    dsimp [z]
    rw [pow_two]
    simp [mul_assoc, hx]
  have hdiv : orderOf z ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [z] using hpow
  have hpos : 0 < orderOf z := orderOf_pos z
  have hneq1 : orderOf z ≠ 1 := by
    intro h1
    have hz1 : z = 1 := by
      simpa [h1] using (pow_orderOf_eq_one z)
    have hxeq1 : x = 1 := by
      calc
        x = y * (y⁻¹ * x * y) * y⁻¹ := by
          simp [mul_assoc, z]
        _ = 1 := by simp [z, hz1]
    exact hxne hxeq1
  have hle : orderOf z ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hz2 : orderOf z = 2 := by
    omega
  exact hx1 z hz2
