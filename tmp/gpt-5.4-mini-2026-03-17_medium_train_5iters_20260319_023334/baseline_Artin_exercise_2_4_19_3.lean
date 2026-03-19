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
    intro h
    subst h
    have hcontra : (1 : ℕ) = 2 := by
      simpa using hx
    exact Nat.one_ne_two hcontra
  have hx2 : x ^ 2 = 1 := by
    simpa [hx] using (pow_orderOf_eq_one x)
  have hpow : z ^ 2 = 1 := by
    dsimp [z]
    rw [pow_two]
    simp [mul_assoc, hx2]
  have hdiv : orderOf z ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hpow
  have hzneq : z ≠ 1 := by
    intro hz1
    have hx1' : x = 1 := by
      calc
        x = y * z * y⁻¹ := by
          dsimp [z]
          simp [mul_assoc]
        _ = 1 := by rw [hz1]; simp
    exact hxne hx1'
  have hpos : 0 < orderOf z := orderOf_pos z
  have hle : orderOf z ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hneq1 : orderOf z ≠ 1 := by
    intro h1
    have hz1 : z = 1 := by
      have hpow1 : z ^ 1 = 1 := by
        simpa [h1] using (pow_orderOf_eq_one z)
      simpa using hpow1
    exact hzneq hz1
  have hz2 : orderOf z = 2 := by
    omega
  have hxy : z = x := hx1 z hz2
  calc
    y * x = y * z := by rw [← hxy]
    _ = x * y := by
      dsimp [z]
      simp [mul_assoc]
