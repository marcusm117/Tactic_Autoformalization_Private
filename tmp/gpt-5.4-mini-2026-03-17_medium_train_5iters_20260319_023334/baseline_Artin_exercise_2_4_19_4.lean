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
    have h : (1 : ℕ) = 2 := by
      simpa [hx1] using hx
    omega
  have hx2 : x ^ 2 = 1 := by
    simpa [hx] using (pow_orderOf_eq_one x)
  have hpow : z ^ 2 = 1 := by
    dsimp [z]
    rw [pow_two]
    group
    simpa [hx2]
  have hdiv : orderOf z ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hpow
  have hle : orderOf z ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hzneq : z ≠ 1 := by
    intro hz1
    have hx1' : x = 1 := by
      calc
        x = y * z * y⁻¹ := by
          dsimp [z]
          group
        _ = 1 := by rw [hz1]; simp
    exact hxne hx1'
  have hneq1 : orderOf z ≠ 1 := by
    intro h1
    have hz1 : z = 1 := by
      have := pow_orderOf_eq_one z
      simpa [h1] using this
    exact hzneq hz1
  have hz12 : orderOf z = 1 ∨ orderOf z = 2 := by
    omega
  have horder : orderOf z = 2 := by
    rcases hz12 with h1 | h2
    · exact False.elim (hneq1 h1)
    · exact h2
  have hxy : z = x := hx1 z horder
  calc
    y * x = y * z := by rw [← hxy]
    _ = x * y := by
      dsimp [z]
      group
