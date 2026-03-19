import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  intro h
  have hp_dvd : p ∣ card G := by
    rw [hG]
    exact dvd_mul_right _ _
  rcases hp.exists_subgroup_card hp_dvd with ⟨H, hHcard⟩
  have hindex : Nat.Prime (card G / card H) := by
    rw [hG, hHcard]
    simpa using hq
  have hHnormal : H.Normal := Subgroup.normal_of_index_eq_prime hindex
  haveI : H.Normal := hHnormal
  have hcase : H = ⊥ ∨ H = ⊤ := h.eq_bot_or_eq_top H
  rcases hcase with hbot | htop
  · have h1 : (1 : ℕ) = p := by
      simpa [hbot] using hHcard
    exact hp.ne_one h1.symm
  · have hEq : p = p * q := by
      simpa [htop, hG] using hHcard.symm
    have hEq' : p * 1 = p * q := by
      simpa using hEq
    have h1 : (1 : ℕ) = q := Nat.mul_left_cancel hp.ne_zero hEq'
    exact hq.ne_one h1.symm
