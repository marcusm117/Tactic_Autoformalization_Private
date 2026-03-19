import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  intro h
  classical
  have hdiv : p ∣ Fintype.card G := by
    rw [hG]
    exact dvd_mul_right _ _
  rcases hp.exists_orderOf_eq hdiv with ⟨x, hx⟩
  let H : Subgroup G := zpowers x
  have hHcard : Fintype.card H = p := by
    change Fintype.card (zpowers x) = p
    simpa [hx] using (Fintype.card_zpowers x)
  have hindex : Nat.Prime (Fintype.card G / Fintype.card H) := by
    rw [hG, hHcard]
    simpa using hq
  have hHnormal : H.Normal := Subgroup.normal_of_index_eq_prime hindex
  haveI : H.Normal := hHnormal
  have hbot : H ≠ ⊥ := by
    intro hbot
    have : p = 1 := by
      simpa [H, hbot] using hHcard.symm
    exact hp.ne_one this
  have htop : H ≠ ⊤ := by
    intro htop
    have hEq : p * q = p * 1 := by
      have : p * q = p := by
        simpa [H, htop] using hG
      simpa using this
    have hq1 : q = 1 := Nat.mul_left_cancel hp.ne_zero hEq
    exact hq.ne_one hq1
  have hcase := h.eq_bot_or_eq_top H
  rcases hcase with hcase | hcase
  · exact hbot hcase
  · exact htop hcase
