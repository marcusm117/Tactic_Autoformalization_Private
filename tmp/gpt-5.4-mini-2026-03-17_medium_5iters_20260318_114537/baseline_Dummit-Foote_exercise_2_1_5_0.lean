import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  intro h
  have hdiv : card H ∣ card G := H.card_dvd_card
  have hEq : card G = card H + 1 := by
    omega
  have hdiv' : card H ∣ card H + 1 := by
    simpa [hEq] using hdiv
  have h1 : card H ∣ 1 := by
    simpa using (Nat.dvd_sub' hdiv' (dvd_refl _) (Nat.le_add_right _ _))
  have hH1 : card H = 1 := Nat.eq_one_of_dvd_one h1
  have hG2 : card G = 2 := by
    omega
  omega
