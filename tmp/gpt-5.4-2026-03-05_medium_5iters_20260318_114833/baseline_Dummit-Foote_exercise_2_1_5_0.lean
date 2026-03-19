import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  intro h
  have hdvd : card H ∣ card G := H.card_subgroup_dvd_card
  rw [h] at hdvd
  have hdiv1 : card G - 1 ∣ 1 := by
    have hsub : card G - (card G - 1) = 1 := by
      omega
    have htmp : card G - 1 ∣ card G - (card G - 1) := by
      exact Nat.dvd_sub' hdvd (dvd_refl (card G - 1))
    simpa [hsub] using htmp
  have hone : card G - 1 = 1 := Nat.eq_one_of_dvd_one hdiv1
  omega
