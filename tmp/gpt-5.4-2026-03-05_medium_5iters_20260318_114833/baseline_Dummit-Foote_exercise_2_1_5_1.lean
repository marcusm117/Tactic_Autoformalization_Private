import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  intro h
  have hdvd_nat : Nat.card H ∣ Nat.card G := H.card_subgroup_dvd_card
  have hdvd : Fintype.card H ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using hdvd_nat
  rw [h] at hdvd
  have hdiv1 : Fintype.card G - 1 ∣ 1 := by
    have htmp : Fintype.card G - 1 ∣ Fintype.card G - (Fintype.card G - 1) := by
      exact Nat.dvd_sub hdvd (dvd_refl (Fintype.card G - 1))
    have hsub : Fintype.card G - (Fintype.card G - 1) = 1 := by
      omega
    simpa [hsub] using htmp
  have hone : Fintype.card G - 1 = 1 := Nat.eq_one_of_dvd_one hdiv1
  omega
