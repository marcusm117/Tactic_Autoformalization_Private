import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  intro h
  have hdiv : card H ∣ card G := by
    have hmul := H.index_mul_card
    exact ⟨H.index, by simpa [Nat.mul_comm] using hmul⟩
  have hdiv' : card G - 1 ∣ card G := by
    simpa [h] using hdiv
  have h1 : card G - 1 ∣ 1 := by
    have htmp := Nat.dvd_sub' (dvd_refl (card G - 1)) hdiv'
    have hsub : card G - (card G - 1) = 1 := by omega
    simpa [hsub] using htmp
  have hEq : card G - 1 = 1 := Nat.eq_one_of_dvd_one h1
  have hG2 : card G = 2 := by omega
  omega
