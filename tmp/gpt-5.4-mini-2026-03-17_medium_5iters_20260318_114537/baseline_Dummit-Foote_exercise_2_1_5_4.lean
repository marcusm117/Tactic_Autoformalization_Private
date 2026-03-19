import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  intro h
  have hdiv : card G - 1 ∣ card G := by
    refine ⟨H.index, ?_⟩
    simpa [h, Nat.mul_comm] using (H.index_mul_card (H := H))
  have hmod0 : card G % (card G - 1) = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hmod1 : card G % (card G - 1) = 1 := by
    have hlt : 1 < card G - 1 := by omega
    have hEq : card G = (card G - 1) + 1 := by omega
    rw [hEq]
    simp [Nat.add_mod_right_right, Nat.mod_eq_of_lt hlt]
  exfalso
  exact Nat.zero_ne_one (hmod0.trans hmod1)
