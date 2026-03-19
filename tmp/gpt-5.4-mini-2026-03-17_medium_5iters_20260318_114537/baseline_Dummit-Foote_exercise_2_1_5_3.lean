import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  intro h
  have hmul : card G = card H * H.index := by
    have hmul' := H.index_mul_card
    rw [Nat.mul_comm] at hmul'
    exact hmul'.symm
  have hEq : card G = (card G - 1) * H.index := by
    simpa [h] using hmul
  by_cases hindex0 : H.index = 0
  · subst hindex0
    omega
  · by_cases hindex1 : H.index = 1
    · subst hindex1
      omega
    · have hindex2 : 2 ≤ H.index := by omega
      have hle' : 2 * (card G - 1) ≤ (card G - 1) * H.index := by
        have := Nat.mul_le_mul_left (card G - 1) hindex2
        simpa [Nat.mul_comm] using this
      have hge : 2 * (card G - 1) ≤ card G := by
        simpa [hEq] using hle'
      have hlt : card G < 2 * (card G - 1) := by
        omega
      omega
