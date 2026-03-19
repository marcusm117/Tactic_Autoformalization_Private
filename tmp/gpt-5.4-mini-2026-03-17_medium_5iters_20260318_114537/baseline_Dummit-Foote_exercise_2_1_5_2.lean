import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_5 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 2) (H : Subgroup G) [Fintype H] :
  card H ≠ card G - 1 := by
  intro h
  have hdiv : card H ∣ card G := by
    refine ⟨H.index, ?_⟩
    simpa using H.index_mul_card.symm
  rcases hdiv with ⟨k, hk⟩
  have hkEq : card G = (card G - 1) * k := by
    simpa [h] using hk
  have hk0 : k ≠ 0 := by
    intro hk0
    subst hk0
    omega
  by_cases hk1 : k = 1
  · subst hk1
    omega
  · have hk2 : 2 ≤ k := by
      omega
    have hle : 2 * (card G - 1) ≤ (card G - 1) * k := by
      exact Nat.mul_le_mul_left _ hk2
    have hlt : card G < 2 * (card G - 1) := by
      omega
    omega
