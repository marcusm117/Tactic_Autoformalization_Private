import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_9a {G : Type*} [Fintype G] [Group G] {p α : ℕ}
  (hp : p.Prime) (ha : α > 0) (hG : card G = p ^ α) :
  ∀ H : Subgroup G, H.index = p → H.Normal := by
  intro H hH
  haveI : IsPGroup p G := by
    rw [isPGroup_iff_card]
    exact ⟨α, by simpa [hG]⟩
  exact H.normal_of_index_eq_prime hp hH
