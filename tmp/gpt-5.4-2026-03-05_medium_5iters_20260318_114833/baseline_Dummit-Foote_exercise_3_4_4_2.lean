import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_4 {G : Type*} [CommGroup G] [Fintype G] {n : ℕ}
    (hn : n ∣ (card G)) :
    ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n  := by
  classical
  obtain ⟨H, hH⟩ := Finite.exists_subgroup_card (n := n) (by
    simpa [Nat.card_eq_fintype_card] using hn)
  refine ⟨H, inferInstance, ?_⟩
  simpa [Nat.card_eq_fintype_card] using hH
