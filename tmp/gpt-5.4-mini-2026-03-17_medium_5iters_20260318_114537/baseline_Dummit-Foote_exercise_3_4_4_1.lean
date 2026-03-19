import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_4 {G : Type*} [CommGroup G] [Fintype G] {n : ℕ}
    (hn : n ∣ (card G)) :
    ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n  := by
  classical
  rcases Subgroup.exists_subgroup_card (G := G) (n := n) hn with ⟨H, hH⟩
  refine ⟨H, inferInstance, ?_⟩
  simpa using hH
