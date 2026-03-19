import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_4 {G : Type*} [Group G] (H : Subgroup G) :
  closure ((H : Set G) \ {1}) = H := by
  refine le_antisymm ?_ ?_
  · exact (Subgroup.closure_le).2 (by
      intro x hx
      exact hx.1)
  · intro x hx
    by_cases h1 : x = 1
    · simpa [h1] using (Subgroup.one_mem (Subgroup.closure ((H : Set G) \ {1})))
    · exact Subgroup.subset_closure ⟨hx, h1⟩
