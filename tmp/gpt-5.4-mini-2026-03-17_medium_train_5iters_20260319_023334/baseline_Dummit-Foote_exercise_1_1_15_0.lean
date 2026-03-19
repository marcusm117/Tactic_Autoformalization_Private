import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod := by
  induction as with
  | nil =>
      simp
  | cons a as ih =>
      simpa [List.prod_cons, List.reverse_cons, List.map_append, List.prod_append, ih]
