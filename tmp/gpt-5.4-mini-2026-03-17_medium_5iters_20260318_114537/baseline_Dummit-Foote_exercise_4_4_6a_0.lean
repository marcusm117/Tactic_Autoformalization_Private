import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_6a {G : Type*} [Group G] (H : Subgroup G)
  [Characteristic H] : Normal H  := by
  infer_instance
