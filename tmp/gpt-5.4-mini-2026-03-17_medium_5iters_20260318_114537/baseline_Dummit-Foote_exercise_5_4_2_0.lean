import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_5_4_2 {G : Type*} [Group G] (H : Subgroup G) :
  H.Normal ↔ ⁅(⊤ : Subgroup G), H⁆ ≤ H := by simpa using (Subgroup.normal_iff_commutator_le (H := H))
