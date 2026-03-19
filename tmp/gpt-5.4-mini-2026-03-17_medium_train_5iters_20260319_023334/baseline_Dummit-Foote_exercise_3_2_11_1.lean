import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_11 {G : Type*} [Group G] {H K : Subgroup G}
  (hHK : H ≤ K) :
  H.index = K.index * H.relindex K := by
  simpa using (H.index_mul_relIndex hHK)
