import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_1_22b {G : Type*} [Group G] (I : Type*) [Nonempty I]
  (H : I → Subgroup G) (hH : ∀ i : I, Normal (H i)) :
  Normal (⨅ (i : I), H i):= by
  haveI : ∀ i : I, Normal (H i) := hH
  infer_instance
