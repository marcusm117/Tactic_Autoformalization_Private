import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_34 {G : Type*} [Group G] {x : G}
  (hx_inf : orderOf x = 0) (n m : ℤ) (hnm : n ≠ m) :
  x ^ n ≠ x ^ m := by
  intro h
  exact hnm ((zpow_left_injective hx_inf) h)
