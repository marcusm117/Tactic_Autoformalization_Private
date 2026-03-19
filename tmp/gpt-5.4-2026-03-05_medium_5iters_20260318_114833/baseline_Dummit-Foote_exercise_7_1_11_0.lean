import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_1_11 {R : Type*} [CommRing R] [IsDomain R]
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1 := by
  have hfac : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 0 := by rw [hx, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    exact eq_neg_iff_add_eq_zero.mpr h
