import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_1_11 {R : Type*} [CommRing R] [IsDomain R]
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1 := by
  have hfactor : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 0 := by rw [hx]
  have h := mul_eq_zero.mp hfactor
  rcases h with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    simpa using (eq_neg_of_add_eq_zero h)
