import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_1_11 {R : Type*} [CommRing R] [IsDomain R]
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1 := by
  have hfactor : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 0 := by rw [hx]; norm_num
  have h := mul_eq_zero.mp hfactor
  rcases h with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    have h' : x + 1 = 0 := by simpa [add_comm] using h
    exact (eq_neg_iff_add_eq_zero).2 h'
