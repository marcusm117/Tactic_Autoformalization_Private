import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) :
∀ a b : R, a*b = b*a := by
  have hneg : ∀ x : R, x = -x := by
    intro x
    simpa [pow_two, hR x] using hR (-x)
  intro a b
  have hsum : a + (a * b + b * a) + b = a + b := by
    simpa [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm, hR a, hR b] using
      hR (a + b)
  have hzero : a * b + b * a = 0 := by
    have h1 : a + (a * b + b * a) = a := by
      apply add_right_cancel
      simpa [add_assoc] using hsum
    exact add_left_cancel h1
  have hab : a * b = -(b * a) := eq_neg_iff_add_eq_zero.mpr hzero
  calc
    a * b = -(b * a) := hab
    _ = b * a := (hneg (b * a)).symm
