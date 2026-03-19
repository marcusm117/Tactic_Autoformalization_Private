import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) :
∀ a b : R, a*b = b*a := by
  have hneg : ∀ x : R, x = -x := by
    intro x
    have hx : x * x = x := by
      simpa [pow_two] using hR x
    have hnx : x * x = -x := by
      simpa [pow_two] using hR (-x)
    exact hx.symm.trans hnx
  intro a b
  have ha : a * a = a := by
    simpa [pow_two] using hR a
  have hb : b * b = b := by
    simpa [pow_two] using hR b
  have htemp : a * a + (a * b + (b * a + b * b)) = a + b := by
    simpa [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm] using hR (a + b)
  have hsum : a + (a * b + b * a) + b = a + b := by
    simpa [ha, hb, add_assoc, add_left_comm, add_comm] using htemp
  have h2 : (a * b + b * a) + b = b := by
    exact add_left_cancel (by simpa [add_assoc] using hsum)
  have hzero : a * b + b * a = 0 := by
    have h3 := congrArg (fun t : R => t + (-b)) h2
    simpa [add_assoc] using h3
  have hab : a * b = -(b * a) := eq_neg_iff_add_eq_zero.mpr hzero
  calc
    a * b = -(b * a) := hab
    _ = b * a := (hneg (b * a)).symm
