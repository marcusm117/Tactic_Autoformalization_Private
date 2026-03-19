import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) :
∀ a b : R, a*b = b*a := by
  intro a b
  have hneg : ∀ x : R, -x = x := by
    intro x
    calc
      -x = (-x)^2 := by
        symm
        exact hR (-x)
      _ = x^2 := by
        simp [pow_two]
      _ = x := hR x
  have ha : a * a = a := by
    simpa [pow_two] using hR a
  have hb : b * b = b := by
    simpa [pow_two] using hR b
  have hs : a * a + a * b + (b * a + b * b) = a + b := by
    calc
      a * a + a * b + (b * a + b * b)
          = (a * a + a * b) + (b * a + b * b) := by simp [add_assoc]
      _ = a * (a + b) + b * (a + b) := by rw [mul_add, mul_add]
      _ = (a + b) * (a + b) := by rw [add_mul]
      _ = a + b := by simpa [pow_two] using hR (a + b)
  have hs' : a + (a * b + (b * a + b)) = a + b := by
    simpa [ha, hb, add_assoc] using hs
  have hmid : a * b + (b * a + b) = b := by
    exact add_left_cancel hs'
  have hmid' : (a * b + b * a) + b = b := by
    simpa [add_assoc] using hmid
  have hzero : a * b + b * a = 0 := by
    have : (a * b + b * a) + b = 0 + b := by
      simpa [zero_add] using hmid'
    exact add_right_cancel this
  have hab : a * b = -(b * a) := by
    have h := congrArg (fun x => x + -(b * a)) hzero
    simpa [add_assoc] using h
  calc
    a * b = -(b * a) := hab
    _ = b * a := hneg (b * a)
