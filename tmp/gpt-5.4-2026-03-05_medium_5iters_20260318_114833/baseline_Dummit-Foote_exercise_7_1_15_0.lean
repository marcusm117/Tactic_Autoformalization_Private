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
  have h1 : a + b = a * a + a * b + b * a + b * b := by
    calc
      a + b = (a + b)^2 := by
        symm
        exact hR (a + b)
      _ = a * a + a * b + b * a + b * b := by
        simp [pow_two, add_mul, mul_add, add_assoc]
  have h1' : a + b = a + a * b + b * a + b := by
    rw [ha, hb] at h1
    exact h1
  have h3 : b = a * b + b * a + b := by
    exact add_left_cancel (by simpa [add_assoc] using h1')
  have h4 : 0 = a * b + b * a := by
    exact add_right_cancel (by simpa [zero_add, add_assoc] using h3)
  have h2 : a * b + b * a = 0 := by
    simpa using h4.symm
  have h5 : a * b = -(b * a) := by
    have h := congrArg (fun x => x + -(b * a)) h2
    simpa [add_assoc] using h
  calc
    a * b = -(b * a) := h5
    _ = b * a := hneg (b * a)
