import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_25 {G : Type*} [Group G]
  (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a*b = b*a := by
  intro a b
  have ha : a = a⁻¹ := by
    have h1 : a * a = 1 := by simpa [pow_two] using h a
    have := congrArg (fun x => a⁻¹ * x) h1
    simpa [mul_assoc] using this
  have hb : b = b⁻¹ := by
    have h1 : b * b = 1 := by simpa [pow_two] using h b
    have := congrArg (fun x => b⁻¹ * x) h1
    simpa [mul_assoc] using this
  have hab : a * b = (a * b)⁻¹ := by
    have h1 : (a * b) * (a * b) = 1 := by simpa [pow_two] using h (a * b)
    have := congrArg (fun x => (a * b)⁻¹ * x) h1
    simpa [mul_assoc] using this
  calc
    a * b = (a * b)⁻¹ := hab
    _ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev]
    _ = b * a := by rw [← hb, ← ha]
