import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_4 :
  IsEmpty (Multiplicative ℝ ≃* Multiplicative ℂ) := by
  classical
  refine ⟨?_⟩
  intro e
  have h : (Complex.I : ℂ) ≠ 1 := Complex.I_ne_one
  let x : Multiplicative ℝ := e.symm Complex.I
  have hx : e x = Complex.I := by
    simp [x]
  have h1 : e (1 : Multiplicative ℝ) = (1 : Multiplicative ℂ) := by
    simp
  have : (Complex.I : ℂ) = 1 := by
    simpa [hx] using congrArg (fun y => y) h1
  exact h this
