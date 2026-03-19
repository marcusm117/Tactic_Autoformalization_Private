import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x*y = y*x := by
  intro x y hx hy
  apply Subtype.ext
  have ha : ∀ z ∈ closure {t : G | t = a ∨ t = b}, a * z = z * a := by
    intro z hz
    refine Subgroup.closure_induction hz ?_ ?_ ?_ ?_
    · intro z hz
      rcases hz with rfl | rfl
      · simp
      · exact h
    · simp
    · intro z₁ z₂ hz₁ hz₂
      calc
        a * (z₁ * z₂) = (a * z₁) * z₂ := by rw [mul_assoc]
        _ = (z₁ * a) * z₂ := by rw [hz₁]
        _ = z₁ * (a * z₂) := by rw [← mul_assoc]
        _ = z₁ * (z₂ * a) := by rw [hz₂]
        _ = (z₁ * z₂) * a := by rw [mul_assoc]
    · intro z hz
      have h1 : z⁻¹ * a * z = a := by
        have := congrArg (fun t => z⁻¹ * t) hz
        simpa [mul_assoc] using this
      have h2 : z⁻¹ * a = a * z⁻¹ := by
        have := congrArg (fun t => t * z⁻¹) h1
        simpa [mul_assoc] using this
      exact h2.symm
  have hb : ∀ z ∈ closure {t : G | t = a ∨ t = b}, b * z = z * b := by
    intro z hz
    refine Subgroup.closure_induction hz ?_ ?_ ?_ ?_
    · intro z hz
      rcases hz with rfl | rfl
      · exact h.symm
      · simp
    · simp
    · intro z₁ z₂ hz₁ hz₂
      calc
        b * (z₁ * z₂) = (b * z₁) * z₂ := by rw [mul_assoc]
        _ = (z₁ * b) * z₂ := by rw [hz₁]
        _ = z₁ * (b * z₂) := by rw [← mul_assoc]
        _ = z₁ * (z₂ * b) := by rw [hz₂]
        _ = (z₁ * z₂) * b := by rw [mul_assoc]
    · intro z hz
      have h1 : z⁻¹ * b * z = b := by
        have := congrArg (fun t => z⁻¹ * t) hz
        simpa [mul_assoc] using this
      have h2 : z⁻¹ * b = b * z⁻¹ := by
        have := congrArg (fun t => t * z⁻¹) h1
        simpa [mul_assoc] using this
      exact h2.symm
  have hxy : (x : G) * (y : G) = (y : G) * (x : G) := by
    refine Subgroup.closure_induction hx ?_ ?_ ?_ ?_
    · intro z hz
      rcases hz with rfl | rfl
      · exact ha (y : G) hy
      · exact hb (y : G) hy
    · simp
    · intro z₁ z₂ hz₁ hz₂
      calc
        (z₁ * z₂) * (y : G) = z₁ * (z₂ * y) := by rw [mul_assoc]
        _ = z₁ * (y * z₂) := by rw [hz₂]
        _ = (z₁ * y) * z₂ := by rw [← mul_assoc]
        _ = (y * z₁) * z₂ := by rw [hz₁]
        _ = y * (z₁ * z₂) := by rw [mul_assoc]
    · intro z hz
      have h1 : z⁻¹ * (y : G) * z = (y : G) := by
        have := congrArg (fun t => z⁻¹ * t) hz
        simpa [mul_assoc] using this
      have h2 : z⁻¹ * (y : G) = (y : G) * z⁻¹ := by
        have := congrArg (fun t => t * z⁻¹) h1
        simpa [mul_assoc] using this
      exact h2.symm
  simpa using hxy
