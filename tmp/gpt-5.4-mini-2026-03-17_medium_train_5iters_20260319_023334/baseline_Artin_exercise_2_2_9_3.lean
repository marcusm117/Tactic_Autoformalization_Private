import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x*y = y*x := by
  intro x y
  have hy_a : (y : G) * a = a * y := by
    apply Subgroup.closure_induction y.2
    · intro z hz
      rcases hz with rfl | rfl
      · simp
      · exact h.symm
    · simp
    · intro u v hu hv
      calc
        (u * v) * a = u * (v * a) := by rw [mul_assoc]
        _ = u * (a * v) := by rw [hv]
        _ = (u * a) * v := by rw [← mul_assoc]
        _ = (a * u) * v := by rw [hu]
        _ = a * (u * v) := by rw [mul_assoc]
    · intro u hu
      have h1 : u⁻¹ * a * u = a := by
        have := congrArg (fun t => u⁻¹ * t) hu
        simpa [mul_assoc] using this
      have h2 : u⁻¹ * a = a * u⁻¹ := by
        have := congrArg (fun t => t * u⁻¹) h1
        simpa [mul_assoc] using this
      exact h2
  have hy_b : (y : G) * b = b * y := by
    apply Subgroup.closure_induction y.2
    · intro z hz
      rcases hz with rfl | rfl
      · exact h
      · simp
    · simp
    · intro u v hu hv
      calc
        (u * v) * b = u * (v * b) := by rw [mul_assoc]
        _ = u * (b * v) := by rw [hv]
        _ = (u * b) * v := by rw [← mul_assoc]
        _ = (b * u) * v := by rw [hu]
        _ = b * (u * v) := by rw [mul_assoc]
    · intro u hu
      have h1 : u⁻¹ * b * u = b := by
        have := congrArg (fun t => u⁻¹ * t) hu
        simpa [mul_assoc] using this
      have h2 : u⁻¹ * b = b * u⁻¹ := by
        have := congrArg (fun t => t * u⁻¹) h1
        simpa [mul_assoc] using this
      exact h2
  have hxy : (x : G) * (y : G) = (y : G) * (x : G) := by
    apply Subgroup.closure_induction x.2
    · intro z hz
      rcases hz with rfl | rfl
      · exact hy_a.symm
      · exact hy_b.symm
    · simp
    · intro u v hu hv
      calc
        (u * v) * (y : G) = u * (v * y) := by rw [mul_assoc]
        _ = u * (y * v) := by rw [hv]
        _ = (u * y) * v := by rw [← mul_assoc]
        _ = (y * u) * v := by rw [hu]
        _ = y * (u * v) := by rw [mul_assoc]
    · intro u hu
      have h1 : u⁻¹ * (y : G) * u = (y : G) := by
        have := congrArg (fun t => u⁻¹ * t) hu
        simpa [mul_assoc] using this
      have h2 : u⁻¹ * (y : G) = (y : G) * u⁻¹ := by
        have := congrArg (fun t => t * u⁻¹) h1
        simpa [mul_assoc] using this
      exact h2
  ext
  exact hxy
