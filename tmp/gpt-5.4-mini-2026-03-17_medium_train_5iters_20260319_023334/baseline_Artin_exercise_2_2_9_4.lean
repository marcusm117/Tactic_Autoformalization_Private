import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x*y = y*x := by
  intro x y
  have hx_a : (x : G) * a = a * x := by
    refine Subgroup.closure_induction (p := fun z => z * a = a * z) x.2 ?_ ?_ ?_ ?_
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
      have h1 : a = u⁻¹ * a * u := by
        have := congrArg (fun t => u⁻¹ * t) hu
        simpa [mul_assoc] using this
      have h2 : a * u⁻¹ = u⁻¹ * a := by
        have := congrArg (fun t => t * u⁻¹) h1
        simpa [mul_assoc] using this
      exact h2.symm
  have hx_b : (x : G) * b = b * x := by
    refine Subgroup.closure_induction (p := fun z => z * b = b * z) x.2 ?_ ?_ ?_ ?_
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
      have h1 : b = u⁻¹ * b * u := by
        have := congrArg (fun t => u⁻¹ * t) hu
        simpa [mul_assoc] using this
      have h2 : b * u⁻¹ = u⁻¹ * b := by
        have := congrArg (fun t => t * u⁻¹) h1
        simpa [mul_assoc] using this
      exact h2.symm
  have hxy : (x : G) * (y : G) = (y : G) * (x : G) := by
    refine Subgroup.closure_induction (p := fun z => (x : G) * z = z * x) y.2 ?_ ?_ ?_ ?_
    · intro z hz
      rcases hz with rfl | rfl
      · exact hx_a
      · exact hx_b
    · simp
    · intro u v hu hv
      calc
        (x : G) * (u * v) = ((x : G) * u) * v := by rw [mul_assoc]
        _ = (u * x) * v := by rw [hu]
        _ = u * (x * v) := by rw [← mul_assoc]
        _ = u * (v * x) := by rw [hv]
        _ = (u * v) * x := by rw [mul_assoc]
    · intro u hu
      have h1 : (x : G) = u⁻¹ * (x : G) * u := by
        have := congrArg (fun t => u⁻¹ * t) hu
        simpa [mul_assoc] using this
      have h2 : (x : G) * u⁻¹ = u⁻¹ * (x : G) := by
        have := congrArg (fun t => t * u⁻¹) h1
        simpa [mul_assoc] using this
      exact h2.symm
  apply Subtype.ext
  exact hxy
