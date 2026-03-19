import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x*y = y*x := by
  intro x y
  let s : Set G := {t : G | t = a ∨ t = b}
  let Ca : Subgroup G :=
    { carrier := {z : G | a * z = z * a}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        calc
          a * (u * v) = (a * u) * v := by rw [mul_assoc]
          _ = (u * a) * v := by rw [hu]
          _ = u * (a * v) := by rw [← mul_assoc]
          _ = u * (v * a) := by rw [hv]
          _ = (u * v) * a := by rw [mul_assoc]
      inv_mem' := by
        intro u hu
        have h1 : u⁻¹ * a * u = a := by
          have := congrArg (fun t => u⁻¹ * t) hu
          simpa [mul_assoc] using this
        have h2 : u⁻¹ * a = a * u⁻¹ := by
          have := congrArg (fun t => t * u⁻¹) h1
          simpa [mul_assoc] using this
        exact h2.symm }
  let Cb : Subgroup G :=
    { carrier := {z : G | b * z = z * b}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        calc
          b * (u * v) = (b * u) * v := by rw [mul_assoc]
          _ = (u * b) * v := by rw [hu]
          _ = u * (b * v) := by rw [← mul_assoc]
          _ = u * (v * b) := by rw [hv]
          _ = (u * v) * b := by rw [mul_assoc]
      inv_mem' := by
        intro u hu
        have h1 : u⁻¹ * b * u = b := by
          have := congrArg (fun t => u⁻¹ * t) hu
          simpa [mul_assoc] using this
        have h2 : u⁻¹ * b = b * u⁻¹ := by
          have := congrArg (fun t => t * u⁻¹) h1
          simpa [mul_assoc] using this
        exact h2.symm }
  have hCa : closure s ≤ Ca := by
    apply (Subgroup.closure_le).2
    intro z hz
    rcases hz with rfl | rfl
    · simp [Ca]
    · exact h
  have hCb : closure s ≤ Cb := by
    apply (Subgroup.closure_le).2
    intro z hz
    rcases hz with rfl | rfl
    · exact h.symm
    · simp [Cb]
  have hx_a : (x : G) * a = a * x := by
    exact (hCa x.1 x.2).symm
  have hx_b : (x : G) * b = b * x := by
    exact (hCb x.1 x.2).symm
  let Cx : Subgroup G :=
    { carrier := {z : G | (x : G) * z = z * (x : G)}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        calc
          (x : G) * (u * v) = ((x : G) * u) * v := by rw [mul_assoc]
          _ = (u * (x : G)) * v := by rw [hu]
          _ = u * ((x : G) * v) := by rw [← mul_assoc]
          _ = u * (v * (x : G)) := by rw [hv]
          _ = (u * v) * (x : G) := by rw [mul_assoc]
      inv_mem' := by
        intro u hu
        have h1 : u⁻¹ * (x : G) * u = (x : G) := by
          have := congrArg (fun t => u⁻¹ * t) hu
          simpa [mul_assoc] using this
        have h2 : u⁻¹ * (x : G) = (x : G) * u⁻¹ := by
          have := congrArg (fun t => t * u⁻¹) h1
          simpa [mul_assoc] using this
        exact h2.symm }
  have haCx : a ∈ Cx := by
    simpa [Cx] using hx_a
  have hbCx : b ∈ Cx := by
    simpa [Cx] using hx_b
  have hCy : closure s ≤ Cx := by
    apply (Subgroup.closure_le).2
    intro z hz
    rcases hz with rfl | rfl
    · exact haCx
    · exact hbCx
  have hxy : (x : G) * (y : G) = (y : G) * (x : G) := hCy y.1 y.2
  apply Subtype.ext
  exact hxy
