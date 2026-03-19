import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_13_6_10 {K : Type*} [Field K] [Fintype Kˣ] :
  (∏ x : Kˣ,  x) = -1 := by
  classical
  have hprod :
      (∏ x : Kˣ, (x : K)) =
        ∏ x in Finset.univ.filter (fun x : Kˣ => x = x⁻¹), (x : K) := by
    simpa using
      (Finset.prod_involution
        (s := Finset.univ : Finset Kˣ)
        (f := fun x : Kˣ => x⁻¹)
        (g := fun x : Kˣ => (x : K))
        (by intro x hx; simp)
        (by intro x hx; simp)
        (by intro x hx hne; simp [hne]))
  have hfixed :
      (Finset.univ.filter (fun x : Kˣ => x = x⁻¹)) = ({1, -1} : Finset Kˣ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have hx' : (x : K) = (x : K)⁻¹ := by
        simpa using congrArg (fun u : Kˣ => (u : K)) hx
      have hx2 : (x : K) ^ 2 = 1 := by
        have hmul := congrArg (fun y : K => y * (x : K)) hx'
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
      rcases sq_eq_one_iff.mp hx2 with h1 | h1
      · left
        apply Units.ext
        simpa using h1
      · right
        apply Units.ext
        simpa using h1
    · intro hx
      rcases hx with rfl | rfl <;> simp
  rw [hprod, hfixed]
  simp
