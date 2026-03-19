import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_13_6_10 {K : Type*} [Field K] [Fintype Kˣ] :
  (∏ x : Kˣ,  x) = -1 := by
  classical
  have hprod :
      (∏ x : Kˣ, (x : K)) =
        (∏ x in (Finset.univ.filter (fun x : Kˣ => x = x⁻¹)), (x : K)) := by
    simpa using
      (Finset.prod_involution
        (s := (Finset.univ : Finset Kˣ))
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
        simpa using hx
      have hx2 : (x : K)^2 = 1 := by
        have h := congrArg (fun y : K => y * (x : K)) hx'
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h
      have hx_or : (x : K) = 1 ∨ (x : K) = -1 := by
        have hfac : ((x : K) - 1) * ((x : K) + 1) = 0 := by
          calc
            ((x : K) - 1) * ((x : K) + 1) = (x : K)^2 - 1 := by ring
            _ = 0 := by rw [hx2]
        rcases mul_eq_zero.mp hfac with h1 | h1
        · left
          exact sub_eq_zero.mp h1
        · right
          exact eq_neg_of_add_eq_zero h1
      rcases hx_or with rfl | rfl <;> simp
    · intro hx
      rcases hx with rfl | rfl <;> simp
  rw [hprod, hfixed]
  simp
