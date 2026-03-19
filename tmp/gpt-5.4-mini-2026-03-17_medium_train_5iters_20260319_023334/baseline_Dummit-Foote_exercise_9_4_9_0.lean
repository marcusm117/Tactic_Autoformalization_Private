import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  classical
  refine Polynomial.irreducible_of_natDegree_eq_two ?_ ?_
  · simp
  · intro x hx
    rcases x with ⟨a, b⟩
    have hx' : ((⟨a, b⟩ : Zsqrtd 2) ^ 2) = Zsqrtd.sqrtd := by
      apply sub_eq_zero.mp
      simpa [Polynomial.IsRoot, pow_two] using hx
    have h2 := congrArg (fun z : Zsqrtd 2 => z.2) hx'
    simp [Zsqrtd.sqrtd, pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] at h2
    have hdiv : (2 : ℤ) ∣ (2 * a * b) := by
      refine ⟨a * b, by ring⟩
    have hmod : (2 * a * b) % 2 = 0 := Int.mod_eq_zero_of_dvd hdiv
    have h2' := congrArg (fun n : ℤ => n % 2) h2
    rw [hmod] at h2'
    norm_num at h2'
