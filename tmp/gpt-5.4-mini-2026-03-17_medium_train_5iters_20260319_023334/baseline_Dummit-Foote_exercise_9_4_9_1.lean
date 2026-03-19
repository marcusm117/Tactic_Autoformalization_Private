import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  classical
  constructor
  · intro hunit
    have hdeg : natDegree (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) = 2 := by
      simp
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    simp [hdeg] at h0
  · intro f g hfg
    by_cases hf : IsUnit f
    · exact Or.inl hf
    · by_cases hg : IsUnit g
      · exact Or.inr hg
      · exfalso
        have hp0 : (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) ≠ 0 := by
          intro hp0
          have := congrArg (fun q : Polynomial (Zsqrtd 2) => q.coeff 2) hp0
          simp at this
        have hlead : leadingCoeff f * leadingCoeff g = 1 := by
          have := congrArg Polynomial.leadingCoeff hfg
          simpa using this
        have hunitLeadF : IsUnit (leadingCoeff f) := by
          refine ⟨⟨leadingCoeff f, leadingCoeff g, hlead, ?_⟩, rfl⟩
          simpa [mul_comm] using hlead
        have hunitLeadG : IsUnit (leadingCoeff g) := by
          refine ⟨⟨leadingCoeff g, leadingCoeff f, ?_, ?_⟩, rfl⟩ <;> simpa [mul_comm] using hlead
        have hf0 : natDegree f ≠ 0 := by
          intro h0
          have hfconst : f = C (coeff f 0) := by
            simpa [h0] using (Polynomial.eq_C_of_natDegree_eq_zero h0)
          have hcoeffunit : IsUnit (coeff f 0) := by
            simpa [h0] using hunitLeadF
          have hfunit : IsUnit f := by
            rw [hfconst]
            simpa using hcoeffunit
          exact hf hfunit
        have hg0 : natDegree g ≠ 0 := by
          intro h0
          have hgconst : g = C (coeff g 0) := by
            simpa [h0] using (Polynomial.eq_C_of_natDegree_eq_zero h0)
          have hcoeffunit : IsUnit (coeff g 0) := by
            simpa [h0] using hunitLeadG
          have hgunit : IsUnit g := by
            rw [hgconst]
            simpa using hcoeffunit
          exact hg hgunit
        have hfne : f ≠ 0 := by
          intro h
          simpa [h] using hf0
        have hgne : g ≠ 0 := by
          intro h
          simpa [h] using hg0
        have hdegp : natDegree (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) = 2 := by
          simp
        have hsum := by
          simpa [hfg, hdegp] using (Polynomial.natDegree_mul hfne hgne)
        have hf1 : natDegree f = 1 := by
          omega
        have hfroot : ∃ x : Zsqrtd 2, IsRoot f x := Polynomial.exists_root_of_natDegree_eq_one hf1
        rcases hfroot with ⟨x, hx⟩
        have hrootp : IsRoot (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) x := by
          simpa [hfg, Polynomial.IsRoot, hx]
        rcases x with ⟨a, b⟩
        have hx0 : ((⟨a, b⟩ : Zsqrtd 2) ^ 2) - Zsqrtd.sqrtd = 0 := by
          simpa [Polynomial.IsRoot] using hrootp
        have hx' : ((⟨a, b⟩ : Zsqrtd 2) ^ 2) = Zsqrtd.sqrtd := by
          exact sub_eq_zero.mp hx0
        have h2 := congrArg (fun z : Zsqrtd 2 => z.2) hx'
        simp [Zsqrtd.sqrtd, pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] at h2
        have hpar : (2 : ℤ) ∣ (2 * a * b) := by
          refine ⟨a * b, by ring⟩
        have hmod : (2 * a * b) % 2 = 0 := Int.mod_eq_zero_of_dvd hpar
        have h2mod := congrArg (fun n : ℤ => n % 2) h2
        simp [hmod] at h2mod
