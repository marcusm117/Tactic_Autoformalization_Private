import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  classical
  haveI : Fact (Squarefree (2 : ℤ)) := ⟨by decide⟩
  haveI : NoZeroDivisors (Zsqrtd 2) := by infer_instance
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
          have hcoeff := congrArg (fun q : Polynomial (Zsqrtd 2) => q.coeff 2) hp0
          simp at hcoeff
          exact hcoeff
        have hfne : f ≠ 0 := by
          intro h
          apply hp0
          rw [h] at hfg
          simp at hfg
          exact hfg
        have hgne : g ≠ 0 := by
          intro h
          apply hp0
          rw [h] at hfg
          simp at hfg
          exact hfg
        have hleadEq : 1 = f.leadingCoeff * g.leadingCoeff := by
          have h := congrArg Polynomial.leadingCoeff hfg
          rw [Polynomial.leadingCoeff_mul hfne hgne] at h
          simpa using h
        have hunitLeadF : IsUnit f.leadingCoeff := IsUnit.of_mul_eq_one hleadEq.symm
        have hunitLeadG : IsUnit g.leadingCoeff := by
          have hleadG : g.leadingCoeff * f.leadingCoeff = 1 := by
            simpa [mul_comm] using hleadEq
          exact IsUnit.of_mul_eq_one hleadG
        have hdegp : natDegree (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) = 2 := by
          simp
        have hsum : natDegree f + natDegree g = 2 := by
          simpa [hfg, hdegp] using Polynomial.natDegree_mul hfne hgne
        have hf0 : natDegree f ≠ 0 := by
          intro h0
          have hcoeff : IsUnit (f.coeff 0) := by
            simpa [h0] using hunitLeadF
          have hfunit : IsUnit f := by
            rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
            exact Polynomial.isUnit_C.mpr hcoeff
          exact hf hfunit
        have hg0 : natDegree g ≠ 0 := by
          intro h0
          have hcoeff : IsUnit (g.coeff 0) := by
            simpa [h0] using hunitLeadG
          have hgunit : IsUnit g := by
            rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
            exact Polynomial.isUnit_C.mpr hcoeff
          exact hg hgunit
        have hf1 : natDegree f = 1 := by
          omega
        obtain ⟨x, hx⟩ := Polynomial.exists_root_of_natDegree_eq_one hf1
        have hrootp : IsRoot (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) x := by
          rw [hfg]
          simpa [Polynomial.IsRoot] using hx
        rcases x with ⟨a, b⟩
        have hsq : ((⟨a, b⟩ : Zsqrtd 2) ^ 2) - Zsqrtd.sqrtd = 0 := by
          simpa [Polynomial.IsRoot] using hrootp
        have hxb : ((⟨a, b⟩ : Zsqrtd 2) ^ 2) = Zsqrtd.sqrtd := sub_eq_zero.mp hsq
        have h2 : (1 : ℤ) = (2 : ℤ) * (a * b) := by
          have h' := congrArg (fun z : Zsqrtd 2 => z.2) hxb
          simpa [Zsqrtd.sqrtd, pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc, eq_comm] using h'
        have hdiv : (2 : ℤ) ∣ 1 := by
          exact ⟨a * b, h2.symm⟩
        have hnot : ¬ (2 : ℤ) ∣ 1 := by norm_num
        exact hnot hdiv
