import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  classical
  haveI : Fact (Squarefree (2 : ℤ)) := ⟨by
    native_decide⟩
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
          norm_num at hcoeff
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
          simpa [Polynomial.leadingCoeff_mul hfne hgne] using h
        have hunitLeadF : IsUnit f.leadingCoeff := by
          exact isUnit_of_mul_eq_one (by simpa [mul_comm] using hleadEq.symm)
        have hunitLeadG : IsUnit g.leadingCoeff := by
          exact isUnit_of_mul_eq_one (by simpa [mul_comm] using hleadEq)
        have hdegp : natDegree (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) = 2 := by
          simp
        have hsum : f.natDegree + g.natDegree = 2 := by
          have hmul := Polynomial.natDegree_mul hfne hgne
          rw [← hfg] at hmul
          simpa [hdegp] using hmul.symm
        have hf0 : f.natDegree ≠ 0 := by
          intro h0
          have hle : f.coeff 0 = f.leadingCoeff := by
            simpa [h0] using (Polynomial.coeff_natDegree (p := f))
          have hcoeff : IsUnit (f.coeff 0) := by
            rw [hle]
            exact hunitLeadF
          have hfunit : IsUnit f := by
            rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
            exact Polynomial.isUnit_C.mpr hcoeff
          exact hf hfunit
        have hg0 : g.natDegree ≠ 0 := by
          intro h0
          have hle : g.coeff 0 = g.leadingCoeff := by
            simpa [h0] using (Polynomial.coeff_natDegree (p := g))
          have hcoeff : IsUnit (g.coeff 0) := by
            rw [hle]
            exact hunitLeadG
          have hgunit : IsUnit g := by
            rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
            exact Polynomial.isUnit_C.mpr hcoeff
          exact hg hgunit
        have hf1 : f.natDegree = 1 := by omega
        have hg1 : g.natDegree = 1 := by omega
        have hfexp : f = C (f.coeff 1) * X + C (f.coeff 0) := by
          simpa using (Polynomial.eq_C_mul_X_add_C (p := f) hf1)
        let x : Zsqrtd 2 := - f.coeff 0 * ((hunitLeadF.unit)⁻¹ : Zsqrtd 2)
        have hrootf : IsRoot f x := by
          simp [Polynomial.IsRoot, hfexp, x, mul_add, add_mul, hunitLeadF.unit_spec]
        have hrootfg : IsRoot (f * g) x := by
          simp [Polynomial.IsRoot, hrootf]
        have hrootp : IsRoot (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) x := by
          simpa [hfg] using hrootfg
        have hx2 : x ^ 2 = Zsqrtd.sqrtd := by
          apply sub_eq_zero.mp
          simpa [Polynomial.IsRoot, pow_two] using hrootp
        rcases x with ⟨a, b⟩
        have hcomp := congrArg (fun z : Zsqrtd 2 => z.2) hx2
        simp [Zsqrtd.sqrtd, pow_two, mul_add, add_mul] at hcomp
        have hdiv : (2 : ℤ) ∣ 1 := by
          refine ⟨a * b, ?_⟩
          simpa [mul_comm, mul_left_comm, mul_assoc] using hcomp.symm
        have hnot : ¬ (2 : ℤ) ∣ 1 := by norm_num
        exact hnot hdiv
