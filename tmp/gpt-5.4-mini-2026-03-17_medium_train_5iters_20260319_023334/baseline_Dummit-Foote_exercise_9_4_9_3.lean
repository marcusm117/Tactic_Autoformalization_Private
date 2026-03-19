import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  classical
  haveI : Fact (Squarefree (2 : ℤ)) := ⟨by
    simpa using (Int.squarefree_two : Squarefree (2 : ℤ))⟩
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
        have hfne : f ≠ 0 := by
          intro h
          apply hp0
          rw [h] at hfg
          simp at hfg
        have hgne : g ≠ 0 := by
          intro h
          apply hp0
          rw [h] at hfg
          simp at hfg
        have hleadEq : 1 = f.leadingCoeff * g.leadingCoeff := by
          have h := congrArg Polynomial.leadingCoeff hfg
          simpa [Polynomial.leadingCoeff_mul] using h
        have hunitLeadF : IsUnit f.leadingCoeff := by
          refine ⟨⟨f.leadingCoeff, g.leadingCoeff, ?_, ?_⟩, rfl⟩
          · simpa [mul_comm] using hleadEq.symm
          · simpa [mul_comm] using hleadEq.symm
        have hunitLeadG : IsUnit g.leadingCoeff := by
          refine ⟨⟨g.leadingCoeff, f.leadingCoeff, ?_, ?_⟩, rfl⟩
          · simpa [mul_comm] using hleadEq.symm
          · simpa [mul_comm] using hleadEq.symm
        have hdegp : natDegree (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) = 2 := by
          simp
        have hsum : natDegree f + natDegree g = 2 := by
          simpa [hfg, hdegp] using (Polynomial.natDegree_mul hfne hgne)
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
        have hf1 : natDegree f = 1 := by omega
        have hg1 : natDegree g = 1 := by omega
        have hfexp : f = C (f.coeff 1) * X + C (f.coeff 0) := by
          simpa using (Polynomial.eq_C_mul_X_add hf1)
        have hgexp : g = C (g.coeff 1) * X + C (g.coeff 0) := by
          simpa using (Polynomial.eq_C_mul_X_add hg1)
        have h2coeff : f.coeff 1 * g.coeff 1 = 1 := by
          have h := congrArg (fun p : Polynomial (Zsqrtd 2) => p.coeff 2) hfg
          simpa [hfexp, hgexp] using h
        have h1coeff : f.coeff 1 * g.coeff 0 + f.coeff 0 * g.coeff 1 = 0 := by
          have h := congrArg (fun p : Polynomial (Zsqrtd 2) => p.coeff 1) hfg
          simpa [hfexp, hgexp] using h
        have h0coeff : f.coeff 0 * g.coeff 0 = - Zsqrtd.sqrtd := by
          have h := congrArg (fun p : Polynomial (Zsqrtd 2) => p.coeff 0) hfg
          simpa [hfexp, hgexp] using h
        have hmid : f.coeff 1 * f.coeff 1 * g.coeff 0 + f.coeff 0 = 0 := by
          have htmp := congrArg (fun z : Zsqrtd 2 => f.coeff 1 * z) h1coeff
          simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, h2coeff] at htmp
          exact htmp
        have hb : f.coeff 0 = - (f.coeff 1 * f.coeff 1 * g.coeff 0) := by
          exact eq_neg_of_add_eq_zero_right hmid
        have hsq0 : f.coeff 1 * f.coeff 1 * g.coeff 0 * g.coeff 0 = Zsqrtd.sqrtd := by
          have htmp := h0coeff
          rw [hb] at htmp
          have htmp' : - (f.coeff 1 * f.coeff 1 * g.coeff 0 * g.coeff 0) = - Zsqrtd.sqrtd := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
          exact neg_injective htmp'
        have hsq : (f.coeff 1 * g.coeff 0)^2 = Zsqrtd.sqrtd := by
          calc
            (f.coeff 1 * g.coeff 0)^2 = f.coeff 1 * f.coeff 1 * g.coeff 0 * g.coeff 0 := by ring
            _ = Zsqrtd.sqrtd := hsq0
        rcases f.coeff 1 * g.coeff 0 with ⟨a, b⟩
        have h2 := congrArg (fun z : Zsqrtd 2 => z.2) hsq
        simp [Zsqrtd.sqrtd, pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] at h2
        have hdiv : (2 : ℤ) ∣ 1 := by
          refine ⟨a * b, ?_⟩
          simpa [mul_comm, mul_left_comm, mul_assoc] using h2
        have hnot : ¬ (2 : ℤ) ∣ 1 := by norm_num
        exact hnot hdiv
