import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_11 :
  Irreducible ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) := by
  classical
  let e0 : MvPolynomial (Fin 1) ℚ ≃ₐ[ℚ] Polynomial ℚ :=
    (MvPolynomial.finSuccEquiv ℚ 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)))
  let e : MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] Polynomial (Polynomial ℚ) :=
    (MvPolynomial.finSuccEquiv ℚ 1).trans (Polynomial.mapAlgEquiv e0)
  have hnsq : ¬ IsSquare (-(Polynomial.X ^ 2 - 1 : Polynomial ℚ)) := by
    rintro ⟨q, hq⟩
    have h := congrArg (fun p : Polynomial ℚ => p.eval (2 : ℚ)) hq
    simp [pow_two, sub_eq_add_neg] at h
    nlinarith [sq_nonneg (q.eval (2 : ℚ))]
  have hpoly :
      Irreducible
        (Polynomial.X ^ 2 + Polynomial.C ((Polynomial.X : Polynomial ℚ)^2 - 1)
          : Polynomial (Polynomial ℚ)) := by
    let f : Polynomial (Polynomial ℚ) :=
      Polynomial.X ^ 2 + Polynomial.C ((Polynomial.X : Polynomial ℚ)^2 - 1)
    refine ⟨?_, ?_⟩
    · intro hu
      have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
      simp [f, pow_two] at hdeg
    · intro g h hgh
      by_cases hg : IsUnit g
      · exact Or.inl hg
      · by_cases hh : IsUnit h
        · exact Or.inr hh
        · have hfneq : f ≠ 0 := by
            intro hf0
            have := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 2) hf0
            simp [f, pow_two] at this
          have hg0 : g ≠ 0 := by
            intro h0
            apply hfneq
            simp [f, h0] at hgh
          have hh0 : h ≠ 0 := by
            intro h0
            apply hfneq
            simp [f, h0] at hgh
          have hfdeg : f.natDegree = 2 := by
            simp [f, pow_two]
          have hdeg : g.natDegree + h.natDegree = 2 := by
            simpa [hgh, hfdeg] using (Polynomial.natDegree_mul hg0 hh0)
          have hgpos : 0 < g.natDegree := by
            by_contra hgnpos
            have hgdeg0 : g.natDegree = 0 := by omega
            have hhdeg2 : h.natDegree = 2 := by omega
            have h2 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 2) hgh
            have hg2 : coeff g 1 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hg3 : coeff g 2 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hh3 : coeff h 3 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hh4 : coeff h 4 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hh5 : coeff h 5 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            simp [f, hgdeg0, hhdeg2, hg2, hg3, hh3, hh4, hh5, Polynomial.coeff_mul] at h2
            have hunitc : IsUnit (g.coeff 0) := by
              exact isUnit_of_mul_eq_one h2
            have hgu : IsUnit g := by
              rw [Polynomial.eq_C_of_natDegree_eq_zero hgdeg0]
              simpa using (isUnit_C.mpr hunitc)
            exact hg hgu
          have hhpos : 0 < h.natDegree := by
            by_contra hhnpos
            have hhdeg0 : h.natDegree = 0 := by omega
            have hgdeg2 : g.natDegree = 2 := by omega
            have h2 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 2) hgh
            have hh2 : coeff h 1 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hh3 : coeff h 2 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hg3 : coeff g 3 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hg4 : coeff g 4 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hg5 : coeff g 5 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            simp [f, hhdeg0, hgdeg2, hh2, hh3, hg3, hg4, hg5, Polynomial.coeff_mul] at h2
            have hunitc : IsUnit (h.coeff 0) := by
              exact isUnit_of_mul_eq_one h2
            have hhu : IsUnit h := by
              rw [Polynomial.eq_C_of_natDegree_eq_zero hhdeg0]
              simpa using (isUnit_C.mpr hunitc)
            exact hh hhu
          have hgdeg : g.natDegree = 1 := by omega
          have hhdeg : h.natDegree = 1 := by omega
          have hg2 : coeff g 2 = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            omega
          have hh2 : coeff h 2 = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            omega
          have hcoeff2 : coeff g 1 * coeff h 1 = 1 := by
            have h2 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 2) hgh
            simp [f, hg2, hh2, hgdeg, hhdeg, Polynomial.coeff_mul] at h2
            simpa using h2
          have hcoeff1 : coeff g 1 * coeff h 0 + coeff g 0 * coeff h 1 = 0 := by
            have h1 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 1) hgh
            have hg3 : coeff g 3 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            have hh3 : coeff h 3 = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              omega
            simp [f, hg2, hh2, hg3, hh3, hgdeg, hhdeg, Polynomial.coeff_mul] at h1
            simpa using h1
          have hcoeff0 : coeff g 0 * coeff h 0 = Polynomial.X ^ 2 - 1 := by
            have h0 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 0) hgh
            have hg1 : coeff g 1 = coeff g 1 := rfl
            have hh1 : coeff h 1 = coeff h 1 := rfl
            simp [f, hg2, hh2, hgdeg, hhdeg, Polynomial.coeff_mul] at h0
            simpa using h0
          have hswap : coeff g 0 * coeff h 1 = - (coeff g 1 * coeff h 0) := by
            apply (eq_neg_iff_add_eq_zero).2
            simpa [add_comm, add_left_comm, add_assoc] using hcoeff1
          have huv : (coeff g 1 * coeff h 0) * (coeff g 0 * coeff h 1) = Polynomial.X ^ 2 - 1 := by
            calc
              (coeff g 1 * coeff h 0) * (coeff g 0 * coeff h 1)
                  = (coeff g 1 * coeff h 1) * (coeff g 0 * coeff h 0) := by ring
              _ = Polynomial.X ^ 2 - 1 := by rw [hcoeff2, hcoeff0]
          have hsq : IsSquare (-(Polynomial.X ^ 2 - 1 : Polynomial ℚ)) := by
            refine ⟨coeff g 1 * coeff h 0, ?_⟩
            calc
              (coeff g 1 * coeff h 0)^2
                  = - ((coeff g 1 * coeff h 0) * (coeff g 0 * coeff h 1)) := by
                      rw [hswap]
                      ring
              _ = -(Polynomial.X ^ 2 - 1) := by rw [huv]
          exact hnsq hsq
  exact (MulEquiv.irreducible_iff e.toMulEquiv).2 <| by
    simpa [e, e0, f, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hpoly
