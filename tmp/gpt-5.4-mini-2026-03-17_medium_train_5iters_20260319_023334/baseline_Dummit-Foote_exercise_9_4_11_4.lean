import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_11 :
  Irreducible ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) := by
  classical
  let e0 : MvPolynomial (Fin 1) ℚ ≃ₐ[ℚ] Polynomial ℚ :=
    (MvPolynomial.finSuccEquiv ℚ 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv (R := ℚ) (σ := Fin 0)))
  let e : MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] Polynomial (Polynomial ℚ) :=
    (MvPolynomial.finSuccEquiv ℚ 1).trans (Polynomial.mapAlgEquiv e0)
  let f : Polynomial (Polynomial ℚ) :=
    Polynomial.X ^ 2 + Polynomial.C ((Polynomial.X : Polynomial ℚ)^2 - 1)
  have hfdeg : f.natDegree = 2 := by
    rw [f]
    have hlt :
        (Polynomial.C ((Polynomial.X : Polynomial ℚ)^2 - 1)).natDegree <
          (Polynomial.X ^ 2 : Polynomial (Polynomial ℚ)).natDegree := by
      simp
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]
    simp [pow_two]
  have hnsq : ¬ IsSquare (-(Polynomial.X ^ 2 - 1 : Polynomial ℚ)) := by
    rintro ⟨q, hq⟩
    have h := congrArg (fun p : Polynomial ℚ => p.eval (2 : ℚ)) hq
    simp [pow_two, sub_eq_add_neg] at h
    nlinarith [sq_nonneg (q.eval (2 : ℚ))]
  have hf0 : f ≠ 0 := by
    intro h0
    have h2 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 2) h0
    simp [f, pow_two] at h2
  have hpoly : Irreducible f := by
    refine ⟨?_, ?_⟩
    · intro hu
      have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [hfdeg] at hdeg0
      norm_num at hdeg0
    · intro g h hgh
      by_cases hgunit : IsUnit g
      · exact Or.inl hgunit
      · by_cases hhunit : IsUnit h
        · exact Or.inr hhunit
        · have hgne : g ≠ 0 := by
            intro h0
            apply hf0
            simpa [h0] using hgh
          have hhne : h ≠ 0 := by
            intro h0
            apply hf0
            simpa [h0] using hgh
          have hsum : g.natDegree + h.natDegree = 2 := by
            have := Polynomial.natDegree_mul hgne hhne
            simpa [hgh, hfdeg] using this
          have hg0 : g.natDegree ≠ 0 := by
            intro hgn0
            have hlead : g.coeff 0 * Polynomial.leadingCoeff h = 1 := by
              have := congrArg Polynomial.leadingCoeff hgh
              simp [f, hgn0, hgne, hhne] at this
              simpa using this
            have hunitc : IsUnit (g.coeff 0) := isUnit_of_mul_eq_one hlead
            have hgunit' : IsUnit g := by
              rw [Polynomial.eq_C_of_natDegree_eq_zero hgn0]
              simpa using (isUnit_C.mpr hunitc)
            exact hgunit hgunit'
          have hh0 : h.natDegree ≠ 0 := by
            intro hhn0
            have hlead : g.coeff 0 * Polynomial.leadingCoeff h = 1 := by
              have := congrArg Polynomial.leadingCoeff hgh
              simp [f, hhn0, hgne, hhne] at this
              simpa using this
            have hunitc : IsUnit (h.coeff 0) := by
              have : IsUnit (Polynomial.leadingCoeff h) := isUnit_of_mul_eq_one hlead
              simpa [hhn0] using this
            have hhunit' : IsUnit h := by
              rw [Polynomial.eq_C_of_natDegree_eq_zero hhn0]
              simpa using (isUnit_C.mpr hunitc)
            exact hhunit hhunit'
          have hgpos : 0 < g.natDegree := Nat.pos_of_ne_zero hg0
          have hhpos : 0 < h.natDegree := Nat.pos_of_ne_zero hh0
          have hgdeg : g.natDegree = 1 := by omega
          have hhdeg : h.natDegree = 1 := by omega
          have hg2 : coeff g 2 = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            omega
          have hh2 : coeff h 2 = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            omega
          have h2 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 2) hgh
          simp [f, hgdeg, hhdeg, hg2, hh2, coeff_mul] at h2
          have h1 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 1) hgh
          simp [f, hgdeg, hhdeg, hg2, hh2, coeff_mul] at h1
          have h0 := congrArg (fun p : Polynomial (Polynomial ℚ) => coeff p 0) hgh
          simp [f, hgdeg, hhdeg, coeff_mul] at h0
          have hac : coeff g 1 * coeff h 1 = 1 := by
            simpa using h2
          have had : coeff g 1 * coeff h 0 + coeff g 0 * coeff h 1 = 0 := by
            simpa using h1
          have hbd : coeff g 0 * coeff h 0 = Polynomial.X ^ 2 - 1 := by
            simpa using h0
          have hneg : coeff g 1 * coeff h 0 = - (coeff g 0 * coeff h 1) := by
            apply eq_neg_iff_add_eq_zero.mpr
            simpa [add_comm, add_left_comm, add_assoc] using had
          have hprod : (coeff g 1 * coeff h 0) * (coeff g 0 * coeff h 1) = Polynomial.X ^ 2 - 1 := by
            calc
              (coeff g 1 * coeff h 0) * (coeff g 0 * coeff h 1)
                  = (coeff g 1 * coeff h 1) * (coeff g 0 * coeff h 0) := by ring
              _ = Polynomial.X ^ 2 - 1 := by rw [hac, hbd]
          have hsquare : IsSquare (-(Polynomial.X ^ 2 - 1 : Polynomial ℚ)) := by
            refine ⟨coeff g 1 * coeff h 0, ?_⟩
            calc
              (coeff g 1 * coeff h 0)^2 = (coeff g 1 * coeff h 0) * (coeff g 1 * coeff h 0) := by ring
              _ = (coeff g 1 * coeff h 0) * (-(coeff g 0 * coeff h 1)) := by rw [hneg]
              _ = - ((coeff g 1 * coeff h 0) * (coeff g 0 * coeff h 1)) := by ring
              _ = -(Polynomial.X ^ 2 - 1) := by rw [hprod]
          exact hnsq hsquare
  have hfinal : Irreducible (e.symm f) := hpoly.map e.symm.toRingHom e.symm.injective
  simpa [e, e0, f, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hfinal
