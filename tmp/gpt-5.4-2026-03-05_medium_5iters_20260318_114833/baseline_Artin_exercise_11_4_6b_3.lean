import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6b {F : Type*} [Field F] [Fintype F] (hF : card F = 7) :
  Irreducible (X ^ 2 + 1 : Polynomial F) := by
  classical
  let p : Polynomial F := X ^ 2 + 1
  have hpdeg : p.natDegree = 2 := by
    simpa [p] using
      (Polynomial.natDegree_X_pow_add_C (R := F) (n := 2) (r := (1 : F)) one_ne_zero)
  have h7zero : (7 : F) = 0 := by
    simpa [hF, nsmul_eq_mul] using (Fintype.card_smul_eq_zero (1 : F))
  haveI : CharP F (ringChar F) := ringChar.charP F
  have hdiv7 : ringChar F ∣ 7 := by
    rw [← CharP.cast_eq_zero_iff (R := F) (p := ringChar F) 7]
    exact h7zero
  have hpchar : Nat.Prime (ringChar F) := Fact.out
  have hchar : ringChar F = 7 := by
    have hle : ringChar F ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hdiv7
    have hge : 2 ≤ ringChar F := hpchar.two_le
    interval_cases ringChar F <;> norm_num at hdiv7 ⊢
  have h2ne : (2 : F) ≠ 0 := by
    intro h2
    have hdiv2 : ringChar F ∣ 2 := by
      rw [← CharP.cast_eq_zero_iff (R := F) (p := ringChar F) 2]
      exact h2
    have : 7 ∣ 2 := by
      simpa [hchar] using hdiv2
    norm_num at this
  have hnoroot : ∀ a : F, ¬ p.IsRoot a := by
    intro a ha
    have hs : a ^ 2 + 1 = 0 := by
      simpa [p] using ha
    have hsq : a ^ 2 = (-1 : F) := by
      exact eq_neg_iff_add_eq_zero.mpr hs
    have ha0 : a ≠ 0 := by
      intro h0
      subst h0
      simp [p] at ha
    have hunits : Fintype.card Fˣ = 6 := by
      rw [Fintype.card_units, hF]
      norm_num
    let u : Fˣ := Units.mk0 a ha0
    have hu : u ^ Fintype.card Fˣ = 1 := by
      simpa using pow_card_eq_one u
    have ha6 : a ^ 6 = (1 : F) := by
      have hu' : (((u ^ Fintype.card Fˣ : Fˣ) : F)) = (1 : F) := by
        exact congrArg (fun x : Fˣ => (x : F)) hu
      simpa [u, hunits] using hu'
    have ha6' : a ^ 6 = (-1 : F) := by
      calc
        a ^ 6 = (a ^ 2) ^ 3 := by rw [show 6 = 2 * 3 by norm_num, pow_mul]
        _ = (-1 : F) ^ 3 := by rw [hsq]
        _ = (-1 : F) := by norm_num
    have h1 : (1 : F) = (-1 : F) := by
      calc
        (1 : F) = a ^ 6 := by symm; exact ha6
        _ = (-1 : F) := ha6'
    have htwo : (2 : F) = 0 := by
      calc
        (2 : F) = (1 : F) + 1 := by norm_num
        _ = (-1 : F) + 1 := by rw [h1]
        _ = 0 := by simp
    exact h2ne htwo
  refine ⟨?_, ?_⟩
  · intro hpunit
    have h := Polynomial.natDegree_eq_zero_of_isUnit hpunit
    rw [hpdeg] at h
    norm_num at h
  · intro f g hfg
    by_cases hf : IsUnit f
    · exact Or.inl hf
    · by_cases hg : IsUnit g
      · exact Or.inr hg
      · have hp0 : p ≠ 0 := by
          simp [p]
        have hf0 : f ≠ 0 := by
          intro h0
          apply hp0
          simpa [h0] using hfg
        have hg0 : g ≠ 0 := by
          intro h0
          apply hp0
          simpa [h0] using hfg
        have hfpos : 0 < f.natDegree := by
          refine Nat.pos_of_ne_zero ?_
          intro hdeg
          have hfc : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
          apply hf
          rw [hfc]
          refine Polynomial.isUnit_C.2 ?_
          refine isUnit_iff_ne_zero.2 ?_
          intro hc
          apply hf0
          rw [hfc, hc]
          simp
        have hgpos : 0 < g.natDegree := by
          refine Nat.pos_of_ne_zero ?_
          intro hdeg
          have hgc : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
          apply hg
          rw [hgc]
          refine Polynomial.isUnit_C.2 ?_
          refine isUnit_iff_ne_zero.2 ?_
          intro hc
          apply hg0
          rw [hgc, hc]
          simp
        have hdegmul : f.natDegree + g.natDegree = 2 := by
          rw [← hpdeg, hfg, Polynomial.natDegree_mul' hf0 hg0]
        have hf1 : f.natDegree = 1 := by
          omega
        rcases Polynomial.exists_root_of_natDegree_eq_one hf1 with ⟨a, ha⟩
        exfalso
        exact hnoroot a <| by
          rw [hfg]
          exact Polynomial.isRoot_mul.2 (Or.inl ha)
