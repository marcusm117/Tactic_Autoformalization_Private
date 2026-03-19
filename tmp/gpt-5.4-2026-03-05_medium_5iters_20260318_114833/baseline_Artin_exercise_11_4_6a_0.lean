import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  have h01 : ∀ x : F, x = 0 ∨ x = 1 := by
    intro x
    have hx : x ^ 2 = x := by
      simpa [hF] using (FiniteField.pow_card x)
    have hmul : x * (x - 1) = 0 := by
      calc
        x * (x - 1) = x ^ 2 - x := by ring
        _ = x - x := by simpa [hx]
        _ = 0 := sub_self x
    rcases mul_eq_zero.mp hmul with hx0 | hx1
    · exact Or.inl hx0
    · exact Or.inr (sub_eq_zero.mp hx1)
  have hone : (1 : F) + 1 = 0 := by
    rcases h01 ((1 : F) + 1) with h | h
    · exact h
    · exfalso
      have h' : (1 : F) = 0 := by
        apply add_left_cancel (a := (1 : F))
        simpa using h
      exact zero_ne_one h'.symm
  have hdegp1 : Polynomial.natDegree (((X : Polynomial F) ^ 2) + X) = 2 := by
    refine Polynomial.natDegree_add_eq_left_of_natDegree_lt ?_
    simp
  have hdegp : Polynomial.natDegree ((X ^ 2 + X + 1 : Polynomial F)) = 2 := by
    refine Polynomial.natDegree_add_eq_left_of_natDegree_lt ?_
    simpa [hdegp1]
  have hp_ne_zero : (X ^ 2 + X + 1 : Polynomial F) ≠ 0 := by
    simp
  have hnoroot : ∀ x : F, ((X ^ 2 + X + 1 : Polynomial F).eval x) ≠ 0 := by
    intro x
    rcases h01 x with rfl | rfl
    · simp
    · simp [hone]
  refine ⟨?_, ?_⟩
  · intro hpunit
    have hdeg0 : Polynomial.natDegree ((X ^ 2 + X + 1 : Polynomial F)) = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hpunit
    omega
  · intro a b hab
    by_cases hua : IsUnit a
    · exact Or.inl hua
    · by_cases hub : IsUnit b
      · exact Or.inr hub
      · exfalso
        have hane : a ≠ 0 := by
          intro ha
          rw [ha, zero_mul] at hab
          exact hp_ne_zero hab
        have hbne : b ≠ 0 := by
          intro hb
          rw [hb, mul_zero] at hab
          exact hp_ne_zero hab
        have hda_ne : Polynomial.natDegree a ≠ 0 := by
          intro hda
          have haC : a = Polynomial.C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hda
          have hcoeff : a.coeff 0 ≠ 0 := by
            intro hc
            apply hane
            rw [haC, hc, Polynomial.C_0]
          apply hua
          rw [haC]
          simpa using (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcoeff))
        have hdb_ne : Polynomial.natDegree b ≠ 0 := by
          intro hdb
          have hbC : b = Polynomial.C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdb
          have hcoeff : b.coeff 0 ≠ 0 := by
            intro hc
            apply hbne
            rw [hbC, hc, Polynomial.C_0]
          apply hub
          rw [hbC]
          simpa using (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcoeff))
        have hsum : Polynomial.natDegree a + Polynomial.natDegree b = 2 := by
          calc
            Polynomial.natDegree a + Polynomial.natDegree b = Polynomial.natDegree (a * b) := by
              symm
              exact Polynomial.natDegree_mul' hane hbne
            _ = 2 := by simpa [hab] using hdegp
        have hda1 : Polynomial.natDegree a = 1 := by
          have hpa : 0 < Polynomial.natDegree a := Nat.pos_of_ne_zero hda_ne
          have hpb : 0 < Polynomial.natDegree b := Nat.pos_of_ne_zero hdb_ne
          omega
        have hma : a.Monic := by
          unfold Polynomial.Monic
          rcases h01 (Polynomial.leadingCoeff a) with h0 | h1
          · exfalso
            exact (Polynomial.leadingCoeff_ne_zero.mpr hane) h0
          · exact h1
        have haform : a = X + Polynomial.C (a.coeff 0) := by
          simpa using hma.eq_X_add_C_of_natDegree_eq_one hda1
        have hroota : ∃ x : F, a.eval x = 0 := by
          rcases h01 (a.coeff 0) with h0 | h1
          · refine ⟨0, ?_⟩
            rw [haform, h0]
            simp
          · refine ⟨1, ?_⟩
            rw [haform, h1]
            simp [hone]
        rcases hroota with ⟨x, hx⟩
        have hp0 : ((X ^ 2 + X + 1 : Polynomial F).eval x) = 0 := by
          rw [hab, Polynomial.eval_mul, hx, zero_mul]
        exact hnoroot x hp0
