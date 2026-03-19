import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  let p : Polynomial F := Polynomial.X ^ 2 + Polynomial.X + (1 : Polynomial F)
  change Irreducible p
  have h01 : ∀ x : F, x = 0 ∨ x = 1 := by
    intro x
    have hx' : x ^ Fintype.card F = x := by
      simpa using (FiniteField.pow_card x)
    have hx : x ^ 2 = x := by
      simpa [hF] using hx'
    have hmul : x * (x - 1) = 0 := by
      calc
        x * (x - 1) = x ^ 2 - x := by ring
        _ = x - x := by rw [hx]
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
  have hdegX2 : Polynomial.natDegree ((Polynomial.X : Polynomial F) ^ 2) = 2 := by
    simp
  have hdegX2X : Polynomial.natDegree (((Polynomial.X : Polynomial F) ^ 2) + Polynomial.X) = 2 := by
    have h :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt
        (p := (Polynomial.X : Polynomial F) ^ 2) (q := (Polynomial.X : Polynomial F)) (by simp)
    simpa [hdegX2] using h
  have hdegp : Polynomial.natDegree p = 2 := by
    dsimp [p]
    have h :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt
        (p := ((Polynomial.X : Polynomial F) ^ 2 + Polynomial.X)) (q := (1 : Polynomial F))
        (by simp [hdegX2X])
    simpa [hdegX2X] using h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    have : (0 : ℕ) = 2 := by simpa [hp0] using hdegp
    omega
  have hnoroot : ∀ x : F, p.eval x ≠ 0 := by
    intro x
    rcases h01 x with rfl | rfl
    · simp [p]
    · simp [p, hone]
  refine ⟨?_, ?_⟩
  · intro hpunit
    have h0 : Polynomial.natDegree p = 0 := Polynomial.natDegree_eq_zero_of_isUnit hpunit
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
          exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcoeff)
        have hdb_ne : Polynomial.natDegree b ≠ 0 := by
          intro hdb
          have hbC : b = Polynomial.C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdb
          have hcoeff : b.coeff 0 ≠ 0 := by
            intro hc
            apply hbne
            rw [hbC, hc, Polynomial.C_0]
          apply hub
          rw [hbC]
          exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcoeff)
        have hsum' : Polynomial.natDegree (a * b) = 2 := by
          simpa [hab] using hdegp
        have hsum : Polynomial.natDegree a + Polynomial.natDegree b = 2 := by
          rw [Polynomial.natDegree_mul hane hbne] at hsum'
          exact hsum'
        have hpa : 0 < Polynomial.natDegree a := Nat.pos_of_ne_zero hda_ne
        have hpb : 0 < Polynomial.natDegree b := Nat.pos_of_ne_zero hdb_ne
        have hda1 : Polynomial.natDegree a = 1 := by
          omega
        have hdega1 : Polynomial.degree a = 1 := by
          rw [Polynomial.degree_eq_natDegree hane, hda1]
        rcases Polynomial.exists_root_of_degree_eq_one hdega1 with ⟨x, hx⟩
        have hax : a.eval x = 0 := by
          simpa [Polynomial.IsRoot] using hx
        have hp0 : p.eval x = 0 := by
          rw [hab, Polynomial.eval_mul, hax, zero_mul]
        exact hnoroot x hp0
