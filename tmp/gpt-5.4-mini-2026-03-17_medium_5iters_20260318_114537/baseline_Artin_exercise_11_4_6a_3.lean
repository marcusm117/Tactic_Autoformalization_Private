import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  classical
  have hcard01 : ({(0 : F), 1} : Finset F).card = 2 := by simp
  have hset : ({(0 : F), 1} : Finset F) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp
    · simpa [hcard01, hF]
  have hcases : ∀ a : F, a = 0 ∨ a = 1 := by
    intro a
    have ha : a ∈ ({(0 : F), 1} : Finset F) := by
      rw [hset]
      simp
    simpa using ha
  have h11 : (1 : F) + 1 = 0 := by
    have hmem : (1 + 1 : F) ∈ ({(0 : F), 1} : Finset F) := by
      rw [hset]
      simp
    have h01 : (1 + 1 : F) = 0 ∨ (1 + 1 : F) = 1 := by
      simpa using hmem
    rcases h01 with h0 | h1
    · exact h0
    · exfalso
      have h10 : (1 : F) = 0 := by
        have h1' : (1 : F) + 1 = 1 + 0 := by simpa using h1
        exact add_left_cancel h1'
      exact one_ne_zero h10
  have hroot : ∀ a : F, ¬ (X ^ 2 + X + 1 : Polynomial F).IsRoot a := by
    intro a
    rcases hcases a with rfl | rfl
    · intro ha
      have hcalc : (X ^ 2 + X + 1 : Polynomial F).eval 0 = (1 : F) := by
        simp
      have hne : (X ^ 2 + X + 1 : Polynomial F).eval 0 ≠ 0 := by
        rw [hcalc]
        exact one_ne_zero
      exact hne ha
    · intro ha
      have hcalc : (X ^ 2 + X + 1 : Polynomial F).eval 1 = (1 : F) := by
        simp [h11]
      have hne : (X ^ 2 + X + 1 : Polynomial F).eval 1 ≠ 0 := by
        rw [hcalc]
        exact one_ne_zero
      exact hne ha
  have hdeg : (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 := by simp
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdeg0 : (X ^ 2 + X + 1 : Polynomial F).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro q r hqr
    by_cases hq : IsUnit q
    · exact Or.inl hq
    · by_cases hr : IsUnit r
      · exact Or.inr hr
      · exfalso
        have hp0 : (X ^ 2 + X + 1 : Polynomial F) ≠ 0 := by
          intro hp0
          have : (0 : ℕ) = 2 := by simpa [hp0] using hdeg
          omega
        have hqnz : q ≠ 0 := by
          intro hq0
          apply hp0
          rw [hqr, hq0]
          simp
        have hrnz : r ≠ 0 := by
          intro hr0
          apply hp0
          rw [hqr, hr0]
          simp
        have hqpos : 0 < q.natDegree := by
          by_contra hqpos
          have hq0deg : q.natDegree = 0 := Nat.eq_zero_of_not_pos hqpos
          exact hq (Polynomial.isUnit_iff_natDegree_eq_zero.2 hq0deg)
        have hrpos : 0 < r.natDegree := by
          by_contra hrpos
          have hr0deg : r.natDegree = 0 := Nat.eq_zero_of_not_pos hrpos
          exact hr (Polynomial.isUnit_iff_natDegree_eq_zero.2 hr0deg)
        have hsum : q.natDegree + r.natDegree = 2 := by
          have h := congrArg Polynomial.natDegree hqr
          rw [hdeg, Polynomial.natDegree_mul hqnz hrnz] at h
          omega
        have hq1 : q.natDegree = 1 := by omega
        have hqdeg : q.degree = 1 := by
          rw [Polynomial.degree_eq_natDegree hqnz, hq1]
        rcases Polynomial.exists_root_of_degree_eq_one hqdeg with ⟨a, ha⟩
        have hproot : (X ^ 2 + X + 1 : Polynomial F).IsRoot a := by
          rw [hqr]
          simpa [Polynomial.IsRoot] using ha
        exact hroot a hproot
