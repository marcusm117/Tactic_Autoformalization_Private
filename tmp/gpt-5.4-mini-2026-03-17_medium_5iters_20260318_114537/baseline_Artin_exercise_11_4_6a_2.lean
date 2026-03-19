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
      simp at hx
    · simpa [hcard01, hF]
  have hcases : ∀ a : F, a = 0 ∨ a = 1 := by
    intro a
    have ha : a ∈ ({(0 : F), 1} : Finset F) := by
      simpa [hset] using (show a ∈ (Finset.univ : Finset F) by simp)
    simpa using ha
  have h11 : (1 : F) + 1 = 0 := by
    have hmem : (1 + 1 : F) ∈ ({(0 : F), 1} : Finset F) := by
      simpa [hset] using (show (1 + 1 : F) ∈ (Finset.univ : Finset F) by simp)
    rcases (by simpa using hmem : (1 + 1 : F) = 0 ∨ (1 + 1 : F) = 1) with h0 | h1
    · exact h0
    · exfalso
      have h10 : (1 : F) = 0 := by
        apply add_left_cancel at h1
        exact h1
      exact one_ne_zero h10
  have hroot : ∀ a : F, ¬ (X ^ 2 + X + 1 : Polynomial F).IsRoot a := by
    intro a
    rcases hcases a with rfl | rfl
    · intro ha
      simpa [Polynomial.IsRoot] using ha
    · intro ha
      simpa [Polynomial.IsRoot, h11] using ha
  have hdeg : (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 := by simp
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdeg0 : (X ^ 2 + X + 1 : Polynomial F).natDegree = 0 := by
      simpa using Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro q r hqr
    by_cases hq : IsUnit q
    · exact Or.inl hq
    · right
      by_contra hr
      have hp0 : (X ^ 2 + X + 1 : Polynomial F) ≠ 0 := by
        intro hp0
        have : (2 : ℕ) = 0 := by simpa [hp0] using hdeg
        omega
      have hq0 : q ≠ 0 := by
        intro hq0
        exact hp0 (by simpa [hq0] using hqr)
      have hr0 : r ≠ 0 := by
        intro hr0
        exact hp0 (by simpa [hr0] using hqr)
      have hqpos : 0 < q.natDegree := by
        exact Polynomial.natDegree_pos_iff.mpr ⟨hq0, hq⟩
      have hrpos : 0 < r.natDegree := by
        exact Polynomial.natDegree_pos_iff.mpr ⟨hr0, hr⟩
      have hsum : q.natDegree + r.natDegree = 2 := by
        have h := congrArg Polynomial.natDegree hqr
        rw [hdeg, Polynomial.natDegree_mul hq0 hr0] at h
        exact h.symm
      have hq1 : q.natDegree = 1 := by omega
      rcases Polynomial.exists_root_of_natDegree_eq_one hq1 with ⟨a, ha⟩
      have hproot : (X ^ 2 + X + 1 : Polynomial F).IsRoot a := by
        rw [hqr]
        simpa [Polynomial.IsRoot] using ha
      exact hroot a hproot
