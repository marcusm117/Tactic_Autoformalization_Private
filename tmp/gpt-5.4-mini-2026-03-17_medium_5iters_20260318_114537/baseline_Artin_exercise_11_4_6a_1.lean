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
      simpa using hx
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
        apply add_left_cancel
        simpa using h1
      exact one_ne_zero h10
  have hroot : ∀ a : F, ¬ (X ^ 2 + X + 1 : Polynomial F).IsRoot a := by
    intro a
    rcases hcases a with rfl | rfl
    · simp [Polynomial.IsRoot]
    · simp [Polynomial.IsRoot, h11]
  have hdeg : (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 := by simp
  exact Polynomial.irreducible_of_no_root (p := X ^ 2 + X + 1) hdeg hroot
