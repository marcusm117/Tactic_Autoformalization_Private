import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  classical
  have hcard01 : ({(0 : F), 1} : Finset F).card = 2 := by
    simp
  have hset : ({(0 : F), 1} : Finset F) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simpa using hx
    · simpa [hcard01, hF]
  have hcases : ∀ a : F, a = 0 ∨ a = 1 := by
    intro a
    have ha : a ∈ ({(0 : F), 1} : Finset F) := by
      have : a ∈ (Finset.univ : Finset F) := by simp
      simpa [hset] using this
    simpa using ha
  have h11 : (1 : F) + 1 = 0 := by
    have hmem : (1 + 1 : F) ∈ ({(0 : F), 1} : Finset F) := by
      have : (1 + 1 : F) ∈ (Finset.univ : Finset F) := by simp
      simpa [hset] using this
    have h01 : (1 + 1 : F) = 0 ∨ (1 + 1 : F) = 1 := by
      simpa using hmem
    rcases h01 with h | h
    · exact h
    · exfalso
      have h10 : (1 : F) = 0 := by
        apply add_left_cancel
        simpa using h
      exact zero_ne_one h10.symm
  have hroot : ∀ a : F, ¬ (X ^ 2 + X + 1 : Polynomial F).IsRoot a := by
    intro a ha
    rcases hcases a with rfl | rfl
    · simpa [Polynomial.IsRoot] using ha
    · simpa [Polynomial.IsRoot, h11] using ha
  have hdeg : (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 := by
    simp
  exact Polynomial.irreducible_of_natDegree_eq_two hdeg hroot
