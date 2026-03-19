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
      have h1' : (1 : F) + 1 = 1 + 0 := by simpa using h1
      have h10 : (1 : F) = 0 := by
        exact add_left_cancel h1'
      exact one_ne_zero h10
  have hroot : ∀ a : F, ¬ (X ^ 2 + X + 1 : Polynomial F).IsRoot a := by
    intro a
    rcases hcases a with rfl | rfl
    · intro ha
      simp [Polynomial.IsRoot] at ha
      exact one_ne_zero ha
    · intro ha
      simp [Polynomial.IsRoot, h11] at ha
      exact one_ne_zero ha
  have hdeg : (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 := by
    simp
  exact Polynomial.irreducible_of_no_roots hdeg hroot
