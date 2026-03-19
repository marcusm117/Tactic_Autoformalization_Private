import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_6a {R : Type} [Ring R]
  (hR : R = (GaussianInt ⧸ span ({⟨1, 1⟩} : Set GaussianInt))) :
  IsField R ∧ ∃ finR : Fintype R, @card R finR = 2 := by
  subst hR
  classical
  set I : Ideal GaussianInt := Ideal.span ({⟨1, 1⟩} : Set GaussianInt) with hI
  have hgen : (⟨1, 1⟩ : GaussianInt) ∈ I := by
    rw [hI]
    exact Ideal.subset_span (by simp)
  have h2 : (2 : GaussianInt) ∈ I := by
    have hmul : (⟨1, 1⟩ : GaussianInt) * ⟨1, -1⟩ = (2 : GaussianInt) := by
      ext <;> simp
    rw [← hmul]
    simpa [mul_comm] using (Ideal.mul_mem_left _ _ hgen : (⟨1, -1⟩ : GaussianInt) * ⟨1, 1⟩ ∈ I)
  have hclasses : ∀ x : GaussianInt ⧸ I, x = 0 ∨ x = 1 := by
    intro x
    refine Quotient.inductionOn x ?_
    intro g
    have hcalc : g - ((g.re - g.im : Int) : GaussianInt) = (g.im : GaussianInt) * ⟨1, 1⟩ := by
      ext <;> ring
    have hdecomp :
        (Ideal.Quotient.mk I g) = (Ideal.Quotient.mk I ((g.re - g.im : Int) : GaussianInt)) := by
      apply Ideal.Quotient.eq.mpr
      rw [hcalc]
      exact Ideal.mul_mem_left _ _ hgen
    rw [hdecomp]
    rcases Int.even_or_odd (g.re - g.im) with h | h
    · rcases h with ⟨k, hk⟩
      left
      apply Ideal.Quotient.eq.mpr
      have hk' : (g.re - g.im : Int) = 2 * k := by
        omega
      rw [hk']
      simpa [mul_comm] using (Ideal.mul_mem_left _ _ h2 : (k : GaussianInt) * (2 : GaussianInt) ∈ I)
    · rcases h with ⟨k, hk⟩
      right
      apply Ideal.Quotient.eq.mpr
      have hk' : (g.re - g.im : Int) - 1 = 2 * k := by
        omega
      rw [hk']
      simpa [mul_comm] using (Ideal.mul_mem_left _ _ h2 : (k : GaussianInt) * (2 : GaussianInt) ∈ I)
  let e : (GaussianInt ⧸ I) ≃ Fin 2 :=
    { toFun := fun x => if hx : x = 0 then 0 else 1
      invFun := fun n => Fin.cases (0 : GaussianInt ⧸ I) 1 n
      left_inv := by
        intro x
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hx1 : x = 1 := by
            rcases hclasses x with rfl | rfl
            · contradiction
            · rfl
          simp [hx0, hx1]
      right_inv := by
        intro n
        fin_cases n <;> rfl }
  haveI : Fintype (GaussianInt ⧸ I) := Fintype.ofEquiv _ e
  have hcard : Fintype.card (GaussianInt ⧸ I) = 2 := by
    simpa using (Fintype.card_congr e)
  have hfield : IsField (GaussianInt ⧸ I) := by
    exact isField_of_card_eq_two hcard
  refine ⟨by simpa [hI] using hfield, ?_⟩
  refine ⟨by simpa [hI] using inferInstance, ?_⟩
  simpa [hI] using hcard
