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
    have hmul : (⟨1, -1⟩ : GaussianInt) * ⟨1, 1⟩ = (2 : GaussianInt) := by
      ext <;> omega
    rw [← hmul]
    exact Ideal.mul_mem_left _ _ hgen
  have hclasses : ∀ x : GaussianInt ⧸ I, x = 0 ∨ x = 1 := by
    intro x
    refine Quotient.inductionOn x ?_
    intro g
    have hcalc : g - ((g.re - g.im : Int) : GaussianInt) = (g.im : GaussianInt) * ⟨1, 1⟩ := by
      ext <;> simp [sub_eq_add_neg]
      · omega
      · rfl
    have hdecomp :
        (Ideal.Quotient.mk I g) = (Ideal.Quotient.mk I ((g.re - g.im : Int) : GaussianInt)) := by
      apply Ideal.Quotient.eq.mpr
      rw [hcalc]
      exact Ideal.mul_mem_left _ _ hgen
    rcases Int.even_or_odd (g.re - g.im) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have ht : (((g.re - g.im : Int) : GaussianInt)) ∈ I := by
        rw [hk]
        simpa [mul_comm] using
          (Ideal.mul_mem_left (I := I) (a := (2 : GaussianInt)) (b := (k : GaussianInt)) h2)
      have hq : (Ideal.Quotient.mk I ((g.re - g.im : Int) : GaussianInt)) = (0 : GaussianInt ⧸ I) := by
        apply Ideal.Quotient.eq.mpr
        simpa using ht
      left
      simpa [hdecomp] using hq
    · have hm : ((2 * k : Int) : GaussianInt) ∈ I := by
        simpa [mul_comm] using
          (Ideal.mul_mem_left (I := I) (a := (2 : GaussianInt)) (b := (k : GaussianInt)) h2)
      have ht : ((((g.re - g.im : Int) : GaussianInt) - 1)) ∈ I := by
        rw [hk]
        simpa using hm
      have hq : (Ideal.Quotient.mk I ((g.re - g.im : Int) : GaussianInt)) = (1 : GaussianInt ⧸ I) := by
        apply Ideal.Quotient.eq.mpr
        simpa using ht
      right
      simpa [hdecomp] using hq
  let e : (GaussianInt ⧸ I) ≃ Fin 2 :=
    { toFun := fun x => if hx : x = 0 then 0 else 1
      invFun := fun n => if hn : (n : Fin 2) = 0 then (0 : GaussianInt ⧸ I) else 1
      left_inv := by
        intro x
        by_cases hx0 : x = 0
        · simp [hx0]
        · rcases hclasses x with rfl | rfl
          · contradiction
          · simp [hx0]
      right_inv := by
        intro n
        fin_cases n <;> simp }
  haveI : Fintype (GaussianInt ⧸ I) := Fintype.ofEquiv _ e
  have hcard : Fintype.card (GaussianInt ⧸ I) = 2 := by
    simpa using (Fintype.card_congr e)
  have hfield : IsField (GaussianInt ⧸ I) := by
    exact isField_of_card_eq_two hcard
  refine ⟨hfield, ?_⟩
  exact ⟨inferInstance, hcard⟩
