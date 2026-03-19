import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_6a {R : Type} [Ring R]
  (hR : R = (GaussianInt ⧸ span ({⟨1, 1⟩} : Set GaussianInt))) :
  IsField R ∧ ∃ finR : Fintype R, @card R finR = 2 := by
  subst hR
  classical
  set I : Ideal GaussianInt := Ideal.span ({⟨1, 1⟩} : Set GaussianInt) with hI
  let f : GaussianInt →+* ZMod 2 :=
    { toFun := fun z => (z.re + z.im : ZMod 2)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by
        intro a b
        simp [add_comm, add_left_comm, add_assoc]
      map_mul' := by
        intro a b
        simp [add_comm, add_left_comm, add_assoc, mul_add, add_mul, sub_eq_add_neg,
          Zsqrtd.re_mul, Zsqrtd.im_mul] }
  have hker : I = f.ker := by
    ext z
    constructor
    · intro hz
      have hz' : ((z.re + z.im : ℤ) : ZMod 2) = 0 := by
        simpa [f] using hz
      have hsum : (2 : ℤ) ∣ z.re + z.im := by
        exact (Int.cast_zmod_eq_zero_iff_dvd).mp hz'
      rcases hsum with ⟨m, hm⟩
      have hdiff : (2 : ℤ) ∣ z.im - z.re := by
        refine ⟨m - z.re, ?_⟩
        omega
      rcases hdiff with ⟨n, hn⟩
      have hre : m - n = z.re := by omega
      have him : m + n = z.im := by omega
      rw [hI]
      apply Ideal.mem_span_singleton.mpr
      refine ⟨⟨m, n⟩, ?_⟩
      ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul, hre, him]
    · intro hz
      rw [hI] at hz
      rw [Ideal.mem_span_singleton] at hz
      rcases hz with ⟨q, hq⟩
      rcases hq with rfl
      simp [f, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hsurj : Function.Surjective f := by
    intro z
    fin_cases z
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f]⟩
  have heq : GaussianInt ⧸ I ≃+* ZMod 2 := by
    simpa [hker] using (Ideal.quotientKerEquivOfSurjective f hsurj)
  have hfield : IsField (GaussianInt ⧸ I) := by
    exact (RingEquiv.isField_iff heq).2 inferInstance
  haveI : Fintype (GaussianInt ⧸ I) := Fintype.ofEquiv _ heq.toEquiv
  have hcard : Fintype.card (GaussianInt ⧸ I) = 2 := by
    simpa using (Fintype.card_congr heq.toEquiv)
  refine ⟨hfield, ?_⟩
  exact ⟨inferInstance, by simpa using hcard⟩
