import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  classical
  have hne : ∃ x : GaussianInt, x ∈ I ∧ x ≠ 0 := by
    by_contra h
    have hsub : I ≤ (⊥ : Ideal GaussianInt) := by
      intro x hx
      by_contra hx0
      exact h ⟨x, hx, hx0⟩
    have hEq : I = ⊥ := le_antisymm hsub bot_le
    exact hI hEq
  rcases hne with ⟨x, hxI, hx0⟩
  rcases x with ⟨a, b⟩
  by_cases hb : b = 0
  · refine ⟨⟨⟨a, 0⟩, by simpa [hb] using hxI⟩, ?_, ?_⟩
    · simpa [hb] using hx0
    · simp [hb]
  · by_cases ha : a = 0
    · let z : GaussianInt := (⟨0, 1⟩ : GaussianInt) • (⟨0, b⟩ : GaussianInt)
      have hzmem : z ∈ I := by
        simpa [z] using I.smul_mem (⟨0, 1⟩ : GaussianInt) hxI
      have him : z.im = 0 := by
        dsimp [z]
        simp [ha]
        ring
      have hzne : z ≠ 0 := by
        simpa [z, ha] using hb
      refine ⟨⟨z, hzmem⟩, hzne, him⟩
    · let z : GaussianInt :=
        (⟨a, b⟩ : GaussianInt) • (⟨a, b⟩ : GaussianInt) +
          ((-2 * a : ℤ) : GaussianInt) • (⟨a, b⟩ : GaussianInt)
      have hzmem : z ∈ I := by
        simpa [z] using
          I.add_mem (I.smul_mem (⟨a, b⟩ : GaussianInt) hxI)
            (I.smul_mem ((-2 * a : ℤ) : GaussianInt) hxI)
      have him : z.im = 0 := by
        dsimp [z]
        simp [ha, hb]
        ring
      have hzre : z.re = -((a^2 + b^2 : ℤ)) := by
        dsimp [z]
        simp [ha, hb]
        ring
      have hsumpos : 0 < (a^2 + b^2 : ℤ) := by
        have ha2 : 0 < a^2 := by
          exact sq_pos_iff.mpr ha
        have hb2 : 0 < b^2 := by
          exact sq_pos_iff.mpr hb
        linarith
      have hzne : z ≠ 0 := by
        intro hz0
        have hzre0 : z.re = 0 := by
          simpa using congrArg GaussianInt.re hz0
        have hbad : -((a^2 + b^2 : ℤ)) = 0 := by
          simpa [hzre] using hzre0
        linarith
      refine ⟨⟨z, hzmem⟩, hzne, him⟩
