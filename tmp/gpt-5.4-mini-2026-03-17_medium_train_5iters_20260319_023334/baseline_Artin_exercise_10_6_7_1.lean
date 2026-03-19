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
      by_cases hx0 : x = 0
      · simpa [hx0]
      · exact False.elim (h ⟨x, hx, hx0⟩)
    have hEq : I = ⊥ := le_antisymm hsub bot_le
    exact hI hEq
  rcases hne with ⟨x, hxI, hx0⟩
  let y : GaussianInt := ⟨x.re, -x.im⟩
  have hyne : y ≠ 0 := by
    intro hy
    apply hx0
    simpa [y] using hy
  have hzmem : x * y ∈ I := by
    simpa [y, mul_comm] using I.smul_mem y hxI
  have him : (x * y : GaussianInt).im = 0 := by
    cases x with
    | mk a b =>
        dsimp [y]
        simp [mul_comm, mul_left_comm, mul_assoc]
        ring
  refine ⟨⟨x * y, hzmem⟩, ?_, ?_⟩
  · simpa using mul_ne_zero hx0 hyne
  · simpa [y] using him
