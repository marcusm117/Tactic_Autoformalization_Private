import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_7_10 {R : Type*} [Ring R]
  (M : Ideal R) (hM : ∀ (x : R), x ∉ M → IsUnit x)
  (hProper : ∃ x : R, x ∉ M) :
  IsMaximal M ∧ ∀ (N : Ideal R), IsMaximal N → N = M := by
  have htop_of_unit_mem : ∀ {I : Ideal R} {x : R}, x ∈ I → IsUnit x → I = ⊤ := by
    intro I x hxI hxu
    rcases hxu with ⟨u, rfl⟩
    apply top_unique
    intro y hy
    have h1 : (1 : R) ∈ I := by
      simpa using I.mul_mem_left (↑(u⁻¹) : R) hxI
    simpa using I.mul_mem_left y h1
  have hM_ne_top : M ≠ ⊤ := by
    rcases hProper with ⟨x, hx⟩
    intro htop
    exact hx (by simpa [htop] using (show x ∈ (⊤ : Ideal R) from by simp))
  have hMaxM : IsMaximal M := by
    refine ⟨hM_ne_top, ?_⟩
    intro J hMJ
    by_cases hJM : J = M
    · left
      exact hJM
    · right
      have hnot_le : ¬ J ≤ M := by
        intro hle
        exact hJM (le_antisymm hle hMJ)
      have hex : ∃ x : R, x ∈ J ∧ x ∉ M := by
        by_contra h
        apply hnot_le
        intro x hxJ
        by_contra hxM
        exact h ⟨x, hxJ, hxM⟩
      rcases hex with ⟨x, hxJ, hxM⟩
      exact htop_of_unit_mem hxJ (hM x hxM)
  refine ⟨hMaxM, ?_⟩
  intro N hN
  have hNM : N ≤ M := by
    intro x hxN
    by_contra hxM
    have hNtop : N = ⊤ := htop_of_unit_mem hxN (hM x hxM)
    exact hN.1 hNtop
  rcases hN.2 M hNM with hEq | hTop
  · exact hEq.symm
  · exact False.elim (hMaxM.1 hTop)
