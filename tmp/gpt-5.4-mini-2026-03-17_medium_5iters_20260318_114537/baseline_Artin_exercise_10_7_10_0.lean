import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_7_10 {R : Type*} [Ring R]
  (M : Ideal R) (hM : ∀ (x : R), x ∉ M → IsUnit x)
  (hProper : ∃ x : R, x ∉ M) :
  IsMaximal M ∧ ∀ (N : Ideal R), IsMaximal N → N = M := by
  constructor
  · have hMne_top : M ≠ ⊤ := by
      intro htop
      rcases hProper with ⟨x, hx⟩
      exact hx (by simpa [htop])
    have hMmax : ∀ ⦃I : Ideal R⦄, M < I → I = ⊤ := by
      intro I hlt
      have hnot : ¬ I ≤ M := hlt.2
      have hex : ∃ x : R, x ∈ I ∧ x ∉ M := by
        by_contra h
        have hsub : I ≤ M := by
          intro x hxI
          by_contra hxM
          exact h ⟨x, hxI, hxM⟩
        exact hnot hsub
      rcases hex with ⟨x, hxI, hxM⟩
      exact Ideal.eq_top_of_isUnit_mem (hM x hxM) hxI
    exact ⟨hMne_top, hMmax⟩
  · intro N hN
    have hNM : N ≤ M := by
      intro x hxN
      by_contra hxM
      have hxunit : IsUnit x := hM x hxM
      exact hN.1 (Ideal.eq_top_of_isUnit_mem hxunit hxN)
    have hMne_top : M ≠ ⊤ := by
      intro htop
      rcases hProper with ⟨x, hx⟩
      exact hx (by simpa [htop])
    by_cases hEq : N = M
    · exact hEq
    · have hlt : N < M := lt_of_le_of_ne hNM hEq
      have htop : M = ⊤ := hN.2 hlt
      exact False.elim (hMne_top htop)
