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
      exact hx (by simp [htop])
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
      exact Ideal.eq_top_of_isUnit_mem hxI (hM x hxM)
    exact ⟨hMne_top, hMmax⟩
  · intro N hN
    have hNco : N ≠ ⊤ ∧ ∀ (b : Ideal R), N < b → b = ⊤ := hN.out
    have hNne : N ≠ ⊤ := hNco.1
    have hNM : N ≤ M := by
      intro x hxN
      by_contra hxM
      exact hNne (Ideal.eq_top_of_isUnit_mem hxN (hM x hxM))
    have hMN : M ≤ N := by
      by_contra hMN
      have hlt : N < M := ⟨hNM, hMN⟩
      exact hMne_top (hNco.2 M hlt)
    exact le_antisymm hMN hNM
