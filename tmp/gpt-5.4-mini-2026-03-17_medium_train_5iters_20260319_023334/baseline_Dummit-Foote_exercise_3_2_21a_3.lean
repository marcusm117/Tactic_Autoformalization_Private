import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_21a (H : AddSubgroup ℚ) (hH : H ≠ ⊤) : H.index = 0 := by
  classical
  by_cases hfin : Fintype (ℚ ⧸ H)
  · let n : ℕ := Fintype.card (ℚ ⧸ H)
    have hdiv : Divisible (ℚ ⧸ H) := inferInstance
    have hzero : ∀ x : ℚ ⧸ H, x = 0 := by
      intro x
      rcases hdiv.divisible x n with ⟨y, hy⟩
      rw [← hy]
      simpa [n] using (Fintype.card_zsmul_eq_zero (ℚ ⧸ H) y)
    have hsub : Subsingleton (ℚ ⧸ H) := by
      refine ⟨?_⟩
      intro x y
      rw [hzero x, hzero y]
    have htop : H = ⊤ := by
      ext q
      constructor
      · intro _; trivial
      · intro hq
        have hq0 : (q : ℚ ⧸ H) = 0 := by
          exact Subsingleton.elim _ _
        simpa using (QuotientAddGroup.eq.mp hq0)
    exact hH htop
  · simp [Subgroup.index, Nat.card, hfin]
