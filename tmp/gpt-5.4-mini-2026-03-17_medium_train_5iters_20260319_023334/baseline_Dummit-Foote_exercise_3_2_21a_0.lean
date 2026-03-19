import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_21a (H : AddSubgroup ℚ) (hH : H ≠ ⊤) : H.index = 0 := by
  classical
  by_contra h
  have hcard : Nat.card (ℚ ⧸ H) ≠ 0 := by
    simpa [Subgroup.index] using h
  haveI := Nat.card_ne_zero_iff.mp hcard
  letI : Fintype (ℚ ⧸ H) := Fintype.ofFinite (ℚ ⧸ H)
  have htop : H = ⊤ := by
    apply le_antisymm le_top
    intro q
    let n : ℕ := Fintype.card (ℚ ⧸ H)
    have hnpos : 0 < n := Fintype.card_pos_iff.mpr ⟨0⟩
    have hn : (n : ℚ) ≠ 0 := by
      exact_mod_cast hnpos.ne'
    have hdiv : ∃ r : ℚ, (n : ℚ) • r = q := by
      refine ⟨q / n, ?_⟩
      have hmul : (n : ℚ) * (q / n) = q := by
        field_simp [hn]
      simpa [nsmul_eq_mul] using hmul
    rcases hdiv with ⟨r, hr⟩
    have hz : n • (r + H) = 0 := by
      simpa [n] using (Fintype.card_nsmul_eq_zero (ℚ ⧸ H) (r + H))
    have hmem : n • r ∈ H := by
      simpa using hz
    simpa [hr] using hmem
  exact hH htop
