import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_21a (H : AddSubgroup ℚ) (hH : H ≠ ⊤) : H.index = 0 := by
  classical
  by_contra hne
  have hcard : Nat.card (ℚ ⧸ H) ≠ 0 := by
    simpa [Subgroup.index] using hne
  have hnotinf : ¬ Infinite (ℚ ⧸ H) := by
    intro hInf
    have h0 : Nat.card (ℚ ⧸ H) = 0 := Nat.card_eq_zero (α := ℚ ⧸ H)
    exact hcard h0
  letI : Fintype (ℚ ⧸ H) := Fintype.ofNotInfinite
  let n : ℕ := Fintype.card (ℚ ⧸ H)
  have hnpos : 0 < n := by
    simpa [n] using Fintype.card_pos_iff.mpr ⟨0⟩
  have hn : (n : ℚ) ≠ 0 := by
    exact_mod_cast hnpos.ne'
  have htop : H = ⊤ := by
    apply le_antisymm le_top
    intro q
    have hz : (n : ℤ) • ((q / n : ℚ) : ℚ ⧸ H) = 0 := by
      simpa [n] using (Fintype.card_zsmul_eq_zero (ℚ ⧸ H) ((q / n : ℚ) : ℚ ⧸ H))
    have hqrat : (n : ℚ) * (q / n) = q := by
      field_simp [hn]
    have hq : (n : ℤ) • ((q / n : ℚ) : ℚ ⧸ H) = (q : ℚ ⧸ H) := by
      simp [hqrat, n]
    have hq0 : (q : ℚ ⧸ H) = 0 := by
      simpa [hq] using hz
    simpa using hq0
  exact hH htop
