import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_21a (H : AddSubgroup ℚ) (hH : H ≠ ⊤) : H.index = 0 := by
  classical
  by_contra h
  have hcard : Nat.card (ℚ ⧸ H) ≠ 0 := by
    simpa [Subgroup.index] using h
  haveI : Fintype (ℚ ⧸ H) := Nat.fintypeOfCardPos (Nat.pos_of_ne_zero hcard)
  let n : ℕ := Fintype.card (ℚ ⧸ H)
  have hnpos : 0 < n := Fintype.card_pos_iff.mpr ⟨0⟩
  have hn : (n : ℚ) ≠ 0 := by
    exact_mod_cast hnpos.ne'
  have htop : H = ⊤ := by
    apply le_antisymm le_top
    intro q
    have hq : n • (q / n) = q := by
      rw [nsmul_eq_mul]
      field_simp [hn]
    have hz : n • ((q / n) + H) = 0 := by
      simpa [n] using (Fintype.card_nsmul_eq_zero (ℚ ⧸ H) ((q / n) + H))
    have hmem : n • (q / n) ∈ H := by
      simpa using hz
    simpa [hq] using hmem
  exact hH htop
