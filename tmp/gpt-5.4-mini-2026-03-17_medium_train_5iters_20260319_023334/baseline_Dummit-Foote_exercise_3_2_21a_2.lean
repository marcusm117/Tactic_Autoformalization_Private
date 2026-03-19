import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_21a (H : AddSubgroup ℚ) (hH : H ≠ ⊤) : H.index = 0 := by
  classical
  by_contra h
  have hcard : Nat.card (ℚ ⧸ H) ≠ 0 := by
    simpa [Subgroup.index] using h
  have hnotinf : ¬ Infinite (ℚ ⧸ H) := by
    intro hInf
    have hzero : Nat.card (ℚ ⧸ H) = 0 := by
      simpa using (Nat.card_eq_zero (α := ℚ ⧸ H))
    exact hcard hzero
  haveI : Finite (ℚ ⧸ H) := finite_of_not_infinite hnotinf
  let n : ℕ := Fintype.card (ℚ ⧸ H)
  have hnpos : 0 < n := Fintype.card_pos_iff.mpr ⟨0⟩
  have hzero : ∀ x : ℚ ⧸ H, n • x = 0 := by
    intro x
    have hdiv : addOrderOf x ∣ n := by
      simpa [n] using (addOrderOf_dvd_card_univ x)
    simpa using (nsmul_eq_zero_of_addOrderOf_dvd hdiv)
  have hsub : Subsingleton (ℚ ⧸ H) := by
    refine ⟨?_⟩
    intro x y
    have hx : x = 0 := by
      obtain ⟨z, hz⟩ := divisible x n
      rw [← hz]
      exact hzero z
    have hy : y = 0 := by
      obtain ⟨z, hz⟩ := divisible y n
      rw [← hz]
      exact hzero z
    simp [hx, hy]
  have htop : H = ⊤ := by
    ext q
    have hq : ((q : ℚ ⧸ H)) = 0 := Subsingleton.elim _ _
    simpa using (QuotientAddGroup.eq_zero_iff.mp hq)
  exact hH htop
