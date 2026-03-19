import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := by
  classical
  by_cases hzero : ∀ a ∈ H, a = 0
  · left
    ext y
    constructor
    · intro hy
      rw [hzero y hy]
      simp
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      rw [hy0]
      simp
  · right
    push_neg at hzero
    rcases hzero with ⟨x, hx, hx0⟩
    have hq : (x : ℚ) = (x.num : ℚ) / x.den := by
      simpa [eq_comm] using (Rat.num_div_den x)
    have hnum : (x.num : ℚ) ∈ H := by
      have h := H.nsmul_mem hx x.den
      rw [hq] at h
      simpa using h
    have hnatabs : ((Int.natAbs x.num : ℕ) : ℚ) ∈ H := by
      by_cases hnonneg : 0 ≤ x.num
      · simpa [Int.natAbs_of_nonneg hnonneg] using hnum
      · have hxle : x.num ≤ 0 := le_of_not_ge hnonneg
        have hneg : (-(x.num : ℚ)) ∈ H := H.neg_mem hnum
        simpa [Int.natAbs_of_nonpos hxle] using hneg
    have h1x : (1 / x) ∈ H := hH ⟨hx, hx0⟩
    have hnumne : (x.num : ℚ) ≠ 0 := by
      intro h0
      have hnum0 : x.num = 0 := by exact_mod_cast h0
      exact hx0 (Rat.num_eq_zero.mp hnum0)
    have hdenne : (x.den : ℚ) ≠ 0 := by
      exact_mod_cast (Rat.den_pos x).ne'
    have hEq : (x.num : ℚ) • (1 / x) = (x.den : ℚ) := by
      rw [hq]
      simp [zsmul_eq_mul]
      field_simp [hnumne, hdenne]
    have hden : (x.den : ℚ) ∈ H := by
      have h := H.zsmul_mem h1x x.num
      simpa [hEq] using h
    have hcop : Nat.Coprime (Int.natAbs x.num) x.den := Rat.coprime_num_den x
    rcases hcop.exists_bezout with ⟨u, v, huv⟩
    have hlin : ((u : ℚ) * ((Int.natAbs x.num : ℕ) : ℚ) + (v : ℚ) * (x.den : ℚ)) ∈ H := by
      simpa [zsmul_eq_mul] using
        (H.add_mem (H.zsmul_mem hnatabs u) (H.zsmul_mem hden v))
    have hcast : ((u : ℚ) * ((Int.natAbs x.num : ℕ) : ℚ) + (v : ℚ) * (x.den : ℚ)) = 1 := by
      exact_mod_cast huv
    have h1 : (1 : ℚ) ∈ H := by
      simpa [hcast] using hlin
    have htop : H = ⊤ := by
      ext y
      constructor
      · intro hy
        trivial
      · intro hy
        have hyEq : (y : ℚ) = (y.num : ℚ) / y.den := by
          simpa [eq_comm] using (Rat.num_div_den y)
        have hInt : ∀ z : ℤ, (z : ℚ) ∈ H := by
          intro z
          simpa using H.zsmul_mem h1 z
        have hdeny : (y.den : ℚ) ∈ H := hInt y.den
        have h1den : (1 / (y.den : ℚ)) ∈ H := hH ⟨hdeny, by exact_mod_cast (Rat.den_pos y).ne'⟩
        have hy' : (y.num : ℚ) • (1 / (y.den : ℚ)) ∈ H := H.zsmul_mem h1den y.num
        have hy'' : (y.num : ℚ) / y.den ∈ H := by
          simpa using hy'
        rw [hyEq]
        exact hy''
    exact htop
