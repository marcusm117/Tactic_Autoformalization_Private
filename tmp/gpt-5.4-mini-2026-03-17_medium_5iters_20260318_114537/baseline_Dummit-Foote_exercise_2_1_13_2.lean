import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := by
  classical
  by_cases hbot : H = ⊥
  · left
    exact hbot
  · right
    have hnonzero : ∃ x ∈ H, x ≠ 0 := by
      by_contra h
      push_neg at h
      have hbot' : H = ⊥ := by
        ext y
        constructor
        · intro hy
          exact h y hy
        · intro hy
          simpa using hy
      exact hbot hbot'
    rcases hnonzero with ⟨x, hx, hx0⟩
    have hq : ((x.num : ℚ) / x.den) = x := Rat.num_div_den x
    have hdenq : (x.den : ℚ) ≠ 0 := by
      exact_mod_cast (Rat.den_pos x).ne'
    have hnumne : (x.num : ℚ) ≠ 0 := by
      intro h0
      have h0' : x.num = 0 := by exact_mod_cast h0
      exact hx0 (Rat.num_eq_zero.mp h0')
    have hnum_eq : (x.den : ℚ) * x = x.num := by
      rw [← hq]
      field_simp [hdenq]
      ring
    have hnum : (x.num : ℚ) ∈ H := by
      have hmul : ((x.den : ℚ) * x) ∈ H := by
        simpa [nsmul_eq_mul] using (H.nsmul_mem hx x.den)
      simpa [hnum_eq] using hmul
    have hden_eq : (x.num : ℚ) * (1 / x) = x.den := by
      rw [← hq]
      field_simp [hnumne, hdenq]
      ring
    have h1x : (1 / x) ∈ H := hH ⟨hx, hx0⟩
    have hden : (x.den : ℚ) ∈ H := by
      have hmul : ((x.num : ℚ) * (1 / x)) ∈ H := by
        simpa [zsmul_eq_mul] using (H.zsmul_mem h1x x.num)
      simpa [hden_eq] using hmul
    have hnatabs : ((Int.natAbs x.num : ℕ) : ℚ) ∈ H := by
      by_cases hneg : x.num < 0
      · have hnegmem : (-(x.num : ℚ)) ∈ H := H.neg_mem hnum
        simpa [Int.natAbs_of_neg hneg] using hnegmem
      · have hnonneg : 0 ≤ x.num := le_of_not_gt hneg
        simpa [Int.natAbs_of_nonneg hnonneg] using hnum
    have hcop : Nat.Coprime (Int.natAbs x.num) x.den := Rat.num_den_coprime x
    rcases hcop.exists_bezout with ⟨u, v, huv⟩
    have hlin : ((u : ℚ) * ((Int.natAbs x.num : ℕ) : ℚ) + (v : ℚ) * (x.den : ℚ)) ∈ H := by
      simpa [zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        (H.add_mem (H.zsmul_mem hnatabs u) (H.zsmul_mem hden v))
    have hlinEq : ((u : ℚ) * ((Int.natAbs x.num : ℕ) : ℚ) + (v : ℚ) * (x.den : ℚ)) = 1 := by
      exact_mod_cast huv
    have h1 : (1 : ℚ) ∈ H := by
      simpa [hlinEq] using hlin
    have htop : H = ⊤ := by
      ext y
      constructor
      · intro hy
        simp
      · intro hy
        have hInt : ∀ z : ℤ, (z : ℚ) ∈ H := by
          intro z
          simpa using H.zsmul_mem h1 z
        have hdeny : (y.den : ℚ) ∈ H := by
          simpa using hInt (y.den : ℤ)
        have h1den : (1 / (y.den : ℚ)) ∈ H := hH ⟨hdeny, by exact_mod_cast (Rat.den_pos y).ne'⟩
        have hy' : (y.num : ℚ) • (1 / (y.den : ℚ)) ∈ H := H.zsmul_mem h1den y.num
        have hy'' : (y.num : ℚ) / y.den ∈ H := by
          simpa [zsmul_eq_mul] using hy'
        have hyEq : (y.num : ℚ) / y.den = y := Rat.num_div_den y
        simpa [hyEq] using hy''
    exact htop
