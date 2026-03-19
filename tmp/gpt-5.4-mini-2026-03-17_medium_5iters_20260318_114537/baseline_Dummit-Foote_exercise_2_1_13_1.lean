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
          simpa [h y hy]
        · intro hy
          simp at hy
          rw [hy]
          simp
      exact hbot hbot'
    rcases hnonzero with ⟨x, hx, hx0⟩
    have hq : x = (x.num : ℚ) / x.den := by
      simpa using (Rat.num_div_den x)
    have hdenq : (x.den : ℚ) ≠ 0 := by
      exact_mod_cast (Rat.den_pos x).ne'
    have hnumne : (x.num : ℚ) ≠ 0 := by
      intro h0
      have h0' : x.num = 0 := by exact_mod_cast h0
      exact hx0 (Rat.num_eq_zero.mp h0')
    have hnum_eq : (x.den : ℚ) * x = x.num := by
      rw [hq]
      field_simp [hdenq]
      ring
    have hnum : (x.num : ℚ) ∈ H := by
      have hmul : ((x.den : ℚ) * x) ∈ H := by
        simpa [nsmul_eq_mul] using (H.nsmul_mem hx x.den)
      simpa [hnum_eq] using hmul
    have hden_eq : (x.num : ℚ) * (1 / x) = x.den := by
      rw [hq]
      field_simp [hnumne, hdenq]
      ring
    have h1x : (1 / x) ∈ H := hH ⟨hx, hx0⟩
    have hden : (x.den : ℚ) ∈ H := by
      have hmul : ((x.num : ℚ) * (1 / x)) ∈ H := by
        simpa [zsmul_eq_mul] using (H.zsmul_mem h1x x.num)
      simpa [hden_eq] using hmul
    have hcop : Int.Coprime x.num x.den := Rat.num_den_coprime x
    rcases hcop.exists_bezout with ⟨u, v, huv⟩
    have hlin : ((u : ℚ) * (x.num : ℚ) + (v : ℚ) * (x.den : ℚ)) ∈ H := by
      simpa [zsmul_eq_mul] using (H.add_mem (H.zsmul_mem hnum u) (H.zsmul_mem hden v))
    have hlinEq : ((u : ℚ) * (x.num : ℚ) + (v : ℚ) * (x.den : ℚ)) = 1 := by
      exact_mod_cast huv
    have h1 : (1 : ℚ) ∈ H := by
      simpa [hlinEq] using hlin
    have htop : H = ⊤ := by
      ext y
      constructor
      · intro hy
        trivial
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
        have hyEq : (y : ℚ) = (y.num : ℚ) / y.den := by
          simpa using (Rat.num_div_den y)
        simpa [hyEq] using hy''
    exact htop
