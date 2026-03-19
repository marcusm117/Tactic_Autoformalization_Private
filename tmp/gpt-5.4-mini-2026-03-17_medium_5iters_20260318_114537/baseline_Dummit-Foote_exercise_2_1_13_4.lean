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
    have hnonzero : ∃ a ∈ H, a ≠ 0 := by
      by_contra h
      push_neg at h
      have hbot' : H = ⊥ := by
        ext y
        constructor
        · intro hy
          exact h y hy
        · intro hy
          simpa [hy] using (H.zero_mem)
      exact hbot hbot'
    rcases hnonzero with ⟨a, ha, ha0⟩
    have hq : a = (a.num : ℚ) / a.den := by
      simpa using (Rat.num_div_den a).symm
    have hdenq : (a.den : ℚ) ≠ 0 := by
      exact_mod_cast (Rat.den_pos a).ne'
    have hnumne : (a.num : ℚ) ≠ 0 := by
      intro h0
      have h0' : a.num = 0 := by exact_mod_cast h0
      exact ha0 (Rat.num_eq_zero.mp h0')
    have hnum_eq : (a.den : ℚ) * a = a.num := by
      calc
        (a.den : ℚ) * a = (a.den : ℚ) * ((a.num : ℚ) / a.den) := by rw [hq]
        _ = a.num := by
          field_simp [hdenq]
          ring
    have hnum : (a.num : ℚ) ∈ H := by
      have hmul : ((a.den : ℚ) * a) ∈ H := by
        simpa [nsmul_eq_mul] using (H.nsmul_mem ha a.den)
      simpa [hnum_eq] using hmul
    have hinv_eq : (1 / a) = (a.den : ℚ) / a.num := by
      calc
        (1 / a) = 1 / ((a.num : ℚ) / a.den) := by rw [hq]
        _ = (a.den : ℚ) / a.num := by
          field_simp [hnumne, hdenq]
          ring
    have hden_eq : (a.num : ℚ) * (1 / a) = a.den := by
      calc
        (a.num : ℚ) * (1 / a) = (a.num : ℚ) * ((a.den : ℚ) / a.num) := by rw [hinv_eq]
        _ = a.den := by
          field_simp [hnumne]
          ring
    have h1a : (1 / a) ∈ H := by
      exact hH ⟨ha, ha0⟩
    have hden : (a.den : ℚ) ∈ H := by
      have hmul : ((a.num : ℚ) * (1 / a)) ∈ H := by
        simpa [zsmul_eq_mul] using (H.zsmul_mem h1a a.num)
      simpa [hden_eq] using hmul
    have hcop : Nat.Coprime (Int.natAbs a.num) a.den := by
      simpa using a.num_coprime_den
    rcases hcop.exists_bezout with ⟨u, v, huv⟩
    have hlin : ((u : ℚ) * ((Int.natAbs a.num : ℕ) : ℚ) + (v : ℚ) * (a.den : ℚ)) ∈ H := by
      have h1' : ((u : ℚ) * ((Int.natAbs a.num : ℕ) : ℚ)) ∈ H := by
        simpa [zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          (H.zsmul_mem hnatabs u)
      have h2' : ((v : ℚ) * (a.den : ℚ)) ∈ H := by
        simpa [zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          (H.zsmul_mem hden v)
      exact H.add_mem h1' h2'
    have hlinEq : ((u : ℚ) * ((Int.natAbs a.num : ℕ) : ℚ) + (v : ℚ) * (a.den : ℚ)) = 1 := by
      exact_mod_cast huv
    have h1 : (1 : ℚ) ∈ H := by
      simpa [hlinEq] using hlin
    have hnatabs : ((Int.natAbs a.num : ℕ) : ℚ) ∈ H := by
      by_cases hnonneg : 0 ≤ a.num
      · simpa [Int.natAbs_of_nonneg hnonneg] using hnum
      · have hnegmem : (-(a.num : ℚ)) ∈ H := H.neg_mem hnum
        have hlt : a.num < 0 := lt_of_not_ge hnonneg
        simpa [Int.natAbs_of_neg hlt] using hnegmem
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
        have hyEq : (y.num : ℚ) / y.den = y := by
          simpa using (Rat.num_div_den y)
        simpa [hyEq] using hy''
    exact htop
