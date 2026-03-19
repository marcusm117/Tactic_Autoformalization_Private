import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := by
  classical
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  · right
    apply AddSubgroup.eq_top_iff'.2
    have hne : ∃ a : ℚ, a ∈ H ∧ a ≠ 0 := by
      by_contra h
      apply hbot
      ext y
      constructor
      · intro hy
        rw [AddSubgroup.mem_bot]
        by_cases hy0 : y = 0
        · exact hy0
        · exfalso
          exact h ⟨y, hy, hy0⟩
      · intro hy
        simpa [AddSubgroup.mem_bot] using hy
    rcases hne with ⟨a, ha, ha0⟩
    have hainv : (1 / a) ∈ H := hH (x := a) ⟨ha, ha0⟩
    have hnumden : (a.num : ℚ) / a.den = a := by
      simpa [Rat.divInt_eq_div] using Rat.num_den' a
    have hden0 : (a.den : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt a.pos)
    have hdenmul : (a.den : ℚ) * a = a.num := by
      rw [← hnumden]
      field_simp [hden0]
    have hnum_mem : (a.num : ℚ) ∈ H := by
      simpa [nsmul_eq_mul, hdenmul] using H.nsmul_mem a.den ha
    have hnum_mul_inv : (a.num : ℚ) * (1 / a) = a.den := by
      calc
        (a.num : ℚ) * (1 / a) = ((a.den : ℚ) * a) * (1 / a) := by rw [← hdenmul]
        _ = (a.den : ℚ) * (a * (1 / a)) := by ring
        _ = (a.den : ℚ) * 1 := by
          rw [div_eq_mul_inv, mul_inv_cancel₀ ha0, mul_one]
        _ = a.den := by ring
    have hden_mem : (a.den : ℚ) ∈ H := by
      simpa [zsmul_eq_mul, hnum_mul_inv] using H.zsmul_mem a.num hainv
    have hnumAbs_mem : ((a.num.natAbs : ℕ) : ℚ) ∈ H := by
      by_cases hnonneg : 0 ≤ a.num
      · have hEqInt : ((a.num.natAbs : ℕ) : ℤ) = a.num :=
          Int.ofNat_natAbs_of_nonneg hnonneg
        have hEq : ((a.num.natAbs : ℕ) : ℚ) = (a.num : ℚ) := by
          exact_mod_cast hEqInt
        simpa [hEq] using hnum_mem
      · have hneg : a.num < 0 := lt_of_not_ge hnonneg
        have hEqInt : ((a.num.natAbs : ℕ) : ℤ) = -a.num :=
          Int.ofNat_natAbs_of_neg hneg
        have hEq : ((a.num.natAbs : ℕ) : ℚ) = -(a.num : ℚ) := by
          exact_mod_cast hEqInt
        simpa [hEq] using H.neg_mem hnum_mem
    have hcop : IsCoprime (a.num.natAbs : ℤ) (a.den : ℤ) := by
      exact a.reduced.isCoprime
    rcases hcop with ⟨u, v, huv⟩
    have hu_mem : (u : ℚ) * ((a.num.natAbs : ℕ) : ℚ) ∈ H := by
      simpa [zsmul_eq_mul] using H.zsmul_mem u hnumAbs_mem
    have hv_mem : (v : ℚ) * (a.den : ℚ) ∈ H := by
      simpa [zsmul_eq_mul] using H.zsmul_mem v hden_mem
    have hone : (1 : ℚ) ∈ H := by
      have hsum :
          (u : ℚ) * ((a.num.natAbs : ℕ) : ℚ) + (v : ℚ) * (a.den : ℚ) ∈ H :=
        H.add_mem hu_mem hv_mem
      have hEq :
          (u : ℚ) * ((a.num.natAbs : ℕ) : ℚ) + (v : ℚ) * (a.den : ℚ) = 1 := by
        exact_mod_cast huv
      simpa [hEq] using hsum
    intro q
    by_cases hq0 : q = 0
    · simpa [hq0] using H.zero_mem
    · have hqden_mem : (q.den : ℚ) ∈ H := by
        simpa [zsmul_eq_mul] using H.zsmul_mem (q.den : ℤ) hone
      have hqden0 : (q.den : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt q.pos)
      have hqinv : (1 / (q.den : ℚ)) ∈ H := hH (x := (q.den : ℚ)) ⟨hqden_mem, hqden0⟩
      have hq_numden : (q.num : ℚ) / q.den = q := by
        simpa [Rat.divInt_eq_div] using Rat.num_den' q
      have hqEq : (q.num : ℚ) * (1 / (q.den : ℚ)) = q := by
        simpa [div_eq_mul_inv] using hq_numden
      simpa [zsmul_eq_mul, hqEq] using H.zsmul_mem q.num hqinv
