import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2d {p : ℕ} (hp : p.Prime ∧ p > 2)
  {f : Polynomial ℤ} (hf : f = (X + 2)^p):
  Irreducible (∑ n ∈ (f.support \ {0}), (f.coeff n : Polynomial ℤ) * X ^ (n-1) :
  Polynomial ℤ) := by
  classical
  let q : Polynomial ℤ :=
    ∑ m ∈ (f.support \ {0}), (f.coeff m : Polynomial ℤ) * X ^ (m - 1)
  have hqcoeff₁ : ∀ n, q.coeff n = f.coeff (n + 1) := by
    intro n
    unfold q
    rw [Polynomial.coeff_sum]
    by_cases hs : n + 1 ∈ f.support
    · have hs' : n + 1 ∈ f.support \ {0} := by
        simp [hs, Nat.succ_ne_zero]
      rw [Finset.sum_eq_single_of_mem (n + 1) hs']
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro m hm hneq
        have hmn : m - 1 ≠ n := by
          intro h
          apply hneq
          omega
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmn]
    · have hzero : f.coeff (n + 1) = 0 := by
        rwa [Polynomial.not_mem_support_iff] at hs
      rw [Finset.sum_eq_zero]
      · simpa [hzero]
      · intro m hm
        have hm_support : m ∈ f.support := by
          simp at hm
          exact hm.1
        have hmn : m - 1 ≠ n := by
          intro h
          apply hs
          have : m = n + 1 := by
            omega
          simpa [this] using hm_support
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmn]
  have hqcoeff : ∀ n, q.coeff n = ((Nat.choose p (n + 1) : ℤ) * 2 ^ (p - (n + 1))) := by
    intro n
    rw [hqcoeff₁ n, hf, add_pow, Polynomial.coeff_sum]
    by_cases hs : n + 1 ∈ Finset.range (p + 1)
    · rw [Finset.sum_eq_single_of_mem (n + 1) hs]
      · simp [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro m hm hneq
        simp [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hneq]
    · rw [Finset.sum_eq_zero]
      · have hlt : p < n + 1 := by
          simp [Finset.mem_range] at hs
          omega
        simp [Nat.choose_eq_zero_of_lt hlt]
      · intro m hm
        have hneq : m ≠ n + 1 := by
          intro h
          apply hs
          simpa [Finset.mem_range, h] using hm
        simp [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hneq]
  have hdeg : q.natDegree ≤ p - 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 ?_
    intro n hn
    rw [hqcoeff n]
    have hlt : p < n + 1 := by
      omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  have htop : q.coeff (p - 1) = 1 := by
    have hp0 : 0 < p := hp.1.pos
    rw [hqcoeff (p - 1), Nat.sub_add_cancel hp0, Nat.choose_self, Nat.sub_self]
    norm_num
  have hm : q.Monic := by
    exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one hdeg htop
  have hpz : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp.1
  have hdiv : ∀ n < q.natDegree, (p : ℤ) ∣ q.coeff n := by
    intro n hn
    rw [hqcoeff n]
    have hklt : n + 1 < p := by
      omega
    have hchoose : p ∣ Nat.choose p (n + 1) := by
      exact hp.1.dvd_choose_self (Nat.succ_pos n) hklt
    exact dvd_mul_of_dvd_left (by exact_mod_cast hchoose) _
  have hnsq : ¬ (p : ℤ) ^ 2 ∣ q.coeff 0 := by
    intro hsq
    rw [hqcoeff 0, Nat.choose_one_right] at hsq
    have hsq_nat : p ^ 2 ∣ p * 2 ^ (p - 1) := by
      exact_mod_cast hsq
    have h2pow : p ∣ 2 ^ (p - 1) := by
      rw [pow_two, Nat.mul_dvd_mul_iff_left hp.1.pos] at hsq_nat
      exact hsq_nat
    have h2 : p ∣ 2 := hp.1.dvd_of_dvd_pow h2pow
    have hle : p ≤ 2 := hp.1.le_of_dvd (by decide : 0 < 2) h2
    omega
  have hirr : Irreducible q := by
    exact hm.irreducible_of_eisenstein_criterion hpz hdiv hnsq
  simpa [q] using hirr
