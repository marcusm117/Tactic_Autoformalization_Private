import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2d {p : ℕ} (hp : p.Prime ∧ p > 2)
  {f : Polynomial ℤ} (hf : f = (X + 2)^p):
  Irreducible (∑ n ∈ (f.support \ {0}), (f.coeff n : Polynomial ℤ) * X ^ (n-1) :
  Polynomial ℤ) := by
  classical
  let q : Polynomial ℤ :=
    ∑ n ∈ (f.support \ {0}), (f.coeff n : Polynomial ℤ) * X ^ (n - 1)
  have hqcoeff₁ : ∀ n, q.coeff n = f.coeff (n + 1) := by
    intro n
    dsimp [q]
    simp only [Polynomial.coeff_sum]
    by_cases hs : n + 1 ∈ f.support
    · have hs' : n + 1 ∈ f.support \ {0} := by
        simp [hs, Nat.succ_ne_zero]
      rw [Finset.sum_eq_single_of_mem (n + 1) hs']
      · simpa [Polynomial.coeff_C_mul]
      · intro m hm hmn
        have hm0 : m ≠ 0 := by
          simp at hm
          exact hm.2
        have hne : n ≠ m - 1 := by
          omega
        simp [Polynomial.coeff_C_mul, hne]
    · have hzero : f.coeff (n + 1) = 0 := by
        by_contra hne
        apply hs
        exact Polynomial.mem_support_iff.mpr hne
      rw [hzero, Finset.sum_eq_zero]
      · rfl
      · intro m hm
        have hm_support : m ∈ f.support := by
          simp at hm
          exact hm.1
        have hne : n ≠ m - 1 := by
          intro h
          apply hs
          have : m = n + 1 := by omega
          simpa [this] using hm_support
        simp [Polynomial.coeff_C_mul, hne]
  have hqcoeff : ∀ n, q.coeff n = ((Nat.choose p (n + 1) : ℤ) * 2 ^ (p - (n + 1))) := by
    intro n
    rw [hqcoeff₁ n, hf]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Polynomial.coeff_X_add_C_pow (n := p) (r := (2 : ℤ)) (k := n + 1))
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
    exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one (n := p - 1) hdeg htop
  have hpz : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp.1
  have hdiv : ∀ n < q.natDegree, (p : ℤ) ∣ q.coeff n := by
    intro n hn
    rw [hqcoeff n]
    have hklt : n + 1 < p := by
      omega
    have hchoose : p ∣ Nat.choose p (n + 1) := by
      exact hp.1.dvd_choose_self (Nat.succ_ne_zero n) hklt
    exact dvd_mul_of_dvd_left (by exact_mod_cast hchoose) _
  have hnsq : ¬ (p : ℤ) ^ 2 ∣ q.coeff 0 := by
    intro hsq
    rw [hqcoeff 0, Nat.choose_one_right] at hsq
    have hsq_nat : p ^ 2 ∣ p * 2 ^ (p - 1) := by
      exact_mod_cast hsq
    rcases hsq_nat with ⟨k, hk⟩
    have hk' : 2 ^ (p - 1) = p * k := by
      apply Nat.eq_of_mul_eq_mul_left hp.1.pos
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hk
    have h2pow : p ∣ 2 ^ (p - 1) := ⟨k, hk'.symm⟩
    have h2 : p ∣ 2 := hp.1.dvd_of_dvd_pow h2pow
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h2
    omega
  have hirr : Irreducible q := by
    exact Polynomial.irreducible_of_eisenstein_criterion hm hpz hdiv hnsq
  simpa [q] using hirr
