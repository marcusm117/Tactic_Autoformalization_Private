import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_13_3 (N : ℕ):
  ∃ p ≥ N, Nat.Prime p ∧ p + 1 ≡ 0 [MOD 4] := by
  classical
  let s : Finset ℕ := (Finset.range (N + 1)).filter (fun x => Nat.Prime x ∧ x % 4 = 3)
  let P : ℕ := s.prod (fun x => x)
  let a : ℕ := 4 * P - 1
  have hPpos : 0 < P := by
    dsimp [P, s]
    refine Finset.prod_pos ?_
    intro x hx
    exact (Nat.Prime.pos (Finset.mem_filter.mp hx).2.1)
  have haeq : a = 4 * (P - 1) + 3 := by
    dsimp [a]
    omega
  have ha4 : a % 4 = 3 := by
    rw [haeq]
    norm_num
  have ha1 : 1 < a := by
    rw [haeq]
    omega
  have hprime_factor : ∀ n, n % 4 = 3 → 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn4 hn1
    rcases Nat.exists_prime_and_dvd hn1 with ⟨q, hqprime, hqdiv⟩
    rcases hqdiv with ⟨k, hk⟩
    have hn2 : n % 2 = 1 := by
      have hmod := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)
      simpa [hn4] using hmod
    have hq2 : q % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
      · exfalso
        have h2q : 2 ∣ q := Nat.mod_eq_zero_iff_dvd.mp hq0
        have h2n : 2 ∣ n := dvd_trans h2q hqdiv
        have hn2' : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2n
        omega
      · exact hq1
    interval_cases hq4 : q % 4
    · have hq2' : q % 2 = 0 := by
        have hmod := Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4)
        simpa [hq4] using hmod
      omega
    ·
      have hq1 : q ≡ 1 [MOD 4] := by
        simpa [Nat.ModEq, hq4]
      have hkgt1 : 1 < k := by
        by_contra hknot
        have hk_eq1 : k = 1 := by omega
        have hnq : n = q := by simpa [hk_eq1] using hk
        have hq3 : q % 4 = 3 := by simpa [hnq] using hn4
        have hq1' : q % 4 = 1 := hq4
        omega
      have hklt : k < n := by
        rw [hk]
        omega
      have hkmod4 : k % 4 = 3 := by
        have hnk : n ≡ k [MOD 4] := by
          rw [hk]
          simpa using hq1.mul (Nat.ModEq.refl k)
        have hn3 : n ≡ 3 [MOD 4] := by
          simpa [Nat.ModEq] using hn4
        have hk3 : k ≡ 3 [MOD 4] := hnk.symm.trans hn3
        simpa [Nat.ModEq] using hk3
      rcases ih k hklt hkmod4 hkgt1 with ⟨p, hpprime, hpdvd, hpmod4⟩
      exact ⟨p, hpprime, dvd_trans hpdvd hqdiv, hpmod4⟩
    · have hq2' : q % 2 = 0 := by
        have hmod := Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4)
        simpa [hq4] using hmod
      omega
    ·
      exact ⟨q, hqprime, hqdiv, by simpa [Nat.ModEq, hq4]⟩
  rcases hprime_factor a ha4 ha1 with ⟨p, hpprime, hpdiva, hpmod4⟩
  have hpgtN : N < p := by
    by_contra hle
    have hp_le : p ≤ N := le_of_not_gt hle
    have hp_mem : p ∈ s := by
      dsimp [s]
      simp [hpprime, hpmod4, hp_le]
    have hpdivP : p ∣ P := by
      dsimp [P]
      simpa using (Finset.dvd_prod_of_mem (s := s) (f := fun x => x) hp_mem)
    have hpdiv4P : p ∣ 4 * P := dvd_mul_of_dvd_right hpdivP 4
    have hpdiv1 : p ∣ 1 := by
      have hsub : p ∣ 4 * P - a := Nat.dvd_sub hpdiv4P hpdiva
      have hsub1 : 4 * P - a = 1 := by
        dsimp [a]
        omega
      simpa [hsub1] using hsub
    have hp_le1 : p ≤ 1 := Nat.le_of_dvd (by decide) hpdiv1
    have hp_ge2 : 2 ≤ p := hpprime.two_le
    omega
  have hpcong : p + 1 ≡ 0 [MOD 4] := by
    have hp3 : p ≡ 3 [MOD 4] := by
      simpa [Nat.ModEq] using hpmod4
    have hsum : p + 1 ≡ 3 + 1 [MOD 4] := hp3.add (by simp)
    simpa using hsum
  exact ⟨p, le_of_lt hpgtN, hpprime, hpcong⟩
