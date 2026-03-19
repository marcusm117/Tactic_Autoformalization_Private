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
    exact (Finset.mem_filter.mp hx).2.1.pos
  have haeq : a = 4 * (P - 1) + 3 := by
    dsimp [a]
    omega
  have ha4 : a % 4 = 3 := by
    rw [haeq]
    norm_num
  have ha1 : 1 < a := by
    rw [haeq]
    omega
  have hprime_factor :
      ∀ n, n % 4 = 3 → 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
    intro n
    refine Nat.strongInductionOn n ?_
    intro n ih hn4 hn1
    rcases Nat.exists_prime_and_dvd hn1 with ⟨q, hqprime, hqdiv⟩
    have hn2 : n % 2 = 1 := by
      have h : n % 2 = (n % 4) % 2 := by
        simpa using (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4))
      simpa [hn4] using h
    have hqmod2 : q % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
      · exfalso
        have h2q : 2 ∣ q := Nat.mod_eq_zero_iff_dvd.mp hq0
        have h2n : 2 ∣ n := dvd_trans h2q hqdiv
        have hn2z : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2n
        omega
      · exact hq1
    have hqmod2' : (q % 4) % 2 = 1 := by
      simpa [hqmod2] using (Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4))
    interval_cases hq4 : q % 4
    · simp [hq4] at hqmod2'
    ·
      have hq1 : q ≡ 1 [MOD 4] := by
        simpa [Nat.ModEq, hq4]
      rcases hqdiv with ⟨k, hk⟩
      have hkpos : 0 < k := by
        omega
      have hklt : k < n := by
        rw [hk]
        omega
      have hkmod : k % 4 = 3 := by
        have hnk : n ≡ k [MOD 4] := by
          rw [hk]
          simpa using (hq1.mul (Nat.ModEq.refl k))
        have hn3 : n ≡ 3 [MOD 4] := by
          simpa [Nat.ModEq] using hn4
        have hk3 : k ≡ 3 [MOD 4] := hnk.symm.trans hn3
        simpa [Nat.ModEq] using hk3
      have hkgt1 : 1 < k := by
        by_contra hk1
        have hkle1 : k ≤ 1 := le_of_not_gt hk1
        have hklt4 : k < 4 := by omega
        rw [Nat.mod_eq_of_lt hklt4] at hkmod
        omega
      rcases ih k hklt hkmod hkgt1 with ⟨p, hpprime, hpdvd, hpmod4⟩
      exact ⟨p, hpprime, dvd_trans hpdvd hqdiv, hpmod4⟩
    · simp [hq4] at hqmod2'
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
      exact Finset.dvd_prod_of_mem hp_mem
    have hpdiv4P : p ∣ 4 * P := dvd_mul_of_dvd_right hpdivP 4
    have h4P : 4 * P = a + 1 := by
      dsimp [a]
      omega
    have hpdiv1 : p ∣ 1 := by
      have hsub : p ∣ (a + 1) - a := Nat.dvd_sub hpdiv4P hpdiva (by omega)
      simpa [h4P] using hsub
    have hple1 : p ≤ 1 := Nat.le_of_dvd (by decide) hpdiv1
    have hpge2 : 2 ≤ p := hpprime.two_le
    omega
  have hpcong : p + 1 ≡ 0 [MOD 4] := by
    dsimp [Nat.ModEq]
    rw [Nat.add_mod_right_left, hpmod4]
    norm_num
  exact ⟨p, le_of_lt hpgtN, hpprime, hpcong⟩
