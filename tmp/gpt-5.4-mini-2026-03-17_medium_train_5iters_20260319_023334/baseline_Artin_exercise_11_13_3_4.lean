import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_13_3 (N : ℕ):
  ∃ p ≥ N, Nat.Prime p ∧ p + 1 ≡ 0 [MOD 4] := by
  classical
  by_cases hN : N ≤ 3
  · refine ⟨3, ?_, by decide, ?_⟩
    · omega
    · norm_num [Nat.ModEq]
  · have hN4 : 4 ≤ N := by omega
    let s : Finset ℕ := (Finset.range (N + 1)).filter (fun x => Nat.Prime x ∧ x % 4 = 3 ∧ x ≠ 3)
    let P : ℕ := s.prod id
    let a : ℕ := 4 * P + 3
    have hPpos : 0 < P := by
      dsimp [P, s]
      refine Finset.prod_pos ?_
      intro x hx
      exact Nat.Prime.pos (Finset.mem_filter.mp hx).2.1
    have ha4 : a % 4 = 3 := by
      dsimp [a]
      norm_num
    have ha1 : 1 < a := by
      dsimp [a]
      omega
    have h3prime : Nat.Prime 3 := by decide
    have hdiv3_of_mem : ∀ x ∈ s, ¬ 3 ∣ x := by
      intro x hx hdiv
      have hxprime : Nat.Prime x := (Finset.mem_filter.mp hx).2.1
      have hxmod4 : x % 4 = 3 := (Finset.mem_filter.mp hx).2.2.1
      have hxne3 : x ≠ 3 := (Finset.mem_filter.mp hx).2.2.2
      have hxle3 : x ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hdiv
      have hxge2 : 2 ≤ x := hxprime.two_le
      have hx23 : x = 2 ∨ x = 3 := by omega
      rcases hx23 with rfl | rfl
      · norm_num at hxmod4
      · exact hxne3 rfl
    have hP3 : ¬ 3 ∣ P := by
      dsimp [P, s]
      refine Finset.induction_on (Finset.range (N + 1)).filter (fun x => Nat.Prime x ∧ x % 4 = 3 ∧ x ≠ 3) ?_ ?_
      · intro _
        simp
      · intro x s hx ih hs
        have hxnd : ¬ 3 ∣ x := by
          exact hdiv3_of_mem x (by
            dsimp [s]
            simp [hx, hN4])
        have hs' : ∀ y ∈ s, ¬ 3 ∣ y := by
          intro y hy
          exact hs y (by
            dsimp [s]
            simp [hy, hx])
        have hrest : ¬ 3 ∣ s.prod id := ih hs'
        intro hdiv
        have hmul : 3 ∣ x * s.prod id := by
          simpa [Finset.prod_insert hx, mul_comm, mul_left_comm, mul_assoc] using hdiv
        rcases h3prime.dvd_mul.mp hmul with hleft | hright
        · exact hxnd hleft
        · exact hrest hright
    have ha3 : ¬ 3 ∣ a := by
      intro hdiv
      have h4P : 3 ∣ 4 * P := by
        have hsub : 3 ∣ a - 3 := Nat.dvd_sub hdiv (by decide : 3 ∣ 3) (by omega)
        simpa [a] using hsub
      rcases h3prime.dvd_mul.mp h4P with h4 | hP
      · norm_num at h4
      · exact hP3 hP
    have hprime_factor : ∀ n, n % 4 = 3 → 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih hn4 hn1
      rcases Nat.exists_prime_and_dvd (ne_of_gt hn1) with ⟨q, hqprime, hqdiv⟩
      have hq2orodd : q = 2 ∨ q % 2 = 1 := hqprime.eq_two_or_odd
      rcases hq2orodd with rfl | hqmod2
      · exfalso
        have : 2 ∣ n := dvd_trans (by decide : 2 ∣ (2 : ℕ)) hqdiv
        have hn2 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd this
        have hn2' : n % 2 = 1 := by
          have hmod := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)
          simpa [hn4] using hmod
        omega
      · have hq4lt : q % 4 < 4 := Nat.mod_lt _ (by decide)
        interval_cases hq4 : q % 4
        · have hqmod2' : q % 2 = 0 := by
            have h := Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4)
            simpa [hq4] using h
          omega
        ·
          rcases hqdiv with ⟨k, hk⟩
          have hkpos : 0 < k := by
            by_contra hk0
            have hk0' : k = 0 := by omega
            simp [hk0'] at hk
          have hklt : k < n := by
            omega
          have hkne0 : k ≠ 0 := by
            intro hk0
            simp [hk0] at hk
          have hkne1 : k ≠ 1 := by
            intro hk1
            simp [hk1] at hk
          have hkgt1 : 1 < k := by omega
          have hkmod4 : k % 4 = 3 := by
            have hnq : (q * k) % 4 = 3 := by simpa [hk] using hn4
            have hcalc : (q * k) % 4 = k % 4 := by
              rw [Nat.mul_mod, hq4]
              norm_num
            simpa [hcalc] using hnq
          rcases ih k hklt hkmod4 hkgt1 with ⟨p, hpprime, hpdvd, hpmod4⟩
          have hkdivn : k ∣ n := by
            refine ⟨q, ?_⟩
            simpa [mul_comm] using hk.symm
          exact ⟨p, hpprime, dvd_trans hpdvd hkdivn, hpmod4⟩
        · have hqmod2' : q % 2 = 0 := by
            have h := Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4)
            simpa [hq4] using h
          omega
        · exact ⟨q, hqprime, hqdiv, by simpa [hq4] using rfl⟩
    rcases hprime_factor a ha4 ha1 with ⟨p, hpprime, hpdiva, hpmod4⟩
    have hpgtN : N < p := by
      by_contra hle
      have hp_le : p ≤ N := le_of_not_gt hle
      have hp_range : p ∈ Finset.range (N + 1) := by
        simpa [Nat.lt_succ_iff] using hp_le
      have hp_mem : p ∈ s := by
        dsimp [s]
        simp [hpprime, hpmod4, hp_range, ha3]
      have hpdivP : p ∣ P := by
        dsimp [P]
        exact Finset.dvd_prod_of_mem hp_mem
      have hpdiv4P : p ∣ 4 * P := dvd_mul_of_dvd_right hpdivP 4
      have hpdiv3 : p ∣ 3 := by
        have hsub : p ∣ a - 4 * P := Nat.dvd_sub hpdiva hpdiv4P (by omega)
        simpa [a] using hsub
      have hp_le3 : p ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hpdiv3
      have hpge2 : 2 ≤ p := hpprime.two_le
      have hp23 : p = 2 ∨ p = 3 := by omega
      rcases hp23 with rfl | rfl
      · norm_num at hpmod4
      · exact (Finset.mem_filter.mp hp_mem).2.2.2 rfl
    have hpcong : p + 1 ≡ 0 [MOD 4] := by
      have hp3 : p ≡ 3 [MOD 4] := by
        simpa [Nat.ModEq] using hpmod4
      simpa using hp3.add (by simp)
    exact ⟨p, le_of_lt hpgtN, hpprime, hpcong⟩
