import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  classical
  have hcyc : IsCyclic G := ⟨x, by simpa [hG]⟩
  letI : IsCyclic G := hcyc
  have hnotTopPow : ∀ {m : ℕ}, Nat.Prime m → m ∣ (n : ℕ) →
      Subgroup.closure ({x ^ m} : Set G) ≠ ⊤ := by
    intro m hm hmn htop
    have hxmem : x ∈ Subgroup.closure ({x ^ m} : Set G) := by
      simpa [htop]
    have hdiv : orderOf x ∣ orderOf (x ^ m) := by
      exact orderOf_dvd_of_mem hxmem
    have hpow : orderOf (x ^ m) = (n : ℕ) / m := by
      simpa [hx, hmn, Nat.gcd_eq_left hmn] using (orderOf_pow x m)
    have hlt : orderOf (x ^ m) < orderOf x := by
      rw [hx, hpow]
      exact Nat.div_lt_self n.2 hm.one_lt
    exact (Nat.not_dvd_of_gt hlt) hdiv
  constructor
  · rintro ⟨p, hp, hpn, rfl⟩
    constructor
    · intro htop
      exact hnotTopPow (m := p) hp hpn htop
    · intro K hHK
      rcases (Subgroup.exists_eq_closure_pow (x := x) (H := K) hx hG) with ⟨q, hq, rfl⟩
      have hxq : x ^ p ∈ Subgroup.closure ({x ^ q} : Set G) := by
        exact hHK (by
          simpa [H] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G))))
      have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ q) := by
        exact orderOf_dvd_of_mem hxq
      have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
      have hpowq : orderOf (x ^ q) = (n : ℕ) / q := by
        simpa [hx, hq, Nat.gcd_eq_left hq] using (orderOf_pow x q)
      have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / q := by
        simpa [hpowp, hpowq] using hdiv
      have hqp : q ∣ p := by
        rcases hdiv' with ⟨t, ht⟩
        have hmpos : 0 < (n : ℕ) / p := Nat.div_pos n.2 hp.pos
        have hmne : (n : ℕ) / p ≠ 0 := Nat.ne_of_gt hmpos
        have hEq : (q * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
          calc
            (q * t) * ((n : ℕ) / p) = q * (((n : ℕ) / p) * t) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
            _ = q * ((n : ℕ) / q) := by rw [ht]
            _ = n := by rw [Nat.mul_div_cancel' hq]
            _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
        have hqtp : q * t = p := Nat.mul_right_cancel hEq hmne
        exact ⟨t, hqtp⟩
      rcases hp.eq_one_or_self_of_dvd hqp with hq1 | hqpEq
      · exact Or.inr (by simpa [hq1, hG])
      · exact Or.inl (by simpa [hqpEq])
  · intro hmax
    rcases hmax with ⟨hHtop, hmax⟩
    rcases (Subgroup.exists_eq_closure_pow (x := x) (H := H) hx hG) with ⟨k, hk, rfl⟩
    have hkne1 : k ≠ 1 := by
      intro hk1
      apply hHtop
      simpa [hk1, hG]
    have hkgt1 : 1 < k := by
      omega
    by_cases hkprime : Nat.Prime k
    · exact ⟨k, hkprime, hk, rfl⟩
    · rcases Nat.exists_prime_and_dvd hkgt1 with ⟨p, hp, hpk⟩
      have hpn : p ∣ (n : ℕ) := dvd_trans hpk hk
      let K : Subgroup G := Subgroup.closure ({x ^ p} : Set G)
      have hxk : x ^ k ∈ K := by
        rcases hpk with ⟨m, rfl⟩
        simp [pow_mul]
      have hHK : Subgroup.closure ({x ^ k} : Set G) ≤ K := by
        exact Subgroup.closure_le.2 (by
          intro y hy
          have hy' : y = x ^ k := by simpa using hy
          simpa [hy'] using hxk)
      cases hmax K hHK with
      | inl hKH =>
          have hxpH : x ^ p ∈ Subgroup.closure ({x ^ k} : Set G) := by
            simpa [hKH] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G)))
          have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ k) := by
            exact orderOf_dvd_of_mem hxpH
          have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
            simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
          have hpowk : orderOf (x ^ k) = (n : ℕ) / k := by
            simpa [hx, hk, Nat.gcd_eq_left hk] using (orderOf_pow x k)
          have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / k := by
            simpa [hpowp, hpowk] using hdiv
          have hkp : k ∣ p := by
            rcases hdiv' with ⟨t, ht⟩
            have hmpos : 0 < (n : ℕ) / p := Nat.div_pos n.2 hp.pos
            have hmne : (n : ℕ) / p ≠ 0 := Nat.ne_of_gt hmpos
            have hEq : (k * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
              calc
                (k * t) * ((n : ℕ) / p) = k * (((n : ℕ) / p) * t) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
                _ = k * ((n : ℕ) / k) := by rw [ht]
                _ = n := by rw [Nat.mul_div_cancel' hk]
                _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
            have hktp : k * t = p := Nat.mul_right_cancel hEq hmne
            exact ⟨t, hktp⟩
          have hk_eq : k = p := by
            rcases hp.eq_one_or_self_of_dvd hkp with hk1 | hk1
            · exact False.elim (hkne1 hk1)
            · exact hk1
          have hkprime' : Nat.Prime k := by simpa [hk_eq] using hp
          exact hkprime hkprime'
      | inr htop =>
          exact False.elim (hnotTopPow (m := p) hp hpn htop)
