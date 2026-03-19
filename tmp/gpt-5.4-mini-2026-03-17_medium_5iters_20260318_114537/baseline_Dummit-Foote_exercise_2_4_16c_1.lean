import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  classical
  have hcyc : IsCyclic G := by
    rw [hG]
    refine ⟨⟨x, by
      simpa using (Subgroup.subset_closure (by simp : x ∈ ({x} : Set G)))⟩, ?_⟩
    intro y
    have hy : y.1 ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := y.2
    rcases (Subgroup.mem_closure_singleton.mp hy) with ⟨z, hz⟩
    exact ⟨z, by simpa [hz]⟩
  haveI : IsCyclic G := hcyc
  constructor
  · rintro ⟨p, hp, hpn, rfl⟩
    constructor
    · intro htop
      have hxmem : x ∈ Subgroup.closure ({x ^ p} : Set G) := by
        simpa [htop]
      rcases (Subgroup.mem_closure_singleton.mp hxmem) with ⟨z, hz⟩
      have hdiv : orderOf x ∣ orderOf (x ^ p) := by
        rw [hz]
        simpa using (orderOf_zpow_dvd (x ^ p) z)
      have hp' : Nat.Prime p := by
        simpa using hp
      have hdiv' : (n : ℕ) ∣ (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using hdiv
      have hlt : (n : ℕ) / p < n := Nat.div_lt_self n.2 hp'.one_lt
      exact (Nat.not_dvd_of_lt hlt) hdiv'
    · intro K hHK
      have hKcyc : IsCyclic K := Subgroup.isCyclic K
      rcases (hcyc.exists_eq_closure_pow K) with ⟨q, hq⟩
      have hxq : x ^ p ∈ Subgroup.closure ({x ^ q} : Set G) := by
        simpa [H, hq] using (hHK (by
          simpa [H] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G)))))
      have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ q) := by
        rcases (Subgroup.mem_closure_singleton.mp hxq) with ⟨z, hz⟩
        rw [hz]
        simpa using (orderOf_zpow_dvd (x ^ q) z)
      have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
      have hpowq : orderOf (x ^ q) = (n : ℕ) / q := by
        simpa [hx, hq, Nat.gcd_eq_left (by
          have : q ∣ (n : ℕ) := by
            have hqmem : x ^ q ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := by
              simpa [hG] using (Subgroup.subset_closure (by simp : x ^ q ∈ ({x ^ q} : Set G)))
            have hqord : orderOf (x ^ q) ∣ orderOf x := by
              rcases (Subgroup.mem_closure_singleton.mp hqmem) with ⟨z, hz⟩
              rw [hz]
              simpa using (orderOf_zpow_dvd x z)
            simpa [hx] using hqord
          exact this) using (orderOf_pow x q)
      have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / q := by
        simpa [hpowp, hpowq] using hdiv
      have hqdivp : q ∣ p := by
        rcases hdiv' with ⟨t, ht⟩
        have hp' : Nat.Prime p := by simpa using hp
        have hpq : p ∣ (n : ℕ) := hpn
        have hqpos : 0 < q := by
          by_contra hq0
          have : (n : ℕ) / q = 0 := by simp [hq0]
          have : (n : ℕ) / p = 0 := by simpa [ht, this] using ht
          exact Nat.ne_of_gt (Nat.div_pos n.2 hp'.pos) this
        have hqdivn : q ∣ (n : ℕ) := by
          have hqord : orderOf (x ^ q) ∣ orderOf x := by
            rcases (Subgroup.mem_closure_singleton.mp (by
              simpa [hG] using (Subgroup.subset_closure (by simp : x ^ q ∈ ({x ^ q} : Set G))))) with
              ⟨z, hz⟩
            rw [hz]
            simpa using (orderOf_zpow_dvd x z)
          simpa [hx] using hqord
        rcases hqdivn with ⟨u, hu⟩
        have hpqeq : p * t = q * u := by
          have hEq : (q * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
            calc
              (q * t) * ((n : ℕ) / p) = q * (((n : ℕ) / p) * t) := by
                simp [mul_assoc, mul_left_comm, mul_comm]
              _ = q * ((n : ℕ) / q) := by rw [ht]
              _ = n := by rw [Nat.mul_div_cancel' hqdivn]
              _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
          have hne : (n : ℕ) / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos n.2 hp'.pos)
          exact Nat.mul_left_cancel hEq
        have hq_le : q ≤ p := by
          have := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
            intro h
            subst h
            simpa using hqpos)) (dvd_trans (by
              refine ⟨t, ?_⟩
              exact hpqeq.symm) (dvd_refl _))
          omega
        exact hp'.eq_one_or_self_of_dvd hqdivp |>.elim (by intro h; omega) id
      rcases hp.eq_one_or_self_of_dvd hqdivp with rfl | rfl
      · exact Or.inr (by simpa [hG, hq])
      · exact Or.inl (by simpa [H, hq])
  · intro hmax
    rcases hmax with ⟨hHtop, hmax⟩
    have hcycH : IsCyclic H := Subgroup.isCyclic H
    rcases (hcyc.exists_eq_closure_pow H) with ⟨k, hk⟩
    have hkne1 : k ≠ 1 := by
      intro hk1
      apply hHtop
      simpa [hk1, hG, hk]
    have hkgt1 : 1 < k := by
      omega
    by_cases hkprime : Nat.Prime k
    · exact ⟨k, hkprime, by
        have hkdiv : k ∣ (n : ℕ) := by
          have hqord : orderOf (x ^ k) ∣ orderOf x := by
            rcases (Subgroup.mem_closure_singleton.mp (by
              simpa [hG] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))) with
              ⟨z, hz⟩
            rw [hz]
            simpa using (orderOf_zpow_dvd x z)
          simpa [hx] using hqord
        exact hkdiv
      , by simpa [hk] ⟩
    · rcases Nat.exists_prime_and_dvd hkgt1 with ⟨p, hp, hpk⟩
      have hp' : Nat.Prime p := hp
      have hpn : p ∣ (n : ℕ) := dvd_trans hpk (by
        have hkdiv : k ∣ (n : ℕ) := by
          have hqord : orderOf (x ^ k) ∣ orderOf x := by
            rcases (Subgroup.mem_closure_singleton.mp (by
              simpa [hG] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))) with
              ⟨z, hz⟩
            rw [hz]
            simpa using (orderOf_zpow_dvd x z)
          simpa [hx] using hqord
        exact hkdiv)
      let K : Subgroup G := Subgroup.closure ({x ^ p} : Set G)
      have hHK : H ≤ K := by
        subst H
        exact Subgroup.closure_le.2 (by
          intro y hy
          rw [Subgroup.mem_closure_singleton] at hy
          rcases hy with ⟨z, rfl⟩
          rw [pow_mul]
          exact Subgroup.subset_closure (by simp))
      cases hmax K hHK with
      | inl hKH =>
          have hqp : k ∣ p := by
            have hxpk : x ^ p ∈ Subgroup.closure ({x ^ k} : Set G) := by
              simpa [hKH, hk] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G)))
            have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ k) := by
              rcases (Subgroup.mem_closure_singleton.mp hxpk) with ⟨z, hz⟩
              rw [hz]
              simpa using (orderOf_zpow_dvd (x ^ k) z)
            have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
              simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
            have hpowk : orderOf (x ^ k) = (n : ℕ) / k := by
              simpa [hx, hk, Nat.gcd_eq_left (by
                have hkdiv : k ∣ (n : ℕ) := by
                  have hqord : orderOf (x ^ k) ∣ orderOf x := by
                    rcases (Subgroup.mem_closure_singleton.mp (by
                      simpa [hG] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))) with
                      ⟨z, hz⟩
                    rw [hz]
                    simpa using (orderOf_zpow_dvd x z)
                  simpa [hx] using hqord
                exact hkdiv) using (orderOf_pow x k)
            have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / k := by
              simpa [hpowp, hpowk] using hdiv
            rcases hdiv' with ⟨t, ht⟩
            have hmpos : 0 < (n : ℕ) / p := Nat.div_pos n.2 hp'.pos
            have hmne : (n : ℕ) / p ≠ 0 := Nat.ne_of_gt hmpos
            have hEq : (k * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
              calc
                (k * t) * ((n : ℕ) / p) = k * (((n : ℕ) / p) * t) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
                _ = k * ((n : ℕ) / k) := by rw [ht]
                _ = n := by rw [Nat.mul_div_cancel' (by
                  have hkdiv : k ∣ (n : ℕ) := by
                    have hqord : orderOf (x ^ k) ∣ orderOf x := by
                      rcases (Subgroup.mem_closure_singleton.mp (by
                        simpa [hG] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))) with
                        ⟨z, hz⟩
                      rw [hz]
                      simpa using (orderOf_zpow_dvd x z)
                    simpa [hx] using hqord
                  exact hkdiv)]
                _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
            have hk_eq : k = p := by
              rcases hp'.eq_one_or_self_of_dvd hqp with hk1 | hk1
              · exact False.elim (hkne1 hk1)
              · exact hk1
            exact by simpa [hk_eq] using hKH
          exact Or.inl hKH
      | inr htop =>
          exact False.elim (hnotTopPow (m := p) hp' hpn htop)
