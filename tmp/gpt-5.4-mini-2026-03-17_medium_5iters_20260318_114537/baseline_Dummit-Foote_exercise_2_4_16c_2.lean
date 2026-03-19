import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  classical
  have hcyc : IsCyclic G := by
    simpa [hG] using (Subgroup.isCyclic (Subgroup.closure ({x} : Set G)))
  have hmem_dvd : ∀ {a : G} {m : ℕ}, a ∈ Subgroup.closure ({x ^ m} : Set G) →
      orderOf a ∣ orderOf (x ^ m) := by
    intro a m ha
    rcases Subgroup.mem_closure_singleton.mp ha with ⟨z, hz⟩
    cases z with
    | ofNat t =>
        have hz' : a = (x ^ m) ^ t := by simpa using hz
        simpa [hz'] using (orderOf_pow_dvd (x ^ m) t)
    | negSucc t =>
        have hz' : a = ((x ^ m)⁻¹) ^ (t + 1) := by simpa using hz
        have hpow : orderOf (((x ^ m)⁻¹) ^ (t + 1)) ∣ orderOf ((x ^ m)⁻¹) := by
          exact orderOf_pow_dvd ((x ^ m)⁻¹) (t + 1)
        have hinv : orderOf ((x ^ m)⁻¹) = orderOf (x ^ m) := by
          simpa using (orderOf_inv (x ^ m))
        simpa [hz', hinv] using hpow
  constructor
  · rintro ⟨p, hp, hpn, rfl⟩
    constructor
    · intro htop
      have hxmem : x ∈ Subgroup.closure ({x ^ p} : Set G) := by
        simpa [htop]
      have hdiv : orderOf x ∣ orderOf (x ^ p) := hmem_dvd (a := x) (m := p) hxmem
      have hp' : Nat.Prime p := by simpa using hp
      have hpow : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
      have hdiv' : (n : ℕ) ∣ (n : ℕ) / p := by
        simpa [hx, hpow] using hdiv
      have hlt : (n : ℕ) / p < n := Nat.div_lt_self n.2 hp'.one_lt
      exact (Nat.not_dvd_of_pos_of_lt (Nat.div_pos n.2 hp'.pos) hlt) hdiv'
    · intro K hHK
      have hKcyc : IsCyclic K := Subgroup.isCyclic K
      rcases hKcyc.exists_generator with ⟨y, hy⟩
      have hKy : K = Subgroup.closure ({(y : G)} : Set G) := by
        simpa using hy
      have hyG : (y : G) ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := by
        simpa [hG] using (show (y : G) ∈ (⊤ : Subgroup G) by simp)
      rcases (Subgroup.mem_closure_singleton.mp hyG) with ⟨k, hk⟩
      have hKx : K = Subgroup.closure ({x ^ k} : Set G) := by
        simpa [hKy, hk] using hKy
      have hxpk : x ^ p ∈ Subgroup.closure ({x ^ k} : Set G) := by
        simpa [H, hKx] using (hHK (by
          simpa [H] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G)))))
      have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ k) := hmem_dvd (a := x ^ p) (m := k) hxpk
      have hp' : Nat.Prime p := by simpa using hp
      have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
      have hkdivn : k ∣ (n : ℕ) := by
        have hkmem : x ^ k ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := by
          simpa [hG] using (show (x ^ k) ∈ (⊤ : Subgroup G) by simp)
        rcases (Subgroup.mem_closure_singleton.mp hkmem) with ⟨t, ht⟩
        have hord : orderOf (x ^ k) ∣ orderOf x := hmem_dvd (a := x ^ k) (m := 1) (by
          simpa [ht] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))
        simpa [hx] using hord
      have hpowk : orderOf (x ^ k) = (n : ℕ) / k := by
        simpa [hx, Nat.gcd_eq_left hkdivn] using (orderOf_pow x k)
      have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / k := by
        simpa [hpowp, hpowk] using hdiv
      have hkp : k ∣ p := by
        rcases hdiv' with ⟨t, ht⟩
        have hp0 : 0 < (n : ℕ) / p := Nat.div_pos n.2 hp'.pos
        have hk0 : 0 < (n : ℕ) / k := by
          exact Nat.div_pos n.2 (Nat.pos_of_ne_zero (by
            intro hk0
            have : orderOf (x ^ k) = 0 := by
              simpa [hpowk, hk0] using (orderOf_pow x k)
            exact (Nat.succ_ne_zero _ ) (by omega)))
        have hEq : k * t = p := by
          have h1 : (k * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
            calc
              (k * t) * ((n : ℕ) / p) = k * (((n : ℕ) / p) * t) := by
                simp [mul_assoc, mul_left_comm, mul_comm]
              _ = k * ((n : ℕ) / k) := by rw [ht]
              _ = n := by rw [Nat.mul_div_cancel' hkdivn]
              _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
          exact Nat.mul_right_cancel h1 (Nat.ne_of_gt hp0)
        exact ⟨t, hEq⟩
      rcases hp.eq_one_or_self_of_dvd hkp with hq1 | hq
      · exact Or.inr (by simp [hq1, hKx, H, hG])
      · exact Or.inl (by simp [hq, hKx, H])
  · intro hmax
    rcases hmax with ⟨hHtop, hmax⟩
    have hHcyc : IsCyclic H := Subgroup.isCyclic H
    rcases hHcyc.exists_generator with ⟨y, hy⟩
    have hHy : H = Subgroup.closure ({(y : G)} : Set G) := by
      simpa using hy
    have hyG : (y : G) ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := by
      simpa [hG] using (show (y : G) ∈ (⊤ : Subgroup G) by simp)
    rcases (Subgroup.mem_closure_singleton.mp hyG) with ⟨k, hk⟩
    have hHk : H = Subgroup.closure ({x ^ k} : Set G) := by
      simpa [hHy, hk] using hHy
    have hkne1 : k ≠ 1 := by
      intro hk1
      apply hHtop
      simpa [hHk, hk1, hG]
    have hkgt1 : 1 < k := by
      omega
    by_cases hkprime : Nat.Prime k
    · have hkdivn : k ∣ (n : ℕ) := by
        have hkmem : x ^ k ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := by
          simpa [hG] using (show (x ^ k) ∈ (⊤ : Subgroup G) by simp)
        rcases (Subgroup.mem_closure_singleton.mp hkmem) with ⟨t, ht⟩
        have hord : orderOf (x ^ k) ∣ orderOf x := hmem_dvd (a := x ^ k) (m := 1) (by
          simpa [ht] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))
        simpa [hx] using hord
      have hpow : orderOf (x ^ k) = (n : ℕ) / k := by
        simpa [hx, Nat.gcd_eq_left hkdivn] using (orderOf_pow x k)
      have hk1 : H = Subgroup.closure ({x ^ k} : Set G) := hHk
      refine ⟨k, hkprime, hkdivn, ?_⟩
      simpa [hk1] using hHk
    · rcases Nat.exists_prime_and_dvd hkgt1 with ⟨p, hp, hpk⟩
      have hp' : Nat.Prime p := hp
      have hpn : p ∣ (n : ℕ) := dvd_trans hpk (by
        have hkdivn : k ∣ (n : ℕ) := by
          have hkmem : x ^ k ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := by
            simpa [hG] using (show (x ^ k) ∈ (⊤ : Subgroup G) by simp)
          rcases (Subgroup.mem_closure_singleton.mp hkmem) with ⟨t, ht⟩
          have hord : orderOf (x ^ k) ∣ orderOf x := hmem_dvd (a := x ^ k) (m := 1) (by
            simpa [ht] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))
          simpa [hx] using hord
        exact hkdivn)
      let K : Subgroup G := Subgroup.closure ({x ^ p} : Set G)
      have hHK : H ≤ K := by
        subst H
        exact Subgroup.closure_le.2 (by
          intro z hz
          rcases hz with ⟨m, rfl⟩
          rw [pow_mul]
          exact Subgroup.subset_closure (by simp))
      cases hmax K hHK with
      | inl hKH =>
          have hxpk : x ^ p ∈ Subgroup.closure ({x ^ k} : Set G) := by
            simpa [hKH, hHk] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G)))
          have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ k) := hmem_dvd (a := x ^ p) (m := k) hxpk
          have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
            simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
          have hpowk : orderOf (x ^ k) = (n : ℕ) / k := by
            simpa [hx, Nat.gcd_eq_left hkdivn] using (orderOf_pow x k)
          have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / k := by
            simpa [hpowp, hpowk] using hdiv
          have hkp : k ∣ p := by
            rcases hdiv' with ⟨t, ht⟩
            have hp0 : 0 < (n : ℕ) / p := Nat.div_pos n.2 hp'.pos
            have hEq : k * t = p := by
              have h1 : (k * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
                calc
                  (k * t) * ((n : ℕ) / p) = k * (((n : ℕ) / p) * t) := by
                    simp [mul_assoc, mul_left_comm, mul_comm]
                  _ = k * ((n : ℕ) / k) := by rw [ht]
                  _ = n := by rw [Nat.mul_div_cancel' hkdivn]
                  _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
              exact Nat.mul_right_cancel h1 (Nat.ne_of_gt hp0)
            exact ⟨t, hEq⟩
          rcases hp'.eq_one_or_self_of_dvd hkp with hk1 | hk1
          · exact False.elim (hkne1 hk1)
          · have hk_eq : k = p := hk1
            exact False.elim (hnotTopPow (m := p) hp' hpn (by
              simpa [hKH, hHk, hk_eq] using hKH))
      | inr htop =>
          exact False.elim (hnotTopPow (m := p) hp' hpn htop)
