import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  classical
  have hsurj : Function.Surjective (fun m : ℕ => x ^ m) := by
    intro g
    have hg : g ∈ Subgroup.closure ({x} : Set G) := by
      simpa [hG] using (show g ∈ (⊤ : Subgroup G) by simp)
    rcases Subgroup.mem_closure_singleton.mp hg with ⟨z, hz⟩
    cases z with
    | ofNat t =>
        refine ⟨t, ?_⟩
        simpa using hz
    | negSucc t =>
        refine ⟨((n : ℕ) - 1) * (t + 1), ?_⟩
        have hxinv : x⁻¹ = x ^ ((n : ℕ) - 1) := by
          simpa [hx] using (inv_eq_pow_orderOf_sub_one x)
        have hpow : x ^ (((n : ℕ) - 1) * (t + 1)) = x ^ (Int.negSucc t) := by
          calc
            x ^ (((n : ℕ) - 1) * (t + 1)) = (x ^ ((n : ℕ) - 1)) ^ (t + 1) := by
              rw [pow_mul]
            _ = (x⁻¹) ^ (t + 1) := by rw [hxinv]
            _ = x ^ (Int.negSucc t) := by simp
        exact hpow.trans hz
  have hcyc : IsCyclic G := ⟨x, hsurj⟩
  have hmem_dvd : ∀ {a : G} {m : ℕ}, a ∈ Subgroup.closure ({x ^ m} : Set G) →
      orderOf a ∣ orderOf (x ^ m) := by
    intro a m ha
    rcases Subgroup.mem_closure_singleton.mp ha with ⟨z, hz⟩
    cases z with
    | ofNat t =>
        have hza : a = (x ^ m) ^ t := by
          simpa using hz.symm
        simpa [hza] using (orderOf_pow_dvd (x ^ m) t)
    | negSucc t =>
        have hza : a = ((x ^ m)⁻¹) ^ (t + 1) := by
          simpa using hz.symm
        have hpow : orderOf (((x ^ m)⁻¹) ^ (t + 1)) ∣ orderOf ((x ^ m)⁻¹) := by
          simpa using (orderOf_pow_dvd ((x ^ m)⁻¹) (t + 1))
        have hinv : orderOf ((x ^ m)⁻¹) = orderOf (x ^ m) := by
          simpa using (orderOf_inv (x ^ m))
        simpa [hza, hinv] using hpow
  constructor
  · rintro ⟨p, hp, hpn, rfl⟩
    constructor
    · intro htop
      have hxmem : x ∈ Subgroup.closure ({x ^ p} : Set G) := by
        simpa [htop]
      have hdiv : orderOf x ∣ orderOf (x ^ p) := hmem_dvd (a := x) (m := p) hxmem
      have hp' : Nat.Prime p := by
        simpa using hp
      have hpow : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
      have hdiv' : (n : ℕ) ∣ (n : ℕ) / p := by
        simpa [hx, hpow] using hdiv
      have hlt : (n : ℕ) / p < n := Nat.div_lt_self n.2 hp'.one_lt
      exact (Nat.not_dvd_of_lt hlt) hdiv'
    · intro K hHK
      have hKcyc : IsCyclic K := Subgroup.isCyclic K
      rcases hKcyc.exists_generator with ⟨y, hy⟩
      have hKy : K = Subgroup.closure ({(y : G)} : Set G) := by
        ext g
        constructor
        · intro hg
          rcases hy ⟨g, hg⟩ with ⟨m, hm⟩
          exact Subgroup.subset_closure (by simpa using hm)
        · intro hg
          exact (Subgroup.closure_le.2 (by
            intro z hz
            simpa using hz)) hg
      rcases hsurj y with ⟨k, hk⟩
      have hKx : K = Subgroup.closure ({x ^ k} : Set G) := by
        simpa [hKy, hk] using hKy
      have hxpk : x ^ p ∈ Subgroup.closure ({x ^ k} : Set G) := by
        simpa [H, hKx] using (hHK (by
          simpa [H] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G)))))
      have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ k) := hmem_dvd (a := x ^ p) (m := k) hxpk
      have hp' : Nat.Prime p := by
        simpa using hp
      have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
      have hpowk : orderOf (x ^ k) = (n : ℕ) / Nat.gcd (n : ℕ) k := by
        simpa [hx] using (orderOf_pow x k)
      have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / Nat.gcd (n : ℕ) k := by
        simpa [hpowp, hpowk] using hdiv
      rcases hdiv' with ⟨t, ht⟩
      have hgcd : Nat.gcd (n : ℕ) k ∣ p := by
        have hgd : Nat.gcd (n : ℕ) k ∣ (n : ℕ) := Nat.gcd_dvd_left _ _
        have hEq : (n : ℕ) / p * (t * Nat.gcd (n : ℕ) k) = (n : ℕ) / p * p := by
          calc
            (n : ℕ) / p * (t * Nat.gcd (n : ℕ) k) = (((n : ℕ) / p) * t) * Nat.gcd (n : ℕ) k := by
              rw [mul_assoc]
            _ = ((n : ℕ) / Nat.gcd (n : ℕ) k) * Nat.gcd (n : ℕ) k := by rw [ht]
            _ = (n : ℕ) := by rw [Nat.mul_div_cancel' hgd]
            _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
            _ = (n : ℕ) / p * p := by rw [mul_comm]
        have hne : (n : ℕ) / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos n.2 hp'.pos)
        have htp : t * Nat.gcd (n : ℕ) k = p := Nat.mul_left_cancel hEq
        exact ⟨t, by simpa [mul_comm] using htp.symm⟩
      rcases hp'.eq_one_or_self_of_dvd hgcd with h1 | hpEq
      · have hcop : Nat.Coprime (n : ℕ) k := by
          rw [Nat.coprime_iff_gcd_eq_one]
          simpa using h1
        rcases hcop.exists with ⟨u, v, huv⟩
        have hxu : x ^ (u * (k : ℤ)) = (x ^ k) ^ u := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using (zpow_mul x (k : ℤ) u)
        have hxv : x ^ (v * (n : ℤ)) = 1 := by
          calc
            x ^ (v * (n : ℤ)) = (x ^ (n : ℤ)) ^ v := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using (zpow_mul x (n : ℤ) v)
            _ = 1 := by simp [hx]
        have hxmem : x ∈ K := by
          have hyk : x ^ k ∈ K := by
            simpa [hKx] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G)))
          have hpow : (x ^ k) ^ u ∈ K := Subgroup.zpow_mem K hyk u
          have hxeq : x = (x ^ k) ^ u := by
            calc
              x = x ^ (1 : ℤ) := by simp
              _ = x ^ (u * (k : ℤ) + v * (n : ℤ)) := by simpa [huv]
              _ = x ^ (u * (k : ℤ)) * x ^ (v * (n : ℤ)) := by rw [zpow_add]
              _ = (x ^ k) ^ u * 1 := by rw [hxu, hxv]
              _ = (x ^ k) ^ u := by simp
          simpa [hxeq] using hpow
        have hcl : Subgroup.closure ({x} : Set G) ≤ K := Subgroup.closure_le.2 (by
          intro z hz
          simpa using hz)
        have htop : (⊤ : Subgroup G) ≤ K := by
          simpa [hG] using hcl
        exact Or.inr (by exact le_antisymm htop le_top)
      · have hpdivk : p ∣ k := by
          rw [← hpEq]
          exact Nat.gcd_dvd_right _ _
        have hKleH : K ≤ H := by
          rw [hKx, H]
          exact Subgroup.closure_le.2 (by
            intro z hz
            rcases hpdivk with ⟨t, rfl⟩
            simpa [pow_mul] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G))))
        exact Or.inl hKleH
  · intro hmax
    rcases hmax with ⟨hHtop, hmax⟩
    have hHcyc : IsCyclic H := Subgroup.isCyclic H
    rcases hHcyc.exists_generator with ⟨y, hy⟩
    have hHy : H = Subgroup.closure ({(y : G)} : Set G) := by
      ext g
      constructor
      · intro hg
        rcases hy ⟨g, hg⟩ with ⟨m, hm⟩
        exact Subgroup.subset_closure (by simpa using hm)
      · intro hg
        exact (Subgroup.closure_le.2 (by
          intro z hz
          simpa using hz)) hg
    rcases hsurj y with ⟨k, hk⟩
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
        rcases (Subgroup.mem_closure_singleton.mp hkmem) with ⟨z, hz⟩
        have hdivk : orderOf (x ^ k) ∣ orderOf x := hmem_dvd (a := x ^ k) (m := 1) (by
          simpa [hz] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))
        simpa [hx] using hdivk
      refine ⟨k, hkprime, hkdivn, ?_⟩
      simpa [hHk] using hHk
    · rcases Nat.exists_prime_and_dvd hkgt1 with ⟨p, hp, hpk⟩
      have hp' : Nat.Prime p := hp
      have hpn : p ∣ (n : ℕ) := dvd_trans hpk (by
        have hkdivn : k ∣ (n : ℕ) := by
          have hkmem : x ^ k ∈ (Subgroup.closure ({x} : Set G) : Subgroup G) := by
            simpa [hG] using (show (x ^ k) ∈ (⊤ : Subgroup G) by simp)
          rcases (Subgroup.mem_closure_singleton.mp hkmem) with ⟨z, hz⟩
          have hdivk : orderOf (x ^ k) ∣ orderOf x := hmem_dvd (a := x ^ k) (m := 1) (by
            simpa [hz] using (Subgroup.subset_closure (by simp : x ^ k ∈ ({x ^ k} : Set G))))
          simpa [hx] using hdivk
        exact hkdivn)
      let K : Subgroup G := Subgroup.closure ({x ^ p} : Set G)
      have hHK : H ≤ K := by
        subst H
        exact Subgroup.closure_le.2 (by
          intro z hz
          rcases hz with rfl
          simp [pow_mul])
      cases hmax K hHK with
      | inl hKH =>
          exact Or.inl hKH
      | inr htop =>
          exact False.elim (hmem_dvd (a := x ^ p) (m := 1) (by
            simpa [htop] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G))))) ▸
            False.elim (by
              have hpnot : Subgroup.closure ({x ^ p} : Set G) ≠ ⊤ := by
                intro h
                have hxmem : x ∈ Subgroup.closure ({x ^ p} : Set G) := by
                  simpa [h] using (Subgroup.subset_closure (by simp : x ∈ ({x} : Set G)))
                have hdiv : orderOf x ∣ orderOf (x ^ p) := hmem_dvd (a := x) (m := p) hxmem
                have hpow : orderOf (x ^ p) = (n : ℕ) / p := by
                  simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow x p)
                have hdiv' : (n : ℕ) ∣ (n : ℕ) / p := by
                  simpa [hx, hpow] using hdiv
                have hlt : (n : ℕ) / p < n := Nat.div_lt_self n.2 hp'.one_lt
                exact (Nat.not_dvd_of_lt hlt) hdiv'
              exact hpnot htop)
