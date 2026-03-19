import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  classical
  have hsurj : Function.Surjective (fun z : ℤ => x ^ z) := by
    intro g
    have hg : g ∈ Subgroup.closure ({x} : Set G) := by
      simpa [hG] using (show g ∈ (⊤ : Subgroup G) by simp)
    rcases Subgroup.mem_closure_singleton.mp hg with ⟨z, hz⟩
    exact ⟨z, by simpa using hz⟩
  have hcyc : IsCyclic G := ⟨x, hsurj⟩
  have hmem_dvd : ∀ {a : G} {m : ℕ}, a ∈ Subgroup.closure ({x ^ m} : Set G) →
      orderOf a ∣ orderOf (x ^ m) := by
    intro a m ha
    rcases Subgroup.mem_closure_singleton.mp ha with ⟨z, hz⟩
    have hpow : orderOf ((x ^ m) ^ z) ∣ orderOf (x ^ m) := by
      simpa using (orderOf_zpow_dvd (x ^ m) z)
    simpa [hz] using hpow
  constructor
  · rintro ⟨p, hp, hpn, rfl⟩
    constructor
    · intro htop
      have hxmem : x ∈ Subgroup.closure ({x ^ p} : Set G) := by
        simpa [htop]
      have hdiv : orderOf x ∣ orderOf (x ^ p) := hmem_dvd (a := x) (m := p) hxmem
      have hpow : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow (x := x) (n := p))
      have hdiv' : (n : ℕ) ∣ (n : ℕ) / p := by
        simpa [hx, hpow] using hdiv
      have hle : (n : ℕ) ≤ (n : ℕ) / p := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
        intro h0
        exact (Nat.ne_of_gt n.2) h0)) hdiv'
      have hlt : (n : ℕ) / p < n := Nat.div_lt_self n.2 hp.one_lt
      exact (not_lt_of_ge hle) hlt
    · intro K hHK
      rcases hcyc.exists_eq_closure_pow K with ⟨k, hk, rfl⟩
      have hxp : x ^ p ∈ Subgroup.closure ({x ^ k} : Set G) := by
        exact hHK (by
          simpa [H] using (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G))))
      have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ k) := hmem_dvd (a := x ^ p) (m := k) hxp
      have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
        simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow (x := x) (n := p))
      have hpowk : orderOf (x ^ k) = (n : ℕ) / k := by
        simpa [hx, Nat.gcd_eq_left hk] using (orderOf_pow (x := x) (n := k))
      have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / k := by
        simpa [hpowp, hpowk] using hdiv
      have hkdivp : k ∣ p := by
        rcases hdiv' with ⟨t, ht⟩
        have hEq : (k * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
          calc
            (k * t) * ((n : ℕ) / p) = k * (((n : ℕ) / p) * t) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
            _ = k * ((n : ℕ) / k) := by rw [ht]
            _ = n := by rw [Nat.mul_div_cancel' hk]
            _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
        have hne : (n : ℕ) / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos n.2 hp.pos)
        have hktp : k * t = p := Nat.mul_right_cancel hEq hne
        exact ⟨t, hktp⟩
      rcases hp.eq_one_or_self_of_dvd hkdivp with rfl | rfl
      · exact Or.inr (by simp [hG, hH])
      · exact Or.inl rfl
  · intro hmax
    rcases hmax with ⟨hHtop, hmax⟩
    rcases hcyc.exists_eq_closure_pow H with ⟨k, hk, hH⟩
    subst hH
    have hkne1 : k ≠ 1 := by
      intro hk1
      apply hHtop
      simp [hk1, hG]
    have hkgt1 : 1 < k := by omega
    by_cases hkprime : Nat.Prime k
    · exact ⟨k, hkprime, hk, rfl⟩
    · rcases Nat.exists_prime_and_dvd hkgt1 with ⟨p, hp, hpk⟩
      have hp' : Nat.Prime p := by simpa using hp
      have hpn : p ∣ (n : ℕ) := dvd_trans hpk hk
      let K : Subgroup G := Subgroup.closure ({x ^ p} : Set G)
      have hHK : H ≤ K := by
        rw [show H = Subgroup.closure ({x ^ k} : Set G) by rfl]
        exact Subgroup.closure_le.2 (by
          intro y hy
          simpa only [Set.mem_singleton_iff] at hy
          rcases hy with rfl
          rcases hpk with ⟨m, rfl⟩
          simpa [pow_mul] using (Subgroup.subset_closure (by simp : x ^ p ∈ K)))
      have hnotLE : ¬ K ≤ H := by
        intro hKH
        have hxpH : x ^ p ∈ Subgroup.closure ({x ^ k} : Set G) := by
          simpa [H] using (hKH (by
            simpa [K] using (Subgroup.subset_closure (by simp : x ^ p ∈ K))))
        have hdiv : orderOf (x ^ p) ∣ orderOf (x ^ k) := hmem_dvd (a := x ^ p) (m := k) hxpH
        have hpowp : orderOf (x ^ p) = (n : ℕ) / p := by
          simpa [hx, hpn, Nat.gcd_eq_left hpn] using (orderOf_pow (x := x) (n := p))
        have hpowk : orderOf (x ^ k) = (n : ℕ) / k := by
          simpa [hx, Nat.gcd_eq_left hk] using (orderOf_pow (x := x) (n := k))
        have hdiv' : (n : ℕ) / p ∣ (n : ℕ) / k := by
          simpa [hpowp, hpowk] using hdiv
        have hkdivp : k ∣ p := by
          rcases hdiv' with ⟨t, ht⟩
          have hEq : (k * t) * ((n : ℕ) / p) = p * ((n : ℕ) / p) := by
            calc
              (k * t) * ((n : ℕ) / p) = k * (((n : ℕ) / p) * t) := by
                simp [mul_assoc, mul_left_comm, mul_comm]
              _ = k * ((n : ℕ) / k) := by rw [ht]
              _ = n := by rw [Nat.mul_div_cancel' hk]
              _ = p * ((n : ℕ) / p) := by rw [Nat.mul_div_cancel' hpn]
          have hne : (n : ℕ) / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos n.2 hp'.pos)
          have hktp : k * t = p := Nat.mul_right_cancel hEq hne
          exact ⟨t, hktp⟩
        rcases hp'.eq_one_or_self_of_dvd hkdivp with rfl | rfl
        · exact hkne1 rfl
        · exact hkne1 rfl
      have htopK : K = ⊤ := by
        rcases hmax K hHK with rfl | htop
        · exact False.elim (hnotLE le_rfl)
        · exact htop
      exact False.elim (hnotTopPow (m := p) hp' hpn htopK)
