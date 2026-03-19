import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  have hmem : ∀ g : G, g ∈ Subgroup.closure ({x} : Set G) := by
    intro g
    have hcast : (((cast hG g : Subgroup.closure ({x} : Set G)) : G)) = g := by
      cases hG
      rfl
    exact hcast ▸ (cast hG g).2
  have htop : Subgroup.closure ({x} : Set G) = ⊤ := by
    ext g
    constructor
    · intro _
      simp
    · intro _
      exact hmem g
  have hgen : ∀ g : G, ∃ m : ℤ, x ^ m = g := by
    intro g
    have hg : g ∈ Subgroup.zpowers x := by
      rw [Subgroup.zpowers_eq_closure, htop]
      simp
    exact Subgroup.mem_zpowers_iff.mp hg
  have hpow_proper :
      ∀ {p : ℕ}, Prime p → p ∣ n → Subgroup.closure ({x ^ p} : Set G) ≠ (⊤ : Subgroup G) := by
    intro p hpprime hpn htop_p
    have hxmem : x ∈ Subgroup.closure ({x ^ p} : Set G) := by
      rw [htop_p]
      simp
    rw [Subgroup.zpowers_eq_closure] at hxmem
    rcases Subgroup.mem_zpowers_iff.mp hxmem with ⟨m, hm⟩
    have hm' : x ^ ((p : ℤ) * m) = x := by
      rw [zpow_mul]
      simpa [zpow_natCast] using hm
    have h1 : x ^ (((p : ℤ) * m) - 1) = 1 := by
      rw [sub_eq_add_neg, zpow_add, hm']
      simp
    have hndiv : (((n : ℕ) : ℤ) ∣ ((p : ℤ) * m - 1)) := by
      simpa [hx] using (zpow_eq_one_iff_dvd.mp h1)
    have hpdvdn : ((p : ℤ) ∣ ((n : ℕ) : ℤ)) := by
      rcases hpn with ⟨k, hk⟩
      refine ⟨(k : ℤ), ?_⟩
      exact_mod_cast hk
    have hpm1 : (p : ℤ) ∣ ((p : ℤ) * m - 1) := dvd_trans hpdvdn hndiv
    have hppm : (p : ℤ) ∣ (p : ℤ) * m := ⟨m, by ring⟩
    have hp1z : (p : ℤ) ∣ (1 : ℤ) := by
      have := dvd_sub hppm hpm1
      simpa using this
    have hp1 : p ∣ 1 := by
      exact_mod_cast hp1z
    exact hpprime.not_dvd_one hp1
  constructor
  · rintro ⟨p, hpprime, hpn, rfl⟩
    refine ⟨hpow_proper hpprime hpn, ?_⟩
    intro K hHK
    let y : G ⧸ K := QuotientGroup.mk' K x
    have hydiv : orderOf y ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      change QuotientGroup.mk' K (x ^ p) = 1
      have hxpowK : x ^ p ∈ K := hHK (Subgroup.subset_closure (by simp))
      simp [hxpowK]
    rcases (Nat.dvd_prime hpprime).mp hydiv with h1 | hp
    · right
      have hy1 : y = 1 := orderOf_eq_one_iff.mp h1
      have hxK : x ∈ K := by
        change QuotientGroup.mk' K x = 1
        simpa [y] using hy1
      have hcl : Subgroup.closure ({x} : Set G) ≤ K := by
        apply Subgroup.closure_le.2
        intro g hg
        rcases Set.mem_singleton_iff.mp hg with rfl
        exact hxK
      have : (⊤ : Subgroup G) ≤ K := by
        simpa [htop] using hcl
      exact top_le_iff.mp this
    · left
      apply le_antisymm
      · intro g hg
        rcases hgen g with ⟨m, rfl⟩
        have hym1 : y ^ m = 1 := by
          change QuotientGroup.mk' K (x ^ m) = 1
          simp [hg]
        have hmdiv : (p : ℤ) ∣ m := by
          have hdivm : ((orderOf y : ℤ) ∣ m) := by
            simpa using (zpow_eq_one_iff_dvd.mp hym1)
          simpa [hp] using hdivm
        rw [Subgroup.zpowers_eq_closure]
        rcases hmdiv with ⟨t, rfl⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨t, by
          simpa [zpow_natCast] using (zpow_mul x (p : ℤ) t).symm⟩
      · exact hHK
  · rintro ⟨hne, hmax⟩
    let y : G ⧸ H := QuotientGroup.mk' H x
    have hydivn : orderOf y ∣ (n : ℕ) := by
      apply orderOf_dvd_of_pow_eq_one
      change QuotientGroup.mk' H (x ^ (n : ℕ)) = 1
      have hx1 : x ^ (n : ℕ) = 1 := by
        simpa [hx] using pow_orderOf_eq_one x
      simp [hx1]
    have hyord_ne_zero : orderOf y ≠ 0 := by
      intro h0
      rcases (show 0 ∣ (n : ℕ) from by simpa [h0] using hydivn) with ⟨k, hk⟩
      exact (Nat.ne_of_gt n.pos) (by simpa using hk)
    have hy_ne_one : y ≠ 1 := by
      intro hy1
      have hxH : x ∈ H := by
        change QuotientGroup.mk' H x = 1
        simpa [y] using hy1
      have hcl : Subgroup.closure ({x} : Set G) ≤ H := by
        apply Subgroup.closure_le.2
        intro g hg
        rcases Set.mem_singleton_iff.mp hg with rfl
        exact hxH
      have : (⊤ : Subgroup G) ≤ H := by
        simpa [htop] using hcl
      exact hne (top_le_iff.mp this)
    have hyord_ne_one : orderOf y ≠ 1 := by
      intro h1
      exact hy_ne_one (orderOf_eq_one_iff.mp h1)
    have hyord_gt : 1 < orderOf y := by
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hyord_ne_zero, hyord_ne_one⟩
    rcases Nat.exists_prime_and_dvd hyord_gt with ⟨p, hpprime, hpq⟩
    have hpn : p ∣ (n : ℕ) := dvd_trans hpq hydivn
    have hHeq : H = Subgroup.closure ({x ^ orderOf y} : Set G) := by
      apply le_antisymm
      · intro g hg
        rcases hgen g with ⟨m, rfl⟩
        have hym1 : y ^ m = 1 := by
          change QuotientGroup.mk' H (x ^ m) = 1
          simp [hg]
        have hmdiv : ((orderOf y : ℤ) ∣ m) := by
          simpa using (zpow_eq_one_iff_dvd.mp hym1)
        rw [Subgroup.zpowers_eq_closure]
        rcases hmdiv with ⟨t, rfl⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨t, by
          simpa [zpow_natCast] using (zpow_mul x (orderOf y : ℤ) t).symm⟩
      · apply Subgroup.closure_le.2
        intro g hg
        rcases Set.mem_singleton_iff.mp hg with rfl
        change QuotientGroup.mk' H (x ^ orderOf y) = 1
        simpa [y] using pow_orderOf_eq_one y
    have hHlep : H ≤ Subgroup.closure ({x ^ p} : Set G) := by
      rw [hHeq]
      apply Subgroup.closure_le.2
      intro g hg
      rcases Set.mem_singleton_iff.mp hg with rfl
      rcases hpq with ⟨t, rfl⟩
      simpa [pow_mul] using
        (Subgroup.pow_mem (Subgroup.closure ({x ^ p} : Set G))
          (Subgroup.subset_closure (by simp : x ^ p ∈ ({x ^ p} : Set G))) t)
    rcases hmax (Subgroup.closure ({x ^ p} : Set G)) hHlep with hEq | hTop
    · exact ⟨p, hpprime, hpn, hEq.symm⟩
    · exact False.elim ((hpow_proper hpprime hpn) hTop)
