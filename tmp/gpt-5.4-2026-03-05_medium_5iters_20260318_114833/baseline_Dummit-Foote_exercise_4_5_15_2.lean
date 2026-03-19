import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  classical
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  let P : Sylow 13 G := Classical.choice (inferInstance : Nonempty (Sylow 13 G))
  have h13dvd : 13 ∣ card G := by omega
  have hpow3 : 3 ^ (Nat.factorization 351 3) = 27 := by native_decide
  have hpow13 : 13 ^ (Nat.factorization 351 13) = 13 := by native_decide
  have hquot13 : 351 / 13 ^ (Nat.factorization 351 13) = 27 := by native_decide
  set n13 : ℕ := card (Sylow 13 G)
  have hn13_dvd : n13 ∣ 27 := by
    simpa [n13, hG, hquot13] using card_sylow_dvd_index (G := G) (p := 13)
  have hn13_mod : n13 ≡ 1 [MOD 13] := by
    simpa [n13] using card_sylow_modEq_one (G := G) (p := 13)
  have hn13_pos : 0 < n13 := by
    dsimp [n13]
    exact Fintype.card_pos_iff.mpr ⟨P⟩
  have hd : n13 = 1 ∨ n13 = 3 ∨ n13 = 9 ∨ n13 = 27 := by
    rcases hn13_dvd with ⟨k, hk⟩
    have hk_le : k ≤ 27 := by omega
    interval_cases k <;> omega
  have hnot3 : n13 ≠ 3 := by
    intro h
    have h' : (3 : ℕ) ≡ 1 [MOD 13] := by simpa [h] using hn13_mod
    have : ¬ ((3 : ℕ) ≡ 1 [MOD 13]) := by native_decide
    exact this h'
  have hnot9 : n13 ≠ 9 := by
    intro h
    have h' : (9 : ℕ) ≡ 1 [MOD 13] := by simpa [h] using hn13_mod
    have : ¬ ((9 : ℕ) ≡ 1 [MOD 13]) := by native_decide
    exact this h'
  rcases hd with h13one | h13three | h13nine | h13max
  · have hsub13 : Subsingleton (Sylow 13 G) := by
      rw [Fintype.card_eq_one_iff] at h13one
      rcases h13one with ⟨S, hS⟩
      exact ⟨fun a b => by
        calc
          a = S := hS a
          _ = b := (hS b).symm⟩
    letI : Subsingleton (Sylow 13 G) := hsub13
    refine ⟨13, P, by decide, h13dvd, ?_⟩
    infer_instance
  · exact (hnot3 h13three).elim
  · exact (hnot9 h13nine).elim
  · letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    let Q : Sylow 3 G := Classical.choice (inferInstance : Nonempty (Sylow 3 G))
    have hQcard : card Q = 27 := by
      have h := Q.card_eq_multiplicity
      rw [hG] at h
      simpa [hpow3] using h
    let D := Σ R : Sylow 13 G, {x : R // x ≠ 1}
    let f : D → G := fun a => a.2.1
    have hf_inj : Function.Injective f := by
      intro a b hab
      rcases a with ⟨Pa, xa, hxa⟩
      rcases b with ⟨Pb, xb, hxb⟩
      dsimp [f] at hab
      have hsuba : Subgroup.zpowers (xa : G) ≤ (Pa : Subgroup G) := by
        exact Subgroup.zpowers_le.2 xa.2
      have hsubb : Subgroup.zpowers (xa : G) ≤ (Pb : Subgroup G) := by
        rw [hab]
        exact Subgroup.zpowers_le.2 xb.2
      have hPaCard : card Pa = 13 := by
        have h := Pa.card_eq_multiplicity
        rw [hG] at h
        simpa [hpow13] using h
      have hPbCard : card Pb = 13 := by
        have h := Pb.card_eq_multiplicity
        rw [hG] at h
        simpa [hpow13] using h
      have hprimePa : Nat.Prime (card Pa) := by
        rw [hPaCard]
        decide
      have hprimePb : Nat.Prime (card Pb) := by
        rw [hPbCard]
        decide
      have hzPa : Subgroup.zpowers (xa : G) = (Pa : Subgroup G) := by
        rcases Subgroup.eq_bot_or_eq_of_le_prime hsuba hprimePa with hbot | hEq
        · exfalso
          have hxmem : (xa : G) ∈ Subgroup.zpowers (xa : G) := by
            exact ⟨1, by simp⟩
          have hx1 : (xa : G) = 1 := by
            simpa [hbot] using hxmem
          exact hxa (Subtype.ext hx1)
        · exact hEq
      have hzPb : Subgroup.zpowers (xa : G) = (Pb : Subgroup G) := by
        rcases Subgroup.eq_bot_or_eq_of_le_prime hsubb hprimePb with hbot | hEq
        · exfalso
          have hxmem : (xa : G) ∈ Subgroup.zpowers (xa : G) := by
            exact ⟨1, by simp⟩
          have hx1 : (xa : G) = 1 := by
            simpa [hbot] using hxmem
          exact hxa (Subtype.ext hx1)
        · exact hEq
      have hPab : (Pa : Subgroup G) = (Pb : Subgroup G) := by
        trans Subgroup.zpowers (xa : G) <;> symm <;> assumption
      have hxa_eq_xb : xa = xb := by
        apply Subtype.ext
        simpa using hab
      cases Pa
      cases Pb
      cases hPab
      cases hxa_eq_xb
      rfl
    have hfiber13 : ∀ R : Sylow 13 G, card {x : R // x ≠ 1} = 12 := by
      intro R
      have hRcard : card R = 13 := by
        have h := R.card_eq_multiplicity
        rw [hG] at h
        simpa [hpow13] using h
      simpa [hRcard] using Fintype.card_ne (1 : R)
    have hDcard : card D = card (Sylow 13 G) * 12 := by
      dsimp [D]
      rw [Fintype.card_sigma]
      simp [hfiber13]
    let A : Finset G := Finset.univ.map ⟨f, hf_inj⟩
    have hAcard : A.card = 324 := by
      have h : A.card = n13 * 12 := by
        calc
          A.card = card D := by
            dsimp [A]
            simp
          _ = card (Sylow 13 G) * 12 := hDcard
          _ = n13 * 12 := by rfl
      rw [h13max] at h
      norm_num at h
      exact h
    have hcompl_card : (Finset.univ \ A).card = 27 := by
      have hs : (Finset.univ \ A).card = (Finset.univ : Finset G).card - A.card := by
        exact Finset.card_sdiff (Finset.subset_univ A)
      have huniv : (Finset.univ : Finset G).card = 351 := by
        simpa [hG]
      omega
    let B : Sylow 3 G → Finset G := fun R =>
      Finset.univ.map
        ⟨fun x : R => (x : G), by
          intro a b h
          exact Subtype.ext h⟩
    have hRcard : ∀ R : Sylow 3 G, card R = 27 := by
      intro R
      have h := R.card_eq_multiplicity
      rw [hG] at h
      simpa [hpow3] using h
    have hBcard : ∀ R : Sylow 3 G, (B R).card = 27 := by
      intro R
      simp [B, hRcard R]
    have hBsubset : ∀ R : Sylow 3 G, B R ⊆ Finset.univ \ A := by
      intro R x hx
      rw [Finset.mem_sdiff]
      constructor
      · simp
      · intro hxA
        have hxR : x ∈ (R : Subgroup G) := by
          rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact y.2
        rcases Finset.mem_map.1 hxA with ⟨a, ha, rfl⟩
        rcases a with ⟨P13, x13, hx13⟩
        have hP13card : card P13 = 13 := by
          have h := P13.card_eq_multiplicity
          rw [hG] at h
          simpa [hpow13] using h
        have hcop : Nat.Coprime (card R) (card P13) := by
          rw [hRcard R, hP13card]
          decide
        have hdisj : Disjoint (R : Subgroup G) (P13 : Subgroup G) := by
          exact Subgroup.disjoint_of_coprime hcop
        have hxinf : ((x13 : G) ∈ (R : Subgroup G) ⊓ (P13 : Subgroup G)) := by
          exact ⟨hxR, x13.2⟩
        have hxbot : ((x13 : G) ∈ (⊥ : Subgroup G)) := by
          simpa [hdisj.eq_bot] using hxinf
        have hx1 : (x13 : G) = 1 := by
          simpa using hxbot
        exact hx13 (Subtype.ext hx1)
    have hBeq : ∀ R : Sylow 3 G, B R = Finset.univ \ A := by
      intro R
      apply Finset.eq_of_subset_of_card_le (hBsubset R)
      rw [hcompl_card, hBcard R]
    have hsub3 : Subsingleton (Sylow 3 G) := by
      refine ⟨fun R S => ?_⟩
      apply Subtype.ext
      ext x
      constructor
      · intro hx
        have hxBR : x ∈ B R := by
          dsimp [B]
          exact Finset.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
        have hxBS : x ∈ B S := by rwa [hBeq R, hBeq S] at hxBR
        rcases Finset.mem_map.mp hxBS with ⟨y, hy, hyx⟩
        simpa using y.2
      · intro hx
        have hxBS : x ∈ B S := by
          dsimp [B]
          exact Finset.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
        have hxBR : x ∈ B R := by rwa [hBeq S, hBeq R] at hxBS
        rcases Finset.mem_map.mp hxBR with ⟨y, hy, hyx⟩
        simpa using y.2
    letI : Subsingleton (Sylow 3 G) := hsub3
    have h3dvd : 3 ∣ card G := by omega
    refine ⟨3, Q, by decide, h3dvd, ?_⟩
    infer_instance
