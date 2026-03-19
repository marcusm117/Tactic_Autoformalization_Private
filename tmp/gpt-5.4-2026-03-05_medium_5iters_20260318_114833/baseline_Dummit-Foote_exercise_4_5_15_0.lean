import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  classical
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  let P : Sylow 13 G := Classical.choice (inferInstance : Nonempty (Sylow 13 G))
  have hPcard : Fintype.card P = 13 := by
    simpa [hG] using P.card_eq
  have h13dvd : 13 ∣ card G := by
    omega
  have hnsyl13_dvd : Fintype.card (Sylow 13 G) ∣ 27 := by
    simpa [hG] using Sylow.card_sylow_dvd_index (G := G) (p := 13)
  have hnsyl13_mod : Fintype.card (Sylow 13 G) ≡ 1 [MOD 13] := by
    simpa using Sylow.card_sylow_modEq_one (G := G) (p := 13)
  have hnsyl13_cases : Fintype.card (Sylow 13 G) = 1 ∨ Fintype.card (Sylow 13 G) = 27 := by
    omega
  rcases hnsyl13_cases with h13one | h13max
  · refine ⟨13, P, by decide, h13dvd, ?_⟩
    exact P.normal_of_card_sylow_eq_one h13one
  · letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    let Q : Sylow 3 G := Classical.choice (inferInstance : Nonempty (Sylow 3 G))
    have hQcard : Fintype.card Q = 27 := by
      simpa [hG] using Q.card_eq
    let D : Type* := Σ P : Sylow 13 G, {x : P // x ≠ 1}
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
      have hprimePa : Nat.Prime (Fintype.card Pa) := by
        simpa [hG] using (show Nat.Prime 13 by decide)
      have hprimePb : Nat.Prime (Fintype.card Pb) := by
        simpa [hG] using (show Nat.Prime 13 by decide)
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
    have hDcard : Fintype.card D = Fintype.card (Sylow 13 G) * 12 := by
      dsimp [D]
      rw [Fintype.card_sigma]
      simp only
      congr
      ext R
      have hRcard : Fintype.card R = 13 := by
        simpa [hG] using R.card_eq
      simpa [hRcard] using Fintype.card_ne (1 : R)
    let A : Finset G := Finset.univ.map ⟨f, hf_inj⟩
    have hAcard : A.card = 324 := by
      dsimp [A]
      simp [hDcard, h13max]
    have hAuniv : A ⊆ Finset.univ := by
      intro x hx
      simp
    have hcompl_card : (Finset.univ \ A).card = 27 := by
      have hs := Finset.card_sdiff hAuniv
      have huniv : Finset.univ.card = 351 := by
        simpa [hG]
      omega
    have hSyl3_eq_compl : ∀ R : Sylow 3 G, (R : Subgroup G).toFinset = Finset.univ \ A := by
      intro R
      have hRcard' : Fintype.card R = 27 := by
        simpa [hG] using R.card_eq
      have hRsubset : (R : Subgroup G).toFinset ⊆ Finset.univ \ A := by
        intro x hxR
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hxA
        rcases Finset.mem_map.1 hxA with ⟨a, -, rfl⟩
        rcases a with ⟨P13, x13, hx13⟩
        have hP13card : Fintype.card P13 = 13 := by
          simpa [hG] using P13.card_eq
        have hcop : Nat.Coprime (Fintype.card R) (Fintype.card P13) := by
          omega
        have hdisj : Disjoint (R : Subgroup G) (P13 : Subgroup G) := by
          exact Subgroup.disjoint_of_coprime hcop
        have hxbot : ((x13 : G) ∈ (⊥ : Subgroup G)) := by
          have hxinf : ((x13 : G) ∈ (R : Subgroup G) ⊓ (P13 : Subgroup G)) := by
            exact ⟨hxR, x13.2⟩
          simpa [hdisj.eq_bot] using hxinf
        have hx1 : (x13 : G) = 1 := by
          simpa using hxbot
        exact hx13 (Subtype.ext hx1)
      apply Finset.eq_of_subset_of_card_le hRsubset
      have htoFinset : ((R : Subgroup G).toFinset).card = 27 := by
        simpa [hRcard'] using Subgroup.toFinset_card (R : Subgroup G)
      omega
    have hsub3 : Subsingleton (Sylow 3 G) := by
      refine ⟨?_⟩
      intro R S
      have hR := hSyl3_eq_compl R
      have hS := hSyl3_eq_compl S
      apply Subtype.ext
      ext x
      simpa [hR, hS]
    have hcard3one : Fintype.card (Sylow 3 G) = 1 := by
      exact Fintype.card_of_subsingleton (Sylow 3 G)
    have h3dvd : 3 ∣ card G := by
      omega
    refine ⟨3, Q, by decide, h3dvd, ?_⟩
    exact Q.normal_of_card_sylow_eq_one hcard3one
