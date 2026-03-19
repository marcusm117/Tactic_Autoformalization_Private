import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have hprime7 : Nat.Prime 7 := by decide
  have hprime2 : Nat.Prime 2 := by decide
  letI : Fact (Nat.Prime 7) := ⟨hprime7⟩
  letI : Fact (Nat.Prime 2) := ⟨hprime2⟩
  have hG' : Nat.card G = 56 := by
    simpa [Nat.card_eq_fintype_card] using hG
  have hcard7 : ∀ Q : Sylow 7 G, Nat.card ↥↑Q = 7 := by
    intro Q
    have h := Q.card_eq_multiplicity
    rw [hG'] at h
    norm_num at h
    exact h
  have hcard2 : ∀ Q : Sylow 2 G, Nat.card ↥↑Q = 8 := by
    intro Q
    have h := Q.card_eq_multiplicity
    rw [hG'] at h
    norm_num at h
    exact h
  have hcard7F : ∀ Q : Sylow 7 G, Fintype.card Q = 7 := by
    intro Q
    simpa [Nat.card_eq_fintype_card] using hcard7 Q
  have hcard2F : ∀ Q : Sylow 2 G, Fintype.card Q = 8 := by
    intro Q
    simpa [Nat.card_eq_fintype_card] using hcard2 Q
  let P7 : Sylow 7 G := Classical.choice inferInstance
  set n7 : ℕ := Nat.card (Sylow 7 G) with hn7def
  have hn7div : n7 ∣ 8 := by
    simpa [hn7def, hG', hcard7 P7] using P7.card_sylow_dvd_index
  have hn7mod : n7 ≡ 1 [MOD 7] := by
    simpa [hn7def] using P7.card_sylow_modEq_one
  have hpos7F : 0 < Fintype.card (Sylow 7 G) := Fintype.card_pos_iff.mpr inferInstance
  have hpos7 : 0 < n7 := by
    simpa [hn7def, Nat.card_eq_fintype_card] using hpos7F
  have hle7 : n7 ≤ 8 := Nat.le_of_dvd hpos7 hn7div
  have hn7cases : n7 = 1 ∨ n7 = 8 := by
    interval_cases n7
    · exfalso
      norm_num at hn7mod
    · exact Or.inl rfl
    · exfalso
      norm_num at hn7mod
    · exfalso
      norm_num at hn7mod
    · exfalso
      norm_num at hn7mod
    · exfalso
      norm_num at hn7mod
    · exfalso
      norm_num at hn7mod
    · exfalso
      norm_num at hn7mod
    · exact Or.inr rfl
  rcases hn7cases with hn7one | hn7eight
  · have hn7one' : Nat.card (Sylow 7 G) = 1 := by
      simpa [hn7def] using hn7one
    have hsubs7 : Subsingleton (Sylow 7 G) := by
      refine ⟨?_⟩
      exact Fintype.card_le_one_iff.mp (by
        simpa [Nat.card_eq_fintype_card, hn7one'])
    exact ⟨7, P7, hprime7, by simp [hG], P7.normal_of_subsingleton⟩
  · have hn7eight' : Nat.card (Sylow 7 G) = 8 := by
      simpa [hn7def] using hn7eight
    have hn7eightF : Fintype.card (Sylow 7 G) = 8 := by
      simpa [Nat.card_eq_fintype_card] using hn7eight'
    let P2 : Sylow 2 G := Classical.choice inferInstance
    have hnot_mem_sylow2_of_mem_sylow7_ne_one :
        ∀ {Q2 : Sylow 2 G} {Q7 : Sylow 7 G} {x : G},
          x ∈ (Q7 : Subgroup G) → x ≠ 1 → x ∉ (Q2 : Subgroup G) := by
      intro Q2 Q7 x hx7 hx1 hx2
      let R : Subgroup G := (Q2 : Subgroup G) ⊓ (Q7 : Subgroup G)
      have hRdiv2 : Nat.card ↥R ∣ 8 := by
        simpa [hcard2 Q2] using
          (Subgroup.card_dvd_of_le (show R ≤ (Q2 : Subgroup G) from inf_le_left))
      have hRdiv7 : Nat.card ↥R ∣ 7 := by
        simpa [hcard7 Q7] using
          (Subgroup.card_dvd_of_le (show R ≤ (Q7 : Subgroup G) from inf_le_right))
      have hne : (1 : R) ≠ ⟨x, ⟨hx2, hx7⟩⟩ := by
        intro h
        apply hx1
        exact congrArg Subtype.val h
      haveI : Nontrivial R := nontrivial_iff_exists_ne.mpr ⟨1, ⟨x, ⟨hx2, hx7⟩⟩, hne⟩
      have hRgtF : 1 < Fintype.card R := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
      have hRgt : 1 < Nat.card ↥R := by
        simpa [Nat.card_eq_fintype_card] using hRgtF
      have hRdiv1 : Nat.card ↥R ∣ 1 := by
        simpa using Nat.dvd_gcd hRdiv2 hRdiv7
      have hRle1 : Nat.card ↥R ≤ 1 := Nat.le_of_dvd (by decide) hRdiv1
      exact (not_lt_of_ge hRle1 hRgt)
    have hsylow7_eq_of_mem :
        ∀ {Q1 Q2 : Sylow 7 G} {x : G},
          x ≠ 1 → x ∈ (Q1 : Subgroup G) → x ∈ (Q2 : Subgroup G) → Q1 = Q2 := by
      intro Q1 Q2 x hx1 hxQ1 hxQ2
      let R : Subgroup G := (Q1 : Subgroup G) ⊓ (Q2 : Subgroup G)
      have hRdiv7 : Nat.card ↥R ∣ 7 := by
        simpa [hcard7 Q1] using
          (Subgroup.card_dvd_of_le (show R ≤ (Q1 : Subgroup G) from inf_le_left))
      have hne : (1 : R) ≠ ⟨x, ⟨hxQ1, hxQ2⟩⟩ := by
        intro h
        apply hx1
        exact congrArg Subtype.val h
      haveI : Nontrivial R := nontrivial_iff_exists_ne.mpr ⟨1, ⟨x, ⟨hxQ1, hxQ2⟩⟩, hne⟩
      have hRgtF : 1 < Fintype.card R := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
      have hRgt : 1 < Nat.card ↥R := by
        simpa [Nat.card_eq_fintype_card] using hRgtF
      have hRcard : Nat.card ↥R = 7 := by
        rcases (Nat.dvd_prime hprime7).mp hRdiv7 with hR1 | hR7
        · exfalso
          have hRle1 : Nat.card ↥R ≤ 1 := by simpa [hR1]
          exact (not_lt_of_ge hRle1 hRgt)
        · exact hR7
      have hR_eq_Q1 : R = (Q1 : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q1 : Subgroup G) from inf_le_left)
        simpa [Nat.card_eq_fintype_card, hRcard, hcard7 Q1]
      have hR_eq_Q2 : R = (Q2 : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q2 : Subgroup G) from inf_le_right)
        simpa [Nat.card_eq_fintype_card, hRcard, hcard7 Q2]
      have hsub : (Q1 : Subgroup G) = (Q2 : Subgroup G) := by
        rw [← hR_eq_Q1, hR_eq_Q2]
      ext y
      change y ∈ (Q1 : Subgroup G) ↔ y ∈ (Q2 : Subgroup G)
      simpa [hsub]
    let A := Σ Q : Sylow 7 G, {x : Q // x ≠ 1}
    have hfiber : ∀ Q : Sylow 7 G, Fintype.card {x : Q // x ≠ 1} = 6 := by
      intro Q
      simpa [hcard7F Q] using (Fintype.card_subtype_neq (1 : Q))
    have hA : Fintype.card A = 48 := by
      rw [Fintype.card_sigma]
      simp [A, hfiber, hn7eightF]
    let f : A → G := fun a => a.2.1
    have hf_inj : Function.Injective f := by
      intro a b hab
      cases a with
      | mk Q1 x1 =>
        cases b with
        | mk Q2 x2 =>
          dsimp [f] at hab
          have hQ : Q1 = Q2 := by
            apply hsylow7_eq_of_mem
            · simpa using x1.2
            · simpa using x1.1.2
            · simpa [hab] using x2.1.2
          subst hQ
          have hx1' : x1.1 = x2.1 := by
            apply Subtype.ext
            simpa using hab
          have hx : x1 = x2 := by
            apply Subtype.ext
            exact hx1'
          simp [hx]
    let g : A ⊕ P2 → G := fun z => Sum.elim (fun a => f a) (fun y => y) z
    have hg_inj : Function.Injective g := by
      intro z₁ z₂ h
      cases z₁ with
      | inl a =>
        cases z₂ with
        | inl b =>
          simp [g] at h
          have ha : a = b := hf_inj h
          simpa [ha]
        | inr y =>
          simp [g, f] at h
          exfalso
          have hy7 : (a.2.1 : G) ∈ (a.1 : Subgroup G) := a.2.1.2
          have hy1 : (a.2.1 : G) ≠ 1 := by simpa using a.2.2
          have hy2 : (a.2.1 : G) ∈ (P2 : Subgroup G) := h ▸ y.2
          exact (hnot_mem_sylow2_of_mem_sylow7_ne_one (Q2 := P2) (Q7 := a.1) hy7 hy1) hy2
      | inr x =>
        cases z₂ with
        | inl b =>
          simp [g, f] at h
          exfalso
          have hx2 : (b.2.1 : G) ∈ (P2 : Subgroup G) := h.symm ▸ x.2
          have hx7 : (b.2.1 : G) ∈ (b.1 : Subgroup G) := b.2.1.2
          have hx1 : (b.2.1 : G) ≠ 1 := by simpa using b.2.2
          exact (hnot_mem_sylow2_of_mem_sylow7_ne_one (Q2 := P2) (Q7 := b.1) hx7 hx1) hx2
        | inr y =>
          simp [g] at h
          have hxy : x = y := by
            apply Subtype.ext
            simpa using h
          simpa [hxy]
    have hsurj : Function.Surjective g := by
      by_contra hnsurj
      have hlt := Fintype.card_lt_of_injective_not_surjective g hg_inj hnsurj
      have hsum : Fintype.card (A ⊕ P2) = 56 := by
        rw [Fintype.card_sum, hA, hcard2F P2]
        norm_num
      rw [hsum, hG] at hlt
      norm_num at hlt
    have huniq : ∀ Q : Sylow 2 G, Q = P2 := by
      intro Q
      have hle : (Q : Subgroup G) ≤ (P2 : Subgroup G) := by
        intro x hxQ
        by_cases hx1 : x = 1
        · simpa [hx1]
        · obtain ⟨z, hz⟩ := hsurj x
          cases z with
          | inl a =>
            have hz' : (a.2.1 : G) = x := by
              simpa [g, f] using hz
            have hx7 : x ∈ (a.1 : Subgroup G) := by
              simpa [hz'] using a.2.1.2
            have hxneq : x ≠ 1 := by
              simpa [hz'] using a.2.2
            exact False.elim ((hnot_mem_sylow2_of_mem_sylow7_ne_one (Q2 := Q) (Q7 := a.1) hx7 hxneq) hxQ)
          | inr y =>
            have hz' : (y : G) = x := by
              simpa [g] using hz
            simpa [hz'] using y.2
      have hsubeq : (Q : Subgroup G) = (P2 : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge hle
        simpa [hcard2F Q, hcard2F P2]
      ext x
      change x ∈ (Q : Subgroup G) ↔ x ∈ (P2 : Subgroup G)
      simpa [hsubeq]
    have hsubs2 : Subsingleton (Sylow 2 G) := by
      refine ⟨?_⟩
      intro Q1 Q2
      rw [huniq Q1, huniq Q2]
    exact ⟨2, P2, hprime2, by simp [hG], P2.normal_of_subsingleton⟩
