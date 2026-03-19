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
  have hpow7 : 7 ^ (Nat.factorization 56) 7 = 7 := by native_decide
  have hpow2 : 2 ^ (Nat.factorization 56) 2 = 8 := by native_decide
  have hcard7Nat : ∀ Q : Sylow 7 G, Nat.card ↥(Q : Subgroup G) = 7 := by
    intro Q
    have h := Q.card_eq_multiplicity
    rw [hG'] at h
    simpa [hpow7] using h
  have hcard2Nat : ∀ Q : Sylow 2 G, Nat.card ↥(Q : Subgroup G) = 8 := by
    intro Q
    have h := Q.card_eq_multiplicity
    rw [hG'] at h
    simpa [hpow2] using h
  have hcard7 : ∀ Q : Sylow 7 G, Fintype.card Q = 7 := by
    intro Q
    simpa [Nat.card_eq_fintype_card] using hcard7Nat Q
  have hcard2 : ∀ Q : Sylow 2 G, Fintype.card Q = 8 := by
    intro Q
    simpa [Nat.card_eq_fintype_card] using hcard2Nat Q
  have hsylow7_eq_of_mem :
      ∀ {Q1 Q2 : Sylow 7 G} {x : G},
        x ≠ 1 → x ∈ (Q1 : Subgroup G) → x ∈ (Q2 : Subgroup G) → Q1 = Q2 := by
    intro Q1 Q2 x hx1 hxQ1 hxQ2
    let R : Subgroup G := (Q1 : Subgroup G) ⊓ (Q2 : Subgroup G)
    have hRdiv7 : Fintype.card R ∣ 7 := by
      simpa [hcard7 Q1] using
        (Subgroup.card_dvd_of_le (show R ≤ (Q1 : Subgroup G) from inf_le_left))
    let xR : R := ⟨x, ⟨hxQ1, hxQ2⟩⟩
    have h1x : (1 : R) ≠ xR := by
      intro h
      apply hx1
      exact congrArg Subtype.val h.symm
    haveI : Nontrivial R := ⟨(1 : R), xR, h1x⟩
    have hRgt : 1 < Fintype.card R := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    have hRcard : Fintype.card R = 7 := by
      rcases (Nat.dvd_prime hprime7).mp hRdiv7 with hR1 | hR7
      · exfalso
        have hRle1 : Fintype.card R ≤ 1 := by omega
        exact (not_lt_of_ge hRle1 hRgt)
      · exact hR7
    have hR_eq_Q1 : R = (Q1 : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q1 : Subgroup G) from inf_le_left)
      simpa [hRcard, hcard7 Q1]
    have hR_eq_Q2 : R = (Q2 : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q2 : Subgroup G) from inf_le_right)
      simpa [hRcard, hcard7 Q2]
    have hsub : (Q1 : Subgroup G) = (Q2 : Subgroup G) := by
      rw [← hR_eq_Q1, hR_eq_Q2]
    ext y
    change y ∈ (Q1 : Subgroup G) ↔ y ∈ (Q2 : Subgroup G)
    simpa [hsub]
  let A := Σ Q : Sylow 7 G, {x : Q // x ≠ 1}
  have hfiber : ∀ Q : Sylow 7 G, Fintype.card {x : Q // x ≠ 1} = 6 := by
    intro Q
    have hsum := Fintype.card_subtype_compl (p := fun x : Q => x = 1)
    have : 1 + Fintype.card {x : Q // x ≠ 1} = 7 := by
      simpa [hcard7 Q] using hsum
    omega
  have hAexpr : Fintype.card A = Fintype.card (Sylow 7 G) * 6 := by
    rw [Fintype.card_sigma]
    simp [A, hfiber]
  let f : A → G := fun a => a.2.1
  have hf_inj : Function.Injective f := by
    intro a b hab
    cases a with
    | mk Q1 x1 =>
      cases b with
      | mk Q2 x2 =>
        dsimp [f] at hab
        have hQ : Q1 = Q2 := by
          apply hsylow7_eq_of_mem (x := (x1.1 : G))
          · exact x1.2
          · exact x1.1.2
          · simpa [hab] using x2.1.2
        subst hQ
        have hxQ : x1.1 = x2.1 := by
          apply Subtype.ext
          simpa using hab
        have hx : x1 = x2 := by
          apply Subtype.ext
          exact hxQ
        simp [hx]
  have hA_le : Fintype.card A ≤ 56 := by
    simpa [hG] using (Fintype.card_le_of_injective f hf_inj)
  have hn7le9 : Fintype.card (Sylow 7 G) ≤ 9 := by
    rw [hAexpr] at hA_le
    omega
  have hn7mod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
    simpa [Nat.card_eq_fintype_card] using (card_sylow_modEq_one (G := G) (p := 7))
  have hn7pos : 0 < Fintype.card (Sylow 7 G) := by
    exact Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Sylow 7 G))
  have hn7mod' : Fintype.card (Sylow 7 G) % 7 = 1 := by
    simpa using hn7mod
  have hn7cases : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 8 := by
    omega
  let P7 : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
  rcases hn7cases with hn7one | hn7eight
  · have hle1 : Fintype.card (Sylow 7 G) ≤ 1 := by omega
    have hsubs7 : Subsingleton (Sylow 7 G) := ⟨Fintype.card_le_one_iff.mp hle1⟩
    letI : Subsingleton (Sylow 7 G) := hsubs7
    exact ⟨7, P7, hprime7, by simp [hG], P7.normal_of_subsingleton⟩
  · let P2 : Sylow 2 G := Classical.choice (inferInstance : Nonempty (Sylow 2 G))
    by_cases hn2one : Fintype.card (Sylow 2 G) = 1
    · have hle1 : Fintype.card (Sylow 2 G) ≤ 1 := by omega
      have hsubs2 : Subsingleton (Sylow 2 G) := ⟨Fintype.card_le_one_iff.mp hle1⟩
      letI : Subsingleton (Sylow 2 G) := hsubs2
      exact ⟨2, P2, hprime2, by simp [hG], P2.normal_of_subsingleton⟩
    · have hnot_mem_sylow2_of_mem_sylow7_ne_one :
          ∀ {Q2 : Sylow 2 G} {Q7 : Sylow 7 G} {x : G},
            x ∈ (Q7 : Subgroup G) → x ≠ 1 → x ∉ (Q2 : Subgroup G) := by
        intro Q2 Q7 x hx7 hx1 hx2
        let R : Subgroup G := (Q2 : Subgroup G) ⊓ (Q7 : Subgroup G)
        have hRdiv2 : Fintype.card R ∣ 8 := by
          simpa [hcard2 Q2] using
            (Subgroup.card_dvd_of_le (show R ≤ (Q2 : Subgroup G) from inf_le_left))
        have hRdiv7 : Fintype.card R ∣ 7 := by
          simpa [hcard7 Q7] using
            (Subgroup.card_dvd_of_le (show R ≤ (Q7 : Subgroup G) from inf_le_right))
        let xR : R := ⟨x, ⟨hx2, hx7⟩⟩
        have h1x : (1 : R) ≠ xR := by
          intro h
          apply hx1
          exact congrArg Subtype.val h.symm
        haveI : Nontrivial R := ⟨(1 : R), xR, h1x⟩
        have hRgt : 1 < Fintype.card R := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
        have hRdiv1 : Fintype.card R ∣ 1 := Nat.dvd_gcd hRdiv2 hRdiv7
        have hRle1 : Fintype.card R ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hRdiv1
        exact (not_lt_of_ge hRle1 hRgt)
      have hn7eightA : Fintype.card A = 48 := by
        rw [hAexpr, hn7eight]
        norm_num
      have hpos2 : 0 < Fintype.card (Sylow 2 G) := by
        exact Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Sylow 2 G))
      have hgt2 : 1 < Fintype.card (Sylow 2 G) := by
        omega
      haveI : Nontrivial (Sylow 2 G) := Fintype.one_lt_card_iff_nontrivial.mp hgt2
      obtain ⟨Q2, hQ2ne⟩ := exists_ne P2
      have hnotle : ¬ ((Q2 : Subgroup G) ≤ (P2 : Subgroup G)) := by
        intro hle
        have hsubeq : (Q2 : Subgroup G) = (P2 : Subgroup G) := by
          apply Subgroup.eq_of_le_of_card_ge hle
          simpa [hcard2 Q2, hcard2 P2]
        apply hQ2ne
        ext y
        change y ∈ (Q2 : Subgroup G) ↔ y ∈ (P2 : Subgroup G)
        simpa [hsubeq]
      have hxexists : ∃ x, x ∈ (Q2 : Subgroup G) ∧ x ∉ (P2 : Subgroup G) := by
        by_contra hno
        apply hnotle
        intro x hx
        by_contra hxP
        exact hno ⟨x, hx, hxP⟩
      rcases hxexists with ⟨x, hxQ2, hxP2⟩
      have hxne1 : x ≠ 1 := by
        intro hx1
        apply hxP2
        simpa [hx1]
      let C := (A ⊕ P2) ⊕ PUnit
      let g : C → G := fun z =>
        match z with
        | Sum.inl (Sum.inl a) => f a
        | Sum.inl (Sum.inr y) => y
        | Sum.inr _ => x
      have hg_inj : Function.Injective g := by
        intro z₁ z₂ h
        cases z₁ with
        | inl z₁ =>
          cases z₁ with
          | inl a =>
            cases z₂ with
            | inl z₂ =>
              cases z₂ with
              | inl b =>
                have hab : f a = f b := by simpa [g] using h
                have hab' : a = b := hf_inj hab
                simpa [g, hab']
              | inr y =>
                exfalso
                have hEq : (a.2.1 : G) = (y : G) := by simpa [g, f] using h
                have ha7 : (a.2.1 : G) ∈ (a.1 : Subgroup G) := a.2.1.2
                have ha1 : (a.2.1 : G) ≠ 1 := a.2.2
                have ha2 : (a.2.1 : G) ∈ (P2 : Subgroup G) := hEq.symm ▸ y.2
                exact (hnot_mem_sylow2_of_mem_sylow7_ne_one (Q2 := P2) (Q7 := a.1) ha7 ha1) ha2
            | inr u =>
              exfalso
              have hEq : (a.2.1 : G) = x := by simpa [g, f] using h
              have hx7 : x ∈ (a.1 : Subgroup G) := hEq ▸ a.2.1.2
              exact (hnot_mem_sylow2_of_mem_sylow7_ne_one (Q2 := Q2) (Q7 := a.1) hx7 hxne1) hxQ2
          | inr y =>
            cases z₂ with
            | inl z₂ =>
              cases z₂ with
              | inl a =>
                exfalso
                have hEq : (y : G) = (a.2.1 : G) := by simpa [g, f] using h
                have ha7 : (a.2.1 : G) ∈ (a.1 : Subgroup G) := a.2.1.2
                have ha1 : (a.2.1 : G) ≠ 1 := a.2.2
                have ha2 : (a.2.1 : G) ∈ (P2 : Subgroup G) := hEq ▸ y.2
                exact (hnot_mem_sylow2_of_mem_sylow7_ne_one (Q2 := P2) (Q7 := a.1) ha7 ha1) ha2
              | inr z =>
                have hEq : (y : G) = (z : G) := by simpa [g] using h
                apply Subtype.ext
                simpa using hEq
            | inr u =>
              exfalso
              have hEq : (y : G) = x := by simpa [g] using h
              exact hxP2 (hEq.symm ▸ y.2)
        | inr u =>
          cases z₂ with
          | inl z₂ =>
            cases z₂ with
            | inl a =>
              exfalso
              have hEq : x = (a.2.1 : G) := by simpa [g, f] using h
              have hx7 : x ∈ (a.1 : Subgroup G) := hEq.symm ▸ a.2.1.2
              exact (hnot_mem_sylow2_of_mem_sylow7_ne_one (Q2 := Q2) (Q7 := a.1) hx7 hxne1) hxQ2
            | inr y =>
              exfalso
              have hEq : x = (y : G) := by simpa [g] using h
              exact hxP2 (hEq ▸ y.2)
          | inr v =>
            cases u
            cases v
            rfl
      have hC : Fintype.card C = 57 := by
        dsimp [C]
        rw [Fintype.card_sum, Fintype.card_sum, hn7eightA, hcard2 P2, Fintype.card_punit]
        norm_num
      exfalso
      have hleC := Fintype.card_le_of_injective g hg_inj
      rw [hC, hG] at hleC
      omega
