import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  intro hS
  have h17p : Nat.Prime 17 := by norm_num
  have h19p : Nat.Prime 19 := by norm_num
  haveI17 : Fact (Nat.Prime 17) := ⟨h17p⟩
  haveI19 : Fact (Nat.Prime 19) := ⟨h19p⟩
  have h17div : Nat.card (Sylow 17 G) ∣ 171 := by
    simpa [hG] using (Sylow.card_sylow_dvd_card_sub_one (G := G) (p := 17))
  have h17mod : Nat.card (Sylow 17 G) ≡ 1 [MOD 17] := by
    simpa using (Sylow.card_sylow_modEq_one (G := G) (p := 17))
  have h19div : Nat.card (Sylow 19 G) ∣ 153 := by
    simpa [hG] using (Sylow.card_sylow_dvd_card_sub_one (G := G) (p := 19))
  have h19mod : Nat.card (Sylow 19 G) ≡ 1 [MOD 19] := by
    simpa using (Sylow.card_sylow_modEq_one (G := G) (p := 19))
  have h17cases : Nat.card (Sylow 17 G) = 1 ∨ Nat.card (Sylow 17 G) = 171 := by
    have hmem : Nat.card (Sylow 17 G) ∈ Nat.divisors 171 := by
      exact Nat.mem_divisors.mpr ⟨h17div, by norm_num⟩
    norm_num at hmem h17mod
    exact hmem
  have h19cases : Nat.card (Sylow 19 G) = 1 ∨ Nat.card (Sylow 19 G) = 153 := by
    have hmem : Nat.card (Sylow 19 G) ∈ Nat.divisors 153 := by
      exact Nat.mem_divisors.mpr ⟨h19div, by norm_num⟩
    norm_num at hmem h19mod
    exact hmem
  rcases h17cases with h17one | h17max
  · let P : Sylow 17 G := Classical.choice inferInstance
    have hPnorm : (P : Subgroup G).Normal := by
      simpa [h17one] using (Sylow.normal_of_card_eq_one (G := G) (p := 17))
    have hbot_or_top := hS.eq_bot_or_eq_top (P : Subgroup G) hPnorm
    rcases hbot_or_top with hbot | htop
    · have hPcard : Fintype.card (P : Type*) = 17 := by
        simpa [hG] using P.card_eq
      have hcard1 : Fintype.card (P : Type*) = 1 := by
        simpa [hbot] using (show Fintype.card (P : Type*) = 1 by simpa using hPcard)
      have hne : (1 : Nat) ≠ 17 := by norm_num
      exact hne (by simpa [hcard1] using hPcard)
    · have hPcard : Fintype.card (P : Type*) = 17 := by
        simpa [hG] using P.card_eq
      have hcardtop : Fintype.card (P : Type*) = 2907 := by
        simpa [htop, hG] using P.card_eq
      have hne : (2907 : Nat) ≠ 17 := by norm_num
      exact hne (by simpa [hcardtop] using hPcard)
  · rcases h19cases with h19one | h19max
    · let P : Sylow 19 G := Classical.choice inferInstance
      have hPnorm : (P : Subgroup G).Normal := by
        simpa [h19one] using (Sylow.normal_of_card_eq_one (G := G) (p := 19))
      have hbot_or_top := hS.eq_bot_or_eq_top (P : Subgroup G) hPnorm
      rcases hbot_or_top with hbot | htop
      · have hPcard : Fintype.card (P : Type*) = 19 := by
          simpa [hG] using P.card_eq
        have hcard1 : Fintype.card (P : Type*) = 1 := by
          simpa [hbot] using (show Fintype.card (P : Type*) = 1 by simpa using hPcard)
        have hne : (1 : Nat) ≠ 19 := by norm_num
        exact hne (by simpa [hcard1] using hPcard)
      · have hPcard : Fintype.card (P : Type*) = 19 := by
          simpa [hG] using P.card_eq
        have hcardtop : Fintype.card (P : Type*) = 2907 := by
          simpa [htop, hG] using P.card_eq
        have hne : (2907 : Nat) ≠ 19 := by norm_num
        exact hne (by simpa [hcardtop] using hPcard)
    · have h17card : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 17 := by
        simpa [hG] using (Classical.choice (Sylow 17 G)).card_eq
      have h19card : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 19 := by
        simpa [hG] using (Classical.choice (Sylow 19 G)).card_eq
      let T17 := Σ P : Sylow 17 G, {x : (P : Subgroup G) // x ≠ 1}
      let T19 := Σ P : Sylow 19 G, {x : (P : Subgroup G) // x ≠ 1}
      let T := T17 ⊕ T19
      let f : T → G := fun t =>
        match t with
        | Sum.inl ⟨P, x⟩ => (x : G)
        | Sum.inr ⟨P, x⟩ => (x : G)
      have hf : Function.Injective f := by
        intro a b hab
        cases a with
        | inl a =>
            rcases a with ⟨P, x⟩
            rcases x with ⟨x, hxne⟩
            cases b with
            | inl b =>
                rcases b with ⟨Q, y⟩
                rcases y with ⟨y, hyne⟩
                simp [f] at hab
                have hxy : (x : G) = y := by simpa using hab
                let H : Subgroup G := Subgroup.closure ({(x : G)} : Set G)
                have hHleP : H ≤ P := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa using hz
                  rw [hz']
                  exact x.property
                have hHleQ : H ≤ Q := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa [hxy] using hz
                  rw [hz']
                  simpa [hxy] using y.property
                have hHdiv : Fintype.card H ∣ 17 := by
                  simpa [h17card] using (Subgroup.card_dvd_card (H := H) (G := P))
                have hHne1 : Fintype.card H ≠ 1 := by
                  intro h1
                  have hsub : Subsingleton H := by
                    simpa [Fintype.card_eq_one_iff] using h1
                  have hxH : (x : G) ∈ H := Subgroup.subset_closure (by simp)
                  exact hxne (Subsingleton.elim ⟨x, hxH⟩ ⟨1, by simp⟩)
                have hHcard : Fintype.card H = 17 := by
                  rcases h17p.eq_one_or_self_of_dvd hHdiv with h1 | h17
                  · exact False.elim (hHne1 h1)
                  · exact h17
                have hHP : H = P := by
                  apply Subgroup.eq_of_le_of_card_eq
                  · exact hHleP
                  · simpa [h17card] using hHcard
                have hHQ : H = Q := by
                  apply Subgroup.eq_of_le_of_card_eq
                  · exact hHleQ
                  · simpa [h17card] using hHcard
                have hPQ : P = Q := by
                  calc
                    P = H := hHP.symm
                    _ = Q := hHQ
                cases hPQ
                simp [hxy]
            | inr b =>
                rcases b with ⟨Q, y⟩
                rcases y with ⟨y, hyne⟩
                simp [f] at hab
                have hxy : (x : G) = y := by simpa using hab
                let H : Subgroup G := Subgroup.closure ({(x : G)} : Set G)
                have hHleP : H ≤ P := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa using hz
                  rw [hz']
                  exact x.property
                have hHleQ : H ≤ Q := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa [hxy] using hz
                  rw [hz']
                  simpa [hxy] using y.property
                have hHdiv17 : Fintype.card H ∣ 17 := by
                  simpa [h17card] using (Subgroup.card_dvd_card (H := H) (G := P))
                have hHdiv19 : Fintype.card H ∣ 19 := by
                  simpa [h19card] using (Subgroup.card_dvd_card (H := H) (G := Q))
                have hHdiv1 : Fintype.card H ∣ 1 := by
                  exact Nat.dvd_gcd hHdiv17 hHdiv19
                have hHcard1 : Fintype.card H = 1 := by
                  exact Nat.dvd_one.mp hHdiv1
                have hsub : Subsingleton H := by
                  simpa [Fintype.card_eq_one_iff] using hHcard1
                have hxH : (x : G) ∈ H := Subgroup.subset_closure (by simp)
                have hx1 : (x : G) = 1 := by
                  exact Subsingleton.elim ⟨x, hxH⟩ ⟨1, by simp⟩
                exact hxne hx1
        | inr a =>
            rcases a with ⟨P, x⟩
            rcases x with ⟨x, hxne⟩
            cases b with
            | inl b =>
                rcases b with ⟨Q, y⟩
                rcases y with ⟨y, hyne⟩
                simp [f] at hab
                have hxy : (x : G) = y := by simpa using hab
                let H : Subgroup G := Subgroup.closure ({(x : G)} : Set G)
                have hHleP : H ≤ P := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa using hz
                  rw [hz']
                  exact x.property
                have hHleQ : H ≤ Q := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa [hxy] using hz
                  rw [hz']
                  simpa [hxy] using y.property
                have hHdiv17 : Fintype.card H ∣ 17 := by
                  simpa [h17card] using (Subgroup.card_dvd_card (H := H) (G := P))
                have hHdiv19 : Fintype.card H ∣ 19 := by
                  simpa [h19card] using (Subgroup.card_dvd_card (H := H) (G := Q))
                have hHdiv1 : Fintype.card H ∣ 1 := by
                  exact Nat.dvd_gcd hHdiv17 hHdiv19
                have hHcard1 : Fintype.card H = 1 := by
                  exact Nat.dvd_one.mp hHdiv1
                have hsub : Subsingleton H := by
                  simpa [Fintype.card_eq_one_iff] using hHcard1
                have hxH : (x : G) ∈ H := Subgroup.subset_closure (by simp)
                have hx1 : (x : G) = 1 := by
                  exact Subsingleton.elim ⟨x, hxH⟩ ⟨1, by simp⟩
                exact hxne hx1
            | inr b =>
                rcases b with ⟨Q, y⟩
                rcases y with ⟨y, hyne⟩
                simp [f] at hab
                have hxy : (x : G) = y := by simpa using hab
                let H : Subgroup G := Subgroup.closure ({(x : G)} : Set G)
                have hHleP : H ≤ P := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa using hz
                  rw [hz']
                  exact x.property
                have hHleQ : H ≤ Q := by
                  refine Subgroup.closure_le.2 ?_
                  intro z hz
                  have hz' : z = (x : G) := by simpa [hxy] using hz
                  rw [hz']
                  simpa [hxy] using y.property
                have hHdiv : Fintype.card H ∣ 17 := by
                  simpa [h17card] using (Subgroup.card_dvd_card (H := H) (G := P))
                have hHne1 : Fintype.card H ≠ 1 := by
                  intro h1
                  have hsub : Subsingleton H := by
                    simpa [Fintype.card_eq_one_iff] using h1
                  have hxH : (x : G) ∈ H := Subgroup.subset_closure (by simp)
                  exact hxne (Subsingleton.elim ⟨x, hxH⟩ ⟨1, by simp⟩)
                have hHcard : Fintype.card H = 17 := by
                  rcases h17p.eq_one_or_self_of_dvd hHdiv with h1 | h17
                  · exact False.elim (hHne1 h1)
                  · exact h17
                have hHP : H = P := by
                  apply Subgroup.eq_of_le_of_card_eq
                  · exact hHleP
                  · simpa [h17card] using hHcard
                have hHQ : H = Q := by
                  apply Subgroup.eq_of_le_of_card_eq
                  · exact hHleQ
                  · simpa [h19card] using hHcard
                have hPQ : P = Q := by
                  calc
                    P = H := hHP.symm
                    _ = Q := hHQ
                cases hPQ
                simp [hxy]
      have hfiber17 : ∀ P : Sylow 17 G, Fintype.card {x : (P : Subgroup G) // x ≠ 1} = 16 := by
        intro P
        have hPcard : Fintype.card (P : Type*) = 17 := by
          simpa [hG] using P.card_eq
        simpa [hPcard] using (Fintype.card_subtype_neq (1 : P))
      have hfiber19 : ∀ P : Sylow 19 G, Fintype.card {x : (P : Subgroup G) // x ≠ 1} = 18 := by
        intro P
        have hPcard : Fintype.card (P : Type*) = 19 := by
          simpa [hG] using P.card_eq
        simpa [hPcard] using (Fintype.card_subtype_neq (1 : P))
      have hcardT17 : Fintype.card T17 = 171 * 16 := by
        simp [T17, h17max, hfiber17]
      have hcardT19 : Fintype.card T19 = 153 * 18 := by
        simp [T19, h19max, hfiber19]
      have hcardT : Fintype.card T = 171 * 16 + 153 * 18 := by
        simp [T, T17, T19, hcardT17, hcardT19]
      have hle : Fintype.card T ≤ Fintype.card G := Fintype.card_le_of_injective f hf
      have hle' : 171 * 16 + 153 * 18 ≤ 2907 := by
        simpa [T, hG, hcardT] using hle
      have hbad : ¬ (171 * 16 + 153 * 18 ≤ 2907) := by norm_num
      exact hbad hle'
