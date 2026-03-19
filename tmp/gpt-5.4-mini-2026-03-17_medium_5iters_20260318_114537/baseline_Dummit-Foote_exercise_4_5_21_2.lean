import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  intro hS
  have h17p : Nat.Prime 17 := by decide
  have h19p : Nat.Prime 19 := by decide
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
      exact Nat.mem_divisors.mpr ⟨h17div, by decide⟩
    norm_num at hmem h17mod
    exact hmem
  have h19cases : Nat.card (Sylow 19 G) = 1 ∨ Nat.card (Sylow 19 G) = 153 := by
    have hmem : Nat.card (Sylow 19 G) ∈ Nat.divisors 153 := by
      exact Nat.mem_divisors.mpr ⟨h19div, by decide⟩
    norm_num at hmem h19mod
    exact hmem
  rcases h17cases with h17one | h17max
  · have hnorm : (Classical.choice (Sylow 17 G) : Subgroup G).Normal := by
      simpa [h17one] using (Sylow.normal_of_card_eq_one (G := G) (p := 17))
    have hbot_or_top := hS.eq_bot_or_eq_top (Classical.choice (Sylow 17 G) : Subgroup G) hnorm
    rcases hbot_or_top with hbot | htop
    · have hcard1 : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 1 := by
        simpa [hbot] using (Classical.choice (Sylow 17 G)).card_eq
      have hcard17 : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 17 := by
        simpa [hG] using (Classical.choice (Sylow 17 G)).card_eq
      omega
    · have hcard2907 : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 2907 := by
        simpa [htop, hG] using (Classical.choice (Sylow 17 G)).card_eq
      have hcard17 : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 17 := by
        simpa [hG] using (Classical.choice (Sylow 17 G)).card_eq
      omega
  · rcases h19cases with h19one | h19max
    · have hnorm : (Classical.choice (Sylow 19 G) : Subgroup G).Normal := by
        simpa [h19one] using (Sylow.normal_of_card_eq_one (G := G) (p := 19))
      have hbot_or_top := hS.eq_bot_or_eq_top (Classical.choice (Sylow 19 G) : Subgroup G) hnorm
      rcases hbot_or_top with hbot | htop
      · have hcard1 : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 1 := by
          simpa [hbot] using (Classical.choice (Sylow 19 G)).card_eq
        have hcard19 : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 19 := by
          simpa [hG] using (Classical.choice (Sylow 19 G)).card_eq
        omega
      · have hcard2907 : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 2907 := by
          simpa [htop, hG] using (Classical.choice (Sylow 19 G)).card_eq
        have hcard19 : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 19 := by
          simpa [hG] using (Classical.choice (Sylow 19 G)).card_eq
        omega
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
          rcases x with ⟨gx, hgxP⟩
          cases b with
          | inl b =>
            rcases b with ⟨Q, y⟩
            rcases y with ⟨y, hyne⟩
            rcases y with ⟨gy, hgyQ⟩
            simp [f] at hab
            subst hab
            let I : Subgroup G := P ⊓ Q
            have hIleP : I ≤ P := inf_le_left
            have hIleQ : I ≤ Q := inf_le_right
            have hgI : (gx : G) ∈ I := ⟨hgxP, by simpa using hgyQ⟩
            have hInotbot : I ≠ ⊥ := by
              intro hbot
              have : (gx : G) = 1 := by
                have hsub : Subsingleton I := by
                  simpa [Fintype.card_eq_one_iff] using (show Fintype.card I = 1 by simpa [hbot])
                exact Subsingleton.elim _ _
              exact hxne this
            have hPcard : Fintype.card (P : Type*) = 17 := by
              simpa [hG] using P.card_eq
            have hQcard : Fintype.card (Q : Type*) = 17 := by
              simpa [hG] using Q.card_eq
            have hIdiv : Fintype.card I ∣ 17 := by
              exact (Subgroup.card_dvd_card (H := I) (G := P)).trans_eq ?_
            · have hIcard : Fintype.card I = 17 := by
                have hdiv' : Fintype.card I ∣ 17 := by
                  exact (Subgroup.card_dvd_card (H := I) (G := P))
                rcases h17p.eq_one_or_self_of_dvd hdiv' with h1 | h17
                · exfalso
                  exact hInotbot (by
                    have hsub : Subsingleton I := by
                      simpa [Fintype.card_eq_one_iff] using h1
                    exact (Subsingleton.elim ⟨gx, hgI⟩ ⟨1, by simp⟩))
                · exact h17
              have hIP : I = P := by
                apply Subgroup.eq_of_le_of_card_eq
                · exact hIleP
                · simpa [hPcard] using hIcard
              have hIQ : I = Q := by
                apply Subgroup.eq_of_le_of_card_eq
                · exact hIleQ
                · simpa [hQcard] using hIcard
              subst hIP
              subst hIQ
              simp at hxne hyne ⊢
          | inr b =>
            rcases b with ⟨Q, y⟩
            rcases y with ⟨y, hyne⟩
            rcases y with ⟨gy, hgyQ⟩
            simp [f] at hab
            subst hab
            let I : Subgroup G := P ⊓ Q
            have hIleP : I ≤ P := inf_le_left
            have hIleQ : I ≤ Q := inf_le_right
            have hgI : (gx : G) ∈ I := ⟨hgxP, by simpa using hgyQ⟩
            have hIdiv17 : Fintype.card I ∣ 17 := by
              exact (Subgroup.card_dvd_card (H := I) (G := P))
            have hIdiv19 : Fintype.card I ∣ 19 := by
              exact (Subgroup.card_dvd_card (H := I) (G := Q))
            have hIdiv1 : Fintype.card I ∣ 1 := by
              exact Nat.dvd_gcd hIdiv17 hIdiv19
            have hIcard1 : Fintype.card I = 1 := by
              exact Nat.dvd_one.mp (by simpa using hIdiv1)
            have hsub : Subsingleton I := by
              simpa [Fintype.card_eq_one_iff] using hIcard1
            have hgx1 : (gx : G) = 1 := by
              exact Subsingleton.elim ⟨gx, hgI⟩ ⟨1, by simp⟩
            exact hxne hgx1
        | inr a =>
          rcases a with ⟨P, x⟩
          rcases x with ⟨x, hxne⟩
          rcases x with ⟨gx, hgxP⟩
          cases b with
          | inl b =>
            rcases b with ⟨Q, y⟩
            rcases y with ⟨y, hyne⟩
            rcases y with ⟨gy, hgyQ⟩
            simp [f] at hab
            subst hab
            let I : Subgroup G := P ⊓ Q
            have hgI : (gx : G) ∈ I := ⟨hgxP, by simpa using hgyQ⟩
            have hIdiv17 : Fintype.card I ∣ 17 := by
              exact (Subgroup.card_dvd_card (H := I) (G := P))
            have hIdiv19 : Fintype.card I ∣ 19 := by
              exact (Subgroup.card_dvd_card (H := I) (G := Q))
            have hIdiv1 : Fintype.card I ∣ 1 := by
              exact Nat.dvd_gcd hIdiv17 hIdiv19
            have hIcard1 : Fintype.card I = 1 := by
              exact Nat.dvd_one.mp (by simpa using hIdiv1)
            have hsub : Subsingleton I := by
              simpa [Fintype.card_eq_one_iff] using hIcard1
            have hgx1 : (gx : G) = 1 := by
              exact Subsingleton.elim ⟨gx, hgI⟩ ⟨1, by simp⟩
            exact hxne hgx1
          | inr b =>
            rcases b with ⟨Q, y⟩
            rcases y with ⟨y, hyne⟩
            rcases y with ⟨gy, hgyQ⟩
            simp [f] at hab
            subst hab
            let I : Subgroup G := P ⊓ Q
            have hIleP : I ≤ P := inf_le_left
            have hIleQ : I ≤ Q := inf_le_right
            have hgI : (gx : G) ∈ I := ⟨hgxP, by simpa using hgyQ⟩
            have hPcard : Fintype.card (P : Type*) = 17 := by
              simpa [hG] using P.card_eq
            have hQcard : Fintype.card (Q : Type*) = 19 := by
              simpa [hG] using Q.card_eq
            have hIdiv : Fintype.card I ∣ 17 := by
              exact (Subgroup.card_dvd_card (H := I) (G := P))
            have hIcard : Fintype.card I = 17 := by
              rcases h17p.eq_one_or_self_of_dvd hIdiv with h1 | h17
              · exfalso
                have hIdiv19 : Fintype.card I ∣ 19 := by
                  exact (Subgroup.card_dvd_card (H := I) (G := Q))
                have hIdiv1 : Fintype.card I ∣ 1 := by
                  exact Nat.dvd_gcd hIdiv hIdiv19
                have hIcard1 : Fintype.card I = 1 := by
                  exact Nat.dvd_one.mp (by simpa using hIdiv1)
                have hsub : Subsingleton I := by
                  simpa [Fintype.card_eq_one_iff] using hIcard1
                exact hxne (by
                  exact Subsingleton.elim ⟨gx, hgI⟩ ⟨1, by simp⟩)
              · exact h17
            have hIP : I = P := by
              apply Subgroup.eq_of_le_of_card_eq
              · exact hIleP
              · simpa [hPcard] using hIcard
            have hIQ : I = Q := by
              apply Subgroup.eq_of_le_of_card_eq
              · exact hIleQ
              · simpa [hQcard] using hIcard
            have hPQ : (P : Subgroup G) = Q := by
              calc
                P = I := by simpa [hIP] using rfl
                _ = Q := hIQ
            subst hPQ
            simp at hxne hyne ⊢
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
      omega
