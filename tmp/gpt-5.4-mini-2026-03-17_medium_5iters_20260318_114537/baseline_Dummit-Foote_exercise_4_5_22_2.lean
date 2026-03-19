import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_22 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 132) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h11div : Fintype.card (Sylow 11 G) ∣ Fintype.card G := by
    simpa [hG] using (Fintype.card_sylow_dvd_card (p := 11) (G := G))
  have h11mod : Fintype.card (Sylow 11 G) ≡ 1 [MOD 11] := by
    simpa using (Fintype.card_sylow_modEq_one (p := 11) (G := G))
  have h11cases : Fintype.card (Sylow 11 G) = 1 ∨ Fintype.card (Sylow 11 G) = 12 := by
    have hle : Fintype.card (Sylow 11 G) ≤ 12 := by
      have := Nat.le_of_dvd (by decide : 0 < 132) (by
        simpa [hG] using h11div)
      omega
    interval_cases Fintype.card (Sylow 11 G) <;> norm_num at h11mod
  rcases h11cases with h11 | h11
  · let P : Sylow 11 G := Classical.choice (Sylow.nonempty (p := 11) (G := G))
    have hsub : Subsingleton (Sylow 11 G) := by
      exact (Fintype.card_eq_one_iff).mp (by simpa using h11)
    have hPuniq : ∀ Q : Sylow 11 G, Q = P := by
      intro Q
      exact Subsingleton.elim _ _
    have hPnorm : (P : Subgroup G).Normal := by
      rw [Subgroup.normal_iff]
      intro g
      exact hPuniq (g • P)
    have hbot_or_top : (P : Subgroup G) = ⊥ ∨ (P : Subgroup G) = ⊤ := by
      exact hsimple.1 (P : Subgroup G) hPnorm
    rcases hbot_or_top with hbot | htop
    · have hcardP : Nat.card (P : Subgroup G) = 11 := by
        simpa using (P.card)
      have hcardBot : Nat.card (P : Subgroup G) = 1 := by
        simpa [hbot] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
      omega
    · have hcardP : Nat.card (P : Subgroup G) = 11 := by
        simpa using (P.card)
      have hcardG : Nat.card G = 11 := by
        simpa [htop] using hcardP
      omega
  · have h3div : Fintype.card (Sylow 3 G) ∣ Fintype.card G := by
      simpa [hG] using (Fintype.card_sylow_dvd_card (p := 3) (G := G))
    have h3mod : Fintype.card (Sylow 3 G) ≡ 1 [MOD 3] := by
      simpa using (Fintype.card_sylow_modEq_one (p := 3) (G := G))
    have h3cases : Fintype.card (Sylow 3 G) = 1 ∨ Fintype.card (Sylow 3 G) = 4 ∨ Fintype.card (Sylow 3 G) = 22 := by
      have hle : Fintype.card (Sylow 3 G) ≤ 44 := by
        have := Nat.le_of_dvd (by decide : 0 < 132) (by
          simpa [hG] using h3div)
        omega
      interval_cases Fintype.card (Sylow 3 G) <;> norm_num at h3mod
    rcases h3cases with h3 | h3 | h3
    · let P : Sylow 3 G := Classical.choice (Sylow.nonempty (p := 3) (G := G))
      have hsub : Subsingleton (Sylow 3 G) := by
        exact (Fintype.card_eq_one_iff).mp (by simpa using h3)
      have hPuniq : ∀ Q : Sylow 3 G, Q = P := by
        intro Q
        exact Subsingleton.elim _ _
      have hPnorm : (P : Subgroup G).Normal := by
        rw [Subgroup.normal_iff]
        intro g
        exact hPuniq (g • P)
      have hbot_or_top : (P : Subgroup G) = ⊥ ∨ (P : Subgroup G) = ⊤ := by
        exact hsimple.1 (P : Subgroup G) hPnorm
      rcases hbot_or_top with hbot | htop
      · have hcardP : Nat.card (P : Subgroup G) = 3 := by
          simpa using (P.card)
        have hcardBot : Nat.card (P : Subgroup G) = 1 := by
          simpa [hbot] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
        omega
      · have hcardP : Nat.card (P : Subgroup G) = 3 := by
          simpa using (P.card)
        have hcardG : Nat.card G = 3 := by
          simpa [htop] using hcardP
        omega
    · -- n3 = 4
      let φ : G →* Equiv.Perm (Sylow 3 G) := MulAction.toPermHom G (Sylow 3 G)
      have hnontriv : ∃ g : G, φ g ≠ 1 := by
        obtain ⟨P, Q, hPQ⟩ := exists_ne (Sylow 3 G)
        rcases (Sylow.transitive (p := 3) (G := G)) P Q with ⟨g, hg⟩
        refine ⟨g, ?_⟩
        intro hg1
        have hfix : g • P = P := by
          simpa [φ] using congrArg (fun e : Equiv.Perm (Sylow 3 G) => e P) hg1
        exact hPQ (by simpa [hg] using hfix)
      have hkerNotTop : φ.ker ≠ ⊤ := by
        intro htop
        rcases hnontriv with ⟨g, hg⟩
        have hgker : g ∈ φ.ker := by
          simpa [htop]
        have hg1 : φ g = 1 := by
          simpa using hgker
        exact hg hg1
      have hkerNorm : (φ.ker).Normal := by infer_instance
      have hkerBotOrTop : φ.ker = ⊥ ∨ φ.ker = ⊤ := by
        exact hsimple.1 φ.ker hkerNorm
      rcases hkerBotOrTop with hbot | htop
      · have hcardKer : Nat.card φ.ker = 1 := by
          simpa [hbot]
        have hcardRange : Nat.card φ.range = 132 := by
          have hprod := Fintype.card_range_mul_card_ker φ
          omega
        have hrangeDvd : Nat.card φ.range ∣ 24 := by
          have := Subgroup.card_dvd_card (φ.range : Subgroup (Equiv.Perm (Sylow 3 G)))
          simpa [h3] using this
        have hrangeLe : Nat.card φ.range ≤ 24 := Nat.le_of_dvd (by decide) hrangeDvd
        omega
      · exact False.elim (hkerNotTop htop)
    · -- n3 = 22
      let D11 := Σ P : Sylow 11 G, {x : P // x ≠ (1 : P)}
      let D3 := Σ Q : Sylow 3 G, {x : Q // x ≠ (1 : Q)}
      let D := D11 ⊕ D3
      have h11fib : ∀ P : Sylow 11 G, Nat.card {x : P // x ≠ (1 : P)} = 10 := by
        intro P
        simpa using (Fintype.card_subtype_neq (1 : P))
      have h3fib : ∀ Q : Sylow 3 G, Nat.card {x : Q // x ≠ (1 : Q)} = 2 := by
        intro Q
        simpa using (Fintype.card_subtype_neq (1 : Q))
      have hD11 : Nat.card D11 = 120 := by
        rw [D11, Fintype.card_sigma]
        simp [h11, h11fib]
      have hD3 : Nat.card D3 = 44 := by
        rw [D3, Fintype.card_sigma]
        simp [h3, h3fib]
      have hD : Nat.card D = 164 := by
        rw [D, Fintype.card_sum]
        omega
      let f : D → G := fun z =>
        match z with
        | Sum.inl a => a.2.1
        | Sum.inr b => b.2.1
      have hinj : Function.Injective f := by
        intro u v huv
        cases u <;> cases v <;> simp [f] at huv
        · -- 11 / 11
          have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
          have hcl : H ≤ (u_1.1 : Sylow 11 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl' : H ≤ (v_1.1 : Sylow 11 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [hEq] using v_1.2.1.2
          have hnontriv : Nontrivial H := by
            refine ⟨⟨u_1.2.1, subset_closure (by simp [H])⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hgt : 1 < Nat.card H := Fintype.one_lt_card
          have hcardP : Nat.card (u_1.1 : Subgroup G) = 11 := by
            simpa using (u_1.1).card
          have hdiv : Nat.card H ∣ 11 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 11 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h11'
          · omega
          · have hcardH : Nat.card H = 11 := h11'
            have hu : H = (u_1.1 : Subgroup G) := by
              apply Subgroup.eq_of_le_of_card_eq hcl
              simpa [hcardP] using hcardH
            have hv : H = (v_1.1 : Subgroup G) := by
              apply Subgroup.eq_of_le_of_card_eq hcl'
              simpa [hcardP] using hcardH
            have hsub : (u_1.1 : Sylow 11 G) = v_1.1 := by
              calc
                (u_1.1 : Sylow 11 G) = H := by symm; exact hu
                _ = v_1.1 := by exact hv
            cases hsub
            exact Subtype.ext hEq
        · -- 11 / 3
          have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
          have hcl : H ≤ (u_1.1 : Sylow 11 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl' : H ≤ (v_1.1 : Sylow 3 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [hEq] using v_1.2.1.2
          have hnontriv : Nontrivial H := by
            refine ⟨⟨u_1.2.1, subset_closure (by simp [H])⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hgt : 1 < Nat.card H := Fintype.one_lt_card
          have hcardP : Nat.card (u_1.1 : Subgroup G) = 11 := by
            simpa using (u_1.1).card
          have hcardQ : Nat.card (v_1.1 : Subgroup G) = 3 := by
            simpa using (v_1.1).card
          have hdiv : Nat.card H ∣ 11 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 11 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h11'
          · omega
          · have hcardH : Nat.card H = 11 := h11'
            have hdiv3 : Nat.card H ∣ 3 := by
              simpa [hcardQ] using (Subgroup.card_dvd_card hcl')
            omega
        · -- 3 / 11
          have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
          have hcl : H ≤ (u_1.1 : Sylow 3 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl' : H ≤ (v_1.1 : Sylow 11 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [hEq] using v_1.2.1.2
          have hnontriv : Nontrivial H := by
            refine ⟨⟨u_1.2.1, subset_closure (by simp [H])⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hgt : 1 < Nat.card H := Fintype.one_lt_card
          have hcardP : Nat.card (u_1.1 : Subgroup G) = 3 := by
            simpa using (u_1.1).card
          have hcardQ : Nat.card (v_1.1 : Subgroup G) = 11 := by
            simpa using (v_1.1).card
          have hdiv : Nat.card H ∣ 3 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 3 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h3'
          · omega
          · have hcardH : Nat.card H = 3 := h3'
            have hdiv11 : Nat.card H ∣ 11 := by
              simpa [hcardQ] using (Subgroup.card_dvd_card hcl')
            omega
        · -- 3 / 3
          have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
          have hcl : H ≤ (u_1.1 : Sylow 3 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl' : H ≤ (v_1.1 : Sylow 3 G) := by
            dsimp [H]
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [hEq] using v_1.2.1.2
          have hnontriv : Nontrivial H := by
            refine ⟨⟨u_1.2.1, subset_closure (by simp [H])⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hgt : 1 < Nat.card H := Fintype.one_lt_card
          have hcardP : Nat.card (u_1.1 : Subgroup G) = 3 := by
            simpa using (u_1.1).card
          have hdiv : Nat.card H ∣ 3 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 3 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h3'
          · omega
          · have hcardH : Nat.card H = 3 := h3'
            have hu : H = (u_1.1 : Subgroup G) := by
              apply Subgroup.eq_of_le_of_card_eq hcl
              simpa [hcardP] using hcardH
            have hv : H = (v_1.1 : Subgroup G) := by
              apply Subgroup.eq_of_le_of_card_eq hcl'
              simpa [hcardP] using hcardH
            have hsub : (u_1.1 : Sylow 3 G) = v_1.1 := by
              calc
                (u_1.1 : Sylow 3 G) = H := by symm; exact hu
                _ = v_1.1 := by exact hv
            cases hsub
            exact Subtype.ext hEq
      have hle : Nat.card D ≤ 132 := by
        exact Fintype.card_le_card_of_injective f hinj
      omega
