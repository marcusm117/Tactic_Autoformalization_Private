import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_22 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 132) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI := hsimple
  have h11div : Nat.card (Sylow 11 G) ∣ 132 := by
    simpa [hG] using card_sylow_dvd_card (p := 11) (G := G)
  have h11mod : Nat.card (Sylow 11 G) ≡ 1 [MOD 11] := by
    simpa using card_sylow_modEq_one (p := 11) (G := G)
  have h11cases : Nat.card (Sylow 11 G) = 1 ∨ Nat.card (Sylow 11 G) = 12 := by
    have hle : Nat.card (Sylow 11 G) ≤ 12 := by
      have := Nat.le_of_dvd (by decide : 0 < 132) h11div
      omega
    interval_cases Nat.card (Sylow 11 G) <;> norm_num at h11mod
  rcases h11cases with h11 | h11
  · obtain ⟨P, hP⟩ := (Fintype.card_eq_one_iff.mp (by simpa using h11))
    have hPnorm : (P : Subgroup G).Normal := by
      constructor
      intro g x hx
      have hgp : g • P = P := by
        exact hP (g • P)
      simpa [hgp] using hx
    have hbot_or_top : (P : Subgroup G) = ⊥ ∨ (P : Subgroup G) = ⊤ := by
      exact IsSimpleGroup.eq_bot_or_eq_top (G := G) (H := (P : Subgroup G))
    rcases hbot_or_top with hbot | htop
    · have hcardP : Nat.card (P : Subgroup G) = 11 := by
        simpa using (show Nat.card (P : Subgroup G) = 11 by
          simpa using (show Nat.card (P : Subgroup G) = Nat.card (P : Subgroup G) from rfl))
      have hcardBot : Nat.card (P : Subgroup G) = 1 := by
        simpa [hbot] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
      omega
    · have hcardP : Nat.card (P : Subgroup G) = 11 := by
        simpa using (show Nat.card (P : Subgroup G) = 11 by
          simpa using (show Nat.card (P : Subgroup G) = Nat.card (P : Subgroup G) from rfl))
      have hcardG : Nat.card G = 11 := by
        simpa [htop] using hcardP
      omega
  · have h3div : Nat.card (Sylow 3 G) ∣ 132 := by
      simpa [hG] using card_sylow_dvd_card (p := 3) (G := G)
    have h3mod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := by
      simpa using card_sylow_modEq_one (p := 3) (G := G)
    have h3cases : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 ∨ Nat.card (Sylow 3 G) = 22 := by
      have hle : Nat.card (Sylow 3 G) ≤ 44 := by
        have := Nat.le_of_dvd (by decide : 0 < 132) h3div
        omega
      interval_cases Nat.card (Sylow 3 G) <;> norm_num at h3mod
    rcases h3cases with h3 | h3 | h3
    · obtain ⟨P, hP⟩ := (Fintype.card_eq_one_iff.mp (by simpa using h3))
      have hPnorm : (P : Subgroup G).Normal := by
        constructor
        intro g x hx
        have hgp : g • P = P := by
          exact hP (g • P)
        simpa [hgp] using hx
      have hbot_or_top : (P : Subgroup G) = ⊥ ∨ (P : Subgroup G) = ⊤ := by
        exact IsSimpleGroup.eq_bot_or_eq_top (G := G) (H := (P : Subgroup G))
      rcases hbot_or_top with hbot | htop
      · have hcardP : Nat.card (P : Subgroup G) = 3 := by
          simpa using (show Nat.card (P : Subgroup G) = 3 by
            simpa using (show Nat.card (P : Subgroup G) = Nat.card (P : Subgroup G) from rfl))
        have hcardBot : Nat.card (P : Subgroup G) = 1 := by
          simpa [hbot] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
        omega
      · have hcardP : Nat.card (P : Subgroup G) = 3 := by
          simpa using (show Nat.card (P : Subgroup G) = 3 by
            simpa using (show Nat.card (P : Subgroup G) = Nat.card (P : Subgroup G) from rfl))
        have hcardG : Nat.card G = 3 := by
          simpa [htop] using hcardP
        omega
    · -- n₃ = 4
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
      have hD3 : Nat.card D3 = 8 := by
        rw [D3, Fintype.card_sigma]
        simp [h3, h3fib]
      have hD : Nat.card D = 128 := by
        rw [D, Fintype.card_sum]
        omega
      let f : D → G := fun z =>
        match z with
        | Sum.inl a => a.2.1
        | Sum.inr b => b.2.1
      have hinj : Function.Injective f := by
        intro u v huv
        cases u <;> cases v <;> simp [f] at huv
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 11 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
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
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 11 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
          have hcardQ : Nat.card (v_1.1 : Subgroup G) = 3 := by
            simpa using (show Nat.card (v_1.1 : Subgroup G) = 3 by
              simpa using (show Nat.card (v_1.1 : Subgroup G) = Nat.card (v_1.1 : Subgroup G) from rfl))
          have hdiv : Nat.card H ∣ 11 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 11 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h11'
          · omega
          · have hcardH : Nat.card H = 11 := h11'
            have hdiv3 : Nat.card H ∣ 3 := by
              simpa [hcardQ] using (Subgroup.card_dvd_card hcl')
            omega
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 3 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
          have hcardQ : Nat.card (v_1.1 : Subgroup G) = 11 := by
            simpa using (show Nat.card (v_1.1 : Subgroup G) = 11 by
              simpa using (show Nat.card (v_1.1 : Subgroup G) = Nat.card (v_1.1 : Subgroup G) from rfl))
          have hdiv : Nat.card H ∣ 3 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 3 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h3'
          · omega
          · have hcardH : Nat.card H = 3 := h3'
            have hdiv11 : Nat.card H ∣ 11 := by
              simpa [hcardQ] using (Subgroup.card_dvd_card hcl')
            omega
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 3 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
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
    · -- n₃ = 22
      have h11fib : ∀ P : Sylow 11 G, Nat.card {x : P // x ≠ (1 : P)} = 10 := by
        intro P
        simpa using (Fintype.card_subtype_neq (1 : P))
      have h3fib : ∀ Q : Sylow 3 G, Nat.card {x : Q // x ≠ (1 : Q)} = 2 := by
        intro Q
        simpa using (Fintype.card_subtype_neq (1 : Q))
      let D11 := Σ P : Sylow 11 G, {x : P // x ≠ (1 : P)}
      let D3 := Σ Q : Sylow 3 G, {x : Q // x ≠ (1 : Q)}
      let D := D11 ⊕ D3
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
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 11 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
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
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 11 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
          have hcardQ : Nat.card (v_1.1 : Subgroup G) = 3 := by
            simpa using (show Nat.card (v_1.1 : Subgroup G) = 3 by
              simpa using (show Nat.card (v_1.1 : Subgroup G) = Nat.card (v_1.1 : Subgroup G) from rfl))
          have hdiv : Nat.card H ∣ 11 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 11 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h11'
          · omega
          · have hcardH : Nat.card H = 11 := h11'
            have hdiv3 : Nat.card H ∣ 3 := by
              simpa [hcardQ] using (Subgroup.card_dvd_card hcl')
            omega
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 3 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
          have hcardQ : Nat.card (v_1.1 : Subgroup G) = 11 := by
            simpa using (show Nat.card (v_1.1 : Subgroup G) = 11 by
              simpa using (show Nat.card (v_1.1 : Subgroup G) = Nat.card (v_1.1 : Subgroup G) from rfl))
          have hdiv : Nat.card H ∣ 3 := by
            simpa [hcardP] using (Subgroup.card_dvd_card hcl)
          have hprime : Nat.Prime 3 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h3'
          · omega
          · have hcardH : Nat.card H = 3 := h3'
            have hdiv11 : Nat.card H ∣ 11 := by
              simpa [hcardQ] using (Subgroup.card_dvd_card hcl')
            omega
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
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
            simpa using (show Nat.card (u_1.1 : Subgroup G) = 3 by
              simpa using (show Nat.card (u_1.1 : Subgroup G) = Nat.card (u_1.1 : Subgroup G) from rfl))
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
