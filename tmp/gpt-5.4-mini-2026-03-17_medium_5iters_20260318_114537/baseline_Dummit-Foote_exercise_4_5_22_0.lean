import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_22 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 132) : ¬ IsSimpleGroup G := by
  classical
  have h11div : Nat.card (Sylow 11 G) ∣ 132 := by
    simpa [hG] using (Sylow.card_sylow_dvd_card (p := 11) (G := G))
  have h11mod : Nat.card (Sylow 11 G) ≡ 1 [MOD 11] := by
    simpa using (Sylow.card_sylow_modEq_one (p := 11) (G := G))
  have h11cases : Nat.card (Sylow 11 G) = 1 ∨ Nat.card (Sylow 11 G) = 12 := by
    omega
  rcases h11cases with h11 | h11
  · have : IsSimpleGroup G := by infer_instance
    have hnorm : (Classical.choice (Sylow.nonempty (p := 11) (G := G))).subgroup.Normal := by
      simpa [h11] using (Sylow.normal_of_unique (p := 11) (G := G))
    exact False.elim (by
      have h := this.eq_bot_or_eq_top (Classical.choice (Sylow.nonempty (p := 11) (G := G))).subgroup
      rcases h with hbot | htop
      · have hcard : Nat.card (Classical.choice (Sylow.nonempty (p := 11) (G := G)).subgroup) = 1 := by
          simpa [hbot] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
        have hmul : 11 ∣ 1 := by
          simpa [hcard] using (Classical.choice (Sylow.nonempty (p := 11) (G := G))).card_dvd_card
        omega
      · have hcard : Nat.card G = 1 := by
          simpa [htop, hG] using (show Nat.card (⊤ : Subgroup G) = Nat.card G by rfl)
        omega)
  · have h3div : Nat.card (Sylow 3 G) ∣ 132 := by
      simpa [hG] using (Sylow.card_sylow_dvd_card (p := 3) (G := G))
    have h3mod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := by
      simpa using (Sylow.card_sylow_modEq_one (p := 3) (G := G))
    have h3cases : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 ∨ Nat.card (Sylow 3 G) = 22 := by
      omega
    rcases h3cases with h3 | h3 | h3
    · have : IsSimpleGroup G := by infer_instance
      have hnorm : (Classical.choice (Sylow.nonempty (p := 3) (G := G))).subgroup.Normal := by
        simpa [h3] using (Sylow.normal_of_unique (p := 3) (G := G))
      exact False.elim (by
        have h := this.eq_bot_or_eq_top (Classical.choice (Sylow.nonempty (p := 3) (G := G))).subgroup
        rcases h with hbot | htop
        · have hcard : Nat.card (Classical.choice (Sylow.nonempty (p := 3) (G := G)).subgroup) = 1 := by
            simpa [hbot] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
          have hmul : 3 ∣ 1 := by
            simpa [hcard] using (Classical.choice (Sylow.nonempty (p := 3) (G := G))).card_dvd_card
          omega
        · have hcard : Nat.card G = 1 := by
            simpa [htop, hG] using (show Nat.card (⊤ : Subgroup G) = Nat.card G by rfl)
          omega)
    · -- n₃ = 4
      let φ : G →* Equiv.Perm (Sylow 3 G) := MulAction.toPermHom G (Sylow 3 G)
      have hker_norm : (φ.ker).Normal := by infer_instance
      have hnontriv : φ.range.Nontrivial := by
        classical
        have hcard3 : Nat.card (Sylow 3 G) = 4 := h3
        have htr : Transitive G (Sylow 3 G) := by
          simpa using (Sylow.transitive (p := 3) (G := G))
        obtain ⟨P, Q, hPQ⟩ := exists_ne (Sylow 3 G)
        rcases htr P Q with ⟨g, hg⟩
        refine ⟨φ g, ?_⟩
        intro h
        have : g • P = P := by
          simpa [φ] using congrArg (fun e : Equiv.Perm (Sylow 3 G) => e P) h
        exact hPQ (by simpa [hg] using this)
      have hcardperm : Nat.card (Equiv.Perm (Sylow 3 G)) = 24 := by
        simp [h3]
      have hrange_dvd : Nat.card φ.range ∣ 24 := by
        have : Nat.card φ.range ∣ Nat.card (Equiv.Perm (Sylow 3 G)) := by
          exact Subgroup.card_dvd_card
        simpa [hcardperm] using this
      have hker_card : Nat.card φ.ker = 132 / Nat.card φ.range := by
        have := Fintype.card_range_mul_card_ker φ
        omega
      have hrange_pos : 1 < Nat.card φ.range := by
        have h : Nat.card φ.range ≠ 1 := by
          intro h1
          have : Subsingleton φ.range := by
            simpa [Nat.card_eq_one_iff] using h1
          exact hnontriv.false
        omega
      have hrange_le : Nat.card φ.range ≤ 24 := by
        omega
      have hker_gt1 : 1 < Nat.card φ.ker := by
        have h : Nat.card φ.range ≤ 24 := hrange_le
        omega
      have hker_lt : Nat.card φ.ker < 132 := by
        have h : 1 < Nat.card φ.range := hrange_pos
        omega
      have hnotbot : φ.ker ≠ ⊥ := by
        intro hbot
        have : Nat.card φ.ker = 1 := by simpa [hbot] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
        omega
      have hnottop : φ.ker ≠ ⊤ := by
        intro htop
        have : Nat.card φ.ker = 132 := by simpa [htop, hG] using (show Nat.card (⊤ : Subgroup G) = Nat.card G by rfl)
        omega
      exact False.elim (by
        have h := this.eq_bot_or_eq_top φ.ker
        rcases h with hbot | htop
        · exact hnotbot hbot
        · exact hnottop htop)
    · -- n₃ = 22
      have h3fib : ∀ Q : Sylow 3 G, Nat.card {x : Q // x ≠ (1 : Q)} = 2 := by
        intro Q
        simpa using (Fintype.card_subtype_neq (1 : Q))
      have h11fib : ∀ P : Sylow 11 G, Nat.card {x : P // x ≠ (1 : P)} = 10 := by
        intro P
        simpa using (Fintype.card_subtype_neq (1 : P))
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
        · -- 11 / 11
          have hsame : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          have hcl : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (u_1.1 : Sylow 11 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl' : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (v_1.1 : Sylow 11 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [hsame] using v_1.2.1.2
          have hcardcl : Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) = 11 := by
            let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
            haveI : Nontrivial H := by
              refine ⟨⟨u_1.2.1, subset_closure (by simp)⟩, 1, ?_⟩
              intro h
              exact u_1.2.2 (Subtype.ext h)
            have hgt : 1 < Nat.card H := Fintype.one_lt_card
            have hdiv : Nat.card H ∣ 11 := by
              simpa [h11] using (Subgroup.card_dvd_card hcl)
            omega
          have hcardu : Nat.card (u_1.1 : Sylow 11 G) = 11 := by simpa using (u_1.1).card
          have hcardv : Nat.card (v_1.1 : Sylow 11 G) = 11 := by simpa using (v_1.1).card
          have hu : Subgroup.closure ({(u_1.2.1 : G)} : Set G) = (u_1.1 : Sylow 11 G) := by
            apply Subgroup.eq_of_le_of_card_eq hcl
            simpa [hcardu] using hcardcl
          have hv : Subgroup.closure ({(u_1.2.1 : G)} : Set G) = (v_1.1 : Sylow 11 G) := by
            apply Subgroup.eq_of_le_of_card_eq hcl'
            simpa [hcardv] using hcardcl
          simpa [hu, hv] using congrArg Subtype.val rfl
        · -- 11 / 3 impossible
          have hcl1 : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (u_1.1 : Sylow 11 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl2 : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (v_1.1 : Sylow 3 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [huv] using v_1.2.1.2
          have hcard1 : Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) ∣ 11 := by
            simpa [h11] using (Subgroup.card_dvd_card hcl1)
          have hcard2 : Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) ∣ 3 := by
            simpa [h3] using (Subgroup.card_dvd_card hcl2)
          have hgt : 1 < Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) := by
            let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
            haveI : Nontrivial H := by
              refine ⟨⟨u_1.2.1, subset_closure (by simp)⟩, 1, ?_⟩
              intro h
              exact u_1.2.2 (Subtype.ext h)
            exact Fintype.one_lt_card
          omega
        · -- 3 / 11 impossible
          have hcl1 : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (u_1.1 : Sylow 3 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl2 : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (v_1.1 : Sylow 11 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [huv] using v_1.2.1.2
          have hcard1 : Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) ∣ 3 := by
            simpa [h3] using (Subgroup.card_dvd_card hcl1)
          have hcard2 : Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) ∣ 11 := by
            simpa [h11] using (Subgroup.card_dvd_card hcl2)
          have hgt : 1 < Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) := by
            let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
            haveI : Nontrivial H := by
              refine ⟨⟨u_1.2.1, subset_closure (by simp)⟩, 1, ?_⟩
              intro h
              exact u_1.2.2 (Subtype.ext h)
            exact Fintype.one_lt_card
          omega
        · -- 3 / 3
          have hsame : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          have hcl : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (u_1.1 : Sylow 3 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa using u_1.2.1.2
          have hcl' : Subgroup.closure ({(u_1.2.1 : G)} : Set G) ≤ (v_1.1 : Sylow 3 G) := by
            refine Subgroup.closure_le.2 ?_
            intro x hx
            rcases hx with rfl
            simpa [hsame] using v_1.2.1.2
          have hcardcl : Nat.card (Subgroup.closure ({(u_1.2.1 : G)} : Set G)) = 3 := by
            let H := Subgroup.closure ({(u_1.2.1 : G)} : Set G)
            haveI : Nontrivial H := by
              refine ⟨⟨u_1.2.1, subset_closure (by simp)⟩, 1, ?_⟩
              intro h
              exact u_1.2.2 (Subtype.ext h)
            have hgt : 1 < Nat.card H := Fintype.one_lt_card
            have hdiv : Nat.card H ∣ 3 := by
              simpa [h3] using (Subgroup.card_dvd_card hcl)
            omega
          have hcardu : Nat.card (u_1.1 : Sylow 3 G) = 3 := by simpa using (u_1.1).card
          have hcardv : Nat.card (v_1.1 : Sylow 3 G) = 3 := by simpa using (v_1.1).card
          have hu : Subgroup.closure ({(u_1.2.1 : G)} : Set G) = (u_1.1 : Sylow 3 G) := by
            apply Subgroup.eq_of_le_of_card_eq hcl
            simpa [hcardu] using hcardcl
          have hv : Subgroup.closure ({(u_1.2.1 : G)} : Set G) = (v_1.1 : Sylow 3 G) := by
            apply Subgroup.eq_of_le_of_card_eq hcl'
            simpa [hcardv] using hcardcl
          simpa [hu, hv] using congrArg Subtype.val rfl
      have hle : Nat.card D ≤ 132 := by
        exact Fintype.card_le_card_of_injective f hinj
      omega
