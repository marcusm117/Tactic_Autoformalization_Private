import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_22 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 132) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h11div : Nat.card (Sylow 11 G) ∣ 132 := by
    simpa [hG] using (Nat.card_sylow_dvd_card (p := 11) (G := G))
  have h11mod : Nat.card (Sylow 11 G) ≡ 1 [MOD 11] := by
    simpa using (Nat.card_sylow_modEq_one (p := 11) (G := G))
  have h11cop : Nat.Coprime (Nat.card (Sylow 11 G)) 11 := h11mod.coprime
  have h11div12 : Nat.card (Sylow 11 G) ∣ 12 := by
    have hmul : Nat.card (Sylow 11 G) ∣ 11 * 12 := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h11div
    exact h11cop.dvd_of_dvd_mul_right hmul
  have h11cases : Nat.card (Sylow 11 G) = 1 ∨ Nat.card (Sylow 11 G) = 12 := by
    have hle : Nat.card (Sylow 11 G) ≤ 12 := Nat.le_of_dvd (by decide) h11div12
    interval_cases Nat.card (Sylow 11 G) <;> norm_num at h11mod
  rcases h11cases with h11 | h11
  · let P : Sylow 11 G := Classical.choice (Sylow.nonempty (p := 11) (G := G))
    have hPsubs : Subsingleton (Sylow 11 G) := by
      have hcard : Nat.card (Sylow 11 G) = 1 := h11
      exact (Fintype.card_eq_one_iff).mp hcard
    have hPuniq : ∀ Q : Sylow 11 G, Q = P := by
      intro Q
      exact Subsingleton.elim _ _
    have hPnorm : (P : Subgroup G).Normal := by
      constructor
      intro g x hx
      have hx' : g * x * g⁻¹ ∈ (g • P : Sylow 11 G) := by
        simpa using hx
      simpa [hPuniq (g • P)] using hx'
    have hcases := hsimple (P : Subgroup G) hPnorm
    rcases hcases with hbot | htop
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
  · haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have h3div : Nat.card (Sylow 3 G) ∣ 132 := by
      simpa [hG] using (Nat.card_sylow_dvd_card (p := 3) (G := G))
    have h3mod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := by
      simpa using (Nat.card_sylow_modEq_one (p := 3) (G := G))
    have h3cop : Nat.Coprime (Nat.card (Sylow 3 G)) 3 := h3mod.coprime
    have h3div44 : Nat.card (Sylow 3 G) ∣ 44 := by
      have hmul : Nat.card (Sylow 3 G) ∣ 3 * 44 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h3div
      exact h3cop.dvd_of_dvd_mul_right hmul
    have h3cases : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 ∨ Nat.card (Sylow 3 G) = 22 := by
      have hle : Nat.card (Sylow 3 G) ≤ 44 := Nat.le_of_dvd (by decide) h3div44
      interval_cases Nat.card (Sylow 3 G) <;> norm_num at h3mod
    rcases h3cases with h3 | h3 | h3
    · let P : Sylow 3 G := Classical.choice (Sylow.nonempty (p := 3) (G := G))
      have hPsubs : Subsingleton (Sylow 3 G) := by
        have hcard : Nat.card (Sylow 3 G) = 1 := h3
        exact (Fintype.card_eq_one_iff).mp hcard
      have hPuniq : ∀ Q : Sylow 3 G, Q = P := by
        intro Q
        exact Subsingleton.elim _ _
      have hPnorm : (P : Subgroup G).Normal := by
        constructor
        intro g x hx
        have hx' : g * x * g⁻¹ ∈ (g • P : Sylow 3 G) := by
          simpa using hx
        simpa [hPuniq (g • P)] using hx'
      have hcases := hsimple (P : Subgroup G) hPnorm
      rcases hcases with hbot | htop
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
    · -- n₃ = 4
      let φ : G →* Equiv.Perm (Sylow 3 G) := MulAction.toPermHom G (Sylow 3 G)
      have hnontriv : ∃ g : G, φ g ≠ 1 := by
        obtain ⟨P, Q, hPQ⟩ := exists_ne (Sylow 3 G)
        rcases (Sylow.transitive (p := 3) (G := G)) P Q with ⟨g, hg⟩
        refine ⟨g, ?_⟩
        intro hg1
        have hfix : g • P = P := by
          simpa [φ] using congrArg (fun e : Equiv.Perm (Sylow 3 G) => e P) hg1
        exact hPQ ((by simpa [hg] using hfix).symm)
      have hkerNotTop : φ.ker ≠ ⊤ := by
        intro htop
        rcases hnontriv with ⟨g, hg⟩
        have hgker : g ∈ φ.ker := by
          simpa [htop] using (show g ∈ (⊤ : Subgroup G) from by simp)
        have hg1 : φ g = 1 := by
          simpa using hgker
        exact hg hg1
      have hkerCases := hsimple (φ.ker) (by infer_instance)
      rcases hkerCases with hker | hker
      · have hkerCard : Nat.card φ.ker = 1 := by
          simpa [hker] using (show Nat.card (⊥ : Subgroup G) = 1 from rfl)
        have hrangeCard : Nat.card φ.range = 132 := by
          have hprod := Fintype.card_range_mul_card_ker φ
          omega
        have hrangeDvd : Nat.card φ.range ∣ 24 := by
          have := Subgroup.card_dvd_card (φ.range : Subgroup (Equiv.Perm (Sylow 3 G)))
          simpa [h3] using this
        have hrangeLe : Nat.card φ.range ≤ 24 := Nat.le_of_dvd (by decide) hrangeDvd
        omega
      · exact False.elim (hkerNotTop hker)
    · -- n₃ = 22
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
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          have hnontriv : Nontrivial (u_1.1 ⊓ v_1.1) := by
            refine ⟨⟨u_1.2.1, ⟨u_1.2.1.2, by simpa [hEq] using v_1.2.1.2⟩⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hdiv : Nat.card (u_1.1 ⊓ v_1.1) ∣ 11 := by
            simpa [h11] using (Subgroup.card_dvd_card (show u_1.1 ⊓ v_1.1 ≤ u_1.1 from inf_le_left))
          have hprime : Nat.Prime 11 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h11'
          · have hgt : 1 < Nat.card (u_1.1 ⊓ v_1.1) := Fintype.one_lt_card
            omega
          · have huCard : Nat.card (u_1.1 ⊓ v_1.1) = Nat.card (u_1.1) := by
              simpa [h11'] using (show Nat.card (u_1.1) = 11 by simpa using (u_1.1).card)
            have hu : u_1.1 ⊓ v_1.1 = u_1.1 := by
              exact Subgroup.eq_of_le_of_card_eq (inf_le_left) huCard
            have hvCard : Nat.card (u_1.1 ⊓ v_1.1) = Nat.card (v_1.1) := by
              simpa [h11'] using (show Nat.card (v_1.1) = 11 by simpa using (v_1.1).card)
            have hv : u_1.1 ⊓ v_1.1 = v_1.1 := by
              exact Subgroup.eq_of_le_of_card_eq (inf_le_right) hvCard
            have hsub : u_1.1 = v_1.1 := by
              calc
                u_1.1 = u_1.1 ⊓ v_1.1 := by symm; exact hu
                _ = v_1.1 := hv
            cases hsub
            exact Subtype.ext hEq
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          have hnontriv : Nontrivial (u_1.1 ⊓ v_1.1) := by
            refine ⟨⟨u_1.2.1, ⟨u_1.2.1.2, by simpa [hEq] using v_1.2.1.2⟩⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hdiv11 : Nat.card (u_1.1 ⊓ v_1.1) ∣ 11 := by
            simpa [h11] using (Subgroup.card_dvd_card (show u_1.1 ⊓ v_1.1 ≤ u_1.1 from inf_le_left))
          have hdiv3 : Nat.card (u_1.1 ⊓ v_1.1) ∣ 3 := by
            simpa [h3] using (Subgroup.card_dvd_card (show u_1.1 ⊓ v_1.1 ≤ v_1.1 from inf_le_right))
          have hdiv1 : Nat.card (u_1.1 ⊓ v_1.1) ∣ 1 := by
            exact Nat.dvd_gcd hdiv11 hdiv3
          have hgt : 1 < Nat.card (u_1.1 ⊓ v_1.1) := Fintype.one_lt_card
          have hle : Nat.card (u_1.1 ⊓ v_1.1) ≤ 1 := Nat.le_of_dvd (by decide) hdiv1
          omega
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          have hnontriv : Nontrivial (u_1.1 ⊓ v_1.1) := by
            refine ⟨⟨u_1.2.1, ⟨u_1.2.1.2, by simpa [hEq] using v_1.2.1.2⟩⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hdiv11 : Nat.card (u_1.1 ⊓ v_1.1) ∣ 3 := by
            simpa [h3] using (Subgroup.card_dvd_card (show u_1.1 ⊓ v_1.1 ≤ u_1.1 from inf_le_left))
          have hdiv3 : Nat.card (u_1.1 ⊓ v_1.1) ∣ 11 := by
            simpa [h11] using (Subgroup.card_dvd_card (show u_1.1 ⊓ v_1.1 ≤ v_1.1 from inf_le_right))
          have hdiv1 : Nat.card (u_1.1 ⊓ v_1.1) ∣ 1 := by
            exact Nat.dvd_gcd hdiv11 hdiv3
          have hgt : 1 < Nat.card (u_1.1 ⊓ v_1.1) := Fintype.one_lt_card
          have hle : Nat.card (u_1.1 ⊓ v_1.1) ≤ 1 := Nat.le_of_dvd (by decide) hdiv1
          omega
        · have hEq : (u_1.2.1 : G) = (v_1.2.1 : G) := huv
          have hnontriv : Nontrivial (u_1.1 ⊓ v_1.1) := by
            refine ⟨⟨u_1.2.1, ⟨u_1.2.1.2, by simpa [hEq] using v_1.2.1.2⟩⟩, 1, ?_⟩
            intro h
            exact u_1.2.2 (Subtype.ext h)
          have hdiv : Nat.card (u_1.1 ⊓ v_1.1) ∣ 3 := by
            simpa [h3] using (Subgroup.card_dvd_card (show u_1.1 ⊓ v_1.1 ≤ u_1.1 from inf_le_left))
          have hprime : Nat.Prime 3 := by decide
          rcases Nat.dvd_prime hprime hdiv with h1 | h3'
          · have hgt : 1 < Nat.card (u_1.1 ⊓ v_1.1) := Fintype.one_lt_card
            omega
          · have huCard : Nat.card (u_1.1 ⊓ v_1.1) = Nat.card (u_1.1) := by
              simpa [h3'] using (show Nat.card (u_1.1) = 3 by simpa using (u_1.1).card)
            have hu : u_1.1 ⊓ v_1.1 = u_1.1 := by
              exact Subgroup.eq_of_le_of_card_eq (inf_le_left) huCard
            have hvCard : Nat.card (u_1.1 ⊓ v_1.1) = Nat.card (v_1.1) := by
              simpa [h3'] using (show Nat.card (v_1.1) = 3 by simpa using (v_1.1).card)
            have hv : u_1.1 ⊓ v_1.1 = v_1.1 := by
              exact Subgroup.eq_of_le_of_card_eq (inf_le_right) hvCard
            have hsub : u_1.1 = v_1.1 := by
              calc
                u_1.1 = u_1.1 ⊓ v_1.1 := by symm; exact hu
                _ = v_1.1 := hv
            cases hsub
            exact Subtype.ext hEq
      have hle : Nat.card D ≤ 132 := by
        exact Fintype.card_le_card_of_injective f hinj
      omega
