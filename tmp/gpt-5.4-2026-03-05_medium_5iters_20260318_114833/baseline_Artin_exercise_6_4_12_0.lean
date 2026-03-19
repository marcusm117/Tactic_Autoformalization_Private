import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_12 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 224) :
  IsSimpleGroup G → false := by
  intro hs
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hdiv2 : Fintype.card (Sylow 2 G) ∣ 224 := by
    simpa [hG] using (Sylow.card_sylow_dvd_card (G := G) (p := 2))
  have hmod2 : Fintype.card (Sylow 2 G) ≡ 1 [MOD 2] := by
    simpa using (Sylow.card_sylow_modEq_one (G := G) (p := 2))
  have hcard2 : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 7 := by
    have haux : ∀ n : ℕ, n ∣ 224 → n ≡ 1 [MOD 2] → n = 1 ∨ n = 7 := by
      native_decide
    exact haux _ hdiv2 hmod2
  rcases hcard2 with hcard2 | hcard2
  · haveI : Subsingleton (Sylow 2 G) :=
      Fintype.card_le_one_iff_subsingleton.mp (by simpa [hcard2])
    let P : Sylow 2 G := Classical.choice (inferInstance : Nonempty (Sylow 2 G))
    have hPnorm : (P : Subgroup G).Normal := P.normal_of_subsingleton
    letI := hPnorm
    have hP : (P : Subgroup G) = ⊥ ∨ (P : Subgroup G) = ⊤ := hs.eq_bot_or_eq_top (P : Subgroup G)
    have hPcard : Fintype.card P = 32 := by
      have h := P.card_eq_multiplicity
      rw [hG] at h
      norm_num at h
      simpa using h
    rcases hP with hP | hP
    · have h' := hPcard
      simpa [hP, hG] at h'
      exact h'
    · have h' := hPcard
      simpa [hP, hG] at h'
      exact h'
  · let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPermHom G (Sylow 2 G)
    have hker_bot : φ.ker = ⊥ := by
      rcases hs.eq_bot_or_eq_top φ.ker with hker | hker
      · exact hker
      · exfalso
        have hfix : ∀ g : G, ∀ P : Sylow 2 G, g • P = P := by
          intro g P
          have hgker : g ∈ φ.ker := by
            simpa [hker]
          have hφg : φ g = 1 := by
            simpa using hgker
          simpa using congrArg (fun σ => σ P) hφg
        haveI : Subsingleton (Sylow 2 G) := by
          refine ⟨?_⟩
          intro P Q
          obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
          exact (hfix g P).symm.trans hg
        have h' : Fintype.card (Sylow 2 G) = 1 := Fintype.card_ofSubsingleton (Sylow 2 G)
        simpa [hcard2] at h'
        exact h'
    have hφinj : Function.Injective φ := by
      intro a b hab
      have hmem : a * b⁻¹ ∈ φ.ker := by
        simp [hab]
      have hone : a * b⁻¹ = 1 := by
        have : a * b⁻¹ ∈ (⊥ : Subgroup G) := by
          simpa [hker_bot] using hmem
        simpa using this
      calc
        a = (a * b⁻¹) * b := by simp [mul_assoc]
        _ = b := by simpa [hone]
    have h' := card_dvd_of_injective φ hφinj
    rw [hG, Fintype.card_perm, hcard2] at h'
    norm_num at h'
    exact h'
