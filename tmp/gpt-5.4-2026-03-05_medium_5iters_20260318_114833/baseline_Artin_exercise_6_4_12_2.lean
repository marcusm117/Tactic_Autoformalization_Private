import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_12 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 224) :
  IsSimpleGroup G → false := by
  intro hs
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P : Sylow 2 G := Classical.choice inferInstance
  have hfac : (224).factorization 2 = 5 := by
    native_decide
  have hPcardN : Nat.card P = 32 := by
    have h : Nat.card P = 2 ^ (Nat.card G).factorization 2 := P.card_eq_multiplicity
    have hG' : Nat.card G = 224 := by
      simpa using hG
    rw [hG', hfac] at h
    norm_num at h
    exact h
  have hPcard : Fintype.card P = 32 := by
    simpa using hPcardN
  have hP_not_normal : ¬ (P : Subgroup G).Normal := by
    intro hPnorm
    rcases hs.eq_bot_or_eq_top_of_normal (P : Subgroup G) hPnorm with hbot | htop
    · have : (1 : ℕ) = 32 := by
        simpa [hbot] using hPcard
      omega
    · have : (224 : ℕ) = 32 := by
        simpa [htop, hG] using hPcard
      omega
  have hIndex : (P : Subgroup G).index = 7 := by
    have h : (P : Subgroup G).index * Nat.card P = Nat.card G := (P : Subgroup G).index_mul_card
    have h' : (P : Subgroup G).index * 32 = 224 := by
      simpa [hPcardN, hG] using h
    omega
  have hcard_eq : Nat.card (Sylow 2 G) = ((P : Subgroup G).normalizer).index := by
    simpa using P.card_eq_index_normalizer
  have hdiv7 : Nat.card (Sylow 2 G) ∣ 7 := by
    have h : ((P : Subgroup G).normalizer).index ∣ (P : Subgroup G).index :=
      Subgroup.index_dvd_of_le (show (P : Subgroup G) ≤ (P : Subgroup G).normalizer from le_normalizer)
    rw [← hcard_eq, hIndex] at h
    exact h
  have hcard2 : Nat.card (Sylow 2 G) = 1 ∨ Nat.card (Sylow 2 G) = 7 := by
    exact (Nat.dvd_prime (by decide : Nat.Prime 7)).1 hdiv7
  rcases hcard2 with hcard2 | hcard2
  · have hcard2' : Fintype.card (Sylow 2 G) = 1 := by
      simpa using hcard2
    haveI : Subsingleton (Sylow 2 G) := by
      refine Fintype.card_le_one_iff_subsingleton.mp ?_
      rw [hcard2']
    have hPnorm : (P : Subgroup G).Normal := P.normal_of_subsingleton
    exact hP_not_normal hPnorm
  · have hcard2' : Fintype.card (Sylow 2 G) = 7 := by
      simpa using hcard2
    let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPermHom G (Sylow 2 G)
    have hker_bot : φ.ker = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal φ.ker (by infer_instance : φ.ker.Normal) with hker | hker
      · exact hker
      · exfalso
        have hfixP : ∀ g : G, g • P = P := by
          intro g
          have hgker : g ∈ φ.ker := by
            simpa [hker]
          have hφg : φ g = 1 := by
            simpa using hgker
          simpa using congrArg (fun σ => σ P) hφg
        have hnormtop : (P : Subgroup G).normalizer = ⊤ := by
          ext g
          constructor
          · intro _
            simp
          · intro _
            simpa using hfixP g
        have hPnorm : (P : Subgroup G).Normal := Subgroup.normalizer_eq_top.mp hnormtop
        exact hP_not_normal hPnorm
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
        _ = b := by simp [hone]
    have hdiv : Fintype.card G ∣ Fintype.card (Equiv.Perm (Sylow 2 G)) := by
      simpa using card_dvd_of_injective φ hφinj
    rw [hG, Fintype.card_perm, hcard2'] at hdiv
    norm_num at hdiv
