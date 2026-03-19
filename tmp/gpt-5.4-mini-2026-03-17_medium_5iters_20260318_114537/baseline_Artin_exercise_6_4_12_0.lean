import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_12 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 224) :
  IsSimpleGroup G → false := by
  classical
  intro hsimple
  have hsyl : Fintype.card (Sylow 2 G) ∣ 7 := by
    simpa [hG] using (card_sylow_dvd_card (G := G) (p := 2))
  have hcardSyl : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 7 := by
    have hprime : Nat.Prime 7 := by decide
    exact hprime.eq_one_or_self_of_dvd hsyl
  rcases hcardSyl with h1 | h7
  · let P : Sylow 2 G := Classical.choice (Sylow.nonempty (p := 2) (G := G))
    have hPnorm : P.1.Normal := by
      simpa [h1] using (Sylow.normal_of_card_eq_one (P := P) (p := 2) h1)
    have hPcard : Fintype.card (P : Type*) = 32 := by
      simpa [hG] using P.card
    rcases hsimple P.1 hPnorm with hbot | htop
    · have : Fintype.card (P : Type*) = 1 := by simpa [hbot]
      omega
    · have : Fintype.card (P : Type*) = 224 := by simpa [htop, hG]
      omega
  · let P : Sylow 2 G := Classical.choice (Sylow.nonempty (p := 2) (G := G))
    have hPnotnormal : ¬ P.1.Normal := by
      intro hnorm
      have hcard1 : Fintype.card (Sylow 2 G) = 1 := by
        exact (Sylow.card_eq_one_iff_normal (P := P) (p := 2)).2 hnorm
      omega
    let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPermHom G (Sylow 2 G)
    have hker : φ.ker = ⊥ := by
      have h' : φ.ker = ⊥ ∨ φ.ker = ⊤ := hsimple φ.ker inferInstance
      rcases h' with hbot | htop
      · exact hbot
      · exfalso
        have htriv : ∀ g : G, φ g = 1 := by
          intro g
          have hg : g ∈ φ.ker := by simpa [htop]
          simpa [MonoidHom.mem_ker] using hg
        have hnorm : P.1.Normal := by
          simpa [φ] using htriv
        exact hPnotnormal hnorm
    have hinj : Function.Injective φ := by
      simpa [MonoidHom.injective_iff_ker_eq_bot] using hker
    have hcardG : Fintype.card G ∣ Fintype.card (Equiv.Perm (Sylow 2 G)) := by
      rw [← Fintype.card_range_of_injective hinj]
      exact Subgroup.card_dvd_card φ.range
    have hperm : Fintype.card (Equiv.Perm (Sylow 2 G)) = 5040 := by
      simpa [h7] using (Fintype.card_perm (α := Sylow 2 G))
    have hdiv : 224 ∣ 5040 := by
      simpa [hG, hperm] using hcardG
    norm_num at hdiv
