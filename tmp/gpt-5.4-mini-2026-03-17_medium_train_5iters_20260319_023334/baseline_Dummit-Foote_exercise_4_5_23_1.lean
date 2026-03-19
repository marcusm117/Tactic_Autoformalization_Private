import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_23 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 462) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hPcard : Fintype.card (P : Subgroup G) = 11 := by
    simpa [hG] using (P.2.card_eq)
  have hmod : Fintype.card (Sylow 11 G) % 11 = 1 := by
    simpa [Nat.ModEq] using (card_sylow_modEq_one (G := G) (p := 11))
  have hdiv : Fintype.card (Sylow 11 G) ∣ 42 := by
    simpa [hG, hPcard] using (card_sylow_dvd_card (P := P))
  have hcardSylow : Fintype.card (Sylow 11 G) = 1 := by
    omega
  haveI : Inhabited (Sylow 11 G) := ⟨Classical.choice Sylow.nonempty⟩
  have hsub : Subsingleton (Sylow 11 G) := by
    classical
    rcases (Fintype.card_eq_one_iff.mp hcardSylow) with ⟨x, hx⟩
    refine ⟨?_⟩
    intro a b
    have ha : a = x := hx a
    have hb : b = x := hx b
    calc
      a = x := ha
      _ = b := hb.symm
  haveI : Unique (Sylow 11 G) := inferInstance
  let P : Sylow 11 G := default
  have hPnormal : (P : Subgroup G).Normal := by
    simpa using (Sylow.normal (P := P))
  have hcases : (P : Subgroup G) = ⊥ ∨ (P : Subgroup G) = ⊤ := hsimple.1 (P : Subgroup G) hPnormal
  rcases hcases with hbot | htop
  · have : (11 : ℕ) = 1 := by
      simpa [hbot] using hPcard
    norm_num at this
  · have : (11 : ℕ) = 462 := by
      simpa [htop, hG] using hPcard
    norm_num at this
