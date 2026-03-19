import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_23 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 462) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  let Q : Sylow 11 G := Classical.choice Sylow.nonempty
  have hQcard : Fintype.card (Q : Subgroup G) = 11 := by
    have h := Q.card_eq_multiplicity
    rw [hG] at h
    norm_num at h
    exact h
  have hdiv : Fintype.card (Sylow 11 G) ∣ 42 := by
    have h := card_sylow_dvd_card (G := G) (p := 11)
    simpa [hG, hQcard] using h
  have hmod : Fintype.card (Sylow 11 G) ≡ 1 [MOD 11] := by
    simpa using (card_sylow_modEq_one (G := G) (p := 11))
  have hcardSylow : Fintype.card (Sylow 11 G) = 1 := by
    omega
  rcases Fintype.card_eq_one_iff.mp hcardSylow with ⟨x, hx⟩
  haveI : Unique (Sylow 11 G) := ⟨x, hx⟩
  let P : Sylow 11 G := x
  have hPnormal : (P : Subgroup G).Normal := by
    infer_instance
  have hPcard : Fintype.card (P : Subgroup G) = 11 := by
    have h := P.card_eq_multiplicity
    rw [hG] at h
    norm_num at h
    exact h
  have hcases := hsimple.2 (P : Subgroup G) hPnormal
  rcases hcases with hbot | htop
  · have : (11 : ℕ) = 1 := by
      simpa [hbot] using hPcard
    norm_num at this
  · have : (11 : ℕ) = 462 := by
      simpa [htop, hG] using hPcard
    norm_num at this
