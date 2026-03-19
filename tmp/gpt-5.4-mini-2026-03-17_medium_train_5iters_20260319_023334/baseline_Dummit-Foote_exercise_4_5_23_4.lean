import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_23 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 462) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  have hdiv : Fintype.card (Sylow 11 G) ∣ 42 := by
    have h := Nat.card_sylow_dvd_card (G := G) (p := 11)
    simpa [hG] using h
  have hmod : Fintype.card (Sylow 11 G) ≡ 1 [MOD 11] := by
    simpa using (card_sylow_modEq_one (G := G) (p := 11))
  have hcardSylow : Fintype.card (Sylow 11 G) = 1 := by
    have hxle : Fintype.card (Sylow 11 G) ≤ 42 := Nat.le_of_dvd (by decide) hdiv
    interval_cases n : Fintype.card (Sylow 11 G) using hxle <;>
      simp at hdiv hmod <;> omega
  have hnonempty : Inhabited (Sylow 11 G) := ⟨Classical.choice (Sylow.nonempty (p := 11) (G := G))⟩
  have hsub : Subsingleton (Sylow 11 G) := by
    classical
    intro a b
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcardSylow
    calc
      a = x := hx a
      _ = b := by symm; exact hx b
  letI : Inhabited (Sylow 11 G) := hnonempty
  letI : Subsingleton (Sylow 11 G) := hsub
  letI : Unique (Sylow 11 G) := inferInstance
  let P : Sylow 11 G := default
  have hPnormal : (P : Subgroup G).Normal := by
    infer_instance
  have hPcard : Fintype.card (P : Subgroup G) = 11 := by
    simpa [hG] using P.card_eq_multiplicity
  have hcases := hsimple.2 (P : Subgroup G) hPnormal
  rcases hcases with hbot | htop
  · have : (11 : ℕ) = 1 := by
      simpa [hbot] using hPcard
    norm_num at this
  · have : (11 : ℕ) = 462 := by
      simpa [htop, hG] using hPcard
    norm_num at this
