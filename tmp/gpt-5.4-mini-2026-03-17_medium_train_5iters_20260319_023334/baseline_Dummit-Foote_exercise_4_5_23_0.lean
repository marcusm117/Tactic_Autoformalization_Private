import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_23 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 462) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  have hdivG : 11 ∣ Fintype.card G := by
    rw [hG]
    norm_num
  have hcardSylow : Fintype.card (Sylow 11 G) = 1 := by
    have hmod : Fintype.card (Sylow 11 G) ≡ 1 [MOD 11] := by
      simpa using (card_sylow_modEq_one (G := G) (p := 11))
    have hdiv : Fintype.card (Sylow 11 G) ∣ 42 := by
      simpa [hG] using (card_sylow_dvd_index (G := G) (p := 11))
    omega
  have hnonempty : Nonempty (Sylow 11 G) := Sylow.nonempty (p := 11) (G := G) hdivG
  letI : Inhabited (Sylow 11 G) := Classical.inhabitedOfNonempty hnonempty
  haveI : Subsingleton (Sylow 11 G) := (Fintype.card_eq_one_iff.mp hcardSylow)
  haveI : Unique (Sylow 11 G) := inferInstance
  let P : Sylow 11 G := default
  have hPnormal : (P : Subgroup G).Normal := by
    simpa using (Sylow.normal_of_unique (P := P) (p := 11) (G := G))
  have hPcard : Fintype.card (P : Subgroup G) = 11 := by
    simpa [hG] using (P.card_eq)
  have hcases := hsimple.eq_bot_or_eq_top (P : Subgroup G) hPnormal
  rcases hcases with hbot | htop
  · have : (11 : ℕ) = 1 := by
      simpa [hbot] using hPcard
    norm_num at this
  · have : (11 : ℕ) = 462 := by
      simpa [htop, hG] using hPcard
    norm_num at this
