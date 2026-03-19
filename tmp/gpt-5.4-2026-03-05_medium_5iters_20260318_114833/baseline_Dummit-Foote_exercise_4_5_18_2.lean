import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_18 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 200) :
  ∃ N : Sylow 5 G, N.Normal := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := by
    simpa using card_sylow_modEq_one (p := 5) (G := G)
  have hPcard : Nat.card P = 25 := by
    simpa [Nat.card_eq_fintype_card, hG] using P.card_eq_multiplicity
  have hindex : (↑P : Subgroup G).index = 8 := by
    have hmul : (↑P : Subgroup G).index * Nat.card P = Nat.card G := by
      simpa using Subgroup.index_mul_card ((↑P : Subgroup G))
    rw [Nat.card_eq_fintype_card, hG, hPcard] at hmul
    omega
  have hdvd : Nat.card (Sylow 5 G) ∣ 8 := by
    have h' : Nat.card (Sylow 5 G) ∣ (↑P : Subgroup G).index := by
      simpa using P.card_sylow_dvd_index
    rwa [hindex] at h'
  have hcardNat : Nat.card (Sylow 5 G) = 1 := by
    let d : Nat := Nat.card (Sylow 5 G)
    have hpos : 0 < d := by
      simpa [d] using (Nat.card_pos (α := Sylow 5 G))
    have hle : d ≤ 8 := Nat.le_of_dvd (by decide) (by simpa [d] using hdvd)
    have hmod' : d % 5 = 1 := by
      simpa [d, Nat.ModEq] using hmod
    have hdvd' : d ∣ 8 := by
      simpa [d] using hdvd
    interval_cases d <;> first
      | rfl
      | (exfalso; norm_num at hmod')
      | (exfalso; norm_num at hdvd')
  have hcard : Fintype.card (Sylow 5 G) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hcardNat
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨N, hN⟩
  letI : Unique (Sylow 5 G) :=
    { default := N
      uniq := fun A => hN A }
  exact ⟨N, by infer_instance⟩
