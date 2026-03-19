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
  have hPcard : Nat.card (↑P : Subgroup G) = 25 := by
    calc
      Nat.card (↑P : Subgroup G) = 5 ^ (Nat.factorization (Nat.card G) 5) := P.card_eq_multiplicity
      _ = 5 ^ (Nat.factorization 200 5) := by rw [Nat.card_eq_fintype_card, hG]
      _ = 25 := by native_decide
  have hindex : (↑P : Subgroup G).index = 8 := by
    have hmul : (↑P : Subgroup G).index * Nat.card (↑P : Subgroup G) = Nat.card G := by
      simpa using Subgroup.index_mul_card (↑P : Subgroup G)
    rw [hPcard, Nat.card_eq_fintype_card, hG] at hmul
    omega
  have hsyl : Nat.card (Sylow 5 G) = (Subgroup.normalizer (↑P : Subgroup G)).index := by
    simpa using card_sylow_eq_index_normalizer (P := P)
  have hdvd : Nat.card (Sylow 5 G) ∣ 8 := by
    rw [hsyl]
    have hdiv :
        (Subgroup.normalizer (↑P : Subgroup G)).index ∣ (↑P : Subgroup G).index :=
      Subgroup.index_dvd_of_le
        (Subgroup.le_normalizer : (↑P : Subgroup G) ≤ Subgroup.normalizer (↑P : Subgroup G))
    rwa [hindex] at hdiv
  have hcardNat : Nat.card (Sylow 5 G) = 1 := by
    let d : Nat := Nat.card (Sylow 5 G)
    have hdvd' : d ∣ 8 := by
      simpa [d] using hdvd
    have hle : d ≤ 8 := Nat.le_of_dvd (by decide) hdvd'
    have hmod' : d % 5 = 1 := by
      simpa [d, Nat.ModEq] using hmod
    let q : Nat := d / 5
    have hdecomp : d = 1 + 5 * q := by
      dsimp [q]
      have h := Nat.mod_add_div d 5
      omega
    have hqle : q ≤ 1 := by
      omega
    interval_cases q
    · have hd : d = 1 := by
        omega
      simpa [d] using hd
    · exfalso
      have hd : d = 6 := by
        omega
      have hdvd6 : 6 ∣ 8 := by
        simpa [d, hd] using hdvd'
      norm_num at hdvd6
  have hcard : Fintype.card (Sylow 5 G) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hcardNat
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨N, hN⟩
  letI : Unique (Sylow 5 G) :=
    { default := N
      uniq := fun A => hN A }
  exact ⟨N, by infer_instance⟩
