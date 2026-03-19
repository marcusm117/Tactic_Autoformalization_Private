import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_18 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 200) :
  ∃ N : Sylow 5 G, N.Normal := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := by
    simpa using card_sylow_modEq_one (p := 5) (G := G)
  have hquot : Nat.card G / 5 ^ padicValNat 5 (Nat.card G) = 8 := by
    rw [Nat.card_eq_fintype_card, hG]
    native_decide
  have hdvd : Nat.card (Sylow 5 G) ∣ 8 := by
    have h' : Nat.card (Sylow 5 G) ∣ Nat.card G / 5 ^ padicValNat 5 (Nat.card G) := by
      simpa using card_sylow_dvd_index (p := 5) (G := G)
    rwa [hquot] at h'
  have hcardNat : Nat.card (Sylow 5 G) = 1 := by
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hmod' : Nat.card (Sylow 5 G) % 5 = 1 := by
      simpa [Nat.ModEq] using hmod
    omega
  have hcard : Fintype.card (Sylow 5 G) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hcardNat
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨N, hN⟩
  letI : Unique (Sylow 5 G) :=
    { default := N
      uniq := fun A => hN A }
  exact ⟨N, by infer_instance⟩
