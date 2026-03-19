import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_18 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 200) :
  ∃ N : Sylow 5 G, N.Normal := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by
    simpa using (Sylow.card_sylow_modEq_one (p := 5) (G := G))
  have hdvd : Fintype.card (Sylow 5 G) ∣ 8 := by
    have hpow : 5 ^ padicValNat 5 200 = 25 := by
      native_decide
    have hquot : 200 / 25 = 8 := by
      native_decide
    simpa [hG, hpow, hquot] using (Sylow.card_sylow_dvd_index (p := 5) (G := G))
  have hcard : Fintype.card (Sylow 5 G) = 1 := by
    let d : Nat := Fintype.card (Sylow 5 G)
    have hmod' : d % 5 = 1 := by
      simpa [d, Nat.ModEq] using hmod
    have hdle : d ≤ 8 := Nat.le_of_dvd (by decide) (by simpa [d] using hdvd)
    have hd : d = 1 := by
      interval_cases d <;> simp_all
    simpa [d] using hd
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨N, hN⟩
  letI : Unique (Sylow 5 G) :=
    { default := N
      uniq := fun A => hN A }
  exact ⟨N, by infer_instance⟩
