import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have hprime7 : Nat.Prime 7 := by decide
  have hprime2 : Nat.Prime 2 := by decide
  have h7dvd : Fintype.card (Sylow 7 G) ∣ 8 := by
    simpa [hG] using (Sylow.card_sylow_dvd_card_univ (G := G) (p := 7))
  have h7mod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
    simpa using (Sylow.card_sylow_modEq_one (G := G) (p := 7))
  have h7count : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 8 := by
    omega
  rcases h7count with h7count | h7count
  · let P7 : Sylow 7 G := Classical.choice (Sylow.nonempty 7 G)
    refine ⟨7, P7, hprime7, by simpa [hG], ?_⟩
    exact P7.normal_of_card_eq_one h7count
  · let P7 : Sylow 7 G := Classical.choice (Sylow.nonempty 7 G)
    have h48 : Fintype.card {x : G // orderOf x = 7} = 48 := by
      simpa [h7count] using (card_orderOf_eq_prime (G := G) (p := 7) hprime7)
    have hcomp : Fintype.card {x : G // orderOf x ≠ 7} = 8 := by
      have h := Fintype.card_subtype_compl (s := {x : G | orderOf x = 7})
      omega
    let P2 : Sylow 2 G := Classical.choice (Sylow.nonempty 2 G)
    have hsub : (P2 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
      intro x hx
      have hord : orderOf x ∣ 8 := by
        simpa [P2.card] using (orderOf_dvd_card (x := x))
      intro hx7
      have : 7 ∣ 8 := by simpa [hx7] using hord
      omega
    have hcardP2 : Fintype.card (P2 : Set G) = 8 := by
      simpa using P2.card
    have hEq : (P2 : Set G) = {x : G | orderOf x ≠ 7} := by
      exact Set.eq_of_subset_of_card_le hsub (by simpa [hcardP2, hcomp])
    have huniq : Subsingleton (Sylow 2 G) := by
      refine ⟨?_⟩
      intro Q1 Q2
      have hsub₁ : (Q1 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
        intro x hx
        have hord : orderOf x ∣ 8 := by
          simpa [Q1.card] using (orderOf_dvd_card (x := x))
        intro hx7
        have : 7 ∣ 8 := by simpa [hx7] using hord
        omega
      have hsub₂ : (Q2 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
        intro x hx
        have hord : orderOf x ∣ 8 := by
          simpa [Q2.card] using (orderOf_dvd_card (x := x))
        intro hx7
        have : 7 ∣ 8 := by simpa [hx7] using hord
        omega
      have hcard₁ : Fintype.card (Q1 : Set G) = 8 := by simpa using Q1.card
      have hcard₂ : Fintype.card (Q2 : Set G) = 8 := by simpa using Q2.card
      have hEq₁ : (Q1 : Set G) = {x : G | orderOf x ≠ 7} := by
        exact Set.eq_of_subset_of_card_le hsub₁ (by simpa [hcard₁, hcomp])
      have hEq₂ : (Q2 : Set G) = {x : G | orderOf x ≠ 7} := by
        exact Set.eq_of_subset_of_card_le hsub₂ (by simpa [hcard₂, hcomp])
      simpa [hEq₁, hEq₂]
    have hcard2 : Fintype.card (Sylow 2 G) = 1 := by
      exact Fintype.card_eq_one_iff.mpr huniq
    refine ⟨2, P2, hprime2, by simpa [hG], ?_⟩
    exact P2.normal_of_card_eq_one hcard2
