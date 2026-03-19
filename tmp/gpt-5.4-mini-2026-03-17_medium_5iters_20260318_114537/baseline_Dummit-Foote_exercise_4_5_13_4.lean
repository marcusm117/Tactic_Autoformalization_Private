import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have h7prime : Nat.Prime 7 := by decide
  have h2prime : Nat.Prime 2 := by decide
  have h7div : Fintype.card (Sylow 7 G) ∣ 8 := by
    have h := card_sylow_dvd_card (G := G) (p := 7)
    simpa [hG] using h
  have h7mod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
    simpa using card_sylow_modEq_one (G := G) (p := 7)
  have h7count : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 8 := by
    omega
  rcases h7count with h7count | h7count
  · let P : Sylow 7 G := Classical.choice (Sylow.nonempty (p := 7) (G := G))
    refine ⟨7, P, h7prime, by norm_num [hG], ?_⟩
    have hsub : Subsingleton (Sylow 7 G) := by
      rcases (Fintype.card_eq_one_iff.mp h7count) with ⟨x, hx⟩
      exact ⟨fun a b => by rw [hx a, hx b]⟩
    haveI : Subsingleton (Sylow 7 G) := hsub
    change ∀ g : G, g • P = P
    intro g
    exact Subsingleton.elim _ _
  ·
    have h48 : Fintype.card {x : G // orderOf x = 7} = 48 := by
      simpa [h7count] using (card_orderOf_eq_prime (G := G) (p := 7) h7prime)
    have hcomp : Fintype.card {x : G // orderOf x ≠ 7} = 8 := by
      have h := Fintype.card_subtype_compl (α := G) (p := fun x => orderOf x = 7)
      omega
    let P2 : Sylow 2 G := Classical.choice (Sylow.nonempty (p := 2) (G := G))
    have hcardP2 : Fintype.card (P2 : Set G) = 8 := by
      simpa using P2.1.card_eq
    have hsub : (P2 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
      intro x hx
      intro hx7
      have hord : orderOf ⟨x, hx⟩ ∣ Fintype.card (P2 : Set G) := by
        simpa using (orderOf_dvd_card (x := ⟨x, hx⟩))
      have : 7 ∣ 8 := by
        simpa [hcardP2, hx7] using hord
      omega
    have hEq : (P2 : Set G) = {x : G | orderOf x ≠ 7} := by
      exact Set.eq_of_subset_of_card_le hsub (by simpa [hcardP2, hcomp])
    have huniq2 : Subsingleton (Sylow 2 G) := by
      refine ⟨?_⟩
      intro Q1 Q2
      have hcard1 : Fintype.card (Q1 : Set G) = 8 := by
        simpa using Q1.1.card_eq
      have hcard2 : Fintype.card (Q2 : Set G) = 8 := by
        simpa using Q2.1.card_eq
      have hsub1 : (Q1 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
        intro x hx
        intro hx7
        have hord : orderOf ⟨x, hx⟩ ∣ Fintype.card (Q1 : Set G) := by
          simpa using (orderOf_dvd_card (x := ⟨x, hx⟩))
        have : 7 ∣ 8 := by
          simpa [hcard1, hx7] using hord
        omega
      have hsub2 : (Q2 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
        intro x hx
        intro hx7
        have hord : orderOf ⟨x, hx⟩ ∣ Fintype.card (Q2 : Set G) := by
          simpa using (orderOf_dvd_card (x := ⟨x, hx⟩))
        have : 7 ∣ 8 := by
          simpa [hcard2, hx7] using hord
        omega
      have hEq1 : (Q1 : Set G) = {x : G | orderOf x ≠ 7} := by
        exact Set.eq_of_subset_of_card_le hsub1 (by simpa [hcard1, hcomp])
      have hEq2 : (Q2 : Set G) = {x : G | orderOf x ≠ 7} := by
        exact Set.eq_of_subset_of_card_le hsub2 (by simpa [hcard2, hcomp])
      simpa [hEq1, hEq2]
    refine ⟨2, P2, h2prime, by norm_num [hG], ?_⟩
    haveI : Subsingleton (Sylow 2 G) := huniq2
    change ∀ g : G, g • P2 = P2
    intro g
    exact Subsingleton.elim _ _
