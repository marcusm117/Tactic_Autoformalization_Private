import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have h7prime : Nat.Prime 7 := by decide
  have h2prime : Nat.Prime 2 := by decide
  have hdiv : Fintype.card (Sylow 7 G) ∣ 8 := by
    have h := Fintype.card_sylow_dvd_card_univ (G := G) (p := 7)
    simpa [hG] using h
  have hmod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
    simpa using Fintype.card_sylow_modEq_one (G := G) (p := 7)
  have h7count : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 8 := by
    omega
  rcases h7count with h7count | h7count
  · let P : Sylow 7 G := Classical.choice (Sylow.nonempty (p := 7) (G := G))
    haveI : Unique (Sylow 7 G) := by
      refine ⟨P, ?_⟩
      intro Q
      exact Subsingleton.elim _ _
    refine ⟨7, P, h7prime, by norm_num [hG], ?_⟩
    simpa using (Sylow.normal_of_unique (G := G) (p := 7) (P := P))
  · let P2 : Sylow 2 G := Classical.choice (Sylow.nonempty (p := 2) (G := G))
    have h48 : Fintype.card {x : G // orderOf x = 7} = 48 := by
      simpa [h7count] using (Fintype.card_orderOf_eq_prime (G := G) (p := 7) h7prime)
    have hcomp : Fintype.card {x : G // orderOf x ≠ 7} = 8 := by
      have h := Fintype.card_subtype_compl (α := G) (p := fun x => orderOf x = 7)
      omega
    have huniq2 : Subsingleton (Sylow 2 G) := by
      refine ⟨?_⟩
      intro Q1 Q2
      have hcard1 : Fintype.card Q1 = 8 := by
        simpa [hG] using (Q1.2.card_eq)
      have hcard2 : Fintype.card Q2 = 8 := by
        simpa [hG] using (Q2.2.card_eq)
      have hsub1 : (Q1 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
        intro x hx
        have hx' : x ∈ (Q1 : Subgroup G) := hx
        have hord : orderOf ⟨x, hx'⟩ ∣ Fintype.card Q1 := by
          simpa using (orderOf_dvd_card (x := ⟨x, hx'⟩))
        intro hx7
        have : 7 ∣ 8 := by
          simpa [hx7, hcard1] using hord
        omega
      have hsub2 : (Q2 : Set G) ⊆ {x : G | orderOf x ≠ 7} := by
        intro x hx
        have hx' : x ∈ (Q2 : Subgroup G) := hx
        have hord : orderOf ⟨x, hx'⟩ ∣ Fintype.card Q2 := by
          simpa using (orderOf_dvd_card (x := ⟨x, hx'⟩))
        intro hx7
        have : 7 ∣ 8 := by
          simpa [hx7, hcard2] using hord
        omega
      have hEq1 : (Q1 : Set G) = {x : G | orderOf x ≠ 7} := by
        exact Set.eq_of_subset_of_card_le hsub1 (by simpa [hcard1, hcomp])
      have hEq2 : (Q2 : Set G) = {x : G | orderOf x ≠ 7} := by
        exact Set.eq_of_subset_of_card_le hsub2 (by simpa [hcard2, hcomp])
      simpa [hEq1, hEq2]
    haveI : Unique (Sylow 2 G) := by
      refine ⟨P2, ?_⟩
      intro Q
      exact Subsingleton.elim _ _
    refine ⟨2, P2, h2prime, by norm_num [hG], ?_⟩
    simpa using (Sylow.normal_of_unique (G := G) (p := 2) (P := P2))
