import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have h7 : Nat.Prime 7 := by decide
  have hdiv : Fintype.card (Sylow 7 G) ∣ 8 := by
    have h := Nat.card_sylow_dvd_card (G := G) (p := 7)
    simpa [hG] using h
  have hmod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
    simpa using Nat.card_sylow_modEq_one (G := G) (p := 7)
  have hcard : Fintype.card (Sylow 7 G) = 1 := by
    omega
  let P : Sylow 7 G := Classical.choice (show Nonempty (Sylow 7 G) from inferInstance)
  refine ⟨7, P, h7, by simpa [hG], ?_⟩
  have hsub : Subsingleton (Sylow 7 G) := (Fintype.card_eq_one_iff.mp hcard)
  change ∀ g : G, P.conj g = P
  intro g
  exact Subsingleton.elim _ _
