import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  intro hS
  have hodd : Odd (Fintype.card G) := by
    rw [hG]
    decide
  letI : Fact (Odd (Fintype.card G)) := ⟨hodd⟩
  letI : IsSimpleGroup G := hS
  haveI : IsSolvable G := by
    infer_instance
  haveI : IsCyclic G := by
    infer_instance
  letI : CommGroup G := IsCyclic.commGroup G
  have hprime : Nat.Prime (Fintype.card G) := by
    simpa using (IsSimpleGroup.prime_card (α := G))
  rw [hG] at hprime
  norm_num at hprime
