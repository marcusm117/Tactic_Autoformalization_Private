import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  intro hS
  have hcard : Nat.card G = 6545 := by
    simpa using hG
  have hodd : Odd (Nat.card G) := by
    rw [hcard]
    decide
  letI : Fact (Odd (Nat.card G)) := ⟨hodd⟩
  letI : IsSimpleGroup G := hS
  haveI : IsSolvable G := feit_thompson (α := G)
  haveI : IsCyclic G := IsSimpleGroup.isCyclic (α := G)
  letI : CommGroup G := by
    infer_instance
  have hprime : Nat.Prime (Nat.card G) := IsSimpleGroup.prime_card (α := G)
  have hnotprime : ¬ Nat.Prime (Nat.card G) := by
    rw [hcard]
    decide
  exact hnotprime hprime
