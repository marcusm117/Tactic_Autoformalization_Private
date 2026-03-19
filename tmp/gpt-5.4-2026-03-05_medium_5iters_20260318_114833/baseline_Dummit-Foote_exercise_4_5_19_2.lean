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
    norm_num
  letI : Fact (Odd (Nat.card G)) := ⟨hodd⟩
  letI : IsSimpleGroup G := hS
  letI : IsSolvable G := by
    infer_instance
  letI : CommGroup G := by
    infer_instance
  have hprime : Nat.Prime (Nat.card G) := by
    simpa using (IsSimpleGroup.prime_card (α := G))
  have hnotprime : ¬ Nat.Prime (Nat.card G) := by
    rw [hcard]
    norm_num
  exact hnotprime hprime
