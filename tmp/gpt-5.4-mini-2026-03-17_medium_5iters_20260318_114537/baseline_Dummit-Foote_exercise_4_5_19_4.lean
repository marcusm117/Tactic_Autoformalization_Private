import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  intro h
  have hprime : Nat.Prime (Fintype.card G) := h.card_eq_prime
  have hnot : ¬ Nat.Prime (6545 : Nat) := by native_decide
  exact hnot (by simpa [hG] using hprime)
