import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_8 {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial := by
  classical
  refine ⟨H.normalCore, H.normalCore_le, H.normalCore_normal, ?_⟩
  haveI : Finite (G ⧸ H) := by
    apply Nat.finite_of_card_ne_zero
    simpa [hH] using (Nat.ne_of_gt hn : n ≠ 0)
  simpa [hH, Fintype.card_perm] using H.index_normalCore_le_card
