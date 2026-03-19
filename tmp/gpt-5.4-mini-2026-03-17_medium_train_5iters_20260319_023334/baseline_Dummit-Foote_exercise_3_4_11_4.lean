import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_11 {G : Type*} [Group G] [IsSolvable G]
  {H : Subgroup G} (hH : H ≠ ⊥) [H.Normal] :
  ∃ A ≤ H, A ≠ ⊥ ∧ A.Normal ∧ ∀ a b : A, a*b = b*a := by
  classical
  have hsol : ∃ n : ℕ, derivedSeries H n = ⊥ := by
    rcases (show IsSolvable H from inferInstance) with ⟨n, hn⟩
    exact ⟨n, hn⟩
  let n := Nat.find hsol
  have hn : derivedSeries H n = ⊥ := Nat.find_spec hsol
  have hn0 : n ≠ 0 := by
    intro h0
    have : (⊤ : Subgroup H) = ⊥ := by
      simpa [n, h0] using hn
    exact top_ne_bot this
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hmin := Nat.find_min' hsol
  have hbot : derivedSeries H (n - 1) ≠ ⊥ := by
    exact hmin (n - 1) (Nat.sub_lt hnpos (by decide))
  have hk : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
  have hcomm : commutatorSubgroup (derivedSeries H (n - 1)) = ⊥ := by
    have hds : derivedSeries H (n - 1 + 1) = commutatorSubgroup (derivedSeries H (n - 1)) := by
      simpa using (derivedSeries_succ (H := H) (n - 1))
    rw [hk] at hds
    rw [hds] at hn
    simpa using hn
  refine ⟨derivedSeries H (n - 1), ?_, ?_, ?_, ?_⟩
  · simpa using (derivedSeries_le (H := H) (n - 1))
  · exact hbot
  · simpa using (derivedSeries_normal (H := H) (n - 1))
  · haveI : IsCommutative (derivedSeries H (n - 1)) :=
      (Subgroup.commutatorSubgroup_eq_bot_iff).mp hcomm
    intro a b
    simpa using mul_comm a b
