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
    exact hH (by simpa [n, h0] using hn)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hmin := Nat.find_min' hsol
  have hbot : derivedSeries H (n - 1) ≠ ⊥ := by
    exact hmin (n - 1) (Nat.sub_lt hnpos (by decide))
  let A : Subgroup G := derivedSeries H (n - 1)
  refine ⟨A, ?_, ?_⟩
  · simpa [A] using (derivedSeries_le (H := H) (n - 1))
  · refine ⟨hbot, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [A] using (derivedSeries_normal (H := H) (n - 1))
    · have hder : commutatorSubgroup A = ⊥ := by
        simpa [A, Nat.succ_pred_eq_of_pos hnpos] using hn
      haveI : IsCommutative A := (Subgroup.commutatorSubgroup_eq_bot_iff).mp hder
      intro a b
      simpa using mul_comm a b
