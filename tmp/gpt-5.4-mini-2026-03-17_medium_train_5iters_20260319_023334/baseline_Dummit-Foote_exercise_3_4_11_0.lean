import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_11 {G : Type*} [Group G] [IsSolvable G]
  {H : Subgroup G} (hH : H ≠ ⊥) [H.Normal] :
  ∃ A ≤ H, A ≠ ⊥ ∧ A.Normal ∧ ∀ a b : A, a*b = b*a := by
  classical
  have hsol : ∃ n : ℕ, H.derivedSeries n = ⊥ := by
    rcases (show IsSolvable H from inferInstance) with ⟨n, hn⟩
    exact ⟨n, hn⟩
  let n := Nat.find hsol
  have hn : H.derivedSeries n = ⊥ := Nat.find_spec hsol
  have hn0 : n ≠ 0 := by
    intro h0
    exact hH (by simpa [n, h0] using hn)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hmin := Nat.find_min' hsol
  have hbot : H.derivedSeries (n - 1) ≠ ⊥ := by
    exact hmin (n - 1) (Nat.sub_lt hnpos (by decide))
  refine ⟨H.derivedSeries (n - 1), ?_, ?_, ?_, ?_⟩
  · simpa using (H.derivedSeries_le (n - 1))
  · simpa [n] using hbot
  · infer_instance
  · have hder : (H.derivedSeries (n - 1)).derivedSeries 1 = ⊥ := by
      simpa [n, Nat.succ_pred_eq_of_pos hnpos] using hn
    have hcomm : commutatorSubgroup (H.derivedSeries (n - 1)) = ⊥ := by
      simpa using hder
    haveI : IsCommutative (H.derivedSeries (n - 1)) :=
      (Subgroup.commutatorSubgroup_eq_bot_iff).mp hcomm
    intro a b
    simpa using mul_comm a b
