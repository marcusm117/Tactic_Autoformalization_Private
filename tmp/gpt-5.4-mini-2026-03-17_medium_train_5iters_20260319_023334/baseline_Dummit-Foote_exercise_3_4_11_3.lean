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
    have : (⊥ : Subgroup H) = ⊤ := by
      simpa [n, h0] using hn.symm
    exact bot_ne_top this
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hmin := Nat.find_min' hsol
  let k := n - 1
  have hk : k + 1 = n := by
    simp [k, Nat.succ_pred_eq_of_pos hnpos]
  have hbot : derivedSeries H k ≠ ⊥ := by
    exact hmin k (Nat.sub_lt hnpos (by decide))
  have hn' : derivedSeries H (k + 1) = ⊥ := by
    simpa [hk] using hn
  have hcomm : commutatorSubgroup (derivedSeries H k) = ⊥ := by
    have hds : derivedSeries H (k + 1) = commutatorSubgroup (derivedSeries H k) := by
      simpa using (derivedSeries_succ (H := H) k)
    rw [hds] at hn'
    simpa using hn'
  let A : Subgroup G := derivedSeries H k
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa [A] using (derivedSeries_le (H := H) k)
  · simpa [A] using hbot
  · simpa [A] using (derivedSeries_normal (H := H) k)
  · haveI : IsCommutative A := (Subgroup.commutatorSubgroup_eq_bot_iff).mp (by simpa [A] using hcomm)
    intro a b
    simpa using mul_comm a b
