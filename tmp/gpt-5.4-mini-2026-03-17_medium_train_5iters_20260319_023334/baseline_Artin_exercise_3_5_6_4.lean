import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_3_5_6 {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {S : Set V} (hS : Set.Countable S)
  (hS1 : span K S = ⊤) {ι : Type*} (R : ι → V)
  (hR : LinearIndependent K R) : Countable ι := by
  classical
  have hι : Cardinal.mk ι ≤ Module.rank K V := by
    exact Cardinal.mk_le_rank hR
  have hr : Module.rank K V ≤ Cardinal.mk S := by
    simpa [hS1, Submodule.rank_top] using (rank_span_le (R := K) (M := V) (s := S))
  have hs : Cardinal.mk S ≤ Cardinal.aleph0 := by
    haveI : Countable S := by
      simpa using hS
    simpa using (Cardinal.mk_le_aleph0 (α := S))
  have hcount : Cardinal.mk ι ≤ Cardinal.aleph0 := hι.trans (hr.trans hs)
  exact (countable_iff.mpr hcount)
