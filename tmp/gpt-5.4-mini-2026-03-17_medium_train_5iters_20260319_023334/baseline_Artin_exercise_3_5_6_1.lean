import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_3_5_6 {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {S : Set V} (hS : Set.Countable S)
  (hS1 : span K S = ⊤) {ι : Type*} (R : ι → V)
  (hR : LinearIndependent K R) : Countable ι := by
  classical
  have hι : Cardinal.mk ι ≤ Module.rank K V := hR.cardinal_mk_le_rank
  have hr : Module.rank K V ≤ Cardinal.mk S := by
    simpa [hS1] using (Submodule.rank_span_le (K := K) (s := S))
  have hs : Cardinal.mk S ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0 hS
  have hcount : Cardinal.mk ι ≤ Cardinal.aleph0 := hι.trans (hr.trans hs)
  exact Cardinal.mk_le_aleph0 hcount
