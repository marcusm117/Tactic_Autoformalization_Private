import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_3_5_6 {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {S : Set V} (hS : Set.Countable S)
  (hS1 : span K S = ⊤) {ι : Type*} (R : ι → V)
  (hR : LinearIndependent K R) : Countable ι := by
  classical
  have hι : Cardinal.mk ι ≤ Module.rank K V := hR.mk_le_rank
  have hrank : Module.rank K V ≤ Cardinal.aleph0 := by
    have hs : Cardinal.mk S ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0.mp hS
    simpa [hS1] using (Module.rank_span_le (K := K) (s := S))
  exact Cardinal.mk_le_aleph0.mpr (hι.trans hrank)
