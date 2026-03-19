import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_23 {G : Type*}
  [Group G] (σ : MulAut G) (hs : ∀ g : G, σ g = g ↔ g = 1)
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x := by
  intro x y
  have hcomm : IsMulCommutative G := by
    simpa using (σ.isCommutative_of_fixedPointFree hs hs2)
  haveI := hcomm
  simpa using (mul_comm x y)
