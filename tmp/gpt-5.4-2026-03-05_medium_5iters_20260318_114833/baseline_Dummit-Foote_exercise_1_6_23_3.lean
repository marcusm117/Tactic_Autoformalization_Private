import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_23 {G : Type*}
  [Group G] (σ : MulAut G) (hs : ∀ g : G, σ g = g ↔ g = 1)
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x := by
  intro x y
  letI : Fact (∀ g : G, σ g = g ↔ g = 1) := ⟨hs⟩
  letI : Fact (∀ g : G, σ g = g → g = 1) := ⟨fun g hg => (hs g).1 hg⟩
  letI : Fact (Function.Involutive σ) := ⟨hs2⟩
  letI : Fact (∀ g : G, σ (σ g) = g) := ⟨hs2⟩
  haveI : IsMulCommutative G := inferInstance
  simpa using mul_comm x y
