import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_6_23 {G : Type*}
  [Group G] (σ : MulAut G) (hs : ∀ g : G, σ g = g ↔ g = 1)
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x := by
  intro x y
  letI : Fact (σ.fixedPoints = ⊥) := ⟨by
    ext g
    constructor
    · intro hg
      change g = 1
      exact (hs g).1 (by simpa using hg)
    · intro hg
      change σ g = g
      exact (hs g).2 hg
  ⟩
  letI : Fact (σ * σ = 1) := ⟨by
    ext g
    simpa using hs2 g
  ⟩
  letI : Fact (σ ^ 2 = 1) := ⟨by
    ext g
    simpa [pow_two] using hs2 g
  ⟩
  letI : Fact (Function.Involutive σ) := ⟨hs2⟩
  haveI : IsMulCommutative G := inferInstance
  simpa using mul_comm x y
