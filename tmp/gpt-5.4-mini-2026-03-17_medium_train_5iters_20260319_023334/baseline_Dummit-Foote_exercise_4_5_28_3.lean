import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_28 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 105) (P : Sylow 3 G) [hP : P.Normal] :
  ∀ a b : G, a*b = b*a := by
  classical
  have hcyc : IsCyclic G := by
    exact Fintype.isCyclic_of_normal_sylow (G := G) (P := P) hG
  letI : CommGroup G := hcyc.commGroup
  intro a b
  exact mul_comm a b
