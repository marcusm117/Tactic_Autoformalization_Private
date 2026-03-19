import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_8_1 {G : Type*} [Group G]
  (a b : G) : closure ({a, b} : Set G) = Subgroup.closure {b*a*b^2, b*a*b^3} := by
  apply _root_.le_antisymm
  · change
      Subgroup.closure ({a, b} : Set G) ≤
        Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)
    refine Subgroup.closure_le.2 ?_
    intro x hx
    have h1 : b * a * b ^ 2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
      Subgroup.subset_closure (by simp)
    have h2 : b * a * b ^ 3 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
      have h :
          (b * a * b ^ 2)⁻¹ * (b * a * b ^ 3) ∈
            Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        (Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)).mul_mem
          ((Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)).inv_mem h1) h2
      simpa [pow_succ, pow_two, mul_assoc] using h
    have ha : a ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
      have hb2 : b ^ 2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        (Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)).pow_mem hb 2
      have h :
          b⁻¹ * (b * a * b ^ 2) * (b ^ 2)⁻¹ ∈
            Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        (Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)).mul_mem
          ((Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)).mul_mem
            ((Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)).inv_mem hb) h1)
          ((Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G)).inv_mem hb2)
      simpa [pow_two, mul_assoc] using h
    simp at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · change
      Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) ≤
        Subgroup.closure ({a, b} : Set G)
    refine Subgroup.closure_le.2 ?_
    intro x hx
    have ha : a ∈ Subgroup.closure ({a, b} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({a, b} : Set G) :=
      Subgroup.subset_closure (by simp)
    simp at hx
    rcases hx with rfl | rfl
    · exact
        (Subgroup.closure ({a, b} : Set G)).mul_mem
          ((Subgroup.closure ({a, b} : Set G)).mul_mem hb ha)
          ((Subgroup.closure ({a, b} : Set G)).pow_mem hb 2)
    · exact
        (Subgroup.closure ({a, b} : Set G)).mul_mem
          ((Subgroup.closure ({a, b} : Set G)).mul_mem hb ha)
          ((Subgroup.closure ({a, b} : Set G)).pow_mem hb 3)
