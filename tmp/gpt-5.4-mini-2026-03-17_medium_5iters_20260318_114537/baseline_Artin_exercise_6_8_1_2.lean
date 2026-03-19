import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_8_1 {G : Type*} [Group G]
  (a b : G) : closure ({a, b} : Set G) = Subgroup.closure {b*a*b^2, b*a*b^3} := by
  refine _root_.le_antisymm ?_ ?_
  · exact (Subgroup.closure_le (K := Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G))).2 ?_
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · have h1 : b * a * b ^ 2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
        exact Subgroup.subset_closure (by simp)
      have h2 : b * a * b ^ 3 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
        exact Subgroup.subset_closure (by simp)
      have hb : b ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
        have hmul : (b * a * b ^ 2)⁻¹ * (b * a * b ^ 3) ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
          mul_mem (inv_mem h1) h2
        have hEq : (b * a * b ^ 2)⁻¹ * (b * a * b ^ 3) = b := by
          group
        simpa [hEq] using hmul
      have hbInv : b⁻¹ ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        inv_mem hb
      have hbInv2 : b⁻¹ * b⁻¹ ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        mul_mem hbInv hbInv
      have hmul : b⁻¹ * (b * a * b ^ 2) * (b⁻¹ * b⁻¹) ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        mul_mem (mul_mem hbInv h1) hbInv2
      have hEq : b⁻¹ * (b * a * b ^ 2) * (b⁻¹ * b⁻¹) = a := by
        group
      simpa [hEq] using hmul
    · exact hb
  · exact (Subgroup.closure_le (K := Subgroup.closure ({a, b} : Set G))).2 ?_
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · have ha : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
      have hb : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
      have hb2 : b ^ 2 ∈ Subgroup.closure ({a, b} : Set G) := by
        simpa using Subgroup.pow_mem hb 2
      have hmul : b * a * b ^ 2 ∈ Subgroup.closure ({a, b} : Set G) := by
        simpa [mul_assoc] using mul_mem (mul_mem hb ha) hb2
      exact hmul
    · have ha : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
      have hb : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
      have hb3 : b ^ 3 ∈ Subgroup.closure ({a, b} : Set G) := by
        simpa using Subgroup.pow_mem hb 3
      have hmul : b * a * b ^ 3 ∈ Subgroup.closure ({a, b} : Set G) := by
        simpa [mul_assoc] using mul_mem (mul_mem hb ha) hb3
      exact hmul
