import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_8_1 {G : Type*} [Group G]
  (a b : G) : closure ({a, b} : Set G) = Subgroup.closure {b*a*b^2, b*a*b^3} := by
  refine _root_.le_antisymm ?_ ?_
  · refine Subgroup.closure_le.2 ?_
    intro x hx
    have hx' : x = a ∨ x = b := by
      simpa using hx
    have h1 : b * a * b ^ 2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
      exact Subgroup.subset_closure (by simp)
    have h2 : b * a * b ^ 3 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
      exact Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
      have hmul : (b * a * b ^ 2)⁻¹ * (b * a * b ^ 3) ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        mul_mem (inv_mem h1) h2
      have hEq : (b * a * b ^ 2)⁻¹ * (b * a * b ^ 3) = b := by
        group
      simpa [hEq] using hmul
    rcases hx' with rfl | rfl
    · have hbInv : b⁻¹ ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        inv_mem hb
      have hbInv2 : (b⁻¹)^2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
        simpa [pow_two] using mul_mem hbInv hbInv
      have hmul : b⁻¹ * (b * a * b ^ 2) * (b⁻¹)^2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        mul_mem (mul_mem hbInv h1) hbInv2
      have hEq : b⁻¹ * (b * a * b ^ 2) * (b⁻¹)^2 = a := by
        group
      simpa [hEq] using hmul
    · exact hb
  · refine Subgroup.closure_le.2 ?_
    intro x hx
    have hx' : x = b * a * b ^ 2 ∨ x = b * a * b ^ 3 := by
      simpa using hx
    have ha : a ∈ Subgroup.closure ({a, b} : Set G) := by
      exact Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({a, b} : Set G) := by
      exact Subgroup.subset_closure (by simp)
    have hb2 : b ^ 2 ∈ Subgroup.closure ({a, b} : Set G) := by
      simpa [pow_two] using mul_mem hb hb
    have hb3 : b ^ 3 ∈ Subgroup.closure ({a, b} : Set G) := by
      simpa [pow_succ, pow_two, mul_assoc] using mul_mem hb2 hb
    have hgen1 : b * a * b ^ 2 ∈ Subgroup.closure ({a, b} : Set G) := by
      simpa [mul_assoc] using mul_mem (mul_mem hb ha) hb2
    have hgen2 : b * a * b ^ 3 ∈ Subgroup.closure ({a, b} : Set G) := by
      simpa [mul_assoc] using mul_mem (mul_mem hb ha) hb3
    rcases hx' with rfl | rfl
    · exact hgen1
    · exact hgen2
