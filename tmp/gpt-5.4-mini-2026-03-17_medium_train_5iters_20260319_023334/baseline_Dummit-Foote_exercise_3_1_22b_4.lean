import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_1_22b {G : Type*} [Group G] (I : Type*) [Nonempty I]
  (H : I → Subgroup G) (hH : ∀ i : I, Normal (H i)) :
  Normal (⨅ (i : I), H i):= by
  refine ⟨fun x hx g => ?_⟩
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro i
  exact (hH i).conj_mem (hx i) g
