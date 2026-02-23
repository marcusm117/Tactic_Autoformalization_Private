import TacticFormalization

namespace TacticFormalization

section KernelImage

variable {G : Type*} [Group G]

-- `ker_img_reduce` unfolds `Function.Injective` into an elementwise goal.
example : Function.Injective (MonoidHom.id G) := by
  ker_img_reduce
  rename_i a b h
  exact h

-- `ker_img_reduce` also unfolds kernel membership.
example (f : G →* G) (x : G) : x ∈ f.ker ↔ f x = 1 := by
  ker_img_reduce

end KernelImage

section InverseCancellation

variable {G : Type*} [LeftCancelSemigroup G] {a b c : G}

-- `inv_cancel_group` turns a cancellation goal into a goal about a common-factor equality.
example (h : a * b = a * c) : b = c := by
  inv_cancel_group
  exact h

end InverseCancellation

section Normality

variable {G : Type*} [Group G]

-- `normal_conj` reduces normality to conjugation closure.
example : (⊤ : Subgroup G).Normal := by
  normal_conj
  intro g n hn
  exact Subgroup.mem_top _

end Normality

section Cosets

variable {G : Type*} [Group G] (H : Subgroup G) (a x : G)

open scoped Pointwise

-- `coset_index` uses `mem_leftCoset_iff` to rewrite coset membership.
example : x ∈ a • (H : Set G) ↔ a⁻¹ * x ∈ (H : Set G) := by
  coset_index

end Cosets

section Equivalence

variable {α : Type*} [s : Setoid α] {a b : α}

-- `eqv_partition` applies quotient soundness.
example (h : a ≈ b) : (⟦a⟧ : Quotient s) = ⟦b⟧ := by
  eqv_partition
  exact h

end Equivalence

section SubgroupVerification

variable {G : Type*} [Group G]

-- `subgroup_verify` helps scaffold `Subgroup` constructions from closure/identity/inverses.
def oneSubgroup : Subgroup G := by
  subgroup_verify
  · exact {x : G | x = 1}
  all_goals
    first
      | exact rfl
      | (intro x y hx hy; cases hx; cases hy; exact one_mul (1 : G))
      | (intro x hx; cases hx; exact inv_one)

example : (1 : G) ∈ oneSubgroup := by
  rfl

end SubgroupVerification

section BezoutGcdLcm

-- `bezout_gcd_lcm` knows the standard gcd*lcm relation (when applicable).
example (m n : ℕ) : Nat.gcd m n * Nat.lcm m n = m * n := by
  bezout_gcd_lcm

end BezoutGcdLcm

section OrderDivisibility

variable {G : Type*} [Group G] [Fintype G] (x : G)

-- `order_cyclic_div` applies the standard order-divides-card lemma.
example : orderOf x ∣ Fintype.card G := by
  order_cyclic_div

end OrderDivisibility

end TacticFormalization
