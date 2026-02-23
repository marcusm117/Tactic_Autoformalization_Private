import Mathlib

namespace TacticFormalization

/-
Kernel–image reduction via homomorphisms (used in 14 proofs)
CASES:
- Proposition 2.5.3
- Proposition 2.5.8
- Corollary 2.5.9
- Proposition 2.5.11
- Lemma 2.6.2
- Corollary 2.8.13
- Proposition 2.8.18
- Proposition 2.10.4
- Proof of Theorem 2.10.5 (Correspondence Theorem)
- Proposition 2.11.4
- Corollary 2.12.3
- Proof of Theorem 2.12.2
- Lemma 2.12.8
- Theorem 2.12.10 (First Isomorphism Theorem)
-/
syntax (name := kerImgReduce) "ker_img_reduce" : tactic
macro_rules
  | `(tactic| ker_img_reduce) =>
    `(tactic|
      first
        | -- turn membership in kernel into an equation
          (rw [Subsemiring.mem_carrier] <;> try rfl)
        | (rw [Submodule.mem_carrier] <;> try rfl)
        | (rw [Subgroup.mem_carrier] <;> try rfl)
        | (rw [AddSubgroup.mem_carrier] <;> try rfl)
        | -- unfold kernel/image/fibre when present
          (rw [MonoidHom.mem_ker] <;> try rfl)
        | (rw [AddMonoidHom.mem_ker] <;> try rfl)
        | (rw [LinearMap.mem_ker] <;> try rfl)
        | (rw [Set.mem_image] <;> try rfl)
        | (rw [Set.mem_preimage] <;> try rfl)
        | -- reduce injective/surjective to elementwise statements
          (rw [Function.Injective] <;> intro <;> intro <;> intro)
        | (rw [Function.Surjective] <;> intro)
        | -- reduce isomorphism to bijective
          (rw [Function.Bijective] <;> constructor)
    )

/-
Inverse-cancellation algebra in groups (used in 9 proofs)
CASES:
- Proposition 2.2.3 (Cancellation Law)
- Proposition 2.5.3
- Proposition 2.5.8
- Corollary 2.5.9
- Proposition 2.5.11
- Proposition 2.8.17
- Proposition 2.10.4
- Proof of Theorem 2.10.5
- Proposition 2.11.4
-/
syntax (name := invCancelGroup) "inv_cancel_group" : tactic
macro_rules
  | `(tactic| inv_cancel_group) =>
    `(tactic|
      first
        | -- cancel a common left factor
          (apply mul_left_cancel)
        | -- cancel a common right factor
          (apply mul_right_cancel)
        | -- cancel in additive groups
          (apply add_left_cancel)
        | (apply add_right_cancel)
        | -- normalize inverse products when they appear
          (rw [inv_mul_cancel_left])
        | (rw [mul_inv_cancel_left])
        | (rw [inv_mul_cancel_right])
        | (rw [mul_inv_cancel_right])
    )

/-
Normality and conjugation invariance (used in 9 proofs)
CASES:
- Proposition 2.5.11
- Proposition 2.8.17
- Proposition 2.8.18
- Proposition 2.10.4
- Proof of Theorem 2.10.5
- Proposition 2.11.4
- Proposition 2.11.5
- Proof of Theorem 2.12.2
- Lemma 2.12.5
-/
syntax (name := normalConj) "normal_conj" : tactic
macro_rules
  | `(tactic| normal_conj) =>
    `(tactic|
      -- Reduce normality to conjugation invariance:
      -- `⊢ N.Normal` becomes `⊢ ∀ g n, n ∈ N → g * n * g⁻¹ ∈ N`.
      refine ⟨?_⟩
    )

/-
Cosets + counting / index arguments (used in 9 proofs)
CASES:
- Corollary 2.8.3
- Lemma 2.8.7
- Corollary 2.8.13
- Proposition 2.8.14
- Proposition 2.8.17
- Proposition 2.11.4
- Proof of Theorem 2.12.2
- Lemma 2.12.5
- Theorem 2.12.10
-/
syntax (name := cosetIndex) "coset_index" : tactic
macro_rules
  | `(tactic| coset_index) =>
    `(tactic|
      first
        | -- unfold left coset membership
          (rw [mem_leftCoset_iff])
        | -- unfold right coset membership
          (rw [mem_rightCoset_iff])
        | -- reduce equality of cosets to membership
          (ext x; constructor <;> intro hx)
        | -- reduce divisibility goals to existence of a multiplier
          (rw [dvd_iff_exists_eq_mul_left] <;> intro)
        | (rw [dvd_iff_exists_eq_mul_right] <;> intro)
    )

/-
Equivalence classes / partitions (used in 6 proofs)
CASES:
- Proposition 2.7.4
- Lemma 2.7.6
- Corollary 2.8.3
- Proposition 2.8.14
- Proposition 2.8.17
- Lemma 2.9.6
-/
syntax (name := eqvPartition) "eqv_partition" : tactic
macro_rules
  | `(tactic| eqv_partition) =>
    `(tactic|
      first
        | -- unfold Setoid equivalence
          (rw [Setoid.r] <;> try intro)
        | -- work with Quot soundness
          (apply Quot.sound)
        | -- work with Quotient soundness
          (apply Quotient.sound)
        | -- reduce membership in a set of classes to existence
          (rw [Set.mem_setOf] <;> try intro)
        | (rw [Set.mem_image] <;> try intro)
        | -- split typical iff goals
          (constructor)
    )

/-
Subgroup verification (closure/identity/inverses) (used in 4 proofs)
CASES:
- Theorem 2.3.3
- Proposition 2.4.2
- Proposition 2.10.4
- Proposition 2.11.4
-/
syntax (name := subgroupVerify) "subgroup_verify" : tactic
macro_rules
  | `(tactic| subgroup_verify) =>
    `(tactic|
      first
        | -- build a subgroup by giving the three fields
          (refine
            { carrier := ?_
              one_mem' := ?_
              mul_mem' := ?_
              inv_mem' := ?_ } )
        | -- for AddSubgroup-like goals
          (refine
            { carrier := ?_
              zero_mem' := ?_
              add_mem' := ?_
              neg_mem' := ?_ } )
        | -- common subgoals
          (intro x hx)
        | (intro x y hx hy)
    )

/-
Bezout / gcd–lcm divisibility trick (used in 3 proofs)
CASES:
- Proposition 2.3.5
- Corollary 2.3.7
- Corollary 2.3.9
-/
syntax (name := bezoutGcdLcm) "bezout_gcd_lcm" : tactic
macro_rules
  | `(tactic| bezout_gcd_lcm) =>
    `(tactic|
      first
        | -- turn divisibility into an existence goal
          (rw [dvd_iff_exists_eq_mul_left] <;> intro)
        | (rw [dvd_iff_exists_eq_mul_right] <;> intro)
        | -- rewrite lcm/gcd product relation when available
          (rw [Nat.gcd_mul_lcm])
        | (rw [Int.gcd_mul_lcm])
    )

/-
Order divisibility via cyclic subgroups (Lagrange-style) (used in 3 proofs)
CASES:
- Corollary 2.8.10
- Corollary 2.8.11
- Proposition 2.11.5
-/
syntax (name := orderCyclicDiv) "order_cyclic_div" : tactic
macro_rules
  | `(tactic| order_cyclic_div) =>
    `(tactic|
      first
        | -- reduce "x ∈ subgroup generated by g" to an exponent witness
          (rw [Subgroup.mem_zpowers_iff])
        | -- common: show orderOf g ∣ Fintype.card G
          (apply orderOf_dvd_card)
        | -- prime order group: reduce to existence of generator via orderOf
          (intro a)
        | -- unfold cyclic subgroup
          (rw [Subgroup.zpowers_eq_closure])
        | -- turn divisibility into existence
          (rw [dvd_iff_exists_eq_mul_left] <;> intro)
        | (rw [dvd_iff_exists_eq_mul_right] <;> intro)
    )

end TacticFormalization
