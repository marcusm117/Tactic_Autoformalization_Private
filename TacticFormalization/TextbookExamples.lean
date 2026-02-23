import TacticFormalization

namespace TacticFormalization

/-!
Concrete formalizations of several statements from `group.pdf` that were tagged as using the
common proof-tactic categories, with proofs that invoke our generated tactics.

These are intentionally small: the goal is to demonstrate that the tactic macros can “factor out”
boilerplate steps while leaving the problem-specific math to the surrounding proof.
-/

section Proposition_2_2_3_Cancellation

variable {G : Type*} [Group G]

-- Proposition 2.2.3 (Cancellation Law), left-cancellation part.
theorem prop_2_2_3_left {a b c : G} (h : a * b = a * c) : b = c := by
  inv_cancel_group
  exact h

-- Proposition 2.2.3 (Cancellation Law), right-cancellation part.
theorem prop_2_2_3_right {a b c : G} (h : b * a = c * a) : b = c := by
  exact mul_right_cancel h

-- Proposition 2.2.3: if `a*b = a` then `b = 1`.
theorem prop_2_2_3_left_id {a b : G} (h : a * b = a) : b = 1 := by
  inv_cancel_group
  -- goal is now `a * b = a * 1`
  calc
    a * b = a := h
    _ = a * 1 := by rw [mul_one]

-- Proposition 2.2.3: if `b*a = a` then `b = 1`.
theorem prop_2_2_3_right_id {a b : G} (h : b * a = a) : b = 1 := by
  have h' : b * a = 1 * a := by
    calc
      b * a = a := h
      _ = 1 * a := by rw [one_mul]
  exact mul_right_cancel h'

end Proposition_2_2_3_Cancellation

section Proposition_2_5_8_KernelCharacterization

variable {G G' : Type*} [Group G] [Group G']

-- Proposition 2.5.8 (one common formulation):
-- `φ(a) = φ(b)` iff `a⁻¹*b ∈ ker φ`.
theorem prop_2_5_8_map_eq_iff_mul_mem_ker (φ : G →* G') (a b : G) :
    φ a = φ b ↔ a⁻¹ * b ∈ φ.ker := by
  constructor
  · intro h
    -- Reduce kernel membership to an equation in the codomain.
    ker_img_reduce
    -- goal: `φ (a⁻¹ * b) = 1`
    have : (φ a)⁻¹ * φ b = 1 := by
      calc
        (φ a)⁻¹ * φ b = (φ a)⁻¹ * φ a := by simpa [h.symm]
        _ = 1 := by rw [inv_mul_cancel]
    calc
      φ (a⁻¹ * b) = φ (a⁻¹) * φ b := by
        simpa using (φ.map_mul a⁻¹ b)
      _ = (φ a)⁻¹ * φ b := by rw [φ.map_inv a]
      _ = 1 := this
  · intro h
    have hk : φ (a⁻¹ * b) = 1 := (MonoidHom.mem_ker).1 h
    have : (φ a)⁻¹ * φ b = 1 := by
      calc
        (φ a)⁻¹ * φ b = φ (a⁻¹) * φ b := by rw [φ.map_inv a]
        _ = φ (a⁻¹ * b) := by
          -- reverse of `map_mul`
          symm
          simpa using (φ.map_mul a⁻¹ b)
        _ = 1 := hk
    -- Multiply the equation on the left by `φ a` to recover `φ a = φ b`.
    have h' : φ a * ((φ a)⁻¹ * φ b) = φ a * 1 := by
      simpa using congrArg (fun t => φ a * t) this
    rw [mul_inv_cancel_left] at h'
    rw [mul_one] at h'
    exact h'.symm

end Proposition_2_5_8_KernelCharacterization

section Proposition_2_5_11_KernelNormal

variable {G G' : Type*} [Group G] [Group G']

-- Proposition 2.5.11: the kernel of a homomorphism is a normal subgroup.
theorem prop_2_5_11_kernel_normal (φ : G →* G') : φ.ker.Normal := by
  normal_conj
  intro n hn g
  -- goal: `g * n * g⁻¹ ∈ ker φ`
  ker_img_reduce
  -- goal: `φ (g * n * g⁻¹) = 1`
  have hn' : φ n = 1 := (MonoidHom.mem_ker).1 hn
  calc
    φ (g * n * g⁻¹) = φ ((g * n) * g⁻¹) := by rw [mul_assoc]
    _ = φ (g * n) * φ g⁻¹ := by
      simpa using (φ.map_mul (g * n) g⁻¹)
    _ = (φ g * φ n) * (φ g)⁻¹ := by
      rw [φ.map_mul g n, φ.map_inv g]
    _ = (φ g * 1) * (φ g)⁻¹ := by rw [hn']
    _ = 1 := by
      rw [mul_one]
      rw [mul_inv_cancel]

end Proposition_2_5_11_KernelNormal

section Corollary_2_8_10_OrderDivides

variable {G : Type*} [Group G] [Fintype G] (x : G)

-- Corollary 2.8.10: the order of an element divides the order of a finite group.
theorem cor_2_8_10_order_dvd_card : orderOf x ∣ Fintype.card G := by
  order_cyclic_div

end Corollary_2_8_10_OrderDivides

end TacticFormalization
