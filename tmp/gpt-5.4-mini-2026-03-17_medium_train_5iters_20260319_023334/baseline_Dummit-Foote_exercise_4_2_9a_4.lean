import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_9a {G : Type*} [Fintype G] [Group G] {p α : ℕ}
  (hp : p.Prime) (ha : α > 0) (hG : card G = p ^ α) :
  ∀ H : Subgroup G, H.index = p → H.Normal := by
  intro H hH
  classical
  have hnotTop : H ≠ ⊤ := by
    intro htop
    have hp1 : p = 1 := by
      simpa [htop] using hH
    exact hp.ne_one hp1
  have hmem : ∃ g : G, g ∉ H := by
    by_contra h
    have hall : ∀ g : G, g ∈ H := by
      intro g
      by_contra hg
      exact h ⟨g, hg⟩
    apply hnotTop
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      exact hall x
  rcases hmem with ⟨g, hg⟩
  let φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom
  have hdivG : Fintype.card φ.range ∣ p ^ α := by
    refine ⟨Fintype.card φ.ker, ?_⟩
    simpa [φ, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Fintype.card_range_mul_card_ker φ)
  rcases Nat.Prime.exists_eq_pow_of_dvd hp hdivG with ⟨k, hk⟩
  have hk' : Fintype.card φ.range = p ^ k := by
    simpa [eq_comm] using hk
  have hdivfact : Fintype.card φ.range ∣ p! := by
    have hsub : Fintype.card φ.range ∣ Fintype.card (Equiv.Perm (G ⧸ H)) := by
      exact Subgroup.card_dvd_card φ.range
    simpa [hcard_perm, hH, Subgroup.index] using hsub
  have hrange_ne_one : Fintype.card φ.range ≠ 1 := by
    intro h1
    haveI : Subsingleton φ.range := Fintype.card_eq_one.mp h1
    have hsub : (1 : φ.range) = ⟨φ g, ⟨g, rfl⟩⟩ := Subsingleton.elim _ _
    have hφg1 : φ g = 1 := by
      simpa using congrArg Subtype.val hsub
    have hfix : (φ g) (1 : G ⧸ H) = (1 : G ⧸ H) := by
      simpa using congrArg (fun f : Equiv.Perm (G ⧸ H) => f (1 : G ⧸ H)) hφg1
    have hg' : g ∈ H := by
      simpa [φ] using hfix
    exact hg hg'
  have hk_ne : k ≠ 0 := by
    intro hk0
    subst hk0
    simpa using hrange_ne_one
  have hpowfac : p ^ k ∣ p! := by
    simpa [hk'] using hdivfact
  have hk_le : k ≤ 1 := hp.pow_dvd_factorial.mp hpowfac
  have hk1 : k = 1 := by
    omega
  have hcardRange : Fintype.card φ.range = p := by
    simpa [hk1] using hk'
  have hmul : Fintype.card φ.range * Fintype.card φ.ker = Fintype.card G := by
    simpa [φ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Fintype.card_range_mul_card_ker φ)
  have h1 : p * Fintype.card φ.ker = Fintype.card G := by
    simpa [hcardRange, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have h2 : p * Fintype.card H = Fintype.card G := by
    simpa [hH, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using H.card_mul_index
  have hcardKerEq : Fintype.card φ.ker = Fintype.card H := by
    have hEqMul : p * Fintype.card φ.ker = p * Fintype.card H := by
      calc
        p * Fintype.card φ.ker = Fintype.card G := h1
        _ = p * Fintype.card H := by symm; exact h2
    exact Nat.mul_left_cancel hp.ne_zero hEqMul
  have hker_le : φ.ker ≤ H := by
    intro x hx
    have hx' : φ x = 1 := by
      simpa [MonoidHom.mem_ker] using hx
    have hx'' : (φ x) (1 : G ⧸ H) = (1 : G ⧸ H) := by
      simpa using congrArg (fun f : Equiv.Perm (G ⧸ H) => f (1 : G ⧸ H)) hx'
    simpa [φ] using hx''
  have hEq : φ.ker = H := Subgroup.eq_of_le_of_card_eq hker_le hcardKerEq
  simpa [hEq] using φ.ker_normal
