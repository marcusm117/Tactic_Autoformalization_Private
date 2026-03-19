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
    have hp1 : 1 = p := by
      simpa [htop] using hH
    exact hp.ne_one hp1.symm
  have hmem : ∃ g : G, g ∉ H := by
    by_contra h
    apply hnotTop
    ext x
    constructor
    · intro hx
      trivial
    · intro x
      by_contra hx
      exact h ⟨x, hx⟩
  rcases hmem with ⟨g, hg⟩
  let φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPerm
  have hφg : φ g ≠ 1 := by
    intro h
    exact hg (by
      simpa [φ] using congrArg (fun f : Equiv.Perm (G ⧸ H) => f (1 : G ⧸ H)) h)
  have hdivG : Fintype.card φ.range ∣ p ^ α := by
    refine ⟨Fintype.card φ.ker, ?_⟩
    simpa [φ, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using φ.card_range_mul_card_ker
  rcases hp.exists_eq_pow_of_dvd hdivG with ⟨k, hk⟩
  have hcardquot : Fintype.card (G ⧸ H) = p := by
    simpa [Subgroup.index] using hH
  have hdivfact : Fintype.card φ.range ∣ p! := by
    have hsub : Fintype.card φ.range ∣ Fintype.card (Equiv.Perm (G ⧸ H)) := Subgroup.card_dvd_card _
    simpa [hcardquot, Fintype.card_perm] using hsub
  have hcardRange_ne_one : Fintype.card φ.range ≠ 1 := by
    intro h1
    haveI : Subsingleton φ.range := Fintype.card_eq_one.mp h1
    have hmem1 : (1 : Equiv.Perm (G ⧸ H)) ∈ φ.range := by
      change ∃ x : G, φ x = 1
      exact ⟨1, by simp [φ]⟩
    have hmemg : φ g ∈ φ.range := by
      change ∃ x : G, φ x = φ g
      exact ⟨g, rfl⟩
    have hEq : (⟨φ g, hmemg⟩ : φ.range) = ⟨1, hmem1⟩ := Subsingleton.elim _ _
    have : φ g = 1 := by
      simpa using congrArg Subtype.val hEq
    exact hφg this
  have hk_ne : k ≠ 0 := by
    intro hk0
    subst hk0
    have : Fintype.card φ.range = 1 := by simpa using hk
    exact hcardRange_ne_one this
  have hpowfac : p ^ k ∣ p! := by
    simpa [hk] using hdivfact
  have hk_le : k ≤ 1 := by
    exact hp.pow_dvd_factorial.mp hpowfac
  have hk1 : k = 1 := by
    omega
  have hcardRange : Fintype.card φ.range = p := by
    simpa [hk1] using hk
  have hcardKerEq : Fintype.card φ.ker = Fintype.card H := by
    have h1 : p * Fintype.card φ.ker = p ^ α := by
      simpa [φ, hcardRange, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using φ.card_range_mul_card_ker
    have h2 : p * Fintype.card H = p ^ α := by
      simpa [hG, hH, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using H.card_mul_index
    exact Nat.mul_left_cancel hp.ne_zero (by
      calc
        p * Fintype.card φ.ker = p ^ α := h1
        _ = p * Fintype.card H := by symm; exact h2)
  have hker_le : φ.ker ≤ H := by
    intro x hx
    have hx' : φ x = 1 := by
      simpa [MonoidHom.mem_ker] using hx
    have hx'' : (φ x) (1 : G ⧸ H) = 1 := by
      simpa using congrArg (fun f : Equiv.Perm (G ⧸ H) => f (1 : G ⧸ H)) hx'
    simpa [φ] using hx''
  have hEq : φ.ker = H := Subgroup.eq_of_le_of_card_eq hker_le hcardKerEq
  simpa [hEq] using (φ.ker_normal)
