import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_9a {G : Type*} [Fintype G] [Group G] {p α : ℕ}
  (hp : p.Prime) (ha : α > 0) (hG : card G = p ^ α) :
  ∀ H : Subgroup G, H.index = p → H.Normal := by
  intro H hH
  classical
  let φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPerm G (G ⧸ H)
  let I : Subgroup (Equiv.Perm (G ⧸ H)) := φ.range
  have hneqtop : H ≠ ⊤ := by
    intro htop
    simpa [htop] using hH
  rcases (Subgroup.ne_top_iff_exists_not_mem.mp hneqtop) with ⟨g, hg⟩
  have hφg : φ g ≠ 1 := by
    intro h
    exact hg (by
      simpa [φ] using congrArg (fun f : Equiv.Perm (G ⧸ H) => f (1 : G ⧸ H)) h)
  have hdivG : Fintype.card I ∣ p ^ α := by
    refine ⟨Fintype.card φ.ker, ?_⟩
    simpa [I, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using φ.card_range_mul_card_ker
  rcases hp.exists_eq_pow_of_dvd hdivG with ⟨k, hk⟩
  have hk_ne : k ≠ 0 := by
    intro hk0
    subst hk0
    have hcard1 : Fintype.card I = 1 := by simpa using hk
    haveI : Subsingleton I := Fintype.card_eq_one.mp hcard1
    exact hφg (Subsingleton.elim _ _)
  have hpowfac : p ^ k ∣ p! := by
    simpa [I, hk, hH, Fintype.card_perm] using (Subgroup.card_dvd_card I)
  have hk_le : k ≤ 1 := by
    have htmp := hp.pow_dvd_factorial.mp hpowfac
    omega
  have hk1 : k = 1 := by omega
  have hcardI : Fintype.card I = p := by
    simpa [hk1] using hk
  have hker_le : φ.ker ≤ H := by
    intro x hx
    have hx' : φ x = 1 := by
      simpa [MonoidHom.mem_ker] using hx
    exact by
      simpa [φ] using congrArg (fun f : Equiv.Perm (G ⧸ H) => f (1 : G ⧸ H)) hx'
  have hcardKer : Fintype.card φ.ker = Fintype.card H := by
    have h1 : Fintype.card φ.ker * p = Fintype.card G := by
      simpa [hcardI, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using φ.card_range_mul_card_ker
    have h2 : Fintype.card H * p = Fintype.card G := by
      simpa [hH, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using H.card_mul_index
    omega
  have hEq : φ.ker = H := Subgroup.eq_of_le_of_card_eq hker_le hcardKer
  simpa [hEq] using φ.ker_normal
