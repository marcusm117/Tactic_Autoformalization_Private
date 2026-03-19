import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_16 {p q r : ℕ} {G : Type*} [Group G]
  [Fintype G]  (hpqr : p < q ∧ q < r)
  (hpqr1 : p.Prime ∧ q.Prime ∧ r.Prime)(hG : card G = p*q*r) :
  (∃ (P : Sylow p G), P.Normal) ∨ (∃ (P : Sylow q G), P.Normal) ∨ (∃ (P : Sylow r G), P.Normal) := by
  classical
  rcases hpqr with ⟨hpq, hqr⟩
  rcases hpqr1 with ⟨hp, hq, hr⟩
  have hpne : p ≠ q := by omega
  have hqne : q ≠ r := by omega
  have hrne : p ≠ r := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let nr := Nat.card (Sylow r G)
  let nq := Nat.card (Sylow q G)
  have hnr_dvd : nr ∣ p * q := by
    simpa [nr, hG, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Sylow.card_sylow_dvd_card (p := r) (G := G))
  have hnr_mod : nr ≡ 1 [MOD r] := by
    simpa [nr] using (Sylow.card_sylow_modEq_one (p := r) (G := G))
  have hnr_cases : nr = 1 ∨ nr = p ∨ nr = q ∨ nr = p * q := by
    exact Nat.dvd_prime_mul hp hq hnr_dvd
  rcases hnr_cases with rfl | rfl | rfl | hnrpq
  · exact Or.inr <| Or.inr <| by
      exact (Sylow.normal_of_card_eq_one (p := r) (G := G) rfl)
  · have hlt : nr < r := by simpa [nr] using hpq.trans hqr
    have := hnr_mod.eq_of_lt hlt
    simp at this
  · have hlt : nr < r := by simpa [nr] using hqr
    have := hnr_mod.eq_of_lt hlt
    simp at this
  · have hq_dvd : nq ∣ p * r := by
      simpa [nq, hG, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Sylow.card_sylow_dvd_card (p := q) (G := G))
    have hq_mod : nq ≡ 1 [MOD q] := by
      simpa [nq] using (Sylow.card_sylow_modEq_one (p := q) (G := G))
    have hq_cases : nq = 1 ∨ nq = p ∨ nq = r ∨ nq = p * r := by
      exact Nat.dvd_prime_mul hp hr hq_dvd
    have hnq_ge : r ≤ nq := by
      rcases hq_cases with rfl | rfl | rfl | rfl
      · exact le_of_lt hqr
      · have hlt : nq < q := by simpa [nq] using hpq
        have := hq_mod.eq_of_lt hlt
        simp at this
      · exact le_rfl
      · exact le_of_lt (by omega)
    have hqcount : Fintype.card {x : G // orderOf x = q} = nq * (q - 1) := by
      simpa [nq] using (Sylow.card_eq_card_sylow_mul_card (p := q) (G := G))
    have hrcount : Fintype.card {x : G // orderOf x = r} = p * q * (r - 1) := by
      simpa [nr, hnrpq, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Sylow.card_eq_card_sylow_mul_card (p := r) (G := G))
    have hqgt : p * q < nq * (q - 1) := by
      have hp_le : p ≤ q - 1 := by omega
      have h1 : p * q ≤ (q - 1) * q := by
        exact Nat.mul_le_mul_right q hp_le
      have hqpos : 0 < q - 1 := by omega
      have h2 : (q - 1) * q < r * (q - 1) := by
        simpa [Nat.mul_comm] using Nat.mul_lt_mul_right hqpos hqr
      have h3 : r * (q - 1) ≤ nq * (q - 1) := by
        exact Nat.mul_le_mul_right (q - 1) hnq_ge
      exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) h3
    have hqgt' : p * q + 1 ≤ nq * (q - 1) := Nat.succ_le_of_lt hqgt
    have hsum_gt : p * q * r < 1 + p * q * (r - 1) + nq * (q - 1) := by
      have htmp : p * q * r + 2 ≤ 1 + p * q * (r - 1) + nq * (q - 1) := by
        have htmp1 : 1 + p * q * (r - 1) + (p * q + 1) ≤ 1 + p * q * (r - 1) + nq * (q - 1) := by
          exact Nat.add_le_add_left hqgt' _
        have hmul : 1 + p * q * (r - 1) + (p * q + 1) = p * q * r + 2 := by
          simp [Nat.mul_add, Nat.sub_add_cancel hr.one_le, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        simpa [hmul] using htmp1
      omega
    have hcard_le :
        Fintype.card (PUnit ⊕ {x : G // orderOf x = r} ⊕ {x : G // orderOf x = q}) ≤ p * q * r := by
      refine Fintype.card_le_of_injective ?f ?_
      · intro x
        rcases x with _ | x | x
        · exact (1 : G)
        · exact x.1
        · exact x.1
      · intro x y hxy
        cases x <;> cases y <;> simp at hxy
        · rfl
        · exfalso
          have := congrArg orderOf hxy
          simp [orderOf_one] at this
        · exfalso
          have := congrArg orderOf hxy
          simp [orderOf_one] at this
        · subst hxy
          rfl
        · exfalso
          have := congrArg orderOf hxy
          simp [x.2, y.2] at this
        · exfalso
          have := congrArg orderOf hxy
          simp [orderOf_one] at this
        · exfalso
          have := congrArg orderOf hxy
          simp [x.2, y.2] at this
        · exfalso
          have := congrArg orderOf hxy
          simp [orderOf_one] at this
        · exfalso
          have := congrArg orderOf hxy
          simp [x.2, y.2] at this
    have hcard_eq :
        Fintype.card (PUnit ⊕ {x : G // orderOf x = r} ⊕ {x : G // orderOf x = q}) =
          1 + p * q * (r - 1) + nq * (q - 1) := by
      simp [hrcount, hqcount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    have hlt : p * q * r < Fintype.card (PUnit ⊕ {x : G // orderOf x = r} ⊕ {x : G // orderOf x = q}) := by
      simpa [hcard_eq] using hsum_gt
    exact (not_lt_of_ge hcard_le) hlt
