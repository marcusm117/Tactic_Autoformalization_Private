import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  classical
  have hpq_nat : (p : ℕ) ≠ (q : ℕ) := by
    intro h
    apply hpq
    exact Subtype.ext h
  have hpdvd : (p : ℕ) ∣ card G := by
    rw [hG]
    exact ⟨(q : ℕ), by simp⟩
  have hqdvd : (q : ℕ) ∣ card G := by
    rw [hG]
    exact ⟨(p : ℕ), by simp [Nat.mul_comm]⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card p.2 hpdvd
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card q.2 hqdvd
  have hcop : Nat.Coprime (p : ℕ) (q : ℕ) := by
    refine p.2.coprime_iff_not_dvd.mpr ?_
    intro h
    exact hpq_nat ((p.2.dvd_iff_eq q.2).mp h)
  have hcomm : Commute a b := by
    exact mul_comm a b
  have hab : orderOf (a * b) = (p : ℕ) * (q : ℕ) := by
    have hcop' : Nat.Coprime (orderOf a) (orderOf b) := by
      simpa [ha, hb] using hcop
    simpa [ha, hb] using hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop'
  exact isCyclic_of_orderOf_eq_card (a * b) (by simpa [hG] using hab)
