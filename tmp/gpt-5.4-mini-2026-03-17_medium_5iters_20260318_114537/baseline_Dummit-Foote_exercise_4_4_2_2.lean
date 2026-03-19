import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  classical
  have hpprime : Nat.Prime (p : ℕ) := p.2
  have hqprime : Nat.Prime (q : ℕ) := q.2
  have hp_card : (p : ℕ) ∣ Fintype.card G := by
    rw [hG]
    exact dvd_mul_of_dvd_left (dvd_refl (p : ℕ)) (q : ℕ)
  have hq_card : (q : ℕ) ∣ Fintype.card G := by
    rw [hG]
    exact dvd_mul_of_dvd_right (dvd_refl (q : ℕ)) (p : ℕ)
  obtain ⟨a, ha⟩ := Nat.Prime.exists_orderOf_eq hpprime hp_card
  obtain ⟨b, hb⟩ := Nat.Prime.exists_orderOf_eq hqprime hq_card
  have hcop : Coprime (p : ℕ) (q : ℕ) := by
    refine hpprime.coprime_iff_not_dvd.mpr ?_
    intro hpqdiv
    exact hpq (Subtype.ext (hpprime.eq_of_dvd_of_prime hpqdiv hqprime))
  have hcop' : Coprime (orderOf a) (orderOf b) := by
    simpa [ha, hb] using hcop
  have hcomm : Commute a b := ⟨mul_comm a b⟩
  have horder : orderOf (a * b) = p * q := by
    simpa [ha, hb] using hcomm.orderOf_mul hcop'
  exact IsCyclic.of_exists_orderOf_eq_card ⟨a * b, by simpa [hG] using horder⟩
