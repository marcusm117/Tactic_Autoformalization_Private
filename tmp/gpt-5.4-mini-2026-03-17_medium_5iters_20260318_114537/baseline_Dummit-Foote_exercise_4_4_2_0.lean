import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  classical
  have hp_card : p ∣ Fintype.card G := by
    rw [hG]
    exact dvd_mul_of_dvd_right (dvd_refl p) q
  have hq_card : q ∣ Fintype.card G := by
    rw [hG]
    exact dvd_mul_of_dvd_left (dvd_refl q) p
  obtain ⟨a, ha⟩ := p.2.exists_orderOf_eq hp_card
  obtain ⟨b, hb⟩ := q.2.exists_orderOf_eq hq_card
  have hcop : Coprime p q := p.2.coprime_iff_not_dvd.mpr (by
    intro hpqdiv
    exact hpq <| Subtype.ext (p.2.eq_of_dvd_of_prime hpqdiv q.2))
  have hcop' : Coprime (orderOf a) (orderOf b) := by
    simpa [ha, hb] using hcop
  have hcomm : Commute a b := ⟨mul_comm a b⟩
  have horder : orderOf (a * b) = p * q := by
    simpa [ha, hb] using hcomm.orderOf_mul hcop'
  exact IsCyclic.of_exists_orderOf_eq_card ⟨a * b, by simpa [hG] using horder⟩
