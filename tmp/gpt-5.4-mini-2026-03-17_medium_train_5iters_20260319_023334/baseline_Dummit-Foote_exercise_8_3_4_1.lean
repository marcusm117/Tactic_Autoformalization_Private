import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_4 {n : ℤ} {r s : ℚ}
  (h : r^2 + s^2 = n) :
  ∃ a b : ℤ, a^2 + b^2 = n := by
  classical
  have hr : (r : ℚ) = (r.num : ℚ) / r.den := by
    simpa using (Rat.num_div_den r).symm
  have hs : (s : ℚ) = (s.num : ℚ) / s.den := by
    simpa using (Rat.num_div_den s).symm
  have hq : ((r.num : ℚ) / r.den)^2 + ((s.num : ℚ) / s.den)^2 = n := by
    simpa [hr, hs] using h
  have hmulQ :
      ((r.num * s.den : ℤ)^2 + (s.num * r.den : ℤ)^2 : ℚ) =
        n * (r.den * s.den : ℚ)^2 := by
    have hq' := hq
    field_simp [sq] at hq'
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hq'
  have hmul :
      (r.num * s.den : ℤ)^2 + (s.num * r.den : ℤ)^2 =
        n * (r.den * s.den : ℤ)^2 := by
    exact_mod_cast hmulQ
  exact Int.exists_sq_add_sq_of_mul_sq ⟨r.num * s.den, s.num * r.den, hmul⟩
