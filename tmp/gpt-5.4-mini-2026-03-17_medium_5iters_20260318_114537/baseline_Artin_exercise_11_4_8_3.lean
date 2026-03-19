import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_8 (p : ℕ) (hp : Prime p) (n : ℕ) (hn : n > 0) :
  Irreducible (X ^ n - (p : Polynomial ℚ) : Polynomial ℚ) := by
  have hZ : Irreducible (X ^ n - (p : Polynomial ℤ)) := by
    have hE : Polynomial.IsEisenstein (p : ℤ) (X ^ n - (p : Polynomial ℤ)) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa using (monic_X_pow n : (X ^ n : Polynomial ℤ).Monic)
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          simp
        · simp [Polynomial.coeff_X_pow, hi0, hn.ne']
      · intro h
        rcases h with ⟨k, hk⟩
        have hk' : (p : ℤ) * ((p : ℤ) * k) = (p : ℤ) * (-1 : ℤ) := by
          calc
            (p : ℤ) * ((p : ℤ) * k) = (p : ℤ) ^ 2 * k := by ring
            _ = - (p : ℤ) := hk
            _ = (p : ℤ) * (-1 : ℤ) := by ring
        have hk1 : (p : ℤ) * k = -1 := by
          exact mul_left_cancel₀ hp.cast_prime.ne_zero hk'
        have hdiv1 : (p : ℤ) ∣ 1 := by
          refine ⟨-k, ?_⟩
          calc
            (p : ℤ) * (-k) = -((p : ℤ) * k) := by ring
            _ = 1 := by rw [hk1]; norm_num
        exact hp.cast_prime.not_dvd_one hdiv1
    exact hE.irreducible
  haveI : Function.Injective (Polynomial.map (Int.castRingHom ℚ)) :=
    Polynomial.map_injective Int.cast_injective
  simpa using hZ.map (Polynomial.map (Int.castRingHom ℚ))
