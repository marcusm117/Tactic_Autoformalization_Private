import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_1_12 {N : ℕ} (hN : N > 0) {M M': ℤ} {d : ℕ}
  (hMN : M.gcd N = 1) (hMd : d.gcd N.totient = 1)
  (hM' : M' ≡ M^d [ZMOD N]) :
  ∃ d' : ℕ, d' * d ≡ 1 [ZMOD N.totient] ∧
  M ≡ M'^d' [ZMOD N] := by
  classical
  have hcop : Nat.Coprime d N.totient := Nat.coprime_iff_gcd_eq_one.mpr hMd
  rcases hcop.exists_mul_right_modEq_one with ⟨d', hd'⟩
  refine ⟨d', ?_, ?_⟩
  · simpa [mul_comm] using hd'
  · have hEuler : M ^ N.totient ≡ 1 [ZMOD N] := Int.modEq_pow_totient hN hMN
    rcases Nat.modEq_iff_dvd.mp (by simpa [mul_comm] using hd') with ⟨k, hk⟩
    have hk' : d' * d = 1 + k * N.totient := by
      omega
    have hpowk : M ^ (k * N.totient) ≡ 1 [ZMOD N] := by
      calc
        M ^ (k * N.totient) = (M ^ N.totient) ^ k := by rw [mul_comm, pow_mul]
        _ ≡ 1 ^ k [ZMOD N] := hEuler.pow k
        _ ≡ 1 [ZMOD N] := by simp
    have hpow1 : M ^ (1 + k * N.totient) ≡ M [ZMOD N] := by
      calc
        M ^ (1 + k * N.totient) = M * M ^ (k * N.totient) := by rw [pow_add, pow_one]
        _ ≡ M * 1 [ZMOD N] := (by simp : M ≡ M [ZMOD N]).mul hpowk
        _ ≡ M [ZMOD N] := by simp
    have hmid : M' ^ d' ≡ M ^ (d' * d) [ZMOD N] := by
      calc
        M' ^ d' ≡ (M ^ d) ^ d' [ZMOD N] := hM'.pow d'
        _ = M ^ (d * d') := by rw [pow_mul]
        _ = M ^ (d' * d) := by rw [mul_comm]
    calc
      M' ^ d' ≡ M ^ (d' * d) [ZMOD N] := hmid
      _ ≡ M ^ (1 + k * N.totient) [ZMOD N] := by rw [hk']
      _ ≡ M [ZMOD N] := hpow1
