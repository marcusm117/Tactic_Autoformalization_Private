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
  have hunit : IsUnit (d : ZMod N.totient) := (ZMod.natCast_isUnit_iff_coprime).2 hcop
  rcases hunit.exists_inv with ⟨u, hu⟩
  refine ⟨u.val, ?_, ?_⟩
  · simpa [mul_comm] using hu
  · have hEuler : M ^ N.totient ≡ 1 [ZMOD N] := Int.ModEq.pow_totient hN hMN
    have hd' : u.val * d ≡ 1 [ZMOD N.totient] := by
      simpa [mul_comm] using hu
    rcases Nat.modEq_iff_dvd.mp hd' with ⟨k, hk⟩
    have hk' : u.val * d = 1 + k * N.totient := by
      omega
    have hpowk : M ^ (k * N.totient) ≡ 1 [ZMOD N] := by
      simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using (hEuler.pow k)
    have hpow1 : M ^ (1 + k * N.totient) ≡ M [ZMOD N] := by
      calc
        M ^ (1 + k * N.totient) = M * M ^ (k * N.totient) := by rw [pow_add, pow_one]
        _ ≡ M * 1 [ZMOD N] := (by rfl).mul hpowk
        _ ≡ M [ZMOD N] := by simp
    have hmid : M' ^ u.val ≡ M ^ (u.val * d) [ZMOD N] := by
      calc
        M' ^ u.val ≡ (M ^ d) ^ u.val [ZMOD N] := hM'.pow u.val
        _ = M ^ (d * u.val) := by rw [pow_mul]
        _ = M ^ (u.val * d) := by simp [mul_comm]
    calc
      M' ^ u.val ≡ M ^ (u.val * d) [ZMOD N] := hmid
      _ ≡ M ^ (1 + k * N.totient) [ZMOD N] := by rw [hk']
      _ ≡ M [ZMOD N] := hpow1
