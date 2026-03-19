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
  have hunit : IsUnit (d : ZMod N.totient) := (ZMod.isUnit_iff).2 hcop
  rcases hunit with ⟨u, hu⟩
  refine ⟨((u⁻¹ : ZMod N.totient).val), ?_, ?_⟩
  · change (((u⁻¹ : ZMod N.totient).val : ℕ) : ZMod N.totient) * d = 1
    simpa [hu] using (show ((u⁻¹ : ZMod N.totient) : ZMod N.totient) * u = 1 by simp)
  · have hd' : ((u⁻¹ : ZMod N.totient).val : ℕ) * d ≡ 1 [ZMOD N.totient] := by
      change (((u⁻¹ : ZMod N.totient).val : ℕ) : ZMod N.totient) * d = 1
      simpa [hu] using (show ((u⁻¹ : ZMod N.totient) : ZMod N.totient) * u = 1 by simp)
    have hEuler : M ^ N.totient ≡ 1 [ZMOD N] := Int.ModEq.pow_totient hN hMN
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
    rcases Nat.modEq_iff_dvd.mp (by simpa [mul_comm] using hd') with ⟨k, hk⟩
    have hk' : ((u⁻¹ : ZMod N.totient).val : ℕ) * d = 1 + k * N.totient := by
      omega
    have hmid : M' ^ ((u⁻¹ : ZMod N.totient).val) ≡ M ^ (((u⁻¹ : ZMod N.totient).val) * d) [ZMOD N] := by
      simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using hM'.pow ((u⁻¹ : ZMod N.totient).val)
    calc
      M' ^ ((u⁻¹ : ZMod N.totient).val) ≡ M ^ (((u⁻¹ : ZMod N.totient).val) * d) [ZMOD N] := hmid
      _ ≡ M ^ (1 + k * N.totient) [ZMOD N] := by rw [hk']
      _ ≡ M [ZMOD N] := hpow1
