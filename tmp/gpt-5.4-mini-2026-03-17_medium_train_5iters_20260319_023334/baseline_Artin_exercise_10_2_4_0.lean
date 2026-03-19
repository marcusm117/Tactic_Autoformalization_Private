import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_2_4 :
  span ({2} : Set $ Polynomial ℤ) ⊓ (span {X}) =
  span ({2 * X} : Set $ Polynomial ℤ) := by
  ext f
  constructor
  · intro hf
    have h2 : (2 : Polynomial ℤ) ∣ f := Ideal.mem_span_singleton.mp hf.1
    have hX : X ∣ f := Ideal.mem_span_singleton.mp hf.2
    rcases h2 with ⟨g, hg⟩
    have hf0 : f.coeff 0 = 0 := by
      rcases hX with ⟨h, rfl⟩
      simp
    have hcoeff : f.coeff 0 = (2 : ℤ) * g.coeff 0 := by
      rw [hg]
      simp
    have hg0 : g.coeff 0 = 0 := by
      linarith
    rcases (Polynomial.X_dvd_iff.mpr hg0) with ⟨q, hq⟩
    exact Ideal.mem_span_singleton.mpr ⟨q, by
      calc
        f = 2 * g := hg
        _ = 2 * (X * q) := by rw [hq]
        _ = (2 * X) * q := by simpa [mul_assoc]
    ⟩
  · intro hf
    rcases Ideal.mem_span_singleton.mp hf with ⟨q, hq⟩
    constructor
    · exact Ideal.mem_span_singleton.mpr ⟨X * q, by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hq
      ⟩
    · exact Ideal.mem_span_singleton.mpr ⟨2 * q, by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hq
      ⟩
