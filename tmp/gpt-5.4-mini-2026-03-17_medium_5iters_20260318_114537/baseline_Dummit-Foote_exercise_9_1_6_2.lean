import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_1_6 : ¬ Submodule.IsPrincipal
  (span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))) := by
  classical
  intro h
  rcases h with ⟨f, hf⟩
  have hx : MvPolynomial.X 0 ∈ span ({f} : Set (MvPolynomial (Fin 2) ℚ)) := by
    simpa [hf] using
      (subset_span
        (by simp : MvPolynomial.X 0 ∈ ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))))
  have hy : MvPolynomial.X 1 ∈ span ({f} : Set (MvPolynomial (Fin 2) ℚ)) := by
    simpa [hf] using
      (subset_span
        (by simp : MvPolynomial.X 1 ∈ ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))))
  have hdiv0 : f ∣ MvPolynomial.X 0 := by
    simpa [Ideal.mem_span_singleton] using hx
  have hdiv1 : f ∣ MvPolynomial.X 1 := by
    simpa [Ideal.mem_span_singleton] using hy
  have hX0irr : Irreducible (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) := by
    simpa using (MvPolynomial.X_irreducible (σ := Fin 2) (R := ℚ) 0)
  have hX1irr : Irreducible (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) := by
    simpa using (MvPolynomial.X_irreducible (σ := Fin 2) (R := ℚ) 1)
  rcases hX0irr.dvd_iff.mp hdiv0 with hunit | hassoc0
  · have htop' : span ({f} : Set (MvPolynomial (Fin 2) ℚ)) = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have htop : span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) = ⊤ := by
      simpa [hf] using htop'
    have h1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
      rw [htop]
      simp
    rw [Submodule.mem_span_pair] at h1
    rcases h1 with ⟨a, b, h1⟩
    let ev : MvPolynomial (Fin 2) ℚ →+* ℚ := MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℚ))
    have h1' : (0 : ℚ) = 1 := by
      simpa [ev] using congrArg ev h1
    exact zero_ne_one h1'
  · rcases hX1irr.dvd_iff.mp hdiv1 with hunit | hassoc1
    · have htop' : span ({f} : Set (MvPolynomial (Fin 2) ℚ)) = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
      have htop : span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) = ⊤ := by
        simpa [hf] using htop'
      have h1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
        rw [htop]
        simp
      rw [Submodule.mem_span_pair] at h1
      rcases h1 with ⟨a, b, h1⟩
      let ev : MvPolynomial (Fin 2) ℚ →+* ℚ := MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℚ))
      have h1' : (0 : ℚ) = 1 := by
        simpa [ev] using congrArg ev h1
      exact zero_ne_one h1'
    · have hassoc : Associated (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) (MvPolynomial.X 1) := by
        exact hassoc0.trans hassoc1.symm
      let ev : MvPolynomial (Fin 2) ℚ →+* ℚ :=
        MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (0 : ℚ) else (1 : ℚ))
      have h01 : Associated (0 : ℚ) 1 := hassoc.map ev
      have hzero : (0 : ℚ) ∣ (1 : ℚ) := by
        exact (h01.dvd_iff).2 (dvd_refl 1)
      exact one_ne_zero (zero_dvd_iff.mp hzero)
