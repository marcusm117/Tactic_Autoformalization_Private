import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_1_6 : ¬ Submodule.IsPrincipal
  (span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))) := by
  classical
  intro h
  rcases h with ⟨f, hf⟩
  have hx : MvPolynomial.X 0 ∈ span ({f} : Set (MvPolynomial (Fin 2) ℚ)) := by
    rw [← hf]
    exact subset_span (by simp)
  have hy : MvPolynomial.X 1 ∈ span ({f} : Set (MvPolynomial (Fin 2) ℚ)) := by
    rw [← hf]
    exact subset_span (by simp)
  have hdiv0 : f ∣ MvPolynomial.X 0 := by
    rw [Submodule.mem_span_singleton] at hx
    rcases hx with ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  have hdiv1 : f ∣ MvPolynomial.X 1 := by
    rw [Submodule.mem_span_singleton] at hy
    rcases hy with ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  have hX0irr : Irreducible (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) := MvPolynomial.irreducible_X 0
  have hX1irr : Irreducible (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) := MvPolynomial.irreducible_X 1
  have h0 := hX0irr.dvd_iff.mp hdiv0
  have h1 := hX1irr.dvd_iff.mp hdiv1
  rcases h0 with hunit | hassoc0
  · have htop : span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) = ⊤ := by
      rw [hf, Submodule.span_singleton_eq_top.mpr hunit]
    have hmem : (1 : MvPolynomial (Fin 2) ℚ) ∈ span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
      rw [htop]
      simp
    rw [Submodule.mem_span_pair] at hmem
    rcases hmem with ⟨a, b, hab⟩
    let ev : MvPolynomial (Fin 2) ℚ →+* ℚ := MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℚ))
    have hab' := congrArg ev hab
    simp [ev] at hab'
  · rcases h1 with hunit | hassoc1
    · have htop : span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) = ⊤ := by
        rw [hf, Submodule.span_singleton_eq_top.mpr hunit]
      have hmem : (1 : MvPolynomial (Fin 2) ℚ) ∈ span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
        rw [htop]
        simp
      rw [Submodule.mem_span_pair] at hmem
      rcases hmem with ⟨a, b, hab⟩
      let ev : MvPolynomial (Fin 2) ℚ →+* ℚ := MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℚ))
      have hab' := congrArg ev hab
      simp [ev] at hab'
    · have hX0f : Associated (MvPolynomial.X 0) f := by
        simpa using hassoc0
      have hX1f : Associated (MvPolynomial.X 1) f := by
        simpa using hassoc1
      have hassoc : Associated (MvPolynomial.X 0) (MvPolynomial.X 1) := hX0f.trans hX1f.symm
      let ev : MvPolynomial (Fin 2) ℚ →+* ℚ :=
        MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (0 : ℚ) else (1 : ℚ))
      have h01 : Associated (0 : ℚ) 1 := hassoc.map ev
      simpa using h01
