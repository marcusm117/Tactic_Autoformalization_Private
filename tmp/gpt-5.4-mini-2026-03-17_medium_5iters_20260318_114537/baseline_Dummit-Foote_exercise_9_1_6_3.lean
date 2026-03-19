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
  have hdeg1 : MvPolynomial.degreeOf f 1 = 0 := by
    rcases hdiv0 with ⟨g, hg⟩
    have h' := congrArg (fun p => MvPolynomial.degreeOf p 1) hg
    simp [MvPolynomial.degreeOf_mul, MvPolynomial.degreeOf_X] at h'
    exact h'.1
  have hdeg0 : MvPolynomial.degreeOf f 0 = 0 := by
    rcases hdiv1 with ⟨g, hg⟩
    have h' := congrArg (fun p => MvPolynomial.degreeOf p 0) hg
    simp [MvPolynomial.degreeOf_mul, MvPolynomial.degreeOf_X] at h'
    exact h'.1
  have hdeg : ∀ i : Fin 2, MvPolynomial.degreeOf f i = 0 := by
    intro i
    fin_cases i <;> simpa using hdeg0 <;> simpa using hdeg1
  rcases MvPolynomial.eq_C_of_degreeOf_eq_zero (p := f) hdeg with ⟨c, rfl⟩
  have hcne : c ≠ 0 := by
    intro hc
    subst hc
    simpa using hdiv0
  have hunitc : IsUnit c := isUnit_iff_ne_zero.mpr hcne
  have hunitf : IsUnit (MvPolynomial.C c) := hunitc.map (MvPolynomial.C : ℚ →+* MvPolynomial (Fin 2) ℚ)
  have htop : span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) = ⊤ := by
    rw [hf, Ideal.span_singleton_eq_top.mpr hunitf]
  let ev : MvPolynomial (Fin 2) ℚ →+* ℚ :=
    MvPolynomial.aeval (fun _ : Fin 2 => (0 : ℚ))
  have hker : span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) ≤ Ideal.ker ev := by
    refine Submodule.span_le.2 ?_
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> simp [ev]
  have h1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
    rw [htop]
    simp
  have h1ker : (1 : MvPolynomial (Fin 2) ℚ) ∈ Ideal.ker ev := hker h1
  have hcontra : (1 : ℚ) = 0 := by
    simpa [Ideal.mem_ker, ev] using h1ker
  exact one_ne_zero hcontra
