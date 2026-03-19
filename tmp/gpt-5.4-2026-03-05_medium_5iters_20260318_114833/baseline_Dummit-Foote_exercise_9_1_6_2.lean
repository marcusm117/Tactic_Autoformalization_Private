import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_1_6 : ¬ Submodule.IsPrincipal
  (span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))) := by
  let R := MvPolynomial (Fin 2) ℚ
  let S : Submodule R R :=
    Submodule.span R ({(MvPolynomial.X 0 : R), (MvPolynomial.X 1 : R)} : Set R)
  have hS : ¬ Submodule.IsPrincipal S := by
    intro hprincipal
    let M : Submodule R R where
      carrier := {q : R | MvPolynomial.constantCoeff q = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp [MvPolynomial.constantCoeff_add, ha, hb]
      smul_mem' := by
        intro a b hb
        simp [smul_eq_mul, MvPolynomial.constantCoeff_mul, hb]
    have hSM : S ≤ M := by
      dsimp [S]
      refine Submodule.span_le.2 ?_
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · change MvPolynomial.constantCoeff (MvPolynomial.X (0 : Fin 2) : R) = 0
        simpa using (MvPolynomial.constantCoeff_X (n := (0 : Fin 2)) (R := ℚ))
      · change MvPolynomial.constantCoeff (MvPolynomial.X (1 : Fin 2) : R) = 0
        simpa using (MvPolynomial.constantCoeff_X (n := (1 : Fin 2)) (R := ℚ))
    have h1not : (1 : R) ∉ S := by
      intro h1
      have hm : (1 : R) ∈ M := hSM h1
      change MvPolynomial.constantCoeff (1 : R) = 0 at hm
      simpa using hm
    let e01 : R →+* ℚ :=
      MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)
    have hnot_dvd : ¬ (MvPolynomial.X 0 : R) ∣ MvPolynomial.X 1 := by
      rintro ⟨q, hq⟩
      have h := congrArg e01 hq
      have h0 : e01 (MvPolynomial.X (0 : Fin 2) : R) = 0 := by
        simp [e01]
      have h1 : e01 (MvPolynomial.X (1 : Fin 2) : R) = 1 := by
        simp [e01]
      rw [map_mul, h0, h1] at h
      norm_num at h
    rcases hprincipal with ⟨p, hp⟩
    have hX0memS : (MvPolynomial.X 0 : R) ∈ S := by
      dsimp [S]
      exact Submodule.subset_span (by simp)
    have hX1memS : (MvPolynomial.X 1 : R) ∈ S := by
      dsimp [S]
      exact Submodule.subset_span (by simp)
    have hX0memp : (MvPolynomial.X 0 : R) ∈ Submodule.span R ({p} : Set R) := by
      rw [← hp]
      exact hX0memS
    have hX1memp : (MvPolynomial.X 1 : R) ∈ Submodule.span R ({p} : Set R) := by
      rw [← hp]
      exact hX1memS
    rcases Submodule.mem_span_singleton.mp hX0memp with ⟨s, hs⟩
    rcases Submodule.mem_span_singleton.mp hX1memp with ⟨t, ht⟩
    have hs' : s * p = (MvPolynomial.X 0 : R) := by
      simpa [smul_eq_mul] using hs
    have ht' : t * p = (MvPolynomial.X 1 : R) := by
      simpa [smul_eq_mul] using ht
    have hpunit : IsUnit p := by
      by_contra hpnu
      have hirr : Irreducible (MvPolynomial.X (0 : Fin 2) : R) := by
        simpa using (irreducible_X (R := ℚ) (n := (0 : Fin 2)))
      have hsunit : IsUnit s := by
        rcases hirr.isUnit_or_isUnit hs'.symm with hsunit | hpunit'
        · exact hsunit
        · exact (hpnu hpunit').elim
      rcases hsunit with ⟨u, rfl⟩
      have hp_eq : p = ↑(u⁻¹) * (MvPolynomial.X 0 : R) := by
        calc
          p = (1 : R) * p := by simp
          _ = (↑(u⁻¹) * ↑u) * p := by simp
          _ = ↑(u⁻¹) * (↑u * p) := by ac_rfl
          _ = ↑(u⁻¹) * (MvPolynomial.X 0 : R) := by rw [hs']
      have hd01 : (MvPolynomial.X 0 : R) ∣ MvPolynomial.X 1 := by
        refine ⟨t * ↑(u⁻¹), ?_⟩
        calc
          (MvPolynomial.X 1 : R) = t * p := ht'.symm
          _ = t * (↑(u⁻¹) * (MvPolynomial.X 0 : R)) := by rw [hp_eq]
          _ = (MvPolynomial.X 0 : R) * (t * ↑(u⁻¹)) := by ac_rfl
      exact hnot_dvd hd01
    rcases hpunit with ⟨u, rfl⟩
    have h1mem : (1 : R) ∈ Submodule.span R ({(↑u : R)} : Set R) := by
      exact Submodule.mem_span_singleton.mpr ⟨↑(u⁻¹), by simp [smul_eq_mul]⟩
    have h1memS : (1 : R) ∈ S := by
      rw [hp]
      exact h1mem
    exact h1not h1memS
  simpa [R, S] using hS
