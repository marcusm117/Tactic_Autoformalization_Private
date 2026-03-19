import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_1_6 : ¬ Submodule.IsPrincipal
  (span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))) := by
  intro hprincipal
  let R := MvPolynomial (Fin 2) ℚ
  let x0 : R := MvPolynomial.X 0
  let x1 : R := MvPolynomial.X 1
  let S : Submodule R R := Submodule.span R ({x0, x1} : Set R)
  change Submodule.IsPrincipal S at hprincipal
  have hx0mem : x0 ∈ S := by
    dsimp [S]
    exact Submodule.subset_span (by simp [x0, x1])
  have hx1mem : x1 ∈ S := by
    dsimp [S]
    exact Submodule.subset_span (by simp [x0, x1])
  have h1not : (1 : R) ∉ S := by
    intro h1
    let e0 : R →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ : Fin 2 => (0 : ℚ))
    have h1' : (1 : R) ∈ Submodule.span R ({x0, x1} : Set R) := by
      simpa [S] using h1
    have he : e0 (1 : R) = 0 := by
      refine Submodule.span_induction h1' ?_ ?_ ?_ ?_
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · simpa [x0, e0] using (MvPolynomial.constantCoeff_X (n := (0 : Fin 2)) (R := ℚ))
        · simpa [x1, e0] using (MvPolynomial.constantCoeff_X (n := (1 : Fin 2)) (R := ℚ))
      · simp [e0]
      · intro a b ha hb
        simp [map_add, ha, hb]
      · intro a b hb
        simp [smul_eq_mul, map_mul, hb]
    have hq : (1 : ℚ) = 0 := by
      simpa [e0] using he
    norm_num at hq
  let e01 : R →+* ℚ :=
    MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)
  have hnot_dvd : ¬ x0 ∣ x1 := by
    rintro ⟨q, hq⟩
    have h' : (1 : ℚ) = 0 := by
      simpa [x0, x1, e01] using congrArg e01 hq
    norm_num at h'
  rcases hprincipal with ⟨p, hp⟩
  have hx0p : x0 ∈ Submodule.span R ({p} : Set R) := by
    rw [← hp]
    exact hx0mem
  have hx1p : x1 ∈ Submodule.span R ({p} : Set R) := by
    rw [← hp]
    exact hx1mem
  rcases Submodule.mem_span_singleton.mp hx0p with ⟨s, hs⟩
  rcases Submodule.mem_span_singleton.mp hx1p with ⟨t, ht⟩
  have hs' : s * p = x0 := by
    simpa [smul_eq_mul] using hs
  have ht' : t * p = x1 := by
    simpa [smul_eq_mul] using ht
  have hpunit : IsUnit p := by
    by_contra hpnu
    have hirr : Irreducible x0 := by
      simpa [x0] using (irreducible_X (R := ℚ) (n := (0 : Fin 2)))
    have hsunit : IsUnit s := by
      rcases hirr.isUnit_or_isUnit hs'.symm with hsunit | hpunit'
      · exact hsunit
      · exact (hpnu hpunit').elim
    rcases hsunit with ⟨u, rfl⟩
    have hp_eq : p = ↑(u⁻¹) * x0 := by
      calc
        p = (1 : R) * p := by simp
        _ = (↑(u⁻¹) * ↑u) * p := by simp
        _ = ↑(u⁻¹) * (↑u * p) := by ac_rfl
        _ = ↑(u⁻¹) * x0 := by rw [hs']
    have hd : x0 ∣ x1 := by
      refine ⟨t * ↑(u⁻¹), ?_⟩
      calc
        x1 = t * p := ht'.symm
        _ = t * (↑(u⁻¹) * x0) := by rw [hp_eq]
        _ = x0 * (t * ↑(u⁻¹)) := by ac_rfl
    exact hnot_dvd hd
  rcases hpunit with ⟨u, rfl⟩
  have h1p : (1 : R) ∈ Submodule.span R ({(↑u : R)} : Set R) := by
    exact Submodule.mem_span_singleton.mpr ⟨↑(u⁻¹), by simp [smul_eq_mul]⟩
  have h1S : (1 : R) ∈ S := by
    rw [hp]
    exact h1p
  exact h1not h1S
