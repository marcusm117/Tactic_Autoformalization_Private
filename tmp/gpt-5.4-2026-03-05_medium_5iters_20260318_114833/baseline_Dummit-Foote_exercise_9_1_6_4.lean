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
  have hprincipalS : Submodule.IsPrincipal S := by
    simpa [R, x0, x1, S] using hprincipal
  let M : Submodule R R :=
    { carrier := {q : R | MvPolynomial.constantCoeff q = 0}
      zero_mem' := by
        simp
      add_mem' := by
        intro a b ha hb
        simp [MvPolynomial.constantCoeff_add, ha, hb]
      smul_mem' := by
        intro a b hb
        simp [smul_eq_mul, MvPolynomial.constantCoeff_mul, hb] }
  have hSM : S ≤ M := by
    dsimp [S]
    refine Submodule.span_le.2 ?_
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · change MvPolynomial.constantCoeff (MvPolynomial.X (0 : Fin 2) : R) = 0
      simpa [R] using (MvPolynomial.constantCoeff_X (n := (0 : Fin 2)) (R := ℚ))
    · change MvPolynomial.constantCoeff (MvPolynomial.X (1 : Fin 2) : R) = 0
      simpa [R] using (MvPolynomial.constantCoeff_X (n := (1 : Fin 2)) (R := ℚ))
  have h1not : (1 : R) ∉ S := by
    intro h1
    have hm : (1 : R) ∈ M := hSM h1
    change MvPolynomial.constantCoeff (1 : R) = 0 at hm
    simpa [R] using hm
  have hx0mem : x0 ∈ S := by
    dsimp [S]
    exact Submodule.subset_span (by simp [x0, x1])
  have hx1mem : x1 ∈ S := by
    dsimp [S]
    exact Submodule.subset_span (by simp [x0, x1])
  let e01 : R →+* ℚ :=
    MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)
  have hnot_dvd : ¬ x0 ∣ x1 := by
    rintro ⟨q, hq⟩
    have h := congrArg e01 hq
    have h0 : e01 x0 = 0 := by
      simp [e01, x0]
    have h1 : e01 x1 = 1 := by
      simp [e01, x1]
    rw [map_mul, h0, h1] at h
    norm_num at h
  rcases hprincipalS with ⟨p, hp⟩
  have hx0p : x0 ∈ Submodule.span R ({p} : Set R) := by
    simpa [hp] using hx0mem
  have hx1p : x1 ∈ Submodule.span R ({p} : Set R) := by
    simpa [hp] using hx1mem
  rcases Submodule.mem_span_singleton.mp hx0p with ⟨s, hs⟩
  rcases Submodule.mem_span_singleton.mp hx1p with ⟨t, ht⟩
  have hs' : s * p = x0 := by
    simpa [smul_eq_mul] using hs
  have ht' : t * p = x1 := by
    simpa [smul_eq_mul] using ht
  have hpunit : IsUnit p := by
    by_contra hpnu
    have hirr : Irreducible x0 := by
      simpa [R, x0] using (irreducible_X (R := ℚ) (n := (0 : Fin 2)))
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
    simpa [hp] using h1p
  exact h1not h1S
