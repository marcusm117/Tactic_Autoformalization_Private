import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_1_6 : ¬ Submodule.IsPrincipal
  (span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))) := by
  let R := MvPolynomial (Fin 2) ℚ
  let S : Submodule R R := span ({(MvPolynomial.X 0 : R), (MvPolynomial.X 1 : R)} : Set R)
  have hS : ¬ Submodule.IsPrincipal S := by
    intro hprincipal
    let e0 : R →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ : Fin 2 => (0 : ℚ))
    have hle : S ≤ e0.ker := by
      dsimp [S]
      refine Submodule.span_le.2 ?_
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl <;> simp [e0]
    have h1not : (1 : R) ∉ S := by
      intro h1
      have hk : (1 : R) ∈ e0.ker := hle h1
      simpa [e0] using hk
    let e01 : R →+* ℚ :=
      MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)
    have hnot_dvd : ¬ (MvPolynomial.X 0 : R) ∣ MvPolynomial.X 1 := by
      rintro ⟨q, hq⟩
      have h := congrArg e01 hq
      simpa [e01] using h
    rcases hprincipal with ⟨p, hp⟩
    have hX0memS : (MvPolynomial.X 0 : R) ∈ S := by
      dsimp [S]
      exact Submodule.subset_span (by simp)
    have hX1memS : (MvPolynomial.X 1 : R) ∈ S := by
      dsimp [S]
      exact Submodule.subset_span (by simp)
    have hX0memp : (MvPolynomial.X 0 : R) ∈ span ({p} : Set R) := by
      rw [hp]
      exact hX0memS
    have hX1memp : (MvPolynomial.X 1 : R) ∈ span ({p} : Set R) := by
      rw [hp]
      exact hX1memS
    rcases Submodule.mem_span_singleton.mp hX0memp with ⟨s, hs⟩
    rcases Submodule.mem_span_singleton.mp hX1memp with ⟨t, ht⟩
    have hs' : s * p = (MvPolynomial.X 0 : R) := by
      simpa [smul_eq_mul] using hs
    have ht' : t * p = (MvPolynomial.X 1 : R) := by
      simpa [smul_eq_mul] using ht
    have hpunit : IsUnit p := by
      by_contra hpnu
      have hsunit : IsUnit s := by
        rcases (MvPolynomial.irreducible_X (0 : Fin 2)).isUnit_or_isUnit hs' with hsunit | hpunit
        · exact hsunit
        · exact (hpnu hpunit).elim
      rcases hsunit with ⟨u, rfl⟩
      have hd01 : (MvPolynomial.X 0 : R) ∣ MvPolynomial.X 1 := by
        refine ⟨t * ↑(u⁻¹), ?_⟩
        calc
          (MvPolynomial.X 1 : R) = t * p := ht'.symm
          _ = t * (↑(u⁻¹) * (MvPolynomial.X 0 : R)) := by
            congr 1
            calc
              p = 1 * p := by simp
              _ = (↑(u⁻¹) * ↑u) * p := by simp
              _ = ↑(u⁻¹) * (↑u * p) := by ac_rfl
              _ = ↑(u⁻¹) * (MvPolynomial.X 0 : R) := by rw [hs']
          _ = (MvPolynomial.X 0 : R) * (t * ↑(u⁻¹)) := by ac_rfl
      exact hnot_dvd hd01
    rcases hpunit with ⟨u, rfl⟩
    have h1mem : (1 : R) ∈ span ({(↑u : R)} : Set R) := by
      exact Submodule.mem_span_singleton.mpr ⟨↑(u⁻¹), by simp [smul_eq_mul]⟩
    have h1memS : (1 : R) ∈ S := by
      rw [← hp]
      exact h1mem
    exact h1not h1memS
  simpa [R, S] using hS
