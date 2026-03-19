import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  classical
  let N : Zsqrtd (-n) → ℤ := fun z => z.re ^ 2 + n * z.im ^ 2
  have hmul : ∀ x y : Zsqrtd (-n), N (x * y) = N x * N y := by
    intro x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    simp [N, pow_two, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
    ring
  have hunit_of_Neq1 : ∀ {z : Zsqrtd (-n)}, N z = 1 → IsUnit z := by
    intro z hz
    rcases z with ⟨a, b⟩
    refine (isUnit_iff_exists_inv).2 ?_
    refine ⟨⟨a, -b⟩, ?_⟩
    ext <;> simp [N, hz, mul_comm, mul_left_comm, mul_assoc, pow_two]
  constructor
  · intro h
    rcases (isUnit_iff_exists_inv.mp h) with ⟨u, hu⟩
    rcases u with ⟨c, d⟩
    have hre := congrArg (fun z : Zsqrtd (-n) => z.re) hu
    simp at hre
    have hmul1 : 2 * c = 1 := by simpa [mul_comm] using hre
    have hbad := Int.mul_eq_one_iff.mp hmul1
    rcases hbad with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · constructor
    · intro x y hxy
      by_cases hx : IsUnit x
      · exact Or.inl hx
      · by_cases hy : IsUnit y
        · exact Or.inr hy
        · rcases x with ⟨a, b⟩
          rcases y with ⟨c, d⟩
          have hN : N ⟨a, b⟩ * N ⟨c, d⟩ = 4 := by
            have h := congrArg N hxy
            have h' := h.trans (hmul ⟨a, b⟩ ⟨c, d⟩)
            simpa [N] using h'.symm
          have hxne1 : N ⟨a, b⟩ ≠ 1 := by
            intro h1
            exact hx (hunit_of_Neq1 h1)
          have hyne1 : N ⟨c, d⟩ ≠ 1 := by
            intro h1
            exact hy (hunit_of_Neq1 h1)
          have hxnonneg : 0 ≤ N ⟨a, b⟩ := by positivity
          have hynonneg : 0 ≤ N ⟨c, d⟩ := by positivity
          have hx2 : 2 ≤ N ⟨a, b⟩ := by omega
          have hy2 : 2 ≤ N ⟨c, d⟩ := by omega
          have hxle2 : N ⟨a, b⟩ ≤ 2 := by
            nlinarith [hN, hy2, hxnonneg]
          have hxEq : N ⟨a, b⟩ = 2 := le_antisymm hxle2 hx2
          have hxEq' : a ^ 2 + n * b ^ 2 = 2 := by simpa [N] using hxEq
          by_cases hb : b = 0
          · subst hb
            nlinarith [hxEq', hn0]
          · have hb2 : 1 ≤ b ^ 2 := by
              have : 0 < b ^ 2 := by positivity
              omega
            nlinarith [hxEq', hn0, hb2]
    · intro x y hxy
      by_cases hx : IsUnit x
      · exact Or.inl hx
      · by_cases hy : IsUnit y
        · exact Or.inr hy
        · rcases x with ⟨a, b⟩
          rcases y with ⟨c, d⟩
          have hN : N ⟨a, b⟩ * N ⟨c, d⟩ = n := by
            have h := congrArg N hxy
            have h' := h.trans (hmul ⟨a, b⟩ ⟨c, d⟩)
            simpa [N] using h'.symm
          have hxne1 : N ⟨a, b⟩ ≠ 1 := by
            intro h1
            exact hx (hunit_of_Neq1 h1)
          have hyne1 : N ⟨c, d⟩ ≠ 1 := by
            intro h1
            exact hy (hunit_of_Neq1 h1)
          have hx2 : 2 ≤ N ⟨a, b⟩ := by
            have hxnonneg : 0 ≤ N ⟨a, b⟩ := by positivity
            omega
          have hy2 : 2 ≤ N ⟨c, d⟩ := by
            have hynonneg : 0 ≤ N ⟨c, d⟩ := by positivity
            omega
          have hb0 : b ≠ 0 := by
            intro hb0
            subst hb0
            have hreal := congrArg (fun z : Zsqrtd (-n) => z.im) hxy
            simp at hreal
            have hmul1 : a * d = 1 := by simpa [mul_comm] using hreal
            have hbad := Int.mul_eq_one_iff.mp hmul1
            rcases hbad with ⟨ha, hd⟩ | ⟨ha, hd⟩ <;> subst ha <;> exact hx (by infer_instance)
          have hb2 : 1 ≤ b ^ 2 := by
            have : 0 < b ^ 2 := by positivity
            omega
          have hxge : n ≤ N ⟨a, b⟩ := by
            dsimp [N]
            nlinarith [hn0, hb2, sq_nonneg a]
          nlinarith [hN, hxge, hy2, hn0]
    · intro x y hxy
      by_cases hx : IsUnit x
      · exact Or.inl hx
      · by_cases hy : IsUnit y
        · exact Or.inr hy
        · rcases x with ⟨a, b⟩
          rcases y with ⟨c, d⟩
          have hN : N ⟨a, b⟩ * N ⟨c, d⟩ = n + 1 := by
            have h := congrArg N hxy
            have h' := h.trans (hmul ⟨a, b⟩ ⟨c, d⟩)
            simpa [N] using h'.symm
          have hxne1 : N ⟨a, b⟩ ≠ 1 := by
            intro h1
            exact hx (hunit_of_Neq1 h1)
          have hyne1 : N ⟨c, d⟩ ≠ 1 := by
            intro h1
            exact hy (hunit_of_Neq1 h1)
          have hx2 : 2 ≤ N ⟨a, b⟩ := by
            have hxnonneg : 0 ≤ N ⟨a, b⟩ := by positivity
            omega
          have hy2 : 2 ≤ N ⟨c, d⟩ := by
            have hynonneg : 0 ≤ N ⟨c, d⟩ := by positivity
            omega
          have hb0 : b ≠ 0 := by
            intro hb0
            subst hb0
            have hreal := congrArg (fun z : Zsqrtd (-n) => z.im) hxy
            simp at hreal
            have hmul1 : a * d = 1 := by simpa [mul_comm] using hreal
            have hbad := Int.mul_eq_one_iff.mp hmul1
            rcases hbad with ⟨ha, hd⟩ | ⟨ha, hd⟩ <;> subst ha <;> exact hx (by infer_instance)
          have hb2 : 1 ≤ b ^ 2 := by
            have : 0 < b ^ 2 := by positivity
            omega
          have hxge : n ≤ N ⟨a, b⟩ := by
            dsimp [N]
            nlinarith [hn0, hb2, sq_nonneg a]
          nlinarith [hN, hxge, hy2, hn0]
