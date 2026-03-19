import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6b {F : Type*} [Field F] [Fintype F] (hF : card F = 7) :
  Irreducible (X ^ 2 + 1 : Polynomial F) := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  let e : ZMod 7 ≃+* F := ZMod.ringEquiv F hF
  let p7 : Polynomial (ZMod 7) := X ^ 2 + 1
  have hp7 : Irreducible p7 := by
    native_decide
  refine ⟨?_, ?_⟩
  · intro hunit
    exact hp7.not_unit <| by
      simpa [p7] using hunit.map (Polynomial.mapRingHom (e.symm : F →+* ZMod 7))
  · intro f g hfg
    have hfg' : p7 = Polynomial.map (e.symm : F →+* ZMod 7) f * Polynomial.map (e.symm : F →+* ZMod 7) g := by
      simpa [p7] using congrArg (Polynomial.map (e.symm : F →+* ZMod 7)) hfg
    rcases hp7.isUnit_or_isUnit hfg' with hf | hg
    · left
      simpa using hf.map (Polynomial.mapRingHom (e : ZMod 7 →+* F))
    · right
      simpa using hg.map (Polynomial.mapRingHom (e : ZMod 7 →+* F))
