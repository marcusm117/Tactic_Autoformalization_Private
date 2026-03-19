import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
  (hf : f = λ i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)):
  Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  classical
  subst f
  let P := MvPolynomial ℕ ℤ
  let I : Ideal P := Ideal.span (Set.range fun i : ℕ => MvPolynomial.X (2 * i) * MvPolynomial.X (2 * i + 1))
  change Infinite (minimalPrimes (P ⧸ I))
  let T : ℕ → Set ℕ := fun n => {m | m = 2 * n ∨ ∃ i, i ≠ n ∧ m = 2 * i + 1}
  let U : ℕ → Set ℕ := fun n => {m | m = 2 * n + 1 ∨ ∃ i, i ≠ n ∧ m = 2 * i}
  let J : ℕ → Ideal P := fun n => Ideal.span (Set.range fun i : {m // m ∈ T n} => MvPolynomial.X i.1)
  have hT_even : ∀ n : ℕ, 2 * n ∈ T n := by
    intro n
    dsimp [T]
    exact Or.inl rfl
  have hT_odd : ∀ {n i : ℕ}, i ≠ n → 2 * i + 1 ∈ T n := by
    intro n i hi
    dsimp [T]
    exact Or.inr ⟨i, hi, rfl⟩
  have hU_odd : ∀ n : ℕ, 2 * n + 1 ∈ U n := by
    intro n
    dsimp [U]
    exact Or.inl rfl
  have hU_even : ∀ {n i : ℕ}, i ≠ n → 2 * i ∈ U n := by
    intro n i hi
    dsimp [U]
    exact Or.inr ⟨i, hi, rfl⟩
  have hTU_disjoint : ∀ {n m : ℕ}, m ∈ T n → m ∈ U n → False := by
    intro n m ht hu
    dsimp [T, U] at ht hu
    rcases ht with rfl | ⟨i, hi, rfl⟩
    · rcases hu with hu | ⟨j, hj, hu⟩ <;> omega
    · rcases hu with hu | ⟨j, hj, hu⟩ <;> omega
  have h_part : ∀ n m : ℕ, m ∈ T n ∨ m ∈ U n := by
    intro n m
    have hm2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    dsimp [T, U]
    rcases hm2 with hm0 | hm1
    · have hm : m = 2 * (m / 2) := by
        have h := Nat.div_add_mod m 2
        omega
      by_cases hq : m / 2 = n
      · left
        left
        omega
      · right
        right
        exact ⟨m / 2, hq, hm⟩
    · have hm : m = 2 * (m / 2) + 1 := by
        have h := Nat.div_add_mod m 2
        omega
      by_cases hq : m / 2 = n
      · right
        left
        omega
      · left
        right
        exact ⟨m / 2, hq, hm⟩
  have hX_not_mem : ∀ {n m : ℕ}, m ∈ U n → MvPolynomial.X m ∉ J n := by
    intro n m hmU hXm
    let ev : P →+* ℤ :=
      MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun k : ℕ => if k = m then (1 : ℤ) else 0)
    have hJker : J n ≤ Ideal.comap ev ⊥ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      change ev (MvPolynomial.X i.1) ∈ (⊥ : Ideal ℤ)
      have him : i.1 ≠ m := by
        intro him
        exact hTU_disjoint i.2 (him ▸ hmU)
      simp [ev, him]
    have h0 : ev (MvPolynomial.X m) = 0 := by
      have : ev (MvPolynomial.X m) ∈ (⊥ : Ideal ℤ) := hJker hXm
      simpa using this
    have : (1 : ℤ) = 0 := by
      simpa [ev] using h0
    exact one_ne_zero this
  have hIJ : ∀ n : ℕ, I ≤ J n := by
    intro n
    refine Ideal.span_le.2 ?_
    intro p hp
    rcases hp with ⟨i, rfl⟩
    by_cases hi : i = n
    · have hx : MvPolynomial.X (2 * n) ∈ J n := by
        exact Ideal.subset_span ⟨⟨2 * n, hT_even n⟩, rfl⟩
      simpa [hi, mul_comm] using Ideal.mul_mem_left (J n) (MvPolynomial.X (2 * i + 1)) hx
    · have hx : MvPolynomial.X (2 * i + 1) ∈ J n := by
        exact Ideal.subset_span ⟨⟨2 * i + 1, hT_odd hi⟩, rfl⟩
      exact Ideal.mul_mem_left (J n) (MvPolynomial.X (2 * i)) hx
  have hJprime : ∀ n : ℕ, (J n).IsPrime := by
    intro n
    let φ : P →+* MvPolynomial {m // m ∈ U n} ℤ :=
      MvPolynomial.eval₂Hom MvPolynomial.C (fun m => if h : m ∈ U n then MvPolynomial.X ⟨m, h⟩ else 0)
    have hJkerφ : J n ≤ RingHom.ker φ := by
      change J n ≤ Ideal.comap φ ⊥
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      change φ (MvPolynomial.X i.1) ∈ (⊥ : Ideal (MvPolynomial {m // m ∈ U n} ℤ))
      have hiU : ¬ i.1 ∈ U n := by
        intro hiU
        exact hTU_disjoint i.2 hiU
      simp [φ, hiU]
    let φbar : P ⧸ J n →+* MvPolynomial {m // m ∈ U n} ℤ :=
      Ideal.Quotient.lift (J n) φ hJkerφ
    let ψ : MvPolynomial {m // m ∈ U n} ℤ →+* P ⧸ J n :=
      MvPolynomial.eval₂Hom (Int.castRingHom (P ⧸ J n))
        (fun i => Ideal.Quotient.mk (J n) (MvPolynomial.X i.1))
    have hφψ : φbar.comp ψ = RingHom.id _ := by
      ext i <;> simp [φbar, ψ, φ]
    have hψφ₀ : ψ.comp φ = Ideal.Quotient.mk (J n) := by
      ext m
      · simp [ψ, φ]
      · by_cases hU : m ∈ U n
        · simp [ψ, φ, hU]
        · have hT : m ∈ T n := (h_part n m).resolve_right hU
          have hx : Ideal.Quotient.mk (J n) (MvPolynomial.X m) = 0 := by
            exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨m, hT⟩, rfl⟩)
          simp [ψ, φ, hU, hx]
    have hψφ : ψ.comp φbar = RingHom.id _ := by
      ext q
      rcases Ideal.Quotient.mk_surjective (J n) q with ⟨p, rfl⟩
      change ψ (φ p) = Ideal.Quotient.mk (J n) p
      simpa [φbar] using congrFun hψφ₀ p
    have hbij : Function.Bijective φbar := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        have := congrArg ψ hab
        simpa [hψφ] using this
      · intro y
        exact ⟨ψ y, by simpa [hφψ]⟩
    let e : P ⧸ J n ≃+* MvPolynomial {m // m ∈ U n} ℤ := RingEquiv.ofBijective φbar hbij
    letI : IsDomain (P ⧸ J n) := e.isDomain
    exact Ideal.Quotient.isDomain_iff_prime.mp inferInstance
  have hJmin : ∀ n : ℕ, ∀ {K : Ideal P}, K.IsPrime → I ≤ K → K ≤ J n → J n ≤ K := by
    intro n K hKprime hIK hKJ
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    dsimp [T] at i
    rcases i.2 with rfl | ⟨j, hj, rfl⟩
    · have hprod : MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈ K := by
        exact hIK (Ideal.subset_span ⟨n, rfl⟩)
      rcases hKprime.mem_or_mem hprod with hxe | hxo
      · exact hxe
      · exfalso
        exact hX_not_mem (n := n) (m := 2 * n + 1) (hU_odd n) (hKJ hxo)
    · have hprod : MvPolynomial.X (2 * j) * MvPolynomial.X (2 * j + 1) ∈ K := by
        exact hIK (Ideal.subset_span ⟨j, rfl⟩)
      rcases hKprime.mem_or_mem hprod with hxe | hxo
      · exfalso
        exact hX_not_mem (n := n) (m := 2 * j) (hU_even hj) (hKJ hxe)
      · exact hxo
  let A := P ⧸ I
  let qIdeal : ℕ → Ideal A := fun n => Ideal.map (Ideal.Quotient.mk I) (J n)
  have hcomap_q : ∀ n : ℕ, Ideal.comap (Ideal.Quotient.mk I) (qIdeal n) = J n := by
    intro n
    simpa [qIdeal, Ideal.Quotient.ker_mk, sup_eq_left.mpr (hIJ n)] using
      (Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective I) (J n))
  have hqprime : ∀ n : ℕ, (qIdeal n).IsPrime := by
    intro n
    haveI : IsDomain (P ⧸ J n) := Ideal.Quotient.isDomain_iff_prime.mpr (hJprime n)
    let e := Ideal.quotientQuotientEquivQuotient (I := I) (J := J n) (hIJ n)
    letI : IsDomain ((P ⧸ I) ⧸ qIdeal n) := by
      simpa [qIdeal] using e.isDomain
    exact Ideal.Quotient.isDomain_iff_prime.mp inferInstance
  have hqmin : ∀ n : ℕ, qIdeal n ∈ minimalPrimes A := by
    intro n
    simpa [minimalPrimes] using
      (show (qIdeal n).IsPrime ∧
          ∀ Q : Ideal A, Q.IsPrime → Q ≤ qIdeal n → qIdeal n ≤ Q from
        ⟨hqprime n, by
          intro Q hQprime hQle
          have hQcomapPrime : (Ideal.comap (Ideal.Quotient.mk I) Q).IsPrime := hQprime.comap _
          have hIle : I ≤ Ideal.comap (Ideal.Quotient.mk I) Q := by
            intro x hx
            change Ideal.Quotient.mk I x ∈ Q
            have hx0 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hx
            simpa [hx0] using Q.zero_mem
          have hQcomapLe : Ideal.comap (Ideal.Quotient.mk I) Q ≤ J n := by
            calc
              Ideal.comap (Ideal.Quotient.mk I) Q ≤ Ideal.comap (Ideal.Quotient.mk I) (qIdeal n) :=
                Ideal.comap_mono hQle
              _ = J n := hcomap_q n
          have hJle : J n ≤ Ideal.comap (Ideal.Quotient.mk I) Q :=
            hJmin n hQcomapPrime hIle hQcomapLe
          calc
            qIdeal n ≤ Ideal.map (Ideal.Quotient.mk I) (Ideal.comap (Ideal.Quotient.mk I) Q) :=
              Ideal.map_mono hJle
            _ = Q := by
              simpa using
                (Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective I) Q)⟩)
  let q : ℕ → minimalPrimes A := fun n => ⟨qIdeal n, hqmin n⟩
  have hq_inj : Function.Injective q := by
    intro n m hnm
    have hEq0 : qIdeal n = qIdeal m := congrArg Subtype.val hnm
    have hEq1 : J n = J m := by
      calc
        J n = Ideal.comap (Ideal.Quotient.mk I) (qIdeal n) := (hcomap_q n).symm
        _ = Ideal.comap (Ideal.Quotient.mk I) (qIdeal m) := by simpa [hEq0]
        _ = J m := hcomap_q m
    by_contra hne
    have hx : MvPolynomial.X (2 * n) ∈ J n := by
      exact Ideal.subset_span ⟨⟨2 * n, hT_even n⟩, rfl⟩
    have hx' : MvPolynomial.X (2 * n) ∈ J m := by simpa [hEq1] using hx
    exact hX_not_mem (n := m) (m := 2 * n) (hU_even hne) hx'
  exact Infinite.of_injective q hq_inj
