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
  let ch : ℕ → ℕ → ℕ := fun n i => if i = n then 2 * i else 2 * i + 1
  let S : ℕ → Set ℕ := fun n => Set.range (ch n)
  let J : ℕ → Ideal P := fun n => Ideal.span (Set.range fun i : S n => MvPolynomial.X i.1)
  have h_even_mem : ∀ n : ℕ, 2 * n ∈ S n := by
    intro n
    exact ⟨n, by simp [S, ch]⟩
  have h_odd_mem : ∀ {n i : ℕ}, i ≠ n → 2 * i + 1 ∈ S n := by
    intro n i hi
    exact ⟨i, by simp [S, ch, hi]⟩
  have h_even_notin : ∀ {n i : ℕ}, i ≠ n → 2 * i ∉ S n := by
    intro n i hi
    rintro ⟨j, hj⟩
    by_cases hjn : j = n
    · simp [S, ch, hjn] at hj
      omega
    · simp [S, ch, hjn] at hj
      omega
  have h_odd_notin : ∀ n : ℕ, 2 * n + 1 ∉ S n := by
    intro n
    rintro ⟨j, hj⟩
    by_cases hjn : j = n
    · simp [S, ch, hjn] at hj
      omega
    · simp [S, ch, hjn] at hj
      omega
  have hX_not_mem : ∀ {n m : ℕ}, m ∉ S n → MvPolynomial.X m ∉ J n := by
    intro n m hm hXm
    let ev : P →+* ℤ :=
      MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun k : ℕ => if k = m then (1 : ℤ) else 0)
    have hJker : J n ≤ Ideal.comap ev ⊥ := by
      refine Ideal.span_le.2 ?_
      intro p hp
      rcases hp with ⟨i, rfl⟩
      change ev (MvPolynomial.X i.1) ∈ (⊥ : Ideal ℤ)
      change ev (MvPolynomial.X i.1) = 0
      have him : i.1 ≠ m := by
        intro him
        apply hm
        exact him ▸ i.2
      simp [ev, him]
    have h0 : ev (MvPolynomial.X m) = 0 := by
      have : MvPolynomial.X m ∈ Ideal.comap ev (⊥ : Ideal ℤ) := hJker hXm
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
    · subst hi
      have hx : MvPolynomial.X (2 * n) ∈ J n := by
        exact Ideal.subset_span ⟨⟨2 * n, h_even_mem n⟩, rfl⟩
      simpa [mul_comm] using Ideal.mul_mem_left (J n) (MvPolynomial.X (2 * n + 1)) hx
    · have hx : MvPolynomial.X (2 * i + 1) ∈ J n := by
        exact Ideal.subset_span ⟨⟨2 * i + 1, h_odd_mem hi⟩, rfl⟩
      exact Ideal.mul_mem_left (J n) (MvPolynomial.X (2 * i)) hx
  have hJprime : ∀ n : ℕ, (J n).IsPrime := by
    intro n
    simpa [J] using (MvPolynomial.isPrime_ideal_span_X (R := ℤ) (s := S n))
  have hJmin : ∀ n : ℕ, ∀ {K : Ideal P}, K.IsPrime → I ≤ K → K ≤ J n → J n ≤ K := by
    intro n K hKprime hIK hKJ
    refine Ideal.span_le.2 ?_
    intro p hp
    rcases hp with ⟨i, rfl⟩
    by_cases hi : i = n
    · subst hi
      have hprod : MvPolynomial.X (2 * n) * MvPolynomial.X (2 * n + 1) ∈ K := by
        exact hIK (Ideal.subset_span ⟨n, rfl⟩)
      rcases hKprime.mem_or_mem hprod with hxe | hxo
      · exact hxe
      · exfalso
        exact hX_not_mem (n := n) (m := 2 * n + 1) (h_odd_notin n) (hKJ hxo)
    · have hprod : MvPolynomial.X (2 * i) * MvPolynomial.X (2 * i + 1) ∈ K := by
        exact hIK (Ideal.subset_span ⟨i, rfl⟩)
      rcases hKprime.mem_or_mem hprod with hxe | hxo
      · exfalso
        exact hX_not_mem (n := n) (m := 2 * i) (h_even_notin hi) (hKJ hxe)
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
    haveI : IsDomain ((P ⧸ I) ⧸ qIdeal n) := by
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
      exact Ideal.subset_span ⟨⟨2 * n, h_even_mem n⟩, rfl⟩
    have hx' : MvPolynomial.X (2 * n) ∈ J m := by simpa [hEq1] using hx
    exact hX_not_mem (n := m) (m := 2 * n) (h_even_notin (n := m) (i := n) hne) hx'
  exact Infinite.of_injective q hq_inj
