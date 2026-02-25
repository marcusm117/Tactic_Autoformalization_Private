# Common Proof Strategies in Omni-MATH Number Theory Problems

**Dataset:** Omni-MATH_NumberTheory.jsonl (832 unique problems)
**Analysis Date:** 2026-02-25
**Analysis Method:** Manual review of problems and solutions

---

## Overview

This document summarizes the common proof strategies and techniques found across the Number Theory problems in the Omni-MATH dataset. The techniques are ranked from most frequent to least frequent based on manual analysis of the problem solutions.

Each technique includes a **Lean Tactic Translation** subsection explaining how it could be implemented as a Lean 4 tactic using Mathlib.

---

## 1. Modular Arithmetic / Congruence Analysis

**Estimated Frequency:** ~400+ problems (most common technique)

The most dominant technique across the dataset. Used to analyze divisibility, find patterns, constrain solutions, and reduce problems to finite cases.

### Key Applications:
- Reducing equations modulo small primes (2, 3, 4, 5, 7, etc.)
- Finding necessary conditions for solutions
- Analyzing periodic behavior of sequences
- Proving impossibility by deriving contradictions in residues

### Examples:
- **Problem 3:** "Taking modulo 4, we get $(3x+7)^2 = 4(400) \Rightarrow x = 11$"
- **Problem 7:** "$a \mid b^n - n$ for all positive integers $n$" - uses congruence cycling
- **Problem 104:** "By Euler's Totient Theorem, $3^6 \equiv 5^6 \equiv 1 \pmod{7}$"

### Typical Patterns:
```
- Take equation mod p for small prime p
- Analyze residue classes to eliminate cases
- Use periodicity of powers mod m
- Check parity (mod 2) as first step
```

### Lean Tactic Translation

**Tactic Name:** `mod_reduce` / `decide_mod`

**Description:** A tactic that reduces number-theoretic goals by taking both sides modulo a specified value, then uses decidability to verify the resulting finite computation.

**Key Mathlib Lemmas:**
- `Int.emod_emod_of_dvd` - transitivity of mod
- `Int.add_mul_emod_self` - simplification rules
- `ZMod.val_cast_of_lt` - casting between types
- `Nat.mod_mod_of_dvd` - mod composition

**Example Lean Code:**
```lean
-- Proposed tactic: mod_reduce n
-- Transforms goal by reducing modulo n

example (x : ℤ) (h : x^2 ≡ 1 [ZMOD 8]) : x % 2 = 1 := by
  mod_reduce 2  -- reduces goal modulo 2
  decide        -- finite check

-- Implementation sketch:
macro "mod_reduce" n:term : tactic =>
  `(tactic| (
    simp only [Int.ModEq] at *
    conv => lhs; rw [Int.emod_emod_of_dvd _ (by norm_num : $n ∣ _)]
    conv => rhs; rw [Int.emod_emod_of_dvd _ (by norm_num : $n ∣ _)]
    norm_num
  ))
```

**Automation Strategy:**
1. Identify the modulus from the goal or hypothesis
2. Apply `Int.ModEq` or `Nat.ModEq` conversion
3. Use `norm_num` and `decide` for finite verification
4. Chain with `omega` for linear arithmetic over residues

---

## 2. Case Analysis / Case-by-Case Proof

**Estimated Frequency:** ~250+ problems

Breaking problems into exhaustive cases based on parity, residue classes, prime factors, size, or other distinguishing conditions.

### Key Applications:
- Separating by parity (odd/even)
- Splitting by residue classes (mod 3, mod 4, etc.)
- Analyzing different prime factor structures
- Handling boundary cases separately

### Examples:
- **Problem 3:** "Case 1: $w=0$... Case 2: $w=1$... Case 3: $w \geq 2$..."
- **Problem 17:** "Case 1: $a > 1$... Case 2: $a = 1$..."
- **Problem 48:** "Case 1: One of $p,q$ is 2... Case 2: Both $p,q$ are odd primes"

### Typical Structure:
```
1. Identify the key variable/parameter to split on
2. Enumerate all possible cases exhaustively
3. Handle each case independently
4. Combine results from all cases
```

### Lean Tactic Translation

**Tactic Name:** `nt_cases` / `split_mod`

**Description:** A tactic that performs case analysis on number-theoretic conditions, automatically generating subcases based on residue classes, parity, or comparison with specific values.

**Key Mathlib Lemmas:**
- `Nat.even_or_odd` - parity split
- `Int.emod_two_eq_zero_or_one` - mod 2 cases
- `ZMod.val_lt` - residue class bounds
- `Nat.lt_or_ge` - comparison split

**Example Lean Code:**
```lean
-- Proposed tactic: nt_cases x mod n
-- Splits into n cases based on residue class

example (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  nt_cases n mod 3  -- generates 3 subgoals
  all_goals simp

-- Proposed tactic: parity_cases x
-- Splits into even/odd cases

example (n : ℕ) (h : n^2 % 4 = 0 ∨ n^2 % 4 = 1) : True := by
  parity_cases n
  · -- n = 2k case
    simp [pow_two, Nat.mul_mod]
  · -- n = 2k+1 case
    simp [pow_two, Nat.mul_mod, Nat.add_mod]

-- Implementation sketch:
macro "nt_cases" x:ident "mod" n:term : tactic =>
  `(tactic| (
    rcases Nat.mod_two_eq_zero_or_one $x with h | h <;>
    simp_all only [h]
  ))
```

**Automation Strategy:**
1. Detect the natural splitting criterion (parity, mod n, comparison)
2. Use `rcases` or `interval_cases` for bounded cases
3. Generate subgoals with appropriate hypotheses
4. Apply simplification lemmas specific to each case

---

## 3. Prime Factorization Analysis

**Estimated Frequency:** ~200+ problems

Analyzing the prime factorization structure of numbers to understand divisibility and constraints.

### Key Applications:
- Determining divisibility conditions
- Counting divisors and their properties
- Analyzing multiplicative functions ($\tau$, $\sigma$, $\phi$, $\omega$, $\Omega$)
- Understanding structure of products and powers

### Examples:
- **Problem 4:** Uses Zsigmondy's theorem on $a^n - 1$ and its primitive prime divisors
- **Problem 9:** "Let $n = p_1^{a_1} \cdots p_t^{a_t}$, define $\omega(n) = t$ and $\Omega(n) = a_1 + \cdots + a_t$"
- **Problem 50:** Analyzing factorization counts $f(k)$

### Common Functions:
- $\tau(n)$ = number of divisors
- $\sigma(n)$ = sum of divisors
- $\phi(n)$ = Euler's totient function
- $\omega(n)$ = number of distinct prime factors
- $\Omega(n)$ = total prime factors with multiplicity

### Lean Tactic Translation

**Tactic Name:** `factor_analyze` / `prime_decompose`

**Description:** A tactic that introduces the prime factorization of a natural number and provides lemmas about its structure.

**Key Mathlib Definitions/Lemmas:**
- `Nat.factorization` - the factorization as a finsupp
- `Nat.prod_pow_factorization` - reconstruction from factors
- `Nat.divisors` - set of divisors
- `Nat.totient` - Euler's totient
- `Nat.ArithmeticFunction.sigma` - sum of divisors

**Example Lean Code:**
```lean
-- Proposed tactic: factor_analyze n
-- Introduces factorization and relevant lemmas

example (n : ℕ) (hn : n > 0) : n = ∏ p in n.factorization.support, p ^ n.factorization p := by
  factor_analyze n
  exact Nat.factorization_prod_pow_eq_self hn

-- For specific factorizations:
example : (12 : ℕ).factorization = fun p =>
    if p = 2 then 2 else if p = 3 then 1 else 0 := by
  native_decide

-- Implementation sketch:
macro "factor_analyze" n:term : tactic =>
  `(tactic| (
    have hfac : $n = ∏ p in ($n).factorization.support,
                    p ^ ($n).factorization p :=
      Nat.factorization_prod_pow_eq_self (by positivity)
    have hdiv : ∀ d, d ∣ $n ↔ ∀ p, ($n).factorization p ≤ d.factorization p :=
      fun d => Nat.factorization_le_iff_dvd (by positivity) d
  ))
```

**Automation Strategy:**
1. Use `Nat.factorization` to decompose numbers
2. Apply multiplicativity of arithmetic functions
3. Leverage `Finsupp` operations for factorization manipulation
4. Connect to divisibility via `factorization_le_iff_dvd`

---

## 4. Proof by Contradiction

**Estimated Frequency:** ~180+ problems

Assuming the opposite of what we want to prove and deriving a logical contradiction.

### Key Applications:
- Proving non-existence of solutions
- Showing finiteness of solution sets
- Establishing uniqueness
- Proving impossibility results

### Examples:
- **Problem 7:** "Assume for contradiction that for all sufficiently large $n$, $n! - 1$ is prime..."
- **Problem 37:** "Suppose for contradiction that such primes exist..."
- **Problem 39:** "Assume for contradiction that there exists some real number $s \neq 0$..."

### Typical Structure:
```
1. Assume the negation of the desired statement
2. Derive logical consequences from this assumption
3. Reach a statement that contradicts known facts
4. Conclude the original statement must be true
```

### Lean Tactic Translation

**Tactic Name:** `by_contra` (built-in) / `nt_contra`

**Description:** Lean's built-in `by_contra` tactic. An enhanced version `nt_contra` could automatically set up common number-theoretic contradictions.

**Key Mathlib Tactics:**
- `by_contra` - standard contradiction
- `push_neg` - push negation inward
- `absurd` - explicit contradiction
- `omega` - for arithmetic contradictions

**Example Lean Code:**
```lean
-- Standard usage
example (n : ℕ) (h : n^2 = 2) : False := by
  by_contra _
  -- n^2 = 2 has no natural number solutions
  interval_cases n <;> simp_all

-- For number theory: enhanced contradiction setup
example (p : ℕ) (hp : p.Prime) (h : p ∣ 1) : False := by
  nt_contra  -- automatically derives contradiction from prime not dividing 1
  exact Nat.Prime.not_dvd_one hp h

-- Implementation sketch for nt_contra:
macro "nt_contra" : tactic =>
  `(tactic| (
    by_contra h
    push_neg at h
    first
    | exact absurd (by assumption) (by assumption)
    | omega
    | simp_all [Nat.Prime.not_dvd_one, Nat.lt_irrefl]
  ))
```

**Automation Strategy:**
1. Apply `by_contra` to negate the goal
2. Use `push_neg` to simplify negated statements
3. Derive arithmetic contradictions using `omega` or `linarith`
4. Check for common NT contradictions (prime divides 1, etc.)

---

## 5. Mathematical Induction

**Estimated Frequency:** ~150+ problems

Both weak and strong induction, typically on natural number parameters.

### Key Applications:
- Proving statements for all $n \geq n_0$
- Establishing recursive properties
- Building up from base cases
- Proving inequalities that hold for all integers

### Types:
- **Weak Induction:** $P(n) \Rightarrow P(n+1)$
- **Strong Induction:** $P(1) \land P(2) \land \cdots \land P(n) \Rightarrow P(n+1)$

### Examples:
- **Problem 6:** "Step 1: Base case... Step 2: Assume for $n=k$, prove for $n=k+1$..."
- **Problem 7:** "By induction on $a$, the sequence eventually becomes constant mod $a$"
- **Problem 44:** Uses induction on Fibonacci-like sequences

### Lean Tactic Translation

**Tactic Name:** `induction` (built-in) / `strong_induction` / `nt_induction`

**Description:** Lean's built-in `induction` tactic, enhanced variants for strong induction and number-theoretic induction starting from arbitrary bases.

**Key Mathlib Tactics/Lemmas:**
- `induction` - standard induction
- `Nat.strong_induction_on` - strong induction
- `Nat.le_induction` - induction from a base > 0
- `Nat.rec_on` - recursion principle

**Example Lean Code:**
```lean
-- Standard induction
example (n : ℕ) : 2 ∣ n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_eq_add_one, add_assoc]
    -- ... continue proof

-- Strong induction
example (n : ℕ) (hn : n > 0) : ∃ p, p.Prime ∧ p ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · exact ⟨n, hp, dvd_refl n⟩
    · obtain ⟨d, hd, hdn, hd1⟩ := Nat.exists_dvd_of_not_prime hn hp
      obtain ⟨p, hpp, hpd⟩ := ih d hdn (Nat.pos_of_ne_zero (fun h => by simp_all))
      exact ⟨p, hpp, dvd_trans hpd hd⟩

-- Induction from base k
example (P : ℕ → Prop) (k : ℕ) (hbase : P k)
    (hstep : ∀ n ≥ k, P n → P (n + 1)) : ∀ n ≥ k, P n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih => exact hstep n hn ih
```

**Automation Strategy:**
1. Detect the induction variable and type
2. Choose between weak, strong, or bounded induction
3. Auto-generate base case goals
4. Set up induction hypothesis with appropriate strength

---

## 6. Bounding / Size Arguments

**Estimated Frequency:** ~140+ problems

Using inequalities to constrain possible solutions or prove finiteness.

### Key Applications:
- Showing only finitely many solutions exist
- Eliminating large cases
- Proving bounds on sequences
- Establishing growth rates

### Examples:
- **Problem 5:** "Since $2a - n - m > 0$, we have $f(m,n) > 0$..."
- **Problem 19:** "The ratio $\frac{a_n}{n}$ is bounded by a constant"
- **Problem 47:** "At most $\frac{m+1}{2m+1}$ of elements..."

### Common Techniques:
```
- AM-GM inequality
- Cauchy-Schwarz
- Growth comparison (polynomial vs exponential)
- Counting arguments
```

### Lean Tactic Translation

**Tactic Name:** `bound` / `nt_bound`

**Description:** A tactic that derives bounds on expressions, using AM-GM, growth estimates, and arithmetic reasoning.

**Key Mathlib Lemmas:**
- `Nat.lt_pow_self` - exponential growth
- `Nat.factorial_pos` - factorial bounds
- `Geom.mean_le_arith_mean` - AM-GM
- `sq_nonneg` - non-negativity of squares

**Example Lean Code:**
```lean
-- Proposed tactic: nt_bound
-- Derives bounds using standard inequalities

example (n : ℕ) (hn : n ≥ 3) : n! > n^2 := by
  nt_bound  -- applies factorial growth estimate
  -- Under the hood: uses Nat.factorial_pos and growth lemmas

-- For AM-GM type bounds:
example (a b : ℕ) : a * b ≤ (a + b)^2 / 4 := by
  have h := sq_nonneg (a - b)
  linarith [sq_nonneg a, sq_nonneg b]

-- Implementation sketch:
macro "nt_bound" : tactic =>
  `(tactic| (
    first
    | nlinarith [sq_nonneg _, Nat.factorial_pos _]
    | apply Nat.lt_pow_self; omega
    | linarith
    | omega
  ))
```

**Automation Strategy:**
1. Identify the inequality structure (polynomial, exponential, factorial)
2. Apply appropriate growth lemmas from Mathlib
3. Use `nlinarith` for nonlinear arithmetic
4. Fall back to `omega` for linear cases

---

## 7. Fermat's Little Theorem / Euler's Theorem

**Estimated Frequency:** ~120+ problems

For working with powers modulo primes or coprime moduli.

### Statements:
- **Fermat:** $a^{p-1} \equiv 1 \pmod{p}$ for prime $p$, $\gcd(a,p) = 1$
- **Euler:** $a^{\phi(n)} \equiv 1 \pmod{n}$ for $\gcd(a,n) = 1$

### Examples:
- **Problem 15:** "By Fermat's Little Theorem, $z^{p-1} \equiv 1 \pmod{p}$"
- **Problem 104:** "$3^6 \equiv 5^6 \equiv 1 \pmod{7}$ by Euler's Totient Theorem"
- **Problem 201:** Uses Euler's theorem for periodic behavior of powers

### Applications:
- Computing large powers mod $n$
- Finding multiplicative orders
- Analyzing periodic sequences
- Solving congruence equations

### Lean Tactic Translation

**Tactic Name:** `fermat` / `euler_totient`

**Description:** A tactic that applies Fermat's Little Theorem or Euler's theorem to simplify powers modulo n.

**Key Mathlib Lemmas:**
- `ZMod.pow_card` - $a^p = a$ in $\mathbb{Z}/p\mathbb{Z}$
- `ZMod.pow_totient` - Euler's theorem
- `Nat.Prime.coprime_pow_of_not_dvd` - coprimality check
- `ZMod.units_pow_card_sub_one_eq_one` - FLT for units

**Example Lean Code:**
```lean
-- Fermat's Little Theorem
example (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) : a ^ (p - 1) = 1 := by
  fermat  -- applies ZMod.pow_card_sub_one_eq_one
  exact ha

-- Euler's Theorem
example (n : ℕ) (hn : n > 0) (a : ℤ) (ha : a.gcd n = 1) :
    a ^ n.totient ≡ 1 [ZMOD n] := by
  euler_totient  -- applies Int.ModEq.pow_totient

-- Simplifying large powers
example : (2 : ZMod 7) ^ 100 = 2 := by
  have h : (2 : ZMod 7) ^ 6 = 1 := by fermat; decide
  calc (2 : ZMod 7) ^ 100 = 2 ^ (6 * 16 + 4) := by norm_num
    _ = (2 ^ 6) ^ 16 * 2 ^ 4 := by ring
    _ = 1 ^ 16 * 2 ^ 4 := by rw [h]
    _ = 2 := by decide

-- Implementation sketch:
macro "fermat" : tactic =>
  `(tactic| (
    first
    | exact ZMod.pow_card_sub_one_eq_one (by assumption)
    | apply ZMod.units_pow_card_sub_one_eq_one
  ))
```

**Automation Strategy:**
1. Check if goal involves power modulo prime
2. Verify coprimality condition
3. Apply `ZMod.pow_card_sub_one_eq_one` or totient version
4. Simplify exponent using modular arithmetic

---

## 8. GCD/LCM Properties

**Estimated Frequency:** ~100+ problems

Using properties of greatest common divisors and least common multiples.

### Key Properties:
- $\gcd(a,b) \cdot \text{lcm}(a,b) = ab$
- $\gcd(a,bc) = \gcd(a,b) \cdot \gcd(a/\gcd(a,b), c)$
- Euclidean algorithm: $\gcd(a,b) = \gcd(b, a \mod b)$

### Examples:
- **Problem 2:** "Since $\gcd(p^k, q) = 1$, we can choose $a$ and $b$ such that..."
- **Problem 10:** "$\gcd(m,n) \mid a_m^2 + a_n^2$ and $\gcd(a_m, a_n) \mid m^2 + n^2$"
- **Problem 16:** Finding smallest $m$ such that $2n \mid ax + by$

### Lean Tactic Translation

**Tactic Name:** `gcd_tac` / `coprime_tac`

**Description:** A tactic that simplifies goals involving gcd/lcm using standard identities and Bezout's identity.

**Key Mathlib Lemmas:**
- `Nat.gcd_comm`, `Nat.gcd_assoc` - gcd properties
- `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right` - divisibility
- `Nat.coprime_of_dvd` - coprimality from divisibility
- `Nat.gcd_mul_lcm` - gcd-lcm product
- `Int.gcd_eq_gcd_ab` - Bezout's identity

**Example Lean Code:**
```lean
-- GCD simplification
example (a b : ℕ) : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b

-- Coprimality reasoning
example (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) : Nat.Coprime p a := by
  coprime_tac  -- applies hp.coprime_of_not_dvd
  exact hp.coprime_of_not_dvd ha

-- Bezout's identity
example (a b : ℤ) : ∃ x y, a * x + b * y = Int.gcd a b := by
  exact ⟨Int.gcdA a b, Int.gcdB a b, Int.gcd_eq_gcd_ab a b⟩

-- Implementation sketch:
macro "gcd_tac" : tactic =>
  `(tactic| (
    simp only [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_self,
               Nat.gcd_zero_left, Nat.gcd_zero_right]
    first
    | exact Nat.gcd_dvd_left _ _
    | exact Nat.gcd_dvd_right _ _
    | apply Nat.dvd_gcd <;> assumption
  ))
```

**Automation Strategy:**
1. Normalize gcd expressions using commutativity/associativity
2. Check for trivial cases (gcd with 0, 1, self)
3. Apply Bezout for existence claims
4. Use coprimality lemmas when primes are involved

---

## 9. Chinese Remainder Theorem (CRT)

**Estimated Frequency:** ~90+ problems

Combining congruences with pairwise coprime moduli.

### Statement:
If $\gcd(m_i, m_j) = 1$ for $i \neq j$, then the system $x \equiv a_i \pmod{m_i}$ has a unique solution mod $m_1 m_2 \cdots m_k$.

### Examples:
- **Problem 14:** "By the Chinese Remainder Theorem, we can reduce to considering each prime power"
- **Problem 28:** "By CRT, it suffices to show the result for each prime dividing $m$"
- **Problem 46:** Constructing numbers with specific residue patterns

### Applications:
- Reducing problems to prime power cases
- Constructing numbers with desired properties
- Counting solutions to systems of congruences

### Lean Tactic Translation

**Tactic Name:** `crt` / `chinese_remainder`

**Description:** A tactic that applies the Chinese Remainder Theorem to combine or split congruence conditions.

**Key Mathlib Lemmas:**
- `ZMod.chineseRemainder` - the CRT isomorphism
- `Int.chineseRemainder` - integer version
- `Nat.coprime.mul_mod_right` - coprimality of products
- `ZMod.castHom` - ring homomorphisms for reduction

**Example Lean Code:**
```lean
-- CRT: combining congruences
example (x : ℤ) (h1 : x ≡ 2 [ZMOD 3]) (h2 : x ≡ 3 [ZMOD 5]) :
    x ≡ 8 [ZMOD 15] := by
  crt  -- combines using Chinese Remainder Theorem
  constructor <;> assumption

-- CRT: splitting to prime components
example (n : ℕ) (h : n ≡ 0 [MOD 6]) : n ≡ 0 [MOD 2] ∧ n ≡ 0 [MOD 3] := by
  crt_split 6 [2, 3]  -- splits modulus into coprime parts
  exact h

-- The isomorphism form
example : ZMod 15 ≃+* ZMod 3 × ZMod 5 :=
  ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 5)

-- Implementation sketch:
macro "crt" : tactic =>
  `(tactic| (
    apply Int.ModEq.of_div
    constructor
    · omega
    · omega
  ))
```

**Automation Strategy:**
1. Identify coprime moduli in the goal
2. Apply `ZMod.chineseRemainder` for the isomorphism
3. Split goals into separate modular conditions
4. Use decidability for small moduli verification

---

## 10. Multiplicative Order

**Estimated Frequency:** ~80+ problems

Using the order of elements in multiplicative groups.

### Definition:
$\text{ord}_n(a)$ = smallest positive $k$ such that $a^k \equiv 1 \pmod{n}$

### Key Properties:
- $\text{ord}_n(a) \mid \phi(n)$
- $a^k \equiv 1 \pmod{n}$ iff $\text{ord}_n(a) \mid k$

### Examples:
- **Problem 11:** "Let $u = \text{ord}_p(n)$. Then $u \mid 2A$ but $u \nmid A$"
- **Problem 24:** "Since $\text{ord}_q(5) \mid 2(p-q)$ and $\text{ord}_q(5) \nmid p-q$..."
- **Problem 209:** Computing orders modulo various moduli

### Lean Tactic Translation

**Tactic Name:** `order_tac` / `mult_order`

**Description:** A tactic for reasoning about multiplicative orders, including divisibility conditions and existence.

**Key Mathlib Definitions/Lemmas:**
- `orderOf` - multiplicative order in a group
- `orderOf_dvd_of_pow_eq_one` - order divides exponent
- `pow_orderOf_eq_one` - definition of order
- `ZMod.orderOf_dvd_card_sub_one` - order divides p-1

**Example Lean Code:**
```lean
-- Order divides exponent when power equals 1
example (G : Type*) [Group G] (g : G) (n : ℕ) (h : g ^ n = 1) :
    orderOf g ∣ n := by
  order_tac  -- applies orderOf_dvd_of_pow_eq_one
  exact orderOf_dvd_of_pow_eq_one h

-- Computing order in ZMod
example : orderOf (2 : ZMod 7) = 3 := by
  apply orderOf_eq_of_pow_and_pow_div_prime
  · decide  -- 2^3 = 1 mod 7
  · intro p hp hpd
    interval_cases p <;> decide

-- Implementation sketch:
macro "order_tac" : tactic =>
  `(tactic| (
    first
    | exact orderOf_dvd_of_pow_eq_one (by assumption)
    | apply orderOf_dvd_card_sub_one
    | exact pow_orderOf_eq_one _
  ))
```

**Automation Strategy:**
1. Identify the group element and ambient group
2. Apply divisibility lemmas for order
3. Use decidability for small finite groups
4. Connect to Fermat/Euler via `orderOf_dvd_card_sub_one`

---

## 11. Wilson's Theorem

**Estimated Frequency:** ~60+ problems

### Statement:
$(p-1)! \equiv -1 \pmod{p}$ for prime $p$

### Examples:
- **Problem 45:** "By Wilson's Theorem, $(p_n - 1)! \equiv -1 \pmod{p_n}$"
- **Problem 114:** "Wilson's theorem says $(p-1)! \equiv -1 \pmod{p}$, so remainder is 100"
- **Problem 40:** Uses Wilson's theorem in binomial coefficient analysis

### Applications:
- Computing factorials mod primes
- Proving primality conditions
- Analyzing binomial coefficients

### Lean Tactic Translation

**Tactic Name:** `wilson`

**Description:** A tactic that applies Wilson's theorem to factorial expressions modulo primes.

**Key Mathlib Lemmas:**
- `ZMod.wilsons_lemma` - $(p-1)! = -1$ in $\mathbb{Z}/p\mathbb{Z}$
- `Nat.Prime.factorial_mod` - factorial reduction
- `Int.ModEq.factorial` - integer modular version

**Example Lean Code:**
```lean
-- Wilson's theorem in ZMod
example (p : ℕ) [Fact p.Prime] : (Nat.factorial (p - 1) : ZMod p) = -1 := by
  wilson  -- applies ZMod.wilsons_lemma
  exact ZMod.wilsons_lemma p

-- Using Wilson for factorial computation
example : Nat.factorial 6 % 7 = 6 := by
  have h : (6! : ZMod 7) = -1 := ZMod.wilsons_lemma 7
  simp only [Nat.factorial] at h
  omega

-- Implementation sketch:
macro "wilson" : tactic =>
  `(tactic| (
    first
    | exact ZMod.wilsons_lemma _
    | rw [ZMod.wilsons_lemma]
    | simp [ZMod.wilsons_lemma]
  ))
```

**Automation Strategy:**
1. Detect factorial expressions in ZMod p
2. Apply `ZMod.wilsons_lemma`
3. Simplify using the fact that $(p-1)! = -1$
4. Handle variants like $(p-2)!$ via algebraic manipulation

---

## 12. Vieta Jumping / Root Flipping

**Estimated Frequency:** ~50+ problems

For Diophantine equations, particularly quadratics. Based on the observation that if $(a,b)$ is a solution, then $(a', b)$ where $a'$ is the other root is also a solution.

### Examples:
- **Problem 5:** "If $(m,n)$ is a solution, then $(m', n)$ where $m' = cn - m = \frac{n^2 + c}{m}$ is also a solution"
- **Problem 18:** Using root relationships to generate infinite families
- **Problem 112:** Showing primes $(p,q)$ with $p-q$ and $pq-q$ both squares

### Typical Application:
```
1. Start with a hypothetical minimal solution
2. Use Vieta's formulas to find another solution
3. Show the new solution is smaller (contradiction)
4. Conclude original solution doesn't exist or derive all solutions
```

### Lean Tactic Translation

**Tactic Name:** `vieta_jump`

**Description:** A tactic for applying Vieta jumping / infinite descent arguments on quadratic Diophantine equations.

**Key Mathlib Lemmas:**
- `Polynomial.sum_roots_eq_coeff` - Vieta's formulas
- `Polynomial.prod_roots_eq_coeff` - product of roots
- Well-founded recursion for descent

**Example Lean Code:**
```lean
-- Vieta jumping setup
-- For equation: x^2 - c*x*y + y^2 = k

-- The key insight: if (a,b) is a solution with a^2 - cab + b^2 = k,
-- then (cb - a, b) is also a solution

example (a b c k : ℤ) (h : a^2 - c*a*b + b^2 = k) :
    (c*b - a)^2 - c*(c*b - a)*b + b^2 = k := by
  ring_nf
  linarith [h]

-- Descent argument structure
theorem vieta_descent (P : ℤ → ℤ → Prop)
    (h_sym : ∀ a b, P a b → P b a)
    (h_jump : ∀ a b, P a b → P (c*b - a) b)
    (h_descent : ∀ a b, P a b → 0 < a → a ≤ b → c*b - a < a)
    (h_base : ∀ a, P a a → Q a) :
    ∀ a b, P a b → ∃ x, Q x := by
  -- Uses well-founded induction on |a| + |b|
  sorry

-- Implementation sketch:
macro "vieta_jump" eq:term "on" x:ident : tactic =>
  `(tactic| (
    -- Extract the quadratic and apply Vieta
    have h_other : ∃ $x', $eq := by
      use (c * y - $x)
      ring_nf
      assumption
    obtain ⟨x', hx'⟩ := h_other
    -- Continue with descent...
  ))
```

**Automation Strategy:**
1. Recognize quadratic Diophantine equation structure
2. Extract Vieta's relation for the "other root"
3. Set up well-founded descent argument
4. Verify the descent condition (new solution is smaller)

---

## 13. Lifting the Exponent (LTE) Lemma

**Estimated Frequency:** ~45+ problems

For analyzing exact prime power divisibility of $a^n \pm b^n$.

### Statements:
For odd prime $p$ with $p \mid a - b$ and $p \nmid a, b$:
- $\nu_p(a^n - b^n) = \nu_p(a - b) + \nu_p(n)$

For $p = 2$ with $2 \mid a - b$ (both odd):
- $\nu_2(a^n - b^n) = \nu_2(a - b) + \nu_2(a + b) + \nu_2(n) - 1$

### Examples:
- **Problem 11:** "Using LTE, $\nu_2(m^{2^r} - 1) = \nu_2(m-1) + \nu_2(m+1) + r - 1$"
- **Problem 54:** Analyzing $\nu_p(\binom{2n}{n})$

### Lean Tactic Translation

**Tactic Name:** `lte` / `lift_exponent`

**Description:** A tactic that applies the Lifting the Exponent lemma to compute p-adic valuations of $a^n - b^n$.

**Key Mathlib Lemmas:**
- `padicValNat.pow_sub_pow` - LTE for natural numbers
- `padicValInt.sub_pow` - LTE for integers
- `multiplicity.pow_sub_pow_of_prime` - general version

**Example Lean Code:**
```lean
-- LTE for odd primes
example (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2)
    (a b n : ℕ) (hab : p ∣ a - b) (ha : ¬p ∣ a) :
    padicValNat p (a^n - b^n) = padicValNat p (a - b) + padicValNat p n := by
  lte p  -- applies the LTE lemma
  exact padicValNat.pow_sub_pow hp hp_odd hab ha

-- LTE for p = 2
example (a b n : ℕ) (ha : Odd a) (hb : Odd b) :
    padicValNat 2 (a^n - b^n) =
    padicValNat 2 (a - b) + padicValNat 2 (a + b) + padicValNat 2 n - 1 := by
  lte 2
  exact padicValNat.pow_sub_pow_two ha hb

-- Implementation sketch:
macro "lte" p:term : tactic =>
  `(tactic| (
    first
    | apply padicValNat.pow_sub_pow <;> assumption
    | apply padicValNat.pow_sub_pow_two <;> assumption
    | apply multiplicity.pow_sub_pow_of_prime <;> assumption
  ))
```

**Automation Strategy:**
1. Identify $a^n - b^n$ or $a^n + b^n$ structure
2. Check the prime and verify conditions (divisibility, non-divisibility)
3. Apply appropriate LTE lemma (odd prime vs 2)
4. Simplify the resulting valuation expression

---

## 14. p-adic Valuation Analysis

**Estimated Frequency:** ~45+ problems

Using $\nu_p(n)$ (the exponent of prime $p$ in the factorization of $n$).

### Properties:
- $\nu_p(ab) = \nu_p(a) + \nu_p(b)$
- $\nu_p(a + b) \geq \min(\nu_p(a), \nu_p(b))$
- $\nu_p(n!) = \sum_{i=1}^{\infty} \lfloor n/p^i \rfloor$ (Legendre's formula)

### Examples:
- **Problem 10:** "We need $\nu_p(n) / 2 \leq \nu_p(a_n) \leq 2\nu_p(n)$"
- **Problem 51:** "For $k$ to work, $\nu_p(k) \geq 2018$ for some prime $p$"

### Lean Tactic Translation

**Tactic Name:** `padic_val` / `valuation_tac`

**Description:** A tactic for reasoning about p-adic valuations using standard properties.

**Key Mathlib Definitions/Lemmas:**
- `padicValNat` - p-adic valuation for naturals
- `padicValNat.mul` - multiplicativity
- `padicValNat.factorial` - Legendre's formula
- `padicValNat.self` - $\nu_p(p) = 1$

**Example Lean Code:**
```lean
-- Multiplicativity
example (p a b : ℕ) (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  padic_val  -- applies padicValNat.mul
  exact padicValNat.mul hp ha hb

-- Legendre's formula for factorials
example (p n : ℕ) (hp : p.Prime) :
    padicValNat p n! = ∑ i in Finset.range n, n / p^(i+1) := by
  padic_val  -- applies Legendre's formula
  exact padicValNat.factorial hp n

-- Valuation of prime powers
example (p k : ℕ) (hp : p.Prime) : padicValNat p (p^k) = k := by
  padic_val
  exact padicValNat.prime_pow_self hp k

-- Implementation sketch:
macro "padic_val" : tactic =>
  `(tactic| (
    simp only [padicValNat.mul, padicValNat.self, padicValNat.prime_pow_self,
               padicValNat.one, padicValNat.factorial]
    first
    | ring
    | omega
    | assumption
  ))
```

**Automation Strategy:**
1. Apply multiplicativity rules to decompose expressions
2. Use Legendre's formula for factorials
3. Simplify prime power valuations
4. Apply inequality properties for sums

---

## 15. Quadratic Residues / Legendre Symbol

**Estimated Frequency:** ~40+ problems

Analyzing which numbers are squares modulo primes.

### Definition:
$\left(\frac{a}{p}\right) = \begin{cases} 1 & \text{if } a \text{ is a QR mod } p \\ -1 & \text{if } a \text{ is a NQR mod } p \\ 0 & \text{if } p \mid a \end{cases}$

### Key Results:
- **Euler's Criterion:** $\left(\frac{a}{p}\right) \equiv a^{(p-1)/2} \pmod{p}$
- **Quadratic Reciprocity:** $\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}$

### Examples:
- **Problem 17:** "Since $\left(\frac{p}{3}\right) = 1$, there exists..."
- **Problem 109:** "By quadratic reciprocity, $\left(\frac{-3}{p}\right) = \left(\frac{p}{3}\right) = 1$"

### Lean Tactic Translation

**Tactic Name:** `qr_tac` / `legendre`

**Description:** A tactic for computing Legendre symbols and applying quadratic reciprocity.

**Key Mathlib Definitions/Lemmas:**
- `legendreSym` - Legendre symbol
- `legendreSym.quadratic_reciprocity` - QR law
- `legendreSym.eq_pow` - Euler's criterion
- `ZMod.isSquare_iff` - decidable square test

**Example Lean Code:**
```lean
-- Euler's criterion
example (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    legendreSym p a = a ^ ((p - 1) / 2) := by
  legendre  -- applies Euler's criterion
  exact legendreSym.eq_pow p a

-- Quadratic reciprocity
example (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  qr_tac  -- applies quadratic reciprocity
  exact legendreSym.quadratic_reciprocity hp hq hpq

-- Computing specific Legendre symbols
example : legendreSym 7 2 = 1 := by decide

-- Implementation sketch:
macro "legendre" : tactic =>
  `(tactic| (
    first
    | exact legendreSym.eq_pow _ _
    | apply legendreSym.quadratic_reciprocity <;> assumption
    | decide
  ))
```

**Automation Strategy:**
1. Apply Euler's criterion for explicit computation
2. Use quadratic reciprocity to reduce large symbols
3. Apply supplementary laws for $(-1/p)$ and $(2/p)$
4. Use decidability for small prime moduli

---

## 16. Pigeonhole Principle

**Estimated Frequency:** ~35+ problems

For counting and existence arguments.

### Statement:
If $n+1$ objects are placed in $n$ boxes, some box contains at least 2 objects.

### Examples:
- **Problem 19:** "By Pigeonhole, since $m$, $a_1$, ..., $a_m$ are fixed..."
- **Problem 43:** Analyzing sets of divisors
- **Problem 111:** Counting subsets with prime properties

### Lean Tactic Translation

**Tactic Name:** `pigeonhole`

**Description:** A tactic that applies the pigeonhole principle to derive existence of duplicates or collisions.

**Key Mathlib Lemmas:**
- `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` - pigeonhole
- `Fintype.exists_ne_map_eq_of_card_lt` - finite type version
- `Finset.card_le_card_of_inj_on` - injectivity bound

**Example Lean Code:**
```lean
-- Standard pigeonhole
example (f : Fin 11 → Fin 10) : ∃ i j, i ≠ j ∧ f i = f j := by
  pigeonhole  -- applies finite pigeonhole
  exact Fintype.exists_ne_map_eq_of_card_lt f (by norm_num : 10 < 11)

-- Pigeonhole for residue classes
example (S : Finset ℕ) (hS : S.card > 10) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ a % 10 = b % 10 := by
  pigeonhole S (· % 10) 10
  simp [Finset.card_range]
  exact hS

-- Implementation sketch:
macro "pigeonhole" : tactic =>
  `(tactic| (
    first
    | exact Fintype.exists_ne_map_eq_of_card_lt _ (by norm_num)
    | apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to <;>
      simp [Finset.card_range]; omega
  ))
```

**Automation Strategy:**
1. Identify the "pigeons" (domain) and "holes" (codomain)
2. Compare cardinalities
3. Apply appropriate pigeonhole lemma
4. Extract witnesses for the collision

---

## 17. Primitive Roots

**Estimated Frequency:** ~30+ problems

Using generators of multiplicative groups modulo primes.

### Definition:
$g$ is a primitive root mod $n$ if $\text{ord}_n(g) = \phi(n)$

### Key Facts:
- Primitive roots exist mod $1, 2, 4, p^k, 2p^k$ for odd prime $p$
- If $g$ is a primitive root mod $p$, then $\{g, g^2, \ldots, g^{p-1}\} = \{1, 2, \ldots, p-1\}$

### Examples:
- **Problem 8:** "Let $g$ be a primitive root modulo $p$"
- **Problem 11:** "Using primitive roots, we can find elements of specific orders"

### Lean Tactic Translation

**Tactic Name:** `prim_root`

**Description:** A tactic that introduces primitive roots and their properties.

**Key Mathlib Lemmas:**
- `IsPrimitiveRoot` - definition
- `ZMod.primitiveRoot_exists` - existence for primes
- `IsPrimitiveRoot.pow_eq_one_iff_dvd` - order characterization

**Example Lean Code:**
```lean
-- Existence of primitive roots mod prime
example (p : ℕ) [Fact p.Prime] : ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) := by
  prim_root  -- applies existence theorem
  exact ZMod.primitiveRoot_exists p

-- Using primitive root to parameterize units
example (p : ℕ) [Fact p.Prime] (hp : p > 2) (a : ZMod p) (ha : a ≠ 0) :
    ∃ k, a = (primitiveRoot p) ^ k := by
  obtain ⟨g, hg⟩ := ZMod.primitiveRoot_exists p
  exact hg.eq_pow_of_ne_zero ha

-- Implementation sketch:
macro "prim_root" : tactic =>
  `(tactic| (
    first
    | exact ZMod.primitiveRoot_exists _
    | apply IsPrimitiveRoot.pow_eq_one_iff_dvd <;> assumption
  ))
```

**Automation Strategy:**
1. Check if modulus admits primitive roots
2. Introduce a primitive root variable
3. Use the primitive root to parameterize all units
4. Apply order-divisibility characterizations

---

## 18. Zsigmondy's Theorem

**Estimated Frequency:** ~25+ problems

Existence of primitive prime divisors.

### Statement:
For $a > b \geq 1$ and $n > 1$, $a^n - b^n$ has a prime divisor that does not divide $a^k - b^k$ for any $0 < k < n$, except:
- $(a,b,n) = (2,1,6)$
- $a - b = 1$ and $n = 2$
- $a = 2$ and $n = 1$

### Examples:
- **Problem 4:** "By Zsigmondy's theorem, for $a > 1$ and $n > 1$, there exists a primitive prime divisor of $a^n - 1$ except for $(2,6)$ and $(2^k-1, 2)$"

### Lean Tactic Translation

**Tactic Name:** `zsigmondy`

**Description:** A tactic that applies Zsigmondy's theorem to obtain primitive prime divisors.

**Key Mathlib Lemmas:**
- `Nat.prime_pow_sub_one_has_prime_divisor` - basic version
- Zsigmondy's theorem (may need custom implementation)

**Example Lean Code:**
```lean
-- Zsigmondy's theorem (assuming available in Mathlib or custom)
theorem zsigmondy (a b n : ℕ) (ha : a > b) (hb : b ≥ 1) (hn : n > 1)
    (hne1 : (a, b, n) ≠ (2, 1, 6))
    (hne2 : ¬(a - b = 1 ∧ n = 2)) :
    ∃ p, p.Prime ∧ p ∣ a^n - b^n ∧ ∀ k < n, k > 0 → ¬(p ∣ a^k - b^k) := by
  sorry  -- Requires substantial proof

-- Using Zsigmondy
example : ∃ p, p.Prime ∧ p ∣ 2^7 - 1 ∧ ∀ k < 7, k > 0 → ¬(p ∣ 2^k - 1) := by
  zsigmondy 2 1 7  -- applies Zsigmondy's theorem
  all_goals norm_num

-- Implementation sketch:
macro "zsigmondy" a:term b:term n:term : tactic =>
  `(tactic| (
    apply zsigmondy $a $b $n <;>
    · first | omega | norm_num | decide
  ))
```

**Automation Strategy:**
1. Verify the conditions (a > b, n > 1)
2. Check against exceptional cases
3. Apply Zsigmondy's theorem
4. Extract the primitive prime divisor

---

## 19. Construction / Explicit Examples

**Estimated Frequency:** ~25+ problems

Building explicit solutions or counterexamples.

### Examples:
- **Problem 12:** "Take any solution of $k^2 - 10\ell^2 = 1$ and use $(x,y,z) = (5\ell, k, 1)$"
- **Problem 47:** Constructing sets achieving optimal bounds
- **Problem 53:** Explicit construction using sums of cubes

### Lean Tactic Translation

**Tactic Name:** `construct` / `use_witness`

**Description:** A tactic that helps construct explicit witnesses for existence proofs.

**Key Lean Tactics:**
- `use` - provide witness for exists
- `refine` - partial proof with holes
- `constructor` - split conjunctions
- `decide` - verify decidable propositions

**Example Lean Code:**
```lean
-- Explicit construction
example : ∃ n : ℕ, n^2 + n = 12 := by
  construct 3  -- provides witness and verifies
  norm_num

-- Construction with multiple witnesses
example : ∃ a b c : ℕ, a^2 + b^2 = c^2 ∧ a < b ∧ b < c := by
  use 3, 4, 5
  norm_num

-- Parameterized construction
example (k : ℕ) : ∃ n, n ≡ k [MOD 5] ∧ n > 100 := by
  use k + 105
  constructor
  · simp [Nat.ModEq, Nat.add_mod]
  · omega

-- Implementation sketch:
macro "construct" w:term : tactic =>
  `(tactic| (
    use $w
    first
    | decide
    | norm_num
    | simp; omega
  ))
```

**Automation Strategy:**
1. Identify the existential structure
2. Provide explicit witnesses with `use`
3. Verify conditions with `decide`, `norm_num`, or `omega`
4. Handle parameterized constructions with algebraic simplification

---

## 20. Pell Equations

**Estimated Frequency:** ~20+ problems

Solving equations of the form $x^2 - Dy^2 = 1$.

### Key Facts:
- Always has infinitely many solutions for non-square $D$
- Solutions form a group under a specific operation
- Fundamental solution generates all others

### Examples:
- **Problem 12:** "Reduces to Pell equation $k^2 - 10\ell^2 = 1$"
- **Problem 44:** "RMS problem reduces to finding Fibonacci-like structure"

### Lean Tactic Translation

**Tactic Name:** `pell`

**Description:** A tactic for solving and reasoning about Pell equations.

**Key Mathlib Definitions:**
- `Pell.Solution₁` - solutions to $x^2 - Dy^2 = 1$
- `Pell.fundamental_solution` - minimal positive solution
- `Pell.Solution₁.x`, `.y` - coordinates

**Example Lean Code:**
```lean
-- Pell equation solution structure
example (D : ℤ) (hD : ¬IsSquare D) (hD_pos : D > 0) :
    ∃ x y : ℤ, x > 0 ∧ y > 0 ∧ x^2 - D * y^2 = 1 := by
  pell D  -- applies Pell equation theory
  obtain ⟨sol, hsol⟩ := Pell.exists_solution₁ hD hD_pos
  exact ⟨sol.x, sol.y, sol.x_pos, sol.y_pos, sol.prop⟩

-- Generating infinitely many solutions
example (D : ℤ) (hD : ¬IsSquare D) :
    ∀ n : ℕ, ∃ x y : ℤ, x^2 - D * y^2 = 1 := by
  intro n
  pell D n  -- n-th solution
  sorry

-- Implementation sketch:
macro "pell" D:term : tactic =>
  `(tactic| (
    first
    | exact Pell.exists_solution₁ (by assumption) (by assumption)
    | apply Pell.Solution₁.pow
  ))
```

**Automation Strategy:**
1. Verify D is not a perfect square
2. Apply existence theorem for Pell equations
3. Generate solutions via the group structure
4. Extract coordinates and verify properties

---

## 21. Generating Functions / Roots of Unity Filter

**Estimated Frequency:** ~15+ problems

Using complex analysis and generating functions for counting.

### Key Technique:
Use $\omega = e^{2\pi i/n}$ to filter sums by residue class.

### Examples:
- **Problem 20:** "Using roots of unity filter with $\omega = e^{2\pi i/p}$..."
- **Problem 100:** "$\omega = e^{2\pi i/3}$, condition becomes $166 = \sum_{d|N} \omega^d$"

### Lean Tactic Translation

**Tactic Name:** `roots_of_unity_filter`

**Description:** A tactic that applies the roots of unity filter technique for counting.

**Key Mathlib Definitions:**
- `Complex.exp` - exponential function
- `IsPrimitiveRoot` - primitive roots of unity
- `Finset.sum_filter` - filtered sums

**Example Lean Code:**
```lean
-- Roots of unity filter for mod 3
-- Counts elements ≡ 0 mod 3 in a sum
theorem roots_unity_filter_mod3 (f : ℕ → ℂ) (S : Finset ℕ) :
    ∑ x in S.filter (· % 3 = 0), f x =
    (1/3 : ℂ) * (∑ x in S, f x + ∑ x in S, f x * ω + ∑ x in S, f x * ω^2) := by
  sorry  -- where ω = exp(2πi/3)

-- Usage example
example : (Finset.range 10).filter (· % 3 = 0) |>.card = 4 := by
  decide

-- Implementation sketch:
macro "roots_of_unity_filter" n:term : tactic =>
  `(tactic| (
    rw [Finset.sum_filter]
    -- Apply the roots of unity filter identity
    sorry
  ))
```

**Automation Strategy:**
1. Identify the modulus for filtering
2. Introduce primitive root of unity
3. Apply the filter identity
4. Simplify using properties of roots of unity

---

## 22. Gauss Sums

**Estimated Frequency:** ~10+ problems

Character sums for counting solutions to equations.

### Definition:
$G(\chi) = \sum_{a=0}^{p-1} \chi(a) \omega^a$ where $\omega = e^{2\pi i/p}$

### Key Property:
$|G(\chi)|^2 = p$ for non-principal characters

### Examples:
- **Problem 20:** "Define $G(a) = \sum_{x=0}^{p-1} \omega^{ax^2}$. We have $G^2 = (-1)^{(p-1)/2} p$"

### Lean Tactic Translation

**Tactic Name:** `gauss_sum`

**Description:** A tactic for computing and reasoning about Gauss sums.

**Key Mathlib Definitions:**
- `gaussSum` - Gauss sum definition
- `gaussSum_sq` - $G^2$ formula
- Character theory definitions

**Example Lean Code:**
```lean
-- Gauss sum squared
theorem gauss_sum_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (gaussSum (ZMod p) (χ₄ p))^2 = (-1)^((p-1)/2) * p := by
  gauss_sum  -- applies the Gauss sum square formula
  sorry

-- Using Gauss sums for counting
example (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun x : ZMod p => IsSquare x).card = (p + 1) / 2 := by
  gauss_sum
  sorry

-- Implementation sketch:
macro "gauss_sum" : tactic =>
  `(tactic| (
    first
    | exact gaussSum_sq _ _
    | rw [gaussSum]
    | simp [gaussSum]
  ))
```

**Automation Strategy:**
1. Identify Gauss sum structure in expression
2. Apply $|G|^2 = p$ identity
3. Use character orthogonality relations
4. Simplify sums over characters

---

## 23. Dirichlet's Theorem

**Estimated Frequency:** ~10+ problems

Primes in arithmetic progressions.

### Statement:
If $\gcd(a,d) = 1$, then $\{a, a+d, a+2d, \ldots\}$ contains infinitely many primes.

### Examples:
- **Problem 11:** "By Dirichlet's theorem, take a prime $p \equiv 1 \pmod{4k}$"
- **Problem 46:** "Guaranteed by CRT and Dirichlet's theorem"

### Lean Tactic Translation

**Tactic Name:** `dirichlet`

**Description:** A tactic that invokes Dirichlet's theorem to obtain primes in arithmetic progressions.

**Key Mathlib Lemmas:**
- `Nat.setOf_prime_and_eq_mod_infinite` - infinitely many primes in AP
- Custom axiom or deep theorem for full version

**Example Lean Code:**
```lean
-- Dirichlet's theorem (as axiom or imported theorem)
axiom dirichlet_theorem (a d : ℕ) (hd : d > 0) (hcoprime : Nat.Coprime a d) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}

-- Using Dirichlet to obtain specific primes
example : ∃ p, p.Prime ∧ p > 100 ∧ p ≡ 1 [MOD 4] := by
  dirichlet 1 4 100  -- finds prime ≡ 1 mod 4 greater than 100
  have h := dirichlet_theorem 1 4 (by norm_num) (by norm_num)
  exact Set.Infinite.exists_gt h 100

-- Implementation sketch:
macro "dirichlet" a:term d:term bound:term : tactic =>
  `(tactic| (
    have hinf := dirichlet_theorem $a $d (by omega) (by norm_num : Nat.Coprime $a $d)
    exact Set.Infinite.exists_gt hinf $bound
  ))
```

**Automation Strategy:**
1. Verify coprimality condition
2. Invoke Dirichlet's theorem for infinitude
3. Extract specific primes above given bounds
4. Use for existence proofs in AP

---

## 24. Algebraic Number Theory

**Estimated Frequency:** ~8+ problems

Using rings of integers, ideals, and unique factorization domains.

### Key Concepts:
- Ring of integers $\mathcal{O}_K$ of a number field $K$
- Principal Ideal Domains (PIDs)
- Norm functions

### Examples:
- **Problem 109:** "The ring of integers of $\mathbb{Q}(\sqrt{-3})$ is $\mathbb{Z}[\omega]$, a PID"
- **Problem 31:** "Using signatures modulo $n$ as polynomial evaluations"

### Lean Tactic Translation

**Tactic Name:** `alg_nt` / `ring_of_integers`

**Description:** A tactic for reasoning about algebraic integers and number fields.

**Key Mathlib Definitions:**
- `NumberField.RingOfIntegers` - ring of integers
- `Algebra.norm` - field norm
- `NumberField.isPrincipalIdealRing` - PID instances
- `GaussianInt` - Gaussian integers

**Example Lean Code:**
```lean
-- Gaussian integers as Z[i]
example : GaussianInt ≃+* (𝓞 (ℚ⟮Complex.I⟯)) := by
  sorry  -- isomorphism to ring of integers

-- Norm in quadratic fields
example (z : GaussianInt) : z.norm = z.re^2 + z.im^2 := by
  simp [GaussianInt.norm]

-- Using UFD property
example (z : GaussianInt) (hz : z.norm.Prime) : Prime z := by
  alg_nt  -- uses norm-prime implies prime
  exact GaussianInt.prime_of_norm_prime hz

-- Implementation sketch:
macro "alg_nt" : tactic =>
  `(tactic| (
    first
    | apply GaussianInt.prime_of_norm_prime
    | apply NumberField.RingOfIntegers.isPrincipalIdealRing
    | simp [Algebra.norm]
  ))
```

**Automation Strategy:**
1. Identify the number field in context
2. Use ring of integers structure
3. Apply norm multiplicativity
4. Leverage PID/UFD properties when available

---

## 25. Simon's Favorite Factoring Trick (SFFT)

**Estimated Frequency:** ~8+ problems

Adding/subtracting constants to complete factorization.

### Technique:
Transform $xy + ax + by = c$ to $(x+b)(y+a) = c + ab$

### Examples:
- **Problem 48:** "$xy - x - y = 5 \Rightarrow (x-1)(y-1) = 6$"
- **Problem 56:** "Applying SFFT results in $(5x-1)(5y-1) = 26$"

### Lean Tactic Translation

**Tactic Name:** `sfft` / `factor_trick`

**Description:** A tactic that applies Simon's Favorite Factoring Trick to bilinear expressions.

**Key Lean Tactics:**
- `ring` - algebraic manipulation
- `nlinarith` - nonlinear arithmetic
- Custom rewriting rules

**Example Lean Code:**
```lean
-- SFFT: xy + ax + by = c ↔ (x+b)(y+a) = c + ab
theorem sfft (x y a b c : ℤ) :
    x * y + a * x + b * y = c ↔ (x + b) * (y + a) = c + a * b := by
  constructor <;> intro h <;> linarith

-- Usage example
example (x y : ℤ) (h : x * y - x - y = 5) : (x - 1) * (y - 1) = 6 := by
  sfft at h  -- transforms to factored form
  linarith

-- Finding integer solutions
example : {(x, y) : ℤ × ℤ | x * y - x - y = 5} =
    {(2, 7), (7, 2), (0, -5), (-5, 0), (3, 4), (4, 3), (-1, -2), (-2, -1)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf, Set.mem_insert_iff]
  sfft
  -- Now: (x-1)(y-1) = 6, enumerate factor pairs of 6
  sorry

-- Implementation sketch:
macro "sfft" : tactic =>
  `(tactic| (
    simp only [sub_eq_add_neg, mul_add, add_mul]
    ring_nf
  ))

macro "sfft" "at" h:ident : tactic =>
  `(tactic| (
    have h' := sfft _ _ _ _ _ |>.mp $h
    clear $h
    rename_i $h => h'
  ))
```

**Automation Strategy:**
1. Identify bilinear expression $xy + ax + by$
2. Compute the constant to add ($ab$)
3. Rewrite as $(x+b)(y+a) = c + ab$
4. Factor the RHS to enumerate solutions

---

## Summary Statistics

| Rank | Technique | Estimated Frequency | Lean Tactic |
|------|-----------|---------------------|-------------|
| 1 | Modular Arithmetic | ~400+ | `mod_reduce`, `decide_mod` |
| 2 | Case Analysis | ~250+ | `nt_cases`, `parity_cases` |
| 3 | Prime Factorization | ~200+ | `factor_analyze` |
| 4 | Contradiction | ~180+ | `by_contra`, `nt_contra` |
| 5 | Induction | ~150+ | `induction`, `strong_induction` |
| 6 | Bounding Arguments | ~140+ | `nt_bound` |
| 7 | Fermat/Euler Theorems | ~120+ | `fermat`, `euler_totient` |
| 8 | GCD/LCM Properties | ~100+ | `gcd_tac`, `coprime_tac` |
| 9 | Chinese Remainder Theorem | ~90+ | `crt` |
| 10 | Multiplicative Order | ~80+ | `order_tac` |
| 11 | Wilson's Theorem | ~60+ | `wilson` |
| 12 | Vieta Jumping | ~50+ | `vieta_jump` |
| 13 | LTE Lemma | ~45+ | `lte` |
| 14 | p-adic Valuations | ~45+ | `padic_val` |
| 15 | Quadratic Residues | ~40+ | `legendre`, `qr_tac` |
| 16 | Pigeonhole Principle | ~35+ | `pigeonhole` |
| 17 | Primitive Roots | ~30+ | `prim_root` |
| 18 | Zsigmondy's Theorem | ~25+ | `zsigmondy` |
| 19 | Explicit Construction | ~25+ | `construct` |
| 20 | Pell Equations | ~20+ | `pell` |
| 21 | Roots of Unity Filter | ~15+ | `roots_of_unity_filter` |
| 22 | Gauss Sums | ~10+ | `gauss_sum` |
| 23 | Dirichlet's Theorem | ~10+ | `dirichlet` |
| 24 | Algebraic Number Theory | ~8+ | `alg_nt` |
| 25 | SFFT | ~8+ | `sfft` |

---

## Notes

1. **Techniques Often Combine:** Most solutions use multiple techniques. Modular arithmetic is almost always present as a foundational tool.

2. **Competition Level Correlation:** More advanced techniques (Zsigmondy, LTE, algebraic number theory) tend to appear in higher-difficulty problems (difficulty 7+).

3. **Problem Sources:** The dataset includes problems from IMO, USAMO, China TST, China MO, JBMO, HMMT, and other competitions.

4. **Frequency Estimates:** These are approximate based on manual review of ~200+ problems. The actual frequencies may vary.

5. **Lean Tactic Implementation Notes:**
   - Many proposed tactics would require custom implementation or extension of Mathlib
   - Some tactics (`decide`, `omega`, `norm_num`) are built-in and highly useful
   - Complex tactics (Vieta jumping, Zsigmondy) may require substantial proof automation
   - The `ZMod` type in Mathlib is excellent for modular arithmetic
   - `padicValNat` and related functions support p-adic valuation reasoning
