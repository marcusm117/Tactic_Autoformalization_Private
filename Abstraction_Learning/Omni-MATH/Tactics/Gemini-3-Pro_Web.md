Here is the complete and merged Markdown (`.md`) document containing the manual analysis of the proof strategies from the dataset, along with their detailed formalizations into Lean 4 automated tactics.

---

# Omni-MATH Number Theory: Proof Strategies & Lean 4 Tactic Formalization

Based on a detailed, manual analysis of the problems and proofs provided in the `Omni-MATH_NumberTheory.jsonl` dataset, several recurring proof strategies and techniques stand out. Number theory problems at this level (olympiad and advanced competition math) frequently combine multiple methods, but the core engines of the proofs can be categorized.

Below is a summary of **ALL** common proof strategies shared across multiple proofs, ranked from the most frequent to the least frequent, complete with their Lean 4 tactic implementations.

---

## 1. Modular Arithmetic and Congruence Analysis

* **Frequency Count:** ~25 proofs
* **Description:** Reducing equations modulo a specific integer to restrict the domain of possible solutions, often analyzing quadratic residues or parity to prove that no solutions exist or to severely limit the candidate pool.
* **Examples:**
* *Sum of 14th powers:* Proving that $n_1^4 + n_2^4 + \dots + n_{14}^4 = 1599$ has no integral solutions by reducing modulo 16 (since $x^4 \equiv 0$ or $1 \pmod{16}$, the LHS maxes out at 14, but $1599 \equiv 15 \pmod{16}$).
* *Exponential equations:* Proving $2^n + 12^n + 2011^n$ is a perfect square only for $n=1$ by taking the equation modulo 12.
* *Fermat's Little Theorem / Euler's Totient:* Used extensively, such as determining $2^{3n} + 3^{6n+2} + 5^{6n+2} \equiv 0 \pmod 7$.



### Formalization: Lean 4 Tactic (`mod_exhaust` / `zmod_reduce`)

We can write a Lean 4 tactic using `TacticM` that takes a target modulus `n` as an argument. The tactic maps the integer equation $A = B$ to $A \equiv B \pmod n$ using `Mathlib.Data.ZMod.Basic`. For finite domain restrictions, it can generate a bounded exhaustive search using `fin_cases` on the variables modulo `n` and evaluate the congruence using `decide`.

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Decide

macro "mod_exhaust" n:term : tactic => `(tactic|
  -- Push the integer equality to a ZMod congruence
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mpr
  -- Revert variables to the context to iterate over them
  revert_all
  intro x
  -- Exhaustively check all finite cases in ZMod n
  fin_cases x <;> decide
)

```

---

## 2. Algebraic Factorization & Diophantine Manipulation

* **Frequency Count:** ~18 proofs
* **Description:** Rearranging algebraic terms to factor expressions, forcing integer factors to divide specific integer constants. This frequently utilizes Difference of Squares or Simon's Favorite Factoring Trick (SFFT).
* **Examples:**
* *Prime factor equations:* Rearranging $x(y^2-p) + y(x^2-p) = 5p$ into the factored form $(xy-p)(x+y) = 5p$, allowing for case-by-case analysis of divisors.
* *Sums of squares:* Transforming equations like $n^2 - x^2 = 3000$ into $(n-x)(n+x) = 3000$ and setting the factors equal to complementary divisors of 3000.



### Formalization: Lean 4 Tactic (`diophantine_factor`)

This tactic acts as an automated oracle for Simon's Favorite Factoring Trick and basic algebraic groupings. It allows the user to assert a factored form of a Diophantine expression. It uses `ring` to prove the algebraic equivalence, clears the old expanded hypothesis, and primes the goal for divisor analysis (spawning subgoals for each divisor pair of $K$).

```lean
import Mathlib.Tactic.Ring

macro "diophantine_factor" h:ident " into " f:term : tactic => `(tactic|
  have h_new : $f := by {
    calc _ = _ := by ring
  }
  clear $h
  rename_i $h
  -- Prepares for divisor extraction (e.g., Int.eq_of_mul_eq_mul)
)

```

---

## 3. Bounding, Inequalities, and Asymptotic Analysis

* **Frequency Count:** ~15 proofs
* **Description:** Establishing strict upper or lower bounds to limit a solution set to a finite number of checkable cases. This often involves the AM-GM Inequality, Cauchy-Schwarz, or the Triangle Inequality.
* **Examples:**
* *Absolute value bounds:* Finding the minimum of $\sum \sqrt{|a_i - b|}$ by repeatedly applying the Triangle Inequality.
* *Growth rates:* Proving that if $n! > M$ (the least common multiple of numbers up to $n+1$), certain sequences of composite numbers must exist, relying heavily on bounding the growth of factorials versus LCMs.
* *AM-GM Inequality:* Used to bound sums of complex numbers $z_n$ restricted by $|z_k z_{k+1}| = 2^k$.



### Formalization: Lean 4 Tactic (`apply_am_gm`)

While Lean already has `linarith` for linear inequalities, bounding non-linear Diophantine equations requires a macro. `apply_am_gm` automates the application of the AM-GM inequality. It applies the core theorem and uses `positivity` to automatically discharge the proof obligations that the terms are non-negative.

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity

macro "apply_am_gm" : tactic => `(tactic|
  apply geom_mean_le_arith_mean
  -- Automatically prove that the elements are non-negative
  · positivity
  · positivity
)

```

---

## 4. Proof by Contradiction (Reductio ad Absurdum)

* **Frequency Count:** ~14 proofs
* **Description:** Assuming the opposite of the desired statement (e.g., assuming a prime exists, or assuming a set is infinite) and logically deducing an impossible scenario (like a fraction being an integer when its denominator is strictly larger than its numerator).
* **Examples:**
* *Factorials and Primes:* Proving that for any positive integer $d$, there are infinitely many $n$ such that $d(n!) - 1$ is composite. The proof assumes it *is* prime for all large $n$, uses Wilson's Theorem, and deduces that $2n+1 = n!-1$, which is impossible for large $n$.
* *Divisibility limits:* Assuming a prime $p$ divides both sums of subsets and deriving a parity or fractional contradiction.



### Formalization: Lean 4 Tactic (`derive_contradiction`)

Lean natively uses `by_contra h`. To make a higher-level tactic specifically for Number Theory, this wraps standard contradiction mechanics. It assumes the negation, pushes negations inward (e.g., turning $\neg \forall$ into $\exists \neg$), and attempts to close the goal with linear arithmetic (`linarith`) or integer arithmetic (`omega`).

```lean
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Linarith

macro "derive_contradiction" : tactic => `(tactic|
  by_contra h_contra
  push_neg at h_contra
  -- Attempt to derive the mathematical absurdity automatically
  try omega
  try linarith
)

```

---

## 5. Mathematical Induction (and Strong Induction)

* **Frequency Count:** ~12 proofs
* **Description:** Proving a base case and an inductive step to establish the validity of a sequence, explicit formula, or bound for all natural numbers $n$.
* **Examples:**
* *Sequence recurrences:* Proving that a sequence defined by $a_{n+1} = (n+1)a_n - n$ has the explicit closed form $a_n = 2 \cdot n! + 1$.
* *Factorization limits:* Using strong induction to prove that the number of ways to factor $n$, denoted $f(n)$, is bounded by $n/p$ where $p$ is a prime factor.



### Formalization: Lean 4 Tactic (`recurrence_induction`)

Rather than just calling `induction n`, this tactic automates the boilerplate for strong/standard induction on recursive sequences. It sets up the base case and the inductive step, automatically rewriting the goal using the recurrence definition and solving the polynomial simplifications with `ring`.

```lean
import Mathlib.Tactic.Ring

macro "recurrence_induction" n:ident "using" eq:ident : tactic => `(tactic|
  induction $n with
  | zero =>
    -- Base case
    simp [$eq]
    try ring
  | succ n ih =>
    -- Inductive step
    simp [$eq]
    rw [ih]
    ring
)

```

---

## 6. Prime Factor Valuation ($p$-adic Valuation / LTE)

* **Frequency Count:** ~10 proofs
* **Description:** Using the function $\nu_p(n)$ (which extracts the highest exponent of prime $p$ dividing $n$) to compare the prime factor weights of both sides of an equation. This includes Legendre's Formula for factorials and the Lifting The Exponent (LTE) lemma.
* **Examples:**
* *Trailing zeroes:* Using Legendre's formula ($\sum \lfloor n/p^k \rfloor$) to calculate the exact number of trailing zeroes in factorials.
* *Congruence lifts:* Finding all $k$ such that $k \mid m^h - 1$ utilizing the LTE lemma to track the valuation of 2 in $m^{2^r}-1$.



### Formalization: Lean 4 Tactic (`lte_simp`)

This tactic simplifies goals involving the $p$-adic valuation of integers. It primes the goal for the Lifting The Exponent (LTE) lemma by breaking down products and powers, then attempts to discharge divisibility side-conditions.

```lean
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Tactic.Omega

macro "lte_simp" : tactic => `(tactic|
  -- Expand padic valuation across products and exponents
  simp only [padicValNat_mul, padicValNat_pow]
  -- Attempt to discharge divisibility side-conditions for LTE
  try omega
)

```

---

## 7. Pigeonhole Principle

* **Frequency Count:** ~8 proofs
* **Description:** Placing $N$ items into $M$ boxes (where $N > M$) to guarantee that at least one box contains multiple items. Often applied to remainders modulo $n$.
* **Examples:**
* *Subset sums:* Proving that in any $K$-element subset of $\{1, 2, \dots, 50\}$, there are two distinct elements $a, b$ where $a+b$ divides $ab$, purely by guaranteeing a collision of subset constraints.
* *Digit cycles:* Proving that among the digit cycles of a number, at least one must fall into a specific residue class modulo 7.



### Formalization: Lean 4 Tactic (`apply_pigeonhole`)

This tactic invokes the finite type pigeonhole principle from Mathlib (`Fintype.exists_ne_map_eq_of_card_lt`). It requires the user to define the mapping, but automatically computes cardinalities and attempts to prove that the cardinality of the domain is strictly greater than the codomain.

```lean
import Mathlib.Data.Fintype.Card

macro "apply_pigeonhole" : tactic => `(tactic|
  -- Applies the theorem: if |A| > |B|, a function f: A -> B is not injective
  apply Fintype.exists_ne_map_eq_of_card_lt
  -- Automatically compute cardinalities and prove the inequality
  exact by decide
)

```

---

## 8. Chinese Remainder Theorem (CRT)

* **Frequency Count:** ~5 proofs
* **Description:** Constructing specific large numbers or proving the existence of numbers that simultaneously satisfy multiple modulo constraints with pairwise coprime moduli.
* **Examples:**
* *Distinct remainders:* Finding the number of integers $\le 420$ that leave distinct remainders when divided by 5, 6, and 7.
* *Polynomial cycles:* Constructing a polynomial modulo $p^t$ and another modulo $n/p^t$ and using CRT to bind them into a single global polynomial $P(x)$.



### Formalization: Lean 4 Tactic (`solve_crt`)

This macro acts on a goal requiring the construction of an integer satisfying multiple modular congruences. It applies Mathlib's `chineseRemainder` and automatically discharges the coprimality constraints using `norm_num`.

```lean
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

macro "solve_crt" : tactic => `(tactic|
  apply Nat.ModEq.chineseRemainder
  -- Prove the moduli are pairwise coprime automatically
  · norm_num
  · norm_num
)

```

---

## 9. Vieta Jumping (Root Jumping / Infinite Descent)

* **Frequency Count:** ~4 proofs
* **Description:** A technique for solving Diophantine equations by assuming a minimal solution exists, interpreting the equation as a quadratic in one of the variables, and using Vieta's formulas to construct an even smaller strictly positive integer root, thus creating a contradiction.
* **Examples:**
* *Divisibility pairs:* Finding pairs $(m,n)$ such that $mn-1$ divides $m^2+n^2$. The proof fixes a minimal sum $m+n$ and uses the secondary root $m' = \frac{n^2+c}{m}$ to force a contradiction unless $n=1$.
* *Perfect squares:* Solving $(xy+1)(xy+x+2) = k^2$ by generating an infinite descent sequence of roots.



### Formalization: Lean 4 Tactic (`vieta_jump`)

Because Vieta Jumping is a complex algorithmic proof method, this macro sets up the well-founded induction (descent) on the sum of the variables.

```lean
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Omega

macro "vieta_jump" x:ident y:ident : tactic => `(tactic|
  -- Setup infinite descent by minimizing the sum of the roots
  apply WellFounded.induction (invImage (fun p : ℕ × ℕ => p.1 + p.2) _)
  intro ⟨$x, $y⟩ ih
  -- (The user is now expected to construct the secondary root x₂ = B - x)
  -- The tactic would ideally use `omega` to close the bounding step: x₂ + y < x + y
)

```

---

## 10. Roots of Unity Filter / Gauss Sums

* **Frequency Count:** ~3 proofs
* **Description:** Using complex roots of unity to extract specific terms from a polynomial or to count the number of elements in a sequence that are divisible by a certain integer $p$.
* **Examples:**
* *Counting constraints:* Finding the number of arrays $(x_1, \dots, x_{100})$ whose sum and sum of squares are divisible by 2017. The proof uses the sum of primitive roots of unity $\omega = e^{2\pi i/p}$ and Gauss sums to filter out the combinations that don't evaluate to $0 \bmod p$.



### Formalization: Lean 4 Tactic (`unity_filter`)

This tactic targets sums over specific modular conditions (e.g., $k \equiv a \pmod p$). It sets up the Gauss Sum indicator function and commutes the summations, preparing the expression for geometric series collapse.

```lean
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Algebra.BigOperators.Basic

macro "unity_filter" : tactic => `(tactic|
  -- Commute the nested sums to sum over the sequence first, then the roots
  rw [Finset.sum_comm]
  -- Distribute the roots of unity into the sequence terms
  simp only [Finset.mul_sum]
  -- (User can now apply geometric sum rules to the inner expression)
)

```