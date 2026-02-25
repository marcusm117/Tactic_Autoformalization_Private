Below is **your original answer (unchanged in structure/content)**, and for **each** strategy I’ve added a subsection **“How to turn this into a Lean tactic”** explaining (1) what the tactic should *do*, (2) what existing mathlib tactics/lemmas it should leverage, and (3) a small **Lean 4 macro sketch** you can use as a starting point.

> Notes up front (Lean reality check):
>
> * Many “number theory proof strategies” are best implemented in Lean as **(a) a normalization step** + **(b) a bundle of existing tactics** (`simp`, `ring`, `linarith`, `nlinarith`, `omega`, `aesop`, `norm_num`, `native_decide`, etc.).
> * Some (counting, pigeonhole, involutions) are less “one-tactic solves all” and more “tactic scaffolds the standard shape” (sets up `Finset`, introduces classical choice, applies the right lemma template).

---

## Ranked common proof strategies (most → least frequent)

### 1) **Modular arithmetic / congruence chasing** — **28**

**What it looks like:** reduce expressions mod small primes (2,3,4,5,7,11,13…), compare residues, force contradictions, or count solutions residue-by-residue.
**Examples**

* **IDX 247**: counting 3-digit numbers with digits 1–7 uses a rewrite mod 7 (e.g. (100a+10b+c \equiv 2a+3b+c\pmod 7)) plus inclusion–exclusion.
* **IDX 533**: binary Hamming weight minimization uses “possible powers of 2 mod 7 are only {1,2,4}”, ruling out cases (k(n)=1,2).
* **IDX 403**: divisibility by (1001=7\cdot 11\cdot 13) handled by counting valid residues mod each factor and combining (CRT-flavored).

**Count (audit):** 28 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** turn “congruence goals” into something **ring-like** (typically in `ZMod n`), then let `ring`/`ring_nf`/`nlinarith` close it.

**Core moves in Lean:**

* Normalize congruence goals:

  * If goal is `a ≡ b [ZMOD n]` (usually `Int.ModEq`/`Nat.ModEq`), try rewriting it into an equality in `ZMod n`.
* Push casts and simplify:

  * Use `zify` (Nat→Int) when inequalities are around.
  * Use `simp` to reduce `%`/`mod` expressions where possible.
* Solve the algebra:

  * In `ZMod n`, `ring` / `ring_nf` often works beautifully.

**Starter macro sketch (Lean 4):**

```lean
import Mathlib

open Lean Elab Tactic

/-- Try to solve modular arithmetic goals by moving to `ZMod` and using algebra. -/
elab "nt_mod" : tactic => do
  evalTactic (← `(tactic|
    first
      | -- If the goal is already in ZMod, just normalize and ring
        ring_nf
      | -- Try to push everything into ZMod and then ring
        (simp at *; try zify at *; try ring_nf; try ring)
      | -- For small moduli / finite goals: brute force
        (native_decide)
      | aesop
  ))
```

**Usage pattern:**

* Works best after you’ve already stated things in `ZMod n` or `ModEq`.
* Typical workflow:

  1. `have : (a : ZMod n) = b := by nt_mod`
  2. convert back to congruence if needed.

---

### 2) **Prime factorization & p-adic valuation (exponent bookkeeping)** — **22**

**What it looks like:** compare exponents of primes on both sides; use (v_p(\cdot)) arguments; classify by prime-power structure.
**Examples**

* **IDX 494**: (3m^3=5n^5) → compare 3-adic and 5-adic exponents to force minimal exponents and smallest solution.
* **IDX 325**: largest (n) with (2^n\mid (7^{2048}-1)) by factoring (7^{2048}-1=\prod (7^{2^k}+1)) and counting factors of 2.
* **IDX 546**: “cubic square” characterization becomes a congruence restriction on valuations: (v_p(n)\not\equiv 1,5\pmod 6).

**Count (audit):** 22 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** reduce statements like “(p^k\mid x)” or “(v_p(x)=k)” to standardized lemmas and let simp + arithmetic finish.

**Core moves in Lean:**

* Choose the valuation API:

  * `padicValNat p n` (Nat valuation) is common in mathlib.
  * Divisibility by prime powers: use lemmas relating `p^k ∣ n` to `k ≤ padicValNat p n` (there are standard lemmas in mathlib; you’ll usually `simp`/`have` them via `by`).
* Expand valuations over products/powers:

  * `simp` can unfold `padicValNat` over `*` and `^` with the right lemmas in scope.
* Convert “equality of products” into “equal valuations for each prime”:

  * `have := congrArg (padicValNat p) hEq` is a standard trick, then `simp` and compare.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Valuation bookkeeping: push goals into `padicValNat` / prime-power divisibility facts. -/
elab "nt_vp" : tactic => do
  evalTactic (← `(tactic|
    -- Try to turn divisibility into valuation inequalities, then simplify.
    first
      | (simp at *; omega)
      | (simp at *; nlinarith)
      | (simp at *; ring_nf)
      | aesop
  ))
```

**What makes this “real”:**

* In practice you’ll add helper lemmas to your environment, e.g. simp-lemmas about
  `padicValNat (m*n)`, `padicValNat (m^k)`, and `p^k ∣ n ↔ k ≤ padicValNat p n` (or similar).

---

### 3) **Casework (split into cases; small values / parity / special subcases)** — **21**

**What it looks like:** break by parity, primality/compositeness, size regimes, or specific small parameter values; solve each branch.
**Examples**

* **IDX 312**: explicit multi-case split (small (n), both composite, etc.) to show a floor expression is always even.
* **IDX 273**: “six divisors” → classify into (p^5) vs (p^2q), then prune by constraints.
* **IDX 741**: diophantine divisibility problem starts by isolating cases like (b=1), then general (b).

**Count (audit):** 21 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** automate the boilerplate “split on parity / split on `n=0` or `n=1` / split on inequalities / split on decidable predicates”.

**Core moves in Lean:**

* Use `by_cases` aggressively:

  * `by_cases h : Even n`
  * `by_cases h0 : n = 0`
  * `by_cases hp : Nat.Prime n`
* For bounded naturals, use `interval_cases` (when you can show `n ≤ K`).
* Let `omega` solve arithmetic side conditions after splitting.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Lightweight casework driver (parity, zero/nonzero, etc.). -/
elab "nt_cases" : tactic => do
  evalTactic (← `(tactic|
    first
      | (by_cases h : Even _ <;> simp [h] at * <;> try omega <;> try nlinarith)
      | (by_cases h : (_ = (0:Nat)) <;> simp [h] at * <;> try omega <;> try nlinarith)
      | (by_cases h : Nat.Prime _ <;> simp [h] at * <;> try aesop)
      | aesop
  ))
```

---

### 4) **Algebraic rewriting / factoring (including Vieta-style coefficient-root relations)** — **14**

**What it looks like:** rewrite into a more structured form (difference of squares, quadratic in a new variable, symmetric sums), then use that structure.
**Examples**

* **IDX 650**: let (t=2^x), rewrite (1+2^x+2^{2x+1}=1+t+2t^2=y^2) → treat as quadratic/diophantine in ((t,y)) with case checks.
* **IDX 728**: (\frac1a+\frac1b+\frac1c=\frac1p) → multiply through to (abc=p(ab+ac+bc)), then combine with bounds.
* **IDX 351**: polynomial with nested radicals: uses sums/products of roots and Vieta identities to solve for parameters.

**Count (audit):** 14 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** normalize algebra and factor, then hand off to `ring`/`nlinarith`/`linarith`.

**Core moves in Lean:**

* `ring_nf` / `nlinarith` are your workhorses.
* For factoring steps:

  * `ring_nf` often exposes factors.
  * `have := by nlinarith` after rewriting can replace many “complete the square” steps.
* For Vieta:

  * represent polynomials using `Polynomial`, use `by` with `simp`/`ring`.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Algebraic normalization + factoring-ish simplification driver. -/
elab "nt_factor" : tactic => do
  evalTactic (← `(tactic|
    first
      | ring_nf
      | (simp at *; ring_nf)
      | (simp at *; nlinarith)
      | (simp at *; linarith)
      | aesop
  ))
```

---

### 5) **Combinatorial counting / packing / partitioning (incl. inclusion–exclusion)** — **14**

**What it looks like:** partition the set into blocks, count configurations, use PIE, count exponent allocations, etc.
**Examples**

* **IDX 117**: digit-product = 180 → enumerate digit-multisets then count permutations.
* **IDX 416**: “difference not in S” style constraint → block ({1,2,3},{4,5,6},\dots) so at most one per block.
* **IDX 377**: divisor triples of 360 → translate to exponent triples ((a_i,b_i,c_i)) with sum constraints, then count solutions.

**Count (audit):** 14 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** set up the classical finset framework automatically:

* introduce `classical`,
* rewrite set statements into `Finset`/`Fintype`,
* reduce counting equalities to `simp` + known lemmas (`card_filter`, `card_bind`, `card_product`, `card_disjoint_union`, PIE lemma templates).

**Core moves in Lean:**

* `by classical` almost always needed.
* `simp` with `Finset.card_*` lemmas + `decide` for finite membership.
* For PIE: use lemma patterns like `card_union_add_card_inter` etc.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Counting scaffolding: turns on classical logic and tries simp-heavy finset counting. -/
elab "nt_count" : tactic => do
  evalTactic (← `(tactic|
    classical
    -- lots of counting goals reduce to simp if the finsets are set up
    first
      | (simp at *; omega)
      | (simp at *; nlinarith)
      | (simp at *; ring_nf)
      | aesop
  ))
```

---

### 6) **Explicit construction / witness / extremal example** — **9**

**What it looks like:** build an explicit object meeting the conditions (a set, sequence, parameters (m,n), etc.), often with a “minimal counterexample” flavor.
**Examples**

* **IDX 156**: explicit parameter choice (m=a^2+a-1, n=a+1) shows *every* positive integer is representable in the required form.
* **IDX 468**: constructs an infinite sequence ensuring every pairwise sum is square-free (choosing the next term as (1+Mx) with huge (M)).
* **IDX 260**: proves all odd (N) are “special” using binary decomposition into powers of 2 (all coprime to odd (N)).

**Count (audit):** 9 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** for existential goals, repeatedly:

* `refine ⟨?, ?_⟩` (or `refine ⟨_, _, ?_⟩`),
* fill witnesses using `exact`/`refine`,
* solve the remaining obligations with `simp`/`ring`/`omega`.

**Core moves in Lean:**

* `refine` + metavariables is the right “construction UI”.
* After building, let `nt_factor` / `nt_mod` / `simp` finish.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Existential/construction driver: build witnesses and discharge goals by simp/algebra. -/
elab "nt_witness" : tactic => do
  evalTactic (← `(tactic|
    first
      | (refine ⟨?_, ?_⟩ <;> try simp <;> try ring_nf <;> try omega <;> try nlinarith)
      | (refine ⟨?_, ?_, ?_⟩ <;> try simp <;> try ring_nf <;> try omega <;> try nlinarith)
      | aesop
  ))
```

---

### 7) **Group/field methods (orders, primitive roots, FLT/Euler, CRT)** — **8**

**What it looks like:** use multiplicative order, primitive roots, finite-field products, or CRT to combine modular constraints.
**Examples**

* **IDX 39**: binomial congruence mod prime (p=6k+1) using primitive roots / FLT-style structure.
* **IDX 208**: (n^{c_n}\equiv 1\pmod{210}) → treat as orders mod 3,5,7 and take an LCM (CRT perspective).
* **IDX 442**: lemma over (\mathbb{F}_p^*) involving (\prod(1+\alpha^n)), explicitly field-structural.

**Count (audit):** 8 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** detect you’re in a finite multiplicative group (often `ZMod nˣ` or `ZMod p`), then:

* rewrite exponent facts with `orderOf`,
* use standard lemmas like “`pow_eq_one` iff order divides exponent”,
* use `simp` heavily (`simp [pow_mul]`, `simp [pow_add]`),
* assemble CRT steps via existing theorems (often not “tactic” but lemma application).

**Core moves in Lean:**

* Work in `ZMod n` / units `ZMod nˣ`.
* Use `simp` with group lemmas.
* Use `nlinarith` only after you’ve reduced to arithmetic constraints on exponents.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Order/finite-group cleanup: simp group laws, reduce pow facts to divisibility. -/
elab "nt_order" : tactic => do
  evalTactic (← `(tactic|
    first
      | (simp at *; try ring_nf)
      | (simp [pow_add, pow_mul] at *; try omega; try nlinarith)
      | aesop
  ))
```

---

### 8) **Divisor functions & divisor enumeration** — **6**

**What it looks like:** list divisors or use multiplicativity ((\tau,\sigma,\phi)-style identities), often paired with symmetry (d \leftrightarrow n/d).
**Examples**

* **IDX 130**: sum of reciprocals of divisors uses the pairing (d \mapsto 144/d).
* **IDX 481**: remainder condition (109 \equiv 4 \pmod x) → (x\mid 105), then enumerate divisors.
* **IDX 624 / 377**: use divisor-structure constraints translated into exponent bounds.

**Count (audit):** 6 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** push goals into `Nat.dvd` / `Nat.divisors` / `Nat.factors` statements, then:

* reduce with `simp` on divisibility,
* optionally do finite divisor enumeration with `decide` if the number is concrete.

**Core moves in Lean:**

* For concrete `n`, `native_decide` can solve divisor membership goals.
* Use lemma patterns: “if `x ∣ n` then `x` is in `Nat.divisors n`” and vice versa.
* For multiplicativity, use existing theorems about `Nat.totient`, `Nat.divisorsAntidiagonal`, etc.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Divisor reasoning: simp on `dvd`, try finite enumeration for concrete numerals. -/
elab "nt_divisors" : tactic => do
  evalTactic (← `(tactic|
    first
      | (simp at *; omega)
      | (simp at *; nlinarith)
      | native_decide
      | aesop
  ))
```

---

### 9) **GCD / coprimality arguments (Euclidean-logic moves)** — **5**

**What it looks like:** exploit (\gcd) constraints to force structure, or use “if (p\mid ab) and (\gcd(p,a)=1) then (p\mid b)” repeatedly.
**Examples**

* **IDX 26**: set (S\subset{1,\dots,108}) with gcd requirements → structure forced by shared prime factors.
* **IDX 390**: opposite vertices relatively prime but adjacent share factors → forces “two-prime-factor” style construction (ab,bc,cd,da).
* **IDX 65**: uses an odd prime divisor (p\mid(m+n)) to force a contradiction via congruences and coprimality.

**Count (audit):** 5 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** normalize coprimality facts into `Nat.Coprime` or `IsCoprime`, then repeatedly apply “coprime divides” lemmas.

**Core moves in Lean:**

* `simp` with coprimality lemmas:

  * `Nat.Coprime.mul_right`, `Nat.Coprime.mul_left`, etc.
* Use `have hx : a ∣ b := ...` and then `exact (Nat.Coprime.dvd_of_dvd_mul_left ...)`-style lemmas (names vary; idea is stable).
* Many steps are `aesop`-friendly if lemmas are in simp set.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- GCD/coprime driver: simp coprimality, push divisibility consequences. -/
elab "nt_gcd" : tactic => do
  evalTactic (← `(tactic|
    first
      | (simp at *; aesop)
      | (simp at *; omega)
      | (simp at *; nlinarith)
      | aesop
  ))
```

---

### 10) **Pigeonhole principle (often via residues / partial sums collisions)** — **4**

**What it looks like:** show two objects must share a residue / state; subtract to get divisibility.
**Examples**

* **IDX 182**: partial sums mod 20 must collide unless all elements share a residue class → forces structure then counts.
* **IDX 169**: across infinitely many primes (p), a bounded triple repeats → pigeonhole to pin down the actual rational roots.
* **IDX 663**: subset size forcing (a^2-b^2\equiv 0\pmod{2004}) (typical: residues / square-classes mod prime factors + pigeonhole).

**Count (audit):** 4 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** recognize the standard Lean shape:

* map a large finset into a smaller finite type (e.g. residues `ZMod n`),
* use a lemma like “if `card s > card t` then `f` not injective on `s`”,
* extract `x ≠ y` with `f x = f y`.

**Core moves in Lean:**

* Convert to `Finset` or `Fintype` statement.
* Apply a non-injectivity lemma (often `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`-ish patterns; the exact lemma you pick depends on your setup).
* After collision, reduce to congruence and finish with `nt_mod`.

**Starter macro sketch (scaffolding):**

```lean
import Mathlib

open Lean Elab Tactic

/-- Pigeonhole scaffolding: sets up classical finiteness and tries common collision lemmas. -/
elab "nt_pigeon" : tactic => do
  evalTactic (← `(tactic|
    classical
    -- This won't magically find the right lemma, but it sets the stage:
    first
      | aesop
      | (simp at *; aesop)
  ))
```

Pragmatically, you’ll often write one line manually (“apply noninjective_of_card_lt …”) and then `nt_mod` finishes.

---

### 11) **Bounding / inequalities** — **4**

**What it looks like:** squeeze sizes, restrict parameter ranges, show only small cases possible.
**Examples**

* **IDX 520**: (n\mid 2^n) ⇒ (n) power of 2, then uses a size bound (n<10^{100}\Rightarrow m\le 340) to limit cases.
* **IDX 728**: combines (a+b+c < 2p\sqrt p) with (abc=p(ab+ac+bc)) to restrict possibilities.
* **IDX 559**: “close divisors” count is controlled by where divisors can lie relative to (\sqrt n).

**Count (audit):** 4 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** normalize inequalities and let `linarith`/`nlinarith`/`omega` solve.

**Core moves in Lean:**

* If Nat inequalities: `zify` into Int, or use `nlinarith` on coerced forms.
* Use `positivity` to discharge side-goals about nonnegativity.
* `nlinarith` handles many polynomial inequalities; `omega` handles Presburger arithmetic.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Inequality solver driver for typical olympiad NT bounds. -/
elab "nt_bounds" : tactic => do
  evalTactic (← `(tactic|
    first
      | (simp at *; positivity)
      | (zify at *; linarith)
      | nlinarith
      | omega
      | aesop
  ))
```

---

### 12) **Invariants / monovariants** — **3**

**What it looks like:** track a quantity preserved (or strictly changes) under allowed operations.
**Examples**

* **IDX 364**: bucket/blackboard process maintains a relation between “stones in bucket” and “sum on board”, constraining outcomes.
* **IDX 754**: condition on (\Omega(\cdot)) (sum of prime exponents) acts like an invariant/monotone constraint on differences (f(a)-f(b)).
* **IDX 104**: Pell-type identity (x_n^2-2y_n^2=(-1)^n) used as a stable structural constraint in an approximation argument.

**Count (audit):** 3 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** invariants are usually proved by:

* `induction` / `cases` on steps,
* a lemma `invariant_preserved : step s t → I s = I t` (or `≤` for monovariant),
* then `simp` closes.

So the tactic is mainly a **workflow helper**: after you introduce the invariant, it pushes you toward induction and tries to discharge algebraic preservation.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Invariant workflow helper: try induction, then simp/algebra on step cases. -/
elab "nt_invariant" : tactic => do
  evalTactic (← `(tactic|
    first
      | (induction' _ <;> simp at * <;> try ring_nf <;> try omega <;> try nlinarith)
      | aesop
  ))
```

(You’ll typically replace the `_` with the “number of moves”/derivation structure manually.)

---

### 13) **Symmetry pairing / involution** — **2**

**What it looks like:** pair objects so exactly one of each pair contributes, or reduce counting by identifying complements.
**Examples**

* **IDX 455**: pair ((a,b)) with ((57-b,57-a)) so exactly one satisfies an inequality unless they are congruent-square pairs.
* **IDX 130**: divisor pairing (d \leftrightarrow n/d) as a symmetry to rewrite reciprocal sums.

**Count (audit):** 2 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** in Lean, pairing/involution arguments are usually:

* build an `Equiv` (bijection) or `Involutive` function,
* apply a counting lemma like `Finset.card_bij` / `Finset.card_equiv` / `Finset.card_congr`,
* then `simp` finishes the algebra.

So the tactic can:

* turn on `classical`,
* try `apply Finset.card_bij` / `apply Finset.card_congr` patterns,
* then run `simp`.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Symmetry/involution scaffolding: try to reduce to `card_bij`/`Equiv` counting lemmas. -/
elab "nt_involution" : tactic => do
  evalTactic (← `(tactic|
    classical
    first
      | aesop
      | (simp at *; aesop)
  ))
```

This is intentionally “scaffolding”: the key creative step is defining the involution/bijection function; the tactic helps clear the rest.

---

### 14) **Direct enumeration / brute force (including “test small primes” / “computer search”)** — **2**

**Examples**

* **IDX 611**: explicitly suggests testing small primes because growth is fast.
* **IDX 338**: “a computer search yields …”.

**Count (audit):** 2 / 60

#### How to turn this into a Lean tactic

**Tactic goal:** for **finite** or **bounded** goals, Lean can actually *compute*.

* If the goal is decidable and reduces to `True`, `native_decide` can close it.
* For bounded naturals, `decide` + rewriting can solve lots of “check all cases ≤ K”.

**Starter macro sketch:**

```lean
import Mathlib

open Lean Elab Tactic

/-- Brute-force driver for decidable/finite goals. -/
elab "nt_bruteforce" : tactic => do
  evalTactic (← `(tactic|
    first
      | native_decide
      | decide
      | (simp at *; native_decide)
  ))
```

---

## Common “blends” (strategies that co-occur a lot)

From the same 60-proof audit:

* **MOD + CASE**: **11** proofs (typical: reduce mod small primes, then split into parity/size cases).
* **MOD + FACT**: **9** proofs (typical: valuation arguments + congruence constraints).
* **MOD + GT (orders/FLT/CRT)**: **6** proofs (typical: order arguments + CRT assembly).
* **MOD + FACT + CASE**: **4** proofs (the “classic olympiad number theory cocktail”).

#### How to turn blends into Lean tactics

Blends are where tactics shine: make a “portfolio tactic” that tries several specialized drivers in sequence.

**Example “cocktail tactic”:**

```lean
import Mathlib

open Lean Elab Tactic

/-- A pragmatic number theory "cocktail": modular + factoring + bounds + casework. -/
elab "nt_cocktail" : tactic => do
  evalTactic (← `(tactic|
    first
      | nt_mod
      | nt_vp
      | nt_factor
      | nt_bounds
      | nt_cases
      | nt_divisors
      | nt_gcd
      | nt_bruteforce
      | aesop
  ))
```

---

## If you truly need “all 832 proofs” with exact counts

Doing *exact* frequencies over **all 832** while staying “manual-only” (no automation at all) isn’t realistically expressible in a single chat response. If you relax the “no scripts” rule **just for tallying** (still keeping **semantic/manual tagging**, not keyword matching), I can produce an exact full-file frequency table.

---

If you want, I can also package the tactic sketches above into a single `NTTactics.lean` file with:

* proper `syntax` declarations (so you can do `nt_mod 7` style),
* a few helper lemmas (`Nat.ModEq`/`Int.ModEq` ↔ `ZMod` conversions) to make `nt_mod` genuinely useful,
* and a recommended import list / namespace layout for mathlib.
