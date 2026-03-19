# Strategy Reuse: Training Strategies Applied to Test Problems

This document maps the **top 10 proof strategies** identified in the training split to the **57 test problems** from `ProofNet-V_Artin_DummitFoote_test.csv`. For each strategy, we list all test problems whose proof relies on that strategy, with a brief justification.

> **Note:** A single test problem may appear under multiple strategies, since many proofs combine techniques.

---

## Strategy 1: Direct Algebraic Computation / Chain of Equalities (Train count: 18)

The most broadly reusable strategy. Proofs that proceed by directly computing and simplifying algebraic expressions step by step.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_5_4_2` | Directly computes that $h^{-1}g^{-1}hg \in H$ iff $g^{-1}hg \in H$ by multiplying by $h$. |
| 2 | `Dummit-Foote\|exercise_1_1_5` | Computes $\bar{0} \cdot \bar{k} = \bar{0}$ to show $\bar{0}$ has no multiplicative inverse. |
| 3 | `Dummit-Foote\|exercise_9_4_2d` | Expands $(x+2)^p$ term by term, simplifies the polynomial, then reads off coefficients. |
| 4 | `Dummit-Foote\|exercise_1_1_18` | Direct chain: $xy=yx \Rightarrow y^{-1}xy=x \Rightarrow x^{-1}y^{-1}xy=1$ and back. |
| 5 | `Dummit-Foote\|exercise_7_2_2` | Expands $p(x)q(x)$ as $\sum(\sum a_i b_j)x^k = 0$ and reads off leading coefficients. |
| 6 | `Dummit-Foote\|exercise_4_4_2` | Computes $|ab| = |a| \cdot |b| = pq$ since $(p,q)=1$ and $ab=ba$. |
| 7 | `Artin\|exercise_2_8_6` | Directly shows $(g_1,g_2)(h_1,h_2) = (h_1,h_2)(g_1,g_2)$ iff $g_1h_1=h_1g_1$ and $g_2h_2=h_2g_2$. |
| 8 | `Dummit-Foote\|exercise_9_3_2` | Uses Gauss' Lemma, then computes $(rf_i)(r^{-1}g_j) = f_ig_j \in \mathbb{Z}$. |
| 9 | `Dummit-Foote\|exercise_1_6_17` | Computes $\varphi(ab) = (ab)^{-1} = b^{-1}a^{-1} = a^{-1}b^{-1} = \varphi(a)\varphi(b)$ in the ($\Rightarrow$) direction. |
| 10 | `Dummit-Foote\|exercise_7_1_11` | Factors $x^2 - 1 = (x-1)(x+1) = 0$, uses no zero divisors. |
| 11 | `Dummit-Foote\|exercise_1_1_20` | Computes $(x^{-1})^n = (x^n)^{-1} = 1$ to show $m \leq n$ and vice versa. |
| 12 | `Artin\|exercise_13_6_10` | Factors $x^{q-1} - 1 = (x-a_1)\cdots(x-a_{q-1})$, reads off constant term as $(-1)^{q-1}a_1\cdots a_{q-1} = -1$. |
| 13 | `Dummit-Foote\|exercise_7_1_15` | Computes $a+b = (a+b)^2 = a + ab + ba + b$, so $ab + ba = 0$, then $ab = -ba = ba$. |
| 14 | `Dummit-Foote\|exercise_7_4_27` | Since $-ab$ is nilpotent (nilpotent radical is an ideal), $1-ab$ is a unit. |
| 15 | `Artin\|exercise_10_4_7a` | Multiplies $i+j=1$ through by $k \in I \cap J$ to get $k = ik + kj \in IJ$. |
| 16 | `Dummit-Foote\|exercise_7_3_16` | Computes $xr = \varphi(y)\varphi(z) = \varphi(yz) = \varphi(zy) = \varphi(z)\varphi(y) = rx$. |
| 17 | `Dummit-Foote\|exercise_1_6_11` | Computes $\varphi((a_1,b_1)(a_2,b_2)) = (b_1b_2, a_1a_2) = (b_1,a_1)(b_2,a_2) = \varphi(a_1,b_1)\varphi(a_2,b_2)$. |
| 18 | `Artin\|exercise_2_3_2` | One-line: $a^{-1}(ab)a = ba$. |
| 19 | `Artin\|exercise_6_8_1` | Computes $(bab^2)^{-1}(bab^3) = b$, then $b^{-1}(bab^2)b^{-2} = a$. |
| 20 | `Dummit-Foote\|exercise_1_6_23` | Computes $\sigma(z) = \sigma(x^{-1}\sigma(x)) = \sigma(x)^{-1}x = z^{-1}$, showing $\sigma$ is inversion. |
| 21 | `Dummit-Foote\|exercise_2_1_13` | Computes $q \cdot (p/q) = p \in H$, then $p \cdot (q/p) = q \in H$, then uses Bezout to get $1 \in H$. |
| 22 | `Dummit-Foote\|exercise_9_4_2c` | Expands $p(x-1)$ term by term to obtain $q(x) = x^4 + 2x^3 - 8x^2 + 8x - 2$. |
| 23 | `Dummit-Foote\|exercise_7_3_37` | Computes $(I_1/J)(I_2/J) = I_1I_2/J$ via double inclusion on sums of products of cosets. |

**Applicable to 23 / 57 test problems.**

---

## Strategy 2: Proof by Contradiction (Train count: 8)

Assume the negation (or an unwanted case) and derive an impossibility.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Artin\|exercise_3_2_7` | Assumes $f(a)=f(b)$ with $a \neq b$; derives $0 \cdot f(u^{-1}) = 1$, a contradiction. |
| 2 | `Dummit-Foote\|exercise_1_1_5` | Assumes $\mathbb{Z}/n\mathbb{Z}$ is a group under multiplication; $\bar{0}$ cannot have an inverse. |
| 3 | `Dummit-Foote\|exercise_4_5_22` | Assumes both $n_{11} = 12$ and $n_3 > 1$; element count exceeds $|G| = 132$. |
| 4 | `Artin\|exercise_6_4_12` | Assumes $n_2 = 7$; embedding $G \hookrightarrow S_7$ fails since $224 \nmid 7!$. |
| 5 | `Dummit-Foote\|exercise_2_4_16c` | Assumes $k$ is not prime; constructs $K = \langle x^p \rangle > H$ contradicting maximality. |
| 6 | `Dummit-Foote\|exercise_3_4_1` | Assumes $G$ is infinite or has composite order; finds a nontrivial normal subgroup. |
| 7 | `Dummit-Foote\|exercise_4_5_16` | Assumes all $n_r, n_q, n_p > 1$; element count exceeds $|G| = pqr$. |
| 8 | `Dummit-Foote\|exercise_7_2_2` | Chooses $q(x)$ of minimal degree with $p(x)q(x) = 0$; shows $a_n q(x)$ has smaller degree. |
| 9 | `Dummit-Foote\|exercise_8_2_4` | Uses Zorn's lemma to find minimal element w.r.t. divisibility; assumes two minimal elements, derives they are associates. |
| 10 | `Dummit-Foote\|exercise_2_1_5` | Assumes $H$ exists with $|H|=n-1$; product $xy$ leads to contradiction in both cases. |
| 11 | `Dummit-Foote\|exercise_9_1_6` | Assumes $(x,y) = (p)$; degree analysis forces $\deg(p) = 0$ but $p \in (x,y)$ has no constant term. |
| 12 | `Dummit-Foote\|exercise_4_5_13` | Assumes both $n_7 = 8$ and $n_2 = 7$; element count exceeds 56. |
| 13 | `Dummit-Foote\|exercise_1_1_20` | Assumes $|x|$ infinite but $|x^{-1}| = n$; derives $x^n = 1$, contradicting infinite order. |
| 14 | `Dummit-Foote\|exercise_8_3_5a` | Assumes $2 = ab$ with neither a unit; $N(a) = 2$ gives $a_1^2 = 2$ for integer $a_1$, contradiction. |
| 15 | `Artin\|exercise_10_7_10` | Assumes ideal $I \supsetneq M$; $I$ contains a unit, so $I = R$, proving maximality. |
| 16 | `Dummit-Foote\|exercise_4_5_19` | Assumes $n_{19} > 1$; but $1 + 19k \mid 3^2 \cdot 17$ forces $k = 0$. (The contradiction is that no valid $k > 0$ exists.) |
| 17 | `Dummit-Foote\|exercise_9_4_2c` | Factorization of $p(x)$ would give factorization of $p(x-1)$, contradicting Eisenstein irreducibility. |

**Applicable to 17 / 57 test problems.**

---

## Strategy 3: Sylow Theorem Counting Arguments (Train count: 7)

Uses $n_p \equiv 1 \pmod{p}$ and $n_p \mid [G:P]$ to constrain the number of Sylow subgroups.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_4_5_22` | $|G|=132=2^2 \cdot 3 \cdot 11$. Constrains $n_{11}$ and $n_3$ using Sylow counting. |
| 2 | `Dummit-Foote\|exercise_4_5_19` | $|G|=6545$. Sylow counting on largest prime factor to find unique (hence normal) Sylow subgroup. |
| 3 | `Artin\|exercise_6_4_12` | $|G|=224=2^5 \cdot 7$. Constrains $n_2$ to be 1 or 7. |
| 4 | `Artin\|exercise_6_4_3` | $|G|=p^2q$. Constrains $n_q \in \{1, p, p^2\}$, then uses $q \mid p^2 - 1$. |
| 5 | `Dummit-Foote\|exercise_4_5_16` | $|G|=pqr$. Systematically constrains $n_r, n_q, n_p$. |
| 6 | `Dummit-Foote\|exercise_4_5_13` | $|G|=56=2^3 \cdot 7$. Constrains $n_7 \in \{1, 8\}$ and $n_2 \in \{1, 7\}$. |
| 7 | `Artin\|exercise_6_4_2` | $|G|=pq$. Constrains $n_p \mid q$, so $n_p = 1$ or $q$; element count finishes. |
| 8 | `Dummit-Foote\|exercise_4_5_21` | $|G|=2907=3^2 \cdot 17 \cdot 19$. $n_{19} = 1+19k \mid 3^2 \cdot 17$ forces $k = 0$. |
| 9 | `Dummit-Foote\|exercise_4_5_15` | $|G|=351=3^2 \cdot 13$. $n_{13} = 1+13k \mid 9$ forces $k = 0$. |
| 10 | `Dummit-Foote\|exercise_4_5_18` | $|G|=200=5^2 \cdot 8$. $n_5 = 1+5k \mid 8$ forces $k = 0$. |

**Applicable to 10 / 57 test problems.**

---

## Strategy 4: Conjugation and Normality Arguments (Train count: 6)

Shows $gHg^{-1} \subseteq H$ for all $g$ to establish normality, or uses conjugation to show commutativity/centrality.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_5_4_2` | Normality is equivalent to $g^{-1}hg \in H$; the proof rewrites this via commutators. |
| 2 | `Dummit-Foote\|exercise_3_4_5b` | Shows $gxg^{-1} \in N_i$ by conjugation arguments using normality of $N$ and $G_i \unlhd G_{i+1}$. |
| 3 | `Dummit-Foote\|exercise_4_4_6a` | Characteristic ⟹ invariant under all automorphisms ⟹ invariant under inner automorphisms ⟹ $gHg^{-1} \subseteq H$. |
| 4 | `Dummit-Foote\|exercise_4_4_8a` | $\phi_g|_K$ is an automorphism of $K$ (since $K \unlhd G$); characteristic $H$ is fixed, so $\phi_g(H) \subseteq H$. |
| 5 | `Artin\|exercise_2_3_2` | Shows $ab$ and $ba$ are conjugate: $a^{-1}(ab)a = ba$. |

**Applicable to 5 / 57 test problems.**

---

## Strategy 5: Order, Index, and Divisibility Arguments / Lagrange's Theorem (Train count: 6)

Uses $|H| \mid |G|$, index factoring $[G:H] = [G:K][K:H]$, or element order divides group order.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_3_4_4` | Uses Cauchy's Theorem (existence of element of prime order) and Lagrange for $|G/N| = |G|/|N|$. |
| 2 | `Dummit-Foote\|exercise_3_3_3` | $[G:N] = p$ prime; Second Isomorphism Theorem gives $[K : K \cap N] = p$. |
| 3 | `Artin\|exercise_6_4_12` | $|G| = 224$ does not divide $7! = 5040$, blocking the embedding $G \hookrightarrow S_7$. |
| 4 | `Dummit-Foote\|exercise_2_4_16c` | Uses $(p, n)$ divides $n$, and Proposition 6 linking cyclic subgroups to divisors of $n$. |
| 5 | `Artin\|exercise_6_4_3` | $q \mid p^2 - 1 = (p-1)(p+1)$ constrains $p$ and $q$. |
| 6 | `Dummit-Foote\|exercise_3_4_1` | Cauchy gives element of order $p$ when $p \mid |G|$; $\langle x \rangle$ is a proper normal subgroup. |
| 7 | `Dummit-Foote\|exercise_4_4_2` | $|ab| = |a| \cdot |b|$ when orders are coprime and elements commute; $|ab| = pq = |G|$. |
| 8 | `Dummit-Foote\|exercise_3_2_8` | $|H \cap K|$ divides both $|H|$ and $|K|$; since $\gcd(|H|,|K|) = 1$, $|H \cap K| = 1$. |
| 9 | `Dummit-Foote\|exercise_4_2_8` | $[G:K] = |G/K|$ divides $|S_{G/H}| = n!$ via First Isomorphism Theorem. |
| 10 | `Dummit-Foote\|exercise_8_3_5a` | Norm is multiplicative: $N(a)N(b) = N(2) = 4$; constrains $N(a) \in \{1, 2, 4\}$. |

**Applicable to 10 / 57 test problems.**

---

## Strategy 6: Quotient Groups and Isomorphism Theorems (Train count: 5)

Uses the First, Second, or Third Isomorphism Theorem, or analyzes quotient structures to transfer information.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_3_3_3` | $G/N \cong \mathbb{Z}/p$; Second Isomorphism Theorem gives $[K : K \cap N] = [KN : N] = p$. |
| 2 | `Dummit-Foote\|exercise_3_4_5b` | Second Isomorphism Theorem: $N_{i+1}/N_i \cong$ a quotient of $G_{i+1}/G_i$, hence abelian. |
| 3 | `Dummit-Foote\|exercise_4_2_8` | First Isomorphism Theorem: $G/K \hookrightarrow S_{G/H}$, so $[G:K] \leq n!$. |
| 4 | `Dummit-Foote\|exercise_3_4_4` | Inductive step works in $G/N$ which has smaller order; lifts subgroup back to $G$. |
| 5 | `Dummit-Foote\|exercise_7_3_37` | Shows $(I_1/J)(I_2/J) = I_1I_2/J$ as quotient ideal computation, then applies inductively. |

**Applicable to 5 / 57 test problems.**

---

## Strategy 7: Element Counting / Pigeonhole Principle (Train count: 5)

Counts elements of specific orders or in substructures to derive constraints or contradictions.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_4_5_22` | 12 Sylow 11-subgroups give $12 \times 10 = 120$ elements of order 11; combined with other Sylow counts exceeds 132. |
| 2 | `Dummit-Foote\|exercise_4_5_19` | Element counting across Sylow subgroups for $|G| = 6545$. |
| 3 | `Artin\|exercise_6_4_3` | $p^2$ Sylow $q$-subgroups account for $p^2(q-1)$ elements of order $q$. |
| 4 | `Dummit-Foote\|exercise_4_5_16` | Counts elements of orders $p, q, r$ from the respective Sylow subgroups; total exceeds $pqr$. |
| 5 | `Dummit-Foote\|exercise_4_5_13` | 8 Sylow 7-subgroups give $48$ elements of order 7; combined with 7 Sylow 2-subgroups overshoots 56. |
| 6 | `Artin\|exercise_6_4_2` | $n_p = q$ Sylow $p$-subgroups account for $q(p-1)$ elements; only room for one Sylow $q$-subgroup. |
| 7 | `Dummit-Foote\|exercise_1_6_23` | $f: G \to G$ is injective on a finite set, hence surjective (Pigeonhole). |
| 8 | `Dummit-Foote\|exercise_11_1_13` | Cardinality argument: $|\mathbb{R}^n| = |\mathbb{R}|$ as sets, which gives the vector space isomorphism dimension. |
| 9 | `Dummit-Foote\|exercise_1_6_4` | $\mathbb{R}^\times$ has exactly 2 elements of finite order; $\mathbb{C}^\times$ has infinitely many (e.g., $i$ has order 4). |

**Applicable to 9 / 57 test problems.**

---

## Strategy 8: Double Inclusion / Biconditional Proof (Train count: 4)

Proves $A = B$ by showing $A \subseteq B$ and $B \subseteq A$, or proves $P \iff Q$ by proving both directions.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_5_4_2` | $H \unlhd G \iff [G,H] \leq H$: proves ($\Rightarrow$) and ($\Leftarrow$) separately. |
| 2 | `Dummit-Foote\|exercise_2_4_16c` | $H$ maximal $\iff$ $H = \langle x^p \rangle$ for prime $p \mid n$: proves both directions. |
| 3 | `Dummit-Foote\|exercise_1_1_18` | Chain of three equivalences, each shown in both directions. |
| 4 | `Dummit-Foote\|exercise_1_6_17` | $g \mapsto g^{-1}$ is homomorphism $\iff$ $G$ abelian: ($\Rightarrow$) and ($\Leftarrow$) proved. |
| 5 | `Artin\|exercise_10_4_7a` | $IJ = I \cap J$: shows $IJ \subseteq I \cap J$ (known) and $I \cap J \subseteq IJ$ (key step). |
| 6 | `Artin\|exercise_6_8_1` | $\langle a,b \rangle = \langle bab^2, bab^3 \rangle$: shows $\supseteq$ (obvious) and $\subseteq$ (recover $a, b$). |
| 7 | `Dummit-Foote\|exercise_7_3_37` | Lemma proves $(I_1/J)(I_2/J) = I_1I_2/J$ by showing $\subseteq$ and $\supseteq$. |

**Applicable to 7 / 57 test problems.**

---

## Strategy 9: Counterexample / Explicit Construction (Train count: 3)

Constructs a specific object (map, element, example) or performs brute-force verification over a finite set.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_1_3_8` | Constructs explicit injection $f: \mathbb{N} \to S_\mathbb{N}$ via $f(n) = (1\ n)$ to show $S_\Omega$ is infinite. |
| 2 | `Dummit-Foote\|exercise_9_1_10` | Explicitly constructs uncountably many distinct prime ideals via choice functions on pairs $\{x_{2k+1}, x_{2k+2}\}$. |
| 3 | `Dummit-Foote\|exercise_1_6_4` | Exhibits $i \in \mathbb{C}^\times$ with order 4; shows no element of $\mathbb{R}^\times$ has order 4. |
| 4 | `Artin\|exercise_11_4_6a` | Checks both elements of $\mathbb{F}_2$: $0^2+0+1 = 1 \neq 0$ and $1^2+1+1 = 1 \neq 0$. |
| 5 | `Artin\|exercise_11_4_6b` | Checks all 7 elements of $\mathbb{F}_7$: none satisfies $x^2 + 1 = 0$. |
| 6 | `Dummit-Foote\|exercise_1_6_11` | Constructs explicit isomorphism $\varphi(a,b) = (b,a)$ and verifies it is a homomorphism. |

**Applicable to 6 / 57 test problems.**

---

## Strategy 10: Case Analysis (Train count: 3)

Breaks the proof into exhaustive cases and handles each one separately.

| # | Test Problem ID | Justification |
|---|-----------------|---------------|
| 1 | `Dummit-Foote\|exercise_2_1_13` | Case 1: $H$ has no nonzero element ($H = 0$). Case 2: $H$ has a nonzero element (then $H = \mathbb{Q}$). |
| 2 | `Dummit-Foote\|exercise_3_4_1` | Cases: $G$ infinite vs. finite; if finite, $|G|$ prime vs. composite. |
| 3 | `Dummit-Foote\|exercise_1_1_20` | Case 1: $|x|$ infinite. Case 2: $|x|$ and $|x^{-1}|$ both finite. |
| 4 | `Dummit-Foote\|exercise_8_3_5a` | For each of 2, $\sqrt{-n}$, $1+\sqrt{-n}$: cases on $N(a) \in \{1, 2, 4\}$ (or appropriate divisors). |
| 5 | `Dummit-Foote\|exercise_3_3_3` | Either $K \leq H$ (done), or there exists $k \in K \setminus H$ (then $G = HK$). |

**Applicable to 5 / 57 test problems.**

---

## Summary: Coverage of Test Problems by Strategy

| Strategy | Rank | Train Count | Test Problems Using It | Test Count |
|----------|------|-------------|----------------------|------------|
| Direct Algebraic Computation | 1 | 18 | 23 test problems | 23 |
| Proof by Contradiction | 2 | 8 | 17 test problems | 17 |
| Sylow Counting | 3 | 7 | 10 test problems | 10 |
| Order/Index/Divisibility | 5 | 6 | 10 test problems | 10 |
| Element Counting | 7 | 5 | 9 test problems | 9 |
| Double Inclusion/Biconditional | 8 | 4 | 7 test problems | 7 |
| Counterexample/Construction | 9 | 3 | 6 test problems | 6 |
| Conjugation and Normality | 4 | 6 | 5 test problems | 5 |
| Quotient/Isomorphism Theorems | 6 | 5 | 5 test problems | 5 |
| Case Analysis | 10 | 3 | 5 test problems | 5 |

### Test Problems NOT Covered by Any Top-10 Strategy

The following test problems rely **primarily** on strategies outside the top 10 (e.g., Eisenstein criterion, induction, group actions, or domain-specific arguments):

| Test Problem ID | Primary Strategy Used |
|-----------------|----------------------|
| `Dummit-Foote\|exercise_9_4_2a` | Eisenstein criterion (rank 14 in training) |
| `Artin\|exercise_11_4_8` | Eisenstein criterion (rank 14 in training) |
| `Artin\|exercise_11_4_1b` | Eisenstein criterion (rank 14 in training) |

> **Note:** Even these 3 problems have *some* overlap with top-10 strategies (e.g., direct computation for coefficient checking), but their **core** technique is Eisenstein, which ranked #14. All other 54 test problems are covered by at least one top-10 strategy.

### Overall Coverage

- **54 out of 57** test problems (94.7%) can be proved using at least one of the top-10 training strategies.
- **3 out of 57** test problems (5.3%) rely primarily on Eisenstein's criterion, which is outside the top 10.
- The most transferable strategy is **Direct Algebraic Computation**, applicable to 23/57 (40.4%) test problems.
- **Sylow Counting** and **Order/Index/Divisibility** are each applicable to 10/57 (17.5%) test problems, reflecting the heavy representation of finite group theory in both splits.
