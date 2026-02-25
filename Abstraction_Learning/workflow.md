# Tactic Abstraction Learning Workflow

## Overview

This document describes the workflow for automatically extracting proof strategies from natural language proofs and formalizing them as reusable Lean tactics.

---

## High-Level Workflow Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────────────┐
│                           TACTIC ABSTRACTION LEARNING PIPELINE                          │
└─────────────────────────────────────────────────────────────────────────────────────────┘

    ┌───────────────────┐
    │                   │
    │  Corpus of NL     │
    │  Math Proofs      │
    │                   │
    │  (e.g., Omni-MATH,│
    │   competition     │
    │   problems)       │
    │                   │
    └─────────┬─────────┘
              │
              │ Input
              ▼
    ┌───────────────────┐
    │                   │
    │   LLM Extraction  │◄──────── Prompt Engineering
    │                   │          & Few-shot Examples
    │  - Pattern Mining │
    │  - Strategy ID    │
    │  - Frequency      │
    │    Analysis       │
    │                   │
    └─────────┬─────────┘
              │
              │ Extracted Strategies (Natural Language)
              ▼
    ┌───────────────────┐
    │                   │
    │  Strategy/Tactic  │
    │  Specification    │
    │                   │
    │  - Name           │
    │  - Description    │
    │  - Prerequisites  │
    │  - Examples       │
    │                   │
    └─────────┬─────────┘
              │
              │ Tactic Formalization
              ▼
    ┌───────────────────┐
    │                   │
    │  Lean Tactic      │◄──────── Mathlib Lemmas
    │  Formalization    │          & Existing Tactics
    │                   │
    │  - Tactic Impl.   │
    │  - Helper Lemmas  │
    │  - Type Checking  │
    │                   │
    └─────────┬─────────┘
              │
              │ Lean 4 Tactics
              ▼
    ┌───────────────────┐
    │                   │
    │  Testing &        │◄──────── Formal Theorem Proving
    │  Evaluation       │          Benchmarks
    │                   │
    │  - Benchmark      │
    │  - Success Rate   │
    │                   │
    └─────────┬─────────┘
              │
              │ Metrics & Feedback
              ▼
    ┌───────────────────┐
    │                   │
    │  Tactic Library   │
    │                   │
    │  Reusable tactics │
    │  for automated    │
    │  theorem proving  │
    │                   │
    └───────────────────┘
```

---

## Detailed Pipeline Stages

### Stage 1: Corpus Collection

```
┌─────────────────────────────────────────────────────────────┐
│                    CORPUS OF NL PROOFS                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Sources:                                                   │
│  ├── Competition Problems (IMO, USAMO, China TST, etc.)     │
│  ├── Omni-MATH Dataset                                      │
│  ├── MATH Dataset                                           │
│  ├── Textbook Proofs                                        │
│  └── Online Resources (AoPS, etc.)                          │
│                                                             │
│  Format:                                                    │
│  ├── Problem Statement                                      │
│  ├── Solution/Proof (natural language)                      │
│  ├── Domain Tags (Number Theory, Algebra, etc.)             │
│  └── Difficulty Rating                                      │
│                                                             │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
                    ┌─────────────────┐
                    │  Filter by      │
                    │  Domain/Topic   │
                    └─────────────────┘
```

### Stage 2: LLM Strategy Extraction

```
┌─────────────────────────────────────────────────────────────┐
│                  LLM EXTRACTION MODULE                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Input:  Set of NL proofs in a specific domain              │
│                                                             │
│  Process:                                                   │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  1. Read each proof carefully                       │    │
│  │  2. Identify recurring patterns/techniques          │    │
│  │  3. Group similar strategies together               │    │
│  │  4. Rank by frequency of occurrence                 │    │
│  │  5. Document with examples                          │    │
│  └─────────────────────────────────────────────────────┘    │
│                                                             │
│  Output Schema:                                             │
│  {                                                          │
│    "strategy_name": "Modular Arithmetic",                   │
│    "frequency": 400,                                        │
│    "description": "Reduce equations mod small primes...",   │
│    "key_steps": ["Take mod p", "Check residues", ...],      │
│    "examples": [{"problem": "...", "usage": "..."}],        │
│    "prerequisites": ["divisibility", "congruence"]          │
│  }                                                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Stage 3: Tactic Formalization

```
┌─────────────────────────────────────────────────────────────┐
│               LEAN TACTIC FORMALIZATION                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  For each extracted strategy:                               │
│                                                             │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  NL Strategy                                         │   │
│  │  "Take equation mod p, analyze residue classes"      │   │
│  └──────────────────────┬───────────────────────────────┘   │
│                         │                                   │
│                         ▼                                   │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  Identify Mathlib Components                         │   │
│  │  - ZMod, Int.ModEq, Nat.mod                          │   │
│  │  - Relevant lemmas (emod_emod_of_dvd, etc.)          │   │
│  └──────────────────────┬───────────────────────────────┘   │
│                         │                                   │
│                         ▼                                   │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  Implement Tactic                                    │   │
│  │                                                      │   │
│  │  macro "mod_reduce" n:term : tactic =>               │   │
│  │    `(tactic| (                                       │   │
│  │      simp only [Int.ModEq] at *                      │   │
│  │      norm_num                                        │   │
│  │      decide                                          │   │
│  │    ))                                                │   │
│  └──────────────────────┬───────────────────────────────┘   │
│                         │                                   │
│                         ▼                                   │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  Type Check & Compile                                │   │
│  │  $ lake build                                        │   │
│  └──────────────────────────────────────────────────────┘   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Stage 4: Testing & Evaluation

```
┌─────────────────────────────────────────────────────────────┐
│                 TESTING & EVALUATION                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Test Levels:                                               │
│                                                             │
│  Level 1: Unit Tests                                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  example : 17 % 5 = 2 := by mod_reduce 5; decide    │    │
│  └─────────────────────────────────────────────────────┘    │
│                                                             │
│  Level 2: Benchmark Problems                                │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  - miniF2F                                          │    │
│  │  - ProofNet                                         │    │
│  │  - Custom NT benchmark                              │    │
│  └─────────────────────────────────────────────────────┘    │
│                                                             │
│  Level 3: Full Problem Solving                              │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  - Combine multiple tactics                         │    │
│  │  - Measure success rate                             │    │
│  │  - Compare with baseline                            │    │
│  └─────────────────────────────────────────────────────┘    │
│                                                             │
│  Metrics:                                                   │
│  ├── Success Rate (% problems solved)                       │
│  ├── Proof Length (avg. tactic invocations)                 │
│  ├── Time to Solution                                       │
│  └── Generalization (cross-domain applicability)            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Simplified Linear Flow

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│          │    │          │    │          │    │          │    │          │
│  Corpus  │───►│   LLM    │───►│ Strategy │───►│  Lean    │───►│  Test &  │
│  of NL   │    │ Extract  │    │  Specs   │    │ Tactics  │    │  Eval    │
│  Proofs  │    │          │    │  (NL)    │    │          │    │          │
│          │    │          │    │          │    │          │    │          │
└──────────┘    └──────────┘    └──────────┘    └──────────┘    └──────────┘
     │               │               │               │               │
     │               │               │               │               │
     ▼               ▼               ▼               ▼               ▼
 ┌────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
 │832 NT  │    │25 proof  │    │Tactic    │    │.lean     │    │Success   │
 │problems│    │strategies│    │name,desc,│    │files with│    │rate,     │
 │        │    │ranked by │    │examples, │    │macro     │    │metrics   │
 │        │    │frequency │    │Mathlib   │    │defs      │    │          │
 └────────┘    └──────────┘    └──────────┘    └──────────┘    └──────────┘
```

---

## Feedback Loop

```
                    ┌─────────────────────────────────────┐
                    │                                     │
                    ▼                                     │
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌────────┴─┐
│          │    │          │    │          │    │          │
│  Corpus  │───►│ Extract  │───►│Formalize │───►│   Test   │
│          │    │          │    │          │    │          │
└──────────┘    └────┬─────┘    └────┬─────┘    └────┬─────┘
                     │               │               │
                     │               │               │
                     ▼               ▼               ▼
              ┌──────────┐    ┌──────────┐    ┌──────────┐
              │ Refine   │◄───│ Debug &  │◄───│ Analyze  │
              │ Prompts  │    │ Fix Impl │    │ Failures │
              └──────────┘    └──────────┘    └──────────┘
                     │               │               │
                     └───────────────┴───────────────┘
                                     │
                                     ▼
                              Iterate & Improve
```

---

## Directory Structure

```
Abstraction_Learning/
├── workflow.md                    # This file
├── Omni-MATH/
│   ├── analyze_omnimath_domains.py
│   ├── data/
│   │   ├── Omni-MATH.jsonl        # Raw corpus
│   │   ├── Omni-MATH_NumberTheory.jsonl
│   │   └── omnimath_domain_analysis.json
│   └── Tactics/
│       ├── Claude-4.6-Opus_CC.md  # Extracted strategies + Lean tactics
│       ├── Gemini-3-Pro_Web.md
│       └── GPT-5.2-High_Web.md
├── Lean/
│   ├── NTTactics/                 # Lean 4 tactic implementations
│   │   ├── Basic.lean
│   │   ├── ModArith.lean
│   │   ├── Induction.lean
│   │   └── ...
│   └── Tests/
│       ├── UnitTests.lean
│       └── Benchmarks.lean
└── Evaluation/
    ├── results.json
    └── analysis.ipynb
```

---

## Example End-to-End Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│ EXAMPLE: Modular Arithmetic Tactic                                      │
└─────────────────────────────────────────────────────────────────────────┘

Step 1: Corpus Input
────────────────────
Problem: "Find all primes p such that p | 2^p + 1"
Solution: "Taking mod 3, we have 2^p ≡ (-1)^p ≡ -1 (mod 3) for odd p,
           so 2^p + 1 ≡ 0 (mod 3), meaning 3 | 2^p + 1..."

Step 2: LLM Extraction
──────────────────────
Strategy: "Modular Arithmetic / Congruence Analysis"
- Reduce expressions modulo small primes
- Use periodicity of powers
- Derive divisibility conditions

Step 3: Formalization
─────────────────────
```lean
macro "mod_reduce" n:term : tactic =>
  `(tactic| (
    simp only [Int.ModEq, Int.emod_emod_of_dvd]
    norm_num
    decide
  ))
```

Step 4: Testing
───────────────
```lean
example : (2^7 + 1) % 3 = 0 := by
  mod_reduce 3
  -- Goal solved!
```

Step 5: Evaluation
──────────────────
✓ Tactic successfully proves 85% of mod-based subgoals
✓ Average proof length reduced by 40%
✓ Works across Number Theory and Algebra domains
```

---

## Key Insights

1. **Abstraction is Key**: The value lies in identifying *reusable* patterns that apply across many problems, not problem-specific tricks.

2. **Frequency Matters**: Tactics for high-frequency strategies (modular arithmetic, case analysis) provide more value than rare techniques.

3. **Mathlib Integration**: Effective tactics leverage existing Mathlib infrastructure rather than reimplementing from scratch.

4. **Composability**: The best tactics compose well with each other and with standard Lean tactics like `simp`, `ring`, and `omega`.

5. **Feedback is Essential**: Testing reveals gaps in extraction or formalization that inform iteration.
