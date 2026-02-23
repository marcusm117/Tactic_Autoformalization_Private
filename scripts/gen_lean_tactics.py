#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Case:
    raw: str


@dataclass(frozen=True)
class TacticBlock:
    name: str
    used: int
    description: str
    cases: list[Case]


HEADER_RE = re.compile(r"^-\s+(?P<name>.+?)\s+\(used in\s+(?P<used>\d+)\s+proofs\)\s*$")
DESC_RE = re.compile(r"^\s{2}(?P<desc>\S.*)$")
CASE_RE = re.compile(r"^\s{2}-\s+(?P<raw>\S.*)$")


def parse_report(text: str) -> list[TacticBlock]:
    """
    Parse any tactic report that follows the (very lightweight) structure:

    - <tactic name> (used in N proofs)
      <one-line description>
      Cases:
      - <case line>
      - <case line>
    """
    lines = [ln.rstrip("\n") for ln in text.splitlines()]
    blocks: list[TacticBlock] = []

    i = 0
    while i < len(lines):
        m = HEADER_RE.match(lines[i])
        if not m:
            i += 1
            continue

        name = m.group("name").strip()
        used = int(m.group("used"))
        i += 1

        desc = ""
        if i < len(lines):
            dm = DESC_RE.match(lines[i])
            if dm:
                desc = dm.group("desc").strip()
                i += 1

        if i < len(lines) and lines[i].strip() == "Cases:":
            i += 1

        cases: list[Case] = []
        while i < len(lines):
            if HEADER_RE.match(lines[i]):
                break
            cm = CASE_RE.match(lines[i])
            if cm:
                cases.append(Case(raw=cm.group("raw").strip()))
            i += 1

        blocks.append(TacticBlock(name=name, used=used, description=desc, cases=cases))

    return blocks


def _lean_ident(s: str) -> str:
    s = s.lower()
    s = s.replace("–", "-").replace("—", "-")
    s = re.sub(r"[^a-z0-9]+", "_", s)
    s = re.sub(r"_+", "_", s).strip("_")
    if not s:
        return "tf_tactic"
    if s[0].isdigit():
        s = f"tf_{s}"
    return s


def _docstring(block: TacticBlock, ident: str) -> str:
    lines: list[str] = []
    lines.append("/--")
    if block.description:
        lines.append(block.description.rstrip())
        lines.append("")
    lines.append(f"Generated from tactic category: `{block.name}` (used in {block.used} proofs).")
    lines.append(f"Lean tactic name: `{ident}`.")
    if block.cases:
        lines.append("")
        lines.append("Cases in the textbook:")
        for c in block.cases:
            lines.append(f"- {c.raw}")
    lines.append("-/")
    return "\n".join(lines)


def generate_stub_lean(blocks: list[TacticBlock], input_rel: str) -> str:
    """
    Offline fallback: generates compiling tactic macros that do *nothing* (just `skip`).
    This keeps the project buildable without any LLM access.
    """
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    out: list[str] = []
    out.append("import Mathlib")
    out.append("")
    out.append("/-!")
    out.append("THIS FILE IS GENERATED (offline stub mode).")
    out.append("")
    out.append(f"Generated at: {ts}")
    out.append(f"Input: {input_rel}")
    out.append("")
    out.append("To generate real tactic bodies, run this script with `OPENAI_API_KEY` set.")
    out.append("-/")
    out.append("")
    out.append("namespace TacticFormalization")
    out.append("")
    for b in blocks:
        ident = _lean_ident(b.name)
        out.append(_docstring(b, ident))
        out.append(f'syntax (name := {ident}) "{ident}" : tactic')
        out.append("")
        out.append("macro_rules")
        out.append(f"  | `(tactic| {ident}) => `(tactic| skip)")
        out.append("")
    out.append("end TacticFormalization")
    out.append("")
    return "\n".join(out)


def _openai_chat_completions(api_key: str, payload: dict) -> dict:
    req = urllib.request.Request(
        "https://api.openai.com/v1/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=120) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="ignore")
        raise RuntimeError(f"OpenAI API HTTPError {e.code}: {body}") from e
    except urllib.error.URLError as e:
        raise RuntimeError(f"OpenAI API URLError: {e}") from e


LLM_SYSTEM_PROMPT = """You are a Lean 4 + Mathlib expert.

Task: given a list of natural-language 'proof tactic categories' and their occurrences, generate a Lean 4 file that defines tactic macros implementing those categories.

Hard constraints:
- Output MUST be a complete Lean file (no markdown), starting with `import Mathlib` as the very first command.
- Define all generated tactics inside `namespace TacticFormalization`.
- For each category, define a `syntax (name := ...) "<name>" : tactic` and `macro_rules` implementation.
- DO NOT use heavy automation tactics: `aesop`, `simp`, `dsimp`, `simp_all`, `linarith`, `nlinarith`, `ring`, `omega`, `grind`, `tauto`, `finish`, `exact?`, `admit`, `sorry`.
- Do not include those forbidden tokens anywhere in the output (including comments/docstrings).
- Prefer factoring out *explicit* mathematical steps (e.g. rewriting with named lemmas, applying cancellation lemmas, converting equalities to membership, etc.).
- It is OK for a generated tactic to leave remaining goals to the user; but it should reliably perform the 'boilerplate' transformation characteristic of the category.

Style:
- Keep tactic bodies small and predictable (mostly `refine`, `apply`, `rw`, `constructor`, `cases`, `rcases`, `have`, `show`, `change`).
- Include a short docstring for each tactic that repeats the category name and its case list as comments (so users can trace back).
"""

FORBIDDEN_LEAN_TOKENS = [
    "aesop",
    "grind",
    "simp",
    "dsimp",
    "simp_all",
    "linarith",
    "nlinarith",
    "ring",
    "omega",
    "tauto",
    "finish",
    "exact?",
    "admit",
    "sorry",
]


def _contains_forbidden_token(lean_source: str) -> list[str]:
    """
    Check for forbidden tactic tokens without substring false-positives like:
    - "simp" in "simple"
    - "ring" in "string"
    """
    bad: list[str] = []
    for tok in FORBIDDEN_LEAN_TOKENS:
        if tok.endswith("?"):
            # `exact?` etc: treat `?` as a literal character, require non-word boundaries.
            pat = re.compile(rf"(^|[^\w]){re.escape(tok)}($|[^\w])")
        else:
            pat = re.compile(rf"(^|[^\w]){re.escape(tok)}($|[^\w])")
        if pat.search(lean_source):
            bad.append(tok)
    return bad


def _render_blocks_for_prompt(blocks: list[TacticBlock]) -> str:
    parts: list[str] = []
    for b in blocks:
        parts.append(f"- CATEGORY: {b.name} (used in {b.used} proofs)")
        if b.description:
            parts.append(f"  DESC: {b.description}")
        if b.cases:
            parts.append("  CASES:")
            for c in b.cases:
                parts.append(f"  - {c.raw}")
    return "\n".join(parts)


def generate_lean_via_llm(
    *,
    api_key: str,
    model: str,
    blocks: list[TacticBlock],
    input_rel: str,
    max_attempts: int,
) -> str:
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    user_prompt = "\n".join(
        [
            "Generate `TacticFormalization/GeneratedTactics.lean` for the following categories.",
            "",
            f"Generated at (UTC): {ts}",
            f"Input: {input_rel}",
            "",
            _render_blocks_for_prompt(blocks),
        ]
    )
    last_bad: list[str] = []
    last_content: str | None = None

    for attempt in range(1, max_attempts + 1):
        messages = [
            {"role": "system", "content": LLM_SYSTEM_PROMPT},
            {"role": "user", "content": user_prompt},
        ]
        if attempt > 1:
            messages.append(
                {
                    "role": "user",
                    "content": "\n".join(
                        [
                            "Your previous output violated constraints by including forbidden tokens.",
                            f"Forbidden tokens detected: {', '.join(last_bad)}",
                            "",
                            "Rewrite the ENTIRE file from scratch and ensure none of those tokens appear anywhere (code or comments).",
                            "Keep the same overall interface: `import Mathlib` first, `namespace TacticFormalization`, one tactic per category.",
                            "Do not mention the forbidden tokens in any comments/docstrings.",
                        ]
                    ),
                }
            )

        payload = {
            "model": model,
            "temperature": 0,
            "messages": messages,
        }
        resp = _openai_chat_completions(api_key, payload)
        try:
            content = resp["choices"][0]["message"]["content"]
        except Exception as e:
            raise RuntimeError(f"Unexpected OpenAI response shape: {resp}") from e

        if not isinstance(content, str) or "import Mathlib" not in content:
            last_content = str(content)
            last_bad = ["(not a Lean file)"]
            continue

        if not content.lstrip().startswith("import Mathlib"):
            last_content = content
            last_bad = ["(missing leading `import Mathlib`)"]
            continue

        bad = _contains_forbidden_token(content.lower())
        if bad:
            last_content = content
            last_bad = bad
            continue

        return content

    raise RuntimeError(
        "LLM output repeatedly violated constraints. "
        f"Last detected forbidden tokens: {last_bad}. "
        "Try a different model, or lower the number of categories per run."
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate Lean tactics from a tactic report.")
    p.add_argument("--input", type=Path, default=ROOT / "out" / "common_proof_tactics.txt")
    p.add_argument("--output", type=Path, default=ROOT / "TacticFormalization" / "GeneratedTactics.lean")
    p.add_argument("--model", type=str, default=os.environ.get("OPENAI_MODEL", "gpt-4.1"))
    p.add_argument(
        "--api-key-file",
        type=Path,
        default=None,
        help="Path to a file containing the OpenAI API key (preferred over pasting keys into commands).",
    )
    p.add_argument(
        "--max-attempts",
        type=int,
        default=3,
        help="Max LLM retries if the output violates constraints (e.g. includes forbidden tokens).",
    )
    p.add_argument(
        "--offline",
        action="store_true",
        help="Do not call an LLM; generate compiling stub tactics (macros expand to `skip`).",
    )
    return p.parse_args(argv)


def main(argv: list[str]) -> int:
    args = _parse_args(argv)
    if not args.input.exists():
        print(f"Missing input report: {args.input}", file=sys.stderr)
        return 2

    input_text = args.input.read_text(errors="ignore")
    blocks = parse_report(input_text)
    if not blocks:
        print(f"No tactic blocks parsed from: {args.input}", file=sys.stderr)
        return 2

    input_rel = str(args.input.resolve().relative_to(ROOT))

    api_key = os.environ.get("OPENAI_API_KEY", "").strip()
    if not api_key and args.api_key_file is not None:
        if not args.api_key_file.exists():
            print(f"--api-key-file not found: {args.api_key_file}", file=sys.stderr)
            return 2
        api_key = args.api_key_file.read_text(errors="ignore").strip()

    if args.offline or not api_key:
        if not api_key and not args.offline:
            print(
                "OPENAI_API_KEY not set; generating offline stubs. "
                "Re-run with OPENAI_API_KEY set for LLM generation.",
                file=sys.stderr,
            )
        lean = generate_stub_lean(blocks, input_rel=input_rel)
    else:
        lean = generate_lean_via_llm(
            api_key=api_key,
            model=args.model,
            blocks=blocks,
            input_rel=input_rel,
            max_attempts=max(1, args.max_attempts),
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(lean)
    print(f"Wrote: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
