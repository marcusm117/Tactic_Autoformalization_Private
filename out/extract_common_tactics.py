#!/usr/bin/env python3
from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TEXT_PATH = ROOT / "out" / "group.txt"
OUTPUT_PATH = ROOT / "out" / "common_proof_tactics.txt"


def _normalize_text(s: str) -> str:
    # pdftotext sometimes uses "~" for negative exponent/inverse.
    s = s.replace("~", "-")
    # Occasionally, the PDF extraction yields repeated dots in numbering: "2.4..2".
    s = re.sub(r"\.{2,}", ".", s)
    return s


def _normalize_number(num: str) -> str:
    return re.sub(r"\.{2,}", ".", num).strip(". ")


@dataclass(frozen=True)
class Label:
    kind: str  # Proposition/Theorem/Lemma/Corollary
    number: str  # e.g. "2.8.14"
    title: str  # rest of the label line (may be empty)
    pdf_page: int  # 1-based PDF page index

    @property
    def short(self) -> str:
        return f"{self.kind} {self.number}"


@dataclass(frozen=True)
class Proof:
    case: str  # e.g. "Proposition 2.2.3" or "Proof of Theorem 2.12.2"
    title: str  # may be empty
    pdf_page: int  # 1-based PDF page index where the proof starts
    text: str

    def case_with_page(self) -> str:
        if self.title:
            return f"{self.case} — {self.title} (PDF p.{self.pdf_page})"
        return f"{self.case} (PDF p.{self.pdf_page})"


LABEL_RE = re.compile(
    r"^(Proposition|Theorem|Lemma|Corollary)\s+"
    r"([0-9]+(?:\.[0-9]+|\.+[0-9]+)+)\b\s*(.*)$"
)

PROOF_START_RE = re.compile(r"^(Proof\b|P\s*roofof\b|Proofof\b)", re.IGNORECASE)
PROOF_OF_RE = re.compile(r"^(P\s*roofof\b|Proofof\b)", re.IGNORECASE)


def load_lines_with_pdf_pages(text: str) -> list[tuple[int, str]]:
    lines: list[tuple[int, str]] = []
    for pdf_page, page_text in enumerate(text.split("\f"), start=1):
        for line in page_text.splitlines():
            lines.append((pdf_page, _normalize_text(line)))
    return lines


def extract_labels(lines: list[tuple[int, str]]) -> dict[int, Label]:
    labels: dict[int, Label] = {}
    for idx, (pdf_page, line) in enumerate(lines):
        m = LABEL_RE.match(line.strip())
        if not m:
            continue
        kind = m.group(1)
        number = _normalize_number(m.group(2))
        title = m.group(3).strip()
        labels[idx] = Label(kind=kind, number=number, title=title, pdf_page=pdf_page)
    return labels


def _find_previous_label(
    labels: dict[int, Label], start_idx: int, lookback: int = 500
) -> Label | None:
    for j in range(start_idx - 1, max(-1, start_idx - lookback), -1):
        lab = labels.get(j)
        if lab is not None:
            return lab
    return None


_NEXT_NONEMPTY_MARKER_RE = re.compile(
    r"^("
    r"(Proposition|Theorem|Lemma|Corollary)\b"
    r"|EXERCISES\b"
    r"|Section\b"
    r"|\d+\.\d+\b"  # section heading like "2.11"
    r"|\(\d+\.\d+\.\d+\)"  # equation/figure label like "(2.12.9)"
    r")"
)


def _next_nonempty_line(lines: list[tuple[int, str]], idx: int) -> str | None:
    for _, line in lines[idx:]:
        if line.strip():
            return line.strip()
    return None


def extract_proofs(lines: list[tuple[int, str]], labels: dict[int, Label]) -> list[Proof]:
    starts = [i for i, (_, line) in enumerate(lines) if PROOF_START_RE.match(line.strip())]
    proofs: list[Proof] = []

    for si in starts:
        start_line = lines[si][1].strip()
        pdf_page = lines[si][0]
        prev_label = _find_previous_label(labels, si)

        if prev_label is not None and not PROOF_OF_RE.match(start_line):
            case = prev_label.short
            title = prev_label.title
        else:
            # Try to extract "Proof of Theorem 2.12.2" style.
            m = re.search(
                r"\b(Theorem|Lemma|Proposition|Corollary)\s+([0-9]+(?:\.[0-9]+)+)\b",
                start_line,
            )
            if m:
                case = f"Proof of {m.group(1)} {m.group(2)}"
                title = ""
            elif "Correspondence Theorem" in start_line:
                case = "Proof of Theorem 2.10.5 (Correspondence Theorem)"
                title = ""
            else:
                case = "(unlabeled proof)"
                title = ""

        # Determine end of proof.
        # - For standard proofs: stop at the first □ after the start.
        # - For "Proof of ..." blocks: stop at a □ that is followed by a new section/label marker.
        end_idx = None
        if PROOF_OF_RE.match(start_line):
            for j in range(si, len(lines)):
                if "□" not in lines[j][1]:
                    continue
                nxt = _next_nonempty_line(lines, j + 1)
                if nxt is None or _NEXT_NONEMPTY_MARKER_RE.match(nxt):
                    end_idx = j
                    break
        else:
            for j in range(si, len(lines)):
                if "□" in lines[j][1]:
                    end_idx = j
                    break

        if end_idx is None:
            # Fallback: stop at next label or next proof start.
            next_boundary = min(
                [b for b in starts if b > si] + [b for b in labels.keys() if b > si] + [len(lines) - 1]
            )
            end_idx = max(si, next_boundary - 1)

        block = "\n".join(line for _, line in lines[si : end_idx + 1]).strip()
        proofs.append(
            Proof(
                case=case,
                title=title,
                pdf_page=pdf_page,
                text=_normalize_text(block),
            )
        )

    # De-duplicate cases (pdf extraction can duplicate some headers in rare cases).
    seen: set[tuple[str, int]] = set()
    unique: list[Proof] = []
    for pr in proofs:
        key = (pr.case, pr.pdf_page)
        if key in seen:
            continue
        seen.add(key)
        unique.append(pr)
    return unique


@dataclass(frozen=True)
class Tactic:
    name: str
    description: str
    patterns: list[re.Pattern[str]]


def build_tactics() -> list[Tactic]:
    def pats(*xs: str) -> list[re.Pattern[str]]:
        return [re.compile(x, re.IGNORECASE) for x in xs]

    return [
        Tactic(
            name="Inverse-cancellation algebra in groups",
            description=(
                "Solve/compare group equations by multiplying on the left/right by inverses "
                "to cancel factors (explicit use of cancellation/inverses)."
            ),
            patterns=pats(
                r"\bmultiply both sides\b",
                r"\bcancel\b",
                r"\bon the left by\b",
                r"\bon the right by\b",
                r"\bmultiplication by\b.*\b-\s*1\b",
                r"\b[a-zA-Z]\s*-\s*1\s*[a-zA-Z]\b",  # e.g. a^{-1}b
                r"\b[a-zA-Z]\s*-\s*1\s*\)",  # e.g. g^{-1})
            ),
        ),
        Tactic(
            name="Kernel–image reduction via homomorphisms",
            description=(
                "Define/use a homomorphism and reduce the claim to statements about "
                "kernel, image, fibres, and injective/surjective properties."
            ),
            patterns=pats(
                r"\bhomomorphism\b",
                r"\bkernel\b",
                r"\bimage\b",
                r"\bfibre\b|\bfiber\b",
                r"\binjective\b",
                r"\bsurjective\b",
            ),
        ),
        Tactic(
            name="Normality and conjugation invariance",
            description=(
                "Prove a subgroup is normal (or use normality) by checking closure under "
                "conjugation: g a g^{-1} stays in the subgroup; use gHg^{-1} manipulations."
            ),
            patterns=pats(
                r"\bnormal\b",
                r"\bgag\b",
                r"g\s*H\s*g\s*-\s*1",
                r"\bconjug",
                r"\bcommutator\b",
                r"h\s*k\s*h\s*-\s*1\s*k\s*-\s*1",
            ),
        ),
        Tactic(
            name="Equivalence classes / partitions",
            description=(
                "Introduce an equivalence relation and work with its equivalence classes "
                "and the induced partition (used for cosets and congruence mod n)."
            ),
            patterns=pats(
                r"\bequivalence relation\b",
                r"\bpartition\b",
                r"\bequivalence class\b",
                r"\bcongruence relation\b",
                r"\bmodulo\b",
                r"\bcongruent\b",
                r"\ba\s*\+\s*r\s*n\b",  # e.g. a' = a + rn
                r"\bb\s*\+\s*s\s*n\b",  # e.g. b' = b + sn
                r"\ba\s*~\s*b\b",
            ),
        ),
        Tactic(
            name="Cosets + counting / index arguments",
            description=(
                "Use coset partitions and counting/index formulas (Lagrange-style divisibility, "
                "multiplicativity of index, cosets all same size)."
            ),
            patterns=pats(
                r"\bcoset\b",
                r"\bcosets\b",
                r"\bindex\b",
                r"\bLagrange\b",
                r"\bCounting Formula\b",
                r"\[G\s*:\s*H\]",
                r"map\s+H\s*-\+\s*aH\b",
            ),
        ),
        Tactic(
            name="Bezout / gcd–lcm divisibility trick",
            description=(
                "Use gcd/lcm structure and Bezout-style linear combinations (d = ra + sb) "
                "to prove divisibility statements."
            ),
            patterns=pats(
                r"\bgcd\b",
                r"\blcm\b",
                r"\bra\s*\+\s*sb\b",
                r"\br\s*a\s*\+\s*s\s*b\b",
                r"\binteger combination\b",
                r"\bgreatest common divisor\b",
                r"\bleast common multiple\b",
            ),
        ),
        Tactic(
            name="Order divisibility via cyclic subgroups (Lagrange-style)",
            description=(
                "Use the cyclic subgroup generated by an element and a divisibility statement "
                "about orders (e.g. “order of a divides |G|”, prime-order implies cyclic)."
            ),
            patterns=pats(
                r"\border of an element\b",
                r"\border of any element\b",
                r"\bdivides the order of\b",
                r"\bcyclic subgroup\b",
                r"\bprime order\b",
            ),
        ),
        Tactic(
            name="Subgroup verification (closure/identity/inverses)",
            description=(
                "Prove a set is a subgroup by verifying subgroup axioms (contains identity, "
                "closed under products, closed under inverses), often explicitly enumerated."
            ),
            patterns=pats(
                r"\bverify\b.*\bsubgroup\b",
                r"\bclosed under\b",
                r"\bclosure\b",
                r"\bsubgroup\b.*\baxiom",
                r"\bthe (first|second|third) property\b.*\bfor a subgroup\b",
                r"\bthis proves closure\b",
            ),
        ),
    ]


def main() -> None:
    if not TEXT_PATH.exists():
        raise SystemExit(f"Missing {TEXT_PATH}. Generate it with pdftotext first.")

    text = TEXT_PATH.read_text(errors="ignore")
    lines = load_lines_with_pdf_pages(text)
    labels = extract_labels(lines)
    proofs = extract_proofs(lines, labels)

    tactics = build_tactics()

    occurrences: dict[str, list[Proof]] = {t.name: [] for t in tactics}
    for pr in proofs:
        for tac in tactics:
            if any(p.search(pr.text) for p in tac.patterns):
                occurrences[tac.name].append(pr)

    # Filter tactics used at least 3 times, as requested.
    tactics_kept = [t for t in tactics if len(occurrences[t.name]) >= 3]
    tactics_kept.sort(key=lambda t: len(occurrences[t.name]), reverse=True)

    out_lines: list[str] = []
    out_lines.append("Most common proof tactics in group.pdf (filtered to tactics used >= 3 times)")
    out_lines.append("")
    out_lines.append(f"Detected proofs analyzed: {len(proofs)}")
    out_lines.append("")

    for tac in tactics_kept:
        items = occurrences[tac.name]
        # De-dup by (case,pdf_page) but preserve order.
        seen: set[tuple[str, int]] = set()
        uniq: list[Proof] = []
        for pr in items:
            key = (pr.case, pr.pdf_page)
            if key in seen:
                continue
            seen.add(key)
            uniq.append(pr)

        out_lines.append(f"- {tac.name} (used in {len(uniq)} proofs)")
        out_lines.append(f"  {tac.description}")
        out_lines.append("  Cases:")
        for pr in uniq:
            out_lines.append(f"  - {pr.case_with_page()}")
        out_lines.append("")

    OUTPUT_PATH.write_text("\n".join(out_lines).rstrip() + "\n")
    print(f"Wrote: {OUTPUT_PATH}")


if __name__ == "__main__":
    main()
