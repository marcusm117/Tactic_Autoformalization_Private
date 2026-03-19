# Authors: marcusm117
# License: Apache 2.0


# Standard Library Modules
import argparse
import re
import subprocess
from pathlib import Path

# External Modules
from joblib import Parallel, delayed


# Project root (where lakefile.lean lives)
PROJECT_ROOT = Path(__file__).resolve().parent.parent

# Directory for temporary Lean files
TMP_DIR = PROJECT_ROOT / "tmp"

# LEAN_PATH for direct `lean` invocation (bypasses lake lock)
LEAN_PATH = ":".join(
    [
        str(PROJECT_ROOT / ".lake/packages/Cli/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/batteries/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/Qq/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/aesop/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/proofwidgets/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/importGraph/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/LeanSearchClient/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/plausible/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/mathlib/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/packages/Canonical/.lake/build/lib/lean"),
        str(PROJECT_ROOT / ".lake/build/lib/lean"),
    ]
)


def find_last_iteration_files(condition: str, tmp_dir: Path | None = None) -> dict[str, tuple[Path, int]]:
    """Find the last iteration Lean file for each problem under a given condition.

    Args:
        condition: Either 'baseline' or 'with_tactics'.
        tmp_dir: Directory to search for .lean files. Defaults to TMP_DIR.

    Returns:
        A dict mapping problem name to (file_path, iteration_number).
    """
    search_dir = tmp_dir if tmp_dir else TMP_DIR
    files = sorted(search_dir.glob(f"{condition}_*.lean"))
    problems: dict[str, tuple[Path, int]] = {}
    for f in files:
        m = re.match(rf"({re.escape(condition)}_.+)_(\d+)\.lean", f.name)
        if m:
            prob = m.group(1)
            iteration = int(m.group(2))
            if prob not in problems or iteration > problems[prob][1]:
                problems[prob] = (f, iteration)
    return problems


def check_compilation(file_path: Path, timeout: int = 300) -> bool:
    """Compile a Lean file and return whether it succeeded.

    Also rejects proofs that use ``sorry`` or ``admit``, which compile
    successfully but leave the proof incomplete.

    Args:
        file_path: Path to the Lean file.
        timeout: Compilation timeout in seconds.

    Returns:
        True if the file compiles without errors and does not use sorry/admit,
        False otherwise.
    """
    try:
        env = {**subprocess.os.environ, "LEAN_PATH": LEAN_PATH}
        result = subprocess.run(
            ["lean", str(file_path)],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(PROJECT_ROOT),
            check=False,
            env=env,
        )
        if result.returncode == 0 and "error" not in result.stderr.lower():
            # Reject proofs that rely on sorry/admit — the Lean compiler
            # emits "declaration uses 'sorry'" warnings in stderr
            stderr_lower = result.stderr.lower()
            if "sorry" in stderr_lower or "admit" in stderr_lower:
                return False
            return True
        return False
    except (subprocess.TimeoutExpired, Exception):
        return False


def check_single_problem(prob: str, file_path: Path, iteration: int) -> dict:
    """Check a single problem's compilation. Designed for parallel execution.

    Args:
        prob: The problem identifier string.
        file_path: Path to the last iteration Lean file.
        iteration: The iteration number (0-indexed).

    Returns:
        A dict with problem name, file path, iteration, and compilation result.
    """
    success = check_compilation(file_path)
    return {
        "problem": prob,
        "file": str(file_path),
        "iterations_used": iteration + 1,  # Convert 0-indexed to 1-indexed
        "compiled": success,
    }


def main():
    """Analyze and compare baseline vs with_tactics experiment results."""
    parser = argparse.ArgumentParser(description="Analyze proof generation experiment results.")
    parser.add_argument(
        "--n-jobs",
        type=int,
        default=64,
        help="Number of parallel workers (default: 64)",
    )
    parser.add_argument(
        "--compile-timeout",
        type=int,
        default=300,
        help="Timeout in seconds for Lean compilation (default: 300)",
    )
    parser.add_argument(
        "--tmp-dir",
        type=str,
        default=None,
        help="Path to the directory containing generated .lean files (default: PROJECT_ROOT/tmp)",
    )
    args = parser.parse_args()

    tmp_dir = Path(args.tmp_dir) if args.tmp_dir else TMP_DIR

    conditions = ["baseline", "with_tactics"]
    all_results: dict[str, list[dict]] = {}

    for condition in conditions:
        problems = find_last_iteration_files(condition, tmp_dir)
        print(f"[{condition}] Found {len(problems)} problems")

        # Check all problems in parallel
        results = Parallel(n_jobs=args.n_jobs, backend="loky")(
            delayed(check_single_problem)(prob, file_path, iteration) for prob, (file_path, iteration) in sorted(problems.items())
        )
        all_results[condition] = results

    # Print comparison
    print("\n" + "=" * 70)
    print("EXPERIMENT RESULTS COMPARISON")
    print("=" * 70)

    for condition in conditions:
        results = all_results[condition]
        total = len(results)
        passed = [r for r in results if r["compiled"]]
        num_passed = len(passed)
        pass_rate = num_passed / total * 100 if total else 0.0
        avg_iter_passed = sum(r["iterations_used"] for r in passed) / num_passed if num_passed else 0.0
        avg_iter_all = sum(r["iterations_used"] for r in results) / total if total else 0.0

        print(f"\n--- {condition} ---")
        print(f"  Total problems:          {total}")
        print(f"  Correct (compiled):      {num_passed}/{total} ({pass_rate:.1f}%)")
        print(f"  Avg iterations (correct): {avg_iter_passed:.2f}")
        print(f"  Avg iterations (all):     {avg_iter_all:.2f}")

        # List correct problems
        if passed:
            print("  Correct problems:")
            for r in passed:
                print(f"    {r['problem']} (iter {r['iterations_used']})")

    # Side-by-side comparison
    if len(conditions) == 2:
        c1, c2 = conditions
        r1 = all_results[c1]
        r2 = all_results[c2]
        p1 = {r["problem"].replace(f"{c1}_", ""): r for r in r1}
        p2 = {r["problem"].replace(f"{c2}_", ""): r for r in r2}

        # Find problems solved by one but not the other
        solved1 = {k for k, v in p1.items() if v["compiled"]}
        solved2 = {k for k, v in p2.items() if v["compiled"]}
        only1 = solved1 - solved2
        only2 = solved2 - solved1
        both = solved1 & solved2

        print("\n" + "=" * 70)
        print("DIFF ANALYSIS")
        print("=" * 70)
        print(f"  Solved by both:          {len(both)}")
        print(f"  Solved only by {c1}:  {len(only1)}")
        if only1:
            for p in sorted(only1):
                print(f"    {p}")
        print(f"  Solved only by {c2}: {len(only2)}")
        if only2:
            for p in sorted(only2):
                print(f"    {p}")

    print("\n" + "=" * 70)


if __name__ == "__main__":
    main()
