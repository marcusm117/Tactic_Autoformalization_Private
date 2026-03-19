# Authors: marcusm117
# License: Apache 2.0


# Standard Library Modules
import argparse
import csv
import json
import logging
import subprocess
from datetime import datetime
from pathlib import Path

# External Modules
from joblib import Parallel, delayed
from openai import OpenAI
from tqdm import tqdm


# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
)
logger = logging.getLogger(__name__)

# Project root (where lakefile.lean lives)
PROJECT_ROOT = Path(__file__).resolve().parent.parent

# Path to the custom tactics file
TACTICS_FILE = PROJECT_ROOT / "Abstraction_Learning" / "ProofNet-V" / "ProofStrategyTactics_parameterized.lean"

# Directory for temporary Lean files during compilation
TMP_DIR = PROJECT_ROOT / "tmp"

# Maximum line length for Lean error messages in feedback
MAX_ERROR_LINES = 60

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

# Default number of parallel workers
DEFAULT_N_JOBS = 64


def load_problems(csv_path: str) -> list[dict]:
    """Load test problems from the CSV file."""
    problems = []
    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            problems.append(row)
    logger.info("Loaded %d problems from %s", len(problems), csv_path)
    return problems


def load_tactics_context() -> str:
    """Load the custom tactics Lean file content for use in prompts."""
    content = TACTICS_FILE.read_text(encoding="utf-8")
    return content


def build_system_prompt(with_tactics: bool, tactics_content: str | None = None) -> str:
    """Build the system prompt for the LLM.

    Args:
        with_tactics: Whether to include custom tactics in the prompt.
        tactics_content: The content of the custom tactics file (required if with_tactics is True).

    Returns:
        The system prompt string.
    """
    base = (
        "You are an expert Lean 4 proof assistant. Your task is to write formal Lean 4 proofs "
        "for mathematical theorems. You will be given:\n"
        "1. An informal mathematical statement\n"
        "2. An informal proof (which may be incomplete or imprecise)\n"
        "3. A formal Lean 4 theorem statement\n\n"
        "You MUST:\n"
        "- Write ONLY the proof body (starting with `by` or `:=`), nothing else\n"
        "- NOT use `sorry` or `admit`\n"
        "- NOT modify the theorem statement\n"
        "- NOT include any import statements or the theorem signature in your response\n"
        "- Output ONLY the proof code, no markdown fences, no explanations\n\n"
        "You are using Lean 4.24.0 with Mathlib.\n"
    )

    if with_tactics and tactics_content:
        base += (
            "\n--- CUSTOM TACTICS AVAILABLE ---\n"
            "The following custom tactics are imported and available for use in your proof. "
            "You should try your best to use them when appropriate.\n\n"
            f"{tactics_content}\n"
            "--- END CUSTOM TACTICS ---\n"
        )

    return base


def build_user_prompt(problem: dict) -> str:
    """Build the user prompt for a single problem.

    Args:
        problem: A dictionary representing one row from the CSV.

    Returns:
        The user prompt string.
    """
    nl_statement = problem.get("nl_statement", "")
    nl_proof = problem.get("nl_proof", "")
    formalization = problem.get("lean4_formalization", "")

    prompt = (
        f"## Informal Statement\n{nl_statement}\n\n"
        f"## Informal Proof\n{nl_proof}\n\n"
        f"## Formal Lean 4 Statement\n```lean\n{formalization}\n```\n\n"
        "Write the proof body below (starting with `by` or `:=`):"
    )
    return prompt


def build_refinement_prompt(proof_attempt: str, error_message: str) -> str:
    """Build a refinement prompt given a failed proof attempt and compiler errors.

    Args:
        proof_attempt: The previous proof attempt that failed.
        error_message: The Lean compiler error output.

    Returns:
        The refinement prompt string.
    """
    # Truncate very long error messages
    error_lines = error_message.strip().split("\n")
    if len(error_lines) > MAX_ERROR_LINES:
        error_message = "\n".join(error_lines[:MAX_ERROR_LINES]) + "\n... (truncated)"

    prompt = (
        f"Your previous proof attempt failed with the following Lean compiler errors:\n\n"
        f"```\n{error_message}\n```\n\n"
        f"Your previous proof attempt was:\n```lean\n{proof_attempt}\n```\n\n"
        "Please fix the proof. Output ONLY the corrected proof body (starting with `by` or `:=`), "
        "no markdown fences, no explanations."
    )
    return prompt


def build_lean_file(problem: dict, proof: str, with_tactics: bool) -> str:
    """Build a complete Lean 4 file for compilation.

    Args:
        problem: A dictionary representing one row from the CSV.
        proof: The proof body to insert.
        with_tactics: Whether to include the custom tactics import.

    Returns:
        The complete Lean file content as a string.
    """
    header = problem.get("lean4_src_header", "")
    formalization = problem.get("lean4_formalization", "")

    # Build the file content
    parts = []

    if with_tactics:
        # Import the custom tactics file (it's in the project as TacticFormalization.Tactics
        # which transitively imports GeneratedTactics which imports Mathlib)
        # But the elabed tactics are standalone - we inline them after the header
        # First, ensure Mathlib is imported (it's in the header already)
        parts.append(header.strip())
        # Add the open statements needed by the elab tactics
        parts.append("")
        # Read and inline the tactics (skip the `import Mathlib` line since header already has it)
        tactics_content = TACTICS_FILE.read_text(encoding="utf-8")
        tactics_lines = tactics_content.split("\n")
        filtered_lines = []
        for line in tactics_lines:
            # Skip duplicate import Mathlib
            if line.strip() == "import Mathlib":
                continue
            filtered_lines.append(line)
        parts.append("\n".join(filtered_lines))
        parts.append("")
    else:
        parts.append(header.strip())
        parts.append("")

    # Add the theorem statement and proof
    # The formalization ends with `:=` so we append the proof after it
    parts.append(f"{formalization} {proof}")
    parts.append("")

    return "\n".join(parts)


def compile_lean_file(file_path: Path, timeout: int = 300) -> tuple[bool, str]:
    """Compile a Lean 4 file and return success status and error output.

    Also rejects proofs that use ``sorry`` or ``admit``, which compile
    successfully but leave the proof incomplete.

    Args:
        file_path: Path to the Lean file to compile.
        timeout: Timeout in seconds for the compilation.

    Returns:
        A tuple of (success, error_message).
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
        if result.returncode == 0:
            # Check stderr for warnings that might indicate issues
            stderr = result.stderr.strip()
            if "error" in stderr.lower():
                return False, stderr
            # Reject proofs that rely on sorry/admit (compiles but is incomplete)
            stderr_lower = stderr.lower()
            if "sorry" in stderr_lower or "admit" in stderr_lower:
                return False, f"Proof uses sorry/admit (incomplete proof)\n{stderr}"
            return True, ""
        error = result.stderr.strip() if result.stderr.strip() else result.stdout.strip()
        return False, error
    except subprocess.TimeoutExpired:
        return False, f"Compilation timed out after {timeout} seconds"
    except Exception as e:
        return False, f"Compilation failed with exception: {e}"


def call_openai(
    client: OpenAI,
    model: str,
    system_prompt: str,
    messages: list[dict],
    reasoning_effort: str = "medium",
) -> str:
    """Call the OpenAI API and return the response text.

    Args:
        client: The OpenAI client instance.
        model: The model name to use.
        system_prompt: The system prompt.
        messages: The conversation messages (user/assistant turns).
        reasoning_effort: The reasoning effort level.

    Returns:
        The model's response text.
    """
    full_messages = [{"role": "system", "content": system_prompt}] + messages

    response = client.chat.completions.create(
        model=model,
        messages=full_messages,
        reasoning_effort=reasoning_effort,
        temperature=1,  # Required for reasoning models
    )
    return response.choices[0].message.content.strip()


def clean_proof_response(response: str) -> str:
    """Clean the model's response to extract just the proof body.

    Removes markdown fences and extraneous text.

    Args:
        response: The raw model response.

    Returns:
        The cleaned proof body.
    """
    # Remove markdown code fences
    if "```lean" in response:
        # Extract content between ```lean and ```
        start = response.index("```lean") + len("```lean")
        end = response.index("```", start)
        response = response[start:end].strip()
    elif "```" in response:
        # Extract content between ``` and ```
        start = response.index("```") + len("```")
        end = response.index("```", start)
        response = response[start:end].strip()

    return response


def solve_single_problem(
    problem: dict,
    prob_idx: int,
    model: str,
    system_prompt: str,
    with_tactics: bool,
    max_iterations: int,
    reasoning_effort: str,
    compile_timeout: int,
    tmp_dir: Path | None = None,
) -> dict:
    """Solve a single problem with self-refinement. Designed to run in a separate process.

    Each worker creates its own OpenAI client to avoid serialization issues with joblib.

    Args:
        problem: A dictionary representing one row from the CSV.
        prob_idx: The index of the problem in the dataset (for unique file naming).
        model: The OpenAI model name.
        system_prompt: The pre-built system prompt string.
        with_tactics: Whether this is the tactics-augmented condition.
        max_iterations: Maximum self-refinement iterations.
        reasoning_effort: The reasoning effort level for the model.
        compile_timeout: Timeout in seconds for Lean compilation.
        tmp_dir: Directory for temporary Lean files (defaults to global TMP_DIR).

    Returns:
        A dictionary with the problem result.
    """
    # Each worker creates its own OpenAI client (uses OPENAI_API_KEY env var)
    client = OpenAI()

    if tmp_dir is None:
        tmp_dir = TMP_DIR

    condition = "with_tactics" if with_tactics else "baseline"
    prob_id = problem.get("id", f"unknown_{prob_idx}")

    user_prompt = build_user_prompt(problem)
    messages = [{"role": "user", "content": user_prompt}]

    solved = False
    iterations_used = 0
    proof_attempts = []

    for iteration in range(max_iterations):
        iterations_used = iteration + 1

        # Call the model (retry on transient API errors)
        try:
            response = call_openai(client, model, system_prompt, messages, reasoning_effort)
        except Exception as e:
            logger.error("  OpenAI API error for %s iteration %d: %s", prob_id, iterations_used, str(e))
            proof_attempts.append({"iteration": iterations_used, "proof": "", "error": f"API error: {e}", "compiled": False})
            continue

        proof = clean_proof_response(response)

        # Build the Lean file and compile
        lean_content = build_lean_file(problem, proof, with_tactics)
        tmp_file = tmp_dir / f"{condition}_{prob_id.replace('|', '_')}_{iteration}.lean"
        tmp_file.write_text(lean_content, encoding="utf-8")

        success, error = compile_lean_file(tmp_file, timeout=compile_timeout)

        proof_attempts.append(
            {
                "iteration": iterations_used,
                "proof": proof,
                "error": error if not success else "",
                "compiled": success,
            }
        )

        if success:
            logger.info("  [%s] %s PASSED on iteration %d", condition, prob_id, iterations_used)
            solved = True
            break

        logger.info("  [%s] %s FAILED on iteration %d", condition, prob_id, iterations_used)

        # Add the assistant response and refinement prompt to messages
        messages.append({"role": "assistant", "content": response})
        refinement = build_refinement_prompt(proof, error)
        messages.append({"role": "user", "content": refinement})

    return {
        "id": prob_id,
        "condition": condition,
        "solved": solved,
        "iterations_used": iterations_used,
        "proof_attempts": proof_attempts,
    }


def run_experiment(
    problems: list[dict],
    model: str,
    with_tactics: bool,
    tactics_content: str | None,
    max_iterations: int,
    reasoning_effort: str,
    output_dir: Path,
    compile_timeout: int,
    n_jobs: int,
    tmp_dir: Path | None = None,
) -> dict:
    """Run the experiment on all problems in parallel using joblib.

    Args:
        problems: List of problem dictionaries from the CSV.
        model: The model name.
        with_tactics: Whether this is the tactics-augmented experiment.
        tactics_content: Content of the tactics file (for prompt context).
        max_iterations: Maximum self-refinement iterations per problem.
        reasoning_effort: The reasoning effort level for the model.
        output_dir: Directory to save results.
        compile_timeout: Timeout in seconds for Lean compilation.
        n_jobs: Number of parallel workers.
        tmp_dir: Directory for temporary Lean files (defaults to global TMP_DIR).

    Returns:
        A dictionary with experiment results and statistics.
    """
    condition = "with_tactics" if with_tactics else "baseline"
    logger.info("Running %s condition on %d problems with %d workers", condition, len(problems), n_jobs)

    system_prompt = build_system_prompt(with_tactics, tactics_content)

    # Run all problems in parallel using joblib multiprocessing
    results = Parallel(n_jobs=n_jobs, backend="loky")(
        delayed(solve_single_problem)(
            problem=problem,
            prob_idx=prob_idx,
            model=model,
            system_prompt=system_prompt,
            with_tactics=with_tactics,
            max_iterations=max_iterations,
            reasoning_effort=reasoning_effort,
            compile_timeout=compile_timeout,
            tmp_dir=tmp_dir,
        )
        for prob_idx, problem in enumerate(tqdm(problems, desc=f"Dispatching {condition}"))
    )

    # Compute statistics
    num_solved = sum(1 for r in results if r["solved"])
    pass_rate = num_solved / len(results) if results else 0.0
    avg_iterations = sum(r["iterations_used"] for r in results) / len(results) if results else 0.0
    solved_results = [r for r in results if r["solved"]]
    avg_iterations_correct = sum(r["iterations_used"] for r in solved_results) / len(solved_results) if solved_results else 0.0

    stats = {
        "condition": condition,
        "model": model,
        "reasoning_effort": reasoning_effort,
        "num_problems": len(results),
        "num_solved": num_solved,
        "pass_rate": pass_rate,
        "avg_iterations": avg_iterations,
        "avg_iterations_correct": avg_iterations_correct,
    }

    logger.info("=== %s Results ===", condition.upper())
    logger.info("  Pass rate: %d/%d (%.1f%%)", num_solved, len(results), pass_rate * 100)
    logger.info("  Avg iterations (all): %.2f", avg_iterations)
    logger.info("  Avg iterations (correct): %.2f", avg_iterations_correct)

    # Save results
    output_dir.mkdir(parents=True, exist_ok=True)
    results_file = output_dir / f"results_{condition}.json"
    with open(results_file, "w", encoding="utf-8") as f:
        json.dump({"stats": stats, "results": results}, f, indent=2)
    logger.info("  Results saved to %s", results_file)

    return stats


def main():
    """Main entry point for the proof generation experiment."""
    parser = argparse.ArgumentParser(description="Run Lean 4 proof generation experiments with OpenAI models.")
    parser.add_argument(
        "--model",
        type=str,
        default="gpt-5.4-mini-2026-03-17",  # gpt-5.4-2026-03-05
        help="OpenAI model to use (default: gpt-5.4-mini-2026-03-17)",
    )
    parser.add_argument(
        "--reasoning-effort",
        type=str,
        default="medium",
        choices=["low", "medium", "high"],
        help="Reasoning effort level (default: medium)",
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=5,
        help="Maximum self-refinement iterations per problem (default: 5)",
    )
    parser.add_argument(
        "--split",
        type=str,
        default="test",
        choices=["train", "test"],
        help="Data split to use: 'train' or 'test' (default: test)",
    )
    parser.add_argument(
        "--csv-path",
        type=str,
        default=None,
        help="Path to the CSV file (overrides --split if provided)",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=str(PROJECT_ROOT / "experiments" / "results"),
        help="Directory to save experiment results",
    )
    parser.add_argument(
        "--compile-timeout",
        type=int,
        default=300,
        help="Timeout in seconds for Lean compilation (default: 300)",
    )
    parser.add_argument(
        "--n-jobs",
        type=int,
        default=DEFAULT_N_JOBS,
        help=f"Number of parallel workers (default: {DEFAULT_N_JOBS})",
    )
    parser.add_argument(
        "--no-baseline",
        action="store_true",
        default=False,
        help="Skip the baseline condition",
    )
    parser.add_argument(
        "--no-tactics",
        action="store_true",
        default=False,
        help="Skip the tactics-augmented condition",
    )
    args = parser.parse_args()

    # Resolve CSV path: --csv-path overrides --split
    if args.csv_path is not None:
        csv_path = args.csv_path
    else:
        csv_path = str(PROJECT_ROOT / "data" / f"ProofNet-V_Artin_DummitFoote_{args.split}.csv")

    # Determine the split name for directory naming
    if args.csv_path is not None:
        # Infer split from the CSV filename, fall back to "custom"
        csv_stem = Path(args.csv_path).stem
        if "train" in csv_stem:
            split_name = "train"
        elif "test" in csv_stem:
            split_name = "test"
        else:
            split_name = "custom"
    else:
        split_name = args.split

    # Setup directories with model, reasoning effort, split, iterations, and timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_name = f"{args.model}_{args.reasoning_effort}_{split_name}_{args.max_iterations}iters_{timestamp}"
    output_dir = Path(args.output_dir) / run_name
    output_dir.mkdir(parents=True, exist_ok=True)
    tmp_run_dir = TMP_DIR / run_name
    tmp_run_dir.mkdir(parents=True, exist_ok=True)

    # Load data
    problems = load_problems(csv_path)
    tactics_content = load_tactics_context()

    all_stats = {}

    # Run baseline
    if not args.no_baseline:
        baseline_stats = run_experiment(
            problems=problems,
            model=args.model,
            with_tactics=False,
            tactics_content=None,
            max_iterations=args.max_iterations,
            reasoning_effort=args.reasoning_effort,
            output_dir=output_dir,
            compile_timeout=args.compile_timeout,
            n_jobs=args.n_jobs,
            tmp_dir=tmp_run_dir,
        )
        all_stats["baseline"] = baseline_stats

    # Run tactics-augmented experiment
    if not args.no_tactics:
        tactics_stats = run_experiment(
            problems=problems,
            model=args.model,
            with_tactics=True,
            tactics_content=tactics_content,
            max_iterations=args.max_iterations,
            reasoning_effort=args.reasoning_effort,
            output_dir=output_dir,
            compile_timeout=args.compile_timeout,
            n_jobs=args.n_jobs,
            tmp_dir=tmp_run_dir,
        )
        all_stats["with_tactics"] = tactics_stats

    # Print summary
    print("\n" + "=" * 60)
    print("EXPERIMENT SUMMARY")
    print("=" * 60)
    print(f"Model: {args.model}")
    print(f"Reasoning effort: {args.reasoning_effort}")
    print(f"Max iterations: {args.max_iterations}")
    print(f"Num problems: {len(problems)}")
    print(f"Parallel workers: {args.n_jobs}")
    print("-" * 60)

    for condition, stats in all_stats.items():
        num_s = stats["num_solved"]
        num_p = stats["num_problems"]
        prate = stats["pass_rate"] * 100
        avg_it = stats["avg_iterations"]
        avg_it_c = stats["avg_iterations_correct"]
        print(f"  {condition:<15s}: {num_s}/{num_p} solved ({prate:.1f}%), avg iter {avg_it:.2f} (all), {avg_it_c:.2f} (correct)")

    print("=" * 60)

    # Save combined summary
    summary_file = output_dir / "summary.json"
    with open(summary_file, "w", encoding="utf-8") as f:
        json.dump(all_stats, f, indent=2)
    print(f"Summary saved to {summary_file}")


if __name__ == "__main__":
    main()
