This folder contains small utilities for turning extracted natural-language proof patterns into Lean tooling.

- `scripts/gen_lean_tactics.py`: reads a tactic report text file and generates `TacticFormalization/GeneratedTactics.lean`.

Usage:
- Offline stubs (no LLM): `python scripts/gen_lean_tactics.py --offline`
- LLM generation (env var): `OPENAI_API_KEY=... python scripts/gen_lean_tactics.py --model gpt-4.1`
- LLM generation (key file): `python scripts/gen_lean_tactics.py --api-key-file ~/.config/openai_api_key --model gpt-4.1`
- Increase retries if the model violates constraints: `python scripts/gen_lean_tactics.py --max-attempts 5`

Notes:
- The generator is report-agnostic: it derives tactic names from the category headings in the input file.
- The generated Lean file is always placed at `TacticFormalization/GeneratedTactics.lean` unless `--output` is provided.
