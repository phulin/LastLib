# Book 1 Lean Proof Orchestrator Prompt

Work only in `/home/phulin/LastLib-book1`. This repository contains one Lean file for each chapter of Book 1. Using `books/01-valuations-dvrs-and-completions.md` as the mathematical blueprint, complete every chapter file under `lean/LastLib/Book01ValuationsDVRsAndCompletions/Chapter01.lean` through `Chapter12.lean`.

Act only as the orchestrator. All substantive proof development and Lean repair work must be performed by `codex exec` workers using `gpt-5.6-luna` with maximum reasoning effort. Start one worker per chapter and run all chapter workers in parallel. Give every worker full filesystem access with no approval requests (`danger-full-access` and approval policy `never`). Each worker must edit only its assigned chapter file, apart from temporary worktree-local scratch files that it removes before finishing.

Before launching workers, prepare the project cache serially from `/home/phulin/LastLib-book1/lean`:

1. Run `lake exe cache get` and confirm the pinned Mathlib executable cache is present.
2. Run one full `lake build` to warm the project cache. Before starting it, require at least 20 GiB of available RAM using a `/proc/meminfo` predicate joined directly to the build with `&&`. If less memory is available, wait 30 seconds and retry.

All workers must use the same project directory and its shared `.lake` tree. Do not set separate `LAKE_HOME`, `LEAN_PATH`, package-cache, or build-directory overrides.

Give each worker the contents of `SUBAGENT_PROMPT.md`, replacing `<CHAPTER>` and `<CHAPTER_NUMBER>` for its assigned file. Tell workers to rely on pinned Mathlib as much as possible. Later chapters may use declarations from earlier chapters.

Enforce these project-wide rules:

- Eliminate every `sorry` and `admit`.
- Do not use or leave `aesop` anywhere. Existing `aesop` invocations must be replaced by explicit Mathlib-based proofs and focused ordinary tactics.
- Do not introduce axioms, unsafe declarations, or other proof loopholes.
- Use `lake build` exclusively for compilation and testing; never use `lake env lean`.
- Immediately before every Lake build, check that `/proc/meminfo` reports `MemAvailable >= 20971520` kB and join the successful check to the Lake command with `&&`. If the check fails, wait 30 seconds and retry.
- Preserve unrelated changes and do not commit.
- If a declaration is false, unprovable from its assumptions, or inaccurately formalizes the book, correct it as closely as possible to the book and require the worker to report the exact change and justification.
- Each worker must first write a complete proof attempt for every placeholder throughout its entire file before compiling. It should then fix compiler errors in batches to reduce agent turns.

If workers are interrupted or killed, restart or resume them with the same Luna model, maximum reasoning, full-access/no-approval settings, shared project cache, assigned-file boundary, and current worktree state. Do not take over their proof work in the main agent.

Monitor the parallel workers with waits of up to 20 minutes rather than frequent polling, while still reporting useful progress. Once every worker finishes, run a guarded aggregate `lake build` from the project directory. Then run a repository-wide audit over all chapter files for `sorry`, `admit`, `aesop`, `axiom`, and `unsafe`, and run `git diff --check`.

The final report must include:

- Whether every chapter and the aggregate project build succeeded.
- The final forbidden-token audit result.
- Confirmation that all workers shared the same `.lake` cache.
- Every theorem, definition, or interface correction reported by the workers, with its reason.
- Remaining nonfatal warnings.
- The exact files modified and confirmation that scratch files were removed.

