# Book 1 Chapter Luna Worker Prompt

You are the sole implementation agent for `ValuationsBook/ValuationsBook/<CHAPTER>.lean` in `/home/phulin/LastLib-book1`. Use `gpt-5.6-luna` with maximum reasoning effort throughout. You are running with full filesystem access and approval policy `never`.

Work only in this worktree and edit only your assigned chapter file, except for temporary scratch files inside the worktree that you must remove before finishing. Preserve unrelated changes and do not commit.

Read the entire target Lean file and the relevant material for Chapter `<CHAPTER_NUMBER>` in `books/01-valuations-dvrs-and-completions.md`. Treat the book as the mathematical blueprint. Inspect the pinned Mathlib sources under `ValuationsBook/.lake/packages/mathlib` freely and rely on existing Mathlib definitions and theorems as much as possible. You may use declarations from earlier chapter files.

Eliminate every `sorry` and `admit` in the entire assigned file with genuine complete Lean proofs. Do not introduce axioms, unsafe declarations, contradictory artificial assumptions, or other proof loopholes. The `aesop` tactic is banned: do not add or invoke it anywhere, and replace every existing `aesop` invocation in your assigned file with explicit proofs using concrete Mathlib lemmas and ordinary focused tactics.

Follow this batching discipline:

1. Read and understand the complete file and corresponding book material.
2. Before compiling, write a complete proof attempt for every `sorry` across the whole file.
3. Only after the whole-file proof-writing pass, compile and eliminate errors in batches to reduce the number of agent turns.
4. Continue autonomously until the file contains no `sorry`, `admit`, or `aesop` and its Lake target builds.

You may revise a definition or theorem statement only when the original is genuinely false, unprovable from its stated assumptions, blocks later results because it is malformed, or inaccurately formalizes the book. Keep every correction as close as possible to the book. Do not weaken a valid mathematical claim merely to make compilation pass. Do not add the conclusion as a hypothesis. Only make these revisions to move the semantics closer to those in the source book, and more mathematically accurate. Record every declaration change and its precise mathematical or formalization reason for your final report.

Use only Lake builds for compilation and testing. Never run `lake env lean`. Run builds from `/home/phulin/LastLib-book1/ValuationsBook` so all workers use the same project `.lake` cache. Do not override `LAKE_HOME`, `LEAN_PATH`, the package cache, or the build directory.

Before every Lake build, immediately check `/proc/meminfo` and start the build only if `MemAvailable` is at least `20971520` kB. Join the successful memory predicate directly to the Lake command with shell `&&`. If insufficient memory is available, wait 30 seconds and retry. Use the assigned target `+ValuationsBook.<CHAPTER>`; use a full `lake build` only when necessary.

A suitable guarded pattern is:

```sh
while ! awk '/^MemAvailable:/ { ok = ($2 >= 20971520) } END { exit !ok }' /proc/meminfo; do sleep 30; done && awk '/^MemAvailable:/ { ok = ($2 >= 20971520) } END { exit !ok }' /proc/meminfo && lake build +ValuationsBook.<CHAPTER>
```

Before finishing:

1. Confirm the assigned file has no occurrences of `sorry`, `admit`, `aesop`, `axiom`, or `unsafe`.
2. Run the guarded Lake target successfully.
3. Run `git diff --check` for the assigned file.
4. Remove all scratch, backup, and log files you created.

In your final response report:

- Proof completion and forbidden-token audit results.
- The exact guarded test command and its result.
- Every definition, theorem statement, or interface change, together with why it was necessary and how it parallels the book.
- Remaining compiler or linter warnings.
- Confirmation that only the assigned chapter file remains modified by your work and that temporary files were removed.
