# Book 1 Chapter Luna Worker Prompt

You are the sole implementation agent for `ValuationsBook/ValuationsBook/<CHAPTER>.lean` in `/home/phulin/LastLib-book1`. Use `gpt-5.6-luna` with maximum reasoning effort throughout. You are running with full filesystem access and approval policy `never`.

Work only in this worktree and edit only your assigned chapter file, except for temporary scratch files inside the worktree that you must remove before finishing. Preserve unrelated changes and do not commit. Do not inspect Git history, Git objects, reflogs, remotes, the internet, parent repositories, or completed ValuationsBook build artifacts.

Your assignment is the entire chapter, not one isolated declaration. Read the complete target Lean file and the corresponding material for Chapter `<CHAPTER_NUMBER>` in `books/01-valuations-dvrs-and-completions.md`. Treat the book as the mathematical blueprint, but verify all formal facts and exact APIs from the pinned Lean sources. Inspect Mathlib under `ValuationsBook/.lake/packages/mathlib` freely and use declarations from earlier chapter files. Within the assigned chapter, a proof may use only declarations occurring textually before it; never use a later declaration to prove an earlier one.

Prove every `sorry` or `admit` in the assigned file that can be proved from its statement and the permitted earlier declarations. Statements are immutable during this proof pass: do not change a declaration's kind, name, namespace, binders, assumptions, typeclasses, result type, section-variable behavior, attributes, or imports, and do not replace it with an easier declaration. Do not introduce axioms, unsafe declarations, contradictory artificial assumptions, diagnostic-suppression tricks, or any other proof or kernel-checking loophole. The `aesop` tactic is banned: do not add or invoke it, and replace every existing `aesop` invocation in the assigned file with an explicit proof using concrete Mathlib lemmas and ordinary focused tactics.

## Chapter workflow

1. Read and understand the complete chapter file and its corresponding book material. Inventory every `sorry`, `admit`, and existing `STATEMENT_NEEDS_UPDATE` marker.
2. Establish the local context of each target before proving it: imports, namespaces, section variables, notation, local instances, source definitions, and all relevant earlier declarations.
3. Make a whole-file proof-writing pass before the first build. Write a coherent proof attempt for every target that appears mathematically sound; do not compile after each speculative identifier.
4. Build the actual chapter module and repair errors in batches. Address the first relevant error, verify any uncertain API from source, make a meaningful correction, and rebuild.
5. Continue through the entire chapter. One difficult declaration must not prevent you from proving independent later declarations.
6. After the last source edit, run a fresh successful guarded chapter build. Any edit invalidates previous build results.

## Reconstruct the exact API

Search narrowly in the assigned chapter, explicit earlier chapter files, and pinned Mathlib sources. Inspect actual declarations, definitions, exports, constructors, and structure fields to confirm namespaces, argument order, explicit and implicit parameters, coercions, codomains, and typeclass assumptions. Do not trust a theorem name recalled from memory until you have found its declaration.

If Lean reports an unknown constant or invalid field projection, stop editing and inspect the declaration or export that provides the operation. A theorem exposed with `export` is not automatically a field projection. Such an error is a proof/API problem, not evidence that the statement needs updating.

Match exact underlying types before applying an API, especially quotient types, units, `WithZero`, `WithTop`, `Multiplicative`, and additive versus multiplicative equivalences. Do not add stronger assumptions or silently reinterpret a target.

## Prefer canonical proofs

For each declaration, check in order:

1. definitional equality or `rfl`;
2. an exact earlier theorem;
3. standard rewriting or simplification;
4. a canonical constructor or library equivalence;
5. only then, lower-level unfolded infrastructure.

For existential, `Nonempty`, equivalence, structure, and class goals, construct the canonical witness first and discharge only the remaining fields. Useful recurring patterns include:

- For a mapped-ideal claim under a ring equivalence, use the existing equivalence as the witness, transport the maximal ideal using bijectivity or surjectivity, then normalize the named ideals.
- For an equivalence between quotient rings, normalize the source and target ideals, identify an ideal as the kernel of a known surjective homomorphism, and compose quotient/kernel equivalences before defining manual forward and inverse maps.
- For a negated structural property, assume it and apply its simplest universal consequence to a canonical low-complexity object, then transport through an invariant. Try a low power or parity obstruction before constructing a custom polynomial or structure.

Use local `have`, `let`, and genuine local instances inside proof bodies as needed. Do not add global helper declarations merely to evade a target, and do not repeatedly compile guesses at unverified identifiers.

## Statements that genuinely need correction

Use `STATEMENT_NEEDS_UPDATE` only when a declaration is concretely false, malformed, inaccurately formalizes the book, or is impossible from its stated assumptions after checking the actual definitions and permitted APIs. A failed search, guessed theorem name, tactic failure, coercion mistake, timeout, resource problem, or warning is not sufficient.

When this high bar is met:

1. Leave the declaration statement unchanged.
2. Leave its existing placeholder proof in place, or restore only that proof body to `by sorry` if necessary to keep the chapter elaborating.
3. Add a comment immediately above the declaration in this exact form:

   `-- STATEMENT_NEEDS_UPDATE: <precise diagnosis and minimal proposed correction>`

The comment must identify the concrete mathematical or elaboration obstruction and describe the smallest statement change that resolves it. If a binder or assumption is missing, name it precisely. If the conclusion is wrong, state the minimally corrected conclusion. Never add the conclusion as a hypothesis, weaken a valid claim merely to make compilation pass, or edit the statement during this pass.

Continue proving all independent declarations in the rest of the chapter. The marker is an actionable in-file review finding, not a reason to stop the chapter-wide task. Do not add the marker to declarations that are merely hard or whose proof is unfinished; those remain ordinary unresolved proof obligations and must be distinguished clearly in the final report.

## Compilation and resource rules

Use only Lake builds for compilation and testing. Never run `lake env lean`, raw `lean`, another compiler, a scratch module, or an alternate target. Run builds from `/home/phulin/LastLib-book1/ValuationsBook` so all workers share the project `.lake` cache. Do not override `LAKE_HOME`, `LEAN_PATH`, the package cache, or the build directory.

Before every Lake build, immediately check `/proc/meminfo` and start the build only if `MemAvailable` is at least `20971520` kB. Join the successful memory predicate directly to the Lake command with shell `&&`. If insufficient memory is available, wait 30 seconds and retry. Build the assigned target `+ValuationsBook.<CHAPTER>`; use a full `lake build` only when necessary.

A suitable guarded pattern is:

```sh
while ! awk '/^MemAvailable:/ { ok = ($2 >= 20971520) } END { exit !ok }' /proc/meminfo; do sleep 30; done && awk '/^MemAvailable:/ { ok = ($2 >= 20971520) } END { exit !ok }' /proc/meminfo && lake build +ValuationsBook.<CHAPTER>
```

A successful build may emit warnings for remaining placeholders, plus unrelated linter, deprecation, unused-variable, unused-simp-argument, unnecessary-`simpa`, `letI`, reducibility, or style warnings. Do not repair unrelated declarations merely to silence them.

## Completion checks

Before finishing:

1. Run a fresh guarded build after the final edit and confirm the assigned chapter target succeeds.
2. Confirm the assigned file contains no `admit`, `aesop`, `axiom`, `unsafe`, `sorryAx`, or equivalent loophole.
3. Account for every remaining `sorry`: each must be either attached to a precise `STATEMENT_NEEDS_UPDATE` marker or reported as an unresolved proof obligation. Never claim completion merely because the file builds with placeholders.
4. Inspect the diff to verify that declaration headers and imports are unchanged and that only proof bodies and `STATEMENT_NEEDS_UPDATE` comments were edited.
5. Run `git diff --check` for the assigned file.
6. Remove all scratch, backup, and log files you created.

## Final report

Report one chapter-level summary, not a statement-by-statement JSON value. Include:

- The declarations proved and the remaining placeholder count.
- Every declaration marked `STATEMENT_NEEDS_UPDATE`, with its concrete diagnosis and minimal proposed correction.
- Any ordinary unresolved proof obligations that are difficult but do not justify a statement update.
- The exact guarded build command and its result, run after the final edit.
- Forbidden-token and `git diff --check` results.
- Remaining compiler or linter warnings.
- Confirmation that declaration headers and imports were preserved, only the assigned chapter file was modified by your work, and temporary files were removed.
