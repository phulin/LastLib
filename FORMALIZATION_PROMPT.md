# Book 2 Chapter Statement-Formalization Prompt

You are the sole statement-formalization worker for Chapter `{chapter_number}`, “{chapter_title},” of *Finite Extensions of Local Fields* (Book 2).

Work in `/home/phulin/LastLib-book1`. Read the complete source chapter in `books/02-finite-extensions-of-local-fields.md`, from the heading `## {chapter_number}. {chapter_title}` up to the next `##` chapter heading (or end of file). Your output is the Lean source for this chapter under:

`lean/LastLib/Book02FiniteExtensionsOfLocalFields/Chapter{chapter_number_padded}/`

and the chapter aggregator:

`lean/LastLib/Book02FiniteExtensionsOfLocalFields/Chapter{chapter_number_padded}.lean`.

Use namespace `LastLib.Book02FiniteExtensionsOfLocalFields.Chapter{chapter_number_padded}`. Create one sensibly named Lean file per numbered section, in section order, using valid Lean module-name components such as `Section01TheLocalExtensionProblem.lean`. The chapter aggregator must import every section file. A later section may import the immediately preceding section, thereby receiving the earlier section chain. Do not edit the project-wide `LastLib.lean` or any other chapter; the orchestrator will assemble the whole book after all parallel workers finish.

## Goal

Turn every substantive mathematical declaration or assertion in the assigned source chapter into an accurate, well-typed Lean declaration, so that later proof passes can replace placeholders without redesigning the interfaces. Include:

- every explicitly labeled definition, theorem, proposition, lemma, and corollary;
- displayed formulas and exact sequences that assert mathematical facts;
- mathematically substantive claims made in prose, including hypotheses, compatibility statements, examples, and warnings when they have precise formal content.

Do not translate motivation, proof strategy, historical remarks, or repeated paraphrases into redundant declarations. Keep declarations in source order. Add concise doc comments identifying the corresponding Book 2 section and explaining any modeling choice that is not obvious.

This is a statement-generation pass, not a proof pass. Theorems may end in `:= by sorry`. Definitions should have genuine bodies when the canonical construction is clear; a difficult noncomputable construction may temporarily use `by sorry`, but its declared type must accurately expose the intended object. All files must elaborate and build despite placeholders.

## Book 1 is an explicit dependency

Book 1 is already formalized in `lean/LastLib/Book01ValuationsDVRsAndCompletions/Chapter01.lean` through `Chapter12.lean`, and its mathematical source is `books/01-valuations-dvrs-and-completions.md`. Read the Book 1 material relevant to this chapter and search the existing Book 1 Lean declarations before designing an interface. Import the specific `LastLib.Book01ValuationsDVRsAndCompletions.ChapterNN` modules needed by this chapter and reuse their definitions and statements where appropriate. Prefer a Book 1 declaration or a canonical Mathlib definition over redeclaring the same notion. Do not import the project root module `LastLib`, because it will later import Book 2 and would create a cycle.

In particular, inspect Book 1 Chapter 11 (extensions and branches) and Chapter 12 (complete/henselian local fields, finite extensions, ramification/residue data, Eisenstein theory, and synthesis) whenever relevant. The fact that a Book 1 theorem still has a placeholder proof does not prevent depending on its declaration during this statement pass.

## Parallel earlier-chapter dependencies

All Book 2 chapters are being generated in parallel. Do not wait for, inspect, edit, or import another Book 2 worker's output. When the assigned chapter depends on a notion or theorem that should ultimately come from an earlier Book 2 chapter and neither Mathlib nor Book 1 supplies a suitable interface, make your best mathematically informed guess now so the assigned chapter remains self-contained and buildable.

Put such guessed interfaces near the start of the chapter (or in a chapter-local `Dependencies.lean` imported by the section files), under this exact comment form:

`-- BOOK2_DEPENDENCY_GUESS: expected from Chapter N; <what is being assumed and why>`

Keep guesses inside the assigned chapter namespace, use a distinctive but meaningful name, and give them the strongest natural type supported by the book—not `True`, an arbitrary proposition, or an assumption engineered to trivialize later statements. A guessed theorem may use `by sorry`. In the final report, list every guess and the earlier chapter expected to replace it. We will reconcile these provisional interfaces after the parallel pass.

## Mathematical and Lean quality

- Use pinned Mathlib APIs whenever possible. Search locally under `lean/.lake/packages/mathlib/Mathlib` before inventing an interface. If Mathlib already defines an object, reuse it and formalize the book's result as a theorem about that object; do not duplicate the definition.
- Model the book's actual hypotheses. Carefully distinguish finite, algebraic, separable, normal, Galois, complete, henselian, unramified, totally ramified, perfect-residue-field, finite-residue-field, and characteristic assumptions. Do not silently assume characteristic zero or residue-field finiteness.
- Preserve normalization factors in valuation, norm, and absolute-value formulas. Avoid collapsing `v_L|_K = e v_K` into literal equality of normalized valuations.
- Prefer established structures (`Algebra`, `FiniteDimensional`, integral closure, valuation subrings, local rings, residue fields, trace, norm, finite Galois groups, quotients, ideals, and filtrations) to ad hoc bundles when those structures express the statement faithfully.
- Repeating an existing theorem as a chapter-facing theorem is desirable; repeating an existing definition is not.
- Do not use `True`, vacuous implications, invented contradictory assumptions, `axiom`, `unsafe`, or other loopholes as substitutes for mathematical content.
- A source statement that is genuinely false or missing a necessary hypothesis must not be silently weakened. Add `-- SOURCE_ISSUE: <precise diagnosis and minimal correction>`, formalize the minimally corrected statement, and report it.
- Follow Mathlib naming and style conventions. Use `noncomputable section` and `open` declarations sparingly. Keep helper definitions private when they are only elaboration scaffolding rather than book concepts.
- Use Lean comments only: `/-- ... -/` for doc comments and `/- ... -/` or `-- ...` otherwise. C-style `/** ... */` comments are invalid Lean.
- Do not leave exploratory commands such as `#check`, `#print`, `#eval`, or `#reduce` in deliverable files.

## Workflow and boundaries

1. Inventory the assigned source chapter section by section and inspect relevant Book 1 and Mathlib APIs.
2. Create the chapter-local dependency interface only if needed.
3. Write all section files and the chapter aggregator. Cover the entire chapter before spending time on optional proof bodies.
4. Build the aggregator from `/home/phulin/LastLib-book1/lean` with `lake build +LastLib.Book02FiniteExtensionsOfLocalFields.Chapter{chapter_number_padded}`. Repair every elaboration error. Warnings caused by deliberate `sorry` placeholders are expected.
5. Before claiming success, force every assigned Lean source to be re-elaborated so stale `.olean` files cannot hide a late source error. From the project directory, run `find LastLib/Book02FiniteExtensionsOfLocalFields/Chapter{chapter_number_padded} -type f -name '*.lean' -exec touch {} +`, also touch the chapter aggregator, and then rerun `lake build +LastLib.Book02FiniteExtensionsOfLocalFields.Chapter{chapter_number_padded}`. Continue until this forced fresh chapter build succeeds.
6. Run `git diff --check` on files you created and audit them for malformed comments, exploratory `#check`/`#print`/`#eval`/`#reduce` commands, and forbidden loopholes (`axiom`, `unsafe`, `sorryAx`, `admit`, and vacuous `True` stand-ins). Ordinary `sorry` proof placeholders are allowed in this pass.

Edit only the assigned chapter directory and aggregator, except for temporary scratch files inside the worktree, which must be removed before finishing. Preserve all existing user changes. Do not alter Book 1 files, the book Markdown, Lake configuration, shared root imports, or other Book 2 chapters. Do not use the internet, inspect Git history, or commit.

## Final report

Report:

- every file created;
- the section-by-section declaration count and total declaration count;
- the exact successful Lake build command;
- every `BOOK2_DEPENDENCY_GUESS`, naming the expected source chapter;
- every `SOURCE_ISSUE` and its correction;
- any important source assertion intentionally not represented, with the reason;
- confirmation that Book 1 dependencies were searched and the exact Book 1 modules imported;
- confirmation that only assigned files were changed and scratch files were removed.
