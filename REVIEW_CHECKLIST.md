# Textbook Review Checklist

This is the common sign-off standard for every manuscript in `books/`. A book may be reported
`READY` only after a fresh-context author or reviewer has checked every applicable item below.
The reviewer records the result in the review ledger at the end of this file. Root commits the
book only after the report is `READY` with no unresolved coverage gap.

## 1. Scope and structure

- [ ] The manuscript matches the current description in `BOOKS.md`, not an older title or scope.
- [ ] Every direct prerequisite in `BOOK_DEPENDENCIES.md` has been inspected.
- [ ] The book is one logically continuous mathematical narrative rather than a collection of notes.
- [ ] The linked table of contents is at the top and agrees exactly with the final headings.
- [ ] Every chapter and section has substantive motivation and a clear role in the overall theory.
- [ ] Complicated arguments receive proportionally deeper explanation and are not compressed at the decisive step.
- [ ] The conclusion states the mathematical package established by the book.
- [ ] There are no appendices, exercises, optional-results sections, reader tasks, planning notes, or bibliographic filler.

## 2. Mathematical correctness

- [ ] Definitions are well-typed and use consistent variance, normalization, and sign conventions.
- [ ] Every theorem states all necessary hypotheses, including characteristic, finiteness, flatness,
      separability, perfectness, coefficient, and local/global assumptions where relevant.
- [ ] Every result central to the catalog description is proved at the required depth.
- [ ] Proof strategies are explained before difficult proofs, decisive steps are explicit, and consequences are interpreted.
- [ ] Examples and counterexamples respect the stated hypotheses and calculations have been checked.
- [ ] Edge cases, exceptional primes, scalar or reducible cases, and normalization changes are handled or explicitly excluded.
- [ ] No circular argument uses a later theorem, the desired conclusion, faithfulness, component coverage,
      or a numerical equality before it has been established.
- [ ] All equation labels, internal references, diagrams, and theorem references resolve correctly.

## 3. Dependency closure

- [ ] Each substantial imported result is ordinary assumed background or is actually proved in a prior numbered book.
- [ ] For every prior-book citation, the cited result exists and its hypotheses imply the form used here.
- [ ] No theorem is lost in a gap between books: if no prior source proves the needed statement, this book proves it.
- [ ] Later books are used only for orientation, never as proof dependencies.
- [ ] External class-field-theory or Chebotarev inputs are used only where the dependency graph permits them.
- [ ] The prose never mentions Lean, Mathlib, proof assistants, code APIs, theorem identifiers, or implementation details.

## 4. Exposition

- [ ] The intended graduate reader can follow the notation and the transition from intuition to formal statement.
- [ ] New constructions are motivated by the problem they solve.
- [ ] Dense theorem-proof cataloguing has been replaced by explanatory connective prose.
- [ ] Notation is introduced before use and remains stable across chapters.
- [ ] Cross-book recollections are sufficient to make the present narrative readable without duplicating whole prior books.
- [ ] The treatment is complete enough for later formalization and is near the soft target of roughly 100 typeset pages,
      while mathematical completeness takes priority over raw length.

## 5. Format and repository hygiene

- [ ] Inline mathematics uses `$...$`; display mathematics uses `$$...$$`.
- [ ] Math delimiters, braces, environments, and code fences are balanced.
- [ ] ASCII diagrams are used where a diagram is needed; no unavailable image is referenced.
- [ ] The manuscript contains no prohibited implementation vocabulary or accidental tool output.
- [ ] Only the assigned book file was edited by the author or reviewer.
- [ ] `git diff --check -- <book-file>` passes.
- [ ] The final report includes path, word count, line count, chapter count, section count, coverage gaps,
      and an unambiguous `READY` or `NOT READY` verdict.

## Review ledger

Add one row after a fresh-context review. `READY` means every applicable item above passed; a
nonempty gap belongs in the final column and prevents sign-off.

| Book | Reviewer/worker | Commit | Verdict | Remaining gaps |
|---:|---|---|---|---|
| 1–20 | serialized fresh-context authors/reviewers | through `d15d5f0` | READY | none reported |

