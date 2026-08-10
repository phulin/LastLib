# Book 1 Chapter Statement-Review and Repair Prompt

You are the sole statement-review worker for Chapter `{chapter_number}`, “{chapter_title},” of *Valuations, DVRs, and Completions* (Book 1).

Work in `/home/phulin/LastLib-book1`. The complete current prose chapter and complete current Lean chapter are embedded below in this initial prompt. Treat those embedded blocks as the authoritative review snapshot. You may inspect pinned Mathlib and earlier Book 1 chapters to validate interfaces and dependencies, but do not substitute an older copy of the prose or Lean chapter for the embedded contents.

Your assigned Lean file is:

`lean/LastLib/Book01ValuationsDVRsAndCompletions/Chapter{chapter_number_padded}.lean`

## Goal

Mutate the assigned Lean file so its declarations faithfully and accurately represent the updated prose chapter and are mathematically provable from their hypotheses, Mathlib, and declarations available earlier in Book 1 source and Lean order. This is primarily a statement-review and statement-repair pass. Do not spend substantial time repairing proof bodies.

Review the entire assigned chapter, section by section. Account for:

- every labeled definition, theorem, proposition, lemma, and corollary;
- displayed formulas, exact sequences, equivalences, and compatibility statements;
- precise mathematical assertions in prose, including hypotheses, examples, counterexamples, normalization conventions, and warnings;
- every additional mathematical lemma required by a plausible proof of those declarations, including basic equivalences and bridge facts that the prose leaves implicit.

Do not formalize motivation, proof sketches, historical remarks, or repeated paraphrases. Add a missing declaration when the prose makes a substantive mathematical assertion that has no adequate Lean counterpart. Preserve useful existing declarations even when the prose has been reorganized, unless they are false, misleading, duplicative, or depend circularly on later material.

Source-to-Lean coverage is only one half of this review. Perform a proof-readiness audit of every
principal declaration: read its informal proof or proof sketch, locate the exact earlier LastLib and
Mathlib APIs that a Lean proof can use, and trace a plausible dependency route to the conclusion.
The chapter is not statement-complete if that route needs a genuine intermediate mathematical fact
whose declaration is absent. Add such facts even when they are not independently labeled in the
prose. Pay particular attention to `↔` lemmas and equivalences between informal and canonical Lean
formulations; constructor/eliminator and extensionality facts; coercion, membership, map,
restriction, and normalization lemmas; closure and functoriality results; and short bridges between
successive proof steps. Do not assume a proof agent should rediscover and locally reprove the same
missing interface inside every theorem.

Before adding anything, search for a canonical existing theorem. Add a chapter-facing bridge only
when it supplies a genuinely missing or materially more usable interface. Every added support lemma
must have the weakest natural hypotheses, precede all of its users, and be independently provable
from earlier declarations. Reject helpers that restate a target, include its conclusion among their
assumptions, depend on a later result, or conceal a circular proof. An accurate, useful support lemma
should not be removed merely because the informal source regards it as obvious or mentions it only
inside a proof.

## Review standard

For every declaration, compare it with the embedded prose and check:

- quantifier scope and implication direction;
- all finiteness, separability, normality, Galois, completeness, henselianity, rank-one, ramification, residue-field, and characteristic hypotheses;
- domains, codomains, coercions, indexing conventions, and normalization factors;
- whether the conclusion has the intended mathematical strength;
- whether it is actually provable without smuggling the conclusion into a hypothesis;
- whether its dependencies precede it in both the source exposition and Lean import/text order.

Search pinned Mathlib and existing earlier LastLib declarations before inventing an interface. Prefer canonical definitions and earlier results over duplicated notions. Never import a later Book 1 chapter, the project root `LastLib`, or anything creating a cycle.

Make the smallest principled statement correction. Add genuinely necessary hypotheses, repair objects or quantifiers, correct conclusions, and add missing declarations. Do not weaken a correct statement merely because its proof is difficult.

Never make a declaration provable by replacing it with `True`, a tautology, an artificial contradiction, the conclusion as a hypothesis, a duplicate/later result, an `axiom`, an `unsafe` declaration, `sorryAx`, or any similar loophole.

Minor omitted side conditions, implicit conventional hypotheses, representation choices, and gaps caused by Lean or Mathlib interfaces are formalization issues. Fix them directly in the Lean declaration and explain the repair in the final report; do not mark them as source issues. This includes adding routine positivity, nonzero, finiteness, typeclass, or library-API hypotheses needed to state or prove the intended mathematics precisely.

Reserve `SOURCE_ISSUE` for a substantive defect in the mathematical source itself: a claim that is genuinely false under its natural conventions, internally contradictory, or materially different from any true statement after routine formalization details are supplied. In that exceptional case, place this comment immediately above the minimally corrected declaration:

`-- SOURCE_ISSUE: <precise diagnosis and minimal correction>`

If there is reasonable doubt whether a problem belongs to the prose or merely to its formal expression, treat it as a formalization issue: repair the Lean declaration without a `SOURCE_ISSUE` marker and report the change.

## Mutation and proof policy

Edit the assigned Lean file directly. Do not edit the prose, `REVIEW_PROMPT.md`, any other chapter, project configuration, or the Mathlib checkout. Do not create scratch files, inspect Git history, commit, or use the internet.

Keep existing proofs when they still elaborate against faithful statements. When a necessary statement repair invalidates a proof and a short robust repair is not immediate, replace only that proof body with `by sorry`; accurate interfaces take priority in this pass. Existing `sorry` placeholders may remain. Do not distort a statement to preserve a proof.

Do not run Lake, raw Lean, or another compiler. Run `git diff --check` on the assigned file. Before
finishing, verify that you changed only the assigned file. The coordinator will merge accepted
changes and run the targeted build through its serialized main-worktree build queue.

Perform the final review workflow in this order:

1. Check source coverage and mathematical fidelity.
2. Check proof readiness and missing reusable interfaces.
3. Make the smallest principled statement/interface repairs.
4. Obtain clean diagnostics for the assigned file.
5. Audit imports. Focused imports may be added freely and do not need to be minimized. Replace the
   exact umbrella imports `import Mathlib` and `import LastLib`, and replace any broad aggregator
   import with focused Mathlib or stable LastLib modules. Do not add later-chapter or cyclic edges.
6. Run `git diff --check`; the coordinator runs the post-merge targeted build.

## Final report

Report:

- the assigned file and whether it was changed;
- a section-by-section source-to-Lean coverage summary;
- every declaration added, removed, or materially corrected;
- every proof-support lemma added or repaired beyond the explicitly labeled source declarations, and the proof dependency it enables;
- every proof newly replaced by `sorry` because of an interface repair;
- every `SOURCE_ISSUE` and its correction;
- any substantive source assertion intentionally not represented and why;
- dependency-order findings;
- `git diff --check` result and confirmation that the coordinator owns the post-merge build;
- confirmation that the complete embedded prose and Lean contents were reviewed and only the assigned file was changed.

## Embedded authoritative source chapter

```markdown
{source_chapter_contents}
```

## Embedded current Lean chapter

```lean
{lean_chapter_contents}
```
