# Fresh chronological review: Books 001–064

This audit applies the repository authoring rule literally: a substantive result is available only when it is present in the local Mathlib checkout or has been proved earlier in the manuscript chronology. Roadmap remarks are distinguished from facts used in proofs. Every book entry states whether I personally read the complete manuscript from line 1 through EOF during this review.

## Per-book verdicts

### Book 001 — `001-valuations-dvrs-and-completions.md`

**Verdict: FAIL — cross-book prerequisite gap.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 3119 (EOF), in chronological/result order, during this audit. I re-read lines 2001–2400 in smaller ranges after an earlier terminal rendering truncated them.

The valuation, DVR, completion, Hensel, integral-closure, and coefficient-ring arguments are developed internally. Important imported foundational claims in Chapter 13 were checked against the local checkout: Artin–Rees and Krull intersection are in `Mathlib/RingTheory/Filtration.lean`; finite-variable formal power-series rings over a Noetherian ring are covered in `Mathlib/RingTheory/MvPowerSeries/Equiv.lean`; Krull's height theorem is in `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`. However, §13.7 imports the existence of systems of parameters (line 2840) without proof, and lines 2885 and 3008 invoke the theorem that regular local rings have finite global dimension/finite free resolutions. No commutative-ring theorem supplying those latter assertions was found in the local checkout. The project proves it only later, in Book 010a, Theorem 2.4 (and again in Book 011, Chapter 14). See Cross-book finding X001 below.

### Book 002 — `002-finite-extensions-of-local-fields.md`

**Verdict: PASS.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 3030 (EOF), in chronological/result order, during this audit.

Book 002 builds its valuation-extension, finite-freeness, degree, norm/trace, inertia, unramified/Eisenstein, unit-filtration, Krasner, finiteness, and approximation results from Book 001 and proved local arguments. The explicit references at lines 737, 973, and 1883 to Book 003 concern finer different/ramification filtrations that the manuscript neither invokes nor needs for a present proof; they are roadmap boundaries rather than logical edges. Important external foundations were checked locally: weak approximation is available in `Mathlib/Analysis/AbsoluteValue/Equivalence.lean`, and separable trace-form nondegeneracy is available in `Mathlib/RingTheory/Trace/Basic.lean`. The linked table of contents matches the chapter/section order, and no backward-order, conditional-interface, notation, conclusion, or display-format defect was found.

### Book 003 — `003-ramification-theory.md`

**Verdict: FAIL — later finite-flat cutoff is used as a conditional interface.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 3153 (EOF), in chronological/result order, during this audit.

The book proves its classical local theory in order: lower groups, Herbrand/upper numbering, a detailed cyclic Hasse–Arf argument, the different and discriminant, Hilbert's formula, and Artin/Swan conductor integrality. Its hypotheses around imperfect residue fields are stated carefully. A malformed carriage-return fragment in the cyclic-subgroup summation at former line 2142 was repaired to `\text{ cyclic}` in commit `ee119fd`. Chapter 15, however, crosses from a legitimate future interface into present conditional conclusions: §15.4 assumes cutoff (15.8), explicitly says it is not proved here, and then presents (15.9)–(15.17) and numerical ceilings as results. The actual proof is only Book 056, Theorem 6.1. See X002.

## Cross-book findings

### X001 — Regular-local homological input is used in Book 001 before it is proved

- **Consumer:** Book 001, §13.7, especially lines 2840, 2885, and 3008; the conclusion repeats the finite-free-resolution consequence.
- **Later source:** Book 010a, Theorem 2.4 (regular local rings have finite global dimension), with a fuller development in Book 011, Chapter 14.
- **Needed result:** existence of systems of parameters in a Noetherian local ring, and the homological characterization/consequence that a regular local ring has finite global dimension and finite free resolutions for finite modules.
- **Why unavailable:** the local checkout supplies Krull height, Artin–Rees, Krull intersection, and Noetherianity of finite-variable power-series rings, but a search of the commutative-algebra library found no theorem proving regular-local finite global dimension or the system-of-parameters existence statement. No earlier book exists from which Book 001 could inherit these facts.
- **Recommended chronological repair:** either prove the necessary dimension and homological statements inside Book 001 before §13.7, or remove the homological assertions from Book 001 and postpone them to Book 010a. The system-of-parameters existence theorem must likewise be proved in Book 001 before the module-finite model-ring conclusion, unless that conclusion is postponed.

### X002 — Book 003 derives discriminant ceilings from Book 056's finite-flat cutoff

- **Consumer:** Book 003, §15.4, equations (15.8)–(15.11), and §§15.5–15.7, especially equations (15.15)–(15.17) and the numerical examples. The manuscript explicitly labels (15.8) a later geometric theorem, but materially substitutes it into the ramification and global-discriminant formulas.
- **Later source:** Book 056, Theorem 6.1 (Fontaine–Raynaud upper-break bound), lines 746ff; Book 056 then proves the corresponding different and global bounds.
- **Needed result:** for a finite-flat $G_K$-module killed by $\ell^n$, triviality of $G_K^u$ above $e_K(n+1/(\ell-1))-1$.
- **Why unavailable:** this is a specialized finite-flat group-scheme ramification theorem, not a Mathlib theorem and not proved in Books 001–002 or earlier in Book 003. Equations (15.9)–(15.17) are conditional consequences, not unconditional results at this chronological point.
- **Recommended chronological repair:** retain only the abstract implication “a supplied cutoff $R$ gives (15.7)” in Book 003. Move the Fontaine constants, global ceilings, and numerical applications to Book 056 after Theorem 6.1, or move/prove that theorem before Book 003.
