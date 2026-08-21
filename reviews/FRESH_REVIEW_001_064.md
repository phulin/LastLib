# Fresh chronological review: Books 001–064

This audit applies the repository authoring rule literally: a substantive result is available only when it is present in the local Mathlib checkout or has been proved earlier in the manuscript chronology. Roadmap remarks are distinguished from facts used in proofs. Every book entry states whether I personally read the complete manuscript from line 1 through EOF during this review.

## Per-book verdicts

### Book 001 — `001-valuations-dvrs-and-completions.md`

**Verdict: FAIL — cross-book prerequisite gap.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 3119 (EOF), in chronological/result order, during this audit. I re-read lines 2001–2400 in smaller ranges after an earlier terminal rendering truncated them.

The valuation, DVR, completion, Hensel, integral-closure, and coefficient-ring arguments are developed internally. Important imported foundational claims in Chapter 13 were checked against the local checkout: Artin–Rees and Krull intersection are in `Mathlib/RingTheory/Filtration.lean`; finite-variable formal power-series rings over a Noetherian ring are covered in `Mathlib/RingTheory/MvPowerSeries/Equiv.lean`; Krull's height theorem is in `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`. However, §13.7 imports the existence of systems of parameters (line 2840) without proof, and lines 2885 and 3008 invoke the theorem that regular local rings have finite global dimension/finite free resolutions. No commutative-ring theorem supplying those latter assertions was found in the local checkout. The project proves it only later, in Book 010a, Theorem 2.4 (and again in Book 011, Chapter 14). See Cross-book finding X001 below.

## Cross-book findings

### X001 — Regular-local homological input is used in Book 001 before it is proved

- **Consumer:** Book 001, §13.7, especially lines 2840, 2885, and 3008; the conclusion repeats the finite-free-resolution consequence.
- **Later source:** Book 010a, Theorem 2.4 (regular local rings have finite global dimension), with a fuller development in Book 011, Chapter 14.
- **Needed result:** existence of systems of parameters in a Noetherian local ring, and the homological characterization/consequence that a regular local ring has finite global dimension and finite free resolutions for finite modules.
- **Why unavailable:** the local checkout supplies Krull height, Artin–Rees, Krull intersection, and Noetherianity of finite-variable power-series rings, but a search of the commutative-algebra library found no theorem proving regular-local finite global dimension or the system-of-parameters existence statement. No earlier book exists from which Book 001 could inherit these facts.
- **Recommended chronological repair:** either prove the necessary dimension and homological statements inside Book 001 before §13.7, or remove the homological assertions from Book 001 and postpone them to Book 010a. The system-of-parameters existence theorem must likewise be proved in Book 001 before the module-finite model-ring conclusion, unless that conclusion is postponed.
