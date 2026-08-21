# Cross-book chronological review dossier

This dossier aggregates defects found by the fresh, complete-manuscript review required by
`AUTHORING.md`. It is not a completion certificate. A finding remains **OPEN** until the missing
result is proved in Mathlib or at a chronologically valid point in this collection and every
affected consumer has been re-read after the repair.

The authoritative per-book attestations and full evidence are maintained in:

- [Books 001--064](FRESH_REVIEW_001_064.md)
- [Books 065--128](FRESH_REVIEW_065_128.md)
- [Books 129--188](FRESH_REVIEW_129_188.md)

Searches, dependency-table checks, and targeted inspections are triage only. A manuscript is not
reviewed until its ledger says that it was read from line 1 through EOF in chronological/result
order. The early targeted read of Book 151 is retained as evidence but will not count as completion
of the ordered pass until Books 129--150 have been completed.

## Open findings

| ID   | Earliest defective consumer                    | Missing or out-of-order result                                                                                                                   | Later source or affected consumers                               | Required chronological repair                                                                                                                                                                   |
| ---- | ---------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| F001 | Book 001, Section 13.7                         | Existence of systems of parameters; regular local rings have finite global dimension and finite free resolutions for finite modules              | Proved only in Books 10a/11                                      | Prove the dimension and homological statements before their first use in Book 001, or postpone every dependent assertion to the later source.                                                   |
| F002 | Book 003, Sections 15.4--15.7                  | Fontaine--Raynaud cutoff for upper ramification of finite-flat torsion                                                                           | Proved only in Book 056, Theorem 6.1                             | Leave Book 003 with only the abstract consequence of a supplied cutoff, or move/prove the cutoff before its numerical use.                                                                      |
| F003 | Book 019, Section 13.1 and Chapter 14          | Exterior-algebra calculation of the absolute etale cohomology of an abelian variety                                                              | Proved only in Book 036 using Book 024                           | Move the absolute calculation to a pre-019 source or prove it inside Book 019 before deriving the relative statements.                                                                          |
| F004 | Book 041, Chapters 11--17                      | Potential semistable reduction, Hodge base change, compactification/comparison, slope certificates, isogeny finiteness, and semisimplicity chain | Downstream height/Tate applications; no earlier complete source  | Prove each retained theorem in chronological order, or remove all claimed conditional conclusions after verifying they are unused; visible conditional interfaces are not acceptable endpoints. |
| F005 | Book 065, Section 7.2                          | Cotangent-amplitude converse: a quotient with relative cotangent complex in amplitude `[-1,-1]` is a complete intersection                       | Used by Book 065's lci converse and later deformation algebra    | Supply a rigorous degeneration/complete-intersection proof before the converse; naming the Quillen criterion is insufficient.                                                                   |
| F006 | Book 118, Section 6.2                          | Strong approximation for the quaternionic norm-one group in the exact finite-adelic form used                                                    | Consumed by Book 120 and later Shimura-curve component arguments | Replace the non-global isotropic-direction argument with a valid earlier strong-approximation theorem and propagate its exact hypotheses.                                                       |
| F007 | Book 132, Lemma 6.2 and local correction lemma | Wild two-primary quotient-stack descent and Smith form producing the unique divided Hasse-square lift                                            | Consumed by Books 133 and 147--149                               | Compute the wild Cech/group-cohomology lattice before Theorem 6.1, or use a chronologically earlier independent component/cusp calculation.                                                     |
| F008 | Book 139, Sections 6 and 14                    | Localized abelian Ihara vanishing                                                                                                                | Books 140, 174--176                                              | Prove the localized theorem at or before Book 139 for every routed spectator level, then remove the corresponding hypotheses from all consumers.                                                |
| F009 | Book 140                                       | Enhanced superspecial-node groupoid uniformization, including flags, branches, Frobenius, Hecke spans, routing, and integral normalization       | Books 174--176                                                   | Prove the datum-specific node classification in an earlier PEL/local-model volume, then reprove the comparison unconditionally.                                                                 |
| F010 | Book 157                                       | Infinitesimal recognition and algebraic cusp-effectivity for the joining/moving construction                                                     | Later potential-modularity geometry                              | Prove recognition and algebraic effectivity before the joining theorem, or remove the conditional theorem rather than presenting it as established.                                             |
| F011 | Book 168                                       | Uniform smooth-proper Hodge--Tate comparison and general finite-monodromy return-map purity                                                      | Strong all-embedding statements in Books 183--185                | Prove the comparison in Book 047 or another pre-168 source and construct the return maps with purity before Book 168.                                                                           |
| F012 | Book 174                                       | Nonbanal quotient-new injection, filtered-cofiber comparison, Cartier-switch transversality, and named-component support                         | Typed branches of Books 175--176                                 | Prove the Bockstein/primitivity, boundary, node, and support assertions before Book 174's reusable theorem, then re-audit its consumers.                                                        |
| F013 | Books 174--176                                 | Mixed sum-primitivity, product-residue comparison, coherent integral iterated switches, and joint component support                              | Several-place geometric route in Book 176                        | Insert a prior finite-set comparison theorem or prove the full product theorem inside Book 176 before any several-place conclusion.                                                             |

## Mechanical dependency evidence

The direct-prerequisite table currently has one row for each of the 190 manuscripts, no duplicate
or unknown book identifiers, and no numeric edge to the same or a later book. This proves only the
syntax and topological order of declared edges. Findings F001--F013 show why declared-edge checks
cannot substitute for reading the proofs and checking every invoked result.

## Repair and re-review rule

For each finding:

1. repair the earliest chronologically valid source;
2. remove every conditional name, imported-input label, or later-book proof dependency that the
   repair discharges;
3. update `BOOK_DEPENDENCIES.md` only after the mathematical source is real;
4. re-read every affected consumer from the repair point through EOF, and re-run its complete
   verdict if statement scope or order changed; and
5. close the finding here only when the per-book ledgers contain that evidence.
