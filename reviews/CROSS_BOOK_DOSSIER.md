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

## Consumer-contract repair log (Books 001/002)

The following statement-scope defects in Books 001 and 002 were repaired at their
chronologically valid sources. Each repair is a manuscript-level change; the affected
consumers must still be re-read from the repair point through EOF per the rule above.

- **Book 001, Section 12.6 (residue-lift extension property).** The chapter's Hensel
  machinery lifted simple residue roots only over the base ring, with residue data in
  $k$. Book 002, Section 9.2 invoked "Hensel's lemma applied in $B$" for a residue root
  living in $l$, which no earlier statement supported. Repaired by adding
  **Theorem 12.3** (henselianity of the extension valuation ring): the valuation ring of
  a finite extension of a complete discretely valued field is complete and separated for
  its maximal-adic topology, hence henselian, so simple residue roots in $l$ lift
  uniquely to $B$. Book 002 Section 9.2 now cites this theorem for both the lift and the
  uniqueness step.

- **Book 001, Section 11.7 (finite-normalization branch-correspondence data;
  normalized valuations).** The norm-valuation formula previously asked only that each
  branch be "normalized to value group $\mathbf Z$", without exposing (a) that the
  branches are those supplied by the finite normalization via Theorem 11.1 — one per
  prime above $\mathfrak m_A$, exhaustive and pairwise inequivalent up to equivalence —
  nor (b) that the coefficient $f_i$ is correct only for genuinely normalized
  representatives: a merely discrete rank-one branch differs by an unspecified positive
  factor and would need weight $f_i/\lambda_i$. Both hypotheses are now stated
  explicitly, with the normalization defect called out as a warning.

- **Book 002, Sections 7.3--7.4 (based data exposed; four consumer sites).** The
  classification and tower statements were phrased "inside a fixed separable closure",
  which admits witnesses (intermediate fields) carrying no specified valuation, while
  downstream use fixes $v_K$ once and for all. Repaired by introducing explicit based
  data $(K, v_K, k)$ — henselian rank-one discrete $v_K$, the unique extended branch on
  the chosen separable closure (Theorem 12.2, Book 1), and a fixed residue
  identification — and restating (i) Theorem 7.2, (ii) the uniqueness of $K_f$, (iii)
  the compositum/intersection laws and the maximal unramified union, and (iv) the
  Frobenius generator of $\operatorname{Gal}(K^{\mathrm{nr}}/K)$ together with the
  nonalgebraicity of its completion, all relative to the fixed based data.

- **Book 002, Section 3.3 (integral-model compatibility and tensor-product
  decomposition).** The completed tensor product is now decomposed first at the level
  of integral models,
  $\mathcal O_E\otimes_{\mathcal O_{K_0}}\widehat{\mathcal O}_{K_0}\cong\prod_w\mathcal O_{E_w}$,
  compatibly with the maps from $\mathcal O_E$ and with reduction branchwise, under the
  explicitly named finite-normalization hypothesis ($\mathcal O_E$ finite free over
  $\mathcal O_{K_0}$, supplied by separability); the field-level decomposition follows
  by inverting uniformizers.

- **Book 002, Section 8.5 (height-one monogenicity principle).** Added **Lemma 8.4**:
  for a finite algebra over a Dedekind domain, $B=A[\alpha]$ holds iff it holds after
  localization at every height-one prime. The surrounding text records precisely what
  the etale case supplies (local monogenicity of height-one localizations over
  henselian bases) and states honestly that local monogenicities do not glue without a
  compatibility input, so the global statement needs henselian/completion hypotheses or
  an independent compatibility choice.
