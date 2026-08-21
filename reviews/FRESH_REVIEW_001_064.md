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

### Book 004 — `004-adeles-and-ideles.md`

**Verdict: PASS.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 3000 (EOF), in chronological/result order, during this audit.

The number-field preliminaries, Minkowski/class-group argument, restricted-product topology, additive and multiplicative compactness, Dirichlet unit theorem, ray quotients, adelic norm, and additive self-duality are proved before use. The later reciprocity theorem and cyclic Hasse norm theorem are clearly labeled as future boundary statements and are not used in a proof or conclusion of the book. The linked contents agree with all sixteen chapters and their internal order; no conditional interface, forward proof dependency, notation defect, or malformed display was found.

### Book 005 — `005-local-class-field-theory.md`

**Verdict: PASS.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 4021 (EOF), in chronological/result order, during this audit.

The manuscript proves its local prerequisites in dependency order: norm openness and Hilbert 90 precede cyclic algebras; the local Brauer invariant and complete-resolution/Tate–Nakayama argument precede finite reciprocity; finite reciprocity precedes the independent Herbrand norm-filtration calculation; and that calculation precedes Lubin–Tate cofinality, existence, infinite reciprocity, ramification compatibility, and the character dictionary. In particular, Lemma 6.4 uses the already established finite Artin isomorphism only for the total unit-norm index and proves the filtered comparison separately, so Theorem 8.1 is not circular. The Book 003 inputs (Hasse–Arf integrality, trace ideals, and Herbrand transitivity/quotients) occur only after those results. Important ambient claims were checked in the local checkout: Hilbert 90 is in `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`, Tate cohomology infrastructure is in `Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean`, Brauer-group definitions are in `Mathlib/Algebra/BrauerGroup/Defs.lean`, and the finite-division-ring theorem is in `Mathlib/RingTheory/LittleWedderburn.lean`. The linked contents match all twelve chapters and sections, and no forward proof dependency, conditional interface, notation, conclusion, or malformed-display defect was found.

### Book 006 — `006-global-class-field-theory.md`

**Verdict: FAIL — the rank-one Tate–Sen theorem rests on an asserted quantitative homotopy.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 5856 (EOF), in chronological/result order, during this audit.

The global class-field-theory core is ordered carefully: the idelic inequalities precede the Brauer localization sequence and principal reciprocity; finite degree-one duality precedes character existence; the regular absolute idèle-class construction precedes the global fundamental class; and reciprocity precedes ray fields, norm principles, and infinite completion. Roadmap boundaries are generally explicit, and the linked contents match all twelve chapters and sections. Chapter 11.5, however, proves a further rank-one Hodge–Tate-to-local-algebraicity theorem and then uses it in the ℓ-adic character discussion. The crucial “Finite Ax–Sen estimate” at lines 5068–5120 gives only a verbal ramification-cluster prescription, and lines 5122–5129 then assert compatible degree-1/degree-2 bar homotopies with the same uniform valuation loss without constructing their operators or verifying the cochain identities and bounds. Those homotopies are immediately used to prove `H^1(H,\mathbf C_\ell)=0`, coefficient descent, decompletion, the Sen operator, and Lemma 11.1. No earlier book or local Mathlib result supplies this missing quantitative Tate–Sen input. See X003.

### Book 007 — `007-analytic-foundations-for-odlyzko-poitou-bounds.md`

**Verdict: PASS.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 2374 (EOF), in chronological/result order, during this audit.

The proof chain is chronological and self-contained above its declared analytic foundations: Minkowski supplies the geometric baseline; ideal Euler products precede the theta/Poisson continuation; the functional equation and internally constructed genus-one product precede the zero count; those estimates precede the explicit formula; strip or GRH positivity precedes the root-discriminant inequalities; and directed rational enclosures precede every finite cutoff. The local checkout supplies the important named analytic inputs: Minkowski's convex-body theorem is in `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean`, Poisson summation is in `Mathlib/Analysis/Fourier/PoissonSummation.lean`, Jensen's formula is in `Mathlib/Analysis/Complex/JensenFormula.lean`, Borel–Carathéodory is in `Mathlib/Analysis/Complex/BorelCaratheodory.lean`, and the vertical-strip Phragmén–Lindelöf principle is in `Mathlib/Analysis/Complex/PhragmenLindelof.lean`. Book 004 supplies the ideal-class and Dirichlet-unit facts used in the theta unfolding. The linked contents match all sixteen chapters and sections, and no conditional interface, forward proof dependency, malformed display, or uncertified numerical conclusion was found.

### Book 007a — `007a-arithmetic-spectral-sequences-and-derived-cohomology.md`

**Verdict: PASS after local chronological repairs.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 1450 (EOF), in chronological/result order, during this audit.

The manuscript builds cones, localization, truncations, K-injective and K-flat criteria, bounded and unbounded replacements, derived operations, filtered-complex convergence, hypercohomology, Leray and Hochschild–Serre, products, and base-change comparison in dependency order. Its single explicitly imported foundation—Grothendieck abelian categories have enough injectives—is genuinely available in `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean`, including the same generating-monomorphism and small-object argument summarized in §1.2; the canonical derived-category t-structure is available in `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean`. The manuscript itself proves the stronger replacement statements it needs, including the presheaf-projective construction of arbitrary K-flat resolutions and the exact-countable-product hypothesis for unbounded K-injective resolutions. Two forward-proof references were repaired locally: §2.5 no longer appeals to Chapter 3 injective replacements to establish t-structure orthogonality, and §11.1 now states bounded-below cohomology directly and cites the already proved §§3.4–3.5 replacements instead of future §12.3. The compact linked contents are accurate and useful despite omitting individual subsection links. No missing cross-book prerequisite, unresolved conditional interface, notation defect, or malformed display remains.

### Book 007b — `007b-quasi-coherent-cohomology-on-schemes.md`

**Verdict: PASS after local proof and cross-reference repairs.**

**Full-read attestation:** I personally read the complete original manuscript from line 1 through line 2545 (then EOF), in chronological/result order, during this audit, and reviewed the inserted local repair text; the repaired manuscript ends at line 2574.

The dependency chain is chronological: unimodular Čech exactness supplies the affine dictionary; the affine dictionary and independently constructed flasque/Godement machinery supply Serre affine vanishing; affine vanishing then supplies the previously deferred extension-closure and the finite affine Čech model; that model precedes higher direct images, base change, colimits, Grothendieck vanishing, and the complete projective-space computation; the final chapter proves Hilbert syzygy and generic freeness before presenting their spreading-out interface. Commit `1f951a6` had already moved extension-closure after affine vanishing. This pass repaired a false §3.3 claim that $j_!\mathcal O_U$ on the spectrum of a DVR was the kernel of $\mathcal O_X\to i_*(R/\pi)$ and had nonzero $H^1$; the kernel is instead the quasi-coherent ideal $\widetilde{\pi R}$, so the asserted sequence supplied no such conclusion. It also replaced the nonexistent synthesis citation “Theorem 2.8” by Corollary 3.10. The prime-filtration input used in the generic-freeness proof was not found as a packaged local theorem, so it is now proved immediately before Theorem 7.6 from maximal annihilators and noetherianity; Noether normalization itself is available in `Mathlib/RingTheory/NoetherNormalization.lean`, and flatness of noetherian adic completion is available in `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`. The fully linked contents match all chapters and sections. No cross-book dependency gap, unresolved conditional interface, notation defect, or malformed display remains.

### Book 008 — `008-ample-line-bundles-hilbert-polynomials-and-symmetric-powers.md`

**Verdict: FAIL — normalization finiteness is imported from later excellence theory, and the integral Gotzmann persistence proof has an unresolved syzygy gap.**

**Full-read attestation:** I personally read the complete original manuscript from line 1 through line 3026 (then EOF), in chronological/result order, during this audit, and reviewed the local repair text; the repaired manuscript ends at line 3032.

The early projective and cohomological chain correctly uses Books 7a–7b: relative Proj, projective bundles, ampleness, Serre vanishing, finite Čech models, relative finiteness, Hilbert polynomials, and faithfully flat module/ideal descent are developed before their routine consequences. Two local chronology/citation defects were repaired: the nonexistent Book 7b “Theorem 2.8” citation now points to Theorem 2.7 and Corollary 3.10, and the proof that composites of projective or quasi-projective morphisms retain that property now occurs in §4.5 after the Serre generation criterion it uses, rather than in §3.2. The linked contents accurately cover all fourteen chapters. Two substantive gaps remain. First, §9.1's finite-normalization lemma treats the inseparable case in a single “finite $p$-basis/bounded lattice” sentence, although the local checkout proves the finite integral-closure theorem only for finite separable extensions of a Dedekind domain; Book 010a later states the universally Japanese theorem intended to supply the missing arbitrary-characteristic finiteness, but X006 shows that its proof is also incomplete. Second, Theorem 12.A's claimed complete Macaulay–Gotzmann proof never proves the decisive assertion at lines 2453–2465 that its “owner” overlaps generate every syzygy and recursively give a linear resolution; the later vector-space persistence, filtered marked-basis lemma, finite-support lemma, incidence construction, and Hilbert representability all depend on precisely that assertion. No local Mathlib theorem supplies Macaulay/Gotzmann or Hilbert-scheme representability. See X004 and X005.

### Book 009 — `009-divisors-riemann-roch-and-duality-on-relative-curves.md`

**Verdict: FAIL — its projectivity and duality package materially inherits Book 008's missing arbitrary-characteristic normalization-finiteness theorem.**

**Full-read attestation:** I personally read the complete original manuscript from line 1 through line 3691 (then EOF), in chronological/result order, during this audit, and reviewed every inserted repair; the repaired manuscript ends at line 3718.

The divisor, degree, residue, absolute and relative duality, nodal-dualizing, completed-node, Riemann–Roch, perfect-pushforward, and Abel-map arguments otherwise form an explicit proof chain rather than a list of standard interfaces. Three local order/exposition defects were repaired. The introductory list no longer cites nonexistent Book 7b Theorem 2.8. Proposition 3.1 now proves, using the principal ideal theorem and the embedding-dimension definition, that the quotient by the first member of a two-dimensional regular system of parameters is regular of dimension one; this closes the formerly asserted step in its direct Koszul/global-dimension argument. Finally, §§8.5–8.6 now label their duality-dependent residue arguments as unavailable previews, and new §9.5 promotes Theorems 8.8–8.9 only after Theorem 9.1, finite trace (9.8), and the smooth identification in §9.4 have all been proved; the former §9.5 is §9.6 and the linked contents were updated. The Book 021 references in §§10.4–10.5 concern only the stronger étale-local node chart: Book 009 proves the completed model it actually uses and explicitly excludes the later chart from its conclusions, so those references are roadmap rather than proof edges. The symmetric-power and finite-length-divisor uses are supplied by Book 008's direct symmetric-power construction and do not consume its later Gotzmann/Hilbert-scheme gap X005.

The remaining failure is X004. Lemma 9.1A begins its proof of projectivity of every proper Cohen–Macaulay curve by taking the finite normalization of each reduced component “by Book 8”; Lemma 9.2A again uses the finite normalization of an arbitrary reduced geometric fiber to prove fiberwise ampleness. Absolute curve duality, relative curve duality, Stein factorization/proper finiteness as developed here, and the later Riemann–Roch/Serre-duality package all depend on those projective embeddings. For inseparable function-field extensions, that finiteness is neither proved in Books 001–008 nor available in the local Mathlib checkout; Book 010a is the first intended Japanese/excellence source, but its own proof has the gaps recorded in X006. See X004.

### Book 010 — `010-faithfully-flat-descent-in-algebraic-geometry.md`

**Verdict: PASS.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 2455 (EOF), in chronological/result order, during this audit.

The manuscript keeps its three target categories distinct and proves each conclusion before using it: faithful exactness and the Amitsur complex precede effective module descent; finiteness/flatness/projectivity precede algebra, affine-scheme, and quasi-coherent descent; full faithfulness and the diagonal method precede the table of local properties; and the arbitrary-fpqc result is deliberately only an equalizer sheaf unless an affine, finite, stable-affine, quasi-affine, or compatibly polarized scheme criterion has been proved. The surjective-étale quotient construction proves its representable diagonal and atlas rather than assuming that every fpqc equalizer is algebraic. Its separated locally-quasi-finite effectivity argument legitimately uses Zariski's Main Theorem, available in the local checkout at `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`; the constructible-topology input is developed in `Mathlib/Topology/Spectral/ConstructibleTopology.lean`. The local checkout also confirms the algebraic backbone in `Mathlib/Algebra/Category/ModuleCat/Descent.lean`, `Mathlib/RingTheory/Flat/FaithfullyFlat/Descent.lean`, and the morphism-property results in `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`. Chapter 12 gives a complete invariant-norm/stable-minor proof of the finite-flat free-action quotient, including arbitrary base change, before torsors and subgroup quotients consume it. The Book 008 Hilbert-scheme discussion in §16.3 is a conditional moduli workflow, not a representability theorem proved or consumed here, so X005 is not a Book 010 dependency. The linked contents match all seventeen chapters and sections; no forward proof edge, conditional conclusion, notation defect, malformed display, or missing pedagogical bridge was found.

### Book 010a — `010a-excellent-rings-and-formal-fibers.md`

**Verdict: FAIL — the final Japanese and excellence packages use three expressly unproved commutative-algebra inputs.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 3399 (EOF), in chronological/result order, during this audit.

The manuscript gives substantial internal developments of regular-local homological algebra, geometric regularity, regular homomorphisms, formal smoothness, formal fibers, $G$-rings, $J$-$2$, and the finite-$p$-degree version of the excellence package. Its scope boundary for fields of infinite $p$-degree is explicit and honest, and the two formally smoothness results in §10.4 are genuinely unused. The dependency audit nevertheless fails at a different, explicitly admitted boundary. Section 1.2 lists Cohen–Macaulay/equidimensionality facts and Serre's reducedness/normality criteria as free background; §10.4, lines 3359–3365, additionally confirms that those facts and a finite-extension inseparability reduction are used without proof. They are not cosmetic: the Cohen–Macaulay facts carry Proposition 10.2 and thus universal catenarity and Theorems 10.5–10.7; the field-extension reduction starts Lemma 9.3 and hence the Japanese/Nagata chain through Corollary 9.9; and Serre's criteria carry normality and reducedness transfers throughout Chapters 3, 4, 9, and 10. Searches of the local checkout for Cohen–Macaulay, equidimensional, and Serre-condition results found no supplying theorem (the sole relevant `equidimensionality` hit is a comment saying the hypothesis cannot be assumed), and Books 001–010 do not prove these inputs. Consequently Book 010a does not yet close X004 merely by naming the missing excellence theorem. See X006.

### Book 011 — `011-normalization-and-regular-models-of-arithmetic-curves.md`

**Verdict: FAIL — it imports Book 010a's incomplete excellence package and uses its own final local-algebra chapter before that chapter proves the required results.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 3859 (EOF), in chronological/result order, during this audit.

The affine normalization, gluing, model closure, blowup charts, base-change warnings, and hypotheses separating normal, regular, smooth, proper, and projective geometry are presented carefully. Chapter 8 also attempts a full proof of excellent-surface resolution rather than naming resolution as a black box: the finite-differential/exterior-trace branch, rational-singularity reduction, formal-arc termination, and completion descent are all stated before Theorem 8.1 is discharged. The delicate degree-$p$ height-one step in Lemma 8.5 was checked against the local ramification/inertia infrastructure: `Mathlib/RingTheory/RamificationInertia/Basic.lean` does supply the equality between finite rank and the ramification-index/inertia-degree sum in the finite-integral setting, so the manuscript's two cases are not an omitted defect case. Likewise, the Rees depth theorem abbreviated in Theorem 14.3 is genuinely available in `Mathlib/RingTheory/Depth/Rees.lean`.

Two chronological failures nevertheless remain. First, Theorem 3.2 imports every substantive normalization, completion, openness, and base-excellence clause from Book 010a. Those clauses inherit X006, and they feed Theorem 3.3 and virtually every normalization/model/resolution theorem from Chapters 6–12. Book 011 therefore cannot serve as a repaired source for X004. Second, the manuscript itself says at the opening of Chapter 14 that earlier chapters used local algebra “on credit.” Proposition 4.2, the Cartier-divisor assertions in Chapters 5, 9, and 11, Proposition 11.0's intersection theory, and the contraction/factorization/minimal-model results all use regular-local factoriality from Theorem 14.43 and Corollary 14.44 before either is proved. The local checkout explicitly still marks “regular local rings are regular” as a TODO in `Mathlib/RingTheory/RegularLocalRing/Defs.lean`, and no theorem supplying regular-local factoriality was found there; Books 001–010 do not prove it. Proposition 4.1A closes several depth and finite-resolution needs early, but does not prove factoriality, so it does not repair this edge. See X007.

### Book 012 — `012-blowups-and-intersection-theory-on-arithmetic-surfaces.md`

**Verdict: FAIL — its regular-surface calculations are sound conditional on a supplied regular model, but its existence, comparison, and Cartier interfaces inherit X006 and X007.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 1816 (EOF), in chronological/result order, during this audit.

The manuscript's independent numerical core is chronological and explicit: Rees algebras and affine blowup charts precede total/strict transforms; regular-point blowups precede local length intersections; restriction degrees precede the projection formula; those formulas precede the point-blowup calculus, adjunction, the weighted-Laplacian identity, fiber negativity, and rational vertical corrections. Residue-field degrees and the distinction between vertical integer intersections and horizontal line-bundle data are handled consistently. The linked contents match all fifteen chapters and sections, and no malformed display or independent notation defect was found.

The global package is not yet available unconditionally. The standing convention that every Weil divisor on a regular surface is Cartier imports Book 011's late Theorem 14.43, so X007 underlies Chapters 7–15 even where the later calculations themselves are correct. Finite normalization in the local Bézout argument and after ramified base change, and the projective surface-resolution, contraction, and common-regular-resolution results repeatedly imported from Book 011, inherit X006 through Book 011's Theorem 3.2. In particular Theorem 15.1(9) uses common regular resolutions to assert model independence, while clauses (10)–(11) directly package the unavailable resolution/contraction/factorization interfaces. Book 012 therefore adds no new independent cross-book defect, but it is a concrete consumer of X006 and X007 and cannot be marked PASS until those earlier edges are repaired.

### Book 015 — `015-coherent-cohomology-in-proper-families.md`

**Verdict: FAIL — its dual-abelian-scheme and abelian-cohomology conclusions require unproved Hilbert, cube/isogeny, and Fourier--Mukai inputs.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 1515 (EOF), in chronological/result order, during this audit.

The general coherent-cohomology spine is carefully ordered: bounded finite complexes precede proper finiteness, the derived base-change morphism precedes the exact base-change criterion, flattening stratification and cohomological flatness precede their applications, and relative duality precedes the Picard construction for smooth projective curves. Book 008 already proves the Fitting-ideal flattening theorem used in §6.3, and its symmetric-power construction independently supplies the curve Picard argument in §10.3; those portions do not add a new dependency defect. The linked contents match the twelve chapters and their sections, and no malformed display or notation defect was found.

Chapter 11 is not discharged, however. The uniform divisor construction in §6.4 and the dual representability proof in §11.2 use Book 008's fixed-polynomial Hilbert scheme and therefore inherit X005. More seriously, the proof of the cube lemma at lines 1124–1137 merely says that coordinate-plane trivializations extend by applying rigidity successively; it neither constructs those extensions nor proves their compatibility. Lines 1139–1150 then assert, without the required Hilbert/Picard equations and isogeny argument, that the algebraically trivial locus is represented, every class lies in the image of `\phi_L` after finite extension, the fiber length is locally constant, and hence the map is finite locally free. No earlier book or local Mathlib theorem supplies the theorem of the cube or dual abelian representability. See X008.

The exterior-algebra proof in §11.3 has an independent gap. Lines 1182–1195 assert that formal functions identifies the completed Poincare direct image with the Koszul complex, that the infinitesimal connecting maps are exterior multiplication, that acyclicity away from the identity upgrades the completed calculation to the global quasi-isomorphism `Rq_*\mathcal P\simeq e_*\mathcal N[-g]`, and that its derived identity fiber gives the cup-product algebra. These are the substantive Poincare/Fourier--Mukai calculation, not consequences of formal functions alone, and none is proved earlier or present in the local checkout. The relative finite-local-freeness and base-change conclusions at lines 1204–1210 therefore do not follow. See X009.

### Book 016 — `016-semistable-curves-dual-graphs-and-component-groups.md`

**Verdict: FAIL — the graph calculations are sound, but their geometric realization inherits the unresolved curve, Hilbert, excellence, and factoriality prerequisites.**

**Full-read attestation:** I personally read this manuscript from line 1 through line 1368 (EOF), in chronological/result order, during this audit.

The combinatorial development is explicit and internally chronological: normalization/conductor gluing motivates the geometric dual graph; chain groups precede Laplacians and critical groups; the cycle lattice and integral length pairing precede subdivision, discriminants, Smith-form examples, base-change scaling, harmonic finite maps, and correspondence actions. The two presentations of the component group agree integrally, not merely after tensoring with `\mathbf Q`, and loops, nonsplit orientation reversal, residue degrees, and saturation are treated consistently. The linked contents match all fifteen chapters and sections, and the sole Book 021 reference at line 178 is expressly excluded from the current conclusions, so it is a roadmap boundary rather than a forward proof edge.

The geometric half is nevertheless conditional on earlier failures. The completed node model and relative dualizing/conductor package imported from Book 009 at lines 147–178 and 218–224 lie downstream of X004. Section 9.1's new reducible Picard representability argument uses the fixed-polynomial Hilbert scheme at lines 731–742 and therefore consumes X005; its quotient then feeds every separated-model and component theorem from §9.3 onward. The regular-model resolution/common-domination inputs used at lines 778–789, 814–817, 960–980, and 1259 inherit X006 through Book 011. Finally, the claim that a generically trivial line bundle on a regular surface is the line bundle of an integral vertical divisor, used at lines 776–784 and again in §9.4, needs the regular-local factoriality/Cartier--Weil interface that Book 011 proves only later in its Chapter 14, hence X007. These are exactly the bridges from the correct graph lattice to the asserted Picard/Neron component group; no additional independent Book-016 gap is needed for the failure verdict.

## Pending scope inventory

The following manuscripts are in this review's assigned 001–064 scope and remain **PENDING**. Each entry will be replaced by a full-read attestation and verdict only after a personal line-1-to-EOF read.

- PENDING — Book 017, `017-finite-etale-covers-and-fundamental-groups.md`
- PENDING — Book 017a, `017a-relative-picard-schemes-and-jacobians.md`
- PENDING — Book 018, `018-derived-etale-and-l-adic-cohomology.md`
- PENDING — Book 019, `019-proper-and-smooth-base-change.md`
- PENDING — Book 020, `020-etale-duality-and-trace-maps-for-curves.md`
- PENDING — Book 021, `021-etale-sheaves-and-cohomology-on-curves.md`
- PENDING — Book 022, `022-nearby-cycles-and-monodromy-for-semistable-curves.md`
- PENDING — Book 023, `023-lefschetz-trace-formulas-for-curves.md`
- PENDING — Book 024, `024-continuous-cohomology-of-profinite-groups.md`
- PENDING — Book 026, `026-finite-locally-free-schemes-and-algebras.md`
- PENDING — Book 027, `027-affine-group-schemes-and-hopf-algebras.md`
- PENDING — Book 028, `028-finite-flat-commutative-group-schemes.md`
- PENDING — Book 029, `029-fppf-cohomology-and-kummer-theory.md`
- PENDING — Book 030, `030-local-galois-cohomology.md`
- PENDING — Book 031, `031-tate-local-duality.md`
- PENDING — Book 032, `032-global-galois-cohomology-and-selmer-groups.md`
- PENDING — Book 033, `033-poitou-tate-duality.md`
- PENDING — Book 034, `034-cartier-duality.md`
- PENDING — Book 035, `035-abelian-schemes-isogenies-and-polarizations.md`
- PENDING — Book 035a, `035a-moduli-stacks-for-modular-and-pel-problems.md`
- PENDING — Book 036, `036-jacobians-and-h1-of-curves.md`
- PENDING — Book 037, `037-weights-and-weil-bounds-for-curves-and-abelian-varieties.md`
- PENDING — Book 038, `038-neron-models-and-component-groups.md`
- PENDING — Book 039, `039-integral-correspondences-on-curves-and-jacobians.md`
- PENDING — Book 040, `040-descent-and-weak-mordell-weil-for-abelian-varieties.md`
- PENDING — Book 041, `041-heights-and-the-mordell-weil-theorem.md`
- PENDING — Book 042, `042-finite-flat-galois-representations.md`
- PENDING — Book 043, `043-elliptic-curves-over-dvrs.md`
- PENDING — Book 044, `044-tate-curves-and-multiplicative-reduction.md`
- PENDING — Book 045, `045-torsion-and-tate-modules-of-elliptic-curves.md`
- PENDING — Book 046, `046-algebraic-de-rham-cohomology-and-gauss-manin-connections.md`
- PENDING — Book 047, `047-betti-de-rham-and-etale-comparison-for-curves.md`
- PENDING — Book 048, `048-divided-powers-and-crystalline-sites.md`
- PENDING — Book 049, `049-crystalline-cohomology-of-curves-and-abelian-schemes.md`
- PENDING — Book 050, `050-syntomic-cohomology-and-integral-period-maps.md`
- PENDING — Book 051, `051-finite-flat-group-schemes-of-small-height.md`
- PENDING — Book 052, `052-dieudonne-theory-and-raynaud-full-faithfulness.md`
- PENDING — Book 053, `053-fontaine-laffaille-modules-and-torsion-representations.md`
- PENDING — Book 054, `054-integral-fontaine-laffaille-equivalence-and-base-change.md`
- PENDING — Book 055, `055-p-divisible-groups-and-serre-tate-theory.md`
- PENDING — Book 056, `056-ramification-and-discriminants-of-finite-flat-representations.md`
- PENDING — Book 057, `057-artinian-and-complete-local-coefficient-rings.md`
- PENDING — Book 058, `058-formal-schemes-gaga-and-algebraization.md`
- PENDING — Book 059, `059-rigid-analytic-curves-and-formal-models.md`
- PENDING — Book 060, `060-rigid-uniformization-of-abelian-varieties.md`
- PENDING — Book 061, `061-semistable-abelian-varieties-and-monodromy.md`
- PENDING — Book 062, `062-pseudocompact-trace-algebras-and-carayol-descent.md`
- PENDING — Book 063, `063-deformation-functors-of-representations.md`
- PENDING — Book 064, `064-complete-local-algebra-for-deformation-theory.md`

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

### X003 — Book 006's rank-one Tate–Sen conclusion lacks the quantitative cochain argument it uses

- **Deficient source:** Book 006, §11.5, especially the “Finite Ax–Sen estimate” at lines 5068–5120 and the asserted compatible approximation homotopies at lines 5122–5129.
- **Consumers:** Book 006, lines 5131–5334 (completion invariants, `H^1` vanishing, semilinear descent, decompletion, Sen integrality, and the rank-one Hodge–Tate algebraicity theorem); Book 047, §9.5, especially lines 1115–1132 and 1187, treats Book 006's rank-one passage as already supplied; Book 098's ℓ-adic Hecke-character discussion likewise uses local algebraicity/Hodge–Tate labels.
- **Needed result:** a uniform finite Ax–Sen approximation theorem together with explicit compatible contracting homotopies on degree-1 and degree-2 continuous bar cochains, with the stated valuation bound, sufficient to pass to `\mathbf C_\ell`, prove `H^1(H,\mathbf C_\ell)=0`, and decomplete the multivariable Lubin–Tate action.
- **Why unavailable:** searches of the local Mathlib checkout found no Ax–Sen, Tate–Sen, Sen-operator, or Hodge–Tate theorem. Books 001–005 do not develop this analytic Galois-cohomology input. Book 006 proves the cyclic weighted-average identity, but the passage to arbitrary ramification clusters and the compatible degree-2 correction is stated rather than constructed; the later conclusions depend on exactly that omitted compatibility. Book 047 explicitly lists a broader `\mathbf C_p`/Tate–Sen foundation as future work and does not repair the rank-one proof.
- **Recommended chronological repair:** keep the Hecke-character and ℓ-adic-avatar construction conditional only on _local algebraicity_, which is enough for the class-field-theory interface, and remove the Hodge–Tate-implies-local-algebraic claim from Book 006. Develop the quantitative Tate–Sen cochain theorem in a later dedicated p-adic comparison volume, then cite it before Book 047/Book 098 use Sen or Hodge–Tate labels. Alternatively, expand §11.5 with a complete ramification-cluster construction and verified bounded bar homotopies before Lemma 11.1.

### X004 — Books 008–009 use inseparable normalization finiteness before the Japanese/excellence theorem

- **Consumers:** Book 008, §9.1, especially the finite-normalization lemma at repaired lines 1208–1223 and the projectivity argument at lines 1225–1239; Book 009, Lemma 9.1A at repaired lines 1472–1474 and Lemma 9.2A at repaired lines 1729–1731, whose projective embeddings feed Theorems 9.1–9.2 and the subsequent duality, proper-pushforward, and Riemann–Roch results. Later Books 011, 015, 016, and 017a consume this projective-curve, completed-node, and divisor package in turn.
- **Putative later source:** Book 010a, §9.2, especially Theorem 9.8 and Corollary 9.9 (quasi-excellent rings are universally Japanese, including finite-type algebras over a field); Book 011 then imports that package explicitly for finite normalization. Book 010a's proof itself depends on the unproved inputs recorded in X006, so it is not yet a discharged source.
- **Needed result:** the integral closure of $k[t]$ in every finite extension of $k(t)$, including a finite inseparable extension in characteristic $p$, is a finite $k[t]$-module; consequently the normalization of every finite-type integral curve over an arbitrary field is finite.
- **Why unavailable:** local `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean` proves module-finiteness for a finite **separable** extension. Books 001–007b do not prove Japanese finiteness. Book 008's separable trace/discriminant lattice argument covers that local theorem, but lines 1218–1221 replace the inseparable half by “choose a finite $p$-basis and clear denominators” without constructing a containing finite lattice or proving a uniform denominator for all integral elements; the trace pairing used immediately before is degenerate in the inseparable case.
- **Recommended chronological repair:** prove the special theorem that $k[t]$ is Japanese, with a complete inseparable argument, before Book 008's finite-normalization lemma. If that proof is instead left to Book 010a, move Book 008's normalization-based projectivity result and Book 009's Lemmas 9.1A/9.2A and dependent duality package after it, or restrict the intervening theorems to projective curves/families supplied with a projective embedding. Do not cite general excellence from Books 008–009 in their present chronological positions.

### X005 — Book 008's Hilbert-scheme construction lacks the equality-case syzygy theorem it needs

- **Deficient source:** Book 008, Theorem 12.A, especially repaired lines 2398–2477. Lines 2453–2465 assert that “owner” overlaps generate the entire first syzygy module and recursively resolve every next kernel, but the preceding slice-compression count proves only cardinality of shadows and does not construct or verify that syzygy resolution.
- **Consumers:** Book 008, lines 2470–2739 (vector-space persistence, Gotzmann regularity, the filtered marked-basis and finite-support lemmas, and the universal incidence scheme), and the Hilbert representability theorem at lines 2750ff; Books 015 and 016 subsequently use the fixed-polynomial Hilbert schemes supplied here. Book 009 uses only Book 008's independently constructed symmetric powers and is not a consumer of this gap.
- **Needed result:** the equality case of Macaulay growth/Gotzmann persistence, including a proof that the relevant monomial ideal generated in one degree has the asserted linear syzygy resolution, followed by an integral marked-basis theorem strong enough to preserve all quotient ranks over nonreduced base rings.
- **Why unavailable:** searches of the local checkout found no Macaulay, Gotzmann, Hilbert-scheme, or equivalent marked-basis theorem, and Books 001–007b stop at Hilbert syzygy and generic freeness. The two sentences at lines 2456–2465 do not specify the induction, its chain modules or differentials, or prove generation of higher kernels; all later Buchberger and nilpotent-base arguments invoke that missing conclusion.
- **Recommended chronological repair:** insert a complete standalone Macaulay–Gotzmann persistence chapter before the relative incidence construction, with the monomial syzygy complex and its exactness proved explicitly, then prove the integral marked-basis lifting from it. Alternatively, treat Hilbert representability as unavailable in Book 008 and move the Hilbert-scheme-dependent material in Books 015/016 after a dedicated Hilbert-scheme volume.

### X006 — Book 010a's Japanese and excellence theorems use declared background results without proof

- **Deficient source:** Book 010a, §1.2, especially lines 207–213, and the explicit admission in §10.4, lines 3359–3365.
- **Consumers:** (a) the Cohen–Macaulay regular-sequence and equidimensionality assertions are used in Proposition 10.2, lines 3205–3231, which carries Corollary 10.3 and Theorems 10.5–10.7; (b) the inseparability reduction is used at the start of Lemma 9.3, lines 2976–2990, which carries Corollary 9.4, Propositions 9.5–9.6, Theorem 9.8, Corollary 9.9, and clause (2) of Theorem 10.7; (c) Serre's reducedness and normality criteria are used in Corollary 3.12, Proposition 4.5, Theorem 4.13, Corollary 9.4, Theorem 9.8, and Theorem 10.7. Books 008–009's normalization arguments, Book 011's imported excellence package, and Book 016's resolution/common-domination steps therefore do not yet receive a proved source.
- **Needed results:** the height-$h$ regular-sequence theorem and equidimensionality of a Cohen–Macaulay quotient; the finite purely inseparable base-extension reduction needed to separate an arbitrary finite field extension; and the $R_0+S_1$ criterion for reducedness and $R_1+S_2$ criterion for normality, with the permanence consequences used here.
- **Why unavailable:** Book 010a labels all three inputs “Standard results used without proof.” Searches of the local Mathlib checkout for `CohenMacaulay`, variants of “Cohen–Macaulay,” `IsSerre`, Serre criteria, and equidimensionality found no implementation supplying them; the only `equidimensionality` match in the searched algebraic-geometry/ring-theory/field-theory tree is a warning that such a hypothesis cannot be assumed. Books 001–010 do not prove these theorems. Although local field-theory files develop purely inseparable extensions, no located theorem supplies this exact reduction, and in any event the two commutative-algebra gaps independently break the final chain.
- **Recommended chronological repair:** add a prerequisite commutative-algebra chapter before Book 010a's first uses, proving depth/Cohen–Macaulay theory through the regular-sequence and equidimensionality statements, and prove the two Serre criteria with their localization consequences. Add the finite-extension separable/purely-inseparable decomposition before Lemma 9.3. Only after those insertions should Theorem 9.8 and the excellence package be used to repair X004 or imported by Book 011.

### X007 — Book 011's divisor and minimal-model theory uses Chapter 14 factoriality before its proof

- **Deficient source/order:** Book 011, Chapter 14, lines 3105–3859, especially its opening admission at lines 3107–3114 and Theorem 14.43/Corollary 14.44 at lines 3791–3823. The theorem is proved in the book, but only after all of Chapters 4–13.
- **Consumers:** Proposition 4.2 uses Theorem 14.43 and Corollary 14.44 to prove regular one-dimensional local rings normal; §9.4 uses factoriality to make a section Cartier; Proposition 11.0 uses it to make every vertical curve Cartier and thereby define the intersection pairing; Theorem 11.1 uses it in the construction and contraction of horizontal divisors; the factorization lemma and Theorems 11.2A–11.2 then use that pairing and contraction to prove existence and uniqueness of minimal regular models. Book 012 explicitly imports Book 011's Cartier–Weil dictionary, intersection package, surface resolution, contraction, and birational factorization. Book 016 §§9.3–9.4 uses the same dictionary to identify every generically trivial line bundle with an integral vertical divisor and to construct the separated Picard quotient; later regular-model books inherit the interface in turn.
- **Needed result:** a regular local ring is factorial, hence normal, so every height-one prime on a regular noetherian scheme is locally principal and every Weil divisor on a regular arithmetic surface is Cartier.
- **Why unavailable at the point of use:** Books 001–010 do not prove regular-local factoriality. The local checkout has definitions and partial regular-local infrastructure, but `Mathlib/RingTheory/RegularLocalRing/Defs.lean` explicitly lists localization of regular local rings as a TODO, and searches found no theorem deriving a unique-factorization structure for an arbitrary regular local ring. Book 011 eventually proves the needed result in §§14.7–14.8, but the physical manuscript order makes that a forward proof dependency; the statement in §14.9 that “no circularity arises” addresses dependence of the late proof, not chronological availability to its earlier consumers.
- **Recommended chronological repair:** move the depth, homological-regularity, and factoriality development needed for Theorem 14.43 before Proposition 4.2 and before the first divisor assertion; then leave Chapter 14's remaining applications as a retrospective summary. A cleaner renumbering is to make the prerequisite algebra the new Chapter 4 and shift the geometric chapters, updating all anchors and theorem references. Until that reordering is made, the Chapter 11 intersection/contraction/minimal-model conclusions and Book 012's imports are chronologically unavailable.

### X008 — Book 015's dual-abelian-scheme construction lacks its cube, Hilbert, and polarization-isogeny arguments

- **Deficient source:** Book 015, §11.2, especially the cube lemma at lines 1124–1137, the Hilbert/Picard locus construction at lines 1139–1141, and the isogeny and descent assertions at lines 1143–1150; §6.4, lines 627–645, already uses the same Hilbert-scheme interface for uniform relative divisors.
- **Consumers:** Book 015's tangent calculation at lines 1154–1162 and exterior-algebra proof in §11.3; Book 017a declares dual abelian schemes from Book 015 as an input at line 114 and uses them in its Poincare-bundle, autoduality, polarization, norm, and correspondence package from §§6–10. Book 008's fixed-polynomial Hilbert representability is itself an upstream consumer via X005. Later abelian-scheme books may reconstruct parts of this package, but cannot retroactively supply Book 015 or Book 017a.
- **Needed results:** a complete theorem-of-the-cube/rigidity proof for rigidified line bundles; a representable algebraically trivial identity component of the relative Picard functor with universal Poincare bundle; and the theorem that an ample line bundle induces a finite locally free surjective homomorphism `\phi_L:A\to A^\vee`, including constant degree and fpqc descent of smoothness and properness.
- **Why unavailable:** coordinate-plane cancellation and constancy of maps from a proper fiber to an affine scheme do not by themselves produce a global trivialization of the cube bundle. The later assertions that coefficient equations cut out `P^0`, every algebraically trivial class lies in `\phi_L(A)` after finite extension, and its fiber length is locally constant are stated without proof and contain the missing polarization theorem. Searches of the local Mathlib checkout found no abelian-scheme, dual-abelian, theorem-of-the-cube, or Poincare-bundle implementation. Books 001–012 do not prove these results, and the Hilbert scheme cited from Book 008 has X005.
- **Recommended chronological repair:** first repair X005 or give a direct relative Picard construction sufficient for abelian schemes. Then insert a full cubical-line-bundle chapter, prove representability of `\operatorname{Pic}^0_{A/S}`, and prove the ample-bundle polarization isogeny (including degree constancy and flatness) before stating dual representability, its Lie algebra, or using it in Book 017a.

### X009 — Book 015's exterior-algebra theorem assumes the Poincare Fourier--Mukai calculation

- **Deficient source:** Book 015, §11.3, especially lines 1178–1202. The decisive assertions are the nontrivial-degree-zero cohomology vanishing argument at line 1180 and, more importantly, the completed Koszul and global direct-image claims at lines 1182–1195.
- **Consumers:** Book 015, lines 1204–1210 and its final abelian-cohomology conclusions; Book 046 explicitly invokes Book 015's translation/coherent exterior-algebra isomorphisms around lines 1399–1415 to form the Hodge-to-de Rham exterior algebra and all later Gauss--Manin calculations for abelian schemes.
- **Needed result:** the normalized Poincare bundle must satisfy `Rq_*\mathcal P\simeq e_*\mathcal N[-g]`, with a proof relating the formal deformation differential to a regular Koszul complex and algebraizing the completed calculation; its derived identity fiber must be identified multiplicatively with `R\Gamma(A,\mathcal O_A)` so that cup product is the exterior algebra on degree one.
- **Why unavailable:** formal functions identifies completions of cohomology/direct images; it does not, without a comparison morphism and an algebraization/support argument, identify the completed derived object with a Koszul complex or imply the displayed global quasi-isomorphism. The manuscript does not construct the connecting maps, prove the induction on infinitesimal neighborhoods, or justify the multiplicative derived-fiber identification. Searches found no local Mathlib theorem on abelian varieties/schemes, Poincare bundles, or Fourier--Mukai transforms, and Books 001–012 do not supply this calculation. X008 also leaves the required `A^\vee` and `\mathcal P` unavailable, but the Koszul/direct-image omission is independent even after those objects are granted.
- **Recommended chronological repair:** after X008, prove the Poincare-bundle acyclicity and completed Fourier--Mukai calculation as a standalone theorem, including the actual filtered complexes, transition maps, support/algebraization step, and multiplicative derived pullback. Only then deduce the fiberwise exterior algebra and apply the already proved base-change criterion relatively.
