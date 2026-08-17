# A 188-Volume Curriculum Toward Fermat's Last Theorem

This is the canonical catalog of the 188 retained mathematical manuscripts. The numbering is
a stable topological reading order: every substantial direct manuscript prerequisite has a
smaller number. Mathlib and the companion Class Field Theory development are proof sources,
not axioms, and their transitive imports remain subject to the same gap-free standard.

The preferred selected-three route is dependency-closed in the present manuscript graph. It
constructs the finite-set source patches used in the potential-modularity argument, obtains the
restricted signed-special finite fibre before choosing the minimal lift, evaluates the retained
support after that lift has been chosen, and carries one coefficient-three member through Brauer
effectivity, the integral tower, and the final contradiction. Stronger uniform and geometric
extensions remain outside the scope of that theorem and are described separately in
`BOOK_DEPENDENCIES.md`.

The route combines local and global arithmetic, curve and PEL geometry, selected trace-formula
transfer, compact-curve Galois realization, Eisenstein and explicit irreducibility, deformation
and paired source patching, potential automorphy and Brauer effectivity, and the fixed-three
finite-flat endgame. Each description records the theorem actually available from the current
manuscript and distinguishes it from optional stronger conclusions.

## Dependency-ordered catalog

1. **Valuations, DVRs, and Completions** — Begin with valuations and absolute values, then study valuation rings, discrete valuation rings, uniformizers, residue fields, maximal-ideal filtrations, completions, extension of valuations, and integral closure in finite extensions. Emphasize the finiteness and compatibility theorems that permit seamless passage among a local field, its valuation ring, its residue field, and its completion.

2. **Finite Extensions of Local Fields** — Study finite extensions of complete discretely valued fields through ramification index,
   residue degree, the fundamental equality, norms and traces, decomposition and inertia groups,
   unramified and totally ramified extensions, and unit filtrations. Develop Krasner's lemma and use
   it to prove finiteness, up to isomorphism, of extensions of bounded degree. The final chapters
   apply this structure to residue-field Frobenius and to number fields with prescribed local
   completions.

3. **Ramification Theory** — Build the finer structure of ramified extensions needed for Galois
   representations. Cover tame and wild ramification, lower and upper filtrations, Herbrand
   functions, the different, discriminant exponents, and ramification of towers. The cyclic
   ramification-number congruence and the integral Brauer-induction theorem are proved in the
   manuscript, so the Hasse--Arf theorem, integral Artin/Swan conductors, and the
   conductor--discriminant identities are unconditional under the explicit residue-separability
   and perfectness hypotheses the book tracks chapter by chapter.

4. **Adeles and Ideles** — Develop finite and full adeles and ideles as restricted products over the places of a number
   field. Study their topologies, diagonal embeddings, compactness theorems, idele class groups,
   local-global norm maps, and ray-class quotients. Conclude by showing how the same adelic language
   supports both global reciprocity and automorphic forms.

5. **Local Class Field Theory** — Give a systematic account of reciprocity for nonarchimedean local fields. Construct the
   local invariant and cyclic norm-index calculation. The finite-group Tate-cohomology machinery
   and the exact Herbrand norm-filtration comparison are developed inside the manuscript, so the
   book unconditionally constructs the local Artin map, calculates it on uniformizers and units,
   proves functoriality, characterizes norm subgroups, establishes the existence theorem, and
   classifies continuous one-dimensional characters.

6. **Global Class Field Theory** — Develop the idelic architecture of global reciprocity and its
   compatibility with local reciprocity. The finite Artin--Verdier duality theorem, the canonical
   $S$-unit sequence, and the rank-one Tate--Sen/Lubin--Tate comparison are proved in the
   manuscript, so finite reciprocity, the existence theorem, and the rank-one Hodge--Tate
   criterion are unconditional. Treat ray groups, Frobenius, and Hecke characters, and develop
   the normalized Brauer-invariant formalism these deductions use.

7. **Analytic Foundations for Odlyzko--Poitou Bounds** — Develop completed Dedekind zeta
   functions, explicit formulas with admissible test functions, archimedean gamma estimates, and
   rigorously certified numerical lower bounds for root discriminants in the relevant degree and
   signature ranges. The subject is restricted to discriminant bounds; Chebotarev density is
   treated separately.

7a. **Arithmetic Spectral Sequences and Derived Cohomology** — Starting from the general
theory of derived categories and spectral objects, construct derived global sections, derived
tensor and Hom, filtered complexes, and exact couples in the categories of arithmetic sheaves.
Prove convergence and comparison theorems for the Leray, Hochschild–Serre, hypercohomology, and
nearby-cycle spectral sequences.

7b. **Quasi-coherent Cohomology on Schemes** — Develop quasi-coherent sheaves and their
cohomology from the affine dictionary up: Serre's affine vanishing over arbitrary rings, finite
Čech models for separated schemes specializing Book 7a's abstract theorem, quasi-coherent higher
direct images, derived base change and filtered colimits, Grothendieck vanishing, and the full
computation of the cohomology of projective space with its perfect top pairing. Closes with
Hilbert's syzygy theorem and generic freeness in the forms the projective volumes consume.

8. **Ample Line Bundles, Hilbert Polynomials, and Symmetric Powers** — Starting from relative
   Proj and the elementary theory of projective morphisms, develop ample and very ample line
   bundles, descent of very ampleness, Hilbert polynomials, and projective embeddings for curves and
   abelian schemes. Projective flattening stratification and the bounded Macaulay--Gotzmann
   package are proved in the manuscript, so fixed-polynomial Hilbert representability and
   symmetric-power representability for smooth curves are unconditional; the quasi-coherent
   sheaf-cohomology formalism, projective-space cohomology, syzygy theorem, and generic freeness
   its cohomological chapters consume are now cited from Books 7a and 7b, and descent along
   finite locally free covers — including descent of morphisms into quasi-projective targets,
   so the universal-divisor construction's sheaf arguments are fully proved — is developed
   inline (no forward use of Book 10 remains).

9. **Divisors, Riemann--Roch, and Duality on Relative Curves** — Develop Cartier and Weil
   divisors, line bundles, degrees in families, residues, and the Euler-characteristic form of
   Riemann--Roch for smooth and nodal curves. The dualizing sheaf, perfect Serre duality,
   relative duality, and arbitrary-base-change theorems are proved in the manuscript, with the
   residue pairing constructed in full (valid over imperfect residue fields) and the cohomology
   formalism cited from Books 7a and 7b; a Stein factorization section proves connectedness of
   fibers for later volumes, and factoriality of regular local rings is proved in the
   dimension-at-most-two case the book uses. The étale-local nodal normal form and simultaneous
   normalization are stated only as flagged external interfaces and are verifiably unused by the
   book's results. Conclude with the divisor and differential interfaces used later.

10. **Faithfully Flat Descent in Algebraic Geometry** — Prove effective fpqc descent for
    modules, algebras, finite projective objects, affine and finite schemes, quasi-coherent sheaves,
    line bundles, and finite-flat group objects. Recover schemes under the proved affine, finite,
    quasi-affine, separated locally-quasi-finite, and compatible-polarization criteria needed by
    the moduli constructions, and show why unrestricted scheme-level effectivity is deliberately
    not asserted; no descent statement beyond the proved cases is assumed. Construct quotients by
    free actions of finite locally free group schemes with the full torsor identity, fppf sheaf
    quotient, and base-change properties, including stable-affine covers and subgroup quotients.

10a. **Excellent Rings and Formal Fibers** — Prove the permanence theory of excellent rings:
Serre's homological criterion for regularity, geometric regularity over fields, regular
homomorphisms and $G$-rings, Cohen's separability theorem, the theorem that algebras essentially
of finite type over complete local rings are $G$-rings, Grothendieck's finite-type permanence,
openness of regular loci, and Nagata theory via Tate--Akizuki. Concludes that fields, $\mathbf
Z$, characteristic-zero Dedekind domains, and complete local rings — and everything essentially
of finite type over them — are excellent, under one explicit standing hypothesis: residue fields
have finite $p$-degree, which holds for every base the collection uses.

11. **Normalization and Regular Models of Arithmetic Curves** — Prove the required finiteness
    of normalization and construct normal projective models of curves over excellent Dedekind
    schemes. Two-dimensional resolution of singularities for excellent surfaces is proved in the
    manuscript by the Lipman-style argument, and the contraction, minimal-model, and factorization
    theorems are unconditional; only the semistable-reduction input of the procedural applications
    chapter remains a declared external interface. Blowups are asserted to commute with flat, not
    arbitrary, base change. Complete-local-ring structure theory is cited from Book 1, Chapter 13;
    the depth calculus culminates in Serre's homological characterization of regularity and the
    Auslander--Buchsbaum theorem (regular local rings are factorial). Excellence is a theorem,
    not a hypothesis: the permanence theory is cited from Book 10a, with the convention that
    excellent rings have residue fields of finite $p$-degree (satisfied by every base the book
    admits, and stated as a narrowing where it bites).

12. **Blowups and Intersection Theory on Arithmetic Surfaces** — Develop blowups, strict
    transforms, local intersection multiplicities, projection formulas, fiber intersection
    matrices, and component pairings on regular arithmetic surfaces. The adjunction and canonical
    divisor package rests on Book 9's proved duality theorems, and the resolution package on
    Book 11's proved surface resolution, so neither is conditional. The scope is not general
    higher-dimensional intersection theory.

13. **Coherent Cohomology in Proper Families** — Prove finiteness, semicontinuity, coherent
    base change, formal functions, and representability consequences for the proper curves, abelian
    schemes, and low-dimensional PEL families used here. Apply these theorems to Picard
    representability, Hodge bundles, and integral modular forms.

14. **Semistable Curves, Dual Graphs, and Component Groups** — Study nodal and semistable
    models, graph Jacobians, relative Picard functors, monodromy pairings, and component groups under
    base change and finite correspondences.

15. **Finite Étale Covers and Fundamental Groups** — Develop étale morphisms, henselian neighborhoods, finite étale descent, Galois categories,
    geometric points, and the étale fundamental groups of curves and arithmetic bases. Prove the
    required base-change and specialization exact sequences and compare them with absolute Galois
    groups. Conclude by constructing continuous Galois representations from geometric covers and
    locally constant sheaves.

17a. **Relative Picard Schemes and Jacobians** — Construct Picard sheaves and schemes,
rigidification, identity components, Jacobians, Abel–Jacobi and Albanese maps, polarizations, and
functoriality under finite maps and correspondences.

18. **Derived Étale and $\ell$-adic Cohomology** — Construct finite-level and continuous $\ell$-adic cohomology, derived completion, cup products, traces, Galois actions, and perfect complexes for the curve and abelian-scheme range. Geometric proper and smooth base-change is prepared as a morphism and is imported only in the next volume, not assumed here.

19. **Proper and Smooth Base Change** — Prove proper and smooth base change for the constructible torsion and $\ell$-adic complexes needed on curves and abelian schemes, with all noetherian, invertibility, and finiteness hypotheses visible. The conclusions are limited to the stated geometric range and do not assert an unrestricted higher-dimensional six-functor formalism.

20. **Étale Duality and Trace Maps for Curves** — Develop trace maps, Poincaré duality, and compatibility with finite correspondences for smooth proper curves and the open or semistable curve situations explicitly treated. Surface duality and the retired unitary-surface branch are outside the theorem.

21. **Étale Sheaves and Cohomology on Curves** — Give a unified account of étale cohomology for smooth proper and semistable curves. Study
    constructible and lisse sheaves, continuous ℓ-adic cohomology in low degrees, proper and smooth
    base change, cup products, Frobenius, trace maps, and Poincaré duality. The étale-local model
    $xy=\pi$ at a node of a regular semistable family, assumed in earlier drafts, is proved here
    (Theorem 19.2) from Book 9's completed model by an elementary standard-étale argument. The
    culminating object is
    (H^1_{\mathrm{\acute et}}), carrying both a continuous Galois action and functorial actions of
    algebraic correspondences.

22. **Nearby Cycles and Monodromy for Semistable Curves** — Compute nearby cycles, vanishing cycles, monodromy, and the weight complex for strict semistable curves. For a tame ramified finite-free coefficient at a strict node, prove the full two-term procyclic complex with semidirect Frobenius, invariant-stable pull and trace (including expansion one), orientation, normalization filtration, and the geometrically constant ray-twist formula; when prime-to-$\ell$ invariants grow under pullback, the source and target complexes retain their distinct invariant summands. The volume proves the nodal-curve formulas used by modular and quaternionic models and does not claim a general surface semistable-reduction theorem.

23. **Lefschetz Trace Formulas for Curves** — Prove the Lefschetz trace formulas required for finite correspondences on proper curves, including the local terms and Frobenius conventions used downstream. The scope is the curve case; no surface trace formula is used to close the curriculum.

24. **Continuous Cohomology of Profinite Groups** — Develop continuous cohomology for profinite groups acting on discrete or topological modules, including the strict two-term $\mathbf Z_\ell$ lattice complex and its semidirect, restriction, adjoint norm, and orientation operators, with the distinction between pro-$\ell$ corestriction and the prime-to-$\ell$ part of a full tame covering degree retained.
    Construct homogeneous and inhomogeneous cochains, long exact sequences, connecting maps,
    restriction and corestriction, inflation–restriction, Shapiro's lemma, and cup products, and
    compare the cochain and derived-functor constructions. Applications identify deformation-theoretic
    tangent and obstruction spaces with low-degree cohomology.

25. **Finite Locally Free Schemes and Algebras** — Study finite locally free morphisms through finite projective algebras. Develop rank, fibers,
    base change, composition, dual modules, finite flatness over local rings and DVRs, and faithfully
    flat descent. The principal structural result is that finite flat morphisms of constant rank are
    stable under every operation used later for group schemes.

26. **Affine Group Schemes and Hopf Algebras** — Introduce affine group schemes through commutative Hopf algebras and prove the
    anti-equivalence between the two viewpoints. Develop subgroup schemes, kernels, the quotient
    constructions needed for finite groups, base change, morphisms, and exact sequences. Throughout,
    translate geometric assertions into explicit Hopf-algebra calculations.

27. **Finite Flat Commutative Group Schemes** — Specialize affine group-scheme theory to finite flat commutative groups over local and
    arithmetic bases. Study rank and fibers, connected and étale parts, kernels of multiplication,
    schematic closure of generic-fiber subgroups, and finite-flat subgroups of abelian schemes. Prove
    the exactness and closure theorems needed to model residual Galois representations integrally.

28. **fppf Cohomology and Kummer Theory** — Develop low-degree fppf cohomology, torsors,
    Kummer sequences, Picard and Brauer interpretations, descent boundaries, and compatibility with
    finite-flat group schemes.

29. **Local Galois Cohomology** — Apply continuous cohomology to absolute Galois groups of local fields. Compute and bound
    (H^0), (H^1), and (H^2) for finite modules and ℓ-adic representations, study unramified
    cohomology and restriction to inertia, prove cohomological-dimension results and the local Euler
    characteristic formula, and give coefficient-uniform Kummer calculations. The final dimension
    formulas govern local deformation conditions and hardly-ramified relation calculations.

30. **Tate Local Duality** — Develop the local duality pairing between a finite Galois module and its Tate-twisted dual.
    Prove continuous Hilbert 90 and the finite-module Tate–Nakayama theorem, construct the local
    invariant and cup-product pairing, and establish perfectness. Conclude by identifying annihilators
    of natural local conditions and deriving the dimension identities used for dual deformation
    conditions.

31. **Global Galois Cohomology and Selmer Groups** — Develop Galois cohomology for number fields with ramification restricted to a finite set of
    places. Define localization maps and general Selmer structures through subspaces of local (H^1),
    construct dual Selmer structures, and prove the exact sequences comparing global and local
    classes. Culminate in the identification of the tangent space of a global deformation problem
    with its associated Selmer group.

32. **Poitou–Tate Duality** — Prove the global duality theorem relating a Selmer condition to its dual. Develop the
    Poitou–Tate exact sequence, local-global pairings, orthogonal complements, global Euler
    characteristic formulas, and dimension identities for Selmer and dual Selmer groups. The final
    numerical formula determines how many Taylor–Wiles primes are required to kill the dual Selmer
    group.

33. **Cartier Duality** — Develop Cartier duality for finite flat commutative group schemes. Construct the dual through
    Hopf algebras, identify constant and diagonalizable examples, prove biduality, and study pairings,
    kernels, base change, and generic fibers. Relate this theory to duality on the torsion of elliptic
    curves and abelian varieties and to Tate-twisted Galois modules.

34. **Abelian Schemes, Isogenies, and Polarizations** — Develop dual abelian schemes, finite
    flat kernels, quotients by finite subgroup schemes, Weil pairings, polarizations, and extension
    over normal bases. Include the odd-isogeny preservation of full two-torsion needed by the Frey
    argument.

35a. **Moduli Stacks for Modular and PEL Problems** — Develop stacks, quotient atlases, rigidification, finite quotients, and coarse descent for the modular, Hilbert, and quaternionic PEL problems actually used later. The volume proves only the bounded representability and descent interfaces stated in its reusable theorem package; it supplies no unitary-surface realization.

36. **Jacobians and $H^1$ of Curves** — Study the Jacobian and Picard variety of a smooth proper curve, with emphasis on modular and
    Shimura curves. Relate torsion and Tate modules of the Jacobian to étale (H^1), develop
    polarizations and duality, and prove the functorial action of correspondences on Jacobians and
    Tate modules. This gives the bridge from geometric Hecke correspondences to finite-dimensional
    ℓ-adic Galois representations.

37. **Weights and Weil Bounds for Curves and Abelian Varieties** — Establish Weil bounds and weight-one purity for smooth proper curves and their Jacobians, together with the correspondence-summand consequences used by the Galois volumes. Hard Lefschetz is invoked only in this bounded curve-and-abelian setting, with no unitary-surface purity claim.

38. **Néron Models and Component Groups** — Construct Néron models of Jacobians and the
    required abelian varieties, prove the mapping property, analyze identity components and component
    groups, and compare with regular curve models.

39. **Integral Correspondences on Curves and Jacobians** — Extend finite correspondences to
    regular models and Néron models, prove compatibility with component groups and duality, and prepare
    integral Hecke actions.

40. **Descent and Weak Mordell--Weil for Abelian Varieties** — Develop Kummer descent, Selmer
    sets in the elementary isogeny range, finiteness modulo multiplication, and effective control of
    the finite bad-place data.

41. **Heights, Mordell--Weil, and the Faltings--Tate Reduction** — Construct Weil and
    Néron–Tate heights, prove Mordell--Weil, and develop the Faltings height, moduli-height, and
    isogeny-finiteness route to rational Tate-module semisimplicity. The stable-lattice and
    Jacobson-radical argument and curve-$H^1$ export are proved from the exact minimal input:
    finiteness of the relevant $K$-isogeny classes. Faltings--Shafarevich finiteness is a
    sufficient uniform source. The book proves finite polarized descent and integral Zarhin
    cancellation after Northcott. Its current internal sketches do not yet establish potential
    semistable reduction, ramified semistable Hodge base change, the arithmetic toroidal Siegel
    compactification, or the integral metrized Hodge--theta comparison from its permitted
    prerequisites. It now proves the Hermitian determinant/saturation identity, a finite
    Pl\"ucker upper-slope criterion, and the deduction of (13.3r) from two explicit universal
    multiplication-map certificates. The logarithmic Hilbert certificate still requires the
    determinant characters, exact boundary orders, positive level-prime divisibility, and cusp norm
    estimate; the theta certificate still requires uniform integral Pl\"ucker frames. Thus Tate
    semisimplicity remains conditional, and none of these two arithmetic gates supplies the four
    geometric/metric gates.

42. **Finite-Flat Galois Representations** — Relate finite flat group schemes over valuation rings to finite continuous representations of
    local Galois groups. Study the generic-fiber functor, integral models of (G_K)-modules, uniqueness
    and nonuniqueness, scalar extension, subobjects, quotients, duals, and extensions. Conclude with a
    mathematical characterization of representations that are finite flat at places above ℓ and the
    closure properties required in deformation theory.

43. **Elliptic Curves over DVRs** — Develop integral Weierstrass models over discrete valuation rings. Treat coordinate changes,
    discriminants and c-invariants, minimal models, good, multiplicative, and additive reduction,
    Néron-type criteria, semistability, and conductor consequences. Conclude with a complete
    calculation of the reduction type and minimal discriminant of the Frey curve from its equation.

44. **Tate Curves and Multiplicative Reduction** — Study elliptic curves with split and nonsplit multiplicative reduction through Tate
    uniformization. Construct the Tate curve, describe its points and torsion, analyze the Galois
    action on the Tate parameter and Tate modules, and relate the analytic description to reduction,
    inertia, and conductor. The closing chapters derive the local shape of residual and ℓ-adic
    representations at multiplicative primes.

45. **Torsion and Tate Modules of Elliptic Curves** — Develop (E[n]), the Weil pairing, Tate modules (T_\ell E), and residual representations
    (E[\ell]) over fields of the relevant characteristics. Prove that the determinant is
    cyclotomic, explain how reduction controls inertia, study duality and isogeny functoriality, and
    relate rational subgroup schemes to reducibility. Apply the theory to the two-dimensional
    representations carried by the Frey curve.

46. **Algebraic de Rham Cohomology and Gauss--Manin Connections** — Construct de Rham
    cohomology of curves and abelian schemes, Hodge filtrations, cup products, base change, and
    Gauss–Manin connections.

47. **Betti, de Rham, and Étale Comparison for Curves** — Construct singular (co)homology,
    period pairings, complex comparison isomorphisms, and compatibility with cycles, Hecke
    correspondences, polarizations, and rational structures. Isolate the coefficient-prime
    smooth-proper Hodge--Tate comparison and prove that, once supplied, it passes to all
    curve-cohomology subquotients and their one-dimensional constituents. The existing
    comparison, crystalline, and rigid volumes do not supply the $C_p$ period exact sequence.
    The smallest source-closed repair is one substantial future volume covering Tate--Sen/$C_p$
    foundations, the good-reduction $p$-divisible-group Hodge--Tate sequence, and the
    coefficient-prime Raynaud one-motive/semistable descent; general perfectoid or pro-étale
    smooth-proper theory would be a broader multi-volume expansion. Proposition 9.1 remains a
    formal inheritance result, not a proof of that input.

48. **Divided Powers and Crystalline Sites** — Develop PD rings and envelopes, crystalline
    sites and topoi, crystals, Frobenius crystals, and the functorial constructions required in
    degree one.

49. **Crystalline Cohomology of Curves and Abelian Schemes** — Construct derived crystalline
    cohomology and prove finiteness, base change, duality, Künneth, and Frobenius in the range required
    by finite-flat and PEL geometry.

50. **Syntomic Cohomology and Integral Period Maps** — Construct the weight-zero and
    weight-one syntomic complexes, integral period morphisms, exact sequences, and their compatibility
    with finite-flat group schemes.

51. **Finite-Flat Group Schemes of Small Height** — Develop schematic closure and exact
    operations, connected–étale and multiplicative decompositions, and the Oort–Tate classification
    of prime-order group schemes over the local bases occurring in FLT.

52. **Dieudonné Theory and Raynaud Full Faithfulness** — Construct Dieudonné modules in the
    finite-level range, compare the modules of torsion in abelian schemes with their first crystalline
    cohomology, classify the needed connected objects, and prove Raynaud full faithfulness below the
    ramification boundary.

53. **Fontaine--Laffaille Modules and Torsion Representations** — Develop divided filtered
    modules, the syntomic construction of their generic Galois modules, exactness, duality, and full
    faithfulness in weights zero and one.

54. **Integral Fontaine--Laffaille Equivalence and Base Change** — Prove essential
    surjectivity in the height-two range, identify finite-flat torsion objects, and establish the
    integral base-change and compatible-quotient results needed for stable lattices. Its
    rank-one inverse-limit calculation proves directly that an all-level finite-flat character
    over an absolutely unramified base is locally algebraic, without a smooth-proper
    $\mathbf C_p$ comparison theorem.

55. **$p$-divisible Groups and Serre--Tate Theory** — Develop connected–étale decompositions,
    ordinary deformation coordinates, canonical lifts, and openness of the ordinary local loci used
    in potential modularity.

56. **Ramification and Discriminants of Finite-Flat Representations** — Prove the
    Fontaine–Raynaud upper-break and different bounds, their stability in towers and under change of
    coefficients, and sharp root-discriminant estimates for fields cut out by finite-flat torsion
    representations.

57. **Artinian and Complete Local Coefficient Rings** — Study local Artinian rings with fixed residue field and complete Noetherian local rings as
    inverse limits. Develop continuous homomorphisms, formal power-series rings, completed tensor
    products, small extensions, pseudocompact modules, and closed subalgebras. The emphasis is the
    topological commutative algebra underlying deformation functors and trace rings.

58. **Formal Schemes, GAGA, and Algebraization** — Develop adic formal schemes, completion,
    formal fibers, Grothendieck existence in the required proper cases, complex GAGA, and
    algebraization of formal curves and abelian varieties.

59. **Rigid Analytic Curves and Formal Models** — Develop Tate algebras, affinoid localization,
    coherent sheaves, rigid generic fibers, admissible blowups, tubes, reduction maps, proper rigid
    curves, and comparison with algebraic curves.

60. **Rigid Uniformization of Abelian Varieties** — Develop analytic tori, discrete lattices,
    polarizations, quotient construction, formal descent, and Raynaud uniformization for the
    semistable abelian varieties and Jacobians used below.

61. **Semistable Abelian Varieties and Monodromy** — Develop toric and abelian parts,
    one-motives in the required range, monodromy pairings, conductor formulas, and quasi-unipotence for
    Tate modules. Prove coefficient independence of the Artin conductor and, over finite
    residue fields, the inertia-invariant Frobenius polynomial on every multiplicity space cut
    out by a split semisimple rational endomorphism algebra.

62. **Pseudocompact Trace Algebras and Carayol Descent** — Develop closed subalgebras of
    pro-Artinian coefficient rings, topological Nakayama, and the compact-group character theory used
    to control their inverse-limit topology. Prove the Burnside/Jacobson-density trace-generation
    theorem, Henselian lifting and splitting of the resulting Azumaya algebra, Skolem–Noether
    conjugacy, and strict-conjugacy descent. Culminate in Carayol's theorem that a residually
    absolutely irreducible representation is defined over its closed trace algebra.

63. **Deformation Functors of Representations** — Introduce deformations of a residual Galois representation over local Artinian coefficient
    rings. Define lifts, strict equivalence, framed and unframed deformations, fixed determinants,
    base change, and infinitesimal deformations. Identify tangent spaces with (H^1) of the adjoint
    representation and construct obstruction classes in (H^2), first locally and then globally.

64. **Complete Local Algebra for Deformation Theory** — Develop the complete local algebra used to analyze universal deformation rings: cotangent
    spaces, embedding dimension, formal-power-series presentations, Krull dimension, regular local
    rings, finite maps, topological Nakayama, and completed tensor products. Apply these results to
    convert cohomological tangent and obstruction calculations into bounds on generators and
    relations.

65. **Cotangent Complexes, Perfect Complexes, and Determinant Lines** — Treat cotangent
    complexes in the lci and deformation cases, perfectness, Tor amplitude, determinants, base change,
    and the determinant-line calculations used in PEL smoothness and patching. Do not develop the
    unneeded general theory of derived algebraic geometry.

66. **Representability of Deformation Problems** — Develop Schlessinger's criteria for pro-representability and versal hulls, emphasizing
    small-extension arguments and automorphism obstructions. Treat framed and unframed
    representations, fixed determinants, and passage between the variants. Conclude with existence
    and uniqueness theorems for the universal local and global deformation rings used later.

67. **Local Deformation Conditions Away from $\ell$** — Study deformation conditions at primes whose residue characteristic differs from ℓ. Treat
    unramified, minimally ramified, tame, Steinberg or special, and fixed-inertial-type deformations
    in the cases required for FLT. Prove representability, calculate tangent spaces, and establish
    formal smoothness and dimension theorems with their precise hypotheses.

68. **Finite Flat Deformation Conditions at $\ell$** — Study fixed-determinant deformations at primes dividing the coefficient characteristic through
    finite-flat group schemes and Fontaine–Laffaille modules. Prove invariance under strict
    equivalence, coefficient change, subquotients, and base change, then compute tangent and
    obstruction spaces. Establish representability and formal smoothness exactly in the residual and
    weight ranges where these statements are true, including the hardly-ramified case.

69. **Global Deformation Problems** — Combine a residual representation with specified local conditions to define a global
    deformation problem. Construct its universal ring, identify its tangent space with a Selmer
    group and its obstructions with global (H^2), compare framed and unframed variants, and impose a
    determinant. Use Poitou–Tate duality to derive the dimension inequalities that control generators
    and relations.

70. **Depth, Complete Intersections, and Fitting Ideals** — Develop regular sequences, depth, projective dimension, Cohen–Macaulay modules,
    complete-intersection rings, Fitting ideals, and support. Study their behavior under finite local
    maps and prove the freeness and faithfulness criteria by which a module forces structural
    conclusions about the ring acting on it.

71. **Numerical Criteria for $R=T$** — Develop the numerical criteria of Wiles and Lenstra independently of automorphic forms.
    Introduce congruence and cotangent modules, compare their lengths, and derive
    complete-intersection criteria. The central theorems characterize when a surjection (R\to T)
    between complete local rings must be an isomorphism.

72. **Smooth Representations of $p$-adic Groups** — Develop harmonic analysis and smooth representation theory for totally disconnected locally
    compact groups. Treat Haar convolution, admissibility, compact-open invariants, compact induction,
    contragredients, intertwiners, Hecke algebras, distributions, and characters. Examples from GL₂
    and quaternion division algebras prepare the character identities used in local transfer.

73. **Parabolic Induction, Jacquet Modules, and Whittaker Models for $\mathrm{GL}_2$** — Treat principal
    series, the geometric lemma in rank one, Jacquet modules, Whittaker uniqueness, Kirillov models,
    and local zeta integrals.

74. **Dihedral Supercuspidals, Types, and Newvectors for $\mathrm{GL}_2$** — Construct the tame and
    quadratic-induced supercuspidals occurring in the auxiliary automorphic representations, develop
    their types and characters, and establish conductors and integral newvector theory. Primitive
    wild types are outside the selected route.

75. **Weil--Deligne Representations and Local Constants** — Develop Weil and Weil–Deligne
    representations, monodromy and conductors, additive characters and self-dual measures, local
    L- and ε-factors, and functional equations.

76. **Local Langlands in the Principal, Special, and Dihedral Cases** — Construct and
    characterize the correspondence for the cases used by unramified forms, Steinberg conditions,
    and automorphic induction, with compatibility under twists and field extension.

77. **Quaternion Algebras over Number Fields** — Develop quaternion algebras as central simple algebras of degree two over local and global
    fields. Study reduced trace and norm, Hilbert symbols, splitting and division criteria,
    ramification at places, and completion. Culminate in the local-global classification by
    ramification set and the construction of the totally definite algebras used in modularity
    lifting.

78. **Characters and Dihedral Types on Quaternion Division Algebras** — Construct special
    packets and the quaternionic dihedral types corresponding to quadratic induction on GL₂,
    together with their conductors, regular-elliptic character formulas, and integral lattices.
    Primitive wild packets are excluded.

79. **Representations of Quaternion Division Algebras** — Study smooth representations of (D^\times) for a quaternion division algebra over a local
    field. Use compactness modulo the center to analyze admissibility and characters, then construct
    the special and dihedral packets by compact induction. Develop their conductors, levels, and
    integral lattices in the range corresponding to the selected GL₂ representations.

80. **Local Jacquet--Langlands for Special and Dihedral Packets** — Prove the character
    correspondence for Steinberg twists and the dihedral supercuspidals occurring in the route,
    including central characters, twists, conductors, local factors, and integral type compatibility.

81. **Cyclic Base Change: Local Theory** — Study the behavior of local representations under finite cyclic extension of local fields.
    Define base change through restriction of Weil–Deligne parameters, treat unramified and ramified
    extensions, and calculate it for principal, special, and dihedral discrete-series
    representations. Prove compatibility with twisting and local Jacquet–Langlands.

82. **Orders in Quaternion Algebras** — Develop orders, maximal orders, Eichler orders, localization at finite places, one-sided
    ideals and ideal classes, norms and discriminants, and finiteness of class sets. Reinterpret these
    structures adelically and use them to construct the compact open subgroups and finite double
    cosets underlying definite quaternionic forms.

83. **Automorphic Forms on Definite Quaternion Algebras** — Define algebraic automorphic forms on a totally definite quaternion algebra as functions on
    adelic double quotients. Develop weights, central characters, compact-open levels,
    finite-dimensionality, and integral coefficient lattices. Exploit compactness at infinity modulo
    the center to reduce the theory to finite combinatorial spaces carrying Hecke actions.

84. **Hecke Operators on Quaternionic Forms** — Construct Hecke operators from local double cosets and prove their algebraic properties.
    Develop spherical Hecke algebras at unramified primes, operators at level primes, global commuting
    families, change of level, and explicit formulas on finite double-coset models. Conclude with the
    Hecke modules compared with deformation rings in (R=T).

85. **Hecke Algebras and Congruences** — Study the commutative algebras generated by Hecke operators on integral automorphic forms.
    Treat localization and completion at maximal ideals, residual eigensystems, congruences, old and
    new subspaces, finite freeness, and change of level. The closing chapters construct the localized
    complete Hecke algebra (T) and its natural modules. The Galois comparison and the map from a
    universal deformation ring are constructed later, once the required Galois representations are
    available.

86. **Schwartz–Bruhat Analysis and Tate’s Thesis** — Construct adelic Schwartz spaces,
    self-dual measures, Fourier transform, Poisson summation, and Tate’s thesis with all character
    functional equations and local normalizations used later.

87. **Archimedean GL₂ and Discrete Series** — Develop real reductive groups, Harish–Chandra
    modules, discrete and limit-of-discrete series, characters, formal degrees, cohomology, and the
    parallel-weight-two infinity type.

88. **Hilbert-Space Spectral and Trace-Class Theory** — Develop unbounded self-adjoint
    operators, graph domains, compact resolvents, Hilbert–Schmidt and trace-class kernels, orthogonal
    decompositions, and the spectral arguments required for the cuspidal automorphic spectrum.

89. **Sobolev Theory and Elliptic Regularity on Arithmetic Quotients** — Develop invariant
    Sobolev norms, elliptic estimates, smooth-vector criteria, cusp decay, compactness on truncated
    quotients, and the analytic estimates needed for automorphic kernels.

90. **Reduction Theory and the Cuspidal Spectrum of $\mathrm{GL}_2$** — Prove adelic reduction theory,
    finite-volume and cusp estimates, construct automorphic L² spaces, and obtain the discrete
    cuspidal decomposition and finite multiplicities.

91. **Global Constant Terms and Eisenstein Contributions for $\mathrm{GL}_2$** — Develop parabolic
    constant terms, the required Eisenstein series, and their global intertwining operators in rank
    one. Prove the continuation and residue statements needed to classify the noncuspidal
    contributions, and show that the selected cuspidal test functions annihilate every one of them;
    do not construct the general automorphic Plancherel formula.

92. **Global Whittaker Models and Rankin–Selberg Theory** — Prove global genericity, Whittaker
    expansions, unfold Rankin–Selberg integrals, factor local zeta integrals, and obtain the analytic
    properties used for multiplicity one and trace formulas.

93. **Analytic Theory of Automorphic Rankin–Selberg L-functions** — Prove continuation,
    functional equations, pole criteria, vertical bounds, and positivity for GL₂ Rankin–Selberg
    L-functions, with compatible local and global normalizations. Deduce the analytic criterion that
    underlies multiplicity one.

94. **Strong Multiplicity One and Global Newforms for $\mathrm{GL}_2$** — Use Rankin–Selberg pole
    criteria to prove strong multiplicity one, then develop conductors, old and new subspaces,
    restricted tensor products, normalized newvectors, and the global newform decomposition.

95. **Automorphic Representations of $\mathrm{GL}_2$** — Develop automorphic representations of (GL_2(\mathbb A_F)) through restricted tensor
    products, cuspidal forms, central characters, and local components. Prove the required
    multiplicity-one and newform theorems and relate unramified Hecke eigenvalues to local Satake
    parameters. Conclude by translating between classical or Hilbert modular forms and adelic
    representations.

96. **Automorphic Representations of $D^\times$** — Develop automorphic representations of the multiplicative group of a quaternion algebra.
    Relate adelic automorphic forms to irreducible global representations, decompose them into local
    components, and prove the required multiplicity statements. Special attention is given to the
    finite algebraic spaces for totally definite algebras and their decomposition into global
    representations.

97. **Algebraicity and Integral Structures of Weight-Two Packets** — Prove rationality fields,
    Galois conjugation, integral Hecke lattices, period comparisons, and compatibility of weight-two
    automorphic packets with coefficient embeddings.

98. **Hecke Characters and Automorphic Induction from $\mathrm{GL}_1$** — Develop algebraic and finite-order Hecke characters, theta series, and quadratic automorphic
    induction. Prove cuspidality criteria, calculate every required local component, control
    coefficient fields, and identify the associated dihedral Galois representations through class
    field theory. These forms furnish the automorphic starting points for potential modularity.

99. **Cuspidal Trace-Formula Kernels for Rank Two** — Construct automorphic kernels with a
    cuspidal archimedean factor, prove their absolute convergence and trace-class properties, and
    establish equality of the spectral and geometric expansions in exactly this simple-trace-formula
    setting.

100. **The Cuspidal Spectral Side of the $\mathrm{GL}_2$ Trace Formula** — Compute the discrete cuspidal
     trace distribution and prove, from constant terms and pseudo-coefficients, that the residual and
     continuous contributions vanish for the selected functions. Record the multiplicities and
     normalizations compatible with local transfer.

101. **The Geometric Side of the GL₂ Trace Formula** — Classify rational conjugacy classes,
     prove convergence, identify the terms killed by the cuspidal factor, and compute the surviving
     central and elliptic distributions with the measures used in trace comparison.

102. **Orbital Integrals for $\mathrm{GL}_2$ and Quaternion Algebras** — Compute the required
     nonarchimedean and archimedean regular orbital integrals, singular limits, measures, and local
     character identities for the test functions used in transfer.

103. **Transfer of Test Functions and the Rank-Two Fundamental Lemma** — Construct matching
     functions for GL₂ and its quaternionic inner form and prove the unit, Iwahori, and selected level
     fundamental lemmas needed by global comparison.

104. **Global Jacquet--Langlands** — Prove global Jacquet--Langlands for noncharacter algebraic weight-two packets whose ramified finite factors lie in the constructed special or tame-dihedral local range. The trace-formula comparison gives multiplicity, good Hecke data, and the compact one-split inverse transfer in every degree $d\ge2$ for $(d-1)+|W|$ even; in odd degree $W$ may be empty. Primitive wild and excluded dyadic packets are not covered.

105. **Twisted Conjugacy and Geometric Trace Distributions** — Develop twisted conjugacy,
     norms, centralizers, stable classes, measures, and the convergent geometric distributions for
     prime-degree cyclic extensions.

106. **Twisted Cuspidal Trace Kernels and Spectral Expansion** — Construct twisted automorphic
     kernels and intertwining operators for the selected cuspidal functions, prove convergence, and
     identify the cuspidal spectral expansion while showing that the noncuspidal terms vanish. Apply
     the resulting twisted simple trace formula to cyclic base change.

107. **Twisted Orbital Matching and the Cyclic Fundamental Lemma** — Prove unramified norm
     matching, the twisted fundamental lemma, and the ramified and level-specific matching statements
     needed to compare the twisted and untwisted trace formulas.

108. **Cyclic Base Change for $\mathrm{GL}_2$** — Prove prime-degree cyclic base change for the cohomological GL₂ packets used here by comparing
     twisted and untwisted cuspidal trace formulas. Establish existence and local compatibility at
     every place, control Hecke eigenvalues, levels, and central characters, and characterize
     cuspidality and the image through self-twists. Conclude with cyclic descent and its character
     ambiguity.

109. **Solvable Base Change and Descent** — Iterate cyclic base change through prime-cyclic towers,
     resolve character-twist ambiguities, prove independence of the chosen tower, and control the
     selected local types in ascent and descent. Chapter 14 additionally constructs positive
     even-degree totally real preparation towers for finite-set Ihara avoidance: it kills the
     actual residual local actions, makes every active residue cardinality congruent to one in the
     coefficient characteristic, preserves protected completions with their exact multiplicities,
     and keeps the tower disjoint from the joint residual--cyclotomic cutout. Separate auxiliary
     and target modes record the different dyadic behavior, while the selected-safe cyclic ledger
     verifies precisely when an automorphic packet can be carried up and descended again.

110. **Generalized Elliptic Curves and Level Structures** — Construct generalized elliptic
     curves, Néron polygons, Drinfeld and Γ₁/Γ₀ structures, contraction, Tate cusp charts, and the
     moduli interpretations required at prime level.

111. **Compactified Modular Stacks and Coarse Modular Curves** — Construct compactified stacks,
     fine rigidified covers, coarse schemes, cusp divisors, descent of universal isogenies, and the
     stack/coarse comparison at exceptional automorphism loci.

112. **Deligne--Rapoport Integral Models of Modular Curves** — Prove regularity and smoothness
     away from level and construct the two-component semistable model at prime level, including nodes,
     Igusa normalizations, degeneracy maps, and component intersection data.

113. **Integral Modular Forms and q-Expansion** — Develop Katz modular forms through the Hodge
     bundle, q-expansion principles at every cusp, Hecke and diamond operators, dualizing forms, cusp-
     form lattices, and Sturm-style finite certification.

114. **Modular Jacobians, Néron Models, and Hecke Correspondences** — Construct the integral
     Hecke action on modular Jacobians, component groups, monodromy, Albanese maps, and the integral
     Eichler–Shimura relation needed by both Mazur’s method and Galois extraction.

115. **Reductive Groups, Inner Forms, and Corestriction in Rank Two** — Develop root data,
     restriction of scalars, inner twisting, quaternionic groups, corestriction algebras, involutions,
     and the symplectic representations used in the PEL constructions.

116. **CM Abelian Varieties, Types, and Reflex Norms** — Develop CM fields, types and orders,
     ideal actions, complex constructions of CM abelian varieties, polarizations, endomorphism descent,
     reflex fields, and reflex norms in the dimensions used by the PEL models.

117. **Complex Multiplication, Reciprocity, and Reduction** — Prove the main complex-
     multiplication reciprocity law in the required cases and develop its canonical descent, Galois
     action, good-reduction, and finite-place consequences for CM points on the selected Shimura data.

118. **Shimura Data and Canonical Models in the FLT Cases** — Develop the relevant Shimura
     data, reflex fields, connected components, reciprocity maps, neat levels, and canonical-model
     descent for Hilbert and quaternionic data. Prove that a mixed split/compact quaternionic
     Hodge map cannot lift to the direct common-norm group because its reduced-norm exponents
     have opposite parity. Construct the exact replacement: the CM-unitary common-multiplier
     PEL datum with the same adjoint group and reflex field the CM composite. By a connected
     fiber product over the common adjoint group, construct an actual finite unitary PEL level
     cover of every centrally saturated routed basic component over a component field unramified
     at prescribed split hyperspecial primes, with all level shrinking away from those primes.
     Central saturation is harmless on the trivial-central-character FLT packet block; fine PEL
     rigidification is imposed only after the effective component comparison.

119. **Quaternionic PEL Functors and Representability** — Construct the moduli functors,
     determinant and polarization conditions, fine covers, representability, and universal abelian
     families for supplied quaternionic PEL realizations. The direct common-norm trace example is
     explicitly excluded in mixed one-split signature by Book 118's Hodge-lift obstruction; the
     unitary common-multiplier replacement is proved PEL-exact with its determinant law.

120. **Uniformization, Components, and Hecke Descent for Shimura Curves** — Prove complex
     uniformization, identify connected components and canonical descent, compare fine and coarse
     levels, and descend universal isogenies and Hecke correspondences.

121. **Good Integral Models of Quaternionic Shimura Curves** — Construct smooth PEL models at
     good primes, extend universal abelian schemes and Hecke correspondences, and prove smooth/proper
     base change and integral comparison for their cohomology. Besides the conditional direct
     presentation, prove the split odd hyperspecial local model and proper good model for Book
     118's unitary common-multiplier cover; no dyadic parahoric comparison is inferred.

122. **Semistable Models and Monodromy of Quaternionic Shimura Curves** — Construct the one-step Iwahori semistable models of supplied direct quaternionic PEL curves in the verified odd and dyadic tensor-split cases. Compute the two branches, nodes, graph monodromy, Hecke action, and raw packet parameter. Normalize the fine vertex--edge diagram in the effective common Galois closure of its actual objectwise principal/ray covers, prove objectwise finite local freeness and that the lifted finite top legs are isomorphisms, and calculate the ray factor. Proposition 9.3 proves the level-one Drinfeld-basis normalization $({\rm DLB}_1)$, (9.29k)--(9.29l) prove every active finite-depth normalization and intermediate invariant ring, and (9.29r)--(9.29x) compute the raw higher branches, inertia, inseparable residue degrees, node-annular complexes, and boundary stabilizers. The explicit Drinfeld divisor, stabilizer, and Bruhat equations give the wild-invariant extreme lines and constant-extreme-line generization without calling the wild principal cover tame; Proposition 9.4 promotes node routing, multiplicity and expansion one, and residue-prime Hecke/transpose compatibility to the actual common factor. Propositions 9.5--9.8 give the general invariant-field, endpoint, Milnor-tube, and proved restriction--Gysin formalisms. Proposition 9.9 constructs the strict ray quotient used downstream and computes its local field, vertical unit, Drinfeld leading class, endpoint factors, Frobenius orbits, and actual active/ray intersection. Proposition 9.10 normalizes the completed two-dimensional tubes and computes their cohomology, actions, and generization maps for the permutation and two Steinberg rows; Corollary 9.11 proves $({\rm KBL}_v)_{\rm act}$, $({\rm BTK}_v)_{\rm act}$, $({\rm HDB}_v)_{\rm act}$, and $({\rm PNS}_v)_{\rm act}$. Only arbitrary intermediate representations or arbitrary cyclic ray data remain outside that result. The mixed one-split direct common-norm realization is excluded by Book 118's Hodge-lift obstruction. The non-common-norm unitary dyadic source is constructed; its finite integral comparison (10.5) remains a stronger raw-to-raw theorem, but Proposition 10.2A and Book 168's targetwise ramified-spectator bypass remove it from the semisimple FLT signed-special route. Ihara saturation and raw-to-global semisimplification remain separate interfaces.

123. **Modular and Shimura Curves** — Give a unified geometric treatment of the modular and quaternionic Shimura curves used in
     FLT. Develop their moduli problems, level structures, compactifications, cusps, connected
     components, canonical descent, Hecke correspondences, and good and semistable integral models.
     Conclude by constructing the geometric Hecke modules in étale cohomology and Jacobian Tate
     modules that will later be compared with automorphic representations.

124. **Hecke Correspondences on Curves and Jacobians** — Construct Hecke correspondences on modular and Shimura curves and compare them with adelic
     double cosets. Extend the correspondences over the required integral models, study their actions
     on divisors, Jacobians, component groups, and étale cohomology, and prove the good-prime
     Eichler–Shimura relations. The same Hecke algebra thereby acts on automorphic forms and on the
     Galois representations arising from geometry.

125. **Automorphic Decomposition of Shimura-Curve $H^1$** — Decompose $H^1$ of the proved compact one-split quaternionic Shimura curves into full finite Hecke blocks and isolate the rank-two Galois multiplicity space. Component routing, Schur splitting, determinant data, and good-prime relations are proved only under the displayed carrier, denominator, and component-separation hypotheses.

126. **Galois Representations from Weight-Two Shimura-Curve Cohomology** — Extract continuous rank-two Galois representations from the full Shimura-curve Hecke block, with determinant, parity, good Frobenius polynomials, and a placewise stable lattice. The construction distinguishes the raw cohomological representation from its semisimplification and claims no bad-place compatibility or canonical integral summand.

127. **Galois Representations Attached to Weight-Two Automorphic Forms** — Assemble the cohomological extraction into a weakly compatible family for weight-two packets that possess a proved compact one-split carrier. Global Jacquet--Langlands supplies that carrier for every parity-compatible selected set: odd nonempty in even degree and possibly empty in odd degree. No surface substitute, strict bad-place compatibility, or canonical finite-flat lattice is asserted.

128. **Local--Global Compatibility for Weight-Two Galois Representations** — Prove the stated local--global recognition results at good, split-Iwahori special, and selected tame places for the raw rank-two carrier. Zero-monodromy pairs pass formally to the global semisimplification. For nonzero monodromy, passage follows at one coefficient place from residual absolute irreducibility and, uniformly, is reduced through the full Hecke block and Morita evaluation to semisimplicity of the ambient curve cohomology. Book 41 proves integral cancellation and the Tate stable-lattice reduction from finite isogeny classes, but its uniform Faltings--Shafarevich route retains the potential-semistability, ramified Hodge-base-change, toroidal-compactification, and metrized theta--Hodge interfaces and the logarithmic-Hilbert and theta upper-slope certificates isolated there. The coefficient-prime local comparison is also not proved here.

129. **Galois Lattices and Finite-Flat Closures in Abelian Tate Modules** — Given a rational Galois plane inside a good-reduction abelian Tate module, construct a saturated stable lattice and an exact all-level finite-flat tower in the Raynaud--Fontaine--Laffaille range. The lattice is noncanonical, coefficient places are not synchronized, and rational crystallinity alone does not supply the required geometric or strongly divisible bridge.

130. **Modular Curves $X_0(N)$ and $X_1(N)$** — Develop modular curves from generalized elliptic curves with Γ₀ and Γ₁ level structures.
     Treat compactification, cusps, degeneracy maps, integral reduction, and rational points. Conclude
     with the precise correspondence between rational X₀(p)-points, rational cyclic isogenies, and
     reducibility of E[p].

131. **Jacobians of Modular Curves** — Study the prime-level modular Jacobian J₀(p), its Hecke action, cuspidal subgroup, Albanese
     maps, reduction and component maps, duality, and Néron model. Construct the Eisenstein quotient
     used in Mazur's argument and relate rational points on X₀(p) to finite subgroup schemes and Hecke
     modules of the Jacobian.

132. **Eisenstein Series, Congruences, and the Eisenstein Ideal** — Construct the prime-level
     Eisenstein series, compute constant terms, define the Eisenstein ideal, prove the q-expansion
     congruence theorem, and calculate its exact index in the Hecke algebra.

133. **Cuspidal Divisors and Specialization on Modular Jacobians** — Determine the cuspidal
     divisor group, its Hecke action, order, and specialization in the component group at the level
     prime. Develop only the auxiliary multiplicative subgroup facts used by the selected Eisenstein
     quotient, not the full Shimura-subgroup intersection theorem.

134. **Mazur–Raynaud Admissible Group Schemes** — Develop the category of group schemes finite
     flat away from the level prime, its constant and multiplicative constituents, extension and
     flat-cohomology calculations, and the devissage needed to control the selected Eisenstein
     prime quotient, including the two-primary boundary. Do not prove complete multiplicity one or the
     full rational torsion of J₀(p) when the FLT quotient does not require it.

135. **Genus-Two Curves, Jacobians, and Abel--Jacobi Geometry** — Develop hyperelliptic curves of
     genus two, divisor classes, Jacobians, principal polarizations, Abel–Jacobi embeddings, reduction,
     and the geometry of rational points in the exact range used by X₁(13) and the mixed-seven curve.

136. **Mumford Representations and Exact Genus-Two Jacobian Arithmetic** — Develop unique
     reduced Mumford representatives, Cantor composition and reduction, torsion tests, finite-field
     point counting, reduction homomorphisms, and checkable arithmetic certificates.

137. **Explicit Two-Descent on Genus-Two Jacobians** — Develop étale descent algebras, S-unit
     squareclasses, norm kernels, local descent images, Selmer bounds, torsion determination, and
     odd-prime saturation. Carry out the two finite calculations needed for the Jacobians of X₁(13)
     and the mixed-seven curve.

138. **Integral Local Types and Type Lattices** — Construct integral primary and companion lattices for principal, special, depth-zero dihedral, and tame positive-depth local types, together with their represented enhanced deformation conditions. Realize the quotient and augmentation Steinberg flag rows on the generic parahoric tower and identify their bad-fiber extensions as strict procyclic normalization--conductor complexes. Book 122 constructs the strict ray datum, factors its actual endpoint Kummer polynomials and intersection fields, normalizes the completed tubes, computes their cohomology/actions/generization, and combines them with the proved restriction--Gysin correspondence to prove $({\rm PNS}_v)_{\rm act}$ for these rows. Arbitrary principal representations and arbitrary cyclic ray data are not asserted. Banality, ordering, sign, and saturation hypotheses are retained, and primitive wild or ramified dyadic positive-depth types are excluded.

139. **Ihara Theory and Saturated Degeneracy Maps on Shimura Curves** — Compute the two-map tree kernel and the integral degeneracy filtration for clean compact Shimura curves. The noncongruence-character quotient is identified exactly with the routed sum of transgression kernels on the $K_c^v$-invariant continuous characters of the full profinite congruence kernels. For fixed $(F,B,v)$ the underlying kernel is invariant under every open spectator level, while the quotient action, transgression, and localization remain row-dependent. Conditional on the finite routed family of localized odd-primary vanishings $({\rm AC}^{\rm loc}_\ell)_{\mathscr R}$, the residual map is injective, the old image is saturated, and the integral new quotient is free with its graph, component, and branch-correction filtrations. This finite-family vanishing is the sole congruence-kernel input retained by the FLT seed construction and remains unproved; no general centrality, metaplectic-duality, or local-multiplier theorem is required.

140. **Integral Level Change and Jacquet--Langlands Comparison** — Compare one-prime integral level change with selected Jacquet--Langlands using the corrected Ihara filtration, graph lattice, and faithful Hecke orders. The theorem remains conditional on abelian Ihara and the datum-specific enhanced flagged PEL node-groupoid classification (5.9a), including its branch, Frobenius, Hecke-span, routing, stabilizer, coefficient-flag, and pairing enhancements. Relative to the separate abelian Ihara input, generic support in the clean constant-coefficient block is proved from Book 125's component-routed semisimple decomposition and the corrected filtration. The type ledger records that an integral flag projector handles the $q_v+1$-unit quotient/augmentation range and that type transport is formal once that groupoid equivalence is supplied; it proves neither the nonbanal quotient-new/filtered-cofiber assertions nor a several-prime comparison.

141. **Dickson Classification and Adequate Residual Image** — Develop the Dickson classification and the adequate-image consequences needed to select Taylor--Wiles elements in coefficient characteristic at least seven. The small-image and coefficient-five boundaries are stated explicitly and no automorphy conclusion follows from adequacy alone.

142. **The Chebotarev Density Theorem** — Develop Frobenius conjugacy classes and Dirichlet
     density, then use ray partial zeta functions, Poisson–Mellin analysis, finite-order Hecke
     characters, and logarithmic Euler products to prove the required pole, holomorphy, and
     nonvanishing statements at one. Prove abelian density by character orthogonality and full
     Chebotarev by cyclic fixed-field reduction and centralizer counting. Derive finite-quotient prime
     selection, profinite Frobenius density, and the precise Brauer–Nesbitt and
     representation-transport interfaces, without claiming effective bounds or general Artin
     holomorphy.

143. **Taylor–Wiles Primes** — Construct auxiliary primes that trade global dual-Selmer
     obstructions for controlled local diamond directions. Besides the usual exact cardinality,
     congruence, ordered-eigenline, and tangent calculations, Chapter 15 treats two integral local
     sources with the same embedded residual deformation problem. It identifies their strict
     relative Selmer group and selects one ordered Taylor--Wiles set that kills it on both sides,
     with separate detector and padding fibres and the full totally real relative variable count.

144. **Taylor–Wiles Systems** — Organize finite deformation rings, modules, diamond actions,
     augmentations, pairings, and presentation maps into systems that can be patched without
     inventing arithmetic transitions between unrelated auxiliary sets. Chapter 18 constructs one
     synchronized diagonal path for a desired--avoidance pair: it retains their common nilpotent
     spectral quotient, base-changed residual module, full partial frames, Hecke and adjoint marks,
     perfect pairings, and exact module coinvariants. Acting-image augmentation remains a distinct
     saturation question.

145. **Patching Modules and Rings** — Construct patched deformation rings and modules, establish
     the depth, support, pairing, and freeness statements needed for $R=T$, and keep nilpotent
     sensitivity separate from topological support. Chapter 17 patches the expanded local sources
     of a desired--avoidance pair. Faithfulness on the integral avoidance source transfers through
     the common residual module and unique-horizontal specialization to every desired component;
     coefficient-power nilpotents are controlled explicitly. Exact module and represented-ring
     recovery then give a nilpotent finite-level action kernel, pointwise factorization, and
     whole-ring finiteness, without assuming exact augmentation of the acting image.

146. **The Abstract $R=T$ Argument** — Complete the Taylor–Wiles method in an abstract algebraic setting. Show how the patched
     module forces faithfulness of the (R_\infty)-action, compare dimensions and
     complete-intersection properties, and descend from infinite level to the original deformation
     and Hecke rings. The main theorem gives (R\simeq T) from the structural hypotheses isolated in
     the preceding volume.

147. **Completed Hecke Pieces and Eisenstein $p$-divisible Groups** — Construct the selected
     Eisenstein quotient, its Néron model and completed Hecke piece, and prove admissibility and control
     of the finite-flat p-power torsion used in Eisenstein descent. Exclude generic cyclotomic-tower
     theory and unrelated p-adic analytic results.

148. **Eisenstein Descent and the Mordell--Weil Group of the Eisenstein Quotient** — Develop
     flat-cohomological Eisenstein descent, compute the relevant Selmer groups and Hecke annihilators,
     and combine descent with height theory to prove finiteness of the rational points of the
     Eisenstein quotient. The treatment follows the algebraic Eisenstein argument rather than the
     winding-quotient method or analytic rank-zero theorems for arbitrary modular factors.

149. **Eisenstein Cotangent Lattices and Formal Immersion** — Develop integral cotangent
     comparisons for the Eisenstein quotient and prove formal immersion at the oriented Γ₁ cusp.
     Combine specialization of rational prime-order points with the uniform theorem for primes at
     least seventeen and with the genus-one calculation at level eleven, isolating the two remaining
     genus-two rational-point problems.

150. **Mordell--Weil Sieves for Hyperelliptic Curves** — Develop reduction-set constraints,
     coset sieving, saturation certificates, completeness criteria, and exhaustive Mordell–Weil
     sieves. Determine X₁(13)(ℚ) and prove that the mixed-seven curve has only cuspidal or degenerate
     rational points.

151. **Semistable Full-Two Residual Irreducibility** — Prove irreducibility over $\mathbf F_p$ for the $p$-torsion of a semistable elliptic curve over $\mathbf Q$ with full rational two-torsion, for every $p\ge7$. The argument imports the bounded formal-immersion and explicit genus-two computations for the exceptional primes and does not claim absolute irreducibility or a general rational-isogeny classification.

152. **Deep-Level Quaternionic Modules and Diamond Actions** — Construct deep-level definite
     quaternionic modules with effective diamond torsors, perfect pairings, finite shadows, and exact
     module augmentation. Chapter 20 carries two coefficient systems on one class groupoid: a
     marked residual lattice and prime-to-coefficient stabilizers give an intrinsic common localized
     residual module, synchronized positive diamond rank, exact saturated orbit-sum coinvariants,
     compatible Hecke operators and adjoints, and genuine partial-frame scalar extension. It also
     gives the precise fixed-rank alternatives needed by the synchronized system of Book 144 and
     isolates the additional saturation required for exact acting-image augmentation.

153. **Hilbert Irreducibility and Arithmetic Approximation** — Develop Hilbert irreducibility together with weak approximation, prescribed decomposition and
     completion data at finitely many places, linear disjointness, avoidance of given extensions, and
     totally real specialization. Use the finiteness of local extensions of bounded degree to reduce
     simultaneous local requirements to finitely many conditions. Conclude with the specialization
     theorems needed for Moret–Bailly and automorphy fields.

154. **Moret–Bailly’s Theorem** — Develop moving lemmas for zero-cycles, symmetric powers, configuration spaces, and irreducible
     zero-cycle approximation, then prove Moret–Bailly's local-open existence theorem in the required
     totally-real form. Derive the linear-disjointness and splitting refinements used later. The
     main theorem turns prescribed local points on a moduli space into a global point over a
     controlled totally real extension. The norm--Abel refinement constructs moving families for
     nonsplit packets repeatable wholesale. For one exceptional factor it gives the exact mixed
     degree-indexed allowed-divisor criterion, coset-complete and integral-open saturation repairs,
     and a residue-tube counterexample showing that norms and high degree alone do not supply either
     geometric hypothesis.

155. **Galois and Solvable Refinements of Arithmetic Approximation** — Control normal closures,
     local completion data, elementary and solvable subfields, mutual disjointness, and the compatible
     families of fields required for Brauer descent. Import the full density and prime-selection
     package from Book 142 rather than reproving Chebotarev, and do not infer the Galois refinements
     from ordinary Moret–Bailly alone.

156. **Hilbert--Blumenthal Moduli and Two-Prime Level Covers** — Construct fine polarized
     real-multiplication moduli, determinant conditions, auxiliary neat level, paired torsion frames,
     twists, components, and geometric monodromy.

157. **Local Geometry of Hilbert--Blumenthal Moduli** — Construct real, good, ordinary,
     nonordinary finite-flat, and semistable local points; prove openness and persistence of the exact
     local conditions used in Moret–Bailly specialization. Permit an elliptic-source neat level
     matching finitely many base-completion tensor seeds, and prove base-field solvability of a
     fixed geometrically connected twist at all sufficiently large good places. At the coefficient
     prime, distinguish finite flatness of one Tate torsion layer from a finite-flat full tower,
     prove ordinary rigidity and trace-$\pm1$ necessity for a good elliptic replacement, and
     construct it by Serre--Tate theory; the required trace-one elliptic curve over the prime
     residue field follows from Book 117's ring-class reciprocity and potential-good-reduction
     package. Section 13.2A proves finite-field Bertini with imposed first jets and the stable
     relative complete-intersection slice once a compatible projective joining model is supplied.
     Section 13.2B proves paired-frame Kummer normalization, a simultaneous regular projective
     equivariant fan, the inverse and full faithfulness over complete traits, the completed
     deformation ring on the already-Mumford-presented side, and the formal family-theta/base-fan
     calculation. Required $(\mathrm{IIT})$ is the first missing relative input: labelled
     reduction does not rule out the square-zero smoothing $XY=\epsilon$ when external $Q=0$.
     Required $(\mathrm{MPE})$ follows only conditionally. Required $(\mathrm{ACE})$ additionally
     needs the bounded conductor presentation $(\mathrm{BCP})$ and single-chart effectivity
     $(\mathrm{AEC}_0)$, ramified conductor descent $(\mathrm{RCD})$, and theta--determinant cusp
     compatibility $(\mathrm{TDC})$. Proposition 13.2B.3b conditionally supplies paired-frame
     normalization and finite-etale twist descent from that complete unframed package. Thus
     $(\mathrm{TCG})_\Sigma$, $(\mathrm{FTJ})$, and the stable integral connecting slice
     $(\mathrm{ICS})$ remain Required; the literal marked-good-section form also requires its
     necessary finite-residue rational-point condition. This conditional singleton boundary is
     not used by Book 158 or the FLT chain, which consume only the proved interior component,
     local seeds, exact frames, and point-centered opens.

158. **Moduli Constructions for Potential Modularity** — Apply Books 156--157 to the target and
     auxiliary residual representations. Match their determinant lines to one corrected
     Hilbert--Blumenthal tensor component, construct the smooth geometrically connected two-prime
     realization space, and export its simultaneous point-centered local opens without
     redeveloping the underlying moduli or local geometry. For the split FLT datum, strengthen
     Book 154's moving pencil to a simply branched presentation. Book 153's transposition
     argument makes its generic normal closure a regular $S_d$-cover, and Book 155 then produces
     a totally real Galois top, completely split at the controlled places and disjoint from the
     full finite avoidance field. Pulling back the universal object supplies both residual
     systems and their named local models on one abelian variety. This route neither assumes nor
     proves a singleton mixed-packet theorem or a toroidal compactification; nonsplit exact local
     algebras still require Book 154's separate common-presentation hypothesis.

159. **Discriminants of Galois Representations** — Develop the general cutout-field, tower,
     compositum, conductor, matrix, lattice, and detailed three-adic exponent calculus. Import the
     canonical finite-flat upper-break, different, and model-stability package from Book 56 under
     compatibility locators. The numerical three-adic ceilings apply only to the displayed modeled
     modules and do not make arbitrary generic extensions finite flat.

160. **Odlyzko Bounds and Fontaine's Argument** — Import the canonical Odlyzko--Poitou formula
     and certified analytic cutoffs from Book 7 and combine them with Book 56's finite-flat ceilings
     and Book 159's three-adic ledger. Prove the degree-$20$, order-$24/48$, and fixed-exponent
     Fontaine criteria while retaining the growing-tower warning. Representation classification
     still requires separate group-theoretic and integral input.

161. **Schoof's Finite-Flat Category over $\mathbf Z[1/2]$** — Classify the finite-flat exponent-three category over $\mathbf Z[1/2]$ under the stated tame dyadic and finite-flat coefficient-prime hypotheses. The resulting cyclotomic-line exact sequence retains the genuine Kummer extension direction and applies only to an actual compatible integral tower.

162. **Quintic Cyclotomic Units and Kummer Arithmetic** — Work in $\mathbf Q(\zeta_5)$ and
     prove its ring of integers, discriminant, and class-number-one theorem from the cyclotomic
     polynomial, the index calculation, and Minkowski's bound. Determine the prime above five, its
     valuations, conjugation, units and cyclotomic units, norms, and associates, and prove the
     fifth-power, Kummer, and coprimality lemmas needed for Diophantine descent.

163. **Cyclotomic Descent for Quintic Fermat-Type Equations** — Develop first- and second-case
     descent in fifth cyclotomic fields, valuation control at the prime above 5, primitive-factor
     decompositions, and well-founded norm descent. Conclude with Fermat's Last Theorem for exponent
     five, leaving the modularity-lifting argument to begin at coefficient primes at least seven.

164. **The Frey Curve: Arithmetic Reduction and the Exact Modular-Method Handoff** — Reduce a putative Fermat solution to exponent five or a prime exponent at least seven, carry out the exponent-three and exponent-four descents, and compute the Frey curve's reduction, residual representation, and signed special deformation datum. The volume is an arithmetic handoff: it does not claim the later conditional modularity, compatible-family, or three-adic steps have closed Fermat's Last Theorem.

165. **Local Conditions for Hardly-Ramified Minimal Deformations** — Construct the local and global hardly-ramified deformation functors for the signed Frey special condition at two and coefficient-linear finite flatness at $\ell\ge7$. The local rings and tangent dimensions are proved without a hidden hypothesis, but no global finite or characteristic-zero point is produced.

166. **Supported Galois Cohomology and Selmer Calculations** — Build the supported global cohomology complex, its Poitou--Tate duality, and the exact equality of tangent and supported-obstruction dimensions for the hardly-ramified problem. Relation bounds and lift existence belong to the next stages.

167. **Relation Obstructions and Poitou--Tate Corrections** — Inject the dual minimal relation space into the correctly supported obstruction group and deduce that the number of relations is at most the number of variables. The balanced presentation does not by itself prove flatness, finiteness, a complete intersection, or a characteristic-zero point.

168. **Compatible Coefficient Systems and Purity** — Import Book 127's curve-carried weak family,
     determinant, good-place purity, and lattice boundaries. Prove coefficient-conjugation and
     carrier independence, prove zero-monodromy raw-to-global preservation formally, and prove
     strict local compatibility where the required return maps and nonzero-monodromy preservation
     are supplied. For a selected cuspidal packet, reduce uniform nonzero-monodromy preservation
     to the exact local-algebraicity input $(\mathrm{HT}_1)$: global class field theory and
     isobaric multiplicity one then prove absolute irreducibility at every coefficient place,
     identify the raw representation with its global semisimplification, and preserve its
     monodromy operator, line, and sign. Book 6 proves the rank-one local-algebraicity theorem and
     Book 47 proves inheritance by geometric subquotients, so the sole missing input in this
     **uniform** route is smooth-proper Hodge--Tate comparison. For the selected place above
     three, protected good unitary carriers, Book 129's all-level finite-flat tower, and Book
     54's rank-one calculation prove absolute irreducibility and preserve the complete dyadic
     SP record without that comparison. No Faltings-height or ambient Tate-semisimplicity
     theorem is needed. Record ambient curve-$H^1$ semisimplicity as a
     stronger optional alternative. Raw
     dyadic-carrier existence and the coefficient-prime boundary remain separate.

169. **The Eisenstein Ideal** — Develop the Eisenstein ideal at prime level, calculate its exact index, and study the cuspidal
     specialization, admissible finite group schemes, completed Hecke piece, and Eisenstein descent.
     Use cotangent lattices to prove formal immersion at the relevant cusp. The scope is the selected
     Eisenstein quotient; full multiplicity one and the complete Shimura-subgroup theory are not
     included.

170. **Hecke-Valued Galois Representations and Nonminimal Reciprocity** — Construct the Hecke-valued Galois representation and the deformation-to-Hecke surjection from verified characteristic-zero branches. Reduced generic order, trace generation, integral coefficient-prime realizations, controlled local types, and the conditional level-change input are all required; unverified local components are not inferred from good traces.

171. **The Minimal Totally-Real Deformation--Hecke Problem** — Assemble the minimal totally real deformation problem, Hecke module, Selmer balance, determinant line, and trace-generated comparison map. The auxiliary detecting sets and later support or patching conclusions are inputs to subsequent volumes, not theorems smuggled into this datum.

172. **Minimal Patching and $R=T$ over Totally Real Fields** — Carry out minimal Taylor--Wiles patching from the exact deformation--Hecke datum and deep-level modules. Exact ring and primary--companion module augmentation suffice for the patch; faithful acting-order augmentation is derived afterward from the proved minimal $R=T$ equality. Adequacy, effective torsors, integral old--new control, and branch realization remain explicit inputs.

173. **Minimal Modularity Lifting** — Import the minimal deformation--Hecke comparison and
     Taylor--Wiles $R=T$ theorem from Books 171--172, then deduce that every characteristic-zero
     minimal point is the exact integral representation of a parallel-weight-two automorphic
     packet. Retain coefficient descent, the prime-five boundary, and every represented local
     hypothesis without repeating patching.

174. **One-Prime Type Complexes and Component Support** — Build the enhanced one-prime type complexes. Choose the strict scalar ray quotient by the odd-exponent local--global theorem, including its exact local Kummer field, vertical unit, and any added conductor spectators. The actual common normalized principal/ray diagram, its isomorphic lifted top legs, and the finite-wild/procyclic strict-node complex are proved. Book 122 computes the Drinfeld leading class and endpoint factors, normalizes the completed tubes, computes cohomology/actions/generization, and combines these with $({\rm RGC}_v)$ to prove $({\rm PNS}_v)_{\rm act}$ and hence $({\rm TPE}_v)$ for the quotient/augmentation rows. Under unit-order coarse descent and the named abelian-Ihara family, the integral projector when $q_v+1$ is a unit proves type-Ihara and primitive residue from the Shapiro constant rows; even when $q_v\equiv-1\pmod\ell$, the augmentation-companion pull is automatic from the abelian-Ihara rows. The two remaining nonbanal algebraic inputs are the quotient-new injection (5.0d) and primitive filtered-cofiber comparison (6.0d). Type-compatible node transport is formal once Book 140's enhanced flagged PEL node-groupoid classification (5.9a) is supplied, but that geometric classification remains a hypothesis. The local special boundary chart and the simultaneous patched common-boundary quotient are proved; the remaining boundary input $({\rm BCD}_v)$ is the relative Cartier-switch transversality theorem (8.2f), after which dimension balance and unique-component routing are formal. The typed filtration and Book 125 prove the generic-residue kernel equality and hence equality of the corresponding integral faithful image orders, so generic support is not another hypothesis. Clean auxiliary augmentation is exact on represented rings, primary and companion complexes, modules, and pairings; its acting-order map remains a surjection until base faithfulness is known.

175. **One-Prime Nonminimal Patching and R=T** — In the scalar-residual line-special range, derive the finite-level one-prime reduced comparison and pointwise modularity from the exact type-complex package. The balanced enhanced obstruction presentation and finiteness force the conductor-one ring to be finite flat over the coefficient DVR. Full $R=T$ is equivalent to characteristic-zero exact-condition adjoint Selmer vanishing at every point. The line is retained in the enhanced tangent calculation; at a monodromy-zero characteristic-zero point its motion is uniquely determined by the two distinct Frobenius characters. Under a coherent clean unpadded $({\rm AUX}_Q)$ system whose arithmetic input supplies exactly $q$ ordered killing primes at every depth, prove that vanishing and full patched and finite $R=T$ by equal-variable rigidity: the enhanced absolute deformation source and diamond source have the same $q$ variables, and Book 174's nonzero primary module free over the diamond source makes the regular source act faithfully. Coherence follows only after those exact-$q$ shadows exist; it does not construct them. The strict ray twist transports the equality to the scalar family and fixed-character fibers, and auxiliary acting-order augmentation is then automatically exact. Without that coherent exact-$q$ auxiliary system, the isolated branchwise torsion-cotangent theorem is the exact alternative input. No generic- or vexing-row theorem and no simultaneous finite-set result is asserted.

176. **Finite-Set Ihara Avoidance and Nonminimal Modularity Lifting** — Develop the direct
     finite-set source-patching route alongside the earlier one-prime and geometric alternatives.
     The scalar desired and avoidance rings have one common, generally nonreduced residual source;
     the avoidance source is integral, while the reduced desired source has component-bijective
     horizontal specialization. Paired relative Taylor--Wiles selection, synchronized definite
     modules, and patching of the expanded sources transfer full support to every desired component,
     giving a finite recovered action with nilpotent kernel and pointwise automorphy. Theorem 1.1J
     packages the prepared auxiliary criterion, Theorem 1.1K the prepared target broad-unipotent
     criterion, and Corollary 1.1L the resulting finite signed-special fibre together with support
     retained for every minimal point chosen later. These criteria do not manufacture their
     reference packets; Book 178 constructs the actual auxiliary packet, upper target packet,
     common definite modules, represented actions, and both source patches before exporting the
     finite-fibre certificate.
     Prove separately the scalar weight-two definite class-set Ihara lemma by strong approximation
     away from the changed finite place; at a non-norm localization its two-map kernel vanishes,
     and Smith normal form gives integral saturation. This removes curve abelian-Ihara from an
     exact-minimal route but does not create lower-level support. The exact remaining
     arithmetic statement on that stronger optional route is $({\rm DLO}_{P_{\rm tar}})$, upper-to-minimal residual occurrence
     for the actual finite set. Classify its places: the upper factor is special and the Frey
     residual factor unramified; controlled places above $3$ are in the regular Mazur range,
     while accidental semistable places may have scalar Frobenius. Proposition 1.3 reduces DLO
     by honest fixed-away-level induction to the one-place outside-$\ell$ level-optimization
     theorem $({\rm FLO}_v)$. Its regular half is Mazur principle. At a repeated-root
     accidental place, general level optimization gives only a spherical-or-special
     alternative, so a stronger application-specific scalar-support theorem is still needed.
     Neither arithmetic proof is present in the corpus. Together with the clean minimal
     structural ledger DLO is $({\rm DMS}_{P_{\rm tar}})$. A finite-free paired countermodel
     shows why upper-side patching, residual monodromy zero, and saturated degeneracy maps do
     not imply DLO.
     DMS constructs the stronger clean minimal $R=T$ datum but is no longer required by the
     preferred pointwise FLT chain once target IAV is supplied. Neither direct route requires a
     several-place old--new cube. For the geometric alternative, reuse Book 84's one-global-module
     several-prime degeneracy map, Book 152's regular-refinement source splitting, Book 7a's
     derived pasting formalism, and Book 145's support algebra, while recording that none proves
     mixed sum-primitivity, routed integral switching, or product-component occurrence. Construct the strict joint scalar ray
     quotient by cross-local prescriptions, so its product group ring does not come from
     potentially diagonal one-place images; fixed-prime augmentation is then formal only on an
     already constructed routed joint cube. Isolate the mixed
     obstruction at two places and identify it over the final coefficient DVR with the torsion
     in the top joint-new quotient, equivalently failure of primitivity for the sum of the two
     top old images; a split-edge countermodel shows generic concentration does not kill it.
     Prove that distinct arithmetic fibers have no common closed stratum, construct the
     parity-correct cube of final inner forms, and isolate the missing integral iterated-switch
     Beck--Chevalley homotopies after proving generic packet-label commutation with the global
     multiplicity module occurring once. Prove the finite-set all-point conclusion
     under the explicit face, cube, mixed-exactness, product-residue, joint-support, simultaneous-
     augmentation, and reciprocity hypotheses. For one named downstream point, construct the
     canonical torsion-free top/adjoint joint carrier and reduce modularity to simultaneous
     branch verification, reciprocity invoked only on that carrier, and occurrence of the one
     global component through the point. Pairwise one-prime inputs do not supply that occurrence.

177. **Potential Modularity of Two-Dimensional Representations** — Construct the paired-frame
     potential-modularity bridge and prove residual automorphy from a lifting-admissible
     specialization. The specialization datum retains the actual packet, local components,
     definite coefficient systems, represented actions, and source-patching hypotheses needed by
     Book 176's prepared finite-set criterion; a bare torsion point or an iteration of one-prime
     comparisons does not supply them. The geometric alternatives remain stronger and require
     their stated localized-Ihara, mixed-exactness, cube, reciprocity, and product-component inputs.
     Book 178 gives the dependency-closed FLT application by constructing the required auxiliary
     and target data explicitly rather than assuming a lifting-admissible specialization.

178. **Auxiliary Dihedral Data and Residual Potential Modularity** — Construct the rational-base
     auxiliary dihedral packet from the corrected ray datum, impose the protected branches at
     $2$, $3$, and $\ell$, and receive both residual coefficient fields in one real-multiplication
     field. A mixed specialization replaces the split-only theorem at the helper places: wholesale
     solvable local packets and split protected packets are placed on one simply branched pencil,
     whose symmetric Galois top has the exact prescribed completions and preserves both joint
     residual images. After specialization, construct the entire actual auxiliary active set,
     avoidance packet, definite coefficient systems, nonzero common residual localization, and
     synchronized source patch required by Book 176, Theorem 1.1J; descent makes the auxiliary Tate
     module automorphic, and a cross-prime stable-lattice comparison identifies the target residual
     member. Then enumerate every target bad place, unramify the zero-monodromy factors, prepare the
     actual nonzero-monodromy set, and construct the upper desired module and the separate target
     source patch required by Theorem 1.1K. The resulting broad action has nilpotent kernel and
     exports both the whole restricted signed-special finite fibre $({\rm SF}_{\rm SP})$ and support
     for any characteristic-zero minimal point chosen afterward.

179. **Compatible Systems of Galois Representations** — Define and analyze compatible systems, coefficient fields, residual members, purity, and recognition from Frobenius data in the precise rank-two range needed later. The volume packages the already constructed automorphic systems and image criteria. Its geometric examples form the weak system from global semisimplifications and retain raw Tate lattices separately, so no Faltings-height, Shafarevich-finiteness, or ambient Tate-semisimplicity theorem is a premise. The final fixed-three handoff distinguishes a merely stable lattice from the selected member's all-level coefficient-prime finite-flat tower; the SP pair supplies odd-tame dyadic behavior and no primitive residual monodromy is required. It does not create a descended base-field family or that selected integral tower at a new coefficient prime.

180. **Brauer Induction and Descent of Automorphy** — Develop the abstract Brauer-induction, Mackey, determinant, Clifford, positivity, and coefficient-descent toolkit. Its theorems act on supplied semisimple representations and packet-local objects; they do not construct the application-specific packets, their overlaps or seed, and cannot recover monodromy erased before the descent input is formed.

181. **Finite Image and the Balanced Minimal-Lift Argument** — Turn the balanced hardly ramified
     presentation into a normalized primitive signed-special lift. The abstract criterion consumes
     only the restricted special-fibre certificate $({\rm SF}_{\rm SP})$; finite restricted image,
     finite-index passage, Carayol trace descent, topological Nakayama, and normalization then give a
     finite free complete-intersection ring and a horizontal integral point with primitive dyadic
     monodromy and compatible finite-flat quotients at the coefficient prime. For a putative
     primitive Fermat solution of prime exponent at least seven, Book 178 has already constructed
     $({\rm SF}_{\rm SP})$ and retained the broad automorphic action. The Frey-range theorem is
     therefore unconditional: it constructs the signed-special lift and only afterward evaluates
     the retained support to make its restriction automorphic. Exact-minimal level lowering remains
     a stronger optional route and is not used.

182. **Potential Automorphy and Galois Refinement of a Chosen Lift** — Begin only after Book 181
     has chosen the primitive signed-special lift. Restrict it to Book 178's prepared target field,
     place it on the already finite minimal quotient of the broad ring, and evaluate the retained
     support; the resulting packet descends through the target-preparation tower to the original
     split symmetric Galois field. Prime-cyclic descent over every elementary fixed field then gives
     a compatible packet array. Parity-correct compact one-split carriers, targetwise dyadic
     spectator constructions, and the finite-flat bridge at one chosen place $\nu\mid3$ prove that
     every selected-three realization is absolutely irreducible, equals its raw multiplicity
     representation, and retains the full dyadic monodromy line and sign. The exported theorem also
     supplies common unramified algebraic pairs away from two, compatible with twisting and Weil
     induction. Uniform all-coefficient Hodge--Tate comparison and strong automorphic type data are
     deliberately stronger than this selected-three theorem and are not required by the final chain.

183. **Brauer Induction for Automorphy Families** — Construct the elementary fixed-field packet array, overlap identities, integral Brauer classes, common polynomials, and virtual Frey-special local record from a supplied controlled top datum. Ordinary elementary packet attachment and the common unramified algebraic Galois pair away from two are proved without principal/dihedral type parameters; finite twisting and Weil induction then form the auxiliary local Mackey objects. Books 118, 122, and 168 supply the targetwise ramified-spectator raw dyadic carriers. Under $(\mathrm{HT}_1)$, cuspidality makes every attached semisimple packet realization absolutely irreducible uniformly; at the selected place above three, the finite-flat certificate of Books 54 and 168 gives the same raw-to-global and signed-special conclusion without smooth-proper Hodge--Tate comparison. Ambient Tate semisimplicity is only a stronger optional alternative. Effectivity is deliberately deferred, and the controlled residual seed is consumed from Book 182 rather than reconstructed.

184. **Brauer Characters and Effectivity of Compatible Families** — Prove characteristic-zero effectivity of the special Brauer virtual class by an application-specific Gram and norm-one calculation. Nonzero special monodromy supplies the needed irreducibility at odd coefficient residue characteristic; the already existing top-packet member at residue characteristic two retains the stated characteristic-zero absolute-irreducibility hypothesis. The fixed-three corollary uses Book 183's finite-flat packet certificate and evaluates the norm-one argument only at the selected place. The result is relative to the controlled packet datum and stops before coherent completion-valued assembly or an integral coefficient-prime model.

185. **Compatible Systems over the Base Field** — Assemble the effective constituents into a coefficient-descended compatible family over the base field, carrying the rational signed special record at two. All-place assembly retains Book 184's characteristic-zero absolute-irreducibility hypothesis at coefficient places above two. A separate selected-member theorem performs completion descent, restriction recovery, auxiliary support cancellation, and dyadic SP cancellation only at one place above three, using Book 183's finite-flat packet certificate and without constructing the other coefficient members. Thus the selected representation is unramified outside $\{2,3\}$. The theorem is rational: the final handoff still requires one selected all-level finite-flat lattice tower. No primitive residual monodromy, residual conductor-one, or family-wide all-odd integral-model record is needed.

186. **Changing the Coefficient Prime while Keeping the Frey Special Place** — Accept either the away-from-two compatible collection or Book 185's selected-three member, retain clean support outside $\{2,3\}$, and transport the full rational special Weil--Deligne record at two. The narrow route is independent of both $(\mathrm{AI}_2)$ and uniform smooth-proper Hodge--Tate comparison. Hand the named member to Book 187's integral construction and Book 161's actual category/classification input as applied by Book 188; do not infer crystallinity, finite flatness, or residual monodromy primitivity. The final consumer needs one all-level tower at the selected place, not the blueprint's stronger family-wide all-odd integral-model record.

187. **The Fixed-Three Integral Local Theory** — Starting from Book 186's cleanly supported selected member, prove that a flat companion $(\mathrm{IC}_3)$ yields crystallinity of Hodge type $\{0,1\}$. Construct the CM-unitary common-multiplier PEL group, its proper good model, and its finite full-component cover of every positive compact division-quaternion carrier after the harmless central saturation of its trivial-character packet level, over a field unramified at $3\ell$. Construct the positive elementary good-abelian carriers and $(\mathrm{IC}_3)$ by product Jacobian, Weil restriction, oldvector embedding, saturation, and finite-flat closure without integral packet idempotents or integral Brauer cancellation. Import Book 182's split evaluated $\mathbf Q_3$ packet and parity-complete basic carriers, and prove that the formerly proposed direct common-norm PEL cover is impossible rather than silently using it. Construct the named all-level Schoof tower for the one selected coefficient-three member using Book 185's proved Galois AUX comparison and clean support at every other odd base prime. The stronger family-wide integral-model record, uniform smooth-proper Hodge--Tate comparison, and automorphic-type parameters are not inputs to the fixed-three tower. The result does not require $(\mathrm{AI}_2)$.

188. **Hardly Ramified $3$-adic Representations** — Verify that Book 187's signed-special tower
     satisfies Book 161's category hypotheses and import its simple-object, Ext, filtration, and
     finite-level trace theorems. Prove the new $\mathcal O$-adic inverse-limit and saturation step,
     identify the global cyclotomic line with the local SP line, and contradict the selected
     member's characteristic-zero absolute irreducibility; the pure-good-prime argument is an
     optional fallback. The residual orientation is proved over an arbitrary residue field, so no
     coefficient descent to $\mathbf F_3$ is assumed. The implication is complete and uses only the coefficient-three member, so
     $(\mathrm{AI}_2)$ is not upstream; the positive-carrier and Galois auxiliary-comparison
     certificates and the preferred controlled rational top are constructed.
