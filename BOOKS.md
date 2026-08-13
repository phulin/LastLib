# A 188-Volume Conditional Curriculum Toward Fermat's Last Theorem

This is the canonical catalog of the 188 retained mathematical manuscripts. The numbering is
a stable topological reading order: every substantial direct manuscript prerequisite has a
smaller number. Mathlib and the companion Class Field Theory development are proof sources,
not axioms, and their transitive imports remain subject to the same no-gap audit.

This repository does **not** presently contain an unconditional dependency-closed proof of
Fermat's Last Theorem. Several later volumes prove bounded conditional theorems while retaining
named Ihara, support, automorphic-seed, simultaneous-level, and coefficient-prime comparison
hypotheses. Those hypotheses are listed separately in `BOOK_DEPENDENCIES.md`; a catalog entry
never upgrades them to conclusions.

The route is conditional but coherent: local and global arithmetic, curve and PEL geometry,
selected trace-formula transfer, compact-curve Galois realization, Eisenstein and explicit
irreducibility, deformation and one-prime patching, potential automorphy and Brauer effectivity,
and the fixed-three finite-flat endgame. Each description records the bounded theorem actually
available from the current manuscript.

## Dependency-ordered catalog

1. **Valuations, DVRs, and Completions** — Begin with valuations and absolute values, then study valuation rings, discrete valuation rings, uniformizers, residue fields, maximal-ideal filtrations, completions, extension of valuations, and integral closure in finite extensions. Emphasize the finiteness and compatibility theorems that permit seamless passage among a local field, its valuation ring, its residue field, and its completion.

2. **Finite Extensions of Local Fields** — Study finite extensions of complete discretely valued fields through ramification index,
   residue degree, the fundamental equality, norms and traces, decomposition and inertia groups,
   unramified and totally ramified extensions, and unit filtrations. Develop Krasner's lemma and use
   it to prove finiteness, up to isomorphism, of extensions of bounded degree. The final chapters
   apply this structure to residue-field Frobenius and to number fields with prescribed local
   completions.

3. **Ramification Theory** — Build the finer structure of ramified extensions needed for Galois representations. Cover tame and wild ramification, lower and upper ramification filtrations, Herbrand functions, the different, discriminant exponents, ramification of towers, and Artin and Swan conductors for finite representations. The book should culminate in formulas relating ramification groups, conductors, and discriminants strongly enough to support later calculations for elliptic curves, torsion fields, finite-flat representations, and Fontaine-style discriminant estimates.

4. **Adeles and Ideles** — Develop finite and full adeles and ideles as restricted products over the places of a number
   field. Study their topologies, diagonal embeddings, compactness theorems, idele class groups,
   local-global norm maps, and ray-class quotients. Conclude by showing how the same adelic language
   supports both global reciprocity and automorphic forms.

5. **Local Class Field Theory** — Give a systematic account of reciprocity for nonarchimedean local fields. Construct the
   local Artin map, calculate it on uniformizers and units, prove functoriality under finite
   extensions, characterize norm subgroups, and establish the existence theorem for abelian
   extensions. Conclude with the classification of continuous one-dimensional Galois characters in
   terms of characters of the multiplicative group.

6. **Global Class Field Theory** — Develop global reciprocity from the idele class group and prove its compatibility with every
   local reciprocity map. Treat existence and norm theorems, ray class fields, ramification,
   Frobenius elements, and Hecke characters. Include the local and global Brauer invariants and their
   reciprocity law in the form used by Tate and Poitou–Tate duality.

7. **Analytic Foundations for Odlyzko--Poitou Bounds** — Develop completed Dedekind zeta
   functions, explicit formulas with admissible test functions, archimedean gamma estimates, and
   rigorously certified numerical lower bounds for root discriminants in the relevant degree and
   signature ranges. The subject is restricted to discriminant bounds; Chebotarev density is
   treated separately.

8. **Ample Line Bundles, Hilbert Polynomials, and Symmetric Powers** — Starting from relative
   Proj and the elementary theory of projective morphisms, develop ample and very ample line
   bundles, descent of very ampleness, Hilbert polynomials, and projective embeddings for curves and
   abelian schemes. Prove representability for symmetric powers and for the particular Hilbert
   functors arising in their moduli, without treating general Quot schemes.

9. **Divisors, Riemann--Roch, and Duality on Relative Curves** — Develop Cartier and Weil
   divisors, line bundles, degrees in families, residues, dualizing sheaves, Riemann–Roch, and Serre
   duality for smooth and nodal relative curves. Conclude with the divisor and differential theory
   used by Picard schemes, modular curves, and formal-immersion arguments.

10. **Faithfully Flat Descent in Algebraic Geometry** — Prove effective fpqc descent for
   modules, algebras, finite projective objects, schemes, morphisms, line bundles, finite-flat group
   objects, and the quasi-projective cases needed by the moduli constructions.

11. **Normalization and Regular Models of Arithmetic Curves** — Prove the required finiteness
   of normalization and construct regular proper models of curves over Dedekind schemes. Treat the
   excellent one- and two-dimensional cases occurring in modular, Shimura, and semistable reduction
   problems.

12. **Blowups and Intersection Theory on Arithmetic Surfaces** — Develop blowups, strict
   transforms, resolution of the relevant surface singularities, intersection multiplicities,
   projection formulas, adjunction, and component pairings. The scope is regular arithmetic surfaces,
   not general higher-dimensional intersection theory.

13. **Moduli Stacks for Modular and PEL Problems** — Develop stacks, quotient atlases, rigidification, finite quotients, and coarse descent for the modular, Hilbert, and quaternionic PEL problems actually used later. The volume proves only the bounded representability and descent interfaces stated in its reusable theorem package; it supplies no unitary-surface realization.

14. **Arithmetic Spectral Sequences and Derived Cohomology** — Starting from the general
   theory of derived categories and spectral objects, construct derived global sections, derived
   tensor and Hom, filtered complexes, and exact couples in the categories of arithmetic sheaves.
   Prove convergence and comparison theorems for the Leray, Hochschild–Serre, hypercohomology, and
   nearby-cycle spectral sequences.

15. **Coherent Cohomology in Proper Families** — Prove finiteness, semicontinuity, coherent
   base change, formal functions, and representability consequences for the proper curves, abelian
   schemes, and low-dimensional PEL families used here. Apply these theorems to Picard
   representability, Hodge bundles, and integral modular forms.

16. **Semistable Curves, Dual Graphs, and Component Groups** — Study nodal and semistable
   models, graph Jacobians, relative Picard functors, monodromy pairings, and component groups under
   base change and finite correspondences.

17. **Finite Étale Covers and Fundamental Groups** — Develop étale morphisms, henselian neighborhoods, finite étale descent, Galois categories,
   geometric points, and the étale fundamental groups of curves and arithmetic bases. Prove the
   required base-change and specialization exact sequences and compare them with absolute Galois
   groups. Conclude by constructing continuous Galois representations from geometric covers and
   locally constant sheaves.

18. **Derived Étale and $\ell$-adic Cohomology** — Construct finite-level and continuous $\ell$-adic cohomology, derived completion, cup products, traces, Galois actions, and perfect complexes for the curve and abelian-scheme range. Geometric proper and smooth base-change is prepared as a morphism and is imported only in the next volume, not assumed here.

19. **Proper and Smooth Base Change** — Prove proper and smooth base change for the constructible torsion and $\ell$-adic complexes needed on curves and abelian schemes, with all noetherian, invertibility, and finiteness hypotheses visible. The conclusions are limited to the stated geometric range and do not assert an unrestricted higher-dimensional six-functor formalism.

20. **Étale Duality and Trace Maps for Curves** — Develop trace maps, Poincaré duality, and compatibility with finite correspondences for smooth proper curves and the open or semistable curve situations explicitly treated. Surface duality and the retired unitary-surface branch are outside the theorem.

21. **Étale Sheaves and Cohomology on Curves** — Give a unified account of étale cohomology for smooth proper and semistable curves. Study
   constructible and lisse sheaves, continuous ℓ-adic cohomology in low degrees, proper and smooth
   base change, cup products, Frobenius, trace maps, and Poincaré duality. The culminating object is
   (H^1_{\mathrm{\acute et}}), carrying both a continuous Galois action and functorial actions of
   algebraic correspondences.

22. **Nearby Cycles and Monodromy for Semistable Curves** — Compute nearby cycles, vanishing cycles, monodromy, and the weight complex for strict semistable curves. The volume proves the nodal-curve formulas used by modular and quaternionic models and does not claim a general surface semistable-reduction theorem.

23. **Lefschetz Trace Formulas for Curves** — Prove the Lefschetz trace formulas required for finite correspondences on proper curves, including the local terms and Frobenius conventions used downstream. The scope is the curve case; no surface trace formula is used to close the curriculum.

24. **Continuous Cohomology of Profinite Groups** — Develop continuous cohomology for profinite groups acting on discrete or topological modules.
   Construct homogeneous and inhomogeneous cochains, long exact sequences, connecting maps,
   restriction and corestriction, inflation–restriction, Shapiro's lemma, and cup products, and
   compare the cochain and derived-functor constructions. Applications identify deformation-theoretic
   tangent and obstruction spaces with low-degree cohomology.

25. **Relative Picard Schemes and Jacobians** — Construct Picard sheaves and schemes,
   rigidification, identity components, Jacobians, Abel–Jacobi and Albanese maps, polarizations, and
   functoriality under finite maps and correspondences.

26. **Finite Locally Free Schemes and Algebras** — Study finite locally free morphisms through finite projective algebras. Develop rank, fibers,
   base change, composition, dual modules, finite flatness over local rings and DVRs, and faithfully
   flat descent. The principal structural result is that finite flat morphisms of constant rank are
   stable under every operation used later for group schemes.

27. **Affine Group Schemes and Hopf Algebras** — Introduce affine group schemes through commutative Hopf algebras and prove the
   anti-equivalence between the two viewpoints. Develop subgroup schemes, kernels, the quotient
   constructions needed for finite groups, base change, morphisms, and exact sequences. Throughout,
   translate geometric assertions into explicit Hopf-algebra calculations.

28. **Finite Flat Commutative Group Schemes** — Specialize affine group-scheme theory to finite flat commutative groups over local and
   arithmetic bases. Study rank and fibers, connected and étale parts, kernels of multiplication,
   schematic closure of generic-fiber subgroups, and finite-flat subgroups of abelian schemes. Prove
   the exactness and closure theorems needed to model residual Galois representations integrally.

29. **fppf Cohomology and Kummer Theory** — Develop low-degree fppf cohomology, torsors,
   Kummer sequences, Picard and Brauer interpretations, descent boundaries, and compatibility with
   finite-flat group schemes.

30. **Local Galois Cohomology** — Apply continuous cohomology to absolute Galois groups of local fields. Compute and bound
   (H^0), (H^1), and (H^2) for finite modules and ℓ-adic representations, study unramified
   cohomology and restriction to inertia, prove cohomological-dimension results and the local Euler
   characteristic formula, and give coefficient-uniform Kummer calculations. The final dimension
   formulas govern local deformation conditions and hardly-ramified relation calculations.

31. **Tate Local Duality** — Develop the local duality pairing between a finite Galois module and its Tate-twisted dual.
   Prove continuous Hilbert 90 and the finite-module Tate–Nakayama theorem, construct the local
   invariant and cup-product pairing, and establish perfectness. Conclude by identifying annihilators
   of natural local conditions and deriving the dimension identities used for dual deformation
   conditions.

32. **Global Galois Cohomology and Selmer Groups** — Develop Galois cohomology for number fields with ramification restricted to a finite set of
   places. Define localization maps and general Selmer structures through subspaces of local (H^1),
   construct dual Selmer structures, and prove the exact sequences comparing global and local
   classes. Culminate in the identification of the tangent space of a global deformation problem
   with its associated Selmer group.

33. **Poitou–Tate Duality** — Prove the global duality theorem relating a Selmer condition to its dual. Develop the
   Poitou–Tate exact sequence, local-global pairings, orthogonal complements, global Euler
   characteristic formulas, and dimension identities for Selmer and dual Selmer groups. The final
   numerical formula determines how many Taylor–Wiles primes are required to kill the dual Selmer
   group.

34. **Cartier Duality** — Develop Cartier duality for finite flat commutative group schemes. Construct the dual through
   Hopf algebras, identify constant and diagonalizable examples, prove biduality, and study pairings,
   kernels, base change, and generic fibers. Relate this theory to duality on the torsion of elliptic
   curves and abelian varieties and to Tate-twisted Galois modules.

35. **Abelian Schemes, Isogenies, and Polarizations** — Develop dual abelian schemes, finite
   flat kernels, quotients by finite subgroup schemes, Weil pairings, polarizations, and extension
   over normal bases. Include the odd-isogeny preservation of full two-torsion needed by the Frey
   argument.

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

41. **Heights and the Mordell--Weil Theorem** — Construct Weil and Néron–Tate heights,
   Northcott finiteness, height pairings, and finite generation of rational points on polarized
   abelian varieties. Conclude with the finite-generation theorem used in Mazur's
   Eisenstein-quotient argument.

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
   correspondences, polarizations, and rational structures.

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
   integral base-change and compatible-quotient results needed for stable lattices.

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
   Tate modules.

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

104. **Global Jacquet--Langlands** — Prove global Jacquet--Langlands for noncharacter algebraic weight-two packets whose ramified finite factors lie in the constructed special or tame-dihedral local range. The trace-formula comparison gives multiplicity, good Hecke data, and the compact one-split inverse transfer under its parity and eligible-place hypotheses; primitive wild and excluded dyadic packets are not covered.

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

109. **Solvable Base Change and Descent** — Iterate cyclic base change through towers of cyclic extensions to obtain solvable base change
   and descent. Resolve character-twist ambiguities, prove independence of the chosen tower, and
   control local types throughout the tower. The main theorem moves automorphy both up and down
   suitable solvable totally real extensions.

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
   descent for Hilbert and quaternionic data.

119. **Quaternionic PEL Functors and Representability** — Construct the moduli functors,
   determinant and polarization conditions, fine covers, representability, and universal abelian
   families for the required quaternionic curves.

120. **Uniformization, Components, and Hecke Descent for Shimura Curves** — Prove complex
   uniformization, identify connected components and canonical descent, compare fine and coarse
   levels, and descend universal isogenies and Hecke correspondences.

121. **Good Integral Models of Quaternionic Shimura Curves** — Construct smooth PEL models at
   good primes, extend universal abelian schemes and Hecke correspondences, and prove smooth/proper
   base change and integral comparison for their cohomology.

122. **Semistable Models and Monodromy of Quaternionic Shimura Curves** — Construct the one-step Iwahori semistable models of the direct quaternionic PEL curves in the verified odd and dyadic tensor-split cases. Compute the two branches, nodes, graph monodromy, Hecke action, and raw packet parameter, while leaving Ihara saturation and raw-to-global semisimplification to separately stated hypotheses.

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

127. **Galois Representations Attached to Weight-Two Automorphic Forms** — Assemble the cohomological extraction into a weakly compatible family for weight-two packets that possess a proved compact one-split carrier. Global Jacquet--Langlands supplies that carrier only when an odd nonempty eligible special or tame-dihedral set exists; no surface substitute, strict bad-place compatibility, or canonical finite-flat lattice is asserted.

128. **Local--Global Compatibility for Weight-Two Galois Representations** — Prove the stated local--global recognition results at good, split-Iwahori special, and selected tame places for the raw rank-two carrier. Passage to the global semisimplification requires the explicit local-preservation condition, supplied at a coefficient place by residual absolute irreducibility but not uniformly for every embedding.

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

138. **Integral Local Types and Type Lattices** — Construct integral primary and companion lattices for principal, special, depth-zero dihedral, and tame positive-depth local types, together with their represented enhanced deformation conditions. Banality, ordering, sign, and saturation hypotheses are retained, and primitive wild or ramified dyadic positive-depth types are excluded.

139. **Ihara Theory and Saturated Degeneracy Maps on Shimura Curves** — Compute the two-map tree kernel and the integral degeneracy filtration for the clean compact Shimura curves. Saturation and residual injectivity are conditional on the named localized abelian Ihara vanishing; strong approximation and the geometry developed here do not prove that vanishing.

140. **Integral Level Change and Jacquet--Langlands Comparison** — Compare one-prime integral level change with selected Jacquet--Langlands using the corrected Ihara filtration, graph lattice, and faithful Hecke orders. The theorem remains conditional on abelian Ihara and datum-specific node uniformization. Relative to the separate abelian Ihara input, generic support in the clean constant-coefficient block is proved from Book 125's component-routed semisimple decomposition and the corrected filtration; the book proves neither a type-Ihara theorem nor a several-prime comparison.

141. **Dickson Classification and Adequate Residual Image** — Develop the Dickson classification and the adequate-image consequences needed to select Taylor--Wiles elements in coefficient characteristic at least seven. The small-image and coefficient-five boundaries are stated explicitly and no automorphy conclusion follows from adequacy alone.

142. **The Chebotarev Density Theorem** — Develop Frobenius conjugacy classes and Dirichlet
   density, then use ray partial zeta functions, Poisson–Mellin analysis, finite-order Hecke
   characters, and logarithmic Euler products to prove the required pole, holomorphy, and
   nonvanishing statements at one. Prove abelian density by character orthogonality and full
   Chebotarev by cyclic fixed-field reduction and centralizer counting. Derive finite-quotient prime
   selection, profinite Frobenius density, and the precise Brauer–Nesbitt and
   representation-transport interfaces, without claiming effective bounds or general Artin
   holomorphy.

143. **Taylor–Wiles Primes** — Study the auxiliary primes that alter a deformation problem while controlling global
   cohomology. Import the full finite-quotient Chebotarev theorem from Book 142 and combine it with
   the residual-image detector to impose simultaneous congruence and Frobenius conditions. Describe
   the enlarged local rings and calculate their tangent
   contributions. Conclude with the existence of Taylor–Wiles sets of prescribed cardinality and
   level that kill the dual Selmer group.

144. **Taylor–Wiles Systems** — Study the towers of deformation rings, Hecke algebras, and modules obtained by adjoining
   Taylor–Wiles primes. Develop the finite quotient group actions, augmentation maps, transition
   maps, and compatibility across levels, and isolate the structural properties that survive passage
   to the inverse limit.

145. **Patching Modules and Rings** — Construct patched deformation rings and modules from Taylor–Wiles towers. Develop the
   inverse-limit or ultraproduct construction, auxiliary power-series and completed group rings,
   support and depth calculations, and freeness over the auxiliary ring. Culminate in the patched
   pair ((R_\infty,M_\infty)) with the dimension and depth properties needed for (R=T).

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

152. **Deep-Level Quaternionic Modules and Diamond Actions** — Construct deep-level quaternionic modules with effective diamond torsors, pairings, finite shadows, and exact module augmentation. Old--new control is a separate hypothesis needed to reach hyperspecial level. Exact acting-image augmentation is not a consequence of group-ring freeness and is deferred to a later faithful comparison.

153. **Hilbert Irreducibility and Arithmetic Approximation** — Develop Hilbert irreducibility together with weak approximation, prescribed decomposition and
   completion data at finitely many places, linear disjointness, avoidance of given extensions, and
   totally real specialization. Use the finiteness of local extensions of bounded degree to reduce
   simultaneous local requirements to finitely many conditions. Conclude with the specialization
   theorems needed for Moret–Bailly and automorphy fields.

154. **Moret–Bailly’s Theorem** — Develop moving lemmas for zero-cycles, symmetric powers, configuration spaces, and irreducible
   zero-cycle approximation, then prove Moret–Bailly's local-open existence theorem in the required
   totally-real form. Derive the linear-disjointness and splitting refinements used later. The
   main theorem turns prescribed local points on a moduli space into a global point over a
   controlled totally real extension.

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
   local conditions used in Moret–Bailly specialization.

158. **Moduli Constructions for Potential Modularity** — Apply Books 156--157 to the target and
   auxiliary residual representations. Match their determinant lines to one corrected
   Hilbert--Blumenthal tensor component, construct the smooth geometrically connected two-prime
   realization space, and export its simultaneous local opens and avoidance datum without
   redeveloping the underlying moduli or local geometry.

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
   carrier independence, strict local compatibility where raw-to-global preservation and return
   maps are supplied, and the resulting bad-place purity and conductor independence; retain the
   all-embedding Frey-special record as a named later hypothesis.

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

174. **One-Prime Type Complexes and Component Support** — Build the enhanced one-prime type complexes and isolate the first missing input as the typed parahoric extension and ramified nearby-cycle theorem. Under that theorem, the accompanying incidence and unit-order coarse-descent hypothesis, and the separate type-Ihara, primitive-residue, type-compatible node-uniformization, and nonminimal boundary chart-and-dimension hypotheses, prove the strict one-prime complexes and topological component-support reductions. The typed filtration and Book 125 also prove the generic-residue kernel equality and hence equality of the corresponding integral faithful image orders, so generic support is not another hypothesis. Clean auxiliary augmentation is exact on represented rings, primary and companion complexes, modules, and pairings; its acting-order map remains a surjection until base faithfulness is known.

175. **One-Prime Nonminimal Patching and R=T** — Derive the finite-level one-prime reduced comparison and pointwise modularity from the exact type-complex package. Full $R=T$ is equivalent to the explicitly isolated generic-rigidity theorem: vertical torsion-freeness and vanishing of every characteristic-zero enhanced fixed-condition tangent--Selmer group, including the flag tangent at monodromy-zero boundary points. Under that theorem—and the strict ray twist for the scalar family—all one-prime auxiliary acting-order augmentations are automatically exact; no patched reduced comparison or simultaneous finite-set result is asserted.

176. **Nonminimal Modularity Lifting** — Import the conditional one-prime Ihara, type-complex,
   component-support, reduced-$R=T$, and pointwise modularity packages from Books 139, 174, and
   175. Isolate the mixed obstruction at two places and prove the finite-set pointwise conclusion
   under the explicit face, cube, mixed-exactness, product-residue, joint-support, simultaneous-
   augmentation, and reciprocity hypotheses; pairwise one-prime inputs do not supply them.

177. **Potential Modularity of Two-Dimensional Representations** — Construct the paired-frame potential-modularity bridge and prove its residual automorphy conclusion only for a lifting-admissible specialization. Localized Ihara, the actual multi-place mixed exactness, product-residue comparison, joint support, coherent simultaneous ring--complex--module--action--pairing augmentation, and finite-set reciprocity are unresolved, so the advertised unconditional existence theorem is not ready.

178. **Auxiliary Dihedral Data and Residual Potential Modularity** — Construct the two-prime Hilbert--Blumenthal specialization and dihedral residual packet from a supplied compatible corrected relative ray datum and a complete admissibility ledger. The compact carrier is obtained in the selected range, but the ray compatibility over a general totally real base, post-specialization cleanability, and its integral comparison hypotheses remain conditional; Book 182 proves the rational-base ray specialization used by the Frey route.

179. **Compatible Systems of Galois Representations** — Define and analyze compatible systems, coefficient fields, residual members, purity, and recognition from Frobenius data in the precise rank-two range needed later. The volume packages the already constructed curve systems and image criteria; it does not create a descended base-field family or an integral lattice at a new coefficient prime.

180. **Brauer Induction and Descent of Automorphy** — Develop the abstract Brauer-induction, Mackey, determinant, Clifford, positivity, and coefficient-descent toolkit. Its theorems act on supplied representations and packet data; they do not construct the application-specific automorphic packets, their overlaps, or the missing Frey-special seed.

181. **Finite Image and the Balanced Minimal-Lift Argument** — Turn the balanced hardly-ramified presentation into a normalized primitive special lift under the stated exact automorphic seed. The seed is the sole new arithmetic hypothesis and is not constructed here, so the lift theorem is conditional.

182. **Potential Automorphy and Galois Refinement of a Chosen Lift** — Prove the corrected relative-ray compatibility in the rational-base Frey case, isolate the missing split paired-frame seeds over the dyadic and target-prime base completions and the missing common moving presentation for the actual mixed local packets, reduce the rest of normal-closure control to disjointness between the avoidance field and the constant field of that presentation's Galois closure, and use the normal top itself as the seed field so that upward transfer is vacuous. The post-specialization clean minimal SP occurrence and the later all-elementary attachment and descent, raw dyadic carrier, and uniform SP preservation remain unproved; the volume does not make its downstream compatible family unconditional.

183. **Brauer Induction for Automorphy Families** — Construct the elementary fixed-field packet array, overlap identities, integral Brauer classes, common polynomials, and virtual Frey-special local record from a supplied controlled top datum. Effectivity is deliberately deferred and the missing controlled seed is not supplied.

184. **Brauer Characters and Effectivity of Compatible Families** — Prove characteristic-zero effectivity of the special Brauer virtual class by an application-specific Gram and norm-one calculation. Nonzero special monodromy supplies the needed irreducibility at odd coefficient residue characteristic; the characteristic-two member retains the stated absolute-irreducibility hypothesis. The result is relative to the controlled packet datum and stops before coherent completion-valued assembly or an integral coefficient-prime model.

185. **Compatible Systems over the Base Field** — Assemble the effective constituents into a coefficient-descended compatible family over the base field, carrying the rational signed special record at two. All-place assembly retains the characteristic-two absolute-irreducibility hypothesis of Book 184; without it, the construction still covers every coefficient place away from two, including those above three. The construction remains conditional on the controlled top datum and provides no crystallinity, finite-flat lattice, or coefficient-prime comparison at three.

186. **Changing the Coefficient Prime while Keeping the Frey Special Place** — Select the coefficient-three member of an already assembled compatible family and transport the full rational special Weil--Deligne record at two. Hand the named member to Book 187's integral construction and Book 161's actual category/classification input as applied by Book 188; do not infer crystallinity, finite flatness, or residual monodromy primitivity.

187. **The Fixed-Three Integral Local Theory** — Develop the fixed-three integral local theory that would turn the rational member into one named all-level finite-flat lattice, measure its residual dyadic thickness, and verify that every level lies in Book 161's Schoof category. The conclusion requires the missing coefficient-prime and clean-support certificates and is therefore conditional.

188. **Hardly Ramified $3$-adic Representations** — Verify that Book 187's signed-special tower
   satisfies Book 161's category hypotheses and import its simple-object, Ext, filtration, and
   finite-level trace theorems. Prove the new $\mathcal O$-adic inverse-limit and saturation step,
   identify the global cyclotomic line with the local SP line, and derive the pure-good-prime
   contradiction. The implication is complete, while the audited upstream certificates remain
   conditional.
