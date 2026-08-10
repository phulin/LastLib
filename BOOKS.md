# An Axiom-Free Curriculum for Fermat's Last Theorem

This is the canonical topical list of the 192 mathematical textbooks in the chosen axiom-free
route to Fermat's Last Theorem. The mathematical background already present in Mathlib is
assumed. The companion Class Field Theory and Chebotarev developments supply those two bodies of
results, so their proofs are not split into additional `N...` volumes here. They remain genuine
prerequisites: no theorem supplied by either development is treated as an axiom.

`B001`–`B071` are stable original identifiers. Where a broad B-numbered book overlaps specialist
`N...` monographs, the B-numbered book is retained as a capstone treatment that unifies the
subject. Topical order is not dependency order; substantial prerequisites are recorded in
`BOOK_DEPENDENCIES.md`.

The route choices are fixed: cuspidal trace-formula proofs of Jacquet–Langlands and cyclic base
change for the required cohomological packets; PEL Shimura geometry for weight-two Galois
realization; Mazur's formal-immersion argument together with the two required genus-two
calculations for Frey irreducibility; separate cyclotomic descent at exponent five; and the
balanced hardly-ramified lift, Brauer-compatible-family, and Schoof-at-three endgame. The list
contains mathematical textbooks only. Each description gives a mathematical narrative and
culminates in a major theorem. New books are scoped as coherent topics targeting approximately
10,000–16,000 words each.

## I. Local and Global Arithmetic

B001. **Valuations, DVRs, and Completions**
   Begin with valuations and absolute values, then study valuation rings, discrete valuation rings, uniformizers, residue fields, maximal-ideal filtrations, completions, extension of valuations, and integral closure in finite extensions. Emphasize the finiteness and compatibility theorems that permit seamless passage among a local field, its valuation ring, its residue field, and its completion.

B002. **Finite Extensions of Local Fields**
   Study finite extensions of complete discretely valued fields through ramification index,
residue degree, the fundamental equality, norms and traces, decomposition and inertia groups,
unramified and totally ramified extensions, and unit filtrations. Develop Krasner's lemma and use
it to prove finiteness, up to isomorphism, of extensions of bounded degree. The final chapters
apply this structure to residue-field Frobenius and to number fields with prescribed local
completions.

B003. **Ramification Theory**
   Build the finer structure of ramified extensions needed for Galois representations. Cover tame and wild ramification, lower and upper ramification filtrations, Herbrand functions, the different, discriminant exponents, ramification of towers, and Artin and Swan conductors for finite representations. The book should culminate in formulas relating ramification groups, conductors, and discriminants strongly enough to support later calculations for elliptic curves, torsion fields, finite-flat representations, and Fontaine-style discriminant estimates.

B004. **Adeles and Ideles**
   Develop finite and full adeles and ideles as restricted products over the places of a number
field. Study their topologies, diagonal embeddings, compactness theorems, idele class groups,
local-global norm maps, and ray-class quotients. Conclude by showing how the same adelic language
supports both global reciprocity and automorphic forms.

B005. **Local Class Field Theory**
   Give a systematic account of reciprocity for nonarchimedean local fields. Construct the
local Artin map, calculate it on uniformizers and units, prove functoriality under finite
extensions, characterize norm subgroups, and establish the existence theorem for abelian
extensions. Conclude with the classification of continuous one-dimensional Galois characters in
terms of characters of the multiplicative group.

B006. **Global Class Field Theory**
   Develop global reciprocity from the idele class group and prove its compatibility with every
local reciprocity map. Treat existence and norm theorems, ray class fields, ramification,
Frobenius elements, and Hecke characters. Include the local and global Brauer invariants and their
reciprocity law in the form used by Tate and Poitou–Tate duality.

N081. **Analytic Foundations for Odlyzko–Poitou Bounds** — Develop completed Dedekind zeta
functions, explicit formulas with admissible test functions, archimedean gamma estimates, and
rigorously certified numerical lower bounds for root discriminants in the relevant degree and
signature ranges. The subject is restricted to discriminant bounds; Chebotarev density is
treated separately.

## II. Algebraic-Geometric Foundations and Descent

N001. **Ample Line Bundles, Hilbert Polynomials, and Symmetric Powers** — Starting from relative
Proj and the elementary theory of projective morphisms, develop ample and very ample line
bundles, descent of very ampleness, Hilbert polynomials, and projective embeddings for curves and
abelian schemes. Prove representability for symmetric powers and for the particular Hilbert
functors arising in their moduli, without treating general Quot schemes.

N002. **Divisors, Riemann–Roch, and Duality on Relative Curves** — Develop Cartier and Weil
divisors, line bundles, degrees in families, residues, dualizing sheaves, Riemann–Roch, and Serre
duality for smooth and nodal relative curves. Conclude with the divisor and differential theory
used by Picard schemes, modular curves, and formal-immersion arguments.

N003. **Normalization and Regular Models of Arithmetic Curves** — Prove the required finiteness
of normalization and construct regular proper models of curves over Dedekind schemes. Treat the
excellent one- and two-dimensional cases occurring in modular, Shimura, and semistable reduction
problems.

N004. **Blowups and Intersection Theory on Arithmetic Surfaces** — Develop blowups, strict
transforms, resolution of the relevant surface singularities, intersection multiplicities,
projection formulas, adjunction, and component pairings. The scope is regular arithmetic surfaces,
not general higher-dimensional intersection theory.

N005. **Semistable Curves, Dual Graphs, and Component Groups** — Study nodal and semistable
models, graph Jacobians, relative Picard functors, monodromy pairings, and component groups under
base change and finite correspondences.

N007. **Faithfully Flat Descent in Algebraic Geometry** — Prove effective fpqc descent for
modules, algebras, finite projective objects, schemes, morphisms, line bundles, finite-flat group
objects, and the quasi-projective cases needed by the moduli constructions.

N008. **Moduli Stacks for Modular and PEL Problems** — Develop fibered categories, stacks,
quotient-stack atlases, inertia, rigidification, finite quotients, and coarse descent for
generalized elliptic curves and for Hilbert, quaternionic, and unitary PEL moduli problems.

N009. **Coherent Cohomology in Proper Families** — Prove finiteness, semicontinuity, coherent
base change, formal functions, and representability consequences for the proper curves, abelian
schemes, and low-dimensional PEL families used here. Apply these theorems to Picard
representability, Hodge bundles, and integral modular forms.

N010. **Arithmetic Spectral Sequences and Derived Cohomology** — Starting from the general
theory of derived categories and spectral objects, construct derived global sections, derived
tensor and Hom, filtered complexes, and exact couples in the categories of arithmetic sheaves.
Prove convergence and comparison theorems for the Leray, Hochschild–Serre, hypercohomology, and
nearby-cycle spectral sequences.

N011. **Cotangent Complexes, Perfect Complexes, and Determinant Lines** — Treat cotangent
complexes in the lci and deformation cases, perfectness, Tor amplitude, determinants, base change,
and the determinant-line calculations used in PEL smoothness and patching. Do not develop the
unneeded general theory of derived algebraic geometry.

N012. **Formal Schemes, GAGA, and Algebraization** — Develop adic formal schemes, completion,
formal fibers, Grothendieck existence in the required proper cases, complex GAGA, and
algebraization of formal curves and abelian varieties.

## III. Étale, fppf, and Galois Cohomology

B049. **Finite Étale Covers and Fundamental Groups**
    Develop étale morphisms, henselian neighborhoods, finite étale descent, Galois categories,
geometric points, and the étale fundamental groups of curves and arithmetic bases. Prove the
required base-change and specialization exact sequences and compare them with absolute Galois
groups. Conclude by constructing continuous Galois representations from geometric covers and
locally constant sheaves.

B050. **Étale Sheaves and Cohomology on Curves**
    Give a unified account of étale cohomology for smooth proper and semistable curves. Study
constructible and lisse sheaves, continuous ℓ-adic cohomology in low degrees, proper and smooth
base change, cup products, Frobenius, trace maps, and Poincaré duality. The culminating object is
(H^1_{\mathrm{\acute et}}), carrying both a continuous Galois action and functorial actions of
algebraic correspondences.

N014. **Derived Étale and ℓ-adic Cohomology** — Construct étale cohomology through derived global
sections and develop continuous ℓ-adic coefficients from inverse systems. Treat constructible and
lisse sheaves, continuous Galois actions, and the finiteness theorems required for curves, abelian
schemes, and the selected Shimura surfaces.

N015. **Proper and Smooth Base Change** — Prove constructibility, proper base change, smooth base
change, local acyclicity, and specialization for the relative curves, abelian schemes, and PEL
families in the FLT route.

N016. **Étale Duality and Trace Maps in Low Dimension** — Construct compact support, trace maps,
cup products, and Poincaré duality for smooth curves and surfaces, together with the relative and
semistable forms used here. Prove compatibility with base change, algebraic correspondences, and
Galois actions.

N017. **Nearby Cycles and Monodromy in Dimensions One and Two** — Develop nearby and vanishing
cycles for the strictly semistable curves and surfaces occurring in the proof. Treat inertia,
monodromy filtrations, the low-degree weight spectral sequence, Picard–Lefschetz formulas, dual
graphs, and component pairings.

N018. **Lefschetz Trace Formulas for Curves and Surfaces** — Construct Frobenius and compactly
supported étale cohomology over finite fields, prove Künneth and cycle-class compatibilities, and
establish the Grothendieck–Lefschetz formula for endomorphisms and the correspondences used here.
Derive rationality and functional equations for the required zeta functions.

N019. **Weights, Hard Lefschetz, and Weil Bounds in Low Dimension** — Develop weights and purity
for the lisse sheaves and smooth proper varieties occurring in dimensions one and two. Prove the
required hard-Lefschetz and Riemann-hypothesis statements, recover the Hasse–Weil bounds for
curves, and obtain the Frobenius purity used to isolate weight-two constituents in Shimura-surface
cohomology.

N020. **Betti, de Rham, and Étale Comparison for Curves** — Construct singular (co)homology,
period pairings, complex comparison isomorphisms, and compatibility with cycles, Hecke
correspondences, polarizations, and rational structures.

N021. **fppf Cohomology and Kummer Theory** — Develop low-degree fppf cohomology, torsors,
Kummer sequences, Picard and Brauer interpretations, descent boundaries, and compatibility with
finite-flat group schemes.

B015. **Continuous Cohomology of Profinite Groups**
    Develop continuous cohomology for profinite groups acting on discrete or topological modules.
Construct homogeneous and inhomogeneous cochains, long exact sequences, connecting maps,
restriction and corestriction, inflation–restriction, Shapiro's lemma, and cup products, and
compare the cochain and derived-functor constructions. Applications identify deformation-theoretic
tangent and obstruction spaces with low-degree cohomology.

B016. **Local Galois Cohomology**
    Apply continuous cohomology to absolute Galois groups of local fields. Compute and bound
(H^0), (H^1), and (H^2) for finite modules and ℓ-adic representations, study unramified
cohomology and restriction to inertia, prove cohomological-dimension results and the local Euler
characteristic formula, and give coefficient-uniform Kummer calculations. The final dimension
formulas govern local deformation conditions and hardly-ramified relation calculations.

B017. **Tate Local Duality**
    Develop the local duality pairing between a finite Galois module and its Tate-twisted dual.
Prove continuous Hilbert 90 and the finite-module Tate–Nakayama theorem, construct the local
invariant and cup-product pairing, and establish perfectness. Conclude by identifying annihilators
of natural local conditions and deriving the dimension identities used for dual deformation
conditions.

B018. **Global Galois Cohomology and Selmer Groups**
    Develop Galois cohomology for number fields with ramification restricted to a finite set of
places. Define localization maps and general Selmer structures through subspaces of local (H^1),
construct dual Selmer structures, and prove the exact sequences comparing global and local
classes. Culminate in the identification of the tangent space of a global deformation problem
with its associated Selmer group.

B019. **Poitou–Tate Duality**
    Prove the global duality theorem relating a Selmer condition to its dual. Develop the
Poitou–Tate exact sequence, local-global pairings, orthogonal complements, global Euler
characteristic formulas, and dimension identities for Selmer and dual Selmer groups. The final
numerical formula determines how many Taylor–Wiles primes are required to kill the dual Selmer
group.

## IV. Curves, Abelian Varieties, and Mordell–Weil Theory

N022. **Rigid Analytic Curves and Formal Models** — Develop Tate algebras, affinoid localization,
coherent sheaves, rigid generic fibers, admissible blowups, tubes, reduction maps, proper rigid
curves, and comparison with algebraic curves.

N023. **Rigid Uniformization of Abelian Varieties** — Develop analytic tori, discrete lattices,
polarizations, quotient construction, formal descent, and Raynaud uniformization for the
semistable abelian varieties and Jacobians used below.

N024. **Relative Picard Schemes and Jacobians** — Construct Picard sheaves and schemes,
rigidification, identity components, Jacobians, Abel–Jacobi and Albanese maps, polarizations, and
functoriality under finite maps and correspondences.

B051. **Jacobians and (H^1) of Curves**
    Study the Jacobian and Picard variety of a smooth proper curve, with emphasis on modular and
Shimura curves. Relate torsion and Tate modules of the Jacobian to étale (H^1), develop
polarizations and duality, and prove the functorial action of correspondences on Jacobians and
Tate modules. This gives the bridge from geometric Hecke correspondences to finite-dimensional
ℓ-adic Galois representations.

N025. **Abelian Schemes, Isogenies, and Polarizations** — Develop dual abelian schemes, finite
flat kernels, quotients by finite subgroup schemes, Weil pairings, polarizations, and extension
over normal bases. Include the odd-isogeny preservation of full two-torsion needed by the Frey
argument.

N026. **Néron Models and Component Groups** — Construct Néron models of Jacobians and the
required abelian varieties, prove the mapping property, analyze identity components and component
groups, and compare with regular curve models.

N027. **Semistable Abelian Varieties and Monodromy** — Develop toric and abelian parts,
one-motives in the required range, monodromy pairings, conductor formulas, and quasi-unipotence for
Tate modules.

N028. **Integral Correspondences on Curves and Jacobians** — Extend finite correspondences to
regular models and Néron models, prove compatibility with component groups and duality, and prepare
integral Hecke actions.

N029. **Descent and Weak Mordell–Weil for Abelian Varieties** — Develop Kummer descent, Selmer
sets in the elementary isogeny range, finiteness modulo multiplication, and effective control of
the finite bad-place data.

N030. **Heights and the Mordell–Weil Theorem** — Construct Weil and Néron–Tate heights,
Northcott finiteness, height pairings, and finite generation of rational points on polarized
abelian varieties. Conclude with the finite-generation theorem used in Mazur's
Eisenstein-quotient argument.

## V. Elliptic Curves, Finite-Flat Groups, and Integral p-adic Theory

B010. **Finite Locally Free Schemes and Algebras**
    Study finite locally free morphisms through finite projective algebras. Develop rank, fibers,
base change, composition, dual modules, finite flatness over local rings and DVRs, and faithfully
flat descent. The principal structural result is that finite flat morphisms of constant rank are
stable under every operation used later for group schemes.

B011. **Affine Group Schemes and Hopf Algebras**
    Introduce affine group schemes through commutative Hopf algebras and prove the
anti-equivalence between the two viewpoints. Develop subgroup schemes, kernels, the quotient
constructions needed for finite groups, base change, morphisms, and exact sequences. Throughout,
translate geometric assertions into explicit Hopf-algebra calculations.

B012. **Finite Flat Commutative Group Schemes**
    Specialize affine group-scheme theory to finite flat commutative groups over local and
arithmetic bases. Study rank and fibers, connected and étale parts, kernels of multiplication,
schematic closure of generic-fiber subgroups, and finite-flat subgroups of abelian schemes. Prove
the exactness and closure theorems needed to model residual Galois representations integrally.

B013. **Cartier Duality**
    Develop Cartier duality for finite flat commutative group schemes. Construct the dual through
Hopf algebras, identify constant and diagonalizable examples, prove biduality, and study pairings,
kernels, base change, and generic fibers. Relate this theory to duality on the torsion of elliptic
curves and abelian varieties and to Tate-twisted Galois modules.

B014. **Finite-Flat Galois Representations**
    Relate finite flat group schemes over valuation rings to finite continuous representations of
local Galois groups. Study the generic-fiber functor, integral models of (G_K)-modules, uniqueness
and nonuniqueness, scalar extension, subobjects, quotients, duals, and extensions. Conclude with a
mathematical characterization of representations that are finite flat at places above ℓ and the
closure properties required in deformation theory.

B007. **Elliptic Curves over DVRs**
   Develop integral Weierstrass models over discrete valuation rings. Treat coordinate changes,
discriminants and c-invariants, minimal models, good, multiplicative, and additive reduction,
Néron-type criteria, semistability, and conductor consequences. Conclude with a complete
calculation of the reduction type and minimal discriminant of the Frey curve from its equation.

B008. **Tate Curves and Multiplicative Reduction**
   Study elliptic curves with split and nonsplit multiplicative reduction through Tate
uniformization. Construct the Tate curve, describe its points and torsion, analyze the Galois
action on the Tate parameter and Tate modules, and relate the analytic description to reduction,
inertia, and conductor. The closing chapters derive the local shape of residual and ℓ-adic
representations at multiplicative primes.

B009. **Torsion and Tate Modules of Elliptic Curves**
   Develop (E[n]), the Weil pairing, Tate modules (T_\ell E), and residual representations
(E[\ell]) over fields of the relevant characteristics. Prove that the determinant is
cyclotomic, explain how reduction controls inertia, study duality and isogeny functoriality, and
relate rational subgroup schemes to reducibility. Apply the theory to the two-dimensional
representations carried by the Frey curve.

N031. **Algebraic de Rham Cohomology and Gauss–Manin Connections** — Construct de Rham
cohomology of curves and abelian schemes, Hodge filtrations, cup products, base change, and
Gauss–Manin connections.

N032. **Divided Powers and Crystalline Sites** — Develop PD rings and envelopes, crystalline
sites and topoi, crystals, Frobenius crystals, and the functorial constructions required in
degree one.

N033. **Crystalline Cohomology of Curves and Abelian Schemes** — Construct derived crystalline
cohomology and prove finiteness, base change, duality, Künneth, Frobenius, and Dieudonné comparison
in the range required by finite-flat and PEL geometry.

N037. **Syntomic Cohomology and Integral Period Maps** — Construct the weight-zero and
weight-one syntomic complexes, integral period morphisms, exact sequences, and their compatibility
with finite-flat group schemes.

N038. **Finite-Flat Group Schemes of Small Height** — Develop schematic closure and exact
operations, connected–étale and multiplicative decompositions, and the Oort–Tate classification
of prime-order group schemes over the local bases occurring in FLT.

N039. **Dieudonné Theory and Raynaud Full Faithfulness** — Construct Dieudonné modules in the
finite-level range, classify the needed connected objects, and prove Raynaud full faithfulness
below the ramification boundary.

N040. **Fontaine–Laffaille Modules and Torsion Representations** — Develop divided filtered
modules, the syntomic construction of their generic Galois modules, exactness, duality, and full
faithfulness in weights zero and one.

N041. **Integral Fontaine–Laffaille Equivalence and Base Change** — Prove essential
surjectivity in the height-two range, identify finite-flat torsion objects, and establish the
integral base-change and compatible-quotient results needed for stable lattices.

N043. **p-divisible Groups and Serre–Tate Theory** — Develop connected–étale decompositions,
ordinary deformation coordinates, canonical lifts, and openness of the ordinary local loci used
in potential modularity.

N044. **Ramification and Discriminants of Finite-Flat Representations** — Prove the
Fontaine–Raynaud upper-break and different bounds, their stability in towers and under change of
coefficients, and sharp root-discriminant estimates for fields cut out by finite-flat torsion
representations.

## VI. Deformation Theory and Abstract Taylor–Wiles Patching

B020. **Artinian and Complete Local Coefficient Rings**
    Study local Artinian rings with fixed residue field and complete Noetherian local rings as
inverse limits. Develop continuous homomorphisms, formal power-series rings, completed tensor
products, small extensions, pseudocompact modules, and closed subalgebras. The emphasis is the
topological commutative algebra underlying deformation functors and trace rings.

N143. **Pseudocompact Trace Algebras and Carayol Descent** — Develop closed subalgebras of
pro-Artinian coefficient rings, topological Nakayama, and the compact-group character theory used
to control their inverse-limit topology. Prove the Burnside/Jacobson-density trace-generation
theorem, Henselian lifting and splitting of the resulting Azumaya algebra, Skolem–Noether
conjugacy, and strict-conjugacy descent. Culminate in Carayol's theorem that a residually
absolutely irreducible representation is defined over its closed trace algebra.

B021. **Deformation Functors of Representations**
    Introduce deformations of a residual Galois representation over local Artinian coefficient
rings. Define lifts, strict equivalence, framed and unframed deformations, fixed determinants,
base change, and infinitesimal deformations. Identify tangent spaces with (H^1) of the adjoint
representation and construct obstruction classes in (H^2), first locally and then globally.

B022. **Representability of Deformation Problems**
    Develop Schlessinger's criteria for pro-representability and versal hulls, emphasizing
small-extension arguments and automorphism obstructions. Treat framed and unframed
representations, fixed determinants, and passage between the variants. Conclude with existence
and uniqueness theorems for the universal local and global deformation rings used later.

B023. **Local Deformation Conditions Away from (\ell)**
    Study deformation conditions at primes whose residue characteristic differs from ℓ. Treat
unramified, minimally ramified, tame, Steinberg or special, and fixed-inertial-type deformations
in the cases required for FLT. Prove representability, calculate tangent spaces, and establish
formal smoothness and dimension theorems with their precise hypotheses.

B024. **Finite-Flat Deformation Conditions at (\ell)**
    Study fixed-determinant deformations at primes dividing the coefficient characteristic through
finite-flat group schemes and Fontaine–Laffaille modules. Prove invariance under strict
equivalence, coefficient change, subquotients, and base change, then compute tangent and
obstruction spaces. Establish representability and formal smoothness exactly in the residual and
weight ranges where these statements are true, including the hardly-ramified case.

B025. **Global Deformation Problems**
    Combine a residual representation with specified local conditions to define a global
deformation problem. Construct its universal ring, identify its tangent space with a Selmer
group and its obstructions with global (H^2), compare framed and unframed variants, and impose a
determinant. Use Poitou–Tate duality to derive the dimension inequalities that control generators
and relations.

B026. **Complete Local Algebra for Deformation Theory**
    Develop the complete local algebra used to analyze universal deformation rings: cotangent
spaces, embedding dimension, formal-power-series presentations, Krull dimension, regular local
rings, finite maps, topological Nakayama, and completed tensor products. Apply these results to
convert cohomological tangent and obstruction calculations into bounds on generators and
relations.

B027. **Depth, Complete Intersections, and Fitting Ideals**
    Develop regular sequences, depth, projective dimension, Cohen–Macaulay modules,
complete-intersection rings, Fitting ideals, and support. Study their behavior under finite local
maps and prove the freeness and faithfulness criteria by which a module forces structural
conclusions about the ring acting on it.

B028. **Numerical Criteria for (R=T)**
    Develop the numerical criteria of Wiles and Lenstra independently of automorphic forms.
Introduce congruence and cotangent modules, compare their lengths, and derive
complete-intersection criteria. The central theorems characterize when a surjection (R\to T)
between complete local rings must be an isomorphism.

B029. **Taylor–Wiles Primes**
    Study the auxiliary primes that alter a deformation problem while controlling global
cohomology. Use Chebotarev density and residual-image theory to impose simultaneous congruence and
Frobenius conditions, describe the enlarged local rings, and calculate their tangent
contributions. Conclude with the existence of Taylor–Wiles sets of prescribed cardinality and
level that kill the dual Selmer group.

B030. **Taylor–Wiles Systems**
    Study the towers of deformation rings, Hecke algebras, and modules obtained by adjoining
Taylor–Wiles primes. Develop the finite quotient group actions, augmentation maps, transition
maps, and compatibility across levels, and isolate the structural properties that survive passage
to the inverse limit.

B031. **Patching Modules and Rings**
    Construct patched deformation rings and modules from Taylor–Wiles towers. Develop the
inverse-limit or ultraproduct construction, auxiliary power-series and completed group rings,
support and depth calculations, and freeness over the auxiliary ring. Culminate in the patched
pair ((R_\infty,M_\infty)) with the dimension and depth properties needed for (R=T).

B032. **The Abstract (R=T) Argument**
    Complete the Taylor–Wiles method in an abstract algebraic setting. Show how the patched
module forces faithfulness of the (R_\infty)-action, compare dimensions and
complete-intersection properties, and descend from infinite level to the original deformation
and Hecke rings. The main theorem gives (R\simeq T) from the structural hypotheses isolated in
the preceding volume.

## VII. Local Representation Theory and Local Transfer

B038. **Smooth Representations of (p)-adic Groups**
    Develop harmonic analysis and smooth representation theory for totally disconnected locally
compact groups. Treat Haar convolution, admissibility, compact-open invariants, compact induction,
contragredients, intertwiners, Hecke algebras, distributions, and characters. Examples from GL₂
and quaternion division algebras prepare the character identities used in local transfer.

B039. **Representations of (GL_2(K))**
    Classify the smooth irreducible representations of GL₂(K) that occur in the chosen proof:
principal series, special representations, and dihedral supercuspidals. Study spherical vectors,
conductors, twists, central characters, newvectors, Weil–Deligne parameters, and local constants.
Primitive wild supercuspidals are outside the scope. Conclude with the local invariants preserved
by Jacquet–Langlands and base change.

N058. **Parabolic Induction, Jacquet Modules, and Whittaker Models for GL₂** — Treat principal
series, the geometric lemma in rank one, Jacquet modules, Whittaker uniqueness, Kirillov models,
and local zeta integrals.

N059. **Dihedral Supercuspidals, Types, and Newvectors for GL₂** — Construct the tame and
quadratic-induced supercuspidals occurring in the auxiliary automorphic representations, develop
their types and characters, and establish conductors and integral newvector theory. Primitive
wild types are outside the selected route.

N060. **Weil–Deligne Representations and Local Constants** — Develop Weil and Weil–Deligne
representations, monodromy and conductors, additive characters and self-dual measures, local
L- and ε-factors, and functional equations.

N061. **Local Langlands in the Principal, Special, and Dihedral Cases** — Construct and
characterize the correspondence for the cases used by unramified forms, Steinberg conditions,
and automorphic induction, with compatibility under twists and field extension.

B040. **Representations of Quaternion Division Algebras**
    Study smooth representations of (D^\times) for a quaternion division algebra over a local
field. Use compactness modulo the center to analyze admissibility and characters, then construct
the special and dihedral packets by compact induction. Develop their conductors, levels, and
integral lattices in the range corresponding to the selected GL₂ representations.

N063. **Characters and Dihedral Types on Quaternion Division Algebras** — Construct special
packets and the quaternionic dihedral types corresponding to quadratic induction on GL₂,
together with their conductors, regular-elliptic character formulas, and integral lattices.
Primitive wild packets are excluded.

B041. **Local Jacquet–Langlands**
    Construct local Jacquet–Langlands for Steinberg twists and the selected dihedral discrete
series. Match regular conjugacy classes and characters and prove compatibility with central
characters, twists, conductors, local factors, and integral type lattices. The main theorem gives
the precise transfer used in global trace-formula comparison and integral level change.

N064. **Local Jacquet–Langlands for Special and Dihedral Packets** — Prove the character
correspondence for Steinberg twists and the dihedral supercuspidals occurring in the route,
including central characters, twists, conductors, local factors, and integral type compatibility.

B046. **Cyclic Base Change: Local Theory**
    Study the behavior of local representations under finite cyclic extension of local fields.
Define base change through restriction of Weil–Deligne parameters, treat unramified and ramified
extensions, and calculate it for principal, special, and dihedral discrete-series
representations. Prove compatibility with twisting and local Jacquet–Langlands.

## VIII. Quaternionic and Global Automorphic Theory

B033. **Quaternion Algebras over Number Fields**
    Develop quaternion algebras as central simple algebras of degree two over local and global
fields. Study reduced trace and norm, Hilbert symbols, splitting and division criteria,
ramification at places, and completion. Culminate in the local-global classification by
ramification set and the construction of the totally definite algebras used in modularity
lifting.

B034. **Orders in Quaternion Algebras**
    Develop orders, maximal orders, Eichler orders, localization at finite places, one-sided
ideals and ideal classes, norms and discriminants, and finiteness of class sets. Reinterpret these
structures adelically and use them to construct the compact open subgroups and finite double
cosets underlying definite quaternionic forms.

B035. **Automorphic Forms on Definite Quaternion Algebras**
    Define algebraic automorphic forms on a totally definite quaternion algebra as functions on
adelic double quotients. Develop weights, central characters, compact-open levels,
finite-dimensionality, and integral coefficient lattices. Exploit compactness at infinity modulo
the center to reduce the theory to finite combinatorial spaces carrying Hecke actions.

B036. **Hecke Operators on Quaternionic Forms**
    Construct Hecke operators from local double cosets and prove their algebraic properties.
Develop spherical Hecke algebras at unramified primes, operators at level primes, global commuting
families, change of level, and explicit formulas on finite double-coset models. Conclude with the
Hecke modules compared with deformation rings in (R=T).

B037. **Hecke Algebras and Congruences**
    Study the commutative algebras generated by Hecke operators on integral automorphic forms.
Treat localization and completion at maximal ideals, residual eigensystems, congruences, old and
new subspaces, finite freeness, and change of level. The closing chapters construct the localized
complete Hecke algebra (T) and its natural modules. The Galois comparison and the map from a
universal deformation ring are constructed later, once the required Galois representations are
available.

B042. **Automorphic Representations of (GL_2)**
    Develop automorphic representations of (GL_2(\mathbb A_F)) through restricted tensor
products, cuspidal forms, central characters, and local components. Prove the required
multiplicity-one and newform theorems and relate unramified Hecke eigenvalues to local Satake
parameters. Conclude by translating between classical or Hilbert modular forms and adelic
representations.

B043. **Automorphic Representations of (D^\times)**
    Develop automorphic representations of the multiplicative group of a quaternion algebra.
Relate adelic automorphic forms to irreducible global representations, decompose them into local
components, and prove the required multiplicity statements. Special attention is given to the
finite algebraic spaces for totally definite algebras and their comparison with GL₂.

B044. **Global Jacquet–Langlands**
    Prove global Jacquet–Langlands for the weight-two packets in the FLT route by comparing the
GL₂ and quaternionic trace formulas with cuspidal archimedean test functions. Establish matching
at every place, preservation of multiplicity, rationality fields, Hecke eigenvalues, central
characters, levels, and ramification. Treat rational transfer here; integral lattices and
congruence indices belong to the later theory of integral level change.

B045. **Hecke Characters and Automorphic Induction from (GL_1)**
    Develop algebraic and finite-order Hecke characters, theta series, and quadratic automorphic
induction. Prove cuspidality criteria, calculate every required local component, control
coefficient fields, and identify the associated dihedral Galois representations through class
field theory. These forms furnish the automorphic starting points for potential modularity.

B047. **Cyclic Base Change for (GL_2)**
    Prove prime-degree cyclic base change for the cohomological GL₂ packets used here by comparing
twisted and untwisted cuspidal trace formulas. Establish existence and local compatibility at
every place, control Hecke eigenvalues, levels, and central characters, and characterize
cuspidality and the image through self-twists. Conclude with cyclic descent and its character
ambiguity.

B048. **Solvable Base Change and Descent**
    Iterate cyclic base change through towers of cyclic extensions to obtain solvable base change
and descent. Resolve character-twist ambiguities, prove independence of the chosen tower, and
control local types, Jacquet–Langlands transfer, and attached Galois representations. The main
theorem moves automorphy both up and down suitable solvable totally real extensions.

N065. **Schwartz–Bruhat Analysis and Tate’s Thesis** — Construct adelic Schwartz spaces,
self-dual measures, Fourier transform, Poisson summation, and Tate’s thesis with all character
functional equations and local normalizations used later.

N066. **Archimedean GL₂ and Discrete Series** — Develop real reductive groups, Harish–Chandra
modules, discrete and limit-of-discrete series, characters, formal degrees, cohomology, and the
parallel-weight-two infinity type.

N067. **Hilbert-Space Spectral and Trace-Class Theory** — Develop unbounded self-adjoint
operators, graph domains, compact resolvents, Hilbert–Schmidt and trace-class kernels, orthogonal
decompositions, and the spectral arguments required for the cuspidal automorphic spectrum.

N125. **Sobolev Theory and Elliptic Regularity on Arithmetic Quotients** — Develop invariant
Sobolev norms, elliptic estimates, smooth-vector criteria, cusp decay, compactness on truncated
quotients, and the analytic estimates needed for automorphic kernels.

N068. **Reduction Theory and the Cuspidal Spectrum of GL₂** — Prove adelic reduction theory,
finite-volume and cusp estimates, construct automorphic L² spaces, and obtain the discrete
cuspidal decomposition and finite multiplicities.

N069. **Global Constant Terms and Eisenstein Contributions for GL₂** — Develop parabolic
constant terms, the required Eisenstein series, and their global intertwining operators in rank
one. Prove the continuation and residue statements needed to classify the noncuspidal
contributions, and show that the selected cuspidal test functions annihilate every one of them;
do not construct the general automorphic Plancherel formula.

N070. **Global Whittaker Models and Rankin–Selberg Theory** — Prove global genericity, Whittaker
expansions, unfold Rankin–Selberg integrals, factor local zeta integrals, and obtain the analytic
properties used for multiplicity one and trace formulas.

N071. **Analytic Theory of Automorphic Rankin–Selberg L-functions** — Prove continuation,
functional equations, pole criteria, vertical bounds, and positivity for GL₂ Rankin–Selberg
L-functions, with compatible local and global normalizations. Deduce the analytic criterion that
underlies multiplicity one.

N138. **Strong Multiplicity One and Global Newforms for GL₂** — Use Rankin–Selberg pole
criteria to prove strong multiplicity one, then develop conductors, old and new subspaces,
restricted tensor products, normalized newvectors, and the global newform decomposition.

N072. **Algebraicity and Integral Structures of Weight-Two Packets** — Prove rationality fields,
Galois conjugation, integral Hecke lattices, period comparisons, and compatibility of weight-two
automorphic packets with coefficient embeddings.

N074. **Cuspidal Trace-Formula Kernels for Rank Two** — Construct automorphic kernels with a
cuspidal archimedean factor, prove their absolute convergence and trace-class properties, and
establish equality of the spectral and geometric expansions in exactly this simple-trace-formula
setting.

N075. **The Cuspidal Spectral Side of the GL₂ Trace Formula** — Compute the discrete cuspidal
trace distribution and prove, from constant terms and pseudo-coefficients, that the residual and
continuous contributions vanish for the selected functions. Record the multiplicities and
normalizations compatible with local transfer.

N126. **The Geometric Side of the GL₂ Trace Formula** — Classify rational conjugacy classes,
prove convergence, identify the terms killed by the cuspidal factor, and compute the surviving
central and elliptic distributions with the measures used in trace comparison.

N076. **Orbital Integrals for GL₂ and Quaternion Algebras** — Compute the required
nonarchimedean and archimedean regular orbital integrals, singular limits, measures, and local
character identities for the test functions used in transfer.

N130. **Transfer of Test Functions and the Rank-Two Fundamental Lemma** — Construct matching
functions for GL₂ and its quaternionic inner form and prove the unit, Iwahori, and selected level
fundamental lemmas needed by global comparison.

N078. **Twisted Conjugacy and Geometric Trace Distributions** — Develop twisted conjugacy,
norms, centralizers, stable classes, measures, and the convergent geometric distributions for
prime-degree cyclic extensions.

N139. **Twisted Cuspidal Trace Kernels and Spectral Expansion** — Construct twisted automorphic
kernels and intertwining operators for the selected cuspidal functions, prove convergence, and
identify the cuspidal spectral expansion while showing that the noncuspidal terms vanish. Apply
the resulting twisted simple trace formula to cyclic base change.

N127. **Twisted Orbital Matching and the Cyclic Fundamental Lemma** — Prove unramified norm
matching, the twisted fundamental lemma, and the ramified and level-specific matching statements
needed to compare the twisted and untwisted trace formulas.

## IX. Modular and Shimura Geometry with Galois Realization

N045. **Generalized Elliptic Curves and Level Structures** — Construct generalized elliptic
curves, Néron polygons, Drinfeld and Γ₁/Γ₀ structures, contraction, Tate cusp charts, and the
moduli interpretations required at prime level.

N046. **Compactified Modular Stacks and Coarse Modular Curves** — Construct compactified stacks,
fine rigidified covers, coarse schemes, cusp divisors, descent of universal isogenies, and the
stack/coarse comparison at exceptional automorphism loci.

N047. **Deligne–Rapoport Integral Models of Modular Curves** — Prove regularity and smoothness
away from level and construct the two-component semistable model at prime level, including nodes,
Igusa normalizations, degeneracy maps, and component intersection data.

N048. **Integral Modular Forms and q-Expansion** — Develop Katz modular forms through the Hodge
bundle, q-expansion principles at every cusp, Hecke and diamond operators, dualizing forms, cusp-
form lattices, and Sturm-style finite certification.

B052. **Modular and Shimura Curves**
    Give a unified geometric treatment of the modular and quaternionic Shimura curves used in
FLT. Develop their moduli problems, level structures, compactifications, cusps, connected
components, canonical descent, Hecke correspondences, and good and semistable integral models.
Conclude by realizing their automorphic Hecke modules in étale cohomology and Jacobian Tate
modules.

N049. **Modular Jacobians, Néron Models, and Hecke Correspondences** — Construct the integral
Hecke action on modular Jacobians, component groups, monodromy, Albanese maps, and the integral
Eichler–Shimura relation needed by both Mazur’s method and Galois extraction.

B053. **Hecke Correspondences on Curves and Jacobians**
    Construct Hecke correspondences on modular and Shimura curves and compare them with adelic
double cosets. Extend the correspondences over the required integral models, study their actions
on divisors, Jacobians, component groups, and étale cohomology, and prove the good-prime
Eichler–Shimura relations. The same Hecke algebra thereby acts on automorphic forms and on the
Galois representations arising from geometry.

N086. **Reductive Groups, Inner Forms, and Corestriction in Rank Two** — Develop root data,
restriction of scalars, inner twisting, quaternionic groups, corestriction algebras, involutions,
and the symplectic representations used in the PEL constructions.

N087. **CM Abelian Varieties, Types, and Reflex Norms** — Develop CM fields, types and orders,
ideal actions, complex constructions of CM abelian varieties, polarizations, endomorphism descent,
reflex fields, and reflex norms in the dimensions used by the PEL models.

N140. **Complex Multiplication, Reciprocity, and Reduction** — Prove the main complex-
multiplication reciprocity law in the required cases and develop its canonical descent, Galois
action, good-reduction, and finite-place consequences for CM points on the selected Shimura data.

N088. **Shimura Data and Canonical Models in the FLT Cases** — Develop the relevant Shimura
data, reflex fields, connected components, reciprocity maps, neat levels, and canonical-model
descent for Hilbert, quaternionic, and unitary data.

N089. **Quaternionic PEL Functors and Representability** — Construct the moduli functors,
determinant and polarization conditions, fine covers, representability, and universal abelian
families for the required quaternionic curves.

N132. **Uniformization, Components, and Hecke Descent for Shimura Curves** — Prove complex
uniformization, identify connected components and canonical descent, compare fine and coarse
levels, and descend universal isogenies and Hecke correspondences.

N090. **Unitary Shimura Surfaces and the Modèles Étranges Construction** — Construct the compact
unitary surfaces and auxiliary PEL varieties used to realize quaternionic automorphic
representations when the parity of the totally-real degree requires degree-two cohomology.

N091. **Good Integral Models of Shimura Curves and Surfaces** — Construct smooth PEL models at
good primes, extend universal abelian schemes and Hecke correspondences, and prove smooth/proper
base change and integral comparison for their cohomology.

N128. **Semistable Models and Monodromy of Shimura Varieties** — Construct and regularize the
bad-prime models required for the quaternionic curves and unitary surfaces, analyze components,
nearby cycles and monodromy, and compute the conductor and type information used in local–global
compatibility.

N092. **Automorphic Decomposition of Shimura-Curve H¹** — Relate constant-coefficient H¹ of the
required Shimura curves to parallel-weight-two automorphic representations, including Hecke
actions, multiplicity, rational structures, and isolation of two-dimensional constituents.

N133. **Automorphic Decomposition of Unitary-Surface H²** — Establish the degree-two
cohomological realization on the auxiliary compact unitary surfaces. Use the low-dimensional
Lefschetz formula, purity, and Hecke correspondences to isolate the relevant quaternionic packets,
then compare their rational, Hecke, and Galois structures with the curve cases.

N093. **Galois Representations from Weight-Two Shimura Cohomology** — Extract continuous
two-dimensional representations and determinants from localized cohomology, establish parity,
semisimplicity, coefficient fields, and the good-prime Frobenius polynomials.

B054. **Galois Representations Attached to Weight-Two Automorphic Forms**
    Construct two-dimensional ℓ-adic Galois representations from weight-two eigensystems in the
cohomology of modular curves, quaternionic Shimura curves, and the required unitary surfaces.
Determine Frobenius polynomials, determinants, ramification, and purity; construct canonical
integral lattices and finite-flat quotients; and prove local–global compatibility. The main
theorem attaches a compatible Galois system to every weight-two automorphic representation in the
cases used by FLT.

N094. **Local–Global Compatibility for Weight-Two Galois Representations** — Prove good-prime
unramified compatibility and bad-prime inertia, monodromy, conductor, Steinberg, and finite-type
compatibility using integral models and vanishing cycles.

N095. **Compatible Coefficient Systems and Purity** — Construct strictly compatible systems from
the coefficient conjugates of a weight-two packet and prove independence of embedding,
polarization, purity, and compatibility at every place in the cases used by FLT.

N134. **Canonical Galois Lattices and Finite-Flat Quotients** — Construct the canonical localized
cohomological lattices, prove freeness and independence of integral choices, and establish
finite-flatness and compatible transition maps for every required coefficient quotient.

## X. Eisenstein Descent, Exceptional Torsion, and the Frey Curve

B067. **Modular Curves (X_0(N)) and (X_1(N))**
    Develop modular curves from generalized elliptic curves with Γ₀ and Γ₁ level structures.
Treat compactification, cusps, degeneracy maps, integral reduction, and rational points. Conclude
with the precise correspondence between rational X₀(p)-points, rational cyclic isogenies, and
reducibility of E[p].

B068. **Jacobians of Modular Curves**
    Study the prime-level modular Jacobian J₀(p), its Hecke action, cuspidal subgroup, Albanese
maps, reduction and component maps, duality, and Néron model. Construct the Eisenstein quotient
used in Mazur's argument and relate rational points on X₀(p) to finite subgroup schemes and Hecke
modules of the Jacobian.

B069. **The Eisenstein Ideal**
    Develop the Eisenstein ideal at prime level, calculate its exact index, and study the cuspidal
specialization, admissible finite group schemes, completed Hecke piece, and Eisenstein descent.
Use cotangent lattices to prove formal immersion at the relevant cusp. The scope is the selected
Eisenstein quotient; full multiplicity one and the complete Shimura-subgroup theory are not
included.

N050. **Eisenstein Series, Congruences, and the Eisenstein Ideal** — Construct the prime-level
Eisenstein series, compute constant terms, define the Eisenstein ideal, prove the q-expansion
congruence theorem, and calculate its exact index in the Hecke algebra.

N051. **Cuspidal Divisors and Specialization on Modular Jacobians** — Determine the cuspidal
divisor group, its Hecke action, order, and specialization in the component group at the level
prime. Develop only the auxiliary multiplicative subgroup facts used by the selected Eisenstein
quotient, not the full Shimura-subgroup intersection theorem.

N052. **Mazur–Raynaud Admissible Group Schemes** — Develop the category of group schemes finite
flat away from the level prime, its constant and multiplicative constituents, extension and
flat-cohomology calculations, and the devissage needed to control the selected Eisenstein
prime quotient, including the two-primary boundary. Do not prove complete multiplicity one or the
full rational torsion of J₀(p) when the FLT quotient does not require it.

N053. **Completed Hecke Pieces and Eisenstein p-divisible Groups** — Construct the selected
Eisenstein quotient, its Néron model and completed Hecke piece, and prove admissibility and control
of the finite-flat p-power torsion used in Eisenstein descent. Exclude generic cyclotomic-tower
theory and unrelated p-adic analytic results.

N054. **Eisenstein Descent and the Mordell–Weil Group of the Eisenstein Quotient** — Develop
flat-cohomological Eisenstein descent, compute the relevant Selmer groups and Hecke annihilators,
and combine descent with height theory to prove finiteness of the rational points of the
Eisenstein quotient. The treatment follows the algebraic Eisenstein argument rather than the
winding-quotient method or analytic rank-zero theorems for arbitrary modular factors.

N055. **Eisenstein Cotangent Lattices and Formal Immersion** — Develop integral cotangent
comparisons for the Eisenstein quotient and prove formal immersion at the oriented Γ₁ cusp.
Combine specialization of rational prime-order points with the uniform theorem for primes at
least seventeen and with the genus-one calculation at level eleven, isolating the two remaining
genus-two rational-point problems.

B070. **Rational Isogenies of Prime Degree**
    Study rational prime-degree isogenies by combining modular curves, semistable isogeny
characters, Mazur's formal-immersion argument, and explicit rational-point calculations on
X₁(13) and the mixed-seven curve. The culminating theorem proves irreducibility of the Frey
curve's mod-p representation for every prime exponent p≥7. Exponent five is treated separately
by cyclotomic descent.

N119. **Genus-Two Curves, Jacobians, and Abel–Jacobi Geometry** — Develop hyperelliptic curves of
genus two, divisor classes, Jacobians, principal polarizations, Abel–Jacobi embeddings, reduction,
and the geometry of rational points in the exact range used by X₁(13) and the mixed-seven curve.

N120. **Mumford Representations and Exact Genus-Two Jacobian Arithmetic** — Develop unique
reduced Mumford representatives, Cantor composition and reduction, torsion tests, finite-field
point counting, reduction homomorphisms, and checkable arithmetic certificates.

N121. **Explicit Two-Descent on Genus-Two Jacobians** — Develop étale descent algebras, S-unit
squareclasses, norm kernels, local descent images, Selmer bounds, torsion determination, and
odd-prime saturation. Carry out the two finite calculations needed for the Jacobians of X₁(13)
and the mixed-seven curve.

N122. **Mordell–Weil Sieves for Hyperelliptic Curves** — Develop reduction-set constraints,
coset sieving, saturation certificates, completeness criteria, and exhaustive Mordell–Weil
sieves. Determine X₁(13)(ℚ) and prove that the mixed-seven curve has only cuspidal or degenerate
rational points.

N056. **Semistable Isogeny Characters and Frey Residual Representations** — Analyze the diagonal
characters of a reducible semistable torsion representation. Use global unramifiedness and the
finite-flat local alternatives to make one character trivial on one side of the isogeny, preserve
full rational two-torsion under the odd isogeny, and combine the prime-torsion theorem with the
mixed-seven calculation to prove Frey irreducibility for every prime exponent at least seven.

B071. **The Frey Curve and Fermat’s Last Theorem**
    Present the complete Frey-curve proof as a mathematical synthesis. Begin from the classical
exponent-three and exponent-four theorems, prove exponent five by cyclotomic descent, and reduce
the remaining equation to prime exponents p≥7. Construct the Frey
curve, calculate its discriminant and reduction, prove residual irreducibility, and verify the
hardly-ramified conditions. Then pass through the balanced characteristic-zero lift, residual
potential modularity, Brauer descent to a compatible family, change of prime to three, and
Schoof's classification. Chebotarev density, Brauer–Nesbitt, the rank-two trace criterion, and
compatibility transport the reducible three-adic traces back to the original residual
representation, yielding the final contradiction and Fermat's Last Theorem.

## XI. Integral Automorphic Infrastructure and Modularity Lifting

B055. **Minimal Modularity Lifting**
    Develop the minimal deformation and Hecke problems over totally real fields and match their
local conditions. Construct the map R→T, calculate the Selmer and congruence invariants, choose
Taylor–Wiles primes, and patch the resulting modules. The culminating theorem is minimal
modularity lifting in the coefficient-prime range ℓ≥7 used by the chosen route.

B056. **Nonminimal Modularity Lifting**
    Extend the minimal theorem to the selected conductor-two local condition. Develop the
Skinner–Wiles class-field-theoretic reduction through solvable base change, then treat integral
types, Ihara theory, saturated level change, nonminimal local reciprocity, and one-prime patching
on the required component. Conclude with the fixed-determinant finite-flat hardly-ramified
modularity-lifting theorem for ℓ≥7, making no claim at coefficient five.

N096. **Integral Local Types and Type Lattices** — Construct integral principal, Steinberg, and
dihedral type lattices, their companion lattices, reduction behavior, and exact local deformation
conditions at the fixed nonminimal prime. Primitive wild supercuspidal types are excluded.

N097. **Ihara Theory and Saturated Degeneracy Maps on Shimura Curves** — Prove geometric Ihara
injectivity, saturation, torsion-freeness of new quotients, and component-group control for the
specific Shimura curves and levels used in patching.

N098. **Integral Level Change and Jacquet–Langlands Comparison** — Refine rational
Jacquet–Langlands transfer integrally. Prove the relevant level-raising and level-lowering
theorems, compare localized automorphic lattices and Hecke orders across inner forms, and
eliminate the resulting congruence indices.

N099. **Deep-Level Quaternionic Modules and Diamond Actions** — Construct the Taylor–Wiles
level modules, prove group-ring freeness, primary and companion duality, exact augmentation, and
transition-map compatibility.

N100. **Hecke-Valued Galois Representations and Nonminimal Reciprocity** — Construct
representations over localized Hecke orders by combining dense Frobenius trace identities with
Carayol descent. Prove the required local deformation conditions on Artinian quotients and
establish the nonminimal factorization, inertia, and monodromy theorems.

N142. **Dickson Classification and Adequate Residual Image** — Classify finite subgroups of
PGL₂ over the relevant finite fields into cyclic, dihedral, exceptional, and large-image cases.
Relate the projective classification to irreducible two-dimensional residual representations,
their cyclotomic restrictions and scalar extensions. Combine the classification with the
conductor and finite-flat restrictions of the hardly-ramified problem, determine the small-image
alternatives, and prove the adequacy and big-image conclusions used in Taylor–Wiles prime
selection and potential modularity. Isolate the coefficient-five exceptional behavior instead of
applying an ℓ≥7 conclusion there.

N135. **The Minimal Totally-Real Deformation–Hecke Problem** — Match local and global deformation
conditions with definite-quaternion Hecke modules, construct the map R→T, and compute tangent
dimensions, congruence modules, determinant lines, and the exact Taylor–Wiles numerical data.

N101. **Minimal Patching and R=T over Totally Real Fields** — Construct the Taylor–Wiles
system for the minimal totally-real deformation problem, patch its modules and rings, prove
support and freeness, and descend to the minimal deformation-ring/Hecke-algebra equality for
coefficient primes ℓ≥7.

N136. **One-Prime Type Complexes and Component Support** — Develop the fixed-prime degeneracy
and type complex, its amplitude and Tor terms, component support, determinant comparisons, and
exact augmentation on the conductor-two Steinberg component.

N102. **One-Prime Nonminimal Patching and R=T** — Combine N136 with the minimal theorem,
nonminimal reciprocity, and level-change infrastructure to patch on the selected component and
prove the conductor-two nonminimal ring/Hecke equality. Its final section proves the resulting
fixed-determinant, finite-flat modularity-lifting corollary, including coefficient extension,
solvable descent, and the local hypotheses used later; it asserts no small-image theorem at 5.

## XII. Arithmetic Approximation and Residual Potential Modularity

B057. **Hilbert Irreducibility and Arithmetic Approximation**
    Develop Hilbert irreducibility together with weak approximation, prescribed decomposition and
completion data at finitely many places, linear disjointness, avoidance of given extensions, and
totally real specialization. Use the finiteness of local extensions of bounded degree to reduce
simultaneous local requirements to finitely many conditions. Conclude with the specialization
theorems needed for Moret–Bailly and automorphy fields.

B058. **Moret–Bailly’s Theorem**
    Develop moving lemmas for zero-cycles, symmetric powers, configuration spaces, and irreducible
zero-cycle approximation, then prove Moret–Bailly's local-open existence theorem in the required
totally-real form. Derive the linear-disjointness and splitting refinements used later. The
main theorem turns prescribed local points on a moduli space into a global point over a
controlled totally real extension.

B059. **Moduli Constructions for Potential Modularity**
    Develop Hilbert–Blumenthal moduli with two-prime level structure. Study twisted torsion
frames, polarizations, determinant conditions, representability, connected components, geometric
monodromy, and the real, good, ordinary, finite-flat, and semistable local loci. Prove that the
resulting cover is smooth and geometrically connected under the hypotheses used in residual
potential modularity.

B060. **Potential Modularity of Two-Dimensional Representations**
    Construct a controlled totally real extension and an auxiliary Hilbert–Blumenthal abelian
variety whose torsion at one prime realizes a prescribed residual representation while its
torsion at a second prime is dihedrally automorphic. Combine Moret–Bailly's theorem with
modularity lifting to transfer automorphy between the two primes. Conclude with residual
potential modularity for coefficient primes at least seven.

N085. **Galois and Solvable Refinements of Arithmetic Approximation** — Control normal closures,
local completion data, elementary and solvable subfields, mutual disjointness, and the compatible
families of fields required for Brauer descent. Do not infer these refinements from ordinary
Moret–Bailly alone.

N104. **Hilbert–Blumenthal Moduli and Two-Prime Level Covers** — Construct fine polarized
real-multiplication moduli, determinant conditions, auxiliary neat level, paired torsion frames,
twists, components, and geometric monodromy.

N105. **Local Geometry of Hilbert–Blumenthal Moduli** — Construct real, good, ordinary,
nonordinary finite-flat, and semistable local points; prove openness and persistence of the exact
local conditions used in Moret–Bailly specialization.

N106. **Auxiliary Dihedral Data and Residual Potential Modularity** — Carry out the two-prime
construction: choose CM fields, Hecke characters, auxiliary primes, determinants, conductors,
residual images, and disjoint extensions; control connected components and local specializations
on a Hilbert–Blumenthal cover; and combine arithmetic approximation, modularity lifting, and
weight-two Galois realization to prove residual automorphy over a controlled finite totally-real
field for coefficient primes at least seven.

## XIII. Hardly-Ramified Lifts, Compatible Systems, and Changing Prime

B061. **Compatible Systems of Galois Representations**
    Develop weakly and strictly compatible systems of two-dimensional Galois representations.
Study common Frobenius polynomials, coefficient fields, ramification sets, determinants, residual
members, restriction, induction, purity, and independence of ℓ. Treat both systems arising from
weight-two automorphic forms and those descended from potential automorphy, with particular
attention to changing coefficient prime.

B062. **Brauer Induction and Descent of Automorphy**
    Develop Brauer induction on elementary subgroups and its use in descending automorphy.
Compare Galois and automorphic induction term by term, control coefficient fields, determinants,
and local types, and analyze the character twists occurring in a Brauer relation. Use Frobenius
reciprocity and character inner products to prove that the resulting virtual character is an
actual two-dimensional compatible system over the base field.

B063. **Changing the Prime**
    Study how a compatible system carries arithmetic information from one coefficient prime to
another. Follow Frobenius polynomials, determinants, residual semisimplifications, and stable
integral lattices, and prove all-level finite-flatness at three together with the special line and
conductor at two. Apply the theory to construct the three-adic companion of the chosen
hardly-ramified lift.

B064. **Discriminants of Galois Representations**
    Relate ramification of finite Galois modules to discriminants of their fixed fields. Combine
differents in towers, upper ramification breaks, change of coefficients, and the sharp
Fontaine–Raynaud bounds for finite-flat group schemes. Derive explicit root-discriminant upper
bounds for the torsion fields occurring in the three-adic argument.

B065. **Odlyzko Bounds and Fontaine’s Argument**
    Develop the Odlyzko–Poitou lower bounds for root discriminants from explicit formulas for
Dedekind zeta functions. Analyze their dependence on degree and signature and certify the
numerical thresholds needed here. Combine them with finite-flat upper bounds to reconstruct
Fontaine's small-ramification argument and rule out the forbidden large torsion fields.

B066. **Hardly Ramified (3)-adic Representations**
    Prove Schoof's classification of the three-adic representations occurring in the FLT
argument. Analyze the residual representation, successive torsion fields, and their discriminants,
then use the global finite-flat filtration over ℤ[1/2]. Conclude that the semisimplification is
1⊕χ₃ and obtain the reducibility statement required for the Frey contradiction.

N141. **Schoof's Finite-Flat Category over ℤ[1/2]** — Construct the category of finite-flat
commutative 3-primary group schemes over ℤ[1/2] whose generic fibers have odd tame inertia at
two, gluing Hopf orders from generic and local data. Prove stability under schematic closure,
subobjects, quotients, Cartier duality, and extensions. Use the finite-flat discriminant estimate,
the exact Odlyzko bound, and explicit ray-class calculations to classify the simple factors as
μ₃ and ℤ/3ℤ. Compute the relevant Ext¹ groups by fppf Kummer theory, cyclotomic units, and
Herbrand theory, then prove filtration rearrangement and the all-level devissage that yields
Schoof's three-adic conclusion.

N108. **Local Conditions for Hardly-Ramified Minimal Deformations** — Study the
fixed-determinant finite-flat condition at the coefficient prime and tame-quadratic conductor-two
condition at 2, including liftability, tangent spaces, obstruction vanishing, and compatibility
with the universal global problem in odd characteristic at least 7.

N109. **Supported Galois Cohomology and Selmer Calculations** — Develop finite local cohomology,
compactly supported cochain complexes, comparison with Poitou–Tate, local orthogonality, and the
exact Greenberg–Wiles dimension inequality for the hardly-ramified deformation problem.

N123. **Relation Obstructions and Poitou–Tate Corrections** — Develop relation factor sets and
their supported H² classes, local obstruction vanishing, the affine torsors of admissible local
lifts, reciprocity for correction targets, and the injection of the relation module into dual
Selmer.

N110. **Finite Image and the Balanced Minimal-Lift Argument** — Prove finite image after scalar
reduction by restricting to a totally-real field on which residual potential modularity and
nonminimal modularity lifting apply. Combine Carayol descent, the supported Selmer calculation,
relation-obstruction corrections, balanced presentations, topological Nakayama, minimal primes,
and normalization to construct a characteristic-zero hardly-ramified lift.

N112. **Potential Automorphy and Galois Refinement of a Chosen Lift** — Apply the two-prime
construction to a fixed hardly-ramified lift while preserving its residual image and specified
local components. Refine the resulting totally-real automorphy field to a controlled normal
closure and a family of elementary subfields on which solvable descent can be applied.

N137. **Brauer Induction for Automorphy Families** — Develop the finite-group Brauer relations
used for solvable and elementary subgroups, induction and restriction of two-dimensional Galois
and automorphic representations, and the compatibilities among coefficient fields, determinants,
local types, and conjugate members. Apply these relations to the field family constructed in
the preceding potential-automorphy argument.

N113. **Brauer Characters and Effectivity of Compatible Families** — Develop Mackey theory,
Frobenius reciprocity, character inner products, and Clifford theory for the induced
representations in a Brauer relation. Prove that the signed character has positive sign,
dimension two, and norm one at every coefficient embedding, and hence is an actual irreducible
semisimple representation. Conclude with Brauer–Nesbitt and the rank-two criterion that a dense
Frobenius trace identity with 1+χ forces reducible semisimplification.

N114. **Compatible Systems over the Base Field** — Combine the systems over elementary
subfields, prove independence of the Brauer decomposition, establish continuity and Frobenius
compatibility, identify the original member, and construct the global compatible family over the
base field.

N116. **The Fixed-Three Integral Local Theory** — Starting from the effective three-adic member,
choose a stable lattice and use weight-two local–global compatibility and integral
Fontaine–Laffaille theory to prove finite-flatness of every quotient. Establish compatible
transition maps, determinant and duality, the tame-unipotent special line and conductor-two type
at 2, and unramifiedness elsewhere. Conclude with the precise local hypotheses for Schoof's
classification.

## XIV. The Coefficient-Five Boundary

N117. **Quintic Cyclotomic Units and Kummer Arithmetic** — Work in Q(ζ₅), taking the
description of its ring of integers, discriminant, and class-number-one theorem as starting
points. Determine the prime above five, its valuations, conjugation, units and cyclotomic units,
norms, and associates, and prove the fifth-power, Kummer, and coprimality lemmas needed for
Diophantine descent.

N118. **Cyclotomic Descent for Quintic Fermat-Type Equations** — Develop first- and second-case
descent in fifth cyclotomic fields, valuation control at the prime above 5, primitive-factor
decompositions, and well-founded norm descent. Conclude with Fermat's Last Theorem for exponent
five, leaving the modularity-lifting argument to begin at coefficient primes at least seven.
