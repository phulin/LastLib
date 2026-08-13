# Representability of Deformation Problems

## Contents

1. [From infinitesimal answers to a formal space](#1-from-infinitesimal-answers-to-a-formal-space)
   - [The representability question](#11-the-representability-question)
   - [The coefficient categories](#12-the-coefficient-categories)
   - [The one-point residue condition](#13-the-one-point-residue-condition)
   - [Fiber-product comparison maps](#14-fiber-product-comparison-maps)
2. [Representable functors and inverse limits](#2-representable-functors-and-inverse-limits)
   - [Why the representing object is complete](#21-why-the-representing-object-is-complete)
   - [Universal elements at finite level](#22-universal-elements-at-finite-level)
   - [Exact gluing for mapping functors](#23-exact-gluing-for-mapping-functors)
   - [Tangent space and cotangent space](#24-tangent-space-and-cotangent-space)
   - [Uniqueness of a representing ring](#25-uniqueness-of-a-representing-ring)
3. [Infinitesimal lifting properties](#3-infinitesimal-lifting-properties)
   - [Small extensions as atomic tests](#31-small-extensions-as-atomic-tests)
   - [Formal smoothness of a natural transformation](#32-formal-smoothness-of-a-natural-transformation)
   - [Formal unramifiedness and formal etaleness](#33-formal-unramifiedness-and-formal-etaleness)
   - [Versal maps and hulls](#34-versal-maps-and-hulls)
   - [Uniqueness properties of hulls](#35-uniqueness-properties-of-hulls)
4. [Schlessinger's four conditions](#4-schlessingers-four-conditions)
   - [The chosen formulation](#41-the-chosen-formulation)
   - [What each condition controls](#42-what-each-condition-controls)
   - [The vector-space structure on the tangent set](#43-the-vector-space-structure-on-the-tangent-set)
   - [Necessity for representable functors](#44-necessity-for-representable-functors)
   - [Small tests versus arbitrary fiber products](#45-small-tests-versus-arbitrary-fiber-products)
   - [Necessity of (H1)--(H3) for a hull](#46-necessity-of-h1--h3-for-a-hull)
   - [Extending gluing beyond principal kernels](#47-extending-gluing-beyond-principal-kernels)
5. [The power-series source](#5-the-power-series-source)
   - [Tangent dimension counts generators](#51-tangent-dimension-counts-generators)
   - [A first-order universal element](#52-a-first-order-universal-element)
   - [Minimality and changes of coordinates](#53-minimality-and-changes-of-coordinates)
   - [Why finite tangent dimension gives Noetherianity](#54-why-finite-tangent-dimension-gives-noetherianity)
6. [Constructing a hull](#6-constructing-a-hull)
   - [The architecture of the sufficiency proof](#61-the-architecture-of-the-sufficiency-proof)
   - [The finite-stage lemma](#62-the-finite-stage-lemma)
   - [Proof of the finite-stage lemma](#63-proof-of-the-finite-stage-lemma)
   - [Passage to the complete ring](#64-passage-to-the-complete-ring)
   - [Formal smoothness of the limit map](#65-formal-smoothness-of-the-limit-map)
   - [Choices, completeness, and what has been proved](#66-choices-completeness-and-what-has-been-proved)
7. [From a hull to a representing object](#7-from-a-hull-to-a-representing-object)
   - [The missing uniqueness condition](#71-the-missing-uniqueness-condition)
   - [Why (H4) is stronger than tangent uniqueness](#72-why-h4-is-stronger-than-tangent-uniqueness)
   - [Universal rings and coordinate choices](#73-universal-rings-and-coordinate-choices)
8. [Obstruction theories as verification devices](#8-obstruction-theories-as-verification-devices)
   - [Why obstruction spaces are auxiliary](#81-why-obstruction-spaces-are-auxiliary)
   - [Obstructions, lift torsors, and gluing](#82-obstructions-lift-torsors-and-gluing)
   - [Unobstructed does not mean representable](#83-unobstructed-does-not-mean-representable)
   - [Relation bounds from obstruction spaces](#84-relation-bounds-from-obstruction-spaces)
9. [Automorphisms and failure of coarse representability](#9-automorphisms-and-failure-of-coarse-representability)
   - [Equality of classes hides an arrow](#91-equality-of-classes-hides-an-arrow)
   - [An explicit stabilizer failure](#92-an-explicit-stabilizer-failure)
   - [What remains meaningful with large stabilizers](#93-what-remains-meaningful-with-large-stabilizers)
10. [Framed deformation functors](#10-framed-deformation-functors)
    - [Exact gluing of matrices](#101-exact-gluing-of-matrices)
    - [Finiteness hypotheses on the profinite group](#102-finiteness-hypotheses-on-the-profinite-group)
    - [Framed pro-representability theorem](#103-framed-pro-representability-theorem)
    - [A direct generators-and-relations construction](#104-a-direct-generators-and-relations-construction)
    - [The universal framed representation](#105-the-universal-framed-representation)
11. [Unframed representations under the scalar-centralizer hypothesis](#11-unframed-representations-under-the-scalar-centralizer-hypothesis)
    - [The Schur condition](#111-the-schur-condition)
    - [Centralizers over Artinian lifts](#112-centralizers-over-artinian-lifts)
    - [The automorphism descent step](#113-the-automorphism-descent-step)
    - [Unframed pro-representability](#114-unframed-pro-representability)
    - [Framed versus unframed rings](#115-framed-versus-unframed-rings)
12. [Fixed determinants](#12-fixed-determinants)
    - [The determinant datum](#121-the-determinant-datum)
    - [Fixed determinant as a closed condition](#122-fixed-determinant-as-a-closed-condition)
    - [A fiber-product description](#123-a-fiber-product-description)
    - [Tangent and characteristic caveats](#124-tangent-and-characteristic-caveats)
    - [Representability theorem with fixed determinant](#125-representability-theorem-with-fixed-determinant)
13. [Operations on represented deformation problems](#13-operations-on-represented-deformation-problems)
    - [Natural transformations reverse ring maps](#131-natural-transformations-reverse-ring-maps)
    - [Closed subfunctors and quotient rings](#132-closed-subfunctors-and-quotient-rings)
    - [Products and fiber products of functors](#133-products-and-fiber-products-of-functors)
    - [Intersections and base change of closed conditions](#134-intersections-and-base-change-of-closed-conditions)
    - [Formally smooth power-series extensions](#135-formally-smooth-power-series-extensions)
    - [A singular fiber-product calculation](#136-a-singular-fiber-product-calculation)
14. [Relative representability of deformation conditions](#14-relative-representability-of-deformation-conditions)
    - [Why an ambient-relative notion is needed](#141-why-an-ambient-relative-notion-is-needed)
    - [The universal-family test](#142-the-universal-family-test)
    - [Fiber-product criteria for a subfunctor](#143-fiber-product-criteria-for-a-subfunctor)
    - [Tangent spaces of closed conditions](#144-tangent-spaces-of-closed-conditions)
    - [Intersections of local conditions](#145-intersections-of-local-conditions)
    - [Extra structures and forgotten choices](#146-extra-structures-and-forgotten-choices)
15. [A reusable universal-ring theorem](#15-a-reusable-universal-ring-theorem)
    - [The abstract package](#151-the-abstract-package)
    - [The representation-theoretic package](#152-the-representation-theoretic-package)
    - [An unobstructed refinement](#153-an-unobstructed-refinement)
    - [A topological finite-generation version](#154-a-topological-finite-generation-version)
    - [What the package does not claim](#155-what-the-package-does-not-claim)
16. [Worked formal geometries](#16-worked-formal-geometries)
    - [One free parameter](#161-one-free-parameter)
    - [A node and nonunique branches](#162-a-node-and-nonunique-branches)
    - [A character of a procyclic group](#163-a-character-of-a-procyclic-group)
    - [Commuting matrices and quadratic relations](#164-commuting-matrices-and-quadratic-relations)
    - [Framing a scalar residual representation](#165-framing-a-scalar-residual-representation)
17. [The representability dictionary](#17-the-representability-dictionary)
    - [Functors and rings](#171-functors-and-rings)
    - [Infinitesimal properties](#172-infinitesimal-properties)
    - [Hull versus universal object](#173-hull-versus-universal-object)
    - [Representation and cohomology entries](#174-representation-and-cohomology-entries)
    - [A representability checklist](#175-a-representability-checklist)
18. [Continuity and reconstruction on complete coefficient rings](#18-continuity-and-reconstruction-on-complete-coefficient-rings)
    - [Why Artinian tests must be reassembled](#181-why-artinian-tests-must-be-reassembled)
    - [Represented functors are continuous](#182-represented-functors-are-continuous)
    - [Universal elements as one continuous object](#183-universal-elements-as-one-continuous-object)
    - [Framed representation functors are continuous](#184-framed-representation-functors-are-continuous)
    - [Unframed classes and compatible conjugators](#185-unframed-classes-and-compatible-conjugators)
    - [Reconstructing a hull over a complete target](#186-reconstructing-a-hull-over-a-complete-target)
    - [A discontinuous extension as a warning](#187-a-discontinuous-extension-as-a-warning)
    - [Continuity of closed conditions](#188-continuity-of-closed-conditions)
    - [The continuity protocol](#189-the-continuity-protocol)
19. [Change of coefficient base](#19-change-of-coefficient-base)
    - [Two different changes of coefficients](#191-two-different-changes-of-coefficients)
    - [Universal rings under a same-residue base change](#192-universal-rings-under-a-same-residue-base-change)
    - [Base-changing a presentation](#193-base-changing-a-presentation)
    - [Tangent spaces after flat coefficient extension](#194-tangent-spaces-after-flat-coefficient-extension)
    - [Enlarging the residual field](#195-enlarging-the-residual-field)
    - [Cohomology after a finite residue extension](#196-cohomology-after-a-finite-residue-extension)
    - [Fixed determinants under coefficient change](#197-fixed-determinants-under-coefficient-change)
    - [What coefficient change preserves](#198-what-coefficient-change-preserves)
20. [Local and global deformation rings](#20-local-and-global-deformation-rings)
    - [Why localization is a fiber-product problem](#201-why-localization-is-a-fiber-product-problem)
    - [The unrestricted local product](#202-the-unrestricted-local-product)
    - [Closed local conditions](#203-closed-local-conditions)
    - [The global functor with prescribed local conditions](#204-the-global-functor-with-prescribed-local-conditions)
    - [Tangent spaces with local conditions](#205-tangent-spaces-with-local-conditions)
    - [Obstructions with local conditions](#206-obstructions-with-local-conditions)
    - [Framed global problems](#207-framed-global-problems)
    - [The global restricted-ramification specialization](#208-the-global-restricted-ramification-specialization)
    - [Local and global uniqueness](#209-local-and-global-uniqueness)
21. [Exact existence and presentation theorems](#21-exact-existence-and-presentation-theorems)
    - [Why the hypotheses should be collected](#211-why-the-hypotheses-should-be-collected)
    - [The master representability theorem](#212-the-master-representability-theorem)
    - [Minimal numbers of variables](#213-minimal-numbers-of-variables)
    - [Relation bounds from representation obstructions](#214-relation-bounds-from-representation-obstructions)
    - [The unobstructed case](#215-the-unobstructed-case)
    - [Locally constrained presentation bounds](#216-locally-constrained-presentation-bounds)
    - [Universal versus versal rings in applications](#217-universal-versus-versal-rings-in-applications)
22. [Conclusion](#22-conclusion)
    - [The formal space assembled from finite tests](#221-the-formal-space-assembled-from-finite-tests)
    - [The role of automorphisms](#222-the-role-of-automorphisms)
    - [The endpoint](#223-the-endpoint)

## 1. From infinitesimal answers to a formal space

### 1.1 The representability question

Book 63 associated to a residual representation several covariant functors on local Artinian coefficient rings. Their values remember lifts, equivalence classes, frames, and determinants; their tangent spaces and small-extension obstructions are controlled by continuous cohomology. Those calculations do not yet say that all answers arise from one complete local ring. That is the new question.

A representing ring is valuable because it turns a family of classification problems into one object. If $R$ represents a functor $F$, then every $x\in F(A)$ is obtained from a unique continuous local map $R\to A$. Parameters become generators of $R$, compatibility conditions become relations, and compatible finite-order deformations assemble into a continuous deformation over $R$. But the word *unique* is severe. Automorphisms of objects can destroy uniqueness even when lifts always exist and tangent spaces are finite.

This book develops the bridge from infinitesimal information to formal geometry. The bridge has three pillars: gluing over fiber products, induction across small extensions, and finite-dimensionality of the tangent space. The first controls compatibility, the second controls nilpotent thickness, and the third ensures that the limiting ring is Noetherian rather than an infinite-variable object.

The development moves from the abstract criteria to their principal representation-theoretic applications. After constructing hulls and isolating the extra uniqueness condition for universality, we diagnose the automorphism obstruction, treat framed and scalar-centralizer problems, and impose determinants and other closed conditions. The final chapters reassemble finite-level data over complete coefficient rings, distinguish two kinds of coefficient change, construct global rings from local conditions by completed fiber products, and state finite-generation and relation bounds with every effectiveness hypothesis visible.

### 1.2 The coefficient categories

Fix a complete Noetherian local ring $(\mathcal O,\mathfrak m_{\mathcal O},k)$ with a specified residue-field identification $\mathcal O/\mathfrak m_{\mathcal O}\simeq k$. We assume $k$ is finite when representations of profinite groups are discussed. Let $\mathcal C=\operatorname{Art}_{\mathcal O}$ be the category of local Artinian $\mathcal O$-algebras $A$ equipped with the prescribed identification $A/\mathfrak m_A\simeq k$. Morphisms are local $\mathcal O$-algebra maps inducing the identity on $k$.

Let $\widehat{\mathcal C}=\operatorname{CNL}_{\mathcal O}$ consist of complete Noetherian local $\mathcal O$-algebras $R$ with residue field $k$, endowed with their maximal-ideal-adic topologies; morphisms are continuous local $\mathcal O$-maps inducing the identity on $k$. Equal characteristic is included by taking $\mathcal O=k$. Nothing in the abstract criteria requires a chosen embedding $k\hookrightarrow A$ in mixed characteristic.

We use the continuous-cohomology conventions and finite-quotient arguments of Book 24, the coefficient categories and completed fiber products of Book 57, the deformation and obstruction calculations of Book 63, and the cotangent, completion, and presentation results of Book 64. Every additional hypothesis needed here will be stated where it enters.

All functors in the main theory are covariant:

$$
F:\mathcal C\longrightarrow\mathbf{Sets}.
$$

Thus $A\to B$ gives $F(A)\to F(B)$. This agrees with extension of coefficients for representations. It is opposite to the variance of formal spectra, and that reversal will account for every contravariant map between representing rings.

### 1.3 The one-point residue condition

A local deformation problem is centered at one residual object. Its set of deformations over $k$ should therefore contain exactly that point.

**Definition.** A **deformation functor** on $\mathcal C$ is a covariant functor $F:\mathcal C\to\mathbf{Sets}$ such that $F(k)$ is a singleton.

We denote its unique element by $*$. This condition is not cosmetic. It makes every first-order object a tangent vector based at the same point and ensures that products such as $F(A')\times_{F(A)}F(A'')$ express gluing near one closed fiber. A functor parametrizing several residual isomorphism classes should first be decomposed or studied as a formal stack; it is not a one-point deformation functor in this sense.

**Counterexample.** The functor $A\mapsto\{0,1\}$ with identity transition maps has finite values and no lifting difficulty, but it has two closed points. No complete *local* ring with residue field $k$ represents it: every local residue-compatible map to $k$ is the unique residue map. Locality and the one-point condition are inseparable.

### 1.4 Fiber-product comparison maps

Suppose $A'\to A\leftarrow A''$ is a diagram in $\mathcal C$ and at least one arrow is surjective. Book 57 shows that

$$
B=A'\times_AA''
$$

is again an object of $\mathcal C$. The two projections induce a natural comparison map

$$
\eta_{A',A,A''}:F(B)\longrightarrow
F(A')\times_{F(A)}F(A'').
$$

The target consists of two deformations whose images over $A$ are equal as elements of the set $F(A)$. Surjectivity of $\eta$ says that compatible branch data can be glued. Injectivity says that the glued object is determined by its two branches. For moduli of actual matrices both assertions are often immediate; for isomorphism classes, equality over $A$ hides a choice of isomorphism, and injectivity becomes the delicate part.

This comparison map is the central diagnostic of the book. Representable functors preserve all such fiber products exactly. Hulls require enough surjectivity and first-order exactness to approximate that behavior without demanding full uniqueness.

## 2. Representable functors and inverse limits

### 2.1 Why the representing object is complete

An Artinian test ring sees only finitely many infinitesimal orders. A parameter that can vary to every order therefore cannot usually live in a single Artinian ring. The natural parameter ring is instead complete and recovered from its Artinian quotients.

For $R\in\widehat{\mathcal C}$ define

$$
h_R(A)=\operatorname{Hom}_{\mathrm{cts,loc},\mathcal O}(R,A).
$$

Since $A$ is Artinian and discrete, a local map $R\to A$ is continuous exactly when its kernel contains some power of $\mathfrak m_R$. Hence

$$
h_R(A)=\varinjlim_n
\operatorname{Hom}_{\mathcal C}(R/\mathfrak m_R^n,A).
$$

The expression explains the prefix *pro*: $R$ participates through the inverse system of its finite quotients. A coefficient map $A\to B$ acts by postcomposition, so $h_R$ is covariant in the test ring.

**Definition.** The functor $F$ is **pro-representable** if there are $R\in\widehat{\mathcal C}$ and a natural isomorphism $h_R\simeq F$. The ring $R$ is then a **universal deformation ring** for $F$.

The adjective “pro” refers to the complete inverse-limit object, not to an approximate uniqueness statement. Pro-representability gives an actual bijection on every Artinian test ring.

### 2.2 Universal elements at finite level

There may be no literal value $F(R)$ because $F$ was defined only on $\mathcal C$. The universal object is instead a compatible family

$$
\xi_n\in F(R/\mathfrak m_R^n).
$$

Under an isomorphism $h_R\simeq F$, the element $\xi_n$ corresponds to the quotient map $R\to R/\mathfrak m_R^n$. Compatibility is forced by functoriality. Conversely, a compatible family defines a natural transformation

$$
h_R\longrightarrow F,
$$

because a continuous $u:R\to A$ factors through some finite quotient and sends the corresponding $\xi_n$ to an element of $F(A)$. Independence of the chosen quotient follows from compatibility.

For representation functors, the compatible family is equivalent to a continuous representation into $\operatorname{GL}_d(R)$. Continuity is not an extra conclusion: it follows because reduction modulo every $\mathfrak m_R^n$ is continuous and the adic congruence subgroups form a neighborhood basis.

### 2.3 Exact gluing for mapping functors

**Proposition.** For every $R\in\widehat{\mathcal C}$ and every diagram $A'\to A\leftarrow A''$ in $\mathcal C$ for which the fiber product lies in $\mathcal C$, the map

$$
h_R(A'\times_AA'')\longrightarrow
h_R(A')\times_{h_R(A)}h_R(A'')
$$

is a bijection.

**Proof strategy.** No infinitesimal induction is needed. The assertion is simply the universal property of a ring fiber product, with continuity checked once.

**Proof.** A map $R\to A'\times_AA''$ is exactly a pair of maps $R\to A'$ and $R\to A''$ having equal composites to $A$. Locality and residue compatibility hold componentwise. Since all three targets are Artinian, the maps are continuous. The two constructions are inverse. $\square$

This proposition supplies all gluing necessities for representability. Schlessinger's conditions isolate a surprisingly small portion of this exactness that is sufficient to construct a hull.

### 2.4 Tangent space and cotangent space

Let $k[\epsilon]=k[\epsilon]/(\epsilon^2)$, regarded as an $\mathcal O$-algebra through $\mathcal O\to k$. Set

$$
t_F=F(k[\epsilon]).
$$

For a general functor this is initially only a pointed set. Under the first-order gluing condition introduced later it acquires a canonical $k$-vector-space structure. For a represented functor the calculation is immediate:

$$
t_{h_R}\simeq
\operatorname{Hom}_k\left(
\frac{\mathfrak m_R}{\mathfrak m_R^2+\mathfrak m_{\mathcal O}R},k
\right).
$$

The quotient on the right is the relative cotangent space. Thus tangent vectors of the functor are linear functionals on infinitesimal generators of the ring. If $R$ is Noetherian, this vector space is finite-dimensional. Consequently finite tangent dimension is necessary for pro-representability by an object of $\widehat{\mathcal C}$.

**Example.** The functor $A\mapsto\mathfrak m_A$ is represented by $\mathcal O[[X]]$: a continuous local $\mathcal O$-map is determined by the arbitrary image of $X$ in $\mathfrak m_A$. Its tangent space is $k$. More generally, the Cartesian-power functor $A\mapsto(\mathfrak m_A)^r$ is represented by $\mathcal O[[X_1,\ldots,X_r]]$.

**Counterexample.** If $I$ is an infinite set, $A\mapsto\mathfrak m_A^I$ has infinite-dimensional tangent space. It is represented in a broader topological category by an infinite-variable construction, but not by a complete Noetherian local ring. This is exactly why tangent finiteness belongs among the representability hypotheses.

### 2.5 Uniqueness of a representing ring

**Theorem.** If $h_R\simeq F\simeq h_S$ naturally with $R,S\in\widehat{\mathcal C}$, then $R$ and $S$ are uniquely isomorphic in the manner compatible with the two displayed representations.

**Proof strategy.** The finite quotients play the role of test objects on which the universal maps can be evaluated. Naturality then forces inverse maps at every precision.

**Proof.** The natural isomorphism $h_R\simeq h_S$, evaluated on the quotient maps $S\to S/\mathfrak m_S^n$, produces compatible maps $R\to S/\mathfrak m_S^n$. Their inverse limit is a continuous local map $R\to S$. Reversing the isomorphism gives $S\to R$. Naturality applied to finite quotients shows that both composites induce the identity modulo every power of the maximal ideal. Completeness and separatedness make the composites identities. The same argument shows uniqueness subject to compatibility with the chosen natural isomorphisms. $\square$

Without a specified identification with $F$, two representing rings are isomorphic but may have automorphisms. Universality makes the object unique in the categorical sense; it does not canonically label its coordinates.

## 3. Infinitesimal lifting properties

### 3.1 Small extensions as atomic tests

A surjection $A'\twoheadrightarrow A$ in $\mathcal C$ is **small** if its kernel $I$ is a principal $A'$-module annihilated by $\mathfrak m_{A'}$. Equivalently, $I\simeq k$ as a vector space after choosing a generator and $\mathfrak m_{A'}I=0$. Some arguments allow a finite-dimensional socle kernel; our chosen Schlessinger formulation uses principal small extensions, and factors larger surjections into these atomic steps.

Every surjection in $\mathcal C$ is a finite composite of small extensions. Therefore a lifting property verified for small extensions propagates to arbitrary Artinian surjections. The distinction remains important: a square-zero extension need not be small, because its kernel may retain a nontrivial action of the maximal ideal.

### 3.2 Formal smoothness of a natural transformation

Suppose $\phi:F\to G$ is a natural transformation of deformation functors. A lift in $F(A')$ should exist whenever compatible data are given in $F(A)$ and $G(A')$. This leads to the comparison

$$
F(A')\longrightarrow F(A)\times_{G(A)}G(A').
$$

**Definition.** The transformation $\phi$ is **formally smooth** if this map is surjective for every surjection $A'\twoheadrightarrow A$ in $\mathcal C$.

It is enough to test principal small extensions: factor an arbitrary surjection and lift successively. Formal smoothness concerns existence only. It says neither that lifts are unique nor that $F$ or $G$ is representable.

When $G$ is the terminal one-point functor, formal smoothness says $F(A')\to F(A)$ is surjective for every Artinian surjection. For a represented functor $h_R$, this means every map $R\to A$ lifts to $A'$. Power-series rings are the basic formally smooth objects.

### 3.3 Formal unramifiedness and formal etaleness

**Definition.** The transformation $\phi:F\to G$ is **formally unramified** if

$$
F(A')\longrightarrow F(A)\times_{G(A)}G(A')
$$

is injective for every small extension $A'\twoheadrightarrow A$. It is **formally etale** if it is both formally smooth and formally unramified.

Small extensions suffice for injectivity over all Artinian surjections as well: compare two candidates successively down a factorization, beginning at the bottom. Formal unramifiedness is uniqueness relative to the target. In particular, a map $h_R\to F$ can be a hull because it is smooth and tangent-bijective without being unramified; that remaining failure of uniqueness is precisely the gap between a hull and a representing object.

For a homomorphism $R\to S$ the induced transformation $h_S\to h_R$ is formally smooth exactly when maps $S\to A$ can be lifted relative to compatible maps from $R$. Notice the reversal: formal smoothness of the transformation corresponds to formal smoothness of $S$ as an $R$-algebra.

### 3.4 Versal maps and hulls

A natural transformation

$$
q:h_R\longrightarrow F
$$

is **versal** if it is formally smooth. It is a **hull** if it is versal and the induced tangent map

$$
t_{h_R}\longrightarrow t_F
$$

is a bijection.

Versality says every deformation over an Artinian ring is locally reached, by induction through nilpotent thickenings, from a map out of $R$. A hull adds minimality at first order: it has exactly the right number of infinitesimal parameters. Yet maps $R\to A$ producing the same deformation may still differ. Thus

$$
\text{pro-representation}\Longrightarrow\text{hull}
\Longrightarrow\text{versal map},
$$

and neither converse holds in general.

**Example.** If $F=h_R$, the identity is a hull and a representation. The map $h_{R[[T]]}\to h_R$ induced by $R\to R[[T]]$ is versal: an image of $T$ can always be lifted across a surjection. It is not a hull because its tangent map has a one-dimensional kernel. This illustrates why tangent minimality must be imposed separately.

### 3.5 Uniqueness properties of hulls

Two representing rings compatible with a fixed functor identification are uniquely isomorphic. Hulls obey a weaker statement.

**Proposition.** If $h_R\to F$ and $h_S\to F$ are hulls, then $R\simeq S$ as complete local $\mathcal O$-algebras, but the isomorphism need not be unique and need not identify the two maps to $F$ in a unique way.

**Proof strategy.** Formal smoothness lifts the compatible universal systems in both directions. Tangent minimality makes the resulting ring maps isomorphisms rather than proper formally smooth enlargements.

At finite level, versality gives compatible maps $R\to S/\mathfrak m_S^n$ and $S\to R/\mathfrak m_R^n$ after successive choices. Passing to limits gives continuous maps in both directions. Their composites induce isomorphisms on relative cotangent spaces because both hull maps induce tangent isomorphisms. The complete cotangent criterion therefore makes each composite surjective. A surjective endomorphism of a Noetherian ring is injective, so the composites are automorphisms and either cross-map is an isomorphism. Replacing one cross-map by the inverse of the other gives inverse isomorphisms. The choices made in the finite-level liftings need not be unique, so no canonical isomorphism results. $\square$

This distinction matters in applications: dimensions and presentation types extracted from a hull are meaningful, but a point over every test ring is represented uniquely only when the stronger criterion holds.

## 4. Schlessinger's four conditions

### 4.1 The chosen formulation

We now state one precise version of the criterion. For a deformation functor $F$ and a diagram $A'\to A\leftarrow A''$, write $\eta$ for the comparison map of Section 1.4.

**(H1)** The map $\eta$ is surjective whenever $A''\twoheadrightarrow A$ is a principal small extension.

**(H2)** The map

$$
F(A'\times_k k[\epsilon])\longrightarrow
F(A')\times F(k[\epsilon])
$$

is bijective for every $A'\in\mathcal C$.

**(H3)** The tangent space $t_F=F(k[\epsilon])$ is finite-dimensional over $k$.

**(H4)** The map

$$
F(A'\times_AA')\longrightarrow
F(A')\times_{F(A)}F(A')
$$

is bijective whenever $A'\twoheadrightarrow A$ is a principal small extension.

Condition (H2) includes the assertion that the tangent set carries the expected additive behavior and that an independent first-order direction glues uniquely onto every $A'$. We will use exactly the displayed four conditions; this fixes the convention, since labels (H1)--(H4) are not uniform across all accounts of the criterion.

**Schlessinger theorem.** A deformation functor $F$ admits a hull if and only if it satisfies (H1), (H2), and (H3). It is pro-representable if and only if it satisfies (H1), (H2), (H3), and (H4).

The theorem concerns set-valued functors on the fixed coefficient category. It does not say that every moduli problem has a canonical obstruction theory, nor that a functor with infinite tangent space is meaningless. It identifies exactly when the formal moduli problem is controlled by a complete Noetherian local ring in the stated senses.

### 4.2 What each condition controls

Condition (H1) is existence of gluing when one branch differs by one socle layer. It is the engine of inductive construction. Condition (H2) normalizes first-order gluing and makes tangent directions linear and independent. Condition (H3) changes a potentially infinite formal object into a quotient of a finite-variable power-series ring. Condition (H4) removes the residual ambiguity in gluing two copies of the same small thickening; it is the uniqueness input absent from a mere hull.

The asymmetry in (H1) is harmless. Once one arrow is small, swapping the two factors gives the analogous statement with the other arrow small. General Artinian surjections can be factored into small ones, so repeated use of (H1) handles thicker kernels.

### 4.3 The vector-space structure on the tangent set

Why may (H3) call $t_F$ a vector space? Let $k\oplus V$ denote the split local algebra with square-zero ideal $V$. Condition (H2), iterated from one-dimensional summands, identifies

$$
F(k\oplus V)\simeq t_F\otimes_k V
$$

for finite-dimensional $V$. More concretely, addition on $t_F$ is induced by first gluing two tangent vectors over

$$
k[\epsilon_1,\epsilon_2]/(\epsilon_1,\epsilon_2)^2
$$

and then applying the map $\epsilon_1,\epsilon_2\mapsto\epsilon$. Scalar multiplication by $a\in k$ comes from $\epsilon\mapsto a\epsilon$. Functoriality and the uniqueness in (H2) give the vector-space axioms.

This construction is intrinsic. No coordinates or representing ring have been assumed. When $F$ is a representation deformation functor, it recovers the cohomological vector-space structures on $Z^1$ or $H^1$ from Book 63.

### 4.4 Necessity for representable functors

**Theorem.** Every functor pro-represented by $R\in\widehat{\mathcal C}$ satisfies (H1)--(H4).

**Proof strategy.** Exact preservation of fiber products proves all gluing conditions at once; Noetherianity supplies finite tangent dimension.

**Proof.** Section 2.3 gives a bijection

$$
h_R(A'\times_AA'')\simeq
h_R(A')\times_{h_R(A)}h_R(A'')
$$

for every relevant diagram. Hence (H1), (H2), and (H4) hold, in fact in stronger forms with no smallness restriction. Section 2.4 identifies the tangent space with the dual of

$$
\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R).
$$

The latter is finite-dimensional because $R$ is Noetherian, proving (H3). $\square$

This proof exposes two logically separate necessities. Exact gluing comes from being a mapping functor. Tangent finiteness comes not from representability in an unrestricted pro-category, but from the Noetherian condition on the representing ring.

### 4.5 Small tests versus arbitrary fiber products

The criterion asks for only selected fiber products, while representability yields all of them. The gap is intentional. Conditions (H1)--(H3) let one build a formally smooth approximation; (H4) makes that approximation formally unramified. Once a hull map is both smooth and unramified, an induction on the length of test rings shows it is bijective everywhere, and exact preservation of arbitrary admissible fiber products follows afterward.

It would be incorrect to replace (H4) by the statement that $F(A')\to F(A)$ is injective for small extensions. Most deformation functors have many genuine lifts of one object. Condition (H4) does not suppress those choices; it says that two compatible choices on two branches have a unique common origin.

### 4.6 Necessity of (H1)--(H3) for a hull

The necessity statement for hulls is slightly subtler than the representable case because a hull map need not be injective.

**Proposition.** If $q:h_R\to F$ is a hull with $R\in\widehat{\mathcal C}$, then $F$ satisfies (H1), (H2), and (H3).

**Proof strategy.** Lift compatible branch data to maps out of $R$, use exact gluing for $h_R$, and correct mismatches by formal smoothness. In the split first-order case, the tangent isomorphism makes the correction unique.

**Proof.** Finite-dimensionality (H3) follows from $t_F\simeq t_{h_R}$ and Noetherianity of $R$. For (H1), begin with compatible $x'\in F(A')$ and $x''\in F(A'')$, where $A''\to A$ is small. Versality gives $f':R\to A'$ representing $x'$, and let $f_A$ be its composite with $A$. Since $q(f_A)$ is the image of $x''$, formal smoothness for $A''\twoheadrightarrow A$ gives $f'':R\to A''$ with $f''\bmod A=f_A$ and $q(f'')=x''$. Thus the two source maps agree literally over $A$. Exact gluing for $h_R$ gives a map to $A'\times_AA''$, whose image is the desired glued object.

For (H2), the same argument gives surjectivity. Injectivity uses the split-correction lemma: if a formally smooth transformation $h_R\to F$ is a tangent isomorphism, then for every $A'$ the map

$$
F(A'\times_k k[\epsilon])\longrightarrow
F(A')\times F(k[\epsilon])
$$

is injective. To prove the lemma, filter $A'$ by principal small extensions and compare two candidates from the residue field upward. Formal smoothness chooses source representatives at each step. Exact gluing for $h_R$ makes their difference in the new split branch an element of $t_{h_R}$ tensored with the socle kernel. Its image is the corresponding difference in $t_F$; if the two $F$-objects agree on both branches, this image is zero. Tangent bijectivity makes the source difference zero, so the representatives, and hence the two candidates, agree at that step. Induction proves the lemma and (H2). $\square$

Thus the hull criterion is genuinely an equivalence: the three conditions are not merely a convenient sufficient recipe.

### 4.7 Extending gluing beyond principal kernels

Repeated small-extension arguments will be used silently later, so it is helpful to record their exact scope.

**Lemma.** If $F$ satisfies (H1), then $\eta_{A',A,A''}$ is surjective whenever $A''\twoheadrightarrow A$ is any surjection in $\mathcal C$.

**Proof.** Factor $A''\to A$ into principal small extensions

$$
A''=A_m\twoheadrightarrow A_{m-1}\twoheadrightarrow\cdots
\twoheadrightarrow A_0=A.
$$

Starting from compatible elements over $A'$ and $A_m$, first glue the $A'$-element to the image over $A_1$. Next glue the resulting object over $A'\times_AA_1$ to the image over $A_2$ along $A_2\to A_1$. The ring identity

$$
(A'\times_AA_i)\times_{A_i}A_{i+1}
\simeq A'\times_AA_{i+1}
$$

shows that each step advances the desired gluing. After $m$ steps one obtains an object over $A'\times_AA''$. $\square$

The analogous propagation of formal smoothness is proved the same way. For uniqueness one needs the relevant injectivity hypothesis at each step; existence alone never manufactures it.

## 5. The power-series source

### 5.1 Tangent dimension counts generators

Assume (H2) and (H3), and set $r=\dim_k t_F$. Choose a basis $v_1,\ldots,v_r$ of $t_F$. Let

$$
P=\mathcal O[[X_1,\ldots,X_r]].
$$

Its relative cotangent space has basis given by the classes of the variables, while

$$
t_{h_P}=\operatorname{Hom}_k
\left(\frac{\mathfrak m_P}{\mathfrak m_P^2+\mathfrak m_{\mathcal O}P},k\right)
$$

has the dual basis. The chosen basis of $t_F$ therefore specifies a tangent isomorphism $t_{h_P}\simeq t_F$.

The variables are not tangent vectors themselves. They are cotangent generators, and a tangent vector evaluates them. This duality reverses many informal descriptions and is worth keeping explicit.

### 5.2 A first-order universal element

Put

$$
P_1=P/(\mathfrak m_{\mathcal O}P+\mathfrak m_P^2).
$$

Its maximal ideal is a square-zero $k$-space spanned by the $X_i$. By the vector-space form of (H2), the tensor

$$
\sum_{i=1}^r v_i\otimes X_i
$$

determines an element $\xi_1\in F(P_1)$. The resulting transformation $h_{P_1}\to F$ induces the prescribed tangent isomorphism.

This is the easy stage of representability: any finite tangent space has a formal affine space with the right derivative. Relations and higher-order compatibility have not yet appeared.

### 5.3 Minimality and changes of coordinates

Choosing another basis of $t_F$ changes the variables by an invertible linear transformation. Lifting that transformation to $P$ gives an automorphism of the power-series ring. Thus the power-series source is noncanonical but its number of variables is intrinsic.

If a complete local ring $R$ is eventually obtained as a quotient of $P$ and the tangent map is an isomorphism, then the kernel lies in

$$
\mathfrak m_P^2+\mathfrak m_{\mathcal O}P.
$$

There are no linear relations among a minimal set of variables relative to $\mathcal O$. Conversely, any presentation with a redundant variable produces a cotangent space larger than $t_F$ and cannot be a hull presentation.

### 5.4 Why finite tangent dimension gives Noetherianity

The eventual hull ring will be $R=P/J$ for a closed ideal $J$. Since $P$ is Noetherian, every ideal is finitely generated and closed, and $R$ is complete Noetherian local. This is the precise point at which (H3) enters the construction.

Without (H3), one may still attempt an inverse limit of Artinian approximations, but it need not be a quotient of a finite-variable power-series ring and need not be Noetherian. Obstruction spaces being finite-dimensional do not repair an infinite tangent space: obstructions govern relations, not the number of generators.

## 6. Constructing a hull

### 6.1 The architecture of the sufficiency proof

We now prove the difficult direction of the theorem. Assume (H1)--(H3). The proof proceeds in four stages.

1. Start with the finite-variable ring $P$ dictated by $t_F$.
2. Construct compatible Artinian quotients $R_n=P/J_n$ and elements $\xi_n\in F(R_n)$, one nilpotent order at a time.
3. Arrange a finite-level versality property by killing exactly those quotient directions across which $\xi_n$ cannot lift.
4. Pass to $R=\varprojlim R_n=P/J$ and prove that $h_R\to F$ is formally smooth with tangent isomorphism.

The choices are genuine. At each stage there may be several lifts and several complements to obstruction subspaces. They explain why a hull is not canonical. What must be canonical is the property achieved by the construction.

### 6.2 The finite-stage lemma

The construction is governed by the following lemma, whose proof contains the compactness and obstruction control needed at the limit.

**Finite-stage lemma.** Suppose $F$ satisfies (H1), (H2), and (H3). There are ideals

$$
J_1\supseteq J_2\supseteq\cdots\subset P
$$

and compatible elements $\xi_n\in F(R_n)$, where $R_n=P/J_n$, such that:

1. every $J_n$ is open and $R_n\in\mathcal C$;
2. $R_{n+1}\twoheadrightarrow R_n$ and $\xi_{n+1}$ maps to $\xi_n$;
3. $\mathfrak m_PJ_n\subseteq J_{n+1}\subseteq J_n$;
4. if $B'\twoheadrightarrow B$ is principal small, then every map $u:R_n\to B$ and every $y'\in F(B')$ whose image is $F(u)(\xi_n)$ admit a map $u':R_{n+1}\to B'$ such that

   $$
   u'\bmod B=u\circ(R_{n+1}\twoheadrightarrow R_n),
   \qquad F(u')(\xi_{n+1})=y';
   $$

5. the tangent map defined by $\xi_n$ is the fixed isomorphism $t_{h_P}\simeq t_F$.

The fourth clause is a precise finite-level formal smoothness statement: every lifting question based on the $n$th approximation is solved by the next approximation. Clause 3 makes the transition kernel a quotient of a finite-dimensional socle layer. It also gives the cofinality needed to identify the inverse limit with a maximal-adically complete quotient of $P$.

### 6.3 Proof of the finite-stage lemma

**Strategy.** The universal small extension of $R_n=P/J_n$ dominated by $P$ is obtained by replacing $J_n$ with $\mathfrak m_PJ_n$. All new information lies in its finite-dimensional socle kernel. Candidate quotients correspond to subspaces of that kernel. Conditions (H1) and (H2) give two correction principles: liftable quotient directions are closed under sums, and a discrepancy in a split socle direction can be removed by a tangent vector. A maximal liftable quotient then solves every lifting problem based on $R_n$. Recording this relative statement, rather than mere existence of $\xi_{n+1}$, prevents circularity when formal smoothness is proved at the limit.

**Proof.** The first stage is $P_1$ and $\xi_1$ from Section 5.2. Assume $(R_n,\xi_n)$ has been constructed. Consider

$$
\widetilde R_{n+1}=P/\mathfrak m_PJ_n.
$$

Its kernel over $R_n$ is

$$
K_n=J_n/\mathfrak m_PJ_n,
$$

a finite-dimensional $k$-vector space annihilated by the maximal ideal. The ring $\widetilde R_{n+1}$ is Artinian because $J_n$ is open. Every quotient extension of $R_n$ dominated by $\widetilde R_{n+1}$ is obtained by quotienting $K_n$ by a subspace.

We first make the correction principle precise. If $E\twoheadrightarrow R_n$ has finite-dimensional kernel $Q$ annihilated by $\mathfrak m_E$, then the iterated form of (H2) gives an action of

$$
t_F\otimes_kQ
$$

on every nonempty fiber of $F(E)\to F(R_n)$, and (H1) makes that action transitive. Indeed,

$$
E\times_{R_n}E\simeq E\times_k(k\oplus Q),
\qquad
(e_1,e_2)\longmapsto(e_1,\overline e_1+e_2-e_1).
$$

Under (H2), the second factor records an element of $F(k\oplus Q)=t_F\otimes_kQ$; the second projection gives the action. Surjectivity in (H1), first for one-dimensional subkernels and then by Section 4.7, proves transitivity. On the source side, changing lifts of the variables of $P$ by elements of $Q$ gives the analogous action of $t_{h_P}\otimes_kQ$. Because $J_n\subseteq J_1=\mathfrak m_{\mathcal O}P+\mathfrak m_P^2$, these variable translations preserve every quotient extension of $R_n$ dominated by $\widetilde R_{n+1}$. The fixed tangent isomorphism $t_{h_P}\simeq t_F$ therefore realizes every target correction by a source translation. In particular, any two lifts of $\xi_n$ to the same quotient extension are carried to one another after changing the quotient map by such a translation.

Let $\mathscr L$ be the collection of quotient spaces $K_n\twoheadrightarrow Q$ for which $\xi_n$ lifts to the corresponding extension $R_{n,Q}$. It is nonempty because $Q=0$ is allowed. Suppose lifts exist over quotients with kernels $L_1,L_2\subseteq K_n$. Section 4.7 glues them over

$$
E=R_{n,Q_1}\times_{R_n}R_{n,Q_2}.
$$

The diagonal map from $\widetilde R_{n+1}$ has image

$$
D=\widetilde R_{n+1}/(L_1\cap L_2)\subseteq E.
$$

Its kernel over $R_n$ is the image of $K_n$ in $Q_1\oplus Q_2$. Choose a $k$-linear complement $W$ to that image in $Q_1\oplus Q_2$. Since the whole kernel is annihilated by the maximal ideal, writing $E=D\oplus W$ additively and killing $W$ defines a local $\mathcal O$-algebra retraction $E\to D$. Pushing the glued object along this retraction gives a lift of $\xi_n$ to $D$. Thus liftability is closed under intersection of kernels. It follows that the intersection of the kernels of all liftable quotients is again the kernel of a largest liftable quotient $Q_n^{\max}$.

All vector spaces here are finite-dimensional: $P$ has finitely many variables and $\mathcal O$ is Noetherian. Hence only a finite subcollection is needed to realize that intersection. Repeated (H1) glues their chosen lifts to an element over the largest quotient. Define $R_{n+1}=R_{n,Q_n^{\max}}$ and choose one such lift $\xi_{n+1}$.

It remains to see why maximal liftability gives clause 4. Given a principal small extension $B'\twoheadrightarrow B$ and compatible data, form

$$
C=R_n\times_BB'.
$$

The projection $C\twoheadrightarrow R_n$ has kernel $I$ and is small. Condition (H1) glues $\xi_n$ and $y'$ to an object $z\in F(C)$. Choose lifts to $C$ of the images of the finitely many variables of $P$. Because the resulting map kills $J_n$ modulo $I$ and $\mathfrak m_CI=0$, it kills $\mathfrak m_PJ_n$; hence it factors through $\widetilde R_{n+1}$.

Let $D$ be the image of $\widetilde R_{n+1}\to C$. The map $D\to R_n$ is surjective, and its kernel is a subspace of the one-dimensional space $I$. There are exactly two cases. If $\ker(D\to R_n)=I$, then $D=C$, so $z$ itself exhibits this quotient of $\widetilde R_{n+1}$ as liftable. If the kernel is zero, then $D\simeq R_n$ is a section of $C\to R_n$. The object induced from $\xi_n$ along this section and $z$ have the same reduction to $R_n$. Their difference lies in the transitive $t_F\otimes_kI$-action described above. The tangent isomorphism changes the section by a source translation whose image is exactly that difference. After the change, $z$ is induced from $D$. Thus in either case there are a liftable quotient $R_{n,Q}$ and a map $R_{n,Q}\to C$ carrying a lift of $\xi_n$ to $z$.

Maximality gives a map $R_{n+1}\to R_{n,Q}$. Its chosen lift need not initially map to the particular lift just obtained, but the two lie in the same fiber over $\xi_n$. Transitivity and the source-translation statement give a corrected map $R_{n+1}\to R_{n,Q}$ that carries $\xi_{n+1}$ to that lift. Composing with $R_{n,Q}\to C\to B'$ gives the required $u'$. This proves clause 4. The inclusions in clause 3 hold by construction, openness propagates because $\mathfrak m_PJ_n$ is open, and clause 5 remains fixed because all translations vanish on the first-order quotient. $\square$

The maximal quotient is intrinsic once the preceding pair is fixed, but the lift $\xi_{n+1}$ is not. This is where obstruction control enters without assuming that $F$ comes equipped with a canonical obstruction space.

### 6.4 Passage to the complete ring

Set

$$
J=\bigcap_{n\geq1}J_n,
\qquad
R=P/J.
$$

The descending-ideal lemma for a complete Noetherian local ring says that, for each $d$, the images of the $J_n$ in $P/\mathfrak m_P^d$ eventually equal the image of their intersection $J$. One proves it by choosing compatible representatives modulo successive maximal-ideal powers; completeness produces an element of every $J_n$, and separatedness identifies its limit. Thus $J_n\subseteq J+\mathfrak m_P^d$ for all sufficiently large $n$. Conversely, openness of $J_1$ gives a $c$ with $\mathfrak m_P^c\subseteq J_1$, while clause 3 gives

$$
\mathfrak m_P^{n+c}\subseteq\mathfrak m_P^nJ_1\subseteq J_{n+1}.
$$

The filtration induced by the $J_n$ on $P/J$ is therefore cofinal with the maximal-ideal powers. It follows that

$$
R\simeq\varprojlim_nR_n.
$$

Because $P$ is complete Noetherian and $J$ is closed, $R$ is an object of $\widehat{\mathcal C}$. In fact every ideal of the Noetherian adic ring $P$ is closed, so no hidden non-Hausdorff quotient occurs. The compatible elements $\xi_n$ define a natural transformation

$$
q:h_R\longrightarrow F.
$$

Continuity is automatic in the correct direction: any map $R\to A$ with $A$ Artinian kills a maximal-ideal power, hence kills some $J_n/J$ by cofinality and factors through $R_n$. The system $(\xi_n)$ then supplies the element to push forward.

### 6.5 Formal smoothness of the limit map

**Proposition.** The transformation $q:h_R\to F$ is formally smooth.

**Proof strategy.** Reduce to one small extension. A map from $R$ to its Artinian target factors through a finite stage, and finite-stage versality solves precisely that lifting problem.

**Proof.** Let $A'\twoheadrightarrow A$ be principal small. Suppose $u:R\to A$ and $y'\in F(A')$ have compatible images in $F(A)$. Choose $n$ such that $u$ factors through $u_n:R_n\to A$. Clause 4 gives a compatible map $R_{n+1}\to A'$. Composing $R\to R_{n+1}$ yields $u':R\to A'$ lifting $u$ and carrying the universal system to $y'$. Thus the defining comparison map is surjective. Factorization of arbitrary Artinian surjections into principal small extensions gives formal smoothness in the stated definition. $\square$

The tangent map is the chosen isomorphism because no stage changed the first-order universal element. Hence $q$ is a hull. This proves the sufficiency of (H1)--(H3).

### 6.6 Choices, completeness, and what has been proved

Three common shortcuts would invalidate the argument. First, nonemptiness of a lift set at every order does not by itself produce compatible lifts; the inductive choice of $\xi_{n+1}$ does. Second, an arbitrary inverse limit of Artinian rings need not be Noetherian; realizing every stage as a quotient of the fixed finite-variable $P$ proves Noetherianity. Third, maps from the limit must be continuous; factorization through a finite quotient is what lets the universal system act on Artinian tests.

We have produced a hull, not a universal ring. The construction guarantees that every relative lifting problem has a solution, but it has not proved that the map $h_R(A)\to F(A)$ is injective.

## 7. From a hull to a representing object

### 7.1 The missing uniqueness condition

Assume $q:h_R\to F$ is a hull. Given $x\in F(A)$, formal smoothness constructs at least one map $R\to A$ producing it. If two maps produce the same $x$, their first possible difference occurs across a small extension. Condition (H4) is designed to rule out precisely that first difference.

**Rigidity lemma.** If $F$ satisfies (H4), every hull $q:h_R\to F$ is a natural isomorphism.

**Proof strategy.** Surjectivity follows by lifting from the residue field through a small-extension filtration. For injectivity, assume equality is known modulo a small kernel, encode two candidates as one map to a self-fiber product, and use (H4) together with the tangent isomorphism to eliminate their difference.

**Proof.** Let $A\in\mathcal C$ and choose a chain

$$
A=A_n\twoheadrightarrow A_{n-1}\twoheadrightarrow\cdots
\twoheadrightarrow A_0=k
$$

of principal small extensions. Starting from the unique map $R\to k$, formal smoothness lifts successively to show that $q_A:h_R(A)\to F(A)$ is surjective.

For injectivity, argue by induction on the length of $A$. Let $A\twoheadrightarrow A_0$ be small with kernel $I$, and suppose $f,g:R\to A$ have $q(f)=q(g)$. By induction their reductions to $A_0$ agree. They therefore determine a map

$$
(f,g):R\longrightarrow A\times_{A_0}A.
$$

The two projections of its image under $q$ are the same element of $F(A)$. By (H4), there is only one element of $F(A\times_{A_0}A)$ with this ordered pair of projections.

Compare $(f,g)$ with the map obtained by using the first component on both branches. Their possible discrepancy is supported on the square-zero anti-diagonal copy of $I$. By (H2), such discrepancies form $t_{h_R}\otimes_k I$ on the source and $t_F\otimes_k I$ on the target. The two images in $F(A\times_{A_0}A)$ agree by (H4), so the discrepancy maps to zero. Since the tangent map of a hull is an isomorphism, the discrepancy is zero. Thus $f=g$. Induction proves injectivity for every $A$. $\square$

Combining the hull construction with the rigidity lemma proves the sufficiency of (H1)--(H4) for pro-representability.

### 7.2 Why (H4) is stronger than tangent uniqueness

The tangent map of a hull is already bijective, so there is no ambiguity over $k[\epsilon]$. Condition (H4) monitors ambiguity *relative to every nontrivial lower-order object*. Automorphisms can be invisible over $k$ yet become visible over $A$ and alter how two higher-order branches are glued. This is why no calculation confined to the tangent space can replace (H4).

The simplest square-zero fiber product

$$
k[\epsilon,\eta]/(\epsilon^2,\epsilon\eta,\eta^2)
=k[\epsilon]\times_k k[\eta]
$$

usually behaves perfectly even for unframed representations. A genuine failure requires a nontrivial common quotient carrying an automorphism that does not lift compatibly.

### 7.3 Universal rings and coordinate choices

Once $F\simeq h_R$, an element of $F(A)$ determines a unique map $R\to A$. The ring $R$ itself may be presented in many ways:

$$
R\simeq\mathcal O[[X_1,\ldots,X_r]]/J.
$$

Changing a tangent basis changes the variables, and changing lifts of higher-order parameters changes the presentation. These are coordinate changes on one universal formal space, not failures of universality.

The minimal number $r$ is intrinsic:

$$
r=\dim_k t_F
=\dim_k\frac{\mathfrak m_R}{\mathfrak m_R^2+\mathfrak m_{\mathcal O}R}.
$$

Relations in $J$ record the failure of tangent directions to extend independently. Even when an obstruction space is known, it generally bounds the number of relations rather than canonically listing them.

## 8. Obstruction theories as verification devices

### 8.1 Why obstruction spaces are auxiliary

The Schlessinger conditions are intrinsic statements about a functor. In concrete problems they can be awkward to verify directly. An obstruction theory replaces repeated lifting calculations by linear data attached to small extensions. It is a sufficient mechanism, not part of the definition of a deformation functor, and there need not be a preferred one.

Let $V$ be a $k$-vector space. A basic obstruction theory assigns to every small extension

$$
e:0\to I\to A'\to A\to0
$$

and every $x\in F(A)$ an element

$$
\operatorname{ob}_e(x)\in V\otimes_k I,
$$

functorially under morphisms of extensions, such that $\operatorname{ob}_e(x)=0$ whenever $x$ lifts. It is **complete** if vanishing is also sufficient.

For representation deformations, Book 63 constructed a complete theory with $V=H^2(G,\operatorname{ad}\bar\rho)$ for unrestricted lifts. If a continuous lift of $\det\bar\rho$ has been fixed and the fixed-determinant lifting calculation identifies infinitesimal determinant-one changes with $\operatorname{ad}^0\bar\rho$, the same construction uses $V=H^2(G,\operatorname{ad}^0\bar\rho)$. In residue characteristic dividing $d$, this statement does not identify fixed determinant with a direct summand of the unrestricted problem.

### 8.2 Obstructions, lift torsors, and gluing

An obstruction class alone controls existence of a lift but does not automatically give (H2) or (H4). A particularly effective package consists of:

1. a complete functorial obstruction theory;
2. whenever the obstruction vanishes, a simply transitive action of $t_F\otimes_k I$ on rigidified lifts;
3. compatibility of these actions with pushout of small extensions and with fiber products;
4. control of automorphisms when rigidifications are forgotten.

Under these hypotheses, compatible branch objects have equal obstruction classes after restriction. Their difference can be corrected by the tangent action, giving (H1). Split square-zero extensions give (H2). If the action remains free after passing to the set-valued problem, the same comparison gives (H4).

The fourth point is essential. For a groupoid of representations, $H^1\otimes I$ acts transitively on rigidified lift classes while $H^0\otimes I$ measures automorphisms. Passing to isomorphism classes can turn a torsor into a quotient. Thus $H^2=0$ may imply formal smoothness while leaving representability unresolved.

### 8.3 Unobstructed does not mean representable

Suppose a complete obstruction theory has zero obstruction space. Then every object lifts through every small extension and, by factorization, every Artinian surjection. This says that the deformation problem is formally smooth over the one-point functor. Vanishing of a merely necessary obstruction class would not justify this conclusion; completeness is essential. Even with completeness, unobstructedness does not imply finite tangent dimension or unique gluing.

For example, a coarse unframed representation problem may have vanishing $H^2$ and a finite $H^1$, yet a nonscalar stabilizer can violate (H4). Conversely, a representable functor can be obstructed: $h_{k[[X]]/(X^2)}$ is represented, but the map sending $X$ to $\epsilon$ over $k[\epsilon]/(\epsilon^2)$ does not lift to a map sending $X$ to an element with leading term $\epsilon$ in $k[\epsilon]/(\epsilon^3)$, because its square is $\epsilon^2\neq0$.

### 8.4 Relation bounds from obstruction spaces

Suppose $F$ has a hull

$$
R=P/J,
\qquad P=\mathcal O[[X_1,\ldots,X_r]],
$$

and a complete obstruction theory with finite-dimensional obstruction space $V$. Assume in addition that obstruction classes are functorial for pushouts, additive in the kernel, and effective in the sense that a relation direction with zero universal obstruction can be removed by a lift. Then the universal obstruction assignment gives an injection from the dual of the minimal relation space

$$
\left(\frac{J}{\mathfrak m_PJ}\right)^\vee
$$

into $V$. Indeed, an element in its kernel would be a first-order relation direction on which every obstruction vanishes; effectiveness would lift the universal element after deleting that relation, contradicting minimality of the relation space. Thus

$$
\dim_k J/\mathfrak m_PJ\leq\dim_kV.
$$

In a minimal presentation this bounds the number of generators needed for $J$. If the coefficient base itself carries relations, the statement is relative to the fixed base $\mathcal O$: only relations added in passing from $P$ to $R$ are counted. Completeness of the obstruction theory by itself is not enough for this numerical bound; the displayed compatibility and effectiveness are substantive hypotheses, not consequences of the existence of a hull.

One should not conclude that $R$ is cut out by $\dim V$ canonical equations. An obstruction theory can contain redundant classes, and different obstruction theories can describe the same functor. Its robust use is to prove lifting and bound relations.

## 9. Automorphisms and failure of coarse representability

### 9.1 Equality of classes hides an arrow

Let $D_{\bar\rho}$ be the unframed functor from Book 63. Two branch classes over $A'$ and $A''$ with equal images in $D_{\bar\rho}(A)$ are represented by lifts whose reductions are strictly conjugate, not necessarily equal. Choosing a conjugator makes them equal and permits matrix gluing. A different choice differs by a strict automorphism of the common reduction.

For fixed branch representatives, the possible glued classes are controlled by

$$
\operatorname{im}\operatorname{Aut}^{\mathrm{str}}_{A'}(\rho')
\backslash
\operatorname{Aut}^{\mathrm{str}}_A(\rho_A)
/
\operatorname{im}\operatorname{Aut}^{\mathrm{str}}_{A''}(\rho'').
$$

A nontrivial double coset gives two global classes with identical branches. That is exactly failure of injectivity of the fiber-product comparison map.

### 9.2 An explicit stabilizer failure

We now exhibit the mechanism beyond first order. Let $k$ be a finite field, let $G=\widehat{\mathbf Z}$, and take the trivial residual two-dimensional representation. Put

$$
A'=k[t]/(t^3),\qquad A=k[t]/(t^2),
\qquad B=A'\times_AA'.
$$

The map $A'\twoheadrightarrow A$ is small, with kernel $(t^2)$. Choose

$$
X=\begin{pmatrix}0&0\\0&1\end{pmatrix},
\qquad
Z=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$

Send a topological generator of $G$ to

$$
M=1+tX\in\operatorname{GL}_2(A').
$$

This defines a continuous representation because its finite image determines a continuous quotient of $\widehat{\mathbf Z}$. Over $A$, every $C=1+tZ$ centralizes $1+tX$: the commutator begins in degree $t^2$, which vanishes there. But a lift $1+tZ+t^2W$ centralizes $M$ over $A'$ only if

$$
[Z,X]=0.
$$

Here $[Z,X]=Z\neq0$, so $C$ does not lift to an automorphism of the chosen branch representation.

Choose the lift $Q=1+tZ$ of $C$ to $A'$. One gluing uses the pair $(M,M)$; another uses $(M,QMQ^{-1})$. Both pairs agree after passage to $A$, because $C$ centralizes the reduction, and hence define representations over $B$. On each branch their unframed classes agree. If the two $B$-representations were strictly equivalent, the two branch conjugators would express $C$ as a product of reductions of automorphisms of the branch representations. The leading $t$-term of every such automorphism commutes with $X$, whereas $Z$ does not. This is impossible.

Thus

$$
D_{\bar\rho}(B)\longrightarrow
D_{\bar\rho}(A')\times_{D_{\bar\rho}(A)}D_{\bar\rho}(A')
$$

is not injective. The coarse unframed functor fails (H4). The example also explains why the fiber product over $k$ alone is too shallow to reveal the problem.

### 9.3 What remains meaningful with large stabilizers

Failure of coarse pro-representability does not erase the deformation theory. Three alternatives remain.

First, the framed functor retains actual matrices and is often pro-representable. Second, the unframed functor may still satisfy (H1)--(H3) and possess a hull, which is adequate for many dimension arguments but does not classify points uniquely. Third, the deformation groupoid retains automorphisms and glues by a fiber product that includes a chosen comparison arrow. Its natural universal object is groupoid-valued rather than an ordinary set-valued formal spectrum.

One must not describe a framed ring modulo a change-of-basis group as automatically representing the coarse orbit functor. Stabilizers make categorical quotients, invariant rings, and orbit sets different constructions.

## 10. Framed deformation functors

### 10.1 Exact gluing of matrices

Fix a profinite group $G$, a finite field $k$, a complete Noetherian local coefficient base $\mathcal O$, and a continuous residual representation

$$
\bar\rho:G\to\operatorname{GL}_d(k).
$$

The framed functor $D_{\bar\rho}^{\square}(A)$ is the set of actual continuous lifts reducing exactly to $\bar\rho$, with no conjugacy quotient. For a fiber product $B=A'\times_AA''$, matrices over $B$ are compatible pairs of matrices. Therefore

$$
D_{\bar\rho}^{\square}(B)\xrightarrow{\sim}
D_{\bar\rho}^{\square}(A')
\times_{D_{\bar\rho}^{\square}(A)}
D_{\bar\rho}^{\square}(A'')
$$

whenever $B$ is an object of the coefficient category. Framed deformations satisfy the strongest gluing condition, not merely (H1) and (H4).

The tangent space is

$$
t_{D^{\square}_{\bar\rho}}
=Z^1(G,\operatorname{ad}\bar\rho).
$$

Thus the only remaining hypothesis for Schlessinger pro-representability is its finite-dimensionality.

### 10.2 Finiteness hypotheses on the profinite group

A useful sufficient condition, with $p=\operatorname{char}k$, is:

$$
(\Phi_p)\qquad
\dim_{\mathbf F_p}\operatorname{Hom}_{\mathrm{cts}}(H,\mathbf F_p)<\infty
\quad\text{for every open subgroup }H\leq G.
$$

For every finite discrete $k[G]$-module $M$, condition $(\Phi_p)$ implies $H^1(G,M)$ is finite-dimensional. To see this, choose an open normal subgroup $H$ acting trivially on $M$. Then $H^1(H,M)=\operatorname{Hom}_{\mathrm{cts}}(H,M)$ is finite-dimensional by $(\Phi_p)$, and inflation--restriction compares $H^1(G,M)$ with invariants in this space and cohomology of the finite quotient $G/H$.

Since

$$
0\to B^1(G,\operatorname{ad}\bar\rho)
\to Z^1(G,\operatorname{ad}\bar\rho)
\to H^1(G,\operatorname{ad}\bar\rho)\to0
$$

and $B^1$ is a quotient of the finite-dimensional space $\operatorname{ad}\bar\rho$, the framed tangent space is finite. Topological finite generation of $G$ is a simpler sufficient condition: a continuous cocycle is determined by its values on finitely many topological generators.

It also implies $(\Phi_p)$. Indeed, if $H\leq G$ is open and $\Gamma$ is the dense abstract subgroup generated by $g_1,\ldots,g_s$, then $\Gamma\cap H$ is dense in $H$ and has finite index in $\Gamma$. Choose a finite set $T$ of right-coset representatives and, for each $t\in T$ and $g_i^{\pm1}$, let $\overline{tg_i^{\pm1}}\in T$ represent its coset. Rewriting a word one letter at a time expresses every element of $\Gamma\cap H$ as a product of the finitely many elements

$$
t g_i^{\pm1}\overline{t g_i^{\pm1}}^{-1}.
$$

Thus $H$ is topologically finitely generated, and a continuous homomorphism $H\to\mathbf F_p$ is determined by finitely many values.

### 10.3 Framed pro-representability theorem

**Theorem.** If $G$ satisfies $(\Phi_p)$—in particular, if $G$ is topologically finitely generated—then $D_{\bar\rho}^{\square}$ is pro-representable by a complete Noetherian local $\mathcal O$-algebra $R_{\bar\rho}^{\square}$.

**Proof.** The one-point condition holds because the residual matrix representation is fixed. Exact matrix gluing proves (H1), (H2), and (H4). Section 10.2 proves (H3). Schlessinger's theorem gives the representing ring. $\square$

No vanishing of $H^2$ is required. A nonzero obstruction group contributes relations to $R_{\bar\rho}^{\square}$; it does not prevent existence of the ring.

### 10.4 A direct generators-and-relations construction

When $G$ is topologically generated by $g_1,\ldots,g_s$, one can see the ring more concretely. Choose lifts of the residual matrices $\bar\rho(g_i)$ to $\operatorname{GL}_d(\mathcal O)$ and attach $sd^2$ formal variables to their entries. This produces universal matrices over a power-series ring $P$.

For completeness, the free profinite group used here can be constructed as the inverse limit of the finite quotients of the abstract free group on $s$ letters. A homomorphism from the abstract free group to a finite group factors through one of these quotients, so passage to the inverse limit gives, uniquely, a continuous homomorphism from $F_s$ for every ordered $s$-tuple in a finite group. Applying this universal property to all finite quotients of $G$ gives the continuous presentation $F_s\twoheadrightarrow G$.

Any tuple of matrices over an Artinian ring determines a continuous homomorphism $F_s\to\operatorname{GL}_d(A)$. The compatible tuples over $P/\mathfrak m_P^n$ likewise give a continuous map to $\operatorname{GL}_d(P)=\varprojlim_n\operatorname{GL}_d(P/\mathfrak m_P^n)$. It descends to $G$ exactly when every element of the closed relation subgroup maps to the identity. Let $J$ be the ideal generated by all matrix entries of these relation defects. Although the relation subgroup may be infinitely generated, $P$ is Noetherian, so $J$ is finitely generated and closed. Then

$$
R_{\bar\rho}^{\square}=P/J
$$

represents framed lifts. This construction makes continuity explicit: the target over every Artinian test ring is finite, and the free profinite universal property concerns continuous homomorphisms.

The number $sd^2$ is generally not minimal. The intrinsic minimal number of relative generators is

$$
\dim_k Z^1(G,\operatorname{ad}\bar\rho).
$$

Passing from a presentation by group generators to a minimal ring presentation removes linear redundancies imposed by the group relations.

### 10.5 The universal framed representation

The representing isomorphism supplies compatible representations over

$$
R_{\bar\rho}^{\square}/\mathfrak m^n.
$$

Their inverse limit is a continuous homomorphism

$$
\rho^{\square,\mathrm{univ}}:
G\longrightarrow\operatorname{GL}_d(R_{\bar\rho}^{\square}).
$$

For every $A\in\mathcal C$, composition with a unique continuous local map $R_{\bar\rho}^{\square}\to A$ gives every framed lift exactly once. The adjective “framed” is part of this universal assertion: forgetting the basis introduces an orbit relation that the same ring does not ordinarily represent.

## 11. Unframed representations under the scalar-centralizer hypothesis

### 11.1 The Schur condition

Assume

$$
\operatorname{End}_{k[G]}(k^d)=k.
$$

This says that the centralizer of $\bar\rho(G)$ in $M_d(k)$ consists only of scalar matrices. Absolute irreducibility implies it, but the scalar-centralizer condition is the exact hypothesis needed in the gluing argument and can hold in slightly greater generality.

Under $(\Phi_p)$ the unframed tangent space

$$
t_{D_{\bar\rho}}=H^1(G,\operatorname{ad}\bar\rho)
$$

is finite-dimensional. Surjectivity in (H1) follows by lifting the chosen comparison conjugator along the surjective branch. Condition (H2) follows from the independent decomposition of first-order cocycles. Only (H4) needs the Schur hypothesis.

### 11.2 Centralizers over Artinian lifts

**Lemma.** Let $A\in\mathcal C$ and let $\rho_A$ lift $\bar\rho$. If the residual centralizer is $k$, then

$$
Z_{M_d(A)}(\rho_A(G))=A\cdot I_d.
$$

Consequently every strict automorphism of $\rho_A$ is a scalar unit congruent to $1$ modulo $\mathfrak m_A$.

**Proof strategy.** Reduce a centralizing matrix modulo successive powers of the maximal ideal. At each layer the commutator equation becomes the residual centralizer equation.

**Proof.** Let $C$ centralize $\rho_A(G)$. Modulo $\mathfrak m_A$, its image centralizes $\bar\rho(G)$, hence equals $a_0I_d$. Subtract a scalar lift of $a_0$. If the remainder lies in $M_d(\mathfrak m_A^n)$, its class in

$$
M_d(\mathfrak m_A^n/\mathfrak m_A^{n+1})
\simeq M_d(k)\otimes_k
(\mathfrak m_A^n/\mathfrak m_A^{n+1})
$$

centralizes $\bar\rho$. It is therefore scalar in the matrix factor. Subtract a scalar element of $\mathfrak m_A^n$ and push the remainder into $\mathfrak m_A^{n+1}$. Nilpotence terminates the process, expressing $C$ as a scalar matrix. The assertion about strict automorphisms follows. $\square$

This lemma is stronger than a dimension count. It controls actual automorphisms at every Artinian order.

### 11.3 The automorphism descent step

**Proposition.** Under the scalar-centralizer hypothesis, the unframed deformation functor satisfies (H4).

**Proof strategy.** Glue after choosing an isomorphism over the common quotient. Two choices differ by a strict automorphism there. The lemma makes that automorphism scalar; a scalar lifts to either branch and acts trivially, so the choice does not alter the glued class.

**Proof.** Let $A'\twoheadrightarrow A$ be small and $B=A'\times_AA'$. Surjectivity of

$$
D_{\bar\rho}(B)\to
D_{\bar\rho}(A')\times_{D_{\bar\rho}(A)}D_{\bar\rho}(A')
$$

holds as follows. Choose representatives $\rho_1,\rho_2$ of the two branch classes. Their reductions are strictly conjugate over $A$. Lift a comparison conjugator through the surjection $\Gamma_{A'}\twoheadrightarrow\Gamma_A$, conjugate one branch, and then glue the now equal reductions entrywise.

For injectivity, suppose two $B$-lifts have equivalent restrictions on both branches. Choose branch conjugators $P_1,P_2\in\Gamma_{A'}$. Their reductions need not initially agree. The mismatch

$$
C=\overline{P}_2^{-1}\overline{P}_1\in\Gamma_A
$$

centralizes the common representation over $A$. By the lemma, $C=cI_d$ for some $c\in1+\mathfrak m_A$. Lift $c$ to $c'\in1+\mathfrak m_{A'}$. Replacing one branch conjugator by $(c'I_d)$ times it changes neither conjugated representation nor its strictness, and makes the two reductions agree. The adjusted pair $(P_1,P_2)$ is therefore a matrix over $B$ and gives a strict equivalence of the two glued lifts. This proves injectivity. $\square$

The proof uses both properties of scalars: they lift along coefficient surjections and conjugation by them is trivial. Merely knowing that the centralizer has small dimension would not suffice.

### 11.4 Unframed pro-representability

**Theorem.** Suppose $G$ satisfies $(\Phi_p)$ and

$$
\operatorname{End}_{k[G]}(k^d)=k.
$$

Then the unframed deformation functor $D_{\bar\rho}$ is pro-representable by a complete Noetherian local $\mathcal O$-algebra $R_{\bar\rho}^{\mathrm{univ}}$.

**Proof.** The functor has one residual point. Conditions (H1) and (H2) follow from gluing representatives and first-order cohomology, (H3) from $(\Phi_p)$, and (H4) from Section 11.3. Apply Schlessinger's theorem. $\square$

Absolute irreducibility is a familiar sufficient hypothesis through Schur's lemma. The theorem should not be inverted: a representation with a larger centralizer might have a representable deformation functor for special reasons, but there is no general set-valued universality theorem without further analysis.

### 11.5 Framed versus unframed rings

Under the scalar-centralizer hypothesis both functors are represented, and forgetting the frame gives

$$
D_{\bar\rho}^{\square}\longrightarrow D_{\bar\rho}.
$$

Its relative tangent space is

$$
B^1(G,\operatorname{ad}\bar\rho),
$$

of dimension $d^2-1$. The transformation is formally smooth: a change of basis modulo a surjection can be lifted entrywise. After choosing formal coordinates one obtains a noncanonical isomorphism

$$
R_{\bar\rho}^{\square}
\simeq R_{\bar\rho}^{\mathrm{univ}}[[Y_1,\ldots,Y_{d^2-1}]].
$$

The direction is worth checking. A transformation $h_{R^\square}\to h_R$ corresponds to a ring map $R\to R^\square$, and adding frame parameters enlarges the representing ring by power-series variables. If the residual centralizer has dimension $c$, the framed tangent exceeds the unframed tangent by $d^2-c$, but without scalar control the existence of an unframed universal ring and hence such a formula cannot be presumed.

## 12. Fixed determinants

### 12.1 The determinant datum

Fix a continuous character

$$
\delta:G\longrightarrow\mathcal O^\times
$$

whose reduction is $\det\bar\rho$. For $A\in\mathcal C$, write $\delta_A$ for its composite with $\mathcal O\to A$. The fixed-determinant framed and unframed functors retain precisely those lifts $\rho_A$ satisfying

$$
\det\rho_A=\delta_A.
$$

A residual determinant by itself is insufficient in mixed characteristic: the functor requires a compatible lift at every coefficient level. Different choices of $\delta$ define different deformation problems.

### 12.2 Fixed determinant as a closed condition

Suppose the ambient framed functor is represented by $R^\square$ with universal representation $\rho^{\square}$. Let $I_\delta$ be the closed ideal generated by all elements

$$
\det\rho^{\square}(g)-\delta(g),\qquad g\in G.
$$

Then a map $R^\square\to A$ factors through $R^\square/I_\delta$ exactly when the induced representation has determinant $\delta_A$. Hence

$$
R^{\square,\delta}=R^\square/I_\delta
$$

represents the framed fixed-determinant functor. The generating family indexed by $G$ causes no Noetherian problem: its ideal is finitely generated because $R^\square$ is Noetherian, and therefore closed.

If the unframed ambient functor is universal, choose compatible representatives of its universal strict-equivalence classes over the Artinian quotients and pass to the inverse limit. This gives a representative over $R^{\mathrm{univ}}$; a different choice is strictly conjugate, so its determinant is unchanged. The same construction therefore gives a canonical determinant character and a quotient

$$
R^{\delta}=R^{\mathrm{univ}}/I_\delta.
$$

This conclusion uses an actual ambient universal family. A fixed-determinant subfunctor of a functor possessing only a hull is not automatically represented by a quotient of the hull.

### 12.3 A fiber-product description

Let $D_{\det\bar\rho}^{\mathrm{char}}$ be the deformation functor of the residual determinant character, and let the fixed character $\delta$ define a natural point $h_{\mathcal O}\to D_{\det\bar\rho}^{\mathrm{char}}$. Then

$$
D_{\bar\rho}^{\square,\delta}
=D_{\bar\rho}^{\square}
\times_{D_{\det\bar\rho}^{\mathrm{char}}}h_{\mathcal O}.
$$

When all functors are represented, this fiber product of functors corresponds contravariantly to a completed tensor product of rings. The quotient description above is the concrete form of the same construction after the point $\delta$ is imposed.

### 12.4 Tangent and characteristic caveats

The derivative of determinant is trace:

$$
\det(1+\epsilon X)=1+\epsilon\operatorname{tr}X.
$$

Thus the framed fixed-determinant tangent space is

$$
Z^1(G,\operatorname{ad}^0\bar\rho).
$$

For ordinary unframed deformations it is safest to write

$$
\frac{Z^1(G,\operatorname{ad}^0\bar\rho)}
{d(\operatorname{ad}\bar\rho)}
=\ker\left(H^1(G,\operatorname{ad}\bar\rho)
\xrightarrow{\operatorname{tr}}H^1(G,k)\right).
$$

If $\operatorname{char}k\nmid d$, trace splits the scalar summand and this is $H^1(G,\operatorname{ad}^0\bar\rho)$. If $\operatorname{char}k\mid d$, scalar matrices have trace zero; the familiar direct-sum argument fails, and one must retain the quotient formula. This caveat changes tangent and obstruction calculations, not the elementary fact that equality of determinants is cut out by a closed ideal.

### 12.5 Representability theorem with fixed determinant

**Theorem.** Under $(\Phi_p)$, the framed fixed-determinant functor is pro-representable. If in addition $\operatorname{End}_{k[G]}(k^d)=k$, the unframed fixed-determinant functor is pro-representable.

**Proof.** One may either use the quotient construction from the corresponding ambient universal ring or verify the criterion directly. Determinants glue over coefficient fiber products, so the exact framed gluing survives. In the unframed case, the scalar-centralizer proof is unchanged because scalar conjugation preserves determinant. Tangent finiteness follows from that of the ambient cocycle or cohomology space. $\square$

The existence of determinant-preserving lifts across a particular small extension may be obstructed in a trace-zero cohomology group. That affects smoothness and relations, not representability under the theorem's hypotheses.

## 13. Operations on represented deformation problems

### 13.1 Natural transformations reverse ring maps

Suppose $F\simeq h_R$ and $G\simeq h_S$. A natural transformation

$$
F\longrightarrow G
$$

corresponds to a continuous local map

$$
S\longrightarrow R.
$$

Indeed, a point $R\to A$ is sent to the composite $S\to R\to A$. This reversal is the basic variance rule for every construction in this chapter. For example, forgetting structure gives a transformation from a more constrained moduli functor to a less constrained one, hence a map from the less constrained universal ring to the more constrained ring.

One should distinguish three arrows that can coexist:

$$
\begin{array}{c|c}
\text{mathematical operation}&\text{direction}\\ \hline
\text{coefficient change}&A\to B\text{ gives }F(A)\to F(B)\\
\text{map of formal moduli problems}&F\to G\\
\text{map of representing rings}&R_G\to R_F.
\end{array}
$$

Confusing the first and third directions leads to incorrect tensor products and quotient maps.

### 13.2 Closed subfunctors and quotient rings

Let $R\in\widehat{\mathcal C}$ and $I\subseteq R$ be an ideal. Since $R$ is Noetherian, $I$ is closed, and $R/I$ remains complete Noetherian local. The quotient map induces an injection

$$
h_{R/I}(A)\hookrightarrow h_R(A),
$$

whose image consists exactly of maps $R\to A$ killing $I$. Thus equations on a universal object define a subfunctor represented by a quotient ring.

Conversely, merely specifying subsets $E(A)\subseteq F(A)$ stable under base change does not prove that $E$ is cut out by a quotient. The condition must be compatible with all Artinian tests in such a way that membership is equivalent to annihilating one closed ideal of the universal ring. Fixed determinant has this property because it is literal equality of two universal characters. More subtle local conditions require separate proofs.

There is a simple counterexample. Over $\mathcal O=k$, let $F(A)=\mathfrak m_A$, represented by $k[[X]]$, and define the natural subfunctor

$$
E(A)=\mathfrak m_A^2\subseteq\mathfrak m_A.
$$

Coefficient maps preserve squares of maximal ideals, so this is genuinely a subfunctor. Its tangent space is zero because $\mathfrak m_{k[\epsilon]}^2=0$, yet

$$
t^2\in E(k[t]/(t^3))
$$

is nonzero. If $E$ were represented inside $F$ by a quotient of $k[[X]]$, its zero tangent space would force that quotient to have zero maximal ideal by Nakayama, hence to be $k$; it would then have no nonzero value over $k[t]/(t^3)$. Thus base-change stability alone gives merely a subfunctor, not a closed formal subspace.

**Worked example.** Let $F(A)=\mathfrak m_A\times\mathfrak m_A$, represented as ordered pairs by $R=\mathcal O[[X,Y]]$. The condition that the two parameters agree is represented by

$$
R/(X-Y)\simeq\mathcal O[[X]].
$$

The condition that their product vanish is represented by

$$
R/(XY).
$$

The latter formal space has two branches and is singular. It is nevertheless perfectly representable: singularity is a lifting obstruction, not a failure of universality.

### 13.3 Products and fiber products of functors

Let transformations $F_1\to F_0\leftarrow F_2$ be represented by maps

$$
R_0\longrightarrow R_1,
\qquad
R_0\longrightarrow R_2.
$$

Assume the maps are continuous local maps between complete Noetherian local rings with the same specified residue field. Each $R_i$ is then topologically of finite type over $R_0$: finitely many lifts of a basis of its relative cotangent space give a surjection $R_0[[\mathbf X]]\twoheadrightarrow R_i$. Thus the residue-compatible completed tensor product is again complete Noetherian local, and the functorial fiber product is represented by

$$
F_1\times_{F_0}F_2
\simeq h_{R_1\widehat\otimes_{R_0}R_2}.
$$

To verify the formula, map the completed tensor product to an Artinian $A$. Its universal property gives a pair of maps $R_1\to A$ and $R_2\to A$ agreeing on $R_0$, exactly a point of the functorial fiber product.

Taking $F_0$ to be the terminal functor $h_{\mathcal O}$ gives

$$
R_{F_1\times F_2}
=R_1\widehat\otimes_{\mathcal O}R_2.
$$

This represents two independent pieces of deformation data. It does not say that a direct sum of representations has no off-diagonal deformations; the latter functor is generally larger than the product of the two summand functors.

### 13.4 Intersections and base change of closed conditions

If $E_i\subseteq h_R$ is represented by $R/I_i$, then the intersection condition is represented by

$$
R/(I_1+I_2).
$$

Imposing two systems of equations therefore adds their ideals. By contrast, the scheme-theoretic union would involve $I_1\cap I_2$ and need not describe a deformation condition stable under the intended interpretation.

If $R\to S$ represents a base change of ambient problems, the pullback of the condition $I$ is represented by

$$
S/\overline{IS}.
$$

Closure is displayed to record the topology; in a Noetherian adic ring the finitely generated extended ideal is closed. These formulas will later let local conditions be imposed simultaneously and transported into global problems without rebuilding their equations.

### 13.5 Formally smooth power-series extensions

For any $R\in\widehat{\mathcal C}$, the map

$$
R\longrightarrow R[[Y_1,\ldots,Y_s]]
$$

induces a formally smooth transformation

$$
h_{R[[\mathbf Y]]}\longrightarrow h_R.
$$

Given a compatible map to the lower ring of a surjection $A'\twoheadrightarrow A$, lift each of the $s$ images in $\mathfrak m_A$ arbitrarily to $\mathfrak m_{A'}$. The relative tangent space is $k^s$.

There is also a converse useful in comparing framed and unframed rings.

**Power-series criterion.** Let $R\to S$ be a continuous local map in $\widehat{\mathcal C}$, topologically of finite type, inducing the identity on residue fields. If $S$ is formally smooth over $R$ and

$$
\dim_k\frac{\mathfrak m_S}
{\mathfrak m_S^2+\mathfrak m_RS}=s,
$$

then, after choosing lifts of a basis, there is a noncanonical $R$-algebra isomorphism

$$
S\simeq R[[Y_1,\ldots,Y_s]].
$$

**Proof strategy.** The chosen lifts give a surjection from the power-series ring. Formal smoothness constructs compatible inverse maps modulo every power. Keeping those maps inverse, rather than merely producing a section, is what rules out a hidden higher-order kernel.

**Proof.** Topological Nakayama gives a surjection $\pi:P=R[[\mathbf Y]]\twoheadrightarrow S$. Its reduction modulo the square of the maximal ideal is an isomorphism relative to $R$ by the dimension hypothesis and the chosen basis. Formal smoothness of $S$ over $R$ now lifts an inverse to $\pi$ successively across the small-extension factorizations of

$$
P/\mathfrak m_P^{n+1}\twoheadrightarrow P/\mathfrak m_P^n.
$$

At each step, the difference between the lifted composite and the identity is a relative derivation into the new socle layers. Changing the lifts of the $Y_i$ by that derivation corrects the composite without disturbing lower orders. Induction therefore gives compatible isomorphisms between the corresponding Artinian quotients of $P$ and $S$. Passing to inverse limits and using completeness and separatedness makes $\pi$ an isomorphism. $\square$

The isomorphism depends on parameter choices. Formal smoothness determines the power-series *type*, not canonical coordinates.

### 13.6 A singular fiber-product calculation

Let

$$
R_0=k[[T]],\quad
R_1=k[[X]],\quad R_2=k[[Y]],
$$

where $T$ maps to $X^2$ and $Y^3$. Then

$$
R_1\widehat\otimes_{R_0}R_2
\simeq k[[X,Y]]/(X^2-Y^3).
$$

The represented functor consists of pairs $(x,y)\in\mathfrak m_A\times\mathfrak m_A$ satisfying $x^2=y^3$. Its tangent space is two-dimensional because the relation has no linear term, but not every tangent vector extends freely to higher order. This example separates three ideas cleanly: the fiber product is representable, its tangent space counts two generators, and its nonlinear relation creates obstructions without threatening representability.

## 14. Relative representability of deformation conditions

### 14.1 Why an ambient-relative notion is needed

Later deformation problems will begin with an ambient representation functor and impose extra requirements. A condition must behave well not only as an isolated functor but in every family already mapping to the ambient problem. This motivates relative representability.

Let $E\hookrightarrow F$ be a natural inclusion of set-valued functors. We call it **relatively pro-representable** if for every $R\in\widehat{\mathcal C}$ and every transformation $h_R\to F$, the pullback

$$
h_R\times_FE
$$

is pro-representable. We call it **closedly relatively representable** if the pullback is always represented by a quotient $R/I$ for a closed ideal $I\subseteq R$.

The second is the form ordinarily desired for local deformation conditions: it says the condition cuts out a closed formal subspace inside every ambient family. It is stronger than saying that $E$ itself happens to possess a representing ring.

### 14.2 The universal-family test

If $F=h_R$ is already represented, a subfunctor $E\subseteq F$ is closedly represented precisely when there is a closed ideal $I\subseteq R$ such that

$$
E(A)=\{u:R\to A\mid u(I)=0\}
$$

for every $A\in\mathcal C$. Once this is proved for the universal family, arbitrary base change follows: for $R\to S$, the pulled-back condition is represented by $S/\overline{IS}$.

This criterion explains both the power and the limitation of a universal representation. To define $I$, one may impose equations on its matrices or on auxiliary finite modules. But it must then be proved that a test-ring deformation satisfies the intended intrinsic condition exactly when its classifying map kills $I$. Merely writing plausible equations is not enough if the condition involves existence of an unrecorded subobject or a choice that may fail to descend.

### 14.3 Fiber-product criteria for a subfunctor

Suppose $E\subseteq F$ and $F$ is a deformation functor. The pullback of $E$ along any $h_R\to F$ will satisfy Schlessinger's gluing conditions if membership in $E$ has the following properties:

1. **base change:** an $E$-object remains an $E$-object after every coefficient map;
2. **effective gluing:** an $F$-object over $A'\times_AA''$ lies in $E$ exactly when both branch objects lie in $E$;
3. **small-extension compatibility:** obstruction and ambiguity data for lifting inside $E$ are functorial under pushout;
4. **first-order linearity:** membership over split square-zero algebras is compatible with sums and scalar pushouts, so the tangent subset is a $k$-linear subspace after pullback.

These properties are a checklist, not by themselves a representability theorem. For each pullback $h_R\times_FE$, one must still verify the precise analogues of (H1) and (H2), finite-dimensionality of its tangent space, and (H4) if a universal object rather than a hull is claimed. Effective gluing often supplies the first, third, and fourth conditions at once, while the tangent space is automatically a subspace of the finite-dimensional $t_{h_R}$. To conclude that the representing map is a quotient, one additionally uses the fact that the pullback is a subfunctor of $h_R$ and proves closedness—usually by an explicit universal ideal or a finite-level stabilization argument.

The warning is important: a subfunctor is only a rule of membership. It gives a quotient ring only after closed relative representability has been established.

### 14.4 Tangent spaces of closed conditions

If $F=h_R$ and $E=h_{R/I}$, then

$$
t_E=\operatorname{Hom}_k\left(
\frac{\mathfrak m_R}
{\mathfrak m_R^2+\mathfrak m_{\mathcal O}R+I},k
\right)
\subseteq t_F.
$$

Only the image of $I$ in the cotangent space affects first-order deformations. An ideal contained in $\mathfrak m_R^2+\mathfrak m_{\mathcal O}R$ imposes no tangent restriction, although it may impose serious higher-order constraints.

**Example.** In $R=k[[X,Y]]$, the quotient by $(X)$ has one-dimensional tangent space, while the quotient by $(XY)$ retains the full two-dimensional tangent space. The second condition is invisible to first order. Therefore identifying a desired tangent subspace cannot by itself construct the corresponding deformation condition.

### 14.5 Intersections of local conditions

Suppose $E_1,E_2\subseteq F=h_R$ are closedly represented by $R/I_1$ and $R/I_2$. Their intersection is represented by $R/(I_1+I_2)$, and its tangent space is the intersection

$$
t_{E_1\cap E_2}=t_{E_1}\cap t_{E_2}
$$

inside $t_F$. The equality follows by dualizing the sum of the images of $I_1$ and $I_2$ in the cotangent space.

This elementary formula is the abstract operation later used to combine independent requirements. Nothing here asserts that any particular arithmetic condition is closedly representable; those proofs require the condition-specific geometry reserved for subsequent books.

### 14.6 Extra structures and forgotten choices

Some conditions are easiest to represent after including extra data: a stable line, a filtration, a basis, or a finite flat model. The enhanced functor may be representable while its image in the ambient set-valued functor is not a closed subfunctor, because one ambient object may admit several choices with automorphisms or because existence of a choice is not preserved as a closed condition.

The safe procedure is:

1. define the enhanced objects and their isomorphisms;
2. prove representability of the enhanced functor;
3. analyze whether forgetting the enhancement is injective, finite, formally smooth, or neither;
4. only then identify its image with a quotient condition if descent and uniqueness justify it.

This is the relative analogue of the framed/unframed distinction. Forgetting data is not the same operation as imposing equations.

## 15. A reusable universal-ring theorem

### 15.1 The abstract package

The preceding theory can be condensed into a theorem for repeated use.

**Universal deformation ring package.** Let $F:\mathcal C\to\mathbf{Sets}$ be covariant and suppose:

1. $F(k)$ consists of one point;
2. for every diagram $A'\to A\leftarrow A''$ with $A''\to A$ small, compatible objects glue, so (H1) holds;
3. split first-order extensions glue uniquely as in (H2);
4. $t_F$ is finite-dimensional over $k$;
5. for every small $A'\twoheadrightarrow A$, self-gluing is unique as in (H4).

Then there is a complete Noetherian local $\mathcal O$-algebra $R_F$ and a natural isomorphism

$$
F\simeq h_{R_F}.
$$

The ring is unique up to unique isomorphism compatible with the representing isomorphism. It has a minimal presentation

$$
R_F\simeq\mathcal O[[X_1,\ldots,X_r]]/J,
\qquad r=\dim_k t_F,
$$

with $J$ having no nonzero relative linear initial form. If only conditions 1--4 hold, the same construction produces a hull; its ring is unique only up to noncanonical isomorphism and its maps to test rings need not classify deformations uniquely.

### 15.2 The representation-theoretic package

Let $G$ be profinite, let $k$ be finite of characteristic $p$, let $\mathcal O$ be a complete Noetherian local coefficient ring with residue field $k$, and let

$$
\bar\rho:G\to\operatorname{GL}_d(k)
$$

be continuous.

**Theorem.** Assume $(\Phi_p)$. Then:

1. the framed deformation functor is represented by $R_{\bar\rho}^{\square}$;
2. if $\operatorname{End}_{k[G]}(k^d)=k$, the unframed deformation functor is represented by $R_{\bar\rho}^{\mathrm{univ}}$;
3. after fixing a continuous determinant lift $\delta:G\to\mathcal O^\times$, the corresponding framed fixed-determinant functor is represented by a quotient $R_{\bar\rho}^{\square,\delta}$;
4. under the scalar-centralizer hypothesis, the unframed fixed-determinant functor is represented by a quotient $R_{\bar\rho}^{\delta}$;
5. the relative numbers of tangent generators are respectively

   $$
   \dim_kZ^1(G,\operatorname{ad}\bar\rho),
   \qquad
   \dim_kH^1(G,\operatorname{ad}\bar\rho),
   $$

   with the fixed-determinant versions obtained from the exact trace-kernel formulas of Section 12.4.

**Proof architecture.** Exact equality of matrices over ring fiber products proves the framed gluing axioms. The finiteness condition proves finite tangent dimension. Scalar centralizers make comparison automorphisms lift harmlessly and hence prove unframed uniqueness. Determinant equality is a closed equation on the universal representation. Each step has a separate hypothesis; none is supplied merely by the vanishing of an obstruction group.

### 15.3 An unobstructed refinement

If, in addition,

$$
H^2(G,\operatorname{ad}\bar\rho)=0,
$$

then the framed universal ring is formally smooth over $\mathcal O$. Consequently

$$
R_{\bar\rho}^{\square}\simeq
\mathcal O[[X_1,\ldots,X_z]],
\qquad
z=\dim_kZ^1(G,\operatorname{ad}\bar\rho),
$$

noncanonically. Under the scalar-centralizer hypothesis, the same vanishing makes the unframed functor formally smooth and gives

$$
R_{\bar\rho}^{\mathrm{univ}}\simeq
\mathcal O[[X_1,\ldots,X_h]],
\qquad
h=\dim_kH^1(G,\operatorname{ad}\bar\rho).
$$

For fixed determinant, replace the obstruction module by the correct determinant-preserving one and retain the characteristic caveat from Book 63: when $p\mid d$, the ordinary unframed tangent and ambiguity are not obtained by naively replacing every adjoint module by its trace-zero submodule.

Vanishing of $H^2$ is sufficient for these smoothness conclusions because Book 63's obstruction theory is complete for the indicated lifting problem. It remains unnecessary for the existence of universal rings.

### 15.4 A topological finite-generation version

For many applications one can replace $(\Phi_p)$ by the more concrete assumption that $G$ is topologically finitely generated. Then framed representability follows either from Schlessinger or from the direct profinite presentation of Section 10.4. The abstract $(\Phi_p)$ formulation is useful because it isolates what the criterion actually needs: finite-dimensional continuous $H^1$ for finite modules.

No hypothesis of finite presentation of $G$ is required for existence of the framed ring. Infinitely many group relations generate an ideal in a finite-variable Noetherian power-series ring, hence a finitely generated closed ideal. This algebraic Noetherianity should not be confused with finite presentation of the profinite group.

### 15.5 What the package does not claim

The theorem package does not assert any of the following:

- that every set-valued deformation functor is representable;
- that a finite tangent space or a vanishing $H^2$ controls automorphisms;
- that a hull classifies points uniquely;
- that a coarse quotient of a framed space is represented by an invariant ring;
- that a subfunctor is cut out by a quotient before relative closedness is proved;
- that fixing determinant has the same tangent effect in every characteristic;
- that local conditions not yet defined are automatically representable.

These exclusions are part of the theorem's accuracy, not limitations to be silently ignored.

## 16. Worked formal geometries

### 16.1 One free parameter

Consider $F(A)=\mathfrak m_A$. The ring $\mathcal O[[X]]$ represents $F$, and every surjection $A'\twoheadrightarrow A$ permits an arbitrary lift of the image of $X$. Thus $F$ is formally smooth and has one-dimensional tangent space. Its universal element is the compatible system of classes of $X$.

If we impose $X^n=0$, the subfunctor is represented by $\mathcal O[[X]]/(X^n)$. Its tangent space remains one-dimensional for $n\geq2$, but higher lifts are obstructed. For example, over $k[t]/(t^{n+1})$ the element $t$ does not satisfy $t^n=0$. This family is the simplest demonstration that equal tangent spaces can conceal different higher-order geometries.

### 16.2 A node and nonunique branches

The ring

$$
R=k[[X,Y]]/(XY)
$$

represents pairs $(x,y)\in\mathfrak m_A\times\mathfrak m_A$ with $xy=0$. Its tangent space has basis dual to $X,Y$. Over the dual numbers every pair $(a\epsilon,b\epsilon)$ is allowed because products of tangent terms vanish. Over $k[t]/(t^3)$, the choice $(t,t)$ is forbidden because $t^2\neq0$.

The two quotient maps $R\to k[[X]]$ and $R\to k[[Y]]$ describe the two smooth branches. The represented functor still satisfies every fiber-product axiom exactly. Geometric reducibility and singularity therefore have no bearing on the uniqueness built into representability.

### 16.3 A character of a procyclic group

Let $G=\mathbf Z_p$, let $k$ have characteristic $p$, and consider deformations of the trivial character with coefficient base $\mathcal O$. A character is determined by the image of a topological generator in $1+\mathfrak m_A$. Hence the functor is represented by $\mathcal O[[T]]$, with universal generator sent to $1+T$. Continuity holds because the filtration of $1+\mathfrak m_A$ by the subgroups $1+\mathfrak m_A^n$ has successive quotients that are finite additive $k$-groups; consequently $1+\mathfrak m_A$ is a finite $p$-group.

The tangent space is $H^1(\mathbf Z_p,k)\simeq k$, and $H^2$ vanishes, agreeing with the one-variable smooth ring. If this character is prescribed as the determinant of a one-dimensional representation, the fixed-determinant quotient sets $T$ equal to the chosen parameter and leaves no deformation direction.

### 16.4 Commuting matrices and quadratic relations

Let $G=\mathbf Z_p^2$ and let the residual representation be trivial of dimension $d$. A framed lift is determined by two sufficiently near-identity matrices that commute. Write their first-order parts as $X$ and $Y$. The commutator relation has leading term

$$
[X,Y].
$$

Accordingly the framed tangent space contains all pairs $(X,Y)$, while the universal ring has quadratic relations expressing commutation. The tangent dimension alone sees $2d^2$ parameters and no equations; the obstruction theory detects the first nonzero initial forms of the relation ideal.

This example mirrors $k[[X,Y]]/(XY)$ in a noncommutative matrix setting. It also shows why a power-series *source* always exists from finite tangent data while the universal ring need not itself be a power-series ring.

### 16.5 Framing a scalar residual representation

Take a scalar residual representation $\bar\rho=\bar\chi\,I_d$. Its residual centralizer is all of $M_d(k)$, so the scalar-centralizer theorem does not apply. The framed tangent is $Z^1(G,M_d(k))$, whereas the unframed tangent is $H^1(G,M_d(k))$ and infinitesimal stabilizers form $M_d(k)$. Framing removes every conjugacy identification and restores exact matrix gluing.

The framed universal ring is therefore the honest set-valued parameter space under the finiteness hypotheses. The coarse unframed functor may have a hull, but the explicit example in Section 9.2 shows how its stabilizers can violate universal uniqueness. The correct groupoid remembers precisely the matrices that the orbit set discards.

## 17. The representability dictionary

### 17.1 Functors and rings

The basic translations are

$$
\begin{array}{c|c}
\text{functorial statement}&\text{complete-local statement}\\ \hline
F\simeq h_R& R\text{ is universal}\\
F\to G& R_G\to R_F\\
E\subseteq h_R\text{ cut out by equations}&R\twoheadrightarrow R/I\\
F_1\times_{F_0}F_2&R_1\widehat\otimes_{R_0}R_2\\
F_1\times F_2&R_1\widehat\otimes_{\mathcal O}R_2\\
\text{formally smooth of relative dimension }s
&\text{noncanonically adjoining }s\text{ power-series variables}.
\end{array}
$$

All ring arrows are opposite to functor arrows. Quotients represent closed subfunctors, whereas completed tensor products represent compatible simultaneous choices.

### 17.2 Infinitesimal properties

For $e:A'\twoheadrightarrow A$ small, examine

$$
F(A')\longrightarrow F(A)\times_{G(A)}G(A').
$$

Surjectivity is formal smoothness, injectivity is formal unramifiedness, and bijectivity is formal etaleness. Testing small extensions suffices because every Artinian surjection factors into them. A square-zero extension with a larger kernel can be decomposed into small steps, but its natural obstruction module may retain more coefficient action before decomposition.

The tangent dictionary is

$$
t_F=F(k[\epsilon]),
\qquad
t_{h_R}=\left(
\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R)
\right)^\vee.
$$

Tangent dimension counts minimal relative generators. Obstruction data govern higher-order relations. Automorphisms govern uniqueness of gluing. These three roles should never be merged.

### 17.3 Hull versus universal object

The logical ladder is

$$
\begin{array}{c|c|c}
\text{object}&\text{existence over small extensions}&\text{uniqueness}\\ \hline
\text{versal map }h_R\to F&\text{yes}&\text{not required}\\
\text{hull}&\text{yes, with tangent minimality}&\text{first order only}\\
\text{pro-representation}&\text{yes}&\text{yes on every Artinian test}.
\end{array}
$$

Conditions (H1)--(H3) produce a hull. Adding (H4) produces a universal ring. Hull rings are noncanonically isomorphic; a representing pair is unique up to unique compatible isomorphism.

### 17.4 Representation and cohomology entries

For a residual representation $\bar\rho$:

$$
\begin{array}{c|c|c}
\text{problem}&\text{tangent space}&\text{factor-set obstruction space}\\ \hline
\text{framed}&Z^1(G,\operatorname{ad}\bar\rho)&H^2(G,\operatorname{ad}\bar\rho)\\
\text{unframed}&H^1(G,\operatorname{ad}\bar\rho)&H^2(G,\operatorname{ad}\bar\rho)\\
\text{framed, fixed }\delta&Z^1(G,\operatorname{ad}^0\bar\rho)&H^2(G,\operatorname{ad}^0\bar\rho)\\
\text{unframed, fixed }\delta&
\ker(H^1(\operatorname{ad}\bar\rho)\to H^1(k))
&\text{determinant-preserving obstruction data}.
\end{array}
$$

The last line is intentionally not simplified when $\operatorname{char}k\mid d$. Continuous cohomology is understood throughout. Framed gluing is exact; unframed gluing is exact under scalar-centralizer control; larger stabilizers call for a framed ring, a hull if available, or a groupoid-valued refinement.

### 17.5 A representability checklist

For a new deformation problem, proceed in this order.

1. Fix $\mathcal O$, $k$, the residue identifications, and the covariant coefficient category.
2. Specify objects, equivalences, all retained auxiliary structures, and continuity.
3. Verify that the residual value is one point.
4. Compute $t_F$ and prove it finite-dimensional.
5. Construct comparison maps over coefficient fiber products and prove (H1) and (H2).
6. Decide whether automorphisms permit (H4); do not infer this from obstruction vanishing.
7. Use a complete obstruction theory, when available, to prove lifting assertions and estimate relations.
8. Conclude “hull” from (H1)--(H3), and “universal ring” only after (H4).
9. For a subcondition, prove closed relative representability before naming a quotient ring.
10. Check every inverse limit, universal representation, and ring homomorphism for the required adic continuity.

This order separates categorical, cohomological, algebraic, and topological issues so that each conclusion uses exactly its hypotheses.

## 18. Continuity and reconstruction on complete coefficient rings

### 18.1 Why Artinian tests must be reassembled

The criterion is deliberately stated on Artinian rings. Small extensions exist there, induction
terminates there, and every obstruction calculation is linear over the residue field there. The
objects eventually used in arithmetic, however, often have coefficients in a complete local
ring. One must therefore answer a question not contained in the word “representable”: when do
compatible finite-order objects determine one complete object, and when do compatible
finite-order equivalences determine one complete equivalence?

Let $S$ be a complete Noetherian local $\mathcal O$-algebra with residue field $k$, and write

$$
S_n=S/\mathfrak m_S^n.
$$

For a functor $F$ defined only on $\mathcal C$, define its **continuous extension** to complete
coefficient rings by

$$
\widehat F(S)=\varprojlim_n F(S_n).
$$

An element of $\widehat F(S)$ is not an arbitrary collection of finite-order objects. It is a
compatible collection. The distinction is decisive: existence at each level does not choose
transition-compatible objects, just as a nonempty inverse system of sets need not have a point
without a lifting or compactness argument.

If a deformation assignment $F^{\mathrm c}$ is already defined on complete rings as well as on
Artinian rings, there is a natural reduction map

$$
F^{\mathrm c}(S)\longrightarrow \varprojlim_nF(S_n).
$$

We call $F^{\mathrm c}$ **continuous** when this map is bijective for every $S$ in its complete
coefficient category. This is a property of the moduli problem, not merely of the topology on
$S$.

### 18.2 Represented functors are continuous

The first reconstruction theorem shows that no extra complete-level choices appear for a
represented functor.

**Theorem (complete reconstruction of a mapping functor).** Let $R$ and $S$ be complete
Noetherian local $\mathcal O$-algebras with the specified residue field. Then reduction induces a
natural bijection

$$
\operatorname{Hom}_{\mathrm{cts,loc},\mathcal O}(R,S)
\xrightarrow{\sim}
\varprojlim_n
\operatorname{Hom}_{\mathrm{loc},\mathcal O}(R,S_n).
$$

Consequently, if $F\simeq h_R$ on Artinian rings, then

$$
\widehat F(S)\simeq
\operatorname{Hom}_{\mathrm{cts,loc},\mathcal O}(R,S).
$$

**Proof strategy.** A complete target is its inverse limit of Artinian quotients. Evaluate a
compatible family of maps on each element of the source and reconstruct its value in that
limit. Locality, the $\mathcal O$-structure, and multiplication can all be checked at finite
level.

**Proof.** A continuous local map $R\to S$ gives compatible maps $R\to S_n$. Conversely, let
$(u_n)_n$ be compatible. For $r\in R$, the sequence $(u_n(r))_n$ is an element of
$\varprojlim_nS_n=S$; call it $u(r)$. Addition, multiplication, the unit, and the
$\mathcal O$-algebra property hold after every projection to $S_n$, hence hold in the separated
ring $S$. The residue map shows that $u$ is local. Moreover

$$
u(\mathfrak m_R^n)\subseteq\mathfrak m_S^n,
$$

so $u$ is continuous. The constructions are inverse. Applying the Artinian representing
bijections before taking the limit proves the final assertion. $\square$

This theorem also reconstructs natural transformations. A transformation between represented
functors on Artinian rings determines its reversed map of representing rings, and that one map
governs the transformation on every complete coefficient ring.

### 18.3 Universal elements as one continuous object

The compatible universal classes over $R/\mathfrak m_R^n$ are often more useful when assembled
into an actual object over $R$. Whether this assembly is automatic depends on the kind of object.

For a represented abstract functor, the universal datum is intrinsically the compatible family

$$
\xi_n\in F(R/\mathfrak m_R^n).
$$

One should not write $\xi\in F(R)$ unless $F$ has been extended to complete rings. With the
continuous extension just defined, the notation becomes legitimate:

$$
\xi=(\xi_n)_n\in\widehat F(R).
$$

For matrix representations, entrywise inverse limits turn this family into a continuous
homomorphism

$$
\rho^{\mathrm{univ}}:G\longrightarrow\operatorname{GL}_d(R).
$$

Multiplicativity holds because it holds modulo every power of $\mathfrak m_R$. Continuity holds
because the inverse image of the $n$th congruence subgroup is the kernel of the finite-level
representation and is therefore open. This argument uses the adic topology essentially; an
abstract matrix homomorphism into the underlying ring would not provide the same conclusion.

### 18.4 Framed representation functors are continuous

Framing makes complete reconstruction completely transparent.

**Proposition.** For every complete Noetherian local coefficient ring $S$,

$$
D_{\bar\rho}^{\square}(S)
\xrightarrow{\sim}
\varprojlim_nD_{\bar\rho}^{\square}(S_n).
$$

The same statement holds with a fixed determinant.

**Proof.** A complete lift gives its reductions. Conversely, a compatible family of framed
lifts is a compatible family of matrices. Taking inverse limits entry by entry produces a
matrix-valued homomorphism over $S$, and the preceding continuity argument applies. Determinant
commutes with reduction and inverse limits, so a compatible family with determinant $\delta$
has determinant $\delta$ over $S$. $\square$

No finiteness assumption on the tangent space is needed for this proposition. Tangent finiteness
is needed to obtain a Noetherian universal ring; it is not needed to reconstruct a given
complete framed lift.

### 18.5 Unframed classes and compatible conjugators

For unframed objects, compatible classes need not arrive with compatible representatives. The
missing arrows must be constructed.

**Theorem (continuity of unframed representation classes).** Assume that $k$ is finite. For
every complete Noetherian local coefficient ring $S$, reduction induces a natural bijection

$$
D_{\bar\rho}(S)
\xrightarrow{\sim}
\varprojlim_nD_{\bar\rho}(S_n).
$$

The same conclusion holds for fixed-determinant classes.

**Proof strategy.** For existence, adjust representatives successively by lifted strict
conjugators. For uniqueness, organize finite-level conjugators into a finitely branching tree
and extract one compatible infinite branch.

**Proof.** Given compatible classes $x_n$, choose a representative $\rho_1$. Suppose
$\rho_n$ has been chosen. Any representative of $x_{n+1}$ reduces to something strictly
equivalent to $\rho_n$. A strict conjugator over $S_n$ lifts to one over $S_{n+1}$ by lifting
its entries; a matrix reducing to an invertible matrix is invertible. Conjugating by this lift
produces $\rho_{n+1}$ reducing exactly to $\rho_n$. The inverse limit of the representatives is
a complete lift.

For injectivity, let $\rho$ and $\rho'$ be complete lifts which are strictly equivalent modulo
every $\mathfrak m_S^n$. Let $C_n$ be the set of strict conjugators between their reductions.
Each $C_n$ is finite because $S_n$ is finite, and it is nonempty by hypothesis. Reduction maps
conjugators to conjugators. A conjugator at level $N$ and all its reductions form a branch of
length $N$ in the resulting finitely branching tree. Starting at the root, choose at each level
a child having descendants at arbitrarily large levels; one exists because there are only
finitely many children. This recursion gives an infinite branch. Its inverse limit is a strict
conjugator over $S$. The fixed determinant condition changes no conjugator and hence no part of
the proof. $\square$

Finiteness of $k$ is used exactly in the compactness argument. With an infinite residue field,
one needs a replacement such as compactness of the relevant congruence groups or a direct
surjectivity theorem for the sets of conjugators. It should not be deleted merely because the
finite-level algebra looks identical.

### 18.6 Reconstructing a hull over a complete target

A hull need not classify Artinian objects uniquely, so it cannot become universal merely by
passing to a limit. It nevertheless remains versal at complete level.

**Proposition.** Let $q:h_R\to F$ be a hull. For every complete Noetherian local $S$, the map

$$
\operatorname{Hom}_{\mathrm{cts,loc},\mathcal O}(R,S)
\longrightarrow\widehat F(S)
$$

is surjective. If $q$ is a pro-representation, it is bijective.

**Proof strategy.** Choose a classifying map at the first level. Formal smoothness lets it be
lifted compatibly whenever the prescribed object is lifted to the next level.

**Proof.** Let $(x_n)_n\in\widehat F(S)$. The unique residue map $R\to k=S_1$ represents
$x_1$. Suppose $u_n:R\to S_n$ represents $x_n$. Apply formal smoothness of $q$ to the
surjection $S_{n+1}\twoheadrightarrow S_n$, the map $u_n$, and the object $x_{n+1}$. It gives
$u_{n+1}$ lifting $u_n$ and representing $x_{n+1}$. The compatible maps reconstruct
$R\to S$. If $q$ is a representation, finite-level uniqueness and the theorem of Section 18.2
give uniqueness at the limit. $\square$

Thus a versal ring supplies coordinates for every complete object, but those coordinates may
not be unique. The universal-versus-versal distinction survives completion unchanged.

### 18.7 A discontinuous extension as a warning

Continuity is not forced if one invents values on complete rings independently of the Artinian
restriction. Let $S=k[[T]]$ and consider the category whose objects are $S$ and
$S_n=S/(T^n)$, with the quotient maps and identities as arrows. Define a covariant functor by
giving every $S_n$ one point, giving $S$ two points, and sending both complete-level points to
the unique point under every reduction. Then

$$
F(k[[T]])\longrightarrow\varprojlim_nF(k[[T]]/(T^n))
$$

is not injective. The second complete-level point is invisible at every finite order.

Such phantom data cannot occur for a mapping functor represented by a separated complete ring.
The example explains why the continuity axiom is substantive whenever a moduli problem is
defined on complete rings before its Artinian representability has been established.

### 18.8 Continuity of closed conditions

Closed relative conditions are automatically compatible with complete reconstruction. Suppose
$F=h_R$ and $E=h_{R/I}$ for a closed ideal $I$. Then for every complete target $S$,

$$
\widehat E(S)
=\{u:R\to S\mid u(I)=0\}.
$$

Indeed, $u(I)$ vanishes in every $S_n$ exactly when it lies in
$\bigcap_n\mathfrak m_S^n=0$. This elementary separation argument is the complete-level reason
closed equations can be checked at every finite order.

The conclusion can fail for a subfunctor not defined by a closed ideal. The earlier example
$E(A)=\mathfrak m_A^2\subseteq\mathfrak m_A$ shows that functorial membership and even a simple
finite-level description do not by themselves produce a formal closed subspace whose complete
points are reconstructed by equations.

### 18.9 The continuity protocol

Whenever a complete coefficient ring occurs, the safe order is now clear. First reduce the
object to every Artinian quotient. Next verify compatibility, including compatibility of arrows
or conjugators rather than only of isomorphism classes. Then use completeness to construct the
limit and separatedness to verify identities. Finally prove that the constructed action or
homomorphism is continuous by testing the congruence quotients.

For represented functors this protocol is a theorem. For framed matrices it is entrywise. For
unframed classes over a finite residue field it uses the finite conjugator tree. For a general
moduli problem it is an additional continuity assertion that must be proved rather than inferred
from notation.

## 19. Change of coefficient base

### 19.1 Two different changes of coefficients

Changing coefficients can mean either changing the complete base while retaining the same
residual field, or enlarging the residual field and hence changing the special fiber. These
operations have different universal properties. Conflating them is a reliable way to reverse a
ring map or assert a false descent theorem.

Let

$$
\mathcal O\longrightarrow\mathcal O'
$$

be a continuous local homomorphism of complete Noetherian local rings. We first assume that it
induces the identity on the common residue field $k$. An Artinian local $\mathcal O'$-algebra is
then also an object of $\operatorname{Art}_{\mathcal O}$ after forgetting part of its structure.
For $F$ on $\operatorname{Art}_{\mathcal O}$ define

$$
F_{\mathcal O'}(A)=F(A_{\mathcal O}),
$$

where the subscript on the right means restriction of scalars. This is the **restricted-base
extension** of $F$. It enlarges the allowed structural maps but does not alter the residual
object.

### 19.2 Universal rings under a same-residue base change

The completed tensor product gives the exact answer for restricted-base extension.

**Theorem (base change of a representing ring).** Suppose $F$ is represented over $\mathcal O$
by $R$, and assume that

$$
R_{\mathcal O'}=R\widehat\otimes_{\mathcal O}\mathcal O'
$$

is a complete Noetherian local ring with residue field $k$; this holds, for example, in the
residue-compatible topologically finite-type setting. Then $F_{\mathcal O'}$ is represented by
$R_{\mathcal O'}$.

**Proof.** For every $A\in\operatorname{Art}_{\mathcal O'}$, the universal property of the
completed tensor product gives

$$
\begin{aligned}
\operatorname{Hom}_{\mathcal O'}
(R\widehat\otimes_{\mathcal O}\mathcal O',A)
&\simeq\operatorname{Hom}_{\mathcal O}(R,A)\\
&\simeq F(A_{\mathcal O}).
\end{aligned}
$$

All maps are local and continuous; continuity into the Artinian target is automatic. Naturality
in $A$ proves the representing statement. $\square$

No flatness is needed for this universal property. Flatness becomes necessary when one wants
old kernels, tangent spaces, or minimal relation modules to survive without acquiring torsion.

The same proof applies to a hull: completed base change of its ring gives a hull for the
restricted-base functor, provided the completed tensor product remains in the complete
Noetherian local category. Formal smoothness is preserved because lifting an
$\mathcal O'$-algebra map is a special case of lifting the underlying $\mathcal O$-algebra map,
and both tangent maps are evaluated on the same dual-number ring $k[\epsilon]$. Thus tangent
minimality is preserved even without flatness; the stronger module comparison in Section 19.4
does require flatness.

### 19.3 Base-changing a presentation

Suppose

$$
R\simeq\mathcal O[[X_1,\ldots,X_r]]/I.
$$

Assume $\mathcal O'[[X_1,\ldots,X_r]]$ is complete Noetherian local and that the completed tensor product is the maximal-ideal-adic completion of the ordinary tensor product. Then

$$
R_{\mathcal O'}
\simeq
\mathcal O'[[X_1,\ldots,X_r]]/\overline{I\mathcal O'[[\mathbf X]]}.
$$

The closure records the topology; it is redundant in the Noetherian target. This formula is
always a presentation of the base-changed ring, but it need not remain minimal and the map

$$
I/\mathfrak m_PI
\longrightarrow
I'/\mathfrak m_{P'}I'
$$

need not preserve dimension after a nonflat change. For example, the one relation defining
$\mathcal O/(\varpi)$ disappears after the coefficient change $\mathcal O\to k$.

Thus “the same equations after base change” means extension of the closed ideal. It does not
mean that the same list remains a minimal list of independent equations.

### 19.4 Tangent spaces after flat coefficient extension

The relative cotangent space is designed to ignore directions already contained in the base.
Suppose $\mathcal O\to\mathcal O'$ is flat and induces a field extension $k\to k'$. Assume
$R$ is topologically of finite type over $\mathcal O$ and
$R'=R\widehat\otimes_{\mathcal O}\mathcal O'$ is complete Noetherian local with residue field
$k'$. Then there is a natural isomorphism

$$
\frac{\mathfrak m_{R'}}
{\mathfrak m_{R'}^2+\mathfrak m_{\mathcal O'}R'}
\simeq
\frac{\mathfrak m_R}
{\mathfrak m_R^2+\mathfrak m_{\mathcal O}R}
\otimes_k k'.
$$

Dualizing gives the corresponding scalar extension of tangent spaces when the spaces are
finite-dimensional. Flatness prevents an old first-order direction from being killed by
coefficient torsion. For a same-residue flat change, the tangent dimension is unchanged.

If $P=\mathcal O[[\mathbf X]]\twoheadrightarrow R$ is minimal, flatness of
$P\to P'=\mathcal O'[[\mathbf X]]$ and exact base change of the kernel imply

$$
\frac{I'}{\mathfrak m_{P'}I'}
\simeq
\frac{I}{\mathfrak m_PI}\otimes_k k'.
$$

Hence the minimal relation number is also unchanged. These hypotheses are exact: completion by
itself is not an exact operation on arbitrary modules, and nonflat specialization can both
destroy and create kernel.

### 19.5 Enlarging the residual field

Now suppose $\mathcal O'$ has residue field $k'$ strictly larger than $k$. The scalar extension

$$
\bar\rho_{k'}:G\longrightarrow\operatorname{GL}_d(k')
$$

is a new residual representation and has its own deformation functor. Base-changing the old
universal representation gives a deformation of $\bar\rho_{k'}$ over
$R\widehat\otimes_{\mathcal O}\mathcal O'$. If the new deformation functor is represented by
$R_{\bar\rho_{k'}}$, universality therefore gives a canonical map

$$
R_{\bar\rho_{k'}}
\longrightarrow
R_{\bar\rho}\widehat\otimes_{\mathcal O}\mathcal O'.
$$

The arrow has this direction because the base-changed old family is one point of the new
functor. It need not be an isomorphism. A $k'$-valued deformation may have coefficients that do
not descend to $k$, and an isomorphism with all coefficient conjugates is not by itself
effective descent data.

An isomorphism follows under the strong and exact hypothesis that, for every Artinian
$\mathcal O'$-algebra $A$, scalar extension induces a natural bijection between the relevant old
deformations after restricted base change and all deformations of $\bar\rho_{k'}$ over $A$.
This hypothesis is a descent theorem; it is not a consequence of tangent-space comparison.

### 19.6 Cohomology after a finite residue extension

Although individual deformations need not descend, their linear theories extend cleanly. Let
$k'/k$ be finite and $M$ a finite-dimensional continuous $k[G]$-module. Then

$$
H^i(G,M)\otimes_k k'
\xrightarrow{\sim}
H^i(G,M\otimes_k k')
$$

for every $i\geq0$.

**Proof.** Choose a $k$-basis of $k'$. A continuous cochain with values in
$M\otimes_kk'$ is a finite tuple of continuous $M$-valued cochains, and the differential acts
coordinatewise. Thus the cochain complexes are related by tensoring with $k'$. Since a field
extension is flat, kernels, images, and quotients commute with that tensor product. $\square$

Applying this to $\operatorname{ad}\bar\rho$ and $\operatorname{ad}^0\bar\rho$ compares the
tangent and factor-set obstruction spaces. It proves equality of their dimensions after scalar
extension. It does not prove equality of universal rings, because rings contain nonlinear
descent information invisible to these vector spaces.

### 19.7 Fixed determinants under coefficient change

A determinant can be transported only when its values can be transported. If

$$
\delta:G\to\mathcal O^\times
$$

is fixed, composition with $\mathcal O\to\mathcal O'$ gives
$\delta':G\to(\mathcal O')^\times$. Under same-residue restricted-base extension, the theorem of
Section 19.2 gives

$$
R_{\bar\rho}^{\square,\delta}
\widehat\otimes_{\mathcal O}\mathcal O'
$$

as the representing ring for the correspondingly restricted fixed-determinant problem. The
quotient and completed base-change operations commute:

$$
(R/I_\delta)\widehat\otimes_{\mathcal O}\mathcal O'
\simeq
(R\widehat\otimes_{\mathcal O}\mathcal O')/\overline{I_\delta R'}.
$$

With a larger residue field, the same canonical comparison map as in Section 19.5 exists for the
new fixed-determinant universal ring. Again, it is an isomorphism only after an actual descent
theorem. The trace-kernel tangent formula commutes with finite field extension because trace and
the cochain differential do.

### 19.8 What coefficient change preserves

The reliable conclusions can be summarized without slogans. The completed tensor product
represents restricted change of a same-residue base. Flatness preserves exact finite-module
sequences, relative tangent dimensions, exact kernel extension, and minimal relation numbers.
Finite residue-field extension preserves continuous cohomology after tensoring. None of these
facts says that every deformation over the larger residual field descends, and none turns a
nonuniversal hull into a universal object.

Thus coefficient change has three layers:

$$
\begin{array}{c|c}
\text{layer}&\text{needed hypothesis}\\ \hline
\text{represent restricted-base functor}&
\text{completed tensor product remains complete Noetherian local}\\
\text{preserve tangent and relation modules}&
\text{flatness and exact extension of the presentation kernel}\\
\text{identify all enlarged-residue deformations}&
\text{effective descent of objects and equivalences}.
\end{array}
$$

Keeping these layers separate is what makes later coefficient extensions safe.

## 20. Local and global deformation rings

### 20.1 Why localization is a fiber-product problem

A global representation is constrained by its restrictions to several local groups. The global
object and the local objects are not independent: they must agree under restriction. This is
exactly the situation encoded by a fiber product of functors and, contravariantly, by a completed
tensor product of representing rings.

Let $G$ be profinite and let

$$
i_v:G_v\longrightarrow G\qquad(v\in S)
$$

be a finite family of continuous homomorphisms. Fix
$\bar\rho:G\to\operatorname{GL}_d(k)$ and put $\bar\rho_v=\bar\rho\circ i_v$. Restriction gives
natural transformations from the global framed, unframed, and fixed-determinant functors to the
corresponding products of local functors. The set $S$ is finite so that ordinary finite products
and finite completed tensor products suffice.

### 20.2 The unrestricted local product

Assume each local functor $D_v$ under consideration is represented by $R_v$. Its product is
represented by

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v\in S,\mathcal O}R_v.
$$

The exact hypotheses used here are that all structural maps are local, every factor has the
same specified residue field $k$, the set $S$ is finite, and every $R_v$ is topologically of
finite type over $\mathcal O$. Under these assumptions the finite completed tensor product is
complete Noetherian local. Topological finite type is automatic for a complete Noetherian local
$\mathcal O$-algebra whose relative cotangent space is finite-dimensional over $k$.

If the global functor $D_G$ is represented by $R_G$, restriction

$$
D_G\longrightarrow\prod_{v\in S}D_v
$$

corresponds to a continuous local map

$$
R_{\mathrm{loc}}\longrightarrow R_G.
$$

This map records all localizations of the universal global family. It need not be finite,
surjective, or injective merely because restriction exists.

Framed local functors are automatically the cleanest choice because matrix gluing is exact.
For unframed local functors, each local residual restriction needs its own representability
hypothesis; a scalar centralizer for the global representation does not imply a scalar
centralizer after restriction to every $G_v$.

### 20.3 Closed local conditions

A **local deformation condition** at $v$ is a subfunctor

$$
\mathcal L_v\hookrightarrow D_v.
$$

For the construction here, assume it is closedly relatively representable. Since $D_v=h_{R_v}$,
this means there is a closed ideal $I_v\subseteq R_v$ such that

$$
\mathcal L_v\simeq h_{R_v/I_v}.
$$

The assumption is mathematical content. It must be proved from the defining local property; it
does not follow from stability under coefficient change or from having a preferred tangent
subspace.

The product of the local conditions is represented by

$$
R_{\mathcal L}
=\widehat\bigotimes_{v\in S,\mathcal O}(R_v/I_v).
$$

There is a natural surjection

$$
R_{\mathrm{loc}}\twoheadrightarrow R_{\mathcal L}.
$$

In a joint power-series presentation its kernel is the closed ideal generated by the images of
all the $I_v$.

### 20.4 The global functor with prescribed local conditions

Define

$$
D_G^{\mathcal L}(A)
=\{x\in D_G(A):x|_{G_v}\in\mathcal L_v(A)
\text{ for every }v\in S\}.
$$

The definition is equivalently the functorial fiber product

$$
D_G^{\mathcal L}
=D_G\times_{\prod_vD_v}\prod_v\mathcal L_v.
$$

This formula does more than abbreviate membership. It proves representability once the three
displayed functors are represented.

**Theorem (global ring with local conditions).** Under the representability and complete
finite-type hypotheses above, $D_G^{\mathcal L}$ is represented by

$$
R_G^{\mathcal L}
=R_G\widehat\otimes_{R_{\mathrm{loc}}}R_{\mathcal L}.
$$

Equivalently, if $J=\ker(R_{\mathrm{loc}}\to R_{\mathcal L})$, then

$$
R_G^{\mathcal L}
\simeq R_G/\overline{JR_G}.
$$

**Proof.** A map from the completed tensor product to an Artinian ring $A$ is a pair of maps
$R_G\to A$ and $R_{\mathcal L}\to A$ agreeing on $R_{\mathrm{loc}}$. Under the representing
bijections this is a global deformation and a tuple of locally admissible deformations identified
with its restrictions. That is exactly an element of $D_G^{\mathcal L}(A)$. The quotient formula
is the quotient base-change identity for $R_{\mathrm{loc}}/J$; the closure is automatic in
the Noetherian target but records the topology. $\square$

This theorem is the precise passage from local conditions to a global universal ring. It uses
closed relative representability locally and representability of the ambient global problem. It
does not assert either hypothesis for a condition not yet analyzed.

### 20.5 Tangent spaces with local conditions

The tangent formula is the linear shadow of the fiber product. Let $t_G$ be the tangent space of
the global functor, let $t_v$ be that of $D_v$, and let $L_v\subseteq t_v$ be the tangent space of
$\mathcal L_v$. Then

$$
t_{D_G^{\mathcal L}}
=\{x\in t_G:\operatorname{res}_v(x)\in L_v
\text{ for every }v\in S\}.
$$

**Proof.** Evaluate the functorial fiber product on $k[\epsilon]$. Fiber products of sets commute
with this evaluation, and every tangent set involved is a vector space because the functors
satisfy the first-order gluing condition. The resulting fiber product of vector spaces is exactly
the displayed inverse image. $\square$

For an unframed unrestricted representation problem,

$$
t_G=H^1(G,\operatorname{ad}\bar\rho),
\qquad
t_v=H^1(G_v,\operatorname{ad}\bar\rho_v).
$$

Thus the global tangent space with local conditions is the kernel of the localization map to
the quotients:

$$
\ker\left(
H^1(G,\operatorname{ad}\bar\rho)
\longrightarrow
\prod_{v\in S}H^1(G_v,\operatorname{ad}\bar\rho_v)/L_v
\right).
$$

For framed problems use cocycles. For fixed determinant use the exact trace-kernel tangent
formula; it simplifies to cohomology with trace-zero coefficients only under the splitting
hypothesis stated earlier.

### 20.6 Obstructions with local conditions

An ambient global obstruction class lies in

$$
H^2(G,\operatorname{ad}\bar\rho)\otimes_k I
$$

for an unrestricted small extension. Its restriction is the ambient local obstruction at every
$v$. Vanishing of all local restrictions does not imply vanishing of the global class unless the
relevant localization map is injective on that class.

Imposing local conditions adds a second issue. Even if an ambient local representation lifts,
it may fail to lift **inside** $\mathcal L_v$. Consequently the obstruction theory for
$D_G^{\mathcal L}$ is not automatically the kernel of a map between ambient $H^2$ groups. A
valid constrained obstruction package must provide:

1. a complete obstruction to the global ambient lift;
2. complete obstructions to membership-preserving local lifts;
3. compatibility of the localized global class with the local classes;
4. a degree-one correction criterion for moving an existing global lift into the prescribed
   local torsors.

Once such a finite-dimensional, functorial, additive, effective package $V_{\mathcal L}$ is
proved, it bounds the minimal relations of $R_G^{\mathcal L}$. Without it, representability of
the quotient ring still holds, but no cohomological relation bound has been justified.

### 20.7 Framed global problems

Framing avoids both residual centralizer hypotheses and ambiguous comparison arrows. If $G$ and
each $G_v$ have finite-dimensional framed tangent spaces, all framed ambient functors are
represented. The restriction diagram therefore produces a framed global ring with any closedly
represented framed local conditions exactly as in Section 20.4.

There are several inequivalent framings in a global problem. One may retain one global frame,
retain independent frames at selected local groups, or add auxiliary local frames to a global
unframed object. Their tangent dimensions differ by explicit change-of-frame spaces. A theorem
relating their rings by power-series variables requires the corresponding forgetful
transformation to be formally smooth and both endpoint functors to be represented. Merely
counting the extra matrices does not prove the power-series statement.

In the common scalar-centralizer situation, forgetting one global frame is formally smooth of
relative tangent dimension $d^2-1$, so

$$
R_G^{\square}\simeq R_G[[Y_1,\ldots,Y_{d^2-1}]]
$$

noncanonically. More generally, for a single restriction $\bar\rho_v$, the change-of-frame
space has dimension

$$
d^2-\dim_k H^0(G_v,\operatorname{ad}\bar\rho_v).
$$

If the corresponding forgetful maps are formally smooth and both their source and target
functors are represented, independent local frames add these dimensions and hence add that many
power-series variables. Without those hypotheses, the dimension calculation is only a tangent
calculation.

### 20.8 The global restricted-ramification specialization

Let $F$ be a global field, let $S$ be a finite set of places containing every place at which the
residual representation or allowed lifts may ramify, and let $G_{F,S}$ be the quotient of the
absolute Galois group obtained by killing inertia outside $S$. Continuous representations
unramified outside $S$ are exactly the representations factoring through $G_{F,S}$.

Assume the finite-tangent condition $\Phi_p$ for $G_{F,S}$, where $p=\operatorname{char}k$.
Then the framed unrestricted functor has a universal ring. If

$$
\operatorname{End}_{k[G_{F,S}]}(k^d)=k,
$$

the unframed unrestricted functor also has a universal ring. A continuous determinant lift may
be imposed by quotient. At each $v\in S$, any local condition already proved closedly relatively
representable may then be imposed by the completed fiber-product theorem.

These are exact existence hypotheses. Arithmetic finiteness theorems may be used to verify
$\Phi_p$ in a particular situation, while geometric or cohomological arguments may establish
closed relative representability of a local condition. The abstract representability theorem
does not replace either verification.

### 20.9 Local and global uniqueness

Once the functors in the diagram are represented, their rings and all structural maps are unique
up to the unique isomorphisms compatible with the chosen representing identifications. The
completed tensor description of $R_G^{\mathcal L}$ is therefore independent of presentations of
the local rings or choices of generators for their defining ideals.

If an ambient unframed functor has a hull $h_R\to D_G$ rather than a representing object, its
pullback along $\prod_v\mathcal L_v\to\prod_vD_v$ parametrizes a restricted deformation together
with a chosen point of $h_R$ above it. If this parameterized pullback is closedly relatively
representable over $h_R$, it is represented by a quotient of $R$. That quotient represents the
parameterized problem, not automatically the coarse restricted functor. A hull for the coarse
restricted functor follows only after (H1)--(H3) are verified for that functor itself; identifying
the quotient just constructed with such a hull additionally requires its map to be formally smooth
and tangent-bijective. Without (H4), none of these statements gives pointwise uniqueness. If a local
condition is represented only after adding a filtration or a line, forgetting that structure
must be analyzed before its image can be inserted as a quotient condition. Universality at the
global level is no stronger than the weakest descent and uniqueness statement used in building
the diagram.

## 21. Exact existence and presentation theorems

### 21.1 Why the hypotheses should be collected

The theory has accumulated several logically independent assumptions: one controls finite
tangent dimension, one controls automorphisms, one supplies a determinant, one makes local
conditions closed, and one makes obstruction spaces count equations. A final theorem should
display these separately so that later applications can cite exactly what they have proved.

Continue to let $k$ be finite of characteristic $p$, let $\mathcal O$ be complete Noetherian
local with residue field $k$, let $G$ be profinite, and let

$$
\bar\rho:G\to\operatorname{GL}_d(k)
$$

be continuous.

### 21.2 The master representability theorem

**Theorem (existence of universal representation rings).** Assume that
$Z^1(G,\operatorname{ad}\bar\rho)$ is finite-dimensional. Then:

1. The framed deformation functor is represented by a complete Noetherian local
   $\mathcal O$-algebra $R_{\bar\rho}^{\square}$.
2. If $\operatorname{End}_{k[G]}(k^d)=k$, the unframed deformation functor is represented by a
   complete Noetherian local $\mathcal O$-algebra $R_{\bar\rho}$.
3. Given a continuous lift $\delta:G\to\mathcal O^\times$ of $\det\bar\rho$, the framed
   fixed-determinant functor is represented by a quotient
   $R_{\bar\rho}^{\square,\delta}$ of $R_{\bar\rho}^{\square}$.
4. Under the scalar-centralizer hypothesis, the unframed fixed-determinant functor is represented
   by a quotient $R_{\bar\rho}^{\delta}$ of $R_{\bar\rho}$.

Condition $(\Phi_p)$ is a convenient sufficient hypothesis for the finite-dimensionality in the
first sentence. Topological finite generation of $G$ is a still simpler sufficient hypothesis.

**Proof.** Framed lifts preserve every admissible coefficient fiber product exactly. Their
tangent space is $Z^1(G,\operatorname{ad}\bar\rho)$, finite by hypothesis. Hence they satisfy
(H1)--(H4), and the criterion gives (1). Under the scalar-centralizer hypothesis, all
centralizers of Artinian lifts are scalar. The argument of Chapter 11 then makes comparison
arrows unique up to liftable scalars, proving (H4) for unframed classes; their tangent space is a
quotient of the finite-dimensional framed tangent space. This proves (2). Equality with the
fixed determinant is a closed equation on the universal family, giving the quotient in (3), and
scalar conjugation preserves determinant, giving (4). $\square$

The theorem requires no vanishing or finiteness of $H^2$. Those properties govern the equations
inside the universal ring, not its existence.

### 21.3 Minimal numbers of variables

Each universal ring has a minimal relative power-series presentation. The exact numbers of
variables are

$$
\begin{array}{c|c}
\text{problem}&\text{minimal relative variables}\\ \hline
\text{framed}&\dim_kZ^1(G,\operatorname{ad}\bar\rho)\\
\text{unframed}&\dim_kH^1(G,\operatorname{ad}\bar\rho)\\
\text{framed, fixed }\delta&
\dim_kZ^1(G,\operatorname{ad}^0\bar\rho)\\
\text{unframed, fixed }\delta&
\dim_k\ker\bigl(H^1(G,\operatorname{ad}\bar\rho)
\to H^1(G,k)\bigr).
\end{array}
$$

The last line becomes $\dim_kH^1(G,\operatorname{ad}^0\bar\rho)$ when
$\operatorname{char}k\nmid d$. In the excluded characteristic the scalar line may lie inside
$\operatorname{ad}^0$, and the trace-kernel formula is the invariant statement.

These numbers count cotangent generators, not distinguished ring elements. Choosing a dual basis
and lifts produces coordinates, and a different choice produces a formal coordinate change.

### 21.4 Relation bounds from representation obstructions

Assume now that the indicated second cohomology group is finite-dimensional. The factor-set
obstruction theory for representations is complete, functorial under pushout, additive in the
small kernel, and compatible with the tangent torsor action. The universal small extensions
selected by functionals on a minimal relation module therefore give the effective obstruction
map described in Section 8.4.

**Theorem (cohomological presentation bounds).** Under the hypotheses of Section 21.2 there are
minimal presentations

$$
R_{\bar\rho}^{\square}
\simeq
\mathcal O[[X_1,\ldots,X_z]]/(f_1,\ldots,f_s),
$$

with

$$
z=\dim_kZ^1(G,\operatorname{ad}\bar\rho),
\qquad
s\leq\dim_kH^2(G,\operatorname{ad}\bar\rho).
$$

Under the scalar-centralizer hypothesis there is likewise

$$
R_{\bar\rho}
\simeq
\mathcal O[[X_1,\ldots,X_h]]/(g_1,\ldots,g_t),
$$

with

$$
h=\dim_kH^1(G,\operatorname{ad}\bar\rho),
\qquad
t\leq\dim_kH^2(G,\operatorname{ad}\bar\rho).
$$

For fixed determinant, replace the second cohomology group by
$H^2(G,\operatorname{ad}^0\bar\rho)$ and use the fixed-determinant tangent dimensions of
Section 21.3.

**Proof strategy.** A functional on the minimal relation space loosens one universal equation and
produces a principal small extension of an Artinian quotient of the universal ring. The
universal deformation has an obstruction in the displayed $H^2$. If the resulting linear map
from the dual relation space had a kernel, completeness and the torsor compatibility would lift
the universal family after deleting that relation direction, contradicting minimality. Hence
the dual relation space injects into $H^2$, giving the bound. $\square$

The proof gives an inequality. The second cohomology group can contain classes never realized by
universal equations, and minimal equations can have smaller height than their number. No equality
of relation number, obstruction dimension, or codimension follows without further arguments.

### 21.5 The unobstructed case

When the controlling second cohomology group vanishes, the conclusion becomes structural rather
than merely numerical.

**Corollary.** If

$$
H^2(G,\operatorname{ad}\bar\rho)=0,
$$

then

$$
R_{\bar\rho}^{\square}
\simeq
\mathcal O[[X_1,\ldots,X_z]]
$$

noncanonically. Under the scalar-centralizer hypothesis,

$$
R_{\bar\rho}
\simeq
\mathcal O[[X_1,\ldots,X_h]].
$$

For fixed determinant, the same conclusion holds when the complete determinant-preserving
obstruction space $H^2(G,\operatorname{ad}^0\bar\rho)$ vanishes, with the correct
fixed-determinant tangent dimension.

**Proof.** Vanishing of the complete factor-set obstruction makes every small-extension lifting
problem solvable, so the represented functor is formally smooth over $\mathcal O$. The
power-series characterization of a topologically finite-type formally smooth complete local
algebra gives the displayed rings. $\square$

This corollary would be false if $H^2$ were merely a receptacle containing the actual
obstructions without a completeness theorem. It would also fail for a coarse unframed functor
that had not first been proved representable.

### 21.6 Locally constrained presentation bounds

Let $D_G^{\mathcal L}$ be the globally constrained functor of Chapter 20 and suppose it is
represented by $R_G^{\mathcal L}$. Its tangent dimension gives the exact number of variables in
a minimal presentation over $\mathcal O$. More usefully, suppose the structural map
$R_{\mathcal L}\to R_G^{\mathcal L}$ is local, both rings have residue field $k$, and
$R_G^{\mathcal L}$ is topologically of finite type over $R_{\mathcal L}$.

If the relative tangent space has dimension $g$, there is a minimal surjection

$$
R_{\mathcal L}[[X_1,\ldots,X_g]]\twoheadrightarrow R_G^{\mathcal L}.
$$

If a finite-dimensional space $V_{G/\mathcal L}$ supplies a complete, functorial, additive, and
effective **relative** obstruction theory, then the kernel is generated by at most
$\dim_kV_{G/\mathcal L}$ elements. Hence

$$
\dim R_G^{\mathcal L}
\geq
\dim R_{\mathcal L}+g-\dim_kV_{G/\mathcal L}.
$$

No regularity or flatness of $R_{\mathcal L}$ is needed for the presentation or the elementary
dimension inequality. Such hypotheses are needed for sharper dimension formulas, preservation
under coefficient change, or complete-intersection conclusions.

The adjective relative prevents double counting. Equations already defining the local
conditions live in $R_{\mathcal L}$; the new variables and equations measure only global
compatibility beyond those local choices.

### 21.7 Universal versus versal rings in applications

The word attached to a ring determines what conclusions may be drawn from it. A universal ring
gives a natural bijection for every Artinian target and, by continuity, for every complete
target. Its points, maps, quotient conditions, and coefficient changes are therefore uniquely
classified.

A versal ring gives existence of classifying maps but not uniqueness. A hull is a versal ring
with minimal tangent space; its dimension and minimal presentation are meaningful up to
noncanonical isomorphism, and an effective obstruction theory can still bound its relations.
But two maps from a hull to the same coefficient ring may determine the same deformation, and a
map between moduli problems need not determine a unique reversed map between chosen hulls.

The safe terminology is therefore:

$$
\begin{array}{c|c}
\text{available statement}&\text{permitted conclusion}\\ \hline
(H1)\text{--}(H3)&\text{a hull, hence a minimal versal formal space}\\
(H1)\text{--}(H4)&\text{a universal ring and unique classification}\\
\text{framed exact gluing + finite tangent}&\text{a framed universal ring}\\
\text{unframed scalar centralizer + finite tangent}&
\text{an unframed universal ring}\\
\text{larger stabilizers}&
\text{a hull at best unless uniqueness is separately proved}.
\end{array}
$$

This distinction is not weakened by complete reconstruction, fixed determinant, local
conditions, or coefficient extension. Every later construction inherits the same level of
uniqueness as its inputs.

## 22. Conclusion

### 22.1 The formal space assembled from finite tests

A deformation functor begins as a collection of answers over finite local thickenings. Fiber products ask whether two answers with a common shadow can be glued; small extensions reduce that question to one infinitesimal layer; the tangent space identifies the necessary generators. Under (H1)--(H3), these data can be organized into compatible quotients of a finite-variable power-series ring. Their inverse limit is complete and Noetherian, and its universal system maps formally smoothly to the functor. That is the hull.

The additional self-gluing condition (H4) removes the last ambiguity. It turns the hull's existence statement into unique classification and hence into a universal deformation ring. This is a categorical uniqueness phenomenon, not an obstruction-vanishing phenomenon.

### 22.2 The role of automorphisms

Framed representations glue as matrices and therefore satisfy exact fiber-product identities. Unframed classes forget comparison arrows. When the residual centralizer is scalar, every Artinian centralizer remains scalar; comparison automorphisms lift and act trivially, restoring unique descent. With a larger centralizer, the explicit second-order example shows that self-gluing can fail. The honest outcomes are then a framed universal ring, perhaps an unframed hull, or a groupoid-valued formal moduli problem—not a falsely universal coarse quotient.

Fixed determinant is a closed equation once a compatible determinant lift has been chosen. Its universal ring is a quotient of an existing ambient universal ring, while its tangent and obstruction theory retain characteristic-sensitive trace phenomena. More general local conditions likewise give quotient rings only after closed relative representability has been proved.

### 22.3 The endpoint

The reusable conclusion is now precise. Finite continuous tangent data supply a Noetherian power-series source. Schlessinger gluing supplies a hull. Automorphism-free self-gluing supplies universality. Complete obstruction theories help verify lifting and bound relations but do not replace any of those categorical steps. Quotients impose closed conditions, completed tensor products combine compatible problems, and formally smooth maps add power-series parameters.

Continuity now completes the passage from finite tests to complete coefficients: represented
functors reconstruct maps into complete rings, framed representations reconstruct entrywise, and
unframed classes reconstruct through compatible strict conjugators when the residue field is
finite. Coefficient change is governed by completed tensor products for a same-residue base,
while enlargement of the residual field requires a separate descent theorem. Finally, closed
local conditions combine with a global universal family through a functorial fiber product, whose
representing ring is the corresponding completed tensor product or quotient.

This package is the formal foundation on which later local and global deformation rings rest.
Their arithmetic content lies in defining the right conditions, proving those conditions closed
in families, and calculating their tangent and obstruction spaces. Their existence, continuity,
coefficient behavior, and exact degree of universality then follow from the mechanisms established
here.
