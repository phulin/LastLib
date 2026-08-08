# Deformation Functors of Representations

## Contents

1. [The deformation problem](#1-the-deformation-problem)
   - [From one residual representation to a family](#11-from-one-residual-representation-to-a-family)
   - [Coefficient categories and the role of a base](#12-coefficient-categories-and-the-role-of-a-base)
   - [No finiteness hypothesis on $G$ is needed yet](#13-no-finiteness-hypothesis-on-g-is-needed-yet)
   - [Matrix convention and the adjoint module](#14-matrix-convention-and-the-adjoint-module)
2. [Lifts and strict equivalence](#2-lifts-and-strict-equivalence)
   - [Why reduction includes an identification](#21-why-reduction-includes-an-identification)
   - [The congruence subgroup](#22-the-congruence-subgroup)
   - [A counterexample to arbitrary conjugacy](#23-a-counterexample-to-arbitrary-conjugacy)
   - [Base change of lifts](#24-base-change-of-lifts)
   - [Continuous lifts over complete rings](#25-continuous-lifts-over-complete-rings)
3. [Unframed and framed deformation functors](#3-unframed-and-framed-deformation-functors)
   - [The unframed set-valued functor](#31-the-unframed-set-valued-functor)
   - [The deformation groupoid](#32-the-deformation-groupoid)
   - [Why a framing removes a quotient](#33-why-a-framing-removes-a-quotient)
   - [Frames, orbits, and stabilizers](#34-frames-orbits-and-stabilizers)
   - [Residual centralizers and the first warning](#35-residual-centralizers-and-the-first-warning)
   - [A useful diagram of distinctions](#36-a-useful-diagram-of-distinctions)
4. [Determinants and constrained deformations](#4-determinants-and-constrained-deformations)
   - [Why the determinant must be lifted first](#41-why-the-determinant-must-be-lifted-first)
   - [Fixed-determinant functors](#42-fixed-determinant-functors)
   - [Determinant linearization](#43-determinant-linearization)
   - [When trace zero splits off](#44-when-trace-zero-splits-off)
   - [A characteristic-two warning in dimension two](#45-a-characteristic-two-warning-in-dimension-two)
5. [Dual numbers and first-order matrices](#5-dual-numbers-and-first-order-matrices)
   - [Why the dual numbers isolate a derivative](#51-why-the-dual-numbers-isolate-a-derivative)
   - [Deriving the cocycle equation](#52-deriving-the-cocycle-equation)
   - [A one-generator calculation](#53-a-one-generator-calculation)
   - [Continuity cannot be recovered afterward](#54-continuity-cannot-be-recovered-afterward)
6. [Strict conjugation and cohomology](#6-strict-conjugation-and-cohomology)
   - [Linearizing a strict change of basis](#61-linearizing-a-strict-change-of-basis)
   - [The canonical tangent-space theorem](#62-the-canonical-tangent-space-theorem)
   - [Framed tangent vectors and change-of-frame directions](#63-framed-tangent-vectors-and-change-of-frame-directions)
   - [Absolutely irreducible and scalar examples](#64-absolutely-irreducible-and-scalar-examples)
   - [Tangent spaces are not sets of generators](#65-tangent-spaces-are-not-sets-of-generators)
7. [Fixed-determinant tangent theory](#7-fixed-determinant-tangent-theory)
   - [Framed fixed determinant](#71-framed-fixed-determinant)
   - [Which coboundaries must be divided out](#72-which-coboundaries-must-be-divided-out)
   - [The familiar formula when $d$ is invertible](#73-the-familiar-formula-when-d-is-invertible)
   - [What changes when the characteristic divides $d$](#74-what-changes-when-the-characteristic-divides-d)
   - [Volume-framed is a different functor](#75-volume-framed-is-a-different-functor)
8. [First examples](#8-first-examples)
   - [One-dimensional characters](#81-one-dimensional-characters)
   - [The trivial residual representation](#82-the-trivial-residual-representation)
   - [Split reducible representations](#83-split-reducible-representations)
   - [A worked upper-triangular cocycle](#84-a-worked-upper-triangular-cocycle)
   - [Nonsplit reducible representations](#85-nonsplit-reducible-representations)
   - [Absolutely irreducible residual representations](#86-absolutely-irreducible-residual-representations)
9. [Lifting across square-zero extensions](#9-lifting-across-square-zero-extensions)
   - [Why multiplication fails by a two-variable defect](#91-why-multiplication-fails-by-a-two-variable-defect)
   - [The correct coefficient module for a square-zero kernel](#92-the-correct-coefficient-module-for-a-square-zero-kernel)
   - [Associativity produces the cocycle equation](#93-associativity-produces-the-cocycle-equation)
   - [Independence of provisional matrix lifts](#94-independence-of-provisional-matrix-lifts)
   - [Vanishing is equivalent to existence](#95-vanishing-is-equivalent-to-existence)
   - [Why small extensions are the standard steps](#96-why-small-extensions-are-the-standard-steps)
10. [The ambiguity and automorphisms of lifts](#10-the-ambiguity-and-automorphisms-of-lifts)
    - [Differences of two genuine lifts are cocycles](#101-differences-of-two-genuine-lifts-are-cocycles)
    - [Strict equivalence produces the $H^1$-torsor](#102-strict-equivalence-produces-the-h1-torsor)
    - [Infinitesimal automorphisms are $H^0$](#103-infinitesimal-automorphisms-are-h0)
    - [The full three-degree pattern](#104-the-full-three-degree-pattern)
    - [An unobstructed example and its limitation](#105-an-unobstructed-example-and-its-limitation)
    - [A concrete obstructed relation](#106-a-concrete-obstructed-relation)
11. [Fixed determinant across small extensions](#11-fixed-determinant-across-small-extensions)
    - [Choosing determinant-preserving provisional lifts](#111-choosing-determinant-preserving-provisional-lifts)
    - [The fixed-determinant obstruction class](#112-the-fixed-determinant-obstruction-class)
    - [Unframed ambiguity and the characteristic caveat](#113-unframed-ambiguity-and-the-characteristic-caveat)
    - [Automorphisms are not trace zero by default](#114-automorphisms-are-not-trace-zero-by-default)
12. [Functoriality of deformation problems](#12-functoriality-of-deformation-problems)
    - [Two independent kinds of variance](#121-two-independent-kinds-of-variance)
    - [Restriction to closed subgroups](#122-restriction-to-closed-subgroups)
    - [Change of residual basis](#123-change-of-residual-basis)
    - [Coefficient extension of the residue field](#124-coefficient-extension-of-the-residue-field)
    - [Direct sums](#125-direct-sums)
    - [Tensor products](#126-tensor-products)
    - [Twists and duals](#127-twists-and-duals)
13. [Local Galois representations as examples](#13-local-galois-representations-as-examples)
    - [The local setting and what is being illustrated](#131-the-local-setting-and-what-is-being-illustrated)
    - [Obstructions detected by local duality](#132-obstructions-detected-by-local-duality)
    - [Mixed-characteristic dimension formulas](#133-mixed-characteristic-dimension-formulas)
    - [Fixed determinant in mixed characteristic](#134-fixed-determinant-in-mixed-characteristic)
    - [Coefficient characteristic away from the residue characteristic](#135-coefficient-characteristic-away-from-the-residue-characteristic)
    - [Unramified tangent directions](#136-unramified-tangent-directions)
    - [A split two-character local calculation](#137-a-split-two-character-local-calculation)
    - [Elliptic-curve residual representations](#138-elliptic-curve-residual-representations)
14. [Fiber products, automorphisms, and the edge of representability](#14-fiber-products-automorphisms-and-the-edge-of-representability)
    - [Gluing framed lifts](#141-gluing-framed-lifts)
    - [Why unframed gluing is subtler](#142-why-unframed-gluing-is-subtler)
    - [The automorphism double-coset](#143-the-automorphism-double-coset)
    - [What this book does not assert](#144-what-this-book-does-not-assert)
    - [What vanishing of $H^2$ really gives](#145-what-vanishing-of-h2-really-gives)
15. [Extended worked calculations](#15-extended-worked-calculations)
    - [Deforming a character of $\mathbf Z_p$](#151-deforming-a-character-of-mathbf-z_p)
    - [A cyclic relation and the obstruction cocycle](#152-a-cyclic-relation-and-the-obstruction-cocycle)
    - [Two commuting generators](#153-two-commuting-generators)
    - [An upper-triangular deformation condition as a preview](#154-an-upper-triangular-deformation-condition-as-a-preview)
    - [A nonscalar centralizer calculation](#155-a-nonscalar-centralizer-calculation)
    - [An absolutely irreducible local example](#156-an-absolutely-irreducible-local-example)
    - [A local reducible eigenvalue jump](#157-a-local-reducible-eigenvalue-jump)
16. [The reusable deformation--cohomology dictionary](#16-the-reusable-deformation--cohomology-dictionary)
    - [Data checklist](#161-data-checklist)
    - [Object and equivalence dictionary](#162-object-and-equivalence-dictionary)
    - [Tangent dictionary](#163-tangent-dictionary)
    - [Fixed-determinant tangent dictionary](#164-fixed-determinant-tangent-dictionary)
    - [Small-extension protocol](#165-small-extension-protocol)
    - [Fixed-determinant lifting protocol](#166-fixed-determinant-lifting-protocol)
    - [Functoriality dictionary](#167-functoriality-dictionary)
    - [Topology and finiteness checklist](#168-topology-and-finiteness-checklist)
    - [Boundary checklist](#169-boundary-checklist)
17. [Conclusion](#17-conclusion)
    - [The coherent low-degree picture](#171-the-coherent-low-degree-picture)
    - [The endpoint for later deformation conditions](#172-the-endpoint-for-later-deformation-conditions)

## 1. The deformation problem

### 1.1 From one residual representation to a family

Fix a finite field $k$, a profinite group $G$, a positive integer $d$, and a continuous representation

$$
\bar\rho:G\longrightarrow \operatorname{GL}_d(k).
$$

The finite group $\operatorname{GL}_d(k)$ has the discrete topology. Thus continuity means that $\ker\bar\rho$ is open, or equivalently that $\bar\rho$ factors through a finite quotient of $G$. This innocent-looking topological condition is part of the datum. If one retained every abstract homomorphism from $G$, first-order calculations would involve abstract rather than continuous cohomology and would generally describe the wrong arithmetic problem.

The representation $\bar\rho$ is a special fiber. Deformation theory asks for representations over local rings that reduce to it. Nilpotents in those rings record directions that cannot be seen over fields: the relation $\epsilon^2=0$, for example, isolates the linear term of a matrix variation. Thicker Artinian rings retain products among lower-order variations, and complete local rings gather compatible finite-order variations into one object.

There are three distinct questions from the outset.

1. What is an individual lift, and when should two lifts count as the same?
2. How do first-order lifts form a cohomology group?
3. What prevents a lift over one coefficient ring from extending across a thicker ring?

The answers occupy degrees $0$, $1$, and $2$ of continuous cohomology. Degree zero records automorphisms, degree one records tangent directions, and degree two records multiplicative defects. The purpose of this book is to derive that dictionary carefully, including the points at which framings, determinants, centralizers, and coefficient characteristic change it.

### 1.2 Coefficient categories and the role of a base

We use the coefficient categories developed in Book 20. Let $\operatorname{Art}_k$ denote local Artinian rings $A$ equipped with a specified identification $A/\mathfrak m_A\simeq k$, with local residue-compatible homomorphisms. This formulation does not assume that $k$ embeds into $A$, so it accommodates mixed characteristic.

Frequently one fixes a complete Noetherian local base $\mathcal O$ with residue field $k$ and works in $\operatorname{Art}_{\mathcal O}$. Its objects are local Artinian $\mathcal O$-algebras with the prescribed residue identification. This is the natural setting when a determinant character already takes values in $\mathcal O^\times$. In equal characteristic one may take $\mathcal O=k$.

Because $k$ is finite, every $A\in\operatorname{Art}_k$ is a finite set: its maximal-ideal filtration has finitely many finite-dimensional $k$-layers. We give $A$ and $\operatorname{GL}_d(A)$ the discrete topology. A representation $G\to\operatorname{GL}_d(A)$ is therefore continuous exactly when its kernel is open. This finiteness makes continuous choices possible in later obstruction calculations.

A complete coefficient ring $R$ instead carries its maximal-ideal-adic topology, and $\operatorname{GL}_d(R)$ carries the induced topology. A continuous representation into it is equivalent to a compatible system of continuous representations into $\operatorname{GL}_d(R/\mathfrak m_R^n)$. This observation is useful, but the deformation functors in this book are functors on Artinian test rings. No complete ring representing them is presumed to exist.

### 1.3 No finiteness hypothesis on $G$ is needed yet

The definitions of lifts and deformation functors require only that $G$ be profinite and that all representations be continuous. The tangent identification also holds without a finite-generation hypothesis. What may fail is finite-dimensionality: $H^1(G,\operatorname{ad}\bar\rho)$ can be infinite-dimensional even though $\operatorname{ad}\bar\rho$ is finite.

Whenever a numerical dimension is asserted below, we assume the relevant cohomology groups are finite-dimensional. A convenient sufficient condition for finite tangent spaces is that $G$ be topologically finitely generated. More generally, if $p=\operatorname{char}k$, the condition that $\operatorname{Hom}_{\mathrm{cts}}(H,\mathbf F_p)$ be finite for every open subgroup $H\leq G$ is sufficient for $H^1(G,M)$ to be finite-dimensional for every finite-dimensional continuous $k[G]$-module $M$: restrict to an open subgroup acting trivially on $M$, then use inflation--restriction and the finite quotient. None of these finiteness conditions is built into the definition of the functor.

The same discipline applies to $H^2$. An obstruction class exists without assuming $H^2$ finite. Finiteness becomes important only when one later seeks finite presentations or representability, topics reserved for Book 22.

### 1.4 Matrix convention and the adjoint module

We use column vectors. A change of basis by $B$ changes a matrix representation to

$$
g\longmapsto B^{-1}\bar\rho(g)B.
$$

For deformation calculations set

$$
\operatorname{ad}\bar\rho=M_d(k)=\operatorname{End}_k(k^d),
\qquad
g\cdot X=\bar\rho(g)X\bar\rho(g)^{-1}.
$$

This is a finite discrete continuous $G$-module. Its invariant space is the residual centralizer:

$$
H^0(G,\operatorname{ad}\bar\rho)
=\operatorname{End}_{k[G]}(k^d).
$$

The order of the conjugation in this formula fixes every later sign. We write continuous inhomogeneous cocycles additively:

$$
c(gh)=c(g)+g\cdot c(h),
$$

and coboundaries as

$$
(dX)(g)=g\cdot X-X.
$$

The topology on cochains is never suppressed: $Z^i$ and $H^i$ always mean continuous cochains for the indicated topological coefficient module.

## 2. Lifts and strict equivalence

### 2.1 Why reduction includes an identification

Let $A\in\operatorname{Art}_k$. Reduction entry by entry gives

$$
\operatorname{GL}_d(A)\longrightarrow\operatorname{GL}_d(k).
$$

A **lift of $\bar\rho$ to $A$** is a continuous homomorphism

$$
\rho_A:G\longrightarrow\operatorname{GL}_d(A)
$$

whose reduction is exactly $\bar\rho$. The word exactly matters. We have fixed not merely the isomorphism class of the special-fiber representation, but also its coordinates in the chosen residual basis.

Intrinsically, a lift is a free $A$-module $V_A$ of rank $d$ with continuous $A$-linear $G$-action, together with a $G$-equivariant identification

$$
V_A\otimes_Ak\xrightarrow{\sim}k^d
$$

with the residual module. Choosing an $A$-basis lifting the fixed basis of $k^d$ turns this intrinsic object into the displayed matrix homomorphism. Different lifting bases lead to the equivalence relation below.

The freeness requirement is part of the problem. Over a local ring, a finite projective module is free, but an arbitrary finite module reducing to $k^d$ need not be flat or free. Allowing such modules would introduce degenerations of the underlying module as well as deformations of its $G$-action.

### 2.2 The congruence subgroup

Define

$$
\Gamma_A=\ker\bigl(\operatorname{GL}_d(A)\to
\operatorname{GL}_d(k)\bigr).
$$

Every element of $\Gamma_A$ has the form $1+X$ with $X\in M_d(\mathfrak m_A)$. It is invertible because $X$ is nilpotent. The group $\Gamma_A$ is the group of changes of an $A$-basis that induce the identity on the fixed residual basis.

Two lifts $\rho_A$ and $\rho_A'$ are **strictly equivalent** if

$$
\rho_A'(g)=P\rho_A(g)P^{-1}
\qquad(g\in G)
$$

for some $P\in\Gamma_A$. This is an equivalence relation, and continuity is preserved because conjugation by a fixed matrix is continuous.

Why not quotient by all of $\operatorname{GL}_d(A)$? If $P$ reduces to $\bar P\in\operatorname{GL}_d(k)$, then the reduction of $P\rho_AP^{-1}$ is

$$
\bar P\bar\rho\bar P^{-1},
$$

which equals $\bar\rho$ only when $\bar P$ centralizes its image. Even in that case, $\bar P$ changes the chosen identification of the special fiber. Arbitrary conjugacy therefore forgets part of the deformation datum. Strict conjugacy is exactly isomorphism inducing the identity under the chosen residual identification.

### 2.3 A counterexample to arbitrary conjugacy

Let

$$
\bar\rho(g)=
\begin{pmatrix}\chi_1(g)&0\\0&\chi_2(g)\end{pmatrix}
$$

with distinct characters. The permutation matrix

$$
S=\begin{pmatrix}0&1\\1&0\end{pmatrix}
$$

interchanges the two characters. Conjugating by a lift of $S$ changes the residual representation to $\chi_2\oplus\chi_1$, not to the fixed matrix-valued map $\bar\rho$. Those two residual modules are isomorphic, but they are not the same based residual object.

At the opposite extreme, if $\bar\rho$ is scalar, every $\bar P$ centralizes it. Quotienting by all matrices would then identify lifts through every residual change of basis, while strict equivalence retains the chosen identification with $k^d$. The discrepancy is largest precisely when the residual centralizer is large.

### 2.4 Base change of lifts

Let $f:A\to B$ be a morphism in the coefficient category. Applying $f$ entrywise defines

$$
f_*\rho_A:G\longrightarrow\operatorname{GL}_d(B).
$$

It is continuous, reduces to $\bar\rho$, and respects composition of coefficient maps. If $\rho_A'$ is obtained from $\rho_A$ by $P\in\Gamma_A$, then $f_*\rho_A'$ is obtained from $f_*\rho_A$ by $f(P)\in\Gamma_B$. Thus base change descends to strict-equivalence classes.

This is the source of variance: coefficient maps point forward,

$$
A\longrightarrow B
\quad\Longrightarrow\quad
\{
\text{deformations over }A
\}\longrightarrow
\{
\text{deformations over }B
\}.
$$

The resulting deformation functors are covariant on coefficient rings, even though the corresponding geometric pullback reverses arrows of affine spectra.

### 2.5 Continuous lifts over complete rings

Suppose $R$ is complete Noetherian local with residue field $k$. A continuous lift

$$
\rho_R:G\to\operatorname{GL}_d(R)
$$

gives compatible lifts $\rho_n$ over $R/\mathfrak m_R^n$. Conversely, compatible $\rho_n$ define a homomorphism into

$$
\operatorname{GL}_d(R)\simeq
\varprojlim_n\operatorname{GL}_d(R/\mathfrak m_R^n).
$$

The resulting map is continuous: the inverse image of each principal congruence subgroup is the kernel of the continuous finite-level map $\rho_n$, hence is open. Strict equivalence at the complete level requires a single $P\in1+M_d(\mathfrak m_R)$, not unrelated conjugators at every finite level. Compatible finite-level conjugators produce such a $P$; arbitrary ones need not.

This finite-level description does not assert that every compatible family is universal, nor that a universal complete ring exists. It only translates continuity and completeness.

## 3. Unframed and framed deformation functors

### 3.1 The unframed set-valued functor

The **unframed deformation functor** of $\bar\rho$ is

$$
D_{\bar\rho}:\operatorname{Art}_{\mathcal O}\longrightarrow\mathbf{Sets},
$$

$$
D_{\bar\rho}(A)=
\{\text{continuous lifts of $\bar\rho$ to $A$}\}/\text{strict equivalence}.
$$

If no coefficient base is needed, replace $\operatorname{Art}_{\mathcal O}$ by $\operatorname{Art}_k$. Base change from Section 2.4 makes this a covariant functor. At the terminal ring $k$ there is one element, represented by $\bar\rho$ itself.

Calling $D_{\bar\rho}$ set-valued makes a deliberate loss of information. A lift can have strict automorphisms, and passing to equivalence classes forgets them. This loss is harmless for defining the set of deformations but crucial for representability questions and for gluing across coefficient fiber products. We will keep the underlying groupoid visible even while studying the set-valued functor.

### 3.2 The deformation groupoid

For each $A$, define a groupoid $\mathcal D_{\bar\rho}(A)$ whose objects are lifts and whose arrows $\rho\to\rho'$ are matrices $P\in\Gamma_A$ satisfying

$$
\rho'(g)=P\rho(g)P^{-1}.
$$

Composition is matrix multiplication. Then

$$
D_{\bar\rho}(A)=\pi_0\mathcal D_{\bar\rho}(A).
$$

The automorphism group of a lift is exactly

$$
\operatorname{Aut}^{\mathrm{str}}_A(\rho)
=\Gamma_A\cap Z_{\operatorname{GL}_d(A)}(\rho(G)).
$$

This formula is more precise than saying that automorphisms are “controlled by the centralizer.” It gives the exact stabilizer. On a square-zero kernel its infinitesimal part will become $H^0$.

A map $A\to B$ sends an arrow $P$ to its image in $\Gamma_B$, so $A\mapsto\mathcal D_{\bar\rho}(A)$ is a functor to groupoids. Passing to connected components yields $D_{\bar\rho}$, but passage to connected components need not preserve every fiber product. That distinction is one reason automorphisms matter in the representability theory of the next book.

### 3.3 Why a framing removes a quotient

A **framing** of an intrinsic lift $V_A$ is an ordered $A$-basis whose reduction is the fixed ordered basis of $k^d$. Once this basis is chosen, the lift is a definite matrix homomorphism. An isomorphism of framed lifts must preserve the basis and is therefore the identity.

Accordingly, the **framed deformation functor** is

$$
D_{\bar\rho}^{\square}(A)
=\{\rho_A:G\to\operatorname{GL}_d(A)
\text{ continuous}:\rho_A\bmod\mathfrak m_A=\bar\rho\}.
$$

There is no conjugacy quotient. The square is a mnemonic for a chosen frame, not an exponent. Coefficient base change again acts entrywise and makes $D_{\bar\rho}^{\square}$ covariant.

The forgetful map

$$
D_{\bar\rho}^{\square}(A)\longrightarrow D_{\bar\rho}(A)
$$

is surjective: every unframed class has a matrix representative. Its fibers are orbits of $\Gamma_A$, not copies of $\Gamma_A$.

### 3.4 Frames, orbits, and stabilizers

The congruence group acts on framed lifts by conjugation. For a fixed lift $\rho$, the orbit-stabilizer description gives its fiber over $[\rho]$ as the homogeneous set

$$
\Gamma_A/\operatorname{Aut}^{\mathrm{str}}_A(\rho).
$$

The action is rarely free. Every scalar matrix in $\Gamma_A$ centralizes every representation. Thus if $\mathfrak m_A\neq0$, the subgroup

$$
(1+\mathfrak m_A)I_d
$$

already lies in every stabilizer. Nonscalar residual endomorphisms can enlarge the stabilizer further.

This corrects a tempting but false slogan: a framed deformation is not an unframed deformation plus a freely chosen element of $\Gamma_A$. It is an unframed lift together with a frame, and the same framed matrix can arise from different changes of frame whenever the lift has automorphisms.

**Worked scalar example.** Suppose $\rho(g)=\chi(g)I_d$ over $A$. Then all of $\Gamma_A$ centralizes $\rho(G)$. Its conjugacy orbit is a single point. The forgetful fiber above $[\rho]$ therefore has one matrix representation, even though the intrinsic scalar module has many lifting bases. Those bases are all related by automorphisms of the $G$-module, so they define the same framed matrix after coordinates are used. Confusing bases as raw lists with based matrix objects obscures this stabilizer cancellation.

### 3.5 Residual centralizers and the first warning

Write

$$
C_{\bar\rho}=Z_{\operatorname{GL}_d(k)}(\bar\rho(G)).
$$

If $\bar\rho$ is absolutely irreducible, Schur's lemma gives $C_{\bar\rho}=k^\times I_d$. The strict stabilizer can still contain all scalar matrices congruent to $1$. Thus absolute irreducibility does not make the framed-to-unframed action free; it makes the residual endomorphism algebra as small as possible.

If $\bar\rho=\chi_1\oplus\chi_2$ with distinct characters, the residual centralizer contains all diagonal matrices and has dimension two as an algebra. If $\chi_1=\chi_2$, it is all of $M_2(k)$. If $\bar\rho$ is a nonsplit self-extension of a character, its centralizer is typically the two-dimensional algebra generated by the identity and the nilpotent extension operator. These differences reappear as $H^0$ terms in tangent dimensions.

### 3.6 A useful diagram of distinctions

The four levels should not be merged:

$$
\begin{array}{c|c|c}
\text{level}&\text{object retained}&\text{automorphisms retained}\\ \hline
\text{framed set}&\text{matrix lift}&\text{none as arrows}\\
\text{deformation groupoid}&\text{lift with residual identification}&\text{strict centralizer}\\
\text{unframed set}&\text{strict-equivalence class}&\text{forgotten}\\
\text{arbitrary conjugacy quotient}&\text{residual basis also forgotten}&\text{too coarse here}
\end{array}
$$

Framed functors are often technically cleaner because they retain equations rather than orbit classes. Unframed functors express the intrinsic deformation problem more economically. Neither is a substitute for the other.

## 4. Determinants and constrained deformations

### 4.1 Why the determinant must be lifted first

The determinant of $\bar\rho$ is a continuous character

$$
\det\bar\rho:G\to k^\times.
$$

To demand a fixed determinant over every $A$ requires more than repeating this residual character: one needs a compatible lift of it to the coefficient base. Fix a continuous character

$$
\delta:G\longrightarrow\mathcal O^\times
$$

whose reduction is $\det\bar\rho$. For $A\in\operatorname{Art}_{\mathcal O}$, let

$$
\delta_A:G\to A^\times
$$

be its composite with $\mathcal O\to A$. Then $\delta_B=f\circ\delta_A$ for every coefficient map $f:A\to B$. This compatibility is what makes fixed determinant a subfunctor rather than an unrelated condition at each ring.

In a residue-only category one may instead specify a natural family $(\delta_A)_A$, but such a family is extra data and may not exist canonically. Mixed characteristic is the main reason not to pretend that $\det\bar\rho$ itself takes values in every coefficient ring.

### 4.2 Fixed-determinant functors

Define

$$
D_{\bar\rho}^{\delta}(A)
=\{[\rho_A]\in D_{\bar\rho}(A):\det\rho_A=\delta_A\}
$$

and

$$
D_{\bar\rho}^{\square,\delta}(A)
=\{\rho_A\in D_{\bar\rho}^{\square}(A):
\det\rho_A=\delta_A\}.
$$

Conjugation preserves determinant, so the first definition is independent of the representative. Base change preserves the condition by construction. The strict-equivalence relation is not changed: every strict conjugator is allowed, not only one of determinant one. Restricting conjugators would define a different moduli problem, one with a chosen volume framing.

The fixed-determinant groupoid is the full subgroupoid on objects of determinant $\delta_A$. Its automorphism group remains

$$
\Gamma_A\cap Z_{\operatorname{GL}_d(A)}(\rho(G)),
$$

not its intersection with $\operatorname{SL}_d(A)$.

### 4.3 Determinant linearization

For a square-zero ideal $I$ and $X\in M_d(I)$,

$$
\det(1+X)=1+\operatorname{tr}(X).
$$

Indeed the determinant expansion is the sum over permutations. The identity permutation contributes $1+\sum_iX_{ii}$, and every other nonconstant contribution contains at least two entries of $I$ and vanishes. Over the dual numbers this reads

$$
\det(1+\epsilon X)=1+\epsilon\operatorname{tr}(X).
$$

The linearized fixed-determinant coefficient module is therefore

$$
\operatorname{ad}^0\bar\rho
=\ker\bigl(\operatorname{tr}:\operatorname{ad}\bar\rho\to k\bigr).
$$

Trace is invariant under conjugation, so this is a $G$-submodule. The map $\operatorname{tr}:M_d(k)\to k$ is always surjective: the matrix $E_{11}$ has trace one.

### 4.4 When trace zero splits off

If $\operatorname{char}k$ does not divide $d$, then

$$
\operatorname{ad}\bar\rho
=kI_d\oplus\operatorname{ad}^0\bar\rho,
$$

because $X$ decomposes as

$$
X=\frac{\operatorname{tr}X}{d}I_d+
\left(X-\frac{\operatorname{tr}X}{d}I_d\right).
$$

This is a $G$-equivariant decomposition. It separates scalar determinant variation from trace-zero variation and consequently splits cohomology in every degree.

If $\operatorname{char}k$ divides $d$, then $\operatorname{tr}(I_d)=0$. The scalar line lies inside $\operatorname{ad}^0\bar\rho$, no scalar projection exists, and the displayed direct sum is false. This affects more than notation: scalar infinitesimal automorphisms survive within the trace-zero module, and fixed-determinant tangent classes require a more careful quotient. Chapter 7 will derive the exact formula rather than subtracting a scalar direction by habit.

### 4.5 A characteristic-two warning in dimension two

Let $d=2$ and $\operatorname{char}k=2$. Then

$$
\operatorname{ad}^0\bar\rho
=\left\{
\begin{pmatrix}a&b\\c&a\end{pmatrix}:a,b,c\in k
\right\},
$$

which contains $I_2$. For an absolutely irreducible $\bar\rho$, the only invariant endomorphisms may be scalars, but then

$$
H^0(G,\operatorname{ad}^0\bar\rho)=kI_2
$$

rather than zero. Any fixed-determinant dimension formula asserting that absolute irreducibility kills $H^0(\operatorname{ad}^0)$ is therefore wrong in characteristic two.

The trace pairing also becomes degenerate on $\operatorname{ad}^0$ in this case: the scalar line is orthogonal to all trace-zero matrices. Local duality formulas that identify $(\operatorname{ad}^0)^*$ with $\operatorname{ad}^0$ need the same hypothesis that $d$ be invertible in $k$, or must replace the module by the correct dual quotient.

## 5. Dual numbers and first-order matrices

### 5.1 Why the dual numbers isolate a derivative

The smallest coefficient ring with a nonzero nilpotent direction is

$$
k[\epsilon]=k[\epsilon]/(\epsilon^2).
$$

It is an object of $\operatorname{Art}_{\mathcal O}$ through the residue map $\mathcal O\to k\hookrightarrow k[\epsilon]$. Its maximal ideal is $k\epsilon$. A lift over this ring retains one linear variation and discards every product of variations. Consequently the value of a deformation functor on $k[\epsilon]$ is its tangent set; in the present problem it will carry a canonical $k$-vector-space structure.

Every matrix reducing to $\bar\rho(g)$ has a unique expression

$$
\rho_\epsilon(g)=(1+\epsilon c(g))\bar\rho(g)
$$

with $c(g)\in M_d(k)$. We place the infinitesimal factor on the left. One could place it on the right, but then the cocycle formula and conjugation signs would change form. Fixing the convention before calculating prevents a silent left-right mismatch.

The map $c:G\to M_d(k)$ is continuous. Indeed

$$
c(g)=\epsilon^{-1}\bigl(\rho_\epsilon(g)\bar\rho(g)^{-1}-1\bigr)
$$

is obtained from continuous maps into finite discrete sets. Conversely, any continuous $c$ produces a continuous matrix-valued map by the displayed formula.

### 5.2 Deriving the cocycle equation

We now impose multiplicativity rather than cite the answer. For $g,h\in G$,

$$
\begin{aligned}
\rho_\epsilon(g)\rho_\epsilon(h)
&=(1+\epsilon c(g))\bar\rho(g)
  (1+\epsilon c(h))\bar\rho(h)\\
&=(1+\epsilon c(g))
  (1+\epsilon\bar\rho(g)c(h)\bar\rho(g)^{-1})
  \bar\rho(gh)\\
&=(1+\epsilon(c(g)+g\cdot c(h)))\bar\rho(gh).
\end{aligned}
$$

The last equality uses $\epsilon^2=0$. Comparing with

$$
\rho_\epsilon(gh)=(1+\epsilon c(gh))\bar\rho(gh)
$$

shows that $\rho_\epsilon$ is a homomorphism exactly when

$$
c(gh)=c(g)+g\cdot c(h).
$$

This is precisely the continuous $1$-cocycle equation for $\operatorname{ad}\bar\rho$. Normalization follows automatically: setting $g=h=1$ gives $c(1)=0$.

We have therefore obtained a canonical bijection

$$
D_{\bar\rho}^{\square}(k[\epsilon])
\xrightarrow{\sim}
Z^1(G,\operatorname{ad}\bar\rho).
$$

Addition and scalar multiplication of cocycles transport to a vector-space structure on the framed tangent set. This structure is not matrix multiplication of lifts; it is the linear structure exposed after the common residual factor has been removed.

### 5.3 A one-generator calculation

Suppose $G=C_m=\langle\sigma\rangle$ and let $T$ be the action of $\sigma$ on $\operatorname{ad}\bar\rho$. A cocycle is determined by $X=c(\sigma)$. Repeated use of the cocycle equation gives

$$
c(\sigma^r)=(1+T+\cdots+T^{r-1})X.
$$

The relation $\sigma^m=1$ imposes

$$
(1+T+\cdots+T^{m-1})X=0.
$$

Thus the framed tangent vectors are exactly the kernel of the norm operator on the adjoint module. If $\bar\rho$ is trivial, then $T=1$ and the condition is $mX=0$. When $\operatorname{char}k$ divides $m$, every $X$ is allowed; when $m$ is invertible in $k$, only $X=0$ is allowed. This simple example already shows that tangent dimensions depend on the pro-order of $G$ relative to the coefficient characteristic.

### 5.4 Continuity cannot be recovered afterward

For trivial residual action, the cocycle equation says that $c:G\to M_d(k)$ is a group homomorphism to the additive group. The correct space is

$$
\operatorname{Hom}_{\mathrm{cts}}(G,M_d(k)),
$$

not the group of all abstract homomorphisms. Since the target is finite discrete, continuity is equivalent to open kernel. For a profinite group with discontinuous finite quotients, the abstract tangent set would therefore be strictly larger.

In arithmetic examples the continuity condition means that a first-order deformation is detected on some finite quotient of $G$. The quotient may depend on the cocycle; there need not be one finite quotient that controls every tangent direction unless an additional finiteness hypothesis is imposed.

## 6. Strict conjugation and cohomology

### 6.1 Linearizing a strict change of basis

Every strict conjugator over $k[\epsilon]$ has the form

$$
P=1+\epsilon X,
\qquad P^{-1}=1-\epsilon X,
$$

with $X\in\operatorname{ad}\bar\rho$. Conjugating our left-normalized lift gives

$$
\begin{aligned}
P\rho_\epsilon(g)P^{-1}
&=(1+\epsilon X)(1+\epsilon c(g))\bar\rho(g)(1-\epsilon X)\\
&=(1+\epsilon(X+c(g)-g\cdot X))\bar\rho(g).
\end{aligned}
$$

Thus the new cocycle is

$$
c'(g)=c(g)+X-g\cdot X=c(g)-(dX)(g).
$$

The minus sign comes from conjugating by $P$ on the left under our convention. Since the subgroup of coboundaries is closed under negation, the quotient is unaffected, but the calculation matters when correcting an obstruction later.

Conversely, if $c'-c=-dX$, the corresponding lifts are conjugate by $1+\epsilon X$. Therefore strict equivalence is exactly quotienting cocycles by coboundaries.

### 6.2 The canonical tangent-space theorem

**Theorem (unframed tangent space).** There is a canonical $k$-linear isomorphism

$$
D_{\bar\rho}(k[\epsilon])
\xrightarrow{\sim}
H^1(G,\operatorname{ad}\bar\rho).
$$

**Proof strategy.** Factor every lift uniquely into its residual matrix and an infinitesimal left factor. Multiplicativity becomes the cocycle equation, while strict conjugation becomes subtraction of a coboundary. These two calculations also show that the construction and its inverse are natural.

**Proof.** Section 5.2 identifies lifts with continuous cocycles. Section 6.1 shows that two such lifts are strictly equivalent precisely when their cocycles differ by an element of $B^1(G,\operatorname{ad}\bar\rho)$. Hence strict-equivalence classes are $Z^1/B^1=H^1$. Addition and scalar multiplication descend from cochains, giving a $k$-linear bijection.

For a coefficient map induced by a field extension compatible with the residual representation, the matrix expansion commutes with scalar extension. For a continuous homomorphism of groups, it commutes with pullback of cocycles. Hence the isomorphism is canonical relative to the fixed residual representation and basis. $\square$

This theorem does not use representability and does not construct a universal ring. It is a direct classification over one test ring.

### 6.3 Framed tangent vectors and change-of-frame directions

The framed tangent space is

$$
t_{\bar\rho}^{\square}
=D_{\bar\rho}^{\square}(k[\epsilon])
=Z^1(G,\operatorname{ad}\bar\rho).
$$

Infinitesimal changes of frame produce $B^1$. Infinitesimal matrices that produce no change are precisely the invariants. Thus there is an exact sequence

$$
0\longrightarrow H^0(G,\operatorname{ad}\bar\rho)
\longrightarrow\operatorname{ad}\bar\rho
\xrightarrow{d}Z^1(G,\operatorname{ad}\bar\rho)
\longrightarrow H^1(G,\operatorname{ad}\bar\rho)
\longrightarrow0.
$$

If one follows the actual conjugation formula, the middle arrow is $-d$; replacing it by $d$ gives the same image and makes the standard cochain sequence visible. The kernel is the residual centralizer, the image is the change-of-frame space, and the cokernel is the unframed tangent space.

Assuming finite dimensions and writing $h^i(M)=\dim_kH^i(G,M)$, we obtain

$$
\dim_kB^1(G,\operatorname{ad}\bar\rho)
=d^2-h^0(\operatorname{ad}\bar\rho),
$$

and

$$
\boxed{
\dim_k Z^1(G,\operatorname{ad}\bar\rho)
=h^1(\operatorname{ad}\bar\rho)+d^2-h^0(\operatorname{ad}\bar\rho).
}
$$

The correction is $d^2-h^0$, not $d^2$. Infinitesimal centralizers do not move the framed matrix.

### 6.4 Absolutely irreducible and scalar examples

If $\bar\rho$ is absolutely irreducible, then

$$
h^0(\operatorname{ad}\bar\rho)=1,
$$

so

$$
\dim t_{\bar\rho}^{\square}
=h^1(\operatorname{ad}\bar\rho)+d^2-1.
$$

The missing direction is scalar conjugation, which changes nothing.

If $\bar\rho$ is scalar, the entire adjoint module is fixed, so $h^0=d^2$ and $B^1=0$. Framed and unframed tangent spaces then coincide. This does not say framed and unframed functors coincide at all orders. It says only that conjugation has zero derivative at a scalar residual point. At thicker order, a noncentral first-order matrix in a lift can interact with a change of frame and produce nontrivial higher-order conjugation.

This is an instructive failure of tangent information to determine the nonlinear quotient.

### 6.5 Tangent spaces are not sets of generators

Even when $H^1$ is finite-dimensional, the dimension of the tangent space alone does not imply that a deformation functor is represented by a power-series ring in that many variables. Tangent vectors see first-order choices. Relations and lifting failures live at higher order, and automorphisms can prevent the set-valued functor from preserving coefficient fiber products.

The tangent theorem is therefore an input to representability, not a representability theorem. Book 22 will study when a functor admits a hull or a representing ring. Here we retain only the unconditional cohomological calculation.

## 7. Fixed-determinant tangent theory

### 7.1 Framed fixed determinant

Let $\delta$ be the fixed determinant character of Chapter 4. Over the dual numbers, write

$$
\rho_\epsilon(g)=(1+\epsilon c(g))\bar\rho(g).
$$

Because $\delta_{k[\epsilon]}$ is obtained from $\delta$ through the residue map, it has no $\epsilon$-variation. Hence

$$
\det\rho_\epsilon(g)=\delta_{k[\epsilon]}(g)
$$

is equivalent to

$$
\operatorname{tr}c(g)=0
\qquad(g\in G).
$$

The cocycle already takes values in the $G$-submodule $\operatorname{ad}^0\bar\rho$. Thus

$$
D_{\bar\rho}^{\square,\delta}(k[\epsilon])
\cong Z^1(G,\operatorname{ad}^0\bar\rho).
$$

This statement is valid in every characteristic.

### 7.2 Which coboundaries must be divided out

For the unframed fixed-determinant functor, every strict conjugator $1+\epsilon X$ with $X\in\operatorname{ad}\bar\rho$ is allowed. Its change is $-dX$. Trace satisfies

$$
\operatorname{tr}(dX)(g)
=\operatorname{tr}(g\cdot X-X)=0,
$$

so $dX$ is an $\operatorname{ad}^0$-valued cocycle even when $X$ itself is not trace zero. Consequently the general formula is

$$
\boxed{
D_{\bar\rho}^{\delta}(k[\epsilon])
\cong
\frac{Z^1(G,\operatorname{ad}^0\bar\rho)}
{d(\operatorname{ad}\bar\rho)}.
}
$$

Equivalently, trace on cocycles induces

$$
D_{\bar\rho}^{\delta}(k[\epsilon])
\cong
\ker\left(
H^1(G,\operatorname{ad}\bar\rho)
\xrightarrow{\operatorname{tr}}
H^1(G,k)
\right),
$$

where $k$ has trivial $G$-action. The two descriptions are the same because $B^1(G,k)=0$.

This quotient is the precise answer in all characteristics. It is often abbreviated too quickly as $H^1(G,\operatorname{ad}^0\bar\rho)$.

When the spaces are finite-dimensional, the formulas valid in every characteristic are

$$
\dim_k t_{\bar\rho}^{\square,\delta}
=h^1(\operatorname{ad}^0\bar\rho)
+d^2-1-h^0(\operatorname{ad}^0\bar\rho)
$$

and

$$
\dim_k t_{\bar\rho}^{\delta}
=h^1(\operatorname{ad}^0\bar\rho)-1
-h^0(\operatorname{ad}^0\bar\rho)
+h^0(\operatorname{ad}\bar\rho).
$$

The second equality subtracts the dimension $d^2-h^0(\operatorname{ad})$ of $d(\operatorname{ad})$ from the framed fixed-determinant dimension. It specializes to $h^1(\operatorname{ad}^0)$ precisely when the invariant terms differ by one, as they do under the trace splitting.

### 7.3 The familiar formula when $d$ is invertible

Assume $\operatorname{char}k\nmid d$. For every $X\in\operatorname{ad}\bar\rho$, subtracting

$$
\frac{\operatorname{tr}X}{d}I_d
$$

produces a trace-zero matrix with the same coboundary, since scalar matrices are invariant. Hence

$$
d(\operatorname{ad}\bar\rho)=d(\operatorname{ad}^0\bar\rho),
$$

and the general formula simplifies canonically to

$$
\boxed{
D_{\bar\rho}^{\delta}(k[\epsilon])
\cong H^1(G,\operatorname{ad}^0\bar\rho).
}
$$

The framed dimension is then

$$
\dim Z^1(G,\operatorname{ad}^0\bar\rho)
=h^1(\operatorname{ad}^0\bar\rho)
+(d^2-1)-h^0(\operatorname{ad}^0\bar\rho).
$$

If $\bar\rho$ is absolutely irreducible, the trace-zero invariant space is zero, and the framed fixed-determinant tangent space has dimension $h^1(\operatorname{ad}^0)+d^2-1$.

### 7.4 What changes when the characteristic divides $d$

Suppose $\operatorname{char}k\mid d$. The exact coefficient sequence

$$
0\longrightarrow\operatorname{ad}^0\bar\rho
\longrightarrow\operatorname{ad}\bar\rho
\xrightarrow{\operatorname{tr}}k
\longrightarrow0
$$

still exists, but it need not split as $G$-modules. Its long exact sequence begins

$$
\begin{aligned}
0&\to H^0(\operatorname{ad}^0)
\to H^0(\operatorname{ad})
\xrightarrow{\operatorname{tr}} k
\xrightarrow{\partial}H^1(\operatorname{ad}^0)\\
&\to H^1(\operatorname{ad})
\xrightarrow{\operatorname{tr}}H^1(k).
\end{aligned}
$$

Therefore

$$
D_{\bar\rho}^{\delta}(k[\epsilon])
\cong
H^1(G,\operatorname{ad}^0\bar\rho)/\operatorname{im}\partial.
$$

The connecting class $\partial(1)$ can be described explicitly. Choose any $X\in M_d(k)$ with $\operatorname{tr}X=1$. Then

$$
\partial(1)(g)=g\cdot X-X.
$$

It is trace zero, and changing $X$ changes it by an $\operatorname{ad}^0$-coboundary. This is exactly the extra change-of-frame direction arising from a conjugator whose infinitesimal matrix has nonzero trace.

If some invariant endomorphism has trace one, then $\partial=0$ and the familiar $H^1(\operatorname{ad}^0)$ formula happens to remain true. For an absolutely irreducible representation when $\operatorname{char}k\mid d$, every invariant is scalar and has trace zero, so the map $H^0(\operatorname{ad})\to k$ is zero and $\partial$ is injective. In that case the fixed-determinant tangent space is smaller than $H^1(\operatorname{ad}^0)$ by one dimension.

### 7.5 Volume-framed is a different functor

One could modify strict equivalence by allowing only conjugators of determinant one. Infinitesimally that would divide by $d(\operatorname{ad}^0)$ and would indeed give $H^1(\operatorname{ad}^0)$ in every characteristic. But that moduli problem retains a volume form on the frame. It is not the ordinary fixed-determinant deformation functor, because determinant of the representation is invariant under every conjugator, not merely special-linear ones.

The distinction disappears when $d$ is invertible in $k$, since every infinitesimal change of frame has the same coboundary as a trace-zero one. It is genuine when the residue characteristic divides $d$.

## 8. First examples

### 8.1 One-dimensional characters

Let $d=1$ and write $\bar\chi:G\to k^\times$. Conjugation on $\operatorname{ad}\bar\chi=k$ is trivial, and $\operatorname{GL}_1(A)$ is abelian. Strict equivalence does nothing at every order, not merely to first order. Hence

$$
D_{\bar\chi}^{\square}=D_{\bar\chi},
$$

and

$$
D_{\bar\chi}(k[\epsilon])
=H^1(G,k)=\operatorname{Hom}_{\mathrm{cts}}(G,k^+).
$$

Explicitly, a first-order character is

$$
\chi_\epsilon(g)=(1+\epsilon c(g))\bar\chi(g),
$$

and commutativity removes the twist from the cocycle equation.

If the determinant is fixed, then in dimension one it fixes the entire representation. The fixed-determinant deformation functor is the one-point functor whenever the chosen determinant lift exists. Its tangent space is zero because $\operatorname{ad}^0=0$. This is a useful consistency check.

### 8.2 The trivial residual representation

Suppose $\bar\rho(g)=I_d$ for all $g$. Then $G$ acts trivially on $M_d(k)$, so

$$
Z^1(G,\operatorname{ad}\bar\rho)
=\operatorname{Hom}_{\mathrm{cts}}(G,M_d(k)^+),
$$

and $B^1=0$. Thus framed and unframed tangent spaces coincide and

$$
t_{\bar\rho}=t_{\bar\rho}^{\square}
=\operatorname{Hom}_{\mathrm{cts}}(G,k^+)\otimes_kM_d(k).
$$

Take $G=C_p$ and $\operatorname{char}k=p$. Sending a generator to any $X\in M_d(k)$ defines a cocycle, so the tangent dimension is $d^2$. If $G=C_m$ with $p\nmid m$, the tangent space is zero.

The vanishing of $B^1$ does not mean the strict action is free; it means its derivative is zero. In fact every infinitesimal conjugator stabilizes the trivial residual representation. This example separates stabilizers from orbit directions as sharply as possible.

### 8.3 Split reducible representations

Let

$$
\bar\rho=\chi_1\oplus\chi_2.
$$

With respect to the splitting, the adjoint module decomposes as

$$
\operatorname{ad}\bar\rho
\simeq k\oplus k\oplus
k(\chi_1\chi_2^{-1})\oplus
k(\chi_2\chi_1^{-1}).
$$

The first two summands are diagonal. The upper-right matrix $E_{12}$ transforms by $\chi_1\chi_2^{-1}$, and the lower-left matrix $E_{21}$ by the inverse ratio. Therefore

$$
\begin{aligned}
H^1(G,\operatorname{ad}\bar\rho)
\simeq{}&H^1(G,k)^{\oplus2}\\
&\oplus H^1(G,k(\chi_1\chi_2^{-1}))
\oplus H^1(G,k(\chi_2\chi_1^{-1})).
\end{aligned}
$$

The diagonal terms deform the two characters. The upper-right term deforms extensions of the second character by the first; the lower-left term moves in the opposite extension direction. A deformation of the full representation may contain both off-diagonal directions, so it need not remain upper triangular. Imposing preservation of a chosen line is an additional deformation condition, not part of the ambient functor.

If $\chi_1\neq\chi_2$, then $h^0(\operatorname{ad})=2$ provided neither ratio is trivial. If they coincide, all four matrix directions are invariant. The framed dimension jumps accordingly.

### 8.4 A worked upper-triangular cocycle

Let

$$
\bar\rho(g)=
\begin{pmatrix}\chi_1(g)&0\\0&\chi_2(g)\end{pmatrix}
$$

and choose a cocycle supported in the upper-right line:

$$
c(g)=\begin{pmatrix}0&u(g)\\0&0\end{pmatrix}.
$$

Then

$$
g\cdot c(h)=
\begin{pmatrix}
0&\chi_1(g)\chi_2(g)^{-1}u(h)\\0&0
\end{pmatrix},
$$

so the cocycle equation becomes

$$
u(gh)=u(g)+\chi_1(g)\chi_2(g)^{-1}u(h).
$$

The lifted matrix is

$$
\rho_\epsilon(g)=
\begin{pmatrix}
\chi_1(g)&\epsilon u(g)\chi_2(g)\\
0&\chi_2(g)
\end{pmatrix}.
$$

Conjugation by $1+\epsilon xE_{12}$ changes

$$
u(g)\longmapsto
u(g)+x-\chi_1(g)\chi_2(g)^{-1}x,
$$

the negative of the usual coboundary. Hence equivalence classes of upper-right first-order extensions lie in $H^1(G,k(\chi_1\chi_2^{-1}))$ exactly as the module decomposition predicts.

### 8.5 Nonsplit reducible representations

For a nonsplit extension

$$
0\to k(\chi_1)\to V\to k(\chi_2)\to0,
$$

the underlying vector space still has a filtration by the stable line, but $\operatorname{ad}V$ need not split into four character modules. It has a filtration whose associated graded has those four factors. Cohomology of the associated graded does not in general equal cohomology of the module: connecting maps encode interaction with the residual extension class.

In the special case of a nonsplit self-extension of a character, one may twist away the character and write

$$
\bar\rho(g)=
\begin{pmatrix}1&u(g)\\0&1\end{pmatrix}
$$

with nonzero $[u]\in H^1(G,k)$. A direct matrix calculation shows that the centralizer consists of matrices $aI+bE_{12}$, assuming the values of $u$ span $k$. Thus $h^0(\operatorname{ad})=2$, neither the value $4$ of the split scalar representation nor the value $1$ of an absolutely irreducible one.

### 8.6 Absolutely irreducible residual representations

If $\bar\rho$ is absolutely irreducible, then

$$
H^0(G,\operatorname{ad}\bar\rho)=kI_d.
$$

Its unframed tangent dimension is $h^1(\operatorname{ad})$, while its framed tangent dimension is

$$
h^1(\operatorname{ad})+d^2-1.
$$

When $\operatorname{char}k\nmid d$ and the determinant is fixed, $H^0(G,\operatorname{ad}^0)=0$, so the corresponding dimensions are

$$
h^1(\operatorname{ad}^0)
\quad\text{and}\quad
h^1(\operatorname{ad}^0)+d^2-1.
$$

Absolute irreducibility simplifies the centralizer, but it says nothing by itself about $H^1$ or $H^2$. An absolutely irreducible representation can have many deformations or serious obstructions.

## 9. Lifting across square-zero extensions

### 9.1 Why multiplication fails by a two-variable defect

Let

$$
0\longrightarrow I\longrightarrow A'
\xrightarrow{\pi}A\longrightarrow0
$$

be a surjection in the coefficient category with $I^2=0$. Suppose a lift

$$
\rho_A:G\to\operatorname{GL}_d(A)
$$

is given. Each individual matrix $\rho_A(g)$ lifts to an invertible matrix over $A'$: lift its entries arbitrarily, and note that a matrix whose determinant reduces to a unit has unit determinant. But independently lifted matrices need not multiply correctly.

Choose a continuous set-theoretic map

$$
\widetilde\rho:G\to\operatorname{GL}_d(A')
$$

lifting $\rho_A$ and satisfying $\widetilde\rho(1)=1$. Such a choice exists in our Artinian setting. The image of $\rho_A$ is finite, choose one matrix lift for each image value, and compose with $\rho_A$; this is continuous because its fibers are open.

The failure of multiplicativity depends on a pair $(g,h)$, so it should be a $2$-cochain. Define $\kappa(g,h)$ by

$$
1+\kappa(g,h)
=\widetilde\rho(g)\widetilde\rho(h)
\widetilde\rho(gh)^{-1}.
$$

The product reduces to the identity, and the kernel of

$$
\operatorname{GL}_d(A')\to\operatorname{GL}_d(A)
$$

is $1+M_d(I)$. Since $I^2=0$, multiplication in this kernel is additive:

$$
(1+X)(1+Y)=1+X+Y.
$$

Thus $\kappa$ is a continuous normalized $2$-cochain with values in $M_d(I)$.

### 9.2 The correct coefficient module for a square-zero kernel

The $A$-module $I$ is well defined because $I^2=0$: two lifts in $A'$ of the same $a\in A$ act identically on $I$. Conjugation by a lift of $\rho_A(g)$ gives a well-defined action on $M_d(I)$,

$$
g\cdot X=\widetilde\rho(g)X\widetilde\rho(g)^{-1}.
$$

Changing $\widetilde\rho(g)$ by an element of $1+M_d(I)$ does not alter this action, because commutators of two $I$-valued matrices vanish. We may denote the resulting module by

$$
\operatorname{ad}(\rho_A)\otimes_A I.
$$

For a general square-zero extension, the nilpotents of $A$ may act nontrivially on $I$, so this coefficient module need not be obtained from $k$.

If the extension is **small**, meaning $\mathfrak m_{A'}I=0$, then the action of $A'$ on $I$ factors through $k$, and conjugation factors through $\bar\rho$. In that case there is a canonical identification

$$
M_d(I)\simeq\operatorname{ad}\bar\rho\otimes_k I.
$$

This is the setting in which the obstruction group takes its most reusable form.

### 9.3 Associativity produces the cocycle equation

**Proposition.** The defect $\kappa$ is a continuous $2$-cocycle.

**Proof strategy.** Expand the triple product $\widetilde\rho(g)\widetilde\rho(h)\widetilde\rho(r)$ in the two associative orders. Moving an $I$-valued defect past $\widetilde\rho(g)$ introduces exactly the adjoint action. Equality of the two results is the inhomogeneous $2$-cocycle equation.

**Proof.** From the definition,

$$
\widetilde\rho(g)\widetilde\rho(h)
=(1+\kappa(g,h))\widetilde\rho(gh).
$$

Multiplying first on the left gives

$$
\begin{aligned}
(\widetilde\rho(g)\widetilde\rho(h))\widetilde\rho(r)
&=(1+\kappa(g,h))(1+\kappa(gh,r))
\widetilde\rho(ghr)\\
&=(1+\kappa(g,h)+\kappa(gh,r))
\widetilde\rho(ghr).
\end{aligned}
$$

Multiplying first on the right gives

$$
\begin{aligned}
\widetilde\rho(g)(\widetilde\rho(h)\widetilde\rho(r))
&=\widetilde\rho(g)(1+\kappa(h,r))\widetilde\rho(hr)\\
&=(1+g\cdot\kappa(h,r))
(1+\kappa(g,hr))\widetilde\rho(ghr)\\
&=(1+g\cdot\kappa(h,r)+\kappa(g,hr))
\widetilde\rho(ghr).
\end{aligned}
$$

Associativity yields

$$
g\cdot\kappa(h,r)-\kappa(gh,r)
+\kappa(g,hr)-\kappa(g,h)=0,
$$

which is $d\kappa=0$ under the cochain convention of Book 15. Continuity and normalization were built into the choice. $\square$

The proof makes the degree two inevitable: multiplication takes two inputs, and associativity compares its behavior on three inputs.

### 9.4 Independence of provisional matrix lifts

Choose a second normalized system of lifts. It has the form

$$
\widetilde\rho'(g)=(1+b(g))\widetilde\rho(g)
$$

for a continuous normalized $1$-cochain $b:G\to M_d(I)$. A direct calculation gives

$$
\begin{aligned}
\widetilde\rho'(g)\widetilde\rho'(h)
&=(1+b(g))\widetilde\rho(g)
  (1+b(h))\widetilde\rho(h)\\
&=(1+b(g)+g\cdot b(h)+\kappa(g,h))
  \widetilde\rho(gh).
\end{aligned}
$$

Since

$$
\widetilde\rho'(gh)^{-1}
=\widetilde\rho(gh)^{-1}(1-b(gh)),
$$

the new defect is

$$
\kappa'(g,h)
=\kappa(g,h)+b(g)+g\cdot b(h)-b(gh)
=\kappa(g,h)+(db)(g,h).
$$

Therefore the cohomology class

$$
\operatorname{ob}(\rho_A,A'/A)
=[\kappa]\in
H^2\bigl(G,\operatorname{ad}(\rho_A)\otimes_A I\bigr)
$$

is independent of all provisional choices. For a small extension this becomes

$$
\boxed{
\operatorname{ob}(\rho_A,A'/A)
\in H^2(G,\operatorname{ad}\bar\rho)\otimes_k I.
}
$$

The displayed tensor-product identification uses that $I$ is a finite-dimensional trivial $G$-space and that cochains commute with finite direct sums. If $I$ carries additional $G$-action in another problem, one must retain $\operatorname{ad}\bar\rho\otimes_k I$ with that action rather than pull $I$ outside cohomology.

The class also respects strict equivalence of the representation being lifted. If $\rho_A'=P\rho_AP^{-1}$ with $P\in\Gamma_A$, lift $P$ to $\widetilde P\in\Gamma_{A'}$ and conjugate the provisional matrices by $\widetilde P$. Their defect is the conjugate of $\kappa$, under the induced identification of the two adjoint coefficient modules. Hence strictly equivalent representatives have corresponding obstruction classes. This is why the construction belongs naturally to the deformation groupoid, even though its most concrete formula starts from a matrix representative.

Similarly, a morphism between square-zero extension diagrams carries provisional lifts and their defects forward. The induced coefficient map sends the obstruction class upstairs to the obstruction class downstairs. Vanishing is therefore stable under coefficient base change, although a class may become zero after a noninjective map on kernels.

### 9.5 Vanishing is equivalent to existence

**Theorem (lifting criterion).** A continuous lift of the fixed representative $\rho_A$ to $A'$ exists if and only if

$$
\operatorname{ob}(\rho_A,A'/A)=0.
$$

**Proof strategy.** A genuine representation has zero defect, proving necessity. For sufficiency, write the defect as a coboundary and correct each provisional matrix by the negative cochain. The sign is checked against Section 9.4.

**Proof.** If $\rho_{A'}$ is a genuine lift, choosing $\widetilde\rho=\rho_{A'}$ gives $\kappa=0$, so the class vanishes.

Conversely, suppose $[\kappa]=0$. Then $\kappa=db$ for some continuous $1$-cochain $b$. Replace the provisional lift by

$$
\rho_{A'}(g)=(1-b(g))\widetilde\rho(g).
$$

Section 9.4, with the correcting cochain $-b$, shows that its new defect is $\kappa-d b=0$. Hence

$$
\rho_{A'}(g)\rho_{A'}(h)=\rho_{A'}(gh).
$$

The map is continuous, reduces to $\rho_A$, and sends $1$ to $1$. It is the desired lift. $\square$

The theorem is exact, not merely one-sided: the cohomology class is the complete obstruction for this square-zero lifting step. It does not claim that all higher-order lifting problems are governed by one fixed class. A longer extension must be factored into square-zero or small steps, and a new class may appear at each step.

### 9.6 Why small extensions are the standard steps

Every surjection in $\operatorname{Art}_k$ factors into principal small extensions. The same factorization works in $\operatorname{Art}_{\mathcal O}$: the one-dimensional socle ideals used in the proof are stable under $\mathcal O$, whose action on them factors through $k$. Therefore repeated application of the preceding theorem reduces arbitrary Artinian lifting in either coefficient category to a finite sequence of obstruction classes with coefficients in $\operatorname{ad}\bar\rho$. The residual adjoint module stays fixed from step to step, which is the main advantage of smallness.

A square-zero extension need not be small. For example,

$$
k[x,e]/(x^2,e^2)\twoheadrightarrow k[x]/(x^2)
$$

has kernel $(e)$ with $e^2=0$ but $xe\neq0$. Here the coefficient action on the kernel remembers $x$, so replacing $\operatorname{ad}(\rho_A)\otimes_A I$ by $\operatorname{ad}\bar\rho\otimes_k I$ would discard genuine information.

## 10. The ambiguity and automorphisms of lifts

### 10.1 Differences of two genuine lifts are cocycles

Assume a lift $\rho_{A'}$ of $\rho_A$ exists across a square-zero extension with kernel $I$. Any second lift has a unique form

$$
\rho_{A'}'(g)=(1+c(g))\rho_{A'}(g)
$$

with $c(g)\in M_d(I)$. Both sides are homomorphisms exactly when

$$
c(gh)=c(g)+g\cdot c(h).
$$

Thus the set of actual matrix lifts of the fixed representative $\rho_A$ is a torsor under

$$
Z^1\bigl(G,\operatorname{ad}(\rho_A)\otimes_A I\bigr).
$$

It is a torsor, not canonically the vector space: choosing one lift as origin gives a bijection, but there is no distinguished origin unless the extension has a preferred lift.

For a small extension, this is a torsor under

$$
Z^1(G,\operatorname{ad}\bar\rho)\otimes_k I.
$$

This is the framed ambiguity. No quotient has yet been taken.

### 10.2 Strict equivalence produces the $H^1$-torsor

Two lifts reducing to the same matrix representation $\rho_A$ can be compared by strict conjugators that reduce to the identity already over $A$. Such a conjugator lies in the kernel of $\Gamma_{A'}\to\Gamma_A$ and has the form $1+X$ with $X\in M_d(I)$. Conjugation changes $c$ by

$$
c(g)\longmapsto c(g)+X-g\cdot X=c(g)-dX(g).
$$

Consequently, if the obstruction vanishes, classes of lifts of the fixed representative, where equivalences are required to reduce to the identity automorphism of that representative, form a torsor under

$$
H^1\bigl(G,\operatorname{ad}(\rho_A)\otimes_A I\bigr).
$$

For a small extension this is

$$
\boxed{
H^1(G,\operatorname{ad}\bar\rho)\otimes_k I.
}
$$

This is a deliberately rigidified statement. There is a subtlety in passing from it to the fiber of the set-valued map

$$
D_{\bar\rho}(A')\to D_{\bar\rho}(A).
$$

An element of that fiber reduces only to a class strictly equivalent to $[\rho_A]$, and a chosen equivalence with the fixed representative can be changed by a strict automorphism of $\rho_A$. The clean $H^1$-torsor statement therefore belongs either to the groupoid fiber with a chosen reduction identification or to the preceding rigidified equivalence relation. If one uses ordinary strict equivalence over $A'$ without fixing its reduction, automorphisms of $\rho_A$ can identify points of that torsor. The coarse set-theoretic fiber may consequently be a further quotient and need not itself be an $H^1$-torsor.

### 10.3 Infinitesimal automorphisms are $H^0$

Let $\rho_{A'}$ be a lift. A conjugator $1+X$ with $X\in M_d(I)$ is an automorphism of $\rho_{A'}$ exactly when

$$
(1+X)\rho_{A'}(g)=\rho_{A'}(g)(1+X)
$$

for every $g$. Modulo $I^2$, this is

$$
X=g\cdot X.
$$

Hence the kernel of reduction on strict automorphism groups is canonically

$$
H^0\bigl(G,\operatorname{ad}(\rho_A)\otimes_A I\bigr)
$$

under addition. For a small extension it is

$$
H^0(G,\operatorname{ad}\bar\rho)\otimes_k I.
$$

More precisely, there is an exact sequence at the left

$$
1\longrightarrow
H^0(G,\operatorname{ad}\bar\rho)\otimes_k I
\longrightarrow\operatorname{Aut}^{\mathrm{str}}_{A'}(\rho_{A'})
\longrightarrow\operatorname{Aut}^{\mathrm{str}}_A(\rho_A),
$$

where surjectivity of the last arrow is not automatic: an automorphism of the reduction may itself have an obstruction to lifting while centralizing the chosen lift. The exact kernel statement is unconditional.

Framed objects have only identity arrows because an arrow must preserve the chosen basis. Nevertheless $H^0$ still appears in the difference between the $d^2$ possible infinitesimal basis changes and the $d^2-h^0$ directions that actually move a framed matrix.

### 10.4 The full three-degree pattern

Across a principal small extension with one-dimensional kernel, the deformation groupoid exhibits the following pattern:

$$
\begin{array}{c|c|c}
\text{cohomological degree}&\text{linear object}&\text{deformation meaning}\\ \hline
0&H^0(G,\operatorname{ad}\bar\rho)&
\text{infinitesimal strict automorphisms}\\
1&Z^1(G,\operatorname{ad}\bar\rho)&
\text{differences of framed lifts}\\
1&H^1(G,\operatorname{ad}\bar\rho)&
\text{differences of unframed lifts}\\
2&H^2(G,\operatorname{ad}\bar\rho)&
\text{obstruction to existence}.
\end{array}
$$

The occurrence of both $Z^1$ and $H^1$ is essential. Framing removes isomorphisms, so it retains cocycles. Unframed classification divides by changes of basis and retains cohomology classes.

### 10.5 An unobstructed example and its limitation

Suppose $G=\mathbf Z_p$ and all kernels are finite $p$-primary modules. Its continuous cohomological dimension is one, so

$$
H^2(G,\operatorname{ad}\bar\rho)=0.
$$

Every lift across a small extension is therefore unobstructed. Starting from $\bar\rho$, one can lift successively along any chosen tower of coefficient surjections, provided at each stage the coefficient category supplies the tower.

This does not yet produce a universal ring. It proves existence along specified small extensions. Compatibility among all coefficient diagrams and the control of automorphisms are separate categorical questions.

### 10.6 A concrete obstructed relation

Let $G=C_p=\langle\sigma\rangle$, let $k$ have characteristic $p$, and begin with the trivial one-dimensional representation. Consider lifting the first-order character

$$
\rho_2(\sigma)=1+\epsilon
$$

from $A=k[\epsilon]/(\epsilon^2)$ to $A'=k[\epsilon]/(\epsilon^3)$. A possible lift is $1+\epsilon+a\epsilon^2$. The group relation demands

$$
(1+\epsilon+a\epsilon^2)^p=1.
$$

For odd $p$, the binomial coefficients vanish modulo $p$ and $\epsilon^p=0$ when $p\geq3$, so the relation holds. For $p=2$,

$$
(1+\epsilon+a\epsilon^2)^2=1+\epsilon^2
\neq1
$$

in $k[\epsilon]/(\epsilon^3)$, independently of $a$. The first-order character of $C_2$ is obstructed at second order.

The obstruction is visible as the defect attached to the relation $\sigma^2=1$, and it represents a nonzero class in $H^2(C_2,k)$. This example shows why a nonzero tangent direction need not lie on a deformation of arbitrary thickness.

## 11. Fixed determinant across small extensions

### 11.1 Choosing determinant-preserving provisional lifts

Let $A'\twoheadrightarrow A$ have square-zero kernel $I$, and suppose $\rho_A$ has determinant $\delta_A$. Assume the prescribed character $\delta_{A'}$ lifts $\delta_A$. We can choose each provisional matrix $\widetilde\rho(g)$ to have determinant exactly $\delta_{A'}(g)$.

Indeed, begin with any matrix lift $M_g$. The ratio

$$
u_g=\delta_{A'}(g)\det(M_g)^{-1}
$$

lies in $1+I$. Multiplying $M_g$ on the left by $\operatorname{diag}(u_g,1,\ldots,1)$ corrects its determinant without changing its reduction. To retain continuity, make the choice on the finite image of the pair

$$
g\longmapsto(\rho_A(g),\delta_{A'}(g)).
$$

Using only the image of $\rho_A$ would be insufficient if two group elements had the same reduced matrix but different determinant lifts in $1+I$.

For such provisional lifts, the defect satisfies

$$
\det(1+\kappa(g,h))=1,
$$

because $\delta_{A'}$ is a character. Hence

$$
\operatorname{tr}\kappa(g,h)=0.
$$

The defect is an $\operatorname{ad}^0$-valued $2$-cocycle.

### 11.2 The fixed-determinant obstruction class

Write

$$
\operatorname{ad}^0(\rho_A)
=\ker\bigl(\operatorname{tr}:\operatorname{End}_A(A^d)\to A\bigr)
$$

with the conjugation action induced by $\rho_A$. Its tensor product with $I$ identifies with the trace-zero matrices in $M_d(I)$. Changing determinant-preserving provisional lifts multiplies them by $1+b(g)$ with $\operatorname{tr}b(g)=0$. Therefore the defect changes by an $\operatorname{ad}^0$-valued coboundary. We obtain

$$
\operatorname{ob}^{\delta}(\rho_A,A'/A)
\in H^2\bigl(G,\operatorname{ad}^0(\rho_A)\otimes_A I\bigr),
$$

and for a small extension,

$$
\boxed{
\operatorname{ob}^{\delta}(\rho_A,A'/A)
\in H^2(G,\operatorname{ad}^0\bar\rho)\otimes_k I.
}
$$

The same correction proof shows that this class vanishes if and only if a lift with determinant $\delta_{A'}$ exists. If it vanishes, framed determinant-preserving lifts form a torsor under

$$
Z^1(G,\operatorname{ad}^0\bar\rho)\otimes_k I.
$$

### 11.3 Unframed ambiguity and the characteristic caveat

For fixed-determinant lifts equipped with an identification of their reduction with the chosen representative, conjugation by every $1+X$ with $X\in M_d(I)$ is allowed. Its coboundary is trace zero, although $X$ need not be. Therefore the rigidified unframed ambiguity is a torsor under

$$
\frac{Z^1(G,\operatorname{ad}^0\bar\rho)\otimes_k I}
{d(\operatorname{ad}\bar\rho\otimes_k I)}.
$$

When $\operatorname{char}k\nmid d$, this is

$$
H^1(G,\operatorname{ad}^0\bar\rho)\otimes_k I.
$$

When $\operatorname{char}k\mid d$, it is instead the kernel of trace on $H^1(\operatorname{ad})$, or equivalently the quotient of $H^1(\operatorname{ad}^0)$ by the connecting directions described in Section 7.4. As in the unrestricted problem, forgetting the chosen reduction identification can further quotient this torsor by strict automorphisms of $\rho_A$. The determinant obstruction still naturally lives in $H^2(\operatorname{ad}^0)$; it is the classification of ambiguities that requires the extra quotient.

### 11.4 Automorphisms are not trace zero by default

A strict automorphism of a fixed-determinant representation is simply a strict matrix centralizing its image. There is no determinant restriction on the conjugator. Infinitesimally the automorphism space over a small kernel is therefore

$$
H^0(G,\operatorname{ad}\bar\rho)\otimes_k I,
$$

not $H^0(G,\operatorname{ad}^0\bar\rho)\otimes_k I$. The latter would describe determinant-one infinitesimal automorphisms of a volume-framed object.

When $d$ is invertible in $k$, the difference is a harmless scalar summand for orbit directions. When the characteristic divides $d$, scalar automorphisms themselves are trace zero, and careless subtraction can miscount both stabilizers and fixed-determinant tangent dimensions.

## 12. Functoriality of deformation problems

### 12.1 Two independent kinds of variance

There are two basic directions of functoriality. A coefficient map $A\to B$ sends a representation forward by applying the map to its entries. A group homomorphism $\varphi:H\to G$ sends a representation backward by composition:

$$
\rho\longmapsto\rho\circ\varphi.
$$

Thus deformation functors are covariant in coefficient rings and contravariant in acting groups. Keeping these directions visible prevents a common reversal when restriction is combined with base change.

Let $\bar\rho_H=\bar\rho\circ\varphi$. Composition defines natural maps

$$
D_{\bar\rho,G}(A)\longrightarrow D_{\bar\rho_H,H}(A)
$$

and similarly for framed and fixed-determinant functors. Strict conjugators remain strict after restriction. On tangent spaces the map is exactly pullback of continuous cochains,

$$
H^1(G,\operatorname{ad}\bar\rho)
\longrightarrow
H^1(H,\operatorname{ad}\bar\rho_H).
$$

The obstruction class also pulls back: provisional lifts for $G$ restrict to provisional lifts for $H$, and their defect cocycle is the restricted defect.

### 12.2 Restriction to closed subgroups

If $H\leq G$ is closed, it is profinite and the preceding construction gives restriction. A global lift can become equivalent to another after restriction even if the global lifts were inequivalent, because a global cohomology class may restrict to zero. Likewise a global obstruction can vanish locally without vanishing globally.

For an open subgroup, restriction followed by corestriction multiplies cohomology by $[G:H]$. Hence if an obstruction restricts to zero and the index is invertible in $k$, it vanishes. If the index is divisible by $\operatorname{char}k$, no such conclusion follows. This is the precise cohomological boundary of descent from a subgroup.

For a quotient map $G\twoheadrightarrow Q$, deformations factoring through $Q$ form a subproblem. At tangent level their classes are inflated from

$$
H^1(Q,(\operatorname{ad}\bar\rho)^N),
$$

where $N$ is the kernel and the residual representation factors through $Q$. Inflation--restriction measures the additional tangent directions detected on $N$.

### 12.3 Change of residual basis

Let $B\in\operatorname{GL}_d(k)$ and put

$$
\bar\rho^B(g)=B^{-1}\bar\rho(g)B.
$$

These are the same abstract residual module with different chosen bases. For a fixed $A$, choose any lift $B_A\in\operatorname{GL}_d(A)$ of $B$. Then

$$
\rho_A\longmapsto B_A^{-1}\rho_A B_A
$$

sends lifts of $\bar\rho$ to lifts of $\bar\rho^B$. If $B_A'$ is another lift, then $B_A'B_A^{-1}$ reduces to the identity, so the two resulting unframed lifts are strictly equivalent. Hence there is a choice-independent bijection

$$
D_{\bar\rho}(A)\xrightarrow{\sim}D_{\bar\rho^B}(A).
$$

These bijections are natural on unframed classes. For framed functors, the actual matrix depends on the chosen lift $B_A$. A natural framed isomorphism is obtained when $B$ has been lifted once to the coefficient base, for then its images in all $A$ are compatible. Intrinsically, this says that changing the chosen residual basis changes the notion of framing and requires a specified transport of frames.

On adjoint modules the map is $X\mapsto B^{-1}XB$. It identifies cocycles, coboundaries, tangent spaces, and obstruction classes. Trace is preserved, so fixed-determinant theories are compatible as well.

### 12.4 Coefficient extension of the residue field

Let $k'/k$ be a finite extension and suppose the coefficient categories have been enlarged compatibly. Scalar extension gives

$$
\bar\rho_{k'}:G\to\operatorname{GL}_d(k').
$$

There is a natural map from deformations obtained by scalar extension to deformations of $\bar\rho_{k'}$. It need not be surjective: the larger coefficient field can supply new parameters or split residual endomorphism algebras. At the level of continuous cochains, finite scalar extension gives

$$
H^i(G,\operatorname{ad}\bar\rho)\otimes_k k'
\simeq H^i(G,\operatorname{ad}\bar\rho_{k'})
$$

because locally constant maps are filtered unions of maps through finite quotients, finite scalar extension commutes with those cochain groups, and $k'/k$ is flat. Thus cohomology commutes with this base change without an additional finiteness assumption on $H^i$. This compares tangent and obstruction spaces even when descent of individual deformations requires more work.

Absolute irreducibility is designed to behave well here: it means irreducibility after extension to an algebraic closure, and it forces the endomorphism algebra to remain scalar after every finite scalar extension.

### 12.5 Direct sums

Suppose

$$
\bar\rho_i:G\to\operatorname{GL}_{d_i}(k)
\qquad(i=1,2).
$$

Block sum gives a natural operation on framed lifts,

$$
D_{\bar\rho_1}^{\square}(A)\times
D_{\bar\rho_2}^{\square}(A)
\longrightarrow
D_{\bar\rho_1\oplus\bar\rho_2}^{\square}(A).
$$

It also descends to unframed classes because block sums of strict conjugators are strict. But it is generally neither injective nor surjective onto all deformations of the direct sum. Off-diagonal extension classes deform $\bar\rho_1\oplus\bar\rho_2$ without preserving either summand, while automorphisms mixing isomorphic summands can identify different decomposed data.

The tangent calculation displays the missing directions:

$$
\operatorname{ad}(\bar\rho_1\oplus\bar\rho_2)
\simeq
\operatorname{ad}\bar\rho_1\oplus
\operatorname{ad}\bar\rho_2\oplus
\operatorname{Hom}(V_2,V_1)\oplus
\operatorname{Hom}(V_1,V_2).
$$

The direct-sum operation reaches the first two summands; the cross terms are extensions between the constituents. Therefore an assertion that the deformation functor of a direct sum is the product of the two deformation functors is false without an additional condition preserving the decomposition and hypotheses controlling its automorphisms.

Determinants satisfy

$$
\det(\rho_1\oplus\rho_2)=\det\rho_1\det\rho_2.
$$

Thus fixed determinants combine only when the chosen characters multiply to the chosen determinant of the sum.

### 12.6 Tensor products

Let $\rho_i$ be lifts on finite free $A$-modules of ranks $d_i$. Their tensor product is a continuous lift of $\bar\rho_1\otimes\bar\rho_2$:

$$
(\rho_1\otimes\rho_2)(g)=\rho_1(g)\otimes\rho_2(g).
$$

Continuity follows because the Kronecker-product map between finite discrete matrix groups is continuous. Strict equivalences $P_i$ induce the strict equivalence $P_1\otimes P_2$, so tensor product descends to unframed classes.

At first order, if

$$
\rho_{i,\epsilon}(g)=(1+\epsilon c_i(g))\bar\rho_i(g),
$$

then

$$
c_{1\otimes2}(g)=c_1(g)\otimes1+1\otimes c_2(g)
$$

under the natural inclusion into $\operatorname{End}(V_1\otimes V_2)$. This map on cocycles need not be surjective; general tensor-product deformations can have directions not decomposable into changes of the two factors.

The determinant formula is

$$
\det(\rho_1\otimes\rho_2)
=(\det\rho_1)^{d_2}(\det\rho_2)^{d_1}.
$$

Accordingly, tensor products respect fixed determinant only with this compatibility. Freeness of both modules is essential for the rank and determinant formulas in this form.

### 12.7 Twists and duals

A fixed continuous character $\chi:G\to\mathcal O^\times$ twists lifts by

$$
\rho_A\longmapsto\rho_A\otimes\chi_A.
$$

Twisting identifies deformation functors of $\bar\rho$ and $\bar\rho\otimes\bar\chi$ when the character is not itself being deformed. Their adjoint modules are canonically the same because the scalar twist cancels in conjugation. Thus tangent and obstruction groups are unchanged, while determinants are multiplied by $\chi_A^d$.

Dualizing a lift gives

$$
\rho_A^\vee(g)={}^{t}\rho_A(g)^{-1}.
$$

It is compatible with strict equivalence, with the conjugator sent to ${}^{t}P^{-1}$. The induced adjoint identification sends $X$ to $-{}^tX$ at first order, reflecting the derivative of inverse transpose. These operations are safe because the underlying modules are finite free; dualizing arbitrary nonflat families would not have the same behavior.

## 13. Local Galois representations as examples

### 13.1 The local setting and what is being illustrated

Let $K$ be a nonarchimedean local field, let $G_K$ be its absolute Galois group, and let $k$ have characteristic $\ell$. The general deformation definitions require no special property of $G_K$. Books 16 and 17 supply additional arithmetic information: low-degree cohomology is finite in the standard finite-coefficient range, local Euler characteristic formulas calculate tangent dimensions, and local duality identifies $H^2$ with twisted invariants.

These calculations describe the **ambient** local deformation functor. Conditions such as unramified, minimally ramified, ordinary, or finite flat select subfunctors and subspaces. Their systematic construction belongs to later books. Here the local examples show how the general deformation--cohomology dictionary becomes numerical.

### 13.2 Obstructions detected by local duality

For a finite-dimensional $k$-representation $M$ in the local duality range,

$$
H^2(K,M)^*\simeq H^0(K,M^*(1)).
$$

The trace pairing identifies $(\operatorname{ad}\bar\rho)^*$ with $\operatorname{ad}\bar\rho$, so

$$
h^2_K(\operatorname{ad}\bar\rho)
=h^0_K(\operatorname{ad}\bar\rho(1)).
$$

Thus the obstruction space vanishes if there is no adjoint endomorphism with the cyclotomic twist. Concretely, a nonzero invariant in $\operatorname{ad}\bar\rho(1)$ is an intertwiner between $\bar\rho$ and an appropriate cyclotomic twist of itself. This is often easier to test than writing down $2$-cocycles.

Vanishing of the group makes every small-extension obstruction vanish. Nonvanishing of the group does not prove that a particular obstruction is nonzero; it only gives a receptacle in which one may occur.

### 13.3 Mixed-characteristic dimension formulas

Assume $K/\mathbf Q_\ell$ is finite of degree $n_K$. The local Euler characteristic formula gives

$$
h^1_K(\operatorname{ad}\bar\rho)
=h^0_K(\operatorname{ad}\bar\rho)
+h^2_K(\operatorname{ad}\bar\rho)
+n_Kd^2.
$$

Substituting into the framed formula yields

$$
\dim_k Z^1(K,\operatorname{ad}\bar\rho)
=h^2_K(\operatorname{ad}\bar\rho)+(n_K+1)d^2.
$$

The residual centralizer cancels. This does not mean automorphisms have disappeared; their contribution to $h^1$ is exactly offset by the quotient from matrices to coboundaries.

Suppose $\bar\rho$ is absolutely irreducible and has no cyclotomic self-twist contributing to $H^0(K,\operatorname{ad}\bar\rho(1))$. Then

$$
h^0=1,\qquad h^2=0,
$$

so

$$
h^1=1+n_Kd^2,
\qquad
\dim Z^1=(n_K+1)d^2.
$$

For $K=\mathbf Q_\ell$ and $d=2$, the unframed tangent dimension is $5$ and the framed tangent dimension is $8$.

### 13.4 Fixed determinant in mixed characteristic

Assume $\ell\nmid d$. Then the trace-zero adjoint splits off and local duality applies through the nondegenerate trace pairing. If

$$
H^0(K,\operatorname{ad}^0\bar\rho)=0,
\qquad
H^0(K,\operatorname{ad}^0\bar\rho(1))=0,
$$

then

$$
h^1_K(\operatorname{ad}^0\bar\rho)
=n_K(d^2-1),
$$

and

$$
\dim Z^1(K,\operatorname{ad}^0\bar\rho)
=(n_K+1)(d^2-1).
$$

For an absolutely irreducible two-dimensional representation of $G_{\mathbf Q_\ell}$ with $\ell\neq2$ and no relevant self-twist, these dimensions are $3$ and $6$.

When $\ell\mid d$, neither the trace splitting nor the self-duality of $\operatorname{ad}^0$ may be used in this form. The framed fixed-determinant tangent space remains $Z^1(\operatorname{ad}^0)$, but the unframed tangent is the kernel of trace on $H^1(\operatorname{ad})$, and the dual of $\operatorname{ad}^0$ is a quotient rather than automatically itself.

### 13.5 Coefficient characteristic away from the residue characteristic

Suppose $\ell$ differs from the residue characteristic of $K$. The Euler characteristic has no $n_K\dim M$ term, so

$$
h^1_K(M)=h^0_K(M)+h^2_K(M).
$$

For $M=\operatorname{ad}\bar\rho$ this gives

$$
\dim Z^1(K,\operatorname{ad}\bar\rho)
=d^2+h^2_K(\operatorname{ad}\bar\rho).
$$

If the adjoint obstruction group vanishes, the framed ambient tangent dimension is exactly $d^2$, regardless of the residual centralizer. The unframed dimension is then $h^0$, so an absolutely irreducible representation has a one-dimensional ambient tangent space. That direction is often unramified, but identifying a particular local condition still requires restriction to inertia.

### 13.6 Unramified tangent directions

Let $I_K\leq G_K$ be inertia and let $\varphi$ be arithmetic Frobenius. For a finite module $M$, the unramified subgroup is

$$
H^1_{\mathrm{ur}}(K,M)
=\ker\bigl(H^1(K,M)\to H^1(I_K,M)\bigr)
$$

and admits the Frobenius description

$$
H^1_{\mathrm{ur}}(K,M)
\simeq M^{I_K}/(\varphi-1)M^{I_K}.
$$

For $M=\operatorname{ad}\bar\rho$, this is the tangent space obtained by requiring the infinitesimal cocycle to vanish on inertia up to coboundary. Its dimension is

$$
\dim H^1_{\mathrm{ur}}(K,\operatorname{ad}\bar\rho)
=h^0_K(\operatorname{ad}\bar\rho).
$$

For an absolutely irreducible residual representation this dimension is one. With fixed determinant and $\ell\nmid d$, it is

$$
h^0_K(\operatorname{ad}^0\bar\rho),
$$

which is zero in the absolutely irreducible case. These are tangent calculations only. Proving that an unramified deformation subfunctor has a particular lifting property belongs to the theory of local deformation conditions.

### 13.7 A split two-character local calculation

Assume here that $\ell$ differs from the residue characteristic of $K$. Let $\bar\rho=\chi_1\oplus\chi_2$ with both characters unramified, and let $q$ be the residue-field cardinality viewed in $k^\times$. Put

$$
\alpha=\chi_1(\varphi)\chi_2(\varphi)^{-1}.
$$

The upper-right adjoint line has Frobenius eigenvalue $\alpha$, and the lower-left line has eigenvalue $\alpha^{-1}$. Away from the residue characteristic, an unramified one-dimensional module with eigenvalue $a$ has

$$
h^0=[a=1],\qquad h^2=[a=q],
\qquad h^1=[a=1]+[a=q].
$$

Therefore the upper-right extension direction appears when $\alpha=1$ or $\alpha=q$, and the lower-left direction appears when $\alpha^{-1}=1$ or $\alpha^{-1}=q$. The diagonal trivial lines each contribute their own unramified direction, with an additional tame contribution if $q=1$ in $k$.

This worked calculation explains tangent-dimension jumps. They occur at special ratios of Frobenius eigenvalues, not because the formal definition changes, but because an off-diagonal character acquires invariants or twisted invariants.

### 13.8 Elliptic-curve residual representations

Let $E/K$ be an elliptic curve and $\ell\neq\operatorname{char}K$. Choosing a basis of $E[\ell]$ gives

$$
\bar\rho_{E,\ell}:G_K\to\operatorname{GL}_2(\mathbf F_\ell).
$$

The Weil pairing gives

$$
\det\bar\rho_{E,\ell}=\bar\chi_\ell,
$$

the mod-$\ell$ cyclotomic character. Deformations arising from an $\ell$-adic Tate module therefore come naturally with a prescribed cyclotomic determinant, motivating the fixed-determinant functor.

If $E[\ell]$ has a $G_K$-stable line, an adapted basis makes the representation upper triangular. The two off-diagonal adjoint cohomology groups then describe possible extension directions between the two residual characters. A stable line is weaker than a rational point: its character can be nontrivial. Deformation theory must remember the characters on both line and quotient, not merely reducibility.

If the residue characteristic of $K$ differs from $\ell$ and $E$ has good reduction, the representation is unramified, so the unramified tangent calculation applies. At multiplicative reduction the residual representation is typically upper triangular with a cyclotomic line and an extension class controlled by the Tate parameter. Those arithmetic shapes motivate local subfunctors but do not alter the ambient definitions developed here.

## 14. Fiber products, automorphisms, and the edge of representability

### 14.1 Gluing framed lifts

Let $A'\to A\leftarrow A''$ be coefficient maps with one map surjective, and put

$$
B=A'\times_AA''.
$$

A matrix over $B$ is exactly a pair of matrices over $A'$ and $A''$ with the same image over $A$. Entrywise multiplication respects this identification. Consequently framed lifts satisfy an exact gluing identity:

$$
D_{\bar\rho}^{\square}(B)
\xrightarrow{\sim}
D_{\bar\rho}^{\square}(A')
\times_{D_{\bar\rho}^{\square}(A)}
D_{\bar\rho}^{\square}(A'').
$$

Continuity is preserved because all target groups are finite discrete. The same statement holds for framed fixed-determinant lifts when the determinant characters are compatible.

This identity is one reason framed deformation problems are well behaved: equality of matrices glues entry by entry.

### 14.2 Why unframed gluing is subtler

For unframed deformations, a pair of classes whose reductions agree gives only the existence of a strict conjugacy over $A$, not a chosen conjugacy. To glue representatives, one must choose that arrow and lift it appropriately. Because one leg is surjective, the chosen strict conjugator over $A$ lifts along that leg. After conjugating one representative by the lift, the two matrices agree over $A$ and hence glue over $B$. Thus the natural map

$$
D_{\bar\rho}(B)
\longrightarrow
D_{\bar\rho}(A')\times_{D_{\bar\rho}(A)}D_{\bar\rho}(A'')
$$

is surjective. What can fail is injectivity: different choices of the comparison arrow over $A$ can produce inequivalent glued objects.

At the groupoid level the missing arrow is retained, and the correct homotopy-style fiber product glues objects together with a specified isomorphism over $A$. Passing prematurely to connected components discards precisely that datum.

This observation is not yet a representability criterion. It identifies the mechanism that later criteria must control. Absolute irreducibility often reduces the endomorphism algebra to scalars, and scalar automorphisms may act harmlessly in suitable diagrams, but the proof belongs to Book 22.

### 14.3 The automorphism double-coset

The ambiguity can be stated exactly without claiming a false first-order counterexample. Fix representatives $\rho'$ over $A'$ and $\rho''$ over $A''$, and identify their reductions with a common lift $\rho_A$. Two strict comparison arrows over $A$ differ by an element of

$$
\operatorname{Aut}^{\mathrm{str}}_A(\rho_A).
$$

Changing $\rho'$ or $\rho''$ by a strict automorphism changes that element through the images of the two upstairs automorphism groups. Thus the possible glued classes attached to the fixed branch objects are measured by a double-coset set of the form

$$
\operatorname{im}\operatorname{Aut}^{\mathrm{str}}_{A'}(\rho')
\backslash
\operatorname{Aut}^{\mathrm{str}}_A(\rho_A)
/
\operatorname{im}\operatorname{Aut}^{\mathrm{str}}_{A''}(\rho'').
$$

Nontriviality of this set is the precise automorphism mechanism behind failure of injectivity. It also explains why merely knowing the dimension of the residual centralizer is not enough: what matters in a particular diagram is whether its automorphisms lift along the two branches.

There is an important sanity check. For

$$
B=k[\epsilon,\eta]/(\epsilon^2,\epsilon\eta,\eta^2)
=k[\epsilon]\times_k k[\eta],
$$

the maximal ideal is square zero, and the two cocycle directions separate. Both framed and unframed tangent calculations give the expected product, so this simplest fiber product is not by itself a counterexample. Automorphism failures arise only when the comparison over a nontrivial common quotient carries information that cannot be absorbed by automorphisms lifting from the branches. Establishing categorical criteria that rule out such failures is left to Book 22.

### 14.4 What this book does not assert

We have defined functors and computed their low-order behavior. We have not asserted any of the following:

- that $D_{\bar\rho}$ or $D_{\bar\rho}^{\square}$ is pro-representable;
- that there is a universal deformation ring;
- that finite-dimensional tangent space alone implies the existence of a hull;
- that $H^2=0$ alone implies representability or a power-series presentation;
- that quotienting a framed representing object by a matrix group automatically represents the unframed functor.

Each assertion needs a categorical lifting analysis across fiber products and small extensions. Those are the subjects of Schlessinger-style theory in Book 22. The current book supplies the deformation functors, tangent spaces, obstruction classes, and automorphism groups to which that theory will be applied.

### 14.5 What vanishing of $H^2$ really gives

If

$$
H^2(G,\operatorname{ad}\bar\rho)=0,
$$

then every lift of a fixed representative extends across every small extension in the coefficient category. By factoring arbitrary Artinian surjections into small extensions, lifts extend across arbitrary Artinian surjections step by step. This is a formal smoothness property of the framed lifting assignment and, with careful treatment of representatives, of the deformation groupoid.

It does not remove automorphisms, prove finite tangent dimension, or force the coarse unframed set-valued functor to have the fiber-product behavior required for a representing ring. Unobstructed and representable are logically distinct adjectives.

For fixed determinant, the relevant sufficient vanishing is

$$
H^2(G,\operatorname{ad}^0\bar\rho)=0,
$$

together with the existence of the prescribed determinant character at every coefficient level.

## 15. Extended worked calculations

### 15.1 Deforming a character of $\mathbf Z_p$

Let $G=\mathbf Z_p$ with topological generator $\gamma$, let $k$ have characteristic $p$, and let $\bar\chi:G\to k^\times$ be a continuous character. Since the adjoint action of a character is trivial,

$$
t_{\bar\chi}=H^1(G,k)
=\operatorname{Hom}_{\mathrm{cts}}(\mathbf Z_p,k^+)
\simeq k.
$$

In fact $\bar\chi$ must be trivial: a finite continuous quotient of the pro-$p$ group $\mathbf Z_p$ has $p$-power order, whereas $k^\times$ has order prime to $p$. We retain the character notation to emphasize how the adjoint calculation generalizes.

A scalar $a\in k$ corresponds to

$$
\chi_a(\gamma)=\bar\chi(\gamma)(1+a\epsilon).
$$

Continuity determines the character on all of $\mathbf Z_p$: the additive cocycle sends $x\in\mathbf Z_p$ to the reduction of $x$ modulo $p$, multiplied by $a$. There is one first-order direction.

Since $\operatorname{cd}_p(\mathbf Z_p)=1$, $H^2(G,k)=0$, and every character lift extends across small extensions. One can see the absence of relations directly: a continuous character is determined by the image of the topological generator, subject only to the condition that this image be pro-$p$ in its infinitesimal part. For an Artinian $A$ of residue characteristic $p$, every element of $1+\mathfrak m_A$ has finite $p$-power order, so a choice near $\bar\chi(\gamma)$ defines a continuous homomorphism from $\mathbf Z_p$.

If instead the determinant is fixed, the one-dimensional representation itself is fixed and the tangent direction disappears. This contrasts “deforming a character” with “using a fixed character as determinant data.”

### 15.2 A cyclic relation and the obstruction cocycle

Let $G=C_m=\langle\sigma\mid\sigma^m=1\rangle$, and suppose a representation $\rho_A$ is generated by a matrix $T\in\operatorname{GL}_d(A)$ satisfying $T^m=1$. Let $A'\twoheadrightarrow A$ be a principal small extension with kernel $I$, choose a $k$-basis of $I$, and use it to identify $M_d(I)$ with $M_d(k)$. Choose a matrix lift $\widetilde T$. A representation lift exists exactly when one can correct $\widetilde T$ by $1+X$, $X\in M_d(I)$, so that

$$
((1+X)\widetilde T)^m=1.
$$

Because $I^2=0$, expansion gives

$$
((1+X)\widetilde T)^m
=1+X+T\cdot X+\cdots+T^{m-1}\cdot X+E,
$$

where $E\in M_d(I)$ is defined by $\widetilde T^m=1+E$, and $T$ acts on $M_d(I)$ by conjugation. Smallness makes this the residual adjoint action. Thus the correction equation is

$$
N_T(X)=-E,
\qquad
N_T=1+T+\cdots+T^{m-1}
$$

on the adjoint module.

The element $E$ is $T$-invariant because $\widetilde T$ commutes with its own $m$th power.

After the chosen identification $I\simeq k$, the class of $E$ modulo the norm image is the periodic description of the obstruction in

$$
H^2(C_m,\operatorname{ad}\bar\rho)
=\frac{(\operatorname{ad}\bar\rho)^{C_m}}
{N_T(\operatorname{ad}\bar\rho)}.
$$

Thus the abstract defect $2$-cocycle specializes to the elementary failure of a lifted generator to satisfy its defining relation. The correction by a $1$-cochain specializes to changing that generator by $1+X$.

### 15.3 Two commuting generators

Let $G=\mathbf Z_p^2$ with topological generators $x,y$, let $k$ have characteristic $p$, and suppose the residual representation is trivial. A first-order framed lift is given by

$$
\rho_\epsilon(x)=1+\epsilon X,
\qquad
\rho_\epsilon(y)=1+\epsilon Y.
$$

The commutator is

$$
(1+\epsilon X)(1+\epsilon Y)
(1-\epsilon X)(1-\epsilon Y)=1,
$$

so there is no first-order condition on $X$ and $Y$. At the next order, over $k[\epsilon]/(\epsilon^3)$, choose

$$
\rho(x)=1+\epsilon X+\epsilon^2X_2,
\qquad
\rho(y)=1+\epsilon Y+\epsilon^2Y_2.
$$

Their commutator is

$$
1+\epsilon^2[X,Y].
$$

The displayed first-order lift extends to this second-order ring only if $[X,Y]=0$. The terms $X_2$ and $Y_2$ do not change the leading commutator, and if $X$ and $Y$ commute one may take $X_2=Y_2=0$. The bracket is therefore the exact quadratic obstruction for this lifting step.

This example explains why $H^1$ alone cannot describe the local shape of a deformation space. Every pair $(X,Y)$ is tangent, but only commuting pairs extend through this particular second-order thickening. The defect class packages the commutator independently of the chosen lifted matrices.

### 15.4 An upper-triangular deformation condition as a preview

Return to $\bar\rho=\chi_1\oplus\chi_2$. If one asks that a deformation preserve the first coordinate line, framed matrices must remain upper triangular. At first order this removes the lower-left cocycles and leaves

$$
Z^1(G,k)^{\oplus2}\oplus
Z^1(G,k(\chi_1\chi_2^{-1})).
$$

But the corresponding unframed tangent space depends on which conjugators are allowed. If the stable line is part of the deformation datum, isomorphisms must preserve it, so only upper-triangular infinitesimal conjugators should be divided out. If the condition merely asserts that some stable line exists, conjugators can move the line and the set-valued quotient is different.

This preview illustrates a general rule for later local conditions: first specify the objects and their isomorphisms, then linearize. Naming a cohomology subspace before deciding what extra structure is retained can give the wrong tangent quotient.

### 15.5 A nonscalar centralizer calculation

Let

$$
\bar\rho(g)=
\begin{pmatrix}1&u(g)\\0&1\end{pmatrix}
$$

be a nonsplit two-dimensional unipotent representation, with the values of $u$ spanning $k$. Write

$$
X=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
$$

The equality $X\bar\rho(g)=\bar\rho(g)X$ gives

$$
cu(g)=0,
\qquad
(a-d)u(g)=0
$$

for all $g$. Hence $c=0$ and $a=d$, while $b$ is arbitrary. Therefore

$$
H^0(G,\operatorname{ad}\bar\rho)
=\left\{
\begin{pmatrix}a&b\\0&a\end{pmatrix}:a,b\in k
\right\}.
$$

It follows that

$$
\dim B^1(G,\operatorname{ad}\bar\rho)=4-2=2,
$$

and

$$
\dim Z^1(G,\operatorname{ad}\bar\rho)
=h^1(G,\operatorname{ad}\bar\rho)+2.
$$

If one had treated every reducible representation as though its two diagonal characters split, one would get the correct centralizer dimension in this self-extension example only by accident; the module structure and connecting maps remain different.

### 15.6 An absolutely irreducible local example

Let $K/\mathbf Q_\ell$ have degree $n_K$, and let

$$
\bar\rho:G_K\to\operatorname{GL}_2(k)
$$

be absolutely irreducible. Assume $\ell\neq2$ and

$$
H^0(K,\operatorname{ad}\bar\rho(1))=0,
\qquad
H^0(K,\operatorname{ad}^0\bar\rho(1))=0.
$$

The unrestricted and fixed-determinant data are then

$$
\begin{array}{c|c|c|c}
\text{problem}&h^0&h^1&\dim Z^1\\ \hline
\text{unrestricted}&1&1+4n_K&4(n_K+1)\\
\text{fixed determinant}&0&3n_K&3(n_K+1).
\end{array}
$$

For $K=\mathbf Q_\ell$, fixing determinant removes two unframed tangent dimensions: the unrestricted space has dimension five and the fixed-determinant space dimension three. One removed direction is the bulk scalar coefficient direction and the other is the scalar invariant contribution appearing through the Euler formula. At framed level the dimensions fall from eight to six, exactly the difference between $\dim\operatorname{ad}=4$ and $\dim\operatorname{ad}^0=3$ across both the local and frame terms.

Both obstruction groups vanish under the hypotheses, so every small-extension lifting problem is soluble. The table still does not produce universal rings; it is a complete low-degree cohomological profile.

### 15.7 A local reducible eigenvalue jump

Let $K$ have residue cardinality $q$, let $\ell$ differ from the residue characteristic, and let $\bar\rho=\chi_1\oplus\chi_2$ be unramified. If

$$
\alpha=\chi_1(\varphi)\chi_2(\varphi)^{-1}
$$

is different from $1$, $q$, and $q^{-1}$, both off-diagonal adjoint lines have vanishing cohomology. The tangent space consists only of diagonal character variations. At $\alpha=1$, the two residual characters coincide on Frobenius and off-diagonal invariants appear. At $\alpha=q$, the upper-right line acquires a degree-two class and a corresponding degree-one direction; at $\alpha=q^{-1}$ the lower-left line does.

Thus a family of residual representations can cross loci where both tangent and obstruction dimensions jump. Absolute irreducibility avoids this particular diagonal decomposition, but it does not rule out analogous self-twist loci detected by $H^0(\operatorname{ad}(1))$.

## 16. The reusable deformation--cohomology dictionary

### 16.1 Data checklist

Before defining a deformation problem, fix all of the following.

1. A profinite group $G$.
2. A finite coefficient field $k$ and, when needed, a complete local base $\mathcal O$ with residue field $k$.
3. A continuous residual representation $\bar\rho:G\to\operatorname{GL}_d(k)$ in a fixed basis.
4. The coefficient category, usually $\operatorname{Art}_{\mathcal O}$.
5. Whether a residual identification, a frame, a stable subobject, a volume form, or only an isomorphism class is part of the datum.
6. For fixed determinant, a continuous lift $\delta:G\to\mathcal O^\times$ of $\det\bar\rho$.

Changing item 5 changes the automorphism group and hence can change the tangent quotient. Changing item 6 changes the functor even when the residual determinant is unchanged.

### 16.2 Object and equivalence dictionary

For $A\in\operatorname{Art}_{\mathcal O}$:

$$
\begin{array}{c|c}
\text{notion}&\text{matrix description}\\ \hline
\text{lift}&
\rho_A:G\to\operatorname{GL}_d(A),\quad \rho_A\bmod\mathfrak m_A=\bar\rho\\
\text{strict conjugator}&
P\in\Gamma_A=1+M_d(\mathfrak m_A)\\
\text{strict equivalence}&
\rho_A'=P\rho_AP^{-1}\\
\text{framed deformation}&
\text{an actual lift, with no conjugacy quotient}\\
\text{unframed deformation}&
\text{a strict-equivalence class}\\
\text{strict automorphism}&
\Gamma_A\cap Z_{\operatorname{GL}_d(A)}(\rho_A(G)).
\end{array}
$$

Arbitrary conjugacy is not strict equivalence. A framed-to-unframed fiber is a $\Gamma_A$-orbit with the displayed stabilizer, not a free $\Gamma_A$-torsor.

### 16.3 Tangent dictionary

Using

$$
\rho_\epsilon(g)=(1+\epsilon c(g))\bar\rho(g),
$$

the translations are

$$
\begin{array}{c|c}
\text{deformation feature}&\text{cohomological object}\\ \hline
\text{multiplicativity}&c\in Z^1(G,\operatorname{ad}\bar\rho)\\
\text{conjugation by }1+\epsilon X&c\mapsto c-dX\\
\text{framed tangent}&Z^1(G,\operatorname{ad}\bar\rho)\\
\text{change-of-frame directions}&B^1(G,\operatorname{ad}\bar\rho)\\
\text{unframed tangent}&H^1(G,\operatorname{ad}\bar\rho)\\
\text{infinitesimal stabilizer}&H^0(G,\operatorname{ad}\bar\rho).
\end{array}
$$

When dimensions are finite,

$$
\dim Z^1=h^1+d^2-h^0,
\qquad
\dim B^1=d^2-h^0.
$$

These formulas require no irreducibility. Absolute irreducibility merely sets $h^0=1$.

### 16.4 Fixed-determinant tangent dictionary

The derivative of determinant is trace:

$$
\det(1+\epsilon X)=1+\epsilon\operatorname{tr}X.
$$

Therefore

$$
t^{\square,\delta}_{\bar\rho}
=Z^1(G,\operatorname{ad}^0\bar\rho).
$$

For the ordinary unframed fixed-determinant functor,

$$
t^\delta_{\bar\rho}
=\frac{Z^1(G,\operatorname{ad}^0\bar\rho)}
{d(\operatorname{ad}\bar\rho)}
=\ker\left(H^1(G,\operatorname{ad}\bar\rho)
\to H^1(G,k)\right).
$$

If $\operatorname{char}k\nmid d$, this is $H^1(G,\operatorname{ad}^0\bar\rho)$. If $\operatorname{char}k\mid d$, it is generally a quotient of that group by the connecting image of $H^0(G,k)$. Scalar matrices then lie in $\operatorname{ad}^0$, and neither trace splitting nor the usual trace-zero self-duality should be assumed.

### 16.5 Small-extension protocol

For a small extension

$$
0\to I\to A'\to A\to0,
\qquad \mathfrak m_{A'}I=0,
$$

and a fixed lift $\rho_A$:

1. Choose continuous matrix lifts $\widetilde\rho(g)$.
2. Form the defect

   $$
   1+\kappa(g,h)=\widetilde\rho(g)\widetilde\rho(h)
   \widetilde\rho(gh)^{-1}.
   $$

3. Associativity gives $d\kappa=0$ in $\operatorname{ad}\bar\rho\otimes_k I$.
4. Replacing $\widetilde\rho$ by $(1+b)\widetilde\rho$ changes $\kappa$ to $\kappa+db$.
5. The class

   $$
   [\kappa]\in H^2(G,\operatorname{ad}\bar\rho)\otimes_k I
   $$

   vanishes exactly when a lift exists.
6. If it vanishes, framed lifts form a torsor under $Z^1\otimes I$. Lifts equipped with a fixed identification of their reduction with the chosen representative form an $H^1\otimes I$-torsor, while the coarse fiber of unframed classes may be its further quotient by automorphisms of that representative. Infinitesimal automorphisms are $H^0\otimes I$.

For a square-zero extension that is not small, replace the residual module by $\operatorname{ad}(\rho_A)\otimes_A I$. The nilpotent action of $A$ on $I$ must not be discarded.

### 16.6 Fixed-determinant lifting protocol

First choose provisional matrix lifts whose determinants equal $\delta_{A'}$. Their defects have trace zero. The obstruction is

$$
[\kappa]^\delta\in
H^2(G,\operatorname{ad}^0\bar\rho)\otimes_k I.
$$

It vanishes exactly when a determinant-preserving lift exists. Framed ambiguity is $Z^1(\operatorname{ad}^0)\otimes I$. With a fixed reduction identification, unframed ambiguity divides by coboundaries coming from all of $\operatorname{ad}$; forgetting that identification can impose a further automorphism quotient. Restricting instead to determinant-one conjugators would retain a volume form and define a different problem.

The existence of a residual determinant is not enough: the compatible lifted character $\delta$ must have been fixed in the coefficient category.

### 16.7 Functoriality dictionary

The safe operations are:

$$
\begin{array}{c|c|c}
\text{operation}&\text{direction on deformations}&\text{direction on cohomology}\\ \hline
A\to B& D(A)\to D(B)&\text{coefficient pushforward}\\
H\to G&D_G\to D_H&H^i(G,M)\to H^i(H,M)\\
\text{residual basis change}&\text{equivalent unframed functor}&X\mapsto B^{-1}XB\\
\text{fixed twist}&D_{\bar\rho}\simeq D_{\bar\rho\otimes\bar\chi}&\operatorname{ad}\text{ unchanged}\\
\text{direct sum}&D_1\times D_2\to D_{1\oplus2}&\text{diagonal summands only}\\
\text{tensor product}&D_1\times D_2\to D_{1\otimes2}&c_1\otimes1+1\otimes c_2.
\end{array}
$$

Direct-sum and tensor maps are not generally isomorphisms of functors. Off-diagonal extension directions, mixing automorphisms, and new tensor deformations prevent such conclusions without additional hypotheses.

### 16.8 Topology and finiteness checklist

Every representation and cochain is continuous. For Artinian coefficients with finite residue field, targets are finite discrete and continuity means open kernel or locally constant cochains. For complete coefficients, targets carry their adic topology and continuity is equivalent to compatible finite-level continuity.

No finiteness property of $G$ is required to define $D_{\bar\rho}$, $D_{\bar\rho}^{\square}$, their groupoids, tangent spaces, or obstruction classes. Finite-dimensional numerical formulas require finite $H^i$. Local absolute Galois groups in the standard finite-coefficient range supply this through arithmetic theorems; a general profinite group may not.

### 16.9 Boundary checklist

The following implications are valid:

$$
H^2(G,\operatorname{ad}\bar\rho)=0
\Longrightarrow
\text{every small-extension lifting obstruction vanishes},
$$

and

$$
t_{\bar\rho}=H^1(G,\operatorname{ad}\bar\rho).
$$

The following implications are not valid without further theory:

$$
\text{finite tangent space}\centernot\Longrightarrow
\text{pro-representability},
$$

$$
H^2=0\centernot\Longrightarrow
\text{existence of a universal ring},
$$

$$
D^{\square}/\Gamma\centernot\Longrightarrow
\text{a representable quotient functor}.
$$

The missing issues are compatibility on coefficient fiber products, effectiveness of lifting, and automorphisms. They are not technical footnotes; they are the content of the next stage of the theory.

## 17. Conclusion

### 17.1 The coherent low-degree picture

A deformation of a continuous residual representation is a continuous lift over a finite local thickening together with a fixed identification of its special fiber. That identification forces strict equivalence: only changes of basis reducing to the identity are allowed. Retaining a basis gives the framed functor; forgetting it produces an orbit set whose stabilizers are strict centralizers. The action is never to be treated as automatically free.

Over the dual numbers, the matrix factorization

$$
\rho_\epsilon(g)=(1+\epsilon c(g))\bar\rho(g)
$$

turns multiplication into the cocycle equation and strict conjugation into a coboundary. This yields the exact distinctions

$$
t^{\square}_{\bar\rho}=Z^1(G,\operatorname{ad}\bar\rho),
\qquad
t_{\bar\rho}=H^1(G,\operatorname{ad}\bar\rho),
$$

with $H^0$ measuring the frame changes that act trivially. Fixing determinant linearizes by trace. When $d$ is invertible in $k$, trace zero splits cleanly; when the residue characteristic divides $d$, scalar directions enter $\operatorname{ad}^0$ and the ordinary unframed tangent is a quotient of $H^1(\operatorname{ad}^0)$ rather than automatically that group.

Across a small extension, provisional matrix lifts fail to multiply by a canonical cohomology class

$$
\operatorname{ob}(\rho_A,A'/A)
\in H^2(G,\operatorname{ad}\bar\rho)\otimes_k I.
$$

Associativity proves it is a cocycle, changing provisional lifts adds a coboundary, and vanishing is equivalent to correcting the lifts into a representation. Once it vanishes, alternatives with a fixed identification of their reduction form an $H^1$-torsor, while infinitesimal automorphisms form $H^0$; the coarse set-valued fiber may further divide by automorphisms of the lower lift. Fixed determinant replaces the obstruction coefficient by $\operatorname{ad}^0$ after determinant-preserving provisional lifts have been chosen.

### 17.2 The endpoint for later deformation conditions

The resulting dictionary is deliberately ambient. Restriction to decomposition groups, preservation of inertia type, unramifiedness, ordinarity, finite flatness, and global Selmer conditions will later select subfunctors and subspaces inside the objects constructed here. At tangent level they will select subspaces of $H^1$; at obstruction level they will refine the $H^2$ class; at the groupoid level they must specify which extra structures and automorphisms remain.

No universal ring has been assumed, and no representability criterion has been used. What has been established is logically prior: a precise continuous deformation functor, its framed and fixed-determinant variants, their naturality, their exact tangent spaces, and their complete obstruction theory across one square-zero step. This is the reusable local language in which the representability theory of Book 22 and the local and global deformation conditions of later books can be stated without ambiguity.
