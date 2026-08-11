# Pseudocompact Trace Algebras and Carayol Descent

## Contents

1. [The coefficient field hidden in a character](#1-the-coefficient-field-hidden-in-a-character)
   - [The descent problem](#11-the-descent-problem)
   - [Why traces are the right invariant](#12-why-traces-are-the-right-invariant)
   - [The three layers of the argument](#13-the-three-layers-of-the-argument)
   - [Standing conventions](#14-standing-conventions)
2. [Closed coefficient algebras and strict topology](#2-closed-coefficient-algebras-and-strict-topology)
   - [Finite shadows and closure](#21-finite-shadows-and-closure)
   - [Locality of a closed coefficient algebra](#22-locality-of-a-closed-coefficient-algebra)
   - [Strict maps and exact inverse limits](#23-strict-maps-and-exact-inverse-limits)
   - [Topological Nakayama](#24-topological-nakayama)
   - [When the induced topology is adic](#25-when-the-induced-topology-is-adic)
   - [Two boundary examples](#26-two-boundary-examples)
   - [Closed images of finite free modules](#27-closed-images-of-finite-free-modules)
3. [Compact groups and continuous characters](#3-compact-groups-and-continuous-characters)
   - [Why compactness enters](#31-why-compactness-enters)
   - [Representations and finite-level factorization](#32-representations-and-finite-level-factorization)
   - [Characters as compatible locally constant functions](#33-characters-as-compatible-locally-constant-functions)
   - [The closed trace algebra](#34-the-closed-trace-algebra)
   - [Character rigidity in the absolutely irreducible case](#35-character-rigidity-in-the-absolutely-irreducible-case)
   - [What a character does not remember](#36-what-a-character-does-not-remember)
   - [Class functions through finite quotients](#37-class-functions-through-finite-quotients)
4. [Burnside and Jacobson density](#4-burnside-and-jacobson-density)
   - [The spanning problem](#41-the-spanning-problem)
   - [Schur's lemma over an algebraically closed field](#42-schurs-lemma-over-an-algebraically-closed-field)
   - [The finite-dimensional density lemma](#43-the-finite-dimensional-density-lemma)
   - [Burnside's theorem](#44-burnsides-theorem)
   - [Descent from an algebraic closure](#45-descent-from-an-algebraic-closure)
   - [Failure without absolute irreducibility](#46-failure-without-absolute-irreducibility)
   - [Equivalent residual density tests](#47-equivalent-residual-density-tests)
5. [Trace coordinates and matrix generation](#5-trace-coordinates-and-matrix-generation)
   - [The trace pairing](#51-the-trace-pairing)
   - [Choosing a residual group basis](#52-choosing-a-residual-group-basis)
   - [The dual-basis calculation](#53-the-dual-basis-calculation)
   - [The trace-generation theorem](#54-the-trace-generation-theorem)
   - [Consequences for centralizers and characters](#55-consequences-for-centralizers-and-characters)
   - [Why no division is needed](#56-why-no-division-is-needed)
   - [Independence of the chosen group basis](#57-independence-of-the-chosen-group-basis)
   - [A rank-two coordinate calculation](#58-a-rank-two-coordinate-calculation)
6. [The algebra generated over the trace ring](#6-the-algebra-generated-over-the-trace-ring)
   - [Constructing the finite free algebra](#61-constructing-the-finite-free-algebra)
   - [Multiplication and scalar extension](#62-multiplication-and-scalar-extension)
   - [The Azumaya criterion](#63-the-azumaya-criterion)
   - [The center and the centralizer](#64-the-center-and-the-centralizer)
   - [Finite quotients and base change](#65-finite-quotients-and-base-change)
   - [Azumaya algebras, orders, and a boundary](#66-azumaya-algebras-orders-and-a-boundary)
   - [Morita intuition and the splitting module](#67-morita-intuition-and-the-splitting-module)
7. [Henselian lifting and splitting](#7-henselian-lifting-and-splitting)
   - [Why a split special fiber should split the algebra](#71-why-a-split-special-fiber-should-split-the-algebra)
   - [Lifting idempotents through nilpotent ideals](#72-lifting-idempotents-through-nilpotent-ideals)
   - [Compatible lifting in a pseudocompact ring](#73-compatible-lifting-in-a-pseudocompact-ring)
   - [A lifted rank-one projector](#74-a-lifted-rank-one-projector)
   - [Splitting the Azumaya algebra](#75-splitting-the-azumaya-algebra)
   - [What Henselianity is doing](#76-what-henselianity-is-doing)
   - [Hensel's lemma behind the projector argument](#77-hensels-lemma-behind-the-projector-argument)
   - [Lifting a complete system of matrix units](#78-lifting-a-complete-system-of-matrix-units)
8. [Skolem--Noether over a local base](#8-skolem--noether-over-a-local-base)
   - [The conjugacy problem for two splittings](#81-the-conjugacy-problem-for-two-splittings)
   - [Matrix units over a local ring](#82-matrix-units-over-a-local-ring)
   - [The local Skolem--Noether theorem](#83-the-local-skolem--noether-theorem)
   - [Uniqueness modulo scalars](#84-uniqueness-modulo-scalars)
   - [Residual normalization](#85-residual-normalization)
   - [Conjugacy of two embeddings](#86-conjugacy-of-two-embeddings)
   - [The module-theoretic form](#87-the-module-theoretic-form)
9. [Carayol descent](#9-carayol-descent)
   - [The theorem](#91-the-theorem)
   - [Proof strategy](#92-proof-strategy)
   - [Construction of the descended representation](#93-construction-of-the-descended-representation)
   - [Strict normalization of the conjugator](#94-strict-normalization-of-the-conjugator)
   - [Minimality of the trace algebra](#95-minimality-of-the-trace-algebra)
   - [Descent at every Artinian level](#96-descent-at-every-artinian-level)
   - [A hypothesis-by-hypothesis audit](#97-a-hypothesis-by-hypothesis-audit)
   - [Rings of definition and their intersection](#98-rings-of-definition-and-their-intersection)
10. [Strict-conjugacy descent](#10-strict-conjugacy-descent)
    - [Strict equivalence and fixed residual bases](#101-strict-equivalence-and-fixed-residual-bases)
    - [Centralizers of residually absolutely irreducible families](#102-centralizers-of-residually-absolutely-irreducible-families)
    - [Descent of a conjugacy](#103-descent-of-a-conjugacy)
    - [Uniqueness of descended models](#104-uniqueness-of-descended-models)
    - [A descent statement for families](#105-a-descent-statement-for-families)
    - [The scalar torsor of conjugators](#106-the-scalar-torsor-of-conjugators)
    - [Compatibility through quotient towers](#107-compatibility-through-quotient-towers)
11. [Examples, counterexamples, and diagnostic variants](#11-examples-counterexamples-and-diagnostic-variants)
    - [Rank one](#111-rank-one)
    - [A pure change of basis](#112-a-pure-change-of-basis)
    - [A diagonal family with a smaller trace ring](#113-a-diagonal-family-with-a-smaller-trace-ring)
    - [Merely irreducible is not enough](#114-merely-irreducible-is-not-enough)
    - [Why closedness and continuity cannot be dropped](#115-why-closedness-and-continuity-cannot-be-dropped)
    - [Characteristic-polynomial variants](#116-characteristic-polynomial-variants)
    - [A finite-group model calculation](#117-a-finite-group-model-calculation)
    - [Coefficient change and trace rings](#118-coefficient-change-and-trace-rings)
12. [The descent machine in final form](#12-the-descent-machine-in-final-form)
    - [The logical dependency chain](#121-the-logical-dependency-chain)
    - [A reusable criterion](#122-a-reusable-criterion)
    - [Consequences for coefficient problems](#123-consequences-for-coefficient-problems)
    - [Conclusion](#124-conclusion)

## 1. The coefficient field hidden in a character

### 1.1 The descent problem

A representation is written with matrices, but its matrix entries depend on a basis. This simple observation creates a subtle coefficient problem. Suppose a compact group $G$ acts continuously on a free module over a large complete local ring $A$. Its matrices may use all of $A$, while their traces lie in a much smaller closed local subring $B$. Is the use of $A$ genuine, or is it an artifact of the chosen basis?

The desired conclusion has a precise form. One seeks a single matrix $u\in\operatorname{GL}_d(A)$ such that

$$
u^{-1}\rho(g)u\in\operatorname{GL}_d(B)
\qquad(g\in G).
$$

This is stronger than descending each matrix separately. The same basis change must work for every group element, preserve multiplication, and behave compatibly at every infinitesimal level. Moreover, when a residual basis has already been fixed, one wants $u$ to reduce to the identity. That strengthened conclusion is called strict descent.

The obstruction is easy to underestimate. Traces are invariant under conjugation, but invariance alone does not reconstruct entries. Two nonsplit extensions can have the same trace, and a trace-generated subring need not contain eigenvalues. The missing hypothesis is residual absolute irreducibility. It forces the residual group matrices to span the entire matrix algebra. Once that spanning is available, the ordinary trace pairing converts invariant trace values into coordinates of every matrix.

The central result of this book is Carayol descent: under the exact topological and irreducibility hypotheses stated in Chapter 9, the representation is strictly conjugate to one defined over its closed trace algebra. The proof is constructive at the structural level. It identifies a finite free algebra over the trace ring, proves that algebra is Azumaya, splits it by Henselian lifting, and then compares its two realizations by conjugacy.

### 1.2 Why traces are the right invariant

For matrices $x,y$ over a commutative ring,

$$
\operatorname{tr}(xy)=\operatorname{tr}(yx),
$$

so trace is unchanged by conjugation. If $\rho^u(g)=u\rho(g)u^{-1}$, then

$$
\operatorname{tr}\rho^u(g)=\operatorname{tr}\rho(g).
$$

Thus every possible coefficient ring for a conjugate of $\rho$ must contain all trace values. In a complete setting it must also contain their limits. This leads to the closed trace algebra

$$
T_\rho=
\overline{\mathcal O[\operatorname{tr}\rho(g):g\in G]}
\subseteq A,
$$

where $\mathcal O$ is the fixed coefficient base and closure is taken in $A$.

There are two reasons to use the trace rather than selected matrix entries. First, traces survive change of basis. Second, products of group matrices are again group matrices:

$$
\operatorname{tr}(\rho(g)\rho(h))
=\operatorname{tr}\rho(gh).
$$

Consequently the trace pairing between two group matrices is itself a character value. If finitely many residual group matrices form a basis of the full matrix algebra, their trace Gram matrix is invertible. Its inverse then expresses every matrix in trace coordinates. This is the decisive calculation of Chapter 5.

Trace is not always the only possible invariant. Coefficients of characteristic polynomials are often useful, especially when residual irreducibility is absent. But in the absolutely irreducible situation, ordinary traces already give the bilinear coordinates needed for descent, in every characteristic and without dividing by $d$.

### 1.3 The three layers of the argument

The proof has three layers, each solving a different difficulty.

The topological layer replaces an infinite coefficient ring by compatible Artinian shadows. Closed subalgebras, strict maps, and topological Nakayama ensure that statements proved at every finite stage reassemble without losing separation or surjectivity. Compactness of $G$ makes every discrete residual representation factor through a finite quotient.

The linear-algebra layer begins with residual absolute irreducibility. Burnside's theorem, obtained from finite-dimensional Jacobson density, says that the residual group matrices span $M_d(k)$. The nondegenerate trace pairing then gives a finite group-matrix basis and explicit trace formulas for all coordinates.

The noncommutative layer packages that basis into an algebra $E$ over $T_\rho$. The algebra becomes $M_d(A)$ after extending scalars and has special fiber $M_d(k)$. It is therefore Azumaya. Henselian lifting produces a rank-one idempotent, which splits $E$ as a full endomorphism algebra. Local Skolem--Noether then says that the abstract splitting and the original embedding differ by one conjugation.

These layers should not be collapsed into the slogan “traces determine the representation.” Topology explains which trace ring is meant; density explains why traces provide coordinates; Azumaya splitting explains why those coordinates come from matrices over the smaller ring; and Skolem--Noether produces the basis change.

### 1.4 Standing conventions

All rings are associative with identity, and commutative unless explicitly called an algebra of matrices or an Azumaya algebra. Ring homomorphisms preserve identity. Fix a complete Noetherian local coefficient ring $\mathcal O$ with maximal ideal $\mathfrak m_{\mathcal O}$ and residue field $k$.

Every matrix rank $d$ is a positive integer. In particular, the residual density, rank-one projector, and matrix-algebra statements below include the case $d=1$ but not a vacuous rank-zero convention.

A **pro-Artinian local $\mathcal O$-algebra** $A$ means a complete Hausdorff topological local $\mathcal O$-algebra presented as

$$
A\cong\varprojlim_r A_r,
$$

where the $A_r$ are local Artinian $\mathcal O$-algebras with residue field $k$, the transition maps are surjective, and their kernels form a neighborhood basis of zero. We assume a countable cofinal tower. This includes every complete Noetherian local $\mathcal O$-algebra with its maximal-ideal topology. The countability assumption permits transparent compatible lifting; it can be replaced by the corresponding general inverse-limit condition.

The maximal ideal of $A$ is $\mathfrak m_A$, and reduction modulo it is marked by a bar. The topology on $M_d(A)$ and $\operatorname{GL}_d(A)$ is the entrywise topology. A representation

$$
\rho:G\longrightarrow\operatorname{GL}_d(A)
$$

of a compact topological group is always assumed continuous. Its reduction is

$$
\bar\rho:G\longrightarrow\operatorname{GL}_d(k).
$$

The residual representation is **absolutely irreducible** if $\bar\rho\otimes_k\overline{k}$ is irreducible. No finiteness or perfection assumption is imposed on $k$. When Artinian shadows are used, they are assumed finite-length coefficient algebras in the sense above; they need not be finite sets.

## 2. Closed coefficient algebras and strict topology

### 2.1 Finite shadows and closure

The descent ring is defined by infinitely many trace values, so one must first know how a closed subalgebra sits inside an inverse limit. Let

$$
A=\varprojlim_r A_r
$$

be pro-Artinian local, with projection kernels $J_r$, and let $B\subseteq A$ be a closed $\mathcal O$-subalgebra. Write

$$
B_r=\operatorname{im}(B\to A_r)
=B/(B\cap J_r).
$$

Then

$$
B\xrightarrow{\sim}\varprojlim_r B_r.
$$

Indeed, injectivity follows from $\bigcap_rJ_r=0$. A compatible family in the $B_r$ defines an element $a\in A$. Every neighborhood $a+J_r$ meets $B$, so $a$ lies in the closure of $B$; closedness gives $a\in B$. Thus a closed subalgebra is exactly the compatible totality of its finite shadows.

If $S\subseteq A$ and

$$
B=\overline{\mathcal O[S]},
$$

then closure disappears at finite level:

$$
B_r=\mathcal O_r[S_r]\subseteq A_r.
$$

This identity is the practical reason for defining trace algebras by closure. In a discrete quotient a dense algebra and its closure have the same image, while in the inverse limit only the closed one is complete.

### 2.2 Locality of a closed coefficient algebra

A closed coefficient subalgebra inherits more than completeness.

**Proposition.** Let $A$ be pro-Artinian local with residue field $k$, and let $B\subseteq A$ be a closed $\mathcal O$-subalgebra whose image in $k$ is all of $k$. Then $B$ is local, with

$$
\mathfrak m_B=B\cap\mathfrak m_A,
\qquad B/\mathfrak m_B\cong k.
$$

**Proof strategy.** An element with nonzero residue is a unit in $A$. The issue is to show its inverse stays in $B$. A geometric series gives the inverse in every Artinian shadow, and closedness puts the compatible limit back in $B$.

**Proof.** Let $b\in B$ have nonzero residue. Choose $o\in\mathcal O$ with the same residue. Then $o$ is a unit and

$$
b=o(1-x),\qquad x=1-o^{-1}b\in B\cap\mathfrak m_A.
$$

In every $A_r$, the image of $x$ lies in a nilpotent maximal ideal, so $1-x$ has inverse given by a finite geometric sum. The compatible partial inverses converge in $A$ to $(1-x)^{-1}$. They belong to $B$, and $B$ is closed, so the limit belongs to $B$. Hence every element outside $B\cap\mathfrak m_A$ is a unit of $B$. The displayed ideal is therefore the unique maximal ideal, and the residue assertion follows from the image of $\mathcal O$. $\square$

Closedness is indispensable. The dense subring $k[t]_{(t)}\subset k[[t]]$ has the correct residue field and the same quotients modulo $t^n$, but it is not complete and is not recovered as their inverse limit.

### 2.3 Strict maps and exact inverse limits

Continuity alone does not control the topology on an image. A continuous map $f:M\to N$ between linearly topologized modules is **strict** if

$$
M/\ker f\longrightarrow f(M)
$$

is a homeomorphism for the quotient and subspace topologies. Strict injections identify the source topology with the induced topology; strict surjections give the target its quotient topology.

This condition is what makes exactness compatible with inverse limits. Suppose

$$
0\longrightarrow M'_r\longrightarrow M_r\longrightarrow M''_r\longrightarrow0
$$

is an inverse system of exact sequences of finite-length modules and the transition maps on the $M'_r$ are surjective. Then

$$
0\longrightarrow\varprojlim_rM'_r
\longrightarrow\varprojlim_rM_r
\longrightarrow\varprojlim_rM''_r\longrightarrow0
$$

is exact. To lift a compatible element on the right, choose a lift one level at a time. If the new lift disagrees with the old one after reduction, the discrepancy lies in $M'_r$; lift that discrepancy to $M'_{r+1}$ and subtract it. The correction preserves the desired image and restores compatibility.

Closed submodules of pseudocompact modules, together with Hausdorff quotients, give strict exact sequences. By contrast, quotienting by a dense proper submodule produces a non-Hausdorff object and destroys finite-shadow reconstruction. Strictness is therefore a mathematical hypothesis, not topological decoration.

### 2.4 Topological Nakayama

Ordinary Nakayama detects generators in a finite module over a local ring. In an inverse limit the image of $\mathfrak m_BM$ need not be closed, so the correct residual quotient is

$$
M/\overline{\mathfrak m_BM}.
$$

**Theorem (topological Nakayama).** Let $B$ be pro-Artinian local and $M$ a pseudocompact $B$-module.

1. If $M=\overline{\mathfrak m_BM}$, then $M=0$.
2. If $m_1,\ldots,m_s$ span $M/\overline{\mathfrak m_BM}$, then the $m_i$ generate $M$ as a $B$-module.

**Proof strategy.** Reduce to every finite quotient, use ordinary Nakayama there, and recover the limit by Hausdorffness.

**Proof.** Let $U$ be an open submodule. The finite-length module $M/U$ is acted on through an Artinian local quotient of $B$. If $M=\overline{\mathfrak m_BM}$, then

$$
M/U=\mathfrak m_B(M/U),
$$

so ordinary Nakayama gives $M/U=0$. This holds for every $U$; their intersection is zero, hence $M=0$.

For the second assertion, first let $N$ be the closure of the algebraic submodule generated by the $m_i$. The quotient $M/N$ is pseudocompact, and the spanning hypothesis gives

$$
M/N=\overline{\mathfrak m_B(M/N)}.
$$

The first part makes $M/N=0$. The continuous map

$$
B^s\longrightarrow M,
\qquad (a_i)\longmapsto\sum_i a_im_i
$$

has closed image by the pseudocompact closed-image theorem recalled in Section 2.7. Its image is dense because its closure is $N=M$, so it is surjective. Thus the $m_i$ generate algebraically. $\square$

The finite-family conclusion is algebraic generation, even before Noetherianity is known. The decisive input is not adic finite-module theory but the closed-image theorem for continuous maps of pseudocompact modules. For an infinite generating family the direct-sum source is not pseudocompact, and topological generation can still be strictly weaker than algebraic generation.

### 2.5 When the induced topology is adic

If $B\subseteq A$ is closed, its neighborhoods are $B\cap J_r$. Its own maximal ideal also gives powers $\mathfrak m_B^n$. The two filtrations need not initially be cofinal. A finite topological generating family repairs this.

Suppose $b_1,\ldots,b_s\in\mathfrak m_B$ topologically generate $B$ over $\mathcal O$. Substitution gives a continuous map

$$
\mathcal O[[X_1,\ldots,X_s]]\longrightarrow B,
\qquad X_i\longmapsto b_i.
$$

At every Artinian stage the map is surjective. Completeness and the descending-ideal argument identify $B$ with the quotient by the intersection of the finite-level kernels. Consequently $B$ is a complete Noetherian local ring and its induced topology agrees with its maximal-ideal topology.

This result is useful but not needed for the core matrix argument. The algebra built in Chapter 6 is finite free over $B$, and topological Nakayama works even when $B$ is merely pro-Artinian. Thus Carayol descent does not require an unproved finite-generation assertion about the trace ring.

### 2.6 Two boundary examples

First take $A=k[[t]]$ and let $B$ be the closed subalgebra generated by $t^2$ and $t^3$. Then

$$
B=k[[t^2,t^3]]\cong k[[X,Y]]/(Y^2-X^3).
$$

Finite topological generation makes $B$ Noetherian and identifies its intrinsic topology with the one induced from $A$. Yet $t$ is integral over $B$ and does not belong to it. Closed descent is not the same as integral closure.

For the opposite boundary, consider the inverse limit of truncated polynomial rings in successively more variables. Its maximal ideal has independent cotangent classes $x_1,x_2,\ldots$. The ring is pro-Artinian and complete but not Noetherian. Topological Nakayama remains valid, while no finite-variable power-series presentation exists. This is why the pseudocompact formulation is genuinely broader than the complete Noetherian one.

### 2.7 Closed images of finite free modules

The matrix algebra used later is finite free over a possibly nonnoetherian pro-Artinian ring. We therefore isolate the closed-image facts that replace an indiscriminate appeal to finite-module adic theory.

Let $B$ be pro-Artinian, let $P$ be a pseudocompact $B$-module, let $N$ be a Hausdorff linearly topologized $B$-module, and let $f:P\to N$ be continuous and $B$-linear. Then $f(P)$ is closed. If $N$ is also pseudocompact, $f$ is strict. Indeed, a pseudocompact module has the finite-coset property: every family of closed cosets with the finite-intersection property has nonempty total intersection. This holds first for a finite-length discrete module by choosing an intersection whose underlying submodule has minimal length, and it passes to products, closed submodules, and inverse limits.

If $y$ lies in the closure of $f(P)$, then for every open submodule $V\subseteq N$ the inverse image

$$
f^{-1}(y+V)
$$

is a nonempty closed coset in $P$. These cosets have the finite-intersection property, so some $x\in P$ lies in all of them. Hausdorffness gives $f(x)=y$, proving that the image is closed. The kernel is closed as well. When $N$ is pseudocompact, let $U\subseteq P$ be open and contain the kernel. The image $f(U)$ is closed, and

$$
f(P)/f(U)\cong P/U
$$

has finite length. A Hausdorff linear topology on a finite-length module is discrete, so $f(U)$ is open in $f(P)$. Hence the inverse from the image to $P/\ker f$ is continuous.

The finite-free maps used below have still more explicit descriptions. For a matrix map $B^m\to B^n$ with $m=n$ and unit determinant, the adjugate formula gives a continuous $B$-linear inverse, so the map is a homeomorphism. If a map admits a continuous retraction, its image is the kernel of the complementary projection. A basis with invertible reduced determinant gives a homeomorphism of finite free modules, and an idempotent endomorphism splits source and image directly.

This observation prevents a circularity. Closedness comes from pseudocompact finite-coset theory, not from an unproved Noetherianity assertion. Explicit inverses, direct-summand decompositions, and unit determinants then supply the stronger structural statements used in the core descent proof.

## 3. Compact groups and continuous characters

### 3.1 Why compactness enters

The descent calculation is algebraic once a representation is given, but compactness controls how that representation meets the inverse-limit topology. A continuous map from a compact space to a discrete space has finite image. Therefore every Artinian shadow of a continuous representation of $G$ factors through a finite quotient of $G$.

This is the precise compact-group input. It does not assert semisimplicity, nor does it require the order of the finite quotient to be invertible in $k$. Modular representations are allowed. Compactness supplies finite-level factorization; absolute irreducibility supplies matrix density.

A compact group need not be profinite, but every continuous homomorphism from it to a discrete group has finite image. Thus only the profinite quotient detected by the representation matters. If the connected component of the identity is nontrivial, it lies in the kernel of every discrete reduction. The representation can still have a nontrivial inverse-limit image, but each requested coefficient precision sees a finite quotient.

This separation of roles is important. Finite image at each level does not imply that the representation is semisimple in residue characteristic dividing that image's order. Conversely, semisimplicity would not by itself control compatibility across infinitely many coefficient levels. The theory uses exactly the input compactness reliably provides and no more.

### 3.2 Representations and finite-level factorization

Let $A=\varprojlim A_r$ and let $\rho:G\to\operatorname{GL}_d(A)$ be continuous. Reduction gives

$$
\rho_r:G\longrightarrow\operatorname{GL}_d(A_r).
$$

The target is discrete. Its image is compact and discrete, hence finite. The kernel is open because $\rho_r$ is continuous. Thus $\rho_r$ factors through the finite group

$$
G/\ker\rho_r.
$$

Conversely, a compatible system of continuous finite-level representations $\rho_r$ defines a unique continuous representation into $\operatorname{GL}_d(A)$. Continuity follows because the inverse-limit topology is the coarsest topology making all projections continuous.

The kernels need not be the same at every level. Increasing coefficient precision can detect finer group elements. What matters is compatibility:

$$
\rho_{r+1}(g)\bmod A_r=\rho_r(g).
$$

If $J_{r+1}\subseteq J_r$, then $\ker\rho_{r+1}\subseteq\ker\rho_r$. Hence the finite quotients form an inverse system, and the image of $G$ in $\operatorname{GL}_d(A)$ is itself an inverse limit of finite groups. It is compact and totally disconnected even when $G$ has additional topology invisible to $\rho$.

For matrix descent it is useful that one finite set of elements $g_i$ is chosen from the residual quotient and then retained at every higher level. Their residual Gram determinant is nonzero, so the same matrices remain a basis through all thickenings. The group quotients may grow, but the number of matrix directions stays fixed at $d^2$.

### 3.3 Characters as compatible locally constant functions

The character of $\rho$ is the continuous class function

$$
\chi_\rho:G\longrightarrow A,
\qquad \chi_\rho(g)=\operatorname{tr}\rho(g).
$$

It is a class function because $\operatorname{tr}(xy)=\operatorname{tr}(yx)$. Its reductions

$$
\chi_r(g)=\operatorname{tr}\rho_r(g)
$$

are locally constant and factor through finite quotients. Moreover

$$
\chi_\rho=\varprojlim_r\chi_r
$$

pointwise. Two continuous characters into $A$ are equal exactly when their reductions agree at every stage, since $A$ is Hausdorff.

It is tempting to invoke ordinary character orthogonality, but that would impose hypotheses irrelevant here and false in modular characteristic. Our arguments use only multiplication in the group, the trace pairing on the full matrix algebra, and finite-level continuity. No averaging by $|G|^{-1}$ occurs.

### 3.4 The closed trace algebra

Define

$$
T_\rho=\overline{\mathcal O[\chi_\rho(g):g\in G]}\subseteq A.
$$

At level $r$, put

$$
T_r=\mathcal O_r[\chi_r(g):g\in G]\subseteq A_r.
$$

Then

$$
T_\rho\cong\varprojlim_rT_r.
$$

Each $T_r$ is a local Artinian coefficient algebra with residue field $k$, and the transitions are surjective: every trace generator at level $r$ is the image of the same generator at the next level. Hence $T_\rho$ is pro-Artinian local. Its maximal ideal is $T_\rho\cap\mathfrak m_A$.

Here is the finite-length argument behind that assertion. The Artinian local ring $A_r$ has a finite filtration whose factors are finite-dimensional over $k$. Since $k$ is a cyclic module over the image $\mathcal O_r$ of $\mathcal O$, the ring $A_r$ is a finite-length $\mathcal O_r$-module. The subalgebra $T_r$ is in particular an $\mathcal O_r$-submodule. It therefore has finite length and is Artinian as a ring: every descending chain of its ideals is a descending chain of $\mathcal O_r$-submodules.

Its residue map is onto $k$ because $T_r$ contains $\mathcal O_r$. The kernel is $T_r\cap\mathfrak m_{A_r}$. If $t$ lies outside this kernel, choose $o\in\mathcal O_r$ with the same residue and write

$$
t=o(1-x),\qquad x\in T_r\cap\mathfrak m_{A_r}.
$$

The element $x$ is nilpotent, so

$$
t^{-1}=o^{-1}(1+x+\cdots+x^{N-1})
$$

for $N$ large enough. The inverse lies in $T_r$, proving locality directly. This proof is the finite counterpart of the convergent geometric-series argument for the closed inverse limit.

The transition $T_{r+1}\to T_r$ is onto because its image contains $\mathcal O_r$ and every generator $\chi_r(g)$. It cannot have a smaller image than the algebra generated by those elements. Consequently the inverse limit has the required surjective pro-Artinian presentation rather than merely an abstract presentation by finite rings.

Compactness gives a modest extra observation. At a fixed level the character takes only finitely many values, because it factors through a finite quotient of $G$. Therefore $T_r$ is generated by finitely many trace values. The number of required values may grow with $r$, so this does not imply that $T_\rho$ is Noetherian. A uniform finite family across all levels would imply finite topological generation, but Carayol descent does not need such uniformity.

### 3.5 Character rigidity in the absolutely irreducible case

Over a field, an absolutely irreducible representation is determined up to conjugacy by its character, with no semisimplicity theorem or division by a group order.

**Proposition (absolutely irreducible character rigidity).** Let $\sigma,\tau:G\to\operatorname{GL}_d(k)$ have the same trace on every group element. If $\sigma$ is absolutely irreducible, then $\tau$ is absolutely irreducible and there is $u\in\operatorname{GL}_d(k)$ such that

$$
\tau(g)=u\sigma(g)u^{-1}
\qquad(g\in G).
$$

**Proof strategy.** Density supplies group elements whose $\sigma$-matrices form a basis. Equality of characters makes the trace Gram matrix for the corresponding $\tau$-matrices identical and therefore invertible. Trace-dual coordinates then identify the two generated matrix algebras. The resulting automorphism of $M_d(k)$ is inner.

**Proof.** Choose $g_1,\ldots,g_{d^2}$ such that the $\sigma(g_i)$ form a basis of $M_d(k)$. The trace Gram matrix for these matrices is invertible. Since

$$
\operatorname{tr}(\tau(g_i)\tau(g_j))
=\operatorname{tr}\tau(g_ig_j)
=\operatorname{tr}\sigma(g_ig_j),
$$

the corresponding Gram matrix for the $\tau(g_i)$ is identical. Hence the $\tau(g_i)$ also form a basis.

Define the $k$-linear isomorphism $\Phi:M_d(k)\to M_d(k)$ by

$$
\Phi(\sigma(g_i))=\tau(g_i).
$$

For an arbitrary $g$, its coordinates in the first basis are obtained by multiplying the vector

$$
(\operatorname{tr}\sigma(gg_j))_j
$$

by the inverse Gram matrix. Equality of characters shows these are exactly the coordinates of $\tau(g)$ in the second basis. Therefore $\Phi(\sigma(g))=\tau(g)$ for every $g$. It follows first on products of group matrices and then by bilinearity that

$$
\Phi(xy)=\Phi(x)\Phi(y)
$$

for all $x,y\in M_d(k)$. Thus $\Phi$ is an algebra automorphism. Local Skolem--Noether over the field $k$ makes it conjugation by some $u\in\operatorname{GL}_d(k)$. Since the $\tau(g_i)$ span the full matrix algebra, $\tau$ is absolutely irreducible by the density tests of Section 4.7. $\square$

This proof gives more than the proposition: the same finite basis controls every lift over a local ring. It also shows why equality on all group elements is the natural hypothesis. Pairings require values at the translated elements $gg_j$, not merely at a generating set of $G$.

### 3.6 What a character does not remember

If absolute irreducibility is removed, equal characters need not imply isomorphism. Let $G$ contain an element $g$ and consider over a field $k$

$$
\sigma(g)=
\begin{pmatrix}1&1\\0&1\end{pmatrix},
\qquad
\tau(g)=
\begin{pmatrix}1&0\\0&1\end{pmatrix}.
$$

All powers have trace $2$, but one action is nontrivial unipotent and the other is trivial. Trace sees their common semisimplification, not the extension class.

Even eigenvalues are not generally trace coefficients. For

$$
\rho(g)=\begin{pmatrix}u&0\\0&u^{-1}\end{pmatrix},
$$

the traces lie in the subring generated by $u+u^{-1}$, although $u$ may not lie there. Residual absolute irreducibility prevents this diagonal phenomenon by forcing products of group matrices to fill all matrix directions.

### 3.7 Class functions through finite quotients

For an open ideal $J\subseteq A$, let $N_J=\ker\rho_J$. Then $N_J$ is open and normal, and the reduced character belongs to the finite-level space

$$
\operatorname{Class}(G/N_J,A/J)
=\{f:G/N_J\to A/J:f(hgh^{-1})=f(g)\}.
$$

As $J$ shrinks, reduction and inflation make these class functions into an inverse system. More generally, continuous $A$-valued class functions are recovered from their locally constant finite-level reductions. Injectivity follows from Hausdorffness. For surjectivity, a compatible family defines a pointwise value in $A$, and inverse images of residue classes are unions of cosets of open kernels.

This is the compact-group character theory appropriate to pseudocompact coefficients. It differs from a semisimple character ring. Addition and multiplication of class functions are pointwise, but the descent argument uses neither orthogonality nor decomposition into irreducibles. What matters is that the translated functions

$$
g\longmapsto\operatorname{tr}\rho(gg_i)
$$

remain continuous trace values in the same inverse-limit setting.

At a fixed Artinian level, choose representatives $h_1,\ldots,h_s$ for the conjugacy classes in the finite image of $G$. The finite trace algebra is generated by

$$
\chi_J(h_1),\ldots,\chi_J(h_s).
$$

This gives a finite generating family at each level. It does not give one uniform list as $J$ varies. That distinction mirrors the difference between a pro-Artinian algebra and an algebra topologically generated by finitely many elements.

## 4. Burnside and Jacobson density

### 4.1 The spanning problem

Let $V$ be a $d$-dimensional vector space over $k$, and let $R\subseteq\operatorname{End}_k(V)$ be the algebra generated by a group action. Irreducibility says that $V$ has no nontrivial $R$-stable subspace. Descent requires the stronger conclusion

$$
R=\operatorname{End}_k(V).
$$

This conclusion is false for a representation that is irreducible only over $k$: its commuting division algebra may be larger than $k$. Absolute irreducibility removes that obstruction. We now prove the density theorem in the finite-dimensional form needed later.

The phrase “algebra generated” includes $k$-linear combinations of arbitrary finite products. Since products of group matrices are again group matrices, it is simply the $k$-linear span of $\sigma(G)$. Thus once density is known, no words in generators need be added: actual matrices of group elements already span the full endomorphism algebra. This observation is what later lets every pairing coefficient remain an ordinary character value.

There are two conceptually different routes from irreducibility to density. One studies minimal-rank operators in the algebra; the other asks whether an operator can be prescribed on finitely many independent vectors. The latter is Jacobson density. Its induction exposes the commutant as the only obstruction and adapts directly to our need for a finite matrix basis.

### 4.2 Schur's lemma over an algebraically closed field

**Lemma.** Let $K$ be algebraically closed and let $V$ be a finite-dimensional irreducible module over a $K$-algebra $R$. Then

$$
\operatorname{End}_R(V)=K.
$$

**Proof.** If $f$ commutes with $R$, choose an eigenvalue $\lambda\in K$ of $f$. The nonzero kernel of $f-\lambda$ is $R$-stable, so irreducibility makes it all of $V$. Thus $f=\lambda I$. $\square$

The algebraic closure is used only to produce an eigenvalue. Over a nonclosed field, the commutant of an irreducible action can be a genuine division algebra.

The finite-dimensional hypothesis ensures that an eigenvalue exists after passing to an algebraic closure and that an endomorphism with one eigenvalue has a nonzero eigenspace. No averaging over the group is involved. Schur's lemma therefore remains valid when the group is infinite and when the characteristic divides every relevant finite quotient order.

Absolute irreducibility over $k$ is precisely what allows this scalar-commutant conclusion after extension to $\overline{k}$. Descent of the full algebra back to $k$ then uses dimension, not a claim that every $k$-linear commuting operator already has an eigenvalue in $k$.

### 4.3 The finite-dimensional density lemma

**Theorem (Jacobson density, finite-dimensional form).** Let $V$ be a simple left module over a $K$-algebra $R$, and suppose $\operatorname{End}_R(V)=K$. If $v_1,\ldots,v_m$ are linearly independent and $w_1,\ldots,w_m$ are arbitrary, there exists $r\in R$ such that

$$
rv_i=w_i\qquad(1\leq i\leq m).
$$

**Proof strategy.** Induct on $m$. The orbit of $(v_1,\ldots,v_m)$ in $V^m$ projects onto the first $m-1$ factors. If the kernel of that projection is nonzero, simplicity makes it the whole last factor and permits an arbitrary correction. If the kernel vanishes, the orbit is the graph of an $R$-linear map $V^{m-1}\to V$, forcing $v_m$ to depend on the preceding vectors.

**Proof.** For $m=1$, the nonzero submodule $Rv_1$ is all of $V$. Assume the result for $m-1$ and set

$$
W=R(v_1,\ldots,v_m)\subseteq V^m.
$$

The projection $p:W\to V^{m-1}$ is surjective by induction. Its kernel, viewed in the last factor, is an $R$-submodule of $V$, so it is either $0$ or $V$.

If it is $V$, first use induction to obtain the desired first $m-1$ coordinates, then use an element of the kernel to correct the last coordinate. Hence the desired tuple lies in $W$.

Suppose instead that the kernel is zero. Then $W$ is the graph of an $R$-linear map

$$
f:V^{m-1}\longrightarrow V.
$$

Every such map is a sum of maps from the individual factors, and each map $V\to V$ is scalar because $\operatorname{End}_R(V)=K$. Thus

$$
f(x_1,\ldots,x_{m-1})=\sum_{i=1}^{m-1}\lambda_i x_i.
$$

Since $(v_1,\ldots,v_m)\in W$, this gives $v_m=\sum_i\lambda_i v_i$, contradicting linear independence. The zero-kernel case is impossible, completing the induction. $\square$

### 4.4 Burnside's theorem

**Theorem (Burnside).** Let $K$ be algebraically closed, let $V$ be finite-dimensional, and let $R\subseteq\operatorname{End}_K(V)$ be a unital subalgebra acting irreducibly. Then

$$
R=\operatorname{End}_K(V).
$$

**Proof.** Choose a basis $v_1,\ldots,v_d$ of $V$. Schur's lemma and Jacobson density show that, for every endomorphism $f$, there is $r\in R$ agreeing with $f$ on every basis vector. Hence $r=f$. $\square$

The theorem says more than the absence of invariant subspaces. It says the action contains enough linear combinations of group elements to prescribe every column of a matrix independently.

### 4.5 Descent from an algebraic closure

**Corollary (absolute density).** Let $V$ be $d$-dimensional over an arbitrary field $k$, and let $R\subseteq\operatorname{End}_k(V)$ be a unital algebra. If $V\otimes_k\overline{k}$ is irreducible under $R\otimes_k\overline{k}$, then

$$
R=\operatorname{End}_k(V).
$$

**Proof.** Burnside gives

$$
R\otimes_k\overline{k}
=\operatorname{End}_{\overline{k}}(V\otimes_k\overline{k}).
$$

The right side has dimension $d^2$. Scalar extension preserves the dimension of the finite-dimensional space $R$, so $\dim_kR=d^2$. Since $R$ is already a subspace of the $d^2$-dimensional space $\operatorname{End}_k(V)$, equality follows. $\square$

Applied to $R=k[\bar\rho(G)]$, this produces finitely many elements $g_1,\ldots,g_{d^2}\in G$ whose matrices $\bar\rho(g_i)$ form a $k$-basis of $M_d(k)$. The finiteness comes from finite-dimensionality, not from finite generation of $G$.

### 4.6 Failure without absolute irreducibility

Let $K/k$ be a finite field extension and regard the $k$-vector space $V=K$ as a module for the multiplicative group $K^\times$ acting by multiplication. Under mild choices the action can be irreducible over $k$, but its commutant contains $K$, not merely $k$. The generated algebra is the copy of $K$ inside $\operatorname{End}_k(K)$ and has dimension $[K:k]$, whereas the full endomorphism algebra has dimension $[K:k]^2$.

After extending scalars to an algebraic closure, the multiplication action decomposes according to embeddings of $K$. Thus it is not absolutely irreducible. This example pinpoints the role of the adjective: without it, the residual algebra may be a field or division algebra rather than a full matrix algebra, the trace Gram matrix on group matrices need not have rank $d^2$, and the Azumaya algebra constructed later need not have split special fiber.

### 4.7 Equivalent residual density tests

For a field-valued representation

$$
\sigma:G\longrightarrow\operatorname{GL}(V),
\qquad \dim_kV=d,
$$

the following conditions are equivalent.

1. The representation is absolutely irreducible.
2. The $k$-algebra generated by $\sigma(G)$ is $\operatorname{End}_k(V)$.
3. There exist $d^2$ group elements whose matrices form a $k$-basis of $\operatorname{End}_k(V)$.
4. There exist group elements $g_1,\ldots,g_{d^2}$ for which

   $$
   \det\bigl(\operatorname{tr}(\sigma(g_i)\sigma(g_j))\bigr)\neq0.
   $$

We have proved that (1) implies (2), and finite-dimensionality gives (2) implies (3). If (3) holds, nondegeneracy of the trace pairing says the Gram matrix in (4) is invertible. Conversely, (4) makes the listed matrices linearly independent: a relation $\sum_i a_i\sigma(g_i)=0$ paired with every $\sigma(g_j)$ gives an invertible linear system with solution $a_i=0$. There are $d^2$ matrices, so they form a basis and give (3).

Finally, (2) implies (1). Any nonzero proper subspace after scalar extension that is stable under $\sigma(G)$ would be stable under

$$
k[\sigma(G)]\otimes_k\overline{k}
=M_d(\overline{k}),
$$

but the full matrix algebra preserves no such subspace. This closes the circle.

Condition (4) is particularly useful because it is expressed solely in character values:

$$
\operatorname{tr}(\sigma(g_i)\sigma(g_j))
=\chi_\sigma(g_ig_j).
$$

Absolute irreducibility can therefore be certified by one finite determinant of traces. For a lift over a local ring, the same determinant is a unit exactly when its residual value is nonzero. The density property is thus stable under every infinitesimal thickening: the chosen matrices remain a basis without having to repeat an irreducibility argument upstairs.

There is also a centralizer test, but it must be used carefully. Absolute irreducibility implies that the centralizer is $k$. The converse can fail over nonclosed fields or for nonsemisimple families: a scalar commutant alone need not force the generated algebra to be the full matrix algebra. The Gram determinant criterion has no such ambiguity and is the preferred finite test in this book.

## 5. Trace coordinates and matrix generation

### 5.1 The trace pairing

For a commutative ring $R$, the matrix algebra $M_d(R)$ carries the bilinear form

$$
\langle x,y\rangle=\operatorname{tr}(xy).
$$

Over a field this form is nondegenerate. Indeed, with $e_{ij}$ denoting the standard matrix units,

$$
\operatorname{tr}(e_{ij}e_{\ell m})
=\delta_{jm}\delta_{i\ell}.
$$

Thus $e_{ji}$ is dual to $e_{ij}$. The same calculation shows that the map

$$
M_d(R)\longrightarrow\operatorname{Hom}_R(M_d(R),R),
\qquad x\longmapsto(y\mapsto\operatorname{tr}(xy))
$$

is an isomorphism over every commutative ring. Nondegeneracy of the full matrix trace pairing never requires $d$ to be invertible.

If $x_1,\ldots,x_{d^2}$ is a basis, its trace Gram matrix is

$$
\Gamma=(\operatorname{tr}(x_ix_j))_{i,j}.
$$

The basis has a trace-dual basis exactly when $\det\Gamma$ is a unit. Over a local ring it is enough that the reduced Gram determinant be nonzero in the residue field.

### 5.2 Choosing a residual group basis

Let $A$ be pro-Artinian local and let

$$
\rho:G\longrightarrow\operatorname{GL}_d(A)
$$

have absolutely irreducible reduction. Absolute density gives elements

$$
g_1,\ldots,g_{d^2}\in G
$$

such that

$$
\bar x_i=\bar\rho(g_i)
$$

form a basis of $M_d(k)$. Put $x_i=\rho(g_i)$.

The $x_i$ form an $A$-basis of $M_d(A)$. To see this, write them in the standard matrix-unit basis. The determinant of the resulting $d^2\times d^2$ coordinate matrix reduces to a nonzero element of $k$, hence is a unit of $A$. Its inverse gives the required change of basis.

Their Gram entries have the special form

$$
\Gamma_{ij}=\operatorname{tr}(x_ix_j)
=\operatorname{tr}\rho(g_ig_j).
$$

They therefore lie in the trace algebra $T_\rho$. Reduction of $\Gamma$ is the Gram matrix of a basis for the nondegenerate trace pairing on $M_d(k)$, so $\det\Gamma$ has nonzero residue. It is a unit not only in $A$ but in the local ring $T_\rho$.

This is the key point where density and invariant theory meet. Density chooses a matrix basis made of group elements; the group law ensures that every entry of its Gram matrix is a trace value.

### 5.3 The dual-basis calculation

Set $B=T_\rho$ and write $\Gamma^{-1}=(\gamma^{ij})$. Since $\det\Gamma\in B^\times$, every $\gamma^{ij}$ lies in $B$. Define

$$
x_i^\vee=\sum_j\gamma^{ij}x_j.
$$

After choosing the indexing convention so that rows of $\Gamma^{-1}$ act on columns of $\Gamma$, these elements satisfy

$$
\operatorname{tr}(x_i^\vee x_\ell)=\delta_{i\ell}.
$$

For any $y\in M_d(A)$, trace duality gives the coordinate identity

$$
y=\sum_i\operatorname{tr}(yx_i^\vee)x_i.
$$

Apply this to $y=\rho(g)$. Its $i$th coordinate is

$$
c_i(g)=\operatorname{tr}(\rho(g)x_i^\vee)
=\sum_j\gamma^{ij}\operatorname{tr}\rho(gg_j).
$$

Every term lies in $B$. Therefore

$$
\rho(g)=\sum_{i=1}^{d^2}c_i(g)x_i
\quad\text{with }c_i(g)\in B.
$$

This formula is the engine of the entire descent theorem. It does not claim that the entries of $x_i$ lie in $B$; generally they do not. Instead it says that every group matrix is a $B$-linear combination of one fixed finite list of group matrices. Those matrices form a twisted model of the full matrix algebra over $B$.

### 5.4 The trace-generation theorem

We record the calculation in a reusable form.

**Theorem (Burnside--density trace generation).** Let $B\subseteq A$ be a local subring with the same residue field $k$, and let $\rho:G\to\operatorname{GL}_d(A)$ have absolutely irreducible reduction. Assume

$$
\operatorname{tr}\rho(g)\in B\qquad(g\in G).
$$

Then there exist $g_1,\ldots,g_{d^2}\in G$ such that, writing $x_i=\rho(g_i)$:

1. the $x_i$ form an $A$-basis of $M_d(A)$;
2. every $\rho(g)$ has a unique expression

   $$
   \rho(g)=\sum_i c_i(g)x_i,
   \qquad c_i(g)\in B;
   $$

3. the $B$-span

   $$
   E=\sum_iBx_i
   $$

   contains $\rho(G)$ and is closed under multiplication;
4. $E$ is free of rank $d^2$ over $B$, and the scalar-extension map

   $$
   E\otimes_BA\longrightarrow M_d(A)
   $$

   is an isomorphism.

**Proof.** The first two assertions are Sections 5.2 and 5.3. Since $x_ix_j=\rho(g_ig_j)$, the second assertion puts every product of basis elements in $E$, so $E$ is an algebra. The $x_i$ are $B$-linearly independent because they are $A$-linearly independent. They therefore form a $B$-basis of $E$. After scalar extension they remain the displayed $A$-basis, proving the last assertion. $\square$

The theorem is a trace-generation theorem in a stronger sense than generation of a commutative ring by trace values. It says those values determine the structure constants of a full rank-$d^2$ noncommutative algebra. That algebra is the bridge between invariant coefficients and matrix entries.

### 5.5 Consequences for centralizers and characters

The same basis immediately controls centralizers.

**Corollary.** Under the hypotheses of the theorem, the centralizer of $\rho(G)$ in $M_d(A)$ is $A\cdot I$.

**Proof.** An element commuting with $\rho(G)$ commutes with every $x_i$ and hence, because the $x_i$ form an $A$-basis, with every element of $M_d(A)$. The center of the full matrix algebra consists of scalar matrices. $\square$

Likewise, if two field-valued representations have the same character and one is absolutely irreducible, choose the group basis for the first. The Gram matrix for the corresponding matrices of the second is identical, hence those matrices are also a basis. The trace-coordinate formula sends every matrix of the first representation to the corresponding matrix of the second and preserves multiplication because

$$
\rho(g)\rho(h)=\rho(gh),
\qquad
\tau(g)\tau(h)=\tau(gh).
$$

It extends to an automorphism of $M_d(k)$, which Chapter 8 will show is inner. This completes the character-rigidity claim of Section 3.5.

### 5.6 Why no division is needed

Newton identities often express characteristic-polynomial coefficients in terms of traces only after division by integers. That route becomes unreliable when the residue characteristic divides one of those integers. The trace-coordinate method avoids it completely.

The only inverse taken is $\Gamma^{-1}$. Its determinant is a unit because its reduction is the Gram determinant of a basis for a perfect pairing. This is an invertibility statement intrinsic to the full matrix algebra, independent of the characteristic. Thus the descent theorem is not restricted by conditions such as $d!\in A^\times$.

### 5.7 Independence of the chosen group basis

The construction began by choosing group elements $g_1,\ldots,g_{d^2}$. Neither the resulting algebra $E$ nor the descended coefficient ring depends on that choice.

Let $h_1,\ldots,h_{d^2}$ be another family whose residual matrices form a basis, and set $y_j=\rho(h_j)$. The trace-coordinate theorem applied to the $x_i$ gives

$$
y_j=\sum_i a_{ij}x_i,
\qquad a_{ij}\in B.
$$

Applied in the other direction it gives

$$
x_i=\sum_j b_{ji}y_j,
\qquad b_{ji}\in B.
$$

Therefore

$$
\sum_iBx_i=\sum_jBy_j.
$$

The change-of-basis matrices $(a_{ij})$ and $(b_{ji})$ are inverse. Their reductions are ordinary changes between two bases of $M_d(k)$, so their determinants are units of $B$.

There is also an intrinsic description:

$$
E=\sum_{g\in G}B\rho(g).
$$

The right side appears to allow an infinite sum, but the theorem says it is already generated by $d^2$ carefully chosen terms. Thus $E$ is the $B$-linear envelope of the group image, independent of every auxiliary choice. Its multiplication, trace, center, and embedding into $M_d(A)$ are consequently canonical; only a later choice of splitting $E\cong M_d(B)$ is noncanonical.

The trace-dual basis itself changes contragrediently. If $y_j=\sum_i a_{ij}x_i$, then

$$
y_j^\vee=\sum_i(a^{-1})_{ji}x_i^\vee.
$$

Hence the coordinate vector of a matrix changes by the inverse basis matrix, exactly as ordinary linear algebra predicts. Trace generation is not tied to a lucky Gram matrix; every residual group basis produces the same finite free algebra.

### 5.8 A rank-two coordinate calculation

In rank two, one can watch the trace mechanism operate with four matrices. Suppose $x_1,x_2,x_3,x_4\in\rho(G)$ reduce to a basis of $M_2(k)$. Form

$$
\Gamma=
\begin{pmatrix}
\operatorname{tr}(x_1x_1)&\cdots&\operatorname{tr}(x_1x_4)\\
\vdots&\ddots&\vdots\\
\operatorname{tr}(x_4x_1)&\cdots&\operatorname{tr}(x_4x_4)
\end{pmatrix}.
$$

Every entry is the trace of one group element because $x_i=\rho(g_i)$. Let $D=\det\Gamma$. The residual basis condition gives $D\in B^\times$. The inverse is

$$
\Gamma^{-1}=D^{-1}\operatorname{adj}(\Gamma),
$$

so its entries are visibly in the trace algebra: the adjugate entries are polynomials in pairwise trace values and $D^{-1}$ belongs to the local ring $B$.

For $y=\rho(g)$, set

$$
t(y)=
\begin{pmatrix}
\operatorname{tr}(yx_1)\\
\operatorname{tr}(yx_2)\\
\operatorname{tr}(yx_3)\\
\operatorname{tr}(yx_4)
\end{pmatrix}
=
\begin{pmatrix}
\operatorname{tr}\rho(gg_1)\\
\operatorname{tr}\rho(gg_2)\\
\operatorname{tr}\rho(gg_3)\\
\operatorname{tr}\rho(gg_4)
\end{pmatrix}.
$$

If $c(y)$ is the column of coefficients in $y=\sum_i c_i(y)x_i$, then

$$
t(y)=\Gamma^{\mathsf T}c(y).
$$

The Gram matrix is symmetric because $\operatorname{tr}(x_ix_j)=\operatorname{tr}(x_jx_i)$, so

$$
c(y)=\Gamma^{-1}t(y)\in B^4.
$$

This is a literal finite algorithm: record sixteen traces to invert the Gram matrix, then four translated traces for each new group element. No eigenvectors and no matrix entries are used.

For a product $x_ix_j$, the same computation gives its four structure constants. Associativity of those constants need not be checked by a separate system of equations; it is inherited from multiplication in $M_2(A)$. Once the four basis matrices are fixed, the character determines the entire multiplication table of their $B$-span.

One may wonder whether traces of only $g$, rather than all translates $gg_i$, suffice. They do, because $g$ ranges over the whole group and every $g_i$ is fixed: $gg_i$ is again a group element. The coordinate functions do not require extra invariant data beyond the original character.

## 6. The algebra generated over the trace ring

### 6.1 Constructing the finite free algebra

Retain $B=T_\rho$ and the group basis $x_1,\ldots,x_{d^2}$. Define

$$
E=B x_1+\cdots+B x_{d^2}\subseteq M_d(A).
$$

The trace-generation theorem says that $E$ is a unital $B$-algebra, finite free of rank $d^2$, containing every $\rho(g)$. The identity belongs to $E$ because it is $\rho(1)$; it need not be one of the chosen basis elements.

The topology on $E$ is the product topology transported from $B^{d^2}$ by the chosen basis. This agrees with the topology induced from $M_d(A)$. Indeed the coordinate functionals

$$
y\longmapsto\operatorname{tr}(yx_i^\vee)
$$

are continuous, so convergence of matrices in $E$ is equivalent to coordinatewise convergence in $B$. In particular $E$ is complete and closed in $M_d(A)$.

This agreement is a useful strictness statement. It ensures that reducing $E$ modulo an open ideal of $B$ gives the same finite algebra as taking the corresponding coordinates modulo that ideal; no hidden completion is introduced.

### 6.2 Multiplication and scalar extension

The multiplication constants of $E$ lie in $B$. Explicitly,

$$
x_ix_j=\sum_\ell m_{ij}^{\ell}x_\ell,
$$

where

$$
m_{ij}^{\ell}
=\operatorname{tr}(x_ix_jx_\ell^\vee)
=\sum_s\gamma^{\ell s}
\operatorname{tr}\rho(g_ig_jg_s).
$$

Every coefficient is a $B$-linear combination of trace values. Thus the entire multiplication table is invariantly defined over the trace ring, even if none of the chosen matrices is entrywise $B$-valued in the original basis.

Once these constants are known, $E$ could be reconstructed abstractly as the free module with basis symbols $X_i$ and products

$$
X_iX_j=\sum_\ell m_{ij}^{\ell}X_\ell.
$$

The associativity identities among the $m_{ij}^{\ell}$ hold because they hold after embedding in $M_d(A)$. The identity element has coordinates obtained by applying the same trace formula to $\rho(1)$. Thus the character determines not only a module but a unital associative algebra together with distinguished elements representing every $g\in G$.

This reconstruction also explains why it is unsafe to select arbitrary $d^2$ matrices with traces in $B$. The products must have trace-controlled coordinates. Choosing the matrices from the group makes every product another represented group element and closes the calculation.

The inclusion $E\hookrightarrow M_d(A)$ induces

$$
E\otimes_BA\xrightarrow{\sim}M_d(A).
$$

This is not an appeal to flatness of $A$ over $B$. Both sides have the explicit $A$-basis given by the images of the $x_i$, so the map is directly an isomorphism.

Moreover the representation factors as

$$
G\longrightarrow E^\times\longrightarrow M_d(A)^\times.
$$

An element $\rho(g)$ is a unit in $E$: its inverse is $\rho(g^{-1})$, which also lies in $E$. Hence the algebra $E$ already contains the group action before it is split. The rest of the proof changes the realization of $E$, not the abstract representation into its unit group.

### 6.3 The Azumaya criterion

A finite projective algebra $E$ over a commutative ring $B$ is **Azumaya** if the natural map

$$
\mu:E\otimes_BE^{\mathrm{op}}
\longrightarrow\operatorname{End}_B(E),
\qquad
a\otimes b\longmapsto(x\mapsto axb)
$$

is an isomorphism. This condition says that, locally on the coefficient ring, $E$ has the internal algebraic behavior of a full matrix algebra. It is stronger than having the correct rank and weaker than having already chosen a splitting.

**Theorem.** The trace-generated algebra $E$ is Azumaya over $B$.

**Proof strategy.** Both sides of $\mu$ are free of rank $d^4$. Reduce modulo the maximal ideal. The special fiber of $E$ is the full matrix algebra, for which left and right multiplication generate all endomorphisms. Nakayama then lifts the isomorphism.

**Proof.** Reduction of the basis $x_i$ identifies

$$
E/\mathfrak m_BE\cong M_d(k).
$$

For $M_d(k)$, the map

$$
M_d(k)\otimes_kM_d(k)^{\mathrm{op}}
\longrightarrow\operatorname{End}_k(M_d(k))
$$

is an isomorphism. One can see this on matrix units: left multiplication by $e_{ia}$ and right multiplication by $e_{bj}$ sends $e_{ab}$ to $e_{ij}$ and annihilates the other matrix units after the appropriate indices are fixed. These operators span all elementary endomorphisms.

More explicitly, define

$$
T_{pq,ab}(x)=e_{pa}xe_{bq}.
$$

On a matrix unit $e_{ij}$,

$$
T_{pq,ab}(e_{ij})
=\delta_{ai}\delta_{jb}e_{pq}.
$$

Thus $T_{pq,ab}$ is the elementary linear operator that reads the $(a,b)$ coordinate and writes it into the $(p,q)$ coordinate. As the four indices vary, these $d^4$ operators form a basis of

$$
\operatorname{End}_k(M_d(k)).
$$

Each is the image of $e_{pa}\otimes e_{bq}$ under the left-right multiplication map, proving both surjectivity and injectivity without a dimension shortcut.

Hence $\mu$ is an isomorphism modulo $\mathfrak m_B$. Relative to finite free bases, its determinant has nonzero residue and is therefore a unit of $B$. Thus $\mu$ itself is an isomorphism. $\square$

This proof uses only finite freeness and locality. It remains valid when $B$ is pro-Artinian but not Noetherian.

### 6.4 The center and the centralizer

An Azumaya algebra has center exactly its base ring. Here this can also be seen directly. If $z\in E$ is central, its image in

$$
E\otimes_BA\cong M_d(A)
$$

is scalar, say $aI$. Write

$$
I=\sum_i b_ix_i,
\qquad
z=\sum_i c_ix_i,
\qquad b_i,c_i\in B.
$$

The reduced identity is nonzero, so at least one $b_i$ has nonzero residue and is a unit of $B$. Since the $x_i$ are an $A$-basis, the equality $z=aI$ gives $c_i=ab_i$ for every $i$. For an index with $b_i\in B^\times$, this yields $a=c_ib_i^{-1}\in B$. Thus

$$
Z(E)=B.
$$

The centralizer of $E$ in $M_d(A)$ is $A\cdot I$. Indeed $E$ contains $\rho(G)$, and Section 5.5 computed the centralizer of that group as the scalar matrices. This scalar-centralizer statement will make conjugating matrices unique modulo $A^\times$.

### 6.5 Finite quotients and base change

Let $I\subseteq B$ be an open ideal. Then

$$
E_I=E/IE
$$

is free of rank $d^2$ over $B/I$, and Azumaya formation commutes with this quotient. Its special fiber is still $M_d(k)$. If $B\to C$ is any coefficient map, then

$$
E_C=E\otimes_BC
$$

is Azumaya over $C$ because the defining multiplication map is obtained from $\mu$ by scalar extension.

In particular $E_A\cong M_d(A)$ is a chosen splitting after the large coefficient extension. The remaining question is whether $E$ already splits over $B$. A general Azumaya algebra need not split globally, but the local Henselian setting and the split special fiber eliminate the obstruction.

### 6.6 Azumaya algebras, orders, and a boundary

It is useful to distinguish three increasingly strong properties of a finite $B$-algebra $F$ of rank $d^2$:

1. $F$ becomes $M_d(A)$ after some scalar extension $B\to A$;
2. $F$ is Azumaya over $B$;
3. $F$ is already isomorphic to $M_d(B)$.

The first property alone is not enough for descent. A nonmaximal order in a split central simple algebra may become the full matrix algebra after inverting a parameter while having a singular special fiber. For example, over a discrete valuation ring $B$ with uniformizer $\pi$, the subalgebra

$$
F=
\left\{
\begin{pmatrix}
a&b\\
\pi c&d
\end{pmatrix}:a,b,c,d\in B
\right\}
\subseteq M_2(B)
$$

becomes $M_2(\operatorname{Frac}B)$ after inverting $\pi$, but its special fiber is triangular rather than $M_2(k)$. Its left-right multiplication map is not an isomorphism, so $F$ is not Azumaya.

Azumaya algebras exclude this degeneration. Their fibers are central simple and their multiplication remains nondegenerate in every direction. Yet an Azumaya algebra need not be globally split: over a field, a nonsplit central division algebra is Azumaya. The third property therefore needs additional information.

For the trace-generated $E$, reduction supplies exactly that information. Its special fiber is not merely central simple but explicitly $M_d(k)$. The Henselian local base lets this residual splitting lift. Both adjectives matter: on a nonlocal base the lifted rank-one summand can be a nonfree projective module, while without Henselian completeness the residual projector need not lift.

### 6.7 Morita intuition and the splitting module

Why should a rank-one idempotent split a matrix-like algebra? In $M_d(B)$, the idempotent $e_{11}$ cuts out the left ideal

$$
M_d(B)e_{11},
$$

the matrices supported in the first column. Forgetting matrix multiplication, this is simply $B^d$. Left multiplication gives every endomorphism of that column module:

$$
M_d(B)\xrightarrow{\sim}
\operatorname{End}_B(M_d(B)e_{11}).
$$

The column remembers the whole matrix algebra because a matrix is determined by what it does to column vectors.

An Azumaya algebra $E$ is a matrix algebra without a chosen column module. A rank-one idempotent $e$ supplies one:

$$
P=Ee.
$$

The word “rank one” refers to the idempotent inside the matrix algebra; the resulting $B$-module $P$ has rank $d$. The Azumaya property ensures that left multiplication is locally as large as possible, while the residual calculation verifies it is exactly all of $\operatorname{End}_B(P)$.

Over a local ring, $P$ is free and a choice of basis gives $E\cong M_d(B)$. Over a general ring, $P$ can be projective but not free. Then

$$
E\cong\operatorname{End}_B(P)
$$

is already a splitting in the geometric sense, but it may not be a literal matrix algebra globally. Thus the local hypothesis does two jobs: it detects units by residue and turns the splitting module into a free module.

Different lifted rank-one idempotents can give different-looking modules and different splittings. In a split Azumaya algebra they are locally conjugate, and over a local base the resulting matrix splittings differ by inner automorphism. This nonuniqueness is exactly what Skolem--Noether manages; it is not a defect of Henselian lifting.

## 7. Henselian lifting and splitting

### 7.1 Why a split special fiber should split the algebra

The special fiber $E\otimes_Bk$ is $M_d(k)$. It contains rank-one projectors, for example $e_{11}$. If one can lift such a projector to an idempotent $e\in E$, then the left ideal $Ee$ behaves like the column module $B^d$. The left action of $E$ on $Ee$ should identify $E$ with $\operatorname{End}_B(Ee)$, producing a splitting.

Trying instead to lift all $d^2$ matrix entries of a splitting at once would create a large coupled system of quadratic equations. The rank-one projector isolates the essential datum. Once it lifts, projective-module structure recovers every other matrix direction automatically. This is a recurring Henselian strategy: lift a rigid geometric object with an invertible linearization, then reconstruct the surrounding structure from it.

The word **Henselian** describes the principle that a solution modulo the maximal ideal lifts when its linearized obstruction is invertible. For idempotents the equation is $X^2-X=0$, whose derivative at $0$ or $1$ is a unit. In a pro-Artinian ring it is most transparent to lift through nilpotent finite stages and take a compatible limit.

The projector must have residual rank one. Lifting the identity idempotent would give $E$ itself as a module and reveal no splitting; lifting a higher-rank projector would yield a larger projective summand whose endomorphism algebra has the wrong rank. The minimal nonzero projector is the algebraic substitute for choosing one column of an unknown matrix realization.

### 7.2 Lifting idempotents through nilpotent ideals

We need a noncommutative version because $E$ is not commutative.

**Lemma (idempotent lifting).** Let $R$ be an associative ring and $I\subseteq R$ a nilpotent two-sided ideal. Every idempotent in $R/I$ lifts to an idempotent in $R$.

**Proof strategy.** First handle a square-zero ideal by correcting an arbitrary lift. Then factor a nilpotent ideal through the successive square-zero layers $I^j/I^{j+1}$.

**Proof.** Suppose first $I^2=0$. Let $a$ lift an idempotent, so $q=a^2-a\in I$. Because $q$ is a polynomial in $a$, it commutes with $a$. Seek a correction $t\in I$ commuting with $a$. Since $I^2=0$,

$$
(a+t)^2-(a+t)=q+(2a-1)t.
$$

The element $(2a-1)^2=1+4q$ is a unit: $4q$ is square-zero, so $1+4q$ has inverse $1-4q$. Hence $2a-1$ is a unit. Taking

$$
t=-(2a-1)^{-1}q
$$

gives an idempotent lift. No division by $2$ occurs.

For general nilpotent $I$, choose $N$ with $I^N=0$ and lift successively through

$$
R/I^N\to R/I^{N-1}\to\cdots\to R/I.
$$

The kernel at the step from $R/I^{j+1}$ to $R/I^j$ is $I^j/I^{j+1}$, whose square is zero because $2j\geq j+1$ for $j\geq1$. Repeated application of the square-zero case completes the lift. $\square$

The formula also shows why idempotents are stable: the linear operator $2a-1$ governing correction is automatically invertible near an idempotent.

### 7.3 Compatible lifting in a pseudocompact ring

Let $R=\varprojlim R_r$ be a countable inverse limit with surjective maps and nilpotent transition kernels. Given an idempotent $e_1\in R_1$, construct $e_{r+1}$ inductively. If $e_r$ has been chosen, the idempotent-lifting lemma applied to $R_{r+1}\to R_r$ produces an idempotent mapping to it. The compatible family defines an idempotent

$$
e=(e_r)_r\in R.
$$

For a pro-Artinian local base $B$ and a finite $B$-algebra $E$, use the quotients $E/I_rE$. The transition kernels are nilpotent because they lie over nilpotent ideals in Artinian coefficient rings. Consequently every idempotent of the special fiber $E/\mathfrak m_BE$ has a compatible lift to $E$.

To make the last sentence precise, enlarge the tower by placing $B/\mathfrak m_B=k$ at its beginning. For a transition $B_{r+1}\twoheadrightarrow B_r$ with kernel $K_r$, the ideal $K_r$ is nilpotent because it lies in the maximal ideal of the Artinian ring $B_{r+1}$. The kernel of

$$
E\otimes_BB_{r+1}\longrightarrow E\otimes_BB_r
$$

is $K_r(E\otimes_BB_{r+1})$, whose $N$th power vanishes whenever $K_r^N=0$. The noncommutative idempotent-lifting lemma therefore applies at every step.

The compatible family lies in

$$
\varprojlim_rE/I_rE\cong E
$$

because $E$ is finite free over the complete ring $B$: in a chosen basis, this reconstruction is simply the product of $d^2$ copies of $B\cong\varprojlim B/I_r$. No separate exactness theorem is concealed here.

This is the Henselian lifting principle needed here. Completeness supplies the limiting element; separation makes it unique once all its finite residues are fixed. The lift itself is not unique, but any one lift will split the algebra.

### 7.4 A lifted rank-one projector

Choose an identification

$$
\bar E=E/\mathfrak m_BE\cong M_d(k)
$$

and let $\bar e$ correspond to $e_{11}$. Lift it to an idempotent $e\in E$. Then

$$
P=Ee
$$

is a direct summand of the finite free $B$-module $E$, since right multiplication by $e$ is an idempotent endomorphism of $E$ with image $Ee$. Hence $P$ is finite projective over $B$.

Its special fiber is

$$
P\otimes_Bk\cong M_d(k)e_{11}\cong k^d.
$$

Finite projective modules over a local ring are free. For completeness, choose $d$ elements of $P$ lifting a basis of $P/\mathfrak m_BP$. They define a surjection $B^d\to P$ by Nakayama. Since $P$ is projective, the kernel is a direct summand; reducing modulo $\mathfrak m_B$ makes that kernel zero, and Nakayama makes it zero. Thus

$$
P\cong B^d.
$$

### 7.5 Splitting the Azumaya algebra

Left multiplication gives a $B$-algebra map

$$
\lambda:E\longrightarrow\operatorname{End}_B(P).
$$

Modulo $\mathfrak m_B$, this is the standard action

$$
M_d(k)\longrightarrow
\operatorname{End}_k(M_d(k)e_{11})
\cong M_d(k),
$$

which is an isomorphism. Both source and target are finite free of rank $d^2$. Therefore the determinant of $\lambda$ is a unit, and $\lambda$ is an isomorphism.

Choosing a $B$-basis of $P$ gives the desired splitting

$$
E\xrightarrow{\sim}M_d(B).
$$

We have proved the precise local splitting theorem used in descent.

**Theorem (Henselian splitting).** Let $B$ be pro-Artinian local with a countable cofinal tower, and let $E$ be an Azumaya $B$-algebra of rank $d^2$. If

$$
E\otimes_Bk\cong M_d(k),
$$

then

$$
E\cong M_d(B).
$$

The proof explains the theorem's scope. A split special fiber supplies a rank-one projector; Henselian lifting supplies a projector upstairs; locality makes its projective column module free. Over a nonlocal base that module may be only locally free, and the Azumaya algebra may remain nonsplit globally.

### 7.6 What Henselianity is doing

Completeness alone, without a topology controlled by nilpotent finite quotients, would not justify the lifting argument. Locality alone would not produce a compatible limit. The pro-Artinian hypotheses combine the two useful properties:

$$
\text{nilpotent correction at finite level}
\quad+\quad
\text{complete compatible passage to the limit}.
$$

The result can also be viewed as injectivity of specialization on the relevant local Brauer class: an Azumaya algebra with trivial residual class has trivial class. The projector proof is preferable here because it displays the descended module and keeps every hypothesis visible.

### 7.7 Hensel's lemma behind the projector argument

The idempotent calculation is one instance of a broader lifting principle. Let $(R,\mathfrak m)$ be complete and separated for a topology whose finite quotients have nilpotent maximal ideals. Suppose $f(X)\in R[X]$ and $a_0\in R$ satisfy

$$
f(a_0)\in\mathfrak m,
\qquad
f'(a_0)\in R^\times.
$$

Then there is a unique $a\equiv a_0\pmod{\mathfrak m}$ with $f(a)=0$, provided the successive corrections are taken through the chosen pro-Artinian tower.

At a square-zero lifting step with kernel $I$, suppose $a$ solves the equation downstairs and $\widetilde a$ is any lift. Seek $\widetilde a+t$ with $t\in I$. Taylor expansion terminates after the linear term:

$$
f(\widetilde a+t)=f(\widetilde a)+f'(\widetilde a)t,
$$

because $I^2=0$. The derivative is a unit, so there is a unique correction

$$
t=-f'(\widetilde a)^{-1}f(\widetilde a).
$$

Factor a nilpotent kernel into square-zero layers and repeat. Compatible solutions converge to a solution in $R$. If two solutions have the same reduction, their difference is forced into every open ideal by the same linearized argument, so separation gives uniqueness.

For $f(X)=X^2-X$, the derivative is $2X-1$, which is a unit at every idempotent. The noncommutative proof in Section 7.2 works because the error $a^2-a$ commutes with $a$; it is the same Newton correction inside the commutative subring generated by $a$.

Completeness cannot simply be omitted. In $R=k[t]_{(t)}$, the polynomial

$$
X^2-X-t
$$

has the simple root $0$ modulo $t$, but a root would require $\sqrt{1+4t}$ in the fraction field, which is absent in general. The $t$-adic completion contains the corresponding binomial series when the characteristic permits the displayed expansion. This example shows what compatible infinite correction adds to a local ring.

### 7.8 Lifting a complete system of matrix units

The projector proof is economical, but a fuller picture can be obtained by lifting all matrix units. Suppose $e\in E$ lifts $e_{11}$ and put $P=Ee$. Choose a basis $p_1,\ldots,p_d$ of $P$ lifting the standard residual column basis. Under

$$
E\xrightarrow{\sim}\operatorname{End}_B(P),
$$

let $e_{ij}'$ be the endomorphism sending $p_j$ to $p_i$ and every other $p_\ell$ to zero. Pulling these endomorphisms back to $E$ gives

$$
e_{ij}'e_{\ell m}'=\delta_{j\ell}e_{im}',
\qquad
\sum_i e_{ii}'=1.
$$

After adjusting the chosen basis residually, the $e_{ij}'$ reduce to the standard $e_{ij}$. Thus one rank-one idempotent plus a basis of its column module lifts the entire system of matrix units.

There is also a direct stagewise construction. Lift the diagonal idempotents one at a time, maintaining orthogonality by working in the complementary corner $(1-e)E(1-e)$. Once $e_{11},\ldots,e_{dd}$ are lifted, each corner

$$
e_{ii}Ee_{jj}
$$

is a rank-one projective $B$-module. Choose lifts of the residual off-diagonal units in these corners and rescale them so that

$$
e_{ij}e_{ji}=e_{ii}.
$$

Compatibility of the triple products then yields a full matrix-unit system. The column-module proof packages these normalizations more cleanly and avoids a long induction on pairs of indices.

The matrix units make the splitting completely explicit:

$$
M_d(B)\longrightarrow E,
\qquad (a_{ij})\longmapsto\sum_{i,j}a_{ij}e_{ij}'.
$$

Multiplication relations show that this is an algebra homomorphism, and reduction or comparison of finite free ranks makes it an isomorphism. In applications where individual projectors carry additional meaning, this explicit form can be preferable to the abstract endomorphism-algebra description.

## 8. Skolem--Noether over a local base

### 8.1 The conjugacy problem for two splittings

Splitting $E$ abstractly is not yet descent. We have two realizations after extending to $A$:

1. the original inclusion $E\hookrightarrow M_d(A)$;
2. a chosen isomorphism $E\cong M_d(B)$, followed by scalar extension to $M_d(A)$.

Their comparison is an $A$-algebra automorphism of $M_d(A)$. To obtain a basis change, one must prove that every such automorphism is inner. Over a field this is the classical Skolem--Noether theorem. Over a local ring it has an elementary proof using matrix units and rank-one summands.

### 8.2 Matrix units over a local ring

Let $R$ be local and let $\varphi$ be an $R$-algebra automorphism of $M_d(R)$. Put

$$
f_{ij}=\varphi(e_{ij}).
$$

They satisfy

$$
f_{ij}f_{\ell m}=\delta_{j\ell}f_{im},
\qquad
\sum_i f_{ii}=1.
$$

Thus

$$
R^d=\bigoplus_i P_i,
\qquad P_i=f_{ii}R^d.
$$

Each $P_i$ is finite projective. The maps $f_{i1}:P_1\to P_i$ and $f_{1i}:P_i\to P_1$ are inverse, so all $P_i$ have the same rank. Their direct sum has rank $d$, hence each has rank one. Since $R$ is local, each $P_i$ is free of rank one.

Choose a generator $v_1$ of $P_1$ and set

$$
v_i=f_{i1}v_1.
$$

Then $v_i$ generates $P_i$, the $v_i$ form a basis of $R^d$, and

$$
f_{ij}v_\ell=\delta_{j\ell}v_i.
$$

If $u$ is the matrix whose $i$th column is $v_i$, this identity says

$$
f_{ij}=u e_{ij}u^{-1}.
$$

### 8.3 The local Skolem--Noether theorem

**Theorem (local Skolem--Noether).** Let $R$ be a commutative local ring. Every $R$-algebra automorphism $\varphi$ of $M_d(R)$ is inner: there is $u\in\operatorname{GL}_d(R)$ such that

$$
\varphi(x)=uxu^{-1}
\qquad(x\in M_d(R)).
$$

**Proof.** The preceding construction gives the formula on every matrix unit. Since the matrix units form an $R$-basis, it holds for every matrix. $\square$

No completeness is needed. Locality is the point: it turns each rank-one projective summand into a free summand with a chosen generator.

The theorem concerns algebra automorphisms that fix $R$ pointwise. If one allows automorphisms of the underlying ring that act nontrivially on $R$, coefficient automorphisms appear in addition to conjugation. Descent compares two $A$-algebra structures and therefore lies exactly in the inner case.

Nor does the theorem assert a preferred implementing matrix. The proof chooses a generator of $P_1$; changing that generator by $a\in R^\times$ multiplies every $v_i$ and hence $u$ by $a$. Section 8.4 shows that this visible ambiguity is the only one.

### 8.4 Uniqueness modulo scalars

If $u$ and $v$ implement the same automorphism, then $v^{-1}u$ commutes with every matrix. The centralizer of $M_d(R)$ inside itself is $R\cdot I$, so

$$
u=a v
$$

for a unique $a\in R^\times$. Thus the implementing conjugator is unique up to multiplication by a scalar unit.

Equivalently,

$$
\operatorname{Aut}_{R\text{-alg}}(M_d(R))
\cong\operatorname{PGL}_d(R).
$$

For descent, scalar ambiguity is helpful: it permits normalization of the residual value of a conjugator without changing the induced conjugacy.

### 8.5 Residual normalization

Suppose an automorphism $\varphi$ reduces to the identity on $M_d(k)$. If $u$ implements it, then $\bar u$ commutes with all of $M_d(k)$ and hence is scalar:

$$
\bar u=\lambda I,
\qquad \lambda\in k^\times.
$$

Choose $a\in R^\times$ lifting $\lambda^{-1}$. The scalar multiple $au$ implements the same automorphism and satisfies

$$
au\equiv I\pmod{\mathfrak m_R}.
$$

Therefore an automorphism that is residually the identity is implemented by a strict matrix. This small normalization step is what preserves a prescribed residual basis in Carayol descent.

### 8.6 Conjugacy of two embeddings

The automorphism theorem has a form tailored to descent. Let $E$ be a $B$-algebra and suppose

$$
\iota_1,\iota_2:E\xrightarrow{\sim}M_d(B)
$$

are two $B$-algebra isomorphisms. Then

$$
\iota_2\circ\iota_1^{-1}
$$

is an automorphism of $M_d(B)$, so there exists $u\in\operatorname{GL}_d(B)$ with

$$
\iota_2(e)=u\iota_1(e)u^{-1}
\qquad(e\in E).
$$

The matrix $u$ is unique modulo $B^\times$. If the two embeddings agree after reduction, $u$ may be chosen congruent to the identity.

More generally, suppose $E$ is Azumaya and $\iota_1,\iota_2:E\to M_d(B)$ are embeddings that become isomorphisms on the special fiber. Both source and target are finite free of rank $d^2$. Each embedding has unit determinant after choosing bases, so each is already an isomorphism. The preceding conjugacy conclusion applies.

This is precisely the comparison needed later. One realization of $E$ comes from the original matrices; another comes from a lifted rank-one module. They are not expected to be equal, because they encode different bases. Skolem--Noether says the discrepancy is exactly a basis transformation and nothing more exotic.

### 8.7 The module-theoretic form

Let $V$ and $W$ be free $R$-modules of rank $d$, where $R$ is local, and suppose

$$
\Phi:\operatorname{End}_R(V)
\xrightarrow{\sim}\operatorname{End}_R(W)
$$

is an $R$-algebra isomorphism. Then there is an $R$-module isomorphism $u:V\to W$ such that

$$
\Phi(f)=ufu^{-1}
\qquad(f\in\operatorname{End}_R(V)).
$$

To prove this, choose bases of $V$ and $W$, identify both endomorphism algebras with $M_d(R)$, and apply local Skolem--Noether. Changing either chosen basis merely changes the implementing matrix by the corresponding pre- or postcomposition, so the statement itself is basis-free.

There is a useful reconstruction hidden here. Regard $W$ as a left $\operatorname{End}_R(V)$-module through $\Phi$. Then $W$ is isomorphic to $V\otimes_RL$ for an invertible rank-one module $L$. Over a local ring every such $L$ is free, and choosing its generator gives $W\cong V$. The scalar ambiguity in $u$ is precisely the ambiguity in choosing that generator.

This explains both the theorem and its limitation. Over a nonlocal ring, the line module $L$ need not be free. The endomorphism algebras of $V$ and $V\otimes L$ are canonically isomorphic, yet there may be no globally chosen $u:V\to V\otimes L$. Local Skolem--Noether succeeds because every line bundle over a local spectrum is trivial.

For the descended representation, the splitting module $P=Ee$ and the original module $A^d$ become two modules for $E\otimes_BA$. The comparison isomorphism is the basis-free origin of the conjugating matrix. Choosing bases turns it into the $u$ used in Chapter 9.

## 9. Carayol descent

### 9.1 The theorem

We can now state the main result without hiding its topology.

**Theorem (Carayol descent to the closed trace algebra).** Let $\mathcal O$ be a complete Noetherian local coefficient ring with residue field $k$. Let $A$ be a pro-Artinian local $\mathcal O$-algebra with residue field $k$ and a countable cofinal tower of Artinian quotients. Let $G$ be a compact topological group and

$$
\rho:G\longrightarrow\operatorname{GL}_d(A)
$$

a continuous representation whose reduction $\bar\rho$ is absolutely irreducible. Define

$$
B=T_\rho
=\overline{\mathcal O[\operatorname{tr}\rho(g):g\in G]}
\subseteq A.
$$

Then there exists $u\in\operatorname{GL}_d(A)$ such that

$$
u\equiv I\pmod{\mathfrak m_A}
$$

and

$$
\rho_B(g)=u^{-1}\rho(g)u\in\operatorname{GL}_d(B)
\qquad(g\in G).
$$

The descended representation $\rho_B:G\to\operatorname{GL}_d(B)$ is continuous. Its trace algebra is all of $B$, and its reduction is the originally fixed matrix representation $\bar\rho$.

The same conclusion holds with $B$ replaced by any closed local $\mathcal O$-subalgebra of $A$ containing all traces. Taking $B=T_\rho$ gives the minimal such coefficient algebra.

### 9.2 Proof strategy

The proof is a sequence of forced constructions.

1. Absolute density chooses $d^2$ group elements whose residual matrices form a basis of $M_d(k)$.
2. Trace duality shows that every group matrix lies in their $B$-span $E$.
3. The multiplication table of $E$ has coefficients in $B$, and $E\otimes_BA=M_d(A)$.
4. Reduction shows that $E$ is Azumaya with split special fiber.
5. Henselian lifting splits $E$ as $M_d(B)$.
6. The original inclusion and the split realization become two identifications with $M_d(A)$; local Skolem--Noether compares them by conjugacy.
7. A residual adjustment makes the conjugator strict.

Every step has a distinct hypothesis. Absolute irreducibility is used in step 1, trace containment in step 2, locality in steps 2, 4, 5, and 6, completeness in step 5, and closedness in identifying $B$ as a complete inverse limit. Compactness ensures that the representation and trace algebra behave through finite group quotients at every Artinian stage.

### 9.3 Construction of the descended representation

Choose $g_1,\ldots,g_{d^2}$ as in Chapter 5, set $x_i=\rho(g_i)$, and define

$$
E=\sum_iBx_i\subseteq M_d(A).
$$

The trace-generation theorem makes $E$ a finite free $B$-algebra containing $\rho(G)$ and gives

$$
j_A:E\otimes_BA\xrightarrow{\sim}M_d(A),
$$

where $j_A$ is induced by the original inclusion. Chapters 6 and 7 give a $B$-algebra isomorphism

$$
\theta:E\xrightarrow{\sim}M_d(B).
$$

After scalar extension,

$$
\theta_A:E\otimes_BA\xrightarrow{\sim}M_d(A).
$$

The comparison

$$
\alpha=j_A\circ\theta_A^{-1}:M_d(A)\longrightarrow M_d(A)
$$

is an $A$-algebra automorphism. By local Skolem--Noether there is $v\in\operatorname{GL}_d(A)$ with

$$
\alpha(y)=vyv^{-1}.
$$

For $g\in G$, regard $\rho(g)$ as the image under $j_A$ of its element of $E$. Then

$$
v^{-1}\rho(g)v=\theta(\rho(g))\in M_d(B).
$$

The right side is invertible over $B$. Indeed its determinant maps to the unit $\det\rho(g)$ in $A$, so its residue is nonzero; a matrix over a local ring is invertible exactly when its determinant is a unit. Thus

$$
\rho_B(g)=\theta(\rho(g))
$$

defines a homomorphism $G\to\operatorname{GL}_d(B)$.

Continuity deserves an explicit check. The map $E\to M_d(B)$ is an isomorphism between finite pseudocompact modules and is strict: it is recovered from compatible isomorphisms at all finite stages. The original map $G\to E$ is continuous because $E$ has the topology induced from $M_d(A)$. Their composite is therefore continuous.

### 9.4 Strict normalization of the conjugator

The splitting $\theta$ is not initially tied to the chosen residual basis. Reduce the comparison modulo $\mathfrak m_A$. Both

$$
\bar j:\bar E\xrightarrow{\sim}M_d(k)
\quad\text{and}\quad
\bar\theta:\bar E\xrightarrow{\sim}M_d(k)
$$

are splittings of the same full matrix algebra. Their comparison is inner. Choose $w_0\in\operatorname{GL}_d(k)$ implementing it and lift $w_0$ to $w\in\operatorname{GL}_d(B)$. Replacing $\theta$ by

$$
e\longmapsto w\theta(e)w^{-1}
$$

arranges that $\bar\theta=\bar j$.

With this normalized splitting, $\alpha$ reduces to the identity automorphism of $M_d(k)$. Section 8.5 then supplies an implementing matrix $u$ satisfying

$$
u\equiv I\pmod{\mathfrak m_A}.
$$

Replacing $v$ by this $u$ gives the claimed strict conjugation. Because $u$ is the identity residually,

$$
\overline{u^{-1}\rho(g)u}=\bar\rho(g),
$$

so the descended model preserves the specified residual basis rather than merely its isomorphism class.

### 9.5 Minimality of the trace algebra

Suppose $C\subseteq A$ is a closed $\mathcal O$-subalgebra and some conjugate of $\rho$ is $C$-valued. Trace invariance gives

$$
\operatorname{tr}\rho(g)\in C
\qquad(g\in G).
$$

Since $C$ is closed and contains $\mathcal O$, it contains the closed algebra generated by these values:

$$
B=T_\rho\subseteq C.
$$

Thus $T_\rho$ is the smallest closed coefficient algebra over which a conjugate can possibly be defined. Carayol descent proves that this necessary lower bound is attained under residual absolute irreducibility.

One must say “closed.” The algebraic trace algebra may be dense and incomplete. A representation over a complete coefficient ring is not descended merely by producing matrices whose entries are limits of algebraic trace expressions; the limits themselves must belong to the coefficient ring.

### 9.6 Descent at every Artinian level

Let $J_r$ be a cofinal tower of open ideals of $A$ and let

$$
B_r=\operatorname{im}(B\to A/J_r).
$$

The strict conjugator reduces to $u_r\in\operatorname{GL}_d(A/J_r)$, and

$$
u_r^{-1}\rho_r(g)u_r\in\operatorname{GL}_d(B_r).
$$

These descended representations are compatible because they all arise by reducing the single $B$-valued representation $\rho_B$. This is stronger than proving separately that a descent exists at every level. Independent levelwise conjugators need not be compatible; the Azumaya splitting over the inverse limit produces a coherent choice automatically.

Conversely, suppose compatible strict conjugators and compatible $B_r$-valued models are given at every level. Their inverse limits yield a strict conjugator and a $B$-valued model. The compatibility is the essential condition. Nonempty sets of choices at every stage do not by themselves define an inverse-limit choice.

### 9.7 A hypothesis-by-hypothesis audit

The theorem is often applied in a more restrictive complete Noetherian setting, but its proof reveals the exact role of every assumption.

**The common residue field.** The trace Gram determinant is recognized as a unit by one residual calculation, and strictness compares reductions inside the same $M_d(k)$. If $B$ and $A$ have different residue fields, the right conclusion requires a separate residue-field descent problem.

**Closedness of $B$.** Closedness makes $B$ complete for its finite-shadow topology and keeps limits of trace expressions inside it. It is used in Henselian lifting. An algebraic trace subring may be dense and insufficient.

**Locality.** Units are detected residually, finite projective modules become free, and matrix-algebra automorphisms become inner by choosing generators of rank-one summands. On a nonlocal base the natural outcome can be an endomorphism algebra of a nonfree projective module rather than literal matrices on a free module.

**Residual absolute irreducibility.** This is the density input. It forces $d^2$ residual group matrices to span the full matrix algebra and forces centralizers to be scalar. Ordinary irreducibility over $k$ does not suffice.

**Continuity and compactness.** Continuity lets the representation be recovered from Artinian reductions. Compactness makes every such reduction factor through a finite group and makes characters locally constant. The trace-coordinate proof for a fixed abstract representation does not itself use compactness, so the theorem extends to other settings where the required continuity and inverse-limit control are supplied separately.

**A countable cofinal tower.** This permits elementary sequential lifting of idempotents. It is automatic for maximal-adic complete Noetherian rings. With a general directed basis it can be replaced by the corresponding compact inverse-limit or Henselian-pair hypothesis.

**Noetherianity.** It is imposed on the fixed base $\mathcal O$ to keep Artinian coefficient categories controlled, but it is not required of the closed trace ring in the core proof. The finite free algebra $E$, explicit determinant tests, and pro-Artinian Nakayama supply all necessary finiteness.

### 9.8 Rings of definition and their intersection

A closed local subring $C\subseteq A$ is a **ring of definition** for $\rho$ if some $A$-basis makes $\rho$ $C$-valued. Trace invariance gives

$$
T_\rho\subseteq C
$$

for every ring of definition. Carayol descent says that $T_\rho$ itself is a ring of definition. Therefore

$$
T_\rho=\bigcap_C C,
$$

where the intersection runs over closed local $\mathcal O$-subalgebras of $A$ that are rings of definition, and the equality is taken inside $A$. The intersection contains $T_\rho$ by necessity and is contained in it because $T_\rho$ occurs among the terms.

This statement concerns coefficient subrings inside one ambient ring. If two models live in unrelated over-rings, their trace algebras are canonically described by the common character values only after a common coefficient comparison has been specified. “Smallest field of definition” language can hide that embedding issue; the closed-subring formulation does not.

Nor does minimality make the descended model canonical. The ring is canonical as a closed subring of $A$, because traces define it without choices. The splitting of $E$ is not canonical, and different splittings produce strictly conjugate $T_\rho$-valued representations. Thus the correct canonical object is

$$
\bigl(T_\rho,\ [\rho_{T_\rho}]_{\mathrm{strict}}\bigr),
$$

the trace ring together with the strict-conjugacy class of its descended model.

There is a useful monotonicity consequence. If $C$ is any closed coefficient algebra containing $T_\rho$, extend the descended model from $T_\rho$ to $C$. It gives a $C$-valued model without repeating the Azumaya argument. Hence all larger rings of definition lie above one minimal model, and coefficient enlargement is ordinary scalar extension followed, at most, by strict conjugacy.

## 10. Strict-conjugacy descent

### 10.1 Strict equivalence and fixed residual bases

Let $R$ be local. Two representations

$$
\rho_1,\rho_2:G\longrightarrow\operatorname{GL}_d(R)
$$

with the same reduction are **strictly equivalent** if

$$
\rho_2(g)=u\rho_1(g)u^{-1}
$$

for some

$$
u\in 1+M_d(\mathfrak m_R).
$$

An arbitrary conjugator may change the chosen residual basis; a strict conjugator does not. This distinction is crucial whenever the residual representation is fixed as an actual matrix-valued homomorphism rather than only up to isomorphism.

Carayol descent constructs a strict model over the trace ring. A second question is equally important: if two representations already defined over a smaller ring become strictly equivalent after enlarging coefficients, was the equivalence itself already defined over the smaller ring? Residual absolute irreducibility again gives an affirmative answer.

### 10.2 Centralizers of residually absolutely irreducible families

Let $B\subseteq A$ be local coefficient rings with the same residue field, and let

$$
\rho:G\to\operatorname{GL}_d(B)
$$

have absolutely irreducible reduction. The trace-generation calculation over $B$ chooses group matrices that form an $A$-basis after scalar extension. Hence

$$
\operatorname{Cent}_{M_d(A)}(\rho(G))=A\cdot I.
$$

Similarly,

$$
\operatorname{Cent}_{M_d(B)}(\rho(G))=B\cdot I.
$$

This scalar-centralizer statement is the uniqueness mechanism. Any two conjugators between the same pair of representations differ by a scalar, and scalar multiplication does not change conjugation.

### 10.3 Descent of a conjugacy

**Theorem (strict-conjugacy descent).** Let $B\subseteq A$ be local rings with the same residue field $k$. Let

$$
\rho_1,\rho_2:G\longrightarrow\operatorname{GL}_d(B)
$$

have the same absolutely irreducible reduction. If there is

$$
u\in1+M_d(\mathfrak m_A)
$$

such that

$$
\rho_2(g)=u\rho_1(g)u^{-1}
\qquad(g\in G),
$$

then there is

$$
v\in1+M_d(\mathfrak m_B)
$$

giving the same conjugacy.

**Proof strategy.** The two residual-density algebras are both $M_d(B)$. Conjugation by $u$ restricts to a $B$-algebra automorphism between them. Local Skolem--Noether replaces it by conjugation using a $B$-matrix. The quotient of the two conjugators centralizes the representation and is therefore scalar. A final scalar normalization makes the $B$-conjugator strict.

**Proof.** The $B$-algebra generated by $\rho_i(G)$ is all of $M_d(B)$. Indeed choose residual basis elements from $\rho_1(G)$; their reductions form a basis, so they form a $B$-basis of $M_d(B)$, and similarly for $\rho_2$.

Conjugation by $u$ maps each $\rho_1(g)$ to $\rho_2(g)$ and therefore restricts to a $B$-algebra automorphism

$$
\varphi:M_d(B)\xrightarrow{\sim}M_d(B).
$$

Local Skolem--Noether gives $w\in\operatorname{GL}_d(B)$ with $\varphi=\operatorname{Ad}(w)$. Thus $w^{-1}u$ centralizes $\rho_1(G)$ in $M_d(A)$, so

$$
u=a w
$$

for some $a\in A^\times$.

Because $u$ reduces to $I$, the reduction of $w$ is scalar, say $\bar w=\lambda I$. Choose $b\in B^\times$ lifting $\lambda^{-1}$ and put $v=bw$. Then $v\equiv I\pmod{\mathfrak m_B}$, and scalar multiplication leaves conjugation unchanged. Hence $v$ gives the desired strict equivalence. $\square$

Notice that $A$ need not be flat over $B$ and neither ring need be complete for this theorem. The proof uses locality, equality of residue fields, and residual absolute irreducibility.

### 10.4 Uniqueness of descended models

Suppose $\rho'_1$ and $\rho'_2$ are two $B$-valued strict descents of the same $A$-valued representation, and both reduce to the fixed $\bar\rho$. Their comparison over $A$ is strict: if $u_i$ sends the original representation to $\rho'_i$, then $u_2^{-1}u_1$ is congruent to the identity and conjugates one descended model to the other. Strict-conjugacy descent supplies a matrix in $1+M_d(\mathfrak m_B)$ giving that comparison.

Thus a descended model is unique up to strict $B$-equivalence. It is not generally unique as a literal matrix-valued homomorphism, because changing a $B$-basis by a strict matrix produces another model. The correct uniqueness object is the strict-conjugacy class.

If one forgets the residual basis, uniqueness is up to arbitrary $\operatorname{GL}_d(B)$-conjugacy. The strict form is sharper and is the one compatible with coefficient problems that fix a residual matrix representation.

### 10.5 A descent statement for families

The preceding results can be summarized as a descent statement for a groupoid. Consider representations with fixed absolutely irreducible reduction as objects and strict conjugacies as arrows. Extension of coefficients from $B$ to $A$ has two properties on the full subcollection whose traces lie in $B$:

- every $A$-valued object is strictly isomorphic to a $B$-valued object;
- every strict isomorphism between $B$-valued objects that exists over $A$ already exists over $B$.

The first is Carayol descent; the second is strict-conjugacy descent. Together they say that enlarging coefficients adds neither essential objects nor new identifications once the trace algebra and residual absolute irreducibility are fixed.

### 10.6 The scalar torsor of conjugators

Fix residually absolutely irreducible $\rho_1$ and $\rho_2$ over a local ring $R$, and suppose at least one conjugator exists. If $u_0$ is one, every other conjugator is

$$
a u_0,\qquad a\in R^\times,
$$

because $u_0^{-1}u$ centralizes $\rho_1(G)$. Conversely every scalar multiple gives the same conjugacy. Thus the set of conjugating matrices is a torsor under $R^\times$.

For strict conjugators, the condition $u\equiv I$ cuts this scalar freedom down to

$$
1+\mathfrak m_R.
$$

If $u_0$ is strict, then $a u_0$ is strict exactly when $a\equiv1\pmod{\mathfrak m_R}$. Consequently strict conjugators form either the empty set or a torsor under $1+\mathfrak m_R$.

This description clarifies the last normalization in both descent theorems. An implementing matrix first appears with scalar residual value. Multiplying by a lift of the inverse residual scalar moves it into the strict torsor without altering the conjugacy. There is generally no canonical point of that torsor, so uniqueness should never be stated as uniqueness of a conjugating matrix.

At inverse-limit level,

$$
1+\mathfrak m_R\cong\varprojlim_r(1+\mathfrak m_{R_r}),
$$

with the evident interpretation of the finite quotients. Compatible strict conjugators therefore differ by a compatible scalar system. This is the simplest manifestation of why the automorphism group of an absolutely irreducible representation is scalar.

### 10.7 Compatibility through quotient towers

Let $R=\varprojlim R_r$ and let $\rho_1,\rho_2$ be $R$-valued with the same absolutely irreducible reduction. Suppose $u_r$ is a strict conjugator between their reductions at level $r$. Even when every level admits such a $u_r$, the chosen sequence may fail to be compatible.

The scalar torsor describes the correction. If $u_{r+1}$ reduces to a conjugator different from $u_r$, then

$$
u_r^{-1}(u_{r+1}\bmod R_r)
$$

centralizes the reduced representation and is therefore a scalar $a_r\in1+\mathfrak m_{R_r}$. If the map

$$
1+\mathfrak m_{R_{r+1}}\longrightarrow1+\mathfrak m_{R_r}
$$

is surjective, lift $a_r^{-1}$ and multiply $u_{r+1}$ by that scalar. The adjusted conjugator still gives the same conjugacy and now reduces to $u_r$.

Surjectivity holds for a quotient of local rings: lift $1+x$ to $1+\widetilde x$, which is a unit because its residue is one. Induction therefore produces a compatible tower of strict conjugators, whose inverse limit is a strict conjugator over $R$.

This gives an alternative finite-level proof of compatibility once strict conjugators are known to exist at every stage. It also explains why absolute irreducibility removes the only obstruction: discrepancies are forced into the scalar unit group, whose transition maps lift. Without scalar centralizers, the discrepancy would lie in a larger possibly nonsmooth automorphism group, and compatible correction could fail.

In the main proof we avoid choosing arbitrary levelwise models. Splitting the global Azumaya algebra produces compatibility from the start. The tower argument is nevertheless valuable when a problem naturally constructs descents one Artinian quotient at a time.

## 11. Examples, counterexamples, and diagnostic variants

### 11.1 Rank one

When $d=1$, trace is the representation itself:

$$
\operatorname{tr}\rho(g)=\rho(g).
$$

The closed trace algebra contains every value, so the representation is already defined over it. The density basis has one element, $E=B$, the Azumaya algebra has rank one, and every conjugation is trivial. Carayol descent reduces to the definition.

This elementary case clarifies what higher rank adds. In rank one invariant coefficients are entries. In higher rank, trace coordinates and matrix-algebra splitting are needed to turn invariant data back into entries after one common basis change.

### 11.2 A pure change of basis

Let $B$ be complete local, let

$$
\rho_0:G\to\operatorname{GL}_d(B)
$$

have absolutely irreducible reduction, and embed $B$ in a larger local ring $A$. For any $u\in\operatorname{GL}_d(A)$ set

$$
\rho(g)=u\rho_0(g)u^{-1}.
$$

All traces lie in $B$, although the entries of $\rho(g)$ may use all of $A$. If $u$ is far from $\operatorname{GL}_d(B)$, no individual inspection of entries reveals the smaller model. Carayol descent recovers some conjugator to a $B$-model; strict-conjugacy descent says that any two such models differ by a strict $B$-basis change once their residual bases agree.

The theorem does not promise to recover the original $u$. Multiplying $u$ by a scalar or by an element normalizing the model changes the presentation without changing the representation. Descent concerns existence and the correct equivalence class, not a canonical basis.

### 11.3 A diagonal family with a smaller trace ring

Let $A=k[[X]]$, put $q=1+X$, and let an infinite cyclic group act by

$$
\rho(g)=
\begin{pmatrix}
q&0\\
0&q^{-1}
\end{pmatrix}.
$$

All traces are polynomials in $q+q^{-1}$. Indeed the recurrence

$$
P_{n+1}(Z)=ZP_n(Z)-P_{n-1}(Z),
\qquad P_0=2,\quad P_1=Z,
$$

gives $P_n(q+q^{-1})=q^n+q^{-n}$. If

$$
s=q+q^{-1}-2=X^2-X^3+X^4-\cdots,
$$

then the closed trace algebra is $B=k[[s]]$, a proper subring of $A$.

The characteristic polynomial

$$
T^2-(q+q^{-1})T+1
$$

has coefficients in $B$, so there is a companion matrix over $B$ with the same characteristic polynomial. Yet the displayed diagonal representation is not integrally conjugate to that companion model near the residual point: the eigenvector change-of-basis determinant is a multiple of $q-q^{-1}$, which lies in the maximal ideal and is not a unit. The residual representation is scalar and reducible. This example shows exactly why trace containment without residual absolute irreducibility does not imply integral descent.

### 11.4 Merely irreducible is not enough

Let $K/k$ be a finite extension and let a group act on the $k$-space $K$ through multiplication. The representation may be irreducible over $k$, while its commuting algebra contains $K$. Its generated algebra is not $M_{[K:k]}(k)$, and after extending scalars it decomposes.

In this situation the invariant algebra naturally remembers an unsplit form rather than a full matrix algebra. The trace pairing on a putative list of $d^2$ group matrices cannot be invertible because the generated algebra has smaller dimension. Henselian lifting cannot manufacture a rank-one projector in a special fiber that has none. Absolute irreducibility is therefore a structural splitting hypothesis, not merely a convenient way to invoke Schur's lemma.

### 11.5 Why closedness and continuity cannot be dropped

Let $A=k[[t]]$. The polynomial algebra $k[t]$ and the localized algebra $k[t]_{(t)}$ are dense in $A$ for the $t$-adic topology but omit genuine infinite series. If trace values algebraically generate $k[t]$ and converge to an element of $A\setminus k[t]$, an attempted descent to the algebraic trace ring loses completeness. The correct coefficient object is its closure.

Continuity is equally important for a compact group. A continuous map to a discrete Artinian quotient has finite image and open kernel. Without continuity, a homomorphism from the underlying abstract group can detect infinitely fine distinctions at a fixed coefficient level, and the character need not be locally constant. The finite-shadow interpretation of the trace algebra would then cease to reflect the topology of the group action.

Compactness itself is used for finite image at discrete stages, not for the trace-coordinate algebra. If one begins with an arbitrary group and a representation already known to be continuous for some other suitable topology, the algebraic descent proof still works. What is lost is the compact character interpretation and the automatic factorization through finite quotients.

### 11.6 Characteristic-polynomial variants

For a $d$-dimensional representation write

$$
\det(TI-\rho(g))
=T^d-c_1(g)T^{d-1}+\cdots+(-1)^dc_d(g).
$$

The closed algebra generated by all $c_i(g)$ contains the trace algebra because $c_1(g)=\operatorname{tr}\rho(g)$. Under residual absolute irreducibility, Carayol descent already works over the smaller trace algebra, so every characteristic coefficient of the descended matrices automatically belongs to it. This conclusion is produced by descent, not by dividing in Newton identities.

Without residual absolute irreducibility, the characteristic-coefficient algebra may be a better invariant than the trace algebra, especially in small characteristic. It still does not by itself force matrix descent. The missing ingredient is a full matrix algebra with a split residual fiber. Characteristic polynomials organize invariant scalar data; Azumaya splitting organizes modules and bases.

Under the hypotheses of Carayol descent, a striking consequence is

$$
c_i(g)\in T_\rho
\qquad(1\leq i\leq d, g\in G).
$$

Indeed the strictly conjugate matrices have entries in $T_\rho$, and characteristic-polynomial coefficients are polynomial expressions in those entries. In particular all determinants lie in the trace ring, even in residue characteristics where Newton identities cannot solve for them by division.

This consequence should not be used as an input to the proof. The trace-coordinate algebra was constructed using traces alone; its Azumaya splitting then forces every other characteristic coefficient into the same ring. The direction of reasoning is important in small characteristic.

For $d=2$ and $2\in A^\times$, the familiar identity

$$
2\det(x)=\operatorname{tr}(x)^2-\operatorname{tr}(x^2)
$$

already puts determinants in the trace algebra. When $2$ is not a unit, that formula only controls twice the determinant. Carayol descent supplies the integral conclusion without cancelling $2$, but only because the entire residual family is absolutely irreducible; a single isolated matrix does not enjoy such a conclusion.

### 11.7 A finite-group model calculation

Assume $\operatorname{char}k$ is neither $2$ nor $3$. Let a group generated by $r$ and $s$ act through

$$
\bar\rho(r)=
\begin{pmatrix}
0&-1\\
1&-1
\end{pmatrix},
\qquad
\bar\rho(s)=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
$$

These matrices satisfy $r^3=s^2=1$ and $srs=r^{-1}$, so they give the standard two-dimensional representation of the symmetric group on three letters. The representation is absolutely irreducible: an invariant line for $r$ would be an eigenspace for a primitive cube root after scalar extension, and $s$ exchanges the two eigenspaces.

The four group matrices

$$
I,\quad \bar\rho(r),\quad \bar\rho(s),\quad
\bar\rho(rs)
$$

span $M_2(k)$. To verify independence directly, write a linear relation and compare the four entries; the resulting coefficient determinant is a nonzero multiple of $3$. Thus they provide a residual group basis.

Now let $A$ be any complete local coefficient ring with residue $k$, and let $\rho$ be a lift. Put

$$
x_1=I,\quad x_2=\rho(r),\quad
x_3=\rho(s),\quad x_4=\rho(rs).
$$

The trace Gram matrix $(\operatorname{tr}(x_ix_j))$ has unit determinant because its reduction is the Gram matrix of the displayed basis. Every $\rho(g)$ therefore has coordinates

$$
c_i(g)=\sum_j(\Gamma^{-1})_{ij}
\operatorname{tr}\rho(gg_j)
$$

in the closed trace algebra. This example shows the general theorem in a familiar finite group: four carefully chosen group elements replace arbitrary matrix entries, and character values of their translates provide all coordinates.

If the characteristic is $3$, the displayed residual representation is no longer absolutely irreducible in the same way and the determinant test degenerates. This is not a limitation of the trace-pairing method in characteristic $3$; it is the failure of this particular residual representation and this particular basis to satisfy the theorem's hypothesis.

### 11.8 Coefficient change and trace rings

Let $A\to A'$ be a continuous local map and let $\rho'$ be the scalar-changed representation. Then

$$
\operatorname{tr}\rho'(g)
$$

is the image of $\operatorname{tr}\rho(g)$. Hence the trace ring of $\rho'$ is the closed image of $T_\rho$ together with the chosen image of the coefficient base. If the base is unchanged,

$$
T_{\rho'}=\overline{\operatorname{im}(T_\rho\to A')}.
$$

The closure cannot be omitted for an arbitrary complete target. If $A'$ is an Artinian quotient, the image is already closed and

$$
T_{\rho'}\cong T_\rho/(T_\rho\cap\ker(A\to A')).
$$

For a flat completed coefficient extension under finite-module hypotheses, completed tensor product identifies the base-changed trace ring with its image. Without flatness a kernel may appear, so the closed-image formulation is the invariant one.

Carayol descent commutes with such coefficient change at the level of strict-conjugacy classes. A $T_\rho$-valued descended model can be extended to the new closed trace ring, producing a descent of $\rho'$. Conversely, applying the theorem after base change may choose a different splitting, but strict-conjugacy uniqueness identifies the two resulting models over the new trace ring.

## 12. The descent machine in final form

### 12.1 The logical dependency chain

The argument can now be read as a chain in which each arrow has been justified:

$$
\begin{array}{c}
\bar\rho\text{ absolutely irreducible}
\\
\Downarrow\ \text{Burnside--density}
\\
k[\bar\rho(G)]=M_d(k)
\\
\Downarrow\ \text{choose group basis and invert trace Gram matrix}
\\
E=\sum_iT_\rho\rho(g_i),\quad
E\otimes_{T_\rho}A=M_d(A)
\\
\Downarrow\ \text{reduction and topological Nakayama}
\\
E\text{ is Azumaya with }E\otimes k=M_d(k)
\\
\Downarrow\ \text{Henselian idempotent lifting}
\\
E\cong M_d(T_\rho)
\\
\Downarrow\ \text{local Skolem--Noether}
\\
\rho\text{ is strictly conjugate into }\operatorname{GL}_d(T_\rho).
\end{array}
$$

The topology runs through the whole chain. It makes $T_\rho$ local and complete, makes $E$ a complete finite module, permits idempotent lifting, and turns the final algebra isomorphisms into continuous ones. The matrix calculation alone would produce only an algebra over an abstract subring, not a coherent inverse-limit descent.

### 12.2 A reusable criterion

The following formulation is often the quickest way to apply the theory.

**Criterion.** Let $B\subseteq A$ be closed pro-Artinian local coefficient rings with the same residue field. Let $G$ be compact and let $\rho:G\to\operatorname{GL}_d(A)$ be continuous. If

1. $\bar\rho$ is absolutely irreducible; and
2. $\operatorname{tr}\rho(g)\in B$ for every $g\in G$,

then $\rho$ is strictly conjugate to a continuous $B$-valued representation. Any two such $B$-valued strict models are strictly conjugate over $B$.

If $B$ is chosen to be the closed trace algebra, it is minimal. If a larger closed ring is convenient because it also contains prescribed determinant values or auxiliary scalars, the same proof descends directly to that ring.

No separate hypotheses are needed about traces of products: $\operatorname{tr}(\rho(g)\rho(h))=\operatorname{tr}\rho(gh)$ is already covered. No inverse of $d$ is needed. No flatness of $A$ over $B$ is needed because the chosen group matrices give explicit bases. No prior Noetherianity of $B$ is needed because all modules used in the matrix argument are finite free and the topology is pro-Artinian.

### 12.3 Consequences for coefficient problems

The theorem separates basis-dependent and invariant coefficient data cleanly. A large coefficient ring may be needed to write an initial family of matrices, but under residual absolute irreducibility the smallest closed ring generated by the character already supports the family after a strict basis change.

At finite level, every representation factors through a finite quotient of the compact group, and every trace algebra is Artinian. At infinite level, closure assembles those trace algebras into one pseudocompact local ring. The finite matrix basis selected in the residual fiber persists at every level, so no new matrix directions appear during lifting. Only their scalar coordinates vary, and those coordinates are trace expressions.

Strict-conjugacy descent adds uniqueness. Enlarging coefficients cannot identify two small-ring models unless they were already identified over the small ring. Thus the trace algebra controls both objects and arrows: it is a genuine coefficient ring for the representation problem, not merely a ring in which numerical invariants happen to lie.

The resulting method is robust in mixed and equal characteristic, over finite or infinite residue fields, and in residue characteristics dividing the dimension. Its essential inputs are instead conceptual: a complete local inverse-limit topology, a compact continuous action, and residual absolute irreducibility.

### 12.4 Conclusion

The trace begins as a modest invariant: one scalar for each group element, unchanged by every basis transformation. Residual absolute irreducibility magnifies that invariant. Burnside density turns finitely many group elements into a basis of the entire residual matrix algebra, and the perfect trace pairing turns all other group matrices into trace-controlled coordinates. Those coordinates assemble into an Azumaya algebra over the closed trace ring.

Topology then performs the descent that linear algebra alone cannot. Closed subalgebras are reconstructed from Artinian shadows; strictness preserves their quotient structure; topological Nakayama lifts finite-level isomorphisms; and Henselian completeness lifts a rank-one residual projector. The resulting column module splits the Azumaya algebra. Local Skolem--Noether finally translates equality of abstract matrix algebras into one simultaneous change of basis, while scalar normalization preserves the chosen residual basis.

Carayol descent is therefore not the assertion that traces mysteriously contain matrix entries. It is the more precise statement that, once the residual action fills the matrix algebra, traces determine a split matrix algebra over their own closed coefficient ring. A basis of its lifted column module then reveals the matrices that were present over that smaller ring all along.
