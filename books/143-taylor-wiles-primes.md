# Taylor–Wiles Primes

## Contents

1. [The auxiliary-prime bargain](#1-the-auxiliary-prime-bargain)
   - [A global problem at its numerical threshold](#11-a-global-problem-at-its-numerical-threshold)
   - [Why the congruence and eigenvalue conditions occur together](#12-why-the-congruence-and-eigenvalue-conditions-occur-together)
   - [The three layers of the construction](#13-the-three-layers-of-the-construction)
   - [Standing conventions and the boundary of the main theorem](#14-standing-conventions-and-the-boundary-of-the-main-theorem)
2. [Adjoint modules and the dual Selmer target](#2-adjoint-modules-and-the-dual-selmer-target)
   - [Full adjoint, trace zero, and the determinant derivative](#21-full-adjoint-trace-zero-and-the-determinant-derivative)
   - [The global local-condition package](#22-the-global-local-condition-package)
   - [What a dual class looks like at an unramified prime](#23-what-a-dual-class-looks-like-at-an-unramified-prime)
   - [The global numerical identity retained from the original problem](#24-the-global-numerical-identity-retained-from-the-original-problem)
   - [Determinant and characteristic-two cautions](#25-determinant-and-characteristic-two-cautions)
   - [Changing the controlling set without changing the problem](#26-changing-the-controlling-set-without-changing-the-problem)
3. [The residual image hypothesis](#3-the-residual-image-hypothesis)
   - [What the image must accomplish](#31-what-the-image-must-accomplish)
   - [Split Taylor–Wiles adequacy](#32-split-taylorwiles-adequacy)
   - [The classical two-dimensional large-image case](#33-the-classical-two-dimensional-large-image-case)
   - [Small images and exceptional cases](#34-small-images-and-exceptional-cases)
   - [From semisimple spanning to the projector detector](#35-from-semisimple-spanning-to-the-projector-detector)
4. [Cohomology extensions and compatible composita](#4-cohomology-extensions-and-compatible-composita)
   - [The extension cut out by a cocycle](#41-the-extension-cut-out-by-a-cocycle)
   - [Why a nonzero class gives a nontrivial extension](#42-why-a-nonzero-class-gives-a-nontrivial-extension)
   - [The exact compositum compatibility lemma](#43-the-exact-compositum-compatibility-lemma)
   - [Residual and cyclotomic disjointness](#44-residual-and-cyclotomic-disjointness)
   - [Cohomology and cyclotomic disjointness](#45-cohomology-and-cyclotomic-disjointness)
   - [Several cohomology classes and the independence trap](#46-several-cohomology-classes-and-the-independence-trap)
   - [A compatibility ledger for one cocycle](#47-a-compatibility-ledger-for-one-cocycle)
5. [Regular semisimple detection](#5-regular-semisimple-detection)
   - [The local linear-algebra quotient](#51-the-local-linear-algebra-quotient)
   - [Selecting a Galois element that detects one class](#52-selecting-a-galois-element-that-detects-one-class)
   - [Prescribing the residual eigenvalues](#53-prescribing-the-residual-eigenvalues)
   - [Why three tempting substitutes fail](#54-why-three-tempting-substitutes-fail)
6. [Chebotarev selection of auxiliary primes](#6-chebotarev-selection-of-auxiliary-primes)
   - [The finite quotient carrying all conditions](#61-the-finite-quotient-carrying-all-conditions)
   - [The one-class prime-selection theorem](#62-the-one-class-prime-selection-theorem)
   - [Additional splitting and avoidance conditions](#63-additional-splitting-and-avoidance-conditions)
   - [Diagnostic example: one dual Selmer class](#64-diagnostic-example-one-dual-selmer-class)
   - [Density, conjugacy, and Frobenius normalization](#65-density-conjugacy-and-frobenius-normalization)
7. [The local Taylor–Wiles condition](#7-the-local-taylorwiles-condition)
   - [Tame generators and the chosen residual branch](#71-tame-generators-and-the-chosen-residual-branch)
   - [Why the tame relation is satisfied](#72-why-the-tame-relation-is-satisfied)
   - [The complete first-order calculation](#73-the-complete-first-order-calculation)
   - [The pairing in coordinates](#74-the-pairing-in-coordinates)
   - [What fails at scalar or nonsplit Frobenius](#75-what-fails-at-scalar-or-nonsplit-frobenius)
   - [Why every permitted extension splits](#76-why-every-permitted-extension-splits)
8. [Universal local deformation rings](#8-universal-local-deformation-rings)
   - [The unrestricted unramified branch](#81-the-unrestricted-unramified-branch)
   - [The finite diamond quotient](#82-the-finite-diamond-quotient)
   - [The unframed Taylor–Wiles ring](#83-the-unframed-taylorwiles-ring)
   - [Framed rings and eigenline coordinates](#84-framed-rings-and-eigenline-coordinates)
   - [Components and the augmentation map](#85-components-and-the-augmentation-map)
   - [Diagnostic example: a split-Frobenius prime](#86-diagnostic-example-a-split-frobenius-prime)
   - [The representing problem and its base changes](#87-the-representing-problem-and-its-base-changes)
9. [Diamond symmetry for a finite set](#9-diamond-symmetry-for-a-finite-set)
   - [Product groups and their completed group algebras](#91-product-groups-and-their-completed-group-algebras)
   - [The diamond character](#92-the-diamond-character)
   - [Completed products of the local rings](#93-completed-products-of-the-local-rings)
   - [Maximal and exact-level quotients](#94-maximal-and-exact-level-quotients)
10. [The enlarged global deformation problem](#10-the-enlarged-global-deformation-problem)
    - [Definition of the datum at auxiliary level](#101-definition-of-the-datum-at-auxiliary-level)
    - [The full local base](#102-the-full-local-base)
    - [Augmentation recovers the original problem](#103-augmentation-recovers-the-original-problem)
    - [The new Selmer structures](#104-the-new-selmer-structures)
    - [The five-term comparison sequence](#105-the-five-term-comparison-sequence)
    - [The global augmentation isomorphism in detail](#106-the-global-augmentation-isomorphism-in-detail)
11. [Killing the dual Selmer group](#11-killing-the-dual-selmer-group)
    - [The exact one-prime drop](#111-the-exact-one-prime-drop)
    - [The inductive construction](#112-the-inductive-construction)
    - [Diagnostic example: two independent classes](#113-diagnostic-example-two-independent-classes)
    - [Why the cardinality is dual, not primal](#114-why-the-cardinality-is-dual-not-primal)
    - [The localization matrix criterion](#115-the-localization-matrix-criterion)
12. [Taylor–Wiles sets at every level](#12-taylorwiles-sets-at-every-level)
    - [Existence with prescribed cardinality](#121-existence-with-prescribed-cardinality)
    - [What simultaneous prescriptions can be retained](#122-what-simultaneous-prescriptions-can-be-retained)
    - [Nonnested sets are the natural outcome](#123-nonnested-sets-are-the-natural-outcome)
    - [Cardinality padding](#124-cardinality-padding)
13. [Numerical output and generator counts](#13-numerical-output-and-generator-counts)
    - [Change in the Wiles defect](#131-change-in-the-wiles-defect)
    - [Unframed and framed generators](#132-unframed-and-framed-generators)
    - [The free pro-$\ell$ diamond variables](#133-the-free-pro-ell-diamond-variables)
    - [The complete finite-level ledger](#134-the-complete-finite-level-ledger)
    - [What dual-Selmer vanishing does and does not imply](#135-what-dual-selmer-vanishing-does-and-does-not-imply)
14. [The theorem package](#14-the-theorem-package)
    - [Precise hypotheses](#141-precise-hypotheses)
    - [Existence and local-structure theorem](#142-existence-and-local-structure-theorem)
    - [Variants and their exact adjustments](#143-variants-and-their-exact-adjustments)
    - [Conclusion](#144-conclusion)
15. [Paired relative Taylor–Wiles selection](#15-paired-relative-taylorwiles-selection)
    - [Two sources and one residual Selmer problem](#151-two-sources-and-one-residual-selmer-problem)
    - [The paired relative selection theorem](#152-the-paired-relative-selection-theorem)
    - [Padding without reopening the obstruction space](#153-padding-without-reopening-the-obstruction-space)
    - [The totally real variable count](#154-the-totally-real-variable-count)
    - [What the paired theorem contributes](#155-what-the-paired-theorem-contributes)

## 1. The auxiliary-prime bargain

### 1.1 A global problem at its numerical threshold

Let $K$ be a number field, let $\ell$ be a prime, and let

$$
\bar\rho:G_{K,S}\longrightarrow \operatorname{GL}_2(k)
$$

be a continuous residual representation over a finite field $k$ of characteristic $\ell$. The global deformation problem assembled earlier prescribes a determinant and a local lifting condition at every place in a finite set $S$. Its first-order deformations form a Selmer group. The relations that global reciprocity can impose are measured by the dual Selmer group. If

$$
M=\operatorname{ad}^0\bar\rho,
\qquad
M'=M^*(1),
$$

in the usual fixed-determinant, odd-characteristic setting, those two spaces are

$$
H^1_{\mathcal L}(K,M)
\quad\text{and}\quad
H^1_{\mathcal L^\perp}(K,M').
$$

The second space is the obstruction that concerns us here. It is not generally an obstruction group in the crude sense that every one of its vectors must occur as a failed lift. Its exact role is sharper: it is dual to the failure of permitted local first-order data to come from a global class. Its dimension controls the number of relations in the standard global presentation and the number of independent local directions needed to remove the reciprocity defect.

Suppose that

$$
q=\dim_k H^1_{\mathcal L^\perp}(K,M').
$$

If $q=0$, global reciprocity contributes no remaining dual Selmer condition. If $q>0$, one cannot simply discard the group. Nor can one choose $q$ arbitrary primes and expect it to disappear. A prime is useful only if localization there detects a class that has survived all previous choices.

The Taylor–Wiles idea is to change the global problem at carefully selected places $v\notin S$. Originally a lift is required to be unramified there. At an auxiliary place we permit a controlled tame character on two distinguished residual eigenspaces. Infinitesimally this adds one local direction. Under local Tate duality, adding that primal direction removes one dual local direction. If a nonzero global dual class occupies the removed line, that class is excluded from the new dual Selmer group.

This is a trade, not a disappearance:

$$
\begin{array}{c}
\text{one newly permitted tame local direction}
\\
\Updownarrow
\\
\text{one removed dual local condition}
\end{array}
$$

The new direction is exceptionally well controlled. It is encoded by a finite $\ell$-group quotient of the residue-field units, and its universal character supplies a diamond symmetry. Thus an opaque global reciprocity relation is exchanged for an explicit local group-algebra variable.

### 1.2 Why the congruence and eigenvalue conditions occur together

At a finite place $v\nmid\ell$, write $q_v$ for the cardinality of the residue field and choose arithmetic Frobenius $\varphi_v$. The maximal tame quotient has generators $\varphi_v$ and $\tau_v$ with relation

$$
\varphi_v\tau_v\varphi_v^{-1}=\tau_v^{q_v}.
\tag{1.1}
$$

Two requirements make this relation useful.

First, one asks that

$$
q_v\equiv 1\pmod{\ell^N}.
\tag{1.2}
$$

Then the residue-field unit group has a quotient of order $\ell^N$, and Frobenius acts trivially on that quotient. A tame character of order dividing $\ell^N$ can therefore coexist with a diagonal Frobenius action.

Second, one asks that $\bar\rho(\varphi_v)$ have two distinct eigenvalues in $k$. This gives two residual eigenlines and makes their lifts unique. Once one eigenline is designated, the local functor has a single branch and admits explicit coordinates. If Frobenius is scalar, no line is distinguished, strict conjugacy has a large stabilizer, and the local ring is not the smooth branch needed below.

These conditions also drive the cohomology. When (1.2) holds modulo $\ell$ and residual Frobenius has distinct eigenvalues, the trace-zero adjoint has precisely one unramified local direction and one tame local direction. The Taylor–Wiles condition permits both; the original unramified condition permits only the first. The quotient is therefore exactly one-dimensional.

The congruence and residual conjugacy conditions are not automatically compatible. They prescribe Frobenius in two finite extensions: a cyclotomic extension and the field cut out by $\bar\rho$. A pair of prescribed automorphisms occurs in their compositum only when the two automorphisms agree on the intersection. The same issue appears again when a cohomology class cuts out a further extension. Establishing the required disjointness is a central part of the argument, not a formality hidden inside Chebotarev.

### 1.3 The three layers of the construction

The theory has three logically separate layers.

The first is an image-and-cohomology lemma. Given a nonzero dual Selmer class, it must produce a Galois element whose cyclotomic character is trivial, whose residual Frobenius is split regular semisimple, and on which the cocycle has a nonzero diagonal projection. Absolute irreducibility by itself does not prove this. One needs a finite-image hypothesis strong enough to force restriction of the class to a residual kernel to be nonzero and to detect the resulting image by regular semisimple elements.

The second is Chebotarev. Once a compatible element has been constructed in one finite Galois quotient, Chebotarev produces infinitely many primes having that Frobenius conjugacy class. It cannot manufacture an element that is absent from the compositum. All compatibility work therefore precedes the density theorem.

The third is local and global deformation theory. At each selected prime one constructs an enhanced local functor, its group-algebra action, and its tangent space. Poitou–Tate comparison then proves that the dual Selmer dimension falls by exactly one. Repeating the procedure yields a set of the required cardinality.

Keeping these layers separate prevents several seductive but false shortcuts:

- nonzero global cohomology does not imply nonzero restriction at an arbitrarily convenient Frobenius element;
- a congruence on $q_v$ and a residual conjugacy class cannot be prescribed independently unless their common quotient is controlled;
- a local condition is killed on the dual side only by taking its exact Tate orthogonal;
- a one-dimensional local quotient gives a drop of at most one, and exactness is needed to prove that the drop is one;
- the number of auxiliary primes is a dual Selmer dimension, not automatically the primal Selmer dimension;
- framed matrix coordinates and diamond variables are different kinds of variables.

### 1.4 Standing conventions and the boundary of the main theorem

The clean theorem developed first assumes that $\ell$ is odd, that the determinant is fixed, and that $\bar\rho$ is absolutely irreducible. Then

$$
M=\operatorname{ad}^0\bar\rho
$$

is the correct tangent coefficient and the trace pairing identifies $M^*$ with $M$. Thus

$$
M'=M(1).
\tag{1.3}
$$

The selection argument itself will be formulated using exact finite-image hypotheses. This makes clear which part of the customary word “adequate” is actually used.

All Frobenius elements are arithmetic. Local reciprocity sends a uniformizer to arithmetic Frobenius. For $N\ge1$, write

$$
\epsilon_{\ell^N}:G_K\longrightarrow(\mathbf Z/\ell^N\mathbf Z)^\times
$$

for the cyclotomic character on $\ell^N$th roots of unity, and write $\bar\epsilon$ for its reduction modulo $\ell$. Thus

$$
\epsilon_{\ell^N}(\varphi_v)=q_v\bmod\ell^N
$$

at every place where the character is unramified. The determinant character is denoted

$$
\delta:G_{K,S}\longrightarrow\mathcal O^\times,
$$

where $\mathcal O$ is the ring of integers of a finite extension of $\mathbf Q_\ell$ with residue field $k$.

Every real and complex place remains in $S$. For odd $\ell$, positive-degree cohomology at real places vanishes, but the real invariant terms remain part of the global numerical formula. In characteristic two the trace-zero module, its dual, and the real-place terms all change. We will state the necessary corrections, but the standard rank-two theorem will not pretend to include that case.

This book stops after constructing auxiliary data and recording its numerical output. It does not build a system across levels, take inverse limits of global rings, or patch modules. The endpoint is the precise finite-level package those later operations require.

The imported foundations are all earlier. Local reciprocity and the residue-field unit quotient are from Book 5, while the global reciprocity and cyclotomic conventions are from Book 6. The Selmer comparison sequence and numerical identity are Book 33, Sections 8--10. Representability, tangent spaces, partial framings, and the relative generator formula are Book 69, Chapters 6--10 and Theorem 15.3. The finite-image adequacy and regular-semisimple detector used in Chapter 3 are Book 141, Theorem 10.2 and Corollary 10.3; the cyclotomic restriction criterion is its Theorem 10.4. Finally, all analytic Frobenius distribution used here is cited result-by-result from Book 142 in Section 6.1. The split Taylor--Wiles conditions below are therefore properties of the input residual image, not placeholders for the prime-selection conclusion; Chapters 4--6 prove that those properties produce the required detecting primes.

## 2. Adjoint modules and the dual Selmer target

Prime selection is meaningful only after the global obstruction has been expressed in the coefficient module that the determinant problem actually supplies. This chapter fixes that coefficient, recalls how local permissions acquire exact dual prohibitions, and isolates the one-dimensional local shadow that an auxiliary prime must detect. It also separates the clean odd-characteristic calculation from the determinant and real-place phenomena that survive in characteristic two.

### 2.1 Full adjoint, trace zero, and the determinant derivative

Let $V$ be the two-dimensional $k$-space underlying $\bar\rho$. The full adjoint module is

$$
\operatorname{ad}\bar\rho=\operatorname{End}_k(V),
\qquad
g\cdot X=\bar\rho(g)X\bar\rho(g)^{-1}.
$$

A first-order lift has the form

$$
\rho_\varepsilon(g)=(1+\varepsilon c(g))\bar\rho(g),
$$

and the determinant expands as

$$
\det\rho_\varepsilon(g)
=\det\bar\rho(g)\bigl(1+\varepsilon\operatorname{tr}c(g)\bigr).
\tag{2.1}
$$

Consequently a fixed determinant forces $c(g)$ to lie in

$$
M=\operatorname{ad}^0\bar\rho
=\ker\bigl(\operatorname{tr}:\operatorname{End}_k(V)\to k\bigr).
$$

When $\ell\ne2$,

$$
\operatorname{ad}\bar\rho=kI_2\oplus M,
\tag{2.2}
$$

and the trace pairing

$$
(X,Y)\longmapsto\operatorname{tr}(XY)
$$

is nondegenerate on $M$. Therefore $M^*\simeq M$. Local and global duality use the Tate-twisted module

$$
M'=M^*(1)\simeq M(1),
$$

not $M$ without the twist.

Fixing determinant does not restrict changes of basis. Infinitesimal conjugation still comes from the full adjoint. This distinction matters in framed counts: the positive-degree coefficient is $M$, but the gauge invariants are computed in $\operatorname{ad}\bar\rho$.

### 2.2 The global local-condition package

Let $\mathcal D$ be a global deformation problem with fixed determinant $\delta$. For each $v\in S$, let

$$
L_v\subseteq H^1(K_v,M)
$$

be the tangent space of its local condition. Outside $S$, both $\bar\rho$ and $M$ are unramified and the built-in condition is

$$
L_v=H^1_{\mathrm{ur}}(K_v,M).
$$

The primal Selmer group is

$$
H^1_{\mathcal L}(K,M)
=\ker\left(
H^1(G_{K,S},M)\longrightarrow
\bigoplus_{v\in S}H^1(K_v,M)/L_v
\right).
\tag{2.3}
$$

Local Tate duality gives a perfect pairing

$$
H^1(K_v,M)\times H^1(K_v,M')
\longrightarrow k.
\tag{2.4}
$$

Define $L_v^\perp$ to be the exact annihilator of $L_v$. The dual Selmer group is

$$
H^1_{\mathcal L^\perp}(K,M')
=\ker\left(
H^1(G_{K,S},M')\longrightarrow
\bigoplus_{v\in S}H^1(K_v,M')/L_v^\perp
\right).
\tag{2.5}
$$

At a finite place $v\notin S$, with residue characteristic different from $\ell$, the unramified condition is orthogonal to the unramified condition:

$$
H^1_{\mathrm{ur}}(K_v,M)^\perp
=H^1_{\mathrm{ur}}(K_v,M').
\tag{2.6}
$$

Thus a dual Selmer class is unramified at every prospective auxiliary prime. Its localization is represented by its value on Frobenius modulo the image of Frobenius minus one.

### 2.3 What a dual class looks like at an unramified prime

Let $z$ be a cocycle representing a class in $H^1(G_{K,S},M')$, and let $v\notin S$. Put

$$
A_v=\bar\rho(\varphi_v),
\qquad
\bar\epsilon(\varphi_v)=q_v\bmod\ell,
$$

where $\bar\epsilon$ is the residual cyclotomic character. Since the class is unramified at $v$, its localization is determined by

$$
z(\varphi_v)\in
M'/(\bar\epsilon(\varphi_v)\operatorname{Ad}(A_v)-1)M'.
\tag{2.7}
$$

At a Taylor–Wiles prime, $q_v\equiv1\pmod\ell$, so the twist disappears from the Frobenius action in (2.7). If $A_v$ has distinct eigenvalues, the quotient is one-dimensional. The class is detected precisely when the projection of $z(\varphi_v)$ onto that quotient is nonzero.

This already shows why merely requiring $z(\varphi_v)\ne0$ is insufficient. A nonzero vector can lie in $(\operatorname{Ad}(A_v)-1)M$ and therefore represent the zero local cohomology class. The correct detector is a functional annihilating that image.

### 2.4 The global numerical identity retained from the original problem

Poitou–Tate duality gives

$$
\begin{aligned}
&\dim_k H^1_{\mathcal L}(K,M)
-\dim_k H^1_{\mathcal L^\perp}(K,M')\\
&\qquad=
h^0(K,M)-h^0(K,M')
+\sum_{v\in S}
\bigl(\dim_kL_v-h^0(K_v,M)\bigr).
\end{aligned}
\tag{2.8}
$$

Write the right side as $\Delta(\mathcal D)$. The original problem is balanced when $\Delta(\mathcal D)=0$. Balanced means that primal and dual Selmer dimensions agree; it does not mean either is zero.

For the standard odd, rank-two, totally real deformation problem, the negative contributions from odd real places are canceled by the local contributions at places above $\ell$. That calculation belongs to the original global problem and is not repeated when auxiliary primes are chosen. Auxiliary finite places contribute their own explicitly calculated change to (2.8).

### 2.5 Determinant and characteristic-two cautions

When $\ell=2$, the scalar matrix $I_2$ has trace zero. Hence (2.2) fails and the trace pairing on $\operatorname{ad}^0\bar\rho$ is degenerate. The fixed-determinant tangent is

$$
\ker\left(
H^1(K,\operatorname{ad}\bar\rho)
\xrightarrow{\operatorname{tr}}H^1(K,k)
\right),
\tag{2.9}
$$

and its Tate dual is governed by the dual trace-kernel complex, involving

$$
(\operatorname{ad}^0\bar\rho)^*
\simeq \operatorname{ad}\bar\rho/kI_2.
$$

At real places, $2$-primary modified cohomology is periodic and cannot be removed. A characteristic-two auxiliary-prime theorem is possible only after replacing every occurrence of $M$ and $M'$ by these correct complexes and separately proving an image-detection statement for them.

The local framed determinant equation remains smooth in characteristic two: determinant is a smooth map on $\operatorname{GL}_2$. The failure occurs in trace splitting, duality, and unframed gauge bookkeeping. Accordingly, the explicit framed local rings below remain meaningful after suitable hypotheses, but the clean global theorem is stated for odd $\ell$.

### 2.6 Changing the controlling set without changing the problem

Auxiliary primes are initially outside $S$, whereas a deformation that is allowed to ramify at them is naturally represented using the larger quotient $G_{K,S\cup Q}$. It is therefore important to separate two operations that are often denoted by the same enlarged set: enlarging the ambient Galois group, and relaxing a local condition.

Let $v\notin S$, suppose that a finite $k[G_{K,S}]$-module $A$ is unramified at $v$, and put $S'=S\cup\{v\}$. Inflation gives

$$
H^1(G_{K,S},A)\longrightarrow H^1(G_{K,S'},A).
\tag{2.10}
$$

Its image is exactly the set of classes whose localization at $v$ is unramified. To see this, let $N$ be the closed normal subgroup of $G_{K,S'}$ generated by inertia at $v$. The quotient by $N$ is $G_{K,S}$. Inflation--restriction gives

$$
0\longrightarrow H^1(G_{K,S},A)
\longrightarrow H^1(G_{K,S'},A)
\longrightarrow H^1(N,A)^{G_{K,S}}.
\tag{2.11}
$$

Because $A$ is unramified, a cocycle restricts trivially to $N$ precisely when its local restriction is trivial on inertia, which is precisely the unramified condition. This proves the assertion. Repeating the argument one prime at a time treats a finite set $Q$.

The same distinction appears on representing functors. Merely replacing $G_{K,S}$ by $G_{K,S'}$ permits all ramification allowed by the larger quotient. Imposing the unramified local subfunctor at $v$ cuts the functor back to the original one. Imposing the Taylor--Wiles subfunctor instead makes one controlled relaxation. Consequently the comparison throughout this book is not between two arbitrary ambient Galois groups. It is between two deformation conditions inside the same enlarged ambient group:

$$
\begin{array}{ccc}
\text{unramified at }v&\subset&\text{Taylor--Wiles at }v,\\
H^1_{\mathrm{ur}}(K_v,M)&\subset&H^1(K_v,M).
\end{array}
\tag{2.12}
$$

This observation justifies both the Selmer comparison in Chapter 10 and the statement that augmentation recovers the original problem. It also prevents a circular count: the extra tangent direction comes from the local relaxation, not from the notational act of adding $v$ to $S$.

## 3. The residual image hypothesis

Chebotarev distributes conjugacy classes, but it does not prove that a useful conjugacy class exists. The residual image must first force a nonzero global class to remain visible on a residual kernel and then supply a regular semisimple element that sees its image. This chapter states those jobs as exact algebraic hypotheses, explains their relation to adequacy, and marks the small-image cases in which absolute irreducibility alone is insufficient.

### 3.1 What the image must accomplish

Let

$$
K_1=K(\zeta_\ell),
\qquad
\Gamma=\bar\rho(G_{K_1})\subseteq\operatorname{GL}_2(k).
$$

On $G_{K_1}$ the residual cyclotomic character is trivial, so $M'=M$ as a coefficient module. The selection proof needs four facts about $\Gamma$.

1. A nonzero class must remain nonzero after restriction to the kernel of $\bar\rho$ over $K_1$.
2. The image of that restriction must be visible to a split regular semisimple element.
3. Higher cyclotomic layers must not shrink the residual image.
4. The elementary abelian extension cut out by the class must be disjoint from those higher cyclotomic layers.

These are the actual jobs often compressed into a large-image or adequacy hypothesis. Naming them separately makes the Chebotarev compatibility transparent.

### 3.2 Split Taylor–Wiles adequacy

For the remainder of this chapter, regard $M=\operatorname{ad}^0(V)$ as a $k[\Gamma]$-module. If $\gamma\in\Gamma$ has distinct eigenvalues $a,b\in k$, let $e_{\gamma,a}$ be the projector onto the $a$-eigenline. Define

$$
\lambda_{\gamma,a}(X)=\operatorname{tr}(e_{\gamma,a}X).
\tag{3.1}
$$

We say that $\Gamma$ satisfies the **split Taylor–Wiles image conditions** if the following assertions hold for the underlying $\mathbf F_\ell[\Gamma]$-module of $M$:

1. $\Gamma$ has no nontrivial quotient of $\ell$-power order;
2. $H^1(\Gamma,M)=0$;
3. every nonzero $\Gamma$-stable $\mathbf F_\ell$-subspace $W\subseteq M$ has no nonzero quotient on which $\Gamma$ acts trivially;
4. for every such $W$, there exist a split regular semisimple $\gamma\in\Gamma$, an eigenvalue $a\in k$, and $w\in W$ such that

   $$
   \lambda_{\gamma,a}(w)\ne0.
   \tag{3.2}
   $$

Condition 1 is the no-$\ell$-quotient part of adequacy. Condition 2 is the cohomological part. Condition 4 is the semisimple detection part, strengthened only by requiring the detecting eigenvalues to lie in the chosen residue field. Condition 3 is the exact ingredient needed for cyclotomic disjointness of cohomology extensions.

In the usual rank-two, odd-characteristic terminology, adequacy consists operationally of the absence of an $\ell$-quotient, the vanishing of $H^1(\Gamma,M)$, and enough semisimple elements to detect every irreducible constituent of the adjoint. Absolute irreducibility of $V$ as a $\Gamma$-module supplies $H^0(\Gamma,M)=0$; absolute irreducibility only over $G_K$ does not by itself make that restriction assertion. The projector formulation (3.2) is the form of semisimple detection used in the prime-selection proof. Our split Taylor–Wiles conditions state that operational package in the residue field actually used locally and add the precise prime-field no-trivial-quotient clause that proves disjointness from the cyclotomic tower.

Conditions 3 and 4 are stated over the prime field because the Galois group cut out by one cocycle need only be an $\mathbf F_\ell$-subspace of the additive group of $M$; it need not be closed under multiplication by all of $k$. If the usual adequate-image theorem is invoked, one must verify these underlying-prime-field clauses and check that its detecting elements split over $k$. Splitting can be arranged by a finite extension of the coefficient residue field because the residual image is finite. Such an extension is harmless only after the coefficient ring and every local condition have been extended compatibly.

The formulation above is deliberately a sufficient package. In a particular application it may be enough to verify the four properties only for the submodules generated by restrictions of the actual dual Selmer classes. That weaker statement gives the same proof, but it is less convenient as a reusable theorem.

### 3.3 The classical two-dimensional large-image case

Suppose $\bar\rho|_{G_{K_1}}$ is absolutely irreducible. Then

$$
H^0(\Gamma,M)=0,
\tag{3.3}
$$

because an invariant trace-zero endomorphism would be a nonscalar residual endomorphism. This is necessary, but it is not the whole image lemma.

A robust sufficient large-image condition is that, after conjugation, $\Gamma$ contain $\operatorname{SL}_2(k_0)$ for a subfield $k_0\subseteq k$ for which the standard finite-group cohomology and no-$\ell$-quotient conclusions hold, and that $k$ contain the eigenvalues of the diagonal detecting elements. In the customary range $\ell\ge7$, absolute irreducibility together with the finite-subgroup adequacy theorem supplies the standard no-quotient, cohomological, and semisimple-spanning conclusions; the prime-field quotient clause and splitting field must still be read in the precise form above. In the common large-image case they follow directly from the explicit adjoint action. More generally, one may verify the four conditions directly.

The detection mechanism for a group containing a sufficiently large $\operatorname{SL}_2(k_0)$ is concrete. The module $M$ is generated by

$$
h=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
e=\begin{pmatrix}0&1\\0&0\end{pmatrix},
\qquad
f=\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$

Upper and lower unipotent conjugation move any nonzero stable subspace among these three directions, so a nonzero stable subspace is all of $M$ in the irreducible adjoint case. Choose $t\in k_0^\times$ with $t^2\ne1$ and put

$$
\gamma=\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix}.
$$

Then $\gamma$ is split regular semisimple and

$$
\lambda_{\gamma,t}(h)=1.
$$

This proves the detection condition. The vanishing of $H^1(\Gamma,M)$ is a finite-group calculation: normalize a cocycle on a diagonal torus, use the relations among upper and lower unipotents to force its values to be coboundaries, and then use generation by those subgroups. The exclusions in the small fields are precisely where there are too few diagonal elements or where this relation calculation acquires an exceptional class.

When the underlying $\mathbf F_\ell[\Gamma]$-module is irreducible and nontrivial, condition 3 is automatic. Every nonzero stable prime-field subspace is the entire additive module, and a trivial quotient would dualize to a trivial submodule of its prime-field dual. In less restrictive situations, irreducibility only over $k$ does not by itself settle this underlying-prime-field assertion, so it should be checked rather than inferred.

### 3.4 Small images and exceptional cases

Absolute irreducibility of $V$ should never be substituted mechanically for the four image conditions. Several failures are possible.

For $\ell=3$ or $5$, small projective images of tetrahedral or icosahedral type can support exceptional first cohomology or fail a semisimple spanning condition. These cases require a direct calculation; a theorem stated only as “absolutely irreducible” is too strong. Dihedral images require the same care. Their adjoint module generally decomposes, and each constituent arising from a cohomology class must have a split regular detector and no trivial quotient.

A residual image with a scalar or projectively scalar restriction is worse. Scalar Frobenius has no preferred eigenline, and the functional (3.1) is undefined. If $\bar\rho|_{G_{K_1}}$ becomes reducible, $M$ can acquire a trivial line. A cohomology extension carried by that line can intersect a cyclotomic layer, exactly invalidating the disjointness used later.

There is also a residue-field issue. Distinct eigenvalues in an algebraic closure do not define two lines over $k$. The local deformation ring over $\mathcal O$ then does not have the claimed ordered eigenline branch. One must enlarge $k$ and $\mathcal O$, or select a different conjugacy class whose characteristic polynomial splits over $k$.

At $\ell=2$ the field $\mathbf F_2$ has only one nonzero scalar, so a two-dimensional invertible matrix cannot have two distinct eigenvalues in $\mathbf F_2$. Larger fields of characteristic two may contain such elements, but the determinant and duality issues of Section 2.5 remain. Split regular Frobenius alone does not repair them.

The correct procedure in every exceptional case is therefore finite and testable: compute $H^1(\Gamma,M)$, list the stable submodules of $M$, test for trivial quotients, and test the functionals (3.1) on split regular elements. If one of these checks fails, either strengthen the image hypothesis, change coefficients, or use a different auxiliary-prime method. Chebotarev cannot cure the failure.

### 3.5 From semisimple spanning to the projector detector

The residual-image theory naturally produces a trace pairing with a semisimple matrix, whereas the local cohomology calculation naturally uses an eigenprojector. In dimension two these are the same detector on trace-zero matrices. Making this conversion explicit closes an otherwise easy-to-miss gap between image theory and prime selection.

Let $\gamma$ have distinct eigenvalues $a,b$ in $k$. Its projector onto the $a$-eigenline is the polynomial

$$
e_{\gamma,a}=\frac{\gamma-bI_2}{a-b}.
\tag{3.4}
$$

For $w\in M=\operatorname{ad}^0(V)$, one therefore has

$$
\lambda_{\gamma,a}(w)
=\operatorname{tr}(e_{\gamma,a}w)
=\frac{\operatorname{tr}(\gamma w)}{a-b},
\tag{3.5}
$$

because $\operatorname{tr}(w)=0$. Hence

$$
\operatorname{tr}(\gamma w)\ne0
\quad\Longleftrightarrow\quad
\lambda_{\gamma,a}(w)\ne0.
\tag{3.6}
$$

Suppose semisimple elements of $\Gamma$ span $\operatorname{End}_k(V)$. If $0\ne w\in M$, nondegeneracy of the trace pairing supplies a semisimple $\gamma\in\Gamma$ with $\operatorname{tr}(\gamma w)\ne0$. Such a $\gamma$ cannot be scalar, because a scalar pairs with $w$ through $\operatorname{tr}(w)=0$. In dimension two, a nonscalar semisimple matrix is regular semisimple. After a finite coefficient extension its eigenvalues lie in the residue field, and (3.6) gives the desired projector detector.

There are two qualifications. First, enlarging coefficients only makes the detector split; it does not enlarge the finite matrix image. The deformation coefficient ring, residual representation, local conditions, and duality pairings must all be extended together. Second, semisimple spanning detects each individual nonzero $w$. Condition 4 of Section 3.2 asks that some $w$ in every actual prime-field stable subspace be detected by a split element over the chosen $k$. This is automatic after one common finite coefficient extension because the image and the collection of stable subspaces are finite. If coefficients are not enlarged, split detection remains an additional hypothesis.

This calculation also explains why the projector, rather than merely the trace of $\gamma$, is the right local object. The quotient $M/(\operatorname{Ad}(\gamma)-1)M$ remembers the diagonal trace-zero direction relative to the two eigenlines. Formula (3.5) says that the residual-image trace pairing lands on exactly that quotient.

## 4. Cohomology extensions and compatible composita

Congruence, residual Frobenius, and cocycle detection live in different finite extensions. To ask for all three at one prime is to ask for one automorphism of their compositum, so their restrictions on every intersection must agree. This chapter turns a cohomology class into a finite translation extension and proves the fiber-product and disjointness lemmas that make the later Frobenius prescription honest.

### 4.1 The extension cut out by a cocycle

Let $z\in Z^1(G_{K,S},M')$. The cocycle identity says that

$$
g\longmapsto (z(g),g)
$$

is a homomorphism into the semidirect product $M'\rtimes G_{K,S}$, where $M'$ is written additively. After adjoining the finite residual and cyclotomic data, this homomorphism has finite image.

Let

$$
L=K(\bar\rho,\zeta_\ell).
$$

Here $K(\bar\rho)$ denotes the finite Galois extension fixed by $\ker\bar\rho$.

On $G_L$, both $\bar\rho$ and $\bar\epsilon$ are trivial. Hence $G_L$ acts trivially on $M'$, and

$$
z|_{G_L}:G_L\longrightarrow M
\tag{4.1}
$$

is an ordinary continuous homomorphism. Let $E_z$ be the fixed field of its kernel. Then

$$
\operatorname{Gal}(E_z/L)=W_z:=z(G_L),
\tag{4.2}
$$

an elementary abelian $\ell$-group contained in the additive group of $M$.

Conjugation by $\operatorname{Gal}(L/K_1)=\Gamma$ makes $W_z$ a $\Gamma$-stable $\mathbf F_\ell$-subspace of the additive group of $M$, and its $k$-span is a $k[\Gamma]$-submodule. Indeed, if $h\in G_L$ and $g$ maps to $\gamma\in\Gamma$, then the cocycle identity gives

$$
z(ghg^{-1})=\gamma z(h).
\tag{4.3}
$$

The translation terms involving $z(g)$ cancel because $h$ acts trivially on $M$.

Changing $z$ by a coboundary does not change (4.1): every coboundary vanishes on $G_L$. Thus $E_z/L$ depends on the cohomology class, not on the chosen cocycle representative.

### 4.2 Why a nonzero class gives a nontrivial extension

Let $x\in H^1(G_{K,S},M')$ be nonzero. Restriction to $G_{K_1}$ is injective because $[K_1:K]$ divides $\ell-1$ and restriction followed by corestriction is multiplication by that prime-to-$\ell$ degree.

On $G_{K_1}$ the coefficient is $M$, and inflation–restriction for

$$
1\longrightarrow G_L\longrightarrow G_{K_1}
\longrightarrow\Gamma\longrightarrow1
$$

begins

$$
0\longrightarrow H^1(\Gamma,M)
\longrightarrow H^1(G_{K_1},M)
\longrightarrow H^1(G_L,M)^\Gamma.
\tag{4.4}
$$

If $H^1(\Gamma,M)=0$, the restricted class cannot vanish on $G_L$. Therefore

$$
W_z\ne0.
\tag{4.5}
$$

This is the first decisive use of the image hypothesis. Without (4.4), a nonzero global class could be inflated entirely from the residual finite quotient and cut out no translation extension over $L$. Evaluating it on the residual kernel would then reveal nothing.

### 4.3 The exact compositum compatibility lemma

The following elementary lemma governs every simultaneous Frobenius prescription in this book.

**Lemma 4.1 (fiber product of Galois groups).** Let $E_1/K$ and $E_2/K$ be finite Galois extensions in a common algebraic closure, and put $I=E_1\cap E_2$. Restriction identifies

$$
\operatorname{Gal}(E_1E_2/K)
$$

with the fiber product

$$
\operatorname{Gal}(E_1/K)
\times_{\operatorname{Gal}(I/K)}
\operatorname{Gal}(E_2/K).
\tag{4.6}
$$

Consequently a pair $(\sigma_1,\sigma_2)$ is induced by an automorphism of $E_1E_2$ if and only if

$$
\sigma_1|_I=\sigma_2|_I.
\tag{4.7}
$$

For conjugacy classes, a class occurs in the compositum if and only if representatives can be chosen whose restrictions agree.

**Proof.** Restriction gives an injective homomorphism from the left side of (4.6) to the product, and every image pair agrees on $I$. Conversely, two agreeing automorphisms define a map on products by

$$
xy\longmapsto\sigma_1(x)\sigma_2(y),
\qquad x\in E_1, y\in E_2.
$$

Agreement on the intersection makes this map well defined on the tensor product image $E_1E_2$. It is a $K$-automorphism. Equivalently, the fiber product has order

$$
\frac{[E_1:K][E_2:K]}{[I:K]}
=[E_1E_2:K],
$$

so the injection is an isomorphism. The conjugacy statement follows by conjugating representatives before applying the same criterion. $\square$

For more than two extensions the lemma must be applied inductively. Pairwise trivial intersections do not by themselves imply joint linear disjointness: three quadratic fields can be pairwise distinct while one lies in the compositum of the other two. At the $j$th step one must compare the next field with the full compositum of the preceding fields.

The cyclotomic application is immediate. To prescribe identity on $K(\zeta_{\ell^N})$ and an automorphism $\sigma$ on another extension $E$, one must prove that $\sigma$ is trivial on

$$
E\cap K(\zeta_{\ell^N}).
$$

Arbitrary choices in the two factors are not legitimate.

### 4.4 Residual and cyclotomic disjointness

Let $K_N=K(\zeta_{\ell^N})$. The extension $K_N/K_1$ has $\ell$-power degree. If the image

$$
\Gamma=\bar\rho(G_{K_1})
$$

has no nontrivial $\ell$-power quotient, then

$$
K(\bar\rho)K_1\cap K_N=K_1
$$

inside the appropriate compositum, in the equivalent form

$$
\bar\rho(G_{K_N})=\bar\rho(G_{K_1})=\Gamma.
\tag{4.8}
$$

Indeed, a nontrivial intersection above $K_1$ would give a nontrivial common Galois quotient of $\Gamma$ and the $\ell$-group $\operatorname{Gal}(K_N/K_1)$. Every nontrivial finite $\ell$-group has a quotient of order $\ell$, contradicting the first image condition.

Thus every $\gamma\in\Gamma$ has a lift $g\in G_{K_N}$. This is exactly the compatibility between a prescribed residual conjugacy class and the congruence $q_v\equiv1\pmod{\ell^N}$.

### 4.5 Cohomology and cyclotomic disjointness

The cohomology extension requires a second argument. Put

$$
C_N=L K_N.
$$

The group $\operatorname{Gal}(C_N/L)$ is an $\ell$-group. More precisely, (4.8) gives $L\cap K_N=K_1$, so restriction identifies

$$
\operatorname{Gal}(C_N/K_1)
\simeq
\Gamma\times\operatorname{Gal}(K_N/K_1).
$$

Consequently conjugation by $\Gamma$ acts trivially on $\operatorname{Gal}(C_N/L)$: in this direct product the cyclotomic factor commutes with the residual factor.

**Lemma 4.2 (module disjointness).** Let $E/L$ be a finite elementary abelian $\ell$-extension, Galois over $K_1$, and let

$$
W=\operatorname{Gal}(E/L)
$$

with its $\Gamma$-action by conjugation. Let $C/L$ be a finite $\ell$-extension, Galois over $K_1$, on whose Galois group $\Gamma$ acts trivially. If $W$ has no nonzero trivial $\Gamma$-quotient, then

$$
E\cap C=L.
\tag{4.9}
$$

**Proof.** If $J=E\cap C$ were larger than $L$, then $\operatorname{Gal}(J/L)$ would be a nonzero $\Gamma$-equivariant quotient of both $W$ and $\operatorname{Gal}(C/L)$. Conjugation by $\Gamma$ is trivial on the latter group, and hence on this common quotient. This would be a nonzero trivial quotient of $W$, contrary to hypothesis. $\square$

Apply the lemma to $E_z/L$ and $C_N/L$. The group $W_z$ is a nonzero stable $\mathbf F_\ell$-subspace of $M$, and condition 3 of split Taylor–Wiles adequacy excludes a trivial quotient. Therefore

$$
E_z\cap C_N=L.
\tag{4.10}
$$

Equivalently, restriction from $G_{C_N}$ to $W_z$ is surjective. Every translation in $W_z$ can be realized by an element that is simultaneously trivial on $K_N$ and on the residual field.

### 4.6 Several cohomology classes and the independence trap

For classes $z_1,\ldots,z_r$, the combined homomorphism on $G_L$ is

$$
h\longmapsto(z_1(h),\ldots,z_r(h))\in M^r.
\tag{4.11}
$$

Its image need not be all of $M^r$. Intersections among the fields $E_{z_i}$ impose linear relations on the possible translation tuples. Thus one cannot prescribe $z_i(h)$ independently merely because the cohomology classes are linearly independent.

The exact object is the $\Gamma$-stable image $W_{\mathbf z}$ of (4.11). A translation tuple is compatible precisely when it lies in this image, and cyclotomic disjointness must be proved for every quotient of this actual module. Under stronger semisimplicity and multiplicity hypotheses, independence of the classes can force $W_{\mathbf z}=M^r$, but that conclusion is additional representation theory.

The inductive prime-selection argument avoids this trap. At each stage it chooses one surviving class and one prime. The next stage works inside the kernel imposed by the preceding prime. No simultaneous prescription of arbitrary translations in several possibly intersecting cohomology extensions is required.

### 4.7 A compatibility ledger for one cocycle

The construction can now be summarized without suppressing any intersection. Fix a nonzero class $x$, a representative $z$, and a level $N$. The fields and the jobs they perform are

$$
\begin{array}{c|c|c}
\text{field}&\text{Galois datum}&\text{condition at }v\\ \hline
K_N=K(\zeta_{\ell^N})&\epsilon_{\ell^N}&q_v\equiv1\pmod{\ell^N}\\
L=K(\bar\rho,\zeta_\ell)&\Gamma&\bar\rho(\varphi_v)=\gamma\\
E_z/L&W_z=z(G_L)&\lambda_{\gamma,a}(z(\varphi_v))\ne0.
\end{array}
\tag{4.12}
$$

The required automorphism is assembled over $L$, not by choosing three unrelated entries. The no-$\ell$-quotient condition proves

$$
L\cap K_N=K_1,
\tag{4.13}
$$

so every $\gamma\in\Gamma$ can be lifted while acting trivially on $K_N$. The no-trivial-quotient condition for $W_z$ proves

$$
E_z\cap LK_N=L,
\tag{4.14}
$$

so any required translation can be added without disturbing either the residual image or the cyclotomic value. Equations (4.13) and (4.14) are different disjointness statements proved from different image hypotheses.

Changing the cocycle representative does not alter this ledger. If $z'=z+\partial m$, then $z'|_{G_L}=z|_{G_L}$, so $E_{z'}=E_z$. At an element $g$ with residual part $\gamma$, the values differ by

$$
z'(g)-z(g)=(\operatorname{Ad}(\gamma)-1)m.
\tag{4.15}
$$

The projector functional kills the right side. Thus the nonvanishing condition is a property of the cohomology class and the residual conjugacy class, not of a representative.

Nor does changing the chosen lift of $\gamma$ cause trouble. Two lifts that agree on $LK_N$ differ by an element of the relevant translation group; Section 5.2 deliberately varies through precisely those translations. The affine variation of the detector is the freedom that avoids cancellation.

The ledger is also a practical test for extra requirements. If a further finite Galois extension $A/K$ is introduced, one appends a row and checks the intersection of $A$ with the full field already assembled. Pairwise checks with the three individual fields are not enough. This is why later splitting and avoidance assertions are always formulated through the full compatible fiber.

## 5. Regular semisimple detection

The value of a cocycle is not itself a local cohomology class: one must quotient by Frobenius coboundaries. Regular semisimple linear algebra provides a canonical one-dimensional detector for that quotient. Combining it with the translation extension will produce the exact Galois element that Chebotarev is later asked to realize.

### 5.1 The local linear-algebra quotient

The passage from a cocycle value to an unramified local cohomology class is controlled by a simple calculation. It is the point at which distinct eigenvalues become indispensable.

**Lemma 5.1 (regular semisimple detector).** Let $A\in\operatorname{GL}_2(k)$ have distinct eigenvalues $a,b\in k$, and let $M=\operatorname{ad}^0(k^2)$. Then

$$
\dim_k M/(\operatorname{Ad}(A)-1)M=1.
\tag{5.1}
$$

If $e_{A,a}$ is the projector onto the $a$-eigenline, the functional

$$
\lambda_{A,a}(X)=\operatorname{tr}(e_{A,a}X)
$$

annihilates $(\operatorname{Ad}(A)-1)M$ and induces an isomorphism

$$
M/(\operatorname{Ad}(A)-1)M\xrightarrow{\sim}k.
\tag{5.2}
$$

**Proof.** Choose an eigenbasis. With

$$
h=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\quad
e=\begin{pmatrix}0&1\\0&0\end{pmatrix},
\quad
f=\begin{pmatrix}0&0\\1&0\end{pmatrix},
$$

one has

$$
\operatorname{Ad}(A)h=h,
\qquad
\operatorname{Ad}(A)e=ab^{-1}e,
\qquad
\operatorname{Ad}(A)f=ba^{-1}f.
$$

The two off-diagonal eigenvalues are not $1$, so the image of $\operatorname{Ad}(A)-1$ is $ke\oplus kf$ and the quotient is represented by $h$. Moreover,

$$
e_{A,a}=\begin{pmatrix}1&0\\0&0\end{pmatrix},
$$

so $\lambda_{A,a}$ vanishes on $e$ and $f$ and takes value $1$ on $h$. This proves both assertions. $\square$

The lemma is basis independent. Replacing $A$ by a conjugate transports its projector, its image subspace, and the functional. Interchanging $a$ and $b$ negates the functional on $M$, so nonvanishing is unchanged.

### 5.2 Selecting a Galois element that detects one class

We now combine the image conditions with the disjointness results of Chapter 4.

**Lemma 5.2 (one-class image lemma).** Assume that $\ell$ is odd and that $\Gamma=\bar\rho(G_{K(\zeta_\ell)})$ satisfies the split Taylor–Wiles image conditions. Let

$$
0\ne x\in H^1(G_{K,S},M(1)),
$$

and choose a cocycle $z$ representing $x$. For every $N\ge1$, there exists $g\in G_{K,S}$ such that:

1. $g$ acts trivially on $K(\zeta_{\ell^N})$;
2. $A=\bar\rho(g)$ is split regular semisimple;
3. for one eigenvalue $a$ of $A$,

   $$
   \lambda_{A,a}(z(g))\ne0.
   \tag{5.3}
   $$

In particular, the image of $z(g)$ in

$$
M/(\operatorname{Ad}(A)-1)M
$$

is nonzero.

**Proof.** By Section 4.2, restriction of $z$ to $G_L$ is nonzero. Let $W=z(G_L)$, regarded as a nonzero $\Gamma$-stable $\mathbf F_\ell$-subspace of $M$. The detection condition supplies a split regular element $\gamma\in\Gamma$, an eigenvalue $a$, and some $w\in W$ with

$$
\lambda_{\gamma,a}(w)\ne0.
$$

Because every element of $W$ is an actual cocycle value, there is $h_0\in G_L$ for which

$$
\lambda_{\gamma,a}(z(h_0))\ne0.
\tag{5.4}
$$

Indeed, choose $h_0$ with $z(h_0)=w$.

Put $C_N=LK(\zeta_{\ell^N})$. By (4.10), restriction from $G_{C_N}$ onto $\operatorname{Gal}(E_z/L)$ is surjective. We may therefore choose $h\in G_{C_N}$ with the same cocycle value as $h_0$ for the purpose of (5.4). By residual–cyclotomic disjointness, choose $g_0\in G_{K(\zeta_{\ell^N})}$ with

$$
\bar\rho(g_0)=\gamma.
$$

For an integer $r$, set

$$
g_r=g_0h^r.
$$

Every $g_r$ is trivial on $K(\zeta_{\ell^N})$ and has residual image $\gamma$. Since $h$ acts trivially on $M$,

$$
z(h^r)=r z(h),
$$

and the cocycle identity gives

$$
z(g_r)=z(g_0)+r\operatorname{Ad}(\gamma)z(h).
\tag{5.5}
$$

The projector $e_{\gamma,a}$ commutes with $\gamma$, so

$$
\lambda_{\gamma,a}(\operatorname{Ad}(\gamma)z(h))
=\lambda_{\gamma,a}(z(h))\ne0.
$$

As $r$ ranges through the prime field $\mathbf F_\ell$, the right side of (5.5) is an affine line with nonzero direction after applying $\lambda_{\gamma,a}$. At most one value of $r$ makes it zero. Choose any other value. The resulting $g=g_r$ satisfies all three conditions, and Lemma 5.1 gives the final assertion. $\square$

The freedom to multiply $g_0$ by a translation element is essential. The value $z(g_0)$ may have zero diagonal projection or may cancel one chosen translation. Varying the power $h^r$ avoids that single cancellation.

### 5.3 Prescribing the residual eigenvalues

Lemma 5.2 chooses a detecting regular element supplied by the stable subspace $W$. In many large-image applications the residual conjugacy class can be fixed in advance.

Suppose $M$ is irreducible as a $k[\Gamma]$-module. Then the $k$-span of every nonzero $W=z(G_L)$ arising in the proof is all of $M$. For any fixed split regular $\gamma\in\Gamma$, the functional $\lambda_{\gamma,a}$ is nonzero on $M$. If it vanished on every element of $W$, it would vanish on the $k$-span of $W$, a contradiction. The proof of Lemma 5.2 therefore works with that fixed $\gamma$. All selected primes can be required to have residual Frobenius conjugate to $\gamma$, and hence to have the same prescribed unordered eigenvalue pair.

If $M$ is reducible, a fixed regular conjugacy class may annihilate one stable constituent. Then one may prescribe only a family $C(W)$ of allowed regular classes with the property that each nonzero stable subspace $W$ is detected by some member of $C(W)$. This is the exact general statement. Claiming an arbitrary prescribed eigenvalue pair without this detector condition is false.

The eigenvalues must lie in $k$. If they become distinct only over a finite extension $k'/k$, the local eigenlines and their universal lifts are defined over the enlarged coefficient ring with residue field $k'$, not over the original one.

### 5.4 Why three tempting substitutes fail

It is useful to isolate what Lemma 5.2 actually proves.

First, density of Frobenius elements does not imply that a nonzero cohomology class has nonzero value on a regular semisimple element. A cocycle is not a class function, and nonzero values may lie in the image of $\operatorname{Ad}(A)-1$. The regular detector and the translation extension are both needed.

Second, $H^0(\Gamma,M)=0$ is not a substitute for $H^1(\Gamma,M)=0$. The first says there are no invariant vectors. The second says a class cannot be inflated from the finite residual quotient. They govern different steps of the proof.

Third, pairwise disjointness of the residual field, cyclotomic field, and cohomology field is not enough when more auxiliary finite extensions are added. The prescribed tuple must lie in the iterated fiber product of all Galois groups. The safe procedure is to prove full linear disjointness over the current compositum or to check agreement on each successive intersection.

## 6. Chebotarev selection of auxiliary primes

All algebraic compatibility has now been settled, so the density theorem can do its proper job. This chapter passes the constructed element to a finite Galois quotient, obtains infinitely many primes with the desired arithmetic Frobenius, and explains how further splitting or avoidance conditions alter the compositum rather than the density argument.

### 6.1 The finite quotient carrying all conditions

Although $z$ is a cocycle on an infinite profinite group, all data relevant to Lemma 5.2 are finite. The residual representation has finite image. The cyclotomic character modulo $\ell^N$ has finite image. The additive group of $M$ is finite. Thus

$$
g\longmapsto
\bigl(\bar\rho(g),\epsilon_{\ell^N}(g),z(g)\bigr)
$$

factors through a finite semidirect-product quotient. Let $F_{z,N}/K$ be the corresponding finite Galois extension. The element constructed in Lemma 5.2 determines a conjugacy class in

$$
\operatorname{Gal}(F_{z,N}/K).
$$

The analytic distribution step is Book 142's Chebotarev theorem, with its complete proof and
normalizations. The matching is exact: $F_{z,N}/K$ is finite Galois; the constructed element
specifies one conjugacy class; arithmetic Frobenius is used on both sides; and the finite set to
be removed contains the ramified, coefficient-prime, and previously selected places. Density
only distributes this already compatible class. It does not create the detector or repair an
empty fiber product.

The following consequences are cited directly from Book 142 and used in the Taylor--Wiles
argument below.

**Lemma 6.1 (the analytic ray-class estimate).** The power-saving count for
narrow ray classes, with leading constant independent of the class, is Book 142, Corollary 4.2.
Its character-weighted consequence is the holomorphy at $s=1$ used in the former proof.

**Lemma 6.2 (nonvanishing and prime sums in an abelian extension).** Book
142, Theorem 5.1 gives the finite-order character prime sum after Book 142, Sections 5.2--5.3
prove holomorphy and nonvanishing at one. Applied through reciprocity to a finite abelian
extension $D/B$, it gives

$$
\sum_{w\text{ unramified in }D}\frac{\chi(\operatorname{Frob}_w)}{(\mathrm Nw)^s}=

\begin{cases}
\log(1/(s-1))+O(1),&\chi=1,\\
O(1),&\chi\ne1.
\end{cases}
$$

**Proposition 6.3 (abelian Frobenius distribution).** Book 142, Theorem 7.1
states that if $D/B$ is finite abelian with group $A$, then the unramified primes with
$\operatorname{Frob}_w=a$ have Dirichlet density $1/|A|$.

**Theorem 6.4 (finite Galois Frobenius selection).** Book 142, Theorem 9.1
is stronger than the form used here: for a finite Galois extension $F/K$ and a conjugacy class
$C\subseteq\operatorname{Gal}(F/K)$, the primes with arithmetic Frobenius class $C$ have
Dirichlet density $|C|/|\operatorname{Gal}(F/K)|$. Book 142, Corollary 10.1 permits deletion of
any finite set.

For simultaneous conditions, form the compositum of the finitely many Galois extensions. The
successive agreement-on-intersections criterion of Lemma 4.1 proves that the desired subset of
the compositum Galois group is nonempty. Choose one conjugacy class in it and apply Book 142,
Theorem 9.1. Thus residual conjugacy, cyclotomic identity, cocycle translation, complete
splitting in auxiliary fields, and compatible avoidance conditions are realized together.

Apply this imported theorem to $F_{z,N}/K$ and the class constructed in Lemma 5.2. Removing
finitely many further primes preserves positive density. This is the only Chebotarev use in the
Taylor--Wiles selection proof.

### 6.2 The one-class prime-selection theorem

**Theorem 6.5 (prime detecting a dual class).** Under the hypotheses of Lemma 5.2, let $T$ be any finite set of places containing $S$, the places above $\ell$, and all places ramified in any additionally specified finite extensions. For every nonzero

$$
x\in H^1_{\mathcal L^\perp}(K,M(1))
$$

and every $N\ge1$, there is a positive-lower-Dirichlet-density set of finite places $v\notin T$ such that:

1. $q_v\equiv1\pmod{\ell^N}$;
2. $\bar\rho$ is unramified at $v$ and $\bar\rho(\varphi_v)$ is split regular semisimple;
3. the localization

   $$
   \operatorname{loc}_v(x)\in H^1_{\mathrm{ur}}(K_v,M(1))
   $$

   is nonzero;
4. the residual Frobenius class may be required to lie in any detecting family allowed by Section 5.3.

**Proof.** Choose the element $g$ of Lemma 5.2 and apply Theorem 6.4 to its conjugacy class in $F_{z,N}/K$. For every resulting unramified prime,

$$
\epsilon_{\ell^N}(\varphi_v)=q_v\equiv1\pmod{\ell^N},
$$

and residual Frobenius is conjugate to $\bar\rho(g)$, so it is split regular semisimple. The dual class is unramified outside $S$. Under the identification (2.7), Lemma 5.1 says that its localization is nonzero because the detector applied to $z(g)$ is nonzero. Finally remove the finite set $T$. $\square$

The conclusion is invariant under conjugacy. If Frobenius is represented by $ugu^{-1}$ in the finite quotient, the cocycle value changes by the corresponding affine conjugation, but its class in the appropriate coinvariant quotient is transported isomorphically. Nonvanishing is therefore a property of the Frobenius conjugacy class.

### 6.3 Additional splitting and avoidance conditions

There are two different meanings of “avoidance.” A finite list of places can always be avoided by deleting it from the infinite Chebotarev set constructed above. Avoiding a Frobenius behavior in another extension is a new Galois condition and must be checked in a compositum.

Let $A/K$ be a finite Galois extension and suppose one wishes to require

$$
\operatorname{Frob}_v(A/K)\in C_A
$$

for a conjugacy-stable subset $C_A$. Form $F_{z,N}A$. By Lemma 4.1, the desired combined condition exists exactly when some representative of the detecting class in $\operatorname{Gal}(F_{z,N}/K)$ and some representative in $C_A$ agree on

$$
F_{z,N}\cap A.
\tag{6.12}
$$

If the two extensions are linearly disjoint over $K$, every pair is compatible. If not, the restrictions must be compared. Requiring $v$ to split completely in $A$ means choosing the identity, so the detecting element must act trivially on the intersection. Requiring $v$ not to split completely means choosing a nonidentity element in a compatible fiber; such an element need not exist.

For several auxiliary extensions, apply the fiber-product criterion successively. If the compatible fiber contains several elements and finitely many unwanted conjugacy subsets are to be avoided, it suffices that their union not exhaust the fiber. This elementary nonexhaustion check is the exact hypothesis behind simultaneous avoidance.

Once that check has produced one allowed element in the Galois group of the full compositum, its conjugacy class lies in the allowed locus. The simultaneous form following Theorem 6.4 then gives a positive-lower-density set of primes satisfying every condition at once. Thus complete splitting, prescribed nontrivial Frobenius, and avoidance do not consume density one condition at a time; their only possible obstruction is emptiness of the combined fiber.

One particularly useful harmless condition is pairwise disjointness of the chosen prime sets as $N$ varies. At each finite stage, all primes selected earlier form a finite set. Adding them to $T$ in Theorem 6.5 produces a new set avoiding every earlier prime.

### 6.4 Diagnostic example: one dual Selmer class

Suppose the dual Selmer group is one-dimensional, generated by $x$. Let the image lemma choose

$$
\gamma=\begin{pmatrix}\bar a&0\\0&\bar b\end{pmatrix},
\qquad \bar a\ne\bar b,
$$

and suppose, after choosing an eigenbasis, that the selected Frobenius has

$$
z(\varphi_v)=
\begin{pmatrix}
c&u\\
w&-c
\end{pmatrix}.
$$

The image of $\operatorname{Ad}(\gamma)-1$ is the off-diagonal subspace. Hence

$$
\operatorname{loc}_v(x)\ne0
\quad\Longleftrightarrow\quad
c\ne0.
$$

The entries $u$ and $w$ are irrelevant to unramified local cohomology: they can be changed by a local coboundary. This is the simplest concrete reason that the matrix value $z(\varphi_v)\ne0$ is not enough. Chebotarev is asked to realize a finite-quotient element for which the diagonal coefficient $c$, not merely the entire matrix, is nonzero.

### 6.5 Density, conjugacy, and Frobenius normalization

Three normalizations are worth checking before passing from a Galois element to a local deformation condition.

First, Frobenius at a prime of $K$ is a conjugacy class, not a distinguished element of the global Galois group. If $z$ is a cocycle and $g$ is replaced by $ugu^{-1}$, a direct use of the cocycle identity gives

$$
z(ugu^{-1})
=u\cdot z(g)+(1-ugu^{-1})z(u),
\tag{6.13}
$$

after identifying the coefficient action in the usual way. The second term is a coboundary for the action of $ugu^{-1}$, while the first transports the class by $u$. Therefore the class of $z(g)$ in the Frobenius coinvariant quotient is nonzero if and only if the corresponding class at $ugu^{-1}$ is nonzero. The detector used in Theorem 6.5 is consequently conjugacy invariant even though a cocycle itself is not a class function.

Second, the density theorem excludes primes ramified in the finite selection field. That exclusion automatically removes every place at which the residual representation, the cyclotomic extension, or the cocycle quotient used in the selection is ramified. Adding the original set $S$ and any prescribed finite avoidance set changes a set of positive lower Dirichlet density by only finitely many places. Hence the conclusion is not merely that one prime exists: each inductive step retains infinitely many choices after all earlier choices have been excluded.

Third, throughout this book arithmetic Frobenius acts on a residue field by $x\mapsto x^{q_v}$. With the arithmetic normalization of local reciprocity, a uniformizer maps to arithmetic Frobenius. Thus

$$
\epsilon_{\ell^N}(\varphi_v)=q_v\pmod{\ell^N}
\tag{6.14}
$$

and the tame relation is

$$
\varphi_v\tau_v\varphi_v^{-1}=\tau_v^{q_v}.
\tag{6.15}
$$

If geometric Frobenius were used instead, both the cyclotomic value and the reciprocity character would be inverted. The congruence $q_v\equiv1\pmod{\ell^N}$ is invariant under inversion, but eigenvalue labels and universal characters would be reversed. Fixing the arithmetic convention makes the local and global formulas literally compatible rather than compatible only up to inverses.

The exact density $|C|/|G|$ is not needed in the induction; positivity is enough. Nevertheless density matters conceptually. It says that the auxiliary conditions do not identify an accidental isolated prime. Once compatibility has produced a nonempty conjugacy class, the arithmetic primes realizing it form a robust supply from which finite avoidance and successive choices may be made.

## 7. The local Taylor–Wiles condition

The global image lemma only chooses places. To use them in a deformation problem, one needs a local condition whose extra tangent direction is exactly one-dimensional and whose dual orthogonal is exactly strict. This chapter builds that condition from tame inertia, a chosen Frobenius eigenline, and fixed determinant, then performs the full local cohomology calculation.

### 7.1 Tame generators and the chosen residual branch

Let $v\nmid\ell$ be a place outside $S$. Assume

$$
q_v\equiv1\pmod\ell
$$

and, after choosing a residual basis,

$$
\bar\rho(\varphi_v)=
\begin{pmatrix}\bar\alpha_v&0\\0&\bar\beta_v\end{pmatrix},
\qquad
\bar\alpha_v\ne\bar\beta_v,
\qquad
\bar\rho(I_v)=1.
\tag{7.1}
$$

Choose the $\bar\alpha_v$-eigenline. This ordered choice is part of the local datum. Since the two residual eigenvalues are distinct, idempotent lifting gives a unique direct summand lifting each eigenline in every Artinian deformation belonging to the split branch.

Let $\varphi_v,\tau_v$ generate the maximal tame quotient, with

$$
\varphi_v\tau_v\varphi_v^{-1}=\tau_v^{q_v}.
\tag{7.2}
$$

The determinant $\delta$ is unramified at $v$, because $v\notin S$. A Taylor–Wiles deformation over an Artinian $\mathcal O$-algebra $A$ is a fixed-determinant lift equipped with a $G_{K_v}$-stable decomposition

$$
A^2=L_{\alpha}\oplus L_{\beta}
\tag{7.3}
$$

lifting the ordered residual eigenspaces, such that the two characters on these lines have the form

$$
\chi_{\alpha}=\eta\theta,
\qquad
\chi_{\beta}=\delta\chi_{\alpha}^{-1}.
\tag{7.4}
$$

Here $\eta$ is unramified and $\theta$ is a tamely ramified $\ell$-power-order character, trivial on Frobenius and on principal units. The determinant on inertia is therefore

$$
\theta\theta^{-1}=1,
$$

as required.

This is sometimes called the ordinary condition at $v$: it remembers a chosen stable line and allows a character on it. The word has no Hodge-theoretic meaning here because $v\nmid\ell$.

One could begin with only the chosen stable line rather than the direct-sum decomposition. In the present regular situation the two formulations agree. An extension between the two residual character lines is governed by a one-dimensional coefficient character whose Frobenius value is $\bar\alpha_v\bar\beta_v^{-1}$ or its inverse. This value is neither $1$ nor $q_v$ in $k$, because $q_v=1$ and the eigenvalues are distinct. The local Euler characteristic calculation therefore gives vanishing of the corresponding $H^1$. Successive lifting across small extensions splits the ordinary representation uniquely up to the diagonal changes already recorded. Writing the decomposition in (7.3) makes this vanishing visible in the definition and avoids carrying a redundant extension parameter.

### 7.2 Why the tame relation is satisfied

In a basis adapted to (7.3), write

$$
F=\rho(\varphi_v)=
\begin{pmatrix}a&0\\0&D_va^{-1}\end{pmatrix},
\qquad
T=\rho(\tau_v)=
\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix},
\tag{7.5}
$$

where

$$
D_v=\delta(\varphi_v).
$$

If $t$ has order dividing $\ell^N$ and $q_v\equiv1\pmod{\ell^N}$, then

$$
T^{q_v}=T.
$$

Since $F$ and $T$ commute, (7.2) holds. Conversely, the local reciprocity construction in Section 8.2 produces all characters of the stipulated residue-field quotient, so no tame character in that finite branch is missing.

The inverse character on the second line is forced by fixed determinant. Allowing a tame character on only one line while insisting that an unramified determinant remain fixed would be inconsistent unless that character were trivial.

### 7.3 The complete first-order calculation

Put

$$
r=\bar\alpha_v\bar\beta_v^{-1}.
$$

On the basis $h,e,f$ of $M$ used in Lemma 5.1, residual Frobenius acts with eigenvalues

$$
1,\quad r,\quad r^{-1}.
$$

Because $r\ne1$ and $q_v=1$ in $k$, linearizing the tame relation gives

$$
(\operatorname{Ad}(\bar\rho(\varphi_v))-1)Y=0,
$$

where $Y$ is the value of a cocycle on tame inertia. Thus $Y$ lies in $kh$. The Frobenius value $X$ is arbitrary before quotienting by strict conjugacy; coboundaries remove its two off-diagonal components. Therefore

$$
H^1(K_v,M)=k\,u_v\oplus k\,t_v,
\tag{7.6}
$$

where $u_v$ is represented by

$$
c(\varphi_v)=h,\qquad c(\tau_v)=0,
$$

and $t_v$ by

$$
c(\varphi_v)=0,\qquad c(\tau_v)=h.
$$

The unramified local condition is

$$
L_v^{\mathrm{ur}}=k\,u_v,
\tag{7.7}
$$

while the Taylor–Wiles condition has tangent space

$$
L_v^{\mathrm{TW}}=k\,u_v\oplus k\,t_v
=H^1(K_v,M).
\tag{7.8}
$$

In particular,

$$
\dim_k L_v^{\mathrm{TW}}/L_v^{\mathrm{ur}}=1.
\tag{7.9}
$$

Local Tate duality gives

$$
(L_v^{\mathrm{ur}})^\perp
=H^1_{\mathrm{ur}}(K_v,M'),
\qquad
(L_v^{\mathrm{TW}})^\perp=0.
\tag{7.10}
$$

The first space on the right is one-dimensional. Thus changing from unramified to Taylor–Wiles makes the dual condition strict, exactly as the global argument requires.

No off-diagonal tangent direction has been forgotten. The two off-diagonal Frobenius values are coboundaries because $r,r^{-1}\ne1$. Off-diagonal tame values would require $r=q_v$ or $r^{-1}=q_v$ in $k$, which would force $r=1$ under $q_v\equiv1\pmod\ell$, contrary to distinct eigenvalues.

### 7.4 The pairing in coordinates

The two lines in (7.6) are complementary under local duality. Up to a nonzero scalar determined by reciprocity normalization, the pairing has the shape

$$
\langle a u_v+b t_v, a'u_v'+b't_v'\rangle_v
=ab'-ba'.
\tag{7.11}
$$

Here the primed basis belongs to $H^1(K_v,M')$ and is defined using the trace pairing. Consequently the unramified line is its own exact orthogonal in the primed space, while the full plane has orthogonal zero. Formula (7.11) is a useful diagnostic, but (7.10), obtained from exact local duality, is the invariant statement.

### 7.5 What fails at scalar or nonsplit Frobenius

If residual Frobenius is scalar, $r=1$ and every element of $M$ is fixed. Both unramified and tame tangent dimensions jump, no eigenline is distinguished, and strict conjugacy acts trivially on the first-order Frobenius matrix. The local condition above is not represented by the rings claimed in Chapter 8.

If the characteristic polynomial is irreducible over $k$, Frobenius is regular semisimple only after a quadratic residue-field extension. There is then no rank-one residual eigenspace over $k$. One may formulate a nonsplit torus condition, but its diamond symmetry and local coordinates differ from (7.3)–(7.5). The theorem below deliberately selects split Frobenius instead.

If $q_v\not\equiv1\pmod\ell$, the diagonal tame direction vanishes. The residue-field unit group also has no nontrivial $\ell$-quotient. Such a prime cannot provide a Taylor–Wiles variable.

### 7.6 Why every permitted extension splits

The direct-sum normal form in Section 7.1 should not be accepted merely because the residual Frobenius has two eigenlines. Over a nonreduced coefficient ring, distinct residual characters can in principle admit extensions. Here the tame relation rules them out. We prove the needed vanishing uniformly over small extensions.

Let $\bar\chi_1,\bar\chi_2$ be the two unramified residual characters and put

$$
\bar\psi=\bar\chi_1\bar\chi_2^{-1},
\qquad
\bar\psi(\varphi_v)=r\ne1.
\tag{7.12}
$$

An extension of $\bar\chi_2$ by $\bar\chi_1$ is governed to first order by $H^1(K_v,k(\bar\psi))$. For an unramified one-dimensional module on which Frobenius acts by $r$, a tame cocycle has values $X$ on $\varphi_v$ and $Y$ on $\tau_v$. Linearizing the tame relation gives

$$
(r-q_v)Y=0,
\tag{7.13}
$$

while changing the splitting changes $X$ by an element of $(r-1)k$. At a Taylor--Wiles prime, $q_v=1$ in $k$, so both $r-q_v$ and $r-1$ are nonzero. Hence $Y=0$ and $X$ is a coboundary:

$$
H^1(K_v,k(\bar\psi))=0.
\tag{7.14}
$$

The same calculation with $\bar\psi^{-1}$ proves vanishing in the opposite extension direction.

Now let $A'\twoheadrightarrow A$ be a small surjection of local Artinian $\mathcal O$-algebras with kernel $J$, and suppose a representation satisfying the chosen stable-line formulation over $A'$ reduces over $A$ to a split one. Choose lifts of the two summands. The off-diagonal failure of the lifted matrices to preserve them is a cocycle with coefficients in

$$
J\otimes_k k(\bar\psi)
\quad\text{or}\quad
J\otimes_k k(\bar\psi^{-1}).
$$

By (7.14) it is a coboundary. Conjugating by an off-diagonal matrix congruent to the identity kills it. Induction on the length of $A$ gives a splitting at every Artinian level. Uniqueness follows from $H^0(K_v,k(\bar\psi))=H^0(K_v,k(\bar\psi^{-1}))=0$: two splittings differ by an invariant off-diagonal homomorphism, hence agree up to the diagonal automorphisms already divided out in the unframed problem.

There is an equivalent idempotent proof. The characteristic polynomial of Frobenius factors modulo the maximal ideal as two coprime linear factors. Hensel lifting produces unique orthogonal Frobenius projectors. The vanishing above says inertia preserves those projectors; otherwise its off-diagonal entry would give a nonzero tame extension class. Thus the two methods establish the same ordered stable decomposition.

This proof uses both hypotheses. If $r=1$, unramified extensions survive. If $r=q_v$ or $r=q_v^{-1}$, a tame extension survives in one direction. At a Taylor--Wiles prime $q_v=1$ modulo $\ell$, distinct eigenvalues exclude all three equalities simultaneously.

## 8. Universal local deformation rings

Tangent spaces explain the numerical exchange, but the later global ring needs an integral local object. The chosen regular branch is simple enough that both the unramified and Taylor–Wiles functors have explicit universal rings. Their equations reveal which directions are smooth matrix coordinates, which direction is a finite diamond character, and how augmentation returns to the unramified problem.

### 8.1 The unrestricted unramified branch

Fix a lift $\widetilde\alpha_v\in\mathcal O^\times$ of the chosen residual eigenvalue and retain the $\bar\alpha_v$-branch. The determinant will set the complementary eigenvalue, so no independent lift of $\bar\beta_v$ is part of the fixed-determinant datum. An unramified fixed-determinant lift is determined up to strict equivalence by the eigenvalue

$$
a=\widetilde\alpha_v(1+X)
$$

on the chosen line. The other eigenvalue is $D_va^{-1}$. Hensel lifting of the two coprime residual factors shows that every unramified lift has a unique ordered eigenspace decomposition and is strictly equivalent to this diagonal form. Hence

$$
\boxed{
R_v^{\mathrm{ur},\delta,\alpha}
\simeq\mathcal O[[X]].}
\tag{8.1}
$$

This is the unrestricted unramified condition on the chosen residual branch: trace, or equivalently the chosen eigenvalue, is free; only determinant and inertia have been fixed. The ring is formally smooth over $\mathcal O$ of relative dimension one, and its tangent space is the line (7.7).

Without choosing an eigenvalue, the same unframed functor can be parametrized by trace because residual Frobenius is nonscalar. The $\alpha$-coordinate and the trace coordinate are related by an invertible formal change of variable. What is not legitimate is to merge this branch with a scalar residual point or to claim one smooth quotient simultaneously chooses either eigenline.

### 8.2 The finite diamond quotient

Assume now that

$$
q_v\equiv1\pmod{\ell^N}.
$$

Because $k(v)^\times$ is cyclic, it has a unique quotient of order $\ell^N$:

$$
\Delta_v(N)
=k(v)^\times/(k(v)^\times)^{\ell^N}.
\tag{8.2}
$$

When no confusion is possible, write $\Delta_v=\Delta_v(N)$. One may instead use the maximal $\ell$-power quotient $\Delta_v^{\max}$; the group in (8.2) is its canonical quotient of order $\ell^N$.

Let

$$
\boldsymbol\theta_v:G_{K_v}\longrightarrow
\mathcal O[\Delta_v]^\times
\tag{8.3}
$$

be the universal tame character defined as follows. Choose a uniformizer $\pi_v$ and first put

$$
\pi_v^n u\longmapsto[\bar u],
\qquad n\in\mathbf Z,\quad u\in\mathcal O_{K_v}^\times,
$$

where $\bar u$ is the image under reduction

$$
\mathcal O_{K_v}^\times\longrightarrow k(v)^\times,
$$

projection to $\Delta_v$, and the group-like embedding

$$
d\longmapsto[d]\in\mathcal O[\Delta_v]^\times.
$$

This character of $K_v^\times$ has open kernel, so arithmetic local reciprocity transports it uniquely to (8.3). It is trivial on the chosen uniformizer and on principal units. Replacing $\pi_v$ by a unit multiple changes the separation between its tame and unramified factors, but the product $\eta_X\boldsymbol\theta_v$ below changes only by a formal reparametrization of $X$. This convention makes the tame character itself, rather than its inverse, the group-like element. Changing the reciprocity convention would invert every diamond element and must be done consistently everywhere.

### 8.3 The unframed Taylor–Wiles ring

Over

$$
\mathcal O[\Delta_v][[X]],
$$

define

$$
\chi_\alpha=\eta_X\boldsymbol\theta_v,
\qquad
\chi_\beta=\delta\chi_\alpha^{-1},
\tag{8.4}
$$

where $\eta_X$ is the unramified character sending arithmetic Frobenius to $\widetilde\alpha_v(1+X)$. Their direct sum is the universal enhanced Taylor–Wiles deformation. Conversely, every object of the functor has a unique ordered stable decomposition and is obtained from a unique value of $X$ and a unique character of $\Delta_v$. Therefore

$$
\boxed{
R_v^{\mathrm{TW},\delta,\alpha}
\simeq\mathcal O[\Delta_v][[X]].}
\tag{8.5}
$$

The ring is finite free over $\mathcal O[[X]]$ of rank $|\Delta_v|=\ell^N$. It is formally smooth of relative dimension one over the base $\mathcal O[\Delta_v]$. It is not formally smooth over $\mathcal O$ when $N>0$.

To see the last point explicitly, choose a generator $d_v$ of $\Delta_v$ and put $Y=[d_v]-1$. Then

$$
R_v^{\mathrm{TW},\delta,\alpha}
\simeq
\mathcal O[[X,Y]]/\bigl((1+Y)^{\ell^N}-1\bigr).
\tag{8.6}
$$

The derivative of the displayed relation vanishes at the residual point modulo $\ell$, so the special-fiber tangent space has dimension two, represented by $X$ and $Y$. These are exactly the unramified and tame directions in (7.8).

### 8.4 Framed rings and eigenline coordinates

A frame remembers the position of the two eigenlines inside the fixed residual basis. Near the residual decomposition, every ordered pair of complementary lifted lines has a unique representative of the form

$$
P(U,V)=
\begin{pmatrix}
1&U\\
V&1
\end{pmatrix}
$$

modulo right multiplication by a diagonal matrix. Since $U,V$ are in the maximal ideal, $1-UV$ is a unit.

Conjugating the diagonal universal matrices by $P(U,V)$ gives

$$
\boxed{
R_v^{\square,\mathrm{ur},\delta,\alpha}
\simeq\mathcal O[[X,U,V]],}
\tag{8.7}
$$

and

$$
\boxed{
R_v^{\square,\mathrm{TW},\delta,\alpha}
\simeq\mathcal O[\Delta_v][[X,U,V]].}
\tag{8.8}
$$

The first ring is formally smooth over $\mathcal O$ of relative dimension three. This agrees with the general fixed-determinant framed unramified count $2^2-1=3$. The second is formally smooth over $\mathcal O[\Delta_v]$ of relative dimension three. Its special-fiber tangent dimension over $k$ is four: three matrix directions and one diamond direction.

The two framing coordinates are not diamond variables. They record strict changes in eigenline position and disappear from the unframed functor. The diamond coordinate records tame inertia and survives unframed.

### 8.5 Components and the augmentation map

After extending the fraction field so that it contains all $\ell^N$th roots of unity, the group algebra splits:

$$
E'[\Delta_v]\simeq
\prod_{\psi:\Delta_v\to E'^\times}E'.
$$

Thus the generic fiber of (8.5) is a disjoint union of $\ell^N$ smooth one-dimensional formal branches, one for each diamond character. The framed generic fiber has the same number of smooth three-dimensional branches. Integrally these branches meet at the single residual point of the local group algebra. This is why the whole integral ring is not smooth over $\mathcal O$ even though every characteristic-zero character branch is smooth.

This component statement concerns diamond characters after the residual eigenline branch has already been chosen. If one allows both residual eigenline choices as separate enhancements, one obtains two ordered copies related by swapping the characters and inverting the diamond character. One must select one copy before using (8.5). There is no assertion of smoothness across an unchosen union of eigenvalue branches.

Let

$$
\operatorname{aug}:\mathcal O[\Delta_v]\longrightarrow\mathcal O,
\qquad [d]\longmapsto1,
$$

be the augmentation. Setting the universal tame character to one gives canonical identifications

$$
R_v^{\mathrm{TW},\delta,\alpha}
\widehat\otimes_{\mathcal O[\Delta_v],\operatorname{aug}}\mathcal O
\simeq R_v^{\mathrm{ur},\delta,\alpha},
\tag{8.9}
$$

and

$$
R_v^{\square,\mathrm{TW},\delta,\alpha}
\widehat\otimes_{\mathcal O[\Delta_v],\operatorname{aug}}\mathcal O
\simeq R_v^{\square,\mathrm{ur},\delta,\alpha}.
\tag{8.10}
$$

In the displayed coordinates, the map from the Taylor–Wiles ring to the unramified ring is the quotient $Y\mapsto0$. There is also a map from the unramified coordinate ring into the Taylor–Wiles ring preserving $X,U,V$; it corresponds to taking the unramified companion of a split Taylor–Wiles representation by killing its tame character. This splitting depends on the enhanced ordered decomposition, which is why the eigenline choice was retained.

### 8.6 Diagnostic example: a split-Frobenius prime

Take $\ell=5$, suppose $q_v\equiv1\pmod{25}$, and suppose

$$
\bar\rho(\varphi_v)=
\begin{pmatrix}2&0\\0&3\end{pmatrix}
$$

over $k=\mathbf F_5$. The eigenvalues are distinct and the ratio is $4$, not $1$. Choose the first line and a generator $d$ of the quotient $\Delta_v(2)\simeq\mathbf Z/25\mathbf Z$. Then the unframed local rings have the forms

$$
R_v^{\mathrm{ur}}\simeq\mathcal O[[X]],
$$

and

$$
R_v^{\mathrm{TW}}
\simeq
\mathcal O[[X,Y]]/\bigl((1+Y)^{25}-1\bigr).
$$

At the residual point, $X$ varies the chosen Frobenius eigenvalue and $Y$ varies tame inertia by

$$
\tau_v\longmapsto
\begin{pmatrix}1+Y&0\\0&(1+Y)^{-1}\end{pmatrix}.
$$

The determinant is unchanged. Augmentation sends $Y$ to zero. The local primal tangent gains precisely the $Y$-line, and the dual orthogonal loses precisely its unramified line. The example simultaneously checks the tame relation, determinant, tangent count, and group-algebra equation.

### 8.7 The representing problem and its base changes

For precision, fix the category $\mathcal C_{\mathcal O}$ of complete Noetherian local $\mathcal O$-algebras with residue field $k$, and first evaluate deformation functors on its Artinian objects. At level $N$, the enhanced unframed Taylor--Wiles functor assigns to $A$ the strict-equivalence classes of triples

$$
(\rho_A,L_{\alpha,A},L_{\beta,A})
\tag{8.11}
$$

with fixed determinant, ordered stable direct summands lifting the residual eigenlines, and tame character killed by $\ell^N$. Strict equivalence is conjugacy by a matrix congruent to the identity carrying each ordered summand to its counterpart. Section 7.6 shows that the summands are uniquely determined by the representation inside this branch, but retaining them in the definition makes base change transparent.

To prove (8.5), associate to a triple its chosen Frobenius eigenvalue

$$
a\in\widetilde\alpha_v(1+\mathfrak m_A)
\tag{8.12}
$$

and its tame character

$$
\theta:I_v\longrightarrow1+\mathfrak m_A.
\tag{8.13}
$$

The latter is trivial on wild inertia and principal units and is killed by $\ell^N$, so local reciprocity makes it factor uniquely through $\Delta_v(N)$. Thus (8.12) is represented by $\mathcal O[[X]]$ and (8.13) by $\mathcal O[\Delta_v]$. Fixed determinant determines the second character. Conversely these two data construct the diagonal representation, and the congruence $\ell^N\mid q_v-1$ verifies the tame relation. The two constructions commute with every morphism $A\to B$. This proves representability, not just a bijection on tangent spaces.

For the framed functor, a frame is an identification of the underlying free module with $A^2$ reducing to the chosen residual basis. Relative to the ordered stable summands, frames form the formal neighborhood of the identity in

$$
\operatorname{GL}_2/\operatorname{GL}_1^2.
$$

The two coordinates $U,V$ of Section 8.4 represent that quotient. Diagonal changes act trivially on the diagonal characters and account for the quotient by $\operatorname{GL}_1^2$. This proves (8.8) functorially.

All displayed rings behave correctly under finite extension of coefficients. If $\mathcal O\to\mathcal O'$ is a finite local extension with residue field $k'$, and the residual data are scalar-extended, then

$$
R_v^{\mathrm{TW}}\widehat\otimes_{\mathcal O}\mathcal O'
\simeq
\mathcal O'[\Delta_v][[X]],
\tag{8.14}
$$

and similarly in the framed case. This is the coefficient enlargement used when a regular semisimple detector splits only over $k'$. It is harmless because the group $\Delta_v$ is arithmetic and unchanged, while the eigenline branch becomes defined over the larger residue field.

Base change along augmentation has a different meaning. It is not a coefficient extension; it specializes the universal tame character to the trivial character. The functorial proof above then leaves exactly the unramified Frobenius eigenvalue, giving (8.9) and (8.10). Confusing these two base changes would conflate enlarging the field of eigenvalues with removing auxiliary ramification.

## 9. Diamond symmetry for a finite set

One auxiliary prime produces one cyclic group-algebra direction; a global auxiliary set requires their product and the completed tensor product of all local rings. This chapter assembles those factors without confusing finite diamond variables with formal eigenvalue or framing coordinates. It also fixes the distinction between maximal and exact-level residue-field quotients.

### 9.1 Product groups and their completed group algebras

Let $Q$ be a finite set of Taylor–Wiles primes, all of level $N$. Put

$$
\Delta_Q=\prod_{v\in Q}\Delta_v(N).
\tag{9.1}
$$

Because each factor is a finite $\ell$-group, $\mathcal O[\Delta_v]$ is local with maximal ideal generated by the maximal ideal of $\mathcal O$ and the augmentation ideal. The same is true of $\mathcal O[\Delta_Q]$. Moreover,

$$
\widehat\bigotimes_{v\in Q,\mathcal O}\mathcal O[\Delta_v]
\simeq\mathcal O[\Delta_Q].
\tag{9.2}
$$

The completion notation is harmless here because every group algebra is finite free over $\mathcal O$, but it records the common closed point used when local deformation rings are combined.

The product augmentation is

$$
\operatorname{aug}_Q:\mathcal O[\Delta_Q]\longrightarrow\mathcal O,
\qquad [d_v]_{v\in Q}\longmapsto1.
\tag{9.3}
$$

Its **relative augmentation cotangent space over $\mathcal O$** has dimension $|Q|$ over $k$. Indeed, each cyclic factor contributes the class of $[d_v]-1$ modulo the square of the augmentation ideal and the coefficient maximal ideal. The absolute cotangent space of the local ring also contains the coefficient direction when that direction is counted; throughout the diamond ledger, cotangent dimensions are relative to $\mathcal O$.

### 9.2 The diamond character

At every $v\in Q$, the chosen eigenline carries the universal tame character $\boldsymbol\theta_v$. Their product is the local diamond datum

$$
\boldsymbol\theta_Q=\prod_{v\in Q}\boldsymbol\theta_v.
\tag{9.4}
$$

More precisely, the $v$th decomposition group maps to the $v$th factor of $\Delta_Q$, and all other factors act trivially there. Thus the universal local representation is naturally defined over an $\mathcal O[\Delta_Q]$-algebra.

The word “diamond” reflects the symmetry that appears when auxiliary level structures are varied by residue-field units. On the Galois side the essential datum is already visible: the same finite group is the quotient through which tame inertia acts on the chosen line. The inverse character acts on the complementary line because determinant is fixed.

Nothing in this construction asserts that a global module is free over $\mathcal O[\Delta_Q]$. Freeness is a later arithmetic property. Here we construct the group-algebra action on deformation rings and calculate its tangent direction.

### 9.3 Completed products of the local rings

Taking completed tensor products of (8.5) gives

$$
\boxed{
R_Q^{\mathrm{TW},\mathrm{loc}}
:=\widehat\bigotimes_{v\in Q,\mathcal O}
R_v^{\mathrm{TW},\delta,\alpha_v}
\simeq
\mathcal O[\Delta_Q][[X_v:v\in Q]].}
\tag{9.5}
$$

The framed product is

$$
\boxed{
R_Q^{\square,\mathrm{TW},\mathrm{loc}}
\simeq
\mathcal O[\Delta_Q]
[[X_v,U_v,V_v:v\in Q]].}
\tag{9.6}
$$

Thus every auxiliary prime contributes:

- one unframed Frobenius-eigenvalue coordinate;
- two additional framed eigenline-position coordinates;
- one finite diamond direction coming from the group algebra.

The first three coordinates are formally smooth relative to the diamond base. The diamond direction is finite flat and ramified over $\mathcal O$.

At augmentation, (8.9) and associativity of completed tensor products give

$$
R_Q^{\mathrm{TW},\mathrm{loc}}
\widehat\otimes_{\mathcal O[\Delta_Q],\operatorname{aug}_Q}\mathcal O
\simeq
\mathcal O[[X_v:v\in Q]],
\tag{9.7}
$$

and the framed analogue is the completed product of the unramified framed rings.

### 9.4 Maximal and exact-level quotients

If

$$
\ell^{a_v}\Vert(q_v-1),
$$

then the maximal $\ell$-power quotient of $k(v)^\times$ has order $\ell^{a_v}$. The congruence condition at level $N$ says only that $a_v\ge N$. There are consequently two legitimate conventions:

$$
\Delta_v^{\max}\simeq\mathbf Z/\ell^{a_v}\mathbf Z
$$

or its canonical quotient

$$
\Delta_v(N)\simeq\mathbf Z/\ell^N\mathbf Z.
$$

The exact-level convention makes all factors have the same order and is used in the theorem package. The maximal convention retains more finite tame characters. Passing from the maximal group to the exact-level group is a quotient on groups and hence a quotient on group algebras. The local tangent calculation is unchanged because both nontrivial cyclic $\ell$-groups have one-dimensional augmentation cotangent space.

These conventions must not be interchanged silently when comparing cardinalities or writing transition maps.

## 10. The enlarged global deformation problem

The local pieces must now be inserted into the original global datum. The central checks are variance of ring maps, recovery of the original problem at augmentation, and exact identification of the new primal and dual local conditions. Once these are in place, Poitou–Tate supplies a comparison sequence rather than a merely numerical prediction.

### 10.1 Definition of the datum at auxiliary level

Let $Q$ be disjoint from $S$. Enlarge the controlling set to

$$
S_Q=S\cup Q.
$$

Define the global deformation datum $\mathcal D_Q$ as follows:

- at every $v\in S$, retain the original local condition of $\mathcal D$;
- at every $v\in Q$, impose the enhanced Taylor–Wiles condition with chosen residual eigenvalue $\bar\alpha_v$ and diamond quotient $\Delta_v$;
- outside $S_Q$, impose the unramified condition;
- retain the fixed determinant $\delta$ everywhere.

In the last item, $\delta$ means its inflation along $G_{K,S_Q}\twoheadrightarrow G_{K,S}$, so it is unramified at $Q$. Enlarging the restricted Galois group from $G_{K,S}$ to $G_{K,S_Q}$ permits ramification at $Q$. The local Taylor–Wiles conditions then cut that permission down to the diagonal tame characters described in Chapter 7. One must not define $\mathcal D_Q$ merely by enlarging $S$: unrestricted ramification would have a larger and generally singular local deformation problem.

Let $R_{\mathcal D_Q}$ denote the unframed universal ring under the global Schur hypothesis, and use $R_{\mathcal D_Q}^{\square_T}$ for a chosen partial framing set $T$. The local maps make these rings naturally into $\mathcal O[\Delta_Q]$-algebras.

### 10.2 The full local base

Suppose the original partially framed global problem uses

$$
R_{\mathrm{loc},S}
=\widehat\bigotimes_{v\in T,\mathcal O}
R_v^{\square,\mathcal D_v}.
$$

If the auxiliary primes are also placed in the local framed base, the enlarged base is

$$
R_{\mathrm{loc},S,Q}
=R_{\mathrm{loc},S}
\widehat\otimes_{\mathcal O}
R_Q^{\square,\mathrm{TW},\mathrm{loc}}.
\tag{10.1}
$$

Using (9.6),

$$
R_{\mathrm{loc},S,Q}
\simeq
R_{\mathrm{loc},S}
\widehat\otimes_{\mathcal O}
\mathcal O[\Delta_Q]
[[X_v,U_v,V_v:v\in Q]].
\tag{10.2}
$$

The structural map points from local to global:

$$
R_{\mathrm{loc},S,Q}
\longrightarrow R_{\mathcal D_Q}^{\square_{T\cup Q}}.
\tag{10.3}
$$

This direction follows the usual contravariance of representing rings. The global ring is not asserted to be a quotient of $\mathcal O[\Delta_Q]$ alone; it is an algebra over the entire chosen local base.

### 10.3 Augmentation recovers the original problem

At every $v\in Q$, augmentation kills tame inertia and turns the Taylor–Wiles condition into the unrestricted unramified condition on the selected regular branch. Enlarging a controlling set while imposing the unramified condition at the new places does not change the original global deformation problem. Therefore

$$
\boxed{
R_{\mathcal D_Q}
\widehat\otimes_{\mathcal O[\Delta_Q],\operatorname{aug}_Q}
\mathcal O
\simeq R_{\mathcal D}.}
\tag{10.4}
$$

With compatible frames and local bases,

$$
R_{\mathcal D_Q}^{\square_T}
\widehat\otimes_{\mathcal O[\Delta_Q],\operatorname{aug}_Q}
\mathcal O
\simeq R_{\mathcal D}^{\square_T}.
\tag{10.5}
$$

The proof is functorial. An augmented Taylor–Wiles lift is unramified at $Q$, hence gives an object of $\mathcal D$. Conversely, an unramified lift at a place with distinct residual Frobenius eigenvalues has a unique ordered lifted eigenspace decomposition, so it acquires the augmented enhanced structure. These constructions are inverse and commute with coefficient change.

Distinct eigenvalues are used again here. At scalar Frobenius an unramified lift need not possess a unique chosen line, so the augmented enhanced functor would not equal the original unramified functor.

Contravariantly, the inclusion of the trivial-diamond fiber is the canonical quotient map

$$
R_{\mathcal D_Q}\longrightarrow R_{\mathcal D}.
$$

There is generally no canonical map in the reverse direction: unlike the local split companion construction of Section 8.5, deleting ramification independently at the places of $Q$ need not turn one global representation into another global representation. Together with (10.3), this records all comparison directions used here: local factors map to the enlarged global ring, and augmentation maps the enlarged global ring to the original one.

### 10.4 The new Selmer structures

Let $\mathcal L_Q$ be the tangent structure for $\mathcal D_Q$. At places of $S$ it equals $\mathcal L$. At $v\in Q$,

$$
(\mathcal L_Q)_v=H^1(K_v,M).
\tag{10.6}
$$

The dual condition is strict:

$$
(\mathcal L_Q^\perp)_v=0.
\tag{10.7}
$$

Thus

$$
H^1_{\mathcal L_Q^\perp}(K,M')
=\left\{
x\in H^1_{\mathcal L^\perp}(K,M'):
\operatorname{loc}_v(x)=0\text{ for every }v\in Q
\right\}.
\tag{10.8}
$$

Here the localization lies in the one-dimensional unramified line because the old class was unramified at $v$. Formula (10.8) is the exact cohomological meaning of killing dual Selmer with $Q$.

### 10.5 The five-term comparison sequence

Changing the local condition at every $v\in Q$ from unramified to full gives the Poitou–Tate comparison sequence

$$
\begin{aligned}
0\longrightarrow& H^1_{\mathcal L}(K,M)
\longrightarrow H^1_{\mathcal L_Q}(K,M)
\longrightarrow \bigoplus_{v\in Q}
\frac{H^1(K_v,M)}{H^1_{\mathrm{ur}}(K_v,M)}\\
\longrightarrow& H^1_{\mathcal L^\perp}(K,M')^*
\longrightarrow H^1_{\mathcal L_Q^\perp}(K,M')^*
\longrightarrow0.
\end{aligned}
\tag{10.9}
$$

Every local quotient in the middle is one-dimensional. The middle map is given by local Tate pairings: a new tame direction at $v$ is paired against the unramified localization of a dual class at $v$.

This exact sequence is stronger than a dimension formula. It identifies which dual classes disappear, whether the primal Selmer group grows, and how the two effects share the same local quotient.

### 10.6 The global augmentation isomorphism in detail

Equation (10.4) is stronger than the existence of a surjection between tangent spaces, so it deserves a proof on arbitrary coefficient rings. Let $A$ be an Artinian object of $\mathcal C_{\mathcal O}$. An $A$-point of

$$
R_{\mathcal D_Q}
\widehat\otimes_{\mathcal O[\Delta_Q],\operatorname{aug}_Q}
\mathcal O
\tag{10.10}
$$

is an enhanced $\mathcal D_Q$-deformation for which every universal diamond element acts as $1$. At $v\in Q$, the tame character is therefore trivial. The representation is unramified and its ordered summands are the two lifted Frobenius eigenspaces.

Forget those summands. By Section 2.6, a deformation of $G_{K,S\cup Q}$ unramified at all places of $Q$ descends uniquely to $G_{K,S}$. Its determinant and its local conditions at $S$ are unchanged, so it is an $A$-point of $\mathcal D$.

Conversely, take a deformation in $\mathcal D(A)$. Inflate it to $G_{K,S\cup Q}$. At every $v\in Q$, residual Frobenius has distinct eigenvalues, so its characteristic polynomial has two coprime residual factors. Hensel lifting produces two unique Frobenius-stable rank-one direct summands reducing to the chosen ordered eigenlines. Inertia is trivial, so the summands are $G_{K_v}$-stable. Giving them the trivial tame character makes an augmented enhanced Taylor--Wiles object.

The two operations are inverse. Forgetting and then reconstructing returns the same summands by uniqueness; inflating and then descending returns the same representation because $G_{K,S}$ is the quotient obtained by killing the normal closures of the new inertia groups. Both operations commute with $A\to B$, so they give an isomorphism of deformation functors. Representability then gives (10.4).

The argument also explains why the ring map points from the enlarged ring to the original ring. An inclusion of functors

$$
\mathcal D\simeq\mathcal D_Q|_{\operatorname{aug}}
\longrightarrow\mathcal D_Q
$$

is represented contravariantly by the quotient

$$
R_{\mathcal D_Q}\longrightarrow R_{\mathcal D}.
\tag{10.11}
$$

Its kernel contains the augmentation ideal generated by every $[d]-1$. The functorial argument proves that after quotienting by that ideal there are no further equations and no extra enhanced choices. A tangent-space isomorphism alone would not prove this integral statement.

For partial framings away from $Q$, the same proof carries the frames unchanged. If frames at $Q$ are included in the local base, augmentation replaces the enhanced framed local factors by their unramified framed factors; it does not delete the framing coordinates $U_v,V_v$. This is the precise framed form of (10.5).

## 11. Killing the dual Selmer group

The selection theorem detects one class, while the goal is to annihilate an entire finite-dimensional space. The key is to update the space after every choice: each prime cuts out the kernel of one nonzero functional, and the next prime is chosen against that kernel. This chapter proves the exact dimension drop and makes the independence mechanism visible in dimensions one and two.

### 11.1 The exact one-prime drop

Let $V$ be the current dual Selmer group and let $v$ be a Taylor–Wiles prime not used previously. The new dual group is

$$
V'=\ker\left(
V\xrightarrow{\operatorname{loc}_v}
H^1_{\mathrm{ur}}(K_v,M')
\right).
\tag{11.1}
$$

The target is one-dimensional. If $v$ is chosen by Theorem 6.5 to detect some nonzero $x\in V$, then the localization map is nonzero and hence surjective. Therefore

$$
\boxed{\dim_kV'=\dim_kV-1.}
\tag{11.2}
$$

This proves an exact drop, not merely a strict decrease. The one-dimensional target is essential. If the local quotient had larger dimension, detecting one class would show only that the kernel has positive codimension, not what that codimension is.

On the primal side, the one-prime version of (10.9) becomes

$$
0\to H^1_{\mathcal L}(K,M)
\to H^1_{\mathcal L'}(K,M)
\to k
\to V^*\to(V')^*\to0.
\tag{11.3}
$$

When $V\to k$ is nonzero, the dual map $k\to V^*$ is injective. Exactness then shows that the primal Selmer group does not grow at this step. The new local direction is consumed by removing one global dual constraint.

### 11.2 The inductive construction

Start with

$$
V_0=H^1_{\mathcal L^\perp}(K,M'),
\qquad \dim_kV_0=q.
$$

If $q=0$, take $Q=\varnothing$. Otherwise choose $0\ne x_0\in V_0$. Theorem 6.5 supplies a level-$N$ prime $v_1$ detecting it. Put

$$
V_1=\ker(\operatorname{loc}_{v_1}|_{V_0}).
$$

Then $\dim V_1=q-1$.

If $V_1\ne0$, choose any nonzero $x_1\in V_1$. Apply Theorem 6.5 again, adding $v_1$ to the finite avoidance set, and obtain $v_2$. Continue. After $i$ steps,

$$
V_i=\left\{
x\in V_0:\operatorname{loc}_{v_j}(x)=0
\text{ for }1\le j\le i
\right\},
\qquad
\dim V_i=q-i.
\tag{11.4}
$$

After $q$ steps, $V_q=0$. With

$$
Q_N=\{v_1,\ldots,v_q\},
$$

equation (10.8) gives

$$
H^1_{\mathcal L_{Q_N}^\perp}(K,M')=0.
\tag{11.5}
$$

This procedure preserves detection of all remaining classes in the only sense needed: the remaining space $V_i$ is a subspace of the original dual Selmer group, and the image lemma applies to every one of its nonzero elements. There is no need to preserve a previously chosen basis vector that no longer belongs to the kernel.

### 11.3 Diagnostic example: two independent classes

Suppose $V_0$ has basis $x_1,x_2$. Choose $v_1$ with a nonzero localization functional

$$
\lambda_1:V_0\to k.
$$

After replacing $x_2$ by a suitable linear combination, arrange

$$
\lambda_1(x_1)\ne0,
\qquad
\lambda_1(x_2)=0.
$$

Then $V_1=kx_2$. Choose $v_2$ so that its localization functional $\lambda_2$ satisfies

$$
\lambda_2(x_2)\ne0.
$$

The localization matrix is

$$
\begin{pmatrix}\lambda_1(x_1)&\lambda_1(x_2)\\\lambda_2(x_1)&\lambda_2(x_2)\end{pmatrix}=

\begin{pmatrix}
\ast&0\\
\ast&\ast
\end{pmatrix},
\tag{11.6}
$$

with nonzero diagonal entries. It is invertible, so the two strict dual conditions kill all of $V_0$. This triangular construction is what the induction proves. It does not assume that the two cohomology extensions are linearly disjoint or that both translation values can be prescribed in one Frobenius element.

### 11.4 Why the cardinality is dual, not primal

The construction begins with

$$
q=\dim_kH^1_{\mathcal L^\perp}(K,M').
$$

It uses $q$ primes because each strict dual local condition has codimension one and each selected localization has rank one. The primal dimension enters only through the global numerical identity.

If the original problem is balanced, then

$$
\dim_kH^1_{\mathcal L}(K,M)=q,
$$

so the two numbers happen to agree. That equality is a consequence of balance, not the definition of the cardinality. For a problem of defect $\Delta(\mathcal D)$,

$$
\dim_kH^1_{\mathcal L}(K,M)=q+\Delta(\mathcal D),
$$

and the selected set still has size $q$.

If some preliminary auxiliary primes are forced by a separate local requirement, first incorporate them into the deformation datum and recompute its dual Selmer group. If the forced set is $P$ and the recomputed dual dimension is $q_P$, the controlled total cardinality is

$$
|P|+q_P,
\tag{11.7}
$$

not $|P|+q$ by default. This is the precisely adjusted defect relevant to that enlarged starting problem.

### 11.5 The localization matrix criterion

The induction has a useful basis-free reformulation. For a finite set $Q$ of split regular primes, define

$$
\operatorname{loc}_Q:
V_0=H^1_{\mathcal L^\perp}(K,M')
\longrightarrow
\bigoplus_{v\in Q}H^1_{\mathrm{ur}}(K_v,M').
\tag{11.8}
$$

Each target summand is one-dimensional. By (10.8), the enlarged dual Selmer group is exactly $\ker(\operatorname{loc}_Q)$. Hence $Q$ kills dual Selmer if and only if $\operatorname{loc}_Q$ is injective.

If $|Q|=q=\dim V_0$, source and target have the same dimension. In this minimal-cardinality case the following conditions are equivalent:

1. $Q$ kills dual Selmer;
2. $\operatorname{loc}_Q$ is injective;
3. $\operatorname{loc}_Q$ is an isomorphism;
4. after choosing bases, its $q\times q$ localization matrix has nonzero determinant.

The induction constructs bases in which this matrix is triangular with nonzero diagonal. Indeed, choose $x_i$ in the kernel of the preceding $i$ localization rows and select $v_{i+1}$ so that the new row does not vanish on $x_i$. Reordering the resulting basis of $V_0$ gives the triangular form displayed in (11.6). Thus the proof establishes independence of the local functionals, rather than merely showing that every original basis vector is detected somewhere.

This criterion gives a sharp lower bound on cardinality. Since the target of $\operatorname{loc}_Q$ has dimension $|Q|$, injectivity requires

$$
|Q|\ge q.
\tag{11.9}
$$

Theorem 12.1 attains equality. Consequently the unpadded Taylor--Wiles set is not just one convenient choice: among primes with the one-dimensional local quotient used here, it has the smallest possible size.

For a padded set $|Q|>q$, injectivity remains the criterion, but surjectivity is impossible. The cokernel has dimension $|Q|-q$ and, through the five-term sequence, becomes exactly the new primal tangent contribution of the padding primes. This is the linear-algebra core of formulas (12.2) and (13.4).

## 12. Taylor–Wiles sets at every level

The inductive argument can be run with an arbitrary cyclotomic precision $N$. This chapter packages the result as a set of prescribed cardinality, distinguishes compatible extra conditions from wishful simultaneous prescriptions, and explains why sets at increasing levels are naturally nonnested. It also records the exact numerical price of padding the cardinality.

### 12.1 Existence with prescribed cardinality

The induction proves the central existence statement.

**Theorem 12.1 (Taylor–Wiles sets).** Assume the split Taylor–Wiles image conditions and the fixed-determinant global setup of Chapters 1–3. Let

$$
q=\dim_kH^1_{\mathcal L^\perp}(K,M(1)).
$$

For every integer $N\ge1$ and every finite avoidance set $T$, there exists a set $Q_N$ of finite places such that:

1. $Q_N\cap(S\cup T)=\varnothing$;
2. $|Q_N|=q$;
3. $q_v\equiv1\pmod{\ell^N}$ for every $v\in Q_N$;
4. $\bar\rho(\varphi_v)$ has two distinct eigenvalues in $k$, with a chosen eigenvalue $\bar\alpha_v$;
5. the exact-level diamond group satisfies

   $$
   \Delta_v(N)\simeq\mathbf Z/\ell^N\mathbf Z;
   $$

6. for the deformation problem $\mathcal D_{Q_N}$ with the local conditions of Chapter 7,

   $$
   H^1_{\mathcal L_{Q_N}^\perp}(K,M(1))=0.
   $$

If $M$ is irreducible under $\Gamma$, any fixed split regular residual conjugacy class may be used at every selected prime. In the general adequate case, the class at each step may be prescribed inside a detecting family for the current stable subspace.

**Proof.** If $q=0$, the empty set has all the stated properties. If $q>0$, apply the induction of Section 11.2. Theorem 6.5 supplies the congruence, split regular Frobenius, allowed residual conjugacy class, and avoidance at every step. Equation (11.2) proves that the dimension falls exactly once per prime, so the process stops after exactly $q$ distinct primes. The local reciprocity construction gives the exact-level diamond quotient, and (10.8) gives the final vanishing. $\square$

### 12.2 What simultaneous prescriptions can be retained

The theorem allows any finite collection of additional Frobenius requirements for which the iterated fiber product is nonempty. In particular, one may:

- exclude any finite list of places;
- require splitting in a finite extension disjoint from the selection field;
- prescribe a compatible conjugacy class in an auxiliary Galois extension;
- avoid finitely many conjugacy subsets that do not exhaust the compatible fiber;
- require all residual Frobenius elements to lie in one fixed detecting class when the adjoint image is irreducible.

Every adjective in this list has content. “Disjoint” means disjoint from the entire current compositum, including the cohomology extension used at that induction step. “Compatible” means agreement on the exact intersection. “Avoid” includes a nonexhaustion assertion. None follows solely from the infinitude of primes.

### 12.3 Nonnested sets are the natural outcome

The sets $Q_N$ should not be asserted to be nested as $N$ varies. A fixed finite place $v$ has a fixed integer

$$
a_v=v_\ell(q_v-1).
$$

It satisfies the level-$N$ congruence only for $N\le a_v$. Therefore no nonempty fixed finite set can satisfy the Taylor–Wiles congruence for arbitrarily large $N$.

If $|Q_N|=q$ is fixed, an inclusion

$$
Q_N\subseteq Q_{N+1}
$$

would force equality. Repeating this would make every prime persist at all higher levels, which is impossible. Thus an infinite nested sequence of nonempty sets of fixed cardinality cannot exist.

What can be arranged is the following:

- for any finite range $1\le N\le N_0$, one level-$N_0$ set works for every lower congruence level;
- for all $N$, sets may be chosen independently;
- by adding all previously used primes to the avoidance set, the sets may be chosen pairwise disjoint;
- after choosing generators, their abstract diamond quotients may all be compared with $(\mathbf Z/\ell^N\mathbf Z)^q$.

The last comparison is algebraic, not a nesting of primes or local fields.

### 12.4 Cardinality padding

Sometimes a later construction asks for a constant cardinality $r\ge q$. After selecting $q$ primes that kill dual Selmer, choose $r-q$ further split regular level-$N$ primes by Theorem 6.4, avoiding all existing places. Impose the same Taylor–Wiles local condition at them.

The new dual local conditions are stricter than before. Since the dual Selmer group is already zero, it remains zero:

$$
H^1_{\mathcal L_{Q'}^\perp}(K,M')
\subseteq
H^1_{\mathcal L_Q^\perp}(K,M')=0.
\tag{12.1}
$$

Thus padding cannot reintroduce dual Selmer.

Padding is not invisible on the primal side. With both old and new dual groups zero, the comparison sequence for an added prime reduces to

$$
0\longrightarrow H^1_{\mathcal L_Q}(K,M)
\longrightarrow H^1_{\mathcal L_{Q'}}(K,M)
\longrightarrow k\longrightarrow0.
\tag{12.2}
$$

Each padding prime adds one primal tangent direction and one diamond factor. Calling such a prime “trivial” means only that it is not needed to detect a surviving dual class. It does not mean that it has no numerical effect.

## 13. Numerical output and generator counts

After dual Selmer vanishes, the remaining information is a ledger of dimensions and algebra generators. This chapter translates the local one-dimensional changes into the global Wiles defect, keeps absolute and relative framing counts separate, and identifies the free pro-$\ell$ diamond variables approximated by the finite groups. These are the numbers that survive after the individual primes themselves recede from view.

### 13.1 Change in the Wiles defect

At a Taylor–Wiles prime the local tangent dimension changes from one to two, while $h^0(K_v,M)=1$ remains fixed. Therefore every auxiliary prime increases the right side of the global numerical identity by one:

$$
\boxed{
\Delta(\mathcal D_Q)=\Delta(\mathcal D)+|Q|.}
\tag{13.1}
$$

If $Q$ kills dual Selmer, then

$$
\dim_kH^1_{\mathcal L_Q}(K,M)
=\Delta(\mathcal D)+|Q|.
\tag{13.2}
$$

For the unpadded set $|Q|=q$, this equals

$$
\Delta(\mathcal D)+q
=\dim_kH^1_{\mathcal L}(K,M).
\tag{13.3}
$$

Thus the inductive killing steps leave the primal Selmer dimension unchanged: each new local direction is used to remove one dual condition. For a balanced problem, both sides of (13.3) are $q$. With $r-q$ padding primes, the primal dimension becomes

$$
\Delta(\mathcal D)+r.
\tag{13.4}
$$

These formulas distinguish three numbers that are often conflated:

$$
|Q|,
\qquad
\dim H^1_{\mathcal L_Q}(K,M),
\qquad
\dim H^1_{\mathcal L_Q^\perp}(K,M').
$$

Their values coincide only under additional numerical hypotheses.

### 13.2 Unframed and framed generators

Under the Schur hypothesis, the unframed tangent space of $R_{\mathcal D_Q}$ is $H^1_{\mathcal L_Q}(K,M)$. Hence the minimal number of topological algebra generators over $\mathcal O$ is

$$
g_Q^{\mathrm{unfr}}
=\dim_kH^1_{\mathcal L_Q}(K,M)
=\Delta(\mathcal D)+|Q|
\tag{13.5}
$$

when dual Selmer has been killed. In the balanced unpadded case this is $q$.

A single global frame adds the dimension of the coboundary space. For an absolutely irreducible rank-two residual representation,

$$
\dim_k B^1(K,\operatorname{ad}\bar\rho)
=4-1=3.
$$

Thus the corresponding fully framed global tangent has dimension

$$
g_Q^{\mathrm{global\ square}}
=g_Q^{\mathrm{unfr}}+3.
\tag{13.6}
$$

Partial local framings must use the exact invariant correction. If $T$ is the framing set, the relative generator count over the chosen local base is

$$
\boxed{
g_{T,Q}
=h^1_{\mathcal L_Q,T^0}(K,M)
+\sum_{v\in T}h^0(K_v,\operatorname{ad}\bar\rho)
-h^0(K,\operatorname{ad}\bar\rho).}
\tag{13.7}
$$

Here $\mathcal L_Q,T^0$ means that the tangent condition is made strict at the framed base places. Formula (13.7), not $|Q|$ and not (13.5), is the number of global variables in a presentation over that local base.

At each auxiliary prime placed inside the framed local base, the factor

$$
R_v^{\square,\mathrm{TW}}
\simeq\mathcal O[\Delta_v][[X_v,U_v,V_v]]
$$

already contains its three framed local coordinates. They must not be counted again as global relative variables.

The absolute dual Selmer vanishing does not automatically make every relative presentation relation-free. A presentation relative to a local base uses a dual Selmer condition relaxed at the framing places, which may be larger than the absolute strict-at-$Q$ group. Its relation bound must be computed with the exact relative condition.

### 13.3 The free pro-$\ell$ diamond variables

Let $m=|Q_N|$. After choosing a generator of each cyclic factor, there is a noncanonical isomorphism

$$
\Delta_{Q_N}\simeq
(\mathbf Z/\ell^N\mathbf Z)^m.
\tag{13.8}
$$

Introduce the completed group algebra

$$
\Lambda_m
=\mathcal O[[\mathbf Z_\ell^m]]
\simeq\mathcal O[[T_1,\ldots,T_m]],
\tag{13.9}
$$

where a standard topological generator in the $i$th factor maps to $1+T_i$. The chosen generators give a surjection

$$
\Lambda_m\longrightarrow\mathcal O[\Delta_{Q_N}]
\tag{13.10}
$$

with kernel

$$
\bigl((1+T_1)^{\ell^N}-1,\ldots,
(1+T_m)^{\ell^N}-1\bigr).
\tag{13.11}
$$

Thus a set of cardinality $m$ supplies exactly $m$ free pro-$\ell$ diamond variables before finite-level quotienting. In the standard unpadded construction $m=q$.

The choices of generators and the isomorphism (13.8) are not canonical. More importantly, the maps (13.10) for different $N$ do not arise from inclusions among the prime sets. They are separate identifications of abstract finite quotients with standard quotients of one free pro-$\ell$ group. Any theory comparing levels must record those identifications as data.

### 13.4 The complete finite-level ledger

For a level-$N$ set $Q_N$ of cardinality $m$, the data exported are:

$$
\Delta_{Q_N}\simeq(\mathbf Z/\ell^N\mathbf Z)^m,
$$

$$
R_{Q_N}^{\mathrm{TW},\mathrm{loc}}
\simeq\mathcal O[\Delta_{Q_N}][[X_v:v\in Q_N]],
$$

$$
R_{Q_N}^{\square,\mathrm{TW},\mathrm{loc}}
\simeq\mathcal O[\Delta_{Q_N}]
[[X_v,U_v,V_v:v\in Q_N]],
$$

$$
R_{\mathcal D_{Q_N}}
\widehat\otimes_{\mathcal O[\Delta_{Q_N}]}\mathcal O
\simeq R_{\mathcal D},
$$

and, for a killing set,

$$
H^1_{\mathcal L_{Q_N}^\perp}(K,M')=0.
$$

The global generator counts are (13.5) and (13.7), while the local framed coordinates are already contained in the displayed local ring. This ledger is sufficient for the next algebraic stage. No compatibility between different levels has been asserted beyond the standard abstract diamond quotients.

### 13.5 What dual-Selmer vanishing does and does not imply

Dual-Selmer vanishing has three immediate consequences in the present finite-level problem. It says that the combined localization map imposed by $Q$ detects every old dual Selmer class, turns the Wiles dimension identity into an exact formula for the primal tangent dimension, and removes the absolute dual term from the five-term comparison sequence. For an unpadded set with $|Q|=q$, source and target have the same dimension, so the localization tests are independent. For a padded set they are necessarily redundant: the combined localization remains injective, but its target has dimension $|Q|>q$. These are substantial conclusions, but they should not be strengthened without further hypotheses.

First, tangent dimension counts generators, not equations. If

$$
R_{\mathcal D_Q}\simeq
\mathcal O[[Z_1,\ldots,Z_g]]/J,
\tag{13.12}
$$

then $g$ is determined by the tangent space only when the presentation is minimal. Vanishing of the dual Selmer group does not by itself show $J=0$. Obstructions may live in a global $H^2$, in a constrained local obstruction theory, or in a relative condition not measured by the absolute Selmer structure used for prime selection.

Second, a presentation over a framed local base changes the cohomological problem. Strict tangent conditions at the framed places have relaxed Tate orthogonals. The relative dual Selmer group can therefore be nonzero even when

$$
H^1_{\mathcal L_Q^\perp}(K,M')=0.
$$

This is why (13.7) records the exact relative tangent, and why a relation bound over $R_{\mathrm{loc},S,Q}$ must use the corresponding relative obstruction group. Absolute vanishing cannot simply be inserted into a relative presentation formula.

Third, the finite group algebra is not a regular power-series base over $\mathcal O$. For one cyclic factor it has the equation

$$
(1+T)^{\ell^N}-1=0.
\tag{13.13}
$$

The equation belongs to the chosen finite-level diamond base; it is not a global deformation relation. Passing to $\Lambda_m$ separates these roles: $\Lambda_m$ is a regular pro-$\ell$ group algebra, while (13.11) imposes the exact finite level. Counts made relative to $\mathcal O[\Delta_Q]$ and counts made relative to $\Lambda_m$ differ by these $m$ level equations.

Finally, nothing in the prime-selection theorem produces an arithmetic module, proves that such a module is free over the diamond algebra, or compares the deformation ring with an algebra of operators. The output is the Galois-theoretic half of a later system: controlled local rings, augmentation, and vanishing dual Selmer. Keeping this boundary exact prevents freeness or faithfulness from entering the existence proof circularly.

The reliable implication chain is therefore

$$
\begin{array}{c}
\text{regular detecting primes}
\\ \Downarrow
\\
\text{injective dual localization}
\\ \Downarrow
\\
\text{dual Selmer }=0
\\ \Downarrow
\\
\text{exact tangent and generator counts},
\end{array}
\tag{13.14}
$$

with every statement about equations, complete intersections, or module freeness requiring an additional argument.

## 14. The theorem package

The preceding arguments used several hypotheses at different moments: representability for the global rings, image conditions for detection, disjointness for compatibility, and regular local structure for the diamond algebra. Collecting them prevents a conclusion proved under one layer from being used under another. The final theorem states the full finite-level package and then records only those variants whose numerical adjustments have been proved.

### 14.1 Precise hypotheses

We collect the assumptions in one place.

Let $K$ be a number field, let $\ell$ be odd, let $k$ be a finite field of characteristic $\ell$, and let $\mathcal O$ be the ring of integers of a finite extension of $\mathbf Q_\ell$ with residue field $k$. Let $S$ contain all archimedean places, all places above $\ell$, and every place where the residual representation, determinant, or chosen local condition is ramified.

Let

$$
\bar\rho:G_{K,S}\longrightarrow\operatorname{GL}_2(k)
$$

be absolutely irreducible, and fix a lift

$$
\delta:G_{K,S}\longrightarrow\mathcal O^\times
$$

of its determinant. Put

$$
M=\operatorname{ad}^0\bar\rho,
\qquad M'=M(1).
$$

Assume that the original global deformation problem $\mathcal D$ is representable with tangent structure $\mathcal L$, that its local conditions have the exact Tate orthogonals used above, and that its Selmer groups are finite-dimensional.

Put

$$
\Gamma=\bar\rho(G_{K(\zeta_\ell)}).
$$

Assume:

1. $\Gamma$ has no nontrivial $\ell$-power quotient;
2. $H^1(\Gamma,M)=0$;
3. every nonzero $\Gamma$-stable $\mathbf F_\ell$-subspace of the additive group of $M$ has no nonzero trivial quotient;
4. every such nonzero prime-field subspace is detected by a split regular semisimple element through (3.2).

Finally, require that every selected local residual eigenvalue lie in $k$. These are exactly the hypotheses used for cyclotomic compatibility, nontrivial restriction of classes, cohomology–cyclotomic disjointness, and regular semisimple detection.

### 14.2 Existence and local-structure theorem

**Theorem 14.1 (Taylor–Wiles data of every level).** Under the hypotheses of Section 14.1, set

$$
q=\dim_kH^1_{\mathcal L^\perp}(K,M').
$$

For every $N\ge1$ and every finite set $T$ of forbidden places, there is a set $Q_N$ disjoint from $S\cup T$ with $|Q_N|=q$ such that, for every $v\in Q_N$:

$$
q_v\equiv1\pmod{\ell^N},
$$

$\bar\rho(\varphi_v)$ has two distinct eigenvalues $\bar\alpha_v,\bar\beta_v\in k$, and one eigenvalue $\bar\alpha_v$ is chosen. With

$$
\Delta_v=k(v)^\times/(k(v)^\times)^{\ell^N},
\qquad
\Delta_{Q_N}=\prod_{v\in Q_N}\Delta_v,
$$

one has

$$
\Delta_{Q_N}\simeq(\mathbf Z/\ell^N\mathbf Z)^q.
\tag{14.1}
$$

The unframed and framed local rings are

$$
R_v^{\mathrm{ur},\delta,\alpha_v}
\simeq\mathcal O[[X_v]],
$$

$$
R_v^{\mathrm{TW},\delta,\alpha_v}
\simeq\mathcal O[\Delta_v][[X_v]],
$$

$$
R_v^{\square,\mathrm{ur},\delta,\alpha_v}
\simeq\mathcal O[[X_v,U_v,V_v]],
$$

and

$$
R_v^{\square,\mathrm{TW},\delta,\alpha_v}
\simeq\mathcal O[\Delta_v][[X_v,U_v,V_v]].
\tag{14.2}
$$

The Taylor–Wiles rings are formally smooth over $\mathcal O[\Delta_v]$ of relative dimensions one and three, respectively. Their augmentation quotients are the corresponding unramified rings. Their generic fibers split into smooth diamond-character components after a coefficient extension containing the relevant roots of unity; the integral union is not formally smooth over $\mathcal O$.

At every $v\in Q_N$,

$$
L_v^{\mathrm{ur}}
\subset L_v^{\mathrm{TW}}=H^1(K_v,M),
\qquad
\dim L_v^{\mathrm{TW}}/L_v^{\mathrm{ur}}=1,
$$

and

$$
(L_v^{\mathrm{TW}})^\perp=0.
\tag{14.3}
$$

For the enlarged global problem,

$$
H^1_{\mathcal L_{Q_N}^\perp}(K,M')=0,
\tag{14.4}
$$

and

$$
R_{\mathcal D_{Q_N}}
\widehat\otimes_{\mathcal O[\Delta_{Q_N}],\operatorname{aug}}
\mathcal O
\simeq R_{\mathcal D}.
\tag{14.5}
$$

The numerical defect and unframed tangent dimension satisfy

$$
\Delta(\mathcal D_{Q_N})=\Delta(\mathcal D)+q,
$$

and

$$
\dim H^1_{\mathcal L_{Q_N}}(K,M)
=\Delta(\mathcal D)+q
=\dim H^1_{\mathcal L}(K,M).
\tag{14.6}
$$

If the original problem is balanced, the common value in (14.6) is $q$. Partial framing generator counts are given by (13.7), with all local framed variables retained in the local base.

**Proof.** The restriction and disjointness lemmas of Chapter 4 reduce the cyclotomic, residual, and cocycle requirements to a compatible element in a finite Galois quotient. The regular semisimple image lemma of Chapter 5 constructs that element, and Theorem 6.5 realizes it at infinitely many primes. The induction of Chapter 11 selects exactly $q$ distinct primes and proves (14.4).

Chapters 7–9 construct the local functors, rings, group-algebra structures, tangent spaces, and augmentation maps. Global assembly gives (14.5). The local tangent quotient has dimension one at each prime, so the global numerical identity gives

$$
\Delta(\mathcal D_{Q_N})=\Delta(\mathcal D)+q.
$$

Together with dual Selmer vanishing, this gives the first equality in (14.6). The original numerical identity gives

$$
\dim H^1_{\mathcal L}(K,M)=\Delta(\mathcal D)+q,
$$

which is the second equality. Equivalently, the comparison sequence shows directly that the primal dimension is unchanged during the $q$ detecting steps. $\square$

### 14.3 Variants and their exact adjustments

If a fixed regular residual conjugacy class detects every nonzero stable subspace arising from dual classes, Theorem 14.1 may prescribe that class, and hence its eigenvalue pair, at every prime. If not, the residual classes must be allowed to vary within the detecting family.

If $r\ge q$, the set may be padded to cardinality $r$. Dual Selmer remains zero, while

$$
\Delta(\mathcal D_Q)=\Delta(\mathcal D)+r
$$

and the primal tangent dimension is $\Delta(\mathcal D)+r$. If another construction first forces a set $P$, recompute the dual dimension after imposing $P$ and add exactly that many detecting primes.

If determinant is variable, the tangent coefficient is the full adjoint and can contain a scalar constituent. Cyclotomic character deformations and scalar dual classes then require their own class-field-theoretic analysis. The fixed-determinant theorem cannot be reused by replacing $M$ with $\operatorname{ad}\bar\rho$ without checking the no-trivial-quotient and detector conditions. If $\ell=2$, use the trace-kernel determinant complex, its quotient dual, and modified real cohomology; Theorem 14.1 does not claim that case.

For different values of $N$, the theorem gives independent sets and permits them to be pairwise disjoint. It does not give nested sets. Chosen generators identify their diamond groups with standard quotients of $\mathbf Z_\ell^q$, supplying the $q$ free pro-$\ell$ variables of (13.9), but these identifications are additional finite-level data.

### 14.4 Conclusion

Auxiliary primes solve a precise global problem by a precise local exchange. A nonzero dual Selmer class first becomes an elementary abelian extension over the residual and cyclotomic fixed field. The split Taylor–Wiles image conditions force that extension to be nontrivial, separate it from higher cyclotomic layers, and supply a split regular semisimple element that detects a translation. Ordinary adequacy supplies the finite-image cohomology vanishing and semisimple detection, but the underlying-prime-field no-trivial-quotient clause used for cyclotomic disjointness is an additional hypothesis unless it has been verified in the particular image. The fiber-product lemma proves that the resulting residual, cyclotomic, and cohomological prescriptions are compatible. Only then does the finite Galois distribution theorem imported from Book 142 in Chapter 6 turn the compatible element into primes.

At each such prime, distinct residual eigenvalues select a unique local branch. The tame relation and the congruence $q_v\equiv1\pmod{\ell^N}$ produce one diamond character, while fixed determinant places its inverse on the complementary line. The universal local ring is a power-series ring over the finite group algebra. Its augmentation is the smooth unramified branch, its special-fiber tangent gains one direction, and its exact dual orthogonal loses one direction.

Poitou–Tate exactness makes the global effect one-for-one. Choosing a prime that detects a surviving class lowers the dual Selmer dimension by exactly one and does not enlarge the primal Selmer group. Repeating the step gives precisely $q$ primes, not an unspecified surplus and not a number guessed from the primal tangent. Padding, framings, determinant restrictions, real places, and characteristic two each have separately recorded numerical effects.

The final data are therefore fully finite and explicit: a set $Q_N$, a product diamond group, local power-series rings over its group algebra, an augmented global deformation ring recovering the original problem, vanishing dual Selmer, and exact generator counts. These are the controlled local variables and symmetries for which the global reciprocity obstructions were traded.

## 15. Paired relative Taylor–Wiles selection

### 15.1 Two sources and one residual Selmer problem

There is a useful situation in which the characteristic-zero local geometry is deliberately allowed to change while the residual deformation problem is held fixed. One global problem is the problem whose horizontal components one ultimately wants to study. A second problem replaces some old local sources by better behaved sources. The second problem is not a new residual deformation problem: it is another integral model of the same one.

Let $\mathcal D^{\mathrm{des}}$ and $\mathcal D^{\mathrm{av}}$ be fixed-determinant global deformation problems for the same absolutely irreducible representation $\bar\rho$, and let $T$ be the finite set of old places placed in the framed local base. At every old place $v$, write $\mathcal D_v^{\mathrm{all}}$ for the unrestricted residual local deformation functor. Suppose there is an isomorphism $\eta_v$ between the two residual local functors which commutes with their forgetful embeddings into $\mathcal D_v^{\mathrm{all}}$:

$$
\begin{array}{ccc}
\mathcal D_{v,k}^{\mathrm{des}}&\xrightarrow{\eta_v}&
\mathcal D_{v,k}^{\mathrm{av}}\\
\downarrow&&\downarrow\\
\mathcal D_{v,k}^{\mathrm{all}}&=&
\mathcal D_{v,k}^{\mathrm{all}}.
\end{array}
\tag{15.0}
$$

Here the vertical arrows are monomorphisms of functors. This embedded compatibility, rather than an abstract isomorphism of the two special fibers, implies that their tangent images inside

$$
H^1(K_v,M),
\qquad M=\operatorname{ad}^0\bar\rho,
$$

are literally the same subspace. The integral sources may nevertheless have different generic fibers, different numbers of components, and different reducedness properties. Without commutativity of (15.0), an abstract automorphism of a residual functor could carry one tangent condition to another subspace of unrestricted cohomology, and the global Selmer structures would not be canonically equal.

For a presentation relative to the old local base, the correct Selmer structure is strict at $T$. Write $\mathcal L_T^0$ for the structure whose primal condition is zero at $v\in T$ and is the common residual local condition away from $T$. Its Tate dual is relaxed at $T$ and is the exact orthogonal of the common condition elsewhere. Put

$$
V_T^0
=H^1_{(\mathcal L_T^0)^\perp}(K,M'),
\qquad
q_T^0=\dim_k V_T^0,
\qquad M'=M^*(1).
\tag{15.1}
$$

The superscript $0$ records strictness of the primal condition, not vanishing of the dual group. Indeed the dual condition at an old framed place is the whole local cohomology group. This is why killing the absolute dual Selmer group is not enough for a relative presentation.

For a prospective split regular prime $v\notin S\cup T$ and a chosen residual eigenline $\bar\alpha$, localization followed by the diagonal projector gives a linear functional

$$
\lambda_{v,\bar\alpha}:V_T^0\longrightarrow k.
\tag{15.2}
$$

It is the functional whose nonvanishing makes the one-prime comparison sequence lose one dual dimension. Both localization and the projector are residual constructions. They therefore do not see which of the two characteristic-zero local sources was chosen.

**Proposition 15.1 (canonical residual relative Selmer identification).** Assume the embedded residual identifications (15.0) at every conditioned place. Then the strict-at-$T$ residual Selmer structures for $\mathcal D^{\mathrm{des}}$ and $\mathcal D^{\mathrm{av}}$ are equal. Consequently there are canonical identifications

$$
V_T^{0,\mathrm{des}}
=V_T^0
=V_T^{0,\mathrm{av}},
\tag{15.3}
$$

and, under these identifications, the localization functionals $\lambda_{v,\bar\alpha}$ agree for every admissible pair $(v,\bar\alpha)$.

**Proof.** Both global cohomology groups in (15.3) are subspaces of the same $H^1(G_{K,S},M')$. At a place of $T$, strictness makes the primal condition zero for both problems, so local duality makes both dual conditions equal to $H^1(K_v,M')$. Away from $T$, differentiating the commuting square (15.0) shows that the two tangent functors have the same image in $H^1(K_v,M)$. Their exact Tate orthogonals are therefore the same subspace of $H^1(K_v,M')$. Thus the defining local restriction conditions are identical place by place. This proves (15.3) as equality of subspaces, not merely as an equality of dimensions or as an abstract isomorphism.

At a new prime, the local residual representation, chosen eigenline, restriction map, and diagonal projector are the same for the two problems. Formula (15.2) is consequently the same map on the common space. $\square$

The proposition is the conceptual heart of paired selection. A characteristic-zero component label is not part of a residual cohomology class. Once strictness at the old local base is imposed correctly, there is only one obstruction space to kill.

### 15.2 The paired relative selection theorem

Retain the split Taylor–Wiles image hypotheses of Section 14.1. Allow also a finite list of auxiliary prescriptions of the kind considered in Section 6.3: avoidance of finitely many places, splitting in specified finite extensions, a permitted residual regular class, and a permitted choice of residual eigenline. The finite avoidance list is enforced after Chebotarev; the remaining prescriptions are conditions in a finite Galois quotient.

Compatibility has two clauses. For every nonzero subspace $W\subseteq V_T^0$, and hence for every current surviving subspace in the killing induction, form the finite quotient containing the residual, $\ell^N$th cyclotomic, prescribed splitting, and cohomology extensions for $W$. The **full detector fiber**

$$
\mathscr C_{N,W}^{\mathrm{det}}
=\{\sigma:\sigma\text{ satisfies every Galois prescription and }
\lambda_\sigma|_W\ne0\}
\tag{15.3a}
$$

must be a nonempty conjugacy-stable subset. Here $\lambda_\sigma$ is the diagonal-projector functional determined by the residual regular class and its ordered eigenline. Separately, after all cocycle-extension conditions are omitted, the **padding fiber**

$$
\mathscr C_N^{\mathrm{pad}}
=\{\sigma:\sigma\text{ satisfies the residual, cyclotomic,
splitting, and eigenline prescriptions}\}
\tag{15.3b}
$$

must be nonempty. The first clause supplies a detecting prime at every killing step. The second supplies primes after the surviving cohomology space has become zero. Neither nonemptiness follows formally from the other.

**Theorem 15.2 (paired relative Taylor–Wiles prime selection).** Let $\mathcal D^{\mathrm{des}}$ and $\mathcal D^{\mathrm{av}}$ satisfy Proposition 15.1. For every $N\geq1$ and every integer $h\geq q_T^0$, there is a single ordered set

$$
Q_N=\{v_{N,1},\ldots,v_{N,h}\}
\tag{15.4}
$$

disjoint from the old controlling set and satisfying all the compatible auxiliary prescriptions such that:

1. $q_v\equiv1\pmod{\ell^N}$ for every $v\in Q_N$;
2. $\bar\rho(\varphi_v)$ is split regular and carries a chosen ordered eigenline at every $v\in Q_N$;
3. the same eigenlines and the same Taylor–Wiles local functors are used in both global problems;
4. the enlarged strict-at-$T$ relative dual Selmer groups vanish for both problems:

   $$
   H^1_{(\mathcal L^{0,\mathrm{des}}_{T,Q_N})^\perp}(K,M')
   =0
   =H^1_{(\mathcal L^{0,\mathrm{av}}_{T,Q_N})^\perp}(K,M').
   \tag{15.5}
   $$

The first $q_T^0$ primes may be chosen so that the matrix of their localization functionals on $V_T^0$ has full rank. Thus (15.5) kills the relative obstruction space itself, rather than only the absolute dual Selmer group.

**Proof.** If $q_T^0=0$, there is no detecting step. Suppose it is positive and let $W=V_T^0$ be the current surviving space. The cohomology-extension and disjointness arguments of Chapters 4 and 5 apply to $W$ exactly as they apply to an absolute dual Selmer space: relative Selmer conditions select a subspace of global cohomology but do not alter the extensions cut out by its classes. By the compatibility hypothesis, the full detector fiber $\mathscr C_{N,W}^{\mathrm{det}}$ is nonempty. The prime-selection theorem of Chapter 6 therefore supplies infinitely many primes satisfying every side prescription for which the resulting localization functional is nonzero on $W$.

Choose one such prime $v_{N,1}$. The comparison sequence for the strict-at-$T$ structure and the Taylor–Wiles local condition has one-dimensional localization target. Since $\lambda_{v_{N,1},\bar\alpha}|_W$ is nonzero, that map is surjective, and the new relative dual group is its kernel. Its dimension is therefore $q_T^0-1$. Replace $W$ by this kernel and repeat, using the separately assumed nonempty fiber $\mathscr C_{N,W}^{\mathrm{det}}$ for that current subspace and placing the previously selected primes in the avoidance set. After $q_T^0$ steps, the common relative dual group is zero and the localization matrix is triangular with nonzero diagonal after suitable choices of bases.

Proposition 15.1 identifies the obstruction spaces and every detecting functional throughout the induction. Indeed, after adding a common Taylor–Wiles condition, the new residual local structures remain identical. Hence each selected prime lowers both dimensions in the same step, and the vanishing obtained after the final detecting prime is precisely the double equality (15.5).

If $h>q_T^0$, choose the remaining primes successively from the non-cocycle padding fiber $\mathscr C_N^{\mathrm{pad}}$, including all earlier choices in the avoidance list. Chebotarev supplies infinitely many such primes. Enlarging the set only tightens the dual local conditions, so both zero groups remain zero. This produces the full ordered set (15.4) with every auxiliary prescription intact. $\square$

There is no union of two separately selected sets in this argument. Such a union would enlarge the diamond rank, obscure the numerical cancellation, and still require a comparison of the two local labelings. The common residual obstruction space removes all three problems at once.

### 15.3 Padding without reopening the obstruction space

The cardinality needed for later dimension matching can exceed $q_T^0$. Once the detecting subset has been chosen, select $h-q_T^0$ more primes from the separately nonempty padding fiber (15.3b). It imposes the same congruence, residual regularity, eigenline, and splitting requirements, but no condition in a cocycle extension. At each stage discard the fixed avoidance list and all earlier choices. Chebotarev leaves infinitely many primes, so the selections can be kept distinct and away from every previously named finite set.

Let $Q_N^{\mathrm{kill}}\subseteq Q_N$ be the first $q_T^0$ primes. Enlarging the auxiliary set makes the dual local conditions more restrictive. Therefore

$$
H^1_{(\mathcal L^0_{T,Q_N})^\perp}(K,M')
\subseteq
H^1_{(\mathcal L^0_{T,Q_N^{\mathrm{kill}}})^\perp}(K,M')
=0.
\tag{15.6}
$$

This proves that padding preserves relative vanishing. Every splitting, congruence, residual-class, and eigenline condition occurs in $\mathscr C_N^{\mathrm{pad}}$, while the finite avoidance list is enforced by discarding those finitely many primes from the resulting Chebotarev set. Thus padding preserves every side requirement; it is not an after-the-fact choice of arbitrary primes. A detector fiber cannot be invoked when the current space is zero, which is exactly why the separate padding hypothesis is present. The ordered labels identify

$$
\Delta_{Q_N}\simeq(\mathbf Z/\ell^N\mathbf Z)^h
\tag{15.7}
$$

for both problems. These common labels are part of the finite-level datum and will later determine common diamond coordinates.

An instructive boundary case is $V_T^0=0$ but $h>0$. Every prime is a padding prime. The theorem still imposes the complete local and avoidance package, while (15.6) shows that no obstruction can reappear. By contrast, vanishing of the absolute dual group with $V_T^0\ne0$ is not this boundary case: relaxed conditions at $T$ can leave relative classes which must still be detected.

### 15.4 The totally real variable count

The reason for prescribing $h$ rather than always taking the minimal cardinality is visible in the relative generator formula. Suppose now that $T$ is nonempty and that $F$ is totally real of degree

$$
d_F=[F:\mathbf Q],
$$

that $\bar\rho$ is an odd absolutely irreducible rank-two representation with fixed determinant, and that every old finite place with nonzero local defect has its full local factor absorbed into the base indexed by $T$. Let $g_{T,Q_N}$ and $q_{T,Q_N}$ denote the relative numbers of generators and dual relations after adding $Q_N$. With the sums taken over the controlling set, the exact fixed-determinant relative Euler characteristic is

$$
\begin{aligned}
g_{T,Q_N}-q_{T,Q_N}
={}&|T|-1-h^0(F,M')+h\\
&+\sum_{\substack{v\nmid\infty\\v\notin T\cup Q_N}}
\bigl(l_v-h_v^0(M)\bigr)
+\sum_{v\mid\infty}\bigl(l_v-h_v^0(M)\bigr).
\end{aligned}
\tag{15.8}
$$

Here $|T|-1$ is the scalar-frame correction: there is one scalar direction at each local frame and one global scalar quotient. Each Taylor–Wiles prime has $l_v-h_v^0(M)=1$, producing the displayed $+h$. Assume now that every remaining finite defect in the first sum is zero, that oddness gives $l_v-h_v^0(M)=-1$ at every real place, and that $h^0(F,M')=0$. The last sum is then $-d_F$, while all nonzero old finite contributions have already been absorbed into the local source. Thus (15.8) becomes

$$
g_{T,Q_N}-q_{T,Q_N}
=|T|-1-d_F+h.
$$

Theorem 15.2 makes $q_{T,Q_N}=0$ for both members of the pair. Consequently their common number of relative source variables is

$$
\boxed{
q_0=g_{T,Q_N}
=h+|T|-1-[F:\mathbf Q].
}
\tag{15.9}
$$

This identity is not obtained from the absolute balanced formula. It comes from the strict-at-$T$ relative structure, including its relaxed dual condition, the full scalar-frame correction, the real-place sum, and the global $H^0$ term. Formula (15.9) is available only after the stated zero-defect and no-self-twist hypotheses reduce (15.8) to the preceding equality. When a power-series presentation with $q_0$ variables is required, $h$ is padded further if necessary so that $q_0\geq0$. The inequality $h\geq q_T^0$ guarantees relative vanishing; the inequality $h\geq d_F+1-|T|$ guarantees a nonnegative displayed variable count. They serve different purposes.

### 15.5 What the paired theorem contributes

The two characteristic-zero local sources can now be carried through the same auxiliary levels without pretending that they are the same integral ring. What is shared is exactly what prime selection can see: the residual representation, the strict relative Selmer structure, the local detecting projectors, the primes, the ordered eigenlines, and the finite diamond groups. What remains different is exactly what the later component argument needs to compare: the characteristic-zero local sources.

The output is therefore stronger than two independent applications of Theorem 14.1. It gives one rank-$h$ diamond direction, one vanishing relative obstruction space, and one relative count $q_0$ for the pair. Those synchronized data make it possible to reduce the two finite-level module systems to the same residual shadow and then compare their patched supports without any forward reference to characteristic-zero components during prime selection.
