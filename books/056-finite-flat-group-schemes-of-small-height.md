# Finite-Flat Group Schemes of Small Height

## Contents

1. [The small-height problem](#1-the-small-height-problem)
   - [Integral torsion at the residue characteristic](#11-integral-torsion-at-the-residue-characteristic)
   - [Bases, conventions, and height](#12-bases-conventions-and-height)
   - [What must be classified](#13-what-must-be-classified)
   - [The architecture of the book](#14-the-architecture-of-the-book)
2. [Schematic closure as an exact operation](#2-schematic-closure-as-an-exact-operation)
   - [Closing a generic subgroup](#21-closing-a-generic-subgroup)
   - [Saturation and the closure theorem](#22-saturation-and-the-closure-theorem)
   - [Intersections, sums, and flat images](#23-intersections-sums-and-flat-images)
   - [From generic subobjects to exact sequences](#24-from-generic-subobjects-to-exact-sequences)
   - [The fixed-ambient-model principle](#25-the-fixed-ambient-model-principle)
   - [Dedekind bases and abelian ambient groups](#26-dedekind-bases-and-abelian-ambient-groups)
3. [Connected and étale directions](#3-connected-and-étale-directions)
   - [The field decomposition](#31-the-field-decomposition)
   - [Lifting components over a henselian base](#32-lifting-components-over-a-henselian-base)
   - [The connected--étale exact sequence](#33-the-connected--étale-exact-sequence)
   - [Functoriality, base change, and splitting](#34-functoriality-base-change-and-splitting)
4. [Multiplicative and local-local directions](#4-multiplicative-and-local-local-directions)
   - [Multiplicative type through Cartier duality](#41-multiplicative-type-through-cartier-duality)
   - [The maximal multiplicative subgroup](#42-the-maximal-multiplicative-subgroup)
   - [The three-step filtration](#43-the-three-step-filtration)
   - [Order $p$ over a perfect field](#44-order-p-over-a-perfect-field)
5. [The first structure of a group of order $p$](#5-the-first-structure-of-a-group-of-order-p)
   - [Why order $p$ implies an $\mathbf F_p$-action](#51-why-order-p-implies-an-mathbf-f_p-action)
   - [The generic character](#52-the-generic-character)
   - [Teichmuller weights](#53-teichmuller-weights)
   - [The line hidden in the augmentation algebra](#54-the-line-hidden-in-the-augmentation-algebra)
6. [The Oort--Tate normal form](#6-the-oort--tate-normal-form)
   - [The universal coefficient calculation](#61-the-universal-coefficient-calculation)
   - [Oort--Tate data](#62-oort--tate-data)
   - [Construction from the data](#63-construction-from-the-data)
   - [Classification and uniqueness](#64-classification-and-uniqueness)
   - [The explicit quadratic case](#65-the-explicit-quadratic-case)
   - [Automorphisms and reduction of the normal form](#66-automorphisms-and-reduction-of-the-normal-form)
7. [The DVR classification](#7-the-dvr-classification)
   - [Parameters over a local principal base](#71-parameters-over-a-local-principal-base)
   - [Isomorphisms and valuations](#72-isomorphisms-and-valuations)
   - [Special-fiber type](#73-special-fiber-type)
   - [Cartier duality in parameters](#74-cartier-duality-in-parameters)
   - [Cotangent length](#75-cotangent-length)
   - [Morphisms and the order of models](#76-morphisms-and-the-order-of-models)
   - [The unramified dichotomy](#77-the-unramified-dichotomy)
8. [Generic characters and inertia](#8-generic-characters-and-inertia)
   - [Recovering the character from the parameter](#81-recovering-the-character-from-the-parameter)
   - [The tame inertia exponent](#82-the-tame-inertia-exponent)
   - [Dual characters](#83-dual-characters)
   - [Twists and descent](#84-twists-and-descent)
   - [Rigidity below the ramification boundary](#85-rigidity-below-the-ramification-boundary)
9. [Exact calculus in small height](#9-exact-calculus-in-small-height)
   - [Closing a line in a finite-flat representation](#91-closing-a-line-in-a-finite-flat-representation)
   - [Prime-order filtrations](#92-prime-order-filtrations)
   - [Extensions and the limits of classification](#93-extensions-and-the-limits-of-classification)
   - [Dual filtrations and annihilators](#94-dual-filtrations-and-annihilators)
   - [A self-dual height-two line](#95-a-self-dual-height-two-line)
10. [Change of base](#10-change-of-base)
    - [Flat extensions of valuation rings](#101-flat-extensions-of-valuation-rings)
    - [Unramified and ramified scalar extension](#102-unramified-and-ramified-scalar-extension)
    - [Completion and henselization](#103-completion-and-henselization)
    - [Descent data rather than generic descent](#104-descent-data-rather-than-generic-descent)
    - [An explicit unramified descent criterion](#105-an-explicit-unramified-descent-criterion)
11. [Arithmetic examples](#11-arithmetic-examples)
    - [The constant and multiplicative endpoints](#111-the-constant-and-multiplicative-endpoints)
    - [An intermediate ramified model](#112-an-intermediate-ramified-model)
    - [The dyadic family](#113-the-dyadic-family)
    - [Torsion on elliptic schemes](#114-torsion-on-elliptic-schemes)
    - [Equal characteristic as a boundary](#115-equal-characteristic-as-a-boundary)
12. [The small-height package](#12-the-small-height-package)
    - [A theorem ledger](#121-a-theorem-ledger)
    - [A failure atlas](#122-a-failure-atlas)
    - [Conclusion](#123-conclusion)

## 1. The small-height problem

### 1.1 Integral torsion at the residue characteristic

Finite group schemes of order prime to the residue characteristic are comparatively rigid. Their order is invertible, their cotangent spaces vanish, and finite flatness forces them to be étale. At the residue characteristic $p$, every part of that argument breaks in a controlled way. Generic points may collide, the special fiber may acquire nilpotents, and two integral models of the same generic group may have different connectedness behavior.

The standard pair already contains the central difficulty. Let $R$ be a mixed-characteristic discrete valuation ring with residue characteristic $p$. Both

$$
\underline{\mathbf Z/p\mathbf Z}_R
\quad\text{and}\quad
\mu_{p,R}
$$

are finite locally free of rank $p$. The first has étale special fiber. The second has special fiber

$$
\operatorname{Spec}k[U]/(U^p),
\qquad U=T-1,
$$

and is connected. Their generic fibers are both étale; after a suitable extension of the fraction field they even become isomorphic. Thus neither generic rank nor geometric generic points determine the integral object.

This book studies the first range in which that ambiguity can be classified. The phrase **small height** refers first to groups of order $p$, and then to finite $p$-groups assembled from order-$p$ subquotients. Rank $p$ is the atomic case: it has just enough room for étale, multiplicative, and additive-looking degeneration, while still admitting a complete coordinate classification. That classification is the Oort--Tate theorem.

The purpose is not only to list normal forms. Arithmetic applications begin with a generic Galois-stable subgroup, close it in an integral torsion group, take quotients, dualize, and read inertia from the resulting model. Every arrow in that procedure needs a flatness or exactness theorem. We therefore develop the closure calculus and the connected--étale and multiplicative filtrations before introducing coordinates.

### 1.2 Bases, conventions, and height

The principal arithmetic base will be

$$
S=\operatorname{Spec}R,
$$

where $R$ is a henselian or complete discrete valuation ring, $K$ is its fraction field, $\pi$ is a uniformizer, and $k$ is its residue field. In the classification chapters we assume mixed characteristic $(0,p)$ and usually that $k$ is perfect. Rings of integers of finite extensions of $\mathbf Q_p$, their henselizations, and their completions satisfy these hypotheses; number-theoretic applications generally have finite $k$.

We normalize the valuation by $v(\pi)=1$ and put

$$
e=v(p).
$$

Thus $e$ is the absolute ramification index. No unramified hypothesis is implicit. The distinction between $e=1$ and $e>1$ will account for the appearance of intermediate order-$p$ models.

A finite flat commutative group scheme means a commutative group scheme finite locally free over its base. Its **order** is its locally constant rank. If the order is $p^h$, we call $h$ its **height**. This is a numerical use of height at finite level; it should not be confused with the height of a formal group. Height one means order $p$.

For a group $G/R$, write

$$
G_K=G\times_RK,
\qquad
G_k=G\times_Rk,
$$

and write $G^D$ for its Cartier dual. Exactness always means exactness as faithfully flat sheaves: in

$$
0\longrightarrow H\longrightarrow G\longrightarrow Q\longrightarrow0,
$$

$H$ is the scheme-theoretic kernel and $G\to Q$ is faithfully flat. Surjectivity on $R$-points is neither required nor expected.

### 1.3 What must be classified

Three questions should be kept separate.

First, given a closed subgroup $H_K\subset G_K$ of the generic fiber of a fixed finite-flat group, does it extend? Over a DVR, schematic closure gives a unique finite-flat subgroup inside that fixed ambient model.

Second, given an abstract generic group $H_K$, how many finite-flat models does it have? Closure does not answer this because there is no fixed ambient lattice. Oort--Tate data classify the rank-$p$ possibilities.

Third, given separately chosen models of two generic groups, which generic extensions admit an integral middle term? Rank-$p$ classification describes the possible endpoints but does not classify arbitrary extensions between them. This distinction is already visible in a connected--étale sequence, which need not split.

The central invariant of an order-$p$ model will be a pair of complementary parameters. Over a DVR their valuations add to $e$. One endpoint gives an étale special fiber, the other a multiplicative special fiber, and a strictly intermediate valuation gives a local-local special fiber. Cartier duality exchanges the two parameters. The generic character remembers the first parameter modulo $(p-1)$st powers.

### 1.4 The architecture of the book

Chapters 2--4 establish the coordinate-free structure. Schematic closure converts generic subgroups into finite-flat integral subgroups. Henselianity and perfection produce the connected--étale sequence. Cartier duality turns the maximal étale quotient of the dual into the maximal multiplicative subgroup, leaving a local-local middle layer.

Chapters 5--7 prove the Oort--Tate classification. The scalar action of $\mathbf F_p$ decomposes the augmentation algebra into Teichmuller weights. A universal coefficient calculation shows that one invertible module and two complementary sections encode the entire Hopf algebra. Over a DVR the line bundle is trivial, so the theorem becomes an explicit pair $(a,b)$ with product a fixed unit multiple of $p$.

Chapters 8--10 translate this classification into inertia characters, exact subquotient operations, base change, and descent. Chapter 11 tests every part of the dictionary on arithmetic examples. The final chapter records the package with all hypotheses visible.

## 2. Schematic closure as an exact operation

### 2.1 Closing a generic subgroup

Arithmetic torsion is often easiest to see over $K$. If a generic finite group is étale, its geometric points form a finite Galois module, and a stable subgroup of that module defines a closed subgroup scheme of the generic fiber. The integral problem is to retain that subgroup through specialization without inventing vertical torsion.

Let $G=\operatorname{Spec}A$ be finite flat over the DVR $R$, and let

$$
H_K\hookrightarrow G_K
$$

have Hopf ideal $I_K\subset A_K=A\otimes_RK$. Define

$$
I=A\cap I_K\subset A_K,
\qquad
H=\operatorname{Spec}(A/I).
\tag{2.1}
$$

This is the schematic closure of $H_K$ in $G$. The contraction, rather than an arbitrary set of cleared-denominator equations, is decisive. It removes every equation supported only at the closed point and makes the quotient saturated.

### 2.2 Saturation and the closure theorem

An $R$-submodule $I\subset A$ is **saturated** when $A/I$ is torsion-free, equivalently when

$$
\pi x\in I\quad\Longrightarrow\quad x\in I.
$$

Contraction from $A_K$ is saturated, and a saturated submodule is recovered from its generic extension. These elementary facts give the closure theorem.

**Theorem 2.1 (finite-flat closure).** Let $R$ be a DVR, let $G/R$ be finite flat, and let $H_K\subset G_K$ be a closed subgroup. The closure $H$ defined by (2.1) is a finite-flat closed subgroup of $G$. It is the unique finite-flat closed subgroup of $G$ with generic fiber $H_K$. Formation of $H$ commutes with flat extensions of DVRs.

**Proof strategy.** The quotient by the contracted ideal embeds into its generic fiber, so it is torsion-free. Over a DVR finite torsion-free modules are free. That freeness is then used a second time to descend the Hopf identities from the generic fiber.

**Proof.** The map

$$
A/I\longrightarrow A_K/I_K
$$

is injective by definition of contraction. Hence $A/I$ is torsion-free over $R$. It is finite because it is a quotient of the finite $R$-module $A$, so it is finite free.

We must show that $I$ is a Hopf ideal. Since $A/I$ is free, the sequence

$$
0\longrightarrow I\longrightarrow A\longrightarrow A/I\longrightarrow0
$$

splits as a sequence of $R$-modules. Therefore the kernel of

$$
A\otimes_RA\longrightarrow(A/I)\otimes_R(A/I)
$$

is $I\otimes A+A\otimes I$. For $x\in I$, the image of $\Delta(x)$ in the target vanishes after tensoring with $K$, because $I_K$ is a Hopf ideal. The target is torsion-free, so the image already vanishes over $R$. The counit and antipode conditions follow in the same way. Thus $H$ is a finite-flat subgroup.

If $H'\subset G$ is another finite-flat subgroup with the same generic fiber, its defining ideal is saturated and has generic extension $I_K$. Hence it is $A\cap I_K=I$. This proves uniqueness. Flat scalar extension preserves the saturated exact sequence and its generic fiber, so uniqueness identifies the base change with the new closure. $\square$

The theorem depends on the ambient group. It says that a generic subgroup has one closure *inside $G$*. It does not say that an abstract generic group has one finite-flat model.

### 2.3 Intersections, sums, and flat images

Raw scheme-theoretic operations can introduce torsion. Let $H_{1,K},H_{2,K}\subset G_K$ and let $H_1,H_2$ be their closures. The scheme-theoretic intersection $H_1\cap H_2$ is finite, but its coordinate algebra need not be flat. The correct integral intersection is

$$
\overline{H_{1,K}\cap H_{2,K}}^{\,G},
$$

obtained by saturating the sum of the two Hopf ideals.

Similarly, addition gives a generic subgroup $H_{1,K}+H_{2,K}\subset G_K$. Its closure is the **flat sum** of $H_1$ and $H_2$. The map

$$
H_1\times H_2\longrightarrow
\overline{H_{1,K}+H_{2,K}}^{\,G}
$$

need not be faithfully flat merely because its generic fiber is. When it is faithfully flat and its kernel is the flat intersection, one obtains the expected exact sequence. Without those extra facts, only the closed flat image object and its rank are automatic.

On generic fibers, ordinary finite-group-scheme rank gives

$$
|H_{1,K}+H_{2,K}|\,|H_{1,K}\cap H_{2,K}|
=|H_{1,K}|\,|H_{2,K}|.
$$

Closure preserves generic rank, so the same numerical identity holds for the flat sum and flat intersection. This rank identity does not by itself prove integral exactness; a torsor statement is stronger than an equality of ranks.

### 2.4 From generic subobjects to exact sequences

The most reliable exact construction begins with one integral middle term. Suppose

$$
H'_K\subset H_K\subset G_K.
$$

Let $H'$ and $H$ be their closures in $G$. Inclusion of generic groups reverses to inclusion of contracted Hopf ideals in the correct direction, so $H'\subset H$. Since both are finite flat, the represented quotient exists and gives

$$
0\longrightarrow H'\longrightarrow H
\longrightarrow H/H'\longrightarrow0.
\tag{2.2}
$$

Its generic fiber is the quotient sequence for $H'_K\subset H_K$. In particular $H/H'$ is a finite-flat model of $H_K/H'_K$ and

$$
|H|=|H'|\,|H/H'|.
$$

This proves a useful inheritance theorem.

**Corollary 2.2.** Let $G/R$ be finite flat and let $M=G_K(K^s)$ when the generic fiber is étale. Every Galois-stable subgroup $M'\subset M$ has a unique closure in $G$, and the quotient of $G$ by that closure models $M/M'$.

The word “unique” again refers to subgroups of the chosen $G$. Separately chosen models of $M'$ and $M/M'$ need not be the closure and quotient produced from $G$.

### 2.5 The fixed-ambient-model principle

Three false inferences are now easy to separate.

A generic morphism between two fixed models need not extend: its graph closure may fail to project isomorphically to the source. A generic isomorphism need not extend for the same reason. And two models with isomorphic generic fibers need not be isomorphic.

What does extend canonically is a generic **closed subgroup of a fixed finite-flat ambient group**. The fixed ambient Hopf lattice provides the integral bounds, and saturation chooses the largest ideal with the prescribed generic equations. This principle is exactly what arithmetic applications use when a Galois-stable line lies inside the generic fiber of an already constructed torsion group.

### 2.6 Dedekind bases and abelian ambient groups

The closure proof is local in codimension one. Let $R$ be a Dedekind domain with fraction field $K$, let $G/R$ be finite flat, and let $H_K\subset G_K$. Contracting the generic Hopf ideal again produces a finite torsion-free quotient. Over a Dedekind domain, finite torsion-free modules are projective, so the closure is finite locally free. Localization at every nonzero prime gives the DVR construction, and the local Hopf ideals glue because they are contractions of the same generic ideal.

**Proposition 2.3 (Dedekind closure).** Schematic closure of a generic subgroup in a finite-flat group over a Dedekind domain is finite flat, unique inside the ambient group, and compatible with flat base change for which the generic open remains dense.

**Proof.** Finiteness and the Hopf-ideal property are checked exactly as in Theorem 2.1. The coordinate quotient embeds in its generic fiber, hence is finite torsion-free and therefore projective. Localizing at each prime identifies it with the unique DVR closure. These local identifications prove uniqueness and glue the group operations. Flat base change preserves the contracted kernel and projectivity. $\square$

There is an important proper ambient application. Let $A/R$ be an abelian scheme and let $H_K\subset A_K[n]$ be a generic finite subgroup. Multiplication by $n$ on $A$ is finite flat, so $A[n]$ is a finite-flat ambient group. Closing $H_K$ inside $A[n]$ gives a finite-flat subgroup $H\subset A$. The quotient abelian scheme $A/H$ exists, and

$$
A\longrightarrow A/H
$$

is an isogeny with kernel $H$. Its generic fiber is the quotient isogeny by $H_K$. Thus a generic isogeny kernel extends whenever it is first placed inside the integral torsion of an abelian scheme.

The finite ambient group is essential in that argument. Taking topological closure directly in the proper scheme $A$ does not prove flatness of the kernel. Factoring through $A[n]$ reduces the problem to saturated finite algebra, where the DVR or Dedekind theorem applies.

## 3. Connected and étale directions

### 3.1 The field decomposition

Closure controls passage from generic to integral subgroups. Connectedness begins at the special fiber. Let $G$ be a finite commutative group scheme over a field $k$. Its coordinate algebra is Artinian and therefore a finite product of local Artinian algebras. The component containing the identity is an open-and-closed subgroup $G^0$.

Assume $k$ is perfect. Then the quotient by the identity component is finite étale, giving

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0.
\tag{3.1}
$$

The quotient is maximal among finite étale quotients. Indeed a map from a connected scheme to a finite étale scheme lands in one open-and-closed point after geometric base change; if it preserves the identity, that point is the identity. Hence every map $G\to E$ with $E$ finite étale kills $G^0$ and factors uniquely through $G^{\mathrm{et}}$.

Perfection is used to turn reduced finite algebras into geometrically reduced, hence étale, algebras. Over an imperfect field a reduced purely inseparable algebra can become nonreduced after scalar extension, so ordinary reducedness is not an adequate substitute.

### 3.2 Lifting components over a henselian base

Let now $(R,\mathfrak m,k)$ be henselian local and let $G/R$ be finite flat. Idempotents of a finite $R$-algebra correspond bijectively to idempotents of its special fiber. Consequently every open-and-closed component of $G_k$ lifts uniquely to an open-and-closed subscheme of $G$.

Assume $k$ is perfect. Define $G^0\subset G$ to be the lift of $(G_k)^0$. Multiplication and inversion preserve it. To see this without a point-counting argument, reduce the structural maps modulo $\mathfrak m$. Their images lie in the identity component there. Uniqueness of the lifted idempotent factor then forces the maps to factor through $G^0$ over $R$.

The notation is special-fiber notation. In mixed characteristic, $(\mu_p)^0=\mu_p$ by this definition even though the generic fiber of $\mu_p$ is étale and becomes disconnected over an algebraic closure.

### 3.3 The connected--étale exact sequence

**Theorem 3.1 (henselian connected--étale sequence).** Let $R$ be henselian local with perfect residue field, and let $G/R$ be finite flat and commutative. There is a functorial exact sequence

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0,
\tag{3.2}
$$

where $G^0$ has connected special fiber and $G^{\mathrm{et}}$ is finite étale. The quotient is maximal among finite étale quotients of $G$.

**Proof strategy.** Lift the identity component, form its finite-flat quotient, and prove that quotient étale by killing its differentials modulo the maximal ideal.

**Proof.** The lifted component $G^0$ is open and closed in a finite-flat scheme, hence finite flat. Its quotient exists and is finite flat. Reduction of the quotient sequence gives (3.1), so the special fiber of $G/G^0$ is étale. The finite module of relative differentials

$$
\Omega_{(G/G^0)/R}
$$

has zero reduction. Nakayama's lemma makes it zero. A finite locally free unramified morphism is finite étale, proving the asserted type of the quotient.

If $G\to E$ has $E$ finite étale, its restriction to $G^0$ is trivial on the special fiber. The inverse image of the identity section is open and closed in $G^0$ and contains its entire connected special fiber. Its complement is finite over the local base with empty special fiber, hence empty by Nakayama. Thus the restriction is trivial and the map factors through $G/G^0$. Uniqueness follows from faithful flatness of the quotient. $\square$

Ranks multiply:

$$
|G|=|G^0|\,|G^{\mathrm{et}}|.
\tag{3.3}
$$

This is a length formula, not a count of special-fiber points.

### 3.4 Functoriality, base change, and splitting

A homomorphism $f:G\to H$ sends $G^0$ into $H^0$, because it does so on special fibers and lifted components are unique. It therefore induces $f^{\mathrm{et}}:G^{\mathrm{et}}\to H^{\mathrm{et}}$. This proves functoriality of (3.2).

Flat extension between henselian valuation rings with perfect residue fields preserves the sequence when geometric connected components of the special fiber are preserved; this includes extensions of perfect residue fields. Completion is faithfully flat and has the same residue field, so the sequence over a henselization pulls back to the sequence over its completion.

The sequence need not split. A splitting would lift every point of the étale quotient to a compatible subgroup, which is extra extension data. Even if each geometric special fiber is isomorphic to a product, there need not be a global product decomposition. We will therefore use the word **decomposition** for the canonical separation into layers, not for a claimed direct product.

## 4. Multiplicative and local-local directions

### 4.1 Multiplicative type through Cartier duality

Connected--étale structure sees the discrete quotient but not the difference between multiplicative and additive infinitesimal groups. Cartier duality supplies the missing direction.

A finite flat commutative group $M/S$ is of **multiplicative type** if it becomes diagonalizable after a faithfully flat base change. Cartier duality gives the equivalences

$$
M\text{ is of multiplicative type}
\quad\Longleftrightarrow\quad
M^D\text{ is finite étale},
\tag{4.1}
$$

and

$$
E\text{ is finite étale}
\quad\Longleftrightarrow\quad
E^D\text{ is of multiplicative type}.
\tag{4.2}
$$

These statements require no perfection assumption. They follow after a faithfully flat cover from the explicit duality between a constant group $\underline M$ and the diagonalizable group $D(M)$, and then descend.

### 4.2 The maximal multiplicative subgroup

Assume again that $R$ is henselian local with perfect residue field. Apply the connected--étale sequence to $G^D$ and dualize its étale quotient. Define

$$
G^{\mathrm{mult}}
=\bigl((G^D)^{\mathrm{et}}\bigr)^D.
\tag{4.3}
$$

Exactness of Cartier duality embeds this group into $G$. It is of multiplicative type by (4.2).

**Proposition 4.1.** The subgroup $G^{\mathrm{mult}}$ is the maximal finite-flat subgroup of multiplicative type in $G$.

**Proof.** Let $M\subset G$ be of multiplicative type. Dualizing the quotient sequence $0\to M\to G\to G/M\to0$ gives a faithfully flat map

$$
G^D\longrightarrow M^D.
$$

The target is finite étale, so maximality of $(G^D)^{\mathrm{et}}$ forces this map to factor through that quotient. Dualizing the factorization gives $M\subset ((G^D)^{\mathrm{et}})^D$. Thus every multiplicative subgroup lies in (4.3), and (4.3) itself has the desired type. $\square$

This construction is canonical and functorial. It does not amount to finding all multiplicative-looking geometric points; in characteristic $p$, $\mu_p$ has only the identity geometric point.

### 4.3 The three-step filtration

Suppose $G$ is a finite flat $p$-group over $R$. A nontrivial finite multiplicative-type $p$-group over the perfect residue field has connected special fiber: after a separable extension it is a product of groups $\mu_{p^n}$, each supported at the identity. Hence

$$
G^{\mathrm{mult}}\subset G^0\subset G.
\tag{4.4}
$$

The three subquotients have distinct roles:

$$
\begin{array}{c|c}
\text{subquotient}&\text{type}\
\hline
G^{\mathrm{mult}}&\text{multiplicative type}\
G^0/G^{\mathrm{mult}}&\text{local-local}\
G/G^0&\text{finite étale}.
\end{array}
\tag{4.5}
$$

Here **local-local** means that the special fiber of the group and that of its Cartier dual are connected.

To prove the middle assertion, connectedness of $G^0/G^{\mathrm{mult}}$ follows because it is a quotient of a group with connected special fiber. Dualize its defining exact sequence. A nontrivial étale quotient of its dual would dualize to a multiplicative subgroup of $G^0$ strictly larger than $G^{\mathrm{mult}}$, contradicting maximality. Thus its dual also has connected special fiber.

Duality reverses (4.4). The étale quotient of $G$ corresponds to the multiplicative subgroup of $G^D$; the multiplicative subgroup of $G$ corresponds to the étale quotient of $G^D$; and the local-local middle term stays in the local-local class. In general (4.4) is a filtration, not a direct product.

### 4.4 Order $p$ over a perfect field

Over an algebraically closed field $k$ of characteristic $p$, the three basic commutative group schemes of order $p$ are

$$
\underline{\mathbf Z/p\mathbf Z},
\qquad \mu_p,
\qquad \alpha_p.
\tag{4.6}
$$

They are respectively étale, multiplicative connected, and local-local. We now justify that this list is complete.

**Theorem 4.2.** Let $k$ be algebraically closed of characteristic $p$, and let $G/k$ be commutative of order $p$. Then $G$ is isomorphic to exactly one group in (4.6).

**Proof strategy.** The connected--étale and multiplicative filtrations leave only the local-local case. There we use the elementary fact that a connected cocommutative Hopf algebra of prime dimension whose dual is also local contains a nonzero primitive element. That element already generates the whole algebra.

**Proof.** If $G$ is not connected, its identity component has rank dividing the prime $p$, hence rank $1$. Therefore $G$ is finite étale and, over algebraically closed $k$, constant. This gives $\underline{\mathbf Z/p\mathbf Z}$.

Assume $G$ connected. If $G^D$ is not connected, the preceding case makes $G^D$ constant, so $G$ is its diagonalizable dual and hence $G\simeq\mu_p$.

It remains to suppose that both $G$ and $G^D$ are connected. Relative Frobenius on either group is zero. Indeed its scheme-theoretic image has rank $1$ or $p$. In the second case Frobenius is an isomorphism, because it is a faithfully flat map between groups of the same finite rank; but a finite group on which relative Frobenius is an isomorphism is étale, contradicting connectedness. Thus both Frobenius maps have trivial image.

Put $A=\mathcal O(G)$. Connectedness of $G^D=\operatorname{Spec}(A^\vee)$ says that the convolution algebra $A^\vee$ is local. Equivalently, the coradical of the coalgebra $A$ is the one-dimensional space $k\cdot1$. In any nontrivial finite-dimensional coalgebra with one-dimensional coradical, the first nonzero step after the coradical contains an element $x$ with

$$
\Delta(x)=x\otimes1+1\otimes x;
$$

subtracting its counit makes it primitive. This follows directly from the definition of the coradical filtration: the first new class has reduced coproduct in earlier steps, and there are no earlier steps beyond $k\cdot1$.

Frobenius being zero gives $x^p=0$. Let $n$ be the least positive integer with $x^n=0$. If $n<p$, then

$$
0=\Delta(x^n)=\sum_{i=0}^n\binom ni x^i\otimes x^{n-i}.
$$

Every intermediate binomial coefficient is nonzero in $k$, and minimality makes the tensors $x^i\otimes x^{n-i}$ nonzero and linearly independent by total bidegree. This is impossible. Hence $n=p$, so the Hopf subalgebra generated by $x$ is $k[x]/(x^p)$ and already has dimension $p$. It equals $A$, with primitive coproduct. Therefore $G\simeq\alpha_p$.

Finally, the three groups are pairwise nonisomorphic: one is étale, one is connected with étale dual, and one is connected with connected dual. $\square$

The primitive-element Hopf argument in the last paragraph is the characteristic-$p$ shadow of the universal calculation carried out in Chapter 6. Over a nonalgebraically closed perfect field, the three types can have forms; type, rather than a chosen split coordinate, is the invariant statement.

## 5. The first structure of a group of order $p$

### 5.1 Why order $p$ implies an $\mathbf F_p$-action

Before choosing a coordinate, one needs a canonical symmetry that will control it. A finite flat commutative group of order $p$ is killed by $p$.

**Proposition 5.1.** Let $G/S$ be finite flat commutative of constant order $p$. Then $[p]_G=0$.

**Proof.** The assertion may be checked after an affine faithfully flat cover, so write $G=\operatorname{Spec}A$. Finite-flat summation associates to every morphism $u:G_T\to G_T$ the sum of its values, with scheme-theoretic multiplicity. Let $a\in G(T)$ and let $\tau_a$ be translation by $a$. Functoriality under automorphisms gives

$$
\sum_{x\in G_T}u(\tau_a x)=\sum_{x\in G_T}u(x).
$$

Taking $u$ to be the identity, additivity of the sum gives

$$
\sum_{x\in G_T}(x+a)=\sum_{x\in G_T}x+pa.
$$

Comparison yields $pa=0$. This is natural in every $T$, so $[p]_G=0$. The summation uses the trace of the finite locally free algebra and therefore counts nilpotent length; no assumption about geometric points enters. $\square$

Consequently every $c\in\mathbf F_p$ acts on $G$ by $[c]$. The units $\mathbf F_p^\times$ act by automorphisms. This scalar action is intrinsic; it does not require a choice of generator of the generic group.

### 5.2 The generic character

Let $R$ now be a mixed-characteristic DVR with fraction field $K$. Because $p$ is invertible in $K$, every order-$p$ group scheme over $K$ is finite étale. Its geometric points form a one-dimensional $\mathbf F_p$-vector space. Thus an order-$p$ finite-flat group $G/R$ determines a character

$$
\chi_G:\Gamma_K\longrightarrow\mathbf F_p^\times,
\tag{5.1}
$$

well defined independently of a basis up to the harmless conjugacy of a one-dimensional representation. Since the target is abelian, even that conjugacy disappears.

This character does not classify the integral model. If $K$ contains $\mu_p$, the generic fibers of the constant group and $\mu_p$ are both trivial $\mathbf F_p$-modules, while their special fibers have opposite types. The missing datum is the position of the integral Hopf lattice inside the generic coordinate algebra.

Cartier duality changes the generic character by the cyclotomic twist. If $\overline\chi_p$ is the mod-$p$ cyclotomic character, then

$$
\chi_{G^D}=\overline\chi_p\chi_G^{-1}.
\tag{5.2}
$$

Indeed $G^D(K^s)=\operatorname{Hom}_{\mathbf F_p}(G(K^s),\mu_p(K^s))$, and Galois acts contragrediently on the source and naturally on the target.

### 5.3 Teichmuller weights

Assume $R$ is henselian with residue characteristic $p$. Each element of $\mathbf F_p^\times\subset k^\times$ has a unique Teichmuller lift, giving a character

$$
\omega:\mathbf F_p^\times\longrightarrow R^\times
$$

with $\omega(c)\equiv c\pmod{\mathfrak m}$. Since $p-1$ is a unit in $R$, the group algebra of $\mathbf F_p^\times$ splits by the idempotents

$$
e_i=\frac1{p-1}\sum_{c\in\mathbf F_p^\times}
\omega(c)^{-i}[c],
\qquad i\in\mathbf Z/(p-1)\mathbf Z.
\tag{5.3}
$$

Let $A=\mathcal O(G)$ and $I=\ker(\varepsilon:A\to R)$. Pullback by scalar multiplication makes $I$ a module for $\mathbf F_p^\times$. Hence

$$
I=\bigoplus_{i\in\mathbf Z/(p-1)}I_i,
\qquad I_i=e_iI.
\tag{5.4}
$$

Multiplication respects weights, and the coproduct of a weight-$i$ element has total weight $i$. These two elementary restrictions are what make a one-coordinate normal form possible.

For $p=2$, the group $\mathbf F_2^\times$ is trivial and (5.3) supplies no decomposition. The order-two Hopf identities are short enough to solve directly; §6.5 does so. Until then, the weight discussion assumes $p$ odd.

### 5.4 The line hidden in the augmentation algebra

The decisive integral fact is that a rank-$p$ Hopf algebra contains one invertible weight-one module and no higher independent choices.

**Lemma 5.2 (weight-line lemma).** Let $p$ be odd, let $R$ be a mixed-characteristic DVR, and let $G/R$ be finite flat of order $p$. With notation (5.4), every nonzero weight occurs with rank one, and the Hopf algebra is locally generated by a weight-one line. More precisely, there is an invertible $R$-module $L$ and, locally after choosing a frame $x$ of $L$, an algebra presentation

$$
A\simeq R[x]/(x^p-a x)
\tag{5.5}
$$

for some $a\in R$. If the frame is changed to $x'=ux$, then

$$
a'=u^{p-1}a.
\tag{5.6}
$$

**Proof strategy.** Work first on the generic fiber, where the group is étale and becomes constant after a separable extension. There the coordinate algebra is the regular representation of the scalar group on a one-dimensional $\mathbf F_p$-space, so each Teichmuller weight occurs once. Saturation brings those multiplicities back to the DVR. The product and coproduct equations then remove all but one generator.

**Proof.** After a finite separable extension of $K$, choose a nonzero point of $G_K$. The scalar action identifies the geometric point set with $\mathbf F_p$. On all functions, the trivial character occurs twice, once from the orbit $\{0\}$ and once from $\mathbf F_p^\times$, while every other character occurs once. Passing to the augmentation ideal removes one trivial copy. Thus the $p-1$ characters of $\mathbf F_p^\times$, including the remaining trivial weight, each occur once in $I_K$. Every $(I_i)_K$ has dimension one. The idempotent summands $I_i$ are direct summands of the finite free module $I$, so they are torsion-free; their generic dimensions show that they are free of rank one.

Choose a generator $x$ in the weight-one summand. Multiplication gives maps

$$
I_1^{\otimes i}\longrightarrow I_i.
$$

They are isomorphisms. This is the delicate coefficient step. Choose generators $z_i$ of the weight summands, with $z_1=x$, and write every product and reduced coproduct in these generators. The identity

$$
\Delta(z_1z_i)=\Delta(z_1)\Delta(z_i)
$$

shows inductively that the coefficient of $z_{i+1}$ in $z_1z_i$ and the coefficient of $z_1\otimes z_i$ in the reduced coproduct of $z_{i+1}$ multiply to $i+1$ modulo coefficients already normalized at earlier stages. For $i+1<p$, this integer is a unit. Both coefficients lie in $R$, so each is a unit. Rescale $z_{i+1}$ so that $z_1z_i=z_{i+1}$. Beginning with $i=1$ produces

$$
z_i=x^i\qquad(1\le i\le p-1).
$$

This induction divides only by $2,\ldots,p-1$, never by $p$.

The remaining product has weight one:

$$
x^p=a x.
$$

The $p$ elements $1,x,\ldots,x^{p-1}$ span and have independent generic images, hence form an $R$-basis. This proves (5.5). The calculation

$$
(ux)^p=u^pa x=u^{p-1}a(ux)
$$

gives (5.6). On overlaps the weight-one modules glue to the invertible module $L$. $\square$

The coefficient comparison used in the induction will now be completed, including the coproduct. It is precisely there that the second Oort--Tate parameter appears.

## 6. The Oort--Tate normal form

### 6.1 The universal coefficient calculation

The algebra $R[x]/(x^p-a x)$ is finite free, but most coproducts on it do not define group laws. Scalar weights force the reduced coproduct of $x$ to have the shape

$$
\Delta(x)=x\otimes1+1\otimes x
+b\,C_p(x\otimes1,1\otimes x),
\tag{6.1}
$$

where $C_p(X,Y)$ is homogeneous of total degree $p$ with no pure terms. Associativity, compatibility with $x^p=ax$, and the antipode identity determine both $C_p$ and the product $ab$ up to one harmless unit normalization.

We isolate the polynomial calculation so that no classification theorem is hidden in notation.

Fix a generator of $\mathbf F_p^\times$. Let $\Lambda_p$ be the finite étale $\mathbf Z_{(p)}$-algebra generated by its universal Teichmuller lift; for $p=2$, take $\Lambda_2=\mathbf Z_{(2)}$. A henselian local ring of residue characteristic $p$ receives the corresponding map from the relevant local factor of $\Lambda_p$, because the chosen residue roots lift uniquely. Changing the generator only changes the universal coordinate normalization.

**Lemma 6.1 (universal Oort--Tate calculation).** For every prime $p$ there are

$$
w_p\in p\Lambda_p^\times,
\qquad
C_p(X,Y)=\sum_{i=1}^{p-1}c_iX^iY^{p-i}
\in\Lambda_p[X,Y],
\tag{6.2}
$$

and a polynomial $J_p(X)\in\Lambda_p[B,X]$ with no constant term, having the following property. For every $\Lambda_p$-algebra $R$ and every $a,b\in R$ satisfying

$$
ab=w_p,
\tag{6.3}
$$

the formulas

$$
\begin{aligned}
A_{a,b}&=R[x]/(x^p-a x),\\
\Delta(x)&=x\otimes1+1\otimes x+bC_p(x\otimes1,1\otimes x),\\
\varepsilon(x)&=0,\\
S(x)&=J_p(b,x)
\end{aligned}
\tag{6.4}
$$

make $A_{a,b}$ a commutative, cocommutative Hopf algebra. The constants can be normalized so that duality interchanges $a$ and $b$. Any weight-one Hopf structure on (5.5) is uniquely of this form after a unique rescaling compatible with (5.6).

**Proof.** Begin over the universal ring

$$
U=\Lambda_p[A,B]/(AB-W),
$$

where $W$ is initially undetermined and is required to generate the same ideal as $p$. Before introducing $B$, write the most general symmetric reduced coproduct as

$$
\Delta(X)=X+Y+\sum_{i=1}^{p-1}D_iX^iY^{p-i},
$$

with $D_i=D_{p-i}$. Compatibility of $\Delta$ with multiplication, compared first in bidegrees $(1,p-1)$ and $(p-1,1)$ and then successively inward, shows that the ideals generated by the nonzero $D_i$ coincide and that their ratios are units determined universally. Over the universal principal chart choose their common factor $B$ and write the normalized law

$$
\Delta(X)=X+Y+B\sum_{i=1}^{p-1}c_iX^iY^{p-i}.
\tag{6.5}
$$

There are no lower-degree mixed terms to eliminate. A monomial $X^iY^j$ in the reduced coproduct must have scalar weight one, so

$$
i+j\equiv1\pmod{p-1}.
$$

For $1\le i,j\le p-1$, the only possible total degree is $p$. This is the crucial economy supplied by the $\mathbf F_p^\times$-action.

Insert (6.5) into

$$
\Delta(X)^p=A\Delta(X)
\quad\text{modulo }(X^p-AX,Y^p-AY).
\tag{6.6}
$$

For a mixed monomial $X^iY^{p-i}$, the binomial coefficient $\binom pi$ is divisible by $p$ and $\binom pi/p$ is a unit of $\Lambda_p$. After the outer coefficients have been fixed, the next equation is linear in the next $c_i$ with coefficient $i$ or $p-i$. Those integers are units. The coefficient equations therefore solve recursively for $c_i$, except for the one common scalar already named $B$. The final unsolved equation is

$$
AB=W,
$$

where $W/p$ is a unit. Fixing the common scalar fixes $W=w_p$ and the $c_i$. Symmetry gives cocommutativity.

Next compare the two substitutions of (6.5) into three variables. Order mixed tridegrees lexicographically. In the first tridegree at which the two expressions could differ, every coefficient involving a later $c_i$ cancels, while the remaining coefficient is one of the same two-variable recursion equations just solved. It therefore vanishes. Induction through the tridegrees proves that the difference between

$$
(X\star Y)\star Z
\quad\text{and}\quad
X\star(Y\star Z)
$$

is governed by the same recursion already solved from (6.6); hence it vanishes. At total degree at least $p$, reduce with $X^p=AX$, $Y^p=AY$, $Z^p=AZ$ and use $AB=w_p$. This proves coassociativity. The zero coordinate gives the counit. Solving $X\star J=0$ recursively determines $J_p(B,X)$; the same unit denominators occur, and associativity makes it both a left and right inverse.

All identities are polynomial identities over $U$, so every specialization satisfying (6.3) inherits them. Conversely, the coefficient eliminations show that any weight-one Hopf law is brought uniquely to (6.5), compatibility with the relation forces (6.3), and the recursive equations force the same constants. Finally, applying the finite dual Hopf construction exchanges multiplication and comultiplication. Choosing the initial common scalar so that the resulting coordinate has coefficient one makes this operation send $(A,B)$ to $(B,A)$. This is the asserted self-dual normalization. $\square$

Only three properties of the constants will be used later: $v(w_p)=v(p)$, the construction is functorial, and the normalized duality swaps the two parameters. Their individual numerical values depend on the chosen universal weight-one coordinate and carry no arithmetic meaning.

### 6.2 Oort--Tate data

The local coordinate changes in (5.6) reveal the coordinate-free object. Let $S$ carry the local $\Lambda_p$-structure supplied above, so that the universal constants of Lemma 6.1 are defined on $S$. An **Oort--Tate datum** is a triple

$$
(L,a,b),
\tag{6.7}
$$

where $L$ is an invertible $\mathcal O_S$-module,

$$
a\in\Gamma(S,L^{\otimes(1-p)}),
\qquad
b\in\Gamma(S,L^{\otimes(p-1)}),
\tag{6.8}
$$

and contraction gives

$$
a\otimes b=w_p\in\Gamma(S,\mathcal O_S).
\tag{6.9}
$$

If a local frame produces a coordinate $x$, changing it by $x'=ux$ changes the scalar representatives by

$$
a'=u^{p-1}a,
\qquad
b'=u^{1-p}b.
\tag{6.10}
$$

These are exactly the transition laws of (6.8). An isomorphism of data is an isomorphism of line bundles carrying both sections to the corresponding sections. Thus the parameters are not intrinsically two elements of a ring; they become elements only after the line is trivialized.

### 6.3 Construction from the data

Choose local frames of $L$. On such a chart define the Hopf algebra $A_{a,b}$ by (6.4). On an overlap, (6.10) and $x'=ux$ give an isomorphism of algebras because

$$
(x')^p-a'x'=u^p(x^p-a x).
$$

Formula (6.1) is also preserved: the correction term has $p$ copies of $x$, while $b$ changes by $u^{1-p}$, producing the required overall factor $u$. The counit and antipode follow from uniqueness in Lemma 6.1. Hence the local Hopf algebras glue.

Denote the resulting group by

$$
G_{L,a,b}.
$$

Its coordinate algebra is locally free with basis

$$
1,x,x^2,\ldots,x^{p-1},
$$

so the group is finite flat of order $p$. The scalar action is visible in the weight of $x$. Arbitrary base change pulls $(L,a,b)$ back and gives the base-changed group.

### 6.4 Classification and uniqueness

**Theorem 6.2 (Oort--Tate classification over the arithmetic local base).** Let $S=\operatorname{Spec}R$, where $R$ is a henselian mixed-characteristic DVR of residue characteristic $p$. The construction

$$
(L,a,b)\longmapsto G_{L,a,b}
\tag{6.11}
$$

identifies the groupoid of Oort--Tate data and their isomorphisms with the groupoid of finite flat commutative group schemes of order $p$ and their isomorphisms. In particular it gives a bijection on isomorphism classes. Under the self-dual normalization,

$$
G_{L,a,b}^D\simeq G_{L^{-1},b,a}.
\tag{6.12}
$$

**Proof strategy.** Essential surjectivity is the weight-line lemma plus the universal coefficient calculation. Full faithfulness follows because a group homomorphism must preserve the scalar weights and is therefore determined by its action on the weight-one line.

**Proof.** Let $G$ have order $p$. Proposition 5.1 supplies the scalar action. For odd $p$, Lemma 5.2 constructs the weight-one invertible module $L$ and local presentations $x^p=ax$. Lemma 6.1 puts the coproduct in the unique form (6.1), produces $b$, and forces $ab=w_p$. The transformation rules on overlaps are (6.10), so the local coefficients glue to an Oort--Tate datum. The direct calculation of §6.5 supplies the same conclusion when $p=2$. This proves essential surjectivity.

Let $f:G_{L,a,b}\to G_{L',a',b'}$ be an isomorphism. Pullback commutes with $[c]$, so it preserves Teichmuller weights. Its restriction to the weight-one summand is therefore an isomorphism $L'\to L$. In local frames it sends $x'$ to $ux$ with $u$ a unit. Compatibility with the relation and coproduct gives precisely (6.10). Conversely such an isomorphism of data makes $x'\mapsto ux$ a Hopf isomorphism. This proves full faithfulness.

The normalized dual Hopf calculation in Lemma 6.1 exchanges the two coefficients and dualizes the weight-one line, proving (6.12). $\square$

The local hypotheses are the ones needed in this book. The line-bundle formulation explains how the theorem globalizes when the same universal constants and descent hypotheses are available. Over a local ring every invertible module is free, but retaining $L$ makes base change and duality transparent.

### 6.5 The explicit quadratic case

When $p=2$, no Teichmuller-weight separation is needed. Put $w_2=2$. For $a,b\in R$ with $ab=2$, define

$$
A_{a,b}=R[x]/(x^2-a x)
$$

and

$$
\Delta(x)=x\otimes1+1\otimes x-bx\otimes x,
\qquad \varepsilon(x)=0,
\qquad S(x)=x.
\tag{6.13}
$$

We verify the only nonformal point. Put $X=x\otimes1$, $Y=1\otimes x$, and $Z=X+Y-bXY$. Using $X^2=aX$, $Y^2=aY$, and $ab=2$, one obtains

$$
Z^2-aZ=((ab)^2+2-3ab)XY=0.
$$

Thus the coproduct respects the relation. The operation

$$
X\star Y=X+Y-bXY
$$

is visibly symmetric, and direct expansion gives

$$
(X\star Y)\star Z=X\star(Y\star Z).
$$

Moreover $X\star X=2X-bX^2=(2-ab)X=0$, so every point is its own inverse. This proves the Hopf identities. A general rank-two augmented free algebra has a basis $1,x$ with $x^2=ax$ after translating $x$ into the augmentation ideal; writing the most general coproduct and imposing the same identities produces one coefficient $b$ and the relation $ab=2$. Hence (6.13) is the full order-two classification.

For $a=2,b=1$, setting $x=1-T$ identifies the group with $\mu_2$. For $a=1,b=2$, the polynomial $x^2-x$ is split étale and gives the constant group. Intermediate valuation pairs occur when $v(2)>1$.

### 6.6 Automorphisms and reduction of the normal form

The normal form also makes its own residual symmetries visible. An automorphism has $x\mapsto ux$ for a unit $u$, and (6.10) preserves the same pair precisely when

$$
u^{p-1}a=a,
\qquad
u^{1-p}b=b.
$$

Over a mixed-characteristic domain neither parameter is zero, so this is equivalent to

$$
u^{p-1}=1.
\tag{6.14}
$$

Thus the automorphism group of an order-$p$ model is the expected scalar group $\mathbf F_p^\times$, realized by Teichmuller units; it is trivial for $p=2$. No extra automorphism appears when the special fiber becomes nonreduced. The full functor of special-fiber automorphisms can be larger, but most of those automorphisms do not lift while preserving the integral model.

Reduction of (6.4) explains the three geometric types directly. If $a$ is a unit, the polynomial derivative is a unit and the group is étale. If both $a$ and $b$ lie in the maximal ideal, then reduction gives

$$
k[x]/(x^p),
\qquad
\Delta(x)=x\otimes1+1\otimes x,
$$

so the special fiber is already the split group $\alpha_p$, without extending $k$. If $b$ is a unit, duality makes the group multiplicative type; after a splitting extension its special fiber is $\mu_p$.

The asymmetry between the algebra relation and coproduct is only coordinate asymmetry. The relation displays étaleness through $a$, while the dual coproduct calculation displays multiplicative type through $b$. Formula (6.12) proves that the two roles are intrinsically equal.

## 7. The DVR classification

### 7.1 Parameters over a local principal base

Let $R$ now be a henselian mixed-characteristic DVR. Every invertible module is free, so choose a frame of $L$. The Oort--Tate datum becomes a pair

$$
(a,b)\in R^2,
\qquad ab=w_p.
\tag{7.1}
$$

Write $G_{a,b}$ for the resulting group. Since $w_p/p$ is a unit,

$$
v(a)+v(b)=v(p)=e.
\tag{7.2}
$$

Both valuations are nonnegative. Thus a single integer

$$
r(G)=v(a),
\qquad 0\le r(G)\le e,
\tag{7.3}
$$

measures how far the model lies from the étale endpoint. The complementary integer $e-r(G)=v(b)$ measures the same distance for the dual.

The integer is intrinsic. Replacing the frame by a unit changes $a$ by a $(p-1)$st power of a unit and does not change its valuation. It is sometimes called the Oort--Tate or Raynaud exponent of the rank-one model.

### 7.2 Isomorphisms and valuations

**Proposition 7.1.** Two pairs $(a,b)$ and $(a',b')$ define isomorphic groups over $R$ if and only if there is $u\in R^\times$ such that

$$
a'=u^{p-1}a,
\qquad
b'=u^{1-p}b.
\tag{7.4}
$$

**Proof.** This is the local form of full faithfulness in Theorem 6.2. A Hopf isomorphism preserves the weight-one line and hence sends the target coordinate to $ux$ for a unit $u$. The relation gives the first equality, and the coproduct gives the second. Conversely these equalities make $x'\mapsto ux$ a Hopf isomorphism. $\square$

Equal valuation is necessary but not always sufficient for isomorphism: the unit class of $a$ in

$$
R^\times/R^{\times(p-1)}
$$

can matter. If the residue field is algebraically closed and $R$ is strictly henselian, every unit has a $(p-1)$st root by Hensel's lemma, so valuation alone classifies the split forms. Over a finite residue field, the residue-unit class retains an unramified twisting character.

### 7.3 Special-fiber type

The two parameters detect the special fiber without computing every coefficient in (6.1).

**Theorem 7.2 (type criterion).** Let $G=G_{a,b}$.

1. $G$ is finite étale over $R$ if and only if $a$ is a unit, equivalently $r(G)=0$.
2. $G$ is of multiplicative type if and only if $b$ is a unit, equivalently $r(G)=e$.
3. If $0<r(G)<e$, then $G_k$ and $G_k^D$ are both isomorphic to $\alpha_p$ in the coordinates induced by a trivialization of the Oort--Tate line; in particular both are connected.

**Proof.** In the presentation $x^p-a x$, the derivative is

$$
px^{p-1}-a.
$$

Modulo the maximal ideal it is $-\bar a$. If $a$ is a unit, the algebra is finite étale. Conversely, if $a$ is not a unit, the special-fiber algebra is $k[x]/(x^p)$ and is not reduced, so the group is not étale. This proves the first assertion.

By (6.12), the dual is $G_{b,a}$. The group $G$ is of multiplicative type exactly when its dual is étale, which by the first assertion is equivalent to $b$ being a unit. This proves the second assertion.

If both parameters are nonunits, the special-fiber coordinate algebra of $G$ and that of $G^D$ is $k[x]/(x^p)$. The correction term in the coproduct is multiplied respectively by $b$ and $a$, so it vanishes in each special fiber. The coordinate is primitive, proving that both groups are $\alpha_p$. $\square$

Thus the valuation interval has a geometric meaning:

$$
\begin{array}{c|c|c}
r&v(b)&\text{special-fiber type}\\
\hline
0&e&\text{étale}\\
0<r<e&e-r&\text{local-local}\\
e&0&\text{multiplicative}.
\end{array}
\tag{7.5}
$$

### 7.4 Cartier duality in parameters

The normalized duality formula reads

$$
G_{a,b}^D\simeq G_{b,a}.
\tag{7.6}
$$

Consequently

$$
r(G^D)=e-r(G).
\tag{7.7}
$$

This proves the endpoint exchange and the stability of the intermediate range. It also supplies a useful check on every inertia formula: replacing a generic character by its cyclotomic dual must replace $r$ by $e-r$.

Self-duality requires more than $r=e/2$. The valuation equality is necessary, but an actual isomorphism $G_{a,b}\simeq G_{b,a}$ requires a unit $u$ with

$$
b=u^{p-1}a.
$$

Thus unit classes can obstruct self-duality even when the valuation lies at the midpoint.

### 7.5 Cotangent length

The exponent has an intrinsic infinitesimal interpretation. Let

$$
\omega_G=e^*\Omega_{G/R}
$$

be the conormal module at the identity. If $I$ is the augmentation ideal, then $\omega_G=I/I^2$.

**Proposition 7.3.** For $G=G_{a,b}$,

$$
\omega_G\simeq R/(a),
\qquad
\omega_{G^D}\simeq R/(b).
\tag{7.8}
$$

Consequently

$$
\operatorname{length}_R\omega_G=r(G),
\qquad
\operatorname{length}_R\omega_{G^D}=e-r(G),
\tag{7.9}
$$

and the two lengths add to $e$.

**Proof.** In the local presentation, $I$ is generated by $x,x^2,\ldots,x^{p-1}$. Modulo $I^2$, only the class of $x$ remains. The relation $x^p=ax$ becomes $a x=0$ in $I/I^2$, because $x^p\in I^2$ for every prime $p$. There are no further linear relations, so $I/I^2\simeq R/(a)$. Apply the same calculation to $G^D=G_{b,a}$. Since a nonzero element of valuation $s$ generates an ideal of colength $s$, (7.9) follows from (7.2). $\square$

The formula explains the endpoints without derivatives. An étale group has zero conormal module, so $r=0$. A multiplicative group has maximal conormal length $e$, while its dual has none. Intermediate groups divide the total infinitesimal defect between the group and its dual.

This length is stable in normalized form under ramified base change: both the length and $e$ are multiplied by the relative ramification index. It is also additive in a short exact sequence under the additional exactness statement for invariant differentials; no such additivity will be assumed here without verifying that sequence.

### 7.6 Morphisms and the order of models

Classification of objects also permits a precise morphism calculation. Let

$$
f:G_{a,b}\longrightarrow G_{a',b'}.
$$

A nonzero generic homomorphism between the one-dimensional $\mathbf F_p$-groups is an isomorphism. Integrally, its pullback on weight-one coordinates must have the form

$$
f^*(x')=c x
\tag{7.10}
$$

for some nonzero $c\in R$. Compatibility with the relation and the homogeneous coproduct gives

$$
c^pa=c a',
\qquad
cb=c^pb'.
\tag{7.11}
$$

Because $R$ is a domain and $c\ne0$, these are equivalent to

$$
a'=c^{p-1}a,
\qquad
b=c^{p-1}b'.
\tag{7.12}
$$

Conversely, (7.12) makes (7.10) a Hopf map. Indeed the algebra relation follows from the first equality, while homogeneity of $C_p$ changes the correction term by $c^p$ and the second equality gives coproduct compatibility.

If $c$ is a unit, this is the isomorphism criterion (7.4). If $c$ is not a unit, $f_K$ is an isomorphism but $f$ is not. On exponents,

$$
r(G_{a',b'})=r(G_{a,b})+(p-1)v(c).
\tag{7.13}
$$

Thus integral models of a fixed generic group can be partially ordered by nonzero morphisms that become isomorphisms generically. Only exponent differences divisible by $p-1$ can occur in this way, and the unit equations in (7.12) must also hold.

The calculation gives a concrete instance of the failure of generic fullness. The inverse of $f_K$ would require $c^{-1}$ on weight-one coordinates and does not preserve the target lattice when $c$ is a nonunit. Hence a generic isomorphism need not be an integral isomorphism even though it may extend in one direction.

### 7.7 The unramified dichotomy

Suppose $R$ is unramified over $\mathbf Z_p$, so $e=1$. Equation (7.2) leaves only

$$
(v(a),v(b))=(0,1)\quad\text{or}\quad(1,0).
$$

Therefore every order-$p$ finite-flat group has either étale or multiplicative special fiber; no local-local rank-$p$ model occurs.

**Corollary 7.4.** Over an unramified mixed-characteristic henselian DVR, an order-$p$ finite-flat group is either finite étale or of multiplicative type. Cartier duality exchanges the two classes.

This is a statement about integral types, not necessarily split groups. The étale endpoint may carry an unramified character, and the multiplicative endpoint its Cartier-dual twist. After strict henselization the endpoints become $\underline{\mathbf Z/p\mathbf Z}$ and $\mu_p$.

When $e>1$, each integer $0\le r\le e$ can occur after a suitable choice of unit parameters satisfying (7.1). The intermediate values are genuine new integral models. This simple valuation fact is why an argument proved over $\mathbf Z_p$ cannot be transferred unchanged to a ramified coefficient field.

## 8. Generic characters and inertia

### 8.1 Recovering the character from the parameter

Coordinates regain their arithmetic meaning on the generic fiber. Let $G=G_{a,b}$ and choose a nonzero geometric point. In the coordinate presentation its value $z$ satisfies

$$
z^{p-1}=a.
\tag{8.1}
$$

Conversely the $p-1$ scalar multiples of one such $z$, together with zero, are all geometric points. Hence

$$
\sigma(z)=\chi_G(\sigma)z,
$$

and the Kummer class of $a$ in

$$
K^\times/K^{\times(p-1)}
\tag{8.2}
$$

determines $\chi_G$. Changing the coordinate multiplies $a$ by a $(p-1)$st power, so the class is intrinsic.

This proves more than a heuristic relation. The splitting field of the generic group is obtained by adjoining a $(p-1)$st root of $a$, and the action on that root is exactly the one-dimensional $\mathbf F_p$-character of the group. Since $p-1$ is prime to the residue characteristic, the resulting ramification is tame; any residue-unit part contributes only an unramified twist.

### 8.2 The tame inertia exponent

Write

$$
a=u\pi^r,
\qquad u\in R^\times,
\qquad 0\le r\le e.
\tag{8.3}
$$

Choose a $(p-1)$st root $\pi^{1/(p-1)}$ in a separable closure and define the tame character

$$
\theta:I_K\longrightarrow\mathbf F_p^\times
$$

by the action on that root, with the convention chosen so that

$$
\overline\chi_p|_{I_K}=\theta^e.
\tag{8.4}
$$

The convention fixes the possible inverse that otherwise comes from choosing arithmetic or geometric Galois action.

**Theorem 8.1 (inertia formula).** For $G_{a,b}$ with $r=v(a)$,

$$
\chi_G|_{I_K}=\theta^r.
\tag{8.5}
$$

**Proof.** A $(p-1)$st root of the unit $u$ generates an unramified extension: after adjoining a root of its residue class, the derivative $(p-1)X^{p-2}$ is a unit and Hensel's lemma lifts the root. Thus inertia acts trivially on the unit-root factor. A chosen root of $a$ is

$$
u^{1/(p-1)}\bigl(\pi^{1/(p-1)}\bigr)^r.
$$

Inertia acts on it by $\theta^r$. By §8.1 this action is $\chi_G$. $\square$

The exponent is read modulo $p-1$ as a character, but its integral representative $0\le r\le e$ contains more information. When $e\ge p-1$, different integral models can have the same inertial character. Oort--Tate classification remembers valuation depth that the generic representation forgets.

### 8.3 Dual characters

Write $b=u'\pi^{e-r}$. Applying Theorem 8.1 to the dual gives

$$
\chi_{G^D}|_{I_K}=\theta^{e-r}.
\tag{8.6}
$$

On the other hand (5.2) and (8.4) give

$$
\overline\chi_p\chi_G^{-1}|_{I_K}
=\theta^e\theta^{-r}
=\theta^{e-r}.
$$

Thus the coordinate classification, valuation complement, and Tate-twisted Cartier dual all agree. This triangular compatibility is a powerful normalization check.

At the endpoints, an étale model has $r=0$ and unramified generic character. A multiplicative model has $r=e$ and generic character equal to the cyclotomic character times an unramified twist. Intermediate models carry the tame exponent $r$.

### 8.4 Twists and descent

The unit class of $a$ records the unramified part of the character. If $a=u\pi^r$ and $u$ is replaced by $u c^{p-1}$, the group is unchanged after the corresponding coordinate rescaling. The residue class of $u$ modulo $(p-1)$st powers determines a character of the residue-field Galois group, and inflating it to $\Gamma_K$ gives the unramified twist of $\theta^r$.

After an unramified extension that extracts the required root of $u$, the model acquires a parameter with pure valuation $\pi^r$. Descent back to $R$ is not automatic from the descended generic character alone; it is carried by the semilinear action on the weight-one line $L$. The line-bundle formulation (6.7) records precisely this descent datum.

For a finite extension $K'/K$, restricting $\chi_G$ gives the generic character after base change. The integral exponent, however, must be recomputed using the normalized valuation of $K'$. Chapter 10 makes that transformation explicit.

### 8.5 Rigidity below the ramification boundary

The interval $0\le r\le e$ explains a sharp rank-one rigidity phenomenon. Assume

$$
e<p-1.
\tag{8.7}
$$

Two exponents in this interval that are congruent modulo $p-1$ must be equal. The generic character then determines not only the inertia exponent but the entire order-$p$ model.

**Theorem 8.2 (height-one low-ramification rigidity).** Let $R$ be as above and assume $e<p-1$. For finite-flat commutative groups $G,H$ of order $p$, every generic morphism

$$
G_K\longrightarrow H_K
$$

extends uniquely over $R$. In particular, two such groups with isomorphic generic fibers are isomorphic. Thus the generic-fiber functor is fully faithful on the order-$p$ subcategory.

**Proof strategy.** A nonzero generic map is an isomorphism between one-dimensional $\mathbf F_p$-characters. Equality of the characters makes the ratio of the two Oort--Tate $a$-parameters a $(p-1)$st power in $K$. The short valuation interval forces that root to be a unit, which is exactly the integral morphism criterion.

**Proof.** The zero morphism extends uniquely. Let the generic morphism be nonzero. Choose parameters $(a,b)$ and $(a',b')$. A nonzero map of the generic one-dimensional groups identifies their characters, so the Kummer classes of $a$ and $a'$ agree. Hence

$$
a'=c^{p-1}a
$$

for some $c\in K^\times$, after incorporating the scalar of the chosen generic map. Taking valuations gives

$$
r(H)-r(G)=(p-1)v(c).
\tag{8.8}
$$

Both exponents lie between $0$ and $e<p-1$. Their difference cannot be a nonzero multiple of $p-1$, so it is zero and $v(c)=0$. Thus $c\in R^\times$. Since $ab=a'b'=w_p$, the first parameter equality implies

$$
b=c^{p-1}b'.
$$

Equations (7.12) now define the required integral morphism, which is an isomorphism because $c$ is a unit. Uniqueness follows from faithfulness of the generic-fiber functor for maps between flat schemes. $\square$

The boundary is real. If $e\ge p-1$ and both endpoints remain integral, take a model with parameter $a$ and replace it by

$$
a'=\pi^{p-1}a,
\qquad
b'=\pi^{1-p}b.
$$

The two generic Kummer classes agree. Equation (7.10) with $c=\pi$ gives a morphism that is a generic isomorphism but not an integral isomorphism. At and beyond the boundary, generic character data can no longer distinguish all height-one Hopf lattices.

The theorem is deliberately rank one. Extending arbitrary maps between higher-height finite-flat groups below the same boundary requires a separate full-faithfulness theorem. Nothing in the existence of order-$p$ factors guarantees that a higher-dimensional generic representation has a stable flag over $K$.

## 9. Exact calculus in small height

### 9.1 Closing a line in a finite-flat representation

The classification becomes useful when an order-$p$ group is not presented in advance but occurs as a subquotient of a larger torsion group. Let $R$ be a mixed-characteristic DVR, let $G/R$ be finite flat, killed by $p$, and suppose $G_K$ is therefore the finite étale group attached to an $\mathbf F_p$-representation

$$
V=G(K^s).
$$

Let $W\subset V$ be a Galois-stable line. It defines a closed order-$p$ subgroup $H_K\subset G_K$. By Theorem 2.1 its closure $H\subset G$ is finite flat of order $p$. The quotient theorem gives

$$
0\longrightarrow H\longrightarrow G
\longrightarrow G/H\longrightarrow0,
\tag{9.1}
$$

and the generic sequence is the representation sequence

$$
0\longrightarrow W\longrightarrow V
\longrightarrow V/W\longrightarrow0.
\tag{9.2}
$$

The group $H$ has Oort--Tate data and an exponent $r(H)$. Thus the integral ambient model assigns more than a character to the line: it chooses one of the admissible valuation lifts of that character.

**Theorem 9.1 (closure of a stable line).** In the preceding setting, a Galois-stable line has a unique finite-flat closure inside $G$. Its generic character, special-fiber type, and Cartier-dual type are given by Chapters 7 and 8. The quotient in (9.1) is finite flat and is uniquely determined by the chosen middle model $G$.

**Proof.** Existence, flatness, and uniqueness of $H$ are Theorem 2.1. Its order equals the generic order $p$, so Theorem 6.2 applies. The represented quotient is finite flat and (9.1) is faithfully flat exact. Its generic fiber is the quotient because quotients commute with base change. $\square$

It is important that the line be Galois stable. A line visible only after extending the coefficient field or the base field does not define a subgroup over $K$. It may define one after scalar extension, but descent back requires a stable line together with compatible descent data.

### 9.2 Prime-order filtrations

Suppose a representation $V$ has a full Galois-stable flag

$$
0=V_0\subset V_1\subset\cdots\subset V_h=V,
\qquad \dim_{\mathbf F_p}(V_i/V_{i-1})=1.
\tag{9.3}
$$

Close every $V_i$ in $G$. The inclusions are nested, and successive represented quotients give a filtration

$$
0=G_0\subset G_1\subset\cdots\subset G_h=G
\tag{9.4}
$$

by finite-flat subgroups with order-$p$ quotients. Each quotient has a parameter exponent $r_i$ between $0$ and $e$.

**Proposition 9.2.** Under (9.3), the closure filtration (9.4) is the unique filtration inside $G$ with those generic subspaces. It is stable under flat extension of DVRs, and

$$
|G_i|=p^i.
$$

**Proof.** Uniqueness and base change hold term by term by the closure theorem. Exactness of

$$
0\to G_{i-1}\to G_i\to G_i/G_{i-1}\to0
$$

gives $|G_i|=|G_{i-1}|p$, and induction starts with order one. $\square$

Not every $V$ has such a flag over $K$. A two-dimensional irreducible $\mathbf F_p$-representation has no stable line, even though its underlying vector space has many lines over $\mathbf F_p$. After a finite extension of $K$ that trivializes the finite image, a full flag exists and closes after base change. Those subgroups descend only when the flag and its closures carry compatible descent data.

Nor does every finite flat $p$-group come killed by $p$. If $G$ is killed by $p^n$, its generic points form a finite $\mathbf Z/p^n\mathbf Z$-module only under an additional module structure, and a prime-order filtration must be justified from the actual Galois module. The phrase “height $h$” records order $p^h$; it does not assert the existence of a height-one composition series over the base.

### 9.3 Extensions and the limits of classification

Given two order-$p$ groups $H$ and $Q$, a faithfully flat exact sequence

$$
0\longrightarrow H\longrightarrow G\longrightarrow Q\longrightarrow0
\tag{9.5}
$$

makes $G$ finite flat of order $p^2$. The middle group need not be killed by $p$: the constant sequence arising from

$$
0\longrightarrow\mathbf Z/p\mathbf Z
\longrightarrow\mathbf Z/p^2\mathbf Z
\longrightarrow\mathbf Z/p\mathbf Z
\longrightarrow0
$$

is the simplest example. Even when $G$ is killed by $p$, the extension may be nonsplit.

Oort--Tate data classify $H$ and $Q$ but not the extension class. The generic extension may split while the integral extension does not, or an extension of generic fibers with prescribed endpoint models may fail to have an integral middle term. The obstruction lies in compatibility of Hopf lattices, not in the two endpoint characters alone.

There is, however, a secure one-way statement.

**Proposition 9.3 (inheritance from a middle model).** If a generic exact sequence

$$
0\to W\to V\to U\to0
$$

is realized by a finite-flat middle model $G$ of $V$, then closure of $W$ in $G$ and the represented quotient give finite-flat models of $W$ and $U$ and an integral exact sequence. Conversely, separately chosen models of $W$ and $U$ do not by themselves produce a model of $V$.

**Proof.** The forward statement is Theorem 2.1 followed by the quotient theorem. For the converse warning, observe that a middle Hopf algebra would have to be a torsor extension of the quotient algebra by the subgroup Hopf algebra. The torsor identity imposes integral equations not determined by the two algebras separately. Hence no construction follows formally from the endpoints. Concrete nonsplit connected--étale sequences on ordinary elliptic $p$-torsion exhibit the extra extension datum. $\square$

This asymmetry is the correct exact-category behavior. Subobjects and quotients inherit finite-flatness from an existing middle term over a DVR. Extensions are new existence problems.

### 9.4 Dual filtrations and annihilators

Let $H\subset G$ be a finite-flat subgroup. Its annihilator

$$
H^\perp=\ker(G^D\to H^D)
$$

is finite flat and fits into

$$
0\longrightarrow H^\perp\longrightarrow G^D
\longrightarrow H^D\longrightarrow0.
\tag{9.6}
$$

If $H$ is the closure of $H_K$, then $H^\perp$ is the closure of the generic annihilator $H_K^\perp$ in $G_K^D$. Indeed both are finite-flat subgroups of $G^D$ with the same generic fiber, so closure uniqueness identifies them.

Apply this to (9.4). Duality reverses the flag:

$$
0=G_h^\perp\subset G_{h-1}^\perp\subset\cdots
\subset G_0^\perp=G^D.
\tag{9.7}
$$

If the quotient $G_i/G_{i-1}$ has exponent $r_i$, the corresponding reversed dual quotient has exponent

$$
e-r_i.
\tag{9.8}
$$

This supplies a clean consistency test for filtered torsion: dualizing reverses the order of the factors, replaces every generic character by its cyclotomic dual, and complements every Oort--Tate exponent.

For a perfect pairing $G\times G\to\mu_p$, the annihilator flag lives inside $G$ itself. A subgroup is isotropic when it lies in its annihilator, and an order computation then constrains its possible height. Such rank calculus uses scheme-theoretic orders and remains valid when the special fiber has only one geometric point.

### 9.5 A self-dual height-two line

The most common small-height configuration is a height-two group with an alternating perfect pairing. Let $G/R$ be finite flat of order $p^2$, killed by $p$, and let

$$
e_G:G\times G\longrightarrow\mu_p
\tag{9.9}
$$

be a perfect alternating pairing. Suppose the generic representation $V=G(K^s)$ has a Galois-stable line $W$. Let $H$ be its closure in $G$.

The restriction of $e_G$ to $H\times H$ is trivial. It is trivial on the generic fiber because an alternating pairing on a one-dimensional vector space vanishes. The source $H\times H$ is flat, and two morphisms from a flat finite scheme to the separated group $\mu_p$ that agree generically agree everywhere. Hence $H$ is isotropic:

$$
H\subset H^\perp.
$$

Perfectness and the rank formula give

$$
|H^\perp|=\frac{|G|}{|H|}=p.
$$

The inclusion between two finite-flat groups of the same rank is an equality because it is already an equality on generic fibers, or by closure uniqueness. Therefore $H=H^\perp$.

**Proposition 9.4 (self-dual line sequence).** Under the preceding hypotheses there is a canonical exact sequence

$$
0\longrightarrow H\longrightarrow G\longrightarrow H^D
\longrightarrow0.
\tag{9.10}
$$

If $H$ has Oort--Tate exponent $r$, the quotient has exponent $e-r$. On generic characters,

$$
\chi_{G/H}=\overline\chi_p\chi_H^{-1},
$$

so

$$
\det V=\overline\chi_p.
\tag{9.11}
$$

**Proof.** The pairing identifies $G/H^\perp$ with $H^D$. Since $H=H^\perp$, the quotient sequence is (9.10). The exponent statement is (7.7), and taking the product of the two one-dimensional generic characters gives (9.11). $\square$

Over an unramified base, $r$ is $0$ or $1$, so the two factors are one étale and one multiplicative. Over a ramified base, a self-dual height-two group can instead have paired intermediate exponents $r$ and $e-r$. The extension class in (9.10) is still extra data: knowing the paired endpoints does not decide whether $G$ splits.

For elliptic $p$-torsion, the Weil pairing supplies (9.9). Thus every Galois-stable generic line whose closure is defined produces its Cartier-dual quotient automatically. This is the integral reason the two diagonal characters of a reducible elliptic representation multiply to the cyclotomic character.

## 10. Change of base

### 10.1 Flat extensions of valuation rings

Let $R\to R'$ be a local extension of DVRs with fraction fields $K\to K'$. Such a map is flat. Finite-flat groups, exact sequences, Cartier duals, and Oort--Tate data all pull back. If $G$ has data $(L,a,b)$, then

$$
G_{R'}=G_{L\otimes_RR',a\otimes1,b\otimes1}.
\tag{10.1}
$$

Schematic closure also commutes with this base change. The proof is worth recalling: the saturated quotient defining the closure is torsion-free, flat tensor product preserves its injection into the generic quotient, and uniqueness identifies the result with closure after scalar extension.

Let $d=e(K'/K)$ be the relative ramification index, normalized so that

$$
v_{K'}(x)=d\,v_K(x)
\qquad(x\in K^\times).
$$

Then

$$
e'=v_{K'}(p)=de.
\tag{10.2}
$$

If $r=v_K(a)$, the base-changed exponent is

$$
r'=v_{K'}(a)=dr.
\tag{10.3}
$$

Thus the normalized ratio

$$
\frac r e
\tag{10.4}
$$

is unchanged. Endpoint and intermediate special-fiber types are preserved under extensions of DVRs, although residue-field twists may split.

### 10.2 Unramified and ramified scalar extension

If $R'/R$ is unramified, then $d=1$, so $e$ and every exponent $r$ are unchanged. The residue extension may extract a $(p-1)$st root of the unit part of $a$, removing an unramified twist while leaving the valuation type fixed.

If $R'/R$ is ramified of index $d$, both $e$ and $r$ are multiplied by $d$. A model that was an endpoint stays an endpoint; an intermediate model stays intermediate. However, the larger interval $0\le s\le de$ contains exponents not divisible by $d$. Those additional order-$p$ models over $R'$ need not descend to $R$.

This observation prevents a common reversal. Base change sends the downstairs list into the upstairs list, but does not make it surjective. For example, an unramified base with $e=1$ has only endpoint models. After a ramified extension of degree $d>1$, intermediate models exist upstairs. Most are new integral lattices rather than scalar extensions of downstairs groups.

The inertia formula is compatible with (10.3). If $\theta'$ is normalized for $K'$ and $I_{K'}\to I_K$ is restriction, then the restriction of $\theta^r$ equals $(\theta')^{dr}$ with the chosen normalization. Equivalently, both characters describe the action on the same root of $a$ while the normalized valuation scale changes by $d$.

### 10.3 Completion and henselization

Let $R$ be a DVR that is not complete. Passing to its henselization $R^h$ or completion $\widehat R$ is faithfully flat, preserves the residue field, and has ramification index one. Consequently finite projectivity, exactness, rank, and isomorphisms can be checked after either passage when the objects and maps already descend.

For an order-$p$ group, the exponent and type are unchanged. Oort--Tate parameters over $R$ pull back to the same valuation pair over $R^h$ and $\widehat R$. Conversely, a pair over the completion descends only if its unit class and weight line carry effective descent data. Faithful flatness detects an isomorphism between two descended objects; it does not assert that every completed object descends.

The connected--étale sequence is naturally henselian. Over a merely local nonhenselian ring, special-fiber idempotents need not lift. Once one passes to $R^h$, the sequence exists; its pullback to $\widehat R$ is the completed sequence. This is why completion is a convenient place to calculate but henselization is already sufficient for the structural theorem.

### 10.4 Descent data rather than generic descent

Suppose $R'/R$ is faithfully flat and $G'/R'$ is finite flat. To descend $G'$, one needs an isomorphism between its two pullbacks to $R'\otimes_RR'$ satisfying the cocycle condition. For an Oort--Tate group this means compatible descent of the line $L'$, its two sections, and their product relation.

Descent of the generic character is weaker. A character of $\Gamma_{K'}$ may extend to $\Gamma_K$ while the integral exponent or unit class has no compatible descent. Likewise, a semilinear action on the generic coordinate algebra need not preserve the chosen integral Hopf lattice.

When descent data do exist, effectiveness follows from finite locally free descent: the coordinate algebra, multiplication, coproduct, counit, and antipode all descend, and the Hopf identities descend by faithful flatness. The resulting downstairs group is unique up to unique isomorphism. Thus the correct implication is

$$
\text{integral descent datum}
\Longrightarrow\text{descent of the group}
\Longrightarrow\text{descent of the generic character},
$$

and neither reverse implication is formal.

### 10.5 An explicit unramified descent criterion

Let $R'/R$ be a finite unramified Galois extension of henselian DVRs with group $\Delta$. Suppose an order-$p$ group over $R'$ has a trivialized datum $(a',b')$. An isomorphism from its $\sigma$-pullback to itself must, by (7.4), be given by a unit $u_\sigma\in R'^\times$ satisfying

$$
\sigma(a')=u_\sigma^{p-1}a',
\qquad
\sigma(b')=u_\sigma^{1-p}b'.
\tag{10.5}
$$

These isomorphisms form descent data exactly when

$$
u_{\sigma\tau}=u_\sigma\,\sigma(u_\tau)
\qquad(\sigma,\tau\in\Delta).
\tag{10.6}
$$

**Proposition 10.1.** The group $G_{a',b'}/R'$ descends to $R$ if and only if, after allowing the weight-one line to be nontrivial, there are units $u_\sigma$ satisfying (10.5) and (10.6). The descended line is the rank-one projective module obtained by semilinear descent from the action $x\mapsto u_\sigma x$, and the sections $a',b'$ descend to complementary sections on that line.

**Proof.** If the group descends, its canonical pullback isomorphisms commute with scalar weights, so their action on the weight-one line has the displayed form. Compatibility with the relation and coproduct gives (10.5), and the descent cocycle gives (10.6).

Conversely, (10.6) is a semilinear descent datum on the free weight-one line over $R'$. Faithfully flat descent produces an invertible $R$-module $L$. Equations (10.5) say exactly that $a'$ and $b'$ are invariant sections of $L^{1-p}$ and $L^{p-1}$; their product descends to $w_p$. The Oort--Tate construction over $R$ then pulls back to $G_{a',b'}$. $\square$

The cocycle is essential. Separate isomorphisms between Galois conjugates prove only that the isomorphism class is invariant; without (10.6) they need not glue to a descended object. In local applications the line $L$ is ultimately free, but its descent presentation can still carry the unramified twisting character.

## 11. Arithmetic examples

### 11.1 The constant and multiplicative endpoints

The split étale endpoint is obtained from

$$
(a,b)=(1,w_p).
\tag{11.1}
$$

Its coordinate polynomial $x^p-x$ is étale, and the scalar action identifies its roots with $\mathbf F_p$; hence it is the constant group $\underline{\mathbf Z/p\mathbf Z}$. The self-dual normalization gives

$$
G_{1,w_p}^D=G_{w_p,1}\simeq\mu_p.
\tag{11.2}
$$

These formulas should be read up to the fixed universal coordinate normalization. Their invariant content is that the constant and multiplicative endpoints are dual, their exponent pair is $(0,e)$ and $(e,0)$, and their generic characters are $1$ and $\overline\chi_p$.

Twisting (11.1) by a unit class gives a finite étale order-$p$ group with an unramified character. Duality gives a multiplicative-type form with generic character equal to the cyclotomic character times the inverse unramified twist. After strict henselization both forms split as in (11.2).

Over $\mathbf Z_p$ there are no other types. This is the valuation explanation behind many uniqueness arguments at an unramified prime: an order-$p$ closure whose generic inertia is trivial must be the étale endpoint, while one whose inertia is cyclotomic must be the multiplicative endpoint, provided the two characters are distinct and the relevant line is defined.

### 11.2 An intermediate ramified model

Let $R$ have $e=v(p)\ge2$, and write

$$
w_p=\epsilon\pi^e,
\qquad \epsilon\in R^\times.
$$

For any $r$ with $0<r<e$, take

$$
a=\pi^r,
\qquad
b=\epsilon\pi^{e-r}.
\tag{11.3}
$$

Then $G_{a,b}$ is connected on the special fiber, and so is its dual. After algebraic closure of the residue field each becomes $\alpha_p$. Nevertheless the generic fiber is étale and carries the tame character

$$
\theta^r.
$$

This example exhibits three layers that should not be conflated:

$$
\begin{array}{c|c}
\text{generic scheme}&\text{étale of order }p\\
\text{generic Galois module}&\text{one-dimensional character }\theta^r\\
\text{special scheme}&\text{local-local of order }p.
\end{array}
$$

If $e\ge p-1$, the exponents $r$ and $r+p-1$ can produce the same tame inertia character while giving different valuation depths and, generally, nonisomorphic integral groups. Generic inertia is therefore not a complete invariant of the model.

For a concrete case, take a totally ramified quadratic extension of $\mathbf Q_p$ with $p$ odd, so $e=2$. The exponent $r=1$ is the unique intermediate valuation. Its dual also has exponent one. Whether it is actually self-dual depends on the unit equation $b/a\in R^{\times(p-1)}$, not merely on the midpoint valuation.

### 11.3 The dyadic family

The prime $2$ exposes model ambiguity with almost no Galois representation theory. Since

$$
\mathbf F_2^\times=1,
$$

every one-dimensional $\mathbf F_2$-character is trivial. Thus every order-two generic étale group over a characteristic-zero field is constant.

Let $R$ be a ramified dyadic DVR with $e=v(2)>1$. For each $0\le r\le e$, choose

$$
a=\pi^r,
\qquad b=2/a
$$

after absorbing a unit into one parameter. Formula (6.13) gives a finite-flat group

$$
G_{a,b}=\operatorname{Spec}R[x]/(x^2-a x)
$$

with law

$$
x\star y=x+y-bxy.
$$

All these groups have the same constant generic group, but their integral exponents run from $0$ to $e$. The endpoints are constant and multiplicative; the intermediate groups have local-local special fiber $\alpha_2$. Hence the generic representation forgets the entire interior of the interval.

Over an unramified dyadic base, $e=1$, so only the two endpoints remain. They still have the same generic $\mathbf F_2$-character. Therefore character distinction cannot select a canonical endpoint at $2$; one needs a specified ambient closure or other integral geometry.

### 11.4 Torsion on elliptic schemes

Let $E/R$ be an elliptic scheme. Multiplication by $p$ is finite flat of degree $p^2$, so $E[p]$ is finite flat of height two. Its connected--étale sequence reflects the reduction type.

If the special fiber is ordinary over an algebraically closed field, there is an exact sequence

$$
0\longrightarrow\mu_p\longrightarrow E_k[p]
\longrightarrow\underline{\mathbf Z/p\mathbf Z}\longrightarrow0.
\tag{11.4}
$$

Over a henselian base, the connected subgroup and étale quotient lift canonically, although the resulting integral sequence need not split. A principal polarization identifies $E[p]^D$ with $E[p]$, so the two endpoint directions are dual.

Suppose in addition that $R$ is unramified. Any finite-flat order-$p$ subgroup of $E[p]$ must be étale or multiplicative by Corollary 7.4. A Galois-stable generic line closes to one of those types. When its character is unramified, it closes to the étale direction; when its character is cyclotomic, it closes to the multiplicative direction, subject to the stated unit twists.

If the special fiber is supersingular, $E_k[p]$ is local-local of height two. Its Frobenius kernel is an $\alpha_p$ subgroup of the special fiber, but over an unramified mixed-characteristic base there is no local-local height-one group to lift it. Thus a special-fiber subgroup need not lift to an integral subgroup. This does not contradict closure: closure begins with a subgroup of the **generic** fiber, while the Frobenius kernel exists only in the special fiber unless extra structure supplies a lift.

This example also shows why height two is not merely two independent copies of height one. The ambient group can be local-local even when the base admits no local-local order-$p$ group, because it need not possess an integral order-$p$ filtration.

### 11.5 Equal characteristic as a boundary

Let $R=k[[t]]$ have characteristic $p$. The generic fiber of a $p$-group need not be étale, so the generic-character argument of Chapter 5 fails at its first step. The scalar action still exists, but the generic coordinate algebra need not be a regular representation on $p$ geometric points.

For example,

$$
\alpha_p=\operatorname{Spec}R[x]/(x^p)
$$

is connected on both fibers. There are also finite-flat kernels of additive polynomials such as

$$
x^p-t^{p-1}x,
$$

whose generic and special fibers have different étaleness behavior. These groups belong to equal-characteristic additive geometry, not to the mixed-characteristic Kummer dictionary (8.1).

The Oort--Tate relation formally degenerates because $p=0$ and hence $ab=0$. Treating that degenerate equation alone as a classification would lose additional additive possibilities and the generic inseparability issue. The mixed-characteristic hypothesis in Theorem 6.2 is therefore structural, not cosmetic. Over perfect fields themselves, Theorem 4.2 remains the complete rank-$p$ classification; over an equal-characteristic DVR, families between the fibers require a separate analysis.

## 12. The small-height package

### 12.1 A theorem ledger

The results can now be assembled in the order in which they are safely used.

Let $R$ be a henselian mixed-characteristic DVR with perfect residue field, fraction field $K$, and $e=v(p)$.

1. A generic closed subgroup of a fixed finite-flat group has a unique finite-flat schematic closure. Nested generic subgroups close to nested integral subgroups, and represented quotients give exact sequences.

2. Every finite-flat group has a functorial connected--étale sequence. Applying it to the Cartier dual produces the maximal multiplicative subgroup. A finite flat $p$-group therefore has the canonical filtration

$$
0\subset G^{\mathrm{mult}}\subset G^0\subset G
$$

with multiplicative, local-local, and étale subquotients.

3. Every order-$p$ group is killed by $p$ and carries its canonical scalar action. Oort--Tate data $(L,a,b)$ with $a\otimes b=w_p$ classify such groups. Cartier duality sends $(L,a,b)$ to $(L^{-1},b,a)$.

4. Over the DVR, choose a frame and write $ab=w_p$. The exponent

$$
r=v(a),\qquad 0\le r\le e,
$$

is intrinsic. The group is étale for $r=0$, multiplicative for $r=e$, and local-local on the special fiber for $0<r<e$.

5. The generic character is determined by the Kummer class of $a$. With $\overline\chi_p|_I=\theta^e$,

$$
\chi_G|_I=\theta^r,
\qquad
\chi_{G^D}|_I=\theta^{e-r}.
$$

6. Under an extension of DVRs of ramification index $d$, $(e,r)$ becomes $(de,dr)$. Closure, exactness, duality, and type commute with the flat base change. Descent in the reverse direction requires integral descent data.

These statements cover the prime-order local group schemes that occur when torsion on an arithmetic family is examined at the coefficient prime. They also state exactly what is *not* supplied: a general classification of height-two extensions, a rank-$p$ filtration of every higher-height group, or a full equal-characteristic family classification.

### 12.2 A failure atlas

The theory is easiest to reuse when each tempting shortcut is paired with its repair.

| Invalid shortcut | What fails | Correct replacement |
|---|---|---|
| A closed subgroup of a finite-flat group is flat | the coordinate quotient can have base torsion | contract the generic Hopf ideal and prove saturation |
| A generic group has a unique integral model | distinct Hopf lattices can share a generic fiber | fix an ambient model or classify models by Oort--Tate data |
| The connected--étale sequence is a product | the extension need not split | retain it as a faithfully flat exact sequence |
| Connected dualizes to étale | $\alpha_p$ is connected and self-dual | use maximal multiplicative type as the dual of maximal étale quotient |
| The valuation $r$ alone classifies a group | unit classes can give unramified twists | retain $(a,b)$ modulo the rescaling (7.4) |
| The generic character determines $r$ | exponents congruent modulo $p-1$ give the same tame character | retain the integral range $0\le r\le e$ |
| Every height-$h$ group has order-$p$ factors over $R$ | the generic representation may have no stable line | require a Galois-stable flag and close it term by term |
| Endpoint models determine their extensions | torsor and Hopf-lattice equations carry extra data | construct or assume an integral middle model |
| A special-fiber subgroup lifts | it may have no generic antecedent | begin with a generic subgroup and use schematic closure |
| An upstairs model descends with its character | the integral line and sections may lack descent data | descend the full Oort--Tate datum or Hopf algebra |
| The mixed-characteristic formula applies when $p=0$ | the generic fiber can be inseparable | treat equal-characteristic additive geometry separately |

Every repair has a precise algebraic source. Saturation uses that a finite torsion-free module over a DVR is free. Henselianity lifts idempotents. Perfection converts reduced finite fibers into étale fibers. Cartier duality exchanges finite étale and multiplicative type. The Oort--Tate coefficient calculation converts the scalar-weight line into a Hopf algebra. None of these hypotheses can be silently transferred to a different setting.

### 12.3 Conclusion

Finite-flat group schemes of small height form the first setting in which integral torsion can be both flexible and completely controlled. The generic fiber supplies an ordinary one-dimensional Galois character, but the integral model adds a valuation depth and a special-fiber type. Schematic closure places a generic line into a fixed torsion group without adding vertical torsion. The connected--étale sequence separates the unramified quotient, and Cartier duality extracts the complementary multiplicative subgroup, leaving the local-local core.

For order $p$, the scalar action compresses the coordinate algebra to one weight line. The Oort--Tate theorem records that line by complementary sections whose product is a fixed unit multiple of $p$. Over a DVR this becomes the interval

$$
0\le r\le e,
$$

with étale and multiplicative endpoints and local-local interior. The same integer gives the tame inertia exponent, while duality reflects the interval by $r\mapsto e-r$. Unit classes record the unramified twist that valuation alone cannot see.

The resulting package is exact but deliberately not abelian. Subgroups and quotients inherit models from a chosen middle term; arbitrary extensions remain genuine existence problems. Base change preserves the full structure, while descent requires the full integral datum. With those boundaries visible, schematic closure, connected and multiplicative decompositions, Oort--Tate parameters, inertia characters, and Cartier duality fit into one continuous language for residue-characteristic torsion over the local bases of arithmetic geometry.
