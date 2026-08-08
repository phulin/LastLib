# Orders in Quaternion Algebras

## Contents

1. [From a rational algebra to integral arithmetic](#1-from-a-rational-algebra-to-integral-arithmetic)
   - [Why the algebra is not enough](#11-why-the-algebra-is-not-enough)
   - [Full lattices and their local shadows](#12-full-lattices-and-their-local-shadows)
   - [Orders solve the multiplication problem](#13-orders-solve-the-multiplication-problem)
   - [Orders exist, but coordinates can mislead](#14-orders-exist-but-coordinates-can-mislead)
   - [Conjugation transports integral structure](#15-conjugation-transports-integral-structure)
2. [Integrality detected by reduced trace and norm](#2-integrality-detected-by-reduced-trace-and-norm)
   - [Why reduced invariants should be integral](#21-why-reduced-invariants-should-be-integral)
   - [Closure under canonical conjugation](#22-closure-under-canonical-conjugation)
   - [Trace duals and denominators](#23-trace-duals-and-denominators)
   - [A worked matrix calculation](#24-a-worked-matrix-calculation)
3. [Discriminants, indices, and ramification](#3-discriminants-indices-and-ramification)
   - [The determinant that survives a change of basis](#31-the-determinant-that-survives-a-change-of-basis)
   - [The index ideal and the square-index formula](#32-the-index-ideal-and-the-square-index-formula)
   - [Local discriminant exponents](#33-local-discriminant-exponents)
   - [Maximality detected by discriminant](#34-maximality-detected-by-discriminant)
   - [Lipschitz and Hurwitz discriminants](#35-lipschitz-and-hurwitz-discriminants)
4. [Localization, completion, and reconstruction](#4-localization-completion-and-reconstruction)
   - [Why integral questions are local](#41-why-integral-questions-are-local)
   - [Inclusion and equality criteria](#42-inclusion-and-equality-criteria)
   - [Reconstructing a lattice from local data](#43-reconstructing-a-lattice-from-local-data)
   - [Indices and discriminants localize](#44-indices-and-discriminants-localize)
5. [Maximal orders](#5-maximal-orders)
   - [Existence by controlling overorders](#51-existence-by-controlling-overorders)
   - [Maximality is local](#52-maximality-is-local)
   - [Split maximal orders as endomorphism rings](#53-split-maximal-orders-as-endomorphism-rings)
   - [The division case has one maximal order](#54-the-division-case-has-one-maximal-order)
   - [Local conjugacy does not imply global conjugacy](#55-local-conjugacy-does-not-imply-global-conjugacy)
6. [The two explicit local models](#6-the-two-explicit-local-models)
   - [Split orders from lattice chains](#61-split-orders-from-lattice-chains)
   - [The elementary Bruhat--Tits tree](#62-the-elementary-bruhat--tits-tree)
   - [Neighboring maximal orders](#63-neighboring-maximal-orders)
   - [Discriminant of the standard intersection](#64-discriminant-of-the-standard-intersection)
   - [The division order in cyclic coordinates](#65-the-division-order-in-cyclic-coordinates)
   - [Why there is no division-tree level](#66-why-there-is-no-division-tree-level)
7. [Eichler orders and level ideals](#7-eichler-orders-and-level-ideals)
   - [Why intersections are the right next class](#71-why-intersections-are-the-right-next-class)
   - [The level ideal](#72-the-level-ideal)
   - [Reduced discriminant equals ramification times level](#73-reduced-discriminant-equals-ramification-times-level)
   - [Squarefree and deeper level](#74-squarefree-and-deeper-level)
   - [Global conjugacy and the genus of an Eichler order](#75-global-conjugacy-and-the-genus-of-an-eichler-order)
   - [A rational matrix order](#76-a-rational-matrix-order)
8. [One-sided and fractional ideals](#8-one-sided-and-fractional-ideals)
   - [Why ideals need two orders](#81-why-ideals-need-two-orders)
   - [Bimodule notation and variance](#82-bimodule-notation-and-variance)
   - [Principal one-sided ideals](#83-principal-one-sided-ideals)
   - [Localization of ideals and their orders](#84-localization-of-ideals-and-their-orders)
   - [A warning from nonmaximal orders](#85-a-warning-from-nonmaximal-orders)
9. [Invertibility and reduced norm ideals](#9-invertibility-and-reduced-norm-ideals)
   - [The inverse ideal](#91-the-inverse-ideal)
   - [Local principality is the usable criterion](#92-local-principality-is-the-usable-criterion)
   - [The reduced norm ideal](#93-the-reduced-norm-ideal)
   - [Norm under multiplication](#94-norm-under-multiplication)
   - [Norm, conjugation, and equivalence](#95-norm-conjugation-and-equivalence)
10. [Ideal classes before adeles](#10-ideal-classes-before-adeles)
    - [One-sided equivalence](#101-one-sided-equivalence)
    - [Locally principal does not mean principal](#102-locally-principal-does-not-mean-principal)
    - [The matrix algebra and Morita's picture](#103-the-matrix-algebra-and-moritas-picture)
    - [Why finiteness is plausible](#104-why-finiteness-is-plausible)
11. [Finite adeles of a quaternion algebra](#11-finite-adeles-of-a-quaternion-algebra)
    - [The restricted product attached to integrality](#111-the-restricted-product-attached-to-integrality)
    - [Completion of an order](#112-completion-of-an-order)
    - [Adelic lattices and intersection](#113-adelic-lattices-and-intersection)
    - [Adelic reduced norm](#114-adelic-reduced-norm)
    - [Conjugating compact opens](#115-conjugating-compact-opens)
12. [Ideal classes as double cosets](#12-ideal-classes-as-double-cosets)
    - [The statement and its conventions](#121-the-statement-and-its-conventions)
    - [Well-definedness](#122-well-definedness)
    - [Constructing the inverse](#123-constructing-the-inverse)
    - [Proving the maps are inverse](#124-proving-the-maps-are-inverse)
    - [Stabilizers and left orders](#125-stabilizers-and-left-orders)
13. [Finiteness of the class set](#13-finiteness-of-the-class-set)
    - [The general finiteness theorem](#131-the-general-finiteness-theorem)
    - [Why definiteness gives a sharper compactness proof](#132-why-definiteness-gives-a-sharper-compactness-proof)
    - [Stabilizers in the definite case](#133-stabilizers-in-the-definite-case)
    - [What fails without definiteness](#134-what-fails-without-definiteness)
14. [Eichler compact opens and concrete level](#14-eichler-compact-opens-and-concrete-level)
    - [From a local order to a local group](#141-from-a-local-order-to-a-local-group)
    - [The global Eichler level subgroup](#142-the-global-eichler-level-subgroup)
    - [What the unit group remembers](#143-what-the-unit-group-remembers)
    - [Change of level](#144-change-of-level)
15. [Explicit arithmetic over $\mathbf Q$](#15-explicit-arithmetic-over-mathbf-q)
    - [The maximal matrix order has one class](#151-the-maximal-matrix-order-has-one-class)
    - [Matrix Eichler level $N$](#152-matrix-eichler-level-n)
    - [The Hurwitz maximal order](#153-the-hurwitz-maximal-order)
    - [The Hurwitz class set](#154-the-hurwitz-class-set)
    - [Adding odd Eichler level to the definite algebra](#155-adding-odd-eichler-level-to-the-definite-algebra)
16. [The integral--adelic dictionary](#16-the-integral--adelic-dictionary)
    - [One table of translations](#161-one-table-of-translations)
    - [The discriminant dictionary](#162-the-discriminant-dictionary)
    - [The ideal dictionary](#163-the-ideal-dictionary)
    - [The finite input for the next book](#164-the-finite-input-for-the-next-book)
    - [Conclusion](#165-conclusion)

## 1. From a rational algebra to integral arithmetic

### 1.1 Why the algebra is not enough

Book 33 classified a quaternion algebra $B$ over a number field $F$ by its local splitting behavior. That classification answers which ambient algebra we have, but it does not yet supply a notion of congruence, denominator, or level inside $B$. All of those are integral questions. Just as the field $F$ acquires arithmetic texture only after one singles out its ring of integers $R=\mathcal O_F$, the four-dimensional $F$-vector space $B$ acquires arithmetic texture only after one singles out a full $R$-lattice compatible with multiplication.

There is no canonical choice in general. Even $M_2(F)$ contains many nonconjugate-looking integral subrings, and one fixed quaternion algebra supports levels at arbitrarily large ideals. This variability is useful: later, a compact open subgroup of the finite adelic group will encode the chosen integral structure. The present book develops the algebraic side of that dictionary.

Throughout, $F$ is a number field, $R=\mathcal O_F$, and $B$ is a quaternion algebra over $F$. A finite place $v$ corresponds to a prime $\mathfrak p_v$ of $R$. We write

$$
F_v,\qquad R_v,\qquad \mathfrak p_vR_v=(\pi_v),\qquad B_v=B\otimes_FF_v
$$

for the completion, its valuation ring, a chosen uniformizer, and the completed algebra. Reduced trace, reduced norm, and canonical conjugation are denoted by $\operatorname{Trd}$, $\operatorname{Nrd}$, and $x\mapsto\bar x$. They are the degree-two invariants of Book 33, not the trace and determinant of the four-dimensional left regular representation.

### 1.2 Full lattices and their local shadows

Before requiring multiplication, we isolate the correct additive size. An **$R$-lattice** in a finite-dimensional $F$-vector space $V$ is a finitely generated torsion-free $R$-submodule $L\subset V$ such that

$$
F L=V.
$$

It is **full** when this last equality holds; in this book “lattice in $B$” always means full unless explicitly qualified. Since $R$ is Dedekind, such an $L$ is projective of rank $\dim_FV$. It need not have a global basis when the class group of $R$ is nontrivial. Locally, however,

$$
L_v=L\otimes_RR_v
$$

is free of the expected rank. This is why basis calculations will often be made over $R_v$ and then reassembled into ideal statements over $R$.

Two elementary facts will be used constantly. First, any two full lattices are commensurable: for some nonzero $a,b\in R$,

$$
aL\subset M\subset b^{-1}L.
$$

Second, a lattice is recovered from all of its localizations:

$$
L=\{x\in V:x\in L_v\text{ for every finite }v\}
=V\cap\prod_{v<\infty}L_v.
$$

The intersection is taken in the finite adelic vector space. At almost every $v$, any two fixed lattices have the same localization, so the displayed condition is genuinely finite in content for a fixed $x$.

### 1.3 Orders solve the multiplication problem

A lattice alone has no reason to remember the algebra product. The smallest condition that makes integral multiplication meaningful is closure under multiplication together with the same identity as $B$.

An **$R$-order** in $B$ is a full $R$-lattice $\mathcal O\subset B$ such that

$$
1\in\mathcal O,
\qquad
\mathcal O\mathcal O\subset\mathcal O.
$$

Thus $\mathcal O$ is a unital subring of $B$ whose scalar extension to $F$ is all of $B$. The word “unital” matters. The lattice $2M_2(\mathbf Z)$ is closed under multiplication, but it does not contain the identity and is not an order in $M_2(\mathbf Q)$. Likewise, the upper triangular matrices in $M_2(\mathbf Z)$ form a unital ring but span only a three-dimensional subspace, so they are not an order.

The standard example is

$$
M_2(R)\subset M_2(F).
$$

More generally, if $L$ is a rank-two projective $R$-lattice in $F^2$, then

$$
\operatorname{End}_R(L)=\{g\in M_2(F):gL\subset L\}
$$

is an order. This endomorphism description will become the local model for every maximal order in a split quaternion algebra.

### 1.4 Orders exist, but coordinates can mislead

Every quaternion algebra over $F$ contains an order. To see the mechanism, choose an $F$-basis $1,e_2,e_3,e_4$ and clear the finitely many denominators in its multiplication table. For a sufficiently divisible nonzero ideal $\mathfrak a\subset R$, the lattice

$$
R\cdot1+\mathfrak a e_2+\mathfrak a e_3+\mathfrak a e_4
$$

is closed under multiplication. The coefficients of products involving two nonscalar basis vectors gain enough factors from $\mathfrak a$ to absorb every denominator. This proves existence without pretending that the order is canonical.

For a presented algebra $B=(a,b)_F$ with $a,b\in R$, the obvious lattice

$$
R[1,i,j,ij]=R+Ri+Rj+Rij
$$

is an order. It is often not maximal. In Hamilton's rational algebra, the Lipschitz order $\mathbf Z[1,i,j,ij]$ sits properly inside the Hurwitz order obtained by adjoining $(1+i+j+ij)/2$. Thus “integral-looking coefficients” depend on the chosen basis; maximality is an intrinsic containment condition, not a visual property of a presentation.

### 1.5 Conjugation transports integral structure

For $b\in B^\times$, the conjugate

$$
b\mathcal O b^{-1}
$$

is again an order. Reduced trace and norm are invariant under this operation. Conjugate orders represent the same integral structure viewed in a different $B$-coordinate system.

Scalar multiplication behaves differently. If $a\in F^\times$, the lattice $a\mathcal O$ is generally not an order: it contains $1$ only in special cases and multiplication sends it into $a^2\mathcal O$. Fractional scaling belongs naturally to ideal theory, not to the theory of unital orders. Keeping conjugation and scaling separate prevents several later errors.

## 2. Integrality detected by reduced trace and norm

### 2.1 Why reduced invariants should be integral

An order is finite over $R$, so multiplication by one of its elements is an integral linear operation. This should force a monic polynomial with coefficients in $R$. The subtlety is that left multiplication acts on a rank-four module, whereas the quaternionic characteristic polynomial has degree two. The reduced invariants bridge those two viewpoints.

An element $x\in B$ is **integral over $R$** if it satisfies a monic polynomial in $R[T]$. Since $R$ is integrally closed and the reduced characteristic polynomial is

$$
P_x(T)=T^2-\operatorname{Trd}(x)T+\operatorname{Nrd}(x),
$$

we have the precise degree-two test.

**Proposition 2.1 (integrality criterion).** An element $x\in B$ is integral over $R$ if and only if

$$
\operatorname{Trd}(x)\in R
\quad\text{and}\quad
\operatorname{Nrd}(x)\in R.
$$

**Proof strategy.** One direction is immediate from the reduced characteristic polynomial. For the other, compare the minimal polynomial of $x$ with $P_x$ and use integral closedness of $R$.

**Proof.** If the two reduced invariants lie in $R$, Cayley--Hamilton gives a monic quadratic equation over $R$. Conversely, suppose $x$ is integral. The commutative algebra $F[x]$ has dimension at most two. If $x\in F$, integrality gives $x\in R$, whence $\operatorname{Trd}(x)=2x$ and $\operatorname{Nrd}(x)=x^2$ lie in $R$. If $[F[x]:F]=2$, the reduced characteristic polynomial is the minimal polynomial of $x$ over $F$. The coefficients of that polynomial are integral over $R$ because its root is integral, and they lie in $F$; since $R$ is integrally closed, they lie in $R$. $\square$

Consequently every element of an order has integral reduced trace and norm. One can also see this by letting $x$ act on the finite $R$-module $\mathcal O$ and observing that the degree-four characteristic polynomial is $P_x(T)^2$.

### 2.2 Closure under canonical conjugation

The integrality of trace has a useful structural consequence. For $x\in\mathcal O$,

$$
\bar x=\operatorname{Trd}(x)-x\in\mathcal O.
$$

Thus every order is stable under canonical conjugation. It follows that the trace pairings

$$
(x,y)\longmapsto\operatorname{Trd}(xy)
\quad\text{and}\quad
(x,y)\longmapsto\operatorname{Trd}(x\bar y)
$$

both take $\mathcal O\times\mathcal O$ into $R$. Their determinants differ only by the determinant of conjugation, hence by a unit locally. We use the first pairing for discriminants because it interacts directly with change of basis.

The converse “every full lattice of integral elements containing $1$ is an order” is false. In $M_2(\mathbf Q)$, put $H=E_{11}-E_{22}$ and let

$$
L=\mathbf ZI+\mathbf Z(2E_{12})
+\mathbf Z\left(\frac12E_{21}\right)+\mathbf ZH.
$$

An element $aI+2bE_{12}+(c/2)E_{21}+dH$ has trace $2a$ and determinant

$$
a^2-d^2-bc,
$$

so every element of $L$ is integral by Proposition 2.1. Nevertheless,

$$
\left(\frac12E_{21}\right)(2E_{12})=E_{22}
=\frac{I-H}{2}\notin L.
$$

Thus $L$ is not closed under multiplication. Integrality is a property of individual elements, while an order requires one common lattice stable under all products.

### 2.3 Trace duals and denominators

The trace pairing on $B$ is nondegenerate because $B$ is separable over $F$. For a lattice $L\subset B$, define its **trace dual**

$$
L^\#=\{x\in B:\operatorname{Trd}(xL)\subset R\}.
$$

Then $L^\#$ is again a full lattice and $(L^\#)^\#=L$. If $L=\mathcal O$ is an order, integrality of traces gives

$$
\mathcal O\subset\mathcal O^\#.
$$

The quotient $\mathcal O^\#/\mathcal O$ measures the failure of the trace pairing to be unimodular. Its size is governed by the discriminant. This is the noncommutative analogue of the codifferent of a number field, although no assertion is being made that the trace dual is a two-sided invertible ideal for an arbitrary order.

Locally, if $e_1,\dots,e_4$ is an $R_v$-basis and $G=(\operatorname{Trd}(e_re_s))$, the dual basis is obtained using $G^{-1}$. Hence

$$
\operatorname{length}_{R_v}(\mathcal O_v^\#/\mathcal O_v)
=v(\det G).
$$

This calculation will make the discriminant an efficient measure of how far an order lies from being maximal.

### 2.4 A worked matrix calculation

Take $\mathcal M=M_2(R)$ with ordered basis

$$
E_{11},E_{12},E_{21},E_{22}.
$$

Because reduced trace is ordinary matrix trace, the Gram matrix of $\operatorname{Trd}(xy)$ is

$$
\begin{pmatrix}
1&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix},
$$

whose determinant is $-1$. Thus $M_2(R)$ has unit discriminant. Notice that the trace of the identity is $2$, but the pairing is nevertheless unimodular: using the matrix units rather than $1$ and three traceless elements reveals the integral structure correctly.

## 3. Discriminants, indices, and ramification

### 3.1 The determinant that survives a change of basis

We need an invariant that detects when an order has unnecessary denominators or admits a proper enlargement. If $\mathcal O$ is free with basis $e=(e_1,\dots,e_4)$, define the basis discriminant

$$
\operatorname{disc}(e)
=\det\bigl(\operatorname{Trd}(e_re_s)\bigr)_{1\le r,s\le4}\in F^\times.
$$

If $e'=eA$ for $A\in\operatorname{GL}_4(F)$, then

$$
\operatorname{disc}(e')=(\det A)^2\operatorname{disc}(e).
$$

The square is decisive. It means that although a generator depends on a basis, the fractional ideal generated locally by these determinants glues globally. The **discriminant ideal** of an order is

$$
\operatorname{disc}(\mathcal O)
=\prod_{v<\infty}\mathfrak p_v^{v(\det G_v)},
$$

where $G_v$ is the trace Gram matrix of any $R_v$-basis of $\mathcal O_v$. Only finitely many exponents are nonzero, and change of local basis by $\operatorname{GL}_4(R_v)$ does not change them.

For a quaternion order every local exponent $v(\operatorname{disc}(\mathcal O))$ is even. This can be checked without assuming that $2$ is a unit. Choose a presentation $B=(a,b)_F$ and use the $F$-basis $1,i,j,ij$. Its trace Gram matrix is diagonal with entries

$$
2,\quad 2a,\quad 2b,\quad -2ab,
$$

so its determinant is $-16a^2b^2$, whose valuation is even at every finite place. Any local basis of $\mathcal O_v$ differs from this $F_v$-basis by a matrix $A\in\operatorname{GL}_4(F_v)$, and its determinant is multiplied by $(\det A)^2$. Its valuation is therefore still even. Integrality of the trace pairing makes it nonnegative. We may consequently define the **reduced discriminant of the order** as the unique integral ideal $\mathfrak d(\mathcal O)$ satisfying

$$
\operatorname{disc}(\mathcal O)=\mathfrak d(\mathcal O)^2.
$$

This notation must be distinguished from $\mathfrak d(B)$, the squarefree product of finite places where the algebra is division.

### 3.2 The index ideal and the square-index formula

If $L\subset M$ are full $R$-lattices, their quotient is finite. Define the **index ideal** $[M:L]$ by

$$
v([M:L])=\operatorname{length}_{R_v}(M_v/L_v).
$$

Thus $[M:L]$ is integral; over $\mathbf Z$ it is the ideal generated by the ordinary positive index. This orientation places the larger lattice first.

**Proposition 3.1 (index--discriminant formula).** If $\mathcal O\subset\mathcal O'$ are orders, then

$$
\operatorname{disc}(\mathcal O)
=[\mathcal O':\mathcal O]^2\operatorname{disc}(\mathcal O'),
$$

and therefore

$$
\mathfrak d(\mathcal O)
=[\mathcal O':\mathcal O]\mathfrak d(\mathcal O').
$$

**Proof strategy.** The assertion is local. Put a basis of the smaller lattice into elementary-divisor form relative to a basis of the larger one, and apply the change-of-basis square.

**Proof.** Over $R_v$, choose a basis $e_1,\dots,e_4$ of $\mathcal O'_v$ such that $\pi_v^{a_1}e_1,\dots,\pi_v^{a_4}e_4$ is a basis of $\mathcal O_v$. The change matrix has determinant $\pi_v^{a_1+\cdots+a_4}$, while

$$
\operatorname{length}(\mathcal O'_v/\mathcal O_v)=a_1+\cdots+a_4.
$$

Taking determinants of the two Gram matrices gives twice that valuation. The local identities glue. $\square$

Thus enlarging an order decreases its reduced discriminant by exactly the index. The formula is both a calculation tool and a termination principle for constructing maximal orders.

### 3.3 Local discriminant exponents

Let $K$ be a nonarchimedean local field with valuation ring $A$, uniformizer $\pi$, and quaternion algebra $C/K$. For an $A$-order $\Lambda$, write

$$
\delta(\Lambda)=\frac12v(\operatorname{disc}(\Lambda)),
$$

so that the local reduced discriminant is $(\pi^{\delta(\Lambda)})$.

Two benchmark computations govern the global theory:

$$
\min_\Lambda\delta(\Lambda)=
\begin{cases}
0,&C\cong M_2(K),\\
1,&C\text{ is division}.
\end{cases}
$$

In the split case $M_2(A)$ realizes exponent zero, as Section 2.4 computed. In the division case the maximal order has discriminant $\pi^2$ and reduced discriminant $\pi$. A proof of the latter will follow from the explicit unramified quadratic model in Chapter 6.

It follows already that every global order satisfies

$$
\mathfrak d(B)\mid\mathfrak d(\mathcal O).
$$

At a ramified finite place, one factor of $\mathfrak p_v$ is forced by the algebra itself. Any additional exponent records nonmaximal integral structure. At a split place, every exponent comes from the order.

### 3.4 Maximality detected by discriminant

An order is **maximal** if it is not properly contained in any other $R$-order in $B$. We will prove existence and the local criterion in Chapter 5. Combining those results with the local minima gives the fundamental discriminant characterization:

**Theorem 3.2.** For an order $\mathcal O\subset B$, the following are equivalent:

1. $\mathcal O$ is maximal;
2. $\mathcal O_v$ is maximal for every finite $v$;
3. $\mathfrak d(\mathcal O)=\mathfrak d(B)$.

The theorem explains the terminology “reduced discriminant.” The rank-four trace determinant of a maximal order is $\mathfrak d(B)^2$, while its square root recovers exactly the algebra ramification ideal introduced in Book 33.

One must not reverse the conclusion for arbitrary subrings that are not full lattices, nor infer that every order with squarefree reduced discriminant is maximal. If $B$ is split at $\mathfrak p$ and an order has local reduced exponent one there, its reduced discriminant can still be squarefree while the order is not maximal. Such an order is the first Eichler level.

### 3.5 Lipschitz and Hurwitz discriminants

Let $B=(-1,-1)_{\mathbf Q}$ with $k=ij$. For the Lipschitz basis $1,i,j,k$, the trace Gram matrix is diagonal:

$$
\operatorname{diag}(2,-2,-2,-2).
$$

Its determinant is $-16$. Hence

$$
\operatorname{disc}(\mathcal L)=(16),
\qquad
\mathfrak d(\mathcal L)=(4).
$$

Set

$$
\omega=\frac{1+i+j+k}{2},
\qquad
\mathcal H=\mathbf Z+\mathbf Zi+\mathbf Zj+\mathbf Z\omega.
$$

The relations $\omega^2=\omega-1$ and the products with $i,j$ show that $\mathcal H$ is an order. It contains $\mathcal L$ with index two. The index formula gives

$$
\operatorname{disc}(\mathcal H)=(4),
\qquad
\mathfrak d(\mathcal H)=(2).
$$

Book 33 found $\mathfrak d(B)=(2)$, so Theorem 3.2 shows that $\mathcal H$ is maximal and $\mathcal L$ is not. This example cleanly separates the discriminant of a presentation lattice, the reduced discriminant of an order, and the ramification discriminant of the algebra.

## 4. Localization, completion, and reconstruction

### 4.1 Why integral questions are local

Containment of lattices is controlled prime by prime. Multiplication also localizes, so an order has a local order at every finite place. This permits explicit DVR calculations without losing global information, provided we state the reconstruction step rather than silently assuming it.

For a prime $\mathfrak p$ let $R_{(\mathfrak p)}$ be the localization and $F_{\mathfrak p}^{\mathrm{loc}}$ its fraction field. Completion then gives $R_v$ and $F_v$. We mostly use the completed notation

$$
\mathcal O_v=\mathcal O\otimes_RR_v\subset B_v.
$$

Because $R_v$ is faithfully flat over $R_{(\mathfrak p)}$, inclusions and equalities among finite lattices may be checked after completion. Completion adds topology and enables the classification of local quaternion algebras; it does not erase finite-length integral data.

### 4.2 Inclusion and equality criteria

**Proposition 4.1 (local--global lattice criterion).** Let $L,M$ be full lattices in a finite-dimensional $F$-vector space. Then

$$
L\subset M
\quad\Longleftrightarrow\quad
L_v\subset M_v\text{ for every finite }v.
$$

Consequently $L=M$ if and only if $L_v=M_v$ for every finite $v$.

**Proof strategy.** The forward implication is formal. For the reverse implication, detect a nonzero class in the finite torsion module $(L+M)/M$ at one prime of its support.

**Proof.** If $L\not\subset M$, then $(L+M)/M$ is a nonzero finite $R$-module. It has a prime $\mathfrak p$ in its support, so localization, and hence completion, at $\mathfrak p$ remains nonzero. Thus $L_v\not\subset M_v$. The equality statement follows by applying inclusion in both directions. $\square$

For orders this immediately yields

$$
\mathcal O\subset\mathcal O'
\Longleftrightarrow
\mathcal O_v\subset\mathcal O'_v\text{ for all }v<\infty.
$$

It also proves that two globally nonconjugate orders can still be locally conjugate everywhere: equality is detected by fixed local embeddings into $B_v$, whereas local conjugacy permits a different conjugating element at each place.

### 4.3 Reconstructing a lattice from local data

Suppose for each finite $v$ we are given an $R_v$-lattice $L_v\subset B_v$, and suppose $L_v=L_v^0$ for almost every $v$, where $L^0\subset B$ is one fixed global lattice. Define

$$
L=B\cap\prod_{v<\infty}L_v
$$

inside $B\otimes_F\mathbf A_{F,f}$. Then $L$ is a full global lattice and its completion at every $v$ is the prescribed $L_v$. This is the lattice patching principle.

The proof reduces to simultaneous approximation in $F$ after choosing a basis of $B$. Only finitely many coordinates differ from $L^0_v$; weak approximation supplies global vectors meeting those local conditions, and the intersection description supplies finite generation. If every $L_v$ contains $1$ and is closed under multiplication, the reconstructed lattice is an order, since these properties can be checked in every completion.

This theorem is the precise foundation for phrases such as “choose an order with these local shapes.” The almost-everywhere reference lattice is essential. An arbitrary family of ever-growing denominators would not define a lattice.

### 4.4 Indices and discriminants localize

For $L\subset M$,

$$
[M:L]=\prod_{v<\infty}\mathfrak p_v^{\operatorname{length}_{R_v}(M_v/L_v)}.
$$

Likewise,

$$
\mathfrak d(\mathcal O)R_v=\mathfrak d(\mathcal O_v),
$$

where the right side denotes the principal local ideal determined by the trace Gram determinant. Conjugation by $b\in B^\times$ preserves the trace pairing and therefore

$$
\mathfrak d(b\mathcal O b^{-1})=\mathfrak d(\mathcal O).
$$

Scalar extension to a completion should not be confused with ideal extension to a finite field. At a completion we merely read one exponent of an $R$-ideal. Under a finite extension $F'/F$, ramification indices enter the extended discriminant, and an order may cease to be maximal because the integral closure and scalar extension need not coincide without hypotheses. No such base-change claim is needed here.

## 5. Maximal orders

### 5.1 Existence by controlling overorders

Maximal orders provide the integral baseline at each place. Their existence is not a consequence of Zorn's lemma alone unless one verifies that unions remain finite lattices. The discriminant supplies a finite argument.

**Theorem 5.1 (existence).** Every order $\mathcal O\subset B$ is contained in a maximal order.

**Proof strategy.** Any overorder lies in the trace dual of $\mathcal O$, so there are only finitely many possible intermediate lattices. Choose a maximal one.

**Proof.** If $\mathcal O'\supset\mathcal O$ is an order and $x\in\mathcal O'$, then for every $y\in\mathcal O$ the product $xy$ belongs to $\mathcal O'$, and its reduced trace lies in $R$. Hence $x\in\mathcal O^\#$. Thus

$$
\mathcal O\subset\mathcal O'\subset\mathcal O^\#.
$$

The finite module $\mathcal O^\#/\mathcal O$ has only finitely many submodules, because $R/I$ is finite for every nonzero ideal $I$ of the number ring $R$. Therefore only finitely many intermediate lattices can be overorders. A maximal member is a maximal order. $\square$

Over a general Dedekind domain with infinite residue fields, the last finiteness sentence must be replaced by a noetherian or discriminant-minimization argument. The number-field hypothesis makes the above proof especially concrete.

### 5.2 Maximality is local

**Theorem 5.2 (local maximality criterion).** An order $\mathcal O\subset B$ is maximal if and only if $\mathcal O_v$ is a maximal $R_v$-order in $B_v$ for every finite $v$.

**Proof strategy.** A global enlargement gives a local enlargement somewhere. Conversely, a local enlargement at one place can be patched with the old order at all other places.

**Proof.** If $\mathcal O\subsetneq\mathcal O'$, Proposition 4.1 shows that $\mathcal O_v\subsetneq\mathcal O'_v$ for at least one $v$. Thus global maximality implies local maximality.

Conversely, suppose $\mathcal O_v$ has a proper overorder $\Lambda_v$. Set $\Lambda_w=\mathcal O_w$ for $w\ne v$. The reconstruction theorem produces a global order $\mathcal O'$ with these completions. It properly contains $\mathcal O$, contradicting global maximality. $\square$

This proof also completes Theorem 3.2 once the two local minimal discriminant computations are known.

### 5.3 Split maximal orders as endomorphism rings

Let $K$ be nonarchimedean with valuation ring $A$, and let $C=M_2(K)=\operatorname{End}_K(K^2)$. Every rank-two $A$-lattice $L\subset K^2$ gives

$$
\operatorname{End}_A(L)=\{g:gL\subset L\}.
$$

**Theorem 5.3.** The maximal $A$-orders in $M_2(K)$ are exactly the rings $\operatorname{End}_A(L)$. They are all conjugate to $M_2(A)$ by $\operatorname{GL}_2(K)$.

**Proof strategy.** A basis of $L$ proves that its endomorphism ring is a conjugate of $M_2(A)$, hence maximal. For the converse, let a maximal order stabilize a suitable lattice and compare it with the full endomorphism ring.

Choose any $A$-lattice $L_0$. If $\Lambda$ is an order, the lattice $L=\Lambda L_0$ is finite because $\Lambda$ is finite over $A$, and it is $\Lambda$-stable. Thus

$$
\Lambda\subset\operatorname{End}_A(L).
$$

Maximality gives equality. Since a lattice over the DVR $A$ is free, $L=gA^2$ for some $g\in\operatorname{GL}_2(K)$, and

$$
\operatorname{End}_A(L)=gM_2(A)g^{-1}.
$$

The order $M_2(A)$ is maximal because any integral matrix algebra containing all matrix units and lying in $M_2(K)$ cannot enlarge one coefficient without multiplication by matrix units enlarging a scalar corner beyond $A$. This proves the theorem.

### 5.4 The division case has one maximal order

Let $D/K$ be the quaternion division algebra. There is a canonical extension of the valuation:

$$
w_D(x)=\frac12v_K(\operatorname{Nrd}(x)),
\qquad x\in D^\times.
$$

Its value group is $\frac12\mathbf Z$. Define

$$
\mathcal O_D=\{x\in D:w_D(x)\ge0\},
\qquad
\mathfrak P_D=\{x:w_D(x)>0\}.
$$

The ultrametric inequality for the division valuation makes $\mathcal O_D$ a ring, and every integral element of $D$ has nonnegative valuation. Hence every $A$-order lies in $\mathcal O_D$.

**Theorem 5.4.** The ring $\mathcal O_D$ is the unique maximal $A$-order in $D$. It is invariant under conjugation by $D^\times$, its Jacobson radical is $\mathfrak P_D$, and $\mathcal O_D/\mathfrak P_D$ is the quadratic extension of the residue field.

**Proof strategy.** Use the division valuation first to capture every integral element, then read the radical and residue field from the positive-value filtration.

**Proof.** The inequalities

$$
w_D(x+y)\ge\min(w_D(x),w_D(y)),
\qquad
w_D(xy)=w_D(x)+w_D(y)
$$

show that $\mathcal O_D$ is a ring and $\mathfrak P_D$ is its unique maximal two-sided ideal. An element of nonnegative value is a unit precisely when its value is zero, with inverse again of value zero. Every element of an $A$-order is integral. If $w_D(x)<0$, the valuations of the terms in any monic polynomial satisfied by $x$ have a unique smallest member, the leading power of $x$, so they cannot sum to zero. Hence an integral element has nonnegative value. Every order is therefore contained in $\mathcal O_D$, proving maximality and uniqueness.

Conjugation preserves reduced norm and hence $w_D$, so it preserves both $\mathcal O_D$ and $\mathfrak P_D$. Finally, the unramified quadratic maximal subfield of $D$ has residue field of degree two and maps onto $\mathcal O_D/\mathfrak P_D$; the cyclic description in Section 6.5 makes this quotient explicit. $\square$

Uniqueness is stronger than conjugacy. In the split case maximal orders form many vertices, all conjugate. In the division case the valuation singles out one actual subset of $D$, and conjugation preserves it because reduced norm is conjugation invariant.

### 5.5 Local conjugacy does not imply global conjugacy

Theorems 5.3 and 5.4 show that any two global maximal orders are locally conjugate at every finite place. It does not follow that they are conjugate by one element of $B^\times$. The obstruction is global: the local conjugating elements form a finite adele, and there need not be a rational element in its double coset.

The set of global $B^\times$-conjugacy classes of maximal orders is finite; its cardinality is called the **type number** of $B$. It can exceed one. This phenomenon is already present in definite rational quaternion algebras of suitable discriminant. Thus statements proved by putting one local maximal order into matrix form describe a genus, not necessarily one global conjugacy class.

The adelic obstruction can be stated exactly. Fix a maximal order $\mathcal M$ and let

$$
\mathcal N(\widehat{\mathcal M})
=\{g\in\widehat B^\times:
g\widehat{\mathcal M}g^{-1}=\widehat{\mathcal M}\}.
$$

Every maximal order has the form

$$
B\cap g\widehat{\mathcal M}g^{-1}
$$

for some $g\in\widehat B^\times$, and two such orders are globally conjugate precisely when the corresponding elements have the same class in

$$
B^\times\backslash\widehat B^\times/
\mathcal N(\widehat{\mathcal M}).
$$

Thus type number is a rational-versus-adelic conjugacy obstruction. Its finiteness will follow from the ideal-class finiteness theorem, since $\widehat{\mathcal M}^\times$ is contained in the normalizer.

This warning will recur for Eichler orders. Local level determines local conjugacy exactly, but a global order can carry additional class information.

## 6. The two explicit local models

### 6.1 Split orders from lattice chains

The endomorphism description of a split maximal order is more than a classification device. It translates intersections of orders into simultaneous stabilization of lattices. Let $V=K^2$ and let $L,L'$ be $A$-lattices. Then

$$
\operatorname{End}_A(L)\cap\operatorname{End}_A(L')
=\{g\in\operatorname{End}_K(V):gL\subset L,\ gL'\subset L'\}.
$$

Thus the intersection remembers a pair of integral models of the same vector space. Scaling a lattice by $K^\times$ does not change its endomorphism ring, so homothety classes, rather than literal lattices, are the natural parameters.

By the elementary divisor theorem, after scaling and changing basis any pair has the form

$$
L=Ae_1+Ae_2,
\qquad
L'=Ae_1+\pi^nAe_2
$$

for one integer $n\ge0$. With respect to $e_1,e_2$,

$$
\operatorname{End}_A(L)=M_2(A)
$$

and

$$
\operatorname{End}_A(L')
=
\begin{pmatrix}
A&\pi^{-n}A\\
\pi^nA&A
\end{pmatrix}.
$$

Their intersection is the standard order

$$
\mathcal E_n=
\begin{pmatrix}
A&A\\
\pi^nA&A
\end{pmatrix}.
$$

For $n=0$ this is maximal. For $n>0$ it is a proper suborder of both displayed maximal orders.

### 6.2 The elementary Bruhat--Tits tree

The preceding normal form has a useful geometric summary. We introduce only the amount of the Bruhat--Tits tree needed to understand these intersections.

Vertices are homothety classes $[L]$ of rank-two $A$-lattices in $K^2$. Two vertices are joined by an edge if representatives can be chosen with

$$
\pi L\subsetneq L'\subsetneq L.
$$

Then $L'/\pi L$ is a one-dimensional subspace of the two-dimensional residue space $L/\pi L$. If the residue field has $q$ elements, each vertex has $q+1$ neighbors. The elementary divisor theorem shows that the graph is connected and gives a path of length $n$ between the two vertices in Section 6.1.

Here is a precise way to see the tree assertion rather than only the existence of paths. Fix a vertex $[L]$. Elementary divisors define the nonnegative distance candidate from $[L]$ to any other vertex, and an edge changes it by exactly one. Every vertex other than $[L]$ has exactly one neighbor on which this integer decreases: in elementary-divisor coordinates, it is obtained by shortening the larger exponent by one. If a reduced closed path existed, choose a vertex on it at maximal distance from $[L]$. Its two neighbors on the path would both be the unique neighbor closer to $[L]$, so the path would immediately backtrack. This is impossible for a reduced path. The graph is therefore connected and acyclic.

The stabilizer in $\operatorname{PGL}_2(K)$ of $[L]$ is the image of $\operatorname{End}_A(L)^\times$. The order $\mathcal E_n$ stabilizes every lattice in the segment

$$
[Ae_1+Ae_2],
[Ae_1+\pi Ae_2],
\ldots,
[Ae_1+\pi^nAe_2].
$$

Conversely, an endomorphism stabilizing the two endpoints stabilizes every intermediate lattice. Thus $\mathcal E_n$ is the endomorphism ring of this length-$n$ lattice chain.

No boundary of the tree, harmonic analysis, or representation theory is needed here. The tree serves one exact purpose: the distance between two maximal split orders is the exponent in their intersection.

### 6.3 Neighboring maximal orders

For $n=1$ the intersection is

$$
\mathcal E_1=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}:
a,b,d\in A,\ c\in\pi A
\right\}.
$$

Reduction modulo $\pi$ maps it to the upper triangular subalgebra of $M_2(k)$. Its unit group maps to the upper triangular Borel subgroup of $\operatorname{GL}_2(k)$. This is the integral meaning of an edge: a vertex chooses a lattice, while an oriented adjacent edge additionally chooses a line in its residue space.

When $n>1$, reduction modulo $\pi$ still sees only an upper triangular matrix. It cannot distinguish $n=1$ from $n=7$. The higher congruence $c\in\pi^nA$ retains the length of the segment. This is the first reason non-squarefree level behaves differently: its depth is invisible in the first residue quotient.

### 6.4 Discriminant of the standard intersection

Use the basis

$$
E_{11},\quad E_{12},\quad \pi^nE_{21},\quad E_{22}
$$

of $\mathcal E_n$. Relative to the basis of $M_2(A)$, its change-of-basis determinant is $\pi^n$. Since $M_2(A)$ has unit discriminant, the index formula gives

$$
\operatorname{disc}(\mathcal E_n)=(\pi^{2n}),
\qquad
\mathfrak d(\mathcal E_n)=(\pi^n).
$$

The tree distance, the lower-left congruence depth, and the reduced discriminant exponent are therefore the same integer.

### 6.5 The division order in cyclic coordinates

Now let $D/K$ be division. Let $L/K$ be the unramified quadratic extension, with ring of integers $A_L$ and nontrivial automorphism $\sigma$. Choose an element $\Pi$ satisfying

$$
\Pi^2=\pi,
\qquad
\Pi a=\sigma(a)\Pi\quad(a\in L).
$$

Then

$$
D=L\oplus L\Pi,
\qquad
\mathcal O_D=A_L\oplus A_L\Pi,
\qquad
\mathfrak P_D=\Pi\mathcal O_D.
$$

Multiplication shows directly that $\mathcal O_D$ is an order. Since $w_D(\Pi)=1/2$ and unramified units have value zero, the displayed lattice is exactly the valuation ring of Section 5.4. Its residue quotient is $A_L/\pi A_L$, a quadratic extension of $k$.

Choose an $A$-basis $1,u$ of $A_L$. Then $1,u,\Pi,u\Pi$ is an $A$-basis of $\mathcal O_D$. The trace pairing splits into two blocks. The $A_L$ block has unit discriminant because $L/K$ is unramified, while the $A_L\Pi$ block acquires one factor of $\pi$ in each of its two directions. Hence

$$
\operatorname{disc}(\mathcal O_D)=(\pi^2),
\qquad
\mathfrak d(\mathcal O_D)=(\pi).
$$

This completes the local discriminant computation promised in Chapter 3.

We can now finish the deferred proof of Theorem 3.2. The equivalence of global and local maximality is Theorem 5.2. If $\mathcal O$ is maximal, then locally it is conjugate to $M_2(R_v)$ at a split place and equals $\mathcal O_{D_v}$ at a division place. Sections 6.4 and 6.5 give reduced exponent zero and one, respectively, so $\mathfrak d(\mathcal O)=\mathfrak d(B)$. Conversely, if the two discriminants agree, place $\mathcal O$ in a maximal order $\mathcal M$ using Theorem 5.1. The square-index formula gives

$$
\mathfrak d(\mathcal O)
=[\mathcal M:\mathcal O]\mathfrak d(\mathcal M)
=[\mathcal M:\mathcal O]\mathfrak d(B).
$$

Equality forces the index ideal to be $R$, hence $\mathcal O=\mathcal M$. This proves all three equivalences.

### 6.6 Why there is no division-tree level

Because $\mathcal O_D$ is the unique maximal order, an intersection of two maximal orders in $D$ is just $\mathcal O_D$. There is therefore no positive Eichler distance at a division place. One can certainly form nonmaximal orders such as

$$
A+\mathfrak P_D^m,
$$

but they are not intersections of two distinct maximal orders. This distinction is essential: not every quaternion order is Eichler, and a level ideal for an Eichler order must be prime to the algebra discriminant.

## 7. Eichler orders and level ideals

### 7.1 Why intersections are the right next class

Maximal orders are too rigid to encode congruence depth at split primes. Arbitrary suborders, on the other hand, have a complicated ideal theory and no uniform local shape. Intersections of two maximal orders form the useful middle ground. Locally, the tree gives them one integer parameter; globally, those integers assemble into an ideal.

An **Eichler order** in $B$ is an order of the form

$$
\mathcal O=\mathcal M\cap\mathcal M'
$$

for two maximal orders $\mathcal M,\mathcal M'$. The two maximal orders are allowed to coincide. Equivalently, $\mathcal O_v$ is an intersection of two maximal $R_v$-orders for every finite $v$; local pairs may be patched to global pairs by the lattice reconstruction principle.

At a split place, $\mathcal O_v$ is conjugate to exactly one $\mathcal E_{n_v}$. At a division place, it equals $\mathcal O_{D_v}$ and we set $n_v=0$. Almost every $n_v$ is zero.

### 7.2 The level ideal

The **level** of an Eichler order is

$$
\mathfrak N(\mathcal O)=\prod_{v<\infty}\mathfrak p_v^{n_v}.
$$

Its support is disjoint from $\mathfrak d(B)$. This coprimality is a theorem built into the local definition, not a simplifying convention: division places have only the unique maximal order and hence exponent zero.

The local classification is exact.

**Theorem 7.1 (local Eichler classification).** Let $K$ be nonarchimedean.

- In $M_2(K)$, two Eichler orders are conjugate by $\operatorname{GL}_2(K)$ if and only if their exponents $n$ agree.
- In the quaternion division algebra, the only Eichler order is the maximal order.

**Proof strategy.** Put the defining maximal orders at vertices of the tree. Conjugation preserves distance, and $\operatorname{PGL}_2(K)$ acts transitively on segments of fixed length. The division assertion is uniqueness of the maximal order.

**Proof.** In the split case write the order as $\operatorname{End}_A(L)\cap\operatorname{End}_A(L')$. Simultaneously putting $L,L'$ in elementary-divisor form conjugates it to $\mathcal E_n$, where $n$ is the distance between $[L]$ and $[L']$. Conjugation acts on the tree by graph automorphisms, so it preserves $n$. Conversely, two pairs at the same distance can be put into the same displayed elementary-divisor form, so their intersections are conjugate. In the division case both defining maximal orders equal $\mathcal O_D$, and their intersection is $\mathcal O_D$. $\square$

The theorem requires that the orders actually be Eichler. Equal discriminant exponents do not classify arbitrary local orders; several non-Eichler orders can share one discriminant.

### 7.3 Reduced discriminant equals ramification times level

The central formula is

**Theorem 7.2 (Eichler discriminant formula).** If $\mathcal O$ is an Eichler order of level $\mathfrak N$, then

$$
\boxed{\mathfrak d(\mathcal O)=\mathfrak d(B)\mathfrak N,}
\qquad
(\mathfrak d(B),\mathfrak N)=1.
$$

**Proof strategy.** Both sides are ideals, so compare their valuations. At a split place the standard matrix calculation gives exponent $n_v$; at a division place the unique maximal order gives exponent one and $n_v=0$.

**Proof.** If $B_v$ is split, conjugate $\mathcal O_v$ to $\mathcal E_{n_v}$. Section 6.4 gives reduced discriminant $\mathfrak p_v^{n_v}$, while $v(\mathfrak d(B))=0$. If $B_v$ is division, $\mathcal O_v$ is maximal and Section 6.5 gives reduced exponent one; here $v(\mathfrak d(B))=1$ and $n_v=0$. The local exponents agree at every finite place. $\square$

The formula has a useful converse with a hypothesis: if $\mathcal O$ is known to be Eichler, its level is $\mathfrak d(\mathcal O)/\mathfrak d(B)$. Without the Eichler hypothesis this quotient is still an integral ideal, but calling it a level can falsely suggest the standard local form.

### 7.4 Squarefree and deeper level

An Eichler level is **squarefree** if every $n_v\le1$. At a split prime dividing such a level, the local order stabilizes one edge and is hereditary: every one-sided ideal is locally projective. When $n_v>1$, the order stabilizes a longer segment and is not hereditary. Proper one-sided ideals need not all be invertible.

The local unit groups also exhibit the distinction:

$$
\mathcal E_n^\times
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{GL}_2(A):c\in\pi^nA
\right\}.
$$

For $n=1$, this is the inverse image of a Borel subgroup modulo $\pi$. For $n>1$, it is a genuinely deeper congruence subgroup. Its reduction modulo $\pi$ is unchanged, so arguments using only residue flags are insufficient at nonsquarefree level.

Squarefree does not mean maximal: $n_v=1$ is still a proper intersection. Nor does nonsquarefree mean pathological; it means that local projectivity and ideal invertibility require explicit hypotheses rather than following from heredity.

### 7.5 Global conjugacy and the genus of an Eichler order

Two Eichler orders with the same level in the same algebra are locally conjugate at every finite place. They are said to lie in the same **genus**. They need not be globally conjugate. As for maximal orders, one adelic conjugating element need not be replaceable by one element of $B^\times$.

Thus the data

$$
(B,\mathfrak N)
$$

determines the local conjugacy type of an Eichler order, but not always its global conjugacy class. Later compact open groups built from the unit groups of locally conjugate orders are conjugate in $\widehat B^\times$; their finite double-coset sets are naturally comparable, but choosing a specific global order remains genuine data.

### 7.6 A rational matrix order

For $N\ge1$, define

$$
\mathcal E_0(N)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in M_2(\mathbf Z):c\equiv0\pmod N
\right\}.
$$

It is the intersection

$$
M_2(\mathbf Z)\cap
\begin{pmatrix}1&0\\0&N\end{pmatrix}
M_2(\mathbf Z)
\begin{pmatrix}1&0\\0&N^{-1}\end{pmatrix}.
$$

At a prime $p$, its local exponent is $v_p(N)$. Since $M_2(\mathbf Q)$ has algebra discriminant $1$, Theorem 7.2 gives

$$
\mathfrak d(\mathcal E_0(N))=(N).
$$

For $N=12$, the level is nonsquarefree at $2$ and squarefree at $3$. Modulo $2$ the conditions $c\equiv0\pmod4$ and $c\equiv0\pmod2$ look identical, but the $2$-adic orders and their unit groups differ.

## 8. One-sided and fractional ideals

### 8.1 Why ideals need two orders

In a commutative field, an ideal has one multiplier ring. In a noncommutative algebra, multiplication from the left and the right are different operations. A lattice can be stable under one order on the right and another on the left, and multiplication of ideals is meaningful only when the middle orders match.

A **fractional right $\mathcal O$-ideal** is a full $R$-lattice $I\subset B$ satisfying

$$
I\mathcal O\subset I.
$$

It is **integral** if $I\subset\mathcal O$. Left ideals are defined symmetrically. “Fractional” refers to the possibility of denominators in the central field; commensurability gives $aI\subset\mathcal O$ for some nonzero $a\in R$.

Define the multiplier orders

$$
\mathcal O_L(I)=\{b\in B:bI\subset I\},
\qquad
\mathcal O_R(I)=\{b\in B:Ib\subset I\}.
$$

Both are orders. If $I$ is a right $\mathcal O$-ideal, then $\mathcal O\subset\mathcal O_R(I)$. We call $I$ **proper as a right $\mathcal O$-ideal** when

$$
\mathcal O_R(I)=\mathcal O.
$$

This convention places the specified order on the side of the action. Properness is not automatic: the same lattice may be stable under a strictly larger right order.

### 8.2 Bimodule notation and variance

It is useful to say that $I$ is an $(\mathcal O_1,\mathcal O_2)$-ideal when

$$
\mathcal O_L(I)=\mathcal O_1,
\qquad
\mathcal O_R(I)=\mathcal O_2.
$$

If $I$ is an $(\mathcal O_1,\mathcal O_2)$-ideal and $J$ is an $(\mathcal O_2,\mathcal O_3)$-ideal, define

$$
IJ=\left\{\sum_{r=1}^m x_ry_r:x_r\in I,\ y_r\in J\right\}.
$$

Then

$$
\mathcal O_1(IJ)\subset IJ,
\qquad
(IJ)\mathcal O_3\subset IJ.
$$

Under invertibility hypotheses the multiplier orders are exactly $\mathcal O_1$ and $\mathcal O_3$. The order $\mathcal O_2$ disappears in the product because it is the matched middle action. Reversing $I$ and $J$ is generally meaningless, not merely unequal.

Canonical conjugation reverses variance:

$$
\overline{IJ}=\bar J\,\bar I,
\qquad
\mathcal O_L(\bar I)=\overline{\mathcal O_R(I)},
\qquad
\mathcal O_R(\bar I)=\overline{\mathcal O_L(I)}.
$$

Every order is stable under the bar, but the reversal of the ideals remains.

### 8.3 Principal one-sided ideals

For $x\in B^\times$,

$$
I=x\mathcal O
$$

is a fractional right $\mathcal O$-ideal. Its orders are

$$
\mathcal O_R(I)=\mathcal O,
\qquad
\mathcal O_L(I)=x\mathcal O x^{-1}.
$$

Thus left multiplication preserves the right order and conjugates the left order. In contrast, $\mathcal O x$ is a left $\mathcal O$-ideal with right order $x^{-1}\mathcal O x$.

This elementary calculation fixes the convention used throughout the adelic classification. Right ideals will be compared by **left** multiplication:

$$
I\sim J
\quad\Longleftrightarrow\quad
I=bJ\text{ for some }b\in B^\times.
$$

Right multiplication would change the specified right order unless the multiplier normalized it.

### 8.4 Localization of ideals and their orders

For every finite $v$,

$$
I_v=I\otimes_RR_v
$$

is a fractional right $\mathcal O_v$-ideal. Multiplier orders commute with completion:

$$
\mathcal O_L(I)_v=\mathcal O_L(I_v),
\qquad
\mathcal O_R(I)_v=\mathcal O_R(I_v).
$$

Indeed, both sides are solutions to finitely many linear integrality conditions, and completion is faithfully flat. Hence properness is local:

$$
I\text{ is proper right }\mathcal O
\Longleftrightarrow
\mathcal O_R(I_v)=\mathcal O_v\text{ for every }v.
$$

Ideal products also localize:

$$
(IJ)_v=I_vJ_v.
$$

These identities justify proving invertibility locally and reconstructing the inverse globally.

### 8.5 A warning from nonmaximal orders

For a maximal local order, finitely generated torsion-free one-sided modules of rank one behave well. For a nonhereditary order they need not. A proper ideal can fail to be locally principal and fail to possess a two-sided inverse. This occurs already for $\mathcal E_n$ when $n>1$.

Therefore the phrases “proper,” “invertible,” and “locally principal” are not synonyms in the generality of arbitrary orders. We will state the implication needed later precisely: locally principal proper ideals are invertible, and invertible ideals are locally principal. At squarefree Eichler level heredity makes more ideals invertible, but later adelic class sets will deliberately classify the locally principal ones so that no hidden hereditary hypothesis is required.

## 9. Invertibility and reduced norm ideals

### 9.1 The inverse ideal

Let $I$ be an $(\mathcal O_1,\mathcal O_2)$-ideal. It is **invertible** if there is an $(\mathcal O_2,\mathcal O_1)$-ideal $I^{-1}$ such that

$$
II^{-1}=\mathcal O_1,
\qquad
I^{-1}I=\mathcal O_2.
$$

The two equations are both required. One-sided equality alone is not a safe substitute in an arbitrary order. If an inverse exists, it is unique and equals

$$
\{x\in B:Ix\subset\mathcal O_1\}
=\{x\in B:xI\subset\mathcal O_2\}.
$$

For $I=x\mathcal O_2$ with $\mathcal O_1=x\mathcal O_2x^{-1}$,

$$
I^{-1}=\mathcal O_2x^{-1}.
$$

The order of factors is forced by variance.

### 9.2 Local principality is the usable criterion

A proper fractional right $\mathcal O$-ideal $I$ is **locally principal** if for every finite $v$ there is $x_v\in B_v^\times$ such that

$$
I_v=x_v\mathcal O_v.
$$

Because $I$ and $\mathcal O$ are two global lattices, $I_v=\mathcal O_v$ outside a finite set, and there one may take $x_v=1$. Equivalently, the family $(x_v)$ belongs to $\widehat B^\times$.

**Theorem 9.1.** A proper fractional ideal is invertible if and only if it is locally principal. More precisely, an invertible $(\mathcal O_1,\mathcal O_2)$-ideal is locally of the form $x_v\mathcal O_{2,v}$, and a family of such local principal ideals reconstructs an inverse globally.

**Proof strategy.** The relevant local statement is stronger than the slogan that projective modules over local rings are free: an order over a DVR is usually only semilocal as a noncommutative ring. The invertible-bimodule identities force the same simple multiplicities as the regular module after reduction modulo the Jacobson radical. Idempotent lifting and Nakayama's lemma then give one generator. Conversely, a principal local generator gives an explicit inverse; equality of the local products at every place gives global equality.

**Proof.** If $I$ is invertible, multiplication exhibits $I_v$ as an invertible right $\mathcal O_{2,v}$-module. Reduce it and its inverse modulo the Jacobson radicals of their multiplier orders. The two product identities show that the resulting bimodules implement an equivalence and have the same simple multiplicities as the regular module. Since idempotents lift in an order over a complete DVR, Nakayama's lemma gives an isomorphism

$$
\mathcal O_{2,v}\xrightarrow{\sim}I_v
$$

of right modules. The image $x_v$ of $1$ generates $I_v$. After extending scalars to $F_v$, multiplication by $x_v$ maps $B_v$ onto $B_v$, so $x_v\in B_v^\times$. Hence $I_v=x_v\mathcal O_{2,v}$.

Conversely, suppose $I_v=x_v\mathcal O_{2,v}$ at every $v$. Its left order is $x_v\mathcal O_{2,v}x_v^{-1}$. Define locally

$$
J_v=\mathcal O_{2,v}x_v^{-1}.
$$

The $J_v$ equal a fixed reference lattice almost everywhere and reconstruct a global lattice $J$. Locally $I_vJ_v=\mathcal O_{1,v}$ and $J_vI_v=\mathcal O_{2,v}$. The local--global equality criterion gives the two global identities. $\square$

### 9.3 The reduced norm ideal

For a full lattice $I\subset B$, define its **reduced norm ideal** by

$$
\operatorname{nrd}(I)
=\text{the fractional ideal generated by }
\{\operatorname{Nrd}(x):x\in I\}.
$$

This is an ideal, not generally the set of norms itself. Sums of norm values need not be norm values. Localization commutes with its formation:

$$
\operatorname{nrd}(I)R_v
=\langle\operatorname{Nrd}(x):x\in I_v\rangle_{R_v}.
$$

If $I_v=x_v\mathcal O_v$ is locally principal, then $1\in\mathcal O_v$ and integrality of norm on $\mathcal O_v$ give

$$
\operatorname{nrd}(I)R_v
=\operatorname{Nrd}(x_v)R_v.
$$

Thus locally principal ideals have a particularly clean norm valuation.

For $b\in B^\times$ and $a\in F^\times$,

$$
\operatorname{nrd}(bI)=(\operatorname{Nrd}(b))\operatorname{nrd}(I),
$$

$$
\operatorname{nrd}(aI)=(a^2)\operatorname{nrd}(I),
$$

because a central scalar has reduced norm $a^2$. The square in the second formula is a common source of errors: $B$ has ordinary dimension four but reduced degree two.

### 9.4 Norm under multiplication

For arbitrary lattices there is no simple multiplicative formula. Although $\operatorname{Nrd}(xy)=\operatorname{Nrd}(x)\operatorname{Nrd}(y)$ for single products, the lattice $IJ$ also contains sums of products, and the quadratic cross terms in the norm of such a sum do not factor. A multiplicativity assertion therefore needs projectivity or local principality, not merely multiplicativity of the norm on elements.

For composable locally principal ideals, equality does hold. Locally write

$$
I_v=x_v\mathcal O_{2,v},
\qquad
J_v=y_v\mathcal O_{3,v},
$$

where the left order of $J_v$ equals $\mathcal O_{2,v}=y_v\mathcal O_{3,v}y_v^{-1}$. Then $I_vJ_v=x_vy_v\mathcal O_{3,v}$, and

$$
\operatorname{nrd}(IJ)
=\operatorname{nrd}(I)\operatorname{nrd}(J).
$$

In particular,

$$
\operatorname{nrd}(I^{-1})=\operatorname{nrd}(I)^{-1}.
$$

### 9.5 Norm, conjugation, and equivalence

Canonical conjugation preserves reduced norm, hence

$$
\operatorname{nrd}(\bar I)=\operatorname{nrd}(I).
$$

Algebra conjugation also preserves it:

$$
\operatorname{nrd}(bIb^{-1})=\operatorname{nrd}(I).
$$

By contrast, equivalent right ideals $I=bJ$ satisfy

$$
\operatorname{nrd}(I)=(\operatorname{Nrd}(b))\operatorname{nrd}(J).
$$

Thus the norm ideal itself is not an invariant of an ideal class, but its class in the ordinary ideal class group changes only by a principal ideal and therefore is invariant. At real places, positivity restrictions on reduced norms can refine this to a narrow statement, but the finite ideal class set used here needs only the ordinary ideal class.

The left order discriminant is invariant under ideal equivalence up to conjugation:

$$
\mathcal O_L(bI)=b\mathcal O_L(I)b^{-1},
\qquad
\mathfrak d(\mathcal O_L(bI))=\mathfrak d(\mathcal O_L(I)).
$$

The right order remains $\mathcal O$. This is the exact package of variance and invariance needed when representatives are changed.

## 10. Ideal classes before adeles

### 10.1 One-sided equivalence

Fix an order $\mathcal O$. The set of equivalence classes of locally principal proper fractional right $\mathcal O$-ideals, under

$$
I\sim J\iff I=bJ\quad(b\in B^\times),
$$

is denoted

$$
\operatorname{Cl}_r(\mathcal O).
$$

It is a set, not usually a group. Multiplying two right $\mathcal O$-ideals is not generally defined with matching middle orders. Only in the commutative rank-one case does ideal multiplication descend automatically to a class group.

There is similarly a left class set $\operatorname{Cl}_\ell(\mathcal O)$. Canonical conjugation gives a bijection

$$
\operatorname{Cl}_r(\mathcal O)\xrightarrow{\sim}
\operatorname{Cl}_\ell(\mathcal O),
\qquad
[I]\longmapsto[\bar I].
$$

It reverses products when those products are defined.

### 10.2 Locally principal does not mean principal

Every principal ideal $b\mathcal O$ is locally principal, but the converse is global and can fail. Local generators $b_v$ need not be the completions of one $b\in B^\times$. The class set measures exactly this failure.

Likewise, a nonprincipal ideal need not signal any local defect. It may be indistinguishable from $\mathcal O$ at each place after a local change of generator. This is analogous to a nonprincipal fractional ideal of $R$: every localization at a DVR is principal, while no global generator exists.

The quaternionic class set is richer because a representative also has a left order. Equivalent representatives have conjugate left orders, and different ideal classes can yield the same left-order conjugacy class. The resulting map to order types is generally neither injective nor surjective without further hypotheses.

### 10.3 The matrix algebra and Morita's picture

Take $B=M_2(F)$ and $\mathcal O=M_2(R)$. A locally principal right ideal is controlled by the corresponding rank-two lattice in $F^2$. Over $R=\mathbf Z$, every such lattice has a basis, and elementary divisors plus a rational change of basis show that every locally principal right ideal is equivalent to $M_2(\mathbf Z)$. Hence

$$
|\operatorname{Cl}_r(M_2(\mathbf Z))|=1.
$$

Over a general number ring, projective modules can carry ideal-class information. Morita equivalence relates right $M_2(R)$-modules of rank one to rank-two projective $R$-modules, and determinant remembers an ideal class. Thus the rational calculation should not be promoted to a universal statement about every $F$.

### 10.4 Why finiteness is plausible

An ideal class permits arbitrary denominators, so finiteness is not obvious from the definition. Equivalence by $B^\times$ must be used to reduce those denominators and then bound the remaining archimedean size. In a totally definite quaternion algebra, reduced norm is positive definite at every real place; a shortest-vector argument can choose a controlled element in each ideal. In an indefinite algebra, the same conclusion is true but requires general reduction theory or the finiteness theorem for lattices over orders.

We postpone the proof until the adelic description turns local generators into one finite adele. The topology will expose the exact compactness input and will also identify the class set with the double quotient needed later.

## 11. Finite adeles of a quaternion algebra

### 11.1 The restricted product attached to integrality

Book 4 built finite adeles by requiring integrality at almost every place. The same construction applies to the four-dimensional vector space $B$. Fix any order $\mathcal O$. The finite adelic algebra is

$$
\widehat B=B\otimes_F\mathbf A_{F,f}
=\prod_{v<\infty}'(B_v,\mathcal O_v).
$$

As an additive restricted product, it consists of tuples $x=(x_v)$ with $x_v\in\mathcal O_v$ for almost every $v$. A different order gives the same restricted product and topology, because two orders have equal localizations outside finitely many places.

Its unit group has the restricted-product topology

$$
\widehat B^\times
=\prod_{v<\infty}'(B_v^\times,\mathcal O_v^\times).
$$

This is the unit group of $\widehat B$ as a set, endowed with the topology controlling both $x$ and $x^{-1}$. Thus $x_v\in\mathcal O_v^\times$ for almost every $v$. As with ideles, the naive subspace topology inherited from the additive ring would make inversion misbehave at a moving prime.

The diagonal embedding $B^\times\hookrightarrow\widehat B^\times$ is well defined because a fixed $b\in B^\times$ and its inverse are integral at almost every finite place. Unlike the diagonal embedding into the full adelic algebra, it is not generally discrete in the finite part alone. Discreteness is not needed for the algebraic double quotient.

### 11.2 Completion of an order

Define

$$
\widehat R=\prod_{v<\infty}R_v,
\qquad
\widehat{\mathcal O}=\mathcal O\otimes_R\widehat R
=\prod_{v<\infty}\mathcal O_v.
$$

The product is unrestricted because each component is integral. Additively, $\widehat{\mathcal O}$ is compact and open in $\widehat B$. Its unit group is

$$
\widehat{\mathcal O}^{\times}
=\prod_{v<\infty}\mathcal O_v^\times.
$$

Each $\mathcal O_v^\times$ is compact open in $B_v^\times$: it consists of elements of $\mathcal O_v$ whose reduced norm is a unit. Therefore $\widehat{\mathcal O}^\times$ is compact open in $\widehat B^\times$.

The distinction between $\widehat{\mathcal O}$ and $\widehat{\mathcal O}^\times$ matters. The first is an additive compact open lattice and contains nonunits. The second is a multiplicative compact open group and is the level subgroup used in a double quotient.

### 11.3 Adelic lattices and intersection

For a global lattice $I\subset B$, write

$$
\widehat I=I\otimes_R\widehat R=\prod_v I_v.
$$

Then

$$
I=B\cap\widehat I
$$

inside $\widehat B$. Conversely, every compact open $\widehat R$-submodule $L_f\subset\widehat B$ that equals a fixed $\widehat I^0$ outside finitely many places comes from

$$
B\cap L_f.
$$

In particular, for $g\in\widehat B^\times$ the product

$$
g\widehat{\mathcal O}=\prod_vg_v\mathcal O_v
$$

is the completion of a global lattice

$$
I(g)=B\cap g\widehat{\mathcal O}.
$$

Since each $g_v\mathcal O_v$ is a right $\mathcal O_v$-ideal, $I(g)$ is a fractional right $\mathcal O$-ideal. Moreover,

$$
\widehat{I(g)}=g\widehat{\mathcal O}.
$$

The equality is the substantive inverse part of lattice reconstruction; taking the intersection does not accidentally shrink a local component.

### 11.4 Adelic reduced norm

Reduced norm acts componentwise and defines

$$
\operatorname{Nrd}:\widehat B^\times\longrightarrow\mathbf A_{F,f}^\times.
$$

For $g=(g_v)$, the fractional ideal associated with this finite idele is

$$
\mathfrak a(\operatorname{Nrd}g)
=\prod_v\mathfrak p_v^{v(\operatorname{Nrd}(g_v))}.
$$

If $I(g)$ is the associated locally principal ideal, Section 9.3 gives

$$
\operatorname{nrd}(I(g))
=\mathfrak a(\operatorname{Nrd}g).
$$

Right multiplication of $g$ by $u\in\widehat{\mathcal O}^\times$ does not change this ideal, since $\operatorname{Nrd}(u_v)\in R_v^\times$. Left multiplication by $b\in B^\times$ multiplies it by the principal ideal $(\operatorname{Nrd}(b))$. This is exactly the norm behavior under ideal equivalence.

### 11.5 Conjugating compact opens

For $g\in\widehat B^\times$,

$$
g\widehat{\mathcal O}g^{-1}
=\prod_vg_v\mathcal O_vg_v^{-1}
$$

is the completion of an order in the genus of $\mathcal O$. Its unit group is

$$
g\widehat{\mathcal O}^{\times}g^{-1}.
$$

If $g$ happens to be diagonal from $b\in B^\times$, this is the completion of the globally conjugate order $b\mathcal O b^{-1}$. For general $g$, it may represent a globally nonconjugate order. The gap between adelic and rational conjugacy is precisely the type phenomenon from Chapter 5.

## 12. Ideal classes as double cosets

### 12.1 The statement and its conventions

The local generators of a locally principal right ideal form a quaternionic finite idele. Changing the generators on the right does nothing; changing the global ideal representative multiplies on the left. This predicts the quotient in the only order compatible with our conventions.

**Theorem 12.1 (adelic ideal-class bijection).** There is a natural bijection

$$
\boxed{
\operatorname{Cl}_r(\mathcal O)
\xrightarrow{\sim}
B^\times\backslash\widehat B^\times/
\widehat{\mathcal O}^{\times}.}
$$

It sends the double coset of $g$ to the equivalence class of

$$
I(g)=B\cap g\widehat{\mathcal O}.
$$

This is a classification of locally principal proper fractional **right** ideals. Left ideals would produce the reversed quotient $\widehat{\mathcal O}^\times\backslash\widehat B^\times/B^\times$, naturally identified with the right quotient by canonical conjugation and inversion.

### 12.2 Well-definedness

Suppose $g'=bgu$ with $b\in B^\times$ and $u\in\widehat{\mathcal O}^\times$. Since $u\widehat{\mathcal O}=\widehat{\mathcal O}$,

$$
I(g')
=B\cap bg\widehat{\mathcal O}
=b(B\cap g\widehat{\mathcal O})
=bI(g).
$$

The middle equality uses $bB=B$. Hence $I(g')$ is equivalent to $I(g)$.

The local lattice $g_v\mathcal O_v$ has right order exactly $\mathcal O_v$, because $g_v$ is invertible. Therefore $I(g)$ is proper. It is visibly locally principal. Thus the construction lands in the stated class set rather than in a larger collection of arbitrary proper ideals.

### 12.3 Constructing the inverse

Let $I$ be a locally principal proper right $\mathcal O$-ideal. Choose $g_v\in B_v^\times$ with

$$
I_v=g_v\mathcal O_v.
$$

At almost every $v$, $I_v=\mathcal O_v$ after comparing the two global lattices, so $g_v$ may be chosen in $\mathcal O_v^\times$. Hence $g=(g_v)$ lies in $\widehat B^\times$ and

$$
\widehat I=g\widehat{\mathcal O}.
$$

If $g'_v$ is another local generator, then

$$
g_v^{-1}g'_v\in\mathcal O_v^\times,
$$

so $g'=gu$ for $u\in\widehat{\mathcal O}^\times$. The resulting right coset is independent of all local choices.

If $I'=bI$, then $\widehat I'=b g\widehat{\mathcal O}$, so the corresponding idele lies in the same left $B^\times$-coset. We have therefore constructed a map from ideal classes to double cosets.

### 12.4 Proving the maps are inverse

Starting with $g$, the reconstructed ideal satisfies

$$
\widehat{I(g)}=g\widehat{\mathcal O}.
$$

Choosing the original $g_v$ as its local generators returns the right coset $g\widehat{\mathcal O}^\times$, and hence the original double coset.

Starting with $I$, the chosen $g$ satisfies $\widehat I=g\widehat{\mathcal O}$. Intersecting with diagonal $B$ gives

$$
I=B\cap\widehat I=B\cap g\widehat{\mathcal O}=I(g).
$$

Thus the two constructions are exact inverses, not merely mutually surjective correspondences. This explicit inverse proof is what makes later passage between ideals and adelic representatives safe.

### 12.5 Stabilizers and left orders

Let $[g]$ represent the right ideal $I=I(g)$. Its left order has completion

$$
\widehat{\mathcal O_L(I)}
=g\widehat{\mathcal O}g^{-1}.
$$

The stabilizer of the right coset $g\widehat{\mathcal O}^\times$ under left multiplication by $B^\times$ is

$$
B^\times\cap g\widehat{\mathcal O}^\times g^{-1}
=\mathcal O_L(I)^\times.
$$

This formula will later turn a double-coset representative into a finite arithmetic stabilizer in the definite case. It also shows why the left order, not the right order, varies with an ideal class.

## 13. Finiteness of the class set

### 13.1 The general finiteness theorem

**Theorem 13.1 (finiteness).** Let $F$ be a number field, let $A$ be a finite-dimensional semisimple $F$-algebra, and let $\Lambda\subset A$ be an $R$-order. Then the set of isomorphism classes in any fixed genus of full right $\Lambda$-lattices is finite. In particular, for every quaternion order $\mathcal O$,

$$
B^\times\backslash\widehat B^\times/
\widehat{\mathcal O}^\times
$$

is finite.

No definiteness hypothesis is needed for this algebraic finiteness statement. The hypotheses that matter are that $F$ is a number field, $A$ is semisimple, and $\Lambda$ is an order. Over more general global rings, or for nonsemisimple ambient algebras, a separate argument is required.

**Proof strategy.** This is the lattice finiteness theorem often called the Jordan--Zassenhaus principle. Embed every lattice in one rational vector space, clear denominators within its genus, and use archimedean reduction to choose a basis whose coordinates lie in a bounded region. Discreteness then leaves finitely many multiplication tables.

Here is the reduction mechanism in the present setting. A locally principal right ideal $I$ is locally isomorphic to $\mathcal O$ as a right $\mathcal O$-module. Central scaling, which does not change its class because $F^\times\subset B^\times$, first makes $I$ integral. The possible Steinitz classes of its underlying $R$-module lie in the finite ideal class group of $F$. After fixing one of them, Minkowski reduction chooses a pseudobasis whose successive minima are balanced by an $A$-linear rational automorphism. Decompose the rational module into its finitely many simple summands. On each isotypic part, the relations expressing right multiplication by a fixed $R$-basis of $\mathcal O$, together with the fixed multiplicities, give the standard reduction bound on the ratios of those minima. Thus the reduced pseudobasis vectors may be taken in a fixed archimedean compact set and a fixed finite-adelic lattice.

The adelic lattice finiteness result from Book 4 then applies: a compact adelic set meets diagonal $A$ in only finitely many points. Hence only finitely many reduced pseudobases, and therefore only finitely many right $\mathcal O$-lattices, occur. This is the content of the Jordan--Zassenhaus reduction argument; semisimplicity is what supplies the uniform bound after decomposing the rational module into simple summands.

Finally, an isomorphism $I\to J$ of right $\mathcal O$-lattices extends after tensoring with $F$ to an endomorphism of the regular right $B$-module $B$. Such an endomorphism is left multiplication by a unique $b\in B$, and invertibility of the isomorphism gives $b\in B^\times$. Thus module isomorphism is exactly the equivalence $J=bI$. This proves the stated finiteness of the double quotient.

### 13.2 Why definiteness gives a sharper compactness proof

Assume now that $F$ is totally real and $B$ is totally definite. In this case the norm itself gives an elementary reduction proof. On

$$
B_\infty=\prod_{v\mid\infty}B_v
$$

the quadratic form

$$
Q(x)=\sum_{v\mid\infty}\operatorname{Nrd}(x_v)
$$

is positive definite. Regard a fractional right ideal $I$ as a lattice in this real vector space. Minkowski's theorem supplies a nonzero $a\in I$ with

$$
Q(a)\le C\operatorname{covol}(I)^{1/(2[F:\mathbf Q])},
$$

where $C$ depends only on the fixed archimedean norm and measure. The arithmetic--geometric mean inequality then gives

$$
\left|N_{F/\mathbf Q}(\operatorname{Nrd}(a))\right|^2
\le C'\operatorname{covol}(I).
$$

Definiteness makes every nonzero $a$ invertible. Replace $I$ by the equivalent ideal $J=a^{-1}I$. Since $a\mathcal O\subset I$, one has $\mathcal O\subset J$. Left multiplication by $a$ has rational determinant $N_{F/\mathbf Q}(\operatorname{Nrd}(a))^2$, so

$$
\operatorname{covol}(J)
=\left|N_{F/\mathbf Q}(\operatorname{Nrd}(a))\right|^{-2}
\operatorname{covol}(I)
\ge (C')^{-1}.
$$

Consequently the additive index $|J/\mathcal O|$ is bounded independently of the ideal class. There are only finitely many over-lattices of $\mathcal O$ of bounded index: if $|J/\mathcal O|\le M$, the exponent of $J/\mathcal O$ divides one fixed integer depending on $M$, so every such $J$ lies between $\mathcal O$ and one fixed fractional multiple of it. This proves finiteness directly and makes clear exactly where definiteness is used.

There is a complementary topological packaging of the same reduction. At each real place, $B_v\cong\mathbf H$, and

$$
B_v^\times/F_v^\times
$$

is compact. Globally, the projective group $PB^\times=B^\times/F^\times$ is anisotropic: it has no nontrivial $F$-split torus. The definite reduction argument just given is the lattice form, in this quaternionic case, of the compactness statement

$$
PB^\times(F)\backslash PB^\times(\mathbf A_F)
$$

is compact.

To extract the desired finite set, quotient this compact adelic space on the right by the full archimedean projective group and by the image of the compact open $\widehat{\mathcal O}^\times$. The quotient remains compact. It is also discrete, because $\widehat{\mathcal O}^\times$ is open in the finite adelic group. Hence it is finite. Passing from $PB^\times$ back to $B^\times$ introduces only fibers that are quotients of

$$
F^\times\backslash\mathbf A_{F,f}^\times/\widehat R^\times
\cong\operatorname{Cl}(F),
$$

which is finite. This yields the desired finite double-coset set.

This proof explains why total definiteness is especially valuable later. General class-set finiteness does not require it, but definiteness makes the archimedean projective quotient compact, so no continuous archimedean parameter survives. Quaternionic automorphic spaces at finite level can then be built from a finite set with finite stabilizers modulo central units.

### 13.3 Stabilizers in the definite case

For a representative ideal $I$, the stabilizer is $\mathcal O_L(I)^\times$. If $B$ is totally definite, the group

$$
\mathcal O_L(I)^\times/R^\times
$$

is finite. Indeed, after scaling by a central unit, its image at infinity lies in a compact norm-one sphere, while it remains in an arithmetic lattice. A compact set meets a lattice in finitely many points.

Here is the unit-scaling step precisely. For $u\in\mathcal O_L(I)^\times$, the reduced norm is a totally positive unit of $R$. The quotient of the totally positive unit group by squares of units is finite. Choose representatives $\eta_1,\ldots,\eta_s$. After multiplying $u$ by the inverse of a suitable central unit, its reduced norm is one of the $\eta_j$. At every real place it therefore lies on one of finitely many fixed norm spheres. Those spheres are compact, while all finite components remain in $\widehat{\mathcal O_L(I)}$. Book 4's compact-set intersection theorem for the diagonal lattice in the adelic vector space $B(\mathbf A_F)$ now leaves only finitely many representatives modulo $R^\times$.

The central unit group $R^\times$ itself can be infinite when $F\ne\mathbf Q$, so one must say “modulo central units.” Over $\mathbf Q$, the center contributes only $\{\pm1\}$ and the full unit group of a definite order is finite.

### 13.4 What fails without definiteness

If $B$ splits at a real place, $B_v^\times/F_v^\times$ is noncompact. The ideal class set is still finite by Theorem 13.1, but the full archimedean quotient is no longer a finite discrete object. Its continuous geometry is essential in the theory of classical or Hilbert modular forms.

Thus two different assertions must not be conflated:

- finite one-sided ideal class sets exist for orders in quaternion algebras over any number field;
- the later finite-set model for weight-zero quaternionic automorphic forms uses total definiteness to eliminate noncompact archimedean directions.

## 14. Eichler compact opens and concrete level

### 14.1 From a local order to a local group

At a split finite place, fix an isomorphism $B_v\cong M_2(F_v)$. For the standard Eichler order

$$
\mathcal E_n=
\begin{pmatrix}
R_v&R_v\\
\pi_v^nR_v&R_v
\end{pmatrix},
$$

its unit group is

$$
K_0(\mathfrak p_v^n)
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{GL}_2(R_v):
c\in\mathfrak p_v^nR_v
\right\}.
$$

The determinant must be a unit; membership of all four entries in the displayed order alone is not enough for invertibility in the order. For $n=0$ this is $\operatorname{GL}_2(R_v)$. For $n=1$ it preserves a line in the residue plane. For general $n$ it preserves the length-$n$ lattice chain from Chapter 6.

At a division place, the maximal compact subgroup is

$$
\mathcal O_{D_v}^\times=\ker\bigl(w_{D_v}:D_v^\times\to\tfrac12\mathbf Z\bigr).
$$

There is no $K_0$-depth arising from an Eichler intersection there.

### 14.2 The global Eichler level subgroup

Let $\mathcal O$ be an Eichler order of level $\mathfrak N$, prime to $\mathfrak d(B)$. Its compact open unit group is

$$
K(\mathcal O)=\widehat{\mathcal O}^\times
=\prod_{v<\infty}\mathcal O_v^\times.
$$

After choosing split identifications compatible with the local standard forms,

$$
K(\mathcal O)_v=
\begin{cases}
K_0(\mathfrak p_v^{v(\mathfrak N)}),
&v\nmid\mathfrak d(B),\\
\mathcal O_{D_v}^\times,
&v\mid\mathfrak d(B).
\end{cases}
$$

At a split place not dividing $\mathfrak N$, the first line is simply $\operatorname{GL}_2(R_v)$. Thus only finitely many factors differ from the standard maximal compact.

This group is sometimes denoted $K_0(\mathfrak N)$ once $B$ and the local matrix identifications are understood. The notation conceals choices: another Eichler order in the same genus gives an adelically conjugate compact open, while a globally conjugate order gives conjugacy by $B^\times$.

### 14.3 What the unit group remembers

In the standard split model, the embedded unit group remembers the level exponent. Indeed, $K_0(\mathfrak p_v^n)$ consists of integral invertible matrices whose lower-left entries have valuation at least $n$, and the unipotent matrix with lower-left entry $\pi_v^n$ shows that this bound is sharp. In the division case, the unique maximal compact subgroup is the value-zero part of $D_v^\times$, and adjoining $0$ and the positive valuation layers recovers the valuation ring.

This does not justify a general assertion that an abstract unit group determines an additive order, or even that an order is always additively generated by its units. In residue characteristic two, for example, the units of the edge order reduce to upper triangular matrices with both diagonal entries equal to $1$, so their additive span does not recover the whole reduced order. The safe statement is that, after fixing the ambient local algebra and the standard maximal-order coordinates, the displayed $K_0$ subgroup records the same exponent $n$ as the Eichler order.

Nevertheless, the conceptual direction in this book is

$$
\text{order}\longrightarrow\text{unit group}.
$$

An additive order supports ideals, traces, and discriminants; its units alone do not visibly retain those constructions. Later automorphic theory starts from the group, but its arithmetic meaning comes from the order behind it.

### 14.4 Change of level

If $\mathfrak N\mid\mathfrak N'$ and compatible standard local models are chosen, then

$$
K_0(\mathfrak N')\subset K_0(\mathfrak N).
$$

The direction is inverse: a larger level ideal imposes a deeper congruence and gives a smaller compact open group. Likewise,

$$
\mathcal E_0(\mathfrak N')\subset\mathcal E_0(\mathfrak N)
$$

in the standard split model. Their reduced discriminants move in the same direction as the level:

$$
\mathfrak d(\mathcal E_0(\mathfrak N'))
=\mathfrak d(B)\mathfrak N'.
$$

One should not assert such literal inclusions for arbitrarily chosen globally conjugate models; only after compatible choices do the local matrix conditions nest.

## 15. Explicit arithmetic over $\mathbf Q$

### 15.1 The maximal matrix order has one class

Let $B=M_2(\mathbf Q)$ and $\mathcal O=M_2(\mathbf Z)$. The adelic class set is

$$
\operatorname{GL}_2(\mathbf Q)
\backslash\operatorname{GL}_2(\mathbf A_f)
/\operatorname{GL}_2(\widehat{\mathbf Z}).
$$

It has one element. To prove this concretely, let $g\in\operatorname{GL}_2(\mathbf A_f)$ and form the lattice

$$
L=\mathbf Q^2\cap g\widehat{\mathbf Z}^{\,2}.
$$

It is a rank-two $\mathbf Z$-lattice in $\mathbf Q^2$, so choose a rational basis and let $b\in\operatorname{GL}_2(\mathbf Q)$ carry $\mathbf Z^2$ onto $L$. Completion gives

$$
b\widehat{\mathbf Z}^{\,2}=g\widehat{\mathbf Z}^{\,2},
$$

whence $b^{-1}g\in\operatorname{GL}_2(\widehat{\mathbf Z})$. Thus $g$ lies in the trivial double coset.

Under the ideal correspondence, every locally principal right $M_2(\mathbf Z)$-ideal is therefore principal up to left multiplication. This conclusion uses that every rank-two lattice over $\mathbf Z$ is free. It is not a declaration that arbitrary one-sided ideals in arbitrary matrix orders are principal.

### 15.2 Matrix Eichler level $N$

For

$$
\mathcal E_0(N)=
\begin{pmatrix}
\mathbf Z&\mathbf Z\\
N\mathbf Z&\mathbf Z
\end{pmatrix},
$$

the finite compact open is

$$
K_0(N)=
\left\{g\in\operatorname{GL}_2(\widehat{\mathbf Z}):
g_{21}\in N\widehat{\mathbf Z}
\right\}.
$$

At $p^n\Vert N$, its $p$-component stabilizes the chain

$$
\mathbf Z_p^2\supset
\mathbf Z_pe_1+p\mathbf Z_pe_2\supset\cdots\supset
\mathbf Z_pe_1+p^n\mathbf Z_pe_2.
$$

The reduced discriminant is $N$, and the double set

$$
\operatorname{GL}_2(\mathbf Q)
\backslash\operatorname{GL}_2(\mathbf A_f)/K_0(N)
$$

may again be interpreted through lattices equipped with the indicated cyclic local flag. Over $\mathbf Q$ the finite double quotient is still controlled by elementary divisors, but at infinity the split group is noncompact. Thus it is not the finite definite automorphic model that Book 35 will use.

For $N=p$, the extra datum is a line in $L/pL$. For $N=p^2$, it is a length-two cyclic filtration, not merely a line. This makes the squarefree/nonsquarefree distinction tangible.

### 15.3 The Hurwitz maximal order

Return to

$$
B=(-1,-1)_{\mathbf Q},
\qquad
\mathcal H=\mathbf Z+\mathbf Zi+\mathbf Zj+
\mathbf Z\frac{1+i+j+ij}{2}.
$$

The algebra is ramified at $2$ and infinity, so it is definite and $\mathfrak d(B)=2$. We computed $\mathfrak d(\mathcal H)=2$, hence $\mathcal H$ is maximal. Locally,

$$
\mathcal H_p\cong M_2(\mathbf Z_p)\quad(p\ne2),
$$

while $\mathcal H_2$ is the unique maximal order in the division algebra $B_2$.

The unit group consists of the $24$ elements of reduced norm one:

$$
\{\pm1,\pm i,\pm j,\pm ij\}
$$

together with the sixteen half-integral quaternions

$$
\frac{\pm1\pm i\pm j\pm ij}{2}.
$$

Every choice of signs occurs. Their norm is one. Definiteness ensures there are no further units, since an integral unit must have positive integral norm one and the unit sphere meets the Hurwitz lattice in exactly these points.

### 15.4 The Hurwitz class set

The Hurwitz order has right ideal class number one:

$$
\operatorname{Cl}_r(\mathcal H)=\{[\mathcal H]\}.
$$

One concrete proof uses its norm-Euclidean property. The Hurwitz lattice has covering radius strictly less than one for the quadratic norm: for every $x\in B\otimes_\mathbf Q\mathbf R$, there is $q\in\mathcal H$ with

$$
\operatorname{Nrd}(x-q)<1.
$$

Apply division with remainder to an element of minimal positive norm in a nonzero integral right ideal. If $0\ne a\in I$ has minimal norm and $x\in I$, approximate $a^{-1}x$ by $q\in\mathcal H$. Then

$$
x-aq\in I
$$

because $I$ is stable under right multiplication by $\mathcal H$. Its norm is

$$
\operatorname{Nrd}(a)\operatorname{Nrd}(a^{-1}x-q)
<\operatorname{Nrd}(a)
$$

unless the remainder is zero. Minimality forces $x=aq$. Hence $I=a\mathcal H$ is principal. The orientation is essential: for a right ideal one approximates $a^{-1}x$ and subtracts $aq$.

Thus

$$
B^\times\backslash\widehat B^\times/
\widehat{\mathcal H}^{\times}
$$

has one element. The example is special. Definite quaternion orders can have class number greater than one, and maximal orders can have more than one global conjugacy type. Definiteness guarantees finiteness, not principality.

### 15.5 Adding odd Eichler level to the definite algebra

Let $N$ be odd. Since $(N,\mathfrak d(B))=1$, choose an Eichler order $\mathcal H_0(N)$ whose local component is maximal at $2$, standard of level $p^{v_p(N)}$ at each $p\mid N$, and maximal elsewhere. Then

$$
\mathfrak d(\mathcal H_0(N))=2N.
$$

Its compact open has local factors

$$
K_p=
\begin{cases}
\mathcal H_2^\times,&p=2,\\
K_0(p^{v_p(N)}),&p\mid N,\\
\operatorname{GL}_2(\mathbf Z_p),&p\nmid2N.
\end{cases}
$$

There is no Eichler level factor at $2$ because the algebra is division there. An expression such as “level $2N$” would conflate algebra discriminant with Eichler level; the order has reduced discriminant $2N$ but level $N$.

The resulting double-coset set is finite. It need not remain a singleton as $N$ grows. Its elements are locally principal right ideal classes, and their left orders supply the stabilizers that appear in the finite model of the next book.

## 16. The integral--adelic dictionary

### 16.1 One table of translations

The theory can now be compressed without being obscured. For a quaternion algebra $B/F$ and an order $\mathcal O$, the principal translations are:

| Integral object | Local description | Finite-adelic description |
|---|---|---|
| full lattice $L\subset B$ | free $R_v$-lattices $L_v$, standard almost everywhere | compact open $\widehat R$-lattice $\widehat L\subset\widehat B$ |
| order $\mathcal O$ | orders $\mathcal O_v$ in $B_v$ | compact open ring $\widehat{\mathcal O}$ |
| units of an order | $\mathcal O_v^\times$ | compact open $\widehat{\mathcal O}^\times\subset\widehat B^\times$ |
| maximal order | maximal at every finite $v$ | maximal compact factors locally |
| Eichler order of level $\mathfrak N$ | $\mathcal E_{n_v}$ at split $v$, maximal at division $v$ | $K_0(\mathfrak p_v^{n_v})$ and $\mathcal O_{D_v}^\times$ factors |
| locally principal right ideal $I$ | $I_v=g_v\mathcal O_v$ | $g\widehat{\mathcal O}$ |
| ideal equivalence $I\sim bI$ | one rational left multiplier | left quotient by $B^\times$ |
| change of local generator | $g_v\mapsto g_vu_v$ | right quotient by $\widehat{\mathcal O}^\times$ |
| right ideal class set | local generators modulo both changes | $B^\times\backslash\widehat B^\times/\widehat{\mathcal O}^\times$ |

The left/right positions in the final row are not typography: they encode the convention that $g\widehat{\mathcal O}$ is a right ideal.

### 16.2 The discriminant dictionary

Three related invariants must remain distinct:

$$
\operatorname{disc}(\mathcal O)
=\mathfrak d(\mathcal O)^2
$$

is the determinant ideal of the rank-four reduced-trace pairing;

$$
\mathfrak d(B)=\prod_{v\in\operatorname{Ram}_f(B)}\mathfrak p_v
$$

is squarefree and records finite division places; and for an Eichler order,

$$
\mathfrak d(\mathcal O)=\mathfrak d(B)\mathfrak N(\mathcal O),
\qquad
(\mathfrak d(B),\mathfrak N(\mathcal O))=1.
$$

At a split place, $v(\mathfrak d(\mathcal O))$ is the tree distance between the defining maximal orders. At a division place, it is one for the maximal order and does not represent level. Under inclusion, reduced discriminant changes by the index; under conjugation, it is unchanged.

### 16.3 The ideal dictionary

For a locally principal proper right ideal $I$:

$$
\mathcal O_R(I)=\mathcal O,
\qquad
\widehat I=g\widehat{\mathcal O},
\qquad
\widehat{\mathcal O_L(I)}=g\widehat{\mathcal O}g^{-1}.
$$

Its inverse has the opposite variance, and its norm ideal is

$$
\operatorname{nrd}(I)
=\prod_v\mathfrak p_v^{v(\operatorname{Nrd}(g_v))}.
$$

Replacing $g$ by $bgu$ changes the ideal by $I\mapsto bI$, conjugates the left order by $b$, and multiplies the norm ideal by $(\operatorname{Nrd}(b))$; the right unit $u$ changes none of them. Composable invertible ideals multiply in the order

$$
(\mathcal O_1,\mathcal O_2)\cdot
(\mathcal O_2,\mathcal O_3)
\longrightarrow
(\mathcal O_1,\mathcal O_3).
$$

This is the safe form of quaternionic ideal arithmetic.

### 16.4 The finite input for the next book

Suppose $F$ is totally real, $B$ is totally definite, and $\mathcal O$ is an Eichler order of level $\mathfrak N$ prime to $\mathfrak d(B)$. Set

$$
K=\widehat{\mathcal O}^\times.
$$

Then:

1. $K$ is a compact open subgroup of $\widehat B^\times$;
2. its split local factors are concrete $K_0$-groups and its division factors are maximal unit groups;
3. the double quotient

   $$
   X_K=B^\times\backslash\widehat B^\times/K
   $$

   is finite;
4. choosing representatives $g_1,\dots,g_h$ identifies their stabilizers with

   $$
   \Gamma_i=B^\times\cap g_iKg_i^{-1}
   =\mathcal O_L(I_i)^\times;
   $$

5. modulo central units, every $\Gamma_i$ is finite.

These statements are precisely the integral and finite-combinatorial input needed to define functions on $X_K$ with prescribed algebraic behavior at infinity. No automorphic form or Hecke operator has been defined here; the present endpoint is the arithmetic set on which those later structures will act.

### 16.5 Conclusion

An order turns a quaternion algebra from a rational object into an arithmetic one. Its full lattice supplies denominators, its multiplicative closure supplies congruences, and its trace pairing measures the cost of enlargement. Maximal orders realize the minimum possible discriminant: unit at a split finite place and the prime itself at a division place. In a split algebra they are endomorphism rings of lattices; in a division algebra the valuation selects one unique maximal order.

Intersecting two maximal orders introduces exactly one local integer, the distance between two vertices in the elementary lattice tree. Those integers assemble into the Eichler level, while the division places remain recorded separately by the algebra discriminant. This separation yields the formula

$$
\mathfrak d(\mathcal O)=\mathfrak d(B)\mathfrak N
$$

with coprime factors and prevents ramification from being mistaken for congruence depth.

One-sided ideals then connect integral and adelic viewpoints. A locally principal right ideal is a family $g_v\mathcal O_v$, its left order is the conjugate family $g_v\mathcal O_vg_v^{-1}$, and its norm ideal is read from $\operatorname{Nrd}(g_v)$. Global equivalence is left multiplication by $B^\times$; changing local generators is right multiplication by $\widehat{\mathcal O}^\times$. The resulting exact classification

$$
\operatorname{Cl}_r(\mathcal O)
\cong
B^\times\backslash\widehat B^\times/
\widehat{\mathcal O}^\times
$$

turns ideal arithmetic into a finite double-coset set. For totally definite $B$, compactness at infinity explains why this set and its stabilizers are especially concrete. The ambient algebra from Book 33, the restricted products from Book 4, and the integral structures developed here have therefore converged on one reusable object: a compact-open level inside $\widehat B^\times$ together with the finite arithmetic quotient it defines.
