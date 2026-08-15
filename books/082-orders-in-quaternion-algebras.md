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
15. [Unit groups and integral norm maps](#15-unit-groups-and-integral-norm-maps)
    - [Why the units deserve separate study](#151-why-the-units-deserve-separate-study)
    - [The radical filtration of a local order](#152-the-radical-filtration-of-a-local-order)
    - [Split maximal and Eichler units](#153-split-maximal-and-eichler-units)
    - [Units in the division order](#154-units-in-the-division-order)
    - [Surjectivity of the local reduced norm](#155-surjectivity-of-the-local-reduced-norm)
    - [Global units, norm-one units, and positivity](#156-global-units-norm-one-units-and-positivity)
16. [Explicit arithmetic over $\mathbf Q$](#16-explicit-arithmetic-over-mathbf-q)
    - [The maximal matrix order has one class](#161-the-maximal-matrix-order-has-one-class)
    - [Matrix Eichler level $N$](#162-matrix-eichler-level-n)
    - [The Hurwitz maximal order](#163-the-hurwitz-maximal-order)
    - [The Hurwitz class set](#164-the-hurwitz-class-set)
    - [Adding odd Eichler level to the definite algebra](#165-adding-odd-eichler-level-to-the-definite-algebra)
17. [Quadratic orders and optimal embeddings](#17-quadratic-orders-and-optimal-embeddings)
    - [From field embeddings to integral embeddings](#171-from-field-embeddings-to-integral-embeddings)
    - [Quadratic orders and conductors](#172-quadratic-orders-and-conductors)
    - [Optimality as an intersection condition](#173-optimality-as-an-intersection-condition)
    - [The split local lattice-pair normal form](#174-the-split-local-lattice-pair-normal-form)
    - [The division-place criterion](#175-the-division-place-criterion)
    - [Local--global optimality and selectivity](#176-local--global-optimality-and-selectivity)
    - [Embedding classes as double quotients](#177-embedding-classes-as-double-quotients)
    - [Examples and counterexamples](#178-examples-and-counterexamples)
18. [Reduced-norm packets](#18-reduced-norm-packets)
    - [The norm quotient attached to a level](#181-the-norm-quotient-attached-to-a-level)
    - [The norm map on an ideal class set](#182-the-norm-map-on-an-ideal-class-set)
    - [What reduced norm does not classify](#183-what-reduced-norm-does-not-classify)
19. [Finite double-coset sets for definite quaternionic forms](#19-finite-double-coset-sets-for-definite-quaternionic-forms)
    - [The finite arithmetic skeleton](#191-the-finite-arithmetic-skeleton)
    - [Representatives, ideals, and stabilizers](#192-representatives-ideals-and-stabilizers)
    - [Central quotients and effective stabilizers](#193-central-quotients-and-effective-stabilizers)
    - [Norm packets](#194-norm-packets)
    - [Changing level](#195-changing-level)
    - [What is and is not canonical](#196-what-is-and-is-not-canonical)
20. [The integral--adelic dictionary](#20-the-integral--adelic-dictionary)
    - [One table of translations](#201-one-table-of-translations)
    - [The discriminant dictionary](#202-the-discriminant-dictionary)
    - [The ideal dictionary](#203-the-ideal-dictionary)
    - [The finite input for the next book](#204-the-finite-input-for-the-next-book)
    - [Conclusion](#205-conclusion)

## 1. From a rational algebra to integral arithmetic

### 1.1 Why the algebra is not enough

Book 77 classified a quaternion algebra $B$ over a number field $F$ by its local splitting behavior. That classification answers which ambient algebra we have, but it does not yet supply a notion of congruence, denominator, or level inside $B$. All of those are integral questions. Just as the field $F$ acquires arithmetic texture only after one singles out its ring of integers $R=\mathcal O_F$, the four-dimensional $F$-vector space $B$ acquires arithmetic texture only after one singles out a full $R$-lattice compatible with multiplication.

There is no canonical choice in general. Even $M_2(F)$ contains many nonconjugate-looking integral subrings, and one fixed quaternion algebra supports levels at arbitrarily large ideals. This variability is useful: later, a compact open subgroup of the finite adelic group will encode the chosen integral structure. The present book develops the algebraic side of that dictionary.

Throughout, $F$ is a number field, $R=\mathcal O_F$, and $B$ is a quaternion algebra over $F$. A finite place $v$ corresponds to a prime $\mathfrak p_v$ of $R$. We write

$$
F_v,\qquad R_v,\qquad \mathfrak p_vR_v=(\pi_v),\qquad B_v=B\otimes_FF_v
$$

for the completion, its valuation ring, a chosen uniformizer, and the completed algebra. Reduced trace, reduced norm, and canonical conjugation are denoted by $\operatorname{Trd}$, $\operatorname{Nrd}$, and $x\mapsto\bar x$. They are the degree-two invariants of Book 77, not the trace and determinant of the four-dimensional left regular representation.

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

For comparison only, this construction parallels the discriminant of a finite field extension developed in Book 3; no result from that book is used here, and the two invariants must not be identified. A field discriminant uses the ordinary field trace on an integral closure and is the norm of a different. Here the ambient object is already a four-dimensional central simple algebra, the pairing uses reduced trace, and the variable integral object is the order inside that fixed algebra. The common square-index behavior comes from change of lattice; it does not assert the existence of a commutative different for an arbitrary quaternion order.

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

The theorem explains the terminology “reduced discriminant.” The rank-four trace determinant of a maximal order is $\mathfrak d(B)^2$, while its square root recovers exactly the algebra ramification ideal introduced in Book 77.

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

Book 77 found $\mathfrak d(B)=(2)$, so Theorem 3.2 shows that $\mathcal H$ is maximal and $\mathcal L$ is not. This example cleanly separates the discriminant of a presentation lattice, the reduced discriminant of an order, and the ramification discriminant of the algebra.

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

To prove that $M_2(A)$ is maximal, let $\Lambda$ be an order containing it and take $x=(x_{ij})\in\Lambda$. Multiplication by matrix units gives

$$
E_{ii}xE_{jj}=x_{ij}E_{ij}\in\Lambda,
\qquad
x_{ij}E_{ij}E_{ji}=x_{ij}E_{ii}\in\Lambda.
$$

Every element of an order has integral reduced trace, so $x_{ij}=\operatorname{Trd}(x_{ij}E_{ii})$ lies in $A$. Thus $x\in M_2(A)$ and $\Lambda=M_2(A)$. This proves the theorem.

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

Finite adeles are formed by requiring integrality at almost every place. Applying this construction to the four-dimensional vector space $B$, and fixing any order $\mathcal O$, gives the finite adelic algebra

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

**Theorem 13.1 (finiteness).** For every order $\mathcal O$ in a quaternion algebra $B$ over a number field $F$, the class set

$$
B^\times\backslash\widehat B^\times/
\widehat{\mathcal O}^\times
$$

is finite.

No definiteness hypothesis is needed. The proof separates the two possible rational algebras and then passes from a maximal order to the given order by a finite-index argument.

**Proof strategy.** If $B$ is division, every nonzero vector is invertible, so Minkowski reduction supplies a short element with which to normalize an ideal into one of finitely many bounded over-lattices of $\mathcal O$. If $B$ is split, Morita equivalence reduces maximal-order classes to Steinitz classes of rank-two projective $R$-modules. A finite unit-index argument then handles every suborder.

**Proof.** Suppose first that $B$ is a division algebra. Fix a Euclidean norm on

$$
B_\infty=B\otimes_{\mathbf Q}\mathbf R
$$

and compatible Lebesgue measure. If $d=[F:\mathbf Q]$, Minkowski's convex-body theorem gives, for every fractional right ideal $I$, a nonzero $a\in I$ such that

$$
\lVert a\rVert\le C_1\operatorname{covol}(I)^{1/(4d)}.
$$

The absolute determinant of left multiplication by $a$ on the $4d$-dimensional real vector space $B_\infty$ is

$$
\left|N_{F/\mathbf Q}(\operatorname{Nrd}(a))\right|^2.
$$

It is a homogeneous polynomial of degree $4d$ in the real coordinates of $a$, so its absolute value is bounded on the Euclidean unit sphere. Consequently

$$
\left|N_{F/\mathbf Q}(\operatorname{Nrd}(a))\right|^2
\le C_2\lVert a\rVert^{4d}
\le C_3\operatorname{covol}(I).
$$

Division makes $a$ invertible. Put $J=a^{-1}I$. Since $a\mathcal O\subset I$, one has $\mathcal O\subset J$, while the determinant formula gives

$$
\operatorname{covol}(J)
=\left|N_{F/\mathbf Q}(\operatorname{Nrd}(a))\right|^{-2}
\operatorname{covol}(I)
\ge C_3^{-1}.
$$

Hence

$$
|J/\mathcal O|
=\frac{\operatorname{covol}(\mathcal O)}
{\operatorname{covol}(J)}
$$

is bounded independently of the class of $I$. There are only finitely many over-lattices of $\mathcal O$ of bounded index: the exponent of each finite group $J/\mathcal O$ is bounded, so all such $J$ lie between $\mathcal O$ and one fixed fractional multiple of it. Thus the division case is finite.

Now suppose $B=M_2(F)$ and let $\mathcal M$ be a maximal order. Choose a rank-two lattice $P_0\subset F^2$ and put $P=\mathcal M P_0$. Then $P$ is a rank-two projective $R$-lattice stabilized by $\mathcal M$, so

$$
\mathcal M\subset\operatorname{End}_R(P).
$$

Maximality makes this an equality. Morita equivalence sends a locally principal right $\mathcal M$-ideal $I$ to the rank-two projective module $I\otimes_{\mathcal M}P$, and its inverse is $Q\mapsto\operatorname{Hom}_R(P,Q)$. It identifies ideal equivalence with module isomorphism: a right $\mathcal M$-module isomorphism $I\to J$ extends over $F$ to an endomorphism of the regular right $B$-module, hence is left multiplication by an element $b\in B^\times$ and gives $J=bI$; the converse is immediate. To recall the needed Dedekind-module classification, a pseudobasis writes every rank-two projective module as $\mathfrak a\oplus\mathfrak b$ for fractional ideals $\mathfrak a,\mathfrak b$, and elementary pseudobasis changes give

$$
\mathfrak a\oplus\mathfrak b
\cong R\oplus\mathfrak a\mathfrak b.
$$

The ideal class of $\mathfrak a\mathfrak b$, equivalently the determinant class, is unchanged by isomorphism and completely determines it. These classes form the finite ideal class group of $F$. The maximal-order class set is therefore finite.

Finally choose a maximal order $\mathcal M\supset\mathcal O$. The inclusion

$$
\widehat{\mathcal O}^\times
\subset\widehat{\mathcal M}^\times
$$

has finite index. Indeed, the local orders agree away from the finite support of $\mathcal M/\mathcal O$, and at each remaining place the smaller unit group is open in the compact larger unit group. The natural map from the $\mathcal O$-class set to the $\mathcal M$-class set has fibers that are quotients of the finite set

$$
\widehat{\mathcal M}^\times/
\widehat{\mathcal O}^\times.
$$

The source is therefore finite. By Theorem 12.1 it is exactly the stated double quotient. $\square$

The same argument gives the form needed for arbitrary level subgroups.

**Corollary 13.2.** For every compact open subgroup $K\subset\widehat B^\times$, the set

$$
B^\times\backslash\widehat B^\times/K
$$

is finite.

**Proof.** Fix an order $\mathcal O$ and put $U=K\cap\widehat{\mathcal O}^\times$. The intersection of two compact open subgroups has finite index in each. The quotient with right level $U$ maps to the finite $\widehat{\mathcal O}^\times$-quotient with fibers bounded by $[\widehat{\mathcal O}^\times:U]$, and it surjects onto the quotient with right level $K$. $\square$

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

This proof explains why total definiteness is especially valuable later. General class-set finiteness does not require it, but definiteness makes the archimedean projective quotient compact, so no continuous archimedean parameter survives. Quaternionic automorphic spaces at finite level can then be built from a finite set with finite stabilizers modulo central units.

### 13.3 Stabilizers in the definite case

For a representative ideal $I$, the stabilizer is $\mathcal O_L(I)^\times$. If $B$ is totally definite, the group

$$
\mathcal O_L(I)^\times/R^\times
$$

is finite. Indeed, after scaling by a central unit, its image at infinity lies in a compact norm-one sphere, while it remains in an arithmetic lattice. A compact set meets a lattice in finitely many points.

Here is the unit-scaling step precisely. For $u\in\mathcal O_L(I)^\times$, the reduced norm is a totally positive unit of $R$. The quotient of the totally positive unit group by squares of units is finite. Choose representatives $\eta_1,\ldots,\eta_s$. After multiplying $u$ by the inverse of a suitable central unit, its reduced norm is one of the $\eta_j$. At every real place it therefore lies on one of finitely many fixed norm spheres. Those spheres are compact, while the integrality conditions put every representative in the fixed lattice $\mathcal O_L(I)\subset B_\infty$. A bounded subset of a Minkowski space meets a fixed lattice in finitely many points, leaving only finitely many representatives modulo $R^\times$.

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

This does not justify a general assertion that an abstract unit group determines an additive order, or even that an order is always additively generated by its units. When the residue field is $\mathbf F_2$, for example, the units of the edge order reduce to upper triangular matrices with both diagonal entries equal to $1$, so their additive span does not recover the whole reduced order. The safe statement is that, after fixing the ambient local algebra and the standard maximal-order coordinates, the displayed $K_0$ subgroup records the same exponent $n$ as the Eichler order.

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

## 15. Unit groups and integral norm maps

### 15.1 Why the units deserve separate study

An order is additive enough to carry discriminants and multiplicative enough to carry ideals. Its unit group is the part visible to finite-adelic quotients. Passing from an order to its units therefore loses information, but it retains exactly the invertible integral changes of coordinates. To use those changes safely, one must know how units reduce, how they are filtered near the identity, and which central units occur as reduced norms.

Let $K$ be a nonarchimedean local field with valuation ring $A$, maximal ideal $\mathfrak p$, and finite residue field $k$. Let $C/K$ be a quaternion algebra and $\Lambda\subset C$ an $A$-order. An element $x\in\Lambda$ is a unit of $\Lambda$ if and only if

$$
\operatorname{Nrd}(x)\in A^\times.
$$

Indeed, a unit has unit reduced norm by multiplicativity. Conversely, every order is stable under canonical conjugation, so if the reduced norm is a unit then

$$
x^{-1}=\frac{\bar x}{\operatorname{Nrd}(x)}\in\Lambda.
$$

This criterion is stronger than invertibility in $C$. A matrix in $M_2(A)$ with determinant $\pi$ is invertible over $K$ but not in $M_2(A)$. The order remembers whether the inverse is integral.

Globally the same argument gives

$$
\mathcal O^\times
=\{x\in\mathcal O:\operatorname{Nrd}(x)\in R^\times\}.
$$

Thus the reduced norm maps local units to $A^\times$ and global units to $R^\times$. Surjectivity is a further assertion, not part of the criterion.

### 15.2 The radical filtration of a local order

Reduction of a maximal matrix order gives a full matrix algebra, while reduction of a positive-level Eichler order gives an upper triangular algebra and reduction of a division order gives a quadratic field. The Jacobson radical provides one language covering all three cases.

Let $J=\operatorname{rad}(\Lambda)$. Since $\Lambda$ is finite over the complete local ring $A$, it is semilocal and complete for the $J$-adic topology. Reduction gives an exact sequence

$$
1\longrightarrow 1+J
\longrightarrow\Lambda^\times
\longrightarrow(\Lambda/J)^\times
\longrightarrow1.
$$

The only point needing proof is surjectivity. If the class of $x\in\Lambda$ is invertible modulo $J$, choose $y$ whose class is its inverse. Then both $1-xy$ and $1-yx$ lie in $J$. By the defining property of the Jacobson radical, $xy$ and $yx$ are units. It follows that $x$ has both a left and a right inverse, which agree; hence $x\in\Lambda^\times$.

The congruence subgroups

$$
U_\Lambda^m=1+J^m\qquad(m\ge1)
$$

measure successively finer motion near the identity. Multiplication linearizes on each layer:

$$
(1+x)(1+y)\equiv1+x+y\pmod{J^{m+1}}
$$

for $x,y\in J^m$, because $J^{2m}\subset J^{m+1}$. Therefore

$$
U_\Lambda^m/U_\Lambda^{m+1}
\cong (J^m/J^{m+1},+).
$$

This is an isomorphism of groups, not usually of rings. It shows that every sufficiently small multiplicative question begins as a finite additive question. The layers need not all have the same dimension over $k$; the shape of the order controls them.

### 15.3 Split maximal and Eichler units

For the maximal split order $\Lambda=M_2(A)$,

$$
J=\pi M_2(A),
\qquad
\Lambda/J\cong M_2(k),
$$

and the reduction sequence becomes

$$
1\longrightarrow1+\pi M_2(A)
\longrightarrow\operatorname{GL}_2(A)
\longrightarrow\operatorname{GL}_2(k)
\longrightarrow1.
$$

Surjectivity can also be seen by lifting the four entries of an invertible residue matrix: its determinant lifts to a unit.

Now take the positive-level Eichler order

$$
\mathcal E_n=
\begin{pmatrix}
A&A\\
\pi^nA&A
\end{pmatrix},
\qquad n\ge1.
$$

Its radical is

$$
J_n=
\begin{pmatrix}
\pi A&A\\
\pi^nA&\pi A
\end{pmatrix},
$$

and diagonal reduction identifies

$$
\mathcal E_n/J_n\cong k\times k.
$$

Consequently a matrix in $\mathcal E_n$ is a unit precisely when both diagonal entries are nonzero modulo $\pi$. Equivalently,

$$
\mathcal E_n^\times
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{GL}_2(A):c\in\pi^nA
\right\}.
$$

The two residue characters $a\bmod\pi$ and $d\bmod\pi$ remember the two endpoints of the stabilized segment. For $n=1$ the entire order is hereditary, but this radical calculation alone does not extend heredity to $n>1$. It only describes units and their first congruence layer.

The determinant supplies the reduced norm in both split models. It is surjective on units, because

$$
u\longmapsto
\begin{pmatrix}u&0\\0&1\end{pmatrix}
$$

embeds $A^\times$ in $\mathcal E_n^\times$ for every $n\ge0$. This elementary diagonal lift is one reason Eichler level imposes no local obstruction on the norm of a unit.

### 15.4 Units in the division order

Let $D/K$ be the quaternion division algebra, with maximal order $\mathcal O_D$, radical $\mathfrak P_D=\Pi\mathcal O_D$, and unramified quadratic residue field $k_2$. Chapter 6 gives

$$
\mathcal O_D/\mathfrak P_D\cong k_2.
$$

The unit sequence is therefore

$$
1\longrightarrow1+\mathfrak P_D
\longrightarrow\mathcal O_D^\times
\longrightarrow k_2^\times
\longrightarrow1.
$$

In cyclic coordinates $D=L\oplus L\Pi$, the image of $a+b\Pi$ modulo $\mathfrak P_D$ is the residue of $a$. The reduced norm has residue shadow

$$
\overline{\operatorname{Nrd}(a+b\Pi)}
=N_{k_2/k}(\bar a).
$$

Since finite-field norm is surjective, every residue unit of $A$ is already the residue of a reduced norm. Deeper principal units also occur as norms, but their surjectivity is most cleanly deduced from the norm theorem for the whole division algebra in the next section.

The valuation exact sequence reads

$$
1\longrightarrow\mathcal O_D^\times
\longrightarrow D^\times
\xrightarrow{\,2w_D\,}\mathbf Z
\longrightarrow0,
$$

where $2w_D(\Pi)=1$. Thus $D^\times$ consists of radical powers multiplied by integral units. This is the division analogue of

$$
\operatorname{GL}_2(K)=
\bigcup_{r\in\mathbf Z}
\{g:v(\det g)=r\},
$$

but there is only one maximal order rather than a tree of them.

### 15.5 Surjectivity of the local reduced norm

The ambient local norm theorem from the preceding book states that for every nonarchimedean local field $K$ and every quaternion algebra $C/K$,

$$
\operatorname{Nrd}(C^\times)=K^\times.
$$

For the split algebra this is the surjectivity of determinant. For the division algebra it is a genuine theorem: norms from any one quadratic maximal subfield have index two, but allowing all elements of $D$ removes that obstruction.

The integral consequence is exact.

**Proposition 15.1 (local unit norms).** Let $\Lambda$ be either a maximal order or an Eichler order in a quaternion algebra over a nonarchimedean local field. Then

$$
\operatorname{Nrd}(\Lambda^\times)=A^\times.
$$

**Proof strategy.** Use an explicit diagonal matrix in the split case. In the division case, lift a prescribed unit using ambient norm surjectivity and observe that its norm valuation forces the lift to have division value zero.

**Proof.** At a split place, conjugate $\Lambda$ to $\mathcal E_n$. The diagonal matrix $\operatorname{diag}(u,1)$ lies in $\mathcal E_n^\times$ and has determinant $u$.

At a division place, an Eichler order is the maximal order $\mathcal O_D$. Given $u\in A^\times$, choose $x\in D^\times$ with $\operatorname{Nrd}(x)=u$. Then

$$
w_D(x)=\frac12v(u)=0,
$$

so $x\in\mathcal O_D^\times$. The reverse containment follows from the unit criterion. $\square$

The Eichler hypothesis is important. An arbitrary suborder can have a smaller norm image on units. For example, extra congruence conditions on both diagonal entries of a split order can force its determinant into a proper subgroup of $A^\times$. Ambient norm surjectivity does not automatically preserve a chosen integral lattice.

For a global Eichler order $\mathcal O$, Proposition 15.1 yields

$$
\operatorname{Nrd}(\widehat{\mathcal O}^{\times})
=\widehat R^\times.
$$

This equality will simplify the norm quotient of its ideal class set. For a general compact open $K\subset\widehat B^\times$, the subgroup $\operatorname{Nrd}(K)\subset\mathbf A_{F,f}^\times$ must remain in the formulas.

### 15.6 Global units, norm-one units, and positivity

Define

$$
\mathcal O^1=\{u\in\mathcal O^\times:\operatorname{Nrd}(u)=1\}.
$$

The global reduced norm theorem says

$$
\operatorname{Nrd}(B^\times)=F_{B,+}^\times,
$$

where

$$
F_{B,+}^\times
=\{a\in F^\times:a>0
\text{ at every real place ramified in }B\}.
$$

Accordingly,

$$
\operatorname{Nrd}(\mathcal O^\times)
\subset R^\times\cap F_{B,+}^\times.
$$

Equality need not follow from the global norm theorem: a global element of the required norm may fail to be integral in the chosen order. What is automatic is that every square of a central unit occurs, because $a\in R^\times$ lies in $\mathcal O^\times$ and has reduced norm $a^2$. Hence

$$
(R^\times)^2
\subset\operatorname{Nrd}(\mathcal O^\times)
\subset R^\times\cap F_{B,+}^\times.
$$

The quotient of the rightmost group by $(R^\times)^2$ is finite. Thus the possible failure of integral norm surjectivity on global units is finite.

If $F$ is totally real and $B$ is totally definite, then $\mathcal O^1$ is finite. Under every real embedding the equation $\operatorname{Nrd}(u)=1$ places $u$ on a compact three-sphere, while $\mathcal O$ is a lattice in the product of the real quaternion spaces. A compact set meets that lattice in finitely many points. The same argument, combined with the finite quotient of totally positive units by squares, proves again that

$$
\mathcal O^\times/R^\times
$$

is finite.

Without total definiteness, $\mathcal O^1$ can be infinite. For $M_2(\mathbf Z)$ it contains $\operatorname{SL}_2(\mathbf Z)$. This counterexample explains why later stabilizers are finite only after the archimedean anisotropy hypothesis is imposed.

## 16. Explicit arithmetic over $\mathbf Q$

### 16.1 The maximal matrix order has one class

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

### 16.2 Matrix Eichler level $N$

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

may again be interpreted through lattices equipped with the indicated cyclic local flag. Over $\mathbf Q$ the finite double quotient is still controlled by elementary divisors, but at infinity the split group is noncompact. Thus it is not the finite definite automorphic model that Book 83 will use.

For $N=p$, the extra datum is a line in $L/pL$. For $N=p^2$, it is a length-two cyclic filtration, not merely a line. This makes the squarefree/nonsquarefree distinction tangible.

### 16.3 The Hurwitz maximal order

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

### 16.4 The Hurwitz class set

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

### 16.5 Adding odd Eichler level to the definite algebra

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

## 17. Quadratic orders and optimal embeddings

### 17.1 From field embeddings to integral embeddings

A quadratic field inside $B$ supplies a commutative direction in a noncommutative algebra. The preceding book answered the rational existence question: a quadratic field $L/F$ embeds in $B$ exactly when no place ramified in $B$ splits in $L$. Integral arithmetic asks a finer question. Given an order $S\subset L$ and an order $\mathcal O\subset B$, can the rational embedding be chosen so that $S$ is exactly the part of $L$ visible inside $\mathcal O$?

Merely requiring $S$ to map into $\mathcal O$ is too weak. If a larger quadratic order $S'\supsetneq S$ also maps into $\mathcal O$, then the embedding has silently forgotten the conductor of $S$. This matters whenever quadratic orders label special points, torus orbits, or arithmetic cycles: the conductor is part of the datum, not decoration.

Throughout this chapter, $L$ is a quadratic étale $F$-algebra. Thus $L$ is either a quadratic field or $F\times F$. Write $\mathcal O_L$ for the integral closure of $R$ in $L$; in the split case this is $R\times R$. An $R$-order $S\subset L$ is a full unital $R$-subring. We consider only $F$-algebra embeddings

$$
\iota:L\hookrightarrow B.
$$

When $B$ is division, $L$ must be a field. When $B$ is split, both possibilities occur.

### 17.2 Quadratic orders and conductors

The conductor records how far a quadratic order lies below the maximal one. Define

$$
\mathfrak f(S)
=\{a\in R:a\mathcal O_L\subset S\}.
$$

It is an integral ideal of $R$. Locally, if $A=R_v$ and

$$
\mathfrak f(S)A=(\pi^c),
$$

then every quadratic $A$-order has the form

$$
S_c=A+\pi^c\mathcal O_{L_v}.
$$

In the split case this means

$$
S_c
=\{(x,y)\in A\times A:x\equiv y\pmod{\pi^c}\}.
$$

The exponent $c=0$ gives the maximal order. Increasing $c$ makes the order smaller. This direction is opposite to inclusion of conductor ideals as sets: a larger exponent gives a smaller ideal and a smaller order.

The local normal form follows from the fact that $\mathcal O_{L_v}/A$ is cyclic as an $A$-module. Any intermediate full ring contains $A$ and corresponds to an $A$-submodule of this rank-one torsion-free quotient; over a DVR that submodule is generated by one power of $\pi$. Multiplication imposes no further restriction because

$$
(A+\pi^c\mathcal O_{L_v})^2
\subset A+\pi^c\mathcal O_{L_v}.
$$

Globally the local exponents assemble into the conductor ideal, and

$$
S=\{x\in L:x\in S_v\text{ for every finite }v\}.
$$

Two quadratic orders can have the same fraction algebra but different conductors. Rational conjugacy of embeddings cannot distinguish them; optimality will.

### 17.3 Optimality as an intersection condition

An embedding $\iota:L\hookrightarrow B$ is an **optimal embedding of $S$ into $\mathcal O$** if

$$
\boxed{\iota(L)\cap\mathcal O=\iota(S).}
$$

The intersection is taken inside $B$. This single equation includes containment $\iota(S)\subset\mathcal O$ and asserts that no element of $L\setminus S$ becomes integral in $\mathcal O$.

Optimality is local.

**Proposition 17.1 (local detection of optimality).** Suppose $\iota(S)\subset\mathcal O$. Then $\iota$ is optimal if and only if

$$
\iota(L_v)\cap\mathcal O_v=\iota(S_v)
$$

for every finite place $v$.

**Proof strategy.** Both sides are lattices in the same quadratic $F$-subspace. Equality of global lattices is equivalent to equality at every completion.

**Proof.** Put $T=\iota(L)\cap\mathcal O$. It is an order in $\iota(L)$ containing $\iota(S)$. Intersection commutes with localization for lattices in finite-dimensional vector spaces, so

$$
T_v=\iota(L_v)\cap\mathcal O_v.
$$

Thus $T=\iota(S)$ if and only if $T_v=\iota(S_v)$ for every $v$, by the local--global lattice criterion. $\square$

The containment hypothesis cannot be omitted from the phrasing, although it follows from the displayed local equalities. It makes clear that an optimal embedding is first an integral embedding and then a maximality statement within its quadratic fraction algebra.

### 17.4 The split local lattice-pair normal form

Let $K$ be nonarchimedean, $A$ its valuation ring, $C=M_2(K)=\operatorname{End}_K(V)$, and $L$ a quadratic étale $K$-algebra embedded in $C$. For an $A$-lattice $M\subset V$, define its multiplier order in $L$ by

$$
S(M)=\{x\in L:xM\subset M\}.
$$

Since $1\in M$ is not meaningful for a general lattice in $V$, one should not identify $M$ with an order. Nevertheless $S(M)$ is an $A$-order in $L$, and

$$
L\cap\operatorname{End}_A(M)=S(M).
$$

If $M_0$ and $M_n$ represent vertices at distance $n$, their endomorphism rings intersect in an Eichler order $\mathcal E$ of exponent $n$. The intersection with $L$ is then

$$
L\cap\mathcal E
=S(M_0)\cap S(M_n).
$$

This yields a complete local criterion with no hidden parity or residue-characteristic assumption.

**Theorem 17.2 (lattice-pair criterion).** An embedding of a quadratic $A$-order $S\subset L$ into a split Eichler order of exponent $n$ is optimal if and only if there are two $A$-lattices $M_0,M_n\subset V$, whose homothety classes have distance $n$, such that

$$
S(M_0)\cap S(M_n)=S.
$$

**Proof.** Conjugate the Eichler order into the form

$$
\operatorname{End}_A(M_0)\cap\operatorname{End}_A(M_n).
$$

Intersecting with the embedded copy of $L$ gives the displayed multiplier-order intersection. This equals $S$ exactly when the embedding is optimal. Conversely, a lattice pair satisfying the equation defines an Eichler order of exponent $n$ into which $S$ embeds optimally. $\square$

The theorem is often visualized through the **branch** of $S$: the subtree consisting of vertices $[M]$ for which $S\subset S(M)$, equivalently maximal orders containing $S$. An optimal embedding into an Eichler order corresponds not merely to a length-$n$ segment in this branch, but to one whose two endpoint multiplier orders intersect in exactly $S$.

Several clean cases build intuition.

- If $L=K\times K$ and $S=A\times A$, the branch is an entire apartment. It contains segments of every length, so the maximal split quadratic order embeds optimally into $\mathcal E_n$ for every $n$.

- If $L/K$ is unramified quadratic and $S=\mathcal O_L$, the branch has one vertex. Indeed, every $\mathcal O_L$-stable lattice is a fractional $\mathcal O_L$-ideal, hence principal, and an unramified uniformizer is central up to a unit. Thus $\mathcal O_L$ embeds optimally into a maximal order but not into a positive-level Eichler order.

- If $L/K$ is ramified quadratic and $S=\mathcal O_L$, the branch consists of two adjacent vertices. Fractional $\mathcal O_L$-ideals have two homothety classes because a base uniformizer has even $L$-valuation. Hence an optimal embedding is possible at exponents $0$ and $1$, but not along a longer segment.

For a nonmaximal order $S_c$, the branch thickens around the branch of $\mathcal O_L$. The precise endpoint count at dyadic places depends on the integral quadratic extension, so a slogan involving only $c$ and $n$ should not be used there without proof. The lattice-pair criterion remains exact in every residue characteristic and is the safe local normal form.

There is one useful maximal-order construction valid for every $S$. Let $V=L$ and let $S$ act by left multiplication on the $A$-lattice $S\subset L$. Then

$$
S(S)=\{x\in L:xS\subset S\}=S,
$$

because $xS\subset S$ implies $x=x\cdot1\in S$. Therefore every quadratic local order embeds optimally into some split maximal order, namely $\operatorname{End}_A(S)$.

### 17.5 The division-place criterion

Let $D/K$ be the quaternion division algebra. A quadratic étale algebra embeds in $D$ only if it is a field. If $L/K$ is quadratic and $\iota:L\hookrightarrow D$, then

$$
\iota(L)\cap\mathcal O_D=\iota(\mathcal O_L).
$$

To see this, restrict the division valuation $w_D$ to $L$. For an unramified quadratic extension,

$$
w_D(x)=v_L(x),
$$

while for a ramified quadratic extension,

$$
w_D(x)=\frac12v_L(x).
$$

In either case $w_D(x)\ge0$ exactly when $v_L(x)\ge0$. Since $\mathcal O_D$ is the nonnegative-value ring, its intersection with $L$ is $\mathcal O_L$.

We obtain a sharp conclusion.

**Proposition 17.3 (optimality at a division place).** Let $S\subset L$ be a quadratic $A$-order and let $D/K$ be the quaternion division algebra. An optimal embedding $S\hookrightarrow\mathcal O_D$ exists if and only if $S=\mathcal O_L$. In that case every field embedding $L\hookrightarrow D$ is optimal.

The field hypothesis and maximality of $S$ are independent. A split quadratic algebra fails to embed rationally. A nonmaximal order in a quadratic field embeds as a subring of $\mathcal O_D$, but never optimally, because the intersection automatically enlarges it to $\mathcal O_L$.

For a global Eichler order, every finite ramified place of $B$ is a division place at which the order is maximal. Therefore a necessary condition for an optimal embedding of $S$ is

$$
v(\mathfrak f(S))=0
\qquad(v\mid\mathfrak d(B)).
$$

This integral condition supplements the rational condition that $L_v$ be a field at those places.

### 17.6 Local--global optimality and selectivity

Suppose first that one global embedding $\iota:L\hookrightarrow B$ has been fixed. Proposition 17.1 says that its optimality in a fixed order is completely local. Existence is subtler because the local conjugating elements may not come from one element of $B^\times$.

There are three distinct assertions:

1. $L$ embeds in $B$ as an $F$-algebra;
2. $S_v$ embeds optimally in $\mathcal O_v$ for every finite $v$;
3. $S$ embeds optimally in this particular global order $\mathcal O$.

The first is equivalent to nonsplitting of every ramified place of $B$ in $L$. The second adds the local conductor and level conditions of Sections 17.4 and 17.5. The third can still fail even when the first two hold. This remaining global phenomenon is called **selectivity**: a quadratic order may embed optimally into some, but not all, global conjugacy classes in one genus of quaternion orders.

Local data do guarantee an order somewhere in the genus. Fix a rational embedding $\iota:L\hookrightarrow B$. Suppose that for every finite $v$ there is $g_v\in B_v^\times$ such that

$$
\iota(L_v)\cap g_v\mathcal O_vg_v^{-1}=\iota(S_v),
$$

with $g_v\in\mathcal O_v^\times$ almost everywhere. Put $g=(g_v)$ and reconstruct

$$
\mathcal O'=B\cap g\widehat{\mathcal O}g^{-1}.
$$

Then $\mathcal O'$ lies in the genus of $\mathcal O$, and localization shows

$$
\iota(L)\cap\mathcal O'=\iota(S).
$$

Thus $S$ embeds optimally into some order of that genus. Selectivity asks whether $\mathcal O'$ can be brought to the originally chosen $\mathcal O$ by rational conjugation. The answer is governed by a global conjugacy class, not by another local conductor inequality.

### 17.7 Embedding classes as double quotients

The exact quotient makes the rational-versus-local obstruction visible. Fix $\iota:L\hookrightarrow B$ and define

$$
Y(S,\mathcal O)
=\{g\in B^\times:
\iota(L)\cap g\mathcal Og^{-1}=\iota(S)\}.
$$

For $g\in Y(S,\mathcal O)$, the map

$$
x\longmapsto g^{-1}\iota(x)g
$$

is an optimal embedding of $S$ into $\mathcal O$. Left multiplication of $g$ by $\iota(L)^\times$ does not change this embedding, because $L$ centralizes itself. Right multiplication by $\mathcal O^\times$ conjugates the embedding by a unit of the target order. Consequently the set of optimal embeddings modulo $\mathcal O^\times$-conjugacy is

$$
\boxed{
\iota(L)^\times\backslash
Y(S,\mathcal O)/\mathcal O^\times.}
$$

The adelic analogue is obtained by replacing every object by its finite completion and imposing the intersection condition at every finite place. It packages all local optimal embeddings. The diagonal rational quotient maps into that adelic set. Failure to hit an adelic class is precisely a global selectivity obstruction.

The centralizer in the left quotient must be $L^\times$, not $F^\times$. Two conjugating elements differing by a noncentral element of $L^\times$ still define the same embedding. On the right, using all of $B^\times$ would erase the chosen target order; the correct equivalence is conjugacy by $\mathcal O^\times$.

### 17.8 Examples and counterexamples

The regular representation gives the universal split example. Let $S$ be any quadratic $A$-order and act on the rank-two lattice $S$ by left multiplication. Then

$$
S\hookrightarrow\operatorname{End}_A(S)\cong M_2(A)
$$

is optimal. The same rational quadratic algebra may therefore have optimal embeddings of every conductor, but generally into different conjugates of the maximal matrix order.

In Hamilton's rational algebra, the inclusion

$$
\mathbf Q(i)\hookrightarrow B
$$

meets the Hurwitz order in $\mathbf Z[i]$. Hence $\mathbf Z[i]\hookrightarrow\mathcal H$ is optimal. The smaller order $\mathbf Z[2i]$ is contained in $\mathcal H$, but that inclusion is not optimal:

$$
\mathbf Q(i)\cap\mathcal H=\mathbf Z[i]
\supsetneq\mathbf Z[2i].
$$

This is the simplest counterexample to “contained” implying “optimal.”

At the prime $2$, the algebra is division and the Hurwitz order is maximal. Proposition 17.3 explains the same example locally: only the maximal quadratic order in $\mathbf Q_2(i)$ can occur optimally. At a split prime dividing an Eichler level, the lattice-pair criterion replaces this rigid conclusion by a segment problem.

Finally, rational embeddability does not imply integral embeddability at a chosen level. A quadratic field may be nonsplit at every ramified place of $B$ and therefore embed in $B$, while its maximal local order at an unramified quadratic place cannot embed into an Eichler order of positive exponent there. Rational ramification conditions and integral level conditions solve different problems and must both be checked.

## 18. Reduced-norm packets

### 18.1 The norm quotient attached to a level

Reduced norm sends quaternionic finite ideles to ordinary finite ideles. To understand what it remembers after taking double cosets, let $K\subset\widehat B^\times$ be a compact open subgroup and put

$$
H_K=\operatorname{Nrd}(K)\subset\mathbf A_{F,f}^\times.
$$

This is an open compact subgroup. Compactness follows from compactness of $K$; openness follows locally from the openness of reduced norm on the unit group and then from the restricted-product topology. Define

$$
F_{B,+}^\times
=\{a\in F^\times:a>0
\text{ at every real place ramified in }B\}
$$

and the finite norm-class quotient

$$
C_K
=F_{B,+}^\times\backslash
\mathbf A_{F,f}^\times/H_K.
$$

Its finiteness is a ray-class argument. The open subgroup $H_K$ contains a product of sufficiently deep principal-unit groups at finitely many places and all local units outside them. Modding out by $H_K$ therefore leaves a quotient of a ray class group, while the positivity condition accounts for the ramified real places.

If $K=\widehat{\mathcal O}^\times$ for an Eichler order, Proposition 15.1 gives

$$
H_K=\widehat R^\times.
$$

When $B$ is totally definite over a totally real field, $F_{B,+}^\times=F_+^\times$, the totally positive elements, and hence

$$
C_K\cong\operatorname{Cl}^+(F),
$$

the narrow ideal class group. For a general quaternion algebra, positivity is imposed only at the ramified real places, so the quotient lies between the ordinary and narrow class quotients.

### 18.2 The norm map on an ideal class set

Reduced norm descends to double cosets:

$$
\nu_K:
B^\times\backslash\widehat B^\times/K
\longrightarrow C_K,
\qquad
[g]\longmapsto[\operatorname{Nrd}(g)].
$$

It is well defined because

$$
\operatorname{Nrd}(b g k)
=\operatorname{Nrd}(b)\operatorname{Nrd}(g)\operatorname{Nrd}(k),
$$

with $\operatorname{Nrd}(b)\in F_{B,+}^\times$ by the global reduced norm theorem and $\operatorname{Nrd}(k)\in H_K$ by definition.

**Proposition 18.1.** The map $\nu_K$ is surjective.

**Proof strategy.** Lift a finite idele component by component using local reduced-norm surjectivity, choosing integral unit lifts almost everywhere.

**Proof.** Let $a=(a_v)\in\mathbf A_{F,f}^\times$. For every finite $v$, choose $g_v\in B_v^\times$ with $\operatorname{Nrd}(g_v)=a_v$. At almost every place $a_v\in R_v^\times$ and $B_v$ is unramified with a fixed maximal integral model. Proposition 15.1 then permits $g_v$ to be chosen in the corresponding unit group. Thus $g=(g_v)$ belongs to $\widehat B^\times$ and $\operatorname{Nrd}(g)=a$. Its double coset maps to the class of $a$. $\square$

For $K=\widehat{\mathcal O}^\times$, this is the norm-ideal map on locally principal right ideal classes. It sends $[I(g)]$ to the class of $\operatorname{nrd}(I(g))$, with principal generators restricted by positivity at ramified real places. The ordinary ideal-class invariant from Chapter 9 is its coarser shadow when signs are forgotten.

Surjectivity does not imply injectivity. If two representatives have the same norm class, adjusting by the rational and level factors in that equality leaves a finite-adelic element of reduced norm one. Deciding whether the representatives are equivalent therefore requires information about the norm-one group that the surjectivity argument does not supply.

### 18.3 What reduced norm does not classify

The norm map

$$
\nu_K:X_K\to C_K
$$

remains surjective, but its fibers can have more than one element.

Those fibers are not a defect in the norm theorem. Reduced norm is abelian data; distinct ideal classes, left-order types, and lattice configurations can share it. The preceding argument proves surjectivity and no more. Injectivity would require an additional approximation theorem for the norm-one group, which is not part of the integral order theory developed here.

The Hurwitz order has one ideal class, so its sole norm packet is a singleton. This does not prove a general norm classification. Over $\mathbf Q$ the narrow class group is trivial, so whenever a definite maximal or Eichler order has class number greater than one, all of its distinct classes lie in the same norm packet. The class number then measures information invisible to reduced norm. No injectivity assertion is needed for the finite definite package below.

## 19. Finite double-coset sets for definite quaternionic forms

### 19.1 The finite arithmetic skeleton

Let $F$ be totally real, let $B/F$ be totally definite, and let $K\subset\widehat B^\times$ be compact open. The fundamental finite set is

$$
X_K=B^\times\backslash\widehat B^\times/K.
$$

Chapter 13 proved finiteness. Total definiteness is not needed for the bare finiteness of an order class set, but it gives this quotient its later force: after the compact archimedean factor is suppressed, no continuous symmetric-space coordinate remains. The finite set $X_K$ is the arithmetic skeleton on which definite quaternionic forms are built.

When $K=\widehat{\mathcal O}^\times$, the elements of $X_K$ are locally principal proper right $\mathcal O$-ideal classes. When $K$ is merely a compact open, the double quotient still makes sense, but there need not be one additive order whose unit group is exactly $K$. Order level is the principal arithmetic case, not the definition of the quotient.

### 19.2 Representatives, ideals, and stabilizers

Choose representatives

$$
\widehat B^\times
=\bigsqcup_{i=1}^h B^\times g_iK.
$$

For order level, put

$$
I_i=B\cap g_i\widehat{\mathcal O}.
$$

Then $I_i$ is a locally principal right $\mathcal O$-ideal, and every class occurs exactly once. Its left order satisfies

$$
\widehat{\mathcal O_L(I_i)}
=g_i\widehat{\mathcal O}g_i^{-1}.
$$

The arithmetic stabilizer of the representative is

$$
\Gamma_i
=B^\times\cap g_iKg_i^{-1}.
$$

If $K=\widehat{\mathcal O}^\times$, this becomes

$$
\Gamma_i=\mathcal O_L(I_i)^\times.
$$

The formula explains why left orders vary while the right order stays fixed. Replacing $g_i$ by $b g_i k$ conjugates $\Gamma_i$ by $b$, replaces $I_i$ by the equivalent ideal $bI_i$, and leaves the point of $X_K$ unchanged. Thus no individual subgroup is canonical as a subset of $B^\times$, but its conjugacy class is attached to the double-coset point.

### 19.3 Central quotients and effective stabilizers

The stabilizer $\Gamma_i$ may be infinite because it contains central units. Define

$$
Z_K=F^\times\cap K.
$$

Since central elements commute with every $g_i$, this group is the same central stabilizer at every point. For order level,

$$
Z_K=R^\times.
$$

The **effective stabilizer** is

$$
\overline\Gamma_i=\Gamma_i/Z_K.
$$

It is finite. Indeed, finite components of $\Gamma_i$ lie in the compact set $g_iKg_i^{-1}$, while total definiteness makes the archimedean image compact modulo the center. After quotienting by $Z_K$, the diagonal arithmetic subgroup is discrete in a compact set and therefore finite.

Here are the central and denominator steps explicitly. For each finite $v$, the valuation of $\operatorname{Nrd}(\Gamma_i)$ is a subgroup of $\mathbf Z$ contained in the bounded valuation image of the compact group $g_iKg_i^{-1}$. It is therefore zero. Thus

$$
\operatorname{Nrd}(\Gamma_i)
\subset R^\times\cap F_+^\times.
$$

The central subgroup $Z_K$ has finite index in $R^\times$: its defining finite-adelic condition is an open subgroup condition on $\widehat R^\times$, hence has finite quotient when restricted to $R^\times$. It follows that $(Z_K)^2$ has finite index in the totally positive unit group. After multiplication by an element of $Z_K$, the norm of any element of $\Gamma_i$ may consequently be put into one fixed finite set of unit representatives. At infinity the resulting elements lie on finitely many compact norm spheres, and at finite places they remain in $g_iKg_i^{-1}$. Bounding the finite denominators places their diagonal representatives in one fractional $R$-lattice in $B$; its Minkowski image meets the compact archimedean set in finitely many points. This proves the finiteness of $\Gamma_i/Z_K$.

Over $\mathbf Q$, $R^\times=\{\pm1\}$ and even the full unit group of a definite order is finite. Over a larger totally real field, the distinction is essential: Dirichlet units make $R^\times$ infinite, although the effective stabilizer remains finite.

These stabilizers are not incidental bookkeeping. Whenever one assigns data to the points of $X_K$, the datum at $[g_i]$ must be invariant under $\Gamma_i$ or under its effective action after a central character has been fixed. Different ideal classes can have stabilizers of different orders.

### 19.4 Norm packets

The surjective map

$$
\nu_K:X_K\twoheadrightarrow C_K
$$

partitions the finite class set into **norm packets**. For Eichler order level in the totally definite case,

$$
C_K\cong\operatorname{Cl}^+(F).
$$

Thus every ideal class has a narrow norm class, and every narrow class occurs. Inside one packet, reduced norm supplies no further distinction.

This partition is useful but must not be mistaken for a classification. If $F=\mathbf Q$, then $\operatorname{Cl}^+(\mathbf Q)$ is trivial, so all points of every definite class set lie in one norm packet. Class numbers greater than one are therefore direct counterexamples to injectivity of $\nu_K$.

The packet decomposition separates the abelian ideal-class contribution from the remaining quaternionic information. The latter is exactly the information that reduced norm alone does not see.

### 19.5 Changing level

Suppose $K'\subset K$ are compact open subgroups. Forgetting part of the level gives a surjection

$$
p:X_{K'}\longrightarrow X_K,
\qquad
[g]_{K'}\longmapsto[g]_K.
$$

The fiber over the class of $g_i$ is not generally a set of cardinality $[K:K']$. Put

$$
\Delta_i=g_i^{-1}B^\times g_i\cap K.
$$

Then there is a natural bijection

$$
p^{-1}([g_i])
\cong\Delta_i\backslash K/K'.
$$

**Proof.** Every point above $[g_i]$ has a representative $g_i k$ with $k\in K$. Two such representatives $g_ik_1$ and $g_ik_2$ define the same $K'$-class exactly when

$$
b g_i k_1K'=g_i k_2K'
$$

for some $b\in B^\times$. Rearranging says that $g_i^{-1}bg_i\in\Delta_i$ carries the right coset $k_1K'$ to $k_2K'$. This is precisely the displayed double quotient. $\square$

Stabilizers can identify points in a fiber, so the fiber sizes may vary with $i$. Even if $K'$ is normal in $K$, the action of $\Delta_i$ can have different images at different classes. This is why a change-of-level map is not automatically a covering of constant degree.

Reduced norm is compatible with change of level. Since $H_{K'}\subset H_K$, there is a natural map

$$
C_{K'}\longrightarrow C_K,
$$

and the square with $X_{K'}\to X_K$ commutes. Finer level can refine both the quaternionic fibers and the abelian norm quotient.

### 19.6 What is and is not canonical

The set $X_K$ is canonical once $B$ and the subgroup $K$ are fixed. The following auxiliary choices are not:

- representatives $g_i$ of its points;
- local matrix identifications at split places;
- a particular global Eichler order within its genus;
- bases of the associated ideals;
- literal embeddings of the stabilizer groups into one coordinate model.

Changing these choices conjugates the relevant orders and stabilizers and transports the corresponding ideals. Statements expressed through double cosets, multiplier orders, reduced norms, and conjugacy classes survive unchanged.

For an Eichler order $\mathcal O$ of level $\mathfrak N$, the reusable finite package is therefore

$$
\left(
X_{\widehat{\mathcal O}^\times},
\{I_i\},
\{\mathcal O_L(I_i)^\times/R^\times\},
\nu_{\widehat{\mathcal O}^\times}
\right).
$$

The ideals and groups in braces depend on representatives up to the equivalences already described; the package as a collection over the finite set does not. It records the class points, their integral stabilizers, and their narrow norm packets. That is exactly the finite arithmetic input needed before weights or correspondences are introduced.

## 20. The integral--adelic dictionary

### 20.1 One table of translations

The theory can now be compressed without being obscured. For a quaternion algebra $B/F$ and an order $\mathcal O$, the principal translations are:

| Integral object | Local description | Finite-adelic description |
|---|---|---|
| full lattice $L\subset B$ | free $R_v$-lattices $L_v$, standard almost everywhere | compact open $\widehat R$-lattice $\widehat L\subset\widehat B$ |
| order $\mathcal O$ | orders $\mathcal O_v$ in $B_v$ | compact open ring $\widehat{\mathcal O}$ |
| units of an order | $\mathcal O_v^\times$ | compact open $\widehat{\mathcal O}^\times\subset\widehat B^\times$ |
| maximal order | maximal at every finite $v$ | maximal compact factors locally |
| Eichler order of level $\mathfrak N$ | $\mathcal E_{n_v}$ at split $v$, maximal at division $v$ | $K_0(\mathfrak p_v^{n_v})$ and $\mathcal O_{D_v}^\times$ factors |
| local units | unit reduced norm; radical filtration near $1$ | compact open factor with norm image in $R_v^\times$ |
| locally principal right ideal $I$ | $I_v=g_v\mathcal O_v$ | $g\widehat{\mathcal O}$ |
| ideal equivalence $I\sim bI$ | one rational left multiplier | left quotient by $B^\times$ |
| change of local generator | $g_v\mapsto g_vu_v$ | right quotient by $\widehat{\mathcal O}^\times$ |
| right ideal class set | local generators modulo both changes | $B^\times\backslash\widehat B^\times/\widehat{\mathcal O}^\times$ |
| optimal embedding $S\hookrightarrow\mathcal O$ | $L_v\cap\mathcal O_v=S_v$ | rational orbit inside a packet of local embedding orbits |
| norm packet | local reduced-norm idele class | fiber of $X_K\to C_K$ |

The left/right positions in the ideal-class rows are not typography: they encode the convention that $g\widehat{\mathcal O}$ is a right ideal.

### 20.2 The discriminant dictionary

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

### 20.3 The ideal dictionary

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

### 20.4 The finite input for the next book

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

5. modulo central units, every $\Gamma_i$ is finite;
6. reduced norm partitions $X_K$ into packets indexed by the narrow ideal class group of $F$;
7. a quadratic order embeds optimally only after both the rational ramification test and the local conductor--level tests have been passed;
8. at every split finite place, the local lattice tree records the maximal-order vertices and Eichler segments underlying the chosen level.

These statements are precisely the integral and finite-combinatorial input needed to define functions on $X_K$ with prescribed algebraic behavior at infinity. No automorphic form or Hecke operator has been defined here; the present endpoint is the arithmetic set on which those later structures will act.

### 20.5 Conclusion

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

turns ideal arithmetic into a finite double-coset set. For totally definite $B$, compactness at infinity explains why this set and its stabilizers are especially concrete. The ambient algebra from Book 77, the finite restricted product, and the integral structures developed here have therefore converged on one reusable object: a compact-open level inside $\widehat B^\times$ together with the finite arithmetic quotient it defines.

Unit groups refine this quotient without replacing the orders behind them. Locally, radical filtrations linearize units and every Eichler unit group has full unit reduced norm. Globally, positivity at ramified real places survives in the norm-class quotient. Reduced norm always gives the proved surjection onto norm classes, but in the totally definite case its finite fibers can retain genuinely quaternionic class information.

Quadratic orders supply a complementary probe. Rational embedding is controlled by the ramification set of $B$, but optimal integral embedding is the sharper intersection equation $L\cap\mathcal O=S$. In split local algebras this becomes a problem about multiplier orders at the endpoints of a lattice segment. At division places it forces the quadratic order to be maximal. Local conditions construct an optimal embedding somewhere in the genus, while selectivity records the possible failure in one chosen global conjugacy class.

The final object is therefore richer than a bare finite set. It is a finite collection of ideal classes equipped with left orders, effective unit stabilizers, norm packets, level-change maps, and quadratic embedding orbits. Those structures are all consequences of the integral theory developed here, and together they form the precise arithmetic foundation for definite quaternionic forms.
