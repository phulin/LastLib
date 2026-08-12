# Galois Representations from Weight-Two Shimura-Curve Cohomology

## Contents

- [1. From a cohomological packet to a Galois representation](#1-from-a-cohomological-packet-to-a-galois-representation)
  - [1.1 The extraction problem](#11-the-extraction-problem)
  - [1.2 Standing conventions](#12-standing-conventions)
  - [1.3 The curve source](#13-the-curve-source)
  - [1.4 The logical order](#14-the-logical-order)
- [2. Commuting actions and localization](#2-commuting-actions-and-localization)
  - [2.1 The abstract bimodule](#21-the-abstract-bimodule)
  - [2.2 Central idempotents and local factors](#22-central-idempotents-and-local-factors)
  - [2.3 Localization is not an eigenspace](#23-localization-is-not-an-eigenspace)
  - [2.4 Galois stability of a localized block](#24-galois-stability-of-a-localized-block)
- [3. Multiplicity-space extraction](#3-multiplicity-space-extraction)
  - [3.1 The split simple block](#31-the-split-simple-block)
  - [3.2 The evaluation theorem](#32-the-evaluation-theorem)
  - [3.3 The rank-two curve constituent](#33-the-rank-two-curve-constituent)
  - [3.4 Old level and noncommutative Hecke algebras](#34-old-level-and-noncommutative-hecke-algebras)
- [4. Continuity and semisimplification](#4-continuity-and-semisimplification)
  - [4.1 Continuity on Hom spaces](#41-continuity-on-hom-spaces)
  - [4.2 Stable lattices](#42-stable-lattices)
  - [4.3 Canonical semisimplification](#43-canonical-semisimplification)
  - [4.4 What semisimplicity does not mean](#44-what-semisimplicity-does-not-mean)
- [5. Coefficient fields and descent](#5-coefficient-fields-and-descent)
  - [5.1 Hecke fields and splitting fields](#51-hecke-fields-and-splitting-fields)
  - [5.2 Schur obstruction](#52-schur-obstruction)
  - [5.3 Trace fields of the Galois constituent](#53-trace-fields-of-the-galois-constituent)
  - [5.4 Change of coefficient place](#54-change-of-coefficient-place)
- [6. Duality and the determinant line](#6-duality-and-the-determinant-line)
  - [6.1 Factoring Poincare duality](#61-factoring-poincare-duality)
  - [6.2 Two-dimensional similitudes](#62-two-dimensional-similitudes)
  - [6.3 The central-component character](#63-the-central-component-character)
  - [6.4 The determinant theorem](#64-the-determinant-theorem)
- [7. Parity at real places](#7-parity-at-real-places)
  - [7.1 Complex conjugation and Hodge lines](#71-complex-conjugation-and-hodge-lines)
  - [7.2 Oddness of the extracted representation](#72-oddness-of-the-extracted-representation)
  - [7.3 Reducible and scalar cases](#73-reducible-and-scalar-cases)
  - [7.4 Where parity is not defined](#74-where-parity-is-not-defined)
- [8. Good-prime Frobenius polynomials](#8-good-prime-frobenius-polynomials)
  - [8.1 The full good-reduction ledger](#81-the-full-good-reduction-ledger)
  - [8.2 From the correspondence relation to an annihilator](#82-from-the-correspondence-relation-to-an-annihilator)
  - [8.3 Determinant upgrades annihilation to characteristic polynomial](#83-determinant-upgrades-annihilation-to-characteristic-polynomial)
  - [8.4 Geometric and arithmetic Frobenius](#84-geometric-and-arithmetic-frobenius)
- [9. Integral lattices and congruences](#9-integral-lattices-and-congruences)
  - [9.1 The ambient cohomological lattice](#91-the-ambient-cohomological-lattice)
  - [9.2 Saturated packet lattices](#92-saturated-packet-lattices)
  - [9.3 Integral Morita extraction](#93-integral-morita-extraction)
  - [9.4 Reduction and determinant](#94-reduction-and-determinant)
- [10. Purity and local boundaries](#10-purity-and-local-boundaries)
  - [10.1 Purity at good places](#101-purity-at-good-places)
  - [10.2 What follows for rank two](#102-what-follows-for-rank-two)
  - [10.3 Semistable places](#103-semistable-places)
  - [10.4 The coefficient prime and other boundaries](#104-the-coefficient-prime-and-other-boundaries)
- [11. Diagnostic examples and failure modes](#11-diagnostic-examples-and-failure-modes)
  - [11.1 A minimal curve packet](#111-a-minimal-curve-packet)
  - [11.2 A three-dimensional oldspace](#112-a-three-dimensional-oldspace)
  - [11.3 A scalar Frobenius](#113-a-scalar-frobenius)
- [12. The extraction theorem](#12-the-extraction-theorem)
  - [12.1 Complete statement](#121-complete-statement)
  - [12.2 Proof](#122-proof)
  - [12.3 Dependency and hypothesis ledger](#123-dependency-and-hypothesis-ledger)
  - [12.4 Conclusion](#124-conclusion)

## 1. From a cohomological packet to a Galois representation

Parallel-weight-two automorphic forms enter arithmetic through curve cohomology, but a cohomological packet block is usually larger than the representation one wants. It contains several packets, several level vectors for one packet, and the two archimedean orientations of weight-one cohomology. The Galois group commutes with the descended Hecke correspondences, so it acts on the multiplicity left after the finite Hecke module has been removed. Extracting that multiplicity, rather than choosing an eigenvector, is the central construction of this book.

### 1.1 The extraction problem

Let $E$ be a number field, let $C/E$ be a smooth projective Shimura curve, and fix a prime $\ell$. The geometric cohomology

$$
H^1_\ell(C)=H^1_{\mathrm{et}}(C_{\bar E},\mathbf Q_\ell)
$$

carries two commuting actions: a continuous action of $G_E=\operatorname{Gal}(\bar E/E)$ and an algebraic action of the finite Hecke image. A weight-two packet determines a rational central idempotent after its algebraic conjugates have been grouped. The first question is not whether the corresponding subspace exists; it does. The first question is which factor of that subspace carries Galois.

Over a splitting field, the packet block has the form

$$
P_\Pi\otimes W_\Pi,
\qquad \dim W_\Pi=2, \tag{1.1}
$$

where $P_\Pi$ is the finite Hecke module of level vectors. Galois commutes with the Hecke algebra, hence acts on $W_\Pi$. Even when $\dim P_\Pi>1$, the arithmetic factor remains two-dimensional.

### 1.2 Standing conventions

All coefficient fields have characteristic zero. If $L$ is a number field and $\lambda\mid\ell$, its completion is $L_\lambda$. Every representation is finite-dimensional and continuous for the profinite topology on a Galois group and the $\lambda$-adic topology on a matrix group.

Galois acts arithmetically. For a finite field $\mathbf F_q$, arithmetic Frobenius is $x\mapsto x^q$ and geometric Frobenius is its inverse. We write $\Phi_u$ for geometric Frobenius at a good finite place $u$. Our Tate convention is

$$
\Phi_u\mid L_\lambda(1)=q_u^{-1},
\qquad
\operatorname{Frob}^{\mathrm{arith}}_u\mid L_\lambda(1)=q_u. \tag{1.2}
$$

Thus untwisted curve $H^1$ is pure of weight one for geometric Frobenius, and its eigenvalues have complex absolute value $q_u^{1/2}$.

At a split hyperspecial place $v$ of the totally real field underlying the packet, the unnormalized Hecke operators are $T_v$ and $S_v$, and the raw polynomial is

$$
Q_v(X)=X^2-T_vX+q_vS_v. \tag{1.3}
$$

No square root of $q_v$ is inserted. The distinction between the operator identity $Q_v(\Phi_v)=0$ and the equality of $Q_v$ with a characteristic polynomial is one of the main points of Chapter 8.

For a representation $V$, the notation $V^{\mathrm{ss}}$ means the direct sum of its Jordan--Holder factors. It is a representation, not merely a list of traces. Its isomorphism class is independent of the chosen composition series.

### 1.3 The curve source

The geometric source is the compact quaternionic Shimura curve $C_K/E$ of Book 132. Its constant-coefficient $H^1$ has a finite semisimple rational Hecke image. For a parallel-weight-two packet $\Pi$, a splitting field $L$ gives

$$
e_\Pi H^1_\ell(C_K)\otimes L_\lambda
\simeq P_{\Pi,\lambda}\otimes_{L_\lambda}W_{\Pi,\lambda},
\qquad \dim W_{\Pi,\lambda}=2. \tag{1.4}
$$

The curve is proper, so there is no boundary or Eisenstein contribution. The two dimensions in $W_{\Pi,\lambda}$ come from Hodge types $(1,0)$ and $(0,1)$, not from two automorphic occurrences. This book studies this reusable curve extraction and does not introduce an auxiliary higher-dimensional carrier.

### 1.4 The logical order

The safe construction has seven stages.

1. Replace the abstract Hecke algebra by its finite image on the chosen cohomology group.
2. Cut out a rational block by a central idempotent, then extend coefficients only far enough to split its simple algebra.
3. Remove the simple finite Hecke module by a Hom construction.
4. Prove continuity and pass, when unconditional semisimplicity is desired, to the canonical semisimplification.
5. Factor Poincare duality; when a descended component twist and a polarization-compatible symmetric finite-module pairing supply the determinant datum of Section 6.3, identify the determinant line.
6. Under that datum, use the determinant to turn the good-prime quadratic annihilator into the characteristic polynomial, including scalar Frobenius.
7. Intersect the rational constituent with the natural integral lattice, without claiming an integral direct sum unless all denominators are units.

Every later conclusion depends on this order. In particular, without the determinant datum the good-prime quadratic remains only an annihilator in the scalar case, and a rational idempotent cannot be applied to an integral lattice before its denominators have been audited.

## 2. Commuting actions and localization

Localization is often described informally as “taking the eigenspace.” That phrase is harmless only at minimal level for a commutative semisimple algebra. The actual construction must also handle oldforms, noncommutative level algebras, conjugate packets, and congruent eigenvalues.

### 2.1 The abstract bimodule

Let $k$ be a field of characteristic zero, let $A$ be a finite-dimensional semisimple $k$-algebra, and let $H$ be a finite-dimensional left $A$-module. Suppose a topological group $\Gamma$ acts continuously and $k$-linearly on $H$, commuting with $A$:

$$
\gamma(ah)=a\gamma(h)
\quad
(\gamma\in\Gamma, a\in A, h\in H). \tag{2.1}
$$

Then $H$ is an $(A,k[\Gamma])$-bimodule. Every central idempotent $e\in A$ gives a $\Gamma$-stable summand $eH$. If $A$ is obtained as the image of algebraic correspondences defined over $E$ and $\Gamma=G_E$, equation (2.1) follows from Galois-equivariance of pullback and trace.

This use of the finite image is essential. An abstract Hecke algebra can be infinite-dimensional and can have a large kernel on $H$. The quotient

$$
A=\operatorname{im}(\mathcal H\to\operatorname{End}_k(H)) \tag{2.2}
$$

contains exactly the operators relevant to the cohomology under discussion.

### 2.2 Central idempotents and local factors

Because $A$ is semisimple, it is a product of simple algebras:

$$
A\simeq\prod_{j=1}^r A_j,
\qquad 1=e_1+\cdots+e_r. \tag{2.3}
$$

The $e_j$ are the primitive central idempotents. They are unique, so the rational block decomposition

$$
H=\bigoplus_j e_jH \tag{2.4}
$$

does not depend on a simultaneous eigenbasis.

Let $\mathcal O$ be the ring of integers of a number field and $\mathfrak m$ a maximal ideal of an integral Hecke image $\mathbb T$. Localization gives

$$
H_\mathfrak m=H\otimes_\mathbb T\mathbb T_\mathfrak m. \tag{2.5}
$$

After characteristic-zero scalar extension, $H_\mathfrak m$ can contain several simple blocks whose eigencharacters are congruent modulo $\mathfrak m$. Thus localization at $\mathfrak m$ and projection to one characteristic-zero packet are different operations. The former is integral and remembers congruences; the latter is rational and uses an idempotent which can have a denominator in $\mathfrak m$.

### 2.3 Localization is not an eigenspace

Suppose two characters $\lambda$ and $\mu$ occur and an operator $T$ separates them. On rational cohomology the projector onto $\lambda$ is

$$
e_\lambda=\frac{T-\mu(T)}{\lambda(T)-\mu(T)}. \tag{2.6}
$$

If $\lambda(T)-\mu(T)$ lies in $\mathfrak m$, then both packets occur in $H_\mathfrak m$ but $e_\lambda$ does not preserve the localized integral lattice. The localized module is therefore generally an extension or congruence lattice joining the two rational summands.

At old level, the difficulty is different. A packet may have a simple finite Hecke module $P$ of dimension greater than one. The entire block is isotypic for $P$, but it is not a simultaneous eigenspace for a commutative family. Choosing one vector of $P$ is neither invariant nor necessary. The Hom construction of Chapter 3 removes $P$ canonically.

### 2.4 Galois stability of a localized block

Let $X/E$ be smooth and proper, and let every correspondence generating $A$ be defined over $E$. Pullback and trace commute with the $G_E$-action on geometric cohomology. Hence every polynomial in those correspondences commutes with $G_E$, and so does every idempotent in their finite image after scalar extension.

It follows that

$$
eH^i_\ell(X)
$$

is Galois stable. This statement uses descent of the actual correspondence. Equality of its numerical eigenvalues under Galois conjugation would not be enough: equal characteristic polynomials do not make an operator commute with Galois.

The same argument works integrally for the abstract integral Hecke action, but not necessarily for a rational idempotent. The ambient localized lattice is Galois stable; an individual rational packet lattice is obtained by saturation, as in Chapter 9.

## 3. Multiplicity-space extraction

The rank of a Galois constituent is the multiplicity with which a simple Hecke module occurs, not the total dimension of the localized cohomology. This is a double-centralizer statement. We prove it in the exact form used for Shimura-curve $H^1$.

### 3.1 The split simple block

Let $A$ be a finite-dimensional semisimple algebra over a field $k$. Fix a simple factor $A_0=eA$. After a finite separable extension $L/k$, assume

$$
A_0\otimes_kL\simeq M_d(L). \tag{3.1}
$$

Let $P=L^d$ be its standard simple left module. Every finite-dimensional left $M_d(L)$-module is a direct sum of copies of $P$. Consequently, for an $A_0\otimes L$-module $H_0$, the multiplicity space

$$
W=\operatorname{Hom}_{M_d(L)}(P,H_0) \tag{3.2}
$$

has dimension equal to the number of copies of $P$ in $H_0$.

There is an evaluation map

$$
\operatorname{ev}:P\otimes_LW\longrightarrow H_0,
\qquad p\otimes f\longmapsto f(p). \tag{3.3}
$$

The matrix algebra acts on the first factor and the commutant acts on the second.

### 3.2 The evaluation theorem

**Theorem 3.1 (multiplicity extraction).** In the setting of Section 3.1, the evaluation map (3.3) is an isomorphism. If a group $\Gamma$ acts on $H_0$ and commutes with $M_d(L)$, then

$$
(\gamma f)(p)=\gamma(f(p)) \tag{3.4}
$$

defines an action of $\Gamma$ on $W$, and (3.3) is $\Gamma$-equivariant when $\Gamma$ acts trivially on $P$.

**Proof.** Let $E_{ij}$ be the standard matrix units and $e_1=E_{11}$. The subspace $e_1H_0$ determines the whole module: the map

$$
P\otimes_L e_1H_0\longrightarrow H_0,
\qquad e_i\otimes h\longmapsto E_{i1}h
$$

is inverse to

$$
h\longmapsto\sum_i e_i\otimes E_{1i}h.
$$

The identities $E_{ij}E_{rs}=\delta_{jr}E_{is}$ verify both composites. An $M_d(L)$-map $P\to H_0$ is determined by the image of $e_1$, and that image may be any element of $e_1H_0$. Hence $W\simeq e_1H_0$, under which (3.3) is the displayed isomorphism.

If $\Gamma$ commutes with every matrix, then (3.4) remains $M_d(L)$-linear. The group law and equivariance follow directly. $\square$

The theorem also proves independence of a choice of matrix coordinates. Replacing (3.1) by another splitting conjugates the matrix algebra. Its standard module is carried to an isomorphic simple module, and Schur's lemma shows that the resulting $W$ is unchanged up to a unique isomorphism class.

### 3.3 The rank-two curve constituent

For the Shimura curve of Book 132, let $A_{K,\mathbf Q}$ be the finite rational Hecke image on $H^1_B(C_K,\mathbf Q)$, let $e_\Pi$ be the central idempotent of a weight-two packet block, and choose a splitting field $L$. If $P_\Pi$ is a simple module for the split block, define

$$
W_{\Pi,\lambda}
=\operatorname{Hom}_{A_{L_\lambda}}
\left(P_{\Pi,\lambda},
e_\Pi H^1_\ell(C_K)\otimes_{\mathbf Q_\ell}L_\lambda\right). \tag{3.5}
$$

The automorphic decomposition gives

$$
\dim_{L_\lambda}W_{\Pi,\lambda}=2. \tag{3.6}
$$

The evaluation theorem gives

$$
P_{\Pi,\lambda}\otimes W_{\Pi,\lambda}
\xrightarrow{\sim}
e_\Pi H^1_\ell(C_K)\otimes L_\lambda. \tag{3.7}
$$

Since Galois commutes with every Hecke correspondence, it acts continuously on $W_{\Pi,\lambda}$. This is the raw cohomological rank-two representation.

At minimal level $P_\Pi$ is a line and (3.5) is the familiar two-dimensional eigenspace. Formula (3.5) is nevertheless preferable: it continues to work without alteration when the packet becomes old.

### 3.4 Old level and noncommutative Hecke algebras

Suppose $\dim P_\Pi=r$. Then

$$
\dim e_\Pi H^1_\ell(C_K)=2r, \tag{3.8}
$$

but the Galois factor still has dimension two. If the level algebra is the full matrix algebra on $P_\Pi$, the commutant on the block is

$$
\operatorname{End}_{A}(P_\Pi\otimes W_\Pi)
\simeq\operatorname{End}(W_\Pi). \tag{3.9}
$$

Thus every Galois operator is $1\otimes g$ under (3.7). It cannot mix level vectors independently of its action on $W_\Pi$.

If one retains only the spherical Hecke algebra away from the level, the algebra may act by scalars on all $r$ oldvectors. Its commutant is then too large, and (3.9) fails. The cure is to use the full finite Hecke image, including the level operators needed to recover the simple module $P_\Pi$. The rank-two conclusion is a theorem about that full bimodule, not about a sparse list of good eigenvalues.

## 4. Continuity and semisimplification

The Hom construction produces an algebraic action immediately. Arithmetic applications also require topological continuity and a precise meaning of semisimplicity. Neither should be inferred merely from the fact that good Frobenius operators are diagonalizable at many places.

### 4.1 Continuity on Hom spaces

Let $H$ be a finite-dimensional continuous $L_\lambda$-representation of a profinite group $\Gamma$, and let $A$ be a finite-dimensional algebra commuting with $\Gamma$. Give

$$
W=\operatorname{Hom}_A(P,H)
$$

the subspace topology inherited from $\operatorname{Hom}_{L_\lambda}(P,H)$. After choosing a basis of $P$, the latter is a finite product of copies of $H$. The equations expressing $A$-linearity are closed linear equations, so $W$ is closed.

For $f\in W$ and $p$ in a basis of $P$, continuity of $\gamma\mapsto\gamma f(p)$ proves continuity of the orbit map $\Gamma\to W$. Since $W$ is finite-dimensional, continuity of all orbit maps is equivalent to continuity of

$$
\Gamma\longrightarrow\operatorname{GL}(W). \tag{4.1}
$$

No separate compactness argument is required.

### 4.2 Stable lattices

Every continuous finite-dimensional $L_\lambda$-representation of a profinite group has a stable $\mathcal O_\lambda$-lattice. Indeed, choose any lattice $M$. Its stabilizer is open, so the compact image of $\Gamma$ moves $M$ through finitely many lattices. Their sum is a lattice and is stable.

For a cohomological representation there is a more geometric candidate. Intersect the rational subspace with the ambient integral cohomology and then saturate. This lattice remembers congruences and is usually preferable to an arbitrary compactness lattice. The two are commensurable, but their reductions need not be isomorphic.

### 4.3 Canonical semisimplification

A continuous representation need not be semisimple merely because its coefficient field has characteristic zero. Let

$$
0=V_0\subset V_1\subset\cdots\subset V_m=V \tag{4.2}
$$

be a composition series by $\Gamma$-stable subspaces. Each subspace is closed, because every linear subspace of a finite-dimensional nonarchimedean vector space is closed. Hence each quotient $V_i/V_{i-1}$ is a continuous representation. Define

$$
V^{\mathrm{ss}}=\bigoplus_{i=1}^m V_i/V_{i-1}. \tag{4.3}
$$

Jordan--Holder gives independence of the series up to isomorphism. The direct sum is continuous and semisimple. Trace, determinant, and characteristic polynomial are unchanged:

$$
\operatorname{Tr}(g\mid V^{\mathrm{ss}})=\operatorname{Tr}(g\mid V),
\qquad
\det(X-g\mid V^{\mathrm{ss}})=\det(X-g\mid V). \tag{4.4}
$$

The second equality follows by making $g$ block upper triangular along (4.2).

We define the **semisimple representation extracted from the packet** to be

$$
\rho_{\Pi,\lambda}:G_E\longrightarrow
\operatorname{GL}(W_{\Pi,\lambda}^{\mathrm{ss}}). \tag{4.5}
$$

It is still two-dimensional. Passing to (4.5) loses extension classes but loses none of the determinant or good-prime polynomial data established in this book.

### 4.4 What semisimplicity does not mean

The ambient $H^1$, the raw multiplicity space, and its semisimplification are three different objects. The construction above proves semisimplicity of (4.5) because it is the semisimplification. It does not prove that every extension occurring in raw cohomology splits over $G_E$.

For example, two characters $\chi_1$ and $\chi_2$ can form a nonsplit extension

$$
0\longrightarrow\chi_1\longrightarrow V
\longrightarrow\chi_2\longrightarrow0. \tag{4.6}
$$

Every element has the same characteristic polynomial on $V$ and on $\chi_1\oplus\chi_2$. Frobenius polynomials cannot detect the extension class. Any assertion that the raw cohomological representation is semisimple would require a separate splitting theorem. No such theorem is smuggled into the word “pure” or into the Hecke decomposition.

## 5. Coefficient fields and descent

Hecke eigenvalues generate a natural number field, but a simple finite Hecke module need not be realizable over that field. The coefficient field of the rank-two representation must therefore be described in two stages: the center field of the packet and a finite splitting field for its simple algebra.

### 5.1 Hecke fields and splitting fields

For a packet $\Pi$, define its good Hecke field by

$$
L_\Pi=\mathbf Q\bigl(t_v(\Pi),s_v(\Pi),
\text{ central and component values}\bigr), \tag{5.1}
$$

where $v$ ranges outside a finite bad set. The finite rational Hecke image has a simple factor

$$
A_\Pi\simeq M_m(D_\Pi),
$$

where $D_\Pi$ is a central division algebra over a number field $E_\Pi$ containing the good Hecke field. Once the full separating Hecke data are included, $E_\Pi$ is the field of rationality of the finite packet block; it can be larger than the field generated only by the displayed good values.

There is a finite extension $L/E_\Pi$ for which

$$
A_\Pi\otimes_{E_\Pi}L\simeq M_d(L). \tag{5.2}
$$

The construction of $W_{\Pi,\lambda}$ is made over a completion of such an $L$. Enlarging $L$ simply extends scalars:

$$
W_{\Pi,\lambda}\otimes_{L_\lambda}L'_{\lambda'}
\simeq W_{\Pi,\lambda'}. \tag{5.3}
$$

### 5.2 Schur obstruction

Before splitting, the correct multiplicity object is not necessarily a vector space over the center. If $P$ is a simple left $A_\Pi$-module, Morita theory gives $\operatorname{End}_{A_\Pi}(P)\simeq D_\Pi^{\mathrm{op}}$, and

$$
\operatorname{Hom}_{A_\Pi}(P,e_\Pi H)
$$

naturally carries an action of the corresponding division-algebra commutant. Choosing (5.2) converts the split multiplicity object into an ordinary vector space.

This is the same descent obstruction that appears for corestriction algebras in rank two. A split central simple algebra is an endomorphism algebra of a vector space of the expected dimension; a nonsplit algebra is not. Declaring a two-dimensional representation over $L_\Pi$ before checking the obstruction would amount to declaring the division algebra split.

The rational conjugacy-orbit block remains canonical over $\mathbf Q$. The rank-two realization is canonical up to finite coefficient extension and isomorphism. This is the strongest statement justified without a vanishing theorem for the Schur class.

### 5.3 Trace fields of the Galois constituent

Let $K_{\rho}$ be the subfield of $L$ generated by

$$
\operatorname{Tr}(\rho(g)),\qquad\det(\rho(g))
\quad(g\in G_E). \tag{5.4}
$$

For a semisimple representation these functions determine the isomorphism class after extension to an algebraic closure. The safe argument is Brauer--Nesbitt, not a pointwise choice of the two roots. Given two representations, let $C$ be the finite-dimensional algebra generated by the diagonal image of $G_E$ in the endomorphisms of their direct sum. Equality of traces on every group element extends linearly to equality of characters on $C$. After quotienting the radical and extending to a splitting field, a semisimple finite-dimensional algebra is a product of matrix algebras, and its irreducible characters are linearly independent. Hence the two semisimple $C$-modules, and therefore the two Galois representations, are isomorphic. In dimension two the determinant is part of the same characteristic-polynomial data, although equality of the trace character already suffices for Brauer--Nesbitt.

The representation need not descend to $K_\rho$ itself: an absolutely irreducible representation can retain a central simple Schur obstruction. It descends after a finite splitting extension. In the Shimura-curve construction, the chosen Hecke splitting field already supplies one.

### 5.4 Change of coefficient place

Fix an embedding $L\hookrightarrow\overline{\mathbf Q}_\ell$. It selects a place $\lambda$ and a representation over $L_\lambda$. A different embedding can select a conjugate packet. Algebraic conjugation sends

$$
t_v(\Pi)\mapsto\sigma(t_v(\Pi)),
\qquad
s_v(\Pi)\mapsto\sigma(s_v(\Pi)), \tag{5.5}
$$

and transports the whole construction to $\Pi^\sigma$.

The present book proves a coefficient-field statement at each $\lambda$. The curve annihilators have coefficients in $L_\Pi$; under the determinant datum they are the characteristic polynomials. The book does not identify the underlying topological vector spaces for different primes $\ell$. Compatibility means that the available polynomials arise from the same algebraic data, not that there is a linear map between an $\ell$-adic and an $\ell'$-adic space.

## 6. Duality and the determinant line

The quadratic Hecke relation becomes a characteristic polynomial in the scalar case only after the determinant is known independently. Book 132 supplies adjoint duality; an alternating self-pairing, and hence the determinant formula below, requires the additional curve determinant datum of Section 6.3.

### 6.1 Factoring Poincare duality

On curve cohomology, Poincare duality has the typed form

$$
H^1_\ell(C_K)\times H^1_\ell(C_K)
\longrightarrow\mathbf Q_\ell(-1). \tag{6.1}
$$

Transpose Hecke correspondences are adjoint. Thus the $\Pi$ block pairs perfectly with the adjoint block $\Pi^\dagger$. After a splitting field is chosen, write

$$
H[\Pi]=P_\Pi\otimes W_\Pi,
\qquad
H[\Pi^\dagger]=P_{\Pi^\dagger}\otimes W_{\Pi^\dagger}. \tag{6.2}
$$

Choose a nonzero Hecke-equivariant pairing

$$
b_P:P_\Pi\times P_{\Pi^\dagger}\to L. \tag{6.3}
$$

Schur's lemma makes it unique up to a scalar. The ambient pairing then factors uniquely as

$$
b_P\otimes b_W,
\qquad
b_W:W_\Pi\times W_{\Pi^\dagger}\to L_\lambda(-1). \tag{6.4}
$$

Perfectness of the ambient pairing and of $b_P$ implies perfectness of $b_W$. Rescaling $b_P$ inversely rescales $b_W$ and changes no multiplier or determinant.

### 6.2 Two-dimensional similitudes

Let $W$ be two-dimensional over a field and let $\psi:W\times W\to M$ be a nonzero alternating form with values in a one-dimensional space $M$. For every $g\in\operatorname{GL}(W)$,

$$
\psi(gx,gy)=\det(g)\psi(x,y). \tag{6.5}
$$

**Proof.** Choose a basis $e_1,e_2$. Both sides are alternating bilinear forms, hence are determined by their value on $(e_1,e_2)$. Expanding $ge_1$ and $ge_2$ gives the $2\times2$ determinant. $\square$

This is the rank-two identity $\operatorname{GSp}_2=\operatorname{GL}_2$. It is stronger than the general determinant formula for higher-dimensional symplectic similitudes and has no square-root ambiguity.

Suppose $G_E$ acts on $M$ through a character $\delta$. If $\psi$ is Galois equivariant, (6.5) gives

$$
\det W=\delta. \tag{6.6}
$$

Thus the determinant problem is reduced to identifying the one-dimensional target of the pairing.

### 6.3 The central-component character

The component set of the Shimura curve is finite, and canonical reciprocity makes its permutation representation a finite continuous $G_E$-set. Let $\kappa_\Pi$ denote the relevant finite automorphic character of the component quotient. Its line in the component permutation module acquires through reciprocity a Galois character

$$
\eta_\Pi:G_E\longrightarrow L^\times. \tag{6.7}
$$

Its image is finite. The normalization is chosen so that at a good unramified place $u$ above $v$,

$$
\eta_\Pi(\operatorname{Frob}^{\mathrm{arith}}_u)
=s_v(\Pi)^{-1}. \tag{6.8}
$$

The inverse is forced by right translation and by the passage from geometric to arithmetic Frobenius. Equivalently,

$$
\eta_\Pi(\Phi_u)=s_v(\Pi). \tag{6.9}
$$

Book 132 unconditionally gives the perfect pairing with the adjoint block in (6.4). It does not by itself give an alternating self-pairing on $W_\Pi$. The extra input needed here will be called a **curve determinant datum**. It consists of:

1. an actual component-character twisting correspondence $M_{\kappa_\Pi^{-1}}$, with its Galois covariance under canonical reciprocity, which realizes the typed automorphic adjoint identity

$$
\Pi^\dagger\simeq
\Pi\otimes(\kappa_\Pi^{-1}\circ\nu)
$$

on the component-stable cohomological realization; and

2. a polarization-compatible identification of the finite modules in (6.3) for which the induced form on $P_\Pi$ is symmetric, so the alternating sign of ambient curve Poincare duality remains alternating on the multiplicity factor.

The first clause is stronger than equality of central eigenvalues: the twisting operator and its covariance must descend. The second clause is essential at old level. The sign of the multiplicity pairing cannot be inferred merely from its dimension; if the finite-module form were alternating, the tensor sign would leave a symmetric form on $W_\Pi$ instead.

Under this datum, the adjoint identity inserts the finite component line; it is not a Tate twist. Multiplicity extraction gives

$$
W_{\Pi^\dagger}\simeq W_\Pi\otimes\eta_\Pi^{-1}.
$$

Choose a basis vector $e$ of the $\eta_\Pi^{-1}$ line and evaluate (6.4) on $(x,y\otimes e)$. Galois equivariance says

$$
b_W(gx,g(y\otimes e))
=\chi_\ell(g)^{-1}b_W(x,y\otimes e).
$$

Since $g(y\otimes e)=\eta_\Pi(g)^{-1}gy\otimes e$, moving the character scalar across the equality shows that the induced form on $W_\Pi\times W_\Pi$ has multiplier $\chi_\ell^{-1}\eta_\Pi$. Substituting the adjoint identification and the symmetric finite-module pairing into (6.4) gives a Galois-equivariant alternating pairing

$$
\psi_\Pi:W_\Pi\times W_\Pi
\longrightarrow L_\lambda(-1)\otimes\eta_\Pi. \tag{6.10}
$$

Here $\eta_\Pi$ denotes its one-dimensional $L_\lambda$-space. This is exactly the place where the central operator $S_v$ enters. If the central character is trivial on the chosen stable component union, then $\eta_\Pi=1$.

Equation (6.10) is not obtained by erasing $P_\Pi$ from (6.1). It uses every clause of the determinant datum. Without that datum one has only the pairing with $W_{\Pi^\dagger}$, which does not determine the determinant of $W_\Pi$.

### 6.4 The determinant theorem

Let $\chi_\ell:G_E\to\mathbf Z_\ell^\times$ be the cyclotomic character in the convention

$$
\chi_\ell(\operatorname{Frob}^{\mathrm{arith}}_u)=q_u.
$$

Assume the curve determinant datum of Section 6.3. The target of (6.10) has character $\chi_\ell^{-1}\eta_\Pi$. Applying (6.6) proves

$$
\boxed{
\det\rho_{\Pi,\lambda}
=\chi_\ell^{-1}\eta_\Pi.}
\tag{6.11}
$$

Semisimplification does not change the determinant, so (6.11) holds for both the raw multiplicity representation and the extracted semisimple representation.

At a good place, evaluate on geometric Frobenius. Since $\chi_\ell(\Phi_u)=q_u^{-1}$ and (6.9) holds,

$$
\boxed{
\det(\Phi_u\mid\rho_{\Pi,\lambda})
=q_us_v(\Pi).}
\tag{6.12}
$$

For arithmetic Frobenius, inversion gives

$$
\det(\operatorname{Frob}^{\mathrm{arith}}_u)
=(q_us_v(\Pi))^{-1}. \tag{6.13}
$$

The two formulas concern inverse operators. Neither is a different determinant convention.

## 7. Parity at real places

For a two-dimensional representation of the Galois group of a totally real field, oddness means that every complex conjugation has determinant $-1$. The Hodge structure of the curve multiplicity space proves this directly.

### 7.1 Complex conjugation and Hodge lines

Fix a real embedding $\tau:E\hookrightarrow\mathbf R$ and a complex conjugation $c_\tau\in G_E$. Assume the individual coefficient block is preserved by the real descent action. Betti comparison gives

$$
W_{\Pi,B}\otimes_{L,\iota}\mathbf C
=W^{1,0}\oplus W^{0,1},
\qquad \dim W^{1,0}=\dim W^{0,1}=1. \tag{7.1}
$$

The topological involution induced by the real place is coefficient-linear, commutes with every descended correspondence, and interchanges the two Hodge lines. This is distinct from the antilinear scalar-conjugation operation which also changes a coefficient embedding. The involution cannot act as a scalar on $W_{\Pi,B}$, because a scalar would preserve each complex line. Since $c_\tau^2=1$ and the coefficient characteristic is zero, its eigenvalues lie in $\{1,-1\}$. Nonscalarity forces both eigenvalues to occur.

Therefore

$$
\operatorname{Tr}(c_\tau\mid W_{\Pi,B})=0,
\qquad
\det(c_\tau\mid W_{\Pi,B})=-1. \tag{7.2}
$$

Comparison transports the characteristic polynomial $X^2-1$ to every $\lambda$-adic realization.

### 7.2 Oddness of the extracted representation

**Theorem 7.1 (parity).** If the rank-two packet is realized in Shimura-curve $H^1$ over a totally real field $E$ and its individual coefficient block is preserved by every real descent action, then

$$
\det\rho_{\Pi,\lambda}(c_\tau)=-1 \tag{7.3}
$$

for every real place $\tau$ of $E$.

**Proof.** Equation (7.2) proves the assertion on the Betti multiplicity space. Betti--etale comparison respects the rational projector and the algebraic correspondence factorization, so it gives the same characteristic polynomial for $c_\tau$ on $W_{\Pi,\lambda}$. Equation (4.4) preserves determinant under semisimplification. $\square$

When the curve determinant datum is available, the determinant formula gives a second check. Since $\chi_\ell(c_\tau)=-1$, equation (6.11) yields

$$
\det\rho(c_\tau)=-\eta_\Pi(c_\tau). \tag{7.4}
$$

Comparison with (7.3) therefore forces $\eta_\Pi(c_\tau)=1$ for every determinant datum occurring in constant-coefficient curve cohomology. Any proposed component normalization which is odd at a real place is incompatible with that datum.

### 7.3 Reducible and scalar cases

Oddness does not imply irreducibility. If

$$
\rho^{\mathrm{ss}}=\chi_1\oplus\chi_2,
$$

then (7.3) says that exactly one of $\chi_1(c_\tau)$ and $\chi_2(c_\tau)$ is $-1$. A nonsplit extension of these characters is also odd because determinant ignores the extension class.

Nor does oddness rule out scalar Frobenius at a finite place. A complex conjugation and a good Frobenius are unrelated elements; the former is forced to have distinct eigenvalues, while the latter can act as a scalar. This is why the scalar case in Chapter 8 must be handled by determinant rather than excluded by parity.

### 7.4 Where parity is not defined

If the base field has no real place, there is no complex conjugation in its absolute Galois group and the adjectives odd and even do not apply.

If a rank-two representation over a totally real subfield is later restricted to a CM extension, it remembers that it came from an odd representation, but oddness is a property of the representation before restriction. It cannot be reconstructed merely from the restricted determinant.

## 8. Good-prime Frobenius polynomials

At a good place, geometry provides an operator relation. Under the curve determinant datum, linear algebra and the determinant theorem identify the characteristic polynomial without assuming that Frobenius is nonscalar. Without that datum, Book 132's unconditional output remains the annihilator of Section 8.2, with equality to the characteristic polynomial whenever Frobenius is nonscalar.

### 8.1 The full good-reduction ledger

Let $u$ be a finite place of the reflex field above a place $v$ with residue cardinality $q_v$. The good-prime theorem requires all of the following:

- the unramified local reflex identification gives the same residue field at $u$ and $v$, so $q_u=q_v$;
- the quaternion algebra and PEL endomorphism algebra are unramified at $v$;
- the level is hyperspecial at $v$;
- the polarization lattice is self-dual and its polarization degree is prime to the residue characteristic;
- the determinant local model is the smooth one-dimensional unramified model;
- the neighboring-subgroup problem has the proved standard rank-one incidence local-model diagram;
- the rank-one Hasse invariant is nonzero on every selected geometric component, equivalently the relevant $\mu$-ordinary locus is dense there;
- the selected component union extends over the local base and is stable under $T_v$ and $S_v$;
- the level is neat, or the calculation is made on the stack and descended through a tame neat cover;
- the residue characteristic does not equal $\ell$.

Under these hypotheses the Shimura curve has a smooth proper model. Smooth proper base change gives unramifiedness and identifies geometric Frobenius on generic cohomology with Frobenius on the special fiber. The two Hecke correspondences extend and commute with specialization.

A split group at $v$ is not enough. Iwahori level, a non-self-dual lattice, a singular determinant local model, an unproved incidence diagram, failure of density on a selected component, a residue-field mismatch, or wild coarse descent invalidates the displayed quadratic relation.

### 8.2 From the correspondence relation to an annihilator

On full untwisted $H^1$, the good-prime relation is

$$
\Phi_u^2-T_v\Phi_u+q_vS_v=0. \tag{8.1}
$$

Since $e_\Pi$, $T_v$, and $S_v$ commute with Galois and the finite Hecke algebra acts only on $P_\Pi$, restriction through (3.7) gives

$$
\Phi_u^2-t_v(\Pi)\Phi_u+q_vs_v(\Pi)=0
\quad\text{on }W_{\Pi,\lambda}. \tag{8.2}
$$

Thus

$$
Q_{v,\Pi}(X)=X^2-t_v(\Pi)X+q_vs_v(\Pi) \tag{8.3}
$$

annihilates geometric Frobenius.

At this point (8.3) is not yet known to be the characteristic polynomial. A scalar operator $cI$ is annihilated by every polynomial having $c$ as a root, while its characteristic polynomial is $(X-c)^2$.

### 8.3 Determinant upgrades annihilation to characteristic polynomial

The following elementary lemma removes the scalar ambiguity.

**Lemma 8.1.** Let $V$ be two-dimensional, let $F\in\operatorname{GL}(V)$, and suppose

$$
F^2-aF+bI=0,
\qquad \det F=b. \tag{8.4}
$$

Then

$$
\det(X-F\mid V)=X^2-aX+b. \tag{8.5}
$$

**Proof.** Cayley--Hamilton gives

$$
F^2-(\operatorname{Tr}F)F+(\det F)I=0.
$$

Subtracting (8.4) and using $\det F=b$ gives

$$
(\operatorname{Tr}F-a)F=0.
$$

Since $F$ is invertible, $\operatorname{Tr}F=a$. Substitution into Cayley--Hamilton proves (8.5). $\square$

Assume the curve determinant datum. Apply the lemma with $F=\Phi_u$, $a=t_v(\Pi)$, and $b=q_vs_v(\Pi)$. Equation (6.12) supplies the determinant. Therefore

$$
\boxed{
\det(X-\rho_{\Pi,\lambda}(\Phi_u))
=X^2-t_v(\Pi)X+q_vs_v(\Pi).}
\tag{8.6}
$$

This proof includes scalar Frobenius. If $\Phi_u=cI$, equations (8.2) and (6.12) force $2c=t_v$ and $c^2=q_vs_v$, so (8.3) is automatically $(X-c)^2$.

### 8.4 Geometric and arithmetic Frobenius

Let the roots of (8.6) be $\alpha_u,\beta_u$. Arithmetic Frobenius acts by their inverses. Hence

$$
\det\left(X-\rho(\operatorname{Frob}^{\mathrm{arith}}_u)\right)
=X^2-\frac{t_v(\Pi)}{q_vs_v(\Pi)}X
+\frac{1}{q_vs_v(\Pi)}. \tag{8.7}
$$

On the covariant Tate module $H^1(1)$ there is an additional twist. Arithmetic Frobenius eigenvalues become $q_u\alpha_u^{-1}$ and $q_u\beta_u^{-1}$ in the normalization of the Jacobian comparison. In the basic $q_u=q_v$ case, this yields

$$
X^2-s_v(\Pi)^{-1}t_v(\Pi)X
+q_vs_v(\Pi)^{-1}, \tag{8.8}
$$

the covariant Tate-module polynomial. Equations (8.6)--(8.8) are compatible conversions, not alternative guesses.

## 9. Integral lattices and congruences

Rational extraction separates packets. Integral cohomology records the primes at which they fail to separate. A correct integral statement begins with the ambient lattice, takes intersections, and uses saturation; it never assumes that a rational projector is integral.

### 9.1 The ambient cohomological lattice

For a smooth proper curve,

$$
\Lambda_\ell=H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell) \tag{9.1}
$$

is finite free. It is stable under $G_E$ and every integral Hecke correspondence. Poincare duality gives a perfect pairing into $\mathbf Z_\ell(-1)$.

### 9.2 Saturated packet lattices

Let $e$ be a packet idempotent over $L_\lambda$, put
$\Lambda_{L}=\Lambda_\ell\otimes_{\mathbf Z_\ell}\mathcal O_{L_\lambda}$, and define

$$
\Lambda[e]
=\Lambda_L\cap e(\Lambda_L\otimes_{\mathcal O_{L_\lambda}}L_\lambda). \tag{9.2}
$$

The quotient of the ambient rational space by the image of $e$ is a vector space, so (9.2) is saturated: if a uniformizer times $x\in\Lambda_L$ lies in $\Lambda[e]$, then $x$ already lies in the same rational subspace.

The lattice (9.2) is Galois and Hecke stable and spans the desired rational block. It need not be a direct summand. If $e$ contains an interpolation denominator divisible by $\ell$, congruent packets meet in the reduction of their saturated lattices.

At coarse level there is an independent denominator: descent from a fine cover divides by the effective deck-group order. Thus stabilizer denominators and Hecke-projector denominators must be audited separately.

### 9.3 Integral Morita extraction

Let $\mathcal A$ be an order in the split matrix algebra $M_d(L_\lambda)$ and let $\mathcal P$ be an $\mathcal A$-stable lattice in the simple left module $P$. The natural candidate is the $\mathcal O_{L_\lambda}$-module

$$
\mathcal W
=\operatorname{Hom}_{\mathcal A}(\mathcal P,\Lambda[e]). \tag{9.3}
$$

Rationally, evaluation becomes the isomorphism (3.7). Integrally, the typed evaluation map is

$$
\mathcal P\otimes_{\mathcal O_{L_\lambda}}\mathcal W
\longrightarrow\Lambda[e]. \tag{9.4}
$$

The tensor product is not over $\mathcal A$: both $\mathcal P$ and $\Lambda[e]$ are left $\mathcal A$-modules, while $\mathcal W$ is the multiplicity lattice. The map (9.4) is an isomorphism when $\mathcal P$ is an $(\mathcal A,\mathcal O_{L_\lambda})$-progenerator giving an integral Morita equivalence; in the split model this means

$$
\mathcal A\simeq\operatorname{End}_{\mathcal O_{L_\lambda}}(\mathcal P),
\qquad
\operatorname{End}_{\mathcal A}(\mathcal P)\simeq\mathcal O_{L_\lambda}.
$$

Then Morita theory gives evaluation for every left $\mathcal A$-module in its scope. Without this integral progenerator property, rational evaluation can be an isomorphism while the image of (9.4) has finite index in $\Lambda[e]$; that is the integral evaluation defect. Failure can occur at primes dividing the discriminant of the order. Projector and deck denominators are independent earlier obstructions to obtaining the lattice as an ambient direct summand.

Without them, one may still choose any stable lattice in the rational $W$, or take the image and saturation of (9.3). What one may not claim is a canonical free rank-two direct summand of ambient cohomology.

### 9.4 Reduction and determinant

Let $\mathcal W$ be a stable rank-two lattice. Reduction gives

$$
\bar\rho:G_E\to\operatorname{GL}_2(k_\lambda). \tag{9.5}
$$

Its isomorphism class can depend on $\mathcal W$, though its semisimplification is independent of the stable lattice. To see the latter, two lattices are commensurable; a finite filtration of their quotient by powers of the uniformizer shows that the multisets of residual Jordan--Holder factors agree.

When the rational determinant identity (6.11) has been proved from a determinant datum, every stable lattice gives

$$
\det\bar\rho
=\bar\chi_\ell^{-1}\bar\eta_\Pi. \tag{9.6}
$$

Indeed, the determinant of the integral matrices reduces to the determinant of their residual matrices; no self-dual lattice is needed for this character identity. Perfectness matters for a different assertion. If (6.10) is only integral up to a nonunit scalar, its reduction can become degenerate, so the residual representation need not carry the claimed perfect alternating polarization. Rational nondegeneracy alone is not an integral polarization theorem.

## 10. Purity and local boundaries

The extraction theorem is strongest at good places away from the coefficient prime. Purity controls the size of Frobenius roots there. Semistable and coefficient-prime behavior require separate geometric theories and should not be inferred from the good polynomial.

### 10.1 Purity at good places

Let $u\nmid\ell$ be a good place. Smooth proper base change identifies curve $H^1$ with the $H^1$ of a smooth projective special fiber. Its geometric Frobenius eigenvalues are pure of weight one. A Galois-stable Hecke direct summand and its multiplicity factor inherit the same roots, so every complex embedding satisfies

$$
|\iota(\alpha_u)|=q_u^{1/2}. \tag{10.1}
$$

The annihilator (8.2), together with purity and the finite image of the central character, implies

$$
|\iota(t_v(\Pi))|\le 2q_u^{1/2},
\qquad
|\iota(s_v(\Pi))|=1 \tag{10.2}
$$

when $q_u=q_v$ and the central character has finite image. The first inequality is the triangle inequality applied to the two roots; the second follows from their product and purity.


### 10.2 What follows for rank two

Under the curve determinant datum, combine purity and the determinant:

$$
\alpha_u\beta_u=q_us_v(\Pi),
\qquad
|\alpha_u|=|\beta_u|=q_u^{1/2}. \tag{10.3}
$$

The reciprocal-duality relation is

$$
\{\alpha_u,\beta_u\}
=\{q_us_v(\Pi)/\alpha_u,
q_us_v(\Pi)/\beta_u\}. \tag{10.4}
$$

In dimension two this merely interchanges the two roots, but it is a useful normalization check.

Purity does not prove that the raw representation is semisimple, and it does not determine inertia at a bad place. A nonsplit extension of two pure characters can have the same good characteristic polynomials as their direct sum.

### 10.3 Semistable places

Suppose that, after a finite extension of the local field, the Shimura curve admits a strict semistable model and that every prime-to-residue-characteristic correspondence used in the packet projector extends to the model and preserves its strata. The curve formalism of Book 20 then supplies the monodromy operator

$$
N:H^1\longrightarrow H^1(-1),
\qquad N^2=0. \tag{10.5}
$$

The Weil--Deligne package retains the finite descent action; on the unipotent subgroup inertia acts by $\exp(t_\ell(\sigma)N)=1+t_\ell(\sigma)N$. Because the extended Hecke correspondences commute with restriction, Gysin, finite descent, Frobenius, and monodromy, $N$ restricts to the packet block and passes through the multiplicity Hom construction to $W_{\Pi,\lambda}$.

The rank of $N$ is governed by the packet part of the dual graph, not merely by the number of nodes. Unramifiedness is equivalent to vanishing of this restricted $N$ together with trivial finite inertia. A compact-type singular fiber can have $N=0$ despite bad reduction. For geometric Frobenius in the convention of Section 1.2, $FNF^{-1}=q^{-1}N$.

These statements are an interface: they apply only after the semistable model, stratum-compatible extensions, and finite descent data have been supplied. They concern the raw cohomological multiplicity space. Passing to the global Galois semisimplification of Chapter 4 can kill the unipotent extension carrying $N$ and can change the conductor, so it must not be substituted for the full Weil--Deligne representation.

### 10.4 The coefficient prime and other boundaries

When $u\mid\ell$, smooth proper etale cohomology still gives a continuous representation, but the prime-to-residue-characteristic argument used for unramified Frobenius and tame monodromy no longer applies. Crystalline, de Rham, finite-flat, or Fontaine--Laffaille properties require additional comparison theorems and integral hypotheses. They are not consequences of (8.6).

At a bad level prime, the operator is usually $U_v$, not the spherical $T_v$. Its adjoint, degree, and local polynomial depend on the integral correspondence. Substituting $U_v$ into (8.6) without a special-fiber calculation is invalid.

The present book also does not prove independence of the integral lattice from $\ell$, bad-prime local--global compatibility, or existence of finite-flat quotients. It supplies the rank-two rational representation, its determinant, parity, semisimplification, coefficient field, and good-prime polynomial on the exact geometric range where those conclusions follow.

## 11. Diagnostic examples and failure modes

The extraction formalism is easiest to trust after testing the three situations which most often lead to a wrong dimension or a wrong Frobenius polynomial.

### 11.1 A minimal curve packet

Assume $P_\Pi$ is one-dimensional, the packet is separated by a commutative Hecke character, and the descended component-twist clause of the determinant datum is available. The finite-module pairing on a line is symmetric, so the determinant datum is complete. Then

$$
e_\Pi H^1_\ell(C_K)=W_{\Pi,\lambda}
$$

is two-dimensional. Its Hodge types are $(1,0)$ and $(0,1)$, and every complex conjugation has eigenvalues $1,-1$. At a good place,

$$
\det(X-\Phi_u)=X^2-t_vX+q_vs_v.
$$

If $s_v=1$, the determinant character is $\chi_\ell^{-1}$. No choice of a normalized holomorphic differential selects a Galois-stable line: the holomorphic line exists only in the complex Hodge realization.

### 11.2 A three-dimensional oldspace

Suppose $\dim P_\Pi=3$. Then the packet part of cohomology has dimension six:

$$
e_\Pi H^1=P_\Pi\otimes W_\Pi,
\qquad \dim W_\Pi=2. \tag{11.1}
$$

Galois acts as $1\otimes\rho_\Pi$. Choosing one oldvector gives a two-dimensional subspace only after a noncanonical choice and need not be preserved by the full level Hecke algebra. The Hom space (3.5) recovers $W_\Pi$ without choosing an oldvector.

If one uses only the good spherical character, all three oldvectors can appear as a scalar Hecke multiplicity. The full finite Hecke image is needed to justify (11.1).

### 11.3 A scalar Frobenius

Let $F=cI$ on a two-dimensional space. Suppose

$$
F^2-aF+bI=0.
$$

This says only $c^2-ac+b=0$. For example, $X^2-3X+2$ annihilates $I$, but the characteristic polynomial of $I$ is $(X-1)^2$. Dimension plus annihilation is insufficient.

If one also knows $\det F=b$, then $c^2=b$. Subtracting gives $c(2c-a)=0$, and invertibility gives $a=2c$. The annihilator becomes $(X-c)^2$, exactly the characteristic polynomial. This is the scalar case of Lemma 8.1 and explains why the determinant theorem is logically prior to (8.6).

## 12. The extraction theorem

We now collect the constructions into one theorem for the compact Shimura-curve source.

### 12.1 Complete statement

**Theorem 12.1 (rank-two extraction from weight-two Shimura-curve cohomology).** Let $E$ be the reflex field of the compact Shimura datum below, let $\ell$ be a prime, and let $\Pi$ be a noncharacter parallel-weight-two packet with coefficient field $L_\Pi$.

Assume $C_K/E$ is a smooth projective, Galois-stable and Hecke-stable component union for a quaternion division algebra split at exactly one real place. Assume the level is fine, or work rationally through a fine normal cover. Let $A$ be the full finite adjoint-stable Hecke image on $H^1$, and let $e_\Pi$ be the rational packet block. Assume for parts 3 and 5 that the curve determinant datum of Section 6.3 has been supplied. Then, after a finite field $L/L_\Pi$ splitting the simple factor of $A$ and for every $\lambda\mid\ell$:

1. the multiplicity space

   $$
   W_{\Pi,\lambda}
   =\operatorname{Hom}_{A_{L_\lambda}}
   (P_{\Pi,\lambda},e_\Pi H^1_\ell(C_K)\otimes L_\lambda)
   $$

   is two-dimensional and carries a continuous $G_E$-action;

2. its canonical semisimplification

   $$
   \rho_{\Pi,\lambda}:G_E\to\operatorname{GL}_2(L_\lambda)
   $$

   is a continuous semisimple representation, well defined up to coefficient extension and isomorphism;

3. if $\eta_\Pi$ is the finite central-component character normalized by (6.8), then

   $$
   \det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi;
   $$

4. if $E$ is totally real and the individual coefficient block is preserved by every real descent action, the representation is odd at every real place;

5. at every place $u\nmid\ell$ satisfying the full good integral-model, hyperspecial, self-dual, component-stability, and unramified hypotheses, it is unramified and

   $$
   \det(X-\rho_{\Pi,\lambda}(\Phi_u))
   =X^2-t_v(\Pi)X+q_vs_v(\Pi);
   $$

6. the roots in part 5 are pure of weight one;

7. after extension to $\mathcal O_{L_\lambda}$, the intersection of the packet block with integral $H^1$ is a saturated Galois- and Hecke-stable lattice. It is not asserted to be a direct summand, nor is its integral rank-two Morita factor asserted canonical, unless the deck, projector, order, and evaluation denominators are $\ell$-adic units.

Without the curve determinant datum, assertions 1, 2, 4, 6, and 7 remain valid, and the good-prime quadratic of part 5 is an annihilator; it is the characteristic polynomial at every nonscalar Frobenius. No unconditional determinant identification or scalar-Frobenius upgrade is then asserted.


### 12.2 Proof

The finite Hecke image is semisimple because transpose makes its complex image adjoint stable. Its central idempotent cuts out a Galois-stable packet block by descent of the Hecke correspondences. A finite coefficient extension splits the simple block. The automorphic decomposition of curve $H^1$ gives multiplicity two, and Theorem 3.1 converts that multiplicity into the two-dimensional Hom space. Section 4.1 proves continuity. Section 4.3 constructs its continuous semisimplification and proves that trace and determinant are unchanged. This proves parts 1 and 2.

Poincare duality pairs the packet with its adjoint. Under the determinant datum, factoring the pairing through the symmetric finite Hecke-module pairing and using the descended component-character identification gives the alternating pairing (6.10). The rank-two similitude identity (6.5) proves the determinant formula, hence part 3. Without that datum the proof stops at adjoint duality (6.4). The two Hodge lines are exchanged by every complex conjugation, so its eigenvalues are $1$ and $-1$. Comparison and invariance under semisimplification prove part 4 independently of the determinant datum.

At a good place, smooth proper base change gives unramifiedness and transfers the special-fiber correspondence identity to geometric generic cohomology. Restriction to the Hom space gives the quadratic annihilator (8.2). The determinant formula gives (6.12), and Lemma 8.1 upgrades the annihilator to the characteristic polynomial even when Frobenius is scalar. This proves part 5. Purity of smooth projective curve $H^1$ passes to the packet block and its multiplicity factor, proving part 6.

Integral cohomology is finite free and stable under Galois and integral correspondences. Intersection with a rational direct summand is saturated. Sections 9.2--9.3 exhibit the independent denominators obstructing direct-summand and integral Morita statements, proving part 7.

This proves all assertions. $\square$

### 12.3 Dependency and hypothesis ledger

| Conclusion | Established input | Hypothesis retained | Failure if omitted |
|---|---|---|---|
| continuous Galois action on curve cohomology | finite etale descent and continuous etale $H^1$ from Books 19 and 20 | smooth proper curve and finite-dimensional adic cohomology | the acting group or coefficient topology can be wrong |
| commuting Hecke and Galois actions | pull--trace correspondence formalism of Book 20 and descended curve spans of Book 132 | both legs and the selected component union defined over $E$ | invariant eigenvalues do not imply an equivariant operator |
| common rational structures and Hodge lines | Betti--de Rham--etale comparison from Book 27 | smooth proper curve and a chosen complex embedding | dimensions alone do not identify realizations or correspondences |
| rank-two curve factor | automorphic decomposition and double-centralizer block of Book 132 | full finite Hecke image and a splitting field | an old packet has total dimension $2\dim P_\Pi$ |
| continuous semisimple representation | closed-subspace continuity and Jordan--Holder semisimplification in Chapter 4 | finite-dimensional characteristic-zero coefficients | raw extension classes need not split |
| determinant | adjoint Poincare pairing of Book 132 and the rank-two identity of Book 123 | descended component-twist covariance and a polarization-compatible symmetric pairing on the finite module | adjoint duality alone gives no alternating self-pairing or determinant line |
| oddness | comparison of Book 27 and the weight-one Hodge types of Book 132 | totally real acting field and preservation of the individual coefficient block | parity is undefined or unsupported otherwise |
| good characteristic polynomial | good correspondence relation of Book 132 plus the determinant theorem | full good-model ledger, $u\nmid\ell$, and the determinant datum for scalar Frobenius | the relation may fail or remain only an annihilator |
| integral packet lattice | finite-free curve cohomology from Book 20 and the packet block of Book 132 | coefficient extension, intersection, and saturation | rational projectors can have nonunit denominators |
| semistable curve interface | curve monodromy formalism of Book 20 | supplied strict semistable model, finite descent, and stratum-compatible correspondence extensions | a good-prime polynomial determines neither inertia nor $N$ |

The exact direct dependency row is

$$
\boxed{134\mid 19,\ 20,\ 27,\ 123,\ 132.}
$$

Book 19 supplies finite etale descent, continuity, and the arithmetic-versus-geometric Frobenius convention. Book 20 supplies smooth proper curve cohomology, pullback and trace, Poincare duality, the finite-free integral lattice, good reduction, and the conditional strict-semistable monodromy interface. Book 27 supplies the compatible Betti, de Rham, and etale realizations, Hodge lines, and correspondence compatibility. Book 123 supplies the rank-two similitude identity, the Schur/corestriction obstruction, tensor-pairing parity, and integral perfectness warnings. Book 132 supplies the compact Shimura-curve packet decomposition, exact multiplicity two, full finite Hecke block, component descent, good-prime annihilator, and saturated packet lattice.

No later attachment, local--global compatibility, compatible-system, or finite-flat theorem is used. The determinant and scalar-Frobenius conclusions remain conditional on the exact curve determinant datum of Section 6.3.

### 12.4 Conclusion

The passage from Shimura-curve cohomology to a rank-two Galois representation is now an auditable sequence of algebraic operations. A Hecke projector isolates a rational packet, but it does not remove oldvectors. The simple finite Hecke module accounts for those vectors; its multiplicity space accounts for arithmetic. On a compact Shimura curve that multiplicity is exactly two, so the Hom construction produces the desired continuous representation at every coefficient place, independently of a choice of eigenvector.

The representation is taken semisimply in a precise sense which preserves every trace and determinant while making no unsupported claim about extension classes in raw cohomology. Its coefficient field is the Hecke field only after the possible Schur obstruction has been split. Poincare duality unconditionally gives duality with the adjoint block. When the descended component twist and polarization-compatible symmetric finite-module pairing of Section 6.3 are supplied, they give the alternating target

$$
L_\lambda(-1)\otimes\eta_\Pi,
$$

so the two-dimensional similitude identity determines

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi.
$$

This determinant datum is the missing input in the good-prime calculation. The geometric correspondence first gives only a quadratic annihilator. Combining it with the independently known determinant proves, including in the scalar case,

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_u))
=X^2-t_v(\Pi)X+q_vs_v(\Pi).
$$

Without that datum, the determinant and scalar-Frobenius upgrade remain open; at nonscalar Frobenius the annihilator is already the characteristic polynomial.

When real descent preserves the individual coefficient block, the Hodge lines prove oddness over a totally real field; smooth projective purity gives weight one without this parity hypothesis. Saturation supplies an integral stable lattice, while projector, coarse-level, and Morita denominators explain why an integral direct summand is a stronger theorem.
