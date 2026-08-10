# Galois Representations from Weight-Two Shimura Cohomology

## Contents

- [1. From a cohomological packet to a Galois representation](#1-from-a-cohomological-packet-to-a-galois-representation)
  - [1.1 The extraction problem](#11-the-extraction-problem)
  - [1.2 Standing conventions](#12-standing-conventions)
  - [1.3 The two geometric sources](#13-the-two-geometric-sources)
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
- [9. The degree-two surface block](#9-the-degree-two-surface-block)
  - [9.1 What the surface gives unconditionally](#91-what-the-surface-gives-unconditionally)
  - [9.2 Cancellation algebras](#92-cancellation-algebras)
  - [9.3 Rank-two extraction after cancellation](#93-rank-two-extraction-after-cancellation)
  - [9.4 Why a Hodge half is not a Galois constituent](#94-why-a-hodge-half-is-not-a-galois-constituent)
- [10. Comparing curve and surface realizations](#10-comparing-curve-and-surface-realizations)
  - [10.1 Common packet data](#101-common-packet-data)
  - [10.2 Weight and twist constraints](#102-weight-and-twist-constraints)
  - [10.3 A comparison criterion](#103-a-comparison-criterion)
  - [10.4 Independence of a chosen carrier](#104-independence-of-a-chosen-carrier)
- [11. Integral lattices and congruences](#11-integral-lattices-and-congruences)
  - [11.1 The ambient cohomological lattice](#111-the-ambient-cohomological-lattice)
  - [11.2 Saturated packet lattices](#112-saturated-packet-lattices)
  - [11.3 Integral Morita extraction](#113-integral-morita-extraction)
  - [11.4 Reduction and determinant](#114-reduction-and-determinant)
- [12. Purity and local boundaries](#12-purity-and-local-boundaries)
  - [12.1 Purity at good places](#121-purity-at-good-places)
  - [12.2 What follows for rank two](#122-what-follows-for-rank-two)
  - [12.3 Semistable places](#123-semistable-places)
  - [12.4 The coefficient prime and other boundaries](#124-the-coefficient-prime-and-other-boundaries)
- [13. Diagnostic examples and failure modes](#13-diagnostic-examples-and-failure-modes)
  - [13.1 A minimal curve packet](#131-a-minimal-curve-packet)
  - [13.2 A three-dimensional oldspace](#132-a-three-dimensional-oldspace)
  - [13.3 A scalar Frobenius](#133-a-scalar-frobenius)
  - [13.4 A four-dimensional surface packet](#134-a-four-dimensional-surface-packet)
- [14. The extraction theorem](#14-the-extraction-theorem)
  - [14.1 Complete statement](#141-complete-statement)
  - [14.2 Proof](#142-proof)
  - [14.3 Dependency and hypothesis ledger](#143-dependency-and-hypothesis-ledger)
  - [14.4 Conclusion](#144-conclusion)

## 1. From a cohomological packet to a Galois representation

Weight-two automorphic forms enter arithmetic through cohomology, but cohomology is usually much larger than the representation one wants. It contains several automorphic packets, several level vectors for one packet, two archimedean orientations on a curve, and sometimes four orientations on a surface. The Galois group commutes with the Hecke correspondences, so it acts on the multiplicity left after the finite Hecke module has been removed. Extracting that multiplicity, rather than choosing an eigenvector, is the central construction of this book.

### 1.1 The extraction problem

Let $E$ be a number field, let $X/E$ be a smooth projective Shimura curve or a compact unitary Shimura surface, and fix a prime $\ell$. The geometric cohomology

$$
H^i_\ell(X)=H^i_{\mathrm{et}}(X_{\bar E},\mathbf Q_\ell)
$$

carries two commuting actions: a continuous action of $G_E=\operatorname{Gal}(\bar E/E)$ and an algebraic action of a finite Hecke image. A weight-two packet determines a rational central idempotent after its algebraic conjugates have been grouped. The first question is not whether the corresponding subspace exists; it does. The first question is which factor of that subspace carries Galois.

For a compact Shimura curve, the answer is particularly clean. Over a splitting field, a packet block has the form

$$
P_\Pi\otimes W_\Pi,
\qquad \dim W_\Pi=2, \tag{1.1}
$$

where $P_\Pi$ is the finite Hecke module of level vectors. Galois commutes with the Hecke algebra, hence acts on $W_\Pi$. Even when $\dim P_\Pi>1$, the arithmetic factor remains two-dimensional.

For a compact unitary surface, the honest packet block can have dimension four before level multiplicity. That four-dimensional space is pure of weight two. It is not permissible to select two of its Hodge lines and call them a Galois representation. A rank-two extraction from surface cohomology requires an additional simple algebra with descent action and a compatible rank-two module, together called a cancellation datum below. The distinction between the unconditional surface block and a cancellable surface block will remain visible in every theorem.

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

### 1.3 The two geometric sources

The curve source is the compact quaternionic Shimura curve $C_K/E$ of Book 132. Its constant-coefficient $H^1$ has a finite semisimple rational Hecke image. For a parallel-weight-two packet $\Pi$, a splitting field $L$ gives

$$
e_\Pi H^1_\ell(C_K)\otimes L_\lambda
\simeq P_{\Pi,\lambda}\otimes_{L_\lambda}W_{\Pi,\lambda},
\qquad \dim W_{\Pi,\lambda}=2. \tag{1.4}
$$

The curve is proper, so there is no boundary or Eisenstein contribution. The two dimensions in $W_{\Pi,\lambda}$ come from Hodge types $(1,0)$ and $(0,1)$, not from two automorphic occurrences.

The surface source is the compact unitary surface $S_C/E$ of Book 133. A full minimal noncharacter packet gives a four-dimensional block

$$
V_{\Pi,\lambda}\subset H^2_\ell(S_C)\otimes L_\lambda
$$

with Hodge numbers $(1,2,1)$ and weight two. Its good-prime Frobenius polynomial is obtained by projected Lefschetz traces and is independent of $\ell$. It is not the quadratic polynomial (1.3). The surface block may nevertheless contain a rank-two multiplicity after a split cancellation algebra acts; Chapters 9 and 10 state the exact hypothesis.

The common input is not an isomorphism between $H^1$ and $H^2$. It is the same quaternionic packet, the same good Hecke field, and the same central and component character. Weight and Tate twist forbid a direct Galois isomorphism between the two full blocks.

### 1.4 The logical order

The safe construction has seven stages.

1. Replace the abstract Hecke algebra by its finite image on the chosen cohomology group.
2. Cut out a rational block by a central idempotent, then extend coefficients only far enough to split its simple algebra.
3. Remove the simple finite Hecke module by a Hom construction.
4. Prove continuity and pass, when unconditional semisimplicity is desired, to the canonical semisimplification.
5. Factor Poincare duality and identify the determinant line, including its central-component character.
6. Use the determinant to turn the good-prime quadratic annihilator into the characteristic polynomial.
7. Intersect the rational constituent with the natural integral lattice, without claiming an integral direct sum unless all denominators are units.

Every later conclusion depends on this order. In particular, a good-prime polynomial cannot be called a characteristic polynomial before Stage 5, and a rational idempotent cannot be applied to an integral lattice before its denominators have been audited.

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

The same argument works integrally for the abstract integral Hecke action, but not necessarily for a rational idempotent. The ambient localized lattice is Galois stable; an individual rational packet lattice is obtained by saturation, as in Chapter 11.

## 3. Multiplicity-space extraction

The rank of a Galois constituent is the multiplicity with which a simple Hecke module occurs, not the total dimension of the localized cohomology. This is a double-centralizer statement. We prove it in the exact form used for Shimura-curve $H^1$ and for cancellable surface blocks.

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

where $v$ ranges outside a finite bad set. The finite rational Hecke image has a simple factor $D_\Pi$ whose center is a number field containing $L_\Pi$. Once the full separating Hecke data are included, this center is the field of rationality of the finite packet block.

There is a finite extension $L/L_\Pi$ for which

$$
D_\Pi\otimes_{L_\Pi}L\simeq M_d(L). \tag{5.2}
$$

The construction of $W_{\Pi,\lambda}$ is made over a completion of such an $L$. Enlarging $L$ simply extends scalars:

$$
W_{\Pi,\lambda}\otimes_{L_\lambda}L'_{\lambda'}
\simeq W_{\Pi,\lambda'}. \tag{5.3}
$$

### 5.2 Schur obstruction

Before splitting, the correct multiplicity object is not necessarily a vector space over the center. If $D_\Pi$ is a division algebra, a simple $D_\Pi$-module $P$ has endomorphism ring $D_\Pi^{\mathrm{op}}$, and

$$
\operatorname{Hom}_{D_\Pi}(P,e_\Pi H)
$$

naturally carries a right action of that opposite algebra. Choosing (5.2) converts this module into an ordinary vector space.

This is the same descent obstruction that appears for corestriction algebras in rank two. A split central simple algebra is an endomorphism algebra of a vector space of the expected dimension; a nonsplit algebra is not. Declaring a two-dimensional representation over $L_\Pi$ before checking the obstruction would amount to declaring the division algebra split.

The rational conjugacy-orbit block remains canonical over $\mathbf Q$. The rank-two realization is canonical up to finite coefficient extension and isomorphism. This is the strongest statement justified without a vanishing theorem for the Schur class.

### 5.3 Trace fields of the Galois constituent

Let $K_{\rho}$ be the subfield of $L$ generated by

$$
\operatorname{Tr}(\rho(g)),\qquad\det(\rho(g))
\quad(g\in G_E). \tag{5.4}
$$

For a semisimple representation these functions determine the isomorphism class after extension to an algebraic closure. To see this in dimension two, separate three cases.

If $\rho$ is absolutely irreducible, the algebra generated by its image is the full matrix algebra by the density theorem for irreducible matrix algebras. Equality of traces gives equality of the associated linear functional on this algebra, and the matrix units reconstruct an intertwiner. If $\rho=\chi_1\oplus\chi_2$, trace and determinant recover the unordered pair of characters through

$$
(X-\chi_1(g))(X-\chi_2(g)).
$$

If $\rho=\chi\oplus\chi$, the trace is $2\chi$. Thus the semisimple isomorphism class is controlled by trace and determinant in every case.

The representation need not descend to $K_\rho$ itself: an absolutely irreducible representation can retain a central simple Schur obstruction. It descends after a finite splitting extension. In the Shimura-curve construction, the chosen Hecke splitting field already supplies one.

### 5.4 Change of coefficient place

Fix an embedding $L\hookrightarrow\overline{\mathbf Q}_\ell$. It selects a place $\lambda$ and a representation over $L_\lambda$. A different embedding can select a conjugate packet. Algebraic conjugation sends

$$
t_v(\Pi)\mapsto\sigma(t_v(\Pi)),
\qquad
s_v(\Pi)\mapsto\sigma(s_v(\Pi)), \tag{5.5}
$$

and transports the whole construction to $\Pi^\sigma$.

The present book proves a coefficient-field statement at each $\lambda$ and common good-prime polynomials with coefficients in $L_\Pi$. It does not identify the underlying topological vector spaces for different primes $\ell$. Compatibility means that the polynomials arise from the same algebraic Hecke data, not that there is a linear map between an $\ell$-adic and an $\ell'$-adic space.

## 6. Duality and the determinant line

The quadratic Hecke relation becomes a characteristic polynomial only after the determinant is known independently. That determinant comes from the alternating pairing on the two-dimensional multiplicity space, together with the finite central-component character which records how the packet is paired with its adjoint.

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

The component set of the Shimura curve is finite, and canonical reciprocity makes its permutation representation a finite continuous $G_E$-set. A packet central and component character cuts out a one-dimensional line in the corresponding finite permutation module. Denote its Galois character by

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

We now spell out the adjoint step, because it is what turns a pairing between two packet labels into the determinant of one packet. In rank two, contragredience changes the finite packet by its inverse central character. With the right-double-coset convention, transpose sends $T(a)$ to $T(a^{-1})$ and reverses the component route. The resulting packet identity is

$$
\Pi^\dagger\simeq\Pi\otimes\eta_\Pi^{-1}
$$

on the component-stable cohomological realization. The tensor sign here means that the finite component line is inserted; it is not a Tate twist. To verify the identity, pass to the full finite Hecke module. Inverse double cosets give its contragredient, while a central element acts on the dual by the inverse scalar. The component permutation line supplies exactly that scalar. Since the full finite Hecke image separates the packet, the identities determine the adjoint simple block.

Multiplicity extraction consequently gives

$$
W_{\Pi^\dagger}\simeq W_\Pi\otimes\eta_\Pi^{-1}.
$$

Choose a basis vector $e$ of the $\eta_\Pi^{-1}$ line and evaluate (6.4) on $(x,y\otimes e)$. Galois equivariance says

$$
b_W(gx,g(y\otimes e))
=\chi_\ell(g)^{-1}b_W(x,y\otimes e).
$$

Since $g(y\otimes e)=\eta_\Pi(g)^{-1}gy\otimes e$, moving the character scalar across the equality shows that the induced form on $W_\Pi\times W_\Pi$ has multiplier $\chi_\ell^{-1}\eta_\Pi$. Substituting the adjoint identification into (6.4) gives a Galois-equivariant alternating pairing

$$
\psi_\Pi:W_\Pi\times W_\Pi
\longrightarrow L_\lambda(-1)\otimes\eta_\Pi. \tag{6.10}
$$

Here $\eta_\Pi$ denotes its one-dimensional $L_\lambda$-space. This is exactly the place where the central operator $S_v$ enters. If the central character is trivial on the chosen stable component union, then $\eta_\Pi=1$.

Equation (6.10) is not obtained by erasing $P_\Pi$ from (6.1). It uses the adjoint pairing (6.3), the contragredient packet identity, and the actual component-character descent. Without that descent one would have only the pairing with $W_{\Pi^\dagger}$, which does not determine the determinant of $W_\Pi$.

### 6.4 The determinant theorem

Let $\chi_\ell:G_E\to\mathbf Z_\ell^\times$ be the cyclotomic character in the convention

$$
\chi_\ell(\operatorname{Frob}^{\mathrm{arith}}_u)=q_u.
$$

The target of (6.10) has character $\chi_\ell^{-1}\eta_\Pi$. Applying (6.6) proves

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

Fix a real embedding $\tau:E\hookrightarrow\mathbf R$ and a complex conjugation $c_\tau\in G_E$. Betti comparison gives

$$
W_{\Pi,B}\otimes_{L,\iota}\mathbf C
=W^{1,0}\oplus W^{0,1},
\qquad \dim W^{1,0}=\dim W^{0,1}=1. \tag{7.1}
$$

Complex conjugation interchanges the two lines. It cannot act as a scalar on $W_{\Pi,B}$, because a scalar would preserve each complex line. Since $c_\tau^2=1$ and the coefficient characteristic is zero, its eigenvalues lie in $\{1,-1\}$. Nonscalarity forces both eigenvalues to occur.

Therefore

$$
\operatorname{Tr}(c_\tau\mid W_{\Pi,B})=0,
\qquad
\det(c_\tau\mid W_{\Pi,B})=-1. \tag{7.2}
$$

Comparison transports the characteristic polynomial $X^2-1$ to every $\lambda$-adic realization.

### 7.2 Oddness of the extracted representation

**Theorem 7.1 (parity).** If the rank-two packet is realized in Shimura-curve $H^1$ over a totally real field $E$, then

$$
\det\rho_{\Pi,\lambda}(c_\tau)=-1 \tag{7.3}
$$

for every real place $\tau$ of $E$.

**Proof.** Equation (7.2) proves the assertion on the Betti multiplicity space. Betti--etale comparison respects the rational projector and the algebraic correspondence factorization, so it gives the same characteristic polynomial for $c_\tau$ on $W_{\Pi,\lambda}$. Equation (4.4) preserves determinant under semisimplification. $\square$

The determinant formula gives a second check. Since $\chi_\ell(c_\tau)=-1$, equation (6.11) yields

$$
\det\rho(c_\tau)=-\eta_\Pi(c_\tau). \tag{7.4}
$$

For the constant-coefficient component characters allowed in the curve packet, the central-component normalization is even at real places, so $\eta_\Pi(c_\tau)=1$. Thus (7.4) agrees with (7.3).

### 7.3 Reducible and scalar cases

Oddness does not imply irreducibility. If

$$
\rho^{\mathrm{ss}}=\chi_1\oplus\chi_2,
$$

then (7.3) says that exactly one of $\chi_1(c_\tau)$ and $\chi_2(c_\tau)$ is $-1$. A nonsplit extension of these characters is also odd because determinant ignores the extension class.

Nor does oddness rule out scalar Frobenius at a finite place. A complex conjugation and a good Frobenius are unrelated elements; the former is forced to have distinct eigenvalues, while the latter can act as a scalar. This is why the scalar case in Chapter 8 must be handled by determinant rather than excluded by parity.

### 7.4 Where parity is not defined

If the base field has no real place, there is no complex conjugation in its absolute Galois group and the adjectives odd and even do not apply. A CM reflex field for a unitary surface therefore carries no intrinsic parity statement of the form (7.3).

If a rank-two representation over a totally real subfield is later restricted to a CM extension, it remembers that it came from an odd representation, but oddness is a property of the representation before restriction. It cannot be reconstructed merely from the restricted determinant.

## 8. Good-prime Frobenius polynomials

At a good place, geometry provides an operator relation. Linear algebra and the determinant theorem then identify the characteristic polynomial without assuming that Frobenius is nonscalar.

### 8.1 The full good-reduction ledger

Let $u$ be a finite place of the reflex field above a place $v$ with residue cardinality $q_v$. The good-prime theorem requires all of the following:

- the quaternion algebra and PEL endomorphism algebra are unramified at $v$;
- the level is hyperspecial at $v$;
- the local lattice is self-dual;
- the determinant and polarization data have smooth integral models;
- the selected component union extends over the local base and is stable under $T_v$ and $S_v$;
- $v$ does not divide the coefficient prime $\ell$.

Under these hypotheses the Shimura curve has a smooth proper model. Smooth proper base change gives unramifiedness and identifies geometric Frobenius on generic cohomology with Frobenius on the special fiber. The two Hecke correspondences extend and commute with specialization.

A split group at $v$ is not enough. Iwahori level, a non-self-dual lattice, or a singular determinant local model changes the special-fiber correspondence and invalidates the quadratic relation used below.

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

Apply the lemma with $F=\Phi_u$, $a=t_v(\Pi)$, and $b=q_vs_v(\Pi)$. Equation (6.12) supplies the determinant. Therefore

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

## 9. The degree-two surface block

The compact unitary surface supplies an indispensable cohomological carrier when the parity of the Shimura datum requires two active real factors. Its full packet is nevertheless a weight-two, usually four-dimensional representation. This chapter states exactly what is obtained before and after an additional cancellation algebra is present.

### 9.1 What the surface gives unconditionally

Let $e_\Pi$ be a noncharacter packet projector on the compact unitary surface. Book 133 constructs

$$
V_{\Pi,\lambda}
=e_\Pi H^2_\ell(S_C)\otimes L_\lambda. \tag{9.1}
$$

It is a continuous Galois representation. For a full minimal orientation packet,

$$
\dim V_{\Pi,\lambda}=4, \tag{9.2}
$$

its Hodge numbers are $(1,2,1)$, and its Poincare pairing has target $L_\lambda(-2)$. At good places it is unramified and pure of weight two. Projected Lefschetz traces determine

$$
R_{u,\Pi}(X)=\det(1-X\Phi_u\mid V_{\Pi,\lambda})
\in L_\Pi[X], \tag{9.3}
$$

independently of $\ell$.

None of these facts makes $V_{\Pi,\lambda}$ two-dimensional. Nor does the quadratic automorphic polynomial (8.3) equal (9.3): their degrees and weights differ.

### 9.2 Cancellation algebras

A **surface cancellation datum** for the packet consists of a finite-dimensional semisimple algebra $B_\Pi$, a two-dimensional simple left $B_\Pi$-module $R_\Pi$, and compatible continuous descent actions on $B_\Pi$, $R_\Pi$, and $V_{\Pi,\lambda}$ such that:

1. the algebra action is induced by algebraic correspondences whose span is stable under Galois descent;
2. $G_E$ normalizes the algebra action:

   $$
   g(bv)=g(b)g(v),
   \qquad g(br)=g(b)g(r);
   $$

   the action need not fix every $b\in B_\Pi$;
3. after the chosen coefficient extension,

   $$
   B_\Pi\simeq M_2(L_\lambda);
   $$

4. as a $B_\Pi$-module, $V_{\Pi,\lambda}$ is a direct sum of two copies of its standard module.

5. at a good place, the descended special-fiber tensor correspondence induces on the Hom factor the operator identity

   $$
   \Phi_u^2-t_v(\Pi)\Phi_u+q_vs_v(\Pi)=0.
   $$

   This is a relation in the Hom factor, not an identification with its characteristic polynomial.

The terminology reflects the tensor-corestriction picture of Book 123. A split corestriction algebra can act as an endomorphism algebra of a two-dimensional auxiliary factor; taking the multiplicity for that factor cancels it. If the corestriction algebra is nonsplit, the honest object remains a module for a division algebra. One cannot replace it by $M_2$ without extending coefficients enough to split it.

The descent condition is as important as splitness. An abstract matrix algebra visible only after choosing a complex Hodge decomposition need not be stable under arithmetic Galois. Conversely, requiring Galois to commute pointwise with $M_2(L_\lambda)$ would make its action on the standard module scalar and would not remove a genuine weight-one factor. The normalized action above is the correct tensor-descent condition: Galois may act on the matrix algebra by conjugation while preserving its isomorphism class.

### 9.3 Rank-two extraction after cancellation

Let $R_\Pi$ be the standard two-dimensional left $B_\Pi$-module. Define

$$
W^{\mathrm{surf}}_{\Pi,\lambda}
=\operatorname{Hom}_{B_\Pi}
(R_\Pi,V_{\Pi,\lambda}). \tag{9.4}
$$

Give this Hom space the action

$$
(g\cdot f)(r)=g\bigl(f(g^{-1}r)\bigr). \tag{9.5}
$$

It remains $B_\Pi$-linear. Indeed, if $b\in B_\Pi$, then

$$
\begin{aligned}
(g\cdot f)(br)
&=g\bigl(f(g^{-1}(b)g^{-1}(r))\bigr)\\
&=g\bigl(g^{-1}(b)f(g^{-1}r)\bigr)\\
&=b(g\cdot f)(r).
\end{aligned}
$$

Thus (9.4) is a continuous Galois representation even though Galois need not commute pointwise with the cancellation algebra.

The evaluation theorem gives

$$
R_\Pi\otimes W^{\mathrm{surf}}_{\Pi,\lambda}
\xrightarrow{\sim}V_{\Pi,\lambda}, \tag{9.6}
$$

and it is Galois equivariant for the diagonal action. Condition 4 gives

$$
\dim W^{\mathrm{surf}}_{\Pi,\lambda}=2. \tag{9.7}
$$

Its semisimplification is the rank-two representation extracted from the cancellable surface block.

Duality and determinant require one further typed input. The cancellation module must be pure of weight one at good places and carry a perfect alternating pairing

$$
R_\Pi\times R_\Pi\longrightarrow
L_\lambda(-1)\otimes\xi_\Pi
$$

for a specified finite character $\xi_\Pi$. Factoring the symmetric surface pairing through this alternating factor must leave the curve-normalized alternating target

$$
W^{\mathrm{surf}}_\Pi\times W^{\mathrm{surf}}_\Pi
\longrightarrow L_\lambda(-1)\otimes\eta_\Pi.
$$

Under that condition, weights add in (9.6), so the extracted factor is pure of weight one. Condition 5 gives the good annihilator; the determinant argument of Chapter 8 then upgrades it to the good characteristic polynomial. Parity follows after descent to a totally real field with the curve-normalized Hodge types.

This last pairing condition is not automatic from dimensions. A tensor product of two alternating forms is symmetric, and its twist is the sum of the two factor twists. Cancellation must remove one full weight-one factor, not a formal half twist.

### 9.4 Why a Hodge half is not a Galois constituent

Over $\mathbf C$, a full minimal surface packet has

$$
V_\mathbf C=V^{2,0}\oplus V^{1,1}_{+-}
\oplus V^{1,1}_{-+}\oplus V^{0,2}. \tag{9.8}
$$

The subspace $V^{2,0}\oplus V^{0,2}$ has dimension two, but there is no reason for it to be defined over the Hecke field or stable under $G_E$. Hodge decomposition is an archimedean structure. Arithmetic Galois acts on the etale realization, not on individual complex Hodge summands.

The middle pair of $(1,1)$ lines is no better. Their labels depend on the two orientations, and a component or conjugation action can interchange them. Only an algebraic projector commuting with Galois may define an arithmetic summand.

Thus the unconditional output of surface $H^2$ is (9.1). The rank-two output (9.4) is unconditional only when the cancellation datum has actually been supplied. This boundary prevents a four-dimensional weight-two representation from being silently replaced by a two-dimensional weight-one one.

## 10. Comparing curve and surface realizations

The same quaternionic packet can occur in curve $H^1$ and surface $H^2$. Their shared Hecke labels provide a powerful consistency check, but equality of labels is weaker than equality of Galois representations. A valid comparison must pass through the multiplicity or cancellation constructions.

### 10.1 Common packet data

For a packet $\Pi$ occurring in both carriers, the following data agree:

$$
L_\Pi,qquad t_v(\Pi),\qquad s_v(\Pi),
\qquad\eta_\Pi, \tag{10.1}
$$

at every common good place. Algebraic conjugation sends both carriers to the corresponding data for $\Pi^\sigma$. Their packet projectors are polynomials in the same abstract good Hecke operators, interpreted as correspondences on different varieties.

The total dimensions need not agree. At full minimal level they are two on the curve and four on the surface. Old level multiplies each by its own finite invariant dimension.

### 10.2 Weight and twist constraints

At a common good place, curve roots have absolute value $q^{1/2}$ and surface roots have absolute value $q$. An integral Tate twist changes weight by an even integer:

$$
\operatorname{wt}(V(n))=\operatorname{wt}(V)-2n. \tag{10.2}
$$

There is no integer $n$ carrying weight two to weight one. The pairings make the same point:

$$
W^{\mathrm{curve}}\times W^{\mathrm{curve},\dagger}
\to L(-1),
$$

$$
V^{\mathrm{surface}}\times V^{\mathrm{surface},\dagger}
\to L(-2). \tag{10.3}
$$

Therefore the full surface block is not a twist of the curve block.

After cancellation, equation (9.6) explains the weight difference honestly: the removed factor has weight one and pairing twist $(-1)$. No half Tate twist appears.

### 10.3 A comparison criterion

Let $W_1$ and $W_2$ be semisimple two-dimensional representations over $L_\lambda$. Suppose that outside a finite set they are unramified and satisfy

$$
\det(X-\Phi_u\mid W_1)
=\det(X-\Phi_u\mid W_2) \tag{10.4}
$$

for every good place in a set whose Frobenius conjugacy classes are dense in the relevant Galois quotient. Then $W_1\simeq W_2$.

**Proof.** Equality of characteristic polynomials gives equality of traces and determinants on the dense set. Continuity extends equality to its closure. Section 5.3 shows that trace and determinant determine a semisimple two-dimensional representation. $\square$

The density hypothesis is an input, not a consequence of the cohomological decompositions reviewed here. In applications where it is available, (8.6) makes (10.4) immediate from the common Hecke data.

### 10.4 Independence of a chosen carrier

Suppose a curve extraction and a cancellable surface extraction are both defined over the same Galois group, have the determinant (6.11), and have the good polynomial (8.6) on a dense Frobenius set. The comparison criterion gives an isomorphism of their semisimplifications.

This is the precise carrier-independence statement. It compares rank-two multiplicity spaces after both have been constructed. It does not compare the ambient cohomology groups, their Hodge weights, or their integral lattices.

If only the surface block exists and no cancellation datum has been supplied, there is nothing two-dimensional to compare. The common automorphic label remains valuable, but it is not a substitute for extraction.

## 11. Integral lattices and congruences

Rational extraction separates packets. Integral cohomology records the primes at which they fail to separate. A correct integral statement begins with the ambient lattice, takes intersections, and uses saturation; it never assumes that a rational projector is integral.

### 11.1 The ambient cohomological lattice

For a smooth proper curve,

$$
\Lambda_\ell=H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell) \tag{11.1}
$$

is finite free. It is stable under $G_E$ and every integral Hecke correspondence. Poincare duality gives a perfect pairing into $\mathbf Z_\ell(-1)$.

For a surface, $H^2$ can contain integral torsion in greater generality. The rational theory uses

$$
\Lambda_\ell^{\mathrm{tf}}
=H^2_{\mathrm{et}}(S_{C,\bar E},\mathbf Z_\ell)/\text{torsion}. \tag{11.2}
$$

It is a lattice in rational $H^2$. Perfect integral duality can involve adjacent-degree torsion, so self-duality of (11.2) is not asserted without an additional torsion-free hypothesis.

### 11.2 Saturated packet lattices

Let $e$ be a rational packet idempotent. Define

$$
\Lambda[e]
=\Lambda_\ell\cap e(\Lambda_\ell\otimes\mathbf Q_\ell). \tag{11.3}
$$

The quotient $(\Lambda_\ell\otimes\mathbf Q_\ell)/e(\Lambda_\ell\otimes\mathbf Q_\ell)$ is a vector space, so (11.3) is saturated: if $\ell x\in\Lambda[e]$ and $x\in\Lambda_\ell$, then $x$ already lies in the same rational subspace.

The lattice (11.3) is Galois and Hecke stable and spans the desired rational block. It need not be a direct summand. If $e$ contains an interpolation denominator divisible by $\ell$, congruent packets meet in the reduction of their saturated lattices.

At coarse level there is an independent denominator: descent from a fine cover divides by the effective deck-group order. Thus stabilizer denominators and Hecke-projector denominators must be audited separately.

### 11.3 Integral Morita extraction

Let $\mathcal A$ be an order in the split matrix algebra $M_d(L_\lambda)$ and let $\mathcal P$ be an $\mathcal A$-stable lattice in $P$. The natural candidate is

$$
\mathcal W
=\operatorname{Hom}_{\mathcal A}(\mathcal P,\Lambda[e]). \tag{11.4}
$$

Rationally, evaluation becomes the isomorphism (3.7). Integrally, three extra conditions are needed for

$$
\mathcal P\otimes_{\mathcal A}\mathcal W
\xrightarrow{\sim}\Lambda[e]: \tag{11.5}
$$

the order must be Morita-split, $\mathcal P$ must be projective over it, and the isotypic lattice must have no index defect relative to evaluation. These conditions can fail at primes dividing the discriminant of the order or a projector denominator.

Without them, one may still choose any stable lattice in the rational $W$, or take the image and saturation of (11.4). What one may not claim is a canonical free rank-two direct summand of ambient cohomology.

### 11.4 Reduction and determinant

Let $\mathcal W$ be a stable rank-two lattice. Reduction gives

$$
\bar\rho:G_E\to\operatorname{GL}_2(k_\lambda). \tag{11.6}
$$

Its isomorphism class can depend on $\mathcal W$, though its semisimplification is independent of the stable lattice. To see the latter, two lattices are commensurable; a finite filtration of their quotient by powers of the uniformizer shows that the multisets of residual Jordan--Holder factors agree.

If the alternating pairing is perfect on $\mathcal W$, reducing (6.10) gives

$$
\det\bar\rho
=\bar\chi_\ell^{-1}\bar\eta_\Pi. \tag{11.7}
$$

If the pairing is only integral up to a nonunit scalar, its reduction can become degenerate. The rational determinant formula remains true, but (11.7) then requires choosing a self-dual or suitably rescaled lattice. Rational nondegeneracy alone is not an integral polarization theorem.

## 12. Purity and local boundaries

The extraction theorem is strongest at good places away from the coefficient prime. Purity controls the size of Frobenius roots there. Semistable and coefficient-prime behavior require separate geometric theories and should not be inferred from the good polynomial.

### 12.1 Purity at good places

Let $u\nmid\ell$ be a good place. Smooth proper base change identifies curve $H^1$ with the $H^1$ of a smooth projective special fiber. Its geometric Frobenius eigenvalues are pure of weight one. A Galois-stable Hecke direct summand and its multiplicity factor inherit the same roots, so every complex embedding satisfies

$$
|\iota(\alpha_u)|=q_u^{1/2}. \tag{12.1}
$$

Equation (8.6) then implies

$$
|\iota(t_v(\Pi))|\le 2q_u^{1/2},
\qquad
|\iota(s_v(\Pi))|=1 \tag{12.2}
$$

when $q_u=q_v$ and the central character has finite image. The first inequality is the triangle inequality applied to the two roots; the second follows from their product and purity.

For surface $H^2$, the corresponding roots have absolute value $q_u$. This weight-two purity passes to the four-dimensional packet block. It passes to a rank-two cancellation factor only after the removed factor and its weights have been identified. One cannot take square roots of the surface roots to manufacture (12.1).

### 12.2 What follows for rank two

For the extracted curve representation, combine purity and the determinant:

$$
\alpha_u\beta_u=q_us_v(\Pi),
\qquad
|\alpha_u|=|\beta_u|=q_u^{1/2}. \tag{12.3}
$$

The reciprocal-duality relation is

$$
\{\alpha_u,\beta_u\}
=\{q_us_v(\Pi)/\alpha_u,
q_us_v(\Pi)/\beta_u\}. \tag{12.4}
$$

In dimension two this merely interchanges the two roots, but it is a useful normalization check.

Purity does not prove that the raw representation is semisimple, and it does not determine inertia at a bad place. A nonsplit extension of two pure characters can have the same good characteristic polynomials as their direct sum.

### 12.3 Semistable places

If the Shimura curve has a verified strict semistable model at a place $u\nmid\ell$, Book 20 supplies

$$
N:H^1\longrightarrow H^1(-1),
\qquad N^2=0, \tag{12.5}
$$

with inertia action $1+t_\ell(\sigma)N$. Every prime-to-$u$ Hecke correspondence extending to the model commutes with $N$. Hence $N$ restricts to the packet block and, through multiplicity extraction, to $W_{\Pi,\lambda}$.

The rank of $N$ is governed by the packet part of the dual graph, not merely by the number of nodes. Unramifiedness is equivalent to vanishing of this restricted $N$ together with trivial finite inertia. A compact-type singular fiber can have $N=0$ despite bad reduction.

For a surface, semistable middle cohomology has

$$
N^3=0. \tag{12.6}
$$

Only after a genuine rank-two cancellation factor is extracted does dimensional reasoning force $N^2=0$ on that factor. The conductor alone does not determine $N^2$ on the original four-dimensional block.

### 12.4 The coefficient prime and other boundaries

When $u\mid\ell$, smooth proper etale cohomology still gives a continuous representation, but the prime-to-residue-characteristic argument used for unramified Frobenius and tame monodromy no longer applies. Crystalline, de Rham, finite-flat, or Fontaine--Laffaille properties require additional comparison theorems and integral hypotheses. They are not consequences of (8.6).

At a bad level prime, the operator is usually $U_v$, not the spherical $T_v$. Its adjoint, degree, and local polynomial depend on the integral correspondence. Substituting $U_v$ into (8.6) without a special-fiber calculation is invalid.

The present book also does not prove independence of the integral lattice from $\ell$, bad-prime local--global compatibility, or existence of finite-flat quotients. It supplies the rank-two rational representation, its determinant, parity, semisimplification, coefficient field, and good-prime polynomial on the exact geometric range where those conclusions follow.

## 13. Diagnostic examples and failure modes

The extraction formalism is easiest to trust after testing the four situations which most often lead to a wrong dimension or a wrong Frobenius polynomial.

### 13.1 A minimal curve packet

Assume $P_\Pi$ is one-dimensional and the packet is separated by a commutative Hecke character. Then

$$
e_\Pi H^1_\ell(C_K)=W_{\Pi,\lambda}
$$

is two-dimensional. Its Hodge types are $(1,0)$ and $(0,1)$, and every complex conjugation has eigenvalues $1,-1$. At a good place,

$$
\det(X-\Phi_u)=X^2-t_vX+q_vs_v.
$$

If $s_v=1$, the determinant character is $\chi_\ell^{-1}$. No choice of a normalized holomorphic differential selects a Galois-stable line: the holomorphic line exists only in the complex Hodge realization.

### 13.2 A three-dimensional oldspace

Suppose $\dim P_\Pi=3$. Then the packet part of cohomology has dimension six:

$$
e_\Pi H^1=P_\Pi\otimes W_\Pi,
\qquad \dim W_\Pi=2. \tag{13.1}
$$

Galois acts as $1\otimes\rho_\Pi$. Choosing one oldvector gives a two-dimensional subspace only after a noncanonical choice and need not be preserved by the full level Hecke algebra. The Hom space (3.5) recovers $W_\Pi$ without choosing an oldvector.

If one uses only the good spherical character, all three oldvectors can appear as a scalar Hecke multiplicity. The full finite Hecke image is needed to justify (13.1).

### 13.3 A scalar Frobenius

Let $F=cI$ on a two-dimensional space. Suppose

$$
F^2-aF+bI=0.
$$

This says only $c^2-ac+b=0$. For example, $X^2-3X+2$ annihilates $I$, but the characteristic polynomial of $I$ is $(X-1)^2$. Dimension plus annihilation is insufficient.

If one also knows $\det F=b$, then $c^2=b$. Subtracting gives $c(2c-a)=0$, and invertibility gives $a=2c$. The annihilator becomes $(X-c)^2$, exactly the characteristic polynomial. This is the scalar case of Lemma 8.1 and explains why the determinant theorem is logically prior to (8.6).

### 13.4 A four-dimensional surface packet

Let $V$ be a full minimal surface packet with Hodge numbers $(1,2,1)$. Its good Frobenius roots all have absolute value $q$. A quadratic polynomial with roots of absolute value $q^{1/2}$ cannot be its characteristic polynomial.

If a split cancellation algebra $M_2(L)$ acts with

$$
V\simeq R\otimes W,
\qquad \dim R=\dim W=2, \tag{13.2}
$$

then $W=\operatorname{Hom}_{M_2(L)}(R,V)$, with the descent action of (9.5), is a genuine two-dimensional Galois representation. If no such algebra acts through descended correspondences, the four Hodge lines do not provide a substitute. The difference between the two cases is algebraic descent, not clever linear algebra after complexification.

## 14. The extraction theorem

We now collect the constructions into one theorem. Its curve part is unconditional under the hypotheses already established for the compact Shimura curve. Its surface part states separately the unconditional degree-two block and the additional cancellation hypothesis needed for rank two.

### 14.1 Complete statement

**Theorem 14.1 (rank-two extraction from weight-two Shimura cohomology).** Let $E$ be the reflex field of one of the compact Shimura data below, let $\ell$ be a prime, and let $\Pi$ be a noncharacter parallel-weight-two packet with coefficient field $L_\Pi$.

**Curve case.** Assume $C_K/E$ is a smooth projective, Galois-stable and Hecke-stable component union for a quaternion division algebra split at exactly one real place. Assume the level is fine, or work rationally through a fine normal cover. Let $A$ be the full finite adjoint-stable Hecke image on $H^1$, and let $e_\Pi$ be the rational packet block. Then, after a finite field $L/L_\Pi$ splitting the simple factor of $A$ and for every $\lambda\mid\ell$:

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

4. if $E$ is totally real, the representation is odd at every real place;

5. at every place $u\nmid\ell$ satisfying the full good integral-model, hyperspecial, self-dual, component-stability, and unramified hypotheses, it is unramified and

   $$
   \det(X-\rho_{\Pi,\lambda}(\Phi_u))
   =X^2-t_v(\Pi)X+q_vs_v(\Pi);
   $$

6. the roots in part 5 are pure of weight one;

7. the intersection of the rational packet block with integral $H^1$ is a saturated Galois- and Hecke-stable lattice. It is not asserted to be a direct summand, nor is its rank-two Morita factor asserted canonical, unless the deck, projector, order, and evaluation denominators are $\ell$-adic units.

**Surface case.** Assume $S_C/E$ is the compact smooth projective unitary surface with two active real factors and the packet lies in the established automorphic range. Then the projector gives an unconditional continuous packet representation $V_{\Pi,\lambda}\subset H^2_\ell(S_C)$, pure of weight two at good places, with its coefficient-independent good Frobenius polynomial and pairing twist $(-2)$. It is generally four-dimensional at full minimal orientation level.

If, in addition, a surface cancellation datum satisfying Section 9.2 and the pairing condition of Section 9.3 is supplied, then

$$
W^{\mathrm{surf}}_{\Pi,\lambda}
=\operatorname{Hom}_{B_\Pi}(R_\Pi,V_{\Pi,\lambda})
$$

is two-dimensional. Its semisimplification has the determinant and good-prime polynomial of parts 3 and 5. If it descends to a totally real field with the curve-normalized Hodge types, it is odd. Without the cancellation datum, no rank-two surface constituent is asserted.

When a curve extraction and a cancellable surface extraction are defined over the same field and their good Frobenius classes form a dense set, their semisimplifications are isomorphic.

### 14.2 Proof

The finite Hecke image is semisimple because transpose makes its complex image adjoint stable. Its central idempotent cuts out a Galois-stable packet block by descent of the Hecke correspondences. A finite coefficient extension splits the simple block. The automorphic decomposition of curve $H^1$ gives multiplicity two, and Theorem 3.1 converts that multiplicity into the two-dimensional Hom space. Section 4.1 proves continuity. Section 4.3 constructs its continuous semisimplification and proves that trace and determinant are unchanged. This proves parts 1 and 2.

Poincare duality pairs the packet with its adjoint. Factoring the pairing through the simple finite Hecke module and using the component-character identification gives the alternating pairing (6.10). The rank-two similitude identity (6.5) proves the determinant formula, hence part 3. The two Hodge lines are exchanged by every complex conjugation, so its eigenvalues are $1$ and $-1$. Comparison and invariance under semisimplification prove part 4.

At a good place, smooth proper base change gives unramifiedness and transfers the special-fiber correspondence identity to geometric generic cohomology. Restriction to the Hom space gives the quadratic annihilator (8.2). The determinant formula gives (6.12), and Lemma 8.1 upgrades the annihilator to the characteristic polynomial even when Frobenius is scalar. This proves part 5. Purity of smooth projective curve $H^1$ passes to the packet block and its multiplicity factor, proving part 6.

Integral cohomology is finite free and stable under Galois and integral correspondences. Intersection with a rational direct summand is saturated. Sections 11.2--11.3 exhibit the independent denominators obstructing direct-summand and integral Morita statements, proving part 7.

For the surface, the automorphic decomposition and projector construction give the unconditional block, while smooth proper base change, the projected Lefschetz formula, and surface purity give its good local assertions. If a cancellation datum is present, Theorem 3.1 applied to the underlying algebra proves the rank-two factorization, while formula (9.5) proves Galois stability and continuity under the descent action. Factoring the surface pairing through the cancellation module gives the determinant target required by Chapter 6, and the good-prime relation in the datum lets the argument of Chapter 8 repeat. The warning of Section 9.4 proves the negative clause. Finally, the comparison criterion of Section 10.3 proves carrier independence under the stated density hypothesis. $\square$

### 14.3 Dependency and hypothesis ledger

| Conclusion | Established input | Hypothesis retained | Failure if omitted |
|---|---|---|---|
| continuous Galois action on cohomology | finite etale descent and continuous etale cohomology from Books 19 and 20 | smooth proper variety, finite-dimensional adic cohomology | the acting group or coefficient topology can be wrong |
| commuting Hecke and Galois actions | pull--trace correspondence formalism from Book 20 and descended correspondences in Books 132 and 133 | both legs and the selected component union defined over $E$ | invariant eigenvalues do not imply an equivariant operator |
| common rational structures | Betti--etale comparison from Book 27 | smooth proper curve for the integral statement; chosen complex embedding | dimensions alone do not identify lattices or correspondences |
| rank-two curve factor | automorphic decomposition and double-centralizer block of Book 132 | full finite Hecke image and a splitting field | an old packet has total dimension $2\dim P_\Pi$ |
| continuous semisimple representation | closed-subspace continuity and Jordan--Holder semisimplification in Chapter 4 | finite-dimensional characteristic-zero coefficients | raw extension classes need not split |
| determinant | Poincare pairing of Book 132, component descent, and the rank-two identity of Book 123 | adjoint packet and central-component character correctly identified | an annihilating polynomial has an undetermined scalar case |
| oddness | weight-one Hodge types and comparison from Books 27 and 132 | base field has real places | parity has no meaning over a totally imaginary field |
| quadratic characteristic polynomial | good correspondence relation of Book 132 plus the determinant theorem | every good-model condition and $u\nmid\ell$ | the relation may fail, or remain only an annihilator |
| coefficient field | rational Hecke blocks of Books 132 and 133 | finite extension splitting the simple algebra | the Hecke field can retain a Schur division algebra |
| integral packet lattice | finite-free curve cohomology from Book 20 | use intersection and saturation | rational projectors can have nonunit denominators |
| surface packet representation | unitary-surface decomposition, projected traces, and purity of Book 133 | compact PEL-exact surface and good model where invoked | boundary terms, wrong weights, or ramification can enter |
| rank-two surface factor | corestriction and split-module linear algebra of Book 123 plus Section 9.2 | descended split cancellation algebra and compatible pairing | the honest surface block remains four-dimensional |
| semistable monodromy restriction | curve monodromy of Book 20 and surface packet monodromy of Book 133 | verified semistable model and extending prime-to-bad correspondences | a good-prime polynomial determines neither inertia nor $N$ |

The dependency boundary is exact. Book 19 supplies continuous monodromy and the arithmetic-versus-geometric Frobenius convention. Book 20 supplies curve cohomology, its Galois action, integral lattice, Poincare duality, pullback, trace, correspondences, good reduction, and semistable monodromy with $N^2=0$. Book 27 supplies the common Betti, de Rham, and etale rational structures, compatibility with correspondences, Hodge lines, and the integral comparison for smooth proper curves. Book 123 supplies the rank-two similitude identity, corestriction obstruction, split-module criterion, tensor parity, and integral perfectness warnings. Book 132 supplies the compact curve packet decomposition, the full Hecke block, exact multiplicity two, component descent, the good-prime operator relation, and the natural saturated lattice. Book 133 supplies the honest surface packet, its weight-two purity, projected Frobenius traces, semistable monodromy, and the warning that no Hodge half is automatically Galois stable.

No later attachment, local--global compatibility, compatible-system, or finite-flat theorem is used. Whenever carrier comparison uses density of Frobenius classes, that density is displayed as an additional hypothesis rather than silently imported.

### 14.4 Conclusion

The passage from Shimura cohomology to a rank-two Galois representation is now an auditable sequence of algebraic operations. A Hecke projector isolates a rational packet, but it does not remove oldvectors. The simple finite Hecke module accounts for those vectors; its multiplicity space accounts for arithmetic. On a compact Shimura curve that multiplicity is exactly two, so the Hom construction produces the desired continuous representation at every coefficient place, independently of a choice of eigenvector.

The representation is taken semisimply in a precise sense which preserves every trace and determinant while making no unsupported claim about extension classes in raw cohomology. Its coefficient field is the Hecke field only after the possible Schur obstruction has been split. Poincare duality, the adjoint packet, and component reciprocity give the alternating target

$$
L_\lambda(-1)\otimes\eta_\Pi,
$$

so the two-dimensional similitude identity determines

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi.
$$

This determinant is the missing input in the good-prime calculation. The geometric correspondence first gives only a quadratic annihilator. Combining it with the independently known determinant proves, including in the scalar case,

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_u))
=X^2-t_v(\Pi)X+q_vs_v(\Pi).
$$

The Hodge lines prove oddness over a totally real field, and smooth projective purity gives weight one. Saturation supplies an integral stable lattice, while projector, coarse-level, and Morita denominators explain why an integral direct summand is a stronger theorem.

The auxiliary surface has also been placed on its correct side of the boundary. Its full packet is a genuine weight-two degree-two representation, normally four-dimensional. A descended split cancellation algebra can remove one complete auxiliary factor and expose a rank-two multiplicity space. Without that algebra, selecting two Hodge lines or taking a half twist is invalid. Thus both $H^1$ and $H^2$ contribute exactly what their geometry proves: the curve gives rank two directly through multiplicity, the surface gives rank two only through algebraic cancellation, and neither source is asked to support a conclusion that its pairings, weights, or integral structures do not justify.
