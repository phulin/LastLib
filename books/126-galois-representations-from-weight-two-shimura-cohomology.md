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
  - [6.3 The returned old-level pairing](#63-the-returned-old-level-pairing)
  - [6.4 The determinant theorem](#64-the-determinant-theorem)
- [7. Parity at real places](#7-parity-at-real-places)
  - [7.1 Evenness of the component character](#71-evenness-of-the-component-character)
  - [7.2 Oddness of the extracted representation](#72-oddness-of-the-extracted-representation)
  - [7.3 The Hodge-theoretic check](#73-the-hodge-theoretic-check)
  - [7.4 Reducible, scalar, and non-real cases](#74-reducible-scalar-and-non-real-cases)
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
- [10. Diagnostic examples and failure modes](#10-diagnostic-examples-and-failure-modes)
  - [10.1 A minimal curve packet](#101-a-minimal-curve-packet)
  - [10.2 A three-dimensional oldspace](#102-a-three-dimensional-oldspace)
  - [10.3 A scalar Frobenius](#103-a-scalar-frobenius)
- [11. The extraction theorem](#11-the-extraction-theorem)
  - [11.1 Complete statement](#111-complete-statement)
  - [11.2 Proof](#112-proof)
  - [11.3 Dependency and hypothesis ledger](#113-dependency-and-hypothesis-ledger)
  - [11.4 Scope boundary](#114-scope-boundary)
  - [11.5 Conclusion](#115-conclusion)

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

At a split hyperspecial place $v$ of the totally real field underlying the packet, the unnormalized Hecke operators are $T_v$ and $S_v$, and the raw polynomial is

$$
Q_v(X)=X^2-T_vX+q_vS_v. \tag{1.3}
$$

No square root of $q_v$ is inserted. The distinction between the operator identity $Q_v(\Phi_v)=0$ and the equality of $Q_v$ with a characteristic polynomial is one of the main points of Chapter 8.

For a representation $V$, the notation $V^{\mathrm{ss}}$ means the direct sum of its Jordan--Holder factors. It is a representation, not merely a list of traces. Its isomorphism class is independent of the chosen composition series.

### 1.3 The curve source

The geometric source is the compact quaternionic Shimura curve $C_K/E$ of Book 125. Its constant-coefficient $H^1$ has a finite semisimple rational Hecke image. The chosen component union is either the full orbit under the component-routing algebra, or the packet is first separated by a component-character idempotent. Stability under a smaller spherical algebra does not by itself isolate an individual packet. For a parallel-weight-two packet $\Pi$, a splitting field $L$ gives

$$
e_\Pi H^1_\ell(C_K)\otimes L_\lambda
\simeq P_{\Pi,\lambda}\otimes_{L_\lambda}W_{\Pi,\lambda},
\qquad \dim W_{\Pi,\lambda}=2. \tag{1.4}
$$

The curve is proper, so there is no boundary or Eisenstein contribution. The two dimensions in $W_{\Pi,\lambda}$ come from Hodge types $(1,0)$ and $(0,1)$, not from two automorphic occurrences. This book studies this reusable curve extraction.

### 1.4 The logical order

The safe construction has seven stages.

1. Replace the abstract Hecke algebra by its finite image on the chosen cohomology group.
2. Cut out a rational block by a central idempotent, then extend coefficients only far enough to split its simple algebra.
3. Remove the simple finite Hecke module by a Hom construction.
4. Prove continuity and pass, when unconditional semisimplicity is desired, to the canonical semisimplification.
5. Apply Book 125's returned old-level pairing and identify its one-dimensional similitude target.
6. Use the resulting determinant to turn the good-prime quadratic annihilator into the characteristic polynomial, including scalar Frobenius.
7. Intersect the rational constituent with the natural integral lattice, without claiming an integral Hecke projector or a canonical stable complement unless all relevant denominators are units.

Every later conclusion depends on this order. In particular, the determinant does not follow from adjoint duality alone, and a rational idempotent cannot be applied to an integral lattice before its denominators have been audited. The needed self-pairing is already assertion 5 of Book 125's main theorem, not a further hypothesis of this book.

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

Let $A$ be a finite-dimensional semisimple algebra over a field $k$. Fix a simple factor $A_0=eA$, and write $Z=Z(A_0)$. The algebra $A_0$ is central simple over $Z$, not necessarily over $k$. Choose a finite extension $L/k$ and a $k$-embedding $\iota:Z\hookrightarrow L$ which splits it, so that

$$
A_{0,\iota}:=A_0\otimes_{Z,\iota}L\simeq M_d(L). \tag{3.1}
$$

The embedding $\iota$ selects one factor of $A_0\otimes_kL$; without that selection the scalar extension can be a product of conjugate matrix algebras. For an $A_0$-module $H_0$, put $H_{0,\iota}=H_0\otimes_{Z,\iota}L$. Let $P=L^d$ be the standard simple left $A_{0,\iota}$-module. Every finite-dimensional left $M_d(L)$-module is a direct sum of copies of $P$, so the multiplicity space

$$
W=\operatorname{Hom}_{A_{0,\iota}}(P,H_{0,\iota}) \tag{3.2}
$$

has dimension equal to the number of copies of $P$ in $H_{0,\iota}$.

There is an evaluation map

$$
\operatorname{ev}:P\otimes_LW\longrightarrow H_{0,\iota},
\qquad p\otimes f\longmapsto f(p). \tag{3.3}
$$

The matrix algebra acts on the first factor and the commutant acts on the second.

### 3.2 The evaluation theorem

**Theorem 3.1 (multiplicity extraction).** In the setting of Section 3.1, the evaluation map (3.3) is an isomorphism. If a group $\Gamma$ acts on $H_{0,\iota}$ and commutes with $M_d(L)$, then

$$
(\gamma f)(p)=\gamma(f(p)) \tag{3.4}
$$

defines an action of $\Gamma$ on $W$, and (3.3) is $\Gamma$-equivariant when $\Gamma$ acts trivially on $P$.

**Proof.** Let $E_{ij}$ be the standard matrix units and $e_1=E_{11}$. The subspace $e_1H_{0,\iota}$ determines the whole module: the map

$$
P\otimes_L e_1H_{0,\iota}\longrightarrow H_{0,\iota},
\qquad e_i\otimes h\longmapsto E_{i1}h
$$

is inverse to

$$
h\longmapsto\sum_i e_i\otimes E_{1i}h.
$$

The identities $E_{ij}E_{rs}=\delta_{jr}E_{is}$ verify both composites. An $M_d(L)$-map $P\to H_{0,\iota}$ is determined by the image of $e_1$, and that image may be any element of $e_1H_{0,\iota}$. Hence $W\simeq e_1H_{0,\iota}$, under which (3.3) is the displayed isomorphism.

If $\Gamma$ commutes with every matrix, then (3.4) remains $M_d(L)$-linear. The group law and equivariance follow directly. $\square$

The theorem also proves independence of matrix coordinates after $\iota$ has been fixed. Replacing (3.1) by another splitting conjugates the matrix algebra, and carries its standard module to an isomorphic simple module. The resulting $W$ is unchanged up to isomorphism. Changing $\iota$ can instead select a conjugate coefficient block; that variance is recorded in Chapter 5.

### 3.3 The rank-two curve constituent

For the Shimura curve of Book 125, let $A_{K,\mathbf Q}$ be the finite rational Hecke image on $H^1_B(C_K,\mathbf Q)$, and let $e_{[\Pi]}$ be the central idempotent of the rational conjugacy-orbit block. Let $Z_\Pi$ be the center of its simple algebra. Choose an embedding $\iota:Z_\Pi\hookrightarrow L$ into a splitting field, and let $e_{\Pi,\iota}$ denote the selected split factor. Write

$$
A_{\Pi,\iota}=e_{\Pi,\iota}(A_{K,\mathbf Q}\otimes_{\mathbf Q}L),
\qquad
A_{\Pi,\iota,\lambda}=A_{\Pi,\iota}\otimes_LL_\lambda.
$$

If $P_{\Pi,\iota}$ is its simple module, define

$$
W_{\Pi,\lambda}
=\operatorname{Hom}_{A_{\Pi,\iota,\lambda}}
\left(P_{\Pi,\iota,\lambda},
e_{\Pi,\iota}\bigl(e_{[\Pi]}H^1_\ell(C_K)\otimes_{\mathbf Q_\ell}L_\lambda\bigr)\right). \tag{3.5}
$$

The automorphic decomposition gives

$$
\dim_{L_\lambda}W_{\Pi,\lambda}=2. \tag{3.6}
$$

The evaluation theorem gives

$$
P_{\Pi,\iota,\lambda}\otimes W_{\Pi,\lambda}
\xrightarrow{\sim}
e_{\Pi,\iota}\bigl(e_{[\Pi]}H^1_\ell(C_K)\otimes L_\lambda\bigr). \tag{3.7}
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

The present book proves a coefficient-field statement at each $\lambda$. In the polarized curve range of Section 6.3, the good characteristic polynomials have coefficients in the packet field. The book does not identify the underlying topological vector spaces for different primes $\ell$. Compatibility means that the available polynomials arise from the same algebraic data, not that there is a linear map between an $\ell$-adic and an $\ell'$-adic space.

## 6. Duality and the determinant line

The quadratic Hecke relation becomes a characteristic polynomial in the scalar case only after the determinant is known independently. Adjoint Poincare duality is not enough: it pairs two packet blocks rather than a packet with itself. Book 125 closes precisely this gap for the basic quaternionic group, and for a connected central modification satisfying its explicit essential-self-duality hypothesis. Its construction works on the complete oldspace and returns from fine level to the original level. This chapter extracts the determinant from that accepted polarized curve package.

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

### 6.3 The returned old-level pairing

Let $T=G^{\mathrm{ab}}$ be the actual abelian quotient and $\nu:G\to T$. For the basic quaternionic group, Book 125 proves a canonical finite-order character $\kappa_\Pi$, trivial at infinity, for which

$$
\Pi^\dagger\simeq
\Pi\otimes(\kappa_\Pi^{-1}\circ\nu). \tag{6.7}
$$

For a connected central modification, equation (6.7) is a retained packet hypothesis on a character of its actual abelian quotient; common adjoint data do not manufacture it, and reduced norm must not be substituted for $\nu$.

Canonical component reciprocity turns $\kappa_\Pi$ into a finite Galois character

$$
\eta_\Pi:G_E\longrightarrow L^\times. \tag{6.8}
$$

At a good unramified place $u$ above $v$, the central-generator normalization is

$$
\eta_\Pi(\operatorname{Frob}^{\mathrm{arith}}_u)
=s_v(\Pi)^{-1},
\qquad
\eta_\Pi(\Phi_u)=s_v(\Pi). \tag{6.9}
$$

The first equality uses arithmetic Frobenius, while the second uses its inverse. For a central modification, Book 125 requires this equality to be checked in the actual abelian quotient with the chosen central generator. It is not a consequence of the basic group's local formula.

The old-level construction is worth recording because it prevents a hidden newvector assumption. Choose a normal fine subgroup

$$
K^\circ\subset K\cap\ker(\kappa_\Pi\circ\nu).
$$

Enlarge $L$ once so that it contains the values of $\kappa_\Pi$, splits the packet algebras at levels $K$ and $K^\circ$, and contains the coefficients of the return operator below. On the finite set of components at level $K^\circ$, multiplication by $\kappa_\Pi^{-1}$ defines a self-transpose component operator $M_{\kappa^{-1}}$. It carries the $\Pi$ block to its adjoint and has the exact covariance

$$
\sigma M_{\kappa^{-1}}
=\eta_\Pi(\sigma)^{-1}M_{\kappa^{-1}}\sigma. \tag{6.10}
$$

If $\Omega$ is the alternating Poincare pairing, then

$$
\Psi^\circ(x,y)=\Omega(x,M_{\kappa^{-1}}y)
$$

is alternating. Book 125's compact mass calculation factors it on the entire packet block as

$$
\Psi^\circ=b_{P,\Pi}^\circ\otimes\psi_\Pi, \tag{6.11}
$$

where $b_{P,\Pi}^\circ$ is symmetric and perfect on the full finite Hecke module and $\psi_\Pi$ is alternating and perfect on the rank-two multiplicity space. The symmetry is a proved property of the component-weighted mass pairing, not an inference from the dimension of the oldspace.

The construction then returns to the original level. If $q:C_{K^\circ}\to C_K$ is the level map, the full split matrix Hecke image supplies an invertible $U$ such that $S=Uq^*$ embeds the finite $K$-module as a nondegenerate subspace. The coefficient-valued return correspondence

$$
R_{\Pi,K}=S^tM_{\kappa^{-1}}S \tag{6.12}
$$

is self-transpose and satisfies the same covariance as (6.10). Pull--trace adjunction gives a perfect symmetric form on the complete finite module at level $K$ and leaves the same rank-two alternating factor. Consequently there is a Galois-equivariant perfect pairing

$$
\psi_\Pi:W_\Pi\times W_\Pi
\longrightarrow L_\lambda(-1)\otimes\eta_\Pi. \tag{6.13}
$$

Indeed, Poincare equivariance gives $\Omega(\sigma x,\sigma z)=\chi_\ell(\sigma)^{-1}\Omega(x,z)$, while the covariance of $R_{\Pi,K}$ is equivalent to $R_{\Pi,K}\sigma=\eta_\Pi(\sigma)\sigma R_{\Pi,K}$. Therefore

$$
\Omega(\sigma x,R_{\Pi,K}\sigma y)
=\chi_\ell(\sigma)^{-1}\eta_\Pi(\sigma)
\Omega(x,R_{\Pi,K}y),
$$

which verifies the multiplier and its sign. Here $\eta_\Pi$ also denotes its one-dimensional $L_\lambda$-space. The return choices can change the finite form, but alternating forms on the two-dimensional $W_\Pi$ differ by a scalar. Hence the multiplier and determinant are independent of those choices. This is the accepted curve input from Book 125, so there is no extra determinant assumption in the range just stated.

### 6.4 The determinant theorem

Let $\chi_\ell:G_E\to\mathbf Z_\ell^\times$ be the cyclotomic character in the convention

$$
\chi_\ell(\operatorname{Frob}^{\mathrm{arith}}_u)=q_u.
$$

The target of (6.13) has character $\chi_\ell^{-1}\eta_\Pi$. Applying (6.6) proves

$$
\boxed{
\det\rho_{\Pi,\lambda}
=\chi_\ell^{-1}\eta_\Pi.}
\tag{6.14}
$$

Semisimplification does not change the determinant, so (6.14) holds for both the raw multiplicity representation and the extracted semisimple representation.

At a good place, evaluate on geometric Frobenius. Since $\chi_\ell(\Phi_u)=q_u^{-1}$ and (6.9) holds,

$$
\boxed{
\det(\Phi_u\mid\rho_{\Pi,\lambda})
=q_us_v(\Pi).}
\tag{6.15}
$$

For arithmetic Frobenius, inversion gives

$$
\det(\operatorname{Frob}^{\mathrm{arith}}_u)
=(q_us_v(\Pi))^{-1}. \tag{6.16}
$$

The two formulas concern inverse operators. Neither is a different determinant convention.

## 7. Parity at real places

For a two-dimensional representation of the Galois group of a totally real field, oddness means that every complex conjugation has determinant $-1$. In the accepted polarized curve range, oddness follows from the determinant and the archimedean normalization of the component character. This route remains valid even when real descent exchanges conjugate coefficient blocks. Hodge theory gives a useful independent check only when one individual split block is preserved.

### 7.1 Evenness of the component character

The character $\kappa_\Pi$ in Section 6.3 is trivial at every infinite place. For the basic group this is proved from the weight-two archimedean type; for a connected central modification it is part of the explicit packet hypothesis. Book 125's component reciprocity calculation therefore gives

$$
\eta_\Pi(c_\tau)=1 \tag{7.1}
$$

for every real place $\tau$ of $E$. Thus the finite component correction is even. This is a normalization statement from the automorphic input, not an inference from finite image alone: a finite-order Galois character can be odd.

### 7.2 Oddness of the extracted representation

**Theorem 7.1 (parity).** In the polarized packet range of Section 6.3, the extracted representation is odd at every real place of $E$.

**Proof.** The cyclotomic character satisfies $\chi_\ell(c_\tau)=-1$. Equations (6.14) and (7.1) give

$$
\det\rho_{\Pi,\lambda}(c_\tau)
=\chi_\ell(c_\tau)^{-1}\eta_\Pi(c_\tau)
=-1. \tag{7.2}
$$

Semisimplification preserves the determinant, so the same formula holds for the raw multiplicity representation and for $\rho_{\Pi,\lambda}$. $\square$

No stability of an individual coefficient embedding under real descent is needed for this proof. The determinant character already descends on the selected split realization.

### 7.3 The Hodge-theoretic check

Suppose now that the individual coefficient block and embedding $\iota$ are preserved by the real descent action. Betti comparison gives

$$
W_{\Pi,B}\otimes_{L,\iota}\mathbf C
=W^{1,0}\oplus W^{0,1},
\qquad \dim W^{1,0}=\dim W^{0,1}=1. \tag{7.3}
$$

The coefficient-linear real involution interchanges the two Hodge lines. It cannot be scalar, and its square is one, so its eigenvalues are $1$ and $-1$. Hence

$$
\operatorname{Tr}(c_\tau)=0,
\qquad
\det(c_\tau)=-1. \tag{7.4}
$$

Comparison transports the polynomial $X^2-1$ to the $\lambda$-adic realization. If real descent instead sends $\iota$ or $\Pi$ to a conjugate block, this argument applies to the rational orbit containing both blocks but does not by itself define an involution on one chosen $W_{\Pi,\lambda}$. The determinant proof of Section 7.2 avoids that variance issue.

### 7.4 Reducible, scalar, and non-real cases

Oddness does not imply irreducibility. If

$$
\rho^{\mathrm{ss}}=\chi_1\oplus\chi_2,
$$

then (7.2) says that exactly one of $\chi_1(c_\tau)$ and $\chi_2(c_\tau)$ is $-1$. A nonsplit extension of these characters is also odd because determinant ignores the extension class.

Nor does oddness rule out scalar Frobenius at a finite place. A complex conjugation and a good Frobenius are unrelated elements; the former has eigenvalues $1,-1$, while the latter can act as a scalar. This is why the scalar case in Chapter 8 must be handled by determinant rather than excluded by parity.

If the base field has no real place, there is no complex conjugation in its absolute Galois group and the adjectives odd and even do not apply. If a rank-two representation over a totally real subfield is later restricted to a CM extension, it remembers that it came from an odd representation, but oddness is a property of the representation before restriction. It cannot be reconstructed merely from the restricted determinant.

## 8. Good-prime Frobenius polynomials

At a good place, geometry provides an operator relation. The polarized curve package of Section 6.3 supplies the independent determinant, so linear algebra identifies the characteristic polynomial without assuming that Frobenius is nonscalar.

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

Apply the lemma with $F=\Phi_u$, $a=t_v(\Pi)$, and $b=q_vs_v(\Pi)$. Equation (6.15) supplies the determinant. Therefore

$$
\boxed{
\det(X-\rho_{\Pi,\lambda}(\Phi_u))
=X^2-t_v(\Pi)X+q_vs_v(\Pi).}
\tag{8.6}
$$

This proof includes scalar Frobenius. If $\Phi_u=cI$, equations (8.2) and (6.15) force $2c=t_v$ and $c^2=q_vs_v$, so (8.3) is automatically $(X-c)^2$.

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

The lattice (9.2) is Galois and Hecke stable and spans the desired rational block. Because it is saturated in a finite free module over a discrete valuation ring, its quotient is finite free; hence it is an abstract $\mathcal O_{L_\lambda}$-module direct summand. Such a complement is noncanonical and need not be Galois or Hecke stable. If $e$ contains an interpolation denominator divisible by $\ell$, the packet lattice need not be the image of an integral Hecke idempotent, and congruent packet lattices can have the same reduction.

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

Then Morita theory gives evaluation for every left $\mathcal A$-module in its scope. Without this integral progenerator property, rational evaluation can be an isomorphism while the image of (9.4) has finite index in $\Lambda[e]$; that is the integral evaluation defect. Failure can occur at primes dividing the discriminant of the order. Projector and deck denominators are independent earlier obstructions to realizing the packet lattice as the image of an integral Hecke idempotent or to finding a canonical stable packet complement.

Without the unit conditions, one may still choose any stable lattice in the rational $W$, or take the image and saturation of (9.3). What one may not claim is a canonical Galois- and Hecke-stable rank-two complement inside ambient cohomology.

### 9.4 Reduction and determinant

Let $\mathcal W$ be a stable rank-two lattice. Reduction gives

$$
\bar\rho:G_E\to\operatorname{GL}_2(k_\lambda). \tag{9.5}
$$

Its isomorphism class can depend on $\mathcal W$, though its semisimplification is independent of the stable lattice. Here is the lattice argument. After rescaling one of two stable lattices, connect them by a finite chain whose adjacent terms satisfy

$$
\varpi\mathcal W\subset\mathcal W'\subset\mathcal W.
$$

Put $U=\mathcal W'/\varpi\mathcal W$. The reductions of the two adjacent lattices have filtrations with factors

$$
\mathcal W/\varpi\mathcal W:\quad
U,\ \mathcal W/\mathcal W',
$$

and

$$
\mathcal W'/\varpi\mathcal W':\quad
\mathcal W'/\varpi\mathcal W=U,\
\varpi\mathcal W/\varpi\mathcal W'\simeq\mathcal W/\mathcal W'.
$$

All terms are Galois stable. Thus the two reductions have the same Jordan--Holder factors, and iteration along the chain proves the claim.

The rational determinant identity (6.14) implies that every stable lattice gives

$$
\det\bar\rho
=\bar\chi_\ell^{-1}\bar\eta_\Pi. \tag{9.6}
$$

Indeed, the determinant of the integral matrices reduces to the determinant of their residual matrices; no self-dual lattice is needed for this character identity. Perfectness matters for a different assertion. If (6.13) is only integral up to a nonunit scalar, its reduction can become degenerate, so the residual representation need not carry the claimed perfect alternating polarization. Rational nondegeneracy alone is not an integral polarization theorem.

## 10. Diagnostic examples and failure modes

The extraction formalism is easiest to trust after testing the three situations which most often lead to a wrong dimension or a wrong Frobenius polynomial.

### 10.1 A minimal curve packet

Assume $P_\Pi$ is one-dimensional and the packet is separated by a commutative Hecke character. In the polarized curve range of Section 6.3, Book 125 supplies the component multiplier; its finite-module form on this line is symmetric. Then

$$
e_\Pi H^1_\ell(C_K)=W_{\Pi,\lambda}
$$

is two-dimensional. Its Hodge types are $(1,0)$ and $(0,1)$, and every complex conjugation has eigenvalues $1,-1$. At a good place,

$$
\det(X-\Phi_u)=X^2-t_vX+q_vs_v.
$$

If $s_v=1$, the determinant character is $\chi_\ell^{-1}$. No choice of a normalized holomorphic differential selects a Galois-stable line: the holomorphic line exists only in the complex Hodge realization.

### 10.2 A three-dimensional oldspace

Suppose $\dim P_\Pi=3$. Then the packet part of cohomology has dimension six:

$$
e_\Pi H^1=P_\Pi\otimes W_\Pi,
\qquad \dim W_\Pi=2. \tag{10.1}
$$

Galois acts as $1\otimes\rho_\Pi$. Choosing one oldvector gives a two-dimensional subspace only after a noncanonical choice and need not be preserved by the full level Hecke algebra. The Hom space (3.5) recovers $W_\Pi$ without choosing an oldvector.

If one uses only the good spherical character, all three oldvectors can appear as a scalar Hecke multiplicity. The full finite Hecke image is needed to justify (10.1).

### 10.3 A scalar Frobenius

Let $F=cI$ on a two-dimensional space. Suppose

$$
F^2-aF+bI=0.
$$

This says only $c^2-ac+b=0$. For example, $X^2-3X+2$ annihilates $I$, but the characteristic polynomial of $I$ is $(X-1)^2$. Dimension plus annihilation is insufficient.

If one also knows $\det F=b$, then $c^2=b$. Subtracting gives $c(2c-a)=0$, and invertibility gives $a=2c$. The annihilator becomes $(X-c)^2$, exactly the characteristic polynomial. This is the scalar case of Lemma 8.1 and explains why the determinant theorem is logically prior to (8.6).

## 11. The extraction theorem

We now collect the construction into one theorem for the accepted compact Shimura-curve source.

### 11.1 Complete statement

**Theorem 11.1 (rank-two extraction from weight-two Shimura-curve cohomology).** Let $F$ be totally real, let $B/F$ be a quaternion division algebra split at exactly one real place, and let $(G,X)$ be the basic quaternionic Shimura datum or a specified connected central modification with a genuine PEL realization. In the second case, assume the packet satisfies the essential-self-duality hypothesis (6.7) for a finite-order character $\kappa_\Pi$ of the actual abelian quotient, trivial at infinity.

Let $K\subset G(\mathbf A_f)$ be compact open, and let $C_K/E$ be the smooth projective canonical curve over its totally real reflex field, attached to a Galois-stable component union which is a full orbit under the finite Hecke and component-routing algebra. A proper smaller union is allowed only after a component-character idempotent has separated the individual packet. Let $\Pi$ be a noncharacter parallel-weight-two packet, let $A$ be the full finite adjoint-stable Hecke image on $H^1$, and let $e_{[\Pi]}$ be its rational conjugacy-orbit block. At non-neat level, work rationally through the normal fine cover and return maps of Book 125.

Choose a finite field $L$ containing the values of $\kappa_\Pi$, splitting the relevant packet algebras at $K$ and at the fine return level, and containing the coefficients of the return construction. Choose an embedding of the center of the simple packet algebra into $L$, and let $e_{\Pi,\iota}$ and $P_{\Pi,\iota}$ be the resulting split factor and simple module. Then for every $\lambda\mid\ell$:

1. the multiplicity space

   $$
   W_{\Pi,\lambda}
   =\operatorname{Hom}_{A_{\Pi,\iota,\lambda}}
   \left(P_{\Pi,\iota,\lambda},
   e_{\Pi,\iota}\bigl(e_{[\Pi]}H^1_\ell(C_K)\otimes L_\lambda\bigr)\right)
   $$

   is two-dimensional and carries a continuous $G_E$-action;

2. its canonical semisimplification

   $$
   \rho_{\Pi,\lambda}:G_E\to\operatorname{GL}_2(L_\lambda)
   $$

   is continuous and semisimple, and is well defined up to coefficient extension and isomorphism;

3. Book 125's returned old-level pairing induces a perfect alternating pairing

   $$
   W_{\Pi,\lambda}\times W_{\Pi,\lambda}
   \longrightarrow L_\lambda(-1)\otimes\eta_\Pi,
   $$

   and therefore

   $$
   W_{\Pi,\lambda}^\vee
   \simeq W_{\Pi,\lambda}(1)\otimes\eta_\Pi^{-1},
   \qquad
   \det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi;
   $$

4. the representation is odd at every real place of $E$;

5. at a place $u\nmid\ell$ above $v$ satisfying every equal-residue-field, unramified PEL, self-dual polarization, hyperspecial level, smooth determinant-model, rank-one incidence, $\mu$-ordinary-density, component-extension, and fine-or-tame hypothesis in Section 8.1, it is unramified. If the central generator satisfies (6.9), then

   $$
   \det(X-\rho_{\Pi,\lambda}(\Phi_u))
   =X^2-t_v(\Pi)X+q_vs_v(\Pi);
   $$

6. the canonical object before splitting is the rational conjugacy-orbit block together with its Morita module. Changing the split matrix model changes $W_{\Pi,\lambda}$ only up to isomorphism, enlarging $L$ extends scalars, and changing the center embedding selects the corresponding conjugate packet;

7. after extension to $\mathcal O_{L_\lambda}$, intersection with integral $H^1$ gives a saturated Galois- and Hecke-stable packet lattice. It is an abstract module direct summand, but no integral Hecke projector, canonical stable complement, integral rank-two Morita factor, or perfect residual polarization is asserted unless every relevant deck, projector, order, evaluation, return, and pairing denominator is an $\ell$-adic unit.

### 11.2 Proof

Book 125 proves that the full finite rational Hecke image is semisimple: after extension to $\mathbf C$, transpose is the adjoint for a positive Hodge Hermitian form, so the image is adjoint stable and has zero radical. Its rational central idempotent cuts out a Galois-stable conjugacy-orbit block because every generating correspondence descends to $E$. Section 3.1 selects one center embedding before splitting the central simple algebra. Book 125's automorphic decomposition gives multiplicity two, and Theorem 3.1 converts that multiplicity into the two-dimensional Hom space. Sections 4.1 and 4.3 prove continuity and construct the continuous semisimplification. This proves parts 1 and 2.

Poincare duality first gives only the adjoint pairing (6.4). In the stated packet range, Book 125 refines to a level in the kernel of $\kappa_\Pi$, constructs the covariant component multiplier, proves the symmetric perfect mass pairing on the complete oldspace, and returns it to level $K$ by pull--trace. Factoring the returned pairing leaves (6.13). The rank-two identity (6.5) gives (6.14), proving part 3. The component character is even at every real place, so Section 7.2 proves part 4 without assuming that real descent fixes one coefficient embedding.

At a good place, smooth proper base change gives unramifiedness and transports Book 125's special-fiber correspondence relation to geometric generic cohomology. Restriction through evaluation gives (8.2). The local component normalization identifies its constant term with the independent determinant (6.15), and Lemma 8.1 upgrades the annihilator to the characteristic polynomial even for scalar Frobenius. This proves part 5.

Section 3.1 and Chapter 5 distinguish the center embedding from the matrix splitting and prove the scalar-extension assertions in part 6. Integral cohomology is finite free and stable under Galois and integral correspondences. Intersection with the rational packet subspace is saturated; over the coefficient discrete valuation ring, the quotient is finite free and the underlying module sequence splits. Sections 9.2--9.4 retain the independent denominators which obstruct an integral Hecke projector, stable complement, integral Morita evaluation, or perfect residual pairing. This proves part 7. $\square$

### 11.3 Dependency and hypothesis ledger

| Conclusion                                   | Established input                                                                      | Hypothesis retained                                                                       | Failure if omitted                                                                                                   |
| -------------------------------------------- | -------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| continuous Galois action on curve cohomology | finite etale descent and continuous etale $H^1$ from Books 17 and 21                   | smooth proper curve and finite-dimensional adic cohomology                                | the acting group or coefficient topology can be wrong                                                                |
| commuting Hecke and Galois actions           | pull--trace correspondence formalism of Book 21 and descended curve spans of Book 125  | both finite legs and the routed component union descend to $E$                            | invariant eigenvalues do not make an operator equivariant                                                            |
| rational structures and Hodge check          | Betti--de Rham--etale comparison from Book 47 and weight-two Hodge types from Book 125 | smooth proper curve and a chosen complex embedding                                        | dimensions alone do not identify realizations or correspondences                                                     |
| rank-two factor                              | automorphic decomposition and full double-centralizer block of Book 125                | full finite Hecke image, component separation, center embedding, and splitting field      | an old packet has total dimension $2\dim P_\Pi$, while an unsplit block need not be a matrix algebra over its center |
| continuous semisimple representation         | closed-subspace continuity and Jordan--Holder semisimplification in Chapter 4          | finite-dimensional characteristic-zero coefficients                                       | raw extension classes need not split                                                                                 |
| returned alternating pairing and determinant | polarized old-level construction of Book 125 and rank-two identity of Book 115         | basic group, or hypothesis (6.7) on the actual abelian quotient of a central modification | adjoint duality alone gives neither a self-pairing nor a determinant line                                            |
| oddness                                      | evenness of $\eta_\Pi$ from Book 125 and determinant from Section 6.4                  | totally real reflex field and the polarized packet hypothesis                             | finite order alone does not make a character even                                                                    |
| good characteristic polynomial               | good correspondence relation and local normalization of Book 125 plus Lemma 8.1        | complete ledger of Section 8.1, $u\nmid\ell$, and (6.9)                                   | the relation can fail, or a degree-two annihilator can remain ambiguous on a scalar operator                         |
| integral packet lattice                      | finite-free curve cohomology from Book 21 and packet block from Book 125               | coefficient extension, intersection, and saturation                                       | nonunit denominators obstruct an integral projector or stable complement, not abstract module splitting              |

The exact direct dependency row is

$$
\boxed{126\mid 17,\ 21,\ 47,\ 115,\ 125.}
$$

Book 17 supplies finite etale descent, absolute Galois actions, stable-lattice facts, and the arithmetic-versus-geometric Frobenius convention. Book 21 supplies smooth proper curve cohomology, Galois-equivariant pullback and trace, Poincare duality, the finite-free integral lattice, and good-reduction unramifiedness. Book 47 supplies compatible Betti, de Rham, and etale realizations, the two Hodge lines, and correspondence compatibility. Book 115 supplies central-simple-algebra and Schur-obstruction bookkeeping, the rank-two similitude identity, tensor-pairing signs, and integral perfectness warnings. Book 125 supplies the compact Shimura-curve packet decomposition, exact multiplicity two, full finite Hecke block, component routing and descent, polarized fine-level multiplier, symmetric oldspace mass pairing, return to arbitrary level, even component character, and the good-prime relation with its local normalization.

No later attachment, local--global compatibility, compatible-system, purity, or finite-flat theorem is used.

### 11.4 Scope boundary

The first missing input outside the theorem's packet range is exact. For a connected central modification without (6.7), the accepted inputs give the rank-two Hom space and the adjoint pairing (6.4), but not an alternating self-pairing. Consequently this book asserts no determinant, determinant-based oddness, or scalar-Frobenius characteristic polynomial there. Equality of central eigenvalues cannot replace a character on the actual abelian quotient.

Likewise, a component union preserved only by a smaller Hecke algebra can mix component-character families. An individual-$\Pi$ statement then begins only after a separating component-character idempotent is supplied. At a place failing the ledger of Section 8.1, or at $u\mid\ell$, this book gives no spherical Frobenius polynomial. Bad-place Weil--Deligne parameters, coefficient-prime comparison properties, purity, and independence across coefficient primes require inputs not declared here.

These are theorem boundaries, not gaps in the compact basic quaternionic range used by the FLT blueprint.

### 11.5 Conclusion

The passage from compact Shimura-curve cohomology to a rank-two Galois representation is an auditable sequence. A rational projector isolates a conjugacy orbit but does not remove oldvectors or split a Schur algebra. Selecting a center embedding, splitting the resulting central simple factor, and applying the Hom construction removes the complete finite Hecke module. Book 125's multiplicity formula then makes the remaining continuous Galois factor exactly two-dimensional.

The determinant is not supplied by dimension or by adjoint duality. It comes from Book 125's curve construction: a covariant component multiplier at fine level, a symmetric perfect pairing on the full finite oldspace, and a pull--trace return to the chosen level. Factoring the alternating Poincare pairing leaves

$$
W_{\Pi,\lambda}\times W_{\Pi,\lambda}
\longrightarrow L_\lambda(-1)\otimes\eta_\Pi,
$$

and hence

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi.
$$

The component character is even at real places, so the representation is odd. At a genuinely good place, its geometric Frobenius characteristic polynomial, including the scalar case, is

$$
X^2-t_v(\Pi)X+q_vs_v(\Pi).
$$

Finally, saturation supplies a stable integral packet lattice and an abstract module complement. Integral projectors, stable complements, rank-two Morita factors, and perfect residual polarizations remain subject to their separate denominator tests. The book therefore delivers exactly the curve-cohomological extraction used downstream.
