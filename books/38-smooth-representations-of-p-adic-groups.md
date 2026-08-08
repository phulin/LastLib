# Smooth Representations of $p$-adic Groups

## Contents

1. [The local symmetry problem](#1-the-local-symmetry-problem)
   - [Why smooth representation theory](#11-why-smooth-representation-theory)
   - [Standing conventions](#12-standing-conventions)
   - [The four recurring distinctions](#13-the-four-recurring-distinctions)
2. [Totally disconnected locally compact groups](#2-totally-disconnected-locally-compact-groups)
   - [Compact open subgroups as local coordinates](#21-compact-open-subgroups-as-local-coordinates)
   - [Haar measure and the modular character](#22-haar-measure-and-the-modular-character)
   - [Basic nonarchimedean examples](#23-basic-nonarchimedean-examples)
   - [Discrete and profinite boundary cases](#24-discrete-and-profinite-boundary-cases)
3. [Smooth representations and their finite-level shadows](#3-smooth-representations-and-their-finite-level-shadows)
   - [Why stabilizers define smoothness](#31-why-stabilizers-define-smoothness)
   - [Cyclic representations and compact induction](#32-cyclic-representations-and-compact-induction)
   - [Invariants, coinvariants, and averaging](#33-invariants-coinvariants-and-averaging)
   - [Generated subcategories](#34-generated-subcategories)
4. [Finiteness, irreducibility, and admissibility](#4-finiteness-irreducibility-and-admissibility)
   - [Three independent finiteness conditions](#41-three-independent-finiteness-conditions)
   - [Subquotients and extensions](#42-subquotients-and-extensions)
   - [Irreducibility and Schur's lemma](#43-irreducibility-and-schurs-lemma)
   - [Central characters and twisting](#44-central-characters-and-twisting)
5. [Smooth induction and compact induction](#5-smooth-induction-and-compact-induction)
   - [Sections over a coset space](#51-sections-over-a-coset-space)
   - [Normalized induction and relative modulus](#52-normalized-induction-and-relative-modulus)
   - [Compact induction from an open subgroup](#53-compact-induction-from-an-open-subgroup)
   - [Transitivity](#54-transitivity)
6. [Frobenius reciprocity](#6-frobenius-reciprocity)
   - [Compact induction is a left adjoint](#61-compact-induction-is-a-left-adjoint)
   - [Smooth induction is a right adjoint](#62-smooth-induction-is-a-right-adjoint)
   - [What normalization changes](#63-what-normalization-changes)
   - [A worked cyclic example](#64-a-worked-cyclic-example)
7. [Restriction and Mackey theory](#7-restriction-and-mackey-theory)
   - [Why double cosets appear](#71-why-double-cosets-appear)
   - [Mackey decomposition for compact induction](#72-mackey-decomposition-for-compact-induction)
   - [Intertwining formulas](#73-intertwining-formulas)
   - [The scope of an intertwining criterion](#74-the-scope-of-an-intertwining-criterion)
8. [Smooth contragredients](#8-smooth-contragredients)
   - [Why the algebraic dual is too large](#81-why-the-algebraic-dual-is-too-large)
   - [Evaluation and admissible biduality](#82-evaluation-and-admissible-biduality)
   - [Exactness and subquotients of duals](#83-exactness-and-subquotients-of-duals)
   - [Duals of induced representations](#84-duals-of-induced-representations)
9. [Matrix coefficients and support modulo the center](#9-matrix-coefficients-and-support-modulo-the-center)
   - [Coefficients as observable functions](#91-coefficients-as-observable-functions)
   - [Central characters and compact-mod-center support](#92-central-characters-and-compact-mod-center-support)
   - [Coefficients of compactly induced representations](#93-coefficients-of-compactly-induced-representations)
   - [Character distributions and the boundary of the book](#94-character-distributions-and-the-boundary-of-the-book)
10. [The convolution algebra of a tdlc group](#10-the-convolution-algebra-of-a-tdlc-group)
    - [From functions to operators](#101-from-functions-to-operators)
    - [Local units and idempotents](#102-local-units-and-idempotents)
    - [Involution](#103-involution)
    - [Smooth representations as nondegenerate modules](#104-smooth-representations-as-nondegenerate-modules)
11. [Compact-open and spherical Hecke algebras](#11-compact-open-and-spherical-hecke-algebras)
    - [Compressing convolution to one level](#111-compressing-convolution-to-one-level)
    - [Action on invariant vectors](#112-action-on-invariant-vectors)
    - [Reconstruction and the generated-category boundary](#113-reconstruction-and-the-generated-category-boundary)
    - [A finite-group sanity check](#114-a-finite-group-sanity-check)
12. [Hecke algebras of types](#12-hecke-algebras-of-types)
    - [Why a nontrivial compact type](#121-why-a-nontrivial-compact-type)
    - [The function model](#122-the-function-model)
    - [Support and intertwining](#123-support-and-intertwining)
    - [The type-generated category](#124-the-type-generated-category)
13. [Operations on representations](#13-operations-on-representations)
    - [Restriction to open subgroups](#131-restriction-to-open-subgroups)
    - [Products and external tensor products](#132-products-and-external-tensor-products)
    - [Smooth characters of abelian groups](#133-smooth-characters-of-abelian-groups)
    - [Central quotients and fixed central character](#134-central-quotients-and-fixed-central-character)
14. [Four model laboratories](#14-four-model-laboratories)
    - [Discrete groups](#141-discrete-groups)
    - [Compact profinite groups](#142-compact-profinite-groups)
    - [The multiplicative group of a local field](#143-the-multiplicative-group-of-a-local-field)
    - [Elementary matrix groups](#144-elementary-matrix-groups)
15. [Admissibility tests and compact induction](#15-admissibility-tests-and-compact-induction)
    - [Fixed vectors in a compact induction](#151-fixed-vectors-in-a-compact-induction)
    - [A practical admissibility criterion](#152-a-practical-admissibility-criterion)
    - [Finite length and Hecke modules](#153-finite-length-and-hecke-modules)
    - [Dual admissibility and central support](#154-dual-admissibility-and-central-support)
16. [A reusable local dictionary](#16-a-reusable-local-dictionary)
    - [From congruence level to Hecke module](#161-from-congruence-level-to-hecke-module)
    - [Data carried by a local representation](#162-data-carried-by-a-local-representation)
    - [The $\operatorname{GL}_2(F)$ interface](#163-the-operatornamegl_2f-interface)
    - [The quaternionic interface](#164-the-quaternionic-interface)
    - [Local components and restricted products](#165-local-components-and-restricted-products)
    - [Transfer-compatible operations](#166-transfer-compatible-operations)
17. [Conclusion: finite level inside an infinite group](#17-conclusion-finite-level-inside-an-infinite-group)

## 1. The local symmetry problem

### 1.1 Why smooth representation theory

A group such as $\operatorname{GL}_n(F)$, with $F$ a nonarchimedean local field, is neither discrete nor a real Lie group. It has arbitrarily small compact open subgroups, and these subgroups record congruence to the identity. A useful representation should allow each vector to have some finite congruence level, while the representation as a whole may contain vectors of unbounded level. This is the idea of smoothness.

The resulting theory is algebraic in its vectors and topological in its stabilizers. There is no norm on the representation space unless one is separately supplied. Integration occurs only against compactly supported, locally constant functions, so it reduces to finite algebra after suitable subdivision. This makes smooth representations simultaneously flexible enough for local components of automorphic representations and rigid enough to admit Hecke-algebra methods.

This book develops that general language for Hausdorff totally disconnected locally compact groups. The principal examples are multiplicative groups of local fields, matrix groups over them, compact profinite groups, and discrete groups. No classification of irreducible representations of $\operatorname{GL}_2(F)$ is attempted; that belongs to the next stage. Nor do we analyze representations of a quaternion division group beyond the general compact-mod-center framework needed to state that later theory.

### 1.2 Standing conventions

Unless explicitly stated otherwise, $G$ is a Hausdorff totally disconnected locally compact group, abbreviated **tdlc group**, and $E$ is a field of characteristic zero. A representation $(\pi,V)$ is an $E$-vector space with a left action: $\pi(g_1)\pi(g_2)=\pi(g_1g_2)$. No topology is placed on $V$.

We use left Haar measure $dg$. Its modular character $\Delta_G:G\to\mathbf R_{>0}$ is normalized by

$$
\int_G f(xg)\,dx=\Delta_G(g)^{-1}\int_G f(x)\,dx.
$$

Thus right translation by $g$ scales left Haar measure by $\Delta_G(g)^{-1}$. A group is unimodular when $\Delta_G=1$. Haar measure may be rescaled; formulas involving characteristic functions will always display the relevant volume.

When $H\subseteq G$ and $g\in G$, write $H^g=g^{-1}Hg$. If $(\sigma,W)$ is an $H$-representation, its conjugate $\sigma^g$ is the representation of $H^g$ defined by

$$
\sigma^g(g^{-1}hg)=\sigma(h).
$$

This convention is chosen to match the point $g$ in a left coset space $H\backslash G$.

### 1.3 The four recurring distinctions

Several pairs of notions look similar and must not be merged.

First, **compact support** in $G$ differs from support compact modulo a subgroup or modulo the center. Second, ordinary induction permits arbitrary support on $H\backslash G$, whereas compact induction permits only compact support there. Third, the full algebraic dual $V^*$ is usually not smooth; the contragredient is its smooth part. Fourth, a convolution algebra acts on invariant vectors on the left, while the same algebra appears as the opposite of an endomorphism algebra because endomorphisms act on Hom spaces by precomposition.

The purpose of explicit conventions is not pedantry. An omitted inverse changes a left action into an antiaction; an omitted modular character breaks change of variables; an omitted admissibility hypothesis turns biduality into a false statement. We will repeatedly test definitions on discrete and compact groups, where the distinctions become visible with minimal machinery.

## 2. Totally disconnected locally compact groups

### 2.1 Compact open subgroups as local coordinates

For a Lie group, small neighborhoods are controlled by tangent directions. In a tdlc group, the replacement is a compact open subgroup. The fundamental structural fact is van Dantzig's theorem: compact open subgroups form a neighborhood basis of the identity. Consequently every open subgroup contains a compact open subgroup.

This has three immediate effects. A locally constant function is constant on right cosets of some compact open subgroup locally on its support. A smooth vector is fixed by some compact open subgroup. A compactly supported calculation can be reduced to finitely many cosets. The topology therefore enters representation theory through finite quotients and finite sums.

Intersections of finitely many compact open subgroups remain compact open. If $K$ is compact open and $g\in G$, then $K^g$ is compact open, and $K\cap K^g$ has finite index in both: an open subgroup of a compact group has finite index. This commensurability is the elementary source of double-coset finiteness inside a fixed compact region.

Two useful compactness tests will recur. If $K$ is open, then $G/K$ and $K\backslash G$ are discrete, so the image of a compact subset in either quotient is finite. Equivalently, if $C\subseteq G$ is compact and $K$ is compact open, then $C$ is contained in finitely many left and finitely many right $K$-cosets. Cover $C$ by open cosets and extract a finite subcover. This is the exact step that turns compact support into a finite sum.

Open subgroups are also closed: their complements are unions of open cosets. A closed subgroup of a locally compact Hausdorff group is locally compact, and quotients by closed subgroups are Hausdorff. Thus “closed” in induction protects the topology of $H\backslash G$, while “open” makes that quotient discrete. Each hypothesis solves a different problem.

### 2.2 Haar measure and the modular character

A left Haar measure is a nonzero regular Borel measure invariant under left translation, unique up to a positive scalar. Every compact open $K$ has finite positive volume. We may normalize $\operatorname{vol}(K)=1$ for one chosen $K$, but generally cannot impose that normalization simultaneously on every compact open subgroup.

If $J\subseteq K$ are compact open, then

$$
\operatorname{vol}(K)=[K:J]\operatorname{vol}(J).
$$

This follows by decomposing $K$ into finitely many left $J$-cosets. It is the measure-theoretic form of the denominators that occur in averaging.

The modular character measures the failure of right invariance. It is a continuous homomorphism. Compact subgroups lie in its kernel, since a compact subgroup has compact image in $\mathbf R_{>0}$ and the latter has no nontrivial compact subgroup. Thus every compact group, every discrete group with counting measure, and every abelian locally compact group is unimodular. Reductive groups over nonarchimedean local fields are also unimodular, while their parabolic subgroups generally are not.

**Example.** Let $F$ be a nonarchimedean local field and $B\subseteq\operatorname{GL}_2(F)$ the upper triangular subgroup. For $t=\operatorname{diag}(a,d)$, conjugation scales the additive coordinate of the unipotent radical by $a/d$. With the convention above,

$$
\Delta_B(t)=|d/a|_F.
$$

Indeed left Haar measure on the semidirect product acquires the inverse of the scaling on the unipotent coordinate. The ambient group $\operatorname{GL}_2(F)$ is unimodular. The parabolic modulus used in normalized induction is therefore $\Delta_G|_B/\Delta_B=|a/d|_F$. Distinguishing the group modular character from this relative modulus prevents an easy inversion error.

### 2.3 Basic nonarchimedean examples

The additive group $(F,+)$ has compact open subgroups $\mathfrak p_F^n$, $n\in\mathbf Z$. The multiplicative group $F^\times$ has compact open subgroup $\mathcal O_F^\times$ and decomposition

$$
F^\times\cong \varpi^{\mathbf Z}\times\mathcal O_F^\times
$$

after choosing a uniformizer $\varpi$. Both groups are abelian and hence unimodular.

For $G=\operatorname{GL}_n(F)$, the subgroup $K_0=\operatorname{GL}_n(\mathcal O_F)$ is compact open. Principal congruence subgroups

$$
K_m=\ker\bigl(\operatorname{GL}_n(\mathcal O_F)\to
\operatorname{GL}_n(\mathcal O_F/\mathfrak p_F^m)\bigr),\qquad m\geq1,
$$

form a neighborhood basis of the identity. Every vector in a smooth representation is therefore fixed at some congruence depth, though no single depth need fix the whole representation.

A finite product of tdlc groups is tdlc, and a product of chosen compact opens is compact open. More broadly, a restricted product $\prod'_v(G_v,K_v)$ is locally compact with compact open $\prod_vK_v$ when each $K_v$ is compact open. The almost-everywhere condition is part of the topology: it lets a global vector have nontrivial local behavior at finitely many places while retaining a compact tail.

### 2.4 Discrete and profinite boundary cases

Every discrete group is tdlc. Its compact subsets are finite, its compact open subgroups are finite subgroups, and the trivial subgroup is compact open. Hence every algebraic representation of a discrete group is smooth. Compact induction from the trivial subgroup is the finitely supported regular representation, not the full space of all functions on the group.

A compact tdlc group is profinite. In a smooth representation of a profinite group, each vector has an open stabilizer and hence a finite orbit. Its cyclic subrepresentation factors through a finite quotient. Over characteristic zero, such finite-dimensional cyclic pieces are semisimple. The whole representation can nevertheless be an infinite direct sum and need not be admissible: the trivial representation repeated infinitely often has infinite-dimensional fixed vectors.

These boundary cases are valuable counterweights. Discreteness shows that smoothness alone imposes no finiteness. Compactness shows that local semisimplicity does not imply finite multiplicities.

## 3. Smooth representations and their finite-level shadows

### 3.1 Why stabilizers define smoothness

Since $V$ has no topology, continuity of the orbit map cannot be phrased in the usual way unless $V$ is declared discrete. Doing so gives exactly the right condition.

A representation $(\pi,V)$ is **smooth** if for every $v\in V$ the stabilizer

$$
G_v=\{g\in G:\pi(g)v=v\}
$$

is open. Equivalently, every vector is fixed by some compact open subgroup. For an arbitrary representation $V$, its subspace of **smooth vectors** is

$$
V^{\mathrm{sm}}=\bigcup_{K}V^K,
\qquad
V^K=\{v:kv=v\text{ for all }k\in K\},
$$

where $K$ ranges over compact open subgroups. This union is a $G$-stable subspace: if $v$ is fixed by $K$, then $gv$ is fixed by $gKg^{-1}$.

**Counterexample.** Let $G=\mathbf Z_p$ and let it act on a characteristic-zero vector space through a homomorphism with a vector having trivial stabilizer. That vector is not smooth, because the trivial subgroup is not open in $\mathbf Z_p$. An abstract group representation of the underlying group is therefore not automatically a smooth representation.

### 3.2 Cyclic representations and compact induction

If $v$ is fixed by a compact open $K$, then the cyclic representation $E[G]v$ is controlled by the coset space $K\backslash G$. This is the first indication that compact induction is universal.

Let $\mathrm{c\text{-}Ind}_K^G\mathbf1$ be the space of locally constant functions $f:G\to E$ that are left $K$-invariant and have finite support on the discrete space $K\backslash G$. The action is right translation:

$$
(g_0f)(x)=f(xg_0).
$$

The characteristic function $\mathbf1_K$ is $K$-fixed. For every $v\in V^K$ there is a unique $G$-map

$$
T_v:\mathrm{c\text{-}Ind}_K^G\mathbf1\longrightarrow V,
\qquad T_v(\mathbf1_K)=v.
$$

Indeed the translates of $\mathbf1_K$ are characteristic functions of right translates $Kg^{-1}$ and form a basis. The image is exactly the cyclic subrepresentation generated by $v$. Thus every smooth representation is a quotient of a direct sum of compactly induced trivial representations, one for a suitable stabilizer of each chosen generator.

### 3.3 Invariants, coinvariants, and averaging

For any subgroup $H$, invariants are left exact: an injection remains injective after taking $H$-fixed vectors, but surjectivity can fail. Coinvariants

$$
V_H=V/\langle hv-v:h\in H,\ v\in V\rangle
$$

are right exact. For compact open $K$ and characteristic-zero coefficients, averaging removes this asymmetry.

Normalize Haar measure on $K$ to total mass $1$. For a smooth $K$-representation define

$$
e_Kv=\int_Kkv\,dk.
$$

This is an algebraic finite sum: the orbit of $v$ factors through a finite quotient of $K$. The operator $e_K$ is idempotent, has image $V^K$, and is the identity on $V^K$.

**Proposition 3.1.** On smooth representations over a characteristic-zero field, $V\mapsto V^K$ is exact for compact open $K$. Moreover the natural map $V^K\to V_K$ is an isomorphism.

**Proof strategy.** Average a lift to repair noninvariance, and average a relation to identify coinvariants with invariants.

**Proof.** Given a surjection $V\to W$ and $w\in W^K$, choose a lift $v$. Then $e_Kv$ is $K$-fixed and maps to $e_Kw=w$. Hence invariants preserve surjections. The composite $V^K\to V\to V_K$ is injective because applying $e_K$ to a relation in the span of $kv-v$ gives zero, and it is surjective because $v$ and $e_Kv$ have the same coinvariant class. $\square$

The characteristic-zero hypothesis can be weakened: it suffices that the orders of all finite quotients through which the relevant $K$-orbits factor be invertible in $E$. It cannot simply be omitted.

There is a normalization-free description of the same projector. If $J\triangleleft K$ is open normal and fixes $v$, then

$$
e_Kv=\frac1{[K:J]}\sum_{k\in K/J}kv.
$$

Choosing a smaller normal subgroup gives the same result, since every old coset is subdivided equally. This proves that the integral is algebraic and shows exactly which denominators are used. For a pro-$p$ group in characteristic different from $p$, averaging over its finite $p$-group quotients remains available; in characteristic $p$ it does not.

**Modular-coefficient failure.** Let $K=C_p$ and let $E$ have characteristic $p$. The augmentation map $E[K]\to E$ is surjective. The invariant line of the regular representation is spanned by $\sum_{k\in K}k$, whose augmentation is $p=0$. Thus the induced map on invariants is zero, not surjective. Averaging would require division by $p$. In modular representation theory compact-open invariants are therefore not generally exact or interchangeable with coinvariants.

### 3.4 Generated subcategories

For a compact open $K$, say that $V$ is **generated by its $K$-fixed vectors** if $V=E[G]V^K$. This is a genuine restriction. A representation may have $V^K=0$ while being nonzero, or may contain $K$-fixed vectors that generate only a proper summand.

The distinction will govern the Hecke correspondence. The spherical Hecke algebra sees $V^K$, so it cannot recover representations invisible at level $K$. Its natural domain is the full subcategory generated by $K$-fixed vectors, not all smooth representations of $G$.

## 4. Finiteness, irreducibility, and admissibility

### 4.1 Three independent finiteness conditions

A smooth representation is **admissible** if $\dim_E V^K<\infty$ for every compact open $K$. It has **finite length** if it has a finite composition series. It is **finitely generated** if finitely many vectors generate it as a $G$-representation. None of these notions is built into smoothness.

For a discrete infinite group, the regular representation is generated by one vector but usually has $V^{\{1\}}=V$ infinite-dimensional, so it is not admissible. For a compact profinite group, an infinite direct sum of pairwise chosen finite-dimensional representations can be semisimple but have infinite length. Conversely, admissibility need not imply finite length for arbitrary tdlc groups.

The setting matters. Deep finiteness theorems for reductive $p$-adic groups often imply admissibility of irreducibles, but that is a structural theorem about those groups, not a formal consequence of the definitions developed here.

### 4.2 Subquotients and extensions

Exactness of compact-open invariants gives robust permanence properties in characteristic zero.

**Proposition 4.1.** In a short exact sequence of smooth representations

$$
0\longrightarrow U\longrightarrow V\longrightarrow W\longrightarrow0,
$$

$V$ is admissible if and only if both $U$ and $W$ are admissible.

**Proof.** For each compact open $K$, averaging gives a short exact sequence

$$
0\longrightarrow U^K\longrightarrow V^K\longrightarrow W^K\longrightarrow0.
$$

Finite dimensionality of the middle term is equivalent to finite dimensionality of the two outer terms. $\square$

Thus subrepresentations, quotients, and finite extensions of admissible representations are admissible. If every irreducible subquotient in a finite composition series is admissible, the whole finite-length representation is admissible. Without admissibility of irreducibles this implication is not automatic.

Finite length itself passes to subquotients and is stable under extensions. Finite generation passes to quotients but need not pass to arbitrary subrepresentations without additional noetherian hypotheses.

An admissible representation has a useful local finiteness property for endomorphisms. Every $G$-endomorphism preserves every $V^K$, so its eigenvalues and polynomial relations can be tested on finite-dimensional levels, and the trace of each restricted operator $T|_{V^K}$ is defined. This does not produce a trace of $T$ on all of $V$: as $K$ shrinks, the spaces $V^K$ may grow without bound, and their union is all of $V$. Admissibility is finite dimensionality at every fixed resolution.

### 4.3 Irreducibility and Schur's lemma

A nonzero smooth representation is **irreducible** if it has no nonzero proper $G$-stable subspace. The usual algebraic proof of Schur's lemma applies without topology: for irreducible $V$, every nonzero $G$-endomorphism is invertible. Hence $\operatorname{End}_G(V)$ is a division algebra over $E$.

It is unsafe to replace “division algebra” by “the coefficient field” without hypotheses. A real irreducible representation may have complex or quaternionic endomorphisms, and over a non-algebraically closed field other division algebras occur.

**Proposition 4.2.** If $E$ is algebraically closed and $V$ is irreducible and admissible, then $\operatorname{End}_G(V)=E$.

**Proof strategy.** Trap an arbitrary endomorphism in one nonzero finite-dimensional fixed-vector space, find an eigenvalue there, and use irreducibility globally.

**Proof.** Choose $0\neq v\in V$ and a compact open $K$ fixing it. Every $G$-endomorphism $T$ preserves the nonzero finite-dimensional space $V^K$. Since $E$ is algebraically closed, $T|_{V^K}$ has an eigenvalue $\lambda$. Then $T-\lambda$ has nonzero kernel in $V$. Its kernel is $G$-stable, so irreducibility makes it all of $V$. Thus $T=\lambda$. $\square$

Admissibility is doing real work: it provides a finite-dimensional place in which an eigenvalue must exist.

### 4.4 Central characters and twisting

Let $Z=Z(G)$. If $V$ is irreducible and Schur's conclusion $\operatorname{End}_G(V)=E$ holds, each $z\in Z$ acts by a scalar. These scalars define the **central character** $\omega_V:Z\to E^\times$. It is smooth: any nonzero vector has open stabilizer in $G$, whose intersection with $Z$ is an open subgroup on which $\omega_V$ is trivial.

For a smooth character $\chi:G\to E^\times$, the twist $V\otimes\chi$ has action

$$
g(v\otimes1)=\chi(g)\,gv\otimes1.
$$

Twisting preserves irreducibility, admissibility, and length. Its central character is $\omega_V\chi|_Z$. Twists are a basic organizing symmetry: many local invariants change predictably under them even when the underlying representation does not remain isomorphic.

## 5. Smooth induction and compact induction

### 5.1 Sections over a coset space

Induction extends a representation of a subgroup to the ambient group. The covariance law should remember the original $H$-action, while the remaining variable should range over $H\backslash G$. Fix a closed subgroup $H\subseteq G$ and a smooth $H$-representation $(\sigma,W)$.

The **unnormalized smooth induction** $\operatorname{Ind}_H^G\sigma$ consists of functions $f:G\to W$ satisfying

$$
f(hg)=\sigma(h)f(g)\qquad(h\in H,g\in G)
$$

whose right-translation orbit is smooth. Equivalently, each $f$ is right invariant under some compact open subgroup of $G$. We let $G$ act by right translation:

$$
(g_0f)(x)=f(xg_0).
$$

The order is correct:

$$
g_1(g_2f)(x)=f(xg_1g_2)=((g_1g_2)f)(x).
$$

For closed $H$, the quotient $H\backslash G$ is locally compact and Hausdorff, so support modulo $H$ is meaningful. The **compact induction** $\mathrm{c\text{-}Ind}_H^G\sigma$ is the subrepresentation consisting of functions whose image of the support in $H\backslash G$ is compact. When $H$ is open, $H\backslash G$ is discrete, so this says that the support meets only finitely many left $H$-cosets. In that case the definition is entirely algebraic and compact induction has its cleanest universal property.

Support means the closure of the nonzero locus. Covariance makes that locus left $H$-stable, so it has a well-defined image in $H\backslash G$. The useful condition is equivalently that the support lie in $HC$ for some compact $C\subseteq G$. When $H$ is open, a finite set of representatives is compact, and this becomes literal finite coset support.

Right translation preserves the condition: the support of $g_0f$ is $\operatorname{supp}(f)g_0^{-1}$, whose quotient image is compact. The inverse agrees with $(g_0f)(x)=f(xg_0)$. Checking support and action together is the quickest way to detect a handedness error.

Ordinary induction and compact induction coincide if $H\backslash G$ is compact. They differ sharply for $H=\{1\}$ in an infinite discrete group: induction is all functions $G\to W$, whereas compact induction is the finitely supported functions.

### 5.2 Normalized induction and relative modulus

Unnormalized induction is the form directly dictated by covariance and is the right adjoint to restriction. In harmonic analysis a modular correction gives better duality. Assume that $E$ contains the required square roots of positive real modular values, or that an $E$-valued square-root character has been chosen. Define

$$
\delta_{H\backslash G}(h)=\Delta_G(h)\Delta_H(h)^{-1}.
$$

The **normalized induction** is

$$
i_H^G(\sigma)=
\operatorname{Ind}_H^G(\delta_{H\backslash G}^{1/2}\otimes\sigma).
$$

Thus its functions satisfy

$$
f(hg)=\delta_{H\backslash G}(h)^{1/2}\sigma(h)f(g).
$$

If $G$ is unimodular and $H$ is a parabolic subgroup, this is the inverse square root of the group modular character of $H$, customarily called the positive half-power of the parabolic modulus. For the upper triangular subgroup of $\operatorname{GL}_2(F)$ it is $|a/d|_F^{1/2}$. For open $H$, the two groups have compatible modular characters: $\Delta_H=\Delta_G|_H$, so the relative modulus is trivial. Normalized and unnormalized induction from an open subgroup then agree.

One should not write a half-modular twist over an arbitrary coefficient field without checking that it exists. All algebraic adjunctions below are stated first for unnormalized induction and require no square roots.

### 5.3 Compact induction from an open subgroup

Suppose $H$ is open. For $w\in W$, define $[1,w]$ by

$$
[1,w](h)=\sigma(h)w\quad(h\in H),
\qquad [1,w](g)=0\quad(g\notin H).
$$

It is locally constant because $H$ is open, and its support is one point in $H\backslash G$. Every compactly induced function is a finite sum of translates of such functions. The relation

$$
h[1,w]=[1,\sigma(h)w]\qquad(h\in H)
$$

encodes exactly the relations needed to extend an $H$-map out of $W$.

If $H$ is closed but not open, extension by zero from $H$ is generally not locally constant along the boundary. This is why the elementary proof of the left adjunction does not extend verbatim. Compact induction for general closed subgroups remains useful analytically, but measure and modular issues enter its universal properties. In this book all purely algebraic compact-induction adjunctions are asserted for open subgroups.

### 5.4 Transitivity

Let $J\subseteq H\subseteq G$. Under the hypotheses making the indicated inductions smooth, induction is transitive:

$$
\operatorname{Ind}_H^G\bigl(\operatorname{Ind}_J^H\tau\bigr)
\cong\operatorname{Ind}_J^G\tau.
$$

For open inclusions, compact induction is transitive as well:

$$
\mathrm{c\text{-}Ind}_H^G\bigl(\mathrm{c\text{-}Ind}_J^H\tau\bigr)
\cong\mathrm{c\text{-}Ind}_J^G\tau.
$$

The second statement is ultimately a finite-support assertion. A function supported on finitely many $H$-cosets, each carrying data supported on finitely many $J$-cosets, has finite support on $J\backslash G$; conversely a finite set of $J$-cosets lies over finitely many $H$-cosets. This simple bookkeeping is the model for later double-coset arguments.

## 6. Frobenius reciprocity

### 6.1 Compact induction is a left adjoint

Adjunction explains why compact induction is ubiquitous: it is the freest smooth $G$-representation containing prescribed $H$-data.

**Theorem 6.1 (compact Frobenius reciprocity).** If $H$ is open in $G$, then naturally

$$
\operatorname{Hom}_G(\mathrm{c\text{-}Ind}_H^G\sigma,V)
\cong\operatorname{Hom}_H(\sigma,V|_H).
$$

**Proof strategy.** A $G$-map is determined by functions supported on $H$. Conversely an $H$-map prescribes images of those functions, and finite support makes the extension a finite sum.

**Proof.** Given a $G$-map $T$, send it to $w\mapsto T([1,w])$. The relation $h[1,w]=[1,\sigma(h)w]$ shows that this map is $H$-equivariant.

Conversely let $a:W\to V$ be $H$-equivariant. Write a compactly induced function as a finite sum

$$
f=\sum_i g_i[1,w_i].
$$

Set $T_a(f)=\sum_i g_i a(w_i)$. The covariance relation is exactly what makes this independent of the expression, and right translation makes $T_a$ $G$-equivariant. The two constructions are inverse. $\square$

Taking $\sigma=\mathbf1$ recovers

$$
\operatorname{Hom}_G(\mathrm{c\text{-}Ind}_K^G\mathbf1,V)\cong V^K.
$$

Naturality is important. A map $\sigma\to\sigma'$ induces a map of compact inductions, and a map $V\to V'$ induces a map on both Hom spaces; reciprocity commutes with both. It is therefore an adjunction, not merely a dimension equality. Since $\operatorname{Hom}_G(P_K,-)=(-)^K$ is exact in characteristic zero, it also proves directly that $P_K=\mathrm{c\text{-}Ind}_K^G\mathbf1$ is projective.

### 6.2 Smooth induction is a right adjoint

Ordinary smooth induction solves the opposite extension problem.

**Theorem 6.2 (induced Frobenius reciprocity).** For a closed subgroup $H$ for which the smooth induced representation is defined as in Section 5.1, there is a natural isomorphism

$$
\operatorname{Hom}_G(V,\operatorname{Ind}_H^G\sigma)
\cong\operatorname{Hom}_H(V|_H,\sigma).
$$

**Proof strategy.** Evaluation at the identity loses no information because equivariance reconstructs every value from the orbit of the input vector.

**Proof.** If $T:V\to\operatorname{Ind}_H^G\sigma$, put $a(v)=T(v)(1)$. For $h\in H$,

$$
a(hv)=T(hv)(1)=(hT(v))(1)=T(v)(h)=\sigma(h)T(v)(1),
$$

so $a$ is $H$-equivariant. Conversely, given $a:V|_H\to W$, define

$$
T_a(v)(g)=a(gv).
$$

Then $T_a(v)(hg)=a(hgv)=\sigma(h)a(gv)$, and if a compact open $K$ fixes $v$, right translation by $K$ fixes $T_a(v)$. Finally

$$
T_a(g_0v)(x)=a(xg_0v)=(g_0T_a(v))(x).
$$

Evaluation and reconstruction are inverse. $\square$

### 6.3 What normalization changes

Applying the unnormalized adjunction to $i_H^G(\sigma)$ gives

$$
\operatorname{Hom}_G(V,i_H^G\sigma)
\cong
\operatorname{Hom}_H
(V,\delta_{H\backslash G}^{1/2}\otimes\sigma).
$$

Thus normalized induction is not literally the same right adjoint; the modular twist must travel to the other side. Normalization is selected because it makes contragredient and unitary formulas symmetric, not because it erases all modular characters from every adjunction.

### 6.4 A worked cyclic example

Let $G=F^\times$, $H=\mathcal O_F^\times$, and take the trivial representation of $H$. Since

$$
H\backslash G\cong\mathbf Z
$$

through valuation, $\mathrm{c\text{-}Ind}_H^G\mathbf1$ has basis $e_n$, the characteristic functions of $H\varpi^n$. Multiplication by $\varpi$ shifts the basis. A vector $v$ fixed by $H$ determines a map $e_0\mapsto v$ and $e_n\mapsto\varpi^{-n}v$ with the present right-translation indexing. The cyclic subrepresentation generated by $v$ is therefore a quotient of a Laurent-polynomial regular module. A smooth character $\chi$ trivial on $H$ imposes the relation that the shift acts by $\chi(\varpi)$.

This example exposes both the usefulness and limitation of compact induction: it records all possible unramified eigenvalues at once but does not choose one until a quotient is taken.

## 7. Restriction and Mackey theory

### 7.1 Why double cosets appear

Restricting an induced representation from $G$ to a subgroup $L$ no longer moves transitively across $H\backslash G$. The $L$-orbits are exactly the double cosets $H\backslash G/L$. Mackey theory decomposes the restricted representation orbit by orbit and identifies the stabilizer on each orbit.

Suppose $H$ and $L$ are open subgroups of $G$, and let $X\subseteq G$ represent $H\backslash G/L$. For $x\in X$, put

$$
J_x=L\cap H^x=L\cap x^{-1}Hx.
$$

On $J_x$, use the representation $\sigma^x(j)=\sigma(xjx^{-1})$.

### 7.2 Mackey decomposition for compact induction

**Theorem 7.1.** With $H,L$ open,

$$
\operatorname{Res}_L^G\mathrm{c\text{-}Ind}_H^G\sigma
\cong
\bigoplus_{x\in H\backslash G/L}
\mathrm{c\text{-}Ind}_{J_x}^L(\sigma^x|_{J_x}).
$$

**Proof strategy.** Split a compactly supported function according to the disjoint open double cosets $HxL$, then read its restriction along $l\mapsto xl$.

**Proof.** A function supported in $HxL$ gives $\phi(l)=f(xl)$. If $j\in J_x$, then $xj=h x$ for $h=xjx^{-1}\in H$, and

$$
\phi(jl)=f(xjl)=f(hxl)=\sigma(h)f(xl)=\sigma^x(j)\phi(l).
$$

Support compactness on $H\backslash HxL$ becomes finite support on $J_x\backslash L$. Conversely such a $\phi$ extends uniquely to $HxL$ by covariance. Because a compact subset of the discrete space $H\backslash G$ is finite, any compactly induced function meets only finitely many double cosets. Hence the sum is algebraic direct, not a product. $\square$

For ordinary induction, the analogous orbitwise expression uses the smooth part of a product rather than a direct sum:

$$
\operatorname{Res}_L^G\operatorname{Ind}_H^G\sigma
\cong
\left(
\prod_{x\in H\backslash G/L}
\operatorname{Ind}_{J_x}^L(\sigma^x|_{J_x})
\right)^{\mathrm{sm}}.
$$

The smooth-part qualification imposes a common open stabilizer on the whole tuple. Confusing product with direct sum is the same support error as confusing all functions with finitely supported functions on an infinite discrete set; omitting the smooth part is a separate error when infinitely many orbit components occur.

**Discrete example.** Let $G$ be discrete. The summand indexed by $HxL$ is induced from $L\cap x^{-1}Hx$. A finitely supported function on $H\backslash G$ meets finitely many $L$-orbits, hence belongs to a direct sum. An arbitrary function may be nonzero on every orbit, hence belongs to a product. The general topological formula is the same orbit-stabilizer calculation with compactness replacing literal finiteness.

### 7.3 Intertwining formulas

Let $K,L$ be compact open, with finite-dimensional smooth representations $\tau$ and $\eta$. Combining compact Frobenius reciprocity, Mackey decomposition, and the fact that induction and compact induction coincide inside the compact group $K$ gives

$$
\operatorname{Hom}_G
(\mathrm{c\text{-}Ind}_K^G\tau,
 \mathrm{c\text{-}Ind}_L^G\eta)
\cong
\bigoplus_{x\in L\backslash G/K}
\operatorname{Hom}_{K\cap x^{-1}Lx}
(\tau,\eta^x).
$$

Here $\eta^x(k)=\eta(xkx^{-1})$ on $K\cap x^{-1}Lx$. The direct sum means that an intertwining operator has only finitely many active double-coset components. If the Hom spaces are nonzero for infinitely many double cosets, the full endomorphism space may be infinite-dimensional, but each individual operator is still a finite sum in this compact-induction model.

For $K=L$ and $\tau=\eta$, define the **intertwining set**

$$
I_G(\tau)=\left\{g\in G:
\operatorname{Hom}_{K\cap K^g}(\tau,\tau^g)\neq0\right\}.
$$

It is stable under left and right multiplication by $K$. The formula shows that the endomorphism algebra of $\mathrm{c\text{-}Ind}_K^G\tau$ is supported precisely on $K\backslash I_G(\tau)/K$.

### 7.4 The scope of an intertwining criterion

If $\tau$ is irreducible, $\operatorname{End}_K(\tau)=E$, and $I_G(\tau)=K$, then the compactly induced representation has scalar endomorphism algebra. This is a powerful diagnostic, but scalar endomorphisms alone do not imply irreducibility in an arbitrary nonsemisimple category.

A precise useful criterion is the following. Put $P=\mathrm{c\text{-}Ind}_K^G\tau$ and assume:

1. $\operatorname{End}_K(\tau)=E$ and $I_G(\tau)=K$;
2. every nonzero $G$-subrepresentation $U\subseteq P$ contains the $K$-type $\tau$, meaning $\operatorname{Hom}_K(\tau,U)\neq0$.

Then $P$ is irreducible. Indeed a nonzero inclusion $U\hookrightarrow P$ and a nonzero map $P\to U$ supplied by Frobenius reciprocity compose to a nonzero endomorphism of $P$. It is scalar and therefore invertible, forcing $U=P$. In concrete constructions the second condition is often proved by a support-minimization argument; it must not be silently inferred from the first.

## 8. Smooth contragredients

### 8.1 Why the algebraic dual is too large

The full algebraic dual $V^*=\operatorname{Hom}_E(V,E)$ carries the contragredient action

$$
(g\lambda)(v)=\lambda(g^{-1}v).
$$

The inverse is forced by the left-action law. But a general functional need not have open stabilizer, even when $V$ is smooth. The representation-theoretic dual is therefore

$$
V^\vee=(V^*)^{\mathrm{sm}}=\bigcup_K(V^*)^K,
$$

the **smooth contragredient**.

For compact open $K$, a functional is $K$-invariant exactly when it annihilates every $kv-v$. Hence

$$
(V^\vee)^K=(V^*)^K\cong(V_K)^*.
$$

In characteristic zero, averaging identifies $V_K\cong V^K$, and therefore

$$
(V^\vee)^K\cong(V^K)^*.
$$

This finite-level formula is the engine behind all admissible duality statements.

### 8.2 Evaluation and admissible biduality

Evaluation defines a natural $G$-map

$$
\iota_V:V\longrightarrow(V^\vee)^\vee,
\qquad \iota_V(v)(\lambda)=\lambda(v).
$$

Over characteristic zero it is injective. To separate $0\neq v$, choose compact open $K$ fixing $v$, choose any algebraic functional nonzero on $v$, and average it over $K$. The averaged functional is smooth and retains its value on $v$.

**Theorem 8.1.** If $V$ is admissible, then $\iota_V$ is an isomorphism. Moreover $V^\vee$ is admissible and $\dim(V^\vee)^K=\dim V^K$ for every compact open $K$.

**Proof strategy.** Test the evaluation map on every fixed-vector space, where it becomes ordinary finite-dimensional biduality.

**Proof.** The displayed identification gives $(V^\vee)^K\cong(V^K)^*$, so the contragredient is admissible. Taking the same formula again, the map on $K$-fixed vectors is

$$
V^K\longrightarrow((V^K)^*)^*,
$$

which is an isomorphism because $V^K$ is finite-dimensional. Every vector on either side is fixed by some compact open subgroup, so the global map is an isomorphism. $\square$

**Counterexample.** If $G$ is trivial and $V$ is infinite-dimensional, then $V^\vee=V^*$ and the map $V\to V^{**}$ is injective but not surjective. The group is compact, the representation is smooth, and only admissibility fails. Thus admissibility is not decorative in biduality.

### 8.3 Exactness and subquotients of duals

The algebraic dual reverses short exact sequences, and taking smooth vectors is exact in this setting because it can be checked after compact-open averaging. Consequently the smooth contragredient is an exact contravariant functor on smooth characteristic-zero representations:

$$
0\to U\to V\to W\to0
$$

gives

$$
0\to W^\vee\to V^\vee\to U^\vee\to0.
$$

For surjectivity on the right, a smooth functional on $U$ fixed by $K$ extends algebraically to $V$ and can then be averaged over $K$. It follows that the contragredient preserves finite length and exchanges irreducible subrepresentations with irreducible quotients. On admissible representations it is an involutive duality.

### 8.4 Duals of induced representations

Modular factors become unavoidable when induction is dualized. Suppose, for example, that $H\backslash G$ is compact and that the normalized quotient integration needed for the natural pairing exists over the coefficients. Then compact and ordinary induction coincide, and normalized induction has the clean formula

$$
(i_H^G\sigma)^\vee\cong i_H^G(\sigma^\vee).
$$

For unnormalized induction, the corresponding formula carries the relative modular character. This is the conceptual reason for normalization: it divides the change-of-variables correction evenly between a representation and its dual. Without cocompactness, a duality formula must also account for the difference between compactly supported and unrestricted sections; there is no blanket identity of the displayed form for an arbitrary closed subgroup.

For open $H$, the relative modulus is trivial. Compact induction and ordinary induction still need not coincide, so duality exchanges the support condition in the expected way: the dual of a direct sum behaves like a product before taking smooth vectors. Any formula identifying the two inductions therefore requires a cocompactness or finiteness hypothesis, not merely openness.

## 9. Matrix coefficients and support modulo the center

### 9.1 Coefficients as observable functions

Given $v\in V$ and $\lambda\in V^\vee$, the **matrix coefficient** is

$$
c_{v,\lambda}(g)=\lambda(gv).
$$

It is locally constant. If $K$ fixes $v$, then $c_{v,\lambda}(gk)=c_{v,\lambda}(g)$; if $L$ fixes $\lambda$, then $c_{v,\lambda}(lg)=c_{v,\lambda}(g)$. Thus a coefficient is bi-invariant under possibly different compact open subgroups. It converts the representation into locally constant scalar data on $G$ and allows convolution to act by integration.

Translation of the inputs matches translation of the function:

$$
c_{hv,\lambda}(g)=c_{v,\lambda}(gh),
\qquad
c_{v,h\lambda}(g)=c_{v,\lambda}(h^{-1}g).
$$

These formulas are useful checks on every inverse convention.

### 9.2 Central characters and compact-mod-center support

Suppose $V$ has central character $\omega$. Then

$$
c_{v,\lambda}(zg)=\omega(z)c_{v,\lambda}(g)\qquad(z\in Z(G)).
$$

Unless $\omega$ is trivial, a nonzero coefficient cannot descend as a scalar-valued function to $Z\backslash G$; nevertheless its support is $Z$-stable. We say it is **compactly supported modulo the center** if the image of its support in $Z\backslash G$ is compact.

This is weaker than compact support when $Z$ is noncompact. For $G=F^\times=Z(G)$, every nonzero character coefficient has support all of $G$, which is compact modulo $Z$ but not compact. The distinction is central for quaternion division groups and for discrete-series phenomena on matrix groups.

An irreducible admissible representation with central character is often called **supercuspidal** in a general reductive setting when its matrix coefficients are compactly supported modulo the center, though equivalent definitions and exact scope depend on the group. Here we use only the support property, leaving classification terminology to group-specific theory.

### 9.3 Coefficients of compactly induced representations

Let $J$ be open and compact modulo a central subgroup $Z$, let $\rho$ be a finite-dimensional representation of $J$, and assume $Z\subseteq J$ acts through a character. Vectors in $\mathrm{c\text{-}Ind}_J^G\rho$ have support in finitely many left $J$-cosets. Pair a vector with a vector in the naturally embedded compact induction of $\rho^\vee$. Their coefficient can be nonzero only when the translating element lies in a finite union of sets of the form $JgJ$. Each such set has compact image in $Z\backslash G$ because $J/Z$ is compact. These particular coefficients are therefore compactly supported modulo $Z$.

The qualification about the dual vector is essential. For an infinite discrete group, the full algebraic—and hence smooth—dual of the finitely supported regular representation contains arbitrary coefficient functions, many with noncompact support. If the compact induction is irreducible and admissible and its contragredient is identified with the expected compactly induced dual, the argument applies to all of its matrix coefficients. This explains why compact induction from compact-mod-center subgroups is a natural source of compact-mod-center representations, while not asserting irreducibility or admissibility for free.

### 9.4 Character distributions and the boundary of the book

For an admissible representation, a compactly supported locally constant function acts with finite-rank image after suitable compact-open averaging, so traces can often be defined and assembled into a distribution character. Character theory is essential in transfer, but its analytic development and character identities belong with the specific groups and correspondences that follow. The durable input established here is simpler: matrix coefficients are locally constant, their left and right levels are controlled by stabilizers, and compact-mod-center support has a precise quotient-topological meaning.

## 10. The convolution algebra of a tdlc group

### 10.1 From functions to operators

Let

$$
\mathcal H(G)=C_c^\infty(G,E)
$$

be the compactly supported locally constant $E$-valued functions. To interpret integrals algebraically, choose one compact open $K_0$ and normalize $\operatorname{vol}(K_0)=1$. The intersection-index formula then makes the volume of every compact open subgroup rational, so the Haar integrals below take values in $E$ through the canonical copy of $\mathbf Q\subseteq E$. More generally one may rescale by any chosen element of $E^\times$. Define convolution using this left Haar measure:

$$
(f_1*f_2)(x)=\int_G f_1(y)f_2(y^{-1}x)\,dy.
$$

The integral is a finite sum after subdividing the compact support into cosets on which the integrand is constant. Associativity follows from Fubini's theorem for compactly supported locally constant functions and left invariance of Haar measure.

Every smooth representation obtains an action

$$
\pi(f)v=\int_G f(g)\pi(g)v\,dg.
$$

Our conventions give

$$
\pi(f_1*f_2)=\pi(f_1)\pi(f_2).
$$

Indeed, expand the right side, set $x=gh$, and use left invariance in the $g$ variable. This compatibility is the main reason for the chosen order $f_2(y^{-1}x)$.

### 10.2 Local units and idempotents

If $K$ is compact open, set

$$
e_K=\frac{\mathbf1_K}{\operatorname{vol}(K)}.
$$

Then $e_K*e_K=e_K$, and $\pi(e_K)$ is the averaging projection onto $V^K$. The full convolution algebra usually has no identity when $G$ is nondiscrete: a delta function at $1$ is not locally constant. Instead it has **local units**. For any finite set of functions there is a sufficiently small compact open $K$ such that left and right convolution by $e_K$ fixes all of them.

Indeed, compactness and local constancy allow one to choose a single $K$ under which every function in the finite set is invariant on both sides. Then

$$
e_K*f=f=f*e_K.
$$

Thus every finite calculation occurs inside a unital corner although the ambient algebra has no global identity. This is the algebraic reflection of the fact that every finite collection of smooth vectors has a common compact-open stabilizer.

If Haar measure is rescaled by $c$, convolution is multiplied by $c$, while the normalized idempotent $e_K$ is divided by $c$ through its volume. The resulting algebras are canonically isomorphic after the corresponding scalar rescaling. Statements framed through $e_K$ and representation actions do not depend on an unrecorded choice of $\operatorname{vol}(K)=1$.

### 10.3 Involution

When $E=\mathbf C$, the standard involution is

$$
f^*(g)=\Delta_G(g^{-1})\overline{f(g^{-1})}.
$$

The modular factor compensates for inversion changing left Haar measure to right Haar measure. It satisfies

$$
(f_1*f_2)^*=f_2^**f_1^*.
$$

For a unitary representation, integrated operators obey $\pi(f^*)=\pi(f)^*$. If $G$ is unimodular, the formula simplifies to $f^*(g)=\overline{f(g^{-1})}$. Compact opens lie in the kernel of $\Delta_G$, so $e_K^*=e_K$ in all cases.

Over a general coefficient field there may be no distinguished conjugation. One may still use the linear anti-involution $f\mapsto\check f$ with

$$
\check f(g)=\Delta_G(g^{-1})f(g^{-1}),
$$

but it should not be called a Hermitian adjoint without additional structure.

### 10.4 Smooth representations as nondegenerate modules

The action of $\mathcal H(G)$ on a smooth representation is **nondegenerate**: for every $v$ there exists $e_K$ with $e_Kv=v$. Conversely, a nondegenerate $\mathcal H(G)$-module carries a smooth $G$-action, reconstructed from translations and local units. This gives an algebraic avatar of the smooth representation category.

The nonunital qualification matters. An arbitrary module over $\mathcal H(G)$ may contain vectors killed by the whole algebra; such a module does not correspond to a genuine smooth representation unless this degenerate part is excluded.

**Discrete example.** If $G$ is discrete and counting measure is used, $\mathcal H(G)$ is the group algebra $E[G]$, the delta function at $1$ is a global unit, and nondegeneracy is automatic for unital modules.

## 11. Compact-open and spherical Hecke algebras

### 11.1 Compressing convolution to one level

Fix a compact open subgroup $K$. The **compact-open Hecke algebra** is

$$
\mathcal H(G,K)=e_K*\mathcal H(G)*e_K.
$$

It consists of compactly supported bi-$K$-invariant functions. Its identity is $e_K$. If $\operatorname{vol}(K)=1$, this identity is simply $\mathbf1_K$. Calling it a spherical Hecke algebra is especially common when $K$ is a distinguished maximal compact subgroup, but no maximality is needed for the construction.

The characteristic functions of double cosets $KgK$ form a basis. Each double coset is compact because it is the image of $K\times K$ under $(k_1,k_2)\mapsto k_1gk_2$. Its decomposition into right $K$-cosets is finite, with number

$$
[K:K\cap gKg^{-1}].
$$

Consequently products of basis elements are finite linear combinations of basis elements. Their coefficients depend on Haar normalization unless normalized idempotents are used consistently.

The coefficients can be read from intersections. With $\operatorname{vol}(K)=1$, the value of

$$
\mathbf1_{KgK}*\mathbf1_{KhK}
$$

at $x$ is the measure of $KgK\cap xKh^{-1}K$. When nonempty this is a finite union of cosets at a suitable compact-open level. This formula explains simultaneously why the product has finite support and why raw structure constants change when Haar measure is rescaled.

### 11.2 Action on invariant vectors

For every smooth $V$, $\mathcal H(G,K)$ acts on $V^K$: since $f=e_K*f*e_K$, one has $\pi(f)=\pi(e_K)\pi(f)\pi(e_K)$. Thus the image lies in $V^K$ and depends only on the $K$-fixed input.

A useful explicit formula arises when $\operatorname{vol}(K)=1$. If

$$
KgK=\coprod_{i=1}^r g_iK,
$$

then for $v\in V^K$,

$$
\pi(\mathbf1_{KgK})v=\sum_{i=1}^r g_i v.
$$

Changing representatives does not change the sum because $v$ is $K$-fixed. With arbitrary Haar normalization, the right side is multiplied by $\operatorname{vol}(K)$.

**Abelian example.** For $G=F^\times$ and $K=\mathcal O_F^\times$, double cosets are $\varpi^nK$, $n\in\mathbf Z$, and with $\operatorname{vol}(K)=1$,

$$
\mathcal H(G,K)\cong E[T,T^{-1}].
$$

An unramified character gives the one-dimensional module on which $T$ acts by its value at $\varpi$.

### 11.3 Reconstruction and the generated-category boundary

Put $P_K=\mathrm{c\text{-}Ind}_K^G\mathbf1$. Compact Frobenius reciprocity gives

$$
\operatorname{Hom}_G(P_K,V)\cong V^K.
$$

Because compact-open invariants are exact in characteristic zero, $P_K$ is projective. It is not a generator of the entire smooth category: maps out of $P_K$ see exactly the $K$-fixed vectors.

There is a canonical convention-sensitive identification

$$
\mathcal H(G,K)\cong\operatorname{End}_G(P_K)^{\mathrm{op}}.
$$

Why the opposite? An endomorphism $a$ of $P_K$ acts on $\operatorname{Hom}_G(P_K,V)$ by precomposition, $T\mapsto T\circ a$. Composition then reverses order. Concretely, ordinary left convolution of functions identifies $e_K\mathcal H(G)e_K$ with $\operatorname{End}_G(P_K)$ in the same order; the inversion anti-isomorphism

$$
f(g)\longmapsto\Delta_G(g^{-1})f(g^{-1})
$$

then identifies it with the opposite algebra. Under this convention the resulting action on $V^K$ is exactly the left integrated action $f\mapsto\pi(f)$. Passing through the anti-isomorphism is the convention-sensitive step that should not be suppressed.

Let $L_K$ be the tensor functor

$$
L_K(M)=P_K\otimes_{\mathcal H(G,K)}M.
$$

The unit $M\to L_K(M)^K$ is an isomorphism. Consequently $L_K$ is fully faithful, and $V\mapsto V^K$ is an equivalence from the essential image of $L_K$ to left $\mathcal H(G,K)$-modules. Equivalently, this **Hecke-reconstructible subcategory** consists of the smooth representations for which the natural evaluation map

$$
P_K\otimes_{\mathcal H(G,K)}V^K\longrightarrow V
$$

is an isomorphism.

There are two boundaries here. First, if $V^K=0$, the Hecke module is zero even when $V\neq0$, so there is no equivalence with all smooth representations. Second, merely assuming that $V$ is generated by $V^K$ makes the evaluation map surjective but does not make it injective for an arbitrary tdlc group. Its kernel can be a nonzero subrepresentation with no $K$-fixed vectors. Thus a blanket Morita equivalence with every representation generated by $K$-fixed vectors would be false.

The reconstruction exposes the exact role of generation. The space $P_K$ carries a right $\mathcal H(G,K)$-action through the opposite-endomorphism convention. Every object in the essential image is generated by its $K$-fixed vectors, but generation alone supplies only the displayed quotient. If, in a specified full subcategory, subrepresentations of $K$-generated objects are again generated by their $K$-fixed vectors, then the kernel is generated by its zero fixed space and vanishes. Under that additional stability hypothesis the Hecke-reconstructible subcategory is exactly the $K$-generated subcategory. This is the situation furnished by a genuine type theorem; it is additional group-specific structure, not a formal consequence of compactness of $K$.

### 11.4 A finite-group sanity check

Let $G$ be finite and $K\subseteq G$. With counting measure, $e_K=|K|^{-1}\mathbf1_K$. The algebra $e_KE[G]e_K$ acts on $V^K$, and $P_K=E[K\backslash G]$ with the right-translation action. This is exactly the classical permutation-module situation. If $K=\{1\}$, then $P_K=E[G]$ and

$$
\operatorname{End}_G(E[G])^{\mathrm{op}}\cong E[G].
$$

This is the simplest place to see the opposite. Endomorphisms commuting with right translation are left convolutions, while inversion identifies their opposite algebra with the usual group algebra acting on $V$.

## 12. Hecke algebras of types

### 12.1 Why a nontrivial compact type

$K$-fixed vectors detect only the trivial representation of $K$. Ramified representations may have no such vectors but contain a distinguished irreducible $K$-representation $\tau$. Replacing the trivial $K$-type by $\tau$ retains the same architecture while selecting a finer part of the category.

Assume $K$ is compact open and $\tau$ is a finite-dimensional smooth irreducible $E$-representation. Put

$$
P_\tau=\mathrm{c\text{-}Ind}_K^G\tau,
\qquad
\mathcal H(G,\tau)=\operatorname{End}_G(P_\tau)^{\mathrm{op}}.
$$

Then Frobenius reciprocity identifies

$$
\operatorname{Hom}_G(P_\tau,V)
\cong\operatorname{Hom}_K(\tau,V).
$$

Precomposition makes the right side a left $\mathcal H(G,\tau)$-module. The opposite in the definition is therefore forced.

### 12.2 The function model

Write $W_\tau$ for the space of $\tau$. Consider compactly supported functions

$$
\Phi:G\longrightarrow\operatorname{End}_E(W_\tau)
$$

with the bi-equivariance law

$$
\Phi(k_1gk_2)=\tau(k_1)\Phi(g)\tau(k_2)
$$

and convolution

$$
(\Phi_1*\Phi_2)(g)=\int_G
\Phi_1(x)\Phi_2(x^{-1}g)\,dx.
$$

For $f\in P_\tau$, set

$$
(T_\Phi f)(g)=\int_G\Phi(x)f(x^{-1}g)\,dx.
$$

The left $K$-covariance of $\Phi$ makes $T_\Phi f$ satisfy the defining covariance of $P_\tau$, and right translation commutes with $T_\Phi$. A direct double-integral calculation gives

$$
T_{\Phi_1}T_{\Phi_2}=T_{\Phi_1*\Phi_2}.
$$

Every endomorphism arises uniquely this way. The identity function is supported on $K$ and has value $\operatorname{vol}(K)^{-1}\tau(k)$ at $k\in K$. Consequently this function algebra identifies with $\operatorname{End}_G(P_\tau)$; its **opposite**, or the same vector space with reversed convolution, is our $\mathcal H(G,\tau)$.

Other conventions put inverses in the bi-equivariance law by modeling the dual type, or transport reversed convolution through inversion. Such a transport also brings the appropriate modular factor. The endomorphism-opposite definition above is the reference convention against which these formulas should be translated.

### 12.3 Support and intertwining

A function in the type Hecke algebra can be nonzero on $KgK$ only if $g$ intertwines $\tau$. Indeed evaluating bi-equivariance on $K\cap K^g$ forces its value at $g$ to lie in

$$
\operatorname{Hom}_{K\cap K^g}(\tau,\tau^g)
$$

up to the displayed convention. Thus Mackey's intertwining spaces are exactly the possible fibers of the Hecke algebra over double cosets.

If each relevant intertwining space is finite-dimensional and only finitely many relevant double cosets occur in a compact region, convolution is an explicitly finite calculation. If the entire intertwining set is $K$, the algebra is concentrated on the identity double coset and reduces to $\operatorname{End}_K(\tau)^{\mathrm{op}}$.

### 12.4 The type-generated category

Say that $V$ is generated by its $\tau$-isotypic data if the images of all $K$-maps $\tau\to V$ span $V$ under $G$. In characteristic zero, $P_\tau$ is projective because $\operatorname{Hom}_K(\tau,-)$ is exact. The functor

$$
M\longmapsto P_\tau\otimes_{\mathcal H(G,\tau)}M
$$

is fully faithful from left $\mathcal H(G,\tau)$-modules into smooth $G$-representations, and

$$
V\longmapsto\operatorname{Hom}_K(\tau,V)
$$

is its inverse on the essential image. Every representation in that image is generated by its $\tau$-isotypic data. For an arbitrary generated representation, however, the natural evaluation from the tensor reconstruction is only known to be surjective; an invisible kernel can remain. A genuine type theorem supplies the extra assertion that a chosen block is the essential image and hence gives an equivalence with the Hecke-module category. The trivial type recovers Section 11.

The word “type” is sometimes reserved for a pair $(K,\tau)$ detecting an entire block of representations, a much stronger property than merely choosing an irreducible $K$-representation. Here the algebra exists for every such pair; whether it captures a naturally defined block is additional group-specific information.

## 13. Operations on representations

### 13.1 Restriction to open subgroups

Restriction of a smooth $G$-representation to any subgroup $H$ with the subspace topology is smooth: if an open subgroup $K$ fixes a vector, then $K\cap H$ is open in $H$ and fixes it. Closedness is needed when one wants $H$ itself to remain locally compact and Hausdorff, but not for this stabilizer calculation.

Admissibility behaves differently. If $H$ is open and $V$ is admissible as a $G$-representation, then $V|_H$ is admissible: every compact open $J\subseteq H$ is also compact open in $G$. For a nonopen closed subgroup, a compact open of $H$ need not be open in $G$, so $G$-admissibility alone gives no direct bound on its fixed vectors.

Restriction need not preserve irreducibility. A smooth character stays irreducible on every subgroup, but higher-dimensional irreducibles may split. If $H$ is normal, Clifford-theoretic phenomena organize the constituents; if $H$ is merely open, Mackey theory is the appropriate bookkeeping device.

### 13.2 Products and external tensor products

Let $G_1,G_2$ be tdlc groups and $V_i$ a smooth $G_i$-representation. The external tensor product $V_1\boxtimes V_2=V_1\otimes_E V_2$ has action

$$
(g_1,g_2)(v_1\otimes v_2)=g_1v_1\otimes g_2v_2.
$$

It is smooth because a pure tensor is fixed by a product of compact opens, and a finite sum is fixed by their finite intersection in each factor. For compact opens $K_i\subseteq G_i$, characteristic-zero averaging gives

$$
(V_1\boxtimes V_2)^{K_1\times K_2}
\cong V_1^{K_1}\otimes_E V_2^{K_2}.
$$

Hence external tensor products of admissible representations are admissible. Under standard hypotheses, irreducible admissible representations over an algebraically closed field have irreducible external tensor product, and irreducibles of a product arise this way; without field and finiteness hypotheses, division-algebra effects can obstruct this simple statement.

Convolution also factors:

$$
\mathcal H(G_1\times G_2)
\cong\mathcal H(G_1)\otimes_E\mathcal H(G_2),
$$

with product Haar measure, because a compactly supported locally constant function is a finite sum of product functions after subdividing compact opens. The same factorization holds at levels $K_1\times K_2$.

### 13.3 Smooth characters of abelian groups

For an abelian tdlc group $A$, a character $\chi:A\to E^\times$ gives a one-dimensional smooth representation exactly when its kernel is open. If $E$ is algebraically closed and an irreducible smooth representation is admissible, Schur's lemma forces every element of $A$ to act by a scalar, so the representation is such a character.

For $F^\times$, every smooth character has an open kernel on $\mathcal O_F^\times$, hence is determined by a finite-level character of the units and an arbitrary nonzero value at a uniformizer. It is **unramified** when it is trivial on $\mathcal O_F^\times$. For $(F,+)$, smooth characters similarly have open kernel, usually a fractional ideal after a nontrivial additive character has been fixed.

Smoothness must not be confused with analytic continuity into a nondiscrete coefficient field. The representation space is algebraic and discrete for the stabilizer condition. A continuous character with no open kernel need not define a smooth one-dimensional representation.

### 13.4 Central quotients and fixed central character

If a closed central subgroup $Z$ acts trivially on $V$, the action factors through $G/Z$. Conversely a smooth representation of $G/Z$ inflates to one of $G$. If $Z$ acts through a fixed character $\omega$, one can work in the full subcategory of representations with central character $\omega$.

Convolution in a fixed-central-character category is often modeled by functions satisfying

$$
f(zg)=\omega(z)^{-1}f(g)
$$

and compact support modulo $Z$. The inverse ensures that integration against $\pi(g)$ is unchanged when $g$ is replaced by $zg$. Such a function is generally not compactly supported on $G$ if $Z$ is noncompact. Haar measure on $Z\backslash G$ and compatibility of modular characters must then be specified separately. Ordinary $C_c^\infty(G)$ and compact-mod-center Hecke spaces are related but are not the same algebra.

## 14. Four model laboratories

### 14.1 Discrete groups

For a discrete group $\Gamma$, smooth representation theory is ordinary algebraic representation theory. Haar measure is counting measure, $\Delta_\Gamma=1$, and

$$
C_c^\infty(\Gamma,E)=E[\Gamma].
$$

If $K$ is finite, $K$-invariants are exact precisely when $|K|$ is invertible in $E$. Compact induction from a subgroup $H$ consists of functions supported on finitely many left $H$-cosets. If $H$ has finite index, induction and compact induction coincide; if not, they differ.

Take $\Gamma=\mathbf Z$ and $H=\{0\}$. Compact induction is $E[T,T^{-1}]$ as its own regular module. Ordinary induction is the space of all bi-infinite sequences. The first is generated by one vector; the second contains sequences that are not finite linear combinations of translates of a delta sequence. This elementary example catches support mistakes before they become hidden by topology.

### 14.2 Compact profinite groups

Let $K$ be profinite. Every smooth cyclic representation factors through a finite quotient, since the stabilizer of its generator contains an open normal subgroup after taking the core. Over characteristic zero, averaging and finite-group semisimplicity show that every smooth representation is a direct sum of irreducibles in the sense that each finite set of vectors lies in a semisimple finite-dimensional subrepresentation.

Admissibility means finite multiplicity of every irreducible $K$-type. Indeed, for an open normal $J$, the space $V^J$ collects precisely the types factoring through $K/J$; finite dimensionality for all $J$ is equivalent to finite multiplicities together with local finiteness. The smooth contragredient reverses each finite-dimensional irreducible and preserves these multiplicities.

In characteristic $p$, representations of a pro-$p$ group behave very differently. Invariants cease to be exact and extensions need not split. This is not a minor coefficient variation but a change in the homological nature of the category.

### 14.3 The multiplicative group of a local field

Let $G=F^\times$ and $K=\mathcal O_F^\times$. Because $G/K\cong\mathbf Z$, every irreducible admissible smooth representation over an algebraically closed field is a smooth character. The level-zero Hecke algebra is the Laurent polynomial algebra. Its simple modules correspond to choices of the eigenvalue of a uniformizer.

For a smaller compact open $K_m=1+\mathfrak p_F^m$, the quotient $F^\times/K_m$ retains the finite unit quotient $\mathcal O_F^\times/K_m$ as well as the valuation direction. The Hecke algebra is the group algebra of this discrete abelian quotient. Passing from $K$ to $K_m$ therefore makes ramified characters visible.

The additive group gives a complementary picture. For $G=(F,+)$ and $K=\mathcal O_F$, the quotient $F/\mathcal O_F$ is discrete torsion. Since the group is abelian,

$$
\mathcal H(F,\mathcal O_F)\cong E[F/\mathcal O_F]
$$

after normalizing $\operatorname{vol}(\mathcal O_F)=1$. A smooth additive character trivial on $\mathcal O_F$ gives a one-dimensional Hecke module. Shrinking $K$ allows characters with smaller kernels to appear. Thus level measures the kernel of an additive character just as it measures ramification on the unit group multiplicatively.

This example is the local prototype for twisting and central characters. In a nonabelian group with center $F^\times$, the restriction of an irreducible representation to the center produces exactly such a smooth character under Schur's hypotheses.

### 14.4 Elementary matrix groups

Take $G=\operatorname{GL}_2(F)$ and $K=\operatorname{GL}_2(\mathcal O_F)$. The Cartan decomposition, whose detailed consequences belong to the next book, writes $G$ as double cosets represented by diagonal matrices. It already illustrates why $\mathcal H(G,K)$ is manageable: bi-$K$-invariant compact support involves only finitely many such cosets.

Let $B$ be the upper triangular subgroup and let $\chi_1,\chi_2$ be smooth characters of $F^\times$. The unnormalized induced representation consists of smooth functions satisfying

$$
f\left(
\begin{pmatrix}a&b\\0&d\end{pmatrix}g
\right)=\chi_1(a)\chi_2(d)f(g).
$$

The normalized version inserts $|a/d|_F^{1/2}$. This single formula displays all three sources of data: characters from the diagonal, no independent character on the unipotent coordinate, and the half-modular correction. Questions of reducibility, special representations, supercuspidals, conductors, and newvectors are deliberately deferred.

For $G=\operatorname{SL}_2(F)$, the center is finite, so compact support modulo center is the same as compact support up to a finite enlargement. For $\operatorname{GL}_2(F)$ the center is $F^\times$ and noncompact, so the distinction is substantial.

## 15. Admissibility tests and compact induction

### 15.1 Fixed vectors in a compact induction

Let $K,J$ be compact open and $\tau$ finite-dimensional. Decomposing a $J$-fixed compactly induced function by its support gives

$$
(\mathrm{c\text{-}Ind}_K^G\tau)^J
\cong
\bigoplus_{x\in K\backslash G/J}
\tau^{K\cap xJx^{-1}}.
$$

Indeed a function supported on $KxJ$ is determined by its value at $x$, and right $J$-invariance forces that value to be fixed by $K\cap xJx^{-1}$. Each summand is finite-dimensional, but the double-coset set may be infinite and infinitely many summands may be nonzero. Thus compact induction from a finite-dimensional compact type need not be admissible for an arbitrary tdlc group.

For the infinite discrete group with $K=J=\{1\}$, the formula says that the regular representation has one copy of $E$ for every group element. This recovers the earlier counterexample. In reductive $p$-adic settings, admissibility of a particular compact induction requires additional control of which double cosets contribute.

### 15.2 A practical admissibility criterion

The preceding formula yields a direct criterion. If for every compact open $J$ only finitely many double cosets $KxJ$ have

$$
\tau^{K\cap xJx^{-1}}\neq0,
$$

then $\mathrm{c\text{-}Ind}_K^G\tau$ is admissible. The same reasoning applies when $K$ is compact modulo a center after fixing a central character, provided double cosets and support are taken modulo that center.

This separates two logically different issues. Compact induction makes each vector finitely supported. Admissibility asks whether a fixed level can occur in only finitely many support positions. The former is definitional; the latter is a theorem.

### 15.3 Finite length and Hecke modules

Inside the Hecke-reconstructible category of Section 11.3, the equivalence with $\mathcal H(G,K)$-modules translates its intrinsic subobjects and quotients into submodules and quotients. Hence an object has finite length in that category exactly when its $K$-fixed space has finite length as a Hecke module. If a type theorem identifies this category with an exact full block of smooth representations, this is also ordinary representation-theoretic finite length. Without that theorem, an ambient subrepresentation invisible to $K$ can escape the Hecke-module calculation.

An ambient irreducible representation with nonzero $K$-fixed vectors does yield a simple Hecke module: any nonzero fixed vector generates the representation, and averaging its translates generates every other $K$-fixed vector under the Hecke action. The converse needs the stronger reconstruction or type hypothesis. A simple Hecke module produces a simple object in the Hecke-reconstructible category, but its tensor reconstruction can still have an ambient subrepresentation with no $K$-fixed vectors if that category has not been identified with an exact block.

### 15.4 Dual admissibility and central support

For admissible $V$, contragredient duality preserves every fixed-vector dimension and reverses composition series. If $V$ has central character $\omega$, then $V^\vee$ has central character $\omega^{-1}$, since

$$
(z\lambda)(v)=\lambda(z^{-1}v)=\omega(z)^{-1}\lambda(v).
$$

The supports of corresponding matrix coefficients are unchanged under inversion, so compact support modulo center is preserved by contragredience. Twisting by $\chi$ multiplies the coefficient by $\chi(g)$ and also leaves its support unchanged. These elementary observations explain why admissibility, contragredience, central character, and twisting can be transported cleanly across later local correspondences.

## 16. A reusable local dictionary

### 16.1 From congruence level to Hecke module

The general theory may be compressed into a sequence of translations, each with a hypothesis that should remain visible:

$$
\begin{array}{c}
\text{compact open }K\subseteq G\\
\Downarrow\\
\text{averaging idempotent }e_K\\
\Downarrow\\
V^K=e_KV\\
\Downarrow\\
\mathcal H(G,K)=e_K\mathcal H(G)e_K\qquad\text{acts on }V^K.
\end{array}
$$

Over characteristic zero, averaging makes $V\mapsto V^K$ exact. If $V$ is admissible, $V^K$ is finite-dimensional. If $V$ is generated by $V^K$, the Hecke module supplies a canonical surjection from its tensor reconstruction onto $V$. It remembers $V$ completely when that map is also injective, as happens in the Hecke-reconstructible subcategory or in a block controlled by a type theorem. Without generation it remembers only the visible level-$K$ part.

Replacing the trivial $K$-representation by $\tau$ changes the dictionary to

$$
P_\tau=\mathrm{c\text{-}Ind}_K^G\tau,
\qquad
\mathcal H(G,\tau)=\operatorname{End}_G(P_\tau)^{\mathrm{op}},
\qquad
M_\tau(V)=\operatorname{Hom}_K(\tau,V).
$$

This is the form suited to ramified local components. Intertwining spaces determine which double cosets can support the type Hecke algebra, while Mackey decomposition calculates restriction and endomorphisms.

### 16.2 Data carried by a local representation

For a later local component $\pi$ of $\operatorname{GL}_2(F)$ or of a quaternionic multiplicative group, the following data now have unambiguous meanings:

- **smoothness:** every vector has an open stabilizer;
- **level data:** spaces $\pi^K$ or multiplicity spaces $\operatorname{Hom}_K(\tau,\pi)$;
- **admissibility:** all compact-open fixed spaces are finite-dimensional;
- **central character:** scalar action of $Z(G)$ under the stated Schur hypotheses;
- **contragredient:** the smooth part of the algebraic dual, with inverse in the action;
- **Hecke eigenvalues:** the action of a convolution algebra on a fixed-vector or type space;
- **compact-mod-center coefficients:** compactness after projecting support to $Z(G)\backslash G$;
- **twist:** tensoring the action by a smooth character.

None of these terms classifies the representation by itself. Their value is that they are functorial and comparable across different groups.

### 16.3 The $\operatorname{GL}_2(F)$ interface

For $G=\operatorname{GL}_2(F)$, the maximal compact $\operatorname{GL}_2(\mathcal O_F)$ and its congruence subgroups supply levels. The Borel subgroup supplies normalized induction, with relative modulus $|a/d|_F$. The center supplies a smooth character of $F^\times$. The spherical Hecke algebra acts when the maximal-compact fixed space is nonzero, and smaller type Hecke algebras see ramification.

The next layer of theory will decide which induced representations are reducible, identify special and supercuspidal representations, and define conductor and newvector. Those results use the present language but are not consequences of it. In particular, “irreducible,” “admissible,” and “spherical” are structural adjectives, not a classification.

### 16.4 The quaternionic interface

Let $D$ be a quaternion division algebra over $F$. The group $D^\times$ is tdlc, its center is $F^\times$, and $D^\times/F^\times$ is compact. Compact-mod-center support is therefore natural rather than exceptional. Smooth irreducible representations, their central characters, compact-open types, and contragredients all fit the preceding definitions unchanged.

Because the quotient by the center is compact, fixed-central-character representation theory has stronger finiteness properties than an arbitrary tdlc group. Establishing the actual irreducible representations, levels, and conductors still requires the internal structure of $D$ and its orders. The present book supplies only the categorical and harmonic language in which those facts will be expressed.

### 16.5 Local components and restricted products

At almost every finite place of a global automorphic problem, a local representation is expected to contain a vector fixed by a distinguished compact open $K_v$. The restricted-product topology provides the global compact open $K=\prod_vK_v$, while the local representation theory supplies the fixed lines or finite-dimensional fixed spaces. A restricted tensor product of local representations is then built relative to chosen spherical vectors at almost all places.

The word “restricted” plays parallel roles. For groups it means that almost every component lies in $K_v$. For representations it means that almost every tensor factor is anchored by a chosen $K_v$-fixed vector. Neither is the unrestricted product or tensor product. Hecke functions likewise factor as the distinguished identity $e_{K_v}$ at almost all places, making global convolution a finite deviation from the compact tail.

This book does not construct the global automorphic representation, but it now makes the local input precise: smoothness is checked place by place, admissibility makes local invariant spaces finite, and the almost-everywhere spherical condition supplies the restricted tensor reference vectors.

### 16.6 Transfer-compatible operations

A local transfer between representation theories is expected to preserve or predict several operations:

$$
\begin{array}{c|c}
\text{operation or invariant}&\text{general mechanism}\\ \hline
\text{central character}&\text{Schur action of the common center}\\
\text{twist by }\chi&\pi(g)\mapsto\chi(g)\pi(g)\\
\text{contragredient}&(g\lambda)(v)=\lambda(g^{-1}v)\\
\text{level/type}&\operatorname{Hom}_K(\tau,\pi)\\
\text{Hecke action}&\operatorname{End}_G(\mathrm{c\text{-}Ind}_K^G\tau)^{\mathrm{op}}\\
\text{coefficient support}&\operatorname{supp}(g\mapsto\lambda(gv))\\
\text{products}&\boxtimes
\end{array}
$$

The table is not a claim that every transfer preserves every row automatically. It is a checklist of well-defined structures against which a transfer theorem can be tested. Local Jacquet--Langlands, for example, will require group-specific character identities to construct the correspondence, while central characters and twisting can already be stated in this common vocabulary.

## 17. Conclusion: finite level inside an infinite group

Smooth representation theory succeeds because it places finiteness at the level of vectors rather than at the level of the whole group or representation. A vector is controlled by a compact open stabilizer. Averaging over that stabilizer creates an idempotent. The idempotent cuts the convolution algebra down to a unital Hecke algebra, and compact induction supplies its universal generator. Mackey decomposition then explains how these finite-level pieces move across subgroups and double cosets.

The theory also marks its own limits. Smoothness is not admissibility. Compact induction is not automatically admissible or irreducible. Scalar endomorphisms are not by themselves an irreducibility proof in a nonsemisimple category. The algebraic dual is not the smooth contragredient, and biduality needs admissibility. Compact support is not compact support modulo a noncompact center. Ordinary and normalized induction differ by a relative modular character, while ordinary and compact induction differ by support. Finally, a level-$K$ Hecke algebra controls its Hecke-reconstructible category, not every smooth representation; identifying that category with a generated block is the content of an additional type theorem.

With these boundaries in place, the main constructions reinforce one another. Frobenius reciprocity turns invariant or type vectors into maps from compact induction. Mackey theory turns restriction into double-coset intertwiners. Convolution turns locally constant functions into operators. Admissibility turns smooth duality into finite-dimensional duality at every level. Central characters and twisting preserve the data that later transfer theorems must compare.

This is the reusable language required for the next local theories. The specific representation theory of $\operatorname{GL}_2(F)$ will add classification, conductors, and newvectors. The quaternion division group will add compact-mod-center structure arising from orders in $D$. Local and global transfer will add character identities and compatibility theorems. Their common grammar is already complete: a vast nonarchimedean group is read through compact open windows, and each window is encoded by a finite-level Hecke module together with the hypotheses needed to reconstruct the representation behind it.
