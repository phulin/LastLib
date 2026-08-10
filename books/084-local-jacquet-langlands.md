# Local Jacquet--Langlands

## Contents

1. [Two inner forms and one elliptic geometry](#1-two-inner-forms-and-one-elliptic-geometry)
   - [The local comparison problem](#11-the-local-comparison-problem)
   - [Standing notation and a normalization ledger](#12-standing-notation-and-a-normalization-ledger)
   - [What the correspondence can and cannot contain](#13-what-the-correspondence-can-and-cannot-contain)
2. [Regular and elliptic conjugacy classes](#2-regular-and-elliptic-conjugacy-classes)
   - [Characteristic polynomials as common coordinates](#21-characteristic-polynomials-as-common-coordinates)
   - [Split and elliptic elements of $\mathrm{GL}_2(K)$](#22-split-and-elliptic-elements-of-mathrmgl_2k)
   - [Regular elements of $D^\times$](#23-regular-elements-of-dtimes)
   - [The matching-class bijection and its orientation](#24-the-matching-class-bijection-and-its-orientation)
   - [Characteristic two and inseparable quadratic subfields](#25-characteristic-two-and-inseparable-quadratic-subfields)
3. [Centralizers, discriminants, and Haar measures](#3-centralizers-discriminants-and-haar-measures)
   - [Why centralizers determine the Jacobian](#31-why-centralizers-determine-the-jacobian)
   - [The Weyl discriminant in degree two](#32-the-weyl-discriminant-in-degree-two)
   - [Measures on groups, centers, and tori](#33-measures-on-groups-centers-and-tori)
   - [Weyl integration on the elliptic set](#34-weyl-integration-on-the-elliptic-set)
4. [Orbital integrals and matching functions](#4-orbital-integrals-and-matching-functions)
   - [Orbital integrals on the central quotient](#41-orbital-integrals-on-the-central-quotient)
   - [The transfer condition](#42-the-transfer-condition)
   - [Existence of matching functions](#43-existence-of-matching-functions)
   - [Nonuniqueness and the elliptic cocenter](#44-nonuniqueness-and-the-elliptic-cocenter)
5. [Characters and elliptic trace distributions](#5-characters-and-elliptic-trace-distributions)
   - [How much character theory is needed](#51-how-much-character-theory-is-needed)
   - [Trace distributions and regular character functions](#52-trace-distributions-and-regular-character-functions)
   - [Characters of induced and compactly induced representations](#53-characters-of-induced-and-compactly-induced-representations)
   - [The Steinberg sign calculation](#54-the-steinberg-sign-calculation)
6. [Elliptic orthogonality in rank one](#6-elliptic-orthogonality-in-rank-one)
   - [The elliptic pairing](#61-the-elliptic-pairing)
   - [Ordinary orthogonality on $D^\times/K^\times$](#62-ordinary-orthogonality-on-dtimesktimes)
   - [The rank-one elliptic orthogonality theorem](#63-the-rank-one-elliptic-orthogonality-theorem)
   - [Why principal series disappear](#64-why-principal-series-disappear)
7. [Definition and uniqueness of transfer](#7-definition-and-uniqueness-of-transfer)
   - [The character identity and its sign](#71-the-character-identity-and-its-sign)
   - [Uniqueness](#72-uniqueness)
   - [Equivalent trace identity](#73-equivalent-trace-identity)
8. [Existence and bijectivity](#8-existence-and-bijectivity)
   - [The rank-one elliptic trace theorem](#81-the-rank-one-elliptic-trace-theorem)
   - [Construction of the transfer](#82-construction-of-the-transfer)
   - [Exhaustivity, including wild representations](#83-exhaustivity-including-wild-representations)
   - [Independence of auxiliary choices](#84-independence-of-auxiliary-choices)
9. [The first structural consequences](#9-the-first-structural-consequences)
   - [Norm characters and twists of Steinberg](#91-norm-characters-and-twists-of-steinberg)
   - [Higher-dimensional representations and supercuspidals](#92-higher-dimensional-representations-and-supercuspidals)
   - [Central characters and twisting](#93-central-characters-and-twisting)
   - [Contragredients](#94-contragredients)
10. [Conductors and compact-open level](#10-conductors-and-compact-open-level)
    - [The two level scales](#101-the-two-level-scales)
    - [The exact conductor comparison](#102-the-exact-conductor-comparison)
    - [Newvectors and division-side invariants](#103-newvectors-and-division-side-invariants)
    - [Cancellation under ramified twists](#104-cancellation-under-ramified-twists)
11. [Formal degrees](#11-formal-degrees)
    - [A compatible pair of quotient measures](#111-a-compatible-pair-of-quotient-measures)
    - [The formal-degree identity](#112-the-formal-degree-identity)
    - [Checks in the special and tame families](#113-checks-in-the-special-and-tame-families)
12. [Local factors](#12-local-factors)
    - [Zeta integrals on the two degree-two algebras](#121-zeta-integrals-on-the-two-degree-two-algebras)
    - [Fourier transform and the functional equation](#122-fourier-transform-and-the-functional-equation)
    - [Compatibility of $L$- and epsilon factors](#123-compatibility-of-l--and-epsilon-factors)
    - [Explicit shapes and conductor numbering](#124-explicit-shapes-and-conductor-numbering)
13. [Tame admissible pairs](#13-tame-admissible-pairs)
    - [One quadratic datum on both sides](#131-one-quadratic-datum-on-both-sides)
    - [The unramified quadratic case](#132-the-unramified-quadratic-case)
    - [The ramified quadratic case](#133-the-ramified-quadratic-case)
    - [Regularity, minimality, and rectification](#134-regularity-minimality-and-rectification)
14. [Worked examples over $\mathbf Q_p$](#14-worked-examples-over-mathbf-q_p)
    - [Unramified norm characters](#141-unramified-norm-characters)
    - [A level-zero correspondence](#142-a-level-zero-correspondence)
    - [A positive-depth unramified example](#143-a-positive-depth-unramified-example)
    - [A tame ramified example and the dyadic boundary](#144-a-tame-ramified-example-and-the-dyadic-boundary)
15. [Scalar symmetries](#15-scalar-symmetries)
    - [Unramified twists](#151-unramified-twists)
    - [Automorphisms of the coefficient field](#152-automorphisms-of-the-coefficient-field)
    - [Changing the additive character](#153-changing-the-additive-character)
16. [The precise image and the missing representations](#16-the-precise-image-and-the-missing-representations)
    - [Essentially square-integrable representations](#161-essentially-square-integrable-representations)
    - [Why irreducible principal series are absent](#162-why-irreducible-principal-series-are-absent)
    - [Boundary phenomena at reducibility](#163-boundary-phenomena-at-reducibility)
17. [The local dictionary for global transfer](#17-the-local-dictionary-for-global-transfer)
    - [The transfer table](#171-the-transfer-table)
    - [What Book 94 may use](#172-what-book-94-may-use)
    - [Conclusion](#173-conclusion)

## 1. Two inner forms and one elliptic geometry

### 1.1 The local comparison problem

Books 77 and 82 developed two representation theories that look almost opposite. The group

$$
G=\mathrm{GL}_2(K)
$$

has a Borel subgroup, principal series, an infinite lattice tree, and infinite-dimensional irreducible representations. The multiplicative group

$$
G'=D^\times
$$

of the quaternion division algebra has no proper parabolic subgroup, is compact modulo its center, and has only finite-dimensional irreducible representations. Yet the two groups are forms of the same degree-two multiplicative group. After a quadratic field splits $D$, both become matrix groups. The local Jacquet--Langlands correspondence identifies the part of their representation theories that survives this change of form.

The point of contact is not the whole of $G$. Split diagonal matrices have no analogue in $D^\times$: a division algebra contains no nontrivial idempotent and hence no split quadratic torus. The common geometry consists of elliptic regular elements. Such an element generates a separable quadratic field over $K$, and every separable quadratic field embeds in both $M_2(K)$ and $D$. Its characteristic polynomial, centralizer, and Weyl discriminant can therefore be read on either side. The word separable matters in characteristic two and will remain visible throughout.

That observation suggests a program.

1. Match regular elliptic conjugacy classes by characteristic polynomial.
2. Match test functions by their orbital integrals on those classes.
3. Compare trace distributions through character functions.
4. Use elliptic orthogonality to show that the comparison pairs irreducibles, rather than arbitrary virtual representations.

The fourth step is the heart of the theorem. Equality of a few numerical invariants cannot define a correspondence: many inequivalent representations share a central character and conductor. Nor may the character identity simply be announced and then used to prove itself. We shall derive it from a rank-one elliptic trace calculation, whose split side is governed by the tree and whose anisotropic side is ordinary character theory on a compact quotient.

### 1.2 Standing notation and a normalization ledger

Let $K$ be a nonarchimedean local field, of arbitrary characteristic, with

$$
\mathcal O=\mathcal O_K,\qquad \mathfrak p=(\varpi),\qquad
k=\mathcal O/\mathfrak p,\qquad |k|=q,
$$

and $|\varpi|=q^{-1}$. Let $D$ be the quaternion division algebra over $K$. We write

$$
Z=K^\times
$$

for the common center, embedded as scalar matrices in $G$ and scalar quaternions in $G'$. On $G$ the determinant is denoted $\det$; on $G'$ the reduced norm is denoted $\operatorname{Nrd}$. On scalars both equal $z^2$.

The coefficient field $C$ is algebraically closed, uncountable, and of characteristic zero, as in Book 77. The uncountability hypothesis ensures that irreducible admissible representations have scalar central character. For arguments involving positivity and Hermitian orthogonality we first take $C=\mathbf C$ and unitary central characters; the character identity then gives the algebraic correspondence over characteristic-zero coefficient fields by scalar extension and descent. All representations and characters are smooth.

The following choices remain fixed.

- Group measures are left Haar measures. On
  $\bar G=G/Z$ we impose
  $\operatorname{vol}(\mathrm{PGL}_2(\mathcal O))=1$.
- On $\bar G'=D^\times/Z$ we impose

  $$
  \operatorname{vol}(\bar G')=\frac{2}{q-1}.
  $$

  This is the measure compatible with the preceding split measure for formal degrees.
- For every separable quadratic extension $E/K$, the quotient $E^\times/K^\times$ receives the Haar measure for which

  $$
  \operatorname{vol}(\mathcal O_E^\times/\mathcal O^\times)=1.
  $$
- We fix an additive character $\psi:K\to C^\times$ trivial on $\mathcal O$ and nontrivial on $\varpi^{-1}\mathcal O$, and take the self-dual additive measure on $K$. Measures on $M_2(K)$ and $D$ are self-dual for the trace pairings introduced in Chapter 12.
- Normalized induction on $G$ uses $|a/d|^{1/2}$ for the upper Borel, exactly as in Book 77.
- The Steinberg representation is

  $$
  \operatorname{St}=I(|\cdot|^{-1/2},|\cdot|^{1/2})/\mathbf1.
  $$

These choices are not all consequences of one another. Torus measures define quotient measures in orbital integrals; the two group measures define formal degrees; the self-dual additive measures define epsilon factors. Keeping the ledger visible prevents an equality valid for one purpose from being silently transported into another normalization.

### 1.3 What the correspondence can and cannot contain

An irreducible representation of $G$ is **essentially square-integrable** if a twist by a character of the determinant has square-integrable matrix coefficients modulo $Z$. In rank one these are exactly

$$
\operatorname{St}\otimes(\mu\circ\det)
\quad\text{and the supercuspidal representations.}
$$

We also call them the discrete-series representations, allowing nonunitary twists. Every irreducible representation of $D^\times$ is essentially square-integrable because $D^\times/Z$ is compact.

The theorem to be proved is a bijection

$$
\operatorname{JL}:
\operatorname{Irr}(D^\times)
\xrightarrow{\sim}
\operatorname{Irr}_{\mathrm{disc}}(\mathrm{GL}_2(K)).
$$

It will not contain an irreducible principal series. It will not contain a one-dimensional representation of $G$. The apparently paradoxical fact that a one-dimensional representation of $D^\times$ maps to an infinite-dimensional Steinberg twist is not a defect: dimension is not invariant under changing the inner form. What is preserved is the elliptic character, with the sign dictated by the difference of split ranks.

A useful counterexample to any broader guess is an unramified irreducible principal series $I(\chi_1,\chi_2)$. It has a spherical vector and two Satake parameters. No higher-dimensional representation of $D^\times$ has an $\mathcal O_D^\times$-fixed vector, and a norm character has only one unramified parameter. There is no possible member on the division side carrying the principal series' split-torus data.

## 2. Regular and elliptic conjugacy classes

### 2.1 Characteristic polynomials as common coordinates

The first obstacle to comparing two different groups is deciding which elements represent the same geometric event. Both groups sit inside central simple algebras of degree two, so trace and determinant provide a common coordinate system.

For $g\in G$, put

$$
P_g(X)=X^2-\operatorname{tr}(g)X+\det(g).
$$

For $d\in D^\times$, put

$$
P_d(X)=X^2-\operatorname{Trd}(d)X+\operatorname{Nrd}(d).
$$

In either case define the polynomial discriminant

$$
\delta(x)=\operatorname{trd}(x)^2-4\operatorname{nrd}(x),
$$

where lower-case notation means ordinary or reduced invariants as appropriate. An element is **regular semisimple** when $P_x$ has two distinct roots over a separable closure. Equivalently, $K[x]$ is a quadratic étale $K$-algebra and the centralizer has minimal dimension two.

The adjective regular is essential. A scalar has polynomial $(X-z)^2$ and centralizer the whole group. In characteristic two an irreducible inseparable quadratic polynomial also has zero derivative; its root generates a field, but the corresponding element is not geometrically semisimple. Such elements will be treated at the boundary in Section 2.5.

### 2.2 Split and elliptic elements of $\mathrm{GL}_2(K)$

For regular semisimple $g\in G$, the algebra $K[g]$ is either

$$
K\times K
\quad\text{or a separable quadratic field }E.
$$

In the first case $g$ is conjugate over $K$ to a diagonal matrix with distinct entries; it is **split regular**. In the second it is **elliptic regular**. The word elliptic means precisely that the centralizer modulo $Z$ is compact. Indeed

$$
G_g=K[g]^\times,
$$

and $E^\times/K^\times$ is compact for a quadratic field, whereas $(K^\times\times K^\times)/K^\times\cong K^\times$ is not.

There is a concrete model. If

$$
P(X)=X^2-tX+n
$$

is irreducible and separable, then its companion matrix

$$
g_P=\begin{pmatrix}0&-n\\1&t\end{pmatrix}
$$

is elliptic regular and has polynomial $P$. Every matrix with polynomial $P$ is conjugate to $g_P$: a cyclic vector $v$ makes $(v,gv)$ a basis, and the Cayley--Hamilton relation gives the companion matrix. Thus a separable irreducible characteristic polynomial determines one $G$-conjugacy class, not merely a stable class.

### 2.3 Regular elements of $D^\times$

If $d\in D^\times$ is regular semisimple, then

$$
E=K[d]
$$

is a separable quadratic field. It cannot be $K\times K$, since that algebra has a nontrivial idempotent and cannot embed in a division algebra. Its centralizer is

$$
G'_d=E^\times.
$$

To see the equality, note that $E$ is a maximal commutative subfield of the four-dimensional central simple algebra. The centralizer dimension formula gives dimension two, so nothing larger than $E$ can centralize $d$.

Two regular elements $d_1,d_2\in D^\times$ are conjugate if and only if $P_{d_1}=P_{d_2}$. Equality of polynomials gives an isomorphism $K[d_1]\to K[d_2]$ carrying $d_1$ to $d_2$. Conjugacy of embeddings of a separable maximal subfield into a central simple algebra then supplies an element of $D^\times$ realizing that isomorphism. This is the division-side counterpart of the companion-matrix argument.

Every separable quadratic field embeds in $D$. Indeed scalar extension to such a field multiplies the local invariant $1/2$ of $D$ by two and therefore splits $D$; the degree-two embedding criterion then gives the embedding. Hence every separable irreducible quadratic polynomial with nonzero constant term occurs as $P_d$ for some $d\in D^\times$. The division algebra has discarded the split polynomials and retained exactly the elliptic ones.

### 2.4 The matching-class bijection and its orientation

We say that elliptic regular $g\in G$ and regular semisimple $d\in D^\times$ **match**, and write

$$
g\leftrightarrow d,
$$

if

$$
P_g=P_d.
$$

Equivalently,

$$
\operatorname{tr}(g)=\operatorname{Trd}(d),\qquad
\det(g)=\operatorname{Nrd}(d).
$$

The preceding sections prove that this defines a bijection

$$
\{\text{elliptic regular classes in }G\}
\longleftrightarrow
\{\text{regular semisimple classes in }D^\times\}.
$$

There is no hidden choice of a root. If $E/K$ is the common quadratic field and $\sigma$ its nontrivial automorphism, then $t$ and $\sigma(t)$ have the same polynomial and are conjugate on both sides. In $M_2(K)$ the conjugating element exchanges the two embeddings of $E$; in $D$ it lies in the nontrivial coset of the normalizer of $E^\times$. Thus choosing an embedding $E\hookrightarrow M_2(K)$ or $E\hookrightarrow D$ does not orient the two roots.

Our orientation is instead the ordered pair of invariants

$$
(\operatorname{trace},\operatorname{norm}).
$$

We do not replace $d$ by $d^{-1}$, conjugate its polynomial, or negate its trace. Consequently

$$
g^{-1}\leftrightarrow d^{-1},\qquad
zg\leftrightarrow zd,\qquad
\det(g)=\operatorname{Nrd}(d).
$$

These elementary compatibilities later force the formulas for contragredients, central characters, and twists.

**Worked example.** Let $E/K$ be unramified quadratic and let $u\in\mathcal O_E^\times$ have residue outside $k$. Multiplication by $u$ on the $K$-space $E$ gives an elliptic matrix $g_u$. Regard the same $u$ in the fixed unramified maximal subfield of $D$. Then

$$
g_u\leftrightarrow u,\qquad
P(X)=X^2-\operatorname{Tr}_{E/K}(u)X+N_{E/K}(u).
$$

Replacing $u$ by $u^q$ changes neither conjugacy class. By contrast, a diagonal matrix $\operatorname{diag}(a,b)$ with $a\ne b$ has split polynomial and matches no element of $D^\times$.

### 2.5 Characteristic two and inseparable quadratic subfields

When $\operatorname{char}K=2$, a quaternion division algebra can contain purely inseparable quadratic fields. If $d$ generates such a field, its minimal polynomial has the form

$$
X^2-a
$$

and derivative zero. The element is noncentral and its algebraic centralizer is still a quadratic field, but it is not regular semisimple in the sense required by Weyl integration or local character theory. A companion matrix with the same polynomial exists, but it too is nonsemisimple over an algebraic closure. We therefore do not declare these elements to be matching regular classes.

This exclusion creates no hole in the correspondence. The regular semisimple locus is open and dense on both sides. Character functions of admissible representations are locally constant there and their distributions are determined by that dense regular locus. Inseparable elements have discriminant zero and lie outside every orbital-integral formula below. A statement that “every noncentral quaternion is regular” is valid in characteristic different from two and false in characteristic two; none of our proofs uses it.

## 3. Centralizers, discriminants, and Haar measures

### 3.1 Why centralizers determine the Jacobian

A conjugacy class is not integrated with the ambient group measure directly. It is the homogeneous space

$$
G_x\backslash G,
$$

so its measure depends on the centralizer. When a class is parameterized by trace and determinant, the change of variables from elements to invariants degenerates where two eigenvalues collide. The Weyl discriminant measures precisely this degeneration.

For a regular element $x$ in either algebra, put $T_x=K[x]^\times$. On matching classes the two centralizers are canonically the same abstract torus $E^\times$. This is stronger than equality of dimensions: it lets us use one Haar measure $dt$ on $E^\times/K^\times$ on both sides. The remaining quotient measures are defined by

$$
d\bar g=dt\,d\dot g,\qquad
d\bar d=dt\,d\dot d,
$$

on $T\backslash G$ and $T\backslash D^\times$, with all groups divided by the common center. This convention fixes orbital integrals exactly.

### 3.2 The Weyl discriminant in degree two

Define

$$
D(x)=\left|\det\left(1-\operatorname{Ad}(x)\mathrel{\big|}
\mathfrak a/\mathfrak t_x\right)\right|,
$$

where $\mathfrak a=M_2(K)$ on the split side and $\mathfrak a=D$ on the division side. Scalars cancel, so the same formula is obtained on the adjoint Lie algebra.

If the roots of $P_x$ are $\alpha,\beta$, then conjugation on the two root directions has eigenvalues $\alpha/\beta$ and $\beta/\alpha$. Therefore

$$
D(x)=\left|(1-\alpha/\beta)(1-\beta/\alpha)\right|
=\left|\frac{(\alpha-\beta)^2}{\alpha\beta}\right|
=\left|\frac{\delta(x)}{\operatorname{nrd}(x)}\right|.
$$

This expression belongs to $K$ and makes matching immediate:

$$
g\leftrightarrow d\quad\Longrightarrow\quad D(g)=D(d).
$$

Some authors call $D(x)^{1/2}$ the Weyl factor and some call $D(x)$ the Weyl discriminant. We use **Weyl discriminant** for $D(x)$ and always display the square root when one is intended. Orbital integrals below are unnormalized; their normalized versions are $D(x)^{1/2}O_x(f)$.

**Sanity check.** For $g=\operatorname{diag}(a,b)$ with $a\ne b$,

$$
D(g)=\left|\frac{(a-b)^2}{ab}\right|.
$$

The same algebraic formula holds for elliptic roots in a quadratic extension. It approaches zero as the class approaches the center, exactly where regular coordinates cease to be valid.

### 3.3 Measures on groups, centers, and tori

For a central character $\omega$, it is cleaner to integrate on the central quotient than to choose a divergent measure on $Z$. Let

$$
\mathcal H(G,\omega)
$$

be the space of locally constant functions $f:G\to C$ satisfying

$$
f(zg)=\omega(z)^{-1}f(g)
$$

and having compact support modulo $Z$. Define $\mathcal H(G',\omega)$ similarly. Then

$$
\pi(f)=\int_{G/Z}f(g)\pi(g)\,d\bar g
$$

is well defined on a representation with central character $\omega$. The inverse on $\omega$ in the function law is forced: replacing $g$ by $zg$ multiplies $f(g)$ and $\pi(g)$ by inverse scalars.

For each separable quadratic $E/K$, normalize $E^\times/K^\times$ by volume one on $\mathcal O_E^\times/\mathcal O^\times$. This prescription works in both ramified and unramified cases. It does not say that the full quotient has volume one. In fact the valuation quotient has size

$$
[\mathbf Z:e(E/K)\mathbf Z]=e(E/K),
$$

so

$$
\operatorname{vol}(E^\times/K^\times)=e(E/K).
$$

Thus it is $1$ for an unramified quadratic extension and $2$ for a ramified one. This small distinction is easy to lose and affects every unnormalized torus integral.

### 3.4 Weyl integration on the elliptic set

Choose one representative of each $K$-isomorphism class of separable quadratic extensions $E/K$ and embeddings into each algebra. For a compactly supported function $F$ on the elliptic regular set of $G/Z$, Weyl integration reads

$$
\int_{G_{\mathrm{ell}}/Z}F(g)\,d\bar g
=\frac12\sum_E
\int_{E^\times/K^\times}
D(t)\int_{E^\times\backslash G}F(x^{-1}tx)\,d\dot x\,dt.
$$

For $G'$ every regular semisimple class is elliptic, and

$$
\int_{G'_{\mathrm{reg}}/Z}F(d)\,d\bar d
=\frac12\sum_E
\int_{E^\times/K^\times}
D(t)\int_{E^\times\backslash G'}F(x^{-1}tx)\,d\dot x\,dt.
$$

The factor $1/2$ is the order of the rational Weyl group

$$
N(E^\times)/E^\times=\{1,\sigma\}.
$$

It occurs on both sides. Omitting it counts $t$ and $\sigma(t)$ separately even though they are conjugate.

In equal characteristic two there are infinitely many isomorphism classes of separable quadratic extensions. The displayed sum is therefore not to be read as a finite classification list. For a compact subset of the regular locus only finitely many bounded-ramification torus charts contribute. For functions or characters whose support reaches the singular boundary, the formula is obtained by exhaustion, and the sum is absolutely convergent after multiplication by $D(t)$. This is also the interpretation used in the elliptic pairing below.

**Proof strategy.** Cover the regular set by conjugation charts

$$
(E^\times\backslash G)\times E^\times_{\mathrm{reg}}
\longrightarrow G_{\mathrm{ell}},\qquad (x,t)\mapsto x^{-1}tx.
$$

The differential in the orbit direction is $1-\operatorname{Ad}(t)$, so its absolute determinant is $D(t)$. The generic fiber has two points, related by the Weyl involution. Partition of unity on compact-open charts gives the formula. The same differential calculation takes place in $D$, and matching identifies the determinant. This proof also shows why inseparable elements, where the differential is singular, are excluded.

## 4. Orbital integrals and matching functions

### 4.1 Orbital integrals on the central quotient

For regular $x$ and a test function $f$ with the appropriate central transformation law, define the unnormalized orbital integral

$$
O_x(f)=\int_{T_x\backslash G}f(y^{-1}xy)\,d\dot y
$$

on the split side, and

$$
O_x'(f')=\int_{T_x\backslash G'}f'(y^{-1}xy)\,d\dot y
$$

on the division side. The quotient is understood after dividing both numerator and denominator by $Z$; the central covariance makes the formula independent of representatives.

The normalized orbital integrals are

$$
I_x(f)=D(x)^{1/2}O_x(f),\qquad
I_x'(f')=D(x)^{1/2}O_x'(f').
$$

Because matching preserves $D(x)$, equality of normalized orbital integrals is equivalent to equality of unnormalized ones under our common torus measures. We shall state transfer using the unnormalized version. This choice leaves the Weyl discriminant visible in the trace formula instead of hiding half of it in each orbital integral.

Orbital integrals are locally constant as functions of the regular conjugacy class. This follows from the conjugation charts used in Weyl integration: on a sufficiently small compact-open neighborhood, both the test function and the quotient fibers are constant at finite level. They need not extend locally constantly through the singular set; the factor $D^{1/2}$ is what controls their typical singular behavior there.

### 4.2 The transfer condition

Functions $f\in\mathcal H(G,\omega)$ and $f'\in\mathcal H(G',\omega)$ **match** if

$$
O_g(f)=O_d'(f')
$$

whenever $g\leftrightarrow d$, and

$$
O_g(f)=0
$$

for every split regular $g\in G$.

The second clause is indispensable when transferring from the anisotropic side to the full split group: there is no division-side class to supply a value on a split torus. Conversely, when starting with an arbitrary $f$ on $G$, a matching $f'$ is required to reproduce only its elliptic orbital integrals; no condition can remember the split orbital integrals of $f$. It is therefore useful to distinguish two directions:

- every $f'$ has an **elliptic lift** $f$ whose split regular orbital integrals vanish;
- every $f$ has a **division transfer** $f'$ reproducing its elliptic orbital integrals.

The lift is nonunique, and a general $f$ is not recovered from its transfer. Transfer lives in an elliptic quotient of the test-function space.

No sign occurs in this definition. Matching classes and orbital integrals use transfer factor $+1$ for these inner forms. The sign $-1$ belongs to the spectral character identity, not to geometry. Putting a minus sign into both definitions would conceal rather than remove the convention.

### 4.3 Existence of matching functions

**Proposition 4.1 (smooth transfer in degree two).** Every test function on either side has a match in the sense appropriate to its direction. If the original function is supported in a sufficiently small saturated neighborhood of one regular class, the match may be supported in an arbitrarily small corresponding regular neighborhood.

**Proof strategy.** First solve the problem near one regular class using the conjugation submersion. Then patch compact-open neighborhoods in the invariant quotient. The difficult point is support approaching discriminant zero: there one must compare the rank-one orbital germs, including the central germ, and not merely extend a regular orbital-integral function by zero.

**Proof.** Fix $g\leftrightarrow d$ with common torus $E^\times$. Choose small compact-open neighborhoods $U\subset E^\times_{\mathrm{reg}}$ stable under $\sigma$ and small transverse neighborhoods $V,V'$ in the two quotient spaces. The maps

$$
V\times U\to G,\qquad V'\times U\to G'
$$

given by conjugation are local analytic isomorphisms modulo the common two-element Weyl action. Their Jacobians differ only through the quotient measures, already fixed by the same $dt$; the variable part is the common $D(t)$.

Start with a locally constant function $h(t)$ on $U/\{1,\sigma\}$. Choose characteristic functions on sufficiently small $V$ and $V'$ and scale them so their quotient integrals are one. Extending by zero produces functions $f_U,f_U'$ with

$$
O_t(f_U)=h(t)=O_t'(f_U')
$$

for $t\in U$, and zero orbital integrals outside the chosen saturated neighborhoods. Thus every compactly supported locally constant class function on a small regular-class chart is realized on both sides.

Away from discriminant zero, compactness modulo the center reduces the required invariant support to finitely many such charts. Near a scalar $z$, filter both algebras by lattices $z+\mathfrak p^rM_2(\mathcal O)$ and $z+\mathfrak P_D^r$. On each finite quotient, conjugation descent expresses an orbital integral as a central germ plus regular torus germs. The central germs agree because the scalar algebra and the chosen central measure are common. On the split side there is one additional split germ. Subtracting its finite-level characteristic function kills it without altering the elliptic germs. Passing compatibly through the lattice filtration constructs a division transfer or an elliptic lift.

Two details prevent circularity. The finite-level germ calculation concerns conjugacy orbits and Fourier sums only; it uses no representation character. Also, in characteristic two the filtration is restricted to separable regular strata. Inseparable strata lie in discriminant zero, and their contribution is absorbed into the singular germ rather than being declared a regular torus. Thus the construction proves smooth transfer before any irreducible correspondence is defined. $\square$

The proposition does not assert equality of functions at matching elements. Such an equality would depend on embeddings and is not conjugacy invariant. Orbital integrals are exactly the amount of averaging needed to compare the two groups canonically.

### 4.4 Nonuniqueness and the elliptic cocenter

Let $[\mathcal H(G,\omega),\mathcal H(G,\omega)]$ denote the span of convolution commutators. Every trace distribution kills this span. We further quotient by functions whose elliptic regular orbital integrals vanish and call the result the **elliptic cocenter**

$$
\overline{\mathcal H}_{\mathrm{ell}}(G,\omega).
$$

On the division side the analogous cocenter is simply the class-function quotient relevant to the compact central quotient. Proposition 4.1 gives a canonical isomorphism

$$
\mathcal T:
\overline{\mathcal H}_{\mathrm{ell}}(G,\omega)
\xrightarrow{\sim}
\overline{\mathcal H}(G',\omega)
$$

characterized by equality of regular orbital integrals.

This is the correct home of function transfer. Choosing representatives $f$ and $f'$ is useful for calculation but not canonical. If two split functions have the same elliptic orbital integrals, every discrete-series character gives them the same trace; principal-series traces may distinguish them because principal series also see split classes. The spectral theorem in Chapter 6 will prove the first assertion rather than assume it.

## 5. Characters and elliptic trace distributions

### 5.1 How much character theory is needed

The representation of $D^\times$ attached to an admissible pair has an ordinary finite-dimensional matrix trace. A representation of $G$, however, is usually infinite dimensional, so $g\mapsto\operatorname{tr}\pi(g)$ makes no sense. Test functions repair the problem: admissibility makes $\pi(f)$ finite rank, and its trace defines a distribution.

We need only the following rank-one character theorem.

**Theorem 5.1 (regular character theorem).** If $\pi$ is an irreducible admissible representation of $G$, its trace distribution is represented by a locally integrable conjugation-invariant function on $G$. Its restriction $\Theta_\pi$ to $G_{\mathrm{reg}}$ is locally constant, and

$$
\operatorname{tr}\pi(f)=\int_{G/Z}\Theta_\pi(g)f(g)\,d\bar g
$$

for every compact-mod-center $f$ with the inverse central transformation law. The representing function is unique almost everywhere, and its locally constant restriction is uniquely determined pointwise on the regular set. For $D^\times$, $\Theta_\rho(d)=\operatorname{tr}\rho(d)$ everywhere and represents the trace distribution directly.

**Proof strategy.** Finite rank of $\pi(f)$ supplies a trace distribution, but by itself does not prove that the distribution is represented by a function. The decisive step is semisimple descent along the conjugation submersion. In rank one its transverse space is one dimensional, so Fourier analysis on finite lattice quotients gives local constancy away from discriminant zero and the required bound at the boundary.

**Proof.** Fix a regular element $x$ with torus centralizer $T$. Choose a small compact-open slice $S$ through $x$ on which

$$
(T\backslash G)\times S\longrightarrow G,
\qquad (\dot y,s)\longmapsto y^{-1}sy,
$$

is a submersion modulo the two-element Weyl action. Pull the invariant trace distribution back to this chart and integrate first in the orbit direction. Admissibility makes every averaging operator at a fixed lattice level finite rank. On the transverse one-dimensional quotient, Fourier inversion on successive finite lattices shows that the descended distribution is integration against a locally constant function on $S\cap G_{\mathrm{reg}}$. The same calculation gives the rank-one bound

$$
D(s)^{1/2}|\Theta_\pi(s)|\le C_S
$$

on compact parts of the slice; this is the estimate needed when a slice approaches the singular locus. It proves local integrability across discriminant zero, whose complement has measure zero. Compatible slices glue because two representatives of the same invariant distribution agree on their overlap. Uniqueness follows from characteristic functions of arbitrarily small regular neighborhoods. On $D^\times$, finite dimensionality gives the ordinary matrix trace, and the same descent identifies its restriction with the distributional representative. $\square$

The theorem does not claim local constancy at singular elements. Characters typically have controlled singularities near the center. All identities defining transfer are therefore asserted on regular elliptic elements, where they have an unambiguous pointwise meaning.

### 5.2 Trace distributions and regular character functions

For a representation with central character $\omega$, write

$$
\Theta_\pi(f)=\operatorname{tr}\pi(f).
$$

The same symbol for the distribution and its regular function causes no ambiguity when the argument is displayed. Conjugation invariance follows from

$$
\pi({}^xf)=\pi(x)\pi(f)\pi(x)^{-1}.
$$

Twisting and contragredience already have visible character formulas:

$$
\Theta_{\pi\otimes\chi}(g)=\chi(\det g)\Theta_\pi(g),
\qquad
\Theta_{\pi^\vee}(g)=\Theta_\pi(g^{-1}),
$$

and on $D^\times$ the determinant is replaced by reduced norm. No complex conjugation belongs in the algebraic contragredient formula. For a unitary realization one may additionally identify $\Theta_{\pi^\vee}(g)$ with $\overline{\Theta_\pi(g)}$.

If $g\leftrightarrow d$, then

$$
\chi(\det g)=\chi(\operatorname{Nrd}d).
$$

Thus any character identity on matching classes is automatically stable under corresponding twists. Likewise $g^{-1}\leftrightarrow d^{-1}$ makes it stable under contragredients. These consequences require no new harmonic analysis once the orientation of Section 2.4 has been fixed.

### 5.3 Characters of induced and compactly induced representations

Character formulas reveal why elliptic classes isolate the desired spectrum. If $\pi=I(\chi_1,\chi_2)$ is a normalized principal series and $g$ is regular, its character is a sum over fixed points of $g$ on $G/B\cong\mathbf P^1(K)$. A split regular element has two $K$-rational eigenlines and contributes two terms. An elliptic element has no $K$-rational eigenline, hence

$$
\Theta_{I(\chi_1,\chi_2)}(g)=0
\qquad(g\text{ elliptic regular}).
$$

One can prove this without a general fixed-point formula. Realize the induction as functions on $B\backslash G$. At a finite compact-open level, the trace of $g$ counts cosets fixed by right translation, weighted by the inducing character. A fixed coset is exactly a $K$-rational line stabilized by $g$. There are none in the elliptic case.

For $\rho=\operatorname{c\text{-}Ind}_J^{D^\times}\Lambda$, finite index gives

$$
\Theta_\rho(d)=
\sum_{\substack{x\in J\backslash D^\times\\xdx^{-1}\in J}}
\operatorname{tr}\Lambda(xdx^{-1}).
$$

The same formula holds for compactly induced supercuspidals of $G$ on regular elements, with a finite sum because the coefficient support is compact modulo $Z$. These formulas will make tame transfer explicit. In the wild range they remain valid once the abstract Clifford datum supplies the finite inducing representation.

### 5.4 The Steinberg sign calculation

The sign in Jacquet--Langlands can already be read at the reducible principal series. The exact sequence of Book 77 is

$$
0\longrightarrow \mu\circ\det\longrightarrow
I(\mu|\cdot|^{-1/2},\mu|\cdot|^{1/2})
\longrightarrow \operatorname{St}\otimes\mu\longrightarrow0.
$$

Trace distributions are additive in exact sequences. On an elliptic regular $g$, the middle character vanishes by Section 5.3. Therefore

$$
\Theta_{\operatorname{St}\otimes\mu}(g)
=-\mu(\det g).
$$

On the division side the norm character $\rho=\mu\circ\operatorname{Nrd}$ has

$$
\Theta_\rho(d)=\mu(\operatorname{Nrd}d).
$$

Thus matching elements satisfy

$$
\Theta_{\operatorname{St}\otimes\mu}(g)=-\Theta_\rho(d).
$$

This calculation fixes the sign once and for all. It is not a convention that may be changed independently after Steinberg has been normalized. Had we put a minus sign into geometric orbital transfer, the trace identity would acquire an artificial plus sign while the actual character values would remain as displayed.

## 6. Elliptic orthogonality in rank one

### 6.1 The elliptic pairing

Characters will determine a unique transfer only if they are linearly independent on the elliptic set. Ordinary character orthogonality is unavailable on $G/Z$, which is noncompact. The remedy is to integrate only over elliptic conjugacy classes and to quotient away the induced spectrum that vanishes there.

Fix a unitary central character $\omega$. For admissible representations $\pi,\tau$ with that central character define

$$
e_G(\pi,\tau)
=\frac12\sum_E\frac1{e(E/K)}
\int_{E^\times/K^\times}
D(t)\Theta_\pi(t)\overline{\Theta_\tau(t)}\,dt.
$$

The sum runs over separable quadratic fields embedded as elliptic tori. The factor $e(E/K)^{-1}$ turns the torus measure of Chapter 3, whose total volume is $e(E/K)$, into probability measure. The regular-character bound of Theorem 5.1 makes the expression integrable at the center: the product of two character singularities is cancelled by $D(t)$. In equal characteristic two, where the set of quadratic tori is infinite, the sum is interpreted by the exhaustion specified after Weyl integration; equivalently, this pairing is the normalized compact-inner-form conjugacy measure transported to the split elliptic quotient. This avoids any assumption that there are only finitely many quadratic extensions.

The pairing is additive on finite-length representations. Every principal series has zero elliptic character and therefore lies in its radical. At a reducibility point the relation

$$
[I(\mu|\cdot|^{-1/2},\mu|\cdot|^{1/2})]
=[\mu\circ\det]+[\operatorname{St}\otimes\mu]
$$

shows that, in the elliptic quotient,

$$
[\operatorname{St}\otimes\mu]=-[\mu\circ\det].
$$

This equality of elliptic characters is not an isomorphism of representations. It is a useful counterexample to the claim that restriction of characters to elliptic elements distinguishes every irreducible of $G$; it distinguishes precisely the elliptic quotient.

### 6.2 Ordinary orthogonality on $D^\times/K^\times$

For a unitary central character, tensoring one coefficient with the inverse central character makes it a function on the compact quotient $\bar G'$. Let

$$
V'=\operatorname{vol}(\bar G')=\frac{2}{q-1}.
$$

Schur orthogonality gives, for irreducibles $\rho,\sigma$ with central character $\omega$,

$$
\frac1{V'}\int_{\bar G'}
\Theta_\rho(d)\overline{\Theta_\sigma(d)}\,d\bar d
=\delta_{\rho,\sigma}.
$$

**Proof.** Apply the averaging operator

$$
A\mapsto\int_{\bar G'}\rho(d)A\sigma(d)^{-1}\,d\bar d
$$

to $\operatorname{Hom}(V_\sigma,V_\rho)$. It projects onto the intertwining space. Its trace is both the displayed character integral and, by Schur's lemma, $0$ or the scalar determined by the identity map. Dividing by $V'$ gives the formula. $\square$

Using Weyl integration, the left side is

$$
\frac12\sum_E\frac1{e(E/K)}
\int_{E^\times/K^\times}
D(t)\Theta_\rho(t)\overline{\Theta_\sigma(t)}\,dt.
$$

Indeed $\operatorname{vol}(E^\times\backslash D^\times)=V'/e(E/K)$. Thus ordinary compact-group orthogonality and the split elliptic pairing have exactly the same normalized conjugacy-class measure.

### 6.3 The rank-one elliptic orthogonality theorem

**Theorem 6.1 (elliptic orthogonality).** For discrete-series representations $\pi,\tau$ of $G$ with the same unitary central character,

$$
e_G(\pi,\tau)=\delta_{\pi,\tau}.
$$

Moreover their characters form an orthonormal basis of the completion of the elliptic cocenter dual. Equivalently, a finite linear combination of discrete-series characters that vanishes on the elliptic regular set has all coefficients zero.

**Proof strategy.** Resolve the elliptic trace at a fixed compact-open level by the two cell orbits of the Bruhat--Tits tree. Vertex terms come from maximal compact stabilizers and edge terms from an Iwahori stabilizer. The resulting finite-level index is zero on parabolically induced representations and is the identity matrix on discrete-series characters. Its geometric trace is the elliptic integral above.

**Proof.** Let $\mathscr T$ be the tree. Modulo $Z$, $G$ has one orbit of vertices and one orbit of unoriented edges. For a sufficiently deep normal subgroup $J$ fixing the vectors under consideration, the cellular complex

$$
0\longrightarrow C_c(\mathscr T_1)\longrightarrow
C_c(\mathscr T_0)\longrightarrow\mathbf1\longrightarrow0
$$

is exact because the tree is connected and contractible. Apply the vertex and edge averaging idempotents to the finite-dimensional $J$-fixed spaces. Finite-group Schur orthogonality then gives the rank-one index formula

$$
\operatorname{tr}\tau(f_\pi^{\mathrm{EP}})
=\begin{cases}
1,&\tau\cong\pi,\\
0,&\tau\text{ is a different discrete series or is parabolically induced}.
\end{cases}
$$

Here $f_\pi^{\mathrm{EP}}$ is the vertex term minus the edge term, with the common central character and the stabilizer indices imposed. The cancellation for an induced representation is the exact cellular complex of its two boundary values on an apartment. For a discrete series the Jacquet boundary is zero, and compact-mod-center coefficient orthogonality leaves precisely the identity intertwiner. This finite-level index statement, rather than finite rank alone, is the algebraic core of elliptic orthogonality.

Now evaluate the same alternating trace geometrically. A regular elliptic $t$ fixes a unique vertex or edge midpoint after subdivision. The Lefschetz trace of $t$ on the cell complex is therefore $1$; a split regular element translates or fixes an infinite apartment and has compactly supported Euler trace zero. The conjugation Jacobian is $D(t)$, so Weyl integration identifies

$$
\operatorname{tr}\tau(f_\pi^{\mathrm{EP}})
=e_G(\pi,\tau).
$$

The scalar is determined by the base case $\pi=\tau=\operatorname{St}$ and Section 5.4; it is one with the probability torus measures just fixed. Combining the spectral and geometric evaluations proves orthogonality. The same calculation is valid after increasing $J$, because subdivision adds a cancelling vertex-edge pair.

At each compact-open level the spaces involved are finite dimensional, so ordinary finite-dimensional duality says the discrete characters span the elliptic cocenter dual at that level. Taking the directed union over levels proves completeness. $\square$

The proof is special to rank one in its visible simplicity: a tree has only vertices and edges. It is nevertheless a full local argument. No global automorphic quotient or global trace formula has entered.

### 6.4 Why principal series disappear

The theorem has two complementary explanations. Geometrically, an elliptic element stabilizes no $K$-rational line, so an induced character has no fixed point from which to receive a contribution. Homologically, a split torus acts on an apartment whose compact Euler characteristic is zero. Both mechanisms say

$$
\Theta_{I(\chi_1,\chi_2)}|_{G_{\mathrm{ell}}}=0.
$$

At a reducibility point the induced representation still vanishes elliptically, but its two constituents do not: their characters are negatives of one another there. Exactly one constituent, Steinberg, is discrete series. The elliptic quotient keeps that constituent and uses the other only to calculate its sign.

## 7. Definition and uniqueness of transfer

### 7.1 The character identity and its sign

We can now state the definition without circularity. For $\rho\in\operatorname{Irr}(D^\times)$, a discrete-series representation $\pi$ of $G$ is its **Jacquet--Langlands transfer** if

$$
\boxed{\ \Theta_\pi(g)=-\Theta_\rho(d)\ }
$$

for every pair $g\leftrightarrow d$ of regular elements. We then write

$$
\pi=\operatorname{JL}(\rho).
$$

The sign is $-1=(-1)^{2-1}$. More importantly, it is forced in degree two by the Steinberg calculation of Section 5.4. Our matching-class orientation uses equal characteristic polynomials, and our geometric transfer uses equal orbital integrals; relative to those choices the boxed sign is not negotiable.

The identity is required only on the regular elliptic set. It determines the trace distribution on the elliptic cocenter, which is all that is needed to identify a discrete-series representation. No value at a central or inseparable element is part of the definition.

### 7.2 Uniqueness

**Theorem 7.1.** At most one discrete-series representation of $G$ can satisfy the boxed identity for a given irreducible $\rho$.

**Proof.** If $\pi_1$ and $\pi_2$ both satisfy it, then

$$
\Theta_{\pi_1}(g)-\Theta_{\pi_2}(g)=0
$$

on every elliptic regular $g$. Elliptic orthogonality gives

$$
0=e_G(\pi_1-\pi_2,\pi_1-\pi_2).
$$

Expanding with Theorem 6.1 yields $2-2\delta_{\pi_1,\pi_2}$, so $\pi_1\cong\pi_2$. $\square$

This proof explains why equality of conductors or local factors would not suffice for uniqueness. Orthogonality uses the entire regular elliptic character and detects every discrete-series isomorphism class, including wild representations with identical coarse invariants.

### 7.3 Equivalent trace identity

Let $f$ and $f'$ be matching test functions. Weyl integration, equality of orbital integrals, equality of discriminants, and the boxed character identity give

$$
\boxed{\ \operatorname{tr}\operatorname{JL}(\rho)(f)
=-\operatorname{tr}\rho(f')\ }.
$$

Here $f$ is taken in an elliptic lift when starting from $f'$. Conversely, if this trace identity holds for every matching pair, choose functions supported in an arbitrarily small regular chart around $g\leftrightarrow d$. Proposition 4.1 and local constancy then recover the pointwise character identity. Thus the two forms are equivalent.

The trace identity is often more useful globally because test functions tensor and traces multiply. The pointwise identity is more useful locally because it fixes conjugacy orientation and makes twisting transparent. We shall use both, always with the same minus sign.

## 8. Existence and bijectivity

### 8.1 The rank-one elliptic trace theorem

Orthogonality proves that a putative transfer is unique, but not that the negative of a division character is itself an irreducible split character. A priori it could be an infinite or virtual combination. The missing ingredient is an integrality statement for the elliptic cocenter.

**Theorem 8.1 (rank-one elliptic trace theorem).** Fix a central character $\omega$. Under geometric transfer of cocenters,

$$
\mathcal T:
\overline{\mathcal H}_{\mathrm{ell}}(G,\omega)
\xrightarrow{\sim}
\overline{\mathcal H}(G',\omega),
$$

the dual map carries the character lattice of $G'$ onto the negative of the discrete-series character lattice of $G$. More explicitly, for each irreducible $\rho$ of $G'$ there are integers $m_\pi(\rho)$, only finitely many at any fixed level, such that

$$
-\Theta_\rho(d)=
\sum_{\pi\in\operatorname{Irr}_{\mathrm{disc}}(G,\omega)}
m_\pi(\rho)\Theta_\pi(g)
$$

on matching classes, and

$$
\sum_\pi m_\pi(\rho)^2=1.
$$

**Proof strategy.** Work at one finite congruence level on the compact side and one finite subtree quotient on the split side. A vertex-minus-edge index map carries the integral character lattice of the first finite algebra to the elliptic character lattice of the second. The local index calculation is an isometry and has the fixed orientation already seen for Steinberg. Orthogonality then forces one irreducible rather than a virtual sum.

**Proof.** Choose $m$ such that $U_D^m$ acts trivially on $\rho$ and impose its central character. After dividing by the center with that character, the relevant quotient of $D^\times/U_D^m$ is finite; its twisted group algebra is a finite-dimensional semisimple algebra $\mathcal A_{m,\omega}$. On the split side choose a finite ball in the tree large enough to contain all vertex and edge types visible at level $m$.

The finite-level index lemma is the following statement. Alternating induction from the vertex stabilizers and restriction to the edge stabilizers defines a homomorphism

$$
R(\mathcal A_{m,\omega})
\longrightarrow R_{\mathrm{ell}}(G,\omega)
$$

of integral Grothendieck groups. Its character on a separable elliptic class is the negative of the original division character on the matching class, and its elliptic pairing is the ordinary compact pairing. To verify the lemma, decompose both finite quotients into trace--norm strata. On a regular stratum the conjugation submersion reduces the assertion to equality of the common torus sum. On a singular stratum the two split cell stabilizers give the central germ with opposite vertex-edge contributions. Fourier inversion on the transverse finite lattice supplies the remaining sign. That transverse orientation is independent of the torus and of the representation carried by the stratum; in the scalar stratum it is exactly the Steinberg computation of Section 5.4.

This proof of the index lemma uses only finite induction, restriction, and Fourier inversion. In particular it applies to a simple $\mathcal A_{m,\omega}$-module described by projective Clifford data: the inverse cocycles on its multiplicity space cancel in the honest induced module, so no splitting of $[\alpha]$ and no quadratic-torus label is required.

Apply the index map to the class of $\rho$. Because it is a homomorphism of integral Grothendieck groups, the resulting elliptic character has an expansion

$$
-\Theta_\rho(d)=
\sum_\pi m_\pi(\rho)\Theta_\pi(g)
$$

with integer coefficients. The isometry assertion and Schur orthogonality make its norm one. Expanding in the orthonormal basis of Theorem 6.1 gives

$$
1=\sum_\pi |m_\pi(\rho)|^2.
$$

The coefficients are integers, so precisely one is $1$ or $-1$ and all others vanish. The orientation clause in the finite-level index lemma says that the surviving coefficient is $+1$: the uniform minus sign has already been placed on the division character. Thus no blockwise choice of signs remains.

Finally, inflation to a deeper division quotient and enlargement of the split finite subtree commute with the index map: the added vertex and edge terms form an exact cancelling pair. Passing through this directed system proves the assertion for arbitrary depth, including projective Clifford data. $\square$

The theorem is the local existence engine. It is not the Jacquet--Langlands correspondence restated: its proof uses only finite quotient character theory, smooth orbital transfer, and the cellular resolution of the tree. In particular, it neither assumes a pre-existing transfer of irreducibles nor imports a global automorphic trace formula.

### 8.2 Construction of the transfer

For $\rho\in\operatorname{Irr}(D^\times)$, Theorem 8.1 supplies a unique discrete-series $\pi$ whose elliptic character is the negative of $\Theta_\rho$. Define

$$
\operatorname{JL}(\rho)=\pi.
$$

Existence of the character identity is built into the construction, and Theorem 7.1 makes the result independent of every finite-level representative used in its proof.

The map is injective. If $\operatorname{JL}(\rho_1)\cong\operatorname{JL}(\rho_2)$, their character identities imply equality of $\Theta_{\rho_1}$ and $\Theta_{\rho_2}$ on the regular set. That set has full measure in the compact quotient; ordinary character orthogonality gives $\rho_1\cong\rho_2$.

It is surjective. Let $\pi$ be a discrete-series representation. Apply the inverse cocenter transfer to its elliptic character. The same integral-lattice argument expresses the result as an integral combination of division characters of norm one, hence as one irreducible character up to sign. The Steinberg orientation again fixes the sign, producing $\rho$ with $\operatorname{JL}(\rho)=\pi$.

We have proved the main theorem.

**Theorem 8.2 (local Jacquet--Langlands for degree two).** There is a unique bijection

$$
\operatorname{JL}:\operatorname{Irr}(D^\times)
\xrightarrow{\sim}
\operatorname{Irr}_{\mathrm{disc}}(\mathrm{GL}_2(K))
$$

such that for matching regular elements

$$
\Theta_{\operatorname{JL}(\rho)}(g)=-\Theta_\rho(d).
$$

It is characterized equivalently by the trace identity with matching functions.

### 8.3 Exhaustivity, including wild representations

The scope of Theorem 8.2 is broader than the tame admissible-pair constructions. Every irreducible of $D^\times$ kills some $U_D^m$ and is described by a Clifford datum

$$
(m,\rho_0,G_{\rho_0},[\alpha],\eta).
$$

The finite-level proof of Theorem 8.1 uses the corresponding simple module of $\mathcal A_{m,\omega}$ without requiring the cocycle $[\alpha]$ to split or the stabilizer to be a quadratic torus. It therefore transfers every wild representation. Conversely every wild supercuspidal of $G$ occurs by surjectivity.

What the theorem does **not** provide is a uniform elementary formula turning an arbitrary wild Clifford tuple into a named compact-induction tuple on $G$. At a fixed depth, one can compute it by transferring the finite character table and locating the unique discrete row through elliptic orthogonality. That is an effective finite calculation, but it is not honestly summarized by a tame pair $(E,\theta)$ in residue characteristic two. We retain the abstract Clifford parameter exactly where Books 77 and 82 retained it.

This distinction matters for later factor calculations. Conductor, central character, contragredient, twists, formal degree, and zeta-integral factors are defined for the wild representation and will be compared intrinsically. A formula involving a quadratic inducing character is asserted only when such a character is genuinely part of the datum.

### 8.4 Independence of auxiliary choices

The construction mentioned embeddings of quadratic fields, regular charts, compact-open levels, and a subdivision of the tree. None survives in the result.

- Changing an embedding conjugates it, and orbital integrals are conjugation invariant.
- Refining a regular chart changes a representative function but not its cocenter class.
- Inflating a finite quotient module to a deeper quotient preserves its primitive character projector and its transferred trace.
- Subdividing the tree replaces the cellular complex by a chain-homotopy equivalent one, so its Euler trace is unchanged.
- Rescaling both quotient measures used in an orbital integral changes the representative functions but not the condition that the two orbital integrals agree. The explicit formal-degree and epsilon-factor statements later do depend on their separately fixed measures.

Most decisively, any two constructions produce discrete-series representations satisfying the same regular character identity. Uniqueness then identifies them. Character theory turns a choice-laden construction into a canonical bijection.

## 9. The first structural consequences

### 9.1 Norm characters and twists of Steinberg

Every one-dimensional representation of $D^\times$ is

$$
\rho=\mu\circ\operatorname{Nrd}
$$

for a unique smooth character $\mu$ of $K^\times$. Section 5.4 proves that

$$
\boxed{\ \operatorname{JL}(\mu\circ\operatorname{Nrd})
=\operatorname{St}\otimes(\mu\circ\det).\ }
$$

This includes ramified and nonunitary $\mu$. The calculation does more than identify the family: it distinguishes $\mu$ from a possible quadratic twist, since the division character itself remembers $\mu$ through reduced norm even though its central character remembers only $\mu^2$.

The trivial representation of $D^\times$ therefore transfers to the Steinberg representation, not to the trivial representation of $G$. On an elliptic element $g$,

$$
\Theta_{\operatorname{St}}(g)=-1.
$$

This is the simplest complete instance of the correspondence and the normalization test for every later formula.

### 9.2 Higher-dimensional representations and supercuspidals

If $\dim\rho>1$, then $\operatorname{JL}(\rho)$ cannot be a Steinberg twist. Indeed every Steinberg twist is already the image of the unique norm character in Section 9.1, and transfer is injective. Since the discrete series of $G$ consist only of special representations and supercuspidals,

$$
\dim\rho>1
\quad\Longleftrightarrow\quad
\operatorname{JL}(\rho)\text{ is supercuspidal}.
$$

This is not a comparison of dimensions: the supercuspidal is infinite dimensional. It is a comparison of the character/noncharacter dichotomy on the anisotropic side with the special/supercuspidal dichotomy inside the split discrete spectrum.

For level-zero data the statement is visible directly. A regular character $\bar\theta:k_2^\times\to C^\times$ gives a two-dimensional division representation whose character on a residue-regular unit is

$$
\bar\theta(u)+\bar\theta(u^q).
$$

The finite cuspidal representation of $\mathrm{GL}_2(k)$ associated with the same regular orbit has character

$$
-\bar\theta(u)-\bar\theta(u^q)
$$

on the elliptic torus. Inflating and compactly inducing gives the required supercuspidal identity.

### 9.3 Central characters and twisting

Let $z\in K^\times$ and choose a regular matching pair $g\leftrightarrow d$. Then $zg\leftrightarrow zd$. If $\pi=\operatorname{JL}(\rho)$, the identity at the two pairs gives

$$
\omega_\pi(z)\Theta_\pi(g)
=-\omega_\rho(z)\Theta_\rho(d).
$$

Comparing with the identity at $g\leftrightarrow d$ and choosing a point where the character is nonzero yields

$$
\boxed{\ \omega_{\operatorname{JL}(\rho)}=\omega_\rho.\ }
$$

For a character $\chi:K^\times\to C^\times$, matching norms give

$$
\Theta_{\operatorname{JL}(\rho)\otimes(\chi\circ\det)}(g)
=-\Theta_{\rho\otimes(\chi\circ\operatorname{Nrd})}(d).
$$

Uniqueness therefore gives

$$
\boxed{\ \operatorname{JL}
(\rho\otimes(\chi\circ\operatorname{Nrd}))
\cong\operatorname{JL}(\rho)\otimes(\chi\circ\det).\ }
$$

Both central characters are multiplied by $\chi^2$, because determinant and reduced norm take $z$ to $z^2$. The formula is exact even when a ramified twist lowers the conductor by cancellation.

### 9.4 Contragredients

Character functions of contragredients satisfy

$$
\Theta_{\pi^\vee}(g)=\Theta_\pi(g^{-1}),\qquad
\Theta_{\rho^\vee}(d)=\Theta_\rho(d^{-1}).
$$

Since inversion preserves matching,

$$
\Theta_{\operatorname{JL}(\rho)^\vee}(g)
=-\Theta_{\rho^\vee}(d).
$$

Uniqueness gives

$$
\boxed{\ \operatorname{JL}(\rho^\vee)
\cong\operatorname{JL}(\rho)^\vee.\ }
$$

For norm characters this reads

$$
\operatorname{St}\otimes\mu^{-1}
=\operatorname{JL}(\mu^{-1}\circ\operatorname{Nrd}).
$$

For a tame pair it sends $\theta$ to $\theta^{-1}$ together with the dual compatible extension. In the wild Clifford parametrization it dualizes the finite representation, inverts the cocycle, and dualizes the projective multiplicity module. No self-duality is inferred merely from a quadratic central character.

## 10. Conductors and compact-open level

### 10.1 The two level scales

Conductors compare arithmetic depth, but the defining compact opens on the two sides are different. On $G$, for an infinite-dimensional generic irreducible,

$$
a_G(\pi)=\min\{n\ge0:\pi^{\mathcal K_1(\mathfrak p^n)}\ne0\}.
$$

The newvector space at $n=a_G(\pi)$ is one dimensional, and at $m\ge a_G(\pi)$ its dimension is $m-a_G(\pi)+1$.

On $D^\times$, let

$$
c_D(\rho)=\min\{m\ge0:U_D^m\text{ acts trivially}\}.
$$

Normality makes the invariant space all or nothing:

$$
\rho^{U_D^m}=
\begin{cases}
0,&m<c_D(\rho),\\
\rho,&m\ge c_D(\rho).
\end{cases}
$$

Book 82 defined the transfer-facing number

$$
a_D(\rho)=
\begin{cases}
2a(\mu),&\rho=\mu\circ\operatorname{Nrd},\\
c_D(\rho)+1,&\dim\rho>1.
\end{cases}
$$

These definitions must remain visible. There can be equality of conductor exponents without an isomorphism of fixed-vector spaces.

### 10.2 The exact conductor comparison

**Theorem 10.1.** Let $\pi=\operatorname{JL}(\rho)$. Then:

1. if $\dim\rho>1$, then $a_G(\pi)=a_D(\rho)=c_D(\rho)+1$;
2. if $\rho=\mu\circ\operatorname{Nrd}$ with $a(\mu)>0$, then

   $$
   a_G(\pi)=2a(\mu)=a_D(\rho);
   $$

3. if $\rho=\mu\circ\operatorname{Nrd}$ with $\mu$ unramified, then

   $$
   a_D(\rho)=0,\qquad a_G(\pi)=1.
   $$

Thus the prepared exponents agree except for the unramified norm-character orbit, where the image is an unramified Steinberg twist and the monodromy contributes one.

**Proof strategy.** For tame pairs compare the explicit different-plus-character formulas. For norm characters use the special conductor formula. For wild representations detect the last nonzero congruence layer in the transferred finite-level Euler trace; a shift by one converts the normal division filtration to the asymmetric split newvector filtration.

**Proof.** If $\rho=\mu\circ\operatorname{Nrd}$, Section 9.1 and Book 77 give

$$
a_G(\operatorname{St}\otimes\mu)=
\begin{cases}1,&a(\mu)=0,\\2a(\mu),&a(\mu)>0.
\end{cases}
$$

This proves (2) and (3).

For a minimal tame pair $(E/K,\theta)$, Books 77 and 82 established on their respective sides the common expression

$$
\Delta(E/K)+f(E/K)a_E(\theta).
$$

This proves (1) in the tame range. For an arbitrary higher-dimensional $\rho$, choose the least $m=c_D(\rho)$. Refine the finite-level index lemma of Chapter 8 by inserting the averaging idempotent of $\mathcal K_1(\mathfrak p^r)$ in its vertex and edge terms. Finite Mackey decomposition gives zero index for $r\le m$: a surviving vector would make the last nontrivial $U_D^{m-1}/U_D^m$-constituent trivial. At $r=m+1$, exactly one orbit of that last constituent survives, and finite Clifford orthogonality makes its multiplicity one. Hence

$$
\dim\operatorname{JL}(\rho)^{\mathcal K_1(\mathfrak p^r)}
=0\quad(r\le m),
\qquad
\dim\operatorname{JL}(\rho)^{\mathcal K_1(\mathfrak p^{m+1})}=1.
$$

The split newvector theorem now gives $a_G=m+1$. In the projective Clifford case, the cocycle and inverse cocycle cancel in the honest stabilizer module, so the same Mackey count applies. This proves (1) without replacing wild data by a tame pair. $\square$

The exceptional shift is mathematically necessary. Calling $a_D=0$ for an unramified norm character records that it is trivial on $\mathcal O_D^\times$. Calling $a_G=1$ for Steinberg records that it has an Iwahori line but no hyperspecial line. These are both correct facts; no renaming makes them equal without changing one established definition.

### 10.3 Newvectors and division-side invariants

Suppose $\dim\rho>1$ and put $a=a_D(\rho)$. Then

$$
\rho^{U_D^{a-2}}=0,\qquad
\rho^{U_D^{a-1}}=\rho,
$$

whereas

$$
\dim\operatorname{JL}(\rho)^{\mathcal K_1(\mathfrak p^{a-1})}=0,\qquad
\dim\operatorname{JL}(\rho)^{\mathcal K_1(\mathfrak p^a)}=1.
$$

At higher split levels,

$$
\dim\operatorname{JL}(\rho)^{\mathcal K_1(\mathfrak p^m)}=m-a+1.
$$

Thus transfer sends the **first level that kills the entire division representation**, shifted by one, to the **first split level that reveals one distinguished line**. It does not send all of $\rho$ to the newvector line. The dimension of $\rho$ reappears in formal degree, not in newvector multiplicity.

For an unramified norm character, $\rho^{\mathcal O_D^\times}$ is one dimensional, while its Steinberg transfer has no $\mathcal K$-fixed vector and a one-dimensional Iwahori-fixed line. For a ramified norm character of conductor $r$, $U_D^{2r-1}$ first kills the character and $\mathcal K_1(\mathfrak p^{2r})$ first fixes a Steinberg newvector.

The exact division-side invariant space for a nonnormal toral compact open is given by the finite Mackey sum

$$
\dim\rho^H
=\sum_{x\in J\backslash D^\times/H}
\dim\operatorname{Hom}_{J\cap xHx^{-1}}(\Lambda,\mathbf1).
$$

There is no universal equality between this number and a split $\mathcal K_0$- or type-invariant dimension. Transfer compares the representation, while a chosen level structure requires its own local calculation.

### 10.4 Cancellation under ramified twists

Twisting compatibility makes the correct conductor rule immediate:

$$
a_G(\operatorname{JL}(\rho)\otimes\chi)
=a_G\bigl(\operatorname{JL}(\rho\otimes\chi)\bigr).
$$

For a tame pair this common value is

$$
\Delta(E/K)+f(E/K)
a_E\bigl(\theta(\chi\circ N_{E/K})\bigr),
$$

after the twisted pair is put in minimal form. For a norm character it is the special formula applied to $\mu\chi$. Equal-depth cancellation can lower the result. If $\chi$ is more deeply ramified than every character visible in the original datum, cancellation is impossible and the common split conductor is $2a(\chi)$.

**Counterexample.** Let $p$ be odd and let $\mu$ be a nontrivial tame quadratic character. Then

$$
\rho=\mu\circ\operatorname{Nrd}
$$

has $a_D(\rho)=2$ and transfers to $\operatorname{St}\otimes\mu$, also of conductor two. Twisting both sides by $\mu$ produces the trivial norm character and unramified Steinberg. Their established exponents are $0$ and $1$, respectively. A naive maximum formula predicts $2$ and fails on both sides.

## 11. Formal degrees

### 11.1 A compatible pair of quotient measures

Formal degree depends inversely on Haar measure. A statement that transfer preserves it is meaningless until the two different central quotients have been normalized relative to one another. We use

$$
\operatorname{vol}(\mathrm{PGL}_2(\mathcal O))=1,
\qquad
\operatorname{vol}(D^\times/K^\times)=\frac{2}{q-1}.
$$

For a unitary irreducible $\pi$ of $G$ that is square-integrable modulo $Z$, its formal degree $d_G(\pi)$ is characterized by

$$
\int_{G/Z}
\langle\pi(g)v_1,\lambda_1\rangle
\langle\pi(g^{-1})v_2,\lambda_2\rangle\,d\bar g
=d_G(\pi)^{-1}
\langle v_1,\lambda_2\rangle
\langle v_2,\lambda_1\rangle.
$$

For finite-dimensional $\rho$ on the compact quotient,

$$
d_{G'}(\rho)
=\frac{\dim\rho}{\operatorname{vol}(G'/Z)}
=\frac{q-1}{2}\dim\rho.
$$

With $\operatorname{vol}(G'/Z)=1$, the degree would instead be $\dim\rho$ and literal preservation would fail by the constant $(q-1)/2$. This is why the measure was fixed at the beginning rather than after the theorem.

### 11.2 The formal-degree identity

**Theorem 11.1.** For every irreducible unitary $\rho$ of $D^\times$,

$$
\boxed{\ d_G(\operatorname{JL}(\rho))=d_{G'}(\rho)
=\frac{q-1}{2}\dim\rho.\ }
$$

The same formula applies to essentially unitary representations after removing a common real unramified twist.

**Proof strategy.** Compare the leading coefficient of the character near the identity through elliptic pseudo-coefficients. On the compact side it is dimension divided by quotient volume. On the split side it is formal degree. Transfer identifies the regular elliptic germ and the Steinberg case fixes the scalar.

**Proof.** Let $f_\rho'$ be a matrix-coefficient projector on $G'/Z$, normalized by $\operatorname{tr}\sigma(f_\rho')=\delta_{\rho,\sigma}$. Its value at the identity is $d_{G'}(\rho)$. Choose an elliptic lift $f_\rho$ on $G$. The trace identity makes $-f_\rho$ a pseudo-coefficient for $\pi=\operatorname{JL}(\rho)$: its trace is one on $\pi$, zero on every other tempered irreducible with the fixed center, and zero on principal series because it is elliptic.

Apply Schur orthogonality to a matrix coefficient of $\pi$ and express its projector in the elliptic cocenter. The value of the projector's regular germ at the identity is $d_G(\pi)$. Matching identifies this germ with the division projector germ. The quotient between the two possible scalar normalizations is independent of $\rho$; evaluate it at $\rho=\mathbf1$. Its transfer is $\operatorname{St}$, whose tree coefficient calculation gives

$$
d_G(\operatorname{St})=\frac{q-1}{2}
$$

when $\operatorname{vol}(\mathrm{PGL}_2(\mathcal O))=1$. The division degree of $\mathbf1$ under our measure is the same. Hence the scalar is one in every block. $\square$

Formal degree is unchanged by a unitary character twist, as is dimension on the division side. The theorem therefore fits twisting compatibility automatically.

### 11.3 Checks in the special and tame families

For $\rho=\mu\circ\operatorname{Nrd}$,

$$
d_{G'}(\rho)=\frac{q-1}{2}
=d_G(\operatorname{St}\otimes\mu)
$$

when $\mu$ is unitary. The degree does not depend on whether $\mu$ is ramified, even though its conductor does.

For a minimal tame unramified pair with $n=a_E(\theta)$, one has $\dim\rho=2q^{n-1}$, hence

$$
d_G(\operatorname{JL}(\rho))=(q-1)q^{n-1}.
$$

For a minimal tame ramified pair, $n$ is even and $\dim\rho=(q+1)q^{(n-2)/2}$, so

$$
d_G(\operatorname{JL}(\rho))
=\frac{q^2-1}{2}q^{(n-2)/2}.
$$

Conductor records the last filtration layer; dimension records the size of the compact orbit and Heisenberg piece; formal degree is where that finite dimension reappears on the infinite-dimensional split side.

## 12. Local factors

### 12.1 Zeta integrals on the two degree-two algebras

Later global arguments require local $L$- and epsilon factors, not merely conductors. Defining a factor on the division side to be the factor of its transfer would prove compatibility by notation. Instead use the same zeta construction on $A=M_2(K)$ and $A'=D$.

Let $\Phi$ be a compactly supported locally constant function on $A$, let $c(g)=\lambda(\pi(g)v)$ be a matrix coefficient, and put

$$
Z_A(s,\Phi,c)
=\int_{A^\times}\Phi(x)c(x)|\operatorname{nrd}(x)|^{s+1/2}\,d^\times x.
$$

Use the identical formula for $A'$, with reduced norm and a coefficient of $\rho$. The shift $1/2=(2-1)/2$ is the unitary degree-two normalization. For real part of $s$ large the integral converges; norm shells make it rational in $q^{-s}$.

The fractional ideal generated by all such integrals is principal. Its normalized generator with constant term one is denoted $L(s,\pi)$ or $L(s,\rho)$. On $M_2(K)$ this agrees with the Whittaker-newform factor of Book 77. It is intrinsic on $D$ and applies to wild Clifford representations.

If $\rho$ has no $\mathcal O_D^\times$-fixed vector, unit-shell averaging gives $L(s,\rho)=1$. If $\rho=\mu\circ\operatorname{Nrd}$ with $\mu$ unramified, take $\Phi=\mathbf1_{\mathcal O_D}$ and a constant coefficient. The nonnegative norm shells form a geometric series:

$$
L(s,\rho)=L(s+1/2,\mu)
=\left(1-\mu(\varpi)q^{-s-1/2}\right)^{-1}.
$$

For ramified $\mu$, unit averaging again gives $1$. These are exactly the Steinberg-factor shapes on the split side.

### 12.2 Fourier transform and the functional equation

Put $\langle x,y\rangle_A=\psi(\operatorname{trd}(xy))$. Choose self-dual additive measure and define

$$
\widehat\Phi(y)=\int_A\Phi(x)\psi(\operatorname{trd}(xy))\,dx.
$$

Use reduced trace on $D$ for the same definition. Finite Fourier inversion on lattice quotients gives $\widehat{\widehat\Phi}(x)=\Phi(-x)$. There is a unique rational function $\gamma(s,\pi,\psi)$ such that

$$
Z_A(1-s,\widehat\Phi,c^\vee)
=\gamma(s,\pi,\psi)Z_A(s,\Phi,c),
$$

where $c^\vee(x)=c(x^{-1})$ is paired with the contragredient. Define $\gamma(s,\rho,\psi)$ identically on $D$. Separating normalized generators gives

$$
\gamma(s,\pi,\psi)
=\epsilon(s,\pi,\psi)
\frac{L(1-s,\pi^\vee)}{L(s,\pi)},
$$

and similarly for $\rho$. This defines the epsilon factor.

For a lattice $L\subset A$, Fourier transform carries $\mathbf1_L$ to $\operatorname{vol}(L)\mathbf1_{L^\perp}$. Splitting $A^\times$ into valuation shells reduces the functional equation to finite Fourier inversion on $L/\varpi^mL$. The last nonzero transform is a Gauss sum; its shell number is the analytic conductor. No global functional equation is used.

### 12.3 Compatibility of $L$- and epsilon factors

**Theorem 12.1.** If $\pi=\operatorname{JL}(\rho)$, then

$$
\boxed{L(s,\pi)=L(s,\rho),\qquad
\epsilon(s,\pi,\psi)=\epsilon(s,\rho,\psi).}
$$

Consequently the gamma factors agree.

**Proof strategy.** The substantial input is a local Fourier-transfer lemma for the two degree-two algebras. Prove it on lattice quotients, including the singular germ, and then apply the two functional equations. This keeps factor compatibility independent of any parameterization by quadratic characters.

**Proof.** We first record the Fourier-transfer lemma in the form needed here. Suppose $\Phi$ and $\Phi'$ have matching regular orbital integrals after restriction to $M_2(K)^\times$ and $D^\times$. Then their Fourier transforms have matching orbital integrals with the same geometric transfer factor. The spectral minus sign is unchanged.

To prove the lemma, filter a maximal order and its trace-dual by powers of the radical. Fourier transform sends the characteristic function of each lattice to the volume of that lattice times the characteristic function of its annihilator. On a regular trace--norm stratum, conjugation descent reduces the comparison to the same finite quadratic Gauss sum on the common torus. At discriminant zero, the central and split germs must be transformed together; the vertex-minus-edge index from Chapter 8 cancels the extra split isotropic line. This singular calculation is essential: comparison only on regular charts would not prove the Fourier lemma. Exhaustion of the lattice filtration proves it for arbitrary compactly supported locally constant functions, including in characteristic two.

Now pair the two zeta distributions with the finite-level elliptic projector that relates $\rho$ and $\pi$. The trace identity equates them, including one minus sign. Apply the Fourier-transfer lemma and the functional equations. The same minus sign appears after Fourier transform, so it cancels, and

$$
\gamma(s,\pi,\psi)=\gamma(s,\rho,\psi).
$$

The possible poles of the zeta-integral ideals determine their normalized generators. Equality of gamma factors for $\pi$ and $\rho$, together with the corresponding equality for their contragredients, therefore gives $L(s,\pi)=L(s,\rho)$. Substitution in the defining gamma-factor quotient gives equality of epsilon factors. Every comparison took place in local lattice quotients; no global functional equation and no parameter-side definition of the division factors was used. $\square$

In the wild range this remains a finite Fourier calculation on the Clifford quotient and does not require a quadratic label.

### 12.4 Explicit shapes and conductor numbering

For a norm character,

$$
L(s,\mu\circ\operatorname{Nrd})
=L(s+1/2,\mu)
=L(s,\operatorname{St}\otimes\mu).
$$

For every higher-dimensional $\rho$ and every supercuspidal transfer, both $L$-factors are $1$. With $\psi$ of conductor zero, write

$$
\epsilon(s,\rho,\psi)
=\epsilon(1/2,\rho,\psi)
q^{-a_{\mathrm{an}}(\rho)(s-1/2)}.
$$

Compatibility and the newform functional equation give

$$
a_{\mathrm{an}}(\rho)=a_G(\operatorname{JL}(\rho)).
$$

Thus $a_{\mathrm{an}}=a_D$ except for an unramified norm character, where $a_D=0$ and $a_{\mathrm{an}}=1$. The analytic exponent sees Steinberg monodromy that the maximal-order conductor of the division character does not. For a ramified norm character of exponent $r$, both analytic and prepared exponents are $2r$; for higher-dimensional representations they are $c_D+1$.

For a tame quadratic datum, let $\psi_E=\psi\circ\operatorname{Tr}_{E/K}$ and let $\theta^\natural$ be the rectified character of Section 13.4. Then

$$
\epsilon(s,\rho(E,\theta),\psi)
=\lambda(E/K,\psi)
\epsilon(s,\theta^\natural,\psi_E),
$$

where $\lambda(E/K,\psi)$ is the normalized quadratic induction constant. The one-dimensional epsilon factor is a finite Gauss sum over $U_E^0/U_E^{a_E(\theta^\natural)}$. Its exponent is

$$
\Delta(E/K)+f(E/K)a_E(\theta^\natural),
$$

which equals the conductor of a minimal normalized pair.

## 13. Tame admissible pairs

### 13.1 One quadratic datum on both sides

The abstract theorem is complete, but tame representations admit a much more concrete description. Let $E/K$ be a quadratic extension with nontrivial automorphism $\sigma$, and let

$$
\theta:E^\times\to C^\times
$$

be a smooth character. The pair is **regular** if $\theta\ne\theta^\sigma$, equivalently if $\theta$ does not factor through $N_{E/K}$. It is **admissible** if, in addition, descent of its principal-unit restriction through the norm can occur only in the unramified quadratic case. It is **minimal** if no product $\theta(\chi\circ N_{E/K})$ has smaller conductor.

Books 77 and 82 constructed representations

$$
\pi_G(E,\theta)\quad\text{of }G,
\qquad
\rho_D(E,\theta)\quad\text{of }D^\times,
$$

from normalized compatible extensions of the same last filtration character. The normalization on the two sides is now fixed by requiring their finite Heisenberg traces to have opposite elliptic orientation. With this normalization:

**Theorem 13.1 (tame pair transfer).** For every normalized tame admissible pair,

$$
\boxed{\ \operatorname{JL}(\rho_D(E,\theta))
\cong\pi_G(E,\theta).\ }
$$

The pair may be replaced by $(E,\theta^\sigma)$ without changing either representation. A norm twist replaces it on both sides by

$$
(E,\theta(\chi\circ N_{E/K})).
$$

**Proof strategy.** Compare the compact-induction character formulas stratum by stratum. On the open stratum attached to $E$ the same two Galois conjugates occur. On every other elliptic stratum, finite Fourier descent in the transverse quotient compares all conjugates meeting the two inducing subgroups. This second step is necessary: checking only the inducing torus would not determine the character on other elliptic tori.

**Proof.** Embed $E$ in both algebras and let $J_D,J_G$ be the inducing subgroups determined by the same conductor. On a sufficiently regular $t\in E^\times$, the conjugates meeting the inducing subgroup are represented by the identity and the normalizer element inducing $\sigma$. Thus

$$
\Theta_{\rho_D(E,\theta)}(t)
=\operatorname{tr}\Lambda_D(t)
+\operatorname{tr}\Lambda_D(\sigma(t)).
$$

The split compact-induction formula has the same two torus terms. On the common torus the inducing actions agree. On the transverse quotient, the finite Heisenberg representation is obtained from the same commutator pairing. Its two polarizations correspond to the vertex and edge terms in the tree, so their alternating trace is the negative of the anisotropic trace. Hence

$$
\Theta_{\pi_G(E,\theta)}(g_t)
=-\Theta_{\rho_D(E,\theta)}(t).
$$

This proves the identity on the open $E$-stratum. Now take an arbitrary matching elliptic pair. If its conjugacy classes miss both inducing supports, both compact-induction sums vanish. Otherwise conjugation descent places the elements in corresponding finite trace--norm strata of $J_G$ and $J_D$. The summands are indexed by the same stabilizer orbits. Fourier inversion on the quotient transverse to the last common filtration character identifies their Heisenberg traces with the same minus sign; the compatible extension normalization identifies the torus and projective multiplicity traces. This is precisely the tame specialization of the finite-level index lemma in Chapter 8, now applied to the explicit inducing types. It covers elliptic tori not isomorphic to the inducing torus as well as the boundary between adjacent regular strata. Therefore the character identity holds on every matching regular class, and uniqueness proves the theorem. $\square$

The phrase “normalized compatible extension” carries real content. If one independently tensors one Heisenberg extension by a residual character, the two labels may differ by a rectifying character even though the underlying transfer theorem is unchanged. Section 13.4 records the normalization used for factors.

### 13.2 The unramified quadratic case

Assume $E/K$ is unramified, so $e=1$, $f=2$, and $\Delta(E/K)=0$. Minimal admissible pairs have

$$
a_G(\pi_G(E,\theta))
=a_D(\rho_D(E,\theta))
=2a_E(\theta).
$$

At level zero, $a_E(\theta)=1$ and the residue character

$$
\bar\theta:k_E^\times\to C^\times
$$

must satisfy $\bar\theta^q\ne\bar\theta$. For a residue-regular unit $t$,

$$
\Theta_{\rho_D(E,\theta)}(t)
=\bar\theta(\bar t)+\bar\theta(\bar t^q),
$$

whereas the inflated finite cuspidal character on the split side is

$$
\Theta_{\pi_G(E,\theta)}(g_t)
=-\bar\theta(\bar t)-\bar\theta(\bar t^q).
$$

This finite-field calculation gives the entire local character identity after compact induction. It also shows why regularity is necessary. If $\bar\theta^q=\bar\theta$, then $\bar\theta$ factors through $N_{k_E/k}$; the division induction splits into norm characters and the split construction belongs to a principal-series block. There is no supercuspidal transfer attached to the irregular datum.

At positive depth $n=a_E(\theta)\ge2$,

$$
\dim\rho_D(E,\theta)=2q^{n-1},\qquad
c_D=2n-1,\qquad a_D=2n.
$$

If $n$ is even, the inducing representation contains a $q$-dimensional Heisenberg factor; omitting it gives the wrong dimension and destroys the character identity. The split representation has one newvector at level $2n$, not a $2q^{n-1}$-dimensional fixed space.

### 13.3 The ramified quadratic case

Assume the residue characteristic is odd and $E/K$ is ramified quadratic. Then

$$
e=2,\qquad f=1,\qquad\Delta(E/K)=1.
$$

A minimal regular tame character has even conductor $n\ge2$. The odd transfer conductor is

$$
a_G(\pi_G(E,\theta))
=a_D(\rho_D(E,\theta))
=n+1,
$$

and

$$
\dim\rho_D(E,\theta)
=(q+1)q^{(n-2)/2}.
$$

Why can a conductor-one tame character not be regular after minimization? The Galois automorphism acts trivially on the common residue field, so the residue character is Galois invariant. Any difference between $\theta$ and $\theta^\sigma$ must occur on a positive unit layer. In the tame ramified filtration the involution changes the uniformizer direction by sign, and minimality forces the first regular layer to occur at the parity represented by even $n$.

The character comparison again has two normalizer terms, but the transverse quotient has $q+1$ isotropic directions rather than the two valuation parities of the unramified torus. The finite Fourier sum over those directions equals the negative of the division trace. Its absolute size accounts for the factor $q+1$ in the division dimension and the factor $(q^2-1)/2$ in the split formal degree.

At residue characteristic two, a ramified quadratic extension is wild. Its discriminant exponent may exceed one, the parity statement above fails, and the tame inducing quotient may be replaced by nontrivial projective Clifford data. The main correspondence and the formula

$$
a_G(\operatorname{JL}(\rho))=c_D(\rho)+1
$$

for higher-dimensional $\rho$ remain valid, but the displayed tame dimension and $n+1$ formulas are not asserted.

### 13.4 Regularity, minimality, and rectification

There are two characters near an admissible-pair construction that should not be silently identified. The type character $\theta$ was normalized so that

$$
\omega_{\pi_G(E,\theta)}
=\omega_{\rho_D(E,\theta)}
=\theta|_{K^\times}.
$$

The character whose induction gives the convenient two-dimensional factor formula must include the quadratic determinant correction. Let $\kappa_{E/K}$ be the quadratic character of $K^\times$ with kernel $N_{E/K}(E^\times)$. Fix the quadratic **rectifier** $\xi_{E/K}:E^\times\to C^\times$ by

$$
\xi_{E/K}|_{K^\times}=\kappa_{E/K},
$$

minimal conductor, and the Gauss-sum sign determined by $\psi_E$. Concretely:

- if $E/K$ is unramified, $\xi_{E/K}$ is unramified and sends a common uniformizer to $-1$;
- if $E/K$ is tamely ramified, its unit restriction is the quadratic residue character and its value on a chosen $E$-uniformizer is the unique sign making the induction constant $\lambda(E/K,\psi)$ agree with the finite Fourier transform.

Put

$$
\theta^\natural=\theta\xi_{E/K}.
$$

Then the determinant of the induced two-dimensional datum is

$$
\theta^\natural|_{K^\times}\,\kappa_{E/K}
=\theta|_{K^\times},
$$

as required by central-character compatibility. The rectifier has the smallest possible depth, so it does not change the conductor of a minimal regular positive-depth pair; at level zero in the unramified case it is trivial on units and does not change $\bar\theta$.

This explains the factor formula of Section 12.4:

$$
L(s,\pi_G(E,\theta))=1,
$$

$$
\epsilon(s,\pi_G(E,\theta),\psi)
=\lambda(E/K,\psi)
\epsilon(s,\theta^\natural,\psi_E).
$$

The same formulas hold for $\rho_D(E,\theta)$. Using $\theta$ in place of $\theta^\natural$ can introduce a quadratic error in the determinant and root number even though it leaves a coarse conductor calculation unchanged.

## 14. Worked examples over $\mathbf Q_p$

### 14.1 Unramified norm characters

Let $K=\mathbf Q_p$ and let $\mu$ be unramified with $\mu(p)=u$. Then

$$
\rho=\mu\circ\operatorname{Nrd}
$$

is one dimensional, trivial on $\mathcal O_D^\times$, and has $a_D(\rho)=0$. Its transfer is

$$
\operatorname{JL}(\rho)=\operatorname{St}\otimes\mu,
$$

which has conductor one and a one-dimensional Iwahori line. On a matching regular pair,

$$
\Theta_{\operatorname{St}\otimes\mu}(g)
=-\mu(\det g)
=-\mu(\operatorname{Nrd}d).
$$

The common local factor is

$$
\left(1-u p^{-s-1/2}\right)^{-1},
$$

and the common formal degree, with our quotient measures, is $(p-1)/2$. This single example simultaneously checks the sign, the exceptional conductor shift, the half-unitary $L$-shift, and the formal-degree scaling.

### 14.2 A level-zero correspondence

Let $E/\mathbf Q_p$ be unramified quadratic and choose

$$
\bar\theta:\mathbf F_{p^2}^\times\to C^\times,
\qquad \bar\theta^p\ne\bar\theta.
$$

Extend it to $E^\times$ with $a_E(\theta)=1$. The division representation

$$
\rho_D(E,\theta)
=\operatorname{c\text{-}Ind}_{E^\times U_D^1}^{D^\times}\theta
$$

has dimension two, $c_D=1$, and $a_D=2$. Its transfer is the depth-zero supercuspidal obtained by inflating the finite cuspidal representation of $\mathrm{GL}_2(\mathbf F_p)$ and compactly inducing from $\mathbf Q_p^\times\mathrm{GL}_2(\mathbf Z_p)$. It has conductor two and a unique $\mathcal K_1(p^2)$-fixed line.

For a residue generator $t$ of $\mathbf F_{p^2}$ over $\mathbf F_p$,

$$
\Theta_\rho(t)=\bar\theta(t)+\bar\theta(t^p),
$$

and the split character is its negative. Both standard $L$-factors are $1$, both epsilon exponents are $2$, and

$$
d_G(\operatorname{JL}(\rho))=p-1.
$$

If $\bar\theta^p=\bar\theta$, the construction is not a counterexample to the theorem: it is not regular. The division induction decomposes into characters, and the finite split representation is not cuspidal.

### 14.3 A positive-depth unramified example

Assume $p$ is odd. Let $E/\mathbf Q_p$ be unramified quadratic and choose $b\in\mathcal O_E^\times$ with residue outside $\mathbf F_p$. Define the last unit layer of $\theta$ by

$$
\theta(1+px)=\psi_E(p^{-1}bx),
$$

and extend it minimally with $a_E(\theta)=2$. The parameter $b$ is not scalar modulo $p$, so the character is regular after norm twists.

The division representation has

$$
\dim\rho=2p,\qquad c_D=3,\qquad a_D=4,
$$

and its construction contains a $p$-dimensional Heisenberg representation before the valuation-two orbit is induced. Its split transfer is supercuspidal of conductor four. It has no fixed vector at $\mathcal K_1(p^3)$ and one at $\mathcal K_1(p^4)$. The common formal degree is

$$
p(p-1),
$$

and the common standard $L$-factor is $1$. The epsilon constant is the finite Gauss sum attached to $\theta^\natural$ on $U_E^0/U_E^2$, multiplied by $\lambda(E/K,\psi)$.

This example shows why “same conductor” does not mean “same level space.” The division group reveals all $2p$ dimensions once $U_D^3$ is killed; the split group reveals a canonical one-dimensional newvector at level four.

### 14.4 A tame ramified example and the dyadic boundary

Let $p$ be odd, $E=\mathbf Q_p(\sqrt p)$, and choose a minimal regular character $\theta$ with $a_E(\theta)=2$. Then

$$
\Delta(E/K)=1,\qquad f(E/K)=1,\qquad a=3.
$$

The division representation has

$$
\dim\rho=p+1,\qquad c_D=2,\qquad a_D=3,
$$

and its transfer is a supercuspidal with a unique $\mathcal K_1(p^3)$-fixed line. Their common formal degree is

$$
\frac{p^2-1}{2}.
$$

The root number is reduced to a Gauss sum for $\theta^\natural$ over $U_E^0/U_E^2$ and the ramified quadratic induction constant.

At $p=2$, the example must not be copied by replacing $p$ with $2$. Ramified quadratic extensions are wild, $\Delta(E/K)$ can exceed one, and conductor-two regularity has different stabilizer data. One may still begin with an abstract Clifford module killed by $U_D^m$, transfer its finite character through the elliptic cocenter, and obtain a supercuspidal of conductor $m+1$. What is unavailable is the tame dimension formula $p+1$ or a universal description by the displayed pair.

## 15. Scalar symmetries

### 15.1 Unramified twists

An unramified character $\chi$ is trivial on $\mathcal O^\times$. Twisting by it changes only the valuation direction. On matching elements,

$$
\chi(\det g)=\chi(\operatorname{Nrd}d),
$$

so the general twisting theorem specializes to

$$
\operatorname{JL}(\rho\otimes\chi)
\cong\operatorname{JL}(\rho)\otimes\chi,
$$

where the two occurrences mean norm and determinant twist, respectively. Unramified twisting preserves $c_D$, $a_D$, and every compact-unit type. It preserves $a_G$ and the newvector level. It multiplies characteristic values on a norm-valuation-$m$ class by $\chi(\varpi)^m$.

For factors it replaces $\mu(\varpi)$ by $\mu(\varpi)\chi(\varpi)$ in the special Euler factor. For supercuspidals the $L$-factor remains one, while the root number is multiplied by the predictable unramified scalar determined by the analytic conductor:

$$
\epsilon(1/2,\pi\otimes\chi,\psi)
=\chi(\varpi)^{a_G(\pi)}\epsilon(1/2,\pi,\psi)
$$

under the convention that $\chi$ is evaluated on arithmetic-valuation uniformizers. If the opposite reciprocity convention is used to name the character, the scalar is inverted. The representation-theoretic statement in terms of $\chi(\varpi)$ has no such ambiguity.

Unramified twisting also reduces nonunitary questions to unitary ones. Every essentially square-integrable representation has an unramified real twist that is unitary. Prove orthogonality or formal-degree statements there, then twist back using the formulas above.

### 15.2 Automorphisms of the coefficient field

Let $\tau$ be an automorphism of the algebraically closed coefficient field $C$. Applying $\tau$ to matrices and scalar values produces representations ${}^\tau\rho$ and ${}^\tau\pi$. Since the matching relation is defined over $K$ and the sign $-1$ is rational,

$$
\Theta_{{}^\tau\pi}(g)
=\tau(\Theta_\pi(g))
=-\tau(\Theta_\rho(d))
=-\Theta_{{}^\tau\rho}(d).
$$

Uniqueness gives

$$
\boxed{\ \operatorname{JL}({}^\tau\rho)
\cong{}^\tau\operatorname{JL}(\rho).\ }
$$

Thus the correspondence is equivariant under coefficient automorphisms. A Schur index can obstruct the existence of a model over a smaller field even when the orbit of the isomorphism class is stable.

The equivariance just proved identifies the fields of rationality of the two isomorphism classes. It does **not** by itself prove equality of Schur indices or the existence of models over every smaller field; those are separate descent questions, so no stronger assertion is needed here.

Conductors and dimensions are integers and remain unchanged. Formal degrees are rational under our measures and remain unchanged. For local factors, coefficient automorphisms act on the Laurent-polynomial coefficients and on the chosen algebraic value of $q^{1/2}$, not on the complex variable $s$. The precise epsilon-factor formula also moves the additive character:

$$
\tau\!\left(\epsilon(s,\pi,\psi)\right)
=\epsilon(s,{}^\tau\!\pi,{}^\tau\!\psi),
\qquad
{}^\tau\!\psi=\tau\circ\psi.
$$

The same formula holds for $\rho$. If $\tau$ fixes the values of $\psi$, one may keep $\psi$ unchanged. This qualification prevents a Gauss sum from being declared invariant while its additive character has actually moved.

### 15.3 Changing the additive character

The correspondence itself does not depend on $\psi$. Epsilon factors do. If

$$
\psi_a(x)=\psi(ax),\qquad a\in K^\times,
$$

then the degree-two change-of-character formula is

$$
\epsilon(s,\pi,\psi_a)
=\omega_\pi(a)|a|^{2(s-1/2)}
\epsilon(s,\pi,\psi).
$$

The same formula holds for $\rho$, with $\omega_\rho$. Since central characters agree, epsilon compatibility for $\psi$ implies compatibility for every $\psi_a$.

**Proof.** In the Fourier transform replace $y$ by $ay$. Self-dual measure scales by $|a|^{\dim_K A/2}=|a|^2$, while the multiplicative change of variables contributes the norm power. The central scalar $a$ acts with determinant $a^2$ and through $\omega(a)$. Collecting the factors yields the displayed exponent. $\square$

If $\psi$ has nonzero conductor exponent, the monomial expression for epsilon factors must include that shift. The intrinsic functional equation is safer than transplanting the conductor-zero exponent without correction.

## 16. The precise image and the missing representations

### 16.1 Essentially square-integrable representations

The image of transfer is exactly

$$
\{\operatorname{St}\otimes\mu\}
\qquad\sqcup\qquad
\{\text{supercuspidal representations of }G\}.
$$

These are precisely the essentially square-integrable irreducibles. A unitary Steinberg coefficient decays like $q^{-m}$ along the Cartan ray, so its square is summable with the Cartan volume growth. A supercuspidal coefficient is compactly supported modulo $Z$. Twists by nonunitary unramified characters give the essentially square-integrable forms.

On $D^\times$, every irreducible is square-integrable modulo $Z$ after a unitary twist because $D^\times/Z$ is compact. Local Jacquet--Langlands is therefore a bijection between the full anisotropic dual and the elliptic part of the split dual. It is not a bijection between full irreducible duals.

### 16.2 Why irreducible principal series are absent

Every irreducible principal series

$$
I(\chi_1,\chi_2),\qquad
\chi_1\chi_2^{-1}\ne|\cdot|^{\pm1},
$$

is absent. Its regular elliptic character is zero. If it were the transfer of $\rho$, the defining identity would force $\Theta_\rho$ to vanish on every regular element of $D^\times$. That regular set has full measure in the compact quotient, and ordinary character orthogonality would force the nonzero irreducible character to be zero, an impossibility.

The absence is structural, not merely a mismatch of conductors. Principal series are built from the split torus $K^\times\times K^\times$. The division algebra contains no split torus. Their two Satake parameters and their two $K$-rational eigenlines have no anisotropic counterpart.

One-dimensional split representations $\mu\circ\det$ are absent for the same image reason: they are not essentially square-integrable. Their elliptic characters are not zero, but they represent the negative of Steinberg in the elliptic quotient. The actual division norm character transfers to Steinberg, not to the determinant character.

### 16.3 Boundary phenomena at reducibility

At the exceptional ratios, normalized induction has two constituents:

$$
0\to\mu\circ\det\to
I(\mu|\cdot|^{-1/2},\mu|\cdot|^{1/2})
\to\operatorname{St}\otimes\mu\to0.
$$

The middle representation has zero elliptic character, so

$$
\Theta_{\mu\circ\det}(g)
+\Theta_{\operatorname{St}\otimes\mu}(g)=0
$$

on the elliptic regular set. Transfer selects the special constituent because it is discrete series. The character constituent is its additive inverse only after passage to the elliptic Grothendieck quotient.

This distinction rules out three common errors.

- The reducible principal series itself is not the transfer; transfer pairs irreducibles.
- The determinant character is not the transfer merely because its elliptic character differs only by a sign.
- Reversing the order of the inducing characters changes the extension structure but not the two constituents; it does not change which constituent transfers.

There are no other boundary cases. An irreducible principal series never becomes essentially square-integrable under a character twist, while every Steinberg twist remains in the image.

## 17. The local dictionary for global transfer

### 17.1 The transfer table

The theorem and its compatibilities may be collected without suppressing exceptional normalizations.

| division-side datum $\rho$ | split transfer $\operatorname{JL}(\rho)$ | conductor comparison | standard $L$-factor |
|---|---|---|---|
| $\mu\circ\operatorname{Nrd}$, $a(\mu)=0$ | $\operatorname{St}\otimes\mu$ | $a_D=0$, $a_G=a_{\mathrm{an}}=1$ | $L(s+1/2,\mu)$ |
| $\mu\circ\operatorname{Nrd}$, $a(\mu)>0$ | $\operatorname{St}\otimes\mu$ | $a_D=a_G=2a(\mu)$ | $1$ |
| regular unramified pair, $a_E(\theta)=n$ | supercuspidal $\pi_G(E,\theta)$ | $a_D=a_G=2n$ | $1$ |
| regular tame ramified pair, $a_E(\theta)=n$ | supercuspidal $\pi_G(E,\theta)$ | $a_D=a_G=n+1$ | $1$ |
| higher-dimensional wild Clifford datum | unique supercuspidal with negative matching character | $a_G=c_D+1=a_D$ | $1$ |

For every row:

$$
\omega_{\operatorname{JL}(\rho)}=\omega_\rho,
$$

$$
\operatorname{JL}(\rho\otimes\chi)
=\operatorname{JL}(\rho)\otimes\chi,
$$

$$
\operatorname{JL}(\rho^\vee)
=\operatorname{JL}(\rho)^\vee,
$$

and

$$
\epsilon(s,\operatorname{JL}(\rho),\psi)
=\epsilon(s,\rho,\psi).
$$

For unitary representations and the quotient measures fixed in Chapter 1,

$$
d_G(\operatorname{JL}(\rho))
=d_{G'}(\rho)=\frac{q-1}{2}\dim\rho.
$$

The character identity that determines every entry remains

$$
\boxed{\ \Theta_{\operatorname{JL}(\rho)}(g)
=-\Theta_\rho(d),\qquad P_g=P_d.\ }
$$

The polynomial equality is the class orientation, the minus sign is spectral, and equality of unnormalized orbital integrals is the function-transfer normalization.

### 17.2 What Book 94 may use

At a finite place where a global quaternion algebra is split, its multiplicative group is already $\mathrm{GL}_2(K)$ and no local inner-form transfer is needed. At a finite ramified place, Book 94 may use the following local package.

- Every irreducible local quaternionic component has one and only one discrete-series transfer.
- Matching regular classes have equal trace and norm and equal Weyl discriminant.
- Matching test functions have equal orbital integrals and traces differing by the fixed minus sign.
- Central characters, determinant/norm twists, contragredients, standard local factors, and epsilon factors agree under transfer.
- Higher-dimensional quaternionic components transfer to supercuspidals; norm characters transfer to Steinberg twists.
- Conductors agree in every ramified or higher-dimensional case, while an unramified norm character has the explicit $0\mapsto1$ level shift.
- With the compatible quotient measures, formal degrees agree.
- Tame pair labels are identical after the normalized compatible extension and rectifier are fixed; wild components are covered by the character theorem without a false tame label.

These statements are local and were proved locally. A global trace comparison may multiply them place by place, but no global automorphic theorem was used to establish any one of them. In particular, global Jacquet--Langlands will assemble the local bijections; it will not retroactively justify their existence.

### 17.3 Conclusion

Local Jacquet--Langlands is governed by a small piece of geometry with unusually large consequences. A regular element on either inner form generates a quadratic étale algebra. The division condition removes the split algebra and leaves precisely the quadratic fields, so characteristic polynomial gives an exact bijection between division regular classes and split elliptic classes. Their centralizers are the same tori, their Weyl discriminants are the same quantity

$$
\left|\frac{\operatorname{trace}^2-4\operatorname{norm}}
{\operatorname{norm}}\right|,
$$

and their orbital integrals can be compared with transfer factor $+1$.

The representation-theoretic sign comes from somewhere different. A principal series has no elliptic fixed line and hence zero elliptic character. At a reducibility point its determinant character and Steinberg constituent therefore have opposite elliptic characters. Since a division norm character has the positive norm value, Steinberg must carry the negative one. The tree's vertex-edge complex extends this calculation to every depth: it turns finite compact character orthogonality into elliptic orthogonality and converts each division irreducible into exactly one discrete-series character. Integrality of the cellular trace, together with norm one, is what upgrades a virtual comparison to a bijection.

Once the character identity is established, its stability becomes a source of structure. Scaling matching elements proves equality of central characters. Multiplying their common norm proves twisting compatibility. Inversion proves compatibility with contragredients. The last congruence layer proves the conductor comparison, while the leading character germ proves the formal-degree identity under explicit quotient measures. Fourier transform on the two degree-two algebras proves equality of zeta-integral factors and reduces tame epsilon constants to finite Gauss sums. None of these consequences asks dimension to be preserved, and none hides the exceptional maximal-order exponent of an unramified norm character.

The final correspondence is therefore both canonical and concrete. It covers every wild Clifford representation without pretending that wild data are tame, gives explicit formulas for unramified and ramified admissible pairs where those formulas are honest, excludes every irreducible principal series for a geometric reason, and supplies exactly the local character, level, factor, and symmetry data needed for global transfer. Two groups with radically different visible representation theories have one common elliptic spectrum; local Jacquet--Langlands is the precise identification of that spectrum.
