# Algebraic de Rham Cohomology and Gauss--Manin Connections

## Contents

1. [Differentiating algebraic families](#1-differentiating-algebraic-families)
   - [The three questions](#11-the-three-questions)
   - [Standing conventions](#12-standing-conventions)
   - [What smoothness contributes](#13-what-smoothness-contributes)
2. [Differential forms and the de Rham complex](#2-differential-forms-and-the-de-rham-complex)
   - [Universal first derivatives](#21-universal-first-derivatives)
   - [Higher forms and signs](#22-higher-forms-and-signs)
   - [Relative and absolute differentials](#23-relative-and-absolute-differentials)
   - [Functoriality](#24-functoriality)
3. [Algebraic de Rham cohomology](#3-algebraic-de-rham-cohomology)
   - [Why hypercohomology is necessary](#31-why-hypercohomology-is-necessary)
   - [Definitions and affine computation](#32-definitions-and-affine-computation)
   - [The two hypercohomology spectral sequences](#33-the-two-hypercohomology-spectral-sequences)
   - [Products and graded commutativity](#34-products-and-graded-commutativity)
   - [The two-factor Kunneth formula](#35-the-two-factor-kunneth-formula)
4. [First computations and characteristic boundaries](#4-first-computations-and-characteristic-boundaries)
   - [Affine space and the algebraic Poincare lemma](#41-affine-space-and-the-algebraic-poincare-lemma)
   - [The punctured line](#42-the-punctured-line)
   - [Projective space](#43-projective-space)
   - [Why characteristic matters](#44-why-characteristic-matters)
5. [The Hodge filtration](#5-the-hodge-filtration)
   - [Filtration by form degree](#51-filtration-by-form-degree)
   - [The Hodge-to-de Rham spectral sequence](#52-the-hodge-to-de-rham-spectral-sequence)
   - [Degeneration versus splitting](#53-degeneration-versus-splitting)
   - [Chern classes from logarithmic differentials](#54-chern-classes-from-logarithmic-differentials)
6. [Smooth proper curves](#6-smooth-proper-curves)
   - [The two-term relative complex](#61-the-two-term-relative-complex)
   - [Degeneration in every characteristic](#62-degeneration-in-every-characteristic)
   - [The Hodge exact sequence](#63-the-hodge-exact-sequence)
   - [Finiteness and arbitrary base change](#64-finiteness-and-arbitrary-base-change)
7. [Cup products and duality on curves](#7-cup-products-and-duality-on-curves)
   - [The de Rham trace](#71-the-de-rham-trace)
   - [The perfect pairing in degree one](#72-the-perfect-pairing-in-degree-one)
   - [The Hodge bundle is Lagrangian](#73-the-hodge-bundle-is-lagrangian)
   - [Maps of curves and adjointness](#74-maps-of-curves-and-adjointness)
8. [Connections as algebraic differentiation](#8-connections-as-algebraic-differentiation)
   - [Connections and horizontal sections](#81-connections-and-horizontal-sections)
   - [Curvature and integrability](#82-curvature-and-integrability)
   - [Tensor operations and de Rham complexes with coefficients](#83-tensor-operations-and-de-rham-complexes-with-coefficients)
   - [Change of base](#84-change-of-base)
9. [Constructing the Gauss--Manin connection](#9-constructing-the-gauss--manin-connection)
   - [Filtering the absolute de Rham complex](#91-filtering-the-absolute-de-rham-complex)
   - [The connection and its Leibniz rule](#92-the-connection-and-its-leibniz-rule)
   - [Integrability, functoriality, and products](#93-integrability-functoriality-and-products)
   - [Base change](#94-base-change)
10. [Transversality and variation of Hodge structure](#10-transversality-and-variation-of-hodge-structure)
    - [Griffiths transversality](#101-griffiths-transversality)
    - [The Kodaira--Spencer class](#102-the-kodaira--spencer-class)
    - [The Higgs map for a family of curves](#103-the-higgs-map-for-a-family-of-curves)
    - [Duality and the second fundamental form](#104-duality-and-the-second-fundamental-form)
11. [De Rham cohomology of abelian schemes](#11-de-rham-cohomology-of-abelian-schemes)
    - [Invariant forms and the first Hodge sequence](#111-invariant-forms-and-the-first-hodge-sequence)
    - [The exterior algebra theorem](#112-the-exterior-algebra-theorem)
    - [Gauss--Manin and the group law](#113-gauss--manin-and-the-group-law)
    - [The universal vector extension viewpoint](#114-the-universal-vector-extension-viewpoint)
12. [Dual abelian schemes, polarizations, and isogenies](#12-dual-abelian-schemes-polarizations-and-isogenies)
    - [The Poincare class and de Rham duality](#121-the-poincare-class-and-de-rham-duality)
    - [Polarization forms](#122-polarization-forms)
    - [Horizontality](#123-horizontality)
    - [Isogeny invariance](#124-isogeny-invariance)
13. [An explicit elliptic family](#13-an-explicit-elliptic-family)
    - [The Legendre family and a cohomology basis](#131-the-legendre-family-and-a-cohomology-basis)
    - [Reduction of differentials](#132-reduction-of-differentials)
    - [The connection matrix](#133-the-connection-matrix)
    - [The Picard--Fuchs equation](#134-the-picard--fuchs-equation)
14. [The de Rham package for later arithmetic geometry](#14-the-de-rham-package-for-later-arithmetic-geometry)
    - [A reusable theorem package](#141-a-reusable-theorem-package)
    - [Failure modes and hypothesis checks](#142-failure-modes-and-hypothesis-checks)
    - [Conclusion](#143-conclusion)

## 1. Differentiating algebraic families

Algebraic geometry can record variation without using analytic paths. A function varies through
its universal differential, a line bundle varies through its infinitesimal transition functions,
and a cohomology class in a smooth family varies through the Gauss--Manin connection. The aim of
this book is to build that chain from the ground up and to show that it is compatible with the
structures already available on curves and abelian schemes.

### 1.1 The three questions

Three questions organize the theory. First, given a smooth scheme $X$ over a base $S$, what
cohomology theory is obtained by placing functions, one-forms, and higher forms in one complex?
The answer is relative algebraic de Rham cohomology

$$
H^n_{\mathrm{dR}}(X/S)=
\mathbb H^n(X,\Omega^\bullet_{X/S}).
$$

Second, when $f:X\to S$ is proper and smooth, when do these groups form vector bundles on $S$ and
commute with changing the base? Proper coherent cohomology and the Hodge-to-de Rham spectral
sequence answer this question. For curves the answer is especially complete: the spectral
sequence degenerates for elementary reasons in every characteristic, producing a short exact
Hodge sequence.

Third, if $S$ itself varies over $T$, how does a relative class change along $S/T$? The absolute
complex $\Omega^\bullet_{X/T}$ contains forms pulled back from $S$. Filtering by the number of such
base differentials produces a first differential

$$
\nabla:H^n_{\mathrm{dR}}(X/S)
\longrightarrow
\Omega^1_{S/T}\otimes H^n_{\mathrm{dR}}(X/S).
$$

This is the Gauss--Manin connection. Its Leibniz rule, zero curvature, compatibility with products,
and transversality to the Hodge filtration all come from the single filtered complex that creates
it.

### 1.2 Standing conventions

All complexes are cohomological. For a morphism $f:X\to S$, $\Omega^p_{X/S}$ denotes the $p$th
exterior power of the sheaf of Kahler differentials. The relative de Rham complex begins in degree
zero:

$$
\Omega^\bullet_{X/S}=
[\mathcal O_X\xrightarrow d\Omega^1_{X/S}\xrightarrow d
\Omega^2_{X/S}\to\cdots].
$$

If $f$ is smooth of relative dimension $d$, each $\Omega^p_{X/S}$ is finite locally free and
vanishes for $p>d$. A **smooth proper curve** over $S$ means a smooth, proper, finitely presented
morphism of pure relative dimension one with geometrically connected fibers. An abelian scheme has
the meaning fixed in Book 35: it is a smooth proper finitely presented group scheme with connected
geometric fibers.

Most relative finiteness statements are made over a locally noetherian base. The connection is
constructed for a tower

$$
X\xrightarrow f S\xrightarrow g T
$$

in which $f$ is smooth and proper and $g$ is smooth, unless a weaker exactness assumption is
explicitly stated. Smoothness of $g$ ensures that base differentials are locally free and that the
cotangent sequence used in the construction is exact on the left. A field is never silently
assumed algebraically closed or perfect.

Books 9 and 15 supply relative duality and coherent base change for curves. Book 7a supplies
hypercohomology, filtered complexes, products, and convergence. Book 35 supplies dual abelian
schemes, the Poincare bundle, polarizations, and isogenies. We recall each interface when it enters
and prove the specifically de Rham assertions here.

### 1.3 What smoothness contributes

Smoothness is not decorative. It says that infinitesimal directions are represented by a vector
bundle $\Omega^1_{X/S}$, that exterior powers have the expected ranks, and that the de Rham complex
has length bounded by the relative dimension. It also gives the exact cotangent sequence for a
smooth tower:

$$
0\longrightarrow f^*\Omega^1_{S/T}
\longrightarrow\Omega^1_{X/T}
\longrightarrow\Omega^1_{X/S}\longrightarrow0. \tag{1.1}
$$

If $X/S$ is singular, $\Omega^1_{X/S}$ can have torsion and need not be the dualizing sheaf. Book 9
explained this at a node. The complex of ordinary differentials on a singular fiber is therefore
not a flat replacement for the smooth de Rham theory. Logarithmic, derived, or crystalline
constructions repair different aspects of that failure, but none is to be confused with the
smooth theory developed here.

Properness has a different role. It makes the coherent cohomology of every $\Omega^p$ finite over
the base. Smoothness without properness still defines de Rham cohomology, but its dimensions and
behavior in families can be much less controlled. The punctured affine line will be a useful
example: it has a genuine degree-one de Rham class, but no proper trace pairing.

## 2. Differential forms and the de Rham complex

The de Rham complex is forced by two demands: differentiation must satisfy the product rule, and a
second derivative must vanish. This chapter constructs the objects carrying those demands and
fixes the sign conventions needed later for products and connections.

### 2.1 Universal first derivatives

For a ring map $R\to A$, an $R$-derivation from $A$ to an $A$-module $M$ is an additive map
$D:A\to M$ satisfying

$$
D(ab)=aD(b)+bD(a),\qquad D(r)=0\quad(r\in R).
$$

There is an $A$-module $\Omega^1_{A/R}$ and a universal derivation $d:A\to\Omega^1_{A/R}$ such that

$$
\operatorname{Hom}_A(\Omega^1_{A/R},M)
\simeq\operatorname{Der}_R(A,M). \tag{2.1}
$$

One construction takes the free $A$-module on symbols $da$ and divides by the displayed relations.
Equivalently, if $I$ is the kernel of multiplication $A\otimes_RA\to A$, then

$$
\Omega^1_{A/R}\simeq I/I^2,
\qquad da=(1\otimes a-a\otimes1)\bmod I^2. \tag{2.2}
$$

The second description explains why differentials measure the first infinitesimal neighborhood of
the diagonal.

For $A=R[x_1,\ldots,x_m]$, the module is free on $dx_1,\ldots,dx_m$. If
$A=R[x_1,\ldots,x_m]/(F_1,\ldots,F_r)$, the conormal sequence gives

$$
(F_1,\ldots,F_r)/(F_1,\ldots,F_r)^2
\longrightarrow\bigoplus_iA\,dx_i
\longrightarrow\Omega^1_{A/R}\longrightarrow0,
$$

and the first arrow sends $F_j$ to $dF_j=\sum_i(\partial F_j/\partial x_i)dx_i$. These affine
constructions localize and glue to $\Omega^1_{X/S}$.

### 2.2 Higher forms and signs

Set $\Omega^p_{A/R}=\bigwedge_A^p\Omega^1_{A/R}$. There is a unique sequence of additive maps

$$
d:\Omega^p_{A/R}\longrightarrow\Omega^{p+1}_{A/R}
$$

extending the universal derivation and satisfying

$$
d(\alpha\wedge\beta)=d\alpha\wedge\beta
+(-1)^p\alpha\wedge d\beta,
\qquad \alpha\in\Omega^p. \tag{2.3}
$$

On a pure expression it is

$$
d(a_0\,da_1\wedge\cdots\wedge da_p)
=da_0\wedge da_1\wedge\cdots\wedge da_p. \tag{2.4}
$$

Formula (2.4) respects the relations defining exterior powers and immediately gives $d^2=0$.
Thus $\Omega^\bullet_{A/R}$ is a differential graded algebra. Its multiplication is graded
commutative:

$$
\alpha\wedge\beta=(-1)^{pq}\beta\wedge\alpha.
$$

The sheaf version gives $\Omega^\bullet_{X/S}$. On a smooth relative $d$-fold it ends at
$\Omega^d_{X/S}$. For a curve, it is only

$$
[\mathcal O_X\xrightarrow d\Omega^1_{X/S}]. \tag{2.5}
$$

The brevity of (2.5), combined with the fact that coherent cohomology on a proper curve occupies
degrees zero and one, is the source of the complete calculations in Chapters 6 and 7.

### 2.3 Relative and absolute differentials

For ring maps $T\to R\to A$, universality gives a right-exact sequence

$$
A\otimes_R\Omega^1_{R/T}\longrightarrow
\Omega^1_{A/T}\longrightarrow\Omega^1_{A/R}\longrightarrow0. \tag{2.6}
$$

Flatness of $A$ over $R$ alone does not make the first arrow injective: in characteristic $p$, the
finite free map $k[t]\to k[x]$ with $t\mapsto x^p$ kills $dt$. In the smooth tower used here,
where both $R/T$ and $A/R$ are smooth, the cotangent transitivity sequence is short exact and
sheafifies to (1.1). It says that an absolute differential consists of a base component and a
relative component, although there is generally no canonical splitting.
Choosing a splitting would amount to choosing a horizontal distribution; the Gauss--Manin
connection will be canonical precisely because it is extracted without choosing one.

Wedge powers of (1.1) carry a filtration. If $F^a\Omega^n_{X/T}$ is the image of

$$
f^*\Omega^a_{S/T}\otimes\Omega^{n-a}_{X/T}
\longrightarrow\Omega^n_{X/T},
$$

then

$$
\operatorname{gr}^a_F\Omega^n_{X/T}
\simeq f^*\Omega^a_{S/T}\otimes\Omega^{n-a}_{X/S}. \tag{2.7}
$$

The absolute differential carries $F^a$ into $F^a$, so this is a filtration by subcomplexes. The
part of $d$ that raises $a$ by one will become differentiation on the base.

### 2.4 Functoriality

For a commutative square

$$
\begin{array}{ccc}
X'&\xrightarrow u&X\\
\downarrow&&\downarrow\\
S'&\xrightarrow v&S,
\end{array}
$$

there is a natural pullback map

$$
u^*\Omega^1_{X/S}\longrightarrow\Omega^1_{X'/S'}.
$$

It extends multiplicatively to a morphism of de Rham complexes. If the square is cartesian and
$S'\to S$ is arbitrary while $X/S$ is smooth, then

$$
u^*\Omega^p_{X/S}\xrightarrow{\sim}\Omega^p_{X'/S'} \tag{2.8}
$$

because differentials of a finitely presented smooth algebra commute with base change and exterior
powers commute with pullback of finite locally free modules.

Contravariance is important. A map $u:X'\to X$ produces

$$
u^*:H^n_{\mathrm{dR}}(X/S)\longrightarrow
H^n_{\mathrm{dR}}(X'/S)
$$

when both schemes lie over the same base. Composition and identities follow already on forms. If
$u$ varies in a family over $S/T$, the same construction will be horizontal for the Gauss--Manin
connections because it respects the filtration (2.7).

## 3. Algebraic de Rham cohomology

Taking only global closed forms misses gluing classes, while taking coherent cohomology term by
term misses the differential joining the terms. Hypercohomology retains both. This chapter makes
that assertion concrete and imports only the derived machinery established in Book 7a.

### 3.1 Why hypercohomology is necessary

On an affine scheme, quasi-coherent sheaves have no higher cohomology, so the cohomology of global
forms is enough. On a proper curve, however, $H^1(X,\mathcal O_X)$ is usually nonzero. A degree-one
de Rham class may therefore arise either from a global one-form or from functions that glue only
up to differentials. A construction that remembers just one source cannot be correct.

The appropriate total object is derived global sections:

$$
R\Gamma(X,\Omega^\bullet_{X/S}).
$$

Locally on an affine base $S=\operatorname{Spec}R$, it is a complex of $R$-modules. Its cohomology
simultaneously accounts for the sheaf differential and for the Cech or derived differential that
measures gluing.

### 3.2 Definitions and affine computation

For an $S$-scheme $X$, define

$$
R\Gamma_{\mathrm{dR}}(X/S)=R\Gamma(X,\Omega^\bullet_{X/S}),
\qquad
H^n_{\mathrm{dR}}(X/S)=H^nR\Gamma_{\mathrm{dR}}(X/S). \tag{3.1}
$$

For a morphism $f:X\to S$, the relative derived de Rham pushforward is

$$
Rf_*\Omega^\bullet_{X/S},
$$

and its cohomology sheaves are denoted

$$
\mathcal H^n_{\mathrm{dR}}(X/S)
=R^nf_*\Omega^\bullet_{X/S}. \tag{3.2}
$$

The notation in (3.2) means hypercohomology sheaves, not $R^nf_*$ applied to one sheaf.

If $X=\operatorname{Spec}A$ and $S=\operatorname{Spec}R$, every $\Omega^p_{A/R}$ is quasi-coherent
and affine-acyclic. Hence

$$
H^n_{\mathrm{dR}}(X/S)
\simeq H^n(\Omega^\bullet_{A/R}). \tag{3.3}
$$

This follows from the termwise hypercohomology spectral sequence, which has only its zeroth
coherent-cohomology row. Formula (3.3) is useful for computations, but it should not be extended to
nonaffine schemes without justification.

### 3.3 The two hypercohomology spectral sequences

There are two complementary ways to approach (3.1). Filtering by the form degree gives

$$
E_1^{p,q}=H^q(X,\Omega^p_{X/S})
\Longrightarrow H^{p+q}_{\mathrm{dR}}(X/S), \tag{3.4}
$$

with $d_1$ induced by exterior differentiation. This is the Hodge-to-de Rham spectral sequence.
It is the main computational tool for proper smooth schemes because each $E_1$ term is coherent
cohomology.

Filtering a resolution through the cohomology sheaves of the de Rham complex gives

$$
E_2^{a,b}=H^a(X,\mathcal H^b(\Omega^\bullet_{X/S}))
\Longrightarrow H^{a+b}_{\mathrm{dR}}(X/S). \tag{3.5}
$$

On the small Zariski site in characteristic zero, local exactness of the de Rham complex is not an
algebraic Zariski Poincare lemma in general, so the sheaves in (3.5) need not collapse to constants.
Sequence (3.4), not an unjustified local-constancy assertion, is the reliable algebraic tool.

For a smooth proper $d$-fold over a noetherian ring, $p$ lies between $0$ and $d$, and coherent
cohomology vanishes in sufficiently high degree. Thus (3.4) is bounded and converges strongly.
Its limiting terms are the graded pieces of a filtration; they are not automatically direct
summands.

### 3.4 Products and graded commutativity

Wedge product is a morphism of complexes

$$
\Omega^\bullet_{X/S}\otimes\Omega^\bullet_{X/S}
\longrightarrow\Omega^\bullet_{X/S}.
$$

After derived global sections it produces cup products

$$
H^m_{\mathrm{dR}}(X/S)\otimes
H^n_{\mathrm{dR}}(X/S)
\longrightarrow H^{m+n}_{\mathrm{dR}}(X/S). \tag{3.6}
$$

The total sign combines the Cech degree and form degree. If a cochain has bidegree $(p,q)$, its
total degree is $p+q$; interchanging total cochains of degrees $m,n$ contributes $(-1)^{mn}$.
Consequently

$$
x\smile y=(-1)^{mn}y\smile x. \tag{3.7}
$$

The form-degree filtration is multiplicative:

$$
F^aH^m_{\mathrm{dR}}\smile F^bH^n_{\mathrm{dR}}
\subseteq F^{a+b}H^{m+n}_{\mathrm{dR}}. \tag{3.8}
$$

Every page of (3.4) therefore has a compatible product, and each differential is a derivation.
This compatibility will prove that polarization pairings are horizontal and that the cohomology
of an abelian scheme is an exterior algebra.

### 3.5 The two-factor Kunneth formula

External products reduce the study of sheaves on a product to two factors. If $\mathcal F$ and
$\mathcal G$ are sheaves on $k$-schemes $X$ and $Y$, their external product is

$$
\mathcal F\boxtimes\mathcal G
=\mathrm{pr}_1^*\mathcal F\otimes_{\mathcal O}\mathrm{pr}_2^*\mathcal G
$$

on $X\times_kY$. When $X$ and $Y$ are proper, each cohomology group of the box product should be
assembled from those of the factors; making this precise is the Kunneth problem. The Kunneth
theorem available so far in this series is the étale one of Book 23, which does not apply here:
coherent cohomology lives on the Zariski site, and its Künneth formula must be built from the
Čech models of Book 7b. This section proves exactly the statements consumed by Chapter 11: an
absolute form over a field and a relative form with locally free direct images.

The engine is a remark of homological algebra. Over a field, every complex splits into its
cohomology groups.

**Lemma 3.1 (splitting over a field).** Let $k$ be a field and let $C^\bullet$ be a complex of
$k$-vector spaces which vanishes in sufficiently negative and positive degrees. Then there is a
quasi-isomorphism, non-canonical,

$$
C^\bullet\;\simeq\;\bigoplus_i H^i(C)[-i],
$$

**Proof.** For each $i$ let $Z^i=\ker d^i$ and $B^i=\operatorname{im}d^{i-1}$, so $B^i\subseteq
Z^i$. Because every subspace of a vector space admits a complement, choose $H'^i\subseteq Z^i$
with $Z^i=B^i\oplus H'^i$, so $H'^i\simeq H^i(C)$; and choose $E^{i+1}\subseteq C^i$ mapping
isomorphically under $d^i$ onto $B^{i+1}$, possible because $d^i$ induces an isomorphism
$C^i/Z^i\xrightarrow{\sim}B^{i+1}$ and we lift a basis. Then $C^i=B^i\oplus H'^i\oplus E^{i+1}$
and $d^i$ kills $B^i\oplus H'^i$ and maps $E^{i+1}$ isomorphically onto $B^{i+1}$. Define
$\pi:C\to\bigoplus_iH^i(C)[-i]$ by projecting each $C^i=B^i\oplus H'^i\oplus E^{i+1}$ onto the
summand $H'^i$ and identifying it with $H^i(C)$. The target has zero differential, and $\pi$
commutes with differentials: for $v=b+h+c$, the differential $dv=d(c)$ lies in $B^{i+1}$, which
the projection to $H'^{i+1}$ kills, so $\pi(dv)=0=d\pi(v)$. The kernel of $\pi$ in degree $i$ is
$B^i\oplus E^{i+1}$, and the differential identifies these kernels isomorphically with one
another from degree to degree, so the kernel complex is exact. A degree-wise surjective morphism
of bounded complexes whose kernel is exact is a quasi-isomorphism: this follows by induction on
the width of the bounding interval from the long exact cohomology sequence of its short exact
sequence with the kernel. Hence $\pi$ is a quasi-isomorphism between bounded complexes. $\square$

**Lemma 3.2 (tensor product of split complexes).** Let $k$ be a field and let
$C^\bullet,D^\bullet$ be complexes of $k$-vector spaces, each zero outside finitely many degrees.
Equip the tensor-product double complex $D^{p,q}=C^p\otimes_kD^q$ with the commuting raw
differentials and its total differential as in Book 7a, Section 7.1. Then

$$
H^n\bigl(\operatorname{Tot}(C\otimes_kD)\bigr)
\simeq\bigoplus_{p+q=n}H^p(C)\otimes_kH^q(D).
$$

**Proof.** By Lemma 3.1 choose quasi-isomorphisms $u:C\to\bigoplus_iH^i(C)[-i]$ and
$v:D\to\bigoplus_jH^j(D)[-j]$; their tensor product is a morphism of double complexes and hence,
after totalization, a map of complexes. Since every term of a double complex built from vector
spaces is flat in the strongest possible sense — all exact sequences of $k$-vector spaces split —
totalizing a quasi-isomorphic pair of double complexes yields a quasi-isomorphism on total
complexes; explicitly, the cone of such a morphism is totalized from an exact double complex, and
an exact first-quadrant double complex has exact totalization because its column filtration
furnishes a convergent spectral sequence whose abutment is zero. It therefore suffices to compute
with the split complexes, where the differential is zero: there

$$
\operatorname{Tot}^n=\bigoplus_{p+q=n}H^p(C)\otimes_kH^q(D),
$$

with zero total differential, so the cohomology in degree $n$ is that direct sum itself.
$\square$

**Theorem 3.3 (two-factor Kunneth over a field).** Let $k$ be a field, let $X$ and $Y$ be
quasi-compact separated $k$-schemes, and let $\mathcal F$ and $\mathcal G$ be quasi-coherent
$\mathcal O_X$- and $\mathcal O_Y$-modules. Then for every $n$ there is a natural isomorphism

$$
H^n\bigl(X\times_kY,\,\mathcal F\boxtimes\mathcal G\bigr)
\simeq\bigoplus_{i+j=n}
H^i(X,\mathcal F)\otimes_kH^j(Y,\mathcal G). \tag{3.9}
$$

It is functorial in $\mathcal F$ and in $\mathcal G$, compatible with pullback along
morphisms $X'\to X$, $Y'\to Y$ over $k$, and associative under triple products.

**Proof.** Quasi-compactness gives finite affine open covers
$\mathfrak U=(U_i)_{i\in I}$ of $X$ and $\mathfrak V=(V_j)_{j\in J}$; separatedness makes every
finite intersection $U_I=\bigcap_{i\in I}U_i$ and $V_J=\bigcap_{j\in J}V_j$ affine. The family
$\mathfrak W=(U_i\times_kV_j)$ is a finite affine open cover of $X\times_kY$: each member is
affine because it is the spectrum of $\Gamma(U_i,\mathcal O)\otimes_k\Gamma(V_j,\mathcal O)$,
and its finite intersections are the schemes $(U_I\times_kV_J)$, again spectra of tensor
products. All three covers satisfy the hypotheses of the finite affine Cech model of Book 7b,
Theorem 4.2.

Write $A_{ij}=\Gamma(U_i\times V_j,\mathcal O)=\Gamma(U_i,\mathcal O)\otimes_k\Gamma(V_j,
\mathcal O)$. The sheaf $\mathcal F\boxtimes\mathcal G$ restricted to $U_i\times V_j$ is
quasi-coherent, associated to the module $\Gamma(U_i,\mathcal F)\otimes_k\Gamma(V_j,\mathcal G)$:
this is the affine dictionary of Book 7b, Chapter 2, applied twice, since pullback of a
quasi-coherent module to an affine open corresponds to tensoring its module over the coordinate
ring, and tensor products of modules correspond to tensor products of sheaves (Book 7b,
Theorem 2.7). Consequently sections over any intersection are given by

$$
\Gamma\bigl(U_I\times_kV_J,\mathcal F\boxtimes\mathcal G\bigr)
=\Gamma(U_I,\mathcal F)\otimes_k\Gamma(V_J,\mathcal G), \tag{3.10}
$$

because restriction of a quasi-coherent sheaf to an affine open localizes the module, and
localization commutes with tensor products over $k$.

Now form the double complex $D^{p,q}$ whose $(I,J)$-component, for $|I|=p+1$ and $|J|=q+1$, is
$\Gamma(U_I,\mathcal F)\otimes_k\Gamma(V_J,\mathcal G)$, with the horizontal differential
induced from the alternating Cech differential of $\mathfrak U$ on the first factor tensored by
the identity on the second, and the vertical differential defined symmetrically. The two raw
differentials commute because they act on different tensor factors. The identification (3.10)
exhibits $D^{p,q}$ as the degree-$(p,q)$ part of the alternating Cech complex
$\check C^\bullet(\mathfrak W,\mathcal F\boxtimes\mathcal G)$, and the alternating differential
of the product cover acts on the component indexed by
$(I,J)\subseteq(I',J')$ as the signed restriction; grouping those indices by which factor grows
shows that this signed restriction is exactly the total differential of $D$ under the convention
of Book 7a, Section 7.1, the sign being the Koszul sign attached to the horizontal degree. Thus

$$
\operatorname{Tot}(D)\;=\;\operatorname{Tot}\bigl(
\check C^\bullet(\mathfrak U,\mathcal F)\otimes_k\check C^\bullet(\mathfrak V,\mathcal G)\bigr),
$$

as complexes computing $R\Gamma(X\times_kY,\mathcal F\boxtimes\mathcal G)$. Both factors are
bounded complexes of vector spaces, so Lemma 3.2 computes their total cohomology as the graded
tensor product of the Cech cohomologies, and the Cech model of Book 7b, Theorem 4.2 identifies
those with the sheaf cohomologies of the two factors and of the product. Assembling the three
identifications gives (3.9).

Functoriality holds because every step — restriction of covers, the dictionary (3.10), and the
splitting maps of Lemma 3.1 after a choice made compatibly — is functorial in $\mathcal F$ and
$\mathcal G$; compatibility with pullback follows by applying the theorem over $X'$ and $Y'$ and
comparing the two Cech models through the refinement induced by the chosen covers and their
pullbacks. Associativity is proved by running the same argument over a triple product cover, or
by iterating (3.9) twice. $\square$

**Remark.** Over a general base ring the splitting lemma fails, and Tor terms can appear; the
correct general statement involves derived tensor products, which are not needed in this book.
What Chapter 11 needs is the relative form below, where local freeness on one side replaces the
field hypothesis.

The relative statement concerns a family $f:X\to S$ with a second family $g:Y\to S$, and
describes the direct images of the box product along $f\times g$ as sheaves on $S$. The proof
runs over an affine open of $S$ and therefore works with complexes of modules over a ring, for
which we need two substitutes for the splitting lemma. The first says that a complex whose
cohomology consists of projective modules receives a quasi-isomorphism from the direct sum of its
shifted cohomology groups; only this direction of formality is available, and only it is used.

**Lemma 3.4 (one-sided formality).** Let $R$ be a ring and let $C^\bullet$ be a bounded complex
of $R$-modules all of whose cohomology modules $H^i(C)$ are projective. Put
$P^\bullet=\bigoplus_iH^i(C)[-i]$, the direct sum of the cohomology modules placed in their own
degrees, with zero differential. Then there is a morphism of complexes $u:P\to C$ inducing the
identity on every cohomology module; in particular $u$ is a quasi-isomorphism.

**Proof.** Since $H^i(C)$ is projective, the surjection $Z^i=\ker d^i\twoheadrightarrow H^i(C)$
splits: choose an $R$-linear section $\sigma_i:H^i(C)\to Z^i$. Define $u^i:P^i=H^i(C)\to C^i$
to be $\sigma_i$. Because $\sigma_i$ lands in cycles and $d_P=0$, both composites around each
square vanish, so $u$ commutes with differentials. On cohomology, $u$ sends the class of $x$ to
the class of $\sigma_i(x)$, which is $x$ by construction. A morphism of bounded complexes that is
an isomorphism on every cohomology group is a quasi-isomorphism. $\square$

The second substitute controls tensor products. Over a field, exactness of tensoring made the
passage from a complex to its split model harmless; over a ring it is exactly here that flatness
is needed.

**Lemma 3.5 (tensoring with bounded flat complexes preserves quasi-isomorphisms).** Let $R$ be a
ring, let $Q^\bullet$ be a complex of flat $R$-modules supported in degrees in an interval
$[a,b]$, and let $\alpha:E^\bullet\to E'^\bullet$ be a quasi-isomorphism of complexes of
$R$-modules. Then

$$
\operatorname{Tot}(Q\otimes_R E)\longrightarrow
\operatorname{Tot}(Q\otimes_R E')
$$

is a quasi-isomorphism.

**Proof.** The proof has two steps. The first is the exactness claim used twice afterward:

_Claim._ If $W^\bullet$ is an exact complex of $R$-modules, then $\operatorname{Tot}(Q\otimes_RW)$
is exact.

_Proof of the claim._ Induct on the length $b-a$ of the supporting interval of $Q$. If $Q$
consists of a single flat module $M$ in one degree, then $\operatorname{Tot}(Q\otimes W)$ is
$M\otimes_RW$ up to shift; tensoring each term of the exact complex $W$ with the flat module $M$
preserves exactness term by term, so the total complex has zero cohomology. For the induction
step let $Q'$ be the stupid truncation that discards the top degree $b$, and apply the
functor $-\otimes_RW^q$ to the split-exact sequences of graded modules
$0\to Q'\to Q\to Q^b[-b]\to0$: since $Q^b$ is flat, the sequences remain exact in every
bidegree, and they commute with the differentials, so the total complexes form a short exact
sequence. Its long exact cohomology sequence exhibits the middle cohomology as sandwiched between
those of $\operatorname{Tot}(Q'\otimes W)$ and $\operatorname{Tot}(Q^b[-b]\otimes W)$, both
exact by induction, so the middle is exact. This proves the claim.

_Second step._ Now let $\alpha:E\to E'$ be an arbitrary quasi-isomorphism. Factor it through the
mapping cylinder: put $\operatorname{Cyl}^q=E'^{q}\oplus E^{q+1}\oplus E^{q}$ with differential
$d(e',e^{+},e)=\bigl(d_{E'}e'+\alpha e^{+},\,-de^{+},\,de\bigr)$, which squares to zero because
$d_{E'}\alpha=\alpha d$. The inclusion $i:E\to\operatorname{Cyl}$,
$e\mapsto(\alpha e,0,e)$, is a degreewise split injection and a quasi-isomorphism; the projection
$p:\operatorname{Cyl}\to E'$, $(e',e^{+},e)\mapsto e'$, is a degreewise split surjection with
$\alpha=p\circ i$; and the kernel of $p$ is the cone of $\mathrm{id}_E$, hence exact, so $p$ is a
quasi-isomorphism. Both factor maps are therefore quasi-isomorphisms whose defining short exact
sequences are split degree-wise, so tensoring those sequences with $Q$ preserves their exactness,
and the resulting short exact sequences of total complexes have flanking terms
$\operatorname{Tot}(Q\otimes\ker)$ or $\operatorname{Tot}(Q\otimes\operatorname{coker})$ which
are exact by the Claim, the kernels and cokernels being the exact cones of identity morphisms.
The long exact cohomology sequence then shows that both $i$ and $p$ remain quasi-isomorphisms
after tensoring with $Q$, and hence so does their composition

$$
\operatorname{Tot}(Q\otimes_R E)\xrightarrow{\ \mathrm{id}_Q\otimes i\ }
\operatorname{Tot}(Q\otimes_R\operatorname{Cyl})
\xrightarrow{\ \mathrm{id}_Q\otimes p\ }
\operatorname{Tot}(Q\otimes_RE').
$$

This proves the lemma. $\square$

The same argument, with the two factors interchanged throughout, shows that
$\operatorname{Tot}(E\otimes_RQ)\to\operatorname{Tot}(E'\otimes_RQ)$ is a quasi-isomorphism under
identical hypotheses on $Q$: the claim and the mapping-cylinder factorization are symmetric once
one filters by the supporting degrees of $Q$ instead of those of the cones involved.

**Theorem 3.6 (relative two-factor Kunneth).** Let $S$ be a locally noetherian scheme and let
$f:X\to S$ and $g:Y\to S$ be proper morphisms with $X$ and $Y$ covered by finitely many affine
opens. Let $\mathcal F$ be coherent on $X$ and $\mathcal G$ coherent on $Y$, and suppose that
every direct image sheaf $R^if_*\mathcal F$, $i\ge0$, is finite locally free on $S$. Then for
every $n$ there is a natural isomorphism of quasi-coherent sheaves on $S$,

$$
R^n(f\times g)_*\bigl(\mathcal F\boxtimes\mathcal G\bigr)
\simeq\bigoplus_{i+j=n}
R^if_*\mathcal F\otimes_{\mathcal O_S}R^jg_*\mathcal G, \tag{3.11}
$$

functorial in $\mathcal F$ and compatible with restriction to open subsets of $S$.

**Proof.** Isomorphisms of quasi-coherent sheaves are detected on affine opens, and all objects
in sight restrict well, so we may assume $S=\operatorname{Spec}R$ affine. Then $X$ and $Y$ are
quasi-compact separated schemes, and we choose finite affine covers $\mathfrak U$ and
$\mathfrak V$ as in the proof of Theorem 3.3, writing $C=\check C^\bullet(\mathfrak U,\mathcal F)$
and $D=\check C^\bullet(\mathfrak V,\mathcal G)$, both bounded complexes of $R$-modules. The
argument of Theorem 3.3 goes through verbatim over $R$: the product cover of $X\times_SY$ by the
spectra of the rings $\Gamma(U_i,\mathcal O)\otimes_R\Gamma(V_j,\mathcal O)$ is a finite affine
cover, sections over its intersections are given by the affine dictionary as
$\Gamma(U_I,\mathcal F)\otimes_R\Gamma(V_J,\mathcal G)$, and the alternating Cech complex of the
box product for that cover is the totalization of $C\otimes_RD$. By Book 7b, Theorem 4.2 and
Corollary 4.9,

$$
H^i(C)=H^i(X,\mathcal F)=\Gamma(S,R^if_*\mathcal F)=:M_i ,
$$

where the edge isomorphism of Corollary 4.9 applies because $S$ is affine and the sheaves
$R^if_*\mathcal F$ are quasi-coherent by Book 7b, Theorem 4.7. Each $M_i$ is a finite projective
$R$-module: a finite locally free sheaf on an affine scheme has module of global sections a
direct summand of a free module, by the standard partition-of-unity argument applied to a finite
cover trivializing the sheaf. In particular the $M_i$ are flat.

Let $P=\bigoplus_iM_i[-i]$. Lemma 3.4 supplies a quasi-isomorphism $u:P\to C$, and Lemma 3.5,
applied with the bounded complex $Q=P$ of flat modules inserted in the first tensor factor —
using the symmetric form recorded after that lemma — upgrades $u$ to a quasi-isomorphism

$$
\operatorname{Tot}(P\otimes_RD)\;\simeq\;\operatorname{Tot}(C\otimes_RD)
= R\Gamma\bigl(X\times_SY,\mathcal F\boxtimes\mathcal G\bigr),
$$

the equality holding in cohomology through the Cech model. Now $P\otimes_RD$ is the direct sum
over $i$ of the complexes $M_i\otimes_RD[-i]$; since $M_i$ is flat, the cohomology of
$M_i\otimes_RD$ in degree $j$ is $M_i\otimes_RH^j(D)$, and cohomology commutes with direct sums
of complexes. Hence

$$
H^n\bigl(\operatorname{Tot}(P\otimes_RD)\bigr)
=\bigoplus_{i+j=n}M_i\otimes_RH^j(D).
$$

Finally $H^j(D)=H^j(Y,\mathcal G)=\Gamma(S,R^jg_*\mathcal G)$, again by Corollary 4.9, and on
the affine scheme $S$ the module of sections of a tensor product of quasi-coherent sheaves is
the tensor product of their modules of sections. Assembling these identifications yields (3.11)
at the level of global sections over every affine open of $S$, and hence as sheaves. Functoriality
and compatibility with further restriction follow because each step was natural in $\mathcal F$.
$\square$

For Chapter 11 the theorem is applied with $S$ arbitrary, $X=Y=A$, and
$\mathcal F=\bigwedge^{a'}\omega_A$, $\mathcal G=\bigwedge^{a''}\omega_A$ pulled back under the
two projections, the local freeness hypothesis being supplied by the exterior algebra theorem
(11.2) together with local freeness of $\omega_A$ and of $R^1p_*\mathcal O_A$.

## 4. First computations and characteristic boundaries

Examples reveal both the strength and the limitations of algebraic differentiation. Affine space
is contractible in characteristic zero, the punctured line detects logarithmic forms, and positive
characteristic shows why one cannot transfer characteristic-zero intuition without checking
division by integers.

### 4.1 Affine space and the algebraic Poincare lemma

Let $R$ be a $\mathbf Q$-algebra and $A=R[x_1,\ldots,x_m]$. Then

$$
H^0(\Omega^\bullet_{A/R})=R,
\qquad H^n(\Omega^\bullet_{A/R})=0\quad(n>0). \tag{4.1}
$$

The proof is a contracting homotopy. Grade a monomial form

$$
x_1^{a_1}\cdots x_m^{a_m}
dx_{i_1}\wedge\cdots\wedge dx_{i_p}
$$

by total polynomial degree plus form degree, say $N=\sum a_i+p$. Let
$E=\sum x_i\partial/\partial x_i$ be the Euler vector field and $\iota_E$ contraction. Cartan's
direct calculation on monomials gives

$$
d\iota_E+\iota_Ed=N. \tag{4.2}
$$

For $N>0$, division by $N$ makes $N^{-1}\iota_E$ a homotopy from the identity to zero. Degree
zero consists exactly of $R$. This proves (4.1).

The same calculation proves homotopy invariance over a $\mathbf Q$-algebra:

$$
H^n_{\mathrm{dR}}(X\times\mathbf A^1/S)
\simeq H^n_{\mathrm{dR}}(X/S) \tag{4.3}
$$

whenever the product complex and hypercohomology comparison are defined with the usual
quasi-compact separated hypotheses. Expand forms polynomially in the affine coordinate and apply
the one-variable homotopy term by term. The need to divide by positive integers is explicit.

### 4.2 The punctured line

Let $k$ have characteristic zero and $A=k[t,t^{-1}]$. The de Rham complex is

$$
A\xrightarrow d A\,dt.
$$

Every Laurent one-form is a sum of $a_nt^n dt$. If $n\ne-1$, then

$$
t^n dt=d\left(\frac{t^{n+1}}{n+1}\right).
$$

The form $dt/t$ is not exact because an algebraic Laurent primitive would require a logarithm.
Therefore

$$
H^0_{\mathrm{dR}}(\mathbf G_m/k)=k,
\qquad H^1_{\mathrm{dR}}(\mathbf G_m/k)=k\,[dt/t], \tag{4.4}
$$

and higher groups vanish. For a split torus $\mathbf G_m^r$, tensoring the one-variable complexes
gives

$$
H^*_{\mathrm{dR}}(\mathbf G_m^r/k)
\simeq\bigwedge_k^*\langle d\log t_1,\ldots,d\log t_r\rangle. \tag{4.5}
$$

The class $d\log t$ is the local model for first Chern classes and for residues. Its existence also
shows why affine does not mean de Rham-acyclic.

### 4.3 Projective space

Let $k$ be any field. The coherent cohomology of differential forms on projective space gives

$$
H^q(\mathbf P^n_k,\Omega^p)=0\quad(p\ne q),
\qquad H^p(\mathbf P^n_k,\Omega^p)\simeq k. \tag{4.6}
$$

We prove both the Euler sequence and (4.6) from the twisting-sheaf machinery of Book 7b,
Chapter 6, which computes $H^q(\mathbf P^n_A,\mathcal O(m))$ for every ring $A$, every twist
$m$, and every degree $q$. Write $\mathbf P^n=\mathbf P^n_k$ with standard charts
$U_i=D_+(x_i)$ and coordinates $t_j=x_j/x_i$ on $U_i$, $j\ne i$, and set $t_i=1$.

**Lemma 4.9 (Euler sequence).** On $\mathbf P^n_k$, $n\ge1$, there is an exact sequence of
locally free sheaves

$$
0\longrightarrow\Omega^1_{\mathbf P^n/k}
\longrightarrow\mathcal O(-1)^{\oplus(n+1)}
\xrightarrow{\ \varphi\ }\mathcal O\longrightarrow0.
$$

**Proof.** By Lemma 6.2 of Book 7b, $\mathcal O(-1)|_{U_i}$ is free of rank one with basis
$x_i^{-1}$; hence the middle term is free on basis vectors $e_0^{(i)},\ldots,e_n^{(i)}$, and on
the overlap $U_i\cap U_j$ the two bases are related by $e_m^{(j)}=(x_i/x_j)\,e_m^{(i)}$, since
$x_j^{-1}=(x_i/x_j)x_i^{-1}$ in $(S_{x_ix_j})_{-1}$. Define $\varphi$ chart by chart by

$$
\varphi\bigl(e_m^{(i)}\bigr)=t_m=x_m/x_i\in(S_{x_i})_0 .
$$

This is compatible with the transitions: expressed in the $i$-th chart, $\varphi(e_m^{(j)})$
reads $(x_i/x_j)(x_m/x_i)=x_m/x_j$, which is the restriction of the same rule. On each chart
$\varphi(e_i^{(i)})=1$, so $\varphi$ is surjective as a map of sheaves. Note that
$\Omega^1_{\mathbf P^n/k}|_{U_i}$ is freely generated over $(S_{x_i})_0$ by the differentials
$dt_j$, $j\ne i$: the chart $U_i$ is an affine space over $k$ with coordinates $t_j$, and
Kahler differentials commute with localization. Define a chart-wise lift by

$$
\psi_i(dt_j)=e_j^{(i)}-t_j\,e_i^{(i)}\qquad(j\ne i).
$$

The $\psi_i$ glue to a global map $\psi:\Omega^1\to\mathcal O(-1)^{\oplus(n+1)}$: one must
check that $\psi_i(dt_m)$ and $\psi_l(dt_m)$ agree on $U_i\cap U_l$ after identifying bases. On
the overlap, from $x_m/x_i=(x_m/x_l)(x_l/x_i)$ and
$d(x_l/x_i)=-(x_l/x_i)^2\,d(x_i/x_l)$, the section $dt_m$ reads

$$
dt_m=-\,(x_m/x_l)\,(x_l/x_i)^2\,d(x_i/x_l)+(x_l/x_i)\,d(x_m/x_l).
$$

Applying $\psi_l$ to both summands and collecting, the $e_l^{(l)}$-coefficients cancel and leave

$$
\psi_l(dt_m)
=-\,(x_m/x_l)\,(x_l/x_i)^2\,e_i^{(l)}+(x_l/x_i)\,e_m^{(l)}.
$$

Converting bases through $e_a^{(l)}=(x_i/x_l)e_a^{(i)}$ turns the two coefficients into
$(x_m/x_l)(x_l/x_i)=x_m/x_i$ and $1$, so

$$
\psi_l(dt_m)=e_m^{(i)}-(x_m/x_i)\,e_i^{(i)}=\psi_i(dt_m),
$$

as required.

The composite $\varphi\circ\psi$ vanishes: $\varphi\psi_i(dt_j)=t_j-t_j=0$. Exactness at the
middle: suppose
$\sum_ma_me_m^{(i)}$ lies in $\ker\varphi|_{U_i}$, that is
$\sum_ma_mt_m=0$ in $(S_{x_i})_0$; then $\omega=\sum_{m\ne i}a_md t_m$ satisfies
$\psi_i(\omega)=\sum_ma_me_m^{(i)}-\bigl(\sum_{m\ne i}a_mt_m\bigr)e_i^{(i)}
=\sum_ma_me_m^{(i)}$, because the vanishing hypothesis gives
$\sum_{m\ne i}a_mt_m=-a_i$. Hence $\ker\varphi=\operatorname{im}\psi$ locally, and therefore
globally. Injectivity of $\psi$: if $\sum_{j\ne i}c_j(e_j-t_je_i)=0$, the coefficient of each
$e_j$, $j\ne i$, is $c_j$, so all $c_j$ vanish. All three verifications together give exactness
at every position. $\square$

Taking exterior powers converts the Euler sequence into the ladder used for the computation.
For a locally split short exact sequence $0\to\mathcal K\to\mathcal E\to\mathcal Q\to0$ there
are canonical exact sequences $0\to\bigwedge^p\mathcal K\to\bigwedge^p\mathcal E\to
\bigwedge^{p-1}\mathcal K\otimes\mathcal Q\to0$, obtained by filtering the exterior algebra of
$\mathcal E$ by the powers of $\mathcal K$ after splitting locally. Applying this to the Euler
sequence, where $\mathcal K=\Omega^1$ and $\mathcal Q=\mathcal O$, yields, for every $p\ge2$,

$$
0\to\Omega^p\to\textstyle\bigwedge^p\mathcal O(-1)^{\oplus(n+1)}\to\Omega^{p-1}\to0,
\tag{4.9a}
$$

with the $p=1$ case the Euler sequence itself. The middle term of (4.9a) identifies with
$\mathcal O(-p)^{\oplus\binom{n+1}{p}}$, because wedge powers commute with direct sums and
reduce to ordinary powers on line-bundle summands.

Now compute cohomology by induction on the form degree $p$. The base case is
$p=0$: by Theorem 6.5 of Book 7b applied with $A=k$, $r=n$, and $m=0$, we have
$H^0(\mathbf P^n,\mathcal O)=k$ and $H^q(\mathbf P^n,\mathcal O)=0$ for $q>0$. Next, for every
twist $-p$ with $1\le p\le n$, all cohomology of $\mathcal O(-p)$ vanishes: part 1 of
Theorem 6.5 kills degree zero because no Laurent monomial of negative total degree has all
exponents nonnegative; part 2 kills the intermediate degrees; part 3 would contribute only in
degree $n$ and only when $-p\le-n-1$, which is excluded; part 4 is void. Consequently the long
exact cohomology sequence of (4.9a) collapses to connecting isomorphisms

$$
H^q(\Omega^{p-1})\;\xrightarrow{\ \sim\ }\;H^{q+1}(\Omega^p)
\qquad(2\le p\le n,\ q\ge0),
$$

and similarly across the Euler sequence itself for $p=1$. Chaining these from $\Omega^p$ back
to $\Omega^0=\mathcal O$ gives $H^q(\Omega^p)\simeq H^{q-p}(\mathcal O)$, whence
$H^p(\mathbf P^n,\Omega^p)\simeq k$ and $H^q(\mathbf P^n,\Omega^p)=0$ for $q\ne p$, which is
exactly (4.6).

Since the $E_1$ page of (3.4) is supported on $p=q$, every
differential changes the two indices unequally and must vanish. Hence

$$
H^{2p}_{\mathrm{dR}}(\mathbf P^n_k/k)\simeq k
\quad(0\le p\le n),
\qquad H^{2p+1}_{\mathrm{dR}}=0. \tag{4.7}
$$

The generator in degree two is $c_1(\mathcal O(1))$, and its $p$th power generates degree $2p$.
Thus

$$
H^*_{\mathrm{dR}}(\mathbf P^n/k)
\simeq k[h]/(h^{n+1}),\qquad |h|=2. \tag{4.8}
$$

### 4.4 Why characteristic matters

Let $k$ have characteristic $p>0$. On $\mathbf A^1_k$,

$$
d(t^p)=0.
$$

Thus $t^p$ is a nonconstant element of $H^0(\Omega^\bullet_{k[t]/k})$, and
$t^{p-1}dt$ is not the derivative of a polynomial: the expected primitive $t^p/p$ does not exist.
The affine Poincare lemma (4.1) and homotopy invariance (4.3) fail for the naive de Rham complex in
positive characteristic.

This failure does not invalidate the smooth proper curve results below. Their degeneration proof
uses proper connected functions, residues, and duality rather than polynomial integration. Nor
does it mean that positive-characteristic de Rham cohomology is useless. It remains finite and
geometric in proper smooth families, but it carries phenomena related to Frobenius that are absent
in characteristic zero. A later cohomology theory will retain that Frobenius integrally. Here we
state every characteristic-dependent assertion at the point where it is used.

## 5. The Hodge filtration

The de Rham complex mixes forms of different degrees. The Hodge filtration remembers how far a
class can be represented toward the high-form end of the complex. It is the bridge between
coherent geometry and the flat bundle supplied by Gauss--Manin.

### 5.1 Filtration by form degree

Use the decreasing stupid filtration

$$
(F^p\Omega^\bullet_{X/S})^n=
\begin{cases}
0,&n<p,\\
\Omega^n_{X/S},&n\ge p.
\end{cases} \tag{5.1}
$$

Thus no shift is made: degrees below $p$ are zero and degrees at least $p$ are unchanged. Define

$$
F^pH^n_{\mathrm{dR}}(X/S)
=\operatorname{im}\left(
\mathbb H^n(X,F^p\Omega^\bullet_{X/S})
\to H^n_{\mathrm{dR}}(X/S)\right). \tag{5.2}
$$

It is finite:

$$
H^n_{\mathrm{dR}}=F^0\supseteq F^1\supseteq\cdots
\supseteq F^{d+1}=0
$$

for a smooth relative $d$-fold. Pullback preserves the filtration, and (3.8) makes it
multiplicative.

The associated graded complex is $\Omega^p_{X/S}[-p]$. Applying derived direct image to the
successive filtration triangles produces the spectral sequence (3.4). Thus the Hodge filtration
is not an extra structure placed on cohomology after the fact; it is the abutment filtration of a
specific filtered complex.

### 5.2 The Hodge-to-de Rham spectral sequence

For a smooth proper morphism $f:X\to S$ over a locally noetherian base,

$$
E_1^{p,q}=R^qf_*\Omega^p_{X/S}
\Longrightarrow\mathcal H^{p+q}_{\mathrm{dR}}(X/S). \tag{5.3}
$$

Every $E_1$ term is coherent by proper finiteness. If these sheaves are locally free and commute
with base change, then (5.3) can be checked on geometric fibers. When the spectral sequence
degenerates at $E_1$, there are canonical identifications

$$
\operatorname{gr}^p_F\mathcal H^n_{\mathrm{dR}}(X/S)
\simeq R^{n-p}f_*\Omega^p_{X/S}. \tag{5.4}
$$

Degeneration is a theorem, not part of the definition. For a general smooth proper scheme it
requires an additional argument not supplied by boundedness alone. For curves and abelian schemes
the group or dimension-one geometry supplies the direct proofs given below.

### 5.3 Degeneration versus splitting

Even when (5.3) degenerates, (5.4) determines only successive quotients. It does not canonically
identify

$$
\mathcal H^n_{\mathrm{dR}}
\quad\text{with}\quad
\bigoplus_pR^{n-p}f_*\Omega^p. \tag{5.5}
$$

For a curve, degree one gives an exact sequence

$$
0\to f_*\Omega^1_{X/S}\to
\mathcal H^1_{\mathrm{dR}}(X/S)\to
R^1f_*\mathcal O_X\to0. \tag{5.6}
$$

It may split locally as a sequence of vector bundles, but no splitting is generally compatible
with base change, cup product, and Gauss--Manin. In fact, the failure of the Hodge subbundle to be
horizontal measures genuine variation of the curve.

Over a field, every short exact sequence of vector spaces splits noncanonically. That elementary
fact should not be promoted to a canonical Hodge decomposition. The connection and the
Kodaira--Spencer map remember exactly the extension behavior discarded by such a choice.

### 5.4 Chern classes from logarithmic differentials

Let $L$ be a line bundle on $X$, trivialized on a cover $U_i$ with transition functions
$g_{ij}\in\mathcal O_X^\times(U_{ij})$. The forms

$$
d\log g_{ij}=g_{ij}^{-1}dg_{ij}
$$

form a Cech one-cocycle in $\Omega^1_{X/S}$ because
$d\log(g_{ij}g_{jk})=d\log g_{ij}+d\log g_{jk}$. Its class lies in
$H^1(X,\Omega^1_{X/S})$ and maps to a de Rham class

$$
c_1^{\mathrm{dR}}(L)\in H^2_{\mathrm{dR}}(X/S). \tag{5.7}
$$

Changing trivializations adds a Cech coboundary, so the class is well defined. Tensor product and
pullback give

$$
c_1(L\otimes M)=c_1(L)+c_1(M),
\qquad c_1(u^*L)=u^*c_1(L). \tag{5.8}
$$

It belongs to $F^1$. On projective space it is the class $h$ in (4.8). If a line bundle is pulled
back from the base, its relative first Chern class vanishes because its relative transition
functions have zero differential. This is why polarizations, which are defined up to base
line-bundle ambiguity, still determine unambiguous relative de Rham pairings.

## 6. Smooth proper curves

Curves are the first setting in which the whole relative theory can be proved without a general
degeneration theorem. There are only four possible $E_1$ terms, and duality controls the one
differential that is not visibly zero.

### 6.1 The two-term relative complex

Let $f:C\to S$ be a smooth proper curve. Since $\Omega^p_{C/S}=0$ for $p>1$,

$$
\Omega^\bullet_{C/S}=[\mathcal O_C\xrightarrow d\omega_{C/S}],
\qquad \omega_{C/S}=\Omega^1_{C/S}. \tag{6.1}
$$

The Hodge-to-de Rham page is

$$
\begin{array}{c|cc}
q=1&R^1f_*\mathcal O_C&R^1f_*\omega_{C/S}\\
q=0&f_*\mathcal O_C&f_*\omega_{C/S}\\
\hline
&p=0&p=1.
\end{array} \tag{6.2}
$$

Book 15 proves

$$
f_*\mathcal O_C\simeq\mathcal O_S,
\quad R^1f_*\omega_{C/S}\simeq\mathcal O_S,
\quad f_*\omega_{C/S}\simeq(R^1f_*\mathcal O_C)^\vee. \tag{6.3}
$$

The middle two bundles have rank equal to the genus $g$. Every term commutes with arbitrary base
change. Thus the spectral sequence is a finite spectral sequence of vector bundles whose
differentials may be tested fiberwise.

### 6.2 Degeneration in every characteristic

**Theorem 6.1.** For a smooth proper curve with geometrically connected fibers, the spectral
sequence (5.3) degenerates at $E_1$ over any locally noetherian base and in every characteristic.

**Proof.** There are two possible $d_1$ maps. The first is

$$
f_*\mathcal O_C\xrightarrow d f_*\omega_{C/S}.
$$

By (6.3), a relative global function is pulled back from $S$, so its relative differential is zero.

The second map is

$$
R^1f_*\mathcal O_C\xrightarrow dR^1f_*\omega_{C/S}. \tag{6.4}
$$

It suffices to show that (6.4) vanishes on every geometric fiber. The target on a fiber is
one-dimensional, and the trace is an isomorphism to the ground field. Represent a class in
$H^1(C,\mathcal O_C)$ by a Cech cocycle of functions $g_{ij}$. Its image is represented by
$dg_{ij}$. The trace of this class is computed by residues after passing to principal parts.
Every exact differential has residue zero, so the trace is zero. Since the trace is an
isomorphism, the image is zero. A morphism between finite locally free sheaves that vanishes on
every geometric fiber is zero.

No higher differential is possible: a $d_r$ with $r\ge2$ leaves the two-column range. Hence the
sequence degenerates. $\square$

The proof uses no division by the characteristic. It is therefore unaffected by the failure in
Section 4.4.

### 6.3 The Hodge exact sequence

Degeneration and (6.3) give

$$
\mathcal H^0_{\mathrm{dR}}(C/S)\simeq\mathcal O_S,
\qquad
\mathcal H^2_{\mathrm{dR}}(C/S)\simeq\mathcal O_S, \tag{6.5}
$$

and the canonical exact sequence

$$
0\longrightarrow\mathbb E
\longrightarrow\mathcal H^1_{\mathrm{dR}}(C/S)
\longrightarrow\mathbb E^\vee
\longrightarrow0,
\qquad \mathbb E=f_*\omega_{C/S}. \tag{6.6}
$$

Thus $\mathcal H^1_{\mathrm{dR}}$ has rank $2g$. Its Hodge filtration is

$$
F^0=\mathcal H^1_{\mathrm{dR}},
\qquad F^1=\mathbb E,
\qquad F^2=0. \tag{6.7}
$$

For a genus-zero curve the middle bundle vanishes. For an elliptic curve, (6.6) is an extension of
one line bundle by its dual. For a constant family $C_0\times S$, there is a natural tensor-product
description after choosing the ground field, but a varying family generally has no canonical
splitting.

### 6.4 Finiteness and arbitrary base change

**Theorem 6.2.** Under the hypotheses above, every
$\mathcal H^n_{\mathrm{dR}}(C/S)$ is finite locally free and, for every morphism $S'\to S$,

$$
\mathcal H^n_{\mathrm{dR}}(C/S)\otimes_{\mathcal O_S}\mathcal O_{S'}
\xrightarrow{\sim}
\mathcal H^n_{\mathrm{dR}}(C_{S'}/S'). \tag{6.8}
$$

**Proof.** The four $E_1$ terms in (6.2) are finite locally free and commute with arbitrary base
change by coherent base change and relative duality. The differentials vanish universally by
Theorem 6.1. The finite filtration on each abutment has finite locally free graded pieces. Locally
on $S$, successive short exact sequences of modules with projective quotient split, so the
abutments are finite locally free. Because both $\mathcal O_C$ and $\omega_{C/S}$ are flat over
$S$, Book 15's derived base-change theorem applies term by term and gives a morphism of filtered
derived pushforwards after every $S'\to S$. On the $E_1$ pages it is the base-change isomorphism
for each of the four terms, and every differential on both sides is zero. Induction on the finite
abutment filtration, using the five lemma on successive short exact sequences, proves (6.8).
$\square$

The local splitting used in the proof establishes projectivity only. It does not select a
canonical splitting of (6.6).

## 7. Cup products and duality on curves

The Hodge sequence gives the rank of degree-one cohomology. Cup product explains its geometry: it
is a self-dual bundle, and the Hodge subbundle is exactly half-dimensional and isotropic. This is
the de Rham origin of the symplectic structures used in moduli problems.

### 7.1 The de Rham trace

By (6.5), the top de Rham cohomology is identified with $R^1f_*\omega_{C/S}$. Define

$$
\operatorname{Tr}_{\mathrm{dR}}:
\mathcal H^2_{\mathrm{dR}}(C/S)
\xrightarrow{\sim}R^1f_*\omega_{C/S}
\xrightarrow{\operatorname{tr}_f}\mathcal O_S. \tag{7.1}
$$

The second arrow is the relative duality trace of Book 9. It commutes with arbitrary base change.
On a geometric fiber it is the residue trace: a Cech class of differentials is evaluated by the
sum of its local residues.

Combining cup product with (7.1) gives

$$
\langle x,y\rangle_C
=\operatorname{Tr}_{\mathrm{dR}}(x\smile y):
\mathcal H^1_{\mathrm{dR}}\otimes\mathcal H^1_{\mathrm{dR}}
\longrightarrow\mathcal O_S. \tag{7.2}
$$

The pairing is alternating. Away from characteristic two this follows from graded commutativity.
In characteristic two, skew-symmetry alone would not prove the diagonal assertion, so a separate
calculation is necessary. Alternation is local on the base, so use the relative principal-parts
model of Book 9 to represent the function-cocycle part of a degree-one class by meromorphic
functions $g$ and choose one-forms that complete it to a Cech--de Rham cocycle. The trace of its
cup square is then a sum of local terms $\operatorname{Res}(g\,dg)$; the form--form term is zero because
$\Omega^2_C=0$, and Cech coboundaries contribute a global residue sum. For a Laurent expansion
$g=\sum_na_nt^n$ one has

$$
\operatorname{Res}(g\,dg)=
\sum_{m+n=0}n a_ma_n=0.
$$

Indeed the terms indexed by $(m,n)$ and $(n,m)$ cancel, and the only diagonal possibility is
$m=n=0$, whose coefficient is zero. This coefficient identity is valid over an arbitrary base
ring and descends from an etale localization with parameters; the parameter-free residue
construction of Book 9 gives the same identity without choosing or splitting closed points.
Hence $\langle x,x\rangle_C=0$ over the original base in every characteristic, so (7.2) is
genuinely alternating rather than merely skew-symmetric.

### 7.2 The perfect pairing in degree one

**Theorem 7.1.** The pairing (7.2) is perfect.

**Proof strategy.** Filter both variables by the Hodge filtration. The product of two elements of
$F^1$ lies in $F^2\mathcal H^2=0$, so the upper-left graded pairing is zero. The quotient
$\mathcal H^1/F^1$ is $R^1f_*\mathcal O_C$, and multiplication gives the cross-pairing

$$
f_*\omega_{C/S}\otimes R^1f_*\mathcal O_C
\longrightarrow R^1f_*\omega_{C/S}
\xrightarrow{\operatorname{tr}}\mathcal O_S. \tag{7.3}
$$

This is exactly the perfect relative Serre-duality pairing of Book 9. The reverse cross-pairing is
its negative, with the total-complex sign.

Choose a local splitting of (6.6) only for the calculation. Relative to
$\mathbb E\oplus\mathbb E^\vee$, the matrix of (7.2) has off-diagonal blocks equal to the duality
isomorphisms. The lower-right block may depend on the splitting, but an alternating change of
splitting does not alter invertibility. The determinant is a unit because the off-diagonal blocks
are perfect. Therefore (7.2) is perfect independently of the chosen splitting. $\square$

### 7.3 The Hodge bundle is Lagrangian

A subbundle $L$ of a rank-$2g$ symplectic bundle is **Lagrangian** if it is isotropic and has rank
$g$. By (6.6), $\mathbb E$ has rank $g$, and by multiplicativity of the Hodge filtration,

$$
\mathbb E\smile\mathbb E\subseteq F^2\mathcal H^2=0.
$$

Hence the Hodge bundle is Lagrangian in $\mathcal H^1_{\mathrm{dR}}$. Perfection identifies the
quotient canonically with its dual:

$$
\mathcal H^1_{\mathrm{dR}}/\mathbb E\simeq\mathbb E^\vee,
$$

recovering (6.6) from the symplectic viewpoint.

This statement is stronger than a rank count. It says that holomorphic relative forms pair to
zero with one another, while every functional on them is represented by a de Rham class. In a
varying family the Lagrangian subbundle moves inside a flat symplectic bundle; the infinitesimal
motion is the Higgs map of Chapter 10.

### 7.4 Maps of curves and adjointness

Let $u:C\to D$ be a finite locally free morphism between smooth proper curves over $S$. Pullback
of forms gives $u^*$ on de Rham cohomology. A pushforward must be defined more carefully in
positive characteristic: for a purely inseparable map, the finite-algebra trace on functions and
the duality trace on differentials do not in general form a termwise map of the naive de Rham
complex.

The perfect pairings give the characteristic-free construction. In degrees $0,1,2$, define
$u_*y$ uniquely by

$$
\operatorname{Tr}_{D,\mathrm{dR}}(u_*y\smile z)
=\operatorname{Tr}_{C,\mathrm{dR}}(y\smile u^*z) \tag{7.4}
$$

for every complementary-degree class $z$. Perfection in degrees zero and two is (6.5) and (7.1),
and perfection in degree one is Theorem 7.1, so this defines $u_*$ over the base and commutes with
arbitrary base change. For a finite etale map it agrees with the familiar termwise trace.

The defining adjointness immediately gives the projection formula

$$
u_*(u^*x\smile y)=x\smile u_*y. \tag{7.5}
$$

The remaining numerical input is the top-degree formula

$$
\operatorname{Tr}_{C,\mathrm{dR}}(u^*z)
=d\,\operatorname{Tr}_{D,\mathrm{dR}}(z), \tag{7.6}
$$

where $d$ is the finite locally free degree. This is relative duality applied to the identity
section of the algebra $u_*\mathcal O_C$: evaluation after pullback is multiplication by its
rank $d$. Pairing $u_*u^*x$ against every complementary class and using (7.4) and (7.6) now gives

$$
u_*u^*=d. \tag{7.7}
$$

Thus if $d$ is invertible on $S$, pullback is a split injection. When the curves vary over
$S/T$, pullback is horizontal; the pairings are horizontal by Chapter 9, so its adjoint $u_*$ is
horizontal as well.

## 8. Connections as algebraic differentiation

A vector bundle does not by itself say how sections at neighboring points should be compared. A
connection supplies the infinitesimal comparison. Its curvature measures whether comparisons
depend on the order of two infinitesimal moves.

### 8.1 Connections and horizontal sections

Let $g:S\to T$ be a morphism and $E$ an $\mathcal O_S$-module. A $T$-connection is an additive map

$$
\nabla:E\longrightarrow\Omega^1_{S/T}\otimes E \tag{8.1}
$$

satisfying the Leibniz rule

$$
\nabla(ae)=da\otimes e+a\nabla(e). \tag{8.2}
$$

A section $e$ is **horizontal** if $\nabla(e)=0$. A morphism
$\varphi:(E,\nabla_E)\to(F,\nabla_F)$ is horizontal if

$$
\nabla_F\varphi=(1\otimes\varphi)\nabla_E.
$$

The structure sheaf has its tautological connection $d:\mathcal O_S\to\Omega^1_{S/T}$. A free
bundle with basis $e_1,\ldots,e_r$ acquires the connection for which the basis is horizontal; after
a change of basis by a matrix $G$, its connection matrix changes to

$$
A' =G^{-1}AG+G^{-1}dG. \tag{8.3}
$$

The inhomogeneous term shows why a connection matrix is not a tensor. The connection itself is
independent of the chosen frame.

### 8.2 Curvature and integrability

Extend $\nabla$ to

$$
\nabla:\Omega^p_{S/T}\otimes E
\longrightarrow\Omega^{p+1}_{S/T}\otimes E
$$

by

$$
\nabla(\alpha\otimes e)=d\alpha\otimes e+(-1)^p\alpha\wedge\nabla(e). \tag{8.4}
$$

The curvature is the $\mathcal O_S$-linear map

$$
R_\nabla=\nabla^2:E\to\Omega^2_{S/T}\otimes E. \tag{8.5}
$$

Linearity follows by expanding $\nabla^2(ae)$ and observing that the two $da\wedge\nabla(e)$ terms
cancel. The connection is **integrable** if $R_\nabla=0$. In a frame with connection matrix $A$,

$$
R_\nabla=dA+A\wedge A. \tag{8.6}
$$

On a one-dimensional smooth base, $\Omega^2_{S/T}=0$, so every connection is automatically
integrable. In higher dimension zero curvature is a real condition.

If $\nabla$ is integrable, (8.4) forms a complex

$$
E\xrightarrow\nabla\Omega^1_{S/T}\otimes E
\xrightarrow\nabla\Omega^2_{S/T}\otimes E\to\cdots, \tag{8.7}
$$

the de Rham complex of $E$ with coefficients in the connection.

### 8.3 Tensor operations and de Rham complexes with coefficients

Connections behave as differentiation should. On a tensor product,

$$
\nabla(e\otimes f)=\nabla_E(e)\otimes f+e\otimes\nabla_F(f). \tag{8.8}
$$

On the dual bundle,

$$
d\langle\lambda,e\rangle
=\langle\nabla_{E^\vee}\lambda,e\rangle
+\langle\lambda,\nabla_Ee\rangle. \tag{8.9}
$$

Exterior and symmetric powers inherit connections by the same Leibniz rule. Curvature is additive
under tensor products, so these constructions preserve integrability.

A pairing $b:E\otimes E\to\mathcal O_S$ is horizontal precisely when

$$
d\,b(x,y)=b(\nabla x,y)+b(x,\nabla y). \tag{8.10}
$$

If $b$ is perfect and horizontal, the induced isomorphism $E\simeq E^\vee$ is horizontal. Thus a
flat symplectic bundle is a vector bundle with an integrable connection and a perfect alternating
horizontal form. The curve bundle of Chapter 7 will have exactly this structure.

### 8.4 Change of base

Given $h:S'\to S$ over $T$, a connection pulls back to

$$
h^*E\longrightarrow\Omega^1_{S'/T}\otimes h^*E
$$

by first pulling (8.1) into $h^*\Omega^1_{S/T}\otimes h^*E$ and then using
$h^*\Omega^1_{S/T}\to\Omega^1_{S'/T}$. The Leibniz rule follows from functoriality of universal
differentials, and curvature pulls back. Hence integrability is preserved.

If instead $S'\to S$ is regarded as a new base direction and one wants a connection relative to
$T'$, the comparison involves the map $\Omega^1_{S/T}\to\Omega^1_{S'/T'}$. We will always display
the base tower so that the direction of differentiation is unambiguous.

## 9. Constructing the Gauss--Manin connection

The Gauss--Manin connection is often introduced by differentiating periods. Algebraically, periods
are unnecessary: the connection is the first differential of the filtration of the absolute de
Rham complex by base forms. This construction proves all structural properties at once.

### 9.1 Filtering the absolute de Rham complex

Let

$$
X\xrightarrow f S\xrightarrow g T
$$

with $f$ smooth proper and $g$ smooth. Filter $\Omega^\bullet_{X/T}$ by the number of factors from
$f^*\Omega^1_{S/T}$ as in (2.7). The associated graded complex is

$$
\operatorname{gr}^a_F\Omega^\bullet_{X/T}
\simeq f^*\Omega^a_{S/T}\otimes
\Omega^\bullet_{X/S}[-a]. \tag{9.1}
$$

Apply $Rf_*$. If $\Omega^a_{S/T}$ is finite locally free, the projection formula gives

$$
Rf_*\operatorname{gr}^a_F\Omega^\bullet_{X/T}
\simeq\Omega^a_{S/T}\otimes
Rf_*\Omega^\bullet_{X/S}[-a]. \tag{9.2}
$$

The spectral sequence of the filtered object therefore begins with

$$
E_1^{a,n}=\Omega^a_{S/T}\otimes
\mathcal H^n_{\mathrm{dR}}(X/S), \tag{9.3}
$$

where the second index has been arranged to record relative de Rham degree. The differential
$d_1$ raises $a$ by one and preserves $n$.

### 9.2 The connection and its Leibniz rule

Define

$$
\nabla_{\mathrm{GM}}=d_1^{0,n}:
\mathcal H^n_{\mathrm{dR}}(X/S)
\longrightarrow
\Omega^1_{S/T}\otimes\mathcal H^n_{\mathrm{dR}}(X/S). \tag{9.4}
$$

**Theorem 9.1.** The map (9.4) satisfies the Leibniz rule and hence is a $T$-connection on the
relative de Rham sheaf. When that sheaf is finite locally free, it is a connection on a vector
bundle in the sense of Chapter 8.

**Proof.** The filtered complex is a module over $\Omega^\bullet_{S/T}$ by pullback and wedge
product. On the associated graded, the absolute differential applied to $f^*a\cdot\alpha$ is

$$
f^*(da)\wedge\alpha+f^*a\,d\alpha.
$$

The first term raises the base-form filtration by one; the second contains the relative
differential and the derivative of $\alpha$. Passing to relative de Rham cohomology yields

$$
d_1(a[\alpha])=da\otimes[\alpha]+a\,d_1[\alpha],
$$

which is the Leibniz rule. Independence of representatives follows because $d_1$ is a spectral
sequence differential. $\square$

The construction makes no choice of local coordinates or splitting of (1.1). A splitting can be
used to calculate the connection, but changing it changes representatives by a relative homotopy
and leaves (9.4) unchanged.

### 9.3 Integrability, functoriality, and products

The later $d_1$ maps in (9.3) are precisely the extension (8.4) of $\nabla_{\mathrm{GM}}$ to base
forms. Since $d_1^2=0$, we obtain

$$
\nabla_{\mathrm{GM}}^2=0. \tag{9.5}
$$

Thus the Gauss--Manin connection is integrable.

A map of smooth proper families over $S$ induces a morphism of absolute de Rham complexes that
respects the base-form filtration. The resulting map on relative de Rham cohomology is therefore
horizontal. The same argument applies to trace maps when they are constructed from duality
compatibly with differentials.

Wedge product also respects the filtration, and the spectral differential is a derivation. Hence

$$
\nabla(x\smile y)=\nabla x\smile y+x\smile\nabla y, \tag{9.6}
$$

with the evident placement of the base one-form. In particular, the de Rham trace for a curve is
horizontal. The isomorphism
$\mathcal H^2_{\mathrm{dR}}\simeq R^1f_*\omega_{C/S}$ comes from the filtered complex, and the
relative-duality trace is compatible with the absolute differential and base change. Under the
resulting identification $\mathcal H^2_{\mathrm{dR}}\simeq\mathcal O_S$, the connection is the
ordinary $d$ on $\mathcal O_S$. Combining this with (9.6) proves that the symplectic pairing
(7.2) is horizontal.

### 9.4 Base change

Consider a cartesian diagram over $T$

$$
\begin{array}{ccc}
X'&\longrightarrow&X\\
\downarrow&&\downarrow\\
S'&\longrightarrow&S.
\end{array}
$$

Assume $S'$ is smooth over $T$ and that relative de Rham cohomology commutes with this base change.
Pullback identifies the relative de Rham complexes by (2.8) and maps the base-form filtration for
$X/T$ to that for $X'/T$. Naturality of spectral sequences gives a horizontal isomorphism

$$
h^*\mathcal H^n_{\mathrm{dR}}(X/S)
\xrightarrow{\sim}\mathcal H^n_{\mathrm{dR}}(X'/S'). \tag{9.7}
$$

For smooth proper curves, the needed base-change hypothesis is Theorem 6.2, so (9.7) holds for
every base change for which the displayed connection directions are defined. For general smooth
proper families, finite local freeness and derived base change must be established before (9.7)
is asserted. Coherence alone is insufficient: torsion in neighboring coherent cohomology can
create new classes after reduction.

## 10. Transversality and variation of Hodge structure

The Hodge filtration is generally not horizontal. Its failure to be horizontal is controlled: one
differentiation can lower form degree by at most one. For curves, the resulting map is the cup
product with the Kodaira--Spencer class and measures the infinitesimal variation of complex
structure in purely algebraic terms.

### 10.1 Griffiths transversality

**Theorem 10.1.** Suppose the Hodge filtration on
$\mathcal H^n_{\mathrm{dR}}(X/S)$ is by subbundles and the relevant Hodge-to-de Rham sequence
degenerates. Then

$$
\nabla_{\mathrm{GM}}(F^p)
\subseteq\Omega^1_{S/T}\otimes F^{p-1}. \tag{10.1}
$$

**Proof.** Let $L$ denote the filtration of the absolute complex by base-form degree. The first two
steps give an exact sequence of complexes

$$
0\longrightarrow L^1/L^2
\longrightarrow\Omega^\bullet_{X/T}/L^2
\longrightarrow\Omega^\bullet_{X/S}\longrightarrow0,
$$

with

$$
L^1/L^2\simeq
f^*\Omega^1_{S/T}\otimes\Omega^\bullet_{X/S}[-1].
$$

After $Rf_*$, the connecting morphism of this sequence is exactly (9.4). Now also filter every term by
relative form degree. In $L^1/L^2$, one of the absolute differential slots is occupied by the
base form; under the displayed shift, a boundary lifted from relative form degree at least $p$
therefore has relative form degree at least $p-1$. Equivalently, the connecting morphism of the
doubly filtered sequence sends the $p$th Hodge truncation into
$\Omega^1_{S/T}\otimes F^{p-1}$.

Degeneration and the subbundle hypothesis identify these truncation images with the Hodge
subbundles themselves, so the filtered connecting morphism descends to (10.1). This argument uses
no splitting of the cotangent sequence; a local splitting merely writes the same connecting map in
coordinates. $\square$

Passing to graded pieces gives the Higgs operators

$$
\theta^{p,q}:R^qf_*\Omega^p_{X/S}
\longrightarrow
\Omega^1_{S/T}\otimes R^{q+1}f_*\Omega^{p-1}_{X/S}. \tag{10.2}
$$

Integrability implies $\theta\wedge\theta=0$ on the associated graded.

### 10.2 The Kodaira--Spencer class

The cotangent sequence (1.1) is an extension of $\Omega^1_{X/S}$ by $f^*\Omega^1_{S/T}$. Its class is

$$
\kappa_{X/S/T}\in
\operatorname{Ext}^1_X(\Omega^1_{X/S},f^*\Omega^1_{S/T}). \tag{10.3}
$$

When $f$ is smooth, $\Omega^1_{X/S}$ is locally free, so

$$
\operatorname{Ext}^1_X(\Omega^1_{X/S},f^*\Omega^1_{S/T})
\simeq H^1(X,T_{X/S}\otimes f^*\Omega^1_{S/T}).
$$

Adjunction yields the Kodaira--Spencer map

$$
\operatorname{KS}:T_{S/T}
\longrightarrow R^1f_*T_{X/S}. \tag{10.4}
$$

To see its deformation meaning, take a tangent vector $v$ on $S$. Pull (1.1) back along the
first-order map defined by $v$. The resulting extension of $\Omega^1$ is the first-order
deformation class of the fiber in direction $v$. If the family is a product, (1.1) splits
canonically by the product decomposition and $\operatorname{KS}=0$. The converse requires an
effectivity and rigidity theorem and is not asserted merely from the vanishing of one class.

### 10.3 The Higgs map for a family of curves

For a smooth proper curve, only one nonzero graded Gauss--Manin map can occur:

$$
\theta:\mathbb E=f_*\omega_{C/S}
\longrightarrow\Omega^1_{S/T}\otimes R^1f_*\mathcal O_C
=\Omega^1_{S/T}\otimes\mathbb E^\vee. \tag{10.5}
$$

**Proposition 10.2.** The map (10.5) is cup product with the Kodaira--Spencer class. More precisely,
for a vector field $v$ and a relative one-form $\omega$,

$$
\theta_v(\omega)=\operatorname{KS}(v)\smile\omega
\in H^1(C,\mathcal O_C). \tag{10.6}
$$

**Proof.** Choose local splittings of (1.1). On overlaps their differences are homomorphisms
$\Omega^1_{C/S}\to f^*\Omega^1_{S/T}$, forming a Cech cocycle representing (10.3). Lift $\omega$
using each splitting and apply the absolute differential. The relative part vanishes because a
one-form on a relative curve is top degree. The differences of the base parts on overlaps are the
chosen cocycle evaluated on $\omega$. Contracting the base one-form with $v$ gives exactly the Cech
cup product in (10.6). $\square$

Thus the motion of the Hodge line or bundle is the infinitesimal deformation of the curve paired
with its differentials.

### 10.4 Duality and the second fundamental form

Because the symplectic pairing is horizontal and $\mathbb E$ is Lagrangian, differentiating
$\langle\omega,\eta\rangle=0$ for $\omega,\eta\in\mathbb E$ gives

$$
\langle\theta(\omega),\eta\rangle
=\langle\theta(\eta),\omega\rangle. \tag{10.7}
$$

Hence the bilinear form

$$
(\omega,\eta)\longmapsto
\langle\theta(\omega),\eta\rangle
\in\Omega^1_{S/T} \tag{10.8}
$$

is symmetric. Equivalently, the second fundamental form of the Hodge Lagrangian lies in

$$
\Omega^1_{S/T}\otimes\operatorname{Sym}^2(\mathbb E^\vee).
$$

For curves this is also visible from (10.6): under Serre duality, the tangent space
$H^1(T_C)$ pairs with quadratic differentials $H^0(\omega_C^{\otimes2})$, and

$$
\langle\theta_v(\omega),\eta\rangle
=\langle\operatorname{KS}(v),\omega\eta\rangle. \tag{10.9}
$$

The product $\omega\eta$ is symmetric, proving (10.7) without choosing a symplectic frame.

## 11. De Rham cohomology of abelian schemes

On an abelian scheme, translation reduces differential forms to their values at the identity, and
the group law turns cohomology into a Hopf algebra. These two facts force the whole de Rham algebra
to be generated in degree one.

### 11.1 Invariant forms and the first Hodge sequence

Let $p:A\to S$ be an abelian scheme of relative dimension $g$, with identity $e$. Set

$$
\omega_A=e^*\Omega^1_{A/S}.
$$

Translation gives the canonical isomorphisms established in Book 15:

$$
\Omega^1_{A/S}\simeq p^*\omega_A,
\qquad
\Omega^a_{A/S}\simeq p^*\bigwedge^a\omega_A. \tag{11.1}
$$

The coherent exterior algebra theorem gives

$$
R^bp_*\mathcal O_A\simeq\bigwedge^bR^1p_*\mathcal O_A. \tag{11.2}
$$

The group law gives a clean proof that every $d_1$ leaving total degree one vanishes, including
the differential on invariant one-forms. By (11.1), (11.2), and the projection formula, the whole
$E_1$ page is the bigraded exterior algebra

$$
E_1^{a,b}\simeq
\bigwedge^a\omega_A\otimes
\bigwedge^bR^1p_*\mathcal O_A.
$$

Addition on $A$ makes every element of the two degree-one summands primitive. Naturality of
exterior differentiation says that $d_1$ is compatible with this coproduct, while
multiplicativity says that it is a derivation. It must therefore send a primitive degree-one
element to a primitive degree-two element. There are no such elements in an exterior Hopf
algebra. Locally choose a basis $v_i$ of the degree-one module. The reduced coproduct of
$\sum_{i<j}a_{ij}v_i\wedge v_j$ is

$$
\sum_{i<j}a_{ij}
(v_i\otimes v_j-v_j\otimes v_i),
$$

and the ordered basis tensors force every $a_{ij}$ to vanish. The argument is unchanged in
characteristic two, where the two ordered tensors remain distinct. Hence $d_1$ vanishes on both
degree-one summands, and therefore everywhere on the displayed exterior algebra. In total degree
one this gives

$$
0\longrightarrow\omega_A
\longrightarrow\mathcal H^1_{\mathrm{dR}}(A/S)
\longrightarrow R^1p_*\mathcal O_A
\longrightarrow0. \tag{11.3}
$$

Book 35 identifies $R^1p_*\mathcal O_A\simeq\omega_{A^\vee}^\vee$, so (11.3) becomes

$$
0\to\omega_A\to\mathcal H^1_{\mathrm{dR}}(A/S)
\to\omega_{A^\vee}^\vee\to0. \tag{11.4}
$$

### 11.2 The exterior algebra theorem

**Theorem 11.1.** For an abelian scheme over a locally noetherian base, the Hodge-to-de Rham
spectral sequence degenerates at $E_1$, every de Rham cohomology sheaf is finite locally free and
commutes with arbitrary base change, and cup product induces

$$
\bigwedge^n\mathcal H^1_{\mathrm{dR}}(A/S)
\xrightarrow{\sim}\mathcal H^n_{\mathrm{dR}}(A/S). \tag{11.5}
$$

In particular, $\mathcal H^n_{\mathrm{dR}}$ has rank $\binom{2g}{n}$.

**Proof strategy and proof.** Addition and the diagonal make
$R p_*\Omega^\bullet_{A/S}$ a commutative Hopf object, and the Hodge filtration respects both its
product and coproduct. We first prove degeneration, then use the same Hopf structure to justify the
exterior power in characteristic two, where graded commutativity alone is insufficient.

The calculation preceding (11.3) has already proved $d_1=0$. Every later page is consequently
still the exterior Hopf algebra displayed there until a differential is found. Its differential
is a derivation and is compatible with the coproduct. A primitive degree-one generator can only
map to a primitive element of total degree two. But there are no such elements: the reduced
coproduct of $x\wedge y$ is

$$
x\otimes y-y\otimes x,
$$

and the basis calculation preceding (11.3) shows that no nonzero linear combination has zero
reduced coproduct. Thus the differential vanishes on the degree-one generators and hence on the
algebra they generate. Induction on the page proves degeneration at $E_1$.

Apply the same argument to $A\times_SA$. External product identifies its $E_1$ page with the
tensor product of the two Hodge pages: by (11.1) each summand $\Omega^{a'}_{A/S}$ is the pullback
of a locally free sheaf, so Theorem 3.6 applies with $\mathcal F$ and $\mathcal G$ exterior
powers of $\omega_A$, and its local-freeness hypothesis holds because $R^bp_*\Omega^{a'}$ is
$\bigwedge^{a'}\omega_A\otimes\bigwedge^bR^1p_*\mathcal O_A$ by the projection formula, (11.1),
and (11.2), all of whose factors are locally free. Finite filtered comparison therefore gives
the de Rham Kunneth isomorphism for this product. We
may consequently write the coproduct in tensor notation without assuming the exterior theorem
being proved.

The abutment itself has no primitive element in degree two. Indeed, if $z$ were primitive, choose
the deepest Hodge step $F^p$ containing it. Its nonzero image in
$\operatorname{gr}^p_F\mathcal H^2_{\mathrm{dR}}$ would be primitive, because the coproduct
preserves the filtration. The associated graded Hopf algebra is the exterior algebra on the two
degree-one Hodge pieces, where the preceding reduced-coproduct calculation rules this out.
Descending through the finite filtration forces $z=0$.

Every element $x$ of $\mathcal H^1_{\mathrm{dR}}$ is primitive. Indeed, the degree-one Kunneth
decomposition just established writes $m^*x$ as a pair of classes. Pulling back along
$a\mapsto(a,e)$ and $a\mapsto(e,a)$ recovers the two components, and both composites with
multiplication are the identity of $A$. Thus
$m^*x=\operatorname{pr}_1^*x+\operatorname{pr}_2^*x$. In the graded tensor-product algebra the
two cross terms in the square cancel with their Koszul signs, so

$$
\Delta(x^2)=x^2\otimes1+1\otimes x^2.
$$

Thus $x^2$ is primitive of degree two and must vanish. This proves genuine alternation even in
characteristic two, so cup product factors canonically through the Hopf morphism (11.5).

It remains to prove that this morphism is an isomorphism. Filter its source using (11.3). Its
graded pieces are

$$
\bigwedge^a\omega_A\otimes
\bigwedge^bR^1p_*\mathcal O_A,
\qquad a+b=n. \tag{11.6}
$$

By the projection formula, (11.1), and (11.2), these are exactly

$$
R^bp_*\Omega^a_{A/S}, \tag{11.7}
$$

the total-degree-$n$ terms of the Hodge page. The induced graded map is the identity under these
coherent exterior-algebra identifications. Finite filtered comparison makes (11.5) an
isomorphism. Since the graded pieces are finite locally free and commute with base change, the
same filtration argument as in Theorem 6.2 proves local freeness and arbitrary base change for
the abutment. $\square$

The proof uses the full group law. A general smooth proper variety need not have de Rham
cohomology generated in degree one.

### 11.3 Gauss--Manin and the group law

Suppose $A\to S\to T$ lies in the smooth tower of Chapter 9. Addition, inversion, the identity,
and multiplication by $n$ are maps of families. Their actions on de Rham cohomology are therefore
horizontal. Since (11.5) is induced by cup product, it is an isomorphism of bundles with
integrable connection:

$$
(\mathcal H^*_{\mathrm{dR}}(A/S),\nabla)
\simeq
\bigwedge^*(\mathcal H^1_{\mathrm{dR}}(A/S),\nabla). \tag{11.8}
$$

The proof of Theorem 11.1 showed that every degree-one class is primitive. Since $[n]$ is the
composite of the diagonal into $A^n$ with $n$-fold addition, pulling a primitive class back by
$[n]$ gives the sum of $n$ identical copies. Thus $[n]^*=n$ on
$\mathcal H^1_{\mathrm{dR}}$. The exterior algebra isomorphism then gives

$$
[n]^*=n^r\quad\text{on }\mathcal H^r_{\mathrm{dR}}. \tag{11.9}
$$

No invertibility of $n$ is needed for the equality. If an isogeny has invertible degree on $S$,
the quasi-inverse identities of Book 35 and pullback show that it induces an isomorphism on de
Rham cohomology; Section 12.4 gives the precise degree-one argument.

### 11.4 The universal vector extension viewpoint

The bundle in (11.4) also has a moduli interpretation. Consider the universal vector extension of
the dual abelian scheme:

$$
0\longrightarrow V(\omega_A)
\longrightarrow E(A^\vee)\longrightarrow A^\vee\longrightarrow0, \tag{11.10}
$$

where our convention is that the vector group $V(M)$ has Lie algebra $M$. Then there is a canonical
identification

$$
\operatorname{Lie}(E(A^\vee)/S)
\simeq\mathcal H^1_{\mathrm{dR}}(A/S). \tag{11.11}
$$

Here is the construction, including the point at which integrability enters. For an $S$-scheme
$U$, let $E(A^\vee)(U)$ consist of rigidified algebraically trivial line bundles $L$ on $A_U$
equipped with an integrable $U$-relative connection compatible with the rigidification. Tensor
product makes this an fppf sheaf of groups, and forgetting the connection maps it to $A^\vee$.

_(The canonical identification (11.11) is the classical description of the universal vector extension; the sketch that follows indicates why it holds, and later chapters use only the existence of an extension whose Lie algebra is identified as stated.)_ The obstruction to a relative connection on $L$ is its Atiyah class in
$H^1(A_U,\Omega^1_{A_U/U})$. On the universal Poincare family, both this class and the de Rham
class $c_1^{\mathrm{dR}}(L)$ are additive in the $A^\vee$-variable. By base change they therefore
define homomorphisms from $A^\vee$ to the vector groups attached respectively to
$R^1p_*\Omega^1_{A/S}$ and $\mathcal H^2_{\mathrm{dR}}(A/S)$. Each homomorphism is zero by
rigidity: a morphism from a proper connected group to an affine vector group is constant, and its
value at the identity is zero because the corresponding line bundle is trivial. Thus the Atiyah
obstruction vanishes, connections exist fppf locally on $U$, and
$c_1^{\mathrm{dR}}(L)=0$.

Two relative connections differ by a global one-form, hence by a section of $\omega_A$ by
(11.1). Such invariant one-forms are closed: the exterior derivative of an invariant form is
given at the identity by the Lie bracket, and the Lie algebra of the commutative group $A$ is
abelian. Finally, the curvature of any chosen connection is a global two-form whose image in
de Rham cohomology is $c_1^{\mathrm{dR}}(L)=0$. Theorem 11.1 makes
$H^0(\Omega^2)\to\mathcal H^2_{\mathrm{dR}}$ injective, so the curvature itself is zero.

It follows that the fiber of $E(A^\vee)\to A^\vee$ is a torsor under $V(\omega_A)$. Such a torsor
is represented by an affine bundle, and tensor product makes it the vector-group extension
(11.10). Infinitesimally, its tangent sequence is

$$
0\to\omega_A\to\operatorname{Lie}(E(A^\vee)/S)
\to\operatorname{Lie}(A^\vee/S)\to0.
$$

Since $\operatorname{Lie}(A^\vee/S)=R^1p_*\mathcal O_A=\omega_{A^\vee}^\vee$, this has the same
graded terms as (11.4). More precisely, over a square-zero thickening a rigidified line bundle is
represented by a Cech cocycle $a_{ij}$ in $\mathcal O_A$, while a connection is represented by
one-forms $\beta_i$ satisfying

$$
\beta_j-\beta_i=d a_{ij}.
$$

Pairs $(a_{ij},\beta_i)$ modulo changes of trivialization are exactly total degree-one cocycles
of $[\mathcal O_A\to\Omega^1_{A/S}]$. This identifies the tangent extension itself, not only its
graded terms, with (11.4), and proves (11.11).

This viewpoint explains why $\mathcal H^1_{\mathrm{dR}}$ is the natural linear realization of an
abelian scheme: it simultaneously records invariant differentials on $A$ and infinitesimal line
bundles on $A^\vee$.

## 12. Dual abelian schemes, polarizations, and isogenies

Book 35 constructed the Poincare bundle and used it to pair finite torsion. Its de Rham first Chern
class gives the corresponding pairing of vector bundles. Polarizations turn that duality into a
symplectic form, and functoriality makes the form horizontal.

### 12.1 The Poincare class and de Rham duality

Let $\mathcal P$ be the normalized Poincare bundle on $A\times_SA^\vee$. Its first Chern class lies
in

$$
c_1^{\mathrm{dR}}(\mathcal P)
\in\mathcal H^2_{\mathrm{dR}}(A\times A^\vee/S). \tag{12.1}
$$

Theorem 11.1 applied to $A\times A^\vee$, together with
$\mathcal H^1_{\mathrm{dR}}(A\times A^\vee/S)=\mathcal H^1_{\mathrm{dR}}(A/S)\oplus\mathcal H^1_{\mathrm{dR}}(A^\vee/S)$,
gives the degree-two
Kunneth decomposition. It places the normalized class entirely in

$$
\mathcal H^1_{\mathrm{dR}}(A/S)
\otimes\mathcal H^1_{\mathrm{dR}}(A^\vee/S). \tag{12.2}
$$

Indeed normalization makes its restrictions to $A\times e$ and $e\times A^\vee$ trivial, killing
the degree-two classes from either factor. Put
$V=\mathcal H^1_{\mathrm{dR}}(A/S)$ and
$W=\mathcal H^1_{\mathrm{dR}}(A^\vee/S)$. A tensor in (12.2) is equivalently a map from the dual of
either factor to the other. The Poincare tensor gives

$$
t_{\mathcal P}:V^\vee\longrightarrow W. \tag{12.3}
$$

**Theorem 12.1.** The map (12.3) is an isomorphism. Its inverse identifies $W$ with $V^\vee$ and
therefore gives a perfect evaluation pairing between the degree-one de Rham bundles of $A$ and
$A^\vee$.

**Proof.** On Hodge graded pieces, the biextension interpretation of $\mathcal P$ gives the
evaluation pairings

$$
\omega_A\otimes R^1p^\vee_*\mathcal O_{A^\vee}\to\mathcal O_S,
\qquad
R^1p_*\mathcal O_A\otimes\omega_{A^\vee}\to\mathcal O_S. \tag{12.4}
$$

They are perfect because $R^1p_*\mathcal O_A=\omega_{A^\vee}^\vee$ and its dual counterpart holds
after biduality. Thus the associated graded map of (12.3) is an isomorphism. Finite filtered
comparison proves that (12.3) itself is an isomorphism. $\square$

### 12.2 Polarization forms

Let $\lambda:A\to A^\vee$ be a polarization and retain the notation $V,W$ of Section 12.1.
Contravariance gives

$$
\lambda^*: \mathcal H^1_{\mathrm{dR}}(A^\vee/S)
\longrightarrow V.
$$

After identifying $W$ with $V^\vee$ by $t_{\mathcal P}^{-1}$, this is a map $V^\vee\to V$. If
$\lambda$ is principal, it is an isomorphism; define

$$
\psi_\lambda(x,y)=\bigl((\lambda^*)^{-1}x\bigr)(y):
V\otimes V\longrightarrow\mathcal O_S. \tag{12.5}
$$

The symmetry condition $\lambda^\vee\delta_A=\lambda$ identifies the transpose of the Poincare
tensor with its pullback under interchange of the two factors. The biextension commutator reverses
under that interchange, so (12.5) is skew-symmetric: $\psi_\lambda(x,y)=-\psi_\lambda(y,x)$.
After inverting $2$ on $S$, skew-symmetry implies genuine alternation,
$\psi_\lambda(x,x)=0$. In residue characteristic two this implication is unavailable, and we do
not supply the stronger input that the literature uses there. That input consists of two steps:
first, a canonical trivialization of the biextension commutator restricted to the diagonal,
produced by the cubical identity for the normalized Poincare bundle; second, its first-order de
Rham linearization, identifying the infinitesimal sign of that trivialization with
$\psi_\lambda(x,x)$. The torsion-level analogue of exactly this cubical input is asserted without
proof at Book 34, (14.5); neither step has been carried out anywhere earlier in this series.
Accordingly, downstream use of (12.5) is made here only through skew-symmetry, with alternation
available after $2$ is inverted; any application requiring genuine alternation of $\psi_\lambda$
in characteristic two is conditional on the unproved diagonal trivialization and its linearization.

The form (12.5) is perfect by construction when $\lambda$ is principal. More generally, the same
formula defines a perfect pairing after inverting $\deg\lambda$: a quasi-inverse to the isogeny
shows that $\lambda^*$ becomes invertible there. Before that degree is inverted, it is safer to
retain the integral map $V^\vee\to V$ rather than claim a perfect form.

The Hodge bundle $\omega_A$ is isotropic. On the Hodge graded pairing, it pairs only with the
quotient $R^1p_*\mathcal O_A$, not with itself. Under a principal polarization it is thus an
isotropic rank-$g$ subbundle of the rank-$2g$ bundle, self-dual under the perfect skew form; when
the ambient form is alternating — in particular after inverting $2$ — it is a Lagrangian
subbundle.

For an elliptic scheme, the canonical principal polarization identifies this construction with
the curve pairing of Chapter 7. Both are induced by the diagonal divisor and have the same
restriction to the Hodge graded pieces, so perfection and normalization force equality.

### 12.3 Horizontality

The Poincare bundle is defined over $S$, and its relative first Chern class is horizontal. To see
this directly, represent it by transition functions $g_{ij}$. In the absolute de Rham complex,
$d(d\log g_{ij})=0$; under the base-form filtration this says precisely that the Gauss--Manin
derivative of the relative class vanishes. Thus (12.3) is horizontal.

If $\lambda$ is a homomorphism of abelian schemes over $S$, pullback by $\lambda$ is horizontal by
functoriality. Therefore

$$
d\psi_\lambda(x,y)
=\psi_\lambda(\nabla x,y)+\psi_\lambda(x,\nabla y). \tag{12.6}
$$

A principally polarized abelian scheme consequently determines a flat bundle equipped with a
horizontal perfect skew-symmetric form — alternating, hence symplectic, after inverting $2$ by
Section 12.2 — whose Hodge subbundle is isotropic of half rank. Its second fundamental form is
symmetric, just as in (10.7). This is
the linear algebra underlying the Hodge conditions in polarized moduli spaces.

### 12.4 Isogeny invariance

Let $u:A\to B$ be an isogeny. Duality of the Poincare bundles gives

$$
\langle u^*x,y\rangle_A
=\langle x,(u^\vee)^*y\rangle_B. \tag{12.7}
$$

Put $d=\deg u$. Book 35 supplies a quasi-inverse homomorphism $u':B\to A$ satisfying

$$
u'u=[d]_A,\qquad uu'=[d]_B.
$$

Contravariance and (11.9) therefore give

$$
u^*(u')^*=d,\qquad (u')^*u^*=d
$$

on degree-one de Rham cohomology. Hence, if $d$ is invertible on $S$,

$$
u^*: \mathcal H^1_{\mathrm{dR}}(B/S)
\xrightarrow{\sim}\mathcal H^1_{\mathrm{dR}}(A/S) \tag{12.8}
$$

with inverse $d^{-1}(u')^*$. It is horizontal because both pullbacks are horizontal. It is
strictly compatible with the Hodge filtration because $u^*$ and its displayed inverse preserve
that filtration; on invariant forms this is the cotangent map at the identity, and on the
coherent quotient it is the induced map on $R^1\mathcal O$.

Without invertibility, (12.8) can fail. In characteristic $p$, the differential of a purely
inseparable $p$-isogeny may vanish on invariant forms. The group schemes still have the same
dimension and the isogeny remains finite locally free, but integral de Rham lattices need not be
identified. Thus isogeny invariance must state which degree is inverted.

## 13. An explicit elliptic family

An explicit calculation shows how the abstract connection becomes a differential equation. The
Legendre family is simple enough for reduction by exact differentials and rich enough to have
nonzero Kodaira--Spencer class.

### 13.1 The Legendre family and a cohomology basis

Let

$$
S=\operatorname{Spec}
\mathbf Z\left[\frac12,\lambda,
\frac1{\lambda(1-\lambda)}\right]
$$

and let $E\to S$ be the smooth projective elliptic curve whose affine equation is

$$
y^2=x(x-1)(x-\lambda). \tag{13.1}
$$

The inversions exclude characteristic two and the singular parameters $0,1,\infty$. Put

$$
\omega=\frac{dx}{y},
\qquad \eta=\frac{x\,dx}{y}. \tag{13.2}
$$

The form $\omega$ extends regularly across the point at infinity and generates the Hodge line.
The class of $\eta$ is a differential of the second kind: it may be represented on the affine
chart and has zero residue at infinity. To see that the two classes form a basis rather than only
fiberwise generators, use the parameter $t=-x/y$ at infinity. Its leading expansions are

$$
x=t^{-2}+O(1),\qquad
\omega=2\,dt+O(t^2)dt,\qquad
\eta=2t^{-2}dt+O(1)dt.
$$

A local primitive for the polar part of $\eta$ is therefore $-2t^{-1}$. Under the Serre-duality
description of the quotient in the Hodge sequence, pairing the image of $\eta$ with $\omega$
has leading residue $\operatorname{Res}(-4\,dt/t)=-4$. This is a unit on $S$. Hence $\omega$
generates $F^1$, the image of $\eta$ generates the quotient $R^1f_*\mathcal O_E$, and the two
classes form a basis of $\mathcal H^1_{\mathrm{dR}}(E/S)$ over the displayed base ring.

### 13.2 Reduction of differentials

Write

$$
P=x(x-1)(x-\lambda),\qquad y^2=P.
$$

Differentiating with respect to $\lambda$ while holding $x$ fixed gives

$$
\partial_\lambda\omega
=\frac{x(x-1)}{2y^3}\,dx,
\qquad
\partial_\lambda\eta
=\frac{x^2(x-1)}{2y^3}\,dx. \tag{13.3}
$$

To reduce a numerator $N(x)dx/y^3$ modulo exact forms, use

$$
d\left(\frac{Q(x)}y\right)
=\frac{Q'P-\frac12QP'}{y^3}\,dx. \tag{13.4}
$$

Solving polynomial identities in (13.4) gives

$$
\frac{x(x-1)}{2y^3}dx
\equiv\frac{\lambda\omega-\eta}
{2\lambda(1-\lambda)}, \tag{13.5}
$$

and

$$
\frac{x^2(x-1)}{2y^3}dx
\equiv\frac{\omega-\eta}{2(1-\lambda)} \tag{13.6}
$$

in de Rham cohomology. For example, in (13.5) one may take

$$
Q=\frac{x^2-x}{\lambda(1-\lambda)};
$$

substitution into (13.4) verifies the identity after moving the indicated combination of
$\omega,\eta$ to the other side. For (13.6), take
$Q=(x^2-x)/(1-\lambda)$. Thus the reduction uses only exact differentials and is valid over the
chosen base ring.

### 13.3 The connection matrix

Equations (13.3)--(13.6) give

$$
\nabla\omega=
\frac{d\lambda}{2\lambda(1-\lambda)}
(\lambda\omega-\eta), \tag{13.7}
$$

$$
\nabla\eta=
\frac{d\lambda}{2\lambda(1-\lambda)}
(\lambda\omega-\lambda\eta). \tag{13.8}
$$

With columns recording the derivatives of the ordered basis $(\omega,\eta)$, the matrix is

$$
\nabla=d+
\frac{d\lambda}{2\lambda(1-\lambda)}
\begin{pmatrix}
\lambda&\lambda\\
-1&-\lambda
\end{pmatrix}. \tag{13.9}
$$

The first column of (13.9) has a nonzero component modulo the Hodge line, so $F^1$ is not
horizontal. That component is the Higgs map and witnesses the nontrivial Kodaira--Spencer class of
the Legendre family. The only poles of the matrix occur at the omitted degenerations
$0,1,\infty$; on the open smooth base it is regular.

### 13.4 The Picard--Fuchs equation

Let a horizontal functional on the dual de Rham bundle assign

$$
Y=I(\omega),\qquad Z=I(\eta).
$$

Horizontality and (13.7)--(13.8) give

$$
Y'=\frac{\lambda Y-Z}{2\lambda(1-\lambda)},
\qquad
Z'=\frac{Y-Z}{2(1-\lambda)}. \tag{13.10}
$$

Eliminating $Z$ yields

$$
\lambda(1-\lambda)Y''+(1-2\lambda)Y'
-\frac14Y=0. \tag{13.11}
$$

This is the Picard--Fuchs equation of the family. Over the complex numbers, integrating $\omega$
over a locally constant topological cycle produces a solution, but equation (13.11) was obtained
entirely from algebraic differential reduction. Its regular singularities occur exactly at the
three parameters where the elliptic curve degenerates.

## 14. The de Rham package for later arithmetic geometry

The constructions now fit into one reusable package. This final chapter records both the positive
results and the checks that prevent them from being applied outside their hypotheses.

### 14.1 A reusable theorem package

**Relative de Rham theory.** For a smooth morphism $X\to S$, the finite complex
$\Omega^\bullet_{X/S}$ is functorial and compatible with arbitrary base change term by term. Its
hypercohomology carries a multiplicative Hodge filtration and cup products. Properness makes the
Hodge-page terms coherent; local freeness and base change of the abutment require degeneration or
another perfectness argument.

**Curves.** For a smooth proper geometrically connected curve of genus $g$ over a locally
noetherian base, the Hodge-to-de Rham sequence degenerates in every characteristic. There is a
base-change-compatible exact sequence

$$
0\to f_*\omega_{C/S}\to\mathcal H^1_{\mathrm{dR}}(C/S)
\to R^1f_*\mathcal O_C\to0,
$$

whose terms have ranks $g,2g,g$. Cup product and trace give a perfect alternating pairing, and the
Hodge bundle is Lagrangian.

**Gauss--Manin.** For a smooth tower $X\to S\to T$, once relative de Rham cohomology is a
base-change-compatible vector bundle, the base-form filtration on $\Omega^\bullet_{X/T}$ gives a
canonical integrable connection. It is functorial, compatible with cup products and trace, and
satisfies Griffiths transversality. On curves its graded map is cup product with the
Kodaira--Spencer class.

**Abelian schemes.** De Rham cohomology is the exterior algebra on degree one, is finite locally
free, and commutes with arbitrary base change. Degree one fits into

$$
0\to\omega_A\to\mathcal H^1_{\mathrm{dR}}(A/S)
\to\omega_{A^\vee}^\vee\to0.
$$

The Poincare class pairs the degree-one bundles of $A$ and $A^\vee$ perfectly. A principal
polarization gives a horizontal perfect skew-symmetric form on $\mathcal H^1_{\mathrm{dR}}(A/S)$,
alternating after $2$ is inverted; its Hodge subbundle is isotropic of half rank, hence
Lagrangian whenever the form is alternating. Section 12.2 records precisely which part of this
statement remains open in residue characteristic two.

### 14.2 Failure modes and hypothesis checks

Before using the package, the following distinctions must be checked.

- Smoothness is needed for locally free differential forms and for the cotangent filtration.
  Ordinary differentials on a nodal curve are not a substitute for the smooth de Rham complex.

- Properness is needed for coherent finiteness, traces, and the perfect global pairings used here.
  Nonproper de Rham cohomology exists but has different boundary behavior.

- Hodge-to-de Rham degeneration is not automatic from boundedness. It was proved directly for
  curves and abelian schemes; a general smooth proper family needs its own degeneration theorem.

- Degeneration identifies graded pieces, not a canonical direct sum. The Hodge exact sequence of
  a varying curve usually has no horizontal splitting.

- Characteristic-zero polynomial integration cannot be used in characteristic $p$. The identity
  $d(t^p)=0$ is the basic counterexample.

- A connection requires a specified direction $S/T$. The relative cohomology bundle over $S$ does
  not determine which differentials count as base differentials until $T$ is fixed.

- Arbitrary coefficient change requires finite local freeness or a derived base-change theorem.
  Coherence by itself does not eliminate Tor from neighboring degrees.

- An isogeny identifies de Rham cohomology by pullback only after its degree is invertible, unless
  a stronger argument is supplied. In residue characteristic its cotangent map can be singular.

- The polarization form of Section 12.2 is skew-symmetric in every characteristic but is proved
  alternating only after $2$ is inverted. The diagonal trivialization of the biextension
  commutator that would give genuine alternation in characteristic two is not established here;
  consumers needing it must treat it as an open input.

These checks are part of the mathematical content: each prevents a real counterexample rather
than a merely formal inconvenience.

### 14.3 Conclusion

Algebraic de Rham cohomology begins with the universal derivative and ends with a flat geometric
object. Hypercohomology joins local differential forms to global gluing classes. The Hodge
filtration remembers their form degrees, while proper coherent cohomology makes its layers finite.
For curves, residues and duality force degeneration and turn degree one into a symplectic bundle.
For abelian schemes, translation and the Hopf structure force every degree to be an exterior power
of degree one.

When the base itself moves, the absolute de Rham complex records that motion. Filtering it by base
forms produces the Gauss--Manin connection; the equality $d^2=0$ becomes integrability, the product
rule becomes horizontality of cup products, and the interaction of two filtrations becomes
Griffiths transversality. The Kodaira--Spencer class then identifies the derivative of the Hodge
bundle with the infinitesimal deformation of the family. For a polarized abelian scheme, the
Poincare class makes the resulting flat bundle carry a perfect skew-symmetric horizontal form,
symplectic after inverting $2$.

The final package is therefore one continuous chain:

$$
\text{universal differentials}
\longrightarrow\text{de Rham hypercohomology}
\longrightarrow\text{Hodge filtration}
\longrightarrow\text{Gauss--Manin connection}
\longrightarrow\text{polarized variation}.
$$

It supplies the degree-one linear algebra, functoriality, base change, cup products, and
connections needed to compare smooth curves and abelian schemes with the integral cohomology
theories that follow.
