# Transfer of Test Functions and the Rank-Two Fundamental Lemma

## Contents

- [1. The transfer problem](#1-the-transfer-problem)
  - [1.1 From two trace formulas to one local identity](#11-from-two-trace-formulas-to-one-local-identity)
  - [1.2 Standing local conventions](#12-standing-local-conventions)
  - [1.3 What will be proved](#13-what-will-be-proved)
- [2. Matching classes and measures](#2-matching-classes-and-measures)
  - [2.1 The invariant quotient](#21-the-invariant-quotient)
  - [2.2 Haar and quotient measures](#22-haar-and-quotient-measures)
  - [2.3 Transfer and its sign](#23-transfer-and-its-sign)
  - [2.4 Central scaling and involutions](#24-central-scaling-and-involutions)
- [3. Local descent on the regular set](#3-local-descent-on-the-regular-set)
  - [3.1 Why existence is not automatic](#31-why-existence-is-not-automatic)
  - [3.2 A rank-two slice](#32-a-rank-two-slice)
  - [3.3 Prescribing an orbital integral locally](#33-prescribing-an-orbital-integral-locally)
  - [3.4 Patching on compact regular sets](#34-patching-on-compact-regular-sets)
- [4. The tree and the elliptic Euler function](#4-the-tree-and-the-elliptic-euler-function)
  - [4.1 Vertices, edges, and stabilizers](#41-vertices-edges-and-stabilizers)
  - [4.2 Orbital integrals as weighted fixed-cell counts](#42-orbital-integrals-as-weighted-fixed-cell-counts)
  - [4.3 The fixed-subtree Euler calculation](#43-the-fixed-subtree-euler-calculation)
  - [4.4 The explicit elliptic Euler function](#44-the-explicit-elliptic-euler-function)
- [5. The unit fundamental lemma](#5-the-unit-fundamental-lemma)
  - [5.1 Split inner forms](#51-split-inner-forms)
  - [5.2 A ramified quaternion place](#52-a-ramified-quaternion-place)
  - [5.3 Proof of the unit identity](#53-proof-of-the-unit-identity)
  - [5.4 Why the raw units do not match](#54-why-the-raw-units-do-not-match)
- [6. The Iwahori fundamental lemma](#6-the-iwahori-fundamental-lemma)
  - [6.1 The two Iwahori cells](#61-the-two-iwahori-cells)
  - [6.2 The alternating Iwahori line](#62-the-alternating-iwahori-line)
  - [6.3 The Iwahori theorem](#63-the-iwahori-theorem)
  - [6.4 Convolution and normalization checks](#64-convolution-and-normalization-checks)
- [7. Spherical shells and central translates](#7-spherical-shells-and-central-translates)
  - [7.1 Determinant shells](#71-determinant-shells)
  - [7.2 The split-place spherical lemma](#72-the-split-place-spherical-lemma)
  - [7.3 Central translation at a division place](#73-central-translation-at-a-division-place)
  - [7.4 The first Hecke shell](#74-the-first-hecke-shell)
- [8. Selected congruence levels](#8-selected-congruence-levels)
  - [8.1 Conjugation averaging](#81-conjugation-averaging)
  - [8.2 Extending functions on the invariant quotient](#82-extending-functions-on-the-invariant-quotient)
  - [8.3 The invariant-level transfer theorem](#83-the-invariant-level-transfer-theorem)
  - [8.4 Congruence depth and scalar reduction](#84-congruence-depth-and-scalar-reduction)
- [9. Special and dihedral type functions](#9-special-and-dihedral-type-functions)
  - [9.1 Type idempotents and matrix coefficients](#91-type-idempotents-and-matrix-coefficients)
  - [9.2 Special packets](#92-special-packets)
  - [9.3 Depth-zero dihedral packets](#93-depth-zero-dihedral-packets)
  - [9.4 Positive-depth tame packets](#94-positive-depth-tame-packets)
  - [9.5 The level-specific fundamental lemma](#95-the-level-specific-fundamental-lemma)
- [10. Singular germs and central terms](#10-singular-germs-and-central-terms)
  - [10.1 What regular matching does not say](#101-what-regular-matching-does-not-say)
  - [10.2 The two rank-two germs](#102-the-two-rank-two-germs)
  - [10.3 Cancellation for the Euler function](#103-cancellation-for-the-euler-function)
  - [10.4 Central distributions](#104-central-distributions)
- [11. Character traces and uniqueness](#11-character-traces-and-uniqueness)
  - [11.1 Weyl integration with the two signs](#111-weyl-integration-with-the-two-signs)
  - [11.2 Trace matching](#112-trace-matching)
  - [11.3 Uniqueness modulo orbital null functions](#113-uniqueness-modulo-orbital-null-functions)
- [12. Archimedean transfer](#12-archimedean-transfer)
  - [12.1 Real elliptic classes](#121-real-elliptic-classes)
  - [12.2 Weight-$k$ transfer](#122-weight-k-transfer)
  - [12.3 The singular endpoints](#123-the-singular-endpoints)
- [13. Assembly for global comparison](#13-assembly-for-global-comparison)
  - [13.1 Restricted tensor products](#131-restricted-tensor-products)
  - [13.2 Matching geometric terms](#132-matching-geometric-terms)
  - [13.3 The normalization ledger](#133-the-normalization-ledger)
  - [13.4 Failure modes and boundary cases](#134-failure-modes-and-boundary-cases)
- [14. Final synthesis](#14-final-synthesis)

## 1. The transfer problem

### 1.1 From two trace formulas to one local identity

An inner-form comparison begins with two groups which have different points but share part of their conjugacy geometry. Let $F$ be a local field, let

$$
G=\mathrm{GL}_2(F),
$$

and let $D$ be a quaternion algebra over $F$. When $D$ is split, $D^\times$ is another copy of $G$. When $D$ is division, every noncentral regular semisimple element of $D^\times$ generates a quadratic field, whereas $G$ also has split regular classes. Trace and determinant on $G$, and reduced trace and reduced norm on $D^\times$, identify the quadratic-field classes on the two sides.

The geometric terms of a trace formula are orbital integrals, not point values. Consequently an identification of characteristic polynomials is only the beginning. One must construct functions whose averages along corresponding orbits agree with the correct sign and whose split orbital integrals disappear. At a singular class the centralizer jumps, so regular matching must also be checked against the limiting germ and against the separate central distribution.

The preceding books supplied the three inputs needed here. The geometric trace formula isolated the central and elliptic distributions and proved their convergence. The orbital-integral calculations fixed the measures and reduced the finite-place integrals to lattice, chain, and congruence counts. The selected local Jacquet--Langlands correspondence proved that matching discrete-series characters differ by $-1$ on regular elliptic classes. We now turn those calculations into actual transfer functions. The proof is rank-two throughout: the building is a tree, the invariant quotient has two coordinates, and the only nonzero nilpotent orbit is the regular one.

### 1.2 Standing local conventions

Until Chapter 12, $F$ is nonarchimedean with ring of integers $\mathcal O$, maximal ideal $\mathfrak p=(\varpi)$, residue field $k$, and $|k|=q$. We normalize

$$
v(\varpi)=1,\qquad |x|=q^{-v(x)}.
$$

Put

$$
K=\mathrm{GL}_2(\mathcal O),\qquad
I=\left\{g\in K:g\bmod\mathfrak p\text{ is upper triangular}\right\}.
$$

Thus $[K:I]=q+1$. Haar measures satisfy

$$
\operatorname{vol}(K)=1,
\qquad \operatorname{vol}(I)=\frac1{q+1}.
\tag{1.1}
$$

When $D$ is division, write $\mathcal O_D$ for its maximal order and normalize $dd$ by

$$
\operatorname{vol}(\mathcal O_D^\times)=1.
\tag{1.2}
$$

For a separable quadratic algebra $E/F$, its multiplicative measure has

$$
\operatorname{vol}(\mathcal O_E^\times)=1.
\tag{1.3}
$$

The center $F^\times$ has multiplicative measure $\operatorname{vol}(\mathcal O^\times)=1$. All quotient measures are defined by $dh=dt\,d\dot h$. Quotienting first by the center identifies the measure on $E^\times\backslash H$ with the iterated measure on

$$
(E^\times/F^\times)\backslash(H/F^\times),
$$

so the local integrals below have exactly the projective normalization used in Book 101's global geometric distribution. These compact-unit choices, rather than an unnamed canonical measure, are responsible for the residue-degree factor that appears below.

Test functions are complex-valued, locally constant, and compactly supported. If a central character is imposed, the equivalent compact-mod-center formulation is obtained by the usual central averaging; every formula below then lies in a fixed determinant or reduced-norm shell. We state the compactly supported form because it keeps point values and volumes visible.

### 1.3 What will be proved

There are four principal results.

First, transfer exists locally on the regular set by an explicit slice construction, not by appeal to a general transfer theorem. Second, at a division place the function

$$
f_{\mathrm{ell}}
=-2\mathbf1_K+(q+1)\mathbf1_I
\tag{1.4}
$$

has zero split regular orbital integrals and has orbital integral $-f(E/F)$ on an integral elliptic unit class with centralizer $E^\times$. Since $\mathbf1_{\mathcal O_D^\times}$ has division-side orbital integral $f(E/F)$, equation (1.4) is the unit fundamental lemma in the present normalization.

Third, the same tree calculation gives a second, odd-determinant kernel supported on the edge-reversing Iwahori coset. These two parity kernels, together with conjugation averaging on the compact projective division group, transfer every selected finite-level and type function. This avoids a false shortcut: the orbital integrals of length-$j$ segment stabilizers do not depend only on one integer called depth, so an unspecified triangular matrix of segment counts would not prove a level fundamental lemma. Fourth, regular, singular, and central contributions are kept separate: the regular transfer sign is $-1$, the normalized singular germ is compatible, and central terms are compared with their actual quotient-volume coefficients.

The geometric averaging construction transfers an arbitrary compactly supported division function. The restriction to selected positive-depth packets is instead spectral: ramified dyadic wild types carry character data not supplied by Book 80's tame finite Fourier comparison. We construct their orbital transfers but make no unsupported claim identifying the corresponding split representation.

## 2. Matching classes and measures

### 2.1 The invariant quotient

For $\gamma\in G$, set

$$
t(\gamma)=\operatorname{tr}(\gamma),\qquad
n(\gamma)=\det(\gamma),\qquad
\Delta(\gamma)=t(\gamma)^2-4n(\gamma).
$$

For $\delta\in D^\times$ use reduced trace and reduced norm in the same formulas. A regular semisimple element has $\Delta\ne0$, and its centralizer is the unit group of the quadratic étale algebra

$$
E=F[X]/(X^2-tX+n).
\tag{2.1}
$$

Two regular elements on the same side are conjugate if and only if $(t,n)$ agree. Indeed, on the split side the element makes $F^2$ a free rank-one module over (2.1); on the quaternionic side conjugacy of embeddings of a quadratic field follows by the elementary intertwiner argument in a central simple algebra of degree two. Thus the map

$$
\chi:H_{\mathrm{reg}}\longrightarrow F\times F^\times,
\qquad h\longmapsto(t(h),n(h))
\tag{2.2}
$$

is the regular conjugacy quotient for either inner form.

We say $\gamma$ and $\delta$ **match** if their images under (2.2) agree. If $D$ is division, its image consists of the elliptic points of the quotient: those for which (2.1) is a field. There is no quaternionic class above a split point. This typing condition is the reason a transfer on $G$ must vanish on split regular orbits.

### 2.2 Haar and quotient measures

For $H=G$ or $D^\times$ and regular $h$, let $T=H_h=E^\times$. Define

$$
O_h(f)=\int_{T\backslash H}f(x^{-1}hx)\,d\dot x.
\tag{2.3}
$$

The Weyl determinant is

$$
|D_H(h)|
=\left|\det(1-\operatorname{Ad}(h)\mid\mathfrak h/\mathfrak t)\right|
=\left|\frac{\Delta(h)}{n(h)}\right|.
\tag{2.4}
$$

The equality follows after diagonalizing $h$ with eigenvalues $a,b$: the two root eigenvalues of $\operatorname{Ad}(h)$ are $a/b$ and $b/a$, whose product after subtracting from one is $-(a-b)^2/(ab)$. Both inner forms give the same expression after scalar extension. Hence matching elements have the same Weyl factor.

We also use

$$
I_h(f)=|D_H(h)|^{1/2}O_h(f).
\tag{2.5}
$$

If $dh$ is multiplied by $a$ and $dt$ by $b$, then every orbital integral is multiplied by $a/b$. Formula (2.4) does not change. This simple scaling rule will check every claimed identity.

### 2.3 Transfer and its sign

Let $f\in C_c^\infty(G)$ and $f_D\in C_c^\infty(D^\times)$, with $D$ division. We call $(f,f_D)$ a **matching pair** if

$$
O_\gamma(f)=0
\quad\text{for every split regular }\gamma,
\tag{2.6}
$$

and

$$
O_\gamma(f)=-O_\delta(f_D)
\quad\text{whenever }\gamma\leftrightarrow\delta.
\tag{2.7}
$$

Because of (2.4), the same definition results if $O$ is replaced everywhere by $I$. Our sign convention places the inner-form sign on orbital transfer. Book 80's selected character identity places another sign on characters:

$$
\Theta_\pi(\gamma)=-\Theta_{\pi_D}(\delta).
\tag{2.8}
$$

The two minus signs cancel in Weyl integration, giving equal operator traces. One may instead define signless orbital transfer and insert a minus in the spectral comparison, but mixing the conventions halfway through produces the wrong trace identity.

When $D\simeq M_2(F)$, matching means ordinary conjugacy matching and the transfer sign is $+1$. Under a fixed isomorphism the simplest transfer is $f_D=f$. The sign $-1$ is the Kottwitz sign of the nonsplit inner form in rank two.

### 2.4 Central scaling and involutions

For $z\in F^\times$, put $f^z(h)=f(z^{-1}h)$. Since $z$ is central,

$$
O_{zh}(f^z)=O_h(f).
\tag{2.9}
$$

Moreover, $\det(z\gamma)=z^2\det\gamma$ and $\operatorname{Nrd}(z\delta)=z^2\operatorname{Nrd}\delta$, so central translation preserves matching. Thus every unit-shell lemma immediately yields all even valuation translates.

Inversion also preserves matching. If $f^\vee(h)=f(h^{-1})$, then directly from the definition

$$
O_{h^{-1}}(f^\vee)=O_h(f).
\tag{2.10}
$$

Finally, twisting by a character $\mu:F^\times\to\mathbf C^\times$ through determinant and reduced norm preserves (2.7), because matching elements have equal norm. These three operations account for the central translates and nonminimal twists used later.

## 3. Local descent on the regular set

### 3.1 Why existence is not automatic

An orbital integral is constrained by conjugation invariance, support, and a Jacobian. It is therefore not enough to prescribe arbitrary values at representatives. Near a regular orbit, however, conjugation has a transverse slice, and in degree two that slice can be written down. This gives a local right inverse to the orbital-integral map and explains exactly where singular germs enter.

The construction is useful even though the fundamental functions below are explicit. It proves that transfer is not restricted to those examples, lets us patch auxiliary functions at finitely many places, and identifies uniqueness as uniqueness only modulo functions with zero regular orbital integrals.

### 3.2 A rank-two slice

Fix a regular $h_0\in H$, let $T=H_{h_0}$, and choose an $F$-linear complement $\mathfrak q$ to $\mathfrak t$ in $\mathfrak h$. A sufficiently small compact-open neighborhood of $0$ in $\mathfrak q$ maps, by $X\mapsto T(1+X)$ after shrinking so that $1+X$ is invertible, homeomorphically onto a compact-open neighborhood $\overline U$ of the identity coset in $T\backslash H$. For a sufficiently small compact-open neighborhood $V$ of $h_0$ in $T$, consider

$$
\Phi:\overline U\times V\longrightarrow H,
\qquad (\dot x,t)\longmapsto x^{-1}tx.
\tag{3.1}
$$

At $(T,h_0)$ its differential, in the quotient coordinate just chosen, sends $(X,Y)$ to

$$
(1-\operatorname{Ad}(h_0^{-1}))X+Y.
$$

The first summand is invertible on $\mathfrak q$ precisely because $h_0$ is regular, while the second spans $\mathfrak t$. Hence the differential is invertible. The nonarchimedean inverse function theorem, proved by successive approximation in coordinates, gives neighborhoods on which (3.1) is a homeomorphism and analytic diffeomorphism onto its image.

Its Jacobian in the orbit direction is $|D_H(t)|$ up to the constant imposed by our fixed coordinate measures. Shrinking $V$, absorb that constant into a test function on $\overline U$. This is the concrete rank-two form of semisimple descent.

### 3.3 Prescribing an orbital integral locally

Let $a(t)$ be a locally constant compactly supported function on $V$. Choose $b\in C_c^\infty(\overline U)$ with integral one relative to the quotient coordinate. On the image of (3.1) define

$$
f(x^{-1}tx)=a(t)b(\dot x)J(t)^{-1},
\tag{3.2}
$$

where $J(t)$ is the quotient Jacobian; extend by zero. If the neighborhoods are chosen so that no other conjugate of $V$ enters the image, substitution in (2.3) gives

$$
O_t(f)=a(t).
\tag{3.3}
$$

If the Weyl involution identifies two points of $V$, average (3.2) over it. Then (3.3) holds for the invariant function $a$.

This proof contains the decisive facts: regularity makes the transverse determinant nonzero, compact support permits extension by zero, and the unit integral of $b$ fixes the constant. There is no appeal to an unspecified theorem about all reductive groups.

### 3.4 Patching on compact regular sets

Let $C$ be a compact subset of the regular invariant quotient. Cover it by finitely many slice neighborhoods $V_i$. Because the topology is totally disconnected, refine to a disjoint compact-open partition $C=\bigsqcup C_i$ with $C_i\subset V_i$. Apply (3.2) to the restriction of the desired invariant function on each $C_i$ and add the results. We obtain:

**Proposition 3.1 (regular patching).** Every locally constant compactly supported function on a compact subset of the regular quotient is the orbital-integral function of a compactly supported test function. On $G$, prescriptions on disjoint split and elliptic compact subsets can be realized independently.

The proof also applies over $\mathbf R$ with smooth partitions of unity, provided one works away from $\Delta=0$. It does not solve the singular boundary. If $C$ accumulates at $\Delta=0$, the Jacobian in (3.2) degenerates and a prescribed function must satisfy the germ relations of Chapter 10. The explicit fundamental functions do satisfy them.

## 4. The tree and the elliptic Euler function

### 4.1 Vertices, edges, and stabilizers

The Bruhat--Tits tree $X$ of $\mathrm{PGL}_2(F)$ has vertices the homothety classes $[L]$ of rank-two $\mathcal O$-lattices. Two vertices are adjacent when representatives can be chosen with

$$
\varpi L\subsetneq L'\subsetneq L.
$$

The neighbors of $[L]$ are the lines in $L/\varpi L$, so every vertex has degree $q+1$. The stabilizer of the standard vertex is $F^\times K$; the stabilizer of the oriented standard edge is $F^\times I$.

For an element $\gamma$ with unit determinant, $x^{-1}\gamma x\in K$ exactly when $\gamma$ fixes the vertex $x[\mathcal O^2]$. Likewise, membership in $I$ means that $\gamma$ fixes the associated oriented edge. Passing from $x$ to the left by the centralizer identifies cells in the same $T$-orbit. Thus orbital integrals of $\mathbf1_K$ and $\mathbf1_I$ are weighted counts of fixed vertices and oriented edges.

The word “weighted” matters. A cell represented by $x$ contributes the volume of its right stabilizer divided by the volume of $T\cap xKx^{-1}$ or $T\cap xIx^{-1}$. These are exactly the reciprocal stabilizer factors in the lattice formulas of Book 102.

### 4.2 Orbital integrals as weighted fixed-cell counts

Let $X^\gamma$ be the fixed subtree. Write $V(X^\gamma)$ and $E^{\mathrm{or}}(X^\gamma)$ for its vertices and oriented edges. With compact-unit measure on $T$, double-coset decomposition gives

$$
O_\gamma(\mathbf1_K)
=\sum_{T\backslash V(X^\gamma)}
\frac1{\operatorname{vol}(T_v)},
\tag{4.1}
$$

and

$$
(q+1)O_\gamma(\mathbf1_I)
=\sum_{T\backslash E^{\mathrm{or}}(X^\gamma)}
\frac1{\operatorname{vol}(T_e)}.
\tag{4.2}
$$

Here $T_v=T\cap xKx^{-1}$ and $T_e=T\cap xIx^{-1}$ for representatives of the corresponding lattice or chain. They are compact even though the scalar direction of $T$ is not: a nonunit scalar does not stabilize an actual lattice. Formula (4.2) contains the factor $q+1$ because $\operatorname{vol}(I)=(q+1)^{-1}$.

There is one small equivariant subtlety. The two orientations of a geometric edge need not be two different $T$-orbits: a ramified torus uniformizer interchanges them. Nevertheless one half of the oriented groupoid count is always the geometric-edge count. If the two orientations are separate, this is obvious. If an element of $T$ reverses the edge, the oriented stabilizer has index two in the setwise stabilizer, and the factor $1/2$ converts the reciprocal stabilizer volumes. Consequently

$$
O_\gamma\left(\mathbf1_K-\frac{q+1}{2}\mathbf1_I\right)
=\chi_T(X^\gamma),
\tag{4.3}
$$

where the right side is the equivariant weighted number of vertex orbits minus the weighted number of geometric-edge orbits. This observation is what makes (4.3) valid also for the edge-inverting core of a ramified torus.

This is an identity of finite sums for elliptic $\gamma$. For split $\gamma$, truncate the fixed tube to distance $N$ from a base vertex, form the alternating sum, and then pass to the quotient by $T$. Boundary vertices and edges pair, so the stable value is again (4.3). No convergence is hidden in the notation.

### 4.3 The fixed-subtree Euler calculation

Put

$$
e_{\mathrm{EP}}=\mathbf1_K-\frac{q+1}{2}\mathbf1_I.
\tag{4.4}
$$

**Lemma 4.1 (rank-two fixed-subtree lemma).** Let $\gamma\in G$ be regular with integral trace and unit determinant, and let $T=F[\gamma]^\times$.

1. If $T$ is split, then $O_\gamma(e_{\mathrm{EP}})=0$.
2. If $T=E^\times$ is elliptic, then

$$
O_\gamma(e_{\mathrm{EP}})=\frac{f(E/F)}2.
\tag{4.5}
$$

**Proof strategy.** Prune finite branches from the fixed subtree. Removing a terminal vertex together with its incident edge changes neither the weighted Euler sum nor the stabilizer ratio. What remains is the minimal subtree of the torus.

**Proof.** Pruning must be done equivariantly. A terminal geometric edge orbit and its terminal vertex orbit have the same compact stabilizer unless an edge inversion occurs; in the inversion case the half-oriented convention just proved inserts exactly the compensating index two. Removing such an orbit pair therefore changes neither side of (4.3). Iteration reduces the fixed subtree to the minimal $T$-invariant core.

In the split case that core is an apartment. The valuation quotient of $T=F^\times\times F^\times$ translates along it. A fundamental cycle has one weighted vertex and one weighted geometric edge, with equal stabilizers, so its Euler value is zero. This proves the first assertion, including elements close to the center: their fixed tubes differ from the apartment by branch orbits already removed by pruning.

Suppose $E/F$ is unramified. The projective torus $E^\times/F^\times$ fixes the vertex represented by $\mathcal O_E$. This is the entire core. Its compact stabilizer is $\mathcal O_E^\times$, of volume one, so the core contributes $1$. A generator of a nonmaximal order fixes extra finite branches, but equivariant pruning removes them. Since $f(E/F)=2$, this is $f(E/F)/2$.

Suppose $E/F$ is ramified. The core is one geometric edge. An $E$-uniformizer exchanges its endpoints, so the endpoints form one $T$-orbit and the two oriented core edges also form one $T$-orbit. Both oriented stabilizers are $\mathcal O_E^\times$ of volume one. The vertex contribution is therefore $1$, while one half of the oriented-edge contribution is $1/2$. Their difference is $1/2=f(E/F)/2$. Extra branches prune as before. The proof uses only the action of a valuation-one element and hence remains valid for every separable ramified quadratic extension, including residue characteristic two. $\square$

The factor $1/2$ is not arbitrary. It records the edge inversion by a ramified torus. Omitting it is the common source of a false claim that one scalar multiple of $\mathbf1_K$ transfers to the quaternionic unit in both ramification types.

Three concrete fixed sets make the calculation visible. Suppose first that $E/F$ is unramified and that $\gamma\in\mathcal O_E^\times$ has irreducible reduction. The lattice $\mathcal O_E$, viewed as a rank-two $\mathcal O$-lattice, is the unique fixed vertex modulo $E^\times$. No line in $\mathcal O_E/\mathfrak p\mathcal O_E\simeq k_{q^2}$ is stable under multiplication by $\bar\gamma$, because such a line would be a one-dimensional $k$-eigenspace and would split the irreducible characteristic polynomial. Thus

$$
O_\gamma(\mathbf1_K)=1,
\qquad O_\gamma(\mathbf1_I)=0,
$$

and (4.5) is immediate.

For a ramified example with odd residue characteristic, write $E=F(\tau)$ with $\tau^2=u\varpi$ and take $\gamma=a+b\tau$ with $a,b\in\mathcal O^\times$. The minimal $E^\times$-invariant set is an edge whose two endpoint lattices differ by the action of a ramified uniformizer. That uniformizer exchanges both endpoints and both orientations. Thus the quotient has vertex weight $1$ and half-oriented edge weight $1/2$, leaving Euler value $1/2$. In residue characteristic two the square-root model may fail, but a valuation-one element of a separable ramified quadratic field acts on the same edge core, so the argument is unchanged.

Finally take $\gamma=\operatorname{diag}(a,b)$ with $a,b\in\mathcal O^\times$. Its torus fixes the standard apartment. If $v(a-b)=c$, the element itself fixes a tube of radius governed by $c$, but the diagonal torus translates along the apartment. A finite quotient of a length-$N$ portion has equally many new vertices and new edges at both ends. Letting $N$ grow leaves Euler value zero. This explains why checking only distinct reduction eigenvalues would prove too little: the same cancellation must persist when $a\equiv b\pmod{\mathfrak p^c}$ for arbitrarily large $c$.

### 4.4 The explicit elliptic Euler function

Define

$$
f_{\mathrm{ell}}=-2e_{\mathrm{EP}}
=-2\mathbf1_K+(q+1)\mathbf1_I.
\tag{4.6}
$$

Lemma 4.1 immediately gives

$$
O_\gamma(f_{\mathrm{ell}})=
\begin{cases}
0,&F[\gamma]\simeq F\times F,\\
-f(E/F),&F[\gamma]=E\text{ is a field},
\end{cases}
\tag{4.7}
$$

provided $\gamma$ has integral trace and unit determinant. If these support conditions fail, both terms in (4.6) vanish. Notice that (4.7) holds for nonmaximal orders as well as maximal ones: the extra fixed branches cancel in the Euler sum. This uniform cancellation is the fundamental lemma's content.

## 5. The unit fundamental lemma

### 5.1 Split inner forms

If $D\simeq M_2(F)$ and the chosen maximal order corresponds to $M_2(\mathcal O)$, the unit functions are literally identified:

$$
\mathbf1_{\mathcal O_D^\times}\longleftrightarrow\mathbf1_K.
\tag{5.1}
$$

Matching classes are the same classes, group and torus measures agree, and conjugation integrals are equal term by term. This is the hyperspecial unit lemma at an unramified split place. It includes split and elliptic regular classes and needs no sign.

### 5.2 A ramified quaternion place

Now suppose $D$ is division. Conjugation preserves its unique maximal order, so $\mathbf1_{\mathcal O_D^\times}$ is invariant. If $\delta$ is regular with $E=F[\delta]$, then

$$
O_\delta(\mathbf1_{\mathcal O_D^\times})
=\mathbf1_{\mathcal O_D^\times}(\delta)
\operatorname{vol}(E^\times\backslash D^\times).
\tag{5.2}
$$

The valuation $v_D=v\circ\operatorname{Nrd}$ maps $D^\times/\mathcal O_D^\times$ to $\mathbf Z$. On $E^\times$ its image is $f(E/F)\mathbf Z$, since

$$
v_D(e)=v(N_{E/F}e)=f(E/F)v_E(e).
$$

Compact unit groups have volume one. A fundamental domain therefore has $f(E/F)$ valuation cosets, each of volume one, and

$$
O_\delta(\mathbf1_{\mathcal O_D^\times})
=f(E/F)\mathbf1_{\mathcal O_D^\times}(\delta).
\tag{5.3}
$$

### 5.3 Proof of the unit identity

**Theorem 5.1 (unit fundamental lemma for the division inner form).** With measures (1.1)--(1.3), the pair

$$
\boxed{
f_{\mathrm{ell}}=-2\mathbf1_K+(q+1)\mathbf1_I,
\qquad
f_D^0=\mathbf1_{\mathcal O_D^\times}}
\tag{5.4}
$$

is matching in the sense of (2.6)--(2.7).

**Proof.** A class meeting either support has integral trace and unit norm. On a split regular class, (4.7) gives $O_\gamma(f_{\mathrm{ell}})=0$. Let $\gamma\leftrightarrow\delta$ be elliptic with centralizer $E^\times$. Membership in $K$ or $\mathcal O_D^\times$ is equivalent to integrality together with unit norm, because trace and norm are shared. If that condition fails, both orbital integrals vanish. If it holds, (4.7) and (5.3) give

$$
O_\gamma(f_{\mathrm{ell}})=-f(E/F)
=-O_\delta(f_D^0).
$$

This proves every regular class, including ramified, unramified, nonmaximal-order, and scalar-reduction cases. $\square$

The proof is a fundamental lemma rather than a definition: both functions in (5.4) are explicit before the class is chosen, and the fixed-subtree calculation proves the equality uniformly over infinitely many orbits.

### 5.4 Why the raw units do not match

For a maximal elliptic order, Book 102 computed

$$
O_\gamma(\mathbf1_K)=1,
$$

whereas (5.3) is $2$ for unramified $E$ and $1$ for ramified $E$. No constant $c$ can make $c\mathbf1_K$ match the division unit on both kinds of tori. The Iwahori term in (5.4) is exactly what distinguishes the vertex fixed by an unramified torus from the edge midpoint fixed by a ramified torus.

This also explains why measure normalization cannot be treated as cosmetic. Rescaling the $E^\times$ measure separately for ramified and unramified $E$ could hide the discrepancy, but those measures would not be a single compatible family and would break the global product formula. The correct response is to change the split test function, not the ledger.

## 6. The Iwahori fundamental lemma

### 6.1 The two Iwahori cells

Let

$$
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

The two double cosets inside the vertex stabilizer $K$ are $I$ and $IwI$. Their volumes are

$$
\operatorname{vol}(I)=\frac1{q+1},
\qquad
\operatorname{vol}(IwI)=\frac q{q+1}.
\tag{6.1}
$$

The first fixes an oriented edge; the second moves it across its initial vertex. Put

$$
e_I=(q+1)\mathbf1_I,
\qquad \tau_w=(q+1)\mathbf1_{IwI}.
\tag{6.2}
$$

Then $e_I$ is the convolution identity in the $I$-bi-invariant algebra and

$$
(\tau_w+e_I)*(\tau_w-qe_I)=0.
\tag{6.3}
$$

The two characters of this finite two-cell algebra send $\tau_w$ to $q$ and $-1$. They are the trivial and sign characters. The sign character is the $I$-fixed line of Steinberg, while both characters occur together in the two-dimensional $I$-fixed module of a generic unramified principal series. We do not claim that these two cells exhaust the full affine Iwahori algebra.

### 6.2 The alternating Iwahori line

The function $e_{\mathrm{EP}}$ of (4.4) can be viewed as the alternating cellular trace of the tree: vertices contribute positively and unoriented edges negatively. Because an unoriented edge has two orientations, its coefficient is $(q+1)/2$. This alternating line is independent of the chosen standard edge up to conjugacy. It is not the sign idempotent. Since $\mathbf1_K=\mathbf1_I+\mathbf1_{IwI}$,

$$
e_{\mathrm{EP}}
=\frac1{q+1}\left(\tau_w-\frac{q-1}{2}e_I\right).
\tag{6.3a}
$$

Its values under the trivial and sign characters of the two-cell algebra are $1/2$ and $-1/2$. Thus its trace on the full two-dimensional unramified principal-series $I$-module is zero, while $-2e_{\mathrm{EP}}$ has trace one on the Steinberg line and trace $-1$ on the one-dimensional determinant constituent. The latter trace is why global comparison must separately remove norm and determinant characters.

For split regular $\gamma$ with distinct reduction eigenvalues, Book 102's direct count gives

$$
O_\gamma(\mathbf1_K)=1,
\qquad
O_\gamma(\mathbf1_I)=\frac2{q+1},
$$

so $O_\gamma(e_{\mathrm{EP}})=0$. The tree proof extends this cancellation to arbitrary split depth, where residue-line counting alone is insufficient. For unramified elliptic regular reduction, the Iwahori integral is zero and the vertex integral is one. For ramified or scalar reduction, many stable edges occur, but pruning gives the half-weight in (4.5).

### 6.3 The Iwahori theorem

**Theorem 6.1 (Iwahori fundamental lemma).**

1. At a split inner-form place, every function in the Iwahori algebra transfers to the identical function under a compatible identification $D^\times\simeq G$.
2. At a division place, the alternating Euler function $e_{\mathrm{EP}}$ has

$$
O_\gamma(e_{\mathrm{EP}})=0
\quad(\gamma\text{ split regular}),
$$

and

$$
O_\gamma(e_{\mathrm{EP}})=\frac12O_\delta(\mathbf1_{\mathcal O_D^\times})
\quad(\gamma\leftrightarrow\delta).
\tag{6.4}
$$

Consequently $-2e_{\mathrm{EP}}$ transfers to the division unit with sign $-1$.

**Proof.** The split assertion is termwise equality. At a division place, equations (4.5) and (5.3) give (6.4). Within the vertex-edge space, requiring zero orbital integral on a regular-reduction split class and the displayed value on an unramified elliptic class determines the two coefficients up to the stated normalization. The fixed-tube argument extends split vanishing from regular reduction to all depths, and the edge-core calculation supplies the ramified value. $\square$

### 6.4 Convolution and normalization checks

Three checks prevent normalization errors. First, replacing $\mathbf1_I$ by the probability idempotent $(q+1)\mathbf1_I$ changes the displayed coefficient in (4.4). Second, using oriented rather than geometric edges omits the factor $1/2$. Third, the transfer statement concerns orbital integrals, not equality in the two Hecke algebras: $D^\times$ has no building edge at a division place.

Convolution by a central translate commutes with $e_{\mathrm{EP}}$. Twisting by an unramified character multiplies a fixed determinant shell by a constant on both sides. Hence Theorem 6.1 supplies the unramified twists of the special packet without a new count.

## 7. Spherical shells and central translates

### 7.1 Determinant shells

For $r\in\mathbf Z$ let

$$
f_{r,0}=\mathbf1_{\varpi^rK}.
$$

Then

$$
O_\gamma(f_{r,0})=O_{\varpi^{-r}\gamma}(\mathbf1_K).
\tag{7.1}
$$

The support condition is $v(\det\gamma)=2r$ together with integrality of $\varpi^{-r}\operatorname{tr}\gamma$. On the division side use $\mathbf1_{\varpi^r\mathcal O_D^\times}$. Equation (2.9) transports the unit lemma to these shells:

$$
-2\mathbf1_{\varpi^rK}+(q+1)\mathbf1_{\varpi^rI}
\quad\longleftrightarrow\quad
\mathbf1_{\varpi^r\mathcal O_D^\times}.
\tag{7.2}
$$

Odd reduced-norm valuation shells on $D^\times$ cannot be reached by a scalar translate. They are treated by invariant congruence shells or type functions, not by pretending that a square root of $\varpi$ is central.

### 7.2 The split-place spherical lemma

At a place where the quaternion algebra splits, put

$$
h_m=\mathbf1_{K\operatorname{diag}(\varpi^m,1)K},\qquad m\ge0.
$$

Under a maximal-order-preserving isomorphism, $h_m$ is the same function on both inner forms. Therefore

$$
O_\gamma(h_m)=O_\delta(h_m)
\tag{7.3}
$$

for matching classes. This is the spherical fundamental lemma in rank two. Its proof is not Satake theory: the two orbital integrals have identical domains, integrands, and quotient measures. Satake theory becomes useful for convolution and eigenvalues after the geometric identity is fixed.

### 7.3 Central translation at a division place

For a conjugation-invariant compact-open subset $C\subset D^\times$, Book 102's valuation decomposition gives

$$
O_\delta(\mathbf1_C)=f(E/F)\mathbf1_C(\delta).
\tag{7.4}
$$

The regular patching proposition constructs a split-side transfer on every compact subset away from the center. For invariant shells one can do better and remain uniform at the singular boundary: extend the shell's value as a locally constant function of $(t,n)$ and multiply it by the appropriate even or odd parity kernel. Chapter 8 proves this construction. Since the multiplier is constant along an orbit, the unit or edge-reversing calculation immediately gives (7.4) with the transfer sign.

Thus the unit lemma is not isolated. It is the depth-zero member of a family of invariant shell identities. The selected higher-depth members are made explicit in Chapters 8 and 9.

### 7.4 The first Hecke shell

The condition $x^{-1}\gamma x\in K\operatorname{diag}(\varpi,1)K$ says that for $L=x\mathcal O^2$,

$$
\gamma L\subset L,
\qquad L/\gamma L\simeq\mathcal O/\mathfrak p.
\tag{7.5}
$$

Hence its orbital integral is the weighted number of stable vertices together with a selected line in $L/\varpi L$. If the reduction has two distinct eigenvalues, two lines contribute; if its characteristic polynomial is irreducible, none does. This direct finite count agrees on two split copies of $G$ and supplies the first nontrivial check of (7.3). It is not, by itself, the division-place odd-shell transfer: the whole spherical double coset contains split elements.

The correct odd kernel uses the edge-reversing coset. Put

$$
\eta=\begin{pmatrix}0&1\\ \varpi&0\end{pmatrix}.
\tag{7.6}
$$

Then $\eta^2=\varpi I_2$ and a direct multiplication shows $\eta I\eta^{-1}=I$. Thus every element of $\eta I$ reverses the underlying standard edge. Define

$$
f_{\mathrm{odd}}=-(q+1)\mathbf1_{\eta I}.
\tag{7.7}
$$

**Proposition 7.1 (odd-shell fundamental kernel).** If $\gamma$ is split regular, then $O_\gamma(f_{\mathrm{odd}})=0$. If $\gamma$ is elliptic with integral trace and determinant valuation one, then its centralizer is ramified and

$$
O_\gamma(f_{\mathrm{odd}})=-1.
\tag{7.8}
$$

On the division side, every regular $\delta$ with $v_D(\delta)=1$ has ramified centralizer and

$$
O_\delta(\mathbf1_{\Pi\mathcal O_D^\times})=1,
\tag{7.9}
$$

because $\Pi\mathcal O_D^\times$ is exactly the conjugation-invariant set $\{d:v_D(d)=1\}$. Consequently (7.7) is the signed transfer of the invariant odd unit shell.

**Proof.** A split semisimple element acts on the tree either with a fixed apartment or by a nonzero translation along its apartment; it cannot reverse an edge. Its orbit therefore misses $\eta I$, proving the first assertion.

If $v(\det\gamma)=1$ and $\gamma$ is elliptic integral, then $v(\operatorname{tr}\gamma)>0$: otherwise the reduction of its polynomial has two distinct roots $0$ and $\overline{\operatorname{tr}\gamma}$ and Hensel lifting makes the polynomial split. Its characteristic polynomial is therefore Eisenstein. Hence $E=F[\gamma]$ is ramified, $\mathcal O[\gamma]=\mathcal O_E$, and the fixed core is one edge. The two orientations of that edge form one $E^\times$-orbit because a valuation-one element interchanges them. The oriented stabilizer is $\mathcal O_E^\times$, of volume one. The double-coset count used in (4.2) therefore gives

$$
O_\gamma(\mathbf1_{\eta I})=\operatorname{vol}(I)=\frac1{q+1},
$$

which proves (7.8). Finally $v_D(E^\times)=\mathbf Z$ for a ramified quadratic field, so the quotient in the division calculation has one valuation class. Conjugation invariance of the saturated shell gives (7.9), exactly as in (5.3). $\square$

Central translation of (7.7) treats every odd determinant shell. Together with (7.2), the even and odd kernels now cover both components of $D^\times/F^\times$; no fictitious central square root of $\varpi$ is needed.

## 8. Selected congruence levels

### 8.1 Conjugation averaging

The level problem becomes cleaner if one first separates spectral normalization from orbital data. Let $f_D\in C_c^\infty(D^\times)$. The projective group $D^\times/F^\times$ is compact. Choose probability Haar measure $d\bar x$ on it and put

$$
f_D^{\natural}(d)
=\int_{D^\times/F^\times}f_D(x^{-1}dx)\,d\bar x.
\tag{8.1}
$$

The function $f_D^{\natural}$ is locally constant, compactly supported, and conjugation invariant. Averaging changes neither orbital nor representation traces:

$$
O_\delta(f_D^{\natural})=O_\delta(f_D),
\qquad
\operatorname{tr}\rho(f_D^{\natural})=\operatorname{tr}\rho(f_D).
\tag{8.2}
$$

For the first equality, insert (8.1), interchange the two compact integrals, and translate the orbit variable by $x$; quotient Haar measure is invariant. For the second, $\rho(f_D^x)=\rho(x)^{-1}\rho(f_D)\rho(x)$, so its trace is unchanged before averaging. The same proof works in a fixed-central-character Hecke space after passing throughout to the projective quotient.

If $E=F[\delta]$, conjugation invariance and (5.3) give the exact formula

$$
O_\delta(f_D)
=f(E/F)f_D^{\natural}(\delta).
\tag{8.3}
$$

Thus an arbitrary selected matrix coefficient has been reduced, without loss of any orbital or spectral information, to a scalar function on the division invariant quotient.

### 8.2 Extending functions on the invariant quotient

Write $\mathcal Q=F\times F^\times$ for the trace--norm quotient. On a fixed reduced-valuation shell, the map

$$
D^\times/\!\!/D^\times\longrightarrow\mathcal Q,
\qquad d\longmapsto(\operatorname{Trd}d,\operatorname{Nrd}d)
\tag{8.4}
$$

is a homeomorphism onto the closed subset consisting of division-admissible quadratic polynomials. Here the scalar points are retained in the closure. Injectivity is conjugacy of quadratic embeddings. The shell $\{d:v_D(d)=m\}=\Pi^m\mathcal O_D^\times$ is compact. Its conjugacy quotient is compact, the target is Hausdorff, and the continuous bijection onto its image is therefore a homeomorphism; its image is compact and hence closed.

We need the following elementary extension fact.

**Lemma 8.1 (clopen extension).** Let $C$ be a compact subset of the image of (8.4), and let $a:C\to\mathbf C$ be locally constant. There is a compactly supported locally constant function $\widetilde a$ on $\mathcal Q$ whose restriction to $C$ is $a$.

**Proof.** The finite image $a(C)=\{c_1,\ldots,c_r\}$ gives a disjoint clopen partition $C=\bigsqcup C_i$. Nonarchimedean affine space has a basis of compact-open boxes. Compactness and separation of the closed sets $C_i$ allow finitely many boxes to be refined to pairwise disjoint compact-open neighborhoods $U_i$ with $U_i\cap C=C_i$. Then $\widetilde a=\sum_i c_i\mathbf1_{U_i}$ works. $\square$

Apply the lemma to $a(t(\delta),n(\delta))=f_D^{\natural}(\delta)$ on the **entire** compact invariant image of each valuation shell meeting the support, taking $a=0$ off the support inside that shell. Put

$$
A(h)=\widetilde a(t(h),n(h)).
\tag{8.5}
$$

This is a conjugation-invariant multiplier on either inner form. Most importantly, it is constant along every orbit, so

$$
O_\gamma(AF)=A(\gamma)O_\gamma(F)
\tag{8.6}
$$

for every test function $F$. Formula (8.6), rather than an unproved claim that segment counts depend on one depth parameter, is the mechanism that carries the unit calculation to arbitrary selected level.

### 8.3 The invariant-level transfer theorem

For an integer $r$, set

$$
F_{2r}=-2\mathbf1_{\varpi^rK}+(q+1)\mathbf1_{\varpi^rI},
\tag{8.7}
$$

and

$$
F_{2r+1}=-(q+1)\mathbf1_{\varpi^r\eta I}.
\tag{8.8}
$$

The subscript records determinant valuation. Theorems 5.1 and Proposition 7.1 say

$$
O_\gamma(F_m)=
\begin{cases}
0,&\gamma\text{ split regular},\\
-f(E/F),&\gamma\text{ elliptic of shell }m,
\end{cases}
\tag{8.9}
$$

where in the odd case $E/F$ is ramified and $f(E/F)=1$.

**Theorem 8.2 (finite-level fundamental lemma).** Let $f_D\in C_c^\infty(D^\times)$. Decompose $f_D^{\natural}$ into the finitely many reduced-valuation shells meeting its support. On shell $m$, choose an extension $A_m$ as in (8.5), and define

$$
f=\sum_m A_mF_m.
\tag{8.10}
$$

Then $f\in C_c^\infty(G)$ and $(f,f_D)$ is matching in the signed sense (2.6)--(2.7). The construction may be made inside the same finite trace--norm congruence depth as $f_D^{\natural}$, after increasing the depth only enough to separate the finitely many clopen pieces. If the noncanonical extensions $A_m$ are transported along with the data, the construction is compatible with central translation, inversion, and twisting through norm.

**Proof.** The product $A_mF_m$ is compactly supported because $F_m$ is. If $\gamma$ is split regular, every summand has zero orbital integral by (8.9). If $\gamma\leftrightarrow\delta$ is elliptic and belongs to shell $m$, disjoint shell support, (8.6), (8.9), and the defining property of $A_m$ give

$$
O_\gamma(f)
=-f(E/F)f_D^{\natural}(\delta)
=-O_\delta(f_D)
$$

by (8.3). This proves matching on every regular class. Central translation, inversion, and twisting induce homeomorphisms of the invariant quotient and preserve the base identities by Section 2.4; transporting each chosen extension through the same homeomorphism proves the compatibility assertion. The extension proof uses finitely many compact-open boxes, so all multipliers can be chosen at finite congruence depth. $\square$

This theorem is stronger geometrically than the selected statement needed later: it transfers every compactly supported division function. The selected restriction reappears only when one asks which split and division representations have the character identity needed to interpret the transferred traces. Book 80 supplies that spectral identity for special and tame dihedral packets, not for omitted primitive wild packets.

In a fixed-central-character Hecke space, choose one even and one odd valuation shell as a fundamental domain for the scalar action. Apply Theorem 8.2 to the two compact restrictions and extend the resulting functions by inverse central covariance. Equations (2.9) and equality of determinant and reduced norm show that the extension is independent of the chosen representatives. Thus the theorem applies exactly to the compact-mod-center type traces used below.

### 8.4 Congruence depth and scalar reduction

The standard level subgroups still explain the finite nature of (8.10). The subgroup $K_0(\mathfrak p^n)$ stabilizes a length-$n$ segment, and

$$
[K:K_0(\mathfrak p^n)]=q^{n-1}(q+1).
\tag{8.11}
$$

The subgroup $K_1(\mathfrak p^n)$ remembers a primitive terminal generator, and

$$
[K:K_1(\mathfrak p^n)]=q^{2n}-q^{2n-2}.
\tag{8.12}
$$

Consequently every multiplier $A_m$ that is constant modulo $\mathfrak p^n$ turns (8.7) or (8.8) into a finite linear combination of characteristic functions of explicit congruence pieces. In the original type construction, character projection on a primitive terminal generator is the finite Fourier idempotent

$$
\frac1{|(\mathcal O/\mathfrak p^n)^\times|}
\sum_u\xi(u)^{-1}[u].
\tag{8.13}
$$

After the division type trace containing (8.13) is conjugation-averaged, smoothness reduces that average to a finite sum on a sufficiently deep compact quotient. Theorem 8.2 transfers this averaged function. We do not claim that the prepared split transfer is the raw $K_1$ idempotent before averaging.

When $\bar\gamma$ is scalar, every residue line is invariant, and raw segment counts proliferate with the conductor of $\mathcal O[\gamma]$. Nothing in Theorem 8.2 replaces that exact behavior by $q+1$. Instead the multiplier records the full trace--norm congruence class, while the parity kernel has already proved its orbital identity uniformly by equivariant pruning. The identity therefore persists through all scalar-reduction annuli. Chapter 10 verifies that this uniform regular matching has precisely the required singular germ.

## 9. Special and dihedral type functions

The geometric transfer of Chapter 8 was valid for every nonarchimedean local field. In this chapter we impose $\operatorname{char}F=0$, exactly as in Book 80, because the selected Jacquet--Langlands character theorem used to identify representation traces was proved there under that hypothesis.

### 9.1 Type idempotents and matrix coefficients

Let $J\subset G$ be compact modulo center and let $\lambda$ be an irreducible finite-dimensional smooth representation of $J$. On a fixed-central-character space, put

$$
p_\lambda(j)=\frac1{\operatorname{vol}(J/Z)}
\operatorname{tr}\lambda(j^{-1})
\quad(j\in J),
\tag{9.1}
$$

and zero off $J$, with the prescribed inverse central covariance. Schur orthogonality gives

$$
\operatorname{tr}\pi(p_\lambda)=\dim\operatorname{Hom}_J(\lambda,\pi).
\tag{9.2}
$$

Indeed, on each copy of $\lambda$, the operator $p_\lambda$ is $(\dim\lambda)^{-1}$ times the identity, so its operator trace is one. The actual convolution idempotent is $(\dim\lambda)p_\lambda$; its trace is $\dim\lambda$ times the multiplicity. Confusing these two normalizations produces a dimension error.

The same definition applies to $J'\subset D^\times$. Equality of dimensions in (9.2) is not by itself orbital transfer. The geometric transfer is obtained by applying Theorem 8.2 to $p_{\lambda'}$; conjugation averaging preserves (9.2) by (8.2).

### 9.2 Special packets

For an unramified character $\mu$, the split special representation $\operatorname{St}\otimes(\mu\circ\det)$ has its minimal line at Iwahori level, while its division companion $\mu\circ\operatorname{Nrd}$ is trivial on $\mathcal O_D^\times$. The relevant functions are therefore a norm twist of the pair in (5.4). The tree proof gives their orbital transfer and trace one on the selected representations. The split Euler function has trace zero on a generic unramified principal series but trace $-1$ on the associated one-dimensional determinant constituent, as (6.3a) shows; removing that residual character is a separate global step.

If $\mu$ is ramified of conductor $m>0$, both selected conductors are $2m$. The division type trace is a compact-mod-center function supported at finite unit depth. Choose representatives in the even and odd valuation shells, apply Theorem 8.2 there, and restore central covariance. Equivalently, multiply each compact shell by the same character through determinant and reduced norm. Equality of these norms on matching classes preserves (2.7). No assertion that a ramified character is constant on an entire determinant shell is needed; it generally is not.

### 9.3 Depth-zero dihedral packets

Let $E/F$ be unramified quadratic and let $\bar\theta:k_{q^2}^\times\to\mathbf C^\times$ be regular. On a regular residue element $x\notin k^\times$, the division type trace is

$$
\bar\theta(x)+\bar\theta(x^q),
\tag{9.3}
$$

whereas the split cuspidal type trace is

$$
-\bar\theta(x)-\bar\theta(x^q).
\tag{9.4}
$$

We recall the finite proof because it is the fundamental calculation. Regard $k_{q^2}$ as a two-dimensional $k$-space. Projection to the $\bar\theta$-isotypic part averages multiplication operators over $k_{q^2}^\times$. Fourier transform in the complementary one-dimensional direction has two stationary embeddings, $x$ and $x^q$; all nonstationary additive-character orbits sum to zero. Passing to the cuspidal quotient subtracts the second Bruhat cell, producing the minus sign in (9.4). Regularity ensures the two characters are distinct and cancels the idempotent denominator against the free torus orbit.

Equations (9.3)--(9.4) are a spectral sign check, not an orbital proof for two preassigned type functions. For the actual fundamental lemma, start with the division type trace $p_{\lambda'}$, average it as in (8.1), and apply Theorem 8.2. The resulting split function has the required orbital integrals. Its trace on the depth-zero split packet is then forced by the two signs in Weyl integration, while (9.3)--(9.4) identify that packet and verify the normalization. This order of argument does not infer orbital transfer from equality of one representation trace.

### 9.4 Positive-depth tame packets

Let $(E,\theta)$ be a tame admissible pair. At its last nontrivial unit layer,

$$
\theta(1+x)=\psi_E(\beta x).
\tag{9.5}
$$

The split and division representation characters reduce to finite Fourier sums on the complements of $E$ in $M_2(F)$ and $D$. Choose $j$ with $jz=\sigma(z)j$. The complementary line is $Ej$, and the commutator form is a scalar multiple of

$$
(u,v)\longmapsto
\operatorname{Tr}_{E/F}\bigl(\beta(u\sigma(v)-v\sigma(u))j^2\bigr).
\tag{9.6}
$$

The square $j^2$ lies in the norm class defining the cyclic algebra. The split and division algebras use the two different classes of $F^\times/N_{E/F}(E^\times)$. Therefore their normalized finite Fourier indices differ by

$$
\omega_{E/F}(j_D^2/j_G^2)=-1.
\tag{9.7}
$$

Changing $j$, the polarization, or additive coordinates multiplies both sides by the same norm-class factor. The tame rectifier cancels the remaining torus Gauss phase. Thus (9.7) is exactly $-1$.

Here is the finite-index calculation in one coordinate. After quotienting the radical, choose a $k$-basis so that, in odd residual characteristic, the relevant quadratic phase is $ax^2$. Its normalized Gauss sum is

$$
g(a)=|k|^{-1/2}\sum_{x\in k}\psi_k(ax^2).
$$

Changing $a$ to $a'$ changes the quotient by the quadratic character of $a'/a$. The two cyclic algebras force this ratio to be the nonnorm class, whose quadratic character is $-1$. In residual characteristic two, quadratic-form notation is replaced by the associated nondegenerate alternating module together with its quadratic refinement; the tame rectifier supplies the corresponding index change. The selected dyadic case is unramified and tame, so that refinement is nondegenerate. Ramified dyadic wild data are excluded because the refinement is no longer determined by the cyclic-algebra class alone.

At several positive-depth layers one might fear a product of many minus signs. That does not occur. Trace-dual successive quotients away from the last active layer occur in paired hyperbolic planes, whose normalized Fourier indices multiply to $1$. Only the anisotropic complementary quotient left by the common torus contributes to the ratio, and that quotient records the single Brauer-class difference between $M_2(F)$ and $D$. Hence the total ratio is one $-1$, independent of depth.

Near the center, extra embeddings enter the compact-induction trace. Book 80 filters them by the largest congruence depth at which they agree with the fixed embedding. Each graded fiber is an affine space over $k$; nonstationary fibers sum to zero, while stationary fibers have the form (9.6). The radicals are the common torus directions and have equal cardinality on both sides. Quotienting by them and applying (9.7) pairs every shell with sign $-1$. This is the previously proved character identity on all regular elliptic classes, not a replacement for Theorem 8.2's orbital construction.

### 9.5 The level-specific fundamental lemma

**Theorem 9.1 (special and selected dihedral fundamental lemma).** Let $(\pi,\pi_D)$ be either a special pair or one of the depth-zero or tame positive-depth dihedral pairs constructed in Book 80. Let $p_{\lambda_D}$ be the normalized division type trace (9.1), with the tame rectifier included in its label. There is a prepared split function $p_{\lambda_D}^{G}$ such that

$$
(p_{\lambda_D}^{G},p_{\lambda_D})
$$

satisfies (2.6)--(2.7), and

$$
\operatorname{tr}\sigma(p_{\lambda_D}^{G})
=\operatorname{tr}\sigma_D(p_{\lambda_D})
=\dim\operatorname{Hom}_{J_D}(\lambda_D,\sigma_D)
\tag{9.8}
$$

for every special or selected dihedral pair $(\sigma,\sigma_D)$ in Book 80's range with the central character prescribed by $p_{\lambda_D}$. In particular, the common value is one for $(\pi,\pi_D)$. Its central translates, contragredients, and norm twists satisfy the corresponding identities. The theorem constructs a transfer of the normalized division type trace; it does not assert that an independently chosen split type idempotent has the same orbital integrals.

**Proof.** Average $p_{\lambda_D}$ by conjugation. Equations (8.2) preserve all its orbital integrals and its trace on $\pi_D$. Apply Theorem 8.2 shell by shell and call the resulting split function $p_{\lambda_D}^{G}$. This proves (2.6)--(2.7) on every regular class, including the scalar-reduction annuli.

Book 80 proves $\Theta_\sigma=-\Theta_{\sigma_D}$ for every selected pair on every matching regular elliptic class with the same rectifier, central character, and compact-unit torus measures. Weyl integration now pairs the two orbital signs and gives equality of traces. Schur orthogonality (9.2) identifies the division trace with the displayed type multiplicity, proving (9.8). Book 80's multiplicity-one theorem makes it one for the defining pair. Section 2.4 proves the assertions about translation, inversion, and twisting. $\square$

The geometric construction of Theorem 8.2 applies to a division type function even outside the selected packet range. What is unavailable for ramified dyadic positive-depth and primitive wild packets is the prior character theorem needed for (9.8) and for identification of the split representation. This is the exact boundary inherited from Book 80.

## 10. Singular germs and central terms

### 10.1 What regular matching does not say

As $\gamma$ approaches a scalar $z$, $|D_G(\gamma)|$ tends to zero and $O_\gamma(f)$ may grow. A cross-inner-form identity on the regular set does not turn into a simple equality of the two point values at $z$, nor does it by itself compare the separately weighted global distributions supported at the scalar class. Global trace formulas isolate the central term, so a defensible transfer argument must keep three assertions separate:

1. equality of regular elliptic orbital integrals with sign;
2. compatibility of their singular limits;
3. equality of the separately weighted central distributions.

In characteristic zero no noncentral nonsemisimple class occurs in $D^\times$. In equal characteristic two a quaternion division algebra can contain inseparable quadratic subfields, but their elements are outside the regular semisimple transfer locus and are not nilpotent germs at a scalar. On $G$, by contrast, the repeated-root fiber contains the regular unipotent orbit. Its contribution is the second rank-two germ.

### 10.2 The two rank-two germs

Translate a neighborhood of $z$ to the identity and write a small element as $1+X$. In $\mathfrak{gl}_2$ there are two nilpotent orbits: $\{0\}$ and the regular orbit. Consequently a normalized regular orbital integral has an expansion

$$
I_{z(1+X)}(f)
=\Gamma_0(X)\,f(z)
+\Gamma_{\mathrm{reg}}(X)\,\mu_{\mathrm{reg},z}(f),
\tag{10.1}
$$

on each sufficiently small regular annulus. Here $\Gamma_0$ is the zero-orbit square-root term for the chosen approach type and $\Gamma_{\mathrm{reg}}$ is locally constant after the Weyl normalization. The coefficient $\mu_{\mathrm{reg},z}$ is the regular nilpotent orbital distribution translated to $z$.

On the division algebra the nilpotent cone contains only zero: if $X^2=0$ in a division ring then $X=0$. Thus

$$
I_{z(1+Y)}(f_D)=\Gamma_0^D(Y)f_D(z).
\tag{10.2}
$$

The coefficient functions in (10.1)--(10.2) are fixed by the declared group, torus, and nilpotent-centralizer measures; they must not be independently normalized to one. Equality on matching regular elliptic directions first forces the split regular-nilpotent coefficient to vanish. The remaining zero-germ terms then satisfy the relation already encoded by the regular orbital identity. That relation is not, in general, the point-value identity $f(z)=-f_D(z)$.

The assertion that there are only two split germs can be checked directly. A nilpotent $2\times2$ matrix has characteristic polynomial $X^2$. If it is nonzero, its image and kernel are the same one-dimensional subspace. Choosing a vector outside the kernel and then its image gives a basis in which the matrix is

$$
N=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$

Conjugation by $\operatorname{diag}(c,1)$ rescales the upper-right entry through every element of $F^\times$, so every nonzero nilpotent is $G$-conjugate to $N$. Thus no square-class family of nilpotent germs is present for $\mathrm{GL}_2$; such a family would arise only after replacing $G$ by $\mathrm{SL}_2$.

One can also see the form of (10.1) without a general germ theorem. On a sufficiently small lattice in the Lie algebra, conjugation-invariant locally constant functions are constant on trace-determinant fibers away from the discriminant. Scaling a regular element toward zero leaves only the zero orbit and the single nonzero nilpotent orbit as possible limits. Homogeneity of the transverse Jacobian supplies $\Gamma_0$, while the constant term on each annulus supplies $\Gamma_{\mathrm{reg}}$. This rank-two argument proves that there is no third distribution waiting at the singular boundary.

### 10.3 Cancellation for the Euler function

The fixed-subtree proof already contains the germ cancellation. As an elliptic element approaches a scalar, its fixed subtree acquires longer branches. In $e_{\mathrm{EP}}$, every new terminal vertex is paired with its incident edge. Therefore the alternating sum remains $1$ in the unramified-core case and $1/2$ in the ramified-core case, independent of the depth of approach.

On a split approach, the fixed tube grows around an apartment. Its vertex and edge contributions cancel exactly, leaving zero. This says

$$
\mu_{\mathrm{reg},z}(f_{\mathrm{ell}})=0.
\tag{10.3}
$$

The elliptic normalized orbital integral is

$$
I_\gamma(f_{\mathrm{ell}})
=-f(E/F)\left|\frac{\Delta(\gamma)}{n(\gamma)}\right|^{1/2},
\tag{10.4}
$$

and tends to zero as $\gamma\to z$. The same is true on the division side with the opposite sign. Thus the unit fundamental lemma reaches the singular boundary without an unaccounted regular-nilpotent distribution.

For every finite-level transfer constructed in Theorem 8.2, the same conclusion follows without a second shell calculation. Matching holds on all sufficiently small elliptic regular annuli, while the split orbital integral is identically zero on the split annuli. The normalization-independent germ criterion proved in Book 102 then forces the coefficient of the regular nilpotent germ to vanish. Thus no near-central annulus was lost in passing from the explicit parity kernels to congruence multipliers.

### 10.4 Central distributions

Regular transfer does not assert $f_{\mathrm{ell}}(z)=-f_D^0(z)$. Indeed at $z=1$,

$$
f_{\mathrm{ell}}(1)=-2+(q+1)=q-1,
\qquad f_D^0(1)=1.
\tag{10.5}
$$

This is not a contradiction. In an inner-form trace comparison the central terms are

$$
\operatorname{vol}([G/Z])f(z)
\quad\text{and}\quad
\operatorname{vol}([D^\times/Z])f_D(z),
\tag{10.6}
$$

with global measures and the selected central character. Their equality is a separate volume-and-point-value identity. One must either choose the global normalizations and scalar multiples so that (10.6) agrees, or subtract the central representations on both spectral sides. Altering local torus measures cannot repair (10.5).

The two-germ expansion does **not** permit one to change $f(z)$ while keeping every regular orbital integral fixed. Indeed, if a function has zero regular orbital integrals, first taking the deep normalized limit in (10.1) kills its regular-nilpotent coefficient, and then the nonzero zero-germ coefficient kills its central value. What can be changed is a _matching pair_: one changes the division function near $z$ and transfers that change to the split side, preserving regular matching between the two new functions.

Here is the exact local operation at $z=1$. Let $b_D$ be a conjugation-invariant bump supported in a sufficiently small neighborhood of $1$ inside the reduced-norm unit shell and let $B$ be its invariant extension from Lemma 8.1. Then

$$
b_G=Bf_{\mathrm{ell}},
\qquad b_D
\tag{10.7}
$$

is a matching bump pair. Its point values at the center are

$$
b_G(1)=(q-1)b_D(1),
\tag{10.8}
$$

while its split regular-nilpotent germ is zero. Central translates give the same statement at any scalar. Adding a multiple of (10.7) changes the regular orbital data near the center on both sides but preserves their matching everywhere. Whether a chosen global linear combination also annihilates specified norm-character traces is a separate finite interpolation problem. Its solution and the resulting global volume coefficient must be checked in the global argument; local regular transfer alone supplies neither.

## 11. Character traces and uniqueness

### 11.1 Weyl integration with the two signs

Let $(f,f_D)$ be matching. For a selected discrete-series pair $(\pi,\pi_D)$, Weyl integration decomposes the ordinary operator trace into regular tori. In a fixed-central-character Hecke space this is the identical quotient formula on $H/Z$; for genuinely compact functions it is the formula on $H$. The singular set has Haar measure zero, so no central point value is inserted into this local character integral. The split contribution on $G$ vanishes by (2.6). On an elliptic torus, substitute

$$
O_t(f)=-O_t(f_D),
\qquad
\Theta_\pi(t)=-\Theta_{\pi_D}(t).
$$

The Weyl groups, torus measures, and discriminants agree. Hence the two signs cancel pointwise in the torus integral.

### 11.2 Trace matching

**Theorem 11.1.** Under the preceding hypotheses,

$$
\operatorname{tr}\pi(f)=\operatorname{tr}\pi_D(f_D)
\tag{11.1}
$$

for every selected special or dihedral Jacquet--Langlands pair having the central character of the matching Hecke spaces.

**Proof.** Characters are locally integrable, and Weyl integration is an identity for the Haar integral defining the operator trace. The regular set has full Haar measure. Section 11.1 therefore compares the complete integrals: split tori contribute zero by (2.6), and the two minus signs cancel on every elliptic torus with identical Weyl order, discriminant, and torus measure. This proves (11.1). The germ calculation is needed for the geometric trace-formula boundary, not to add a measure-zero term to the local character integral. $\square$

For the unit pair, (11.1) says that the alternating Iwahori Euler function has trace one on Steinberg, matching the maximal-order unit on its one-dimensional division companion. For dihedral pairs it says that the prepared split transfer of the normalized division type trace selects the corresponding multiplicity line.

### 11.3 Uniqueness modulo orbital null functions

Transfer is not unique as a test function. If $u\in C_c^\infty(G)$ has zero orbital integral on every regular class, then $f+u$ transfers whenever $f$ does. Conversely, any two transfers of the same division function have difference with zero regular orbital integrals, directly from (2.6)--(2.7).

The correct elementary uniqueness statement is therefore uniqueness in the regular-orbital quotient

$$
C_c^\infty(G)\big/
\{u:O_\gamma(u)=0\text{ for all regular }\gamma\}.
\tag{11.2}
$$

We do not call (11.2) the Hecke-algebra cocenter: identifying its kernel with the commutator subspace would require a separate density theorem not used here. The extension construction of Chapter 8 chooses a concrete representative in this quotient. A normalized split type function may choose another representative adapted to spectral traces, but Theorem 9.1 does not assert that the two functions coincide.

## 12. Archimedean transfer

### 12.1 Real elliptic classes

Let $F=\mathbf R$, $G=\mathrm{GL}_2(\mathbf R)$, and $D=\mathbf H$. A regular elliptic class is represented by

$$
rR_\theta,
\qquad
R_\theta=
\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix},
\quad 0<\theta<\pi.
$$

The square-root Weyl factor is $|D_G(rR_\theta)|^{1/2}=2|\sin\theta|$. The matching quaternion has the same trace $2r\cos\theta$ and norm $r^2$. Split regular classes have no quaternionic partner.

### 12.2 Weight-$k$ transfer

For $k\ge2$, let $f_k$ be the normalized cuspidal projector selecting the weight-$k$ discrete series on $G$, and let $f_{D,k}$ be the normalized character projector for the $(k-1)$-dimensional representation of $\mathbf H^\times/\mathbf R_{>0}$. The explicit orbital calculations give

$$
O_{rR_\theta}(f_k)
=-\operatorname{sgn}(r)^k
\frac{\sin((k-1)\theta)}{\sin\theta},
\qquad
O_{ra_t}(f_k)=0,
\tag{12.1}
$$

and

$$
O_\delta(f_{D,k})
=\operatorname{sgn}(r)^k
\frac{\sin((k-1)\theta)}{\sin\theta}.
\tag{12.2}
$$

For completeness, the sine quotient in (12.2) is the character of $\operatorname{Sym}^{k-2}(\mathbf C^2)$: diagonalizing a unit quaternion with eigenvalues $e^{\pm i\theta}$ gives the geometric sum

$$
e^{i(k-2)\theta}+e^{i(k-4)\theta}+\cdots+e^{-i(k-2)\theta}
=\frac{\sin((k-1)\theta)}{\sin\theta}.
$$

The split projector's minus sign is the alternating orientation of the two real root directions. Thus (12.1)--(12.2) prove archimedean transfer with the same convention (2.7).

### 12.3 The singular endpoints

At the two endpoints,

$$
\lim_{\theta\to0}
\frac{\sin((k-1)\theta)}{\sin\theta}=k-1,
\qquad
\lim_{\theta\to\pi}
\frac{\sin((k-1)\theta)}{\sin\theta}=(-1)^k(k-1).
$$

The ordinary orbital integral has a finite elliptic limit, while multiplication by the square-root Weyl factor makes the normalized orbital integral tend to zero. This is compatible with the finite-place pattern (10.4). At $k=1$ there is no discrete-series projector with the asserted properties, so the hypothesis $k\ge2$ is essential.

## 13. Assembly for global comparison

### 13.1 Restricted tensor products

Let $F$ now be a number field and $D$ a quaternion algebra. At almost every finite split place choose the common hyperspecial unit. At a finite division place choose the pair (5.4), or a finite-level pair from Theorem 8.2 or 9.1. At a real division place choose (12.1)--(12.2). At the remaining finitely many places use identical split functions or the regular patching construction. The assembly below is conditional on Book 101's stated two-sided strong-cuspidality hypothesis; in the global route treated there, the distinguished factor is a real discrete-series projector. If no such real factor is present, another input satisfying that hypothesis must be supplied before Book 101's geometric formula can be invoked.

The resulting restricted tensors

$$
f=\bigotimes_v f_v,
\qquad
f_D=\bigotimes_v f_{D,v}
\tag{13.1}
$$

are well-defined because almost every factor is hyperspecial. For a global elliptic class $\gamma\leftrightarrow\delta$, quotient measures factor orbit by orbit, and so do orbital integrals.

### 13.2 Matching geometric terms

At each division place the local sign is $-1$; at each split place it is $+1$. Thus

$$
O_\gamma(f)
=(-1)^{\#\operatorname{Ram}(D)}O_\delta(f_D)
\tag{13.2}
$$

for the regular elliptic global term, with the archimedean ramified places included. A quaternion algebra over a number field is ramified at an even number of places, so the total sign is $+1$. This parity follows from the product formula for local invariants of a quaternion algebra. Hence the elliptic geometric sums agree term by term once the common torus-volume coefficient is identified.

A rational regular class with no quaternionic partner is split at some ramified place; its local orbital integral then vanishes by (2.6). The nonsemisimple and parabolic terms disappear for a different reason: Book 101 groups them by rational stable lines and applies the two-sided zero parabolic transform of the distinguished strongly cuspidal factor. The finite Euler function (5.4) need not itself have zero parabolic transform, and zero split regular orbital integrals alone would not prove the required unipotent cancellation.

The division side has no split classes and no noncentral nilpotent class. Absolute convergence established in Book 101 permits termwise comparison of the elliptic series. The scalar term is not automatic: the global functions must additionally satisfy

$$
\operatorname{vol}([G/Z])f(1)
=\operatorname{vol}([D^\times/Z])f_D(1),
\tag{13.3}
$$

in the chosen global measures, or both sides must be projected away from the corresponding determinant and norm characters. Matching bumps from (10.7) are the local device available for that final interpolation. Without this extra condition, regular transfer proves equality of elliptic terms but not equality of the complete geometric distributions.

### 13.3 The normalization ledger

The entire comparison can be audited in one table.

| datum                  | normalization and consequence                                    |
| ---------------------- | ---------------------------------------------------------------- |
| absolute value         | $\lvert\varpi\rvert=q^{-1}$                                      |
| split group measure    | $\operatorname{vol}(K)=1$                                        |
| division group measure | $\operatorname{vol}(\mathcal O_D^\times)=1$                      |
| quadratic torus        | $\operatorname{vol}(\mathcal O_E^\times)=1$                      |
| quotient measure       | $dh=dt\,d\dot h$                                                 |
| Iwahori                | $\operatorname{vol}(I)=1/(q+1)$                                  |
| geometric edge         | two orientations, producing $1/2$                                |
| odd kernel             | $-(q+1)\mathbf1_{\eta I}$ on determinant valuation one           |
| Weyl factor            | $\lvert D_H(h)\rvert=\lvert\Delta(h)/n(h)\rvert$                 |
| division quotient      | $\operatorname{vol}(E^\times\backslash D^\times)=f(E/F)$         |
| regular orbital sign   | $O_G=-O_D$ at division places                                    |
| character sign         | $\Theta_G=-\Theta_D$ for selected packets                        |
| trace sign             | the two signs cancel                                             |
| parabolic cancellation | supplied globally by Book 101's strongly cuspidal factor         |
| scalar term            | separate condition (13.3), not a consequence of regular transfer |

Rescaling a group or torus measure changes the corresponding row and must be propagated through every orbital integral, formal degree, and global coefficient. The formulas are consistent precisely because no row is changed in isolation.

### 13.4 Failure modes and boundary cases

Several tempting shortcuts are false.

Raw maximal-compact units do not transfer at a division place: their orbital integrals are $1$ versus $f(E/F)$. Regular elliptic matching alone does not kill principal-series traces; split orbital vanishing is necessary. Equality of trace and determinant does not include inseparable quadratic subalgebras in residue characteristic two; regular semisimplicity must be retained. Residue eigenlines do not compute scalar-reduction orbital integrals at positive depth. Equality of one representation trace does not prove orbital transfer, and the normalized type trace differs by a factor of $\dim\lambda$ from the actual type idempotent. Finally, the tame Fourier-index proof identifies selected representation characters but does not cover ramified dyadic wild types.

These are boundaries of the theorem, not missing steps inside it. The even and odd parity kernels and the finite-level orbital transfer hold in every residue characteristic for separable regular classes because their proof uses the tree, invariant quotient, and valuation indices. The selected positive-depth **spectral interpretation** has exactly the tame scope of the prior type construction.

## 14. Final synthesis

Transfer in rank two is governed by one invariant polynomial and one one-dimensional building. Trace and norm identify the common elliptic classes of $\mathrm{GL}_2$ and its quaternionic inner form. Compact-unit torus measures make the quaternionic orbital integral of the maximal-order unit equal to the residue degree $f(E/F)$. The tree then supplies the missing function on the split group.

The decisive identity is the weighted Euler calculation

$$O_\gamma\left(\mathbf1_K-\frac{q+1}{2}\mathbf1_I\right)=

\begin{cases}
0,&\gamma\text{ split regular},\\
f(E/F)/2,&\gamma\text{ elliptic regular}.
\end{cases}
$$

Its proof pairs every noncore vertex with an edge. A split torus leaves an apartment of Euler characteristic zero; an unramified elliptic torus has a vertex core; a ramified elliptic torus has an edge-midpoint core with half weight. Multiplication by $-2$ gives the explicit unit fundamental lemma

$$
-2\mathbf1_K+(q+1)\mathbf1_I
\quad\longleftrightarrow\quad
\mathbf1_{\mathcal O_D^\times}.
$$

The same cellular mechanism gives the Iwahori statement and the odd edge-reversing kernel $-(q+1)\mathbf1_{\eta I}$. Conjugation averaging on the compact projective division group preserves both orbital and representation traces. A locally constant division class function extends from the closed elliptic invariant quotient to trace--norm space; multiplying that extension by the appropriate even or odd kernel gives the selected congruence transfer, including every scalar-reduction annulus. This is the finite-level fundamental lemma.

For spectral interpretation, the unramified special case begins with the alternating Iwahori Euler function. Depth-zero dihedral character identities reduce to the two residue-field embeddings, and positive-depth tame identities reduce to complementary finite Fourier forms whose cyclic-algebra norm classes differ by $-1$. These are genuine prior inputs from Book 80. Combined with the newly constructed orbital transfer, their second minus sign gives trace one on the corresponding prepared split type function.

The singular audit is equally explicit. The split regular-nilpotent germ vanishes by vertex-edge cancellation, and the general finite-level transfer inherits this vanishing from the two-germ criterion. Normalized elliptic integrals tend to zero, while central point values remain a separate distribution with their actual global quotient volumes. A matching bump may alter both local functions near the center, but no function with all regular orbital integrals zero can independently change its central value. At the real place the sine quotient supplies the same transfer sign.

Globally, local ramification signs occur an even number of times and elliptic terms match orbit by orbit. Book 101's distinguished strongly cuspidal factor, not the finite Euler function alone, removes the unmatched parabolic and nonsemisimple geometry. Equality of complete geometric distributions additionally requires the scalar identity (13.3) or projection away from determinant and norm characters.

We have therefore constructed, rather than postulated, the matching functions required for rank-two global comparison: hyperspecial units at split places, the Euler--Iwahori even unit at division places, the odd edge-reversing kernel, spherical functions at split places, selected congruence and prepared type transfers, and the real discrete-series projectors. Their Haar normalizations, regular orbital terms, singular germs, central qualifications, and transfer signs now form one closed local-to-global package, with the global scalar condition stated rather than silently assumed.
