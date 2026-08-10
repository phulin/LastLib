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
  - [4.4 The explicit elliptic projector](#44-the-explicit-elliptic-projector)
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
  - [8.1 Segments and depth](#81-segments-and-depth)
  - [8.2 A triangular finite-count argument](#82-a-triangular-finite-count-argument)
  - [8.3 The selected level theorem](#83-the-selected-level-theorem)
  - [8.4 The scalar-reduction boundary](#84-the-scalar-reduction-boundary)
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

An inner-form comparison begins with two groups which have different points but share part of their conjugacy geometry.  Let $F$ be a local field, let

$$
G=\mathrm{GL}_2(F),
$$

and let $D$ be a quaternion algebra over $F$.  When $D$ is split, $D^\times$ is another copy of $G$.  When $D$ is division, every noncentral regular semisimple element of $D^\times$ generates a quadratic field, whereas $G$ also has split regular classes.  Trace and determinant on $G$, and reduced trace and reduced norm on $D^\times$, identify the quadratic-field classes on the two sides.

The geometric terms of a trace formula are orbital integrals, not point values.  Consequently an identification of characteristic polynomials is only the beginning.  One must construct functions whose averages along corresponding orbits agree with the correct sign and whose split orbital integrals disappear.  At a singular class the centralizer jumps, so regular matching must also be checked against the limiting germ and against the separate central distribution.

The preceding books supplied the three inputs needed here.  The geometric trace formula isolated the central and elliptic distributions and proved their convergence.  The orbital-integral calculations fixed the measures and reduced the finite-place integrals to lattice, chain, and congruence counts.  The selected local Jacquet--Langlands correspondence proved that matching discrete-series characters differ by $-1$ on regular elliptic classes.  We now turn those calculations into actual transfer functions.  The proof is rank-two throughout: the building is a tree, the invariant quotient has two coordinates, and the only nonzero nilpotent orbit is the regular one.

### 1.2 Standing local conventions

Until Chapter 12, $F$ is nonarchimedean with ring of integers $\mathcal O$, maximal ideal $\mathfrak p=(\varpi)$, residue field $k$, and $|k|=q$.  We normalize

$$
v(\varpi)=1,\qquad |x|=q^{-v(x)}.
$$

Put

$$
K=\mathrm{GL}_2(\mathcal O),\qquad
I=\left\{g\in K:g\bmod\mathfrak p\text{ is upper triangular}\right\}.
$$

Thus $[K:I]=q+1$.  Haar measures satisfy

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

All quotient measures are defined by $dh=dt\,d\dot h$.  These compact-unit choices, rather than an unnamed canonical measure, are responsible for the residue-degree factor that appears below.

Test functions are complex-valued, locally constant, and compactly supported.  If a central character is imposed, the equivalent compact-mod-center formulation is obtained by the usual central averaging; every formula below then lies in a fixed determinant or reduced-norm shell.  We state the compactly supported form because it keeps point values and volumes visible.

### 1.3 What will be proved

There are four principal results.

First, transfer exists locally on the regular set by an explicit slice construction, not by appeal to a general transfer theorem.  Second, at a division place the function

$$
f_{\mathrm{ell}}
=-2\mathbf1_K+(q+1)\mathbf1_I
\tag{1.4}
$$

has zero split regular orbital integrals and has orbital integral $-f(E/F)$ on an integral elliptic unit class with centralizer $E^\times$.  Since $\mathbf1_{\mathcal O_D^\times}$ has division-side orbital integral $f(E/F)$, equation (1.4) is the unit fundamental lemma in the present normalization.

Third, the same tree calculation identifies the unique alternating line in the Iwahori algebra and extends, by finite segment and congruence Fourier sums, to the selected $K_0$, $K_1$, special, and tame dihedral functions required in global comparison.  Fourth, regular, singular, and central contributions are kept separate: the regular transfer sign is $-1$, the normalized singular germ is compatible, and central terms are compared with their actual quotient-volume coefficients.

The restriction to selected positive-depth functions is substantive.  Ramified dyadic wild types carry data not captured by the tame finite Fourier comparison.  No assertion about them will be smuggled into the theorem.

## 2. Matching classes and measures

### 2.1 The invariant quotient

For $\gamma\in G$, set

$$
t(\gamma)=\operatorname{tr}(\gamma),\qquad
n(\gamma)=\det(\gamma),\qquad
\Delta(\gamma)=t(\gamma)^2-4n(\gamma).
$$

For $\delta\in D^\times$ use reduced trace and reduced norm in the same formulas.  A regular semisimple element has $\Delta\ne0$, and its centralizer is the unit group of the quadratic étale algebra

$$
E=F[X]/(X^2-tX+n).
\tag{2.1}
$$

Two regular elements on the same side are conjugate if and only if $(t,n)$ agree.  Indeed, on the split side the element makes $F^2$ a free rank-one module over (2.1); on the quaternionic side conjugacy of embeddings of a quadratic field follows by the elementary intertwiner argument in a central simple algebra of degree two.  Thus the map

$$
\chi:H_{\mathrm{reg}}\longrightarrow F\times F^\times,
\qquad h\longmapsto(t(h),n(h))
\tag{2.2}
$$

is the regular conjugacy quotient for either inner form.

We say $\gamma$ and $\delta$ **match** if their images under (2.2) agree.  If $D$ is division, its image consists of the elliptic points of the quotient: those for which (2.1) is a field.  There is no quaternionic class above a split point.  This typing condition is the reason a transfer on $G$ must vanish on split regular orbits.

### 2.2 Haar and quotient measures

For $H=G$ or $D^\times$ and regular $h$, let $T=H_h=E^\times$.  Define

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

The equality follows after diagonalizing $h$ with eigenvalues $a,b$: the two root eigenvalues of $\operatorname{Ad}(h)$ are $a/b$ and $b/a$, whose product after subtracting from one is $-(a-b)^2/(ab)$.  Both inner forms give the same expression after scalar extension.  Hence matching elements have the same Weyl factor.

We also use

$$
I_h(f)=|D_H(h)|^{1/2}O_h(f).
\tag{2.5}
$$

If $dh$ is multiplied by $a$ and $dt$ by $b$, then every orbital integral is multiplied by $a/b$.  Formula (2.4) does not change.  This simple scaling rule will check every claimed identity.

### 2.3 Transfer and its sign

Let $f\in C_c^\infty(G)$ and $f_D\in C_c^\infty(D^\times)$, with $D$ division.  We call $(f,f_D)$ a **matching pair** if

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

Because of (2.4), the same definition results if $O$ is replaced everywhere by $I$.  Our sign convention places the inner-form sign on orbital transfer.  Book 85's selected character identity places another sign on characters:

$$
\Theta_\pi(\gamma)=-\Theta_{\pi_D}(\delta).
\tag{2.8}
$$

The two minus signs cancel in Weyl integration, giving equal operator traces.  One may instead define signless orbital transfer and insert a minus in the spectral comparison, but mixing the conventions halfway through produces the wrong trace identity.

When $D\simeq M_2(F)$, matching means ordinary conjugacy matching and the transfer sign is $+1$.  Under a fixed isomorphism the simplest transfer is $f_D=f$.  The sign $-1$ is the Kottwitz sign of the nonsplit inner form in rank two.

### 2.4 Central scaling and involutions

For $z\in F^\times$, put $f^z(h)=f(z^{-1}h)$.  Since $z$ is central,

$$
O_{zh}(f^z)=O_h(f).
\tag{2.9}
$$

Moreover, $\det(z\gamma)=z^2\det\gamma$ and $\operatorname{Nrd}(z\delta)=z^2\operatorname{Nrd}\delta$, so central translation preserves matching.  Thus every unit-shell lemma immediately yields all even valuation translates.

Inversion also preserves matching.  If $f^\vee(h)=f(h^{-1})$, then unimodularity and the change $x\mapsto x^{-1}$ give

$$
O_{h^{-1}}(f^\vee)=O_h(f).
\tag{2.10}
$$

Finally, twisting by a character $\mu:F^\times\to\mathbf C^\times$ through determinant and reduced norm preserves (2.7), because matching elements have equal norm.  These three operations account for the central translates and nonminimal twists used later.

## 3. Local descent on the regular set

### 3.1 Why existence is not automatic

An orbital integral is constrained by conjugation invariance, support, and a Jacobian.  It is therefore not enough to prescribe arbitrary values at representatives.  Near a regular orbit, however, conjugation has a transverse slice, and in degree two that slice can be written down.  This gives a local right inverse to the orbital-integral map and explains exactly where singular germs enter.

The construction is useful even though the fundamental functions below are explicit.  It proves that transfer is not restricted to those examples, lets us patch auxiliary functions at finitely many places, and identifies uniqueness as uniqueness only modulo functions with zero regular orbital integrals.

### 3.2 A rank-two slice

Fix a regular $h_0\in H$, let $T=H_{h_0}$, and choose an $F$-linear complement $\mathfrak q$ to $\mathfrak t$ in $\mathfrak h$.  For sufficiently small compact-open neighborhoods $U\subset\mathfrak q$ and $V\subset T$, consider

$$
\Phi:T\backslash H\times V\longrightarrow H,
\qquad (\dot x,t)\longmapsto x^{-1}tx.
\tag{3.1}
$$

At $(1,h_0)$ its differential sends $(X,Y)$ to

$$
(1-\operatorname{Ad}(h_0^{-1}))X+Y.
$$

The first summand is invertible on $\mathfrak q$ precisely because $h_0$ is regular, while the second spans $\mathfrak t$.  Hence the differential is invertible.  The nonarchimedean inverse function theorem, proved by successive approximation in coordinates, gives neighborhoods on which (3.1) is a homeomorphism and analytic diffeomorphism onto its image.

Its Jacobian in the orbit direction is $|D_H(t)|$ up to the constant imposed by our fixed coordinate measures.  Shrinking $V$, absorb the constant into a test function on $U$.  This is the concrete rank-two form of semisimple descent.

### 3.3 Prescribing an orbital integral locally

Let $a(t)$ be a locally constant compactly supported function on $V$.  Choose $b\in C_c^\infty(U)$ with integral one relative to the quotient coordinate.  On the image of (3.1) define

$$
f(x^{-1}tx)=a(t)b(\dot x)J(t)^{-1},
\tag{3.2}
$$

where $J(t)$ is the quotient Jacobian; extend by zero.  If the neighborhoods are chosen so that no other conjugate of $V$ enters the image, substitution in (2.3) gives

$$
O_t(f)=a(t).
\tag{3.3}
$$

If the Weyl involution identifies two points of $V$, average (3.2) over it.  Then (3.3) holds for the invariant function $a$.

This proof contains the decisive facts: regularity makes the transverse determinant nonzero, compact support permits extension by zero, and the unit integral of $b$ fixes the constant.  There is no appeal to an unspecified theorem about all reductive groups.

### 3.4 Patching on compact regular sets

Let $C$ be a compact subset of the regular invariant quotient.  Cover it by finitely many slice neighborhoods $V_i$.  Because the topology is totally disconnected, refine to a disjoint compact-open partition $C=\bigsqcup C_i$ with $C_i\subset V_i$.  Apply (3.2) to the restriction of the desired invariant function on each $C_i$ and add the results.  We obtain:

**Proposition 3.1 (regular patching).**  Every locally constant compactly supported function on a compact subset of the regular quotient is the orbital-integral function of a compactly supported test function.  On $G$, prescriptions on disjoint split and elliptic compact subsets can be realized independently.

The proof also applies over $\mathbf R$ with smooth partitions of unity, provided one works away from $\Delta=0$.  It does not solve the singular boundary.  If $C$ accumulates at $\Delta=0$, the Jacobian in (3.2) degenerates and a prescribed function must satisfy the germ relations of Chapter 10.  The explicit fundamental functions do satisfy them.

## 4. The tree and the elliptic Euler function

### 4.1 Vertices, edges, and stabilizers

The Bruhat--Tits tree $X$ of $\mathrm{PGL}_2(F)$ has vertices the homothety classes $[L]$ of rank-two $\mathcal O$-lattices.  Two vertices are adjacent when representatives can be chosen with

$$
\varpi L\subsetneq L'\subsetneq L.
$$

The neighbors of $[L]$ are the lines in $L/\varpi L$, so every vertex has degree $q+1$.  The stabilizer of the standard vertex is $F^\times K$; the stabilizer of the oriented standard edge is $F^\times I$.

For an element $\gamma$ with unit determinant, $x^{-1}\gamma x\in K$ exactly when $\gamma$ fixes the vertex $x[\mathcal O^2]$.  Likewise, membership in $I$ means that $\gamma$ fixes the associated oriented edge.  Passing from $x$ to the left by the centralizer identifies cells in the same $T$-orbit.  Thus orbital integrals of $\mathbf1_K$ and $\mathbf1_I$ are weighted counts of fixed vertices and oriented edges.

The word “weighted” matters.  A cell represented by $x$ contributes the volume of its right stabilizer divided by the volume of $T\cap xKx^{-1}$ or $T\cap xIx^{-1}$.  These are exactly the reciprocal stabilizer factors in the lattice formulas of Book 111.

### 4.2 Orbital integrals as weighted fixed-cell counts

Let $X^\gamma$ be the fixed subtree.  Write $V(X^\gamma)$ and $E^{\mathrm{or}}(X^\gamma)$ for its vertices and oriented edges.  With compact-unit measure on $T$, double-coset decomposition gives

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

Here $T_v$ and $T_e$ mean the compact stabilizers after the common scalar direction is removed.  Formula (4.2) contains the factor $q+1$ because $\operatorname{vol}(I)=(q+1)^{-1}$.  Each geometric edge has two orientations with the same stabilizer.  Therefore

$$
O_\gamma\left(\mathbf1_K-\frac{q+1}{2}\mathbf1_I\right)
=\chi_T(X^\gamma),
\tag{4.3}
$$

where the right side is the weighted number of vertex orbits minus the weighted number of geometric-edge orbits.

This is an identity of finite sums for elliptic $\gamma$.  For split $\gamma$, truncate the fixed tube to distance $N$ from a base vertex, form the alternating sum, and then pass to the quotient by $T$.  Boundary vertices and edges pair, so the stable value is again (4.3).  No convergence is hidden in the notation.

### 4.3 The fixed-subtree Euler calculation

Put

$$
e_{\mathrm{EP}}=\mathbf1_K-\frac{q+1}{2}\mathbf1_I.
\tag{4.4}
$$

**Lemma 4.1 (rank-two fixed-subtree lemma).**  Let $\gamma\in G$ be regular with integral trace and unit determinant, and let $T=F[\gamma]^\times$.

1. If $T$ is split, then $O_\gamma(e_{\mathrm{EP}})=0$.
2. If $T=E^\times$ is elliptic, then

$$
O_\gamma(e_{\mathrm{EP}})=\frac{f(E/F)}2.
\tag{4.5}
$$

**Proof strategy.**  Prune finite branches from the fixed subtree.  Removing a terminal vertex together with its incident edge changes neither the weighted Euler sum nor the stabilizer ratio.  What remains is the minimal subtree of the torus.

**Proof.**  In the split case the torus preserves an apartment.  The quotient of that apartment by the valuation lattice is a circle in the weighted cell complex, hence has Euler characteristic zero.  Every extra fixed branch is finite modulo $T$ and can be pruned in vertex-edge pairs.  This proves the first assertion, including elements close to the center whose fixed set is a thick tube.

Suppose $E/F$ is unramified.  Its unit group fixes one distinguished vertex and no edge issuing from it is fixed by a residue-regular generator.  A generator of a smaller order fixes a larger finite subtree, but pruning returns to the distinguished vertex.  The valuation image of $E^\times$ in $\mathbf Z=v(\det G)$ is $2\mathbf Z$, so there are two determinant-parity positions in the full centralizer quotient; our unit determinant shell retains one weighted vertex.  Hence the value is $1=f(E/F)/2$.

Suppose $E/F$ is ramified.  The minimal $E^\times$-invariant set is the midpoint of an edge.  An $E$-uniformizer exchanges its endpoints.  In the quotient this geometric edge has one vertex orbit with stabilizer index two relative to the edge stabilizer; its weighted Euler value is $1/2$.  Again all additional fixed branches prune.  Since $f(E/F)=1$, this is (4.5).  The argument uses only the valuation image and the tree, so it remains valid for separable ramified quadratic extensions in residue characteristic two.  $\square$

The factor $1/2$ is not arbitrary.  It records the edge inversion by a ramified torus.  Omitting it is the common source of a false claim that one scalar multiple of $\mathbf1_K$ transfers to the quaternionic unit in both ramification types.

Three concrete fixed sets make the calculation visible.  Suppose first that $E/F$ is unramified and that $\gamma\in\mathcal O_E^\times$ has irreducible reduction.  The lattice $\mathcal O_E$, viewed as a rank-two $\mathcal O$-lattice, is the unique fixed vertex modulo $E^\times$.  No line in $\mathcal O_E/\mathfrak p\mathcal O_E\simeq k_{q^2}$ is stable under multiplication by $\bar\gamma$, because such a line would be a one-dimensional $k$-eigenspace and would split the irreducible characteristic polynomial.  Thus

$$
O_\gamma(\mathbf1_K)=1,
\qquad O_\gamma(\mathbf1_I)=0,
$$

and (4.5) is immediate.

For a ramified example with odd residue characteristic, write $E=F(\tau)$ with $\tau^2=u\varpi$ and take $\gamma=a+b\tau$ with $a,b\in\mathcal O^\times$.  The minimal $E^\times$-invariant set is an edge whose two endpoint lattices differ by the action of a ramified uniformizer.  That uniformizer exchanges the endpoint homothety classes.  Hence the two vertex contributions form one orbit, while the edge is fixed as an unoriented cell.  The stabilizer index is two, leaving Euler weight $1/2$.  In residue characteristic two the square-root model may fail, but a valuation-one element of a separable ramified quadratic field acts on the same edge core, so the argument is unchanged.

Finally take $\gamma=\operatorname{diag}(a,b)$ with $a,b\in\mathcal O^\times$.  Its torus fixes the standard apartment.  If $v(a-b)=c$, the element itself fixes a tube of radius governed by $c$, but the diagonal torus translates along the apartment.  A finite quotient of a length-$N$ portion has equally many new vertices and new edges at both ends.  Letting $N$ grow leaves Euler value zero.  This explains why checking only distinct reduction eigenvalues would prove too little: the same cancellation must persist when $a\equiv b\pmod{\mathfrak p^c}$ for arbitrarily large $c$.

### 4.4 The explicit elliptic projector

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

provided $\gamma$ has integral trace and unit determinant.  If these support conditions fail, both terms in (4.6) vanish.  Notice that (4.7) holds for nonmaximal orders as well as maximal ones: the extra fixed branches cancel in the Euler sum.  This uniform cancellation is the fundamental lemma's content.

## 5. The unit fundamental lemma

### 5.1 Split inner forms

If $D\simeq M_2(F)$ and the chosen maximal order corresponds to $M_2(\mathcal O)$, the unit functions are literally identified:

$$
\mathbf1_{\mathcal O_D^\times}\longleftrightarrow\mathbf1_K.
\tag{5.1}
$$

Matching classes are the same classes, group and torus measures agree, and conjugation integrals are equal term by term.  This is the hyperspecial unit lemma at an unramified split place.  It includes split and elliptic regular classes and needs no sign.

### 5.2 A ramified quaternion place

Now suppose $D$ is division.  Conjugation preserves its unique maximal order, so $\mathbf1_{\mathcal O_D^\times}$ is invariant.  If $\delta$ is regular with $E=F[\delta]$, then

$$
O_\delta(\mathbf1_{\mathcal O_D^\times})
=\mathbf1_{\mathcal O_D^\times}(\delta)
\operatorname{vol}(E^\times\backslash D^\times).
\tag{5.2}
$$

The valuation $v_D=v\circ\operatorname{Nrd}$ maps $D^\times/\mathcal O_D^\times$ to $\mathbf Z$.  On $E^\times$ its image is $f(E/F)\mathbf Z$, since

$$
v_D(e)=v(N_{E/F}e)=f(E/F)v_E(e).
$$

Compact unit groups have volume one.  A fundamental domain therefore has $f(E/F)$ valuation cosets, each of volume one, and

$$
O_\delta(\mathbf1_{\mathcal O_D^\times})
=f(E/F)\mathbf1_{\mathcal O_D^\times}(\delta).
\tag{5.3}
$$

### 5.3 Proof of the unit identity

**Theorem 5.1 (unit fundamental lemma for the division inner form).**  With measures (1.1)--(1.3), the pair

$$
\boxed{
f_{\mathrm{ell}}=-2\mathbf1_K+(q+1)\mathbf1_I,
\qquad
f_D^0=\mathbf1_{\mathcal O_D^\times}}
\tag{5.4}
$$

is matching in the sense of (2.6)--(2.7).

**Proof.**  A class meeting either support has integral trace and unit norm.  On a split regular class, (4.7) gives $O_\gamma(f_{\mathrm{ell}})=0$.  Let $\gamma\leftrightarrow\delta$ be elliptic with centralizer $E^\times$.  Membership in $K$ or $\mathcal O_D^\times$ is equivalent to integrality together with unit norm, because trace and norm are shared.  If that condition fails, both orbital integrals vanish.  If it holds, (4.7) and (5.3) give

$$
O_\gamma(f_{\mathrm{ell}})=-f(E/F)
=-O_\delta(f_D^0).
$$

This proves every regular class, including ramified, unramified, nonmaximal-order, and scalar-reduction cases.  $\square$

The proof is a fundamental lemma rather than a definition: both functions in (5.4) are explicit before the class is chosen, and the fixed-subtree calculation proves the equality uniformly over infinitely many orbits.

### 5.4 Why the raw units do not match

For a maximal elliptic order, Book 111 computed

$$
O_\gamma(\mathbf1_K)=1,
$$

whereas (5.3) is $2$ for unramified $E$ and $1$ for ramified $E$.  No constant $c$ can make $c\mathbf1_K$ match the division unit on both kinds of tori.  The Iwahori term in (5.4) is exactly what distinguishes the vertex fixed by an unramified torus from the edge midpoint fixed by a ramified torus.

This also explains why measure normalization cannot be treated as cosmetic.  Rescaling the $E^\times$ measure separately for ramified and unramified $E$ could hide the discrepancy, but those measures would not be a single compatible family and would break the global product formula.  The correct response is to change the split test function, not the ledger.

## 6. The Iwahori fundamental lemma

### 6.1 The two Iwahori cells

Let

$$
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

The two double cosets inside the vertex stabilizer $K$ are $I$ and $IwI$.  Their volumes are

$$
\operatorname{vol}(I)=\frac1{q+1},
\qquad
\operatorname{vol}(IwI)=\frac q{q+1}.
\tag{6.1}
$$

The first fixes an oriented edge; the second moves it across its initial vertex.  Put

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

The two characters of this finite two-cell algebra are the trivial and sign characters.  Only the sign direction is discrete; the trivial direction belongs to the parabolically induced constituent.  We do not claim that these two cells exhaust the full affine Iwahori algebra.

### 6.2 The alternating Iwahori line

The function $e_{\mathrm{EP}}$ of (4.4) can be viewed as the alternating cellular trace of the tree: vertices contribute positively and unoriented edges negatively.  Because an unoriented edge has two orientations, its coefficient is $(q+1)/2$.  This alternating line is independent of the chosen standard edge up to conjugacy.

For split regular $\gamma$ with distinct reduction eigenvalues, Book 111's direct count gives

$$
O_\gamma(\mathbf1_K)=1,
\qquad
O_\gamma(\mathbf1_I)=\frac2{q+1},
$$

so $O_\gamma(e_{\mathrm{EP}})=0$.  The tree proof extends this cancellation to arbitrary split depth, where residue-line counting alone is insufficient.  For unramified elliptic regular reduction, the Iwahori integral is zero and the vertex integral is one.  For ramified or scalar reduction, many stable edges occur, but pruning gives the half-weight in (4.5).

### 6.3 The Iwahori theorem

**Theorem 6.1 (Iwahori fundamental lemma).**

1. At a split inner-form place, every function in the Iwahori algebra transfers to the identical function under a compatible identification $D^\times\simeq G$.
2. At a division place, the discrete quotient of the two-cell Iwahori test space inside $K$ is one-dimensional for the selected transfer.  Its alternating generator $e_{\mathrm{EP}}$ has

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

**Proof.**  The split assertion is termwise equality.  At a division place, the trivial two-cell character is detected by split principal-series orbital data and cannot have a division counterpart.  Quotienting it out leaves the alternating cellular line.  Equations (4.5) and (5.3) give (6.4).  Within the vertex-edge space, the values on a regular-reduction split class and an unramified elliptic class are independent; hence the two residue counts determine both coefficients and leave precisely the displayed line.  The fixed-tube argument extends its vanishing from regular reduction to all split depths.  $\square$

### 6.4 Convolution and normalization checks

Three checks prevent normalization errors.  First, replacing $\mathbf1_I$ by the probability idempotent $(q+1)\mathbf1_I$ changes the displayed coefficient in (4.4).  Second, using oriented rather than geometric edges omits the factor $1/2$.  Third, the transfer statement concerns orbital integrals, not equality in the two Hecke algebras: $D^\times$ has no building edge at a division place.

Convolution by a central translate commutes with $e_{\mathrm{EP}}$.  Twisting by an unramified character multiplies a fixed determinant shell by a constant on both sides.  Hence Theorem 6.1 supplies the unramified twists of the special packet without a new count.

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

The support condition is $v(\det\gamma)=2r$ together with integrality of $\varpi^{-r}\operatorname{tr}\gamma$.  On the division side use $\mathbf1_{\varpi^r\mathcal O_D^\times}$.  Equation (2.9) transports the unit lemma to these shells:

$$
-2\mathbf1_{\varpi^rK}+(q+1)\mathbf1_{\varpi^rI}
\quad\longleftrightarrow\quad
\mathbf1_{\varpi^r\mathcal O_D^\times}.
\tag{7.2}
$$

Odd reduced-norm valuation shells on $D^\times$ cannot be reached by a scalar translate.  They are treated by invariant congruence shells or type functions, not by pretending that a square root of $\varpi$ is central.

### 7.2 The split-place spherical lemma

At a place where the quaternion algebra splits, put

$$
h_m=\mathbf1_{K\operatorname{diag}(\varpi^m,1)K},\qquad m\ge0.
$$

Under a maximal-order-preserving isomorphism, $h_m$ is the same function on both inner forms.  Therefore

$$
O_\gamma(h_m)=O_\delta(h_m)
\tag{7.3}
$$

for matching classes.  This is the spherical fundamental lemma in rank two.  Its proof is not Satake theory: the two orbital integrals have identical domains, integrands, and quotient measures.  Satake theory becomes useful for convolution and eigenvalues after the geometric identity is fixed.

### 7.3 Central translation at a division place

For a conjugation-invariant compact-open subset $C\subset D^\times$, Book 111's valuation decomposition gives

$$
O_\delta(\mathbf1_C)=f(E/F)\mathbf1_C(\delta).
\tag{7.4}
$$

The regular patching proposition constructs a split-side transfer on every compact subset away from the center.  For the invariant shells used here one can do better: express the support conditions through $v(n)$ and congruences in $(t,n)$, decompose them into finitely many tree-depth strata, and take the corresponding alternating vertex-edge sums.  Pruning again leaves $f(E/F)/2$, while the congruence indicator is constant on the fixed core.  Multiplication by $-2$ gives (7.4) with the transfer sign.

Thus the unit lemma is not isolated.  It is the depth-zero member of a family of invariant shell identities.  The selected higher-depth members are made explicit in Chapters 8 and 9.

### 7.4 The first Hecke shell

The condition $x^{-1}\gamma x\in K\operatorname{diag}(\varpi,1)K$ says that for $L=x\mathcal O^2$,

$$
\gamma L\subset L,
\qquad L/\gamma L\simeq\mathcal O/\mathfrak p.
\tag{7.5}
$$

Hence its orbital integral is the weighted number of stable vertices together with a selected line in $L/\varpi L$.  If the reduction has two distinct eigenvalues, two lines contribute; if its characteristic polynomial is irreducible, none does.  This direct finite count agrees on two split copies of $G$ and supplies the first nontrivial check of (7.3).

At a division place an element of odd reduced-norm valuation lies in a ramified quadratic torus.  Its valuation quotient has one class.  The corresponding split function is obtained from oriented-edge displacement one, with the alternating endpoint correction.  Pairing all noncore branches leaves one core edge with weight $-1$, exactly the negative of the division integral.  This is the odd-shell analogue of Lemma 4.1.

## 8. Selected congruence levels

### 8.1 Segments and depth

The subgroup $K_0(\mathfrak p^n)$ stabilizes a length-$n$ segment of the tree.  Its index and volume are

$$
[K:K_0(\mathfrak p^n)]=q^{n-1}(q+1),
\qquad
\operatorname{vol}(K_0(\mathfrak p^n))
=\frac1{q^{n-1}(q+1)}.
\tag{8.1}
$$

The subgroup $K_1(\mathfrak p^n)$ remembers a generator at the terminal quotient, and

$$
[K:K_1(\mathfrak p^n)]=q^{2n}-q^{2n-2}.
\tag{8.2}
$$

Thus $K_0$-orbital integrals count stable segments with reciprocal stabilizer weights, while $K_1$-integrals refine the count by fixed primitive generators.  These descriptions remain correct when the reduction is scalar, where a naive eigenline count fails.

### 8.2 A triangular finite-count argument

Fix a determinant shell and a depth bound $n$.  For a regular integral class define its **fixed depth** $c$ to be the largest radius of a tube around its minimal torus subtree fixed pointwise by the order $\mathcal O[\gamma]$.  Only $0\le c\le n$ can be distinguished by length-$n$ segment functions.

Let $S_j$ be the normalized characteristic function of the stabilizer of a length-$j$ segment, with $S_0=\mathbf1_K$.  Let $N_{cj}$ be its weighted orbital integral on a class of fixed depth $c$.  A segment of length $j$ can lie in the fixed tube only when $j\le 2c+\epsilon$, where $\epsilon$ records whether the torus core is a vertex or an edge midpoint.  At the maximal allowable $j$, the core segment occurs with nonzero stabilizer weight.  Ordering rows by $c$ and columns by $j$ therefore makes the matrix $(N_{cj})$ triangular with nonzero diagonal after separating the vertex-core and edge-core parities.

This elementary observation proves that every prescribed function of the finitely many depth strata can be realized by a unique linear combination

$$
F=\sum_{j=0}^n a_jS_j
\tag{8.3}
$$

modulo combinations whose regular orbital integrals vanish.  The coefficients are obtained recursively from deepest stratum to shallowest.  They belong to $\mathbf Q(q)$ because every entry is a product of subgroup indices and finite stabilizer indices.

The argument is a proof, not a dimension guess.  The support implication gives triangularity, and the unique core segment gives a nonzero diagonal.  At residue characteristic two one retains the two core types instead of labeling them by a discriminant square class.

It is helpful to see the first recursion steps.  At depth zero, $S_0=\mathbf1_K$ records fixed vertices.  At depth one, normalized $S_1$ records fixed oriented edges.  On a regular-reduction split class the row is proportional to

$$
(N_{00},N_{01})=(1,2),
$$

when $S_1$ is normalized to count oriented edges rather than to have subgroup volume $1/(q+1)$.  On an unramified elliptic class it is $(1,0)$.  Solving for a function which is zero on the split row and one on the elliptic row gives the vertex-minus-half-edge combination.  Restoring subgroup volumes produces $e_{\mathrm{EP}}$.

At depth two, a scalar-reduction class may fix several length-two segments.  Subtract first the multiple of $S_2$ prescribed by the deepest core segment.  The remainder has no depth-two contribution and is a linear combination of the already solved depth-zero and depth-one rows.  Inductively, at stage $j$ one removes the unique core length-$j$ segment and falls back to stages $<j$.  This is ordinary backward substitution, and it shows both existence and uniqueness of the coefficients without requiring a closed but fragile formula for every stabilizer index.

The $K_1$ refinement adds a finite Fourier transform rather than a new geometric obstruction.  Over each stable $K_0$ segment, primitive terminal generators form a torsor under $(\mathcal O/\mathfrak p^n)^\times$.  Projecting to a character $\eta$ uses

$$
e_\eta=\frac1{|(\mathcal O/\mathfrak p^n)^\times|}
\sum_u\eta(u)^{-1}[u].
\tag{8.3a}
$$

Orthogonality makes the sum zero unless the torus action on the terminal generator has character $\eta$.  When it survives, the denominator cancels the size of the free unit orbit.  Thus the same triangular segment matrix remains, with each nonzero entry multiplied by an explicitly finite character sum.  This is why the selected $K_1$ functions, not only the $K_0$ characteristic functions, are covered by the theorem.

### 8.3 The selected level theorem

On $D^\times$, let $U_D^m=1+\mathfrak P_D^m$.  A selected invariant level function is constant on reduced valuation and on finitely many reduced trace-norm congruence strata modulo $\mathfrak p^n$.  Such a function has orbital integral

$$
f(E/F)\,f_D(\delta)
\tag{8.4}
$$

when it is conjugation invariant; a type matrix coefficient is treated in Chapter 9.

**Theorem 8.1 (selected congruence fundamental lemma).**  For every selected invariant division function of depth at most $n$, there is an explicitly recursive combination of the segment functions $S_0,\ldots,S_n$ and their determinant-shell translates whose split regular orbital integrals vanish and whose elliptic orbital integrals are the negatives of (8.4).  The coefficients are determined by the triangular system of Section 8.2.  The construction commutes with central translation, inversion, and norm twisting.

**Proof.**  Partition the support by reduced valuation, trace-norm congruence, core parity, and fixed depth.  There are finitely many pieces.  On each piece, (8.4) is a prescribed constant times $f(E/F)$.  Apply the inverse triangular system separately to vertex-core and edge-core strata.  Subtract the cellular Euler combination on every split tube; its endpoint and edge contributions pair, so the split orbital integral is zero.  On an elliptic fixed subtree, pruning reduces the combination to the core, where the recursive coefficient was chosen to be $-f(E/F)f_D(\delta)$.  Disjointness of the invariant pieces lets us sum.  $\square$

This theorem is “selected” because the support is described by the finite trace-norm and segment data actually used by the global test functions.  It does not claim that every wild noninvariant coset is captured by those invariants.

### 8.4 The scalar-reduction boundary

When $\bar\gamma$ is scalar, every residue line is invariant, but lifts to deeper stable segments depend on the order $\mathcal O[\gamma]$.  The number of lifts grows with fixed depth, and stabilizers shrink.  Replacing the exact count by $q+1$ therefore gives a wrong higher-level formula.

The triangular construction avoids the error.  Scalar reduction simply moves the class to a deeper row of $(N_{cj})$.  The recursive subtraction removes contributions already accounted for at greater depth.  Near the actual scalar locus the number of rows grows, but a fixed test function has bounded level, so only finitely many rows are visible.  The remaining limiting behavior is the germ calculation of Chapter 10.

## 9. Special and dihedral type functions

### 9.1 Type idempotents and matrix coefficients

Let $J\subset G$ be compact modulo center and let $\lambda$ be a finite-dimensional smooth representation of $J$.  On a fixed central-character space, its normalized type idempotent is

$$
e_\lambda(j)=\frac{\dim\lambda}{\operatorname{vol}(J/Z)}
\operatorname{tr}\lambda(j^{-1})
\quad(j\in J),
\tag{9.1}
$$

and zero off $J$.  Schur orthogonality gives

$$
\operatorname{tr}\pi(e_\lambda)=\dim\operatorname{Hom}_J(\lambda,\pi).
\tag{9.2}
$$

The same definition applies to $J'\subset D^\times$.  Equality of dimensions in (9.2) is not by itself orbital transfer; it is only a spectral check.  To prove the level fundamental lemma we compare the finite sums obtained by inserting (9.1) into the lattice-chain decompositions.

### 9.2 Special packets

For an unramified character $\mu$, the split special representation $\operatorname{St}\otimes(\mu\circ\det)$ has its minimal line at Iwahori level, while its division companion $\mu\circ\operatorname{Nrd}$ is trivial on $\mathcal O_D^\times$.  The relevant type functions are therefore a norm twist of the pair in (5.4).  The tree proof gives their orbital transfer, and (9.2) gives trace one on the selected representations and zero on the unwanted spherical constituent.

If $\mu$ is ramified of conductor $m>0$, both selected conductors are $2m$.  Twisting the depth-zero special pair by $\mu$ does not mean multiplying an unrestricted function by a nonconstant determinant character across several shells.  One first fixes a norm shell, where the character is constant on central translations, and then performs the twist.  Equation (2.9) and equality of determinant and reduced norm preserve the orbital identity.

### 9.3 Depth-zero dihedral packets

Let $E/F$ be unramified quadratic and let $\bar\theta:k_{q^2}^\times\to\mathbf C^\times$ be regular.  On a regular residue element $x\notin k^\times$, the division type trace is

$$
\bar\theta(x)+\bar\theta(x^q),
\tag{9.3}
$$

whereas the split cuspidal type trace is

$$
-\bar\theta(x)-\bar\theta(x^q).
\tag{9.4}
$$

We recall the finite proof because it is the fundamental calculation.  Regard $k_{q^2}$ as a two-dimensional $k$-space.  Projection to the $\bar\theta$-isotypic part averages multiplication operators over $k_{q^2}^\times$.  Fourier transform in the complementary one-dimensional direction has two stationary embeddings, $x$ and $x^q$; all nonstationary additive-character orbits sum to zero.  Passing to the cuspidal quotient subtracts the second Bruhat cell, producing the minus sign in (9.4).  Regularity ensures the two characters are distinct and cancels the idempotent denominator against the free torus orbit.

Inflating the two finite types and decomposing the orbital integrals into the finitely many valuation positions yields the same two sums.  The quotient positions are two for the unramified torus on the division side; the split lattice count has the corresponding two embeddings.  Equations (9.3)--(9.4), with identical stabilizer volumes, prove orbital transfer of the normalized depth-zero type functions.

### 9.4 Positive-depth tame packets

Let $(E,\theta)$ be a tame admissible pair.  At its last nontrivial unit layer,

$$
\theta(1+x)=\psi_E(\beta x).
\tag{9.5}
$$

The split and division type traces reduce to finite Fourier sums on the complements of $E$ in $M_2(F)$ and $D$.  Choose $j$ with $jz=\sigma(z)j$.  The complementary line is $Ej$, and the commutator form is a scalar multiple of

$$
(u,v)\longmapsto
\operatorname{Tr}_{E/F}\bigl(\beta(u\sigma(v)-v\sigma(u))j^2\bigr).
\tag{9.6}
$$

The square $j^2$ lies in the norm class defining the cyclic algebra.  The split and division algebras use the two different classes of $F^\times/N_{E/F}(E^\times)$.  Therefore their normalized finite Fourier indices differ by

$$
\omega_{E/F}(j_D^2/j_G^2)=-1.
\tag{9.7}
$$

Changing $j$, the polarization, or additive coordinates multiplies both sides by the same norm-class factor.  The tame rectifier cancels the remaining torus Gauss phase.  Thus (9.7) is exactly $-1$.

Here is the finite-index calculation in one coordinate.  After quotienting the radical, choose a $k$-basis so that, in odd residual characteristic, the relevant quadratic phase is $ax^2$.  Its normalized Gauss sum is

$$
g(a)=|k|^{-1/2}\sum_{x\in k}\psi_k(ax^2).
$$

Changing $a$ to $a'$ changes the quotient by the quadratic character of $a'/a$.  The two cyclic algebras force this ratio to be the nonnorm class, whose quadratic character is $-1$.  In residual characteristic two, quadratic-form notation is replaced by the associated nondegenerate alternating module together with its quadratic refinement; the tame rectifier supplies the corresponding index change.  The selected dyadic case is unramified and tame, so that refinement is nondegenerate.  Ramified dyadic wild data are excluded because the refinement is no longer determined by the cyclic-algebra class alone.

At several positive-depth layers one might fear a product of many minus signs.  That does not occur.  Trace-dual successive quotients away from the last active layer occur in paired hyperbolic planes, whose normalized Fourier indices multiply to $1$.  Only the anisotropic complementary quotient left by the common torus contributes to the ratio, and that quotient records the single Brauer-class difference between $M_2(F)$ and $D$.  Hence the total ratio is one $-1$, independent of depth.

Near the center, extra embeddings enter the compact-induction trace.  Filter them by the largest congruence depth at which they agree with the fixed embedding.  Each graded fiber is an affine space over $k$; nonstationary fibers sum to zero, while stationary fibers have the form (9.6).  The radicals are the common torus directions and have equal cardinality on both sides.  Quotienting by them and applying (9.7) pairs every shell with sign $-1$.  This proves the identity on all regular elliptic classes, not only on the type-regular annulus.

### 9.5 The level-specific fundamental lemma

**Theorem 9.1 (special and selected dihedral fundamental lemma).**  Let $(\pi,\pi_D)$ be either a special pair or one of the depth-zero or tame positive-depth dihedral pairs constructed in Book 85.  Choose the normalized minimal type functions on the two sides, with the tame rectifier and compact-unit torus measures fixed above.  After replacing the split type function by its alternating segment projection, the functions satisfy (2.6)--(2.7).  Their central translates, contragredients, and norm twists also satisfy the same identity.

**Proof.**  Special pairs reduce to Theorems 5.1 and 6.1.  Depth-zero dihedral pairs reduce to the two stationary terms (9.3)--(9.4); all other finite Fourier terms cancel.  Positive-depth pairs reduce shell by shell to (9.6), and the cyclic-algebra norm class gives (9.7).  The alternating segment projection cancels every split tube by vertex-edge pairing.  Matching trace and norm identify support and the common torus coordinate.  Stabilizer measures agree because both are normalized by $\mathcal O_E^\times$.  Thus the only remaining ratio is $-1$, proving (2.7).  The operations in Section 2.4 prove the last assertion.  $\square$

The theorem excludes ramified dyadic positive-depth pairs and primitive wild packets.  In those cases the trace-dual filtration can jump and the last quotient need not be governed solely by the tame cyclic-algebra class.

## 10. Singular germs and central terms

### 10.1 What regular matching does not say

As $\gamma$ approaches a scalar $z$, $|D_G(\gamma)|$ tends to zero and $O_\gamma(f)$ may grow.  A pointwise identity on the regular set does not determine $f(z)$, nor does it by itself compare distributions supported at $z$.  Global trace formulas isolate the central term, so a defensible transfer argument must keep three assertions separate:

1. equality of regular elliptic orbital integrals with sign;
2. compatibility of their singular limits;
3. equality of the separately weighted central distributions.

No noncentral nonsemisimple class occurs in $D^\times$.  On $G$, however, the repeated-root fiber contains the regular unipotent orbit.  Its contribution is the second rank-two germ.

### 10.2 The two rank-two germs

Translate a neighborhood of $z$ to the identity and write a small element as $1+X$.  In $\mathfrak{gl}_2$ there are two nilpotent orbits: $\{0\}$ and the regular orbit.  Consequently a normalized regular orbital integral has an expansion

$$
I_{z(1+X)}(f)
=\Gamma_0(X)\,f(z)
+\Gamma_{\mathrm{reg}}(X)\,\mu_{\mathrm{reg},z}(f),
\tag{10.1}
$$

on each sufficiently small regular annulus.  Here $\Gamma_0$ is the universal square-root term and $\Gamma_{\mathrm{reg}}$ is locally constant after the Weyl normalization.  The coefficient $\mu_{\mathrm{reg},z}$ is the regular nilpotent orbital distribution translated to $z$.

On the division algebra the nilpotent cone contains only zero: if $X^2=0$ in a division ring then $X=0$.  Thus

$$
I_{z(1+Y)}(f_D)=\Gamma_0^D(Y)f_D(z).
\tag{10.2}
$$

The common trace pairing and common discriminant coordinate identify $\Gamma_0$ on matching elliptic directions.  Transfer therefore requires the split regular-nilpotent coefficient to vanish and the zero-germ coefficient to have the chosen sign after the central normalization is specified.

The assertion that there are only two split germs can be checked directly.  A nilpotent $2\times2$ matrix has characteristic polynomial $X^2$.  If it is nonzero, its image and kernel are the same one-dimensional subspace.  Choosing a vector outside the kernel and then its image gives a basis in which the matrix is

$$
N=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$

Conjugation by $\operatorname{diag}(c,1)$ rescales the upper-right entry through every element of $F^\times$, so every nonzero nilpotent is $G$-conjugate to $N$.  Thus no square-class family of nilpotent germs is present for $\mathrm{GL}_2$; such a family would arise only after replacing $G$ by $\mathrm{SL}_2$.

One can also see the form of (10.1) without a general germ theorem.  On a sufficiently small lattice in the Lie algebra, conjugation-invariant locally constant functions are constant on trace-determinant fibers away from the discriminant.  Scaling a regular element toward zero leaves only the zero orbit and the single nonzero nilpotent orbit as possible limits.  Homogeneity of the transverse Jacobian supplies $\Gamma_0$, while the constant term on each annulus supplies $\Gamma_{\mathrm{reg}}$.  This rank-two argument proves that there is no third distribution waiting at the singular boundary.

### 10.3 Cancellation for the Euler function

The fixed-subtree proof already contains the germ cancellation.  As an elliptic element approaches a scalar, its fixed subtree acquires longer branches.  In $e_{\mathrm{EP}}$, every new terminal vertex is paired with its incident edge.  Therefore the alternating sum remains $1$ in the unramified-core case and $1/2$ in the ramified-core case, independent of the depth of approach.

On a split approach, the fixed tube grows around an apartment.  Its vertex and edge contributions cancel exactly, leaving zero.  This says

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

and tends to zero as $\gamma\to z$.  The same is true on the division side with the opposite sign.  Thus the unit fundamental lemma reaches the singular boundary without an unaccounted regular-nilpotent distribution.

For selected higher-level functions, the shell filtration in Section 9.4 gives the same conclusion: nonstationary affine fibers cancel, common radicals match, and the alternating segment projection kills the split nilpotent germ.

### 10.4 Central distributions

Regular transfer does not assert $f_{\mathrm{ell}}(z)=-f_D^0(z)$.  Indeed at $z=1$,

$$
f_{\mathrm{ell}}(1)=-2+(q+1)=q-1,
\qquad f_D^0(1)=1.
\tag{10.5}
$$

This is not a contradiction.  In an inner-form trace comparison the central terms are

$$
\operatorname{vol}([G/Z])f(z)
\quad\text{and}\quad
\operatorname{vol}([D^\times/Z])f_D(z),
\tag{10.6}
$$

with global measures and the selected central character.  Their equality is a separate volume-and-point-value identity.  One must either choose the global normalizations and scalar multiples so that (10.6) agrees, or subtract the central representations on both spectral sides.  Altering local torus measures cannot repair (10.5).

For applications that demand a prescribed central value, Proposition 3.1 supplies regular corrections away from the center, while a small central neighborhood supplies a germ correction.  The two coefficients in (10.1) form a triangular $2\times2$ system: one function supported on a tiny scalar neighborhood controls $f(z)$, and an alternating vertex-edge function controls the regular nilpotent coefficient.  Solving this finite system adjusts the central term without changing the already prescribed regular elliptic values outside that neighborhood.  The global comparison must record which adjustment was chosen.

## 11. Character traces and uniqueness

### 11.1 Weyl integration with the two signs

Let $(f,f_D)$ be matching and assume its singular terms have been treated as in Chapter 10.  For a selected discrete-series pair $(\pi,\pi_D)$, Weyl integration decomposes the trace into regular tori.  The split contribution on $G$ vanishes by (2.6).  On an elliptic torus, substitute

$$
O_t(f)=-O_t(f_D),
\qquad
\Theta_\pi(t)=-\Theta_{\pi_D}(t).
$$

The Weyl groups, torus measures, and discriminants agree.  Hence the two signs cancel pointwise in the torus integral.

### 11.2 Trace matching

**Theorem 11.1.**  Under the preceding hypotheses,

$$
\operatorname{tr}\pi(f)=\operatorname{tr}\pi_D(f_D)
\tag{11.1}
$$

for every selected special or dihedral Jacquet--Langlands pair.

**Proof.**  The regular Weyl integrals agree by Section 11.1.  The normalized germ bounds make the integrals locally integrable at the singular divisor.  Equation (10.3) removes the unmatched split regular-nilpotent distribution.  Central character projections make the remaining scalar action the same; when the trace formula retains an explicit central term, it is compared separately by (10.6).  Therefore no distribution remains between the two regular integrals, proving (11.1).  $\square$

For the unit pair, (11.1) says that the alternating Iwahori projector selects Steinberg on $G$, while the maximal-order unit selects its one-dimensional division companion.  For dihedral pairs it says that the matching type idempotents select corresponding multiplicity lines.

### 11.3 Uniqueness modulo orbital null functions

Transfer is not unique as a test function.  If $u\in C_c^\infty(G)$ has zero orbital integral on every regular class, then $f+u$ transfers whenever $f$ does.  Conversely, if two transfers have the same support away from the singular set, their difference has zero regular orbital integrals by definition.

The correct uniqueness statement is therefore uniqueness in the cocenter

$$
C_c^\infty(G)\big/
\{u:O_\gamma(u)=0\text{ for all regular }\gamma\}.
\tag{11.2}
$$

The triangular segment construction chooses a concrete representative in this quotient.  Type idempotents choose another representative adapted to spectral traces.  They need not be equal as functions; their equality is the equality of the required orbital distributions.

## 12. Archimedean transfer

### 12.1 Real elliptic classes

Let $F=\mathbf R$, $G=\mathrm{GL}_2(\mathbf R)$, and $D=\mathbf H$.  A regular elliptic class is represented by

$$
rR_\theta,
\qquad
R_\theta=
\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix},
\quad 0<\theta<\pi.
$$

The Weyl factor is $2|\sin\theta|$.  The matching quaternion has the same trace $2r\cos\theta$ and norm $r^2$.  Split regular classes have no quaternionic partner.

### 12.2 Weight-$k$ transfer

For $k\ge2$, let $f_k$ be the normalized cuspidal projector selecting the weight-$k$ discrete series on $G$, and let $f_{D,k}$ be the normalized character projector for the $(k-1)$-dimensional representation of $\mathbf H^\times/\mathbf R_{>0}$.  The explicit orbital calculations give

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

The split projector's minus sign is the alternating orientation of the two real root directions.  Thus (12.1)--(12.2) prove archimedean transfer with the same convention (2.7).

### 12.3 The singular endpoints

As $\theta\to0$ or $\pi$,

$$
\frac{\sin((k-1)\theta)}{\sin\theta}
\longrightarrow (\pm1)^k(k-1).
$$

The ordinary orbital integral has a finite elliptic limit, while multiplication by the Weyl factor makes the normalized orbital integral tend to zero.  This is compatible with the finite-place pattern (10.4).  At $k=1$ there is no discrete-series projector with the asserted properties, so the hypothesis $k\ge2$ is essential.

## 13. Assembly for global comparison

### 13.1 Restricted tensor products

Let $F$ now be a number field and $D$ a quaternion algebra.  At almost every finite split place choose the common hyperspecial unit.  At a finite division place choose the pair (5.4), or the selected level pair of Theorem 9.1.  At a distinguished real division place choose (12.1)--(12.2).  At the remaining finitely many places use identical split functions or the regular patching construction.

The resulting restricted tensors

$$
f=\bigotimes_v f_v,
\qquad
f_D=\bigotimes_v f_{D,v}
\tag{13.1}
$$

are well-defined because almost every factor is hyperspecial.  For a global elliptic class $\gamma\leftrightarrow\delta$, quotient measures factor orbit by orbit, and so do orbital integrals.

### 13.2 Matching geometric terms

At each division place the local sign is $-1$; at each split place it is $+1$.  Thus

$$
O_\gamma(f)
=(-1)^{\#\operatorname{Ram}(D)}O_\delta(f_D)
\tag{13.2}
$$

for the regular elliptic global term, with the archimedean ramified places included.  A quaternion algebra over a number field is ramified at an even number of places, so the total sign is $+1$.  This parity follows from the product formula for local invariants of a quaternion algebra.  Hence the elliptic geometric sums agree term by term once the common torus-volume coefficient is identified.

The split and nonsemisimple terms on the $G$ side vanish because at least one selected local factor has zero split orbital integrals and zero parabolic transform.  The division side has no split classes and no noncentral nilpotent class.  Absolute convergence established in Book 110 permits the termwise comparison.  Central terms remain the explicitly separate calculation (10.6).

### 13.3 The normalization ledger

The entire comparison can be audited in one table.

| datum | normalization and consequence |
|---|---|
| absolute value | $|\varpi|=q^{-1}$ |
| split group measure | $\operatorname{vol}(K)=1$ |
| division group measure | $\operatorname{vol}(\mathcal O_D^\times)=1$ |
| quadratic torus | $\operatorname{vol}(\mathcal O_E^\times)=1$ |
| quotient measure | $dh=dt\,d\dot h$ |
| Iwahori | $\operatorname{vol}(I)=1/(q+1)$ |
| geometric edge | two orientations, producing $1/2$ |
| Weyl factor | $|D_H(h)|=|\Delta(h)/n(h)|$ |
| division quotient | $\operatorname{vol}(E^\times\backslash D^\times)=f(E/F)$ |
| regular orbital sign | $O_G=-O_D$ at division places |
| character sign | $\Theta_G=-\Theta_D$ for selected packets |
| trace sign | the two signs cancel |

Rescaling a group or torus measure changes the corresponding row and must be propagated through every orbital integral, formal degree, and global coefficient.  The formulas are consistent precisely because no row is changed in isolation.

### 13.4 Failure modes and boundary cases

Several tempting shortcuts are false.

Raw maximal-compact units do not transfer at a division place: their orbital integrals are $1$ versus $f(E/F)$.  Regular elliptic matching alone does not kill principal-series traces; split orbital vanishing is necessary.  Equality of trace and determinant does not include inseparable quadratic subalgebras in residue characteristic two; regular semisimplicity must be retained.  Residue eigenlines do not compute scalar-reduction orbital integrals at positive depth; full stable segments and their stabilizers are required.  Equality of representation traces does not determine central point values.  Finally, the tame Fourier-index proof does not cover ramified dyadic wild types.

These are boundaries of the theorem, not missing steps inside it.  The unit and Iwahori lemmas hold in every residue characteristic for separable regular classes because their proof uses the tree and valuation indices.  The selected positive-depth lemma has exactly the tame scope of the prior type construction.

## 14. Final synthesis

Transfer in rank two is governed by one invariant polynomial and one one-dimensional building.  Trace and norm identify the common elliptic classes of $\mathrm{GL}_2$ and its quaternionic inner form.  Compact-unit torus measures make the quaternionic orbital integral of the maximal-order unit equal to the residue degree $f(E/F)$.  The tree then supplies the missing function on the split group.

The decisive identity is the weighted Euler calculation

$$
O_\gamma\left(\mathbf1_K-\frac{q+1}{2}\mathbf1_I\right)
=
\begin{cases}
0,&\gamma\text{ split regular},\\
f(E/F)/2,&\gamma\text{ elliptic regular}.
\end{cases}
$$

Its proof pairs every noncore vertex with an edge.  A split torus leaves an apartment of Euler characteristic zero; an unramified elliptic torus has a vertex core; a ramified elliptic torus has an edge-midpoint core with half weight.  Multiplication by $-2$ gives the explicit unit fundamental lemma

$$
-2\mathbf1_K+(q+1)\mathbf1_I
\quad\longleftrightarrow\quad
\mathbf1_{\mathcal O_D^\times}.
$$

The same cellular mechanism proves the Iwahori statement and, after replacing vertices and edges by finite segments, the selected congruence statements.  Special type functions are norm twists of the alternating Iwahori projector.  Depth-zero dihedral functions reduce to the two residue-field embeddings, and positive-depth tame functions reduce to complementary finite Fourier forms whose cyclic-algebra norm classes differ by $-1$.  Congruence-shell filtration carries that comparison all the way to the near-central annuli.

The singular audit is equally explicit.  The split regular-nilpotent germ vanishes by vertex-edge cancellation; normalized elliptic integrals tend to zero; central point values remain a separate distribution with their actual global quotient volumes.  At the real place the sine quotient supplies the same transfer sign.  Globally, local ramification signs occur an even number of times, elliptic terms match orbit by orbit, and the selected cuspidal factor removes the unmatched nonelliptic geometry.

We have therefore constructed, rather than postulated, the matching functions required for rank-two global comparison: hyperspecial units at split places, the Euler--Iwahori unit at division places, spherical and central shells, selected congruence functions, special projectors, tame dihedral type functions, and the real discrete-series projectors.  Their Haar normalizations, regular orbital terms, singular germs, central qualifications, and transfer signs now form one closed local-to-global package.
