# Orbital Integrals for $\mathrm{GL}_2$ and Quaternion Algebras

## Contents

- [1. From conjugacy to local comparison](#1-from-conjugacy-to-local-comparison)
  - [1.1 Why orbital integrals are the local geometric terms](#11-why-orbital-integrals-are-the-local-geometric-terms)
  - [1.2 Standing conventions and scope](#12-standing-conventions-and-scope)
  - [1.3 The normalization ledger](#13-the-normalization-ledger)
- [2. Regular classes in degree two](#2-regular-classes-in-degree-two)
  - [2.1 Trace, norm, and discriminant](#21-trace-norm-and-discriminant)
  - [2.2 Split, elliptic, and singular elements](#22-split-elliptic-and-singular-elements)
  - [2.3 Rational and stable conjugacy](#23-rational-and-stable-conjugacy)
  - [2.4 Matching with a quaternion algebra](#24-matching-with-a-quaternion-algebra)
- [3. Measures on groups, tori, and orbits](#3-measures-on-groups-tori-and-orbits)
  - [3.1 Additive and multiplicative measures](#31-additive-and-multiplicative-measures)
  - [3.2 Group measures](#32-group-measures)
  - [3.3 Centralizer and quotient measures](#33-centralizer-and-quotient-measures)
  - [3.4 Scaling tests](#34-scaling-tests)
- [4. The Weyl discriminant and normalized orbital integrals](#4-the-weyl-discriminant-and-normalized-orbital-integrals)
  - [4.1 The determinant on the tangent space](#41-the-determinant-on-the-tangent-space)
  - [4.2 Orbital integrals](#42-orbital-integrals)
  - [4.3 Local constancy and convergence](#43-local-constancy-and-convergence)
  - [4.4 Weyl integration in rank two](#44-weyl-integration-in-rank-two)
- [5. Lattices and nonarchimedean orbital integrals](#5-lattices-and-nonarchimedean-orbital-integrals)
  - [5.1 The lattice interpretation](#51-the-lattice-interpretation)
  - [5.2 Optimal embeddings and quadratic orders](#52-optimal-embeddings-and-quadratic-orders)
  - [5.3 A finite weighted-count formula](#53-a-finite-weighted-count-formula)
  - [5.4 The maximal elliptic calculation](#54-the-maximal-elliptic-calculation)
  - [5.5 Ramified elliptic and split checks](#55-ramified-elliptic-and-split-checks)
- [6. Spherical and congruence test functions](#6-spherical-and-congruence-test-functions)
  - [6.1 Central translates of the unit](#61-central-translates-of-the-unit)
  - [6.2 Spherical Hecke shells](#62-spherical-hecke-shells)
  - [6.3 Iwahori functions](#63-iwahori-functions)
  - [6.4 Selected level functions](#64-selected-level-functions)
- [7. Quaternionic orbital integrals](#7-quaternionic-orbital-integrals)
  - [7.1 Compactness modulo the center](#71-compactness-modulo-the-center)
  - [7.2 Maximal-order unit functions](#72-maximal-order-unit-functions)
  - [7.3 Congruence shells](#73-congruence-shells)
  - [7.4 Comparing matching elliptic classes](#74-comparing-matching-elliptic-classes)
- [8. Germs and singular limits](#8-germs-and-singular-limits)
  - [8.1 Why ordinary orbital integrals become singular](#81-why-ordinary-orbital-integrals-become-singular)
  - [8.2 Split germs](#82-split-germs)
  - [8.3 Elliptic germs](#83-elliptic-germs)
  - [8.4 Central values and the two nilpotent germs](#84-central-values-and-the-two-nilpotent-germs)
  - [8.5 A normalization-independent matching criterion](#85-a-normalization-independent-matching-criterion)
- [9. Characters as local distributions](#9-characters-as-local-distributions)
  - [9.1 From pointwise characters to traces](#91-from-pointwise-characters-to-traces)
  - [9.2 Principal and special characters](#92-principal-and-special-characters)
  - [9.3 Dihedral characters](#93-dihedral-characters)
  - [9.4 Quaternionic character formulas](#94-quaternionic-character-formulas)
  - [9.5 The selected regular character identity](#95-the-selected-regular-character-identity)
- [10. The real place](#10-the-real-place)
  - [10.1 Real regular classes and measures](#101-real-regular-classes-and-measures)
  - [10.2 Weyl formulas and regular orbital integrals](#102-weyl-formulas-and-regular-orbital-integrals)
  - [10.3 Discrete-series test functions](#103-discrete-series-test-functions)
  - [10.4 Singular limits at the real place](#104-singular-limits-at-the-real-place)
- [11. The real quaternion inner form](#11-the-real-quaternion-inner-form)
  - [11.1 Polar coordinates on the real division algebra](#111-polar-coordinates-on-the-real-division-algebra)
  - [11.2 Characters and orbital integrals](#112-characters-and-orbital-integrals)
  - [11.3 The archimedean inner-form identity](#113-the-archimedean-inner-form-identity)
- [12. Fourier transforms on invariant coordinates](#12-fourier-transforms-on-invariant-coordinates)
  - [12.1 The trace--determinant quotient](#121-the-trace--determinant-quotient)
  - [12.2 Descent near a semisimple element](#122-descent-near-a-semisimple-element)
  - [12.3 Compatibility with self-dual additive measure](#123-compatibility-with-self-dual-additive-measure)
- [13. Local test-function identities](#13-local-test-function-identities)
  - [13.1 What it means to have the same regular data](#131-what-it-means-to-have-the-same-regular-data)
  - [13.2 The unit, Iwahori, and level packages](#132-the-unit-iwahori-and-level-packages)
  - [13.3 Character traces forced by regular identities](#133-character-traces-forced-by-regular-identities)
  - [13.4 Exceptional and boundary cases](#134-exceptional-and-boundary-cases)
- [14. A complete local comparison ledger](#14-a-complete-local-comparison-ledger)
  - [14.1 Nonarchimedean inputs](#141-nonarchimedean-inputs)
  - [14.2 Archimedean inputs](#142-archimedean-inputs)
  - [14.3 What has and has not been proved](#143-what-has-and-has-not-been-proved)
- [15. Conclusion](#15-conclusion)

## 1. From conjugacy to local comparison

### 1.1 Why orbital integrals are the local geometric terms

The trace of an operator is spectral: it adds eigenvalues. The same trace, when the operator is convolution by a function on a group, also has a geometric description. The geometric description groups kernel values by conjugacy class. Its local building block is therefore not the value of a test function at a point but its average along a conjugacy orbit. That average is an orbital integral.

Degree two is the first setting in which this average is both rich and explicitly manageable. In $\mathrm{GL}_2$ a regular semisimple class is determined by trace and determinant. It is split when the characteristic polynomial splits over the base field and elliptic when it generates a quadratic field. A quaternion division algebra contains precisely the quadratic-field classes and no split regular class. Thus the passage from $\mathrm{GL}_2$ to its nonsplit inner form deletes the split geometry and retains the elliptic geometry, with a sign on the corresponding discrete-series characters.

The apparent simplicity conceals three normalization problems. First, an orbit carries a quotient measure, and that measure depends on compatible choices on the group and its centralizer. Second, the orbit degenerates near the center; the unnormalized integral usually has a square-root singularity. Third, the split group and division group have different compact subgroups and different quotient volumes. A correct comparison must keep all three issues visible.

This book develops the local calculation needed for rank-two transfer. We classify regular and singular classes, fix compatible Haar measures, prove convergence and Weyl integration, reduce nonarchimedean orbital integrals to finite lattice counts, compute the unit, first Hecke, Iwahori, and selected congruence cases, analyze singular germs, and derive the regular character identities for special and quadratic-dihedral packets. At the real place we perform the corresponding elliptic calculation for $\mathrm{GL}_2(\mathbf R)$ and $\mathbf H^\times$. The construction of matching functions as a general theorem belongs to the next stage; here we establish the formulas and criteria which that construction must satisfy.

### 1.2 Standing conventions and scope

Until Chapter 10, $F$ is a nonarchimedean local field with ring of integers $\mathcal O$, maximal ideal $\mathfrak p=(\varpi)$, residue field $k$, and $|k|=q$. We set

$$
v(\varpi)=1,
\qquad |x|=q^{-v(x)}.
$$

Write

$$
G=\mathrm{GL}_2(F),\qquad Z=F^\times I_2,\qquad K=\mathrm{GL}_2(\mathcal O).
$$

Let $D$ denote the quaternion division algebra over $F$, with reduced trace $\operatorname{Trd}$, reduced norm $\operatorname{Nrd}$, maximal order $\mathcal O_D$, maximal ideal $\mathfrak P_D$, and valuation

$$
v_D(x)=v(\operatorname{Nrd}x).
$$

Thus a division uniformizer $\Pi$ has $v_D(\Pi)=1$, whereas a scalar $z$ has $v_D(z)=2v(z)$. This is the convention of the quaternionic representation theory recalled from Book 79.

All test functions are complex valued. At a nonarchimedean place they are locally constant and compactly supported; at an archimedean place they are smooth and compactly supported unless a rapidly decreasing matrix coefficient is explicitly used. Conjugation is $x^{-1}\gamma x$. Haar measures are left Haar measures. Both $G$ and $D^\times$ are unimodular, so no modular character appears when passing between left and right quotients.

We use results about smooth representations, $\mathrm{GL}_2(F)$, Weil--Deligne parameters, quaternionic representations, and real discrete series established in Books 73--75, 79, and 87. We recall every convention that affects a formula. We do not assume a local transfer theorem in proving the orbital calculations.

### 1.3 The normalization ledger

The following choices remain fixed.

| Object | Normalization |
|---|---|
| additive measure $dx$ on $F$ | $\operatorname{vol}(\mathcal O)=1$ |
| multiplicative measure $d^\times x$ | $\operatorname{vol}(\mathcal O^\times)=1$ |
| measure $dg$ on $G$ | $\operatorname{vol}(K)=1$ |
| measure $dd$ on $D^\times$ | $\operatorname{vol}(\mathcal O_D^\times)=1$ |
| split torus $A\simeq F^\times\times F^\times$ | product of $d^\times x$ |
| quadratic torus $E^\times$ | $\operatorname{vol}(\mathcal O_E^\times)=1$ |
| quotient $T\backslash H$ | $dh=dt\,d\dot h$ |
| Weyl discriminant | $D_H(\gamma)=\det(1-\operatorname{Ad}(\gamma)\mid\mathfrak h/\mathfrak h_\gamma)$ |
| normalized orbital integral | $I_\gamma(f)=|D_H(\gamma)|^{1/2}O_\gamma(f)$ |

The multiplicative measure is related to additive measure by

$$
d^\times x=(1-q^{-1})^{-1}\frac{dx}{|x|}.
$$

On a quadratic extension $E/F$, the displayed condition $\operatorname{vol}(\mathcal O_E^\times)=1$ defines the torus measure even when the additive measure on $E$ is instead chosen self-dual for a trace character. Those two normalizations must not be silently identified. Book 75 shows that if $\psi$ has conductor exponent $n(\psi)$ and $d(E/F)$ is the different exponent, then

$$
n(\psi\circ\operatorname{Tr}_{E/F})=e(E/F)n(\psi)+d(E/F).
$$

Consequently the self-dual additive volume of $\mathcal O_E$ need not be one. Orbital integrals in this book use the compact-unit normalization on multiplicative tori; Fourier transforms in Chapter 12 use self-dual additive measure and display the conversion factor.

For later auditing, suppose $dy$ is additive measure on $E$ with $\operatorname{vol}(\mathcal O_E)=c_E$. Then

$$
d_E^\times y=(1-q_E^{-1})^{-1}c_E^{-1}\frac{dy}{|y|_E}
\tag{1.1}
$$

has unit volume one. If $dy$ is self-dual for $\psi\circ\operatorname{Tr}_{E/F}$, then $c_E=q_E^{-n(\psi_E)/2}$. Thus (1.1) and the conductor formula above give the exact different factor needed to convert Fourier-normalized torus integrals to the orbital normalization. No unspecified canonical measure is being used.

## 2. Regular classes in degree two

### 2.1 Trace, norm, and discriminant

For either $H=G$ or $H=D^\times$, attach to $\gamma\in H$ its reduced characteristic polynomial

$$
P_\gamma(X)=X^2-t(\gamma)X+n(\gamma),
$$

where $(t,n)=(\operatorname{tr},\det)$ on $G$ and $(t,n)=(\operatorname{Trd},\operatorname{Nrd})$ on $D^\times$. Its polynomial discriminant is

$$
\Delta(\gamma)=t(\gamma)^2-4n(\gamma).
$$

This pair of invariants is not chosen merely for convenience. It is the categorical quotient for conjugation in degree two: every polynomial invariant of a matrix is a polynomial in trace and determinant, and the same assertion follows for a quaternion algebra after scalar extension to a splitting field.

**Proposition 2.1.** An element $\gamma$ is regular semisimple if and only if $\Delta(\gamma)\ne0$. In that case $F[\gamma]$ is an étale quadratic $F$-algebra and

$$
H_\gamma=F[\gamma]^\times.
$$

**Proof strategy.** The minimal polynomial has degree two exactly away from scalar elements, and separability is measured by its discriminant.

**Proof.** If $\Delta\ne0$, the two roots of $P_\gamma$ over a separable closure are distinct. Hence the minimal polynomial equals $P_\gamma$, the algebra $F[\gamma]$ has dimension two and is étale, and the commutant of a cyclic degree-two element in the ambient central simple algebra has dimension two. It is therefore $F[\gamma]$; taking units gives the centralizer. Conversely, if $\Delta=0$, the reduced characteristic polynomial is not separable. If it has a root in $F$, the element is scalar or becomes a nontrivial Jordan element on the split side. In characteristic two it may instead be irreducible and purely inseparable. None of these cases is regular semisimple. $\square$

The nontrivial Jordan alternative occurs in $M_2(F)$ but not in a division algebra: if $(\gamma-z)^2=0$ with $z\in F$ in a division ring, then $\gamma=z$. When $\operatorname{char}F\ne2$, this proves that every nonregular element of $D^\times$ is central. In characteristic two, however, $D$ may contain a purely inseparable quadratic field, and its noncentral generators have inseparable reduced characteristic polynomial. They are nonregular and must be excluded explicitly. The quaternionic singular analysis below concerns approaches through separable regular tori; it does not silently turn these inseparable elements into central classes.

### 2.2 Split, elliptic, and singular elements

For $G$, a regular semisimple element is **split** if $F[\gamma]\simeq F\times F$ and **elliptic** if $F[\gamma]$ is a quadratic field. Equivalently, $P_\gamma$ has two roots in $F$ in the split case and is irreducible in the elliptic case. When the residue characteristic is not two, the square class of $\Delta$ gives the same dichotomy. In residue characteristic two, the discriminant still detects separability but square-class language alone is insufficient; the étale algebra $F[X]/(P_\gamma)$ is the invariant definition.

The singular semisimple elements of $G$ are the scalars. There are also nonsemisimple elements

$$
z u_b=z\begin{pmatrix}1&b\\0&1\end{pmatrix},\qquad b\ne0.
$$

For $b,b'\ne0$, the elements $zu_b$ and $zu_{b'}$ are conjugate: conjugation by $\operatorname{diag}(1,b'/b)$ sends one to the other under our $x^{-1}\gamma x$ convention. Thus $\mathrm{GL}_2(F)$ has one nonzero nilpotent orbit. This would fail for the derived group $\mathrm{SL}_2(F)$, where the available diagonal scalings are squares; confusing the two groups creates spurious square-class germs. The unique regular unipotent class enters the singular germ expansion even though the regular trace formula is indexed by semisimple classes.

Every noncentral element of $D^\times$ generates a quadratic field when that field is separable. In residue characteristic two there can be inseparable quadratic subfields, so we retain the adjective regular semisimple and exclude those elements. This is exactly the boundary already isolated in Book 79.

### 2.3 Rational and stable conjugacy

Two regular semisimple elements of $G$ with the same characteristic polynomial are conjugate over $F$. To see this without invoking a classification theorem, view $F^2$ as a module over $F[X]/(P)$. Since $P$ is separable of degree two, a faithful two-dimensional module is free of rank one. Any two such module structures are therefore isomorphic, and an $F$-linear module isomorphism conjugates the matrices.

The same statement holds in $D^\times$: two regular elements with the same reduced characteristic polynomial determine two embeddings of the same quadratic field in $D$, and any two embeddings are conjugate. One may prove the embedding assertion directly. If $E/F$ is quadratic and $i_1,i_2:E\hookrightarrow D$, then $D$, considered as a left $E$-module through either embedding, has dimension two. Comparing the two simple module structures after scalar extension and descending a nonzero intertwiner gives $x\in D^\times$ with $i_2(a)=x^{-1}i_1(a)x$.

Thus for both inner forms, regular stable conjugacy and rational conjugacy coincide. This is special to degree two and to these groups. It means that no hidden finite sum of rational orbits sits inside one regular stable class.

### 2.4 Matching with a quaternion algebra

A regular element $\gamma\in G$ and $\delta\in D^\times$ **match** when

$$
t(\gamma)=t(\delta),\qquad n(\gamma)=n(\delta).
$$

Equivalently, they have the same characteristic polynomial. A split regular element of $G$ cannot match an element of $D^\times$, because a split quadratic algebra has nontrivial idempotents and cannot embed in a division algebra. Every elliptic regular element does match: its quadratic field embeds as a maximal subfield of $D$, and the image of the element has the same polynomial. The preceding section proves uniqueness of the resulting conjugacy class.

We therefore have an exact matching diagram:

```text
regular classes in D^x  ----->  regular classes in GL_2(F)
        |                                  |
        | (Trd,Nrd)                        | (tr,det)
        v                                  v
 irreducible separable quadratics  =  elliptic invariant pairs.
```

This is a bijection onto the elliptic regular classes, not onto all regular classes. Any transfer statement which assigns quaternionic data to split classes is wrongly typed.

In characteristic two the invariant test can be written explicitly. A polynomial

$$
P(X)=X^2+tX+n
$$

is separable exactly when $t\ne0$. Scaling $X=tY$ gives $Y^2+Y+n/t^2$. It splits over $F$ precisely when $n/t^2$ lies in the image of the Artin--Schreier map $y\mapsto y^2+y$; otherwise it defines a separable quadratic field. Thus the formal discriminant $t^2$ is nonzero in both cases and cannot distinguish split from elliptic. This is why the algebra $F[X]/(P)$, rather than a square class of $\Delta$, is the primary invariant throughout.

## 3. Measures on groups, tori, and orbits

### 3.1 Additive and multiplicative measures

The additive normalization $\operatorname{vol}(\mathcal O)=1$ implies

$$
\operatorname{vol}(\mathfrak p^m)=q^{-m}.
$$

Since $\mathcal O^\times=\mathcal O\setminus\mathfrak p$, its additive volume is $1-q^{-1}$. Hence

$$
d^\times x=(1-q^{-1})^{-1}|x|^{-1}dx
$$

gives $\operatorname{vol}(\mathcal O^\times)=1$. Each valuation shell $\varpi^m\mathcal O^\times$ then also has multiplicative volume one.

For a finite extension $E/F$, we independently normalize $d^\times e$ by $\operatorname{vol}(\mathcal O_E^\times)=1$. This makes the valuation quotient $E^\times/\mathcal O_E^\times\simeq\mathbf Z$ carry counting measure. If $E=F\times F$, the torus measure is the product measure. These choices make the compact-stabilizer formulas in Chapter 5 literal rather than true only up to a scalar.

### 3.2 Group measures

There is a unique Haar measure $dg$ on $G$ with $\operatorname{vol}(K)=1$. The Iwahori subgroup

$$
I=\left\{\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K:c\in\mathfrak p\right\}
$$

has index $q+1$, because $K/I\simeq\mathbf P^1(k)$. Thus

$$
\operatorname{vol}(I)=\frac1{q+1}.
$$

Likewise $K(m)=1+\varpi^mM_2(\mathcal O)$ has volume the reciprocal of its finite index in $K$. No dimension heuristic may replace this exact finite index at shallow level.

On $D^\times$ choose $dd$ by $\operatorname{vol}(\mathcal O_D^\times)=1$. Its congruence subgroups $U_D^m=1+\mathfrak P_D^m$ have

$$
\operatorname{vol}(U_D^m)=[\mathcal O_D^\times:U_D^m]^{-1}.
$$

Because $\mathcal O_D^\times/U_D^1\simeq\mathbf F_{q^2}^\times$ and every subsequent additive graded layer has $q^2$ elements,

$$
[\mathcal O_D^\times:U_D^m]=(q^2-1)q^{2(m-1)},\qquad m\ge1.
$$

### 3.3 Centralizer and quotient measures

Let $H$ be $G$ or $D^\times$, let $\gamma$ be regular, and let $T=H_\gamma$. Give $T$ the measure from Section 3.1 through its identification with $F[\gamma]^\times$. The quotient measure $d\dot x$ on $T\backslash H$ is characterized by

$$
\int_H\Phi(x)\,dx
=\int_{T\backslash H}\int_T\Phi(tx)\,dt\,d\dot x
$$

for every compactly supported continuous $\Phi$. Existence and uniqueness follow by first choosing local sections of $T\backslash H$ and then patching with a partition of unity; in the totally disconnected case, compact-open sections suffice.

This definition is more reliable than declaring a quotient volume informally. It also gives a useful compact-orbit formula. If $J\subset H$ is compact open and $h^{-1}\gamma h\in J$, then the orbit of $hJ$ in $T\backslash H$ has volume

$$
\frac{\operatorname{vol}(J)}{\operatorname{vol}(T\cap hJh^{-1})}.
\tag{3.1}
$$

Indeed, integrate the characteristic function of $ThJ$ in the quotient formula and use the fiber $T\cap hJh^{-1}$. Formula (3.1) is the source of every stabilizer weight in the lattice calculations.

### 3.4 Scaling tests

Suppose $dh$ is multiplied by $a>0$ and $dt$ by $b>0$. Then $d\dot h$ and every orbital integral are multiplied by $a/b$. The Weyl discriminant is algebraic and does not change. Therefore

$$
I_\gamma(f)\longmapsto \frac ab I_\gamma(f).
$$

This elementary rule is the fastest audit of a purported comparison. A character distribution $\operatorname{tr}\pi(f)$ scales by $a$ when the group measure scales. To preserve a character identity derived from orbital integrals, the centralizer measure must be transported as well. Formal degrees scale inversely with the quotient measure, in agreement with Books 79 and 87.

## 4. The Weyl discriminant and normalized orbital integrals

### 4.1 The determinant on the tangent space

For regular $\gamma\in H$, define

$$
D_H(\gamma)=\det\left(1-\operatorname{Ad}(\gamma)\mid
\mathfrak h/\mathfrak h_\gamma\right).
$$

This determinant measures the failure of the conjugation map to be singular transverse to the centralizer. In degree two it has an elementary expression.

**Proposition 4.1.** For either inner form,

$$
|D_H(\gamma)|=\frac{|\Delta(\gamma)|}{|n(\gamma)|}.
\tag{4.1}
$$

**Proof.** After extension to a splitting field, write the eigenvalues as $\alpha,\beta$. The quotient of the Lie algebra by the diagonal centralizer is the sum of the two root lines. Conjugation acts on them by $\alpha/\beta$ and $\beta/\alpha$. Thus

$$
D_H(\gamma)=(1-\alpha/\beta)(1-\beta/\alpha)
=-\frac{(\alpha-\beta)^2}{\alpha\beta}.
$$

Taking absolute values and using $(\alpha-\beta)^2=\Delta$ and $\alpha\beta=n$ proves (4.1). The calculation descends because both sides are invariant under the splitting field's Galois group. $\square$

The sign of the algebraic determinant is irrelevant for absolute normalization but relevant in orientation-sensitive real formulas. We therefore write $|D_H|$ in orbital integrals and retain $\Delta$ when discussing stable invariant coordinates.

### 4.2 Orbital integrals

For $f\in C_c^\infty(H)$ and regular $\gamma$, define

$$
O_\gamma(f)=\int_{H_\gamma\backslash H}f(x^{-1}\gamma x)\,d\dot x,
$$

and its normalized version

$$
I_\gamma(f)=|D_H(\gamma)|^{1/2}O_\gamma(f).
\tag{4.2}
$$

Conjugating $\gamma$ changes neither integral. Multiplication by a scalar $z\in F^\times$ leaves $D_H$ unchanged and gives

$$
O_{z\gamma}(f)=O_\gamma(f_z),
\qquad f_z(h)=f(zh).
\tag{4.3}
$$

Inversion gives

$$
O_{\gamma^{-1}}(f)=O_\gamma(f^\vee),
\qquad f^\vee(h)=f(h^{-1}),
\tag{4.4}
$$

provided the centralizer measure is transported by inversion. These two tests catch many support and determinant mistakes.

### 4.3 Local constancy and convergence

**Theorem 4.2.** For a nonarchimedean local field, $O_\gamma(f)$ converges absolutely for every regular semisimple $\gamma$ and $f\in C_c^\infty(H)$. On each fixed regular torus, it is locally constant as a function of $\gamma$.

**Proof strategy.** Compact support restricts the conjugating elements to a bounded region modulo the centralizer. For $G$, Cartan decomposition turns this into a bound on one tree distance. For $D^\times$, compactness modulo the center makes it immediate.

**Proof.** On $D^\times/F^\times$ the quotient is compact, and $F^\times\subset T$, so $T\backslash D^\times$ is compact. The integrand is bounded, proving convergence.

For $G$, let the support of $f$ lie in finitely many sets

$$
zK\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}K,
$$

with $z\in F^\times$ and $m$ bounded. If $x^{-1}\gamma x$ belongs to this support, the lattice vertex $x[\mathcal O^2]$ and its image under $\gamma$ have bounded distance. For a regular $\gamma$, the set of vertices with bounded displacement lies in a bounded tube around the apartment or fixed subtree of its torus. Modulo the torus, that tube has finitely many vertices. Hence the relevant subset of $T\backslash G$ is compact. Absolute convergence follows.

Choose a compact set in $G$ mapping onto that relevant quotient subset. Because $f$ is locally constant, a sufficiently small change of $\gamma$ inside $T$ leaves every value $f(x^{-1}\gamma x)$ unchanged uniformly on this compact set. The same compactness bound remains valid in a small regular neighborhood. The integral is therefore locally constant. $\square$

At an archimedean place the same theorem holds with smoothness replacing local constancy. Properness on support of the orbit map, together with differentiation under the integral, proves that orbital integrals are smooth on the regular set.

### 4.4 Weyl integration in rank two

Orbital integrals are not auxiliary decorations: they are precisely the radial pieces of Haar integration. Let $\mathcal T(H)$ be a set of representatives for rational conjugacy classes of maximal tori. For $G$ it contains the split torus and the quadratic field tori that embed in $M_2(F)$; for $D^\times$ it contains only field tori. Write $W(H,T)=N_H(T)/T$.

**Theorem 4.3 (Weyl integration).** For $f\in C_c^\infty(H)$,

$$
\int_H f(h)\,dh
=\sum_{T\in\mathcal T(H)}\frac1{|W(H,T)|}
\int_T |D_H(t)|O_t(f)\,dt.
\tag{4.5}
$$

The singular set has Haar measure zero and may be omitted.

**Proof strategy.** Apply change of variables to the conjugation map $T\times T\backslash H\to H$, then compute its transverse Jacobian.

**Proof.** On the regular locus the map $(t,\dot x)\mapsto x^{-1}tx$ is a local analytic isomorphism modulo the finite Weyl group. Its differential in an orbit direction $X\bmod\mathfrak t$ is $(1-\operatorname{Ad}(t)^{-1})X$, whose absolute determinant equals $|D_H(t)|$. The map has generic degree $|W(H,T)|$. Change of variables therefore gives the summand in (4.5). The discriminant-zero locus is the zero set of a nonzero polynomial in local coordinates and has measure zero.

In characteristic different from two only finitely many quadratic torus types occur. In equal characteristic two there can be infinitely many Artin--Schreier quadratic extensions, so the last sum must not be called finite. Apply the change-of-variables identity first to $|f|$: the resulting nonnegative sum over torus types is bounded by $\int_H|f(h)|\,dh$ and hence converges. Absolute convergence then permits the same sum for $f$. $\square$

In terms of normalized orbital integrals, the integrand is $|D_H(t)|^{1/2}I_t(f)$. This symmetric placement of the square root is the form suited to comparison with characters, whose regular singularities have the reciprocal square-root size.

## 5. Lattices and nonarchimedean orbital integrals

### 5.1 The lattice interpretation

The coset space $G/K$ is the set of rank-two $\mathcal O$-lattices in $F^2$: the coset $xK$ corresponds to $L_x=x\mathcal O^2$. Therefore

$$
x^{-1}\gamma x\in K
\quad\Longleftrightarrow\quad
\gamma L_x=L_x.
\tag{5.1}
$$

If only $x^{-1}\gamma x\in M_2(\mathcal O)$ is required, the right side becomes $\gamma L_x\subseteq L_x$. The equality in (5.1) uses invertibility of the reduction, equivalently $\det\gamma\in\mathcal O^\times$.

When $\gamma$ is elliptic and $E=F[\gamma]$, left multiplication makes $F^2$ a one-dimensional $E$-space. The centralizer $E^\times$ acts by rescaling lattices. Hence

$$
E^\times\backslash
\{x\in G:x^{-1}\gamma x\in K\}/K
$$

is the finite set of $E^\times$-homothety classes of $\gamma$-stable lattices. This is the decisive reduction: an integral over a noncompact $p$-adic orbit becomes a finite arithmetic count.

### 5.2 Optimal embeddings and quadratic orders

Assume that $\gamma$ is elliptic, integral, and has unit norm. Put

$$
R=\mathcal O[\gamma]\subseteq\mathcal O_E.
$$

A $\gamma$-stable lattice is precisely a fractional $R$-ideal: it is a finitely generated $\mathcal O$-lattice $L\subset E$ with $RL\subseteq L$. Its multiplier order is

$$
R_L=\{a\in E:aL\subseteq L\}.
$$

Because $L$ is a lattice, $R_L$ is an order between $R$ and $\mathcal O_E$. Its unit group is exactly the stabilizer of $L$ in $E^\times$.

For a quadratic field, every order containing $\mathcal O$ has the form

$$
\mathcal O_c=\mathcal O+\mathfrak p^c\mathcal O_E,
\qquad c\ge0,
$$

where $\mathfrak p^c\mathcal O_E$ means extension of the base-field ideal. Indeed, after choosing $\omega$ with $\mathcal O_E=\mathcal O\oplus\mathcal O\omega$, an order containing $\mathcal O$ is $\mathcal O\oplus I\omega$ for an ideal $I$ of the DVR $\mathcal O$; multiplicative closure forces no additional condition in degree two after replacing $\omega$ by an integral generator. Hence $I=\mathfrak p^c$. Equivalently, the order is determined by its conductor

$$
\mathfrak f(R)=\{a\in\mathcal O_E:a\mathcal O_E\subseteq R\}.
$$

There are only finitely many overorders of $R$. For each overorder, the local ideal classes represented by $R$-lattices with that multiplier order form a finite set. Thus the lattice quotient in Section 5.1 is finite. This proves finiteness arithmetically, independently of the tree proof in Theorem 4.2.

### 5.3 A finite weighted-count formula

Let $\mathscr L(\gamma)$ denote the $E^\times$-homothety classes of $\gamma$-stable lattices. Choose one $L=x\mathcal O^2$ in each class. Formula (3.1) gives the exact answer.

**Theorem 5.1 (elliptic unit formula).** If $\gamma$ is elliptic, $\gamma$ is integral, and $\det\gamma\in\mathcal O^\times$, then

$$
O_\gamma(\mathbf1_K)
=\sum_{[L]\in\mathscr L(\gamma)}
[\mathcal O_E^\times:R_L^\times].
\tag{5.2}
$$

If either integrality or the unit-norm condition fails, the orbital integral is zero.

**Proof.** The support condition is (5.1). Double cosets $E^\times xK$ are exactly homothety classes of stable lattices. The stabilizer $E^\times\cap xKx^{-1}$ is $R_L^\times$. Since $\operatorname{vol}(K)=1$ and $\operatorname{vol}(\mathcal O_E^\times)=1$, (3.1) assigns the double coset the weight

$$
\operatorname{vol}(R_L^\times)^{-1}
=[\mathcal O_E^\times:R_L^\times].
$$

Summing gives (5.2). If $x^{-1}\gamma x\in K$, its characteristic polynomial is integral with unit constant term, so the vanishing assertion follows. $\square$

Formula (5.2) is a computation, not merely a reinterpretation: it reduces the integral to a finite list of orders and their elementary unit indices. It is also robust in residue characteristic two, where discriminant exponents alone need not classify the order.

### 5.4 The maximal elliptic calculation

The most important clean case occurs when $R=\mathcal O_E$. Then every stable lattice is a fractional $\mathcal O_E$-ideal. Since $\mathcal O_E$ is a discrete valuation ring, every such ideal is principal, so there is one $E^\times$-homothety class and its multiplier order is $\mathcal O_E$.

**Corollary 5.2.** If $\mathcal O[\gamma]=\mathcal O_E$ and $\det\gamma\in\mathcal O^\times$, then

$$
O_\gamma(\mathbf1_K)=1,
\qquad
I_\gamma(\mathbf1_K)
=\left|\frac{\Delta(\gamma)}{\det\gamma}\right|^{1/2}.
\tag{5.3}
$$

This applies to both unramified and ramified quadratic $E/F$. In the unramified case, a convenient sufficient condition is that the reduction of $P_\gamma$ be irreducible over $k$. It then follows by Hensel lifting that $E/F$ is unramified and $\mathcal O[\gamma]=\mathcal O_E$. In a ramified quadratic extension generated by an integral uniformizer, one instead uses a unit $\gamma$ whose difference from a scalar generates the maximal order; merely saying “ramified elliptic” does not force maximality.

### 5.5 Ramified elliptic and split checks

If $R$ is nonmaximal, (5.2) explains exactly why the answer can exceed one: extra homothety classes and smaller stabilizer unit groups both contribute. For example, if the only ideal classes are represented by the overorders $R=R_0\subset R_1\subset\cdots\subset R_c=\mathcal O_E$, then

$$
O_\gamma(\mathbf1_K)=
\sum_{i=0}^c[\mathcal O_E^\times:R_i^\times].
\tag{5.4}
$$

Equation (5.4) is conditional on the stated ideal classification; (5.2), not (5.4), is the general formula. This distinction matters at dyadic places.

There is a parallel split calculation. Let $\gamma=\operatorname{diag}(a,b)$ with $a,b\in\mathcal O^\times$ and $a-b\in\mathcal O^\times$. The idempotents

$$
e_a=\frac{\gamma-b}{a-b},\qquad e_b=\frac{\gamma-a}{b-a}
$$

are integral polynomials in $\gamma$. Every stable lattice therefore decomposes as

$$
L=e_aL\oplus e_bL.
$$

The split torus rescales the two rank-one summands independently, so there is one homothety class and its stabilizer has volume one. Hence

$$
O_\gamma(\mathbf1_K)=1.
\tag{5.5}
$$

When $a-b\in\mathfrak p$, the idempotents cease to be integral. Mixed lattices then appear, and the answer grows with the depth $v(a-b)$. Thus “both eigenvalues are units” is not enough for (5.5); regular reduction is the missing hypothesis.

The tree makes this growth visible. The split torus fixes an apartment, the bi-infinite geodesic formed by lattices

$$
L_j=\mathcal Oe_1\oplus\varpi^j\mathcal Oe_2,
\qquad j\in\mathbf Z.
$$

If $c=v(a-b)$, then $\gamma$ fixes pointwise a tube of positive radius around this apartment. A vertex at distance $r$ from the apartment corresponds to a lattice in which the two eigenlines are mixed modulo $\mathfrak p^r$. Direct substitution shows that such a vertex is fixed only if $r\le c$; a sharper bound can be read from the elementary divisors of $\gamma-a$. The split torus is transitive along the apartment but not across the transverse branches. Thus the quotient of the fixed set by the torus is finite, and its vertices with their compact stabilizers give $O_\gamma(\mathbf1_K)$. This supplies an effective calculation at arbitrary depth without an unjustified closed formula.

Two examples check the hypotheses. Over $\mathbf Q_p$ with $p$ odd, take

$$
\gamma=\begin{pmatrix}0&-u\\1&t\end{pmatrix},
$$

where $X^2-tX+u$ is irreducible modulo $p$ and $u$ is a unit. Then $\mathcal O[\gamma]$ is the ring of integers in the unramified quadratic extension, so (5.3) gives $O_\gamma(\mathbf1_K)=1$. In contrast,

$$
\gamma_c=\begin{pmatrix}1&0\\0&1+\varpi^c\end{pmatrix}
$$

has unit eigenvalues but scalar reduction when $c\ge1$. The lattices generated by $e_1$ and $e_1+\varpi^{-r}e_2$, together with $e_2$, exhibit new stable classes for $1\le r\le c$. Thus its orbital integral cannot equal the regular-reduction value (5.5).

There is also a useful invariance under changing generators of the same order. If

$$
\gamma'=a+b\gamma,
\qquad a\in\mathcal O,\qquad b\in\mathcal O^\times,
$$

then $\mathcal O[\gamma']=\mathcal O[\gamma]$, and a lattice is $\gamma'$-stable exactly when it is $\gamma$-stable. If both elements have unit norm, their unit-function orbital integrals agree. Their discriminants differ by $b^2$, so their normalized orbital integrals also agree because $|b|=1$. This is a helpful check that the calculation depends on the embedded order, not on an arbitrary integral generator.

## 6. Spherical and congruence test functions

### 6.1 Central translates of the unit

For $r\in\mathbf Z$, put

$$
f_{r,0}=\mathbf1_{\varpi^rK}.
$$

By (4.3),

$$
O_\gamma(f_{r,0})=O_{\varpi^{-r}\gamma}(\mathbf1_K).
\tag{6.1}
$$

Thus Theorem 5.1 computes every central translate. Its support condition is

$$
v(\det\gamma)=2r
$$

together with integrality of the scaled trace $\varpi^{-r}\operatorname{tr}\gamma$. The parity condition is useful: it proves immediate vanishing on half of the determinant shells.

### 6.2 Spherical Hecke shells

For $m\ge0$ let

$$
h_m=\mathbf1_{K\operatorname{diag}(\varpi^m,1)K}.
$$

The elementary-divisor theorem says that $x^{-1}\gamma x$ lies in the support precisely when

$$
\gamma L_x\subseteq L_x,\qquad
L_x/\gamma L_x\text{ is cyclic of length }m.
\tag{6.2}
$$

In particular $v(\det\gamma)=m$. Let $\mathscr L_m(\gamma)$ be the $E^\times$-homothety classes of lattices satisfying (6.2). The same stabilizer argument proves

$$
O_\gamma(h_m)=
\sum_{[L]\in\mathscr L_m(\gamma)}
[\mathcal O_E^\times:R_L^\times]
\tag{6.3}
$$

for elliptic $\gamma$, with zero if the determinant valuation is wrong. For split $\gamma$, replace $E^\times$ by $F^\times\times F^\times$ and $R_L$ by the stabilizer of $L$ in that torus. Formula (6.3) is the required spherical-shell algorithm: Smith normal form decides (6.2), and a finite order computation gives each weight.

At $m=1$, the standard right-coset decomposition has $q+1$ cosets. If $\gamma$ acts on $L/\varpi L$ with two distinct eigenlines, the cyclic-colength-one lattices between $\gamma L$ and $L$ are read off from those lines. This gives a direct finite-field calculation rather than an appeal to Satake theory. The latter governs convolution eigenvalues; the present count governs conjugacy averages, and the two must not be conflated.

### 6.3 Iwahori functions

A coset in $G/I$ is a lattice chain

$$
L_0\supset L_1\supset\varpi L_0,
\qquad \dim_k(L_0/L_1)=1.
$$

Thus $x^{-1}\gamma x\in I$ precisely when $\gamma$ stabilizes the chain and acts invertibly on both lattices. If $\gamma\in K$ has regular reduction, invariant chains are invariant lines in $L_0/\varpi L_0$.

Assume first that $\bar\gamma$ has two distinct eigenvalues in $k$. There are two invariant lines. The split torus unit group fixes each one, and each Iwahori coset has volume $1/(q+1)$. Combining this with the regular-reduction calculation (5.5) gives

$$
O_\gamma(\mathbf1_I)=\frac{2}{q+1}.
\tag{6.4}
$$

If $\bar P_\gamma$ is irreducible over $k$, there is no invariant line, so

$$
O_\gamma(\mathbf1_I)=0.
\tag{6.5}
$$

If $\bar\gamma$ is scalar, every residue line is invariant, but stabilizers and lifts at deeper level can differ; neither (6.4) nor (6.5) applies. The exact answer is the weighted chain count

$$
O_\gamma(\mathbf1_I)=
\sum_{[\mathcal L]}
\frac{\operatorname{vol}(I)}
{\operatorname{vol}(T\cap\operatorname{Stab}(\mathcal L))},
\tag{6.6}
$$

where $\mathcal L$ runs through $T$-orbits of stable chains. This formula handles the singular-reduction boundary without pretending that a residue-field count alone suffices.

The other standard Iwahori basis element is $\mathbf1_{IwI}$, where $w=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$. It sends an oriented edge of the lattice tree across its initial vertex. Consequently its orbital integral is the same weighted count as (6.6), with the condition that $\gamma$ move the chain by the relative Weyl position $w$. Since $IwI$ has $q$ right $I$-cosets,

$$
\operatorname{vol}(IwI)=\frac q{q+1}.
$$

This agrees with the quadratic Hecke relation $(T_w+1)(T_w-q)=0$ under the unnormalized characteristic-function convention.

### 6.4 Selected level functions

For $n\ge1$, a $K_0(\mathfrak p^n)$-coset is a cyclic subgroup of order $q^n$ in the finite module $L/\mathfrak p^nL$, or equivalently a length-$n$ lattice segment. Therefore

$$
O_\gamma(\mathbf1_{K_0(\mathfrak p^n)})
=\sum_{[\mathcal S]}
\frac{\operatorname{vol}(K_0(\mathfrak p^n))}
{\operatorname{vol}(T\cap\operatorname{Stab}(\mathcal S))},
\tag{6.7}
$$

where $\mathcal S$ ranges over $T$-orbits of $\gamma$-stable length-$n$ segments. This is finite because the fixed-point set of a regular element meets only finitely many segment orbits modulo its torus.

Similarly, $K_1(\mathfrak p^n)$ remembers a generator of the terminal cyclic quotient. Stable segments are now weighted by the number of compatible fixed generators. Formula (6.7), with the stabilizer replaced by the pointwise stabilizer of that generator, remains exact. These formulas are the correct level-sensitive input: they distinguish $K_0$ from $K_1$, and they remain valid when the residue characteristic is two or the reduction is scalar.

The volume in (6.7) is explicit. Reduction modulo $\mathfrak p^n$ gives a transitive action of $K$ on $\mathbf P^1(\mathcal O/\mathfrak p^n)$, whose cardinality is

$$
q^n+q^{n-1}=q^{n-1}(q+1).
$$

Indeed, primitive pairs modulo $\mathfrak p^n$ number $q^{2n}-q^{2n-2}$, and dividing by the $q^n-q^{n-1}$ units gives the displayed value. Therefore

$$
\operatorname{vol}(K_0(\mathfrak p^n))
=\frac1{q^{n-1}(q+1)}.
\tag{6.8}
$$

For $K_1(\mathfrak p^n)$, the quotient remembers a primitive row rather than only its line. There are $q^{2n}-q^{2n-2}$ primitive rows, so

$$
[K:K_1(\mathfrak p^n)]=q^{2n}-q^{2n-2},
\qquad
\operatorname{vol}(K_1(\mathfrak p^n))
=\frac1{q^{2n}-q^{2n-2}}.
\tag{6.9}
$$

This formula uses the definition in which the lower-right entry is $1$ modulo $\mathfrak p^n$ and the lower-left entry is $0$. A convention allowing an arbitrary unit in the lower-right entry gives $K_0$, not $K_1$, and changes the index by $q^n-q^{n-1}$.

For regular reduction these index formulas recover the simplest level behavior. A split regular element has exactly two invariant lines modulo $\mathfrak p$, giving (6.4). An unramified elliptic element has none, giving (6.5). At level $n>1$, Hensel lifting preserves each simple split eigenline uniquely, whereas an irreducible residue polynomial still yields no invariant rank-one direct summand. Scalar reduction is the only place where multiple lifts proliferate, and (6.7) records their stabilizer weights exactly.

## 7. Quaternionic orbital integrals

### 7.1 Compactness modulo the center

Let $\delta\in D^\times$ be regular and $E=F[\delta]$. Since $F^\times\subset E^\times$ and $D^\times/F^\times$ is compact, the orbit space

$$
E^\times\backslash D^\times
$$

is compact. There is no split escape direction and no lattice tree. This proves convergence for every compactly supported function immediately.

The maximal order $\mathcal O_D$ is unique. Hence every $x\in D^\times$ normalizes it and its ideal filtration:

$$
x\mathcal O_Dx^{-1}=\mathcal O_D,
\qquad x\mathfrak P_D^mx^{-1}=\mathfrak P_D^m.
\tag{7.1}
$$

This feature sharply contrasts with $M_2(F)$, whose maximal orders are indexed by tree vertices.

### 7.2 Maximal-order unit functions

Because of (7.1), the function $\mathbf1_{\mathcal O_D^\times}$ is conjugation invariant. Hence

$$
O_\delta(\mathbf1_{\mathcal O_D^\times})
=\mathbf1_{\mathcal O_D^\times}(\delta)
\operatorname{vol}(E^\times\backslash D^\times).
\tag{7.2}
$$

The quotient volume is elementary. The valuation $v_D$ maps $D^\times/\mathcal O_D^\times$ onto $\mathbf Z$. Its restriction to $E^\times$ has image $f(E/F)\mathbf Z$, because

$$
v_D(e)=v(N_{E/F}e)=f(E/F)v_E(e).
$$

The unit groups on both sides have volume one. Therefore a fundamental domain contains $f(E/F)$ valuation cosets, each of volume one.

**Proposition 7.1.** With the measures of Chapter 3,

$$
O_\delta(\mathbf1_{\mathcal O_D^\times})=
\begin{cases}
f(E/F),&\delta\in\mathcal O_D^\times,\\
0,&\delta\notin\mathcal O_D^\times.
\end{cases}
\tag{7.3}
$$

Thus the answer is $2$ for an unramified quadratic torus and $1$ for a ramified quadratic torus. This dependence is not a defect: the raw unit functions on the two inner forms are not automatically matching functions under the present measures.

### 7.3 Congruence shells

A raw coset $\Pi^rU_D^m$ need not be stable under conjugation: although $U_D^m$ is normal, the chosen uniformizer is not central. The invariant objects are its conjugacy saturation, or, more intrinsically, compact-open sets specified by valuation together with congruences of reduced trace and norm. For any conjugation-invariant compact-open set $C$,

$$
O_\delta(\mathbf1_C)
=\mathbf1_C(\delta)\operatorname{vol}(E^\times\backslash D^\times)
=f(E/F)\mathbf1_C(\delta).
\tag{7.4}
$$

For a non-invariant coset or a matrix coefficient of a type, one uses the finite decomposition

$$
D^\times=\bigsqcup_{j=0}^{f(E/F)-1}E^\times\Pi^j\mathcal O_D^\times
\tag{7.5}
$$

and integrates over the compact unit quotients. Since the filtration quotients $U_D^m/U_D^{m+1}$ are finite additive groups, every such integral reduces after a finite depth to a character sum over $\mathbf F_{q^2}$. This is the quaternionic counterpart of the split lattice count.

### 7.4 Comparing matching elliptic classes

Let $\gamma\in G$ and $\delta\in D^\times$ match. Equation (4.1) gives

$$
|D_G(\gamma)|=|D_{D^\times}(\delta)|.
\tag{7.6}
$$

Therefore normalized and unnormalized matching differ by the same common discriminant factor. All remaining differences come from the test functions and quotient measures.

For the raw maximal compact units, a maximal-order elliptic $\gamma$ has orbital integral $1$ by (5.3), while $\delta$ has orbital integral $f(E/F)$ by (7.3). Thus a torus-independent scalar cannot make the two unit functions match simultaneously on ramified and unramified elliptic tori. The resolution is to modify the split or quaternionic function by additional shells. Establishing those modifications uniformly is the fundamental-lemma problem of the next book. The present calculation exposes exactly why that theorem is substantive.

It is useful to see the two quaternionic cases in cyclic coordinates. Write

$$
D=L\oplus L\Pi,
\qquad \Pi a=a^\sigma\Pi,qquad \Pi^2=\varpi,
$$

with $L/F$ unramified quadratic. If $\delta\in\mathcal O_L^\times$ has residue outside $k^\times$, then $F[\delta]=L$. Since $v_D(L^\times)=2\mathbf Z$, the two valuation representatives $1$ and $\Pi$ survive in $L^\times\backslash D^\times/\mathcal O_D^\times$. Both conjugates remain units, so the orbital integral is $2$.

If the residue characteristic is odd, a ramified quadratic field may be displayed as $E=F[\Pi u]$ for a suitable unit $u\in\mathcal O_L^\times$; the same display applies whenever a ramified quadratic field admits this cyclic coordinate. Its uniformizer has $D$-valuation one. In arbitrary residue characteristic the coordinate need not exist, but the intrinsic norm-valuation calculation gives the same conclusion: $v_D(E^\times)=\mathbf Z$. Thus only the representative $1$ survives and the orbital integral is $1$. This derivation also shows why one must use $v_D=v\circ\operatorname{Nrd}$: the half-integral alternative would hide the index that produces the factor two.

The same coordinate model computes type matrix coefficients. On the first quotient,

$$
\mathcal O_D^\times/U_D^1\simeq k_{q^2}^\times,
$$

conjugation by $\Pi$ acts as $x\mapsto x^q$. Hence a regular residue character appears through the orbit sum

$$
\bar\theta(x)+\bar\theta(x^q).
$$

At depth $m$, the quotient $U_D^m/U_D^{m+1}$ is the additive group of $k_{q^2}$, and conjugation acts semilinearly. The orbital integral of a matrix coefficient is therefore a finite sum with at most two valuation positions and finitely many additive-character values. No limiting analytic argument is hidden in the phrase “congruence-shell computation.”

## 8. Germs and singular limits

### 8.1 Why ordinary orbital integrals become singular

As a regular element approaches a scalar $z$, its centralizer jumps from dimension two to dimension four. Transversely, the conjugation map loses rank, and its Jacobian $|D_H(\gamma)|$ tends to zero. Thus $O_\gamma(f)$ can blow up even for a perfectly smooth test function. The normalized integral $I_\gamma(f)$ removes the universal square-root part of this blow-up.

To analyze the limit, translate by $z^{-1}$ and use a small neighborhood of the identity. For sufficiently small $X$ in the Lie algebra, $1+X$ is defined and conjugation-equivariant. Scalar directions separate, so the problem reduces to the trace-zero Lie algebra. There the invariant is $-\det X$, a one-dimensional coordinate, and the nilpotent cone is its zero fiber.

### 8.2 Split germs

Let $\mathfrak g_0=\mathfrak{sl}_2(F)$. There are two nilpotent conjugacy strata: $0$ and the regular nilpotent orbit. The latter is a single $G$-orbit; every nonzero nilpotent matrix is conjugate to $N=\left(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\right)$.

Fix the measure on its centralizer

$$
G_N=Z U,
\qquad
U=\left\{\begin{pmatrix}1&s\\0&1\end{pmatrix}:s\in F\right\}
$$

by giving $Z$ its compact-unit multiplicative measure and $U$ the additive measure for which $\mathcal O$ has volume one. The quotient formula then defines the translated regular-nilpotent distribution

$$
\mu_{N,z}(f)
=\int_{G_N\backslash G} f\bigl(z(1+x^{-1}Nx)\bigr)\,d\dot x,
$$

The integral converges by the same compact-support argument as a regular orbital integral. If one uses a smaller Lie neighborhood in the slice proof, extending its cutoff changes the displayed germ coefficients but not their sum on that neighborhood.

**Theorem 8.1 (rank-one two-germ expansion).** Fix a regular quadratic-algebra type $\mathcal A$ in $M_2(F)$. For $f\in C_c^\infty(G)$ and $z\in Z$, there are functions $\Gamma_{0,\mathcal A}$ and $\Gamma_{N,\mathcal A}$, determined by the group, torus, and nilpotent-centralizer measures fixed above, such that on every sufficiently small regular annulus of type $\mathcal A$,

$$
I_{z(1+X)}(f)
=\Gamma_{0,\mathcal A}(X)f(z)
+\Gamma_{N,\mathcal A}(X)\mu_{N,z}(f).
\tag{8.1}
$$

The coefficients are locally constant on sufficiently small valuation annuli and satisfy

$$
\Gamma_{0,\mathcal A}(X)\longrightarrow0,
\qquad
\Gamma_{N,\mathcal A}(X)=c_{\mathcal A}
\tag{8.2}
$$

on every sufficiently deep ray of fixed type, for a nonzero constant $c_{\mathcal A}$ fixed by the declared measures. Thus the normalized singular limit detects the regular-nilpotent orbital distribution, not the raw point value $f(z)$. In the unnormalized orbital integral the regular-nilpotent coefficient has size $|D_G(1+X)|^{-1/2}$, while the zero-orbit coefficient stays bounded.

**Proof strategy.** Use companion matrices as a transverse slice and sum the conjugation integral by the valuation of one off-diagonal coordinate. Shells that collapse to zero and shells that converge toward the nonzero nilpotent orbit give the two terms. Finite Fourier inversion shows there can be no third term.

**Proof.** Write

$$
X=\begin{pmatrix}x&y\\c&-x\end{pmatrix},
\qquad -\det X=x^2+yc=u.
\tag{8.3}
$$

On the chart $c\ne0$, conjugation by the upper unipotent changes $x$ affinely; after $x$ is eliminated, $y$ is forced by (8.3). Diagonal conjugation changes the valuation of $c$ and contributes the root Jacobian. Thus the orbital integral is a finite sum of valuation shells once the support of $f$ is fixed. The bounded shells collapsing to zero see $f(z)$. The growing string of shells parallel to the nonzero nilpotent orbit, after a fixed rescaling, samples that orbit and gives $\mu_{N,z}(f)$. Multiplication by $|D|^{1/2}$ kills the bounded zero-orbit coefficient and turns the growing regular-nilpotent coefficient into the nonzero constant $c_{\mathcal A}$.

To see that these are the only distributions, note that the singular fiber $u=0$ consists exactly of $0$ and the one nonzero nilpotent orbit. On each finite quotient of a small Lie lattice, Fourier inversion in the transverse coordinate expresses any invariant shell sum as a linear combination of evaluation at zero and the sum over the nonzero nilpotent orbit. Passing through the nested finite quotients gives (8.1). Finally choose $f$ supported in a small thickening of a compact-open piece of the regular nilpotent orbit, disjoint from $z$, with $\mu_{N,z}(f)\ne0$. The root-coordinate change of variables has positive nonzero Jacobian on that piece, so its normalized limiting coefficient is nonzero. This proves $c_{\mathcal A}\ne0$. The construction also proves local constancy on annuli and preserves the declared measures. $\square$

The theorem deliberately does not assign $c_{\mathcal A}$ the value one. Compact-unit normalization of different tori was fixed in Chapter 3 and cannot now be rescaled separately to manufacture such a value. For example, the lattice count for $\mathbf1_K$ grows as the order $\mathcal O[1+X]$ becomes less maximal; after Weyl normalization its leading constant depends on whether the limiting quadratic torus is split, unramified elliptic, or ramified elliptic. Formula (5.2) computes that constant without ambiguity.

There is an especially important cancellation phenomenon. A linear combination of vertex and edge functions can kill $\mu_{N,z}$ while retaining a nonzero value at $z$. Its ordinary regular orbital integral may then remain bounded, and its normalized orbital integral tends to zero. Consequently

$$
I_{z(1+X)}(f)\longrightarrow0
$$

does **not** imply $f(z)=0$. This distinction is essential at the interface with transfer.

The shell proof also explains why local constancy on the regular set does not give a locally constant extension across the center. As $v(u)$ crosses a threshold, a new nilpotent-direction shell enters the sum. Singular limits are therefore identities among measured germs, not pointwise continuation statements.

### 8.3 Elliptic germs

An elliptic family can approach a scalar only when its discriminant tends to zero through nonsquares, or through the corresponding separable quadratic invariant in residue characteristic two. The same slice proof applies. The companion matrix does not care whether its nonzero invariant fiber is split or elliptic; only the square class of the parameter changes. Hence the two-germ expansion (8.1) remains valid along elliptic regular elements.

Here “the same slice proof” means the same two-dimensional space of germs, not identical numerical coefficient functions for every torus. If quotient measures are rescaled separately in different torus classes, further artificial constants appear. Likewise, using $|\Delta|^{1/2}$ rather than $|D_G|^{1/2}$ introduces the central factor $|\det\gamma|^{1/2}$. Near $zI_2$ that factor tends to $|z|$, so the two conventions have different singular coefficients.

### 8.4 Central values and the two nilpotent germs

The phrase “two nilpotent germs” refers to the two nilpotent **orbits** $\{0\}$ and $\mathcal O_N$, not to two nonzero rational orbits. Their distributions are

$$
f\longmapsto f(z),
\qquad
f\longmapsto\mu_{N,z}(f).
$$

They have different homogeneity as distributions, and their coefficient functions have the complementary homogeneity. In the **normalized** expansion (8.1), the zero-orbit coefficient tends to zero and the regular-nilpotent coefficient has degree zero. Before Weyl normalization, the latter carries the reciprocal square-root growth. Reversing these roles gives the false conclusion that a normalized singular limit recovers $f(z)$.

On $D^\times$, there is no nonzero nilpotent element. Moreover $E^\times\backslash D^\times$ is compact. For a regular $\delta\to z$ within a fixed torus type,

$$
O_\delta(f)\longrightarrow
f(z)\operatorname{vol}(E^\times\backslash D^\times),
$$

and hence

$$
I_\delta(f)\longrightarrow0.
\tag{8.4}
$$

The disappearance of the regular nilpotent germ is the singular geometric signature of the anisotropic inner form.

### 8.5 A normalization-independent matching criterion

Suppose functions $f$ on $G$ and $f_D$ on $D^\times$ satisfy

$$
I_\gamma(f)=-I_\delta(f_D)
\tag{8.5}
$$

on matching regular elliptic classes, with zero split regular normalized orbital integrals for $f$. The sign is the rank-two inner-form transfer sign; one may instead absorb it into the definition of transfer.

Letting matching elements approach the center and using (8.1), (8.2), and (8.4) forces

$$
c_{\mathcal A}\mu_{N,z}(f)=0
\tag{8.6}
$$

for every elliptic approach type occurring in the matching. Since $c_{\mathcal A}\ne0$, regular transfer kills the split regular-nilpotent germ. It neither forces $f(z)=0$ nor identifies $f(z)$ with $f_D(z)$. In applications, an alternating vertex--edge function kills $\mu_{N,z}$ while having a nonzero central value. Central distributions on the two groups must therefore be computed separately with their actual global coefficients. This conclusion is normalization-independent and is the correct singular interface for the transfer theorem.

## 9. Characters as local distributions

### 9.1 From pointwise characters to traces

For an admissible representation $\pi$ of $G$, its distribution character is

$$
\Theta_\pi(f)=\operatorname{tr}\pi(f),
\qquad
\pi(f)=\int_Gf(g)\pi(g)\,dg.
$$

On the regular semisimple set it is represented by a locally integrable, locally constant function $\Theta_\pi(g)$. Therefore

$$
\operatorname{tr}\pi(f)=\int_G f(g)\Theta_\pi(g)\,dg.
\tag{9.1}
$$

Applying Weyl integration gives

$$
\operatorname{tr}\pi(f)=
\sum_T\frac1{|W(G,T)|}
\int_T |D_G(t)|O_t(f)\Theta_\pi(t)\,dt.
\tag{9.2}
$$

This identity explains why normalized orbital integrals pair naturally with normalized characters $|D_G(t)|^{1/2}\Theta_\pi(t)$. It also proves that equality of regular orbital data implies equality of traces against representations whose characters satisfy the corresponding pointwise identity, provided the singular set contributes no separate distribution.

For $D^\times$, every irreducible representation is finite dimensional and its pointwise matrix trace is already locally constant. Equation (9.1) is then ordinary finite-dimensional linear algebra.

### 9.2 Principal and special characters

Let $\chi_1,\chi_2$ be characters of $F^\times$ and let $I(\chi_1,\chi_2)$ be normalized induction. If $\gamma$ is regular split with eigenvalues $a,b$, the fixed-point formula on $\mathbf P^1(F)$ gives

$$
\Theta_{I(\chi_1,\chi_2)}(\gamma)
=\frac{\chi_1(a)\chi_2(b)+\chi_1(b)\chi_2(a)}
{|D_G(\gamma)|^{1/2}}.
\tag{9.3}
$$

On the elliptic regular set it is zero because an elliptic element fixes no $F$-rational line. The denominator is the fixed-point Jacobian combined with normalized induction, exactly as in the real calculation of Book 87.

At the reducibility wall there is an exact sequence whose constituents are $\mu\circ\det$ and $\operatorname{St}\otimes\mu$, where the latter abbreviates $\operatorname{St}\otimes(\mu\circ\det)$. Character additivity and the vanishing of the induced character on elliptic elements yield

$$
\Theta_{\operatorname{St}\otimes\mu}(\gamma)
=-\mu(\det\gamma)
\qquad(\gamma\text{ elliptic regular}).
\tag{9.4}
$$

This proof also fixes the sign: it is not a free convention once the Steinberg representation is the generic constituent and characters are ordinary traces.

### 9.3 Dihedral characters

Let $E/F$ be quadratic and let $\theta$ be a regular character, so $\theta\ne\theta^\sigma$. The selected dihedral supercuspidal $\pi(E,\theta)$ is compactly induced from a compact-mod-center subgroup $J$ containing $E^\times$. On a sufficiently regular element $t\in E^\times$, the compact-induction character formula reduces to the two embeddings of $E$:

$$
\Theta_{\pi(E,\theta)}(t)
=c_G(t)\bigl(\theta(t)+\theta(t^\sigma)\bigr).
\tag{9.5}
$$

The scalar $c_G(t)$ is the trace of the finite Heisenberg factor divided by the conjugation Jacobian. At depth zero it is constant on each regular residue shell; at positive depth it is a normalized finite Fourier sum. Its exact value is determined, not guessed, by the inducing character and the self-dual measure of Book 75.

For completeness, the computation is as follows. The induced character is

$$
\Theta_\pi(t)=
\sum_{x\in J\backslash G,\ xtx^{-1}\in J}
\operatorname{tr}\Lambda(xtx^{-1}).
\tag{9.6}
$$

Intertwining regularity says that the contributing cosets lie in the two normalizer positions of $E^\times$. Their torus values are $t$ and $t^\sigma$. On the congruence quotient, $\Lambda$ is a Heisenberg representation. Its trace vanishes off the central radical and on the radical equals its dimension times the defining additive character. Finite Fourier inversion, with annihilator lattice determined by the different, produces $c_G(t)$. Thus (9.5) includes wild-looking scalar factors without suppressing them.

### 9.4 Quaternionic character formulas

The one-dimensional representation $\rho=\mu\circ\operatorname{Nrd}$ has

$$
\Theta_\rho(\delta)=\mu(\operatorname{Nrd}\delta).
\tag{9.7}
$$

For a quaternionic dihedral representation $\rho(E,\theta)=\mathrm{c\text{-}Ind}_{J_D}^{D^\times}\Lambda_D$, the finite-index character formula from Book 79 gives

$$
\Theta_{\rho(E,\theta)}(t)
=c_D(t)\bigl(\theta(t)+\theta(t^\sigma)\bigr)
\tag{9.8}
$$

on the corresponding regular torus shell. Here too $c_D(t)$ is the trace of the finite Heisenberg factor. Unlike the split formula, no root singularity is hidden in a noncompact orbit: the group is compact modulo center. The factor nevertheless changes with depth because the inducing representation changes dimension.

### 9.5 The selected regular character identity

**Theorem 9.1.** For the special pairs and for the depth-zero or tame quadratic-dihedral pairs constructed in the selected range of Books 74 and 79 and compared in Book 80, matching regular elements satisfy

$$
\boxed{\Theta_{\pi}(\gamma)=-\Theta_{\rho}(\delta).}
\tag{9.9}
$$

Moreover the split regular character of $\pi$ has no quaternionic partner.

**Proof strategy.** The special row follows from an exact sequence. For the dihedral row, use the paired tame-type trace calculation proved in Book 80 after checking that its rectifier, additive character, valuation, and pointwise-character conventions agree with the inducing data of Book 79 and the self-dual measures of Book 75. We recall the terminal finite calculation to make the sign visible, but do not replace the earlier full compact-induction proof by a two-coset approximation near the center.

**Proof.** If $\pi=\operatorname{St}\otimes\mu$ and $\rho=\mu\circ\operatorname{Nrd}$, equations (9.4) and (9.7), together with $\det\gamma=\operatorname{Nrd}\delta$, prove the identity.

For a quadratic-dihedral pair, the rectified torus character used on the two sides is the same one. Matching identifies the two copies of $E$, the values at $t$ and $t^\sigma$, the trace-dual congruence lattices, and the Heisenberg commutator pairings. Book 80 proves that every nonterminal compact-induction contribution cancels in paired finite Fourier fibers, including the extra fibers that occur when the element is close to the center. The terminal transverse plane is hyperbolic for $M_2(F)$ and anisotropic for $D$. Its normalized Fourier sums have ratio $-1$, as (9.10)--(9.11) below verify. Thus the scalar traces satisfy $c_G(t)=-c_D(t)$ and (9.9) follows. This use is genuine prior-library mathematics: Book 75 supplies only the trace-character and self-dual-measure normalization, while Book 79 supplies the division type and its finite character formula; neither is being silently promoted into the comparison theorem. $\square$

Here is the finite calculation behind the sign. On a residue quotient of odd characteristic, the split transverse plane has hyperbolic quadratic form $Q_s(x,y)=xy$, whereas the anisotropic transverse plane has a norm form $Q_a(u)=N_{k_{q^2}/k}(u)$ multiplied by a nonsquare scalar. For a nontrivial additive character $\bar\psi$ of $k$,

$$
\sum_{x,y\in k}\bar\psi(xy)=q.
\tag{9.10}
$$

Indeed, the inner sum over $y$ is $q$ for $x=0$ and zero otherwise. For the anisotropic plane, group terms by norm. Each nonzero norm has $q+1$ preimages and zero has one, so

$$
\sum_{u\in k_{q^2}}\bar\psi(Nu)
=1+(q+1)\sum_{a\in k^\times}\bar\psi(a)
=-q.
\tag{9.11}
$$

Thus the normalized Gauss sums differ by $-1$. At higher tame depth, the new layers occur in dual pairs and their Fourier sums cancel in the ratio, leaving the same first anisotropic sign. In characteristic two one uses the polar form and the established separable trace pairing; the selected type calculation gives the same ratio. This supplies the decisive scalar step omitted by a bare comparison of parameter names.

The determinant, conductor, and additive-character conventions matter in this proof. Changing $\psi$ changes both finite Fourier sums by the same determinant factor; the relative sign remains $-1$. Unramified twisting multiplies both sides by $\mu(n)$, again preserving the identity. At residue characteristic two, the statement applies to the selected pairs whose type construction and trace pairing were established; it makes no claim about an unconstructed primitive wild packet.

## 10. The real place

### 10.1 Real regular classes and measures

We now take $F=\mathbf R$ and $G=\mathrm{GL}_2(\mathbf R)$. The selected global applications have totally real base field, so these are the archimedean places that require an inner-form comparison. There is no quaternion division algebra over $\mathbf C$, and no complex-place calculation is asserted here.

The center is $Z=\mathbf R^\times$. A regular split element is conjugate to $\operatorname{diag}(a,b)$ with $a\ne b$. A regular elliptic element is conjugate to

$$
\gamma=rR_\theta,
\qquad
R_\theta=
\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix},
\qquad \theta\notin\pi\mathbf Z.
\tag{10.1}
$$

Its centralizer is $T\simeq\mathbf C^\times$. Matching invariant pairs are

$$
\operatorname{tr}\gamma=2r\cos\theta,
\qquad
\det\gamma=r^2,
\qquad
\Delta(\gamma)=-4r^2\sin^2\theta.
$$

Therefore

$$
|D_G(\gamma)|^{1/2}=2|\sin\theta|.
\tag{10.2}
$$

We use the measure convention of Book 87: on $(G/Z)^0=\mathrm{PSL}_2(\mathbf R)$, $\mathrm{PSO}(2)$ has volume one and the quotient upper-half-plane measure is $dx\,dy/y^2$; the other component has the translated measure. On $T/Z\simeq\mathrm{SO}(2)/\{\pm1\}$ use probability measure. Together with $d^\times r=dr/|r|$ on the center, this determines $dt$ and the quotient measure on $T\backslash G$.

For the split torus $A$, use $d^\times a\,d^\times b$. The real Weyl group has order two for both $A$ and $T$. Every formula below changes predictably under rescaling by Section 3.4.

### 10.2 Weyl formulas and regular orbital integrals

The elliptic orbit of $rR_\theta$ in the positive component is parametrized by the upper half-plane. Since the orbital quotient is the **left** quotient $T\backslash G$, choose $g_z$ so that $g_z^{-1}$ carries $i$ to $z=x+iy$. Then

$$
O_{rR_\theta}(f)
=\int_{\mathfrak H}f(g_z^{-1}rR_\theta g_z)\frac{dx\,dy}{y^2}
\tag{10.3}
$$

for a function supported in the positive component. This is independent of the chosen measurable section because changing $g_z$ on the left by the elliptic centralizer does not change the conjugate. Choosing instead a matrix that carries $i$ to $z$ parametrizes a right quotient and reverses the section convention; the integral is the same only after replacing that matrix by its inverse.

For a positive split element $ra_t$, where

$$
a_t=\begin{pmatrix}e^{t/2}&0\\0&e^{-t/2}\end{pmatrix},
\qquad t\ne0,
$$

the quotient $A\backslash G$ may be parametrized on its open Bruhat cell by the two unipotent coordinates, modulo the one redundancy absorbed by $A$. The corresponding integral is

$$
O_{ra_t}(f)=\int_{A\backslash G}f(g^{-1}ra_tg)\,d\dot g.
\tag{10.4}
$$

Equations (10.3)--(10.4), together with

$$
|D_G(ra_t)|^{1/2}=|e^{t/2}-e^{-t/2}|,
\tag{10.5}
$$

are explicit convergent coordinate formulas. Compact support bounds $z$ in (10.3) away from the boundary of every cusp-shaped escape region unless the orbit meets the support; the same root-coordinate estimate proves convergence of (10.4).

In these coordinates the Weyl formula becomes

$$
\begin{aligned}
\int_{G^+}f(g)\,dg
&=\frac12\int_{\mathbf R^\times}\int_{\mathbf R\setminus\{0\}}
|e^{t/2}-e^{-t/2}|^2O_{ra_t}(f)\,dt\,d^\times r\\
&\quad+
\frac12\int_{\mathbf R^\times}\int_0^\pi
4\sin^2\theta\,O_{rR_\theta}(f)\,d\theta_0\,d^\times r.
\end{aligned}
\tag{10.6}
$$

where $d\theta_0=d\theta/\pi$ is the probability measure on $T/Z$. The $t$-measure is the one induced from the declared split-torus and group measures; writing it as $dt$ fixes that coordinate normalization. Formula (10.6) is best read as a measure identity, not as permission to change one displayed coordinate measure independently of the others.

### 10.3 Discrete-series test functions

Let $D_k$ be the full-group discrete series of Book 87, $k\ge2$, with trivial real-power twist for simplicity. It has elliptic character

$$
\Theta_{D_k}(rR_\theta)
=-\operatorname{sgn}(r)^k
\frac{\sin((k-1)\theta)}{\sin\theta}
\tag{10.7}
$$

and formal degree $(k-1)/(4\pi)$ for the measure above.

A **cuspidal projector** for $D_k$ is a smooth compact-mod-center function $f_k$ with the prescribed central character such that

$$
\operatorname{tr}D_k(f_k)=1,
\qquad
\operatorname{tr}\pi(f_k)=0
$$

for every irreducible tempered representation with different infinitesimal and minimal compact type. It can be constructed from a compactly supported Euler--Poincaré function on $G/Z$: take the alternating trace of the two-term relative Lie algebra complex and project to the $K$-types $\pm k$. Finite propagation of the compact-type projector gives compact support modulo $Z$.

**Theorem 10.1.** The projector can be normalized so that

$$
O_{rR_\theta}(f_k)
=-\operatorname{sgn}(r)^k
\frac{\sin((k-1)\theta)}{\sin\theta},
\qquad
O_{ra_t}(f_k)=0.
\tag{10.8}
$$

**Proof strategy.** Compute the orbital supertrace of the relative Lie algebra complex. A split element has two fixed flags with opposite cohomological contributions; an elliptic element has one compact fixed orbit, whose fiber trace is the finite-dimensional $\operatorname{Sym}^{k-2}$ character.

**Proof.** On a split regular element the two fixed points on $\mathbf P^1(\mathbf R)$ contribute the same root denominator and opposite signs in the alternating complex, so the sum is zero. On $rR_\theta$, the fixed point occurs only after complexification. The alternating normal determinant cancels the Weyl denominator. The contributing relative Lie algebra cohomology lies in degree one, so its supertrace supplies a minus sign and leaves

$$
-\operatorname{sgn}(r)^k
\operatorname{tr}(R_\theta\mid\operatorname{Sym}^{k-2}\mathbf C^2)
=-\operatorname{sgn}(r)^k\frac{\sin((k-1)\theta)}{\sin\theta}.
$$

The scalar is fixed by requiring trace one on $D_k$ and using its formal degree. This proves (10.8). $\square$

For $k=2$ the elliptic orbital integral is simply $-1$ and the split integral is zero. This is the exact archimedean function used to suppress nonelliptic geometric terms in the weight-two trace comparison.

### 10.4 Singular limits at the real place

As $\theta\to0$,

$$
\frac{\sin((k-1)\theta)}{\sin\theta}\longrightarrow k-1.
\tag{10.9}
$$

Thus the orbital integral in (10.8) has finite elliptic limit $-(k-1)\operatorname{sgn}(r)^k$, while the normalized integral tends to zero because $|D|^{1/2}=2|\sin\theta|$. The discrete-series character has the same limit by (10.7), because its numerator and denominator vanish to the same order. On the split side, the character

$$
2\operatorname{sgn}(r)^k
\frac{e^{-(k-1)|t|/2}}{|e^{t/2}-e^{-t/2}|}
$$

has a $|t|^{-1}$ singularity. Multiplication by the Weyl denominator removes it and gives limit $2\operatorname{sgn}(r)^k$. These observations illustrate an important distinction: orbital integrals of the specially constructed projector are bounded, whereas arbitrary orbital integrals and pointwise characters can display root singularities. “Singular limit” must always name the object being normalized.

At $k=1$, (10.8) has zero elliptic term. This is not a harmless endpoint: Book 87 proves that the limit-of-discrete series is not square-integrable, so formal degree is not defined for it. The formula $(k-1)/(4\pi)$ merely tends to zero at the boundary; it does not assign a zero formal degree to $D_1$. The limit representation cannot serve as the cuspidal archimedean projector used here.

## 11. The real quaternion inner form

### 11.1 Polar coordinates on the real division algebra

Let $D_\infty=\mathbf H$, Hamilton's quaternion algebra. Every nonzero quaternion has a unique polar decomposition

$$
q=\rho u,\qquad \rho=\sqrt{\operatorname{Nrd}(q)}>0,\qquad u\in\mathrm{SU}(2),
$$

together with the central sign already contained in $u$. Modulo $\mathbf R^\times$, one obtains

$$
\mathbf H^\times/\mathbf R^\times\simeq\mathrm{SO}(3).
$$

Give this compact quotient volume one, and give the center $d^\times r=dr/|r|$. This defines Haar measure on $\mathbf H^\times$. A regular element is nonreal and may be represented, compatibly with the real-matrix notation, by

$$
\delta=r(\cos\theta+i\sin\theta),
\qquad r\in\mathbf R^\times,\quad 0<\theta<\pi.
$$

This parametrization has the expected Weyl redundancy: changing the sign of $r$ replaces the angle by its supplementary angle after conjugating $i$ to $-i$. The positive radial coordinate in the polar decomposition is $|r|$. Its centralizer is $\mathbf C^\times$, and it matches $rR_\theta$ in $\mathrm{GL}_2(\mathbf R)$. The discriminant formula is again

$$
|D_{\mathbf H^\times}(\delta)|^{1/2}=2|\sin\theta|.
$$

### 11.2 Characters and orbital integrals

Irreducible representations of $\mathbf H^\times$ with algebraic compact type are obtained from the $(m+1)$-dimensional representation $V_m=\operatorname{Sym}^m(\mathbf C^2)$ of $\mathrm{SU}(2)$, extended across the center with the required parity. In the untwisted normalization its central character on $\mathbf R^\times$ is $\operatorname{sgn}^m$; an absolute-value twist may be added independently. Its regular character is

$$
\Theta_{V_m}(r(\cos\theta+i\sin\theta))
=\operatorname{sgn}(r)^m
\frac{\sin((m+1)\theta)}{\sin\theta},
\tag{11.1}
$$

with the central exponent adjusted if an absolute-value twist is present.

Because the quotient by the center is compact, Schur orthogonality gives an explicit trace-one character projector. This statement is made in the Hecke space with the fixed central character: functions are compactly supported modulo $\mathbf R^\times$ and transform by the inverse central character. This qualification is essential when $m$ is odd, since $V_m(-1)=(-1)^m$ and its character is not an ordinary function on $\mathbf H^\times/\mathbf R^\times$. With quotient volume one, put

$$
p_m(u)=\overline{\Theta_{V_m}(u)}
$$

on a section of the compact quotient and extend it by the required central equivariance. If one works with genuinely compactly supported functions on $\mathbf H^\times$ instead, multiply by a central cutoff of multiplicative integral one; all formulas then acquire that explicitly chosen cutoff at the central coordinate. In the fixed-central-character space,

$$
\operatorname{tr}V_j(p_m)=\delta_{jm}.
\tag{11.2}
$$

Here $V_j$ ranges over representations in the same fixed-central-character Hecke space; after an absolute-value twist this means the same central exponent and parity. Schur orthogonality gives $V_m(p_m)=(m+1)^{-1}\operatorname{id}$, whose trace is one; for $j\ne m$ it gives zero. The actual convolution idempotent is $(m+1)p_m$, and its trace on $V_m$ is $m+1$. Keeping these two normalizations separate prevents a dimension error.

Since $p_m$ is conjugation invariant and has the declared central equivariance,

$$
O_\delta(p_m)=p_m(\delta)
\operatorname{vol}(\mathbf C^\times\backslash\mathbf H^\times).
\tag{11.3}
$$

Thus every regular orbital integral is an elementary sine quotient times the declared quotient volume. With both compact group quotient and compact torus quotient of volume one, Weil's quotient formula gives $\operatorname{vol}(\mathbf C^\times\backslash\mathbf H^\times)=1$, and (11.3) is exactly the character quotient in (11.1). We retain the declared measures rather than renormalizing separately for each representation.

### 11.3 The archimedean inner-form identity

The representation corresponding to $D_k$ on $\mathbf H^\times$ is $V_{k-2}$ with the same central character. Comparing (10.7) and (11.1) gives, on matching regular elements,

$$
\boxed{
\Theta_{D_k}(rR_\theta)
=-\Theta_{V_{k-2}}(r(\cos\theta+i\sin\theta)).}
\tag{11.4}
$$

For $k=2$, the split discrete-series character is $-1$ on the elliptic set and the quaternionic character is $1$. This is the archimedean form of the same inner-form sign as (9.9).

Normalize the quaternionic idempotent using the same group and centralizer measures. Its elliptic orbital integral is the positive finite-dimensional character in (11.1), whereas (10.8) is its negative. Thus the two trace-one projectors obey the geometric sign convention (8.5). The pointwise representation characters obey the same inner-form sign (11.4); the two signs cancel in the trace comparison. No independent rescaling of a torus quotient is needed.

## 12. Fourier transforms on invariant coordinates

### 12.1 The trace--determinant quotient

For this chapter we return to the nonarchimedean field $F$ and the normalizations of Chapters 1--9. The archimedean Fourier transform is not needed for the selected comparison.

The map

$$
c:M_2(F)\longrightarrow F^2,
\qquad X\longmapsto(\operatorname{tr}X,\det X)
\tag{12.1}
$$

organizes conjugacy-invariant integration. Its Jacobian vanishes exactly on the discriminant divisor $t^2-4n=0$. Away from that divisor, the coarea formula says that pushing forward a test function along $c$ gives the orbital integral times the Weyl Jacobian.

One must specify which measures occur in this assertion. Let $dX_0$ give $M_2(\mathcal O)$ volume one. On $G$,

$$
dg=\frac{|\det g|^{-2}}{(1-q^{-1})(1-q^{-2})}\,dX_0.
\tag{12.2}
$$

Indeed the expression on the right is left and right invariant, while the additive volume of $K$ is

$$
\frac{|\mathrm{GL}_2(k)|}{q^4}=(1-q^{-1})(1-q^{-2});
$$

thus (12.2) is forced by $\operatorname{vol}(K)=1$. On a quadratic centralizer, formula (1.1) gives the corresponding conversion from additive measure to the compact-unit multiplicative measure. Applying these two explicit conversions and then the coarea formula shows, on each regular quadratic-algebra chart, that

$$
c_*(f\,dX_0)(t,n)
=J_{\mathcal A}(t,n)\,I_\gamma(f),
\tag{12.3}
$$

where $J_{\mathcal A}$ is the nonvanishing locally constant density obtained from (1.1) and (12.2). It is determined by the declared measures and should not be replaced by one universal constant across split, ramified, and unramified charts. The essential singular factor in (12.3) is exactly

$$
|D_G(\gamma)|^{1/2}=|\Delta(\gamma)|^{1/2}|n(\gamma)|^{-1/2}.
$$

This is why the square-root normalization is natural from invariant theory, not only from character estimates.

### 12.2 Descent near a semisimple element

Let $s$ be semisimple and write $H_s$ and $\mathfrak h_s$ for its group and Lie-algebra centralizers. Choose a sufficiently small $H_s$-stable neighborhood $\mathcal U$ of $0$ in $\mathfrak h_s$. The correct descent space is the associated bundle

$$
H_s\backslash\bigl(H\times(s+\mathcal U)\bigr),
\qquad
a\cdot(h,Y)=(ah,aYa^{-1}),
\tag{12.4}
$$

with map

$$
[h,Y]\longmapsto h^{-1}Yh.
$$

It is a submersion near $[1,s]$. The orbit part of its derivative is $1-\operatorname{Ad}(s)$ on $\mathfrak h/\mathfrak h_s$, while the $\mathfrak h_s$ direction supplies the transverse slice. Hence its orbit Jacobian is the Weyl discriminant. Integration along the fibers transfers invariant distributions near $s$ to invariant distributions near $s$ in the centralizer.

For regular $s$, the centralizer is a torus and descent merely proves smoothness or local constancy of orbital integrals. For central $s$, the centralizer is all of $H$ and the first nontrivial transverse invariant is the quadratic discriminant. This is the conceptual origin of the germ calculation in Chapter 8.

The submersion claim follows directly from the derivative. Choose an $\operatorname{Ad}(s)$-stable complement $\mathfrak q$ to $\mathfrak h_s$. Semisimplicity makes $1-\operatorname{Ad}(s)$ invertible on $\mathfrak q$, so the orbit directions cover $\mathfrak q$ and the slice directions cover $\mathfrak h_s$. The ordinary implicit-function theorem over $\mathbf R$ and the nonarchimedean analytic inverse-function theorem produce the local chart. The associated-bundle quotient in (12.4) is what records both the orbit directions and the residual conjugation action of $H_s$.

### 12.3 Compatibility with self-dual additive measure

Fix a nontrivial additive character $\psi$ of $F$. Book 75 normalizes its conductor by declaring the largest fractional ideal in its kernel to be $\mathfrak p^{-n(\psi)}$ and proves

$$
\operatorname{vol}_\psi(\mathcal O)=q^{-n(\psi)/2}.
$$

Use the trace pairing

$$
\langle X,Y\rangle=\operatorname{tr}(XY)
$$

to define Fourier transform on $M_2(F)$. If $dX_0$ gives $M_2(\mathcal O)$ volume one, the self-dual measure is

$$
dX_\psi=q^{-2n(\psi)}dX_0,
\tag{12.5}
$$

because the space has dimension four. On a quadratic field centralizer, trace descent uses $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$, whose conductor exponent is

$$
e(E/F)n(\psi)+d(E/F).
$$

The different therefore supplies precisely the volume correction between the self-dual centralizer measure and the compact-unit measure used for orbital integrals. Both split and division forms use the same field $E$ on matching classes, so this correction cancels in their ratio. This proves that the relative inner-form sign in (9.9) is independent of the conductor of $\psi$.

## 13. Local test-function identities

### 13.1 What it means to have the same regular data

We remain over the nonarchimedean field $F$ in Sections 13.1--13.4; the real analogue is the projector identity of Chapter 11.

Let $f\in C_c^\infty(G)$ and $f_D\in C_c^\infty(D^\times)$. With the geometric-sign convention of Chapter 8, call their regular data compatible if

$$
I_\gamma(f)=-I_\delta(f_D)
\tag{13.1}
$$

for every matching elliptic regular pair and

$$
I_\gamma(f)=0
\tag{13.2}
$$

for every split regular $\gamma$. Since matching discriminants agree, one may replace normalized integrals by unnormalized ones in (13.1), but only because the same centralizer measure has been transported through the common quadratic field.

The Weyl formula does not contain a separate integral over central elements, because they form a Haar-null set, but distributions supported on the center can still occur as separate geometric terms. For exact inner-form matching, the normalized singular limit kills the split regular-nilpotent germ; it neither forces the split central value to vanish nor identifies it with the quaternionic central value. A separately declared central distribution is therefore still required when a global trace identity includes central classes.

### 13.2 The unit, Iwahori, and level packages

The calculations of Chapters 5--7 may be summarized as finite recipes.

| function | split-side orbital integral | quaternionic orbital integral |
|---|---|---|
| $\mathbf1_K$ | weighted stable-lattice count (5.2), equal to $1$ for maximal regular order | not applicable |
| $\mathbf1_I$ | weighted stable-chain count (6.6); $2/(q+1)$ for split regular reduction, $0$ for irreducible reduction | not applicable |
| spherical shell $h_m$ | cyclic-colength weighted count (6.3) | not applicable |
| $\mathbf1_{K_0(\mathfrak p^n)}$ | stable-segment count (6.7) | not applicable |
| invariant quaternionic shell | not applicable | $f(E/F)$ times its value at the class (7.4) |
| type matrix coefficient | finite lattice/chain Fourier sum | finite congruence-layer Fourier sum |

These are computations for individual functions. They do not assert that a displayed split function already transfers to the function in the same row on the division side. Indeed, Section 7.4 proves that raw unit functions cannot be matched by one scalar across both ramification types with our measures. A genuine unit or level fundamental lemma must form the correct linear combination and prove equality of the resulting finite counts.

### 13.3 Character traces forced by regular identities

Suppose $(f,f_D)$ satisfy (13.1)--(13.2), have compatible central character, and have no unaccounted singular distribution. Let $(\pi,\rho)$ be one of the special or selected dihedral pairs of Theorem 9.1. Weyl integration gives

$$
\operatorname{tr}\pi(f)
=\sum_{T\ \mathrm{elliptic}}
\frac1{|W(G,T)|}\int_T
|D_G(t)|O_t(f)\Theta_\pi(t)\,dt,
\tag{13.3}
$$

because the split orbital integrals vanish. Identify each elliptic torus with the corresponding torus in $D^\times$. Substitute both minus signs, one from (13.1) and one from (9.9). They cancel. The Weyl groups, discriminants, and torus measures agree, so

$$
\boxed{\operatorname{tr}\pi(f)=\operatorname{tr}\rho(f_D).}
\tag{13.4}
$$

This proof explains the division of labor between geometry and representation theory. Orbital transfer contributes one sign; the inner-form character identity contributes the other. The trace identity has no sign.

Twisting both functions by a character through determinant and reduced norm preserves the argument. Contragredience follows by inversion and (4.4). Changing group measures rescales both sides only when centralizer and formal-degree normalizations are transported according to Section 3.4.

### 13.4 Exceptional and boundary cases

Several hypotheses cannot be dropped.

First, a principal series has nonzero split character and no quaternionic partner. The trace identity (13.4) therefore requires the split orbital vanishing (13.2); elliptic matching alone is insufficient.

Second, a one-dimensional representation $\mu\circ\det$ does not pair with $\mu\circ\operatorname{Nrd}$. The latter corresponds to Steinberg, as the sign computation (9.4) shows. Matching characters by dimension would put the reducibility-wall packets in the wrong rows.

Third, at residue characteristic two, inseparable quadratic subfields are not regular semisimple tori. All regular formulas remain valid for separable quadratic algebras, but one may not replace that hypothesis by “noncentral.” Primitive wild character formulas not supplied by the selected type construction are outside Theorem 9.1.

Fourth, singular limits do not determine central values. A global comparison must compare its central distributions using the actual central measures and central characters. Regular matching only supplies the approach to that boundary.

Finally, at the real place $k\ge2$ is essential. The limit $k=1$ has no cuspidal projector with the asserted formal-degree normalization.

## 14. A complete local comparison ledger

### 14.1 Nonarchimedean inputs

At a finite place, the reusable calculation proceeds in the following logically ordered way.

1. Compute $P_\gamma(X)=X^2-tX+n$ and verify $\Delta\ne0$.
2. Determine whether $F[X]/(P_\gamma)$ is split or a separable quadratic field. In residue characteristic two, do this directly rather than by square classes alone.
3. Normalize the centralizer measure by compact units and the group measure by the maximal compact subgroup.
4. Compute $|D_H(\gamma)|=|\Delta/n|$.
5. For $\mathrm{GL}_2$, translate support into stable lattices, chains, or segments and apply the stabilizer weight (3.1).
6. For $D^\times$, use uniqueness of the maximal order, the valuation quotient (7.5), and the finite congruence filtration.
7. Near the center, multiply by $|D_H|^{1/2}$ and check the regular-nilpotent germ on the split side; the zero-orbit coefficient tends to zero after normalization but its raw central distribution remains separate.
8. For a selected representation pair, apply the regular character identity with sign $-1$.

Every step has now been proved. The only input left for a general fundamental lemma is the combinatorial identity equating the two finite recipes for the specifically constructed pair of functions.

### 14.2 Archimedean inputs

At a real place, a regular elliptic class is represented by $rR_\theta$ and has discriminant factor $2|\sin\theta|$. The weight-$k$ cuspidal projector has

$$
O_{rR_\theta}(f_k)=
-\operatorname{sgn}(r)^k\frac{\sin((k-1)\theta)}{\sin\theta},
\qquad O_{ra_t}(f_k)=0.
$$

The matching quaternionic representation is $V_{k-2}$, and its character is the same sine quotient without the inner-form minus sign. For parallel weight two, these become the particularly transparent values

$$
O_{rR_\theta}(f_2)=-1,
\qquad
\Theta_{D_2}(rR_\theta)=-1,
\qquad
\Theta_{V_0}(\delta)=1.
$$

The singular elliptic limit of the orbital integral is $-(k-1)\operatorname{sgn}(r)^k$, while its normalized version tends to zero. The split discrete-series character has a root singularity, but its Weyl-normalized character has a finite limit. These statements refer to different functions and must not be merged.

### 14.3 What has and has not been proved

This book has proved the class classification, all measure conversion rules, the discriminant formula, convergence, Weyl integration, exact finite formulas for the named compact and level functions, the quaternionic volume calculation, the rank-one singular germ behavior, the selected special and dihedral character identities, and the real discrete-series and quaternionic formulas.

It has not declared the raw characteristic functions to be transfers when their computed orbital integrals disagree. Nor has it proved a general fundamental lemma, constructed transfer for every Hecke-algebra element, or treated twisted conjugacy. Those are distinct problems: the next rank-two transfer stage uses the formulas here to build matching functions, while the later twisted theory changes the centralizer and norm geometry.

This boundary is mathematical rather than editorial. An orbital-integral computation gives the two sides of an identity; a fundamental lemma identifies the correct functions and proves that the computed finite expressions coincide. Keeping those assertions separate prevents circular use of the theorem that the calculation is meant to support.

## 15. Conclusion

Regular conjugacy in degree two is governed by a single quadratic polynomial. Its trace and norm identify rational classes, its discriminant separates the regular locus from the singular divisor, and its associated étale algebra distinguishes split from elliptic geometry. The quaternion division algebra retains exactly the quadratic-field classes. This makes matching precise before any representation is introduced.

Measures turn that classification into analysis. Compact-unit normalizations on tori, maximal-compact normalizations on groups, and the quotient identity $dh=dt\,d\dot h$ fix every orbital constant. The Weyl determinant is

$$
|D_H(\gamma)|=|\Delta(\gamma)/n(\gamma)|,
$$

and its square root produces the normalization compatible with invariant coordinates, singular germs, and character formulas.

At a nonarchimedean place, split orbital integrals become finite weighted counts of stable lattices, chains, and segments. The weights are exact reciprocal stabilizer volumes. Quaternionic orbital integrals become finite valuation and congruence sums because the maximal order is unique and the central quotient is compact. The unit calculation already reveals a genuine ramification-dependent discrepancy, explaining why transfer requires carefully chosen linear combinations rather than an informal identification of compact units.

Near a scalar, the split group has both the zero and regular-nilpotent germs, while the division group has only the zero germ. Weyl normalization detects the regular-nilpotent coefficient and leaves the raw central distribution as a separate term; this, rather than a point-value identity, is the complete singular boundary in rank one. On the representation side, the special and selected dihedral characters differ across matching elliptic classes by the inner-form sign $-1$. Combined with the geometric transfer sign, Weyl integration produces equality of traces.

At the real place, elliptic classes are rotations, the Weyl factor is $2|\sin\theta|$, and the weight-$k$ cuspidal projector has the finite-dimensional sine quotient as its elliptic orbital integral and zero split orbital integral. Hamilton quaternions supply the same compact character, while the discrete-series character carries the opposite sign. In parallel weight two, the entire identity reduces to the values $1$, $-1$, and $1$.

The resulting package is ready for local transfer: class matching, Haar measures, discriminants, regular orbital integrals, singular limits, compact-level algorithms, archimedean projectors, and local character identities have all been fixed in one compatible normalization. What remains beyond this book is to construct, for each required Hecke function, the partner whose finite formulas agree and thereby prove the corresponding fundamental lemma.
