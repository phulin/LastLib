# $p$-divisible Groups and Serre--Tate Theory

## Contents

- [1. Why an infinite torsion object controls deformation](#1-why-an-infinite-torsion-object-controls-deformation)
  - [1.1 The organizing principle](#11-the-organizing-principle)
  - [1.2 Conventions and hypotheses](#12-conventions-and-hypotheses)
  - [1.3 The package developed here](#13-the-package-developed-here)
- [2. Barsotti--Tate groups](#2-barsotti--tate-groups)
  - [2.1 Definition by exact divisibility](#21-definition-by-exact-divisibility)
  - [2.2 Height, dimension, and basic examples](#22-height-dimension-and-basic-examples)
  - [2.3 Kernels, quotients, duality, and Tate modules](#23-kernels-quotients-duality-and-tate-modules)
- [3. Connected and etale directions](#3-connected-and-etale-directions)
  - [3.1 Finite levels over a perfect field](#31-finite-levels-over-a-perfect-field)
  - [3.2 Passage to the divisible system](#32-passage-to-the-divisible-system)
  - [3.3 Lifting the decomposition over complete local bases](#33-lifting-the-decomposition-over-complete-local-bases)
- [4. Dieudonne modules and slopes](#4-dieudonne-modules-and-slopes)
  - [4.1 The contravariant infinite-level module](#41-the-contravariant-infinite-level-module)
  - [4.2 Isocrystals and the slope decomposition](#42-isocrystals-and-the-slope-decomposition)
  - [4.3 Geometry read from slopes](#43-geometry-read-from-slopes)
- [5. Ordinary $p$-divisible groups](#5-ordinary-p-divisible-groups)
  - [5.1 Equivalent criteria](#51-equivalent-criteria)
  - [5.2 Ordinary abelian varieties](#52-ordinary-abelian-varieties)
  - [5.3 Examples, forms, and nonsplitting](#53-examples-forms-and-nonsplitting)
- [6. Crystals and infinitesimal lifting](#6-crystals-and-infinitesimal-lifting)
  - [6.1 The Hodge filtration](#61-the-hodge-filtration)
  - [6.2 The Grothendieck--Messing lifting theorem](#62-the-grothendieck--messing-lifting-theorem)
  - [6.3 Tangent spaces and obstructions](#63-tangent-spaces-and-obstructions)
- [7. The Serre--Tate equivalence](#7-the-serre--tate-equivalence)
  - [7.1 Deformation groupoids](#71-deformation-groupoids)
  - [7.2 Equivalence for abelian schemes](#72-equivalence-for-abelian-schemes)
  - [7.3 Polarizations, endomorphisms, and level structure](#73-polarizations-endomorphisms-and-level-structure)
- [8. The ordinary extension problem](#8-the-ordinary-extension-problem)
  - [8.1 Rigidity of the two pure parts](#81-rigidity-of-the-two-pure-parts)
  - [8.2 Extensions as Kummer data](#82-extensions-as-kummer-data)
  - [8.3 The Serre--Tate pairing](#83-the-serre--tate-pairing)
- [9. Formal coordinates on the ordinary deformation space](#9-formal-coordinates-on-the-ordinary-deformation-space)
  - [9.1 The universal formal torus](#91-the-universal-formal-torus)
  - [9.2 Coordinates, tangent vectors, and change of basis](#92-coordinates-tangent-vectors-and-change-of-basis)
  - [9.3 Isogenies and homomorphism loci](#93-isogenies-and-homomorphism-loci)
- [10. The canonical lift](#10-the-canonical-lift)
  - [10.1 Construction and uniqueness](#101-construction-and-uniqueness)
  - [10.2 Lifting all endomorphisms](#102-lifting-all-endomorphisms)
  - [10.3 Frobenius and arithmetic characterizations](#103-frobenius-and-arithmetic-characterizations)
- [11. Polarized ordinary coordinates](#11-polarized-ordinary-coordinates)
  - [11.1 Duality of the coordinate pairing](#111-duality-of-the-coordinate-pairing)
  - [11.2 Symmetric coordinates for principal polarizations](#112-symmetric-coordinates-for-principal-polarizations)
  - [11.3 Nonprincipal polarizations and integrality](#113-nonprincipal-polarizations-and-integrality)
- [12. PEL structures](#12-pel-structures)
  - [12.1 Endomorphisms and Rosati adjoints](#121-endomorphisms-and-rosati-adjoints)
  - [12.2 The PEL formal subtorus](#122-the-pel-formal-subtorus)
  - [12.3 Determinant conditions and smoothness boundaries](#123-determinant-conditions-and-smoothness-boundaries)
- [13. Ordinary loci in families](#13-ordinary-loci-in-families)
  - [13.1 The Hasse map](#131-the-hasse-map)
  - [13.2 Openness and base change](#132-openness-and-base-change)
  - [13.3 Completed local rings at ordinary points](#133-completed-local-rings-at-ordinary-points)
- [14. Local loci used in potential modularity](#14-local-loci-used-in-potential-modularity)
  - [14.1 Ordinary PEL neighborhoods](#141-ordinary-pel-neighborhoods)
  - [14.2 Components, residue extensions, and density](#142-components-residue-extensions-and-density)
  - [14.3 What the local theorem does and does not say](#143-what-the-local-theorem-does-and-does-not-say)
- [15. Structural synthesis](#15-structural-synthesis)
  - [15.1 The complete theorem package](#151-the-complete-theorem-package)
  - [15.2 A convention and hypothesis ledger](#152-a-convention-and-hypothesis-ledger)
  - [15.3 Conclusion](#153-conclusion)

## 1. Why an infinite torsion object controls deformation

### 1.1 The organizing principle

An abelian scheme is proper, smooth, and nonlinear, whereas its kernels of multiplication by powers of a prime are finite and affine. It is therefore surprising that, in residue characteristic $p$, the tower

$$
A[p]\subset A[p^2]\subset A[p^3]\subset\cdots
$$

remembers every infinitesimal deformation of $A$. This is the Serre--Tate principle. It says that near a characteristic-$p$ fiber one may replace the deformation theory of an abelian scheme by the deformation theory of its $p$-power torsion. At an ordinary fiber the replacement becomes especially concrete: the connected and etale pieces lift uniquely, and all freedom lies in the extension between them. Kummer theory turns that extension into multiplicative formal coordinates.

There are three layers to this statement. First, the compatible torsion tower must be treated as one object, a $p$-divisible or Barsotti--Tate group. Second, crystalline Dieudonne theory must connect that group to a filtered linear object. Third, one must prove that the filtration controlling a lift of the $p$-divisible group is exactly the filtration controlling a lift of the abelian scheme. Only after these steps do the familiar parameters $q_{ij}$ acquire a canonical meaning.

The ordinary case is not merely a convenient example. It is the locus on which the Newton slopes are only $0$ and $1$, so the deformation space is a formal torus rather than a more complicated formal scheme. Polarizations impose symmetry on the torus, endomorphisms impose linear character relations, and PEL conditions select formal subtori. These facts provide the ordinary local neighborhoods used in moduli arguments.

### 1.2 Conventions and hypotheses

Fix a prime $p$. All group schemes are commutative. A finite group scheme is finite locally free unless explicitly qualified. We write

$$
\mathbf Q_p/\mathbf Z_p=\varinjlim_n\underline{\mathbf Z/p^n\mathbf Z},
\qquad
\mu_{p^\infty}=\varinjlim_n\mu_{p^n}.
$$

Dieudonne theory is **contravariant**. For a perfect field $k$ of characteristic $p$, put $W=W(k)$ and let $\sigma$ be Witt Frobenius. If $G$ is a $p$-divisible group, its module $D(G)$ has operators

$$
F(am)=\sigma(a)F(m),\qquad
V(am)=\sigma^{-1}(a)V(m),\qquad FV=VF=p.
$$

Thus $\mathbf Q_p/\mathbf Z_p$ has slope $0$ and $\mu_{p^\infty}$ has slope $1$. A homomorphism $G\to H$ induces $D(H)\to D(G)$. Cartier duality is denoted $G\mapsto G^D$. For an abelian scheme $A$, the associated group is $A[p^\infty]$, and the convention agrees with the contravariant crystal $H^1_{\mathrm{cris}}(A)$ developed earlier.

Statements about slopes are made over a perfect field. Statements about connected--etale lifting are made over a complete local ring, or level by level over an artinian local ring, with perfect residue field. The Serre--Tate theorem is stated for nilpotent thickenings on which $p$ is locally nilpotent and, by passage to inverse limits, for complete noetherian local $W$-algebras. Whenever divided powers are used directly in a lifting step, the ideal carries nilpotent divided powers compatible with those on $(p)$. For a general nilpotent thickening no such divided powers are silently assumed: one passes to its divided-power envelope and uses crystalline descent. This distinction is needed especially when the ideal contains $p$.

An **ordinary abelian scheme** in characteristic $p$ means one whose geometric fibers are ordinary. We do not use “ordinary” to mean that a Galois representation or an extension is split. This distinction will prevent several common errors.

Books 38, 54, 57, and 59 supply the exact prior foundations. In particular, multiplication kernels of an abelian scheme are finite locally free, polarizations give perfect torsion pairings in the principal case, first crystalline cohomology is a finite locally free contravariant crystal with its Hodge sequence, and finite-level Dieudonne theory identifies $D(A[p^n])$ with $H^1_{\mathrm{cris}}(A)/p^n$. The low-weight integral equivalence explains how compatible finite-flat levels and filtered lattices pass between one another. We shall recall every form needed below and prove the genuinely infinite-level and deformation assertions here.

### 1.3 The package developed here

The route is dictated by the geometry. Chapters 2--5 construct $p$-divisible groups, their connected--etale sequences, slopes, and ordinary criterion. Chapters 6--7 prove the infinitesimal lifting theorem and the Serre--Tate equivalence. Chapters 8--10 calculate the ordinary deformation functor and isolate the canonical lift. Chapters 11--12 incorporate polarizations and PEL endomorphisms. Chapters 13--14 prove openness of the ordinary locus and describe the resulting local moduli neighborhoods.

Every comparison keeps variance visible. The etale Tate module is covariant, the Dieudonne module is contravariant, and a Serre--Tate coordinate pairs the Tate module of the etale quotient with the Tate module of the etale quotient of the dual. This is why the coordinate module is a tensor of two lattices rather than an endomorphism ring chosen without duality.

## 2. Barsotti--Tate groups

### 2.1 Definition by exact divisibility

Finite group schemes killed by $p^n$ do not by themselves remember whether they extend coherently to higher levels. Exact divisibility is the condition that supplies this missing coherence.

A **$p$-divisible group** $G$ of height $h$ over a scheme $S$ is an fppf sheaf of abelian groups such that multiplication by $p$ is an epimorphism and, for every $n\geq1$,

$$
G[p^n]=\ker(p^n:G\to G)
$$

is represented by a finite locally free group scheme of rank $p^{nh}$. Equivalently, it is a system $(G_n,i_n)$ in which $G_n$ has rank $p^{nh}$, $i_n:G_n\hookrightarrow G_{n+1}$ identifies $G_n$ with $G_{n+1}[p^n]$, and multiplication by $p^n$ gives an exact sequence

$$
0\longrightarrow G_n\longrightarrow G_{n+m}
\xrightarrow{p^n}G_m\longrightarrow0. \tag{2.1}
$$

To see the equivalence, pass from a divisible sheaf to its kernels. Conversely, take the fppf colimit of the system. Exactness of (2.1) makes multiplication by $p$ locally surjective and identifies its kernels with the prescribed levels. The rank condition is stable under arbitrary base change, so $p$-divisibility is as well.

A morphism $G\to H$ is a compatible family $G[p^n]\to H[p^n]$. Compatibility at all levels is essential: unrelated maps at each level need not define a map of the colimit. An exact sequence of $p$-divisible groups means a sequence which is fppf exact, equivalently exact at every sufficiently large finite level. If the heights are $h',h,h''$, finite-level ranks in an exact sequence give

$$
h=h'+h''. \tag{2.2}
$$

There is a useful finite-level test for divisibility. Suppose groups $G_n$ of ranks $p^{nh}$ are supplied with closed immersions $G_n\subset G_{n+1}$ and multiplication maps $p:G_{n+1}\to G_n$. It is not enough that every $G_n$ be killed by $p^n$. One must check that $p:G_{n+1}\to G_n$ is faithfully flat and has kernel $G_1$. Once this holds, induction shows that $p^r:G_{n+r}\to G_n$ is faithfully flat with kernel $G_r$, which is (2.1). This test prevents a compatible-looking tower of subgroup schemes from being mistaken for a divisible system.

Truncation loses information. A finite group killed by $p^n$ may have the correct order without extending to level $n+1$; even a BT$_1$ satisfying the Frobenius--Verschiebung rank conditions need not determine a unique infinite group. The deformation theory below therefore uses the full crystal or the entire compatible tower, never one isolated torsion level.

### 2.2 Height, dimension, and basic examples

Height measures the logarithmic growth of the finite levels. Dimension measures the infinitesimal connected direction. Define

$$
\dim G=\operatorname{rank}_S\operatorname{Lie}(G[p^n])
$$

for any sufficiently large $n$; the Lie algebra is already stable at level one because the inclusion $G[p]\subset G[p^n]$ induces an isomorphism on tangent spaces. When the base is connected this rank is constant in the situations considered here. More intrinsically, $\omega_G=e^*\Omega^1_{G[p^n]/S}$ stabilizes, and $\dim G=\operatorname{rank}\omega_G$.

The two height-one models are

$$
(\mathbf Q_p/\mathbf Z_p)[p^n]=\underline{\mathbf Z/p^n\mathbf Z},
\qquad
\mu_{p^\infty}[p^n]=\mu_{p^n}.
$$

The first has dimension $0$ and is etale when $p$ is locally nilpotent; the second has dimension $1$. Cartier duality exchanges them. If $A/S$ is an abelian scheme of relative dimension $g$, Book 38 proves that $A[p^n]$ has rank $p^{2gn}$. Exactness of multiplication gives a $p$-divisible group

$$
A[p^\infty]
$$

of height $2g$ and dimension $g$. The formal completion $\widehat A$ at the identity is not the whole $p$-divisible group: in characteristic $p$ it detects the connected part, while the etale quotient is invisible to the formal completion.

Products add heights and dimensions. An isogeny of $p$-divisible groups is a homomorphism with finite locally free kernel; it preserves height and dimension after passing to an exact sequence. The zero group has height and dimension zero and causes no exception in the formulas.

### 2.3 Kernels, quotients, duality, and Tate modules

Cartier duality at finite levels is compatible with the transition maps, so

$$
G^D[p^n]=G[p^n]^D
$$

defines a $p$-divisible group of height $h$ and dimension $h-d$ when $G$ has dimension $d$. The dimension formula can be checked over a field by Dieudonne theory and then fiberwise: duality interchanges $F$ and $V$, so the codimension of the Hodge subspace becomes its dimension. For an abelian scheme,

$$
A[p^\infty]^D\simeq A^\vee[p^\infty]. \tag{2.3}
$$

A principal polarization therefore gives a self-duality of $A[p^\infty]$, and the finite-level Weil pairings combine into a perfect pairing with values in $\mu_{p^\infty}$.

For an etale $p$-divisible group $E$ over a connected base with geometric point $\bar s$, define its covariant Tate module

$$
T_pE=\varprojlim_n E[p^n](\bar s),
$$

where the transition is multiplication by $p$. It is a free $\mathbf Z_p$-module of rank $\operatorname{ht}E$ with continuous fundamental-group action. Conversely such a local system produces an etale $p$-divisible group. This is the finite-etale correspondence applied compatibly at all levels. We reserve $T_p$ for etale groups in characteristic $p$; geometric points of a connected group would erase its structure.

## 3. Connected and etale directions

### 3.1 Finite levels over a perfect field

The first structural operation is to separate the infinitesimal and locally constant directions. Let $k$ be perfect and $H/k$ a finite commutative group scheme. The identity component $H^0$ is a closed normal subgroup, and the quotient $H^{\mathrm{et}}=H/H^0$ is finite etale. Thus

$$
0\longrightarrow H^0\longrightarrow H
\longrightarrow H^{\mathrm{et}}\longrightarrow0. \tag{3.1}
$$

Perfectness is used because a finite reduced $k$-scheme is then etale. Formation of (3.1) commutes with perfect field extension. Any map from a connected finite scheme to an etale scheme is constant, so (3.1) is functorial and uniquely characterized by having connected kernel and maximal etale quotient.

For a finite $p$-group, Book 57 translates (3.1) into the Fitting decomposition for Frobenius on the contravariant Dieudonne module:

$$
D(H)=D(H)_{F\text{-inv}}\oplus D(H)_{F\text{-nil}}. \tag{3.2}
$$

Because the functor is contravariant, the first summand is the module of $H^{\mathrm{et}}$ and the second that of $H^0$. On a finite-length module, a sufficiently high power of $F$ has stable image and stable kernel; their intersection is zero and their lengths add, which proves (3.2). This proof also shows functoriality.

### 3.2 Passage to the divisible system

Apply (3.1) to every $G[p^n]$. Functoriality makes the connected subgroups compatible. The etale quotients are compatible because multiplication by $p$ respects connected components. Taking the colimit yields the canonical connected--etale sequence

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0. \tag{3.3}
$$

Both ends are $p$-divisible. To prove this rather than assume it, let the ranks of $G[p^n]^{\mathrm{et}}$ be $p^{e_n}$. Exactness of multiplication gives $e_{n+m}=e_n+e_m$, because a fiber of the etale quotient map has the rank of the preceding etale kernel. Hence $e_n=ne_1$. The connected ranks are then $p^{n(h-e_1)}$, and multiplication is fppf-surjective on both pieces. Thus $G^{\mathrm{et}}$ has height $e_1$ and $G^0$ height $h-e_1$.

Sequence (3.3) need not split over $k$. It does split over a perfect field when $G$ is ordinary; that stronger assertion will follow from the absence of slopes strictly between $0$ and $1$. For a general group, a connected local-local piece may carry nontrivial extensions internally.

Duality turns the etale quotient of $G$ into the multiplicative subgroup of $G^D$. Define

$$
G^{\mathrm{mult}}=((G^D)^{\mathrm{et}})^D.
$$

It is the maximal subgroup of multiplicative type. In particular, ordinary groups will have connected part equal to their multiplicative part; without ordinarity, connected does not imply multiplicative.

### 3.3 Lifting the decomposition over complete local bases

Let $R$ be a complete local ring with perfect residue field $k$ of characteristic $p$, and assume $p$ is topologically nilpotent. If $G/R$ is $p$-divisible, its etale special-fiber quotient has a unique etale lift: finite etale schemes over $R$ and over $k$ are equivalent because $(R,\mathfrak m)$ is henselian. At level $n$, the quotient map on the special fiber lifts uniquely to a map

$$
G[p^n]\longrightarrow E_n.
$$

One way to see existence is to lift the corresponding idempotent in the coordinate algebra of the maximal etale quotient; idempotents lift uniquely through nilpotent quotients, and completeness passes to the limit. The kernels are finite locally free by the fiberwise flatness criterion. Compatibility and uniqueness at adjacent levels give

$$
0\longrightarrow G^0\longrightarrow G\longrightarrow G^{\mathrm{et}}\longrightarrow0 \tag{3.4}
$$

over $R$. The etale quotient and the connected kernel commute with complete local base change.

The local and completeness hypotheses matter. Over an arbitrary characteristic-$p$ family, the height of the etale part can jump, so no global finite locally free quotient of constant rank need exist across different Newton strata. One first restricts to a locus where the rank is constant. This is exactly why openness of the ordinary locus must be proved before using a connected--etale sequence uniformly in a moduli family.

## 4. Dieudonne modules and slopes

### 4.1 The contravariant infinite-level module

For a $p$-divisible group $G/k$ over a perfect field, finite-level Dieudonne theory gives compatible modules $D(G[p^n])$. Define

$$
D(G)=\varprojlim_nD(G[p^n]). \tag{4.1}
$$

The comparison of compatible truncations proves

$$
D(G[p^n])\simeq D(G)/p^nD(G). \tag{4.2}
$$

Since the right sides have $W$-length $nh$, completeness and Nakayama show that $D(G)$ is free of rank $h$ over $W$. The operators $F,V$ pass to the limit and satisfy $FV=VF=p$. Conversely, a finite free $W$-module with such operators and with $F$ injective reconstructs every quotient modulo $p^n$ by finite Dieudonne theory; compatibility gives a $p$-divisible group. Thus infinite-level Dieudonne theory is an exact anti-equivalence.

The atomic calculations fix the normalization:

$$
\begin{array}{c|c|c}
G&D(G)&(F,V)\\ \hline
\mathbf Q_p/\mathbf Z_p&W&(\sigma,p\sigma^{-1})\\
\mu_{p^\infty}&W&(p\sigma,\sigma^{-1}).
\end{array} \tag{4.3}
$$

For an abelian variety $A/k$, Book 57 identifies

$$
D(A[p^\infty])\simeq H^1_{\mathrm{cris}}(A/W), \tag{4.4}
$$

compatibly with Frobenius, Verschiebung, duality, endomorphisms, and polarizations. This is the bridge from the torsion tower to the crystalline deformation theory used later.

### 4.2 Isocrystals and the slope decomposition

Put $K_0=W[1/p]$ and $N=D(G)[1/p]$. Since $V=pF^{-1}$, the rational object is a finite-dimensional $K_0$-space with bijective $\sigma$-semilinear $F$. Such an object is an **isocrystal**.

For coprime integers $0\leq a\leq b$, let $N_{a/b}$ be the $b$-dimensional cyclic isocrystal with basis $e_0,\ldots,e_{b-1}$ and

$$
Fe_i=e_{i+1}\ (i<b-1),\qquad Fe_{b-1}=p^ae_0. \tag{4.5}
$$

Its slope is $a/b$. After extending a perfect base field to an algebraic closure, every isocrystal is a direct sum of these cyclic objects, uniquely up to order. We recall the proof because slope conventions control the geometry. Regard $N$ as a module over the skew Laurent ring $K_0\{F,F^{-1}\}$ with $Fa=\sigma(a)F$. A cyclic-vector argument presents each simple quotient by a twisted polynomial. The Newton polygon of that polynomial factors it, after unramified scalar extension, into one-slope factors. For a one-slope factor, dividing the exponents by their common denominator and successively changing the cyclic vector reduces the relation to $F^b=p^a$. Distinct slopes have no extensions after inverting $p$: if $u$ is an off-diagonal extension map between slopes $\lambda<\mu$, repeated conjugation by $F$ multiplies its valuation by a quantity tending to $+\infty$, and the convergent geometric correction kills $u$. Induction gives the direct sum. The valuations of the determinants of $F^m$ recover the multiset of slopes, proving uniqueness.

The polygon with these slopes, repeated with multiplicity and arranged increasingly, is the **Newton polygon**. Because $D(G)$ is an integral lattice with

$$
pD(G)\subseteq F(D(G))\subseteq D(G)
$$

after interpreting semilinearity by $\sigma^*$, every slope lies in $[0,1]$. Indeed the first inclusion gives nonnegative slopes for $F$, while $V=pF^{-1}$ integral gives nonnegative slopes for $V$, hence slopes of $F$ at most one.

### 4.3 Geometry read from slopes

The slope-$0$ summand is the rational Dieudonne module of $G^{\mathrm{et}}$; the slope-$1$ summand is that of $G^{\mathrm{mult}}$. The remaining slopes belong to the local-local part. This follows first for the atomic objects (4.3). In general, the Fitting decomposition modulo $p^n$ passes to the slope decomposition after inversion, and the uniqueness of the latter identifies the factors.

One must distinguish the rational decomposition from an integral direct product. Every slope summand $N_\lambda\subset D(G)[1/p]$ is canonical, but the intersection $D(G)\cap N_\lambda$ need not be a direct summand whose sum is all of $D(G)$. The quotient of the sum of these intersections can have finite $p$-power index. Geometrically, the slope decomposition is therefore an isogeny decomposition in general. The endpoint pieces are exceptional: the maximal etale quotient and maximal multiplicative subgroup exist integrally. In the ordinary case the two endpoint lattices split integrally, as proved in §5.1.

If the slopes are $\lambda_1,\ldots,\lambda_h$, then

$$
\dim G=\sum_{i=1}^h\lambda_i. \tag{4.6}
$$

To prove (4.6), choose $r$ so that $F^r$ is linear over a common fixed coefficient field after scalar extension. The valuation of $\det F^r$ is $r\sum\lambda_i$. On the other hand, compare the lattice $D(G)$ with $F^rD(G)$. At each step the length of $D/F D$ equals $\dim G$: modulo $p$, $D/FD$ is the invariant-differential space. Additivity of lattice indices gives length $r\dim G$. Dividing by $r$ proves the formula.

Duality replaces every slope $\lambda$ by $1-\lambda$. Indeed the Dieudonne pairing has weight one, so

$$
\langle Fx,Fy\rangle=p\sigma\langle x,y\rangle.
$$

A principally polarized group therefore has a Newton polygon symmetric about slope $1/2$. These calculations also distinguish three notions that are sometimes conflated: connected means no slope $0$, multiplicative means every slope is $1$, and local-local means no slope $0$ or $1$.

## 5. Ordinary $p$-divisible groups

### 5.1 Equivalent criteria

Let $G/k$ have height $h$ and dimension $d$. It is **ordinary** if its slopes are

$$
\underbrace{0,\ldots,0}_{h-d},
\underbrace{1,\ldots,1}_{d}. \tag{5.1}
$$

The following forms make the definition usable.

**Theorem 5.1 (ordinary criteria).** For a $p$-divisible group $G$ over a perfect field, the following are equivalent:

1. its Newton slopes satisfy (5.1);
2. $\operatorname{ht}G^{\mathrm{et}}=h-d$;
3. $G^0=G^{\mathrm{mult}}$ has height $d$;
4. over an algebraic closure,

   $$
   0\to\mu_{p^\infty}^{,d}\to G
   \to(\mathbf Q_p/\mathbf Z_p)^{h-d}\to0;
   \tag{5.2}
   $$

5. $G[p]$ has $p^{h-d}$ geometric points.

**Proof.** The slope-$0$ multiplicity is the etale height and the slope-$1$ multiplicity is the multiplicative height. Formula (4.6) says that if the slope-$0$ multiplicity is $h-d$, the remaining $d$ slopes have sum $d$ and are at most one, so all are one. This proves $2\Rightarrow1$; the reverse and equivalence with $3$ follow from §4.3. Over an algebraically closed field, etale and multiplicative groups of fixed heights are the displayed constant and diagonalizable groups, giving $4$. Finally only the etale part contributes geometric points to $G[p]$, so their number is $p^{\operatorname{ht}G^{\mathrm{et}}}$. $\square$

The extension (5.2) splits over a perfect field. On Dieudonne modules it is an extension between the slope-$0$ and slope-$1$ integral lattices. Solve the off-diagonal Frobenius equation by the convergent series whose $n$th term gains $n$ powers of $p$; completeness of $W$ makes the correction integral. This produces an $F,V$-stable splitting. The splitting is canonical because there is no nonzero homomorphism between an etale and a connected $p$-divisible group. Over a thicker mixed-characteristic base the extension generally does not split; its failure to split is precisely the ordinary deformation parameter.

Here is the matrix calculation behind the convergence assertion. Choose the canonical etale submodule $M_0$ and a $W$-module lift of the slope-$1$ quotient $M_1$. In a semilinear block basis,

$$
F=\begin{pmatrix}U&C\\0&pW_1\end{pmatrix},
$$

where $U$ and $W_1$ are $\sigma$-linear units. Replacing the lift of $M_1$ by its graph under a map $Z:M_1\to M_0$ kills $C$ precisely when

$$
ZpW_1-U\sigma(Z)=C.
$$

After multiplying by $U^{-1}$ and iterating, $Z$ is a series in which the $n$th correction contains $p^n$. It converges $p$-adically and is unique. The equation for $V=pF^{-1}$ is then automatically block diagonal. This also shows why perfectness, which makes $\sigma$ invertible, enters the integral splitting.

### 5.2 Ordinary abelian varieties

For an abelian variety $A/k$ of dimension $g$, the group $A[p^\infty]$ has height $2g$ and dimension $g$. Thus ordinarity is equivalent to each of the following:

$$
\operatorname{rank}_{\mathbf Z_p}T_p(A[p^\infty]^{\mathrm{et}})=g,
\qquad
\#A[p](\bar k)=p^g,
$$

or invertibility of the Hasse--Witt operator on $H^1(A,\mathcal O_A)$. The last equivalence follows from the Hodge sequence and $\omega_A=\ker F=\operatorname{im}V$ modulo $p$: maximal etale rank means that $F$ has rank $g$ on the quotient, equivalently that the dual Verschiebung map on invariant differentials has nonzero determinant.

For an elliptic curve there are only two Newton polygons. The ordinary polygon has slopes $0,1$ and

$$
E[p^\infty]\simeq\mu_{p^\infty}\oplus\mathbf Q_p/\mathbf Z_p
$$

over a perfect field. The supersingular polygon has slopes $1/2,1/2$; its $p$-divisible group is connected and local-local. At finite level, counting geometric points distinguishes the cases, but it does not describe the supersingular group.

For dimension at least two, intermediate Newton polygons occur. A connected group can have slopes such as $1/3$ and $2/3$ and is then not multiplicative. Consequently the connected--etale decomposition alone does not detect ordinarity unless its heights are compared with the dimension.

### 5.3 Examples, forms, and nonsplitting

Over a nonalgebraically closed perfect field, the pure parts can be twisted. An etale group corresponds to a free $\mathbf Z_p$-module with continuous Galois action, and a multiplicative group is the dual of such an etale group. Thus (5.2) should be read after separable extension; over $k$ the intrinsic statement is

$$
0\to G^{\mathrm{mult}}\to G\to G^{\mathrm{et}}\to0.
$$

The special-fiber sequence nevertheless splits canonically over a perfect field as a sequence of $p$-divisible groups with its descent data.

Nonsplitting reappears over a deformation ring. For example, extensions of $\mathbf Q_p/\mathbf Z_p$ by $\mu_{p^\infty}$ over an artinian local $W(k)$-algebra are indexed by elements of $1+\mathfrak m$. Their special fibers are all split because $1+\mathfrak m$ maps to $1$, but distinct elements give distinct lifts. Hence “ordinary special fiber” fixes the two graded pieces and leaves the extension variable free.

Products preserve ordinarity because Newton slopes concatenate. Duals preserve it because $0$ and $1$ are exchanged. Isogenies preserve it because the rational isocrystal, hence its slopes, is unchanged. These elementary stability properties will allow ordinary loci to be described independently of a chosen polarization or isogeny representative.

## 6. Crystals and infinitesimal lifting

### 6.1 The Hodge filtration

Let $S_0\hookrightarrow S$ be a nilpotent divided-power thickening in characteristic $p$, and let $G_0/S_0$ be a $p$-divisible group. Its contravariant Dieudonne crystal $\mathbb D(G_0)$ evaluates on $S$ to a finite locally free module

$$
M=\mathbb D(G_0)(S).
$$

On $S_0$ there is a canonical exact Hodge sequence

$$
0\longrightarrow\omega_{G_0}
\longrightarrow M\otimes_{\mathcal O_S}\mathcal O_{S_0}
\longrightarrow\operatorname{Lie}(G_0^D)\longrightarrow0. \tag{6.1}
$$

For $G_0=A_0[p^\infty]$, comparison (4.4) identifies (6.1) with

$$
0\to\omega_{A_0}\to H^1_{\mathrm{dR}}(A_0/S_0)
\to\operatorname{Lie}(A_0^\vee)\to0.
$$

This agreement is the heart of Serre--Tate theory. It is not merely a rank coincidence: both sequences arise from the universal vector extension of the dual abelian scheme, so their inclusions and functorialities agree.

A lift $G/S$ supplies a direct summand

$$
\operatorname{Fil}^1_G=\omega_G\subset M \tag{6.2}
$$

lifting $\omega_{G_0}$. It has rank $d=\dim G_0$, and the quotient has rank $h-d$. Cartier duality identifies the orthogonal complement of $\operatorname{Fil}^1_G$ with the corresponding filtration for $G^D$. Under a principal quasi-polarization, the filtration is Lagrangian.

### 6.2 The Grothendieck--Messing lifting theorem

The filtration in (6.2) contains exactly the infinitesimal freedom.

**Theorem 6.1 (lifting by the Hodge filtration).** Let $S_0\hookrightarrow S$ be a nilpotent PD thickening on which $p$ is nilpotent. The groupoid of lifts of $G_0$ to $S$ is equivalent to the groupoid of direct summands $\operatorname{Fil}^1\subset\mathbb D(G_0)(S)$ lifting $\omega_{G_0}$. Morphisms lift exactly when the induced crystal map carries one filtration into the other.

**Proof strategy.** Work first over a square-zero PD ideal. A lift of each finite level is obtained by lifting the Hopf algebra and its divided-power logarithm; associativity makes the discrepancy a linear cocycle. The cocycle is measured by a map from invariant differentials to the Lie algebra of the dual, exactly the difference between two lifted filtrations. Compatibility in the level removes all other choices. General nilpotent thickenings follow by induction.

For the decisive square-zero calculation, write the ideal as $I$ and choose one lift $G$ locally. Any other lift has the same crystal $M$ by crystalline rigidity. Its Hodge summand is the graph of a unique map

$$
u:\omega_{G_0}\longrightarrow
\operatorname{Lie}(G_0^D)\otimes I. \tag{6.3}
$$

Conversely, alter the coproduct on a local Hopf presentation by the bilinear cocycle corresponding to $u$. The cocycle equation is precisely coassociativity modulo $I^2=0$; the counit and antipode equations follow from normalization at the identity. At level $p^n$, this produces a finite locally free lift, and the construction commutes with inclusion and multiplication because $u$ is defined on the stable Hodge sequence rather than on one level. The fppf-local constructions glue: two gluings differ by an infinitesimal automorphism, and crystalline rigidity identifies that automorphism with the unique correction preserving the graph.

A morphism induces a map of crystals. The same calculation says that its obstruction to lifting is the failure to preserve the two graphs; if they are preserved, the lift is unique. For a PD ideal with a finite nilpotence filtration, apply the square-zero result successively. Effectivity for an inverse system over a complete base follows because the finite Hopf algebras at each level are finite projective and complete. $\square$

The word “unique” for a lifted morphism is relative to a chosen lift on the closed fiber. It follows from the crystal, not from a claim that $p$-divisible groups have no automorphisms. Indeed $\mathbf Q_p/\mathbf Z_p$ has many automorphisms. If two lifts of the same closed-fiber morphism preserve the filtration, their difference has zero crystalline realization on the square-zero layer, and finite-level Dieudonne faithfulness makes the difference zero. This distinction becomes important when passing from a framed deformation functor to a moduli stack.

The theorem is compatible with duality, pairings, and coefficient actions because all three are morphisms of crystals. Thus a quasi-polarization lifts exactly when its alternating form makes the chosen filtration isotropic, and an endomorphism lifts exactly when the filtration is stable under its crystalline action.

### 6.3 Tangent spaces and obstructions

Take $S_0=\operatorname{Spec}k$ and $S=\operatorname{Spec}k[\epsilon]/(\epsilon^2)$. Formula (6.3) gives the tangent space

$$
t_G\simeq
\operatorname{Hom}_k(\omega_G,\operatorname{Lie}(G^D)). \tag{6.4}
$$

Its dimension is $d(h-d)$. The local Grassmannian of rank-$d$ direct summands is smooth, so the unrestricted deformation functor of a $p$-divisible group over a perfect field is formally smooth. Choosing bases gives a universal ring

$$
W(k)[[x_1,\ldots,x_{d(h-d)}]]. \tag{6.5}
$$

This is a statement about the deformation functor with a fixed identification of the special fiber. Automorphisms of $G$ act on the coordinates, so a coarse moduli quotient need not itself be a power-series space.

For a principally quasi-polarized group of height $2g$, the Hodge subspace is Lagrangian. First-order Lagrangian graphs correspond to symmetric bilinear forms, giving tangent dimension

$$
\frac{g(g+1)}2. \tag{6.6}
$$

At $p=2$, genuine alternation must be retained; skew-symmetry alone is insufficient. The Lagrangian Grassmannian is nevertheless smooth over $\mathbf Z$, so (6.6) remains valid for an actual perfect alternating form.

## 7. The Serre--Tate equivalence

### 7.1 Deformation groupoids

Let $R_0\twoheadleftarrow R$ be a nilpotent thickening with kernel $I$, with $p$ nilpotent on $R$. Fix an abelian scheme $A_0/R_0$. A deformation is a pair $(A,\alpha)$, where $A/R$ is an abelian scheme and $\alpha:A\otimes_RR_0\simeq A_0$. Isomorphisms must respect $\alpha$. Define deformations of $G_0=A_0[p^\infty]$ similarly.

Taking multiplication kernels gives a functor

$$
\mathrm{Def}_{A_0}(R)\longrightarrow
\mathrm{Def}_{G_0}(R),\qquad A\longmapsto A[p^\infty]. \tag{7.1}
$$

The use of groupoids matters: an automorphism which is the identity on the special fiber must be shown to be the identity, rather than silently discarded. Rigidity of homomorphisms of abelian schemes and Theorem 6.1 provide this control.

### 7.2 Equivalence for abelian schemes

**Theorem 7.1 (Serre--Tate).** Under the hypotheses above, (7.1) is an equivalence of groupoids. The equivalence is functorial in the thickening and in $A_0$. It remains true over a complete noetherian local $W(k)$-algebra after interpreting a deformation as a compatible system over its artinian quotients.

**Proof strategy.** Both deformation problems are controlled by the same crystal and the same Hodge direct summand. This proves the assertion across square-zero thickenings. Induction gives nilpotent thickenings, and formal effectivity gives the complete case.

Evaluate $H^1_{\mathrm{cris}}(A_0)$ on $R$. Book 54 and the torsion comparison identify it with $\mathbb D(G_0)(R)$, including the Hodge submodule. The infinitesimal deformation theorem for an abelian scheme says that its lifts across a PD square-zero thickening are classified by direct-summand lifts of

$$
\omega_{A_0}\subset H^1_{\mathrm{dR}}(A_0/R_0). \tag{7.2}
$$

This follows by deforming the universal vector extension of $A_0^\vee$: a lifted Hodge summand determines the lifted extension, and the theorem of the cube reconstructs the group law. Proper smooth effectivity reconstructs the abelian scheme. By Theorem 6.1, the same direct summands classify lifts of $G_0$. Under comparison, the maps from both lift sets to the Grassmannian are identical. Hence (7.1) is essentially surjective and fully faithful over a square-zero step.

If the nilpotent thickening has no compatible divided powers, form its finite divided-power envelope at each nilpotence stage. The two lifting problems over the envelope are equivalent by the argument just given. Their descent data over the two projections to the divided-power envelope of the self-product are also identified, because morphisms are identified by preservation of the same Hodge filtration. Crystalline descent is effective for the finite locally free torsion levels and for proper smooth abelian schemes. The descended equivalence is independent of the chosen presentation of the envelope. This proves the arbitrary nilpotent case without putting nonexistent divided powers on the original ideal.

For a complete ring $R$, apply the nilpotent result to $R/\mathfrak m^n$. A compatible formal abelian scheme is algebraizable: a relatively ample cubical line bundle on the special fiber has a positive tensor power lifting compatibly, and formal GAGA algebraizes the proper formal scheme and its group law. The finite levels of the algebraized group are the prescribed finite levels by uniqueness over every quotient. This proves the complete case. $\square$

Full faithfulness can also be seen directly. Given a morphism of the deformed $p$-divisible groups, its crystal map preserves the Hodge filtrations. The abelian lifting theorem therefore produces a morphism of the abelian schemes across each square-zero layer. Rigidity of morphisms from a proper connected group to an abelian scheme makes these lifts unique and compatible. Conversely a morphism of abelian schemes plainly induces the morphism on every multiplication kernel. Thus no morphism is gained or lost when the infinite torsion tower replaces the abelian scheme.

The theorem does not say that an abstract $p$-divisible group over $R$ is globally the torsion of an abelian scheme. It says that a deformation of one already arising from $A_0$ arises uniquely in the formal neighborhood of $A_0$.

### 7.3 Polarizations, endomorphisms, and level structure

Let $\lambda_0:A_0\to A_0^\vee$ be a polarization. It induces a quasi-polarization

$$
\lambda_0[p^\infty]:G_0\longrightarrow G_0^D.
$$

Under Theorem 7.1, a lift of $A_0$ carries a lift of $\lambda_0$ if and only if the corresponding $p$-divisible group carries a lift of this quasi-polarization. Indeed homomorphisms lift exactly when their crystal maps preserve the Hodge filtration, and positivity is open and already holds on the nilpotent closed fiber. If the degree of $\lambda_0$ is prime to $p$, its $p$-divisible quasi-polarization is an isomorphism; if the degree is divisible by $p$, one must retain the actual isogeny and may not replace it by a perfect integral form.

Likewise an action $\iota_0:\mathcal O\to\operatorname{End}(A_0)$ lifts exactly when the induced action on $G_0$ lifts. A prime-to-$p$ level structure is finite etale and therefore lifts uniquely over a henselian nilpotent thickening. Thus it contributes no infinitesimal coordinate. A $p$-power level structure is not rigid and must be included as structure on the $p$-divisible group.

Consequently the Serre--Tate equivalence respects the full PEL deformation problem: endomorphisms, a polarization with its Rosati involution, and prime-to-$p$ level data. The determinant condition is an additional condition on the Hodge summand; it is not automatic from the underlying $p$-divisible group with endomorphisms.

## 8. The ordinary extension problem

### 8.1 Rigidity of the two pure parts

Let $k$ be perfect, let $R$ be an artinian local $W(k)$-algebra with residue field $k$, and let $G_0/k$ be ordinary. Write

$$
0\longrightarrow M_0\longrightarrow G_0
\longrightarrow E_0\longrightarrow0, \tag{8.1}
$$

where $M_0=G_0^{\mathrm{mult}}$ and $E_0=G_0^{\mathrm{et}}$. The special-fiber sequence is canonically split, but a deformation need not be.

The etale group $E_0$ has a unique lift $E/R$, because finite etale groups lift uniquely over a henselian nilpotent pair at every level. The multiplicative group $M_0$ also has a unique lift: its Cartier dual is etale, lift the dual uniquely, and dualize back. Therefore every deformation $G/R$ has a canonical sequence

$$
0\longrightarrow M\longrightarrow G\longrightarrow E\longrightarrow0, \tag{8.2}
$$

with fixed ends. Conversely any extension (8.2) is a $p$-divisible group: at level $n$ it is an extension of finite locally free groups of ranks $p^{nd}$ and $p^{n(h-d)}$, multiplication is locally surjective, and the ranks have the required product.

Thus the ordinary deformation functor is the extension functor

$$
\operatorname{Ext}^1_{p\text{-div}/R}(E,M) \tag{8.3}
$$

with the condition that the extension reduce to the split special fiber. The apparent nonlinear deformation problem has been reduced to calculating one Ext group.

### 8.2 Extensions as Kummer data

We begin with one etale generator. An extension

$$
0\to\mu_{p^\infty}\to G\to\mathbf Q_p/\mathbf Z_p\to0
$$

is determined by the compatible pullbacks along $p^{-n}\mathbf Z/\mathbf Z\subset\mathbf Q_p/\mathbf Z_p$. Choosing a lift of $p^{-n}$ produces a $\mu_{p^n}$-torsor. By the fppf Kummer sequence

$$
1\to\mu_{p^n}\to\mathbf G_m\xrightarrow{p^n}\mathbf G_m\to1,
$$

such a torsor over the local ring $R$ is represented by a unit modulo $p^n$th powers. Compatibility in $n$ is represented by one element of the formal multiplicative group

$$
\widehat{\mathbf G}_m(R)=1+\mathfrak m_R. \tag{8.4}
$$

The special fiber is split exactly because this unit is congruent to $1$. Baer sum of extensions multiplies the units.

For precision, the compatible Kummer map is

$$
\widehat{\mathbf G}_m(R)\longrightarrow
\varprojlim_n H^1_{\mathrm{fppf}}(R,\mu_{p^n}). \tag{8.5}
$$

It is injective on deformations with a fixed special-fiber trivialization: if $q$ has compatible $p^n$th roots congruent to $1$, nilpotence and successive comparison modulo powers of $\mathfrak m_R$ force $q=1$. It is surjective because a compatible system of Kummer classes can be represented successively by units $q_n$; multiplying $q_{n+1}$ by a $p^n$th power adjusts it to $q_n$, and artinian completeness produces one $q\in1+\mathfrak m_R$. Hence (8.5) identifies the framed extension group with $\widehat{\mathbf G}_m(R)$.

The construction can be made without choices by using the one-motive $[\mathbf Z\xrightarrow{1\mapsto q}\mathbf G_m]$. Its $p^n$-torsion consists fppf-locally of pairs $(a,z)$ with $a\in\mathbf Z/p^n\mathbf Z$ and $z^{p^n}=q^a$. It fits into

$$
0\to\mu_{p^n}\to M_q[p^n]\to
\mathbf Z/p^n\mathbf Z\to0. \tag{8.5a}
$$

Multiplication carries the level $n+1$ sequence to level $n$, so the colimit is a $p$-divisible group. Replacing $q$ by $qq'$ gives the Baer sum. Conversely, pull an extension back along $1/p^n$ and read its Kummer torsor; compatibility reconstructs $q$. This proves both directions of the rank-one classification and shows explicitly why the parameter law is multiplicative.

For general pure parts, set

$$
X=T_pE_0,\qquad Y=T_p(M_0^D). \tag{8.6}
$$

These are free $\mathbf Z_p$-modules, with descent action if $k$ is not algebraically closed. Since

$$
M\simeq\underline{\operatorname{Hom}}_{\mathbf Z_p}(Y,\mu_{p^\infty}),
$$

additivity in the etale source and multiplicative target gives

$$
\operatorname{Def}_{G_0}(R)\simeq
\operatorname{Hom}_{\mathbf Z_p}
(X\otimes_{\mathbf Z_p}Y,\widehat{\mathbf G}_m(R)). \tag{8.7}
$$

Over a nonalgebraically closed $k$, the homomorphisms in (8.7) must respect the semilinear descent data. This is the intrinsic form of the Kummer calculation.

### 8.3 The Serre--Tate pairing

Now take $G_0=A_0[p^\infty]$ for an ordinary abelian variety. The multiplicative part of $G_0$ is dual to the etale part of $G_0^D=A_0^\vee[p^\infty]$. Put

$$
X=T_p(A_0[p^\infty]^{\mathrm{et}}),\qquad
Y=T_p(A_0^\vee[p^\infty]^{\mathrm{et}}). \tag{8.8}
$$

The homomorphism in (8.7) can be written as a bilinear pairing

$$
q_A:X\times Y\longrightarrow\widehat{\mathbf G}_m(R), \tag{8.9}
$$

called the **Serre--Tate pairing**. It is multiplicative in each variable:

$$
q_A(x+x',y)=q_A(x,y)q_A(x',y),
\qquad
q_A(x,y+y')=q_A(x,y)q_A(x,y').
$$

The value is not an element of the residue field and is not a Weil pairing. It is a Kummer extension parameter congruent to $1$ modulo the maximal ideal. Its two arguments come from the etale Tate modules of $A_0$ and its dual, not from two arbitrary copies of the same lattice.

**Theorem 8.1 (ordinary Serre--Tate classification).** The assignment $A\mapsto q_A$ gives a functorial bijection

$$
\mathrm{Def}_{A_0}(R)\simeq
\operatorname{Hom}_{\mathbf Z_p}
(X\otimes Y,\widehat{\mathbf G}_m(R)), \tag{8.10}
$$

with descent invariants understood over nonalgebraically closed $k$.

**Proof.** Theorem 7.1 identifies deformations of $A_0$ with deformations of $G_0$. Section 8.1 identifies the latter with extensions of its unique pure lifts. The Kummer calculation (8.7), followed by the duality identification (8.8), gives (8.10). Every step respects base change and Baer sum, proving functoriality. $\square$

## 9. Formal coordinates on the ordinary deformation space

### 9.1 The universal formal torus

Choose bases $x_1,\ldots,x_{h-d}$ of $X$ and $y_1,\ldots,y_d$ of $Y$. Put

$$
q_{ij}=q(x_i,y_j),\qquad t_{ij}=q_{ij}-1. \tag{9.1}
$$

Then (8.7) is represented by

$$
R_G=W(k)[[t_{ij}:1\leq i\leq h-d,
1\leq j\leq d]]. \tag{9.2}
$$

The group law is not addition of the $t_{ij}$ but

$$
t_{ij}\star t'_{ij}=t_{ij}+t'_{ij}+t_{ij}t'_{ij}, \tag{9.3}
$$

because $q_{ij}$ multiply. In basis-free language the deformation space is the formal torus

$$
\underline{\operatorname{Hom}}
(X\otimes Y,\widehat{\mathbf G}_m). \tag{9.4}
$$

Its dimension $d(h-d)$ agrees with the crystalline tangent calculation (6.4), providing an important check on the Kummer computation. For an ordinary abelian variety of dimension $g$, $h=2g$ and the unrestricted dimension is $g^2$.

Representability follows directly from the universal units $q_{ij}=1+t_{ij}$. Given an artinian local $W(k)$-algebra $R$, a continuous map from (9.2) to $R$ is exactly a choice of all $q_{ij}\in1+\mathfrak m_R$, hence by bilinearity a unique homomorphism $X\otimes Y\to\widehat{\mathbf G}_m(R)$. This identification respects small extensions and inverse limits. The power-series ring is therefore not obtained from a tangent-dimension guess; it represents the entire nonlinear functor.

### 9.2 Coordinates, tangent vectors, and change of basis

Modulo the square of the maximal ideal, multiplication in $1+\mathfrak m$ becomes addition. Thus

$$
d\log(q_{ij})=dt_{ij}
$$

at the origin, and the tangent space of (9.4) is

$$
\operatorname{Hom}_k
((X/pX)\otimes(Y/pY),k). \tag{9.5}
$$

The Hodge calculation identifies $X/pX$ dually with the appropriate etale quotient of the Dieudonne module and $Y/pY$ with the dual connected Hodge direction, carrying (9.5) to (6.4).

Coordinates depend on bases, but the formal torus does not. If $x'_a=\sum_i u_{ia}x_i$ and $y'_b=\sum_jv_{jb}y_j$, then

$$
q'_{ab}=\prod_{i,j}q_{ij}^{,u_{ia}v_{jb}}, \tag{9.6}
$$

where $z\mapsto z^c$ for $c\in\mathbf Z_p$ is defined on the formal group by the compatible binomial power series. Consequently a linear change of Tate basis becomes a monomial change of multiplicative coordinates. Treating the $t_{ij}$ as linearly transforming coordinates beyond first order would lose the formal group law.

For an ordinary elliptic curve, $X$ and $Y$ both have rank one. After choosing generators, the entire deformation is one unit

$$
q_{\mathrm{ST}}\in1+\mathfrak m_R,
$$

and the universal ring is $W(k)[[q_{\mathrm{ST}}-1]]$. This parameter should not be confused with the Tate-curve parameter of a curve with split multiplicative reduction. The Tate parameter measures degeneration near a cusp in characteristic zero; the Serre--Tate parameter measures the extension of the connected and etale parts near a smooth ordinary characteristic-$p$ elliptic curve. They live in different formal neighborhoods even though both are multiplicative coordinates.

### 9.3 Isogenies and homomorphism loci

Let $A$ and $B$ be ordinary deformations of $A_0$ and $B_0$, and let $f_0:A_0\to B_0$ be a homomorphism. Denote its maps on etale Tate modules by

$$
f_X:X_A\to X_B,
\qquad
f_Y^\vee:Y_B\to Y_A.
$$

**Proposition 9.1 (lifting a homomorphism).** The map $f_0$ lifts to $f:A\to B$ if and only if

$$
q_A(x,f_Y^\vee y)=q_B(f_Xx,y)
\quad\text{for all }x\in X_A, y\in Y_B. \tag{9.7}
$$

If it lifts, it lifts uniquely.

**Proof.** A morphism of extensions must commute with their etale quotients and multiplicative subgroups. Pull the extension for $B$ back along $f_X$ and push the extension for $A$ out along the dual multiplicative map. The two resulting Kummer classes are respectively the right and left sides of (9.7). Equality is therefore necessary and sufficient for a morphism of $p$-divisible groups. Serre--Tate full faithfulness then gives the unique homomorphism of abelian schemes. $\square$

The homomorphism locus is consequently a closed formal subtorus cut out by character equations. Isogenies cause no denominator problem in (9.7), because the maps on Tate lattices are integral. Replacing an isogeny by its rational inverse would introduce denominators and is not legitimate on the integral formal torus.

## 10. The canonical lift

### 10.1 Construction and uniqueness

The identity element of a formal torus is distinguished independently of coordinates. This produces the canonical lift.

**Definition 10.1.** The **canonical lift** $A^{\mathrm{can}}/W(k)$ of an ordinary abelian variety $A_0/k$ is the deformation whose Serre--Tate pairing is identically $1$:

$$
q_{A^{\mathrm{can}}}(x,y)=1
\quad\text{for every }x\in X, y\in Y. \tag{10.1}
$$

To construct it, take at every artinian Witt level the split extension of the unique etale and multiplicative lifts. These extensions are compatible under reduction. The Serre--Tate equivalence gives compatible abelian schemes, and formal effectivity algebraizes them over $W(k)$. Uniqueness follows from (8.10): there is only one identity point.

If $k$ is not algebraically closed, the identity pairing is invariant under descent, so the canonical lift is defined over $W(k)$ without choosing a splitting basis. After any perfect extension $k'/k$,

$$
A^{\mathrm{can}}\otimes_{W(k)}W(k')
\simeq(A_0\otimes_kk')^{\mathrm{can}}. \tag{10.2}
$$

### 10.2 Lifting all endomorphisms

Set $A=B$ in (9.7). An endomorphism $f_0$ lifts to a deformation with pairing $q$ precisely when

$$
q(f_Xx,y)=q(x,f_Y^\vee y). \tag{10.3}
$$

For $q=1$, the equation is automatic.

**Theorem 10.2.** Every endomorphism of $A_0$ lifts uniquely to $A^{\mathrm{can}}$. More generally, every homomorphism between ordinary special fibers lifts uniquely between their canonical lifts. Composition and identities are preserved, so

$$
\operatorname{Hom}_k(A_0,B_0)
\xrightarrow{\sim}
\operatorname{Hom}_{W(k)}(A_0^{\mathrm{can}},B_0^{\mathrm{can}}). \tag{10.4}
$$

**Proof.** Both sides of (9.7) equal $1$ for canonical pairings, so the homomorphism lifts. Rigidity gives uniqueness. Reducing a characteristic-zero homomorphism gives the inverse map, proving bijectivity. $\square$

This property often characterizes the canonical lift among deformations, but one must state enough endomorphisms. A generic ordinary abelian variety may have endomorphism ring $\mathbf Z$, and multiplication maps lift over every deformation. “All scalar endomorphisms lift” therefore does not distinguish the identity point. The universal characterization is the split $p$-divisible extension, or equivalently (10.1).

### 10.3 Frobenius and arithmetic characterizations

Assume $k=\mathbf F_q$ with $q=p^r$. The relative $q$-power Frobenius of $A_0$ acts on the etale Tate lattice by a unit operator and on the dual etale lattice in the corresponding dual fashion. Since the canonical pairing is $1$, equation (9.7) holds, so Frobenius lifts uniquely to an endomorphism

$$
\widetilde\pi:A^{\mathrm{can}}\to A^{\mathrm{can}}. \tag{10.5}
$$

Conversely, suppose a deformation admits a lift of an endomorphism whose actions on the two slope parts have $p$-adic valuations $0$ and $r$, as Frobenius does. Equation (10.3) forces a coordinate $q$ to satisfy both a unit-weight and a $p^r$-weight relation. Iterating and using $q\in1+\mathfrak m$ gives $q=1$: in each artinian quotient, the relation drives $q-1$ into arbitrarily high powers of the nilpotent ideal. Thus a genuine Frobenius lift characterizes the canonical point.

This argument is integral. Looking only at the rational isocrystal would not distinguish the deformations, because all ordinary deformations have the same two rational slope pieces; the extension is encoded in the integral formal coordinate.

## 11. Polarized ordinary coordinates

### 11.1 Duality of the coordinate pairing

Let $A/R$ be an ordinary deformation and $A^\vee/R$ its dual. The dual extension reverses source and target. The Kummer construction therefore gives

$$
q_{A^\vee}(y,x)=q_A(x,y). \tag{11.1}
$$

No inverse appears with the conventions used here: Cartier duality exchanges the extension arguments, while the evaluation pairing $\mu_{p^n}\times\mathbf Z/p^n\to\mu_{p^n}$ retains its order. One may obtain an inverse under a convention using the alternating commutator as the coordinate itself; (11.1) fixes our normalization.

At finite level this can be checked on (8.5a). Cartier duality interchanges the character $a$ and the Kummer root $z$; evaluation sends their commutator to the same power of $q$, with the arguments transposed. Since the finite-level identifications commute with multiplication by $p$, the equality persists in the inverse limit. This finite calculation rules out a hidden sign or inverse.

If $f:A\to B$, formula (9.7) is exactly the functoriality of (11.1). This compatibility shows that duality on deformation spaces is the transpose map between the character lattices $X_A\otimes Y_A$ and $X_{A^\vee}\otimes Y_{A^\vee}$.

### 11.2 Symmetric coordinates for principal polarizations

Let $\lambda_0:A_0\xrightarrow\sim A_0^\vee$ be a principal polarization. It identifies

$$
Y\xrightarrow{\sim}X
$$

after using the etale part of $\lambda_0$. We write the resulting coordinate as $q(x,x')$. The polarization lifts precisely when it is a homomorphism from the deformation to its dual. Equations (9.7) and (11.1) give

$$
q(x,x')=q(x',x). \tag{11.2}
$$

Thus the principally polarized ordinary deformation functor is

$$
\underline{\operatorname{Hom}}
(\operatorname{Sym}^2_{\mathbf Z_p}X,
\widehat{\mathbf G}_m). \tag{11.3}
$$

For a basis $x_1,\ldots,x_g$, it has coordinates $q_{ij}=q_{ji}$ and universal ring

$$
W(k)[[t_{ij}:1\leq i\leq j\leq g]], \tag{11.4}
$$

of dimension $g(g+1)/2$. This agrees with the Lagrangian tangent calculation (6.6).

**Proof of sufficiency in (11.2).** Symmetry makes the Kummer class of the extension equal to that of its dual pulled back through $\lambda_0$. Hence $\lambda_0$ lifts as a self-dual isogeny of $p$-divisible groups. Serre--Tate gives a lift $\lambda:A\to A^\vee$. Its special fiber is a polarization; the locus on which the inducing line bundle is ample is open, and a nilpotent thickening has the same underlying topological space. Therefore $\lambda$ is a polarization. Principality follows because its kernel has empty special fiber and is finite locally free. $\square$

### 11.3 Nonprincipal polarizations and integrality

Suppose $\lambda_0$ has degree divisible by $p$. Its map on etale Tate modules need not be an isomorphism, so one cannot identify $X$ and $Y$ integrally. The correct lifting condition remains

$$
q_A(x,\lambda_Y y)
=q_{A^\vee}(\lambda_Xx,y)
=q_A(y,\lambda_Xx), \tag{11.5}
$$

where $x,y\in X_A$, $\lambda_X:X_A\to X_{A^\vee}=Y_A$, and $\lambda_Y:Y_{A^\vee}=X_A\to Y_A$ are the integral maps appearing on the two arguments. The first equality is (9.7), and the second is (11.1). After inverting $p$ this may be rewritten as symmetry on a rational lattice, but that rational equation can miss integral character relations.

For degree prime to $p$, $\lambda_0$ induces an isomorphism on the $p$-divisible group and the principal calculation applies to its perfect $p$-adic pairing, even if the global polarization is not principal. For degree divisible by $p$, the polarized deformation space is still the closed formal subgroup cut out by (11.5), but it need not have the same smooth symmetric-torus description. This distinction matches the crystalline warning that a nonprincipal polarization supplies a map $M^*\to M$, not necessarily a unimodular form.

## 12. PEL structures

### 12.1 Endomorphisms and Rosati adjoints

Let $\mathcal O$ be a finite free $\mathbf Z$-algebra acting on a principally polarized ordinary abelian variety $(A_0,\lambda_0)$, and suppose the Rosati involution restricts to $a\mapsto a^\dagger$ on $\mathcal O$. On the etale Tate lattice $X$, the action is covariant. The dual action on $Y$, transported to $X$ through $\lambda_0$, is the adjoint action $a^\dagger$.

By Proposition 9.1, the endomorphism $a$ lifts exactly when

$$
q(ax,y)=q(x,a^\dagger y) \tag{12.1}
$$

for every $x,y\in X$. Requiring (12.1) for a set of ring generators requires it for all of $\mathcal O$, because multiplication and addition of lifted endomorphisms are unique. Together with symmetry, these are the defining equations of the PEL deformation locus.

The order of the adjoint in (12.1) is forced by the polarization identity

$$
\lambda_0a=a^{\vee}\lambda_0
\quad\Longleftrightarrow\quad a^\dagger=a
$$

in the self-adjoint case, and more generally by $a^\dagger=\lambda_0^{-1}a^\vee\lambda_0$. Replacing $a^\dagger$ with $a$ without a self-adjoint hypothesis gives the wrong PEL locus.

### 12.2 The PEL formal subtorus

Let

$$
L_{\mathrm{PEL}}=
\operatorname{Sym}^2X\Big/
\left\langle ax\otimes y-x\otimes a^\dagger y
\right\rangle_{a,x,y}. \tag{12.2}
$$

Then the functor of ordinary deformations carrying the polarization and $\mathcal O$-action is

$$
\underline{\operatorname{Hom}}_{\mathbf Z_p}
(L_{\mathrm{PEL}},\widehat{\mathbf G}_m). \tag{12.3}
$$

If $L_{\mathrm{PEL}}$ is finite free, this is a smooth formal torus of dimension $\operatorname{rank}L_{\mathrm{PEL}}$. If it has torsion, (12.3) can contain a finite non-smooth diagonalizable factor at $p$; smoothness may not be inferred merely by counting rational dimensions.

**Proof.** A character of the unrestricted polarized torus is an element of $\operatorname{Sym}^2X$. Equation (12.1) says that the characters $ax\otimes y$ and $x\otimes a^\dagger y$ have equal values. Hence the character map factors exactly through the quotient (12.2). Conversely any homomorphism out of that quotient defines a symmetric pairing satisfying (12.1), so Chapters 7 and 11 reconstruct the PEL deformation. $\square$

This character-lattice description is invariant under choice of basis and under unramified extension of the residue field. It also makes products and idempotent decompositions transparent: self-adjoint idempotents give orthogonal factors, while idempotents exchanged by Rosati give mutually dual isotropic factors.

Two standard calculations illustrate the quotient lattice. Suppose first that $\mathcal O_p$ is the ring of integers in an unramified extension of $\mathbf Q_p$, fixed by Rosati, and that $X$ is locally free of rank one over $\mathcal O_p$. After an unramified scalar extension,

$$
\mathcal O_p\otimes_{\mathbf Z_p}W'
\simeq\prod_{\tau}W'.
$$

Let $e_\tau$ be the resulting idempotents. Relation (12.1) with $a=e_\tau$ makes distinct eigenspaces orthogonal. The surviving coordinates are the diagonal pairings on $e_\tau X$, one for each embedding $\tau$. Descent packages them into the formal torus whose character lattice is the corresponding rank-one $\mathcal O_p$-module. This is the ordinary Hilbert--Blumenthal pattern: the endomorphism action reduces the $g(g+1)/2$ principally polarized coordinates to $g$ coordinates when $[\mathcal O_p:\mathbf Z_p]=g$ and $X$ has rank one over it.

For a split unitary pattern, let

$$
\mathcal O_p=\mathbf Z_p\times\mathbf Z_p,
\qquad e^\dagger=1-e.
$$

Write $X=eX\oplus(1-e)X$. Taking $a=e$ in (12.1) forces the pairings on $eX\times eX$ and on $(1-e)X\times(1-e)X$ to be trivial; only the cross-pairing survives. Symmetry identifies the two orders, so

$$
L_{\mathrm{PEL}}\simeq eX\otimes_{\mathbf Z_p}(1-e)X. \tag{12.4}
$$

If the two ranks are $r$ and $s$, the local dimension is $rs$. This is the linear-algebra source of the familiar unitary local dimension. Both examples use integral idempotents. A decomposition only after tensoring with $\mathbf Q_p$ would not justify either calculation.

### 12.3 Determinant conditions and smoothness boundaries

A PEL moduli problem also prescribes the characteristic polynomial of $a\in\mathcal O$ on $\operatorname{Lie}A$, or equivalently on the Hodge quotient. This **determinant condition** is not an extra equation on the Serre--Tate pairing once the ordinary special fiber and the connected-component signature are fixed and the relevant idempotents are integral: the ranks of the Hodge summands are locally constant over a nilpotent thickening, and their characteristic polynomials lift the prescribed ones.

In ramified coefficient situations, or when the integral order is not etale at $p$, a rational signature need not determine an integral direct summand. The local model can then impose additional equations and may fail to be smooth. The clean formal-torus statement therefore has the following exact safe form.

**Theorem 12.1 (ordinary PEL coordinates).** Suppose the PEL endomorphism order at $p$ acts on $X$ through a finite etale $\mathbf Z_p$-algebra, the polarization pairing is perfect at $p$, and the determinant condition selects an open-and-closed rank condition on integral idempotent factors. Then the completed PEL deformation space at an ordinary point is the smooth formal torus (12.3); its dimension is $\operatorname{rank}_{\mathbf Z_p}L_{\mathrm{PEL}}$.

**Proof.** Finite etaleness makes the idempotent decomposition integral and stable under every nilpotent lift. Perfectness gives the symmetric coordinate description. The determinant condition fixes only the ranks of the direct factors and hence selects connected components rather than adding infinitesimal equations. Finally the relations in (12.2) form a saturated direct summand: after the etale algebra splits unramifiedly into copies of $\mathbf Z_p$, they simply set pairings between incompatible eigenspaces to $1$ and identify adjoint pairs. Thus $L_{\mathrm{PEL}}$ is free, and (12.3) is a smooth formal torus. $\square$

The hypotheses are substantive. If the order is ramified, saturation requires a separate local-model theorem. If the polarization degree is divisible by $p$, §11.3 replaces the symmetric lattice. If $p=2$, one must use the genuine alternating PEL pairing rather than infer alternation from a sign.

## 13. Ordinary loci in families

### 13.1 The Hasse map

Coordinates describe the formal neighborhood once ordinarity is known. Moduli arguments also need ordinarity to persist on a Zariski-open neighborhood.

Let $A/S$ be an abelian scheme of relative dimension $g$ over an $\mathbf F_p$-scheme. Relative Verschiebung

$$
V:A^{(p)}\longrightarrow A
$$

induces on invariant differentials a map

$$
V^*:\omega_{A/S}\longrightarrow\omega_{A^{(p)}/S}
\simeq F_S^*\omega_{A/S}. \tag{13.1}
$$

Taking determinants gives the Hasse map

$$
\operatorname{Ha}(A):det\omega_{A/S}
\longrightarrow F_S^*\det\omega_{A/S}. \tag{13.2}
$$

After identifying $F_S^*L$ with $L^{\otimes p}$ for a line bundle $L$, this is a section of $(\det\omega)^{\otimes(p-1)}$. At a geometric point $s$, it is nonzero exactly when $V^*$ is invertible.

The construction is independent of any trivialization of $\det\omega$. On an open set where a generator $\eta$ is chosen, (13.2) reads $\eta\mapsto h\eta^{\otimes p}$ for a function $h$. On an overlap, replacing $\eta$ by $u\eta$ replaces $h$ by $u^{1-p}h$, so the vanishing locus is unchanged and the local functions glue to the stated line-bundle section.

**Proposition 13.1.** A geometric fiber $A_s$ is ordinary if and only if $\operatorname{Ha}(A)(s)\ne0$.

**Proof.** On the Hodge sequence for $D(A_s[p])$, the map induced by Verschiebung on $\omega_{A_s}$ is dual to Frobenius on $H^1(A_s,\mathcal O_{A_s})$. It is invertible exactly when Frobenius has rank $g$. By Theorem 5.1 this is equivalent to etale height $g$, hence to ordinarity. $\square$

For a general $p$-divisible group of height $h$ and dimension $d$, the same construction uses Verschiebung on $\omega_G$ and its determinant. Its nonvanishing detects multiplicative height $d$, equivalently ordinarity.

### 13.2 Openness and base change

The nonvanishing locus of a section of a line bundle is open. Proposition 13.1 therefore proves:

**Theorem 13.2 (openness of the ordinary locus).** For an abelian scheme, or a $p$-divisible group of constant height and dimension, over a locally noetherian characteristic-$p$ base, the set

$$
S^{\mathrm{ord}}=
\{s\in S:A_s\text{ is ordinary}\}
$$

is Zariski open. Its formation commutes with arbitrary base change.

The base-change assertion follows because invariant differentials, relative Verschiebung, determinants, and nonvanishing all commute with base change. No perfection assumption on the base is needed; ordinarity is tested after passing to geometric fibers.

This proof gives more than upper semicontinuity of $p$-rank. It supplies an actual equation for the complement. On a moduli space, the Hasse invariant is therefore a canonical local witness that an ordinary point has an ordinary neighborhood. For a PEL factor, partial Hasse determinants may be formed on integral idempotent summands; under the etale hypotheses of Theorem 12.1, simultaneous nonvanishing gives the PEL ordinary locus.

### 13.3 Completed local rings at ordinary points

Let $\mathscr M$ be a moduli scheme or Deligne--Mumford stack of abelian varieties with a rigidifying level structure, and let $x$ be an ordinary geometric point. Assume the moduli problem has no infinitesimal automorphisms at $x$, as happens after a sufficiently fine prime-to-$p$ level. The Serre--Tate equivalence identifies the completed local deformation functor with the appropriate $p$-divisible deformation functor.

Without a polarization,

$$
\widehat{\mathcal O}_{\mathscr M,x}
\simeq W(k)[[t_1,\ldots,t_{g^2}]]. \tag{13.3}
$$

For a principal polarization,

$$
\widehat{\mathcal O}_{\mathscr A_g,x}
\simeq W(k)[[t_1,\ldots,t_{g(g+1)/2}]]. \tag{13.4}
$$

For a safe unramified PEL datum, the number of variables is $\operatorname{rank}L_{\mathrm{PEL}}$.

These isomorphisms are noncanonical as power-series rings because they require bases. Canonically, the completions are formal tori with the character lattices already described. If the level does not remove automorphisms, the completed stack is the quotient of this formal torus by the finite stabilizer; its coarse completed local ring is the invariant ring and need not itself be regular.

## 14. Local loci used in potential modularity

### 14.1 Ordinary PEL neighborhoods

Potential-modularity constructions use moduli spaces with endomorphisms and polarizations to realize prescribed Galois data. Their local argument needs a nonempty smooth neighborhood in residue characteristic $p$, together with enough control to keep the desired component after extending the residue field.

Let $x$ be an ordinary point of an unramified PEL moduli problem satisfying Theorem 12.1. Then its completed local space is

$$
\widehat{\mathscr M}_x\simeq
\underline{\operatorname{Hom}}
(L_{\mathrm{PEL}},\widehat{\mathbf G}_m). \tag{14.1}
$$

Since the character lattice is free, this formal scheme is formally smooth over $W(k)$. The identity is the PEL canonical lift; every sufficiently small choice of parameters gives another lift. The ordinary locus contains the entire special-fiber formal neighborhood because every deformation in this formal neighborhood has ordinary special fiber and its pure parts remain etale and multiplicative.

If a local condition asks certain special-fiber endomorphisms to lift, equations (12.1) cut out a formal subtorus. If it asks for a prime-to-$p$ level structure, that structure lifts uniquely and adds no parameter. Thus many local conditions relevant to a moduli construction remain smooth character conditions rather than arbitrary nonlinear equations.

### 14.2 Components, residue extensions, and density

Unramified extension from $W(k)$ to $W(k')$ tensors the etale Tate lattices with unchanged character relations. Therefore (14.1) base changes to the corresponding formal torus at the extended point. Geometric connected components do not merge unexpectedly in the completed ordinary neighborhood: a formal torus over a complete local base has connected special fiber, while determinant rank conditions have already selected an open-and-closed component.

The generic fiber of a smooth formal torus has many algebraic points after finite extensions of the fraction field. Concretely, assign each $t_i$ an element of the maximal ideal of a finite extension; the resulting continuous map from the power-series ring gives a point. Conditions excluding finitely many proper subtori remain satisfiable because a nonzero Laurent character cannot vanish identically on an open polydisc. Hence the ordinary formal neighborhood supplies locally abundant characteristic-zero points.

This is the precise local input used in approximation arguments: nonemptiness comes from the canonical lift, smoothness from the free PEL character lattice, and room to avoid closed conditions from the positive-dimensional formal torus. A global theorem is still needed to satisfy conditions at several places simultaneously.

### 14.3 What the local theorem does and does not say

The local conclusions have exact boundaries.

First, openness of the ordinary locus does not assert that it is nonempty in every PEL moduli space. One must construct an ordinary special point compatible with the datum. Second, a smooth completed local ring does not imply that the whole integral model is smooth; singularities may occur at nonordinary points or on other components. Third, a rational endomorphism decomposition does not define an integral PEL subtorus unless the idempotents preserve the Tate lattice. Fourth, the existence of many local algebraic points is not a global approximation theorem.

Within those boundaries the conclusion is strong: once an ordinary point of an unramified PEL integral model exists, its ordinary local locus is open, has a canonical characteristic-zero point, and is controlled by explicit multiplicative coordinates compatible with polarization, endomorphisms, and unramified base change.

## 15. Structural synthesis

### 15.1 The complete theorem package

The constructions above establish the following reusable statement.

**Theorem 15.1 (the $p$-divisible and Serre--Tate package).** Let $k$ be a perfect field of characteristic $p$.

1. A $p$-divisible group $G/k$ of height $h$ is classified contravariantly by a free rank-$h$ Dieudonne module with $FV=VF=p$. Its connected, etale, and multiplicative parts correspond respectively to the positive-slope, slope-$0$, and slope-$1$ pieces.
2. Its Newton slopes lie in $[0,1]$, have sum $\dim G$, and duality sends $\lambda$ to $1-\lambda$.
3. The group is ordinary exactly when its slopes are $0^{h-d},1^d$, equivalently when its etale height is $h-d$ or its multiplicative height is $d$.
4. Across a nilpotent PD thickening, deformations of $G$ are classified by lifts of its Hodge direct summand in its Dieudonne crystal. The tangent space is

   $$
   \operatorname{Hom}(\omega_G,\operatorname{Lie}(G^D)).
   $$

5. If $G=A[p^\infty]$, this classification is identical to the infinitesimal classification of deformations of $A$. Consequently deformations of $A$ and of $G$ are equivalent, including polarizations, endomorphisms, and level structures in their correct forms.
6. If $A_0$ is ordinary, its deformation functor is the formal torus

   $$
   \underline{\operatorname{Hom}}
   (T_pA_0^{\mathrm{et}}\otimes
   T_pA_0^{\vee,\mathrm{et}},\widehat{\mathbf G}_m).
   $$

   Its identity is the canonical lift, characterized by the split $p$-divisible extension.
7. A principal polarization imposes symmetry, giving character lattice $\operatorname{Sym}^2T_pA_0^{\mathrm{et}}$. A PEL action imposes

   $$
   q(ax,y)=q(x,a^\dagger y).
   $$

   Under unramified integral hypotheses the quotient character lattice is free and the PEL deformation space is a smooth formal torus.
8. In a characteristic-$p$ family, nonvanishing of the Hasse determinant is equivalent to ordinarity. Hence the ordinary locus is open and stable under base change. At an ordinary unramified PEL point the completed local locus is the formal torus described above.

**Proof.** Parts 1--3 are Chapters 3--5. Part 4 is Theorem 6.1 and its tangent calculation. Part 5 is Theorem 7.1 and §7.3. Part 6 is Theorem 8.1 and Chapters 9--10. Part 7 is Chapters 11--12. Part 8 is Chapter 13, with the local interpretation of Chapter 14. $\square$

### 15.2 A convention and hypothesis ledger

The theory is compact only when its conventions are kept visible.

| Assertion | Exact convention or hypothesis | Error prevented |
|---|---|---|
| Dieudonne realization | contravariant; $FV=VF=p$ | reversing arrows or slopes |
| slope normalization | etale is $0$, multiplicative is $1$ | exchanging Newton endpoints |
| dimension formula | $\dim G=\sum\lambda_i$ | using the covariant complement |
| connected--etale sequence in families | perfect field, complete local base, or constant-rank stratum | claiming a global quotient across jumps |
| ordinary | maximal etale height, not split generic representation | confusing filtration with splitting |
| Hodge sequence | $0\to\omega_G\to\mathbb D(G)\to\operatorname{Lie}(G^D)\to0$ | putting the dual on the wrong term |
| infinitesimal lifting | nilpotent PD steps; complete case by limits | applying a crystal without a valid thickening |
| Serre--Tate equivalence | deformations of an existing $A_0$, not arbitrary groups | global algebraization overclaim |
| ordinary coordinate | $X\times Y$ with $Y=T_p(A_0^\vee)^{\mathrm{et}}$ | pairing two unjustified copies |
| coordinate group law | multiplication of $q$, not addition of $q-1$ | incorrect nonlinear basis change |
| dual coordinate | $q_{A^\vee}(y,x)=q_A(x,y)$ in our normalization | hidden inverse convention |
| principal polarization | perfect at $p$ and symmetric $q$ | treating nonprincipal forms as unimodular |
| PEL relation | $q(ax,y)=q(x,a^\dagger y)$ | omitting the Rosati adjoint |
| smooth PEL torus | etale order at $p$, saturated character quotient, integral determinant factors | rational dimension mistaken for smoothness |
| openness | Hasse determinant on a constant-rank family | unsupported Newton-stratum assertion |
| local potential-modularity input | an ordinary point already exists | inferring global nonemptiness from local theory |

The dependency chain is now closed in the precise forms used. Book 38 supplies finite locally free multiplication kernels, dual abelian schemes, the Poincare biextension, Weil pairings, and polarizations. Book 54 supplies finite locally free $H^1_{\mathrm{cris}}$, its Hodge sequence, Frobenius, duality, and the integral polarization form. Book 57 supplies the contravariant finite Dieudonne anti-equivalence, the connected--etale operator criteria, and the comparison

$$
D(A[p^n])\simeq H^1_{\mathrm{cris}}(A)/p^n.
$$

Book 59 supplies the compatibility of finite-flat levels with integral filtered lattices and confirms that ordinary and local-local types survive the allowed base changes and coefficient operations. What was not already present there has been proved here: passage to the infinite divisible object, its slope and ordinary structures, the Grothendieck--Messing lifting classification, the Serre--Tate equivalence, the Kummer coordinate calculation, the canonical lift, the PEL character quotient, and openness through the Hasse determinant. No classification over a ramified base or result about a later global moduli construction is used as a proof input.

### 15.3 Conclusion

A $p$-divisible group packages infinitely many finite-flat kernels into one exact object. Its contravariant Dieudonne module separates the etale slope $0$, the multiplicative slope $1$, and the intermediate local-local directions, while its Hodge filtration retains the integral information which the isocrystal forgets. In the ordinary case only the two endpoint slopes remain. The pure pieces then lift rigidly, so every deformation is an extension between them.

The Serre--Tate theorem identifies that extension problem with the deformation problem of the abelian scheme itself. Kummer theory turns extensions into a bilinear pairing valued in the formal multiplicative group. This produces canonical multiplicative coordinates, not merely a convenient choice of power-series variables. The identity coordinate gives the canonical lift; functoriality gives the exact equation for lifting homomorphisms; duality and polarization give symmetry; and a PEL action gives the Rosati-adjoint character relations.

Finally, the Hasse determinant makes ordinarity visible in families. Its nonvanishing defines an open locus, and at an ordinary unramified PEL point the completed local space is a smooth formal torus with an explicit integral character lattice. The resulting package supplies both the conceptual deformation equivalence and the concrete local coordinates needed in arithmetic moduli constructions, while keeping separate the hypotheses required for slopes, integral polarizations, PEL smoothness, and global existence.
