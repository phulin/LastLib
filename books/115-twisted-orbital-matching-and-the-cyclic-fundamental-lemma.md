# Twisted Orbital Matching and the Cyclic Fundamental Lemma

## Contents

- [Introduction](#introduction)
- [1. The local comparison problem](#1-the-local-comparison-problem)
  - [1.1 Why base change needs a geometric theorem](#11-why-base-change-needs-a-geometric-theorem)
  - [1.2 Standing notation and scope](#12-standing-notation-and-scope)
  - [1.3 The normalization ledger](#13-the-normalization-ledger)
  - [1.4 The three forms of the matching assertion](#14-the-three-forms-of-the-matching-assertion)
- [2. Norms and matching classes](#2-norms-and-matching-classes)
  - [2.1 Twisted classes and ordered norms](#21-twisted-classes-and-ordered-norms)
  - [2.2 The regular norm image](#22-the-regular-norm-image)
  - [2.3 Split local algebras](#23-split-local-algebras)
  - [2.4 Scalar norms and the quadratic exception](#24-scalar-norms-and-the-quadratic-exception)
- [3. Measures, discriminants, and transfer factors](#3-measures-discriminants-and-transfer-factors)
  - [3.1 Complementary quotient measures](#31-complementary-quotient-measures)
  - [3.2 Ordinary and twisted Weyl determinants](#32-ordinary-and-twisted-weyl-determinants)
  - [3.3 The base-change transfer factor](#33-the-base-change-transfer-factor)
  - [3.4 Measure changes and products](#34-measure-changes-and-products)
- [4. Twisted characters in the selected rank-two range](#4-twisted-characters-in-the-selected-rank-two-range)
  - [4.1 Normalizing the intertwiner](#41-normalizing-the-intertwiner)
  - [4.2 Principal and determinant characters](#42-principal-and-determinant-characters)
  - [4.3 Special representations](#43-special-representations)
  - [4.4 Dihedral supercuspidals](#44-dihedral-supercuspidals)
  - [4.5 The selected norm character identity](#45-the-selected-norm-character-identity)
- [5. Unramified integral geometry](#5-unramified-integral-geometry)
  - [5.1 Semilinear stable lattices](#51-semilinear-stable-lattices)
  - [5.2 Weighted lattice groupoids](#52-weighted-lattice-groupoids)
  - [5.3 Integral descent through congruence layers](#53-integral-descent-through-congruence-layers)
  - [5.4 The weighted descent theorem](#54-the-weighted-descent-theorem)
- [6. The unramified unit fundamental lemma](#6-the-unramified-unit-fundamental-lemma)
  - [6.1 Statement of the unit identity](#61-statement-of-the-unit-identity)
  - [6.2 Proof by weighted descent](#62-proof-by-weighted-descent)
  - [6.3 Vanishing outside the norm image](#63-vanishing-outside-the-norm-image)
  - [6.4 Boundary and residue-characteristic checks](#64-boundary-and-residue-characteristic-checks)
- [7. The spherical cyclic fundamental lemma](#7-the-spherical-cyclic-fundamental-lemma)
  - [7.1 The base-change homomorphism](#71-the-base-change-homomorphism)
  - [7.2 Galleries and Hecke correspondences](#72-galleries-and-hecke-correspondences)
  - [7.3 Proof of spherical matching](#73-proof-of-spherical-matching)
  - [7.4 Explicit rank-two formulas](#74-explicit-rank-two-formulas)
- [8. Regular transfer at ramified places](#8-regular-transfer-at-ramified-places)
  - [8.1 Why the unit statement changes](#81-why-the-unit-statement-changes)
  - [8.2 Twisted descent on a regular slice](#82-twisted-descent-on-a-regular-slice)
  - [8.3 Patching compact regular data](#83-patching-compact-regular-data)
  - [8.4 A complete regular transfer theorem](#84-a-complete-regular-transfer-theorem)
- [9. Ramified lattice matching](#9-ramified-lattice-matching)
  - [9.1 Ramification, depth, and fixed subtrees](#91-ramification-depth-and-fixed-subtrees)
  - [9.2 The finite triangular system](#92-the-finite-triangular-system)
  - [9.3 Tail recurrences near the scalar locus](#93-tail-recurrences-near-the-scalar-locus)
  - [9.4 The ramified invariant-level theorem](#94-the-ramified-invariant-level-theorem)
- [10. Iwahori and congruence matching](#10-iwahori-and-congruence-matching)
  - [10.1 Oriented edges and relative position](#101-oriented-edges-and-relative-position)
  - [10.2 The twisted Iwahori statement](#102-the-twisted-iwahori-statement)
  - [10.3 Segment stabilizers and $K_0$-level](#103-segment-stabilizers-and-k_0-level)
  - [10.4 Primitive endpoints and $K_1$-level](#104-primitive-endpoints-and-k_1-level)
- [11. Level-specific matching for selected representations](#11-level-specific-matching-for-selected-representations)
  - [11.1 Type functions and twisted traces](#111-type-functions-and-twisted-traces)
  - [11.2 Principal and special types](#112-principal-and-special-types)
  - [11.3 Depth-zero dihedral types](#113-depth-zero-dihedral-types)
  - [11.4 Tame positive-depth dihedral types](#114-tame-positive-depth-dihedral-types)
  - [11.5 The selected level theorem](#115-the-selected-level-theorem)
- [12. Singular germs and scalar norms](#12-singular-germs-and-scalar-norms)
  - [12.1 Why regular matching is not enough](#121-why-regular-matching-is-not-enough)
  - [12.2 The two split germs and the twisted germs](#122-the-two-split-germs-and-the-twisted-germs)
  - [12.3 Germ-compatible transfer](#123-germ-compatible-transfer)
  - [12.4 Quadratic division-centralizer terms](#124-quadratic-division-centralizer-terms)
  - [12.5 Central distributions](#125-central-distributions)
- [13. Archimedean cyclic matching](#13-archimedean-cyclic-matching)
  - [13.1 Split archimedean algebras](#131-split-archimedean-algebras)
  - [13.2 The extension $\mathbf C/\mathbf R$](#132-the-extension-mathbf-cmathbf-r)
  - [13.3 Weight and singular-endpoint checks](#133-weight-and-singular-endpoint-checks)
- [14. Assembly in the twisted trace comparison](#14-assembly-in-the-twisted-trace-comparison)
  - [14.1 Restricted tensor products](#141-restricted-tensor-products)
  - [14.2 Matching regular elliptic terms](#142-matching-regular-elliptic-terms)
  - [14.3 Scalar and nonelliptic channels](#143-scalar-and-nonelliptic-channels)
  - [14.4 Spectral traces in the selected range](#144-spectral-traces-in-the-selected-range)
  - [14.5 Failure modes](#145-failure-modes)
- [15. The cyclic matching package](#15-the-cyclic-matching-package)
  - [15.1 Main local theorem](#151-main-local-theorem)
  - [15.2 A calculation protocol](#152-a-calculation-protocol)
  - [15.3 Conclusion](#153-conclusion)

## Introduction

Let $L/F$ be a cyclic extension of local fields and let $\sigma$ generate its Galois group.
Local cyclic base change sends a selected representation of $\mathrm{GL}_2(F)$ to a
$\sigma$-invariant representation of $\mathrm{GL}_2(L)$.  That representation-theoretic
statement is not yet a trace-formula comparison.  On the geometric side, the first trace
formula averages a function along ordinary conjugacy classes in $\mathrm{GL}_2(F)$, while the
second averages a function along the twisted orbits

$$
x^{-1}\delta\sigma(x),\qquad \delta,x\in\mathrm{GL}_2(L).
$$

The bridge is the ordered norm

$$
N_\sigma(\delta)=\delta\sigma(\delta)\cdots\sigma^{d-1}(\delta),
\qquad d=[L:F].
$$

Its characteristic polynomial has coefficients in $F$.  A regular twisted class therefore
has a stable norm $\gamma\in\mathrm{GL}_2(F)$, but not every $\gamma$ occurs: it must be a norm
from its own centralizer torus.  Even when the class exists and is unique, equality of its two
characteristic polynomials does not imply equality of orbital integrals.  The groups, their
compact subgroups, their tangent determinants, and their quotient measures are different.
The cyclic fundamental lemma is the theorem that the correct test functions nevertheless
produce the same normalized orbital distribution.

The unramified unit case is the indispensable core.  It says that the characteristic function
of $\mathrm{GL}_2(\mathcal O_L)$ matches that of
$\mathrm{GL}_2(\mathcal O_F)$.  The proof given here is integral and rank two: both orbital
integrals are weighted counts of stable lattices, and unramified descent identifies their
groupoid cardinalities through successive congruence layers.  Adding Hecke correspondences
gives the full spherical statement and identifies the base-change homomorphism on the Satake
algebra.

Ramified places require a different conclusion.  There is no reason for the two raw maximal-
compact units to match, and the depth of a character changes according to the ramification
filtration.  We first prove transfer on the regular set by explicit transverse descent.  We
then turn stable vertices, edges, segments, and primitive endpoints into a finite triangular
system.  Its solution gives the invariant, Iwahori, $K_0$, $K_1$, special, and tame-dihedral
functions needed in cyclic trace comparisons.  The proof retains the wild boundary: primitive
wild packets and ramified dyadic positive-depth types are not covered by a finite tame Fourier
calculation.

There is also a singular boundary.  Near a scalar, regular orbital integrals have nilpotent
germs, and in quadratic degree a scalar norm can have quaternion division centralizer.  These
terms cannot be repaired by changing a sign in the regular identity.  They are analyzed and
matched separately.  The final package therefore distinguishes regular matching, germ
compatibility, and central distributions before assembling local factors into the geometric
comparison.

## 1. The local comparison problem

### 1.1 Why base change needs a geometric theorem

The local base-change operation of Book 86 is defined on Weil--Deligne parameters by
restriction from $W_F$ to $W_L$.  It determines central characters, conductors, local factors,
and the selected representation upstairs.  None of those assertions evaluates a geometric
orbit.  In particular, the equality

$$
\operatorname{rec}_L(\Pi)
=\operatorname{rec}_F(\pi)|_{W_L}
$$

does not by itself identify $\operatorname{tr}\pi(f)$ with a twisted trace of $\Pi(\phi)$.
Weyl integration shows what is missing: the first trace is built from ordinary orbital
integrals of $f$, while the second is built from twisted orbital integrals of $\phi$.

This distinction is not formal.  Consider a regular split norm with eigenvalues $a$ and $b$.
It occurs only if each eigenvalue lies in $N_{L/F}(L^\times)$; the weaker condition
$ab\in N_{L/F}(L^\times)$ does not suffice.  A function supported on integral matrices may
therefore meet an ordinary class for which no twisted class exists.  Matching must require the
ordinary orbital integral to vanish on the nonnorm locus.

At the opposite extreme, suppose $L/F$ is quadratic and
$N_\sigma(\delta)=aI_2$.  If $a$ is not a field norm, the twisted centralizer is the
multiplicative group of the quaternion division algebra $(L/F,a)$.  The stable norm is scalar,
but the twisted orbit is elliptic.  Any statement mentioning only strongly regular norms omits
this genuine trace-formula term.

The goal is consequently threefold: classify the matching classes, normalize their measures,
and construct functions with matching orbital distributions.  Only after those tasks are
complete may character identities turn geometric matching into equality of traces.

### 1.2 Standing notation and scope

Unless Chapter 13 says otherwise, $F$ is a nonarchimedean local field with ring of integers
$\mathcal O_F$, maximal ideal $\mathfrak p_F=(\varpi_F)$, residue field $k_F$, and
$q_F=|k_F|$.  Let $L/F$ be cyclic of degree $d$ with generator $\sigma$.  Write

$$
e=e(L/F),\qquad f=f(L/F),\qquad d=ef,qquad q_L=q_F^f.
$$

Set

$$
G=\mathrm{GL}_{2/F},\qquad H=\operatorname{Res}_{L/F}G_L.
$$

Thus $G(F)=\mathrm{GL}_2(F)$ and $H(F)=\mathrm{GL}_2(L)$.  At a split local place in a global
extension, $L$ is instead the cyclic étale algebra $F^d$; Section 2.3 treats that case without
calling it a field.

We normalize valuations and absolute values by

$$
v_F(\varpi_F)=1,\quad |x|_F=q_F^{-v_F(x)},
\qquad
v_L(\varpi_L)=1,\quad |y|_L=q_L^{-v_L(y)}.
$$

Put

$$
K_F=\mathrm{GL}_2(\mathcal O_F),\qquad
K_L=\mathrm{GL}_2(\mathcal O_L).
$$

All finite-place functions are complex-valued, locally constant, and compactly supported.  A
compact-mod-center formulation with fixed unitary central character is obtained by central
averaging; central terms are retained explicitly in Chapter 12.

The unramified theorems hold for every finite cyclic unramified extension.  The ramified
regular-transfer theorem also holds for every finite cyclic extension.  The explicit positive-
depth type calculations are asserted in the selected range already constructed by the local
representation theory: characters, principal series, special representations, depth-zero
dihedral supercuspidals, and tame positive-depth dihedral supercuspidals whose restricted
parameters remain selected.  No statement is made for primitive wild packets or ramified
dyadic wild types.

The global geometric application inherited from Book 113 has prime cyclic degree.  We retain
that hypothesis only when using its exhaustive scalar-norm classification and global twisted
distribution.  The local unramified and regular statements do not need primality.

### 1.3 The normalization ledger

The following choices remain fixed throughout the finite-place theory.

| object | normalization |
|---|---|
| $dg$ on $G(F)$ | $\operatorname{vol}(K_F)=1$ |
| $dh$ on $H(F)$ | $\operatorname{vol}(K_L)=1$ in the field case; product volume one in the split case |
| split torus $F^\times\times F^\times$ | product of unit-volume multiplicative measures |
| quadratic torus $K^\times$ | $\operatorname{vol}(\mathcal O_K^\times)=1$ when integral and unramified; otherwise transported as stated |
| twisted centralizer | identified with the norm centralizer and given the transported measure |
| orbit quotient | complementary measure from $dh=di\,d\dot h$ or $dg=dt\,d\dot g$ |
| ordinary normalization | $I_\gamma(f)=|D_G(\gamma)|^{1/2}O_\gamma(f)$ |
| twisted normalization | $I_\delta^\sigma(\phi)=|D^\sigma(\delta)|^{1/2}O_\delta^\sigma(\phi)$ |

At ramified places, the phrase “transported measure” is not shorthand for a nonexistent
canonical choice.  We select a Haar measure on the common algebraic centralizer
$T_\gamma\simeq I_\delta$, then use that one measure in both quotient formulas.  Changing it
rescales both normalized orbital integrals inversely and leaves the global volume-times-orbit
term unchanged.

Normalized induction is used on the representation side.  Local reciprocity is geometrically
normalized, so $\operatorname{rec}_F(\varpi_F)$ is geometric Frobenius and a multiplicative
character $\chi$ restricts from $W_F$ to $W_L$ as $\chi\circ N_{L/F}$.  This is exactly the
normalization of Book 86.

### 1.4 The three forms of the matching assertion

Let $\delta\in H(F)$ be strongly $\sigma$-regular with stable norm $\gamma\in G(F)$.  A pair
$(f,\phi)$, with $f$ on $G(F)$ and $\phi$ on $H(F)$, has **matching regular orbital
integrals** if

$$
I_\gamma(f)=I_\delta^\sigma(\phi)
\tag{1.1}
$$

for every matching pair and

$$
I_\gamma(f)=0
\tag{1.2}
$$

whenever the regular class $\gamma$ is not in the local torus-norm image.  The stable twisted
fiber has one rational class in rank two, so no additional sum occurs in (1.1).  We retain the
word “stable” because the norm class, not a chosen ordered product matrix, is the comparison
variable.

The unnormalized form of (1.1) is

$$
O_\gamma(f)
=\Delta_{L/F}(\gamma,\delta)^{-1}O_\delta^\sigma(\phi),
\qquad
\Delta_{L/F}(\gamma,\delta)
=\left|\frac{D_G(\gamma)}{D^\sigma(\delta)}\right|^{1/2}.
\tag{1.3}
$$

Thus an assertion of raw equality is valid only when the chosen measures and tangent
normalizations make the displayed factor one.  We use (1.1) as the primary statement.

The second form is the **fundamental lemma**: for prescribed natural functions, usually
hyperspecial units or Hecke functions, prove (1.1)--(1.2) without choosing the function class
by class.  The point is uniformity over infinitely many regular orbits.

The third form is **germ-compatible matching**.  It requires (1.1), compatibility of the
nilpotent expansions as $\gamma$ approaches a scalar, and a separately declared rule for
scalar distributions.  Regular matching alone never implies equality of point values at the
center.

## 2. Norms and matching classes

### 2.1 Twisted classes and ordered norms

For $\delta\in\mathrm{GL}_2(L)$ define the $\sigma$-semilinear operator

$$
T_\delta(v)=\delta\sigma(v),\qquad v\in L^2.
\tag{2.1}
$$

Twisted conjugation by $x$ is ordinary similarity of semilinear maps:

$$
T_{x^{-1}\delta\sigma(x)}=x^{-1}T_\delta x.
$$

Its $d$th power is the $L$-linear operator

$$
T_\delta^d=N_\sigma(\delta)
=\delta\sigma(\delta)\cdots\sigma^{d-1}(\delta).
\tag{2.2}
$$

Cyclically moving the first factor gives

$$
\sigma(N_\sigma(\delta))
=\delta^{-1}N_\sigma(\delta)\delta.
\tag{2.3}
$$

Consequently the trace and determinant of the ordered norm lie in $F$, and

$$
\det N_\sigma(\delta)=N_{L/F}(\det\delta).
\tag{2.4}
$$

If the ordered norm is noncentral, its characteristic polynomial determines one rational
conjugacy class in $G(F)$, represented by its companion matrix.  If it is $aI_2$, equation
(2.3) gives $a\in F$ and the scalar itself is the stable norm.  A scalar norm is not identified
with a noncentral Jordan norm having the same repeated polynomial.

The discriminant

$$
\Delta_\delta
=\operatorname{tr}(N_\sigma(\delta))^2
-4\det(N_\sigma(\delta))
\tag{2.5}
$$

is nonzero exactly for strongly $\sigma$-regular classes.  In residue characteristic two, it
still detects separability, but the étale algebra

$$
F[X]/(X^2-sX+n)
$$

rather than a square class distinguishes split and field cases.

### 2.2 The regular norm image

Let $\gamma\in G(F)$ be regular semisimple and let

$$
T_\gamma=G_\gamma\simeq
\operatorname{Res}_{K/F}\mathbf G_m,
\qquad K=F[\gamma].
$$

The algebra $K$ is either $F\times F$ or a quadratic field.  Book 113 proves the following
classification, and we recall the proof because it types every orbital identity in this book.

**Theorem 2.1 (regular norm fiber).** There is a strongly regular twisted class with stable norm
$\gamma$ if and only if

$$
\gamma\in N_{L/F}^{T_\gamma}(T_\gamma(L)).
\tag{2.6}
$$

When it exists, the rational twisted class is unique and its twisted centralizer is
canonically isomorphic, up to conjugacy, to $T_\gamma$.

**Proof strategy.** Conjugate the ordered norm to $\gamma$.  The twisted representative then
commutes with $\gamma$ and lies in its torus.  Existence becomes an abelian norm equation;
uniqueness is Hilbert 90 in the quadratic étale algebra.

**Proof.** Choose $y\in G(L)$ with
$y^{-1}N_\sigma(\delta)y=\gamma$ and replace $\delta$ by
$y^{-1}\delta\sigma(y)$.  Equation (2.3) now says that $\delta$ commutes with $\gamma$, so
$\delta\in T_\gamma(L)$ and its ordered norm is the torus norm.  This proves necessity.
Conversely, any $t\in T_\gamma(L)$ with norm $\gamma$ supplies a twisted class.

If $t_1$ and $t_2$ have the same norm, $u=t_2t_1^{-1}$ has norm one in
$(K\otimes_FL)^\times$.  Hilbert 90 gives $u=x^{-1}\sigma(x)$ with
$x\in T_\gamma(L)$, and commutativity yields
$x^{-1}t_1\sigma(x)=t_2$.  Finally, an element fixed by twisted conjugation commutes with the
norm and therefore lies in $T_\gamma(L)$; there the equation reduces to $\sigma(x)=x$, so the
centralizer is $T_\gamma(F)$. $\square$

For a split class with eigenvalues $a\ne b$, condition (2.6) is

$$
a,b\in N_{L/F}(L^\times).
\tag{2.7}
$$

For an elliptic class, regard $\gamma$ as an element of the quadratic field $K$.  Then (2.6)
becomes

$$
\gamma\in
N_{K\otimes_FL/K}((K\otimes_FL)^\times).
\tag{2.8}
$$

These exact conditions explain the vanishing clause (1.2).

### 2.3 Split local algebras

In a global cyclic extension, a place can split completely.  Locally one then has

$$
L=F^d,qquad
H(F)=G(F)^d,
$$

with $\sigma$ cyclically permuting the factors.  Write
$\delta=(\delta_0,\ldots,\delta_{d-1})$.  Successive twisted conjugations reduce it to

$$
(\delta_0\delta_1\cdots\delta_{d-1},1,\ldots,1).
\tag{2.9}
$$

Indeed, choose the last $d-1$ components of the conjugating tuple recursively so that the last
$d-1$ transformed components become one; the first becomes the displayed product up to
ordinary conjugacy.  The twisted centralizer is the diagonal copy of the ordinary centralizer
of that product.

If $\phi=\phi_0\otimes\cdots\otimes\phi_{d-1}$, quotient integration and repeated convolution
give

$$
O_\delta^\sigma(\phi)
=O_{\delta_0\cdots\delta_{d-1}}
(\phi_0*\phi_1*\cdots*\phi_{d-1}).
\tag{2.10}
$$

This identity is the split-place fundamental lemma.  It is an equality of integrals, not an
analogy: after using (2.9), the $d-1$ free group variables are exactly the convolution
variables.  In particular, the tensor of hyperspecial units transfers to the hyperspecial
unit, and every local norm class occurs.

### 2.4 Scalar norms and the quadratic exception

Suppose $N_\sigma(\delta)=aI_2$.  The fixed algebra

$$
B_\delta
=\{X\in M_2(L):X=\delta\sigma(X)\delta^{-1}\}
\tag{2.11}
$$

is a central simple algebra of degree two over $F$, split by $L$, and
$I_\delta=B_\delta^\times$.  If $d$ is odd, its Brauer class is killed by both $2$ and $d$,
hence is zero.  The class is twisted conjugate to a scalar.

If $d=2$, then

$$
B_\delta\simeq(L/F,a),
\tag{2.12}
$$

the quaternion cyclic algebra.  It is split precisely when $a\in N_{L/F}(L^\times)$ and is
division otherwise.  A convenient representative is

$$
\delta_a=
\begin{pmatrix}0&a\\1&0\end{pmatrix},
\qquad \delta_a\sigma(\delta_a)=aI_2.
\tag{2.13}
$$

Solving $X\delta_a=\delta_a\sigma(X)$ gives

$$
X=
\begin{pmatrix}
r&a\sigma(t)\\t&\sigma(r)
\end{pmatrix},
\qquad
\det X=N(r)-aN(t).
\tag{2.14}
$$

The determinant form is anisotropic exactly when $a$ is not a norm, proving the split-versus-
division assertion directly.

Scalar-norm classes are not part of the regular norm fiber and carry no regular discriminant.
They will be compared as separate relative or quaternionic distributions in Chapter 12.

## 3. Measures, discriminants, and transfer factors

### 3.1 Complementary quotient measures

For regular $\gamma\in G(F)$, let $T=G_\gamma$.  Choose $dt$ on $T(F)$ and define
$d\dot g$ by

$$
\int_{G(F)}\Phi(g)\,dg
=\int_{T(F)\backslash G(F)}\int_{T(F)}
\Phi(tg)\,dt\,d\dot g.
\tag{3.1}
$$

Then

$$
O_\gamma(f)
=\int_{T(F)\backslash G(F)}f(g^{-1}\gamma g)\,d\dot g.
\tag{3.2}
$$

For matching $\delta$, Theorem 2.1 identifies $I_\delta$ with the same $F$-torus $T$.  Use the
same $dt$ and define the complementary quotient measure by

$$
O_\delta^\sigma(\phi)
=\int_{I_\delta(F)\backslash H(F)}
\phi(h^{-1}\delta\sigma(h))\,d\dot h.
\tag{3.3}
$$

This shared centralizer measure is the only meaningful way to compare (3.2) and (3.3).  If it
is multiplied by $c$, both orbital integrals are multiplied by $c^{-1}$.  If only one quotient
measure is rescaled, any equality between them has been changed rather than renormalized.

For an unramified integral torus, $dt$ gives its maximal compact subgroup volume one.  This
choice is compatible on both sides because the twisted centralizer and norm centralizer have
the same smooth integral model.  At ramified places, we state the chosen torus model before
using a volume.

### 3.2 Ordinary and twisted Weyl determinants

The ordinary Weyl determinant is

$$
D_G(\gamma)
=\det_F(1-\operatorname{Ad}(\gamma)mid
\mathfrak g/\mathfrak t).
\tag{3.4}
$$

If $\gamma$ has trace $s$, determinant $n$, and polynomial discriminant
$\Delta=s^2-4n$, then

$$
|D_G(\gamma)|=\left|\frac{\Delta}{n}\right|_F.
\tag{3.5}
$$

Indeed, after diagonalization with eigenvalues $a,b$, the two root eigenvalues are $a/b$ and
$b/a$, and

$$
(1-a/b)(1-b/a)=-(a-b)^2/(ab).
$$

The twisted tangent map at $\delta$ is

$$
X\longmapsto\operatorname{Ad}(\delta)\sigma(X)-X
\tag{3.6}
$$

on $\mathfrak h=\operatorname{Res}_{L/F}\mathfrak{gl}_2$.  Its kernel is
$\mathfrak i_\delta$.  For a twisted semisimple element define

$$
D^\sigma(\delta)
=\det_F(1-\operatorname{Ad}(\delta)\sigmamid
\mathfrak h/\mathfrak i_\delta).
\tag{3.7}
$$

This determinant is invariant under twisted conjugacy.  It is nonzero with
$\dim I_\delta=2$ exactly for strongly regular classes.

It is tempting to replace (3.7) by (3.4) because the centralizers are isomorphic.  That is not
valid without a calculation: $\mathfrak h$ has $F$-dimension $4d$, while $\mathfrak g$ has
dimension four.  The extra semilinear directions contribute to (3.7).  The transfer factor in
the next section records them.

### 3.3 The base-change transfer factor

For a matching regular pair define

$$
\Delta_{L/F}(\gamma,\delta)
=\left|\frac{D_G(\gamma)}{D^\sigma(\delta)}\right|_F^{1/2}.
\tag{3.8}
$$

This factor is positive and depends only on the two stable classes with the declared absolute
value convention.  Its role is forced, not chosen: equality of normalized integrals is
equivalent to (1.3).

There is a useful root calculation.  Over a splitting field of the norm torus, a root direction
of $\mathfrak h$ is an $L$-line on which the twisted operator is $c\sigma$.  The elementary
determinant identity

$$
\det_F(1-c\sigma\mid L)=1-N_{L/F}(c)
\tag{3.9}
$$

follows by choosing a normal basis: the matrix of $c\sigma$ is a weighted cycle, and the
constant term of its characteristic polynomial is $N(c)$.  The two root directions therefore
contribute

$$
(1-a/b)(1-b/a)=D_G(\gamma).
$$

The remaining factor in $D^\sigma$ comes from the nonfixed directions of the centralizer
algebra.  It is independent of the root values and is exactly compensated by the Jacobian
used when the centralizer measure is descended from $L$ to $F$.  Thus with quotient measures
defined from a common invariant differential form, (3.8) is the full conversion between raw
orbital densities; no orbit-dependent sign remains for $\mathrm{GL}_2$.

At an unramified place the root lattices descend integrally, but the nonfixed semilinear
directions of the centralizer can still contribute a constant determinant, notably when the
residue characteristic divides $d$.  One must therefore retain (3.8) unless the chosen
quotient differentials have been checked to make it one.  At a ramified place the different
adds a further possible contribution.  This is why the normalized formulation remains
primary.

### 3.4 Measure changes and products

Suppose $dg,dh,dt$ are multiplied by $a,b,c>0$.  Then

$$
O_\gamma\longmapsto(a/c)O_\gamma,
\qquad
O_\delta^\sigma\longmapsto(b/c)O_\delta^\sigma.
\tag{3.10}
$$

The discriminants do not change.  A matching identity survives only if the test functions or
group measures are adjusted accordingly.

Globally, the centralizer coefficient

$$
a(\delta)=\operatorname{vol}
\bigl(I_\delta(F)\backslash I_\delta(\mathbf A_F)^1\bigr)
$$

is multiplied by the product of local centralizer scalars, while the adelic orbital integral
is multiplied by its inverse.  Hence

$$
a(\delta)O_\delta^\sigma(\phi)
\tag{3.11}
$$

is invariant.  Also, for rational regular $\delta$, the product formula gives

$$
\prod_v|D^\sigma(\delta)|_v
=\prod_v|D_G(\gamma)|_v=1.
\tag{3.12}
$$

Local discriminant factors therefore cancel in the product, but they remain essential at each
place.

## 4. Twisted characters in the selected rank-two range

### 4.1 Normalizing the intertwiner

Let $\pi$ be a selected irreducible representation of $G(F)$ and let

$$
\Pi=\operatorname{BC}_{L/F}(\pi)
$$

be defined.  Book 86 proves $\Pi^\sigma\simeq\Pi$.  An isomorphism

$$
A_\sigma:\Pi\longrightarrow\Pi^\sigma
$$

is unique up to scalar when $\Pi$ is irreducible.  A twisted trace is meaningless until this
scalar is fixed.

For a generic $\Pi$, choose the Whittaker model for the trace-compatible additive character

$$
\psi_L=\psi_F\circ\operatorname{Tr}_{L/F}.
$$

There is one Whittaker functional up to scalar.  Normalize $A_\sigma$ to fix it.  Iterating then
gives $A_\sigma^d=1$: the iterate fixes the same functional and is scalar by irreducibility.
For a spherical representation this normalization also fixes the standard spherical vector.

For a determinant character $\mu_L\circ\det$, take the natural action induced from
$\mu_L=\mu\circ N_{L/F}$; it is already $\sigma$-fixed.  At a reducible restriction where a
supercuspidal base change becomes principal series, normalize the induced model by the same
Whittaker condition.  These choices are compatible with twists and with transitivity in towers.

The twisted character distribution is

$$
\Theta_{\Pi,\sigma}(\phi)
=\operatorname{tr}(\Pi(\phi)A_\sigma).
\tag{4.1}
$$

On the strongly regular twisted set it is represented by a locally integrable function,
denoted $\Theta_{\Pi,\sigma}(\delta)$.

### 4.2 Principal and determinant characters

Let $\pi=I_F(\chi_1,\chi_2)$ be an irreducible normalized principal series and put
$\chi_{i,L}=\chi_i\circ N_{L/F}$.  Away from the reducibility boundary,

$$
\Pi=I_L(\chi_{1,L},\chi_{2,L}).
$$

The character of normalized induction is a fixed-point sum over the two flags of a split
regular element.  The twisted version is a fixed-point sum over semilinear invariant lines.
If $\delta$ has split regular norm with eigenvalues $a,b$, those lines exist exactly when
$a,b$ are norms.  Choosing $u,v\in L^\times$ with $N(u)=a$ and $N(v)=b$, the two contributions
are

$$
\chi_{1,L}(u)\chi_{2,L}(v)
=\chi_1(a)\chi_2(b)
$$

and the term with $a,b$ exchanged.  The tangent Jacobian converts by (3.8).  Hence

$$
|D^\sigma(\delta)|^{1/2}\Theta_{\Pi,\sigma}(\delta)
=|D_G(\gamma)|^{1/2}\Theta_\pi(\gamma).
\tag{4.2}
$$

If the norm is elliptic, neither side has an invariant flag and both principal-series
characters vanish.  If the regular ordinary class is not a norm, there is no twisted value;
this is the character counterpart of (1.2).

At the boundary, the restricted split parameter can yield a determinant character rather than
an irreducible principal series.  The monodromy is zero, so the character selected upstairs is
$\mu_L\circ\det$.  Since

$$
\det N_\sigma(\delta)=N_{L/F}(\det\delta),
$$

its twisted value is $\mu(\det\gamma)$, the ordinary determinant-character value.  Thus (4.2)
persists at the boundary after interpreting the irreducible constituent correctly.

### 4.3 Special representations

Let $\pi=\operatorname{St}_F\otimes\mu$.  Its base change is

$$
\Pi=\operatorname{St}_L\otimes(\mu\circ N_{L/F}).
$$

Use the normalized-induction exact sequence

$$
0\longrightarrow\mu\circ\det
\longrightarrow I_F(\mu\nu_F^{-1/2},\mu\nu_F^{1/2})
\longrightarrow\operatorname{St}_F\otimes\mu
\longrightarrow0
\tag{4.3}
$$

and its $L$-analogue.  The normalized intertwiner preserves the subrepresentation and quotient,
so twisted characters are additive in the upstairs sequence.  The induced and determinant
rows satisfy (4.2); subtracting them proves (4.2) for the special row.

This proof also explains why monodromy must be remembered.  The special and determinant
parameters have the same semisimple characters at the wall, but the exact sequence assigns
opposite ends.  Restriction preserves the nonzero monodromy operator, so the special quotient
cannot turn into the determinant subrepresentation.

On an elliptic regular class, the induced character vanishes.  Therefore

$$
\Theta_{\operatorname{St}_F\otimes\mu}(\gamma)
=-\mu(\det\gamma),
$$

and the twisted special character has the corresponding norm value with the same tangent
conversion.

### 4.4 Dihedral supercuspidals

Let $\pi$ have parameter

$$
r=\operatorname{Ind}_{W_K}^{W_F}\theta
$$

for a selected tame admissible quadratic pair $(K/F,\theta)$.  Put $M=KL$.  Mackey theory from
Book 86 gives either an induced quadratic parameter over $L$ or a sum of two characters.
Accordingly, $\Pi$ is a selected supercuspidal or an irreducible principal series.

The character calculation is most transparent in the compact-induction model.  On a regular
torus element, the character is a sum over embeddings of the quadratic torus.  Twisted
conjugation replaces ordinary embeddings by semilinear embeddings whose $d$th power is the
chosen norm embedding.  The regular norm fiber theorem makes this set a torsor under the same
centralizer group on both sides.  Each contributing torus value upstairs is

$$
(\theta\circ N_{M/K})(t)=\theta(N_{M/K}t),
$$

which is the value of $\theta$ on the ordinary norm element downstairs.

At depth zero, the remaining finite quotient is a Frobenius orbit in a quadratic residue
field.  The two terms are

$$
\bar\theta(x)+\bar\theta(x^{q_F}).
\tag{4.4}
$$

Upstairs, semilinear fixed points form the corresponding Frobenius orbit over $k_L$; taking the
$\sigma$-trace collapses it to (4.4).  At tame positive depth, the compact-induction trace is a
finite Fourier sum on the trace-orthogonal complement of the torus.  Successive layers occur in
dual pairs.  Their Fourier indices cancel, while the last active layer is carried by the field
trace from $M$ to $K$.  Trace transitivity makes its phase exactly the downstairs phase.  The
Whittaker normalization removes the common Gauss scalar.  Thus (4.2) holds.

If restriction makes the parameter reducible, the two torus embeddings become two character
lines.  The same Mackey sum is then precisely the fixed-flag formula for the resulting
principal series.  No extra term appears at the discrete-to-principal boundary.

The tame hypothesis enters at the last Fourier layer.  In a ramified dyadic wild pair, the
trace-dual filtration can jump and its quadratic refinement is not determined by the data
constructed in the selected correspondence.  The preceding argument makes no assertion in
that case.

### 4.5 The selected norm character identity

We collect the preceding calculations.

**Theorem 4.1 (selected local norm character identity).** Let $L/F$ be finite cyclic, let
$\pi$ lie in the selected local base-change domain of Book 86, and put
$\Pi=\operatorname{BC}_{L/F}(\pi)$.  Normalize $A_\sigma$ as in Section 4.1.  For every
matching strongly regular pair $(\gamma,\delta)$,

$$
\boxed{
|D_G(\gamma)|^{1/2}\Theta_\pi(\gamma)
=|D^\sigma(\delta)|^{1/2}
\Theta_{\Pi,\sigma}(\delta).}
\tag{4.5}
$$

The theorem covers determinant characters, irreducible principal series and their boundary,
special representations, depth-zero dihedral representations, and tame positive-depth
dihedral representations whose restricted parameter remains selected.  It is compatible with
character twists, contragredients, and transitivity in cyclic towers.

**Proof.** Sections 4.2--4.4 prove all selected parameter shapes.  They are exhaustive by the
rank-two dictionary of Book 86.  Twists multiply both sides by the same norm value;
contragredience follows by inversion; tower compatibility follows from transitivity of norm,
trace, and the Whittaker normalization. $\square$

The identity is a character theorem, not the fundamental lemma.  It says what matching test
functions will do to selected traces once their orbital integrals have been constructed.  It
cannot be used to infer the unit orbital identity from equality on a few representations.

## 5. Unramified integral geometry

### 5.1 Semilinear stable lattices

Assume throughout this chapter that $L/F$ is unramified of degree $d$.  Then
$\varpi_F$ is also a uniformizer of $L$, $\mathcal O_L/\mathfrak p_L$ is the degree-$d$
extension of $k_F$, and $\sigma$ preserves every power of $\mathfrak p_L$.

The vertices of the building tree $X_L$ of $\mathrm{PGL}_2(L)$ are homothety classes of
$\mathcal O_L$-lattices in $L^2$.  The semilinear operator $T_\delta$ acts on this tree.  For
$x\in G(L)$ and $\Lambda_x=x\mathcal O_L^2$,

$$
x^{-1}\delta\sigma(x)\in K_L
\quad\Longleftrightarrow\quad
T_\delta(\Lambda_x)=\Lambda_x.
\tag{5.1}
$$

The implication uses equality, not containment: an element of $K_L$ acts invertibly on the
standard lattice.  Thus the twisted orbital integral of the unit is a weighted count of
$T_\delta$-stable lattice classes.

If $T_\delta^d=\gamma$, every $T_\delta$-stable lattice is $\gamma$-stable.  The converse is
false for an individual lattice, so the fundamental lemma is not a literal identification of
fixed sets.  What descends is their weighted quotient.  The weights remember automorphism
groups and make the extra semilinear choices cancel.

On the ordinary side, for $y\in G(F)$ and $M_y=y\mathcal O_F^2$,

$$
y^{-1}\gamma y\in K_F
\quad\Longleftrightarrow\quad
\gamma M_y=M_y.
\tag{5.2}
$$

When $\gamma$ is elliptic with centralizer $K^\times$, these are fractional ideals for the
quadratic order $R=\mathcal O_F[\gamma]$.  When $\gamma$ is split, they are rank-two lattices
for a split order.  The same order controls the semilinear problem after unramified base
change.

### 5.2 Weighted lattice groupoids

It is useful to keep stabilizers inside the objects rather than divide them away prematurely.
Define $\mathscr L_F(\gamma)$ to be the groupoid whose objects are $\gamma$-stable
$\mathcal O_F$-lattices in $F^2$ in the determinant shell under consideration, and whose
morphisms are elements of $T_\gamma(F)$ carrying one lattice to another.  Define
$\mathscr L_L(\delta)$ similarly using $T_\delta$-stable $\mathcal O_L$-lattices and the
twisted centralizer $I_\delta(F)=T_\gamma(F)$.

For a finite quotient groupoid $\mathscr C$, its weighted cardinality is

$$
|\mathscr C|_{\mathrm w}
=\sum_{[C]}\frac1{\operatorname{vol}(\operatorname{Aut}C)},
\tag{5.3}
$$

with the common compact-unit Haar normalization.  In a fixed determinant shell the groupoids
above have finitely many isomorphism classes.  Quotient integration gives

$$
O_\gamma(\mathbf1_{K_F})
=|\mathscr L_F(\gamma)|_{\mathrm w},
\qquad
O_\delta^\sigma(\mathbf1_{K_L})
=|\mathscr L_L(\delta)|_{\mathrm w},
\tag{5.4}
$$

after the unramified descent Jacobian has been absorbed in the common torus measure.  More
explicitly, a lattice $M=y\mathcal O_F^2$ contributes

$$
\frac{\operatorname{vol}(K_F)}
{\operatorname{vol}(T_\gamma(F)\cap yK_Fy^{-1})},
$$

and the analogous formula holds upstairs.  Since both maximal compacts have volume one, these
are precisely reciprocal stabilizer volumes.

The determinant shell is necessary.  Scalar homothety otherwise produces an infinite
$\mathbf Z$-direction.  Fixing $v_F(\det\gamma)$ on the ordinary side and the compatible
$v_L(\det\delta)$ on the twisted side leaves a finite quotient; central translates recover all
other shells.

### 5.3 Integral descent through congruence layers

We now prove the descent calculation on which the unit lemma rests.  Let

$$
R=\mathcal O_F[\gamma]\subset K=F[\gamma]
$$

for an elliptic norm; the split case uses the same argument with $K=F\times F$.  Every stable
lattice has a multiplier order $R_c$ containing $R$.  Filter its automorphism group by

$$
U_c^m=1+\mathfrak p_F^mR_c,
\qquad m\ge1.
\tag{5.5}
$$

After tensoring with $\mathcal O_L$, the successive quotients are additive groups of finite
$k_L$-vector spaces.  The semilinear descent equation on one layer has the form

$$
z^{-1}\sigma(z)=u
\tag{5.6}
$$

multiplicatively at level zero and

$$
\sigma(Z)-Z=U
\tag{5.7}
$$

on the higher additive layers.

The solvability conditions are the expected norm and trace conditions.  For (5.7), the image
of $\sigma-1$ is the trace-zero subspace.  This follows because
$\operatorname{Tr}(\sigma Z-Z)=0$ and both spaces have codimension one: the kernel consists of
the $k_F$-rational vectors.  For (5.6) on residue-field units, the kernel of the norm is the
image of $z\mapsto z^{-1}\sigma(z)$.  Indeed the finite cyclic group $k_L^\times$ has order
$q_F^d-1$; the image has size

$$
\frac{q_F^d-1}{q_F-1},
$$

which is exactly the kernel size of the norm to $k_F^\times$.

Inductively lift a solution modulo $\mathfrak p_L^m$ to one modulo
$\mathfrak p_L^{m+1}$.  The error lies in the additive quotient and has trace zero because the
norm equation already holds one level lower.  Equation (5.7) removes it.  Completeness gives a
solution in the full unit group.  This proves the integral form of Hilbert 90 needed here:

$$
H^1(\langle\sigma\rangle,(R_c\otimes\mathcal O_L)^\times)=1
\tag{5.8}
$$

for the unit filtrations that occur, with the split order interpreted componentwise.

The groupoid count requires one further observation.  At every lifting layer, the set of
solutions is a torsor under the fixed vectors, and the automorphism group is enlarged by the
same fixed-vector group.  Hence

$$
\frac{\#\{\text{lifts of an object}\}}
{\#\{\text{new automorphisms}\}}=1.
\tag{5.9}
$$

This ratio is the finite version of cancellation between orbit multiplicity and stabilizer
volume.  Iterating (5.9) cancels all congruence-layer factors.  A determinant from the
nonfixed semilinear torus and orbit directions remains; it is recorded by the transfer factor
below.

The argument also handles nonmaximal orders.  Their unit filtration may have a larger nilpotent
radical modulo $\mathfrak p$, but that radical is an additive $k_F$-space; (5.7) applies to it.
The reduced quotient is a product of finite multiplicative groups, handled by (5.6).  No
smoothness assertion about the whole nonmaximal order is being assumed.

### 5.4 The weighted descent theorem

**Theorem 5.1 (unramified weighted lattice descent).** Let $L/F$ be finite cyclic unramified,
let $\delta\in G(L)$ be strongly $\sigma$-regular with stable norm $\gamma$, and choose the
common compact-unit measure on $I_\delta\simeq T_\gamma$.  In every compatible determinant
shell,

$$
\boxed{
|\mathscr L_L(\delta)|_{\mathrm w}
=\Delta_{L/F}(\gamma,\delta)
|\mathscr L_F(\gamma)|_{\mathrm w}.}
\tag{5.10}
$$

The same assertion holds for stable chains of any fixed finite length and for chains with a
primitive endpoint vector, provided the relative-position labels are carried through the norm
correspondence.

**Proof strategy.** Decompose both groupoids by multiplier order and elementary-divisor data.
On each piece, descend the semilinear structure through the residue quotient and then through
the principal-unit filtration.  At every step, lift multiplicity cancels automorphism
multiplicity.

**Proof.** A $T_\delta$-stable lattice is stable under $\gamma=T_\delta^d$ and hence has one of
the finitely many multiplier orders $R_c$ visible in the fixed determinant shell.  Choose an
$R_c$-lattice model.  The possible semilinear structures on its unramified scalar extension
are cocycles in $(R_c\otimes\mathcal O_L)^\times$.  Equation (5.8) says that every cocycle with
the prescribed norm is a coboundary, so it descends to an $R_c$-lattice over $\mathcal O_F$.

Conversely, extending a downstairs stable lattice to $\mathcal O_L$ and choosing the given
norm representative produces the corresponding semilinear object.  Different choices are
measured by the same cocycle group.  The layerwise ratio (5.9) cancels the integral lifting
factors even when there is no bijection on bare isomorphism classes.  Comparing the remaining
quotient differential lattices gives
$|D_G(\gamma)/D^\sigma(\delta)|^{1/2}$, exactly the factor in (5.10).  Summing over multiplier
orders proves the formula.

A chain is a lattice together with finitely many subquotients.  Their automorphism filtrations
have the same multiplicative residue part and additive congruence layers, so the identical
argument applies.  Remembering a primitive endpoint replaces one additive quotient by a free
unit torsor; its number of choices and its stabilizer index again cancel. $\square$

This theorem is the integral heart of unramified base change.  It is stronger than a
regular-reduction calculation and therefore remains valid when the characteristic polynomial
is scalar modulo $\mathfrak p_F$ and the fixed subtree has arbitrarily large depth.

## 6. The unramified unit fundamental lemma

### 6.1 Statement of the unit identity

Let $L/F$ be cyclic unramified.  Put

$$
\phi_L^0=\mathbf1_{K_L},
\qquad
f_F^0=\mathbf1_{K_F}.
\tag{6.1}
$$

Both functions are specified before a conjugacy class is chosen.  This is what makes the next
statement a fundamental lemma rather than local patching.

**Theorem 6.1 (unramified unit fundamental lemma for $\mathrm{GL}_2$).** For every matching
strongly regular pair $(\gamma,\delta)$,

$$
\boxed{I_\gamma(f_F^0)=I_\delta^\sigma(\phi_L^0).}
\tag{6.2}
$$

If a regular $\gamma$ is not in the local norm image, its matching stable twisted orbital
distribution is zero.  In unnormalized form, (6.2) is exactly

$$
O_\gamma(\mathbf1_{K_F})
=\Delta_{L/F}(\gamma,\delta)^{-1}
O_\delta^\sigma(\mathbf1_{K_L}).
\tag{6.3}
$$

The theorem holds in every residue characteristic and for split or quadratic regular
centralizer algebras.

### 6.2 Proof by weighted descent

**Proof of Theorem 6.1.** If either side is nonzero, trace and determinant of the corresponding
norm are integral and the determinant has the compatible unit valuation.  Equations (5.1) and
(5.2) identify the two raw orbital integrals with the weighted groupoid cardinalities in
(5.4).  Theorem 5.1 relates those cardinalities by the transfer factor.  Substituting its
definition (3.8) gives (6.3), and multiplication by the two square-root discriminants gives
(6.2).
$\square$

It is worth isolating the decisive step.  A $T_\delta$-stable lattice does not generally arise
as the scalar extension of one particular $\gamma$-stable lattice.  Bare fixed-point counts can
therefore differ.  The quotient integral assigns reciprocal automorphism volume to every
object.  Equation (5.9) makes the excess choices and excess automorphisms cancel.  Any proof
that merely identifies the two buildings overlooks this issue.

For a maximal unramified elliptic order, the congruence part of each groupoid has one object
with unit stabilizer; the remaining scale is exactly the quotient-differential factor in
(5.10).  For a nonmaximal order, extra stable lattice classes occur on both sides and their
layerwise ratios cancel in the same way.  For a split torus, quotienting its apartment removes
the infinite translation direction, leaving a finite tube calculation with the same transfer
factor.

### 6.3 Vanishing outside the norm image

The phrase “the twisted orbital integral is zero” outside the norm image needs interpretation:
there is no twisted class to integrate.  Define the stable twisted unit distribution on a
regular ordinary class by

$$
SO_\gamma^\sigma(\phi_L^0)
=\sum_{N^{\mathrm{st}}\delta=\gamma}I_\delta^\sigma(\phi_L^0).
\tag{6.4}
$$

The regular fiber theorem makes this sum empty or a singleton.  Thus

$$
SO_\gamma^\sigma(\phi_L^0)=0
$$

unless $\gamma$ satisfies the torus norm equation (2.6), and Theorem 6.1 says

$$
SO_\gamma^\sigma(\phi_L^0)=I_\gamma(f_F^0)
\tag{6.5}
$$

on the norm image.

Equation (6.5) does not mean that $I_\gamma(f_F^0)$ vanishes for every integral nonnorm class.
Indeed the ordinary unit can have a nonzero orbital integral there.  The standard base-change
statement compares only the norm image; if one wants a function whose ordinary orbital
integral is zero off that image, one applies the norm projector in the spherical Hecke algebra
or the regular patching construction of Chapter 8.  Keeping these two formulations distinct
prevents an impossible claim about $\mathbf1_{K_F}$.

Accordingly, the **unit fundamental lemma** is (6.2) on matching classes.  A **complete transfer
function** additionally includes off-image vanishing, and need not be the raw unit.  In global
cyclic comparison, rational classes on the twisted side already satisfy the norm condition, so
(6.2) is the required unramified identity.

### 6.4 Boundary and residue-characteristic checks

The theorem is stated for strongly regular classes.  As the discriminant approaches zero, the
weighted stable-lattice count may grow, but the normalized integral has a controlled germ.
Chapter 12 proves that the two unit germs correspond.  Thus no regular-nilpotent term is lost
when a global sum approaches the scalar divisor.

Nothing in the proof divides by two.  In residue characteristic two, separability is detected
by the étale algebra rather than by a discriminant square class; finite-field Hilbert 90 and
the additive trace sequence remain valid.  Inseparable quadratic algebras are not regular
semisimple centralizers and are excluded by the theorem's hypotheses.

Finally, unramified refers to the field extension, not to the norm class.  A ramified
representation or a norm with nonmaximal integral order is allowed.  The proof depends on the
unramified scalar extension of integral orders, not on regular reduction.

## 7. The spherical cyclic fundamental lemma

### 7.1 The base-change homomorphism

Let

$$
\mathcal H_F=C_c(K_F\backslash G(F)/K_F),
\qquad
\mathcal H_L=C_c(K_L\backslash G(L)/K_L)
$$

with convolution measures giving the maximal compacts volume one.  The normalized Satake
isomorphisms are

$$
\mathcal S_F:\mathcal H_F\xrightarrow{\sim}
\mathbf C[X_1^{\pm1},X_2^{\pm1}]^{S_2},
$$

$$
\mathcal S_L:\mathcal H_L\xrightarrow{\sim}
\mathbf C[Y_1^{\pm1},Y_2^{\pm1}]^{S_2}.
$$

Unramified base change raises geometric-Frobenius eigenvalues to the $d$th power.  Therefore
the **base-change homomorphism**

$$
b_{L/F}:\mathcal H_L\longrightarrow\mathcal H_F
\tag{7.1}
$$

is characterized by

$$
\mathcal S_F(b_{L/F}\phi)(X_1,X_2)
=\mathcal S_L(\phi)(X_1^d,X_2^d).
\tag{7.2}
$$

This direction is forced by traces.  If a spherical $\pi$ has Satake pair
$\{\alpha,\beta\}$, its base change has pair $\{\alpha^d,\beta^d\}$.  Hence

$$
\operatorname{tr}\pi(b_{L/F}\phi)
=\operatorname{tr}\operatorname{BC}_{L/F}(\pi)(\phi).
\tag{7.3}
$$

In particular $b_{L/F}(\mathbf1_{K_L})=\mathbf1_{K_F}$.

### 7.2 Galleries and Hecke correspondences

A double coset

$$
K_L\operatorname{diag}(\varpi_F^m,1)K_L
$$

is a correspondence on $X_L$: it sends a lattice vertex to vertices at elementary-divisor
distance $m$.  A convolution product counts galleries with prescribed successive distances.
Inserting a twisted orbital integral counts such galleries fixed by the semilinear endomorphism
$T_\delta$, modulo its centralizer.  The stabilizer of a gallery is the intersection of the
stabilizers of its vertices.

The chain version of Theorem 5.1 relates the weighted groupoid cardinality of these twisted
fixed galleries to that of ordinary $\gamma$-fixed galleries over $F$, with the same
$\Delta_{L/F}$ quotient-differential factor as for vertices.  A cyclic orbit of gallery steps
upstairs descends to one step downstairs whose coweight is the sum of the orbit.
On the dual torus, summing a $d$-cycle of equal coweights is exactly

$$
(X_1,X_2)\longmapsto(X_1^d,X_2^d).
\tag{7.4}
$$

Thus the descended correspondence is not usually the double coset with the same integer label;
it is the linear combination prescribed by (7.2).

To make the last statement independent of Satake theory, use the basis of monomial symmetric
functions.  A based gallery carries a sequence of choices of one of the two coordinate
directions.  The cyclic semilinear action permutes the $d$ copies of each choice.  A fixed
choice is constant around the cycle and contributes weight $d(1,0)$ or $d(0,1)$.  After
forgetting the ordering, these are the monomials $X_1^d$ and $X_2^d$.  Products of galleries
give products of monomials, and lower-distance folds give the usual triangular Satake
correction.  Hence the descended operator is exactly (7.2).

### 7.3 Proof of spherical matching

**Theorem 7.1 (spherical cyclic fundamental lemma for $\mathrm{GL}_2$).** Let $L/F$ be cyclic
unramified.  For every $\phi\in\mathcal H_L$ and every matching strongly regular pair
$(\gamma,\delta)$,

$$
\boxed{
I_\gamma(b_{L/F}\phi)=I_\delta^\sigma(\phi).}
\tag{7.5}
$$

Equivalently, the corresponding unnormalized integrals satisfy (1.3).  The identity is
compatible with convolution, central translation, inversion, and cyclic towers.

**Proof strategy.** Prove the identity first for convolution words in elementary double
cosets by counting fixed galleries.  Apply weighted unramified descent to the gallery groupoid.
Identify the descended correspondence through its coweight action, which is the Satake rule
(7.2).  Then use the fact that such convolution words span the spherical algebra.

**Proof.** Every spherical double coset for $\mathrm{GL}_2$ is generated under convolution and
linear combination by the standard distance-one correspondence and the central scalar
correspondence.  A convolution word expands as a finite weighted set of galleries.  Its
twisted orbital integral is the weighted cardinality of the $T_\delta$-fixed gallery groupoid.
The chain statement in Theorem 5.1 turns this into the weighted cardinality of the descended
$\gamma$-fixed gallery groupoid with the factor $\Delta_{L/F}(\gamma,\delta)$.

Section 7.2 identifies the operator represented by that descended groupoid with
$b_{L/F}$ of the original convolution word.  Therefore its weighted cardinality is
$O_\gamma(b_{L/F}\phi)$.  The unramified tangent and measure calculation converts this raw
identity to (7.5).  Linearity proves the theorem for all $\phi$.

Central translations add $(r,r)$ to every coweight and commute with (7.4).  Reversing a gallery
proves compatibility with inversion.  In a tower, substitution by $d_1$th powers followed by
$d_2$th powers is substitution by $(d_1d_2)$th powers, proving transitivity. $\square$

### 7.4 Explicit rank-two formulas

Let $\mathsf T_F$ and $\mathsf T_L$ be the normalized standard Hecke operators, with Satake
transforms $X_1+X_2$ and $Y_1+Y_2$.  Let $\mathsf S_F$ have transform $X_1X_2$.  Define

$$
P_0=2,qquad P_1=\mathsf T_F,qquad
P_m=\mathsf T_F*P_{m-1}-\mathsf S_F*P_{m-2}.
\tag{7.6}
$$

Then

$$
\mathcal S_F(P_m)=X_1^m+X_2^m,
$$

so

$$
b_{L/F}(\mathsf T_L)=P_d.
\tag{7.7}
$$

For example,

$$
b_{L/F}(\mathsf T_L)=
\begin{cases}
\mathsf T_F*\mathsf T_F-2\mathsf S_F,&d=2,\\
\mathsf T_F^{*3}-3\mathsf S_F*\mathsf T_F,&d=3.
\end{cases}
\tag{7.8}
$$

Also

$$
b_{L/F}(\mathsf S_L)=\mathsf S_F^{*d}.
\tag{7.9}
$$

Evaluating (7.7) on a spherical parameter $\{\alpha,\beta\}$ gives
$\alpha^d+\beta^d$, exactly the Frobenius-power rule of Book 86.  This is a spectral check of
the geometrically proved identity, not its proof.

The formulas expose a common error: the base-change image of the first Hecke operator is not
$d\mathsf T_F$, nor generally the characteristic function of one distance-$d$ shell.  Folded
galleries contribute the lower terms in the recursion.

## 8. Regular transfer at ramified places

### 8.1 Why the unit statement changes

Assume now that $L/F$ is ramified.  The residue fields, lattice scales, and different no longer
descend without a Jacobian.  A $T_\delta$-stable $\mathcal O_L$-lattice need not have the same
weighted count as a $\gamma$-stable $\mathcal O_F$-lattice, and there is no spherical
base-change homomorphism determined by unramified Satake parameters.  Thus the formula

$$
\mathbf1_{K_L}\longleftrightarrow\mathbf1_{K_F}
$$

is not asserted.

What remains true is local transfer on the strongly regular set.  Its proof is analytic-
algebraic rather than hyperspecial: the ordinary and twisted orbit maps have transverse slices,
and the norm map identifies their invariant coordinates.  This produces a matching function on
every compact regular region.  The subsequent chapters choose concrete representatives for
the level data needed globally.

### 8.2 Twisted descent on a regular slice

Fix a strongly regular $\delta_0$ with norm $\gamma_0$ and common centralizer $T$.  Choose
complements

$$
\mathfrak g=\mathfrak t\oplus\mathfrak q_F,
\qquad
\mathfrak h=\mathfrak i_{\delta_0}\oplus\mathfrak q_L.
$$

The ordinary orbit map near $(1,\gamma_0)$ is

$$
(\dot g,t)\longmapsto g^{-1}tg,
\tag{8.1}
$$

while the twisted orbit map is

$$
(\dot h,u)\longmapsto h^{-1}u\sigma(h).
\tag{8.2}
$$

Their transverse derivatives are $1-\operatorname{Ad}(\gamma_0)$ and
$1-\operatorname{Ad}(\delta_0)\sigma$, respectively.  Strong regularity makes both invertible
on the chosen complements.  The nonarchimedean inverse function theorem gives orbit-times-slice
charts.

On the invariant quotient, both slices are parameterized by trace and determinant of the
stable norm.  The derivative of the norm map on the centralizer direction is the torus trace

$$
X\longmapsto X+\sigma(X)+\cdots+\sigma^{d-1}(X),
\tag{8.3}
$$

after translating to the identity.  On the regular norm image its cokernel is exactly the
local obstruction already encoded by (2.6).  Restricting to one norm coset gives an analytic
submersion onto the ordinary invariant slice.

Let $a(\gamma)$ be a locally constant compactly supported function on such an ordinary slice,
supported inside the norm image.  Choose compactly supported functions of integral one in the
two orbit directions.  Divide by the corresponding Jacobians and extend by zero.  This
constructs $f$ and $\phi$ with

$$
I_\gamma(f)=a(\gamma)
=I_\delta^\sigma(\phi)
\tag{8.4}
$$

throughout the slice.  The ratio of Jacobians is precisely the transfer factor (3.8).

### 8.3 Patching compact regular data

Let $C$ be a compact subset of the regular ordinary quotient, separated from the discriminant
divisor.  Its intersection with the norm image is locally closed: the torus-norm subgroup has
finite index in the relevant multiplicative coordinates.  Partition $C$ into finitely many
compact-open pieces on which the centralizer type, norm coset, and discriminant valuation are
constant.

On each norm piece apply the slice construction of Section 8.2.  On each nonnorm piece use the
ordinary slice to prescribe zero.  Since the pieces are disjoint, their test functions can be
added.  This proves simultaneous matching and off-image vanishing on $C$.

Conversely, begin with a twisted function $\phi$ whose regular orbital function is supported
over $C$.  Its normalized orbital integral is locally constant on each twisted slice.  Push it
to the ordinary norm slice using the unique regular fiber, extend by zero across the nonnorm
cosets, and realize the resulting function by ordinary descent.  Compactness ensures that only
finitely many slices are needed.

The construction is unique only modulo **regular orbital null functions**, functions whose
orbital integral vanishes on every regular class.  This is the correct ambiguity.  A pointwise
choice of representatives or equality of test functions has no invariant meaning.

### 8.4 A complete regular transfer theorem

**Theorem 8.1 (regular cyclic transfer).** Let $L/F$ be a finite cyclic extension of
nonarchimedean local fields.  Let $\phi\in C_c^\infty(G(L))$, and suppose the stable twisted
orbital function of $\phi$ is supported over a compact subset of the ordinary regular quotient
bounded away from the discriminant divisor.  Then there exists
$f\in C_c^\infty(G(F))$ such that

$$
I_\gamma(f)=
\begin{cases}
I_\delta^\sigma(\phi),&N^{\mathrm{st}}\delta=\gamma,\\
0,&\gamma\text{ is not a norm},
\end{cases}
\tag{8.5}
$$

for every regular $\gamma$ in that compact set.  The transfer is unique modulo regular orbital
null functions there.  The same statement holds with the roles reversed for any prescribed
locally constant compact regular orbital datum satisfying the norm-image condition.

**Proof.** Local twisted orbital integrals are locally constant on the strongly regular set by
the orbit-times-slice chart.  The regular fiber theorem makes their pushforward to the norm
image single-valued.  Section 8.3 patches finitely many local realizations and sets the datum to
zero on nonnorm pieces.  Uniqueness is tautological in the quotient by regular orbital null
functions. $\square$

The separation from the discriminant is essential to this proof.  Near a scalar, the
transverse Jacobian degenerates and the orbital function must satisfy germ relations.  Chapter
12 extends the construction across that boundary for the unit and selected level functions.

## 9. Ramified lattice matching

### 9.1 Ramification, depth, and fixed subtrees

Regular transfer by slices proves existence but does not identify the compact-open functions
that a trace formula actually uses.  To do that, return to the trees $X_F$ and $X_L$.  The
ordinary class $\gamma$ acts linearly on $X_F$; the twisted class $\delta$ acts through the
semilinear isometry $T_\delta$ on $X_L$.  Their fixed sets are convex subtrees.

For a regular elliptic class, the minimal torus subtree is a vertex when the quadratic
centralizer is unramified and an edge midpoint when it is ramified.  A nonmaximal order fixes a
finite neighborhood of this core.  For a split class, the core is an apartment and an element
close to scalar fixes a tube around it.  These statements follow directly from stable lattices:
a vertex is fixed precisely when the corresponding lattice is a module over the order generated
by the element.

Define the **ordinary fixed depth** $c_F(\gamma)$ to be the largest integer $c$ such that the
$c$-neighborhood of the minimal torus subtree is fixed.  Define the **twisted fixed depth**
$c_L(\delta)$ similarly.  The two numbers are not generally equal.  Positive ramification
breaks are reindexed by the Herbrand function, and new invariants can appear when restriction
kills a tame character.  In rank two the relation is visible in the order discriminants:

$$
\operatorname{disc}(\mathcal O_F[\gamma])
\quad\text{and}\quad
\operatorname{disc}_{\sigma}(\mathcal O_L[T_\delta])
\tag{9.1}
$$

determine the radii up to the vertex-versus-edge core parity.  We do not replace this data by a
formula involving only $e$ and $f$; Book 86's conductor examples already show why such a
formula cannot exist without a survival hypothesis.

For a compact-open function of level $n$, only the truncated fixed subtrees out to distance
$n$ are visible.  Thus regular classes fall into finitely many **level-$n$ strata**, determined
by:

- the determinant shell;
- split, unramified-quadratic, or ramified-quadratic core type;
- trace and determinant modulo a fixed power of the maximal ideal;
- $\min(c_F,n)$ or $\min(c_L,n)$;
- the local torus-norm coset.

Residue characteristic two requires the centralizer algebra itself in this list; a
discriminant square class is not enough.

### 9.2 The finite triangular system

Let $S_{F,j}$ be the normalized characteristic function of the stabilizer of a length-$j$
segment in $X_F$, with $S_{F,0}=\mathbf1_{K_F}$.  Let $S_{L,j}$ be the corresponding function
upstairs.  Choose representatives $C_0,\ldots,C_r$ of the finitely many level-$n$ regular
strata in the norm image.  Put

$$
A_{ij}=I_{\gamma_i}(S_{F,j}),
\qquad
B_{ij}=I_{\delta_i}^\sigma(S_{L,j}),
\tag{9.2}
$$

where $(\gamma_i,\delta_i)$ is a matching pair in $C_i$.

Order the strata from deepest fixed subtree to shallowest, separately for vertex and edge
cores.  A length-$j$ segment can be fixed only when it lies in the truncated fixed subtree.
At the largest visible $j$ for a stratum, the core segment occurs and has nonzero reciprocal
stabilizer volume.  Consequently the matrices obtained from (9.2) by selecting one new segment
length at each depth are triangular with nonzero diagonal.

The diagonal entries are explicit.  If $\mathcal S$ is the unique new core segment, its
contribution is

$$
\frac{\operatorname{vol}(\operatorname{Stab}(\mathcal S))}
{\operatorname{vol}(T\cap\operatorname{Stab}(\mathcal S))}
\tag{9.3}
$$

downstairs, and the same quotient with the twisted centralizer upstairs.  Every group in (9.3)
is a compact open subgroup whose index is computed in a finite quotient of
$\mathrm{GL}_2(\mathcal O/\mathfrak p^m)$ or of a quadratic order.  Thus all entries, and hence
all solutions, are explicit rational functions of the relevant residue cardinalities and
unit indices.

Suppose a twisted invariant function

$$
\phi=\sum_{j=0}^n b_jS_{L,j}
\tag{9.4}
$$

is prescribed.  Its value vector on the strata is $v_i=\sum_jB_{ij}b_j$.  Solve

$$
\sum_jA_{ij}a_j=v_i
\tag{9.5}
$$

by backward substitution, deepest stratum first.  The result

$$
f=\sum_ja_jS_{F,j}
\tag{9.6}
$$

matches $\phi$ on every visible norm stratum.  Add slice functions supported in the finitely
many nonnorm strata to force zero there.  This is an algorithm, not a dimension count: the
support implication proves triangularity, (9.3) proves the diagonal is nonzero, and backward
substitution gives each coefficient.

### 9.3 Tail recurrences near the scalar locus

A fixed-level function encounters regular classes of arbitrarily large depth as they approach
a scalar.  It is therefore not enough to solve a finite list and ignore the tail.  The tail is
controlled by a recurrence.

Once the fixed tube contains every segment of length at most $n$ meeting a chosen core, moving
one layer deeper attaches identical finite branches to each boundary vertex.  Every new branch
has one initial edge and $q$ forward edges.  Weighted vertex and segment counts therefore obey
a linear recurrence with coefficients determined by $q$ and compact-stabilizer indices.  On
the twisted side the same statement holds with $q_L$ and the semilinear fixed branches.  Norm
descent identifies the orbit of boundary branches and converts the recurrence by the tangent
factor (3.8).

Concretely, let $V_c$ and $E_c$ denote weighted fixed vertices and oriented edges visible at
depth $c$.  Away from the core,

$$
V_{c+1}-V_c=q^c u_c,
\qquad
E_{c+1}-E_c=(q+1)q^c u_c,
\tag{9.7}
$$

where $u_c$ is the reciprocal torus-stabilizer index of one boundary orbit.  Higher segment
counts have the same first-order form after shifting the length.  The exact value of $u_c$
depends on the multiplier order, but its transition
$u_{c+1}/u_c$ is the index of one principal-unit layer and is therefore explicit.  The
ramified norm map sends that layer through the trace map on its additive quotient; kernel and
cokernel sizes give the conversion factor.

It follows that if (9.5) holds through the first complete layer beyond level $n$, then the two
sides satisfy the same recurrence and match for every deeper class.  The finite system must
therefore include the core strata, all depths through $n$, and one recurrence-check row for
each core parity.  No infinite interpolation is required.

The alternating vertex-edge combination illustrates the mechanism.  New terminal vertices
and their incident edges cancel, so its tail is constant.  More general segment combinations
have nonconstant tails, but (9.7) determines them from finitely many initial values.

### 9.4 The ramified invariant-level theorem

Call a compact-open function on $G(L)$ **selected invariant of level $n$** if it is a finite
linear combination of determinant-shell translates of segment stabilizer functions and of
indicators of trace-norm congruence strata modulo $\mathfrak p_L^n$.  This class contains the
invariant functions used to isolate the selected local packets.  It does not contain arbitrary
noninvariant wild cosets.

**Theorem 9.1 (ramified invariant-level matching).** Let $L/F$ be finite cyclic, possibly
ramified, and let $\phi$ be selected invariant of level $n$.  Then there is an explicitly
recursive compactly supported $f$ on $G(F)$ such that

$$
I_\gamma(f)=I_\delta^\sigma(\phi)
\tag{9.8}
$$

for every matching strongly regular pair and $I_\gamma(f)=0$ on regular nonnorm strata.  The
coefficients of $f$ are obtained from (9.3)--(9.6), with the tail rows of Section 9.3.  The
construction commutes with central translation, inversion, and twisting through determinant
and norm.

**Proof strategy.** Partition by finite invariant data, solve the fixed-segment system on the
visible strata, and use the common tail recurrence near the scalar boundary.  Use regular
descent to remove the finitely many nonnorm values.

**Proof.** Compact support leaves finitely many determinant shells.  On each shell, the level
$n$ data produce finitely many core and depth strata.  Triangularity and the nonzero core
weights solve (9.5).  Include one full transition layer; Section 9.3 then propagates equality
to every deeper regular class.  The regular norm fiber makes the twisted value single-valued.
The norm coset is locally constant on each regular stratum, so Theorem 8.1 supplies finite
corrections supported on nonnorm pieces.  Central translation, inversion, and norm twisting
preserve fixed subtrees and multiply matching values by the same scalar. $\square$

This theorem is the ramified matching statement at the level of invariant compact data.  It
does not say that $\mathbf1_{K_L}$ transfers to $\mathbf1_{K_F}$, nor that the transfer is
unique as a function.  It gives a canonical recursive representative once the segment basis
and stratum ordering are fixed.

## 10. Iwahori and congruence matching

### 10.1 Oriented edges and relative position

Let $I_F\subset K_F$ and $I_L\subset K_L$ be the standard Iwahori subgroups.  An $I$-coset is
an oriented edge

$$
\Lambda_0\supset\Lambda_1\supset\varpi\Lambda_0,
\qquad \dim_k(\Lambda_0/\Lambda_1)=1.
\tag{10.1}
$$

The condition

$$
x^{-1}\gamma x\in I_F
$$

means that $\gamma$ fixes the oriented edge.  The twisted condition

$$
y^{-1}\delta\sigma(y)\in I_L
$$

means that $T_\delta$ fixes the corresponding semilinear edge.  Thus their orbital integrals
are weighted fixed-edge counts.

The second elementary Iwahori double coset has relative Weyl position $w$.  It counts edges
sent across their initial vertex rather than fixed.  Relative position is stable under base
extension and under the norm descent of a cyclic gallery.  Consequently the same triangular
method applies to the two-cell Iwahori space and, by convolution, to any finite part of the
affine Iwahori algebra.

Volumes must be retained:

$$
\operatorname{vol}(I_F)=\frac1{q_F+1},
\qquad
\operatorname{vol}(I_L)=\frac1{q_L+1}.
\tag{10.2}
$$

Identifying the two characteristic functions without these factors gives the wrong fixed-edge
weight whenever $f>1$.

### 10.2 The twisted Iwahori statement

Let

$$
e_{I,F}=(q_F+1)\mathbf1_{I_F},
\qquad
e_{I,L}=(q_L+1)\mathbf1_{I_L}
$$

be the probability-normalized idempotents.  Let $\tau_{w,F}$ and $\tau_{w,L}$ be the similarly
normalized $w$-cell functions.  A chosen finite Iwahori function upstairs is a polynomial in
these cells and central translations.

**Theorem 10.1 (twisted Iwahori matching).** For every function $\phi$ in the selected finite
Iwahori subspace of $G(L)$ there is a function $f$ in the corresponding finite segment
subspace of $G(F)$ satisfying regular cyclic matching.  For unramified $L/F$, this transfer is
the restriction of the spherical/gallery base-change operation when $\phi$ is spherical.  For
ramified $L/F$, its coefficients are the edge-core and recurrence solution of Theorem 9.1.

**Proof.** Decompose the orbital integrals into fixed and relative-position edge groupoids.
The diagonal weight is nonzero because the core edge or the first edge from a core vertex has a
nonzero compact stabilizer.  Order by fixed depth and relative position; this gives the same
triangular matrix as in Section 9.2 with separate parity blocks.  Backward substitution matches
the prescribed values, and the tail recurrence propagates them.  Nonnorm strata are removed by
regular descent. $\square$

At a split local algebra $F^d$, the theorem reduces to convolution as in (2.10).  At an
unramified field place, $q_L=q_F^d$ and the probability normalization in (10.2) is essential.
At a totally ramified place, $q_L=q_F$ but the fixed-depth relation can still change; equality
of residue cardinalities does not make the extension unramified.

### 10.3 Segment stabilizers and $K_0$-level

The subgroup $K_0(\mathfrak p^n)$ stabilizes a length-$n$ segment.  Its volume is

$$
\operatorname{vol}(K_0(\mathfrak p^n))
=\frac1{q^{n-1}(q+1)}.
\tag{10.3}
$$

Indeed $K$ acts transitively on $\mathbf P^1(\mathcal O/\mathfrak p^n)$, whose cardinality is
$q^{n-1}(q+1)$.  Consequently

$$
O_\gamma(\mathbf1_{K_0(\mathfrak p^n)})
=\sum_{[\mathcal S]}
\frac{\operatorname{vol}(K_0(\mathfrak p^n))}
{\operatorname{vol}(T\cap\operatorname{Stab}(\mathcal S))},
\tag{10.4}
$$

where $\mathcal S$ runs through torus orbits of stable segments.  The twisted formula is
identical with semilinear stability.

Formula (10.4) is exact even for scalar reduction.  A residue eigenline count sees only the
first edge and fails when an order fixes several lifts.  Segment stabilizers record every lift
and its correct weight.

Applying Theorem 9.1 to the normalized functions for lengths $0,\ldots,n$ gives a transfer
matrix

$$
\mathbf B_n=(B_{ij})
\quad\longmapsto\quad
\mathbf A_n^{-1}\mathbf B_n.
\tag{10.5}
$$

This is the level-$K_0$ base-change matrix.  Its entries are finite subgroup indices and are
therefore computable without selecting a representative inside each conjugacy orbit.

### 10.4 Primitive endpoints and $K_1$-level

The subgroup $K_1(\mathfrak p^n)$ remembers a primitive generator of the terminal cyclic
quotient.  With the convention that the lower-left entry is zero and the lower-right entry is
one modulo $\mathfrak p^n$,

$$
[K:K_1(\mathfrak p^n)]=q^{2n}-q^{2n-2}.
\tag{10.6}
$$

Over each $K_0$-segment, primitive generators form a torsor under
$(\mathcal O/\mathfrak p^n)^\times$.  Projecting to a character $\eta$ uses

$$
e_\eta
=\frac1{|(\mathcal O/\mathfrak p^n)^\times|}
\sum_u\eta(u)^{-1}[u].
\tag{10.7}
$$

Orthogonality makes the sum vanish unless the torus action on the endpoint has character
$\eta$.  When it survives, the size of the free unit orbit cancels the denominator.  Thus the
$K_1$ transfer is the $K_0$ triangular system with each nonzero entry multiplied by an explicit
finite character sum.

Under base change, the endpoint character upstairs is the norm pullback of the downstairs
character.  On the residue quotient this is the finite-field norm; on principal-unit layers it
is the trace map to first order.  The conductor can drop if the character is killed by the
norm.  Therefore the correct level downstairs is determined by the surviving character layer,
not by multiplying $n$ by $e$.

**Corollary 10.2 (selected $K_0/K_1$ matching).** Every selected $K_0$- or character-projected
$K_1$-function of finite level on $G(L)$ has a germ-compatible regular transfer on $G(F)$,
computed by (10.5) and (10.7), provided the relevant character filtration lies in the selected
tame range.  If norm pullback kills the top character, the recursion automatically moves the
transfer to the lower surviving level.

The proof is the segment theorem plus finite character orthogonality.  Ramified dyadic wild
quadratic refinements are excluded for the same reason as in Section 4.4.

## 11. Level-specific matching for selected representations

### 11.1 Type functions and twisted traces

Let $J_L\subset G(L)$ be compact modulo center, stable under $\sigma$, and let $\lambda_L$ be a
finite-dimensional representation equipped with an intertwiner $a_\sigma$ satisfying
$a_\sigma^d=1$.  On a fixed central-character quotient define the twisted type function

$$
e_{\lambda_L,\sigma}(j)
=\frac{\dim\lambda_L}{\operatorname{vol}(J_L/Z_L)}
\operatorname{tr}(\lambda_L(j^{-1})a_\sigma),
\qquad j\in J_L,
\tag{11.1}
$$

and extend it by zero.  Twisted Schur orthogonality gives

$$
\operatorname{tr}(\Pi(e_{\lambda_L,\sigma})A_\sigma)
=\operatorname{tr}igl(A_\sigmamid
\operatorname{Hom}_{J_L}(\lambda_L,\Pi)igr).
\tag{11.2}
$$

If the selected type occurs with multiplicity one and the normalizations agree, the right side
is one.  Downstairs the ordinary type idempotent

$$
e_{\lambda_F}(j)
=\frac{\dim\lambda_F}{\operatorname{vol}(J_F/Z_F)}
\operatorname{tr}(\lambda_F(j^{-1}))
\tag{11.3}
$$

has trace one on the selected representation.

Equality of the two traces is only a spectral check.  To use the functions in a trace formula,
we must prove their orbital matching.  In the selected families, (11.1) reduces their orbital
integrals to the segment and finite Fourier calculations already developed.

### 11.2 Principal and special types

A principal-series type is built from characters of a Borel quotient together with a
$K_0$- or $K_1$-level structure.  Twisted conjugacy on the two invariant flags sends those
characters through the norm.  The fixed-flag calculation of Section 4.2 and the endpoint
projection (10.7) therefore give the matching function.  If the restricted ratio reaches
$\nu_L^{\pm1}$, zero monodromy selects the determinant-character idempotent; it does not select
the special function.

For $\operatorname{St}_F\otimes\mu$, the minimal unramified type is the alternating Iwahori
line.  Upstairs it is the corresponding alternating semilinear edge function, twisted by
$\mu\circ N_{L/F}$.  The exact sequence (4.3) subtracts the spherical determinant line from
the two-cell induced space, so its orbital integral is the alternating fixed-edge count.
Theorem 10.1 supplies its transfer.

If $\mu$ is ramified, first restrict to a determinant shell and then multiply by the character.
On matching classes,

$$
(\mu\circ N_{L/F})(\det\delta)
=\mu(\det\gamma).
\tag{11.4}
$$

Thus the twist preserves orbital matching.  Its level is the conductor of the norm-pulled
character, with the survival qualifications of Book 86; it is not assumed to be $e$ times the
original level.

### 11.3 Depth-zero dihedral types

Let the selected parameter be induced from an unramified quadratic field $K/F$ and a regular
residue character

$$
\bar\theta:k_{q_F^2}^\times\longrightarrow\mathbf C^\times.
$$

The compact type trace on a regular residue torus is the Frobenius orbit sum

$$
\bar\theta(x)+\bar\theta(x^{q_F}).
\tag{11.5}
$$

After base change, put $M=KL$.  On the twisted side the type is labeled by
$\theta\circ N_{M/K}$.  A semilinear embedding with norm $x$ contributes

$$
(\bar\theta\circ N_{k_M/k_K})(y)=\bar\theta(x).
$$

The conjugate embedding contributes $\bar\theta(x^{q_F})$.  All other terms lie in free finite
orbits under a nontrivial additive character and sum to zero.  Stabilizers are the unit groups
of the same descended torus, so their quotient volumes agree after the transfer factor.

If $K\subset L$, the base-changed parameter splits into two characters.  The two terms in
(11.5) then become the two invariant-flag terms of the principal-series type upstairs.  This is
the level-function form of the discrete-to-principal boundary; no supercuspidal type is asserted
upstairs.

### 11.4 Tame positive-depth dihedral types

Let $(K/F,\theta)$ be a tame admissible pair.  On its last active unit layer write

$$
\theta(1+x)=\psi_K(\beta x).
\tag{11.6}
$$

The compact-induction trace is a finite Fourier transform on the trace-orthogonal complement of
$K$ in $M_2(F)$.  Upstairs, the corresponding complement for $M/L$ is obtained by scalar
extension and the phase is

$$
\psi_M(\beta x)
=\psi_K(\operatorname{Tr}_{M/K}(\beta x)).
\tag{11.7}
$$

Norm and trace are adjoint under the multiplicative-to-additive linearization of principal
units.  Hence summing a $\sigma$-orbit of upstairs phases gives the downstairs phase.  On every
paired layer, finite Fourier inversion contributes one.  On the last unpaired layer, the
Whittaker-normalized intertwiner supplies the inverse Gauss scalar, leaving equality.

More explicitly, if $V$ is a finite additive quotient and $V^\vee$ its trace dual, then

$$
\frac1{|V|}\sum_{x\in V}\psi(\langle x,y\rangle)
=\begin{cases}1,&y=0,\\0,&y\ne0.
\end{cases}
\tag{11.8}
$$

The nonstationary embedding shells vanish by (11.8).  Stationary shells are indexed by the
same norm embeddings as the regular class and produce the same torus character.  The segment
projection of Chapter 9 cancels any split fixed-tube contribution.  This proves orbital
matching on all regular annuli, including those close to the center.

The argument needs the trace pairing on each active quotient to be nondegenerate and the tame
rectifying character to be available.  Those are exactly the selected tame hypotheses.  In a
ramified dyadic wild type, a quadratic refinement can survive beyond the alternating form;
(11.8) alone does not determine its index.

### 11.5 The selected level theorem

**Theorem 11.1 (level-specific cyclic matching).** Let $\pi$ be a determinant character,
irreducible principal series, special representation, depth-zero dihedral supercuspidal, or
tame positive-depth dihedral supercuspidal in the selected local base-change domain.  Put
$\Pi=\operatorname{BC}_{L/F}(\pi)$, allowing the selected discrete-to-principal transition.
Choose the minimal type functions downstairs and the normalized twisted type functions
upstairs as in (11.1)--(11.3).  After applying the segment projection and norm-character
projection prescribed in Chapters 9 and 10, the pair has germ-compatible regular orbital
matching.  Moreover,

$$
\operatorname{tr}\pi(e_{\lambda_F})
=\operatorname{tr}(\Pi(e_{\lambda_L,\sigma})A_\sigma)=1
\tag{11.9}
$$

on the selected multiplicity line, and the corresponding traces vanish on selected packets
without that type.

Central translates, contragredients, and selected character twists satisfy the same theorem.

**Proof.** Principal and special rows are Section 11.2.  The depth-zero finite orbit sum is
Section 11.3.  Tame positive depth reduces shell by shell to the Fourier orthogonality (11.8)
and trace transitivity (11.7).  The invariant support and split-tube corrections are supplied by
Theorems 9.1 and 10.1.  Twisted and ordinary Schur orthogonality prove (11.9).  The operations in
the last sentence preserve norm, inversion, and determinant values. $\square$

The theorem proves precisely the ramified and level-specific statements needed for the
selected cyclic comparison.  It does not extrapolate from trace one to an orbital identity;
the lattice and Fourier calculations supply that identity independently.

## 12. Singular germs and scalar norms

### 12.1 Why regular matching is not enough

As $\gamma$ approaches a scalar $zI_2$, its centralizer jumps from dimension two to four and
$|D_G(\gamma)|$ tends to zero.  The unnormalized orbital integral can grow even when the test
function is locally constant.  The twisted orbit map degenerates at the corresponding scalar-
norm boundary.  A pointwise identity on the regular set therefore does not determine the
limiting distribution.

Three assertions must be separated:

1. matching on strongly regular classes;
2. matching of nilpotent germ coefficients;
3. equality of separately weighted scalar distributions.

The first has been proved.  We now establish the second and describe the third.  Quadratic
division-centralizer scalar classes form a fourth-looking term, but geometrically they belong to
the scalar-norm stratum and must be unfolded through their actual quaternionic centralizer.

### 12.2 The two split germs and the twisted germs

Translate a neighborhood of $zI_2$ to the identity and pass to the trace-zero Lie algebra.
For $\mathrm{GL}_2(F)$ there are exactly two nilpotent orbits: zero and the regular orbit of

$$
N=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$

Every nonzero nilpotent has one-dimensional image equal to its kernel and is conjugate to $N$.
Thus a normalized ordinary orbital integral has an expansion

$$
I_{z(1+X)}(f)
=\Gamma_0(X)f(z)
+\Gamma_{\mathrm{reg}}(X)\mu_{N,z}(f)
\tag{12.1}
$$

on sufficiently small regular annuli.  The zero-orbit coefficient carries the universal
square-root behavior; the regular-nilpotent coefficient is bounded after Weyl normalization.

On the twisted side, nilpotent germs are invariant distributions for the semilinear tangent
operator.  Taking the $d$th power maps its zero orbit to zero and its unique rank-one
semilinear degeneration to the ordinary regular nilpotent orbit.  On the transverse slice, the
Jacobian ratio is the transfer factor (3.8).  Consequently

$$
I_{\delta(1+Y)}^\sigma(\phi)
=\Gamma_0^\sigma(Y)c_0^\sigma(\phi)
+\Gamma_{\mathrm{reg}}^\sigma(Y)c_N^\sigma(\phi),
\tag{12.2}
$$

with the two coefficients carried to those of (12.1).  There is no third rank-two germ.

One can see this without a general germ theorem.  In a companion-matrix slice, the invariant
coordinate is the discriminant.  Summing valuation shells of an off-diagonal coordinate splits
them into shells collapsing to zero and shells converging to the rank-one nilpotent orbit.  The
first geometric series gives the square-root coefficient; the second is bounded.  Replacing
ordinary conjugation by semilinear conjugation changes the linear equation by
$1-\operatorname{Ad}(\delta)\sigma$ and hence only by the declared Jacobian.

### 12.3 Germ-compatible transfer

For the unramified unit functions, the weighted congruence descent of Chapter 5 applies on
every finite truncation of a near-scalar fixed subtree.  New lifts and new automorphisms cancel
layer by layer.  Passing to the limit identifies both germ coefficients.  Hence the unit
fundamental lemma is germ-compatible.

For the ramified segment functions, the tail recurrence (9.7) separates the two coefficients.
The alternating vertex-edge direction kills the regular-nilpotent coefficient: every new
terminal vertex is paired with its incident edge.  A small scalar-neighborhood function
controls the zero coefficient.  The resulting $2\times2$ system is triangular because the
alternating function has zero scalar value after central correction, while the neighborhood
function has nonzero zero-orbit coefficient.

**Theorem 12.1 (germ extension).** The unramified spherical matching of Theorem 7.1 and the
selected level matching of Theorem 11.1 extend across the regular singular boundary after a
unique choice of the two germ coefficients modulo distributions supported at the scalar.  The
regular-nilpotent coefficients agree under norm descent, and a central correction can prescribe
the zero-orbit coefficient without changing regular matching away from a chosen scalar
neighborhood.

**Proof.** The two-germ expansions (12.1)--(12.2) show that only two coefficients must be
matched.  Weighted unramified descent identifies both for spherical functions.  In the
ramified selected case, the segment recurrence identifies the regular coefficient, while the
finite Fourier sums of Chapter 11 introduce no new nilpotent orbit.  The scalar-neighborhood
and alternating functions give a triangular coefficient matrix with nonzero diagonal, so it
can be solved. $\square$

The qualification “modulo distributions supported at the scalar” is unavoidable.  Regular
orbital integrals do not determine the value of a test function at one central point.

### 12.4 Quadratic division-centralizer terms

Let $L/F$ be quadratic and $a\notin N_{L/F}(L^\times)$.  The representative $\delta_a$ of
(2.13) has twisted centralizer

$$
I_{\delta_a}=B_a^\times,
\qquad B_a=(L/F,a)
$$

with $B_a$ quaternion division.  Define its relative twisted orbital integral by

$$
O_{\delta_a}^\sigma(\phi)
=\int_{B_a^\times\backslash G(L)}
\phi(h^{-1}\delta_a\sigma(h))\,d\dot h.
\tag{12.3}
$$

There is no regular discriminant factor.  The quotient is compact modulo the center because
$B_a^\times/F^\times$ is anisotropic, so (12.3) converges for compactly supported $\phi$.

The correct untwisted comparison is not an orbital integral at the scalar $aI_2$ in
$G(F)$.  It is the central distribution on the quaternionic inner form $B_a^\times$.  Book 111
supplies its Haar measures and selected character sign.  Relative semisimple descent pushes
the left side of (12.3) to a locally constant function of $a$ on each compact scalar-norm
stratum.  Choose $f_{B_a}$ with that prescribed central value and with the regular elliptic
values supplied by ordinary rank-two inner-form matching.  Then the scalar-norm comparison is

$$
O_{\delta_a}^\sigma(\phi)
=f_{B_a}(aI_2).
\tag{12.4}
$$

Here the central point is viewed in $B_a^\times$, and the quotient-volume coefficient is kept
outside the local point value.  The construction is uniform on every compact-open scalar-norm
stratum: local constancy gives one prescribed value per finite stratum, while regular descent
supplies the neighboring elliptic data.  Thus (12.4) is a genuine local test-function
statement, not an identification of two orbit spaces of different dimensions.

Locally the obstruction group has order two at a nonsplit place.  Globally, the quaternion
algebras $B_a$ have an even set of ramified places.  Their local inner-form transfer signs
therefore multiply to one.  This is why the exceptional terms fit the global comparison
rather than obstruct it.

### 12.5 Central distributions

If $a=N_{L/F}(b)$, the scalar-norm class is twisted conjugate to $bI_2$ and has centralizer
$G(F)$.  Its orbital integral is the relative integral

$$
O_{bI_2}^\sigma(\phi)
=\int_{G(F)\backslash G(L)}
\phi(h^{-1}b\sigma(h))\,d\dot h,
\tag{12.5}
$$

not generally the point value $\phi(b)$.  In a determinant-one global realization it is
weighted by the volume of the corresponding relative centralizer quotient.

On the ordinary side, a central term is a point value times an arithmetic quotient volume.
No regular germ identity makes

$$
\operatorname{vol}([G]^1)f(aI_2)
$$

equal to (12.5).  The equality must be imposed by the central normalization of the global test
functions or removed symmetrically from the two trace formulas.

With a fixed $\sigma$-invariant central character, scalar multiples are combined by Fourier
projection along the norm-one idele-class center.  Split scalar norms form one projective
channel; in quadratic degree, nonnorm scalars form the nontrivial obstruction channel.  The
projective stabilizer can be larger than $I_\delta/F^\times$ by a finite index, and central
disintegration automatically supplies that index.

The final rule is therefore strict: regular matching proves no unrecorded central identity.
Every application must state whether it uses determinant-one quotients, fixed central
character, or explicit subtraction of scalar terms.

## 13. Archimedean cyclic matching

### 13.1 Split archimedean algebras

At an archimedean place of a global cyclic extension, the local étale algebra is either a
field extension $\mathbf C/\mathbf R$ or a product cyclically permuted by the Galois generator.
The product case is the smooth analogue of Section 2.3.

Let $L=F^d$ with $F=\mathbf R$ or $\mathbf C$.  For
$\delta=(\delta_0,\ldots,\delta_{d-1})$, twisted conjugation reduces the tuple to the ordinary
product $\gamma=\delta_0\cdots\delta_{d-1}$.  For Schwartz functions
$\phi_i$ whose convolutions are defined,

$$
O_\delta^\sigma(\phi_0\otimes\cdots\otimes\phi_{d-1})
=O_\gamma(\phi_0*\cdots*\phi_{d-1}).
\tag{13.1}
$$

Absolute convergence follows from rapid decay and the polynomial volume growth of the orbit
quotients.  Differentiation under the integral proves the identity for all derivatives, so the
convolution is again an admissible archimedean test function.  There is no transfer factor
beyond the common quotient Jacobian because (13.1) is a change of variables in the same group.

### 13.2 The extension $\mathbf C/\mathbf R$

Now let $L=\mathbf C$, $F=\mathbf R$, and $\sigma$ be complex conjugation.  For
$\delta\in\mathrm{GL}_2(\mathbf C)$, the ordered norm is $\delta\bar\delta$.  Its trace and
determinant are real, and regular norm fibers satisfy the same torus criterion as in Theorem
2.1.

For a split regular $\gamma$ with eigenvalues $a,b\in\mathbf R^\times$, the norm condition is

$$
a>0,qquad b>0,
\tag{13.2}
$$

because the norm from $\mathbf C^\times$ to $\mathbf R^\times$ is $z\mapsto|z|^2$.  For an
elliptic $\gamma$, its centralizer is $\mathbf C^\times$ and

$$
\mathbf C\otimes_\mathbf R\mathbf C\simeq\mathbf C\times\mathbf C;
$$

the torus norm is multiplication and is surjective.  Hence every real elliptic regular class
is a stable norm.

Let $D_k$ be the weight-$k$ discrete series of $\mathrm{GL}_2(\mathbf R)$, $k\ge2$, with the
chosen central twist.  Its parameter restricts to $W_\mathbf C$ as two characters, so its
cyclic base change is a principal series $\Pi_k$ of $\mathrm{GL}_2(\mathbf C)$.  Normalize
complex conjugation on its Whittaker model as in Section 4.1.  The selected character identity
(4.5) gives, for an elliptic real norm

$$
\gamma=rR_\theta,qquad
R_\theta=
\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix},
$$

the normalized value

$$
|D_G(\gamma)|^{1/2}\Theta_{D_k}(\gamma)
=-2\,\operatorname{sgn}(r)^k
\sin((k-1)\theta),
\tag{13.3}
$$

because $|D_G(\gamma)|^{1/2}=2|\sin\theta|$.  The twisted character of $\Pi_k$ has the same
value on every matching twisted class.

Choose a smooth compact-mod-center Euler--Poincare function $f_k$ on
$\mathrm{GL}_2(\mathbf R)$ with trace one on $D_k$, zero on the other tempered infinitesimal
characters under consideration, and zero split regular orbital integral.  On the elliptic set,

$$
O_{rR_\theta}(f_k)
=-\operatorname{sgn}(r)^k
\frac{\sin((k-1)\theta)}{\sin\theta}.
\tag{13.4}
$$

To construct its twisted partner, use the regular slice on
$\mathrm{GL}_2(\mathbf C)$ and prescribe the normalized orbital function given by (13.4) on
the norm fiber.  The sine quotient is smooth on $0<\theta<\pi$ and has finite limits at the
endpoints.  A partition of unity and rapid central cutoff give a Schwartz function $\phi_k$.
The two-germ calculation fixes its endpoint correction.  Thus

$$
I_{rR_\theta}(f_k)=I_\delta^\sigma(\phi_k)
\tag{13.5}
$$

for every matching elliptic pair.  On positive split norm classes, the same construction uses
the split character row; if the global comparison is cuspidal, one chooses the Euler function
so that the parabolic channel is absent.

This construction does not identify $\phi_k$ with a pointwise character.  It realizes the
required orbital function by archimedean descent and fixes its spectral scalar by the twisted
trace of $\Pi_k$.

### 13.3 Weight and singular-endpoint checks

As $\theta\to0$,

$$
\frac{\sin((k-1)\theta)}{\sin\theta}\longrightarrow k-1.
\tag{13.6}
$$

Thus the ordinary orbital integral in (13.4) has a finite limit, while the normalized integral
tends to zero.  The twisted partner has the same behavior by (13.5).  This is the archimedean
counterpart of the finite-place zero germ for a cuspidal Euler function.

The hypothesis $k\ge2$ is essential.  At $k=1$, the limiting representation has formal degree
zero and there is no trace-one discrete-series Euler function with the stated cuspidal orbital
properties.  The central twist must also be compatible with complex norm: a scalar
$z\in\mathbf C^\times$ has real norm $|z|^2$, so a prescribed real central character is pulled
back along that map.

At complex base places there is no nontrivial finite field extension, only split product
algebras in the global localization.  Hence Sections 13.1 and 13.2 exhaust the archimedean
cyclic cases.

## 14. Assembly in the twisted trace comparison

### 14.1 Restricted tensor products

Let $E/F$ now be a cyclic extension of number fields of prime degree $\ell$, with generator
$\sigma$.  Book 113 constructs the absolutely convergent twisted geometric distribution for
admissible test functions having one strongly cuspidal local factor.  Choose a restricted
tensor

$$
\phi=\bigotimes_v\phi_v
$$

on $\mathrm{GL}_2(\mathbf A_E)$.  At almost every finite place, the extension and all data are
unramified and $\phi_v$ is the hyperspecial unit.  At split places use the convolution transfer
(2.10).  At unramified field places put

$$
f_v=b_{E_v/F_v}(\phi_v).
$$

At ramified places choose the invariant, Iwahori, congruence, or selected type transfer of
Chapters 9--11.  At real places use Chapter 13.  The resulting functions form a restricted
tensor

$$
f=\bigotimes_vf_v
$$

because almost every transfer is the hyperspecial unit.

Local centralizer measures are chosen from one global invariant measure on each rational norm
centralizer.  Quotient measures then factor, and any finite rescaling cancels between the
global centralizer coefficient and the product of orbital integrals.

### 14.2 Matching regular elliptic terms

Let $\delta\in\mathrm{GL}_2(E)$ have regular elliptic stable norm $\gamma\in G(F)$.  The global
norm criterion is equivalent to its local versions.  At every place, the local fiber is unique
and

$$
I_{\gamma_v}(f_v)=I_{\delta_v}^\sigma(\phi_v).
\tag{14.1}
$$

Multiplying (14.1) and using the product formula for the two discriminants gives equality of
the raw adelic orbital products.  The algebraic centralizers are the same torus
$T_\gamma$, so their arithmetic volume coefficient is identical.  Hence

$$
a(\gamma)O_\gamma(f)
=a(\delta)O_\delta^\sigma(\phi).
\tag{14.2}
$$

The absolutely convergent geometric expansion of Book 113 permits (14.2) to be summed over all
regular elliptic norm classes.  There is no hidden multiplicity: the global and local regular
fibers are singletons.

At an unramified place, (14.1) is Theorem 7.1; no finite exceptional set is concealed in the
phrase “almost all.”  At a ramified selected place, it is Theorem 11.1 with its stated tame
scope.  If a desired global test function uses a wild local type outside that scope, the
comparison stops there rather than inferring an unavailable local identity.

### 14.3 Scalar and nonelliptic channels

The twisted geometric expansion has a split scalar channel, regular elliptic channel, and in
quadratic degree a division-centralizer scalar channel.  Split regular and nonsemisimple terms
cancel together after parabolic unfolding because one local factor is strongly cuspidal.  They
are not compared orbit by orbit.

For split scalar norms, compare the relative distribution (12.5) with the separately normalized
ordinary central term.  In the determinant-one realization, retain the actual scalar norm
$a$ and its quotient volume.  In a fixed-central-character realization, Fourier projection
combines scalar multiples into one projective channel.  Either method is valid; mixing their
coefficients is not.

When $\ell=2$ and $a$ is not a norm, use the quaternion algebra
$B_a=(E/F,a)$.  Locally, Chapter 12 identifies the twisted scalar-norm distribution with the
corresponding inner-form distribution.  The set of places where $B_a$ is division has even
cardinality, so the local inner-form signs multiply to one.  The global coefficient is the
volume of $B_a^\times(F)\backslash B_a^\times(\mathbf A_F)^1$, exactly the centralizer volume
appearing on the twisted side.  Thus the exceptional scalar terms match as a family.

No noncentral Jordan term survives.  On the twisted side it belongs to the semilinear
invariant-line channel; on the ordinary side its unique invariant line belongs to the same
parabolic channel.  Strong cuspidality removes the combined distribution, not each raw orbital
integral separately.

### 14.4 Spectral traces in the selected range

Suppose a global automorphic representation has selected local components and let its cyclic
base change have the normalized local intertwiners of Section 4.1.  At every place, the local
norm character identity and Weyl integration show that matching functions have equal local
selected traces:

$$
\operatorname{tr}\pi_v(f_v)
=\operatorname{tr}(\Pi_v(\phi_v)A_{\sigma,v}).
\tag{14.3}
$$

For type functions this equality is also the direct Schur-orthogonality calculation (11.9).
At unramified places it is the Satake identity (7.3).  The product of normalized local
intertwiners gives the global field-automorphism action after the global Whittaker functional is
fixed.

Equation (14.3) explains the representation-theoretic meaning of geometric matching, but it is
not used to prove (14.2).  The proof order is important:

```text
local lattice and Fourier identities
              |
              v
matching orbital integrals -----> matching global geometric terms
              |
              v
selected character identity ----> equality of selected spectral traces.
```

The vertical implication uses Weyl integration and the singular audit.  A trace identity alone
would determine only the cocenter class of a function and would not supply the orbit-by-orbit
geometric equality required by the trace formula.

### 14.5 Failure modes

The full comparison is sensitive to a short list of recurring errors.

First, norm matching is a torus norm condition.  Determinant norm alone is insufficient.
Second, the primary local identity uses normalized orbital integrals; raw equality requires the
factor (3.8).  Third, the unramified base-change homomorphism substitutes $d$th powers in
Satake variables; it does not multiply the first Hecke operator by $d$.

Fourth, a ramified unit is not declared to match another raw unit.  Ramified transfer is the
segment and Fourier combination constructed here.  Fifth, a supercuspidal parameter can become
principal after base change, so its upstairs type must be chosen from the actual restricted
parameter.  Sixth, a nonzero monodromy operator never disappears; special must not be replaced
by a determinant character.

Seventh, residue eigenlines do not control scalar-reduction classes at positive depth; full
segments and their stabilizers are required.  Eighth, regular matching does not compare central
point values.  Ninth, a quadratic nonnorm scalar has quaternion division centralizer and cannot
be discarded as singular noise.  Tenth, the tame Fourier proof does not cover primitive wild or
ramified dyadic positive-depth packets.

Finally, local orbital integrals factor, but global centralizer volumes generally do not.  The
latter contain class groups, units, and the product formula and must remain global coefficients.

## 15. The cyclic matching package

### 15.1 Main local theorem

We can now collect the local results with their exact scope.

**Theorem 15.1 (twisted orbital matching and the cyclic fundamental lemma for rank two).** Let
$L/F$ be a finite cyclic extension of nonarchimedean local fields and fix a generator $\sigma$.

1. A strongly regular ordinary class $\gamma$ has a twisted norm class if and only if

   $$
   \gamma\in N_{L/F}^{T_\gamma}(T_\gamma(L)).
   $$

   The fiber is one rational twisted class and
   $I_\delta\simeq T_\gamma$.
2. Matching is normalized by

   $$
   I_\gamma(f)=I_\delta^\sigma(\phi),
   $$

   or, in raw form, by the transfer factor (3.8).  Common centralizer measures and complementary
   quotient measures are required.
3. If $L/F$ is unramified, the hyperspecial units satisfy the unit fundamental lemma, and every
   spherical Hecke function satisfies

   $$
   I_\gamma(b_{L/F}\phi)=I_\delta^\sigma(\phi),
   \qquad
   \mathcal S_F(b_{L/F}\phi)(X_1,X_2)
   =\mathcal S_L(\phi)(X_1^d,X_2^d).
   $$

4. For arbitrary ramification, every compact regular twisted orbital datum transfers by local
   descent.  Selected invariant finite-level data have the explicit segment recursion of
   Theorem 9.1, including the tail at the scalar boundary.
5. The Iwahori, selected $K_0$, and character-projected $K_1$ functions match by fixed edges,
   segments, and finite norm-character sums.  Character levels are determined by the surviving
   norm-pulled filtration, not by a universal degree multiple.
6. Determinant, principal, special, depth-zero dihedral, and tame positive-depth dihedral type
   functions have the level-specific matching of Theorem 11.1 whenever the restricted
   parameter remains selected.  The statement includes discrete-to-principal transitions and
   excludes primitive wild and ramified dyadic wild packets.
7. Unramified spherical and selected level matching are compatible with the two nilpotent germs.
   Central distributions remain separate.  In quadratic degree, a nonnorm scalar has
   quaternion division centralizer and is matched through that inner form.
8. For every selected representation in the local base-change domain, normalized twisted
   characters satisfy (4.5), and matching type functions have equal ordinary and twisted
   selected traces.

**Proof.** The regular class and centralizer assertions are Theorem 2.1.  Chapter 3 proves the
measure conversion.  Weighted integral descent proves Theorem 6.1, and fixed-gallery descent
proves Theorem 7.1.  Chapters 8--10 prove regular, ramified invariant, Iwahori, and congruence
transfer.  Chapter 11 proves the selected type statements.  Chapter 12 proves germ
compatibility and classifies the scalar channels.  The selected character identity is Theorem
4.1. $\square$

For a split cyclic étale algebra, replace item 3 by the convolution identity (2.10).  For
$\mathbf C/\mathbf R$, use the archimedean descent and weight projectors of Chapter 13.

### 15.2 A calculation protocol

For a concrete local comparison, first compute the ordered norm and its characteristic
polynomial.  Decide whether the norm is regular, noncentral repeated, or scalar.  In the
regular case identify its quadratic étale centralizer and test the full torus norm condition.
Do not use determinant alone.

Next choose one Haar measure on the common centralizer and define both quotient measures from
it.  Compute $D_G(\gamma)$ and $D^\sigma(\delta)$ before deciding whether a raw or normalized
identity is being used.

At an unramified place, apply the Satake base-change homomorphism.  For the standard Hecke
operator use the recurrence (7.6), not a single distance shell.  At a ramified place, identify
the determinant shell, core type, fixed depth, and visible segment length; solve the triangular
system and include its tail row.  For $K_1$ data, apply the finite norm-character projector.

If the function selects a representation, restrict the complete Weil--Deligne parameter first.
Retain monodromy, allow a dihedral parameter to split, and only then choose the upstairs type.
Normalize the field-automorphism intertwiner through the Whittaker functional or the natural
determinant-character action.

Finally inspect the scalar boundary.  Match the two germ coefficients, state the central
normalization, and in quadratic degree test the scalar norm class in
$F^\times/N_{L/F}(L^\times)$.  A nontrivial class requires the quaternion division-centralizer
term.

### 15.3 Conclusion

Cyclic base change reverses direction twice.  Parameters restrict from $W_F$ to $W_L$, while
characters pull back from $F^\times$ to $L^\times$ through the norm.  On geometric classes the
same norm appears as the $d$th power of a semilinear operator.  In rank two, its centralizer is
an induced quadratic torus, so Hilbert 90 gives both the exact norm image and the uniqueness of
every regular twisted fiber.

The fundamental lemma is the integral content hidden behind that classification.  For an
unramified extension, a twisted unit orbital integral and an ordinary unit orbital integral are
weighted counts of semilinear and linear stable lattices.  Congruence-layer descent shows that
extra lifts and extra automorphisms cancel.  Fixed galleries extend the argument to the entire
spherical algebra, and the resulting operator is exactly the Satake substitution
$(X_1,X_2)\mapsto(X_1^d,X_2^d)$.

Ramification replaces hyperspecial descent by controlled finite geometry.  Vertices, oriented
edges, segments, and primitive endpoints form a triangular system whose diagonal is a compact-
stabilizer index.  Its tail recurrence reaches all the way to the scalar divisor.  Finite norm
and trace sums then supply the principal, special, depth-zero dihedral, and tame positive-depth
type identities, with an honest boundary at wild types not constructed by the preceding local
theory.

The singular analysis completes the package.  There are two rank-two nilpotent germs, their
coefficients can be matched independently, and regular identities do not determine central
terms.  In quadratic degree a nonnorm scalar descends the matrix algebra to a quaternion
division algebra, producing a genuine elliptic distribution.  Once that term and the split
scalar channel are retained, the local identities multiply with the global centralizer
coefficients of the convergent twisted geometric expansion.

The result is the complete selected matching theory required for cyclic rank-two comparison:
unramified norm matching, the unit and spherical cyclic fundamental lemmas, ramified regular
transfer, explicit finite-level and type matching, singular compatibility, scalar obstruction
terms, archimedean selectors, and the selected twisted character identity, all in one measure
and normalization ledger.
