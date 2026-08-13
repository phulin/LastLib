# The Geometric Side of the GL₂ Trace Formula

## Contents

- [Introduction](#introduction)
- [1. The geometric question](#1-the-geometric-question)
  - [1.1 From a diagonal kernel to rational orbits](#11-from-a-diagonal-kernel-to-rational-orbits)
  - [1.2 Standing hypotheses](#12-standing-hypotheses)
  - [1.3 The measure ledger](#13-the-measure-ledger)
  - [1.4 The theorem to be proved](#14-the-theorem-to-be-proved)
- [2. Projective conjugacy in degree two](#2-projective-conjugacy-in-degree-two)
  - [2.1 Characteristic polynomials and the four cases](#21-characteristic-polynomials-and-the-four-cases)
  - [2.2 Rational canonical forms](#22-rational-canonical-forms)
  - [2.3 Projective invariants](#23-projective-invariants)
  - [2.4 Stable lines and multiplicities](#24-stable-lines-and-multiplicities)
- [3. Centralizers and elliptic tori](#3-centralizers-and-elliptic-tori)
  - [3.1 The commutant of a regular matrix](#31-the-commutant-of-a-regular-matrix)
  - [3.2 Quotienting by the scalar center](#32-quotienting-by-the-scalar-center)
  - [3.3 Anisotropy and compact adelic quotients](#33-anisotropy-and-compact-adelic-quotients)
  - [3.4 Singular centralizers](#34-singular-centralizers)
- [4. Haar measures and orbital measures](#4-haar-measures-and-orbital-measures)
  - [4.1 Quotient integration](#41-quotient-integration)
  - [4.2 Local and adelic orbital integrals](#42-local-and-adelic-orbital-integrals)
  - [4.3 Factorization and rescaling](#43-factorization-and-rescaling)
  - [4.4 The elliptic coefficient](#44-the-elliptic-coefficient)
- [5. The diagonal distribution and compact truncation](#5-the-diagonal-distribution-and-compact-truncation)
  - [5.1 What the kernel theorem supplies](#51-what-the-kernel-theorem-supplies)
  - [5.2 Why direct absolute regrouping is unsafe](#52-why-direct-absolute-regrouping-is-unsafe)
  - [5.3 Rank-one truncation](#53-rank-one-truncation)
  - [5.4 Finite rearrangement on truncated regions](#54-finite-rearrangement-on-truncated-regions)
- [6. The central distribution](#6-the-central-distribution)
  - [6.1 There is one projective central class](#61-there-is-one-projective-central-class)
  - [6.2 Evaluation of the central term](#62-evaluation-of-the-central-term)
  - [6.3 Dependence on central-character conventions](#63-dependence-on-central-character-conventions)
- [7. The parabolic organization of nonelliptic elements](#7-the-parabolic-organization-of-nonelliptic-elements)
  - [7.1 Incidence with rational lines](#71-incidence-with-rational-lines)
  - [7.2 Borel coordinates](#72-borel-coordinates)
  - [7.3 Unipotent unfolding](#73-unipotent-unfolding)
  - [7.4 The exact cancellation mechanism](#74-the-exact-cancellation-mechanism)
- [8. Removing the truncation boundary](#8-removing-the-truncation-boundary)
  - [8.1 The boundary discrepancy](#81-the-boundary-discrepancy)
  - [8.2 Iwasawa coordinates in the cusp](#82-iwasawa-coordinates-in-the-cusp)
  - [8.3 A quantitative boundary estimate](#83-a-quantitative-boundary-estimate)
  - [8.4 Vanishing of split and unipotent terms](#84-vanishing-of-split-and-unipotent-terms)
- [9. Elliptic unfolding](#9-elliptic-unfolding)
  - [9.1 Orbit-by-orbit unfolding](#91-orbit-by-orbit-unfolding)
  - [9.2 Compactness in the centralizer direction](#92-compactness-in-the-centralizer-direction)
  - [9.3 Passage from local to global orbits](#93-passage-from-local-to-global-orbits)
  - [9.4 The provisional elliptic expansion](#94-the-provisional-elliptic-expansion)
- [10. Uniform bounds for orbital integrals](#10-uniform-bounds-for-orbital-integrals)
  - [10.1 The Weyl discriminant](#101-the-weyl-discriminant)
  - [10.2 Nonarchimedean orbit charts](#102-nonarchimedean-orbit-charts)
  - [10.3 Archimedean decay](#103-archimedean-decay)
  - [10.4 Global height decay](#104-global-height-decay)
- [11. Counting elliptic classes and their volumes](#11-counting-elliptic-classes-and-their-volumes)
  - [11.1 Integral representatives and height](#111-integral-representatives-and-height)
  - [11.2 Polynomial counting](#112-polynomial-counting)
  - [11.3 Polynomial torus-volume bounds](#113-polynomial-torus-volume-bounds)
  - [11.4 Absolute summability](#114-absolute-summability)
- [12. The geometric expansion](#12-the-geometric-expansion)
  - [12.1 The central-plus-elliptic formula](#121-the-central-plus-elliptic-formula)
  - [12.2 Continuity and independence of cutoffs](#122-continuity-and-independence-of-cutoffs)
  - [12.3 Equality with the spectral expansion](#123-equality-with-the-spectral-expansion)
  - [12.4 The complete simple trace formula](#124-the-complete-simple-trace-formula)
- [13. Examples and limiting phenomena](#13-examples-and-limiting-phenomena)
  - [13.1 Elliptic classes over the rational field](#131-elliptic-classes-over-the-rational-field)
  - [13.2 Finite-place support conditions](#132-finite-place-support-conditions)
  - [13.3 Approaching the singular set](#133-approaching-the-singular-set)
  - [13.4 What changes without a cuspidal factor](#134-what-changes-without-a-cuspidal-factor)
- [14. Final synthesis](#14-final-synthesis)
  - [14.1 The geometric proof ledger](#141-the-geometric-proof-ledger)
  - [14.2 The reusable distribution](#142-the-reusable-distribution)
  - [14.3 Conclusion](#143-conclusion)

## Introduction

The trace of a finite matrix can be read in two ways: from its eigenvalues or from the sum of
its diagonal entries.  An automorphic trace formula begins with the same observation, but each
side has become infinite.  The geometric diagonal is a sum over rational matrices, the space
over which it is integrated is noncompact, and rational matrices occur in several qualitatively
different kinds of conjugacy classes.  A formal rearrangement therefore does not constitute a
proof.  The central, split, unipotent, and elliptic pieces have to be separated in an order that
preserves convergence.

This book develops that separation for the simple trace formula on $G=\mathrm{GL}_2$.  The
adjective *simple* refers to a carefully chosen local test function, not to an absence of
analysis.  At one real place the test function is strongly cuspidal.  Its two-sided parabolic
transform vanishes.  Globally, that single zero removes the unique proper parabolic channel of
$\mathrm{GL}_2$.  It is the reason that split and nonsemisimple rational elements leave no term
after truncation is removed.  What survives is the scalar class and the classes whose
characteristic polynomial is irreducible over the ground field.

There are three distinct difficulties.  First comes algebra: rational conjugacy must be
classified modulo the scalar center, and each centralizer must be identified with the right
torus.  Second comes measure theory: the volume of a rational centralizer quotient and the
orbital integral use complementary quotient measures, so they cannot be normalized
independently.  Third comes convergence: even when the diagonal kernel is integrable, the sum
of the absolute values of its rational summands need not be.  The safe route is to truncate the
automorphic quotient, perform only finite or absolutely convergent rearrangements there, use
parabolic cancellation, and then prove an independent absolute estimate for the elliptic
series.

The preceding kernel theory establishes the analytic input needed here.  In particular, for
the test functions used below it constructs a smooth automorphic kernel, proves rapid decay in
both variables, identifies its integrable diagonal with the trace of a trace-class operator,
and gives the absolutely convergent cuspidal spectral expansion.  We recall the exact interface
but do not repeat the functional analysis.  Our task is the geometric half: to turn the same
diagonal integral into a measure-compatible, absolutely convergent sum of central and elliptic
orbital distributions.

The result is deliberately prior to explicit local calculation.  We define every local orbital
integral and prove that the global products and sums exist, but we do not evaluate the special
functions that occur at particular places.  That separation matters.  A local orbital formula
can be inserted into the trace formula only after one knows that the global expression it is
supposed to evaluate is an honest distribution.

## 1. The geometric question

### 1.1 From a diagonal kernel to rational orbits

Let $F$ be a number field, let $\mathbf A=\mathbf A_F$, and put

$$
G=\mathrm{GL}_{2/F},\qquad Z=\{zI:z\in\mathbf G_m\},
\qquad \overline G=G/Z.
$$

For a suitable test function $f$ the automorphic kernel on the central quotient is

$$
K_f(x,y)=\sum_{\gamma\in Z(F)\backslash G(F)}
f(x^{-1}\gamma y).
\tag{1.1}
$$

On the diagonal this becomes

$$
K_f(x,x)=\sum_{\gamma\in \overline G(F)}f(x^{-1}\gamma x).
\tag{1.2}
$$

Conjugating the index by $G(F)$ suggests grouping (1.2) by rational conjugacy classes.  For a
representative $\gamma$, a formal unfolding would produce

$$
\operatorname{vol}\bigl(
\overline G_\gamma(F)\backslash\overline G_\gamma(\mathbf A)
\bigr)
\int_{\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A)}
f(g^{-1}\gamma g)\,d\dot g.
\tag{1.3}
$$

Formula (1.3) is correct for elliptic $\gamma$.  It is not an acceptable starting point for
all $\gamma$.  The adelic quotient of a split centralizer is noncompact, the raw majorant of
(1.2) need not be integrable, and the terms killed by cuspidality disappear only after an
unipotent regrouping.  The central problem of this book is to justify exactly where (1.3) is
valid and to replace the invalid nonelliptic unfoldings by a convergent cancellation argument.

### 1.2 Standing hypotheses

We work inside the simple-trace-formula setting of Book 99, Theorem 11.1.  Thus $F$ has a real
place $v_0$, and

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times
$$

is unitary.  A local test function satisfies inverse central covariance

$$
f_v(zg)=\omega_v(z)^{-1}f_v(g).
\tag{1.4}
$$

At finite places $f_v$ is locally constant and compactly supported modulo $Z(F_v)$; at
archimedean places it is a Schwartz function modulo the center and is finite under both
maximal-compact actions.  For the geometric estimates we use the following, slightly smaller,
test space.  For a proper submultiplicative projective norm, every invariant differential
operator $D$, and every $A>0$, we require

$$
|Df_v(g)|\le C_{D,A}\|g\|_v^{-A}.
\tag{1.4a}
$$

This explicit form is the decay used in the height estimates below.  It is stronger than Book
99's one-fixed-power kernel-admissibility condition, so there is no hidden claim that every test
function admitted by the kernel theorem has the geometric expansion proved here.  Compactly
supported functions modulo the center satisfy (1.4a), including the compactly supported
pseudo-coefficients used in trace comparison.  We begin with a restricted tensor product
$f=\otimes_v f_v$ and later allow finite sums.

The distinguished factor $f_{v_0}$ is **strongly cuspidal**: for the upper triangular Borel
$B=TN$, one has

$$
\int_{N(F_{v_0})}f_{v_0}(x^{-1}tny)\,dn=0
\tag{1.5}
$$

for all $x,y\in G(F_{v_0})$ and $t\in T(F_{v_0})$.  Absolute convergence is included in this
condition.  The freedom in both $x$ and $y$ is indispensable.  After global unfolding, neither
side of a unipotent integral is fixed, and a one-sided or trace-only vanishing statement would
not reach the resulting expression.

Compactly supported modulo-center pseudo-coefficients of real discrete series provide the
intended examples.  This is the standard local real-harmonic-analysis source of the test class;
the proof below uses only the explicit decay and two-sided vanishing in (1.4a)--(1.5), not a
packet-selection property.

These hypotheses are stable under invariant differentiation and under the adjoint
$f^*(g)=\overline{f(g^{-1})}$.  They imply that the global two-sided parabolic transform

$$
f_B(x,y;t)=\delta_B(t)^{1/2}
\int_{N(\mathbf A)}f(x^{-1}tny)\,dn
\tag{1.6}
$$

vanishes identically.  Indeed, for a tensor the integral factors, and its $v_0$-factor is zero;
finite sums follow by linearity.

The associated Hilbert space $L^2_\omega$ consists of measurable functions on
$G(F)\backslash G(\mathbf A)$ satisfying $\phi(zx)=\omega(z)\phi(x)$ and square-integrable on
$[\overline G]$.  Right convolution is

$$
(R_\omega(f)\phi)(x)=
\int_{Z(\mathbf A)\backslash G(\mathbf A)}f(g)\phi(xg)\,d\bar g.
\tag{1.6a}
$$

The two covariance factors in the integrand cancel.  Thus (1.6a), rather than an integral over
$G(\mathbf A)$ with an infinite central direction, is the operator whose trace is studied.

### 1.3 The measure ledger

At every finite place normalize $|\varpi_v|_v=q_v^{-1}$; at a complex place use the square of
the ordinary complex modulus.  Choose Haar measures $dg_v$ on $G(F_v)$ and $dz_v$ on $Z(F_v)$,
with maximal compact subgroups of $G(F_v)$ having volume one at almost every finite place.
Quotient integration determines $d\bar g_v$ on $\overline G(F_v)$ by

$$
\int_{G(F_v)}\Phi(g)\,dg_v
=\int_{\overline G(F_v)}\int_{Z(F_v)}
\Phi(zg)\,dz_v\,d\bar g_v.
\tag{1.7}
$$

The restricted products give measures on the adelic groups.  The automorphic quotient

$$
[\overline G]=Z(\mathbf A)G(F)\backslash G(\mathbf A)
\tag{1.8}
$$

has finite volume in these conventions.  On $N(F)\backslash N(\mathbf A)$ we use probability
measure.  Equivalently, one may begin with self-dual local additive measures and divide their
global quotient by its covolume.  What matters for (1.6) is that the same choice is used in
local factorization and in global unfolding.

For a regular $\gamma$ choose Haar measure $dt_{\gamma,v}$ on
$\overline G_\gamma(F_v)$.  The measure $d\dot g_v$ on
$\overline G_\gamma(F_v)\backslash\overline G(F_v)$ is then defined, not chosen independently,
by

$$
\int_{\overline G(F_v)}h(g)\,d\bar g_v
=\int_{\overline G_\gamma(F_v)}
\int_{\overline G_\gamma(F_v)\backslash\overline G(F_v)}
h(tg)\,d\dot g_v\,dt_{\gamma,v}.
\tag{1.9}
$$

Compatible restricted products give the adelic version.  This convention is the backbone of
the measure bookkeeping: multiplying $dt_\gamma$ by $c>0$ divides $d\dot g$ by $c$.

### 1.4 The theorem to be proved

Write $[\gamma]_{\mathrm{ell}}$ for a $G(F)$-conjugacy class in $\overline G(F)$ represented by
a matrix with irreducible characteristic polynomial over $F$.  Define

$$
a(\gamma)=\operatorname{vol}\bigl(
\overline G_\gamma(F)\backslash\overline G_\gamma(\mathbf A)
\bigr)
\tag{1.10}
$$

and

$$
O_\gamma(f)=
\int_{\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A)}
f(g^{-1}\gamma g)\,d\dot g.
\tag{1.11}
$$

There is one projective stabilizer correction.  Put

$$
\kappa(\gamma)=
\begin{cases}
\frac12,&\operatorname{tr}(\gamma)=0,\\
1,&\operatorname{tr}(\gamma)\ne0.
\end{cases}
\tag{1.11a}
$$

The condition is invariant under scalar multiplication.  Section 3.2 proves that it is the
reciprocal of the number of components in the rational projective stabilizer.  The main result
is

$$
\boxed{
I_{\mathrm{geom}}(f)
=\operatorname{vol}([\overline G])f(1)
+\sum_{[\gamma]_{\mathrm{ell}}}\kappa(\gamma)a(\gamma)O_\gamma(f).}
\tag{1.12}
$$

The elliptic series is absolutely convergent and continuous in the admissible Schwartz
topology.  Moreover,

$$
I_{\mathrm{geom}}(f)
=\int_{[\overline G]}K_f(x,x)\,dx
=\operatorname{tr}R_\omega(f).
\tag{1.13}
$$

The kernel theorem already proves the second equality in (1.13), together with absolute
integrability of the chosen smooth diagonal.  Our proof establishes the first equality.  At the
end we combine it with the cuspidal spectral expansion supplied by the preceding theory.

## 2. Projective conjugacy in degree two

### 2.1 Characteristic polynomials and the four cases

The geometric simplification in rank two begins with elementary linear algebra.  For
$\gamma\in G(F)$ put

$$
p_\gamma(X)=X^2-s_\gamma X+d_\gamma,\qquad
s_\gamma=\operatorname{tr}(\gamma),\quad d_\gamma=\det(\gamma),
$$

and

$$
\Delta_\gamma=s_\gamma^2-4d_\gamma.
\tag{2.1}
$$

**Theorem 2.1 (rank-two classification).** Exactly one of the following occurs:

1. $\gamma$ is central;
2. $\Delta_\gamma$ is a nonzero square in $F$, and $\gamma$ is split regular semisimple;
3. $\Delta_\gamma=0$ and $\gamma$ is noncentral, in which case $\gamma$ is a scalar times a
   nontrivial unipotent matrix;
4. $p_\gamma$ is irreducible over $F$, in which case $\gamma$ is elliptic.

The four cases are invariant under multiplication by $F^\times$ and hence classify elements of
$\overline G(F)$.

**Proof.** The minimal polynomial of a two-dimensional endomorphism has degree one or two.  In
degree one the matrix is scalar.  In degree two, two distinct roots in $F$ give two independent
$F$-eigenlines and diagonalizability, which is case 2.  A repeated root belongs to $F$; after
subtracting that scalar, the matrix is a nonzero nilpotent of square zero, producing one Jordan
block and case 3.  If the polynomial has no root in $F$, it is irreducible of degree two, which
is case 4.  Scaling by $z\in F^\times$ multiplies the roots by $z$ and $\Delta$ by $z^2$, so it
does not change the alternative.  $\square$

The term *elliptic* is global here: it means that the connected centralizer is anisotropic
modulo $Z$ over $F$.  It does not mean that $\gamma$ is elliptic at every completion.  A
quadratic field $E/F$ may split at some places, and the local component of a globally elliptic
element is then locally split.

### 2.2 Rational canonical forms

The classification becomes useful only after conjugacy, rather than merely eigenvalue type, is
under control.

**Proposition 2.2.** Two regular matrices in $M_2(F)$ are conjugate by $G(F)$ if and only if
they have the same characteristic polynomial.

**Proof.** Equality of characteristic polynomials is necessary.  Conversely, a regular matrix
has minimal polynomial of degree two, equal to its characteristic polynomial.  Choose a vector
$v$ that is not an eigenvector over $F$; then $(v,\gamma v)$ is a basis.  In this basis $\gamma$
has the companion matrix

$$
C(s,d)=\begin{pmatrix}0&-d\\1&s\end{pmatrix}.
\tag{2.2}
$$

Thus every regular matrix with characteristic polynomial $X^2-sX+d$ is conjugate to the same
companion matrix.  $\square$

For split regular matrices one may instead use $\operatorname{diag}(a,d)$ with $a\ne d$, where
the unordered pair $\{a,d\}$ is the conjugacy invariant.  For the nonsemisimple case every
matrix is conjugate to

$$
z\begin{pmatrix}1&1\\0&1\end{pmatrix}.
\tag{2.3}
$$

Indeed, every nonzero nilpotent endomorphism of a two-dimensional vector space has a basis in
which it is $\begin{psmallmatrix}0&1\\0&0\end{psmallmatrix}$.  Modulo rational scalars, (2.3)
therefore gives a single nontrivial unipotent conjugacy class.  This does not mean that its
trace-formula contribution is a single convergent orbital integral; its centralizer quotient
has precisely the parabolic noncompactness that necessitates regrouping.

### 2.3 Projective invariants

For a noncentral matrix define

$$
j(\gamma)=\frac{s_\gamma^2}{d_\gamma},
\qquad
D(\gamma)=\frac{\Delta_\gamma}{d_\gamma}=j(\gamma)-4.
\tag{2.4}
$$

Both are unchanged by scalar multiplication and conjugacy.  If $s_\gamma\ne0$, scale to trace
one.  The normalized characteristic polynomial is then
$X^2-X+j(\gamma)^{-1}$, so $j(\gamma)$ determines the projective rational conjugacy class.
When $s_\gamma=0$, all matrices have $j=0$ and the determinant square class remains necessary:

$$
\begin{pmatrix}0&-d\\1&0\end{pmatrix}
$$

and the analogous matrix with $d'$ are projectively conjugate exactly when
$d/d'\in F^{\times2}$.  This exceptional fiber is a useful warning against treating $j$ as a
global coordinate on the entire adjoint quotient.

The eigenvalue-ratio interpretation explains (2.4).  Over a splitting field, if
$r=\lambda_1/\lambda_2$, then

$$
j=r+r^{-1}+2,\qquad D=r+r^{-1}-2.
\tag{2.5}
$$

Thus exchanging the eigenvalues replaces $r$ by $r^{-1}$ and changes neither invariant.  The
singular value $D=0$ is exactly $r=1$, where regular semisimple classes meet the central and
unipotent loci.

### 2.4 Stable lines and multiplicities

Let $\mathscr L=\mathbf P^1(F)$ be the set of rational lines in $F^2$.  It is naturally
$B(F)\backslash G(F)$, with the convention that a right coset records the inverse image of the
standard line.  For a noncentral nonelliptic $\gamma$, define

$$
e(\gamma)=\#\{L\in\mathscr L:\gamma L=L\}.
\tag{2.6}
$$

Then

$$
e(\gamma)=
\begin{cases}
2,&\gamma\text{ split regular},\\
1,&\gamma\text{ nonsemisimple}.
\end{cases}
\tag{2.7}
$$

The proof is immediate from the eigenspaces: stable lines are precisely eigenlines.  The point
of recording $e(\gamma)$ is combinatorial.  For every finitely supported function $\Phi$ on the
noncentral nonelliptic elements,

$$
\sum_\gamma\Phi(\gamma)
=\sum_{L\in\mathscr L}
\sum_{\substack{\gamma L=L\\\gamma\ \mathrm{noncentral}}}
e(\gamma)^{-1}\Phi(\gamma).
\tag{2.8}
$$

Each matrix is counted once for every stable line and then divided by the number of such lines.
We shall apply (2.8) only with finite cutoffs in place.  Its infinite formal version is not used
to justify a conditionally convergent rearrangement.

## 3. Centralizers and elliptic tori

### 3.1 The commutant of a regular matrix

Orbital integrals live on a quotient by the centralizer, so the centralizer must be identified
before any measure is assigned.

**Proposition 3.1.** If $\gamma\in G(F)$ is regular, then

$$
\operatorname{Cent}_{M_2(F)}(\gamma)=F[\gamma],
\qquad G_\gamma(F)=F[\gamma]^\times.
\tag{3.1}
$$

The same identity holds functorially after every extension of scalars.

**Proof.** Choose a cyclic vector $v$ as in Proposition 2.2.  If $A$ commutes with $\gamma$,
write $Av=av+b\gamma v$.  Commutation then forces

$$
A(\gamma v)=\gamma Av=a\gamma v+b\gamma^2v.
$$

Thus $A=a+b\gamma$ on the basis $(v,\gamma v)$.  Conversely every polynomial in $\gamma$
commutes with it.  The invertible elements are exactly the units of the quadratic algebra.
The cyclic-vector argument is unchanged after scalar extension.  $\square$

Consequently

$$
F[\gamma]\simeq
\begin{cases}
F\times F,&\gamma\text{ split regular},\\
E,&\gamma\text{ elliptic, with }E/F\text{ quadratic}.
\end{cases}
\tag{3.2}
$$

In the first case $G_\gamma$ is a split torus; in the second it is
$\operatorname{Res}_{E/F}\mathbf G_m$.

### 3.2 Quotienting by the scalar center

The local orbital integrals use the connected projective centralizer

$$
\overline G_\gamma=G_\gamma/Z.
\tag{3.3}
$$

For an elliptic element this is

$$
T_E=(\operatorname{Res}_{E/F}\mathbf G_m)/\mathbf G_m.
\tag{3.4}
$$

There is a useful comparison with the norm-one torus
$T_E^1=\ker(N_{E/F}:\operatorname{Res}_{E/F}\mathbf G_m\to\mathbf G_m)$.
The map of $F$-tori

$$
E^\times/F^\times\longrightarrow E^1,\qquad x\longmapsto x/\sigma(x),
\tag{3.5}
$$

is an isomorphism of $F$-tori.  After base change to a separable closure, write an element of
$E^\times$ as $(a,b)$.  The source has coordinate $a/b$, the norm-one target has coordinate
$(u,u^{-1})$, and (3.5) sends $a/b$ to $(a/b,b/a)$.  It is therefore an isomorphism after a
faithfully flat base change, hence over $F$.  On $F$-points its surjectivity is the familiar
Hilbert theorem 90.  We use (3.4), which is canonically the projective centralizer; (3.5) is
used to see anisotropy and compactness.

One must distinguish this connected centralizer from the stabilizer of the *projective* rational
element.  Set

$$
C_\gamma(F)=
\{\bar g\in\overline G(F):g^{-1}\gamma g\in F^\times\gamma\}.
\tag{3.5a}
$$

If $s_\gamma\ne0$, taking traces in $g^{-1}\gamma g=z\gamma$ forces $z=1$, so
$C_\gamma(F)=\overline G_\gamma(F)$.  If $s_\gamma=0$, determinants force $z=\pm1$.
The nontrivial automorphism of the quadratic algebra $F[\gamma]$ is implemented by an
$F$-linear automorphism of the two-dimensional space and sends $\gamma$ to $-\gamma$.
Consequently

$$
[C_\gamma(F):\overline G_\gamma(F)]
=\begin{cases}2,&s_\gamma=0,\\1,&s_\gamma\ne0.\end{cases}
\tag{3.5b}
$$

This is the exceptional Weyl symmetry of a projective involution.  Local orbital integrals in
this book and the next one continue to use the connected quadratic centralizer
$\overline G_\gamma$.  Rational orbit unfolding must therefore include the reciprocal index
$\kappa(\gamma)$ from (1.11a).  Omitting it would double every trace-zero elliptic term.

At a place $v$ where $E\otimes_FF_v\simeq F_v\times F_v$, the local quotient torus is split
and noncompact.  This does not conflict with global anisotropy.  Compactness concerns the
adelic rational quotient, not each local factor separately.

### 3.3 Anisotropy and compact adelic quotients

**Proposition 3.2.** If $E/F$ is a quadratic field, $T_E$ has no nontrivial $F$-rational
character.  Hence

$$
T_E(F)\backslash T_E(\mathbf A)
\tag{3.6}
$$

is compact.

**Proof.** Over a separable closure, the character lattice of
$\operatorname{Res}_{E/F}\mathbf G_m$ is generated by $e_1,e_2$, and the scalar subtorus pairs
with $e_1+e_2$.  The quotient torus has character lattice generated by $e_1-e_2$.  The nontrivial
element of $\operatorname{Gal}(E/F)$ sends this generator to its negative, so the invariant
sublattice is zero.  This is anisotropy.

For completeness, compactness can be seen idelically.  The quotient in (3.6) is

$$
\mathbf A_E^\times/(E^\times\mathbf A_F^\times).
\tag{3.6a}
$$

The idele module of an embedded $a\in\mathbf A_F^\times$ is $|a|_{\mathbf A_F}^2$, and the
idele-module map of $\mathbf A_F^\times$ is onto $\mathbf R_{>0}$.  Every class in (3.6a)
therefore has a representative of $E$-idele module one.  The norm-one idele class group
$E^\times\backslash\mathbf A_E^1$ is compact: choose ideal representatives from the finite
ideal class group, reduce every finite idele to a compact unit group, and use the unit theorem
to reduce the logarithms of the archimedean coordinates to a compact fundamental
parallelepiped.  Thus (3.6a), a continuous quotient of that compact group, is compact.
$\square$

Compactness proves finiteness of $a(\gamma)$ for elliptic $\gamma$.  It also explains why no
truncation is needed in the centralizer direction of an elliptic orbit.  For the split torus the
character $a/d$ is rational and supplies a noncompact real direction; this is exactly the
direction absorbed into the parabolic cancellation.

### 3.4 Singular centralizers

If $\gamma=zI$, then $G_\gamma=G$.  Its orbit is a point and it must be handled before any
regular-orbit formula.  If
$\gamma=z(1+N_0)$ with $N_0\ne0$ nilpotent, a direct calculation gives

$$
G_\gamma=\left\{
\begin{pmatrix}a&b\\0&a\end{pmatrix}:a\in\mathbf G_m, b\in\mathbf G_a
\right\}=ZN.
\tag{3.7}
$$

Thus $\overline G_\gamma\simeq N$.  Although $N(F)\backslash N(\mathbf A)$ is compact, the
quotient of $\overline G(\mathbf A)$ by this centralizer still runs down the split torus cusp.
Treating (3.7) as though it were an elliptic torus would therefore miss the divergence that
truncation is designed to control.

The four algebraic types now have their geometric meaning:

$$
\begin{array}{c|c|c}
\text{type}&\overline G_\gamma&\text{treatment}\\ \hline
\text{central}&\overline G&\text{one constant term}\\
\text{split regular}&\text{split one-dimensional torus}&\text{parabolic regrouping}\\
\text{nonsemisimple}&N&\text{parabolic regrouping}\\
\text{elliptic}&T_E\text{ anisotropic}&\text{orbital unfolding}.
\end{array}
\tag{3.8}
$$

This table is a guide to the proof, not merely a classification: each row has a different
convergence mechanism.

## 4. Haar measures and orbital measures

### 4.1 Quotient integration

Let $H$ be a closed unimodular subgroup of a unimodular locally compact group $L$.  Haar
measures $dh$ and $d\ell$ determine a unique invariant measure $d\dot\ell$ on $H\backslash L$
such that

$$
\int_L\Phi(\ell)\,d\ell
=\int_{H\backslash L}\int_H\Phi(h\ell)\,dh\,d\dot\ell
\tag{4.1}
$$

for compactly supported continuous $\Phi$.  All groups used below are unimodular: reductive
groups and tori are unimodular, as is the one-dimensional unipotent group $N$.

There are two successive quotients in an elliptic term.  First, $dt_\gamma$ and $d\bar g$
determine the orbital measure $d\dot g$ on
$\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A)$.  Second, $dt_\gamma$ determines
the measure on
$\overline G_\gamma(F)\backslash\overline G_\gamma(\mathbf A)$.  These are the same
$dt_\gamma$.  Using unrelated normalizations would insert an invisible scalar into every
geometric coefficient.

### 4.2 Local and adelic orbital integrals

For a regular element $\gamma\in G(F_v)$ define

$$
O_{\gamma,v}(f_v)=
\int_{\overline G_\gamma(F_v)\backslash\overline G(F_v)}
f_v(g^{-1}\gamma g)\,d\dot g_v.
\tag{4.2}
$$

Central covariance makes the integrand a well-defined section with the fixed representative
$\gamma$.  Replacing $\gamma$ by $z\gamma$, $z\in F_v^\times$, multiplies the value by
$\omega_v(z)^{-1}$.  For a rational scalar $z\in F^\times$, the product of these factors is one,
so the global distribution depends only on the projective rational class.

At a finite place the integral in (4.2) is absolutely convergent because the inverse image of a
compact subset of the regular orbit is compact modulo the centralizer.  At an archimedean place
the orbit map has at most exponential volume growth in Cartan coordinates, while a
Harish--Chandra Schwartz function has decay stronger than the corresponding growth.  Uniformity
as $\gamma$ approaches the singular set requires more work and is treated in Chapter 10.

The adelic orbital integral is

$$
O_\gamma(f)=
\int_{\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A)}
f(g^{-1}\gamma g)\,d\dot g.
\tag{4.3}
$$

For elliptic $\gamma$ it is absolutely convergent.

### 4.3 Factorization and rescaling

Choose the local centralizer measures uniformly as follows.  At every finite place give the
maximal compact subgroup of $T_E(F_v)$ volume one.  At a split real place transport $d^\times r$
through $T_E(\mathbf R)\simeq\mathbf R^\times$, and at a nonsplit real place give the compact
circle probability measure; use the analogous polar convention at complex places.  These
choices agree with the usual unramified convention at almost every place.  If $v$ is outside a
finite set containing the residue-characteristic-two places, the ramification of $E/F$, and the
denominators of $\gamma$, then $T_E$ extends to a smooth torus over $\mathcal O_v$, the orbit of
$\gamma$ meets the hyperspecial compact in one integral orbit, and quotient integration gives

$$
O_{\gamma,v}(f_v)=1.
\tag{4.3a}
$$

Here $f_v$ is the normalized spherical unit.  To verify the assertion, reduce a primitive
integral representative modulo $\varpi_v$.  Its discriminant is a unit, so its centralizer is
smooth and conjugacy is smooth transverse to that centralizer.  Hensel lifting identifies the
integral fiber with the orbit of $K_v$; both the centralizer compact and $K_v$ have volume one,
which gives (4.3a).  Thus only finitely many local factors differ from one for a fixed rational
class.  The adelic quotient and the integrand are genuine restricted products, and finite Fubini
gives

$$
O_\gamma(f)=\prod_vO_{\gamma,v}(f_v)
\tag{4.4}
$$

for a factorizable test function.  This uses only the elementary good-place value (4.3a); the
values at the finitely many bad or level places belong to the local orbital analysis of the next
book.  For a finite sum $f=\sum_i\otimes_v f_{i,v}$, linearity instead gives

$$
O_\gamma(f)=\sum_i\prod_vO_{\gamma,v}(f_{i,v}).
\tag{4.4a}
$$

If $dt_\gamma$ is replaced by $c\,dt_\gamma$, then

$$
a(\gamma)\longmapsto c\,a(\gamma),
\qquad O_\gamma(f)\longmapsto c^{-1}O_\gamma(f).
\tag{4.5}
$$

Thus $\kappa(\gamma)a(\gamma)O_\gamma(f)$ is independent of this auxiliary normalization.  It
still depends
on the initially fixed measure $d\bar g$ on $\overline G(\mathbf A)$, exactly as the operator
trace does.

### 4.4 The elliptic coefficient

For elliptic $\gamma$ the volume (1.10) is finite by Proposition 3.2.  Its occurrence can be
derived rather than memorized.  The rational orbit of the projective element is
$C_\gamma(F)\backslash\overline G(F)$.  The summand is invariant under $C_\gamma(F)$: if
$c^{-1}\gamma c=z\gamma$ with $z\in F^\times$, then its covariance factor is
$\omega(z)^{-1}=1$.  When this orbit is unfolded against the automorphic quotient,
the integration domain becomes

$$
C_\gamma(F)\backslash\overline G(\mathbf A).
$$

By (3.5b), passage from $C_\gamma(F)$ to its connected subgroup
$\overline G_\gamma(F)$ is a finite cover of degree $\kappa(\gamma)^{-1}$.  Give the finite
quotient counting measure.  Then insert the intermediate adelic connected centralizer and apply
(4.1):

$$
\begin{aligned}
&\int_{C_\gamma(F)\backslash\overline G(\mathbf A)}
f(x^{-1}\gamma x)\,dx\\
&\quad=\kappa(\gamma)
\operatorname{vol}\bigl(
\overline G_\gamma(F)\backslash\overline G_\gamma(\mathbf A)
\bigr)
\int_{\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A)}
f(g^{-1}\gamma g)\,d\dot g\\
&\quad=\kappa(\gamma)a(\gamma)O_\gamma(f).
\end{aligned}
\tag{4.6}
$$

This calculation is legitimate orbit by orbit.  Passing from one orbit to the infinite sum of
elliptic orbits will be justified only after the uniform estimates of Chapters 10 and 11.

## 5. The diagonal distribution and compact truncation

### 5.1 What the kernel theorem supplies

Book 99, Theorem 11.1 proves the following statement for its kernel-admissible test class.
Condition (1.4a) implies that fixed-power admissibility, so the theorem applies to every test
function used here without changing its central character, compact types, level, or measures.

**Kernel input.** The series (1.1), and every series obtained by invariant differentiation,
converges absolutely and locally uniformly on $G(\mathbf A)\times G(\mathbf A)$.  It is the
canonical smooth kernel of a trace-class operator $R_\omega(f)$, it is cuspidal and rapidly
decreasing in both variables, and

$$
\int_{[\overline G]}|K_f(x,x)|\,dx<\infty,
\qquad
\operatorname{tr}R_\omega(f)=
\int_{[\overline G]}K_f(x,x)\,dx.
\tag{5.1}
$$

More quantitatively, if $\operatorname{ht}(x)\ge1$ is the rank-one cusp height, then for all
$A,B\ge0$ and invariant differential operators $D_x,D_y$,

$$
|D_xD_yK_f(x,y)|
\le C_{A,B,D_x,D_y}(f)
\operatorname{ht}(x)^{-A}\operatorname{ht}(y)^{-B}.
\tag{5.2}
$$

The coefficient is a continuous seminorm in finitely many Schwartz seminorms of $f$.  This
input rests on projective rational-point counting, vanishing of kernel constant terms, cuspidal
Sobolev estimates, and a two-sided Hilbert--Schmidt factorization.  Those results do more than
show that some almost-everywhere kernel exists: they identify the periodized series with its
canonical smooth representative, so its pointwise diagonal in (5.1) is legitimate.

We will not import a geometric expansion from that theorem.  Only (5.1), (5.2), local uniform
periodization, and the global identity (1.6) are used below.  This isolates the logical task of
the present book.

### 5.2 Why direct absolute regrouping is unsafe

One might try to write

$$
\int_{[\overline G]}\sum_{\gamma\in\overline G(F)}
f(x^{-1}\gamma x)\,dx
=\sum_{[\gamma]}
\int_{\overline G_\gamma(F)\backslash\overline G(\mathbf A)}
f(x^{-1}\gamma x)\,dx.
\tag{5.3}
$$

Local uniform convergence of the kernel does not justify (5.3) on the noncompact quotient.
Nor does the integrability of the sum justify integrability of the sum of absolute values.  In
general,

$$
\int_{[\overline G]}
\sum_\gamma|f(x^{-1}\gamma x)|\,dx
\tag{5.4}
$$

diverges in the cusp.  Elements of a rational Borel can be conjugated by a large split-torus
element while their upper-right entries are compressed.  Many rational elements then meet a
fixed local support.  Their signed or complex sum has zero constant term, but absolute values
destroy precisely that cancellation.

This observation dictates the order of proof:

$$
\text{truncate}\longrightarrow
\text{regroup}\longrightarrow
\text{cancel parabolic terms}\longrightarrow
\text{bound the boundary}\longrightarrow
\text{sum elliptic terms absolutely}.
\tag{5.5}
$$

Every arrow addresses a different convergence issue.  In particular, absolute convergence of
the final elliptic series does not retroactively validate an absolute regrouping of the full
rational kernel.

### 5.3 Rank-one truncation

Reduction theory supplies finitely many cusp charts.  In each chart write an Iwasawa
decomposition

$$
x=n(u)a(y)k,\qquad
a(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix},\qquad
H(x)=|y|_{\mathbf A}\ge1,
\tag{5.6}
$$

up to bounded factors and the central quotient.  Choose a smooth function
$\chi:[0,\infty)\to[0,1]$ equal to one on $[0,1]$ and zero on $[2,\infty)$.  Patch the cusp
charts with a compact partition of unity and obtain $\chi_T$ satisfying

$$
\chi_T(x)=1\quad(H(x)\le T),\qquad
\chi_T(x)=0\quad(H(x)\ge2T),
\tag{5.7}
$$

with derivatives bounded by the corresponding powers of $T^{-1}$ in the height variable.
Define

$$
I_T(f)=\int_{[\overline G]}\chi_T(x)K_f(x,x)\,dx.
\tag{5.8}
$$

By (5.1) and dominated convergence,

$$
\lim_{T\to\infty}I_T(f)
=\int_{[\overline G]}K_f(x,x)\,dx.
\tag{5.9}
$$

No geometric rearrangement has yet been made.  Equation (5.9) uses the integrable canonical
diagonal as one function.

### 5.4 Finite rearrangement on truncated regions

The support of $\chi_T$ is compact in $[\overline G]$.  Local uniform absolute convergence of
(1.2) therefore permits termwise integration there.  To make finiteness completely explicit,
also choose an archimedean projective height cutoff $\rho_R$ on the rational index and write

$$
K_{f,R}(x,x)=\sum_{\substack{\gamma\in\overline G(F)\\H_{\mathrm{rat}}(\gamma)\le R}}
f(x^{-1}\gamma x).
\tag{5.10}
$$

Finite-place support bounds denominators of a primitive representative of $\gamma$.  The height
bound places its four entries in a bounded subset of a fixed Minkowski lattice, so (5.10) is a
finite sum.  For fixed $T$, it converges uniformly to $K_f(x,x)$ as $R\to\infty$.  We may thus
classify and regroup the finite sum, establish estimates independent of $R$, and then let
$R\to\infty$.

This double cutoff prevents two common logical errors.  The compact cutoff in $x$ controls the
automorphic cusp; the rational height cutoff controls the number of summands.  Neither one by
itself substitutes for the other.

## 6. The central distribution

### 6.1 There is one projective central class

The central elements of $G(F)$ are $zI$ with $z\in F^\times$.  But the kernel is indexed by
$Z(F)\backslash G(F)$, so they all represent the identity element of $\overline G(F)$.  Hence
there is one central summand, not a sum over $F^\times$.

This elementary point is where the central quotient does real work.  Had one written a kernel
over $G(F)$ while using a test function supported only modulo $Z(\mathbf A)$, the scalar sum
would not even be the intended object.  Fixed-central-character harmonic analysis naturally
lives on the line bundle over (1.8), and the projective index in (1.1) is forced by that
geometry.

### 6.2 Evaluation of the central term

For the identity projective class,

$$
f(x^{-1}1x)=f(1).
$$

Its truncated contribution is therefore

$$
I_{T,\mathrm{cent}}(f)
=f(1)\int_{[\overline G]}\chi_T(x)\,dx.
\tag{6.1}
$$

The quotient has finite volume, so dominated convergence gives

$$
\lim_{T\to\infty}I_{T,\mathrm{cent}}(f)
=\operatorname{vol}([\overline G])f(1).
\tag{6.2}
$$

This proves the first term of (1.12).  Notice that the coefficient is the volume for the same
$d\bar g$ used in the convolution operator and in orbital quotient integration.  Rescaling
$d\bar g$ multiplies both the diagonal trace and every term of the geometric side by the same
factor.

### 6.3 Dependence on central-character conventions

Our convention is

$$
\phi(zg)=\omega(z)\phi(g),\qquad
f(zg)=\omega(z)^{-1}f(g).
\tag{6.3}
$$

Then $f(g)\phi(xg)$ descends in the convolution variable.  If one instead writes a function on
$Z(\mathbf A)\backslash G(\mathbf A)$ by choosing a section, its value at the identity depends
on that section; (6.3) is the invariant formulation.  Replacing a rational representative
$\gamma$ by $z\gamma$ changes the local values but the global factor is
$\omega(z)^{-1}=1$ because $\omega$ is an idele class character.  Thus both the central term
and elliptic terms are well defined on $\overline G(F)$.

Unitarity of $\omega$ is needed in the Hilbert-space input and ensures that adjunction preserves
the same central quotient.  The geometric classification itself does not use unitarity, but the
equality with an ordinary operator trace does.

## 7. The parabolic organization of nonelliptic elements

### 7.1 Incidence with rational lines

Let $\Gamma_{\mathrm{par}}$ be the set of noncentral nonelliptic elements of
$\overline G(F)$.  By Theorem 2.1 each such element stabilizes a rational line.  Apply the finite
incidence identity (2.8) to the doubly truncated diagonal sum.  For a line $L$, choose
$\delta_L\in G(F)$ carrying $L$ to the standard line $Fe_1$.  Then

$$
\delta_L\gamma\delta_L^{-1}\in B(F).
$$

The sum over lines becomes a sum over $B(F)\backslash G(F)$, and the integration over
$G(F)$ in the automorphic quotient unfolds that coset space.  What remains is a sum over
rational elements of $B(F)/Z(F)$.

The weight $e(\gamma)^{-1}$ is not cosmetic.  A split regular element appears once for each of
its two eigenlines and must receive weight $1/2$; a nontrivial unipotent has one eigenline and
receives weight one.  Central elements would stabilize infinitely many lines, which is why the
central locus was removed before applying the incidence identity.

### 7.2 Borel coordinates

Modulo the center, every element of $B(F)$ may be represented as

$$
t(r)n(u),\qquad
t(r)=\begin{pmatrix}r&0\\0&1\end{pmatrix},\qquad
n(u)=\begin{pmatrix}1&u\\0&1\end{pmatrix}.
\tag{7.1}
$$

If $r\ne1$, conjugation by $n(v)$ gives

$$
n(v)^{-1}t(r)n(v)
=t(r)n((1-r^{-1})v).
\tag{7.2}
$$

Because $1-r^{-1}\ne0$, the variable $v\in F$ runs through all upper-right entries.  Thus, for
fixed $r\ne1$, the rational unipotent translates in (7.1) form the rational conjugacy orbit
inside $B$.  If $r=1$, the term $u=0$ is central and has already been removed, while all
$u\ne0$ give the unique nontrivial unipotent class projectively.

This common coordinate description is why split regular and nonsemisimple elements can be
handled by one unipotent unfolding.  Their incidence multiplicities differ, but the analytic
integral that appears is the same parabolic transform.

### 7.3 Unipotent unfolding

The additive quotient $N(F)\backslash N(\mathbf A)$ is compact.  With the probability measure
fixed in Section 1.3, for every absolutely integrable function $h$ on $N(\mathbf A)$ one has

$$
\sum_{u\in N(F)}
\int_{N(F)\backslash N(\mathbf A)}h(n(u)n(v))\,dv
=\int_{N(\mathbf A)}h(n)\,dn.
\tag{7.3}
$$

This is simply the decomposition of $N(\mathbf A)$ into rational translates of a fundamental
domain.  Two different appearances of (7.3) are needed.  When $r\ne1$, formula (7.2) gives the
sum-integral identity

$$
\sum_{u\in F}\int_{F\backslash\mathbf A}
H\bigl(u+(1-r^{-1})v\bigr)\,dv
=\int_{\mathbf A}H(w)\,dw.
\tag{7.3a}
$$

Changing the representative of $v$ merely reindexes $u$, and the substitution by
$1-r^{-1}\in F^\times$ has global modulus one by the product formula.  Thus (7.3a) unfolds the
rational upper-right entry and the compact unipotent coordinate in the Borel quotient.  When
$r=1$, the nonzero entries $u\in F^\times$ are scaled by the rational diagonal
torus.  Unfolding $F^\times\backslash\mathbf A^\times$ and using
$t(a)^{-1}n(u)t(a)=n(a^{-1}u)$ changes the multiplicative measure, together with the Borel
modular factor, into additive Haar measure on $\mathbf A\setminus\{0\}$.  The omitted point has
additive measure zero.  This last observation is what permits the central element $u=0$ to have
been removed without leaving a spurious correction.

In the truncated trace, after the $B(F)\backslash G(F)$ incidence unfolding, both cases reduce
to (7.3) with

$$
h(n)=f(x^{-1}tny)
$$

for translated $x,y$ and a diagonal $t$.  With both cutoffs present all sums and integrals are
finite or absolutely convergent, so the changes of variables apply without qualification.  The
full unipotent integral is

$$
\delta_B(t)^{-1/2}f_B(x,y;t),
\tag{7.4}
$$

which is zero by (1.6).

The variables $x$ and $y$ in (7.4) include representatives and translations generated during
unfolding.  This is the precise reason for the two-sided strong cuspidality in (1.5).  Vanishing
only at $x=y=1$ would not imply the zero required here.

### 7.4 The exact cancellation mechanism

It is tempting to summarize the preceding calculation by saying that every split or unipotent
orbital integral vanishes.  That formulation is generally wrong and obscures convergence.
What vanishes is a parabolically grouped expression obtained by:

1. marking every rational stable line;
2. dividing by the number of stable lines;
3. moving that line to the standard Borel;
4. unfolding $N(F)\backslash N(\mathbf A)$;
5. applying the zero global transform (1.6).

The following finite-level statement records the equality that will be estimated in the next
chapter.  It is important because it includes the repeated-root fiber rather than appealing to
an undefined “unipotent orbital integral.”

**Lemma 7.1 (rank-one parabolic regrouping).** Let $\rho_R$ be the rational height cutoff of
Section 5.4 and let $\Psi$ be a smooth compactly supported function on $[\overline G]$.  The
incidence-weighted integral of all noncentral nonelliptic terms with cutoff $\rho_R$ is the sum
of:

1. finitely many integrals in which the inner factor is

   $$
   \delta_B(t)^{-1/2}f_B(x,y;t);
   \tag{7.5}
   $$

2. finitely many integrals obtained from the same unfolded variables by replacing $\Psi(x)$
   with a difference $\Psi(n(v)x)-\Psi(x)$.

The coefficients in these integrals are the incidence weights $1/2$ for $r\ne1$ and $1$ for
$r=1$; on every rational-height shell their absolute values and Jacobians are bounded by a fixed
polynomial in the torus and unipotent heights, independently of $R$.

**Proof.** Apply (2.8) before removing either cutoff.  A marked line is a point of
$B(F)\backslash G(F)$; moving it to $Fe_1$ and unfolding that coset sum changes the automorphic
domain from $G(F)\backslash G(\mathbf A)$ to $B(F)\backslash G(\mathbf A)$.  Write the rational
Borel element as $t(r)n(u)$ and use the compact quotient
$N(F)\backslash N(\mathbf A)$ in this domain.  For $r\ne1$, (7.3a) turns the sum over
$u$ and the compact integration variable into the full $N(\mathbf A)$ integral.  The two Weyl
choices are exactly the two eigenlines, so their total coefficient is the incidence weight
$1/2$ counted twice.  For $r=1$, unfold the rational diagonal scaling as described after
(7.3a); $u=0$ is absent, but its image is the additive-Haar null point $0\in\mathbf A$.  This
produces the same full unipotent integral with coefficient one.

If $\Psi$ were invariant under every translation made in these changes of variables, the result
would be exactly (7.5).  Insert and subtract the untranslated value of $\Psi$ at each change of
variables.  The untranslated pieces give (7.5); the remaining pieces have the asserted cutoff
difference.  On the finite rational sum every step is ordinary finite Fubini.  The affine
Jacobians in (7.3a), the root character in diagonal scaling, and the two incidence weights are
rational functions of $r$ of bounded degree.  They therefore have polynomial height on every
shell, which proves the uniform assertion.  $\square$

For a split regular semisimple element the local orbital integral of a strongly cuspidal factor
does vanish, and this gives a useful consistency check.  The nonsemisimple contribution,
however, is naturally entangled with the truncation boundary and should not be defined as an
isolated absolutely convergent global orbital term.  The stable-line method treats both strata
uniformly and produces the correct cancellation before taking the limit.

The main terms in Lemma 7.1 are zero by (1.6).  The actual cutoff $\chi_T$ is not invariant
under the translations used in the unfolding, so only its difference terms remain.  Proving
that they tend to zero is the final nonelliptic step.

## 8. Removing the truncation boundary

### 8.1 The boundary discrepancy

Let $I_T^{\mathrm{par}}(f)$ denote the split-regular plus nonsemisimple portion of the truncated
diagonal, grouped by stable lines.  Insert the full unipotent integral from (7.3), whose
contribution is zero, and subtract it again.  The result is a finite sum of expressions whose
essential form is

$$
\int \bigl(\chi_T(n(v)x)-\chi_T(x)\bigr)
f(x^{-1}tn(v)y)\,dv\,d\mu(x,t,y).
\tag{8.1}
$$

The variables suppressed in (8.1) range over fixed compact sets or over the rational torus
shells of Lemma 7.1; their measures and incidence coefficients have fixed polynomial height.
The difference of cutoffs is supported where either $x$ or $n(v)x$ lies in the band

$$
T\ll H\ll T(1+|v|)^c.
\tag{8.2}
$$

Thus the discrepancy is pushed farther into the cusp as $T$ grows.  To conclude that it
vanishes, one needs a bound uniform in the rational torus and unipotent sums, not merely
pointwise decay for each fixed summand.

### 8.2 Iwasawa coordinates in the cusp

In every cusp chart write $x=n(q)a(H)k$ as in (5.6), with $q$ and $k$ in fixed compact sets.
The root character satisfies

$$
a(H)^{-1}n(v)a(H)=n(H^{-1}v)
\tag{8.3}
$$

after harmless normalization of $H$.  The quotient measure has the bound

$$
dx\ll d\mu_{\mathrm{comp}}\frac{dH}{H^2}.
\tag{8.4}
$$

The exponent $2$ is the rank-one modular decay.  It is crucial: a gain of any additional
negative power of $H$ is integrable uniformly beyond $T$.

Choose $\chi_T(x)=\chi(H/T)$ inside the chart.  If $|v|\le H^{1/2}$, the mean-value theorem and
(8.3) give

$$
|\chi_T(n(v)x)-\chi_T(x)|
\le C H^{-1}(1+|v|),
\tag{8.5}
$$

after replacing the adelic norm by an equivalent height on the fixed compact coordinates.  If
$|v|>H^{1/2}$, we discard the cutoff difference and use rapid decay of the test function:

$$
|D f(x^{-1}tn(v)y)|
\le C_N(f)(1+|v|)^{-N}
$$

times a fixed polynomial in $H$ and the torus height.  Any prescribed polynomial loss can be
absorbed by taking $N$ larger.

### 8.3 A quantitative boundary estimate

**Proposition 8.1.** There exist $\eta>0$ and a continuous Schwartz seminorm $\nu$ such that

$$
|I_T^{\mathrm{par}}(f)|\le \nu(f)T^{-\eta}
\qquad(T\ge1).
\tag{8.6}
$$

**Proof.** Work first with the rational height cutoff of Section 5.4.  In the range
$|v|\le H^{1/2}$, use (8.5).  The first unipotent moment of the translate of $f$ is finite and,
after invariant differentiation, bounded by a fixed Schwartz seminorm times a polynomial in
the torus height.  This gives one negative power of $H$, up to that polynomial.

In the complementary range use the bound following (8.5).  Integration of
$(1+|v|)^{-N}$ over $|v|>H^{1/2}$ gives an arbitrarily large negative power of $H$ when $N$ is
large.  At finite places the support of $f$ confines the rational torus coordinates to fixed
fractional ideals.  In each dyadic archimedean torus shell, lattice counting is polynomial.
More explicitly, there are fixed exponents $d,e$ such that a shell of torus-unipotent height
$2^m$ contains at most $C2^{dm}$ rational parameters and the Jacobians and coordinate changes
in Lemma 7.1 cost at most $C2^{em}$.  A Schwartz seminorm of order $L$ contributes
$C\nu_L(f)2^{-Lm}$.  Taking $L>d+e+2$ makes

$$
\sum_{m\ge0}C\nu_L(f)2^{-m(L-d-e)}
\tag{8.5a}
$$

converge uniformly, independently of the rational height cutoff.  This also justifies all
limit passages that remove that cutoff.

After the compact variables are integrated, the remaining height integral is bounded by

$$
C\nu(f)\int_T^\infty H^{-\eta}\frac{dH}{H^2}
\le C'\nu(f)T^{-1-\eta}.
\tag{8.7}
$$

There are only finitely many cusp charts.  Letting the rational height cutoff tend to infinity
by the same summable majorant proves (8.6), after weakening the exponent if desired.
$\square$

The proof displays every source of convergence: a cutoff derivative handles small unipotent
translations, Schwartz decay handles large translations, finite support bounds denominators,
lattice counting controls rational torus points, and $dH/H^2$ integrates the result.

### 8.4 Vanishing of split and unipotent terms

The full parabolic transform inserted in Section 8.1 is zero.  Proposition 8.1 shows that the
difference between it and the truncated nonelliptic contribution tends to zero.  Hence

$$
\lim_{T\to\infty}I_T^{\mathrm{par}}(f)=0.
\tag{8.8}
$$

This conclusion includes both split regular and noncentral nonsemisimple rational elements.
There is no missing singular term: the central point $u=0$ in the repeated-root fiber was
removed before stable-line incidence, while every $u\ne0$ was included in the unipotent
unfolding.

Equation (8.8) is also stable under finite sums of tensors.  If the tensors use the same
distinguished cuspidal place, every global transform vanishes there.  The constants in (8.6)
add, and no new convergence issue appears.

## 9. Elliptic unfolding

### 9.1 Orbit-by-orbit unfolding

Fix an elliptic $G(F)$-conjugacy class in $\overline G(F)$ and a representative $\gamma$.
Its contribution to the rational kernel is

$$
K_{[\gamma]}(x,x)=
\sum_{\delta\in C_\gamma(F)\backslash\overline G(F)}
f(x^{-1}\delta^{-1}\gamma\delta x).
\tag{9.1}
$$

On a compactly truncated region and with rational height bounded, unfolding the sum over
$\delta$ yields an integral over
$C_\gamma(F)\backslash\overline G(\mathbf A)$.  To remove the rational height cutoff
for this fixed orbit, note that the orbit map is proper on the inverse image of compact sets
modulo $\overline G_\gamma$.  Finite-place compact support and archimedean Schwartz decay then
give absolute convergence.  Consequently

$$
\int_{[\overline G]}K_{[\gamma]}(x,x)\,dx
=\int_{C_\gamma(F)\backslash\overline G(\mathbf A)}
f(x^{-1}\gamma x)\,dx.
\tag{9.2}
$$

Here it is safe to omit truncation for one fixed elliptic orbit.  The centralizer quotient is
compact and the transverse orbit integral is absolutely convergent.  Uniformity in $\gamma$ is
not asserted yet.

### 9.2 Compactness in the centralizer direction

Pass first from $C_\gamma(F)$ to $\overline G_\gamma(F)$, acquiring the finite-cover factor
$\kappa(\gamma)$, and then decompose the connected-centralizer domain in two stages:

$$
\overline G_\gamma(F)\backslash\overline G(\mathbf A)
\longrightarrow
\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A).
\tag{9.3}
$$

The fiber is
$\overline G_\gamma(F)\backslash\overline G_\gamma(\mathbf A)$, compact by Proposition 3.2.
The integrand is invariant along this fiber because its elements centralize $\gamma$.  Quotient
integration therefore gives

$$
\int_{\overline G_\gamma(F)\backslash\overline G(\mathbf A)}
f(x^{-1}\gamma x)\,dx
=a(\gamma)O_\gamma(f),
\tag{9.4}
$$

so the integral in (9.2) is
$\kappa(\gamma)a(\gamma)O_\gamma(f)$.

The equality is unchanged by rescaling the centralizer measure, as shown in (4.5).  It is also
unchanged by replacing $\gamma$ by a rational scalar multiple, by the central-character
argument of Section 6.3.

### 9.3 Passage from local to global orbits

A global elliptic class determines a local regular semisimple class at every place.  The
converse need not hold: arbitrarily chosen local classes may fail to arise from one rational
characteristic polynomial.  Our sum is over rational classes first, and only then factors their
orbital integrals as in (4.4).  This order avoids inserting any unproved local-to-global
principle.

For $\mathrm{GL}_2$, stable and rational conjugacy agree for regular semisimple elements with a
fixed characteristic polynomial.  Indeed, Proposition 2.2 constructs a rational conjugating
matrix.  There is therefore no hidden sum over rational classes inside a stable elliptic class.
The trace-zero projective class still has the extra Weyl stabilizer of (3.5b); that changes the
orbit coefficient by $\kappa(\gamma)$ but does not split the orbit into two rational classes.
This special degree-two control fails for many other groups and is one reason the rank-two
formula has such a clean geometric side.

The quadratic field $E=F[\gamma]$ is determined by the irreducible characteristic polynomial.
At a place $v$, $E\otimes_FF_v$ may be a field or $F_v\times F_v$.  The formula (4.4) includes
both possibilities.  A strongly cuspidal real factor forces the local orbital integral to be
zero when $E$ splits at $v_0$, so only global elliptic classes that are also elliptic at the
distinguished real place can contribute.  We retain the sum over all global elliptic classes;
the local zero removes the others automatically.

### 9.4 The provisional elliptic expansion

Combining the central evaluation, parabolic cancellation, and fixed-orbit unfolding suggests

$$
\lim_{T\to\infty}I_T(f)
=\operatorname{vol}([\overline G])f(1)
+\sum_{[\gamma]_{\mathrm{ell}}}\kappa(\gamma)a(\gamma)O_\gamma(f).
\tag{9.5}
$$

There remains one decisive issue: the sum in (9.5) is infinite, and fixed-orbit convergence
does not permit passage through it.  We must produce a summable majorant independent of the
truncation.  The next two chapters divide that task into analysis and arithmetic.  Local orbit
charts give decay up to powers of the discriminant; global height and lattice counting show
that there are only polynomially many classes and that their torus volumes grow at most
polynomially.  Arbitrary Schwartz decay then wins.

## 10. Uniform bounds for orbital integrals

### 10.1 The Weyl discriminant

Uniformity deteriorates when a regular orbit approaches the singular set.  The invariant that
measures this deterioration is the projective Weyl discriminant.  If $\lambda_1,\lambda_2$ are
the eigenvalues of $\gamma$ in a splitting field, put

$$
\mathfrak D(\gamma)
=\left(1-\frac{\lambda_1}{\lambda_2}\right)
 \left(1-\frac{\lambda_2}{\lambda_1}\right)
=-\frac{\Delta_\gamma}{d_\gamma}.
\tag{10.1}
$$

Its absolute value is invariant under conjugacy, scalar multiplication, and exchange of the
eigenvalues.  It vanishes exactly on the repeated-root locus.

The orbit map

$$
q_\gamma:\overline G_\gamma\backslash\overline G
\longrightarrow \overline G,\qquad g\longmapsto g^{-1}\gamma g
\tag{10.2}
$$

has differential at the identity coset

$$
X\longmapsto [\gamma,X]
\tag{10.3}
$$

on $\mathfrak g/\mathfrak g_\gamma$.  Over a splitting field the two root vectors are multiplied
by $\lambda_1-\lambda_2$ and $\lambda_2-\lambda_1$.  After removing the scalar size of
$\gamma$, the determinant of (10.3) is a nonzero constant times $\mathfrak D(\gamma)$.  Thus
inverse orbit charts can lose powers of $|\mathfrak D(\gamma)|^{-1}$ near singularity, but no
worse kind of algebraic singularity occurs.

This calculation does not claim that the orbital integral is bounded near the singular set.
It identifies the allowed loss: powers and, at archimedean places, logarithms of the
discriminant.  Those losses will be included explicitly in the global height.

### 10.2 Nonarchimedean orbit charts

Let $k$ be a nonarchimedean local field and let $C\subset\overline G(k)$ be compact.  Fix a
compactly supported locally constant function $h$ supported in $C$.  Subdivide $C$ into finitely
many coordinate neighborhoods and, when necessary, according to
$m=v_k(\mathfrak D(\gamma))$.  The nonarchimedean inverse-function theorem applied to (10.2)
gives orbit charts whose Jacobian and inverse Jacobian are bounded by $q^{cm}$ for a constant
$c$ depending only on $C$ and the chosen coordinates.  The number of residue-class charts
needed at depth $m$ is also $O(q^{c'm})$.

It follows that there are constants $C_0,c_0$ such that

$$
|O_{\gamma,k}(h)|
\le C_0\|h\|_\infty
\max\bigl(1,|\mathfrak D(\gamma)|_k^{-c_0}\bigr)
\tag{10.4}
$$

whenever the orbit of $\gamma$ meets $C$.  If $h$ ranges over a fixed finite-dimensional
space of functions with common support and level, $C_0$ may be chosen as a continuous norm on
that space.

Here is the proof in more detail.  On the stratum where $v_k(\mathfrak D)=m$, choose a complement
$\mathfrak q$ to the centralizer Lie algebra.  The determinant of the derivative on
$\mathfrak q$ has valuation $m+O(1)$.  Hensel's inverse theorem gives injective charts after
restricting $\mathfrak q$ to balls of radius $q^{-c(m+1)}$.  At most $q^{c'(m+1)}$ such balls
meet $C$.  Change variables in each chart, bound $h$ by its supremum, and sum.  This proves
(10.4).  Local constancy ensures that no derivative estimates are needed.

At almost every place the data are integral and unramified.  The support is the image of a
maximal compact subgroup, the centralizer has its hyperspecial compact subgroup of volume one,
and the constants in (10.4) are uniform.  Only places dividing the denominator or discriminant
of the orbit can produce a loss.

### 10.3 Archimedean decay

Let $k=\mathbf R$ or $\mathbf C$.  In Cartan coordinates $g=k_1a(s)k_2$, Haar measure is bounded
by

$$
C e^{cs}\,ds\,dk_1\,dk_2,\qquad s\ge0.
\tag{10.5}
$$

Away from the centralizer, conjugation by $a(s)$ makes at least one off-centralizer coordinate
of $g^{-1}\gamma g$ grow like $e^{c's}$, multiplied by a factor whose reciprocal is bounded by
a power of $|\mathfrak D(\gamma)|_k^{-1}$.  A Schwartz seminorm of order $N$ therefore yields

$$
|h(g^{-1}\gamma g)|
\le \nu_N(h)
|\mathfrak D(\gamma)|_k^{-C_N}
e^{-Ns}(1+\|\gamma\|_{\mathrm{ad}})^{-N},
\tag{10.6}
$$

where $\|\gamma\|_{\mathrm{ad}}$ is any proper projective norm.  Taking $N>c$ and integrating
(10.5) gives

$$
|O_{\gamma,k}(h)|
\le \nu_N(h)
|\mathfrak D(\gamma)|_k^{-C_N}
(1+\|\gamma\|_{\mathrm{ad}})^{-N+C'_N}.
\tag{10.7}
$$

Because $N$ is arbitrary, the final projective decay may be made stronger than every fixed
power after absorbing the discriminant loss.

At the distinguished real place, a regular split orbital integral is zero.  To see this
directly, diagonalize $\gamma$ into $T(\mathbf R)$.  Iwasawa integration on
$T(\mathbf R)\backslash G(\mathbf R)$ expresses its orbital integral as an integral, over
compact variables, of

$$
\int_{N(\mathbf R)}f_{v_0}(x^{-1}\gamma ny)\,dn.
$$

This is zero by strong cuspidality.  All changes of order are permitted by the Schwartz bounds
just proved.  Thus a globally elliptic class that splits at $v_0$ has zero global orbital
integral, confirming the claim in Section 9.3.

If the class is elliptic at the real place, the centralizer is compact modulo the center and
the Cartan estimate is simpler.  Nevertheless, uniformity as its two complex eigenvalues
coalesce still carries a discriminant factor.  One must not replace (10.7) by a bound uniform
all the way to $\mathfrak D=0$.

### 10.4 Global height decay

Finite support restricts the rational classes that can contribute.  Fix a finite set $S$
containing all archimedean places and every finite place where $f_v$ is not the distinguished
spherical function or where the chosen measures are ramified.  If
$O_{\gamma,v}(f_v)\ne0$ outside $S$, then the projective characteristic coefficients of
$\gamma$ are integral there and their denominators are uniformly bounded.  At places in $S$
the compact support again imposes a fixed denominator bound.

Let $H_F$ be the multiplicative Weil height on $F$.  For an elliptic class define the invariant
height

$$
H_{\mathrm{ell}}(\gamma)=H_F(j(\gamma))
N\mathfrak d_{E/F},\qquad E=F[\gamma].
\tag{10.7a}
$$

This height is independent of representatives.  When $j\ne0$, scaling to trace one shows that
$j$ determines the projective class.  When $j=0$, the quadratic field $E$ determines the
remaining determinant square class.  On the finite-support set, (10.7a) is polynomially
comparable with any standard height built from a primitive companion matrix: the relative
discriminant divides, up to a fixed denominator ideal, the discriminant of the order generated
by $\gamma$, and the latter is quadratic in its coefficients.  The product formula turns
large inverse local discriminants at finite places into archimedean size or into the explicit
factor $N\mathfrak d_{E/F}$.  Multiplying (10.4) over finite places and (10.7) over archimedean
places therefore gives the key estimate.

We isolate the arithmetic comparison used in that multiplication.  Let $\mathcal S(f)$ be the
set of rational regular classes whose finite orbits meet the support of $f_{\mathrm{fin}}$.
There are constants $c,C>0$ such that, for $\gamma\in\mathcal S(f)$ with $j(\gamma)\ne0$,

$$
N\mathfrak d_{F[\gamma]/F}
\prod_{v<\infty}\max(1,|\mathfrak D(\gamma)|_v^{-1})
\le C H_F(j(\gamma))^c.
\tag{10.7b}
$$

Indeed, normalize to trace one.  Then
$d=j^{-1}$, $\Delta=(j-4)/j$, and $\mathfrak D=4-j$, up to harmless sign conventions.  The
quadratic field is $F(\sqrt{j(j-4)})$.  Finite support bounds the denominator ideal of $j$;
clearing that fixed ideal, the relative field discriminant divides a fixed dyadic ideal times
the squarefree part of the numerator ideals of $j$ and $j-4$.  The finite product in (10.7b) is
the denominator norm of $j-4$, again up to a fixed ideal.  Taking norms and applying the product
formula gives (10.7b).  Conversely, the product of the archimedean coefficient heights of a
primitive companion representative is bounded below by a fixed positive power of $H_F(j)$
once the finite denominator of $j$ is fixed.

When $j=0$, finite orbital support permits only finitely many determinant squareclasses.  To
see this locally, outside a fixed finite set the good-place calculation (4.3a) forces the
quadratic algebra to be unramified; at a place in the fixed set, $F_v^\times/F_v^{\times2}$ is
finite.  Globally, squareclasses with prescribed parity outside that set form a finite group by
the $S$-unit and ideal-class argument displayed later in (11.1).  Thus all estimates below on
the trace-zero fiber can be enlarged uniformly over a finite set.

**Theorem 10.1 (rapid global orbital decay).** For every $M>0$ there is a continuous Schwartz
seminorm $\nu_M$ such that

$$
|O_\gamma(f)|\le \nu_M(f)H_{\mathrm{ell}}(\gamma)^{-M}
\tag{10.8}
$$

for every globally elliptic class whose finite orbit meets the support of $f$.

**Proof.** First suppose $j(\gamma)\ne0$.  Multiply (10.4) at the finite places.  At the
finitely many places in $S$, the constants are controlled by finitely many local seminorms;
their discriminant factors remain in the displayed product of (10.7b).  Outside $S$, (4.3a)
removes every good-discriminant place.  Thus the product of every remaining local loss is at
worst a fixed power of the left side of (10.7b), hence at most a fixed power of $H_F(j)$.

At the archimedean places, multiply (10.7).  The lower bound following (10.7b) converts the
arbitrary projective decay in (1.4a) into an arbitrary negative power of $H_F(j)$.  The
archimedean inverse-discriminant factors are at most another fixed power of $H_F(j)$, by the
definition of Weil height applied to $4-j$.  Choose the Schwartz order after all these fixed
losses have been determined, large enough to leave
$H_F(j)^{-M}$ and an additional negative power absorbing
$N\mathfrak d_{E/F}^{M}$.  This is possible because that discriminant is itself bounded by a
fixed power of $H_F(j)$ in (10.7b).  The result is (10.8).

On the trace-zero fiber there are only finitely many contributing classes by the paragraph
following (10.7b).  Enlarge the same continuous seminorm by the maximum of the finitely many
continuous orbital-integral seminorms multiplied by $H_{\mathrm{ell}}(\gamma)^M$.  This proves
the estimate there as well.  Finite sums of tensors follow by adding seminorms.  $\square$

A logarithmic singularity causes no problem: for every $\epsilon>0$,
$|\log x|\ll_\epsilon x^{-\epsilon}$ on $0<x\le1$.  Hence logarithms are absorbed by an
arbitrarily small increase in the discriminant exponent before the Schwartz order is chosen.

## 11. Counting elliptic classes and their volumes

### 11.1 Integral representatives and height

The analytic estimate (10.8) is useful only if the number and volume of classes of bounded
height grow at most polynomially.  We now prove these coarse arithmetic bounds.

Finite-place support bounds the denominator ideal of $j(\gamma)$ uniformly.  If
$H_F(j)\le X$, its archimedean embeddings lie in a box of polynomial size in $X$.  Clearing the
fixed denominator puts $j$ in a fixed fractional-ideal lattice, so the number of possible
values is $O(X^A)$ for some $A$.

For $j\ne0$, Section 2.3 shows that the value of $j$ determines the projective rational class:
scale to trace one and use the companion matrix.  The exceptional value $j=0$ is handled by
the second factor in (10.7a).  A trace-zero class determines the quadratic field $E$, and $E$
determines its determinant square class.  Quadratic extensions with
$N\mathfrak d_{E/F}\le X$ are polynomially numerous.  To see this without an asymptotic
counting theorem or class field theory, write $E=F(\sqrt a)$ and let $S$ contain the archimedean
places and the finite places dividing $2\mathfrak d_{E/F}$.  Outside $S$, every valuation of
$a$ is even.  The relevant squareclasses fit into the elementary ideal-theoretic sequence

$$
\mathcal O_{F,S}^{\times}/\mathcal O_{F,S}^{\times2}
\longrightarrow
\{a\in F^\times/F^{\times2}:v(a)\equiv0\pmod2\text{ off }S\}
\longrightarrow
\operatorname{Cl}(\mathcal O_{F,S})[2].
\tag{11.1}
$$

The first group has order at most a fixed constant times $2^{|S|}$ by the unit theorem.  The
last has order at most the class number of $F$ times $2^{|S|}$, as follows by inverting the
primes of $S$ one at a time in the ideal-class presentation.  There are polynomially many
possible discriminant ideals of norm at most $X$, and $2^{|S|}$ is at most a fixed multiple of
the norm of their product.  The finitely many dyadic squareclasses contribute only a fixed
factor.  Hence the number of fields is $O(X^C)$ for a constant depending only on $F$.  Thus the
invariant height counts both the ordinary and trace-zero fibers correctly.

### 11.2 Polynomial counting

**Proposition 11.1.** There exist constants $A,C>0$, depending on $F$ and the finite support of
$f$, such that

$$
\#\bigl\{[\gamma]_{\mathrm{ell}}:
H_{\mathrm{ell}}(\gamma)\le X, O_{\gamma,\mathrm{fin}}(f_{\mathrm{fin}})\ne0\bigr\}
\le CX^A
\tag{11.2}
$$

for $X\ge1$.

Here
$O_{\gamma,\mathrm{fin}}(f_{\mathrm{fin}})=\prod_{v<\infty}O_{\gamma,v}(f_v)$ denotes the
finite-adelic factor.

**Proof.** The lattice count for $j\ne0$ and the discriminant-and-squareclass count for $j=0$ were
proved in Section 11.1.  Discarding values that give split or singular polynomials can only
decrease the count.  The finite orbital support condition imposes further restrictions and
likewise cannot increase it.  $\square$

This estimate is intentionally wasteful.  The precise asymptotic number of quadratic fields or
conjugacy classes is irrelevant: a polynomial bound is enough because (10.8) has arbitrary
power decay.

### 11.3 Polynomial torus-volume bounds

We must also control

$$
a(\gamma)=\operatorname{vol}(T_E(F)\backslash T_E(\mathbf A)),
\qquad E=F[\gamma].
$$

**Proposition 11.2.** With the compatible measures of Chapter 4, there are constants $B,C>0$
such that

$$
a(\gamma)\le C H_{\mathrm{ell}}(\gamma)^B
\tag{11.3}
$$

for all contributing elliptic classes.

**Proof.** Compare $T_E$ with the norm-one torus through the isomorphism of Section 3.2.
A fundamental domain for its idele class quotient is assembled from an ideal-class
representative, compact local unit groups, and a fundamental parallelepiped for the logarithmic
unit lattice.

Minkowski's convex-body theorem supplies in every ideal class an integral ideal whose norm is
bounded by a fixed power of $|D_E|$.  It also bounds the number of ideal classes coarsely by a
fixed power of $|D_E|$: represent each class by such an ideal and count integral ideals of
bounded norm through lattice points.

We also need an upper, rather than lower, regulator bound.  In fixed degree it follows by the
quantitative form of Dirichlet's box argument.  Embed $\mathcal O_E$ as a lattice of covolume
$2^{-r_2(E)}|D_E|^{1/2}$.  Apply the pigeonhole proof of the unit theorem in an archimedean box
whose side lengths are $\exp(C|D_E|^{C_0})$, subdivided by a fundamental cell of that lattice
and by the finitely many ideal classes just bounded.  Two elements in the same cell and ideal
class have a quotient which is a unit; its logarithm vector has norm at most
$C|D_E|^{C_0}$.  After one unit has been found, perform the same argument in the quotient by
its logarithmic span.  At each of the fixed number
$r_E=r_1(E)+r_2(E)-1$ of stages, enlarging $C_0$ if necessary prevents all lattice points from
lying in the finitely many previously obtained lower-rank slabs.  This produces $r_E$
independent units with logarithm vectors of polynomial size in $|D_E|$.  The determinant of
those vectors bounds from above the covolume of the full unit lattice.  Thus

$$
R_E\le C|D_E|^{C_0}.
\tag{11.3a}
$$

Dirichlet's unit theorem identifies this regulator with the volume of the noncompact
archimedean unit directions.  Roots of unity are bounded in fixed degree.  Comparing integral
maximal compact subgroups under (3.5) can introduce local indices only at places dividing the
relative discriminant, and each index is bounded by a fixed power of the residue-field size;
their product is bounded by a fixed power of $N\mathfrak d_{E/F}$.

Multiplying these estimates bounds the volume by $C|D_E|^{B_0}$.  Since
$|D_E|=|D_F|^2N\mathfrak d_{E/F}$ and the relative discriminant norm is a factor of our height,
(11.3) follows after increasing $B$.  $\square$

No class-number formula or analytic estimate for a quadratic $L$-value is being imported.  The
argument requires only the geometry of ideals and units in a quadratic extension, and its
coarseness is an advantage: it is uniform over all fields $E$ that occur.

### 11.4 Absolute summability

**Theorem 11.3.** The series

$$
\sum_{[\gamma]_{\mathrm{ell}}}\kappa(\gamma)a(\gamma)O_\gamma(f)
\tag{11.4}
$$

converges absolutely.  On a bounded set of admissible test functions with fixed finite support,
it is dominated by one summable majorant.

**Proof.** Divide the classes into shells
$2^m\le H_{\mathrm{ell}}(\gamma)<2^{m+1}$.  Proposition 11.1 bounds the number in the $m$-th shell by
$C2^{Am}$.  Proposition 11.2 bounds each volume by $C2^{Bm}$.  Theorem 10.1 bounds the orbital
integral by $\nu_M(f)2^{-Mm}$, and $0<\kappa(\gamma)\le1$.  Hence the sum of absolute values in
the shell is at most

$$
C\nu_M(f)2^{-m(M-A-B)}.
\tag{11.5}
$$

Choose $M>A+B+1$ and sum the resulting geometric series.  The seminorm $\nu_M$ is uniform on
the stated bounded test-function set, proving both assertions.  $\square$

Absolute convergence is asserted after grouping rational elements into elliptic conjugacy
classes.  This is the natural grouping in (11.4) and is sufficient for order independence,
continuity, and passage through truncation.  It does not imply convergence of the raw majorant
(5.4), which also contains the parabolic incidence responsible for cusp divergence.

## 12. The geometric expansion

### 12.1 The central-plus-elliptic formula

We can now complete the passage from the diagonal to rational orbits.

**Theorem 12.1 (geometric expansion).** Under the hypotheses of Section 1.2,

$$
\int_{[\overline G]}K_f(x,x)\,dx
=\operatorname{vol}([\overline G])f(1)
+\sum_{[\gamma]_{\mathrm{ell}}}\kappa(\gamma)a(\gamma)O_\gamma(f),
\tag{12.1}
$$

and the elliptic series converges absolutely.

**Proof.** Begin with $I_T(f)$ and the rational height cutoff of Section 5.4.  The resulting
finite sum decomposes by Theorem 2.1.  The central part tends to (6.2).  Regroup the split and
nonsemisimple parts by stable rational lines.  Sections 7.2 and 7.3 unfold their full main term
to the zero parabolic transform; Proposition 8.1 shows that the cutoff discrepancy tends to
zero.

For each elliptic class, orbit unfolding and quotient integration give
$\kappa(\gamma)a(\gamma)O_\gamma(f)$ by Sections 9.1--9.2.  Theorem 11.3 supplies a majorant
independent of both cutoffs,
so dominated convergence permits the rational height cutoff and then $T$ to tend to infinity
through the elliptic class sum.  Finally, (5.9) identifies the limit of $I_T(f)$ with the
diagonal integral.  This proves (12.1).  $\square$

Every term in (12.1) is now an ordinary complex number.  There is no retained truncation
parameter, no regularized centralizer volume, and no unspecified distribution supported on the
singular set.

### 12.2 Continuity and independence of cutoffs

Let $\chi_T'$ be another family of cutoffs with the same support and derivative properties.
The difference $\chi_T-\chi_T'$ is supported in a cusp band whose lower height tends to
infinity.  From (5.2),

$$
\int_{[\overline G]}
|\chi_T(x)-\chi_T'(x)|\,|K_f(x,x)|\,dx\longrightarrow0.
\tag{12.2}
$$

The quantitative boundary estimate gives the same conclusion within the parabolic regrouping,
and Theorem 11.3 gives a cutoff-independent majorant for the elliptic sum.  Therefore the right
side of (12.1) is independent of every auxiliary truncation and partition of unity.

The proof of Theorem 11.3 also shows continuity.  For fixed finite support and level,

$$
\left|
\sum_{[\gamma]_{\mathrm{ell}}}\kappa(\gamma)a(\gamma)O_\gamma(f)
\right|\le C\nu_M(f).
\tag{12.3}
$$

The evaluation $f\mapsto f(1)$ is continuous in the same topology.  Thus
$I_{\mathrm{geom}}$ is a continuous linear distribution on each admissible test-function
space, and hence on their finite inductive union.

### 12.3 Equality with the spectral expansion

Book 99, Theorem 11.1 and its discrete cuspidal decomposition give

$$
\int_{[\overline G]}K_f(x,x)\,dx
=\operatorname{tr}R_\omega(f)
=\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
m(\pi)\operatorname{tr}\pi(f).
\tag{12.4}
$$

The spectral series is absolutely convergent because $R_\omega(f)$ is trace class and block
diagonal on the discrete cuspidal decomposition.  Strong cuspidality annihilates the continuous
Eisenstein spectrum and its residual representations at the operator level.  Thus no spectral
term has been omitted by merely taking a trace-zero cancellation.

Combining (12.1) and (12.4) proves equality of the spectral and geometric expansions in the
precise simple-trace-formula setting.  Logically, the two absolute convergence statements come
from different sources: trace ideals control the spectral sum, while orbit charts, arithmetic
counting, and torus volumes control the elliptic sum.

### 12.4 The complete simple trace formula

**Theorem 12.2 (simple trace formula for $\mathrm{GL}_2$).** Let $F$ be a number field with a
real place $v_0$, let $\omega$ be a unitary idele class character, and let $f$ be a finite sum
of factorizable central-character Schwartz functions satisfying (1.4) and (1.4a), finite under
left and right maximal-compact actions, with a strongly cuspidal factor at $v_0$ in every tensor.
Write $f=\sum_i f_i$ with $f_i=\otimes_v f_{i,v}$.  Then
$R_\omega(f)$ is trace class, annihilates the noncuspidal spectrum, and

$$
\boxed{
\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
m(\pi)\operatorname{tr}\pi(f)
=\operatorname{vol}([\overline G])f(1)
+\sum_{[\gamma]_{\mathrm{ell}}}
\kappa(\gamma)a(\gamma)\sum_i\prod_vO_{\gamma,v}(f_{i,v}).}
\tag{12.5}
$$

Both displayed series converge absolutely.  All quotient measures are induced from the fixed
Haar measures by (1.7), (1.9), and (4.1).  Rescaling a centralizer measure changes
$a(\gamma)$ and $O_\gamma(f)$ inversely and leaves (12.5) unchanged.  By (4.4a), the inner
finite sum depends only on $f$, not on its chosen tensor decomposition.

**Proof.** Trace class, noncuspidal annihilation, and the first equality in (12.4) are the kernel
input.  Theorem 12.1 gives its geometric evaluation.  Factorization of an elliptic orbital
integral is (4.4), its finite-sum form is (4.4a), and all interchanges are justified by Theorem
11.3.  $\square$

The formula includes multiplicities $m(\pi)$; no multiplicity-one theorem is needed.  It also
does not assert a numerical value for any local orbital integral.  Those values can now be
computed and substituted without revisiting global convergence.

## 13. Examples and limiting phenomena

### 13.1 Elliptic classes over the rational field

Take $F=\mathbf Q$ and

$$
\gamma_{s,d}=\begin{pmatrix}0&-d\\1&s\end{pmatrix},
\qquad d\ne0.
\tag{13.1}
$$

Its characteristic polynomial is $X^2-sX+d$.  The class is elliptic over $\mathbf Q$ exactly
when

$$
s^2-4d\notin\{r^2:r\in\mathbf Q\}.
\tag{13.2}
$$

Then $E=\mathbf Q(\sqrt{s^2-4d})$, and the projective centralizer is
$E^\times/\mathbf Q^\times$.  At the real place the class is elliptic precisely when
$s^2-4d<0$.  If the distinguished real test function is strongly cuspidal, a globally
irreducible polynomial with positive discriminant contributes zero because its real local
orbit is split.

For trace zero,

$$
\gamma_{0,d}^2=-dI.
$$

The projective invariant $j$ is always zero, but the field
$\mathbf Q(\sqrt{-d})$ varies with the square class of $d$.  This concrete family exhibits the
exceptional fiber discussed in Section 2.3.  Conjugation implementing the nontrivial automorphism
of that field sends $\gamma_{0,d}$ to $-\gamma_{0,d}$, so this is also exactly the fiber on which
$\kappa=1/2$.  It shows why a convergence height must record the quadratic discriminant in
addition to $j$.

If $f_\infty$ is a pseudo-coefficient of a holomorphic discrete series and the finite factors
are spherical away from a level $N$, (12.5) has the familiar shape

$$
\text{cuspidal trace}
=\text{volume}\cdot f(1)
+\sum_{\substack{\text{imaginary quadratic}\\
\text{projective classes meeting the level}}}
\text{projective stabilizer factor}\cdot
\text{torus volume}\cdot\text{orbital product}.
$$

This is a structural identity; computing the displayed orbital products is a separate local
problem.

### 13.2 Finite-place support conditions

Let $v$ be a finite place at which $f_v$ is the characteristic function of
$Z(F_v)K_v$ with $K_v=\mathrm{GL}_2(\mathcal O_v)$, normalized for the central character.  If
$O_{\gamma,v}(f_v)\ne0$, some conjugate and scalar multiple of $\gamma$ lies in $K_v$.  Hence
the projective characteristic invariants are integral at $v$, and the determinant is a unit
after the same scaling.  This is the local source of the denominator bounds used in Chapter 11.

At a ramified place one may replace the spherical function by a compact-open projector or a
finite linear combination of double-coset functions.  The allowed denominators then lie in a
larger but still fixed fractional ideal.  Polynomial counting and all convergence estimates
remain unchanged in form; only their constants and the finite set $S$ change.

There is an important distinction between support of $f_v$ and support of its orbital
integral.  The latter consists of conjugacy classes whose orbits meet the former.  It need not
be compact as a set of representatives in $G(F_v)$, because representatives can escape along
their conjugacy orbits.  The invariant coefficients, rather than arbitrary matrix entries, are
the correct quantities controlled by compact orbital support.

### 13.3 Approaching the singular set

Consider over $\mathbf R$

$$
\gamma_\theta=
\begin{pmatrix}
\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta
\end{pmatrix},\qquad 0<|\theta|<\pi.
\tag{13.3}
$$

Modulo scalars this is elliptic, and

$$
|\mathfrak D(\gamma_\theta)|
=4\sin^2\theta.
\tag{13.4}
$$

As $\theta\to0$, the class approaches the identity and the orbit map degenerates.  An orbital
integral may grow logarithmically or by a normalization-dependent power.  The estimates of
Chapter 10 permit that growth.  They require only that it be controlled by a fixed power of
$|\mathfrak D|^{-1}$, which is then absorbed globally by stronger Schwartz decay.

This example explains why pointwise smoothness of $f$ does not imply uniform boundedness of all
regular orbital integrals.  Singular limits are real geometric phenomena.  The global trace
formula remains convergent because singularity in one invariant is balanced by arithmetic
height and decay in the full adelic class.

### 13.4 What changes without a cuspidal factor

Remove condition (1.5).  The periodized kernel can still be locally smooth, but the proof above
breaks in three related places.  The transform (1.6) need not vanish, so the main term in the
stable-line unfolding survives.  The boundary discrepancy may have a nonzero limiting
companion rather than tend to zero by itself.  Spectrally, principal-series wave packets and
residues are no longer annihilated.

The correct full trace formula then contains weighted split, unipotent, continuous, and residual
distributions.  Their separate pieces generally depend on a truncation parameter before
compensating terms are combined.  Merely imposing $\int f=0$ kills at most a one-dimensional
representation, and requiring the trace of every induced operator to vanish is weaker than the
operator-level zero needed for the two-variable kernel.  Strong cuspidality is therefore the
exact structural hypothesis behind the simple formula, not a convenient cosmetic restriction.

There is also a geographic limitation.  Our chosen source of strong cuspidality is a real
discrete-series factor.  A number field with no real place is not covered by Theorem 12.2 in
this form.  One can formulate variants using a suitable nonarchimedean cuspidal factor, but that
is a different test-function contract and is not silently included here.

## 14. Final synthesis

### 14.1 The geometric proof ledger

The proof can be audited by matching every type of rational element with its mechanism:

$$
\begin{aligned}
&Z(F)\backslash Z(F)
&&\longrightarrow
\operatorname{vol}([\overline G])f(1),\\
&\text{split regular classes}
&&\longrightarrow
\text{two stable lines, Borel unfolding, zero parabolic transform},\\
&\text{noncentral repeated-root class}
&&\longrightarrow
\text{one stable line, the same unipotent unfolding},\\
&\text{elliptic classes}
&&\longrightarrow
\kappa(\gamma)a(\gamma)O_\gamma(f).
\end{aligned}
\tag{14.1}
$$

The analytic order is equally rigid:

$$
\begin{aligned}
&\text{canonical rapidly decreasing kernel}
&&\Longrightarrow \text{integrable diagonal},\\
&\text{compact and rational cutoffs}
&&\Longrightarrow \text{legal finite regrouping},\\
&\text{strong local cuspidality}
&&\Longrightarrow \text{zero global parabolic main term},\\
&\text{rank-one boundary estimate}
&&\Longrightarrow \text{no surviving nonelliptic term},\\
&\text{orbit charts and Schwartz decay}
&&\Longrightarrow \text{rapid elliptic orbital decay},\\
&\text{lattice counting and torus geometry}
&&\Longrightarrow \text{absolute elliptic summability}.
\end{aligned}
\tag{14.2}
$$

None of these implications subsumes another.  In particular, trace class does not authorize a
rational-orbit rearrangement, and compactness of each elliptic centralizer quotient does not
give uniform summability over all quadratic tori.

### 14.2 The reusable distribution

Define on the admissible cuspidal test space

$$
I_{\mathrm{ell}}(f)=
\sum_{[\gamma]_{\mathrm{ell}}}\kappa(\gamma)a(\gamma)O_\gamma(f).
\tag{14.3}
$$

Theorem 11.3 proves that this is a continuous distribution.  It is independent of centralizer
measure rescaling, compatible with finite sums of restricted tensors, and factorizes orbit by
orbit into local orbital integrals.  The complete geometric distribution is

$$
I_{\mathrm{geom}}(f)
=\operatorname{vol}([\overline G])f(1)+I_{\mathrm{ell}}(f).
\tag{14.4}
$$

Theorem 12.2 identifies it simultaneously with the canonical diagonal trace and the absolutely
convergent cuspidal spectral trace.  Thus it is ready for local comparison: if two families of
test functions have matching central values and matching elliptic orbital integrals with
compatible quotient measures, their geometric trace distributions agree.  Establishing such
matching is an additional local theorem, not an assumption used in the construction above.

### 14.3 Conclusion

The geometric side of the simple $\mathrm{GL}_2$ trace formula is now a genuine, convergent
distribution.  Degree-two linear algebra divides rational projective conjugacy into four
classes.  The scalar class contributes the quotient volume times $f(1)$.  Rational lines place
the split and nonsemisimple classes inside the unique proper parabolic, where a strongly
cuspidal real factor makes their unfolded main term zero and rapid decay removes the truncation
boundary.  Irreducible characteristic polynomials produce anisotropic projective tori; their
compact adelic quotients supply the coefficients $a(\gamma)$ and their transverse orbits supply
the orbital integrals.  The factor $\kappa(\gamma)=1/2$ on the trace-zero fiber records its extra
projective Weyl stabilizer; it is one on every other elliptic class.

The convergence proof is as structural as the classification.  Local orbit charts measure the
only singularity through the Weyl discriminant, archimedean Schwartz estimates provide
arbitrary decay, arithmetic lattices count rational classes polynomially, and the elementary
geometry of quadratic idele classes bounds centralizer volumes polynomially.  Consequently the
elliptic series is absolutely convergent in precisely the grouping used by the formula.

With the quotient measures synchronized throughout, the central-plus-elliptic expansion equals
the diagonal trace already furnished by the cuspidal kernel theory and therefore equals the
cuspidal spectral expansion.  The geometric side is no longer a formal rearrangement: it is an
ordinary measure-compatible trace distribution, with every nonelliptic disappearance and every
limit accounted for.
