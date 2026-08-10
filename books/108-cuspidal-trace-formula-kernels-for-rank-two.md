# Cuspidal Trace-Formula Kernels for Rank Two

## Contents

- [Introduction](#introduction)
- [1. The simple trace-formula problem](#1-the-simple-trace-formula-problem)
  - [1.1 Why an ordinary trace can exist](#11-why-an-ordinary-trace-can-exist)
  - [1.2 Standing global notation](#12-standing-global-notation)
  - [1.3 The measure and central-character ledger](#13-the-measure-and-central-character-ledger)
  - [1.4 Scope of the theorem](#14-scope-of-the-theorem)
- [2. The test-function class](#2-the-test-function-class)
  - [2.1 Local central-character Schwartz spaces](#21-local-central-character-schwartz-spaces)
  - [2.2 Strong cuspidality](#22-strong-cuspidality)
  - [2.3 Cuspidal factors at a real place](#23-cuspidal-factors-at-a-real-place)
  - [2.4 Global restricted tensor products](#24-global-restricted-tensor-products)
  - [2.5 Adjoint, convolution, and finite type](#25-adjoint-convolution-and-finite-type)
- [3. Periodization and the automorphic kernel](#3-periodization-and-the-automorphic-kernel)
  - [3.1 The kernel formula](#31-the-kernel-formula)
  - [3.2 A projective rational-point count](#32-a-projective-rational-point-count)
  - [3.3 Absolute and differentiated convergence](#33-absolute-and-differentiated-convergence)
  - [3.4 Unfolding to the convolution operator](#34-unfolding-to-the-convolution-operator)
  - [3.5 Covariance and the adjoint kernel](#35-covariance-and-the-adjoint-kernel)
- [4. Parabolic cancellation and cuspidal range](#4-parabolic-cancellation-and-cuspidal-range)
  - [4.1 Global parabolic transforms](#41-global-parabolic-transforms)
  - [4.2 One local zero forces a global zero](#42-one-local-zero-forces-a-global-zero)
  - [4.3 Vanishing of kernel constant terms](#43-vanishing-of-kernel-constant-terms)
  - [4.4 Annihilation of the noncuspidal spectrum](#44-annihilation-of-the-noncuspidal-spectrum)
  - [4.5 Rapid decay in both variables](#45-rapid-decay-in-both-variables)
- [5. Smoothing and finite analytic support](#5-smoothing-and-finite-analytic-support)
  - [5.1 Invariant differentiation of convolution](#51-invariant-differentiation-of-convolution)
  - [5.2 Finite level and finite compact type](#52-finite-level-and-finite-compact-type)
  - [5.3 The cuspidal measuring operator](#53-the-cuspidal-measuring-operator)
  - [5.4 Two-sided Sobolev smoothing](#54-two-sided-sobolev-smoothing)
- [6. Trace class](#6-trace-class)
  - [6.1 The one-sided elliptic factorization](#61-the-one-sided-elliptic-factorization)
  - [6.2 The two-sided Hilbert--Schmidt factorization](#62-the-two-sided-hilbert--schmidt-factorization)
  - [6.3 Trace-norm control and continuity](#63-trace-norm-control-and-continuity)
  - [6.4 Why typewise trace class is enough here](#64-why-typewise-trace-class-is-enough-here)
- [7. The canonical diagonal and the operator trace](#7-the-canonical-diagonal-and-the-operator-trace)
  - [7.1 Why a formal diagonal is insufficient](#71-why-a-formal-diagonal-is-insufficient)
  - [7.2 Identification of the canonical kernel](#72-identification-of-the-canonical-kernel)
  - [7.3 Absolute diagonal integrability](#73-absolute-diagonal-integrability)
  - [7.4 The diagonal trace theorem](#74-the-diagonal-trace-theorem)
- [8. The cuspidal spectral expansion](#8-the-cuspidal-spectral-expansion)
  - [8.1 The discrete decomposition recalled](#81-the-discrete-decomposition-recalled)
  - [8.2 Traces on irreducible summands](#82-traces-on-irreducible-summands)
  - [8.3 Absolute convergence of the spectral side](#83-absolute-convergence-of-the-spectral-side)
  - [8.4 The spectral kernel identity](#84-the-spectral-kernel-identity)
- [9. Rational conjugacy in rank two](#9-rational-conjugacy-in-rank-two)
  - [9.1 Central, split, unipotent, and elliptic elements](#91-central-split-unipotent-and-elliptic-elements)
  - [9.2 Centralizers and quotient measures](#92-centralizers-and-quotient-measures)
  - [9.3 Elliptic orbital distributions](#93-elliptic-orbital-distributions)
  - [9.4 The central term](#94-the-central-term)
- [10. Truncation and parabolic cancellation](#10-truncation-and-parabolic-cancellation)
  - [10.1 Compact truncations](#101-compact-truncations)
  - [10.2 Stable rational lines](#102-stable-rational-lines)
  - [10.3 Unfolding the nonelliptic part](#103-unfolding-the-nonelliptic-part)
  - [10.4 Removal of the truncation](#104-removal-of-the-truncation)
- [11. Absolute convergence of the elliptic expansion](#11-absolute-convergence-of-the-elliptic-expansion)
  - [11.1 Arithmetic height of a projective conjugacy class](#111-arithmetic-height-of-a-projective-conjugacy-class)
  - [11.2 Coarse counting and torus-volume bounds](#112-coarse-counting-and-torus-volume-bounds)
  - [11.3 Decay of orbital integrals](#113-decay-of-orbital-integrals)
  - [11.4 Summability](#114-summability)
- [12. Equality of the two expansions](#12-equality-of-the-two-expansions)
  - [12.1 The geometric expansion](#121-the-geometric-expansion)
  - [12.2 The simple cuspidal trace formula](#122-the-simple-cuspidal-trace-formula)
  - [12.3 Independence of auxiliary truncations](#123-independence-of-auxiliary-truncations)
  - [12.4 Factorization without evaluation](#124-factorization-without-evaluation)
- [13. Examples, boundaries, and failure modes](#13-examples-boundaries-and-failure-modes)
  - [13.1 A weight-$k$ kernel over the rationals](#131-a-weight-k-kernel-over-the-rationals)
  - [13.2 Adding finite-place Hecke conditions](#132-adding-finite-place-hecke-conditions)
  - [13.3 What fails without a cuspidal factor](#133-what-fails-without-a-cuspidal-factor)
  - [13.4 What this formula does not yet compute](#134-what-this-formula-does-not-yet-compute)
- [14. Final synthesis](#14-final-synthesis)
  - [14.1 The proof ledger](#141-the-proof-ledger)
  - [14.2 The reusable kernel theorem](#142-the-reusable-kernel-theorem)
  - [14.3 Conclusion](#143-conclusion)

## Introduction

A trace formula begins with a deceptively finite-dimensional picture.  If a matrix $A$ has
kernel $(A_{ij})$, then its trace is at once the sum of its eigenvalues and the sum of its
diagonal entries.  On an automorphic quotient both expressions become infinite.  The
eigenvectors belong to infinitely many automorphic representations, the geometric kernel is a
sum over rational matrices, and the quotient on which its diagonal is integrated is noncompact.
None of the three infinite operations is automatically legitimate.

For $mathrm{GL}_2$ there is a particularly clean way to remove the obstruction.  Choose the
archimedean test function to be cuspidal at one real place.  Its parabolic averages vanish.  The
resulting global convolution operator kills the Eisenstein and residual subspaces, and its range
lies in the discrete cuspidal space.  Cuspidal decay prevents mass from escaping into the unique
rank-one cusp.  Elliptic smoothing then makes the operator trace class, so its spectral trace and
its diagonal trace are ordinary absolutely convergent quantities.  Finally, rank-two rational
conjugacy separates the diagonal into a central term and elliptic orbital terms; all proper
parabolic terms vanish.

The word *simple* in “simple trace formula” refers to this removal of the parabolic channel.  It
does not mean that convergence may be ignored.  In fact, the purpose of this book is to prove
every interchange that turns the formal identity

$$
\sum_\pi m(\pi)\operatorname{tr}\pi(f)
\stackrel{?}{=}
\int_{[\overline G]}\sum_\gamma f(x^{-1}\gamma x)\,dx
$$

into a theorem.  The proof is organized so that each infinity has a separate control:
rational-point counting controls periodization, constant-term cancellation controls the cusp,
Sobolev smoothing controls singular values, and arithmetic height controls elliptic conjugacy
classes.

The preceding books supply four exact foundations.  The Hilbert-space theory supplies
Hilbert--Schmidt factorizations, trace ideals, and safe diagonal formulas.  The Sobolev theory
supplies elliptic estimates, polynomial spectral counting, and rapidly decreasing kernels on
cuspidal spaces.  Adelic reduction theory supplies the finite-volume quotient, its measures,
the closed cuspidal subspace, and its discrete finite-multiplicity decomposition.  The rank-one
constant-term theory supplies the decisive theorem that one strongly cuspidal local factor
annihilates all Eisenstein wave packets and all residues.  We recall each interface when it is
used and prove the additional kernel and geometric arguments here.

Detailed evaluation of the cuspidal characters is not part of the present task, nor is detailed
evaluation of central and elliptic orbital integrals.  Those computations require their own
normalization and local harmonic analysis.  Here the goal is prior and indispensable: to prove
that both expansions exist, converge absolutely in their natural grouped forms, and equal the
same operator trace.

## 1. The simple trace-formula problem

### 1.1 Why an ordinary trace can exist

The full automorphic $L^2$ space is not a discrete sum.  Its constant terms propagate down the
cusp and generate continuous Eisenstein families.  Consequently a general convolution operator
does not have an ordinary trace on the full space; one normally truncates and regularizes.  A
cuspidal local factor changes the problem rather than regularizing it.  It makes the convolution
operator zero on the entire noncuspidal channel.  The only remaining Hilbert space is the closed
cuspidal subspace, where fixed-level, fixed-type elliptic operators have compact resolvent.

There are still two tasks.  First, an arbitrary bounded operator on a discrete Hilbert sum need
not be trace class.  Smooth convolution must be combined with a polynomial eigenvalue count.
Second, the Poincare series defining the kernel must be shown to represent that trace-class
operator with an integrable canonical diagonal.  These tasks are analytic and cannot be replaced
by the representation-theoretic statement that the spectrum is discrete.

The eventual identity will have the form

$$
\operatorname{tr}R_\omega(f)
=\sum_{\pi}m(\pi)\operatorname{tr}\pi(f)
=\operatorname{vol}([\overline G])f(1)
 +\sum_{[\gamma]_{\mathrm{ell}}}a(\gamma)O_\gamma(f).
\tag{1.1}
$$

The middle sum is the spectral expansion and the right side is the geometric expansion.  The
main theorem will state the test-function hypotheses under which both sums converge absolutely.

### 1.2 Standing global notation

Let $F$ be a number field with at least one real place, and let $\mathbf A=\mathbf A_F$.  Put

$$
G=\mathrm{GL}_2,\qquad Z=\text{the scalar center},\qquad
B=TN,
$$

where

$$
N=\left\{n(u)=\begin{pmatrix}1&u\\0&1\end{pmatrix}\right\},
\qquad
T=\left\{\operatorname{diag}(a,d)\right\}.
$$

The central quotient is

$$
[\overline G]=Z(\mathbf A)G(F)\backslash G(\mathbf A).
\tag{1.2}
$$

It has finite volume.  Fix a unitary idele class character

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times.
$$

The Hilbert space $L^2_\omega$ consists of functions on $G(F)\backslash G(\mathbf A)$ satisfying

$$
\phi(zg)=\omega(z)\phi(g)
\tag{1.3}
$$

and square-integrable on (1.2).  Its closed cuspidal subspace is denoted
$L^2_{\mathrm{cusp},\omega}$.  Cuspidality means

$$
\phi_N(g)=\int_{F\backslash\mathbf A}\phi(n(u)g)\,d\bar u=0
\tag{1.4}
$$

for every $g$, initially for smooth vectors and then in the closed $L^2$ sense.  Since every
proper $F$-parabolic of $G$ is rationally conjugate to $B$, (1.4) at all right translates is the
full cuspidality condition.

Choose a real place $v_0$.  It is at this place that the test function will be strongly
cuspidal.  This hypothesis is not an artificial restriction: $\mathrm{GL}_2(\mathbf C)$ has no
discrete series modulo center, whereas a real place supplies discrete-series coefficients and
pseudo-coefficients with the required parabolic cancellation.

### 1.3 The measure and central-character ledger

At every finite place normalize $|\varpi_v|_v=q_v^{-1}$, and at a complex place use the square
of the ordinary complex modulus.  Give maximal compact subgroups probability Haar measure.
Use the Iwasawa Haar measures and quotient measures fixed by adelic reduction theory.  On
$F\backslash\mathbf A$, $d\bar u$ is probability measure.

There are two compatible descriptions of this last measure.  Integer-ring measure at finite
places and ordinary archimedean measure give additive covolume
$2^{-r_2}|d_F|^{1/2}$; dividing by it gives $d\bar u$.  Self-dual local measures for the standard
global additive character have product covolume one and induce the same probability quotient
measure.  Thus constant terms and factorizable local unipotent integrals differ by no hidden
global scalar.

A test function has inverse central character:

$$
f(zg)=\omega(z)^{-1}f(g).
\tag{1.5}
$$

Although neither factor in

$$
f(g)\phi(xg)
$$

descends separately to $Z(\mathbf A)\backslash G(\mathbf A)$, their product does.  We define

$$
(R_\omega(f)\phi)(x)
=\int_{Z(\mathbf A)\backslash G(\mathbf A)}f(g)\phi(xg)\,d\bar g.
\tag{1.6}
$$

All orbital quotient measures below are obtained from the same Haar measures by iterated
quotient integration.  This convention is essential: an orbital integral and the volume of its
centralizer quotient must use complementary measures for their product to be intrinsic.

### 1.4 Scope of the theorem

We shall prove (1.1) for factorizable Schwartz test functions that are finite under the left and
right maximal compact actions, compactly supported modulo the center at finite places, and
strongly cuspidal at $v_0$.  Finite sums of such tensors are allowed by linearity.

The theorem includes:

1. absolute locally uniform convergence of the automorphic kernel and all its derivatives;
2. operator-level annihilation of the continuous and residual subspaces;
3. trace-classness on the whole fixed-central-character $L^2$ space;
4. an absolutely integrable canonical diagonal;
5. an absolutely convergent cuspidal spectral expansion;
6. an absolutely convergent central-plus-elliptic geometric expansion;
7. equality of those expansions without regularization.

It does not evaluate $\operatorname{tr}\pi(f)$ or $O_\gamma(f)$.  Keeping existence separate
from evaluation prevents a circular argument: local character and orbital calculations may use
the trace formula only after the trace formula itself has been analytically justified.

For later reference, here is the precise dependency contract.  From Book 100 we use the
Hilbert--Schmidt kernel theorem, the characterization of trace class as a product of two
Hilbert--Schmidt operators, cyclicity of trace, and the two-kernel contraction formula.  From
Book 101 we use Proposition 9.1 and Theorem 11.1: on fixed finite level and compact type the
cuspidal measuring operator has a polynomial counting function, its high inverse powers are
trace class, and their kernels are smooth and rapidly decreasing.  From Book 102 we use
Theorem 9.1, Theorem 10.1, and Theorem 12.1: the cuspidal subspace is closed, its Sobolev form
domain embeds compactly, and it has the discrete finite-multiplicity decomposition recalled in
Chapter 8 below.  From Book 103 we use Theorem 13.1, whose test-function hypothesis is exactly
(2.2) at one place and whose conclusion is operator-level annihilation of induced families,
wave packets, and residues.  We do not use the weaker trace-only Corollary 13.2.  Thus every
imported conclusion is applied with the same fixed central character, finite level, finite
archimedean type, and Haar measures with which it was proved.

## 2. The test-function class

### 2.1 Local central-character Schwartz spaces

Let $v$ be a place of $F$.  Write $G_v=G(F_v)$ and $Z_v=Z(F_v)$.  At a finite place define
$\mathcal H(G_v,\omega_v^{-1})$ to be the smooth, locally constant functions satisfying (1.5)
whose support has compact image in $Z_v\backslash G_v$.  At an archimedean place let
$\mathcal C(G_v,\omega_v^{-1})$ be the Harish--Chandra Schwartz space modulo $Z_v$, again with
central transformation (1.5).

For the arguments below it is useful to state the decay concretely.  Choose a proper
submultiplicative norm $\|\cdot\|_v\geq1$ on $Z_v\backslash G_v$.  For every left-right invariant
differential operator $D$ and every $A>0$, an archimedean Schwartz function satisfies

$$
|Df_v(g)|\leq C_{D,A}\|g\|_v^{-A}.
\tag{2.1}
$$

Equivalent norms give the same space.  We additionally require finite left and right
$K_v$-type.  This makes the eventual global operator land in finitely many compact types; it is
not needed merely to define the local integral.

At almost every finite place, $\omega_v$ is unramified and the distinguished function is the
normalized central-character extension of the characteristic function of $K_v$.  Its precise
scalar is chosen so that it is the identity on the unramified $K_v$-fixed line.  Restricted
products formed with these distinguished functions are well defined.

### 2.2 Strong cuspidality

Ordinary vanishing of the total integral removes at most the trivial representation.  The
parabolic channel contains every principal series, so the cancellation must retain both left
and right variables.

**Definition 2.1.** A local test function $f_v$ is **strongly cuspidal** if

$$
\int_{N_v}f_v(x^{-1}tny)\,dn=0
\tag{2.2}
$$

for every $x,y\in G_v$ and $t\in T_v$.  At an archimedean place absolute convergence is part of
the definition.

The condition is stable under left and right translation.  It is also stable under the adjoint

$$
f_v^*(g)=\overline{f_v(g^{-1})}.
\tag{2.3}
$$

Indeed, invert $x^{-1}tny$, use $n^{-1}\in N_v$, and conjugate the unipotent variable by the
torus.  Haar measure changes by the modular character, a harmless nonzero scalar, and the
resulting integral is another instance of (2.2).

The representation-theoretic meaning is exact.

**Proposition 2.2.** If $f_v$ is strongly cuspidal, then every representation smoothly induced
from $B_v$ satisfies

$$
I_v(\chi_v,s)(f_v)=0.
\tag{2.4}
$$

**Proof.** In the compact picture the operator kernel between compact-picture points $x$ and
$y$ is

$$
\int_{T_v}\chi_v(t)|\alpha(t)|_v^{s}\delta_B(t)^{1/2}
 \left(\int_{N_v}f_v(x^{-1}tny)\,dn\right)dt.
$$

The inner integral is zero.  This proves (2.4) in the chamber of absolute convergence.
Meromorphic continuation of the finite-dimensional compact-type matrix coefficients proves it
for all $s$.  $\square$

### 2.3 Cuspidal factors at a real place

At $v_0$, choose a discrete-series representation $D$ of $\mathrm{GL}_2(\mathbf R)$ with the
central character compatible with $\omega_{v_0}^{-1}$.  A compact-finite matrix coefficient of
$D$, or a finite linear combination forming a pseudo-coefficient, belongs to the Schwartz space
modulo the center and is strongly cuspidal.

The last assertion is the archimedean constant-term theorem established in the preceding
constant-term theory.  Its hypotheses match ours: the coefficient is square-integrable modulo
the center, compact-finite, and its unipotent integrals are absolutely convergent.  Orthogonality
of discrete series to parabolically induced representations makes the compact-picture kernel in
Proposition 2.2 zero, and left-right translates give the full two-sided condition (2.2).

This construction explains the phrase “cuspidal archimedean factor.”  We use actual
operator-level cuspidality, not merely a function whose induced characters happen to have trace
zero.  The stronger condition is what permits constant terms, residues, and kernels to be
handled before taking traces.

### 2.4 Global restricted tensor products

Let

$$
f=\bigotimes_v f_v
\tag{2.5}
$$

with $f_v$ in the local space just defined, distinguished spherical factors almost everywhere,
and $f_{v_0}$ strongly cuspidal.  We call such an $f$ an **admissible cuspidal test function**.
A finite sum of admissible tensors will be called admissible as well, provided every tensor has
a strongly cuspidal factor at the same real place.

The global function is smooth, has rapid archimedean decay modulo the center, and has compact
finite-adelic support modulo the center.  It is integrable on
$Z(\mathbf A)\backslash G(\mathbf A)$, as are all its invariant derivatives.  Young's inequality
therefore makes (1.6) a bounded operator and gives

$$
\|R_\omega(Df)\|\leq\|Df\|_{L^1}.
\tag{2.6}
$$

Factorization is used only where it is legitimate.  For absolutely convergent integrals,

$$
I(\chi,s)(f)=\bigotimes_v I_v(\chi_v,s)(f_v).
\tag{2.7}
$$

Since the $v_0$ factor is zero, the global induced operator is zero.  Continuation preserves the
identity.

### 2.5 Adjoint, convolution, and finite type

The adjoint of (1.6) is $R_\omega(f^*)$, with $f^*$ defined by (2.3) place by place.  Unimodularity
and the substitution $g\mapsto g^{-1}$ prove

$$
\langle R_\omega(f)u,v\rangle
=\langle u,R_\omega(f^*)v\rangle.
\tag{2.8}
$$

If $f,h$ have compatible central character conventions and their convolution is defined on the
central quotient, Fubini gives

$$
R_\omega(f*h)=R_\omega(f)R_\omega(h).
\tag{2.9}
$$

For trace-classness we shall not need to factor $f$ itself as one convolution.  Instead we use
elliptic half-powers.  This matters because an arbitrary algebraic factorization need not place
cuspidality in both factors.

Finite left $K$-type of $f$ implies that the range of $R_\omega(f)$ lies in finitely many right
compact types; finite right $K$-type gives the corresponding statement for the adjoint.  At the
finite adeles, local constancy and compact support give compact open subgroups $K_f^L,K_f^R$ such
that

$$
R_\omega(f)=P_LR_\omega(f)P_R,
\tag{2.10}
$$

where $P_L,P_R$ project to finite sums of fixed-level, fixed-archimedean-type spaces.  To verify
the left equality, average $\pi(k)\pi(f)$ and use left invariance or finite left type; the right
equality follows similarly from $\pi(f)\pi(k)$.

## 3. Periodization and the automorphic kernel

### 3.1 The kernel formula

The projective rational group $Z(F)\backslash G(F)$ is the correct index set.  Define

$$
K_f(x,y)=\sum_{\gamma\in Z(F)\backslash G(F)}
 f(x^{-1}\gamma y).
\tag{3.1}
$$

This expression is independent of the representative of $\gamma$: an idele class character is
trivial on $F^\times$.  It has the covariance

$$
K_f(z_1x,z_2y)=\omega(z_1)\omega(z_2)^{-1}K_f(x,y),
\tag{3.2}
$$

so it is a kernel between the central-character line bundles on $[\overline G]$.

The sum is visibly finite on compact sets when every archimedean factor is compactly supported
modulo center.  A discrete-series coefficient is only rapidly decreasing, so a counting
argument is required in our actual test class.

### 3.2 A projective rational-point count

Choose a proper height $H$ on $Z(\mathbf A)\backslash G(\mathbf A)$ satisfying

$$
H(ab)\leq H(a)^cH(b)^c
\tag{3.3}
$$

for a fixed $c$.  One may take the product over places of the maximum of the entries and the
entries of the inverse, minimized over scalar multiplication.

**Lemma 3.1.** For compact sets $C_1,C_2$ in $G(\mathbf A)$ modulo the center, and for a fixed
compact finite-adelic set $C_f$, there are constants $A,C$ such that

$$
\#\{\gamma\in Z(F)\backslash G(F):
 x^{-1}\gamma y\in C_fG_\infty,\ H(x^{-1}\gamma y)\leq X\}
\leq CX^A
\tag{3.4}
$$

for $x\in C_1$, $y\in C_2$, and $X\geq1$.

**Proof.** The finite support bounds the denominators of the four matrix entries in one fixed
fractional ideal.  Modulo a scalar, choose a primitive representative, meaning that the entries
generate one of finitely many ideal classes.  Multiplying by one of finitely many class
representatives puts the four entries in a fixed lattice in $F_\infty^4$.  The height bound puts
that lattice point in a box of side at most a fixed power of $X$.  A lattice has at most
$O(X^A)$ points in such a box.  The determinant-zero locus is discarded, and passing from
primitive matrices to projective classes only decreases the count.  Multiplication by $x$ and
$y$ in fixed compact sets changes all bounds by a constant.  Summing over the finitely many
ideal classes proves (3.4).  $\square$

The exponent is intentionally coarse.  Arbitrary power decay of a Schwartz function makes any
fixed polynomial exponent sufficient.

### 3.3 Absolute and differentiated convergence

**Theorem 3.2.** For an admissible test function, (3.1) and every series obtained from it by
invariant differentiation in $x$ and $y$ converge absolutely and locally uniformly on
$G(\mathbf A)\times G(\mathbf A)$.  Hence $K_f$ is smooth in the archimedean variables and
locally constant in the finite variables.

**Proof.** Fix compact sets for $x$ and $y$.  Divide the rational elements into height shells
$2^j\leq H(x^{-1}\gamma y)<2^{j+1}$.  Lemma 3.1 bounds the number in the $j$-th shell by
$C2^{Aj}$.  For any $M$, (2.1) bounds a differentiated summand by $C_M2^{-Mj}$.  Taking $M>A+1$
makes

$$
\sum_{j\geq0}C2^{Aj}2^{-Mj}
$$

converge.  The constants are uniform on the chosen compact sets.  The Weierstrass criterion
gives local uniform convergence, and applying it to every derivative justifies termwise
differentiation.  $\square$

Local uniform convergence is not yet a trace theorem.  It says that the periodized formula is a
genuine smooth kernel; it says nothing about integrability as $x$ and $y$ enter a cusp.

### 3.4 Unfolding to the convolution operator

**Proposition 3.3.** The integral operator defined by $K_f$ is $R_\omega(f)$ on a dense subspace
of compactly supported smooth automorphic vectors, and hence on all of $L^2_\omega$.

**Proof.** Let $\phi$ be compactly supported modulo $Z(\mathbf A)G(F)$.  Absolute convergence
from Theorem 3.2 and compact support permit Tonelli.  Integrating (3.1) over a fundamental region
and translating its rational copies gives

$$
\begin{aligned}
\int_{[\overline G]}K_f(x,y)\phi(y)\,dy
&=\int_{[\overline G]}\sum_\gamma
 f(x^{-1}\gamma y)\phi(y)\,dy\\
&=\int_{Z(\mathbf A)\backslash G(\mathbf A)}
 f(x^{-1}y)\phi(y)\,dy.
\end{aligned}
$$

Set $y=xg$ and use right invariance of quotient measure.  The result is (1.6).  Boundedness of
$R_\omega(f)$ and density extend the equality.  $\square$

### 3.5 Covariance and the adjoint kernel

The kernel of the adjoint is

$$
K_{f^*}(x,y)=\overline{K_f(y,x)}.
\tag{3.5}
$$

Indeed, invert the rational index and use (2.3).  This elementary identity has an important
consequence.  Every estimate proved for the first variable using $f$ has a corresponding
estimate for the second variable using $f^*$.  Because strong cuspidality survives adjoint,
cuspidal decay will be available on both sides of the diagonal.

## 4. Parabolic cancellation and cuspidal range

### 4.1 Global parabolic transforms

For $x,y\in G(\mathbf A)$ and $t\in T(\mathbf A)$ define

$$
f_B(x,y;t)=\delta_B(t)^{1/2}
\int_{N(\mathbf A)}f(x^{-1}tny)\,dn.
\tag{4.1}
$$

The integral converges absolutely.  At finite places this follows from compact support modulo
the center; at infinity it follows from Schwartz decay and the polynomial volume growth of
$N(F_v)$.  For a tensor $f=\otimes f_v$, Fubini and the product measure give

$$
f_B(x,y;t)=\prod_v (f_v)_B(x_v,y_v;t_v).
\tag{4.2}
$$

This is why the compatibility of the global probability measure with the product of self-dual
local measures was recorded in Section 1.3.

### 4.2 One local zero forces a global zero

**Lemma 4.1.** If $f_{v_0}$ is strongly cuspidal, then

$$
f_B(x,y;t)=0
\tag{4.3}
$$

for every $x,y,t$.  The same holds for $f^*$.

**Proof.** The $v_0$ factor in (4.2) is the integral (2.2), multiplied by a nonzero modular
factor, and is zero.  The assertion for $f^*$ follows from stability of strong cuspidality under
adjoint.  $\square$

The strength of (4.3) should be noted.  It is not merely the vanishing of an averaged trace; the
left and right variables remain free.  Consequently it controls the range of the operator and
both variables of its kernel.

### 4.3 Vanishing of kernel constant terms

**Proposition 4.2.** For every fixed $y$, the function $x\mapsto K_f(x,y)$ is cuspidal.  For every
fixed $x$, the conjugate-dual section $y\mapsto K_f(x,y)$ is cuspidal.  All differentiated
constant terms vanish as well.

**Proof.** Average (3.1) over $N(F)\backslash N(\mathbf A)$.  Rational elements are grouped by
$B(F)\backslash G(F)$, which parametrizes rational lines.  Within one group, the sum over
$N(F)$ and the quotient integral unfold to the full $N(\mathbf A)$ integral in (4.1).  Absolute
convergence on truncated cusp regions follows from Theorem 3.2; Schwartz decay then permits the
truncation to tend to infinity.  Each unfolded term is zero by (4.3).  Thus the constant term in
$x$ vanishes.  Applying (3.5) and the same argument to $f^*$ proves the assertion in $y$.
Differentiation is permitted by Theorem 3.2 and only replaces $f$ by a derivative, whose
parabolic transform is still zero because (2.2) allows arbitrary left and right translates.
$\square$

### 4.4 Annihilation of the noncuspidal spectrum

There is a second, spectral proof of the range statement, and it supplies more information.  The
rank-one constant-term theory classifies the noncuspidal closed subspace, at fixed level and
finite type, as the closure of unitary Eisenstein wave packets and one-dimensional residual
characters.  Proposition 2.2 and restricted tensor factorization make $R_\omega(f)$ zero on
every induced representation.  Convolution through the Eisenstein sum, followed by continuation,
makes it zero on every Eisenstein series; integration makes it zero on wave packets; taking
residues makes it zero on residual characters.

Therefore

$$
R_\omega(f)=P_{\mathrm{cusp}}R_\omega(f)P_{\mathrm{cusp}},
\tag{4.4}
$$

where $P_{\mathrm{cusp}}$ is the orthogonal cuspidal projection.  The right equality uses
invariance of the cuspidal subspace and annihilation of its orthogonal complement; applying the
same statement to $f^*$ gives the left equality.

This argument verifies the exact dependency hypotheses.  The central character is unitary, the
test is factorizable and finite-level, and the local hypothesis is the strong two-sided condition,
not merely trace-level vanishing.  Hence no residual contribution is left untreated.

### 4.5 Rapid decay in both variables

Cuspidal smooth vectors of fixed level and type decay rapidly in every cusp with all invariant
derivatives.  Applied to the kernel, this gives a two-variable form.

**Proposition 4.3.** Let $\operatorname{ht}(x)\geq1$ be the adelic cusp height from reduction
theory.  For invariant differential operators $D_x,D_y$ and integers $A,B\geq0$, there is a
continuous seminorm $\nu$ on the admissible test space such that

$$
|D_xD_yK_f(x,y)|
\leq \nu(f)\operatorname{ht}(x)^{-A}\operatorname{ht}(y)^{-B}.
\tag{4.5}
$$

The estimate is uniform after $x,y$ are reduced into the finitely many cusp charts belonging to
the fixed finite level.

**Proof.** First fix $y$ in a compact set.  Proposition 4.2 gives zero constant term in $x$;
the invariant Sobolev bounds obtained by differentiating the periodization are locally uniform
in $y$.  The transverse Poincare inequality and Sobolev embedding from cuspidal Sobolev theory
then give arbitrary power decay in $\operatorname{ht}(x)$.  Apply the same argument to (3.5) for
decay in $y$.  To make the bounds simultaneous, apply the first argument to the finitely many
$y$-Sobolev derivatives required by the second Sobolev embedding.  The differentiated
periodization seminorms are bounded by finitely many Schwartz seminorms of $f$.  Iterating with
arbitrary orders proves (4.5).  $\square$

Because the quotient measure has cusp density comparable to $dH/H^2$, any sufficiently large
choice of $A$ and $B$ makes the right side integrable in either or both variables.

## 5. Smoothing and finite analytic support

### 5.1 Invariant differentiation of convolution

Let $D$ be a right-invariant differential operator acting on the output variable.  Moving $D$
through (1.6), with the appropriate left derivative $D'$ on the test function, gives

$$
DR_\omega(f)=R_\omega(D'f).
\tag{5.1}
$$

Young's inequality and (2.6) imply, for every invariant Sobolev order $s$,

$$
\|R_\omega(f)u\|_{H^s}
\leq C_s\nu_s(f)\|u\|_2,
\tag{5.2}
$$

where $\nu_s$ is a finite sum of $L^1$ norms of derivatives of $f$.  Applying this to $f^*$ and
duality shows that $R_\omega(f)$ maps $H^{-s}$ continuously to $L^2$.  Combining the two sides,

$$
R_\omega(f):H^{-s}\longrightarrow H^t
\tag{5.3}
$$

continuously for all $s,t\geq0$.  Thus convolution is infinitely smoothing in the sense needed
for an elliptic factorization.

### 5.2 Finite level and finite compact type

Equation (2.10) confines the operator to two finite analytic data sets.  Let

$$
\mathcal H_L=P_L L^2_{\mathrm{cusp},\omega},\qquad
\mathcal H_R=P_R L^2_{\mathrm{cusp},\omega}.
\tag{5.4}
$$

Each is a finite direct sum of spaces with one compact open level and one archimedean maximal
compact type.  Enlarging the level and the finite type set if necessary, we may place both in a
single finite-data space $\mathcal H_0$.  Then

$$
R_\omega(f)=P_0R_\omega(f)P_0.
\tag{5.5}
$$

This is the point at which a possible infinite sum over compact types disappears.  A general
Schwartz convolution operator might require uniform trace-norm estimates over all types.  Our
finite-type hypothesis makes only finitely many of them occur.

### 5.3 The cuspidal measuring operator

On $\mathcal H_0$, let $A\geq1$ be the positive self-adjoint elliptic measuring operator from
cuspidal Sobolev theory.  It includes a positive compact-direction operator, so it is elliptic on
the fixed types.  Its form domain embeds compactly, hence it has compact resolvent.  Write its
eigenvalues, with multiplicity, as

$$
1\leq\lambda_1\leq\lambda_2\leq\cdots,
$$

and its counting function as $N_A(\Lambda)$.  The established polynomial bound gives constants
$C,D$ such that

$$
N_A(\Lambda)\leq C(1+\Lambda)^D.
\tag{5.6}
$$

Consequently

$$
A^{-r}\text{ is trace class if }r>D,
\qquad
A^{-r}\text{ is Hilbert--Schmidt if }2r>D.
\tag{5.7}
$$

To see this directly, divide the eigenvalues into dyadic intervals.  The contribution to
$\sum\lambda_j^{-r}$ from $2^k\leq\lambda_j<2^{k+1}$ is at most
$C2^{kD}2^{-kr}$, which is summable for $r>D$.  The square-sum statement is identical with
$r$ replaced by $2r$.

### 5.4 Two-sided Sobolev smoothing

Elliptic norm equivalence translates (5.3) into the boundedness of

$$
A^rR_\omega(f)A^s
\tag{5.8}
$$

on $\mathcal H_0$ for every $r,s\geq0$, initially on the algebraic span of eigenvectors and then
by closure.  Indeed, the right factor $A^s$ measures a positive Sobolev order in the input;
duality moves it to a negative-order source, and infinite smoothing gains the orders required by
the left factor.

More quantitatively, for every $r,s$ there is a Schwartz seminorm $\nu_{r,s}$ with

$$
\|A^rR_\omega(f)A^s\|\leq C_{r,s}\nu_{r,s}(f).
\tag{5.9}
$$

This estimate will control both trace norm and convergence under approximation of the test
function.

## 6. Trace class

### 6.1 The one-sided elliptic factorization

Choose an integer $r>D$.  From (5.8), $A^rR_\omega(f)$ is bounded, while $A^{-r}$ is trace class.
Thus on $\mathcal H_0$,

$$
R_\omega(f)=A^{-r}\big(A^rR_\omega(f)\big)
\tag{6.1}
$$

is trace class.  On the orthogonal complement of $\mathcal H_0$ it is zero by (5.5), so it is
trace class on all of $L^2_\omega$.

This proof makes the logical roles transparent.  Cuspidality supplies compact resolvent;
polynomial counting supplies summability of $A^{-r}$; smooth convolution supplies boundedness
of the other factor; finite type prevents an uncontrolled infinite direct sum.

### 6.2 The two-sided Hilbert--Schmidt factorization

For the diagonal formula, choose $r$ with $2r>D$.  Put

$$
S=A^rR_\omega(f)A^r.
$$

Then $S$ is bounded and

$$
R_\omega(f)=A^{-r}SA^{-r}.
\tag{6.2}
$$

Both outer factors are Hilbert--Schmidt, so their product through the bounded operator $S$ is
trace class.  More explicitly, $A^{-r}S$ is Hilbert--Schmidt and

$$
\|R_\omega(f)\|_1
\leq\|A^{-r}\|_2^2\|S\|.
\tag{6.3}
$$

Unlike a formal restriction of an $L^2$ kernel to its diagonal, (6.2) provides an honest
two-kernel contraction.  It will be the safe route from operator trace to diagonal integral.

### 6.3 Trace-norm control and continuity

Combining (5.9) and (6.3) gives

$$
\|R_\omega(f)\|_1\leq C\nu_{r,r}(f).
\tag{6.4}
$$

Hence the trace distribution

$$
f\longmapsto\operatorname{tr}R_\omega(f)
\tag{6.5}
$$

is continuous on each fixed finite-level, finite-type admissible Schwartz space.  If $f_n\to f$
in that topology, then $R_\omega(f_n)\to R_\omega(f)$ in trace norm and their traces converge.

This continuity permits compactly supported archimedean approximations to be removed without
changing the identity.  It is also what makes finite sums of factorizable tests harmless: prove
the formula tensor by tensor and use linearity and (6.4).

### 6.4 Why typewise trace class is enough here

The typewise compact-resolvent theorem alone would not imply trace class on the whole cuspidal
space.  An infinite direct sum of trace-class blocks is trace class only when the sum of their
trace norms converges.  Equation (5.5) is stronger: all but finitely many level-type blocks are
exactly zero.  Therefore the finite sum of their trace norms is automatically finite.

This is one reason for retaining compact-finiteness in the test class.  A larger Schwartz algebra
can also be treated, but it requires quantitative decay of the test function in the compact dual
and an additional summation theorem.  That extension is unnecessary for the simple kernel used
here.

## 7. The canonical diagonal and the operator trace

### 7.1 Why a formal diagonal is insufficient

An $L^2$ kernel is defined only almost everywhere on a product space.  The diagonal has product
measure zero, so changing an $L^2$ representative there changes the expression $K(x,x)$ without
changing the operator.  Moreover, a Hilbert--Schmidt operator need not be trace class.  Thus the
formula

$$
\operatorname{tr}T=\int K(x,x)\,dx
$$

is not a definition.

Our situation has two extra structures.  The Poincare series (3.1) selects a smooth canonical
representative, and the factorization (6.2) proves trace class before the diagonal is used.  We
must still show that the canonical representative agrees with the contraction kernel produced
by (6.2) and that its diagonal is integrable.

### 7.2 Identification of the canonical kernel

Let $H_r(x,y)$ be the smooth rapidly decreasing cuspidal kernel of $A^{-r}$, taking $r$ larger if
necessary to obtain continuity with all derivatives used below.  The kernel of (6.2) is the
iterated contraction

$$
L_f(x,y)=\int\!\!\int H_r(x,u)S(u,v)H_r(v,y)\,du\,dv,
\tag{7.1}
$$

where $S(u,v)$ is understood distributionally if $S$ itself has no pointwise kernel.  Equivalently,
expand $A^{-r}$ in its eigenbasis and interpret (7.1) as an absolutely convergent Sobolev
pairing.  Elliptic smoothing makes $L_f$ smooth.

Both $L_f$ and $K_f$ represent $R_\omega(f)$ by Proposition 3.3 and (6.2).  Their difference is a
smooth kernel representing the zero operator.  Fix $x$.  Pairing the difference against every
compactly supported smooth function in $y$ gives zero.  A smooth function defining the zero
distribution is identically zero.  Hence

$$
L_f(x,y)=K_f(x,y)
\tag{7.2}
$$

for all $x,y$.  This argument upgrades almost-everywhere kernel uniqueness to pointwise equality
using the independently proved smoothness of the Poincare series.

Here is a finite-rank version that makes the construction of $L_f$ explicit.  Let $E_n$ be the
spectral projection of $A$ onto its first $n$ eigenvectors and put

$$
R_n=E_nA^{-r}SA^{-r}E_n.
\tag{7.2a}
$$

Its kernel is the finite sum

$$
L_n(x,y)=\sum_{i,j\leq n}
\lambda_i^{-r}\lambda_j^{-r}
\langle S\phi_j,\phi_i\rangle
\phi_i(x)\overline{\phi_j(y)}.
\tag{7.2b}
$$

The two outer inverse powers gain as many Sobolev orders as desired after $r$ is increased.
Polynomial spectral counting and elliptic pointwise bounds therefore show that $L_n$ is Cauchy,
with all prescribed derivatives, uniformly on compact subsets.  In the cusps the same argument,
combined with rapid decay of the eigenfunctions and their derivatives, is Cauchy in weighted
supremum norms.  Its limit is the smooth kernel denoted $L_f$.  On the other hand,
$R_n\to R_\omega(f)$ in trace norm: spectral projections converge strongly, and finite-rank
compression converges in trace norm for every trace-class operator.  Hence $L_f$ represents
$R_\omega(f)$ and the preceding uniqueness argument applies.

This approximation also settles a possible diagonal ambiguity.  Every $L_n(x,x)$ is a genuine
finite-dimensional diagonal.  The weighted convergence just proved gives

$$
L_n(x,x)\longrightarrow L_f(x,x)=K_f(x,x)
$$

pointwise and in $L^1([\overline G])$.  Thus the diagonal used below is the limit of honest
finite-rank diagonals, not an arbitrary representative of an almost-everywhere kernel.

### 7.3 Absolute diagonal integrability

Set $y=x$ in (4.5).  Choosing $A+B$ larger than the exponent needed for the cusp measure gives

$$
\int_{[\overline G]}|K_f(x,x)|\,dx<\infty.
\tag{7.3}
$$

There is also a purely ideal-theoretic estimate.  Write (6.2) as $UV$ with
$U=A^{-r}S$ and $V=A^{-r}$.  Both are Hilbert--Schmidt.  If $K_U,K_V$ are their $L^2$ kernels,
the diagonal contraction

$$
x\longmapsto\int K_U(x,y)K_V(y,x)\,dy
\tag{7.4}
$$

belongs to $L^1$, because Cauchy--Schwarz on the product gives norm at most
$\|U\|_2\|V\|_2$.  By (7.2), (7.4) is the canonical diagonal $K_f(x,x)$.  This second proof does
not depend on the visual plausibility of a pointwise series.

More precisely, approximate $U$ and $V$ in Hilbert--Schmidt norm by their spectral
compressions.  Their contractions converge in $L^1$ by

$$
\|K_{U_n}K_{V_n}^{\mathrm{op}}-K_UK_V^{\mathrm{op}}\|_{L^1}
\leq \|U_n-U\|_2\|V_n\|_2+\|U\|_2\|V_n-V\|_2.
\tag{7.4a}
$$

The finite contractions are exactly $L_n(x,x)$.  The preceding weighted convergence identifies
their $L^1$ limit with the pointwise diagonal of $K_f$.  This supplies the missing bridge between
the Hilbert--Schmidt equivalence class and the canonical smooth representative.

### 7.4 The diagonal trace theorem

**Theorem 7.1.** For every admissible cuspidal test function,

$$
\operatorname{tr}R_\omega(f)
=\int_{[\overline G]}K_f(x,x)\,dx,
\tag{7.5}
$$

and the integral is absolutely convergent.

**Proof.** Use the Hilbert--Schmidt product formula on $UV$ from Section 7.3.  It identifies the
operator trace with the integral of the contraction (7.4).  Pointwise kernel identification
(7.2) turns that contraction into $K_f(x,x)$, and (7.3) gives absolute convergence.  $\square$

The order of proof is decisive: trace ideal, canonical kernel, integrable diagonal, trace
identity.  Reversing that order would assume the main analytic conclusion.

## 8. The cuspidal spectral expansion

### 8.1 The discrete decomposition recalled

Adelic reduction and cuspidal compactness give the Hilbert direct sum

$$
L^2_{\mathrm{cusp},\omega}
\simeq\widehat\bigoplus_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
M_\pi\otimes\mathcal H_\pi,
\qquad \dim M_\pi=m(\pi)<\infty.
\tag{8.1}
$$

The index set is countable.  On fixed level, compact type, and bounded elliptic window, only
finitely many summands occur, counted with multiplicity and type dimension.  Smooth finite-type
vectors are rapidly decreasing.

Right convolution respects every isotypic summand and acts as

$$
R_\omega(f)|_{M_\pi\otimes\mathcal H_\pi}
=I_{M_\pi}\otimes\pi(f).
\tag{8.2}
$$

No multiplicity-one theorem is being used.  The factor $m(\pi)$ must remain in the trace.

### 8.2 Traces on irreducible summands

Because $f$ is left and right finite under level and compact type, $\pi(f)$ has finite-dimensional
range.  Indeed, the local projectors in (2.10) make its range lie in a finite sum of admissible
fixed-vector and compact-type spaces.  Thus $\pi(f)$ is finite rank and
$\operatorname{tr}\pi(f)$ is an ordinary finite-dimensional trace.

Equivalently, choose an orthonormal basis $(e_{\pi,j})$ adapted to compact types.  Only finitely
many basis vectors can contribute to the diagonal of $\pi(f)$, and

$$
\operatorname{tr}\pi(f)=\sum_j\langle\pi(f)e_{\pi,j},e_{\pi,j}\rangle.
\tag{8.3}
$$

The finiteness is representation by representation.  Absolute convergence over all $\pi$ comes
from global trace class, not from this observation alone.

### 8.3 Absolute convergence of the spectral side

Let $P_\pi$ be the orthogonal projection onto the summand in (8.1).  A trace-class operator
which is block diagonal satisfies

$$
\sum_\pi\|P_\pi R_\omega(f)P_\pi\|_1
=\|R_\omega(f)\|_1.
\tag{8.4}
$$

This follows first for finite sums of projections and then by monotone convergence applied to
$|R_\omega(f)|$, or by the direct-sum criterion for trace ideals.  Therefore

$$
\sum_\pi m(\pi)|\operatorname{tr}\pi(f)|
\leq\sum_\pi m(\pi)\|\pi(f)\|_1
=\|R_\omega(f)\|_1<\infty.
\tag{8.5}
$$

The spectral series is consequently independent of its ordering and may later be regrouped by
local packet or infinitesimal character once those labels are introduced.

### 8.4 The spectral kernel identity

**Theorem 8.1.** For an admissible cuspidal test function,

$$
\int_{[\overline G]}K_f(x,x)\,dx
=\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
m(\pi)\operatorname{tr}\pi(f),
\tag{8.6}
$$

and both sides are absolutely convergent in the senses of (7.3) and (8.5).

**Proof.** Equation (4.4) makes the operator zero off the cuspidal space.  Take the trace in the
orthogonal decomposition (8.1), use (8.2), and apply the direct-sum trace identity justified by
(8.4).  The diagonal trace theorem identifies the same trace with the left side.  $\square$

This completes the spectral half of the trace formula without invoking a Plancherel formula for
the full automorphic space.

## 9. Rational conjugacy in rank two

### 9.1 Central, split, unipotent, and elliptic elements

The geometric expansion is governed by a classification peculiar to degree two.  For
$\gamma\in G(F)$ let

$$
p_\gamma(X)=X^2-\operatorname{tr}(\gamma)X+\det(\gamma),
\qquad
\Delta(\gamma)=\operatorname{tr}(\gamma)^2-4\det(\gamma).
\tag{9.1}
$$

Exactly one of the following occurs.

1. **Central:** $\gamma=zI$.
2. **Split regular:** $\Delta(\gamma)$ is a nonzero square in $F$; there are two distinct
   $F$-eigenlines.
3. **Noncentral nonsemisimple:** $\Delta(\gamma)=0$ but $\gamma$ is not central; there is one
   $F$-eigenline and $\gamma$ is a scalar times a nontrivial unipotent element.
4. **Elliptic:** $p_\gamma$ is irreducible over $F$; there is no $F$-eigenline.

**Proof.** The minimal polynomial has degree at most two.  If it has degree one, $\gamma$ is
central.  If it has two distinct roots in $F$, their eigenspaces give case 2.  A repeated root
gives either a scalar matrix or one Jordan block, case 3.  If there is no root in $F$, the
quadratic characteristic polynomial is irreducible, case 4.  These alternatives are exhaustive
and disjoint.  $\square$

Multiplication by a rational scalar does not change the classification.  Thus it descends to
$Z(F)\backslash G(F)$.

### 9.2 Centralizers and quotient measures

For noncentral $\gamma$, let $G_\gamma$ be its algebraic centralizer and put
$\overline G_\gamma=G_\gamma/Z$.  If $\gamma$ is regular, then

$$
F[\gamma]\simeq
\begin{cases}
F\times F,&\gamma\text{ split},\\
E,&\gamma\text{ elliptic},
\end{cases}
$$

where $E/F$ is quadratic, and $G_\gamma\simeq F[\gamma]^\times$ as an $F$-torus.  In the elliptic
case $\overline G_\gamma$ is anisotropic over $F$, so

$$
\overline G_\gamma(F)\backslash\overline G_\gamma(\mathbf A)
\tag{9.2}
$$

is compact and has finite volume.  This compactness is the torus analogue of the compactness of
the norm-one idele class group: after quotienting scalars, the remaining torus is a norm-one
torus up to a finite isogeny.

Choose Haar measure $dg_\gamma$ on $\overline G_\gamma(\mathbf A)$ and the complementary quotient
measure on $\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A)$, where
$\overline G=G/Z$.  Define

$$
a(\gamma)=\operatorname{vol}\big(
\overline G_\gamma(F)\backslash\overline G_\gamma(\mathbf A)
\big).
\tag{9.3}
$$

Rescaling $dg_\gamma$ rescales $a(\gamma)$ and the quotient orbital measure inversely, so their
product below is independent of that auxiliary scalar.

### 9.3 Elliptic orbital distributions

For elliptic $\gamma$ define

$$
O_\gamma(f)=
\int_{\overline G_\gamma(\mathbf A)\backslash\overline G(\mathbf A)}
f(g^{-1}\gamma g)\,d\dot g.
\tag{9.4}
$$

The integral is absolutely convergent.  At finite places compact support restricts the orbit to
a compact set modulo the centralizer.  At archimedean places a regular semisimple orbit map is
proper modulo its centralizer up to polynomial Jacobian factors, and Schwartz decay dominates
those factors.  A detailed uniform estimate over varying rational $\gamma$ will be proved in
Chapter 11.

For a factorizable function and compatible product measures, Fubini gives

$$
O_\gamma(f)=\prod_vO_{\gamma_v}(f_v).
\tag{9.5}
$$

Only finitely many factors differ from their normalized unramified values.  Formula (9.5) records
factorization; it does not evaluate the local factors.

### 9.4 The central term

Modulo $Z(F)$ all rational scalar matrices give one element, represented by $1$.  Its summand in
the diagonal kernel is constant:

$$
f(x^{-1}1x)=f(1).
$$

Therefore its contribution is

$$
I_{\mathrm{cent}}(f)=\operatorname{vol}([\overline G])f(1).
\tag{9.6}
$$

The finite volume and the value $f(1)$ use the normalizations of Chapter 1.  There is no sum over
rational scalars because the kernel was correctly indexed by $Z(F)\backslash G(F)$.

## 10. Truncation and parabolic cancellation

### 10.1 Compact truncations

Although $K_f(x,x)$ is absolutely integrable, the raw nonnegative majorant

$$
\sum_\gamma|f(x^{-1}\gamma x)|
\tag{10.1}
$$

need not be integrable on the whole quotient.  Cuspidal cancellation may be destroyed by the
absolute values.  Thus one may not invoke Tonelli on (10.1) and simply group the full sum by
conjugacy classes.

Let $[\overline G]_{\leq T}$ be the compact truncation defined by cusp height at most $T$, with a
smooth cutoff $\chi_T$ equal to one below $T$ and zero above $2T$.  Set

$$
I_T(f)=\int_{[\overline G]}\chi_T(x)K_f(x,x)\,dx.
\tag{10.2}
$$

On the compact support of $\chi_T$, Theorem 3.2 permits integration and rearrangement of the
rational sum.  By (7.3), dominated convergence gives

$$
\lim_{T\to\infty}I_T(f)=\operatorname{tr}R_\omega(f).
\tag{10.3}
$$

### 10.2 Stable rational lines

Every noncentral nonelliptic element stabilizes at least one rational line.  Let $\mathscr L$
be the set of $F$-lines in $F^2$.  Then $\mathscr L\simeq B(F)\backslash G(F)$.  A split regular
element fixes exactly two members of $\mathscr L$; a nontrivial unipotent element fixes exactly
one.

Consequently a sum over noncentral nonelliptic elements can be rewritten as a sum over pairs
$(\gamma,L)$ with $\gamma L=L$, with weight $1/2$ on the split regular pairs and weight $1$ on
the unipotent pairs.  Conjugating $L$ to the standard line puts $\gamma$ in $B(F)$.  This is the
rank-two replacement for the general combinatorics of parabolic subgroups.

To see that the weights introduce no hidden choice, define

$$
e(\gamma)=\#\{L\in\mathscr L:\gamma L=L\}.
$$

Then $e(\gamma)=2$ in the split regular case and $e(\gamma)=1$ in the noncentral
nonsemisimple case.  For any finitely supported function $\Phi$ on the noncentral nonelliptic
set,

$$
\sum_\gamma\Phi(\gamma)
=\sum_{L\in\mathscr L}
\sum_{\substack{\gamma L=L\\ \gamma\ \mathrm{noncentral}}}
e(\gamma)^{-1}\Phi(\gamma).
\tag{10.3a}
$$

This is double counting.  We apply it first after both geometric and cusp truncation, where the
support is finite, and only afterward remove the truncations.  No conditional infinite
rearrangement is concealed in the stable-line argument.

### 10.3 Unfolding the nonelliptic part

**Proposition 10.1.** After the stable-line regrouping of Section 10.2, the main term obtained by
replacing the truncation cutoff with its full unipotent translate is a finite linear combination
of integrals of the global parabolic transform (4.1).  Hence this main term is zero for an
admissible cuspidal test function.  The difference from the truncated contribution is supported
in the truncation boundary band.

**Proof.** We give the mechanism, including the convergence order.  For the standard line, write
an element of $B(F)$ modulo $Z(F)$ as $tn(u)$ with $t\in T(F)/Z(F)$ and $u\in N(F)$, separating
the repeated-root locus when necessary.  In the conjugacy sum, conjugation by a rational element
carrying the standard line to $L$ unfolds the sum over $B(F)\backslash G(F)$ against the
automorphic quotient.  The remaining $N(F)$ sum is paired with integration over
$N(F)\backslash N(\mathbf A)$.  For a compact truncation all sums and integrals are absolutely
convergent, so

$$
\sum_{u\in N(F)}\int_{N(F)\backslash N(\mathbf A)}
 f(x^{-1}t n(u)n(v)y)\,dv
=\int_{N(\mathbf A)}f(x^{-1}tny)\,dn.
\tag{10.4}
$$

The right side, with its modular factor, is $f_B(x,y;t)$ and is zero by Lemma 4.1.  The split
regular weight $1/2$ corrects the two choices of stable line; the unipotent weight is one.  The
central locus was removed before this regrouping, so its infinitely many stable lines cause no
overcount.  Passing from compact support to Schwartz decay is justified by cutting the
archimedean height, applying (10.4), and using arbitrary power decay to remove that cutoff.
$\square$

There is a small algebraic point in the notation $tn(u)$.  If
$t=\operatorname{diag}(a,d)$ with $a\ne d$, every element
$\begin{psmallmatrix}a&b\\0&d\end{psmallmatrix}$ is conjugate inside $N(F)$ to $t$, since

$$
n(v)^{-1}tn(v)=t n((1-d/a)v),
$$

and $1-d/a\ne0$.  The sum over $u$ is therefore the rational orbit inside the Borel.  If
$a=d$, the central element corresponds to $u=0$ and has already been removed; the remaining
$u\ne0$ form the nontrivial unipotent locus.  Thus the same unipotent unfolding covers both the
split and repeated-root cases, with exactly the weights in (10.3a).

The proposition explains why strong cuspidality is the right local condition.  It annihilates
the full two-sided transform appearing after unfolding, before any character or orbital trace is
taken.

### 10.4 Removal of the truncation

The cutoff $\chi_T$ in (10.2) prevents (10.4) from being an exact full unipotent unfolding near
the truncation boundary.  We must show that the discrepancy tends to zero.

**Lemma 10.2.** Let $I_T^{\mathrm{par}}(f)$ be the stable-line-regrouped noncentral nonelliptic
part of (10.2).  There are $C>0$ and $\eta>0$ such that

$$
|I_T^{\mathrm{par}}(f)|\leq C T^{-\eta}.
\tag{10.5}
$$

**Proof.** Insert and subtract the full unipotent integral (10.4), which is zero.  The difference
is supported where conjugation by $n(v)$ moves a point across the band $T\leq\operatorname{ht}
\leq2T$.  Reduction theory expresses that band in Iwasawa coordinates with measure
$dH/H^2$ times compact factors.  If $v$ is small relative to the shrinking unipotent
cross-section, the cutoff difference is bounded by a derivative of $\chi_T$ times a power of
$|v|/H$; if $v$ is large, Schwartz decay of $f(x^{-1}tn(v)y)$ gives an arbitrary negative power
of $|v|$.  Split the $v$-integral at $|v|=H^{1/2}$.  Use the first estimate in the
small range and the second in the large range.  Since all invariant derivatives of $f$ are
Schwartz, the resulting integrand is $O(H^{-2-\eta})$ for some $\eta>0$.  Integration for $H\geq T$
gives (10.5).  The finitely many cusp charts and finite-place supports only change $C$.
$\square$

We spell out the estimate behind the phrase “repeatedly use.”  In a cusp chart write
$x=n(q)a(H)k$, where $q$ lies in a fixed compact fundamental set,
$|\alpha(a(H))|_{\mathbf A}=H$, and the measure is bounded by a compact density times
$dH/H^2$.  Choose the cutoff as $\chi_T(x)=\chi(H/T)$.  Conjugation gives

$$
a(H)^{-1}n(v)a(H)=n(\alpha(a(H))^{-1}v).
\tag{10.5a}
$$

For $|v|\leq H^{1/2}$, the mean-value theorem and the uniform derivative bounds on $\chi$ give

$$
|\chi_T(n(v)x)-\chi_T(x)|
\leq C H^{-1}(1+|v|).
\tag{10.5b}
$$

The first moment of the relevant unipotent translate of $f$ is finite uniformly up to fixed
polynomial factors in the torus variable.  Thus the small range gains one negative root-height
power.  For
$|v|>H^{1/2}$, (2.1) gives

$$
|Df(x^{-1}tn(v)y)|\leq C_N(1+|v|)^{-N}
\tag{10.5c}
$$

times fixed polynomial factors in $H$ and $t$.  Taking $N$ large makes the tail gain at least the
same negative root-height power.  Finite support bounds the nonarchimedean $t$-denominators, while summation over the
remaining rational $t$ is controlled by the lattice-shell estimate of Lemma 3.1.  Finally,

$$
\int_T^\infty H^{-\eta}\frac{dH}{H^2}\leq C_\eta T^{-1-\eta}.
$$

This proves (10.5) and shows explicitly where the rank-one cusp density and
Schwartz derivatives enter.

Combining Proposition 10.1 and Lemma 10.2 shows that no split or unipotent distribution survives
the limit in (10.3).  This is a genuine cancellation statement, not an assertion that every
summand in (10.1) vanishes.

## 11. Absolute convergence of the elliptic expansion

### 11.1 Arithmetic height of a projective conjugacy class

For a noncentral projective element define the invariant

$$
j(\gamma)=\frac{\operatorname{tr}(\gamma)^2}{\det(\gamma)}.
\tag{11.1}
$$

It is unchanged by scalar multiplication and conjugacy.  Together with the isomorphism class of
the quadratic algebra $F[\gamma]$, it controls a regular projective conjugacy class up to a
finite ambiguity.  Choose a multiplicative Weil height $H_j(\gamma)$ of $j(\gamma)$ and put

$$
H_{\mathrm{ell}}(\gamma)=H_j(\gamma)\,
N_{F/\mathbf Q}(\mathfrak d_{F[\gamma]/F}).
\tag{11.2}
$$

Any other standard projective height is polynomially comparable on the finite-support set
defined by $f$.  Precise exponents are immaterial; the test function decays faster than every
power.

The quadratic algebra is genuinely additional rational information.  For example, projective
elements with trace zero all have $j=0$, while the square class of their determinant can produce
different quadratic centralizers.  This is why (11.2) includes the relative discriminant rather
than trying to count classes by $j$ alone.  Finite orbital support bounds the permitted local
square classes outside finitely many places, and the discriminant height measures the remaining
variation.

### 11.2 Coarse counting and torus-volume bounds

**Lemma 11.1.** There are constants $C,A$ depending on $F$ and the finite support of $f$ such
that

$$
\#\{[\gamma]_{\mathrm{ell}}:H_{\mathrm{ell}}(\gamma)\leq X,
\ O_{\gamma_f}(f_f)\ne0\}\leq CX^A.
\tag{11.3}
$$

Moreover, for some $B$,

$$
a(\gamma)\leq C H_{\mathrm{ell}}(\gamma)^B.
\tag{11.4}
$$

**Proof.** Finite orbital support bounds denominators of the coefficients of the characteristic
polynomial in fixed fractional ideals.  Bounded height then places those coefficients in a box
in a fixed Minkowski lattice.  Lattice-point counting gives a polynomial bound.  For each
polynomial there are only finitely many rational conjugacy classes: a regular semisimple
$2\times2$ matrix is determined up to rational conjugacy by its characteristic polynomial.
This proves (11.3).

For (11.4), identify the centralizer quotient, up to finite kernel and cokernel, with the adelic
quotient of the norm-one torus of the quadratic extension $E=F[\gamma]$.  A fundamental region
is built from ideal classes and a logarithmic unit lattice.  Minkowski's theorem supplies an
integral ideal of norm at most a fixed power of $N(\mathfrak d_{E/F})$ in every ideal class.
Counting lattice points in the corresponding bounded Minkowski boxes gives a polynomial bound
for the number of such classes.  A basis of the logarithmic unit lattice may be chosen with
lengths bounded by a fixed power of the discriminant by applying successive minima to the
logarithmic embedding; its covolume, the regulator, obeys the same coarse bound.  The remaining
roots of unity and local component groups have order bounded by a fixed power of $[E:\mathbf Q]$
and the discriminant.  Multiplying these factors proves (11.4).  No class-number formula is
needed.  $\square$

These deliberately rough estimates are enough for convergence and avoid importing any analytic
information about quadratic $L$-values.

### 11.3 Decay of orbital integrals

**Lemma 11.2.** For every $M>0$ there is a Schwartz seminorm $\nu_M$ such that

$$
|O_\gamma(f)|\leq \nu_M(f)H_{\mathrm{ell}}(\gamma)^{-M}
\tag{11.5}
$$

for every elliptic class meeting the fixed finite support.

**Proof.** At finite places, meeting the compact support bounds the denominators and contributes
at most a fixed polynomial in the local discriminant.  This follows by covering the compact
support with finitely many cosets on which the orbit map has constant Jacobian valuation; the
number and inverse Jacobians of the relevant cosets are polynomial in the discriminant
valuation.

At the distinguished real place, a nonzero orbital integral of a cuspidal Schwartz function
requires the class to be elliptic there; locally split regular classes have zero orbital integral
by the parabolic-transform condition.  On the elliptic set, conjugate $\gamma$ to a rotation
times a scalar.  The quotient by its compact-mod-center centralizer has polar coordinates whose
Jacobian grows at most exponentially in the polar distance, while the Harish--Chandra Schwartz
estimates give arbitrary exponential decay in that distance and arbitrary polynomial decay in
the semisimple parameter.  At every other archimedean place, the same orbit-coordinate argument
gives a fixed polynomial Jacobian absorbed by arbitrary Schwartz decay.

The product formula relates the archimedean size of the characteristic coefficients to their
finite denominators and to the discriminant norm.  Hence, after absorbing the fixed polynomial
losses just described, the product of local estimates is smaller than every negative power of
(11.2).  The required constants use only finitely many local Schwartz seminorms, yielding
(11.5).  $\square$

We justify the orbit-coordinate estimate used in the proof.  Over a local field $k$, let $t$ be
regular semisimple and let $\mathfrak g=\mathfrak t\oplus\mathfrak q$ be a vector-space
decomposition.  In exponential or algebraic coordinates near the identity, the derivative of

$$
\mathfrak q\longrightarrow G_t\backslash G\cdot t,
\qquad X\longmapsto \exp(-X)t\exp(X),
$$

is $X\mapsto[t,X]$.  On the two root directions its determinant is, up to a unit and a scalar
power removed by the center,

$$
D(t)=(\lambda_1/\lambda_2-1)(\lambda_2/\lambda_1-1).
\tag{11.5a}
$$

The inverse-function theorem therefore gives coordinate charts whose Jacobians and inverse
Jacobians are bounded by fixed powers of $|D(t)|^{-1}$.  A compact set is covered by finitely
many such charts after subdivision according to the valuation of $D(t)$ at a nonarchimedean
place.  The number of subdivisions up to valuation $m$ is polynomial in $q^m$, which proves the
finite-place polynomial loss asserted above.

At an archimedean place use Cartan coordinates $g=k_1a(s)k_2$.  Haar measure is bounded by
$Ce^{cs}ds\,dk_1\,dk_2$.  Conjugating a fixed regular element by $a(s)$ makes a matrix norm grow
at least $c_t e^{c's}$ off its centralizer.  The constant $c_t^{-1}$ is bounded by a power of
$|D(t)|^{-1}$ by (11.5a).  A Schwartz seminorm of order $N$ then bounds the orbital integrand by

$$
C_N|D(t)|^{-C_N}e^{-(N-c)s}(1+\|t\|)^{-N}.
\tag{11.5b}
$$

Taking $N$ large makes the $s$-integral converge and leaves only polynomial powers of the orbit
discriminant.  At the cuspidal real place, locally split $t$ has orbital integral zero: Iwasawa
integration writes it as an integral of the parabolic transform (2.2).  For elliptic $t$, its
centralizer is compact modulo center and the same estimate is easier.  Multiplying the local
bounds, using the product formula to exchange inverse local discriminants for positive powers at
the remaining places, and then increasing $N$ proves (11.5) with any prescribed $M$.

This derivation also covers classes approaching the singular set $D(t)=0$.  Their local orbital
integrals may have polynomial or logarithmic growth, but a logarithm is bounded by every small
negative power and is absorbed by the discriminant factors in (11.5b).  No uniform regularity at
the singular orbit has been assumed.

The lemma is a convergence estimate, not an explicit orbital-integral formula.  It is stable
under invariant differentiation and under finite sums of tensors.

### 11.4 Summability

**Theorem 11.3.** The elliptic geometric series

$$
\sum_{[\gamma]_{\mathrm{ell}}}a(\gamma)O_\gamma(f)
\tag{11.6}
$$

converges absolutely.

**Proof.** Divide the classes into dyadic shells
$2^k\leq H_{\mathrm{ell}}(\gamma)<2^{k+1}$.  Lemma 11.1 bounds the number of classes by
$C2^{Ak}$ and the volume by $C2^{Bk}$.  Lemma 11.2 bounds each orbital integral by
$C_M2^{-Mk}$.  Choose $M>A+B+1$.  The absolute contribution of the $k$-th shell is at most
$C2^{-k(M-A-B)}$, and the resulting geometric series converges.  $\square$

Absolute convergence here applies after rational elements have been grouped into elliptic
conjugacy classes.  It does not assert the generally false integrability of the raw majorant
(10.1).

## 12. Equality of the two expansions

### 12.1 The geometric expansion

Define

$$
I_{\mathrm{geom}}(f)=
\operatorname{vol}([\overline G])f(1)
+\sum_{[\gamma]_{\mathrm{ell}}}a(\gamma)O_\gamma(f).
\tag{12.1}
$$

Theorem 11.3 makes this an ordinary absolutely convergent sum.  It is continuous in the
admissible Schwartz topology: the proof of Lemma 11.2 bounds all terms by one summable majorant
formed from finitely many Schwartz seminorms.

### 12.2 The simple cuspidal trace formula

**Theorem 12.1 (simple trace formula for a cuspidal archimedean factor).** Let $F$ be a number
field with a real place $v_0$, let $\omega$ be a unitary idele class character, and let $f$ be a
finite sum of factorizable admissible test functions of inverse central character
$\omega^{-1}$.  Assume every tensor has a strongly cuspidal factor at $v_0$ and is finite under
the left and right maximal compact actions.  Then $R_\omega(f)$ is trace class on $L^2_\omega$,
annihilates the noncuspidal subspace, and

$$
\boxed{
\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
m(\pi)\operatorname{tr}\pi(f)
=\operatorname{vol}([\overline G])f(1)
+\sum_{[\gamma]_{\mathrm{ell}}}a(\gamma)O_\gamma(f).}
\tag{12.2}
$$

The spectral series and the elliptic series converge absolutely.  The common value also equals
$\int_{[\overline G]}K_f(x,x)\,dx$, whose absolute value is integrable.

**Proof.** Theorem 3.2 constructs the smooth automorphic kernel.  Chapter 4 proves cuspidal range
and annihilation of every continuous and residual term.  Chapters 5 and 6 prove trace class.
Theorem 7.1 identifies its trace with the absolutely convergent diagonal integral, and Theorem
8.1 identifies that trace with the absolutely convergent cuspidal spectral series.

For the geometric side, insert a compact truncation as in (10.2).  On the truncation, group the
rational sum by the four cases of Section 9.1.  The central part tends to (9.6).  The
noncentral nonelliptic part tends to zero by Proposition 10.1 and Lemma 10.2.  Each elliptic
class unfolds by quotient integration:

$$
\int_{\overline G_\gamma(F)\backslash\overline G(\mathbf A)}
f(x^{-1}\gamma x)\,dx
=a(\gamma)O_\gamma(f).
\tag{12.3}
$$

Theorem 11.3 permits passage to the limit through the elliptic class sum.  Thus the diagonal
trace equals (12.1).  Combining with the spectral identity proves (12.2).  Linearity handles a
finite sum of tensors.  $\square$

### 12.3 Independence of auxiliary truncations

The final formula contains no truncation parameter.  Suppose $\chi_T$ and $\chi'_T$ are two
families of smooth cutoffs with the standard support and derivative bounds.  Their difference is
supported in a cusp band whose lower height tends to infinity.  Proposition 4.3 makes the
integral of $|K_f(x,x)|$ over that band tend to zero.  Lemma 10.2 does the same for the
parabolic regrouping, and Theorem 11.3 supplies a cutoff-independent majorant for the elliptic
terms.  Hence both procedures have the same limit.

The identity is likewise independent of the chosen scalar normalization on a centralizer:
$a(\gamma)$ and $O_\gamma(f)$ change inversely.  It does depend, as it must, on the original
Haar measure on $G(\mathbf A)$ and on the induced quotient measure used on both sides.

### 12.4 Factorization without evaluation

For a tensor $f=\otimes_vf_v$, equation (9.5) rewrites the geometric term as

$$
a(\gamma)\prod_vO_{\gamma_v}(f_v).
\tag{12.4}
$$

On the spectral side, restricted tensor product theory gives

$$
\pi(f)=\bigotimes_v\pi_v(f_v)
\tag{12.5}
$$

on the finite-dimensional range selected by the level and types.  Formula (12.2) is therefore
already compatible with later local comparison.  What is not yet supplied is a numerical or
character-theoretic evaluation of the factors in (12.4) or (12.5).  Their existence,
factorization, measures, and absolute summability have all been settled here.

## 13. Examples, boundaries, and failure modes

### 13.1 A weight-$k$ kernel over the rationals

Take $F=\mathbf Q$, $v_0=\infty$, and let $f_\infty$ be a compact-finite pseudo-coefficient of a
discrete series $D_k$ of lowest weight $k\geq2$.  Choose at every finite prime a compactly
supported Hecke function, spherical almost everywhere.  The resulting kernel

$$
K_f(x,y)=\sum_{\gamma\in\mathbf Q^\times\backslash
\mathrm{GL}_2(\mathbf Q)}f(x^{-1}\gamma y)
$$

is smooth, cuspidal in both variables, and rapidly decreasing in the modular cusp.  Its trace is
a sum over cuspidal automorphic representations whose real component is detected by $D_k$.

Geometrically, the identity class contributes the quotient volume times $f(1)$.  A rational
matrix with irreducible characteristic polynomial contributes through the torus of a quadratic
field.  Split matrices and nontrivial unipotent matrices contribute nothing after parabolic
regrouping.  Thus the familiar “identity plus elliptic” shape follows from the local discrete
series factor before any elliptic orbital integral is calculated.

### 13.2 Adding finite-place Hecke conditions

At a prime $p$ away from the level, replace the spherical identity by a compactly supported
spherical Hecke function.  This does not disturb strong cuspidality at infinity.  On the spectral
side it inserts the corresponding Hecke operator $\pi_p(f_p)$; on the geometric side it changes
which rational elliptic classes meet the finite support and weights them by
$O_{\gamma_p}(f_p)$.  All convergence proofs remain uniform on a fixed finite-dimensional
subspace of the spherical Hecke algebra.

At ramified primes one may instead impose compact-open projectors or matrix coefficients.  The
left-right invariance subgroups change, hence so does the finite level $\mathcal H_0$, but the
trace-class proof is unchanged.  This flexibility is why the cuspidal factor is placed at one
archimedean place: the finite factors remain free for level and comparison conditions.

### 13.3 What fails without a cuspidal factor

If the archimedean factor is a general Schwartz function, the periodized kernel may still
converge locally and define a bounded smoothing operator.  Three later conclusions fail.

First, the constant term of the kernel need not vanish.  Constant-mode wave packets can move
arbitrarily far into the cusp with bounded energy, so the relevant elliptic operator does not
have compact resolvent on that channel.  Second, the operator acts nontrivially on Eisenstein
families and their residues; a purely cuspidal spectral sum is incomplete.  Third, the raw
diagonal develops parabolic contributions whose integrals require truncation and compensation.

Total integral zero does not repair these failures.  It kills at most one one-dimensional
character.  The averaged local condition $f^B=0$ kills induced traces but need not kill induced
operators, so it is insufficient for the two-variable kernel proof.  Strong cuspidality (2.2)
is exactly the hypothesis used at every cancellation step.

### 13.4 What this formula does not yet compute

The theorem isolates, but does not evaluate, two families of terms.  On the spectral side one
must still compute $\operatorname{tr}\pi(f)$ with multiplicities and compatible local
normalizations.  On the geometric side one must classify rational elliptic classes more
explicitly and calculate their local orbital integrals.  Comparison with an inner form further
requires matching functions and local transfer identities.

Those are subsequent tasks.  The present theorem ensures that their answers may be substituted
into genuine absolutely convergent expansions.  It also establishes the measure framework that
prevents a later local scalar from being hidden in a global quotient volume.

## 14. Final synthesis

### 14.1 The proof ledger

Every arrow in the construction has a distinct source:

$$
\begin{aligned}
&\text{projective rational-point counting}+\text{Schwartz decay}
&&\Longrightarrow \text{smooth absolute periodization},\\
&\text{one strongly cuspidal real factor}+\text{tensor factorization}
&&\Longrightarrow \text{zero global parabolic transform},\\
&\text{rank-one Eisenstein classification}+\text{the same local zero}
&&\Longrightarrow \text{annihilation of continuous and residual spectrum},\\
&\text{cuspidal Sobolev compactness}+\text{elliptic smoothing}
&&\Longrightarrow \text{trace class},\\
&\text{two Hilbert--Schmidt half-powers}+\text{kernel uniqueness}
&&\Longrightarrow \text{the diagonal trace formula},\\
&\text{discrete finite-multiplicity cuspidal spectrum}+\text{trace class}
&&\Longrightarrow \text{absolute spectral expansion},\\
&\text{rank-two stable-line regrouping}+\text{parabolic cancellation}
&&\Longrightarrow \text{central and elliptic terms only},\\
&\text{arithmetic height counting}+\text{Schwartz orbital decay}
&&\Longrightarrow \text{absolute elliptic expansion}.
\end{aligned}
\tag{14.1}
$$

No arrow is redundant.  Local convergence does not imply diagonal integrability; discreteness
does not imply trace class; trace class does not by itself justify a chosen pointwise diagonal;
and cuspidal spectral annihilation does not by itself prove geometric orbital convergence.

### 14.2 The reusable kernel theorem

The argument may be summarized in a form useful for later comparison.

**Theorem 14.1 (cuspidal kernel package).** Under the hypotheses of Theorem 12.1, the Poincare
series $K_f$ is the unique smooth kernel of $R_\omega(f)$ and is rapidly decreasing with all
derivatives in both variables.  The operator is trace class, has range and adjoint range in the
cuspidal space, and has three equal descriptions:

$$
\begin{aligned}
\operatorname{tr}R_\omega(f)
&=\int_{[\overline G]}K_f(x,x)\,dx\\
&=\sum_\pi m(\pi)\operatorname{tr}\pi(f)\\
&=\operatorname{vol}([\overline G])f(1)
+\sum_{[\gamma]_{\mathrm{ell}}}a(\gamma)O_\gamma(f).
\end{aligned}
\tag{14.2}
$$

The diagonal integral and both displayed series are absolutely convergent in their stated
groupings.  All measures arise from the fixed local Haar measures by quotient integration, and
both spectral and orbital terms factor for tensor-product tests.

**Proof.** This is the conjunction of Theorems 3.2, 7.1, 8.1, 11.3, and 12.1, together with the
two-variable decay of Proposition 4.3.  $\square$

### 14.3 Conclusion

The trace formula in rank two becomes an ordinary trace identity when one archimedean factor
removes the single proper parabolic channel.  That local cancellation has three global effects:
the kernel is cuspidal in both variables, the convolution operator annihilates every Eisenstein
wave packet and residue, and the nonelliptic rational conjugacy terms vanish after stable-line
unfolding.

The remaining analysis is exact rather than formal.  Projective counting constructs the kernel;
cuspidal Sobolev theory confines it; elliptic half-powers make it trace class; a
Hilbert--Schmidt contraction legitimizes its diagonal; and arithmetic height makes the elliptic
orbital sum absolutely convergent.  The spectral and geometric expansions are therefore not
competing definitions.  They are two absolutely convergent evaluations of the same canonical
operator trace.

This completes the analytic kernel foundation for the rank-two simple trace formula.  The
cuspidal representations, central term, and elliptic orbital terms now stand in one measure-
compatible identity, ready for their separate spectral and local geometric computations.
