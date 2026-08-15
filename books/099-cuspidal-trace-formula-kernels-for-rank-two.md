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
- [9. Equality of the spectral and geometric kernel expansions](#9-equality-of-the-spectral-and-geometric-kernel-expansions)
  - [9.1 Compact truncations of the geometric kernel](#91-compact-truncations-of-the-geometric-kernel)
  - [9.2 The simple cuspidal kernel identity](#92-the-simple-cuspidal-kernel-identity)
  - [9.3 Independence of auxiliary truncations](#93-independence-of-auxiliary-truncations)
  - [9.4 The boundary with the orbital geometric side](#94-the-boundary-with-the-orbital-geometric-side)
- [10. Examples, boundaries, and failure modes](#10-examples-boundaries-and-failure-modes)
  - [10.1 A fixed-weight kernel over the rationals](#101-a-fixed-weight-kernel-over-the-rationals)
  - [10.2 Adding finite-place Hecke conditions](#102-adding-finite-place-hecke-conditions)
  - [10.3 What fails without a cuspidal factor](#103-what-fails-without-a-cuspidal-factor)
  - [10.4 What this formula does not yet compute](#104-what-this-formula-does-not-yet-compute)
- [11. Final synthesis](#11-final-synthesis)
  - [11.1 The proof ledger](#111-the-proof-ledger)
  - [11.2 The reusable kernel theorem](#112-the-reusable-kernel-theorem)
  - [11.3 Conclusion](#113-conclusion)

## Introduction

A trace formula begins with a deceptively finite-dimensional picture. If a matrix $A$ has
kernel $(A_{ij})$, then its trace is at once the sum of its eigenvalues and the sum of its
diagonal entries. On an automorphic quotient both expressions become infinite. The
eigenvectors belong to infinitely many automorphic representations, the geometric kernel is a
sum over rational matrices, and the quotient on which its diagonal is integrated is noncompact.
None of the three infinite operations is automatically legitimate.

For $\mathrm{GL}_2$ there is a particularly clean way to remove the obstruction. Choose the
archimedean test function to be cuspidal at one real place. Its parabolic averages vanish. The
resulting global convolution operator kills the Eisenstein and residual subspaces, and its range
lies in the discrete cuspidal space. Cuspidal decay prevents mass from escaping into the unique
rank-one cusp. Elliptic smoothing then makes the operator trace class, so its spectral trace and
its diagonal trace are ordinary absolutely convergent quantities. The result is the analytic
simple trace formula: the absolutely convergent cuspidal spectral trace equals the integral of
the canonical geometric kernel. Regrouping that kernel by rational conjugacy is a further
geometric problem, deliberately left to the later volume devoted to the geometric side.

The word _simple_ in “simple trace formula” refers to this removal of the parabolic channel. It
does not mean that convergence may be ignored. In fact, the purpose of this book is to prove
every interchange that turns the formal identity

$$
\sum_\pi m(\pi)\operatorname{tr}\pi(f)
\stackrel{?}{=}
\int_{[\overline G]}\sum_\gamma f(x^{-1}\gamma x)\,dx
$$

into a theorem. The proof is organized so that each infinity has a separate control:
rational-point counting controls periodization, constant-term cancellation controls the cusp,
and Sobolev smoothing controls singular values and the canonical diagonal.

The preceding books supply four exact foundations. The Hilbert-space theory supplies
Hilbert--Schmidt factorizations, trace ideals, and safe diagonal formulas. The Sobolev theory
supplies elliptic estimates, polynomial spectral counting, and rapidly decreasing kernels on
cuspidal spaces. Adelic reduction theory supplies the finite-volume quotient, its measures,
the closed cuspidal subspace, and its discrete finite-multiplicity decomposition. The rank-one
constant-term theory supplies the decisive theorem that one strongly cuspidal local factor
annihilates all Eisenstein wave packets and all residues. We recall each interface when it is
used and prove the additional kernel and geometric arguments here.

Detailed evaluation of cuspidal characters is not part of the present task. Neither is the
classification and convergence of rational conjugacy-class contributions: those are the
subject of the later geometric-side volume and cannot be imported backward here. The goal is
prior and indispensable: construct the canonical automorphic kernel, prove that its diagonal is
absolutely integrable, and identify its integral with an absolutely convergent cuspidal spectral
sum.

## 1. The simple trace-formula problem

### 1.1 Why an ordinary trace can exist

The full automorphic $L^2$ space is not a discrete sum. Its constant terms propagate down the
cusp and generate continuous Eisenstein families. Consequently a general convolution operator
does not have an ordinary trace on the full space; one normally truncates and regularizes. A
cuspidal local factor changes the problem rather than regularizing it. It makes the convolution
operator zero on the entire noncuspidal channel. The only remaining Hilbert space is the closed
cuspidal subspace, where fixed-level, fixed-type elliptic operators have compact resolvent.

There are still two tasks. First, an arbitrary bounded operator on a discrete Hilbert sum need
not be trace class. Smooth convolution must be combined with a polynomial eigenvalue count.
Second, the Poincare series defining the kernel must be shown to represent that trace-class
operator with an integrable canonical diagonal. These tasks are analytic and cannot be replaced
by the representation-theoretic statement that the spectrum is discrete.

The eventual identity will have the form

$$
\operatorname{tr}R_\omega(f)
=\sum_{\pi}m(\pi)\operatorname{tr}\pi(f)
=\int_{[\overline G]}\sum_{\gamma\in Z(F)\backslash G(F)}
f(x^{-1}\gamma x)\,dx.
\tag{1.1}
$$

The middle expression is the spectral expansion and the right side is the geometric kernel
expansion. The spectral series and the diagonal integral will be absolutely convergent. The
rational sum converges absolutely and locally uniformly before integration, but we do not claim
that the sum of its absolute values is globally integrable; cuspidal cancellation can be lost
under absolute values.

### 1.2 Standing global notation

Let $F$ be a number field with at least one real place, and let $\mathbf A=\mathbf A_F$. Put

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

It has finite volume. Fix a unitary idele class character

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times.
$$

The Hilbert space $L^2_\omega$ consists of functions on $G(F)\backslash G(\mathbf A)$ satisfying

$$
\phi(zg)=\omega(z)\phi(g)
\tag{1.3}
$$

and square-integrable on (1.2). Its closed cuspidal subspace is denoted
$L^2_{\mathrm{cusp},\omega}$. Cuspidality means

$$
\phi_N(g)=\int_{F\backslash\mathbf A}\phi(n(u)g)\,d\bar u=0
\tag{1.4}
$$

for every $g$, initially for smooth vectors and then in the closed $L^2$ sense. Since every
proper $F$-parabolic of $G$ is rationally conjugate to $B$, (1.4) at all right translates is the
full cuspidality condition.

Choose a real place $v_0$. It is at this place that the test function will be strongly
cuspidal. This hypothesis is not an artificial restriction: $\mathrm{GL}_2(\mathbf C)$ has no
discrete series modulo center, whereas a real place supplies discrete-series coefficients and
pseudo-coefficients with the required parabolic cancellation.

### 1.3 The measure and central-character ledger

At every finite place normalize $|\varpi_v|_v=q_v^{-1}$, and at a complex place use the square
of the ordinary complex modulus. Give maximal compact subgroups probability Haar measure.
Use the Iwasawa Haar measures and quotient measures fixed by adelic reduction theory. On
$F\backslash\mathbf A$, $d\bar u$ is probability measure.

There are two compatible descriptions of this last measure. Integer-ring measure at finite
places and ordinary archimedean measure give additive covolume
$2^{-r_2}|d_F|^{1/2}$; dividing by it gives $d\bar u$. Self-dual local measures for the standard
global additive character have product covolume one and induce the same probability quotient
measure. Thus constant terms and factorizable local unipotent integrals differ by no hidden
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

descends separately to $Z(\mathbf A)\backslash G(\mathbf A)$, their product does. We define

$$
(R_\omega(f)\phi)(x)
=\int_{Z(\mathbf A)\backslash G(\mathbf A)}f(g)\phi(xg)\,d\bar g.
\tag{1.6}
$$

Every quotient measure below is obtained from these Haar measures by iterated quotient
integration. This convention makes the central quotient, convolution operator, and kernel
integral use one compatible normalization.

### 1.4 Scope of the theorem

We shall prove (1.1) for factorizable kernel-admissible Schwartz test functions that are finite
under the left and right maximal compact actions, compactly supported modulo the center at
finite places, and strongly cuspidal at $v_0$. Kernel admissibility is the explicit fixed-power
decay condition in Section 2.1. Finite sums of such tensors are allowed by linearity.

The theorem includes:

1. absolute locally uniform convergence of the automorphic kernel and all its derivatives;
2. operator-level annihilation of the continuous and residual subspaces;
3. trace-classness on the whole fixed-central-character $L^2$ space;
4. an absolutely integrable canonical diagonal;
5. an absolutely convergent cuspidal spectral expansion;
6. equality of the spectral and geometric kernel expansions without regularization.

It does not evaluate $\operatorname{tr}\pi(f)$, classify rational conjugacy classes, or unfold
the diagonal into orbital integrals. Keeping the kernel theorem separate prevents a circular
argument: the later spectral and geometric volumes may use this trace identity only after its
analytic justification has been completed.

For later reference, here is the precise dependency contract. From Book 88 we use the
Hilbert--Schmidt kernel theorem, the characterization of trace class as a product of two
Hilbert--Schmidt operators, cyclicity of trace, and the two-kernel contraction formula. From
Book 89 we use Proposition 9.1 and Theorem 11.1: on fixed finite level and compact type the
cuspidal measuring operator has a polynomial counting function, its high inverse powers are
trace class, and their kernels are smooth and rapidly decreasing. From Book 90 we use
Theorem 9.1, Theorem 10.1, and Theorem 12.1: the cuspidal subspace is closed, its Sobolev form
domain embeds compactly, and it has the discrete finite-multiplicity decomposition recalled in
Chapter 8 below. From Book 91 we use Theorem 13.1, whose test-function hypothesis is exactly
(2.2) at one place and whose conclusion is operator-level annihilation of induced families,
wave packets, and residues. We do not use the weaker trace-only Corollary 13.2. Thus every
imported conclusion is applied with the same fixed central character, finite level, finite
archimedean type, and Haar measures with which it was proved.

## 2. The test-function class

### 2.1 Local central-character Schwartz spaces

Let $v$ be a place of $F$. Write $G_v=G(F_v)$ and $Z_v=Z(F_v)$. At a finite place define
$\mathcal H(G_v,\omega_v^{-1})$ to be the smooth, locally constant functions satisfying (1.5)
whose support has compact image in $Z_v\backslash G_v$. At an archimedean place let
$\mathcal C(G_v,\omega_v^{-1})$ be the Harish--Chandra Schwartz space modulo $Z_v$, again with
central transformation (1.5). For the pointwise Poincare series we use a smaller
**kernel-admissible** subspace. Choose proper symmetric submultiplicative algebraic heights
$\|\cdot\|_v\geq1$ on $Z_v\backslash G_v$. Algebraic-height balls have polynomial Haar
volume, and the rational-point lemma below has a polynomial exponent depending only on $F$ and
these heights; finite-adelic support changes its constant, not its exponent. Choose $A_F$ at
least as large as both exponents and fix $Q>A_F+1$. Kernel admissibility means that, for every
left-right invariant differential operator $D$,

$$
|Df_v(g)|\leq C_D\|g\|_v^{-Q}.
\tag{2.1}
$$

Replacing the heights by equivalent ones only changes the admissible threshold. Compactly
supported functions modulo $Z_v$ are kernel-admissible. This extra condition must not be
confused with the defining Harish--Chandra Schwartz estimates: a Harish--Chandra Schwartz
function need not decrease faster than every algebraic power, and only one sufficiently large
fixed power is required here. The volume choice in $A_F$ also makes (2.1), and every derivative
version of it, integrable modulo the center. We additionally require finite left and right
$K_v$-type. This
makes the eventual global operator land in finitely many compact types; it is not needed merely
to define the local integral.

At almost every finite place, $\omega_v$ is unramified and the distinguished function is the
normalized central-character extension of the characteristic function of $K_v$. Its precise
scalar is chosen so that it is the identity on the unramified $K_v$-fixed line. Restricted
products formed with these distinguished functions are well defined.

### 2.2 Strong cuspidality

Ordinary vanishing of the total integral removes at most the trivial representation. The
parabolic channel contains every principal series, so the cancellation must retain both left
and right variables.

**Definition 2.1.** A local test function $f_v$ is **strongly cuspidal** if

$$
\int_{N_v}f_v(x^{-1}tny)\,dn=0
\tag{2.2}
$$

for every $x,y\in G_v$ and $t\in T_v$. At an archimedean place absolute convergence is part of
the definition.

The condition is stable under left and right translation. It is also stable under the adjoint

$$
f_v^*(g)=\overline{f_v(g^{-1})}.
\tag{2.3}
$$

Indeed, invert $x^{-1}tny$, use $n^{-1}\in N_v$, and conjugate the unipotent variable by the
torus. Haar measure changes by the modular character, a harmless nonzero scalar, and the
resulting integral is another instance of (2.2).

The representation-theoretic meaning is exact.

**Proposition 2.2.** If $f_v$ is strongly cuspidal, then every unitary representation smoothly
induced from $B_v$ satisfies

$$
I_v(\chi_v,s)(f_v)=0.
\tag{2.4}
$$

**Proof.** On the unitary axis, the compact-picture kernel between compact-picture points $x$
and $y$ is

$$
\int_{Z_v\backslash T_v}\chi_v(t)|\alpha(t)|_v^{s}\delta_B(t)^{1/2}
 \left(\int_{N_v}f_v(x^{-1}tny)\,dn\right)dt.
$$

The central quotient is required for the integrand to descend and prevents an infinite central
factor. Absolute convergence holds for the honest tempered action, and the inner integral is
zero. This proves (2.4) for unitary induction. If $v$ is nonarchimedean and $f_v$ is compactly
supported modulo the center, the compact-picture matrix entries are Laurent transforms of
compactly supported data, so the zero extends meromorphically to every parameter. No such
off-axis assertion is made for a general archimedean Schwartz coefficient: at a nonunitary
reducibility point formal continuation need not agree with honest convolution. $\square$

### 2.3 Cuspidal factors at a real place

At $v_0$, the local constant-term theory supplies strongly cuspidal compact-finite matrix
coefficients of discrete-series representations of $\mathrm{GL}_2(\mathbf R)$ with central
character $\omega_{v_0}^{-1}$. This supply meets the kernel condition rather than merely making
it a formal hypothesis. For lowest weight $k$, the lowest-weight coefficient in Cartan
coordinates is, up to a unitary central factor and compact phases,
$\big(\cosh(t/2)\big)^{-k}$. Invariant derivatives of a compact-finite coefficient are finite
sums of coefficients in the same representation and have the same exponential rate, up to a
polynomial in $t$. Algebraic height is comparable to $e^{c|t|}$ for a fixed $c>0$.
Consequently, choosing $k$ sufficiently large in the parity prescribed by
$\omega_{v_0}(-1)$ makes (2.1) hold for the fixed $Q$. There are arbitrarily large weights in
either parity, so admissible strongly cuspidal factors exist for every unitary real central
character. A compactly supported strongly cuspidal function modulo the center, when chosen,
is also allowed.

Strong cuspidality is the archimedean constant-term theorem established in the preceding
constant-term theory: compact-finite discrete-series coefficients are square-integrable modulo
the center, their unipotent integrals converge absolutely, and every left-right translate has
zero constant term. Kernel admissibility is an additional convergence condition here; it is
not inferred merely from membership in the Harish--Chandra Schwartz space. The high-weight
calculation above proves that the condition is nonempty but does not claim packet selection.
Constructing packet-selecting pseudo-coefficients belongs to the later spectral-side analysis
and is not smuggled in as a proof input here.

This construction explains the phrase “cuspidal archimedean factor.” We use actual
operator-level cuspidality, not merely a function whose induced characters happen to have trace
zero. The stronger condition is what permits constant terms, residues, and kernels to be
handled before taking traces.

### 2.4 Global restricted tensor products

Let

$$
f=\bigotimes_v f_v
\tag{2.5}
$$

with $f_v$ in the local space just defined, distinguished spherical factors almost everywhere,
every archimedean factor kernel-admissible, and $f_{v_0}$ strongly cuspidal. We call such an $f$
an **admissible cuspidal test function**.
A finite sum of admissible tensors will be called admissible as well, provided every tensor has
a strongly cuspidal factor at the same real place.

The global function is smooth, has rapid archimedean decay modulo the center, and has compact
finite-adelic support modulo the center. It is integrable on
$Z(\mathbf A)\backslash G(\mathbf A)$, as are all its invariant derivatives. Young's inequality
therefore makes (1.6) a bounded operator and gives

$$
\|R_\omega(Df)\|\leq\|Df\|_{L^1}.
\tag{2.6}
$$

Factorization is used only where it is legitimate. For absolutely convergent integrals,

$$
I(\chi,s)(f)=\bigotimes_v I_v(\chi_v,s)(f_v).
\tag{2.7}
$$

On the unitary axis the $v_0$ factor is zero, so the global induced operator is zero. This is
exactly the range needed for Eisenstein wave packets. Residual determinant characters are
annihilated separately by the vanishing parabolic transform, as in Book 91; we do not pass the
archimedean convolution operator through a nonunitary reducibility point.

### 2.5 Adjoint, convolution, and finite type

The adjoint of (1.6) is $R_\omega(f^*)$, with $f^*$ defined by (2.3) place by place. Unimodularity
and the substitution $g\mapsto g^{-1}$ prove

$$
\langle R_\omega(f)u,v\rangle
=\langle u,R_\omega(f^*)v\rangle.
\tag{2.8}
$$

Inversion exchanges left and right derivatives, and the heights in Section 2.1 are symmetric;
hence $f^*$ is again kernel-admissible, compact-finite, and of the required finite support.

If $f,h$ have compatible central character conventions and their convolution is defined on the
central quotient, Fubini gives

$$
R_\omega(f*h)=R_\omega(f)R_\omega(h).
\tag{2.9}
$$

For trace-classness we shall not need to factor $f$ itself as one convolution. Instead we use
elliptic half-powers. This matters because an arbitrary algebraic factorization need not place
cuspidality in both factors.

Finite left $K$-type of $f$ implies that the range of $R_\omega(f)$ lies in finitely many right
compact types; finite right $K$-type gives the corresponding statement for the adjoint. At the
finite adeles, local constancy and compact support give compact open subgroups $K_f^L,K_f^R$ such
that

$$
R_\omega(f)=P_LR_\omega(f)P_R,
\tag{2.10}
$$

where $P_L,P_R$ project to finite sums of fixed-level, fixed-archimedean-type spaces. To verify
the left equality, average $\pi(k)\pi(f)$ and use left invariance or finite left type; the right
equality follows similarly from $\pi(f)\pi(k)$.

## 3. Periodization and the automorphic kernel

### 3.1 The kernel formula

The projective rational group $Z(F)\backslash G(F)$ is the correct index set. Define

$$
K_f(x,y)=\sum_{\gamma\in Z(F)\backslash G(F)}
 f(x^{-1}\gamma y).
\tag{3.1}
$$

This expression is independent of the representative of $\gamma$: an idele class character is
trivial on $F^\times$. It has the covariance

$$
K_f(z_1x,z_2y)=\omega(z_1)\omega(z_2)^{-1}K_f(x,y),
\tag{3.2}
$$

so it is a kernel between the central-character line bundles on $[\overline G]$.

The sum is visibly finite on compact sets when every archimedean factor is compactly supported
modulo center. A discrete-series coefficient is only rapidly decreasing, so a counting
argument is required in our actual test class.

### 3.2 A projective rational-point count

Choose a proper height $H$ on $Z(\mathbf A)\backslash G(\mathbf A)$ satisfying

$$
H(ab)\leq H(a)^cH(b)^c
\tag{3.3}
$$

for a fixed $c$. One may take the product over places of the maximum of the entries and the
entries of the inverse, minimized over scalar multiplication.

**Lemma 3.1.** For compact sets $C_1,C_2$ in $G(\mathbf A)$ modulo the center, and for a fixed
compact finite-adelic set $C_f$, there are constants $A_F,C$ such that

$$
\#\{\gamma\in Z(F)\backslash G(F):
 x^{-1}\gamma y\in C_fG_\infty,\ H(x^{-1}\gamma y)\leq X\}
\leq CX^{A_F}
\tag{3.4}
$$

for $x\in C_1$, $y\in C_2$, and $X\geq1$.

**Proof.** The finite support bounds the denominators of the four matrix entries in one fixed
fractional ideal. Modulo a scalar, choose a primitive representative, meaning that the entries
generate one of finitely many ideal classes. Multiplying by one of finitely many class
representatives puts the four entries in a fixed lattice in $F_\infty^4$. The height bound puts
that lattice point in a box of side at most a fixed power of $X$. Its power depends only on
$F$ and the fixed height, while the lattice depends on $C_f$. A lattice therefore has at most
$O(X^{A_F})$ points in such a box. The determinant-zero locus is discarded, and passing from
primitive matrices to projective classes only decreases the count. Multiplication by $x$ and
$y$ in fixed compact sets changes all bounds by a constant. Summing over the finitely many
ideal classes proves (3.4). $\square$

The exponent is intentionally coarse. Its role is only to choose the fixed admissibility
threshold $Q>A_F+1$ in Section 2.1.

### 3.3 Absolute and differentiated convergence

**Theorem 3.2.** For an admissible test function, (3.1) and every series obtained from it by
invariant differentiation in $x$ and $y$ converge absolutely and locally uniformly on
$G(\mathbf A)\times G(\mathbf A)$. Hence $K_f$ is smooth in the archimedean variables and
locally constant in the finite variables.

**Proof.** Fix compact sets for $x$ and $y$. Divide the rational elements into height shells
$2^j\leq H(x^{-1}\gamma y)<2^{j+1}$. Lemma 3.1 bounds the number in the $j$-th shell by
$C2^{A_Fj}$. The product of the local bounds (2.1) bounds a differentiated summand by
$C_D2^{-Qj}$. Since $Q>A_F+1$,

$$
\sum_{j\geq0}C2^{A_Fj}2^{-Qj}
$$

converges. The constants are uniform on the chosen compact sets. The Weierstrass criterion
gives local uniform convergence, and applying it to every derivative justifies termwise
differentiation. $\square$

Local uniform convergence is not yet a trace theorem. It says that the periodized formula is a
genuine smooth kernel; it says nothing about integrability as $x$ and $y$ enter a cusp.

### 3.4 Unfolding to the convolution operator

**Proposition 3.3.** The integral operator defined by $K_f$ is $R_\omega(f)$ on a dense subspace
of compactly supported smooth automorphic vectors, and hence on all of $L^2_\omega$.

**Proof.** Let $\phi$ be compactly supported modulo $Z(\mathbf A)G(F)$. Absolute convergence
from Theorem 3.2 and compact support permit Tonelli. Integrating (3.1) over a fundamental region
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

Set $y=xg$ and use right invariance of quotient measure. The result is (1.6). Boundedness of
$R_\omega(f)$ and density extend the equality. $\square$

### 3.5 Covariance and the adjoint kernel

The kernel of the adjoint is

$$
K_{f^*}(x,y)=\overline{K_f(y,x)}.
\tag{3.5}
$$

Indeed, invert the rational index and use (2.3). This elementary identity has an important
consequence. Every estimate proved for the first variable using $f$ has a corresponding
estimate for the second variable using $f^*$. Because strong cuspidality survives adjoint,
cuspidal decay will be available on both sides of the diagonal.

## 4. Parabolic cancellation and cuspidal range

### 4.1 Global parabolic transforms

For $x,y\in G(\mathbf A)$ and $t\in T(\mathbf A)$ define

$$
f_B(x,y;t)=\delta_B(t)^{1/2}
\int_{N(\mathbf A)}f(x^{-1}tny)\,dn.
\tag{4.1}
$$

The integral converges absolutely. At finite places this follows from compact support modulo
the center; at infinity it follows from Schwartz decay and the polynomial volume growth of
$N(F_v)$. For a tensor $f=\otimes f_v$, Fubini and the product measure give

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

for every $x,y,t$. The same holds for $f^*$.

**Proof.** The $v_0$ factor in (4.2) is the integral (2.2), multiplied by a nonzero modular
factor, and is zero. The assertion for $f^*$ follows from stability of strong cuspidality under
adjoint. $\square$

The strength of (4.3) should be noted. It is not merely the vanishing of an averaged trace; the
left and right variables remain free. Consequently it controls the range of the operator and
both variables of its kernel.

### 4.3 Vanishing of kernel constant terms

**Proposition 4.2.** For every fixed $y$, the function $x\mapsto K_f(x,y)$ is cuspidal. For every
fixed $x$, the conjugate-dual section $y\mapsto K_f(x,y)$ is cuspidal. All differentiated
constant terms vanish as well.

**Proof.** Average (3.1) over $N(F)\backslash N(\mathbf A)$. Rational elements are grouped by
$B(F)\backslash G(F)$, which parametrizes rational lines. More explicitly, after choosing a
representative $\delta$ of such a line, the elements in its fiber are represented by
$t n(a)\delta$ with $t\in Z(F)\backslash T(F)$ and $a\in F$. The sum over $a$ and the quotient
integral over $F\backslash\mathbf A$ unfold, after the harmless torus change of variable, to the
full $N(\mathbf A)$ integral in (4.1), with $\delta$ absorbed into the free right variable.
The unipotent quotient is compact. Thus Theorem 3.2 gives uniform absolute convergence while
the averaging variable runs over it, and Tonelli justifies the grouping and unfolding. Every
unfolded term is zero by (4.3), so the constant term in $x$ vanishes. Applying (3.5) and the
same argument to $f^*$ proves the assertion in $y$. Differentiation is permitted by Theorem 3.2;
differentiating the identically zero transform (2.2) in its free left and right variables shows
that the transformed derivatives are still zero. $\square$

### 4.4 Annihilation of the noncuspidal spectrum

There is a second, spectral proof of the range statement, and it supplies more information. The
rank-one constant-term theory classifies the noncuspidal closed subspace, at fixed level and
finite type, as the closure of unitary Eisenstein wave packets and one-dimensional residual
characters. Proposition 2.2 and restricted tensor factorization make $R_\omega(f)$ zero on
every unitary induced representation, so it kills every genuine $L^2$ Eisenstein wave packet.
The parabolic transform of the strongly cuspidal factor is zero; the residual calculation in
Book 91 therefore makes its scalar on every determinant-character residue zero as well. This
uses the honest archimedean action on the unitary axis and a direct one-dimensional calculation
on residues, not an invalid meromorphic continuation of archimedean convolution through a
nonunitary reducibility point.

Therefore

$$
R_\omega(f)=P_{\mathrm{cusp}}R_\omega(f)P_{\mathrm{cusp}},
\tag{4.4}
$$

where $P_{\mathrm{cusp}}$ is the orthogonal cuspidal projection. The right equality uses
invariance of the cuspidal subspace and annihilation of its orthogonal complement; applying the
same statement to $f^*$ gives the left equality.

This argument verifies the exact dependency hypotheses. The central character is unitary, the
test is factorizable and finite-level, and the local hypothesis is the strong two-sided condition,
not merely trace-level vanishing. Hence no residual contribution is left untreated.

## 5. Smoothing and finite analytic support

### 5.1 Invariant differentiation of convolution

Let $D$ be a right-invariant differential operator acting on the output variable. Moving $D$
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

where $\nu_s$ is a finite sum of $L^1$ norms of derivatives of $f$. Applying this to $f^*$ and
duality shows that $R_\omega(f)$ maps $H^{-s}$ continuously to $L^2$. To gain output
derivatives and allow a negative-order source simultaneously, pair $D R_\omega(f)u$ with a
smooth vector $v$. After moving $D$ to the test function and taking the adjoint, the resulting
operator on $v$ is again convolution by a differentiated admissible test; (5.2), now with $s$
derivatives, bounds it in $H^s$. Sobolev duality therefore gives

$$
R_\omega(f):H^{-s}\longrightarrow H^t
\tag{5.3}
$$

continuously for all $s,t\geq0$. Thus convolution is infinitely smoothing in the sense needed
for an elliptic factorization.

### 5.2 Finite level and finite compact type

Equation (2.10) confines the operator to two finite analytic data sets. Let

$$
\mathcal H_L=P_L L^2_{\mathrm{cusp},\omega},\qquad
\mathcal H_R=P_R L^2_{\mathrm{cusp},\omega}.
\tag{5.4}
$$

Each is a finite direct sum of spaces with one compact open level and one archimedean maximal
compact type. Enlarging the level and the finite type set if necessary, we may place both in a
single finite-data space $\mathcal H_0$. Then

$$
R_\omega(f)=P_0R_\omega(f)P_0.
\tag{5.5}
$$

This is the point at which a possible infinite sum over compact types disappears. A general
Schwartz convolution operator might require uniform trace-norm estimates over all types. Our
finite-type hypothesis makes only finitely many of them occur.

### 5.3 The cuspidal measuring operator

On $\mathcal H_0$, let $A\geq1$ be the positive self-adjoint elliptic measuring operator from
cuspidal Sobolev theory. It includes a positive compact-direction operator, so it is elliptic on
the fixed types. Its form domain embeds compactly, hence it has compact resolvent. Write its
eigenvalues, with multiplicity, as

$$
1\leq\lambda_1\leq\lambda_2\leq\cdots,
$$

and its counting function as $N_A(\Lambda)$. The established polynomial bound gives constants
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

To see this directly, divide the eigenvalues into dyadic intervals. The contribution to
$\sum\lambda_j^{-r}$ from $2^k\leq\lambda_j<2^{k+1}$ is at most
$C2^{kD}2^{-kr}$, which is summable for $r>D$. The square-sum statement is identical with
$r$ replaced by $2r$.

### 5.4 Two-sided Sobolev smoothing

Elliptic norm equivalence translates (5.3) into the boundedness of

$$
A^rR_\omega(f)A^s
\tag{5.8}
$$

on $\mathcal H_0$ for every $r,s\geq0$, initially on the algebraic span of eigenvectors and then
by closure. Indeed, the right factor $A^s$ measures a positive Sobolev order in the input;
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

Choose an integer $r>D$. From (5.8), $A^rR_\omega(f)$ is bounded, while $A^{-r}$ is trace class.
Thus on $\mathcal H_0$,

$$
R_\omega(f)=A^{-r}\big(A^rR_\omega(f)\big)
\tag{6.1}
$$

is trace class. On the orthogonal complement of $\mathcal H_0$ it is zero by (5.5), so it is
trace class on all of $L^2_\omega$.

This proof makes the logical roles transparent. Cuspidality supplies compact resolvent;
polynomial counting supplies summability of $A^{-r}$; smooth convolution supplies boundedness
of the other factor; finite type prevents an uncontrolled infinite direct sum.

### 6.2 The two-sided Hilbert--Schmidt factorization

For the diagonal formula, choose $r$ with $2r>D$. Put

$$
S=A^rR_\omega(f)A^r.
$$

Then $S$ is bounded and

$$
R_\omega(f)=A^{-r}SA^{-r}.
\tag{6.2}
$$

Both outer factors are Hilbert--Schmidt, so their product through the bounded operator $S$ is
trace class. More explicitly, $A^{-r}S$ is Hilbert--Schmidt and

$$
\|R_\omega(f)\|_1
\leq\|A^{-r}\|_2^2\|S\|.
\tag{6.3}
$$

Unlike a formal restriction of an $L^2$ kernel to its diagonal, (6.2) provides an honest
two-kernel contraction. It will be the safe route from operator trace to diagonal integral.

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

is continuous on each fixed finite-level, finite-type admissible Schwartz space. If $f_n\to f$
in that topology, then $R_\omega(f_n)\to R_\omega(f)$ in trace norm and their traces converge.

This continuity also makes finite sums of factorizable tests harmless: prove the formula tensor
by tensor and use linearity and (6.4). No density assertion for compactly supported
archimedean tests is needed in the stronger algebraic-weight topology of Section 2.1.

### 6.4 Why typewise trace class is enough here

The typewise compact-resolvent theorem alone would not imply trace class on the whole cuspidal
space. An infinite direct sum of trace-class blocks is trace class only when the sum of their
trace norms converges. Equation (5.5) is stronger: all but finitely many level-type blocks are
exactly zero. Therefore the finite sum of their trace norms is automatically finite.

This is one reason for retaining compact-finiteness in the test class. A larger Schwartz algebra
can also be treated, but it requires quantitative decay of the test function in the compact dual
and an additional summation theorem. That extension is unnecessary for the simple kernel used
here.

## 7. The canonical diagonal and the operator trace

### 7.1 Why a formal diagonal is insufficient

An $L^2$ kernel is defined only almost everywhere on a product space. The diagonal has product
measure zero, so changing an $L^2$ representative there changes the expression $K(x,x)$ without
changing the operator. Moreover, a Hilbert--Schmidt operator need not be trace class. Thus the
formula

$$
\operatorname{tr}T=\int K(x,x)\,dx
$$

is not a definition.

Our situation has two extra structures. The Poincare series (3.1) selects a smooth canonical
representative, and the factorization (6.2) proves trace class before the diagonal is used. We
must still show that the canonical representative agrees with the contraction kernel produced
by (6.2) and that its diagonal is integrable.

### 7.2 Identification of the canonical kernel

Fix first a finite derivative order. Since (5.8) holds for every exponent, increase $r$ in
(6.2) until the inverse-power kernel theorem gives a cuspidal kernel $H_r(x,y)$ with that many
continuous derivatives and the corresponding rapid-decay bounds. Put $B=A^{-r}$ and define
the $L^2$ row vector

$$
h_x(y)=\overline{H_r(x,y)}.
\tag{7.1}
$$

Then $(Bu)(x)=\langle u,h_x\rangle$. The high inverse-power kernel estimates from cuspidal
Sobolev theory say that $x\mapsto h_x$ has the chosen number of continuous $L^2$-valued
derivatives and that each decreases rapidly in every cusp. Since $S$ is bounded,

$$
L_f(x,y)=\overline{\big(BS^*h_x\big)(y)}
\tag{7.2}
$$

defines a kernel with the chosen differentiability and decay in both variables. Moreover,

$$
(BSB u)(x)=\langle SB u,h_x\rangle
=\langle u,BS^*h_x\rangle
=\int L_f(x,y)u(y)\,dy,
$$

first for smooth compactly supported $u$ and then for every $u\in L^2$. This construction does
not pretend that the middle bounded operator $S$ has a pointwise kernel.

Indeed, self-adjointness of $B$ gives

$$
L_f(x,y)=\langle h_y,S^*h_x\rangle,
$$

so every differentiated value is bounded by $\|S\|$ times the corresponding rapidly decreasing
$L^2$ row norms at $x$ and $y$. This proves the asserted simultaneous decay rather than only
separate smoothness.

Both $L_f$ and $K_f$ represent $R_\omega(f)$ by Proposition 3.3 and (6.2). Taking the chosen
order at least zero, their difference is continuous. Pairing the two operator formulas against
compactly supported smooth vectors in both variables shows that this difference is the zero
distribution on $[\overline G]\times[\overline G]$. A continuous function defining the zero
distribution for a measure of full support vanishes everywhere. Hence

$$
L_f(x,y)=K_f(x,y)
\tag{7.3}
$$

for all $x,y$. This upgrades almost-everywhere kernel uniqueness to pointwise equality. It also
proves rapid two-variable decay through the chosen derivative order at the correct logical
point: after a global smoothing factorization has supplied $L^2$ row estimates. Repeating the
argument with larger $r$ proves the statement for every order; the result is always the same
canonical kernel $K_f$. Local convergence of the Poincare series alone would not have done so.

### 7.3 Absolute diagonal integrability

Write (6.2) as $UV$ with
$U=A^{-r}S$ and $V=A^{-r}$. Both are Hilbert--Schmidt. If $K_U,K_V$ are their $L^2$ kernels,
the diagonal contraction

$$
x\longmapsto\int K_U(x,y)K_V(y,x)\,dy
\tag{7.4}
$$

belongs to $L^1$, because Cauchy--Schwarz on the product gives norm at most
$\|U\|_2\|V\|_2$. With the row convention above,

$$
K_U(x,y)=\overline{(S^*h_x)(y)},
\qquad K_V(y,x)=h_x(y).
$$

Thus the contraction is defined for every $x$ and equals

$$
\int \overline{(S^*h_x)(y)}h_x(y)\,dy
=\langle h_x,S^*h_x\rangle
=L_f(x,x)=K_f(x,x).
\tag{7.5}
$$

Consequently

$$
\int_{[\overline G]}|K_f(x,x)|\,dx<\infty.
\tag{7.6}
$$

This supplies the bridge between the Hilbert--Schmidt equivalence class and the canonical smooth
representative without relying on the visual plausibility of a pointwise diagonal.

### 7.4 The diagonal trace theorem

**Theorem 7.1.** For every admissible cuspidal test function,

$$
\operatorname{tr}R_\omega(f)
=\int_{[\overline G]}K_f(x,x)\,dx,
\tag{7.7}
$$

and the integral is absolutely convergent.

**Proof.** Use the Hilbert--Schmidt product formula on $UV$ from Section 7.3. It identifies the
operator trace with the integral of the contraction (7.4). Identity (7.5) turns that
contraction into $K_f(x,x)$, and (7.6) gives absolute convergence. $\square$

The order of proof is decisive: trace ideal, canonical kernel, integrable diagonal, trace
identity. Reversing that order would assume the main analytic conclusion.

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

The index set is countable. On fixed level, compact type, and bounded elliptic window, only
finitely many summands occur, counted with multiplicity and type dimension. Smooth finite-type
vectors are rapidly decreasing.

Right convolution respects every isotypic summand and acts as

$$
R_\omega(f)|_{M_\pi\otimes\mathcal H_\pi}
=I_{M_\pi}\otimes\pi(f).
\tag{8.2}
$$

No multiplicity-one theorem is being used. The factor $m(\pi)$ must remain in the trace.

### 8.2 Traces on irreducible summands

Because $f$ is left and right finite under level and compact type, $\pi(f)$ has finite-dimensional
range. Indeed, the local projectors in (2.10) make its range lie in a finite sum of admissible
fixed-vector and compact-type spaces. Thus $\pi(f)$ is finite rank and
$\operatorname{tr}\pi(f)$ is an ordinary finite-dimensional trace.

Equivalently, choose an orthonormal basis $(e_{\pi,j})$ adapted to compact types. Only finitely
many basis vectors can contribute to the diagonal of $\pi(f)$, and

$$
\operatorname{tr}\pi(f)=\sum_j\langle\pi(f)e_{\pi,j},e_{\pi,j}\rangle.
\tag{8.3}
$$

The finiteness is representation by representation. Absolute convergence over all $\pi$ comes
from global trace class, not from this observation alone.

### 8.3 Absolute convergence of the spectral side

Let $P_\pi$ be the orthogonal projection onto the summand in (8.1). A trace-class operator
which is block diagonal satisfies

$$
\sum_\pi\|P_\pi R_\omega(f)P_\pi\|_1
=\|R_\omega(f)\|_1.
\tag{8.4}
$$

This follows first for finite sums of projections and then by monotone convergence applied to
$|R_\omega(f)|$, or by the direct-sum criterion for trace ideals. Therefore

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

and both sides are absolutely convergent in the senses of (7.6) and (8.5).

**Proof.** Equation (4.4) makes the operator zero off the cuspidal space. Take the trace in the
orthogonal decomposition (8.1), use (8.2), and apply the direct-sum trace identity justified by
(8.4). The diagonal trace theorem identifies the same trace with the left side. $\square$

This completes the spectral half of the trace formula without invoking a Plancherel formula for
the full automorphic space.

## 9. Equality of the spectral and geometric kernel expansions

The spectral expansion has now been justified as an ordinary trace. What remains in this book
is to identify the same number with the geometric object that was used to construct the
operator. At this stage “geometric expansion” means the diagonal of the rational Poincare
kernel. It does not yet mean a sum of orbital integrals. That distinction preserves the
dependency order: rational conjugacy, centralizer measures, orbital convergence, and the
central-plus-elliptic regrouping are the work of the later geometric-side volume.

### 9.1 Compact truncations of the geometric kernel

Let $\chi_T$ be a smooth reduction-theoretic cutoff which is one below cusp height $T$, zero
above height $2T$, and has invariant derivatives bounded independently of $T$. Define

$$
I_T(f)=
\int_{[\overline G]}
\chi_T(x)
\sum_{\gamma\in Z(F)\backslash G(F)}
f(x^{-1}\gamma x)\,dx.
\tag{9.1}
$$

For fixed $T$, the support of $\chi_T$ is compact on the fixed-level quotient. Theorem 3.2
gives absolute, uniform convergence of the rational sum there. It follows that (9.1) is an
ordinary integral and that sum, differentiation, and integration may be interchanged on this
truncation. In particular,

$$
I_T(f)=\int_{[\overline G]}\chi_T(x)K_f(x,x)\,dx.
\tag{9.2}
$$

This is the safe finite-height geometric expansion. Notice what has not been asserted:
$\sum_\gamma |f(x^{-1}\gamma x)|$ need not be globally integrable. Strong cuspidality creates
cancellation after periodization, and absolute values can destroy it.

### 9.2 The simple cuspidal kernel identity

**Theorem 9.1 (simple cuspidal kernel trace formula).** Let $F$ have a real place, let
$\omega$ be a unitary idele class character, and let $f$ be a finite sum of factorizable
admissible cuspidal tests of inverse central character $\omega^{-1}$. Then
$R_\omega(f)$ is trace class on $L^2_\omega$, is zero on the noncuspidal subspace, and

# $$\boxed{\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}m(\pi)\operatorname{tr}\pi(f)

\int_{[\overline G]}
\sum_{\gamma\in Z(F)\backslash G(F)}
f(x^{-1}\gamma x)\,dx.}
\tag{9.3}
$$

The spectral series is absolutely convergent, the Poincare series is absolutely and locally
uniformly convergent with every derivative, and its canonical diagonal is absolutely integrable.
The right side means the integral of that canonical summed kernel, not an unproved exchange of
the global integral with the rational sum.

**Proof.** Theorem 3.2 constructs the smooth Poincare kernel and Proposition 3.3 identifies its
operator with $R_\omega(f)$. Chapter 4 puts both the operator and its adjoint in the cuspidal
space and annihilates the Eisenstein and residual complement. Chapters 5 and 6 prove trace
class. Theorem 7.1 identifies the trace with the absolutely convergent diagonal integral, while
Theorem 8.1 identifies the same trace with the absolutely convergent cuspidal spectral series.
Substitution gives (9.3). Every equality is therefore an equality of already-defined ordinary
quantities. $\square$

This is exactly the analytic simple-trace-formula setting promised by the book: no regularized
operator, truncated spectral distribution, or continuous-spectrum correction survives.

### 9.3 Independence of auxiliary truncations

Since $0\leq\chi_T\leq1$, $\chi_T(x)\to1$, and $K_f(x,x)\in L^1$, dominated convergence
gives

# $$\lim_{T\to\infty}I_T(f)

\int_{[\overline G]}K_f(x,x)\,dx.
\tag{9.4}
$$

The same conclusion holds for any other family of cutoffs with pointwise limit one and a
uniform bound. Thus the right side of (9.3) is independent of the reduction coordinates,
smooth transition band, or chosen exhaustion.

This argument is deliberately shorter than an orbital truncation argument. Trace class and the
canonical $L^1$ diagonal have already absorbed the cusp analysis. No stable-line regrouping is
needed to remove the auxiliary cutoff at the kernel level.

### 9.4 The boundary with the orbital geometric side

The diagonal in (9.3) contains rational elements of four familiar kinds: central, split regular,
noncentral nonsemisimple, and elliptic. Classifying them algebraically is elementary, but three
further assertions are not:

1. regrouping the noncompact diagonal integral by rational conjugacy classes;
2. proving that split and unipotent distributions vanish after the correct parabolic unfolding;
3. proving absolute convergence of the remaining elliptic orbital distributions with compatible
   centralizer measures.

Those results are neither consequences of trace class nor supplied by Books 88--91. Proving
them here would silently import the content of the later geometric-side book into one of its own
prerequisites. Accordingly, (9.3) is the terminal geometric statement of this volume. The later
geometric analysis starts from its canonical $L^1$ diagonal and performs the conjugacy-class
regrouping with the additional arithmetic and local orbital estimates it establishes there.

## 10. Examples, boundaries, and failure modes

### 10.1 A fixed-weight kernel over the rationals

Take $F=\mathbf Q$, $v_0=\infty$, and choose a sufficiently high fixed discrete-series weight
with the desired central character. Section 2.3 supplies a kernel-admissible, compact-finite,
strongly cuspidal coefficient $f_\infty$ at that weight.
Choose at every finite prime a compactly supported Hecke function, spherical almost everywhere.
The resulting kernel

$$
K_f(x,y)=\sum_{\gamma\in\mathbf Q^\times\backslash
\mathrm{GL}_2(\mathbf Q)}f(x^{-1}\gamma y)
$$

is smooth, cuspidal in both variables, and rapidly decreasing in the modular cusp. Its trace is
the absolutely convergent sum over the cuspidal representations detected by the chosen
archimedean factor.

The geometric expression at this stage is the integral of the displayed Poincare kernel on its
diagonal. Its later division into central, split, unipotent, and elliptic conjugacy terms is not
being assumed here.

### 10.2 Adding finite-place Hecke conditions

At a prime $p$ away from the level, replace the spherical identity by a compactly supported
spherical Hecke function. This does not disturb strong cuspidality at infinity. On the spectral
side it inserts the corresponding Hecke operator $\pi_p(f_p)$; in the Poincare kernel it changes
the finite-place support of the rational summands. All convergence proofs remain uniform on a
fixed finite-dimensional subspace of the spherical Hecke algebra.

At ramified primes one may instead impose compact-open projectors or matrix coefficients. The
left-right invariance subgroups change, hence so does the finite level $\mathcal H_0$, but the
trace-class proof is unchanged. This flexibility is why the cuspidal factor is placed at one
archimedean place: the finite factors remain free for level and comparison conditions.

### 10.3 What fails without a cuspidal factor

If the archimedean factor is a general Schwartz function, the periodized kernel may still
converge locally and define a bounded smoothing operator. Three later conclusions fail.

First, the constant term of the kernel need not vanish. Constant-mode wave packets can move
arbitrarily far into the cusp with bounded energy, so the relevant elliptic operator does not
have compact resolvent on that channel. Second, the operator acts nontrivially on Eisenstein
families and their residues; a purely cuspidal spectral sum is incomplete. Third, the raw
diagonal develops parabolic contributions whose integrals require truncation and compensation.

Total integral zero does not repair these failures. It kills at most one one-dimensional
character. The averaged local condition $f^B=0$ kills induced traces but need not kill induced
operators, so it is insufficient for the two-variable kernel proof. Strong cuspidality (2.2)
is exactly the hypothesis used at every cancellation step.

### 10.4 What this formula does not yet compute

The theorem does not compute $\operatorname{tr}\pi(f)$, and it does not yet regroup the rational
diagonal by conjugacy. The spectral side, the orbital geometric side, and comparison with an
inner form require their own multiplicity, centralizer-measure, orbital-integral, matching, and
local transfer arguments.

Those are subsequent tasks. The present theorem supplies the trace-class operator and canonical
$L^1$ diagonal from which they begin, with a measure framework that prevents a later local scalar
from being hidden in a global quotient volume.

## 11. Final synthesis

### 11.1 The proof ledger

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
&\text{canonical Poincare kernel}+\text{integrable diagonal}
&&\Longrightarrow \text{the geometric kernel expansion}.
\end{aligned}
\tag{11.1}
$$

No arrow is redundant. Local convergence does not imply diagonal integrability; discreteness
does not imply trace class; trace class does not by itself justify a chosen pointwise diagonal;
and cuspidal spectral annihilation does not by itself prove geometric orbital convergence.

### 11.2 The reusable kernel theorem

The argument may be summarized in a form useful for later comparison.

**Theorem 11.1 (cuspidal kernel package).** Under the hypotheses of Theorem 9.1, the Poincare
series $K_f$ is the unique smooth representative of the distribution kernel of $R_\omega(f)$
and is rapidly decreasing with all derivatives in both variables. The operator is trace class,
has range and adjoint range in the cuspidal space, and has three equal descriptions:

$$
\begin{aligned}
\operatorname{tr}R_\omega(f)
&=\int_{[\overline G]}K_f(x,x)\,dx\\
&=\sum_\pi m(\pi)\operatorname{tr}\pi(f).
\end{aligned}
\tag{11.2}
$$

The diagonal integral and spectral series are absolutely convergent. The Poincare series is
absolutely locally uniformly convergent with every derivative, and all measures arise from the
fixed local Haar measures by quotient integration.

**Proof.** This is the conjunction of Theorems 3.2, 7.1, 8.1, and 9.1, together with the
two-variable decay proved in Section 7.2. $\square$

### 11.3 Conclusion

The kernel trace formula in rank two becomes an ordinary trace identity when one archimedean factor
removes the single proper parabolic channel. That local cancellation has three global effects:
the kernel is cuspidal in both variables, the convolution operator annihilates every Eisenstein
wave packet and residue, and the trace needs no continuous-spectrum regularization.

The remaining analysis is exact rather than formal. Projective counting constructs the kernel;
cuspidal Sobolev theory confines it; elliptic half-powers make it trace class; a
Hilbert--Schmidt contraction legitimizes and integrates its diagonal. The spectral expansion
and geometric kernel expansion are therefore not competing definitions. They are two ordinary
evaluations of the same canonical operator trace.

This completes the analytic kernel foundation for the rank-two simple trace formula. The
cuspidal spectral distribution and canonical $L^1$ Poincare diagonal now stand in one
measure-compatible identity, ready for their separate spectral and orbital geometric analyses.
