# Analytic Foundations for Odlyzko--Poitou Bounds

## Contents

1. [The discriminant as analytic complexity](#1-the-discriminant-as-analytic-complexity)
   - [The problem and the scale](#11-the-problem-and-the-scale)
   - [Degree, signature, and root discriminant](#12-degree-signature-and-root-discriminant)
   - [The shape of a useful lower bound](#13-the-shape-of-a-useful-lower-bound)
   - [Scope and standing conventions](#14-scope-and-standing-conventions)
2. [The geometric baseline](#2-the-geometric-baseline)
   - [The Minkowski lattice](#21-the-minkowski-lattice)
   - [The convex-body argument](#22-the-convex-body-argument)
   - [The exact root-discriminant inequality](#23-the-exact-root-discriminant-inequality)
   - [Monotonicity of the factorial factor](#24-monotonicity-of-the-factorial-factor)
   - [Why geometry is not enough](#25-why-geometry-is-not-enough)
3. [Dedekind zeta functions in the Euler half-plane](#3-dedekind-zeta-functions-in-the-euler-half-plane)
   - [Ideals and absolute convergence](#31-ideals-and-absolute-convergence)
   - [Euler products](#32-euler-products)
   - [Logarithmic derivatives](#33-logarithmic-derivatives)
   - [Prime powers and positivity](#34-prime-powers-and-positivity)
4. [Completion and the functional equation](#4-completion-and-the-functional-equation)
   - [Archimedean local factors](#41-archimedean-local-factors)
   - [Theta kernels and dual lattices](#42-theta-kernels-and-dual-lattices)
   - [Continuation and functional equation](#43-continuation-and-functional-equation)
   - [Poles, zeros, and growth](#44-poles-zeros-and-growth)
   - [Discriminant and analytic conductor](#45-discriminant-and-analytic-conductor)
5. [Transforms and admissible test functions](#5-transforms-and-admissible-test-functions)
   - [Transform conventions](#51-transform-conventions)
   - [The basic admissible class](#52-the-basic-admissible-class)
   - [Positive type and autocorrelation](#53-positive-type-and-autocorrelation)
   - [Two positivity regimes](#54-two-positivity-regimes)
6. [The Weil--Poitou explicit formula](#6-the-weil--poitou-explicit-formula)
   - [Statement with every term visible](#61-statement-with-every-term-visible)
   - [The truncated contour identity](#62-the-truncated-contour-identity)
   - [Prime and discriminant terms](#63-prime-and-discriminant-terms)
   - [Gamma and pole terms](#64-gamma-and-pole-terms)
   - [Removing the truncations](#65-removing-the-truncations)
   - [Normalization diagnostics](#66-normalization-diagnostics)
7. [Positivity of the zero term](#7-positivity-of-the-zero-term)
   - [The conditional argument](#71-the-conditional-argument)
   - [The strip-positive kernel](#72-the-strip-positive-kernel)
   - [The unconditional argument](#73-the-unconditional-argument)
   - [What positivity does not permit](#74-what-positivity-does-not-permit)
8. [Archimedean losses and test-function design](#8-archimedean-losses-and-test-function-design)
   - [The three governing integrals](#81-the-three-governing-integrals)
   - [The triangular autocorrelation](#82-the-triangular-autocorrelation)
   - [Exact evaluation of the archimedean terms](#83-exact-evaluation-of-the-archimedean-terms)
   - [Smoothing corners without changing the bound](#84-smoothing-corners-without-changing-the-bound)
9. [Universal Odlyzko--Poitou inequalities](#9-universal-odlyzko--poitou-inequalities)
   - [One test function, one rigorous bound](#91-one-test-function-one-rigorous-bound)
   - [Unconditional asymptotic constants](#92-unconditional-asymptotic-constants)
   - [Bounds under the generalized Riemann hypothesis](#93-bounds-under-the-generalized-riemann-hypothesis)
   - [Degree and signature monotonicity](#94-degree-and-signature-monotonicity)
   - [Threshold and stabilization principles](#95-threshold-and-stabilization-principles)
10. [Certified numerical evaluation](#10-certified-numerical-evaluation)
    - [Rational enclosures for elementary constants](#101-rational-enclosures-for-elementary-constants)
    - [Finite formulas for $B_T$ and $C_T$](#102-finite-formulas-for-b_t-and-c_t)
    - [Tail bounds and interval propagation](#103-tail-bounds-and-interval-propagation)
    - [A reproducible certificate format](#104-a-reproducible-certificate-format)
11. [The finite-degree certificate ledger](#11-the-finite-degree-certificate-ledger)
    - [The threshold $4$](#111-the-threshold-4)
    - [The threshold $3^{3/2}$](#112-the-threshold-332)
    - [The threshold $5^{5/4}$](#113-the-threshold-554)
    - [The two-prime threshold $3^{3/2}2^{2/3}$](#114-the-two-prime-threshold-332223)
    - [Totally real certificates](#115-totally-real-certificates)
    - [A quadratic-base certificate](#116-a-quadratic-base-certificate)
12. [Signature grids and optimization](#12-signature-grids-and-optimization)
    - [Intermediate signatures](#121-intermediate-signatures)
    - [Finite rational searches](#122-finite-rational-searches)
    - [Prime-ideal information](#123-prime-ideal-information)
    - [Choosing between geometry and the explicit formula](#124-choosing-between-geometry-and-the-explicit-formula)
13. [Applications to discriminant ceilings](#13-applications-to-discriminant-ceilings)
    - [The abstract comparison theorem](#131-the-abstract-comparison-theorem)
    - [Nested fields and bounded-root-discriminant towers](#132-nested-fields-and-bounded-root-discriminant-towers)
    - [Uniform finite composita](#133-uniform-finite-composita)
    - [Base fields and auxiliary primes](#134-base-fields-and-auxiliary-primes)
14. [Failure diagnostics](#14-failure-diagnostics)
    - [A growing ceiling is not uniform](#141-a-growing-ceiling-is-not-uniform)
    - [Bounded step degree is not bounded total degree](#142-bounded-step-degree-is-not-bounded-total-degree)
    - [Signature is not inherited automatically](#143-signature-is-not-inherited-automatically)
    - [Endpoint and normalization failures](#144-endpoint-and-normalization-failures)
    - [Analysis controls size, not group shape](#145-analysis-controls-size-not-group-shape)
15. [The reusable theorem package](#15-the-reusable-theorem-package)
    - [Explicit lower-bound theorem](#151-explicit-lower-bound-theorem)
    - [Certified cutoff theorem](#152-certified-cutoff-theorem)
    - [Unconditional and conditional ledgers](#153-unconditional-and-conditional-ledgers)
16. [Conclusion](#16-conclusion)

## 1. The discriminant as analytic complexity

### 1.1 The problem and the scale

A number field can be large in two very different senses. Its degree counts embeddings, while its discriminant records how tightly the ring of integers sits inside its real and complex ambient space. Local ramification can give an upper bound for the discriminant of a field constructed arithmetically. The analytic problem is to force a lower bound from the mere existence of the field.

The useful comparison is not between absolute discriminants. If $K\subseteq L$ is unramified at every finite prime, then

$$
|D_L|=|D_K|^{[L:K]},
$$

so the absolute discriminant grows even though no new finite ramification has appeared. Taking a degree root removes precisely this repetition. The natural invariant is

$$
\operatorname{rd}(K)=|D_K|^{1/[K:\mathbf Q]}.
$$

The analytic theory developed here produces inequalities of the form

$$
\operatorname{rd}(K)\geq L(n,r_1),
\qquad n=[K:\mathbf Q],
$$

where $L(n,r_1)$ rises with the degree and improves when more embeddings are real. Such a lower bound becomes decisive when arithmetic supplies a degree-independent ceiling $\operatorname{rd}(K)<U$.

### 1.2 Degree, signature, and root discriminant

Write the signature of $K$ as $(r_1,r_2)$, so

$$
n=r_1+2r_2.
$$

The discriminant convention throughout is

$$
D_K=\left|\operatorname{disc}(\mathcal O_K/\mathbf Z)\right|>0.
$$

The signed discriminant has sign $(-1)^{r_2}$, but only its absolute value enters the completed zeta function and the root discriminant. We normalize the real proportion by

$$
\alpha(K)=\frac{r_1}{n}\in[0,1].
$$

Thus $\alpha=0$ is the safe unrestricted signature, while $\alpha=1$ means totally real. A field with $r_1=0$ need not possess any special involution; the analytic formula sees the signature and nothing more.

For a finite extension $L/K$, let $\mathfrak d_{L/K}\subseteq\mathcal O_K$ denote the relative discriminant ideal. Discriminant transitivity gives

$$
D_L=D_K^{[L:K]}N_{K/\mathbf Q}(\mathfrak d_{L/K}),
$$

and hence

$$
\operatorname{rd}(L)
=\operatorname{rd}(K)
N_{K/\mathbf Q}(\mathfrak d_{L/K})^{1/[L:\mathbf Q]}
\geq\operatorname{rd}(K).
$$

Equality holds exactly when $L/K$ is unramified at every finite prime. This monotonicity is algebraic and must not be confused with the analytic monotonicity in degree proved later.

### 1.3 The shape of a useful lower bound

Three levels of conclusion recur.

First, if a lower bound valid in degree $n$ exceeds an arithmetic ceiling, fields of that degree cannot occur. Second, if the lower bound is increasing and crosses the ceiling at degree $N$, every possible degree is at most $N-1$. Third, if the fields form a nested chain, bounded degree forces eventual equality and hence stabilization.

These conclusions require strict bookkeeping. If arithmetic gives $\operatorname{rd}(K)<U$ and analysis gives $\operatorname{rd}(K)\geq U$, there is a contradiction. If the arithmetic inequality is weak, $\operatorname{rd}(K)\leq U$, then the analytic lower bound must be strictly greater than $U$ unless equality is independently impossible. An asymptotic constant alone never excludes a finite degree; one must exhibit the degree at which a finite test-function bound crosses the ceiling.

### 1.4 Scope and standing conventions

Only discriminant bounds are developed here. No distribution theorem for Frobenius classes enters any proof. The foundational tools are real and complex integration, including Tonelli's theorem, Fubini's theorem, and dominated convergence; Fourier inversion and Poisson summation for rapidly decreasing functions; the residue theorem, Jensen's formula, Borel--Carathéodory, Cauchy's derivative estimates, and the Phragmén--Lindelöf principle on a strip; the defining gamma integral and its functional identities; geometry of numbers; unique factorization of ideals; Dirichlet's unit theorem; and the elementary arithmetic of number-field discriminants. Finiteness of the ideal class group also follows from Theorem 2.1, because only finitely many integral ideals have bounded norm.

No factorization theorem for entire functions and no Stirling asymptotic is assumed. Section 4.4 derives the only growth estimates required here, constructs the genus-one product directly from the zeros, and proves that the remaining zero-free factor is exponential-linear. The same section obtains the fixed-height gamma bounds from Euler's logarithmic-derivative series. Thus the later explicit formula rests on the displayed construction rather than on an unnamed theorem of entire-function theory. Nothing stronger, such as a zero-free region or a prime-number theorem, is used.

Fourier transforms use angular frequency:

$$
\widehat f(t)=\int_{-\infty}^{\infty}f(x)e^{-itx}\,dx.
$$

There is no $2\pi$ in the exponent. Euler's constant is denoted by $\gamma$. Every logarithm is natural. Sums over zeros are symmetric limits with multiplicity. These conventions determine every factor of $2$ and $\pi$ below.

## 2. The geometric baseline

### 2.1 The Minkowski lattice

Before zeta functions enter, geometry of numbers gives a universal lower bound. Embed $K$ diagonally in

$$
K_{\mathbf R}=K\otimes_{\mathbf Q}\mathbf R
\simeq\mathbf R^{r_1}\times\mathbf C^{r_2}.
$$

Each complex coordinate carries ordinary two-dimensional Lebesgue measure. With that convention, the image of $\mathcal O_K$ is a lattice of covolume

$$
2^{-r_2}\sqrt{D_K}.
$$

For a nonzero fractional ideal $I$, the covolume is multiplied by $N(I)$. The factor $2^{-r_2}$ arises when one conjugate pair is replaced by real and imaginary coordinates. Losing it changes the final signature factor from $(\pi/4)^{2r_2}$.

### 2.2 The convex-body argument

**Theorem 2.1 (Minkowski ideal-class estimate).** Every ideal class contains an integral ideal $\mathfrak a$ satisfying

$$
N\mathfrak a\leq
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{D_K}.
$$

**Proof.** Choose a fractional ideal $I$ representing the inverse class. In $K_{\mathbf R}$ consider the convex symmetric region

$$
\sum_{v\text{ real}}|x_v|
+2\sum_{v\text{ complex}}|z_v|\leq T.
$$

Successive integration over the simplex gives its volume as

$$
\frac{2^{r_1}(\pi/2)^{r_2}}{n!}T^n.
$$

When this is larger than $2^n$ times the covolume of $I$, Minkowski's convex-body theorem supplies $0\ne x\in I$ inside the region. Weighted arithmetic--geometric mean yields

$$
|N_{K/\mathbf Q}(x)|\leq\left(\frac Tn\right)^n.
$$

For every $T$ above the critical value, the constructed integral ideal has integral norm bounded by the corresponding right-hand side. Since positive integral ideal norms are discrete, letting $T$ decrease to the critical value and substituting the covolume gives

$$
\frac{|N(x)|}{N(I)}\leq
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{D_K}.
$$

The ideal $xI^{-1}$ is integral, lies in the desired class, and has norm $|N(x)|/N(I)$. $\square$

The proof explains the constant: the factorial comes from the simplex, while $4/\pi$ measures the difference between a complex disc and a real box.

### 2.3 The exact root-discriminant inequality

Apply Theorem 2.1 to the principal class. Every nonzero integral ideal has norm at least $1$, so

$$
1\leq
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{D_K}.
$$

Therefore

$$
\boxed{
D_K\geq
\left(\frac\pi4\right)^{2r_2}
\frac{n^{2n}}{(n!)^2}.}
$$

Taking $n$th roots and using $2r_2/n=1-\alpha$ gives

$$
\boxed{
\operatorname{rd}(K)\geq
\left(\frac\pi4\right)^{1-\alpha}M_n,
\qquad
M_n=\left(\frac{n^n}{n!}\right)^{2/n}.}
$$

For a totally real field the factor $\pi/4$ disappears. For arbitrary signature the worst case is $\alpha=0$.

### 2.4 Monotonicity of the factorial factor

The later finite cutoffs use the fact that $M_n$ increases. This deserves proof rather than numerical assumption.

Put $a_n=(n!)^{1/n}/n$, so $M_n=a_n^{-2}$. It is enough to prove $a_{n+1}\leq a_n$. Raising to the positive power $n(n+1)$ shows that this is equivalent to

$$
\left(1+\frac1n\right)^{n^2}\geq\frac{n^n}{n!}.
$$

Both sides admit elementary estimates in the needed direction. Since $\log x$ is increasing,

$$
\log(n!)=\sum_{k=1}^n\log k
\geq\int_1^n\log x\,dx
=n\log n-n+1,
$$

so $\log(n^n/n!)\leq n-1$. On the other hand,

$$
\log(1+u)\geq u-\frac{u^2}{2}
\qquad(0\leq u\leq1),
$$

because the derivative of the difference is $u^2/(1+u)\geq0$. With $u=1/n$ this gives

$$
n^2\log\left(1+\frac1n\right)\geq n-\frac12\geq n-1.
$$

The required comparison follows, and therefore $M_{n+1}\geq M_n$.

The limit needs no factorial asymptotic. Monotonicity of $\log x$ also gives the reverse
integral comparison

$$
\log(n!)\leq\int_1^n\log x\,dx+\log n
=n\log n-n+1+\log n.
$$

Together with the lower bound already proved, this says
$\log(n!)=n\log n-n+O(\log n)$. Hence
$\log M_n=2+O(\log n/n)$ and consequently

$$
M_n\longrightarrow e^2,
$$

and the two extreme geometric limits are

$$
\frac{\pi e^2}{4}=5.803\ldots,
\qquad e^2=7.389\ldots.
$$

### 2.5 Why geometry is not enough

The geometric bound is remarkably effective at small thresholds. It will certify the cutoffs at $4$ and $3^{3/2}$. But it cannot handle every small-ramification problem. In particular,

$$
5^{5/4}=7.4767\ldots>e^2,
$$

so even the totally real Minkowski limit lies below the desired ceiling. More information is required. Dedekind zeta functions supply it by placing prime ideals, the discriminant, archimedean places, and zeros into a single identity.

## 3. Dedekind zeta functions in the Euler half-plane

### 3.1 Ideals and absolute convergence

For $\Re(s)>1$, define

$$
\zeta_K(s)=
\sum_{0\ne\mathfrak a\subseteq\mathcal O_K}(N\mathfrak a)^{-s}.
$$

There are only finitely many integral ideals of bounded norm. To see absolute convergence, group prime ideals by the rational prime below them. At most $n$ prime ideals lie over a rational prime $p$, and every such ideal has norm at least $p$. Hence, for $\sigma>1$,

$$
\prod_{\mathfrak p}\left(1-(N\mathfrak p)^{-\sigma}\right)^{-1}
\leq\prod_p(1-p^{-\sigma})^{-n}
=\zeta(\sigma)^n<\infty.
$$

Expanding the product proves absolute convergence of the ideal series, uniformly on each half-plane $\Re(s)\geq1+\varepsilon$. It follows that $\zeta_K$ is holomorphic there and may be differentiated term by term on smaller closed half-planes.

### 3.2 Euler products

Unique factorization of nonzero ideals gives

$$
\boxed{
\zeta_K(s)=\prod_{\mathfrak p}
\left(1-(N\mathfrak p)^{-s}\right)^{-1},
\qquad \Re(s)>1.}
$$

Absolute convergence makes rearrangement legitimate. The product has no zero in this half-plane: its logarithm is represented by an absolutely convergent series. In particular, a logarithmic derivative is available without selecting a global branch of logarithm.

### 3.3 Logarithmic derivatives

For $\Re(s)>1$,

$$
\log\zeta_K(s)
=\sum_{\mathfrak p}\sum_{m\geq1}
\frac{(N\mathfrak p)^{-ms}}m.
$$

Normal convergence follows from the preceding comparison. Differentiating gives

$$
\boxed{
-\frac{\zeta_K'}{\zeta_K}(s)
=\sum_{\mathfrak p}\sum_{m\geq1}
\frac{\log N\mathfrak p}{(N\mathfrak p)^{ms}}.}
$$

For $\sigma\geq1+\varepsilon$, the differentiated series converges normally because $\log q\ll_\varepsilon q^{\varepsilon/2}$ and the remaining exponent is still greater than one. This is the precise half-plane in which the prime-power series may be inserted into a contour integral.

### 3.4 Prime powers and positivity

All coefficients on the right are positive. If $F\geq0$, a term weighted by

$$
F(m\log N\mathfrak p)
$$

is nonnegative. Known prime-ideal data can therefore strengthen a discriminant lower bound, while discarding the whole prime sum gives a valid universal estimate. This direction is crucial: inventing degree-one prime ideals would produce a false lower bound, but omitting genuine prime ideals only weakens a true one.

Two examples fix the meaning of the coefficients. For $K=\mathbf Q$, the prime ideals are $(p)$ and the logarithmic derivative is

$$
-\frac{\zeta'}\zeta(s)=\sum_p\sum_{m\geq1}\frac{\log p}{p^{ms}}.
$$

For $K=\mathbf Q(i)$, a rational prime $p\equiv1\pmod4$ produces two ideals of norm $p$, a prime $p\equiv3\pmod4$ produces one ideal of norm $p^2$, and $2$ produces one ramified ideal of norm $2$. Their first-power contributions are therefore respectively

$$
2\frac{\log p}{p^s},
\qquad
2\frac{\log p}{p^{2s}},
\qquad
\frac{\log2}{2^s}.
$$

The middle coefficient is $\log(p^2)=2\log p$, not $\log p$. This is why residue degrees enter (12.2), while ramification indices do not count extra Euler factors.

The support of $F$ later turns the infinite prime series into a finite ledger. If $F$ is supported in $[-T,T]$, then only $m\log N\mathfrak p\leq T$ occurs. Thus the analytic formula never asks for an uncontrolled rearrangement at the line $\Re(s)=1/2$: the Euler expansion is made where it converges absolutely, and Laplace inversion inserts a finite-support weight only afterward.

## 4. Completion and the functional equation

### 4.1 Archimedean local factors

For $\operatorname{Re}(s)>0$, the following improper integrals converge and give the real and
complex Mellin transforms of the Gaussian:

$$
\int_{-\infty}^{\infty}e^{-\pi x^2}|x|^s\,\frac{dx}{|x|}
=\pi^{-s/2}\Gamma\left(\frac s2\right),
$$

and, with angular measure normalized in the indicated way,

$$
\int_{\mathbf C}e^{-2\pi|z|^2}|z|^{2s}\,
\frac{dx\,dy}{\pi|z|^2}
=(2\pi)^{-s}\Gamma(s).
$$

This leads to

$$
\Gamma_{\mathbf R}(s)=\pi^{-s/2}\Gamma(s/2),
\qquad
\Gamma_{\mathbf C}(s)=(2\pi)^{-s}\Gamma(s).
$$

The completed Dedekind zeta function is

$$
\boxed{
\Lambda_K(s)=D_K^{s/2}
\Gamma_{\mathbf R}(s)^{r_1}
\Gamma_{\mathbf C}(s)^{r_2}
\zeta_K(s).}
$$

The powers of $2$ and $\pi$ are fixed here once and for all. Moving them between $D_K^{s/2}$ and the gamma factors without changing the later constants would be an error.

### 4.2 Theta kernels and dual lattices

We now prove the continuation and symmetry rather than treating them as black boxes. The Fourier normalization must be chosen with care. On

$$
K_{\mathbf R}\simeq\mathbf R^{r_1}\times\mathbf C^{r_2}
$$

use the positive pairing

$$
\langle x,y\rangle
=\sum_{v\text{ real}}x_vy_v
+2\sum_{v\text{ complex}}\Re(x_v\overline{y_v}).
$$

For this Fourier calculation, give each complex coordinate twice ordinary Lebesgue measure. This is the self-dual measure for the trace character, and the covolume of a fractional ideal $\mathfrak a$ becomes

$$
\Delta_{\mathfrak a}=\sqrt{D_K}\,N(\mathfrak a).
$$

The ordinary-measure covolume $2^{-r_2}\sqrt{D_K}N(\mathfrak a)$ used in Chapter 2 has not changed; the factor $2^{r_2}$ here comes solely from changing to self-dual measure. The coordinate dual of $\mathfrak a$ is the coordinatewise conjugate of

$$
\mathfrak a^*=\mathfrak d_K^{-1}\mathfrak a^{-1}.
$$

Coordinatewise conjugation is an isometry, so it may be suppressed in the theta notation.

Normalize the ideal lattice to covolume one:

$$
L_{\mathfrak a}=\Delta_{\mathfrak a}^{-1/n}\mathfrak a.
$$

Its dual is, up to the preceding isometry, $L_{\mathfrak a^*}$. Indeed,

$$
N(\mathfrak a^*)=D_K^{-1}N(\mathfrak a)^{-1},
\qquad
\Delta_{\mathfrak a^*}=\Delta_{\mathfrak a}^{-1}.
$$

Let $Y$ be the group of positive diagonal archimedean scalings of determinant one:

$$
Y=\left\{(y_v):
\prod_{v\text{ real}}y_v
\prod_{v\text{ complex}}y_v^2=1\right\}.
$$

Dirichlet's unit theorem says that the logarithmic image of the units modulo roots of unity is a full lattice in $\log Y$. Fix a measurable fundamental parallelepiped $P$ and normalize Haar measure by $\operatorname{vol}(P)=1$.

For $y\in Y$ and $t>0$, set

$$
\Theta_{\mathfrak a}(t,y)
=\sum_{x\in L_{\mathfrak a}}
\exp\left(-\pi\left\|t^{1/n}yx\right\|^2\right).
$$

Gaussian decay makes the series and all its $t$-derivatives locally uniform. For completeness, the lattice form of Poisson summation used here follows from the one-dimensional Schwartz formula: choose a real basis carrying $\mathbf Z^n$ to the lattice, apply the one-dimensional identity successively in the $n$ coordinates, and change variables in the Fourier integral. The determinant of the basis produces the covolume, and the transpose inverse produces the dual lattice. Since the determinant of $t^{1/n}y$ is $t$, applying that identity to the self-dual Gaussian and to the covolume-one lattice above gives

$$
\Theta_{\mathfrak a}(t,y)
=t^{-1}\Theta_{\mathfrak a^*}(t^{-1},y^{-1}).
\tag{4.1}
$$

This choice of radial parameter is essential: $t$ is the determinant scale, not the square of a common coordinate scale. It is what makes the Mellin exponent independent of the degree.

We record the convergence needed to integrate the series. The bounded parallelepiped $P$, or
equivalently its compact closure, has all singular values bounded above and below in $Y$. If
$m_{\mathfrak a}$ is the length of a shortest nonzero vector of $L_{\mathfrak a}$, there are
constants $c,C>0$ such that, uniformly for $y\in P$ and $t\geq1$,

$$
0\leq\Theta_{\mathfrak a}(t,y)-1
\leq C\exp(-ct^{2/n}).
$$

One way to obtain the displayed bound is to count lattice points in successive unit shells, use $\#(L_{\mathfrak a}\cap B_R)=O_{\mathfrak a}((R+1)^n)$, and sum the resulting Gaussian tail. The same argument, with an additional polynomial in $t^{1/n}\lVert x\rVert$, treats every $t$-derivative. On a compact $t$-interval it instead gives a normally convergent lattice series. Consequently every use of Fubini below has an explicit locally integrable majorant.

To connect (4.1) with ideals, integrate over $P$. Multiplication by a unit carries $L_{\mathfrak a}$ to itself, and its archimedean absolute values translate $\log y$ by the unit lattice. Thus the summand attached to $x_0\in\mathfrak a\setminus\{0\}$ descends to the quotient by the free part of $\mathcal O_K^\times$. Its orbit corresponds to the integral ideal $x_0\mathfrak a^{-1}$ in the inverse ideal class; every such ideal occurs, and the only remaining multiplicity is the common finite number of roots of unity. The normalized archimedean product of that vector is

$$
D_K^{-1/2}N(x_0\mathfrak a^{-1}).
$$

There is no hidden ideal-dependent stabilizer in this count. If $ux_0=x_0$ for a unit $u$ and
$x_0\ne0$, then $u=1$. Choose a free subgroup $U_0\subset\mathcal O_K^\times$ mapping
isomorphically onto the logarithmic unit lattice, and write
$\mathcal O_K^\times=\mu(K)U_0$. The generators of a fixed principal ideal then split into
exactly $|\mu(K)|$ distinct $U_0$-orbits. Elements of $\mu(K)$ fix the logarithmic scaling
variable, not the vector, which is why their number is a common multiplicity rather than a
stabilizer order to be divided out.

Here is the measure calculation behind the unfolding. Give a real place weight $d_v=1$ and a
complex place weight $d_v=2$. First decompose independent positive scaling factors $q_v$ by

$$
t=\prod_v q_v^{d_v},
\qquad y_v=q_vt^{-1/n}.
$$

Then $y\in Y$, and logarithmic coordinates split $\prod_vdq_v/q_v$ as a constant multiple of
$dt/t$ times Haar measure on $Y$. For a fixed nonzero $\ell\in L_{\mathfrak a}$, put
$r_v=q_v|\ell_v|$. Every embedding of the nonzero algebraic number underlying $\ell$ is nonzero,
so this is a valid change of variables, and

$$
t^s
=\left(\prod_v|\ell_v|^{d_v}\right)^{-s}
\prod_v r_v^{d_vs}.
$$

The real radial integral is $\frac12\Gamma_{\mathbf R}(s)$ and the complex radial integral is
$\frac12\Gamma_{\mathbf C}(s)$; the missing sign and angular factors, the logarithmic Jacobian,
the volume chosen for the unit parallelepiped, and $|\mu(K)|$ are all absorbed into one positive
constant. They are independent of $s$ and, because every $L_{\mathfrak a}$ was normalized to
covolume one, independent of the ideal class. This proves rather than assumes the two local gamma
factors in the unfolding.

For real $s=\sigma>1$ all unfolded summands are nonnegative, so Tonelli applies. For complex
$s$ with the same real part, the absolute value is bounded by the $\sigma$-integrand. The
unfolded sum is the partial zeta series, which converges absolutely by §3.1. This proves both
absolute convergence and the interchange of the lattice sum, the $P$-integral, and the
$t$-integral. We therefore obtain, initially for $\Re(s)>1$,

$$
\int_0^\infty\int_P
\bigl(\Theta_{\mathfrak a}(t,y)-1\bigr)
t^s\,d^\times y\,\frac{dt}{t}
=c_KD_K^{s/2}
\Gamma_{\mathbf R}(s)^{r_1}
\Gamma_{\mathbf C}(s)^{r_2}
\zeta_{[\mathfrak a]^{-1}}(s).
\tag{4.2}
$$

Here $c_K>0$ depends only on the chosen Haar normalization and the number of roots of unity, not on $s$ or the ideal class. Formula (4.2) is now dimensionally exact: the determinant scale contributes $t^s$, normalization of the lattice contributes $D_K^{s/2}$, and each orbit contributes precisely $(N\mathfrak b)^{-s}$.

### 4.3 Continuation and functional equation

Write the left side of (4.2) as $I_{\mathfrak a}(s)$ and split its $t$-integral at $1$. On $(0,1)$ apply (4.1) and substitute $t\mapsto1/t$. Inversion carries $P$ to another unit fundamental parallelepiped, over which the integral of the unit-invariant theta kernel is the same. One obtains

$$
\begin{aligned}
I_{\mathfrak a}(s)={}&
\int_1^\infty\int_P
\bigl(\Theta_{\mathfrak a}(t,y)-1\bigr)t^s
\,d^\times y\,\frac{dt}{t}\notag\\
&+\int_1^\infty\int_P
\bigl(\Theta_{\mathfrak a^*}(t,y)-1\bigr)t^{1-s}
\,d^\times y\,\frac{dt}{t}
+\frac1{s-1}-\frac1s.
\tag{4.3}
\end{aligned}
$$

The uniform estimate preceding (4.2) bounds either integrand on a compact $s$-set by
$C_K(1+t^{R})e^{-ct^{2/n}}/t$ for a suitable $R$. This is integrable on $[1,\infty)$, and the
same is true after any number of $s$-derivatives, which merely insert powers of $\log t$.
Dominated differentiation therefore proves that the two integrals on the right are entire in
$s$. The rational term is the zero-vector contribution:

$$
\int_0^1(t^{-1}-1)t^s\,\frac{dt}{t}
=\frac1{s-1}-\frac1s.
$$

Thus each completed partial zeta has meromorphic continuation with simple poles only at $0$ and $1$, and (4.3) is invariant under simultaneously replacing $(\mathfrak a,s)$ by $(\mathfrak a^*,1-s)$. Duality permutes the finite ideal class group. Summing over its classes proves:

**Theorem 4.1 (Dedekind functional equation).** The function $\Lambda_K(s)$ continues meromorphically to $\mathbf C$, has simple poles at $0$ and $1$, and satisfies

$$
\boxed{\Lambda_K(s)=\Lambda_K(1-s).}
$$

The residues are opposite under this symmetry. Their exact positive magnitude is immaterial for logarithmic derivatives, but positivity of the residue at $1$ also follows from the positive Dirichlet series and (4.2).

The case $K=\mathbf Q$ is a useful model for the construction. There is one ideal class and the unit logarithm space is zero-dimensional. If the traditional parameter $u=t^2$ is used, the theta kernel becomes

$$
\theta(u)=\sum_{m\in\mathbf Z}e^{-\pi um^2}.
$$

Poisson summation reads $\theta(u)=u^{-1/2}\theta(1/u)$. One-half of the Mellin transform of $\theta(u)-1$ against $u^{s/2}\,du/u$ gives

$$
\pi^{-s/2}\Gamma(s/2)\zeta(s),
$$

and splitting at $1$ gives its symmetry under $s\mapsto1-s$. The number-field argument is the same mechanism with three additions: ideal classes replace positive integers, the trace-dual lattice inserts the different, and norm-one archimedean scalings account for units. These additions complicate the bookkeeping but do not alter the source of the functional equation.

It is also worth seeing why the discriminant has exponent $s/2$. Before covolume normalization, Poisson summation contributes the inverse covolume $D_K^{-1/2}$ when the lattice is inverted. Normalizing to covolume one transfers that factor into the archimedean product of each orbit, where Mellin transformation produces $D_K^{s/2}$. Under duality it becomes $D_K^{(1-s)/2}$. No other exponent is compatible with the symmetry. In this sense the discriminant is forced by Fourier duality.

### 4.4 Poles, zeros, and growth

Define

$$
\xi_K(s)=\frac12s(s-1)\Lambda_K(s).
$$

The preceding integral representation shows that $\xi_K$ is entire. It also gives the growth
estimate used later. If $|s|\leq R$, the estimate before (4.2) bounds the integral over
$t\geq1$ by a constant times

$$
\int_1^\infty e^{-ct^{2/n}}t^R\,\frac{dt}{t}
\leq C_K^{R+1}\Gamma\left(\frac{nR}{2}+1\right).
$$

The same estimate applies to the dual integral in (4.3), and multiplication by $s(s-1)$
removes its rational term. We need only a crude real gamma bound, which follows directly from
the defining integral. For $x\geq1$, split

$$
\Gamma(x+1)=\int_0^{2x}e^{-t}t^x\,dt+\int_{2x}^{\infty}e^{-t}t^x\,dt.
$$

The first term is at most $2x(2x)^x$. In the second write $e^{-t}=e^{-t/2}e^{-t/2}$;
the function $t^xe^{-t/2}$ is decreasing for $t\geq2x$, so that term is at most
$2(2x)^xe^{-x}$. Consequently $\log\Gamma(x+1)=O(x\log(x+2))$. Applied with
$x=nR/2$, this gives

$$
\log\max_{|s|\leq R}|\xi_K(s)|=O_K(R\log(R+3)).
\tag{4.4a}
$$

This is the growth bound needed below; no matching lower-order assertion is required. The
symmetries are

$$
\xi_K(s)=\xi_K(1-s),
\qquad
\xi_K(\overline s)=\overline{\xi_K(s)}.
$$

Its zeros lie in the closed critical strip $0\leq\Re(s)\leq1$. Indeed, the Euler product has no zeros for $\Re(s)>1$, and symmetry excludes $\Re(s)<0$ after the trivial gamma cancellations are accounted for. Proving that no zero lies on the two boundary lines is a separate zero-free-line theorem and is unnecessary here; the positivity argument in Chapter 7 includes the endpoints. The zeros of $\xi_K$, with multiplicity, are the nontrivial zeros used below.

Away from the residual simple pole of $\Lambda_K$ at $s=0$, the gamma poles are canceled by the trivial zeros of $\zeta_K$; the other simple pole is at $s=1$. It is safer in the explicit formula to retain the aggregate trivial-zero contribution inside the archimedean integrals than to enumerate it. The factors $s(s-1)$ remove the two poles of $\Lambda_K$ and create the finite-degree pole term seen later.

We now isolate the exact entire-function consequence used in the contour shift.

**Lemma 4.2 (zeros and logarithmic derivative).** Uniformly for $T\geq2$,

$$
N_K(T+1)-N_K(T)\ll \log D_K+n\log(T+3),
\tag{4.4}
$$

where $N_K(T)$ counts zeros with $|\Im\rho|\leq T$. Moreover, away from zeros,

$$
\frac{\xi_K'}{\xi_K}(s)
=b_K+\sum_\rho\left(\frac1{s-\rho}+\frac1\rho\right),
\tag{4.4b}
$$

with zeros repeated according to multiplicity and the sum taken in symmetric expanding discs.
It converges normally on compact sets avoiding the zeros.

**Proof.** We first prove the factorization rather than import it. Jensen's formula and (4.4a)
give

$$
\#\{\rho:|\rho|\leq R\}=O_K(R\log(R+3)).
\tag{4.4c}
$$

Summation over dyadic annuli therefore shows $\sum_{\rho\ne0}|\rho|^{-2}<\infty$.
Hence the products of the elementary factors

$$
E_1(z/\rho)=\left(1-\frac z\rho\right)e^{z/\rho}
$$

converge uniformly on every compact set: outside a fixed finite set of zeros,
$|\log E_1(z/\rho)|\leq C|z/\rho|^2$. Their limit $P(z)$ is entire and has exactly the
nonzero zeros of $\xi_K$, with multiplicity. Factor off the zero at the origin, if present, and
put $h=\xi_K/(z^mP)$. Removable-singularity division makes $h$ entire and zero-free.

Because the plane is simply connected, integrating $h'/h$ from $0$ to $z$ gives an entire
function $g$ with $h=e^g$. We claim that $g$ is affine. Estimate the canonical product by splitting
its zeros at $2R$ and using (4.4c) on dyadic annuli; for every $\varepsilon>0$ this gives

$$
\log\max_{|z|\leq R}|P(z)|=O_{K,\varepsilon}(R^{1+\varepsilon}).
$$

Here is the minimum-modulus step needed for the quotient. In the interval $[2R,3R]$, remove an
interval of radius $R^{-2}$ about the modulus of every zero in $|\rho|\leq4R$. By (4.4c) the
total removed length is $O_K(\log R/R)$, so some radius $r_R\in[2R,3R]$ remains. On
$|z|=r_R$ every nearby elementary factor is at least polynomially far from zero. Splitting again
into dyadic annuli and using $|\log E_1(w)|\ll|w|^2$ for $|w|\leq1/2$ gives the two-sided estimate

$$
|\log|P(z)||=O_{K,\varepsilon}(R^{1+\varepsilon})
\qquad(|z|=r_R).
$$

Together with (4.4a), this bounds $\Re g=\log|\xi_K|-m\log|z|-\log|P|$ from above on that
circle. The maximum principle for the harmonic function $\Re g$ then gives
$\max_{|z|\leq R}\Re g(z)=O_{K,\varepsilon}(R^{1+\varepsilon})$. Borel--Carathéodory on the
concentric discs of radii $R$ and $2R$ turns this into
$\max_{|z|\leq R}|g(z)-g(0)|=O_{K,\varepsilon}(R^{1+\varepsilon})$. Cauchy's estimate for the
second derivative at any fixed center is then

$$
|g''(z_0)|\ll_{z_0,K,\varepsilon}R^{-1+\varepsilon}.
$$

Taking $0<\varepsilon<1$ and letting $R\to\infty$ gives $g''=0$. Thus $g(z)=a_K+b_Kz$ and we
have proved, internally,

$$
\xi_K(s)=s^m e^{a_K+b_Ks}\prod_{\rho\ne0}
\left(1-\frac{s}{\rho}\right)e^{s/\rho}.
$$

Logarithmic differentiation of the normally convergent product on compacta gives (4.4b), with
$m/s$ included when $m>0$.

For the sharper fixed-height count, first take $T\geq6$ and center Jensen's formula at
$s_T=2+iT$. We record the strip bound that will control a fixed disc about this point. The gamma
comparison needed for it requires no asymptotic formula. Euler's product for $\Gamma$ gives, away
from its poles,

$$
\frac{\Gamma'}{\Gamma}(z)
=-\gamma+\sum_{k\geq0}
\left(\frac1{k+1}-\frac1{k+z}\right).
\tag{4.4d}
$$

After using $\Gamma(z+1)=z\Gamma(z)$ a fixed number of times, all arguments to be compared have
real part at least one. Split the series at $k\leq2(|\Im z|+3)$. The initial part is
$O(\log(|\Im z|+3))$ by comparison with the harmonic series, and pairing the two fractions makes
the tail $O(1)$. Integrating (4.4d) along a path of bounded length consequently gives

$$
\log\left|\frac{\Gamma(z+u)}{\Gamma(z+v)}\right|
=O_{u,v}(\log(|\Im z|+3))
\tag{4.4e}
$$

when $u,v$ range over a fixed compact set and the quotient is read after the necessary recurrence
shifts, uniformly for $|\Im z|\geq3$. The upper bounds obtained from this estimate extend over a
reciprocal gamma zero by continuity.

Put $Z_K(s)=(s-1)\zeta_K(s)$. The continuation already proved shows that $Z_K$ is entire: away
from $s=1$, divide $\Lambda_K$ by the gamma factors, whose reciprocals are entire; at $s=0$ their
zero cancels the simple pole of $\Lambda_K$, and the factor $s-1$ removes the remaining pole at
$s=1$. On $\Re(s)=2$, the Euler product gives

$$
|Z_K(2+it)|\leq |1+it|\,\zeta(2)^n.
$$

On $\Re(s)=-1$, the functional equation expresses $\zeta_K(-1+it)$ in terms of
$\zeta_K(2-it)$, a factor $D_K^{3/2}$, and quotients of gamma factors whose arguments differ by
fixed real shifts. Formula (4.4e), the recurrence relation, and
$|\zeta_K(2-it)|\leq\zeta(2)^n$ therefore give absolute constants $C_0,C_1$ such that

$$
|Z_K(-1+it)|
\leq D_K^{3/2}C_0^n(|t|+3)^{C_1n+C_1}.
\tag{4.4f}
$$

Choose an integer $M\geq C_1n+C_1$. Dividing $Z_K(s)$ by $(s+2)^M$ introduces no pole in the
strip $-1\leq\Re(s)\leq2$, and makes the two boundary bounds constant after increasing the
constant by $D_K^{3/2}C_0^n$. The growth estimate (4.4a), Euler's gamma product, and the
recurrence relation give
$\log^+|Z_K(\sigma+it)|=O_K(|t|\log(|t|+3))$ in this strip. This is far smaller than the
double-exponential allowance in the strip Phragmén--Lindelöf principle. Applying that principle
to $Z_K(s)/(s+2)^M$ yields

$$
|Z_K(\sigma+it)|
\leq D_K^{3/2}C_2^n(|t|+3)^{C_3n+C_3}
\qquad(-1\leq\sigma\leq2).
\tag{4.4g}
$$

For $2\leq\sigma\leq5$, the Euler product gives the same shape of bound directly. Formula
(4.4e) compares the gamma factors at any $s$ with $|s-s_T|\leq3$ to those at $s_T$. The powers
of $D_K$, the polynomial $s(s-1)$, (4.4g), and the Euler-product lower bound at the center now
give

$$
\log\frac{\max_{|s-s_T|\leq3}|\xi_K(s)|}{|\xi_K(s_T)|}
\ll \log D_K+n\log(T+3).
\tag{4.4h}
$$

Here the lower bound just used is, at $\sigma=2$,

$$
|\zeta_K(2+iT)|^{-1}
\leq\prod_{\mathfrak p}(1+(N\mathfrak p)^{-2})
\leq\zeta(2)^n.
$$

The disc $|s-s_T|<5/2$ contains the whole rectangle
$0\leq\Re(s)\leq1$, $T\leq\Im(s)\leq T+1$. Jensen's formula with outer radius $3$, (4.4h),
and the nonvanishing of the center consequently give (4.4) for positive ordinates. Conjugation
gives the negative ordinates. For the bounded range of initial heights, cover
$0\leq\Re(s)\leq1$, $|\Im(s)|\leq7$ by finitely many inner discs centered on $\Re(s)=2$, with
slightly larger boundary circles avoiding the discrete gamma poles. The same Euler-product center
bound, (4.4g), gamma recurrence, and Jensen argument give $O(\log D_K+n)$ zeros in this compact
rectangle. Increasing the absolute implied constant therefore covers every $T\geq2$. This proves
the lemma. $\square$

This lemma is enough to justify every symmetric zero limit below. Its proof used only the analytic
tools listed in §1.4 and the displayed canonical-product construction; no arithmetic statement
about prime distribution or zero location was inserted.

### 4.5 Discriminant and analytic conductor

For the Dedekind zeta function, the finite conductor in the completed expression is exactly $D_K$. On a vertical line, the archimedean parameters add the height scale, so a convenient analytic conductor is

$$
Q_K(t)=D_K(|t|+3)^n.
$$

Different conventions replace $3$ by another fixed positive number, but the exponent of $D_K$ and the $n$ archimedean degrees do not change. The bound (4.4) is naturally logarithmic in $Q_K(t)$. The explicit formula isolates $\log D_K$; the height part is spent only in controlling contour edges and zero sums.

## 5. Transforms and admissible test functions

### 5.1 Transform conventions

For an even real function $F$, define

$$
\widehat F(t)=\int_{-\infty}^{\infty}F(x)e^{-itx}\,dx
$$

and its bilateral Laplace transform centered on the critical line by

$$
\Phi_F(s)=\int_{-\infty}^{\infty}
F(x)e^{(s-1/2)x}\,dx.
$$

If $F$ is continuous and compactly supported, $\Phi_F$ is entire. Evenness gives

$$
\Phi_F(s)=\Phi_F(1-s),
$$

and on the critical line

$$
\Phi_F\left(\frac12+it\right)=\widehat F(t).
$$

The sign of $t$ is irrelevant because $F$ is even.

### 5.2 The basic admissible class

Call $F$ **basically admissible** if it is real, even, continuous, compactly supported, piecewise $C^2$, satisfies $F(0)=1$, and has one-sided first derivatives of bounded variation. Require also

$$
\int_0^1\frac{|1-F(x)|}{x}\,dx<\infty.
\tag{5.1}
$$

For a smooth even function, $1-F(x)=O(x^2)$ and (5.1) is automatic. It also admits a corner at the origin with $1-F(x)=O(x)$, which is needed for triangular functions. Two integrations by parts on each smooth piece show

$$
\Phi_F(\sigma+it)=O_F((1+|t|)^{-2})
$$

uniformly for $\sigma$ in a fixed bounded interval. Together with (4.4), this makes the symmetric zero sum convergent.

For lower bounds we additionally require $F(x)\geq0$. Positivity of the zero term requires a further condition, which differs between the unconditional and conditional arguments.

### 5.3 Positive type and autocorrelation

A continuous integrable function $G:\mathbf R\to\mathbf R$ is of **positive type** when its
Fourier transform is real-valued and $\widehat G(t)\geq0$ for every real $t$. Autocorrelation supplies the main examples. If $h\in L^1(\mathbf R)\cap L^2(\mathbf R)$ is real, nonzero, and $\widetilde h(x)=h(-x)$, then

$$
G=h*\widetilde h,
\qquad
\widehat G(t)=|\widehat h(t)|^2\geq0.
$$

Here $G\in L^1(\mathbf R)$, the displayed Fourier identity holds pointwise, and
$G(0)=\|h\|_2^2>0$. After division by $G(0)$, one has $G(0)=1$. Pointwise nonnegativity does not follow from positive type in general, so it will always be imposed separately when the prime sum is discarded.

### 5.4 Two positivity regimes

A basically admissible $F$ is **GRH-admissible** if

$$
F\geq0,
\qquad \widehat F\geq0.
$$

It gives a lower bound under the generalized Riemann hypothesis for $\zeta_K$.

A basically admissible $F$ is **unconditionally admissible** if

$$
F(x)=\frac{G(x)}{\cosh(x/2)},
$$

where $G\geq0$ is even and of positive type. This stronger shape protects zero positivity across the entire critical strip. The division by $\cosh(x/2)$ has a calculable archimedean cost, but it removes every unproved hypothesis about zero locations.

## 6. The Weil--Poitou explicit formula

### 6.1 Statement with every term visible

The functional equation is a symmetry, but a discriminant bound needs an equality of real quantities with controlled signs. The bridge is obtained by pairing the logarithmic derivative of the completed zeta function with $\Phi_F$. The normalization fixed in Chapters 4 and 5 gives the following identity.

**Theorem 6.1 (Weil--Poitou explicit formula).** Let $K$ have degree $n$ and signature $(r_1,r_2)$, and let $F$ be basically admissible. Then

$$
\begin{aligned}
\log D_K={}&n\bigl(\gamma+\log(8\pi)\bigr)+\frac{\pi r_1}{2}
-4\int_0^\infty F(x)\cosh(x/2)\,dx\\
&-n\int_0^\infty\frac{1-F(x)}{2\sinh(x/2)}\,dx
-r_1\int_0^\infty\frac{1-F(x)}{2\cosh(x/2)}\,dx\\
&+\sum_\rho\Phi_F(\rho)
+2\sum_{\mathfrak p}\sum_{m\geq1}
\frac{\log N\mathfrak p}{(N\mathfrak p)^{m/2}}F(m\log N\mathfrak p).
\end{aligned}
\tag{6.1}
$$

The zero sum is the symmetric limit over the nontrivial zeros, counted with multiplicity. The prime sum is finite because $F$ has compact support. All three integrals converge. Near zero, condition (5.1) handles the only singular kernel; at infinity, compact support of $F$ and exponential decay of the kernels suffice.

The rest of this chapter proves (6.1). The detail is important because a wrong factor of two changes the asymptotic threshold, while a wrong sign can turn a valid lower bound into a false one.

### 6.2 The truncated contour identity

Choose $c>1$, and first suppose that $F$ is even and $C^\infty$ with compact support. Let $R_T$ be the rectangle with vertical sides $\Re(s)=c$ and $\Re(s)=1-c$ and horizontal sides at heights $\pm T$. Avoid the ordinates of zeros. Apply the residue theorem to

$$
\frac{\xi_K'}{\xi_K}(s)\Phi_F(s).
$$

The poles of the logarithmic derivative are simple, with residue equal to the multiplicity of the corresponding zero. With the positive orientation of $R_T$, the right vertical side is traversed upward and the left one downward. Thus, after placing both displayed vertical integrals in the upward direction, the residue theorem gives

$$
\frac1{2\pi i}\left(
\int_{c-iT}^{c+iT}\frac{\xi_K'}{\xi_K}(s)\Phi_F(s)\,ds
-\int_{1-c-iT}^{1-c+iT}\frac{\xi_K'}{\xi_K}(s)\Phi_F(s)\,ds
\right)
=\sum_{|\Im\rho|<T}\Phi_F(\rho)+E_T,
\tag{6.2}
$$

where $E_T$ consists of the two horizontal integrals. Lemma 4.2 supplies a sequence of heights
with quantified separation from every zero ordinate. For each sufficiently large integer $j$,
let $Z_j$ be the multiset of ordinates in $[j-1,j+2]$. Its cardinality is
$O(\log D_K+n\log(j+3))$. Choose an integer $d\geq2$. The union of the intervals of radius
$(j+3)^{-d}$ about the members of $Z_j$ has length
$O((\log D_K+n\log(j+3))(j+3)^{-d})<1$ for all sufficiently large $j$. We may therefore choose
$T_j\in[j,j+1]$ outside that union. Zeros with ordinate outside $[j-1,j+2]$ are at distance at
least one. After discarding finitely many $j$, there is consequently a constant $a>0$ such that,
for every nontrivial zero $\rho$,

$$
|T_j-\operatorname{Im}\rho|\geq\frac{a}{(T_j+3)^d}.
$$

To estimate the logarithmic derivative, use (4.4b). First split off $|\rho|\leq T_j/2$.
For these zeros, $|s-\rho|\gg T_j$ on the horizontal edge, and summing
$s/(\rho(s-\rho))$ in unit bands from the origin gives
$O_K(1)+O(\log Q_K(T_j)\log(T_j+3))$. For the remaining zeros, group ordinates by
$k\leq|\operatorname{Im}\rho-T_j|<k+1$. The band $k=0$ contributes at most the inverse
separation times $O(\log Q_K(T_j))$. For $1\leq k\leq2T_j+3$, the canonical summand and (4.4)
give $O(\log Q_K(T_j)/(k+1))$ per band. For larger $k$, the factor
$s/(\rho(s-\rho))$ gives a convergent $O(T_j\log(k+3)/k^2)$ tail. The constant term is harmless.
Hence

$$
\frac{\xi_K'}{\xi_K}(\sigma\mathbin{\pm}iT_j)
=O\left((T_j+3)^d\log(Q_K(T_j))^2\right)
$$

uniformly for $1-c\leq\sigma\leq c$ on the upper edge; the lower edge follows from the
conjugation symmetry of $\xi_K$. The displayed bound is deliberately coarse, but it records the
inverse-polynomial loss and derives the previously implicit logarithmic bound from the canonical
product.

Repeated integration by parts in the definition of $\Phi_F$ gives
$\Phi_F(\sigma+iT)=O_{F,M}(T^{-M})$ for every $M$, uniformly in the same strip. Taking $M>d$
(and increasing it once more if necessary to absorb the logarithmic factor) shows that the
integrand on each horizontal edge tends uniformly to zero. Since those edges have fixed length
$2c-1$, it follows that $E_{T_j}\to0$.

The functional equation and evenness give

$$
\frac{\xi_K'}{\xi_K}(1-s)=-\frac{\xi_K'}{\xi_K}(s),
\qquad \Phi_F(1-s)=\Phi_F(s).
$$

Substituting $s\mapsto1-s$ in the left vertical integral in (6.2) shows that it is the negative of the right vertical integral when both are oriented upward. Their difference is therefore twice the right vertical integral. This is the source of the factor $2$ in the prime-power term.

### 6.3 Prime and discriminant terms

Logarithmically differentiating

$$
\xi_K(s)=\frac12s(s-1)D_K^{s/2}\Gamma_{\mathbf R}(s)^{r_1}\Gamma_{\mathbf C}(s)^{r_2}\zeta_K(s)
$$

separates five contributions. On $\Re(s)=c$, the zeta part may be expanded normally as $\zeta_K'/\zeta_K$, whose prime-power coefficients are negative. For $y>0$, bilateral Laplace inversion in our convention says

$$
\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}\Phi_F(s)e^{-y(s-1/2)}\,ds=F(y).
\tag{6.3}
$$

Putting $y=m\log N\mathfrak p$ and interchanging the series and integral gives a negative
prime-power contribution on the contour side. This interchange is absolute: on $\Re(s)=c$,
$\int_{\mathbf R}|\Phi_F(c+it)|\,dt<\infty$ by repeated integration by parts, while

$$
\sum_{\mathfrak p,m\geq1}
(\log N\mathfrak p)(N\mathfrak p)^{-mc}<\infty
$$

by §3.3. Fubini therefore applies before inversion. The derivative of $D_K^{s/2}$ is
$\frac12\log D_K$; doubling the right vertical line turns it into $\log D_K$. Solving the
contour identity for this discriminant term moves the negative prime contribution to the other
side, giving its positive sign in (6.1).

There is no conditional rearrangement here. If $F$ is supported in $[-T_0,T_0]$, only prime powers with $(N\mathfrak p)^m\leq e^{T_0}$ occur. This also explains why known splitting data can be inserted one prime at a time.

### 6.4 Gamma and pole terms

The archimedean calculation begins with

$$
\psi(z)=\frac{\Gamma'}{\Gamma}(z)=-\gamma+\int_0^\infty\frac{e^{-x}-e^{-zx}}{1-e^{-x}}\,dx,
\qquad \Re(z)>0.
\tag{6.4}
$$

To prove it, expand $(1-e^{-x})^{-1}=\sum_{k\geq0}e^{-kx}$ on $[\varepsilon,\infty)$, integrate termwise, and let $\varepsilon\downarrow0$. The singular terms cancel. The resulting series is $-\gamma+\sum_{k\geq0}(1/(k+1)-1/(k+z))$, the logarithmic derivative of Euler's product for $\Gamma$. Absolute convergence after pairing justifies all passages.

Apply (6.4) to $s/2$ and $s$ on the right line $\Re(s)=c>1$, double the right-line contribution as in §6.2, and use (6.3). Thus the integral representation is invoked only where its hypothesis $\Re(z)>0$ holds. A real place contributes

$$
\gamma+\log(8\pi)+\frac\pi2
-\int_0^\infty\frac{1-F(x)}{2\sinh(x/2)}\,dx
-\int_0^\infty\frac{1-F(x)}{2\cosh(x/2)}\,dx,
$$

while one complex place contributes

$$
2\bigl(\gamma+\log(8\pi)\bigr)
-2\int_0^\infty\frac{1-F(x)}{2\sinh(x/2)}\,dx.
$$

Since $n=r_1+2r_2$, summing gives exactly the first constant and the two archimedean integrals in (6.1). One check is

$$
\int_0^\infty\frac{dx}{2\cosh(x/2)}=\frac\pi2.
$$

Finally, the factors $s(s-1)$ contribute the transforms at $0$ and $1$. Evenness yields

$$
\Phi_F(0)=\Phi_F(1)=2\int_0^\infty F(x)\cosh(x/2)\,dx.
$$

Their sum enters with the opposite sign after solving for $\log D_K$, giving the coefficient $-4$ in (6.1).

### 6.5 Removing the truncations

For smooth $F$, §6.2 supplies rectangles whose horizontal edges vanish. The zero count (4.4) and rapid decay of $\Phi_F$ show absolute convergence in horizontal bands, so the symmetric value is independent of the selected heights.

For basically admissible $F$, choose an even nonnegative $\kappa\in C_c^\infty(\mathbf R)$,
supported in $[-1,1]$, with $\int\kappa=1$, and put
$\kappa_\varepsilon(x)=\varepsilon^{-1}\kappa(x/\varepsilon)$. Then
$(F*\kappa_\varepsilon)(0)\to F(0)=1$, so it is nonzero for all sufficiently small
$\varepsilon$; define

$$
F_\varepsilon=
\frac{F*\kappa_\varepsilon}{(F*\kappa_\varepsilon)(0)}.
$$

These functions are even, smooth, compactly supported, normalized at zero, and converge to $F$
uniformly. Their supports lie in one compact interval. Since the one-sided derivatives of $F$
have bounded variation, convolution does not increase that variation; after the normalizing
denominator, which tends to $1$, two integrations by parts give one common
$O((1+|t|)^{-2})$ transform majorant. In particular, (4.4) and summation by horizontal unit bands
give a summable majorant for the zero sum.

The only weighted integral needing care is the $\sinh$ kernel at zero. The same derivative bound
gives $|1-F_\varepsilon(x)|\leq C|x|$ for $|x|\leq1$, with $C$ independent of small
$\varepsilon$; away from zero, common compact support suffices. Dominated convergence therefore
handles all three archimedean integrals. Finally, a common compact support makes the prime sum
finite, and its individual terms converge. Formula (6.1) follows. This also covers triangles;
their endpoint convention has no effect once the universal prime sum is discarded.

### 6.6 Normalization diagnostics

Four checks expose most errors in (6.1): the prime term and zero term have positive signs; the pole term enters with a minus sign and is therefore a nonpositive finite-degree penalty when $F\geq0$; and the extra real-place constant is $\pi/2$. The factor $8\pi$ is tied to the completion in §4.1. Altering one convention without recomputing the other fails the asymptotic checks in Chapter 9.

There is a fifth, more conceptual check. Set aside the prime and zero sums and let an unconditional triangular support $T=T(n)$ grow with the degree in the regime $T(n)\to\infty$ and $T(n)/n\to0$, as in §9.2. The remaining constant must tend to $\log(4\pi)+\gamma+\alpha$. If it tends instead to $\log(8\pi)+\gamma+\alpha$, the universal $B$-loss was omitted. If the coefficient of $\alpha$ tends to $\pi/2$, the $C$-loss was omitted. This limiting check simultaneously tests the gamma constants, both kernels, and their signature multiplicities.

Contour shifts also have a diagnostic failure mode. Shifting $-\zeta_K'/\zeta_K$ alone would cross the pole of $\zeta_K$ and all trivial zeros individually. Using $\xi_K$ packages the trivial zeros into gamma factors and the poles into $s(s-1)$. The resulting pole integral is not optional: deleting it produces a bound that is implausibly strong in degree one. The completed function is therefore not merely elegant notation; it is the device that makes every residue visible exactly once.

## 7. Positivity of the zero term

### 7.1 The conditional argument

Suppose the generalized Riemann hypothesis holds for $\zeta_K$. Every zero is $\rho=1/2+i\gamma_\rho$, so $\Phi_F(\rho)=\widehat F(\gamma_\rho)$. For a GRH-admissible function this is nonnegative term by term. This is the only conditional step in the GRH bound.

### 7.2 The strip-positive kernel

**Lemma 7.1.** If $|a|<1/2$, then

$$
H_a(x)=\frac{\cosh(ax)}{\cosh(x/2)}
$$

is of positive type, with

$$
\widehat H_a(t)=\frac{4\pi\cos(\pi a)\cosh(\pi t)}{\cosh(2\pi t)+\cos(2\pi a)}\geq0.
\tag{7.1}
$$

At $a=\pm1/2$, one has $H_a=1$, which is of positive type as a tempered measure.

**Proof.** First evaluate the transform of $S(x)=\operatorname{sech}(x/2)$. Integrating $S(z)e^{-itz}$ around a rectangle of height $2\pi i$ uses

$$
S(z+2\pi i)=-S(z)
$$

and the simple pole at $z=\pi i$. The vertical sides vanish by exponential decay, and the residue identity gives

$$
\widehat S(t)=\frac{2\pi}{\cosh(\pi t)}
\qquad(t\in\mathbf R).
$$

Both the integral and the right side are holomorphic for $|\Im t|<1/2$, so the identity theorem extends this formula throughout that strip. Since

$$
H_a(x)=\frac12\left(e^{ax}+e^{-ax}\right)S(x),
$$

we may substitute $t+ia$ and $t-ia$ in the transform of $S$. Hence

$$
\widehat H_a(t)
=\pi\left(
\frac1{\cosh(\pi(t+ia))}
+\frac1{\cosh(\pi(t-ia))}
\right),
$$

which simplifies to (7.1). Its denominator is $2(\sinh^2(\pi t)+\cos^2(\pi a))$, and its numerator is nonnegative. $\square$

Products of positive-type integrable functions are of positive type because the Fourier transform of a product is $(2\pi)^{-1}$ times the convolution of the nonnegative transforms. At the endpoints $a=\pm1/2$, the product used below is simply $G$, so no product with a nonintegrable function is required.

### 7.3 The unconditional argument

Let $F=G/\cosh(x/2)$. Pair a zero $\rho=\beta+i\gamma$ with $1-\overline\rho$. Their contribution is

$$
2\int_{-\infty}^{\infty}G(x)H_{\beta-1/2}(x)\cos(\gamma x)\,dx.
\tag{7.2}
$$

Since $|\beta-1/2|\leq1/2$, Lemma 7.1 and the product rule make this nonnegative. Zeros fixed by the pairing are handled by halving the paired expression. Hence

$$
\boxed{\sum_\rho\Phi_F(\rho)\geq0.}
\tag{7.3}
$$

This proves zero positivity without any hypothesis on zero locations.

### 7.4 What positivity does not permit

Fourier positivity and pointwise positivity are different. The former controls zeros; the latter controls prime powers. Both must be checked. Nor may one invent splitting data: retaining known primes strengthens a bound, but omitting them is the only universally safe operation.

A Gaussian illustrates the distinction between conceptual and numerical suitability. Its Fourier transform is positive and its tails are excellent, but it is not compactly supported. One can still formulate an explicit formula for it after proving enough decay of the prime sum, yet the finite-prime bookkeeping becomes less transparent. The triangle sacrifices smoothness but makes the prime sum finite and its autocorrelation positivity exact. Smoothing in §8.4 recovers the analytic hypotheses without losing the elementary certificate.

Another tempting choice is a broad nonnegative bump chosen solely to make $B(F)$ small. Its transform can oscillate below zero, so zeros on the central line already destroy conditional positivity. Conversely, a positive-type function can dip below zero and make a prime term adverse. Test-function optimization is therefore constrained optimization: small archimedean loss is useful only inside the intersection of the required positivity cones.

## 8. Archimedean losses and test-function design

### 8.1 The three governing integrals

Put

$$
\begin{aligned}
A(F)&=\int_0^\infty F(x)\cosh(x/2)\,dx,\\
B(F)&=\int_0^\infty\frac{1-F(x)}{2\sinh(x/2)}\,dx,\\
C(F)&=\int_0^\infty\frac{1-F(x)}{2\cosh(x/2)}\,dx.
\end{aligned}
\tag{8.1}
$$

Dropping nonnegative zero and prime terms in (6.1) gives

$$
\boxed{\log\operatorname{rd}(K)\geq\gamma+\log(8\pi)+\alpha\frac\pi2-\frac{4A(F)}n-B(F)-\alpha C(F).}
\tag{8.2}
$$

The pole cost disappears with degree; $B$ is the universal archimedean loss; and the signature correction is favorable when $C<\pi/2$.

### 8.2 The triangular autocorrelation

Fix $T>0$, and use the convention

$$
\operatorname{sinc}(u)=
\begin{cases}\sin u/u,&u\ne0,\\1,&u=0.\end{cases}
$$

The normalized autocorrelation of the indicator of $[-T/2,T/2]$ is

$$
G_T(x)=\left(1-\frac{|x|}{T}\right)_+,
\qquad
\widehat G_T(t)=T\operatorname{sinc}(Tt/2)^2\geq0.
\tag{8.3}
$$

Thus $F_T^{\mathrm{un}}=G_T/\cosh(x/2)$ is unconditionally admissible and $F_T^{\mathrm{GRH}}=G_T$ is GRH-admissible. Their pole integrals are

$$
A(F_T^{\mathrm{un}})=\frac T2,
\qquad
A(F_T^{\mathrm{GRH}})=\frac4T\bigl(\cosh(T/2)-1\bigr).
\tag{8.4}
$$

### 8.3 Exact evaluation of the archimedean terms

Write $B_T=B(F_T^{\mathrm{un}})$ and $C_T=C(F_T^{\mathrm{un}})$. Splitting at $T$, expanding $1/\sinh x=2\sum_{k\geq0}e^{-(2k+1)x}$, and integrating termwise gives

$$
\boxed{\begin{aligned}
B_T={}&\log2+\frac{\pi^2}{4T}+\log\coth(T/2)\\
&-\frac2T\sum_{k\geq0}\frac{\bigl(1+(2k+1)T\bigr)e^{-(2k+1)T}}{(2k+1)^2},\\
C_T={}&\frac\pi2-\frac2T\log\cosh(T/2).
\end{aligned}}
\tag{8.5}
$$

The limiting pieces used here are

$$
\int_0^\infty\frac{1-\operatorname{sech}(x/2)}{2\sinh(x/2)}\,dx=\log2,
\qquad
\int_0^\infty\frac{1-\operatorname{sech}(x/2)}{2\cosh(x/2)}\,dx=\frac\pi2-1.
$$

If the series is stopped after $k=m$, where $m\in\mathbf N$ (including $m=0$), its omitted part before multiplication by $2/T$ is at most

$$
\frac{(1+T)e^{-(2m+3)T}}{1-e^{-2T}}.
\tag{8.6}
$$

This follows from $(1+jT)/j^2\leq1+T$ and a geometric series.

### 8.4 Smoothing corners without changing the bound

Choose even nonnegative $\kappa\in C_c^\infty([-1,1])$ with $\int\kappa=1$, set
$\kappa_\varepsilon(x)=\varepsilon^{-1}\kappa(x/\varepsilon)$, and smooth the interval indicator
by $h_\varepsilon=\mathbf 1_{[-T/2,T/2]}*\kappa_\varepsilon$. Its normalized autocorrelation

$$
G_{T,\varepsilon}=
\frac{h_\varepsilon*\widetilde h_\varepsilon}
{(h_\varepsilon*\widetilde h_\varepsilon)(0)}
$$

is smooth, even, nonnegative, compactly supported, and has nonnegative Fourier transform.
Take, for example, $\varepsilon_j=T/(8j)$. Then $h_{\varepsilon_j}$ converges to the interval
indicator in $L^1$ and $L^2$. Young's inequality, first in the $L^2*L^2\to L^\infty$ form and
then in the $L^1*L^1\to L^1$ form, shows that the autocorrelations converge respectively
uniformly and in $L^1$. Their values at zero converge to $T$, so
$G_{T,\varepsilon_j}\to G_T$ in both senses; all supports lie in
$[-T-T/4,T+T/4]$.

There is also a common majorant at the singular endpoint. Indeed,
$0\leq h_\varepsilon\leq1$, its total variation is at most $2$, and, for
$0<\varepsilon\leq T/8$,

$$
(h_\varepsilon*\widetilde h_\varepsilon)(0)\geq T-2\varepsilon\geq\frac{3T}{4},
\qquad
\|h_\varepsilon(\,\cdot+x)-h_\varepsilon\|_1\leq2|x|.
$$

The identity

$$
(h_\varepsilon*\widetilde h_\varepsilon)(0)
-(h_\varepsilon*\widetilde h_\varepsilon)(x)
=\frac12\|h_\varepsilon(\,\cdot+x)-h_\varepsilon\|_2^2
$$

follows by expanding the square and translating one of the two $L^2$ integrals. Moreover,
$|h_\varepsilon(u+x)-h_\varepsilon(u)|\leq1$, so its squared $L^2$ norm is at most its
$L^1$ norm. The preceding bounds therefore give

$$
0\leq1-G_{T,\varepsilon}(x)\leq\frac{4|x|}{3T}.
$$

Put $F_{T,\varepsilon}=G_{T,\varepsilon}/\cosh(x/2)$. On $0<x\leq1$,

$$
0\leq1-F_{T,\varepsilon}(x)
\leq\frac{4x}{3T}+\bigl(1-\operatorname{sech}(x/2)\bigr)
\leq C_Tx,
$$

with $C_T$ independent of $\varepsilon$. Since $2\sinh(x/2)\geq x$, the $B$-integrands are
bounded near zero by $C_T$; on the common compact support they have an ordinary bounded
majorant, and beyond it they equal the fixed integrable kernel $1/(2\sinh(x/2))$. For the
$C$-integral the denominator is bounded away from zero at the origin, and for the $A$-integral
$F_{T,\varepsilon}(x)\cosh(x/2)=G_{T,\varepsilon}(x)$. These are explicit integrable majorants
for all three applications of dominated convergence.

For the limit itself, as $x\downarrow0$,

$$
1-F_T^{\mathrm{un}}(x)=\frac{x}{T}+O(x^2),
$$

so the apparent singularity in $B_T$ is removable. Dominated convergence transfers (8.2) to the triangular limit.

## 9. Universal Odlyzko--Poitou inequalities

### 9.1 One test function, one rigorous bound

**Theorem 9.1.** For every number field $K$ of degree $n$ and real proportion $\alpha$, and every $T>0$,

$$
\boxed{\operatorname{rd}(K)\geq\exp\left(\gamma+\log(8\pi)+\alpha\frac\pi2-\frac{2T}{n}-B_T-\alpha C_T\right).}
\tag{9.1}
$$

**Proof.** Insert $F_T^{\mathrm{un}}$ into (8.2) and use (8.4). $\square$

### 9.2 Unconditional asymptotic constants

As $T\to\infty$, $B_T\to\log2$ and $C_T\to\pi/2-1$. Choose $T(n)\to\infty$ with $T(n)/n\to0$. Then any sequence with degrees tending to infinity and $\liminf\alpha\geq\alpha_0$ satisfies

$$
\boxed{\liminf\operatorname{rd}(K)\geq4\pi e^{\gamma+\alpha_0}.}
\tag{9.2}
$$

The endpoint constants are $4\pi e^\gamma=22.3816160954\ldots$ and $4\pi e^{1+\gamma}=60.8395403238\ldots$.

### 9.3 Bounds under the generalized Riemann hypothesis

Under GRH, use $G_T$. Then $B(G_T),C(G_T)\to0$, while (8.4) shows that the pole penalty vanishes if $T\to\infty$ and $e^{T/2}/(nT)\to0$. Hence

$$
\boxed{\liminf\operatorname{rd}(K)\geq8\pi e^{\gamma+\alpha_0\pi/2}.}
\tag{9.3}
$$

The endpoint constants are $44.7632321909\ldots$ and $215.3325159534\ldots$. A finite-degree GRH claim still requires an evaluated finite test function; the limit alone is not a certificate.

### 9.4 Degree and signature monotonicity

For fixed $F$, the logarithm in (8.2) is $c_F+\alpha(\pi/2-C(F))-4A(F)/n$. It increases with $n$, and with $\alpha$ whenever $C(F)<\pi/2$. Thus one certificate at $(N,\alpha_0)$ covers every $n\geq N$ and $\alpha\geq\alpha_0$.

### 9.5 Threshold and stabilization principles

**Theorem 9.2 (threshold principle).** If $0<U<4\pi e^{\gamma+\alpha_0}$, there is an explicit integer $N(U,\alpha_0)$ such that $\operatorname{rd}(K)\leq U$ and $\alpha(K)\geq\alpha_0$ imply $[K:\mathbf Q]<N(U,\alpha_0)$.

**Proof.** Choose rational $T$ so the infinite-degree part of (9.1) exceeds $\log U$, then choose $N$ so $2T/N$ is smaller than the gap. Formulas (8.5)--(8.6) make both choices effective. $\square$

The GRH version replaces the threshold by $8\pi e^{\gamma+\alpha_0\pi/2}$. Equality with either limit is insufficient.

## 10. Certified numerical evaluation

### 10.1 Rational enclosures for elementary constants

For $|y|<1$,

$$
\log\frac{1+y}{1-y}=2\sum_{j=0}^{M}\frac{y^{2j+1}}{2j+1}+R_M,
\qquad |R_M|\leq\frac{2|y|^{2M+3}}{(2M+3)(1-y^2)}.
\tag{10.1}
$$

This follows by integrating the geometric series for $2/(1-y^2)$. It evaluates $\log2$ with $y=1/3$ and any rational logarithm after power-of-two range reduction.

The alternating arctangent series and

$$
\pi=16\arctan(1/5)-4\arctan(1/239)
\tag{10.2}
$$

give rational bounds for $\pi$. More explicitly,
$4\arctan(1/5)-\arctan(1/239)$ lies in $(0,\pi/2)$ and has tangent $1$, as the addition
formula verifies by rational arithmetic; it is therefore $\pi/4$, which proves (10.2) without
using a decimal value of $\pi$. For every integer $N>0$,
Euler--Maclaurin gives

$$
\gamma=H_N-\log N-\frac1{2N}+\frac1{12N^2}-\frac1{120N^4}+\frac1{252N^6}+R_N,
\qquad |R_N|<\frac1{240N^8}.
\tag{10.3}
$$

The remainder in (10.3) can be checked directly rather than imported as a numerical convention. Let $\widetilde B_j(x)=B_j(x-\lfloor x\rfloor)$ be the periodic Bernoulli polynomial. Starting from the integral comparison for $H_M-H_N$ and integrating by parts repeatedly, using $B_j'=jB_{j-1}$ on each unit interval, gives the displayed coefficients from the Bernoulli numbers

$$
B_2=\frac16,
\qquad B_4=-\frac1{30},
\qquad B_6=\frac1{42}.
$$

After letting $M\to\infty$, the remainder has the form

$$
R_N=\pm\int_N^\infty\frac{\widetilde B_8(x)}{x^9}\,dx.
$$

Here

$$
B_8(x)=x^8-4x^7+\frac{14}{3}x^6
-\frac73x^4+\frac23x^2-\frac1{30}.
$$

Elementary differentiation on $[0,1]$ gives $|B_8(x)|\leq1/30$, with equality only at isolated endpoints. Therefore

$$
|R_N|<\frac1{30}\int_N^\infty x^{-9}\,dx
=\frac1{240N^8},
$$

which proves the directed error bound used below.

For the logarithm in (10.3), use
$\log(10^4)=4\log10=4(\log2+\log5)$, evaluate $\log2$ from (10.1) with $y=1/3$ and $M=20$,
and evaluate $\log(5/4)$ with $y=1/9$ and $M=8$. Thus $\log5=2\log2+\log(5/4)$ is also a
directed rational interval. With $N=10^4$, the harmonic number is a finite rational sum, so
(10.1)--(10.3) yield entirely by rational arithmetic

$$
0.577215664901532<\gamma<0.577215664901533,
\qquad
3.141592653589793<\pi<3.141592653589794.
\tag{10.4}
$$

The other logarithms used by the cutoff ledger have similarly fixed term counts. Use $M=14$
and $y=1/5$ for $\log(3/2)$, so $\log3=\log2+\log(3/2)$. For $\log(8\pi)$, write

$$
\log(8\pi)=5\log2+
\log\left(\frac\pi4\right),
\qquad
y=\frac{\pi-4}{\pi+4},
$$

and use $M=12$ in (10.1), evaluating the monotone rational function $y$ at the directed
$\pi$-endpoints in (10.4). The remainder in every case is the one displayed in (10.1).
Cross-multiplication of the resulting finite sums gives

$$
\begin{aligned}
0.6931471805599453094&<\log2<0.6931471805599453095,\\
1.0986122886681096&<\log3<1.0986122886681098,\\
1.6094379124341003&<\log5<1.6094379124341005,\\
3.224171427529236&<\log(8\pi)<3.224171427529237.
\end{aligned}
\tag{10.4a}
$$

Every endpoint in (10.4)--(10.4a) is a terminating decimal and hence an exact rational number.
The displayed term counts and remainder formulas, rather than a transcendental-function
evaluation, are the provenance of these intervals.

### 10.2 Finite formulas for $B_T$ and $C_T$

For $T>0$, use

$$
\log\coth(T/2)=\log(1+e^{-T})-\log(1-e^{-T}),
$$

$$
\log\cosh(T/2)=\frac T2-\log2+\log(1+e^{-T}).
\tag{10.5}
$$

Bound $e^{-T}$ by the alternating exponential series after halving $T$, then square the interval back; use (10.1) for the logarithms and (8.6) for the series tail. Keeping $k=0,1$ gives

$$
\begin{array}{c|c|c|c}
T&A_T&B_T&C_T\\
\hline
17/5&17/10&1.39921<B_T<1.39923&0.95921<C_T<0.95923\\
9/2&9/4&1.23652<B_T<1.23653&0.87395<C_T<0.87396\\
6&3&1.10355<B_T<1.10356&0.80102<C_T<0.80103.
\end{array}
\tag{10.6}
$$

We now give the finite ledger behind every row of (10.6). This is deliberately more
detailed than the displayed precision: it makes the table reproducible using integer
arithmetic alone. Every terminating decimal below denotes the corresponding exact
rational number, and every comparison can therefore be checked by cross-multiplication.

Write

$$
E_j(x)=\sum_{r=0}^j\frac{(-x)^r}{r!},
\qquad
L_M(y)=2\sum_{r=0}^M\frac{y^{2r+1}}{2r+1}.
$$

Our term-count convention is inclusive: $E_{33}$ retains degrees $0$ through $33$,
and $L_M$ retains $M+1$ terms. Taylor's theorem with its one-sided sign gives

$$
E_{33}(x)<e^{-x}<E_{32}(x),
\qquad
E_{32}(x)-E_{33}(x)=\frac{x^{33}}{33!}.
\tag{10.6a}
$$

Before squaring, the corresponding outward rational exponential boxes are

$$
\begin{array}{c|c|c}
T&e^{-T/2}\text{ box}&\text{reserved width}\\
\hline
17/5&[0.18268352405273465022,0.18268352405273465023]&10^{-20}\\
9/2&[0.10539922456186433678,0.10539922456186433679]&10^{-20}\\
6&[0.04978706836786394297,0.04978706836786394299]&2\cdot10^{-20}.
\end{array}
$$

For the two logarithms needed in (10.5), if $q=e^{-T}$, the reduced arguments are

$$
\log\coth(T/2)=L(q),
\qquad
\log(1+q)=L\left(\frac{q}{2+q}\right),
\tag{10.6b}
$$

where $L(y)=\log((1+y)/(1-y))$. The following are the exact rational argument
boxes obtained by applying (10.6a) at $x=T/2$, squaring, and rounding outward.
Each $q$-box has reserved width $10^{-12}$.

$$
\begin{array}{c|c|c|c}
T&x=T/2&q^-<q<q^+&u^-<q/(2+q)<u^+\\
\hline
17/5&17/10&
\dfrac{834331749}{25000000000},\;
\dfrac{33373269961}{10^{12}}&
\dfrac{834331749}{50834331749},\;
\dfrac{33373269961}{2033373269961}\\[3mm]
9/2&9/4&
\dfrac{5554498269}{500000000000},\;
\dfrac{11108996539}{10^{12}}&
\dfrac{5554498269}{1005554498269},\;
\dfrac{11108996539}{2011108996539}\\[3mm]
6&3&
\dfrac{154922011}{62500000000},\;
\dfrac{2478752177}{10^{12}}&
\dfrac{154922011}{125154922011},\;
\dfrac{2478752177}{2002478752177}.
\end{array}
\tag{10.6c}
$$

In each interval column the first rational is the lower endpoint and the second is
the upper endpoint. For reference, the $q$-boxes are respectively

$$
[0.033373269960,0.033373269961],\quad
[0.011108996538,0.011108996539],\quad
[0.002478752176,0.002478752177].
$$

The term counts and analytic remainder bounds are as follows. In the
$R_{\coth}$ column we use (10.1) with $M=4$ and argument $q^+$; in the
$R_+$ column we use it with $M=3$ and argument $u^+$. The exponential
column is the exact gap in (10.6a), before squaring.

$$
\begin{array}{c|c|c|c|c|c|c}
T&M_{\exp}&E_{32}-E_{33}&M_{\coth}&R_{\coth}&M_+&R_+\\
\hline
17/5&33&<4.636\cdot10^{-30}&4&<1.042\cdot10^{-17}&3&<1.922\cdot10^{-17}\\
9/2&33&<4.824\cdot10^{-26}&4&<5.783\cdot10^{-23}&3&<1.065\cdot10^{-21}\\
6&33&<6.403\cdot10^{-22}&4&<3.947\cdot10^{-30}&3&<1.517\cdot10^{-27}.
\end{array}
\tag{10.6d}
$$

Evaluating those finite sums at the directed endpoints in (10.6c) gives the
following rational elementary-function boxes. Their widths are the reserves carried
through (10.6i); the analytic remainders in (10.6d) are already included.

$$
\begin{array}{c|c|c|c|c}
T&L_{\coth}^-<\log\coth(T/2)<L_{\coth}^+&\text{width}&
L_+^-<\log(1+e^{-T})<L_+^+&\text{width}\\
\hline
17/5&0.0667713367053918<\cdots<0.0667713367073941&2.0023\cdot10^{-12}&
0.0328284704245497<\cdots<0.0328284704255176&9.679\cdot10^{-13}\\
9/2&0.0222189071164060<\cdots<0.0222189071184064&2.0004\cdot10^{-12}&
0.0110477448483541<\cdots<0.0110477448493432&9.891\cdot10^{-13}\\
6&0.0049575145053572<\cdots<0.0049575145073573&2.0001\cdot10^{-12}&
0.0024756851370657<\cdots<0.0024756851380633&9.976\cdot10^{-13}.
\end{array}
\tag{10.6e}
$$

The constants shared by all three rows have their own finite counts. For $\log2$,
take the reduced argument $y=1/3$ and $M=20$ in (10.1). Then

$$
R_{20}<1.595\cdot10^{-22},
\qquad
0.6931471805599453094<\log2<0.6931471805599453095.
\tag{10.6f}
$$

For (10.2), retain $j=0,\ldots,12$ in the alternating series for
$\arctan(1/5)$ and $j=0,\ldots,3$ for $\arctan(1/239)$. The first omitted
terms give the total Machin remainder

$$
\frac{16}{27\cdot5^{27}}+\frac4{9\cdot239^9}
<7.972\cdot10^{-20}.
\tag{10.6g}
$$

The resulting interval is contained in the rational $10^{-15}$-wide $\pi$-box
in (10.4), which is the box carried in the following arithmetic.

For completeness, keeping $k=0,1$ in (8.5) means retaining the rational function

$$
S_1(q)=(1+T)q+\frac{1+3T}{9}q^3.
$$

After the factor $2/T$ is included, the omitted positive tail is bounded, using
$q^+$, by

$$
\rho_T=\frac2T\frac{(1+T)(q^+)^5}{1-(q^+)^2}.
$$

The row-specific rational bounds are

$$
\begin{array}{c|c|c}
T&S_1(q^-)<S_1(q)<S_1(q^+)&\rho_T\\
\hline
17/5&0.1468886442205<S_1(q)<0.1468886442250&<1.072709\cdot10^{-7}\\
9/2&0.0611016897264<S_1(q)<0.0611016897320&<4.136261\cdot10^{-10}\\
6&0.0173512973841<S_1(q)<0.0173512973912&<2.183459\cdot10^{-13}.
\end{array}
\tag{10.6h}
$$

Here is the directed endpoint calculation. Let $\ell_2^\pm$, $p^\pm$,
$L_{\coth}^\pm$, and $L_+^\pm$ denote the rational bounds just recorded, and put

$$
H^-=\frac T2-\ell_2^++L_+^-,
\qquad
H^+=\frac T2-\ell_2^-+L_+^+.
$$

Then exact rational arithmetic gives

$$
\begin{aligned}
B_T^-&=\ell_2^-+\frac{(p^-)^2}{4T}+L_{\coth}^-
-\frac2T S_1(q^+)-\rho_T,\\
B_T^+&=\ell_2^++\frac{(p^+)^2}{4T}+L_{\coth}^+
-\frac2T S_1(q^-),\\
C_T^-&=\frac{p^-}{2}-\frac2T H^+,
\qquad
C_T^+=\frac{p^+}{2}-\frac2T H^-.
\end{aligned}
\tag{10.6i}
$$

The deliberately rounded outward output boxes, together with their reserved widths,
are

$$
\begin{array}{c|c|c|c|c}
T&B_T^-<B_T<B_T^+&B_T^+-B_T^-&C_T^-<C_T<C_T^+&C_T^+-C_T^-\\
\hline
17/5&1.3992195311<B_T<1.3992196384&1.073\cdot10^{-7}&
0.9592190974622<C_T<0.9592190974628&6\cdot10^{-13}\\
9/2&1.2365211363<B_T<1.2365211368&5\cdot10^{-10}&
0.8739516315551<C_T<0.8739516315557&6\cdot10^{-13}\\
6&1.1035544459<B_T<1.1035544460&10^{-10}&
0.8010201586021<C_T<0.8010201586026&5\cdot10^{-13}.
\end{array}
\tag{10.6j}
$$

These tighter intervals imply every entry of (10.6). More importantly, (10.6a)--
(10.6j) specify every reduced argument, retained term count, one-sided analytic
remainder, geometric-series tail, input reserve, and output reserve. No quadrature,
machine transcendental value, or network-fetched constant is part of the certificate.

### 10.3 Tail bounds and interval propagation

In a lower bound, every subtracted quantity uses its upper endpoint and every positive quantity its lower endpoint. Logarithms should be compared before exponentiation. If a decimal exponential is wanted, the positive Taylor series has tail

$$
0\leq e^r-\sum_{j=0}^{M}\frac{r^j}{j!}
\leq\frac{r^{M+1}}{(M+1)!}\frac1{1-r/(M+2)},
\qquad 0\leq r<1.
\tag{10.7}
$$

Both inequalities are strict when $0<r<1$.

Range reduction handles arbitrary $r$.

### 10.4 A reproducible certificate format

A certificate records $T$, $(n,\alpha)$, directed enclosures for all constants, the logarithmic lower endpoint, an upper endpoint for the ceiling logarithm, their positive difference, and the monotonicity extension. This finite ledger exposes every rounding and remainder; it does not rely on quadrature or an unexplained table.

## 11. The finite-degree certificate ledger

Every terminating decimal retained as a certificate endpoint in this chapter is an exact
rational number. Its proof source is either one of the finite sums and directed remainders in
Chapter 10 or one of the explicit integer comparisons below. A decimal followed by $\ldots$ is
only a readability aid and is never an endpoint used to prove a comparison. The geometric rows
can be checked with especially small data: put
$p_0=6283/2000=3.1415$, so (10.4) gives $p_0<\pi$.

### 11.1 The threshold $4$

At very small thresholds, Minkowski is sharper and simpler. At degree $12$ and worst signature,

$$
\begin{aligned}
\frac\pi4M_{12}
&=\frac\pi4\left(\frac{12^{12}}{12!}\right)^{1/6}\\
&>4.0432402329>4.
\end{aligned}
$$

This is certified without its displayed approximation by the exact integer inequality

$$
6283^6\,12^{12}>16^6\,2000^6\,12!,
$$

which is what results after substituting $p_0$ and taking sixth powers. Since $M_n$ increases,

$$
\boxed{\operatorname{rd}(K)<4\Longrightarrow [K:\mathbf Q]\leq11.}
\tag{11.1}
$$

For a totally real field, $M_6>4.0165977004>4$. Here the exact certificate is simply
$6^6>4^3\,6!$, obtained by taking third powers. Thus

$$
\boxed{\operatorname{rd}(K)<4,\ K\text{ totally real}\Longrightarrow [K:\mathbf Q]\leq5.}
\tag{11.2}
$$

These two rows illustrate an important optimization rule: a zeta-function bound need not replace a simpler geometric argument when the latter is stronger.

### 11.2 The threshold $3^{3/2}$

At degree $53$,

$$
\begin{aligned}
\frac\pi4M_{53}
&=\frac\pi4\left(\frac{53^{53}}{53!}\right)^{2/53}\\
&>5.2006733020,
\end{aligned}
$$

whereas

$$
3^{3/2}=5.1961524227\ldots.
$$

Squaring removes the square root, and raising to the $53$rd power reduces the comparison to the
integer certificate

$$
6283^{106}53^{212}>
2000^{106}16^{53}27^{53}(53!)^4.
$$

Thus

$$
\boxed{\operatorname{rd}(K)<3^{3/2}\Longrightarrow [K:\mathbf Q]\leq52.}
\tag{11.3}
$$

This arbitrary-signature cutoff is deliberately stated at the first excluded degree. No asymptotic inference is being substituted for it.

For totally real fields, $M_{13}>5.2610732465>3^{3/2}$; after squaring and taking thirteenth
powers, the exact certificate is

$$
13^{52}>27^{13}(13!)^4.
$$

Therefore

$$
\boxed{\operatorname{rd}(K)<3^{3/2},\ K\text{ totally real}\Longrightarrow [K:\mathbf Q]\leq12.}
\tag{11.4}
$$

### 11.3 The threshold $5^{5/4}$

Minkowski cannot cross this ceiling even in the totally real limit, so the explicit formula is essential. Use $T=9/2$, $n=17$, $\alpha=0$, and $B_T<1.23653$. Directed substitution in (9.1) gives

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)-\frac9{17}-1.23653\\
&>2.03544.
\end{aligned}
$$

Formula (10.4a) gives

$$
\frac54\log5<2.011797390542625625<2.011798.
$$

The strict logarithmic comparison already proves the contradiction; the corresponding decimal
sizes are approximately $7.6556$ and $7.4767$. Monotonicity proves

$$
\boxed{\operatorname{rd}(K)<5^{5/4}\Longrightarrow [K:\mathbf Q]\leq16.}
\tag{11.5}
$$

The gap is large enough that the five-decimal enclosure for $B_T$ is more than sufficient.

### 11.4 The two-prime threshold $3^{3/2}2^{2/3}$

The decisive two-prime ceiling is

$$
U_{2,3}=3^{3/2}2^{2/3}=8.248377821991615758\ldots.
$$

Take $T=6$, $n=21$, and $\alpha=0$. From (10.6), $B_6<1.10356$, so

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)-\frac{12}{21}-1.10356\\
&>2.1263985210021965.
\end{aligned}
\tag{11.6}
$$

Here the last endpoint in (11.6) uses the lower endpoints for $\gamma$ and $\log(8\pi)$ in
(10.4)--(10.4a), together with the exact rational $12/21$ and the upper endpoint for $B_6$.
On the other hand, (10.4a) gives

$$
\log U_{2,3}=\frac32\log3+\frac23\log2<2.110016553375462.
\tag{11.7}
$$

The logarithmic margin is greater than

$$
0.016381967626734.
$$

For readability, the two sides are approximately $8.38461535304387$ and
$8.24837782199162$. The proof uses the directed logarithmic intervals (11.6)--(11.7), not these
rounded exponentials.

Consequently,

$$
\boxed{\operatorname{rd}(K)<3^{3/2}2^{2/3}\Longrightarrow [K:\mathbf Q]\leq20.}
\tag{11.8}
$$

This is a separate certificate from (11.3). Multiplying a ceiling by $2^{2/3}$ invalidates the degree-$53$ Minkowski comparison and requires the degree-$21$ explicit-formula crossing just proved.

Because $3^{3/2}<3^{3/2}2^{2/3}$, the stronger analytic calculation at the larger ceiling also improves the conclusion at the smaller one:

$$
\boxed{\operatorname{rd}(K)<3^{3/2}\Longrightarrow [K:\mathbf Q]\leq20.}
\tag{11.8a}
$$

Thus (11.3) remains an independent geometric certificate, but it is not the strongest final degree bound available in this book.

### 11.5 Totally real certificates

For $5^{5/4}$ take $T=17/5$, $n=7$, and $\alpha=1$. The upper endpoints in (10.6) give

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)+\frac\pi2
-\frac{34}{35}-1.39923-0.95923\\
&>2.04229>\frac54\log5.
\end{aligned}
$$

Therefore

$$
\boxed{\operatorname{rd}(K)<5^{5/4},\ K\text{ totally real}\Longrightarrow [K:\mathbf Q]\leq6.}
\tag{11.9}
$$

Together, (11.2), (11.4), and (11.9) give the totally real caps $5,12,6$ at the three basic ceilings. The apparently nonmonotone sequence reflects changing ceilings, not a failure of degree monotonicity.

### 11.6 A quadratic-base certificate

The base-field factor must be retained. As an illustration, take the ceiling $4\sqrt5$. With $T=6$, $n=24$, and $\alpha=0$,

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)-\frac{12}{24}-1.10356\\
&>2.19782.
\end{aligned}
$$

Also, (10.4a) gives

$$
\log(4\sqrt5)=2\log2+\frac12\log5
<2.191013317336940869<2.19782.
$$

Thus the logarithmic comparison, independently of rounded square-root or exponential values,
gives

$$
\boxed{\operatorname{rd}(K)<4\sqrt5\Longrightarrow [K:\mathbf Q]\leq23.}
\tag{11.10}
$$

If $K$ contains a quadratic base, its absolute degree is even, so it is at most $22$ and its relative degree is at most $11$. Omitting $\sqrt5$ would change the premise rather than sharpen the conclusion.

## 12. Signature grids and optimization

### 12.1 Intermediate signatures

At fixed $T,n$, the logarithmic bound is affine in $\alpha$:

$$
\gamma+\log(8\pi)-\frac{2T}{n}-B_T
+\alpha\left(\frac\pi2-C_T\right).
\tag{12.1}
$$

When $U>0$ and $0<\pi/2-C_T$, one may exclude a degree at ceiling $U$ by solving (12.1) for
$\alpha$. An actual signature satisfies

$$
r_1\in\{n,n-2,n-4,\ldots\},
$$

so the continuous threshold is rounded upward to the least admissible $r_1/n$ strictly greater than it. If no admissible value is strictly greater, that degree is not excluded by this comparison. This produces a finite signature-by-degree grid with no new analytic input.

The signature belongs to the field being bounded. A totally real base may acquire no real embeddings in an extension, so its signature alone cannot justify using $\alpha=1$ upstairs.

### 12.2 Finite rational searches

Optimization can be completely finite. Choose a rational grid of positive supports

$$
\mathcal T=\{a+jh:0\leq j\leq M\}.
$$

Here $a>0$, $h\geq0$, and hence every grid point is positive.

For each $T$, enclose $B_T,C_T$ by Chapter 10, form the directed lower endpoint of (12.1), and retain the largest. The maximum of certified lower endpoints is certified. A theorem needs only one successful rational support; it need not assert that the support is globally optimal.

If optimality matters, differentiate (8.5), enclose the derivative on rational subintervals, and isolate each sign change. This is again finite interval arithmetic. None of the cutoff ledger depends on an unstated optimization.

### 12.3 Prime-ideal information

Suppose the primes above a rational prime $q$ have residue degrees $f_1,\ldots,f_g$. Retaining their contributions improves $\log\operatorname{rd}(K)$ by

$$
\frac2n\sum_{j=1}^g\sum_{m\geq1}
\frac{f_j\log q}{q^{mf_j/2}}F(mf_j\log q),
\tag{12.2}
$$

with only terms inside the support. Ramification indices do not multiply this count: there is one Euler factor per prime ideal. None of the universal ledger rows assumes any such splitting information.

### 12.4 Choosing between geometry and the explicit formula

Minkowski has no pole cost and can be sharper at small degree. The explicit formula has the larger asymptotic constant and wins when the ceiling exceeds the geometric limit. The safe bound is their maximum.

Thus $4$ and $3^{3/2}$ have independent factorial certificates, whereas $5^{5/4}$ and $3^{3/2}2^{2/3}$ require the unconditional explicit formula. The larger two-prime certificate also supplies the strongest final cap recorded here at the smaller $3^{3/2}$ ceiling. The choice is dictated by the numerical comparison, not by a desire to use one method everywhere.

There is also a scale diagnostic. For fixed support, the test-function bound approaches a constant exponentially fast in neither degree nor support: its finite-degree deficit is exactly $2T/n$, whereas its archimedean deficit approaches its limit roughly like $1/T$. Balancing these crude sizes suggests $T$ on the order of $\sqrt n$ for the unconditional triangle. Near a particular ceiling, however, the best rational support can differ substantially because the exponentially small terms in (8.5) and the available logarithmic margin matter. The finite search of §12.2 resolves this without appealing to asymptotic guesswork.

For the GRH triangle, the pole cost grows like $e^{T/2}/(nT)$ while the archimedean losses shrink exponentially or like $1/T$ depending on the kernel. Thus the useful support is logarithmic in $n$. Confusing the two regimes is a reliable way to obtain a poor certificate: the unconditional factor $\operatorname{sech}(x/2)$ completely changes the pole integral.

## 13. Applications to discriminant ceilings

### 13.1 The abstract comparison theorem

**Theorem 13.1.** Let $U>0$, let $N$ be a positive integer, let $0\leq\alpha_0\leq1$, and let $F$ be unconditionally admissible. Alternatively, assume GRH for every field under consideration and let $F$ be GRH-admissible. Suppose in either case that

$$
C(F)\leq\frac\pi2.
$$

If

$$
\gamma+\log(8\pi)+\alpha_0\frac\pi2
-\frac{4A(F)}N-B(F)-\alpha_0C(F)>\log U,
\tag{13.1}
$$

then every $K$ with $\operatorname{rd}(K)\leq U$ and $\alpha(K)\geq\alpha_0$ has degree less than $N$.

**Proof.** Admissibility gives $A(F)>0$, so the right side of (8.2) is nondecreasing with the degree. The displayed hypothesis on $C(F)$ makes its coefficient of $\alpha$ nonnegative. Thus, if $n\geq N$ and $\alpha(K)\geq\alpha_0$, (8.2) is at least the left side of (13.1), contradicting the ceiling. $\square$

If arithmetic gives the strict ceiling $\operatorname{rd}(K)<U$, an analytic lower bound equal to $U$ suffices. The ledger uses positive margins, so it remains valid for weak ceilings.

### 13.2 Nested fields and bounded-root-discriminant towers

**Theorem 13.2 (tower stabilization).** Suppose

$$
K_0\subseteq K_1\subseteq K_2\subseteq\cdots
$$

is nested, $\operatorname{rd}(K_j)\leq U$, and $\alpha(K_j)\geq\alpha_0$ for all $j$. If

$$
U<4\pi e^{\gamma+\alpha_0},
$$

then the tower stabilizes.

**Proof.** The threshold principle bounds all absolute degrees. They are nondecreasing positive integers, hence eventually constant. An inclusion of equal-degree finite fields is equality. $\square$

This is a compatibility warning rather than an existence assertion: if an infinite unramified
tower exists, its root discriminant is constant, so the theorem merely forces that constant to
lie at or above the applicable analytic threshold.

### 13.3 Uniform finite composita

Fix an overfield $\Omega$ of $F$, let $\{L_i\}_{i\in I}$ be intermediate fields of $\Omega/F$, and suppose every finite compositum satisfies one ceiling $U$ and one signature lower bound $\alpha_0$. If $U<4\pi e^{\gamma+\alpha_0}$, their directed compositum is finite.

Indeed, all finite subcomposita have bounded degree. Choose one of maximal degree. Composing it with any other member cannot increase the degree, so it already contains that member. The common compositum is therefore the chosen finite field.

Closure of the ceiling under composita is an arithmetic premise. A generic product of separate discriminant estimates usually grows with the number of fields and does not supply it.

### 13.4 Base fields and auxiliary primes

For $L/F$ finite,

$$
\operatorname{rd}(L)=\operatorname{rd}(F)N_{F/\mathbf Q}(\mathfrak d_{L/F})^{1/[L:\mathbf Q]}.
\tag{13.2}
$$

If normalized local different costs are $b_v$, a typical absolute ceiling is

$$
U=\operatorname{rd}(F)\prod_v(Nv)^{b_v/[F:\mathbf Q]}.
\tag{13.3}
$$

Analysis begins after (13.3) is proved. It does not supply the local costs. Once $U$ is known, Theorem 13.1 gives an absolute cap, and division by $[F:\mathbf Q]$ gives a relative cap.

## 14. Failure diagnostics

### 14.1 A growing ceiling is not uniform

An estimate $\operatorname{rd}(K_m)<c\ell^m$ has no stabilizing force because its right side grows. For an odd prime $\ell$ and an integer $m\geq1$,

$$
[\mathbf Q(\zeta_{\ell^m}):\mathbf Q]=\ell^{m-1}(\ell-1),
\qquad
\operatorname{rd}(\mathbf Q(\zeta_{\ell^m}))=\ell^{m-1/(\ell-1)}.
$$

Both quantities grow. A level-one ceiling cannot be reused at every level.

### 14.2 Bounded step degree is not bounded total degree

Even if $[K_{m+1}:K_m]\leq C$, the total degree can grow like $C^m$, and cumulative ramification
depth in the tower need not be bounded by the degree of each step. The analytic theorem needs a uniform absolute root-discriminant ceiling, not bounded relative group order.

### 14.3 Signature is not inherited automatically

Adjoining $i$ to a totally real field removes all real embeddings. In a tower the real proportion can decrease. A signature-sensitive threshold is uniform only after a uniform lower bound for $r_1/[K:\mathbf Q]$ is established at every level.

### 14.4 Endpoint and normalization failures

The asymptotic theorem needs $U$ strictly below its limit; equality leaves no room for the pole cost. At finite degree, a weak arithmetic ceiling needs an analytic bound strictly above it unless equality is separately impossible.

Normalization errors have recognizable symptoms: changing Fourier frequency inserts $2\pi$; omitting the complex covolume factor changes $(\pi/4)^{1-\alpha}$; changing gamma factors changes $\log(8\pi)$; and forgetting $s(s-1)$ removes the pole penalty. The diagnostics in §6.6 should be repeated after any convention change.

### 14.5 Analysis controls size, not group shape

Under the strict analytic threshold and the uniform signature hypothesis of Theorem 13.1, a degree cap restricts a Galois group order when the field is Galois, but it does not classify the group, determine reducibility, calculate ray groups, or remove extension classes. Those are separate arithmetic problems. Under the nesting hypothesis of Theorem 13.2, or the common finite-compositum ceiling of §13.3, the corresponding uniform cap yields stabilization or finiteness.

Several examples separate these conclusions. The field $\mathbf Q(i)$ has root discriminant $2$ and degree $2$; the analytic bound does not say its group is trivial. An unramified extension has the same root discriminant as its base; the analytic bound may cap the length of a small-discriminant tower but cannot identify an intermediate class group. A family of pairwise nonnested fields can have bounded degree without forming a tower; bounded degree then gives no stabilization until a common finite-compositum ceiling is proved.

The finite-degree certificates should therefore be read as interfaces. An arithmetic argument supplies a ceiling and, if available, a signature constraint. The analytic ledger returns a degree range. Any subsequent elimination of fields inside that range must use additional information and must not be attributed to the explicit formula. This division of labor prevents numerical strength from being mistaken for structural classification.

## 15. The reusable theorem package

### 15.1 Explicit lower-bound theorem

**Theorem 15.1.** Let $K$ have degree $n$ and real proportion $\alpha$. For $T>0$ put

$$
F_T(x)=\frac{(1-|x|/T)_+}{\cosh(x/2)}.
$$

Then, unconditionally,

$$
\operatorname{rd}(K)\geq
\exp\left(\gamma+\log(8\pi)+\alpha\frac\pi2-\frac{2T}{n}-B_T-\alpha C_T\right),
$$

with exact formulas (8.5) and tail (8.6). Under GRH for $\zeta_K$, any basically admissible $F$ with $F\geq0$ and $\widehat F\geq0$ gives (8.2); for $F=G_T$, the pole cost is $16(\cosh(T/2)-1)/(nT)$.

**Proof.** Chapters 4, 6, 7, and 8 prove respectively the functional equation, explicit formula, zero positivity, and archimedean evaluation. Their combination is (8.2), specialized as stated. $\square$

### 15.2 Certified cutoff theorem

**Theorem 15.2.** The following implications hold unconditionally for arbitrary signature:

$$
\begin{array}{c|c}
\text{root-discriminant ceiling}&\text{degree conclusion}\\
\hline
\operatorname{rd}(K)<4&[K:\mathbf Q]\leq11\\
\operatorname{rd}(K)<3^{3/2}&[K:\mathbf Q]\leq20\\
\operatorname{rd}(K)<5^{5/4}&[K:\mathbf Q]\leq16\\
\operatorname{rd}(K)<3^{3/2}2^{2/3}&[K:\mathbf Q]\leq20.
\end{array}
\tag{15.1}
$$

For totally real $K$, the first three caps improve to $5,12,6$.

**Proof.** The first row is §11.1. Section 11.2 gives the independent Minkowski cap $52$ at $3^{3/2}$, while (11.8a) improves it to $20$ using the larger-ceiling calculation of §11.4. The remaining arbitrary-signature rows are §§11.3--11.4, and the totally real refinements are §§11.1--11.2 and §11.5. Each crossing has a certified positive margin, and monotonicity extends it to all larger degrees. $\square$

### 15.3 Unconditional and conditional ledgers

The asymptotic thresholds are

$$
\begin{array}{c|c|c}
&\alpha=0&\alpha=1\\
\hline
\text{unconditional}&4\pi e^\gamma&4\pi e^{1+\gamma}\\
\text{under GRH}&8\pi e^\gamma&8\pi e^{\gamma+\pi/2}.
\end{array}
\tag{15.2}
$$

For intermediate $\alpha_0$, use $\gamma+\alpha_0$ unconditionally and $\gamma+\alpha_0\pi/2$ under GRH. A ceiling strictly below the relevant value gives an effective degree bound. A finite-degree cap still requires an actual test function; the asymptotic row alone supplies none.

## 16. Conclusion

The root discriminant is the scale on which ramification and degree can be compared across fields. Geometry of numbers first constrains it through the covolume of the integer lattice. The completed Dedekind zeta function then reveals more: its Euler product supplies positive prime powers, its gamma factors record signature, its functional equation reflects zeros, and its poles impose the finite-degree cost of a test function.

The explicit formula makes that balance exact. Under GRH, Fourier positivity controls zeros on the central line. Unconditionally, the strip-positive kernel $\cosh(ax)/\cosh(x/2)$ controls symmetric zero pairs throughout the strip. Its exact archimedean cost changes $8\pi e^{\gamma+\alpha\pi/2}$ into $4\pi e^{\gamma+\alpha}$.

Finite support turns asymptotic pressure into reproducible certificates. Exact formulas for $B_T,C_T$, geometric tail bounds, and rational enclosures certify every displayed cutoff. Minkowski independently gives the cap $52$ at $3^{3/2}$, while the stronger explicit-formula calculation at the larger ceiling $3^{3/2}2^{2/3}$ gives cap $20$ and therefore also improves the smaller-ceiling cap to $20$. The threshold $5^{5/4}$ demonstrates the gain beyond Minkowski's reach.

The logical boundary is equally important. A uniform ceiling below the threshold bounds degree; nestedness or uniform closure under finite composita then forces stabilization. A growing ceiling, bounded step degrees, an unverified signature, or a missing base-field factor defeats the argument. Within the stated scope, every contour, sign, archimedean constant, positivity mechanism, numerical remainder, and monotonicity step needed for discriminant bounds is now explicit.
