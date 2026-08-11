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

For a finite extension $L/K$, discriminant transitivity gives

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

Only discriminant bounds are developed here. No distribution theorem for Frobenius classes enters any proof. The foundational tools are real and complex integration, Fourier inversion and Poisson summation for rapidly decreasing functions, the residue theorem, standard gamma-function identities, geometry of numbers, unique factorization of ideals, Dirichlet's unit theorem, and the elementary arithmetic of number-field discriminants. Finiteness of the ideal class group also follows from Theorem 2.1, because only finitely many integral ideals have bounded norm.

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

Letting $T$ decrease to the critical volume and substituting the covolume gives

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

Stirling's formula, with its usual two-sided remainder, gives

$$
\log M_n
=2-\frac{\log(2\pi n)}n-\frac1{6n^2}+O(n^{-4}).
$$

Consequently

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

The real and complex Mellin transforms of the Gaussian are

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

To connect (4.1) with ideals, integrate over $P$. A nonzero vector arising from $x_0\in\mathfrak a$ is counted once modulo the free part of the unit group, with the common roots-of-unity multiplicity absorbed below, and its orbit corresponds to the integral ideal $x_0\mathfrak a^{-1}$ in the inverse ideal class. The normalized archimedean product of that vector is

$$
D_K^{-1/2}N(x_0\mathfrak a^{-1}).
$$

Passing from $(t,y)$ to the independent positive archimedean scales and applying the Mellin integrals of §4.1 therefore gives, initially for $\Re(s)>1$,

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

The two integrals on the right are entire in $s$, because the theta series minus its zero term decays exponentially as $t\to\infty$. The rational term is the zero-vector contribution:

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

The preceding integral representation shows that $\xi_K$ is entire. Repeated integration by parts in the exponentially convergent theta integrals, together with Stirling's estimate for the gamma factors in vertical strips, shows that it has order one. It satisfies

$$
\xi_K(s)=\xi_K(1-s),
\qquad
\xi_K(\overline s)=\overline{\xi_K(s)}.
$$

Its zeros lie in the closed critical strip $0\leq\Re(s)\leq1$. Indeed, the Euler product has no zeros for $\Re(s)>1$, and symmetry excludes $\Re(s)<0$ after the trivial gamma cancellations are accounted for. Proving that no zero lies on the two boundary lines is a separate zero-free-line theorem and is unnecessary here; the positivity argument in Chapter 7 includes the endpoints. The zeros of $\xi_K$, with multiplicity, are the nontrivial zeros used below.

The gamma poles are canceled by the trivial zeros of $\zeta_K$. It is safer in the explicit formula to retain their aggregate contribution inside the archimedean integrals than to enumerate them. The factors $s(s-1)$ remove the two poles of $\Lambda_K$ and create the finite-degree pole term seen later.

The order-one bound also gives a symmetric zero-counting estimate

$$
N_K(T+1)-N_K(T)\ll \log D_K+n\log(T+3),
\tag{4.4}
$$

where $N_K(T)$ counts zeros with $|\Im\rho|\leq T$. To prove (4.4), apply the argument principle to $\xi_K$ on a unit-width rectangle, use Stirling's formula on the gamma factors, and bound $\zeta_K$ on the right by $\zeta(1+1/\log(T+3))^n$; the functional equation controls the left. This estimate is enough to justify every symmetric zero limit below.

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

If $F$ has compact support, $\Phi_F$ is entire. Evenness gives

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

A continuous integrable function $G$ is of **positive type** when $\widehat G(t)\geq0$ for all real $t$. Autocorrelation supplies the main examples. If $h\in L^2(\mathbf R)$ is real and $\widetilde h(x)=h(-x)$, then

$$
G=h*\widetilde h,
\qquad
\widehat G(t)=|\widehat h(t)|^2\geq0.
$$

After division by $G(0)$, one has $G(0)=1$. Pointwise nonnegativity does not follow from positive type in general, so it will always be imposed separately when the prime sum is discarded.

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

where $E_T$ consists of the two horizontal integrals. From the order-one estimate in §4.4, there is a sequence $T_j\to\infty$, avoiding zero ordinates by a fixed inverse-polynomial distance, on which

$$
\frac{\xi_K'}{\xi_K}(\sigma+iT_j)=O\bigl(\log(D_K(T_j+3)^n)^2\bigr)
$$

uniformly for $1-c\leq\sigma\leq c$. Repeated integration by parts in the definition of $\Phi_F$ gives $\Phi_F(\sigma+iT)=O_F(T^{-M})$ for every $M$. Hence $E_{T_j}\to0$.

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

Putting $y=m\log N\mathfrak p$ and interchanging the absolutely convergent series and integral gives a negative prime-power contribution on the contour side. The derivative of $D_K^{s/2}$ is $\frac12\log D_K$; doubling the right vertical line turns it into $\log D_K$. Solving the contour identity for this discriminant term moves the negative prime contribution to the other side, giving its positive sign in (6.1).

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

For basically admissible $F$, smooth by even convolution with a nonnegative compactly supported approximate identity, then correct the value at zero by a factor tending to one. Uniform bounded variation gives a common $O((1+|t|)^{-2})$ transform majorant. Dominated convergence handles the zero sum, (5.1) handles the $\sinh$ kernel at zero, and compact support handles the prime sum. Formula (6.1) follows. This also covers triangles; their endpoint convention has no effect once the universal prime sum is discarded.

### 6.6 Normalization diagnostics

Four checks expose most errors in (6.1): the prime term and zero term have positive signs; the pole term is negative and becomes a finite-degree penalty; and the extra real-place constant is $\pi/2$. The factor $8\pi$ is tied to the completion in §4.1. Altering one convention without recomputing the other fails the asymptotic checks in Chapter 9.

There is a fifth, more conceptual check. Set aside the prime and zero sums and let an unconditional triangular support grow with the degree. The remaining constant must tend to $\log(4\pi)+\gamma+\alpha$. If it tends instead to $\log(8\pi)+\gamma+\alpha$, the universal $B$-loss was omitted. If the coefficient of $\alpha$ tends to $\pi/2$, the $C$-loss was omitted. This limiting check simultaneously tests the gamma constants, both kernels, and their signature multiplicities.

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

The normalized autocorrelation of the indicator of $[-T/2,T/2]$ is

$$
G_T(x)=\left(1-\frac{|x|}{T}\right)_+,
\qquad
\widehat G_T(t)=T\left(\frac{\sin(Tt/2)}{Tt/2}\right)^2\geq0.
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

If the series is stopped after $k=m$, its omitted part before multiplication by $2/T$ is at most

$$
\frac{(1+T)e^{-(2m+3)T}}{1-e^{-2T}}.
\tag{8.6}
$$

This follows from $(1+jT)/j^2\leq1+T$ and a geometric series.

### 8.4 Smoothing corners without changing the bound

Smooth the interval indicator by nonnegative even approximate identities and take normalized autocorrelations. The transforms remain nonnegative and the functions converge in every integral above. Near zero,

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

**Theorem 9.2 (threshold principle).** If $U<4\pi e^{\gamma+\alpha_0}$, there is an explicit integer $N(U,\alpha_0)$ such that $\operatorname{rd}(K)\leq U$ and $\alpha(K)\geq\alpha_0$ imply $[K:\mathbf Q]<N(U,\alpha_0)$.

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

give rational bounds for $\pi$; (10.2) is checked by taking tangents. Euler--Maclaurin gives

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

With $N=10^4$ and (10.1)--(10.2), directed rational arithmetic yields

$$
0.577215664901532<\gamma<0.577215664901533,
\qquad
3.141592653589793<\pi<3.141592653589794.
\tag{10.4}
$$

### 10.2 Finite formulas for $B_T$ and $C_T$

Use

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

The omitted series contribution is at most $(2/T)(1+T)e^{-5T}/(1-e^{-2T})$, below $1.1\cdot10^{-7}$ even in the first row. Twenty terms after range reduction make every Taylor remainder smaller than the unused interval width.

### 10.3 Tail bounds and interval propagation

In a lower bound, every subtracted quantity uses its upper endpoint and every positive quantity its lower endpoint. Logarithms should be compared before exponentiation. If a decimal exponential is wanted, the positive Taylor series has tail

$$
0<e^r-\sum_{j=0}^{M}\frac{r^j}{j!}
<\frac{r^{M+1}}{(M+1)!}\frac1{1-r/(M+2)},
\qquad 0\leq r<1.
\tag{10.7}
$$

Range reduction handles arbitrary $r$.

### 10.4 A reproducible certificate format

A certificate records $T$, $(n,\alpha)$, directed enclosures for all constants, the logarithmic lower endpoint, an upper endpoint for the ceiling logarithm, their positive difference, and the monotonicity extension. This finite ledger exposes every rounding and remainder; it does not rely on quadrature or an unexplained table.

## 11. The finite-degree certificate ledger

### 11.1 The threshold $4$

At very small thresholds, Minkowski is sharper and simpler. At degree $12$ and worst signature,

$$
\frac\pi4M_{12}
=\frac\pi4\left(\frac{12^{12}}{12!}\right)^{1/6}
>4.0432402329>4.
$$

This is certified by exact integer arithmetic, (10.4), and repeated squaring after raising both positive sides to the sixth power. Since $M_n$ increases,

$$
\boxed{\operatorname{rd}(K)<4\Longrightarrow [K:\mathbf Q]\leq11.}
\tag{11.1}
$$

For a totally real field, $M_6>4.0165977004>4$, giving

$$
\boxed{\operatorname{rd}(K)<4,\ K\text{ totally real}\Longrightarrow [K:\mathbf Q]\leq5.}
\tag{11.2}
$$

The second comparison is exact after raising to the third power. These two rows illustrate an important optimization rule: a zeta-function bound need not replace a simpler geometric argument when the latter is stronger.

### 11.2 The threshold $3^{3/2}$

At degree $53$,

$$
\frac\pi4M_{53}
=\frac\pi4\left(\frac{53^{53}}{53!}\right)^{2/53}
>5.2006733020,
$$

whereas

$$
3^{3/2}=5.1961524227\ldots.
$$

Squaring removes the square root, and raising to the $53$rd power reduces the comparison to integers and the rational lower endpoint for $\pi$. Thus

$$
\boxed{\operatorname{rd}(K)<3^{3/2}\Longrightarrow [K:\mathbf Q]\leq52.}
\tag{11.3}
$$

This arbitrary-signature cutoff is deliberately stated at the first excluded degree. No asymptotic inference is being substituted for it.

For totally real fields, $M_{13}>5.2610732465>3^{3/2}$, so

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

Formula (10.1) gives $(5/4)\log5<2.011798$. Hence

$$
\operatorname{rd}(K)>7.6556>5^{5/4}=7.4767439061\ldots,
$$

and monotonicity proves

$$
\boxed{\operatorname{rd}(K)<5^{5/4}\Longrightarrow [K:\mathbf Q]\leq16.}
\tag{11.5}
$$

The gap is large enough that the five-decimal enclosure for $B_T$ is more than sufficient.

### 11.4 The two-prime threshold $3^{3/2}2^{2/3}$

The decisive two-prime ceiling is

$$
U_{2,3}=3^{3/2}2^{2/3}=8.248377821991616\ldots.
$$

Take $T=6$, $n=21$, and $\alpha=0$. From (10.6), $B_6<1.10356$, so

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)-\frac{12}{21}-1.10356\\
&>2.126398521002197.
\end{aligned}
\tag{11.6}
$$

On the other hand, (10.1) applied to $\log2$ and $\log3$ gives

$$
\log U_{2,3}=\frac32\log3+\frac23\log2<2.110016553375462.
\tag{11.7}
$$

The logarithmic margin is greater than

$$
0.016381967626735.
$$

Exponentiating only for readability,

$$
\operatorname{rd}(K)>8.38461535304387
>8.248377821991616=U_{2,3}.
$$

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
\log\operatorname{rd}(K)
>\gamma+\log(8\pi)-\frac{12}{24}-1.10356
>2.19782.
$$

Thus $\operatorname{rd}(K)>9.0053>4\sqrt5$, and

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

To exclude a degree at ceiling $U$, solve (12.1) for $\alpha$. An actual signature satisfies

$$
r_1\in\{n,n-2,n-4,\ldots\},
$$

so the continuous threshold is rounded upward to the next admissible $r_1/n$. This produces a finite signature-by-degree grid with no new analytic input.

The signature belongs to the field being bounded. A totally real base may acquire no real embeddings in an extension, so its signature alone cannot justify using $\alpha=1$ upstairs.

### 12.2 Finite rational searches

Optimization can be completely finite. Choose a rational grid of supports

$$
\mathcal T=\{a+jh:0\leq j\leq M\}.
$$

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

**Theorem 13.1.** Let $U>0$, $0\leq\alpha_0\leq1$, and let $F$ be unconditionally admissible. Alternatively, assume GRH for every field under consideration and let $F$ be GRH-admissible. Suppose in either case that

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

This does not prohibit all infinite towers. An unramified tower has constant root discriminant and can exist above the analytic threshold.

### 13.3 Uniform finite composita

Let $\{L_i\}_{i\in I}$ be extensions of a fixed field, and suppose every finite compositum satisfies one ceiling $U$ and one signature lower bound $\alpha_0$. If $U<4\pi e^{\gamma+\alpha_0}$, their directed compositum is finite.

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

An estimate $\operatorname{rd}(K_m)<c\ell^m$ has no stabilizing force because its right side grows. For odd $\ell$,

$$
[\mathbf Q(\zeta_{\ell^m}):\mathbf Q]=\ell^{m-1}(\ell-1),
\qquad
\operatorname{rd}(\mathbf Q(\zeta_{\ell^m}))=\ell^{m-1/(\ell-1)}.
$$

Both quantities grow. A level-one ceiling cannot be reused at every level.

### 14.2 Bounded step degree is not bounded total degree

Even if $[K_{m+1}:K_m]\leq C$, the total degree can grow like $C^m$. Fixed-degree local extensions can also have arbitrarily deep ramification. The analytic theorem needs a uniform absolute root-discriminant ceiling, not bounded relative group order.

### 14.3 Signature is not inherited automatically

Adjoining $i$ to a totally real field removes all real embeddings. In a tower the real proportion can decrease. A signature-sensitive threshold is uniform only after a uniform lower bound for $r_1/[K:\mathbf Q]$ is established at every level.

### 14.4 Endpoint and normalization failures

The asymptotic theorem needs $U$ strictly below its limit; equality leaves no room for the pole cost. At finite degree, a weak arithmetic ceiling needs an analytic bound strictly above it unless equality is separately impossible.

Normalization errors have recognizable symptoms: changing Fourier frequency inserts $2\pi$; omitting the complex covolume factor changes $(\pi/4)^{1-\alpha}$; changing gamma factors changes $\log(8\pi)$; and forgetting $s(s-1)$ removes the pole penalty. The diagnostics in §6.6 should be repeated after any convention change.

### 14.5 Analysis controls size, not group shape

A degree cap restricts a Galois group order when the field is Galois, but it does not classify the group, determine reducibility, calculate ray groups, or remove extension classes. Those are separate arithmetic problems. The conclusion here is exactly that small root discriminant forces small degree or, under uniform compositum hypotheses, stabilization.

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
