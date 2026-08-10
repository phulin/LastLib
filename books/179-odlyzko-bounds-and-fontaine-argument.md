# Odlyzko Bounds and Fontaine's Argument

## Contents

1. [Discriminant as analytic complexity](#1-discriminant-as-analytic-complexity)
   - [What an analytic lower bound must accomplish](#11-what-an-analytic-lower-bound-must-accomplish)
   - [Absolute and root discriminants](#12-absolute-and-root-discriminants)
   - [The pressure created by towers](#13-the-pressure-created-by-towers)
   - [Signature as visible infinite ramification](#14-signature-as-visible-infinite-ramification)
   - [The two inputs and the logical route](#15-the-two-inputs-and-the-logical-route)
2. [The geometric baseline](#2-the-geometric-baseline)
   - [Minkowski's convex-body theorem](#21-minkowskis-convex-body-theorem)
   - [The ideal-class estimate](#22-the-ideal-class-estimate)
   - [Minkowski's discriminant bound](#23-minkowskis-discriminant-bound)
   - [Root form and finite-degree consequences](#24-root-form-and-finite-degree-consequences)
   - [What geometry alone cannot see](#25-what-geometry-alone-cannot-see)
3. [The zeta function of a number field](#3-the-zeta-function-of-a-number-field)
   - [Why ideals are the correct spectrum](#31-why-ideals-are-the-correct-spectrum)
   - [Euler product and logarithmic derivative](#32-euler-product-and-logarithmic-derivative)
   - [Completion and functional equation](#33-completion-and-functional-equation)
   - [Poles, trivial zeros, and nontrivial zeros](#34-poles-trivial-zeros-and-nontrivial-zeros)
   - [Analytic hypotheses and growth estimates](#35-analytic-hypotheses-and-growth-estimates)
4. [The explicit formula](#4-the-explicit-formula)
   - [From a functional equation to a weighted identity](#41-from-a-functional-equation-to-a-weighted-identity)
   - [Transform conventions and admissibility](#42-transform-conventions-and-admissibility)
   - [The Weil--Poitou identity](#43-the-weil--poitou-identity)
   - [Why every sign matters](#44-why-every-sign-matters)
   - [Discarding positive terms](#45-discarding-positive-terms)
   - [Convergence and passage to nonsmooth kernels](#46-convergence-and-passage-to-nonsmooth-kernels)
5. [Designing test functions](#5-designing-test-functions)
   - [Positive type and autocorrelation](#51-positive-type-and-autocorrelation)
   - [The GRH and unconditional positivity mechanisms](#52-the-grh-and-unconditional-positivity-mechanisms)
   - [A triangular family](#53-a-triangular-family)
   - [Smooth approximations and endpoint control](#54-smooth-approximations-and-endpoint-control)
   - [Prime information as a refinement](#55-prime-information-as-a-refinement)
6. [Odlyzko--Poitou lower bounds](#6-odlyzko--poitou-lower-bounds)
   - [A bound attached to one test function](#61-a-bound-attached-to-one-test-function)
   - [Unconditional asymptotic constants](#62-unconditional-asymptotic-constants)
   - [Conditional asymptotic constants](#63-conditional-asymptotic-constants)
   - [Signature interpolation](#64-signature-interpolation)
   - [What the asymptotic statement really says](#65-what-the-asymptotic-statement-really-says)
7. [Finite-degree bounds without tables](#7-finite-degree-bounds-without-tables)
   - [An explicit optimization algorithm](#71-an-explicit-optimization-algorithm)
   - [Certified evaluation of the integrals](#72-certified-evaluation-of-the-integrals)
   - [The thresholds needed at 2, 3, and 5](#73-the-thresholds-needed-at-2-3-and-5)
   - [The decisive two-prime certificate](#74-the-decisive-two-prime-certificate)
   - [Totally real improvements](#75-totally-real-improvements)
   - [Degree and signature grids](#76-degree-and-signature-grids)
8. [Upper bounds force finite degree](#8-upper-bounds-force-finite-degree)
   - [Monotonicity in degree](#81-monotonicity-in-degree)
   - [The threshold principle](#82-the-threshold-principle)
   - [Nonexistence, bounded degree, and finiteness](#83-nonexistence-bounded-degree-and-finiteness)
9. [Towers and the meaning of a threshold](#9-towers-and-the-meaning-of-a-threshold)
   - [Unramified class-field towers](#91-unramified-class-field-towers)
   - [Tame towers with bounded root discriminant](#92-tame-towers-with-bounded-root-discriminant)
   - [Cyclotomic towers as a warning](#93-cyclotomic-towers-as-a-warning)
   - [The analytic obstruction to a small tower](#94-the-analytic-obstruction-to-a-small-tower)
10. [Finite-flat torsion fields](#10-finite-flat-torsion-fields)
    - [The inherited upper bound](#101-the-inherited-upper-bound)
    - [Bounded degree at one torsion level](#102-bounded-degree-at-one-torsion-level)
    - [Auxiliary ramification](#103-auxiliary-ramification)
    - [Base fields](#104-base-fields)
    - [Why the finite-flat exponent is uniform](#105-why-the-finite-flat-exponent-is-uniform)
    - [The residual three-adic ledger](#106-the-residual-three-adic-ledger)
11. [Fontaine's stabilization mechanism](#11-fontaines-stabilization-mechanism)
    - [The maximal small-ramification compositum](#111-the-maximal-small-ramification-compositum)
    - [Uniform exponent-$\ell$ layers](#112-uniform-exponent-ell-layers)
    - [From bounded degree to stabilization](#113-from-bounded-degree-to-stabilization)
    - [Successive torsion fields](#114-successive-torsion-fields)
    - [The missing group-theoretic bridge](#115-the-missing-group-theoretic-bridge)
    - [Forbidden large torsion fields](#116-forbidden-large-torsion-fields)
12. [Small-prime calculations](#12-small-prime-calculations)
    - [The prime 2](#121-the-prime-2)
    - [The prime 3](#122-the-prime-3)
    - [The prime 5](#123-the-prime-5)
    - [Strict and weak inequalities](#124-strict-and-weak-inequalities)
    - [The prime 3 with tame cubic inertia at 2](#125-the-prime-3-with-tame-cubic-inertia-at-2)
13. [Signature and base-field refinements](#13-signature-and-base-field-refinements)
    - [Totally real fields](#131-totally-real-fields)
    - [Intermediate signatures](#132-intermediate-signatures)
    - [Relative small ramification](#133-relative-small-ramification)
    - [A worked base-field comparison](#134-a-worked-base-field-comparison)
14. [Comparative examples and counterexamples](#14-comparative-examples-and-counterexamples)
    - [Tame-only fields](#141-tame-only-fields)
    - [Cyclotomic fields](#142-cyclotomic-fields)
    - [Finite-flat exponent-$\ell$ families](#143-finite-flat-exponent-ell-families)
    - [Why bounded step degree is not enough](#144-why-bounded-step-degree-is-not-enough)
15. [A theorem package for the next stage](#15-a-theorem-package-for-the-next-stage)
    - [Analytic degree cutoff](#151-analytic-degree-cutoff)
    - [Finite-flat cutoff](#152-finite-flat-cutoff)
    - [Uniform-compositum stabilization](#153-uniform-compositum-stabilization)
    - [What remains to be classified](#154-what-remains-to-be-classified)
16. [Conclusion](#16-conclusion)

## 1. Discriminant as analytic complexity

### 1.1 What an analytic lower bound must accomplish

The preceding discriminant theory starts with local ramification and ends with an upper bound for the absolute root discriminant of a field cut out by a finite action. We now approach the same invariant from the opposite direction. A number field has many embeddings, many ideals, and a zeta function whose zeros are constrained by a functional equation. Those global objects prevent a field of large degree from having an arbitrarily small discriminant.

The desired comparison has a characteristic shape. Arithmetic geometry gives

$$
\operatorname{rd}(L)<B,
$$

where $B$ does not depend on $[L:\mathbf Q]$. Analysis gives a lower bound

$$
\operatorname{rd}(L)\geq B(n,r_1),
\qquad n=[L:\mathbf Q],
$$

which increases toward a positive limiting constant. If the upper threshold lies below that limit, only finitely many degrees remain possible. An increasing tower subject to the same upper threshold must then stabilize. This is the numerical heart of Fontaine's argument.

Three conclusions must be kept separate. A comparison can show that a specified degree is impossible. It can show that all possible degrees are bounded. Or, after applying bounded degree to an increasing tower, it can show stabilization. None of these conclusions by itself classifies the Galois image. That final step requires group theory and, in arithmetic applications, structural information about the representations.

### 1.2 Absolute and root discriminants

Let $K$ be a number field of degree

$$
n=r_1+2r_2,
$$

with $r_1$ real embeddings and $r_2$ conjugate pairs of complex embeddings. Its absolute discriminant is

$$
D_K=\left|\operatorname{disc}(\mathcal O_K/\mathbf Z)\right|.
$$

The absolute value is part of the definition used here. The signed discriminant has sign $(-1)^{r_2}$, but both the zeta functional equation and ramification comparisons naturally use $D_K>0$.

The root discriminant

$$
\operatorname{rd}(K)=D_K^{1/n}
$$

measures discriminant per embedding. Its logarithm is especially natural:

$$
\log\operatorname{rd}(K)=\frac{\log D_K}{n}.
$$

If $L/K$ is finite, discriminant transitivity gives

$$
\operatorname{rd}(L)
=\operatorname{rd}(K)
N_{K/\mathbf Q}(\mathfrak d_{L/K})^{1/[L:\mathbf Q]}.
$$

Thus

$$
\operatorname{rd}(L)\geq\operatorname{rd}(K),
$$

with equality exactly when $L/K$ is unramified at every finite prime. This monotonicity is why the root, rather than $D_K$ itself, is the stable scale for towers.

### 1.3 The pressure created by towers

Suppose

$$
K_0\subsetneq K_1\subsetneq K_2\subsetneq\cdots
$$

is an infinite tower. Then $[K_j:\mathbf Q]\to\infty$, because the degrees are positive integers and strictly increase. If the root discriminants are uniformly bounded by $B$, any asymptotic lower bound with limiting constant $C>B$ contradicts the existence of the tower.

The qualifier “uniformly” is decisive. A levelwise estimate such as

$$
\operatorname{rd}(K_j)<c\ell^j
$$

has no force against a degree tending to infinity, because its right side also tends to infinity. Likewise, a uniform bound on $[K_{j+1}:K_j]$ does not bound the total degrees. The cyclotomic tower will later provide a concrete counterexample to both shortcuts.

On the other hand, equality of root discriminants in an unramified tower shows that bounded-root-discriminant towers genuinely exist. The analytic theorem is therefore not “all infinite towers are impossible.” It is that an infinite tower cannot remain below a specific universal threshold, refined by signature.

### 1.4 Signature as visible infinite ramification

The discriminant ideal records finite primes, but the zeta functional equation also sees infinite places through gamma factors. Real embeddings and complex pairs contribute different factors. It is convenient to normalize the real proportion by

$$
\alpha=\frac{r_1}{n},
\qquad 0\leq\alpha\leq1.
$$

The analytic lower bound improves as $\alpha$ increases. Intuitively, real embeddings impose more restrictive archimedean geometry than complex pairs. The extreme cases are

$$
\alpha=0
\quad\text{and}\quad
\alpha=1,
$$

corresponding respectively to totally imaginary and totally real fields. A field with no real embeddings is not necessarily a CM field; the analytic estimate depends on signature, not on the existence of a special involution.

### 1.5 The two inputs and the logical route

The argument developed in this book has two independent engines. The first is analytic. It begins
with the completed Dedekind zeta function, inserts a positive test function into its explicit
formula, and ends with a lower bound for the root discriminant in terms of degree and signature.
The second is arithmetic. It begins with a finite Galois module possessing integral finite-flat
models at the coefficient prime, converts separation of torsion points into an upper ramification
break, and ends with an upper bound for the root discriminant of the field cut out by the module.
Neither engine knows the conclusion of the other.

The architecture is therefore

```
Dedekind zeta function                 finite-flat integral model
          |                                      |
          v                                      v
positive explicit formula              upper ramification cutoff
          |                                      |
          v                                      v
lower bound for rd(L)                   upper bound for rd(L)
          \                                      /
           \                                    /
            +-------- degree comparison -------+
                              |
                              v
                 exclusion or stabilization
```

This separation prevents several circular arguments. The field whose zeta function is used must
already have been defined; analysis does not construct it. Its ramification ceiling must already
have been proved; the explicit formula does not make a local representation finite flat. In the
opposite direction, the local argument controls discriminant but not degree from below; a large
image must be supplied by independent group theory. At the last step, a degree contradiction
rules out the specified field, but it does not classify every smaller field under the same
ceiling.

The principal concrete comparison is three-adic. If $M$ is killed by $3$, finite flat at $3$, and
unramified away from $3$, then its cutout field $L$ satisfies

$$
\operatorname{rd}(L)<3^{3/2}.
$$

If the only extra ramification is nontrivial tame cubic inertia at $2$, then the exact additional
cost is $2^{2/3}$, giving

$$
\operatorname{rd}(L)<3^{3/2}2^{2/3}.
$$

The dedicated Minkowski certificate for the first inequality gives the valid cap $52$. The
explicit-formula certificate for the larger second ceiling gives the stronger cap $20$; because a
field below the first ceiling is also below the second, the stronger cap applies to both once it
has been proved. This dominance is easy to overlook when numerical rows are organized by their
arithmetic source. Degree $20$ excludes residual fields whose Galois groups have orders $24$ or
$48$. Those are the forbidden large torsion fields relevant here.

Every logarithm in this book is natural. Ramification groups use upper numbering when a quotient
field is under discussion. The root discriminant is always absolute, even when it is computed
from a relative extension. The main comparison is unconditional. Conditional estimates are
included to explain the analytic landscape, but no Fontaine conclusion rests on them.

## 2. The geometric baseline

### 2.1 Minkowski's convex-body theorem

Before bringing in zeta functions, it is useful to establish the universal lower bound supplied by geometry of numbers. Besides handling small numerical thresholds efficiently, it reveals why discriminants measure the covolume of the ring of integers.

Embed $K$ diagonally into

$$
K_\mathbf R=K\otimes_\mathbf Q\mathbf R
\simeq\mathbf R^{r_1}\times\mathbf C^{r_2}.
$$

Give each complex coordinate its ordinary two-dimensional Lebesgue measure. Under this convention the lattice $\mathcal O_K$ has covolume

$$
2^{-r_2}\sqrt{D_K}.
$$

The factor $2^{-r_2}$ is easy to lose: the determinant formed from one embedding in each conjugate pair becomes a real determinant only after separating real and imaginary parts.

Minkowski's convex-body theorem says that a centrally symmetric convex measurable set $C\subset K_\mathbf R$ with

$$
\operatorname{vol}(C)>2^n\operatorname{covol}(\mathcal O_K)
$$

contains a nonzero algebraic integer. The same assertion applied to a fractional ideal $I$ replaces the covolume by

$$
2^{-r_2}\sqrt{D_K}\,N(I).
$$

### 2.2 The ideal-class estimate

The form needed for discriminants is the following.

**Theorem 2.1 (Minkowski ideal-class bound).** Every ideal class of $K$ contains an integral ideal $\mathfrak a$ satisfying

$$
N\mathfrak a\leq
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{D_K}.
$$

**Proof strategy.** Apply the convex-body theorem to an inverse ideal and choose a body whose coordinate product, hence the field norm, is controlled as sharply as possible. The arithmetic--geometric mean inequality is the decisive optimization.

Let $I$ represent the inverse of the desired ideal class. For positive parameters $t_1,\ldots,t_{r_1+r_2}$, consider the product body cut out by

$$
|x_i|\leq t_i
$$

at real places and by discs $|z_j|\leq t_{r_1+j}$ at complex places. A weighted simplex variant, obtained by integrating over

$$
\sum_{i=1}^{r_1}|x_i|+
2\sum_{j=1}^{r_2}|z_j|\leq T,
$$

has volume

$$
\frac{2^{r_1}(\pi/2)^{r_2}}{n!}T^n.
$$

Once this exceeds $2^n2^{-r_2}\sqrt{D_K}\,N(I)$, it contains $0\ne x\in I$. Weighted arithmetic--geometric mean gives

$$
|N_{K/\mathbf Q}(x)|
\leq\left(\frac{T}{n}\right)^n.
$$

Taking the limiting value of $T$ at which the volume inequality becomes equality yields

$$
|N(x)|\leq
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{D_K}\,N(I).
$$

The integral ideal $xI^{-1}$ lies in the required class, and its norm is $|N(x)|/N(I)$. This proves the theorem. $\square$

The constant reflects both sources of geometry: $n!/n^n$ comes from the simplex and arithmetic--geometric mean, while $(4/\pi)^{r_2}$ records the difference between discs and squares at complex places.

### 2.3 Minkowski's discriminant bound

Apply Theorem 2.1 to the principal ideal class. Its only integral ideal of norm below $1$ would be impossible, while the unit ideal has norm $1$. Hence

$$
1\leq
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{D_K}.
$$

Rearranging gives the exact bound

$$
\boxed{
D_K\geq
\left(\frac\pi4\right)^{2r_2}
\frac{n^{2n}}{(n!)^2}.
}
$$

For $K=\mathbf Q(i)$, the right side is

$$
\left(\frac\pi4\right)^2\frac{2^4}{(2!)^2}
=\frac{\pi^2}{4}<4=D_K.
$$

For a real quadratic field it gives $D_K\geq4$, which is true but not sharp: congruence restrictions on quadratic discriminants give more. This illustrates the role of Minkowski's theorem. It is universal and structural, but it does not exploit the arithmetic of prime ideals or zeros of zeta functions.

### 2.4 Root form and finite-degree consequences

Taking $n$th roots gives

$$
\boxed{
\operatorname{rd}(K)\geq
\left(\frac\pi4\right)^{2r_2/n}
\left(\frac{n^n}{n!}\right)^{2/n}.
}
$$

Since $2r_2/n=1-\alpha$, this is

$$
\operatorname{rd}(K)\geq
\left(\frac\pi4\right)^{1-\alpha}
M_n,
\qquad
M_n:=\left(\frac{n^n}{n!}\right)^{2/n}.
$$

The sequence $M_n$ is increasing, and the finite certificates later use this fact. Put

$$
a_n=\frac{(n!)^{1/n}}n,
$$

so $M_n=a_n^{-2}$. The inequality $a_{n+1}\leq a_n$, after raising to the positive power
$n(n+1)$ and canceling factorials, is equivalent to

$$
\left(1+\frac1n\right)^{n^2}\geq n+1.
$$

By the binomial theorem $(1+1/n)^n\geq2$, so the left side is at least $2^n\geq n+1$.
Therefore $M_{n+1}\geq M_n$. Stirling's formula with its usual two-sided remainder gives

$$
\log M_n
=2-\frac{\log(2\pi n)}n-\frac1{6n^2}+O(n^{-4}),
$$

so the limiting bounds are $\pi e^2/4$ in the worst signature and $e^2$ in the totally real case.

These constants are too small for the main large-degree argument. Nevertheless, exact factorial values will later give useful degree cutoffs at $2$ and $3$ without any numerical zeta computation.

### 2.5 What geometry alone cannot see

The asymptotic lower constants just obtained are

$$
\frac{\pi e^2}{4}=5.803\ldots,
\qquad e^2=7.389\ldots.
$$

The finite-flat threshold at $5$ will be

$$
5^{5/4}=7.476\ldots,
$$

which lies above even the totally real Minkowski limit. No refinement of Stirling's formula can bridge that gap; new arithmetic information is needed. Dedekind zeta functions provide it by placing prime ideals, discriminants, gamma factors, and zeros into one identity.

## 3. The zeta function of a number field

### 3.1 Why ideals are the correct spectrum

The ordinary zeta function counts positive integers. For a number field, unique factorization survives at the level of nonzero ideals, so the correct analogue is

$$
\zeta_K(s)=\sum_{0\ne\mathfrak a\subseteq\mathcal O_K}
\frac1{(N\mathfrak a)^s},
\qquad \Re(s)>1.
$$

The series converges absolutely in this half-plane. Its coefficients are nonnegative, an elementary fact with profound consequences: prime terms in the explicit formula will have a favorable sign when the test function is nonnegative.

Unique ideal factorization gives

$$
\zeta_K(s)=\prod_{\mathfrak p}
\left(1-(N\mathfrak p)^{-s}\right)^{-1}.
$$

For $K=\mathbf Q$, this is the ordinary zeta function. For a quadratic field it factors as the product of that function and a quadratic Dirichlet $L$-function, but the intrinsic ideal formulation avoids choosing characters and works uniformly in every degree.

### 3.2 Euler product and logarithmic derivative

Taking the logarithmic derivative in $\Re(s)>1$ gives

$$
-\frac{\zeta_K'}{\zeta_K}(s)
=\sum_{\mathfrak p}\sum_{m\geq1}
\frac{\log N\mathfrak p}{(N\mathfrak p)^{ms}}.
$$

The double sum counts prime powers. It is this formula, rather than the Euler product in multiplicative form, that interacts linearly with contour integration. Notice the sign: $-\zeta_K'/\zeta_K$ has positive coefficients on the real axis to the right of $1$.

A test function $F$ evaluated at $m\log N\mathfrak p$ weights the prime power $\mathfrak p^m$. If $F\geq0$, every prime-power contribution is nonnegative. Discarding these terms weakens a lower bound but never invalidates it. Retaining known splitting information can improve the bound substantially.

### 3.3 Completion and functional equation

The discriminant and signature enter through the completed function

$$
\Lambda_K(s)=
D_K^{s/2}
\left(\pi^{-s/2}\Gamma\left(\frac s2\right)\right)^{r_1}
\left((2\pi)^{-s}\Gamma(s)\right)^{r_2}
\zeta_K(s).
$$

With precisely these gamma factors,

$$
\Lambda_K(s)=\Lambda_K(1-s).
$$

The origin of the equation is geometric. For a nonzero fractional ideal $\mathfrak a$, place its Minkowski lattice in $K_\mathbf R$ and form the Gaussian theta series

$$
\Theta_{\mathfrak a}(t)
=\sum_{x\in\mathfrak a}
\exp\left(-\pi t\sum_{v\text{ real}}|x_v|^2
-2\pi t\sum_{v\text{ complex}}|x_v|^2\right).
$$

Poisson summation relates this series at $t$ to the theta series of the trace-dual lattice at $1/t$. The covolume of the lattice contributes $D_K^{1/2}$, while the one- and two-dimensional Gaussian integrals contribute the real and complex gamma factors. Mellin transforming $\Theta_{\mathfrak a}(t)-1$ and summing over ideal classes gives $\Lambda_K(s)$. Splitting the Mellin integral at $t=1$ and applying Poisson summation on $(0,1)$ continues it meromorphically and produces the symmetry $s\leftrightarrow1-s$.

Here are the details of that passage. Equip $K_{\mathbf R}$ with the trace pairing

$$
\langle x,y\rangle=\operatorname{Tr}_{K/\mathbf Q}(x\overline y).
$$

The lattice dual to a fractional ideal $\mathfrak a$ is

$$
\mathfrak a^*=\mathfrak D_K^{-1}\mathfrak a^{-1},
$$

where $\mathfrak D_K$ is the different. With complex coordinates counted with weight two, Fourier
transformation of the Gaussian gives

$$
\Theta_{\mathfrak a}(t)
=\frac{t^{-n/2}}{\operatorname{covol}(\mathfrak a)}
\Theta_{\mathfrak a^*}(t^{-1}),
\qquad
\operatorname{covol}(\mathfrak a)
=2^{-r_2}\sqrt{D_K}\,N\mathfrak a.
\tag{3.1}
$$

Units prevent a raw theta series from being a sum indexed once by ideals. To remove the
overcounting, let $Y$ be the group of positive archimedean scalings of weighted product one and
integrate over a fundamental parallelepiped for the logarithmic image of
$\mathcal O_K^\times$. Every nonzero element of $\mathfrak a$ is then counted once modulo units,
and its orbit corresponds to the integral ideal it generates in the inverse ideal class. Separating
the radial coordinate from $Y$ gives, initially for $\Re(s)>1$,

$$
\Gamma_{\mathbf R}(s)=\pi^{-s/2}\Gamma(s/2),
\qquad
\Gamma_{\mathbf C}(s)=(2\pi)^{-s}\Gamma(s),
$$

and

$$
\int_0^\infty\int_P
\bigl(\Theta_{\mathfrak a}(t,y)-1\bigr)t^{s/2}
\,d^\times y\,\frac{dt}{t}
=c_KD_K^{s/2}
\Gamma_{\mathbf R}(s)^{r_1}
\Gamma_{\mathbf C}(s)^{r_2}
\zeta_{[\mathfrak a]^{-1}}(s),
\tag{3.2}
$$

where $c_K>0$ is independent of the ideal class. The one-dimensional radial Mellin integrals are

$$
\int_{-\infty}^{\infty}e^{-\pi x^2}|x|^s\frac{dx}{|x|}
=\pi^{-s/2}\Gamma(s/2),
$$

and the two-dimensional complex integrals give $(2\pi)^{-s}\Gamma(s)$ after the common measure
normalization is absorbed into $c_K$. This proves (3.2) rather than merely identifying its shape.

Split the $t$-integral at $1$. On $(0,1)$ use (3.1), then substitute $t\mapsto1/t$. The nonzero
parts become exponentially convergent integrals over $(1,\infty)$ with $s$ replaced by $1-s$ and
the ideal class replaced by its inverse dual class. They are entire in $s$. The zero-vector terms
are elementary:

$$
\int_0^1t^{s/2}\frac{dt}{t}=\frac2s,
\qquad
\int_0^1t^{(1-s)/2}\frac{dt}{t}=\frac2{1-s}.
$$

Thus every completed partial zeta function continues meromorphically with only simple poles at
$0$ and $1$. Duality permutes ideal classes, so summing (3.2) over the class group proves both the
continuation of $\Lambda_K$ and

$$
\Lambda_K(s)=\Lambda_K(1-s).
$$

The exponent $s/2$ on $D_K$ is forced: inversion in Poisson summation contributes
$D_K^{-1/2}$, and only $D_K^{s/2}$ transforms it into $D_K^{(1-s)/2}$.

This argument also identifies the poles. The zero vector in the theta series produces simple terms proportional to $1/s$ and $1/(s-1)$; everything left after their removal is entire. Thus the analytic continuation, the functional equation, and the pole orders are consequences of the same lattice duality. The discriminant appears because the duality changes covolume, not because it was inserted after the fact.

There are several equivalent conventions in which powers of $2$ and $\pi$ move between the discriminant factor and gamma factors. The displayed convention is fixed throughout this book. Under it, the explicit formula below contains $\gamma+\log(8\pi)$ and $r_1\pi/2$. Changing the completed function without changing those constants would give a wrong root-discriminant threshold.

The function $\Lambda_K$ has simple poles at $s=0$ and $s=1$. Thus

$$
\xi_K(s)=\frac12s(s-1)\Lambda_K(s)
$$

is entire of order one and satisfies $\xi_K(s)=\xi_K(1-s)$. The harmless factor $1/2$ fixes a normalization but disappears from logarithmic derivatives.

### 3.4 Poles, trivial zeros, and nontrivial zeros

The zeros of $\xi_K$ are precisely the zeros coming from $\zeta_K$ in the strip

$$
0<\Re(s)<1
$$

and are called the nontrivial zeros. They occur with multiplicity and are symmetric under

$$
\rho\longmapsto1-\rho,
\qquad
\rho\longmapsto\overline\rho.
$$

The trivial zeros of $\zeta_K$ outside the strip cancel poles of the gamma factors in the completed function; they are therefore not additional zeros of $\xi_K$. In the explicit formula their effect is most cleanly retained inside the archimedean integrals rather than listed separately. The poles of $\Lambda_K$ at $0$ and $1$, removed in $\xi_K$ by the factor $s(s-1)$, contribute another explicit term. Losing either contribution changes the finite-degree correction.

The generalized Riemann hypothesis for $\zeta_K$ asserts that every nontrivial zero has the form

$$
\rho=\frac12+i\gamma_\rho,
\qquad \gamma_\rho\in\mathbf R.
$$

We will derive both unconditional and conditional bounds. Every result used in the main Fontaine stabilization theorem will be unconditional.

### 3.5 Analytic hypotheses and growth estimates

The contour argument needs more than a formal functional equation. It needs enough control on
$\xi_K$ and on the test transform to make the horizontal sides of large rectangles disappear and
to make the sum over zeros meaningful. We record the required estimates because this is where a
plausible formal identity becomes a theorem.

The theta-integral representation used in §3.3 shows that $\xi_K$ is entire of order one. Stirling's
formula for the gamma factors, the Euler product on $\Re(s)>1$, and the functional equation then
give, for $T\geq2$,

$$
N_K(T+1)-N_K(T)
\ll n\log\bigl(D_K(T+3)^n\bigr),
\tag{3.3}
$$

where $N_K(T)$ counts nontrivial zeros with $|\operatorname{Im}\rho|\leq T$, with
multiplicity. To prove (3.3), apply the argument principle to $\xi_K$ on a rectangle of width one.
On the right edge, $\zeta_K$ is bounded by a suitable power of the ordinary zeta function; on the
left edge the functional equation supplies the same bound; on the horizontal edges Stirling's
formula controls the logarithmic derivatives of the gamma factors.

If $F$ is compactly supported, piecewise $C^2$, and has one-sided first derivatives of bounded
variation, integration by parts on its smooth pieces gives

$$
\Phi_F(\sigma+it)=O_F((1+|t|)^{-2})
$$

uniformly when $\sigma$ remains in a bounded interval. Combining this with (3.3) shows that the
symmetric zero sum converges after grouping zeros in horizontal bands. For a smooth $F$, repeated
integration by parts gives arbitrarily rapid decay.

The horizontal sides require a mild avoidance argument. Because an order-one entire function has
only the number of zeros permitted by (3.3), one can choose heights $T_j\to\infty$ that remain an
inverse-polynomial distance from every zero ordinate. On those heights the logarithmic derivative
satisfies a polynomial logarithmic bound, while $\Phi_F$ decays faster than any polynomial in the
smooth case. Hence the horizontal integrals tend to zero. The final identity is independent of
this chosen sequence because the zero series converges symmetrically.

There is also a local integrability condition at the origin. The kernel

$$
\frac1{2\sinh(x/2)}
$$

has a simple pole, so it is enough to require

$$
\int_0^1\frac{|1-F(x)|}{x}\,dx<\infty.
\tag{3.4}
$$

Smooth even functions satisfy $1-F(x)=O(x^2)$. Triangular functions satisfy
$1-F(x)=O(x)$, which also suffices. Condition (3.4), compact support, and the exponential decay of
the hyperbolic kernels account for every archimedean convergence assertion below.

## 4. The explicit formula

### 4.1 From a functional equation to a weighted identity

The functional equation relates values at $s$ and $1-s$, while the Euler product controls values to the right of $1$. To turn this into a discriminant inequality, one integrates the logarithmic derivative against a transform chosen from a real test function. Moving the contour across the critical strip collects residues at zeros and poles. The functional equation converts the new vertical line back to the original one, and the gamma logarithmic derivatives become real integrals.

This is a weighted trace formula. Prime powers occupy one side, zeros the other, and the discriminant is the scale factor connecting them. Its strength comes not from knowing individual zeros, but from choosing a test function for which their total contribution is nonnegative.

### 4.2 Transform conventions and admissibility

Let $F:\mathbf R\to\mathbf R$ be even, continuous, compactly supported, piecewise $C^2$, and normalized by $F(0)=1$. Corners may be replaced by smooth limits. We use the Fourier transform

$$
\widehat F(t)=\int_{-\infty}^{\infty}F(x)e^{-itx}\,dx
$$

with no factor of $2\pi$. Its Laplace--Fourier transform is

$$
\Phi_F(s)=\int_{-\infty}^{\infty}
F(x)e^{(s-1/2)x}\,dx.
$$

Thus on the critical line

$$
\Phi_F\left(\frac12+it\right)=\widehat F(-t)=\widehat F(t).
$$

We call $F$ **conditionally admissible** when $F\geq0$ and $\widehat F\geq0$. Under the generalized Riemann hypothesis, this makes every zero contribution nonnegative.

For an unconditional result we require a stronger construction. Let

$$
F(x)=\frac{G(x)}{\cosh(x/2)},
$$

where $G\geq0$ is even and of positive type, meaning $\widehat G(t)\geq0$ for all real $t$. We call such an $F$ **unconditionally admissible**. The reason for the hyperbolic denominator will be proved in Chapter 5.

### 4.3 The Weil--Poitou identity

For either class of test functions, contour integration gives the following exact identity.

**Theorem 4.1 (explicit formula).** Let $K$ have degree $n$ and signature $(r_1,r_2)$. Then

$$
\begin{aligned}
\log D_K={}&n(\gamma+\log(8\pi))+\frac{\pi r_1}{2}
-4\int_0^\infty F(x)\cosh(x/2)\,dx\\
&-n\int_0^\infty
\frac{1-F(x)}{2\sinh(x/2)}\,dx
-r_1\int_0^\infty
\frac{1-F(x)}{2\cosh(x/2)}\,dx\\
&+\sum_\rho\Phi_F(\rho)
+2\sum_{\mathfrak p}\sum_{m\geq1}
\frac{\log N\mathfrak p}{(N\mathfrak p)^{m/2}}
F(m\log N\mathfrak p).
\end{aligned}
$$

The zero sum is taken symmetrically over nontrivial zeros with multiplicity. Both integrals involving $1-F$ converge: near zero, even smooth $F$ satisfies $1-F(x)=O(x^2)$, while for a triangular limiting function it is $O(x)$ and the quotient remains bounded; at infinity the hyperbolic denominators decay exponentially.

**Proof strategy.** Apply the residue theorem to $-(\xi_K'/\xi_K)(s)\Phi_F(s)$ on a rectangle symmetric about $\Re(s)=1/2$. Zeros of $\xi_K$ give the zero sum. Expanding $-\zeta'_K/\zeta_K$ on the right edge and using Fourier inversion gives the prime-power sum. The logarithmic derivative of $D_K^{s/2}$ gives $\log D_K$. The real and complex gamma factors are evaluated with

$$
\frac{\Gamma'}{\Gamma}(z)
=\int_0^\infty
\left(\frac{e^{-x}}x-\frac{e^{-zx}}{1-e^{-x}}\right)dx,
$$

interpreted after cancellation at zero. Pairing $s$ with $1-s$ produces the two displayed hyperbolic kernels. Finally the factors $s(s-1)$ contribute

$$
-4\int_0^\infty F(x)\cosh(x/2)\,dx.
$$

The horizontal integrals vanish first for a smooth compactly supported function and then by approximation for the stated class. $\square$

Here is the accounting in greater detail. Choose $c>1$ and integrate first on $\Re(s)=c$. Absolute convergence permits insertion of

$$
-\frac{\zeta'_K}{\zeta_K}(s)
=\sum_{\mathfrak p,m}
(\log N\mathfrak p)(N\mathfrak p)^{-ms}.
$$

For $y>0$, bilateral Laplace inversion gives

$$
\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}
\Phi_F(s)e^{-y(s-1/2)}ds=F(y).
$$

Putting $y=m\log N\mathfrak p$ yields the displayed weight

$$
(N\mathfrak p)^{-m/2}F(m\log N\mathfrak p).
$$

The factor $2$ in the theorem comes from pairing the two vertical lines after the functional equation.

Next move the line from $c$ to $1-c$. Every nontrivial zero crossed contributes $\Phi_F(\rho)$. Rather than treating trivial zeros one by one, retain the logarithmic derivatives of the gamma factors and use their integral representation. The singular pieces at $x=0$ cancel against $F(0)=1$, leaving the kernels

$$
\frac{1-F(x)}{2\sinh(x/2)}
\quad\text{and}\quad
\frac{1-F(x)}{2\cosh(x/2)}.
$$

The constants left by that cancellation are $\gamma+\log(8\pi)$ per degree and $\pi/2$ per real place. Finally, the poles removed by $s(s-1)$ contribute the value of the transform at $0$ and $1$:

$$
\Phi_F(0)+\Phi_F(1)
=2\int_{-\infty}^{\infty}F(x)\cosh(x/2)dx
=4\int_0^\infty F(x)\cosh(x/2)dx.
$$

They occur on the opposite side before solving for $\log D_K$, which explains the negative pole term. This derivation simultaneously verifies the prime weight, the factor $4$, and the hyperbolic kernels.

### 4.4 Why every sign matters

Several quick checks detect normalization errors.

First, the prime term must have a plus sign in the expression for $\log D_K$. Its coefficients and $F$ are nonnegative, so known small prime ideals improve a lower bound. Second, the zero term must also have a plus sign; positivity is the mechanism that permits it to be dropped. Third, the pole term has a minus sign and is divided by $n$ after passage to root discriminants. It is the finite-degree penalty and disappears asymptotically.

Finally, the coefficient of $r_1$ outside the integrals is $\pi/2$. This is what produces the conditional totally real factor $e^{\pi/2}$. The unconditional test function pays back $\pi/2-1$, leaving the factor $e$ instead. These checks recover all four asymptotic constants derived below.

### 4.5 Discarding positive terms

Put

$$
\begin{aligned}
A(F)&=\int_0^\infty F(x)\cosh(x/2)\,dx,\\
B(F)&=\int_0^\infty\frac{1-F(x)}{2\sinh(x/2)}\,dx,\\
C(F)&=\int_0^\infty\frac{1-F(x)}{2\cosh(x/2)}\,dx.
\end{aligned}
$$

If the zero contribution is nonnegative and $F\geq0$, Theorem 4.1 gives

$$
\boxed{
\log\operatorname{rd}(K)\geq
\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{4A(F)}n-B(F)-\alpha C(F).
}
$$

This is the basic Odlyzko--Poitou inequality. It is already an explicit algorithm: choose $F$, evaluate three one-dimensional integrals, and compare the result with an arithmetic upper bound. Prime powers may be restored whenever splitting information is known; omitting them is uniform over all fields of the given degree and signature.

### 4.6 Convergence and passage to nonsmooth kernels

For completeness, we explain why the formula proved first for smooth functions applies to the
triangles used numerically. Let $h_j$ be nonnegative, even, smooth approximations to the indicator
of $[-T/2,T/2]$, and take the normalized autocorrelation $G_{T,j}$. Then

$$
G_{T,j}(0)=1,
\qquad G_{T,j}\geq0,
\qquad \widehat G_{T,j}\geq0,
$$

and $G_{T,j}\to G_T$ pointwise away from the corners and in $L^1$. Multiplication by
$\operatorname{sech}(x/2)$ preserves a common compact support and gives an integrable majorant for
the pole integral. Near zero the quotient in (3.4) is uniformly bounded after a rescaling tending
to one that restores value $1$ at the origin.

The prime sum is finite because the support is compact, so it passes to the limit term by term
unless a prime power lies exactly at an endpoint. In that exceptional case one approaches the
triangle through supports from the appropriate side; because the universal inequality discards
the prime sum, its endpoint value is immaterial here. The archimedean terms pass by dominated
convergence. Finally the zero sums have a common
$(1+|\operatorname{Im}\rho|)^{-2}$ majorant, and (3.3) permits dominated convergence by horizontal
bands. Thus the explicit formula and every lower bound derived from it hold for the triangular
limiting functions exactly as stated.

This passage identifies which facts are structural and which are cosmetic. Positivity comes from
autocorrelation and survives smoothing. The exact elementary formulas for $B_T$ and $C_T$ belong
to the nonsmooth limit. Smoothness is used only to justify the contour shift before that limit is
taken.

## 5. Designing test functions

### 5.1 Positive type and autocorrelation

The explicit formula turns test-function design into an optimization problem with constraints. We want $F$ close to $1$ over a long interval, because that makes $B(F)$ and $C(F)$ small. We also want $A(F)$ small relative to $n$, because $4A(F)/n$ is the finite-degree penalty. Finally, positivity of the zero and prime terms must be guaranteed rather than guessed.

A reliable source of Fourier positivity is autocorrelation. If $h\in L^2(\mathbf R)$ is real and

$$
\widetilde h(x)=h(-x),
$$

then

$$
G=h*\widetilde h
$$

satisfies

$$
\widehat G(t)=|\widehat h(t)|^2\geq0.
$$

After division by $G(0)$ it has value $1$ at the origin. Taking $h$ to be the indicator of $[-T/2,T/2]$ gives the triangle

$$
G_T(x)=\left(1-\frac{|x|}{T}\right)_+.
$$

Its transform, in our normalization, is

$$
\widehat G_T(t)
=T\left(\frac{\sin(Tt/2)}{Tt/2}\right)^2\geq0.
$$

This formula also checks the absence of a hidden $2\pi$: at $t=0$ the right side is $T$, equal to the area under the triangle.

Fourier positivity does not imply pointwise nonnegativity in general. We impose both because zeros require the former and prime powers require the latter. The triangular family has both properties.

### 5.2 The GRH and unconditional positivity mechanisms

Under the generalized Riemann hypothesis, every zero is $1/2+i\gamma_\rho$, so

$$
\Phi_F(\rho)=\widehat F(\gamma_\rho)\geq0
$$

for a conditionally admissible $F$. This is the entire conditional step. All remaining terms and calculations are unconditional.

Without that hypothesis, write a zero as $\rho=\beta+i\gamma$ and group it with $1-\overline\rho$. If the involution fixes $\rho$, then $\beta=1/2$ and the single contribution is covered by the case $a=0$ below. If

$$
F(x)=\frac{G(x)}{\cosh(x/2)},
$$

their combined contribution is

$$
2\int_{-\infty}^{\infty}
G(x)\frac{\cosh((\beta-1/2)x)}{\cosh(x/2)}
\cos(\gamma x)\,dx.
$$

For $|a|\leq1/2$, the function

$$
x\longmapsto\frac{\cosh(ax)}{\cosh(x/2)}
$$

is of positive type. One sees this directly by evaluating its Fourier transform by residues. For $|a|<1/2$ it is

$$
\frac{4\pi\cos(\pi a)\cosh(\pi t)}
{\cosh(2\pi t)+\cos(2\pi a)}\geq0,
$$

with the boundary cases obtained by limits. The product of two positive-type functions is again of positive type, because on the transform side it corresponds to convolution of nonnegative measures. Since $|\beta-1/2|\leq1/2$, the paired zero contribution is nonnegative.

We include the residue calculation because unconditionality rests on it. For $t>0$, integrate

$$
\frac{\cosh(az)}{\cosh(z/2)}e^{-itz}
$$

over a large rectangle closed in the lower half-plane. The vertical sides vanish because
$|a|<1/2$, and the lower horizontal side vanishes because of the exponential factor. The enclosed
poles are

$$
z_k=-(2k+1)\pi i,
\qquad k\geq0.
$$

Since

$$
\frac{d}{dz}\cosh(z/2)\bigg|_{z=z_k}
=-\frac i2(-1)^k,
$$

the clockwise residue theorem gives

$$
\widehat H_a(t)
=4\pi\sum_{k\geq0}(-1)^k
\cos\bigl((2k+1)\pi a\bigr)e^{-(2k+1)\pi t}.
$$

Writing the cosine as the real part of an exponential and summing the resulting geometric series
reduces this expression to

$$
\widehat H_a(t)
=\frac{4\pi\cos(\pi a)\cosh(\pi t)}
{\cosh(2\pi t)+\cos(2\pi a)}.
$$

Evenness gives the same formula for $t<0$. Its denominator is
$2(\sinh^2(\pi t)+\cos^2(\pi a))$ and its numerator is nonnegative for
$|a|\leq1/2$. At the endpoints, monotone weak limits of the nonnegative Fourier measures preserve
positive type. Finally,

$$
\widehat{G H_a}
=\frac1{2\pi}\widehat G*\widehat H_a\geq0.
$$

The paired zero contribution is twice $\widehat{G H_{\beta-1/2}}(\gamma)$ and is therefore
nonnegative. This proves positivity for every symmetric zero pair, including zeros off the
critical line.

This argument explains both the strength and the cost of the unconditional method. The factor $1/\cosh(x/2)$ protects positivity throughout the critical strip, but prevents $F$ itself from tending to $1$ at large fixed $x$. That loss changes the asymptotic constant by an exact, computable amount.

### 5.3 A triangular family

We use two related families:

$$
F_T^{\mathrm{GRH}}(x)=G_T(x),
\qquad
F_T^{\mathrm{un}}(x)=\frac{G_T(x)}{\cosh(x/2)}.
$$

For the unconditional family,

$$
A(F_T^{\mathrm{un}})
=\int_0^T\left(1-\frac{x}{T}\right)dx
=\frac T2.
$$

This exact identity makes finite-degree calculations particularly transparent. Put

$$
B_T=B(F_T^{\mathrm{un}}),
\qquad C_T=C(F_T^{\mathrm{un}}).
$$

Then

$$
\boxed{
\log\operatorname{rd}(K)\geq
\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{2T}{n}-B_T-\alpha C_T.
}
$$

The two competing effects are visible. Increasing $T$ decreases $B_T$ and $C_T$ toward their limiting values, but increases the penalty $2T/n$. The optimal $T$ therefore grows with $n$, though much more slowly than $n$.

### 5.4 Smooth approximations and endpoint control

The triangle has corners at $0$ and $\pm T$. They cause no mathematical ambiguity. Choose nonnegative even smooth functions $h_j$ converging in $L^2$ to the interval indicator and form normalized autocorrelations $G_j=h_j*\widetilde h_j$. Then $G_j$ and their transforms are nonnegative, $G_j(0)=1$, and $G_j\to G_T$ pointwise away from the corners and in every integral appearing above.

Near zero,

$$
1-F_T^{\mathrm{un}}(x)=\frac{x}{T}+O(x^2)
\quad(x\downarrow0),
$$

so the apparent singularity in $B_T$ is removable and its limiting integrand value is $1/T$. Dominated convergence therefore passes the explicit inequality to the triangular limit. Values at the support endpoint and at individual zeros or prime powers can be chosen by a limiting convention; they do not alter the integrals, and a smooth approximation can be used if an exact endpoint happens to matter.

### 5.5 Prime information as a refinement

Dropping the prime sum gives a universal bound, but arithmetic applications sometimes prescribe splitting. If $K$ has $g_q$ prime ideals of norm $q$, then retaining only their first powers improves the lower bound for $\log\operatorname{rd}(K)$ by

$$
\frac{2g_q\log q}{n\sqrt q}F(\log q).
$$

Higher powers and other prime ideals add further nonnegative terms. The degree constraint $g_q\leq n$ prevents arbitrary insertion of prime ideals. If the residue degrees above $q$ are $f_1,\ldots,f_g$, the correct terms are $F(mf_j\log q)$ weighted by $f_j\log q/q^{mf_j/2}$.

This refinement is useful only when the splitting data are proved independently. Assuming that every rational prime contributes a degree-one ideal would reverse the logic and manufacture a false lower bound. The main Fontaine theorem below uses no prime contribution at all.

## 6. Odlyzko--Poitou lower bounds

### 6.1 A bound attached to one test function

For degree $n$, real proportion $\alpha$, and an admissible $F$, define

$$
\mathcal L(n,\alpha;F)=
\exp\left(
\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{4A(F)}n-B(F)-\alpha C(F)
\right).
$$

The explicit formula proves

$$
\operatorname{rd}(K)\geq\mathcal L(n,\alpha;F).
$$

Taking the supremum over unconditionally admissible test functions gives an unconditional function $\mathcal L_{\mathrm{un}}(n,\alpha)$. Taking the supremum over conditionally admissible functions gives $\mathcal L_{\mathrm{GRH}}(n,\alpha)$, valid under the generalized Riemann hypothesis. The second admissible class is larger, so its numerical values are stronger; it must never be substituted into an unconditional argument.

For a fixed $F$, the bound increases with $n$, because only the negative term $4A(F)/n$ depends on degree. It also increases with $\alpha$ provided

$$
C(F)<\frac\pi2,
$$

which holds for the families used here. These elementary monotonicities let one verify a whole degree or signature range at a single endpoint.

### 6.2 Unconditional asymptotic constants

Take $F_T=G_T/\cosh(x/2)$ and let $T\to\infty$. For every fixed $x$,

$$
F_T(x)\longrightarrow\frac1{\cosh(x/2)}.
$$

The limiting archimedean losses are elementary integrals. With $y=x/2$,

$$
\begin{aligned}
\lim_{T\to\infty}B_T
&=\int_0^\infty
\frac{1-\operatorname{sech}(x/2)}{2\sinh(x/2)}dx\\
&=\int_0^\infty
\frac{\cosh y-1}{\sinh y\cosh y}dy
=\log2,
\end{aligned}
$$

and

$$
\begin{aligned}
\lim_{T\to\infty}C_T
&=\int_0^\infty
\left(\operatorname{sech}y-\operatorname{sech}^2y\right)dy\\
&=\frac\pi2-1.
\end{aligned}
$$

To pass simultaneously to large degree, choose $T=T(n)$ with

$$
T(n)\to\infty,
\qquad \frac{T(n)}n\to0.
$$

Then $2T/n\to0$, and the inequality becomes

$$
\liminf_{n\to\infty}\operatorname{rd}(K_n)
\geq4\pi e^{\gamma+\alpha}
$$

for any sequence whose real proportions tend to $\alpha$. In particular,

$$
\boxed{C_{\mathrm{un}}(\alpha)=4\pi e^{\gamma+\alpha}.}
$$

Using $\gamma=0.577215664901532\ldots$ gives

$$
C_{\mathrm{un}}(0)=4\pi e^\gamma
=22.3816160954\ldots,
$$

and

$$
C_{\mathrm{un}}(1)=4\pi e^{1+\gamma}
=60.8395403238\ldots.
$$

Every factor has now been accounted for: the $8\pi$ in the explicit formula loses a factor $2$ through $B_T\to\log2$, and the real-place exponent $\pi/2$ loses $\pi/2-1$ through $C_T$.

### 6.3 Conditional asymptotic constants

Under the generalized Riemann hypothesis use $F_T=G_T$. It tends pointwise to $1$. Hence

$$
B(F_T)\to0,
\qquad C(F_T)\to0.
$$

The pole integral $A(F_T)$ grows exponentially in $T/2$, so choose $T(n)\to\infty$ slowly enough that $A(F_T)/n\to0$; for example, any fixed sufficiently small multiple of $\log n$ works. The conditional asymptotic constant is

$$
\boxed{C_{\mathrm{GRH}}(\alpha)=8\pi e^{\gamma+\alpha\pi/2}.}
$$

At the two signature extremes,

$$
C_{\mathrm{GRH}}(0)=8\pi e^\gamma
=44.7632321909\ldots,
$$

and

$$
C_{\mathrm{GRH}}(1)=8\pi e^{\gamma+\pi/2}
=215.3325159534\ldots.
$$

These larger constants are valuable conditional information, but they play no role in the unconditional Fontaine theorem. Labeling them is not merely editorial: using $44.76\ldots$ without the hypothesis would double the general asymptotic threshold illegitimately.

### 6.4 Signature interpolation

The constants vary exponentially, not linearly, with the real proportion:

$$
\log C_{\mathrm{un}}(\alpha)
=\log(4\pi)+\gamma+\alpha,
$$

$$
\log C_{\mathrm{GRH}}(\alpha)
=\log(8\pi)+\gamma+\frac\pi2\alpha.
$$

If $r_1/n\geq\alpha_0$, one may use the constant at $\alpha_0$. Thus a family need not be totally real to benefit from signature. A positive density of real embeddings already raises the threshold by $e^{\alpha_0}$ unconditionally.

Signature behaves differently in a tower. A real place of the base may become complex upstairs, so the real proportion need not increase. If every embedding of every level is real, the totally real bound applies uniformly. If no such structural hypothesis is known, the safe choice is $\alpha=0$.

### 6.5 What the asymptotic statement really says

The notation

$$
\liminf_{n\to\infty}\operatorname{rd}(K)\geq C
$$

means that for every $B<C$ there exists $N(B)$ such that every field of degree at least $N(B)$ has root discriminant greater than $B$. It does not say that every field has root discriminant at least $C$. Small-degree fields provide obvious counterexamples: $\mathbf Q$ has root discriminant $1$, and $\mathbf Q(i)$ has root discriminant $2$.

Nor does the asymptotic constant by itself give a practical $N(B)$. For that one chooses a finite test function and evaluates its integrals. The next chapter performs precisely the computations needed for the primes $2$, $3$, and $5$.

## 7. Finite-degree bounds without tables

### 7.1 An explicit optimization algorithm

For the unconditional triangular family, define

$$
L_T(n,\alpha)=
\exp\left(
\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{2T}{n}-B_T-\alpha C_T
\right).
$$

A reproducible finite-degree procedure is:

1. Fix the proposed upper threshold $U$ and a lower signature ratio $\alpha_0$.
2. Choose a positive rational support $T$.
3. Enclose $B_T$ and $C_T$ by rational intervals.
4. Insert the upper endpoints of those intervals into $L_T(n,\alpha_0)$, producing a rigorous lower bound.
5. Solve $L_T(n,\alpha_0)>U$ for $n$.
6. If desired, vary $T$ over a finite rational grid and retain the best certified result.

For fixed $T$ the logarithm is affine in $1/n$ and in $\alpha$. Consequently one calculation handles every $n$ above the tested degree and every $\alpha$ above the tested signature ratio.

The test-function bound can be combined with Minkowski by taking the larger of the two lower bounds. This is often more efficient than optimizing the explicit formula at very small degree.

### 7.2 Certified evaluation of the integrals

No external numerical table is needed for the calculations below. On $0\leq x\leq T$ insert

$$
F_T(x)=\frac{1-x/T}{\cosh(x/2)};
$$

on $x\geq T$ insert $F_T(x)=0$. The tails can be bounded by geometric series after writing

$$
\frac1{2\sinh(x/2)}
=\frac{e^{-x/2}}{1-e^{-x}},
\qquad
\frac1{2\cosh(x/2)}
=\frac{e^{-x/2}}{1+e^{-x}}.
$$

For transparency, the needed integrals reduce further to rapidly convergent expressions. Comparing $F_T$ with $\operatorname{sech}(x/2)$ gives

$$
\begin{aligned}
B_T={}&\log2+\frac{\pi^2}{4T}+\log\coth\left(\frac T2\right)\\
&-\frac2T\sum_{k\geq0}
\frac{\bigl(1+(2k+1)T\bigr)e^{-(2k+1)T}}{(2k+1)^2},\\
C_T={}&\frac\pi2-\frac2T\log\cosh\left(\frac T2\right).
\end{aligned}
$$

Indeed, $1/\sinh x=2\sum_{k\geq0}e^{-(2k+1)x}$ and the sum of the reciprocal squares of the positive odd integers is $\pi^2/8$. If the sum for $B_T$ is stopped after $k=m$, the omitted part before multiplication by $2/T$ is at most

$$
\frac{(1+T)e^{-(2m+3)T}}{1-e^{-2T}}.
$$

The identities

$$
\log\coth\left(\frac T2\right)
=\log(1+e^{-T})-\log(1-e^{-T}),
$$

$$
\log\cosh\left(\frac T2\right)
=\frac T2-\log2+\log(1+e^{-T})
$$

put every remaining logarithm in a rapidly convergent range. Bounding the exponentials and logarithms by alternating Taylor series gives the following rational enclosures; already $m=1$ makes the displayed series-remainder bound smaller than the quoted interval widths:

$$
\begin{array}{c|c|c|c}
T&A_T&B_T&C_T\\
\hline
17/5&17/10&1.39921<B_T<1.39923&0.95921<C_T<0.95923\\
9/2&9/4&1.23652<B_T<1.23653&0.87395<C_T<0.87396\\
6&3&1.10355<B_T<1.10356&0.80102<C_T<0.80103.
\end{array}
$$

As a check using the original integral form, the tails after $x=80$ are below $4e^{-40}/(1-e^{-80})<2\cdot10^{-17}$ in each case. The interval widths displayed above are far larger than that tail and the series remainders. Thus the rounded upper endpoints used below are rigorous. The exact identity $A_T=T/2$ requires no numerical evaluation.

This finite verification is intentionally isolated. Any sharper quadrature or a different admissible function may improve the degree cutoffs, but no later theorem depends on an unverified tabulation.

### 7.3 The thresholds needed at 2, 3, and 5

The finite-flat level-$\ell$ upper thresholds over $\mathbf Q$ are

$$
U_\ell=\ell^{\ell/(\ell-1)}.
$$

Explicitly,

$$
U_2=4,
\qquad
U_3=3^{3/2}=5.1961524227\ldots,
\qquad
U_5=5^{5/4}=7.4767439061\ldots.
$$

For $\ell=2$, the worst-signature Minkowski bound at degree $12$ is

$$
\frac\pi4M_{12}
=\frac\pi4\left(\frac{12^{12}}{12!}\right)^{1/6}
=4.0432402329\ldots>4.
$$

Since $M_n$ is increasing, $\operatorname{rd}(K)<4$ forces

$$
[K:\mathbf Q]\leq11.
$$

At degree $53$,

$$
\frac\pi4M_{53}=5.2006733020\ldots
>3^{3/2}.
$$

Thus

$$
\operatorname{rd}(K)<3^{3/2}
\quad\Longrightarrow\quad
[K:\mathbf Q]\leq52.
$$

For $\ell=5$, use the unconditional explicit formula with $T=9/2$, $\alpha=0$, $n=17$, and the rigorous upper bound $B_T<1.23653$. It gives

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)-\frac9{17}-1.23653\\
&>2.03544,
\end{aligned}
$$

and hence

$$
\operatorname{rd}(K)>7.6556>5^{5/4}.
$$

Therefore

$$
\operatorname{rd}(K)<5^{5/4}
\quad\Longrightarrow\quad
[K:\mathbf Q]\leq16.
$$

These degree bounds are deliberately elementary rather than optimal. Their virtue is that every constant used later has been derived in the text.

### 7.4 The decisive two-prime certificate

The three-adic application permits a specific auxiliary contribution at $2$. When inertia there
is tame of order $3$, its normalized different exponent is $1-1/3=2/3$. The resulting ceiling is

$$
U_{2,3}=3^{3/2}2^{2/3}
=8.248377821991616\ldots.
$$

This ceiling is larger than the three-only value, so the degree-$53$ Minkowski calculation cannot
be recycled. We need a separate finite certificate. Take $T=6$, $n=21$, and $\alpha=0$. The
certified enclosure $B_6<1.10356$ gives

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)-\frac{12}{21}-1.10356\\
&>2.126398521002197.
\end{aligned}
\tag{7.1}
$$

The elementary logarithm series

$$
\log\frac{1+y}{1-y}
=2\sum_{j=0}^{m}\frac{y^{2j+1}}{2j+1}+R_m,
\qquad
|R_m|\leq
\frac{2|y|^{2m+3}}{(2m+3)(1-y^2)},
$$

after power-of-two range reduction, gives directed enclosures for $\log2$ and $\log3$. They yield

$$
\log U_{2,3}
=\frac32\log3+\frac23\log2
<2.110016553375462.
\tag{7.2}
$$

The logarithmic margin in (7.1)--(7.2) is greater than
$0.016381967626735$. It is therefore far larger than every interval remainder used in §7.2.
Exponentiating only to make the comparison visible,

$$
\operatorname{rd}(K)>8.38461535304387
>8.248377821991616=U_{2,3}.
$$

Degree monotonicity now proves the exact interface needed later:

$$
\boxed{
\operatorname{rd}(K)<3^{3/2}2^{2/3}
\Longrightarrow [K:\mathbf Q]\leq20.}
\tag{7.3}
$$

The same conclusion holds if the arithmetic premise is weak,
$\operatorname{rd}(K)\leq U_{2,3}$, because the analytic lower bound at degree $21$ is strictly
larger. The certificate is unconditional and makes no signature assumption.

Since $3^{3/2}<U_{2,3}$, this certificate also sharpens the standalone degree-$52$ row of §7.3:

$$
\operatorname{rd}(K)<3^{3/2}
\quad\Longrightarrow\quad
[K:\mathbf Q]\leq20.
\tag{7.4}
$$

There is no paradox. The degree-$52$ row used only Minkowski's inequality and was never asserted
to be optimal; the degree-$20$ row uses the stronger explicit formula.

### 7.5 Totally real improvements

For a totally real field, Minkowski has no $(\pi/4)$ loss. At degrees $6$ and $13$,

$$
M_6=4.0165977005\ldots>4,
$$

$$
M_{13}=5.2610732466\ldots>3^{3/2}.
$$

Thus the first two cutoffs improve to

$$
\operatorname{rd}(K)<4\Longrightarrow n\leq5,
$$

$$
\operatorname{rd}(K)<3^{3/2}\Longrightarrow n\leq12.
$$

For $\ell=5$, take $T=17/5$, $n=7$, and $\alpha=1$. Using $B_T<1.39923$ and $C_T<0.95923$ gives

$$
\begin{aligned}
\log\operatorname{rd}(K)
&>\gamma+\log(8\pi)+\frac\pi2
-\frac{34}{35}-1.39923-0.95923\\
&>2.04229,
\end{aligned}
$$

so

$$
\operatorname{rd}(K)>7.7082>5^{5/4}.
$$

Consequently a totally real field below the $5$-threshold has degree at most $6$.

### 7.6 Degree and signature grids

For intermediate signatures, no new theory is required. At fixed $T$ and $n$, solve

$$
\gamma+\log(8\pi)-\frac{2T}{n}-B_T
+\alpha\left(\frac\pi2-C_T\right)>\log U
$$

for $\alpha$. Because an actual signature satisfies $r_1\equiv n\pmod2$, only the finite grid

$$
\alpha\in\left\{\frac{n}{n},\frac{n-2}{n},\ldots\right\}
$$

occurs. This gives an explicit signature-by-degree exclusion algorithm. The totally real and unrestricted calculations above are its two endpoints.

## 8. Upper bounds force finite degree

### 8.1 Monotonicity in degree

For a fixed admissible $F$, write

$$
\log L_F(n,\alpha)=c_F(\alpha)-\frac{4A(F)}n.
$$

Since $A(F)>0$, this increases strictly with $n$. The optimized lower bound, being a supremum of increasing functions, is nondecreasing. Therefore, once a single test function proves $L_F(N,\alpha_0)>U$, it excludes every degree $n\geq N$ and every signature ratio at least $\alpha_0$.

Minkowski's $M_n$ is also increasing. The computations in Chapter 7 thus verify whole infinite ranges, not isolated degrees. This monotonicity is the small logical step that converts a numerical entry into a theorem.

### 8.2 The threshold principle

**Theorem 8.1 (unconditional threshold principle).** Fix $0\leq\alpha_0\leq1$ and

$$
U<4\pi e^{\gamma+\alpha_0}.
$$

Then there exists an explicit integer $N(U,\alpha_0)$ such that every number field $K$ satisfying

$$
\frac{r_1(K)}{[K:\mathbf Q]}\geq\alpha_0,
\qquad \operatorname{rd}(K)\leq U
$$

has degree less than $N(U,\alpha_0)$.

**Proof strategy.** Choose $T$ large enough that the limiting archimedean loss puts the infinite-degree test-function bound above $U$. Then choose $N$ large enough that the finite-degree penalty $2T/N$ does not erase the gap.

More explicitly, because

$$
B_T+\alpha_0 C_T
\longrightarrow
\log2+\alpha_0\left(\frac\pi2-1\right),
$$

the strict hypothesis allows a rational $T$ with

$$
\gamma+\log(8\pi)+\alpha_0\frac\pi2
-B_T-\alpha_0C_T>\log U.
$$

Choose $N$ so that subtracting $2T/N$ preserves the strict inequality. The explicit formula then excludes every $n\geq N$. $\square$

The strict gap $U<C$ is essential. The method gives no uniform degree bound exactly at the asymptotic constant. Infinite towers with root discriminants above, and sometimes close to, the threshold show that this is not a cosmetic issue.

### 8.3 Nonexistence, bounded degree, and finiteness

If a proposed field also has degree at least $N$, Theorem 8.1 proves nonexistence. Without such a degree lower bound, it proves only bounded degree. Hermite's theorem then says that there are only finitely many isomorphism classes of fields of bounded degree and bounded discriminant, because

$$
D_K=\operatorname{rd}(K)^n\leq U^{N-1}.
$$

For an increasing chain, bounded degree is stronger than mere finiteness of isomorphism classes: the integer sequence $[K_j:\mathbf Q]$ is nondecreasing and bounded, so it eventually becomes constant. An inclusion of finite fields of the same degree is equality. Hence the chain stabilizes.

This last conclusion uses nestedness. An infinite collection of pairwise nonnested subfields could repeat bounded degrees, although Hermite still makes it finite under a common discriminant bound.

## 9. Towers and the meaning of a threshold

### 9.1 Unramified class-field towers

If $K_{j+1}/K_j$ is unramified at every finite prime, then

$$
\operatorname{rd}(K_{j+1})=\operatorname{rd}(K_j).
$$

Thus an infinite unramified class-field tower has constant root discriminant. The unconditional threshold principle forces that constant to be at least

$$
4\pi e^\gamma=22.3816\ldots
$$

unless a persistent positive real proportion gives a stronger threshold. This does not prohibit class-field towers; it separates arithmetically possible large constants from impossible small ones.

The example also clarifies why the discriminant itself is the wrong invariant. Along an unramified tower,

$$
D_{K_j}=D_{K_0}^{[K_j:K_0]},
$$

which grows explosively even though no new finite ramification appears. Taking the degree root removes exactly that repeated base contribution.

### 9.2 Tame towers with bounded root discriminant

Let every finite Galois level $L/K$ be ramified only at a fixed finite set $S$ and tamely there. At $v\in S$ the normalized local different is

$$
\frac{d_v}{e_v}=1-\frac1{e_v}<1.
$$

Consequently

$$
\operatorname{rd}(L)
<\operatorname{rd}(K)
\prod_{v\in S}(Nv)^{1/[K:\mathbf Q]},
$$

independently of $[L:K]$. Tameness can therefore support bounded-root-discriminant towers. If the displayed upper constant is below the relevant analytic threshold, the tower cannot be infinite; if it is above, the analytic inequality alone gives no contradiction.

This is why “ramified at finitely many primes” is not enough. The sizes of those primes and the normalized ramification depths determine whether the field lies on the forbidden side of the threshold.

### 9.3 Cyclotomic towers as a warning

For odd $\ell$, the local different of $\mathbf Q_\ell(\zeta_{\ell^m})/\mathbf Q_\ell$ satisfies

$$
\frac{d}{e}=m-\frac1{\ell-1}.
$$

Globally the field is ramified only at $\ell$, so

$$
\operatorname{rd}(\mathbf Q(\zeta_{\ell^m}))
=\ell^{m-1/(\ell-1)}.
$$

The step degrees are eventually $\ell$, but the root discriminants tend to infinity. Moreover, $\mu_{\ell^m}$ is finite flat at every level. Thus neither finite flatness at all levels nor bounded successive degree supplies a uniform root-discriminant bound for the full $\ell$-power torsion tower.

At level $m=1$, the exact root discriminant is

$$
\ell^{1-1/(\ell-1)},
$$

well below the universal finite-flat upper threshold $\ell^{1+1/(\ell-1)}$. The universal estimate is designed to control arbitrary finite-flat modules, not to be sharp for the cyclotomic character.

### 9.4 The analytic obstruction to a small tower

**Theorem 9.1 (small-tower obstruction).** Let $K_1\subseteq K_2\subseteq\cdots$ be number fields with

$$
\operatorname{rd}(K_j)<U
$$

for all $j$. If either

$$
U<4\pi e^\gamma,
$$

or every $K_j$ has real proportion at least $\alpha_0>0$ and

$$
U<4\pi e^{\gamma+\alpha_0},
$$

then the tower stabilizes.

**Proof.** The threshold principle bounds all degrees. Nestedness then forces eventual equality. $\square$

The theorem is unconditional. Under the generalized Riemann hypothesis the corresponding constants may be replaced by $8\pi e^{\gamma+\alpha_0\pi/2}$, but that conditional improvement will not be used below.

## 10. Finite-flat torsion fields

### 10.1 The inherited upper bound

Let $F$ be a number field, let $\ell$ be a rational prime, and let $M$ be a finite global module killed by $\ell$. Put $L=F(M)$, the field over which the action becomes trivial. Assume:

- $L/F$ is unramified away from places above $\ell$;
- at every $v\mid\ell$, the local module is the generic fiber of a finite flat commutative group scheme over $\mathcal O_{F_v}$.

The local ramification estimate, proved in §10.5, gives

$$
\boxed{
\operatorname{rd}(L)
<\operatorname{rd}(F)\ell^{\ell/(\ell-1)}.
}
$$

This inequality is strict. At a completion above $\ell$, the upper break may occur at the endpoint, but the normalized different satisfies a strict degree-free inequality because the tame contribution is $1-1/e$, not $1$.

The bound is independent of the rank of $M$ and the size of its matrix image. That independence is precisely what allows analysis to constrain large images.

### 10.2 Bounded degree at one torsion level

Put

$$
U(F,\ell)=\operatorname{rd}(F)\ell^{\ell/(\ell-1)}.
$$

If

$$
U(F,\ell)<4\pi e^\gamma,
$$

then Theorem 8.1 gives an effectively computable bound

$$
[F(M):\mathbf Q]<N(U(F,\ell),0).
$$

If $F(M)$ is totally real, or has real proportion at least $\alpha_0$, one may replace the general threshold by $4\pi e^{\gamma+\alpha_0}$. This can recover a degree bound even when the general threshold fails.

The conclusion is bounded degree, not nonexistence. To prove nonexistence one needs an independent lower bound on the degree, perhaps arising from a large subgroup in the image. For example, if group theory shows that

$$
[F(M):\mathbf Q]\geq N(U,\alpha_0),
$$

the two bounds contradict each other. If it only shows divisibility by a certain integer, one must compare that divisibility with the finite list of degrees still allowed.

### 10.3 Auxiliary ramification

Suppose ramification away from $\ell$ occurs at a finite set $S$. If it is tame with inertia index $e_v$, the refined upper bound is

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)\ell^{\ell/(\ell-1)}
\prod_{v\in S}(Nv)^{(1-1/e_v)/[F:\mathbf Q]}.
$$

If only a last upper break $R_v$ is known, replace the exponent by $1+R_v$. These factors can push the upper bound across the analytic threshold. A prime of auxiliary ramification cannot be ignored merely because it differs from $\ell$.

As a worked example over $\mathbf Q$, one tame quadratic auxiliary prime $q$ gives

$$
\operatorname{rd}(L)<
\ell^{\ell/(\ell-1)}q^{1/2}.
$$

For $\ell=3$ and $q=2$, the threshold is

$$
3^{3/2}\sqrt2=7.348\ldots<22.381\ldots,
$$

so degree is still bounded unconditionally. For $q=101$ the same coarse upper bound is $52.22\ldots$, above the general asymptotic constant; the universal analytic comparison alone then says nothing about degree.

### 10.4 Base fields

The factor $\operatorname{rd}(F)$ is never optional. Absolute discriminant transitivity gives

$$
D_L=D_F^{[L:F]}N_{F/\mathbf Q}(\mathfrak d_{L/F}),
$$

so taking $[L:\mathbf Q]$th roots preserves one full factor of $\operatorname{rd}(F)$. Ramification of $F/\mathbf Q$ has already spent part of the analytic budget before the torsion field is adjoined.

The clean finite-flat exponent of $\ell$ remains independent of the splitting of $\ell$ in $F$. Indeed, if $e_v^0$ and $f_v^0$ are the local ramification and residue degrees, then

$$
\frac1{[F:\mathbf Q]}
\sum_{v\mid\ell}e_v^0f_v^0
\frac{\ell}{\ell-1}
=\frac\ell{\ell-1}.
$$

This cancellation concerns only the new relative ramification. It does not cancel $\operatorname{rd}(F)$.

### 10.5 Why the finite-flat exponent is uniform

The upper bound in §10.1 is the arithmetic half of Fontaine's argument, so we now reconstruct its
proof. The important feature is that the exponent depends on the power of $\ell$ annihilating the
module, but not on its rank.

Let $K/\mathbf Q_\ell$ be finite, put $R=\mathcal O_K$, normalize $v_K(K^\times)=\mathbf Z$, and
write

$$
e_K=v_K(\ell).
$$

Let $\mathcal G=\operatorname{Spec}A$ be a finite locally free commutative $R$-group scheme with
étale generic fiber. Its identity section is an augmentation $\varepsilon:A\to R$; write
$I=\ker\varepsilon$. For a geometric point $P:A\to\mathcal O_{\overline K}$, define its depth
from the identity by

$$
\nu(P)=\inf_{a\in I}v_K(P(a)).
$$

Because $I$ is a finite $R$-module, the infimum is attained on any finite set of generators. The
group law makes the same definition measure the distance between two points:

$$
\nu(P-Q)=\inf_{a\in A}v_K(P(a)-Q(a)).
\tag{10.1}
$$

This translation invariance is what an arbitrary finite flat algebra lacks.

The decisive Hopf-algebra estimate is

$$
[\ell]^*I\subseteq \ell I+I^\ell,
\qquad
[\ell]^*a-\ell a\in\ell I^2+I^\ell
\quad(a\in I).
\tag{10.2}
$$

To prove it, choose generators of $I$ and express multiplication by $\ell$ through the iterated
comultiplication. The degree-one contribution is the sum of the same generator in the $\ell$
tensor positions, hence becomes $\ell a$. Modulo $\ell$, multiplication by $\ell$ on a
commutative group factors through relative Frobenius. Its pullback carries the augmentation ideal
into its $\ell$th power. Equivalently, every homogeneous contribution of degree strictly between
$1$ and $\ell$ has a multinomial coefficient divisible by $\ell$. Lifting from $R/\ell R$ gives
(10.2), including the sharper assertion about the linear term.

Suppose now that $P$ is killed by $\ell$ and set $r=\nu(P)>0$. Choose a generator $a$ attaining
$r$. Evaluating $[\ell]^*a$ at $P$ produces a sum whose linear term $\ell P(a)$ has valuation
$e_K+r$, whose terms in $\ell I^2$ have valuation at least $e_K+2r$, and whose terms in $I^\ell$
have valuation at least $\ell r$. If

$$
r>\frac{e_K}{\ell-1},
$$

then $e_K+r<\ell r$, so the linear term is uniquely of least valuation. A nonarchimedean sum with
a unique least-valuation term cannot be zero. This contradicts $[\ell]P=0$ unless $P=0$.

The same ball contains no nonzero point killed by any power of $\ell$. Indeed, (10.2) gives

$$
\nu([\ell]P)\geq\min\{e_K+\nu(P),\ell\nu(P)\}.
$$

If $\nu(P)>e_K/(\ell-1)$, the right side is again greater than that radius. Induction on the
exponent reduces to the order-$\ell$ case. By (10.1), any two distinct $\ell$-power torsion points
are therefore separated by some integral function at depth at most

$$
c=\frac{e_K}{\ell-1}.
\tag{10.3}
$$

For $\mu_\ell$, a primitive root satisfies
$v_K(\zeta_\ell-1)=e_K/(\ell-1)$, so the strict radius cannot be improved uniformly.

It remains to convert separation of points into an upper ramification cutoff. We state the bridge
with its endpoint, since confusing the radius with the ramification break loses $e_K-1$ over a
ramified base.

**Lemma 10.1 (congruence to ramification).** Suppose a finite locally free commutative
$R$-group scheme is killed by $\ell^a$, its generic fiber is étale, and every two distinct
geometric points are separated at depth at most $c$. Then the upper ramification group $G_K^u$
acts trivially on its geometric points for

$$
u>e_Ka+c-1.
\tag{10.4}
$$

**Proof.** Choose a finite Galois extension $E/K$ splitting every point. For $r\geq0$, put two
points in the same $r$-class when every integral function takes values differing by valuation
greater than $r$. Translation shows that every nonempty class is a coset of the class of zero;
all classes consequently have equal size. As $r$ passes the finitely many critical distances,
the stabilizers of the classes form a filtration of $\operatorname{Gal}(E/K)$.

Measure distances with $v_E$. An interval of $v_K$-length $b$ has $v_E$-length
$e(E/K)b$. When a congruence class has $h$ points, its conjugates form equal blocks, and the
index of its stabilizer divides this raw length in the Herbrand integral. Thus the factor
$e(E/K)$ cancels when the filtration is converted to upper numbering. This is the orbit count
behind quotient compatibility of upper ramification groups.

Refine the zero class by its intersections with the kernels of $[\ell^j]$, for
$1\leq j\leq a$. Let $b_j$ be the last upper parameter at which the action on the order
$\ell^j$ layer can be nontrivial. At the terminal order-$\ell$ layer, multiplication by $\ell$
contributes $e_K$, separation contributes at most $c$, and the isolated tame inertia term
contributes the shift $-1$. Hence

$$
b_1\leq e_K+c-1.
$$

For each lift from the $\ell^{j-1}$-layer to the $\ell^j$-layer, (10.2) spends at most one further
$v_K(\ell)=e_K$ on the upper clock. Therefore

$$
b_j\leq b_{j-1}+e_K.
$$

Induction gives $b_a\leq e_Ka+c-1$. Above that value every difference of points is fixed, so every
point is fixed. Enlarging $E$ does not alter the conclusion because upper numbering passes to
quotients. $\square$

Combining (10.3) and (10.4) yields the finite-flat ramification theorem.

**Theorem 10.2 (finite-flat upper break).** Let $M$ be a finite continuous $G_K$-module killed by
$\ell^a$. If $M$ is the generic fiber of a finite locally free commutative group scheme over
$R$, then

$$
G_K^u\text{ acts trivially on }M
\quad\text{for every}\quad
u>e_K\left(a+\frac1{\ell-1}\right)-1.
\tag{10.5}
$$

Let $E=K(M)$ and let $e=e(E/K)$ and $d=d(E/K)$. Hilbert's different formula in upper numbering is

$$
d=(e-1)+e\int_0^\infty
\left(1-\frac1{|G^u|}\right)du.
\tag{10.6}
$$

The cutoff (10.5) and the bound of the integrand by $1$ give

$$
d\leq e\,e_K\left(a+\frac1{\ell-1}\right)-1,
$$

and hence

$$
\boxed{
\frac de<e_K\left(a+\frac1{\ell-1}\right).}
\tag{10.7}
$$

The strict sign in (10.7) comes from the surviving $-1/e$, not from removing the possible endpoint
break in (10.5). For $a=1$ and $K/\mathbf Q_\ell$ unramified, the last upper break is at most
$1/(\ell-1)$ while the normalized different is strictly less than $\ell/(\ell-1)$. These are
different constants with different meanings.

Finally let $F$ be a number field and $L=F(M)$. At a place $v\mid\ell$, put
$e_v^0=e(F_v/\mathbf Q_\ell)$ and $f_v^0=f(F_v/\mathbf Q_\ell)$. The exact global formula is

$$
\operatorname{rd}(L)=\operatorname{rd}(F)
\prod_v(Nv)^{d_v/(e_v[F:\mathbf Q])}.
\tag{10.8}
$$

Using (10.7) at all $v\mid\ell$ and
$\sum_{v\mid\ell}e_v^0f_v^0=[F:\mathbf Q]$ gives

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)\ell^{a+1/(\ell-1)}
$$

when no other finite prime ramifies. This proves §10.1, and also proves the general exponent-$a$
form needed to diagnose higher torsion levels.

### 10.6 The residual three-adic ledger

We now specialize every factor rather than hiding it under the phrase “small ramification.” Let
$M$ be a finite $G_{\mathbf Q}$-module killed by $3$, possessing a finite-flat model at $3$, and
let $L=\mathbf Q(M)$. At $3$, Theorem 10.2 gives last upper break at most $1/2$ and

$$
\frac{d_3}{e_3}<\frac32.
\tag{10.9}
$$

If $L$ is unramified outside $3$, then

$$
\boxed{\operatorname{rd}(L)<3^{3/2}.}
\tag{10.10}
$$

The strongest certified degree consequence in this book is nevertheless $[L:\mathbf Q]\leq20$,
by (7.4). The degree-$52$ Minkowski row remains a useful independent check, but is weaker.

If $L$ is also ramified at $2$ and the inertia image there has order $3$, it is tame because the
residue characteristic is $2$. Its positive ramification groups vanish, so

$$
d_2=e_2-1=2,
\qquad
\frac{d_2}{e_2}=\frac23.
\tag{10.11}
$$

An unramified part at $2$ changes the residue degree but not either value in (10.11). Formula
(10.8) now gives the exact two-prime ceiling

$$
\boxed{
\operatorname{rd}(L)<3^{3/2}2^{2/3}.}
\tag{10.12}
$$

If inertia at $2$ is trivial, its factor is $1$, not $2^{2/3}$. If its order is an arbitrary odd
power $3^b$, the exact tame factor is

$$
2^{1-3^{-b}}.
$$

No assertion about $b$ follows from finite flatness at $3$; it is separate local information.

The coefficient exponent also matters. Let $\mathcal O$ be the integers of a finite extension of
$\mathbf Q_3$, choose a uniformizer $\varpi$, and write

$$
e_{\mathcal O}=v_\varpi(3).
$$

For a free $\mathcal O$-lattice $T$, the quotient $T/\varpi^nT$ is killed by

$$
3^{m(n)},
\qquad
m(n)=\left\lceil\frac{n}{e_{\mathcal O}}\right\rceil,
\tag{10.13}
$$

and, when $T\ne0$, by no smaller power. Thus the full-level three-adic bound is

$$
\operatorname{rd}\bigl(\mathbf Q(T/\varpi^nT)\bigr)
<3^{m(n)+1/2}
$$

before auxiliary factors. Only at residual level is $m(1)=1$ automatically. A first-order
difference module arising at a high coefficient level can return to the residual ceiling if its
underlying additive group is killed by $3$ and an actual finite-flat model of the whole difference
module is supplied. Finite flatness of its diagonal constituents alone does not control an
off-diagonal extension class.

For rank two over $\mathbf F_3$, the matrix degree bound is

$$
[L:\mathbf Q]leq|\operatorname{GL}_2(\mathbf F_3)|
=(3^2-1)(3^2-3)=48.
\tag{10.14}
$$

The determinant-one subgroup has order $24$. The analytic bounds do not replace these image
calculations; their force comes from simultaneous comparison with (10.10) or (10.12).

## 11. Fontaine's stabilization mechanism

### 11.1 The maximal small-ramification compositum

The most effective form of Fontaine's method does not begin with the full $\ell$-power torsion tower. It begins with a class of exponent-$\ell$ fields whose finite composita retain one uniform ramification bound.

Fix $F$, $\ell$, and a finite set $S$ of auxiliary places with prescribed local cutoffs. Let $\mathscr C$ be a collection of finite global modules such that:

1. every $M\in\mathscr C$ is killed by $\ell$;
2. every $M$ has a finite-flat local model at $v\mid\ell$;
3. every $M$ is unramified away from $S\cup\{v:v\mid\ell\}$ and satisfies the fixed cutoff at $S$;
4. every finite direct sum of objects of $\mathscr C$ again has the same local properties.

Let

$$
\Omega_{\mathscr C}=\prod_{M\in\mathscr C}F(M)
$$

inside a fixed algebraic closure, where the product means the directed compositum. Every finite subcompositum is cut out by a finite direct sum. It therefore satisfies the single upper bound

$$
\operatorname{rd}(E)<U_{\mathscr C},
$$

where

$$
U_{\mathscr C}=
\operatorname{rd}(F)\ell^{\ell/(\ell-1)}
\prod_{v\in S}(Nv)^{b_v/[F:\mathbf Q]}
$$

and $b_v=1+R_v$, or the sharper tame value $1-1/e_v$ when available.

This construction is the reason direct-sum closure matters. Applying a generic compositum discriminant inequality to $m$ fields would multiply $m$ upper factors and destroy uniformity. A finite-flat product model retains the maximum local upper break, so the same $U_{\mathscr C}$ works for every finite subcompositum.

### 11.2 Uniform exponent-$\ell$ layers

Assume

$$
U_{\mathscr C}<4\pi e^\gamma.
$$

The threshold principle bounds the absolute degree of every finite subcompositum by one integer $N$. Since the subcomposita form a directed set, their degrees form a directed set of positive integers bounded by $N$. Choose one of maximal degree, say $E$. Any other finite subcompositum $E'$ lies in the finite subcompositum $EE'$, whose degree cannot exceed the maximal degree. Hence

$$
EE'=E,
$$

so $E'\subseteq E$. It follows that

$$
\boxed{\Omega_{\mathscr C}=E\text{ is a finite extension of }F.}
$$

This is stronger than saying that each individual field has bounded degree. It says that all fields in the class live inside one finite extension. The proof uses closure under finite composita, uniform root discriminant, and analytic degree boundedness in exactly that order.

If every finite subcompositum is totally real, the weaker numerical condition

$$
U_{\mathscr C}<4\pi e^{1+\gamma}
$$

suffices. More generally, a uniform real-proportion lower bound $\alpha_0$ permits $4\pi e^{\gamma+\alpha_0}$.

### 11.3 From bounded degree to stabilization

Let

$$
E_1\subseteq E_2\subseteq\cdots\subseteq\Omega_{\mathscr C}
$$

be fields assembled from objects of $\mathscr C$. Since $\Omega_{\mathscr C}/F$ is finite, the chain stabilizes. Equivalently, there are only finitely many possible kernels for the corresponding finite actions once all their fields are required to lie in the same small-ramification compositum.

In representation-theoretic language, suppose a profinite action has finite quotients whose cutout fields form such a chain. If the chain stabilizes at $E_N$, then every later quotient factors through

$$
\operatorname{Gal}(E_N/F).
$$

If those quotients separate the profinite image, the whole image is finite. This last separation holds, for example, for the quotients of a faithful $\mathbf Z_\ell$-lattice: an automorphism congruent to the identity modulo $\ell^m$ for every $m$ is the identity.

Thus the analytic argument can force a finite image, but only after arithmetic has placed all relevant quotient fields in one uniformly bounded compositum.

### 11.4 Successive torsion fields

Let $T$ be a free $\mathbf Z_\ell$-module of finite rank with continuous global action, and put

$$
K_m=F(T/\ell^mT).
$$

Then

$$
K_1\subseteq K_2\subseteq\cdots,
$$

and the successive kernel groups are $\ell$-groups of bounded order. If every $T/\ell^mT$ has a finite-flat model at $\ell$, the established full-level estimate is only

$$
\operatorname{rd}(K_m)
<\operatorname{rd}(F)\ell^{m+1/(\ell-1)}
$$

when there is no auxiliary ramification. This grows with $m$ and cannot be inserted into Theorem 9.1.

The safe Fontaine passage therefore has an additional hypothesis. Suppose for every $m$ there are modules

$$
M_{m,1},\ldots,M_{m,a_m}\in\mathscr C
$$

such that

$$
K_m\subseteq K_1
F(M_{m,1})\cdots F(M_{m,a_m}).
$$

Then every $K_m$ lies in the fixed finite field $K_1\Omega_{\mathscr C}$, so the torsion tower stabilizes and the image on $T$ is finite.

This hypothesis says that the successive congruence information descends to exponent-$\ell$ objects over the fixed base with the required integral models. Merely observing that

$$
\operatorname{Gal}(K_{m+1}/K_m)
$$

has exponent $\ell$ does not provide that descent. It is a module over the moving base $K_m$, and applying the finite-flat estimate there reintroduces $\operatorname{rd}(K_m)$.

### 11.5 The missing group-theoretic bridge

The analytic argument ends at one of two points:

- all fields in the chosen exponent-$\ell$ category lie in a finite maximal field;
- a torsion tower satisfying the descent condition stabilizes, so its image is finite.

To obtain a classification of a representation, one still needs group-theoretic and arithmetic input. Typical required statements include:

1. a description of residual simple constituents, often trivial or cyclotomic;
2. control of extension classes, showing that congruence layers are realized by the fixed exponent-$\ell$ category;
3. a Frattini or generation argument converting restrictions on elementary quotients into restrictions on the pro-$\ell$ kernel;
4. determinant, duality, and parity constraints;
5. classification of the remaining finite subgroups of the relevant linear group.

None follows from a root-discriminant inequality. In particular, finite image does not imply reducibility, and bounded degree does not determine the semisimplification. The next stage of the theory supplies these group-theoretic inputs.

### 11.6 Forbidden large torsion fields

We can now state the exclusion furnished by Fontaine's comparison without folding later
classification into it.

**Theorem 11.1 (two-prime forbidden-field theorem).** Let $M$ be a finite
$\mathbf F_3$-representation of $G_{\mathbf Q}$ satisfying the following hypotheses:

- $M$ is the generic fiber of a finite locally free commutative group scheme over $\mathbf Z_3$;
- the cutout field $L=\mathbf Q(M)$ is unramified outside $\{2,3\}$;
- inertia at $2$ is either trivial or cyclic of order $3$.

Then

$$
[L:\mathbf Q]\leq20.
\tag{11.1}
$$

Consequently the image of $G_{\mathbf Q}$ on $M$ cannot have order divisible by $24$. In
particular, when $M$ has dimension two, its image is neither
$\operatorname{SL}_2(\mathbf F_3)$ nor $\operatorname{GL}_2(\mathbf F_3)$.

**Proof.** The whole module is killed by $3$, so its model gives the strict local exponent
$d_3/e_3<3/2$. If inertia at $2$ is trivial, the factor at $2$ is absent; if it has order $3$, the
exact tame exponent is $2/3$. In both cases

$$
\operatorname{rd}(L)<3^{3/2}2^{2/3}.
$$

The certified comparison (7.3) gives $[L:\mathbf Q]\leq20$. Because $L/\mathbf Q$ is Galois,
its degree is the order of the image. An image whose order is divisible by $24$ would give degree
at least $24$, a contradiction. The two named groups have orders $24$ and $48$. $\square$

There are two useful quotient forms. If a projective representation attached to $M$ has image
$\operatorname{PGL}_2(\mathbf F_3)$, its projective cutout field is a Galois subfield of degree

$$
|\operatorname{PGL}_2(\mathbf F_3)|=24.
$$

Root discriminants decrease on passage to subfields, so this already contradicts (11.1).
Equivalently, upper ramification cutoffs pass to quotient actions. Also, if the linear image
contains $\operatorname{SL}_2(\mathbf F_3)$ and the determinant is surjective, then it is all of
$\operatorname{GL}_2(\mathbf F_3)$: the determinant-one subgroup has index two and the image meets
the other coset. The theorem excludes this common large-image alternative.

The hypotheses attach to the full faithful action. Knowing only that the semisimplification has
small constituents is insufficient: a nontrivial extension class can cut out a larger unipotent
field. Conversely, once a full affine or difference representation is killed by $3$ and has its
own finite-flat model, its dimension is irrelevant to the discriminant estimate. The same degree
cap applies.

The theorem also persists under finite composita of such modeled exponent-three fields. Products
of the models give a model of the direct sum, still killed by $3$. At $2$, tame inertia is a finite
cyclic quotient of tame inertia. If every summand has exponent-three inertial image, the direct
sum image is cyclic of order at most $3$, not a product of arbitrarily many independent cubic
groups. Thus the factor $2^{2/3}$ is paid once. Every finite subcompositum again has degree at most
$20$, so the directed compositum is finite by the maximal-degree argument of §11.2.

If inertia at $2$ is absent, one has the stronger arithmetic inequality

$$
\operatorname{rd}(L)<3^{3/2},
$$

and the same degree-$20$ conclusion follows because $3^{3/2}<3^{3/2}2^{2/3}$. The separate
degree-$52$ Minkowski calculation is valid but not optimal after the explicit-formula certificate
has been established. In particular, the universal root-discriminant comparison does exclude
the full $\operatorname{GL}_2(\mathbf F_3)$ image in the three-only case as well.

Finally, the theorem is a fixed-exponent result. For $T/3^nT$, the safe upper bound grows like
$3^{n+1/2}$ and cannot be compared with the fixed certificate (7.3). To use Theorem 11.1 at a high
lifting stage, the obstruction must be represented by a new exponent-three module over the fixed
base, with the stated local models and ramification. This is Fontaine's stabilization mechanism in
its precise form: return each first-order obstruction to one uniformly bounded category, rather
than pretend that the full torsion tower has a uniform discriminant.

## 12. Small-prime calculations

### 12.1 The prime 2

Over $\mathbf Q$, a module killed by $2$, finite flat at $2$, and unramified away from $2$ cuts out a field $L$ satisfying

$$
\operatorname{rd}(L)<2^{2}=4.
$$

Chapter 7 gives

$$
[L:\mathbf Q]\leq11.
$$

If $L$ is totally real, the stronger bound is

$$
[L:\mathbf Q]\leq5.
$$

Because $L/\mathbf Q$ is Galois, these bounds constrain the group order. If separate structure shows that the image is a $2$-group, its order is a power of $2$; hence

$$
[L:\mathbf Q]\leq8
$$

in general and at most $4$ in the totally real case. The $2$-group hypothesis is not analytic. It often comes from a filtration with trivial one-dimensional factors, since the mod-$2$ cyclotomic character is itself trivial.

The strict upper bound matters. The analytic conclusion is valid for $\operatorname{rd}(L)<4$. It would also follow from a weak upper bound $\operatorname{rd}(L)\leq4$ because the degree-$12$ lower bound is strictly greater than $4$, but the arithmetic theorem naturally supplies the stronger sign.

### 12.2 The prime 3

At $3$ the upper bound is

$$
\operatorname{rd}(L)<3^{3/2}=5.1961524227\ldots,
$$

and the standalone Minkowski calculation gives

$$
[L:\mathbf Q]\leq52.
$$

The explicit-formula certificate of §7.4 is stronger: because
$3^{3/2}<3^{3/2}2^{2/3}$, it gives

$$
[L:\mathbf Q]\leq20.
$$

If $L$ is totally real, then

$$
[L:\mathbf Q]\leq12.
$$

Suppose additional residual structure shows that the image is an extension of a $3$-group by a group of order dividing $2$, as happens when all diagonal constituents are trivial or cyclotomic. Then its order divides $2\cdot3^a$. The strongest degree cap leaves only

$$
1,2,3,6,9,18.
$$

If the cyclotomic quotient of order $2$ is known to occur, only the even entries remain. If the field is totally real, complex conjugation is trivial in the Galois group and the cyclotomic constituent at $3$ cannot occur nontrivially; that is a group-theoretic signature constraint, not part of the analytic estimate.

These reductions are often enough to turn an unmanageably large matrix group into a short finite list. They do not decide which listed groups actually arise.

### 12.3 The prime 5

For $\ell=5$,

$$
\operatorname{rd}(L)<5^{5/4}=7.4767439061\ldots.
$$

Minkowski alone cannot bound the degree because $5^{5/4}>e^2$. The unconditional explicit-formula calculation gives

$$
[L:\mathbf Q]\leq16,
$$

and the totally real refinement gives

$$
[L:\mathbf Q]\leq6.
$$

If separate structure makes the image an extension of a $5$-group by a subgroup of $\mathbf F_5^\times$, its order divides $4\cdot5^a$. Under the unrestricted cap, the $5$-part has order at most $5$; possible orders are among

$$
1,2,4,5,10.
$$

Under the totally real cap only $1,2,4,5$ remain. Again, this list records divisibility plus analysis; realizing or eliminating an entry requires further arithmetic.

The prime $5$ calculation displays the genuine gain from Odlyzko--Poitou theory. It crosses a threshold that geometry of numbers cannot cross even asymptotically.

As a concrete nonexistence test, a surjective two-dimensional action has degree

$$
|\operatorname{GL}_2(\mathbf F_\ell)|
=(\ell^2-1)(\ell^2-\ell).
$$

For $\ell=2,3,5$ these orders are respectively

$$
6,\qquad48,\qquad480.
$$

The unrestricted $2$-bound does not exclude the first image because $6\leq11$. The strongest
$3$-bound does exclude the second because $48>20$, and the $5$-bound excludes the third because
$480>16$. Therefore there is no surjective action

$$
G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathbf F_5)
$$

whose cutout field is unramified away from $5$ and whose local module at $5$ is finite flat. This is a genuine nonexistence conclusion, not merely bounded degree. If an independent hypothesis makes a cutout field totally real, the smaller signature caps can exclude additional images; one must first check compatibility of that hypothesis with complex conjugation and the determinant.

Likewise, there is no surjective action to $\operatorname{GL}_2(\mathbf F_3)$ whose cutout field is
unramified away from $3$ and whose local module at $3$ is finite flat. This conclusion uses the
degree-$20$ explicit-formula row, not the weaker degree-$52$ Minkowski row.

### 12.4 Strict and weak inequalities

Suppose arithmetic gives $\operatorname{rd}(L)<U$ and analysis gives $\operatorname{rd}(L)\geq A_n$. A contradiction follows when

$$
A_n\geq U.
$$

If arithmetic gives only $\operatorname{rd}(L)\leq U$, one needs

$$
A_n>U
$$

unless equality is ruled out independently. Our finite computations use a visible positive margin, so they remain valid under either upper-bound convention.

At the asymptotic level, the hypothesis is strictly

$$
U<C(\alpha_0).
$$

Equality with the limiting constant gives no finite-degree cutoff by this argument. Likewise, the local statement that an upper ramification group is trivial for $u>R$ allows a break at $R$; the strict root-discriminant inequality comes instead from the $-1/e$ in the normalized different. These are distinct endpoint phenomena.

### 12.5 The prime 3 with tame cubic inertia at 2

The two-prime row is the one that changes a degree estimate into a large-image exclusion. Let
$L/\mathbf Q$ be the field cut out by an exponent-three module finite flat at $3$. Suppose its only
other ramification is tame at $2$, with inertia of order at most $3$. Then

$$
\operatorname{rd}(L)<3^{3/2}2^{2/3}
$$

and §7.4 gives

$$
[L:\mathbf Q]\leq20.
\tag{12.1}
$$

This conclusion is stronger than combining separate one-prime estimates. The exponent $3/2$ at
$3$ already includes the tame baseline there, and the exponent $2/3$ at $2$ is exact. There is no
additional factor $2$, no factor counting the number of primes above $2$, and no multiplication by
the representation dimension.

For a two-dimensional $\mathbf F_3$-module, the complete matrix group has order $48$ and its
determinant-one subgroup has order $24$. Both are impossible by (12.1). A Borel subgroup has order

$$
(3-1)^2\cdot3=12,
$$

so the analytic cap does not exclude reducible upper-triangular actions. A nonsplit Cartan has
order $3^2-1=8$, and its normalizer has order $16$; these too fit below the cap. Thus the numerical
comparison separates genuinely large images from several small irreducible or reducible
possibilities, but it does not itself decide among the survivors.

The subgroup arithmetic makes the division of labor clear. If an independent argument proves
that the image contains $\operatorname{SL}_2(\mathbf F_3)$, then the degree is at least $24$ and
Fontaine's comparison gives an immediate contradiction. If all that is known is irreducibility,
the image might have order $8$ or $16$, so no contradiction follows. Irreducible, large, and
surjective are distinct hypotheses at this exceptional small prime.

The same caution applies to projective images. The scalar subgroup of
$\operatorname{GL}_2(\mathbf F_3)$ has order $2$, so passage to the projective field can halve the
degree. A projective image $S_4$ has order $24$ and is excluded; a projective image $A_4$ has order
$12$ and is not. Quotienting never worsens the ramification ceiling, but it can move the degree
below the analytic cutoff.

## 13. Signature and base-field refinements

### 13.1 Totally real fields

A totally real torsion field benefits twice. Analytically, its asymptotic threshold rises from

$$
4\pi e^\gamma=22.3816\ldots
$$

to

$$
4\pi e^{1+\gamma}=60.8395\ldots.
$$

At finite degree, the $\alpha C(F)$ term in the explicit inequality improves the bound, and Minkowski loses no factor $(\pi/4)^{1-\alpha}$. These improvements produced the degree caps $5$, $12$, and $6$ at the primes $2$, $3$, and $5$.

Totally real must refer to the field to which the lower bound is applied. A totally real base field can acquire complex embeddings in an extension. Conversely, a representation with a suitable parity condition may force its cutout field to be totally real, because complex conjugations lie in its kernel. That parity statement must be proved from the action.

### 13.2 Intermediate signatures

Let every field in a family satisfy

$$
r_1\geq\alpha_0 n.
$$

Then the unconditional asymptotic threshold is

$$
4\pi e^{\gamma+\alpha_0}.
$$

For the triangular finite bound, the gain over the totally imaginary estimate is

$$
\alpha_0\left(\frac\pi2-C_T\right)
$$

in the logarithm. Since $C_T<\pi/2$, any positive guaranteed real proportion helps. The integer constraints $r_1+2r_2=n$ should be imposed only after obtaining the continuous bound; they can sharpen the last one or two borderline degrees.

A counterexample to careless signature inheritance is a real quadratic base $F$ and the extension $F(i)$. The base is totally real, but the extension has no real embedding. Any lower bound for $F(i)$ must use $\alpha=0$.

### 13.3 Relative small ramification

Let $F$ be arbitrary and let $L/F$ be cut out by a level-$\ell$ finite-flat module, with auxiliary local factors summarized by $Q_S$. Then

$$
\operatorname{rd}(L)<
\underbrace{\operatorname{rd}(F)
\ell^{\ell/(\ell-1)}Q_S}_{U(F,\ell,S)}.
$$

If

$$
U(F,\ell,S)<4\pi e^{\gamma+\alpha_0}
$$

and the cutout field has real proportion at least $\alpha_0$, its absolute degree is effectively bounded. Consequently its relative degree is bounded by

$$
[L:F]\leq
\left\lfloor\frac{N(U,\alpha_0)-1}{[F:\mathbf Q]}\right\rfloor.
$$

This formula makes the role of the base field transparent. A larger base degree reduces the relative room once an absolute degree cap is known, while a larger base root discriminant consumes more of the analytic threshold.

### 13.4 A worked base-field comparison

Take

$$
F=\mathbf Q(\sqrt5),
\qquad \operatorname{rd}(F)=\sqrt5.
$$

For a level-$2$ module finite flat above $2$ and unramified elsewhere,

$$
\operatorname{rd}(L)<4\sqrt5
=8.9442719099\ldots.
$$

This is below the general unconditional asymptotic constant even if $L$ is not totally real. Using $T=6$ in the unconditional triangular family gives

$$
A_T=3,
\qquad 1.10355<B_T<1.10356.
$$

At $n=24$ and $\alpha=0$,

$$
\log\operatorname{rd}(L)
>\gamma+\log(8\pi)-\frac{12}{24}-1.10356
>2.19782,
$$

so

$$
\operatorname{rd}(L)>9.0053>4\sqrt5.
$$

Therefore

$$
[L:\mathbf Q]\leq23.
$$

Since $[F:\mathbf Q]=2$ divides $[L:\mathbf Q]$, in fact

$$
[L:F]\leq11.
$$

Had the factor $\sqrt5$ been omitted, one would have claimed the much smaller $\mathbf Q$-threshold $4$ and obtained a false degree estimate.

## 14. Comparative examples and counterexamples

### 14.1 Tame-only fields

Suppose $L/\mathbf Q$ is Galois and tamely ramified only at distinct rational primes $q_1,\ldots,q_s$. If the inertia orders are $e_i$, then

$$
\operatorname{rd}(L)
=\prod_{i=1}^s q_i^{1-1/e_i}
<\prod_{i=1}^s q_i.
$$

For a quadratic field of odd squarefree discriminant $d$, every ramified odd prime has $e_i=2$, and the root discriminant is $|d|^{1/2}$, agreeing with the formula. At $2$, wild or discriminant-congruence effects require separate treatment.

The example shows why tame ramification is cheap but not free. Adding a new large tame prime can raise the root discriminant more than deep ramification at a small prime. Analytic arguments compare the total logarithmic cost, not a count of ramified primes.

### 14.2 Cyclotomic fields

For odd $\ell$ and $m\geq1$,

$$
[\mathbf Q(\zeta_{\ell^m}):\mathbf Q]
=\ell^{m-1}(\ell-1),
$$

and

$$
\operatorname{rd}(\mathbf Q(\zeta_{\ell^m}))
=\ell^{m-1/(\ell-1)}.
$$

At $m=1$ this is a tame field. For $m>1$ the wild depth grows linearly with $m$. Every torsion group involved is finite flat, yet the tower has unbounded root discriminant. This is the canonical counterexample to replacing “killed by $\ell$ over a fixed base” with “killed by some power of $\ell$.”

For $\ell=3$, the first level has root discriminant $\sqrt3$, while the universal level-$3$ estimate is $3^{3/2}$. At level $m$, the exact exponent is $m-1/2$ and the universal full-level exponent is $m+1/2$. The gap is constant, but both grow. No asymptotic analytic threshold can stabilize this tower.

### 14.3 Finite-flat exponent-$\ell$ families

Now let $M_1,\ldots,M_s$ be modules over a fixed $F$, each killed by $\ell$, each finite flat above $\ell$, and all unramified away from the same controlled set. Their direct sum is still killed by $\ell$, and its cutout field is the compositum

$$
F(M_1)\cdots F(M_s).
$$

The upper bound is independent of $s$. If it lies below the analytic threshold, the degrees of all such finite composita are bounded, so the compositum over every member of the family is finite.

This family has the uniformity absent from the cyclotomic tower. The distinction is exponent, not merely finite flatness: direct sums of exponent-$\ell$ objects remain exponent $\ell$, while $\mu_{\ell^m}$ has increasing exponent.

### 14.4 Why bounded step degree is not enough

Consider any nested sequence with

$$
[K_{m+1}:K_m]\leq C.
$$

Then $[K_m:K_1]\leq C^{m-1}$, which still tends to infinity. The cyclotomic tower realizes this behavior with $C=\ell$. Its normalized local different grows even though the number of new automorphisms at each step is bounded.

Nor does a bound on the abstract order of each relative Galois group control its ramification depth. Cyclic extensions of fixed prime degree can have arbitrarily large upper breaks. The Fontaine mechanism needs both ingredients:

- finite composita remain in a class with a uniform absolute root-discriminant bound;
- analysis converts that uniform bound into a uniform absolute degree bound.

Dropping either condition leaves standard infinite towers untouched.

## 15. A theorem package for the next stage

### 15.1 Analytic degree cutoff

**Theorem 15.1 (explicit Odlyzko--Poitou cutoff).** Let $K$ be a number field of degree $n$, with $\alpha=r_1/n$. For $T>0$, put

$$
F_T(x)=\frac{(1-|x|/T)_+}{\cosh(x/2)}
$$

and define $B_T,C_T$ as in Chapter 5. Then, unconditionally,

$$
\boxed{
\operatorname{rd}(K)\geq
\exp\left(
\gamma+\log(8\pi)+\alpha\frac\pi2
-\frac{2T}{n}-B_T-\alpha C_T
\right).
}
$$

Consequently, for every $U<4\pi e^{\gamma+\alpha_0}$ there is an explicit $N(U,\alpha_0)$ such that

$$
\operatorname{rd}(K)\leq U,
\qquad \alpha\geq\alpha_0
$$

imply $n<N(U,\alpha_0)$.

Under the generalized Riemann hypothesis one may instead use any nonnegative $F$ with nonnegative Fourier transform and obtains the asymptotic threshold

$$
8\pi e^{\gamma+\alpha_0\pi/2}.
$$

This conditional sentence is not used in Theorems 15.2 or 15.3.

### 15.2 Finite-flat cutoff

**Theorem 15.2 (finite-flat field bound).** Let $F$ be a number field and $M$ a finite global module killed by $\ell$. Assume that $M$ is finite flat at every place above $\ell$, unramified outside those places and a finite set $S$, and has normalized auxiliary local costs $b_v$ at $v\in S$. For $L=F(M)$,

$$
\boxed{
\operatorname{rd}(L)<U,
\qquad
U=\operatorname{rd}(F)\ell^{\ell/(\ell-1)}
\prod_{v\in S}(Nv)^{b_v/[F:\mathbf Q]}.
}
$$

Here $b_v=1-1/e_v$ for known tame ramification, while $b_v=1+R_v$ is valid for last upper break at most $R_v$. If

$$
U<4\pi e^{\gamma+\alpha_0}
$$

and $r_1(L)/[L:\mathbf Q]\geq\alpha_0$, then $[L:\mathbf Q]$ is explicitly bounded by Theorem 15.1.

Over $\mathbf Q$, with $S=\varnothing$, the following unconditional conclusions hold:

$$
\begin{array}{c|c|c|c}
\ell&U&[L:\mathbf Q]\text{, arbitrary signature}
&[L:\mathbf Q]\text{, totally real}\\
\hline
2&4&\leq11&\leq5\\
3&3^{3/2}&\leq20&\leq12\\
5&5^{5/4}&\leq16&\leq6.
\end{array}
$$

The upper inequalities for root discriminants are strict; the degree conclusions are weak
inequalities because degrees are integers. The arbitrary-signature entry $20$ at $3$ uses the
explicit-formula certificate for the larger ceiling $3^{3/2}2^{2/3}$; the independent Minkowski
row gives the weaker but still valid value $52$.

There is one additional certified row with $S\ne\varnothing$. For $\ell=3$, if the only auxiliary
place is $2$ and its inertia has order at most $3$, then

$$
\operatorname{rd}(L)<3^{3/2}2^{2/3}
\quad\Longrightarrow\quad
[L:\mathbf Q]\leq20.
\tag{15.1}
$$

Thus no such faithful action has image order divisible by $24$; in rank two over $\mathbf F_3$,
the groups $\operatorname{SL}_2(\mathbf F_3)$ and
$\operatorname{GL}_2(\mathbf F_3)$ are excluded.

### 15.3 Uniform-compositum stabilization

**Theorem 15.3 (Fontaine stabilization criterion).** Let $\mathscr C$ be a direct-sum-closed class of global modules killed by $\ell$, satisfying the local hypotheses of Theorem 15.2 with one common upper constant $U$. Assume every finite compositum of their cutout fields has real proportion at least $\alpha_0$. If

$$
U<4\pi e^{\gamma+\alpha_0},
$$

then the compositum of all fields $F(M)$, $M\in\mathscr C$, is finite over $F$.

Consequently every nested sequence of fields contained in that compositum stabilizes. If a torsion tower $F(T/\ell^mT)$ is contained in a fixed finite extension of this compositum and its finite quotients separate the image, then the image on $T$ is finite.

**Proof strategy.** Finite direct sums turn finite field composita into single objects of $\mathscr C$, so Theorem 15.2 gives a uniform root-discriminant bound. Theorem 15.1 bounds their degrees. A finite subcompositum of maximal degree then contains every other one. Stabilization and finiteness of the separated inverse-limit image follow. $\square$

The theorem is unconditional. Its hypotheses deliberately include the fixed-base exponent-$\ell$ condition that the cyclotomic tower violates.

### 15.4 What remains to be classified

The package is ready to receive group-theoretic input in several equivalent forms. One may show that a proposed image forces a cutout degree above the analytic cap, proving nonexistence. One may show that all successive congruence layers descend to the class $\mathscr C$, proving stabilization. Or one may combine the explicit small-prime degree lists with determinant and residual-constituent information to restrict possible finite images.

What the package does not say is that every finite-flat representation is reducible, that every bounded image is trivial, or that every torsion tower satisfies the descent hypothesis. Those are genuinely different assertions. The analytic result controls field size; the subsequent classification must control group shape.

## 16. Conclusion

The discriminant is simultaneously a covolume, a ramification product, and a coefficient in a functional equation. Minkowski's theorem uses the first interpretation to give a universal geometric lower bound. Dedekind's zeta function exposes the deeper arithmetic: its logarithmic derivative counts prime powers, its gamma factors record signature, and its functional equation balances primes against zeros. The Weil--Poitou explicit formula makes that balance numerical.

Positivity is the decisive design principle. On the critical line, Fourier positivity controls zeros under the generalized Riemann hypothesis. Unconditionally, dividing a positive-type function by $\cosh(x/2)$ controls symmetric zero pairs throughout the strip. The exact archimedean cost of that protection changes $8\pi e^{\gamma+\alpha\pi/2}$ into the unconditional constant $4\pi e^{\gamma+\alpha}$. Finite support then converts the asymptotic statement into explicit degree bounds, with every value needed at $2$, $3$, and $5$ obtained directly from the displayed integrals.

The certified two-prime value is particularly decisive. The strict ceiling
$3^{3/2}2^{2/3}$ forces degree at most $20$, and therefore rules out three-adic residual torsion
fields with Galois group of order $24$ or $48$ under the stated finite-flat and tame-inertia
hypotheses. The smaller three-only ceiling inherits the same cap. Its dedicated Minkowski
calculation gives $52$, a useful independent but nonoptimal row; the stronger conclusion comes
from the explicit formula.

Fontaine's method is the collision of this analytic lower pressure with an arithmetic upper ceiling. Finite-flat exponent-$\ell$ modules over a fixed base have cutout fields with uniformly small root discriminant, and finite direct sums preserve the bound across composita. If that ceiling lies below the Odlyzko--Poitou threshold, the maximal compositum is finite. Nested fields stabilize; separated torsion quotients then have finite image.

The limits of the method are as important as its conclusion. Full $\ell^m$-torsion bounds grow with $m$, bounded relative degree does not control depth, and cyclotomic towers demonstrate both failures. Passing from stabilized fields to a classification of representations requires residual constituents, descent of extension layers, pro-$\ell$ generation, determinant constraints, and finite-group analysis. The analytic and arithmetic work completed here supplies the sharp finite arena in which that final classification can take place.
