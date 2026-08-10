# Explicit Two-Descent on Genus-Two Jacobians

## Contents

1. [From Jacobian arithmetic to descent](#1-from-jacobian-arithmetic-to-descent)
   - [The missing global bound](#11-the-missing-global-bound)
   - [Standing hypotheses](#12-standing-hypotheses)
   - [The architecture of an explicit proof](#13-the-architecture-of-an-explicit-proof)
2. [The branch algebra and rational two-torsion](#2-the-branch-algebra-and-rational-two-torsion)
   - [The finite etale algebra](#21-the-finite-etale-algebra)
   - [Signs on branch points](#22-signs-on-branch-points)
   - [The odd-degree kernel sequence](#23-the-odd-degree-kernel-sequence)
   - [The even-degree quotient](#24-the-even-degree-quotient)
3. [The $x-T$ descent map](#3-the-x-t-descent-map)
   - [Evaluation on good divisors](#31-evaluation-on-good-divisors)
   - [Moving and Weierstrass values](#32-moving-and-weierstrass-values)
   - [Mumford evaluation](#33-mumford-evaluation)
   - [Norm identities](#34-norm-identities)
   - [Identification with the Kummer boundary](#35-identification-with-the-kummer-boundary)
4. [Odd degree: true two-descent](#4-odd-degree-true-two-descent)
   - [The cohomological target](#41-the-cohomological-target)
   - [Injectivity and exactness](#42-injectivity-and-exactness)
   - [The local version](#43-the-local-version)
   - [Characteristic restrictions](#44-characteristic-restrictions)
5. [Even degree: fake and true Selmer groups](#5-even-degree-fake-and-true-selmer-groups)
   - [Why scalar classes must be removed](#51-why-scalar-classes-must-be-removed)
   - [The norm-compatible pair](#52-the-norm-compatible-pair)
   - [The true-to-fake map](#53-the-true-to-fake-map)
   - [When a fake computation is sufficient](#54-when-a-fake-computation-is-sufficient)
6. [Global squareclasses and finite support](#6-global-squareclasses-and-finite-support)
   - [Valuations in an etale algebra](#61-valuations-in-an-etale-algebra)
   - [$S$-units and class-group corrections](#62-s-units-and-class-group-corrections)
   - [The norm kernel](#63-the-norm-kernel)
   - [A rigorous bad-place bound](#64-a-rigorous-bad-place-bound)
7. [Local descent images](#7-local-descent-images)
   - [The local image as a finite group](#71-the-local-image-as-a-finite-group)
   - [Good odd places](#72-good-odd-places)
   - [Places above two](#73-places-above-two)
   - [Bad odd places](#74-bad-odd-places)
   - [The real place](#75-the-real-place)
8. [Computing local images completely](#8-computing-local-images-completely)
   - [Residue disks and finite precision](#81-residue-disks-and-finite-precision)
   - [Generating the source quotient](#82-generating-the-source-quotient)
   - [Square tests in field factors](#83-square-tests-in-field-factors)
   - [A local completeness certificate](#84-a-local-completeness-certificate)
9. [Selmer bounds and Mordell-Weil information](#9-selmer-bounds-and-mordell-weil-information)
   - [The finite intersection](#91-the-finite-intersection)
   - [Rank bounds](#92-rank-bounds)
   - [What the bound says about the Tate-Shafarevich group](#93-what-the-bound-says-about-the-tate-shafarevich-group)
   - [Avoiding circularity](#94-avoiding-circularity)
10. [Torsion and saturation](#10-torsion-and-saturation)
    - [Prime-by-prime torsion bounds](#101-prime-by-prime-torsion-bounds)
    - [Exact torsion certificates](#102-exact-torsion-certificates)
    - [Odd-prime saturation by reduction](#103-odd-prime-saturation-by-reduction)
    - [Saturation at two](#104-saturation-at-two)
11. [Certificate design](#11-certificate-design)
    - [The global ledger](#111-the-global-ledger)
    - [The local ledger](#112-the-local-ledger)
    - [Linear algebra over squareclasses](#113-linear-algebra-over-squareclasses)
    - [Independent checks](#114-independent-checks)
12. [The Jacobian of $X_1(13)$](#12-the-jacobian-of-x_113)
    - [The curve and its two points at infinity](#121-the-curve-and-its-two-points-at-infinity)
    - [The sextic descent algebra](#122-the-sextic-descent-algebra)
    - [The finite two-descent calculation](#123-the-finite-two-descent-calculation)
    - [Torsion and the complete Jacobian](#124-torsion-and-the-complete-jacobian)
13. [The mixed-seven Jacobian](#13-the-mixed-seven-jacobian)
    - [The curve and visible classes](#131-the-curve-and-visible-classes)
    - [Arithmetic of the cubic factor](#132-arithmetic-of-the-cubic-factor)
    - [The global norm kernel](#133-the-global-norm-kernel)
    - [The local cuts](#134-the-local-cuts)
    - [The Mordell-Weil group](#135-the-mordell-weil-group)
14. [Odd-prime saturation in practice](#14-odd-prime-saturation-in-practice)
    - [A reduction-kernel criterion](#141-a-reduction-kernel-criterion)
    - [Choosing useful primes](#142-choosing-useful-primes)
    - [Certificates for finite-index generators](#143-certificates-for-finite-index-generators)
15. [Hypothesis and dependency ledger](#15-hypothesis-and-dependency-ledger)
    - [What is assumed](#151-what-is-assumed)
    - [What is proved here](#152-what-is-proved-here)
    - [Model boundaries](#153-model-boundaries)
16. [The completed two-descent package](#16-the-completed-two-descent-package)
    - [The main theorem](#161-the-main-theorem)
    - [The two finite calculations](#162-the-two-finite-calculations)
    - [Conclusion](#163-conclusion)

## 1. From Jacobian arithmetic to descent

### 1.1 The missing global bound

Let $C/K$ be a genus-two curve over a number field and let $J$ be its
Jacobian. Exact divisor arithmetic answers a concrete question: given two
classes already in hand, what is their sum? It does not answer the more
global question of whether the classes in hand generate a subgroup of finite
index, nor does it bound the rank of $J(K)$. Two-descent supplies that missing
bound.

The basic Kummer injection is

$$
J(K)/2J(K)\hookrightarrow H^1(K,J[2]). \tag{1.1}
$$

Abstractly, the Selmer condition cuts out a finite subgroup of the group on
the right. For a hyperelliptic curve, the branch points make the coefficient
module $J[2]$ unusually concrete. Their residue fields assemble into one
finite etale algebra, and the cohomology classes become squareclasses in that
algebra subject to a norm relation. The expression $x-T$ is the bridge from
divisors to those squareclasses.

Three distinctions govern the entire subject. First, a squareclass satisfying
the norm relation is only a global candidate; it must lie in the local image
at every completion. Second, the even-degree $x-T$ target can be a quotient
of the true cohomology group and is then called a fake target. Third, a rank
bound does not by itself exhibit generators or determine torsion. A complete
Mordell--Weil certificate combines descent, exact divisor arithmetic, good
reduction, and saturation.

### 1.2 Standing hypotheses

Except where the even-degree case is explicitly treated, let $K$ be a field
of characteristic different from $2$, let

$$
C:y^2=f(x) \tag{1.2}
$$

be the smooth projective curve associated with a squarefree polynomial
$f\in K[x]$ of degree $5$, and assume $f$ is monic. The unique point at
infinity is denoted $\infty$. It is a $K$-rational Weierstrass point, so every
class of $J(K)$ has a unique reduced Mumford representative $[u,v]$ with

$$
u\text{ monic},\qquad \deg v<\deg u\le2,\qquad u\mid f-v^2. \tag{1.3}
$$

For global finiteness statements, $K$ is a number field. For local statements,
$K$ is replaced by a completion $K_v$. The two explicit calculations are over
$\mathbf Q$.

The monic quintic presentation is more than a convenient chart. Odd degree
makes the norm map on branch signs surjective and turns the $x-T$ target into
the true cohomological target. A squarefree sextic has two points above
infinity and a different exact sequence; Chapter 5 keeps the resulting scalar
ambiguity visible. The $X_1(13)$ calculation necessarily uses that sextic
theory because its standard model has no rational Weierstrass point.

### 1.3 The architecture of an explicit proof

A complete two-descent proceeds through the following mathematical chain:

$$
\begin{array}{c}
J(K)/2J(K)\longrightarrow L^\times/L^{\times2}\quad
\text{with a norm condition}\\
\downarrow\\
\text{classes unramified outside a finite set }S\\
\downarrow\\
\text{intersection with the images of }J(K_v)/2J(K_v),\ v\in S\\
\downarrow\\
\operatorname{rank}J(K)\le
\dim_{\mathbf F_2}\operatorname{Sel}_2(J/K)-
\dim_{\mathbf F_2}J(K)[2].
\end{array} \tag{1.4}
$$

Every downward arrow needs a proof. The first is the Kummer boundary written
in branch coordinates. The second uses integral unramifiedness and ideal
factorization, including the $2$-torsion of an $S$-class group. The third uses
the full local Kummer image, not merely values found by a short search. The
last is the Mordell--Weil--Selmer exact sequence.

Once the rank is bounded, exact Mumford arithmetic proves relations among
displayed points, and reductions at good primes bound torsion and test
saturation. The result is a finite certificate rather than a numerical
expectation.

## 2. The branch algebra and rational two-torsion

### 2.1 The finite etale algebra

Put

$$
L=K[T]/(f(T)),\qquad \theta=T\bmod f. \tag{2.1}
$$

Because $f$ is squarefree, $L$ is a finite etale $K$-algebra. If
$f=f_1\cdots f_r$ is its factorization into distinct monic irreducibles, then

$$
L\simeq\prod_{i=1}^rK_i,qquad K_i=K[T]/(f_i). \tag{2.2}
$$

Thus $L^\times/L^{\times2}$ is the product of the squareclass groups of the
field factors. Working with the algebra, rather than choosing all roots in a
splitting field, retains the Galois action automatically.

Over a separable closure, $L$ becomes a product of one copy of the ground
field for every finite branch point. An element of $\operatorname{Res}_{L/K}
\mu_2$ is therefore a sign attached to every finite branch point. This simple
description is the source of the descent algebra.

### 2.2 Signs on branch points

The six Weierstrass points of an odd-degree genus-two curve are the five
finite roots of $f$ and $\infty$. A geometric two-torsion class is an even
subset of these six points, modulo replacing a subset by its complement.
Using $\infty$ to choose a representative turns such a class into a sign
vector on the five finite roots whose product is $1$.

More explicitly, for an even subset $A$ attach the sign $-1$ to a finite
branch point when its membership differs from that of $\infty$, and $+1$
otherwise. Complementing $A$ changes neither sign vector. Even cardinality
is exactly the product-one condition. Hence, over a separable closure,

$$
J[2]\simeq
\left\{(\epsilon_1,\ldots,\epsilon_5)\in\mu_2^5:
\prod_i\epsilon_i=1\right\}. \tag{2.3}
$$

This description is Galois equivariant, so it descends to a group-scheme
identification.

### 2.3 The odd-degree kernel sequence

Let $N$ denote the norm on the restriction of scalars. Equation (2.3) gives
an exact sequence of finite etale group schemes

$$
1\longrightarrow J[2]\longrightarrow
\operatorname{Res}_{L/K}\mu_2
\xrightarrow{N}\mu_2\longrightarrow1. \tag{2.4}
$$

The last map is surjective already on $K$-points. Indeed the diagonal sign
$-1\in L$ has norm $(-1)^5=-1$. This apparently small oddness fact removes a
cohomological ambiguity. Applying cohomology and Kummer theory yields an
injection

$$
H^1(K,J[2])\hookrightarrow L^\times/L^{\times2} \tag{2.5}
$$

whose image is exactly

$$
(L^\times/L^{\times2})_{N=1}
=\{\alpha:N_{L/K}(\alpha)\in K^{\times2}\}. \tag{2.6}
$$

Here and below a condition on a squareclass means that one, hence every,
representative satisfies it modulo squares.

The long exact sequence makes the assertion precise:

$$
\mu_2(L)\xrightarrow{N}\mu_2(K)\longrightarrow H^1(K,J[2])
\longrightarrow H^1(K,\operatorname{Res}_{L/K}\mu_2)
\xrightarrow{N}H^1(K,\mu_2). \tag{2.6a}
$$

The first arrow is onto because $[L:K]=5$. Shapiro's lemma and Kummer theory
identify the last two groups with $L^\times/L^{\times2}$ and
$K^\times/K^{\times2}$. Exactness therefore proves (2.5)--(2.6), including
when $L$ is a product of fields. This explains why oddness matters at the
cohomological level, not merely in a count of geometric branch points.

### 2.4 The even-degree quotient

If $f$ has degree $6$, all six branch points are finite. Their sign vectors
of product $1$ still describe even subsets, but a vector and its negative
describe complementary subsets. Consequently

$$
J[2]\simeq
\ker\left(N:\operatorname{Res}_{L/K}\mu_2\to\mu_2\right)
/\mu_2, \tag{2.7}
$$

where the denominator is the diagonal subgroup. The corresponding
cohomology is not simply a norm kernel inside $L^\times/L^{\times2}$.
Scalar squareclasses enter, and a connecting obstruction can remain.

When the leading coefficient is $c$, the natural explicit target is

$$
L^\times/(L^{\times2}K^\times), \tag{2.8}
$$

together with a compatible norm datum. Calling (2.8) the true $2$-Selmer
group erases information. It is the fake target; Chapter 5 gives the exact
comparison.

If all six branch points are rational, the product-one sign vectors have
dimension five, while quotienting by the diagonal sign gives dimension four,
the correct dimension of $J[2]$. Omitting that quotient produces twice as
many geometric elements. In cohomology the correction becomes a connecting
map, so it cannot be repaired by simply subtracting one from a final
dimension.

## 3. The $x-T$ descent map

### 3.1 Evaluation on good divisors

Let $D=\sum_P n_PP$ be a degree-zero divisor on $C$, defined over $K$, whose
support avoids the Weierstrass points and $\infty$. Define

$$
(x-T)(D)=
\prod_P N_{K(P)/K}\bigl(x(P)-\theta\bigr)^{n_P}
\in L^\times. \tag{3.1}
$$

The norms in (3.1) are taken after scalar extension of $L$ to $K(P)$.
Galois-stability of $D$ makes the product lie in $L$, and avoidance of branch
points makes it invertible.

If $D$ is replaced by a linearly equivalent good divisor, Weil reciprocity
shows that (3.1) changes by a square. The key divisor identity is that, in the
function field after adjoining a branch root $\theta$,

$$
\operatorname{div}(x-\theta)=2(W_\theta-\infty). \tag{3.2}
$$

For a principal divisor $\operatorname{div}(h)$, reciprocity applied to
$h$ and $x-\theta$ gives

$$
(x-\theta)(\operatorname{div}h)
=h(2W_\theta-2\infty), \tag{3.3}
$$

which is a square. Thus (3.1) defines a homomorphism on divisor classes once
every class has been moved away from the exceptional support.

Indeed Weil reciprocity says that, for functions $a,b$ with disjoint
divisors, $a(\operatorname{div}b)=b(\operatorname{div}a)$. Taking
$a=x-\theta$ and $b=h$, the right side is
$h(W_\theta)^2/h(\infty)^2$, with leading coefficients used at infinity.
It is a square in every branch component. This proves invariance under all
principal divisors. Multiplicativity on divisors proves that the induced map
on $J(K)$ is a homomorphism.

### 3.2 Moving and Weierstrass values

The map must not be left undefined on the very classes that make rational
two-torsion visible. A moving lemma provides a linearly equivalent divisor
disjoint from the finite branch divisor and infinity. Definition (3.1) on
that moved divisor is independent of the move by (3.3).

There is also a useful regularized value. Suppose $\alpha$ is a simple root
of $f$. For the class $[W_\alpha-\infty]$, its component at a different root
$\beta$ is $\alpha-\beta$, while the vanishing component at $\alpha$ is
replaced by

$$
f'(\alpha)=\prod_{\beta\ne\alpha}(\alpha-\beta). \tag{3.4}
$$

This is not a convention assigning a squareclass to zero. It is the value
obtained from a moved divisor, or equivalently from the leading nonzero term
of $x-\alpha$ in a local parameter at the ramification point.

For a divisor containing several points, one multiplies (3.4) by the ordinary
factors contributed by the other points. This derivative rule is especially
convenient when $f$ has rational linear factors.

Moving can be done over $K$. Given a divisor $D$ and a finite forbidden set,
choose a sufficiently large $K$-rational effective divisor $E$. Riemann--Roch
makes both $|D+E|$ and $|E|$ positive-dimensional. Members meeting a fixed
forbidden point form a proper linear subspace, so over the infinite field $K$
one can choose $D_1\sim D+E$ and $E_1\sim E$ avoiding every forbidden point.
Then $D_1-E_1\sim D$ is good.

The derivative value also follows locally. With $s=y$ at $W_\alpha$,

$$
x-\alpha=\frac{s^2}{f'(\alpha)}+O(s^4). \tag{3.4a}
$$

Removing the square $s^2$ leaves $f'(\alpha)^{-1}$, which has the same
squareclass as $f'(\alpha)$. Thus moving and regularization agree.

### 3.3 Mumford evaluation

Let $[u,v]$ be a reduced Mumford class whose support avoids the branch points.
If $r=\deg u$ and the roots of $u$ are $x_1,\ldots,x_r$, counted with
multiplicity, then

$$
(-1)^ru(\theta)=\prod_{i=1}^r(x_i-\theta). \tag{3.5}
$$

Therefore

$$
\delta([u,v])=(-1)^{\deg u}u(\theta)
\quad\text{in }L^\times/L^{\times2}. \tag{3.6}
$$

The polynomial $v$ does not appear in (3.6), but it is not irrelevant: it
chooses which points above the roots of $u$ occur in the divisor and certifies
that $u$ lies on the curve. Changing $v$ to $-v$ negates the Jacobian class;
because the target has exponent two, the two descent values agree, as they
must.

When $\gcd(u,f)\ne1$, formula (3.6) is interpreted by moving or by the
derivative rule. For example, if $u=(x-\alpha)u_0$ and the branch root
$\alpha$ occurs once, the $\alpha$-component is

$$
f'(\alpha)(-1)^{r-1}u_0(\alpha), \tag{3.7}
$$

while every other component is obtained by literal evaluation. Formula
(3.7) makes the map total on $J(K)$.

### 3.4 Norm identities

For a good divisor supported at points $(x_i,y_i)$,

$$
N_{L/K}(x_i-\theta)=f(x_i)=y_i^2. \tag{3.8}
$$

Multiplying proves

$$
N_{L/K}(\delta(D))\in K^{\times2}. \tag{3.9}
$$

The same conclusion follows from the resultant identity

$$
N_{L/K}\bigl((-1)^ru(\theta)\bigr)
=(-1)^r\operatorname{Res}(f,u)
=\operatorname{Res}(u,f)
=\prod_i f(x_i), \tag{3.10}
$$

with multiplicities. The regularized Weierstrass values satisfy the same
identity by continuity, or directly from (3.4). Thus the norm condition is a
theorem forced by the curve equation, not an extra filter guessed from
examples.

### 3.5 Identification with the Kummer boundary

To identify (3.6), choose a geometric divisor class $Q$ with $2Q=P$. For
each finite branch point $W_\alpha$, the function $x-\alpha$ has divisor
$2(W_\alpha-\infty)$. A square root of its evaluation on $P$ trivializes the
character of the division cocycle obtained by pairing with the class
$[W_\alpha-\infty]$. Galois conjugation changes that root by precisely the
corresponding branch sign.

Consequently the cocycle

$$
\sigma\longmapsto\sigma Q-Q\in J[2] \tag{3.11}
$$

maps under (2.5) to the Kummer cocycle of $(x-T)(P)$. Hence the $x-T$ map is
the abstract boundary (1.1) in the coordinates (2.6). This proves at once
that it is a homomorphism and, in odd degree, injective on $J(K)/2J(K)$.

More concretely, let $\chi_\alpha$ be the character obtained by pairing with
$[W_\alpha-\infty]$. A compatible square root $r_\alpha$ of the evaluation
on $P$ satisfies

$$
\frac{\sigma r_\alpha}{r_\alpha}
=\chi_\alpha(\sigma Q-Q). \tag{3.12}
$$

The branch characters separate points of $J[2]$, so these componentwise
equalities prove equality of the two cocycles.

## 4. Odd degree: true two-descent

### 4.1 The cohomological target

Combining (2.5), (2.6), and Chapter 3 gives a commutative injection

$$
\begin{array}{ccc}
J(K)/2J(K)&\xrightarrow{\delta_2}&H^1(K,J[2])\\
\Vert&&\downarrow\sim\\
J(K)/2J(K)&\xrightarrow{x-T}&
(L^\times/L^{\times2})_{N=1}.
\end{array} \tag{4.1}
$$

The right vertical arrow is an isomorphism onto the displayed norm kernel.
Thus a complete odd-degree $x-T$ calculation computes the true $2$-Selmer
group. There is no hidden scalar quotient and no loss between fake and true
classes.

### 4.2 Injectivity and exactness

Suppose $(x-T)(P)$ is trivial. Its image in $H^1(K,J[2])$ is zero by (4.1),
so the Kummer exact sequence gives $P\in2J(K)$. Conversely every double has
trivial value because the target has exponent two. Therefore

$$
\ker(x-T)=2J(K). \tag{4.2}
$$

This statement includes branch-supported divisor classes because the map was
extended by moving. Literal evaluation only on coprime Mumford polynomials
would not prove (4.2).

For a number field, define the odd-degree explicit Selmer group by

$$
\operatorname{Sel}_{x-T}(J/K)=
\left\{\alpha\in(L^\times/L^{\times2})_{N=1}:
\alpha_v\in(x-T)_v(J(K_v))\text{ for every }v\right\}. \tag{4.3}
$$

By the local form of (4.1), this is canonically
$\operatorname{Sel}_2(J/K)$.

### 4.3 The local version

Every construction above commutes with extension of the ground field. For a
completion $K_v$, put $L_v=L\otimes_KK_v$. Then

$$
J(K_v)/2J(K_v)\hookrightarrow
(L_v^\times/L_v^{\times2})_{N=1}. \tag{4.4}
$$

The image is the local Kummer condition. It need not be the whole norm kernel.
At a good odd place it is the unramified subgroup; at a place above $2$ or of
bad reduction it can contain ramified unit information. Replacing the image
by the whole target weakens the bound, and replacing it by values of a few
visible points can make the bound falsely small.

### 4.4 Characteristic restrictions

The construction uses $2\ne0$ in three places: $y^2=f(x)$ is a separable
double cover, the branch divisor is detected by the simple roots of $f$, and
$\mu_2$ is etale. In characteristic two a hyperelliptic equation has the form
$y^2+h(x)y=f(x)$, and neither the branch algebra nor the function $x-T$ above
has the asserted Kummer interpretation.

Over number fields and their completions the generic characteristic is zero,
including at places above $2$. The global coefficient group remains etale,
but its integral model at such a place is not etale. This is exactly why the
$2$-adic local condition requires separate finite-precision analysis.

## 5. Even degree: fake and true Selmer groups

### 5.1 Why scalar classes must be removed

Let

$$
C:y^2=f(x),\qquad \deg f=6, \tag{5.1}
$$

with $f$ squarefree and leading coefficient $c$. A degree-zero divisor may be
evaluated by $x-T$ as before. Changing the reference divisor at infinity,
however, multiplies the value by a scalar from $K^\times$. Complementary
branch subsets likewise differ by the diagonal sign. The natural visible
class is therefore

$$
\overline\delta(P)\in L^\times/(L^{\times2}K^\times). \tag{5.2}
$$

The quotient is mathematically forced. It is also the source of the word
fake: (5.2) may identify two distinct true cohomology classes.

### 5.2 The norm-compatible pair

It is useful to retain the scalar discarded by (5.2). Define

$$
\mathcal H_K=
\frac{\{(\alpha,s)\in L^\times\times K^\times:
N_{L/K}(\alpha)=s^2\}}
{\{(\gamma^2r,r^3N(\gamma)):
\gamma\in L^\times, r\in K^\times\}}. \tag{5.3}
$$

For a monic sextic, evaluation on a degree-zero good divisor produces such a
pair: $\alpha$ is its $x-T$ value and $s$ is the product of its $y$-values.
For leading coefficient $c$, the same formula contains the predictable power
of $c$ determined by the degree of the chosen reference divisor; fixing that
reference fixes the normalization.

The first component maps $\mathcal H_K$ to (5.2). The pair remembers enough
norm information to construct the corresponding two-covering and to compare
with $H^1(K,J[2])$. Different normalizations of the sextic change (5.3) by a
canonical isomorphism, whereas dropping the second coordinate without taking
the scalar quotient is not invariant.

The exponent $3$ in (5.3) is half the sextic degree. Multiplying $\alpha$ by
a scalar $r$ multiplies its norm by $r^6$, so the compatible square root must
be multiplied by $r^3$. Multiplying $\alpha$ by $\gamma^2$ multiplies that
root by $N(\gamma)$. The denominator in (5.3) is therefore exactly the change
of trivialization.

### 5.3 The true-to-fake map

The exact sequence (2.7) gives a natural map

$$
H^1(K,J[2])\longrightarrow
L^\times/(L^{\times2}K^\times). \tag{5.4}
$$

Its image satisfies the norm condition coming from (5.3). Its kernel and
cokernel are controlled by the diagonal $\mu_2$ and by the connecting map
attached to the norm sequence. Both have order at most two in the common
sextic situations, but they are not automatically zero.

Define the **fake $2$-Selmer group** by imposing all local $x-T$ image
conditions in the quotient (5.2). Define the **true $2$-Selmer group** by the
usual local Kummer conditions in $H^1(K,J[2])$. Then there is a natural map

$$
\operatorname{Sel}_2(J/K)\longrightarrow
\operatorname{Sel}^{\mathrm{fake}}_{x-T}(J/K). \tag{5.5}
$$

One must compute the kernel of (5.5), or prove it irrelevant to the desired
rank bound. Equality of the two groups is a conclusion, never a definition.

The comparison is organized by

$$
1\to\mu_2\to\ker(N)\to J[2]\to1,
\qquad
1\to\ker(N)\to\operatorname{Res}_{L/K}\mu_2\to\mu_2\to1. \tag{5.5a}
$$

Their cohomology sequences show that the kernel in (5.5) comes from a
diagonal scalar class, while failure of a fake class to lift is measured by
the next connecting map. The norm-compatible pair retains the data needed to
test both phenomena without choosing all six roots.

### 5.4 When a fake computation is sufficient

There are three safe ways to use an even-degree computation.

First, compute in $\mathcal H_K$ and identify it directly with the true
cohomological classes. Second, determine the kernel of (5.5) from the
diagonal connecting sequence and add its dimension to the fake bound. Third,
if a rational divisor of odd degree fixes the Picard obstruction, use it to
split the scalar ambiguity and prove that the relevant kernel is trivial.

Rational points at infinity are helpful but do not, by themselves, license
the odd-degree formula. Their difference can be a nontrivial Jacobian class,
and its fake $x-T$ value may disappear. The $X_1(13)$ calculation in Chapter
12 explicitly performs the true lift after the fake local intersection.

## 6. Global squareclasses and finite support

### 6.1 Valuations in an etale algebra

Let $K$ be a number field and write $L=\prod_iK_i$. For a finite set $S$ of
places of $K$, let $S_L$ be the set of places of the factors above $S$. Define

$$
L(S,2)=\left\{\alpha\in L^\times/L^{\times2}:
v_{\mathfrak P}(\alpha)\equiv0\pmod2
\text{ for every }\mathfrak P\notin S_L\right\}. \tag{6.1}
$$

This is finite. The definition is componentwise and includes split rational
factors. It is not enough to require the norm to have even valuation: two
odd component valuations can cancel in the norm while the class remains
ramified in $L$.

### 6.2 $S$-units and class-group corrections

For each field factor there is an exact sequence

$$
0\longrightarrow
\mathcal O_{K_i,S_i}^\times/\mathcal O_{K_i,S_i}^{\times2}
\longrightarrow K_i(S_i,2)
\longrightarrow\operatorname{Cl}(\mathcal O_{K_i,S_i})[2]
\longrightarrow0. \tag{6.2}
$$

To prove (6.2), associate to $a$ with even valuations outside $S_i$ the ideal
$\mathfrak a$ satisfying $(a)=\mathfrak a^2$ away from $S_i$. Its class has
order dividing two. The kernel consists exactly of classes that can be made
$S_i$-units after multiplication by a square.

Thus a list of $S$-units is complete only after the $2$-torsion of the
$S$-class group has been shown trivial or represented. A certificate may use
an integral basis, a factorization of the primes in $S$, a relation matrix
for ideals, and generators for the unit group. Row reduction modulo two then
gives a basis of (6.1).

The sequence is constructive. Choose ideals $\mathfrak a_j$ representing the
two-torsion classes and elements $a_j$ satisfying

$$
\mathfrak a_j^2=(a_j)
\prod_{\mathfrak p\in S_i}\mathfrak p^{m_{j,\mathfrak p}}. \tag{6.2a}
$$

The classes of the $a_j$, together with fundamental units, $-1$, and the
allowed prime-ideal generators, span $K_i(S_i,2)$. If an allowed prime is
nonprincipal, no global uniformizer may be invented for it; its row must be
combined with (6.2a). For the base field,

$$
\mathbf Q(S,2)=\langle-1,p:p\in S\setminus\{\infty\}\rangle. \tag{6.2b}
$$

### 6.3 The norm kernel

Norm induces a linear map of finite $\mathbf F_2$-spaces

$$
N:L(S,2)\longrightarrow K(S,2). \tag{6.3}
$$

For odd-degree descent the global ambient space is

$$
V_S=\ker N. \tag{6.4}
$$

For even degree one first forms the scalar quotient and then imposes the
norm-compatible-pair condition. Computing norms only as rational numbers is
not enough: their valuations and unit squareclasses must be expressed in the
chosen basis of $K(S,2)$.

The norm matrix provides an important independent check. The product of the
component norms computed from field multiplication must agree with a
resultant. For a polynomial representative $a(T)$,

$$
N_{K_i/K}(a(\theta_i))=
\operatorname{Res}(f_i,a) \tag{6.5}
$$

up to the standard leading-coefficient power. This turns every column of the
norm matrix into a finite polynomial identity.

### 6.4 A rigorous bad-place bound

Choose $S$ to contain

- all archimedean places;
- every place above $2$;
- every place at which the chosen curve has bad reduction;
- every place needed for the denominators and leading coefficient of the
  chosen model.

For a monic integral squarefree odd-degree equation over $\mathbf Q$, it is
safe to take

$$
S=\{\infty,2\}\cup\{p:p\mid\operatorname{disc}(f)\}. \tag{6.6}
$$

At a finite place outside $S$, the Jacobian has good reduction, $2$ is a
unit, and the Kummer image is unramified. Under the branch-coordinate
identification, unramifiedness means exactly even valuation at every prime of
$L$ above that place. Hence every Selmer class belongs to $V_S$.

The discriminant in (6.6) belongs to the chosen model. A nonminimal equation
may enlarge $S$, which weakens efficiency but not correctness. Omitting a
prime merely because another model might be good is unsafe unless the change
of model and the integral descent functions have been checked.

**Proposition 6.1 (finite-support theorem).** Every odd-degree Selmer class
belongs to $V_S$.

**Proof.** At $v\notin S$, the Jacobian has good reduction, $2$ is a unit,
and the branch algebra is etale over the valuation ring. Integral Kummer
theory identifies the local image with unramified cohomology. Kummer theory
in each field factor identifies an unramified squareclass with one of even
valuation. Thus every prime of $L$ outside $S_L$ has even valuation on the
global class. Its norm is a square by (3.9), so it belongs to $V_S$.
$\square$

The converse is false in general: the finitely many places of $S$ still
impose their full Kummer-image conditions.

## 7. Local descent images

### 7.1 The local image as a finite group

For every place $v$, write

$$
\mathcal I_v=(x-T)_v\bigl(J(K_v)/2J(K_v)\bigr). \tag{7.1}
$$

In odd degree the map is injective, so

$$
|\mathcal I_v|=|J(K_v)/2J(K_v)|. \tag{7.2}
$$

This identity is the central completeness test for a list of local values.
Finding independent values up to the known dimension proves that the list is
the whole image.

If $v$ is nonarchimedean of odd residue characteristic, multiplication by two
is an automorphism on a sufficiently small pro-$p$ subgroup. Comparing kernel
and cokernel on the finite quotient gives

$$
\dim_{\mathbf F_2}J(K_v)/2J(K_v)
=\dim_{\mathbf F_2}J(K_v)[2]. \tag{7.3}
$$

If $K_v/\mathbf Q_2$ is finite and $J$ has dimension $g$, the formal group
contributes $g[K_v:\mathbf Q_2]$ dimensions, so

$$
\dim_{\mathbf F_2}J(K_v)/2J(K_v)
=g[K_v:\mathbf Q_2]+
\dim_{\mathbf F_2}J(K_v)[2]. \tag{7.4}
$$

To prove the formulas, choose an open formal subgroup $U$ on which the formal
logarithm identifies the group law with $\mathfrak m_v^g$. At odd residue
characteristic, multiplication by two is an automorphism of $U$. On the
finite quotient $J(K_v)/U$, the kernel and cokernel of multiplication by two
have the same order, and the kernel is the image of $J(K_v)[2]$. This proves
(7.3). Above two,

$$
U/2U\simeq(\mathcal O_v/2\mathcal O_v)^g,
$$

of dimension $g[K_v:\mathbf Q_2]$; the snake lemma adds the finite-quotient
kernel and proves (7.4).

### 7.2 Good odd places

Suppose $J$ has good reduction at $v\nmid2$. Integral Kummer theory identifies
the local image with unramified cohomology. In branch coordinates this is the
subgroup of squareclasses represented by local units whose residue data obey
the norm relation.

Equivalently, reduction induces an isomorphism on the relevant cokernels:

$$
J(K_v)/2J(K_v)\simeq J(k_v)/2J(k_v). \tag{7.5}
$$

Indeed the formal kernel is uniquely two-divisible. Exact finite-field
Jacobian arithmetic can therefore enumerate the local image. No search
through deeper residue disks is needed at such a place.

### 7.3 Places above two

At $v\mid2$, principal units are not automatically squares and the formal
group contributes the extra term in (7.4). Squareclasses in a field factor
$F/K_v$ are detected by valuation parity and a sufficiently deep unit
quotient

$$
\mathcal O_F^\times/(1+\mathfrak p_F^m)\mathcal O_F^{\times2}. \tag{7.6}
$$

One chooses $m$ so that $1+\mathfrak p_F^m\subset F^{\times2}$. A Hensel
argument supplies such an $m$; for an unramified extension of $\mathbf Q_2$,
reduction modulo $8\mathcal O_F$ is sufficient for units.

The image itself may be generated by divisor classes in finitely many residue
disks. Completeness is certified by independence together with (7.4), not by
the apparent stabilization of a list.

### 7.4 Bad odd places

At an odd bad place the unramified equality need not hold. Nevertheless
$J(K_v)/2J(K_v)$ is finite and has dimension (7.3). A semistable model can
organize the calculation through components and the identity neighborhood;
alternatively, compactness and openness of $2J(K_v)$ reduce it to finitely
many residue classes at a justified depth.

If all local two-torsion is already rational and supplies the dimension in
(7.3), its descent values generate the complete image. This useful shortcut
still requires a factorization over $K_v$ proving that no additional
two-torsion exists.

### 7.5 The real place

Over $\mathbf C$ the local quotient is zero. Over $\mathbf R$, multiplication
by two is surjective on the identity component, and

$$
J(\mathbf R)/2J(\mathbf R)\simeq\pi_0(J(\mathbf R)). \tag{7.7}
$$

For a hyperelliptic curve, the component group is read from the arrangement
of real branch points. In the etale algebra, the local target is a sign
vector on the real field factors; complex factors contribute no sign. The
image can be obtained by moving points along the real ovals. A sign table is
a complete local certificate once its number of independent rows equals the
dimension of (7.7).

If a monic quintic has $m$ real roots, then $m$ is odd. The real curve has
$(m+1)/2$ components, and the bounded ovals give independent component
differences in the Jacobian. Consequently

$$
\dim_{\mathbf F_2}J(\mathbf R)/2J(\mathbf R)=\frac{m-1}{2}. \tag{7.8}
$$

Ordering the real roots and recording the signs of $x-\alpha$ on each oval
produces a full sign-image matrix.

## 8. Computing local images completely

### 8.1 Residue disks and finite precision

Fix a nonarchimedean local field $F$. The subgroup $2J(F)$ is open, so there
is an integer $m$ such that two points of $J(F)$ congruent modulo the $m$th
formal neighborhood have the same class modulo $2J(F)$. Cover $C^{(2)}(F)$
by finitely many residue polydisks, including charts meeting infinity and the
diagonal. The Abel map then gives finitely many classes modulo $2J(F)$.

The depth $m$ is proved from the formal logarithm away from residue
characteristic two, or from a direct Hensel estimate at two. Because every
Jacobian class has a degree-at-most-two representative in the pointed
odd-degree case, this finite disk enumeration reaches every class.

Diagonal disks cannot be omitted. Two points approaching the same
non-Weierstrass point produce a tangent divisor, so the local Mumford
polynomial has a double root and its second coordinate must contain the
derivative prescribed by $y^2=f(x)$. Two points approaching hyperelliptic
conjugates cancel to a lower-degree class. Exact divisor reduction handles
both limits, while an enumeration of distinct residue points would miss them.

### 8.2 Generating the source quotient

There is often no need to enumerate all disks. First determine the dimension
by (7.3) or (7.4). Then exhibit that many local classes and prove their
$x-T$ values independent. Injectivity of (4.4) shows that the classes are
independent in $J(F)/2J(F)$, and the dimension count proves they generate.

Visible Weierstrass points are natural generators when they exist. At two,
non-Weierstrass points in carefully chosen residue disks usually supply the
formal-group directions. The values are computed by (3.6) or (3.7).

### 8.3 Square tests in field factors

Let $M/F$ be one factor of $L\otimes F$. To compare two descent values, test
whether their quotient is a square in $M$. For odd residue characteristic,
this means even valuation and square residue after removing a uniformizer
power. At residue characteristic two, use the finite unit quotient (7.6).

These tests are linear over $\mathbf F_2$. After fixing a basis of each local
squareclass group, every global candidate becomes a column and every local
image becomes a subspace. Membership is ordinary row reduction.

### 8.4 A local completeness certificate

A complete local certificate contains:

1. the factorization of $f$ over $F$ and the resulting dimension of
   $J(F)[2]$;
2. the source dimension from (7.3), (7.4), or (7.7);
3. explicit divisor classes and their regularized $x-T$ values;
4. a squareclass matrix proving the required independence;
5. a precision bound for every unit-square decision.

The first two items prove how large the image must be. The next two prove a
subgroup of that size has been found. The last item makes every equality in
the matrix exact.

## 9. Selmer bounds and Mordell-Weil information

### 9.1 The finite intersection

Let $V_S$ be the finite global norm kernel of (6.4). Localization gives maps

$$
\lambda_v:V_S\longrightarrow
(L_v^\times/L_v^{\times2})_{N=1}. \tag{9.1}
$$

In odd degree,

$$
\operatorname{Sel}_2(J/K)=
\bigcap_{v\in S}\lambda_v^{-1}(\mathcal I_v). \tag{9.2}
$$

Places outside $S$ impose no further condition because membership in $V_S$
is exactly the unramified condition there. Equation (9.2) is therefore a
finite intersection of kernels of linear maps between finite
$\mathbf F_2$-spaces.

A dimension ledger records the size after each local cut. An obstruction
matrix is stronger: its rows are linear functionals vanishing on the local
image, and its kernel is visibly the Selmer group. Either presentation must
use complete local images.

### 9.2 Rank bounds

Write

$$
J(K)\simeq\mathbf Z^r\oplus J(K)_{\mathrm{tors}}. \tag{9.3}
$$

Then

$$
\dim_{\mathbf F_2}J(K)/2J(K)
=r+\dim_{\mathbf F_2}J(K)[2]. \tag{9.4}
$$

The Kummer injection into the Selmer group yields

$$
r\le
\dim_{\mathbf F_2}\operatorname{Sel}_2(J/K)
-\dim_{\mathbf F_2}J(K)[2]. \tag{9.5}
$$

If $r$ independent rational points have already been exhibited and the right
side of (9.5) equals $r$, then their subgroup has finite odd index. It need
not yet have index one; odd-prime saturation closes that gap.

Equation (9.4) follows from the structure theorem for finitely generated
abelian groups. The free part contributes one $\mathbf F_2$-dimension per
generator. For a finite abelian group $T$, the kernel $T[2]$ and the cokernel
$T/2T$ have equal order. This explains why (9.5) subtracts rational
two-torsion, not all sixteen geometric two-torsion points.

### 9.3 What the bound says about the Tate-Shafarevich group

The exact sequence

$$
0\longrightarrow J(K)/2J(K)
\longrightarrow\operatorname{Sel}_2(J/K)
\longrightarrow\Sha(J/K)[2]
\longrightarrow0 \tag{9.6}
$$

shows exactly where excess Selmer classes go. If displayed points attain the
rank bound and the rational two-torsion is known, equality of dimensions in
(9.6) proves $\Sha(J/K)[2]=0$. If the upper bound is larger, one cannot decide
from two-descent alone whether the excess is rank or a locally soluble
two-covering without a rational point.

### 9.4 Avoiding circularity

A local image must not be declared complete because its dimension matches a
desired global answer. Its dimension is established independently by local
group theory. A torsion subgroup must not be declared complete because it
accounts for the computed Selmer classes; torsion is bounded by reduction.
Finally, a finite-index subgroup must not be called the Mordell--Weil group
until every possible prime divisor of its index has been removed.

The safe order is:

$$
\text{local completeness}\Rightarrow\text{Selmer bound}
\Rightarrow\text{rank}
\Rightarrow\text{torsion bound}
\Rightarrow\text{saturation}. \tag{9.7}
$$

## 10. Torsion and saturation

### 10.1 Prime-by-prime torsion bounds

At a good prime $p$, reduction is injective on torsion of order prime to $p$.
Thus for every prime $\ell\ne p$,

$$
v_\ell\bigl(|J(\mathbf Q)_{\mathrm{tors}}|\bigr)
\le v_\ell\bigl(|J(\mathbf F_p)|\bigr). \tag{10.1}
$$

Using two good primes of distinct residue characteristics usually turns this
into a gcd bound. The prime-by-prime formulation (10.1) is authoritative: a
reduction in characteristic $\ell$ does not control the $\ell$-primary
kernel.

Finite group structure can sharpen the order bound. A proposed torsion group
must embed, prime to $p$, into the actual invariant-factor decomposition of
$J(\mathbf F_p)$.

If a prime-to-$p$ torsion point reduces to zero, it lies in the formal group.
Multiplication by its order has invertible linear term there and is therefore
an automorphism on a sufficiently small neighborhood. The point must be zero.
This proves the injectivity used in (10.1) for arbitrary finite torsion
subgroups, not only for cyclic points.

### 10.2 Exact torsion certificates

A displayed Mumford class has exact order $n$ when exact addition proves
$nP=0$ and $(n/\ell)P\ne0$ for every prime $\ell\mid n$. Independence of
several points is proved by a relation matrix or by exhaustive enumeration in
the bounded coefficient box.

A complete torsion proof therefore has a lower half and an upper half:
explicit classes produce a subgroup $T$, while good reductions show that no
larger group can occur. A point count without a displayed rational class is
only an upper bound; a displayed relation without reductions is only a lower
bound.

### 10.3 Odd-prime saturation by reduction

Let $G\subseteq J(K)$ be a finitely generated subgroup containing
$J(K)[\ell]$, where $\ell$ is odd. Suppose good places
$v_1,\ldots,v_m$ of residue characteristic different from $\ell$ satisfy

$$
\ker\left(
G/\ell G\longrightarrow
\prod_i J(k_{v_i})/\ell J(k_{v_i})
\right)=0. \tag{10.2}
$$

Then $G$ is $\ell$-saturated in $J(K)$.

Indeed, if $\ell P=Q\in G$, reduction shows that the class of $Q$ belongs to
the kernel in (10.2). Hence $Q=\ell R$ for some $R\in G$. Then
$P-R\in J(K)[\ell]\subseteq G$, so $P\in G$. This proof explains every
hypothesis: reduction must be good, the residue characteristic must differ
from $\ell$, and rational $\ell$-torsion must already lie in $G$.

### 10.4 Saturation at two

When the exhibited subgroup reaches the two-Selmer bound, its image in
$J(K)/2J(K)$ is the whole Kummer image. If it also contains $J(K)[2]$, it is
two-saturated by the same division argument. Thus two-descent controls the
prime $2$ directly, while reduction kernels efficiently handle the remaining
possible index primes.

Only finitely many odd primes need be tested once an independent index bound
is known. Such a bound may come from heights or from a determinant comparison.
In rank zero, there is no free-part saturation problem: complete torsion
determination already gives the whole group.

## 11. Certificate design

### 11.1 The global ledger

A global descent certificate records:

- the factorization of $f$ and an integral basis for every field factor;
- the discriminant and the chosen set $S$;
- prime-ideal factorizations above $S$;
- unit generators and the $2$-torsion of the $S$-class groups;
- a basis of $L(S,2)$ and its norm matrix;
- a basis of the norm kernel, or the even-degree norm-compatible quotient.

The unit statement is certified by a regulator and an index bound, or by an
independent unit-index theorem with matching signature hypotheses. The class
statement is certified by a Minkowski bound and ideal relations. Merely
listing plausible units is not a proof of completeness.

### 11.2 The local ledger

For each $v\in S$, record the local factorization of $f$, the source
dimension, generators of $J(K_v)/2J(K_v)$, and their descent values. Express
the localized global basis and the local-image basis in one squareclass basis.
At two, state the modulus used for unit-square tests. At the real place, state
the sign order of the real factors.

The output is a pair of matrices: one for localization and one whose columns
span the local image. Membership of each global vector is then exact finite
linear algebra.

### 11.3 Linear algebra over squareclasses

Choose ordered global basis vectors $b_1,\ldots,b_n$. For every local
functional $\lambda$ vanishing on $\mathcal I_v$, form the row

$$
(\lambda(b_1),\ldots,\lambda(b_n))\in\mathbf F_2^n. \tag{11.1}
$$

Stacking all rows gives an obstruction matrix $M$. Then

$$
\operatorname{Sel}_2(J/K)=\ker M \tag{11.2}
$$

in odd degree. Displaying $M$ makes the final dimension reproducible and
exposes redundant local tests. In even degree, the same statement applies to
the fake space, followed by the true-lift test of Chapter 5.

### 11.4 Independent checks

Several checks catch different errors:

- resultants verify norms of algebra elements;
- the product formula verifies valuation columns;
- (7.2)--(7.4) verify local-image dimensions;
- exact Mumford addition verifies descent values of known sums;
- two good-prime point counts verify torsion independently of descent;
- the dimension identity (9.4) checks compatibility of rank and visible
  two-torsion.

Agreement is meaningful because the checks use different structures. A
repetition of the same squareclass calculation in another notation is not an
independent certificate.

## 12. The Jacobian of $X_1(13)$

### 12.1 The curve and its two points at infinity

A standard affine model is

$$
y^2+(x^3+x^2+1)y=x^2+x. \tag{12.1}
$$

Completing the square with $z=2y+x^3+x^2+1$ gives

$$
C_{13}:z^2=F(x), \tag{12.2}
$$

where

$$
F(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1. \tag{12.3}
$$

The polynomial is squarefree, with

$$
\operatorname{disc}(F)=-2^{12}13^2. \tag{12.4}
$$

The monic sextic has two rational points $\infty^+$ and $\infty^-$ above
infinity, distinguished by $z/x^3\to+1$ and $-1$. Neither is Weierstrass.
Thus this calculation belongs to the even-degree theory; applying (4.1)
would be invalid.

The six visible rational points are

$$
\infty^+,\ \infty^-,\ (0,0),\ (0,-1),\ (-1,0),\ (-1,-1) \tag{12.5}
$$

in the coordinates of (12.1). They are the rational cusps needed later, but
their modular meaning is not used in the Jacobian calculation.

At $x=0$ and $x=-1$, equation (12.1) becomes $y(y+1)=0$, verifying the four
affine points. Homogenizing (12.2) in weights $(1,3,1)$ gives
$z^2=x^6$ on the line at infinity, hence the two stated rational branches.
The nonzero discriminant proves affine smoothness and smoothness of the
projective genus-two model.

### 12.2 The sextic descent algebra

Put

$$
L_{13}=\mathbf Q[\theta]/(F(\theta)). \tag{12.6}
$$

The polynomial $F$ is irreducible over $\mathbf Q$. Its signature is
$(0,3)$, and the polynomial discriminant is (12.4). Away from $2$ the power
basis is maximal; the integral-basis check at $2$ and the ideal relations at
$2$ and $13$ give the complete set of squareclasses unramified outside

$$
S=\{2,13,\infty\}. \tag{12.7}
$$

Two elementary factorization checks used in that ledger are

$$
F(X)\equiv(X^3+X^2+1)^2\pmod2 \tag{12.8}
$$

and

$$
F(X)\equiv(X-3)^3
(X^3+11X^2+8X+12)\pmod{13}. \tag{12.9}
$$

The last expression denotes a product. The cubic factor in (12.9) is
coprime to $X-3$. These factorizations, together with the integral basis,
determine the primes above the bad rational primes and their ramification.

Irreducibility has an independent finite certificate: modulo $3$, the
polynomial has no factor of degree $1$, $2$, or $3$, as verified by the gcd
tests with $X^{3^i}-X$ for the proper divisors of six. Hence it is irreducible
over $\mathbf Q$. A direct interval check using

$$
F(x)=(x^3+x^2+1)^2+4x(x+1) \tag{12.9a}
$$

shows $F(x)>0$ outside $[-1,0]$. On that interval put
$q=-x(x+1)\le1/4$. Since $x^3+x^2+1=1+x^2(x+1)\ge1$, one has
$F(x)\ge1-4q\ge0$; equality in the last inequality would require
$x=-1/2$, where the first square is strictly larger than one. Thus $F$ has
no real root and the field has signature $(0,3)$.

The global squareclass calculation is most compactly recorded by dimensions:

$$
\begin{array}{c|c}
\text{space}&\mathbf F_2\text{-dimension}\\ \hline
L_{13}(S,2)&6\\
\text{after quotient by scalar classes}&3\\
\text{after the norm-compatible-pair relation}&2.
\end{array} \tag{12.10}
$$

These dimensions come from the unit and ideal relation matrix, not from
assuming the class group trivial. In particular its $2$-primary contribution
is included before the scalar quotient.

### 12.3 The finite two-descent calculation

At the real place there are no real field factors in $L_{13}$, so the sign
target is trivial. The two nontrivial global candidates in (12.10) are tested
at $2$ and $13$. Using the integral basis fixed above, unit squareclasses at
$2$ are tested modulo $8\mathcal O_{L_{13},2}$; at $13$, valuation parity and
residue-square tests on the two local factors suffice after the ramified
uniformizer is separated.

The exact local ledger is

$$
\begin{array}{c|c}
\text{stage}&\mathbf F_2\text{-dimension}\\ \hline
\text{global fake norm-compatible candidates}&2\\
\text{after the }2\text{-adic image}&1\\
\text{after the }13\text{-adic image}&0.
\end{array} \tag{12.11}
$$

If $b_1,b_2$ is the ordered basis of the last global line in (12.10), the
surviving obstruction functionals may be normalized to

$$
\begin{array}{c|cc}
&b_1&b_2\\ \hline
\mathbf Q_2&1&0\\
\mathbf Q_{13}&0&1.
\end{array} \tag{12.11b}
$$

This is the row-reduced form of the exact unit-square tests, not a deduction
from the desired rank. Invertible changes of the global basis alter the two
columns but preserve the zero kernel.

Each local image is complete by the local source-order calculation: the
factorization of $F$ over the relevant local field determines
$J(\mathbf Q_v)[2]$, and residue-disk representatives attain the dimension
given by (7.3) or (7.4).

It remains essential to lift from fake to true descent. The connecting
sequence of (2.7), with the rational divisor $\infty^+$ of degree one as
base divisor, shows that the kernel of the true-to-fake map is generated by
the infinity-difference alternative. Its associated norm-compatible pair
fails the $13$-adic lifting condition. Consequently

$$
\operatorname{Sel}_2(J_{13}/\mathbf Q)=0, \tag{12.12}
$$

and therefore

$$
\operatorname{rank}J_{13}(\mathbf Q)=0,
\qquad J_{13}(\mathbf Q)[2]=0. \tag{12.13}
$$

The second equality is also visible from irreducibility of $F$: there is no
nontrivial Galois-stable even branch subset modulo complement.

### 12.4 Torsion and the complete Jacobian

Let

$$
T=[\infty^- -\infty^+]\in J_{13}(\mathbf Q). \tag{12.14}
$$

The class $T$ is nonzero, because a principal divisor
$\infty^- -\infty^+$ would define a degree-one map from a genus-two curve to
$\mathbf P^1$.

The independently counted good reductions are

$$
\begin{array}{c|cc|c}
p&\#C_{13}(\mathbf F_p)&\#C_{13}(\mathbf F_{p^2})
&\#J_{13}(\mathbf F_p)\\ \hline
3&6&8&19\\
5&6&12&19.
\end{array} \tag{12.16}
$$

For a genus-two curve,

$$
\#J(\mathbf F_p)=
\frac{\#C(\mathbf F_p)^2+\#C(\mathbf F_{p^2})}{2}-p. \tag{12.17}
$$

Thus rational torsion injects into groups of order $19$ at both good primes.
Since (12.13) says the entire rational group is torsion, the nonzero class
$T$ has order dividing $19$ and therefore exact order $19$. The same
reduction bound shows there can be no further class. Together with (12.13),
this proves the first required finite
calculation:

$$
\boxed{J_{13}(\mathbf Q)=\langle T\rangle
\simeq\mathbf Z/19\mathbf Z.} \tag{12.18}
$$

This chapter determines the Jacobian. Determining which of its nineteen
classes lie on the Abel image is a separate finite curve calculation.

## 13. The mixed-seven Jacobian

### 13.1 The curve and visible classes

Consider

$$
C_7:z^2=f(t),\qquad
f(t)=t(t-1)(t^3-8t^2+5t+1). \tag{13.1}
$$

Expanded,

$$
f(t)=t^5-9t^4+13t^3-4t^2-t,
\qquad\operatorname{disc}(f)=7^4. \tag{13.2}
$$

This is a monic squarefree quintic, so it has a rational Weierstrass point
$\infty$ and the odd-degree theory applies. Put

$$
T_0=[t,0],\qquad T_1=[t-1,0],\qquad
A=[t^2-t+1,1-3t]. \tag{13.3}
$$

The first two classes are independent of order two. Exact division gives

$$
f-(1-3t)^2=(t^2-t+1)(t^3-8t^2+4t-1), \tag{13.4}
$$

so $A$ is a valid reduced class. One exact Cantor reduction gives

$$
2A=[t^2-t+1,3t-1]=-A. \tag{13.5}
$$

Hence $A$ has exact order three.

### 13.2 Arithmetic of the cubic factor

The descent algebra is

$$
L=\mathbf Q\times\mathbf Q\times K,
\qquad K=\mathbf Q(\theta),
\qquad\theta^3-8\theta^2+5\theta+1=0. \tag{13.6}
$$

Let $\alpha$ satisfy

$$
\alpha^3+\alpha^2-2\alpha-1=0. \tag{13.7}
$$

Direct substitution gives

$$
\theta=-1-\alpha+2\alpha^2,qquad
K=\mathbf Q(\zeta_7+\zeta_7^{-1}), \tag{13.8}
$$

and

$$
[\mathcal O_K:\mathbf Z[\theta]]=7,qquad
\operatorname{disc}(K)=49. \tag{13.9}
$$

The Minkowski bound is $14/9<2$, so every ideal class contains the unit ideal
and $K$ has class number one. The unit index calculation shows that
$\alpha$ and $\alpha+1$ form a system of fundamental units. Their norms and
the ramified prime generator satisfy

$$
N(\alpha)=1,qquad N(\alpha+1)=-1,qquad
N(2-\alpha)=7. \tag{13.10}
$$

Moreover,

$$
\theta=\frac{\alpha^3}{\alpha+1},qquad
1-\theta=\frac{\alpha^2}{(\alpha+1)^3}. \tag{13.11}
$$

The polynomial $X^3+X^2+1$ is irreducible over $\mathbf F_2$, so $2$ is
inert in $K$. The prime $7$ is totally ramified and generated by
$2-\alpha$. Thus all arithmetic entering the $S$-squareclasses for
$S=\{2,7,\infty\}$ is explicit.

The class-number proof is short: every ideal class contains an integral ideal
of norm at most $14/9$, and the only positive integer below that bound is
$1$. The norm identities in (13.10) follow from signed constant terms.
Reducing powers of $\alpha$ with (13.7) verifies (13.11) directly.

### 13.3 The global norm kernel

For a divisor disjoint from the branch points,

$$
\delta([u,v])=
\bigl((-1)^{\deg u}u(0),
(-1)^{\deg u}u(1),
(-1)^{\deg u}u(\theta)\bigr). \tag{13.12}
$$

The derivative rule gives

$$
e_0:=\delta(T_0)=(-1,-1,-\theta),qquad
e_1:=\delta(T_1)=(1,-1,1-\theta). \tag{13.13}
$$

Using (13.10)--(13.11), the $S$-unit norm kernel has the following basis:

$$
\begin{aligned}
e_0,e_1,\qquad
h_1&=(-1,1,-1),&h_2&=(1,-1,-1),\\
h_3&=(2,1,2),&h_4&=(1,2,2),\\
h_5&=(7,1,2-\alpha),&h_6&=(1,7,2-\alpha).
\end{aligned} \tag{13.14}
$$

Their norms are squares: respectively $1,1,1,1,16,16,49,49$. Independence
follows by valuation parity at the two rational factors, the inert prime over
$2$, the ramified prime over $7$, and the three independent unit signs and
squareclasses. Hence the global ambient space has dimension eight.

For spanning, the cubic-component squareclasses are generated by

$$
-1,\ \alpha,\ \alpha+1,\ 2,\ 2-\alpha. \tag{13.14a}
$$

The rational components are generated by $-1,2,7$. Writing all norms in that
rational basis and taking the kernel of the product-norm row gives exactly
the eight vectors in (13.14). This derives the basis from the complete unit
and ideal calculation rather than guessing it from visible torsion.

### 13.4 The local cuts

Write addition of the symbols in (13.14) for multiplication of squareclasses.
The complete real and $2$-adic images intersect the global space as

$$
\begin{aligned}
V_S\cap\mathcal I_\infty
&=\langle e_0,e_1,h_3,h_4,h_5,h_6\rangle,\\
V_S\cap\mathcal I_2
&=\langle e_0,e_1,h_1+h_5,h_2+h_6\rangle.
\end{aligned} \tag{13.15}
$$

At $2$, the cubic extension is unramified. Valuation parity and unit residues
modulo $8\mathcal O_{K,2}$ verify the second line. Completeness has an
independent dimension proof. The points with $t=-4$ and $t=13$ exist over
$\mathbf Q_2$ because

$$
f(-4)=4(-1055),\qquad f(13)=4(35529), \tag{13.16}
$$

and both parenthesized odd units are $1$ modulo $8$. Their descent values,
together with $e_0,e_1$, are independent. Since

$$
\dim_{\mathbf F_2}J(\mathbf Q_2)/2J(\mathbf Q_2)
=2+\dim_{\mathbf F_2}J(\mathbf Q_2)[2]=4, \tag{13.17}
$$

they generate the full local image.

At $7$, the cubic is irreducible over $\mathbf Q_7$ although its reduction
has a triple root, and

$$
J(\mathbf Q_7)[2]=\langle T_0,T_1\rangle. \tag{13.18}
$$

Equation (7.3) makes the local quotient two-dimensional, so these two classes
give its entire image. The sequential ledger is

$$
\begin{array}{c|c}
\text{space}&\mathbf F_2\text{-dimension}\\ \hline
S\text{-unit norm kernel}&8\\
\text{after the real image}&6\\
\text{after the }2\text{-adic image}&2\\
\text{after the }7\text{-adic image}&2.
\end{array} \tag{13.19}
$$

Equivalently, in the ordered basis of (13.14), an obstruction matrix is

$$
\begin{array}{c|cc|cccccc}
&e_0&e_1&h_1&h_2&h_3&h_4&h_5&h_6\\ \hline
\mathbf R&0&0&1&0&0&0&0&0\\
\mathbf R&0&0&0&1&0&0&0&0\\
\mathbf Q_2&0&0&0&0&1&0&0&0\\
\mathbf Q_2&0&0&0&0&0&1&0&0\\
\mathbf Q_2&0&0&1&0&0&0&1&0\\
\mathbf Q_2&0&0&0&1&0&0&0&1.
\end{array} \tag{13.20}
$$

Its kernel is exactly $\langle e_0,e_1\rangle$. Therefore

$$
\operatorname{Sel}_2(J/\mathbf Q)
=\langle\delta(T_0),\delta(T_1)\rangle,qquad
\operatorname{rank}J(\mathbf Q)=0. \tag{13.21}
$$

### 13.5 The Mordell-Weil group

Direct point counting gives

$$
\begin{array}{c|cc|c}
q&\#C_7(\mathbf F_q)&\#C_7(\mathbf F_{q^2})
&\#J(\mathbf F_q)\\ \hline
3&5&5&12\\
5&9&25&48.
\end{array} \tag{13.22}
$$

Thus rational torsion has order dividing $\gcd(12,48)=12$, prime by prime as
in (10.1). The subgroup generated by $A,T_0,T_1$ has order
$3\cdot2\cdot2=12$. Combining this lower bound with (13.21)--(13.22) proves
the second required finite calculation:

$$
\boxed{
J_7(\mathbf Q)=\langle A\rangle\oplus\langle T_0\rangle
\oplus\langle T_1\rangle
\simeq\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2.} \tag{13.23}
$$

Again, the statement concerns the complete Jacobian group. The further task
of testing which of its twelve classes lie on the embedded curve is a finite
Mordell--Weil sieve, logically downstream from (13.23).

The displayed subgroup already has twelve elements. The order-three group
$\langle A\rangle$ meets the two-primary group trivially. The classes
$T_0,T_1$ are distinct and nonzero by injectivity of the Abel map, and their
sum is the nonidentity reduced class $[t(t-1),0]$. Hence they generate a
group of order four before any reduction upper bound is invoked.

## 14. Odd-prime saturation in practice

### 14.1 A reduction-kernel criterion

The criterion (10.2) can be written entirely in matrices. Suppose
$G=\langle P_1,\ldots,P_r,T\rangle$, with the torsion subgroup already known.
For a good prime $q\ne\ell$, reduce the $P_i$ and express them in an
invariant-factor basis of $J(\mathbf F_q)$. Modulo $\ell$, this gives a matrix
$R_q$. Then

$$
\bigcap_q\ker R_q=0 \tag{14.1}
$$

is exactly the hypothesis required for $\ell$-saturation of the free
generators, after the torsion coordinates are included.

The proof does not assume that reduction is injective on the free group. It
uses only the implication that an $\ell$-divisible global point reduces to an
$\ell$-divisible finite point.

### 14.2 Choosing useful primes

A prime is useful for $\ell$-saturation only when
$J(\mathbf F_q)/\ell J(\mathbf F_q)$ is nonzero and the reductions of the
chosen generators detect a new direction. The factorization of the Frobenius
polynomial modulo $\ell$ predicts the target dimension, while exact Mumford
arithmetic supplies the actual columns.

Several small primes are usually better than one large prime: their kernel
intersection can be zero even when no single reduction map is injective. Bad
primes and primes equal to $\ell$ are excluded from this simple criterion.

### 14.3 Certificates for finite-index generators

For a positive-rank Jacobian, a complete generator certificate contains:

1. exact rational Mumford pairs and a height or specialization proof of their
   independence;
2. a two-descent showing their images span $J(K)/2J(K)$;
3. the full rational torsion subgroup;
4. an upper bound on the finite index;
5. reduction matrices satisfying (14.1) for every odd prime dividing that
   upper bound.

In the two rank-zero calculations of Chapters 12 and 13, steps 1, 2, 4, and
5 collapse: the descent proves no free part exists, and the exact reduction
bounds determine all torsion. The saturation language remains essential for
the positive-rank descents to which the same method will be applied.

## 15. Hypothesis and dependency ledger

### 15.1 What is assumed

The general descent theory used here supplies the Kummer injection, local
Kummer images, their equality with unramified cohomology at good places away
from $2$, Selmer finiteness, and the exact sequence (9.6). Its hypotheses
match the present setting: Jacobians are abelian varieties over number fields,
and multiplication by two is an isogeny in characteristic zero.

The exact genus-two arithmetic used here supplies unique reduced Mumford
pairs, total Cantor addition, finite-field point counting, specialization at
good primes, and torsion certificates. Its odd-degree formulas require a
monic squarefree quintic in characteristic different from two and a rational
Weierstrass point at infinity. Every use in Chapter 13 satisfies these
hypotheses. Chapter 12 uses the separately stated sextic divisor arithmetic
and never imports the quintic normal form unchanged.

The finite-field order formula rests on the Weil theorem for smooth proper
genus-two curves. Squarefreeness and good reduction are checked before each
use.

### 15.2 What is proved here

The new mathematical package consists of:

- the branch-algebra realization of $J[2]$ in odd and even degree;
- total $x-T$ evaluation, including moved divisors and derivative values;
- the exact norm condition and identification with the Kummer boundary;
- equality of odd-degree explicit and true Selmer groups;
- the true-to-fake comparison in even degree;
- finite $S$-squareclass enumeration with class-group corrections;
- complete local-image methods at real, odd, bad, and $2$-adic places;
- rank, torsion, and odd-prime saturation certificates;
- the complete Mordell--Weil calculations (12.18) and (13.23).

No rational-point classification is inferred solely from these Jacobian
groups. Recovering curve points requires testing the Abel image in the finite
group, which is a separate sieve problem.

### 15.3 Model boundaries

The hypotheses and their consequences can be summarized as follows.

| Assertion | Required hypotheses |
|---|---|
| $L$ is etale | $f$ squarefree |
| odd-degree norm-kernel identification | $\deg f=5$, $2\ne0$, rational branch point at infinity |
| Mumford formula $(-1)^{\deg u}u(\theta)$ | pointed monic quintic; use moving at branch support |
| fake quotient in sextic degree | squarefree sextic; a reference divisor fixes normalization |
| finite global squareclass space | number field and finite $S$, including class-group terms |
| unramified local equality | good reduction and residue characteristic not two |
| formula (7.4) | finite extension of $\mathbf Q_2$ and an abelian variety of dimension $g$ |
| torsion injection at $p$ | good reduction and torsion prime to $p$ |
| reduction saturation criterion | good primes away from $\ell$ and known rational $\ell$-torsion |

Neither characteristic two nor a curve without the stated rational divisor
is silently forced into the pointed odd-degree formulas. A birational change
to a quintic is permitted only when it sends an actual rational Weierstrass
point to infinity.

## 16. The completed two-descent package

### 16.1 The main theorem

**Theorem 16.1 (explicit odd-degree two-descent).** Let $K$ be a number field
and let $C/K$ be the smooth projective curve given by a monic squarefree
quintic $y^2=f(x)$. Put $J=\operatorname{Jac}(C)$ and
$L=K[T]/(f)$. Then:

1. the map

   $$
   [u,v]\longmapsto(-1)^{\deg u}u(\theta)
   \tag{16.1}
   $$

   extended at branch support by moving, identifies the Kummer injection
   $J(K)/2J(K)\hookrightarrow H^1(K,J[2])$ with an injection into
   $(L^\times/L^{\times2})_{N=1}$;
2. under this identification the explicit Selmer group cut out by all local
   $x-T$ images is the true $2$-Selmer group;
3. it is contained in the finite $S$-unit norm kernel for any $S$ containing
   the archimedean places, the places above two, and all places of bad
   reduction;
4. complete local images at the places of $S$ reduce its computation to
   finite linear algebra;
5. its dimension gives the rank bound (9.5), and exact reductions determine
   torsion and certify odd-prime saturation through (10.2).

**Proof.** The kernel sequence (2.4) and its surjectivity on signs prove the
cohomological identification. Chapter 3 identifies evaluation with the
Kummer boundary and proves the norm relation. Integral Kummer theory outside
$S$ gives the finite-support bound. Chapters 7--8 prove local completeness,
Chapter 9 gives the rank inequality, and Chapter 10 proves the torsion and
saturation criteria. $\square$

For a squarefree sextic, the same construction first yields the fake quotient
of Chapter 5. A true Selmer statement additionally requires the
norm-compatible pair and the diagonal connecting calculation.

### 16.2 The two finite calculations

For the sextic model of $X_1(13)$, the bad-place set is
$\{2,13,\infty\}$. The fake candidates are eliminated locally and the true
lifting kernel is checked separately. Exact reduction at $3$ and $5$ then
proves

$$
J_1(13)(\mathbf Q)\simeq\mathbf Z/19\mathbf Z. \tag{16.2}
$$

For the mixed-seven quintic, the bad-place set is
$\{2,7,\infty\}$. The eight-dimensional $S$-unit norm kernel is cut by the
real and $2$-adic images to the two visible Weierstrass classes; the $7$-adic
image confirms the result. Exact reduction at $3$ and $5$ proves

$$
J_7(\mathbf Q)\simeq
\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2. \tag{16.3}
$$

Both are complete Mordell--Weil statements: the rank upper bound, displayed
torsion lower bound, and good-reduction upper bound meet exactly.

### 16.3 Conclusion

Two-descent on a genus-two Jacobian is controlled by its branch points. Their
residue fields form the etale algebra $L$, their even subsets form $J[2]$, and
the function $x-T$ converts a divisor class into a squareclass. In odd degree,
the rational branch point at infinity makes the norm sequence exact in the
strongest possible form: the explicit norm kernel is the true cohomological
target. In even degree, scalar and connecting data survive, so a fake Selmer
calculation must be lifted before it can support a rank claim.

The global calculation is finite for a structural reason. Away from two and
bad reduction, local Kummer classes are unramified; ideals therefore have even
valuation outside a finite set. Units and $2$-torsion in class groups enumerate
all such squareclasses, norm equations cut the first global space, and complete
local images cut the Selmer group. Source-dimension formulas, residue-disk
representatives, and exact square tests turn local completeness into a
certificate.

Finally, descent is only one part of a complete Mordell--Weil argument. Exact
Mumford arithmetic proves relations, good reductions bound torsion, and
reduction kernels certify saturation. Applied to the two curves motivating
the theory, these layers determine their Jacobians exactly. The result is a
reusable bridge from hyperelliptic equations to rigorous rank bounds and
finite Mordell--Weil groups.
