# Quintic Cyclotomic Units and Kummer Arithmetic

## Contents

1. [Why the fifth cyclotomic field](#1-why-the-fifth-cyclotomic-field)
   - [The arithmetic problem](#11-the-arithmetic-problem)
   - [Standing data and notation](#12-standing-data-and-notation)
   - [The architecture of the argument](#13-the-architecture-of-the-argument)
2. [Coordinates, symmetries, and the real subfield](#2-coordinates-symmetries-and-the-real-subfield)
   - [The cyclotomic equation](#21-the-cyclotomic-equation)
   - [Integral basis, discriminant, and class number](#22-integral-basis-discriminant-and-class-number)
   - [Galois automorphisms and conjugation](#23-galois-automorphisms-and-conjugation)
   - [The real quadratic core](#24-the-real-quadratic-core)
   - [Integral coordinates](#25-integral-coordinates)
3. [The unique prime above five](#3-the-unique-prime-above-five)
   - [The uniformizer](#31-the-uniformizer)
   - [The exact factorization of five](#32-the-exact-factorization-of-five)
   - [Residues and normalized valuations](#33-residues-and-normalized-valuations)
   - [A coordinate formula for the valuation](#34-a-coordinate-formula-for-the-valuation)
   - [Galois action near the ramified prime](#35-galois-action-near-the-ramified-prime)
4. [Norms, conjugates, and associates](#4-norms-conjugates-and-associates)
   - [Absolute and relative norms](#41-absolute-and-relative-norms)
   - [The binary cyclotomic norm form](#42-the-binary-cyclotomic-norm-form)
   - [Associates of cyclotomic differences](#43-associates-of-cyclotomic-differences)
   - [Norms as valuation checks](#44-norms-as-valuation-checks)
5. [All units are cyclotomic](#5-all-units-are-cyclotomic)
   - [Roots of unity](#51-roots-of-unity)
   - [From complex units to real units](#52-from-complex-units-to-real-units)
   - [The units of the real quadratic subfield](#53-the-units-of-the-real-quadratic-subfield)
   - [The full unit theorem](#54-the-full-unit-theorem)
   - [Cyclotomic generators and examples](#55-cyclotomic-generators-and-examples)
6. [Primary elements and local unit arithmetic](#6-primary-elements-and-local-unit-arithmetic)
   - [Why congruence modulo powers of $\lambda$ matters](#61-why-congruence-modulo-powers-of-lambda-matters)
   - [Primary associates](#62-primary-associates)
   - [Units modulo $\lambda^2$](#63-units-modulo-lambda2)
   - [The quintic Kummer unit lemma](#64-the-quintic-kummer-unit-lemma)
   - [Sharpness of the congruence thresholds](#65-sharpness-of-the-congruence-thresholds)
7. [Fifth powers and ideal exponents](#7-fifth-powers-and-ideal-exponents)
   - [Frobenius modulo five](#71-frobenius-modulo-five)
   - [Extracting fifth powers from ideals](#72-extracting-fifth-powers-from-ideals)
   - [A global fifth-power criterion](#73-a-global-fifth-power-criterion)
   - [Normal forms modulo fifth powers](#74-normal-forms-modulo-fifth-powers)
8. [Kummer extensions of degree five](#8-kummer-extensions-of-degree-five)
   - [Radicals and cyclic extensions](#81-radicals-and-cyclic-extensions)
   - [When two radicals define the same field](#82-when-two-radicals-define-the-same-field)
   - [Ramification away from five](#83-ramification-away-from-five)
   - [The prime above five and the Kummer boundary](#84-the-prime-above-five-and-the-kummer-boundary)
9. [Coprimality of cyclotomic factors](#9-coprimality-of-cyclotomic-factors)
   - [Common prime divisors](#91-common-prime-divisors)
   - [The two valuation patterns](#92-the-two-valuation-patterns)
   - [The rational quotient](#93-the-rational-quotient)
   - [Normalized coprime factors](#94-normalized-coprime-factors)
10. [Fifth-power extraction for quintic equations](#10-fifth-power-extraction-for-quintic-equations)
    - [The abstract extraction principle](#101-the-abstract-extraction-principle)
    - [The case away from five](#102-the-case-away-from-five)
    - [The case above five](#103-the-case-above-five)
    - [Eliminating the unit in the ramified case](#104-eliminating-the-unit-in-the-ramified-case)
    - [The rational shadows](#105-the-rational-shadows)
11. [A reusable descent package](#11-a-reusable-descent-package)
    - [Signs, differences, and changes of root](#111-signs-differences-and-changes-of-root)
    - [The first-case conjugate quotient](#112-the-first-case-conjugate-quotient)
    - [A decision table for applications](#113-a-decision-table-for-applications)
    - [What has been achieved](#114-what-has-been-achieved)

## 1. Why the fifth cyclotomic field

### 1.1 The arithmetic problem

The identity

$$
X^5+Y^5=(X+Y)(X^4-X^3Y+X^2Y^2-XY^3+Y^4)
$$

is useful but incomplete. Over the integers it gives only two factors, and those factors can share the prime $5$. The fifth cyclotomic field replaces this coarse factorization by the five linear factors

$$
X^5+Y^5=\prod_{i=0}^4(X+\zeta^iY),
$$

where $\zeta$ is a primitive fifth root of unity. This is the point of adjoining $\zeta$: an exponent-five equation becomes a statement about a product of linear algebraic integers. If those linear factors are coprime, a fifth-power product forces every factor to be a unit times a fifth power. If they are not coprime, their common divisor is concentrated at one explicitly controlled prime.

That promising outline conceals three difficulties. First, the factors are never to be treated as ordinary integers: one needs the prime ideals and normalized valuations of the cyclotomic ring. Second, “a unit times a fifth power” is not yet a fifth power. The units must be classified and then tested by congruences. Third, the exceptional prime $5$ is totally ramified, so ordinary divisibility by $5$ becomes divisibility by the fourth power of a uniformizer. Every successful descent depends on keeping those two normalizations distinct.

This book develops precisely that arithmetic. It does not carry out a particular infinite descent. Instead it proves the local, unit, Kummer, and coprimality statements that make such a descent legitimate. The recurring lesson is that the exceptional behavior at $5$ is not an error term. It is rigid enough to remove the otherwise troublesome unit.

### 1.2 Standing data and notation

Fix

$$
K=\mathbf Q(\zeta),\qquad \zeta^5=1,\qquad \zeta\ne1.
$$

We write $\mathcal O=\mathcal O_K$ for the ring of integers of $K$. The three
structural facts on which the later ideal arguments depend are

$$
\mathcal O_K=\mathbf Z[\zeta],\qquad
\operatorname{disc}(K)=5^3,
\qquad
\operatorname{Cl}(\mathcal O_K)=1.
$$

These are not assumptions: Theorem 2.1 proves all three from the cyclotomic
polynomial, an index calculation, and Minkowski's theorem. In particular, it
will follow before the first ideal extraction that every nonzero ideal of
$\mathcal O$ is principal. We will nevertheless use ideal factorization first
and pass to element factorization only afterward; this prevents units from
being lost.

Our distinguished elements are

$$
\lambda=1-\zeta,
\qquad
\eta=1+\zeta+\zeta^{-1}.
$$

The symbol $\mathfrak p$ will denote the ideal $(\lambda)$. Complex conjugation is written with a bar, and

$$
\sigma_a(\zeta)=\zeta^a
\qquad (a\in(\mathbf Z/5\mathbf Z)^\times)
$$

denotes a Galois automorphism. The normalized $\mathfrak p$-valuation is $v_{\mathfrak p}$, so $v_{\mathfrak p}(\lambda)=1$. For a rational prime $q$ and a nonzero integer $n$, $v_q(n)$ has its usual normalization $v_q(q)=1$.

Book 1, _Valuations, DVRs, and Completions_, supplies the valuation language used throughout: unequal values do not cancel, a localization of a Dedekind domain at a nonzero prime is a discrete valuation ring, and normalized values measure prime-ideal exponents. We recall each normalization when it first becomes decisive.

### 1.3 The architecture of the argument

The arithmetic separates naturally into four layers:

$$
\begin{array}{c}
\text{cyclotomic identity and Galois symmetry}\\
\Downarrow\\
\text{the prime }(1-\zeta)\text{ and its valuation}\\
\Downarrow\\
\text{units, primary associates, and fifth-power tests}\\
\Downarrow\\
\text{coprime linear factors and Kummer extraction.}
\end{array}
$$

The order matters. Coprimality alone gives a unit ambiguity. Unit classification alone gives no information about which primes divide a factor. The two meet in a short congruence calculation modulo $\lambda^3$. That calculation is the decisive local step in the ramified case.

There are also two useful forms of every main conclusion. The ideal form is canonical and best for proving divisibility. The element form is concrete and best for descent. Passing from one to the other is exactly where class number one is used. No stronger factorization assumption will be hidden in the notation.

## 2. Coordinates, symmetries, and the real subfield

### 2.1 The cyclotomic equation

The minimal polynomial of $\zeta$ over $\mathbf Q$ is

$$
\Phi_5(T)=T^4+T^3+T^2+T+1.
$$

It is monic with integer coefficients, so $\zeta$ is an algebraic integer.
Consequently $[K:\mathbf Q]=4$, and

$$
1+\zeta+\zeta^2+\zeta^3+\zeta^4=0.
\tag{2.1}
$$

Every element of $K$ has a unique expression

$$
a_0+a_1\zeta+a_2\zeta^2+a_3\zeta^3,
\qquad a_i\in\mathbf Q,
$$

and the integer combinations form the order

$$
A=\mathbf Z[\zeta].
$$

The next section proves that this order is the full ring of integers; that
conclusion must not be built into the choice of coordinates. The relation
(2.1) is more than a way to shorten powers: it makes all four nontrivial fifth
roots symmetric and turns every conjugate of $1-\zeta$ into an explicit
associate.

The four embeddings of $K$ into $\mathbf C$ send $\zeta$ to $\zeta,\zeta^2,\zeta^3,\zeta^4$. There are no real embeddings. They occur in two conjugate pairs, so the norm of every nonzero element is real, and the norm of a unit is positive. In particular, a unit of $\mathcal O$ always has absolute norm $1$, not $-1$.

Thus $K$ is quartic and totally imaginary, with signature

$$
(r_1,r_2)=(0,2).
$$

This will determine both the sign of the discriminant and the archimedean
factor in Minkowski's bound.

### 2.2 Integral basis, discriminant, and class number

We now prove the arithmetic facts announced in Section 1.2. The index step is
essential: computing the discriminant of the visible order
$\mathbf Z[\zeta]$ does not by itself prove that this order is maximal.

**Theorem 2.1 (arithmetic foundation).** One has

$$
\boxed{
\mathcal O_K=\mathbf Z[\zeta],\qquad
\operatorname{disc}(K)=+125,\qquad
\operatorname{Cl}(\mathcal O_K)=1.
}
$$

Consequently $\mathcal O_K$ is a principal ideal domain, hence also a unique
factorization domain.

**Proof strategy.** First compute the discriminant of the power basis from
$\Phi_5'$. Its only possible defect from the full ring of integers is then an
index of five. The shifted polynomial for $\lambda=1-\zeta$ gives distinct
$5$-adic values for the four power-basis terms, excluding that index. Finally,
the Minkowski bound is strictly less than two, so every ideal class contains
the unit ideal.

**Proof.** We use the convention

$$
\operatorname{disc}(b_1,\ldots,b_4)
=\det\bigl(\operatorname{Tr}_{K/\mathbf Q}(b_ib_j)\bigr).
$$

For a monic separable irreducible polynomial $f$ of degree four, let $\alpha$
be one root and let $\alpha_1,\ldots,\alpha_4$ be its conjugates. The
Vandermonde determinant gives

$$
\operatorname{disc}(1,\alpha,\alpha^2,\alpha^3)
=\prod_{i<j}(\alpha_i-\alpha_j)^2
=(-1)^6\prod_{i=1}^4 f'(\alpha_i).
$$

Take $f=\Phi_5$. Differentiating

$$
(T-1)\Phi_5(T)=T^5-1
$$

and evaluating at $\zeta^a$, for $1\le a\le4$, gives

$$
\Phi_5'(\zeta^a)=\frac{5\zeta^{4a}}{\zeta^a-1}.
$$

Now $\zeta^{4(1+2+3+4)}=\zeta^{40}=1$, while the four minus signs cancel in

$$
\prod_{a=1}^4(\zeta^a-1)
=\prod_{a=1}^4(1-\zeta^a)
=\Phi_5(1)=5.
$$

Therefore the visible order $A=\mathbf Z[\zeta]$ has

$$
\boxed{\operatorname{disc}(A)=5^3=125.}
\tag{2.2}
$$

The sign here is positive, not merely an absolute-value convention. It agrees
with the general sign $(-1)^{r_2}$ because $r_2=2$.

Let

$$
m=[\mathcal O_K:A].
$$

The discriminant-index formula says

$$
\operatorname{disc}(A)=m^2\operatorname{disc}(K).
\tag{2.3}
$$

Since the field discriminant is an integer, (2.2) shows that $m^2$ divides
$5^3$. Hence $m=1$ or $m=5$. We rule out the latter directly.

For the shifted element $\lambda=1-\zeta$, consider

$$
g(X)=\Phi_5(1-X)
=X^4-5X^3+10X^2-10X+5.
$$

We have $g(\lambda)=0$, and $g$ is Eisenstein at $5$. We spell out the
valuation argument needed for maximality instead of treating that observation
as an integral-basis black box. The defining equation rearranges to

$$
\lambda^4=5(\lambda^3-2\lambda^2+2\lambda-1).
\tag{2.4}
$$

Choose a prime ideal $\mathfrak P$ of $\mathcal O_K$ above $5$, and let
$\widetilde\zeta$ be the residue class of $\zeta$. In the residue field,
characteristic five gives

$$
(\widetilde\zeta-1)^5=\widetilde\zeta^5-1=0,
$$

so $\widetilde\zeta=1$ and $\lambda\in\mathfrak P$. The factor in parentheses
on the right of (2.4) is congruent to $-1$ modulo $\mathfrak P$ and is
therefore a $\mathfrak P$-adic unit. For the normalized valuation
$v_{\mathfrak P}$,

$$
4v_{\mathfrak P}(\lambda)
=v_{\mathfrak P}(5)
=e(\mathfrak P/5).
\tag{2.5}
$$

The value $v_{\mathfrak P}(\lambda)$ is a positive integer, so four divides
$e(\mathfrak P/5)$. Since the ramification index is at most
$[K:\mathbf Q]=4$, equality holds:

$$
e(\mathfrak P/5)=4,\qquad v_{\mathfrak P}(\lambda)=1.
$$

Indeed, the fundamental identity

$$
[K:\mathbf Q]=\sum_{\mathfrak Q\mid5}
e(\mathfrak Q/5)f(\mathfrak Q/5)=4
$$

now forces $f(\mathfrak P/5)=1$ and leaves no room for any other prime above
$5$. This preliminary argument is used only to settle the index; Chapter 3
will identify the same prime explicitly as $(\lambda)$ and record the exact
factorization of $5$.

Suppose for contradiction that $m=5$. The finite group
$\mathcal O_K/A$ has order five, so $5\mathcal O_K\subseteq A$. The binomial
change from $1,\zeta,\zeta^2,\zeta^3$ to
$1,\lambda,\lambda^2,\lambda^3$ is triangular with diagonal entries
$1,-1,1,-1$, hence unimodular. Thus this is also a $\mathbf Z$-basis of $A$,
and every $\alpha\in\mathcal O_K$ can be written

$$
\alpha=b_0+b_1\lambda+b_2\lambda^2+b_3\lambda^3,
\qquad b_i\in\tfrac15\mathbf Z.
$$

There is nothing to prove for $\alpha=0$. Otherwise, for each nonzero summand,

$$
v_{\mathfrak P}(b_i\lambda^i)=4v_5(b_i)+i.
$$

Here $v_5$ is the usual valuation extended to $\mathbf Q^\times$. The finite
values among these four terms are pairwise distinct modulo four, so the least
occurs only once and cannot cancel. Since $\alpha$ is integral,
$v_{\mathfrak P}(\alpha)\ge0$; hence every displayed summand has nonnegative
value. For $0\le i\le3$, the inequality
$4v_5(b_i)+i\ge0$ forces $v_5(b_i)\ge0$. Because the only possible
denominator of $b_i$ is five, all $b_i$ are integers. Thus every element of
$\mathcal O_K$ already lies in $A$, contradicting $m=5$. We have proved

$$
\mathcal O_K=A=\mathbf Z[\zeta],
\qquad
\operatorname{disc}(K)=+125.
$$

It remains to prove the class-number assertion. Minkowski's ideal-class
theorem says that every ideal class of a degree-$n$ field of signature
$(r_1,r_2)$ contains a nonzero integral ideal $I$ satisfying

$$
N(I)\le
\left(\frac4\pi\right)^{r_2}
\frac{n!}{n^n}\sqrt{|\operatorname{disc}(K)|}.
$$

Here $N(I)=|\mathcal O_K/I|$ is the absolute ideal norm. In our field,
$n=4$, $r_2=2$, and $|\operatorname{disc}(K)|=125$, so the exact bound is

$$
N(I)\le
\left(\frac4\pi\right)^2\frac{4!}{4^4}\sqrt{125}
=\frac{15\sqrt5}{2\pi^2}<2.
\tag{2.6}
$$

For the last strict inequality,

$$
(15\sqrt5)^2=1125<1296=36^2,\qquad \pi>3,
$$

so $15\sqrt5/(2\pi^2)<36/18=2$. The norm of a nonzero integral ideal is a
positive integer, so (2.6) forces $N(I)=1$. Then
$|\mathcal O_K/I|=1$, whence $I=\mathcal O_K$. Every ideal class is therefore
trivial:

$$
\operatorname{Cl}(\mathcal O_K)=1.
$$

The ring of integers is a Dedekind domain, and a Dedekind domain with trivial
ideal class group has every nonzero ideal principal. Thus $\mathcal O_K$ is a
PID, and every PID is a UFD. $\square$

This proof is deliberately field-specific. It uses neither a general formula
for cyclotomic class numbers nor a classification of imaginary quadratic
fields.

### 2.3 Galois automorphisms and conjugation

The Galois group is

$$
G=\operatorname{Gal}(K/\mathbf Q)
\cong(\mathbf Z/5\mathbf Z)^\times,
$$

with $\sigma_a\sigma_b=\sigma_{ab}$. Since $2$ generates $(\mathbf Z/5\mathbf Z)^\times$, the group is cyclic of order four. Complex conjugation is

$$
\overline{\phantom{x}}=\sigma_{-1}=\sigma_4,
\qquad \overline\zeta=\zeta^{-1}=\zeta^4.
$$

This cyclic structure has a unique subgroup of order two, generated by conjugation. Its fixed field is therefore the unique quadratic subfield of $K$. That field is real, and it will contain the infinite part of every unit.

When an expression is indexed by $i$ modulo $5$, conjugation replaces $i$ by $-i$. Thus

$$
\overline{x+\zeta^iy}=x+\zeta^{-i}y
$$

for rational $x,y$. This simple pairing is the source of both positivity of the norm form and the conjugate-quotient identities used after fifth-power extraction.

### 2.4 The real quadratic core

Put

$$
t=\zeta+\zeta^{-1}.
$$

Dividing (2.1) by $\zeta^2$ gives

$$
(\zeta^2+\zeta^{-2})+(\zeta+\zeta^{-1})+1=0.
$$

Since $\zeta^2+\zeta^{-2}=t^2-2$, we obtain

$$
t^2+t-1=0.
$$

Hence

$$
K^+=\mathbf Q(t)=\mathbf Q(\sqrt5),
\qquad
t=\frac{\sqrt5-1}{2}.
$$

The element

$$
\eta=1+t=1+\zeta+\zeta^{-1}=\frac{1+\sqrt5}{2}
$$

satisfies

$$
\eta^2-\eta-1=0,\qquad
\eta'=1-\eta=-\eta^{-1},\qquad
N_{K^+/\mathbf Q}(\eta)=-1.
\tag{2.7}
$$

Here the prime denotes the nontrivial conjugation of $K^+/\mathbf Q$. Because $K/K^+$ has degree two and $\eta$ is fixed by complex conjugation,

$$
N_{K/\mathbf Q}(\eta)=N_{K^+/\mathbf Q}(\eta)^2=1.
$$

The intersection $\mathcal O\cap K^+$ is $\mathbf Z[\eta]$. Indeed, if

$$
u=a_0+a_1\zeta+a_2\zeta^2+a_3\zeta^3\in\mathcal O
$$

is fixed by conjugation, use

$$
\bar\zeta=\zeta^4=-1-\zeta-\zeta^2-\zeta^3,
\qquad
\overline{\zeta^2}=\zeta^3,
\qquad
\overline{\zeta^3}=\zeta^2.
$$

Comparing coefficients in the integral basis gives $a_1=0$ and $a_2=a_3$. Hence

$$
u=a_0+a_2(\zeta^2+\zeta^3)
=a_0-a_2(1+t),
$$

an integral linear combination of $1$ and $\eta=1+t$. Conversely $\eta$ is visibly integral and fixed by conjugation. Thus

$$
\mathcal O_{K^+}=\mathbf Z[\eta].
\tag{2.8}
$$

The field $K^+$ is not a side calculation. Complex conjugation will reduce the unit problem in $K$ to the elementary Pell-type unit problem in this real quadratic ring.

### 2.5 Integral coordinates

Since $\zeta=1-\lambda$, the ring also has the integral basis

$$
1,\lambda,\lambda^2,\lambda^3.
$$

Indeed the change-of-basis matrix from $1,\zeta,\zeta^2,\zeta^3$ is triangular with diagonal entries $1,-1,1,-1$. Thus

$$
\mathcal O=\mathbf Z[\lambda],
$$

and every algebraic integer has a unique $\lambda$-coordinate expansion

$$
\alpha=b_0+b_1\lambda+b_2\lambda^2+b_3\lambda^3,
\qquad b_i\in\mathbf Z.
\tag{2.9}
$$

These are global coordinates, not an infinite power series. Nevertheless, after localizing at $(\lambda)$ they behave exactly like the first four digits in a totally ramified extension of $\mathbf Q_5$. The distinct residue classes of their valuations modulo four will make cancellation impossible between the four displayed terms.

## 3. The unique prime above five

### 3.1 The uniformizer

The element $\lambda=1-\zeta$ is the natural measure of proximity to the identity among fifth roots of unity. Its conjugates are

$$
1-\zeta^a=\lambda(1+\zeta+\cdots+\zeta^{a-1})
\qquad (a=1,2,3,4).
\tag{3.1}
$$

Taking the product over $a$ gives

$$
N_{K/\mathbf Q}(\lambda)
=\prod_{a=1}^4(1-\zeta^a)
=\Phi_5(1)=5.
\tag{3.2}
$$

Therefore the principal ideal $(\lambda)$ has absolute ideal norm $5$. Its quotient is a field with five elements, so

$$
\mathfrak p=(\lambda)
$$

is a prime ideal and

$$
\mathcal O/\mathfrak p\cong\mathbf F_5,
\qquad \zeta\longmapsto1.
\tag{3.3}
$$

This identifies the prime above $5$ concretely. The index argument in Theorem
2.1 already forced uniqueness and total ramification; the next identity
recovers both facts inside $\mathcal O$ and, more importantly, records the
exact unit relating $5$ and $\lambda^4$.

### 3.2 The exact factorization of five

The associates in (3.1) can be made completely explicit. From the definitions and (2.1),

$$
\begin{aligned}
1-\zeta^2&=\lambda(1+\zeta),\\
1-\zeta^3&=\lambda(1+\zeta+\zeta^2),\\
1-\zeta^4&=-\zeta^4\lambda.
\end{aligned}
$$

The unit identities

$$
1+\zeta=-\zeta^3\eta,\qquad
1+\zeta+\zeta^2=\zeta\eta
\tag{3.4}
$$

follow by multiplying out and using $\eta=1+\zeta+\zeta^4$. Substituting (3.4) into the product (3.2) yields the exact equality

$$
\boxed{5=\zeta^3\eta^2\lambda^4.}
\tag{3.5}
$$

Both $\zeta$ and $\eta$ are units, so at the ideal level

$$
\boxed{(5)=\mathfrak p^4.}
\tag{3.6}
$$

Thus $\mathfrak p$ is the unique prime of $\mathcal O$ above $5$, with ramification index four and residue degree one. The degree check is $4\cdot1=[K:\mathbf Q]$. Theorem 2.1 gives $\operatorname{disc}(K)=125$, so no rational prime other than $5$ ramifies; equation (3.6) gives the finer structure at the exceptional prime directly.

It is important not to abbreviate (3.6) as “$5=\lambda^4$.” The two elements differ by the nontrivial unit $\zeta^3\eta^2$. Ideal divisibility ignores this unit, but congruences and exact fifth-power equations do not.

### 3.3 Residues and normalized valuations

Let $v_{\mathfrak p}$ be the normalized valuation of the DVR $\mathcal O_{\mathfrak p}$. Then

$$
v_{\mathfrak p}(\lambda)=1,\qquad
v_{\mathfrak p}(5)=4.
\tag{3.7}
$$

For every nonzero rational integer $n$,

$$
\boxed{v_{\mathfrak p}(n)=4v_5(n).}
\tag{3.8}
$$

Indeed write $n=5^rm$ with $5\nmid m$. No prime above $5$ divides $m$, while (3.6) gives value $4r$ for $5^r$.

Equation (3.8) is the normalization conversion used most often in descent. A rational integer divisible once by $5$ has $\mathfrak p$-value four, whereas $1-\zeta$ has value one. Confusing these two measurements destroys the exceptional-case calculation.

For $a\not\equiv0\pmod5$, (3.1) and the nonzero residue

$$
1+\zeta+\cdots+\zeta^{a-1}\equiv a\pmod{\mathfrak p}
$$

give

$$
v_{\mathfrak p}(1-\zeta^a)=1.
\tag{3.9}
$$

In particular all four conjugates of $\lambda$ are uniformizers and are associates.

### 3.4 A coordinate formula for the valuation

The basis (2.9) makes $v_{\mathfrak p}$ computable without factoring an element. If

$$
\alpha=b_0+b_1\lambda+b_2\lambda^2+b_3\lambda^3\ne0,
$$

then

$$
\boxed{
v_{\mathfrak p}(\alpha)
=\min_{0\le i\le3}\{4v_5(b_i)+i\},
}
\tag{3.10}
$$

where the value of a zero coefficient is understood as $\infty$.

To prove this, the four summands have the indicated values by (3.8). Two finite values $4v_5(b_i)+i$ and $4v_5(b_j)+j$ cannot agree for distinct $i,j\in\{0,1,2,3\}$ because they are different modulo four. The least value therefore occurs once. By the unequal-value lemma from Book 1, no cancellation can raise it. This is a particularly clean instance of the principle that different ramification residues cannot cancel.

For example,

$$
v_{\mathfrak p}(5+\lambda^2)=\min\{4,2\}=2,
$$

even though both summands vanish modulo $\mathfrak p$. The smaller $\mathfrak p$-value, not ordinary integer divisibility, controls the sum.

### 3.5 Galois action near the ramified prime

Every Galois automorphism preserves the unique prime $\mathfrak p$, and

$$
\sigma_a(\lambda)=1-\zeta^a
=\lambda c_a,\qquad
c_a=1+\zeta+\cdots+\zeta^{a-1}\in\mathcal O^\times.
\tag{3.11}
$$

Moreover $c_a\equiv a\pmod\lambda$. Hence all Galois automorphisms preserve $v_{\mathfrak p}$.

Complex conjugation gives the especially useful exact formula

$$
\overline\lambda=1-\zeta^{-1}=-\zeta^{-1}\lambda=-\zeta^4\lambda.
\tag{3.12}
$$

Reduction modulo $\lambda$ sends every $\zeta^a$ to $1$, so every Galois automorphism acts trivially on $\mathcal O/\mathfrak p$. Consequently

$$
\sigma(\alpha)\equiv\alpha\pmod\lambda
\qquad(\alpha\in\mathcal O,\ \sigma\in G).
\tag{3.13}
$$

This congruence is weak but pervasive. For a unit $u$, it implies $u/\bar u\equiv1\pmod\lambda$; that observation will eliminate half of the possible roots of unity when the full unit group is determined.

For comparison, primes away from five have no ramification. Their splitting is determined by the order of the residue cardinality modulo five. Let $q\ne5$ be rational and put

$$
f=\operatorname{ord}_{(\mathbf Z/5\mathbf Z)^\times}(q).
$$

A primitive fifth root first appears over $\mathbf F_q$ in $\mathbf F_{q^f}$, because $f$ is the least positive exponent for which $5\mid q^f-1$. Hence every irreducible factor of $\Phi_5$ modulo $q$ has degree $f$. Since $q$ does not divide the discriminant $5^3$, these factors are distinct and correspond to distinct unramified primes of $\mathcal O$ above $q$. There are $4/f$ such primes:

$$
\begin{array}{c|c|c}
q\bmod5 & f & \text{splitting in }K\\ \hline
1 & 1 & \text{four primes of degree }1\\
4 & 2 & \text{two primes of degree }2\\
2,3 & 4 & \text{one prime of degree }4.
\end{array}
\tag{3.14}
$$

This table explains why later gcd statements must use prime ideals rather than rational primes. When $q\equiv1\pmod5$, different primes over the same rational $q$ can divide different cyclotomic factors.

## 4. Norms, conjugates, and associates

### 4.1 Absolute and relative norms

The absolute norm is

$$
N(\alpha)=N_{K/\mathbf Q}(\alpha)
=\prod_{a=1}^4\sigma_a(\alpha).
$$

Because the embeddings occur in conjugate pairs,

$$
N(\alpha)=|\sigma_1(\alpha)|^2|\sigma_2(\alpha)|^2>0
$$

for $\alpha\ne0$. Thus $N(\alpha)$ is a positive rational number, and it is a positive integer when $\alpha\in\mathcal O$. In particular,

$$
N(u)=1\qquad(u\in\mathcal O^\times).
\tag{4.1}
$$

The relative norm to the real subfield is even more concrete:

$$
N_{K/K^+}(\alpha)=\alpha\bar\alpha.
$$

For the uniformizer,

$$
N_{K/K^+}(\lambda)
=(1-\zeta)(1-\zeta^{-1})
=2-(\zeta+\zeta^{-1})=3-\eta.
\tag{4.2}
$$

Taking the real quadratic norm of (4.2) recovers $N(\lambda)=5$. Also $(\sqrt5)^2=5$ and (3.7) show

$$
v_{\mathfrak p}(\sqrt5)=2;
$$

thus $\sqrt5$ is an associate of $\lambda^2$ in $\mathcal O$.

Norms are multiplicative and insensitive to associates up to the norm of a unit, which is one here. Consequently associates have exactly the same positive absolute norm. The converse is false in general: equal norm does not force two algebraic integers to be associates. We will use norm only after ideal or divisibility information has supplied the missing direction.

### 4.2 The binary cyclotomic norm form

For rational integers $x,y$,

$$
\begin{aligned}
N(x+\zeta y)
&=\prod_{a=1}^4(x+\zeta^ay)\\
&=x^4-x^3y+x^2y^2-xy^3+y^4.
\end{aligned}
\tag{4.3}
$$

When $x+y\ne0$, this is equivalently

$$
\boxed{
N(x+\zeta y)=\frac{x^5+y^5}{x+y}.
}
\tag{4.4}
$$

The quotient expression explains why this norm appears in quintic equations. The product expression explains why it is positive, even when the alternating polynomial does not look obviously positive.

The relative norm displays the same positivity in the real subfield:

$$
(x+\zeta y)(x+\zeta^{-1}y)
=x^2+(\eta-1)xy+y^2.
\tag{4.5}
$$

Applying the other real embedding, which sends $\eta-1$ to $-\eta$, gives the second positive quadratic factor. Their product is (4.3).

As a check, $x=y=1$ gives

$$
N(1+\zeta)=1-1+1-1+1=1,
$$

so $1+\zeta$ is a unit. This also follows from (3.4).

### 4.3 Associates of cyclotomic differences

The factorization (3.1) proves more than equality of valuations.

**Proposition 4.1 (cyclotomic-difference associates).** If $a,b$ are not divisible by $5$, then $1-\zeta^a$ and $1-\zeta^b$ are associates. More generally, if $a\not\equiv b\pmod5$, then

$$
\zeta^a-\zeta^b
$$

is an associate of $\lambda$.

**Proof strategy.** Factor out a root of unity and reduce the remaining exponent modulo five.

**Proof.** We have

$$
\zeta^a-\zeta^b
=\zeta^b(\zeta^{a-b}-1).
$$

The first factor is a unit. Since $a-b$ is nonzero modulo five, (3.1) writes the second factor as $-\lambda$ times an element congruent to $a-b$ modulo $\lambda$, hence times a unit. $\square$

This proposition is the engine behind the later gcd calculation. The difference of two linear cyclotomic factors contains no mysterious prime: apart from factors already dividing $x$ or $y$, its only possible new prime is $\mathfrak p$.

### 4.4 Norms as valuation checks

Book 1 proves that the valuation of a field norm is the residue-degree-weighted sum of the valuations over a base prime. Here there is one prime above $5$ and its residue degree is one, so

$$
v_5(N(\alpha))=v_{\mathfrak p}(\alpha)
\qquad(\alpha\in K^\times).
\tag{4.6}
$$

The normalizations really do agree: for $\alpha=5$, the left side is $v_5(5^4)=4$ because $N_{K/\mathbf Q}(5)=5^4$, and the right side is $4$. For $\alpha=\lambda$, both sides equal one.

Formula (4.6) is a valuable audit tool. If a calculation predicts $v_{\mathfrak p}(x+\zeta y)=1$, then its norm must be divisible by exactly one ordinary factor of $5$. Conversely, the norm alone cannot identify other prime-ideal valuations when a rational prime splits into several primes; the uniqueness above $5$ is what makes (4.6) so simple.

There is a second rigidity principle that is especially useful when a field-level fifth power happens to be rational.

**Proposition 4.2 (rational fifth-power rigidity).** One has

$$
(K^\times)^5\cap\mathbf Q^\times=(\mathbf Q^\times)^5.
\tag{4.7}
$$

Consequently, if an ordinary integer is a fifth power in $K$, then it is already the fifth power of an ordinary integer.

**Proof strategy.** Inspect the equation at a prime of $K$ above each rational prime. If one rational prime occurs to an exponent not divisible by five, the equation $\beta^5=a$ forces that prime's ramification index in $K/\mathbf Q$ to be divisible by five. This is impossible in a degree-four extension.

**Proof.** Suppose $\beta\in K^\times$ and $\beta^5\in\mathbf Q^\times$. For every $\sigma\in G$,

$$
\left(\frac{\sigma(\beta)}{\beta}\right)^5=1.
$$

Thus $\sigma(\beta)/\beta\in\mu_5$, but we will use valuations rather than try to turn these ratios into an ordinary character.

Put $a=\beta^5\in\mathbf Q^\times$, and write the prime factorization of $a$ with possibly negative integer exponents. If some exponent $m=v_q(a)$ is not divisible by five, choose a prime $\mathfrak Q$ of $\mathcal O$ above $q$, and let $e=e(\mathfrak Q/q)$. The normalized valuation at $\mathfrak Q$ gives

$$
5v_{\mathfrak Q}(\beta)=v_{\mathfrak Q}(a)=e\,m.
$$

Because $5\nmid m$, it follows that $5\mid e$. On the other hand, the local degree inequality gives

$$
e\le ef\le [K:\mathbf Q]=4,
$$

a contradiction. Therefore every prime exponent of $a$ is divisible by five. Since the exponent is odd, the sign causes no obstruction, and $a=c^5$ for some $c\in\mathbf Q^\times$. This is exactly (4.7).

If $a=n\in\mathbf Z$ and $n=c^5$ with $c=r/s$ in lowest terms, then $s^5\mid r^5$, so $s=1$ and $c\in\mathbf Z$. $\square$

An immediate companion is the norm test

$$
\alpha=u\beta^5\quad\Longrightarrow\quad
N(\alpha)=N(\beta)^5,
\tag{4.8}
$$

because $N(u)=1$. This implication does not reverse: a fifth-power norm does not force an algebraic integer to be a unit times a fifth power, since the norm combines prime exponents over split rational primes.

## 5. All units are cyclotomic

### 5.1 Roots of unity

Before finding all units, we must identify the finite ones. The roots of unity already visible in $K$ are

$$
\mu_{10}=\{\pm\zeta^a:0\le a<5\}.
$$

There are no others. If a primitive $m$th root lies in a degree-four field, then $\varphi(m)$ divides four. The possibilities are

$$
m\in\{1,2,3,4,5,6,8,10,12\}.
$$

Orders $3$ and $6$ introduce the imaginary quadratic field $\mathbf Q(\sqrt{-3})$; orders $4$, $8$, and $12$ introduce $\mathbf Q(i)$. Either would contradict the fact that $K^+=\mathbf Q(\sqrt5)$ is the unique quadratic subfield of the cyclic quartic field $K$. The remaining orders divide ten. Hence

$$
\boxed{\mu(K)=\mu_{10}=\langle-\zeta\rangle.}
\tag{5.1}
$$

There is a useful elementary principle behind the next step.

**Lemma 5.1 (Kronecker's bounded-conjugates lemma).** Let $\alpha$ be a nonzero algebraic integer. If every conjugate of $\alpha$ has complex absolute value at most one, then $\alpha$ is a root of unity.

**Proof strategy.** The coefficients of the monic polynomial whose roots are the powers of the conjugates remain bounded integers. Only finitely many such polynomials can occur, so two powers coincide.

**Proof.** Let $d$ be the degree of $\alpha$. For every $n\ge1$, the conjugates of $\alpha^n$ still have absolute value at most one. Each coefficient of their monic characteristic polynomial is an elementary symmetric function of at most $d$ numbers of absolute value at most one. Its absolute value is bounded by a constant depending only on $d$. These coefficients are rational algebraic integers and hence integers. There are therefore only finitely many possible polynomials. Infinitely many powers $\alpha^n$ lie among the roots of this finite collection, so $\alpha^r=\alpha^s$ for some $r>s$. Since $\alpha\ne0$, it follows that $\alpha^{r-s}=1$. $\square$

The hypothesis that $\alpha$ be integral matters. A rational number such as $1/2$ has its only conjugate inside the unit circle but is not a root of unity.

### 5.2 From complex units to real units

Let $u\in\mathcal O^\times$. For every embedding $\sigma:K\hookrightarrow\mathbf C$,

$$
\left|\sigma\left(\frac{u}{\bar u}\right)\right|=1,
$$

because the numerator and denominator are complex conjugates after a possible reindexing of embeddings. The quotient $u/\bar u$ is again an algebraic-integer unit. Lemma 5.1 therefore makes it a root of unity.

At first this only places $u/\bar u$ in $\mu_{10}$. Reduction modulo $\lambda$ sharpens the answer. From (3.13),

$$
\frac{u}{\bar u}\equiv1\pmod\lambda.
$$

The roots $-\zeta^a$ reduce to $-1$, not $1$, in $\mathbf F_5$. Consequently

$$
\frac{u}{\bar u}\in\mu_5.
\tag{5.2}
$$

The squaring map $\mu_{10}\to\mu_5$ is surjective. Choose $\rho\in\mu_{10}$ with

$$
\rho^2=\frac{u}{\bar u}.
$$

Since $\bar\rho=\rho^{-1}$, the unit $v=u/\rho$ satisfies

$$
\frac{v}{\bar v}
=\frac{u}{\bar u}\frac{\bar\rho}{\rho}
=\rho^2\rho^{-2}=1.
$$

Thus $v$ is real. We have proved that every unit is a root of unity times a unit of $\mathcal O_{K^+}$.

This argument is worth remembering. Absolute values show that the quotient by conjugation is torsion; reduction at the ramified prime decides which torsion can occur. Neither step alone gives the result.

### 5.3 The units of the real quadratic subfield

We now determine the units of $\mathbf Z[\eta]$ without appealing to an unspecified fundamental-unit theorem.

**Theorem 5.2 (real unit theorem).** Every unit of $\mathbf Z[\eta]$ is of the form

$$
\pm\eta^n,\qquad n\in\mathbf Z.
$$

**Proof strategy.** Use powers of $\eta>1$ to move one real embedding of a unit into the interval $[1,\eta)$. The norm then controls its other embedding. Its integral trace lies in an interval containing only one possible integer.

**Proof.** Let $v\in\mathbf Z[\eta]^\times$. Change its sign so that its identity embedding is positive, and multiply by a suitable power of $\eta$ so that

$$
1\le v<\eta.
\tag{5.3}
$$

The other embedding is $v'=N(v)/v$, with $N(v)=\pm1$.

If $N(v)=1$, then $v'=1/v$ and

$$
2\le v+v'<\eta+1<3.
$$

The trace $v+v'$ is an integer, so it equals $2$. The equation $v+v^{-1}=2$ forces $v=1$.

If $N(v)=-1$, then $v'=-1/v$ and

$$
0\le v+v'=v-v^{-1}<\eta-\eta^{-1}=1.
$$

Again the trace is an integer, so it equals $0$, and $v-v^{-1}=0$ gives $v=1$. Undoing the sign and power of $\eta$ proves the claim. $\square$

The proof also explains why $\eta$ is the correct generator. Its two embeddings sit exactly at the boundary needed to trap the trace. A larger unit would not prove that smaller units were absent.

### 5.4 The full unit theorem

Combining Sections 5.2 and 5.3 gives the complete answer.

**Theorem 5.3 (units of the quintic cyclotomic ring).** Every unit of $\mathcal O$ has a unique expression

$$
\boxed{u=\pm\zeta^a\eta^n,}
\tag{5.4}
$$

where $a\in\{0,1,2,3,4\}$ and $n\in\mathbf Z$.

**Proof.** Existence follows from the reduction to real units and Theorem 5.2. For uniqueness, suppose $\zeta^a\eta^n=\pm\zeta^b\eta^m$. Then $\eta^{n-m}$ is a root of unity. Under the identity real embedding, $\eta>1$, so this is possible only when $n=m$. It then follows that $\zeta^{a-b}=\pm1$. A fifth root of unity cannot equal $-1$, and the chosen ranges give $a=b$ with the same sign. $\square$

Modulo fifth powers, only two exponents remain:

$$
\boxed{
\mathcal O^\times/(\mathcal O^\times)^5
=\{\zeta^a\eta^b(\mathcal O^\times)^5:0\le a,b<5\}
\cong(\mathbf Z/5\mathbf Z)^2.
}
\tag{5.5}
$$

The sign disappears because $-1=(-1)^5$. The two generators play different roles. The class of $\zeta$ measures a nonreal torsion ambiguity; the class of $\eta$ measures the real infinite-unit ambiguity. Congruences modulo successive powers of $\lambda$ will detect them one at a time.

### 5.5 Cyclotomic generators and examples

A cyclotomic unit is generated from roots of unity and quotients

$$
\frac{1-\zeta^a}{1-\zeta}
=1+\zeta+\cdots+\zeta^{a-1}.
$$

For $a=2$, identity (3.4) gives

$$
1+\zeta=-\zeta^3\eta.
$$

Thus $\eta$ itself is a root of unity times a cyclotomic unit. Theorem 5.3 now shows:

$$
\boxed{\text{Every unit of }\mathcal O\text{ is a cyclotomic unit.}}
\tag{5.6}
$$

This equality is special. In larger cyclotomic fields the cyclotomic units can have nontrivial finite index in the full unit group, an index closely related to the class number of the real subfield. Here the degree is small enough for the explicit unit $1+\zeta$ to generate the entire infinite direction.

Some examples help calibrate the formulas:

- $N(1+\zeta)=1$, and $1+\zeta$ is not a root of unity because its complex absolute value is $\eta$ in one conjugate pair.
- $\eta$ is real and has relative quadratic norm $-1$, but absolute norm $1$ in $K$.
- $-\zeta$ has order ten, whereas $\zeta$ has order five. Both represent the same torsion direction modulo fifth powers because the sign is itself a fifth power.

The last two points warn against using the sign of a real norm as though it were the sign of the absolute norm from $K$.

## 6. Primary elements and local unit arithmetic

### 6.1 Why congruence modulo powers of $\lambda$ matters

Unique factorization of ideals, followed by the principality proved in
Theorem 2.1, turns an ideal fifth power into an element of the form

$$
u\alpha^5,\qquad u\in\mathcal O^\times.
$$

The unit $u$ cannot simply be discarded: neither $\zeta$ nor $\eta$ is a fifth power. The ramified prime supplies a way to read the two unit exponents in (5.5). Modulo $\lambda^2$ one detects the $\zeta$-exponent; modulo $\lambda^3$ one also detects the $\eta$-exponent.

We say that an element $\alpha\in\mathcal O$ prime to $\lambda$ is **primary** if

$$
\alpha\equiv r\pmod{\lambda^2}
\tag{6.1}
$$

for some rational integer $r$ not divisible by $5$. The requirement $5\nmid r$ is automatic from $\lambda\nmid\alpha$. The exponent two is the first level at which a linear $\lambda$-coefficient appears, so it is the first level that can distinguish an element from its root-of-unity associates.

Some accounts use “semiprimary” for congruence to an integer modulo $\lambda$. In this field every element prime to $\lambda$ is semiprimary, because the residue field is $\mathbf F_5$. That weaker word carries no information here, so we will work directly with primary elements.

### 6.2 Primary associates

**Proposition 6.1 (unique primary root-of-unity associate).** If $\lambda\nmid\alpha$, there is a unique $k\in\mathbf Z/5\mathbf Z$ such that $\zeta^k\alpha$ is primary.

**Proof strategy.** Retain the first two $\lambda$-digits and use $\zeta^k=(1-\lambda)^k\equiv1-k\lambda\pmod{\lambda^2}$.

**Proof.** Write

$$
\alpha\equiv a+b\lambda\pmod{\lambda^2},
\qquad a,b\in\mathbf F_5,\quad a\ne0.
$$

Then

$$
\zeta^k\alpha
\equiv(1-k\lambda)(a+b\lambda)
\equiv a+(b-ka)\lambda\pmod{\lambda^2}.
$$

The coefficient of $\lambda$ vanishes exactly when $k=b/a$ in $\mathbf F_5$. $\square$

Primary elements are closed under multiplication, and the conjugate of a primary element is primary. Both statements follow directly from congruence to rational integers. A fifth power of a $\lambda$-adic unit is primary; in fact it satisfies a stronger congruence proved in Section 7.1.

For the factor $x+\zeta y$ with $5\nmid x+y$, we have

$$
x+\zeta y=(x+y)-y\lambda.
$$

Proposition 6.1 therefore selects

$$
k\equiv-\frac{y}{x+y}\pmod5
\tag{6.2}
$$

as the unique exponent for which $\zeta^k(x+\zeta y)$ is primary.

### 6.3 Units modulo $\lambda^2$

The first Kummer-type lemma removes the nonreal part of a unit.

**Theorem 6.2 (primary-unit lemma).** For a unit $u\in\mathcal O^\times$, the following are equivalent:

1. $u$ is primary;
2. $u\equiv r\pmod{\lambda^2}$ for some rational integer $r$;
3. $u$ is real;
4. $u=\pm\eta^n$ for some $n\in\mathbf Z$.

**Proof strategy.** Classification already gives $u=\pm\zeta^a\eta^n$. The real unit $\eta$ has no linear $\lambda$-term, while $\zeta^a$ has linear term $-a\lambda$.

**Proof.** Conditions 1 and 2 are the same for a unit, and 3 and 4 are equivalent by Theorem 5.3. It remains to compare the congruence. Since

$$
\zeta=1-\lambda
$$

and

$$
\eta=1+\zeta+\zeta^{-1}
\equiv3\pmod{\lambda^2},
$$

we have

$$
\pm\zeta^a\eta^n
\equiv\pm3^n(1-a\lambda)\pmod{\lambda^2}.
$$

This is congruent to a rational integer precisely when $a\equiv0\pmod5$. $\square$

The exponent two is sharp: every unit is congruent modulo $\lambda$ to an ordinary residue in $\mathbf F_5$, including the nonreal unit $\zeta$.

### 6.4 The quintic Kummer unit lemma

One more $\lambda$-adic digit detects whether the remaining real unit is a fifth power. In the quotient modulo $\lambda^4$, the geometric expansion gives

$$
\zeta^{-1}=(1-\lambda)^{-1}
\equiv1+\lambda+\lambda^2+\lambda^3\pmod{\lambda^4}.
$$

Therefore

$$
\boxed{
\eta=1+\zeta+\zeta^{-1}
\equiv3+\lambda^2+\lambda^3\pmod{\lambda^4}.
}
\tag{6.3}
$$

We only need the reduction modulo $\lambda^3$, but the extra term makes the expansion transparent.

**Theorem 6.3 (quintic Kummer unit lemma).** For $u\in\mathcal O^\times$, the following are equivalent:

1. $u$ is a fifth power in $\mathcal O^\times$;
2. $u\equiv r\pmod{\lambda^3}$ for some rational integer $r$;
3. $u\equiv r\pmod{5\mathcal O}$ for some rational integer $r$.

The implication from 3 to 2 uses $5\mathcal O=(\lambda^4)$; the content is that congruence modulo $\lambda^3$ already suffices.

**Proof strategy.** Reduce the normal form $\pm\zeta^a\eta^n$ modulo $\lambda^3$. The linear coefficient detects $a$, and after $a=0$ the quadratic coefficient detects $n$ modulo five. Conversely, a fifth power becomes rational modulo $5$ by the characteristic-five Frobenius map.

**Proof.** In the ring $\mathcal O/(\lambda^3)$, whose residue characteristic is five, equations (6.3) and $\zeta=1-\lambda$ give

$$
\zeta^a\equiv1-a\lambda+\binom a2\lambda^2,
$$

and, for every integer $n$,

$$
\eta^n
\equiv3^n\left(1+\frac n3\lambda^2\right)
\pmod{\lambda^3}.
\tag{6.4}
$$

The formula for negative $n$ follows by inversion; all coefficients are read in $\mathbf F_5$, where $3$ is invertible.

Suppose $u=\pm\zeta^a\eta^n$ is congruent to an integer modulo $\lambda^3$. Its linear coefficient in (6.4) is $\mp a3^n$, so $a\equiv0\pmod5$. Its quadratic coefficient then becomes $\pm n3^{n-1}$, so $n\equiv0\pmod5$. Hence

$$
u=\pm\eta^{5m}=(\pm\eta^m)^5.
$$

Thus 2 implies 1. If 1 holds, Section 7.1 will show directly that every integral fifth power is congruent to a rational integer modulo $5\mathcal O$, proving 1 implies 3. Finally 3 implies 2 because $(5)=(\lambda^4)\subset(\lambda^3)$. $\square$

This is the unit-removal theorem needed in ramified quintic descent. Its strength comes from the unusually explicit unit group. The statement is not a generic property of units in arbitrary cyclotomic fields.

### 6.5 Sharpness of the congruence thresholds

Two counterexamples show exactly what each modulus accomplishes.

First,

$$
\zeta\equiv1\pmod\lambda,
$$

but $\zeta$ is not real and is not a fifth power. Thus modulus $\lambda$ cannot imply the primary-unit lemma.

Second, (6.3) gives

$$
\eta\equiv3\pmod{\lambda^2},
$$

so $\eta$ is primary, but its exponent in (5.4) is one and it is not a fifth power. Thus modulus $\lambda^2$ cannot imply Theorem 6.3. The nonzero $\lambda^2$-coefficient of $\eta$ is precisely why modulus $\lambda^3$ succeeds.

There is also a conceptual counterexample to a tempting global shortcut. Every prime-ideal valuation of $\eta$ is zero, hence divisible by five, yet $\eta$ is not a fifth power. Divisibility of ideal exponents never removes the unit ambiguity by itself.

The filtration of local principal units explains why the exponent five creates a four-step jump. Put

$$
U^n=1+\lambda^n\mathcal O_{\mathfrak p}\qquad(n\ge1).
$$

If $n\ge2$ and $x\in\lambda^n\mathcal O_{\mathfrak p}$ has exact value $n$, then

$$
(1+x)^5-1=5x+10x^2+10x^3+5x^4+x^5.
\tag{6.5}
$$

The five displayed terms have values

$$
n+4,\quad 2n+4,\quad 3n+4,\quad 4n+4,\quad 5n.
$$

For $n\ge2$, the first is uniquely smallest. It follows that

$$
v_{\mathfrak p}\bigl((1+x)^5-1\bigr)=n+4.
\tag{6.6}
$$

Thus the fifth-power map carries $U^n$ into $U^{n+4}$ and raises the exact depth by four once $n\ge2$. The number four is the ramification index of $5$. At depth one the first and last values in (6.5) both equal five, so cancellation can occur; the exceptional behavior of roots of unity lives precisely at this shallow level.

The finite quotients make the digit count concrete. Since the ideal norm of $(\lambda^m)$ is $5^m$,

$$
|\mathcal O/(\lambda^m)|=5^m.
\tag{6.7}
$$

For $m\le4$, this quotient has characteristic five because $5\in(\lambda^4)\subseteq(\lambda^m)$. Every class modulo $\lambda^3$ therefore has a unique expression

$$
a_0+a_1\lambda+a_2\lambda^2,
\qquad a_i\in\mathbf F_5.
\tag{6.8}
$$

The Kummer unit lemma can now be read digit by digit. The constant digit records the residue of a unit. The linear digit records its $\zeta$-class. Once that digit vanishes, the quadratic digit records its $\eta$-class. This also explains why no analytic approximation or infinite expansion is hidden in the proof: only the three finite digits in (6.8) are used.

As a worked calculation, take

$$
u=\zeta^2\eta^7.
$$

Modulo fifth powers its class is $\zeta^2\eta^2$. It is not primary because the linear digit supplied by $\zeta^2$ is nonzero. Multiplication by $\zeta^{-2}$ produces the real unit $\eta^7$, which is primary but is not a fifth power because $7\not\equiv0\pmod5$. The identity

$$
\eta^7=\eta^2(\eta)^5
$$

displays its remaining class. Modulo $\lambda^3$,

$$
\eta^7\equiv3^7\left(1+\frac73\lambda^2\right),
$$

and the nonzero quadratic digit detects exactly that obstruction. By contrast, $\eta^{10}=(\eta^2)^5$ has neither a linear nor a quadratic obstruction and is rational modulo $5\mathcal O$.

The example shows why passing to the primary associate is a normalization rather than a complete solution. It removes the torsion direction canonically, but five real unit classes remain.

## 7. Fifth powers and ideal exponents

### 7.1 Frobenius modulo five

The quotient $\mathcal O/5\mathcal O$ has characteristic five. For

$$
\alpha=a_0+a_1\zeta+a_2\zeta^2+a_3\zeta^3\in\mathcal O,
$$

the Frobenius identity and $\zeta^5=1$ give

$$
\alpha^5
\equiv a_0^5+a_1^5+a_2^5+a_3^5
\equiv a_0+a_1+a_2+a_3
\pmod{5\mathcal O}.
\tag{7.1}
$$

Thus:

**Proposition 7.1 (rational residue of a fifth power).** Every fifth power in $\mathcal O$ is congruent to a rational integer modulo $5\mathcal O$, and hence modulo $\lambda^4$.

This congruence is much stronger than merely reducing $\zeta$ to $1$ modulo $\lambda$. It is the converse direction in the Kummer unit lemma and the bridge by which a fifth-power factor transfers a rational congruence to its accompanying unit.

One should not reverse Proposition 7.1 for arbitrary algebraic integers. For instance, an ordinary rational prime $q\ne5$ is rational modulo $5$ but need not be a fifth power in $K$. The converse becomes valid only after all prime-ideal exponents are already known to be multiples of five.

### 7.2 Extracting fifth powers from ideals

The class-number-one conclusion of Theorem 2.1 enters in a precise two-step
argument.

**Proposition 7.2 (ideal-to-element extraction).** Let $0\ne\alpha\in\mathcal O$.

1. If every prime-ideal exponent in $(\alpha)$ is divisible by five, then
   $$
   \alpha=u\beta^5
   $$
   for some $u\in\mathcal O^\times$ and $\beta\in\mathcal O$.
2. More generally, if
   $$
   v_{\mathfrak p}(\alpha)\equiv r\pmod5,
   \qquad 0\le r<5,
   $$
   and every prime-ideal exponent away from $\mathfrak p$ is divisible by five, then
   $$
   \alpha=u\lambda^r\beta^5.
   $$

**Proof strategy.** Divide the ideal by the indicated power of $\mathfrak p$. The remaining ideal has all exponents divisible by five, so it is the fifth power of an ideal. Theorem 2.1 makes that ideal principal. Equality of principal ideals then leaves exactly a unit.

**Proof.** In the first case, unique factorization of ideals gives $(\alpha)=\mathfrak a^5$. By Theorem 2.1, write $\mathfrak a=(\beta)$. Then $(\alpha)=(\beta^5)$, so $\alpha=u\beta^5$ for a unit $u$. In the second case,

$$
(\alpha)=\mathfrak p^r\mathfrak a^5=(\lambda^r\beta^5)
$$

for a principal $\mathfrak a=(\beta)$, and the same conclusion follows. $\square$

The proposition deliberately begins with ideals. If one merely says that prime elements occur with exponents divisible by five, unique associates have already been chosen and the unit issue has been hidden rather than solved.

### 7.3 A global fifth-power criterion

The ideal extraction proposition and the Kummer unit lemma fit together perfectly.

**Theorem 7.3 (global quintic Kummer criterion).** Let $0\ne\alpha\in\mathcal O$ satisfy:

1. $v_{\mathfrak q}(\alpha)\equiv0\pmod5$ for every nonzero prime ideal $\mathfrak q$ of $\mathcal O$;
2. $\lambda\nmid\alpha$ and $\alpha\equiv r\pmod{\lambda^3}$ for some rational integer $r$.

Then $\alpha$ is a fifth power in $\mathcal O$.

**Proof strategy.** The ideal condition produces $\alpha=u\beta^5$. Both $\alpha$ and $\beta^5$ are rational modulo $\lambda^3$, so their quotient unit is rational modulo $\lambda^3$. Theorem 6.3 absorbs it.

**Proof.** Proposition 7.2 gives $\alpha=u\beta^5$. Since $\lambda\nmid\alpha$, both $u$ and $\beta$ are $\lambda$-adic units. By Proposition 7.1,

$$
\beta^5\equiv s\pmod{\lambda^4}
$$

for some $s\not\equiv0\pmod5$. Its inverse modulo $\lambda^3$ is therefore congruent to the inverse of the rational residue $s$. Hence

$$
u=\alpha/\beta^5
$$

is congruent to a rational integer modulo $\lambda^3$. Theorem 6.3 gives $u=v^5$, and $\alpha=(v\beta)^5$. $\square$

If $v_{\mathfrak p}(\alpha)$ is a nonzero multiple of five, divide by the corresponding fifth power of $\lambda$ and apply the theorem to the resulting $\mathfrak p$-unit. Thus the prime-to-$\lambda$ hypothesis is a normalization, not a genuine loss of generality.

Both hypotheses are necessary. The unit $\eta$ shows that condition 1 alone is insufficient. A rational prime $q\ne5$ shows that condition 2 alone is insufficient because its prime-ideal exponents need not be multiples of five.

There is a fractional version suited to Kummer classes. If $a\in K^\times$, write

$$
(a)=\prod_{\mathfrak q}\mathfrak q^{m_{\mathfrak q}},
\qquad m_{\mathfrak q}\in\mathbf Z.
$$

If every $m_{\mathfrak q}$ is divisible by five, then $(a)=\mathfrak a^5$ for a fractional ideal $\mathfrak a$. Theorem 2.1 makes $\mathfrak a=(b)$ for some $b\in K^\times$, so

$$
a=ub^5
$$

with $u\in\mathcal O^\times$. The same unit normal forms apply. Negative exponents record poles instead of zeros but introduce no new obstruction. After multiplying by a suitable rational fifth power, one may make the quantities integral and apply the $\lambda^2$ or $\lambda^3$ congruence tests exactly as before.

### 7.4 Normal forms modulo fifth powers

Proposition 7.2 and (5.5) give a finite list of unit ambiguities. If every prime-ideal exponent of $\alpha$ is divisible by five, then after absorbing fifth powers of units one may write

$$
\boxed{\alpha=\zeta^a\eta^b\beta^5,\qquad 0\le a,b<5.}
\tag{7.2}
$$

If $\alpha$ is primary, then $\beta^5$ is primary and Theorem 6.2 forces the unit $\zeta^a\eta^b$ to be real. Thus $a=0$, and

$$
\boxed{\alpha=\eta^b\beta^5,\qquad 0\le b<5.}
\tag{7.3}
$$

If $\alpha$ is congruent to an integer modulo $\lambda^3$, Theorem 7.3 forces $b=0$ as well. The successive normal forms are therefore

$$
\zeta^a\eta^b\beta^5
\quad\longrightarrow\quad
\eta^b\beta^5
\quad\longrightarrow\quad
\beta^5,
$$

as the congruence improves from none, to primary, to rational modulo $\lambda^3$. This is the local logic behind the unit calculations in quintic descent.

## 8. Kummer extensions of degree five

### 8.1 Radicals and cyclic extensions

The phrase “Kummer arithmetic” refers to the fact that $K$ already contains all fifth roots of unity. Adjoining one fifth root therefore produces either nothing or a cyclic extension of degree five.

**Theorem 8.1 (quintic Kummer dichotomy).** Let $a\in K^\times$, and let $\theta$ satisfy $\theta^5=a$.

1. The polynomial $T^5-a$ is irreducible over $K$ unless $a\in(K^\times)^5$.
2. If $a$ is not a fifth power, then $K(\theta)/K$ is cyclic of degree five, generated by
   $$
   \tau(\theta)=\zeta\theta.
   $$
3. If $a$ is a fifth power, the extension is trivial.

**Proof strategy.** Because $\zeta\in K$, adjoining one root adjoins all five roots. The resulting splitting field has Galois group embedded in the cyclic group of fifth roots of unity, so its order is one or five.

**Proof.** The roots of $T^5-a$ are $\theta,\zeta\theta,\ldots,\zeta^4\theta$, all of which lie in $K(\theta)$. The polynomial is separable in characteristic zero, so $K(\theta)$ is its splitting field. Every automorphism sends $\theta$ to $\zeta^i\theta$, giving an injection

$$
\operatorname{Gal}(K(\theta)/K)\hookrightarrow\mu_5.
$$

The group therefore has order one or five. In the first case $\theta\in K$ and $a=\theta^5$. In the second case the extension has degree five and the displayed automorphism generates it. This also proves irreducibility in the nontrivial case. $\square$

The assumption $\mu_5\subset K$ is essential. Over a field not containing $\zeta$, a pure quintic extension need not be normal and need not be cyclic.

The norm of the radical in the nontrivial case is

$$
N_{K(\theta)/K}(\theta)
=\prod_{i=0}^4\zeta^i\theta
=\theta^5\zeta^{0+1+2+3+4}=a,
\tag{8.1}
$$

because $\zeta^{10}=1$. This agrees with the constant-term formula for $T^5-a$.

### 8.2 When two radicals define the same field

The multiplicative group modulo fifth powers is naturally an $\mathbf F_5$-vector space: multiplication of classes is written additively if desired, and exponentiation by $j\in\mathbf F_5$ gives scalar multiplication.

**Theorem 8.2 (Kummer lines).** Let $a,b\in K^\times$ represent nonzero classes in $K^\times/(K^\times)^5$. Then

$$
K(\sqrt[5]{a})=K(\sqrt[5]{b})
$$

if and only if

$$
b=a^jc^5
$$

for some $j\in\{1,2,3,4\}$ and $c\in K^\times$. Thus nontrivial cyclic quintic Kummer extensions correspond to one-dimensional subspaces of $K^\times/(K^\times)^5$.

**Proof strategy.** In a cyclic quintic extension, the eigenvectors on which a generator acts through $\zeta^j$ are exactly a base-field scalar times $\theta^j$.

**Proof.** The displayed relation immediately gives equality of fields. Conversely let $L=K(\theta)=K(\phi)$, where $\theta^5=a$ and $\phi^5=b$. Choose the generator $\tau(\theta)=\zeta\theta$. Since $\tau(\phi)^5=b=\phi^5$, there is some $j\in\{1,2,3,4\}$ with $\tau(\phi)=\zeta^j\phi$; $j$ cannot be zero because then $\phi\in K$. In the basis $1,\theta,\ldots,\theta^4$, the $\zeta^j$-eigenspace of $\tau$ is the one-dimensional space $K\theta^j$. Hence $\phi=c\theta^j$ for some $c\in K^\times$, and raising to the fifth power gives $b=c^5a^j$. $\square$

The use of lines rather than individual classes explains a common ambiguity: replacing a radical by its square usually changes its Kummer class but not its field.

### 8.3 Ramification away from five

Let $\mathfrak q\ne\mathfrak p$ be a prime of $\mathcal O$. The behavior of a Kummer extension at $\mathfrak q$ is controlled exactly by the exponent of $\mathfrak q$ in the radicand modulo five.

**Theorem 8.3 (Kummer ramification away from five).** Let $L=K(\sqrt[5]{a})$ be a nontrivial Kummer extension, and let $\mathfrak q\nmid5$.

- If $v_{\mathfrak q}(a)\not\equiv0\pmod5$, then every prime of $L$ above $\mathfrak q$ is totally ramified, with ramification index five.
- If $v_{\mathfrak q}(a)\equiv0\pmod5$, then $\mathfrak q$ is unramified in $L$.

**Proof strategy.** In the first direction, compare the valuation of $\theta^5=a$ after extending the normalized valuation. In the second, change $a$ by a fifth power so that it is a local unit; the derivative of $T^5-a$ is then a unit modulo $\mathfrak q$.

**Proof.** Let $w$ be a normalized valuation above $v_{\mathfrak q}$, with ramification index $e$. From $\theta^5=a$,

$$
5w(\theta)=w(a)=e\,v_{\mathfrak q}(a).
\tag{8.2}
$$

If $5\nmid v_{\mathfrak q}(a)$, equation (8.2) forces $5\mid e$. Since $[L:K]=5$, we have $e=5$. The fundamental equality then forces residue degree one and leaves room for no second prime above $\mathfrak q$, so the prime is totally ramified.

Now suppose $5\mid v_{\mathfrak q}(a)$, say
$v_{\mathfrak q}(a)=5m$. Theorem 2.1 gives
$\mathfrak q=(\pi_{\mathfrak q})$. Replacing $a$ by the Kummer-equivalent
radicand

$$
a/\pi_{\mathfrak q}^{5m}
$$

does not change $K(\sqrt[5]{a})$ and makes its $\mathfrak q$-valuation zero.
Rename this radicand $a$, and put $A=\mathcal O_{\mathfrak q}$. The finite
free $A$-algebra

$$
B=A[T]/(T^5-a)
$$

has derivative $5T^4$. The image of $T$ is a unit, and $5$ is a unit because $\mathfrak q\nmid5$. Thus the polynomial and its derivative are relatively prime after reduction, so $B$ is finite étale over $A$. A finite étale algebra over the normal ring $A$ is normal; because $T^5-a$ is irreducible over $K$, its fraction field is $L$, so $B$ is the integral closure of $A$ in $L$. Localizing $B$ at a maximal ideal produces a finite étale local algebra over the DVR $A$; it is again a DVR, its maximal ideal is generated by the base uniformizer, and its residue extension is separable. Hence its ramification index is one. These localizations are exactly the local rings at the primes of $L$ above $\mathfrak q$, so $\mathfrak q$ is unramified in $L$. $\square$

The theorem is invariant under multiplying $a$ by a fifth power, as it must be. It also shows that a Kummer class with every prime-ideal valuation divisible by five can ramify only at $\mathfrak p$. Such a class need not be trivial: the units $\zeta$ and $\eta$ provide counterexamples. The arithmetic at $\mathfrak p$ is the remaining boundary.

### 8.4 The prime above five and the Kummer boundary

At $\mathfrak p$, the derivative $5T^4$ is never a unit, so the proof of Theorem 8.3 deliberately fails. Ramification at the residue characteristic is governed by deeper unit congruences, not merely by the valuation of the radicand.

For the global descent arguments considered here, the following package is the useful replacement:

1. remove the $\lambda$-valuation modulo five using Proposition 7.2;
2. represent the remaining unit class by $\zeta^a\eta^b$;
3. use primarity modulo $\lambda^2$ to force $a=0$;
4. use rational congruence modulo $\lambda^3$ to force $b=0$.

In particular, after the first normalization has made $a$ a $\mathfrak p$-unit, if all prime-ideal valuations of $a$ are divisible by five and $a$ is rational modulo $\lambda^3$, then Theorem 7.3 says the Kummer extension is trivial. This is stronger than merely saying it is unramified away from $\mathfrak p$.

The thresholds cannot be lowered. The class of $\eta$ has zero valuation everywhere and is rational modulo $\lambda^2$, yet it defines a nontrivial Kummer extension. Thus “primary” and “a fifth power” are genuinely different notions.

Three examples distinguish the available Kummer classes.

1. For a prime ideal $\mathfrak q\nmid(5)$, choose a generator
   $\pi_{\mathfrak q}$ with
   $\mathfrak q=(\pi_{\mathfrak q})$; such a generator exists by Theorem 2.1.
   The extension
   $K(\sqrt[5]{\pi_{\mathfrak q}})/K$ is totally ramified at $\mathfrak q$ by Theorem 8.3. Its radicand has an obvious valuation obstruction to being a fifth power.
2. The extension $K(\sqrt[5]{\eta})/K$ is unramified away from $\mathfrak p$ because $\eta$ is a global unit. It is nontrivial because $\eta$ is not a fifth power. Its obstruction is the real unit exponent $b=1$ in (5.5).
3. The extension $K(\sqrt[5]{\zeta})/K=K(\zeta_{25})$ is also unramified away from $\mathfrak p$. Its obstruction is the torsion exponent $a=1$. The identity with $K(\zeta_{25})$ follows because a fifth root of $\zeta_5$ is a primitive twenty-fifth root of unity.

These examples show why valuation data, real primarity, and the full $\lambda^3$ congruence are three different levels of information. The first example is detected by an ordinary prime exponent. The second passes every valuation test and every $\lambda^2$ test. The third is already excluded at the linear $\lambda$-digit.

Kummer classes also interact cleanly with conjugation. If $a$ is real, conjugation extends to $K(\sqrt[5]{a})$ by fixing a chosen real fifth root, and it conjugates the generator $\tau$ to $\tau^{-1}$. The conjugate-quotient calculation in Section 11.2 is the element-level version of this symmetry for the classes arising from cyclotomic factors.

## 9. Coprimality of cyclotomic factors

### 9.1 Common prime divisors

Let $x,y\in\mathbf Z$ with $\gcd(x,y)=1$, and set

$$
F_i=x+\zeta^iy,\qquad i\in\mathbf Z/5\mathbf Z.
\tag{9.1}
$$

The product of the five $F_i$ is $x^5+y^5$. To extract fifth powers, we need to know how the principal ideals $(F_i)$ intersect.

**Theorem 9.1 (pairwise coprimality away from $\mathfrak p$).** If $i\ne j$, every common prime-ideal divisor of $F_i$ and $F_j$ is $\mathfrak p$. Equivalently,

$$
(F_i)+(F_j)=\mathfrak p^m
$$

for some $m\ge0$, where $\mathfrak p^0=\mathcal O$.

**Proof strategy.** Two linear combinations eliminate $x$ and $y$ in turn. The remaining coefficients are differences of fifth roots of unity, hence associates of $\lambda$.

**Proof.** Let $\mathfrak q$ divide both $F_i$ and $F_j$. Their difference gives

$$
\mathfrak q\mid y(\zeta^i-\zeta^j).
\tag{9.2}
$$

Multiplying $F_i$ by $\zeta^{j-i}$ before subtracting $F_j$ gives

$$
\mathfrak q\mid x(\zeta^{j-i}-1).
\tag{9.3}
$$

If $\mathfrak q\ne\mathfrak p$, Proposition 4.1 says the cyclotomic differences in (9.2) and (9.3) are $\mathfrak q$-units. Hence $\mathfrak q$ divides both rational integers $x$ and $y$. An integer combination of $x$ and $y$ equals one, contradicting that $\mathfrak q$ is proper. Therefore $\mathfrak q=\mathfrak p$. $\square$

The primitivity hypothesis is indispensable. If an ordinary prime $q$ divides both $x$ and $y$, then every prime of $\mathcal O$ above $q$ divides all five factors.

Reduction modulo $\mathfrak p$ gives the exact condition for the exceptional common divisor:

$$
F_i\equiv x+y\pmod{\mathfrak p}
\qquad\text{for every }i.
\tag{9.4}
$$

Thus $\mathfrak p$ divides one $F_i$ if and only if it divides them all, if and only if

$$
5\mid x+y.
\tag{9.5}
$$

### 9.2 The two valuation patterns

The factors exhibit exactly two local patterns.

**Theorem 9.2 (valuation of the linear factors).** Assume $\gcd(x,y)=1$.

1. If $5\nmid x+y$, then
   $$
   v_{\mathfrak p}(F_i)=0
   \qquad(0\le i<5).
   $$
2. If $5\mid x+y$, then $5\nmid xy$ and
   $$
   v_{\mathfrak p}(F_0)=4v_5(x+y),
   \qquad
   v_{\mathfrak p}(F_i)=1\quad(1\le i<5).
   \tag{9.6}
   $$

**Proof strategy.** The first statement is (9.4). In the second, split $F_i$ into the rational term $x+y$ and a cyclotomic difference. Their $\mathfrak p$-values are at least four and exactly one, so they cannot cancel.

**Proof.** If $5\mid x+y$, primitivity shows $5\nmid y$ and $5\nmid x$. For $i\ne0$,

$$
F_i=(x+y)+y(\zeta^i-1).
$$

By (3.8), the first term has $\mathfrak p$-value at least four. By (3.9), the second has value one. Unequal values do not cancel, so $v_{\mathfrak p}(F_i)=1$. The formula for $F_0=x+y$ is (3.8). $\square$

Here and in (9.6), the valuation of zero is understood to be $\infty$. Thus the formula also covers the primitive degenerate pair $x=-y=\pm1$; later divisions by $x+y$ will explicitly exclude that case.

The gap between values one and four is the source of the exceptional descent. Each nonrational factor contains one copy of $\lambda$, while the rational factor contains copies in blocks of four.

### 9.3 The rational quotient

Write

$$
Q(x,y)=x^4-x^3y+x^2y^2-xy^3+y^4.
\tag{9.7}
$$

Then $(x+y)Q(x,y)=x^5+y^5$ and $Q(x,y)=N(x+\zeta y)$. The rational factors are almost coprime.

**Proposition 9.3 (rational gcd and exact five-adic value).** If $\gcd(x,y)=1$, then

$$
\gcd(x+y,Q(x,y))\mid5.
\tag{9.8}
$$

More precisely:

- if $5\nmid x+y$, the gcd is $1$;
- if $5\mid x+y$, then $v_5(Q(x,y))=1$ and the gcd is $5$.

**Proof strategy.** Modulo a prime divisor of $x+y$, substitute $x=-y$. For the exact value at five, write $x=-y+h$ and expand before dividing by $h=x+y$.

**Proof.** If a rational prime $q$ divides $x+y$, then

$$
Q(x,y)\equiv5y^4\pmod q.
$$

Primitivity gives $q\nmid y$, so a common divisor $q$ must equal $5$. This proves (9.8).

Now assume $h=x+y$ is divisible by $5$. Expanding $x=-y+h$ gives

$$
Q(x,y)
=5y^4-10y^3h+10y^2h^2-5yh^3+h^4.
\tag{9.9}
$$

Every term after the first is divisible by $25$, whereas $5y^4$ is not because $5\nmid y$. Hence $Q(x,y)\equiv5y^4\pmod{25}$ and $v_5(Q)=1$. $\square$

Equation (9.9) is the exponent-five instance of the lifting-the-exponent phenomenon, but its direct proof records exactly the congruence needed here. It also agrees with (4.6) and (9.6):

$$
v_5(Q(x,y))=v_{\mathfrak p}(x+\zeta y)=1.
$$

### 9.4 Normalized coprime factors

In the ramified pattern, define

$$
A_i=\frac{x+\zeta^iy}{\lambda_i},
\qquad
\lambda_i=1-\zeta^i,\qquad 1\le i<5.
\tag{9.10}
$$

Each $\lambda_i$ is a uniformizer associate, so Theorem 9.2 gives $v_{\mathfrak p}(A_i)=0$. The ideals $(A_i)$ are pairwise coprime. Indeed a common prime away from $\mathfrak p$ would already divide two $F_i$, and $\mathfrak p$ divides none of the $A_i$.

If one uses the same denominator $\lambda$ for every factor, the quotients are still integral because all $\lambda_i$ are associates. The Galois-symmetric choice in (9.10) is better for conjugation; the common choice $\lambda$ is better for the explicit congruence in Section 10.4.

The exact pairwise gcd is now visible. If $5\nmid x+y$, then $m=0$. If $5\mid x+y$, Theorem 9.2 says that at least one of the two factors has $\mathfrak p$-value one, so $m=1$. Therefore

$$
(F_i)+(F_j)=
\begin{cases}
\mathcal O,&5\nmid x+y,\\
\mathfrak p,&5\mid x+y,
\end{cases}
\qquad i\ne j.
\tag{9.11}
$$

This is stronger than saying that a common divisor is supported above five: it identifies exactly one common copy of the exceptional prime.

For the rational factor, if $x+y\ne0$ and $t=v_5(x+y)$, the normalized integer

$$
B_0=\frac{x+y}{5^t}
$$

is prime to $5$. Thus all five factors can be stripped of their exact $\mathfrak p$-parts. What remains is pairwise coprime, both ideally and elementwise up to units.

Two examples clarify what the theorem does and does not say. With $x=y=1$, the pair is primitive and $5\nmid x+y$. The five factors $1+\zeta^i$ are pairwise coprime; indeed the four nonrational ones are units because their norms are one. With $x=1,y=4$, one has $5\mid x+y$. Every nonrational factor $1+4\zeta^i$ has exact $\mathfrak p$-value one, even though the rational factor has value four. Dividing each nonrational factor by its uniformizer leaves $\mathfrak p$-units that are pairwise coprime.

By contrast, $x=y=5$ violates primitivity. Every factor is divisible by every prime above $5$, and primes dividing the common rational content also occur throughout the factorization. Cancelling the rational gcd before entering $\mathcal O$ is therefore a mathematical step, not merely a cosmetic convention.

There is another possible misunderstanding. Pairwise coprimality of the principal ideals $(F_i)$ does not say that their rational norms are pairwise coprime. Distinct prime ideals over the same rational prime may divide different $F_i$, causing their norms to share that rational prime. The ideal statement is the one that permits fifth-power extraction.

## 10. Fifth-power extraction for quintic equations

### 10.1 The abstract extraction principle

We first isolate the logical step used in both cases.

**Theorem 10.1 (one-exceptional-prime extraction).** Let $\alpha_0,\ldots,\alpha_4\in\mathcal O\setminus\{0\}$ satisfy

$$
\alpha_0\alpha_1\alpha_2\alpha_3\alpha_4=\gamma^5.
$$

Assume that no prime ideal other than $\mathfrak p$ divides two different $\alpha_i$. Then, for each $i$, every prime-ideal exponent of $(\alpha_i)$ away from $\mathfrak p$ is divisible by five. If

$$
v_{\mathfrak p}(\alpha_i)\equiv r_i\pmod5,
\qquad 0\le r_i<5,
$$

then

$$
\boxed{\alpha_i=u_i\lambda^{r_i}\beta_i^5}
\tag{10.1}
$$

for a unit $u_i$ and an algebraic integer $\beta_i$.

**Proof.** Fix a prime $\mathfrak q\ne\mathfrak p$. It occurs in at most one $(\alpha_i)$, so its exponent there equals its exponent in the product $(\gamma)^5$ and is divisible by five. Proposition 7.2 now gives (10.1). $\square$

The theorem is intentionally asymmetric at $\mathfrak p$. It does not require the factors to be coprime there; it only records each known valuation modulo five. This is exactly what the cyclotomic factorization supplies.

### 10.2 The case away from five

The extraction arguments concern nonzero solutions. The degenerate cases require no ideal theory: if $x=0$ or $y=0$, the equation reduces to equality of two integer fifth powers, while if $z=0$, then $x=-y$; under $\gcd(x,y)=1$ this last pair is $(1,-1)$ or $(-1,1)$. We therefore assume throughout the rest of this chapter that $xyz\ne0$.

Suppose

$$
x^5+y^5=z^5,\qquad \gcd(x,y)=1,
\tag{10.2}
$$

and $5\nmid x+y$. By Theorems 9.1 and 9.2, the five factors $F_i$ are pairwise coprime and have $\mathfrak p$-value zero. Theorem 10.1 gives, in particular,

$$
\boxed{x+\zeta y=u\alpha^5}
\tag{10.3}
$$

for $u\in\mathcal O^\times$ and $\alpha\in\mathcal O$.

The unit can be placed in a finite normal form. Let $k$ be the unique residue class (6.2) for which $\zeta^k(x+\zeta y)$ is primary. Since $\alpha^5$ is primary, the unit $\zeta^ku$ is primary. Theorem 6.2 makes it real. Absorbing its sign and every fifth power of $\eta$ into $\alpha^5$ gives:

**Corollary 10.2 (first-case normal form).** Under (10.2) and $5\nmid x+y$, there exist $b\in\{0,1,2,3,4\}$ and $\beta\in\mathcal O$ such that

$$
\boxed{
\zeta^k(x+\zeta y)=\eta^b\beta^5,
\qquad
k\equiv-\frac{y}{x+y}\pmod5.
}
\tag{10.4}
$$

This is the correct conclusion away from five. There is no general reason for $b$ to vanish. The real unit $\eta$ is the concrete obstruction to replacing (10.4) immediately by a fifth power.

### 10.3 The case above five

Now assume (10.2) and $5\mid x+y$. Theorem 9.2 gives

$$
v_{\mathfrak p}(x+\zeta y)=1.
$$

Theorem 10.1 therefore yields

$$
\boxed{x+\zeta y=u\lambda\alpha^5.}
\tag{10.5}
$$

The product valuation also imposes a rational congruence. Put $t=v_5(x+y)$ and $s=v_5(z)$. From Theorem 9.2,

$$
\begin{aligned}
v_{\mathfrak p}(x^5+y^5)
&=v_{\mathfrak p}(F_0)+\sum_{i=1}^4v_{\mathfrak p}(F_i)\\
&=4t+4.
\end{aligned}
$$

On the other hand $v_{\mathfrak p}(z^5)=20s$. Hence

$$
t+1=5s,
\qquad
\boxed{t\equiv4\pmod5.}
\tag{10.6}
$$

In particular $x+y$ is divisible by $5^4$, not merely by $5$. This conclusion also follows from Proposition 9.3, but the cyclotomic valuation calculation explains why the residue class is four.

### 10.4 Eliminating the unit in the ramified case

Equation (10.5) still contains a unit. The exceptional valuation now produces exactly the congruence needed to remove it.

**Theorem 10.3 (ramified factor is $\lambda$ times a fifth power).** Under (10.2), $\gcd(x,y)=1$, and $5\mid x+y$, there exists $\beta\in\mathcal O$ such that

$$
\boxed{x+\zeta y=\lambda\beta^5.}
\tag{10.7}
$$

**Proof strategy.** Divide (10.5) by $\lambda$. The quotient is congruent to the rational integer $-y$ modulo $\lambda^3$, because the term $(x+y)/\lambda$ contains $\lambda^3$. The fifth-power part is also rational modulo $\lambda^3$, forcing the unit to be a fifth power by Theorem 6.3.

**Proof.** Write $x+y=5m$. The exact identity (3.5) gives

$$
\frac{x+\zeta y}{\lambda}
=\frac{x+y-y\lambda}{\lambda}
=\zeta^3\eta^2m\lambda^3-y
\equiv-y\pmod{\lambda^3}.
\tag{10.8}
$$

Since $5\nmid y$, this quotient is a $\mathfrak p$-unit. From (10.5),

$$
\frac{x+\zeta y}{\lambda}=u\alpha^5.
$$

Proposition 7.1 makes $\alpha^5$ congruent to a nonzero rational integer modulo $\lambda^4$. Dividing the congruence (10.8) by that rational residue shows that $u$ is congruent to a rational integer modulo $\lambda^3$. By Theorem 6.3, $u=v^5$ for some unit $v$. Taking $\beta=v\alpha$ proves (10.7). $\square$

This is the decisive gain in the case above five. Away from five, a real unit class survives. At five, the forced factor $\lambda$ moves the remaining quotient three digits deep, and those three digits kill the entire unit class.

The exponent three in (10.8) is not accidental:

$$
\frac{5}{\lambda}=\zeta^3\eta^2\lambda^3.
$$

Total ramification of degree four converts one rational factor of $5$ into four factors of $\lambda$; dividing the cyclotomic factor by its single $\lambda$ leaves exactly $\lambda^3$.

### 10.5 The rational shadows

Taking absolute norms of (10.3) and (10.7) removes all units because of (4.1).

**Corollary 10.4 (norm extraction).** Under the nonzero primitive equation (10.2):

1. if $5\nmid x+y$, then
   $$
   \boxed{Q(x,y)=w^5}
   \tag{10.9}
   $$
   for the positive integer $w=|N(\alpha)|$;
2. if $5\mid x+y$, then
   $$
   \boxed{Q(x,y)=5w^5}
   \tag{10.10}
   $$
   for the positive integer $w=|N(\beta)|$.

**Proof.** In the first case, (10.3) and $N(u)=1$ give

$$
Q(x,y)=N(x+\zeta y)=N(\alpha)^5.
$$

The norm is an integer and $Q>0$. In the second case, (10.7) and $N(\lambda)=5$ give

$$
Q(x,y)=5N(\beta)^5.
$$

Again positivity permits the stated choice of $w$. $\square$

The rational factor $x+y$ is then forced as well.

**Corollary 10.5 (rational fifth-power shapes).** Under the same nonzero primitive equation (10.2):

1. if $5\nmid x+y$, there is an integer $a$ such that
   $$
   \boxed{x+y=a^5,\qquad Q(x,y)=w^5,\qquad z=aw;}
   \tag{10.11}
   $$
2. if $5\mid x+y$, there is an integer $a$ such that
   $$
   \boxed{x+y=5^4a^5,\qquad Q(x,y)=5w^5,\qquad z=5aw.}
   \tag{10.12}
   $$

**Proof.** In the first case, $z^5=(x+y)w^5$, so $(z/w)^5=x+y$ is an integer. A rational number whose fifth power is an integer is itself an integer: compare prime valuations in numerator and denominator. Put $a=z/w$.

In the second case,

$$
z^5=5(x+y)w^5,
$$

so $r=z/w$ is an integer with $r^5=5(x+y)$. Its $5$-adic valuation is positive, hence $r=5a$. Substitution gives $5^5a^5=5(x+y)$, proving (10.12). $\square$

These are consequences, not the descent itself. They transform a quintic equation into much more rigid simultaneous conditions and supply the smaller quantities from which a later well-founded descent can be built.

The same reasoning gives a useful version with a fifth-power multiplier. Suppose

$$
x^5+y^5=d\,z^5,
\qquad \gcd(x,y)=1,
\tag{10.13}
$$

where the prime ideals dividing $d$ are known. At any prime ideal outside $\mathfrak p$ and the support of $(d)$, Theorem 9.1 still forces the exponent in each individual cyclotomic factor to be divisible by five. Thus every new non-fifth-power ideal exponent is confined to the explicitly declared support of $d$ and to $\mathfrak p$. This supported form is often the right input for Fermat-type equations with coefficients.

One must not conclude that (10.7) follows from the norm equation (10.10). The norm sees only the sum of prime-ideal exponents weighted by residue degrees. The proof of (10.7) first isolates the ideal of one linear factor and only then applies the unit congruence. This order is what preserves enough information to build a descent.

## 11. A reusable descent package

### 11.1 Signs, differences, and changes of root

Everything above has a difference-form analogue. Replacing $y$ by $-y$ gives

$$
x^5-y^5=\prod_{i=0}^4(x-\zeta^iy).
$$

The exceptional condition becomes $5\mid x-y$. If $\gcd(x,y)=1$ and $5\mid x-y$, then

$$
v_{\mathfrak p}(x-\zeta^iy)=1
\qquad(i\ne0),
$$

because

$$
x-\zeta^iy=(x-y)+y(1-\zeta^i)
$$

has summands of values at least four and one. The normalized quotient satisfies

$$
\frac{x-\zeta y}{\lambda}
=\frac{x-y}{\lambda}+y
\equiv y\pmod{\lambda^3}.
$$

Thus the same Kummer unit lemma removes the unit.

Changing $\zeta$ to $\zeta^i$ with $i\ne0$ changes $\lambda$ to the associate $\lambda_i=1-\zeta^i$. All ideal and valuation conclusions are invariant. Exact element equations acquire the corresponding explicit unit. For example, from (10.7), applying $\sigma_i$ gives

$$
x+\zeta^iy=(1-\zeta^i)\,\sigma_i(\beta)^5.
\tag{11.1}
$$

It is usually better to retain $1-\zeta^i$ than to replace it by $\lambda$ and introduce an unnecessary unit.

Signs of fifth powers cause no difficulty because $-1=(-1)^5$. This is special to odd exponent. It permits signs to be absorbed into radicals throughout the normal-form arguments.

### 11.2 The first-case conjugate quotient

The real unit in (10.4) survives absolute norm, but it disappears when an equation is divided by its complex conjugate. Conjugating (10.4) gives

$$
\zeta^{-k}(x+\zeta^{-1}y)=\eta^b\bar\beta^5.
$$

Division yields:

**Proposition 11.1 (conjugate-quotient fifth power).** Under the hypotheses of Corollary 10.2,

$$
\boxed{
\zeta^{2k}\frac{x+\zeta y}{x+\zeta^{-1}y}
=\left(\frac{\beta}{\bar\beta}\right)^5.
}
\tag{11.2}
$$

The fraction is a field element rather than generally an algebraic integer, which is harmless: Kummer theory naturally lives in $K^\times/(K^\times)^5$. The root-of-unity correction $\zeta^{2k}$ is essential. Omitting it amounts to forgetting the unique primary normalization.

There is also an ideal interpretation. The numerator and denominator are conjugate principal ideals, and away from $\mathfrak p$ each is a fifth power. Primary normalization aligns their unit classes so that the real unit cancels. Equation (11.2) is the element-level record of that alignment.

In the ramified case, (10.7) and its conjugate give

$$
\frac{x+\zeta y}{x+\zeta^{-1}y}
=\frac{\lambda}{\bar\lambda}
\left(\frac{\beta}{\bar\beta}\right)^5
=-\zeta\left(\frac{\beta}{\bar\beta}\right)^5,
\tag{11.3}
$$

because $\bar\lambda=-\zeta^{-1}\lambda$. Again the exact root-of-unity factor matters.

### 11.3 A decision table for applications

For coprime integers $x,y$, the following table collects the conclusions in the order in which they should be used.

| Input                                                | Local conclusion at $\mathfrak p$           | Coprimality                                                                           | Fifth-power conclusion                                                                                                    |
| ---------------------------------------------------- | ------------------------------------------- | ------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------- |
| $5\nmid x+y$                                         | $v_{\mathfrak p}(x+\zeta^iy)=0$ for all $i$ | all five factors pairwise coprime                                                     | if their product is a fifth power, $x+\zeta y=u\alpha^5$; after primary normalization, $\zeta^k(x+\zeta y)=\eta^b\beta^5$ |
| $5\mid x+y$                                          | $v_{\mathfrak p}(x+\zeta^iy)=1$ for $i\ne0$ | common divisors occur only at $\mathfrak p$; division by one uniformizer removes them | if their product is a fifth power, $x+\zeta y=\lambda\beta^5$                                                             |
| all ideal exponents of $\alpha$ are multiples of $5$ | no exceptional exponent                     | not applicable                                                                        | $\alpha=u\beta^5$                                                                                                         |
| previous row and $\alpha$ is primary                 | $\alpha\equiv r\pmod{\lambda^2}$            | not applicable                                                                        | $\alpha=\eta^b\beta^5$                                                                                                    |
| previous row and $\alpha\equiv r\pmod{\lambda^3}$    | deepest required congruence                 | not applicable                                                                        | $\alpha=\beta^5$                                                                                                          |

The table is not a substitute for the hypotheses. In the first two rows, primitivity of $x,y$ is what excludes common primes away from $\mathfrak p$. In the last three rows, divisibility of every ideal exponent is what permits the unit analysis to begin. Dropping either condition produces immediate counterexamples.

A safe application follows this sequence:

1. primitive reduction in $\mathbf Z$;
2. factorization in $\mathcal O$;
3. ideal gcd analysis;
4. exact $\mathfrak p$-valuations;
5. ideal fifth-power extraction;
6. class-number-one passage to elements;
7. primary or $\lambda^3$ congruence to control the unit;
8. norm or conjugate quotient, depending on which information is needed next.

Changing this order often creates a circular argument. In particular, one cannot use an element fifth-power equation before the unit has been justified, and one cannot infer pairwise coprimality merely from coprimality of the rational norms.

### 11.4 What has been achieved

The arithmetic of $K=\mathbf Q(\zeta_5)$ is now explicit at every point needed
for quintic Diophantine descent. Theorem 2.1 proves

$$
\mathcal O_K=\mathbf Z[\zeta],\qquad
\operatorname{disc}(K)=+125,\qquad
\operatorname{Cl}(\mathcal O_K)=1,
$$

so every later passage from an ideal fifth power to an element fifth power is
justified. The ring $\mathcal O=\mathbf Z[\zeta]$ has one prime

$$
\mathfrak p=(1-\zeta)
$$

above five, and

$$
(5)=\mathfrak p^4,\qquad
v_{\mathfrak p}(n)=4v_5(n),\qquad
\mathcal O/\mathfrak p=\mathbf F_5.
$$

All conjugates of $1-\zeta$ are associates. Complex conjugation is controlled both exactly, by $\bar\lambda=-\zeta^{-1}\lambda$, and infinitesimally, by its trivial action modulo $\lambda$. The absolute norm of $x+\zeta y$ is the positive rational quotient

$$
\frac{x^5+y^5}{x+y}.
$$

The unit group has no hidden part:

$$
\mathcal O^\times=\{\pm\zeta^a\eta^n\},
\qquad
\eta=\frac{1+\sqrt5}{2},
$$

and every unit is cyclotomic. Modulo fifth powers, $\zeta$ and $\eta$ give the two independent directions. Congruence modulo $\lambda^2$ kills the first; congruence modulo $\lambda^3$ kills both. This yields the quintic Kummer criterion: ideal exponents divisible by five plus the correct deep rational congruence force an actual fifth power.

Finally, the linear factors $x+\zeta^iy$ of a primitive quintic sum are pairwise coprime away from $\mathfrak p$. If $5\nmid x+y$, each is a unit times a fifth power and admits a finite primary normal form. If $5\mid x+y$, each nonrational factor has exact $\mathfrak p$-value one, and the forced congruence after division by $\lambda$ removes the unit completely:

$$
x+\zeta y=\lambda\beta^5.
$$

That equality is the central handoff to descent. The field factorization has been converted into a rigid radical equation, its exceptional prime has been measured exactly, and every ambiguity from associates and units has been accounted for rather than suppressed.
