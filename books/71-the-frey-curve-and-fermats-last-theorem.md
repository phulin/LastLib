# The Frey Curve and Fermat's Last Theorem

## Contents

1. [The theorem and the assembly problem](#1-the-theorem-and-the-assembly-problem)
   - [Fermat's Last Theorem](#11-fermats-last-theorem)
   - [What the Frey method must accomplish](#12-what-the-frey-method-must-accomplish)
   - [Normalization conventions](#13-normalization-conventions)
2. [Reduction of the exponent](#2-reduction-of-the-exponent)
   - [Odd prime divisors of the exponent](#21-odd-prime-divisors-of-the-exponent)
   - [The exponent three](#22-the-exponent-three)
   - [The exponent four](#23-the-exponent-four)
   - [The complete exponent reduction](#24-the-complete-exponent-reduction)
3. [Primitive prime-exponent solutions](#3-primitive-prime-exponent-solutions)
   - [Primitivity and pairwise coprimality](#31-primitivity-and-pairwise-coprimality)
   - [Signs and the unique even term](#32-signs-and-the-unique-even-term)
   - [The two-adic normalization](#33-the-two-adic-normalization)
4. [The Frey curve and its invariants](#4-the-frey-curve-and-its-invariants)
   - [Why this cubic is chosen](#41-why-this-cubic-is-chosen)
   - [The integral invariants](#42-the-integral-invariants)
   - [A worked numerical audit](#43-a-worked-numerical-audit)
5. [Odd-prime minimal models](#5-odd-prime-minimal-models)
   - [Good primes](#51-good-primes)
   - [Primes dividing one root difference](#52-primes-dividing-one-root-difference)
   - [The odd local discriminant ledger](#53-the-odd-local-discriminant-ledger)
6. [The prime two](#6-the-prime-two)
   - [Why the displayed equation is not minimal](#61-why-the-displayed-equation-is-not-minimal)
   - [The integral change of variables](#62-the-integral-change-of-variables)
   - [Minimality, multiplicative reduction, and splitting](#63-minimality-multiplicative-reduction-and-splitting)
7. [Semistability, discriminant, and conductor](#7-semistability-discriminant-and-conductor)
   - [The complete minimal-discriminant formula](#71-the-complete-minimal-discriminant-formula)
   - [The exact conductor](#72-the-exact-conductor)
   - [What is and is not removed modulo $p$](#73-what-is-and-is-not-removed-modulo-p)
8. [The residual representation at the Fermat prime](#8-the-residual-representation-at-the-fermat-prime)
   - [Determinant, parity, and ramification](#81-determinant-parity-and-ramification)
   - [Finite flatness at $p$](#82-finite-flatness-at-p)
   - [The exact residual level](#83-the-exact-residual-level)
9. [Irreducibility from rational isogenies](#9-irreducibility-from-rational-isogenies)
   - [The stable-line dictionary](#91-the-stable-line-dictionary)
   - [The semistable full-two theorem](#92-the-semistable-full-two-theorem)
   - [The exponents five and seven](#93-the-exponents-five-and-seven)
   - [Absolute irreducibility](#94-absolute-irreducibility)
10. [The Frey compatible system](#10-the-frey-compatible-system)
    - [Common Frobenius polynomials](#101-common-frobenius-polynomials)
    - [Hodge theory, purity, and local compatibility](#102-hodge-theory-purity-and-local-compatibility)
    - [The immovable monodromy at two](#103-the-immovable-monodromy-at-two)
11. [The minimal hardly ramified deformation problem](#11-the-minimal-hardly-ramified-deformation-problem)
    - [The exact functor](#111-the-exact-functor)
    - [The Frey residual point](#112-the-frey-residual-point)
    - [Formal smoothness at two](#113-formal-smoothness-at-two)
    - [Formal smoothness at the coefficient prime](#114-formal-smoothness-at-the-coefficient-prime)
    - [The balanced global presentation](#115-the-balanced-global-presentation)
12. [Potential modularity as a finiteness theorem](#12-potential-modularity-as-a-finiteness-theorem)
    - [The scalar-reduced universal representation](#121-the-scalar-reduced-universal-representation)
    - [The potential-modularity field](#122-the-potential-modularity-field)
    - [The integral Hecke factorization](#123-the-integral-hecke-factorization)
    - [Scalar, vexing, simultaneous, and coefficient-prime places](#124-scalar-vexing-simultaneous-and-coefficient-prime-places)
    - [The first irreducible arithmetic lemma](#125-the-first-irreducible-arithmetic-lemma)
    - [Extracting the characteristic-zero lift](#126-extracting-the-characteristic-zero-lift)
13. [Spreading the lift and changing the prime](#13-spreading-the-lift-and-changing-the-prime)
    - [An admissible top field](#131-an-admissible-top-field)
    - [Brauer induction without automorphic descent to $\mathbf Q$](#132-brauer-induction-without-automorphic-descent-to-mathbf-q)
    - [Descent cocycles and effectivity](#133-descent-cocycles-and-effectivity)
    - [The local record in the effective system](#134-the-local-record-in-the-effective-system)
    - [The single missing arithmetic theorem](#135-the-single-missing-arithmetic-theorem)
14. [Finite-flat lattices from good reduction](#14-finite-flat-lattices-from-good-reduction)
    - [The intersection-and-closure lemma](#141-the-intersection-and-closure-lemma)
    - [Why the arbitrary-lattice statement matters](#142-why-the-arbitrary-lattice-statement-matters)
    - [Application to the prime-switched member](#143-application-to-the-prime-switched-member)
15. [The fixed-$3$ member and the contradiction](#15-the-fixed-3-member-and-the-contradiction)
    - [The integral filtration at two](#151-the-integral-filtration-at-two)
    - [The complete Book 66 ledger](#152-the-complete-book-66-ledger)
    - [Purity at five](#153-purity-at-five)
16. [Final assembly and dependency status](#16-final-assembly-and-dependency-status)
    - [Prime exponents](#161-prime-exponents)
    - [Return to every exponent](#162-return-to-every-exponent)
    - [Dependency audit](#163-dependency-audit)
    - [Proof construction ledger and scale](#164-proof-construction-ledger-and-scale)

## 1. The theorem and the assembly problem

### 1.1 Fermat's Last Theorem

Fermat's Last Theorem is the following assertion.

**Theorem 1.1 (Fermat).** If $n>2$ is an integer, then there are no nonzero
integers $x,y,z$ satisfying

$$
x^n+y^n=z^n.
$$

The qualification that the integers be nonzero removes the obvious degenerate
identities. There is no coprimality hypothesis in the theorem. Coprimality is a
normalization forced on a hypothetical solution, not part of the original
statement.

The final proof is not obtained by studying the three powers directly. The
equation is converted into an elliptic curve whose reduction remembers the
factorization of the three terms. One then studies the two-dimensional Galois
representations attached to that curve. The decisive feature is a tension between
two sorts of information:

- the Diophantine equation makes the residual representation exceptionally
  lightly ramified;
- a compatible characteristic-zero realization remains pure of weight one.

The representation-theoretic middle of the argument must preserve both facts.
That is where almost every hidden hypothesis in the modular method occurs.

### 1.2 What the Frey method must accomplish

For a prime exponent $p\geq5$, a hypothetical primitive solution will give a curve
$E$ with full rational $2$-torsion. We shall prove directly that

$$
\det E[p]=\overline\chi_p,
\qquad
N(E[p])=2,
$$

where $N(E[p])$ denotes the prime-to-$p$ Artin conductor, and that $E[p]$ is
finite flat at $p$ and irreducible. The number $2$ in this display is not a
typographical simplification: the local representation at $2$ is nontrivial and
cannot be discarded.

The intended global chain has the form

```text
hypothetical Fermat solution
          |
          v
Frey curve and its mod-p representation
          |
          v
minimal hardly ramified deformation ring
          |
          v
potential modularity and modularity lifting
make the scalar reduction finite
          |
          v
minimal p-adic lift over Q
          |
          v
effective compatible system by Brauer descent
and a controlled 3-adic member
          |
          v
classification of hardly ramified 3-adic representations
          |
          v
contradiction with purity
```

Each arrow has more hypotheses than its label suggests.  In particular, residual
irreducibility is not residual automorphy; potential automorphy over an extension
does not automatically produce an effective system over $\mathbf Q$; and changing
a coefficient prime does not erase a nonzero characteristic-zero monodromy
operator or construct an integral lattice.  Chapters 11--16 keep these interfaces
explicit and isolate the one global theorem not proved by the available
prerequisites.

### 1.3 Normalization conventions

Arithmetic Frobenius is used throughout. Thus, at a good prime $q\ne\ell$, the
$\ell$-adic representation of an elliptic curve has polynomial

$$
P_q(X)=X^2-a_qX+q,
\qquad
a_q=q+1-\#E(\mathbf F_q),
$$

and the cyclotomic character satisfies

$$
\chi_\ell(\operatorname{Frob}_q)=q.
$$

Hodge--Tate weights are normalized so that $\chi_\ell$ has weight $1$.
Consequently an elliptic-curve Tate module has weights $\{0,1\}$ and purity
weight $1$. For a local field, valuations are normalized by $v_q(q)=1$.

The Frey curve will always be written

$$
y^2=x(x-A)(x+B),
\qquad C=A+B.
$$

This convention fixes every sign in $c_6$ and prevents later ambiguity about
which root difference equals $C$.

## 2. Reduction of the exponent

The modular argument is designed for prime exponent at least five. Before using
it, one must show that these cases, together with one elementary exponent, cover
every $n>2$. The even case is the common source of an unnoticed gap.

### 2.1 Odd prime divisors of the exponent

Suppose $n>2$ has an odd prime divisor $p$, and write $n=pm$. From a nonzero
solution

$$
x^n+y^n=z^n
$$

we obtain

$$
(x^m)^p+(y^m)^p=(z^m)^p.
$$

If $n$ is even, taking absolute values before this substitution produces a
positive solution of exponent $p$. If $n$ is odd, the displayed signed solution
is already sufficient; Section 3.2 will normalize its signs. Thus the exclusion
of every odd prime exponent excludes every exponent having an odd prime divisor.

The prime $3$ does not enter the Frey argument developed below. It needs its
own descent, which we give next rather than hide inside the phrase ``the
classical small-exponent case.''

### 2.2 The exponent three

The factorization of a sum of two cubes becomes a prime factorization after
adjoining a primitive cube root of unity. The only subtlety is that the three
factors can meet at the prime above $3$; keeping its exact valuation is what
drives the descent.

Let $\omega^2+\omega+1=0$ and put

$$
R=\mathbf Z[\omega],
\qquad
N(u+v\omega)=u^2-uv+v^2.
$$

The triangular lattice $R\subset\mathbf C$ is Euclidean for $N$: every point
of the plane lies in a hexagonal cell around some lattice point whose squared
distance is less than $1$. Division by a nonzero element followed by this
nearest-lattice-point choice gives a remainder of smaller norm. Hence $R$ is
a unique-factorization domain. Its units are

$$
\{\pm1,\pm\omega,\pm\omega^2\}.
$$

Write $\lambda=1-\omega$. Then

$$
N(\lambda)=3,
\qquad
3=-\omega^2\lambda^2.                  \tag{2.1a}
$$

**Theorem 2.1 (descent for cubes).** There are no nonzero integers $x,y,z$
with $x^3+y^3=z^3$.

**Proof.** Divide a hypothetical solution by its common gcd. Cubes of integers
prime to $3$ are $\pm1$ modulo $9$. If none of $x,y,z$ were divisible by $3$,
the left side modulo $9$ would be $-2$, $0$, or $2$, never $\pm1$. Pairwise
coprimality shows that exactly one variable is divisible by $3$.

Among all primitive solutions choose one for which the absolute value of that
distinguished variable is least. Move its cube to the right, changing signs
if necessary. We obtain pairwise coprime nonzero integers $X,Y,Z$ such that

$$
X^3+Y^3=Z^3,
\qquad
3\mid Z,
\qquad
3\nmid XY.                              \tag{2.1b}
$$

Modulo $3$, $X+Y\equiv0$. Put

$$
X+Y=3M,
\qquad
X^2-XY+Y^2=3N.
$$

Substitution of $Y=3M-X$ gives

$$
N=X^2-3MX+3M^2.
$$

Consequently $3\nmid N$ and
$\gcd(M,N)=\gcd(M,X^2)=1$. From

$$
Z^3=9MN
$$

unique factorization in $\mathbf Z$ shows that $N$ is a signed cube, that
every prime other than $3$ occurs in $M$ to a multiple of three, and that
$v_3(M)\equiv1\pmod3$. Thus, for a nonzero integer $r$,

$$
M=3r^3,
\qquad
X+Y=9r^3.                               \tag{2.1c}
$$

Now factor in $R$:

$$
(X+Y)(X+\omega Y)(X+\omega^2Y)=Z^3.    \tag{2.1d}
$$

Any common prime divisor of two factors away from $\lambda$ would divide both
$X$ and $Y$. Moreover,

$$
X+\omega Y=(X+Y)-\lambda Y
$$

has $\lambda$-valuation exactly one: the first term has valuation at least
four by (2.1a) and (2.1c), while the second has valuation one. Unique
factorization therefore gives

$$
X+\omega Y=\varepsilon\lambda(a+b\omega)^3.             \tag{2.1e}
$$

The unit cannot be suppressed without checking it. Absorbing a sign into the
cube leaves $\varepsilon\in\{1,\omega,\omega^2\}$. Write

$$
(a+b\omega)^3=U+V\omega,
$$

where direct expansion gives

$$
U=a^3+b^3-3ab^2,
\qquad
V=3ab(a-b).                             \tag{2.1f}
$$

Since $a+b\omega$ is not divisible by $\lambda$, we have
$U\equiv a+b\not\equiv0\pmod3$, whereas $3\mid V$. The sum of the two
integer coefficients on the right of (2.1e) is respectively

$$
3V,\qquad 3(U-V),\qquad -3U
$$

as $\varepsilon$ is $1,\omega,\omega^2$. The last two quantities have
exactly one factor of $3$, contradicting (2.1c). Hence $\varepsilon=1$, and
comparison with (2.1c) yields

$$
r^3=ab(a-b).                            \tag{2.1g}
$$

If a rational integer divided both $a$ and $b$, its cube would divide both
coefficients in (2.1e), contrary to $\gcd(X,Y)=1$. Thus $a,b,a-b$ are
pairwise coprime. Their product is a cube, so signs included, there exist
nonzero integers $u,v,w$ such that

$$
a=u^3,
\qquad b=v^3,
\qquad a-b=w^3.
$$

We have produced another solution

$$
v^3+w^3=u^3.                            \tag{2.1h}
$$

It is genuinely smaller. Taking norms in (2.1e) and using (2.1d),

$$
N(a+b\omega)^3
=\frac{X^2-XY+Y^2}{3}
=\frac{|Z|^3}{3|X+Y|}
\leq\frac{|Z|^3}{27}.
$$

For integers $a,b$, the positive form $a^2-ab+b^2$ is at least each of
$|a|,|b|,|a-b|$; this follows by completing the square, with the cases of
absolute value at most one immediate. Hence

$$
|u|,|v|,|w|<|Z|.
$$

Exactly one of $u,v,w$ is divisible by $3$, by the same modulo-$9$ argument.
After moving that cube to the right, (2.1h) contradicts the minimal choice of
$|Z|$. $\square$

This descent closes the only odd prime exponent not covered by the later Frey
construction. In particular, no modularity or representation-theoretic input
will be invoked at exponent $3$.

### 2.3 The exponent four

If $n$ has no odd prime divisor and $n>2$, then $n=2^r$ with $r\ge2$, so $4\mid n$.
It is enough to exclude exponent $4$. We prove the stronger statement that

$$
X^4+Y^4=Z^2
\tag{2.2a}
$$

has no solution in positive integers.

**Theorem 2.2 (descent for fourth powers).** Equation (2.2a) has no positive
integer solution.

**Proof.** Assume otherwise and choose a solution with $Z$ minimal. Divide by
the common divisor of $X$ and $Y$; after absorbing its square into $Z$, we may
assume $\gcd(X,Y)=1$. Exactly one of $X,Y$ is even. Interchange them so that
$Y$ is even.

Indeed, they cannot both be even by coprimality, while if both were odd then
$X^4+Y^4\equiv2\pmod{16}$, which is not a square modulo $16$.

The triple

$$
(X^2,Y^2,Z)
$$

is a primitive Pythagorean triple. Hence there are coprime integers $m>n>0$ of
opposite parity such that

$$
X^2=m^2-n^2,
\qquad
Y^2=2mn,
\qquad
Z=m^2+n^2.
\tag{2.2b}
$$

Since $X$ is odd, $m$ is odd and $n$ is even. Coprimality in (2.2b) and unique
factorization of integers imply

$$
m=R^2,
\qquad
n=2S^2.
\tag{2.2c}
$$

Indeed, every odd prime occurs to an even exponent in each of $m,n$, while
$1+v_2(n)$ is even, so $v_2(n)$ is odd.

Substituting (2.2c) into the first equation of (2.2b) gives

$$
X^2+(2S^2)^2=R^4.
$$

This is again a primitive Pythagorean triple. Therefore there are coprime
$U>V>0$ of opposite parity with

$$
X=U^2-V^2,
\qquad
2S^2=2UV,
\qquad
R^2=U^2+V^2.
$$

The middle equality says $S^2=UV$. Since $U$ and $V$ are coprime, each is a
square: $U=H^2$ and $V=K^2$. Consequently

$$
H^4+K^4=R^2.
$$

This is another positive solution of (2.2a), but

$$
R^2=m< m^2+n^2=Z,
$$

so $R<Z$. This contradicts the minimal choice of $Z$. $\square$

In particular, $X^4+Y^4=Z^4$ is impossible, since it would give (2.2a) with
the right side $(Z^2)^2$.

### 2.4 The complete exponent reduction

Let $n>2$. If $n$ has an odd prime divisor, Section 2.1 reduces a hypothetical
solution to an odd prime exponent. The case $p=3$ is impossible by Theorem 2.1,
and the remaining primes are $p\ge5$. If $n$ has no odd prime divisor, then
$4\mid n$ and the substitution

$$
X=|x|^{n/4},
\qquad
Y=|y|^{n/4},
\qquad
Z=|z|^{n/4}
$$

contradicts Theorem 2.2. Thus it remains only to exclude nonzero solutions of
prime exponent $p\ge5$.

## 3. Primitive prime-exponent solutions

The local model at $2$ depends on more than knowing that one of the variables
is even. We now normalize a hypothetical solution without assuming that all
three signed variables can remain positive.

### 3.1 Primitivity and pairwise coprimality

Let

$$
a_0^p+b_0^p=c_0^p,
\qquad p\ge5
\tag{3.1}
$$

be a nonzero integer solution. Divide $a_0,b_0,c_0$ by their common gcd. The
result is again an integer solution, now with

$$
\gcd(a_0,b_0,c_0)=1.
$$

It is then pairwise coprime. For example, a prime dividing $a_0$ and $b_0$
also divides $c_0^p$ and hence $c_0$, contradicting primitivity. The other
pairs are identical.

This elementary observation is load-bearing. It implies that a rational prime
can divide at most one of the three root differences used in the Frey equation.

### 3.2 Signs and the unique even term

Rewrite (3.1) as a signed three-term equation

$$
a_0^p+b_0^p+(-c_0)^p=0.
\tag{3.2}
$$

Modulo $2$, the number of odd terms in (3.2) is even. It cannot be zero by
primitivity, so exactly two terms are odd and exactly one is even. Denote the
even signed term by $e$ and the odd terms by $u,v$. Then

$$
e^p+u^p+v^p=0.
$$

Set

$$
a=e,
\qquad b=u,
\qquad c=-v.
$$

We have obtained

$$
a^p+b^p=c^p,
\tag{3.3}
$$

with $a$ even and $b,c$ odd. This signed permutation handles, without a
positivity assumption, the case in which the even term was originally on the
right side of (3.1).

The variables remain nonzero and pairwise coprime. Replacing all three by their
negatives preserves (3.3), because $p$ is odd.

### 3.3 The two-adic normalization

Since $a$ is even and $p\ge5$,

$$
a^p\equiv0\pmod{32}.
$$

Equation (3.3) gives $b^p\equiv c^p\pmod{32}$ and in particular modulo $4$.
For every odd integer $t$ and odd exponent $p$,

$$
t^p\equiv t\pmod4.
$$

Thus $b\equiv c\pmod4$. If both are $3$ modulo $4$, negate $a,b,c$.
We may therefore impose the fixed normalization

$$
\boxed{
a\text{ even},\qquad b,c\text{ odd},\qquad b\equiv c\equiv1\pmod4.}
\tag{3.4}
$$

No stronger congruence modulo $8$ is being assumed. That distinction will
determine whether the multiplicative reduction at $2$ is split or nonsplit.

## 4. The Frey curve and its invariants

### 4.1 Why this cubic is chosen

The curve must turn the three coprime terms of the Fermat equation into local
collision data. The most economical way is to make those terms the three
root differences of a cubic. This simultaneously exposes full rational
$2$-torsion, which will control rational isogenies, and makes every bad prime
visible in a factorized discriminant. These requirements determine the
following convention up to harmless permutations and quadratic twists.

Put

$$
A=a^p,
\qquad B=b^p,
\qquad C=c^p=A+B.
\tag{4.1}
$$

The Frey curve is

$$
\boxed{
E=E_{a,b,p}: y^2=x(x-A)(x+B).}
\tag{4.2}
$$

The three roots are $0,A,-B$, so their pairwise differences are, up to sign,

$$
A,\qquad B,\qquad A+B=C.
$$

This is why the cubic takes its apparently asymmetric form: every term of the
Fermat equation becomes a root difference. A prime dividing one Diophantine
variable makes exactly two roots collide, which is the geometric signature of
multiplicative reduction.

The points

$$
(0,0),\qquad(A,0),\qquad(-B,0)
$$

are the three nonzero rational points of order $2$. Hence

$$
E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
\tag{4.3}
$$

Pairwise coprimality and $abc\ne0$ make the three roots distinct, so $E$ is
nonsingular.

### 4.2 The integral invariants

Expanding (4.2) gives

$$
y^2=x^3+(B-A)x^2-ABx.
$$

Thus

$$
a_1=a_3=a_6=0,
\qquad a_2=B-A,
\qquad a_4=-AB.
$$

The intermediate invariants are

$$
b_2=4(B-A),
\qquad b_4=-2AB,
\qquad b_6=0,
\qquad b_8=-A^2B^2.
$$

Substitution in the standard formulas yields

$$
\boxed{c_4=16(A^2+AB+B^2),}
\tag{4.4}
$$

$$
\boxed{c_6=-32(B-A)(2A^2+5AB+2B^2),}
\tag{4.5}
$$

and

$$
\begin{aligned}
\Delta
&=16A^2B^2\bigl((B-A)^2+4AB\bigr)\\
&=16A^2B^2(A+B)^2\\
&=\boxed{16A^2B^2C^2=2^4(abc)^{2p}.}
\end{aligned}
\tag{4.6}
$$

Consequently

$$
\boxed{
j(E)=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}.}
\tag{4.7}
$$

The signs and powers of $2$ can be checked by the universal relation

$$
c_4^3-c_6^2=1728\Delta.
\tag{4.8}
$$

Equation (4.6) can also be read directly: the discriminant of the monic cubic
is the square of the product of its three root differences, and the elliptic
discriminant of $y^2=f(x)$ is $16$ times that cubic discriminant.

### 4.3 A worked numerical audit

The tuple

$$
(A,B,C)=(32,1,33)
$$

is not asserted to come from a Fermat solution; it is a useful sign and
$2$-power check because it has exactly the required local parity. Formulas
(4.4)--(4.6) give

$$
c_4=16(1024+32+1)=16\cdot1057,
$$

$$
c_6=-32(1-32)(2\cdot1024+5\cdot32+2),
$$

and

$$
\Delta=16\cdot32^2\cdot33^2.
$$

After the two-adic change of variables in Chapter 6, $c_4$ loses precisely a
factor $2^4$ and $\Delta$ loses precisely a factor $2^{12}$. The new
discriminant valuation is

$$
4+2\cdot5-12=2,
$$

which anticipates the general formula $2p\,v_2(a)-8$.

## 5. Odd-prime minimal models

The factorization of the discriminant tells us where bad reduction can occur,
but a conductor calculation needs a minimal equation and a reduction type.
At odd primes the displayed Frey equation is already the correct model.

### 5.1 Good primes

Let $q$ be odd and suppose $q\nmid abc$. Then $A,B,C$ are $q$-adic units, so
(4.6) gives

$$
v_q(\Delta)=0.
$$

The integral equation (4.2) is therefore smooth over $\mathbf Z_q$, and $E$
has good reduction at $q$. This includes primes which happen to divide
$A^2+AB+B^2$: vanishing of $c_4$ modulo $q$ does not cause bad reduction when
the discriminant is a unit.

### 5.2 Primes dividing one root difference

Suppose $q\mid a$. Pairwise coprimality makes $B$ and $C$ units, and

$$
A^2+AB+B^2\equiv B^2\not\equiv0\pmod q.
$$

Hence $c_4$ is a unit at $q$. An integral equation with unit $c_4$ cannot be
made smaller by an admissible change of variables, so (4.2) is minimal.
Its discriminant has positive valuation, and unit $c_4$ shows that the
reduction is multiplicative. Formula (4.6) gives

$$
v_q(\Delta_{\min})=2v_q(A)=2p\,v_q(a).
\tag{5.1}
$$

The two other cases are the same computation with a different root
difference. If $q\mid b$, then

$$
A^2+AB+B^2\equiv A^2\not\equiv0\pmod q,
$$

while if $q\mid c$, then $B\equiv-A\pmod q$ and

$$
A^2+AB+B^2\equiv A^2\not\equiv0\pmod q.
$$

Thus

$$
v_q(\Delta_{\min})=
\begin{cases}
2p\,v_q(a),&q\mid a,\\
2p\,v_q(b),&q\mid b,\\
2p\,v_q(c),&q\mid c.
\end{cases}
\tag{5.2}
$$

The nodal tangent calculation also records the split character. It is not
needed for the conductor, but it is a useful diagnostic:

$$
\begin{array}{c|c}
\text{divisibility}&\text{split multiplicative exactly when}\\
\hline
q\mid a&B\text{ is a square modulo }q,\\
q\mid b&-A\text{ is a square modulo }q,\\
q\mid c&A\text{ is a square modulo }q.
\end{array}
\tag{5.3}
$$

For example, if $q\mid a$, the reduced equation is
$y^2=x^2(x+B)$ and its tangent cone at the node is
$y^2-Bx^2$.

### 5.3 The odd local discriminant ledger

Combining the preceding sections gives the complete odd-prime statement:

$$
\boxed{
\begin{array}{ll}
q\nmid abc:&E\text{ has good reduction and }v_q(\Delta_{\min})=0,\\[2mm]
q\mid abc:&E\text{ has multiplicative reduction and }
v_q(\Delta_{\min})=2p\,v_q(abc).
\end{array}}
\tag{5.4}
$$

In the second line only one of $v_q(a),v_q(b),v_q(c)$ is nonzero, so the
compact notation is unambiguous. In particular, the conclusion remains true
when $q=p$.

## 6. The prime two

At $2$, the factor $16$ in (4.6) and the large even root difference make the
original equation nonminimal. Removing the correct twelfth power of $2$ is
essential: the residual representation at $2$ depends on the resulting
valuation modulo $p$.

### 6.1 Why the displayed equation is not minimal

From (3.4),

$$
v_2(A)=p\,v_2(a)\ge5,
\qquad B,C\text{ are odd}.
\tag{6.1}
$$

Moreover

$$
B-A\equiv1\pmod4.
\tag{6.2}
$$

The raw discriminant valuation is

$$
v_2(\Delta)=4+2p\,v_2(a).
$$

The large gap between the even root $A$ and the two odd roots permits an
integral rescaling by $u=2$; its effect on the discriminant is division by
$u^{12}=2^{12}$.

### 6.2 The integral change of variables

Make the admissible change

$$
x=4x',
\qquad
y=8y'+4x'.
\tag{6.3}
$$

Substitution in (4.2) and division by $64$ gives

$$
\boxed{
y'^2+x'y'
=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x'.}
\tag{6.4}
$$

Both coefficients are integral. The first is integral by (6.2), and the
second is integral because $v_2(A)\ge5$. Under (6.3), the invariants transform
by

$$
c_4'=2^{-4}c_4,
\qquad
c_6'=2^{-6}c_6,
\qquad
\Delta'=2^{-12}\Delta.
$$

Consequently

$$
c_4'=A^2+AB+B^2,
\tag{6.5}
$$

$$
c_6'=-\frac{(B-A)(2A^2+5AB+2B^2)}2,
\tag{6.6}
$$

and

$$
\boxed{\Delta'=2^{-8}A^2B^2C^2.}
\tag{6.7}
$$

Formula (6.6) is integral: $A$ is even, $B$ is odd, and the second factor in
its numerator is even.

### 6.3 Minimality, multiplicative reduction, and splitting

The number $c_4'$ is odd, because

$$
A^2+AB+B^2\equiv B^2\equiv1\pmod2.
$$

Also

$$
v_2(\Delta')=2p\,v_2(a)-8\ge2.
\tag{6.8}
$$

Thus (6.4) is minimal and has multiplicative reduction. We have proved the
exact formula

$$
\boxed{v_2(\Delta_{\min})=2p\,v_2(a)-8.}
\tag{6.9}
$$

The split type can be read from the special fiber. Put

$$
\alpha=\frac{B-A-1}{4}.
$$

Since $AB/16$ is even, the tangent cone at the node is

$$
y^2+xy+\overline\alpha x^2.
$$

It splits over $\mathbf F_2$ exactly when $\overline\alpha=0$. Because
$A\equiv0\pmod{32}$, this gives

$$
\begin{array}{c|c}
B\pmod8&\text{reduction at }2\\
\hline
1&\text{split multiplicative},\\
5&\text{nonsplit multiplicative}.
\end{array}
\tag{6.10}
$$

Our normalization $b\equiv1\pmod4$ permits both rows. The conductor exponent
is one in either case.

## 7. Semistability, discriminant, and conductor

The separate local models now have to be assembled without confusing three
different invariants: the minimal discriminant, the conductor of the elliptic
curve, and the conductor after reduction modulo the Fermat prime. The first
remembers large valuations, the second remembers only that each bad fiber is
multiplicative, and the third can lose an odd bad prime when its monodromy
parameter becomes divisible by $p$. This chapter records all three layers.

### 7.1 The complete minimal-discriminant formula

Chapters 5 and 6 show that every bad prime is multiplicative. Hence

$$
\boxed{E/\mathbf Q\text{ is semistable}.}
\tag{7.1}
$$

Prime by prime, the minimal discriminant valuations are

$$
\boxed{
v_q(\Delta_{\min})=
\begin{cases}
2p\,v_q(a)-8,&q=2,\\
2p\,v_q(abc),&q\text{ odd and }q\mid abc,\\
0,&q\nmid abc.
\end{cases}}
\tag{7.2}
$$

The first line is positive because $p\ge5$ and $v_2(a)\ge1$. Thus no prime
dividing $abc$ disappears from the bad-reduction set.

### 7.2 The exact conductor

Good reduction has conductor exponent zero. Multiplicative reduction has
conductor exponent one, independently of whether it is split. Therefore

$$
f_q(E)=
\begin{cases}
1,&q\mid abc,\\
0,&q\nmid abc.
\end{cases}
$$

Since $a$ is even, $2\mid abc$. The global conductor is exactly

$$
\boxed{
N_E=\prod_{q\mid abc}q=\operatorname{rad}(|abc|).}
\tag{7.3}
$$

This formula is a conclusion of the local calculations, not a folklore
shortcut. In particular, the exponent of $2$ in the conductor is one even
though the raw equation has discriminant valuation at least $14$.

### 7.3 What is and is not removed modulo $p$

Let $q\ne p$ be a multiplicative prime. The Tate-curve inertia calculation
says that the action on $E[p]$ is unramified exactly when

$$
p\mid v_q(\Delta_{\min}).
\tag{7.4}
$$

Here is the calculation behind the criterion. After an unramified quadratic
twist, choose the Tate basis given by a $p$th root of unity and a $p$th root
of the Tate parameter $q_E$. Since $q\neq p$, the cyclotomic character is
unramified on inertia, and

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
1&v_q(q_E)t_p(\sigma)\\
0&1
\end{pmatrix}
\qquad(\sigma\in I_q),                 \tag{7.4a}
$$

where $t_p:I_q\twoheadrightarrow\mathbf F_p$ is the tame character. For a
minimal multiplicative equation, $v_q(q_E)=v_q(\Delta_{\min})$. The
unramified twist does not alter inertia. Thus the matrix is trivial exactly
when (7.4) holds; otherwise its inertia image has order $p$ and its fixed
space has codimension one, giving conductor exponent one.

For an odd $q\mid abc$ with $q\ne p$, equation (7.2) gives the divisibility
in (7.4). Thus

$$
E[p]\text{ is unramified at every odd }q\mid abc,\ q\ne p.
\tag{7.5}
$$

At $2$, however,

$$
v_2(\Delta_{\min})
=2p\,v_2(a)-8
\equiv-8\not\equiv0\pmod p.
\tag{7.6}
$$

Consequently

$$
\boxed{E[p]\text{ is ramified at }2.}
\tag{7.7}
$$

Its inertia is nonzero tame unipotent and its conductor exponent is one. This
single local fact is the reason the residual level is $2$ rather than $1$.

## 8. The residual representation at the Fermat prime

Let

$$
\overline\rho_{E,p}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p)
\tag{8.1}
$$

be the action on $E[p]$. We now assemble the exact local and global record
needed by any lifting or level-lowering argument.

### 8.1 Determinant, parity, and ramification

The Weil pairing gives

$$
\boxed{\det\overline\rho_{E,p}=\overline\chi_p.}
\tag{8.2}
$$

For complex conjugation $c$, the cyclotomic character has value $-1$, so

$$
\det\overline\rho_{E,p}(c)=-1.
\tag{8.3}
$$

Because $p$ is odd and $c^2=1$, its eigenvalues are $1$ and $-1$ and its
trace is zero. Thus the representation is odd.

Away from $p$, Chapters 5--7 give the complete ramification record:

$$
\overline\rho_{E,p}
\text{ is unramified outside }\{2,p\},
\tag{8.4}
$$

and its conductor exponent at $2$ is exactly one.

### 8.2 Finite flatness at $p$

The coefficient-prime place has two cases.

If $p\nmid abc$, the curve has good reduction at $p$. The finite group scheme
$\mathcal E[p]$ of the good elliptic scheme over $\mathbf Z_p$ is a
finite-flat model of $E[p]$.

Suppose instead that $p\mid abc$. The curve has multiplicative reduction and

$$
m:=v_p(\Delta_{\min})=2p\,v_p(abc)
\tag{8.5}
$$

is divisible by $p$. Let $K/\mathbf Q_p$ be the trivial or unramified
quadratic extension which splits the torus. Tate uniformization over $K$
gives

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0,
\tag{8.6}
$$

whose extension class is the class of a Tate parameter
$q_E\in K^\times/K^{\times p}$ with
$v_K(q_E)=m$, where $v_K(p)=1$. Write

$$
q_E=p^m u,\qquad u\in\mathcal O_K^\times.
$$

Since $p\mid m$, the class of $q_E$ equals the class of the unit $u$:

$$
p^m=\bigl(p^{m/p}\bigr)^p.
$$

Flat Kummer theory over $\mathcal O_K$ realizes unit classes as finite-flat
extensions of the constant group by $\mu_p$. The Tate descent datum over the
unramified extension is finite étale, so finite-flat descent carries this
model back to $\mathbf Z_p$; equivalently, the possible unramified quadratic
twist preserves finite flatness. Therefore

$$
\boxed{E[p]\text{ is finite flat at }p}
\tag{8.7}
$$

in both the good-reduction and multiplicative cases.

Because the local base is $\mathbf Q_p$ and $p\ge5$, this is the low-weight
finite-flat range: the two labels are $0$ and $1$, both lying in
$[0,p-2]$. The finite-flat ramification theorem therefore supplies the small
coefficient-prime ramification bound required by the deformation problem. In
the ordinary branch the residual semisimplification on inertia is
$1\oplus\overline\chi_p$; in the supersingular good-reduction branch the two
niveau-two inertia weights have base-$p$ digits $0$ and $1$. These are
different shapes of the same finite-flat type, so finite flatness must not be
replaced by an assumption of ordinarity.

This is a level-one assertion. If $E$ is multiplicative at $p$, the same
argument does not make every $E[p^n]$ finite flat: the fixed valuation $m$ is
not divisible by all $p^n$. Thus the full $p$-adic Tate module is semistable
ordinary, not a smooth finite-flat lift of type $(0,1)$.

### 8.3 The exact residual level

Combining (8.2), (8.4), (8.7), and irreducibility from the next chapter gives
the classical residual package:

$$
\boxed{
\begin{array}{l}
\overline\rho_{E,p}\text{ is odd and irreducible},\\
\det\overline\rho_{E,p}=\overline\chi_p,\\
\overline\rho_{E,p}\text{ is finite flat at }p,\\
\overline\rho_{E,p}\text{ has prime-to-}p\text{ conductor }2.
\end{array}}
\tag{8.8}
$$

The last line is exact. Every odd bad prime away from $p$ has disappeared
modulo $p$, while $2$ has not.

## 9. Irreducibility from rational isogenies

All local entries in the residual package are now known except
irreducibility. A stable line in $E[p]$ is geometric: it is the kernel of a
rational cyclic isogeny. The subtle point is that a rational kernel need not
have a rational generator. Semistability is what converts one of the two
isogeny characters into the trivial character, and full rational
$2$-torsion then makes the exceptional degrees $5$ and $7$ accessible to the
explicit mixed-torsion calculations of Book 70.

### 9.1 The stable-line dictionary

If $\overline\rho_{E,p}$ is reducible over $\mathbf F_p$, it has a
$G_{\mathbf Q}$-stable line. Finite étale descent turns that line into a
rational cyclic subgroup scheme $C\subset E[p]$ of rank $p$, and the quotient
map

$$
E\longrightarrow E/C
\tag{9.1}
$$

is a rational cyclic isogeny of degree $p$. Conversely, the kernel of such an
isogeny is a stable line. Thus

$$
E[p]\text{ reducible over }\mathbf F_p
\Longleftrightarrow
E\text{ has a rational }p\text{-isogeny}.
\tag{9.2}
$$

This statement concerns a rational subgroup, not necessarily a rational
generator. The extra passage to rational torsion uses semistability.

### 9.2 The semistable full-two theorem

The semistable full-two criterion (13.6) in Book 70 proves the exact
FLT-facing result:

> If an elliptic curve over $\mathbf Q$ is semistable and has full rational
> $2$-torsion, then its mod-$\ell$ representation is irreducible over
> $\mathbf F_\ell$ for every prime $\ell\ge5$.

Both hypotheses have been verified for the Frey curve in (4.3) and (7.1).
Taking $\ell=p$ gives

$$
\boxed{\overline\rho_{E,p}\text{ is irreducible over }\mathbf F_p.}
\tag{9.3}
$$

It is useful to recall why the result has exactly this scope. A rational
$p$-isogeny on a semistable curve has a kernel character $\lambda$ whose
restriction at $p$ is either trivial or cyclotomic and which is unramified at
every other finite prime. Hence either $\lambda$ or the dual kernel character
$\overline\chi_p\lambda^{-1}$ is everywhere unramified and therefore trivial.
One of the two isogenous curves consequently has a rational point of order
$p$. An odd isogeny transports the full rational $2$-torsion isomorphically
to the other curve.

For $p\ge11$, the independent prime-torsion theorem excludes the rational
$p$-torsion. The two remaining degrees require the mixed-torsion
calculations described next.

### 9.3 The exponents five and seven

For $p=5$, reducibility would produce, on one side of the isogeny, both full
rational $2$-torsion and a rational point of order $5$. Its torsion would
contain

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/10\mathbf Z.
$$

Book 70 derives from Tate normal form the necessary curve

$$
C_5:\quad z^2=t(t^2-11t-1)
$$

and proves

$$
C_5(\mathbf Q)=\{\infty,(0,0)\}.
$$

Both points are boundary or degenerate parameters, so no such elliptic curve
exists.

For $p=7$, the analogous torsion subgroup

$$
\mathbf Z/2\mathbf Z\times\mathbf Z/14\mathbf Z
$$

would give a nondegenerate rational point on

$$
C_7:\quad
z^2=t(t-1)(t^3-8t^2+5t+1).
$$

The complete Jacobian descent and Mordell--Weil sieve of Book 70 gives

$$
C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\},
$$

again only degenerate or cuspidal parameters. Thus the small primes are not
hidden inside a large-prime theorem; each is explicitly closed.

### 9.4 Absolute irreducibility

Theorem (9.3) says irreducible over $\mathbf F_p$. The lifting theorems used
later ask for absolute irreducibility. Oddness upgrades the conclusion in
this two-dimensional situation.

**Lemma 9.1.** An odd two-dimensional representation over $\mathbf F_p$,
$p$ odd, which is irreducible over $\mathbf F_p$ is absolutely irreducible.

**Proof.** If $V$ were irreducible over $\mathbf F_p$ but not absolutely
irreducible, its endomorphism division ring would be $\mathbf F_{p^2}$.
Then $V$ would be one-dimensional over $\mathbf F_{p^2}$ and the image would
act by $\mathbf F_{p^2}$-scalars. Complex conjugation would act by a scalar
$u$ satisfying $u^2=1$. Since $p$ is odd, $u=\pm1$, and its determinant on
the underlying two-dimensional $\mathbf F_p$-space would be $u^2=1$. This
contradicts oddness. $\square$

Consequently

$$
\boxed{\overline\rho_{E,p}\text{ is absolutely irreducible}.}
\tag{9.4}
$$

Absolute irreducibility still does not, by itself, verify adequacy, an adjoint
vanishing, residual automorphy, or any automorphic component condition.

## 10. The Frey compatible system

The representation modulo the Fermat prime contains the level-lowering
miracle, but reduction has also discarded information. In particular, the
congruence

$$
2p\,v_q(abc)\equiv0\pmod p
$$

can make multiplicative inertia invisible modulo $p$, even though the original
elliptic curve is still multiplicative at $q$. To change coefficient primes
without confusing these two layers, we now retain the entire family of Tate
modules of $E$.

### 10.1 Common Frobenius polynomials

For each rational prime $\ell$, set

$$
T_\ell E=\varprojlim_m E[\ell^m](\overline{\mathbf Q}),
\qquad
V_\ell E=T_\ell E\otimes_{\mathbf Z_\ell}\mathbf Q_\ell,
$$

and write

$$
\rho_{E,\ell}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}(V_\ell E).
$$

If $q\nmid \ell N_E$, reduction of $E$ modulo $q$ is an elliptic curve. Put

$$
a_q=q+1-\#E(\mathbf F_q).
$$

The characteristic polynomial of arithmetic Frobenius in the normalization
used throughout the preceding books is

$$
P_q(X)=X^2-a_qX+q.                     \tag{10.1}
$$

It belongs to $\mathbf Z[X]$, is independent of $\ell$, and satisfies

$$
\det\rho_{E,\ell}=\chi_\ell.           \tag{10.2}
$$

Here $\chi_\ell$ is the $\ell$-adic cyclotomic character. Equation (10.2)
comes directly from the Weil pairing

$$
T_\ell E\times T_\ell E\longrightarrow\mathbf Z_\ell(1).
$$

It is therefore an equality of characters, not merely an equality of
determinants at a density-one collection of Frobenius elements.

The family

$$
\mathcal V(E)=\{V_\ell E\}_\ell       \tag{10.3}
$$

is a rational compatible system with coefficient field $\mathbf Q$. Its
common good polynomials are (10.1). For every complex embedding, the two roots
$\alpha_q,\beta_q$ of $P_q$ obey

$$
|\alpha_q|=|\beta_q|=q^{1/2}.          \tag{10.4}
$$

Thus the system is pure of weight one. Notice the normalization: determinant
$q$ at Frobenius, Hodge--Tate labels $\{0,1\}$, and complex absolute value
$q^{1/2}$ are three faces of the same weight-one convention.

For later use, the elementary point-count identity gives the concrete bound

$$
|a_q|\leq2\sqrt q.                     \tag{10.5}
$$

This will be compared with the trace $1+q$ of
$\mathbf 1\oplus\chi_3$. Inequality (10.5) survives a change of coefficient
prime *within* the original rational system because its Frobenius polynomials
are common. A later level-lowered system need not have the same $a_q$ as the
Frey curve; what survives there is the weight-one purity bound for that new
system's own trace.

### 10.2 Hodge theory, purity, and local compatibility

The three local regimes of $V_\ell E$ must be kept separate.

At a prime $q\neq\ell$ of good reduction, $V_\ell E$ is unramified and has
Frobenius polynomial (10.1). At a prime $q\neq\ell$ of multiplicative
reduction, it has a Steinberg Weil--Deligne parameter: its inertia is
unipotent, its nilpotent operator $N_q$ has rank one, and its Artin conductor
exponent is one. The split or nonsplit unramified quadratic character is the
one computed in Sections 5.2 and 6.3. At the coefficient prime $\ell$, good
reduction makes $V_\ell E$ crystalline with Hodge--Tate labels $\{0,1\}$;
multiplicative reduction makes it semistable and noncrystalline, again with
labels $\{0,1\}$.

These statements give strong compatibility away from coefficient primes. In
particular, for every fixed $q$ and all $\ell\neq q$, the Weil--Deligne
parameter has the same semisimplified Frobenius, the same inertial type, and
the same nilpotent rank. The conductor of the characteristic-zero member is
therefore

$$
N(V_\ell E)=\operatorname{rad}(|abc|)
$$

away from the coefficient prime, exactly as in (7.3). Strong compatibility
does not say that every residual conductor is the same: reduction of a lattice
can kill a unipotent extension class.

There is an equally important integral distinction at the coefficient prime.
If $E$ has good reduction at $\ell$, the finite group schemes $E[\ell^m]$ over
$\mathbf Z_\ell$ show that the distinguished lattice $T_\ell E$ has finite-flat
quotients at every level. If $E$ is multiplicative at $\ell$, the rational
representation is semistable noncrystalline. Section 8.2 proved the special
fact that $E[p]$ is finite flat when $p$ is the Fermat exponent and
$p\mid abc$, because the valuation of the Tate parameter is divisible by
$p$. It did not prove finite flatness of $E[p^m]$ for all $m$. Indeed, for
$d=v(q_E)$ over the unramified splitting field and $r>v_p(d)$, the
valuation direction cannot be a
$p^r$-th power. Thus

$$
E[p]\text{ finite flat}
\quad\not\Longrightarrow\quad
T_pE/p^mT_pE\text{ finite flat for every }m.       \tag{10.6}
$$

This is why a later all-level finite-flat theorem cannot be applied directly
to a multiplicative coefficient-prime member merely by citing the residual
calculation.

Oddness is also compatible across the system. For complex conjugation $c$,
the determinant identity gives

$$
\det\rho_{E,\ell}(c)=\chi_\ell(c)=-1. \tag{10.7}
$$

No coefficient enlargement changes this sign. A finite scalar extension may
be needed to compare a member with an automorphic representation, but it
neither changes (10.1) nor turns a residue field of degree greater than one
into $\mathbf F_\ell$.

### 10.3 The immovable monodromy at two

Section 6.3 proved that $E$ has multiplicative reduction at $2$. Hence for
every $\ell\neq2$ the common local parameter at $2$ has

$$
\operatorname{rank}N_2=1.              \tag{10.8}
$$

This nonzero operator is a characteristic-zero invariant. It is not erased by
changing $\ell$, extending coefficient fields, or restricting to a finite base
field. After restriction to a local extension it may be multiplied by a
nonzero ramification index, but it remains nonzero in characteristic zero.

The residual picture is different. In a Tate basis, tame inertia at a
multiplicative prime acts as

$$
\begin{pmatrix}1&t_\ell(\sigma)m_2\\0&1\end{pmatrix},
$$

up to an unramified quadratic twist, where

$$
m_2=v_2(\Delta_{\min})=2p\,v_2(a)-8.  \tag{10.9}
$$

Modulo the Fermat prime, $m_2\equiv-8\not\equiv0\pmod p$, so ramification at
$2$ survives. Modulo a different coefficient prime $r$, it survives precisely
when the corresponding integral monodromy parameter is nonzero modulo the
chosen place above $r$. Therefore the statement

> the compatible system is Steinberg at $2$

does not by itself imply

> a chosen residual member is ramified at $2$.

The integral monodromy parameter is part of the switching certificate. Any
route to a $3$-adic classification must retain both sides of this distinction:
nonzero rational monodromy at $2$, and the exact residual behavior of the
chosen lattice at $2$.

## 11. The minimal hardly ramified deformation problem

The calculation up to this point gives more than a small conductor.  It gives a
specific integral deformation problem.  The distinction matters.  We do not seek
a characteristic-zero lift of the original Frey curve: its odd multiplicative
primes would remain in every such lift.  We seek a new lift of its residual
representation in which those primes have disappeared and the prime $2$ has
retained its ordered special line.

### 11.1 The exact functor

Let $p\geq5$, put $k=\mathbf F_p$, and let $W=W(k)=\mathbf Z_p$.  Let

$$
\overline\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
$$

be odd and absolutely irreducible.  Suppose that it has determinant
$\overline\chi_p$, is unramified at every odd prime different from $p$, is finite
flat at $p$, and over $G_{\mathbf Q_2}$ has an exact sequence

$$
0\longrightarrow
k(1)\otimes\overline\eta_2
\longrightarrow \overline V
\longrightarrow k\otimes\overline\eta_2
\longrightarrow0,                       \tag{11.1}
$$

where $\overline\eta_2$ is unramified and
$\overline\eta_2^2=1$.  In the Frey case the extension is ramified: Section 10.3
computed its tame parameter as

$$
m_2\equiv-8\not\equiv0\pmod p.           \tag{11.2}
$$

For a complete local $W$-algebra $A$ with residue field $k$, a **minimal hardly
ramified deformation** of $\overline\rho$ is a free rank-two $A$-representation
$\rho_A$ with the following properties.

1. Its determinant is $\chi_p$.
2. It is unramified at every odd prime $q\neq p$.
3. Its restriction at $2$ has a free rank-one quotient on which
   $G_{\mathbf Q_2}$ acts through an unramified character
   $\eta_{2,A}$ satisfying $\eta_{2,A}^2=1$.  The kernel character is then
   $\chi_p\eta_{2,A}$.
4. For every open ideal $I\subset A$, the underlying
   $(A/I)[G_{\mathbf Q_p}]$-module of $\rho_A\bmod I$ is represented by a
   finite-flat group scheme over $\mathbf Z_p$.

The last clause is deliberately levelwise.  It does not posit a single
infinite finite-flat group object.  Coefficient actions are part of the finite
level models, and changing $A$ means changing those actions.

Absolute irreducibility makes
$\operatorname{End}_{k[G_{\mathbf Q}]}(\overline V)=k$.  The global
representability theorem of Book 25, applied to the represented framed local
conditions and then divided by strict conjugacy, therefore gives a universal
ring

$$
R^{\min}
$$

and a universal minimal hardly ramified deformation

$$
\rho^{\mathrm{univ}}:
G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(R^{\min}).           \tag{11.3}
$$

This use of a universal ring is not an automorphy assertion.  It only collects
all lifts satisfying the four local rules.

### 11.2 The Frey residual point

Let a primitive Fermat solution of exponent $p\geq5$ be fixed and put

$$
\overline\rho=\overline\rho_{E,p}.
$$

Sections 7 and 8 prove that $\overline\rho$ is unramified at every odd
$q\neq p$, has determinant $\overline\chi_p$, is odd, and is finite flat at
$p$.  The Tate-curve calculation at $2$ gives (11.1).  The quotient character
is trivial in the split multiplicative case and is the unramified quadratic
character in the nonsplit case.  In either case its square is one.

Book 70 and Section 9 prove absolute irreducibility, including $p=5$ and
$p=7$.  Thus every hypothesis used to define $R^{\min}$ is verified for the
Frey residual representation.  No residual automorphy has been used.

There is also a useful image consequence.  The nonzero tame class (11.2)
gives a transvection in the image.  If $L$ is its fixed line, irreducibility
gives an element carrying $L$ to a different line.  In a basis adapted to
the two lines, powers of the transvection and its conjugate give

$$
\begin{pmatrix}1&x\\0&1\end{pmatrix},
\qquad
\begin{pmatrix}1&0\\y&1\end{pmatrix}
\qquad(x,y\in\mathbf F_p).
$$

These elementary matrices generate $\operatorname{SL}_2(\mathbf F_p)$.
Consequently

$$
\operatorname{SL}_2(\mathbf F_p)
\subseteq\overline\rho(G_{\mathbf Q}).   \tag{11.4}
$$

This calculation controls disjointness fields and self-twists in the later
potential-modularity construction.  It does not by itself supply an
automorphic maximal ideal.  In particular, the exceptional small-prime
patching issue at $p=5$ is not erased by (11.4).

### 11.3 Formal smoothness at two

The local condition at $2$ has no hidden relation.

**Lemma 11.1 (tame-quadratic lifting at $2$).**  Let $A'\twoheadrightarrow A$
be a surjection of local Artinian $W$-algebras.  Every framed deformation over
$A$ satisfying clause 3 of Section 11.1 lifts to one over $A'$ satisfying the
same clause and the fixed determinant.  Thus the framed local condition at
$2$ is formally smooth.

**Proof.**  Write the quotient as a unimodular row
$A^2\twoheadrightarrow A$.  Lift its two entries to $A'$.  At least one entry
is a unit, so elementary row operations extend the lifted row to an element
of $\operatorname{GL}_2(A')$.  After changing basis by this matrix, the
representation over $A$ is upper triangular and the quotient is the second
coordinate.

The value of its unramified character on arithmetic Frobenius is a unit
$u\in A^\times$ with $u^2=1$.  In any local ring in which $2$ is invertible,

$$
e=\frac{1+u}{2}
$$

is an idempotent.  A local ring has only the idempotents $0$ and $1$, so
$u=-1$ or $u=1$.  Its sign is detected in the common residue field and
therefore has a unique lift to $A'$.  This lifts the unramified character
$\eta_{2,A}$.  The fixed determinant then prescribes the other diagonal
character as $\chi_p\eta_{2,A'}$.

After division by the quotient character, the upper-right entry is a
continuous cocycle with values in $A(1)$.  Local Kummer theory gives, naturally
in $A$,

$$
H^1(G_{\mathbf Q_2},A(1))
\simeq
\widehat{\mathbf Q_2^\times}^{\,p}\otimes_{\mathbf Z_p}A.
                                                        \tag{11.5}
$$

Now

$$
\mathbf Q_2^\times
\simeq 2^{\mathbf Z}\times\mathbf Z_2^\times,
$$

and $\mathbf Z_2^\times$ has no nontrivial pro-$p$ quotient for odd $p$.
Hence the pro-$p$ completion in (11.5) is $\mathbf Z_p$, generated by the
valuation of $2$, and (11.5) is isomorphic to $A$.  The map on $H^1$ induced
by $A'\twoheadrightarrow A$ is therefore surjective.  Lift the cocycle,
and choose a continuous representative upstairs.  Its reduction can differ
from the original representative by a coboundary.  Lift the element producing
that coboundary and conjugate by the corresponding upper-unipotent matrix;
the adjusted cocycle now reduces exactly to the given one.  Reconstruct the
upper-triangular representation and undo the lifted change of basis.  The
quotient, determinant, and reduction are exactly the required ones.  An
arbitrary Artinian surjection is a composite of small extensions, so the same
argument applies successively. $\square$

The proof permits the extension parameter to become divisible by $p$ in
characteristic zero.  The residual Frey parameter remains nonzero because it
is fixed by (11.2).  Formal smoothness is a lifting statement, not a claim
that every point has nonzero monodromy.

### 11.4 Formal smoothness at the coefficient prime

At $p$ the local problem is not ordinary or merely crystalline; it is the
finite-flat deformation condition with determinant $\chi_p$.  Book 24 proves
the needed integral theorem in precisely this range.

**Lemma 11.2 (finite-flat lifting at $p$).**  For $p>2$ over
$\mathbf Q_p$, every rank-two finite-flat deformation with determinant
$\chi_p$ lifts through every small extension of coefficient rings.  The same
holds with a frame.  The framed fixed-determinant local functor is formally
smooth.

**Proof.**  The base $\mathbf Z_p$ is absolutely unramified and the labelled
weights are $\{0,1\}$.  The low-weight classification used in Book 24
associates to every finite-flat group a strongly divisible rank-two object.
After splitting the finite étale coefficient algebra, this object consists
of a direct-summand filtration line and invertible divided-Frobenius matrices.
Across a small extension, lift the line in the smooth Grassmannian and lift
the matrices entrywise.  Their determinants are still units.  There is one
determinant discrepancy.  Multiplying one matrix by
$\operatorname{diag}(u,1)$, where $u$ is the inverse discrepancy, corrects it
without changing any other equation.  Descent from a splitting field uses
surjectivity of the trace on the infinitesimal kernel of the norm.  The
classification then returns a finite-flat group with the lifted coefficient
action.  A frame lifts because
$\operatorname{GL}_2(A')\to\operatorname{GL}_2(A)$ is surjective. $\square$

This argument treats irreducible, nonsplit reducible, and scalar residual
shapes.  It is stronger than tangent-space membership and is the reason that
the coefficient-prime relation obstruction vanishes.

### 11.5 The balanced global presentation

Put $S=\{2,p,\infty\}$ and
$M=\operatorname{ad}^0\overline\rho$.  Let $L_2$ and $L_p$ be the tangent
spaces of Lemmas 11.1 and 11.2, and impose oddness at infinity.  The tangent
space of $R^{\min}$ is the Selmer group

$$
H^1_{\mathcal L}(\mathbf Q,M)
=
\ker\left(
H^1(G_{\mathbf Q,S},M)
\longrightarrow
\frac{H^1(\mathbf Q_2,M)}{L_2}
\times
\frac{H^1(\mathbf Q_p,M)}{L_p}
\times H^1(\mathbf R,M)
\right).                                 \tag{11.6}
$$

Let its dimension be $g$.  A relation in a minimal power-series presentation
has a canonical factor-set obstruction in $H^2(G_{\mathbf Q,S},M)$.  It is
unramified outside $S$.  Lemmas 11.1 and 11.2 lift the two finite local
restrictions, so the obstruction dies in $H^2(\mathbf Q_2,M)$ and
$H^2(\mathbf Q_p,M)$.  Oddness gives the real-place condition.  Thus every
relation functional lands in the supported kernel

$$
\ker\left(
H^2(G_{\mathbf Q,S},M)
\longrightarrow
H^2(\mathbf Q_2,M)\times H^2(\mathbf Q_p,M)
\right).                                 \tag{11.7}
$$

Poitou--Tate duality identifies the dual of (11.7) with the appropriate
quotient of the dual Selmer group.  The Greenberg--Wiles Euler-characteristic
formula compares that quotient with (11.6).  The determinant removes the
scalar direction, the real place contributes the odd line, and the local
dimensions from Lemmas 11.1 and 11.2 cancel the two finite-place corrections.
The result is

$$
\dim_k(11.7)\leq g.                       \tag{11.8}
$$

If a provisional relation lift has the right obstruction class but the wrong
local representative, the mismatch is a point of

$$
\frac{H^1(\mathbf Q_2,M)}{L_2}
\times
\frac{H^1(\mathbf Q_p,M)}{L_p}.
$$

Global reciprocity says that this point annihilates the dual Selmer group.
Exactness in Poitou--Tate therefore supplies a global class correcting the
lift.  Translating by that class restores the tame-quadratic quotient at $2$,
finite flatness at $p$, and unramifiedness elsewhere.  This proves the
relation bound, rather than merely counting ambient cohomology groups.

Consequently $R^{\min}$ has a balanced presentation

$$
R^{\min}\simeq
W[[X_1,\ldots,X_g]]/(f_1,\ldots,f_r),
\qquad r\leq g.                           \tag{11.9}
$$

The material through (11.9) is local deformation theory, global duality, and
commutative algebra.  It does not show that $R^{\min}$ has a
characteristic-zero point.  For that, one must prove that its scalar reduction
is finite.

## 12. Potential modularity as a finiteness theorem

The intended use of modularity is now precise.  It is not necessary to
descend an automorphic representation to $\mathbf Q$, and it is not necessary
to construct a level-$2$ cusp form over $\mathbf Q$.  What is necessary is an
integral automorphic factorization of the scalar-reduced universal
representation after restriction to a suitable totally real field.  That
factorization makes $R^{\min}/pR^{\min}$ finite.

### 12.1 The scalar-reduced universal representation

Set

$$
\overline R=R^{\min}/pR^{\min}
$$

and reduce (11.3):

$$
\rho_{\overline R}:G_{\mathbf Q}
\longrightarrow\operatorname{GL}_2(\overline R).        \tag{12.1}
$$

The ring $\overline R$ is a complete noetherian local $k$-algebra, not yet
known to be Artinian.  Thus (12.1) need not have finite image.  Proving its
image finite is equivalent to proving the missing vertical finiteness in the
deformation argument.

It is enough to prove finite image after restriction to an open subgroup.
Indeed, if $H\subset G_{\mathbf Q}$ has finite index and
$\rho_{\overline R}(H)$ is finite, then $\rho_{\overline R}(G_{\mathbf Q})$
is a union of finitely many cosets of that finite subgroup.  Passing from
finite image to a finite coefficient ring uses one further argument which is
easy to omit.  Absolute irreducibility gives *topological* trace generation:
the closed $k$-subalgebra generated by the traces of (12.1) is all of
$\overline R$.  Finite image makes the set of traces finite, but a finite set
of arbitrary elements need not generate a finite algebra.  What completes
the argument is integrality.

Let $T$ be one of the matrices in the finite image and let $m>0$ be its
order.  In every prime quotient $C$ of $\overline R$ one has
$T^m=1$.  After embedding the fraction field of $C$ in an algebraic closure,
all roots of the characteristic polynomial of $T$ are $m$th roots of unity.
They are integral over $k$, and so is their sum
$\operatorname{tr}(T)$.  Thus the image of every trace is integral over $k$
in every prime quotient.  Since $\overline R$ is noetherian and has only
finitely many minimal primes, multiplying one monic equation chosen on each
minimal prime and then raising the product to a power lifts these equations
through the nilradical.  Hence every trace is integral over $k$ already in
$\overline R$.

The $k$-algebra generated by the finite trace set is consequently a finite
$k$-module, hence a finite set.  A finite subset of the Hausdorff local ring
$\overline R$ is closed.  Topological trace generation says that this closed
subalgebra is dense, so it is the whole of $\overline R$.  We have therefore
proved the precise implication

$$
\boxed{
\rho_{\overline R}\text{ has finite image}
\quad\Longrightarrow\quad
\overline R\text{ is a finite }k\text{-algebra}.}
\tag{12.1a}
$$

The absolute irreducibility in this implication is used only through the
trace-generation theorem for the universal unframed deformation.  It cannot
be replaced by the observation that the image consists of finitely many
matrices: in characteristic $p$, a finite-order unipotent matrix can contain
a nonalgebraic parameter in an off-diagonal entry while having constant
trace.

### 12.2 The potential-modularity field

The two-prime construction of Book 60 is used with more data than an
irreducible residual representation.  One chooses an auxiliary odd prime
$r$, an auxiliary residually automorphic weight-two object at $r$, symplectic
frames at $p$ and $r$, polarizations, and sufficiently small prime-to-$2pr$
level.  The realization space is required to be smooth and geometrically
connected.  Its local opens impose:

- the finite-flat type at every place above $p$;
- the auxiliary automorphic type at every place above $r$;
- the ordered tame-quadratic quotient above $2$;
- hyperspecial conditions above $3$;
- disjointness from the fields cut out by both residual representations,
  their cyclotomic characters, their self-twists, and every later descent
  cocycle.

A totally real specialization theorem then gives a finite totally real field
$F$ and an auxiliary abelian variety over $F$ carrying the two prescribed
torsion modules.  The specialization is required to make every place in the
finite local-control set, in particular $2$, $p$, $r$, and $3$, split
completely.  Thus the local rings used in Lemmas 11.1 and 11.2 remain
$\mathbf Q_2$ and $\mathbf Q_p$, rather than silently changing to ramified
extensions.  The disjointness condition preserves absolute
irreducibility and (11.4).  Modularity lifting at the auxiliary prime makes
the new abelian variety automorphic.  Switching through its $p$-torsion gives
residual automorphy of

$$
\overline\rho|_{G_F}.                    \tag{12.2}
$$

This paragraph is a construction only when the integral lifting theorem used
at both coefficient primes applies to the exact local components produced by
the specialization.  Merely naming a two-prime datum does not establish it.
The Frey-special theorem in Section 13.5 must prove the component and
integral assertions described next.

For the finiteness argument, $F/\mathbf Q$ need not be solvable and no
automorphic object is descended from $F$ to $\mathbf Q$.  The field is simply
retained as the finite-index subgroup on which (12.1) will be controlled.
This is the first important simplification of the correct route.

### 12.3 The integral Hecke factorization

Let $\mathcal D_F$ be the deformation problem over $F$ obtained by restricting
the four minimal conditions of Section 11.1.  Let

$$
R_F^{\mathcal D}
$$

be its universal ring, and let $\mathbb T_F^{\mathcal D}$ be the localized
integral Hecke order acting on the definite quaternionic or curve-cohomology
module which realizes the same determinant and local conditions.  The
restricted representation (12.1) gives a map

$$
R_F^{\mathcal D}\longrightarrow\overline R.              \tag{12.3}
$$

Residual automorphy gives the non-Eisenstein maximal ideal at which the Hecke
module is localized.  The required modularity-lifting statement is an
integral factorization, up to one strict conjugacy,

$$
\rho_{\overline R}|_{G_F}
\quad\text{through}\quad
\mathbb T_F^{\mathcal D}\otimes_W k
\longrightarrow\overline R.              \tag{12.4}
$$

The order $\mathbb T_F^{\mathcal D}$ is finite over $W$.  Hence its reduction
is a finite $k$-algebra.  Equation (12.4) makes the restricted image finite.
The integrality and trace-generation argument of Section 12.1 then makes
$\overline R$ finite.

For later auditing, it is useful to state the source record without the
shorthand ``integral modularity lifting.''  Let $H=G_F$ after choosing a
compatible embedding of algebraic closures.  A **Frey-special finite-image
arithmetic source** for (12.1) consists of:

1. a finite totally real field $F/\mathbf Q$;
2. a totally definite quaternion algebra $D/F$, a compact open level $U$
   whose nonhyperspecial finite places all lie above $2$, and the finite
   integral parallel-weight-two module $M(U,W)$;
3. the faithful localized Hecke order $\mathbb T(U)_{\mathfrak m}$ cut out by
   $\overline\rho|_{G_F}$, a commutative local $k$-algebra $B$ finite as a
   $k$-module, and a surjective generalized eigenvalue map
   $$
   \theta:\mathbb T(U)_{\mathfrak m}\longrightarrow B;
   $$
4. a continuous representation
   $$
   r_B:G_F\longrightarrow\operatorname{GL}_2(B)
   $$
   which is unramified away from the places above $2p$, is finite flat at
   every $v\mid p$, and at every level place above $2$ has the ordered tame
   rank-one quotient obtained by restricting (11.1);
5. for every $v\nmid p$ outside the quaternionic level,
   $$
   \det r_B(\operatorname{Frob}_v)=N v,
   \qquad
   \operatorname{tr}r_B(\operatorname{Frob}_v)=\theta(T_v),       \tag{12.4a}
   $$
   with arithmetic Frobenius, together with the global determinant identity
   $\det r_B=\chi_p$; and
6. a $k$-algebra map $\iota:B\to\overline R$ and one matrix
   $C\in\operatorname{GL}_2(\overline R)$ such that
   $$
   \rho_{\overline R}(h)
   =C\,\iota(r_B(h))\,C^{-1}
   \qquad(h\in H).                       \tag{12.4b}
   $$

The word ``faithful'' in item 3 refers only to defining the Hecke order as
its image on the localized module.  It does not assert that the deformation
ring acts faithfully.  That latter assertion is a conclusion of the patched
comparison and is exactly what is needed to obtain (12.4b).

**Proposition 12.2 (arithmetic source implies scalar finiteness).**  A
Frey-special finite-image arithmetic source makes $\overline R$ a finite
$k$-algebra.  Consequently Proposition 12.1 makes $R^{\min}$ finite flat over
$W$ and produces the minimal characteristic-zero lift (12.5).

**Proof.**  Since $k$ is finite and $B$ is module-finite over $k$, the ring
$B$ is a finite set.  Hence $\operatorname{GL}_2(B)$ and the image of $r_B$
are finite.  Coefficient change and conjugation in (12.4b) preserve
finiteness, so $\rho_{\overline R}(H)$ is finite.  The subgroup $H$ has
finite index because $F/\mathbf Q$ is finite.  Thus
$\rho_{\overline R}(G_{\mathbf Q})$ is finite.  The roots-of-unity
integrality and topological trace-generation argument of Section 12.1 now
proves that $\overline R$ is finite.  Proposition 12.1 gives the remaining
claims. $\square$

A rational equality of generic fibers is insufficient.  The map in (12.4)
must be a map of integral local algebras; its support must contain the point
defined by (12.3); the localized cohomology module must be torsion free; and
the image of every degeneracy map used to reach $\mathcal D_F$ must be
saturated.  Otherwise a residual eigenclass can disappear when lifted to the
universal coefficient algebra.

### 12.4 Scalar, vexing, simultaneous, and coefficient-prime places

The exact nonminimal infrastructure needed for (12.4) can be stated without
abbreviations.

At a finite place $v\nmid p$ that is to be removed from an auxiliary
automorphic level, take the two integral degeneracy maps from hyperspecial to
Iwahori level.  Localize both source and target at the non-Eisenstein maximal
ideal defined by (12.2).  One must prove:

1. injectivity of the sum of the two degeneracy maps;
2. torsion-freeness of its cokernel over $W$;
3. compatibility of the adjoint composite with the two Frobenius roots;
4. identification of the monodromy quotient with the required local
   deformation component; and
5. support of the actual universal point, not merely a generic point on some
   component.

When residual Frobenius has distinct eigenvalues and
$N(v)\not\equiv\pm1\pmod p$, the two root projectors separate the branches.
The Frey-special theorem must also handle the cases in which Frobenius is
scalar, the roots collide, or $N(v)\equiv\pm1\pmod p$.  In those cases no
division by the root difference or by $N(v)^2-1$ is allowed.  The repair is
to retain the ordered eigenline as a framed flag, use the full Iwahori
old-space rather than one root quotient, and compute the integral
degeneracy Gram matrix on that flagged module.  Ihara injectivity controls
its kernel; the component-group sequence controls its cokernel; a Smith
normal-form calculation proves saturation before any specialization.  The
two branches are then separated by their normalized local deformation rings
and by the ordered monodromy quotient, not by an invertible numerical
difference.  This is the scalar and vexing part of the argument.

For several places, lowering one at a time is not enough unless saturation
survives every previous quotient.  Let $\Sigma$ be the full set of unwanted
places.  Form the $2^{|\Sigma|}$ cube of integral degeneracy modules, with one
hyperspecial/Iwahori choice at each place.  The alternating total complex is
the tensor product of the one-place two-term complexes.  The theorem must
prove that this total complex is exact after localization and that every
boundary has saturated image.  Equivalently, the intersection of the
old-space lattices equals the lattice in the intersection of their rational
spaces.  The commuting Hecke actions and ordered local projectors then show
that the result is independent of the order of lowering.  This is the
simultaneous part of the argument.

At a place above the coefficient prime $p$, an Iwahori degeneracy theorem
away from $p$ does not apply.  The target is the hyperspecial weight-two
finite-flat block.  Here one uses the integral model of the relevant modular
or Shimura curve, its finite-flat $p$-divisible group, and the
nearby-cycles/component sequence to compare the parahoric source with the
good-reduction target.  The closure and quotient results of Books 12, 14,
and 24 retain the coefficient action.  The finite-flat local deformation
ring of Lemma 11.2 maps to the completed integral Hecke order; the comparison
must prove that the localized target is torsion free, that the map is
saturated, and that its support contains the selected finite-flat component.
This is coefficient-prime level and weight lowering.  It is required even
when the generic representation is already crystalline, because the
automorphic source may have been constructed at parahoric level.

These four paragraphs are the concrete content of the packages customarily
called NM-I, NM-II, and NM-III:

- NM-I is the represented local ring, its ordered components, the
  Hecke-valued representation, and the determinant comparison;
- NM-II is integral level and type change with Ihara injectivity,
  component groups, and saturated images, including scalar and coefficient
  places;
- NM-III is the simultaneous patched support theorem showing that the
  localized module meets the same component tuple as the universal point.

There is no need to assume faithful support once the exact finite-level
modules have been constructed.  The direct equal-variable argument of Book
55 applies over $F$ without change.  We record the kernel-killing step because
it sharply separates formal patching from the arithmetic theorem still
needed here.

**Lemma 12.3 (balanced restricted auxiliary count).**  Let $F/\mathbf Q$ be
finite totally real, suppose that $p$ splits completely in $F$, and suppose
that $\overline\rho|_{G_F}$ remains absolutely irreducible, contains
$\operatorname{SL}_2(\mathbf F_p)$, and has no cyclotomic adjoint invariant.
Give it the restricted local conditions of Section 11.1.  If

$$
q_F=\dim_kH^1_{\mathcal L_F^\perp}
   (F,\operatorname{ad}^0\overline\rho(1)),
$$

then

$$
\dim_kH^1_{\mathcal L_F}
   (F,\operatorname{ad}^0\overline\rho)=q_F.           \tag{12.4i}
$$

For every $n\geq1$ there is a set $Q_n$ of exactly $q_F$ Taylor--Wiles
places with distinct residual Frobenius eigenvalues and
$N(v)\equiv1\pmod {p^n}$ which kills the dual Selmer group.  The resulting
absolute, unframed auxiliary deformation ring has tangent dimension exactly
$q_F$.

**Proof.**  Put $M=\operatorname{ad}^0\overline\rho$.  Absolute
irreducibility gives $H^0(F,M)=0$, and the adjoint hypothesis gives
$H^0(F,M(1))=0$.  The trace pairing identifies the Tate dual of $M$ with
$M(1)$.  The Greenberg--Wiles formula is therefore

$$
\begin{aligned}
\dim H^1_{\mathcal L_F}(F,M)
-\dim H^1_{\mathcal L_F^\perp}(F,M(1))
&=\sum_v\bigl(\dim L_v-\dim H^0(F_v,M)\bigr)\\
&=\sum_{v\mid p}[F_v:\mathbf Q_p]
  -\#\{v\mid\infty\}.                 \tag{12.4j}
\end{aligned}
$$

Here the unramified condition is neutral away from $2p$; the nonzero ordered
tame extension at $2$ has no unframed tangent direction and is neutral; the
finite-flat fixed-determinant condition contributes
$[F_v:\mathbf Q_p]$ beyond local invariants at $v\mid p$; and oddness
contributes $-1$ at each real place.  Both terms on the last line of
(12.4j) equal $[F:\mathbf Q]$, proving (12.4i).

For completeness, the assertion at $2$ is not only a dimension label.
Because $F_v=\mathbf Q_2$, the Kummer space of extension classes is
one-dimensional.  The fixed residual class is nonzero, so it spans that
space; every first-order change is a scalar multiple of it and is removed by
a strict diagonal conjugacy.  Thus its unframed tangent space and
$H^0(F_v,M)$ are both zero.

Choose a basis of the $q_F$-dimensional dual Selmer group.  Successively,
the large residual image supplies a regular semisimple conjugacy class on
which the next undetected class has nonzero localization.  Chebotarev,
applied also to the $p^n$th cyclotomic extension and to the fields used at
the preceding steps, realizes the classes at distinct places with
$N(v)\equiv1\pmod {p^n}$.  The resulting localization matrix is invertible,
so the ordered conditions at those $q_F$ places kill dual Selmer.  Each new
ordered local quotient is one-dimensional.  In the exact Poitou--Tate
comparison, their direct sum maps isomorphically to the old dual Selmer
dual; hence the new primal tangent dimension remains
$q_F+q_F-q_F=q_F$. $\square$

Apply the lemma to a field and local datum satisfying the arithmetic
assertions isolated in Theorem 12.4, and write

$$
q_F=\dim_kH^1_{\mathcal L_F^\perp}
   (F,\operatorname{ad}^0\overline\rho(1)).
$$

The restricted Euler calculation (12.4i) says that the primal Selmer space
has the same dimension $q_F$.  Lemma 12.3 gives a
Taylor--Wiles set $Q_n$ of exactly $q_F$ split regular places which kills the
displayed dual Selmer space.  In the localization sequence, the sum of the
$q_F$ one-dimensional auxiliary quotients maps isomorphically to the old
dual Selmer dual.  Hence the absolute unframed auxiliary tangent space still
has dimension exactly $q_F$, not $q_F$ plus a framing correction.  There are
therefore
surjections

$$
P=W[[X_1,\ldots,X_{q_F}]]\twoheadrightarrow R_{Q_n}.     \tag{12.4c}
$$

The diamond source has the same number of variables:

$$
S=W[[Z_1,\ldots,Z_{q_F}]]
\longrightarrow W[\Delta_{Q_n}],
\qquad
\Delta_{Q_n}\simeq(\mathbf Z/p^n\mathbf Z)^{q_F}.       \tag{12.4d}
$$

Suppose now that the explicit quaternionic construction described above has
proved that its localized module $M_{Q_n}$ is free of a fixed positive rank
over $W[\Delta_{Q_n}]$, that module and faithful Hecke-order augmentation are
exact, and that the Hecke-valued representation gives the displayed
$R_{Q_n}$-action.  At precision $d$, define the ring shadow independently of
the action image:

$$
R_{n,d}
=R_{Q_n}/\mathfrak m_{R_{Q_n}}^{\nu(d)}
=P/(\ker(P\to R_{Q_n})+\mathfrak m_P^{\nu(d)}),         \tag{12.4e}
$$

where $\nu(d)$ is increasing and cofinal.  Separately record the image of
$P$ in the endomorphisms of the finite module shadow.  Record in the same
finite diagram the diamond coordinates, the action matrices, and the exact
ring, module, and Hecke-order augmentations.  Every marked set at fixed
precision is finite.  A diagonal subsequence therefore has compatible
shadows, and inverse limits give

$$
P\longrightarrow R_\infty\longrightarrow
A_\infty\subseteq\operatorname{End}_S(M_\infty),
\qquad
M_\infty\simeq S^r,                     \tag{12.4f}
$$

with $r>0$, together with a local map $\alpha:S\to P$ whose composite with
the action is scalar multiplication.  Retaining (12.4e), rather than using
the faithful action image as the ring shadow, is essential: otherwise the
kernel one is trying to kill has already been discarded before the limit is
taken.

Put $A=\operatorname{im}(P\to\operatorname{End}_S(S^r))$.  It is finite over
$S$.  Scalar multiplication on the nonzero free $S$-module is faithful, so
$S\hookrightarrow A$.  Therefore

$$
\dim A=\dim S=q_F+1.                    \tag{12.4g}
$$

The ring $P$ is a regular domain of the same dimension.  If the kernel of
$P\twoheadrightarrow A$ contained a nonzero element, its quotient would
have dimension at most $q_F$, contradicting (12.4g).  Thus the action of
$P$ is injective.  Since it factors through $R_\infty=P/I_\infty$, one gets

$$
I_\infty=0,
\qquad R_\infty=P=A.                    \tag{12.4h}
$$

Moreover $P$ is finite over the regular ring $S$.  Depth is $q_F+1$ on both
sides: the maximal ideal of $S$ extends to an ideal with radical
$\mathfrak m_P$, so a parameter sequence of $S$ is also a parameter
sequence of the Cohen--Macaulay ring $P$ and is $P$-regular.  The same
sequence is regular on $M_\infty$ because that module is free over $S$.
Auslander--Buchsbaum first makes $P$ free over $S$ and then makes
$M_\infty$ free over $P$.  Exact augmentation, retained in the finite
shadows, now descends this faithful action to the minimal module.  Since the
minimal Hecke order is faithful on that module by its definition as an image,
the canonical map from the universal ring has zero kernel.  It is
surjective because absolute irreducibility gives topological generation by
unramified Frobenius traces and those traces map to the Hecke generators.
Thus

$$
R_F^{\mathcal D}\twoheadrightarrow\mathbb T_F^{\mathcal D}
$$

is an isomorphism.  This proves the required integral factorization (12.4)
from the finite-level arithmetic statements; it does not assume Hecke
faithfulness for the deformation ring, component coverage, or an equality of
generic fibers.

Books 55, 56, and 60 explain this infrastructure but do not prove every one
of these Frey-special scalar, vexing, and coefficient-prime cases.  Books
30--32 prove the patching algebra once the arithmetic modules, maps,
saturation, and support statements have been supplied.  Thus (12.4) remains
part of the single theorem isolated in Section 13.5.

### 12.5 The first irreducible arithmetic lemma

The discussion above separates a proved commutative-algebra argument from
the first unavailable arithmetic input.  Here is that input in a form which
cannot conceal residual automorphy, integral level lowering, or support
inside a package name.

**Theorem 12.4 (Frey-special integral automorphic finite shadows; missing).**
Let $p\geq5$ and let $\overline\rho$ satisfy clauses 1--4 of Theorem 13.1.
For the scalar-reduced universal minimal representation (12.1), there exist
the following objects, constructed from those four hypotheses alone.

1. There is a finite totally real extension $F/\mathbf Q$, split completely
   at $2$ and $p$ and disjoint from the fields cut out by
   $\overline\rho$, $\overline\chi_p$, and their nontrivial self-twists.
   In particular, restriction still contains
   $\operatorname{SL}_2(\mathbf F_p)$ and has no cyclotomic adjoint
   invariant.
2. There are a totally definite quaternion algebra $D/F$, a weight-two
   level $U$ whose nonhyperspecial finite factors lie only above $2$, and a
   non-Eisenstein maximal ideal $\mathfrak m$ of the integral Hecke order on
   $M(U,W)$.  The residual representation at $\mathfrak m$ is
   $\overline\rho|_{G_F}$, with the prescribed ordered tame quotient at
   every $v\mid2$ and the finite-flat component at every $v\mid p$.  This
   clause includes the construction of the auxiliary two-prime moduli
   point, the automorphy of its auxiliary-prime member, and the switch back
   to the $p$-torsion member; it is not an assumption of residual
   automorphy.
3. With $q_F$ and $Q_n$ supplied by Lemma 12.3, there are localized
   definite-quaternion modules $M_{Q_n}$, of one fixed positive rank over
   $W[\Delta_{Q_n}]$, and faithful Hecke orders $\mathbb T_{Q_n}$ acting on
   them, where
   $$
   \Delta_{Q_n}=\prod_{v\in Q_n}\Delta_v,
   $$
   and $\Delta_{Q_n}\simeq(\mathbf Z/p^n\mathbf Z)^{q_F}$.  Each module is
   finite free over $W$ and free over its diamond algebra.  The Hecke order
   carries a
   genuine representation with cyclotomic determinant, Frobenius trace
   $T_v$ and determinant $Nv$ away from the level, finite-flat local
   condition at every $v\mid p$, the ordered tame rank-one quotient at every
   $v\mid2$, and the declared ordered characters at $Q_n$.
4. At every auxiliary, unwanted, scalar, vexing, or coefficient-prime level
   place, the two degeneracy maps and their adjoints are integral.  For the
   full set $\Sigma$ of places changed in reaching $U$, the
   $2^{|\Sigma|}$ degeneracy cube is exact after localization and every
   boundary has saturated image.  Its component-group quotients identify
   the ordered local deformation components, including collided Frobenius
   roots and $N(v)\equiv\pm1\pmod p$, without dividing by a root difference.
   The coefficient-prime face lands on the finite-flat component.  These
   statements hold also for $p=5$ and $p=7$.
5. The augmentation $Q_n\mapsto\varnothing$ gives exact ring, module, and
   faithful-Hecke-order sequences.  At every precision $d$ these sequences,
   the diamond coordinates, the deformation maps, and the action matrices
   form finite marked diagrams with a cofinal choice of $\nu(d)$.  Thus the
   inverse-limit construction uses the deformation shadows (12.4e), not
   quotients by the kernels of the module actions.

These data produce a Frey-special finite-image arithmetic source in the
sense of Section 12.3.  In particular, if
$R_F^{\mathcal D}$ is the restricted universal minimal ring, then

$$
R_F^{\mathcal D}\simeq\mathbb T(U)_{\mathfrak m},       \tag{12.4k}
$$

and the restriction map $R_F^{\mathcal D}\to\overline R$ factors through a
finite local $k$-algebra $B$.  After one strict conjugacy, the universal
representation satisfies (12.4b), with all the local and Frobenius
compatibilities in (12.4a).

The conclusion follows from the five clauses without another arithmetic
hypothesis.  Lemma 12.3 gives the equal $q_F$-variable deformation sources,
and clauses 3--5 give the exact finite shadows required in (12.4e).  The
dimension argument (12.4f)--(12.4h) kills the patched kernel and descends
faithfulness.  Absolute irreducibility makes the restricted
universal ring topologically generated by unramified Frobenius traces; those
traces map to the Hecke generators.  Hence the resulting map to the
faithful Hecke order is surjective as well as injective, proving (12.4k).
Reducing (12.4k) modulo $p$ and taking the image in $\overline R$ gives
$B$ and the factorization.

What is missing is the proof of clauses 1--5.  The preceding books
prove the deformation theory, the prime-selection mechanism once the image
and disjointness are retained, and the equal-variable patching implication.
They do not construct the residual automorphic maximal ideal over $F$, nor
the integral Hilbert or quaternionic modules with the saturated simultaneous
degeneracy and coefficient-prime comparison asserted here.  In particular,
a single automorphic point, a generic-fiber equality, or support on one
component would not imply (12.4b).  Theorem 12.4 is therefore the first
irreducible missing lemma in the finite-image half of Theorem 13.1.

### 12.6 Extracting the characteristic-zero lift

Once $\overline R$ is finite, the passage to a lift is elementary and
unconditional.

**Proposition 12.1 (finite scalar reduction gives a finite-flat ring and a
minimal lift).**  If $R^{\min}/pR^{\min}$ is finite over $k$, then
$R^{\min}$ is a nonzero finite free, hence finite flat, $W$-algebra.  There is
also a finite extension $E_p/\mathbf Q_p$, with valuation ring
$\mathcal O_p$, and a minimal hardly ramified representation

$$
\rho_p:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathcal O_p)        \tag{12.5}
$$

whose reduction is isomorphic to
$\overline\rho\otimes_k k_p$, where $k_p$ is the residue field of
$\mathcal O_p$.

**Proof.**  We first prove the assertion about the whole universal ring.  It
is not enough to choose one characteristic-zero branch; flatness of
$R^{\min}$ is a stronger conclusion and is what the arithmetic lifting
argument actually supplies.

Write

$$
S=W[[X_1,\ldots,X_g]],
\qquad I=(f_1,\ldots,f_r),
\qquad R^{\min}=S/I,
$$

with $r\leq g$ as in (11.9).  The regular local ring $S$ has dimension
$g+1$.  The generalized principal ideal theorem gives

$$
\dim R^{\min}\geq
1+g-r\geq1.                              \tag{12.6}
$$

On the other hand, $R^{\min}/pR^{\min}$ is Artinian, so it has dimension
zero.  The dimension inequality for quotient by one element gives

$$
\dim R^{\min}\leq
\dim R^{\min}/pR^{\min}+1=1.
$$

Thus equality holds throughout (12.6):

$$
\dim R^{\min}=1,
\qquad r=g.                              \tag{12.6a}
$$

Equivalently, the ideal generated in $S$ by

$$
f_1,\ldots,f_g,p
$$

has radical the maximal ideal of $S$ and is generated by exactly
$\dim S=g+1$ elements.  A power-series ring over a DVR is Cohen--Macaulay,
so every such system of parameters is a regular sequence.  In particular

$$
f_1,\ldots,f_g,p
\text{ is an }S\text{-regular sequence}.                \tag{12.6b}
$$

After first quotienting by $f_1,\ldots,f_g$, equation (12.6b) says that
multiplication by $p$ on $R^{\min}$ is injective.  This is the regularity
which a mere dimension lower bound would not have supplied.

We next prove module finiteness.  Since $R^{\min}/pR^{\min}$ is a finite
ring, choose one lift in $R^{\min}$ of each of its elements and let $N$ be
their $W$-span.  Then

$$
R^{\min}=N+pR^{\min}.                    \tag{12.6c}
$$

Here is the convergence hidden in the usual phrase ``topological
Nakayama.''  Finiteness modulo $p$ gives an integer $a$ with

$$
\mathfrak m_{R^{\min}}^a\subseteq pR^{\min}.
$$

Therefore the maximal-ideal and $p$-adic topologies on $R^{\min}$ are
cofinal.  Iterating (12.6c), every $x\in R^{\min}$ admits, for every $n$, an
expression

$$
x=n_0+pn_1+\cdots+p^{n-1}n_{n-1}+p^nx_n,
\qquad n_i\in N.                         \tag{12.6d}
$$

Choose the lifts defining $N$ from a finite $k$-basis rather than from all
elements if desired.  The coefficients of the partial sums in (12.6d) are
Cauchy in the complete DVR $W$, and cofinality makes the remainder tend to
zero in $R^{\min}$.  Their limits express $x$ as a $W$-linear combination of
the finitely many chosen lifts.  Hence $R^{\min}$ is finite over $W$.

We have shown that $R^{\min}$ is a finite torsion-free $W$-module.  A finite
torsion-free module over a DVR is free.  It is nonzero because it is a local
ring with residue field $k$.  Thus

$$
\boxed{R^{\min}\text{ is finite free, and hence finite flat, over }W.}
\tag{12.6e}
$$

It remains to extract a field-valued point.  Inverting $p$ in the nonzero
free module gives a nonzero finite-dimensional $\mathbf Q_p$-algebra
$R^{\min}[1/p]$.  Choose a maximal ideal of this algebra and let $E_p$ be
the resulting residue field.  It is a finite extension of $\mathbf Q_p$.
Every element of $R^{\min}$ is integral over $W$, so its image in $E_p$
lies in the valuation ring $\mathcal O_p$.  We obtain a local homomorphism

$$
R^{\min}\longrightarrow\mathcal O_p.                   \tag{12.6f}
$$

The contraction of the maximal ideal of $\mathcal O_p$ contains $p$; since
$R^{\min}/pR^{\min}$ is Artinian local, that contraction is the unique
maximal ideal of $R^{\min}$.  Thus (12.6f) induces an embedding of $k$ into
the residue field of $\mathcal O_p$.  Composing the universal representation (11.3) with
(12.6f) gives (12.5).  Each defining local condition is stable under this
coefficient change: the determinant remains cyclotomic, odd-prime
unramifiedness remains unramifiedness, the ordered tame-quadratic quotient at
$2$ base changes as a free rank-one quotient, and the levelwise finite-flat
models at $p$ base change with their coefficient actions.  Reducing (12.5)
therefore gives $\overline\rho$ after the displayed residue-field extension,
which is the customary meaning of lifting the fixed residual
representation. $\square$

Notice the direction of the argument:

$$
\text{potential modularity and integral lifting over }F
\Longrightarrow
R^{\min}/p\text{ finite}
\Longrightarrow
\text{a minimal lift over }\mathbf Q.    \tag{12.7}
$$

There is no automorphic descent from $F$ to $\mathbf Q$ in (12.7).

## 13. Spreading the lift and changing the prime

A single $p$-adic lift still cannot be fed into Book 66.  It must be spread
into an effective compatible system, and then the coefficient prime must be
changed to $3$.  This is a second use of potential modularity and modularity
lifting.  It is logically distinct from the finiteness use in Chapter 12.

### 13.1 An admissible top field

Apply a strengthened two-prime potential-modularity construction to
$\rho_p$.  The required output is a finite Galois totally real extension

$$
M/\mathbf Q                                      \tag{13.1}
$$

such that:

- the rational primes $2$, $p$, and $3$ split completely in $M$, and all
  local moduli data above $3$ are hyperspecial;
- $M$ is disjoint from the residual, cyclotomic, self-twist, and coefficient
  fields used in the construction;
- $\rho_p|_{G_M}$ remains absolutely irreducible;
- it is attached to a named parallel-weight-two cuspidal automorphic
  representation $\Pi_M$;
- the equality includes determinant, polarization, the ordered special
  parameter above $2$, and finite-flat components above $p$.

One cannot obtain these statements merely by taking the normal closure of
the arbitrary field $F$ in Section 12.2.  Automorphy need not base change
through the nonsolvable extension from $F$ to that closure, and the closure
can meet the avoidance fields.  The Galois field (13.1) must be built as an
output of the potential-modularity theorem, or potential modularity must be
rerun on a moduli problem whose specialization already has that property.
This effectivity requirement is included in the missing theorem below.

Book 54 attaches to $\Pi_M$ a compatible system
$\mathcal R_M=\{R_{\mu,M}\}$.  Its common polynomials are pure of weight one.
At the distinguished place above $p$, Chebotarev and absolute
irreducibility identify

$$
R_{\mu_p,M}\simeq\rho_p|_{G_M}.           \tag{13.2}
$$

### 13.2 Brauer induction without automorphic descent to $\mathbf Q$

Put $G=\operatorname{Gal}(M/\mathbf Q)$.  Choose an integral Brauer identity

$$
\mathbf1_G
=
\sum_i n_i\operatorname{Ind}_{H_i}^G\theta_i,            \tag{13.3}
$$

where each $H_i$ is elementary, each $\theta_i$ is one-dimensional, and the
integers $n_i$ may be negative.  Let $F_i=M^{H_i}$.  The upper extension

$$
M/F_i
$$

is solvable even when $F_i/\mathbf Q$ is not.  Cyclic automorphic descent,
one layer at a time, descends $\Pi_M$ to an automorphic representation
$\Pi_i$ over $F_i$, after twisting by the character selected by
$\rho_p|_{G_{F_i}}$.  Cuspidality, absence of a new self-twist, determinant,
and the ordered local types must be checked at every layer.

Attach compatible systems $\mathcal R_i$ to the $\Pi_i$.  For every coefficient
place $\mu$, Brauer induction gives the virtual class

$$
\mathcal V_\mu
=
\sum_i n_i
\left[
\operatorname{Ind}_{G_{F_i}}^{G_{\mathbf Q}}
(R_{i,\mu}\otimes\theta_{i,\mu})
\right].                                 \tag{13.4}
$$

At $\mu_p$, the projection formula and the normalization by $\rho_p$ give

$$
\mathcal V_{\mu_p}=[\rho_p].              \tag{13.5}
$$

Equation (13.4) is not yet a representation when some $n_i$ is negative.
Its positive virtual rank and its polynomial-looking Frobenius factors do not
make it effective.  This is exactly why no automorphic descent to
$\mathbf Q$ is being smuggled into the argument.

### 13.3 Descent cocycles and effectivity

For each $\mu$, conjugation by $g\in G$ carries $R_{\mu,M}$ to an isomorphic
representation.  Choose intertwiners $A_{g,\mu}$.  With a section
$s:G\to G_{\mathbf Q}$ and factor
$c(g,h)=s(g)s(h)s(gh)^{-1}\in G_M$, the intertwiners must satisfy

$$
A_{g,\mu}R_{\mu,M}(x)A_{g,\mu}^{-1}
=
R_{\mu,M}(s(g)xs(g)^{-1})                 \tag{13.6}
$$

and

$$
A_{g,\mu}A_{h,\mu}
=
R_{\mu,M}(c(g,h))A_{gh,\mu}.              \tag{13.7}
$$

Arbitrary intertwiners satisfy (13.7) only up to a scalar $2$-cocycle.
The values of that cocycle lie, after one coefficient enlargement, among
roots of unity.  At the distinguished $p$-adic place, the actual
representation $\rho_p$ supplies intertwiners satisfying (13.7) exactly.
To carry this vanishing to every $\mu$, the Hecke correspondences and
multiplicity-one lines must show that all scalar cocycles are images of one
algebraic cocycle.  An embedding of a number field cannot send a nontrivial
root of unity to $1$, so the common algebraic cocycle then vanishes.

There is a second cocycle.  If $K/K_0$ is a coefficient-field extension,
the isomorphisms between coefficient conjugates of the system have a factor
set in

$$
H^2(\operatorname{Gal}(K/K_0),K^\times).                 \tag{13.8}
$$

Good-prime traces in $K_0$ do not kill this relative Brauer class.  The
integral Hecke eigensummands must provide coherent coefficient descent, or
the theorem must retain the larger field $K$ and prove that every completion
used below is a genuine $K$-model.  Self-twist ambiguity is normalized by
the distinguished member, the determinant, and the ordered quotient at $2$.

Once (13.6)--(13.8) are coherent, define

$$
\rho_\mu(xs(g))=
R_{\mu,M}(x)A_{g,\mu}.                    \tag{13.9}
$$

This is an actual continuous representation of $G_{\mathbf Q}$.  The Brauer
identity proves that its good Frobenius traces and determinants are algebraic
and independent of $\mu$.  Conversely, Chebotarev shows that (13.9) is the
unique semisimple effective object represented by (13.4), with the chosen
twist normalization.  This constructs a compatible system over
$\mathbf Q$ without asserting that any $\rho_\mu$ is automorphic over
$\mathbf Q$.

### 13.4 The local record in the effective system

The descent construction must carry more than good-prime traces.

At every odd base prime $q$ away from the characteristic of $\mu$, the
minimal lift is unramified.  Local--global compatibility for each Brauer
term and (13.9) therefore give an unramified $\rho_\mu$.  At $2$, the
ordered local component gives a rational exact sequence

$$
0\longrightarrow
K_\mu(1)\otimes\eta_2
\longrightarrow V_\mu
\longrightarrow K_\mu\otimes\eta_2
\longrightarrow0,                       \tag{13.10}
$$

where $\eta_2$ is unramified and $\eta_2^2=1$.  The ordering is part of the
descent datum; equality of unramified Frobenius traces away from $2$ would
not recover it.  Its Weil--Deligne monodromy has rank one.  Hence the common
base-prime conductor is exactly $2$, although the extension class of a
particular integral reduction may vanish.

At coefficient places of odd characteristic, the automorphic geometric
realizations have weights $\{0,1\}$.  The common polynomial at an odd good
prime $q$ is

$$
P_q(X)=X^2-a_qX+q\in K[X],                \tag{13.11}
$$

and the system is pure of weight one.  The member at the distinguished
place above $p$ is (12.5), after a common finite coefficient extension.
This equality fixes the character ambiguity in (13.9).

For the place above $3$, more integral information is required.  The
Brauer construction is arranged with hyperspecial level above $3$.
The positive terms in (13.4) are realized in the $3$-adic Tate modules of
products of modular or Shimura Jacobians with good reduction at $3$, after
Weil restriction.  Finite-order twists are realized by passing to the
kernel field and applying the corresponding rational character projector.
Because $3$ splits completely in $M$ and every intermediate field, these
Jacobians extend at all places above $3$ and their Weil restrictions extend
to abelian schemes over $\mathbf Z_3$.  The character projectors need only be
rational: denominators change the lattice but not the rational embedding
used below.
Move the negative terms to the other side of (13.4).  Semisimplicity then
gives

$$
V_3\oplus N_3\simeq P_3,                 \tag{13.12}
$$

where $P_3$ is a positive direct sum of those geometric representations.
Thus there is an abelian scheme $\mathcal A/\mathbf Z_3$ and a rational
$G_{\mathbf Q_3}$-equivariant embedding

$$
V_3\hookrightarrow V_3(\mathcal A).      \tag{13.13}
$$

Chapter 14 proves that (13.13), rather than an unspecified crystalline
label, supplies the all-level finite-flat lattice certificate required by
Book 66.

### 13.5 The single missing arithmetic theorem

All unresolved global work can now be stated as one theorem.  Its statement
is specialized to the only residual representations needed here, so none of
the scalar, small-prime, or coefficient-prime cases can be excluded by a
genericity hypothesis.

**Theorem 13.1 (Frey-special minimal lift and effective spread; missing).**
Let $p\geq5$ and let

$$
\overline\rho:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbf F_p)
$$

satisfy all of the following.

1. It is odd and absolutely irreducible, with
   $\det\overline\rho=\overline\chi_p$.
2. It is unramified at every odd prime $q\neq p$.
3. At $2$ it has (11.1), the quotient character is unramified of square one,
   and the tame extension class is nonzero.
4. At $p$ it has a finite-flat model over $\mathbf Z_p$.

Then:

1. the universal minimal ring of Section 11.1 has finite scalar reduction
   and is a nonzero finite free, hence finite flat, $W$-algebra; hence
   Proposition 12.1 gives a minimal lift $\rho_p$;
2. there are a number field $K$, a place $\lambda_p\mid p$, and a semisimple
   rank-two compatible system
   $\mathcal R=\{\rho_\lambda\}_{\lambda\nmid2}$ over $\mathbf Q$ whose
   $\lambda_p$-member is $\rho_p$ after a common scalar extension;
3. every member has cyclotomic determinant and is odd, is unramified at
   every odd $q$ different from its coefficient characteristic, has the
   ordered rank-one-monodromy local sequence (13.10) at $2$, and has labelled
   weights $\{0,1\}$ at its coefficient prime; equivalently, the compatible
   system has exact common level $2$; at every odd coefficient place it has
   a stable lattice whose finite quotients are levelwise finite flat;
4. its common polynomials are (13.11), and the system is pure of weight one;
5. for some place $\lambda_3\mid3$, the representation $V_3$ admits the
   geometric embedding (13.13) into the Tate module of an abelian scheme
   over $\mathbf Z_3$.

The theorem includes, rather than assumes, the following arithmetic
construction.

- It produces residual automorphy over a named totally real field from an
  actual lifting-admissible two-prime moduli datum, with all determinant,
  polarization, connectedness, local-open, avoidance, and cuspidality
  clauses proved.
- It proves the integral modularity-lifting factorization (12.4) on the
  exact local component.  This includes the local Hecke-valued
  representations, Ihara injectivity, component-group comparison,
  saturation, multiplicity one, patched support, and determinant comparison.
- It treats simultaneously all scalar Frobenius, vexing congruence,
  $p=5$, $p=7$, multi-prime, and coefficient-prime finite-flat lowering
  branches described in Section 12.4.
- It constructs an admissible Galois top field rather than silently taking a
  normal closure, carries out the solvable descents over the fields
  $M^{H_i}$, and proves the base-field and coefficient-field cocycle
  equalities (13.6)--(13.8).
- It proves effectivity of the Brauer class at every coefficient place,
  descends the stable lattices and their finite-flat witnesses, transports
  the ordered parameter at $2$, and supplies the stronger good-reduction
  geometric realization at $3$ used in (13.13).

The first conclusion has the exact proof chain

$$
\text{Theorem 12.4}
\Longrightarrow\text{Proposition 12.2}
\Longrightarrow\text{Proposition 12.1}.                \tag{13.14}
$$

Thus its only unproved input is the finite-shadow arithmetic construction;
the passage from that construction to finite scalar reduction, finite
flatness of the whole universal ring, and a characteristic-zero minimal lift
is proved in Chapter 12.

Theorem 13.1 is not a reformulation of the four gaps in the former draft.
It is the one construction whose proof closes them together.  The
scalar/vexing work is needed for the Hecke factorization that proves ring
finiteness; the Galois and cocycle work is needed for effective spreading;
and the integral geometric output at $3$ is built from the same Brauer
summands.  None can be removed while retaining the stated conclusion.

The available books do not prove Theorem 13.1.  In particular, Book 55 starts
with a residual automorphic maximal ideal, Book 56 leaves the nonminimal
arithmetic infrastructure as hypotheses, Book 60 leaves its
lifting-admissible realization and nonminimal packages as hypotheses, and
Book 62 makes effectivity conditional on a coherent cocycle or determinant
package.  Treating their conclusions as though these hypotheses had already
been verified would be circular.

## 14. Finite-flat lattices from good reduction

The final integral issue at $3$ can be closed without asking for a compatible
tower of finite-flat group schemes.  The following lemma is stronger than
what Book 66 needs: every stable lattice in the rational summand works.

### 14.1 The intersection-and-closure lemma

**Theorem 14.1 (every lattice in a good-reduction summand is levelwise finite
flat).**  Let $E/\mathbf Q_3$ be finite, let $\mathcal O$ be its valuation
ring with uniformizer $\varpi$, and let $W$ be a finite-dimensional
$E$-linear representation of $G_{\mathbf Q_3}$.  Suppose there is a rational
$G_{\mathbf Q_3}$-equivariant embedding

$$
\iota:W\hookrightarrow V_3(\mathcal A)
$$

for an abelian scheme $\mathcal A/\mathbf Z_3$.  Then for every
$G_{\mathbf Q_3}$-stable $\mathcal O$-lattice $T\subset W$ and every
$n\geq1$, the finite $(\mathcal O/\varpi^n)[G_{\mathbf Q_3}]$-module

$$
T/\varpi^nT
$$

has a finite-flat model over $\mathbf Z_3$ with its
$\mathcal O/\varpi^n$-action.

Only levelwise existence is asserted.

**Proof.**  Identify $W$ with its image and put

$$
S=W\cap T_3(\mathcal A)
\subset V_3(\mathcal A).                 \tag{14.1}
$$

Viewed as a $\mathbf Z_3$-module, $S$ is a full lattice in the underlying
$\mathbf Q_3$-space of $W$.  It is stable under $G_{\mathbf Q_3}$.  It is
also $3$-saturated in $T_3(\mathcal A)$: if
$x\in T_3(\mathcal A)$ and $3^rx\in S$, then $3^rx\in W$ implies
$x\in W$, hence $x\in S$.  Therefore

$$
S/3^rS\hookrightarrow
T_3(\mathcal A)/3^rT_3(\mathcal A)
=\mathcal A[3^r](\overline{\mathbf Q}_3) \tag{14.2}
$$

is injective for every $r$.

The lattice $S$ need not be stable under $\mathcal O$, because the rational
$E$-action on $W$ need not preserve the ambient Tate lattice.  No such
stability is used: the nested modules below are built from the
$\mathcal O$-stable lattice $T$, while $S$ supplies only a common
$\mathbf Z_3$-integral ambient torsion group.

The $\mathbf Z_3$-lattices $S$ and $T$ are commensurable.  Choose $a\geq0$
with

$$
3^aT\subseteq S.
$$

For the fixed $n$, choose $r$ sufficiently large that

$$
3^rS\subseteq3^a\varpi^nT.               \tag{14.3}
$$

Inside the generic points in (14.2) there are nested stable subgroups

$$
\frac{3^a\varpi^nT}{3^rS}
\subseteq
\frac{3^aT}{3^rS}
\subseteq
\frac{S}{3^rS}.                          \tag{14.4}
$$

The torsion group $\mathcal A[3^r]$ is finite flat over $\mathbf Z_3$.
Take the saturated schematic closures of the three generic subgroups in
$\mathcal A[3^r]$.  The closure theorem of Book 12 makes them finite flat;
over a DVR its contracted Hopf ideals are saturated, and inclusion of generic
subgroups gives inclusion of their closures.
The quotient of the middle closure by the first is represented and finite
flat.  Its generic points are

$$
\frac{3^aT/3^rS}{3^a\varpi^nT/3^rS}
\simeq
\frac{3^aT}{3^a\varpi^nT}
\simeq
T/\varpi^nT.                             \tag{14.5}
$$

Thus the underlying finite abelian Galois module has a finite-flat model.

It remains to install the coefficient action.  Put
$\Lambda=\mathcal O/\varpi^n$ and choose $m$ with $3^m\Lambda=0$.  Starting
from the finite-flat model of the underlying $\mathbf Z/3^m$-module, take a
finite product corresponding to a presentation of the additive
$\mathbf Z/3^m$-module $\Lambda$.  On generic points, the map

$$
\Lambda\otimes_{\mathbf Z/3^m}
(T/\varpi^nT)\longrightarrow T/\varpi^nT,
\qquad b\otimes x\longmapsto bx           \tag{14.6}
$$

is surjective.  Close its generic kernel in the product model and take the
represented quotient.  Book 14's subquotient theorem makes the quotient
finite flat.  Multiplication by every $b\in\Lambda$ preserves the generic
kernel, so it preserves its closure.  The resulting endomorphisms descend
to the quotient.  Addition, multiplication, zero, and unit identities hold
on the generic fiber and hence everywhere by flatness.  This gives the
required $\Lambda$-linear model.

The choices of $a$, $r$, presentations, closures, and quotient models may
depend on $n$.  No transition map between the models for $n$ and $n+1$ has
been constructed or used. $\square$

### 14.2 Why the arbitrary-lattice statement matters

A rational direct summand of an abelian Tate module need not meet the
ambient Tate lattice in the lattice selected globally.  Theorem 14.1 avoids
having to compare those lattices.  One first chooses any stable
$\mathcal O$-lattice required by the global compatible system; commensurability
with (14.1) and the two nested closures in (14.4) then produce the desired
model at each level.

It is not enough to close only $T/\varpi^nT$ in an ambient torsion group
without first choosing a common $3^r$-torsion level.  Nor is it enough to
say that subquotients of finite-flat representations are finite flat without
displaying an ambient model.  Equations (14.2)--(14.4) supply exactly that
ambient model and prove the necessary saturation.

### 14.3 Application to the prime-switched member

Assume the arithmetic output of Theorem 13.1.  Choose the place
$\lambda_3\mid3$, let $E=K_{\lambda_3}$, and write
$V_3=\rho_{\lambda_3}$.  The geometric construction in Section 13.4 gives
an embedding

$$
V_3\hookrightarrow V_3(\mathcal A)
$$

with $\mathcal A/\mathbf Z_3$ an abelian scheme.  A stable
$\mathcal O_E$-lattice $T_3\subset V_3$ exists because the image is compact.
Theorem 14.1 now gives, for every $n\geq1$, a finite-flat
$\mathcal O_E/\varpi_3^n$-model of

$$
T_3/\varpi_3^nT_3.                       \tag{14.7}
$$

This proves the fourth hypothesis of Book 66, Theorem 18.6.  It is no longer
a separate bridge assumption.

## 15. The fixed-$3$ member and the contradiction

The last step uses the exact prime-$2$ theorem of Book 66.  It is important
to transport the rational ordered line to the chosen lattice before invoking
that theorem.

### 15.1 The integral filtration at two

Restrict (13.10) to the place $\lambda_3$.  Let $V_3^+$ be its first
one-dimensional subspace and put

$$
T_3^+=T_3\cap V_3^+.
$$

This intersection is saturated in $T_3$.  Indeed, if
$\varpi_3x\in T_3^+$ for $x\in T_3$, then
$\varpi_3x\in V_3^+$ and hence $x\in V_3^+$.  Thus
$T_3/T_3^+$ is torsion free.  Both $T_3^+$ and the quotient are free of rank
one, and restriction to $G_{\mathbf Q_2}$ gives the exact sequence

$$
0\longrightarrow
\mathcal O_E(1)\otimes\eta_2
\longrightarrow T_3
\longrightarrow\mathcal O_E\otimes\eta_2
\longrightarrow0.                       \tag{15.1}
$$

The quotient character is unramified and $\eta_2^2=1$.  This argument does
not assert that the integral extension class is a unit.  Book 66 permits
both trivial residual inertia and tame cyclic inertia of order $3$.

### 15.2 The complete Book 66 ledger

The member $V_3$ and lattice $T_3$ satisfy the five hypotheses of Book 66,
Theorem 18.6, as follows.

1. The determinant is $\chi_3$ and the representation is odd by Theorem
   13.1.
2. It is unramified at every odd prime different from $3$, because the
   minimal compatible system has common bad set $\{2\}$.
3. Equation (15.1) is the required exact local sequence at $2$, including
   the ordered free quotient and the equation $\eta_2^2=1$.
4. Equation (14.7) supplies a finite-flat model at every uniformizer level,
   with its coefficient action.
5. Equation (13.11) gives the common polynomial
   $X^2-a_qX+q$ at every $q\notin\{2,3\}$, and the system is pure of weight
   one.

No irreducibility of the residual $3$-adic member is required.  No claim is
made that the prime-$2$ extension splits.  No residue-degree-one hypothesis
is imposed on $\lambda_3$.

Book 66, Theorem 18.4 first gives

$$
\operatorname{tr}\rho_{\lambda_3}(g)
=
1+\chi_3(g)
\qquad(g\in G_{\mathbf Q}),              \tag{15.2}
$$

and an integral extension of the trivial character by the cyclotomic
character whose class is a coefficient multiple of the Kummer class of
$2$.  Semisimplicity would split the rational extension, but the trace
identity alone is enough here.

### 15.3 Purity at five

The prime $5$ is good for the minimal system even if it was bad for the
original Frey curve.  Evaluating (15.2) at arithmetic Frobenius gives

$$
a_5=1+5=6.                               \tag{15.3}
$$

This equality holds first in $K_{\lambda_3}$.  Both sides come from the
common algebraic coefficient field, and the embedding of that field into
its completion is injective, so (15.3) is an equality in $K$.

Purity of weight one says that the two complex roots of

$$
X^2-a_5X+5
$$

have absolute value $\sqrt5$.  Hence

$$
|a_5|\leq2\sqrt5.                        \tag{15.4}
$$

But $6>2\sqrt5$.  Therefore the compatible system asserted by Theorem 13.1
cannot exist.

This contradiction uses, in order, modularity lifting to make the minimal
deformation ring finite, potential modularity to supply both that
factorization and the top automorphic system, compatible systems and Brauer
effectivity to spread back to $\mathbf Q$, changing the coefficient prime
to $3$, the geometric lattice theorem of Chapter 14, and Book 66's
hardly-ramified classification.  It does not stop at a dimension computation
for classical forms of level $2$.

## 16. Final assembly and dependency status

The Diophantine and local parts of the argument are unconditional.  The
global construction has been reduced to the single exact theorem in Section
13.5.  We now record both the mathematical assembly and the honest status of
that theorem.

### 16.1 Prime exponents

Suppose that

$$
a^p+b^p=c^p
$$

is a primitive nonzero solution with prime $p\geq5$, normalized as in Chapter
3.  Its Frey representation $\overline\rho_{E,p}$ satisfies clauses 1--4 of
Theorem 13.1:

- determinant, parity, and ramification are proved in Chapter 8;
- the exact tame-quadratic sequence and its nonzero parameter at $2$ are
  proved in Chapters 6 and 10;
- finite flatness at $p$ is proved in Section 8.2;
- absolute irreducibility, including $p=5$ and $p=7$, is proved in Chapter 9
  from Book 70.

Theorem 13.1 would therefore construct the system used in Chapters 14 and
15.  Theorem 14.1 supplies its all-level finite-flat $3$-adic lattice, and
Book 66 gives (15.3), contradicting purity.  Hence a proof of Theorem 13.1
would exclude every prime exponent $p\geq5$.

This is the exact blueprint route.  The minimal lift is not the original
Frey Tate module; it is a new lift of the hardly ramified residual
representation.  The compatible system is not obtained by descending a
level-$2$ automorphic representation to $\mathbf Q$; it is made effective
over $\mathbf Q$ from a potentially automorphic top system.

### 16.2 Return to every exponent

The reduction of Chapter 2 is already complete.  If $n>2$ has an odd prime
divisor $p$, a nonzero solution of exponent $n$ gives one of exponent $p$.
Theorem 2.1 excludes $p=3$, while Section 16.1 excludes every $p\geq5$ once
Theorem 13.1 is proved.  If $n$ has no odd prime divisor, then $4\mid n$,
and Theorem 2.2 excludes the resulting exponent-$4$ solution.

Thus Theorem 13.1, together with the proved material in this book and its
actual prerequisites, implies Theorem 1.1 with no further bridge.  There is
no separate descent hypothesis, no scalar-prime exception, and no missing
integral certificate at $3$ after Theorem 14.1.

### 16.3 Dependency audit

The established dependencies are as follows.

- Books 12 and 14 prove schematic closure, represented quotients,
  finite-flat subquotients, and installation of finite coefficient actions.
  They prove Theorem 14.1 once the rational good-reduction embedding is
  supplied.
- Book 24 proves the unramified odd-prime rank-two finite-flat classification
  and explicit small-extension lifting used in Lemma 11.2.  Book 25 supplies
  the global represented deformation problem.
- The local Kummer calculation at $2$, the supported obstruction map, the
  Poitou--Tate correction, the balanced presentation, and the normalization
  argument are carried out in Chapters 11 and 12.
- Books 30--32 provide the algebra of Taylor--Wiles systems, patching,
  support, and the abstract comparison after their arithmetic modules and
  integral maps have been constructed.
- Lemma 12.3 proves the totally real balanced dimension and exact auxiliary
  generator count once the disjoint large image is retained.  Section 12.4
  then proves the direct equal-variable kernel-killing argument, including
  deformation shadows independent of the action image and exact
  augmentation.  Neither step assumes faithful deformation-ring support.
- Book 44 supplies global Jacquet--Langlands in the stated range, and Book
  54 supplies Galois representations and geometric Jacobian realizations
  from weight-two automorphic forms.
- Books 55 and 56 state the minimal and nonminimal lifting mechanisms, but
  their arithmetic control and nonminimal packages are not unconditional
  in every Frey-special branch.
- Book 60 supplies the two-prime potential-modularity architecture, but its
  lifting-admissible realization and nonminimal infrastructure must still
  be constructed in the cases listed in Section 12.4.
- Books 61--63 supply compatible-system bookkeeping, Brauer identities,
  exact effectivity criteria, and the rules for changing prime.  They do
  not manufacture the coherent cocycles or the geometric lattice.
- Book 70 proves the semistable full-two irreducibility theorem, including
  the explicit degrees $5$ and $7$.
- The repaired Book 66, Theorems 18.4 and 18.6, unconditionally supplies the
  exact prime-$2$ $3$-adic character theorem and the final trace--purity
  contradiction.

After Theorem 14.1, the former fourth gap is closed.  The former residual
automorphy, descent, and scalar/coefficient-lowering gaps are not independent
assumptions anymore; they are the inseparable internal assertions of Theorem
13.1.  That theorem is the only missing theorem.

Within its first, finite-image conclusion, Theorem 12.4 is the first
irreducible missing arithmetic statement.  Proposition 12.2 proves that its
output makes the scalar reduction finite, while Proposition 12.1 then proves
finite freeness of the entire universal ring and extracts the minimal lift.

### 16.4 Proof construction ledger and scale

A complete proof of Theorem 13.1 must be organized in the following order.

1. **Two-prime realization and residual automorphy.**  Construct the fine
   polarized moduli space, prove geometric connectedness by product
   monodromy, build every local comparison point, impose one avoidance field,
   and obtain a totally real specialization preserving (11.4).  Prove
   cuspidality of the auxiliary source and run the auxiliary-prime lift.
2. **Frey-special integral level control.**  Construct the quaternionic and
   curve-cohomology lattices, Hecke-valued representations, determinant
   pairings, Ihara maps, component-group sequences, and saturated
   degeneracy cube.  Prove the flagged scalar/vexing calculation, the
   simultaneous exactness theorem, and coefficient-prime finite-flat
   lowering.  Verify component support for the actual universal point,
   including $p=5$ and $p=7$.
3. **Finiteness and lift.**  Establish (12.4), deduce finite image of
   (12.1) after restriction, use trace generation to make
   $R^{\min}/p$ finite, and apply Proposition 12.1.
4. **Galois potential automorphy.**  Construct an admissible Galois totally
   real field with $3$ split, rather than passing formally to a normal
   closure.  Recheck residual image, local components, and cuspidality
   there, and attach the top compatible system.
5. **Brauer effectivity.**  Perform every solvable descent over
   $M/M^{H_i}$, normalize self-twists with $\rho_p$, construct the common
   algebraic base-field cocycle and coefficient cocycle, prove their
   vanishing, and turn (13.4) into the actual family (13.9).
6. **Local and geometric compatibility.**  Prove purity and the common
   determinants, transport the ordered special line at $2$, choose
   hyperspecial geometry at $3$, rearrange the positive and negative Brauer
   terms, and construct (13.13).

The first, third, and much of the local deformation algebra already have
foundational support in the preceding books.  The genuinely new specialist
proof is concentrated in items 1--2 and 4--6.  At the level of this series,
a realistic proof occupies approximately $190$--$270$ manuscript pages:
$35$--$50$ pages for the two-prime realization, $70$--$100$ pages for the
integral scalar/vexing and coefficient-prime control, $20$--$30$ pages for
the finiteness comparison, $45$--$65$ pages for Galois potential automorphy
and cocycle effectivity, and $20$--$25$ pages for local and geometric
compatibility.  It requires roughly forty to fifty major lemmas or
propositions, with the saturated multi-level Hecke complex and the common
algebraic descent-cocycle theorem the two largest individual components.

That proof is not present in the available corpus.  Supplying it is
mathematically comparable to the Frey-special Khare--Wintenberger
minimal-lift-and-compatible-family argument, together with the integral
nonminimal cases retained here.  Until Theorem 13.1 is proved, this book is
not an unconditional proof of Fermat's Last Theorem.  Within its first half,
Theorem 12.4 is the exact irreducible missing statement; the remaining
implications to finite flatness and a minimal lift are proved.  Asserting
Theorem 1.1 without that arithmetic construction would fabricate the central
modern arithmetic argument.
