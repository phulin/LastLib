# Cyclotomic Descent for Quintic Fermat-Type Equations

## Contents

1. [The coefficient-five boundary](#1-the-coefficient-five-boundary)
   - [The endpoint](#11-the-endpoint)
   - [What a descent must actually provide](#12-what-a-descent-must-actually-provide)
   - [First and second cases](#13-first-and-second-cases)
   - [The architecture of the proof](#14-the-architecture-of-the-proof)
2. [The cyclotomic input](#2-the-cyclotomic-input)
   - [The field and the ramified prime](#21-the-field-and-the-ramified-prime)
   - [The norm form](#22-the-norm-form)
   - [Units and the three-digit test](#23-units-and-the-three-digit-test)
   - [Coprimality of the linear factors](#24-coprimality-of-the-linear-factors)
   - [The exact ramified extraction](#25-the-exact-ramified-extraction)
   - [The rational coprimality shadow](#26-the-rational-coprimality-shadow)
3. [Primitive solutions and the first case](#3-primitive-solutions-and-the-first-case)
   - [Primitive and symmetric formulations](#31-primitive-and-symmetric-formulations)
   - [Parity and divisibility alternatives](#32-parity-and-divisibility-alternatives)
   - [The short congruence proof](#33-the-short-congruence-proof)
   - [Primary normalization](#34-primary-normalization)
   - [The cyclotomic residue lemma](#35-the-cyclotomic-residue-lemma)
   - [Cycling the signed variables](#36-cycling-the-signed-variables)
4. [Entering the second case](#4-entering-the-second-case)
   - [The exact valuation ledger](#41-the-exact-valuation-ledger)
   - [Removing the common prime](#42-removing-the-common-prime)
   - [Eliminating the unit](#43-eliminating-the-unit)
   - [The rational shapes](#44-the-rational-shapes)
   - [Why the carrier changes fields](#45-why-the-carrier-changes-fields)
5. [The real-quadratic bridge](#5-the-real-quadratic-bridge)
   - [The real ring is Euclidean](#51-the-real-ring-is-euclidean)
   - [The first norm identity](#52-the-first-norm-identity)
   - [Coprime conjugate factors](#53-coprime-conjugate-factors)
   - [Removing the real unit](#54-removing-the-real-unit)
   - [Coordinates of the fifth root](#55-coordinates-of-the-fifth-root)
   - [The initial carrier](#56-the-initial-carrier)
   - [Why this is the right carrier](#57-why-this-is-the-right-carrier)
6. [The carrier replacement](#6-the-carrier-replacement)
   - [Carrier data and the closure problem](#61-carrier-data-and-the-closure-problem)
   - [The second norm identity](#62-the-second-norm-identity)
   - [The forced unit class](#63-the-forced-unit-class)
   - [Absorbing the unit and fixing parity](#64-absorbing-the-unit-and-fixing-parity)
   - [The coordinate engine](#65-the-coordinate-engine)
   - [Coprimality and fifth-power extraction](#66-coprimality-and-fifth-power-extraction)
   - [The explicit successor](#67-the-explicit-successor)
   - [How the replacement identities fit together](#68-how-the-replacement-identities-fit-together)
7. [Strict well-founded descent](#7-strict-well-founded-descent)
   - [The positive quartic identity](#71-the-positive-quartic-identity)
   - [Strict decrease of the carrier](#72-strict-decrease-of-the-carrier)
   - [Iteration and contradiction](#73-iteration-and-contradiction)
   - [The second-case theorem](#74-the-second-case-theorem)
8. [Fermat's theorem at exponent five](#8-fermats-theorem-at-exponent-five)
   - [The primitive nonzero theorem](#81-the-primitive-nonzero-theorem)
   - [All integer and rational solutions](#82-all-integer-and-rational-solutions)
   - [Exponents divisible by five](#83-exponents-divisible-by-five)
9. [Proof integrity and the reusable descent package](#9-proof-integrity-and-the-reusable-descent-package)
   - [The ideal and norm ledgers](#91-the-ideal-and-norm-ledgers)
   - [The valuation and unit ledgers](#92-the-valuation-and-unit-ledgers)
   - [Why the replacement is closed](#93-why-the-replacement-is-closed)
   - [Dependency closure](#94-dependency-closure)
   - [What has been proved](#95-what-has-been-proved)

## 1. The coefficient-five boundary

### 1.1 The endpoint

This volume proves the exponent-five case of Fermat's equation by a complete classical
descent. Its symmetric form is the cleanest statement.

**Theorem 1.1 (Fermat at exponent five).** If $x,y,z\in\mathbf Z$ satisfy

$$
x^5+y^5+z^5=0,
\tag{1.1}
$$

then $xyz=0$.

Equivalently, the only integer solutions of $X^5+Y^5=Z^5$ have a zero
coordinate. The equivalence uses only the oddness of the exponent: in (1.1), move
$z^5$ to the other side and put $Z=-z$.

Book 162, *Quintic Cyclotomic Units and Kummer Arithmetic*, established the arithmetic
of

$$
K=\mathbf Q(\zeta),\qquad \zeta^5=1,\qquad \zeta\ne1.
$$

It proved the exact factorization of $5$, classified all units, controlled the common
prime divisors of the factors $X+\zeta^iY$, and extracted actual fifth powers after
the required local congruence. Those results are the sole substantial prerequisite of
this book. The present task is to turn their output into a genuine descent.

The last phrase matters. Fifth-power extraction produces smaller-looking quantities,
but a proof of infinite descent needs more: a class of objects closed under a
replacement operation and a positive integral measure that becomes strictly smaller.
The second half of this book constructs both explicitly.

### 1.2 What a descent must actually provide

The cyclotomic factorization is

$$
X^5+Y^5=\prod_{i=0}^4(X+\zeta^iY).
\tag{1.2}
$$

For a primitive pair, distinct factors are coprime away from the unique prime above
$5$. Ideal factorization can therefore show that one factor has the shape

$$
X+\zeta Y=u\lambda A^5,
\qquad \lambda=1-\zeta,
\tag{1.3}
$$

in the ramified case. The unit $u$ must still be removed, and even the exact equation
$X+\zeta Y=\lambda A^5$ is not itself an infinite descent. Its norm gives a smaller
integer, but the norm forgets how primes that split in $K$ were distributed among the
conjugate factors. It cannot be reversed to manufacture a new Fermat solution.

There is a second danger. Suppose one factors a new difference of fifth powers and
extracts fifth roots of four of its factors. Multiplying those exact factors determines
the fifth-power class of the fifth factor. That class is forced by the product; it is
not a free state that may be changed to make a proposed recurrence close. A valid
replacement lemma must derive every unit class of its successor from an explicit
identity.

We avoid both dangers by changing the carrier after the cyclotomic extraction. The
absolute norm first gives two rigid rational shapes. A quadratic identity then moves
them to the real subfield $\mathbf Q(\sqrt5)$, where the two conjugate factors are
provably coprime. Their fifth root supplies coprime integers $r,s,b,c$ satisfying

$$
r-s=5b^5,
\qquad
F(r,s)=c^5,
\tag{1.4}
$$

where

$$
F(U,V)=U^4-U^3V+U^2V^2-UV^3+V^4.
\tag{1.5}
$$

The pair of equations (1.4), together with parity and coprimality, is the descent
carrier. Every carrier will produce another one with a new positive parameter
$d<b$. No converse to a norm statement is used.

### 1.3 First and second cases

For a primitive nonzero solution of (1.1), the traditional alternatives are:

- the **first case**, in which $5\nmid xyz$;
- the **second case**, in which $5\mid xyz$.

Pairwise coprimality implies that at most one variable is divisible by $5$. The first
case is impossible already modulo $25$. We will also give its cyclotomic proof,
because it displays exactly what primary normalization does and does not remove.

In the second case, after a permutation and a sign change, the equation becomes

$$
X^5+Y^5=Z^5,
\qquad 5\mid Z,\qquad 5\nmid XY.
\tag{1.6}
$$

Then $5\mid X+Y$. The rational factor $X+Y$ has cyclotomic valuation divisible by
four, while each of the other four linear factors has valuation one. That imbalance
forces

$$
X+Y=5^4a^5,
\qquad
F(X,Y)=5w^5.
\tag{1.7}
$$

The two equations in (1.7) are the entrance to the real-quadratic descent.

### 1.4 The architecture of the proof

The proof has four logically distinct layers:

$$
\begin{array}{c}
\text{primitive signed Fermat equation}\\
\Downarrow\\
\text{first-case contradiction or exact ramified cyclotomic factor}\\
\Downarrow\\
\text{real-quadratic fifth power and an initial carrier}\\
\Downarrow\\
\text{explicit carrier replacement }b\longmapsto d<b.
\end{array}
\tag{1.8}
$$

The hard strategy is concentrated in the last two arrows. The first real-quadratic
factorization creates the carrier. The second is applied to the carrier and, after one
forced unit calculation, reproduces the same carrier equations. An exact positive
quartic identity supplies strictness. Thus closure and decrease are proved by different
identities and neither is hidden in the phrase “repeat the argument.”

## 2. The cyclotomic input

### 2.1 The field and the ramified prime

Put

$$
\mathcal O=\mathbf Z[\zeta],
\qquad
\lambda=1-\zeta,
\qquad
\mathfrak p=(\lambda),
\qquad
\eta=1+\zeta+\zeta^{-1}=\frac{1+\sqrt5}{2}.
\tag{2.1}
$$

Book 162 proves that $\mathcal O$ is a principal ideal domain and that
$\mathfrak p$ is the unique prime above $5$. The exact element identity is

$$
\boxed{5=\zeta^3\eta^2\lambda^4.}
\tag{2.2}
$$

For the normalized valuation $v_{\mathfrak p}$,

$$
v_{\mathfrak p}(\lambda)=1,
\qquad
v_{\mathfrak p}(5)=4,
\qquad
v_{\mathfrak p}(n)=4v_5(n)
\quad(n\in\mathbf Z\setminus\{0\}).
\tag{2.3}
$$

Every nontrivial conjugate

$$
\lambda_i=1-\zeta^i,
\qquad 1\le i\le4,
\tag{2.4}
$$

is an associate of $\lambda$ and has valuation one. The residue field is
$\mathcal O/\mathfrak p\cong\mathbf F_5$, with every $\zeta^i$ reducing to one.

The factor four in (2.3) will account for every exceptional exponent below. A rational
integer divisible once by $5$ lies four levels deep at $\mathfrak p$; a nonrational
linear factor in the second case lies only one level deep.

### 2.2 The norm form

The absolute norm of a nonzero element of $\mathcal O$ is positive. Units have norm
one, and

$$
N_{K/\mathbf Q}(\lambda)=5.
\tag{2.5}
$$

For ordinary integers $U,V$,

$$
N_{K/\mathbf Q}(U+\zeta V)
=F(U,V)
=U^4-U^3V+U^2V^2-UV^3+V^4.
\tag{2.6}
$$

When $U+V\ne0$,

$$
(U+V)F(U,V)=U^5+V^5.
\tag{2.7}
$$

The form $F$ is positive away from $(0,0)$ because it is an absolute norm. It is also
symmetric:

$$
F(U,V)=F(V,U).
\tag{2.8}
$$

Two elementary identities involving $F$ will later do all the archimedean work:

$$
5(U^2+V^2)^2-(U+V)^4=4F(U,V),
\tag{2.9}
$$

and

$$
\begin{aligned}
16\bigl(5F(U,V)-(U-V)^4\bigr)
={}&5(U+V)^4\\
&+50(U+V)^2(U-V)^2+9(U-V)^4.
\end{aligned}
\tag{2.10}
$$

Both follow by expansion. Identity (2.9) creates the real-quadratic norm equations;
(2.10) later proves that the replacement is strictly smaller.

### 2.3 Units and the three-digit test

Every unit of $\mathcal O$ has a unique expression

$$
u=\pm\zeta^a\eta^n,
\qquad 0\le a<5,\quad n\in\mathbf Z.
\tag{2.11}
$$

Modulo fifth powers, $\zeta$ and $\eta$ give the two independent unit classes. An
element prime to $\lambda$ is **primary** when it is congruent to a nonzero rational
integer modulo $\lambda^2$. Every $\lambda$-adic unit has a unique associate
$\zeta^kA$ that is primary.

We will use two exact consequences from Book 162.

**Primary-unit criterion.** A unit congruent to a rational integer modulo
$\lambda^2$ is real. Thus it is $\pm\eta^n$.

**Fifth-power unit criterion.** A unit congruent to a rational integer modulo
$\lambda^3$ is a fifth power in $\mathcal O^\times$.

The second criterion follows from the expansion

$$
\eta\equiv3+\lambda^2\pmod{\lambda^3}.
\tag{2.12}
$$

The linear $\lambda$-digit detects the $\zeta$-exponent, and the quadratic digit then
detects the $\eta$-exponent modulo five. The modulus is sharp: $\eta$ is rational
modulo $\lambda^2$ but is not a fifth power.

Every integral fifth power is congruent to a rational integer modulo $5\mathcal O$,
hence modulo $\lambda^4$. Therefore, if a $\lambda$-adic unit has the form $uA^5$
and is rational modulo $\lambda^3$, then $u$ is a fifth power. This is the unit-removal
step used in the second case.

### 2.4 Coprimality of the linear factors

Let $U,V\in\mathbf Z$ be coprime and put

$$
L_i=U+\zeta^iV,
\qquad i\in\mathbf Z/5\mathbf Z.
\tag{2.13}
$$

If a prime ideal divides both $L_i$ and $L_j$ with $i\ne j$, two linear
combinations show that it divides

$$
U(\zeta^{j-i}-1)
\quad\text{and}\quad
V(\zeta^i-\zeta^j).
$$

Every displayed cyclotomic difference is an associate of $\lambda$. A prime other
than $\mathfrak p$ would consequently divide both $U$ and $V$, contradicting
primitivity. Hence distinct $L_i$ have no common prime ideal away from
$\mathfrak p$.

Their exact valuations at $\mathfrak p$ have two forms:

$$
\begin{array}{c|c}
5\nmid U+V & v_{\mathfrak p}(L_i)=0\text{ for every }i,\\
5\mid U+V &
v_{\mathfrak p}(L_0)=4v_5(U+V),\quad
v_{\mathfrak p}(L_i)=1\text{ for }i\ne0.
\end{array}
\tag{2.14}
$$

For the second row, write

$$
U+\zeta^iV=(U+V)+V(\zeta^i-1).
$$

The two summands have valuations at least four and exactly one. They cannot cancel.

### 2.5 The exact ramified extraction

The cyclotomic input can now be packaged in the exact form needed later.

**Proposition 2.1 (ramified factor).** Suppose

$$
U^5+V^5=W^5,
\qquad \gcd(U,V)=1,
\qquad 5\mid U+V.
\tag{2.15}
$$

Then there is $A\in\mathcal O$ such that

$$
\boxed{U+\zeta V=\lambda A^5.}
\tag{2.16}
$$

**Proof strategy.** Ideal coprimality and the valuation-one statement first give a
unit times $\lambda$ times a fifth power. Dividing by $\lambda$ leaves a rational
residue three digits deep, which forces the unit to be a fifth power.

**Proof.** In the product (1.2), every prime away from $\mathfrak p$ occurs in at
most one factor. Its exponent there is therefore divisible by five. Equation (2.14)
gives $v_{\mathfrak p}(U+\zeta V)=1$. Since $\mathcal O$ is a PID, ideal extraction
gives

$$
U+\zeta V=u\lambda B^5
\tag{2.17}
$$

for a unit $u$ and a $\lambda$-adic unit $B$.

Write $U+V=5m$. Using (2.2),

$$
\frac{U+\zeta V}{\lambda}
=\frac{U+V-V\lambda}{\lambda}
=\zeta^3\eta^2m\lambda^3-V
\equiv -V\pmod{\lambda^3}.
\tag{2.18}
$$

The quotient is a $\lambda$-adic unit. The fifth power $B^5$ is congruent to a
nonzero rational integer modulo $\lambda^4$. Dividing (2.18) by that residue makes
$u$ rational modulo $\lambda^3$. The fifth-power unit criterion writes $u=v^5$.
Replacing $B$ by $vB$ proves (2.16). $\square$

Taking norms gives the safe implication

$$
F(U,V)=5N(A)^5.
\tag{2.19}
$$

The proof went from ideals to an element and only then to its norm. We will never
reverse (2.19).

### 2.6 The rational coprimality shadow

The ideal calculation has a useful integer shadow that will audit every later
$5$-adic exponent. For coprime $U,V$,

$$
\gcd(U+V,F(U,V))\mid5.
\tag{2.20}
$$

Indeed, if a rational prime $q$ divides $U+V$, then $U\equiv-V\pmod q$, and

$$
F(U,V)\equiv5V^4\pmod q.
$$

Primitivity gives $q\nmid V$, so a common prime must be $5$.

The value at $5$ is exact. Put $h=U+V$ and $U=-V+h$. Direct expansion gives

$$
F(U,V)
=5V^4-10V^3h+10V^2h^2-5Vh^3+h^4.
\tag{2.21}
$$

If $5\mid h$ and $5\nmid V$, the first term has $5$-adic value one and every
remaining term has value at least two. Hence

$$
v_5(F(U,V))=1.
\tag{2.22}
$$

This agrees with the cyclotomic calculation

$$
v_5\bigl(N(U+\zeta V)\bigr)
=v_{\mathfrak p}(U+\zeta V)=1.
$$

The agreement is special to the unique prime above $5$. At a split rational prime,
two coprime ideals can have norms sharing that prime, so (2.20) cannot replace the
ideal argument that produced (2.16). Its role is instead to certify that the factor
$5$ in (2.19) occurs exactly once and that $N(A)$ is prime to $5$.

## 3. Primitive solutions and the first case

### 3.1 Primitive and symmetric formulations

Assume that (1.1) has a nonzero solution. Divide all three variables by their positive
common divisor. The resulting solution is primitive:

$$
\gcd(x,y,z)=1.
\tag{3.1}
$$

It is then pairwise coprime. A prime dividing two variables divides the fifth power of
the third and hence the third variable, contrary to (3.1).

Whenever convenient, move one term to the other side and write

$$
a^5+b^5=c^5.
\tag{3.2}
$$

All signs are absorbed into $a,b,c$ because the exponent is odd. Conversely, any
result proved for (3.2) applies to the symmetric equation after one sign change. This
orientation never assumes that the variables themselves are positive.

### 3.2 Parity and divisibility alternatives

In a primitive solution of the symmetric equation, exactly two variables are odd and
one is even. Indeed, reduction modulo $2$ shows that the number of odd variables is
even, and primitivity excludes zero odd variables. After orienting the equation as
(3.2), there are consequently two legitimate parity patterns:

$$
\begin{array}{c|c}
c\text{ odd} & a,b\text{ have opposite parity},\\
c\text{ even} & a,b\text{ are both odd}.
\end{array}
$$

Both patterns really must be retained. The congruence of two odd fifth powers can
vanish to high $2$-adic order when the two bases are negatives of one another modulo a
large power of $2$. There is no valid reduction modulo $4$ that rules out the second
row.

At the prime $5$, pairwise coprimality permits at most one divisible variable. If none
is divisible, we are in the first case. If one is divisible, a permutation of the
three signed terms in (1.1) places it on the right of (3.2). We may therefore orient
the second case as

$$
a^5+b^5=c^5,
\qquad 5\mid c,\qquad 5\nmid ab.
\tag{3.3}
$$

Fermat's congruence $t^5\equiv t\pmod5$ then gives

$$
a+b\equiv c\equiv0\pmod5.
\tag{3.4}
$$

### 3.3 The short congruence proof

The first case can be closed without algebraic number theory. We give this proof first
because it is an independent check on the longer cyclotomic mechanism.

**Lemma 3.1 (fifth powers modulo $25$).** If $5\nmid n$, then

$$
n^5\pmod{25}\in\{1,7,-7,-1\}.
\tag{3.5}
$$

No sum of two members of this set is again a member of the set.

**Proof.** Write $n=r+5t$ with $r\in\{1,2,3,4\}$. The binomial theorem gives
$n^5\equiv r^5\pmod{25}$. The four values are

$$
1^5\equiv1,\qquad
2^5\equiv7,\qquad
3^5\equiv-7,\qquad
4^5\equiv-1\pmod{25}.
$$

Adding the unordered pairs from $\{\pm1,\pm7\}$ gives only
$0,\pm2,\pm6,\pm8,\pm14$, none of which is $\pm1$ or $\pm7$ modulo $25$.
$\square$

If $5\nmid abc$ in (3.2), the three fifth powers are nonzero fifth-power residues
modulo $25$, contradicting Lemma 3.1. Thus:

**Theorem 3.2 (first case, congruence form).** A primitive nonzero solution of
(3.2) cannot satisfy $5\nmid abc$.

The remainder of this chapter proves the same theorem cyclotomically. It records how
the real unit that survives first-case extraction is handled, a distinction that
becomes important when comparing the two cases.

### 3.4 Primary normalization

Assume for contradiction that

$$
a^5+b^5=c^5,
\qquad \gcd(a,b)=1,
\qquad 5\nmid abc.
\tag{3.6}
$$

Then $5\nmid a+b$. The five factors $a+\zeta^ib$ are pairwise coprime, including at
$\mathfrak p$, so ideal extraction gives

$$
a+\zeta b=uA^5.
\tag{3.7}
$$

There is a unique $k\in\mathbf Z/5\mathbf Z$ such that
$\zeta^k(a+\zeta b)$ is primary. Since

$$
a+\zeta b=(a+b)-b\lambda,
$$

its first two $\lambda$-digits give

$$
k(a+b)+b\equiv0\pmod5,
\quad\text{or equivalently}\quad
ka+(k+1)b\equiv0\pmod5.
\tag{3.8}
$$

The fifth power $A^5$ is primary. The primary-unit criterion therefore makes the unit
in the normalized equation real. Absorbing a sign and a fifth power of $\eta$ into
$A^5$, we obtain

$$
\boxed{\zeta^k(a+\zeta b)=\eta^eA^5}
\tag{3.9}
$$

for some $e\in\{0,1,2,3,4\}$. We do not assert that $e=0$; in the first case there
is no three-digit congruence that would justify that assertion.

### 3.5 The cyclotomic residue lemma

The surviving real unit disappears when (3.9) is compared with its complex
conjugate. We first record the required depth.

**Lemma 3.3.** For every $A\in\mathcal O$,

$$
\lambda^5\mid A^5-\bar A^5.
\tag{3.10}
$$

**Proof.** Since conjugation acts trivially modulo $\lambda$, write
$A=\bar A+\lambda D$. Expanding $A^5-\bar A^5$, the first four nonzero terms contain
$5\lambda,5\lambda^2,5\lambda^3,5\lambda^4$, respectively, and the last contains
$\lambda^5$. Since $\lambda^4\mid5$, every term is divisible by $\lambda^5$.
$\square$

Conjugating (3.9) and subtracting gives

$$
a(\zeta^k-\zeta^{-k})
+b(\zeta^{k+1}-\zeta^{-(k+1)})
=\eta^e(A^5-\bar A^5).
\tag{3.11}
$$

The right side is divisible by $\lambda^5$.

**Lemma 3.4 (first-case residue lemma).** Under (3.6),

$$
a\equiv b\pmod5.
\tag{3.12}
$$

**Proof strategy.** Equation (3.8) excludes two values of $k$. For two more values,
the rational coordinate of the left side of (3.11) contradicts divisibility by
$\lambda^5$. The middle value is then forced.

**Proof.** If $k=0$, equation (3.8) gives $5\mid b$; if $k=4$, it gives
$5\mid a$. Hence $k\in\{1,2,3\}$.

Use the integral basis $1,\lambda,\lambda^2,\lambda^3$. For $k=1$, the left side of
(3.11) has coordinates

$$
5a+(-7a+b)\lambda+(4a-2b)\lambda^2+(-a+b)\lambda^3.
\tag{3.13}
$$

An element divisible by $\lambda^5$ has rational coordinate divisible by $25$.
Thus (3.13) would give $25\mid5a$, contrary to $5\nmid a$. For $k=3$, the rational
coordinate is $-5b$, giving the same contradiction with $5\nmid b$.

Therefore $k=2$. Equation (3.8) becomes

$$
2a+3b\equiv2(a-b)\equiv0\pmod5,
$$

which proves (3.12). $\square$

For $k=2$, the left side of (3.11) is exactly

$$
(a-b)(\zeta^2-\zeta^3).
$$

The cyclotomic difference contributes one copy of $\lambda$ and $a-b$ contributes
four when $5\mid a-b$. This explains why the middle residue class survives for one
ordered pair.

It is useful to see the complete residue ledger. The primary congruence and the
consequence of $\lambda^5$-divisibility are

| $k$ | equation from primarity | consequence of conjugate subtraction |
|---|---|---|
| $0$ | $b\equiv0$ | excluded by the first case |
| $1$ | $a+2b\equiv0$ | the rational coordinate forces $a\equiv0$ |
| $2$ | $2a+3b\equiv0$ | $a\equiv b$ |
| $3$ | $3a+4b\equiv0$ | the rational coordinate forces $b\equiv0$ |
| $4$ | $4a\equiv0$ | excluded by the first case |

The rational-coordinate test in the two asymmetric rows uses the valuation formula
from Book 162. If

$$
C_0+C_1\lambda+C_2\lambda^2+C_3\lambda^3
$$

is divisible by $\lambda^5$, then $4v_5(C_0)\ge5$, so $25\mid C_0$.
For $k=1$ that coordinate is $5a$; for $k=3$ it is $-5b$. The table therefore
contains no suppressed cancellation among the other three coordinates.

This calculation also shows exactly why one ordered pair is insufficient. In the
middle row, $a-b$ may contribute the required rational factor $5$, and then the left
side of (3.11) really is divisible by $\lambda^5$. Cycling the signed variables in the
next section is a mathematical step, not a stylistic repetition.

### 3.6 Cycling the signed variables

Apply Lemma 3.4 to (3.6): $a\equiv b\pmod5$. Rewrite the same equation as

$$
a^5+(-c)^5=(-b)^5.
$$

It is still a primitive first-case equation, so the lemma also gives

$$
a\equiv-c\pmod5.
$$

On the other hand, the original equation modulo $5$ and $a\equiv b$ give

$$
c\equiv a+b\equiv2a\pmod5.
$$

Thus $a\equiv-2a$, so $3a\equiv0\pmod5$, contradicting $5\nmid a$. We have proved
the cyclotomic form of the first-case theorem.

The two proofs illuminate different facts. Modulo $25$, the first case fails because
the nonzero fifth-power residues are too sparse. Cyclotomically, primary normalization
leaves a real unit, conjugate subtraction removes it, and cycling the signed variables
closes the contradiction. Neither proof assumes that a primary unit is a fifth power.

## 4. Entering the second case

### 4.1 The exact valuation ledger

Assume a primitive nonzero second-case solution has been oriented as

$$
x^5+y^5=z^5,
\qquad 5\mid z,\qquad 5\nmid xy.
\tag{4.1}
$$

Then $5\mid x+y$. Put

$$
t=v_5(x+y),
\qquad
s=v_5(z).
$$

The rational factor has $\mathfrak p$-value $4t$, while each of the four
nonrational factors has value one. Hence

$$
v_{\mathfrak p}(x^5+y^5)=4t+4.
$$

The right side has value $20s$. Therefore

$$
\boxed{t+1=5s.}
\tag{4.2}
$$

In particular,

$$
t\equiv4\pmod5,
\qquad
t\ge4.
\tag{4.3}
$$

The congruence $t\equiv4$ is the first rigid gain of the second case. It comes from
the four nonrational factors, not from treating $5$ as a uniformizer.

The same equality can be read factor by factor:

$$
\underbrace{4t}_{x+y}
+\underbrace{1+1+1+1}_{x+\zeta^iy,\ i=1,2,3,4}
=\underbrace{5\cdot4s}_{z^5}.
$$

The left side counts the five cyclotomic factors, while the right side first multiplies
the valuation by the exponent five and then converts an ordinary factor of $5$ into
four copies of $\lambda$. This ledger is a useful hostile check: using
$v_{\mathfrak p}(5)=1$ would give the false relation $t+4=5s$.

There is no cancellation hidden in the four unit valuations. For $i\ne0$,

$$
x+\zeta^iy=(x+y)+y(\zeta^i-1).
$$

The first summand has value at least sixteen because $t\ge4$ once (4.2) is known,
whereas the second has value one. Even before knowing $t\ge4$, divisibility of
$x+y$ by $5$ gives values at least four and one. The smaller value occurs uniquely.

### 4.2 Removing the common prime

For $i=1,2,3,4$, divide the factor $x+\zeta^iy$ by its exact conjugate uniformizer
$1-\zeta^i$. The resulting integral factors are prime to $\mathfrak p$ and pairwise
coprime. Consequently every prime-ideal exponent away from $\mathfrak p$ in
$x+\zeta y$ is divisible by five. Its $\mathfrak p$-value is one. The ideal argument
therefore gives

$$
x+\zeta y=u\lambda A^5
\tag{4.4}
$$

with $u\in\mathcal O^\times$ and $A$ a $\lambda$-adic unit.

This is the exact point where class number one is used. Prime-ideal factorization
first produces

$$
(x+\zeta y)=\mathfrak p\mathfrak a^5.
$$

The ideal $\mathfrak a$ is principal, say $(A)$, and equality of principal ideals
leaves the unit $u$. No unit has been silently discarded.

### 4.3 Eliminating the unit

Write $x+y=5m$. Dividing (4.4) by $\lambda$ and using (2.2) gives

$$
\frac{x+\zeta y}{\lambda}
=\zeta^3\eta^2m\lambda^3-y
\equiv-y\pmod{\lambda^3}.
\tag{4.5}
$$

The quotient is a $\lambda$-adic unit. Since $A^5$ is rational modulo
$\lambda^4$, equation (4.5) makes $u$ rational modulo $\lambda^3$. The
fifth-power unit criterion absorbs it into $A^5$. Thus Proposition 2.1 gives the exact
equation

$$
\boxed{x+\zeta y=\lambda A^5.}
\tag{4.6}
$$

This is stronger than its ideal version and stronger than its norm. The depth three in
(4.5) is exact: one rational factor $5$ contributes four copies of $\lambda$, and
division by the one common copy leaves three.

### 4.4 The rational shapes

Taking absolute norms of (4.6) yields

$$
F(x,y)=5w^5,
\qquad
w=N_{K/\mathbf Q}(A)>0.
\tag{4.7}
$$

Now

$$
z^5=(x+y)F(x,y)=5(x+y)w^5.
$$

Thus $(z/w)^5=5(x+y)$. A rational number whose fifth power is an integer is an
integer, so $z/w=q\in\mathbf Z$. Its fifth power is divisible by $5$, hence
$q=5a$ for some nonzero $a\in\mathbf Z$. We obtain

$$
\boxed{
x+y=5^4a^5,
\qquad
F(x,y)=5w^5,
\qquad
z=5aw.
}
\tag{4.8}
$$

These formulas agree with (4.2):

$$
v_5(x+y)=4+5v_5(a),
\qquad
v_5(z)=1+v_5(a),
$$

because $5\nmid w$ follows from $v_5(F(x,y))=1$.

There is also a prime-by-prime way to read the same shapes. By Section 2.6, the two
rational factors $x+y$ and $F(x,y)$ are coprime away from $5$, and the latter has
exact value one at $5$. Since their product is $z^5$, every prime away from $5$ occurs
to a multiple of five in each factor separately. At $5$, the exponents have residues
$4$ and $1$ modulo five. This forces

$$
x+y=5^4a^5,
\qquad
F(x,y)=5w^5
$$

directly, including their signs because $F$ is positive and fifth powers preserve
sign. This rational verification agrees with the norm proof but does not replace the
exact cyclotomic equation (4.6), which is what resolved the unit ambiguity.

The quantities $|a|$ and $w$ are smaller than $|z|$, but (4.8) alone is not a
descent. Neither is yet the last coordinate of a new Fermat solution. The next chapter
constructs an object that is genuinely closed under replacement.

### 4.5 Why the carrier changes fields

The exact cyclotomic element $A$ remembers all prime-ideal information, but a direct
iteration on conjugate differences of $A$ introduces exact roots of unity whose
classes are fixed by the product of the factors. There is no legitimate freedom to
alter those classes in a successor definition.

The rational shadows (4.8) suggest a more stable path. Identity (2.9) turns
$F(x,y)=5w^5$ into a norm equation in the real quadratic subfield. Its two conjugate
factors will be coprime for elementary reasons. Unique factorization there gives an
actual fifth power, and comparing its two coordinates produces the carrier (1.4).

This change of field does not throw away the cyclotomic proof. Equation (4.6) is what
certifies (4.7) without reversing a norm, and the unit criterion that proves (4.6)
will be used again to remove the first real-quadratic unit. The real subfield is the
place where the replacement becomes closed, not a substitute for the cyclotomic
arithmetic.

The quadratic identity is also naturally suggested by the relative norm. The two
complex-conjugate pairs of embeddings of $K$ pass through $K^+$. Grouping the four
linear factors into those pairs turns the quartic form into a product of two positive
quadratic forms over $K^+$. Identity (2.9) is the rational-coordinate version of that
grouping. Its advantage for descent is that a real quadratic element has only two
coordinates. A fifth-power comparison therefore produces two explicit equations,
and one linear combination can isolate the old ramified difference.

The field change also makes positivity available without sacrificing arithmetic
control. The absolute norm from $K$ is positive but has four conjugate factors; the
norm from $K^+$ has two real factors whose signs and gcds can be inspected directly.
The later inequality (7.2) belongs to the same two-coordinate geometry. In this way
the real subfield supplies both closure and strictness, while the quartic field supplies
the exact initial extraction.

## 5. The real-quadratic bridge

### 5.1 The real ring is Euclidean

Put

$$
K^+=\mathbf Q(\sqrt5),
\qquad
\pi=\sqrt5,
\qquad
\eta=\frac{1+\pi}{2}.
\tag{5.1}
$$

Book 162 identifies the ring of integers as

$$
\mathcal O^+=\mathbf Z[\eta]
=\left\{\frac{m+n\pi}{2}:m,n\in\mathbf Z, m\equiv n\pmod2\right\}.
\tag{5.2}
$$

It also proves

$$
(\mathcal O^+)^\times=\{\pm\eta^n:n\in\mathbf Z\}.
\tag{5.3}
$$

We need principal ideals in this real ring. Rather than import another class-number
statement, we prove the stronger Euclidean property directly.

**Lemma 5.1 (Euclideanity of the real ring).** The function

$$
\delta(\alpha)=|N_{K^+/\mathbf Q}(\alpha)|
$$

makes $\mathcal O^+$ a Euclidean domain.

**Proof strategy.** Approximate the two coefficients in the basis $1,\eta$ by nearest
integers. The norm of the error is uniformly less than one.

**Proof.** Write an arbitrary element of $K^+$ as $a+b\eta$ with
$a,b\in\mathbf Q$. Choose $m,n\in\mathbf Z$ such that

$$
|a-m|\le\frac12,
\qquad
|b-n|\le\frac12.
$$

Put $u=a-m$ and $v=b-n$. Since $\eta+\eta'=1$ and $\eta\eta'=-1$,

$$
N(u+v\eta)=u^2+uv-v^2.
$$

Therefore

$$
|N(u+v\eta)|
\le |u|^2+|uv|+|v|^2
\le\frac34<1.
$$

Given $\alpha,\beta\in\mathcal O^+$ with $\beta\ne0$, apply this approximation to
$\alpha/\beta$ and choose $q=m+n\eta$. Then

$$
|N(\alpha-q\beta)|
=|N(\beta)|\,|N(\alpha/\beta-q)|
<|N(\beta)|.
$$

This is Euclidean division. $\square$

Consequently $\mathcal O^+$ is a PID. We will use ideal factorization before choosing
generators, exactly as in the cyclotomic ring.

### 5.2 The first norm identity

Return to the second-case shapes (4.8). Set

$$
S=x+y,
\qquad
R=x^2+y^2,
\qquad
T=\frac{S^2}{5}.
\tag{5.4}
$$

The integer $T$ is well defined because $5^4\mid S$. Its parity depends on the two
patterns in Section 3.2. If $x,y$ have opposite parity, then $S,R,T$ are odd. If they are
both odd, then $S,R,T$ are even; more precisely, $R/2$ is odd and $T/2$ is even.
Indeed, an even $S=5^4a^5$ makes $a$ even, so $T=S^2/5$ is divisible by a high
power of two.

Identity (2.9) and $F(x,y)=5w^5$ give

$$
R^2-5T^2
=\frac{5R^2-S^4}{5}
=4w^5.
\tag{5.5}
$$

In either parity pattern, the algebraic integer

$$
\alpha=\frac{R+T\pi}{2}\in\mathcal O^+
\tag{5.6}
$$

satisfies

$$
N_{K^+/\mathbf Q}(\alpha)=w^5.
\tag{5.7}
$$

This is the first real-quadratic bridge. The particular division by $5$ in the
definition of $T$ is forced: it changes the norm $F(x,y)=5w^5$ into the exact fifth
power $w^5$.

### 5.3 Coprime conjugate factors

To extract a fifth power from (5.7), the ideals $(\alpha)$ and $(\bar\alpha)$ must be
coprime. This is where the special origin of $R$ and $T$ is used.

The general test is simple. If

$$
\theta=\frac{A+B\pi}{2}\in\mathcal O^+,
$$

then a prime ideal common to $\theta$ and $\bar\theta$ divides both $A$ and
$B\pi$. Away from the primes over $2$ and $5$, coprimality of the ordinary integers
$A,B$ excludes it. The prime over $5$ is tested by the rational coordinate $A$, since
$\pi$ vanishes in the residue field. Primes over $2$ must be checked in the
integral lattice actually containing $\theta$; one cannot simply divide both
coordinates by two inside a residue field of characteristic two.

First, $R$ and $S$ have no common odd prime divisor:

$$
\gcd(R,S)\mid2.
\tag{5.8}
$$

Indeed, a common odd prime would give $x\equiv-y$ and hence
$R=x^2+y^2\equiv2y^2$ modulo that prime. Since $x,y$ are coprime, no such prime is
possible. Also

$$
R\equiv2y^2\not\equiv0\pmod5,
$$

because $x\equiv-y\pmod5$ and $5\nmid y$. Since $T=S^2/5$, it follows that

$$
\gcd(R,T)=
\begin{cases}
1,&x,y\text{ have opposite parity},\\
2,&x,y\text{ are both odd},
\end{cases}
\qquad 5\nmid R.
\tag{5.9}
$$

Now suppose a prime ideal of $\mathcal O^+$ divides both $\alpha$ and
$\bar\alpha$. It divides their sum $R$ and their difference $T\pi$. Away from the
primes above $2$ and $5$, this contradicts (5.9). At $(\pi)$ it would force
$5\mid R$, also impossible.

It remains to check $2$ in the both-odd pattern. Write $R=2R_0$ and $T=2T_0$.
Then $R_0$ is odd, $T_0$ is even, and

$$
\alpha=R_0+T_0\pi.
$$

Modulo $2\mathcal O^+$, one has $\pi=2\eta-1\equiv1$, so $\alpha$ and
$\bar\alpha$ both reduce to $1$. Thus no prime above $2$ divides either factor.
Hence in both parity patterns

$$
(\alpha)+(\bar\alpha)=\mathcal O^+.
\tag{5.10}
$$

This proof also excludes a common ideal above a rational prime that splits in
$K^+$. The argument is made prime ideal by prime ideal: a common prime ideal divides
the two displayed rational combinations, and the integer gcd then produces the
contradiction. We are not claiming that the rational norms of $\alpha$ and
$\bar\alpha$ are coprime; they are equal. What matters is coprimality of the two
conjugate ideals whose product is $(w)^5$.

Their product is the fifth-power ideal $(w)^5$. Unique factorization of ideals and
(5.10) give

$$
(\alpha)=\mathfrak a^5.
$$

Lemma 5.1 makes $\mathfrak a$ principal. Therefore

$$
\alpha=u\beta^5
\tag{5.11}
$$

for $u\in(\mathcal O^+)^\times$ and $\beta\in\mathcal O^+$.

At this point the logic has three independent inputs: the norm equation makes the
product a fifth power, conjugate coprimality assigns every prime exponent wholly to
one side, and Euclideanity makes the resulting fifth-root ideal principal. If any one
of these inputs were omitted, equation (5.11) would not follow.

### 5.4 Removing the real unit

The unit in (5.11) is not discarded merely because it is real. The deep divisibility
of $T$ removes it.

From $S=5^4a^5$,

$$
v_5(T)=v_5(S^2/5)=7+10v_5(a).
\tag{5.12}
$$

Book 162 proves that $\pi=\sqrt5$ is an associate of $\lambda^2$. Consequently

$$
v_{\mathfrak p}(T\pi)
=4v_5(T)+2
\ge30.
$$

In particular, $\alpha$ is congruent to a rational integer modulo $\lambda^3$.
It is a $\lambda$-adic unit because $5\nmid R$.
When $R$ is odd, the notation $R/2$ causes no congruence ambiguity: the quotient
modulo $\lambda^3$ has characteristic five, and the inverse of $2$ is represented by
the ordinary integer $3$.

Every fifth power is rational modulo $\lambda^4$, so (5.11) makes $u$ rational
modulo $\lambda^3$. The fifth-power unit criterion from Book 162 says that $u$ is a
fifth power. Since $u$ is real, (5.3) shows directly that its $\eta$-exponent is
divisible by five; its fifth root may be chosen in $\mathcal O^+$. Absorbing that root
into $\beta$, we obtain the exact equation

$$
\boxed{\frac{R+T\pi}{2}=\beta^5.}
\tag{5.13}
$$

This use of the three-digit criterion is legitimate because the ideal fifth-power
condition was proved first. Deep rational congruence alone would not make an arbitrary
algebraic integer a fifth power.

### 5.5 Coordinates of the fifth root

Write $\beta=(m+n\pi)/2$ with $m\equiv n\pmod2$. The parity of these coordinates
follows the parity of $R,T$.

We will repeatedly use the following elementary parity calculation. If $m,n$ are
odd, then

$$
\begin{aligned}
m^5+50m^3n^2+125mn^4&\equiv16\pmod{32},\\
5m^4n+50m^2n^3+25n^5&\equiv16\pmod{32}.
\end{aligned}
\tag{5.14}
$$

Thus the fifth power of $(m+n\pi)/2$ again has genuinely half-integral coordinates.
By contrast, the fifth power of an element of $\mathbf Z[\pi]$ has integral
coordinates. These two coordinate lattices therefore cannot be confused by taking a
fifth power.

Suppose first that $x,y$ have opposite parity. Then $R,T$ are odd, so the right side
of (5.13) has half-integral rational and $\pi$-coordinates. Thus $m,n$ are odd.
Expanding gives

$$
16R=m^5+50m^3n^2+125mn^4,
\tag{5.15}
$$

$$
16T=5n\bigl(m^4+10m^2n^2+5n^4\bigr).
\tag{5.16}
$$

In this branch define

$$
r=\frac{m+n}{2},
\qquad
s=\frac{m-n}{2}.
\tag{5.17}
$$

Now suppose that $x,y$ are both odd. Then $R,T$ are even and $\alpha$ has integral
rational and $\pi$-coordinates. An element with odd half-integral coordinates has a
fifth power with half-integral coordinates, so $m,n$ are even. Write

$$
\beta=M+N\pi.
$$

Coordinate comparison gives

$$
\frac R2=M^5+50M^3N^2+125MN^4,
\tag{5.18}
$$

$$
\frac T2=5N\bigl(M^4+10M^2N^2+5N^4\bigr).
\tag{5.19}
$$

In this branch define

$$
r=M+N,
\qquad
s=M-N.
\tag{5.20}
$$

The definitions are different because one fifth root has half-integral coordinates
and the other has integral coordinates. They are chosen so that the same two formulas
hold in both branches:

$$
r-s>0,
\qquad
(r-s)F(r,s)=\frac T5.
\tag{5.21}
$$

For the first branch, the polynomial identity behind (5.21) is

$$
m^4+10m^2n^2+5n^4
=16F\left(\frac{m+n}{2},\frac{m-n}{2}\right).
\tag{5.22}
$$

For the second branch, homogeneity gives

$$
M^4+10M^2N^2+5N^4=F(M+N,M-N).
\tag{5.23}
$$

The quartic factors in (5.16) and (5.19) are positive, so $n>0$ or $N>0$ and
hence $r-s>0$.

The new pair is primitive. The ideals $(\beta)$ and $(\bar\beta)$ are coprime
because their fifth powers are $(\alpha)$ and $(\bar\alpha)$. Thus the coordinates
in the relevant branch are coprime. In the half-integral branch this gives
$\gcd(r,s)=1$. In the integral branch, $R/2$ is odd; reducing (5.18) modulo $2$
forces $M$ odd and $N$ even. Hence $r,s$ are odd, and a common divisor would divide
both $M$ and $N$. Again $\gcd(r,s)=1$.

Finally, $\beta$ is a unit at $(\pi)$. Thus $5\nmid m$ in the first branch and
$5\nmid M$ in the second. These residue facts locate the exceptional factor $5$ in
the next extraction.

### 5.6 The initial carrier

Equation (5.21) and $T=5^7a^{10}$ give, in both parity branches,

$$
(r-s)F(r,s)=5^6a^{10}=5(5a^2)^5.
\tag{5.24}
$$

The two factors on the left are coprime. Indeed, modulo $r-s$ one has $r\equiv s$
and

$$
F(r,s)\equiv r^4\pmod{r-s}.
$$

Since $\gcd(r,s)=1$, this proves

$$
\gcd(r-s,F(r,s))=1.
\tag{5.25}
$$

The prime $5$ belongs to $r-s$. In the first branch, the quartic factor in (5.16) is
congruent to $m^4\not\equiv0\pmod5$; in the second, the quartic factor in (5.19) is
congruent to $M^4\not\equiv0\pmod5$. Since
$v_5(T)=7+10v_5(a)$, the difference $r-s$ is divisible by $5$, while
$F(r,s)$ is not.

Ordinary unique factorization in $\mathbf Z$, applied to (5.24) and (5.25), now
produces positive integers $b,c$ with

$$
\boxed{
r-s=5b^5,
\qquad
F(r,s)=c^5.
}
\tag{5.26}
$$

Taking the positive fifth root of (5.24) also gives

$$
bc=5a^2.
\tag{5.27}
$$

Thus every primitive second-case Fermat solution creates data

$$
(r,s;b,c)
\tag{5.28}
$$

such that $r,s$ are coprime, $b,c$ are positive, and (5.26) holds. If $b$ is odd,
$r,s$ have opposite parity; if $b$ is even, they are both odd. This is the promised
initial carrier. The remaining argument concerns carriers only; the original variables
need not be recovered.

### 5.7 Why this is the right carrier

The carrier equations retain exactly the information needed for another extraction.
The equality $F(r,s)=c^5$ is an absolute-norm statement, but it is accompanied by
the much stronger ramified difference

$$
r-s=5b^5.
$$

That difference has three jobs. First, it fixes the residue relation
$r\equiv s\not\equiv0\pmod5$, which will determine the real unit class in the next
norm factorization. Second, it singles out the positive integer $b$ that will serve as
the well-founded measure. Third, it makes the square $(r-s)^2$ a fifth-power square,

$$
(r-s)^2=25b^{10},
$$

and this is precisely the quantity isolated by the coordinate combination
$11\mathcal Q-5\mathcal P$ in Chapter 6.

The parity branches are also structural. An algebraic integer of $\mathcal O^+$ lies
either in $\mathbf Z[\pi]$ or in the coset represented by $(1+\pi)/2$. Fifth powers
preserve the distinction relevant to our equations, as the congruence modulo $32$ in
(5.14) shows. When the original pair has opposite parity, the first real-quadratic
fifth root uses the half-integral lattice and produces an opposite-parity carrier. When
the original pair is both odd, the fifth root uses the integral lattice and produces
a both-odd carrier. The carrier definition includes both because replacement can move
between them.

There is no need to retain $a$ after (5.27). Relation (5.27) records how $b,c$ arose,
but the replacement uses only coprimality, positivity, and the two equations in
(5.26). This is an advantage rather than a loss: closure is proved for every carrier,
not merely for carriers whose ancestry can still be recognized as a Fermat triple.
Consequently iteration never needs to reverse the construction of Chapter 5.

The choice of $b$, rather than $c$ or $|r|+|s|$, as the descent measure is deliberate.
The successor factorization will give $de=b^2$. That relation alone does not decide
which of $d,e$ is smaller. The positive quartic identity will show that $e$ is large
relative to $d$, and therefore that $d<b$. The carrier has been designed so that its
arithmetic factorization and its archimedean inequality meet at the same parameter.

## 6. The carrier replacement

### 6.1 Carrier data and the closure problem

A **quintic carrier** is a quadruple $(r,s;b,c)$ satisfying

$$
\gcd(r,s)=1,
\qquad b,c\in\mathbf Z_{>0},
\tag{6.1}
$$

and

$$
r-s=5b^5,
\qquad
F(r,s)=c^5.
\tag{6.2}
$$

The first equation gives $r\equiv s\not\equiv0\pmod5$. Primitivity leaves exactly
two parity types. If $b$ is odd, then $r-s$ is odd and $r,s$ have opposite parity.
If $b$ is even, then $r-s$ is even and $r,s$ are both odd. The replacement must be
closed in both types.

Our goal is precise:

**Replacement goal.** From every carrier $(r,s;b,c)$, construct another carrier
$(r_1,s_1;d,e)$ with

$$
0<d<b.
\tag{6.3}
$$

Closure requires four separate checks: the two new equations, positivity, coprimality,
and the correct integral parity. Strictness is a fifth check. We now derive all five
from explicit identities.

### 6.2 The second norm identity

Set

$$
S=r+s,
\qquad
R=r^2+s^2.
\tag{6.4}
$$

If $r,s$ have opposite parity, then $S,R$ are odd. If $r,s$ are both odd, then
$S,R$ are even and $R/2$ is odd. Identity (2.9) and $F(r,s)=c^5$ give

$$
S^4-5R^2=-4c^5.
\tag{6.5}
$$

Therefore

$$
\alpha=\frac{S^2+R\pi}{2}\in\mathcal O^+
\tag{6.6}
$$

has norm

$$
N_{K^+/\mathbf Q}(\alpha)=-c^5.
\tag{6.7}
$$

As before, $\alpha$ and $\bar\alpha$ are coprime. A common odd divisor of $S$ and
$R$ would give $r\equiv-s$ and $R\equiv2s^2$, contradicting
$\gcd(r,s)=1$. Also $5\nmid S$, because
$r\equiv s\not\equiv0\pmod5$. Thus no common prime ideal lies away from the primes
above $2$ and $5$, and the prime above $5$ is excluded by $5\nmid S$.

In the opposite-parity pattern, $S$ is odd. A common prime above $2$ would divide
$\alpha+\bar\alpha=S^2$, an odd rational integer, so it is impossible. This disposes
of the prime $2$ in that branch without any coordinate division.

If $r,s$ are both odd, write $S=2S_0$ and $R=2R_0$. Then
$\alpha=2S_0^2+R_0\pi$, with $R_0$ odd. Modulo $2\mathcal O^+$ this reduces to
$1$, because $\pi=2\eta-1\equiv1$. Hence no prime above $2$ divides $\alpha$.

Since $\mathcal O^+$ is a PID, there are $\beta\in\mathcal O^+$ and a unit $u$
such that

$$
\alpha=u\beta^5.
\tag{6.8}
$$

Unlike the first real-quadratic factor, $\alpha$ is not deeply rational: its
$\pi$-coefficient is a unit. The unit in (6.8) is not a fifth power. Its exact class
must be computed.

### 6.3 The forced unit class

Write the unit modulo fifth powers as

$$
u=\eta^j,
\qquad 0\le j<5,
\tag{6.9}
$$

after absorbing a sign and a fifth power of $\eta$ into $\beta^5$. We determine $j$
in the quotient $\mathcal O^+/(\pi^2)$, where $\pi^2=5$.

Every fifth power in $\mathcal O$ is rational modulo $5\mathcal O$, so
$\beta^5$ is congruent to a nonzero rational residue modulo $\pi^2$. Also

$$
\eta^j=2^{-j}(1+\pi)^j
\equiv2^{-j}(1+j\pi)\pmod{\pi^2}.
\tag{6.10}
$$

For a unit written as a nonzero constant times $1+k\pi$, the ratio of its
$\pi$-coefficient to its constant coefficient is $k$ in $\mathbf F_5$. Comparing
(6.6), (6.8), and (6.10) gives

$$
j\equiv\frac{R}{S^2}\pmod5.
\tag{6.11}
$$

But $r\equiv s\not\equiv0\pmod5$, so

$$
R\equiv2r^2,
\qquad
S^2\equiv4r^2,
\qquad
\frac{R}{S^2}\equiv\frac12\equiv3\pmod5.
$$

Thus the unit class is forced:

$$
\boxed{\alpha=\eta^3\beta^5.}
\tag{6.12}
$$

There is no second state and no choice of root-of-unity exponent. The same calculation
will apply to every successor because the defining equation of a carrier again gives
$r_1\equiv s_1\not\equiv0\pmod5$.

### 6.4 Absorbing the unit and fixing parity

The exponent three in (6.12) is designed to be absorbed after multiplying by
$\eta^2$:

$$
\eta^2\alpha=(\eta\beta)^5.
\tag{6.13}
$$

Since $\eta^2=(3+\pi)/2$, direct multiplication gives

$$
\eta^2\alpha=\frac{\mathcal P+\mathcal Q\pi}{2},
\tag{6.14}
$$

where

$$
\mathcal P=4r^2+3rs+4s^2,
\qquad
\mathcal Q=2r^2+rs+2s^2.
\tag{6.15}
$$

Put $\gamma=\eta\beta$. The parity of $r,s$ now determines which integral lattice
contains $\gamma$.

If $r,s$ have opposite parity, then $\mathcal P,\mathcal Q$ are even, so the right
side of (6.14) lies in $\mathbf Z[\pi]$. In this branch

$$
\boxed{\gamma=M+N\pi}
\tag{6.16}
$$

for integers $M,N$. To justify the claim, suppose instead that
$\gamma=(m+n\pi)/2$ with $m,n$ odd. Its fifth power is

$$
\gamma^5=\frac{A+B\pi}{32},
$$

where

$$
\begin{aligned}
A&=m^5+50m^3n^2+125mn^4,\\
B&=5m^4n+50m^2n^3+25n^5.
\end{aligned}
$$

For odd $m,n$, reduction modulo $32$ gives
$A\equiv B\equiv16\pmod{32}$. Both coordinates of $\gamma^5$ would be
half-integral, a contradiction.

If $r,s$ are both odd, then $\mathcal P,\mathcal Q$ are odd, so the right side of
(6.14) has half-integral coordinates. In this branch

$$
\boxed{\gamma=\frac{M+N\pi}{2}}
\tag{6.17}
$$

with $M,N$ odd. An element of $\mathbf Z[\pi]$ cannot have a fifth power with
half-integral coordinates, so this is the only possible parity.

In either branch, $(\gamma)$ and $(\bar\gamma)$ are coprime because they differ from
$(\beta)$ and $(\bar\beta)$ only by units. Thus

$$
\gcd(M,N)=1,
\qquad 5\nmid M.
\tag{6.18}
$$

### 6.5 The coordinate engine

Define the two fifth-power coordinate polynomials

$$
\begin{aligned}
A(M,N)&=M^5+50M^3N^2+125MN^4,\\
B(M,N)&=5N\bigl(M^4+10M^2N^2+5N^4\bigr).
\end{aligned}
\tag{6.19}
$$

Expanding $\gamma^5$ in the two parity branches gives

$$
\begin{array}{c|c|c}
r,s\text{ of opposite parity}
& A=\mathcal P/2 & B=\mathcal Q/2,\\
r,s\text{ both odd}
& A=16\mathcal P & B=16\mathcal Q.
\end{array}
\tag{6.20}
$$

The powers of two are not cosmetic. They record whether $\gamma$ lies in
$\mathbf Z[\pi]$ or in its nontrivial half-integral coset.

The $5$-adic information is the same in both rows. Write $r=s+5b^5$. Then

$$
\mathcal Q
=2r^2+rs+2s^2
=5\bigl(s^2+5sb^5+10b^{10}\bigr).
\tag{6.21}
$$

The parenthesis is a unit modulo $5$. Since $5\nmid M$, the quartic factor in
$B(M,N)$ is also a unit modulo $5$. Comparing either row of (6.20) gives

$$
5\nmid N.
\tag{6.22}
$$

The decisive linear combination of $\mathcal P$ and $\mathcal Q$ recovers the known
square:

$$
11\mathcal Q-5\mathcal P=2(r-s)^2=50b^{10}.
\tag{6.23}
$$

On the fifth-root side, direct expansion factors the same combination:

$$
11B(M,N)-5A(M,N)=-5(M-N)H(M,N),
\tag{6.24}
$$

where

$$
H(M,N)
=M^4-10M^3N+40M^2N^2-70MN^3+55N^4.
\tag{6.25}
$$

The form has the exact interpretation

$$
\boxed{H(M,N)=F(M-3N,-2N).}
\tag{6.26}
$$

Combining (6.20), (6.23), and (6.24) gives the two parity-scaled product identities

$$
\begin{array}{c|c}
r,s\text{ of opposite parity}
&(N-M)H(M,N)=5b^{10},\\
r,s\text{ both odd}
&(N-M)H(M,N)=160b^{10}.
\end{array}
\tag{6.27}
$$

Every coefficient and every power of two in (6.27) has now been derived from the
displayed fifth-power formulas.

### 6.6 Coprimality and fifth-power extraction

We first remove the parity scaling in (6.27) by defining an integer pair. In the
opposite-parity branch put

$$
r_1=-2N,
\qquad
s_1=M-3N.
\tag{6.28}
$$

In the both-odd branch, $M,N$ are odd, so put

$$
r_1=-N,
\qquad
s_1=\frac{M-3N}{2}.
\tag{6.29}
$$

Identity (6.26), homogeneity of $F$, and the two rows of (6.27) give the same
equation in both branches:

$$
\boxed{(r_1-s_1)F(r_1,s_1)=5b^{10}.}
\tag{6.30}
$$

The pair $r_1,s_1$ is primitive. In the first branch, (6.27) has an odd right side,
so $M-N$ is odd and $M,N$ have opposite parity. Hence $r_1$ is even and $s_1$ is
odd. Any odd common divisor would divide both $M$ and $N$. In the second branch,
$r_1=-N$ is odd, and again any common odd divisor of $r_1$ and $s_1$ would divide
$M,N$. Thus

$$
\gcd(r_1,s_1)=1
\tag{6.31}
$$

in both cases.

For every coprime pair $U,V$,

$$
\gcd(U-V,F(U,V))=1,
\tag{6.32}
$$

because $F(U,V)\equiv U^4\pmod{U-V}$. Applying this to $r_1,s_1$ proves that the
two factors in (6.30) are coprime. Moreover $F(r_1,s_1)$ is not divisible by $5$:
by (6.26), it is $H(M,N)$ or $H(M,N)/16$, and

$$
H(M,N)\equiv M^4\not\equiv0\pmod5.
\tag{6.33}
$$

Now inspect an ordinary prime $q$ in (6.30). If $q\ne5$ divides $r_1-s_1$, it does
not divide $F(r_1,s_1)$, so its exponent in the difference equals its exponent in
$b^{10}=(b^2)^5$ and is a multiple of five. The same reasoning applies with the two
factors interchanged. At $q=5$, equation (6.33) places the entire $5$-adic exponent
in $r_1-s_1$; its exponent is congruent to one modulo five. Thus the two factors have
exactly the shapes $5$ times a fifth power and a fifth power. This is ordinary integer
factorization, with no unit beyond the signs.

The form $F$ is positive, so (6.30) also gives $r_1-s_1>0$. Ordinary prime
factorization now yields positive integers $d,e$ such that

$$
\boxed{
r_1-s_1=5d^5,
\qquad
F(r_1,s_1)=e^5.
}
\tag{6.34}
$$

Comparing the product in (6.34) with (6.30) gives

$$
\boxed{de=b^2.}
\tag{6.35}
$$

Positivity removes every sign ambiguity: $F(r_1,s_1)>0$, the product (6.30) is
positive, and hence $r_1-s_1>0$. The positive fifth roots $d,e$ are therefore
canonical. This is why the successor has a well-defined positive parameter rather
than merely an absolute-value class.

### 6.7 The explicit successor

Equations (6.28) and (6.29) give the successor explicitly in the two parity branches:

$$
(r_1,s_1)=
\begin{cases}
(-2N,M-3N),&r,s\text{ have opposite parity},\\
\left(-N,(M-3N)/2\right),&r,s\text{ are both odd}.
\end{cases}
\tag{6.36}
$$

Equations (6.31) and (6.34) prove closure: $(r_1,s_1;d,e)$ is again a quintic
carrier. Its own parity is automatically one of the two allowed types. Every component
of the successor is explicit, including the factor of two required in each branch.
What remains is to prove that its positive parameter $d$ is strictly smaller than
$b$.

### 6.8 How the replacement identities fit together

The replacement may be read as a sequence of forced design choices. This perspective
is useful because each apparently unusual coefficient solves a specific obstruction.

The first obstruction is the unit in the norm factorization. Modulo $\pi^2$, the
ratio of the irrational and rational coordinates of $\alpha$ is always $3$. Thus the
unit is $\eta^3$ modulo fifth powers. Multiplication by $\eta^2$ is then forced by

$$
\eta^2\eta^3=\eta^5.
$$

It turns the unit-bearing equation into the exact fifth power
$\eta^2\alpha=(\eta\beta)^5$. The quadratic forms $\mathcal P,\mathcal Q$ in
(6.15) are simply the two coordinates of this product; they were not guessed to make
a later factorization work.

The second obstruction is recovering the old ramified parameter from those two
coordinates. Solving for constants $A,B$ such that

$$
A\mathcal Q+B\mathcal P
$$

is a multiple of $(r-s)^2$ gives, after removing a common scalar, the combination
$11\mathcal Q-5\mathcal P$. Indeed,

$$
11(2r^2+rs+2s^2)-5(4r^2+3rs+4s^2)
=2(r-s)^2.
$$

Because $r-s=5b^5$, this coordinate combination is already $50b^{10}$. It is the
bridge from a quadratic coordinate calculation to a product of fifth-power-shaped
integers.

The third obstruction is closure in the quartic form $F$. Substituting the fifth-power
coordinates $A(M,N),B(M,N)$ into the same linear combination gives

$$
11B-5A=-5(M-N)H(M,N).
$$

The remaining quartic is not merely positive; it is exactly a linear transform of the
original norm form:

$$
H(M,N)=F(M-3N,-2N).
$$

This identity dictates the successor coordinates. In the integral lattice they are
$(-2N,M-3N)$. In the half-integral lattice both displayed arguments are even, so they
must be divided by two, giving $(-N,(M-3N)/2)$. The factors $1$ and $1/16$ in the
quartic values match the factors $1$ and $1/2$ in the differences, which is why both
branches reduce to the single product (6.30).

Finally, primitive integer factorization does the only extraction left. Because
$r_1-s_1$ and $F(r_1,s_1)$ are coprime and only the former is divisible by $5$, the
product $5b^{10}$ forces

$$
r_1-s_1=5d^5,
\qquad
F(r_1,s_1)=e^5.
$$

Thus the unit calculation, the linear combination, the quartic change of variables,
and the parity scaling each have a separate role. Omitting any one of them would leave
either a unit ambiguity, an unrecognized factor, or a nonprimitive successor.

## 7. Strict well-founded descent

### 7.1 The positive quartic identity

A replacement is not a descent until it comes with a strict well-founded measure.
Here the measure is simply the positive integer $b$ in the equation $r-s=5b^5$.
Strictness comes from identity (2.10), which we restate as a lemma.

**Lemma 7.1 (quartic separation).** For real $U,V$ not both zero,

$$
5F(U,V)>(U-V)^4.
\tag{7.1}
$$

**Proof.** Expansion gives

$$
\begin{aligned}
16\bigl(5F(U,V)-(U-V)^4\bigr)
={}&5(U+V)^4\\
&+50(U+V)^2(U-V)^2+9(U-V)^4.
\end{aligned}
\tag{7.2}
$$

The right side is a sum of nonnegative terms. If it vanished, both $U+V$ and
$U-V$ would vanish, so $U=V=0$. $\square$

The identity is tailored to the carrier: its left side compares the quartic value
$F(U,V)$ with the fourth power of the very difference that carries the ramified
factor $5$.

No approximate lower bound is being smuggled into the proof. The right side of (7.2)
can be read as

$$
5\bigl((U+V)^2\bigr)^2
+2\bigl(5(U+V)(U-V)\bigr)^2
+\bigl(3(U-V)^2\bigr)^2.
$$

It is therefore an explicit sum of three squares. Strict positivity fails only when
both the sum and difference of $U,V$ vanish. This exact form is stronger than merely
knowing that $F$ is positive: positivity of $F$ would control its sign, but (7.1)
compares it quantitatively with the fourth power of the carrier difference.

### 7.2 Strict decrease of the carrier

Apply Lemma 7.1 to the successor pair $(r_1,s_1)$. Equation (6.34) gives

$$
5e^5>(5d^5)^4,
$$

and hence

$$
e^5>5^3d^{20}.
\tag{7.3}
$$

Multiply by $d^5$ and use $de=b^2$ from (6.35):

$$
b^{10}=d^5e^5>5^3d^{25}.
\tag{7.4}
$$

If $d\ge b$, then, since $b\ge1$,

$$
5^3d^{25}\ge5^3b^{25}>b^{10},
$$

contradicting (7.4). Therefore

$$
\boxed{0<d<b.}
\tag{7.5}
$$

We can now state the replacement theorem in its final form.

**Theorem 7.2 (quintic carrier replacement).** Every quintic carrier
$(r,s;b,c)$ has an explicitly constructed successor

$$
(r_1,s_1;d,e),
\tag{7.6}
$$

that is again a quintic carrier and satisfies $0<d<b$. Its pair $(r_1,s_1)$ is the
parity-dependent expression in (6.36), and $d,e$ are the positive fifth roots in
(6.34).

**Proof.** Sections 6.2--6.6 construct $M,N,d,e$ and prove the exact successor
equations. Section 6.7 proves primitivity and parity. Equation (7.5) proves strictness.
$\square$

### 7.3 Iteration and contradiction

Suppose a carrier exists. Among all positive integers that occur as its parameter
$b$, choose a least one. Theorem 7.2 constructs another carrier with positive
parameter $d<b$, contradicting minimality.

This minimality argument quantifies over carriers, not over Fermat triples. That
distinction is essential. The successor need not come with integers $x_1,y_1,z_1$
whose fifth powers satisfy the original Fermat equation; closure was deliberately
proved in the larger but rigid carrier family. Since the initial Fermat solution
produces one carrier and every carrier produces another, minimality in that family is
enough.

Equivalently, repeated replacement would create

$$
b_0>b_1>b_2>\cdots>0,
\tag{7.7}
$$

an impossible strictly decreasing sequence of positive integers. This is an infinite
descent in the well-founded sense: every alleged carrier has a successor, and the
ordinary order on $\mathbf Z_{>0}$ admits no infinite descending chain.

At every iteration the full hypothesis is re-established. The new pair is primitive
by (6.31). Its quartic value is a positive fifth power and its difference is exactly
$5$ times a positive fifth power by (6.34). If the new difference is odd, the next
root lies in the integral coordinate branch; if it is even, the next root lies in the
half-integral branch. In either event Section 6.3 recalculates the unit class as
$\eta^3$. No property is inherited merely because the successor resembles its
predecessor.

Notice what is not being used. We do not claim that the absolute values of $r$ and
$s$ decrease. We do not choose a smallest algebraic norm. We do not infer a new
equation from a norm equality alone. The measure is the explicit positive fifth-root
parameter in the ramified difference, and inequality (7.2) proves its strict decrease.

The strictness also rules out a fixed point. If a carrier returned to itself up to
signs or interchange of its two integer entries, its positive parameter would have to
remain $b$. But every replacement has parameter $d<b$. Thus the contradiction does
not depend on analyzing possible cycles among the algebraic fifth roots.

### 7.4 The second-case theorem

We can close the second case.

**Theorem 7.3 (second case).** There is no primitive nonzero solution of

$$
x^5+y^5=z^5
$$

for which $5\mid xyz$.

**Proof strategy.** Orient the unique variable divisible by $5$ on the right.
Cyclotomic extraction gives the rational shapes (4.8). The first real-quadratic norm
equation gives an initial carrier. The replacement theorem contradicts the existence
of any carrier.

**Proof.** Pairwise coprimality shows that exactly one variable is divisible by $5$.
After a signed permutation, assume (4.1). Sections 4.1--4.4 give

$$
x+y=5^4a^5,
\qquad
F(x,y)=5w^5.
$$

Sections 5.2--5.6 construct from these equations a quintic carrier
$(r,s;b,c)$. Theorem 7.2 produces a strictly smaller carrier, contradicting the
least-positive-integer principle as in Section 7.3. $\square$

The proof has now supplied the missing logical bridge between a smaller expression and
a descent. The carrier is closed, the successor is explicit, and strictness is an
identity rather than an assertion about unspecified coordinate carries.

## 8. Fermat's theorem at exponent five

### 8.1 The primitive nonzero theorem

We first state the result in the symmetric form requested by the two-case analysis.

**Theorem 8.1 (primitive exponent-five theorem).** There is no primitive nonzero
integer solution of

$$
x^5+y^5+z^5=0.
\tag{8.1}
$$

**Proof.** If $5\nmid xyz$, move one signed fifth power to the right. The resulting
equation is a primitive first-case equation, contradicted by Theorem 3.2 or by the
cyclotomic proof in Sections 3.4--3.6.

If $5\mid xyz$, pairwise coprimality says that exactly one variable is divisible by
$5$. Permute the signed terms so that this variable is moved to the right. The result
is a primitive second-case equation, contradicted by Theorem 7.3. These alternatives
are exhaustive. $\square$

This proof treats signs intrinsically. No positivity assumption on $x,y,z$ is hidden
in either case.

### 8.2 All integer and rational solutions

**Proof of Theorem 1.1.** Suppose (1.1) holds. If all variables are nonzero, divide
by their positive greatest common divisor to obtain a primitive nonzero solution,
contrary to Theorem 8.1. Hence $xyz=0$. $\square$

The zero-coordinate solutions of the symmetric equation are exactly the permutations
of

$$
(t,-t,0),
\qquad t\in\mathbf Z.
\tag{8.2}
$$

For the oriented equation $X^5+Y^5=Z^5$, they are

$$
(t,0,t),
\qquad
(0,t,t),
\qquad
(t,-t,0).
\tag{8.3}
$$

Indeed, the fifth-power map is injective on $\mathbf Z$.

Clearing denominators gives the rational version.

**Corollary 8.2.** If $x,y,z\in\mathbf Q$ and $x^5+y^5+z^5=0$, then
$xyz=0$.

**Proof.** Multiply by the fifth power of a common positive denominator and apply
Theorem 1.1. $\square$

### 8.3 Exponents divisible by five

The exponent-five theorem also removes every exponent divisible by five.

**Corollary 8.3.** Let $n=5m$ with $m\ge1$. If

$$
x^n+y^n=z^n,
\qquad x,y,z\in\mathbf Z,
$$

then $xyz=0$.

**Proof.** Put $X=x^m$, $Y=y^m$, and $Z=z^m$. Then
$X^5+Y^5=Z^5$. Theorem 1.1 gives $XYZ=0$, hence $xyz=0$. $\square$

No primality assumption on $n$ is needed. The result follows by substitution, not by
rerunning the descent.

## 9. Proof integrity and the reusable descent package

### 9.1 The ideal and norm ledgers

The proof uses ideals and norms for different purposes. The ideal ledger is:

$$
\begin{array}{c}
\text{coprime cyclotomic factors away from }\mathfrak p\\
\Downarrow\\
\text{individual prime-ideal exponents divisible by five}\\
\Downarrow\\
x+\zeta y=u\lambda A^5\\
\Downarrow\\
x+\zeta y=\lambda A^5.
\end{array}
\tag{9.1}
$$

Only after the last line is proved do we take its norm. Thus

$$
F(x,y)=5N(A)^5
$$

is a consequence of an exact element equation, not a premise from which prime-ideal
distribution is guessed.

The real-quadratic norm equations are handled with the same discipline. Before
writing $\alpha=u\beta^5$, we prove that $(\alpha)$ and $(\bar\alpha)$ are coprime.
Their product being a fifth power then forces each ideal to be a fifth power, and
Euclideanity makes its root principal. Neither occurrence of a real-quadratic fifth
root is obtained from the numerical norm alone.

### 9.2 The valuation and unit ledgers

Every appearance of the prime $5$ has one of three normalizations:

$$
v_5(5)=1,
\qquad
v_{\mathfrak p}(5)=4,
\qquad
v_{(\pi)}(5)=2.
\tag{9.2}
$$

The first is the ordinary integer valuation. The second belongs to the quartic field
$K$ and explains $t+1=5s$. The third belongs to $K^+$ and is used in the congruence
modulo $\pi^2=5$ that determines the unit $\eta^3$. The proof never transfers a value
between these scales without the corresponding ramification factor.

There are likewise three distinct unit steps:

1. in the first case, primary normalization makes the unit real but does not make it
   a fifth power;
2. in the ramified cyclotomic factor and in the first real-quadratic factor, rationality
   modulo $\lambda^3$ makes the unit a fifth power;
3. in the carrier replacement, the unit is not a fifth power, and comparison modulo
   $\pi^2$ forces its exact class $\eta^3$ before multiplication by $\eta^2$ absorbs
   it.

The third step is especially important. The unit class is recomputed from
$r\equiv s\pmod5$ for every carrier. Closure does not depend on an alternating or
freely chosen state.

### 9.3 Why the replacement is closed

For reference, the replacement certificate is the following exact chain. A carrier
satisfies

$$
r-s=5b^5,
\qquad
F(r,s)=c^5.
$$

The coprime norm factor

$$
\frac{(r+s)^2+(r^2+s^2)\pi}{2}
$$

has norm $-c^5$ and exact unit class $\eta^3$. After multiplying by $\eta^2$, it is

$$
\frac{\mathcal P+\mathcal Q\pi}{2}=\gamma^5,
$$

with

$$
\mathcal P=4r^2+3rs+4s^2,
\qquad
\mathcal Q=2r^2+rs+2s^2.
$$

There are two exact coordinate lattices:

$$
\gamma=
\begin{cases}
M+N\pi,&r,s\text{ of opposite parity},\\
(M+N\pi)/2,&r,s\text{ both odd}.
\end{cases}
$$

The identity

$$
11\mathcal Q-5\mathcal P=2(r-s)^2
$$

and the fifth-power expansion give the parity-scaled products in (6.27). Dividing
their exact powers of two defines

$$
(r_1,s_1)=
\begin{cases}
(-2N,M-3N),&r,s\text{ of opposite parity},\\
\left(-N,(M-3N)/2\right),&r,s\text{ both odd}.
\end{cases}
$$

In both rows one obtains the same primitive integer identity

$$
(r_1-s_1)F(r_1,s_1)=5b^{10}.
$$

Coprimality and the exact residue at $5$ then give

$$
r_1-s_1=5d^5,
\qquad
F(r_1,s_1)=e^5,
\qquad
de=b^2.
$$

Finally,

$$
16\bigl(5F(r_1,s_1)-(r_1-s_1)^4\bigr)
$$

is the positive expression in (7.2), and it forces $0<d<b$. This certificate contains
an equation for every transition and a strict positive-integer measure.

### 9.4 Dependency closure

The proof has one direct mathematical dependency: Book 162. Its imported statements
are limited and can be listed exactly.

1. The quartic cyclotomic ring is $\mathcal O=\mathbf Z[\zeta]$, is a PID, and has
   the unique prime $\mathfrak p=(1-\zeta)$ above $5$ with
   $5=\zeta^3\eta^2\lambda^4$.
2. Its units are $\pm\zeta^a\eta^n$, primary units are real, and a unit rational
   modulo $\lambda^3$ is a fifth power.
3. Distinct primitive linear factors $U+\zeta^iV$ are coprime away from
   $\mathfrak p$, and their ramified valuations are those in (2.14).
4. Every integral fifth power is rational modulo $5\mathcal O$, and the absolute norm
   of $U+\zeta V$ is $F(U,V)$.

Each imported assertion is used with the same hypotheses and normalization as in Book
162. In particular, class number one is used only after prime-ideal exponents have
been isolated, and the fifth-power unit criterion is used only for a unit already
known to accompany an ideal fifth power.

Everything specific to the descent is proved in the present book. Lemma 5.1 proves
that $\mathbf Z[\eta]$ is Euclidean, so no class-number assertion about the real
subfield is imported. The coprimality of each pair of real conjugate factors is proved
from the displayed integer gcds. Both real-unit calculations are explicit: the first
unit is killed by the three-digit criterion, while the second is computed as
$\eta^3$ modulo fifth powers. The coordinate polynomials, their parity scalings, the
factorization through $H(M,N)$, and the strict quartic inequality are all established
here by exact identities.

No later book enters the proof. In particular, the exponent-five conclusion does not
use Frey curves, modularity lifting, a classification of rational points, or a theorem
that already contains Fermat's equation as a special case. This is why the conclusion
can serve as the independent coefficient-five endpoint for the later global assembly.

### 9.5 What has been proved

The first case has been proved twice: by the nonzero fifth-power residues modulo $25$
and by primary cyclotomic normalization followed by a conjugate-difference calculation.
The second case begins with the exact Book 162 factor

$$
x+\zeta y=\lambda A^5.
$$

Its norm and rational companion have the rigid shapes

$$
F(x,y)=5w^5,
\qquad
x+y=5^4a^5.
$$

The first real-quadratic norm identity turns these shapes into a carrier. The second
real-quadratic norm identity, its forced unit $\eta^3$, and the exact coordinate
factorization produce a successor carrier. The quartic separation identity makes the
new positive parameter strictly smaller. Well-foundedness rules out the initial
carrier and therefore the second case.

The two real-quadratic passages should be distinguished. In the first, the irrational
coordinate is so deeply divisible by $5$ that the accompanying real unit is itself a
fifth power; this passage creates the carrier. In the second, the irrational coordinate
is a unit modulo $5$, so the unit survives with the forced class $\eta^3$; multiplication
by $\eta^2$ turns it into a fifth power and drives the replacement. Treating these two
unit calculations as interchangeable would lose the exact successor.

Parity is equally part of the theorem rather than an editorial detail. A primitive
second-case solution may place either the unique even variable or an odd variable at
the position divisible by $5$. The half-integral and integral coordinate branches in
Chapters 5 and 6 cover both possibilities. Their powers of two cancel in the common
identity

$$
(r_1-s_1)F(r_1,s_1)=5b^{10},
$$

so the same descent measure works in both branches.

It follows that every primitive nonzero solution of

$$
x^5+y^5+z^5=0
$$

is impossible. Hence Fermat's equation at exponent five has only the trivial integer
solutions, and the same is true over $\mathbf Q$ and for every exponent divisible by
five. This completes the coefficient-five boundary using only the cyclotomic
arithmetic of Book 162 and the explicit descent developed here.

The endpoint is therefore genuinely classical and self-contained relative to its
declared prerequisite: the exceptional prime is measured, every unit is accounted
for, both parity lattices are carried through the replacement, and the descent ends
in the well-founded order of positive integers.
No unproved recurrence or numerical coincidence remains at the decisive step of the
argument. Every displayed decrease follows from a positive identity over the ordinary
integers.
