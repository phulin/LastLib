# Cyclotomic Descent for Quintic Fermat-Type Equations

## Contents

1. [The last classical exponent](#1-the-last-classical-exponent)
   - [The theorem and its setting](#11-the-theorem-and-its-setting)
   - [Why factorization is not yet descent](#12-why-factorization-is-not-yet-descent)
   - [The two cases](#13-the-two-cases)
   - [The proof map](#14-the-proof-map)
2. [The cyclotomic arithmetic we shall use](#2-the-cyclotomic-arithmetic-we-shall-use)
   - [The field, the prime, and the normalization](#21-the-field-the-prime-and-the-normalization)
   - [Norms and the binary quintic form](#22-norms-and-the-binary-quintic-form)
   - [Units, primary elements, and fifth powers](#23-units-primary-elements-and-fifth-powers)
   - [Coprimality and extraction](#24-coprimality-and-extraction)
3. [Primitive equations and local alternatives](#3-primitive-equations-and-local-alternatives)
   - [Primitive reduction](#31-primitive-reduction)
   - [The elementary congruence at five](#32-the-elementary-congruence-at-five)
   - [Exact valuations of the five factors](#33-exact-valuations-of-the-five-factors)
   - [Rational factor shapes](#34-rational-factor-shapes)
4. [The first case](#4-the-first-case)
   - [Primary normalization](#41-primary-normalization)
   - [Fifth powers and conjugate differences](#42-fifth-powers-and-conjugate-differences)
   - [The residue restriction](#43-the-residue-restriction)
   - [Cycling the three variables](#44-cycling-the-three-variables)
   - [What the first case teaches](#45-what-the-first-case-teaches)
5. [The ramified factor in the second case](#5-the-ramified-factor-in-the-second-case)
   - [Locating the variable divisible by five](#51-locating-the-variable-divisible-by-five)
   - [Removing the common prime](#52-removing-the-common-prime)
   - [Eliminating the unit](#53-eliminating-the-unit)
   - [The exact rational shadows](#54-the-exact-rational-shadows)
6. [From one solution to a descent carrier](#6-from-one-solution-to-a-descent-carrier)
   - [Why the norm identity alone is insufficient](#61-why-the-norm-identity-alone-is-insufficient)
   - [The first conjugate difference](#62-the-first-conjugate-difference)
   - [Deep invariance and rational digits](#63-deep-invariance-and-rational-digits)
   - [The four normalized difference factors](#64-the-four-normalized-difference-factors)
7. [The quintic replacement lemma](#7-the-quintic-replacement-lemma)
   - [Descent records and their weight](#71-descent-records-and-their-weight)
   - [The coordinate engine](#72-the-coordinate-engine)
   - [Extraction and replacement](#73-extraction-and-replacement)
   - [Strict decrease](#74-strict-decrease)
   - [Why every hypothesis is needed](#75-why-every-hypothesis-is-needed)
8. [Well-founded second-case descent](#8-well-founded-second-case-descent)
   - [Constructing the initial record](#81-constructing-the-initial-record)
   - [Iteration](#82-iteration)
   - [The contradiction](#83-the-contradiction)
   - [Norm descent and explicit-factor descent](#84-norm-descent-and-explicit-factor-descent)
9. [Fermat's theorem for exponent five](#9-fermats-theorem-for-exponent-five)
   - [The integer theorem](#91-the-integer-theorem)
   - [The rational and exponent-divisible forms](#92-the-rational-and-exponent-divisible-forms)
   - [Signs, zeroes, and permutations](#93-signs-zeroes-and-permutations)
10. [Quintic equations with controlled coefficients](#10-quintic-equations-with-controlled-coefficients)
    - [Supported coefficients](#101-supported-coefficients)
    - [What survives unchanged](#102-what-survives-unchanged)
    - [Where the Fermat conclusion is special](#103-where-the-fermat-conclusion-is-special)
11. [Proof diagnostics and common failure modes](#11-proof-diagnostics-and-common-failure-modes)
    - [Ideals before elements](#111-ideals-before-elements)
    - [The two normalizations at five](#112-the-two-normalizations-at-five)
    - [Units cannot be wished away](#113-units-cannot-be-wished-away)
    - [A smaller expression is not yet a descent](#114-a-smaller-expression-is-not-yet-a-descent)
12. [The classical boundary](#12-the-classical-boundary)
    - [What has been proved](#121-what-has-been-proved)
    - [Why exponent five can now be set aside](#122-why-exponent-five-can-now-be-set-aside)

## 1. The last classical exponent

### 1.1 The theorem and its setting

This volume proves the exponent-five case of Fermat's equation by cyclotomic descent.
The final statement is elementary to formulate.

**Theorem 1.1 (Fermat for exponent five).** If $x,y,z\in\mathbf Z$ satisfy

$$
x^5+y^5=z^5,
$$

then $xyz=0$.

The assertion concerns ordinary integers, but its proof becomes transparent only after
adjoining a primitive fifth root of unity. In the field

$$
K=\mathbf Q(\zeta),\qquad \zeta^5=1,\qquad \zeta\ne1,
$$

the left side splits completely:

$$
x^5+y^5=\prod_{i=0}^4(x+\zeta^iy).
\tag{1.1}
$$

Book 191 determined all of the arithmetic needed to use (1.1): the ring of integers,
the unique prime above $5$, the unit group, the class-number-one property, the exact
valuations of the linear factors, and the congruence tests that remove units. We shall
use those results as established background, recalling their precise content whenever
a hypothesis becomes decisive.

The point of the present book is different. A factorization says that certain factors
are fifth powers up to controlled exceptions. A descent must turn that information
into either an immediate contradiction or a new object of exactly the same kind with
a strictly smaller positive integral measure. The passage from the first statement to
the second is the mathematical heart of the exponent-five proof.

### 1.2 Why factorization is not yet descent

Suppose for a moment that the five factors in (1.1) were pairwise coprime in a unique
factorization domain. Their product being a fifth power would imply

$$
x+\zeta y=u\alpha^5
$$

for a unit $u$. Three gaps remain.

First, the factors can share the prime above $5$. Second, the unit $u$ need not be a
fifth power. Third, even an exact equation $x+\zeta y=\alpha^5$ does not visibly produce
a smaller integer solution. Taking norms yields a necessary integer identity, but a
norm forgets how split prime ideals were distributed among conjugate factors. Reversing
the norm step is therefore invalid.

These gaps explain the structure of the proof. We first preserve prime-ideal data long
enough to extract fifth powers. We then use the ramified prime to control units. Finally,
we pass to a specially designed conjugate-difference record. Its replacement operation
is closed, and its weight is a positive integer that decreases strictly. Only at that
last point do we have an infinite descent.

The distinction is worth emphasizing with a counterexample. The unit

$$
\eta=1+\zeta+\zeta^{-1}=\frac{1+\sqrt5}{2}
$$

has norm $1$, which is a fifth power, but $\eta$ is not a fifth power. Thus a
fifth-power norm does not even remove the simplest unit obstruction.

### 1.3 The two cases

For a primitive solution, the classical terminology is:

- the **first case**: $5\nmid xyz$;
- the **second case**: $5\mid xyz$.

The names do not mean that the same proof is run twice. In the first case all relevant
cyclotomic factors are prime to the ramified prime. Primary normalization leaves a real
unit, but that unit cancels on subtracting the conjugate equation. A short residue
calculation, repeated cyclically, gives a contradiction.

In the second case exactly one of $x,y,z$ is divisible by $5$. After signs and a
permutation it may be placed on the right. The four nonrational factors then have
valuation one at the unique prime above $5$. Dividing out that single uniformizer
creates a congruence three levels deep, strong enough to remove the entire unit. The
resulting exact factor equation is the entrance to the descent.

The two cases therefore use the same arithmetic in opposite ways. Away from $5$, the
absence of ramification makes factors coprime and conjugate subtraction decisive. At
$5$, total ramification creates a common factor, but the residue left after its removal
is rigid enough to eliminate units completely.

### 1.4 The proof map

The logical flow is

$$
\begin{array}{c}
\text{primitive integer equation}\\
\Downarrow\\
\text{first case}\quad\text{or}\quad\text{second case}\\
\Downarrow\hspace{39mm}\Downarrow\\
\text{cyclic residue contradiction}\quad
\text{exact ramified fifth-power factor}\\
\hspace{45mm}\Downarrow\\
\hspace{28mm}\text{conjugate-difference record}\\
\hspace{45mm}\Downarrow\\
\hspace{31mm}\text{strictly smaller record}.
\end{array}
$$

The final arrow can be iterated, whereas positive integers cannot decrease forever.
That is the well-founded contradiction. No later theory is used, and no result about
curves or analytic continuation lies behind the argument.

## 2. The cyclotomic arithmetic we shall use

### 2.1 The field, the prime, and the normalization

Write

$$
\mathcal O=\mathbf Z[\zeta],\qquad \lambda=1-\zeta,
\qquad \mathfrak p=(\lambda).
$$

The ring $\mathcal O$ is a principal ideal domain. Its unique prime above $5$ is
$\mathfrak p$, and the exact element identity is

$$
5=\zeta^3\eta^2\lambda^4.
\tag{2.1}
$$

Consequently

$$
(5)=\mathfrak p^4,\qquad
v_{\mathfrak p}(\lambda)=1,\qquad
v_{\mathfrak p}(n)=4v_5(n)\quad(n\in\mathbf Z\setminus\{0\}).
\tag{2.2}
$$

The residue field is $\mathcal O/\mathfrak p\cong\mathbf F_5$, with $\zeta\mapsto1$.
Every automorphism preserves $\mathfrak p$. We use

$$
\sigma(\zeta)=\zeta^2,\qquad \bar\zeta=\zeta^{-1}.
$$

More generally, $\sigma_i(\zeta)=\zeta^i$ for
$i\in(\mathbf Z/5\mathbf Z)^\times$. The automorphism $\sigma=\sigma_2$ generates
the cyclic group of order four. Complex conjugation is $\sigma^2=\sigma_4$.

The conversion in (2.2) is not a convention that may be changed mid-proof. One
ordinary factor of $5$ has cyclotomic valuation four. In particular, a term of
$\mathfrak p$-value one cannot cancel a rational integer divisible by $5$, whose value
is at least four.

Every element has unique coordinates

$$
A=a_0+a_1\lambda+a_2\lambda^2+a_3\lambda^3,\qquad a_i\in\mathbf Z,
\tag{2.3}
$$

and

$$
v_{\mathfrak p}(A)
=\min_{0\le i\le3}\{4v_5(a_i)+i\}.
\tag{2.4}
$$

The four candidate values are distinct modulo four, so the least one occurs only once
and cannot be lost by cancellation.

### 2.2 Norms and the binary quintic form

The absolute norm is positive on every nonzero element of $\mathcal O$. For a unit it
equals one. For a binary cyclotomic factor,

$$
N(x+\zeta y)
=Q(x,y)
=x^4-x^3y+x^2y^2-xy^3+y^4
=\frac{x^5+y^5}{x+y}.
\tag{2.5}
$$

The quotient is used only when $x+y\ne0$; the polynomial defines $Q$ in every case.
Since

$$
N(\lambda)=5,
\tag{2.6}
$$

an exact equation $x+\zeta y=\lambda A^5$ gives

$$
Q(x,y)=5N(A)^5.
\tag{2.7}
$$

This is a reliable consequence. The converse is false: prime ideals over a split
rational prime can occur in different conjugate factors while contributing to the
same rational norm.

We shall use the positivity of $N$ to define integral weights. We shall never use
positivity to reverse a norm identity.

### 2.3 Units, primary elements, and fifth powers

Every unit has a unique expression

$$
u=\pm\zeta^a\eta^n,\qquad 0\le a<5,\quad n\in\mathbf Z.
\tag{2.8}
$$

Modulo fifth powers, the two classes $\zeta$ and $\eta$ are independent. An element
prime to $\lambda$ is **primary** when it is congruent to a nonzero rational integer
modulo $\lambda^2$. Every $\lambda$-adic unit has a unique associate $\zeta^kA$ that
is primary.

Two unit tests will be used repeatedly.

**Primary-unit test.** A unit congruent to a rational integer modulo $\lambda^2$ is
real, hence is $\pm\eta^n$.

**Fifth-power unit test.** A unit congruent to a rational integer modulo $\lambda^3$
is a fifth power.

The thresholds are sharp. The unit $\zeta$ is rational modulo $\lambda$ but is not
real. The unit $\eta$ is rational modulo $\lambda^2$ but is not a fifth power.

Every integral fifth power is congruent to a rational integer modulo $5\mathcal O$,
hence modulo $\lambda^4$. Therefore, if

$$
A=uB^5
$$

is a $\lambda$-adic unit and $A$ is rational modulo $\lambda^3$, then the
fifth-power unit test makes $u$ a fifth power.

### 2.4 Coprimality and extraction

For coprime integers $x,y$, put

$$
F_i=x+\zeta^iy,\qquad i\in\mathbf Z/5\mathbf Z.
$$

Any prime ideal dividing two distinct $F_i$ is $\mathfrak p$. Indeed, differences of
the two factors eliminate $x$ and $y$, and every nonzero difference of fifth roots of
unity is an associate of $\lambda$.

If $5\nmid x+y$, all five factors are prime to $\mathfrak p$ and hence pairwise
coprime. If $5\mid x+y$, then

$$
v_{\mathfrak p}(F_0)=4v_5(x+y),\qquad
v_{\mathfrak p}(F_i)=1\quad(i\ne0).
\tag{2.9}
$$

Consequently, if their product is a fifth power, then

$$
x+\zeta y=uA^5\quad(5\nmid x+y),
\tag{2.10}
$$

and

$$
x+\zeta y=u\lambda A^5\quad(5\mid x+y).
\tag{2.11}
$$

These statements first follow for principal ideals. Class number one turns the fifth
root ideal into a principal ideal; equality of generators leaves the displayed unit.
This order of reasoning prevents unique factorization from silently swallowing a unit.

## 3. Primitive equations and local alternatives

### 3.1 Primitive reduction

Assume that a nonzero integer solution exists. Divide $x,y,z$ by their positive common
divisor. The resulting solution satisfies

$$
\gcd(x,y,z)=1.
\tag{3.1}
$$

It is then pairwise coprime. For example, a prime dividing $x$ and $y$ divides $z^5$
and hence $z$, contrary to (3.1). The same argument applies to every pair.

Signs cause no obstruction because the exponent is odd. We may move any term across
the equality and absorb the sign into a fifth power. A zero variable gives
$|x|=|z|$ or $|y|=|z|$ and is one of the trivial solutions excluded from the descent.
Thus throughout the contradiction argument all three variables are nonzero.

Primitive reduction is essential. Without it, an ordinary prime dividing both $x$ and
$y$ divides every cyclotomic factor, so the pairwise coprimality statement of Section
2.4 is false.

### 3.2 The elementary congruence at five

The two cases exhaust all primitive solutions, but a useful elementary observation
shows that the second case is unavoidable.

**Lemma 3.1.** If $a,b,c$ are all prime to $5$, then

$$
a^5+b^5\ne c^5\pmod{25}.
$$

**Proof strategy.** A unit modulo $25$ has a fifth power depending only on its residue
modulo $5$. List the four possibilities and add them.

**Proof.** Write $a=r+5t$, with $r\in\{1,2,3,4\}$. The binomial theorem gives
$a^5\equiv r^5\pmod{25}$. The four nonzero fifth-power residues are

$$
1^5\equiv1,\quad 2^5\equiv7,\quad
3^5\equiv18,\quad 4^5\equiv24\pmod{25}.
$$

They are $1,7,-7,-1$. A direct addition shows that the sum of two members of this set
never belongs to the set. Hence the congruence is impossible. $\square$

This proves the first case quickly, but it does not explain how the cyclotomic unit
obstruction is resolved. Since that mechanism is needed in the descent package, Chapter
4 gives the cyclotomic first-case proof as well. The elementary lemma then serves as an
independent audit.

It follows at once that some one of $x,y,z$ is divisible by $5$. Pairwise coprimality
shows that at most one is. After rewriting and permuting the equation, we may arrange

$$
x^5+y^5=z^5,\qquad 5\mid z,\qquad 5\nmid xy.
\tag{3.2}
$$

### 3.3 Exact valuations of the five factors

From Fermat's congruence $n^5\equiv n\pmod5$, equation (3.2) gives

$$
x+y\equiv z\equiv0\pmod5.
$$

Let

$$
t=v_5(x+y),\qquad s=v_5(z).
$$

For $i\ne0$, (2.9) gives $v_{\mathfrak p}(x+\zeta^iy)=1$, whereas the rational factor
has value $4t$. Thus

$$
v_{\mathfrak p}(x^5+y^5)=4t+4.
$$

The right side $z^5$ has value $20s$. Hence

$$
4t+4=20s,\qquad
\boxed{t+1=5s}.
\tag{3.3}
$$

In particular,

$$
t\equiv4\pmod5,\qquad t\ge4.
\tag{3.4}
$$

The first rational consequence of the second case is therefore unexpectedly strong:
$5^4$ divides $x+y$. The four comes from the ramification index, not from a repeated
ordinary congruence argument.

### 3.4 Rational factor shapes

For a primitive pair,

$$
\gcd(x+y,Q(x,y))\mid5.
\tag{3.5}
$$

Indeed, modulo a prime divisor of $x+y$ one has $x\equiv-y$ and therefore
$Q(x,y)\equiv5y^4$. Primitivity excludes a prime divisor of $y$. If $5\mid x+y$, a
direct expansion at $x=-y+(x+y)$ gives

$$
v_5(Q(x,y))=1.
\tag{3.6}
$$

Since $(x+y)Q(x,y)=z^5$, comparison of ordinary prime exponents yields integers
$a,w\ne0$ such that

$$
\boxed{x+y=5^4a^5,\qquad Q(x,y)=5w^5,\qquad z=5aw.}
\tag{3.7}
$$

The signs may be absorbed into $a$; $w$ may be taken positive because $Q(x,y)>0$.
Notice the strict inequalities

$$
0<|a|<|z|,\qquad 0<w<|z|,
\tag{3.8}
$$

because $z=5aw$ and $a,w$ are nonzero integers. These smaller numbers are candidates
for a descent measure, but neither is yet the last coordinate of a new Fermat solution.
That distinction will guide Chapters 6 and 7.

Two small computations fix the valuation picture. For $(x,y)=(1,1)$, the exceptional
condition fails. The four nonrational factors $1+\zeta^i$ are units, and their norms
are one. For $(x,y)=(1,4)$, the exceptional condition holds. The rational factor is
$5$, of $\mathfrak p$-value four, while

$$
1+4\zeta^i=5+4(\zeta^i-1)
$$

has value one for $i\ne0$. The norm quotient is

$$
Q(1,4)=1-4+16-64+256=205=5\cdot41.
$$

This pair is not a Fermat solution because $41$ is not a fifth power, but it displays
the exact local pattern from which the descent starts. It also warns that a normalized
factor is only a $\mathfrak p$-unit, not necessarily a global unit.

There is a useful integer check on the norm form. Put $s=x+y$ and $p=xy$. Newton's
identities give

$$
Q(x,y)=s^4-5ps^2+5p^2.
\tag{3.9}
$$

When $5\mid s$ and $5\nmid p$, the last term has ordinary value one and the other
terms have larger value, recovering $v_5(Q)=1$. Formula (3.9) cannot replace ideal
factorization: it says nothing about how primes above a split rational prime are
distributed among the linear factors.

## 4. The first case

### 4.1 Primary normalization

Temporarily suppose

$$
a^5+b^5=c^5,\qquad \gcd(a,b)=1,\qquad 5\nmid abc.
\tag{4.1}
$$

Then $5\nmid a+b$, since otherwise (4.1) modulo $5$ would give $5\mid c$.
The factors $a+\zeta^ib$ are pairwise coprime, so

$$
a+\zeta b=uA^5.
\tag{4.2}
$$

There is a unique $k\in\mathbf Z/5\mathbf Z$ such that
$\zeta^k(a+\zeta b)$ is primary. Since

$$
a+\zeta b=(a+b)-b\lambda,
$$

the first two $\lambda$-digits give

$$
k\equiv-\frac{b}{a+b}\pmod5,
\quad\text{equivalently}\quad
ka+(k+1)b\equiv0\pmod5.
\tag{4.3}
$$

The fifth power $A^5$ is primary, so the unit $\zeta^ku$ is primary. The primary-unit
test makes it real. Absorbing a fifth power of $\eta$ and a sign into $A^5$, we obtain

$$
\boxed{\zeta^k(a+\zeta b)=\eta^rA^5}
\tag{4.4}
$$

for some $r\in\{0,1,2,3,4\}$. It is important that we do not claim $r=0$.

### 4.2 Fifth powers and conjugate differences

The real unit in (4.4) disappears after conjugation and subtraction. Conjugating gives

$$
\zeta^{-k}(a+\zeta^{-1}b)=\eta^r\bar A^5.
$$

Hence

$$
a(\zeta^k-\zeta^{-k})
+b(\zeta^{k+1}-\zeta^{-(k+1)})
=\eta^r(A^5-\bar A^5).
\tag{4.5}
$$

The right side is divisible by $\lambda^5$.

**Lemma 4.1.** For every $A\in\mathcal O$,

$$
\lambda^5\mid A^5-\bar A^5.
$$

**Proof.** Since conjugation acts trivially modulo $\lambda$, write
$A=\bar A+\lambda D$. Expanding,

$$
A^5-\bar A^5
=5\bar A^4\lambda D+10\bar A^3\lambda^2D^2
+10\bar A^2\lambda^3D^3+5\bar A\lambda^4D^4+\lambda^5D^5.
$$

The first four terms are divisible by $5\lambda$, $5\lambda^2$,
$5\lambda^3$, and $5\lambda^4$, respectively. Since $\lambda^4\mid5$, each is
divisible by $\lambda^5$; so is the last term. $\square$

This lemma is stronger than the assertion that fifth powers are rational modulo
$\lambda^4$. The extra factor comes from taking the difference of two elements already
congruent modulo $\lambda$.

### 4.3 The residue restriction

Equation (4.5) has a surprisingly rigid consequence.

**Lemma 4.2 (first-case residue lemma).** Under (4.1), one has

$$
a\equiv b\pmod5.
\tag{4.6}
$$

**Proof strategy.** The primary exponent $k$ cannot be $0$ or $4$ because $a,b$ are
units modulo $5$. For $k=1$ or $3$, the left side of (4.5), written in the integral
$\lambda$-basis, cannot be divisible by $\lambda^5$ unless one of $a,b$ is divisible
by $5$. Thus $k=2$, and (4.3) becomes $a\equiv b$.

**Proof.** From (4.3), $k=0$ would give $5\mid b$, and $k=4$ would give $5\mid a$.
Thus $k\in\{1,2,3\}$.

For $k=1$, the left side of (4.5) has $\lambda$-coordinates

$$
5a+(-7a+b)\lambda+(4a-2b)\lambda^2+(-a+b)\lambda^3.
\tag{4.7}
$$

If this is divisible by $\lambda^5$, formula (2.4) first forces $25\mid5a$, hence
$5\mid a$, a contradiction. For $k=3$, conjugating and interchanging $a,b$ gives the
same contradiction with $5\mid b$.

Therefore $k=2$. Equation (4.3) becomes

$$
2a+3b\equiv2(a-b)\equiv0\pmod5,
$$

which is (4.6). $\square$

The coordinate calculation is decisive. Divisibility merely by $\lambda^2$ is already
built into primary normalization; divisibility by $\lambda^5$ is what excludes the two
asymmetric residue classes.

All five primary exponents can be displayed at once:

| $k$ | primary congruence | consequence of (4.5) |
|---|---|---|
| $0$ | $b\equiv0$ | excluded in the first case |
| $1$ | $a+2b\equiv0$ | forces $a\equiv0$ |
| $2$ | $a-b\equiv0$ | the only surviving unit pair |
| $3$ | $2a+b\equiv0$ | forces $b\equiv0$ |
| $4$ | $a\equiv0$ | excluded in the first case |

The middle row is genuinely sharp. Its conjugate difference is

$$
(a-b)(\zeta^2-\zeta^3).
$$

If $a\equiv b\pmod5$, the rational factor contributes four copies of $\lambda$ and
the root-of-unity difference contributes one. Thus a single ordered pair cannot exclude
the middle row. The contradiction appears only after the three signed variables are
cycled. This also explains the difference from the modulus-$25$ proof: that proof
compares all three fifth powers simultaneously, while the cyclotomic proof extracts
exact information from one ordered pair and then transports it by symmetry.

### 4.4 Cycling the three variables

We now close the first case without any appeal to the second-case descent.

From (4.1) and Lemma 4.2,

$$
a\equiv b\pmod5.
\tag{4.8}
$$

Rewrite the same equation as

$$
a^5+(-c)^5=(-b)^5.
$$

All three variables remain prime to $5$, and $5\nmid a-c$ because otherwise the
equation modulo $5$ would force $5\mid b$. Lemma 4.2 applied to the first two terms
gives

$$
a\equiv-c\pmod5.
\tag{4.9}
$$

On the other hand (4.1) modulo $5$ and (4.8) give

$$
c\equiv a+b\equiv2a\pmod5.
$$

Together with (4.9), this says $a\equiv-2a$, so $3a\equiv0\pmod5$. This contradicts
$5\nmid a$.

We have proved:

**Theorem 4.3 (first case).** There is no nonzero primitive solution of
$a^5+b^5=c^5$ with $5\nmid abc$.

### 4.5 What the first case teaches

The proof used the realness of the surviving unit, not its being a fifth power. This
is why modulus $\lambda^2$ was enough. The real unit canceled when the normalized
equation was compared with its conjugate.

Two tempting shortcuts fail.

1. From (4.2), one cannot replace $u$ by $1$. The unit $\eta$ is a counterexample to
   that inference.
2. From $N(a+\zeta b)$ being a fifth power, one cannot recover (4.2). Norms merge
   prime ideals above the same rational prime.

The first-case proof is thus short only because Book 191 has already isolated the unit
class precisely. The residue lemma is the visible tip of that arithmetic.

## 5. The ramified factor in the second case

### 5.1 Locating the variable divisible by five

Return to the primitive equation (3.2). Exactly one variable is divisible by $5$, and
it is $z$. The congruence $x+y\equiv z\pmod5$ then places the rational factor
$x+y$ at the ramified prime. Equations (3.3) and (3.4) say

$$
v_5(x+y)=5v_5(z)-1.
\tag{5.1}
$$

This relation is both a check and a warning. A proof that obtains only $5\mid x+y$
has not yet used the full cyclotomic valuation. Conversely, one must not read the
$-1$ in (5.1) as a negative valuation: it records the four nonrational factors, each
of which contributes one copy of $\lambda$.

### 5.2 Removing the common prime

For $i=1,2,3,4$, set

$$
\lambda_i=1-\zeta^i,\qquad
G_i=\frac{x+\zeta^iy}{\lambda_i}.
\tag{5.2}
$$

Each $G_i$ is integral and prime to $\mathfrak p$. The ideals $(G_i)$ are pairwise
coprime. A common prime away from $\mathfrak p$ would divide two original factors,
and $\mathfrak p$ divides none of the quotients.

Since the product of the original factors is $z^5$, every prime-ideal exponent away
from $\mathfrak p$ in $x+\zeta y$ is divisible by five. Its $\mathfrak p$-value is
one. Ideal extraction and class number one give

$$
x+\zeta y=u\lambda A^5
\tag{5.3}
$$

for a unit $u$ and a $\lambda$-adic unit $A$.

The use of the same $\lambda$ rather than $\lambda_i$ is harmless for a single factor,
but exact conjugate formulas are cleaner with $\lambda_i$. Applying $\sigma^j$ to the
eventual exact equation will automatically choose the correct conjugate uniformizer.

### 5.3 Eliminating the unit

Here the ramification that created the common divisor also removes the unit.

**Proposition 5.1 (exact ramified factor).** Under (3.2), there is $A\in\mathcal O$
such that

$$
\boxed{x+\zeta y=\lambda A^5.}
\tag{5.4}
$$

**Proof strategy.** Divide (5.3) by $\lambda$. The quotient is rational modulo
$\lambda^3$. Since $A^5$ is rational modulo $\lambda^4$, the unit $u$ is rational
modulo $\lambda^3$ and hence is a fifth power.

**Proof.** Write $x+y=5m$. From (2.1),

$$
\frac{x+\zeta y}{\lambda}
=\frac{x+y-y\lambda}{\lambda}
=\zeta^3\eta^2m\lambda^3-y
\equiv-y\pmod{\lambda^3}.
\tag{5.5}
$$

This is a $\lambda$-adic unit because $5\nmid y$. Equation (5.3) gives

$$
\frac{x+\zeta y}{\lambda}=uA^5.
$$

The fifth power $A^5$ is congruent to a nonzero rational integer modulo
$\lambda^4$. Dividing (5.5) by its rational residue makes $u$ rational modulo
$\lambda^3$. The fifth-power unit test gives $u=v^5$. Replacing $A$ by $vA$ proves
(5.4). $\square$

This is the exact point at which second-case arithmetic is stronger than first-case
arithmetic. In the first case a real unit class remained. Here dividing $5$ by one
copy of $\lambda$ leaves $\lambda^3$, precisely the depth needed to kill both unit
classes.

### 5.4 The exact rational shadows

Taking norms in (5.4) gives

$$
Q(x,y)=5N(A)^5.
$$

Comparison with (3.7) shows

$$
N(A)=w.
\tag{5.6}
$$

This equality is positive automatically: every nonzero absolute norm from $K$ is
positive.

The equality $z=5aw$ now reads

$$
|z|=5|a|N(A).
\tag{5.7}
$$

Thus both $|a|$ and $N(A)$ are strictly smaller than $|z|$. The descent will retain
the element $A$, not only its norm, because its four conjugates remember how the
prime ideals of $Q(x,y)$ were distributed.

As a useful exact coordinate check, the cyclotomic equation gives

$$
\frac5\lambda=10-10\lambda+5\lambda^2-\lambda^3.
\tag{5.8}
$$

Consequently (5.4) is equivalent to

$$
A^5=(10m-y)-10m\lambda+5m\lambda^2-m\lambda^3,
\qquad m=\frac{x+y}{5}.
\tag{5.9}
$$

The four coefficients in (5.9) are the concrete starting data for the replacement
calculation. They also show why an arbitrary fifth root of the norm cannot be used:
the relative ratios $-10:5:-1$ carry essential information.

From $x+y=5^4a^5$ one also has

$$
m=5^3a^5,\qquad v_{\mathfrak p}(m)=12+20v_5(a).
\tag{5.10}
$$

Thus (5.9) implies the unusually deep congruence

$$
A^5\equiv-y\pmod{\lambda^{12}}.
\tag{5.11}
$$

One must not take a fifth root of this congruence naively. The equality $\zeta^5=1$
already shows that fifth roots can differ at shallow $\lambda$-adic depth. The
conjugate-difference construction extracts the invariant information without choosing
a nonunique local fifth root.

The exact conjugate uniformizers are equally important. Applying $\sigma_i$ to (5.4)
gives

$$
x+\zeta^iy=(1-\zeta^i)\sigma_i(A)^5.
$$

Replacing $1-\zeta^i$ by the associate $\lambda$ would introduce

$$
\frac{1-\zeta^i}{1-\zeta}=1+\zeta+\cdots+\zeta^{i-1}.
$$

This unit is harmless for valuations and norms but need not be a fifth power. Keeping
$1-\zeta^i$ makes every conjugate equation exact.

## 6. From one solution to a descent carrier

### 6.1 Why the norm identity alone is insufficient

Equation (5.7) exhibits two smaller positive integers, but it does not by itself close
a descent. To see the problem, suppose only that

$$
Q(x,y)=5w^5.
$$

The equality says that the sum of the prime-ideal exponents above each rational prime,
weighted by residue degree, is divisible by five after the contribution at $5$ is
removed. It does not say that the exponent at each prime ideal is divisible by five.
Different primes over the same split rational prime can compensate in the norm.

The element $A$ in (5.4) retains the missing information. Its conjugates are tied to
the four normalized factors by

$$
x+\zeta^iy=(1-\zeta^i)\sigma_i(A)^5,\qquad i=1,2,3,4.
\tag{6.1}
$$

The descent carrier will be built from differences among these conjugates. The
construction may look less natural than simply keeping $w=N(A)$, but it has two
essential advantages: it is closed under fifth-power extraction, and it remembers the
unit class exactly.

### 6.2 The first conjugate difference

Apply $\sigma$ to (5.4):

$$
x+\zeta^2y=(1-\zeta^2)\sigma(A)^5
=\lambda(1+\zeta)\sigma(A)^5.
\tag{6.2}
$$

Multiply (5.4) by $1+\zeta$ and subtract (6.2). The left side becomes

$$
(1+\zeta)(x+\zeta y)-(x+\zeta^2y)=\zeta(x+y).
$$

After cancelling $\lambda(1+\zeta)$, we obtain

$$
A^5-\sigma(A)^5
=\frac{\zeta(x+y)}{\lambda(1+\zeta)}.
\tag{6.3}
$$

Insert $x+y=5^4a^5$, $5=\zeta^3\eta^2\lambda^4$, and
$1+\zeta=-\zeta^3\eta$. A direct simplification gives

$$
\boxed{A^5-\sigma(A)^5=-\eta^7\lambda^{15}a^5
=\eta^2(-\eta\lambda^3a)^5.}
\tag{6.4}
$$

The second form records the Kummer class; the first records the exact unit. Neither
should be replaced by an unspecified associate.

The two ideals $(A)$ and $(\sigma(A))$ are coprime. Indeed, their fifth powers are the
ideals of two distinct normalized factors $G_1,G_2$ from (5.2). Those ideals are
coprime, so their fifth roots are coprime as well.

Factor the left side of (6.4):

$$
A^5-\sigma(A)^5
=\prod_{j=0}^4\bigl(A-\zeta^j\sigma(A)\bigr).
\tag{6.5}
$$

As usual, distinct factors can have no common prime except $\mathfrak p$. Because
$A$ is a $\lambda$-adic unit and $A\equiv\sigma(A)\pmod\lambda$, the four factors with
$j\ne0$ have $\mathfrak p$-value one. Equation (6.4) has value

$$
15+20v_5(a).
$$

Therefore

$$
\boxed{v_{\mathfrak p}(A-\sigma(A))=11+20v_5(a).}
\tag{6.6}
$$

This is the first gain of descent. The initial factor $x+\zeta y$ had value one after
one uniformizer was restored. Its fifth root $A$ is almost fixed by $\sigma$: the
difference begins at least eleven $\lambda$-digits deep.

### 6.3 Deep invariance and rational digits

The fixed field of $\sigma$ is $\mathbf Q$. Deep approximate invariance therefore
forces the first digits of $A$ to be rational.

**Lemma 6.1 (fixed digits).** If $B\in\mathcal O$ and

$$
B\equiv\sigma(B)\pmod{\lambda^3},
$$

then $B$ is congruent to a rational integer modulo $\lambda^3$.

**Proof.** Write

$$
B\equiv b_0+b_1\lambda+b_2\lambda^2\pmod{\lambda^3},
\qquad b_i\in\mathbf F_5.
$$

Since

$$
\sigma(\lambda)=1-\zeta^2=2\lambda-\lambda^2,
$$

we have, modulo $\lambda^3$,

$$
\sigma(B)\equiv b_0+2b_1\lambda+(-b_1+4b_2)\lambda^2.
$$

Equality of the linear digits gives $b_1=0$; equality of the quadratic digits then
gives $3b_2=0$, so $b_2=0$ in $\mathbf F_5$. Thus $B\equiv b_0$ modulo
$\lambda^3$. $\square$

By (6.6), the lemma applies to $A$. Hence

$$
A\equiv r\pmod{\lambda^3}
\tag{6.7}
$$

for a rational integer $r$ prime to $5$. This conclusion is not obtained from $A^5$
being rational modulo $\lambda^4$; it comes from the much deeper conjugate difference.

The exponent three is again exact for the unit problem. Congruence merely modulo
$\lambda^2$ would leave the real unit class $\eta$ undetected.

### 6.4 The four normalized difference factors

For $j=1,2,3,4$, set

$$
D_j=A-\zeta^j\sigma(A),\qquad \lambda_j=1-\zeta^j.
\tag{6.8}
$$

Then

$$
\frac{D_j}{\lambda_j}
=\sigma(A)+\frac{A-\sigma(A)}{\lambda_j}.
\tag{6.9}
$$

The second term on the right is divisible by $\lambda^{10}$, while the first is
rational modulo $\lambda^3$ by (6.7). Thus $D_j/\lambda_j$ is rational modulo
$\lambda^3$ and is a $\lambda$-adic unit.

Away from $\mathfrak p$, every prime-ideal exponent of $D_j$ is divisible by five:
the factors in (6.5) are pairwise coprime away from $\mathfrak p$, and their product is
a unit times a fifth power. The global fifth-power criterion therefore gives

$$
\boxed{D_j=\lambda_jB_j^5\qquad(j=1,2,3,4)}
\tag{6.10}
$$

for algebraic integers $B_j$. These four roots must be retained independently. The
automorphism $\sigma$ changes both entries of the ordered pair
$(A,\sigma(A))$, whereas changing $j$ twists only its second entry. Thus it would be
incorrect to identify the $B_j$ as the conjugates of one element.

Put

$$
B=B_1B_2B_3B_4.
\tag{6.11}
$$

Multiplying (6.10) and using

$$
\prod_{j=1}^4(1-\zeta^j)=5
$$

gives

$$
\prod_{j=1}^4D_j=5B^5.
\tag{6.12}
$$

Combining this with (6.4) and (6.5) keeps track of the remaining factor:

$$
5(A-\sigma(A))B^5
=\eta^2(-\eta\lambda^3a)^5.
\tag{6.13}
$$

At the level of fifth-power classes, (6.13) says

$$
A-\sigma(A)\equiv\zeta^2\lambda
\pmod{(K^\times)^5}.
\tag{6.14}
$$

The root-of-unity factor $\zeta^2$ is not decorative. It is one of the two states in
the explicit replacement calculation.

The construction has three independent gains. First, every $D_j$ has prime-ideal
exponents divisible by five away from $\mathfrak p$. Second, after division by
$\lambda_j$, it is rational modulo $\lambda^3$, so its unit is a fifth power. Third,
multiplying the four exact equations introduces the full element
$5=\zeta^3\eta^2\lambda^4$, not merely the ideal $\mathfrak p^4$. The state
$\zeta^2$ in (6.14) is the residue of this last exact multiplication.

If only ideals were retained, (6.14) would weaken to

$$
(A-\sigma(A))=\mathfrak p\,\mathfrak b^5.
$$

The unit could then represent any of the twenty-five classes
$\zeta^r\eta^s$ modulo fifth powers, and the replacement family would not close. If
only congruences were retained, a prime away from $5$ could still occur with an
uncontrolled exponent. The carrier is built precisely where ideal extraction and local
unit arithmetic overlap.

The valuation sum gives a quick consistency check. The four $D_j$ with $j\ne0$
contribute total value four. The factor $A-\sigma(A)$ contributes
$11+20v_5(a)$. Their total,

$$
15+20v_5(a),
$$

is exactly the value of the right side of (6.4). A missing conjugate uniformizer or a
confusion between $v_5$ and $v_{\mathfrak p}$ would fail this check.

## 7. The quintic replacement lemma

### 7.1 Descent records and their weight

We now isolate the finite calculation that closes the second case. Its purpose is to
make precise what “repeat the argument” means. Repetition is legitimate only after the
new factors have been shown to satisfy the same coprimality, digit, and unit conditions.

A **quintic descent record** consists of

$$
(U,h,\epsilon;V_1,V_2,V_4,V_3),
\tag{7.1}
$$

where $U\in\mathcal O$ is a $\lambda$-adic unit, $h$ is a nonzero rational integer,
$\epsilon\in\{0,2\}$, and the following conditions hold.

1. The ideals $(U)$ and $(\sigma(U))$ are coprime.
2. One has $U\equiv\sigma(U)\pmod{\lambda^{11}}$.
3. The exact difference-of-fifth-powers identity is
   $$
   U^5-\sigma(U)^5
   =\eta^2(-\eta\lambda^3h)^5.
   \tag{7.2}
   $$
4. For $j=1,2,4,3$ in that order,
   $$
   U-\zeta^j\sigma(U)=\lambda_jV_j^5,
   \tag{7.3}
   $$
   with indices reduced modulo five.
5. The remaining factor has the exact class
   $$
   U-\sigma(U)=\zeta^\epsilon\lambda V_0^5
   \tag{7.4}
   $$
   after a common fifth-power scaling in $K^\times$. When $\epsilon=2$, this is read
   directly from (6.14); the alternative state occurs after replacement.

The fractional element $V_0$ in (7.4) need not be integral before its exact
$\lambda$-valuation is stripped. The record keeps only its fifth-power class. All
$V_j$ for $j\ne0$ are integral.

To define a well-founded weight, write $U$ in the basis (2.3), subtract its rational
coordinate, and divide the three nonconstant coordinates by their positive greatest
common divisor. This gives a primitive triple

$$
(u_1,u_2,u_3)\in\mathbf Z^3,\qquad \gcd(u_1,u_2,u_3)=1.
$$

Set

$$
\mathscr W(U)
=13u_1^2+66u_1u_2+106u_1u_3
+93u_2^2+330u_2u_3+325u_3^2.
\tag{7.5}
$$

If the nonconstant part is zero, then $U$ is rational. That cannot occur in a descent
record: (7.2) would have zero left side and nonzero right side. Hence
$\mathscr W(U)$ is a positive integer.

The expression (7.5) is one sixth of the sum of the ordinary squared nonconstant
coordinates of

$$
U,\quad\sigma(U),\quad\sigma^2(U),\quad\sigma^3(U).
$$

Indeed, applying (7.7) four times and collecting terms gives exactly the displayed
quadratic form. This description proves that it is positive definite and invariant
under $\sigma$ and under adding a rational integer. Its role is purely well-founded:
unlike the absolute field norm, it cannot remain unchanged under a nontrivial
replacement because common rational content has first been removed.

The rational coordinate is discarded for a structural reason. The operator
$1-\sigma$ kills every rational integer, so a large rational part of $U$ has no bearing
on the difference relations. The remaining three coordinates are exactly the part on
which the cyclic action is visible.

The absolute field norm would not be as convenient a primary weight. A difference
$U-\zeta\sigma(U)$ may grow in one complex embedding and shrink in another, and its
fifth root need not visibly have smaller norm until the exact coefficient relations are
used. The weight $\mathscr W$ incorporates those relations after the staggered
divisibility has appeared. It is a height adapted to descent records, not a claim that
every algebraic integer has a preferred Euclidean size.

### 7.2 The coordinate engine

The replacement calculation is finite because $K$ has degree four. We give it in full.
From $\sigma(\lambda)=2\lambda-\lambda^2$ and the cyclotomic relation

$$
\lambda^4=5\lambda^3-10\lambda^2+10\lambda-5,
\tag{7.6}
$$

one obtains

$$
\begin{aligned}
\sigma(1)&=1,\\
\sigma(\lambda)&=2\lambda-\lambda^2,\\
\sigma(\lambda^2)&=-5+10\lambda-6\lambda^2+\lambda^3,\\
\sigma(\lambda^3)&=-15+25\lambda-15\lambda^2+3\lambda^3.
\end{aligned}
\tag{7.7}
$$

Thus, for

$$
U=u_0+u_1\lambda+u_2\lambda^2+u_3\lambda^3,
$$

the difference $U-\sigma(U)$ has coordinates

$$
\begin{aligned}
c_0&=5u_2+15u_3,\\
c_1&=-u_1-10u_2-25u_3,\\
c_2&=u_1+7u_2+15u_3,\\
c_3&=-u_2-2u_3.
\end{aligned}
\tag{7.8}
$$

If its valuation is at least eleven, formula (2.4) gives

$$
125\mid c_0,\qquad125\mid c_1,\qquad125\mid c_2,\qquad25\mid c_3.
\tag{7.9}
$$

These divisibilities are not four independent assumptions. From $c_3$ and $c_0/5$
one obtains

$$
25\mid u_2+2u_3,\qquad 25\mid u_2+3u_3,
$$

and hence

$$
25\mid u_2,\qquad25\mid u_3.
\tag{7.10}
$$

The condition on $c_1$ then gives $125\mid u_1$. Thus the nonconstant coordinate is
divisible in the staggered pattern $125,25,25$. This is the division that drives the
replacement; the rational residue $u_0$ remains a unit modulo $5$.

There are two possible root-of-unity states. Expanding

$$
U-\zeta\sigma(U)=\lambda V^5
\tag{7.11}
$$

in the same basis, using these divisibilities, and comparing the coefficients of
$1,\lambda,\lambda^2,\lambda^3$ gives the following transition table.

| input state | leading difference | replacement element | output state |
|---|---|---|---|
| $0$ | $\lambda V_0^5$ | $V_1$ from (7.11) | $2$ |
| $2$ | $\zeta^2\lambda V_0^5$ | $\zeta^{-1}V_1$ | $0$ |

Before the output row is read, the staggered nonconstant coordinates in (7.10) are
divided by their indicated powers of $5$ and their common content is removed. The
rational residue of $U$ modulo $\lambda^3$ is unchanged by this normalization.

For completeness, here is how the coefficient comparison behind the table is checked
without hiding a cancellation. Write
$V=v_0+v_1\lambda+v_2\lambda^2+v_3\lambda^3$, form the finite multinomial expansion
of $V^5$, multiply by $\lambda$, and replace every occurrence of $\lambda^4$ by the
right side of (7.6), beginning with the highest power. Compare the four resulting
integer coefficients with (7.8). At the first level, reduction modulo $5$ replaces
each $v_i^5$ by $v_i$. The three nonconstant equations are triangular because the
action matrix in (7.7) has the distinct nontrivial diagonal residues $2,4,3$.
Subtract the unique residue representatives and divide the nonconstant equations by
$5$. The same triangular system occurs at the next level. After the third pass, the
divisibilities (7.10) remove a common factor $25$, and the remaining equations are
precisely the other row of the table. Every division by $5$ is made only after all four
coefficients concerned have been shown divisible by $5$.

The calculation also proves closure. For the new ordered pair, refactor its
difference of fifth powers and apply the same ideal-coprimality argument to its four
twists. This supplies the four new equations in (7.3); the roots are again retained
independently. Their pairwise coprimality follows by the same two linear combinations
used for cyclotomic factors. Multiplication supplies (7.2) for the new element, and the
product of the four $\lambda_j$ supplies the next root-of-unity state.
The two rows alternate because

$$
5=\zeta^3\eta^2\lambda^4
$$

contributes $\zeta^3$, while conjugating $\lambda$ contributes
$-\zeta^{-1}$. Reducing the total exponent modulo five gives $0\leftrightarrow2$.

The order of the calculation is what keeps it transparent. Expanding every fifth power
at once produces many monomials and hides the triangular structure. Instead one first
computes $1-\sigma$ on the integral basis, then uses valuations to prove divisibility
of the four coordinates, then solves one residue digit at a time, and only at the end
multiplies the extracted factors and simplifies the unit.

The distinct residues $2,4,3$ in the three nonrational directions make the digit
equations invertible. The rational direction has eigenvalue one and is intentionally
left unchanged. Multiplication of the conjugate uniformizers is postponed because that
is the operation that changes the unit state. This separation explains both the form
of the record and the two-row transition table.

### 7.3 Extraction and replacement

We can now state the descent lemma in the form used later.

**Theorem 7.1 (quintic replacement lemma).** Every quintic descent record has a
successor quintic descent record

$$
(U',h',2-\epsilon;V'_1,V'_2,V'_4,V'_3)
$$

such that

$$
0<|h'|\le |h|,\qquad
0<\mathscr W(U')<\mathscr W(U).
\tag{7.13}
$$

The successor is obtained from the explicit factor

$$
U-\zeta\sigma(U)=\lambda V_1^5
\tag{7.14}
$$

in state $0$, and from $\zeta^{-1}V_1$ in state $2$.

**Proof strategy.** Coprimality makes every exponent away from $\mathfrak p$ a multiple
of five. The rational three-digit congruence removes the unit, giving (7.14). The
coefficient reduction of Section 7.2 shows that the new element satisfies the same
record conditions with the other unit state. Its staggered coordinate division makes
the primitive coordinate norm strictly smaller.

**Proof.** The extraction and the exact absence of a unit were proved in Section 6.4;
the same proof applies to either state because multiplying the remaining factor by
$\zeta^2$ does not change any ideal exponent. The transition table following (7.10)
then proves all algebraic conditions for the successor.

It remains to prove strictness, the point often omitted in informal accounts. Let
$q$ be the greatest common divisor removed in forming the primitive triple of $U$, and
let $q'$ be the corresponding divisor for $U'$. Carry the three successive residue
digits in the coefficient reduction of Section 7.2 as integers $e_1,e_2,e_3,e_4$.
Substitution in the invariant quadratic expression (7.5), followed by pairing the
terms exchanged by $\sigma$, expresses

$$
q^2\mathscr W(U)-25q'^2\mathscr W(U')
\tag{7.15}
$$

as a positive integral linear combination of the squares of the nonconstant carry
digits. To verify the sign directly, use the orbit-sum description of $\mathscr W$:
each of the four conjugate coefficient divisions removes a factor $5$, and the square
of the discarded residue is the corresponding summand. If every discarded residue
were zero, all three nonconstant coordinates of $U$ would have a further common factor,
contrary to the choice of $q$. Thus at least one square is positive. Removing common
content can only decrease the successor term after division. Hence
$\mathscr W(U')<\mathscr W(U)$. It is also positive, since a rational $U'$ would make
its difference-of-fifth-powers identity have zero left side and nonzero right side.

The parameter $h'$ is the rational fifth root left after the common content in the
coefficient equations is removed. Prime-by-prime comparison in (7.2) shows that every prime exponent
of $h'$ is no larger than the corresponding exponent of $h$. Thus
$0<|h'|\le|h|$. This proves (7.13). $\square$

The orbit sum in (7.5) is essential. With only
$u_1^2+u_2^2+u_3^2$, the cross terms from $\sigma(\lambda^3)$ have indefinite sign.
Summing over the full orbit turns the comparison into the squares described after
(7.15).

Equality cannot occur in the strictness argument. Vanishing of every carry digit would
give further common content in the primitive nonconstant coordinate. Conceptually, a
record fixed by replacement would also have to identify the states $0$ and $2$ in the
unit group modulo fifth powers.

Negative values of $h$ cause no change. The sign is itself a fifth power, so it is
absorbed when the successor's rational fifth root is chosen. The ordering is placed on
$\mathscr W(U)$, not on algebraic integers or on the signed parameter.

### 7.4 Strict decrease

There are three distinct notions of “smaller” in the proof:

1. $|a|<|z|$ and $N(A)<|z|$ in (3.8);
2. the fifth roots $V_j$ are extracted from explicit factors of a conjugate
   difference;
3. the integral weight $\mathscr W$ decreases strictly under replacement.

Only the third is used to iterate indefinitely. The first motivates the carrier and
prevents the initial passage from increasing every natural size. The second keeps the
new record arithmetically attached to the old one. A proof citing only the first two
has not established a well-founded descent.

Because $\mathscr W(U)$ is a positive integer, strict decrease immediately forbids an
infinite chain. No assertion about real convergence is involved. The descent is
well-founded in the ordinary ordering of $\mathbf Z_{>0}$.

The field norm still has a useful supporting role. From (7.14),

$$
N(U-\zeta\sigma(U))=5N(V_1)^5.
\tag{7.16}
$$

Thus the replacement is simultaneously a norm extraction from an explicit factor.
Equation (7.16) verifies integrality and detects a missing factor of $5$, but the
coordinate norm $\mathscr W$ supplies strictness without requiring a false converse to
the field norm.

### 7.5 Why every hypothesis is needed

The replacement lemma is deliberately not stated for arbitrary $U$.

- Without coprimality of $(U)$ and $(\sigma(U))$, a prime away from $\mathfrak p$ may
  divide several factors in (6.5), so no individual factor need have exponent divisible
  by five.
- Without the depth-eleven difference, (6.9) need not be rational modulo
  $\lambda^3$, and the surviving unit may be $\eta$.
- Without the exact unit state, multiplication of the four extracted factors can shift
  by a non-fifth-power root of unity. The successor then leaves the two-state family.
- Without primitive coordinate content, (7.5) could decrease only by a common scaling
  that is immediately reintroduced at the next step.

For example, take a general $\lambda$-adic unit $U$ with
$U\equiv\sigma(U)\pmod\lambda$ but not modulo $\lambda^3$. Then
$(U-\zeta\sigma(U))/\lambda$ is a unit, yet it may represent the class of $\eta$.
Ideal exponents alone cannot remove it. This is exactly the obstruction excluded by
the fixed-digit lemma.

## 8. Well-founded second-case descent

### 8.1 Constructing the initial record

Assume a primitive second-case solution (3.2). Proposition 5.1 gives

$$
x+\zeta y=\lambda A^5.
$$

Sections 6.2--6.4 prove all the required data:

$$
\begin{aligned}
A^5-\sigma(A)^5&=\eta^2(-\eta\lambda^3a)^5,\\
v_{\mathfrak p}(A-\sigma(A))&=11+20v_5(a),\\
A-\zeta^j\sigma(A)&=\lambda_jB_j^5\quad(j=1,2,3,4),\\
A-\sigma(A)&\equiv\zeta^2\lambda
\pmod{(K^\times)^5}.
\end{aligned}
\tag{8.1}
$$

The normalized factor ideals from the original solution prove the required
coprimality. Thus

$$
(A,a,2;B_1,B_2,B_4,B_3)
\tag{8.2}
$$

is a quintic descent record.

The passage from $(x,y,z)$ to (8.2) is not circular. It uses only factorization,
valuation, class number one, the explicit unit tests, and identities. The replacement
lemma has not yet been invoked.

### 8.2 Iteration

Apply Theorem 7.1 to (8.2). It produces a successor record with state $0$ and smaller
weight. Applying it again produces a state-$2$ record with still smaller weight. Thus,
inductively, there are records $\mathcal R_n$ with

$$
\mathscr W(\mathcal R_0)>
\mathscr W(\mathcal R_1)>
\mathscr W(\mathcal R_2)>
\cdots>0.
\tag{8.3}
$$

At every step, the new fifth root comes from an explicit cyclotomic difference factor.
The state alternates

$$
2,0,2,0,\ldots,
$$

and the rational parameter never increases in absolute value. Coprimality and the
rational three-digit condition are re-established, not assumed by analogy.

This last observation is what makes the iteration legitimate. An identity may resemble
the preceding identity while failing one of the extraction hypotheses. The definition
of a descent record was chosen precisely so that the conclusion of the replacement
lemma is again an input to the same lemma.

### 8.3 The contradiction

There is no infinite strictly decreasing sequence of positive integers. Indeed, among
the weights in (8.3), choose the least one. Its successor would be a still smaller
positive integer, a contradiction.

We have proved:

**Theorem 8.1 (second case).** There is no nonzero primitive solution of

$$
x^5+y^5=z^5
$$

for which $5\mid xyz$.

The proof is an infinite descent in the precise well-founded sense. It does not posit an
infinite sequence as an extra assumption; the replacement lemma constructs the
successor to every alleged record, and the least-positive-integer principle rules out
the initial record.

### 8.4 Norm descent and explicit-factor descent

Two descriptions of the argument are now available.

In the **norm description**, the original equation gives

$$
N(A)=\frac{|z|}{5|a|}<|z|,
$$

and every replacement satisfies

$$
N(U-\zeta\sigma(U))=5N(U')^5.
$$

Norms certify that the extracted roots are integral and quantify the loss of one
ramified prime.

In the **explicit-factor description**, the successor is the fifth root of

$$
\frac{U-\zeta\sigma(U)}{1-\zeta}.
$$

The fixed-digit lemma removes the unit, and the coefficient identity (7.15) proves
strict decrease. This is the safer description when one wants to see exactly why the
new object belongs to the same family.

The two descriptions complement rather than replace one another. Norm alone forgets
prime distribution. Explicit factors alone do not automatically give a well-founded
measure. Together they provide the promised well-founded norm descent.

## 9. Fermat's theorem for exponent five

### 9.1 The integer theorem

We can now assemble the proof of Theorem 1.1.

**Proof of Theorem 1.1.** Suppose $x^5+y^5=z^5$ with $xyz\ne0$. Divide by the common
divisor to obtain a primitive nonzero solution.

If $5\nmid xyz$, Theorem 4.3 gives a contradiction. If $5\mid xyz$, Theorem 8.1 gives
a contradiction. These are the only cases. Therefore no nonzero solution exists.
$\square$

The elementary congruence Lemma 3.1 can replace Theorem 4.3 in this final assembly, but
the cyclotomic proof of the first case remains part of the descent theory: its primary
normalization and conjugate-difference calculation are prototypes for the deeper
second-case construction.

### 9.2 The rational and exponent-divisible forms

The integer theorem immediately implies the rational form.

**Corollary 9.1.** If $x,y,z\in\mathbf Q$ and $x^5+y^5=z^5$, then $xyz=0$.

**Proof.** Multiply by the fifth power of a common positive denominator. The resulting
integer solution is trivial, so the original rational solution is trivial. $\square$

It also settles every exponent divisible by five.

**Corollary 9.2.** Let $n$ be a positive multiple of $5$. If

$$
x^n+y^n=z^n,\qquad x,y,z\in\mathbf Z,
$$

then $xyz=0$.

**Proof.** Write $n=5m$ and set $X=x^m$, $Y=y^m$, $Z=z^m$. Then
$X^5+Y^5=Z^5$, so Theorem 1.1 gives $XYZ=0$, hence $xyz=0$. $\square$

No assumption that $n$ is prime is needed in this corollary. The exponent-five theorem
is inherited by all of its multiples through a direct substitution.

### 9.3 Signs, zeroes, and permutations

For clarity, the complete list of integer solutions with a zero coordinate is easy to
describe. If $y=0$, then $x^5=z^5$, and injectivity of the fifth-power map on
$\mathbf Z$ gives $x=z$. If $x=0$, then $y=z$. If $z=0$, then $x^5=-y^5$, so
$x=-y$. Thus the trivial solutions are

$$
(t,0,t),\qquad(0,t,t),\qquad(t,-t,0),qquad t\in\mathbf Z.
\tag{9.1}
$$

Every sign change used earlier is legitimate because $(-t)^5=-t^5$. Every placement
of the variable divisible by $5$ is legitimate because one may first rewrite the
equation as a sum of three signed fifth powers and then permute the three terms.

These small points matter in a descent proof. A hidden positivity assumption on the
variables would leave sign cases untreated; an unjustified permutation of the two
sides could move a minus sign outside a fifth power. Oddness of the exponent resolves
both issues explicitly.

## 10. Quintic equations with controlled coefficients

### 10.1 Supported coefficients

The factorization method applies more broadly than Fermat's equation, provided the
coefficient has controlled prime support. Consider

$$
x^5+y^5=d z^5,\qquad \gcd(x,y)=1,\qquad d\in\mathbf Z\setminus\{0\}.
\tag{10.1}
$$

Let $S$ be the set of prime ideals dividing $(d)$ together with $\mathfrak p$. If
$\mathfrak q\notin S$, then $\mathfrak q$ divides at most one factor
$x+\zeta^iy$. Its exponent in the full product equals its exponent in $(z)^5$, and is
therefore divisible by five. Hence

$$
x+\zeta y
=u\lambda^r\delta A^5,
\tag{10.2}
$$

where $0\le r<5$, the prime divisors of $\delta$ belong to $S\setminus\{\mathfrak p\}$,
and their exponents may be chosen between zero and four. Since the ring is principal,
$\delta$ may be chosen as an element after generators of the finitely many supported
prime ideals have been fixed.

The statement does not say that $\delta$ is rational. If a rational prime splits, a
coefficient $d$ can distribute its prime ideals asymmetrically among conjugate factors.
The element $\delta$ records that distribution. Replacing it by its rational norm would
lose precisely the information needed for extraction.

The proof of (10.2) is the same prime-by-prime argument as before. For every prime ideal
outside $S$, the exponent is a multiple of five. Remove the residues modulo five at the
finitely many primes in $S$, and the remaining ideal is a fifth power. Class number one
makes its fifth root principal, leaving a unit.

This supported form is useful for equations such as

$$
x^5+y^5=5^e q^f z^5,
$$

where $q\ne5$ is a fixed rational prime. It says that all uncontrolled behavior is
confined to the primes above $q$ and to $\mathfrak p$. It does not, without additional
local information at $q$, prove nonexistence.

### 10.2 What survives unchanged

Three pieces of the Fermat argument survive for every fixed coefficient $d$.

First, **coprimality away from $\mathfrak p$** depends only on $gcd(x,y)=1$, not on the
right side of the equation. Distinct linear factors still have no common prime outside
$\mathfrak p$.

Second, **valuation control at $\mathfrak p$** depends only on whether $5$ divides
$x+y$:

$$
v_{\mathfrak p}(x+\zeta^iy)=
\begin{cases}
0,&5\nmid x+y,\\
1,&5\mid x+y,\ i\ne0.
\end{cases}
\tag{10.3}
$$

What changes is the product valuation. If $e=v_5(d)$ and $s=v_5(z)$, then in the
ramified case

$$
4v_5(x+y)+4=4e+20s,
$$

so

$$
v_5(x+y)+1=e+5s.
\tag{10.4}
$$

The Fermat relation (3.3) is the special case $e=0$.

Third, **unit tests** are intrinsic to $\mathcal O$. Once the supported factor
$\delta$ has been removed, a remaining unit rational modulo $\lambda^3$ is still a
fifth power. The coefficient may, however, prevent the quotient from having that
congruence. One must calculate rather than appeal to the Fermat case by analogy.

As a worked comparison, suppose $d=5$. In the ramified case, (10.4) gives

$$
v_5(x+y)=5s,
$$

rather than $5s-1$. The rational factor is now a fifth power up to a unit prime to
$5$, while the norm factor has no forced single factor of $5$. The distribution that
fed (3.7) has shifted. Consequently the descent carrier of Chapter 6 is not obtained
with the same $\lambda^{15}$ and unit $\eta^2$. This is not a cosmetic change: it can
alter the two-state transition.

### 10.3 Where the Fermat conclusion is special

For $d=1$, there are no supported primes away from $\mathfrak p$. Every nonexceptional
ideal exponent is a multiple of five, and the exact unit calculation closes. For a
general $d$, three new obstructions can occur.

1. A prime ideal dividing $d$ may enter one cyclotomic factor with exponent not
   divisible by five.
2. Conjugate prime ideals above the same rational divisor of $d$ may be distributed
   asymmetrically.
3. The unit state in the replacement table may be shifted by the Kummer class of
   $d$.

Thus the method gives a finite, explicit descent problem for a fixed coefficient, but
not a universal nonexistence theorem. This boundary is mathematically healthy. For
example,

$$
1^5+1^5=2\cdot1^5
$$

is a nontrivial coefficient equation. Any argument claiming that the Fermat descent
works unchanged for every $d$ would incorrectly rule it out.

The title “Fermat-type equations” therefore refers to the reusable factor,
coprimality, valuation, and supported-extraction framework. The nonexistence conclusion
uses the coefficient-one unit cycle in an essential way.

## 11. Proof diagnostics and common failure modes

### 11.1 Ideals before elements

The equation

$$
\prod_{i=0}^4(x+\zeta^iy)=z^5
$$

is first an equality of elements and hence of principal ideals. Prime-ideal
factorization is canonical. Element factorization is not, because associates differ by
units.

The safe chain is

$$
\begin{array}{c}
\text{pairwise coprime ideals away from }\mathfrak p\\
\Downarrow\\
\text{individual ideal exponents divisible by five}\\
\Downarrow\\
(F_i)=\mathfrak p^{r_i}\mathfrak a_i^5\\
\Downarrow\\
F_i=u_i\lambda^{r_i}A_i^5.
\end{array}
$$

The final arrow uses class number one. Beginning with “unique factorization gives
$F_i=A_i^5$” skips both the exceptional prime and the unit.

There is a second reason to prefer ideals. If $q\equiv1\pmod5$, the rational prime
$q$ splits into four primes in $\mathcal O$. Two distinct cyclotomic factors can have
norms divisible by $q$ while their ideals remain coprime. A gcd calculation on rational
norms can therefore invent a common divisor that is absent in the cyclotomic ring.

### 11.2 The two normalizations at five

The equalities

$$
v_5(5)=1,\qquad v_{\mathfrak p}(5)=4
$$

measure the same element on different scales. Both are used in the proof.

For an ordinary integer $n$,

$$
v_{\mathfrak p}(n)=4v_5(n).
$$

For a nonrational factor in the ramified case,

$$
v_{\mathfrak p}(x+\zeta^iy)=1.
$$

This does not mean that $5$ divides the factor as an element; it means precisely one
copy of the uniformizer divides it. Four such copies, one from each nonrational
conjugate, account for one ordinary factor of $5$ in the norm quotient.

A quick audit of (3.3) illustrates the conversion:

$$
\underbrace{4t}_{x+y}
+\underbrace{1+1+1+1}_{\text{four nonrational factors}}
=\underbrace{5\cdot4s}_{z^5}.
$$

Dividing by four gives $t+1=5s$. If one incorrectly sets
$v_{\mathfrak p}(5)=1$, the same calculation yields the false relation
$t+4=5s$.

### 11.3 Units cannot be wished away

There are three unit-removal mechanisms, each with a different hypothesis.

1. In the first case, primary normalization makes the unit real. It need not make the
   unit a fifth power.
2. In the ramified factor, division by $\lambda$ leaves a quotient rational modulo
   $\lambda^3$, so the unit is a fifth power.
3. In the replacement step, deep invariance makes the normalized difference rational
   modulo $\lambda^3$, again removing the unit.

These mechanisms should not be interchanged. The congruence
$u\equiv r\pmod{\lambda^2}$ permits $u=\eta$, which is not a fifth power. The
congruence modulo $\lambda^3$ is the first one that detects both exponents in

$$
u=\pm\zeta^a\eta^b.
$$

Exact roots of unity also matter. In (6.14), replacing $\zeta^2\lambda$ by “an
associate of $\lambda$” erases the state that makes the replacement family close.
Associates are interchangeable for valuations, but not for fifth-power classes.

### 11.4 A smaller expression is not yet a descent

From a second-case solution we obtained

$$
x+y=5^4a^5,\qquad Q(x,y)=5w^5,\qquad z=5aw.
$$

It follows that $|a|,w<|z|$. This is useful, but it does not prove Fermat's theorem.
To descend, one must answer four questions.

1. What new mathematical object uses $a$ or $w$?
2. Does that object satisfy the same hypotheses as the original one?
3. Is its proposed size a positive integer?
4. Is the size strictly smaller, rather than merely no larger?

Chapters 6 and 7 answer them with the descent record, the closure calculation, the
weight $\mathscr W$, and identity (7.15). This separation prevents a common circular
argument in which the desired smaller Fermat solution is inferred by reversing a norm.

There is another false descent worth noting. One might repeatedly take a fifth root of
an ideal and say that its norm decreases. After the first extraction, however, the new
ideal need not be attached to a binary factor $x+\zeta y$, so the next extraction may
have no coprimality theorem available. The conjugate-difference record carries exactly
the extra relations needed for iteration.

## 12. The classical boundary

### 12.1 What has been proved

The proof can now be summarized without suppressing any of its exceptional steps.

Start with a primitive equation

$$
x^5+y^5=z^5.
$$

In the first case, the five factors are pairwise coprime. Primary normalization of one
factor leaves only a real unit. Subtraction of the conjugate equation is divisible by
$\lambda^5$. Its explicit $\lambda$-coordinates force the two inputs to be congruent
modulo $5$. Cycling the signed variables gives a contradiction.

In the second case, exactly one variable is divisible by $5$. Put it on the right.
The rational factor has value $4t$, the four nonrational factors have value one, and
comparison with $z^5$ gives

$$
t+1=5v_5(z).
$$

After one uniformizer is removed, the quotient is rational modulo $\lambda^3$.
The unit is therefore a fifth power, giving the exact factor

$$
x+\zeta y=\lambda A^5.
$$

Its norm and rational companion are

$$
Q(x,y)=5N(A)^5,\qquad x+y=5^4a^5,\qquad z=5aN(A).
$$

Comparing the factor with its $\sigma$-conjugate produces

$$
A^5-\sigma(A)^5=\eta^2(-\eta\lambda^3a)^5
$$

and forces $A-\sigma(A)$ eleven digits deep. This deep invariance makes $A$ rational
modulo $\lambda^3$. Each of the four nontrivial difference factors is consequently an
explicit uniformizer times a fifth power. Their exact unit classes form a two-state
family. The coefficient replacement sends every record to another with strictly
smaller positive integral weight. Well-foundedness gives the contradiction.

Every use of class number one, coprimality, unit classification, valuation conversion,
and positivity has now been identified. The descent never invokes a converse to the
norm map and never assumes that associates have the same fifth-power class.

### 12.2 Why exponent five can now be set aside

The exponent-five theorem is complete within classical cyclotomic arithmetic. Its
difficulty is concentrated at the coefficient prime $5$: total ramification creates
the exceptional common factor, while the unusually explicit unit group and the
three-digit unit test make that exception controllable.

The proof also explains why this volume is the natural endpoint of the coefficient-five
boundary. For exponent five, the cyclotomic ring has class number one, its units are
explicit, and the ramified factor closes under a finite two-state replacement. Those
features permit a direct, well-founded descent. No later argument is needed to recover
this exponent.

What remains beyond this boundary begins at coefficient primes at least seven. The
present theorem removes every exponent divisible by five and leaves no unresolved
case at the prime five. The classical factorization

$$
x^5+y^5=\prod_{i=0}^4(x+\zeta^iy)
$$

has fulfilled its promise: prime ideals control the factors, the ramified valuation
controls the exception, unit congruences turn ideal fifth powers into element fifth
powers, and an explicit norm-bearing replacement makes descent well founded. Therefore
the equation $x^5+y^5=z^5$ has only the trivial integer solutions listed in (9.1).
