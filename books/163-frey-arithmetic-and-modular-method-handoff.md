# The Frey Curve: Arithmetic Reduction and the Exact Modular-Method Handoff

## Contents

1. [The endpoint of this book](#1-the-endpoint-of-this-book)
   - [Scope](#11-scope)
   - [Conventions](#12-conventions)
   - [Main theorem](#13-main-theorem)
2. [Reduction to prime exponent](#2-reduction-to-prime-exponent)
   - [Primitivity and signs](#21-primitivity-and-signs)
   - [Exponent three](#22-exponent-three)
   - [Exponent four](#23-exponent-four)
   - [Exponent five](#24-exponent-five)
   - [The exact prime-exponent split](#25-the-exact-prime-exponent-split)
3. [The normalized Fermat triple](#3-the-normalized-fermat-triple)
   - [Pairwise coprimality and parity](#31-pairwise-coprimality-and-parity)
   - [Notation forced by the equation](#32-notation-forced-by-the-equation)
4. [The Frey curve and its minimal models](#4-the-frey-curve-and-its-minimal-models)
   - [The raw curve and full two-torsion](#41-the-raw-curve-and-full-two-torsion)
   - [Minimality at odd primes](#42-minimality-at-odd-primes)
   - [The normalized minimal model at two](#43-the-normalized-minimal-model-at-two)
   - [Global minimal discriminant and conductor](#44-global-minimal-discriminant-and-conductor)
5. [The residual representation away from the coefficient prime](#5-the-residual-representation-away-from-the-coefficient-prime)
   - [Determinant, oddness, and good primes](#51-determinant-oddness-and-good-primes)
   - [Tate curves at multiplicative primes](#52-tate-curves-at-multiplicative-primes)
   - [The residual level calculation](#53-the-residual-level-calculation)
6. [Finite flatness and irreducibility at $p$](#6-finite-flatness-and-irreducibility-at-p)
   - [Good reduction at $p$](#61-good-reduction-at-p)
   - [Multiplicative reduction at $p$](#62-multiplicative-reduction-at-p)
   - [Irreducibility from full two-torsion](#63-irreducibility-from-full-two-torsion)
   - [From irreducible to absolutely irreducible](#64-from-irreducible-to-absolutely-irreducible)
7. [The exact special datum at two](#7-the-exact-special-datum-at-two)
   - [The Tate filtration and its sign](#71-the-tate-filtration-and-its-sign)
   - [The residual hardly-ramified SP datum](#72-the-residual-hardly-ramified-sp-datum)
   - [The deformation problem receiving the datum](#73-the-deformation-problem-receiving-the-datum)
8. [The exact modular-method handoff](#8-the-exact-modular-method-handoff)
   - [What has been proved before the handoff](#81-what-has-been-proved-before-the-handoff)
   - [The downstream implication](#82-the-downstream-implication)
   - [The resulting logical contract](#83-the-resulting-logical-contract)
9. [Dependency and coverage audit](#9-dependency-and-coverage-audit)
   - [Exact direct dependency ledger](#91-exact-direct-dependency-ledger)
   - [Blueprint coverage](#92-blueprint-coverage)
   - [Conclusion](#93-conclusion)

## 1. The endpoint of this book

### 1.1. Scope

This book isolates one reusable piece of the proof of Fermat's Last Theorem: the passage from a hypothetical Fermat solution to the precise residual deformation datum used by the later modular method.

There are two branches, and keeping them separate is essential.

1. Exponent $5$ is already eliminated by the independent descent proved in Book 162.
2. For every prime exponent $p\ge 7$, a normalized primitive solution produces a Frey curve whose mod-$p$ representation is absolutely irreducible, finite flat at $p$, and special of a prescribed sign at $2$.

The second branch is the Frey residual/deformation spine. Book 150 applies exactly in its natural range $p\ge 7$; it is not asked to prove anything at exponent $5$.

This book proves all arithmetic assertions needed to manufacture that spine. It does not construct a characteristic-zero lift, a compatible family, or the final modular contradiction. Those are outputs of later books. The last section records the exact implication that those later outputs must supply.

### 1.2. Conventions

All valuations $v_q$ are normalized by $v_q(q)=1$. Frobenius at an unramified prime means arithmetic Frobenius. The mod-$p$ cyclotomic character is denoted
$$
  \bar\chi_p:G_{\mathbf Q}\longrightarrow \mathbf F_p^\times.
$$
For an elliptic curve $E/\mathbf Q$, write
$$
  \bar\rho_{E,p}:G_{\mathbf Q}\longrightarrow
  \operatorname{GL}(E[p])
$$
for the action on its geometric $p$-torsion.

For each prime $q\ne p$, choose the $p$-primary tame character
$$
  t_{p,q}:I_q\longrightarrow \mathbf Z_p,
$$
normalized so that arithmetic Frobenius $F_q$ satisfies
$$
  t_{p,q}(F_q\sigma F_q^{-1})=q\,t_{p,q}(\sigma).
$$
Write $\bar t_{p,q}$ for its reduction modulo $p$. At $q=2$ we abbreviate
$t_{p,2}$ and $\bar t_{p,2}$ to $t_p$ and $\bar t_p$.

### 1.3. Main theorem

The result proved here is the following.

**Theorem 1.1 (Frey arithmetic package and handoff).**
Suppose that
$$
  x^n+y^n=z^n,\qquad xyz\ne 0,\qquad n>2.
$$
Then one of the following reductions applies.

- If $5\mid n$, the solution contradicts the exponent-$5$ theorem of Book 162.
- If $3\mid n$, the solution contradicts the elementary exponent-$3$ descent proved below.
- If $4\mid n$, the solution contradicts the elementary exponent-$4$ descent proved below.
- Otherwise some prime $p\ge 7$ divides $n$, and the solution gives a primitive triple
  $$
    a^p+b^p=c^p
  $$
  normalized by
  $$
    a\equiv0\pmod2,\qquad b\equiv c\equiv1\pmod4.
  $$
  The associated Frey curve
  $$
    E_{a,b,c,p}:y^2=x(x-a^p)(x+b^p)
  $$
  is semistable, has full rational $2$-torsion, and has
  $$
    \Delta_{\min}=2^{-8}(abc)^{2p},
    \qquad
    N_E=\prod_{q\mid abc}q.
  $$
  Its residual representation is odd and absolutely irreducible, has determinant
  $\bar\chi_p$, is unramified outside $\{2,p\}$, is finite flat at $p$, and at $2$ has the exact special form
  $$
    \bar\rho(\sigma)=I+\bar t_p(\sigma)\bar N
    \quad(\sigma\in I_2),
    \qquad
    \bar\rho(F_2)=
    \begin{pmatrix}2\bar s_2&0\\0&\bar s_2\end{pmatrix},
  $$
  where
  $$
    \bar N=\begin{pmatrix}0&1\\0&0\end{pmatrix},
    \qquad
    \bar s_2\in\{1,-1\}.
  $$
  The sign is $+1$ for split multiplicative reduction and $-1$ for nonsplit multiplicative reduction. The line
  $$
    L_2=\ker\bar N=\operatorname{im}\bar N
  $$
  is intrinsic.

Consequently the $p\ge7$ branch supplies exactly a residual point of the hardly-ramified, special-at-$2$, finite-flat-at-$p$ deformation problem used downstream.

The proof occupies Sections 2 through 7. Section 8 states the later endgame as a conditional implication.

## 2. Reduction to prime exponent

### 2.1. Primitivity and signs

Starting with a nonzero integral solution of
$$
  x^n+y^n=z^n,
$$
divide by the common greatest divisor. We may assume
$$
  \gcd(x,y,z)=1.
$$
If $n$ is odd, put $c=-z$; then
$$
  x^n+y^n+c^n=0.
$$
This symmetric form is convenient for the cubic and quintic descents. For
the Frey construction we retain the equivalent form with one power on the
right.

If a prime $p\mid n$, write $n=pm$. Then
$$
  (x^m)^p+(y^m)^p=(z^m)^p.
$$
Thus a solution at exponent $n$ produces one at exponent $p$. If $4\mid n$, the same observation produces a solution at exponent $4$.

It remains to remove exponents $3,4,5$. The exponent-$5$ case is imported from Book 162; the other two are included so that the elementary reduction is complete.

### 2.2. Exponent three

We use the equivalent symmetric statement, which lets the variable divisible
by $3$ be moved into the distinguished position without losing signs.

**Proposition 2.1.**
There are no nonzero integers $X,Y,Z$ satisfying
$$
  X^3+Y^3+Z^3=0.
$$

**Proof.**
Suppose otherwise and choose a primitive solution with $|Z|$ minimal after permuting the variables. Cubes modulo $9$ are $0,\pm1$. Primitivity and the displayed equation imply that exactly one of $X,Y,Z$ is divisible by $3$; take it to be $Z$. Then
$$
  3\nmid XY,\qquad X+Y\equiv0\pmod3.
$$
Write
$$
  X+Y=3M.
$$
The factorization
$$
  X^3+Y^3=(X+Y)(X^2-XY+Y^2)
$$
and the substitution $Y=3M-X$ give
$$
  X^2-XY+Y^2
  =3\bigl(X^2-3MX+3M^2\bigr).
$$
Put
$$
  N=X^2-3MX+3M^2.
$$
Since $3\nmid X$, one has $3\nmid N$. Any common divisor of $M$ and $N$ divides $X^2$, and then also $Y$; primitivity gives
$$
  \gcd(M,N)=1.
$$
Therefore
$$
  Z^3=-9MN.
$$
The coprimality and the $3$-adic valuations show that, after absorbing signs,
$$
  M=3r^3
$$
for some nonzero integer $r$. In particular
$$
  X+Y=9r^3. \tag{2.1}
$$

Now work in the Eisenstein integer ring
$$
  R=\mathbf Z[\omega],
  \qquad
  \omega^2+\omega+1=0.
$$
This ring is Euclidean for the norm
$$
  \operatorname N(u+v\omega)=u^2-uv+v^2,
$$
because choosing a nearest point in the triangular lattice gives a remainder
of strictly smaller norm. It is therefore a unique factorization domain.
Let $\lambda=1-\omega$; then
$$
  3=-\omega^2\lambda^2.
$$
The three factors
$$
  X+Y,\qquad X+\omega Y,\qquad X+\omega^2Y
$$
are pairwise coprime away from $\lambda$. Because $3\nmid XY$ and $3\mid X+Y$, direct reduction modulo $\lambda^2$ gives
$$
  v_\lambda(X+\omega Y)=1.
$$
Unique factorization therefore yields
$$
  X+\omega Y=\varepsilon\lambda(\alpha+\beta\omega)^3,
  \qquad
  \varepsilon\in R^\times.
  \tag{2.2}
$$

Set
$$
  U=\alpha^3-3\alpha\beta^2+\beta^3,
  \qquad
  V=3\alpha\beta(\alpha-\beta),
$$
so that
$$
  (\alpha+\beta\omega)^3=U+V\omega.
$$
The element $\alpha+\beta\omega$ is not divisible by $\lambda$, for otherwise
the right side of (2.2) would have $\lambda$-valuation at least four.
Consequently
$$
  U\equiv\alpha+\beta\not\equiv0\pmod3,
  \qquad
  3\mid V.
$$
Multiplication by $\lambda$, $-\omega\lambda$, or $\omega^2\lambda$, up to an overall sign, makes the sum of the two rational coefficients respectively
$$
  3V,\qquad 3(U-V),\qquad -3U.
$$
In the last two cases that sum has exactly one factor of $3$, whereas (2.1) has at least two. Thus the unit in (2.2) may be absorbed so that the first case holds. Comparing coefficient sums with (2.1) gives
$$
  r^3=\pm\alpha\beta(\alpha-\beta).
$$
The three integers
$$
  \alpha,\qquad \beta,\qquad \alpha-\beta
$$
are pairwise coprime: a common prime would divide both coefficients in (2.2), contrary to the primitive construction. Hence each is a signed cube:
$$
  \alpha=u^3,\qquad \beta=v^3,\qquad \alpha-\beta=w^3.
$$
After changing signs,
$$
  v^3+w^3=u^3.
$$
This is a new nonzero solution.

Finally, taking norms in (2.2) and using $X^3+Y^3=-Z^3$ shows
$$
  \operatorname N(\alpha+\beta\omega)^3
  =\frac{|Z|^3}{27|r|^3}.
$$
Since $r\ne0$,
$$
  \operatorname N(\alpha+\beta\omega)<|Z|.
$$
The positive definite norm dominates the absolute values of $\alpha$, $\beta$, and $\alpha-\beta$. Hence all three entries of the new solution have absolute value strictly below $|Z|$. The same modulo-$9$ argument says that exactly one of them is divisible by $3$; after writing the equation again in symmetric form, its distinguished entry contradicts minimality. $\square$

### 2.3. Exponent four

**Proposition 2.2.**
There are no nonzero integers $X,Y,Z$ satisfying
$$
  X^4+Y^4=Z^2.
$$
In particular there are no nonzero solutions of $X^4+Y^4=Z^4$.

**Proof.**
Replace $X,Y$ by their absolute values and $Z$ by $|Z|$. If
$d=\gcd(X,Y)$, valuation comparison in
$X^4+Y^4=Z^2$ shows that $d^2\mid Z$, so division by
$(d,d,d^2)$ produces a primitive solution. Choose one with $Z>0$
minimal.

Exactly one of $X,Y$ is even: they cannot both be even by primitivity, and if both were odd then their fourth powers would sum to $2$ modulo $16$, which is not a square. Take $Y$ even. The primitive Pythagorean triple
$$
  (X^2,Y^2,Z)
$$
has a parametrization
$$
  X^2=m^2-n^2,\qquad
  Y^2=2mn,\qquad
  Z=m^2+n^2,
$$
where
$$
  m>n>0,\qquad \gcd(m,n)=1,
$$
and $m,n$ have opposite parity. Take $n$ even. Since $2mn$ is a square and $m,n$ are coprime, there are coprime $R,S>0$ such that
$$
  m=R^2,\qquad n=2S^2.
$$
Indeed every odd prime occurs to an even exponent in each of $m,n$, while
$1+v_2(n)$ is even, so the remaining power of $2$ in $n/2$ is a square.
Now
$$
  X^2+(2S^2)^2=R^4
$$
is another primitive Pythagorean triple: any common divisor of $X$ and
$2S^2$ would also divide $m$ and $n$. Its parametrization gives coprime $H>K>0$ of opposite parity with
$$
  X=H^2-K^2,\qquad 2S^2=2HK,\qquad R^2=H^2+K^2.
$$
Because $HK=S^2$ and $\gcd(H,K)=1$, both $H$ and $K$ are squares:
$$
  H=U^2,\qquad K=V^2.
$$
Consequently
$$
  U^4+V^4=R^2.
$$
This is another nonzero solution of the same type, but
$$
  0<R<Z=m^2+n^2,
$$
contradicting the minimality of $Z$. $\square$

### 2.4. Exponent five

We use the following accepted result exactly once.

**Theorem 2.3 (Book 162).**
There are no nonzero integers $X,Y,Z$ satisfying
$$
  X^5+Y^5+Z^5=0.
$$

Book 162 proves this theorem by descent in $\mathbf Z[\zeta_5]$. Its proof, including the ramified prime above $5$, the unit calculation, and the class-number-one input, is independent of the Frey-curve argument here. No result from Book 150 is used for exponent $5$.

### 2.5. The exact prime-exponent split

**Proposition 2.4.**
Every nonzero solution at exponent $n>2$ is eliminated by the
exponent-$3$, exponent-$4$, or exponent-$5$ result when the corresponding
number divides $n$. In every remaining case it produces a primitive
solution at a prime exponent $p\ge7$.

**Proof.**
Divisibility by $3$ or $5$ reduces the equation to the corresponding prime
exponent, and divisibility by $4$ reduces it to exponent $4$; the three
results above give contradictions. If none of $3,4,5$ divides $n$, then
$n>2$ has an odd prime divisor $p\ne3,5$, hence $p\ge7$.
Exponent reduction gives a $p$-power solution, and division by its common
greatest divisor makes it primitive. $\square$

For the rest of the book, fix a prime
$$
  p\ge7
$$
and a primitive nonzero solution
$$
  a^p+b^p=c^p.
  \tag{2.3}
$$

## 3. The normalized Fermat triple

The Frey equation is sensitive to which leg is even and to the odd residues
modulo $4$. A careless signed permutation changes the equation and can
invalidate the integral model at $2$. This chapter makes the permitted
normalization explicit before any curve is introduced.

### 3.1. Pairwise coprimality and parity

Primitivity of (2.3) implies pairwise coprimality. Indeed, a prime dividing any two of $a,b,c$ divides the third.

Modulo $2$, precisely one of $a,b,c$ is even. They cannot all be odd because
$$
  1+1\not\equiv1\pmod2,
$$
and they cannot contain two even entries because pairwise coprimality would then force the third to be even as well.

We may put the even entry in the first position while preserving the shape of the equation. If $a$ or $b$ is even, merely interchange them. If $c$ is even, replace
$$
  (a,b,c)\quad\text{by}\quad(-c,a,-b);
$$
because $p$ is odd,
$$
  (-c)^p+a^p=(-b)^p.
$$
Thus from now on $a$ is even and $b,c$ are odd.

Reducing (2.3) modulo $4$ gives
$$
  b\equiv c\pmod4,
$$
since $a^p\equiv0\pmod4$ and $u^p\equiv u\pmod4$ for odd $u$ and odd $p$. If necessary replace all three entries by their negatives. We have therefore proved the normalization
$$
  a\equiv0\pmod2,
  \qquad
  b\equiv c\equiv1\pmod4.
  \tag{3.1}
$$

### 3.2. Notation forced by the equation

Put
$$
  A=a^p,\qquad B=b^p,\qquad C=c^p.
$$
Then
$$
  A+B=C,
  \tag{3.2}
$$
the three integers $A,B,C$ are pairwise coprime, and
$$
  v_2(A)=p\,v_2(a)\ge7,
  \qquad
  B\equiv C\equiv1\pmod4.
  \tag{3.3}
$$
These congruences are exactly what the dyadic minimal model will use.

## 4. The Frey curve and its minimal models

Three features must be computed together: the rational two-torsion, the
minimal discriminant at every prime, and the split or nonsplit character of
each node. The raw cubic displays the first feature and all odd local
behavior, while a single integral coordinate change exposes the true
dyadic model.

### 4.1. The raw curve and full two-torsion

Attach to the normalized triple the curve
$$
  E=E_{a,b,c,p}:
  \qquad
  y^2=x(x-A)(x+B).
  \tag{4.1}
$$
The roots $0,A,-B$ are distinct because $ABC\ne0$ and $A+B=C\ne0$. Hence (4.1) is a nonsingular elliptic curve.

Its nonzero points of order $2$ are exactly
$$
  (0,0),\qquad(A,0),\qquad(-B,0).
  \tag{4.2}
$$
Thus
$$
  E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2.
  \tag{4.3}
$$
As a finite étale group scheme over $\mathbf Q$, the full two-torsion is
constant. It therefore has the constant extension
$$
  \mathcal T_2:=(\mathbf Z/2\mathbf Z)^2_{\mathbf Z[1/2]},
  \qquad
  \mathcal T_{2,\mathbf Q}\simeq E[2].
  \tag{4.4}
$$
The rational full-two structure, not merely the
numerical divisibility of $\#E[2](\mathbf Q)$, is the input to Book 150.

Expanding (4.1) gives
$$
  y^2=x^3+(B-A)x^2-ABx.
$$
The integral invariant formulas yield
$$
\begin{aligned}
  c_4&=16(A^2+AB+B^2),\\
  c_6&=-32(B-A)(2A^2+5AB+2B^2),\\
  \Delta&=16A^2B^2C^2
          =2^4(abc)^{2p},\\
  j&=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}.
\end{aligned}
\tag{4.5}
$$
The discriminant is $16$ times the square of the product of the three root differences:
$$
  A,\qquad B,\qquad A+B=C.
$$

### 4.2. Minimality at odd primes

Let $q$ be odd. If $q\nmid abc$, the discriminant in (4.5) is a unit at $q$, so $E$ has good reduction.

Suppose $q\mid a$. Then $B$ and $C$ are units, while
$$
  A^2+AB+B^2\equiv B^2\not\equiv0\pmod q.
$$
Thus $c_4$ is a $q$-adic unit. The displayed integral model is minimal and has multiplicative reduction, with
$$
  v_q(\Delta_{\min})=2p\,v_q(a).
$$
The same argument applies when $q\mid b$ or $q\mid c$. Pairwise coprimality ensures that only one case occurs, and we obtain
$$
  v_q(\Delta_{\min})=2p\,v_q(abc)
  \qquad(q\mid abc,\ q\text{ odd}).
  \tag{4.6}
$$

The splitness can also be read directly from the node. If $q\mid a$, the
reduction begins $y^2=B x^2+$ terms of degree at least three at the
origin. If $q\mid b$, it begins $y^2=-A x^2+$ higher terms. If
$q\mid c$, translate the repeated root $A=-B$ to the origin; the
tangent equation is then $y^2=A u^2$. Thus the tangent cone has the
following square class:

| bad odd prime | repeated root | tangent coefficient | split precisely when |
|---|---:|---:|---|
| $q\mid a$ | $0$ | $B$ | $b$ is a square modulo $q$ |
| $q\mid b$ | $0$ | $-A$ | $-a$ is a square modulo $q$ |
| $q\mid c$ | $A=-B$ | $A$ | $a$ is a square modulo $q$ |

Here raising to the odd power $p$ does not change a square class. This table fixes every odd local splitting character, although only the dyadic sign will be built into the later special deformation condition.

### 4.3. The normalized minimal model at two

The raw equation is not minimal at $2$. Make the change
$$
  x=4x',
  \qquad
  y=8y'+4x'.
  \tag{4.7}
$$
After dividing by $64$ and suppressing primes on the new coordinates, one gets
$$
  y^2+xy
  =
  x^3+\frac{B-A-1}{4}x^2-\frac{AB}{16}x.
  \tag{4.8}
$$
Both coefficients are integral: (3.3) gives $4\mid B-A-1$, while
$$
  v_2(AB)=p\,v_2(a)\ge7.
$$

The invariants of (4.8) are
$$
\begin{aligned}
  c_{4,\min}&=A^2+AB+B^2,\\
  c_{6,\min}&=-\frac12(B-A)(2A^2+5AB+2B^2),\\
  \Delta_{\min}&=2^{-8}A^2B^2C^2.
\end{aligned}
\tag{4.9}
$$
The first is odd, so (4.8) is minimal and has multiplicative reduction at $2$. Its discriminant exponent is
$$
  m_2:=v_2(\Delta_{\min})
  =2p\,v_2(a)-8.
  \tag{4.10}
$$
In particular
$$
  m_2>0,
  \qquad
  m_2\equiv-8\not\equiv0\pmod p.
  \tag{4.11}
$$

Put
$$
  d=\frac{B-A-1}{4}.
$$
Since $AB/16$ is even, reduction of (4.8) modulo $2$ is
$$
  y^2+xy=x^3+\bar d x^2.
$$
Its unique singular point is the origin, and its tangent cone is
$$
  y^2+xy+\bar d x^2.
$$
Writing $y=tx$, the two tangent directions are rational over
$\mathbf F_2$ precisely when
$$
  t^2+t+\bar d
$$
splits, which is equivalent to $\bar d=0$. Now
$$
  d\equiv\frac{B-1}{4}\pmod2,
$$
and $B=b^p\equiv b\pmod8$ because $p$ is odd. The split-node criterion
therefore gives
$$
  s_2=
  \begin{cases}
    +1,&b\equiv1\pmod8
       \quad\text{(split multiplicative)},\\
    -1,&b\equiv5\pmod8
       \quad\text{(nonsplit multiplicative)}.
  \end{cases}
  \tag{4.12}
$$
The normalization $b\equiv1\pmod4$ leaves exactly these two cases.

### 4.4. Global minimal discriminant and conductor

The local calculations prove that $E$ is semistable everywhere: it has good or multiplicative reduction at every finite prime. Combining (4.6) and (4.10),
$$
  \boxed{\Delta_{\min}=2^{-8}(abc)^{2p}.}
  \tag{4.13}
$$
The exponent is positive at $2$, so the right side is an integer.

A multiplicative prime contributes conductor exponent $1$, while a good prime contributes $0$. Therefore
$$
  \boxed{N_E=\operatorname{rad}(|abc|)
  =\prod_{q\mid abc}q.}
  \tag{4.14}
$$
Since $2\mid a$, the prime $2$ occurs exactly once in this product.

## 5. The residual representation away from the coefficient prime

The conductor of the curve still contains every prime dividing $abc$, but
the residual conductor does not. Tate uniformization explains the
difference: a multiplicative extension becomes unramified modulo $p$
exactly when its minimal-discriminant exponent is divisible by $p$. This
chapter performs that cancellation while retaining the dyadic
transvection.

### 5.1. Determinant, oddness, and good primes

Let
$$
  \bar\rho=\bar\rho_{E,p}:G_{\mathbf Q}
  \longrightarrow\operatorname{GL}_2(\mathbf F_p).
  \tag{5.1}
$$
The Weil pairing gives
$$
  \det\bar\rho=\bar\chi_p.
  \tag{5.2}
$$
For complex conjugation $c_\infty$,
$$
  \det\bar\rho(c_\infty)=\bar\chi_p(c_\infty)=-1,
$$
so $\bar\rho$ is odd.

At a good prime $q\ne p$, the representation is unramified and
$$
  \det\!\left(X-\bar\rho(\operatorname{Frob}_q)\right)
  \equiv X^2-a_q(E)X+q\pmod p,
  \tag{5.3}
$$
where
$$
  a_q(E)=q+1-\#E(\mathbf F_q).
$$

### 5.2. Tate curves at multiplicative primes

Let $q\ne p$ be a multiplicative prime and set
$$
  m_q=v_q(\Delta_{\min}).
$$
After at most the unramified quadratic extension that makes the reduction split, Tate uniformization supplies a basis in which
$$
  \bar\rho(\sigma)=
  \begin{pmatrix}
    1&m_q\bar t_{p,q}(\sigma)\\
    0&1
  \end{pmatrix}
  \qquad(\sigma\in I_q).
  \tag{5.4}
$$
An unramified quadratic twist changes the diagonal Frobenius sign but not this inertia calculation. It follows that
$$
  \bar\rho|_{I_q}\text{ is trivial}
  \quad\Longleftrightarrow\quad
  p\mid m_q.
  \tag{5.5}
$$

For every odd $q\mid abc$, equation (4.6) makes $m_q$ divisible by $p$. Hence $\bar\rho$ is unramified at all odd primes $q\ne p$, including the odd primes of bad reduction of $E$.

More precisely, let $\eta_q$ be the unramified splitting character, with
$\eta_q(F_q)=s_q\in\{1,-1\}$. The Tate filtration is
$$
  0\longrightarrow\mathbf F_p(1)\otimes\eta_q
  \longrightarrow E[p]
  \longrightarrow\mathbf F_p\otimes\eta_q
  \longrightarrow0.
$$
At an odd bad prime $q\ne p$, the representation is unramified and
$$
  \det\!\left(X-\bar\rho(F_q)\right)
  =(X-\bar s_q)(X-q\bar s_q).
  \tag{5.6}
$$
The value of $s_q$ is exactly the splitness computed in the table of
Section 4.2.

At $2$, however, (4.11) gives
$$
  m_2\not\equiv0\pmod p.
$$
Thus $\bar\rho(I_2)$ is a nontrivial cyclic group of order $p$, generated by a transvection. Its invariant subspace has codimension $1$, so the Artin conductor exponent at $2$ is exactly $1$.
Wild inertia is pro-$2$ and acts trivially on this odd-order tame image, so
there is no Swan contribution.

We have proved
$$
  \bar\rho\text{ is unramified outside }\{2,p\},
  \qquad
  N(\bar\rho)_{\text{prime-to-}p}=2.
  \tag{5.7}
$$
The latter is the residual conductor, not the conductor (4.14) of the elliptic curve.

### 5.3. The residual level calculation

The cancellation at the odd bad primes is the arithmetic reason the Frey curve is useful. In one line,
$$
  v_q(\Delta_{\min})\equiv
  \begin{cases}
    0\pmod p,&q\mid abc,\ q\text{ odd},\\
    -8\pmod p,&q=2.
  \end{cases}
  \tag{5.8}
$$
Thus all the variable odd primes in the curve conductor disappear from the prime-to-$p$ conductor of $E[p]$, while $2$ remains with conductor exponent one.

## 6. Finite flatness and irreducibility at $p$

The coefficient prime requires two independent assertions. Finite flatness
is integral local geometry and must be proved separately in the good and
multiplicative cases. Irreducibility is global; it comes from semistability
and full rational two-torsion only after the range $p\ge7$ has been fixed.

### 6.1. Good reduction at $p$

There are two possibilities at the coefficient prime. First suppose
$$
  p\nmid abc.
$$
Then (4.5) has $p$-adic unit discriminant, so $E$ has good reduction over $\mathbf Z_p$. Let $\mathcal E/\mathbf Z_p$ be its smooth proper elliptic model. Multiplication by $p$ on $\mathcal E$ is finite locally free of degree $p^2$; hence
$$
  \mathcal E[p]
$$
is a finite flat commutative group scheme over $\mathbf Z_p$ with generic fiber $E[p]$. Thus $\bar\rho|_{G_{\mathbf Q_p}}$ is finite flat.

### 6.2. Multiplicative reduction at $p$

Now suppose $p\mid abc$. The curve has multiplicative reduction and
$$
  v_p(\Delta_{\min})=2p\,v_p(abc),
  \tag{6.1}
$$
which is divisible by $p$.

After at most an unramified quadratic extension $K/\mathbf Q_p$, the curve is a Tate curve $E_q$. Let $R$ be the valuation ring of $K$, let $\pi$ be a uniformizer, and write
$$
  v_K(q)=ps,
  \qquad
  q=(\pi^s)^p u,
  \qquad
  u\in R^\times.
  \tag{6.2}
$$
The Tate $p$-torsion has its canonical exact sequence
$$
  0\longrightarrow\mu_p\longrightarrow E_q[p]
  \longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0.
  \tag{6.3}
$$

The integral extension can be written explicitly. For
$i=0,\ldots,p-1$, set
$$
  \mathcal G_i
  =\operatorname{Spec}R[T_i]/(T_i^p-u^i),
  \qquad
  \mathcal G=\coprod_{i=0}^{p-1}\mathcal G_i.
  \tag{6.4}
$$
Each component is finite free of rank $p$. Multiplication uses
$T_iT_j$ if $i+j<p$, and $T_iT_j/u$ after reducing $i+j$ modulo $p$. It makes $\mathcal G$ a finite flat commutative group scheme of rank $p^2$, fitting into
$$
  0\longrightarrow\mu_p\longrightarrow\mathcal G
  \longrightarrow(\mathbf Z/p\mathbf Z)_R\longrightarrow0.
  \tag{6.5}
$$
On the generic fiber, a point $T_i=z$ maps to the Tate parameter
$$
  (\pi^s)^i z;
$$
its $p$-th power is $q^i$, so (6.5) identifies with (6.3).

If the reduction was nonsplit, the unramified quadratic splitting character acts as finite étale descent data on this construction. Descent preserves finite flatness. Hence $E[p]$ has a finite flat model over $\mathbf Z_p$ in the multiplicative case as well.
The scalar action of $\mathbf F_p$ is induced by the multiplication maps of
the group scheme and is preserved by the descent, so the model is
coefficient-linear in the sense used by the deformation condition.

Combining the two cases proves
$$
  \boxed{\bar\rho|_{G_{\mathbf Q_p}}\text{ is finite flat}.}
  \tag{6.6}
$$
This is a coefficient-prime integral assertion. It does not say that $\bar\rho$ is unramified at $p$, and it does not say that the elliptic curve has good reduction there.

### 6.3. Irreducibility from full two-torsion

Book 150 proves the following theorem in exactly the range needed here.

**Semistable full-two irreducibility theorem.** If $E/\mathbf Q$ is
semistable, if
$$
  E[2](\mathbf Q)\simeq(\mathbf Z/2\mathbf Z)^2,
$$
and if $p\ge7$ is prime, then $E[p]$ has no
$G_{\mathbf Q}$-stable $\mathbf F_p$-line.

The Frey curve is semistable by Section 4.4 and has full rational two-torsion by Section 4.1. Therefore
$$
  \bar\rho\text{ is irreducible over }\mathbf F_p.
  \tag{6.7}
$$
The lower bound $p\ge7$ is essential to this invocation. Exponent $5$ has already been discharged by Book 162 and never enters this argument.

### 6.4. From irreducible to absolutely irreducible

The later global deformation problem requires absolute irreducibility, so we record the short upgrade.

**Proposition 6.1.**
The representation $\bar\rho$ is absolutely irreducible.

**Proof.**
Suppose an irreducible two-dimensional representation over $\mathbf F_p$ were not absolutely irreducible. Its commuting algebra would then be $\mathbf F_{p^2}$, and its underlying space would be one-dimensional over that field. Every Galois element would act $\mathbf F_{p^2}$-linearly.

Complex conjugation would therefore act by a scalar
$$
  \alpha\in\mathbf F_{p^2}^\times
  \quad\text{with}\quad
  \alpha^2=1.
$$
Since $p$ is odd, $\alpha=\pm1$. As an $\mathbf F_p$-linear map on a two-dimensional space, either scalar has determinant $1$. This contradicts
$$
  \det\bar\rho(c_\infty)=-1
$$
from (5.2). $\square$

In particular
$$
  \operatorname{End}_{\mathbf F_p[G_{\mathbf Q}]}(E[p])
  =\mathbf F_p,
  \tag{6.8}
$$
the global Schur condition used in the deformation theory.

## 7. The exact special datum at two

Conductor one alone is not a sufficiently precise deformation condition.
The downstream theory retains the monodromy line, the Frobenius-return
factor, and the splitness sign. We now turn the dyadic Tate calculation
into those exact matrices and then spell out the deformation problem they
define.

### 7.1. The Tate filtration and its sign

Let
$$
  \eta_2:G_{\mathbf Q_2}\longrightarrow\{1,-1\}
$$
be the unramified splitting character, normalized by
$$
  \eta_2(F_2)=s_2.
  \tag{7.1}
$$
For split multiplicative reduction $\eta_2=1$; for nonsplit multiplicative reduction it is the unramified quadratic character. Tate uniformization gives the exact residual sequence
$$
  0\longrightarrow
  \mathbf F_p(1)\otimes\eta_2
  \longrightarrow E[p]
  \longrightarrow
  \mathbf F_p\otimes\eta_2
  \longrightarrow0.
  \tag{7.2}
$$

In a basis respecting this filtration, inertia acts by
$$
  \bar\rho(\sigma)
  =
  I+m_2\bar t_p(\sigma)e_{12}
  \qquad(\sigma\in I_2).
  \tag{7.3}
$$
Since $m_2\not\equiv0\pmod p$, rescale the quotient basis vector and put
$$
  \bar N=e_{12}
  =
  \begin{pmatrix}0&1\\0&0\end{pmatrix}.
  \tag{7.4}
$$
Then
$$
  \bar\rho(\sigma)=I+\bar t_p(\sigma)\bar N.
  \tag{7.5}
$$
In particular $\bar N^2=0$, $\bar N\ne0$, and
$$
  L_2:=\ker\bar N=\operatorname{im}\bar N
  \tag{7.6}
$$
is a uniquely determined $G_{\mathbf Q_2}$-stable line.

Arithmetic Frobenius acts on the subline in (7.2) by $2s_2$ and on the quotient by $s_2$. Any off-diagonal Frobenius entry can be removed by changing the lift of the quotient basis vector, because the two eigenvalues differ by the nonzero scalar $s_2$. Hence
$$
  \bar\rho(F_2)=
  \begin{pmatrix}
    2\bar s_2&0\\
    0&\bar s_2
  \end{pmatrix},
  \qquad
  \bar s_2\in\{1,-1\}\subset\mathbf F_p^\times.
  \tag{7.7}
$$
The tame relation becomes
$$
  \bar\rho(F_2)\bar N\bar\rho(F_2)^{-1}
  =2\bar N.
  \tag{7.8}
$$
Equations (7.5)--(7.8), including the sign from (4.12), are stronger than the bare statement that inertia has a rank-one quotient. They specify the oriented special residual point used downstream.

### 7.2. The residual hardly-ramified SP datum

The Frey representation now satisfies the following complete ledger:

1. $p\ge7$;
2. $\bar\rho:G_{\mathbf Q}\to\operatorname{GL}_2(\mathbf F_p)$ is continuous and absolutely irreducible;
3. $\det\bar\rho=\bar\chi_p$;
4. $\bar\rho$ is odd;
5. $\bar\rho$ is unramified outside $\{2,p\}$;
6. at $2$, it has nonzero conductor-one special monodromy (7.5), the Frobenius relation (7.8), the intrinsic line (7.6), and the fixed sign $\bar s_2$;
7. at $p$, it is coefficient-linearly finite flat over $\mathbf Z_p$.

This is exactly the residual input called the hardly-ramified, special-at-$2$, finite-flat-at-$p$ datum.

### 7.3. The deformation problem receiving the datum

For precision, let $\mathcal O$ be a finite extension of $\mathbf Z_p$ with
residue field $k$ containing $\mathbf F_p$, put
$\bar\rho_k=\bar\rho\otimes_{\mathbf F_p}k$, and let $A$ be a local
Artinian $\mathcal O$-algebra with residue field $k$. The downstream
global deformation problem considers strict-equivalence classes of lifts of
$\bar\rho_k$,
$$
  \rho_A:G_{\mathbf Q,\{2,p,\infty\}}
  \longrightarrow\operatorname{GL}_2(A)
  \tag{7.9}
$$
subject to all of the following conditions:

- fixed determinant
  $$
    \det\rho_A=\chi_p;
    \tag{7.10}
  $$
- no ramification outside $\{2,p\}$;
- coefficient-linear finite flatness over $\mathbf Z_p$ at $p$;
- at $2$, trivial wild inertia and an endomorphism $N_A$ lifting $\bar N$ such that
  $$
    \rho_A(\sigma)=I+t_p(\sigma)N_A,
    \qquad N_A^2=0
    \quad(\sigma\in I_2);
    \tag{7.11}
  $$
- with $F_A=\rho_A(F_2)$,
  $$
    F_AN_AF_A^{-1}=2N_A;
    \tag{7.12}
  $$
- the unramified character on the quotient by
  $$
    L_A=\ker N_A=\operatorname{im}N_A
  $$
  has Frobenius value equal to the fixed lift
  $$
    s_2\in\{1,-1\}\subset\mathcal O^\times.
    \tag{7.13}
  $$

Here coefficient-linear finite flatness means that
$\rho_A|_{G_{\mathbf Q_p}}$ is identified with the geometric generic fiber
of a finite locally free commutative group scheme
$\mathcal G_A/\mathbf Z_p$, equipped with an action
$$
  A\longrightarrow
  \operatorname{End}_{\mathbf Z_p}(\mathcal G_A)
$$
that induces the given free rank-two $A$-module structure.

Because $\bar N\ne0$ has rank one, one entry of every $N_A$ is a unit. Thus $L_A$ is a direct-summand line, and (7.11) determines $N_A$ from the representation after choosing an inertia element on which $t_p$ is $1$. The condition is therefore intrinsic and remains on the closed nonzero-monodromy branch; it is not an auxiliary choice of a line and it does not admit an unintended unramified component.

The quotient character in (7.13) is the unique unramified character
$\eta_A$ with $\eta_A(F_2)=s_2$, so $\eta_A^2=1$. The fixed
determinant then makes the subline character $\chi_p\eta_A$. Thus the
lifted filtration has exactly the same orientation as (7.2).

This book supplies the residual point of this deformation problem. It makes no assertion here that the functor is representable, that a characteristic-zero point exists, or that such a point belongs to a compatible family.

## 8. The exact modular-method handoff

The arithmetic reduction and the later modular argument meet at a sharply
defined boundary. Recording that boundary prevents a residual datum from
being mistaken for a characteristic-zero lift, and prevents the final
contradiction from being invoked before its stronger compatible-family and
integral-lattice hypotheses exist.

### 8.1. What has been proved before the handoff

Assuming a Fermat solution, the arithmetic completed in this book produces:

- no exponent-$5$ branch, by Book 162;
- for the only remaining prime exponents $p\ge7$, the exact residual datum of Section 7.2;
- the precise signed SP deformation condition in which any later lift must lie.

No variable prime remains in the residual level. No local hypothesis needed by the Frey-SP deformation problem is left implicit.

### 8.2. The downstream implication

The later modular endgame proves an implication whose antecedent is strictly stronger than the output of this book. It may be stated as follows.

**Downstream endgame implication.**
Suppose the residual Frey datum produced here is carried through the later
lifting and changing-prime arguments to a pure weight-one compatible family
on the same SP branch. Write $K$ for the coefficient completion at a place
above $3$ and $\mathcal O$ for its ring of integers. Suppose the member there
has:

1. a continuous two-dimensional representation
   $$
     \rho_3:G_{\mathbf Q}\longrightarrow\operatorname{GL}_K(V)
   $$
   with determinant $\chi_3$, unramified outside $\{2,3\}$, and the common pure weight-one good-prime polynomials;
2. the exact signed SP filtration at $2$;
3. a globally stable free rank-two lattice $T\subset V$ whose every quotient by a power of the coefficient uniformizer has a compatible coefficient-linear finite-flat model over $\mathbf Z_3$.

Then the later finite-flat classification and endgame give
$$
  0\longrightarrow\mathcal O(1)\longrightarrow T
  \longrightarrow\mathcal O\longrightarrow0
  \tag{8.1}
$$
and hence
$$
  \operatorname{tr}\rho_3(g)=1+\chi_3(g).
  \tag{8.2}
$$
At arithmetic Frobenius $5$, compatibility gives
$$
  a_5=6,
  \tag{8.3}
$$
whereas weight-one purity gives
$$
  |a_5|\le2\sqrt5.
  \tag{8.4}
$$
Since $6>2\sqrt5$, the antecedent leads to a contradiction.

This is an implication from the later endgame, not an existence theorem asserted in the present book. In particular, (8.1) is not deduced merely from the residual representation and is not used in proving any result above.

### 8.3. The resulting logical contract

The modular-method interface is therefore
$$
\begin{aligned}
  &\text{hypothetical Fermat solution at }p\ge7\\
  &\quad\Longrightarrow
  \text{absolutely irreducible hardly-ramified Frey-SP residual datum}\\
  &\quad\Longrightarrow
  \text{later SP lifting and changing-prime package}\\
  &\quad\Longrightarrow
  \text{the downstream contradiction (8.3)--(8.4).}
\end{aligned}
\tag{8.5}
$$
Only the first implication is the theorem of this book. The middle implication is the construction required from the later deformation and compatible-family books. The last implication is the separately proved endgame just stated.

Together with the independent exponent-$5$ theorem and the elementary exponent reductions, this contract preserves every input the Fermat blueprint needs from the Frey-curve stage without absorbing the later modularity machinery into this book.

## 9. Dependency and coverage audit

The narrowed manuscript has fewer themes than the former omnibus version,
so its closure is best checked by provenance and output rather than by the
old chapter list. The first ledger distinguishes direct proof inputs from
transitive foundations and downstream consumers; the second checks every
Frey-stage output required by the blueprint.

### 9.1. Exact direct dependency ledger

The proof uses the following earlier books directly.

| Book | Imported result | Use here |
|---|---|---|
| 43 | integral Weierstrass invariants, minimality, reduction type, and the split-node criterion | Sections 4.1--4.4 |
| 44 | Tate uniformization, the residual inertia formula, the conductor criterion, and the canonical coefficient-prime finite-flat Kummer model | Sections 5.2 and 6.2 |
| 45 | rank-two torsion, the Weil pairing, good-reduction Frobenius, and finite flatness of torsion for good reduction | Sections 5.1 and 6.1 |
| 150 | semistable full-two residual irreducibility for every prime $p\ge7$ | Section 6.3 |
| 162 | the complete exponent-$5$ descent | Sections 2.4--2.5 |

Book 161 supplies cyclotomic foundations to Book 162, but no theorem from it is invoked directly here. Likewise the prerequisites internal to Books 43--45 and 150 remain transitive dependencies, not extra direct imports.

The later deformation books consume the datum of Section 7. The later three-adic endgame consumes the stronger package listed in Section 8.2. They are downstream consumers, not foundations for the arithmetic theorem proved here.

For clarity, the forward interface was checked against the following
consumers.

| Downstream book | Interface checked |
|---|---|
| 173 and 176 | coefficient primes are in the range at least $7$, with finite-flat coefficient-prime and special dyadic conditions |
| 164 | the residual matrices, intrinsic monodromy line, fixed sign, and global hardly-ramified deformation datum are exactly those of Section 7 |
| 181 | the balanced minimal-lift input begins with the same absolutely irreducible signed SP residual datum |
| 188 | only the conditional three-adic package-to-trace contradiction recorded in Section 8.2 is used for orientation |

None of these rows is a backward citation in the proof.

### 9.2. Blueprint coverage

The narrowed topic retains every output required at the Frey stage:

| Required output | Location |
|---|---|
| reduction from arbitrary $n>2$ | Section 2 |
| independent removal of $p=5$ | Sections 2.4--2.5 |
| exact range $p\ge7$ for the Frey spine | Sections 2.5 and 6.3 |
| primitive normalized triple | Section 3 |
| full rational and integral-away-from-two $2$-torsion structure | Section 4.1 |
| raw and dyadically minimal equations and invariants | Sections 4.1 and 4.3 |
| all discriminant exponents and the curve conductor | Sections 4.2--4.4 |
| splitness at every bad prime, including the dyadic sign | Sections 4.2--4.3 |
| residual determinant, oddness, Frobenius polynomials, ramification, and conductor | Section 5 |
| coefficient-prime finite flatness in both reduction cases | Sections 6.1--6.2 |
| irreducibility and absolute irreducibility | Sections 6.3--6.4 |
| exact signed nonzero-monodromy SP matrices and intrinsic line | Section 7.1 |
| global hardly-ramified SP deformation datum | Sections 7.2--7.3 |
| exact boundary with the later modular contradiction | Section 8 |

The former omnibus themes—general modularity, deformation-ring construction, compatible-family construction, changing coefficient prime, finite-flat classification, and the proof of the final trace contradiction—are deliberately absent. Their only appearance is as the typed interface in Section 8.

### 9.3. Conclusion

For its stated topic, the manuscript is closed: every elementary reduction is proved, exponent $5$ is assigned to its independent accepted descent, and the $p\ge7$ branch ends with the exact residual and deformation data required downstream. The existence of later lifting and compatible-family outputs is not a premise of the Frey arithmetic theorem and therefore does not affect the readiness of this narrowed book.
