# Mumford Representations and Exact Genus-Two Jacobian Arithmetic

## Contents

1. [From divisor geometry to exact arithmetic](#1-from-divisor-geometry-to-exact-arithmetic)
   - [Why coordinates on divisor classes are needed](#11-why-coordinates-on-divisor-classes-are-needed)
   - [The pointed odd-degree setting](#12-the-pointed-odd-degree-setting)
   - [The logical route](#13-the-logical-route)
   - [Exactness as a mathematical condition](#14-exactness-as-a-mathematical-condition)
2. [The affine coordinate ring and its divisors](#2-the-affine-coordinate-ring-and-its-divisors)
   - [Removing the point at infinity](#21-removing-the-point-at-infinity)
   - [Prime ideals and conjugation](#22-prime-ideals-and-conjugation)
   - [The interpolation ideal](#23-the-interpolation-ideal)
   - [Multiplicity and tangency](#24-multiplicity-and-tangency)
3. [Mumford pairs](#3-mumford-pairs)
   - [Admissible and semireduced pairs](#31-admissible-and-semireduced-pairs)
   - [From a pair to a divisor](#32-from-a-pair-to-a-divisor)
   - [From a divisor to a pair](#33-from-a-divisor-to-a-pair)
   - [Field of definition](#34-field-of-definition)
4. [Reduced representatives](#4-reduced-representatives)
   - [Reduction as removal of a principal divisor](#41-reduction-as-removal-of-a-principal-divisor)
   - [Termination in genus two](#42-termination-in-genus-two)
   - [Uniqueness of the reduced pair](#43-uniqueness-of-the-reduced-pair)
   - [The identity and the theta curve](#44-the-identity-and-the-theta-curve)
5. [Negation and elementary group tests](#5-negation-and-elementary-group-tests)
   - [Conjugation is inversion](#51-conjugation-is-inversion)
   - [Equality and inverse tests](#52-equality-and-inverse-tests)
   - [Two-torsion](#53-two-torsion)
   - [Small examples](#54-small-examples)
6. [Composition before reduction](#6-composition-before-reduction)
   - [The coprime Chinese-remainder case](#61-the-coprime-chinese-remainder-case)
   - [Why a three-way gcd is necessary](#62-why-a-three-way-gcd-is-necessary)
   - [The full composition formula](#63-the-full-composition-formula)
   - [Proof of the formula](#64-proof-of-the-formula)
7. [Cantor addition in genus two](#7-cantor-addition-in-genus-two)
   - [The complete addition procedure](#71-the-complete-addition-procedure)
   - [Doubling and tangent interpolation](#72-doubling-and-tangent-interpolation)
   - [Exceptional cancellation cases](#73-exceptional-cancellation-cases)
   - [A symbolic worked addition](#74-a-symbolic-worked-addition)
8. [Correctness, associativity, and complexity](#8-correctness-associativity-and-complexity)
   - [Why the formulas define the Jacobian law](#81-why-the-formulas-define-the-jacobian-law)
   - [Normalization choices and independence](#82-normalization-choices-and-independence)
   - [Degree bounds](#83-degree-bounds)
   - [Failure diagnostics](#84-failure-diagnostics)
9. [Exact arithmetic over rational and finite fields](#9-exact-arithmetic-over-rational-and-finite-fields)
   - [Canonical polynomial arithmetic](#91-canonical-polynomial-arithmetic)
   - [Rational coefficients and denominator control](#92-rational-coefficients-and-denominator-control)
   - [Finite fields and extension fields](#93-finite-fields-and-extension-fields)
   - [Batch verification identities](#94-batch-verification-identities)
10. [Finite-field Jacobians](#10-finite-field-jacobians)
   - [Enumerating reduced pairs](#101-enumerating-reduced-pairs)
   - [Counting curves and Jacobians](#102-counting-curves-and-jacobians)
   - [Determining the group structure](#103-determining-the-group-structure)
   - [Frobenius consistency checks](#104-frobenius-consistency-checks)
11. [Torsion tests and certificates](#11-torsion-tests-and-certificates)
   - [Exact order of a represented class](#111-exact-order-of-a-represented-class)
   - [Visible and full rational two-torsion](#112-visible-and-full-rational-two-torsion)
   - [Bounding rational torsion by good reduction](#113-bounding-rational-torsion-by-good-reduction)
   - [Proving a complete torsion statement](#114-proving-a-complete-torsion-statement)
12. [Specialization and reduction homomorphisms](#12-specialization-and-reduction-homomorphisms)
   - [Good integral models](#121-good-integral-models)
   - [When coefficients reduce directly](#122-when-coefficients-reduce-directly)
   - [Collisions and degree loss](#123-collisions-and-degree-loss)
   - [Compatibility with addition](#124-compatibility-with-addition)
13. [Arithmetic certificate design](#13-arithmetic-certificate-design)
   - [Certificates for curves and pairs](#131-certificates-for-curves-and-pairs)
   - [Certificates for additions and scalar multiples](#132-certificates-for-additions-and-scalar-multiples)
   - [Certificates for finite groups and point counts](#133-certificates-for-finite-groups-and-point-counts)
   - [A complete verification protocol](#134-a-complete-verification-protocol)
14. [Other hyperelliptic presentations](#14-other-hyperelliptic-presentations)
   - [Even-degree equations](#141-even-degree-equations)
   - [Characteristic two](#142-characteristic-two)
   - [Coordinate changes](#143-coordinate-changes)
   - [Safe transfer to the odd-degree model](#144-safe-transfer-to-the-odd-degree-model)
15. [The exact genus-two arithmetic package](#15-the-exact-genus-two-arithmetic-package)
   - [Hypothesis and dependency ledger](#151-hypothesis-and-dependency-ledger)
   - [The representation theorem](#152-the-representation-theorem)
   - [The arithmetic theorem](#153-the-arithmetic-theorem)
   - [Conclusion](#154-conclusion)

## 1. From divisor geometry to exact arithmetic

The geometry of a genus-two curve explains why its Jacobian is accessible: every divisor class has a representative of degree at most two, and only the canonical pencil causes nonuniqueness before reduction. Geometry alone, however, does not tell us how to store a class, add two stored classes, or verify a claimed torsion relation. This chapter turns those needs into a precise coordinate problem.

### 1.1 Why coordinates on divisor classes are needed

Let $k$ be a field and let $C/k$ be a smooth proper genus-two curve with Jacobian $J$. A divisor class is an equivalence class under multiplication by rational functions. This definition is ideal for proving functorial facts and poor for arithmetic: infinitely many divisors represent one class, their points may live in field extensions, and cancellation can be hidden inside a principal divisor.

Suppose instead that the curve has a rational Weierstrass point $\infty$. Then $K_C\sim2\infty$, hyperelliptic conjugate pairs satisfy

$$
P+\iota(P)\sim2\infty, \tag{1.1}
$$

and every class has a unique expression

$$
[D-r\infty],\qquad 0\le r\le2, \tag{1.2}
$$

where $D$ is effective of degree $r$, avoids $\infty$, and contains no pair $P+\iota(P)$. The point of Mumford coordinates is to encode the finite divisor $D$ by two polynomials: one records its $x$-coordinates, with multiplicity, and the other interpolates its $y$-coordinates.

This encoding solves three problems at once. Galois-stable divisors are represented over the ground field even when their points are not individually rational. Equality becomes literal equality of normalized polynomial pairs. Most importantly, multiplication of the corresponding ideals converts the Jacobian law into gcd, Bézout, division, and remainder operations in $k[x]$.

### 1.2 The pointed odd-degree setting

The main arithmetic theory has the following standing hypotheses:

$$
\operatorname{char}k\ne2,\qquad
C:y^2=f(x), \tag{1.3}
$$

where $f\in k[x]$ is monic, squarefree, and has degree $5$. The symbol $C$ always means the smooth projective model, not merely the affine equation. It has one rational point $\infty$ above infinity, and

$$
\operatorname{ord}_\infty(x)=-2,\qquad
\operatorname{ord}_\infty(y)=-5,\qquad
K_C\sim2\infty. \tag{1.4}
$$

Here and below, **squarefree** means geometrically squarefree:

$$
\gcd(f,f')=1. \tag{1.4a}
$$

Over an imperfect field this is stronger than merely asking that no square of a nonconstant
polynomial in $k[x]$ divide $f$. The stronger condition is exactly what makes the affine curve
geometrically smooth and is the condition used in every argument below.

The monicity of $f$ is a normalization, not a geometric necessity. A quintic with nonzero leading coefficient can be treated after a harmless rescaling when that coefficient can be made one over the chosen field; otherwise every formula below still works with systematic leading-coefficient factors. We impose monicity so that “make monic” is the only normalization needed during reduction.

Squarefreeness and $2\ne0$ imply affine smoothness: a singular affine point would have $y=0$ and $f=f'=0$. The odd degree gives the single smooth point at infinity. These hypotheses are checked before any Jacobian calculation. Sections 14.1--14.4 explain exactly what must change for a sextic equation, for characteristic two, or under a coordinate transformation.

### 1.3 The logical route

The route from (1.3) to a checkable group calculation has five stages.

First, remove $\infty$. Its affine coordinate ring is a Dedekind domain. Effective divisors away from infinity correspond to integral ideals, and hyperelliptic conjugation exchanges the two primes above a typical $x$-coordinate.

Second, encode a divisor by an ideal

$$
I(u,v)=(u,y-v),\qquad u\mid f-v^2. \tag{1.5}
$$

The divisibility condition is exactly what makes (1.5) an ideal compatible with the equation. Normalizing $u$ to be monic and $v$ to have smaller degree removes polynomial ambiguity.

Third, reduce every semireduced pair to degree at most two. The rational function $y-v$ supplies the required principal divisor. The degree strictly decreases, and genus two makes the reduction particularly short.

Fourth, multiply two ideals. Shared inverse points must be cancelled before multiplying the $u$-polynomials. This is measured by

$$
d=\gcd(u_1,u_2,v_1+v_2). \tag{1.6}
$$

A three-term Bézout identity for $d$ produces one formula valid for disjoint supports, doubling, shared points, Weierstrass points, and complete inverse cancellation.

Finally, use normalized pairs to certify finite-field groups, scalar multiples, torsion, and specialization. Every claimed result will be reducible to polynomial identities and finite lists.

### 1.4 Exactness as a mathematical condition

An exact calculation is one whose conclusion follows from identities in a specified ring. Over $\mathbf Q$, coefficients are reduced fractions. Over $\mathbf F_q$, they are elements of a precisely presented finite field. A zero test is equality in that ring, not comparison with a numerical tolerance.

This distinction is structural. The decision whether a gcd is $1$ or has positive degree changes the divisor being added. A tiny nonzero coefficient cannot safely be rounded to zero: doing so can turn tangent composition into inverse cancellation. Similarly, observing that a large scalar multiple is numerically close to the identity is not evidence of torsion. Torsion means that its unique reduced pair is exactly $(1,0)$.

Exactness also includes hypotheses. A table of reductions is not a certificate until every listed prime is shown to be a prime of good reduction. A pair is not a Jacobian element until monicity, degree, and divisibility have been checked. An asserted finite group structure is not certified by its order alone. The remaining chapters build these checks into the mathematics rather than treating them as clerical afterthoughts.

## 2. The affine coordinate ring and its divisors

The polynomial formulas become transparent only after they are connected to divisors. Removing the distinguished point at infinity turns the curve into a nonsingular affine curve, whose ideals factor uniquely. Composition will then be ideal multiplication followed by return to a canonical representative.

### 2.1 Removing the point at infinity

Put

$$
A=k[x,y]/(y^2-f(x)). \tag{2.1}
$$

This is the coordinate ring of $U=C\setminus\{\infty\}$. Since $C$ is smooth, $A$ is a regular noetherian domain of dimension one. Consequently it is a Dedekind domain: every nonzero ideal factors uniquely into nonzero prime ideals, and every nonzero fractional ideal is invertible.

For a nonzero ideal $I\subset A$, write

$$
\operatorname{div}(I)=\sum_{P\in U(\bar k)}n_P P \tag{2.2}
$$

after scalar extension, where $n_P$ is the valuation of $I$ at the discrete valuation ring $\mathcal O_{C,P}$. Our convention is that $I$ vanishes along this effective divisor. The ideal class of $I(D)$ corresponds to the divisor class $[D-(\deg D)\infty]$; with this convention multiplication adds divisor classes. Fixing this sign now prevents an otherwise common reversal in the composition formula.

The relation with principal ideals is worth stating explicitly. If $h\in A$ is nonzero, then its affine zero divisor has the same degree as its pole order at $\infty$, and

$$
[\operatorname{div}_U(h)-(\deg\operatorname{div}_U(h))\infty]=0. \tag{2.3}
$$

Thus multiplying an ideal by $(h)$ changes its affine effective divisor by a principal divisor and does not change the associated point of $J$.

### 2.2 Prime ideals and conjugation

Let $P=(a,b)$ be a geometric affine point, so $b^2=f(a)$. Its maximal ideal is

$$
\mathfrak p_P=(x-a,y-b). \tag{2.4}
$$

Hyperelliptic conjugation sends $P$ to $\iota(P)=(a,-b)$ and sends $y$ to $-y$. Therefore

$$
\mathfrak p_{\iota(P)}=(x-a,y+b). \tag{2.5}
$$

Their product is

$$
\mathfrak p_P\mathfrak p_{\iota(P)}=(x-a), \tag{2.6}
$$

unless $P$ is Weierstrass, in which case the two primes coincide and $(x-a)=\mathfrak p_P^2$. Divisor-theoretically, (2.6) is the affine form of $P+\iota(P)\sim2\infty$.

Conjugation of an ideal is defined by applying $y\mapsto-y$ to its elements. From (2.6), $I\bar I$ is principal for every invertible ideal $I$. Hence conjugation represents inversion in the ideal class group and therefore in $J$.

### 2.3 The interpolation ideal

Let $u,v\in k[x]$ satisfy

$$
u\ne0,\qquad u\mid f-v^2. \tag{2.7}
$$

Then

$$
I(u,v)=(u,y-v)\subset A \tag{2.8}
$$

is the kernel of the well-defined quotient map

$$
A\longrightarrow k[x]/(u),\qquad x\longmapsto x,\quad y\longmapsto v. \tag{2.8a}
$$

Indeed the relation $y^2=f$ survives in the target exactly because $u\mid f-v^2$. The two
generators in (2.8) would generate an ideal even without this divisibility; what the condition
ensures is that the quotient has the intended length and graph interpretation.

Over an algebraic closure, write

$$
u(x)=\prod_i(x-a_i)^{m_i}. \tag{2.9}
$$

The ideal is supported above the roots $a_i$, on the branch determined by $y\equiv v(x)$ modulo the relevant power of $x-a_i$. If $m_i=1$, it chooses the point $(a_i,v(a_i))$. Higher powers retain infinitesimal information, not merely a repeated entry in a list.

The quotient has a simple form:

$$
A/I(u,v)\simeq k[x]/(u),\qquad y\longmapsto v. \tag{2.10}
$$

It follows that the colength of $I(u,v)$ is $\deg u$ when $u$ is monic. Thus its divisor has degree $\deg u$.

### 2.4 Multiplicity and tangency

Suppose $P=(a,b)$ with $b\ne0$. The local parameter $t=x-a$ is valid because the cover is étale at $P$. Expanding the curve equation gives a unique power series

$$
y=b+\frac{f'(a)}{2b}t+\cdots. \tag{2.11}
$$

The condition

$$
(x-a)^2\mid f-v^2 \tag{2.12}
$$

therefore says not only $v(a)=b$ but also

$$
v'(a)=\frac{f'(a)}{2b}. \tag{2.13}
$$

It encodes the length-two divisor $2P$ by tangent interpolation.

At a Weierstrass point $W=(a,0)$, $x-a$ has order two. The divisor $2W$ is the principal affine zero divisor of $x-a$ and is a hyperelliptic pair in the ramified sense. A semireduced divisor may contain $W$ once but not twice. The pair $(x-a,0)$ is therefore valid; the local smoothness condition below is designed to retain it.

These local observations explain two features of addition that might otherwise look mysterious. Doubling a non-Weierstrass point creates a square factor in $u$ and needs a derivative condition on $v$. Adding inverse points cancels their common $x$-factor instead. The gcd in (1.6) distinguishes the two situations exactly because $2b\ne0$ at a non-Weierstrass point and $b+(-b)=0$ for inverse points.

## 3. Mumford pairs

We now define the normal form. The definition is designed so that its clauses have separate jobs: divisibility places the divisor on the curve, the graph equation chooses one hyperelliptic branch, an auxiliary gcd checks local regularity, and the degree bound chooses the unique representative of a Jacobian class.

### 3.1 Admissible and semireduced pairs

An **admissible Mumford pair** is a pair $(u,v)\in k[x]^2$ such that

1. $u$ is monic and nonzero;
2. $\deg v<\deg u$;
3. $u\mid f-v^2$.

The pair is **semireduced** if in addition it satisfies the local coprimality condition

$$
\gcd(u,u',v)=1. \tag{3.1}
$$

Under our standing hypotheses this condition is automatic for every admissible pair. The point
needs a little care over an imperfect field. Suppose that an irreducible $p$ divides $u,u'$, and
$v$. If $p'\ne0$, then $p\mid u'$ forces $p^2\mid u$; hence $p^2\mid f-v^2$ and $p^2\mid v^2$
force $p^2\mid f$, contrary to (1.4a). If $p'=0$, then $p\mid u$ and $p\mid v$ imply $p\mid f$;
but differentiating a factorization $f=ph$ gives $p\mid f'$, again contrary to (1.4a). Thus
$\gcd(u,u',v)=1$ in all cases. We retain the word semireduced to emphasize the geometric
consequence: the graph $y=v(x)$ chooses only one branch over each $x$-subscheme and therefore
contains no pair $P+\iota(P)$. At a branch point the valid pair $(x-a,0)$ satisfies

$$
\gcd(x-a,1,0)=1. \tag{3.2}
$$

A semireduced pair may have repeated roots in $u$ at non-Weierstrass points; such roots encode multiplicity. It may not contain both a point and its conjugate, including twice a Weierstrass point.

A semireduced pair is **reduced** when

$$
\deg u\le2. \tag{3.3}
$$

The identity pair is $(1,0)$. When $u=1$, the degree condition on $v$ forces $v=0$.

### 3.2 From a pair to a divisor

Let $(u,v)$ be admissible. The quotient (2.10) defines a finite effective subscheme $D(u,v)$ of $U$ of length $r=\deg u$. If the pair is semireduced, this subscheme is an effective divisor containing no conjugate pair. Associate to it the class

$$
\Phi(u,v)=[D(u,v)-r\infty]\in J(k). \tag{3.4}
$$

Why is this class defined over $k$ even if $u$ does not split? Both equations $u=0$ and $y=v$ have coefficients in $k$, so the finite subscheme is Galois stable. Conversely, the roots of $u$ are exactly the $x$-coordinates of the geometric points, counted with scheme-theoretic multiplicity.

For example, if $u=x-a$ and $v=b$, then

$$
\Phi(x-a,b)=[(a,b)-\infty]. \tag{3.5}
$$

If $u=(x-a)(x-c)$ with $a\ne c$, $v$ is the unique polynomial of degree at most one taking the specified $y$-values at the two points. If $u$ is irreducible quadratic, the same pair represents a degree-two closed point rather than two rational points.

### 3.3 From a divisor to a pair

Let $D$ be an effective divisor of degree $r$ on $U$, defined over $k$, containing no conjugate pair. The finite map $x:C\to\mathbf P^1$ pushes $D$ to a length-$r$ divisor on the affine line. Its monic defining polynomial is

$$
u(x)=\prod_P(x-x(P))^{n_P}. \tag{3.6}
$$

Because no conjugate pair occurs, the function $y$ on $D$ belongs to the image of $k[x]/(u)$. There is therefore a unique residue class $v\bmod u$ such that $y=v(x)$ on $D$. Choose its representative with $\deg v<\deg u$. The curve equation on $D$ says $f-v^2=0$ in $k[x]/(u)$, so $u\mid f-v^2$.

This argument includes multiplicities. At a non-Weierstrass point, $x-a$ is a local parameter and Hermite interpolation gives the required jet of $v$. At a Weierstrass point, length two would be the forbidden conjugate pair $2W$, so a semireduced divisor contains it with multiplicity at most one.

We have proved:

**Proposition 3.1 (pair--divisor correspondence).** Semireduced admissible pairs $(u,v)$ are in bijection with effective divisors on $U$ containing no hyperelliptic conjugate pair. Under the bijection, degree is $\deg u$, and the associated ideal is $(u,y-v)$.

### 3.4 Field of definition

The pair--divisor correspondence commutes with every field extension $K/k$. In particular, a geometric semireduced divisor is Galois stable if and only if its normalized pair has coefficients in $k$.

**Proof.** The monic polynomial $u$ is uniquely determined by the pushed-forward divisor, and $v$ is the unique representative of its residue class of degree less than $\deg u$. If the divisor is Galois stable, uniqueness fixes both polynomials under Galois. The converse follows directly from their equations. Scalar extension preserves monicity, divisibility, and the quotient algebra (2.10). $\square$

This is a major advantage over listing geometric points. For instance, over $\mathbf Q$ an irreducible quadratic $u$ and a linear $v$ encode a rational Jacobian point supported on a conjugate quadratic pair. No choice of a square root enters the representation or its subsequent arithmetic.

## 4. Reduced representatives

An arbitrary ideal product can have degree as large as four. Reduction replaces its divisor by the unique divisor of degree at most two in the same class. The formula comes from the zeros of $y-v$, and its proof makes the sign in the new $v$ unavoidable.

### 4.1 Reduction as removal of a principal divisor

Let $(u,v)$ be semireduced of degree $m>2$. Since $u\mid f-v^2$, put

$$
q=\frac{f-v^2}{u}. \tag{4.1}
$$

Let $c$ be the leading coefficient of $q$, define the monic polynomial

$$
u'=c^{-1}q, \tag{4.2}
$$

and let $v'$ be the remainder of $-v$ modulo $u'$. The resulting pair is again admissible and hence semireduced under the squarefreeness hypothesis.

To see why the class is unchanged, factor the principal function $y-v$. At the divisor $D(u,v)$ it vanishes on the chosen branch. Its remaining finite zeros lie where $q=0$ and, because $y=v$, are the conjugates of the points encoded by $(u',-v\bmod u')$. Pole orders at infinity balance the total degree. Consequently

$$
[D(u,v)-m\infty]
=[D(u',v')-(\deg u')\infty]. \tag{4.3}
$$

Equivalently, in ideal language the product of $I(u,v)$ and the conjugate of $I(u',v')$ differs from the principal ideal $(y-v)$ by a scalar. Conjugating the complementary divisor accounts for the minus sign in $v'$.

### 4.2 Termination in genus two

Because $\deg v<m$ and $\deg f=5$,

$$
\deg q\le\max(5-m,m-2). \tag{4.4}
$$

For $m=3$ or $4$, the right side is at most $2$. These are precisely the degrees arising from the composition of two reduced genus-two pairs. Thus one reduction step reaches degree at most two.

For a larger semireduced input, (4.4) shows strict decrease whenever $m>2$: if $m\ge5$, then $\deg q\le m-2$. Repetition therefore terminates. Every step preserves the divisor class by (4.3), so the final reduced pair represents the original class.

The leading coefficient normalization in (4.2) has no geometric effect. Multiplying $u'$ by a nonzero scalar does not change its zero divisor or the ideal it generates together with $y-v'$. Monicity makes the output unique.

### 4.3 Uniqueness of the reduced pair

Existence is only half of a normal form. We now prove that two reduced pairs in the same class coincide.

**Lemma 4.1 (reduced-divisor rigidity).** Let $D$ and $E$ be effective divisors on $U$, each of degree at most two and containing no conjugate pair. If

$$
[D-(\deg D)\infty]=[E-(\deg E)\infty], \tag{4.5}
$$

then $D=E$.

**Proof strategy.** A rational function witnessing (4.5) would have very small poles. We use the pole orders $2$ and $5$ of $x$ and $y$ to show that a nonconstant such function either identifies the divisors literally or introduces a full hyperelliptic fiber, which reducedness forbids.

Write $r=\deg D$, $s=\deg E$. Equation (4.5) gives a function $h$ with

$$
\operatorname{div}(h)=D+s\infty-E-r\infty. \tag{4.6}
$$

If $r=s$, then $D\sim E$. For degree zero or one, rigidity of degree-one linear systems gives $D=E$. For degree two, the genus-two degree-two classification says either $D=E$ or both lie in the canonical pencil. The latter would make each a conjugate pair, contrary to reducedness.

It remains to rule out $r\ne s$. Interchanging $D,E$, assume $r>s$. The possibilities are $(r,s)=(1,0),(2,0),(2,1)$. In the first case $D\sim\infty$, and rigidity of effective degree-one divisors forces $D=\infty$, contrary to $D\subset U$. In the second, $D\sim2\infty=K_C$, so $D$ is a canonical fiber, contrary to reducedness. In the third, (4.5) says

$$
D\sim E+\infty. \tag{4.6a}
$$

These are effective divisors of degree two. If the class is noncanonical, degree-two uniqueness forces literal equality, impossible because the right side contains $\infty$ and the left side does not. If it is canonical, then $D$ is a canonical fiber, again forbidden. Hence $r=s$ and $D=E$. $\square$

**Theorem 4.2 (unique reduced Mumford representation).** Every class in $J(k)$ has a unique reduced pair $(u,v)$ over $k$.

**Proof.** The genus-two small-divisor theorem applied over $k$ supplies, for every class $\xi$,
an effective $k$-rational divisor $D$ of degree two with

$$
\xi=[D-2\infty].
$$

If $D$ is canonical, then $D\sim2\infty$ and $\xi=0$, represented by $(1,0)$. Otherwise $D$
cannot contain a conjugate pair, because every degree-two conjugate pair is a canonical fiber.
Proposition 3.1 therefore gives a semireduced pair over $k$, already of degree at most two.
This proves existence over the ground field without first choosing geometric points. Lemma 4.1
gives uniqueness of the divisor, and Proposition 3.1 gives uniqueness of its monic $u$ and its
reduced residue representative $v$. Sections 4.1--4.2 additionally give the terminating
polynomial reduction of any larger semireduced representative. $\square$

The final assertion uses the rational point $\infty$, which identifies every rational point of the Picard scheme with an actual degree-zero line bundle. Without such a point, a Picard-class obstruction can prevent this literal ground-field divisor description.

### 4.4 The identity and the theta curve

Uniqueness immediately turns geometric membership into a degree test:

$$
0_J\longleftrightarrow(1,0), \tag{4.7}
$$

and

$$
j_\infty(C(k))
=\{(1,0)\}\cup
\{(x-a,b):a,b\in k,\ b^2=f(a)\}. \tag{4.8}
$$

Thus a nonzero reduced class lies on the Abel--Jacobi curve exactly when $\deg u=1$. A degree-two pair is a genuine point of the Jacobian outside theta, even if its supporting divisor splits into two rational curve points.

Formula (4.8) is the simplest exact membership test used in reduction arguments. It relies on the odd-degree Weierstrass base point. With another base point the embedded theta curve is translated, so degree one alone tests membership in the translate determined by $\infty$, not in every possible Abel image.

## 5. Negation and elementary group tests

Before addition, the involution already gives several exact operations. It supplies inverse classes, equality tests, and a complete description of geometric two-torsion.

### 5.1 Conjugation is inversion

Let $(u,v)$ be reduced. Conjugating its divisor changes every $(a,b)$ to $(a,-b)$, so the conjugate pair is

$$
(u,-v\bmod u). \tag{5.1}
$$

Because $\deg v<\deg u$, this is simply $(u,-v)$ unless $u=1$. From $D+\iota(D)\sim2(\deg D)\infty$ one gets

$$
-[u,v]=[u,-v]. \tag{5.2}
$$

The pair remains admissible because $f-(-v)^2=f-v^2$. It remains reduced because neither $u$ nor its degree changes.

### 5.2 Equality and inverse tests

For reduced pairs, uniqueness gives

$$
[u_1,v_1]=[u_2,v_2]
\Longleftrightarrow u_1=u_2\text{ and }v_1=v_2, \tag{5.3}
$$

and

$$
[u_1,v_1]=-[u_2,v_2]
\Longleftrightarrow u_1=u_2\text{ and }v_1\equiv-v_2\pmod{u_1}. \tag{5.4}
$$

These statements fail for unreduced pairs: distinct semireduced pairs can represent the same class after a reduction step. Therefore every comparison in a certificate must either normalize both sides first or prove separately that both are already reduced.

### 5.3 Two-torsion

A reduced pair represents a two-torsion class exactly when it equals its inverse. Thus

$$
2[u,v]=0
\Longleftrightarrow 2v\equiv0\pmod u. \tag{5.5}
$$

Since $\operatorname{char}k\ne2$ and $\deg v<\deg u$, this is equivalent to $v=0$. Admissibility then becomes

$$
u\mid f. \tag{5.6}
$$

We have proved:

**Proposition 5.1.** The nonzero $k$-rational two-torsion classes are precisely the reduced pairs

$$
[u,0],\qquad u\text{ monic},\quad u\mid f,\quad1\le\deg u\le2. \tag{5.7}
$$

Here a divisor of $f$ of degree three, four, or five gives the same geometric even subset of branch points as its complementary divisor, and reduction selects the representative of degree at most two. The complement relation follows from

$$
\operatorname{div}(y)=\sum_{f(a)=0}(a,0)-5\infty. \tag{5.7a}
$$

Equivalently, the sum of all six Weierstrass points, including $\infty$, is linearly equivalent
to $6\infty=3K_C$. The factor is three, not two; the latter would even have the wrong degree.

Over an algebraic closure, $J[2]$ has $16$ elements. They correspond to even subsets of the six Weierstrass points modulo identifying a subset with its complement. The polynomial formula (5.7) is the ground-field version appropriate to a distinguished branch point at infinity; irreducible factors of $f$ are retained as Galois-stable blocks.

### 5.4 Small examples

Let

$$
C:y^2=(x-a)(x-b)g(x) \tag{5.8}
$$

with $a,b\in k$, $a\ne b$, and $f$ squarefree. Then

$$
T_a=[x-a,0],\qquad T_b=[x-b,0] \tag{5.9}
$$

are nonzero two-torsion classes. Their sum is

$$
T_a+T_b=[(x-a)(x-b),0], \tag{5.10}
$$

already reduced. It is nonzero because its $u$ has degree two. These three classes form a copy of $(\mathbf Z/2\mathbf Z)^2$.

By contrast, if $P=(a,b)$ with $b\ne0$, then $[x-a,b]$ is not two-torsion. Its inverse is $[x-a,-b]$, and their addition must cancel completely. This is the smallest exceptional-gcd case and an important check on the full composition formula.

## 6. Composition before reduction

Adding two reduced classes first produces a semireduced divisor and then reduces it. When the supports are disjoint, interpolation is a Chinese-remainder problem. Shared support forces either tangent conditions or cancellation. The full formula handles both without factoring the input polynomials.

### 6.1 The coprime Chinese-remainder case

Suppose $\gcd(u_1,u_2)=1$. Choose $a,b\in k[x]$ with

$$
a u_1+b u_2=1. \tag{6.1}
$$

Set

$$
u=u_1u_2,\qquad
v\equiv b u_2v_1+a u_1v_2\pmod u,\quad\deg v<\deg u. \tag{6.2}
$$

Then $v\equiv v_i\pmod{u_i}$, so $u_i\mid f-v^2$ for each $i$. Coprimality gives $u\mid f-v^2$. The divisor $D(u,v)$ is the union of the two input divisors, and

$$
\Phi(u,v)=\Phi(u_1,v_1)+\Phi(u_2,v_2). \tag{6.3}
$$

If $\deg u\le2$, this is already reduced. Otherwise Section 4.1 reduces it.

Formula (6.2) cannot handle doubling, because then $u_1=u_2$. Nor can one first divide by $\gcd(u_1,u_2)$ indiscriminately: a shared point on the same branch should acquire multiplicity, while a shared $x$-coordinate on opposite branches should cancel.

### 6.2 Why a three-way gcd is necessary

At a common root $a$ of $u_1$ and $u_2$, the two divisors choose values $v_1(a)$ and $v_2(a)$. If

$$
v_1(a)+v_2(a)=0, \tag{6.4}
$$

the chosen points are hyperelliptic conjugates and their common $x-a$ factor should cancel. If instead $v_1(a)=v_2(a)\ne0$, the same point occurs twice and should be retained with tangent multiplicity. Because $2v_1(a)\ne0$, the factor $x-a$ does not divide $v_1+v_2$ in the second case.

This proves that the cancellation polynomial must be

$$
d=\gcd(u_1,u_2,v_1+v_2), \tag{6.5}
$$

normalized to be monic. Multiplicity in this gcd also matters. It cancels the largest common inverse subscheme, not merely the set of common $x$-coordinates.

Three instructive extremes are:

$$
\begin{array}{c|c|c}
\text{inputs}&d&\text{effect}\\ \hline
\gcd(u_1,u_2)=1&1&\text{ordinary interpolation}\\
(u,v),(u,v),\ \gcd(u,2v)=1&1&\text{tangent doubling}\\
(u,v),(u,-v)&u&\text{complete cancellation}.
\end{array} \tag{6.6}
$$

At a Weierstrass point $v=0$, doubling falls in the last row, as it must because that point represents two-torsion.

### 6.3 The full composition formula

Let $(u_1,v_1)$ and $(u_2,v_2)$ be semireduced admissible pairs. Compute the monic gcd $d$ in (6.5) and polynomials $e_1,e_2,e_3\in k[x]$ satisfying

$$
e_1u_1+e_2u_2+e_3(v_1+v_2)=d. \tag{6.7}
$$

Define

$$
u=\frac{u_1u_2}{d^2} \tag{6.8}
$$

and

$$
w=
\frac{
e_1u_1v_2+e_2u_2v_1+e_3(v_1v_2+f)
}{d}. \tag{6.9}
$$

The numerator is divisible by $d$. Let $v$ be the remainder of $w$ modulo $u$. Then $(u,v)$ is a semireduced composition pair for the sum; apply the reduction of Chapter 4.

The expression (6.9) is symmetric in the two inputs after exchanging $e_1$ and $e_2$. Different Bézout triples may give different $w$, but they give the same residue class modulo $u$ and therefore the same admissible pair after normalization.

### 6.4 Proof of the formula

**Theorem 6.1 (general composition).** The pair defined by (6.7)--(6.9) satisfies

$$
u\mid f-v^2 \tag{6.10}
$$

and represents

$$
\Phi(u,v)=\Phi(u_1,v_1)+\Phi(u_2,v_2). \tag{6.11}
$$

**Proof strategy.** Localize at every irreducible factor of $u_1u_2$. The gcd $d$ removes precisely the common inverse part. Away from that part, (6.9) gives the required interpolation on each input subscheme, including Hermite interpolation where the same branch is repeated.

First observe from (6.7) that $d$ divides $u_1$, $u_2$, and $v_1+v_2$. Since $u_i\mid f-v_i^2$, modulo $d$ one has

$$
v_1v_2+f\equiv-v_1^2+f\equiv0. \tag{6.12}
$$

Thus (6.9) is a polynomial.

Put $u_i=d\tilde u_i$ and $v_1+v_2=d\tilde s$. Dividing (6.7) by $d$ gives

$$
e_1\tilde u_1+e_2\tilde u_2+e_3\tilde s=1. \tag{6.13}
$$

Modulo $\tilde u_1$, use $f\equiv v_1^2$ to rewrite the numerator of (6.9) as

$$
e_2d\tilde u_2v_1+e_3v_1(v_1+v_2)
=d v_1(e_2\tilde u_2+e_3\tilde s)
\equiv d v_1. \tag{6.14}
$$

Hence $w\equiv v_1\pmod{\tilde u_1}$. Similarly

$$
w\equiv v_2\pmod{\tilde u_2}. \tag{6.15}
$$

These two congruences alone would prove divisibility only by the least common multiple of
$\tilde u_1$ and $\tilde u_2$. The extra multiplicity when they share a factor is the decisive
part of the formula, so we verify it by an exact polynomial identity. Put

$$
h_i=\frac{f-v_i^2}{u_i},\qquad
A=e_1(v_2-v_1)+e_3h_1. \tag{6.15a}
$$

The numerator identity defining $w$ can be regrouped as

$$
dw=dv_1+u_1A. \tag{6.15b}
$$

Consequently

$$
d^2(f-w^2)
=u_1R,
\qquad
R=d^2h_1-2dv_1A-u_1A^2. \tag{6.15c}
$$

It remains to show $u_2\mid R$. Work modulo $u_2$, put $s=v_1+v_2$ and
$\delta=v_2-v_1$, and use $d\equiv e_1u_1+e_3s$. Expanding and grouping the
$e_1^2$, $e_1e_3$, and $e_3^2$ terms gives

$$
R\equiv
(e_1^2u_1+2e_1e_3v_1-e_3^2h_1)
\bigl(u_1h_1-s\delta\bigr)
\pmod{u_2}. \tag{6.15d}
$$

But $s\delta=v_2^2-v_1^2$ and

$$
u_1h_1-(v_2^2-v_1^2)=f-v_2^2=u_2h_2. \tag{6.15e}
$$

Thus $u_2\mid R$. Since $u_1u_2=d^2u$, equation (6.15c) now permits
cancellation of the nonzero polynomial $d^2$ and proves

$$
u=\frac{u_1u_2}{d^2}
\mid f-w^2. \tag{6.16}
$$

Replacing $w$ by its remainder modulo $u$ preserves this divisibility, proving (6.10).

Identity (6.15d) is the algebraic content of tangent and higher-jet interpolation. It does not
factor the inputs and remains valid for repeated irreducible factors and inseparable residue
extensions.

For the class statement, factor the input ideals locally in the Dedekind domain $A$. At a prime corresponding to a point $P$, multiplication adds valuations. If the second divisor contains $\iota(P)$, the factor $d$ records the common power and (2.6) turns the product into a principal power of $x-x(P)$; division by $d^2$ removes its two $x$-factors. If both divisors contain $P$, then $v_1+v_2$ is a unit at $P$ unless $P$ is ramified, so $d$ does not cancel it and the valuation is added. Equations (6.14)--(6.15) show that $I(u,v)$ has exactly the remaining local valuations. Therefore

$$
I(u_1,v_1)I(u_2,v_2)
=(d)I(u,v). \tag{6.17}
$$

The equality follows because the two invertible ideals have the same valuation at every
height-one prime. The ideal $(d)$ is principal, so the two sides have the same ideal class. Under
the sign convention of Section 2.1 this is precisely (6.11). $\square$

Squarefreeness in the sense of (1.4a) ensures that the affine coordinate ring remains Dedekind
and that ramified points are nonsingular.

## 7. Cantor addition in genus two

Composition and reduction now assemble into one deterministic group operation. This chapter states it as mathematics, then examines the cases most likely to expose a sign or gcd error.

### 7.1 The complete addition procedure

Given reduced pairs $[u_1,v_1]$ and $[u_2,v_2]$:

1. compute the monic $d=\gcd(u_1,u_2,v_1+v_2)$ and a Bézout triple satisfying (6.7);
2. form $u=u_1u_2/d^2$ and $w$ from (6.9);
3. replace $w$ by $v=w\bmod u$ with $\deg v<\deg u$;
4. verify $u\mid f-v^2$ and $\gcd(u,u',v)=1$;
5. while $\deg u>2$, form $q=(f-v^2)/u$, replace $u$ by the monic associate of $q$, and replace $v$ by $-v\bmod u$;
6. normalize and return the resulting reduced pair.

Every division in these instructions is exact. Every gcd is monic. The output does not depend on any choice made in the extended gcd, by uniqueness of reduced representatives.

**Theorem 7.1 (Cantor addition).** Under the standing hypotheses, the procedure terminates and returns the unique reduced pair representing

$$
[u_1,v_1]+[u_2,v_2]\in J(k). \tag{7.1}
$$

**Proof.** Theorem 6.1 proves composition. Section 4.1 proves that each reduction preserves the class, and Section 4.2 proves termination. Theorem 4.2 identifies the final pair as the unique reduced representative of the sum. $\square$

### 7.2 Doubling and tangent interpolation

Take $(u_1,v_1)=(u_2,v_2)=(u,v)$. Then

$$
d=\gcd(u,2v). \tag{7.2}
$$

For a semireduced divisor with no Weierstrass support, $\gcd(u,v)=1$, and $2$ is a unit, so $d=1$. Composition produces $u^2$. The new polynomial $w$ satisfies

$$
w\equiv v\pmod u,\qquad w^2\equiv f\pmod{u^2}. \tag{7.3}
$$

The second congruence is the tangent lift of the first. If $u=x-a$ and $v=b\ne0$, it gives

$$
w=b+\frac{f'(a)}{2b}(x-a)\pmod{(x-a)^2}, \tag{7.4}
$$

exactly as in (2.13). A rule that merely interpolates the value $b$ and ignores the derivative does not compute doubling.

If the divisor is the Weierstrass pair $[x-a,0]$, then (7.2) gives $d=x-a$. Hence $u_1u_2/d^2=1$, so doubling returns the identity, as required for two-torsion. If a degree-two divisor contains one Weierstrass point and one other point, only the Weierstrass factor cancels during doubling; the other point is doubled with its tangent jet.

### 7.3 Exceptional cancellation cases

The full gcd formula should be tested against the following cases.

**Complete inverses.** For $(u_2,v_2)=(u_1,-v_1)$, one has $d=u_1=u_2$. Formula (6.8) gives $u=1$, and the reduced output is $(1,0)$.

**Partial inverse support.** Suppose

$$
u_1=(x-a)r_1,\qquad u_2=(x-a)r_2,\qquad
v_1(a)=-v_2(a), \tag{7.5}
$$

with the remaining factors coprime. Then $x-a$ divides $d$, so the conjugate pair is removed and the composed degree is

$$
\deg u_1+\deg u_2-2. \tag{7.6}
$$

The remaining points add normally.

**Shared same branch.** If $v_1(a)=v_2(a)\ne0$, then $x-a$ does not divide $v_1+v_2$. It is not in $d$, and the composed $u$ contains $(x-a)^2$. The Bézout term involving $v_1+v_2$ produces the tangent jet.

**Shared Weierstrass point.** Here same branch and inverse branch coincide. Since $v_1(a)=v_2(a)=0$, the factor lies in $d$ and cancels. This is exactly the ramified identity $2W\sim2\infty$.

These are not rare nuisances. Scalar multiplication repeatedly creates shared support, and two-torsion is supported entirely at ramification points. A composition rule proved only under pairwise coprimality is not a group law on all of $J(k)$.

### 7.4 A symbolic worked addition

Let $P=(a,b)$ and $Q=(c,d)$ be affine points with $a\ne c$. Their pairs are

$$
[x-a,b],\qquad[x-c,d]. \tag{7.7}
$$

The coprime formula gives

$$
u=(x-a)(x-c) \tag{7.8}
$$

and the line

$$
v(x)=b+\frac{d-b}{c-a}(x-a). \tag{7.9}
$$

Because $v(a)^2=f(a)$ and $v(c)^2=f(c)$, $u\mid f-v^2$. The degree is two, so the pair is already reduced unless it contains a conjugate pair, which cannot occur when $a\ne c$. Thus

$$
[P-\infty]+[Q-\infty]=[(x-a)(x-c),v]. \tag{7.10}
$$

If $Q=P$, replace (7.9) by the tangent line (7.4); the composed $u=(x-a)^2$ is again degree two. If $Q=\iota(P)$, the denominator $c-a$ signals that the disjoint formula is inapplicable. The full gcd formula instead gives the identity. This one family displays interpolation, tangency, and cancellation as three branches of a single ideal product.

Here is the same calculation with coefficients that can be checked directly. Consider

$$
C:y^2=x^5-x+1. \tag{7.11}
$$

This quintic is squarefree over $\mathbf Q$: a common root of $f$ and $f'=5x^4-1$ would satisfy $x^5=x/5$, and substitution in $f=0$ would give $x=5/4$, which does not satisfy $5x^4=1$. The points

$$
P=(0,1),\qquad Q=(1,1) \tag{7.12}
$$

have pairs $[x,1]$ and $[x-1,1]$. Their sum has

$$
u=x(x-1),\qquad v=1, \tag{7.13}
$$

and the certificate is

$$
f-v^2=x^5-x=x(x-1)(x^3+x^2+x+1). \tag{7.14}
$$

For doubling $P$, the cancellation gcd is $1$ and one may take $e_3=1/2$ in (6.7). Formula (6.9) gives

$$
w=\frac{1+f}{2}\equiv1-\frac{x}{2}\pmod{x^2}. \tag{7.15}
$$

Thus

$$
2[P-\infty]=[x^2,1-x/2], \tag{7.16}
$$

certified by

$$
f-(1-x/2)^2=x^5-\frac{x^2}{4}
=x^2\left(x^3-\frac14\right). \tag{7.17}
$$

Finally, adding $[x,1]$ to $[x,-1]$ gives $d=x$ and $u=x^2/d^2=1$. These three exact lines test disjoint interpolation, the tangent derivative, and complete inverse cancellation on one smooth curve.

## 8. Correctness, associativity, and complexity

A collection of polynomial formulas is not automatically a group law. Its correctness comes from the divisor-class interpretation, and its determinism comes from reduced uniqueness. This chapter makes those two sources of structure explicit and records the degree estimates that keep genus-two arithmetic finite.

### 8.1 Why the formulas define the Jacobian law

Let $\mathcal R(k)$ be the set of reduced pairs. The representation theorem gives a bijection

$$
\Phi:\mathcal R(k)\xrightarrow{\sim}J(k). \tag{8.1}
$$

Cantor addition was proved to satisfy

$$
\Phi(A\boxplus B)=\Phi(A)+\Phi(B). \tag{8.2}
$$

Consequently all group axioms on pairs follow from those on $J(k)$. In particular,

$$
(A\boxplus B)\boxplus C=A\boxplus(B\boxplus C), \tag{8.3}
$$

even though intermediate composition pairs on the two sides can look completely different. The identity is $(1,0)$ and inversion is (5.2).

This is also a proof without circularity. Ideal multiplication first proves that composition adds divisor classes. Principal-divisor reduction proves that reduction preserves them. Associativity is then inherited from multiplication of ideals, or equivalently from addition in $\operatorname{Pic}^0(C)$. No experimental comparison of several triples is used to establish the law.

### 8.2 Normalization choices and independence

Extended gcd expressions are not unique. If $(e_1,e_2,e_3)$ and
$(e'_1,e'_2,e'_3)$ both satisfy (6.7), either choice gives, by Theorem 6.1, the ideal obtained
from $I(u_1,v_1)I(u_2,v_2)$ after removing the same principal factor $(d)$. The resulting ideal
has the fixed monic first polynomial $u=u_1u_2/d^2$. The pair--ideal correspondence then makes
its second polynomial unique modulo $u$. Thus the two values of $w$ differ by a multiple of $u$,
and their reduced remainders are identical. This argument includes the shared-factor case, where
the two elementary congruences (6.14)--(6.15) by themselves would not suffice.

Likewise, the quotient $q=(f-v^2)/u$ may have any nonzero leading coefficient. Dividing by that coefficient changes neither its roots nor the complementary divisor. Reducing $-v$ modulo the monic associate makes the next pair canonical.

One can therefore vary the route of a calculation without varying its result. This gives useful independent checks: compute a scalar multiple by left-to-right addition and by binary doubling, normalize every intermediate result, and compare the final pairs. Equality follows mathematically from associativity, while a discrepancy exposes an arithmetic error.

### 8.3 Degree bounds

For reduced genus-two inputs,

$$
\deg u_i\le2. \tag{8.4}
$$

Composition has degree

$$
\deg u=\deg u_1+\deg u_2-2\deg d\le4. \tag{8.5}
$$

If this degree is three or four, one reduction step produces degree at most two by (4.4). Thus every group addition requires one extended gcd of polynomials of degree at most two, a bounded number of multiplications of degree at most five, and at most one genuine genus-two reduction step.

These are algebraic bounds, independent of the size of $k$. Over a finite field they make exhaustive group enumeration feasible for modest $q$. Over $\mathbf Q$ the polynomial degrees remain bounded but coefficient heights can grow. Frequent reduction controls degree, not numerator and denominator size; exact fraction normalization remains necessary.

For scalar multiplication, the binary method expresses $n$ using $O(\log |n|)$ doublings and additions. Negative scalars are handled by (5.2). An addition chain supplied as a certificate is checked one line at a time.

### 8.4 Failure diagnostics

Every valid intermediate pair satisfies a short list of invariants:

$$
u\text{ monic},\qquad
\deg v<\deg u,\qquad
u\mid f-v^2. \tag{8.6}
$$

After final reduction, also $\deg u\le2$ and $\gcd(u,u',v)=1$. Failure of divisibility usually signals a wrong sign in (6.9), an incorrectly scaled gcd, or a remainder taken in the wrong modulus. A correct divisibility test coupled with an incorrect group result often signals that $d$ was replaced by $\gcd(u_1,u_2)$ and same-branch multiplicity was wrongly cancelled.

There are two valuable universal test identities:

$$
A\boxplus(-A)=(1,0), \tag{8.7}
$$

and, for every Weierstrass factor $x-a$ of $f$,

$$
2[x-a,0]=(1,0). \tag{8.8}
$$

They test the exceptional gcd. Doubling a generic degree-one point tests tangent interpolation. Adding two disjoint degree-one points tests the Chinese-remainder path. A trustworthy arithmetic table includes all three kinds of test.

## 9. Exact arithmetic over rational and finite fields

The group law is field-independent, but exact representation of coefficients differs across fields. This chapter specifies canonical arithmetic conventions and explains how to make large calculations reproducible through identities rather than decimal output.

### 9.1 Canonical polynomial arithmetic

Over any field, polynomial division uses the unique quotient and remainder with remainder degree smaller than the divisor. Every nonzero gcd is scaled to be monic. Every $v$ is replaced by its remainder modulo its current $u$. These conventions make equal mathematical objects literally equal as coefficient lists.

For three polynomials, one may compute (6.7) in two stages. First find

$$
a_1u_1+a_2u_2=g,\qquad g=\gcd(u_1,u_2), \tag{9.1}
$$

then find

$$
b_1g+b_2(v_1+v_2)=d. \tag{9.2}
$$

The Bézout triple is

$$
e_1=b_1a_1,\qquad e_2=b_1a_2,\qquad e_3=b_2. \tag{9.3}
$$

Scaling $d$ to monic requires scaling all three $e_i$ by the same unit. Forgetting that simultaneous scaling makes (6.7) false and usually makes the numerator of (6.9) fail divisibility by $d$.

Polynomial factorization is not needed for addition. It is useful for interpreting support, enumerating two-torsion, and constructing extension fields, but the gcd and quotient identities operate entirely over the ground field.

### 9.2 Rational coefficients and denominator control

Over $\mathbf Q$, write every coefficient as a fraction with coprime numerator and positive denominator. Polynomial content can be cleared temporarily: if $U,V\in\mathbf Z[x]$ represent rational polynomials, primitive-part gcd algorithms avoid unnecessary fraction growth. The mathematical gcd over $\mathbf Q[x]$ is the monic normalization of the primitive gcd over $\mathbf Z[x]$.

A rational reduced pair has monic $u$, so its coefficients have an intrinsic denominator. Clearing denominators in the displayed pair does not mean replacing $u$ by a nonmonic integral polynomial without recording its leading coefficient: monicity is part of the equality convention. A safe record stores rational coefficients or stores an integral primitive polynomial together with the scalar needed to recover its monic form.

Before reducing modulo a prime $p$, every coefficient denominator used in the chosen affine chart must be a $p$-adic unit. If not, the rational divisor class may still have good specialization by properness, but coefficientwise reduction in that chart is invalid. Section 12.3 explains how points approaching infinity cause precisely this phenomenon.

Exact rational verification needs no bound on numerical roundoff. It needs proofs that asserted denominators are nonzero, that each exact division has zero remainder, and that the final polynomials satisfy (8.6).

### 9.3 Finite fields and extension fields

For $k=\mathbf F_p$, coefficients are residues modulo $p$. For

$$
k=\mathbf F_{p^n}=\mathbf F_p[T]/(m(T)), \tag{9.4}
$$

the polynomial $m$ must be displayed and proved irreducible. Elements are uniquely represented by polynomials in $T$ of degree less than $n$. Inversion is certified by a Bézout identity with $m$.

The condition $\operatorname{char}k\ne2$ becomes $p\ne2$. Squarefreeness of the reduced curve is checked by

$$
\gcd(f,f')=1\quad\text{in }k[x]. \tag{9.5}
$$

This is equivalent to nonvanishing discriminant for a monic polynomial. It must be checked in the actual residue field, not inferred from generic smoothness when reducing a rational model.

To count $C(\mathbf F_{q^2})$, one may use a fixed irreducible quadratic presentation and enumerate its $q^2$ elements. The result must be independent of the chosen presentation. Alternatively, quadratic-character sums give

$$
\#C(\mathbf F_{q^n})
=1+q^n+\sum_{a\in\mathbf F_{q^n}}\chi_n(f(a)), \tag{9.6}
$$

where $\chi_n(0)=0$. The leading $1$ is the unique point at infinity.

### 9.4 Batch verification identities

A long calculation can be compressed without becoming opaque. For every composition line record

$$
d,\quad(e_1,e_2,e_3),\quad u,\quad w,\quad v, \tag{9.7}
$$

and verify (6.7), (6.8), (6.9), and $u\mid f-v^2$. For every reduction line record

$$
q=\frac{f-v^2}{u},\quad \operatorname{lc}(q),\quad
u'=q/\operatorname{lc}(q),\quad v'\equiv-v\pmod{u'}. \tag{9.8}
$$

These identities are shorter and stronger than expanding every geometric point over a splitting field.

For a table of many group elements, a deterministic recurrence suffices. State $P_0=(1,0)$ and

$$
P_{i+1}=P_i\boxplus P, \tag{9.9}
$$

give every reduced $P_i$, and verify each adjacent addition. The first repeated pair proves periodicity. Because reduced pairs are unique, no hidden equivalence test remains.

## 10. Finite-field Jacobians

Over a finite field, reduced pairs turn the abstract finite group $J(k)$ into a finite set with a fully explicit operation. Point counts provide its order; enumeration and relation certificates determine its structure.

### 10.1 Enumerating reduced pairs

Let $k=\mathbf F_q$ with $q$ odd, and let $f$ be a monic squarefree quintic. Every element of $J(k)$ occurs exactly once in one of three forms:

$$
(1,0),\qquad
(x-a,b),\qquad
(x^2+s x+t,\,rx+w), \tag{10.1}
$$

subject to monicity, $u\mid f-v^2$, and $\gcd(u,u',v)=1$. Thus exhaustive enumeration is finite. In the squarefree setting the last check follows from divisibility, but retaining it detects malformed inputs.

For degree one, the pairs are exactly the affine $k$-points of $C$. For degree two, loop through monic quadratics $u$ and linear residues $v$, retaining exactly those for which the remainder of $f-v^2$ on division by $u$ is zero and the pair is semireduced. The number of retained pairs plus the degree-zero and degree-one pairs must equal $\#J(k)$.

This enumeration automatically includes split divisors, doubled non-Weierstrass points, and irreducible quadratic divisors. Enumerating only unordered pairs of $C(k)$ misses the last kind and therefore generally misses Jacobian points.

An alternative enumerates $C^{(2)}(k)$ and collapses the $q+1$ canonical divisors to the identity. It is geometrically illuminating but less direct than enumerating reduced pairs, which already performs the collapse.

### 10.2 Counting curves and Jacobians

Put

$$
N_1=\#C(\mathbf F_q),\qquad
N_2=\#C(\mathbf F_{q^2}). \tag{10.2}
$$

The genus-two Frobenius polynomial is

$$
P(T)=1-a_1T+a_2T^2-qa_1T^3+q^2T^4, \tag{10.3}
$$

where

$$
a_1=q+1-N_1,\qquad
a_2=\frac{N_2-q^2-1+a_1^2}{2}. \tag{10.4}
$$

The numerator is even; this follows from the power-sum identity and also serves as a parity check on the counts. The Jacobian order is

$$
\#J(\mathbf F_q)=P(1)
=\frac{N_1^2+N_2}{2}-q. \tag{10.5}
$$

The finite-field weight theorem for smooth proper curves supplies

$$
|N_n-(q^n+1)|\le4q^{n/2} \tag{10.6}
$$

and the reciprocal symmetry in (10.3). These imported facts apply because squarefreeness and the odd-degree chart establish a smooth proper geometrically connected genus-two curve. Formula (10.5), proved from its Frobenius polynomial or from the symmetric-square blowup, then gives an independent check on reduced-pair enumeration.

Order is not structure. Groups such as $\mathbf Z/8\mathbf Z\times\mathbf Z/2\mathbf Z$ and $(\mathbf Z/4\mathbf Z)^2$ have the same order and different scalar behavior. Cantor arithmetic is what distinguishes them.

The curve (7.11) gives a compact numerical example at $q=3$. For every $a\in\mathbf F_3$, one has $a^5-a+1=1$, so each affine fiber has two points and

$$
N_1=7. \tag{10.6a}
$$

Present $\mathbf F_9$ as $\mathbf F_3[t]/(t^2+1)$; the quadratic is irreducible because $2=-1$ is not a square in $\mathbf F_3$. Evaluating at the nine elements gives seven nonzero squares, two nonsquares, and no zero values of $f$. Hence the character sum is $7-2=5$ and

$$
N_2=1+9+5=15. \tag{10.6b}
$$

Equations (10.4)--(10.5) yield

$$
a_1=-3,\qquad a_2=7,\qquad
\#J(\mathbf F_3)=\frac{7^2+15}{2}-3=29. \tag{10.6c}
$$

The reduction is squarefree: a common root would satisfy $x^4=-1$ from $f'=2(x^4+1)$ and then $f=x+1=0$, but $(-1)^4=1\ne-1$ in $\mathbf F_3$. Thus the good-reduction hypothesis is present. Since $29$ is prime, every nonidentity reduced pair generates this finite Jacobian. In particular the reduction of $[x,1]$ has exact order $29$. This conclusion uses both unique representation, which proves the pair is nonidentity, and the independently counted group order.

### 10.3 Determining the group structure

Let $G=J(\mathbf F_q)$ and let $N=\#G$. The classification of finite abelian groups says

$$
G\simeq\mathbf Z/n_1\mathbf Z\times\cdots\times
\mathbf Z/n_r\mathbf Z,\qquad
n_1\mid\cdots\mid n_r. \tag{10.7}
$$

For a genus-two Jacobian, at most four generators are needed because $G/\ell G$ injects into $J[\ell]$ for $\ell\ne\operatorname{char}k$, whose geometric rank is four; the characteristic-primary part also has generator rank at most two times the dimension.

A constructive structure certificate chooses pairs $P_1,\ldots,P_r$, proves their exact orders $n_i$, proves that the homomorphism

$$
\prod_i\mathbf Z/n_i\mathbf Z\longrightarrow G,\qquad
(a_i)\longmapsto\sum_i a_iP_i \tag{10.8}
$$

is injective, and checks $\prod_i n_i=N$. The last equality then proves surjectivity. Injectivity can be certified prime by prime through a relation matrix in Smith normal form, or by exhaustive uniqueness of the $\prod_i n_i$ displayed reduced sums when the group is small.

A mere list of generator orders with product $N$ is insufficient: cyclic subgroups can intersect. One must verify the relation kernel. Conversely, exhaustive enumeration plus a closed addition table proves a group structure without appealing to Frobenius, while (10.5) proves that the enumeration omitted nothing.

### 10.4 Frobenius consistency checks

The coefficients in (10.3) obey the Weil restrictions because its four reciprocal roots have complex absolute value $\sqrt q$. At minimum,

$$
|a_1|\le4\sqrt q, \tag{10.9}
$$

and the roots of the quadratic real Weil factor constrain $a_2$ further. A count violating (10.9) cannot come from the stated smooth curve.

For extension fields,

$$
\#J(\mathbf F_{q^n})=\prod_{i=1}^4(1-\alpha_i^n), \tag{10.10}
$$

where $P(T)=\prod(1-\alpha_iT)$. Newton recurrences compute the power sums and extension-field orders exactly from $a_1,a_2,q$. Direct reduced-pair enumeration over one small extension provides a strong cross-check.

The characteristic polynomial controls orders but still not invariant factors. The action of Frobenius on torsion can impose divisibility restrictions on those factors, yet an actual group-structure claim should be supported by relations among represented pairs.

## 11. Torsion tests and certificates

Torsion is where exact group arithmetic meets global arithmetic. A scalar relation proves that a displayed class has finite order; good reduction bounds all rational torsion. A complete determination needs both directions.

### 11.1 Exact order of a represented class

Let $P=[u,v]\in J(k)$ and let $n>0$. A scalar-multiplication transcript proves $nP=0$ when its final reduced pair is $(1,0)$. To prove that the order is exactly $n$, factor

$$
n=\prod_{\ell}\ell^{e_\ell} \tag{11.1}
$$

and verify

$$
\frac n\ell P\ne0
\quad\text{for every prime }\ell\mid n. \tag{11.2}
$$

Indeed, if the order were a proper divisor of $n$, it would divide $n/\ell$ for some prime divisor $\ell$ of the quotient. Nonzero means that the unique reduced output is not $(1,0)$.

This criterion is stronger and shorter than listing all multiples up to $n$. A binary addition chain proves the required scalars in logarithmically many steps. Each step is certified by Chapter 13.

### 11.2 Visible and full rational two-torsion

Proposition 5.1 makes two-torsion especially transparent. Factor

$$
f=f_1\cdots f_r \tag{11.3}
$$

into distinct monic irreducibles over $k$. A rational two-torsion class is a Galois-stable even subset of the five finite roots together with $\infty$, modulo complement. Equivalently, it is represented after complement and reduction by a divisor $u$ of $f$ of degree at most two.

It is unsafe to infer the dimension from the number $r$ alone without checking degrees. The invariant subsets must have even total cardinality after deciding whether $\infty$ is included, and quotienting by the full six-point set identifies complements. The finite procedure is exact: list the $2^{r+1}$ unions of Galois orbits, retain even unions, quotient by complement, and convert each class to its reduced $[u,0]$.

When $f$ splits completely, the $15$ nonzero classes can be represented by unordered pairs of Weierstrass points. With $\infty$ as one member, a pair $\{a,\infty\}$ gives $[x-a,0]$; a pair of finite roots gives their quadratic product. The count $1+5+10=16$ checks the full geometric $J[2]$.

### 11.3 Bounding rational torsion by good reduction

Let $C/\mathbf Q$ have the integral model (1.3), and let $p$ be an odd prime with $p\nmid\operatorname{disc}(f)$. Then $C$ and $J$ have good reduction at $p$. Reduction

$$
J(\mathbf Q)_{\mathrm{tors}}\longrightarrow J(\mathbf F_p) \tag{11.4}
$$

is injective on torsion of order prime to $p$. This follows from the formal group of the abelian scheme: multiplication by an integer prime to $p$ has invertible linear term on the kernel of reduction.

For a prime $\ell$, choose a good $p\ne\ell$. Then the $\ell$-primary rational torsion injects into $J(\mathbf F_p)$, so

$$
v_\ell(\#J(\mathbf Q)_{\mathrm{tors}})
\le v_\ell(\#J(\mathbf F_p)). \tag{11.5}
$$

Using several good primes gives the prime-by-prime bound

$$
v_\ell\bigl(\#J(\mathbf Q)_{\mathrm{tors}}\bigr)
\le
\min_{\substack{p\in S\\p\ne\ell}}
v_\ell\bigl(\#J(\mathbf F_p)\bigr). \tag{11.6}
$$

The minimum is taken only over residue characteristics different from $\ell$ and must be nonempty.
A compact divisibility by $\gcd_{p\in S}\#J(\mathbf F_p)$ follows from the prime-to-$p$
injectivity proved here only when, for every relevant $\ell$, that gcd's minimum $\ell$-adic
valuation is attained at some $p\ne\ell$. Merely having one such prime in $S$ is not enough:
including the count in residue characteristic $\ell$ can otherwise make the gcd artificially
smaller. Formula (11.6), rather than an unqualified gcd, is the authoritative bound.

Group structure gives sharper bounds than orders. The prime-to-$p$ part of a rational torsion
subgroup injects into the actual finite abelian group $J(\mathbf F_p)$, so incompatible invariant
factors can exclude a candidate even when all its prime-by-prime orders satisfy (11.6).

### 11.4 Proving a complete torsion statement

A complete proof that $J(\mathbf Q)_{\mathrm{tors}}=T$ has two halves.

First, exhibit generators of $T$ as rational reduced pairs, prove their relations and independence, and hence prove $T\subseteq J(\mathbf Q)_{\mathrm{tors}}$. Second, compute certified good-reduction groups and use (11.5), prime by prime, to prove that no larger finite abelian group can contain the displayed subgroup and inject into all selected reductions.

For example, two independent visible Weierstrass classes prove a subgroup $(\mathbf Z/2\mathbf Z)^2$. If good reductions show that every rational torsion order divides $4$, the determination is complete. If the gcd is $8$, one must still exclude a cyclic order-four extension or an additional independent two-torsion class by using the factorization of $f$, group structures at the good primes, or further reductions.

Point counting supplies the orders in this argument; Mumford arithmetic supplies candidate elements and group structures. Neither replaces the other.

## 12. Specialization and reduction homomorphisms

Reducing coefficients of a pair is often the visible form of specialization, but it is not the definition. The definition comes from the proper smooth model of the Jacobian. This distinction is essential when support collides or approaches infinity.

### 12.1 Good integral models

Let $R$ be a discrete valuation ring with fraction field $K$, residue field $k$ of characteristic not two, and suppose

$$
f\in R[x]\text{ is monic of degree five},\qquad
\operatorname{disc}(f)\in R^\times. \tag{12.1}
$$

Then the odd-degree hyperelliptic model is smooth and proper over $R$, including at its section $\infty$. Its relative Jacobian $\mathcal J/R$ is an abelian scheme. Properness gives

$$
J(K)=\mathcal J(R), \tag{12.2}
$$

and reduction gives a group homomorphism

$$
\operatorname{sp}:J(K)\longrightarrow J_k(k). \tag{12.3}
$$

The Abel--Jacobi maps based at $\infty$ commute with this specialization. Thus a rational curve point reduces first on the curve and then has its reduced degree-one pair in the special Jacobian.

The discriminant condition is sufficient for good reduction of this model. A nonunit discriminant of a chosen equation does not prove intrinsic bad reduction, because a coordinate change can remove nonminimal collisions. Conversely, generic squarefreeness alone does not prove good reduction at a particular prime.

### 12.2 When coefficients reduce directly

Let $[u,v]$ be a reduced pair over $K$. Suppose all coefficients lie in $R$, $u$ remains monic of the same degree after reduction, and

$$
\gcd(\bar u,\bar u',\bar v)=1. \tag{12.4}
$$

Reducing the exact identity $u\mid f-v^2$ gives

$$
\bar u\mid\bar f-\bar v^2. \tag{12.5}
$$

The reduced pair $[\bar u,\bar v]$ then represents $\operatorname{sp}[u,v]$. If its degree is at most two, it is already reduced.

Under the squarefreeness hypothesis, every admissible special pair automatically satisfies the semireduced smoothness condition. Thus if integral coefficient reduction appears to violate $\gcd(\bar u,\bar u',\bar v)=1$, at least one premise has failed: the special quintic is not squarefree, the claimed divisibility is false, or the displayed coefficients do not describe a flat divisor of the same degree. The remedy is not to discard a factor informally; it is to specialize the class on the proper model and then compute its unique reduced pair.

### 12.3 Collisions and degree loss

Three phenomena prevent naive coefficient reduction.

First, two distinct generic points can reduce to the same non-Weierstrass point. Their quadratic $u$ acquires a double root, which is legitimate only if the reduced $v$ carries the correct tangent jet. The divisibility condition modulo $u$ checks that jet.

Second, distinct points can acquire inverse support in the special fiber. The degree-two interpolation polynomial then usually develops a nonintegral denominator, so the hypotheses of Section 12.2 fail. On the proper symmetric square the limiting divisor contains a canonical pair, which disappears when its class is reduced; the specialization therefore has smaller reduced degree.

Third, a point can approach $\infty$. Its affine $x$-coordinate has negative valuation, so the monic polynomial $u$ has nonintegral coefficients. The point nonetheless extends to the proper curve and reduces to $\infty$, whose Abel class is zero. There is no meaningful coefficientwise reduction in the affine $x$-chart; one must use the chart at infinity or the proper model.

Thus integrality of a displayed pair is a sufficient coordinate criterion, not a prerequisite for specialization. Properness is the intrinsic source of the map.

### 12.4 Compatibility with addition

Because $\mathcal J$ is a group scheme, specialization is a homomorphism:

$$
\operatorname{sp}(P+Q)=\operatorname{sp}(P)+\operatorname{sp}(Q). \tag{12.6}
$$

When all intermediate coefficients are integral and the same gcd degrees persist, this can be checked by reducing every Cantor identity. When gcd degree jumps after reduction, the generic formula does not reduce term by term to the same composition branch, but the final reduced special pair still satisfies (12.6). The jump records new cancellation in the special fiber, not failure of the homomorphism.

This observation is important in certificates using global generators. One may reduce each generator geometrically, then perform all finite-field additions. There is no need to reduce a rational addition transcript whose denominators happen to be divisible by the residue characteristic.

At semistable bad reduction, the target is not simply the Jacobian of a smooth special curve. Generalized Jacobians, multidegrees, and the component group intervene. The coefficient rules of this chapter are asserted only under (12.1).

## 13. Arithmetic certificate design

An arithmetic certificate is a finite body of data from which every claimed conclusion follows by displayed identities and exhaustive finite checks. Its purpose is not stylistic reproducibility; it separates mathematical proof from trust in an unexplained calculation.

### 13.1 Certificates for curves and pairs

A curve certificate over a field $k$ contains:

1. the field presentation;
2. the monic quintic $f$;
3. a Bézout identity proving $\gcd(f,f')=1$;
4. the declaration that $\operatorname{char}k\ne2$.

These data prove that the smooth projective odd-degree model has genus two and a rational Weierstrass point at infinity.

A pair certificate for $[u,v]$ contains the coefficient lists of $u,v$ and the quotient

$$
h=\frac{f-v^2}{u}. \tag{13.1}
$$

Direct multiplication checks $f-v^2=uh$. Monicity, $\deg v<\deg u\le2$, and a Bézout identity for $\gcd(u,u',v)=1$ prove that the pair is reduced. Therefore it identifies one and only one Jacobian point.

For a rational pair, the field presentation includes reduced fractions. For a finite extension, it includes the irreducible defining polynomial and canonical basis.

### 13.2 Certificates for additions and scalar multiples

An addition certificate from $A_i=[u_i,v_i]$ to $A_3$ records:

1. $d,e_1,e_2,e_3$ satisfying (6.7);
2. the exact quotient $u_1u_2/d^2$;
3. the numerator and exact quotient $w$ in (6.9);
4. the remainder $v=w\bmod u$;
5. every reduction quotient $(f-v^2)/u$;
6. the final monic reduced pair $A_3$.

The identities prove $\Phi(A_3)=\Phi(A_1)+\Phi(A_2)$ by Theorems 6.1 and 7.1. A scalar certificate is a directed acyclic list of such additions beginning with the claimed generators. Binary labels such as $P_{2i}=2P_i$ and $P_{2i+1}=P_{2i}+P$ make the target scalar independently readable.

To certify exact order $n$, append the identity output for $nP$ and nonidentity outputs for $(n/\ell)P$ for every $\ell\mid n$. To certify independence of several finite-order points, provide a Smith-normal-form relation computation or enumerate the bounded coefficient box and show that only the zero vector yields $(1,0)$.

### 13.3 Certificates for finite groups and point counts

A point-count certificate can list, for each $a\in\mathbf F_{q^n}$, the value of $f(a)$ and its quadratic character, then use (9.6). For larger fields it can instead give the frequency distribution of character values together with enough information to verify the field traversal. Counts over $q$ and $q^2$ determine $a_1,a_2$ and $\#J(\mathbf F_q)$ by (10.4)--(10.5).

A reduced-pair enumeration certificate lists all retained pairs grouped by $\deg u$. Each entry has its quotient (13.1), and a count of rejected candidates is partitioned by nonzero remainder or failed semireduction. Agreement with (10.5) proves completeness.

A group-structure certificate displays generators, exact orders, and a relation kernel. The product of invariant factors must equal the independently counted order. If an addition table is used, closure, identity, inverse, and every product are checkable from Cantor certificates; associativity need not be rechecked entrywise because the operation has already been proved to be the Jacobian law.

### 13.4 A complete verification protocol

The following protocol is sufficient for a global torsion-and-reduction calculation.

First verify the rational curve and every claimed rational pair. Next verify rational scalar relations and independence. Then, for each reduction prime, prove good reduction by the discriminant or gcd criterion, count the residue curve over the first two extensions, and derive the Jacobian order. Determine enough of the finite group structure to support the claimed injection or congruence. Reduce each global generator using Section 12.2 or a proper-model argument. Finally compare the lower subgroup with the prime-by-prime upper bounds of Section 11.3.

Every conclusion has a named source:

$$
\begin{array}{c|c}
\text{claim}&\text{certificate}\\ \hline
\text{smooth genus-two curve}&\gcd(f,f')=1\text{ and odd-degree chart}\\
\text{valid Jacobian point}&f-v^2=uh\text{ and reduced conditions}\\
\text{sum or multiple}&\text{Bézout, composition, and reduction identities}\\
\text{finite group order}&N_1,N_2\text{ and (10.5)}\\
\text{finite group structure}&\text{generators, exact relations, full order}\\
\text{specialization}&\text{good model and compatible reduced pairs}\\
\text{complete rational torsion}&\text{exhibited subgroup plus local upper bounds}.
\end{array} \tag{13.2}
$$

No row is implied merely by a plausible decimal approximation, by a group order without elements, or by survival at several primes.

## 14. Other hyperelliptic presentations

The clean odd-degree calculus is powerful precisely because its hypotheses are explicit. This chapter describes the boundaries: a sextic has two points at infinity, characteristic two changes conjugation, and a coordinate change can alter which divisors have integral affine coordinates.

### 14.1 Even-degree equations

Let

$$
C:y^2=f_6(x) \tag{14.1}
$$

with $f_6$ squarefree of degree six and $\operatorname{char}k\ne2$. There are two geometric points at infinity, exchanged by the involution; they are individually rational exactly when the leading coefficient is a square. Their sum is a rational canonical divisor.

The simple class $[D-(\deg D)\infty]$ is unavailable when there is no distinguished rational Weierstrass point. One may use balanced divisors relative to the degree-two divisor at infinity, but degrees and the action of inversion acquire correction terms. Applying the quintic formulas unchanged silently chooses one of the two infinite points and is generally wrong.

If the sextic curve has a rational Weierstrass point at a finite branch root, a projective transformation of the $x$-line can send that branch point to infinity. After the corresponding $y$-scaling, the equation becomes an odd-degree quintic and the entire preceding theory applies. The chosen branch point becomes the base point.

If there is no rational Weierstrass point, exact Jacobian arithmetic still exists using ideals and a rational degree-two base divisor, but the normal form is a balanced representation rather than the specific reduced pairs of Theorem 4.2. This book does not identify those formulas with the odd-degree formulas; it records the hypothesis difference so that certificates cannot cross it unnoticed.

### 14.2 Characteristic two

In characteristic two a separable hyperelliptic equation has the form

$$
y^2+h(x)y=f(x),\qquad h\ne0. \tag{14.2}
$$

The involution is

$$
(x,y)\longmapsto(x,-h(x)-y)=(x,h(x)+y). \tag{14.3}
$$

A Mumford pair must satisfy

$$
u\mid v^2+h v-f, \tag{14.4}
$$

and negation replaces $v$ by $-h-v$ modulo $u$. Accordingly the cancellation gcd uses

$$
\gcd(u_1,u_2,v_1+v_2+h), \tag{14.5}
$$

with $h$ reduced in the common quotient. Derivative and ramification behavior also change.

The formulas (5.2), (5.5), (6.5), and (6.9) were proved using $y^2=f$ and $2\ne0$ and are not asserted in characteristic two. In particular, $2v=0$ cannot characterize two-torsion there. Smoothness must be checked from the partial derivatives of (14.2), including at infinity, rather than from squarefreeness of $f$ alone.

### 14.3 Coordinate changes

A projective change

$$
x=\frac{aX+b}{cX+d},\qquad ad-bc\ne0, \tag{14.6}
$$

is accompanied by $y=Y/(cX+d)^3$ in a sextic presentation. It transports divisors and Jacobian classes functorially, but the Mumford polynomials do not transform by simple coefficient substitution alone. Roots that cross the pole $cX+d=0$ move to infinity, and monic normalization introduces scalar factors.

For an affine change $x=\alpha X+\beta$ with $\alpha\ne0$, transformation is simpler: substitute into $u,v$, divide the transformed $u$ by its leading coefficient, and scale $y$ consistently so that the curve equation remains in its normalized form. The resulting pair must still be reduced and verified by divisibility.

Integrality is coordinate-dependent. A class with integral $u,v$ in one good chart can have denominators in another chart whose pole meets its special support. Specialization itself is coordinate-independent because it belongs to the abelian scheme.

### 14.4 Safe transfer to the odd-degree model

To use the main calculus on a differently presented curve, a complete transfer record contains:

1. an explicit birational map extending to an isomorphism of smooth projective curves;
2. the image of the chosen rational Weierstrass point and the verification that it becomes the unique point at infinity;
3. the transformed monic squarefree quintic;
4. formulas transporting the divisor support, including points crossing infinity;
5. a final Mumford divisibility and reduction check.

Because smooth proper curves are determined by their function fields, a birational map between smooth projective models is an isomorphism. Nevertheless, the base point matters: changing it translates the Abel--Jacobi embedding and therefore changes the coordinate representative of every class. The transfer record must state the base point, not only the affine equation.

## 15. The exact genus-two arithmetic package

We finish by collecting the representation, group law, finite-field, torsion, and specialization results with their exact assumptions. This ledger is the point at which a later descent or sieve can safely import the arithmetic without reopening its foundations.

### 15.1 Hypothesis and dependency ledger

The intrinsic geometric input is the theorem package proved in Book 149: a smooth proper
geometrically connected genus-two curve is hyperelliptic; a rational Weierstrass point $\infty$
satisfies $K_C\sim2\infty$; every degree-zero class has an effective representative of degree
two relative to a rational base point; the noncanonical degree-two representative is unique; the
Abel map is an embedding; and good models specialize points and divisor classes compatibly. In
this book these facts are sharpened to a unique polynomial normal form and an exact group
operation.

The finite-field input is the Weil theorem for smooth proper curves proved in Book 26 and imported
geometrically in Book 149: Frobenius on $H^1$ has four eigenvalues of absolute value $\sqrt q$ in
genus two, the trace formula gives the curve counts, and $\#J(\mathbf F_q)=P(1)$. Its hypotheses
match Sections 1.2 and 9.3: the odd-degree geometrically squarefree equation produces a smooth
proper geometrically connected curve over the finite field. We use the theorem only after that
check.

All other central assertions are proved here from polynomial arithmetic, ideal factorization on a smooth affine curve, and the divisor geometry just recalled. In particular, no unproved descent theorem, Mordell--Weil computation, or rational-point classification is used. A finite-field order is never treated as a group structure, and local survival is never treated as global existence.

The characteristic and model restrictions are:

$$
\begin{array}{c|c}
\text{result}&\text{hypotheses}\\ \hline
\text{odd Mumford pair and Cantor formula}&y^2=f,\ \deg f=5,\ f\text{ monic squarefree},\ 2\ne0\\
\text{unique degree }\le2\text{ normal form}&\text{same, with rational }\infty\\
\text{finite-field count formulas}&\text{smooth proper genus two over }\mathbf F_q\\
\text{coefficientwise specialization}&\text{good model plus integral pair in the chart}\\
\text{intrinsic specialization}&\text{smooth proper model over the valuation ring}\\
\text{prime-to-}p\text{ torsion injection}&\text{good reduction in residue characteristic }p.
\end{array} \tag{15.1}
$$

### 15.2 The representation theorem

**Theorem 15.1 (reduced Mumford representation).** Let $k$ be a field of characteristic different from two and let

$$
C:y^2=f(x)
$$

be the smooth projective curve attached to a monic squarefree quintic. Then every element of $J(k)$ is represented uniquely by a pair

$$
[u,v] \tag{15.2}
$$

such that

$$
u\text{ is monic},\quad
\deg v<\deg u\le2,\quad
u\mid f-v^2,\quad
\gcd(u,u',v)=1. \tag{15.3}
$$

The identity is $[1,0]$, inversion is $[u,v]\mapsto[u,-v]$, and the embedded curve based at infinity consists of the identity and the pairs of degree one. Two-torsion consists exactly of $[u,0]$ with monic $u\mid f$ and $\deg u\le2$ after complement reduction.

**Proof.** Sections 2--4 prove existence and uniqueness. Section 5 proves the stated operations and tests. $\square$

### 15.3 The arithmetic theorem

**Theorem 15.2 (exact genus-two Jacobian arithmetic).** Under the hypotheses of Theorem 15.1:

1. the full three-way-gcd formulas (6.7)--(6.9), followed by reduction (4.1)--(4.2), compute the sum of any two reduced pairs, including doubling, shared support, Weierstrass support, and partial or complete inverse cancellation;
2. every step is certified by polynomial Bézout, divisibility, quotient, and remainder identities;
3. over a finite field, enumeration of reduced pairs is exhaustive, and counts over the first two field extensions give the independent order formula (10.5);
4. exact scalar multiplication proves element orders, while finite abelian relation certificates prove group structure;
5. over $\mathbf Q$, good reductions bound rational torsion prime by prime, and displayed rational pairs plus those upper bounds can certify the complete torsion subgroup;
6. over a discrete valuation ring with good reduction, intrinsic specialization is a homomorphism, agrees with coefficient reduction when the pair is integral and remains semireduced, and otherwise is found by proper specialization followed by reduction.

**Proof.** The first two clauses are Theorems 6.1 and 7.1 together with Chapter 13. The third follows from unique representation and the finite-field Frobenius formulas. The fourth is finite abelian group theory applied to the proved group law. The fifth is the formal-group injectivity of prime-to-residue-characteristic torsion. The last is the abelian-scheme specialization of Chapter 12. $\square$

### 15.4 Conclusion

A genus-two divisor class can now be handled without ambiguity. The monic polynomial $u$ records its finite $x$-divisor, the residue polynomial $v$ selects the branch and its infinitesimal multiplicities, and $u\mid f-v^2$ certifies that the data lie on the curve. Reduction removes the complementary zeros of $y-v$ and terminates at degree at most two. Reduced uniqueness turns equality, inversion, theta membership, and torsion relations into literal polynomial tests.

The group law is equally exact. The gcd $\gcd(u_1,u_2,v_1+v_2)$ measures precisely the inverse support that must disappear. The accompanying three-term Bézout identity interpolates all remaining support, including tangent multiplicity in doubling. One complementary-divisor step returns the genus-two result to reduced form. Exceptional cases are therefore part of the law, not exceptions to its proof.

Over finite fields, reduced pairs enumerate the Jacobian while Frobenius counts its order independently. Over rational fields, the same identities prove scalar relations, and good specialization bounds torsion and transports classes to finite groups. Every substantial arithmetic assertion admits a compact certificate made from curve smoothness, polynomial divisibility, Bézout identities, point counts, and finite relations.

The resulting package is the exact interface needed for descent and sieving. It supplies canonical representatives, a proved total group operation, reliable reduction maps, torsion tests, and finite-field structures. What remains in later arithmetic problems is not ambiguity in Jacobian addition: it is the genuinely global task of finding generators, proving saturation, computing descent images, and exhausting the resulting finite congruence conditions.
