# Tate Curves and Multiplicative Reduction

## Contents

1. [The parameter of a degenerating elliptic curve](#1-the-parameter-of-a-degenerating-elliptic-curve)
   - [From a node to a multiplicative period](#11-from-a-node-to-a-multiplicative-period)
   - [Standing hypotheses and three closures](#12-standing-hypotheses-and-three-closures)
   - [A convergence calculus for $q$-series](#13-a-convergence-calculus-for-q-series)
   - [Products, logarithmic derivatives, and Lambert series](#14-products-logarithmic-derivatives-and-lambert-series)
   - [The theta product and its functional equations](#15-the-theta-product-and-its-functional-equations)
2. [The equation of the Tate curve](#2-the-equation-of-the-tate-curve)
   - [Why the coefficients are Lambert series](#21-why-the-coefficients-are-lambert-series)
   - [The Weierstrass equation](#22-the-weierstrass-equation)
   - [The discriminant product](#23-the-discriminant-product)
   - [The $j$-expansion and its inverse](#24-the-j-expansion-and-its-inverse)
   - [A first numerical expansion](#25-a-first-numerical-expansion)
3. [Multiplicative uniformization](#3-multiplicative-uniformization)
   - [Elliptic functions on a multiplicative annulus](#31-elliptic-functions-on-a-multiplicative-annulus)
   - [The uniformizing map](#32-the-uniformizing-map)
   - [Kernel, surjectivity, and the group law](#33-kernel-surjectivity-and-the-group-law)
   - [Galois equivariance and descent](#34-galois-equivariance-and-descent)
   - [Why algebraic points do not require completion](#35-why-algebraic-points-do-not-require-completion)
   - [Analytic and algebraic uniformization compared](#36-analytic-and-algebraic-uniformization-compared)
4. [Integral geometry and split multiplicative reduction](#4-integral-geometry-and-split-multiplicative-reduction)
   - [The integral equation](#41-the-integral-equation)
   - [Minimality and the exact discriminant exponent](#42-minimality-and-the-exact-discriminant-exponent)
   - [The special fiber and its tangent directions](#43-the-special-fiber-and-its-tangent-directions)
   - [The polygon of components](#44-the-polygon-of-components)
5. [The converse theorem and the canonical parameter](#5-the-converse-theorem-and-the-canonical-parameter)
   - [Why negative $j$-valuation should force a period](#51-why-negative-j-valuation-should-force-a-period)
   - [Analytic inversion of $j$](#52-analytic-inversion-of-j)
   - [Tate's converse uniformization theorem](#53-tates-converse-uniformization-theorem)
   - [Uniqueness and behavior under extension](#54-uniqueness-and-behavior-under-extension)
6. [Nonsplit multiplicative reduction](#6-nonsplit-multiplicative-reduction)
   - [The splitting character](#61-the-splitting-character)
   - [Unramified quadratic twisting](#62-unramified-quadratic-twisting)
   - [The nonsplit converse](#63-the-nonsplit-converse)
   - [Component groups in the nonsplit case](#64-component-groups-in-the-nonsplit-case)
   - [Twisted point descent](#65-twisted-point-descent)
7. [Local points and the reduction filtration](#7-local-points-and-the-reduction-filtration)
   - [A fundamental annulus](#71-a-fundamental-annulus)
   - [$E(K)$, $E_0(K)$, and $E_1(K)$](#72-ek-e_0k-and-e_1k)
   - [Reduction and component exact sequences](#73-reduction-and-component-exact-sequences)
   - [Valuations of coordinates](#74-valuations-of-coordinates)
   - [Rational torsion](#75-rational-torsion)
8. [Finite torsion and the Kummer extension](#8-finite-torsion-and-the-kummer-extension)
   - [The exact sequence for $E_q[n]$](#81-the-exact-sequence-for-e_qn)
   - [Roots of unity and a root of $q$](#82-roots-of-unity-and-a-root-of-q)
   - [The Galois matrix](#83-the-galois-matrix)
   - [Splitting and reducibility](#84-splitting-and-reducibility)
   - [The Weil pairing in multiplicative coordinates](#85-the-weil-pairing-in-multiplicative-coordinates)
   - [What changes in characteristic $p$](#86-what-changes-in-characteristic-p)
9. [Tate modules and cyclotomic determinant](#9-tate-modules-and-cyclotomic-determinant)
   - [Prime-to-residue-characteristic Tate modules](#91-prime-to-residue-characteristic-tate-modules)
   - [The integral matrix and its determinant](#92-the-integral-matrix-and-its-determinant)
   - [Coefficient characteristic equal to residue characteristic](#93-coefficient-characteristic-equal-to-residue-characteristic)
   - [The nonsplit twist](#94-the-nonsplit-twist)
   - [Duality and the determinant](#95-duality-and-the-determinant)
10. [Inertia, monodromy, and conductor](#10-inertia-monodromy-and-conductor)
    - [The tame character from roots of a uniformizer](#101-the-tame-character-from-roots-of-a-uniformizer)
    - [Unipotent inertia](#102-unipotent-inertia)
    - [Conductor consequences](#103-conductor-consequences)
    - [Residual ramification and level lowering](#104-residual-ramification-and-level-lowering)
    - [Frobenius and the local special representation](#105-frobenius-and-the-local-special-representation)
    - [The boundary at the residue characteristic](#106-the-boundary-at-the-residue-characteristic)
11. [Finite-flat boundaries at the coefficient prime](#11-finite-flat-boundaries-at-the-coefficient-prime)
    - [Why generic torsion is not enough](#111-why-generic-torsion-is-not-enough)
    - [The integral Kummer boundary](#112-the-integral-kummer-boundary)
    - [The canonical finite-flat extension](#113-the-canonical-finite-flat-extension)
    - [When the criterion is necessary](#114-when-the-criterion-is-necessary)
    - [The dyadic and equal-characteristic boundaries](#115-the-dyadic-and-equal-characteristic-boundaries)
12. [Worked local fields](#12-worked-local-fields)
    - [A split curve over $\mathbf Q_5$](#121-a-split-curve-over-mathbf-q_5)
    - [Its nonsplit quadratic twist](#122-its-nonsplit-quadratic-twist)
    - [An equal-characteristic split example](#123-an-equal-characteristic-split-example)
    - [An equal-characteristic nonsplit example](#124-an-equal-characteristic-nonsplit-example)
    - [A counterexample about residual splitting](#125-a-counterexample-about-residual-splitting)
    - [A coefficient-prime boundary example](#126-a-coefficient-prime-boundary-example)
13. [The local representation at a multiplicative place](#13-the-local-representation-at-a-multiplicative-place)
    - [A compact structural dictionary](#131-a-compact-structural-dictionary)
    - [Precise formulas for semistable modularity](#132-precise-formulas-for-semistable-modularity)
    - [Exactly what is passed to the next volume](#133-exactly-what-is-passed-to-the-next-volume)
    - [Conclusion](#134-conclusion)

## 1. The parameter of a degenerating elliptic curve

### 1.1 From a node to a multiplicative period

The preceding volume approached multiplicative reduction from an integral equation. A minimal cubic becomes nodal, its smooth special fiber is a one-dimensional torus, and the valuation of its minimal discriminant measures the thickness of the degeneration. That description is geometric and intrinsic, but it leaves a striking question unanswered: can the generic elliptic curve itself be recovered from the multiplicative group suggested by the node?

The Tate curve answers yes. If $K$ is complete and $q\in K$ satisfies $0<|q|<1$, multiplication by $q$ acts discretely on $\overline K^\times$. The quotient

$$
\overline K^\times/q^{\mathbf Z}
$$

is a multiplicative analogue of a complex torus. It is not merely an abstract group. Convergent functions on it produce an elliptic curve $E_q$, and multiplication in the quotient becomes the chord-and-tangent law on $E_q$. The valuation of $q$ becomes the minimal discriminant exponent; the residue of a unit becomes a point on the smooth part of the nodal fiber; and extracting roots of $q$ describes torsion and Galois action.

Thus one small parameter coordinates several theories at once:

$$
q
\quad\rightsquigarrow\quad
\begin{cases}
\text{an analytic period},\\
\text{a minimal discriminant},\\
\text{a cycle of components},\\
\text{a Kummer extension in torsion},\\
\text{a unipotent inertia operator}.
\end{cases}
$$

The point of this book is to prove that these are not analogies but different faces of one construction. The split case comes first because the torus is literally $\mathbf G_m$. Nonsplit multiplicative reduction is then obtained by descent through the unique quadratic character that exchanges the two tangent directions.

### 1.2 Standing hypotheses and three closures

Unless stated otherwise, $K$ is complete for a nontrivial discrete valuation

$$
v:K^\times\longrightarrow\mathbf Z.
$$

We write $R=\mathcal O_K$, $\mathfrak m=(\pi)$, and $k=R/\mathfrak m$. Choose an absolute value compatible with $v$, so $|x|=c^{v(x)}$ for a fixed $0<c<1$. The **residue characteristic exponent** is denoted $p$: it is $\operatorname{char}k$ when that characteristic is positive and $1$ in residue characteristic zero.

Three fields must be kept distinct. Fix a separable closure $K^s$, an algebraic closure $\overline K$, and a completion $C$ of $\overline K$ for the extended absolute value. In positive characteristic $K^s$ may be smaller than $\overline K$ because of purely inseparable elements. The Galois group is

$$
G_K=\operatorname{Gal}(K^s/K).
$$

Analytic identities are most naturally proved in the complete field $C$. Algebraic points, however, live in finite extensions of $K$, and every finite extension is complete. Consequently the series defining the point attached to $u\in\overline K^\times$ already converge in the finite complete field $K(q,u)$ whenever their denominators do not vanish. Completion is a proof environment for identities, not a license to identify $C$-points with algebraic points.

Fix henceforth

$$
q\in K^\times,\qquad 0<|q|<1,
$$

and put $m=v(q)>0$. The positivity and nonzeroness are both essential. At $q=0$ the eventual cubic is singular; if $|q|=1$, the period orbit does not escape toward $0$ and the defining bilateral series fail to converge in the required fashion.

### 1.3 A convergence calculus for $q$-series

Nonarchimedean convergence is controlled by the largest term. This makes $q$-series especially rigid.

**Lemma 1.1 (one-sided $q$-series).** Let $F$ be a complete nonarchimedean field and $|q|<1$. If $(a_n)$ has at most polynomial growth in the real-valued norm, so $|a_n|\leq A n^r$ for fixed real $A>0$ and integer $r\geq0$, then

$$
\sum_{n\geq1}a_nq^n
$$

converges. In particular, for every integer $r\geq0$,

$$
\sum_{n\geq1}\frac{n^r q^n}{1-q^n}
$$

converges.

**Proof.** Every integer has absolute value at most $1$ in a nonarchimedean field, so in fact $|n^r|\leq1$. Also $|1-q^n|=1$. The displayed Lambert-series terms therefore have absolute value at most $|q|^n$, which tends to zero. A series in a complete nonarchimedean field converges exactly when its terms tend to zero. The same estimate proves the first assertion whenever the stated bound tends to zero after multiplication by $|q|^n$. $\square$

The relevant two-sided sums are only slightly subtler. Let $u\in F^\times$ and suppose $u\notin q^{\mathbf Z}$. For

$$
z_n=q^nu,
$$

the terms with $n\to+\infty$ satisfy $z_n\to0$. For $n\to-\infty$, one rewrites rational functions at infinity. For example,

$$
\frac{z}{(1-z)^2}=\frac{z^{-1}}{(1-z^{-1})^2},
\qquad
\frac{z^2}{(1-z)^3}=-\frac{z^{-1}}{(1-z^{-1})^3}.
$$

Both tend to zero as $|z|\to\infty$. Hence the bilateral sums made from these terms converge. More precisely, for any threshold $\varepsilon>0$, only finitely many indices have term of size at least $\varepsilon$. This **normal convergence** on a closed annulus avoiding the points $q^{\mathbf Z}$ permits termwise addition, multiplication by uniformly convergent series, and reindexing.

There is no hidden archimedean absolute convergence argument here. Normal convergence follows because the two tails separately tend to zero, and in an ultrametric field a finite or infinite tail is bounded by its largest term.

It is useful to record a uniform version because every later identity multiplies or differentiates such sums. Fix real numbers $0<r\leq s$ and consider the closed annulus

$$
A[r,s]=\{u\in C^\times:r\leq|u|\leq s\}.
$$

Assume that it contains none of the finitely many possible poles $q^j$. For $n\to+\infty$, one has $|q^nu|\leq |q|^ns$, so the positive tail is uniformly bounded by a geometric sequence in the ultrametric sense. For $n\to-\infty$, put $w=(q^nu)^{-1}$; then $|w|\leq |q|^{-n}r^{-1}\to0$, and the rewritten terms above give the same bound. All denominators for the remaining finitely many indices have a positive lower bound on the annulus. The sums are therefore uniform limits of rational functions there.

Termwise differentiation introduces factors $q^n$ and powers of $(1-q^nu)^{-1}$, but the same two-tail estimate still tends to zero on a slightly smaller pole-free annulus. Products may be formed by taking rectangular partial sums: outside a finite rectangle every product term contains a factor smaller than a prescribed threshold. These observations justify the analytic algebra used below without importing an archimedean comparison test.

The hypothesis $|q|<1$ cannot be weakened to $|q|\leq1$. If $|q|=1$ and $q$ is not a root of unity, the terms $q^n u/(1-q^nu)^2$ need not tend to zero in either direction. If $q$ is a root of unity, denominators actually repeat and may vanish. The strict inequality makes the orbit $q^{\mathbf Z}$ discrete: it tends to $0$ in one direction and to infinity in the other.

### 1.4 Products, logarithmic derivatives, and Lambert series

The basic infinite product is

$$
P(q)=\prod_{n\geq1}(1-q^n).
$$

It converges to a nonzero element of $K$. Indeed, $q^n\to0$, so the infinite-product criterion applies, and every factor is a unit. Moreover

$$
|P(q)|=1,
$$

because every finite partial product has absolute value $1$.

Products and Lambert series are linked by logarithmic differentiation as a formal identity:

$$
q\frac{d}{dq}\log P(q)
=-\sum_{n\geq1}\frac{nq^n}{1-q^n}.
$$

This identity is useful even in positive characteristic, where division by some integers or a global logarithm may be unavailable: after expanding each fraction geometrically, it is simply an identity of integral formal power series followed by specialization at $|q|<1$.

For $r\geq0$ put

$$
S_r(q)=\sum_{n\geq1}\frac{n^r q^n}{1-q^n}
=\sum_{N\geq1}\left(\sum_{d\mid N}d^r\right)q^N. \tag{1.1}
$$

The equality follows by expanding $(1-q^n)^{-1}=\sum_{a\geq0}q^{an}$ and grouping terms with $N=n(a+1)$. Normal convergence justifies the regrouping analytically, while the integral coefficient identity shows that the formula survives every characteristic. The functions $S_3$ and $S_5$ will be the coefficients of the curve; $S_1$ will normalize its coordinate functions.

### 1.5 The theta product and its functional equations

The Lambert series package the coefficients of the eventual cubic, but a second product is better suited to divisors and addition. For $u\in C^\times$ define

$$
\Theta(u,q)=(1-u)\prod_{n\geq1}(1-q^nu)(1-q^nu^{-1}). \tag{1.2}
$$

On a closed annulus, away from $q^{\mathbf Z}$, both tails tend uniformly to $1$. Indeed, $q^nu$ and $q^nu^{-1}$ tend uniformly to $0$. The product therefore converges normally and is nonzero unless one of its displayed factors vanishes. Its zero set is exactly

$$
\{q^r:r\in\mathbf Z\}, \tag{1.3}
$$

and every zero is simple. This is the multiplicative analogue of a sine function: it vanishes precisely on the period lattice and nowhere else.

Reindexing the factors gives the two basic functional equations

$$
\Theta(qu,q)=-u^{-1}\Theta(u,q),
\qquad
\Theta(u^{-1},q)=-u^{-1}\Theta(u,q). \tag{1.4}
$$

The sign and the power of $u$ are worth checking. Separate the factor $1-qu^{-1}$ from the second product in $\Theta(qu,q)$, shift the remaining indices, and use $1-u^{-1}=-u^{-1}(1-u)$. No division by $2$, $3$, or an integer index occurs, so the identities remain valid in every characteristic.

The function $\Theta$ itself does not descend to the quotient: it is **quasiperiodic**. Ratios in which the multipliers cancel do descend. For example, if $a_1a_2=b_1b_2$, then

$$
u\longmapsto
\frac{\Theta(u/a_1,q)\Theta(u/a_2,q)}
{\Theta(u/b_1,q)\Theta(u/b_2,q)} \tag{1.5}
$$

is unchanged by $u\mapsto qu$. Its divisor on the quotient is

$$
[a_1]+[a_2]-[b_1]-[b_2].
$$

Thus the theta product solves a concrete problem: it manufactures periodic functions with prescribed zeros and poles. It also gives a direct route to the group law. A degree-zero divisor $\sum_i[a_i]-\sum_j[b_j]$ is principal precisely when the two multisets have equal size and

$$
\prod_i a_i\equiv\prod_j b_j\pmod{q^{\mathbf Z}}. \tag{1.6}
$$

The necessity follows by multiplying the quasiperiodicity factors; the sufficiency follows from the corresponding theta quotient. Relation (1.6) says that addition in the divisor class group is multiplication of uniformizing parameters. It is the divisor-theoretic core of Tate uniformization.

Logarithmic derivatives connect this product with the functions used below. On any pole-free annulus, termwise differentiation gives

$$
u\frac{\partial}{\partial u}\log\Theta(u,q)
=-\frac{u}{1-u}
-\sum_{n\geq1}\frac{q^nu}{1-q^nu}
+\sum_{n\geq1}\frac{q^nu^{-1}}{1-q^nu^{-1}}. \tag{1.7}
$$

Here the notation means the quotient $u\Theta'(u,q)/\Theta(u,q)$; it does not require a globally defined logarithm. Differentiating once more produces the orbit sum with double poles that defines $X(u)$. In positive characteristic this quotient-of-derivatives interpretation is essential, since a global analytic logarithm need not exist and differentiation can annihilate $p$th powers. The product identities themselves, being integral, remain reliable.

Uniform convergence is asserted only on closed subannuli avoiding period points. There can be no uniform convergence on all of $C^\times$: every fundamental annulus has translates of the zero on its boundary, and $C^\times$ is not compact. All later termwise operations are therefore local on pole-free closed annuli and are glued using (1.4).

## 2. The equation of the Tate curve

### 2.1 Why the coefficients are Lambert series

A quotient of a one-dimensional analytic group by one period should have a one-dimensional space of invariant differentials and functions with prescribed poles. On the multiplicative group the invariant differential is $du/u$. To construct a degree-two function on the quotient, begin with the rational function $u/(1-u)^2$, which has a double pole at $u=1$, and sum it over the orbit $q^{\mathbf Z}$. A degree-three companion comes from $u^2/(1-u)^3$. Their Laurent expansions at the identity force an algebraic relation of Weierstrass type.

The constants in that relation are orbit sums. Comparing principal parts eliminates all dependence on $u$ and leaves the Lambert series $S_3$ and $S_5$. This explains why modular-looking coefficients arise: they are the correction needed to turn rational functions on $\mathbf G_m$ into functions periodic under $u\mapsto qu$.

### 2.2 The Weierstrass equation

Define

$$
a_4(q)=-5S_3(q),
\qquad
a_6(q)=-\frac{1}{12}\bigl(5S_3(q)+7S_5(q)\bigr). \tag{2.1}
$$

At first the factor $1/12$ appears to exclude characteristics $2$ and $3$. It does not. The coefficient of $q^N$ in $5S_3+7S_5$ is

$$
\sum_{d\mid N}(5d^3+7d^5),
$$

and $5d^3+7d^5=d^3(5+7d^2)$ is divisible by $12$ for every integer $d$: modulo $3$ it is $d^3(d^2-1)$, the product of three consecutive integers up to a harmless factor, and modulo $4$ the assertion is immediate for even $d$ while for odd $d$ one has $5+7d^2\equiv0\pmod4$. Thus $a_6\in\mathbf Z[[q]]$, and (2.1) means specialization of an integral power series in every characteristic.

The **Tate curve** attached to $q$ is

$$
E_q:\quad y^2+xy=x^3+a_4(q)x+a_6(q). \tag{2.2}
$$

Its invariants follow from the general formulas with $a_1=1$, $a_2=a_3=0$:

$$
\begin{aligned}
b_2&=1,& b_4&=2a_4,& b_6&=4a_6,& b_8&=a_6-a_4^2,\\
c_4&=1-48a_4=1+240S_3,\\
c_6&=-1+72a_4-864a_6=-1+504S_5.
\end{aligned} \tag{2.3}
$$

The identity $c_4^3-c_6^2=1728\Delta$ determines the discriminant as an integral series. Since $a_4,a_6\in q\mathbf Z[[q]]$, it already shows $c_4\equiv1$ and $c_6\equiv-1$ modulo $q$.

### 2.3 The discriminant product

The decisive closed formula is

$$
\Delta(q)=q\prod_{n\geq1}(1-q^n)^{24}. \tag{2.4}
$$

There are two complementary proofs. Algebraically, insert (2.1) into the discriminant polynomial, compare logarithmic derivatives of both sides using (1.1), and compare the leading coefficient. Analytically, compute the leading term of the invariant differential and the product of differences among the $q^{\mathbf Z}$-translates of a point. The first proof is especially robust across characteristics.

Here are the details of the logarithmic-derivative strategy in characteristic zero; the resulting integral identity then holds universally. From the Lambert expansions one calculates

$$
q\frac{d}{dq}\log\Delta(q)
=1-24S_1(q).
$$

The right side is also the logarithmic derivative of $qP(q)^{24}$. Their quotient therefore has zero logarithmic derivative and is constant. Both series begin with $q$, so the constant is $1$. Since all coefficients involved are integers, equality in $\mathbf Q[[q]]$ is equality in $\mathbf Z[[q]]$, and it may be specialized in every complete field.

Formula (2.4) proves smoothness at once. No factor $1-q^n$ vanishes when $|q|<1$, and the product is nonzero. It also gives the exact valuation

$$
v(\Delta(q))=v(q), \tag{2.5}
$$

because each factor is a unit. This simple equality will become the minimal discriminant formula in Chapter 4.

For completeness, the leading comparison used above may be made without logarithms. Since $S_3,S_5\in q\mathbf Z[[q]]$, direct substitution into the discriminant polynomial gives $\Delta=q+O(q^2)$. Let

$$
D(q)=qP(q)^{24}=q+O(q^2).
$$

The differential identity says $D\Delta'-\Delta D'=0$. If $\Delta/D=1+b_rq^r+O(q^{r+1})$ with $r\geq1$ least and the coefficient computed in characteristic zero, its derivative has leading term $rb_rq^{r-1}$, so $b_r=0$, a contradiction. Thus $\Delta/D=1$ in $\mathbf Q[[q]]$. Both sides have integral coefficients, and equality coefficient by coefficient may then be reduced to any characteristic. This argument also explains why proving the formula only by integrating a logarithm directly in residue characteristic $p$ would be unsafe: derivatives can kill $p$th powers there, whereas the universal integral identity does not lose them.

The exponent $24$ is not decorative. It is forced by the first logarithmic derivative, and it controls the first correction $-24q^2$ in (2.11). In particular $\Delta/q$ is always a unit congruent to $1$ modulo $q$. Hence no cancellation, even in residue characteristics $2$ or $3$, can raise $v(\Delta)$ above $v(q)$.

### 2.4 The $j$-expansion and its inverse

By definition,

$$
j(q)=\frac{c_4(q)^3}{\Delta(q)}.
$$

Expanding the integral series gives

$$
j(q)=q^{-1}+744+196884q+21493760q^2+864299970q^3+\cdots. \tag{2.6}
$$

Only two features are needed for most local arguments:

$$
j(q)=q^{-1}U(q),\qquad U(q)\in1+q\mathbf Z[[q]], \tag{2.7}
$$

and therefore

$$
v(j(q))=-v(q)<0. \tag{2.8}
$$

The series has an inverse at the cusp. Put $t=j^{-1}$. Then there is a unique integral series

$$
Q(t)=t+744t^2+750420t^3+872769632t^4+\cdots \tag{2.9}
$$

satisfying $j(Q(t))=t^{-1}$. Formal recursive substitution constructs it, and every term converges when $|t|<1$. Thus an element $j_0\in K$ with $|j_0|>1$ determines a canonical candidate

$$
q=Q(j_0^{-1})\in K,
\qquad |q|=|j_0|^{-1}. \tag{2.10}
$$

This is the analytic seed of the converse theorem. Equal $j$ does not alone imply isomorphism over $K$; a twist may remain. Splitness will remove that ambiguity.

### 2.5 A first numerical expansion

Modulo $q^4$, divisor sums give

$$
S_3=q+9q^2+28q^3+O(q^4),
\qquad
S_5=q+33q^2+244q^3+O(q^4).
$$

Hence

$$
\begin{aligned}
a_4&=-5q-45q^2-140q^3+O(q^4),\\
a_6&=-q-23q^2-154q^3+O(q^4),\\
c_4&=1+240q+2160q^2+6720q^3+O(q^4),\\
\Delta&=q-24q^2+252q^3-1472q^4+O(q^5).
\end{aligned} \tag{2.11}
$$

These are identities with integer coefficients, so $O(q^r)$ means an element of $q^rR$ after specialization. In small residue characteristic some displayed integer coefficients vanish, but the valuation conclusions $c_4\in R^\times$ and $v(\Delta)=v(q)$ remain unchanged. This is why the general equation (2.2), rather than a short equation obtained by dividing by $2$ or $3$, is the correct integral model.

## 3. Multiplicative uniformization

### 3.1 Elliptic functions on a multiplicative annulus

For $u\in C^\times\setminus q^{\mathbf Z}$ define

$$
\begin{aligned}
X(u)&=\sum_{n\in\mathbf Z}\frac{q^nu}{(1-q^nu)^2}
-2\sum_{n\geq1}\frac{nq^n}{1-q^n},\\
Y(u)&=\sum_{n\in\mathbf Z}\frac{(q^nu)^2}{(1-q^nu)^3}
+\sum_{n\geq1}\frac{nq^n}{1-q^n}.
\end{aligned} \tag{3.1}
$$

Chapter 1 proves convergence. Reindexing the bilateral sums gives

$$
X(qu)=X(u),\qquad Y(qu)=Y(u). \tag{3.2}
$$

Inversion gives

$$
X(u^{-1})=X(u),\qquad
Y(u^{-1})=-Y(u)-X(u), \tag{3.3}
$$

which agrees with negation on (2.2). Near $u=1$, if $z=1-u$, then

$$
X(u)=z^{-2}-z^{-1}+O(1),\qquad
Y(u)=z^{-3}-2z^{-2}+z^{-1}+O(1). \tag{3.4}
$$

Thus $X$ has a double pole and $Y$ a triple pole at every $q^n$, exactly the pole pattern of Weierstrass coordinates at the origin.

### 3.2 The uniformizing map

Substitution and comparison of principal parts prove

$$
Y(u)^2+X(u)Y(u)=X(u)^3+a_4X(u)+a_6. \tag{3.5}
$$

A useful proof avoids an unilluminating full expansion. The difference of the two sides is $q$-periodic. Its possible poles occur at $q^{\mathbf Z}$. Expanding at $u=1$ shows that all negative-power terms cancel precisely for the constants (2.1). The difference is therefore an analytic function on the proper quotient with no pole and hence constant. Evaluating in the limit $u\to0$ through a fundamental annulus shows the constant is zero. This pole-cancellation argument is the multiplicative counterpart of deriving a Weierstrass relation from Riemann--Roch spaces.

Define

$$
\phi_q:C^\times/q^{\mathbf Z}\longrightarrow E_q(C)
$$

by

$$
\phi_q([u])=
\begin{cases}
(X(u),Y(u)),&u\notin q^{\mathbf Z},\\
O,&u\in q^{\mathbf Z}.
\end{cases} \tag{3.6}
$$

The Laurent expansions show that the second line is the removable value on the quotient: the poles of $X$ and $Y$ are simply the affine manifestation of approaching the point at infinity.

### 3.3 Kernel, surjectivity, and the group law

**Theorem 3.1 (Tate uniformization).** The map $\phi_q$ is an isomorphism of analytic groups. In particular,

$$
0\longrightarrow q^{\mathbf Z}\longrightarrow C^\times
\xrightarrow{\ \phi_q\ }E_q(C)\longrightarrow0 \tag{3.7}
$$

is exact, and

$$
\phi_q(u_1u_2)=\phi_q(u_1)+\phi_q(u_2). \tag{3.8}
$$

The proof has three genuine parts. First, (3.4) identifies a local parameter at the identity and shows that the pullback of the invariant differential is

$$
\phi_q^*\left(\frac{dx}{2y+x}\right)=\frac{du}{u}. \tag{3.9}
$$

Thus the map is locally an isomorphism. Second, the divisor of $X(u)-X(a)$ shows that the only points with the same image as $a$ are $a$ and the inverse dictated by the group law; together with $Y$, this proves injectivity modulo $q^{\mathbf Z}$. In particular the preimage of $O$ is exactly $q^{\mathbf Z}$. Third, a nonconstant morphism from the complete one-dimensional quotient to the smooth cubic has open and closed image; connectedness gives surjectivity.

To see why the analytic isomorphism respects groups rather than merely spaces, consider

$$
(u,v)\longmapsto
\phi_q(uv)-\phi_q(u)-\phi_q(v).
$$

It is an analytic map from a connected two-dimensional domain to the discrete kernel of the induced local homomorphism near $(1,1)$. It is zero near $(1,1)$ by (3.9), hence zero everywhere. Equivalently, the invariant differential and the chosen identity rigidify a genus-one isomorphism into a group isomorphism.

The kernel statement is not $\mu_\infty$ and not the unit group. Multiplication by the single period $q$ is exactly what is forgotten. This distinction is the source of the later exact sequence for torsion.

Here is a more algebraic view of injectivity and surjectivity. On the quotient, $X$ has exactly one pole, at the identity, of order two. Therefore the induced map to the projective $X$-line has degree two. Identity (3.3) shows that its two points over a generic value are $[u]$ and $[u^{-1}]$. The function $Y$ separates these two unless they are equal, because (3.3) identifies its other value with $-Y-X$. Thus the pair $(X,Y)$ is generically injective. A finite degree-one map between smooth complete curves is an isomorphism; the Laurent expansion at the identity supplies finiteness there and normal convergence supplies it on every other annulus. This proves both global injectivity and surjectivity without a point count.

For the group law, let $\alpha$ denote the analytic isomorphism of the quotient with the cubic just obtained. Transport the cubic group law back to the quotient. Both the transported law and ordinary multiplication have identity $[1]$. Their invariant differential at that identity is $du/u$ by (3.9). For fixed $v$, the discrepancy between the two translations has zero derivative and fixes one point; on a smooth connected one-dimensional analytic group it is the identity. Varying $v$ gives equality of the two laws. This supplies the rigidity step behind (3.8).

The differential computation itself follows by differentiating (3.1). The derivative terms telescope after shifting $n$, and substitution of (3.5) simplifies the quotient to $du/u$. Near $u=1$, it is already forced: from (3.4), $dx/(2y+x)$ has leading term $-dz/(1-z)=du/u$. The quotient of the two invariant differentials is a pole-free function on the complete quotient, hence constant, and the leading term makes that constant $1$.

### 3.4 Galois equivariance and descent

All coefficients in (3.1) belong to $K$ and the series commute with every continuous $K$-automorphism of $C$. Therefore

$$
\sigma(X(u))=X(\sigma u),\qquad
\sigma(Y(u))=Y(\sigma u), \tag{3.10}
$$

and

$$
\phi_q(\sigma u)=\sigma\phi_q(u) \tag{3.11}
$$

for $\sigma\in G_K$. Since $q\in K$, the subgroup $q^{\mathbf Z}$ is fixed. The construction therefore descends to $K$ and yields

$$
E_q(K)\cong K^\times/q^{\mathbf Z}. \tag{3.12}
$$

More generally, for every algebraic extension $L/K$ endowed with the extended valuation,

$$
E_q(L)\cong L^\times/q^{\mathbf Z}. \tag{3.13}
$$

When $L$ is not complete, the right interpretation is the union over finite subextensions. Each individual point and its uniformizing parameter lie in a finite extension, where the series converge.

### 3.5 Why algebraic points do not require completion

There are two superficially plausible but incorrect shortcuts. The first is to state only $C^\times/q^{\mathbf Z}\cong E_q(C)$ and silently replace $C$ by $\overline K$. The second is to claim that a convergent series of algebraic elements must be algebraic; this is false in general.

Here the correct argument is more precise. If $q,u\in L$ for a finite extension $L/K$, every term of (3.1) lies in $L$, and $L$ is complete. Hence $X(u),Y(u)\in L$. Conversely, if $P\in E_q(\overline K)$, choose a finite extension $L$ containing its coordinates. Analytic surjectivity gives a parameter in $C^\times$; the finite morphism behavior on a fundamental annulus, or equivalently the descent of the inverse analytic map, shows that some representative belongs to a finite algebraic extension of $L$. Thus

$$
\overline K^\times/q^{\mathbf Z}\xrightarrow{\sim}E_q(\overline K), \tag{3.14}
$$

and similarly with $K^s$ when torsion orders are prime to the field characteristic. Completion proves the analytic theorem, while finite-extension completeness returns the result to algebraic arithmetic.

### 3.6 Analytic and algebraic uniformization compared

It is useful to isolate exactly what has been proved, because three quotients occur in practice. For every finite extension $L/K$, the same convergent formulas give an exact sequence

$$
0\longrightarrow q^{\mathbf Z}\longrightarrow L^\times
\xrightarrow{\ \phi_q\ }E_q(L)\longrightarrow0. \tag{3.15}
$$

For an arbitrary algebraic extension $M/K$, both sides are unions over finite subextensions, so (3.15) remains exact with $L$ replaced by $M$. For the complete algebraically closed field $C$, it is an exact sequence of analytic groups. These assertions are compatible but not interchangeable: $C^\times$ contains transcendental elements over $K$, whereas $(K^s)^\times$ does not.

Surjectivity over $K$ can also be read directly from equivariance. Take $P\in E_q(K)$ and choose $u\in(K^s)^\times$ mapping to it. For every $\sigma\in G_K$ there is an integer $n_\sigma$ such that

$$
\sigma(u)=q^{n_\sigma}u. \tag{3.16}
$$

The map $\sigma\mapsto n_\sigma$ is a continuous homomorphism from the compact group $G_K$ to the discrete torsion-free group $\mathbf Z$. Its image is finite and hence zero. Thus $u\in K^\times$. This argument explains why no hidden obstruction appears when passing from invariant classes to classes of invariant elements.

The algebraic content may be summarized as follows.

**Theorem 3.2 (uniformization over complete extensions).** Let $L/K$ be a complete valued extension, not necessarily discretely valued, and retain $q\in K$ with $0<|q|<1$. Then the formulas (3.1) define a homomorphism

$$
L^\times/q^{\mathbf Z}\longrightarrow E_q(L).
$$

It is an isomorphism when $L$ is algebraically closed and complete. It is also an isomorphism for every algebraic extension of $K$, interpreted as a union of its finite subextensions. In all cases the pullback of the invariant differential is $du/u$.

**Proof strategy.** Normal convergence gives the map and its differential. The theta quotients of Section 1.5 show that every meromorphic function on the quotient with a prescribed degree-zero divisor is generated by multiplicative parameters. In particular, $X$ has degree two and $(X,Y)$ has degree one, proving the algebraically closed case. Descent to algebraic extensions uses (3.16). The differential identity was established locally at $u=1$ and then globally because the ratio of two invariant differentials is constant. $\square$

The theorem is functorial in $L$. If $L'/L$ is an extension, the square

$$
\begin{array}{ccc}
L^\times/q^{\mathbf Z}&\longrightarrow&E_q(L)\\
\downarrow&&\downarrow\\
(L')^\times/q^{\mathbf Z}&\longrightarrow&E_q(L')
\end{array}
$$

commutes. This elementary compatibility is what later allows one to read Galois action from roots of $q$: the parameter is not reconstructed separately after every extension.

## 4. Integral geometry and split multiplicative reduction

### 4.1 The integral equation

Because $a_4,a_6\in qR$, equation (2.2) is integral. Its invariant quantities satisfy

$$
c_4\equiv1\pmod{\mathfrak m},\qquad
c_6\equiv-1\pmod{\mathfrak m},\qquad
\Delta\in\mathfrak m. \tag{4.1}
$$

Reduction gives the same cubic in every residue characteristic:

$$
\overline E:\quad y^2+xy=x^3. \tag{4.2}
$$

Its unique affine singular point is $(0,0)$. The lowest-degree part at that point is

$$
y^2+xy=y(y+x), \tag{4.3}
$$

so the two tangent lines $y=0$ and $y=-x$ are distinct and defined over $k$, even in characteristic $2$. Thus the special fiber is nodal and split. The deliberate presence of the $xy$ term makes this conclusion uniform across residue characteristics.

### 4.2 Minimality and the exact discriminant exponent

The integral equation is minimal. Indeed, $c_4$ is a unit. Any integral coordinate change lowering the discriminant would divide $c_4$ by a positive fourth power of a uniformizer, contradicting integrality of the new $c_4$. This is precisely the minimality criterion developed for integral Weierstrass models.

Combining minimality with (2.4) yields the central equality

$$
v(\Delta_{\min}(E_q/K))=v(\Delta(q))=v(q)=m. \tag{4.4}
$$

The normalization matters: $v(K^\times)=\mathbf Z$. If $L/K$ has ramification index $e$ and $v_L$ is normalized separately, then

$$
v_L(q)=e\,v_K(q). \tag{4.5}
$$

The same Tate equation over $\mathcal O_L$ remains minimal because $c_4$ remains a unit, so its minimal discriminant exponent is $e m$. There is no subsequent decrease modulo $12$. The unit $c_4$ rules out every weighted dilation.

Since $j=c_4^3/\Delta$, one also has

$$
v(j(E_q))=-m. \tag{4.6}
$$

Thus for multiplicative reduction the three integers

$$
v(q),\qquad v(\Delta_{\min}),\qquad -v(j)
$$

coincide. This equality is special to multiplicative reduction and should not be transplanted to additive reduction.

### 4.3 The special fiber and its tangent directions

Remove the node from (4.2). The map

$$
t\longmapsto (x,y)=\left(\frac{t}{(1-t)^2},\frac{t^2}{(1-t)^3}\right)
$$

with a harmless sign change depending on the chosen parameter identifies the smooth locus with $\mathbf G_{m,k}$ and sends multiplication of $t$ to the cubic group law. One can verify the inverse rationally by taking the ratio of two tangent-adapted linear forms. The missing values $t=0,\infty$ are the two branches at the node; identifying them produces the nodal cubic.

The generic uniformizing coordinate $u$ reduces to this $t$ when $|u|=1$. Consequently the isomorphism

$$
E_0(K)/E_1(K)\cong k^\times
$$

is not an accidental agreement of abstract groups. It is reduction of the multiplicative coordinate itself. The two tangent directions being rational is exactly what permits $k^\times$, rather than a nonsplit one-dimensional torus, to appear.

### 4.4 The polygon of components

The minimal plane cubic records a node but not all components of the smooth model. Resolving a degeneration of thickness $m$ replaces the node by a cycle of $m$ rational components, the fiber type traditionally denoted $I_m$. Their incidence graph is a polygon; for $m=1$ it is a looped single component in the appropriate regular-model sense.

The quotient description already predicts the component labels. Valuation gives

$$
K^\times/q^{\mathbf Z}\longrightarrow\mathbf Z/m\mathbf Z,
\qquad [u]\longmapsto v(u)\bmod m. \tag{4.7}
$$

The kernel consists of classes with a unit representative. Hence the geometric component group is cyclic of order $m$. The cyclic order in the polygon reflects successive valuations $0,1,\ldots,m-1$; multiplication by $q$ closes the cycle by identifying $m$ with $0$. Chapter 7 will turn this observation into exact sequences for local points.

## 5. The converse theorem and the canonical parameter

### 5.1 Why negative $j$-valuation should force a period

The construction so far begins with $q$ and produces split multiplicative reduction. Arithmetic applications usually begin in the opposite direction: an elliptic curve $E/K$ is given by an equation, and its minimal model is found to have split multiplicative reduction. To use multiplicative coordinates on its points and torsion, one must recover a parameter $q\in K$ and prove that $E$ is actually $E_q$.

The invariant $j$ identifies the analytic region in which this is possible. For a minimal multiplicative equation, $c_4$ is a unit and $v(\Delta_{\min})>0$, so

$$
v(j(E))=-v(\Delta_{\min})<0. \tag{5.1}
$$

Conversely, a negative $j$-valuation says that the curve is potentially multiplicative: after a finite extension it becomes a Tate curve. It does not by itself say that the reduction is split over $K$. A nonsplit quadratic twist has the same $j$. The missing datum is the action on the two branches of the node.

This separation is conceptually useful. The value $j^{-1}$ measures distance to the cusp in the one-dimensional moduli line. The splitness character measures whether the multiplicative coordinate descends without inversion. The first supplies $q$; the second decides the form of the curve over $K$.

### 5.2 Analytic inversion of $j$

Let $j_0\in K$ satisfy $v(j_0)<0$ and set $t=j_0^{-1}\in\mathfrak m$. The inverse series (2.9) converges and defines

$$
q=Q(t)=t(1+744t+750420t^2+\cdots). \tag{5.2}
$$

Because the parenthesis is a unit,

$$
v(q)=v(t)=-v(j_0). \tag{5.3}
$$

It remains to justify uniqueness without appealing only to a formal symbol. Suppose $q_1,q_2\in\mathfrak m\setminus\{0\}$ and $j(q_1)=j(q_2)$. From $q=j^{-1}(1+O(q))$ one first gets $|q_1|=|q_2|$. Applying the convergent inverse series to the common $j^{-1}$ gives $q_1=q_2$. Thus the condition $0<|q|<1$ removes the apparent alternative $q^{-1}$ and selects a unique period.

The inverse is stable under extension. If $j_0\in K$ and the calculation is performed in any complete extension $L$, every partial sum of $Q(j_0^{-1})$ lies in $K$ and its limit lies in $K$ because $K$ is closed in $L$. Hence adjoining a splitting field cannot change the parameter.

### 5.3 Tate's converse uniformization theorem

**Theorem 5.1 (converse Tate uniformization).** Let $K$ be complete for a nontrivial discrete valuation and let $E/K$ have split multiplicative reduction. There is a unique $q\in K^\times$ with $v(q)>0$ and a $K$-isomorphism

$$
E\xrightarrow{\sim}E_q.
$$

The isomorphism may be chosen to carry a minimal invariant differential of $E$ to a unit multiple of $du/u$ under uniformization. Moreover

$$
v(q)=-v(j(E))=v(\Delta_{\min}(E/K)). \tag{5.4}
$$

**Proof strategy.** Equation (5.2) first constructs the only possible $q$ from $j(E)$. Over an algebraic closure, equal $j$ gives an isomorphism between $E$ and $E_q$, apart from the familiar exceptional automorphisms; negative valuation excludes $j=0,1728$ as field elements of nonnegative valuation. The obstruction to descending that isomorphism is an automorphism cocycle. Near a nodal fiber, its only relevant quadratic part acts on the multiplicative coordinate by $u\mapsto u^{-1}$. Split reduction says that both tangent directions are individually rational, so this cocycle is trivial. The isomorphism descends to $K$.

One may also prove the theorem directly from the formal neighborhood and the smooth locus. The formal group of $E$ is analytically identified with $1+\mathfrak m$ through the minimal differential. Continue this local isomorphism across successive annuli. Traversing all $m=v(\Delta_{\min})$ components returns to the identity after multiplication by one element $q$ of valuation $m$. The resulting map $K^\times/q^{\mathbf Z}\to E(K)$ has the correct differential and extends algebraically to $E_q\to E$. Comparing $j$ identifies this period with (5.2).

Both proofs explain the hypotheses. Completeness glues the successive local corrections. Multiplicative reduction supplies a torus. Splitness identifies that torus with $\mathbf G_m$ over $K$ rather than only after an unramified quadratic extension.

We can make the descent step in the first proof explicit. Choose an isomorphism

$$
f:E_{K^s}\longrightarrow(E_q)_{K^s}.
$$

For $\sigma\in G_K$, the composite $f\,{}^\sigma f^{-1}$ is an automorphism of $E_q$ fixing the origin. Because $v(j)<0$, the values $j=0$ and $1728$ are excluded, so over a separably closed field the automorphism group is $\{\pm1\}$, including in the small-characteristic cases relevant here after interpreting the exceptional values correctly. Hence the composites define a quadratic character. Under degeneration, $+1$ fixes each tangent branch and $-1$ exchanges them, as is visible from $u\mapsto u^{-1}$. Split reduction says that Galois fixes both branches, so the character is trivial. Then ${}^\sigma f=f$ for every $\sigma$, and ordinary Galois descent gives $f$ over $K$.

There is one apparent circularity: equal $j$ first gives an isomorphism only after an algebraic closure, while $q$ was constructed analytically. But $q\in K$ by convergence of (5.2), and $E_q$ is algebraic by equation (2.2). The classification of elliptic curves over an algebraically closed field now applies directly to the two algebraic curves. No descent assertion is hidden in the analytic inversion.

Finally, (5.4) follows without choosing the descended isomorphism carefully. Isomorphic elliptic curves have the same $j$, so (5.3) gives $v(q)=-v(j(E))$. A minimal multiplicative equation has $v(c_4)=0$, and therefore $v(j(E))=-v(\Delta_{\min})$. This also proves that the analytic period has exactly the collision thickness found from the original integral model.

### 5.4 Uniqueness and behavior under extension

The parameter is stronger than a choice of equation. If $E_q\cong_K E_{q'}$ with $v(q),v(q')>0$, equality of $j$ and analytic inversion give $q=q'$. In particular changing a minimal equation does not change $q$.

Let $L/K$ be finite. The curve $E_q/L$ is still a Tate curve with the same field element $q$, while normalized valuations give

$$
v_L(q)=e(L/K)v_K(q).
$$

Thus the number of geometric components is multiplied by the ramification index. Under unramified extension it is unchanged, although residue extension may alter splitness for a nonsplit curve. This clean division—ramification changes the polygon length, residue extension changes its Galois labeling—is one of the most useful features of the parameter.

A warning is worthwhile. Two elements $q$ and $q\varepsilon$ with $\varepsilon\in1+\mathfrak m^N$ can have the same valuation and extremely close $j$-invariants, but unless $\varepsilon=1$ the Tate curves are generally not isomorphic. The integer $v(q)$ records reduction thickness; the full element $q$ records the analytic isomorphism class.

## 6. Nonsplit multiplicative reduction

### 6.1 The splitting character

For a nodal special fiber, the two tangent directions are defined over a separable extension of $k$ of degree at most two. The absolute Galois group permutes them, producing a character

$$
\eta:G_K\longrightarrow\{\pm1\}. \tag{6.1}
$$

It is trivial precisely for split multiplicative reduction. Because the tangent directions live in the residue field, inertia acts trivially on them; hence $\eta$ is unramified. If the reduction is nonsplit, $\eta$ is the nontrivial unramified quadratic character and the curve becomes split over the corresponding unramified quadratic extension $K'/K$.

This formulation requires that such a quadratic residue extension exist. For the standard local fields with finite residue field it always does. More generally, the two tangent directions define a quadratic étale $k$-algebra; lifting that algebra gives the appropriate unramified étale extension or split algebra. No assumption that the residue characteristic is odd is needed for this separable branch construction.

Over $K'$, choose the multiplicative parameter $u$. The nontrivial automorphism $\tau\in\operatorname{Gal}(K'/K)$ exchanges the tangent directions and therefore acts by

$$
\tau(u)=u^{-1}\quad\text{modulo }q^{\mathbf Z}. \tag{6.2}
$$

This inversion is the geometric meaning of the sign $\eta(\tau)=-1$.

### 6.2 Unramified quadratic twisting

Let $E/K$ have nonsplit multiplicative reduction, and let $K'/K$ split it. The converse theorem over $K'$ gives $E_{K'}\cong E_q$ for a unique $q\in K'$. Since $j(E)\in K$, formula (5.2) shows in fact that

$$
q\in K. \tag{6.3}
$$

The descent datum differs from the ordinary descent of $E_q$ by the involution $[-1]$, which is $u\mapsto u^{-1}$ in multiplicative coordinates. Thus $E$ is the quadratic twist of $E_q$ by $\eta$.

When $2$ is invertible, this can be seen in an equation. Complete the square in (2.2): with $Y=y+x/2$,

$$
Y^2=x^3+\frac14x^2+a_4x+a_6. \tag{6.4}
$$

If $d\in R^\times$ represents the unramified quadratic class, a twist is

$$
Y^2=x^3+\frac d4x^2+d^2a_4x+d^3a_6. \tag{6.5}
$$

Its $j$ is unchanged. Its tangent square class is multiplied by $d$, so split and nonsplit reduction are exchanged. Formula (6.5) is only a convenient odd-residue-characteristic picture; the twisting statement itself is valid without dividing by $2$.

### 6.3 The nonsplit converse

**Theorem 6.1 (potentially multiplicative classification).** Let $E/K$ be an elliptic curve with $v(j(E))<0$. Put

$$
q=Q(j(E)^{-1}).
$$

Then there is a unique character $\eta:G_K\to\{\pm1\}$ such that $E$ is the $\eta$-twist of $E_q$. If $E$ has multiplicative reduction over $K$, the character is unramified; it is trivial in the split case and nontrivial in the nonsplit case. In either of these two multiplicative cases

$$
v(\Delta_{\min})=v(q)=-v(j(E)). \tag{6.6}
$$

The final equality for nonsplit multiplicative reduction follows either from the minimal-model criterion or after unramified base change, which preserves normalized valuations and minimal discriminant exponents. A ramified quadratic character can also occur when $v(j)<0$, but then the curve need not already have multiplicative reduction over $K$; it may have additive, potentially multiplicative reduction. That case lies beyond the split/nonsplit multiplicative dichotomy of this book.

The theorem prevents a common error: a nonsplit curve is not uniformized over $K$ by the naive quotient $K^\times/q^{\mathbf Z}$. Its points are the fixed points of a twisted Galois action on $K'^\times/q^{\mathbf Z}$.

### 6.4 Component groups in the nonsplit case

Over $K'$ the geometric component group is $\mathbf Z/m\mathbf Z$, where $m=v(q)$. The nontrivial descent automorphism sends the multiplicative coordinate to its inverse, hence acts on component labels by

$$
a\longmapsto-a. \tag{6.7}
$$

Therefore the rational component classes are

$$
(\mathbf Z/m\mathbf Z)^{\eta=-1}
=\{a\in\mathbf Z/m\mathbf Z:2a=0\}. \tag{6.8}
$$

For a henselian local field with finite residue field, smooth lifting identifies these with the quotient $E(K)/E_0(K)$. Its order is

$$
c(E/K)=
\begin{cases}
1,&m\text{ odd},\\
2,&m\text{ even}.
\end{cases} \tag{6.9}
$$

This is a useful counterpoint to the split case, where the quotient has order $m$. The geometric fiber still has $m$ components; descent, not geometry, reduces the number represented by $K$-points.

### 6.5 Twisted point descent

The formula $\tau([u])=[u]^{-1}$ deserves to be unpacked. A class $[u]\in (K')^\times/q^{\mathbf Z}$ descends to a $K$-point of the nonsplit twist exactly when

$$
\tau(u)u\in q^{\mathbf Z}. \tag{6.10}
$$

Consequently

$$
E(K)\cong
\{u\in(K')^\times:\tau(u)u\in q^{\mathbf Z}\}/q^{\mathbf Z}, \tag{6.11}
$$

where multiplication by $q^r$ changes $\tau(u)u$ by $q^{2r}$. Taking valuations in (6.10) yields

$$
2v(u)\equiv0\pmod m. \tag{6.12}
$$

This immediately recovers the possible rational components: only $0$ occurs when $m$ is odd, while $0$ and $m/2$ can occur when $m$ is even. For finite $k$, the norm-one theorem and smooth lifting show that every one of these fixed component classes is attained.

On the identity component one may choose $v(u)=0$. After multiplying by a power of $q$, condition (6.10) becomes

$$
N_{K'/K}(u)=1. \tag{6.13}
$$

Reduction gives the norm-one torus over $k$. Its formal subgroup consists of $u\in1+\mathfrak m_{K'}$ with norm one. Thus nonsplit points retain a multiplicative description, but the correct group is a norm kernel rather than $K^\times$.

If the residue field is not finite, two qualifications are necessary. First, the quadratic étale algebra of tangent directions need not be a field and need not be unique merely from the word “unramified”; it is the particular algebra cut out by the two branches. Second, the map from $E(K)$ onto the fixed geometric component classes can fail to be surjective, with obstruction in the first cohomology of the identity torus over $k$. Formula (6.11) remains correct and is safer than replacing rational components by Galois-fixed geometric components without a hypothesis.

For residue characteristic $2$, the branch algebra is still separable because a node has two distinct geometric tangent lines. A quadratic polynomial defining those lines may be an Artin--Schreier polynomial rather than $T^2-d$. Accordingly, the character $\eta$ and the inversion descent remain valid, but the square-root twist equation (6.5) is not an integral model and should not be used.

## 7. Local points and the reduction filtration

### 7.1 A fundamental annulus

Every class in $K^\times/q^{\mathbf Z}$ has a representative $u$ with

$$
0\leq v(u)<m. \tag{7.1}
$$

Multiply by the unique power of $q$ that moves $v(u)$ into this interval. The representative is unique in valuation, though its unit part remains arbitrary. Thus a fundamental annulus decomposes into $m$ valuation circles. The circle $v(u)=0$ is the identity component; the others label the remaining components.

This is the nonarchimedean replacement for choosing a parallelogram for a complex lattice. There is no angular continuum. Instead, valuation gives the radial coordinate modulo $m$, and the unit filtration gives successively finer coordinates along the identity component.

### 7.2 $E(K)$, $E_0(K)$, and $E_1(K)$

For split multiplicative reduction, uniformization identifies the reduction filtration exactly:

$$
\begin{aligned}
E(K)&\cong K^\times/q^{\mathbf Z},\\
E_0(K)&\cong R^\times,\\
E_1(K)&\cong U^1=1+\mathfrak m.
\end{aligned} \tag{7.2}
$$

The second and third lines mean that the indicated subgroups inject into the quotient, since no nonzero power of $q$ is a unit. Reduction of the uniformizing coordinate gives

$$
E_0(K)/E_1(K)\cong R^\times/U^1\cong k^\times. \tag{7.3}
$$

At deeper levels,

$$
E_n(K)/E_{n+1}(K)\cong U^n/U^{n+1}\cong k^+
\qquad(n\geq1), \tag{7.4}
$$

where $E_n$ denotes the formal-group filtration. The pullback formula $dx/(2y+x)=du/u$ explains why multiplication near $u=1$ linearizes to addition in $\mathfrak m^n/\mathfrak m^{n+1}$.

For nonsplit reduction, let $K'/K$ be the unramified quadratic splitting extension. Then

$$
E(K)=\{[u]\in K'^\times/q^{\mathbf Z}:\tau[u]=[u]^{-1}\}. \tag{7.5}
$$

On the identity component this reduces to the norm-one torus. Its special-fiber points are

$$
\{z\in k'^\times:N_{k'/k}(z)=1\}, \tag{7.6}
$$

not $k^\times$. This is the point-level manifestation of the nonsplit tangent cone.

### 7.3 Reduction and component exact sequences

In the split case the valuation and residue maps yield exact sequences

$$
0\longrightarrow R^\times
\longrightarrow K^\times/q^{\mathbf Z}
\xrightarrow{v}\mathbf Z/m\mathbf Z
\longrightarrow0, \tag{7.7}
$$

and

$$
1\longrightarrow U^1\longrightarrow R^\times
\longrightarrow k^\times\longrightarrow1. \tag{7.8}
$$

The first sequence splits as abstract groups only when one can choose an element of valuation $1$ whose $m$th power differs from $q$ by an $m$th power in $R^\times$; it has no canonical splitting in general. Confusing a set of annular representatives with a group-homomorphic section loses precisely the unit part of $q$.

When $k$ is finite of cardinality $Q$, (7.8) gives $|E_0(K)/E_1(K)|=Q-1$. The full group $E(K)$ is locally compact, with finite component quotient of order $m$. It need not be finite because $U^1$ is infinite.

### 7.4 Valuations of coordinates

The series (3.1) provide useful coordinate estimates. If $0<v(u)<m$, then the $n=0$ term dominates the positive tail while the $n=-1$ term controls the negative tail in a complementary range. In particular $X(u),Y(u)$ are integral and reduce to the singular point on the minimal plane cubic; the valuation $v(u)$ remembers which resolved component the section meets.

If $u\in R^\times$ and $u\not\equiv1\pmod{\mathfrak m}$, the $n=0$ terms are units and reduction gives a smooth nonidentity point. If $u=1+z$ with $v(z)>0$, then (3.4) gives

$$
v(X(u))=-2v(z),\qquad v(Y(u))=-3v(z). \tag{7.9}
$$

Thus points in the formal neighborhood of $O$ have nonintegral affine coordinates in exactly the weighted ratio $2:3$. The local parameter $-x/y$ has valuation $v(z)$ and agrees with $1-u$ to first order.

These estimates also show why the node of the plane model cannot by itself distinguish all nonidentity components: many different positive values of $v(u)$ reduce to $(0,0)$. Resolution separates them according to valuation modulo $m$.

### 7.5 Rational torsion

A class $[u]\in K^\times/q^{\mathbf Z}$ has order dividing $n$ exactly when

$$
u^n=q^a
$$

for some $a\in\mathbf Z$. Taking valuations gives

$$
nv(u)=am. \tag{7.10}
$$

Thus the component of a rational torsion point must be killed by $n$ in $\mathbf Z/m\mathbf Z$. On the identity component, rational torsion is the root-of-unity subgroup of $K$.

More explicitly, write $d=\gcd(n,m)$. The possible component labels killed by $n$ form a subgroup of order $d$. A label is actually realized over $K$ only if the corresponding unit equation has a solution. For example, a point mapping to $m/d$ requires an element $u\in K$ with

$$
u^{n/d}=q^{1/d}
$$

up to a root of unity, so the unit part of $q$ matters. Valuation conditions are necessary, not sufficient.

If $K$ has finite residue field and $n$ is prime to $p$, roots of unity of order dividing $n$ are controlled by $k^\times$, while the power map is an automorphism on $U^1$. Hence rational prime-to-$p$ torsion can be decided by a finite residue calculation together with the divisibility of $m$ and the Kummer class of $q$.

Here is that decision in coordinates. Write

$$
q=\pi^m\omega\varepsilon,
$$

where $\omega$ is a Teichmüller lift of a residue unit and $\varepsilon\in U^1$. For $n$ prime to $p$, choose uniquely $\varepsilon_0\in U^1$ with $\varepsilon_0^n=\varepsilon$. Thus modulo $(K^\times)^n$ the class of $q$ is represented by $\pi^m\omega$. It is an $n$th power precisely when

$$
n\mid m
\quad\text{and}\quad
\overline\omega\in(k^\times)^n. \tag{7.11}
$$

More generally, the rational lifts of a component label $a\in\mathbf Z/m\mathbf Z$ killed by $n$ are governed by the same test applied to $q^{a/n}$ after clearing the evident valuation. This reduces all prime-to-$p$ rational torsion questions to the cyclic residue group when $k$ is finite.

For example, let $K=\mathbf Q_7$, $q=7^6\cdot2$, and $n=3$. The component group has three-torsion because $3\mid6$. But $2$ is not a cube modulo $7$, so $q$ is not a cube and no $K$-rational point gives a splitting lift of the generator of $\mathbf Z/3\mathbf Z$. Replacing $2$ by $-1$ makes the residue unit a cube and produces such a point. The component group alone cannot distinguish the two curves.

At $p$-power order, principal units are no longer automatically divisible. Over $\mathbf Q_p$, the equation $x^p=1+a$ can have a derivative divisible by $p$, so its solvability depends on deeper unit layers. This is the point-level warning corresponding to the representation-theoretic boundary in Section 9.3.

## 8. Finite torsion and the Kummer extension

### 8.1 The exact sequence for $E_q[n]$

Let $n\geq1$ and assume

$$
\gcd(n,\operatorname{char}K)=1. \tag{8.1}
$$

Then multiplication by $n$ on an elliptic curve is separable and $E_q[n](K^s)$ has order $n^2$. A uniformizing class is $n$-torsion exactly when $u^n\in q^{\mathbf Z}$. Sending it to the exponent modulo $n$ gives a canonical exact sequence of $G_K$-modules

$$
0\longrightarrow\mu_n
\longrightarrow E_q[n]
\longrightarrow\mathbf Z/n\mathbf Z
\longrightarrow0. \tag{8.2}
$$

The first map sends $\zeta$ to $[\zeta]$. For the last map, if $u^n=q^a$, send $[u]$ to $a\bmod n$. Replacing $u$ by $q^r u$ changes $a$ by $nr$, so the map is well defined. Its kernel has $a\equiv0$, and after multiplying $u$ by a power of $q$ one has $u^n=1$, giving $\mu_n$.

Surjectivity is seen after choosing $q^{1/n}\in K^s$: its class maps to $1$. The exact sequence is canonical, but this choice of a lift is not. The failure of a $K$-rational choice is measured by the Kummer class of $q$.

We check exactness without counting points. If $[u]$ is killed by $n$, then $[u^n]=[1]$, so $u^n=q^a$ for a unique integer $a$ once a representative is fixed. Replacing the representative by $q^ru$ replaces $a$ by $a+nr$, proving that $a\bmod n$ is intrinsic. Every residue class $b\bmod n$ is attained by $u=q_n^b$. If $a\equiv0\pmod n$, write $a=nr$ and replace $u$ by $q^{-r}u$; the new representative has $n$th power one. This identifies the kernel with $\mu_n$, including its Galois action. Thus all arrows and exactness assertions in (8.2) arise directly from the quotient.

The hypothesis on $n$ is used twice. It makes $X^n-q$ separable, so $q_n$ lies in $K^s$, and it makes $\mu_n(K^s)$ cyclic of order $n$. If $n$ is divisible by $\operatorname{char}K$, both statements can fail simultaneously. Merely knowing that the residue characteristic does not divide $n$ is stronger than necessary for (8.2), but it is the natural hypothesis for the tame analysis of Chapters 9 and 10.

### 8.2 Roots of unity and a root of $q$

Choose a primitive root $\zeta_n\in K^s$ and an element $q_n\in K^s$ with

$$
q_n^n=q.
$$

In additive notation for the torsion group, put

$$
e_1=[\zeta_n],\qquad e_2=[q_n]. \tag{8.3}
$$

These form a basis of the free $\mathbf Z/n\mathbf Z$-module $E_q[n]$. Indeed, every torsion parameter is $\zeta_n^a q_n^b$ modulo $q^{\mathbf Z}$, and the only relation has both $a$ and $b$ divisible by $n$.

The field generated by the torsion coordinates is therefore

$$
K(E_q[n])=K(\mu_n,q^{1/n}), \tag{8.4}
$$

where equality means equality inside a fixed separable closure. One inclusion follows from the parameterization. For the other, the inverse uniformization recovers the parameters modulo $q^{\mathbf Z}$; ratios among chosen torsion parameters recover roots of unity and an $n$th root of $q$.

### 8.3 The Galois matrix

Define the cyclotomic character $\chi_n:G_K\to(\mathbf Z/n\mathbf Z)^\times$ by

$$
\sigma(\zeta_n)=\zeta_n^{\chi_n(\sigma)}.
$$

Define the Kummer cocycle $c_{q,n}:G_K\to\mathbf Z/n\mathbf Z$ by

$$
\sigma(q_n)=\zeta_n^{c_{q,n}(\sigma)}q_n. \tag{8.5}
$$

Then

$$
c_{q,n}(\sigma\tau)
=c_{q,n}(\sigma)+\chi_n(\sigma)c_{q,n}(\tau). \tag{8.6}
$$

With column vectors and with the images of basis vectors placed in the columns, the Galois matrix is

$$
\rho_{E_q,n}(\sigma)=
\begin{pmatrix}
\chi_n(\sigma)&c_{q,n}(\sigma)\\
0&1
\end{pmatrix}. \tag{8.7}
$$

The convention matters. Formula (8.6) is exactly what makes (8.7) multiplicative in the order $\rho(\sigma\tau)=\rho(\sigma)\rho(\tau)$. Choosing $q_n^{-1}$ or reversing the basis changes the sign or triangular orientation but not the extension class.

The determinant is

$$
\det\rho_{E_q,n}=\chi_n. \tag{8.8}
$$

Here this is a direct calculation from uniformization. The general conceptual relation between the determinant and the Weil pairing belongs to the next volume.

### 8.4 Splitting and reducibility

Sequence (8.2) always gives a $G_K$-stable line $\mu_n$. Hence for prime $n=\ell\ne\operatorname{char}K$, the two-dimensional residual representation is reducible. Reducible does not mean split. Its semisimplification is

$$
E_q[\ell]^{\mathrm{ss}}\cong\mathbf F_\ell(1)\oplus\mathbf F_\ell. \tag{8.9}
$$

The extension splits if and only if its Kummer class vanishes:

$$
E_q[n]\cong\mu_n\oplus\mathbf Z/n\mathbf Z
\quad\Longleftrightarrow\quad
q\in(K^\times)^n. \tag{8.10}
$$

For if $q=r^n$ with $r\in K$, the class $[r]$ is a $G_K$-fixed lift of $1$. Conversely, a $G_K$-equivariant section supplies such a lift; after multiplying its parameter by a root of unity, Galois descent gives an $n$th root of $q$ in $K$. Equivalently, the extension class is the image of $q$ under

$$
K^\times/(K^\times)^n\cong H^1(G_K,\mu_n). \tag{8.11}
$$

For a nonsplit multiplicative curve with splitting character $\eta$, twisting (8.7) gives diagonal characters $\eta\chi_n$ and $\eta$. It remains reducible, and its extension splits under the same Kummer condition on $q$.

A useful valuation obstruction is immediate: if $n\nmid v(q)$, then $q$ cannot be an $n$th power. The converse fails because a unit may obstruct extraction. When $n$ is prime to $p$, the principal-unit part causes no obstruction, but the residue unit can.

One can see the extension class change under a different choice of $q_n$. Replacing $q_n$ by $\zeta_n^a q_n$ changes

$$
c_{q,n}(\sigma)
\quad\text{to}\quad
c_{q,n}(\sigma)+a\chi_n(\sigma)-a. \tag{8.12}
$$

This is a coboundary, so the class is independent of the root. Replacing the primitive root $\zeta_n$ by $\zeta_n^b$ with $b\in(\mathbf Z/n\mathbf Z)^\times$ rescales the first basis vector and the cocycle by $b^{-1}$. Again, vanishing and ramification are unchanged.

For composite $n$, “reducible” is best expressed by the exact sequence rather than by field-linear language, since $\mathbf Z/n\mathbf Z$ is not a field. The subgroup $\mu_n$ is cyclic and direct summand as an abstract module, but need not have a Galois-stable complement. For a prime $\ell$, (8.9) is the usual two-dimensional semisimplification.

The Kummer condition also distinguishes a rational cyclic subgroup from a rational basis. The subgroup $\mu_n\subset E_q[n]$ is always $G_K$-stable, even when its individual generators are not rational. Thus it defines a rational cyclic direction. A full split basis requires both the cyclotomic action to be accounted for and the quotient extension to split; $q\in(K^\times)^n$ addresses the latter, not the rationality of every root of unity.

### 8.5 The Weil pairing in multiplicative coordinates

The triangular matrix already gives the cyclotomic determinant, but the alternating pairing explains why that determinant is intrinsic. Assume $n$ is invertible in $K$. Normalize the Weil pairing by requiring, for the basis (8.3),

$$
e_n(e_1,e_2)=\zeta_n. \tag{8.13}
$$

This fixes the harmless inverse ambiguity that comes from competing sign conventions. Bilinearity and alternation then give, for

$$
P=[\zeta_n^a q_n^b],
\qquad
Q=[\zeta_n^c q_n^d],
$$

the explicit formula

$$
e_n(P,Q)=\zeta_n^{ad-bc}. \tag{8.14}
$$

One can prove (8.13) without presupposing the general pairing theory. Choose a theta quotient whose divisor is the pullback under multiplication by $n$ of a divisor representing $e_1$. Comparing its value after translation by $e_2$ with its value before translation, the quasiperiodicity (1.4) contributes exactly $\zeta_n$. Bilinearity follows from multiplying divisor functions, alternation from interchanging the two translations, and nondegeneracy from the determinant $ad-bc$. This divisor construction agrees with the usual Weil pairing because both are characterized by the same translation formula.

Galois equivariance reads

$$
e_n(\sigma P,\sigma Q)=\sigma(e_n(P,Q)). \tag{8.15}
$$

If $A(\sigma)$ is the matrix of $\sigma$ in the ordered basis $(e_1,e_2)$, then (8.14) transforms the exponent by $\det A(\sigma)$. The right side of (8.15) transforms $\zeta_n$ by $\chi_n(\sigma)$. Hence

$$
\det A(\sigma)=\chi_n(\sigma). \tag{8.16}
$$

This recovers (8.8) in a basis-free way. It also shows why an unramified quadratic twist does not change the determinant: both basis vectors acquire the factor $\eta$, and $\eta^2=1$.

Formula (8.14) makes the two canonical directions visibly dual. The subgroup $\mu_n$ is isotropic, as every cyclic subgroup must be under an alternating pairing, and the quotient $\mathbf Z/n\mathbf Z$ pairs perfectly with it after choosing a lift. There is no canonical lift: changing $e_2$ by $ae_1$ leaves $e_n(e_1,e_2)$ unchanged, exactly as the Kummer cocycle changes by a coboundary.

When $n$ is not invertible, the same formula belongs to the finite flat group objects rather than merely to geometric points. The multiplicative group $\mu_n$ may then be nonreduced, but Cartier duality still pairs it with the constant cyclic quotient. The pointwise determinant argument is therefore valid only for invertible $n$; the group-theoretic pairing survives more generally and anticipates the coefficient-prime discussion of Chapter 11.

### 8.6 What changes in characteristic $p$

Condition (8.1) concerns the characteristic of the field, not the residue characteristic. Over a $p$-adic field, $\operatorname{char}K=0$, so (8.2) remains valid even for $n$ divisible by $p$ as a statement about generic-fiber algebraic points. Its integral and ramification behavior is then much subtler because $\mu_{p^r}$ is highly ramified.

Over $K=k((t))$ of characteristic $p$, the sequence of geometric points fails for $n$ divisible by $p$. The group of $p$th roots of unity in $K^s$ is trivial, since $X^p-1=(X-1)^p$, and multiplication by $p$ is inseparable. Scheme-theoretically there is still a multiplicative subgroup, but its geometric points do not form a cyclic group of order $p$. All matrix statements in this book therefore impose $n$ prime to $\operatorname{char}K$; the prime-to-$p$ Tate modules remain two-dimensional and behave exactly as described.

The scheme-theoretic replacement is still exact in the faithfully flat sense:

$$
0\longrightarrow\mu_n\longrightarrow E_q[n]
\longrightarrow\mathbf Z/n\mathbf Z\longrightarrow0. \tag{8.17}
$$

To see why, use the same exponent map as in (8.2). A local lift of the class $a\bmod n$ is obtained after adjoining a solution of $T^n=q^a$; that cover is finite and flat because the polynomial is monic, even when it is inseparable. Its kernel is defined by $T^n=1$, namely $\mu_n$. Thus separability is needed to turn (8.17) into an exact sequence of $n^2$ geometric points, not for the finite flat exact sequence itself. In characteristic $p$, this distinction is decisive.

## 9. Tate modules and cyclotomic determinant

### 9.1 Prime-to-residue-characteristic Tate modules

Fix a prime $\ell\ne p$. Then $\ell$ is invertible in $R$ and, in particular, $\ell\ne\operatorname{char}K$. Choose compatible systems

$$
\zeta_{\ell^{r+1}}^\ell=\zeta_{\ell^r},
\qquad
q_{r+1}^\ell=q_r,
\qquad q_r^{\ell^r}=q. \tag{9.1}
$$

Passing to inverse limits in (8.2) gives an exact sequence

$$
0\longrightarrow\mathbf Z_\ell(1)
\longrightarrow T_\ell(E_q)
\longrightarrow\mathbf Z_\ell
\longrightarrow0. \tag{9.2}
$$

Exactness on the right can be seen concretely from the compatible classes $[q_r]$. No inverse-limit obstruction occurs because the transition maps on the finite cyclic quotients are surjective.

Let

$$
e_1=( [\zeta_{\ell^r}] )_r,
\qquad
e_2=( [q_r] )_r. \tag{9.3}
$$

They form a $\mathbf Z_\ell$-basis. Define the $\ell$-adic cyclotomic character by

$$
\sigma(\zeta_{\ell^r})
=\zeta_{\ell^r}^{\chi_\ell(\sigma)\bmod\ell^r},
$$

and define $c_{q,\ell}(\sigma)\in\mathbf Z_\ell$ through

$$
\sigma(q_r)=
\zeta_{\ell^r}^{c_{q,\ell}(\sigma)\bmod\ell^r}q_r. \tag{9.4}
$$

The compatible finite cocycles make this well defined.

### 9.2 The integral matrix and its determinant

In the basis (9.3), with the column convention of Chapter 8,

$$
\rho_{E_q,\ell}(\sigma)=
\begin{pmatrix}
\chi_\ell(\sigma)&c_{q,\ell}(\sigma)\\
0&1
\end{pmatrix}. \tag{9.5}
$$

The cocycle law is

$$
c_{q,\ell}(\sigma\tau)
=c_{q,\ell}(\sigma)
+\chi_\ell(\sigma)c_{q,\ell}(\tau). \tag{9.6}
$$

Consequently

$$
\det\rho_{E_q,\ell}=\chi_\ell. \tag{9.7}
$$

Tensoring with $\mathbf Q_\ell$ gives

$$
0\longrightarrow\mathbf Q_\ell(1)
\longrightarrow V_\ell(E_q)
\longrightarrow\mathbf Q_\ell
\longrightarrow0. \tag{9.8}
$$

This rational extension never splits over $G_K$ for a genuine Tate parameter. Indeed, splitting would make the Kummer class of $q$ vanish in the inverse limit of $K^\times/(K^\times)^{\ell^r}$. Its valuation $m>0$ cannot be divisible by arbitrarily high powers of $\ell$. Finite-level reductions may split, but the full $\ell$-adic extension does not.

Changing the compatible roots changes $e_2$ to $e_2+a e_1$ for some $a\in\mathbf Z_\ell$. The cocycle changes by the coboundary

$$
c'_{q,\ell}(\sigma)=c_{q,\ell}(\sigma)
+a\chi_\ell(\sigma)-a. \tag{9.9}
$$

Thus the individual upper-right entries depend on choices, while their extension class and all ramification conclusions do not.

### 9.3 Coefficient characteristic equal to residue characteristic

Suppose now that $p$ is a prime, $\operatorname{char}K=0$, and the residue characteristic is $p$. Because multiplication by $p^r$ on the generic elliptic curve is separable, the same construction gives

$$
0\longrightarrow\mathbf Z_p(1)
\longrightarrow T_p(E_q)
\longrightarrow\mathbf Z_p
\longrightarrow0 \tag{9.10}
$$

and the same matrix

$$
\begin{pmatrix}
\chi_p&c_{q,p}\\0&1
\end{pmatrix}. \tag{9.11}
$$

The determinant is still cyclotomic. What changes is inertia: $\chi_p$ is now ramified, and extracting $p$-power roots of units is no longer controlled by the prime-to-$p$ unit argument. The simple tame formula of Chapter 10 must not be used.

If $\operatorname{char}K=p$, the inverse limit of geometric $p^r$-torsion points is not a free rank-two $\mathbf Z_p$-module. The multiplicative part has no nontrivial geometric points, and inseparability intervenes. Accordingly, every assertion here about a two-dimensional $p$-adic Tate module at residue characteristic $p$ assumes mixed characteristic $(0,p)$.

Even in mixed characteristic, (9.10) alone does not provide the full structure of the representation relative to period rings or integral models. It does give the exact extension and determinant that can be justified directly from Tate uniformization.

### 9.4 The nonsplit twist

Let $E/K$ have nonsplit multiplicative reduction and splitting character $\eta$. Over the unramified quadratic splitting field, $E$ is $E_q$. Descent twists the representation:

$$
T_\ell(E)\cong T_\ell(E_q)\otimes\eta. \tag{9.12}
$$

Thus a suitable basis gives

$$
\rho_{E,\ell}(\sigma)=
\begin{pmatrix}
\eta(\sigma)\chi_\ell(\sigma)&
\eta(\sigma)c_{q,\ell}(\sigma)\\
0&\eta(\sigma)
\end{pmatrix}. \tag{9.13}
$$

Its determinant is

$$
\eta^2\chi_\ell=\chi_\ell, \tag{9.14}
$$

so splitness changes the two diagonal characters but not the determinant. Since $\eta$ is unramified, split and nonsplit multiplicative curves have identical restrictions to inertia after compatible choices.

At finite level, the semisimplification is

$$
E[\ell]^{\mathrm{ss}}\cong
(\mathbf F_\ell(1)\otimes\eta)
\oplus\eta. \tag{9.15}
$$

For $\ell=2$, the sign character becomes trivial modulo $2$, so the residual representation cannot distinguish split from nonsplit through its diagonal characters alone. The integral or odd-adic representation still does.

### 9.5 Duality and the determinant

Passing the pairings $e_{\ell^r}$ to the inverse limit gives a perfect alternating pairing

$$
T_\ell(E)\times T_\ell(E)
\longrightarrow\mathbf Z_\ell(1). \tag{9.16}
$$

Equivalently,

$$
T_\ell(E)^\vee\cong T_\ell(E)(-1). \tag{9.17}
$$

For the Tate basis this is simply the inverse-limit form of the determinant $ad-bc$. The submodule $\mathbf Z_\ell(1)\otimes\eta$ is its own annihilator, and the quotient $\mathbf Z_\ell\otimes\eta$ is dual to that line after the indicated twist. The extension is therefore self-dual in the symplectic sense even though it is not split.

There is a useful check on every matrix convention. Let

$$
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

For the matrix $A(\sigma)$ in (9.13), direct multiplication gives

$$
A(\sigma)^{\mathsf t}J A(\sigma)
=\chi_\ell(\sigma)J. \tag{9.18}
$$

The off-diagonal Kummer term cancels. Thus the representation has symplectic multiplier $\chi_\ell$; in dimension two that multiplier is the determinant. If a proposed local formula has determinant $\eta\chi_\ell$ rather than $\chi_\ell$, it has twisted only one diagonal character and cannot be the representation of the elliptic curve.

The same calculation works modulo $\ell^r$. At $\ell=2$, alternation still means $e(P,P)=1$ even though the matrix $J$ reduces to a symmetric matrix. The determinant identity is unchanged. What disappears modulo $2$ is the distinction between the signs $+1$ and $-1$, not the pairing or its nondegeneracy.

## 10. Inertia, monodromy, and conductor

### 10.1 The tame character from roots of a uniformizer

Assume in this chapter that $K$ has finite residue field of characteristic $p>0$ and that $\ell\ne p$. Write

$$
q=\pi^m u,\qquad u\in R^\times. \tag{10.1}
$$

Choose compatible $\ell^r$th roots of $\pi$ and compatible roots of unity. For $\sigma$ in inertia $I_K$, define the $\ell$-primary tame character $t_\ell:I_K\to\mathbf Z_\ell$ by

$$
\sigma(\pi^{1/\ell^r})
=\zeta_{\ell^r}^{t_\ell(\sigma)\bmod\ell^r}
\pi^{1/\ell^r}. \tag{10.2}
$$

This normalization depends on the chosen roots and uniformizer, but changing them only makes a compatible harmless adjustment. It captures the maximal pro-$\ell$ quotient of tame inertia.

Why does the unit $u$ not contribute on inertia? The principal-unit group $U^1$ is uniquely $\ell$-divisible because the derivative of $X^{\ell^r}-a$ is a unit at each lifting step. The residue-unit part acquires its prime-to-$p$ roots in unramified extensions. Therefore compatible $\ell$-power roots of $u$ may be chosen in the maximal unramified extension times $K$, and their Kummer cocycle restricts trivially to inertia. It follows that

$$
c_{q,\ell}|_{I_K}=m\,t_\ell. \tag{10.3}
$$

This formula is exact with the conventions (9.4) and (10.2). Replacing the chosen primitive roots by their inverses changes both $c$ and $t$ by the same sign.

### 10.2 Unipotent inertia

For $\ell\ne p$, all $\ell$-power roots of unity are unramified over $K$, so

$$
\chi_\ell|_{I_K}=1. \tag{10.4}
$$

Combining (9.5) and (10.3) gives

$$
\rho_{E_q,\ell}(\sigma)=
\begin{pmatrix}
1&m\,t_\ell(\sigma)\\
0&1
\end{pmatrix}
\qquad(\sigma\in I_K). \tag{10.5}
$$

This is the characteristic unipotent shape of multiplicative reduction. The operator

$$
N=\begin{pmatrix}0&m\\0&0\end{pmatrix}
$$

is nilpotent with $N^2=0$, and inertia acts as $1+t_\ell(\sigma)N$. Rescaling the second basis vector over $\mathbf Q_\ell$ can replace $m$ by $1$, so the rational representation remembers only that monodromy is nonzero. The integral lattice remembers the exact divisibility of $m=v(q)$.

Wild inertia acts trivially because $t_\ell$ factors through tame inertia. The same formula holds for nonsplit multiplicative reduction: the character $\eta$ is unramified and hence equals $1$ on $I_K$.

### 10.3 Conductor consequences

For an $\ell$-adic representation with $\ell\ne p$, the Artin conductor exponent is

$$
a(V)=\dim V-\dim V^{I_K}+\operatorname{Swan}(V). \tag{10.6}
$$

For $V=V_\ell(E)$ at a multiplicative place, wild inertia is trivial, so the Swan term is zero. Since $m\ne0$ in the characteristic-zero field $\mathbf Q_\ell$, equation (10.5) has a one-dimensional invariant subspace, namely the line spanned by $e_1$. Therefore

$$
a(V_\ell(E))=2-1=1. \tag{10.7}
$$

This proves, at exactly the level supplied by uniformization, that split and nonsplit multiplicative reduction both have conductor exponent one. It does not calculate conductors for additive reduction, and it does not identify all higher ramification filtrations. Those require the systematic ramification theory developed elsewhere.

The result is independent of $m$, although the minimal discriminant exponent is $m$. A curve of type $I_1$ and one of type $I_{100}$ both have conductor exponent one. Discriminant thickness and representation-theoretic ramification measure different phenomena: the first counts the component cycle, while the second sees the rank of the nonzero monodromy operator.

To verify the invariant dimension directly, let $ae_1+be_2\in V_\ell(E_q)$ be fixed by inertia. Equation (10.5) sends it to

$$
(a+bmt_\ell(\sigma))e_1+be_2.
$$

The tame character has infinite image in $\mathbf Z_\ell$, and $m\ne0$ in $\mathbf Q_\ell$, so invariance for every $\sigma$ forces $b=0$. Every multiple of $e_1$ is fixed because $\chi_\ell$ is unramified. Hence $V^{I_K}=\mathbf Q_\ell e_1$ exactly.

Wild inertia lies in the kernel of $t_\ell$ and of $\chi_\ell$, so it acts trivially; this proves the vanishing of the Swan conductor rather than assuming it from the word “multiplicative.” Formula (10.7) is therefore a complete calculation from the matrix.

### 10.4 Residual ramification and level lowering

Reduce (10.5) modulo $\ell$. Then

$$
\overline\rho_{E,\ell}(\sigma)=
\begin{pmatrix}
1&\overline m\,\overline t_\ell(\sigma)\\
0&1
\end{pmatrix}. \tag{10.8}
$$

The residual representation is ramified on inertia precisely when

$$
\ell\nmid m=v(\Delta_{\min}). \tag{10.9}
$$

If $\ell\mid m$, its inertial action is trivial. This does not imply that the residual extension splits as a $G_K$-module: the unit part of $q$ can leave a nonzero unramified Kummer class, visible on Frobenius. It says only that the local conductor of the residual representation is zero.

When $\ell\nmid m$, the invariant subspace has dimension one and wild inertia remains trivial, so the residual Artin conductor exponent is one. Thus

$$
a(\overline\rho_{E,\ell})=
\begin{cases}
1,&\ell\nmid v(\Delta_{\min}),\\
0,&\ell\mid v(\Delta_{\min}).
\end{cases} \tag{10.10}
$$

This divisibility criterion is a principal local input in arguments that compare the conductor of an elliptic curve with the conductor of its residual representation. It is valid for $\ell\ne p$ and multiplicative reduction. It should not be applied at $\ell=p$ or to additive reduction.

The semisimplification is unramified on inertia in either case because both diagonal characters are unramified for $\ell\ne p$. All residual multiplicative ramification is therefore extension data, not semisimple diagonal data.

### 10.5 Frobenius and the local special representation

The inertial formula does not by itself remember splitness. Frobenius supplies the missing sign. Let $k$ have cardinality $Q$, and call a lift $F\in G_K$ of $x\mapsto x^Q$ on $\overline k$ an arithmetic Frobenius lift. With this convention

$$
\chi_\ell(F)=Q. \tag{10.11}
$$

For $\ell\ne p$, formula (9.13) becomes

$$
\rho_{E,\ell}(F)=
\eta(F)
\begin{pmatrix}
Q&c_{q,\ell}(F)\\
0&1
\end{pmatrix}. \tag{10.12}
$$

The entry $c_{q,\ell}(F)$ depends on compatible roots of $q$ and on the chosen lift of Frobenius. The diagonal characters, the determinant, and the conjugacy class of the associated monodromy data do not. Over $\mathbf Q_\ell$, replacing $e_2$ by $e_2+a e_1$ changes the Frobenius entry by $(Q-1)a$. Since $Q-1\ne0$ in $\mathbf Q_\ell$, one can choose $a$ so that the displayed Frobenius matrix is diagonal. This change does not kill inertia, because the nonzero monodromy operator remains.

We now state a convention-complete form of the local special representation. Put

$$
N(e_1)=0,
\qquad
N(e_2)=m e_1. \tag{10.13}
$$

Let $r$ be the unramified representation with

$$
r(F)=\eta(F)
\begin{pmatrix}Q&0\\0&1\end{pmatrix}. \tag{10.14}
$$

Then

$$
r(F)N r(F)^{-1}=QN. \tag{10.15}
$$

Equations (10.13)--(10.15), together with the declared arithmetic-Frobenius convention, are the monodromy package attached to $V_\ell(E)$. Some sources use geometric Frobenius $F^{-1}$; every occurrence of $Q$ in (10.14) and (10.15) is then replaced by $Q^{-1}$. Other sources rescale $e_2$ and write $N(e_2)=e_1$. Such a rescaling is legitimate over $\mathbf Q_\ell$ but not necessarily over $\mathbf Z_\ell$ when $\ell\mid m$. The integral factor $m$ is exactly what residual level lowering detects.

The phrase **special local representation** means precisely that $N\ne0$ and that the two unramified diagonal characters differ by the cyclotomic character, with the common unramified sign $\eta$. In the present normalization,

$$
V_\ell(E)^{\mathrm{ss}}
\cong (\mathbf Q_\ell(1)\otimes\eta)\oplus\eta,
\qquad N\ne0. \tag{10.16}
$$

The sign $\eta(F)$ is $+1$ for split and $-1$ for nonsplit multiplicative reduction. Thus the special representation distinguishes the two cases through its unramified character, while the restriction to inertia and the conductor exponent do not.

One must also distinguish the representation on the Tate module from its dual or from a twist used in cohomology. Dualizing inverts the two diagonal characters; twisting moves a power of $\chi_\ell$ between them. Formula (10.12) is for the covariant Tate module $T_\ell(E)=\varprojlim E[\ell^r]$ with column vectors. It has determinant $\chi_\ell$ and is the normalization used throughout this book.

### 10.6 The boundary at the residue characteristic

At $\ell=p$ in mixed characteristic, the matrix (9.11) remains valid, but neither diagonal cyclotomic action nor the unit Kummer class is tame. Formula (10.5) is false: $\chi_p$ is generally nontrivial on inertia. The naive expression $1+t_pN$ omits essential ramification.

One may still read several facts directly. The representation is reducible, has a $G_K$-stable line $\mathbf Q_p(1)$, has cyclotomic determinant, and is governed by the Kummer class of $q$. Its extension does not split over $\mathbf Q_p$ because $v(q)>0$. A finer statement describes it as semistable and noncrystalline, with a nonzero monodromy operator, but proving and even defining those terms requires additional $p$-adic comparison theory. We record the elementary exact sequence and stop at that precise boundary.

In equal characteristic $p$, there is no two-dimensional $p$-adic representation made from geometric $p$-power torsion points, as Chapter 8 explained. Prime-to-$p$ representations still satisfy every tame formula above.

## 11. Finite-flat boundaries at the coefficient prime

### 11.1 Why generic torsion is not enough

Let $K$ now have mixed characteristic $(0,p)$. The generic $p$-torsion of a Tate curve still fits into

$$
0\longrightarrow\mu_p\longrightarrow E_q[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0. \tag{11.1}
$$

Over $K$ all three terms are étale, because the characteristic is zero. Over $R$, however, $\mu_p$ is finite and flat but not étale, while the constant group $\mathbf Z/p\mathbf Z$ remains étale. Asking whether (11.1) extends over $R$ is therefore an integral question invisible from the dimension of the generic representation.

There is an immediate conceptual distinction from Chapter 10. When $\ell\ne p$, the residual cyclotomic character is unramified and the whole residual representation becomes unramified exactly when $\ell\mid m$. When $\ell=p$, the character $\overline\chi_p$ is usually ramified, so even a finite-flat residual representation is generally not unramified. The correct local condition at the coefficient prime is extendability by a finite flat group over $R$, not triviality on inertia.

Nor does finite flatness mean that the elliptic curve has good reduction. A Tate curve has multiplicative reduction by construction. What may extend is its finite layer of torsion, in a model depending on that layer; the curve itself does not become an elliptic scheme over $R$.

### 11.2 The integral Kummer boundary

The Kummer sequence must now be read for the faithfully flat topology. For a DVR, every line bundle is trivial, so its low-degree part gives

$$
R^\times/(R^\times)^p
\cong H^1(R,\mu_p). \tag{11.2}
$$

Over the fraction field,

$$
K^\times/(K^\times)^p
\cong H^1(K,\mu_p). \tag{11.3}
$$

The map from (11.2) to (11.3) is induced by inclusion of units. Its image consists exactly of the Kummer classes whose valuation is divisible by $p$:

$$
[a]\text{ comes from }R
\quad\Longleftrightarrow\quad
v(a)\equiv0\pmod p. \tag{11.4}
$$

To prove this, write $a=\pi^r u$. Multiplication by a $p$th power changes $r$ by a multiple of $p$, so a unit representative forces $p\mid r$. Conversely, if $r=ps$, then

$$
a(\pi^{-s})^p=u\in R^\times,
$$

so the class is represented by a unit. No assertion about the $p$th-power map on principal units is being made; all of the delicate unit information remains in $R^\times/(R^\times)^p$.

Applying (11.4) to $q$ gives the exact numerical boundary

$$
[q]\text{ is an integral Kummer class}
\quad\Longleftrightarrow\quad
p\mid v(q)=v(\Delta_{\min}). \tag{11.5}
$$

This is the coefficient-prime counterpart of the residual criterion (10.9), but the conclusions differ. Away from $p$, divisibility kills inertia. At $p$, divisibility says that the extension class can be represented over $R$; it does not kill the cyclotomic inertia on the multiplicative line.

The same argument works at level $p^r$:

$$
[q]\in\operatorname{im}\bigl(R^\times/(R^\times)^{p^r}
\to K^\times/(K^\times)^{p^r}\bigr)
\quad\Longleftrightarrow\quad
p^r\mid m. \tag{11.6}
$$

Since a fixed positive integer $m$ is not divisible by every $p^r$, the entire $p$-divisible Tate extension never extends as an extension of a constant $p$-divisible group by the multiplicative one. Finite flatness at one residual level is therefore compatible with noncrystalline monodromy of the full $p$-adic representation.

### 11.3 The canonical finite-flat extension

We now construct the finite flat model promised by (11.5). Suppose $m=ps$ and write

$$
q=(\pi^s)^p a,
\qquad a\in R^\times. \tag{11.7}
$$

For each $i\in\{0,1,\ldots,p-1\}$ take the finite flat $R$-scheme

$$
\mathcal G_i=\operatorname{Spec}R[T_i]/(T_i^p-a^i). \tag{11.8}
$$

Their disjoint union $\mathcal G=\coprod_i\mathcal G_i$ has rank $p^2$. Multiplication is defined on coordinates by multiplying $T_iT_j$ when $i+j<p$ and by dividing the product by $a$ when the index is reduced modulo $p$. This is legitimate because $a$ is a unit. Associativity is inherited from multiplication of the corresponding parameters, the component $i=0$ is $\mu_p$, and the component label gives a quotient $\mathbf Z/p\mathbf Z$. Thus

$$
0\longrightarrow\mu_p\longrightarrow\mathcal G
\longrightarrow(\mathbf Z/p\mathbf Z)_R\longrightarrow0 \tag{11.9}
$$

is an exact sequence of finite flat groups.

On the generic fiber, send a point $T_i=z$ to the Tate parameter

$$
u=(\pi^s)^i z.
$$

Then $u^p=q^i$, so its class is $p$-torsion and maps to $i$ in (11.1). This identifies the generic fiber of (11.9) with $E_q[p]$. The construction proves the following precise statement.

**Theorem 11.1 (canonical extension criterion).** The Tate exact sequence (11.1), with its specified subgroup $\mu_p$ and constant quotient, extends to an exact sequence of finite flat groups over $R$ if and only if

$$
p\mid v(q).
$$

**Proof.** Sufficiency is the construction (11.7)--(11.9). For necessity, pull back a hypothetical extension along the section $1\in\mathbf Z/p\mathbf Z$. The resulting $\mu_p$-torsor over $R$ has generic Kummer class $q$. By (11.2), that class is represented by a unit, and (11.4) gives $p\mid v(q)$. $\square$

Twisting by an unramified quadratic character preserves finite flatness: the character is represented by a finite étale quadratic descent datum over $R$, and tensoring the two generic directions by it commutes with descent. Hence Theorem 11.1 applies equally to split and nonsplit multiplicative reduction at the level of the canonical twisted sequence.

### 11.4 When the criterion is necessary

The word “canonical” in Theorem 11.1 matters. It asks for a model extending the visibly distinguished multiplicative subgroup and constant quotient. An abstract generic representation can conceivably have another finite flat model in which those two generic lines do not extend in the expected order. To promote (11.5) to a criterion for the representation itself, one needs a uniqueness principle for the relevant finite flat subgroup.

Here is the form used most often in semistable arguments. Assume that $K/\mathbf Q_p$ is unramified and $p$ is odd. On inertia, the two residual diagonal characters are

$$
\overline\chi_p\eta
\qquad\text{and}\qquad
\eta. \tag{11.10}
$$

Since $\eta$ is unramified and $\overline\chi_p$ is nontrivial on tame inertia, the two characters are distinct. The multiplicative line is therefore intrinsic. If $E[p]$ has any finite flat model, schematic closure of that line gives $\mu_p$, the quotient gives the constant group, and the model is an extension of the form (11.9). Theorem 11.1 then yields

$$
E[p]\text{ is finite flat over }R
\quad\Longleftrightarrow\quad
p\mid v(\Delta_{\min}) \tag{11.11}
$$

under these hypotheses.

The uniqueness assertion in that argument has a short valuation explanation. A rank-$p$ finite flat group over an unramified DVR is controlled, after choosing an augmentation parameter, by two coefficients whose product is a unit multiple of $p$. Their valuations are nonnegative integers adding to $v(p)=1$, so only the pairs $(0,1)$ and $(1,0)$ occur. They give respectively the étale and multiplicative models. Their generic characters are $1$ and $\overline\chi_p$, which are distinct for odd $p$. Thus the closure of the cyclotomic line can only be $\mu_p$, and the quotient can only be constant. Exactness follows because over a DVR a finite torsion-free module is flat. This proves the particular uniqueness input used above; when $v(p)>1$, intermediate valuation pairs appear and the argument no longer applies.

The proof uses only two features of the unramified odd-prime setting: the two generic characters remain distinguishable, and closure of the multiplicative line preserves the required finite-flat exact sequence. More ramified bases can have several integral models of the same generic group and require a separate classification. It would be incorrect to quote (11.11) there without checking that uniqueness input.

Residue characteristic $3$ causes no exception to the Tate equation or to the Kummer calculation. The integral equation $y^2+xy=x^3+a_4x+a_6$ avoids division by $3$, the discriminant product remains valid, and for an unramified extension of $\mathbf Q_3$ the two characters in (11.10) are distinct. Thus (11.11) includes $p=3$. What fails in characteristic $3$ is the casual use of a short Weierstrass equation, not the Tate construction.

### 11.5 The dyadic and equal-characteristic boundaries

At $p=2$, the mod-$2$ cyclotomic character is trivial. The two diagonal characters of the residual Tate representation coincide, and the sign character also reduces to $1$. Consequently the generic representation no longer singles out the multiplicative line by its character. The closure argument used in Section 11.4 breaks at exactly this point.

The integral Kummer statement itself remains true:

$$
[q]\text{ has a unit representative modulo squares}
\quad\Longleftrightarrow\quad
2\mid v(q). \tag{11.12}
$$

Hence even $m$ is necessary and sufficient for the **canonical** extension of $\mu_2$ by $\mathbf Z/2\mathbf Z$ constructed above. It is not, without further classification, a theorem that every possible finite flat model of the abstract two-dimensional mod-$2$ representation must preserve that filtration. This is why dyadic statements in modularity arguments are normally formulated using a separately established finite-flat condition or a more refined classification, rather than inferred from the odd-prime proof.

One can see the loss of information directly. Modulo $2$ the matrices for split and nonsplit multiplicative reduction have the same diagonal entries, and changing a basis may interchange extensions that were distinguished by their characters at odd primes. Neither the tangent-cone sign nor the generic semisimplification repairs this.

In equal characteristic $p$, geometric $p$-torsion is not a two-dimensional vector space, and the matrix language of (11.10) is unavailable. The finite group object still has a nonreduced multiplicative part, but its classification belongs to inseparable group geometry. For every coefficient prime $\ell\ne p$, the prime-to-$p$ results of Chapters 8--10 remain unchanged, including the exact residual unramified criterion $\ell\mid m$.

The boundary can now be stated cleanly:

$$
\begin{array}{c|c|c}
\text{coefficient prime}&\text{condition on }m&\text{conclusion}\\ \hline
\ell\ne p&\ell\mid m&\overline\rho_{E,\ell}\text{ is unramified}\\
\ell=p>2,\ \operatorname{char}K=0&p\mid m&
\text{the canonical residual extension is finite flat}\\
\ell=p=2&2\mid m&
\text{same canonical conclusion; abstract necessity needs more input}\\
\ell=p=\operatorname{char}K&-&
\text{no rank-two geometric }p\text{-torsion representation.}
\end{array} \tag{11.13}
$$

This table is not merely terminological. It prevents the prime-to-$p$ phrase “unramified after reduction” from being carried across the coefficient-prime boundary, where the cyclotomic line is intrinsically ramified.

## 12. Worked local fields

### 12.1 A split curve over $\mathbf Q_5$

Take $K=\mathbf Q_5$ with $v(5)=1$ and

$$
q=25.
$$

Then $m=2$. The first terms (2.11) give

$$
\begin{aligned}
a_4&=-5\cdot25-45\cdot25^2+O(5^6),\\
a_6&=-25-23\cdot25^2+O(5^6).
\end{aligned}
$$

Thus $v(a_4)=3$ and $v(a_6)=2$, while $c_4$ is a unit. The discriminant product gives

$$
\Delta=25\prod_{n\geq1}(1-25^n)^{24},
\qquad v(\Delta)=2. \tag{12.1}
$$

The equation

$$
y^2+xy=x^3+a_4x+a_6
$$

is minimal with split multiplicative reduction of type $I_2$. Its component quotient is $\mathbf Z/2\mathbf Z$, and

$$
E_q(\mathbf Q_5)\cong\mathbf Q_5^\times/25^{\mathbf Z}. \tag{12.2}
$$

The class of $5$ has order two because $5^2=q$. Together with the class of $-1$, it exhibits the two independent rational points in the split exact sequence for $E_q[2]$: here $q$ is a square, so the mod-$2$ extension splits.

For $\ell=3$, inertia acts by

$$
\begin{pmatrix}1&2t_3\\0&1\end{pmatrix}.
$$

Since $3\nmid2$, the residual representation remains ramified and has conductor exponent one.

### 12.2 Its nonsplit quadratic twist

The unit $2\in\mathbf Z_5^\times$ has nonsquare residue. Twist the preceding curve by the unramified quadratic character attached to $\mathbf Q_5(\sqrt2)/\mathbf Q_5$. After completing the square, equation (6.5) gives a concrete model.

The twist has the same $j$, the same parameter $q=25$, and the same minimal discriminant exponent $2$, but its tangent directions are conjugate over $\mathbf F_{25}$. It has nonsplit multiplicative reduction. Since $m$ is even, (6.9) gives component quotient of order $2$; had $m$ been odd, that quotient would have been trivial.

For every odd $\ell\ne5$, its representation has semisimplification

$$
(\eta\chi_\ell)\oplus\eta.
$$

On inertia this twist is invisible because $\eta$ is unramified. On an arithmetic Frobenius it changes both diagonal signs. Thus splitness is detected by Frobenius descent, not by the unipotent inertia operator.

### 12.3 An equal-characteristic split example

Let

$$
K=\mathbf F_7((t)),\qquad q=t^3(1+t).
$$

Then $m=3$. The integral power-series definitions are valid in characteristic $7$. Their leading terms give

$$
a_4=-5q+O(q^2)=2q+O(q^2),
\qquad
a_6=-q+O(q^2). \tag{12.3}
$$

The product formula yields

$$
\Delta=q(1-q)^{24}(1-q^2)^{24}\cdots,
\qquad v_t(\Delta)=3. \tag{12.4}
$$

Thus $E_q$ has split type $I_3$ and

$$
E_q(K)\cong K^\times/q^{\mathbf Z},
\qquad E_q(K)/E_0(K)\cong\mathbf Z/3\mathbf Z. \tag{12.5}
$$

Notice that $q$ is not a cube in $K$: although its valuation is divisible by $3$, its unit $1+t$ need not have a cube root because $3$ is prime to $7$—in this particular case it actually does, by Hensel lifting, since the residue $1$ is a cube and $3$ is a unit. Hence $q=t^3(1+t)$ is a cube after all. Replacing $1+t$ by a unit with noncube residue, such as $3+t$, removes the cube root. This comparison isolates the residue-unit obstruction from the valuation obstruction.

For every $\ell\ne7$, the Tate module is two-dimensional and inertia has the unipotent form with coefficient $3$. There is no analogous rank-two $7$-adic Tate module built from geometric torsion points.

### 12.4 An equal-characteristic nonsplit example

In $\mathbf F_7$, the element $3$ is a nonsquare. Twist the curve with parameter $q=t^3(1+t)$ by the unramified quadratic extension

$$
\mathbf F_{49}((t))/\mathbf F_7((t)).
$$

The resulting curve has nonsplit type $I_3$. Geometrically its component group is $\mathbf Z/3\mathbf Z$, with Frobenius acting by $a\mapsto-a$. The only fixed class is $0$, so

$$
E(K)/E_0(K)=0. \tag{12.6}
$$

Its identity-component reduction is the norm-one group

$$
\ker\bigl(\mathbf F_{49}^\times\to\mathbf F_7^\times\bigr),
$$

which has order $8$, rather than $|\mathbf F_7^\times|=6$. This gives a concrete numerical distinction between the split and nonsplit tori even though their curves have the same $j$ and minimal discriminant exponent.

### 12.5 A counterexample about residual splitting

Let $K=\mathbf Q_7$, $\ell=3$, and

$$
q=2\cdot7^3.
$$

Then $m=3$, so (10.8) shows that $E_q[3]$ is unramified on inertia. Nevertheless $q$ is not a cube in $K$: its residue unit $2$ is not a cube in $\mathbf F_7^\times$, whose cubes are $1$ and $-1$. Hence the exact sequence

$$
0\to\mu_3\to E_q[3]\to\mathbf Z/3\mathbf Z\to0
$$

does not split.

The remaining extension class is unramified and is detected by Frobenius. This example separates three statements that are often mistakenly conflated:

$$
\ell\mid v(q),\qquad
\overline\rho|_{I_K}=1,
\qquad
q\in(K^\times)^\ell.
$$

The first implies the second at a multiplicative prime away from $\ell$'s residue characteristic, but neither implies the third without a unit calculation.

### 12.6 A coefficient-prime boundary example

Let $K=\mathbf Q_5$ and compare

$$
q_1=5^5\cdot2,
\qquad
q_2=5^4\cdot2. \tag{12.7}
$$

Both Tate curves have split multiplicative reduction, and both $5$-adic representations have the triangular form

$$
\begin{pmatrix}\chi_5&c_{q_i,5}\\0&1\end{pmatrix}.
$$

For $q_1$, the valuation is divisible by $5$. Modulo fifth powers its class is represented by the unit $2$, because $q_1/5^5=2$. The construction of Section 11.3 therefore supplies a finite flat model of $E_{q_1}[5]$ over $\mathbf Z_5$. The residual representation is not unramified: its cyclotomic diagonal character is nontrivial on inertia. Finite flatness, not unramifiedness, is the relevant conclusion.

For $q_2$, the valuation class is $4$ modulo $5$, so no unit represents $[q_2]$ in $\mathbf Q_5^\times/(\mathbf Q_5^\times)^5$. Since $5$ is odd and the base is unramified, the distinguished-line argument applies, and $E_{q_2}[5]$ is not finite flat over $\mathbf Z_5$.

The unit $2$ need not be a fifth power. That is irrelevant: a finite flat extension may be non-split. This example separates once more the three levels of information:

$$
\begin{array}{c|c}
q\in(K^\times)^5&\text{the generic extension splits},\\
v(q)\equiv0\pmod5&\text{the canonical class is finite flat},\\
\overline\rho|_{I_K}=1&\text{not expected when the coefficient prime is }5.
\end{array}
$$

## 13. The local representation at a multiplicative place

### 13.1 A compact structural dictionary

Let $E/K$ have multiplicative reduction, let $\eta$ be its unramified splitting character, and let

$$
q=Q(j(E)^{-1}),\qquad m=v(q)>0.
$$

All principal local invariants can now be read from this pair $(q,\eta)$:

$$
\begin{array}{c|c}
\text{geometric or arithmetic datum}&\text{Tate description}\\ \hline
\text{splitness}&\eta=1\text{ or }\eta\ne1\\
\text{minimal discriminant exponent}&v(\Delta_{\min})=m\\
\text{$j$-valuation}&v(j)=-m\\
\text{geometric components}&\mathbf Z/m\mathbf Z\\
\text{split local points}&K^\times/q^{\mathbf Z}\\
\text{finite torsion extension}&0\to\mu_n\otimes\eta\to E[n]\to(\mathbf Z/n)\otimes\eta\to0\\
\text{extension class}&q\in K^\times/(K^\times)^n\\
\text{diagonal characters}&\eta\chi_n,\ \eta\\
\text{prime-to-$p$ inertia}&\begin{pmatrix}1&mt_\ell\\0&1\end{pmatrix}\\
\text{$\ell$-adic conductor, finite $k$, $\ell\ne p$}&1\\
\text{residual conductor, finite $k$, $\ell\ne p$}&1\text{ if }\ell\nmid m,\ 0\text{ if }\ell\mid m.
\end{array} \tag{13.1}
$$

Each row loses some information retained by the rows above it. The conductor remembers only that monodromy is nonzero. The integral inertia matrix remembers the $\ell$-adic divisibility of $m$. The finite extension class remembers $q$ modulo powers. The full parameter remembers the analytic curve. This hierarchy explains both the power and the limitations of local representation data.

For a split curve and a prime $\ell\ne\operatorname{char}K$, the residual representation is always reducible:

$$
\overline\rho_{E,\ell}\sim
\begin{pmatrix}
\overline\chi_\ell&*\\0&1
\end{pmatrix}. \tag{13.2}
$$

For a nonsplit curve it is

$$
\overline\rho_{E,\ell}\sim
\begin{pmatrix}
\overline\eta\,\overline\chi_\ell&*\\0&\overline\eta
\end{pmatrix}. \tag{13.3}
$$

The star vanishes precisely when $q$ is an $\ell$th power in $K$. Its restriction to inertia vanishes under the weaker condition $\ell\mid m$. These two criteria are among the most frequently used consequences of Tate uniformization.

### 13.2 Precise formulas for semistable modularity

Fix a finite residue field of cardinality $Q$, a prime $\ell\ne p$, and the covariant Tate-module convention. For an elliptic curve with multiplicative reduction, the complete reusable formula is

$$
\rho_{E,\ell}(\sigma)=
\eta(\sigma)
\begin{pmatrix}
\chi_\ell(\sigma)&c_{q,\ell}(\sigma)\\
0&1
\end{pmatrix}, \tag{13.4}
$$

where

$$
q=Q_{\!j}(j(E)^{-1}),
\qquad
c_{q,\ell}(\sigma\tau)
=c_{q,\ell}(\sigma)+\chi_\ell(\sigma)c_{q,\ell}(\tau). \tag{13.5}
$$

Here $Q_{\!j}$ denotes the inverse $j$-series from (2.9), not the residue cardinality $Q$. The splitting character $\eta$ is unramified, and

$$
m=v(q)=v(\Delta_{\min})=-v(j(E)). \tag{13.6}
$$

With the tame character normalized by (10.2),

$$
\rho_{E,\ell}(\sigma)=
\begin{pmatrix}1&m t_\ell(\sigma)\\0&1\end{pmatrix}
\quad(\sigma\in I_K), \tag{13.7}
$$

while for an arithmetic Frobenius lift $F$,

$$
\rho_{E,\ell}(F)=
\eta(F)
\begin{pmatrix}Q&c_{q,\ell}(F)\\0&1\end{pmatrix}. \tag{13.8}
$$

The determinant and trace are therefore

$$
\det\rho_{E,\ell}=\chi_\ell,
\qquad
\operatorname{tr}\rho_{E,\ell}(\sigma)
=\eta(\sigma)(\chi_\ell(\sigma)+1). \tag{13.9}
$$

The trace formula is independent of the Kummer entry, but the representation is not: monodromy and residual level lowering live entirely in that entry. The rational monodromy operator has rank one, the Swan conductor is zero, and

$$
a(V_\ell(E))=1. \tag{13.10}
$$

After reduction modulo $\ell$,

$$
\overline\rho_{E,\ell}|_{I_K}=1
\quad\Longleftrightarrow\quad
\ell\mid m, \tag{13.11}
$$

but

$$
\overline\rho_{E,\ell}\text{ splits over }G_K
\quad\Longleftrightarrow\quad
q\in(K^\times)^\ell. \tag{13.12}
$$

Thus the residual conductor drops from one to zero under the numerical divisibility in (13.11), even when an unramified nonsplit extension remains. This is the exact local statement used to remove a multiplicative prime from a residual conductor.

At the coefficient prime $p$ in mixed characteristic, retain (13.4) with $\ell=p$ but discard (13.7), (13.10), and (13.11). The cyclotomic character is ramified and the unit part of the Kummer class matters on inertia. In the unramified odd-prime setting, the replacement is

$$
E[p]\text{ is finite flat}
\quad\Longleftrightarrow\quad
p\mid m. \tag{13.13}
$$

In particular the coefficient-prime representation is ordinary in the elementary triangular sense: it has the stable line $\mathbf Z_p(1)\otimes\eta$, and its quotient $\mathbf Z_p\otimes\eta$ is unramified. Its residual extension satisfies the finite-flat local condition precisely under (13.13). For $p=2$, only the canonical-extension direction is supplied here, as explained in Section 11.5. These qualifications are part of the formula, not peripheral cautions.

Finally, changing from covariant Tate modules to the dual representation inverts the diagonal characters, and changing arithmetic to geometric Frobenius replaces $Q$ by $Q^{-1}$. A comparison theorem must make those two convention changes explicitly; otherwise a correct special representation can appear to have the wrong determinant or Frobenius eigenvalues.

### 13.3 Exactly what is passed to the next volume

This book has derived the torsion and Tate-module structure in the special setting where an elliptic curve is multiplicatively uniformized. The next volume develops torsion and Tate modules for arbitrary elliptic curves: separability of multiplication maps, pairings, functoriality under isogenies, reduction at good places, and determinant arguments independent of a Tate parameter.

The interface is precise. From the present book one may carry forward the exact sequences

$$
0\to\mu_n\to E_q[n]\to\mathbf Z/n\to0
$$

and

$$
0\to\mathbf Z_\ell(1)\otimes\eta
\to T_\ell(E)\to\mathbf Z_\ell\otimes\eta\to0,
$$

the Kummer class of $q$, the explicit Galois matrices, and the inertia and conductor calculations at a multiplicative place. One should not infer from these special triangular matrices that torsion of every elliptic curve is reducible. Reducibility here comes from the canonical multiplicative subgroup $\mu_n$ of a Tate curve.

Nor should the cyclotomic determinant proved here by a triangular calculation replace its general explanation. Uniformization exhibits the determinant in one important local case. The general theorem identifies it through the alternating pairing on torsion and remains valid without multiplicative reduction.

### 13.4 Conclusion

A nodal special fiber is not merely a damaged elliptic curve. Its two branches reveal a torus, and completeness allows that torus to be lifted and wound around a single period. The resulting quotient $\overline K^\times/q^{\mathbf Z}$ recovers the entire elliptic curve. Its equation has integral Lambert-series coefficients, its discriminant is the product $q\prod(1-q^n)^{24}$, and its minimal discriminant exponent is exactly the valuation of the period.

The same quotient makes the arithmetic transparent. Valuation modulo $v(q)$ labels components; units reduce to the smooth multiplicative group; roots of unity and roots of $q$ generate torsion. Galois acts triangularly, with the cyclotomic character on the multiplicative line and the Kummer cocycle of $q$ in the extension entry. Away from the residue characteristic, inertia becomes a single nontrivial unipotent direction, giving conductor exponent one and explaining why divisibility of $v(\Delta_{\min})$ can erase ramification after residual reduction.

At the coefficient prime, the same divisibility has a different meaning. It moves the Kummer class of $q$ into the unit group and thereby permits the canonical residual extension to spread over the valuation ring as a finite flat group. The odd unramified case turns this into an exact criterion for the residual representation; the dyadic case requires a separate uniqueness analysis. Keeping this boundary explicit is essential to the local conditions used in semistable modularity.

Split and nonsplit reduction differ by one unramified quadratic sign. That sign exchanges the branches, inverts the multiplicative coordinate, twists both diagonal characters, and changes rational components without altering the discriminant exponent or inertia monodromy. Thus the pair $(q,\eta)$ is the complete local language of multiplicative degeneration: $q$ measures and uniformizes the degeneration, while $\eta$ records its descent. Through that pair, integral geometry, nonarchimedean analysis, local points, and Galois representations become one coherent mathematical object.
