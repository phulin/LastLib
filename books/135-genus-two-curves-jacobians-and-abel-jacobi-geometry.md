# Genus-Two Curves, Jacobians, and Abel--Jacobi Geometry

## Contents

1. [Why genus two is the first genuinely new case](#1-why-genus-two-is-the-first-genuinely-new-case)
   - [The meeting point of curves and abelian surfaces](#11-the-meeting-point-of-curves-and-abelian-surfaces)
   - [Standing hypotheses and conventions](#12-standing-hypotheses-and-conventions)
   - [The geometric and arithmetic route](#13-the-geometric-and-arithmetic-route)
2. [The canonical double cover](#2-the-canonical-double-cover)
   - [Riemann--Roch forces hyperellipticity](#21-riemann--roch-forces-hyperellipticity)
   - [The hyperelliptic involution and its uniqueness](#22-the-hyperelliptic-involution-and-its-uniqueness)
   - [Ramification and Weierstrass points](#23-ramification-and-weierstrass-points)
   - [Canonical divisors and conjugate pairs](#24-canonical-divisors-and-conjugate-pairs)
3. [Equations and smooth projective models](#3-equations-and-smooth-projective-models)
   - [Affine equations in characteristic different from two](#31-affine-equations-in-characteristic-different-from-two)
   - [Odd and even degree at infinity](#32-odd-and-even-degree-at-infinity)
   - [Coordinate changes and twists](#33-coordinate-changes-and-twists)
   - [What changes in characteristic two](#34-what-changes-in-characteristic-two)
4. [Divisors in genus two](#4-divisors-in-genus-two)
   - [Degree, linear systems, and specialness](#41-degree-linear-systems-and-specialness)
   - [Effective divisors of degree two](#42-effective-divisors-of-degree-two)
   - [Reduction to degree at most two](#43-reduction-to-degree-at-most-two)
   - [Uniqueness and the exceptional canonical class](#44-uniqueness-and-the-exceptional-canonical-class)
5. [The Jacobian and its theta divisor](#5-the-jacobian-and-its-theta-divisor)
   - [The degree-zero Picard surface](#51-the-degree-zero-picard-surface)
   - [Theta in genus two](#52-theta-in-genus-two)
   - [The principal polarization](#53-the-principal-polarization)
   - [Intersection numbers and translates](#54-intersection-numbers-and-translates)
6. [The Abel--Jacobi curve](#6-the-abel--jacobi-curve)
   - [Construction and change of base point](#61-construction-and-change-of-base-point)
   - [Injectivity on points](#62-injectivity-on-points)
   - [The differential and closed immersion](#63-the-differential-and-closed-immersion)
   - [The curve as the theta divisor](#64-the-curve-as-the-theta-divisor)
7. [The symmetric square](#7-the-symmetric-square)
   - [Degree-two divisors as a smooth surface](#71-degree-two-divisors-as-a-smooth-surface)
   - [Fibers of the degree-two Abel map](#72-fibers-of-the-degree-two-abel-map)
   - [The blowup theorem](#73-the-blowup-theorem)
   - [Rational points on the symmetric square](#74-rational-points-on-the-symmetric-square)
8. [Addition, subtraction, and incidence](#8-addition-subtraction-and-incidence)
   - [Sums of two points](#81-sums-of-two-points)
   - [Differences and intersections of theta translates](#82-differences-and-intersections-of-theta-translates)
   - [The diagonal and the canonical direction](#83-the-diagonal-and-the-canonical-direction)
   - [Maps to elliptic curves and split Jacobians](#84-maps-to-elliptic-curves-and-split-jacobians)
9. [Finite fields and exact geometric counts](#9-finite-fields-and-exact-geometric-counts)
   - [Frobenius on a genus-two Jacobian](#91-frobenius-on-a-genus-two-jacobian)
   - [Point bounds for the curve and Jacobian](#92-point-bounds-for-the-curve-and-jacobian)
   - [The symmetric-square count](#93-the-symmetric-square-count)
   - [What finite-field counts can certify](#94-what-finite-field-counts-can-certify)
10. [Models and reduction over discrete valuation rings](#10-models-and-reduction-over-discrete-valuation-rings)
    - [Good hyperelliptic models](#101-good-hyperelliptic-models)
    - [Specialization of points and divisor classes](#102-specialization-of-points-and-divisor-classes)
    - [Prime-to-residue-characteristic torsion](#103-prime-to-residue-characteristic-torsion)
    - [Semistable fibers and graph corrections](#104-semistable-fibers-and-graph-corrections)

11. [Local fields and residue constraints](#11-local-fields-and-residue-constraints)
    - [Integral points from properness](#111-integral-points-from-properness)
    - [Residue disks and the Abel map](#112-residue-disks-and-the-abel-map)
    - [Local divisor classes](#113-local-divisor-classes)
    - [Compatibility across extensions](#114-compatibility-across-extensions)

12. [Number fields, Mordell--Weil groups, and heights](#12-number-fields-mordell--weil-groups-and-heights)
    - [The Jacobian as a finitely generated group](#121-the-jacobian-as-a-finitely-generated-group)
    - [The theta height](#122-the-theta-height)
    - [The embedded curve is not a subgroup](#123-the-embedded-curve-is-not-a-subgroup)
    - [Reduction maps as arithmetic interfaces](#124-reduction-maps-as-arithmetic-interfaces)

13. [Rational-point geometry in genus two](#13-rational-point-geometry-in-genus-two)
    - [Degree one versus degree two information](#131-degree-one-versus-degree-two-information)
    - [Known classes and unknown points](#132-known-classes-and-unknown-points)
    - [Finite quotients and surviving residue classes](#133-finite-quotients-and-surviving-residue-classes)
    - [Completeness criteria and their boundaries](#134-completeness-criteria-and-their-boundaries)

14. [The modular genus-two range](#14-the-modular-genus-two-range)
    - [From a modular point to a divisor class](#141-from-a-modular-point-to-a-divisor-class)
    - [Cusps, degeneracy points, and base divisors](#142-cusps-degeneracy-points-and-base-divisors)
    - [The range needed for $X_1(13)$](#143-the-range-needed-for-x_113)
    - [The range needed for the mixed-seven curve](#144-the-range-needed-for-the-mixed-seven-curve)

15. [A reusable genus-two package](#15-a-reusable-genus-two-package)
    - [Hypothesis ledger](#151-hypothesis-ledger)
    - [Geometric theorem package](#152-geometric-theorem-package)
    - [Arithmetic theorem package](#153-arithmetic-theorem-package)
    - [Conclusion](#154-conclusion)

## 1. Why genus two is the first genuinely new case

This chapter identifies the structural coincidences that make genus two tractable and fixes the hypotheses under which they will be used. Its purpose is to prevent the later explicit geometry from appearing as a collection of isolated tricks: canonical divisors, theta divisors, symmetric squares, reduction, and heights will all be parts of one route from a curve point to an arithmetic class.

### 1.1 The meeting point of curves and abelian surfaces

Genus two is the first place where the arithmetic of a curve and the arithmetic of its Jacobian are visibly different. A pointed genus-one curve is its own Jacobian. Its rational points therefore form a group. A genus-two curve instead embeds in a two-dimensional abelian variety. Addition takes place in the ambient surface, while the curve occupies a distinguished divisor inside it. This mismatch is the source of both the power and the delicacy of the method.

Three exceptional features make genus two unusually concrete. First, every smooth proper genus-two curve is hyperelliptic: its canonical linear system gives a degree-two map to a genus-zero curve. Second, every degree-zero divisor class can be represented by the difference of an effective divisor of degree at most two and a fixed divisor. Third, the symmetric square of the curve is almost its Jacobian; exactly one projective line must be contracted. These facts turn questions about rational points into geometry on a surface without making the curve itself into a group.

It helps to place this transition beside the two lower genera. A smooth pointed genus-zero curve is $\mathbf P^1$; rational functions and parametrization govern its points, while its degree-zero Picard variety is trivial. A smooth pointed genus-one curve is an elliptic curve; the degree-one Abel map is an isomorphism, and secant geometry becomes a group law on the curve itself. In genus two, the Abel map remains an embedding but its target gains one dimension. The missing dimension is not an inconvenience to be discarded. It is what permits two points to add freely and makes the symmetric square birational to an abelian surface.

There is also a sharp numerical coincidence. A theta divisor on a two-dimensional principally polarized abelian variety has self-intersection two. A genus-two curve has canonical degree two. The equality of these two numbers is reflected repeatedly: two theta translates meet twice, a generic Jacobian class is a sum of two curve points, and the only nonunique degree-two representative is a canonical fiber. The book will prove these statements independently before assembling them into one picture.

The intended applications begin with modular curves. A modular interpretation produces a point, a cusp supplies a base point, and the Abel--Jacobi map produces a rational divisor class. Reduction then constrains that class in finite groups. The present book establishes the geometric and arithmetic interfaces needed for this passage. Exact formulas for group addition, descent computations, and exhaustive sieves require further input and are not assumed here.

### 1.2 Standing hypotheses and conventions

Unless a statement says otherwise, $k$ is a field, $C/k$ is a smooth, proper, geometrically connected curve of genus $2$, and

$$
J=\operatorname{Pic}^0_{C/k}
$$

is its Jacobian. A geometric point means a point over an algebraic closure $\bar k$. Divisors are Cartier divisors; on a smooth curve these agree with Weil divisors. Linear equivalence is written $D\sim E$, and the class of a degree-zero divisor $D$ is written $[D]$.

The canonical divisor class is denoted $K_C$. Since $g=2$,

$$
\deg K_C=2,\qquad h^0(C,K_C)=2.
$$

When a rational point $b\in C(k)$ is chosen, the Abel--Jacobi map is

$$
j_b:C\longrightarrow J,\qquad P\longmapsto[P-b].
$$

If $D$ is a closed point, its degree includes the residue degree. Thus a $k$-rational effective divisor of degree two need not be the sum of two $k$-rational points: it may be one closed point of degree two. This distinction is essential in arithmetic applications.

Explicit equations $y^2=f(x)$ are used only when $\operatorname{char}k\ne2$. Intrinsic statements about the canonical map, divisors, Jacobians, and theta remain valid in every characteristic. A local field means a field complete for a discrete valuation with finite residue field. A global field in the height chapters means a number field, because the height and Mordell--Weil package used there has been established in that setting.

### 1.3 The geometric and arithmetic route

The argument develops in four layers. The canonical linear system first produces the double cover and its involution. Riemann--Roch then classifies the small-degree linear systems that control divisor representatives. Picard theory packages these classes into the principally polarized surface $(J,\Theta)$, and the symmetric square explains nearly every point of that surface by an effective divisor of degree two.

Arithmetic enters only after this geometry is fixed. Over finite fields, Frobenius bounds and the blowup description give point counts. Over a discrete valuation ring, properness specializes points and the abelian scheme specializes divisor classes. Over a number field, the theta polarization supplies a canonical height and Mordell--Weil supplies finite generation. Combining these structures gives a precise interface:

$$
C(K)\xrightarrow{j_b}J(K)
\longrightarrow J(k_v)
$$

at every place of good reduction $v$. The first arrow is geometric and injective; the second is a group homomorphism with finite target. Neither arrow alone determines $C(K)$. Their compatibility is what later exact arithmetic exploits.

## 2. The canonical double cover

Every later exceptional phenomenon comes from the canonical pencil, so the first geometric task is to construct that pencil intrinsically. This chapter proves that it is a degree-two cover, identifies its symmetry and ramification, and extracts the divisor relation that will drive genus-two reduction.

### 2.1 Riemann--Roch forces hyperellipticity

The canonical bundle is the smallest natural line bundle large enough to see a genus-two curve. Its two independent sections define a pencil. The decisive question is whether that pencil has a base point and what degree its associated map has.

**Theorem 2.1 (canonical double cover).** The complete canonical linear system $|K_C|$ is base-point free and defines a finite morphism

$$
\pi:C\longrightarrow
\mathbf P(H^0(C,\omega_C)^\vee)\simeq\mathbf P^1_k
$$

of degree $2$.

**Proof.** Suppose a geometric point $P$ were a base point. Then

$$
h^0(K_C-P)=h^0(K_C)=2.
$$

Riemann--Roch applied to $P$ gives

$$
h^0(P)-h^0(K_C-P)=\deg(P)+1-g=0,
$$

so $h^0(P)=2$. A nonconstant section of $\mathcal O_C(P)$ would be a rational function with at most one simple pole. It would define a degree-one map $C_{\bar k}\to\mathbf P^1$, forcing $C_{\bar k}\simeq\mathbf P^1$, contrary to genus two. Thus there is no base point.

Two independent canonical sections therefore define a morphism to the projectivization of the dual of their two-dimensional $k$-vector space. This target is a split projective line over $k$, without any rational-point hypothesis on $C$. Because $\pi^*\mathcal O(1)\simeq\omega_C$, the degree formula gives

$$
\deg\pi\cdot\deg\mathcal O(1)=\deg K_C=2.
$$

Since $\deg\mathcal O(1)=1$, one gets $\deg\pi=2$. Finiteness follows because a nonconstant morphism between proper integral curves is finite. $\square$

### 2.2 The hyperelliptic involution and its uniqueness

A separable degree-two cover has a symmetry exchanging the two points of a general fiber. The intrinsic canonical construction shows that this deck transformation belongs to the curve, not to a chosen equation; the first issue is to exclude inseparability in characteristic two.

**Proposition 2.2.** The canonical map is generically separable. Consequently there is a unique nontrivial automorphism

$$
\iota:C\longrightarrow C
$$

over $\mathbf P^1$, and $C/\langle\iota\rangle=\mathbf P^1$. Every automorphism of $C$ commutes with $\iota$ and descends to an automorphism of $\mathbf P^1$ preserving the branch divisor.

**Proof.** Only characteristic two needs a separability argument. After extending the ground field to an algebraic closure, suppose the degree-two canonical map were purely inseparable. If $K=\bar k(C)$ and $F=\bar k(\mathbf P^1)$, then $K^2\subseteq F$. Since $\bar k$ is perfect and $K$ has transcendence degree one,

$$
[K:K^2]=2=[K:F],
$$

so $F=K^2$. Frobenius identifies $K$ with $K^2$ after twisting constants; in geometric terms, the purely inseparable map would be the relative Frobenius of $C$ followed by an isomorphism from its Frobenius twist to $\mathbf P^1$. Frobenius twisting preserves the genus of a smooth proper curve over a perfect field, contradicting $g(C)=2$. Thus the canonical map is separable.

The separable quadratic extension $k(C)/k(\mathbf P^1)$ now has a unique nontrivial field automorphism. Normality of the smooth curve extends it to an automorphism $\iota$ of $C$. Any automorphism of $C$ acts linearly on $H^0(C,\omega_C)$ and therefore carries fibers of the canonical map to fibers. It conjugates the unique nontrivial automorphism over the generic point to itself, so it commutes with $\iota$ and descends to $\mathbf P^1$. A descended automorphism must preserve the ramification, hence the branch divisor. $\square$

In characteristic two the separable double cover is Artin--Schreier in nature, and its ramification can be wild. What fails there is the sign-change equation and the count of six distinct ramification points, not the existence of the canonical involution.

The uniqueness has a useful consequence. If a genus-two curve is presented in two apparently different hyperelliptic forms, their degree-two maps differ only by an automorphism of the genus-zero target. Thus coordinate changes on the $x$-line account for every change of hyperelliptic coordinate.

The branch divisor also recovers the curve when $2$ is invertible. Let $B\subset\mathbf P^1_{\bar k}$ be the reduced divisor of six branch points. A quadratic cover with branch $B$ is obtained from a line bundle $M$ with

$$
M^{\otimes2}\simeq\mathcal O_{\mathbf P^1}(B).
$$

Since $\deg B=6$, one has $M\simeq\mathcal O(3)$ over $\bar k$. The cover is

$$
\operatorname{Spec}_{\mathbf P^1}
\bigl(\mathcal O\oplus M^{-1}\bigr),
$$

with multiplication on $M^{-1}\otimes M^{-1}$ specified by the branch section of $M^{\otimes2}$. Two choices differing by a nonzero scalar give quadratic twists; after algebraic closure that scalar is a square. Consequently an unordered configuration of six distinct points of $\mathbf P^1$, modulo $\operatorname{PGL}_2$, determines a geometric genus-two curve. Since configurations have dimension $6-3=3$, this also explains the three-dimensional moduli of genus-two curves.

### 2.3 Ramification and Weierstrass points

Riemann--Hurwitz determines the ramification of the now-proved separable canonical cover without coordinates. Let $R_\pi$ be its different divisor, also called the ramification divisor. Since the target has genus zero,

$$
K_C\sim\pi^*K_{\mathbf P^1}+R_\pi.
$$

Taking degrees gives

$$
2=2(-2)+\deg R_\pi,\qquad \deg R_\pi=6. \tag{2.1}
$$

The geometric ramification points are the **Weierstrass points**. When the characteristic is not two, ramification is tame and (2.1) gives six distinct geometric Weierstrass points. Their images form a reduced branch divisor of degree six on $\mathbf P^1$.

At a Weierstrass point $W$, the fiber is $2W$. Since a fiber of the canonical map is a canonical divisor,

$$
2W\sim K_C. \tag{2.2}
$$

Conversely, if $2P\sim K_C$, then $2P$ belongs to the canonical pencil and is a nonreduced fiber, so $P$ is ramified. Thus (2.2) characterizes Weierstrass points intrinsically.

Wild ramification changes the counting language in characteristic two: the different, rather than the number of distinct ramification points, has degree six. It is therefore unsafe to assert that every genus-two curve in characteristic two has six distinct Weierstrass points. The divisor-theoretic statements below are phrased through scheme-theoretic canonical fibers and remain valid in every characteristic.

### 2.4 Canonical divisors and conjugate pairs

For every geometric point $P$, write $\bar P=\iota(P)$. The fiber through $P$ is

$$
P+\bar P\sim K_C. \tag{2.3}
$$

If $P$ is Weierstrass, this means $2P\sim K_C$. If it is not, the fiber has two distinct points. Equation (2.3) is the elementary relation behind all genus-two divisor reduction.

It also describes the action of the involution on the Jacobian. Fix $b\in C(k)$. From

$$
P+\bar P\sim b+\bar b
$$

one obtains

$$
j_b(\bar P)=-j_b(P)+[\bar b-b]. \tag{2.4}
$$

If $b$ is Weierstrass, then $\bar b=b$ and the formula simplifies to

$$
j_b\circ\iota=[-1]\circ j_b. \tag{2.5}
$$

This is why a rational Weierstrass base point is especially convenient. A non-Weierstrass base point is equally valid, but the involution becomes inversion followed by a fixed translation.

## 3. Equations and smooth projective models

Intrinsic geometry becomes computational only after the canonical target is given a coordinate. This chapter explains exactly when the resulting equation is smooth and genus two, what its affine form omits at infinity, and why characteristic two requires a genuinely different equation rather than a cosmetic change of signs.

### 3.1 Affine equations in characteristic different from two

Suppose $\operatorname{char}k\ne2$. Choose an affine coordinate $x$ away from one point of the canonical target $\mathbf P^1_k$. A separable quadratic extension of $k(x)$ can be written

$$
k(C)=k(x,y),\qquad y^2=f(x), \tag{3.1}
$$

after multiplying by a square and clearing even valuations. For a genus-two curve one may arrange that $f\in k[x]$ is squarefree of degree $5$ or $6$.

**Proposition 3.1.** If $f\in k[x]$ is squarefree of degree $5$ or $6$, the smooth projective model of $y^2=f(x)$ has genus $2$. Its canonical map is $x$, and its involution is $(x,y)\mapsto(x,-y)$.

**Proof.** Squarefreeness implies that the affine curve is smooth: a singular point would satisfy

$$
y^2-f(x)=0,\qquad 2y=0,\qquad f'(x)=0,

$$

and hence $y=0$ and $f(x)=f'(x)=0$. The map $x$ has degree two. It is branched at each root of $f$. If $\deg f=5$, it is also branched at infinity; if $\deg f=6$, it is unramified at infinity. In either case there are six geometric branch points. Riemann--Hurwitz gives

$$
2g(C)-2=2(-2)+6=2,
$$

so $g(C)=2$. The unique nontrivial deck transformation changes the sign of $y$. Since the canonical degree-two map is unique, it is the $x$-map. $\square$

Squarefreeness is not cosmetic. If $f$ has a repeated root, the affine equation is singular there. Normalizing may lower the genus because a repeated branch point has disappeared from the branch divisor.

### 3.2 Odd and even degree at infinity

The affine equation does not by itself specify the points at infinity. Their behavior distinguishes degree five from degree six.

For $\deg f=5$, there is one geometric point $\infty$ above infinity, and it is ramified. Its valuations satisfy

$$
\operatorname{ord}_\infty(x)=-2,\qquad
\operatorname{ord}_\infty(y)=-5. \tag{3.2}
$$

Thus $\infty$ is rational whenever the equation is defined over $k$, it is Weierstrass, and

$$
K_C\sim2\infty. \tag{3.3}
$$

For $\deg f=6$ with leading coefficient $a$, there are two geometric points at infinity. They are defined over $k(\sqrt a)$ and are exchanged by the involution. They are individually $k$-rational exactly when $a$ is a square in $k$. Their sum is a rational canonical divisor even if neither is rational.

Regular differentials make these assertions visible. In either degree-five or degree-six form,

$$
\omega_1=\frac{dx}{y},\qquad
\omega_2=\frac{x\,dx}{y} \tag{3.4}
$$

form a basis of $H^0(C,\omega_C)$. Direct valuation at infinity shows that both are regular. Their ratio is $x$, so the canonical map is indeed the hyperelliptic coordinate.

### 3.3 Coordinate changes and twists

An automorphism of the target has the form

$$
x=\frac{aX+b}{cX+d},\qquad ad-bc\ne0.
$$

For a sextic model, clearing denominators transforms (3.1) to

$$
Y^2=(cX+d)^6f\!\left(\frac{aX+b}{cX+d}\right),
$$

after replacing $y$ by $Y/(cX+d)^3$. Multiplying the right side by a square gives an isomorphic curve. Multiplying by $d\in k^\times$ gives the quadratic twist

$$
C^{(d)}:dy^2=f(x).
$$

The twist is isomorphic to $C$ over $k(\sqrt d)$ but need not be isomorphic over $k$. Its branch divisor and geometric genus are unchanged, while its rational points and Jacobian arithmetic can change drastically.

These transformations explain why coefficients alone are not geometric invariants. The branch divisor on $\mathbf P^1$, modulo projective transformations, determines the geometric curve in characteristic different from two. A $k$-form additionally remembers descent and twisting data.

### 3.4 What changes in characteristic two

Completing the hypothesis ledger requires a separate description in characteristic two. Proposition 2.2 shows that the canonical quadratic extension is separable, so after choosing a hyperelliptic coordinate it is written

$$
y^2+h(x)y=f(x), \tag{3.5}
$$

with $h\ne0$. The involution is

$$
(x,y)\longmapsto(x,y+h(x)).
$$

The smoothness test is not squarefreeness of $f$. For the affine equation

$$
F=y^2+h(x)y-f(x),
$$

a singular geometric point must satisfy

$$
F=0,\qquad h(x)=0,\qquad h'(x)y-f'(x)=0. \tag{3.6}
$$

Behavior at infinity must also be checked in a proper model. The degree and pole conditions on $f/h^2$ determine the different and hence the genus.

The intrinsic theory in Chapters 4--8 does not divide by two and does not rely on the sign-change formula. Whenever an explicit affine calculation is invoked, the standing assumption $\operatorname{char}k\ne2$ will be restated. This separation prevents formulas such as $y\mapsto-y$ or a sextic discriminant from being used where they do not apply.

## 4. Divisors in genus two

The Jacobian remembers divisor classes, while rational-point questions begin with actual divisors. The bridge is a sharp classification of linear systems of degree at most two. This chapter derives that classification from Riemann--Roch and isolates the single canonical class in which an effective representative is not unique.

### 4.1 Degree, linear systems, and specialness

Riemann--Roch specializes in genus two to

$$
\ell(D)-\ell(K_C-D)=\deg D-1. \tag{4.1}
$$

This one equation nearly classifies every low-degree divisor. A divisor of negative degree has no nonzero section. A degree-zero divisor has a section exactly when it is linearly equivalent to zero. For degree at least three, $K_C-D$ has negative degree, so

$$
\ell(D)=\deg D-1\qquad(\deg D\ge3). \tag{4.2}
$$

Degree one is rigid. If $D$ is effective of degree one, then $\ell(D)=1$. Otherwise a nonconstant function in $L(D)$ would define a degree-one map to $\mathbf P^1$. Degree two has exactly one exceptional class.

**Proposition 4.1.** Let $D$ be an effective geometric divisor of degree two. Then

$$
\ell(D)=
\begin{cases}
2,&D\sim K_C,\\
1,&D\not\sim K_C.
\end{cases} \tag{4.3}
$$

**Proof.** Formula (4.1) gives

$$
\ell(D)-\ell(K_C-D)=1.
$$

The divisor $K_C-D$ has degree zero. It has a section precisely when it is principal, equivalently when $D\sim K_C$. In that case its space of sections has dimension one and $\ell(D)=2$; otherwise it has no section and $\ell(D)=1$. $\square$

Thus every effective degree-two divisor outside the canonical pencil is the unique effective divisor in its linear-equivalence class.

### 4.2 Effective divisors of degree two

The canonical degree-two divisors are exactly the fibers of the hyperelliptic map.

**Proposition 4.2.** For an effective geometric divisor $D$ of degree two, the following are equivalent:

1. $D\sim K_C$;
2. $\ell(D)=2$;
3. $D=P+\iota(P)$ for some $P\in C(\bar k)$;
4. $D$ is a fiber of the canonical map.

**Proof.** The first two conditions are equivalent by Proposition 4.1. The complete linear system $|K_C|$ is precisely the pencil defining $\pi$. Its effective members are therefore its scheme-theoretic fibers, which are $P+\iota(P)$, including $2P$ at a ramification point. This proves all equivalences. $\square$

Over $k$, an effective divisor of degree two is a $k$-point of $C^{(2)}$. Geometrically it is either $P+Q$ with $P,Q\in C(k)$, twice a rational point, or $P+P^\sigma$ for a degree-two closed point. Rational canonical divisors exist even when $C(k)$ is empty: the canonical bundle and its two-dimensional space of sections are defined over $k$, and every $k$-line of nonzero sections has a $k$-rational zero divisor.

For an equation $y^2=f(x)$ over a field of characteristic different from two, these alternatives can be read from a quadratic polynomial. If

$$
u(x)=x^2-sx+p\in k[x]
$$

is separable and $v(x)$ has degree at most one with $u\mid f-v^2$, then the equations

$$
u(x)=0,\qquad y=v(x)
$$

define a rational effective divisor of degree two. It splits over $k$ exactly when the discriminant $s^2-4p$ is a square. If $u=(x-a)^2$, the divisibility condition alone does not decide whether the divisor is $2(a,v(a))$ or an infinitesimal tangent divisor; the first derivative condition encoded by divisibility to order two supplies that information. This example anticipates why exact divisor coordinates must retain both $u$ and $v$.

### 4.3 Reduction to degree at most two

Fix a rational point $b\in C(k)$. Before choosing polynomial coordinates, the useful first goal is a **small-degree presentation** of a divisor class, meaning an expression

$$
[D-rb],\qquad D\ge0,\quad r=\deg D\le2. \tag{4.4}
$$

When $b$ is Weierstrass, the relation $P+\iota(P)\sim2b$ permits direct cancellation of conjugate pairs and leads to the usual reduced-divisor notion. For a general base point, $P+\iota(P)\sim b+\iota(b)$ instead, so the normalization includes a fixed translation. The existence result needed here is simpler and does not claim a unique reduced presentation.

Existence follows directly from Riemann--Roch.

**Theorem 4.3 (small-degree representation).** For every $\xi\in J(k)$ and every $b\in C(k)$, there is an effective $k$-rational divisor $D$ of degree $2$ such that

$$
\xi=[D-2b]. \tag{4.5}
$$

**Proof.** The class $\xi+[2b]$ is a $k$-point of $\operatorname{Pic}^2(C)$. Over $k$ it is represented in the Picard sheaf; because $b$ gives a rigidification, it is represented by an actual line bundle $L$ of degree two. Riemann--Roch gives

$$
h^0(L)-h^0(\omega_C\otimes L^{-1})=1.
$$

Hence $h^0(L)\ge1$. A nonzero $k$-section exists because $H^0(C,L)$ is a nonzero $k$-vector space, and its zero divisor is an effective $k$-rational divisor $D$ with $L\simeq\mathcal O(D)$. This proves (4.5). $\square$

The theorem asserts existence, not a unique coordinate formula. Unique polynomial representatives and composition rules require choices at infinity and a separate arithmetic development.

There is a useful variant when the preferred base object is a rational divisor $B$ of degree two rather than a point. If $\xi\in J(k)$ is represented by an actual degree-zero line bundle, then the same proof applied after tensoring with $\mathcal O(B)$ produces an effective rational divisor $D$ with

$$
\xi=[D-B]. \tag{4.6}
$$

This formulation is available even if $C(k)$ is empty, but the line-bundle hypothesis on $\xi$ is essential. One must distinguish an actual line bundle from a mere $k$-point of the Picard scheme: without a rational point on the curve, the latter can carry a Brauer obstruction. Adding the actual divisor $B$ does not erase a nonzero obstruction already carried by $\xi$.

### 4.4 Uniqueness and the exceptional canonical class

For degree two, Proposition 4.1 gives the exact uniqueness statement.

**Theorem 4.4.** Let $D,E$ be effective geometric divisors of degree two with $D\sim E$.

- If $D\not\sim K_C$, then $D=E$.
- If $D\sim K_C$, then both $D$ and $E$ are fibers of the canonical map, and the full family of equivalent effective divisors is $|K_C|\simeq\mathbf P^1$.

**Proof.** If $D\not\sim K_C$, then $\ell(D)=1$. The projective space of nonzero sections of $\mathcal O(D)$ has dimension zero, so its only effective zero divisor is $D$. Thus $E=D$. If $D\sim K_C$, then $|D|=|K_C|$ has projective dimension one and consists of the canonical fibers by Proposition 4.2. $\square$

This exceptional pencil is the sole reason the symmetric square is not already the Jacobian. It will become the exceptional curve of a blowup.

The low-degree classification can be summarized without losing its hypotheses:

$$
\begin{array}{c|c|c}
\deg D&\text{condition}&\ell(D)\\ \hline
0&D\sim0&1\\
0&D\not\sim0&0\\
1&D\ge0&1\\
2&D\sim K_C&2\\
2&D\ge0,\ D\not\sim K_C&1\\
d\ge3&\text{arbitrary}&d-1.
\end{array} \tag{4.7}
$$

For the last row, $K_C-D$ has negative degree. For degree one, the row applies to effective divisors; a general degree-one class can have no section. This table is often the quickest way to detect an invalid divisor argument: any claim of two distinct effective representatives in a noncanonical degree-two class contradicts the fourth and fifth rows.

## 5. The Jacobian and its theta divisor

The divisor calculations now need a geometric group in which they can vary. This chapter specializes the general Jacobian and polarization theory to dimension two, where theta is itself the original curve and its self-intersection has the decisive value two.

### 5.1 The degree-zero Picard surface

The Jacobian is the geometric recipient of divisor classes. Picard theory gives more than an abstract group: $J$ is a smooth, proper, geometrically connected commutative group variety of dimension two, and its tangent and cotangent spaces at the origin are

$$
T_0J\simeq H^1(C,\mathcal O_C),\qquad
\Omega^1_{J,0}\simeq H^0(C,\omega_C). \tag{5.1}
$$

Both spaces have dimension two. The identifications commute with extension of the ground field.

Degree components $\operatorname{Pic}^d(C)$ are torsors under $J$. A rational point $b$ trivializes every such torsor by

$$
[L]\longmapsto[L(-db)].
$$

Without a rational point, the Jacobian still exists but there is no canonical curve-to-group map. The natural degree-one Abel map lands in the torsor $\operatorname{Pic}^1(C)$.

### 5.2 Theta in genus two

For a genus-$g$ curve, theta is the image of effective divisors of degree $g-1$. Here $g-1=1$, so theta is unusually simple. The map

$$
a_1:C\longrightarrow\operatorname{Pic}^1(C),\qquad
P\longmapsto\mathcal O(P)
$$

has image

$$
W_1=\{[L]:\deg L=1, h^0(C,L)>0\}. \tag{5.2}
$$

Every degree-one effective divisor is a single geometric point, and degree-one linear systems are rigid, so $a_1$ is injective on geometric points. Its cotangent map at $P$ is the evaluation map

$$
H^0(C,\omega_C)\longrightarrow\omega_C|_P.
$$

The canonical system is base-point free by Theorem 2.1, so this map is surjective and $a_1$ is unramified. A proper morphism that is unramified and universally injective is a closed immersion. Thus $a_1$ is a geometric embedding over the ground field, including in positive characteristic. Once $b\in C(k)$ is fixed, translation by $\mathcal O(-b)$ identifies $W_1$ with the divisor

$$
\Theta_b=j_b(C)\subset J. \tag{5.3}
$$

Thus the genus-two theta divisor is smooth and isomorphic to the curve. In higher genus theta may be singular; genus two is the last case in which its geometry is automatically this transparent.

### 5.3 The principal polarization

For any line bundle $M$ on an abelian variety $A$, translation defines

$$
\phi_M:A\longrightarrow A^\vee,\qquad
x\longmapsto t_x^*M\otimes M^{-1}. \tag{5.4}
$$

Taking $M=\mathcal O_J(\Theta_b)$ gives the canonical polarization

$$
\lambda_C:J\xrightarrow{\sim}J^\vee. \tag{5.5}
$$

It is principal: it is an isomorphism, not merely an isogeny. Changing $b$ translates $\Theta_b$, and translation does not change $\phi_M$. Hence $\lambda_C$ is independent of the base point and exists even when $C(k)$ is empty.

For clarity, the numerical reason for principality can be seen directly in dimension two without presupposing the conclusion. The theta divisor is the smooth curve $C$, while $K_J$ is trivial. Adjunction therefore gives

$$
\Theta_b^2=\deg K_C=2.
$$

On an abelian surface, Riemann--Roch then gives

$$
\chi(M)=\frac{c_1(M)^2}{2},\qquad
\deg\phi_M=\chi(M)^2. \tag{5.6}
$$

For the theta line, $c_1(M)^2=2$, so $\chi(M)=1$ and $\deg\phi_M=1$. The kernel has scheme-theoretic length one, including in positive characteristic, and therefore is trivial.

### 5.4 Intersection numbers and translates

The self-intersection, already used in the numerical proof of principality,

$$
\Theta^2=2 \tag{5.7}
$$

is the central incidence number of genus-two Jacobian geometry. It has two compatible proofs. The general theta intersection formula gives $\Theta^g=g!$, hence $2$ when $g=2$. Alternatively, adjunction on the abelian surface gives

$$
2g(\Theta)-2=\Theta\cdot(\Theta+K_J)=\Theta^2,
$$

because $K_J\sim0$ and $g(\Theta)=2$.

Every translate $\Theta+x$ has the same numerical class. If $x\ne0$, then $\Theta+x\ne\Theta$: otherwise the stabilizer of the ample divisor would contain a nonzero translation, while the associated principal polarization has trivial kernel. Therefore two distinct translates have zero-dimensional intersection of total scheme-theoretic length

$$
\Theta\cdot(\Theta+x)=2. \tag{5.8}
$$

The points may coincide with multiplicity two. This possibility records tangency and cannot be discarded in characteristic-dependent or local arguments.

We can see the number two without intersection theory when the translate comes from the curve. Assume for simplicity that $b$ is Weierstrass and let $x=j_b(R)$ be nonzero. A point $j_b(P)$ lies in $\Theta\cap(\Theta+x)$ exactly when

$$
[P-b]=[Q-b]+[R-b]
$$

for some $Q$, or equivalently

$$
P+b\sim Q+R. \tag{5.9}
$$

Unless this degree-two class is canonical, uniqueness forces equality of the effective divisors and leaves the evident incidences. When it is canonical, hyperelliptic conjugation supplies the limiting double intersection. This elementary calculation and the intersection number (5.8) describe the same scheme with different emphases: divisor uniqueness describes its points, while intersection theory retains multiplicity at tangency.

## 6. The Abel--Jacobi curve

A rational base point converts points into degree-zero classes, but usefulness requires much more than a set map. This chapter proves that the conversion is a closed embedding, identifies its differential, and shows that the embedded curve is precisely the theta divisor controlling the principal polarization.

### 6.1 Construction and change of base point

Choose $b\in C(k)$. The divisor $\Delta-C\times\{b\}$ on $C\times C$ defines the family of degree-zero line bundles $\mathcal O(P-b)$ and hence

$$
j_b:C\longrightarrow J,\qquad P\longmapsto[P-b]. \tag{6.1}
$$

It sends $b$ to $0$. If $b'$ is another rational point, then

$$
j_{b'}(P)=j_b(P)+[b-b']. \tag{6.2}
$$

Thus changing the base point translates the embedded curve. Every property invariant under translation, including being a closed immersion and defining the principal polarization, is independent of the choice.

The construction is compatible with field extension. If $K/k$ is any extension, the base change of $j_b$ is $j_{b_K}$. This elementary fact is what permits geometric injectivity over $\bar k$ to imply injectivity on $K$-points for every $K$.

### 6.2 Injectivity on points

**Proposition 6.1.** The map $j_b$ is injective on geometric points.

**Proof.** If $j_b(P)=j_b(Q)$, then $P-Q$ is principal. If $P\ne Q$, a rational function with divisor $P-Q$ has exactly one simple pole and defines a morphism

$$
C\longrightarrow\mathbf P^1
$$

of degree one. It would be an isomorphism, contradicting $g(C)=2$. Hence $P=Q$. $\square$

This proof works for every positive-genus smooth proper curve. It is worth noting what it does not say: equality after applying a quotient $J\to A$ need not imply equality of points, because the difference may lie in the kernel of the quotient.

### 6.3 The differential and closed immersion

Pointwise injectivity alone does not rule out inseparable behavior. The differential supplies the missing infinitesimal statement.

**Theorem 6.2 (Abel--Jacobi embedding).** For every field $k$ and every $b\in C(k)$, the map $j_b:C\to J$ is a closed immersion.

**Proof strategy.** We show that it separates geometric points and tangent directions. Properness then upgrades the resulting immersion to a closed immersion.

At a geometric point $P$, the transpose of the tangent map is evaluation of differentials,

$$
H^0(C,\omega_C)\longrightarrow\omega_C|_P. \tag{6.3}
$$

The canonical linear system is base-point free by Theorem 2.1, so this evaluation is surjective. Therefore

$$
d(j_b)_P:T_PC\longrightarrow T_{j_b(P)}J
$$

is injective. Proposition 6.1 gives injectivity on geometric points. A locally finite-type morphism between smooth varieties that is injective on geometric points and unramified is a locally closed immersion here: equivalently, the diagonal is both radicial and unramified, while the cotangent criterion gives the local surjection on completed local rings. Since $C$ is proper and $J$ is separated, the image is closed. Hence $j_b$ is a closed immersion. $\square$

The proof identifies more than injectivity. Pullback of invariant differentials is an isomorphism

$$
j_b^*:H^0(J,\Omega^1_J)\xrightarrow{\sim}H^0(C,\omega_C). \tag{6.4}
$$

Thus the two infinitesimal directions on the Jacobian are detected by the two regular differentials on the curve.

For later local use, the completed-local-ring form is worth recording. Let $z=j_b(P)$. Smoothness gives

$$
\widehat{\mathcal O}_{J,z}\simeq k[[X,Y]],\qquad
\widehat{\mathcal O}_{C,P}\simeq k[[t]].
$$

After choosing invariant differentials whose restrictions have expansions

$$
\omega_1=(a_0+a_1t+\cdots)\,dt,\qquad
\omega_2=(b_0+b_1t+\cdots)\,dt,
$$

at least one of $a_0,b_0$ is nonzero. The cotangent map therefore sends some linear combination of $X,Y$ to a unit times $t$ modulo $t^2$. Nakayama's lemma and completeness show that

$$
\widehat{\mathcal O}_{J,z}\longrightarrow\widehat{\mathcal O}_{C,P}
$$

is surjective. This is the formal-immersion statement hidden inside the closed-embedding proof. It remains valid after reduction at every point where the curve and Jacobian models are smooth.

### 6.4 The curve as the theta divisor

By construction,

$$
j_b(C)=\Theta_b.
$$

The embedded curve is therefore not an arbitrary ample curve on $J$; it is the divisor that defines the principal polarization. Its normal bundle follows from adjunction:

$$
N_{C/J}\simeq\mathcal O_J(\Theta_b)|_C\simeq\omega_C, \tag{6.5}
$$

because $\omega_J$ is trivial. Its degree is $2$, agreeing with $\Theta^2=2$.

The involution formula (2.4) now has a surface interpretation. The image of $\iota(C)$ is the inverse of $\Theta_b$ followed by a translation. If $b$ is Weierstrass, $[-1]^*\Theta_b=\Theta_b$ as a divisor. For a general base point, the canonical theta class remains symmetric even though the chosen translate need not be fixed by inversion.

## 7. The symmetric square

One point gives the theta curve; two points are enough to reach the whole Jacobian. This chapter makes that statement exact by studying the degree-two Abel map. The canonical pencil supplies its only exceptional fiber, and resolving that fiber reveals the symmetric square as a blowup.

### 7.1 Degree-two divisors as a smooth surface

The symmetric square

$$
C^{(2)}=(C\times C)/\mathfrak S_2
$$

parametrizes effective divisors of degree two. It is a smooth proper surface over $k$. Smoothness along the diagonal deserves explanation: if $t_1,t_2$ are local parameters on the two factors, the symmetric functions

$$
s=t_1+t_2,\qquad p=t_1t_2
$$

are regular parameters on the quotient. This remains true in characteristic two when interpreted through the Hilbert scheme of length-two divisors; the symmetric square of a smooth curve represents finite flat effective divisors and is smooth.

The universal degree-two divisor gives the Abel map

$$
a_2:C^{(2)}\longrightarrow\operatorname{Pic}^2(C),\qquad
D\longmapsto\mathcal O_C(D). \tag{7.1}
$$

After choosing $b\in C(k)$, translation gives

$$
u_b:C^{(2)}\longrightarrow J,\qquad
D\longmapsto[D-2b]. \tag{7.2}
$$

The source and target are both smooth proper surfaces. Riemann--Roch makes $a_2$ surjective, and the uniqueness theorem for effective degree-two divisors makes it birational.

### 7.2 Fibers of the degree-two Abel map

The fiber over a degree-two line bundle $L$ is its complete linear system:

$$
a_2^{-1}([L])=\mathbf P(H^0(C,L)). \tag{7.3}
$$

Proposition 4.1 therefore gives the complete fiber classification.

**Theorem 7.1.** Every geometric fiber of $a_2$ is a single reduced point except the fiber over $[\omega_C]$, which is

$$
|K_C|\simeq\mathbf P^1. \tag{7.4}
$$

Under $u_b$, the exceptional fiber maps to

$$
\kappa_b=[K_C-2b]\in J(k). \tag{7.5}
$$

**Proof.** Equation (7.3) and Proposition 4.1 give the dimensions. Away from the canonical class, the unique section has a unique zero divisor and varies with no infinitesimal freedom, so the fiber is reduced. At the canonical class the projectivized two-dimensional space $H^0(C,\omega_C)$ is $\mathbf P^1$ and parametrizes the canonical fibers. Translation produces (7.5). $\square$

If $b$ is Weierstrass, then $K_C\sim2b$, so $\kappa_b=0$. For an arbitrary base point, the exceptional point is a fixed translate of the origin.

### 7.3 The blowup theorem

The exceptional fiber has self-intersection $-1$ and resolves the unique indeterminacy of the inverse Abel map. This yields the strongest geometric description in the book.

**Theorem 7.2 (symmetric square as a blowup).** The morphism

$$
u_b:C^{(2)}\longrightarrow J
$$

identifies $C^{(2)}$ with the blowup of $J$ at the $k$-rational point $\kappa_b=[K_C-2b]$. The exceptional curve is the canonical pencil $|K_C|$, and its normal bundle is $\mathcal O_{\mathbf P^1}(-1)$.

**Proof strategy.** The fiber theorem shows that $u_b$ is a proper birational morphism, an isomorphism away from one point, with one projective-line fiber. We identify its first-order behavior with the universal directions through that point.

Put $E=|K_C|$. At a divisor $D\in E$, the tangent space to $C^{(2)}$ is

$$
H^0(D,\mathcal O_D(D)).
$$

The differential of $a_2$ is the boundary map in

$$
0\longrightarrow\mathcal O_C
\longrightarrow\mathcal O_C(D)
\longrightarrow\mathcal O_D(D)
\longrightarrow0. \tag{7.6}
$$

Because $h^0(\mathcal O_C(D))=2$, its kernel is one-dimensional after quotienting by constants; this kernel is exactly the tangent line to $E$. The transpose of the differential is restriction

$$
H^0(C,\omega_C)\longrightarrow H^0(D,\omega_C|_D). \tag{7.7}
$$

The induced map from the normal line $N_{E/C^{(2)},D}$ to $T_{\kappa_b}J=H^0(C,\omega_C)^\vee$ is nonzero. If $s$ is the canonical section with zero divisor $D$, then (7.7) has kernel $ks$, so the image of the original differential is the annihilator line $(ks)^\perp$. As $D$ varies, these annihilator lines form the tautological line over $\mathbf P(T_{\kappa_b}J)$. Consequently

$$
N_{E/C^{(2)}}\simeq\mathcal O_E(-1), \tag{7.7a}
$$

and the exceptional curve maps canonically and isomorphically to

$$
\mathbf P(T_{\kappa_b}J)\simeq\mathbf P^1.
$$

The two generators of the maximal ideal of $\kappa_b$ pull back to functions vanishing to order one along $E$, and their first-order normal parts never vanish simultaneously by the preceding tangent calculation. Hence

$$
\mathfrak m_{\kappa_b}\mathcal O_{C^{(2)}}=\mathcal O_{C^{(2)}}(-E), \tag{7.7b}
$$

an invertible ideal. The universal property of the blowup therefore factors $u_b$ through

$$
C^{(2)}\longrightarrow\operatorname{Bl}_{\kappa_b}J\longrightarrow J.
$$

The first arrow is proper and birational and is an isomorphism away from the exceptional divisor. Along that divisor it induces an isomorphism both on the divisor and, by (7.7a), on the normal line. Its tangent map is therefore an isomorphism at every point of $E$, so it is etale and quasi-finite there. It is quasi-finite everywhere, hence finite; being finite birational onto the smooth, therefore normal, blowup, it is an isomorphism. Formula (7.7a) also identifies the exceptional normal bundle with $\mathcal O_{\mathbf P^1}(-1)$. $\square$

The theorem is defined over $k$, not merely over $\bar k$, because $K_C$ and $b$ are defined over $k$. It explains why a degree-two class is represented uniquely except at the canonical class: blowing down forgets which member of the canonical pencil was chosen.

The canonical-class formula checks the sign of the exceptional normal bundle. Since $J$ has trivial canonical bundle and blowing up a smooth surface at a point adds the exceptional divisor $E$, one has

$$
K_{C^{(2)}}\sim E. \tag{7.8}
$$

Adjunction on $E\simeq\mathbf P^1$ gives

$$
-2=(K_{C^{(2)}}+E)\cdot E=2E^2,
$$

and hence $E^2=-1$. This calculation also proves that the contraction cannot be a quotient singularity masquerading as a smooth point: the exceptional curve has precisely the numerical type of the blowup of a smooth surface.

There is a complementary birational description of the inverse map. For $\xi\ne\kappa_b$, Riemann--Roch produces the unique nonzero section, up to scalar, of the degree-two line bundle represented by $\xi+[2b]$. Taking its zero divisor defines

$$
J\setminus\{\kappa_b\}\longrightarrow C^{(2)}.
$$

As $\xi$ approaches $\kappa_b$, the unique section loses uniqueness and its limiting line in $H^0(C,\omega_C)$ records a point of $\mathbf P(H^0(C,\omega_C))=|K_C|$. The blowup adds exactly this missing limiting direction.

### 7.4 Rational points on the symmetric square

Taking $k$-points in the blowup theorem must be done with care. If $\xi\in J(k)$ and $\xi\ne\kappa_b$, then the unique effective divisor $D$ satisfying $[D-2b]=\xi$ is fixed by Galois and hence lies in $C^{(2)}(k)$. Over $\kappa_b$, the rational points of the fiber are the $k$-rational canonical divisors, parametrized by the genus-zero curve $|K_C|$.

The canonical pencil is always $|K_C|\simeq\mathbf P^1_k$, so this exceptional fiber has many $k$-points when $k$ is infinite. Their images in $J(k)$ are all the same. Consequently the map

$$
C^{(2)}(k)\longrightarrow J(k)
$$

is surjective but never injective. By contrast, the degree-one map $C(k)\to J(k)$ is injective.

A $k$-point of $C^{(2)}$ can encode a quadratic point of $C$. Therefore determining $C^{(2)}(k)$ is a stronger and different problem than determining $C(k)$. In modular applications one must track whether a surviving effective divisor splits into rational points, is twice a rational point, or is an irreducible degree-two closed point.

## 8. Addition, subtraction, and incidence

The blowup theorem describes individual classes, but arithmetic also compares sums, differences, and quotient images. This chapter translates the group law into intersections of theta translates and explains how additional involutions can project the genus-two problem onto elliptic curves without erasing fiber ambiguities.

### 8.1 Sums of two points

The group law on $J$ is geometrically visible through $u_b$. For points $P,Q\in C(\bar k)$,

$$
j_b(P)+j_b(Q)=[P+Q-2b]=u_b(P+Q). \tag{8.1}
$$

Thus every geometric point of $J$ is a sum of two geometric points on the Abel--Jacobi curve. Over $k$, the associated effective divisor of degree two may instead be a nonsplit quadratic point. The representation is unique except at $\kappa_b$, where all conjugate pairs $P+\iota(P)$ give the same sum.

If $b$ is Weierstrass, then $\kappa_b=0$, and

$$
j_b(P)+j_b(\iota(P))=0. \tag{8.2}
$$

This gives the geometric origin of inversion. For a general base point, the sum is the constant $\kappa_b$.

Equation (8.1) is not yet a rule for adding arbitrary reduced representatives: a sum of two degree-two divisors initially has degree four and must be reduced. What the equation provides is the existence and uniqueness geometry that any exact addition procedure must respect.

### 8.2 Differences and intersections of theta translates

Consider the difference map

$$
\delta:C\times C\longrightarrow J,\qquad
(P,Q)\longmapsto j_b(P)-j_b(Q). \tag{8.3}
$$

For $x\in J(\bar k)$, a pair lies over $x$ precisely when

$$
j_b(P)\in\Theta_b\cap(\Theta_b+x).
$$

If $x\ne0$, the two theta translates are distinct and their intersection has length two. Hence $\delta$ is generically finite of degree two away from the special behavior at the origin.

At $x=0$, the fiber is the diagonal $P=Q$, a whole copy of $C$. Thus $\delta$ is not finite. This positive-dimensional exceptional fiber is compatible with the intersection calculation because at $x=0$ the two divisors coincide, so their intersection is not proper and the number $\Theta^2=2$ is no longer a literal point count.

This distinction is useful in rational-point arguments. For a nonzero known class $x\in J(k)$, finding rational pairs with difference $x$ is a finite incidence problem of total geometric length two. For $x=0$, equality of Abel--Jacobi images reduces to injectivity and gives the diagonal.

### 8.3 The diagonal and the canonical direction

The differential of $\delta$ at $(P,Q)$ is

$$
d\delta_{(P,Q)}(v,w)=dj_P(v)-dj_Q(w). \tag{8.4}
$$

At a point of the diagonal, the tangent direction $(v,v)$ lies in the kernel. A complementary direction measures the tangent line of the theta curve in the two-dimensional tangent space of $J$. Via (6.4), that tangent line is annihilated by the one-dimensional space of regular differentials vanishing at $P$.

Two theta translates meet nontransversely exactly when their tangent lines agree at an intersection point. In canonical coordinates this means that the corresponding points have the same image under the canonical map, hence form a hyperelliptic pair. Thus tangency is governed by the same canonical pencil that produced the exceptional curve in $C^{(2)}$.

This gives a unified picture: conjugate pairs are exceptional for degree-two representation, inversion, tangent incidence, and ramification. These are not separate coincidences; they are four manifestations of the canonical double cover.

### 8.4 Maps to elliptic curves and split Jacobians

Some genus-two curves possess an involution other than $\iota$. Let $\tau$ be such an involution in characteristic different from two, and suppose the quotient

$$
q:C\longrightarrow E=C/\langle\tau\rangle
$$

is a smooth genus-one curve with a rational point. Riemann--Hurwitz gives

$$
2=2(2g(E)-2)+\deg R_q=\deg R_q,
$$

so $q$ has degree two and two ramification points counted with multiplicity.

Pullback and norm induce

$$
q^*:E\longrightarrow J,\qquad
q_*:J\longrightarrow E,\qquad
q_*q^*=[2]. \tag{8.5}
$$

The connected kernel of $q_*$ is an elliptic curve $E'$. The map

$$
E\times E'\longrightarrow J
$$

is an isogeny. Thus $J$ is split up to isogeny, though generally not isomorphic as a principally polarized abelian variety to the product with its product polarization.

The proof of the isogeny assertion is dimension-theoretic. The nonzero map $q^*$ has finite kernel because $q_*q^*=[2]$. Its image is an elliptic subvariety of $J$. The norm has one-dimensional connected kernel. Addition of the image and kernel gives a homomorphism between two-dimensional abelian varieties with finite kernel, hence an isogeny.

Such quotients are valuable arithmetic interfaces: a rank-zero elliptic quotient can constrain the curve even when the full Jacobian has positive rank. Equality in the quotient, however, is weaker than equality in $J$, so fibers of the quotient map must always be analyzed.

A common source of extra involutions is an even sextic. Suppose $\operatorname{char}k\ne2$ and

$$
C:y^2=x^6+ax^4+bx^2+c
$$

is smooth. Besides the hyperelliptic involution, the map

$$
\tau(x,y)=(-x,y)
$$

is an involution. Its invariant functions $X=x^2$ and $Y=y$ satisfy

$$
Y^2=X^3+aX^2+bX+c,
$$

which is a genus-one equation when the cubic is nonsingular. The product $\iota\tau$ yields the other elliptic quotient, using invariant functions $X=x^{-2}$ and a suitable multiple of $y/x^3$ on the complementary chart. The resulting two elliptic factors account for the two independent differential eigenspaces

$$
H^0(C,\omega_C)
=k\frac{dx}{y}\oplus k\frac{x\,dx}{y}.
$$

This worked family shows why one must identify which involution corresponds to which quotient: the hyperelliptic involution itself has genus-zero quotient and contributes no elliptic factor.

## 9. Finite fields and exact geometric counts

Reduction arguments require finite targets whose sizes and embedded curve subsets are controlled. This chapter brings Frobenius, Weil bounds, and symmetric-square geometry together. The result is both a set of exact formulas and a warning that group orders alone do not determine reduction images.

### 9.1 Frobenius on a genus-two Jacobian

Let $C/\mathbf F_q$ be smooth, proper, and geometrically connected. Write the numerator of its zeta function as

$$
P_C(T)=\prod_{i=1}^4(1-\alpha_iT)
=1-a_1T+a_2T^2-qa_1T^3+q^2T^4. \tag{9.1}
$$

Every complex conjugate of every $\alpha_i$ has absolute value $\sqrt q$, and the roots occur in pairs $\alpha,q/\alpha$. The point counts satisfy

$$
N_n:=\#C(\mathbf F_{q^n})
=q^n+1-\sum_{i=1}^4\alpha_i^n. \tag{9.2}
$$

In particular,

$$
a_1=q+1-N_1. \tag{9.3}
$$

Since

$$
\sum_i\alpha_i^2=a_1^2-2a_2,
$$

the $n=2$ count gives

$$
a_2=\frac{N_2-q^2-1+a_1^2}{2}. \tag{9.4}
$$

More precisely,

$$
P_C(T)=\det(1-TF\mid V_\ell J)
$$

for every auxiliary prime $\ell$ different from the characteristic; the reciprocal polynomial is the usual characteristic polynomial $\det(T-F)$. Consequently

$$
\#J(\mathbf F_q)=P_C(1)
=1-a_1+a_2-qa_1+q^2. \tag{9.5}
$$

Thus counts of the curve over $\mathbf F_q$ and $\mathbf F_{q^2}$ determine the order of its Jacobian over $\mathbf F_q$.

### 9.2 Point bounds for the curve and Jacobian

The Hasse--Weil bound in genus two is

$$
|N_n-(q^n+1)|\le4q^{n/2}. \tag{9.6}
$$

It is a consequence of (9.2) and $|\alpha_i|=\sqrt q$. For the Jacobian, (9.5) may be written

$$
\#J(\mathbf F_q)=\prod_{i=1}^4(1-\alpha_i).
$$

Pairing complex-conjugate roots, or taking absolute values in all embeddings, gives the useful coarse bounds

$$
(\sqrt q-1)^4\le\#J(\mathbf F_q)\le(\sqrt q+1)^4. \tag{9.7}
$$

These inequalities are meaningful even when the lower bound is not integral. They control size but do not determine group structure. Two finite abelian groups with the same order can impose different reduction constraints.

The bounds require smooth proper reduction. Applying them to a singular affine equation without first taking its smooth projective model can give the wrong genus and the wrong constant.

### 9.3 The symmetric-square count

There are two exact ways to count $C^{(2)}(\mathbf F_q)$. An effective rational divisor of degree two is either an unordered pair of rational points, allowing repetition, or a closed point of degree two. Since the number of degree-two closed points is $(N_2-N_1)/2$,

$$
\#C^{(2)}(\mathbf F_q)
=\frac{N_1(N_1+1)}2+\frac{N_2-N_1}2
=\frac{N_1^2+N_2}{2}. \tag{9.8}
$$

If $C(\mathbf F_q)$ contains a base point, the blowup theorem gives a second formula. Blowing up one rational point replaces it by $\mathbf P^1(\mathbf F_q)$, so it adds

$$
(q+1)-1=q
$$

points. Hence

$$
\#C^{(2)}(\mathbf F_q)=\#J(\mathbf F_q)+q. \tag{9.9}
$$

Combining the two yields

$$
\boxed{
\#J(\mathbf F_q)=\frac{N_1^2+N_2}{2}-q.
} \tag{9.10}
$$

This identity provides an internal consistency check on point counts and on the chosen smooth model. It is geometric, not a substitute for determining the invariant factors of $J(\mathbf F_q)$.

The identity remains true when $C(\mathbf F_q)$ is empty. Indeed substitute

$$
N_1=q+1-a_1,\qquad
N_2=q^2+1-a_1^2+2a_2
$$

into the right side of (9.10). It becomes

$$
q^2+1-(q+1)a_1+a_2=P_C(1)=\#J(\mathbf F_q).
$$

Thus the base-point-free proof comes directly from Frobenius, while the blowup proof explains the extra term $q$ whenever the two surfaces are identified using a rational point.

As a concrete check, consider

$$
C_7:z^2=t(t-1)(t^3-8t^2+5t+1). \tag{9.11}
$$

The cubic factor has discriminant $7^4$, takes the values $1$ and $-1$ at $0$ and $1$, and therefore shares no root with $t(t-1)$. The quintic is squarefree over $\mathbf Q$, so this is a smooth genus-two curve with one rational Weierstrass point at infinity. At the good primes $3$ and $5$, direct enumeration gives

$$
\begin{array}{c|cc}
q&\#C_7(\mathbf F_q)&\#C_7(\mathbf F_{q^2})\\ \hline
3&5&5\\
5&9&25.
\end{array} \tag{9.12}
$$

Formula (9.10) then gives

$$
\#J_7(\mathbf F_3)=\frac{25+5}{2}-3=12,
$$

and

$$
\#J_7(\mathbf F_5)=\frac{81+25}{2}-5=48. \tag{9.13}
$$

The calculation illustrates the proper logical order: verify smooth good reduction, count the curve over the first two residue extensions, and only then infer the Jacobian order. No conclusion about $J_7(\mathbf Q)$ follows from these two orders alone.

### 9.4 What finite-field counts can certify

Finite-field data support three distinct conclusions. First, $N_1$ and $N_2$ determine the Frobenius polynomial through (9.3)--(9.4). Second, that polynomial determines the orders $\#J(\mathbf F_{q^n})$ through

$$
\#J(\mathbf F_{q^n})=\prod_{i=1}^4(1-\alpha_i^n). \tag{9.14}
$$

Third, the actual group $J(\mathbf F_q)$ receives specialization from a global or local Jacobian at a good prime.

One must not merge these conclusions. The order of a finite group does not specify its elements. A congruence for an order may exclude torsion of a certain prime, but locating the reduction of a divisor class requires group-law information. Likewise, a finite-field point absent from $C(\mathbf F_q)$ excludes an integral lift in its residue disk, but a point present in the special fiber need not lift to the ground field.

## 10. Models and reduction over discrete valuation rings

A finite-field calculation constrains a global point only when generic and special fibers are connected by a valid model. This chapter gives sufficient good-reduction criteria, proves compatibility of specialization with Abel--Jacobi maps, and describes the graph corrections that replace the good-reduction picture in semistable families.

### 10.1 Good hyperelliptic models

Let $R$ be a discrete valuation ring with fraction field $K$, residue field $k$, and $2\in R^\times$. Suppose

$$
C: y^2=f(x)
$$

with $f\in R[x]$ of degree five, leading coefficient a unit, and discriminant a unit. The weighted projective closure, followed by the standard chart at infinity, is smooth and proper over $R$. Its generic and special fibers are genus-two curves, and the point at infinity is a section.

The same conclusion holds for a degree-six equation when the leading coefficient and discriminant are units and both charts at infinity pass the smoothness test. The unit discriminant says precisely that the six geometric branch points remain distinct after reduction. The assumption that $2$ is invertible makes the cover tamely ramified and lets the branch criterion detect smoothness.

These conditions are sufficient, not necessary. A curve may have good reduction even when a poorly chosen integral equation has nonunit discriminant. Coordinate change or minimization can remove artificial collisions. Conversely, an integral affine equation with squarefree generic polynomial need not have good reduction if its reduction acquires a repeated root.

For a degree-five equation, smoothness at infinity can be checked explicitly. Put

$$
u=x^{-1},\qquad w=y/x^3.
$$

Then the equation becomes

$$
w^2=u^6f(u^{-1})=u(a_5+a_4u+\cdots+a_0u^5). \tag{10.0a}
$$

The point at infinity is $(u,w)=(0,0)$. If $a_5$ is a unit and $2$ is invertible, the partial derivative with respect to $u$ is $-a_5$ at this point, so the model is smooth there. On the affine chart, a simultaneous zero of the two partial derivatives would be a repeated root of the reduction of $f$, excluded by the unit discriminant. This proves the sufficient good-reduction criterion rather than merely asserting it.

For degree six the same substitution gives

$$
w^2=a_6+a_5u+\cdots+a_0u^6.
$$

The points at infinity lie above the two square roots of $a_6$. Their union is finite étale over $R$ when $a_6$ is a unit and $2$ is invertible; it need not split into two sections over $R$. Good reduction does not require the individual points at infinity to be rational.

In residue characteristic two, a sextic discriminant criterion is inadequate. One must use a proper model of $y^2+h(x)y=f(x)$ and check smoothness, including at infinity.

### 10.2 Specialization of points and divisor classes

Let $\mathcal C/R$ be smooth and proper with generic fiber $C$ and special fiber $C_k$. Properness and the valuative criterion give a bijection

$$
\mathcal C(R)=C(K) \tag{10.1}
$$

when $R$ is a valuation ring: every $K$-point extends uniquely to a section. Reduction gives

$$
\operatorname{red}_C:C(K)\longrightarrow C(k). \tag{10.2}
$$

The relative Picard scheme has identity component an abelian scheme $\mathcal J/R$ with generic fiber $J$ and special fiber $J_k$. Its properness similarly gives

$$
J(K)=\mathcal J(R)
$$

and a group homomorphism

$$
\operatorname{red}_J:J(K)\longrightarrow J(k). \tag{10.3}
$$

If $b\in C(K)$ extends to a section, formation of the Abel map commutes with base change, so the square

$$
\begin{array}{ccc}
C(K)&\xrightarrow{j_b}&J(K)\\
\downarrow&&\downarrow\\
C(k)&\xrightarrow{j_{\bar b}}&J(k)
\end{array} \tag{10.4}
$$

commutes. This square is the basic reduction interface for rational points.

### 10.3 Prime-to-residue-characteristic torsion

Let the residue characteristic be $p$. The kernel of reduction on $J(K)$ is controlled by the formal group of $\mathcal J$ and is pro-$p$ when $R$ is complete with finite residue field. Consequently reduction is injective on torsion of order prime to $p$.

**Proposition 10.1.** If $T\in J(K)$ has finite order $n$ with $(n,p)=1$ and $\operatorname{red}_J(T)=0$, then $T=0$.

**Proof.** Multiplication by $n$ on the smooth formal group is an automorphism because its linear term is multiplication by the unit $n\in R^\times$. Thus the formal kernel contains no nonzero $n$-torsion. Since a point reducing to zero lies in that formal kernel, $T=0$. Equivalently, the finite étale group scheme $\mathcal J[n]$ has separated sections, and a section specializing to the identity is the identity. $\square$

If $v$ and $w$ are two good places of distinct residue characteristics, the torsion subgroup of $J(K)$ injects into both finite groups away from those characteristics. In particular its order divides a suitably adjusted greatest common divisor of $\#J(k_v)$ and $\#J(k_w)$. This yields an upper bound on torsion, not its full determination unless candidate classes are also exhibited.

### 10.4 Semistable fibers and graph corrections

Good reduction is the clean case, but genus-two curves can degenerate semistably. Let $\mathcal C/R$ be a regular proper semistable model. The special fiber may be irreducible with nodes, or reducible. After passing to an algebraic closure $\bar k$ of the residue field, let $\Gamma$ be the geometric dual graph and let $\widetilde C_v$ be the normalization of its geometric components. The generalized Jacobian fits into

$$
0\longrightarrow T_\Gamma
\longrightarrow\operatorname{Pic}^0(C_{\bar k})
\longrightarrow\prod_vJ(\widetilde C_v)
\longrightarrow0, \tag{10.5}
$$

where $T_\Gamma$ is the graph torus. Its rank is $b_1(\Gamma)$.

The separated model of the generic Jacobian has geometric component group

$$
\Phi\simeq\operatorname{Div}^0(\Gamma)/\Delta\mathbf Z^{V(\Gamma)} \tag{10.6}
$$

for a split regular unit-thickness model, or equivalently after geometric base change. Weighted edge lengths replace the ordinary Laplacian when nodes have thickness. Over the original residue field, Galois acts on the geometric graph, torus, component Jacobians, and component group; rational points are not obtained by simply forgetting that action. Thus specialization contains three geometric layers: component Jacobians, a torus from graph cycles, and a finite graph-Jacobian component group.

It is incorrect at bad reduction simply to reduce a divisor and regard its total-degree-zero class as a point of an abelian special fiber. Multidegree and vertical divisors intervene. A common regular semistable model and the separated Picard quotient are needed to make the specialization map canonical.

## 11. Local fields and residue constraints

Over a local field, properness turns every rational point into a section and smoothness organizes sections into residue disks. This chapter studies how the Abel embedding sits inside the two-dimensional formal group, and how degree-two divisors and field extensions interact with that local structure.

### 11.1 Integral points from properness

Let $K$ be a local field with valuation ring $R$ and residue field $k$. For a proper smooth model $\mathcal C/R$, every $K$-point is integral and reduces to $C(k)$. Therefore

$$
C(K)=\coprod_{\bar P\in C(k)}C(K)_{\bar P}, \tag{11.1}
$$

where $C(K)_{\bar P}$ is the residue disk above $\bar P$. Smoothness gives each disk a local parameter $t$ identifying its completed local ring with $R[[t]]$ after choosing a lift.

This decomposition is finite because $C(k)$ is finite. It does not assert that every disk contains a $K$-point beyond the chosen lifts, nor that reduction is injective. A residue disk generally contains infinitely many local points.

### 11.2 Residue disks and the Abel map

The Abel--Jacobi embedding respects residue disks. At $P\in C(K)$, its tangent map is injective, and dually invariant differentials on $J$ restrict to regular differentials on $C$. If $t$ is a parameter at $P$ and $\omega$ is a differential, write

$$
\omega=(a_0+a_1t+a_2t^2+\cdots)\,dt. \tag{11.2}
$$

The coefficient $a_0$ is the cotangent evaluation controlling the first-order Abel map. Because the canonical system has no base point, at least one of the two basis differentials has $a_0\ne0$. Hence the curve is formally immersed in $J$ at every smooth point.

At two distinct residue points, their reductions have distinct Abel images over $k$ because the special-fiber Abel map is injective. Therefore points in different residue disks cannot have the same image in $J(K)$. Within one disk, equality is already excluded globally by the Abel embedding, while congruence to high order is measured by the formal group and the differential expansions.

The first-order map can be made coordinate-free. The kernel of reduction

$$
J_1(K)=\ker(J(K)\to J(k))
$$

has successive quotients modeled on the two-dimensional additive group of $k$, while a curve residue disk contributes a one-dimensional tangent line inside the first quotient. Under (10.4), that line is the image of

$$
T_{\bar P}C\hookrightarrow T_{j(\bar P)}J.
$$

Thus reduction first selects one of finitely many special points and the differential then selects one line in the two-dimensional formal neighborhood. This is the local geometric content behind formal-immersion arguments.

### 11.3 Local divisor classes

The map

$$
C^{(2)}(K)\longrightarrow J(K)
$$

is surjective when a base point is present, by the same Riemann--Roch proof as over an arbitrary field. Away from $\kappa_b$, its inverse is a unique $K$-rational effective divisor of degree two. The divisor may be split, doubled, or a quadratic closed point.

Reduction of such a divisor preserves degree but can change splitting behavior. Two conjugate $K$-points can reduce to distinct conjugate residue points, to rational residue points, or collide into a nonreduced divisor. Smoothness of the symmetric square ensures that all three patterns fit one proper specialization map.

The exceptional class $\kappa_b$ requires separate treatment: its inverse image is the entire canonical pencil. Thus a local condition imposed only on the Jacobian cannot distinguish the hyperelliptic fibers above that one class.

### 11.4 Compatibility across extensions

Let $L/K$ be a finite separable extension of local fields. Base change gives compatible maps

$$
C(K)\longrightarrow C(L),\qquad J(K)\longrightarrow J(L).
$$

If the model has good reduction and $R_L$ is the integral closure of $R$, specialization commutes with the residue-field extension. For divisor classes, pullback is the evident scalar extension. Norm in the opposite direction satisfies

$$
\operatorname{Nm}_{L/K}(\xi_L)=[L:K]\xi
$$

for $\xi\in J(K)$, with the norm interpreted through restriction of scalars or the sum of Galois conjugates in a normal closure.

Ramification can refine a residue disk into smaller disks but cannot merge distinct special-fiber points. At bad reduction it can also resolve nodes or split components, so graph and component-group data must be recomputed after base change. Statements about good reduction remain stable under unramified extension; semistable statements require tracking edge lengths and Galois action on the dual graph.

## 12. Number fields, Mordell--Weil groups, and heights

The local images must ultimately be imposed on one global group. This chapter recalls the exact finite-generation and canonical-height consequences available for a genus-two Jacobian and explains how they convert global classes into a lattice subject to finite reduction congruences.

### 12.1 The Jacobian as a finitely generated group

Let $K$ be a number field. The Jacobian is an abelian surface, so the Mordell--Weil theorem gives

$$
J(K)\simeq J(K)_{\mathrm{tors}}\oplus\mathbf Z^r \tag{12.1}
$$

for a finite torsion group and an integer $r\ge0$. This is the global finiteness structure needed for arithmetic, but it is not itself a list of generators and it does not determine $C(K)$.

Choosing $b\in C(K)$ embeds $C(K)$ into this finitely generated group. If $J(K)$ is finite, then $C(K)$ is finite immediately. If $r>0$, the ambient group is infinite. Even when $r=1<g$, additional arguments are required to prove or determine the intersection with the curve; finite generation alone supplies no such list.

### 12.2 The theta height

The canonical principal polarization is represented by a theta divisor. A chosen translate $\Theta_b$ need not itself be symmetric as a divisor over $K$. The line bundle

$$
L_\Theta=\mathcal O_J(\Theta_b+[-1]^*\Theta_b) \tag{12.2}
$$

is symmetric and ample and induces twice the principal polarization. More generally, any symmetric ample line bundle inducing a positive multiple of the theta polarization gives an equivalent normalization. Its canonical height

$$
\widehat h_\Theta:J(\bar K)\longrightarrow\mathbf R_{\ge0} \tag{12.3}
$$

satisfies

$$
\widehat h_\Theta([n]x)=n^2\widehat h_\Theta(x),\qquad
\widehat h_\Theta(x)=0\Longleftrightarrow x\text{ is torsion}. \tag{12.4}
$$

Polarization gives a positive-definite bilinear pairing on $J(K)$ modulo torsion:

$$
\langle x,y\rangle_\Theta
=\frac12\bigl(
\widehat h_\Theta(x+y)-\widehat h_\Theta(x)-\widehat h_\Theta(y)
\bigr). \tag{12.5}
$$

The free quotient is therefore a Euclidean lattice. A bound on canonical height contains only finitely many $K$-rational classes. In applications, an ordinary projective height can be used because it differs from the canonical height by a bounded function, but an effective enumeration requires an actual bound for that difference.

Changing the base point translates the curve but does not change the polarization. Translation changes a chosen Weil height by controlled lower-order terms, while the quadratic height remains attached to the symmetric line bundle on $J$. It is therefore important to distinguish the canonical height of a class from a naive height of coordinates on a chosen curve model.

### 12.3 The embedded curve is not a subgroup

The image $j_b(C)$ contains $0$ but is not a subgroup of $J$.

**Proposition 12.1.** No translate of $j_b(C)$ is a positive-dimensional abelian subvariety of $J$.

**Proof.** A one-dimensional abelian subvariety is a smooth genus-one curve. Every translate has the same genus. But $j_b(C)$ is isomorphic to $C$ and has genus two. Thus it cannot be an elliptic subgroup or its translate. It also cannot be all of $J$ because its dimension is one. $\square$

Accordingly, adding two rational points of $C$ usually leaves the curve. Equation (8.1) lands in the symmetric-square image, which is all of $J$, not in the degree-one theta curve. A group-theoretic generation statement for $J(K)$ and a geometric membership test for $\Theta_b(K)$ are separate ingredients.

If $J$ has an elliptic quotient, the image of $C$ in that quotient can still be useful. But the quotient map may identify several points, and its fibers must be controlled by the incidence geometry of Chapter 8 or by additional functions.

### 12.4 Reduction maps as arithmetic interfaces

At every finite place $v$ of good reduction, the reduction map gives

$$
J(K)\longrightarrow J(k_v). \tag{12.6}
$$

For a subgroup $G\subseteq J(K)$ known to contain $j_b(C(K))$, define the surviving subset

$$
S_v(G)=\{g\in G:\operatorname{red}_v(g)\in j_{\bar b}(C(k_v))\}. \tag{12.7}
$$

Every global point maps into $S_v(G)$. Intersecting conditions from several places can greatly reduce the possibilities because they are simultaneous congruence conditions on one finitely generated group.

There are two logical directions. If a class fails one local condition, it cannot come from a global point. If it survives every tested place, no conclusion of global existence follows. Completeness requires a proof that the tested finite quotients distinguish every remaining global class or that a height bound has reduced the search to a verified finite set.

The role of the height becomes especially clear after a basis $P_1,\ldots,P_r$ of the free part is known. A class has the form

$$
x=T+n_1P_1+\cdots+n_rP_r,
$$

and its height is the quadratic form

$$
\widehat h_\Theta(x)
=(n_1,\ldots,n_r)H(n_1,\ldots,n_r)^{\mathsf t}. \tag{12.8}
$$

because torsion pairs trivially, where $H=(\langle P_i,P_j\rangle_\Theta)$. If the least eigenvalue of $H$ is $\lambda>0$, then

$$
\widehat h_\Theta(x)\ge\lambda\sum_i n_i^2.
$$

A proven height upper bound therefore gives a finite coefficient box. Conversely, reduction conditions give congruences on the vector $(n_i)$. Effective arguments are strongest when the archimedean ellipsoid from height and the nonarchimedean congruences from reduction are used together.

## 13. Rational-point geometry in genus two

The preceding chapters provide several kinds of finiteness, none of which alone is an exhaustive rational-point proof. This chapter separates degree-one points from degree-two divisors, full Mordell--Weil information from finite-index information, and necessary local survival from a genuine completeness certificate.

### 13.1 Degree one versus degree two information

The Abel embedding and symmetric-square blowup encode different levels of information:

$$
C(K)\hookrightarrow J(K),\qquad
C^{(2)}(K)\twoheadrightarrow J(K). \tag{13.1}
$$

The first map loses no point information but does not reach most divisor classes. The second reaches every class but loses the whole canonical pencil at $\kappa_b$ and does not distinguish rational points from quadratic pairs.

Suppose $\xi\ne\kappa_b$ and let $D_\xi$ be its unique effective degree-two representative. Then $\xi$ lies in the sum set $j_b(C(K))+j_b(C(K))$ exactly when $D_\xi$ splits as two $K$-rational points. It lies in $2j_b(C(K))$ exactly when $D_\xi=2P$ for a rational point $P$. A nonsplit degree-two closed point gives a rational Jacobian class without giving a rational point of $C$.

This distinction prevents a frequent error: surjectivity of $C^{(2)}(K)\to J(K)$ does not imply that every Jacobian class is a sum of two rational curve points.

### 13.2 Known classes and unknown points

Let $B\subset C(K)$ be a finite set of known points, such as cusps or degenerate moduli points. Their Abel images generate a subgroup

$$
G_B=\langle j_b(P):P\in B\rangle\subseteq J(K). \tag{13.2}
$$

There are three increasingly strong possible statements:

1. the known classes lie in $J(K)$;
2. they generate a finite-index subgroup of $J(K)$;
3. they generate all of $J(K)$, including torsion and saturation.

Only the third permits every unknown point to be written in known generators without an index ambiguity. Even then, membership in the embedded theta curve must be tested. A finite-index assertion can miss classes in the omitted cosets, and reduction modulo primes dividing the index may fail to detect that omission.

Heights can certify independence of known classes through a nonzero Gram determinant. They do not by themselves certify saturation. Reduction orders and descent information are the natural complements.

### 13.3 Finite quotients and surviving residue classes

Choose generators for a subgroup $G\subseteq J(K)$ of finite index. For a good place $v$, reduction factors the coefficient lattice through a finite quotient. The inverse image of $j(C(k_v))$ is therefore a finite union of cosets of a finite-index sublattice of $G$.

For several places $v_1,\ldots,v_s$, the simultaneous condition is the intersection of these coset unions. The Chinese remainder principle applies to the coefficient lattice only after accounting for common factors in the finite group orders and for the kernel of each reduction map. The geometry supplies the subsets $j(C(k_v))$; the group structure supplies the congruences.

The exceptional class $\kappa_b$ should be isolated before interpreting degree-two representatives. It has many divisors above it, but only the points among those divisors that split appropriately can contribute to a degree-one rational-point problem.

### 13.4 Completeness criteria and their boundaries

A rational-point determination is complete when two facts have both been proved:

- every displayed point really lies on $C$ and has the claimed arithmetic meaning;
- every other possible global class has been excluded.

The second fact may follow from an exhaustive finite quotient argument on a saturated Mordell--Weil group, or from a height bound followed by complete enumeration, or from a quotient whose fibers are fully understood. Merely checking many primes, finding no new small points, or matching the expected number of cusps is not a completeness proof.

A quotient argument has its own exact criterion. Let $\varphi:J\to A$ be a homomorphism to an abelian variety whose rational group is known. If the finite set

$$
\varphi(j_b(C(K)))\subseteq A(K)
$$

is determined, one must still determine, for every surviving $a\in A(K)$, the rational points of

$$
C\cap j_b^{-1}(\varphi^{-1}(a)).
$$

When $A$ is elliptic this fiber condition can often be expressed by a degree-two map from $C$, but its two geometric points may be conjugate or ramified. A rank-zero quotient is powerful because its rational image is finite, not because quotienting preserves the Abel embedding.

The present geometry supplies the exact interfaces required by such a proof: injective degree-one Abel maps, unique noncanonical degree-two representatives, finite-field theta subsets, specialization compatibility, and height discreteness. It does not replace the separate arithmetic certificates that determine the Mordell--Weil group and exhaust its relevant cosets.

## 14. The modular genus-two range

The abstract package is needed for two particular modular handoffs: the pointed curve $X_1(13)$ and the mixed-seven auxiliary curve. This chapter states exactly which geometric conclusions pass to those problems and keeps the moduli interpretation separate from the divisor-class calculation.

### 14.1 From a modular point to a divisor class

A modular curve point represents level structure only after the fine/coarse and field-of-definition conditions have been checked. Once an actual $K$-rational point $P$ on a smooth proper genus-two modular curve $C$ is obtained and a rational cusp $b$ is chosen, the geometric passage is canonical:

$$
P\longmapsto[P-b]\in J(K). \tag{14.1}
$$

At a good prime, the stable level object specializes, the point reduces on the proper curve, and (10.4) specializes its divisor class. At a multiplicative place the modular point may reduce to a cusp, while the Jacobian class reduces to the difference of two cusp classes.

The modular interpretation and the genus-two geometry have different roles. The former explains which rational points correspond to elliptic curves or level structures and which are cuspidal or degenerate. The latter supplies an injective embedding and reduction constraints. Neither role may be inferred from the other.

### 14.2 Cusps, degeneracy points, and base divisors

A cusp rational over $K$ is the ideal base point. If individual cusps are not rational but a Galois-stable divisor $B$ of degree $d$ is, one can instead use

$$
C\longrightarrow\operatorname{Pic}^0(C),\qquad
P\longmapsto[dP-B]. \tag{14.2}
$$

This map is defined over $K$, but multiplication by $d$ can weaken injectivity after passage to quotients or reduction at primes dividing $d$. A rational degree-one cusp avoids this complication.

Degenerate moduli points may be interior points of an auxiliary curve even when they correspond to excluded elliptic data. Their divisor classes are nonetheless legitimate. A final arithmetic classification must first determine all rational points on the complete curve and only then interpret which are cuspidal, degenerate, or genuinely modular.

### 14.3 The range needed for $X_1(13)$

The curve $X_1(13)$ belongs to the genus-two range and carries rational cuspidal data suitable for an Abel--Jacobi embedding. The precise geometric package needed for its rational-point problem is the following:

Its genus can be checked directly from the modular-curve canonical formula. For prime $p\ge5$, the image of $\Gamma_1(p)$ in $\operatorname{PSL}_2(\mathbf Z)$ is torsion-free, has index

$$
\mu=\frac{p^2-1}{2},
$$

and has $p-1$ geometric cusps. The first formula follows by choosing a nonzero first column modulo $p$, dividing the $\operatorname{SL}_2$ index by two because $-I\notin\Gamma_1(p)$, and the second follows by the primitive cusp-orbit calculation. Therefore

$$
g(X_1(p))
=1+\frac{p^2-1}{24}-\frac{p-1}{2}
=\frac{(p-5)(p-7)}{24}. \tag{14.3}
$$

At $p=13$ this gives

$$
g(X_1(13))=\frac{8\cdot6}{24}=2.
$$

Thus the use of genus-two geometry is forced by the canonical calculation, not inferred from a chosen affine equation.

- a verified smooth proper genus-two model and its canonical involution;
- an identified rational cusp $b$ and the embedding $P\mapsto[P-b]$;
- the theta interpretation of the embedded curve;
- good-reduction maps to $J(\mathbf F_q)$ and the subsets coming from $C(\mathbf F_q)$;
- the distinction between rational points, quadratic effective divisors, and the exceptional canonical pencil;
- a height and finite-generation interface for any global generators used.

Nothing in this list asserts the Mordell--Weil group or the final rational-point set. Those are arithmetic conclusions requiring exact divisor-class calculations and exhaustive global certificates. The geometry here guarantees that, once such certificates are supplied, equality of Abel--Jacobi classes recovers equality of points.

### 14.4 The range needed for the mixed-seven curve

The mixed-seven auxiliary curve similarly uses genus-two geometry to encode a level problem with cuspidal or degenerate boundary points. Its modular meaning differs from that of $X_1(13)$, but the geometric handoff is the same. One must verify the model and marked points, embed using a rational base point, determine how every known boundary point reduces, and compare the embedded curve with finite reductions of its Jacobian.

For the standard model, the curve is the $C_7$ of (9.11):

$$
z^2=t(t-1)(t^3-8t^2+5t+1).
$$

The odd degree gives a rational Weierstrass point $\infty$ and

$$
K_{C_7}\sim2\infty.
$$

The rational roots $t=0$ and $t=1$ give two further rational Weierstrass points

$$
W_0=(0,0),\qquad W_1=(1,0).
$$

Their Abel classes

$$
T_0=[W_0-\infty],\qquad T_1=[W_1-\infty]. \tag{14.4}
$$

have order dividing two because $2W_i\sim2\infty$. They are nonzero by injectivity of the Abel map. They are distinct for the same reason, and therefore generate a subgroup isomorphic to $(\mathbf Z/2\mathbf Z)^2$. Indeed, if $T_0+T_1=0$, then $W_0+W_1\sim2\infty=K_C$; Proposition 4.2 would force $W_1=\iota(W_0)=W_0$, a contradiction.

This calculation shows how the abstract geometry immediately certifies visible torsion without any general group computation. The good-prime orders $12$ and $48$ from (9.13) are compatible with this subgroup but do not prove that it is all the rational torsion. Any complete rational-point determination must additionally control the remaining torsion and free rank, then test which certified classes lie on the embedded theta curve.

If the curve has additional involutions or elliptic quotients, Chapter 8 explains exactly what may be deduced: the quotient can constrain Abel images, but its fibers must be analyzed and equality in the quotient must not be promoted to equality in $J$. If a degree-two divisor survives, Chapter 7 requires checking whether it splits into rational points or represents a quadratic orbit.

The phrase “only cuspidal or degenerate points” is therefore a conclusion with two components: an exhaustive determination of points on the smooth proper curve and a separate interpretation of each point in the moduli problem. Genus-two geometry supplies the bridge but does not conflate the two.

## 15. A reusable genus-two package

The final chapter consolidates the theory into a hypothesis ledger and two theorem packages. Its role is not merely to summarize: it marks the boundary between the geometry proved here and the exact group arithmetic required to turn local constraints into complete rational-point lists.

### 15.1 Hypothesis ledger

The main assertions depend on the following exact hypotheses.

**Intrinsic geometry.** Smoothness, properness, and geometric connectedness are required for the genus, Riemann--Roch, the abelian Jacobian, and the Abel embedding. Genus exactly two forces $\deg K_C=2$ and produces the canonical double cover. A rational point is required to land canonically in $J$ rather than in a Picard torsor.

**Hyperelliptic equations.** The form $y^2=f(x)$, the sign involution, and the squarefree criterion require characteristic different from two. A squarefree polynomial of degree five or six gives genus two only after taking the smooth projective model and checking infinity. The canonical cover remains separable in characteristic two, but it uses $y^2+h(x)y=f(x)$ with $h\ne0$, has the translation involution $y\mapsto y+h(x)$, and requires a different smoothness and ramification test.

**Finite-field results.** The Frobenius formulas and Weil bounds require a smooth proper geometrically connected curve over a finite field. The formula $\#J(\mathbf F_q)=P_C(1)$ uses the Jacobian of that curve. The blowup count requires a rational blowup center, supplied by a rational base point.

**Reduction.** The clean commutative reduction square requires a smooth proper model over the valuation ring. Prime-to-$p$ torsion injectivity uses good reduction. At semistable reduction, generalized Jacobians and component groups replace an abelian special fiber.

**Global arithmetic.** Finite generation and the canonical-height lattice are invoked over number fields. A known finite-index subgroup is not silently treated as the full Mordell--Weil group. Survival of local tests is never treated as proof of a global point.

### 15.2 Geometric theorem package

Let $C/k$ be a smooth proper geometrically connected genus-two curve.

1. The canonical system is base-point free and defines a separable degree-two map to $\mathbf P^1$. It has the canonical involution $\iota$ and canonical fibers $P+\iota(P)$.
2. An effective divisor $D$ of degree two has $h^0(D)=2$ exactly when $D\sim K_C$; otherwise $h^0(D)=1$ and $D$ is unique in its class.
3. The Jacobian $J$ is an abelian surface with canonical principal polarization. After choosing $b\in C(k)$, the Abel map $j_b$ is a closed immersion and its image is a theta divisor.
4. The theta divisor satisfies $\Theta^2=2$. Distinct translates meet in a zero-dimensional scheme of length two.
5. The degree-two Abel map is the blowup

   $$
   C^{(2)}\simeq\operatorname{Bl}_{[K_C-2b]}J.
   $$

   Its exceptional curve is the canonical pencil. Every other degree-two class has a unique effective representative.
6. Every Jacobian point is a sum of two geometric points on the Abel curve, uniquely up to the canonical-pair exception.

Each assertion is compatible with field extension. These statements constitute the exact geometric reason genus-two arithmetic can be made explicit.

### 15.3 Arithmetic theorem package

Over a finite field $\mathbf F_q$, the curve has Frobenius polynomial (9.1), satisfies

$$
|\#C(\mathbf F_{q^n})-(q^n+1)|\le4q^{n/2},
$$

and obeys

$$
\#J(\mathbf F_q)
=\frac{\#C(\mathbf F_q)^2+\#C(\mathbf F_{q^2})}{2}-q.
$$

Over a local field with good reduction, points and Abel classes specialize compatibly, and prime-to-residue-characteristic torsion injects under reduction. Over a number field, $J(K)$ is finitely generated and the theta height makes its free quotient a Euclidean lattice.

For rational-point work, these facts combine as

$$
C(K)\hookrightarrow J(K)
\longrightarrow\prod_{v\in S}J(k_v), \tag{15.1}
$$

with the image in each factor constrained to the embedded finite set $j(C(k_v))$. A complete determination additionally requires certified global generators or controlled finite index, saturation at relevant primes, and an exhaustive argument in the resulting finite quotients or bounded height region.

### 15.4 Conclusion

Genus two turns the canonical divisor into a double cover, and that double cover governs the entire small-divisor geometry. Its fibers are exactly the exceptional degree-two divisors. Its involution becomes inversion up to translation on the Jacobian. Its tangent directions control intersections of theta translates. The one-dimensional canonical pencil becomes the exceptional curve when the symmetric square is blown down to the Jacobian.

The Jacobian then supplies the group that the curve itself lacks. The Abel--Jacobi map embeds the curve as the smooth theta divisor of a principally polarized abelian surface. Every divisor class is represented in degree two, but only the canonical class has many representatives. This precise exception explains both the effectiveness and the limits of passing from points to divisor classes.

Arithmetic respects the geometry. Frobenius measures the finite-field curve and its Jacobian; proper models specialize points and classes together; formal groups protect prime-to-residue-characteristic torsion; theta heights turn global classes into a lattice. For modular genus-two curves, a cusp fixes the origin and converts a moduli point into a class that can be compared at many places.

The resulting package is deliberately exact about what has and has not been proved. Geometry gives injectivity, divisor uniqueness, the blowup, and compatible reduction. It does not manufacture a Mordell--Weil basis or turn local survival into global existence. Once those arithmetic certificates are supplied, however, the genus-two geometry has no hidden ambiguity: divisor classes recover points, canonical exceptions are isolated, and the rational-point problem becomes a finite, verifiable intersection between a theta curve and a finitely generated group.
