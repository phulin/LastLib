# Local Geometry of Hilbert--Blumenthal Moduli

## Contents

- [1. From a global moduli space to local arithmetic](#1-from-a-global-moduli-space-to-local-arithmetic)
  - [1.1 Why local points are the missing input](#11-why-local-points-are-the-missing-input)
  - [1.2 Standing data and conventions](#12-standing-data-and-conventions)
  - [1.3 The five local conditions](#13-the-five-local-conditions)
  - [1.4 What a local construction must prove](#14-what-a-local-construction-must-prove)
- [2. Integral points, residue tubes, and extension](#2-integral-points-residue-tubes-and-extension)
  - [2.1 Models and integral points](#21-models-and-integral-points)
  - [2.2 Residue tubes are open](#22-residue-tubes-are-open)
  - [2.3 Smooth lifting](#23-smooth-lifting)
  - [2.4 Finite etale covers over a local field](#24-finite-etale-covers-over-a-local-field)
  - [2.5 Reduction is not a property of an arbitrary presentation](#25-reduction-is-not-a-property-of-an-arbitrary-presentation)
- [3. A supply of real-multiplication abelian varieties](#3-a-supply-of-real-multiplication-abelian-varieties)
  - [3.1 The Serre tensor construction](#31-the-serre-tensor-construction)
  - [3.2 Duality and the polarization module](#32-duality-and-the-polarization-module)
  - [3.3 The determinant condition](#33-the-determinant-condition)
  - [3.4 Torsion and pairings](#34-torsion-and-pairings)
  - [3.5 Which polarization types this construction reaches](#35-which-polarization-types-this-construction-reaches)
- [4. Real local points](#4-real-local-points)
  - [4.1 Real points are component data](#41-real-points-are-component-data)
  - [4.2 An explicit real construction](#42-an-explicit-real-construction)
  - [4.3 Odd involutions and paired frames](#43-odd-involutions-and-paired-frames)
  - [4.4 Openness at infinity](#44-openness-at-infinity)
- [5. Good integral points away from the level primes](#5-good-integral-points-away-from-the-level-primes)
  - [5.1 Smooth special fibers give good points](#51-smooth-special-fibers-give-good-points)
  - [5.2 Producing points after an unramified extension](#52-producing-points-after-an-unramified-extension)
  - [5.3 Lifting torsion frames](#53-lifting-torsion-frames)
  - [5.4 The good-reduction neighborhood](#54-the-good-reduction-neighborhood)
- [6. Ordinary points at a residue-characteristic level](#6-ordinary-points-at-a-residue-characteristic-level)
  - [6.1 Ordinary means multiplicative plus etale](#61-ordinary-means-multiplicative-plus-etale)
  - [6.2 Explicit ordinary elliptic curves](#62-explicit-ordinary-elliptic-curves)
  - [6.3 Tensoring produces ordinary Hilbert--Blumenthal points](#63-tensoring-produces-ordinary-hilbert--blumenthal-points)
  - [6.4 The ordinary deformation coordinate](#64-the-ordinary-deformation-coordinate)
  - [6.5 Ordinary residue tubes](#65-ordinary-residue-tubes)
- [7. Nonordinary finite-flat points](#7-nonordinary-finite-flat-points)
  - [7.1 Why nonordinary requires a different argument](#71-why-nonordinary-requires-a-different-argument)
  - [7.2 Supersingular seed points](#72-supersingular-seed-points)
  - [7.3 Local--local finite-flat torsion](#73-local--local-finite-flat-torsion)
  - [7.4 Exact finite-flat representations and admissibility](#74-exact-finite-flat-representations-and-admissibility)
  - [7.5 The nonordinary residue tube](#75-the-nonordinary-residue-tube)
- [8. Semistable points from Tate curves](#8-semistable-points-from-tate-curves)
  - [8.1 A degeneration with a controllable parameter](#81-a-degeneration-with-a-controllable-parameter)
  - [8.2 Tensoring the Tate curve](#82-tensoring-the-tate-curve)
  - [8.3 Torsion and the Kummer class](#83-torsion-and-the-kummer-class)
  - [8.4 Finite flatness at the coefficient prime](#84-finite-flatness-at-the-coefficient-prime)
  - [8.5 Semistable neighborhoods](#85-semistable-neighborhoods)
- [9. Twisted two-prime covers and local solvability](#9-twisted-two-prime-covers-and-local-solvability)
  - [9.1 What a point of the twist says](#91-what-a-point-of-the-twist-says)
  - [9.2 The determinant obstruction](#92-the-determinant-obstruction)
  - [9.3 Good-prime solvability](#93-good-prime-solvability)
  - [9.4 Coefficient-prime solvability](#94-coefficient-prime-solvability)
  - [9.5 Simultaneous frames](#95-simultaneous-frames)
- [10. Openness of the exact local conditions](#10-openness-of-the-exact-local-conditions)
  - [10.1 Three different meanings of openness](#101-three-different-meanings-of-openness)
  - [10.2 Good and ordinary loci](#102-good-and-ordinary-loci)
  - [10.3 Nonordinary finite-flat tubes](#103-nonordinary-finite-flat-tubes)
  - [10.4 Semistable and Kummer conditions](#104-semistable-and-kummer-conditions)
  - [10.5 Frame conditions are locally constant](#105-frame-conditions-are-locally-constant)
- [11. Persistence under extension of local fields](#11-persistence-under-extension-of-local-fields)
  - [11.1 Integral and good reduction](#111-integral-and-good-reduction)
  - [11.2 Ordinary and local--local type](#112-ordinary-and-local--local-type)
  - [11.3 Semistability and splitness](#113-semistability-and-splitness)
  - [11.4 Finite-flat representations](#114-finite-flat-representations)
  - [11.5 What is not persistent](#115-what-is-not-persistent)
- [12. Combining conditions without losing a component](#12-combining-conditions-without-losing-a-component)
  - [12.1 Intersections must be witnessed](#121-intersections-must-be-witnessed)
  - [12.2 Component bookkeeping](#122-component-bookkeeping)
  - [12.3 Avoiding degeneracy loci](#123-avoiding-degeneracy-loci)
  - [12.4 A simultaneous local-neighborhood theorem](#124-a-simultaneous-local-neighborhood-theorem)
- [13. The Moret--Bailly local package](#13-the-moret--bailly-local-package)
  - [13.1 The input ledger](#131-the-input-ledger)
  - [13.2 The local construction theorem](#132-the-local-construction-theorem)
  - [13.3 Passing from neighborhoods to every conjugate](#133-passing-from-neighborhoods-to-every-conjugate)
  - [13.4 Failure modes](#134-failure-modes)
- [14. Conclusion](#14-conclusion)
  - [14.1 The local dictionary](#141-the-local-dictionary)
  - [14.2 The package established](#142-the-package-established)

## 1. From a global moduli space to local arithmetic

### 1.1 Why local points are the missing input

The preceding construction of Hilbert--Blumenthal moduli solves a global geometric problem. It gives a smooth fine scheme, pairing-preserving torsion-frame covers, twists by prescribed representations, and geometrically connected components. An arithmetic approximation theorem, however, does not manufacture a point on such a space from geometry alone. At every selected completion it must be given a nonempty open set of points having the required local behavior.

This changes the nature of the question. It is not enough to know that some Hilbert--Blumenthal abelian variety exists over an algebraic closure. One needs an object over a specified local field, on the specified twist and component, and one must know that nearby objects retain the desired condition. At a real place, “nearby” refers to the ordinary real topology. At a finite place, it refers to the topology defined by the valuation. At a residue-characteristic level prime, generic torsion is etale but its integral model is not, so a basis of geometric points does not see the finite-flat condition. At a semistable place, the abelian variety need not extend as an abelian scheme at all.

The purpose of this book is to turn those distinctions into a reusable local package. We construct seed points of five kinds: real, good, ordinary, nonordinary finite-flat, and semistable. We then put each seed inside an explicit local neighborhood and prove persistence under the field extensions that occur after specialization. The endpoint is not a vague assertion of local solvability. It is a theorem whose hypotheses say exactly when the local point lies on the required two-prime twist and whose conclusion supplies the open subsets demanded by arithmetic approximation.

### 1.2 Standing data and conventions

Fix a totally real field $F$ of degree $d$, with ring of integers $\mathcal O_F$, different $\mathfrak d_F$, and discriminant $D_F$. Fix an ordered invertible fractional ideal $(\mathfrak c,\mathfrak c^+)$, auxiliary principal level $\mathfrak n=N\mathcal O_F$ with $N\geq3$, and two distinct prime ideals

$$
\mathfrak p\mid p,
\qquad
\mathfrak q\mid q
$$

of distinct rational residue characteristics. Unless a section explicitly studies one of $p$ or $q$ as the residue characteristic, all primes dividing $D_FNpq\mathfrak c\mathfrak n$ are excluded. Thus the coefficient algebra is unramified, the polarization pairing is perfect, and the displayed prime-to-residue-characteristic torsion is finite etale.

Write $H=H_{\mathfrak c,\mathfrak n}$ for the fine Hilbert--Blumenthal scheme. Its points are quadruples

$$
(A,\iota,\lambda,\eta_{\mathfrak n}),
$$

where $A$ has relative dimension $d$, $\iota:\mathcal O_F\to\operatorname{End}(A)$ satisfies the Hilbert determinant condition, $\lambda$ identifies $(\mathfrak c,\mathfrak c^+)$ with the ordered polarization module and makes $A\otimes_{\mathcal O_F}\mathfrak c\to A^\vee$ an isomorphism, and $\eta_{\mathfrak n}$ is the fixed neat auxiliary level. The two-prime twist $Y\to H$ additionally carries pairing-preserving isomorphisms

$$
\alpha_{\mathfrak p}:V_{\mathfrak p}\xrightarrow{\sim}A[\mathfrak p],
\qquad
\alpha_{\mathfrak q}:V_{\mathfrak q}\xrightarrow{\sim}A[\mathfrak q].
\tag{1.1}
$$

Here each $V_{\mathfrak r}$ has determinant equal, as a local system with a specified isomorphism, to

$$
\mathscr D_{\mathfrak r}
=(\mathfrak d_F^{-1}\mathfrak c^{-1}\otimes k_{\mathfrak r})(1).
\tag{1.2}
$$

This determinant identification is part of the datum. Equality of determinant characters without a chosen identification does not define the paired twist.

At a finite place let $K$ be a finite extension of $\mathbf Q_r$, let $R$ be its valuation ring, $\pi$ a uniformizer, and $k$ its finite residue field. We normalize $v_K(\pi)=1$. An **unramified local base** means $K=W(k)[1/r]$, equivalently $v_K(r)=1$. Completion, henselization, and unramified extension are never silently identified.

### 1.3 The five local conditions

The words used in the catalog have precise meanings.

A **real point** is a point of a selected real connected component of $Y(\mathbf R)$. For odd torsion primes its prescribed representations must be odd: complex conjugation has eigenvalues $1$ and $-1$ and determinant $-1$.

A **good point** over $K$ is one whose underlying abelian variety, real multiplication, polarization, and prime-to-$r$ auxiliary level extend over $R$ to the corresponding smooth integral moduli problem. In particular, $A$ has good reduction.

Suppose $r=p$ and $p$ is unramified in $F$. A good point is **ordinary at $\mathfrak p$** if the $\mathfrak p$-divisible direction of its special fiber has etale and multiplicative height-one parts. In the tensor examples below, this is equivalent to ordinary reduction of the seed elliptic curve.

A good point is **nonordinary finite-flat at $\mathfrak p$** if $A[\mathfrak p]$ extends to a finite flat $k_{\mathfrak p}$-module scheme over $R$ and its special fiber has a local--local factor. Good reduction automatically supplies the finite-flat extension; the adjective records the exact special-fiber type. When a prescribed representation is involved, “finite flat” always means that the given generic representation is the generic fiber of a specified finite flat model, not merely that its semisimplification has plausible characters.

A **semistable point** is one whose abelian variety has semiabelian reduction: the identity component of the special fiber is an extension of an abelian variety by a torus. Our explicit points have totally toric, split multiplicative reduction. They are constructed from Tate curves, so their degeneration parameter, torsion extension, and behavior under base change are all visible.

These conditions overlap. An ordinary point and a nonordinary point are both good. A semistable point may be good, but in this book the term is used mainly for the genuinely multiplicative case. Finite flatness of one torsion layer does not imply good reduction of the abelian variety; a Tate curve at the coefficient prime is the decisive counterexample.

### 1.4 What a local construction must prove

For later specialization a local seed must pass four tests.

First, it must exist on the chosen moduli problem, including polarization type, component, auxiliary level, and both determinant-compatible frames. Second, its arithmetic condition must be stated intrinsically: good reduction must not depend on a nonminimal equation, and finite flatness must concern a group scheme over $R$. Third, the point must lie in a nonempty open subset of local points all of whose members satisfy the same required condition. Fourth, the condition must persist under the completion extensions actually allowed in the global construction.

The third test is subtle for nonordinary reduction. The ordinary locus is Zariski open in the special fiber, whereas the nonordinary locus is closed. Nevertheless, the inverse image of one nonordinary special point under reduction is an open subset of $H(K)$. This **residue tube** is the correct local-open condition. It remembers an exact reduction rather than pretending that nonordinarity is globally open.

The fourth test also requires restraint. Good reduction, ordinarity, local--local type, semistability, and finite flatness persist after the extensions stated later. A numerical valuation such as $v(q)=m$ does not persist unchanged under ramification: it becomes $e m$. Splitness may improve under an unramified quadratic extension. An exact frame over $K$ restricts to a frame over an extension, but descent in the reverse direction is a separate problem.

## 2. Integral points, residue tubes, and extension

### 2.1 Models and integral points

Let $\mathcal X$ be a separated scheme of finite type over a complete DVR $R$, and write $X=\mathcal X_K$. An $R$-point gives a $K$-point by restriction. Because $\mathcal X$ is separated, two $R$-points with the same generic point agree: their equalizer is closed and contains the generic point of $\operatorname{Spec}R$, hence contains its closure. We may therefore regard $\mathcal X(R)$ as a subset of $X(K)$.

This subset need not be all of $X(K)$ when $\mathcal X$ is not proper. The missing points are precisely where denominators drive the generic point toward the boundary. If $\mathcal X$ is proper, the valuative criterion gives $\mathcal X(R)=X(K)$. Hilbert moduli with fixed level is generally quasi-projective, so local arguments must work inside an integral chart rather than invoke properness that is not present.

Choose an affine open $\mathcal U=\operatorname{Spec}B\subset\mathcal X$ and generators $b_1,\ldots,b_m$ of $B$ as an $R$-algebra. A $K$-point belongs to $\mathcal U(R)$ exactly when all coordinate values $b_i(x)$ lie in $R$ and satisfy the defining relations. Since $R\subset K$ is open and closed, integrality of finitely many coordinates is a local-field condition. This gives the first elementary source of open neighborhoods.

### 2.2 Residue tubes are open

For $n\geq1$, reduction defines

$$
\operatorname{red}_n:\mathcal X(R)\longrightarrow\mathcal X(R/\pi^nR).
$$

For a point $\bar x_n$ of the target, define its level-$n$ tube by

$$
]\bar x_n[_{\mathcal X}
=\{x\in\mathcal X(R):\operatorname{red}_n(x)=\bar x_n\}.
\tag{2.1}
$$

**Proposition 2.1 (openness of tubes).** Every set (2.1) is open in $X(K)$. If $\mathcal X$ is smooth at the reduction $\bar x$ of $\bar x_n$, then every nonempty tube contains an open ball of dimension $\dim_{\bar x}\mathcal X_k$ in etale coordinates.

**Proof.** Work first in an affine chart containing $\bar x$. Equality modulo $\pi^n$ of the finitely many coordinate functions is the intersection of conditions

$$
|b_i(x)-b_i(x_0)|\leq |\pi|^n,
$$

which are open as well as closed in a nonarchimedean field. Thus the tube is open in the affine $K$-points. Separatedness lets these affine descriptions agree on overlaps.

If $\mathcal X/R$ is smooth at $\bar x$, there is, after shrinking, an etale map to $\mathbf A_R^s$. The multivariable Hensel lemma makes this map a local homeomorphism on $R$-points near any lift. The congruence class in $R^s$ is an ordinary product ball, and its inverse image gives the final assertion. $\square$

The result is stronger than local constancy of a finite invariant. It says that fixing the entire object modulo $\pi^n$ leaves a full-dimensional set of characteristic-zero lifts. This is why a closed condition on the special fiber can still furnish an open local condition upstairs.

### 2.3 Smooth lifting

The existence of a special-fiber point is useful only if it lifts.

**Theorem 2.2 (smooth lifting).** Let $R$ be complete henselian and let $\mathcal X/R$ be smooth at $x_0\in\mathcal X(k)$. Then $x_0$ lifts to an $R$-point. More generally, every lift modulo $\pi^n$ extends to a lift modulo $\pi^{n+1}$, and the inverse limit is an $R$-point.

**Proof strategy.** Smoothness says that every square-zero extension admits a lift locally. The successive kernels $\pi^nR/\pi^{n+1}R$ are square-zero for the relevant quotient, and completeness assembles the compatible approximations.

**Proof.** Choose an etale neighborhood $\mathcal U\to\mathbf A_R^s$ of $x_0$. Lift the coordinates of its image arbitrarily from $k$ to $R$. Formal etaleness gives a unique compatible lift in $\mathcal U(R/\pi^n)$ at every level. Since $\mathcal U$ is of finite presentation, an $R$-point is the same as a compatible system of points over $R/\pi^n$; completeness of $R$ supplies the limit. Equivalently, one may apply Hensel's lemma to etale local equations. $\square$

Applied to the good integral Hilbert moduli problem at an unramified coefficient prime, smoothness follows by lifting one Hodge line for each embedding of $F$. Applied away from the level primes, the torsion-frame cover is finite etale over that smooth model and is smooth as well.

### 2.4 Finite etale covers over a local field

Let $f:Y\to X$ be finite etale over $K$. A point $y\in Y(K)$ has neighborhoods on which $f$ is a homeomorphism.

**Proposition 2.3 (local sections).** There are open neighborhoods $y\in V\subset Y(K)$ and $x=f(y)\in U\subset X(K)$ such that $f:V\to U$ is a homeomorphism. Consequently the image of $Y(K)$ in $X(K)$ is open.

**Proof.** Choose affine neighborhoods and write the chosen factor of the finite etale algebra near $y$ in the form $A[T]/(g)$ with $g'(y)$ a unit after shrinking. For points of $X(K)$ sufficiently close to $x$, the coefficients of $g$ remain close to their original values. The simple-root form of Hensel's lemma gives a unique root close to $y$, continuously in the coefficients. This root defines the inverse section. $\square$

This is the precise reason a fixed torsion representation is locally constant on a framed moduli space. Once (1.1) exists at one point, the finite etale isomorphism scheme gives it throughout a sufficiently small neighborhood. No choice of matrices has to be continued by hand.

At a residue-characteristic level prime the integral frame cover is not etale, but its generic fiber still is: the characteristic of $K$ is zero. Proposition 2.3 therefore preserves the generic representation. Finite flatness is then preserved because the same generic representation retains its already constructed finite flat model. This reasoning proves existence of a finite-flat model nearby; it does not identify that model with the torsion of a good integral abelian scheme unless goodness is imposed separately.

### 2.5 Reduction is not a property of an arbitrary presentation

An abelian variety has good reduction if it extends to an abelian scheme over $R$. This definition is intrinsic. For an elliptic curve, a Weierstrass equation with unit discriminant proves good reduction, but a nonminimal equation can have positive discriminant valuation even when the curve has good reduction. Conversely, an integral equation with singular special fiber does not prove that the curve lacks a different smooth model until minimality is controlled.

The same warning applies to Hilbert--Blumenthal objects. An arbitrary collection of matrices for the $\mathcal O_F$-action can acquire denominators after a change of basis even though the endomorphisms extend intrinsically. We will either construct an actual abelian scheme over $R$ or work in the integral moduli scheme. Reduction type is never inferred from a convenient generic presentation alone.

## 3. A supply of real-multiplication abelian varieties

### 3.1 The Serre tensor construction

The most concrete local points come from elliptic curves. Let $S$ be a scheme, let $E/S$ be an elliptic scheme or an elliptic curve over a field, and let $I$ be an invertible fractional $\mathcal O_F$-ideal. As a free $\mathbf Z$-module, $I$ has rank $d$. Define

$$
A=E\otimes_{\mathbf Z}I.
\tag{3.1}
$$

Choose temporarily a $\mathbf Z$-basis of $I$. Then (3.1) is $E^d$. A different basis acts through an element of $\operatorname{GL}_d(\mathbf Z)$, and the corresponding integral linear combination maps identify the two products. Descent therefore makes (3.1) independent of the basis. Multiplication on $I$ gives

$$
\iota:\mathcal O_F\longrightarrow\operatorname{End}_S(A).
$$

If $E/S$ is an abelian scheme, so is $A/S$; if $E/K$ is a Tate curve, $A/K$ is still an abelian variety and its semiabelian model is the corresponding tensor of the Tate model.

The construction commutes with arbitrary base change because it is built from finite products and integral idempotent matrices. It also carries isogenies of elliptic curves to $\mathcal O_F$-linear isogenies of the resulting abelian varieties.

### 3.2 Duality and the polarization module

Let

$$
I^\dagger=\operatorname{Hom}_{\mathbf Z}(I,\mathbf Z).
$$

Trace duality identifies

$$
I^\dagger=\mathfrak d_F^{-1}I^{-1}
\tag{3.2}
$$

inside $F$. If $E$ is identified with its dual by its canonical principal polarization, product duality gives

$$
A^\vee\simeq E\otimes I^\dagger.
\tag{3.3}
$$

An $\mathcal O_F$-linear symmetric map $A\to A^\vee$ is therefore multiplication by an element of

$$
\operatorname{Hom}_{\mathcal O_F}(I,I^\dagger)
=I^{-1}I^\dagger
=\mathfrak d_F^{-1}I^{-2}.
\tag{3.4}
$$

There is a small point hidden in this assertion: an elliptic curve can have extra endomorphisms, especially after supersingular reduction. They do not create extra symmetric directions. Choose a prime $\ell$ invertible on the base. Under the canonical principal polarization, the Rosati adjoint on the rank-two Tate module is adjoint with respect to its perfect alternating form. If a $2\times2$ matrix $M$ is self-adjoint for such a form, then

$$
M^tJ=JM,
\qquad
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
$$

and direct multiplication forces $M$ to be scalar. Faithfulness of the Tate module action makes every symmetric rational endomorphism of $E$ a rational scalar; integrality makes it an integer. Hence

$$
\operatorname{End}^{\mathrm{sym}}(E)=\mathbf Z
$$

even in the CM and supersingular cases. Tensor--Hom adjunction now gives exactly (3.4), with no additional symmetric factor.

Positivity of the product Riemann form says exactly that this element is totally positive. Put

$$
\mathfrak c_I=\mathfrak d_F^{-1}I^{-2}.
\tag{3.5}
$$

**Proposition 3.1.** The ordered polarization module of $A=E\otimes I$ is canonically

$$
(\mathcal P(A),\mathcal P(A)^+)\simeq(\mathfrak c_I,\mathfrak c_I^+),
$$

and the induced tensor polarization

$$
A\otimes_{\mathcal O_F}\mathfrak c_I\xrightarrow{\sim}A^\vee
\tag{3.6}
$$

is an isomorphism.

**Proof.** Formula (3.4) identifies the symmetric $\mathcal O_F$-linear homomorphisms. On every real embedding factor, multiplication by $c\in F$ scales the positive form of $E$ by the real number $\tau(c)$, so it is a polarization precisely when every $\tau(c)>0$. Finally,

$$
I\mathfrak c_I
=I\mathfrak d_F^{-1}I^{-2}
=\mathfrak d_F^{-1}I^{-1}
=I^\dagger.
$$

Tensoring $E$ with this equality identifies the source of (3.6) with (3.3). $\square$

This computation explains both the inverse different in the determinant pairing and the square ideal in changes of polarization type. Neither is a normalization convention.

For example, take $F=\mathbf Q(\sqrt5)$ and $I=\mathcal O_F$. Then $A=E^2$ as an abelian scheme after choosing the basis $1,(1+\sqrt5)/2$, but the $\mathcal O_F$-action is not the scalar action on the two factors. The polarization module is $\mathfrak d_F^{-1}$, not $\mathcal O_F$. The trace-dual basis has denominators measured exactly by the different. Forgetting those denominators would predict the wrong determinant line on torsion at the prime above $5$, which is also why our good-prime tensor calculations exclude the ramified coefficient prime.

### 3.3 The determinant condition

The Lie algebra is

$$
\operatorname{Lie}(A/S)
\simeq\operatorname{Lie}(E/S)\otimes_{\mathbf Z}I.
\tag{3.7}
$$

When $D_F$ is invertible on $S$, the algebra $\mathcal O_F\otimes\mathcal O_S$ is etale-locally a product of $d$ copies of $\mathcal O_S$. The invertible ideal $I$ is locally free of rank one over this product. Since $\operatorname{Lie}(E/S)$ is a line, (3.7) is locally free of rank one over $\mathcal O_F\otimes\mathcal O_S$. Hence for every $a\in\mathcal O_F$,

$$
\det(T-\iota(a)\mid\operatorname{Lie}A)
=\operatorname N_{F/\mathbf Q}(T-a).
\tag{3.8}
$$

Thus the tensor construction lies on the Hilbert determinant locus. At primes ramified in $F$, equation (3.8) still holds, but it no longer by itself implies the rank-one local-model condition. Our integral constructions exclude those primes.

### 3.4 Torsion and pairings

Let $\mathfrak r$ be a prime of $F$ above a rational prime $s$ that is invertible on the base. Then

$$
A[\mathfrak r]
\simeq E[s]\otimes_{\mathbf F_s}(I/\mathfrak r I).
\tag{3.9}
$$

The right side is two-dimensional over $k_{\mathfrak r}$. The Weil pairing of $E[s]$, trace duality, and (3.6) give its alternating pairing with target

$$
(\mathfrak d_F^{-1}\mathfrak c_I^{-1}\otimes k_{\mathfrak r})(1).
$$

Since $\mathfrak c_I^{-1}=\mathfrak d_F I^2$, this coefficient line is $I^2\otimes k_{\mathfrak r}(1)$, exactly the determinant of the scalar extension in (3.9). Thus the determinant calculation agrees on both sides.

If $s$ equals the residue characteristic, formula (3.9) remains valid as a formula for finite flat group schemes when $E$ has good reduction and as a generic-fiber formula for a Tate curve. It must not be replaced by a count of geometric points: $\mu_s$ and local--local group schemes can be nonreduced in the special fiber.

### 3.5 Which polarization types this construction reaches

The explicit tensor family reaches the ordered types

$$
\mathfrak c=\mathfrak d_F^{-1}I^{-2}.
\tag{3.10}
$$

Not every narrow ideal class need have this form. It would be false to claim that tensoring one elliptic curve supplies a point on every fixed polarization component. For a general $\mathfrak c$, Book 172's complex uniformization describes precisely the determinant components selected by the moduli datum. At a finite place, Chapter 5 supplies local points on such a component after suitable residue extension once its chosen integral model has been verified to possess a special-fiber point. The tensor construction is used when (3.10) holds or when the polarization type is free to be chosen, as it is in the standard two-prime potential-modularity setup.

In ideal-class language, (3.10) says that the narrow class of $\mathfrak d_F\mathfrak c$ is a square. If the narrow class group has a nonsquare class, choosing $\mathfrak c$ in that class produces a legitimate Hilbert component that no one-elliptic-curve tensor construction reaches. This is an illuminating counterexample to the tempting assertion that every Hilbert--Blumenthal abelian variety is a power of an elliptic curve with a changed lattice.

This boundary matters in applications. One must either choose $\mathfrak c$ to fit the seed point, or first exhibit a point on the desired component by another construction. Isogeny of generic abelian varieties is not enough: it can change the integral polarization module and the determinant coefficient line.

## 4. Real local points

### 4.1 Real points are component data

At a real place there is no valuation ring and no reduction. The local condition is membership in a connected component of the real manifold $Y(\mathbf R)$. Complex uniformization writes a geometric Hilbert component as an arithmetic quotient of a product of upper and lower half-planes. Complex conjugation reverses every half-plane. A real structure is therefore an antiholomorphic involution compatible with the lattice, polarization, level, and torsion descent.

Not every complex component need have a real point over the chosen field of definition. The local theorem consequently begins with a **real-admissible component**: a component stable under conjugation whose PEL and twist descent data possess a fixed point. We now give an explicit fixed point for the tensor polarization types and identify the exact condition on torsion representations.

### 4.2 An explicit real construction

Let $E/\mathbf R$ be

$$
E:y^2=x^3-x.
\tag{4.1}
$$

Its discriminant is nonzero, so it is an elliptic curve. Equivalently, over $\mathbf C$ it is $\mathbf C/(\mathbf Z+i\mathbf Z)$, with complex conjugation induced by $z\mapsto\bar z$. For an invertible ideal $I$, put $A=E\otimes I$. Proposition 3.1 gives real multiplication and the $\mathfrak c_I$-polarization. Every construction is defined over $\mathbf R$.

For a more flexible analytic description, choose positive real numbers $y_\tau$ indexed by embeddings $\tau:F\hookrightarrow\mathbf R$ and put $z_\tau=iy_\tau$. The lattice determined by $I$ and its trace dual is stable under conjugation because $\bar z_\tau=-z_\tau$. The trace alternating form changes sign together with the complex structure and hence defines the same real polarization. Varying the $y_\tau$ fills a real cell inside the selected fixed component.

Auxiliary level must carry its natural real descent action. A literal constant symplectic basis with a trivially acted-on determinant line is generally incompatible with conjugation on roots of unity. The invariant level convention pairs the standard lattice with the cyclotomic target, and under that convention the tensor point acquires level after choosing the prescribed equivariant orbit. If a finer literal basis is required, a real point exists only when its descent involution matches that of the torsion.

### 4.3 Odd involutions and paired frames

Let $s$ be odd and let $c\in G_{\mathbf R}=\{1,c\}$ be complex conjugation. On $E[s]$, the determinant of $c$ is the mod-$s$ cyclotomic value $-1$. Since $c^2=1$ and $2$ is invertible in $\mathbf F_s$, the representation splits into its $+1$ and $-1$ eigenspaces. Their product is $-1$, so each has dimension one. In a suitable paired basis,

$$
c\longmapsto
\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
\tag{4.2}
$$

After scalar extension, the same is true on $A[\mathfrak r]$ for every $\mathfrak r\mid s$.

**Proposition 4.1 (real frame criterion).** Let $s$ be odd. A determinant-compatible rank-two $k_{\mathfrak r}$-representation $V_{\mathfrak r}$ of $G_{\mathbf R}$ admits a paired isomorphism to $A[\mathfrak r]$ if and only if $\det(c)=-1$. When it does, any isomorphism between the $+1$ lines, followed by the uniquely normalized isomorphism between the $-1$ lines, gives a paired frame.

**Proof.** Necessity follows from the pairing determinant. Conversely, $c^2=1$ makes $V_{\mathfrak r}$ semisimple with eigenvalues in $\{1,-1\}$. Determinant $-1$ forces one of each. Choose nonzero $v_+$ and $v_-$ in the two eigenspaces. Their pairing is nonzero by perfectness: each eigenline is isotropic, and if the cross-pairing vanished the form would be degenerate. Rescale $v_-$ so the pairing equals that of a chosen eigenbasis of $A[\mathfrak r]$. The resulting map is equivariant and paired. $\square$

At $s=2$, $1=-1$ and this eigenspace argument disappears. Oddness cannot be encoded by the determinant of a two-dimensional $\mathbf F_2$-representation. A dyadic real frame requires the actual involution and pairing to be compared, not merely their characters.

For two odd primes, Proposition 4.1 applies independently. Thus a tensor real point lifts to the two-prime twist exactly when both prescribed local systems are odd and their determinant identifications match (1.2).

### 4.4 Openness at infinity

The real points of a smooth variety form a real manifold. Connected components are open because manifolds are locally connected, and they are closed because components always are. The paired frame map is finite etale, hence a local diffeomorphism. Therefore a real point $y\in Y(\mathbf R)$ has a small open neighborhood contained in its chosen component and carrying the same frame descent.

Sign conditions are also open: positivity of a real number survives a small perturbation, and the positive cone in $F\otimes\mathbf R\simeq\mathbf R^d$ is the open orthant. Consequently polarization positivity, orientation of every half-plane, and the real component label remain fixed in a sufficiently small neighborhood.

This proves the archimedean input needed for a totally real specialization: one supplies such a nonempty open at every real place. Supplying it at only one real place does not prevent other embeddings of the eventual field from becoming complex.

## 5. Good integral points away from the level primes

### 5.1 Smooth special fibers give good points

Let $r$ be a rational prime outside the discriminant, polarization, auxiliary-level, and two torsion-level sets. Assume also that the restrictions of $V_{\mathfrak p}$ and $V_{\mathfrak q}$ to $G_K$ are unramified and that their determinant identifications extend over $R$. Over $R$ the Hilbert moduli functor is represented by a smooth scheme $\mathcal H$. Both $\mathfrak p$- and $\mathfrak q$-torsion, as well as the two prescribed local systems, are finite etale over $R$, so the prescribed paired-frame twist extends to a finite etale scheme

$$
\mathcal Y\longrightarrow\mathcal H_R.
\tag{5.1}
$$

An $R$-point of $\mathcal Y$ is already the desired good local point with both frames. Thus local existence reduces to the elementary problem of finding a special-fiber point and lifting it.

**Theorem 5.1 (good lifting criterion).** Let $R$ be a complete DVR of residue characteristic $r\nmid D_FNpq\mathfrak c\mathfrak n$. If $\bar y\in\mathcal Y(k)$, then $\bar y$ lifts to $y\in\mathcal Y(R)$. Its image is a Hilbert--Blumenthal abelian scheme with good reduction and the prescribed two paired frames. The full residue tube $]\bar y[_{\mathcal Y}$ is a nonempty open set of such points.

**Proof.** The base $\mathcal H_R$ is smooth. A finite etale morphism is smooth, so $\mathcal Y/R$ is smooth at $\bar y$. Theorem 2.2 lifts $\bar y$ to an $R$-point. The universal abelian scheme and all its structures pull back to $R$, proving good reduction. Proposition 2.1 makes the tube open, and every point of that tube is integral on the same moduli scheme and retains both universal frames. $\square$

This theorem deliberately assumes a point of the twist, not merely a point of the untwisted Hilbert scheme. The latter does not force either prescribed torsion representation to occur.

### 5.2 Producing points after an unramified extension

Over a finite field, a nonempty scheme of finite type always has a point after a finite extension. Indeed, a nonempty affine open has a maximal ideal, its residue field is a finite extension of the ground finite field by the weak Nullstellensatz, and the corresponding closed point becomes rational over that extension.

**Corollary 5.2 (unramified good solvability).** Suppose the special fiber $\mathcal Y_k$ is nonempty. Then there is a finite extension $k'/k$ and, for the corresponding unramified extension $R'/R$, a point $y\in\mathcal Y(R')$. In particular the good paired local condition is realizable after a finite unramified extension.

**Proof.** Choose a closed point of $\mathcal Y_k$ and let $k'$ be its residue field. Unramified local-field theory gives the unique unramified extension $R'/R$ with residue field $k'$. The closed point is then a $k'$-point, and Theorem 5.1 lifts it. $\square$

Geometric connectedness of the characteristic-zero twist is useful globally, but by itself it does not logically imply that an arbitrarily chosen integral model has nonempty special fiber: an open model can lose its entire fiber. In the applications one verifies nonemptiness in one of two ways. Either the smooth model is chosen as the actual integral moduli functor and an explicit tensor point supplies a special-fiber object, or the closure of the selected component is checked to meet the good special fiber. Corollary 5.2 begins only after that check.

### 5.3 Lifting torsion frames

Suppose first that an untwisted object $\bar A/k$ has been constructed. A paired frame of $\bar A[\mathfrak p]$ over a finite extension of $k$ exists because any two-dimensional symplectic vector space over the finite field $k_{\mathfrak p}$ has a symplectic basis. For a twisted frame, existence is equivalent to an isomorphism of the two local systems over the finite residue-field Galois group.

At a good prime these representations are unramified. They are determined by arithmetic Frobenius, and a paired isomorphism exists exactly when the two Frobenius matrices are conjugate in the relevant special linear torsor after their common determinant line has been fixed. Passing from $k$ to $k_m$ replaces Frobenius by its $m$th power. Thus extension can make a frame possible, but it does not do so for arbitrary matrices by magic; their suitable powers must be conjugate.

There is a second, more geometric route. If the whole twisted special fiber $\mathcal Y_k$ is nonempty, Corollary 5.2 chooses a closed point of it directly. That point includes both frames and automatically resolves their simultaneous conjugacy constraints. This is safer than choosing an abelian variety first and hoping its two Frobenius matrices later match prescribed ones.

Once a special-fiber frame exists, finite etaleness lifts it uniquely over each nilpotent thickening. Indeed finite etale schemes are formally etale. Therefore the lift in Theorem 5.1 carries the same exact representation, not merely its semisimplification or characteristic polynomial.

### 5.4 The good-reduction neighborhood

Let $y\in\mathcal Y(R)$ be a good point. Choose an affine integral neighborhood of its image in $\mathcal Y$ and let

$$
\Omega_y=]y\bmod\pi[_{\mathcal Y}.
\tag{5.2}
$$

Then $\Omega_y$ is open and nonempty. Every point in it extends to the same integral moduli problem and has good reduction. The reductions need not be canonically isomorphic unless the entire special point, including all coordinates, has been fixed as in (5.2); when it has, their special fibers are isomorphic as objects with real multiplication, polarization, auxiliary level, and paired frames.

This distinction lets one tune the local condition. To require only good reduction, one may take a larger union of integral tubes. To preserve a particular Frobenius action or ordinary/nonordinary type, one fixes enough special-fiber data and uses a smaller tube.

## 6. Ordinary points at a residue-characteristic level

### 6.1 Ordinary means multiplicative plus etale

Now let the residue characteristic be an odd prime $p$, assume $K/\mathbf Q_p$ is unramified, and assume $p\nmid D_F\mathfrak c\mathfrak n$. The coefficient algebra decomposes

$$
\mathcal O_F\otimes\mathbf Z_p
=\prod_{\mathfrak r\mid p}\mathcal O_{F,\mathfrak r}.
\tag{6.1}
$$

There is an integral Hilbert moduli scheme $\mathcal H^{(p)}/R$ obtained by retaining the determinant condition, $\mathfrak c$-polarization, and auxiliary level but forgetting the $\mathfrak p$-frame integrally. Neat auxiliary level still removes automorphisms. Its smoothness follows from the same infinitesimal calculation as at primes away from the frame levels: after the etale coefficient algebra is split, de Rham cohomology is a sum of rank-two symplectic modules and the Hodge bundle selects one line in each. Across a square-zero thickening, every line in a rank-two alternating module is isotropic and lifts in an affine one-dimensional family. The $d$ factors lift independently, so there are no obstructions and the relative dimension is $d$. The generic fiber of $\mathcal H^{(p)}$ is $H_K$. What fails integrally is only the claim that paired $\mathfrak p$-frames form a finite etale cover.

For an abelian scheme $A/R$ with Hilbert determinant condition, the $p$-divisible group decomposes accordingly. The $\mathfrak r$-factor has height two and dimension one over $\mathcal O_{F,\mathfrak r}$. It is **ordinary** if its connected--etale sequence has a multiplicative height-one connected part and an etale height-one quotient. At level one this has the form

$$
0\longrightarrow G^{\mathrm{mult}}[p]
\longrightarrow A[\mathfrak r]
\longrightarrow G^{\mathrm{et}}[p]
\longrightarrow0.
\tag{6.2}
$$

The sequence need not split over $R$ or on the generic Galois representation. Ordinary refers to the two slopes and the special-fiber connected--etale structure, not to a diagonal matrix presentation.

### 6.2 Explicit ordinary elliptic curves

Ordinary seed curves exist after a finite extension of every finite field of odd characteristic. We give a direct argument because local nonemptiness should not rest on an unnamed density assertion.

For $\lambda\ne0,1$, consider the Legendre curve

$$
E_\lambda:y^2=x(x-1)(x-\lambda).
\tag{6.3}
$$

Put $m=(p-1)/2$. Its Hasse invariant is, up to a nonzero scalar, the coefficient of $x^{p-1}$ in

$$
[x(x-1)(x-\lambda)]^m.
$$

Expanding gives the nonzero polynomial

$$
H_p(\lambda)=\sum_{i=0}^{m}\binom mi^2\lambda^i
\in\mathbf F_p[\lambda].
\tag{6.4}
$$

It has degree $m$, so it cannot vanish at every element of the algebraic closure. Choose $\lambda$ outside its finite zero set and outside $\{0,1\}$. Then $E_\lambda$ is smooth and ordinary. Its coefficients lie in some finite field $k'/k$.

The Hasse-invariant criterion follows from Frobenius on invariant differentials. For a Weierstrass equation $y^2=f(x)$, the Cartier operator sends $dx/y$ to the coefficient of $x^{p-1}$ in $f(x)^m$, raised through the inverse Frobenius scalar. The curve is ordinary exactly when this operator is nonzero; if it vanishes, both Frobenius and Verschiebung on the local height-two group are nilpotent. Thus (6.4) proves rather than assumes ordinarity.

Lift $\lambda$ by its Teichmuller representative to $R'$, the unramified extension with residue field $k'$. Equation (6.3) has unit discriminant

$$
\Delta=16\lambda^2(1-\lambda)^2,
$$

so it defines an elliptic scheme $E/R'$ with ordinary special fiber.

### 6.3 Tensoring produces ordinary Hilbert--Blumenthal points

Let $I$ be an invertible ideal with $\mathfrak c=\mathfrak c_I$. Put

$$
A=E\otimes I.
\tag{6.5}
$$

Then $A/R'$ is a Hilbert--Blumenthal abelian scheme with the correct polarization module. For every $\mathfrak r\mid p$,

$$
A[\mathfrak r]
\simeq E[p]\otimes_{\mathbf F_p}I/\mathfrak r I.
\tag{6.6}
$$

The connected--etale sequence of $E[p]$ scalar-extends to (6.2), so all $\mathfrak r$-directions are ordinary.

Prime-to-$p$ auxiliary level and the $\mathfrak q$-frame become rational after a finite unramified extension because their isomorphism schemes are finite etale. A prescribed $\mathfrak p$-frame at the residue characteristic is more restrictive: it exists precisely when the generic representation $V_{\mathfrak p}$ is paired-isomorphic to the generic fiber of (6.6). Finite flatness or equality of semisimplifications alone does not supply that isomorphism.

The displayed formula has a typographical role as well as a mathematical one: $A[\mathfrak r]$ is a group scheme, not just the two-dimensional space of geometric generic points. Its multiplicative subgroup can have only one geometric special-fiber point.

For a numerical example, take $p=5$ and $\lambda=2$. Formula (6.4) gives

$$
H_5(2)=1+4\cdot2+2^2=13\equiv3\pmod5,
$$

so $E_2:y^2=x(x-1)(x-2)$ is ordinary over $\mathbf F_5$. Its discriminant is $16\cdot4\cdot1\equiv4$, a unit. For $I=\mathcal O_F$ and a totally real field unramified at $5$, the lift of $E_2\otimes\mathcal O_F$ is therefore an ordinary Hilbert--Blumenthal point of polarization type $\mathfrak d_F^{-1}$. The discriminant proves good reduction, while the Hasse invariant decides ordinary rather than supersingular reduction.

### 6.4 The ordinary deformation coordinate

The ordinary extension (6.2) explains why ordinary points move. Over a complete local base, extensions of the etale height-one direction by the multiplicative direction are measured by a unit parameter. In the elliptic case this can be seen without a general deformation theorem.

Choose a parameter $t=-x/y$ at the origin. The formal group of an ordinary elliptic curve has height one, and after an unramified extension it is isomorphic, noncanonically, to the formal multiplicative group. The etale quotient lifts uniquely through nilpotent thickenings. Gluing the two directions changes by a Kummer class in

$$
1+\mathfrak m_R.
\tag{6.7}
$$

Reduction sends every such parameter to $1$, so all these deformations have the same ordinary special fiber. This one-dimensional coordinate is the elliptic shadow of the $d$ Hodge-line coordinates on the Hilbert moduli scheme.

We do not infer that the generic representation splits. A nontrivial value of (6.7) gives a nonsplit extension even though its special fiber is ordinary. This is a useful source of ordinary finite-flat representations with nontrivial extension class.

### 6.5 Ordinary residue tubes

The ordinary locus in the special fiber of the good Hilbert moduli scheme is the nonvanishing locus of the product of the partial Hasse invariants. We recall their construction. After extending the finite residue field, decompose the Hodge bundle using the idempotents of the unramified coefficient algebra:

$$
\omega_A=\bigoplus_\tau\omega_\tau,
$$

with each $\omega_\tau$ a line. Verschiebung pulls differentials back and, because it is Frobenius-semilinear, induces maps

$$
V^*:\omega_\tau
\longrightarrow\omega_{\sigma^{-1}\tau}^{\otimes p},
\tag{6.8}
$$

where $\sigma$ is arithmetic Frobenius on the residue embeddings. Relative to local generators, (6.8) is multiplication by a scalar; invariantly that scalar is a section of

$$
\omega_\tau^{-1}\otimes
\omega_{\sigma^{-1}\tau}^{\otimes p}.
$$

This section is the partial Hasse invariant $h_\tau$. It is nonzero exactly when Verschiebung is nonzero in that embedding direction. All $h_\tau$ are nonzero exactly when every height-two direction has slopes $0$ and $1$, which is ordinarity. Their simultaneous nonvanishing is therefore Zariski open. The definition descends from the residue-field extension because Frobenius permutes the sections.

**Proposition 6.1 (ordinary openness).** Let $x\in\mathcal H(R)$ have ordinary special fiber. There is an open neighborhood $\Omega_x\subset H(K)$ consisting of good ordinary points. If $x$ lifts to the generic paired twist, $\Omega_x$ may be chosen so that every point has the same paired generic torsion representations.

**Proof.** Choose an open subscheme of the special fiber on which all relevant partial Hasse invariants are invertible. Its inverse image in $\mathcal H(R)$ is open by the coordinate criterion of Section 2.1, and every member is good and ordinary. On the generic fiber, Proposition 2.3 gives local sections of both finite etale frame isomorphism schemes around the chosen lift. Intersect the resulting finitely many open neighborhoods. $\square$

The proof keeps two forms of openness separate. Invertibility of the Hasse invariants is algebraic openness on the special fiber. Constancy of a prescribed generic representation comes from a finite etale cover on characteristic-zero points.

If only one $h_\tau$ vanishes, the point is already nonordinary even though other coefficient directions remain ordinary. The supersingular tensor seed is more special: every partial Hasse invariant vanishes. The residue-tube method of Chapter 7 works for either pattern, provided the exact special point is fixed.

## 7. Nonordinary finite-flat points

### 7.1 Why nonordinary requires a different argument

The vanishing of a Hasse invariant is closed, so the nonordinary locus is not generally Zariski open. An arithmetic approximation theorem nevertheless needs an open subset of $K$-points. The solution is to begin with one nonordinary integral point and fix its reduction. Every lift inside that residue tube remains nonordinary because its special fiber is the same.

There is also an integral issue. For a good abelian scheme, $A[\mathfrak p]$ is automatically finite flat. But if one starts only with a generic representation $V_{\mathfrak p}$, the words “nonordinary finite-flat” require an actual finite flat model and a local--local special fiber. A character calculation on inertia is not a substitute.

### 7.2 Supersingular seed points

The same Legendre family supplies a nonordinary seed. The polynomial $H_p$ in (6.4) has positive degree. Moreover

$$
H_p(0)=1,
\qquad
H_p(1)=\sum_i\binom mi^2=\binom{2m}{m}\equiv(-1)^m\pmod p,
\tag{7.1}
$$

where the middle equality is Vandermonde's identity and $2m=p-1$. Thus neither $0$ nor $1$ is a root. Over the algebraic closure $H_p$ has a root $\lambda_0$, and $E_{\lambda_0}$ is a smooth supersingular elliptic curve. The root lies in a finite extension $k'/k$.

Lift the coefficients of a general integral Weierstrass equation for this curve to $W(k')$. Smoothness of the special equation means its discriminant lifts to a unit, so the result is an elliptic scheme $E/R'$. We do not require the Teichmuller lift of $\lambda_0$ to be a canonical supersingular lift; any lift has the same supersingular special fiber.

For $p=3$, the Legendre argument still works, although short Weierstrass shortcuts must be handled carefully. At $p=2$, supersingular curves exist but the small-height uniqueness and odd-character arguments used later fail; dyadic assertions therefore require separate models and are not included in the finite-flat classification theorem below.

### 7.3 Local--local finite-flat torsion

Let $A=E\otimes I$ for the supersingular lift. Then $A/R'$ is good and, for each $\mathfrak r\mid p$, its special-fiber $\mathfrak r$-torsion is local--local. Indeed $E[p]$ has neither an etale nor a multiplicative height-one direct factor in the supersingular case; Frobenius and Verschiebung are nilpotent on its height-two Dieudonne plane. Scalar extension by $I/\mathfrak rI$ preserves this property.

The group $A[\mathfrak r]$ is finite flat of rank $|k_{\mathfrak r}|^2$. Its generic fiber is etale because $K$ has characteristic zero, but that generic fiber does not determine the number of special-fiber points or the local--local type. This is precisely the phenomenon for which integral finite-flat theory is needed.

For $p>2$ over an unramified base, the height-two integral classification gives an exact check. The filtered module has one Hodge line, an invertible normalized Frobenius matrix, and local--local reduction. Unramified ground-field extension tensors this filtered module with the larger Witt ring and preserves nilpotence of Frobenius and Verschiebung. Thus the nonordinary type survives every unramified extension.

For $p=5$, the Deuring polynomial is $H_5(\lambda)=1+4\lambda+\lambda^2$. Its discriminant is $12\equiv2\pmod5$, so its two roots lie in $\mathbf F_{25}$ and are neither $0$ nor $1$. Either root gives a supersingular Legendre curve over $\mathbf F_{25}$. Tensoring a lift with $\mathcal O_F$ therefore gives a concrete nonordinary point after an unramified quadratic extension of a $5$-adic base. This illustrates why allowing a controlled unramified extension is natural: the desired special-fiber geometry can exist geometrically without having a point over the original residue field.

### 7.4 Exact finite-flat representations and admissibility

There are three increasingly strong notions that must not be conflated.

1. A representation is **finite flat** if it is the generic fiber of some finite flat group scheme.
2. It is **height-two Barsotti--Tate admissible** if the model is the first layer of a compatible height-two system with Hodge type $(0,1)$.
3. It is **PEL-realizable on $Y$** if there is a polarized real-multiplication abelian scheme with auxiliary level and both frames whose $\mathfrak p$-torsion is that representation.

The implications run from 3 to 2 to 1. Neither converse is formal. A single finite-flat group need not come with compatible lifts through all $p^n$, and a compatible $p$-divisible system does not by itself select a global polarization component or auxiliary level.

In the unramified range $p>2$, the finite-flat classification gives a precise linear test for the first two notions. A torsion object is finite flat exactly when it comes from an admissible filtered module of weights $[0,1]$. It is the first layer of a stable height-two lattice when that module belongs to a compatible exact system. Ordinary and local--local types are then read from Frobenius and Verschiebung, and perfect alternating pairings encode the cyclotomic determinant.

For the explicit tensor seed, PEL realizability is already proved by construction. Over the original field, a prescribed $V_{\mathfrak p}$ requires either a supplied PEL realization or a paired isomorphism

$$
V_{\mathfrak p}\simeq
E[p]\otimes_{\mathbf F_p}I/\mathfrak pI
\tag{7.2}
$$

for one of the constructed ordinary or supersingular lifts. Under (7.2), the frame in (1.1) exists and the point lies on the exact twist. This is stronger than asking that $V_{\mathfrak p}$ and the right side have the same semisimplification.

There is nevertheless an important local escape that is legitimate in a specialization theorem allowing a prescribed finite completion extension. Given any two finite representations, one can pass to the compositum of their finite splitting fields. Both then become constant. If their paired determinant lines agree, symplectic bases give a paired isomorphism. Thus a finite-flat $V_{\mathfrak p}$ need not be realized by the chosen seed over $K$ itself: after a finite extension splitting both $V_{\mathfrak p}$ and the seed torsion, it is realized exactly. Finite flatness and ordinary or local--local reduction persist under that extension. Section 9.4 formulates this distinction between unramified realization over a small field and unconditional realization after a finite completion extension.

### 7.5 The nonordinary residue tube

Let $y\in Y(K)$ be a PEL-realized nonordinary finite-flat point that extends to $x\in\mathcal H(R)$. Let $\bar x$ be its special point. Define

$$
\Omega_y
=]\bar x[_{\mathcal H}
\cap U_{\mathfrak p}
\cap U_{\mathfrak q},
\tag{7.3}
$$

where $U_{\mathfrak p}$ and $U_{\mathfrak q}$ are the local images of the chosen generic frames supplied by Proposition 2.3.

**Theorem 7.1 (nonordinary finite-flat openness).** The set (7.3) is a nonempty open neighborhood of the image of $y$ in $H(K)$. Every point in it has good reduction with the same nonordinary special fiber, and both generic torsion representations remain paired-isomorphic to the prescribed ones. In particular the prescribed $\mathfrak p$-representation remains finite flat.

**Proof.** The residue tube is open by Proposition 2.1 and contains the image of $y$. Fixing the special moduli point fixes its $\mathfrak p$-torsion group scheme and hence its local--local type. The two frame images are open by Proposition 2.3 and contain the same point, so the finite intersection is nonempty and open. Every member has generic torsion isomorphic to the given finite-flat representation; the original finite flat model therefore witnesses finite flatness for that representation. $\square$

The last sentence concerns the abstract generic representation. It does not assert that the finite flat model attached to a nearby abelian scheme is canonically the original one. If the full special point is fixed, their reductions agree; uniqueness of an integral model requires the small-ramification hypotheses of finite-flat rigidity and should be invoked only when needed.

## 8. Semistable points from Tate curves

### 8.1 A degeneration with a controllable parameter

Let $K$ be a complete discretely valued field and choose $q_0\in K^\times$ with

$$
0<|q_0|<1.
$$

The Tate curve $E_{q_0}$ is an elliptic curve with split multiplicative reduction and uniformization

$$
E_{q_0}(\overline K)
\simeq\overline K^\times/q_0^{\mathbf Z}.
\tag{8.1}
$$

Its canonical parameter is unique, its minimal discriminant satisfies

$$
v_K(\Delta_{\min})=v_K(q_0),
\tag{8.2}
$$

and $v_K(j(E_{q_0}))=-v_K(q_0)<0$. The identity component of the special fiber is $\mathbf G_m$, so the reduction is semistable but not good.

The parameter $q_0$ separates three kinds of information. Its positive valuation forces multiplicative reduction. Its unit class controls Kummer extensions in torsion. Its exact valuation measures the number of geometric components after strict henselization.

### 8.2 Tensoring the Tate curve

Let $I$ be an invertible ideal and put

$$
A_{q_0}=E_{q_0}\otimes I.
\tag{8.3}
$$

Proposition 3.1 gives real multiplication and polarization type $\mathfrak c_I$. The product of the Tate semiabelian models, descended through a basis change of $I$, gives a semiabelian model of $A_{q_0}$. Its connected special fiber is a split torus of dimension $d$. Thus $A_{q_0}$ has totally toric split semistable reduction.

The Hilbert determinant condition holds on the generic fiber by (3.8). Prime-to-residue-characteristic auxiliary level becomes rational after a finite extension. If that extension is unramified, split multiplicative reduction stays split and the valuation (8.2) is unchanged. A ramified extension multiplies it by the ramification index.

This construction reaches exactly the tensor polarization types (3.10). For another component, a semistable seed must be exhibited in that component; one cannot move (8.3) there merely by forgetting the polarization.

### 8.3 Torsion and the Kummer class

For an integer $n$ not divisible by $\operatorname{char}K$, Tate uniformization gives

$$
0\longrightarrow\mu_n
\longrightarrow E_{q_0}[n]
\longrightarrow\mathbf Z/n\mathbf Z
\longrightarrow0.
\tag{8.4}
$$

Choose $q_n$ with $q_n^n=q_0$ and a primitive root $\zeta_n$. In the ordered basis represented by $\zeta_n$ and $q_n$, Galois acts by

$$
\rho_{E_{q_0},n}(\sigma)
=\begin{pmatrix}
\chi_n(\sigma)&c_{q_0,n}(\sigma)\\
0&1
\end{pmatrix},
\tag{8.5}
$$

where $\sigma(q_n)=\zeta_n^{c_{q_0,n}(\sigma)}q_n$. The determinant is cyclotomic and the extension class is the image of $q_0$ in $K^\times/(K^\times)^n$.

Tensoring (8.4) with $I/\mathfrak r I$ gives $A_{q_0}[\mathfrak r]$ at every $\mathfrak r\mid n$. Consequently a prescribed triangular local system occurs on this seed exactly when its extension class is the scalar extension of $[q_0]$ with the correct pairing normalization. Equality of its two diagonal characters is insufficient; the Kummer class is part of the representation.

If $n=\ell$ differs from the residue characteristic, the residual representation becomes unramified precisely when $\ell\mid v_K(q_0)$. Indeed the $\ell$th-power map is an automorphism on a sufficiently deep principal-unit group, while adjoining an $\ell$th root of a residue unit gives an unramified extension because its reduced polynomial is separable. The residue-unit class can remain nontrivial, but it contributes only unramified Frobenius. We nevertheless retain the full Kummer class whenever the exact representation, rather than only its inertia, is prescribed.

### 8.4 Finite flatness at the coefficient prime

Now suppose $K/\mathbf Q_p$ is unramified and $p$ is odd. Although $E_{q_0}$ has bad reduction, its generic $p$-torsion may be finite flat. The exact criterion for the canonical Tate filtration is

$$
p\mid v_K(q_0).
\tag{8.6}
$$

We recall the proof because it is the cleanest example separating finite-flat torsion from good reduction. Write $q_0=\pi^m u$. Its Kummer class comes from

$$
R^\times/(R^\times)^p
\longrightarrow K^\times/(K^\times)^p
$$

if and only if $p\mid m$: multiplying by a $p$th power changes $m$ by a multiple of $p$, and if $m=ps$ then $q_0(\pi^{-s})^p=u$ is a unit. A unit Kummer class defines an extension over $R$

$$
0\longrightarrow\mu_p
\longrightarrow\mathcal G
\longrightarrow(\mathbf Z/p\mathbf Z)_R
\longrightarrow0,
\tag{8.7}
$$

whose generic fiber is (8.4). Conversely, pulling a hypothetical extension back along $1\in\mathbf Z/p\mathbf Z$ gives a $\mu_p$-torsor over $R$, so its Kummer class must have a unit representative. This proves (8.6).

Here is the extension explicitly. When $q_0=\pi^{ps}u$, take the disjoint union

$$
\mathcal G=\coprod_{i=0}^{p-1}
\operatorname{Spec}R[T_i]/(T_i^p-u^i).
\tag{8.8}
$$

Each component is finite free of rank $p$. Multiply a point on component $i$ by a point on component $j$ by multiplying their $T$-coordinates; if $i+j\geq p$, divide the product by the unit $u$ and put it on component $i+j-p$. Associativity follows from ordinary multiplication together with the rule $T_{i+p}=uT_i$. Component $0$ is $\mu_p$, and the component index gives the quotient $\mathbf Z/p\mathbf Z$. On the generic fiber send $T_i=z$ to the Tate parameter $(\pi^s)^iz$. Its $p$th power is $q_0^i$, so it represents the points in the fiber of (8.4) above $i$. This identifies the generic fiber of (8.8) with $E_{q_0}[p]$ and proves the sufficiency in scheme-theoretic form.

Over an unramified odd-prime base, the two inertia characters $\overline\chi_p$ and $1$ are distinct. Hence the multiplicative line is intrinsic, its schematic closure is $\mu_p$, and any finite flat model respects the canonical filtration. Under these hypotheses (8.6) is therefore a criterion for the abstract residual representation, not only for a chosen extension presentation.

After tensoring by $I/\mathfrak pI$, the same criterion makes $A_{q_0}[\mathfrak p]$ finite flat. The abelian variety remains multiplicative. At $p=2$, the cyclotomic character modulo $2$ is trivial and the intrinsic-line argument fails; even valuation still constructs the canonical model, but abstract necessity needs separate dyadic classification.

For example, over an unramified $p$-adic field take

$$
q_0=\pi^p u,
\qquad u\in R^\times.
\tag{8.9}
$$

Then $E_{q_0}$ has split multiplicative reduction with minimal discriminant exponent $p$, while $E_{q_0}[p]$ is finite flat. The generic representation is normally ramified because its multiplicative line carries $\overline\chi_p$; finite flat is therefore not synonymous with unramified. If instead $q_1=\pi u$, the two curves have the same coarse reduction type and the same diagonal characters, but $E_{q_1}[p]$ is not finite flat over an unramified odd-prime base. The exponent distinguishes the integral torsion models.

### 8.5 Semistable neighborhoods

Semistability is open in the local topology around a fixed semiabelian model. We isolate the exact form used here.

For the tensor Tate point, the needed chart can be described directly from periods. Choose dual $\mathbf Z$-bases of $I$ and $I^\dagger$. The totally degenerate semiabelian object is encoded by a one-motive

$$
[,I\longrightarrow\mathbf G_m\otimes I^\dagger,],
\tag{8.10}
$$

whose period pairing sends $(a,b)$ to a power of $q_0$ determined by $\operatorname{Tr}_{F/\mathbf Q}(ab)$. The polarization says that this pairing is symmetric after the identification (3.6), and positivity says its valuation form is positive definite. Real multiplication imposes linear equalities

$$
q(ax,b)=q(x,ab)
\tag{8.11}
$$

on the period coordinates. Consequently the independent logarithmic period directions form the rank-$d$ lattice of symmetric $\mathcal O_F$-linear homomorphisms, the same lattice that gives the $d$ tangent directions of the Hilbert moduli space.

Choose a rational polyhedral cone containing the positive valuation form of the diagonal tensor period. The corresponding completed monoid algebra has one boundary monomial for each primitive ray. Over it, the quotient construction for (8.10) is obtained by the same convergent products as the one-dimensional Tate curve, applied to the character monomials. Positive valuation makes every product converge; (8.11) makes the $\mathcal O_F$-action descend; symmetry gives the polarization; and a change of dual bases acts by integral monomials, so the construction glues. Inverting the boundary monomials gives an abelian scheme and a map to $H$. The tangent characters are the full rank-$d$ PEL lattice, so this map is etale at the tensor Tate point. The completed monoid chart therefore supplies the scheme $\mathcal U$ in the next theorem. This argument is the higher-dimensional version of building $E_q$ from $K^\times/q^{\mathbf Z}$; the cone records which multi-periods tend to zero.

**Theorem 8.1 (semistable local persistence).** Let $A/K$ be a polarized abelian variety with real multiplication and split semiabelian reduction. Suppose there is a finite-type $R$-scheme $\mathcal U$, a semiabelian scheme over $\mathcal U$, and an open immersion $\mathcal U_K\hookrightarrow H_K$ whose universal generic abelian scheme is the given semiabelian scheme's generic fiber near the point $A$. Assume that on $\mathcal U$ the torus has a fixed split character lattice and that the boundary is cut out by normal-crossing parameters. Then there is an open neighborhood $\Omega_A\subset H(K)$ such that every point in $\Omega_A$ has semistable reduction with the same toric rank. If the generic paired frames exist at $A$, the neighborhood may be chosen to preserve them.

**Proof strategy.** A split semiabelian scheme is an extension of an abelian scheme by a split torus. Both pieces and the extension law are given by finitely many regular functions. Smoothness of the torus and abelian part makes their defining unit and discriminant conditions stable under small changes. The boundary parameters must remain nonzero with positive valuation; valuation is locally constant on $K^\times$. These conditions give the desired open chart.

**Proof.** Choose the stipulated basis of the character lattice. On $\mathcal U$, the semiabelian group law is described by the abelian part, copies of $\mathbf G_m$, and finitely many biextension transition functions, all units. Smoothness of the abelian part is the invertibility of a finite Jacobian determinant; preservation of the fixed character lattice is built into the chart. The normal-crossing parameters $t_1,\ldots,t_a$ cut out its boundary divisors. The given generic point has $0<v_K(t_i)<\infty$ for the degenerating directions and unit parameters for the others. Each equality $v_K(t_i)=m_i$ is open because a sufficiently small perturbation of a nonzero element has the same valuation. Keeping all Jacobian determinants and transition functions units gives a finite intersection of open conditions. By the universal property assumed for $\mathcal U$, every resulting generic point is the generic fiber of the displayed semiabelian scheme and has the same toric rank. Finally intersect with the local images of the finite etale generic frame covers, as in Proposition 2.3. $\square$

For the tensor Tate point, one may take all boundary parameters equal to $q_0$ after a choice of tensor basis. Thus $v(q_0)>0$ is the visible semistable condition. If finite flatness at $p$ is also required, choose $v(q_0)$ divisible by $p$ and restrict to the valuation shell $v(q)=v(q_0)$. Every point of that smaller neighborhood retains (8.6).

## 9. Twisted two-prime covers and local solvability

### 9.1 What a point of the twist says

A $K$-point of the two-prime twist is a tuple

$$
(A,\iota,\lambda,\eta_{\mathfrak n},
\alpha_{\mathfrak p},\alpha_{\mathfrak q})
\tag{9.1}
$$

with the isomorphisms (1.1). It realizes the prescribed representations exactly, including extension classes and pairings. There is no weakening to semisimplification.

The local geometry and the twisting operation solve different problems. The Hilbert scheme supplies abelian varieties and reduction types. The twist asks whether their two torsion modules equal the prescribed local systems. A beautiful ordinary or semistable abelian variety that lacks either frame is not a local point of $Y$.

### 9.2 The determinant obstruction

The polarization gives canonical determinant isomorphisms

$$
\det A[\mathfrak r]\simeq\mathscr D_{\mathfrak r}.
$$

Therefore a necessary condition for (9.1) is a specified equivariant isomorphism

$$
\det V_{\mathfrak r}\xrightarrow{\sim}\mathscr D_{\mathfrak r}
\tag{9.2}
$$

for $\mathfrak r=\mathfrak p,\mathfrak q$. In rank two, (9.2) gives the unique alternating pairing inducing that determinant map. It is also sufficient to define the twist, but not sufficient for the twist to have a $K$-point.

At a real place, local solvability reduces to oddness by Proposition 4.1. At a good finite place away from $p$ and $q$, it is a simultaneous Frobenius realization problem. At a coefficient prime, it is an exact finite-flat PEL realization problem. At a semistable place, it includes the Kummer extension class.

### 9.3 Good-prime solvability

Let $r\ne p,q$ be good for all integral data. The finite etale twist extends as in (5.1).

**Theorem 9.1 (good-prime local point).** If the special fiber of the chosen integral twist has a point over some finite extension $k'/k$, then the twist has a good point over the corresponding unramified extension $K'/K$. This point possesses an open residue neighborhood on which good reduction and both exact frames persist.

Alternatively, suppose a good PEL seed of the selected polarization type is available over a finite extension of $K$, without frames. Then any two determinant-compatible finite local systems are realized on that seed after a further finite extension. The resulting point again has a good open neighborhood.

**Proof.** The first assertion is Theorem 5.1 after unramified base change. For the alternative, take a finite compositum splitting the two prescribed local systems, the two seed torsion modules, the auxiliary level, and the determinant coefficient lines. Over that field choose symplectic bases and match them at each prime. Base change preserves the good abelian scheme. Its integral residue tube, intersected with the generic local frame images, is the desired neighborhood. $\square$

The hypothesis is directly verifiable. One may construct a special-fiber tensor point and compare its two Frobenius representations, or find a closed point on the entire twist. Geometric connectedness of the generic cover helps ensure that no constant-field obstruction is hidden, but local special-fiber nonemptiness is still checked rather than inferred.

### 9.4 Coefficient-prime solvability

Suppose the residue characteristic is $p$. The $\mathfrak q$-frame and auxiliary level are prime to $p$ and behave etale-locally. The $\mathfrak p$-frame is a generic isomorphism involving a finite flat group on the integral side.

**Theorem 9.2 (coefficient-prime local point).** Assume $p>2$, $K/\mathbf Q_p$ and $F_{\mathfrak p}/\mathbf Q_p$ are unramified, and the polarization is prime to $p$. Fix an ordinary or supersingular tensor seed of the selected polarization type, or another PEL point of the desired type.

1. If both exact generic frames already exist on the seed, then after a finite unramified extension sufficient for its prime-to-$p$ level there is a point of $Y$. It has an open neighborhood consisting respectively of ordinary finite-flat or nonordinary finite-flat points with both prescribed generic torsion representations.
2. More generally, let $V_{\mathfrak p}$ be any determinant-compatible finite-flat representation and let $V_{\mathfrak q}$ be any determinant-compatible finite representation. Then there is a finite extension $L/K$ over which the seed defines a point of $Y(L)$. Its reduction type is the chosen ordinary or nonordinary type, and $V_{\mathfrak p}|_{G_L}$ remains finite flat. The extension $L/K$ is not asserted to be unramified.

**Proof.** For assertion 1, the supplied $\mathfrak p$-isomorphism gives the residue-characteristic frame on the generic fiber. The auxiliary level and any remaining prime-to-$p$ isomorphism scheme are finite etale and become rational after a finite unramified extension because the seed has good reduction. Proposition 6.1 gives the ordinary neighborhood and Theorem 7.1 the nonordinary one.

For assertion 2, first make the finite residue extension needed to define the seed. Let $L$ contain the finite splitting fields of

$$
V_{\mathfrak p},\quad V_{\mathfrak q},\quad
A[\mathfrak p],\quad A[\mathfrak q],
\tag{9.3}
$$

as well as the finite field needed for the auxiliary level and the roots of unity occurring in the determinant targets. Over $L$, all four torsion local systems in (9.3) and their coefficient lines are constant. A perfect alternating form on a two-dimensional vector space over a field has a symplectic basis: choose a nonzero first vector, choose a second with nonzero pairing, and rescale it to the prescribed value. Applying this separately at $\mathfrak p$ and $\mathfrak q$ gives the two paired frames on the same seed. Good reduction and ordinary or local--local type persist by base change. Since $V_{\mathfrak p}$ was the generic fiber of a finite flat group over $R$, its restriction is represented by that group's base change to the valuation ring of $L$. Proposition 6.1 or Theorem 7.1, together with the local frame sections of Proposition 2.3, gives the required open neighborhood. $\square$

Finite flatness of $V_{\mathfrak p}$ alone is intentionally not asserted to imply the hypotheses. The gap from an abstract finite flat group to a polarized abelian variety on a selected component is a genuine PEL realization problem.

### 9.5 Simultaneous frames

The two frame conditions must be solved on the same abelian variety. Separate local existence for $V_{\mathfrak p}$ and $V_{\mathfrak q}$ does not suffice. The product twist encodes this simultaneity.

Once one simultaneous point exists, however, openness is straightforward. Each generic frame cover is finite etale over $K$, so each has an open local image. Their intersection contains the point and is therefore nonempty. Reduction, ordinary, nonordinary, or semistable conditions can then be intersected with it, provided the same seed point witnesses all of them.

This order prevents a common circular argument. We do not prove the intersection nonempty by observing that all its factors are individually nonempty. We first construct one tuple (9.1), then shrink around it.

The finite-splitting argument also applies to a semistable seed. Starting from $A_{q_0}$ on the correct polarization component, pass to a finite field splitting both prescribed local systems, both seed torsion modules, and the auxiliary level. Symplectic bases give simultaneous frames. Semistability and split toric reduction persist; if $V_{\mathfrak p}$ was finite flat, its restriction remains finite flat. If the seed's own Tate $p$-torsion is required to be finite flat, choose $p\mid v(q_0)$ before extending. The exact valuation after extension is then $e(L/K)v(q_0)$, so only divisibility and semistability, not the original normalized exponent, are claimed to persist.

## 10. Openness of the exact local conditions

### 10.1 Three different meanings of openness

Three topologies occur in the local argument.

1. A locus in an algebraic special fiber can be Zariski open, as the ordinary locus is.
2. A subset of $H(K)$ can be open for the local-field topology, as every residue tube is.
3. A condition in a family can be stable under generization or base change, which is a statement about morphisms rather than either of the preceding topologies.

The distinctions are not verbal. The nonordinary locus fails the first kind of openness but yields the second kind after one special point is fixed. Semistability persists under field extension, the third kind of statement, but a fixed component-group order need not. A framed torsion isomorphism is locally constant on characteristic-zero points because it is represented by a finite etale scheme, even when no etale integral frame scheme exists.

We now gather the local-field openness assertions in one place and prove them with the exact hypotheses used later.

### 10.2 Good and ordinary loci

Let $\mathcal H/R$ be the smooth integral Hilbert moduli scheme at a good coefficient prime. Its integral points form an open subset in the generic local points on every affine chart meeting the chosen point. Thus good reduction has an open neighborhood around every good point.

For ordinarity, let $h_\tau$ be the partial Hasse invariant for each residue embedding direction. Each $h_\tau$ is a section of a line bundle on the special fiber. The locus where it is nonzero is open, and the simultaneous ordinary locus is

$$
\mathcal H_k^{\mathrm{ord}}
=\bigcap_\tau D(h_\tau).
\tag{10.1}
$$

Because there are finitely many $\tau$, (10.1) is open. Its inverse image under reduction is therefore open in $H(K)$. The tensor ordinary points of Chapter 6 show that it is nonempty on every tensor-admissible component that they meet.

**Proposition 10.1.** Around a good ordinary point there is a basic open set determined by finitely many conditions

$$
f_i(x)\in R,
\qquad
g_j(x)\in R^\times,
\qquad
h_\tau(\bar x)\ne0,
\tag{10.2}
$$

and every point of that set has good ordinary reduction.

**Proof.** Choose an affine integral chart. The $f_i$ express integrality of its coordinates and the $g_j$ invert the functions cutting out the chart, the polarization-perfect locus, and the smooth locus. Units form an open subset of $K$. The last conditions are equivalent to chosen lifts of $h_\tau$ being units, again an open condition. All are finite in number. $\square$

This description is useful when neighborhoods must later be made smaller: adding congruences does not destroy openness as long as the chosen point remains.

### 10.3 Nonordinary finite-flat tubes

Let $x\in\mathcal H(R)$ have local--local $\mathfrak p$-torsion. The set

$$
\operatorname{red}^{-1}(\operatorname{red}(x))
\tag{10.3}
$$

is open, and every point in it has exactly the same special-fiber group scheme. This proves nonordinary persistence without asserting that the vanishing locus of the Hasse invariant is open.

Sometimes fixing the whole moduli point is more than necessary. It is enough to fix the finite truncation on which Frobenius and Verschiebung matrices are defined. If local--local type is expressed by nilpotence of these matrices on the level-one special fiber, then their residue entries are fixed by congruence modulo $\pi$. The corresponding congruence class is an open union of full residue tubes.

Finite flatness of the generic representation enters separately. Let $P\to H_K$ be the finite etale isomorphism scheme

$$
P=\operatorname{Isom}^{\mathrm{pair}}
(V_{\mathfrak p},A[\mathfrak p]).
$$

If $P(K)$ contains a point above $x$, Proposition 2.3 supplies an open $U$ around $x$ contained in the image of $P(K)$. For every $u\in U$, the representation $A_u[\mathfrak p]$ is isomorphic to the same $V_{\mathfrak p}$. If $V_{\mathfrak p}$ has a finite flat model, that model proves the finite-flat property for all these generic representations.

The intersection of $U$ with (10.3) is the exact nonordinary finite-flat neighborhood. One factor controls the integral special-fiber type; the other controls the generic isomorphism class.

### 10.4 Semistable and Kummer conditions

For a Tate curve, $v(j)<0$ is stable under small perturbation of $j$ because valuation is locally constant on $K^\times$. On the tensor Tate locus the same condition is read in each elliptic factor. In a general semiabelian chart, Theorem 8.1 uses boundary parameters $t_i$. Conditions

$$
v_K(t_i)=m_i>0
\tag{10.4}
$$

are open shells. Keeping the remaining parameters and determinant functions units preserves the toric rank and polarization type.

At the coefficient prime, canonical finite flatness of Tate $p$-torsion is the divisibility condition $p\mid m_i$. Divisibility by itself is a union of valuation shells and is open among nonzero parameters: each point has one fixed valuation. If the exact Kummer class must be preserved, valuation is not enough. The class lies in the finite group

$$
K^\times/(K^\times)^p.
$$

For a $p$-adic local field this quotient is finite, and the $p$th-power subgroup is open. To see openness directly, write

$$
K^\times=\pi^{\mathbf Z}\times\mu_{|k|-1}\times U^1.
$$

On a sufficiently deep principal-unit group $U^n$, the $p$-adic logarithm identifies the $p$th-power map with multiplication by $p$, whose image contains another open subgroup. Hence every Kummer class is open. A sufficiently small neighborhood of $q_0$ therefore preserves both $v(q_0)$ and $[q_0]$.

For a prime $\ell\ne p$, the same conclusion is easier: raising to the $\ell$th power is an automorphism on a sufficiently deep principal-unit group. Thus $K^\times/(K^\times)^\ell$ is finite and discrete, and the Tate extension class is locally constant.

### 10.5 Frame conditions are locally constant

Let $T$ be a connected local analytic neighborhood in $H(K)$ and let $\mathcal A[\mathfrak r]$ be the generic finite etale torsion family. Choosing a point $t_0$ identifies its fiber with a finite set carrying a $k_{\mathfrak r}$-module structure and pairing. The monodromy of this finite local system factors through a finite quotient. After replacing $T$ by the open neighborhood corresponding to the kernel of that quotient, the local system is constant. In particular all fibers are paired-isomorphic.

This topological argument is equivalent to using the isomorphism scheme and Proposition 2.3. The scheme-theoretic version is preferable because it retains descent and works simultaneously for two primes.

**Theorem 10.2 (openness theorem).** Let $y\in Y(K)$ be a local point of one of the following kinds:

- real on a fixed real component;
- good away from the level primes;
- good ordinary at an unramified odd coefficient prime;
- good nonordinary finite-flat at such a prime;
- split semistable, with any stated Tate Kummer class.

Assume the relevant integral or semiabelian model exists at $y$. Then there is a nonempty open neighborhood $\Omega_y\subset Y(K)$ on which the same listed local condition, both exact paired frames, the polarization type, the auxiliary level, and the geometric component all persist.

**Proof.** At a real place use Section 4.4. At a good point use an integral residue tube and, for ordinarity, intersect with (10.1). For nonordinary type fix the special point as in (10.3). At a semistable point use the boundary-parameter chart and, when needed, fix the Kummer classes by Section 10.4. The frames and auxiliary level are universal on $Y$; if one works downstairs on $H$, intersect with their finite etale local images. A sufficiently small neighborhood cannot cross an open-and-closed component. Every intersection contains $y$, so it is nonempty. $\square$

## 11. Persistence under extension of local fields

### 11.1 Integral and good reduction

Let $L/K$ be a finite extension, with valuation rings $S/R$. If $A/R$ is an abelian scheme, then

$$
A_S=A\times_RS
$$

is an abelian scheme. The real multiplication, polarization-module isomorphism, determinant condition, and prime-to-residue-characteristic level all commute with base change. Hence good reduction persists under every finite extension.

Good reduction also descends through a finite unramified extension when the generic object and all its structures descend to $K$. Indeed $S/R$ is finite etale and faithfully flat. The smooth proper group scheme over $S$, together with its canonical descent datum from the generic fiber, descends effectively; smoothness and properness descend faithfully flat. Ramified descent is more delicate because a good model upstairs need not carry effective descent data and potential good reduction is common.

For a frame already defined over $K$, restriction gives a frame over $L$. A frame that appears only over $L$ need not descend: its obstruction is the corresponding torsor class.

### 11.2 Ordinary and local--local type

Suppose $A/R$ has good reduction. After base change to $S$, the new special fiber is obtained from the old one by extending the residue field, even when $L/K$ is ramified; nilpotent thickening in the base does not change the reduced geometric fiber. The connected--etale sequence commutes with perfect residue-field extension. Multiplicative, etale, and local--local factors therefore retain their geometric types.

**Proposition 11.1.** Ordinary and nonordinary local--local reduction of a good Hilbert--Blumenthal abelian variety persist under every finite extension of local fields.

**Proof.** On the special-fiber $p$-divisible group, ordinarity is the statement that the Newton slopes are $0$ and $1$ with the prescribed multiplicities, equivalently that the Hasse invariants are nonzero. Extending the residue field cannot turn a nonzero scalar into zero. Local--local type is equivalently the absence of etale and multiplicative geometric factors, or nilpotence of Frobenius and Verschiebung at level one; both properties are unchanged by scalar extension. $\square$

Descent is asymmetric. Ordinary reduction descends through residue-field extension because nonvanishing descends. A local--local factor also descends geometrically. But a splitting of the ordinary extension may exist only after extension and need not descend.

### 11.3 Semistability and splitness

Semistable reduction persists under every finite extension. The abelian part remains an abelian scheme and a torus remains a torus after base change. In the elliptic case this is visible from minimal invariants: good stays good, while multiplicative reduction has $c_4$ a unit, which remains a unit after extension.

For the Tate parameter,

$$
v_L(q_0)=e(L/K)v_K(q_0).
\tag{11.1}
$$

Thus the polygon of components becomes $e$ times thicker. Split multiplicative reduction remains split. Nonsplit multiplicative reduction can become split, often over an unramified quadratic extension, because the two tangent directions become rational. The reverse change never occurs.

Toric rank is geometrically invariant under extension. Rational component groups can change because residue Galois acts differently after extension. Consequently “semistable of toric rank $t$” is persistent, while “has exactly $m$ rational components” is not.

### 11.4 Finite-flat representations

If a finite $G_K$-module $V$ is the generic fiber of a finite flat group $\mathcal G/R$, then its restriction to $G_L$ is the generic fiber of

$$
\mathcal G_S=\mathcal G\times_RS.
$$

Finite flatness is preserved by arbitrary base change, so the restricted representation remains finite flat. Pairings, coefficient actions, and exact sequences base-change with it.

At an unramified ground-field extension in the Fontaine--Laffaille range, the filtered module base-changes by tensoring with the larger Witt ring. Ordinary or local--local type, duality, determinant, and stable lines are preserved. This is stronger than the abstract base-change observation because it identifies the classified integral object.

For Tate $p$-torsion, if $p\mid v_K(q_0)$ then

$$
p\mid v_L(q_0)=e(L/K)v_K(q_0),
$$

so canonical finite flatness persists. The converse after restriction fails: a ramification index divisible by $p$ can make $p\mid v_L(q_0)$ even when $p\nmid v_K(q_0)$. Finite flatness acquired after ramified extension need not descend.

### 11.5 What is not persistent

The following data require separate bookkeeping.

- Exact normalized valuations multiply by the ramification index.
- Nonsplit multiplicative reduction can become split.
- A finite etale level or frame can become rational only after extension.
- A Kummer class can vanish after extension, so a nonsplit torsion extension can split.
- An arithmetic connected component can divide into or merge Galois orbits after changing constants, even though geometric components do not change.
- Good reduction acquired after ramification need not descend.

These are not exceptions to the persistence theorems; they are data those theorems deliberately do not claim to preserve.

## 12. Combining conditions without losing a component

### 12.1 Intersections must be witnessed

Let $\Omega_1,\ldots,\Omega_m$ be nonempty open subsets of $Y(K)$. Their intersection can be empty. In local moduli applications the danger is concrete: one neighborhood may lie on an ordinary residue disk, another on a supersingular disk, and a third on a different determinant component.

The safe construction begins with one point $y$ satisfying all desired conditions. Each condition then supplies an open neighborhood of $y$, and the finite intersection remains nonempty because it contains $y$. This elementary order of reasoning prevents separate local existence statements from being combined illegitimately.

For two frames, the seed must already lie on the fiber product twist. For finite flatness and semistability at the same coefficient prime, the Tate seed must satisfy the divisibility criterion (8.6) before shrinking. For a nonordinary good point, one uses a supersingular seed, not an ordinary point plus a separate closed condition.

### 12.2 Component bookkeeping

The geometric components of the Hilbert moduli space are indexed by determinant classes in a narrow adelic quotient. A twist does not alter them after algebraic closure, but Galois may permute them. A local point belongs to one definite arithmetic orbit of geometric components.

Let $Y^\circ$ be the component used in the global approximation theorem. Every local neighborhood must meet $Y^\circ(K_v)$, not merely $Y(K_v)$. If $Y^\circ$ is open and closed over $K$, then a sufficiently small neighborhood of a point in it stays in it. If it is defined only after an extension, it cannot be used as a $K$-variety without descending its Galois orbit.

Tensoring by an ideal or changing polarization type can move the determinant class. Thus the calculation $\mathfrak c_I=\mathfrak d_F^{-1}I^{-2}$ is part of local component verification. A prime-to-level isogeny does not automatically preserve the ordered polarization-module identification.

### 12.3 Avoiding degeneracy loci

Applications often remove a proper closed subset $Z\subset Y$: loci with extra endomorphisms, reducible auxiliary torsion, vanishing coordinates, or unwanted automorphisms. If the chosen seed lies outside $Z$, then

$$
Y(K)\setminus Z(K)
$$

is open near it because $Z(K)$ is closed for a separated finite-type scheme over a local field. Intersecting with this complement preserves nonemptiness.

If the seed lies in $Z$, no amount of shrinking removes it while retaining the seed. One must choose a different point. Smooth positive-dimensional residue tubes help: in etale coordinates, a proper closed subset has empty interior unless it contains an entire local irreducible component. When necessary, pass to a finite residue extension so that a point of the tube avoids the reduction of $Z$.

The last assertion has a direct algebraic proof. A nonzero polynomial on an affine ball cannot vanish at every point over all finite extensions of a finite residue field. Reduce its first nonzero coefficient modulo a suitable power of $\pi$ and choose residue coordinates outside its zero set after a finite extension. Hensel lifting gives the desired point.

### 12.4 A simultaneous local-neighborhood theorem

**Theorem 12.1 (simultaneous local neighborhood).** Let $K$ be $\mathbf R$ or a finite extension of $\mathbf Q_r$, let $Y^\circ$ be a $K$-defined open-and-closed smooth component of the two-prime twist, and let $Z\subsetneq Y^\circ$ be closed. Suppose there is a point

$$
y\in(Y^\circ\setminus Z)(K)
$$

equipped, at a finite place, with the integral or semiabelian model required for one of the five local conditions. Then there is a nonempty open

$$
\Omega_y\subset(Y^\circ\setminus Z)(K)
\tag{12.1}
$$

such that:

1. every point has the same two prescribed paired torsion representations;
2. every point retains the auxiliary level, ordered polarization type, and component;
3. every point has the same selected real, good, ordinary, nonordinary finite-flat, or semistable condition;
4. any finitely many locally constant valuation, Kummer, splitness, or reduction constraints satisfied by $y$ also persist after shrinking.

**Proof.** Theorem 10.2 gives an open neighborhood for the principal local condition and frames. The component is already the ambient space. The complement of $Z(K)$ is open and contains $y$. Each additional locally constant invariant supplies an open neighborhood by Sections 10.4--10.5. Intersect the finitely many neighborhoods. Their intersection is open and contains $y$, proving nonemptiness. $\square$

The theorem is intentionally point-centered. It does not assert that arbitrary separately specified local conditions have a common point.

## 13. The Moret--Bailly local package

### 13.1 The input ledger

Before local neighborhoods can be passed to arithmetic approximation, the following facts must be recorded at every controlled place.

| place | seed point | condition retained | essential compatibility |
|---|---|---|---|
| real | real PEL point | real component and signs | odd paired involutions |
| $r\ne p,q$ | integral point on the twist | good reduction | special-fiber twist nonempty |
| $r=p$ ordinary | ordinary good point | ordinary finite-flat type | finite-flat $V_{\mathfrak p}$; exact frame after the allowed splitting field |
| $r=p$ nonordinary | local--local good point | fixed nonordinary finite-flat reduction | a PEL seed plus finite-flat $V_{\mathfrak p}$ |
| semistable | tensor Tate or supplied semiabelian point | toric rank, splitness, Kummer class | correct component; frames over the allowed splitting field |

For every row, the point must lie on the same $K$-defined component $Y^\circ$ used globally. At every real place a row is required if the output field is to be totally real. At finite places the local field can sometimes be enlarged unramified in advance; when that is done, the desired completion algebra in the global theorem must record the enlargement.

### 13.2 The local construction theorem

We can now state the complete result of the book.

**Theorem 13.1 (local geometry package for Hilbert--Blumenthal specialization).** Fix the two-prime Hilbert--Blumenthal datum of Section 1.2 and a $K_0$-defined smooth geometrically connected component $Y^\circ$ of its determinant-compatible twist. Let $S$ be a finite set of places of a totally real number field $K_0$. Assume all coefficient, polarization, and auxiliary-level primes are unramified wherever the corresponding integral assertion is made, and assume coefficient residue characteristics are odd.

For each $v\in S$, suppose one of the following verified local inputs is given.

1. If $v$ is real, $Y^\circ(K_{0,v})$ contains a real-admissible point; equivalently in the explicit tensor case, both prescribed odd torsion involutions admit paired frames.
2. If $v\nmid pq$, either the good integral model of $Y^\circ$ has a smooth special-fiber point on the twist after a specified finite residue extension, or a good PEL seed on the selected component is given and a finite splitting extension for the frames is allowed.
3. If $v\mid p$ or $v\mid q$ and ordinary reduction is required, there is an ordinary tensor seed or another PEL-realized ordinary point on the selected component; the prescribed residue-characteristic representation is finite flat, and a finite splitting extension for the two frames is allowed when they do not already exist.
4. If nonordinary finite-flat reduction is required, there is a supersingular tensor seed or another PEL-realized local--local point on the selected component; again the prescribed residue-characteristic representation is finite flat and the necessary finite splitting extension is allowed.
5. If semistable reduction is required, there is a tensor Tate point or another supplied semiabelian point on $Y^\circ$ with the required toric rank and Kummer class, and a finite splitting extension for the frames is allowed; at an odd coefficient prime, finite flatness of the canonical Tate torsion is imposed by divisibility of the Tate valuation.

Then, after making only the finite local extensions explicitly included in these inputs, there is for every $v\in S$ a nonempty open subset

$$
\Omega_v\subset Y^\circ(K_{0,v}')
\tag{13.1}
$$

such that every point in $\Omega_v$ has the required exact local condition, both prescribed paired torsion representations, the fixed ordered polarization and auxiliary level, and the selected component. These properties persist after any further finite extension in the following sense:

- good reduction, ordinarity, local--local type, semistability, toric rank, and finite flatness persist;
- split multiplicative reduction persists, while nonsplit reduction is allowed to become split;
- exact frames restrict to the larger local Galois group;
- normalized valuations rescale by the ramification index, and no stronger invariance is asserted.

If a proper closed degeneracy locus is to be avoided, the neighborhoods may be chosen in its complement provided every seed point lies outside it.

**Proof strategy.** The construction of seed points and the proof of openness are logically separate. Chapters 4--8 provide the five seeds. Chapters 9--10 put them on the exact twist and turn each into an open neighborhood. Chapter 11 proves the persistence statements. Chapter 12 keeps all intersections on the chosen component and outside the degeneracy locus.

**Proof.** At real places apply Proposition 4.1 and Section 4.4. At a good prime away from $p$ and $q$, use the first or second construction of Theorem 9.1 and then take its good residue tube. At an ordinary or nonordinary coefficient prime use Theorem 9.2; in the latter case its residue tube supplies openness even though the nonordinary special locus is closed. At a semistable place use the simultaneous splitting construction of Section 9.5 and Theorem 8.1, shrinking further to preserve the Kummer class as in Section 10.4. In every case, exact paired frames are retained by finite etale local sections on the generic fiber. The simultaneous component and avoidance assertions are Theorem 12.1. Finally Chapter 11 proves every stated base-change property and also explains the listed qualifications. $\square$

The theorem's seed hypotheses are part of its mathematical content. A determinant-compatible representation need not equal the torsion of a fixed seed over the original local field. The finite-splitting construction proves that it does become exactly that torsion after an explicitly allowed finite completion extension. What must still be constructed geometrically is a real, good, ordinary, nonordinary, or semistable PEL seed on the selected polarization component; the tensor constructions provide such seeds on every tensor-admissible component.

### 13.3 Passing from neighborhoods to every conjugate

An arithmetic approximation theorem uses (13.1) in one of two ways. If a place is required to split completely, the local algebra is a product of copies of $K_{0,v}$ and every conjugate point is required to lie in $\Omega_v$. If a prescribed field extension $K_{0,v}'/K_{0,v}$ is part of the seed, the local algebra must contain that factor and the point is evaluated in $Y^\circ(K_{0,v}')$.

These are different inputs. Constructing a point after an unramified extension does not prove that the original local field has a point. Nor does one chosen embedding control all conjugates. The global local-algebra datum must place every factor in the desired neighborhood.

Persistence makes this usable. Suppose a specialized global point is locally an extension of a seed in $\Omega_v$. Good, ordinary, nonordinary, semistable, and finite-flat properties survive restriction to that extension by Chapter 11. When exact valuation or nonsplitness matters, the completion data must also control ramification index or residue field, since those invariants can change.

At real places a split algebra $\mathbf R^n$ ensures that every embedding remains real and every conjugate point belongs to the chosen real open. A single real point without a split real local condition is not enough to force total reality.

### 13.4 Failure modes

The local package fails in recognizable ways.

**Wrong determinant.** If (9.2) is absent, the paired twist is empty even if the unpaired representations are isomorphic.

**Wrong component.** A point on another polarization or determinant component does not give a local point on $Y^\circ$.

**Finite flat but not realized.** A finite-flat $V_{\mathfrak p}$ need not be the torsion of a polarized real-multiplication abelian variety on the selected component. PEL realization must be constructed or assumed.

**Separate frames.** Realizing $V_{\mathfrak p}$ and $V_{\mathfrak q}$ on different abelian varieties does not give a point of the fiber-product twist.

**Closed is not open.** Nonordinarity is imposed by a residue tube around a seed, not by calling its special-fiber closed locus open.

**Generic is not integral.** A basis of characteristic-zero torsion does not determine a finite flat special-fiber group scheme.

**Semistable is not good.** Tate $p$-torsion can be finite flat while the Tate curve remains multiplicative.

**Unramified is not arbitrary.** Local solvability after an unramified extension must be encoded in the global completion algebra; it cannot be silently descended.

**Persistence is not constancy.** Semistability persists under ramification, but discriminant valuation and component counts rescale.

Each failure identifies a concrete repair: change the determinant datum, choose the correct component, construct a PEL seed, solve the two frames simultaneously, pass to a residue tube, retain an integral model, or strengthen the prescribed local algebra.

## 14. Conclusion

### 14.1 The local dictionary

The five local conditions are controlled by five different pieces of geometry:

$$
\begin{array}{c|c}
\text{condition}&\text{controlling datum}\\ \hline
\text{real}&\text{fixed real component and odd involution},\\
\text{good}&\text{smooth integral moduli point},\\
\text{ordinary}&\text{nonvanishing partial Hasse invariants},\\
\text{nonordinary finite flat}&\text{fixed local--local special point plus generic frame},\\
\text{semistable}&\text{semiabelian boundary parameters and Kummer class}.
\end{array}
\tag{14.1}
$$

The topology required by arithmetic approximation is obtained correspondingly from a real component, an integral residue tube, an ordinary open tube, a fixed nonordinary residue disk, or a semistable valuation shell. Paired torsion frames are then preserved by finite etale local sections on the characteristic-zero generic fiber.

### 14.2 The package established

We constructed explicit local points by tensoring elliptic curves with invertible $\mathcal O_F$-ideals. Trace duality computed their polarization module as

$$
\mathfrak c_I=\mathfrak d_F^{-1}I^{-2},
$$

proved the Hilbert determinant condition, and recovered the correct inverse-different coefficient line in torsion pairings. Real tensor points gave the odd-involution criterion. Smooth special-fiber points lifted to good points after controlled unramified extension. Ordinary and supersingular Legendre curves produced the two good residue-characteristic types, with finite-flat torsion treated scheme-theoretically. Tate curves supplied split semistable points, exact triangular torsion representations, and the criterion $p\mid v(q)$ for finite flat residual Tate torsion over an unramified odd-prime base.

The openness proofs retain exactly what specialization needs. Ordinary reduction is open by Hasse invariants. Nonordinary reduction is retained on an open residue tube despite being closed in the special fiber. Semistability is retained by keeping boundary parameters in fixed valuation shells. Exact torsion representations and both frames are locally constant through finite etale isomorphism schemes. All conditions are intersected only after one common point on the chosen twist and component has been exhibited.

Finally, the persistence theorem separates stable properties from changing numerical data. Good reduction, ordinary or local--local type, semistability, toric rank, and finite flatness survive finite extension. Splitness can improve, frames need not descend, and valuations rescale. With these qualifications visible, the neighborhoods produced here are precisely legitimate local-open inputs for a Moret--Bailly specialization: they are nonempty, component-correct, determinant-compatible, stable under the allowed completions, and strong enough to recover the intended arithmetic condition at every resulting conjugate.
