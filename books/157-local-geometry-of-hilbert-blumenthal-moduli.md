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
  - [3.5 The tensor component and the exact catalog reduction](#35-the-tensor-component-and-the-exact-catalog-reduction)
- [4. Real local points](#4-real-local-points)
  - [4.1 Real points are component data](#41-real-points-are-component-data)
  - [4.2 The underlying tensor real point](#42-the-underlying-tensor-real-point)
  - [4.3 The cyclotomic-split auxiliary level](#43-the-cyclotomic-split-auxiliary-level)
  - [4.4 Odd involutions and paired frames](#44-odd-involutions-and-paired-frames)
  - [4.5 Openness at infinity](#45-openness-at-infinity)
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
  - [8.5 The full-dimensional Mumford chart](#85-the-full-dimensional-mumford-chart)
  - [8.6 Semistable neighborhoods](#86-semistable-neighborhoods)
- [9. Twisted two-prime covers and local solvability](#9-twisted-two-prime-covers-and-local-solvability)
  - [9.1 What a point of the twist says](#91-what-a-point-of-the-twist-says)
  - [9.2 The determinant obstruction](#92-the-determinant-obstruction)
  - [9.3 Good-prime solvability](#93-good-prime-solvability)
  - [9.4 Coefficient-prime solvability](#94-coefficient-prime-solvability)
  - [9.5 Simultaneous frames](#95-simultaneous-frames)
  - [9.6 Base-field points at sufficiently large good places](#96-base-field-points-at-sufficiently-large-good-places)
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
  - [13.2A The stable integral connecting-slice boundary](#132a-the-stable-integral-connecting-slice-boundary)
  - [13.3 Passing from neighborhoods to every conjugate](#133-passing-from-neighborhoods-to-every-conjugate)
  - [13.4 Failure modes](#134-failure-modes)
- [14. Conclusion](#14-conclusion)
  - [14.1 The local dictionary](#141-the-local-dictionary)
  - [14.2 The package established and its boundaries](#142-the-package-established-and-its-boundaries)

## 1. From a global moduli space to local arithmetic

### 1.1 Why local points are the missing input

The preceding construction of Hilbert--Blumenthal moduli solves a global geometric problem. It gives a smooth fine scheme, pairing-preserving torsion-frame covers, twists by prescribed representations, and geometrically connected components. An arithmetic approximation theorem, however, does not manufacture a point on such a space from geometry alone. At every selected completion it must be given a nonempty open set of points having the required local behavior.

This changes the nature of the question. It is not enough to know that some Hilbert--Blumenthal abelian variety exists over an algebraic closure. One needs an object over a specified local field, on the specified twist and component, and one must know that nearby objects retain the desired condition. At a real place, “nearby” refers to the ordinary real topology. At a finite place, it refers to the topology defined by the valuation. At a residue-characteristic level prime, generic torsion is etale but its integral model is not, so a basis of geometric points does not see the finite-flat condition. At a semistable place, the abelian variety need not extend as an abelian scheme at all.

The purpose of this book is to turn those distinctions into a reusable local package. We construct seed points of five kinds: real, good, ordinary, nonordinary finite-flat, and semistable, put them on one corrected auxiliary-level component, and place each in a full-dimensional local neighborhood. The correction has three parts. The auxiliary principal level is given a cyclotomic-split source, so it has real points. A rank-$d$ Mumford period torus is algebraized at the tensor cusp, so the one-parameter Tate ray sits inside an ambient semistable chart. Finally, the polarization and component used in the potential-automorphy catalog are proved to be auxiliary choices and are reduced to the single tensor component. The endpoint is an unconditional local-open package with exactly the inputs required by arithmetic approximation.

### 1.2 Standing data and conventions

Fix a totally real field $F$ of degree $d$, with ring of integers $\mathcal O_F$, different $\mathfrak d_F$, and discriminant $D_F$. Fix an invertible fractional $\mathcal O_F$-ideal $I$ and put

$$
\mathfrak c_I=\mathfrak d_F^{-1}I^{-2},
\qquad
\mathfrak c_I^\vee
=\mathfrak d_F^{-1}\mathfrak c_I^{-1}
=I^2.
\tag{1.0}
$$

The ordered cone is the totally positive cone $\mathfrak c_I^+$. Fix an auxiliary integer $N\geq3$, write $\mathfrak n=N\mathcal O_F$, and assume $N$ is prime to every prime at which integral geometry will be used. The tensor PEL lattice is

$$
L_I=I\oplus I,
\qquad
\psi_I((a,b),(a',b'))=ab'-a'b\in I^2=\mathfrak c_I^\vee.
\tag{1.1a}
$$

Unlike the constant paired orientation in Book 156, the auxiliary level source used here is the finite etale local system

$$
\mathscr L_{I,N}^{\natural}
=(I/NI)\oplus(I/NI)(1),
\tag{1.1b}
$$

with its perfect alternating pairing

$$
\psi_{I,N}^{\natural}((a,b),(a',b'))
=ab'-a'b
\in(I^2/NI^2)(1).
\tag{1.1c}
$$

Thus $\det\mathscr L_{I,N}^{\natural}=(I^2/NI^2)(1)$ before any trivialization. This is the decisive real-level correction.

Fix two distinct prime ideals

$$
\mathfrak p\mid p,
\qquad
\mathfrak q\mid q
$$

of distinct rational residue characteristics. Unless a section explicitly studies one of $p$ or $q$ as the residue characteristic, we exclude every rational prime below the support of $D_F$, $N$, $pq$, or the numerator or denominator of $I$. Thus the coefficient algebra is unramified, the polarization pairing is perfect, and the displayed prime-to-residue-characteristic torsion is finite etale.

Write $H_I^{\natural}$ for the corrected fine Hilbert--Blumenthal scheme. Its points are quadruples

$$
(A,\iota,\lambda,\eta_{\mathfrak n}^{\natural}),
$$

where $A$ has relative dimension $d$, $\iota:\mathcal O_F\to\operatorname{End}(A)$ satisfies the Hilbert determinant condition, $\lambda$ identifies $(\mathfrak c_I,\mathfrak c_I^+)$ with the ordered polarization module and makes $A\otimes_{\mathcal O_F}\mathfrak c_I\to A^\vee$ an isomorphism, and

$$
\eta_{\mathfrak n}^{\natural}:
\mathscr L_{I,N}^{\natural}\xrightarrow{\sim}A[N]
\tag{1.1d}
$$

is an isometry. No separate orientation from a constant line to a Tate twist occurs. Chapter 4 proves that this functor is a smooth fine scheme and that, geometrically, it is the fixed-pairing orientation subfunctor of the principal-level scheme of Book 156. From Section 3.5 onward, $H_I^{\mathrm{ten}}\subset H_I^{\natural}$ denotes the single component containing the tensor locus. The two-prime twist $Y_I^{\mathrm{ten}}\to H_I^{\mathrm{ten}}$ additionally carries pairing-preserving isomorphisms

$$
\alpha_{\mathfrak p}:V_{\mathfrak p}\xrightarrow{\sim}A[\mathfrak p],
\qquad
\alpha_{\mathfrak q}:V_{\mathfrak q}\xrightarrow{\sim}A[\mathfrak q].
\tag{1.1e}
$$

Here each $V_{\mathfrak r}$ has determinant equal, as a local system with a specified isomorphism, to

$$
\mathscr D_{\mathfrak r}
=(I^2\otimes k_{\mathfrak r})(1).
\tag{1.2}
$$

This determinant identification is part of the datum. Equality of determinant characters without a chosen identification does not define the paired twist.

For the rest of the book, unless an arbitrary-polarization variant is explicitly discussed, write

$$
H=H_I^{\mathrm{ten}},
\qquad
Y=Y_I^{\mathrm{ten}},
\qquad
\mathfrak c=\mathfrak c_I.
\tag{1.3}
$$

At a finite place let $K$ be a finite extension of $\mathbf Q_r$, let $R$ be its valuation ring, $\pi$ a uniformizer, and $k$ its finite residue field. We normalize $v_K(\pi)=1$. An **unramified local base** means $K=W(k)[1/r]$, equivalently $v_K(r)=1$. Completion, henselization, and unramified extension are never silently identified.

### 1.3 The five local conditions

The words used in the catalog have precise meanings.

A **real point** is a point of the tensor component $Y_I^{\mathrm{ten}}(\mathbf R)$. For odd torsion primes its prescribed representations must be odd: complex conjugation has eigenvalues $1$ and $-1$ and determinant $-1$. The corrected auxiliary source (1.1b) has the same $+1,-1$ involution, so there is no additional archimedean orientation obstruction.

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

This is the precise reason a fixed torsion representation is locally constant on a framed moduli space. Once the frames (1.1e) exist at one point, the finite etale isomorphism schemes give them throughout a sufficiently small neighborhood. No choice of matrices has to be continued by hand.

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

Assume first that $S$ is connected. An $\mathcal O_F$-linear symmetric map $A\to A^\vee$ is therefore multiplication by an element of

$$
\operatorname{Hom}_{\mathcal O_F}(I,I^\dagger)
=I^{-1}I^\dagger
=\mathfrak d_F^{-1}I^{-2}.
\tag{3.4}
$$

There is a small point hidden in this assertion: an elliptic curve can have extra endomorphisms, especially after supersingular reduction. They do not create extra symmetric directions. On a geometric fiber choose a prime $\ell$ different from its characteristic. Under the canonical principal polarization, the Rosati adjoint on the rational rank-two Tate module is adjoint with respect to its perfect alternating form. If a $2\times2$ matrix $M$ is self-adjoint for such a form, then

$$
M^tJ=JM,
\qquad
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
$$

and direct multiplication forces $M$ to be scalar. Faithfulness of the Tate module action makes every symmetric rational endomorphism of that fiber a rational scalar; integrality makes it an integer. A homomorphism of abelian schemes that is multiplication by $n$ on one geometric fiber is multiplication by the same $n$ on the connected base: the equalizer is closed, and rigidity for homomorphisms of abelian schemes makes it open. Hence

$$
\operatorname{End}^{\mathrm{sym}}(E)=\mathbf Z
$$

even in the CM and supersingular cases. Tensor--Hom adjunction now gives exactly (3.4), with no additional symmetric factor. On a disconnected base the same assertion is read componentwise, so the polarization module is the corresponding locally constant sheaf.

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

### 3.5 The tensor component and the exact catalog reduction

The explicit tensor family reaches exactly the ordered types

$$
\mathfrak c\simeq\mathfrak d_F^{-1}I^{-2}
\quad\text{through multiplication by a totally positive element.}
\tag{3.10}
$$

Equivalently, the narrow class of $\mathfrak d_F\mathfrak c$ is a square. This restriction is real: if the narrow class group has a nonsquare class, the corresponding Hilbert moduli problem is legitimate but no tensor power of one elliptic curve has that ordered polarization module.

The restriction does not leave a component ambiguity in the range used below. Let $\mathcal M_N^{\natural}$ be the fine modular curve classifying an elliptic curve together with an isometry

$$
(\mathbf Z/N\mathbf Z)\oplus\mu_N
\xrightarrow{\sim}E[N]
\tag{3.11}
$$

for the standard pairing with values in $\mu_N$. Let $B_I$ be the good base obtained by also inverting every rational prime below the numerator or denominator of $I$. Tensoring (3.11) with $I$ defines a morphism over $B_I$

$$
t_I:\mathcal M_N^{\natural}\longrightarrow H_I^{\natural},
\qquad E\longmapsto E\otimes I.
\tag{3.12}
$$

After base change to an algebraic closure and a choice of primitive $N$th root, the source is the connected analytic curve $\Gamma(N)\backslash\mathfrak H$. Hence its image lies in one geometric component of $H_I^{\natural}$; denote that component by $H_I^{\mathrm{ten}}$.

**Proposition 3.2 (the tensor component).** The component $H_I^{\mathrm{ten}}$ is defined over $\mathbf Q$. Every real, good, ordinary, supersingular, and Tate tensor seed constructed in this book, with the tensor-induced corrected auxiliary level, lies on this component. For monodromy-admissible $\mathfrak p$ and $\mathfrak q$, the determinant-compatible two-prime twist over it is smooth and geometrically connected.

**Proof.** The curve $\mathcal M_N^{\natural}$ and the morphism (3.12) are defined over $\mathbf Q$. If $C$ is the unique geometric component containing the connected image, then for every $\sigma\in G_{\mathbf Q}$ the component $\sigma C$ contains the same image, because (3.12) is equivariant. Components are disjoint, so $\sigma C=C$; the open-and-closed component therefore descends to $\mathbf Q$. Each tensor seed is, by construction, the image of its elliptic seed with (3.11), proving the second assertion. Over an algebraic closure the corrected auxiliary level becomes one fixed-pairing orientation of the principal level for the lattice $I\oplus I$. Book 156's simultaneous congruence theorem on that geometric component therefore gives full

$$
\operatorname{SL}_2(k_{\mathfrak p})
\times\operatorname{SL}_2(k_{\mathfrak q})
$$

monodromy on $C$. Its frame torsor is geometrically connected, and an arithmetic determinant-compatible twist is geometrically isomorphic to it. Smoothness follows from smoothness of the base and finite etaleness of the two generic frame covers. $\square$

We now isolate why this one component covers the intended catalog rather than merely one convenient example.

**Theorem 3.3 (exact component reduction).** Consider a two-prime realization problem in which the prescribed data are $F$, two rank-two residual systems with specified cyclotomic determinant isomorphisms, their local conditions, and the desired field-theoretic output, while the ordered polarization ideal, PEL lattice, neat auxiliary level, and Hilbert component are auxiliary choices. Then one may, without changing any prescribed representation or local conclusion, take

$$
I=\mathcal O_F,
\qquad
\mathfrak c=\mathfrak d_F^{-1},
\qquad
\mathfrak c^\vee=\mathcal O_F,
\qquad
H^{\circ}=H_{\mathcal O_F}^{\mathrm{ten}}.
\tag{3.13}
$$

Thus every such catalog case is covered by the component in Proposition 3.2. If an external application prescribes a nonsquare narrow polarization class, the reduction does not apply and this book makes no universal seed claim for that different problem.

**Proof.** In the realization space the polarization ideal and auxiliary level serve only to make a smooth fine PEL scheme, normalize the Weil-pairing determinant, and select a geometrically connected component. They do not occur in the desired residual representations or in the final automorphy statement. Choose $N\geq3$ prime to the finite set of coefficient and controlled residue characteristics. With the choice (3.13), the determinant coefficient line in (1.2) is the constant line with its cyclotomic twist, exactly the cyclotomic determinant required of both residual systems. Proposition 3.2 supplies a $\mathbf Q$-defined smooth component, the corrected level supplies real points, and all five local tensor seeds lie on it. Replacing a previously provisional auxiliary polarization, level, and component by these choices therefore changes none of the prescribed arithmetic data. Conversely, if $\mathfrak c$ is externally fixed, changing it would change the moduli problem and the coefficient line; that is why the final sentence is necessary. $\square$

From here on the word **intended component** means the tensor component of Proposition 3.2, with (3.13) in the catalog application. This is an exact scope statement, not an assertion that all narrow polarization classes are squares.

## 4. Real local points

### 4.1 Real points are component data

At a real place there is no valuation ring and no reduction. The local condition is membership in a connected component of the real manifold $Y(\mathbf R)$. Complex uniformization writes a geometric Hilbert component as an arithmetic quotient of a product of upper and lower half-planes. Complex conjugation reverses every half-plane. A real structure is therefore an antiholomorphic involution compatible with the lattice, polarization, level, and torsion descent.

Not every complex component need have a real point over its field of definition. For the intended component this is no longer an assumption: Proposition 3.2 defines it over $\mathbf Q$, the tensor construction supplies the underlying real PEL object, the cyclotomic-split level supplies its auxiliary rigidification, and oddness supplies the two residual frames. We prove those four assertions separately so that real component data are not confused with a determinant-character calculation.

### 4.2 The underlying tensor real point

Let $E/\mathbf R$ be

$$
E:y^2=x^3-x.
\tag{4.1}
$$

Its discriminant is nonzero, so it is an elliptic curve. Equivalently, over $\mathbf C$ it is $\mathbf C/(\mathbf Z+i\mathbf Z)$, with complex conjugation induced by $z\mapsto\bar z$. For an invertible ideal $I$, put $A=E\otimes I$. Proposition 3.1 gives real multiplication and the $\mathfrak c_I$-polarization. Every construction is defined over $\mathbf R$.

For a more flexible analytic description, choose positive real numbers $y_\tau$ indexed by embeddings $\tau:F\hookrightarrow\mathbf R$ and put $z_\tau=iy_\tau$. The lattice determined by $I$ and its trace dual is stable under conjugation because $\bar z_\tau=-z_\tau$. The trace alternating form changes sign together with the complex structure and hence defines the same real polarization. Varying the $y_\tau$ fills a real cell inside the selected fixed component.

### 4.3 The cyclotomic-split auxiliary level

We first record why the literal Book 156 level cannot be retained. Its auxiliary orientation includes an isomorphism

$$
\delta_{\mathfrak n}:
(\mathfrak c^\vee/\mathfrak n\mathfrak c^\vee)_{\mathbf R}
\xrightarrow{\sim}
(\mathfrak c^\vee/\mathfrak n\mathfrak c^\vee)_{\mathbf R}(1).
\tag{4.2a}
$$

Complex conjugation acts trivially on the source and by $-1$ on the cyclotomic target. If (4.2a) were equivariant, every element in its image would satisfy $x=-x$. For $N\geq3$ the subgroup killed by $2$ is a proper subgroup of the target, so no isomorphism can have this property. Consequently the literal full paired auxiliary-level scheme $H_{\mathfrak c,\mathfrak n}$ of Book 156 has no real points.

The correction is (1.1b), not a choice of a root of unity. Complex conjugation acts trivially on its first summand and by inversion on its second. Its determinant is already $(I^2/NI^2)(1)$, so an isometry to $A[N]$ requests no impossible orientation.

**Theorem 4.1 (corrected principal level).** The functor $H_I^{\natural}$ is represented by a smooth quasi-projective fine scheme of relative dimension $d$ over the good base and carries a universal tuple. After base change to an algebraic closure and a choice of primitive $N$th root, it is isomorphic to the fixed-pairing orientation subfunctor of Book 156's principal-level scheme for the PEL lattice $L_I=I\oplus I$. It has a real tensor point, and Book 156's geometric component and two-prime product-monodromy assertions hold on each resulting geometric component.

**Proof.** The local system $\mathscr L_{I,N}^{\natural}$ is finite etale where $N$ is invertible, and (1.1c) is perfect because $I$ is invertible. Its isometry sheaf to $A[N]$ is therefore a finite etale level sheaf on the unlevelled PEL stack. Choose over an algebraic closure a primitive $N$th root of unity. This trivializes the Tate-twisted second summand and the value line, turning (1.1b)--(1.1c) into the constant paired lattice $(L_I/NL_I,\psi_I)$ with one fixed value-line orientation in Book 156. Thus the corrected problem becomes exactly that open-and-closed orientation subfunctor.

An automorphism preserving $\eta_{\mathfrak n}^{\natural}$ acts trivially on $A[N]$. The principal-congruence torsion-freeness argument for $N\geq3$ makes it the identity. The PEL stack is therefore a scheme with a universal object. The level sheaf is finite etale, so it adds no infinitesimal deformation; lifting one Hodge line for every embedding gives smoothness of relative dimension $d$, exactly as for Book 156. Quasi-projectivity follows from the same polarized Hilbert parameter construction.

For the curve $E=\mathbf C/(\mathbf Z+i\mathbf Z)$, let $P$ be the class of $1/N$. It spans a constant cyclic subgroup, while the class of $i/N$ spans its anti-invariant complement. The map

$$
Q\longmapsto e_N(P,Q)
$$

identifies that complement $G_{\mathbf R}$-equivariantly with $\mu_N$; use its inverse for the second level vector. Hence there is a paired $G_{\mathbf R}$-equivariant isomorphism

$$
(\mathbf Z/N\mathbf Z)\oplus\mu_N\xrightarrow{\sim}E[N].
\tag{4.2b}
$$

Tensoring (4.2b) with $I$ gives (1.1d) on $E\otimes I$. This is the promised real point. Finally, geometric isomorphism of the auxiliary levels identifies their arithmetic stabilizers after conjugation. The determinant component calculation and simultaneous reduction onto the two special-linear factors are therefore unchanged. $\square$

The same correction is integral away from $N$. Both summands of (1.1b) are finite etale, and a corrected level on a good special fiber lifts uniquely through nilpotent thickenings. At a Tate cusp the constant summand is represented by a chosen $N$th root of the period and the cyclotomic summand by toric $N$-torsion; Section 8.5 builds both into the algebraized chart.

There is a second correction which is useful when a later application requires points over
specified base completions rather than after completion extension.  The source of the neat
level is auxiliary; it need not be the split module (1.1b).

**Proposition 4.1A (elliptic-source rigidification).**  Let $K_0$ be a number field, let
$E_*/K_0$ be an elliptic curve, and let $N\geq3$ be invertible on the base under
consideration.  Put

$$
\mathscr L_{I,N}^{E_*}=E_*[N]\otimes_{\mathbf Z/N\mathbf Z}I/NI,
\tag{4.2c}
$$

with the alternating form induced by the Weil pairing and multiplication
$I/NI\otimes I/NI\to I^2/NI^2$.  Replace (1.1d) by a paired isomorphism

$$
\eta_N^{E_*}:\mathscr L_{I,N}^{E_*}\xrightarrow{\sim}A[N].
\tag{4.2d}
$$

Then this functor is a smooth quasi-projective fine scheme of relative dimension $d$.  It has
a $K_0$-point given by $E_*\otimes I$ and the identity frame.  The geometric component
$H_I^{E_*,\mathrm{ten}}$ containing the image of the corresponding twisted modular curve is
defined over $K_0$.  Every tensor point $B\otimes I$ carrying a paired isomorphism
$E_*[N]\simeq B[N]$ lies on this component.  On it the prime-level and two-prime frame covers
have exactly the geometric monodromy asserted in Book 156, Theorems 10.2 and 11.2; in
particular every determinant-compatible two-prime arithmetic twist is geometrically connected.

**Proof.**  The local system (4.2c) is finite etale and its pairing is perfect.  Over
$\overline K_0$, choose a paired basis of $E_*[N]$.  This identifies (4.2c) with one
fixed-pairing orientation of the constant principal-level lattice.  Consequently the new
functor is an arithmetic twist of the same geometric level scheme used in Theorem 4.1.
Representability, fineness, smoothness, and relative dimension follow by the identical
finite-etale descent and deformation argument.  The identity on $E_*[N]$, tensored with $I$,
gives the displayed $K_0$-point.

The determinant-compatible twist of the full-level modular curve by $E_*[N]$ is geometrically
the usual connected fixed-pairing modular curve.  Its tensor morphism is defined over $K_0$.
Hence the unique Hilbert component containing its connected image is Galois-stable and descends
to $K_0$.  A tensor point equipped with (4.2d) is a point of that same twisted modular curve,
so it lies on the descended component.  Geometrically the auxiliary-level stabilizer is merely
a conjugate of the principal congruence subgroup $\Gamma(N)$.  The simultaneous elementary-
matrix reductions used in Book 156 are therefore unchanged.  They give the same special-linear
monodromy at each prime and the same product monodromy at two primes.  Finally an arithmetic
twist changes only descent, so Book 156, Corollary 11.3 gives geometric connectedness. $\square$

The point of Proposition 4.1A is not to assert that an arbitrary local elliptic curve has the
split level (1.1b).  It lets the auxiliary source be selected after finitely many base-field
tensor seeds have been chosen.  The following elementary approximation supplies such a source.

**Lemma 4.1B (one elliptic source for finitely many local seeds).**  Let $K_0$ be a number
field, let $S$ be finite, and for each $v\in S$ let $B_v/K_{0,v}$ be an elliptic curve.  Fix
$N\geq3$ prime to the residue characteristics in $S$.  There is an elliptic curve $E_*/K_0$
and paired isomorphisms

$$
E_*[N]|_{G_{K_{0,v}}}\simeq B_v[N]
\qquad(v\in S).
\tag{4.2e}
$$

The curve $E_*$ may simultaneously be required to lie in any prescribed sufficiently small
local neighborhoods of the $B_v$ in the smooth Weierstrass parameter space.  Thus every
locally constant generic torsion invariant and every open reduction condition imposed on those
neighborhoods is retained.

**Proof.**  Choose general Weierstrass equations for the $B_v$.  The nonzero-discriminant locus
in the affine five-coefficient space is smooth and open.  Over it the paired $N$-torsion
isomorphism scheme from the fixed fiber $B_v[N]$ to the universal fiber is finite etale and has
the identity point above the chosen equation.  Proposition 2.3 gives a local section on a
sufficiently small coefficient neighborhood.  Weak approximation in the five coefficients
chooses one tuple in $K_0^5$ inside every such neighborhood and outside the discriminant
hypersurface.  Its curve is $E_*$.  Evaluating the local sections gives (4.2e), with pairings
preserved because the isomorphism schemes were paired. $\square$

### 4.4 Odd involutions and paired frames

Let $s$ be odd and let $c\in G_{\mathbf R}=\{1,c\}$ be complex conjugation. On $E[s]$, the determinant of $c$ is the mod-$s$ cyclotomic value $-1$. Since $c^2=1$ and $2$ is invertible in $\mathbf F_s$, the representation splits into its $+1$ and $-1$ eigenspaces. Their product is $-1$, so each has dimension one. In a suitable paired basis,

$$
c\longmapsto
\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
\tag{4.2}
$$

After scalar extension, the same is true on $A[\mathfrak r]$ for every $\mathfrak r\mid s$.

**Proposition 4.2 (real frame criterion).** Let $s$ be odd. A determinant-compatible rank-two $k_{\mathfrak r}$-representation $V_{\mathfrak r}$ of $G_{\mathbf R}$ admits a paired isomorphism to $A[\mathfrak r]$ if and only if $\det(c)=-1$. When it does, any isomorphism between the $+1$ lines, followed by the uniquely normalized isomorphism between the $-1$ lines, gives a paired frame.

**Proof.** Necessity follows from the pairing determinant. Conversely, $c^2=1$ makes $V_{\mathfrak r}$ semisimple with eigenvalues in $\{1,-1\}$. Determinant $-1$ forces one of each. Choose nonzero $v_+$ and $v_-$ in the two eigenspaces. Their pairing is nonzero by perfectness: each eigenline is isotropic, and if the cross-pairing vanished the form would be degenerate. Rescale $v_-$ so the pairing equals that of a chosen eigenbasis of $A[\mathfrak r]$. The resulting map is equivariant and paired. $\square$

At $s=2$, $1=-1$ and this eigenspace argument disappears. Oddness cannot be encoded by the determinant of a two-dimensional $\mathbf F_2$-representation. A dyadic real frame requires the actual involution and pairing to be compared, not merely their characters.

For two odd primes, Proposition 4.2 applies independently. Theorem 4.1 has already supplied the auxiliary level on the same tensor point. Thus the tensor point lifts to $Y(\mathbf R)$ exactly when both prescribed local systems are odd and their determinant identifications match (1.2). In particular the intended twist has a real point at every real place of its totally real base.

### 4.5 Openness at infinity

The real points of a smooth variety form a real manifold. Connected components are open because manifolds are locally connected, and they are closed because components always are. The paired frame map is finite etale, hence a local diffeomorphism. Therefore a point $y\in Y(\mathbf R)$ constructed above has a small open neighborhood contained in its chosen component and carrying the same auxiliary and residual frame descent.

Sign conditions are also open: positivity of a real number survives a small perturbation, and the positive cone in $F\otimes\mathbf R\simeq\mathbf R^d$ is the open orthant. Consequently polarization positivity, orientation of every half-plane, and the real component label remain fixed in a sufficiently small neighborhood.

This proves the archimedean input for totally real specialization: one supplies this nonempty open at every real place. Supplying it at only one real place does not prevent other embeddings of the eventual field from becoming complex. The literal Book 156 level remains empty over $\mathbf R$; all downstream uses in this book are of the corrected scheme $H_I^{\natural}$ and its tensor component.

## 5. Good integral points away from the level primes

### 5.1 Smooth special fibers give good points

Let $r$ be a rational prime outside the discriminant, polarization, auxiliary-level, and two torsion-level sets. Assume also that the restrictions of $V_{\mathfrak p}$ and $V_{\mathfrak q}$ to $G_K$ are unramified and that their determinant identifications extend over $R$. Over $R$ the Hilbert moduli functor is represented by a smooth scheme $\mathcal H$. Both $\mathfrak p$- and $\mathfrak q$-torsion, as well as the two prescribed local systems, are finite etale over $R$, so the prescribed paired-frame twist extends to a finite etale scheme

$$
\mathcal Y\longrightarrow\mathcal H_R.
\tag{5.1}
$$

An $R$-point of $\mathcal Y$ is already the desired good local point with both frames. Thus local existence reduces to the elementary problem of finding a special-fiber point and lifting it.

**Theorem 5.1 (good lifting criterion).** Let $R$ be a complete DVR whose residue characteristic $r$ lies below none of the primes in the support of $D_F$, $N$, $pq$, or the numerator or denominator of $\mathfrak c$. If $\bar y\in\mathcal Y(k)$, then $\bar y$ lifts to $y\in\mathcal Y(R)$. Its image is a Hilbert--Blumenthal abelian scheme with good reduction and the prescribed two paired frames. The full residue tube $]\bar y[_{\mathcal Y}$ is a nonempty open set of such points.

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

Now let the residue characteristic be an odd prime $p$, assume $K/\mathbf Q_p$ is unramified, and assume that $p$ is unramified in $F$ and lies below neither the support of the numerator or denominator of $\mathfrak c$ nor the auxiliary level $\mathfrak n$. The coefficient algebra decomposes

$$
\mathcal O_F\otimes\mathbf Z_p
=\prod_{\mathfrak r\mid p}\mathcal O_{F,\mathfrak r}.
\tag{6.1}
$$

There is an integral Hilbert moduli scheme $\mathcal H^{(p)}/R$ obtained by retaining the determinant condition, $\mathfrak c$-polarization, and auxiliary level but forgetting the $\mathfrak p$-frame integrally. Neat auxiliary level still removes automorphisms. Its smoothness follows from the same infinitesimal calculation as at primes away from the frame levels: after the etale coefficient algebra is split, de Rham cohomology is a sum of rank-two symplectic modules and the Hodge bundle selects one line in each. Across a square-zero thickening, every line in a rank-two alternating module is isotropic and lifts in an affine one-dimensional family. The $d$ factors lift independently, so there are no obstructions and the relative dimension is $d$. The generic fiber of $\mathcal H^{(p)}$ is $H_K$. What fails integrally is only the claim that paired $\mathfrak p$-frames form a finite etale cover.

For an abelian scheme $A/R$ with Hilbert determinant condition, the $p$-divisible group decomposes accordingly. The $\mathfrak r$-factor has $\mathcal O_{F,\mathfrak r}$-height two and $\mathcal O_{F,\mathfrak r}$-dimension one; as an ordinary $p$-divisible group its height and dimension are multiplied by $[F_{\mathfrak r}:\mathbf Q_p]$. It is **ordinary** if its connected--etale sequence has an $\mathcal O_{F,\mathfrak r}$-height-one multiplicative connected part and an $\mathcal O_{F,\mathfrak r}$-height-one etale quotient. At level one this has the form

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

Choose the corrected elliptic $N$-level after a finite unramified extension and tensor it with $I$; this is the level (3.12), so the seed lies on $H_I^{\mathrm{ten}}$. That auxiliary level and the $\mathfrak q$-frame become rational after a finite unramified extension because their isomorphism schemes are finite etale. A prescribed $\mathfrak p$-frame at the residue characteristic is more restrictive: it exists precisely when the generic representation $V_{\mathfrak p}$ is paired-isomorphic to the generic fiber of (6.6). Finite flatness or equality of semisimplifications alone does not supply that isomorphism.

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

Let $A=E\otimes I$ for the supersingular lift. After a finite unramified extension choose the corrected elliptic $N$-level and tensor it with $I$; Proposition 3.2 places the resulting object on the intended component. Then $A/R'$ is good and, for each $\mathfrak r\mid p$, its special-fiber $\mathfrak r$-torsion is local--local. Indeed $E[p]$ has neither an etale nor a multiplicative height-one direct factor in the supersingular case; Frobenius and Verschiebung are nilpotent on its height-two Dieudonne plane. Scalar extension by $I/\mathfrak rI$ preserves this property.

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

for one of the constructed ordinary or supersingular lifts. Under (7.2), the corresponding frame in (1.1e) exists and the point lies on the exact twist. This is stronger than asking that $V_{\mathfrak p}$ and the right side have the same semisimplification.

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

Over an unramified odd-prime base, the two inertia characters $\overline\chi_p$ and $1$ are distinct, so the multiplicative generic line is intrinsic. To turn this observation into an assertion about integral models one needs the rigidity proved in the finite-flat books. Suppose $\mathcal G/R$ is any finite flat model of the abstract Tate representation. The schematic closure $\mathcal H$ of the intrinsic line in $\mathcal G$ is finite flat: on coordinate rings, quotienting by the saturated Hopf ideal gives a finite torsion-free, hence free, $R$-module. Its generic fiber is $\mu_{p,K}$. Raynaud full faithfulness in ramification index $1<p-1$, together with the rank-$p$ classification, identifies $\mathcal H$ with $\mu_p$. The fppf quotient $\mathcal G/\mathcal H$ is finite flat with constant generic fiber and is therefore the constant group $\mathbf Z/p\mathbf Z$ by the same rigidity. Thus every finite flat model would extend the canonical Tate filtration. The necessity already proved for that filtration now applies. Under these hypotheses (8.6) is therefore a criterion for the abstract residual representation, not only for a chosen extension presentation.

After tensoring by $I/\mathfrak pI$, the same criterion makes $A_{q_0}[\mathfrak p]$ finite flat. The abelian variety remains multiplicative. At $p=2$, the cyclotomic character modulo $2$ is trivial and the intrinsic-line argument fails; even valuation still constructs the canonical model, but abstract necessity needs separate dyadic classification.

For example, over an unramified $p$-adic field take

$$
q_0=\pi^p u,
\qquad u\in R^\times.
\tag{8.9}
$$

Then $E_{q_0}$ has split multiplicative reduction with minimal discriminant exponent $p$, while $E_{q_0}[p]$ is finite flat. The generic representation is normally ramified because its multiplicative line carries $\overline\chi_p$; finite flat is therefore not synonymous with unramified. If instead $q_1=\pi u$, the two curves have the same coarse reduction type and the same diagonal characters, but $E_{q_1}[p]$ is not finite flat over an unramified odd-prime base. The exponent distinguishes the integral torsion models.

### 8.5 The full-dimensional Mumford chart

We now construct the missing ambient chart. Put

$$
I^\dagger=\mathfrak d_F^{-1}I^{-1},
\qquad
T_I=\underline{\operatorname{Hom}}_{\mathbf Z}(I^\dagger,\mathbf G_m).
\tag{8.10}
$$

The character lattice of $T_I$ is $I^\dagger$ and its cocharacter lattice is $I$. The Fourier-exponent lattice at the tensor cusp is

$$
\mathfrak M=I I^\dagger=\mathfrak d_F^{-1},
\tag{8.11}
$$

which has rank $d$ over $\mathbf Z$. To carry full level $N$, use $\mathfrak M_N=N^{-1}\mathfrak M$. Write $Q^\xi$ for the character indexed by $\xi\in\mathfrak M_N$.

Trace duality identifies $\mathfrak M^\vee$ with $\mathcal O_F$. Let $C^\vee$ be the open cone of real homomorphisms $\nu:\mathfrak M\to\mathbf R$ that are positive on every nonzero totally positive element of $\mathfrak M$. The tensor functional

$$
\nu_{\mathrm{ten}}(\xi)=\operatorname{Tr}_{F/\mathbf Q}(\xi)
\tag{8.12}
$$

is integral and lies in $C^\vee$. Choose a full-dimensional regular rational polyhedral cone $\sigma\subset C^\vee$ having $\nu_{\mathrm{ten}}$ in its interior. Begin with a rational simplicial cone around the fixed ray and apply toric desingularization, choosing subdivision centers away from that ray; this gives a unimodular cone still containing it in the interior. If cusp units are retained, take all their translates and a common locally finite refinement. Dirichlet's unit theorem makes the projectivized positive cone modulo totally positive units compact, so only finitely many cone orbits are needed. For the local chart one cone containing (8.12) suffices.

Let $R$ be a complete DVR on the good PEL base. Put

$$
P_\sigma=\sigma^\vee\cap\mathfrak M_N,
\qquad
A_\sigma=\widehat{R[P_\sigma]}
\tag{8.13}
$$

where completion is along the ideal generated by the nonzero boundary monomials. Regularity of $\sigma$ gives parameters $t_1,\ldots,t_d$ and an isomorphism, after a finite etale coefficient extension if the cusp label requires one,

$$
A_\sigma\simeq R'[[t_1,\ldots,t_d]].
\tag{8.14}
$$

This is a complete algebraic base, not merely a list of period formulas.

Over the locus where all boundary monomials are invertible, define the universal period map

$$
u_Q:I\longrightarrow T_I,
\qquad
x(u_Q(a))=Q^{ax}
\quad(a\in I, x\in I^\dagger).
\tag{8.15}
$$

The exponent $ax$ belongs to $\mathfrak d_F^{-1}$, so (8.15) is defined over $A_\sigma$. It is $\mathcal O_F$-balanced. For $c\in\mathfrak c_I^+$, the map

$$
I\longrightarrow I^\dagger,
\qquad a\longmapsto ca
\tag{8.16}
$$

gives the multiplicative period form

$$
(a,b)\longmapsto Q^{abc}.
\tag{8.17}
$$

It is symmetric, and for every $\nu\in\sigma$ its valuation on $(a,a)$ is $\nu(a^2c)>0$ when $a\ne0$. Thus (8.17) is a positive Riemann form. As $c$ ranges through $\mathfrak c_I$, (8.16) identifies $I\otimes\mathfrak c_I$ with $I^\dagger$, exactly the tensor-polarization isomorphism.

**Theorem 8.1 (algebraized tensor-cusp chart).** After possibly replacing $\sigma$ by a rational subdivision that still contains $\nu_{\mathrm{ten}}$ in the interior, the data (8.10)--(8.17) have the following algebraization over $A_\sigma$.

1. There is a projective flat Mumford family $\overline{\mathcal A}_\sigma\to\operatorname{Spec}A_\sigma$ with an open semiabelian group locus $\mathcal G_\sigma$. Over
   $$
   U_\sigma=\operatorname{Spec}A_\sigma[(t_1\cdots t_d)^{-1}]
   $$
   it is an abelian scheme; write this restriction as $\mathcal A_\sigma$. Over the closed cusp stratum $t_1=\cdots=t_d=0$, the identity component of $\mathcal G_\sigma$ is the split torus $T_I$ of dimension $d$.
2. Multiplication on $I$ gives an $\mathcal O_F$-action, (8.16)--(8.17) give the ordered $\mathfrak c_I$-polarization and a relatively ample symmetric bundle, and the Lie algebra satisfies the Hilbert determinant condition.
3. The $N$-division periods give the cyclotomic-split level
   $$
   \mathscr L_{I,N}^{\natural}\xrightarrow{\sim}\mathcal A_\sigma[N]
   $$
   on the abelian locus and the corresponding level of the boundary one-motive.
4. The classifying map from the punctured $d$-dimensional period polydisc to $H_I^{\mathrm{ten}}$ is etale in every period direction. Its tensor ray is $A_{q_0}=E_{q_0}\otimes I$.

**Proof.** We give the construction because an individual Tate variety would not prove the theorem. Start with an $I$-periodic rational triangulation of $I\otimes\mathbf R$. Add a generic $I$-periodic rational piecewise-linear perturbation to the quadratic support function defined by (8.17), small enough that it remains strictly convex for $\nu_{\mathrm{ten}}$. Convexity and compatibility across faces are finitely many strict rational linear inequalities modulo $I$. They therefore remain valid on a full-dimensional rational cone containing $\nu_{\mathrm{ten}}$ in its interior. Intersect that cone with $\sigma$, subdivide without putting the tensor ray on a wall, and take a common regular refinement of the triangulation. This proves the simultaneous fan assertion rather than assuming a fan adapted to every period independently. There are finitely many cells modulo $I$.

Each cell gives the standard toric formal chart for $T_I$ over $A_\sigma$; translation by $a\in I$ changes its character $x$ by the monomial $Q^{ax}$ from (8.15). The period identity

$$
Q^{(a+a')x}=Q^{ax}Q^{a'x}
$$

is exactly the cocycle on triple overlaps. The finitely many cell orbits therefore glue to a proper formal quotient. Fullness follows because every $\nu\in\sigma$ makes the pairing (8.17) positive definite, so a tropical point can be translated into a fixed finite union of cells. This is the higher-dimensional valuative argument used for Raynaud quotients.

Before completion, each toric chart algebra is a direct sum of copies of the base indexed by a saturated monoid. It is therefore $A_\sigma$-flat; completion and the open gluings preserve flatness. Hence the proper formal quotient is flat over $\operatorname{Spf}A_\sigma$.

The positive quadratic form (8.17) gives an integral strictly convex support function after multiplying by one positive integer. Its automorphy factors glue a relatively ample symmetric formal line bundle. The ample-line algebraization theorem for proper formal schemes algebraizes the quotient and that bundle uniquely to the projective $A_\sigma$-scheme $\overline{\mathcal A}_\sigma$. Equivalently, theta sections of a high power give the relative Proj; quadratic growth of (8.17) is their convergence and finite-generation estimate. This is the point at which the formal quotient becomes an algebraic family. Faithful completion transfers the formal flatness just proved to the algebraization. The toric action and period translations are monomial on the finitely many charts, so they algebraize the open semiabelian group locus $\mathcal G_\sigma$. More precisely, the polarized Raynaud quotient and periodic polyhedral model are the construction of Book 60, and algebraization of the proper formal scheme with its ample line bundle is the theorem of Book 58. Multiplying the support function only supplies an ample algebraizing bundle; it does not replace the exact maps (8.16). Those formal homomorphisms and their tensor-perfectness identities algebraize by graph effectivity. No compactification is being inferred from the open Hilbert scheme.

Multiplication by $b\in\mathcal O_F$ acts on the cocharacter lattice $I$, on the character lattice $I^\dagger$ contragrediently, and preserves (8.15). It therefore acts on $\mathcal G_\sigma$ and on the abelian generic locus. The equality $I\mathfrak c_I=I^\dagger$ proves tensor perfectness, while (8.17) proves symmetry and positivity. Since

$$
\operatorname{Lie}T_I\simeq I\otimes_{\mathbf Z}A_\sigma
$$

is locally free of rank one over $\mathcal O_F\otimes A_\sigma$, the universal determinant polynomial holds on the boundary formal chart. It is a closed identity and hence holds on the algebraization and its abelian locus.

The $N$-torsion of the one-motive $[I\xrightarrow{u_Q}T_I]$ fits into

$$
0\longrightarrow T_I[N]
\longrightarrow [I\to T_I][N]
\longrightarrow I/NI\longrightarrow0.
\tag{8.18}
$$

Here $T_I[N]=(I/NI)(1)$. Because the base contains every monomial $Q^{\xi/N}$ for $\xi\in\mathfrak M$, the rule

$$
x(u_Q(a/N))=Q^{ax/N}
$$

splits the quotient term in (8.18). Together with toric $N$-torsion it gives (1.1b), and the one-motive Weil pairing is (1.1c). Thus the determinant, PEL, and auxiliary-level data all extend on the same chart.

It remains to check dimension rather than merely count parameters. The cotangent space of a Hilbert--Blumenthal deformation is the rank-$d$ module of symmetric $\mathcal O_F$-balanced bilinear forms on the Hodge lattice. The logarithmic differentials of the period torus are

$$
d\log Q^\xi\qquad(\xi\in\mathfrak M),
$$

and (8.15) identifies the Kodaira--Spencer map with the identity on $\mathfrak M\otimes K$. It is therefore an isomorphism. The auxiliary level is etale and adds no tangent directions, so the classifying map is etale on the punctured polydisc.

Finally choose $q_N\in K$ with $v_K(q_N)>0$, put $q_0=q_N^N$, and specialize by

$$
Q^{\xi/N}\longmapsto q_N^{\operatorname{Tr}(\xi)}.
\tag{8.19}
$$

Then $Q^{ax}$ maps to $q_0^{\operatorname{Tr}(ax)}$, which is the period evaluation for $E_{q_0}\otimes I$. The ring in (8.14) is a domain, so $U_\sigma$ is connected. Its classifying map meets the open-and-closed component $H_I^{\mathrm{ten}}$ along this tensor specialization and therefore factors through that component everywhere. This proves the tensor-ray and component assertions and completes the construction. $\square$

The theorem also gives the correct multivariable finite-flat criterion. A $K$-point of the chart determines a valuation homomorphism

$$
\nu_Q:\mathfrak d_F^{-1}\longrightarrow\mathbf Z.
\tag{8.20}
$$

At an unramified odd coefficient prime $p$, the canonical $p$-torsion of its one-motive extends finite flat if and only if

$$
\nu_Q(\mathfrak d_F^{-1})\subset p\mathbf Z.
\tag{8.21}
$$

Indeed, pulling (8.18) back along $a\bmod p$ and evaluating by $x\bmod p$ gives the Kummer class $Q^{ax}$; it comes from a unit precisely when $p$ divides its valuation. After choosing bases, the resulting unit Kummer extensions assemble into a finite flat extension of the constant lattice by the toric $\mu_p$-lattice. The products $ax$ generate $II^\dagger=\mathfrak d_F^{-1}$, proving necessity and sufficiency. On the tensor ray, (8.20) is $v_K(q_0)\operatorname{Tr}$. The element $1\in\mathcal O_F$ is primitive as a $\mathbf Z$-lattice vector, so evaluation at $1$ maps $\operatorname{Hom}_{\mathbf Z}(\mathcal O_F,\mathbf Z)=\mathfrak d_F^{-1}$ onto $\mathbf Z$. Hence (8.21) is equivalent to $p\mid v_K(q_0)$, recovering (8.6).

### 8.6 Semistable neighborhoods

**Theorem 8.2 (full-dimensional semistable openness).** Let $y\in Y(K)$ be a tensor Tate point with corrected auxiliary level and both exact generic frames. Then there is a nonempty open neighborhood

$$
\Omega_y\subset Y(K)
\tag{8.22}
$$

all of whose underlying abelian varieties have split totally toric semistable reduction. The toric rank is $d$, equivalently one over $\mathcal O_F$. Any prescribed finite list of torsion Kummer classes and valuation shells can be retained. At an unramified odd coefficient prime, if (8.21) holds at $y$, the neighborhood may be chosen so that it holds throughout.

**Proof.** Use (8.19) to place $y$ on the algebraized chart. Because $\nu_{\mathrm{ten}}$ lies in the interior of $\sigma$, all regular boundary parameters $t_1,\ldots,t_d$ have positive valuation at $y$. Require

$$
v_K(t_i)=v_K(t_i(y))>0
\qquad(1\leq i\leq d).
\tag{8.23}
$$

These are open conditions. Every resulting point reduces to the same deepest boundary stratum, whose identity component is $T_I$; pulling back $\mathcal G_\sigma$ gives split semistable reduction of toric rank $d$. The etale Kodaira--Spencer calculation in Theorem 8.1 and the nonarchimedean inverse function theorem identify a small parameter polydisc around $y$ with an open subset of $H(K)$. Thus this is an ambient $d$-dimensional open, not the one-dimensional tensor ray.

The quotients $K^\times/(K^\times)^n$ are finite and their power subgroups are open, so finitely many Kummer classes remain fixed after shrinking. Conditions (8.23) fix the homomorphism (8.20), hence preserve (8.21). Finally intersect with the local images of the two finite etale generic frame schemes. The intersection contains $y$, so it is nonempty and gives (8.22). $\square$

## 9. Twisted two-prime covers and local solvability

### 9.1 What a point of the twist says

A $K$-point of the two-prime twist is a tuple

$$
(A,\iota,\lambda,\eta_{\mathfrak n}^{\natural},
\alpha_{\mathfrak p},\alpha_{\mathfrak q})
\tag{9.1}
$$

with the isomorphisms (1.1d)--(1.1e). It realizes the prescribed representations exactly, including extension classes and pairings. There is no weakening to semisimplification.

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

At a real place, Theorem 4.1 supplies the corrected auxiliary level and Proposition 4.2 solves the two residual frames. At a good finite place away from $p$ and $q$, local solvability is a simultaneous Frobenius realization problem. At a coefficient prime, it is an exact finite-flat PEL realization problem. At a semistable place, Theorems 8.1--8.2 supply the ambient chart in addition to the Kummer extension class.

### 9.3 Good-prime solvability

Let $r\ne p,q$ be good for all integral data. The finite etale twist extends as in (5.1).

**Theorem 9.1 (good-prime local point).** Assume $r\ne p,q$ is good for $F$, $I$, and $N$, and the restrictions of both prescribed systems to $G_K$ are unramified. Then after a finite unramified extension $K'/K$, the intended twist has a good point. It has a nonempty open residue neighborhood on which good reduction, corrected auxiliary level, component, and both exact frames persist.

**Proof.** Choose any smooth elliptic curve over a finite extension of $k$. After a further finite residue extension choose its corrected elliptic $N$-level (3.11), and tensor both curve and level with $I$. Proposition 3.2 puts the resulting good PEL object on the intended component. The two seed torsion representations and the two prescribed unramified representations have finite image. After replacing arithmetic Frobenius by a common positive power, all four actions and their determinant lines are trivial. Paired bases then give both frames on the same special-fiber seed. Theorem 5.1 lifts that point over the corresponding unramified extension, and its residue tube gives the asserted neighborhood. $\square$

If ramification of a prescribed prime-to-$r$ system is allowed initially, pass first to the recorded finite completion extension killing that inertia. The theorem then applies over its maximal unramified stage; no descent to the original field is asserted.

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

Finite flatness of $V_{\mathfrak p}$ alone is intentionally not asserted to give assertion 1 over the original field or over an unramified extension. Assertion 2 works because the tensor PEL seed has been constructed independently on the intended component and a general finite splitting extension is allowed. On an externally fixed component for which no seed is known, the PEL realization problem remains genuine.

### 9.5 Simultaneous frames

The two frame conditions must be solved on the same abelian variety. Separate local existence for $V_{\mathfrak p}$ and $V_{\mathfrak q}$ does not suffice. The product twist encodes this simultaneity.

Once one simultaneous point exists, however, openness is straightforward. Each generic frame cover is finite etale over $K$, so each has an open local image. Their intersection contains the point and is therefore nonempty. Reduction, ordinary, nonordinary, or semistable conditions can then be intersected with it, provided the same seed point witnesses all of them.

This order prevents a common circular argument. We do not prove the intersection nonempty by observing that all its factors are individually nonempty. We first construct one tuple (9.1), then shrink around it.

The finite-splitting argument also applies to a semistable seed. Choose $q_0=q_N^N$ so the corrected auxiliary level is already present on the boundary chart. Since $N$ is prime to $p$ and $q$, raising to the $N$th power is an automorphism of every relevant residual Kummer quotient; this restriction loses no prescribed compatible pair of $p$- and $q$-Kummer classes. Pass to a finite extension splitting both prescribed local systems and both seed torsion modules. Symplectic bases give simultaneous frames. Theorem 8.2 then gives an ambient semistable neighborhood. If $V_{\mathfrak p}$ was finite flat, its restriction remains finite flat. If the seed's own one-motive $p$-torsion is required to be finite flat over the unramified starting field, impose (8.21) before extending. Exact valuations rescale by $e(L/K)$, so only divisibility and semistability, not the original normalized exponents, are claimed to persist.

### 9.6 Base-field points at sufficiently large good places

The finite-extension clauses above are essential at a fixed small place.  They do not imply
that base-field points are scarce at all good places.  For a fixed geometrically connected
twist, a curve and the Hasse--Weil bound give a uniform large-residue-field statement which is
useful for constant-field certificates.

**Proposition 9.3 (large-good-place base-field solvability).**  Let $K_0$ be a number field and
let $U/K_0$ be a smooth geometrically connected quasi-projective variety of positive dimension.
There are a finite set $S_U$ of finite places and a constant $Q_U$ such that

$$
U(K_{0,v})\ne\varnothing
\qquad
(v\notin S_U,\ |k_v|>Q_U).
\tag{9.4}
$$

Every such point has a nonempty full-dimensional analytic neighborhood.  The assertion applies
in particular to the complement of a proper closed subset of an elliptic-source or
cyclotomic-split determinant-compatible two-prime twist.

**Proof.**  The empty-local-set case of Book 154, Lemma 5.2 slices out a geometrically integral
curve $C\subset U$.  Let $\overline C$ be its smooth projective normalization, let $g$ be its
genus, and let $b$ be the number of geometric points in
$\overline C\setminus C$.  Spread $\overline C$, its open $C$, and the map to $U$ over the
integers outside a finite set.  After enlarging that set, every special fiber of
$\overline C$ is smooth and geometrically connected and the boundary has at most $b$ geometric
points.  The Hasse--Weil bound of Book 37 gives

$$
\#\overline C(k_v)\geq |k_v|+1-2g|k_v|^{1/2}.
$$

For $|k_v|$ larger than a constant depending only on $g$ and $b$, the right side exceeds $b$.
There is therefore a $k_v$-point of $C$.  It is a smooth point of the spread-out model, so
Theorem 2.2 lifts it to an $\mathcal O_{K_{0,v}}$-point and hence to a point of $U(K_{0,v})$.
Proposition 2.1 supplies the analytic neighborhood.  Replacing $U$ at the outset by the
complement of a proper closed subset proves the last assertion. $\square$

This proposition is deliberately asymmetrical.  It permits certificate primes to be selected
after a fixed twist has been constructed, because Chebotarev classes contain arbitrarily large
good primes.  It says nothing about the small prescribed places $2$, $p$, or $q$; at those
places an exact base-completion point remains a separate realization problem.

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

Because there are finitely many $\tau$, (10.1) is open. Its inverse image under reduction is therefore open in $H(K)$. The tensor ordinary points of Chapter 6 show that it is nonempty on the intended component.

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

For a Tate curve, $v(j)<0$ is stable under small perturbation of $j$ because valuation is locally constant on $K^\times$. On the tensor Tate locus the same condition is read in each elliptic factor. On the Mumford chart of Theorem 8.1, conditions

$$
v_K(t_i)=m_i>0
\tag{10.4}
$$

are open shells. Keeping the remaining parameters and determinant functions units preserves the toric rank and polarization type. The numbers $m_i$ determine the valuation homomorphism $\nu_Q$ in (8.20), but the invariant finite-flat condition is not the basis-dependent assertion that each displayed $m_i$ is divisible by $p$. It is

$$
\nu_Q(\mathfrak d_F^{-1})\subset p\mathbf Z.
\tag{10.5}
$$

Because (10.4) fixes $\nu_Q$, condition (10.5) persists on the whole shell. On the tensor ray it reduces to $p\mid v_K(q_0)$ by trace duality. If an exact Kummer class must also be preserved, valuation is not enough. Each character evaluation gives a class in the finite group

$$
K^\times/(K^\times)^p.
$$

For a $p$-adic local field this quotient is finite, and the $p$th-power subgroup is open. To see openness directly, write

$$
K^\times=\pi^{\mathbf Z}\times\mu_{|k|-1}\times U^1.
$$

On a sufficiently deep principal-unit group $U^n$, the $p$-adic logarithm identifies the $p$th-power map with multiplication by $p$, whose image contains another open subgroup. Hence every Kummer class is open. A sufficiently small neighborhood therefore preserves both the valuation homomorphism and any prescribed finite list of evaluated Kummer classes.

For a prime $\ell\ne p$, the same conclusion is easier: raising to the $\ell$th power is an automorphism on a sufficiently deep principal-unit group. Thus $K^\times/(K^\times)^\ell$ is finite and discrete, and the Tate extension class is locally constant.

### 10.5 Frame conditions are locally constant

Let $t_0\in H(K)$ and fix a paired identification between a prescribed $V_{\mathfrak r}$ and $\mathcal A[\mathfrak r]_{t_0}$. The paired isomorphism scheme is finite etale over $H_K$. Proposition 2.3 gives a neighborhood of the chosen point of that scheme mapping homeomorphically to an open neighborhood of $t_0$. Thus every fiber in that neighborhood has the prescribed paired isomorphism. Applying this construction to both primes and intersecting the two images proves simultaneous local constancy without invoking a topological covering space for an arbitrary analytic subset.

**Theorem 10.2 (openness theorem).** Let $y\in Y(K)$ be a local point of one of the following kinds:

- real on a fixed real component;
- good away from the level primes;
- good ordinary at an unramified odd coefficient prime;
- good nonordinary finite-flat at such a prime;
- a split totally toric tensor-cusp point, with any stated Tate Kummer classes.

Then there is a nonempty open neighborhood $\Omega_y\subset Y(K)$ on which the same listed local condition, both exact paired frames, the polarization type, the auxiliary level, and the geometric component all persist. At an odd unramified coefficient prime, the neighborhood also preserves canonical finite flatness whenever (10.5) holds at $y$.

**Proof.** At a real place use Section 4.5. At a good point use an integral residue tube and, for ordinarity, intersect with (10.1). For nonordinary type fix the special point as in (10.3). At a tensor-cusp point Theorem 8.2 supplies the full-dimensional semistable neighborhood; Section 10.4 retains the requested Kummer classes and (10.5). The frames and auxiliary level are universal on $Y$; if one works downstairs on $H$, intersect with their finite etale local images. A sufficiently small neighborhood cannot cross an open-and-closed component. Every intersection contains $y$, so it is nonempty. $\square$

## 11. Persistence under extension of local fields

### 11.1 Integral and good reduction

Let $L/K$ be a finite extension, with valuation rings $S/R$. If $A/R$ is an abelian scheme, then

$$
A_S=A\times_RS
$$

is an abelian scheme. The real multiplication, polarization-module isomorphism, determinant condition, and prime-to-residue-characteristic level all commute with base change. Hence good reduction persists under every finite extension.

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

On a Mumford chart, base change multiplies the valuation homomorphism by the ramification index:

$$
\nu_{Q,L}=e(L/K)\nu_{Q,K}.
\tag{11.2}
$$

Consequently $\nu_{Q,K}(\mathfrak d_F^{-1})\subset p\mathbf Z$ implies the same inclusion over $L$, so the canonical finite-flat one-motive torsion of (8.21) persists. On the tensor ray this says that if $p\mid v_K(q_0)$, then

$$
p\mid v_L(q_0)=e(L/K)v_K(q_0),
$$

as expected. The converse after restriction fails: a ramification index divisible by $p$ can force (8.21) over $L$ even when it fails over $K$. Finite flatness acquired after ramified extension need not descend.

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

For two frames, the seed must already lie on the fiber product twist. For finite flatness and semistability at the same coefficient prime, the Mumford seed must satisfy (8.21) before shrinking; on the tensor ray this is (8.6). For a nonordinary good point, one uses a supersingular seed, not an ordinary point plus a separate closed condition.

### 12.2 Component bookkeeping

The geometric components of an arbitrary Hilbert moduli space are indexed by determinant classes in a narrow adelic quotient. A twist does not alter them after algebraic closure, but Galois may permute them. This warning is the reason the component was fixed before any local construction.

For the corrected datum, the bookkeeping has already been completed. Proposition 3.2 proves that $H_I^{\mathrm{ten}}$ is defined over $\mathbf Q$, that every tensor seed with corrected level lies on it, and that the determinant-compatible two-prime twist $Y_I^{\mathrm{ten}}$ is geometrically connected. Passing to a completion or to a finite extension does not change that algebraic component. Once simultaneous frames have been chosen, the seed is therefore a point of this one $K$-defined twist, not merely a point somewhere on a union of conjugate components.

Theorem 3.3 makes this uniform for the potential-automorphy catalog: choose $I=\mathcal O_F$ and $\mathfrak c=\mathfrak d_F^{-1}$ before declaring the auxiliary PEL datum. Real, good, ordinary, supersingular, and tensor-cusp seeds then all have the same determinant class. There is no component intersection left to prove downstream.

If a different application externally fixes a nonsquare narrow class of $\mathfrak d_F\mathfrak c$, this reduction is unavailable. It must supply its own common seeds and component descent; a prime-to-level isogeny does not automatically transport the ordered polarization-module identification.

### 12.3 Avoiding degeneracy loci

Applications often remove a proper closed subset $Z\subset Y$: loci with extra endomorphisms, reducible auxiliary torsion, vanishing coordinates, or unwanted automorphisms. If the chosen seed lies outside $Z$, then

$$
Y(K)\setminus Z(K)
$$

is open near it because $Z(K)$ is closed for a separated finite-type scheme over a local field. Intersecting with this complement preserves nonemptiness.

If the seed lies in $Z$, no amount of shrinking removes it while retaining the seed. One must choose a different point. Smooth positive-dimensional residue tubes help: in etale coordinates, a proper closed subset has empty interior unless it contains an entire local irreducible component. When necessary, pass to a finite residue extension so that a point of the tube avoids the reduction of $Z$.

The last assertion has a direct algebraic proof. A nonzero polynomial on an affine ball cannot vanish at every point over all finite extensions of a finite residue field. Reduce its first nonzero coefficient modulo a suitable power of $\pi$ and choose residue coordinates outside its zero set after a finite extension. Hensel lifting gives the desired point.

### 12.4 A simultaneous local-neighborhood theorem

**Theorem 12.1 (simultaneous local neighborhood).** Let $K$ be $\mathbf R$ or a finite extension of $\mathbf Q_r$, let $Y=Y_I^{\mathrm{ten}}$ be the corrected determinant-compatible twist, and let $Z\subsetneq Y$ be closed. Suppose there is a point

$$
y\in(Y\setminus Z)(K)
$$

which is real, good, good ordinary, good nonordinary finite-flat, or a split totally toric tensor-cusp point. Then there is a nonempty open

$$
\Omega_y\subset(Y\setminus Z)(K)
\tag{12.1}
$$

such that:

1. every point has the same two prescribed paired torsion representations;
2. every point retains the auxiliary level, ordered polarization type, and component;
3. every point has the same selected real, good, ordinary, nonordinary finite-flat, or semistable condition;
4. any finitely many locally constant valuation, Kummer, splitness, or reduction constraints satisfied by $y$ also persist after shrinking; at an odd unramified coefficient prime this includes (8.21).

**Proof.** Theorem 10.2 gives an open neighborhood for the principal local condition and frames; in the semistable case its chart is the constructed chart of Theorems 8.1--8.2. Proposition 3.2 makes the intended geometrically connected twist the ambient space. The complement of $Z(K)$ is open and contains $y$. Each additional locally constant invariant supplies an open neighborhood by Sections 10.4--10.5. Intersect the finitely many neighborhoods. Their intersection is open and contains $y$, proving nonemptiness. $\square$

The theorem is intentionally point-centered. It does not assert that arbitrary separately specified local conditions have a common point.

## 13. The Moret--Bailly local package

### 13.1 The input ledger

Before local neighborhoods can be passed to arithmetic approximation, the following facts must be recorded at every controlled place. The corrected level, the ambient tensor-cusp chart, and membership in the tensor component are now constructions, not entries to be assumed.

| place | seed point | condition retained | essential compatibility |
|---|---|---|---|
| real | $E/\mathbf R\otimes I$ with (4.2b) | real component and signs | both prescribed involutions are odd |
| $r\ne p,q$ | good tensor point after a recorded inertia-killing extension and a finite unramified stage | good reduction | both prescribed systems are then unramified |
| $r=p$ or $q$, ordinary | ordinary tensor lift | ordinary finite-flat type | finite-flat $V_{\mathfrak r}$ and the permitted frame field |
| $r=p$ or $q$, nonordinary | supersingular tensor lift | fixed local--local finite-flat reduction | finite-flat $V_{\mathfrak r}$ and the permitted frame field |
| semistable | $q_0=q_N^N$ on the algebraized tensor cusp | toric rank, splitness, Kummer classes, (8.21) when required | any Kummer classes retained before extension come from one tensor Tate parameter |

Proposition 3.2 puts every row on the same $\mathbf Q$-defined component and makes its two-prime twist geometrically connected. At every real place a row is required if the output field is to be totally real. At finite places every enlargement used to obtain the frames is recorded in the completion algebra. Away from $p$ and $q$, after any recorded inertia-killing extension, the remaining enlargement can be taken unramified by Theorem 9.1. At a coefficient prime an arbitrary determinant-compatible finite representation becomes framed after a finite splitting extension by Theorem 9.2; if a downstream lifting theorem permits only an unramified extension, exact realization over such an extension is a representation-theoretic input and cannot be replaced by ramified splitting.

### 13.2 The local construction theorem

**Theorem 13.1 (local geometry package for Hilbert--Blumenthal specialization).** Fix the corrected tensor datum of Section 1.2, take monodromy-admissible odd primes $\mathfrak p$ and $\mathfrak q$, and let

$$
Y=Y_I^{\mathrm{ten}}
$$

be its determinant-compatible two-prime twist. Let $S$ be a finite set of places of a totally real number field $K_0$. At every integral place assume the exclusions stated in Section 1.2; at a coefficient prime assume the unramified odd-prime hypotheses of Chapters 6--8.

Choose at each $v\in S$ one of the five rows in Section 13.1. Require only the corresponding representation-theoretic compatibility:

1. at a real place both prescribed residual systems are odd;
2. at a good place away from $p$ and $q$ both are unramified, or an explicitly permitted finite preliminary extension kills their inertia;
3. at an ordinary or nonordinary coefficient place the prescribed residue-characteristic system is finite flat, and either arbitrary finite splitting is allowed or the exact frame is known over the more restrictive permitted completion extension;
4. at a semistable place, any nontrivial residual Kummer classes that must be retained over the chosen completion are the scalar extensions of one class $[q_0]$; if arbitrary finite splitting is allowed, no further frame hypothesis is needed. When semistable coefficient-prime torsion must already be finite flat over the unramified starting field, impose (8.21); finite flatness acquired only after a ramified splitting extension is not asserted to descend.

Then there are finite local extensions $K_v'/K_{0,v}$ obeying those permissions and nonempty open subsets

$$
\Omega_v\subset Y(K_v')
\tag{13.1}
$$

such that every point in $\Omega_v$ has the required exact local condition, both prescribed paired torsion representations, the fixed ordered polarization and auxiliary level, and the selected component. These properties persist after any further finite extension in the following sense:

- good reduction, ordinarity, local--local type, semistability, toric rank, and finite flatness persist;
- split multiplicative reduction persists, while nonsplit reduction is allowed to become split;
- exact frames restrict to the larger local Galois group;
- normalized valuations rescale by the ramification index, and no stronger invariance is asserted.

If $Z\subsetneq Y$ is a proper closed degeneracy locus, the neighborhoods may be chosen in $Y(K_v')\setminus Z(K_v')$, after enlarging a finite residue field when necessary.

**Proof.** Theorem 4.1 constructs the corrected auxiliary level on the real tensor point, Proposition 4.2 gives both frames exactly from oddness, and Section 4.5 gives the real open. At a good prime away from $p$ and $q$, first make any recorded inertia-killing extension and then apply Theorem 9.1 over that field; the remaining enlargement is unramified and produces a simultaneous point with its good residue neighborhood.

Chapters 6 and 7 construct ordinary and supersingular tensor PEL seeds. If the exact frames are not already available over a restricted permitted field, take the finite compositum splitting both prescribed systems, both seed torsion modules, their determinant targets, and the corrected auxiliary level. Paired symplectic bases then give simultaneous frames. Restriction preserves the given finite-flat model, while Proposition 11.1 preserves the seed's ordinary or local--local reduction. Theorem 9.2 and the relevant residue tube give the desired open.

For the semistable row, the $N$th-power map is invertible on both residual Kummer quotients because $N$ is prime to $p$ and $q$. If nontrivial classes are to be retained, choose a simultaneous preimage class $[q_N]$ of the compatible prescribed tensor Tate classes, and multiply a representative by a sufficiently large $(pq)$th power of a uniformizer so that it has positive valuation without changing either residual class. If the frames will instead be split, choose any $q_N$ of positive valuation. Put $q_0=q_N^N$. Theorem 8.1 places $E_{q_0}\otimes I$ on the algebraized full-dimensional tensor cusp with its corrected level. Take the permitted simultaneous frame field as in Section 9.5. If arbitrary splitting is used at a coefficient prime, enlarge it to contain the needed $p$th division periods; the canonical sequence then splits into finite flat constant and multiplicative pieces over the enlarged valuation ring, and its valuation homomorphism is automatically $p$-divisible. Theorem 8.2 supplies the ambient semistable open and retains all stated Kummer classes and valuation shells.

Proposition 3.2 puts every construction on the same geometrically connected $K_0$-defined twist. Theorem 12.1 intersects the exact frame and reduction neighborhoods. Since $Y$ is smooth of positive dimension, a proper closed subset has empty interior in each analytic neighborhood; Section 12.3 permits a point outside $Z$ after a finite residue extension and another application of Theorem 12.1. Chapter 11 proves the persistence statements. $\square$

The restriction on semistable Kummer classes is exact. Two arbitrary triangular residual systems need not be scalar extensions of the same Tate parameter, and no Hilbert moduli argument can make them so. Likewise, an unramified-only coefficient-prime policy cannot use a ramified splitting field. These are prescribed-representation constraints, not missing real-level, component, or compactification geometry.

**Corollary 13.2 (potential-automorphy catalog interface).** In every catalog problem in which the polarization ideal, PEL lattice, neat level, and Hilbert component are auxiliary, take the datum (3.13) and the corrected level (1.1b). Then the moduli variety supplied to arithmetic approximation is smooth and geometrically connected, and Theorem 13.1 supplies its five required kinds of nonempty local opens. Thus the catalog's local-seed clause is discharged in the stated unramified odd-prime and tensor-Tate ranges once its exact representation compatibility and completion-extension policy have been checked; no separate hypothesis of real auxiliary descent, a toroidal chart, or seed existence on a chosen polarization component remains.

**Proof.** Theorem 3.3 makes the catalog reduction without changing either residual system or
any desired local conclusion. Proposition 3.2 gives smooth geometric connectedness of the
determinant-compatible twist, and Theorem 13.1 gives the asserted nonempty local opens on it.
These discharge the local-seed clause.  To apply Book 154 with an exact completion algebra one
must additionally supply the common moving presentation required there; the opens alone do not
prove its degree and Abel-class compatibility. $\square$

In particular, the separate good residue tubes and full-dimensional semistable boundary chart
do not construct one smooth proper integral slice through the special packet whose special
fiber contains a dense open of allowed good points.  Such a slice would invoke Book 154, Lemma
5.2D's integral-open saturation, while a coset-complete finite family of good divisors would
invoke Lemma 5.2B.  Neither geometric assertion follows from Theorem 13.1's point-centered
neighborhoods.

### 13.2A The stable integral connecting-slice boundary

We isolate the exact first theorem missing from the integral-slice route.  This is more than
the existence of one curve over the local field.  Book 154 first approximates the local cutting
sections by one global tuple.  The integral property must therefore hold on a congruence
neighborhood of the local tuple, so that it survives that approximation.

Let $v$ be a finite place of the global base field and let $k$ be its completion.  Assume that
$v$ satisfies all the good-model exclusions of Section 5.1, in particular that it lies away
from the two coefficient primes and every auxiliary level prime.  Let $R$ be the valuation ring
of $k$ and $\kappa$ its residue field.  Suppose the two prescribed frame systems
are unramified over $k$ and have the determinant-compatible trivializations used at the special
place.  The good Hilbert--Blumenthal problem and its paired frame twist then have the smooth
integral model of Section 5.1,

$$
\mathcal Y^{\mathrm{good}}/R
$$

on the interior.  Fix a split semistable point in the tensor-cusp chart,

$$
y_{\mathrm{sp}}\in (Y\setminus Z)(k)
$$

with its exact frames, enhanced line, sign, and a point-centered special neighborhood
$V_{\mathrm{sp}}\subset (Y\setminus Z)(k)$.  Also fix a good integral point
$y_{\mathrm{good}}\in(Y\setminus Z)(k)$
on the same framed component.

Call the following assertion $(\mathrm{ICS})_{v,Z}$, the **stable integral connecting-slice
assertion**.

1. The projective closure and very ample bundle chosen in Book 154, Step 1 have a
   finite-presentation $R$-model $\overline{\mathcal Y}$ and a relatively very ample extension,
   with $\mathcal Y^{\mathrm{good}}$ contained as an open.  There is a tuple of relative
   cutting sections drawn from the scalar extension of that same finite-dimensional global
   coefficient space.  Their intersection is a smooth proper geometrically connected relative
   curve
   $$
   \mathcal C/R.
   $$
2. A dense open $C^\circ\subset \mathcal C_k$ of the generic fiber maps to $Y\setminus Z$.
   It contains distinct $k$-points $T$ and $P$, with $T$ mapping into $V_{\mathrm{sp}}$ and
   $P$ mapping into a good integral neighborhood of $y_{\mathrm{good}}$.  The map is an
   immersion near both points.  The closure of $T$ is allowed to meet the boundary of
   $\overline{\mathcal Y}$ on the special fiber; this is how the semistable condition is
   retained.
3. There is a nonempty (hence dense) Zariski-open
   $$
   W\subset \mathcal C_\kappa
   $$
   on which the map factors through $\mathcal Y^{\mathrm{good}}_\kappa$ and avoids the closure
   of $Z$, and it contains the specialization of $P$.  It is disjoint from the specializations
   of the finite set $\mathcal C_k\setminus C^\circ$.  Thus every closed point of
   $\mathcal C_k$ whose closure has special fiber contained in $W$ belongs to $C^\circ$ and
   carries good minimal reduction, the same two paired frames, the chosen auxiliary level, and
   the same arithmetic component.

These clauses have the stability needed in Book 154; this is why clause 1 includes the global
coefficient space.  The tuple defines an $R$-point of a finite-type coefficient parameter.
Book 8, Sections 13.2--13.3 make the smooth geometrically connected curve locus open there.
After restricting to one sufficiently small congruence class, the reductions of all cutting
sections are unchanged, so the special-fiber curve and $W$ are unchanged.  Book 154, Step 1's
full-rank Jacobian argument continues the marked points $T$ and $P$ under a small change of the
tuple, and their images remain in their point-centered neighborhoods.  Consequently clauses
1--3 persist on a nonempty congruence neighborhood, and the global cutting tuple selected by
weak approximation may be required to have a smooth integral model with the same special-fiber
curve and good open.

A curve defined only over $k$ would not suffice: it need not be represented in the global
coefficient space and hence need not survive Book 154's approximation.  The finite-type
integral presentation in clause 1 is what proves, rather than merely assumes, stability.  The
formal cusp chart by itself is not such a presentation.

**Proposition 13.2A (conditional closure of the singleton moving input).**  Consider a
simultaneous approximation problem on $Y\setminus Z$ with one special place $v_0$.  Suppose
$(\mathrm{ICS})_{v_0,Z}$ holds there, every other exact packet may be repeated wholesale, and
every remaining split packet is flexible in the sense of Book 154, Lemma 5.2.  Assume also
that any requested equivariant normal-closure local behavior is realized by the chosen local
parameters.  Then those packets admit one simultaneous moving-family presentation.  Its fiber
at $v_0$ has exactly one
degree-one factor in $V_{\mathrm{sp}}$, every other factor is good minimal, all paired frames
and component labels and all assigned equivariant normal-closure local fibers are retained, and
every flexible split packet, including a certificate packet, remains split with all sheets in
its assigned open.  The common degree satisfies any prescribed finite divisibility condition
(in particular compatible required evenness), and the evaluation avoids $Z$.

**Proof.**  In Book 154, Step 1, impose the congruence neighborhood just constructed at $v_0$
while approximating the cutting sections at all other places.  After base change to $k$, the
resulting global curve has a nearby smooth proper model, good open, and marked points satisfying
clauses 1--3; relabel them $\mathcal C,W,T,P$.  Apply Book 154, Lemma 5.2D on this actual slice.
For every sufficiently large degree,
every Jacobian class is then represented by a reduced divisor, disjoint from the marked special
point, all of whose residue-field factors have closure in $W$.  Clause 3 puts every such factor
in $C^\circ$ and makes it an allowed good minimal point of the same framed twist.  Hence, for
the pencil bundle $\mathcal A$ and every sufficiently large $n$,

$$
n([\mathcal A]-e[P])-[T-P]
\in \mathscr R^{\mathrm{good}}_{v_0,ne-1}.
$$

This is Book 154, (5.4g), and implies its full varying-special condition (5.4g').  The special
point occurs once, while reducedness and disjointness keep it from reappearing in the good
divisor.

Book 154, Lemma 5.2A puts every wholesale-repeatable packet in a sufficiently large arithmetic
progression of exponents.  The remaining split packets are flexible instances of Lemma 5.2.
Choose the global ample bundle as in Book 154, Lemma 5.2A, with degree divisible by every
wholesale packet degree and by any prescribed finite divisor (in particular by $2$ when an even
common degree is required).  Since the integral slice makes every sufficiently large exponent
available at $v_0$, choose one exponent in the common progression and apply Corollary 5.2E.
Weak approximation of the two pencil sections retains all factorwise neighborhoods;
on the resulting fixed presentation, Book 155, Proposition 5.2 supplies parameter
neighborhoods retaining its assumed equivariant normal-closure fibers (and hence all quotient
finite etale algebras), while the evaluation neighborhoods retain the frames and component
labels.  As in Book 154, Step 3, remove the branch values and the images
of the finite global complement of the curve open mapping to $Y\setminus Z$.  The resulting
evaluation family lies in $Y\setminus Z$; clause 3 ensures that the selected $v_0$-fiber is
disjoint from that complement and that every selected good factor lies in $C^\circ$.  This
gives the asserted common presentation. $\square$

Thus $(\mathrm{ICS})_{v_0,Z}$ discharges the one-special/all-other-good moving input, with no
remaining Picard congruence, in any later application satisfying the other hypotheses of the
proposition.  The presently established sources do not prove $(\mathrm{ICS})_{v_0,Z}$.  The
first absent reusable input in this route is a theorem identifying a finite-type projective
model with the required cusp germ and good interior and producing the stable relative slice
with the three clauses above.

Here is the source audit.

- Theorem 8.1 constructs the Mumford family over the completed boundary algebra
  $R'[[t_1,\ldots,t_d]]$ and Theorem 8.2 constructs a point-centered valuation shell.  They do
  not identify that completed chart with the boundary completion of one projective
  finite-presentation $R$-model containing $\mathcal Y^{\mathrm{good}}$, or algebraize a curve
  crossing from its boundary point into a special-fiber open of the good interior.  Indeed every
  point in the prescribed shell has
  $v(t_i)>0$ for all $i$ and therefore reduces to the deepest boundary stratum; shrinking that
  shell cannot produce the inverse image of a good special-fiber open.
- Book 8 represents fixed-polynomial curve families by a Hilbert scheme.  Representability
  supplies a parameter space and its universal family; it does not prove that the open locus
  expressing clauses 1--3 has an $R$-point.  In particular an open in a parameter space over
  the finite field $\kappa$ need not have a $\kappa$-point merely because it is geometrically
  nonempty.  A bare projective closure of the already quasi-projective integral model is also
  standard; it supplies neither compatibility with the completed cusp chart nor the required
  smooth crossing slice.
- Book 153's Bertini argument is over an infinite characteristic-zero field and controls the
  generic curve.  It contains no relative Bertini theorem over a DVR with finite residue field,
  prescribed boundary section, smooth special fiber, and incidence with the good interior.
  Books 9 and 10 respectively control divisors on an already supplied relative curve and the
  descent of already supplied projective data; neither is an existence theorem for this slice.
- Proposition 4.1A puts the unperturbed tensor seeds on one twisted modular curve.  Even if its
  standard good integral compactification is used as the initial slice, it is not an avoidance
  repair in the higher-dimensional Hilbert case: the prescribed proper closed set $Z$ is
  allowed to contain the entire tensor locus.  A theorem that Hecke translates or deformations
  of that curve meet all the prescribed point-centered neighborhoods while escaping $Z$ is not
  among the audited sources.

The relative symmetric powers used in the Abel argument start only after the curve has been
produced.  The finite-length Hilbert or configuration space of $Y$ does carry a universal
incidence family without choosing a curve, but Book 8 does not make that parameter space an
open of affine space or prove weak approximation on it.  Producing a rational affine subfamily
with geometrically integral incidence that meets all the prescribed local configurations is
exactly the alternative common moving presentation still being sought.  Book 154's
Moret--Bailly theorem consumes such a presentation; applying it to the Hilbert or configuration
space merely repeats the same problem and is circular.

### 13.3 Passing from neighborhoods to every conjugate

An arithmetic approximation theorem uses (13.1) in one of two ways. If a place is required to split completely, the local algebra is a product of copies of $K_{0,v}$ and every conjugate point is required to lie in $\Omega_v$. If a prescribed field extension $K_v'/K_{0,v}$ is part of the seed, the local algebra must contain that factor and the point is evaluated in $Y(K_v')$.

These are different inputs. Constructing a point after an unramified extension does not prove that the original local field has a point. Nor does one chosen embedding control all conjugates. The global local-algebra datum must place every factor in the desired neighborhood.

Persistence makes this usable. Suppose a specialized global point is locally an extension of a seed in $\Omega_v$. Good, ordinary, nonordinary, semistable, and finite-flat properties survive restriction to that extension by Chapter 11. When exact valuation or nonsplitness matters, the completion data must also control ramification index or residue field, since those invariants can change.

At real places a split algebra $\mathbf R^n$ ensures that every embedding remains real and every conjugate point belongs to the chosen real open. A single real point without a split real local condition is not enough to force total reality.

### 13.4 Failure modes

The local package fails in recognizable ways.

**Wrong determinant.** If (9.2) is absent, the paired twist is empty even if the unpaired representations are isomorphic.

**Reverting to the literal Book 156 orientation.** Its constant value line cannot be identified over $\mathbf R$ with its cyclotomic twist. The corrected source (1.1b) is essential; using the obsolete orientation would make the real row empty again.

**Wrong external component.** Theorem 3.3 covers the catalog because its PEL data are auxiliary. An application that externally fixes a nonsquare narrow polarization class cannot substitute a tensor seed from $Y_I^{\mathrm{ten}}$.

**An extension policy too small for the frame.** A finite-flat $V_{\mathfrak p}$ need not equal the torsion of a fixed seed over the original or an unramified local field. A general finite splitting extension solves the frame problem, but a downstream theorem that forbids it must verify exact realization over its permitted field.

**Separate frames.** Realizing $V_{\mathfrak p}$ and $V_{\mathfrak q}$ on different abelian varieties does not give a point of the fiber-product twist.

**Closed is not open.** Nonordinarity is imposed by a residue tube around a seed, not by calling its special-fiber closed locus open.

**Generic is not integral.** A basis of characteristic-zero torsion does not determine a finite flat special-fiber group scheme.

**Semistable is not good.** Tate $p$-torsion can be finite flat while the Tate curve remains multiplicative.

**Discarding the ambient chart.** The tensor Tate ray has one parameter and by itself is not open when $d>1$. Theorems 8.1--8.2 repair this by placing it in an algebraized $d$-parameter Mumford chart; a bare Tate point cannot replace those theorems in another component.

**Unramified is not arbitrary.** Local solvability after an unramified extension must be encoded in the global completion algebra; it cannot be silently descended.

**Persistence is not constancy.** Semistability persists under ramification, but discriminant valuation and component counts rescale.

Each failure identifies a concrete repair: use the corrected level, change the determinant datum, invoke the exact catalog reduction or supply the externally fixed component, solve the two frames simultaneously over an allowed field, pass to a residue tube, retain an integral model, or use the algebraized Mumford chart.

## 14. Conclusion

### 14.1 The local dictionary

The five local conditions are controlled by five different pieces of geometry:

$$
\begin{array}{c|c}
\text{condition}&\text{controlling datum}\\ \hline
\text{real}&\text{cyclotomic-split auxiliary level and odd involution},\\
\text{good}&\text{smooth integral moduli point},\\
\text{ordinary}&\text{nonvanishing partial Hasse invariants},\\
\text{nonordinary finite flat}&\text{fixed local--local special point plus generic frame},\\
\text{semistable}&\text{algebraized Mumford chart, valuation homomorphism, and Kummer classes}.
\end{array}
\tag{14.1}
$$

The controlling data in the first and fifth rows were constructed in Theorems 4.1 and 8.1 rather than assumed. The required topology is obtained correspondingly from a real component, an integral residue tube, an ordinary open tube, a fixed nonordinary residue disk, or a semistable valuation shell in the boundary chart. Paired torsion frames are then preserved by finite etale local sections on the characteristic-zero generic fiber.

### 14.2 The package established and its boundaries

We constructed explicit local points by tensoring elliptic curves with invertible $\mathcal O_F$-ideals. Trace duality computed their polarization module as

$$
\mathfrak c_I=\mathfrak d_F^{-1}I^{-2},
$$

proved the Hilbert determinant condition, and recovered the correct inverse-different coefficient line in torsion pairings. Replacing the impossible constant orientation by

$$
(I/NI)\oplus(I/NI)(1)
$$

made the principal level compatible with complex conjugation while leaving its geometric paired-level scheme and product monodromy unchanged. The real tensor point therefore carries the auxiliary level and both odd residual frames over $\mathbf R$.

When prescribed finite-place tensor seeds must remain over their base completions, Proposition
4.1A permits the neat source to be $E_*[N]\otimes I/NI$ instead.  Lemma 4.1B chooses one
$E_*/K_0$ whose $N$-torsion matches finitely many such seeds.  This changes only arithmetic
descent of the auxiliary level: the geometric component and two-prime monodromy are unchanged.

The tensor polarization restriction was resolved exactly rather than ignored. Proposition 3.2 places every constructed seed on one $\mathbf Q$-defined component. Theorem 3.3 proves that every catalog problem in which PEL data are auxiliary may choose $I=\mathcal O_F$ and $\mathfrak c=\mathfrak d_F^{-1}$, so all five seed types occur on that component. An externally prescribed nonsquare narrow polarization class remains a different problem and is outside the stated reduction.

The semistable construction is genuinely $d$-dimensional. The period lattice $\mathfrak d_F^{-1}$, a regular cone containing the tensor valuation, and a periodic polyhedral decomposition give a proper polarized Mumford formal quotient. The polarized Raynaud-quotient construction of Book 60 and the ample formal algebraization theorem of Book 58 turn it into the projective algebraic family of Theorem 8.1. Its $\mathcal O_F$-action, ordered polarization, determinant condition, corrected $N$-level, and boundary one-motive are constructed on the same chart. Its Kodaira--Spencer map is an isomorphism in all $d$ directions, and the multivariable finite-flat condition is the intrinsic inclusion (8.21).

Ordinary reduction is open by partial Hasse invariants. Nonordinary reduction is retained on an open residue tube despite being closed in the special fiber. Semistability is retained in the full-dimensional chart by fixed positive valuation shells. Exact torsion representations and both frames are locally constant through finite etale isomorphism schemes, after only the completion extensions explicitly allowed in the datum. Proposition 3.2 and Theorem 12.1 ensure that every intersection is witnessed on the same geometrically connected twist.

Finally, good reduction, ordinary or local--local type, semistability, toric rank, and finite flatness survive finite extension. Splitness can improve, frames need not descend, and valuations rescale. Theorem 13.1 and Corollary 13.2 therefore provide all five nonempty local-open inputs required by simultaneous Moret--Bailly specialization in the unramified odd-prime, monodromy-admissible catalog range; an exact singleton mixed packet still needs Book 154's separate moving-presentation criterion, with $(\mathrm{ICS})_{v_0,Z}$ of Section 13.2A one sufficient but presently unproved input. The remaining qualifications—an externally fixed nonsquare polarization class, a dyadic coefficient prime, an unramified-only frame not realized over an unramified field, or two incompatible prescribed Tate Kummer classes—are explicit changes of scope, not unresolved dependencies of the local package proved here.

For a fixed smooth geometrically connected twist, Proposition 9.3 additionally gives
base-field points at all sufficiently large good places.  This uniform statement is designed
for auxiliary Chebotarev certificates; it makes no descent assertion at a prescribed small
place.
