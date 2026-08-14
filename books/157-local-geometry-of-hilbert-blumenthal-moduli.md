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
  - [13.2B Normalized fans and the toroidal joining boundary](#132b-normalized-fans-and-the-toroidal-joining-boundary)
  - [13.3 Passing from neighborhoods to every conjugate](#133-passing-from-neighborhoods-to-every-conjugate)
  - [13.4 Failure modes](#134-failure-modes)
- [14. Conclusion](#14-conclusion)
  - [14.1 The local dictionary](#141-the-local-dictionary)
  - [14.2 The package established and its boundaries](#142-the-package-established-and-its-boundaries)

## 1. From a global moduli space to local arithmetic

### 1.1 Why local points are the missing input

The preceding construction of Hilbert--Blumenthal moduli solves a global geometric problem. It gives a smooth fine scheme, pairing-preserving torsion-frame covers, twists by prescribed representations, and geometrically connected components. An arithmetic approximation theorem, however, does not manufacture a point on such a space from geometry alone. At every selected completion it must be given a nonempty open set of points having the required local behavior.

This changes the nature of the question. It is not enough to know that some Hilbert--Blumenthal abelian variety exists over an algebraic closure. One needs an object over a specified local field, on the specified twist and component, and one must know that nearby objects retain the desired condition. At a real place, “nearby” refers to the ordinary real topology. At a finite place, it refers to the topology defined by the valuation. At a residue-characteristic level prime, generic torsion is etale but its integral model is not, so a basis of geometric points does not see the finite-flat condition. At a semistable place, the abelian variety need not extend as an abelian scheme at all.

The purpose of this book is to turn those distinctions into a reusable local package. We construct seed points of five kinds: real, good, ordinary, nonordinary finite-flat, and semistable, put them on one corrected auxiliary-level component, and place each in a full-dimensional local neighborhood. The correction has three parts. The auxiliary principal level is given a cyclotomic-split source, so it has real points. A rank-$d$ Mumford period torus is algebraized at the tensor cusp, so the one-parameter Tate ray sits inside an ambient semistable chart. Finally, the polarization and component used in the potential-automorphy catalog are proved to be auxiliary choices and are reduced to the single tensor component. The local-open package is unconditional in its stated range.  For an exact singleton mixed packet, arithmetic approximation additionally needs the common moving presentation whose remaining joining input is isolated in Sections 13.2A--13.2B.

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

**Proposition 8.4A (the Tate level--tower boundary and ordinary rigidity).**  Let
$K/\mathbf Q_p$ be unramified, let $p$ be odd, and let $q_0\in K^\times$ have
$m=v_K(q_0)>0$.  Then the canonical filtered Tate group at level $p^r$ has a finite flat
model over $\mathcal O_K$ if and only if

$$
p^r\mid m.                                                     \tag{8.9a}
$$

In particular, no genuine Tate curve gives a characteristic-zero finite-flat lattice: its
residual $p$-torsion can be finite flat, but its compatible $p$-power tower cannot be.  If
$p\mid m$, the selected level-$p$ model is ordinary, with connected--etale sequence

$$
0\longrightarrow\mu_p\otimes\eta
\longrightarrow\mathcal G_{q_0,\eta}
\longrightarrow(\mathbf Z/p\mathbf Z)\otimes\eta
\longrightarrow0,                                             \tag{8.9b}
$$

where $\eta$ is trivial in the split case and is the unramified quadratic character in the
nonsplit case.  Consequently a good abelian scheme whose $p$-torsion is identified with this
selected model has ordinary special fiber.  It cannot lie in a local--local tube.
If $K=\mathbf Q_p$, $p\geq7$, and the good realization is elliptic, its reduction moreover
has Frobenius trace

$$
a_p=\eta(\operatorname{Frob}_p)\in\{1,-1\}.                 \tag{8.9b'}
$$

**Proof.**  Write $q_0=\pi^m u$.  The level-$p^r$ Kummer class has an integral unit
representative exactly when multiplication by a $p^r$th power can remove its valuation,
which is exactly (8.9a).  This is the same calculation as (8.6), with $p$ replaced by
$p^r$; Book 44, (11.6) records the compatible-level statement.  A fixed positive $m$ is not
divisible by every $p^r$.  Equivalently, the rational Tate representation has the nonzero
monodromy of Book 44, Section 10.5, whereas Book 54, Theorem 14.1 identifies a finite-flat
lattice with one whose every finite quotient belongs to one compatible finite-flat tower.
Thus level-one finite flatness does not supply the characteristic-zero deformation condition.

When $p\mid m$, (8.8), followed by the unramified quadratic twist when necessary, gives
(8.9b).  Its connected subgroup has rank $p$ and its etale quotient has rank $p$, so its
special fiber is ordinary.  If only a generic paired frame is initially given, Raynaud full
faithfulness for $e(K)=1<p-1$ extends it uniquely to the selected integral model.  An exact
integral identification therefore forces the same connected--etale sequence on the
$p$-torsion of any good realization, proving the last assertion.  In the elliptic case the
etale Frobenius eigenvalue is both $a_p\bmod p$ and
$\eta(\operatorname{Frob}_p)$.  Thus $a_p\equiv\eta(\operatorname{Frob}_p)\pmod p$.
The Hasse bound and $2\sqrt p+1<p$ for $p\geq7$ turn this congruence into (8.9b').
$\square$

The following proposition isolates the precise good-reduction replacement.  It deliberately
states the finite-field input instead of smuggling a converse to the Hasse bound into the
local moduli argument.

**Proposition 8.4B (Serre--Tate replacement from a trace-one seed).**  Let
$p\geq7$, let $q_0=p^{ps}u\in\mathbf Q_p^\times$ with $u\in\mathbf Z_p^\times$, and let
$\eta$ be trivial or unramified quadratic.  Assume that there is an elliptic curve
$C/\mathbf F_p$ with Frobenius trace $a_p(C)=1$.  Then there is a principally polarized good
ordinary elliptic curve $B/\mathbf Q_p$, extending to $\mathcal B/\mathbf Z_p$, and a paired
isomorphism of finite flat group schemes

$$
\mathcal B[p]\simeq\mathcal G_{q_0,\eta}.                     \tag{8.9c}
$$

Thus the multiplicative residual model, including its intrinsic line, Kummer class, split or
nonsplit sign, cyclotomic determinant, and Weil-pairing orientation, has a good ordinary
base-field realization.  The conclusion concerns level $p$; the full tower on the left is
finite flat because $\mathcal B$ is an abelian scheme.

**Proof.**  First take $\eta=1$.  Write
$u=\omega(\bar u)\langle u\rangle$ with $\langle u\rangle\in1+p\mathbf Z_p$.  Since a
Teichmuller unit satisfies $\omega(\bar u)^p=\omega(\bar u)$, it is itself a $p$th power.
Hence $[u]=[\langle u\rangle]$ in
$\mathbf Z_p^\times/(\mathbf Z_p^\times)^p$.

The trace-one curve is ordinary, and its etale line at level $p$ has arithmetic Frobenius
$1$: its polynomial is $X^2-X+p$, which reduces to $X(X-1)$.  Over the perfect residue field
its connected--etale $p$-divisible sequence splits, as in Book 55, Section 5.3.  At level
$p$ its two pure lines therefore have descended dual generators.  Fix them as a dual pair for
the principal polarization; this fixes both the Serre--Tate coordinate and the Weil-pairing
orientation before the deformation is chosen.  The required Kummer class is

$$
\xi_u=[\langle u\rangle]
\in(1+p\mathbf Z_p)/(1+p\mathbf Z_p)^p
\simeq(1+p\mathbf Z_p)/(1+p^2\mathbf Z_p).                   \tag{8.9d}
$$

Book 55, Sections 6 and 8 identifies the one-dimensional polarized Serre--Tate tangent space
over $\mathbf Z/p^2\mathbf Z$ with precisely this level-$p$ Kummer quotient.  Choose the
first-order deformation corresponding to $\xi_u$.  The polarized deformation functor is
formally smooth, so lift that point compatibly through all $\mathbf Z/p^n\mathbf Z$.  This
formulation is important: over the strict unramified splitting ring one may write a
Serre--Tate unit, but its higher-level coordinate need not be a constant unit over
$\mathbf Z_p$ because the pure Tate lattices carry descent.  Only its level-$p$ class is being
prescribed here.

For odd $p$, the $p$th-power map carries $1+p\mathbf Z_p$ onto
$1+p^2\mathbf Z_p$, by the $p$-adic logarithm.  Hence the class in
$\mathbf Z_p^\times/(\mathbf Z_p^\times)^p$ is already determined modulo $p^2$, and every
higher lift retains exactly $\xi_u$.  Book 55, Theorem 7.1 algebraizes the compatible
principally polarized formal deformation over $\mathbf Z_p$.  The resulting elliptic scheme
is good ordinary, and (8.9d), in the fixed dual generators, identifies its $p$-torsion
extension with (8.8) by a Weil-pairing-preserving isomorphism.  This also fixes the
determinant-line orientation.

For nontrivial $\eta$, take the unramified quadratic twist of the construction.  The twist
extends over $\mathbf Z_p$, changes the etale Frobenius sign from $1$ to $-1$, twists both
pure lines in (8.9b), and leaves the Kummer coordinate between them unchanged.  This proves
(8.9c). $\square$

**Lemma 8.4B.1 (the trace-one finite-field seed).**  For every prime $p\geq7$ there is an
elliptic curve over $\mathbf F_p$ with Frobenius trace $1$.

**Proof.**  Put

$$
D=1-4p,
\qquad
\varpi=\frac{1+\sqrt D}{2},
\qquad
\mathcal O=\mathbf Z[\varpi].
$$

Then $\mathcal O$ is the imaginary-quadratic order of discriminant $D$ and
$\varpi\bar\varpi=p$, $\varpi+\bar\varpi=1$.  Since $p\nmid D$, the proper invertible prime
$\mathfrak p=(\varpi)$ is away from the conductor.  Book 117, Section 5.4 identifies the
ring-class Galois action with $\operatorname{Pic}(\mathcal O)$.  The class of
$\mathfrak p$ is trivial, so $\mathfrak p$ splits completely in the ring class field
$H_{\mathcal O}/K$; a place above it has completion with residue field $\mathbf F_p$.

Book 117, Section 5.4 puts its CM $j$-invariant in $H_{\mathcal O}$.  Since $D<-4$, this
$j$-invariant is neither $0$ nor $1728$, so the standard $j$-equation gives an elliptic curve
over $H_{\mathcal O}$.  Its full $\mathcal O$-action is defined there: the field contains
$K$, and the differential embedding of $\mathcal O$ in characteristic zero is injective, so
Book 117, Section 6.5's Galois criterion fixes every endomorphism.  Its polarized CM
automorphism group is $\mathcal O^\times=\{\pm1\}$.  Fix a rational prime $r\ne p$.
Book 117, Theorem 4.1 and the local formula of its Section 8.3 apply to the resulting
unlevelled model up to exactly this automorphism group.  A unit at $\mathfrak p$ has trivial
$r$-component in its reflex idele and gives the trivial proper ideal transform.  Consequently
inertia on $T_r$ has image in $\{\pm1\}$.  Book 117, Theorem 8.1 gives potential good
reduction; more precisely, since $p$ is odd, the kernel of this at-most-quadratic inertia
character is reached over a totally ramified extension of degree at most two.  The residue
field remains $\mathbf F_p$, and the good-reduction criterion of Book 117, Section 8.3 gives
good reduction there.

For a lift of arithmetic Frobenius, the same CM comparison sends the lattice through the
$\mathfrak p^{-1}$-transform and returns it by multiplication with $\varpi$; the descended
unlevelled curve introduces only the same sign ambiguity.  A Frobenius lift after the totally
ramified base change differs by inertia and hence still acts on $T_r$ as
$\epsilon\varpi$ for some $\epsilon\in\{\pm1\}$.  Its characteristic polynomial is therefore

$$
X^2-\epsilon X+p,
\qquad \epsilon\in\{1,-1\}.
$$

Smooth proper base change gives an elliptic curve over the unchanged residue field
$\mathbf F_p$ with trace $\epsilon$.  If $\epsilon=-1$, its nontrivial quadratic twist over
$\mathbf F_p$ has trace $1$. $\square$

Combining Lemma 8.4B.1 with Proposition 8.4B makes the good ordinary replacement
unconditional in the stated range.  The Hasse bound alone would not prove the lemma; the
existence input comes from the prior CM reciprocity and potential-good-reduction package.

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

is integral and lies in $C^\vee$.  Put

$$
\rho_{\mathrm{ten}}=\mathbf R_{\geq0}\nu_{\mathrm{ten}}.
\tag{8.12a}
$$

The marked ray, rather than its interior in a maximal cone, is the correct regular-fan datum.
Indeed, under trace duality the ray is generated by $1\in\mathcal O_F$.  After scaling the
Fourier-dual lattice $N_N=N\mathcal O_F$ back to $\mathcal O_F$, if $d>1$ and a regular cone
generated by totally positive lattice vectors $a_1,\ldots,a_d$ contained $1$ in its interior,
regularity would give
$1=\sum n_i a_i$ with positive integers $n_i$.  Every real embedding would then give
$0<\tau(a_i)<1$, contradicting that the positive integer
$N_{F/\mathbf Q}(a_i)$ is less than $1$.  Thus the former interior-cone formulation is in
general impossible.

Let $N_N=\operatorname{Hom}(\mathfrak M_N,\mathbf Z)$ and let $v_1$ be the primitive generator
of $\rho_{\mathrm{ten}}$ in $N_N$.  Extend $v_1$ to a basis
$v_1,w_2,\ldots,w_d$ of $N_N$.  Since $v_1$ is an interior point of $C^\vee$, for sufficiently
large integers $c_i$ all

$$
v_i=w_i+c_iv_1\quad(2\leq i\leq d)
$$

belong to $C^\vee$.  The $v_i$ remain a basis.  Hence
$\sigma=\sum_i\mathbf R_{\geq0}v_i$ is a regular full-dimensional cone contained in
$C^\vee$ and $\rho_{\mathrm{ten}}$ is one of its faces.  This elementary construction is the
local marked-ray fan.  Section 13.2B constructs the unit- and descent-invariant projective fan
containing all its translates.

Let $R$ be a complete DVR on the good PEL base. Put

$$
P_\sigma=\sigma^\vee\cap\mathfrak M_N,
\qquad
B_\sigma=R[P_\sigma].
\tag{8.13}
$$

Let $x_{\mathrm{ten}}$ be the point of the toric orbit belonging to
$\rho_{\mathrm{ten}}$ obtained by reducing the tensor specialization below.  After a finite
etale coefficient extension if the cusp label or its unit coordinates require one, regularity
of $\sigma$ gives toric coordinates $t_1,\ldots,t_d$ for which $t_1=0$ cuts out the marked
boundary divisor and $t_2,\ldots,t_d$ are units at $x_{\mathrm{ten}}$.  If $u_i$ denotes the
Teichmuller lift of $t_i(x_{\mathrm{ten}})$ and $z_i=t_i-u_i$, completion at that point gives

$$
A_{\sigma,x}:=\widehat{(B_\sigma\otimes_RR')_{x_{\mathrm{ten}}}}
\simeq R'[[t_1,z_2,\ldots,z_d]].
\tag{8.14}
$$

This is the completion of a finite-type toric base at the actual tensor boundary orbit, not a
formal completion at the closed orbit that the tensor valuation never reaches.

Over the locus where all boundary monomials are invertible, define the universal period map

$$
u_Q:I\longrightarrow T_I,
\qquad
x(u_Q(a))=Q^{ax}
\quad(a\in I, x\in I^\dagger).
\tag{8.15}
$$

The exponent $ax$ belongs to $\mathfrak d_F^{-1}$, so (8.15) is defined over the torus of
$B_\sigma$ and over the punctured completion $A_{\sigma,x}[1/t_1]$. It is
$\mathcal O_F$-balanced. For $c\in\mathfrak c_I^+$, the map

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

**Theorem 8.1 (algebraized tensor-cusp chart).**  After narrowing the regular marked-ray cone
$\sigma$ above if necessary, the data (8.10)--(8.17) have the following algebraization over
$A_{\sigma,x}$.

1. There is a projective flat Mumford family $\overline{\mathcal A}_\sigma\to\operatorname{Spec}A_{\sigma,x}$ with an open semiabelian group locus $\mathcal G_\sigma$. Over
   $$
   U_\sigma=\operatorname{Spec}A_{\sigma,x}[1/t_1]
   $$
   it is an abelian scheme; write this restriction as $\mathcal A_\sigma$. Over the marked
   boundary orbit $t_1=0$, $z_2=\cdots=z_d=0$, the identity component of
   $\mathcal G_\sigma$ is the split torus $T_I$ of dimension $d$.
2. Multiplication on $I$ gives an $\mathcal O_F$-action, (8.16)--(8.17) give the ordered $\mathfrak c_I$-polarization and a relatively ample symmetric bundle, and the Lie algebra satisfies the Hilbert determinant condition.
3. The $N$-division periods give the cyclotomic-split level
   $$
   \mathscr L_{I,N}^{\natural}\xrightarrow{\sim}\mathcal A_\sigma[N]
   $$
   on the abelian locus and the corresponding level of the boundary one-motive.
4. The classifying map from the punctured $d$-dimensional period polydisc to $H_I^{\mathrm{ten}}$ is etale in every period direction. Its tensor ray is $A_{q_0}=E_{q_0}\otimes I$.

**Proof.** We give the construction because an individual Tate variety would not prove the theorem. Start with a coherent $I$-periodic rational polyhedral decomposition of $I\otimes\mathbf R$, obtained from the lower faces of the positive rational quadratic support function defined by (8.17), and use a generic periodic rational perturbation of its finitely many cell orbits to obtain a coherent triangulation refining it.  Choose the perturbation small enough that its support function remains strictly convex at $\nu_{\mathrm{ten}}$.  Convexity and compatibility across faces are finitely many strict rational linear inequalities modulo $I$. They therefore remain valid on a full-dimensional rational neighborhood of the marked ray.  In the basis construction preceding (8.13), take the $c_i$ sufficiently large that $\sigma$ lies in this neighborhood.  Refine coherently without changing the base ray $\rho_{\mathrm{ten}}$.  There are finitely many cells modulo $I$.

Each cell gives the standard toric formal chart for $T_I$ over $A_{\sigma,x}$; translation by $a\in I$ changes its character $x$ by the monomial $Q^{ax}$ from (8.15). The period identity

$$
Q^{(a+a')x}=Q^{ax}Q^{a'x}
$$

is exactly the cocycle on triple overlaps. The finitely many cell orbits therefore glue to a proper formal quotient. Fullness follows because every $\nu\in\sigma$ makes the pairing (8.17) positive definite, so a tropical point can be translated into a fixed finite union of cells. This is the higher-dimensional valuative argument used for Raynaud quotients.

Before completion, each toric chart algebra is a direct sum of copies of the base indexed by a saturated monoid. It is therefore $B_\sigma$-flat; localization at $x_{\mathrm{ten}}$, completion, and the open gluings preserve flatness. Hence the proper formal quotient is flat over $\operatorname{Spf}A_{\sigma,x}$.

The positive quadratic form (8.17) gives an integral strictly convex support function after multiplying by one positive integer. Its automorphy factors glue a relatively ample symmetric formal line bundle. The ample-line algebraization theorem for proper formal schemes algebraizes the quotient and that bundle uniquely to the projective $A_{\sigma,x}$-scheme $\overline{\mathcal A}_\sigma$. Equivalently, theta sections of a high power give the relative Proj; quadratic growth of (8.17) is their convergence and finite-generation estimate. This is the point at which the formal quotient becomes an algebraic family. Faithful completion transfers the formal flatness just proved to the algebraization. The toric action and period translations are monomial on the finitely many charts, so they algebraize the open semiabelian group locus $\mathcal G_\sigma$. More precisely, the polarized Raynaud quotient and periodic polyhedral model are the construction of Book 60, and algebraization of the proper formal scheme with its ample line bundle is the theorem of Book 58. Multiplying the support function only supplies an ample algebraizing bundle; it does not replace the exact maps (8.16). Those formal homomorphisms and their tensor-perfectness identities algebraize by graph effectivity. No compactification is being inferred from the open Hilbert scheme.

Multiplication by $b\in\mathcal O_F$ acts on the cocharacter lattice $I$, on the character lattice $I^\dagger$ contragrediently, and preserves (8.15). It therefore acts on $\mathcal G_\sigma$ and on the abelian generic locus. The equality $I\mathfrak c_I=I^\dagger$ proves tensor perfectness, while (8.17) proves symmetry and positivity. Since

$$
\operatorname{Lie}T_I\simeq I\otimes_{\mathbf Z}A_{\sigma,x}
$$

is locally free of rank one over $\mathcal O_F\otimes A_{\sigma,x}$, the universal determinant polynomial holds on the boundary formal chart. It is a closed identity and hence holds on the algebraization and its abelian locus.

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

Then $Q^{ax}$ maps to $q_0^{\operatorname{Tr}(ax)}$, which is the period evaluation for
$E_{q_0}\otimes I$.  In the regular coordinates of (8.14), $t_1$ has positive valuation and
$t_2,\ldots,t_d$ are units; after subtracting their residue lifts, the map is continuous on
$A_{\sigma,x}$.  The punctured completed ring is a domain, so $U_\sigma$ is connected. Its
classifying map meets the open-and-closed component $H_I^{\mathrm{ten}}$ along this tensor
specialization and therefore factors through that component everywhere. This proves the
tensor-ray and component assertions and completes the construction. $\square$

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

**Proof.** Use (8.19) to place $y$ on the algebraized chart.  Write
$x_1=t_1$ and $x_i=u_i+z_i=t_i$ for $i>1$.  The tensor valuation belongs to the relative
interior of $\rho_{\mathrm{ten}}$, so

$$
v_K(x_i)=v_K(x_i(y))=:m_i,
\qquad m_1>0,\quad m_i=0\ (i>1).
\tag{8.23}
$$

These are open conditions; shrink further so that the unit coordinates have the same residues.
Every resulting point reduces to the same marked boundary orbit.  Its identity component is
$T_I$; pulling back $\mathcal G_\sigma$ gives split semistable reduction of toric rank $d$.
The etale Kodaira--Spencer calculation in Theorem 8.1 and the nonarchimedean inverse function
theorem identify a small parameter polydisc around $y$ with an open subset of $H(K)$. Thus this
is an ambient $d$-dimensional open, not the one-dimensional tensor ray.

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
v_K(t_i)=m_i\geq0,
\qquad \nu_Q=\sum_i m_iv_i\in C^\vee,
\qquad \max_i m_i>0
\tag{10.4}
$$

are open shells; an entry equal to zero says that the corresponding toric coordinate is a unit.
Keeping its residue in a fixed unit neighborhood preserves the boundary orbit, toric rank, and
polarization type. The numbers $m_i$ determine the valuation homomorphism $\nu_Q$ in (8.20),
but the invariant finite-flat condition is not the basis-dependent assertion that each positive
displayed $m_i$ is divisible by $p$. It is

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

We first isolate the exact geometric output missing from the integral-slice route; Section
13.2B below separates its proved slicing and fan parts from the first absent toroidal premise.
This output is more than the existence of one curve over the local field.  Book 154 first approximates the local cutting
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

There are two logically different existence questions in this assertion.  The first is the
finite-type **joining problem**: put the corrected framed interior and the selected completed
cusp branch in one smooth projective model.  The second is the relative slicing problem inside
an already supplied model.  The second problem can be solved, including over the finite residue
field.  We do so now, so that it is not hidden inside the boundary assertion.

**Lemma 13.2A.1 (finite-field Bertini with imposed first jets).**  Let $X$ be a smooth
projective geometrically connected variety of dimension $m\geq2$ over a finite field
$\kappa=\mathbf F_Q$, let $\mathcal L$ be very ample, and let $E\subset X$ be a finite
reduced closed subscheme.  At every geometric point of $E$, prescribe a first jet of a section
of $\mathcal L^n$ whose value is zero and whose differential on the tangent space of $X$ is
nonzero; the collection of jets is required to be Galois-compatible.  After making the evident
choice of trivialization on the first infinitesimal neighborhood of $E$, for every sufficiently
large $n$ there is a section having those jets
whose zero scheme is smooth and geometrically connected of dimension $m-1$.

The same conclusion holds with $X$ replaced successively by smooth geometrically connected
complete intersections and with the sections still drawn from the ambient projective
coefficient spaces.  Consequently finitely many closed points, not necessarily
$\kappa$-rational, can be put on a smooth geometrically connected complete-intersection curve.

**Proof.**  We give the finite-field count.  This is the point not covered by Book 153's
infinite-field Bertini theorem.  Embed $X$ in $\mathbf P^N_\kappa$ by $\mathcal L$.  If $A$ is
a zero-dimensional subscheme of length $a$, then

$$
H^0(\mathbf P^N,\mathcal O(n))\longrightarrow H^0(A,\mathcal O_A(n))
\tag{13.14}
$$

is onto for $n\geq a-1$.  To prove this without assuming that a suitable hyperplane is defined
over the finite base field, extend scalars to $\overline\kappa$ and choose one hyperplane
disjoint from the finite support of $A$.  On its affine complement, filter
$H^0(A,\mathcal O_A)$ by the images of
polynomials of degree at most $j$ in the affine coordinates.  If two consecutive terms agree,
the common term is stable under every coordinate generator and hence is the whole algebra;
otherwise the dimension increases by at least one.  Since the algebra has dimension $a$, degree
$a-1$ suffices.  Homogenization proves surjectivity after scalar extension, and faithful
flatness descends it to $\kappa$.  Thus the space $S_n$ of polynomials with the prescribed
restriction on the first infinitesimal neighborhood of $E$ is a nonempty affine space for
large $n$.

For a closed point $x\notin E$ of degree $e$, singularity of $X\cap V(f)$ at $x$ says that
$f$ vanishes on

$$
x^{(2)}=\operatorname{Spec}(\mathcal O_{X,x}/\mathfrak m_x^2),
$$

which has length $(m+1)e$ over $\kappa$.  Whenever
$n\geq c_E+(m+1)e$, (13.14) makes this independent of the conditions at $E$, and hence

$$
\Pr_{f\in S_n}(x\text{ is singular})=Q^{-(m+1)e}.
\tag{13.15}
$$

Fix $r$.  The restrictions at the finitely many points of degree less than $r$ are
simultaneously onto for large $n$, so the probability of no singular point of degree less than
$r$ is

$$
\prod_{\substack{x\in|X\setminus E|\\ \deg x<r}}
 (1-Q^{-(m+1)\deg x}).
\tag{13.16}
$$

This has a positive limit as $r\to\infty$.  Indeed the number of degree-$e$ closed points is
$O(Q^{me})$, while
$\sum_eQ^{me}Q^{-(m+1)e}<\infty$.  The union bound and (13.15) show that the probability of a
singular point with

$$
r\leq\deg x\leq (n-c_E)/(m+1)
$$

is $O(Q^{-r})$, uniformly in $n$.

It remains to prove that points of larger degree have density zero; this is where merely
counting the points of $X$ would be insufficient.  Cover $X$ by finitely many affine opens on
which some $m$ ambient affine linear coordinates $t_1,\ldots,t_m$ have independent
differentials; after a principal localization they have dual derivations
$D_1,\ldots,D_m$.  This choice makes the products below restrictions of homogeneous
polynomials after multiplying by a fixed power of the homogenizing coordinate.  Put
$p=\operatorname{char}\kappa$ and
$\tau=\lfloor(n-c)/p\rfloor$, where $c$ absorbs homogenization and the imposed jets.  On one
such open choose $f_0$ uniformly in $S_n$, independently choose the variables below, and put

$$
f=f_0+g_1^pt_1+\cdots+g_m^pt_m+h^p,
\tag{13.17}
$$

where the $g_i$ and $h$ range independently through polynomials of degree at most $\tau$
whose first jets vanish on $E$.  The summand added to $f_0$ has zero prescribed jet, so for
every fixed choice of that summand translation is a bijection of $S_n$; consequently the
resulting $f$ is still uniform on $S_n$.  In characteristic $p$,

$$
D_i f=D_i f_0+g_i^p.
\tag{13.18}
$$

Set $W_i=V(D_1f,\ldots,D_if)$ in the chosen affine open.  Conditional on the earlier choices,
failure of $D_if$ to cut the dimension of one positive-dimensional irreducible component of
$W_{i-1}$ means that the restriction of $g_i^p$ equals one fixed regular function on that
component.  The restrictions of degree-$\tau$ polynomials to a positive-dimensional integral
affine scheme have dimension at least $\tau-c$: choose one nonconstant linear function and use
$1,u,\ldots,u^{\tau-c}$; these powers are linearly independent in its function field.  The
Frobenius map is injective on that field.  Bezout bounds the number of components of
$W_{i-1}$ by $O(n^{i-1})$.  Therefore the probability that the expected dimension drop fails
at the $i$th step is

$$
O(n^{i-1}Q^{-\tau+c}).
\tag{13.19}
$$

Outside an event tending to zero, $W_m$ is zero-dimensional of degree $O(n^m)$.

The last variable $h$ does not alter $W_m$.  At a closed point $x$ of degree $e$, the image of
polynomials of degree at most $\tau$ in $\kappa(x)$ has dimension at least
$\min\{\tau-c,e\}$.  To see this without a primitive-element assumption, filter the field
$\kappa(x)$ by polynomial degree in the fixed affine coordinate generators.  If two consecutive
terms of this filtration agree before the whole field is reached, the common term is stable
under every generator and hence already is the whole field; otherwise its dimension increases
by at least one at each step.  The fixed jet conditions cost only $c$ dimensions.  Since
Frobenius is an automorphism of $\kappa(x)$, conditional on $W_m$ the probability that
$f(x)=0$ is at most

$$
Q^{-\min\{\tau-c,e\}}.
$$

For $e>(n-c_E)/(m+1)$ this is $Q^{-c'n}$ for a constant $c'>0$.  The degree bound on $W_m$
therefore makes the probability of any such singular point
$O(n^mQ^{-c'n})$.  Summing over the finite affine cover, (13.19) proves that the high-degree
probability tends to zero.

Choose $r$ so that the positive product (13.16) is larger than twice the medium-degree error,
and then choose $n$ so large that the high-degree error is smaller than the remaining half.
A desired section exists.  Its divisor is geometrically connected after increasing $n$ once
more.  Over $\overline\kappa$, the exact sequence

$$
0\longrightarrow\mathcal O_X(-n)
\longrightarrow\mathcal O_X
\longrightarrow\mathcal O_{V(f)}\longrightarrow0
$$

and Serre duality identify the only connectedness obstruction with
$H^{m-1}(X,\omega_X\otimes\mathcal L^n)$, which vanishes by Serre vanishing.  Thus
$H^0(V(f),\mathcal O)=\overline\kappa$.  Smoothness then makes $V(f)$ geometrically connected.
Apply the same argument on each successive smooth cut, choosing its degree large enough and
using ambient restriction surjectivity from Serre vanishing.  This proves the last assertion.
$\square$

**Lemma 13.2A.2 (stable relative complete-intersection slice).**  Let $R$ be a complete DVR
with finite residue field $\kappa$, and let $\mathcal X/R$ be smooth and projective of relative
dimension $d\geq1$, with geometrically connected fibers.  Let $\mathcal L$ be relatively very
ample, let $s_1,\ldots,s_a$ be pairwise disjoint $R$-sections, and let
$U\subset\mathcal X_\kappa$ be a nonempty open.  Then, after replacing $\mathcal L$ by powers
which may be different at the successive cuts, there are $d-1$ relative sections from the
finite free coefficient modules

$$
H^0(\mathcal X,\mathcal L^{n_i})
$$

whose common zero scheme $\mathcal C$ is a smooth proper geometrically connected relative curve,
contains every $s_i$, and has $\mathcal C_\kappa\cap U\ne\varnothing$.  At the marked sections
the inclusion is a regular immersion and the cutting Jacobian has rank $d-1$.

The conclusion is stable on a congruence neighborhood of the coefficient tuple.  A nearby
tuple need not contain the original sections, but after fixing one transverse etale coordinate
at each $s_i$, the implicit-function theorem supplies nearby $R$-sections with the same
reductions.  If the coefficient tuple is obtained by scalar extension from a global
finite-dimensional coefficient space, this entire congruence neighborhood is a legitimate
weak-approximation condition in that space.

**Proof.**  For $d=1$ take $\mathcal C=\mathcal X$.  Suppose $d>1$.  Choose a closed point
$u\in U$; it need not be $\kappa$-rational.  On the special fiber apply Lemma 13.2A.1
successively, imposing zero values and independent normal first jets at the reductions of the
$s_i$ and at $u$.  This gives a smooth geometrically connected complete-intersection curve
$C_0\subset\mathcal X_\kappa$ through those points.

For $n$ large, relative Serre vanishing gives

$$
H^1(\mathcal X,\mathcal I_{\cup s_i}\mathcal L^n)=0.
$$

Reduction on sections vanishing along all the $s_i$ is therefore onto.  Lift the special-fiber
cuts one at a time inside these modules.  A lift is a relative nonzerodivisor because its
special-fiber restriction is a nonzerodivisor; the resulting cut is flat over $R$.
Inductively its special fiber is the smooth cut already constructed.  The nonsmooth locus of
the resulting proper flat
$R$-scheme is closed and proper over $R$.  It has empty special fiber, and hence is empty;
otherwise its proper image would contain the generic point and therefore also the closed point
of $\operatorname{Spec}R$.  Thus every cut, and finally $\mathcal C$, is smooth over $R$.
Geometric connectedness follows from that of the special fiber, equivalently from the etale
component scheme of a proper smooth family.

The rank condition at the sections is the imposed first-jet condition.  Smoothness of a fixed
special fiber and that rank condition depend only on a finite reduction of the coefficients.
Keeping the tuple congruent modulo a sufficiently high power of the maximal ideal therefore
keeps the special curve and the point $u$ unchanged.  Complete the cutting equations at a
marked section by one transverse coordinate.  Their Jacobian is invertible; Hensel's lemma
solves the perturbed equations with that coordinate fixed and produces the asserted nearby
section.  This proves stability. $\square$

We can now state exactly what remains of the joining problem.  Call
$(\mathrm{FTJ})_{v,Z}$ the following **finite-type framed joining datum**.

1. There is a projective compactification $\overline Y$ of the selected corrected twist $Y$
   over the global characteristic-zero base and a smooth projective $R$-model
   $\overline{\mathcal Y}$ of $\overline Y_k$ which contains
   $\mathcal Y^{\mathrm{good}}$ as an open.  A relatively very ample bundle on this model is
   the extension of a power of the global ample bundle, so its spaces of cutting sections are
   lattices in Book 154's global coefficient spaces.
2. The closure of the selected semistable point is an $R$-section, and the completion of
   $\overline{\mathcal Y}$ along its boundary branch is identified with the normalization of
   Theorem 8.1's Mumford chart after adjoining the division monomials required by the corrected
   auxiliary level and both paired frame levels.  Under this identification the section has
   the prescribed valuation and Kummer shells, enhanced line, sign, and exact frames.
3. The closure of $Z$ does not contain the good special fiber.  For the literal clause 3 in
   $(\mathrm{ICS})_{v,Z}$, there is in addition a good $R$-section $P$ whose generic point lies
   in the assigned good integral neighborhood of $y_{\mathrm{good}}$ and whose reduction lies
   outside that closure.  If this last rational-point clause is omitted, retain instead any
   closed point of the nonempty good complement and use $y_{\mathrm{good}}$ as the marked good
   section.

The word "normalization" in item 2 is essential.  A full prime-to-residue-characteristic frame
at a cusp adjoins roots of the period monomials; it is not the unramified extension of the
unframed toroidal chart along the boundary.

The exact geometric theorem to be proved is therefore:

> **Required framed joining theorem $(\mathrm{FTJ})$.**  For the global corrected tensor
> component and determinant-compatible two-prime twist, at every finite place satisfying the
> exclusions above and for every selected tensor-cusp branch, the already recorded global and
> local data admit items 1--2 of $(\mathrm{FTJ})_{v,Z}$, without enlarging the completion beyond
> the extension already present in the local packet.  The construction is compatible with the
> unramified descent cocycles of the corrected auxiliary source and both prescribed frame
> systems, and the relatively ample bundle descends with them.

This is a finite-type compactification-and-comparison theorem, not merely the existence of a
regular fan after geometric base change.  In particular it must identify the completed local
ring and the universal one-motive on the normalized framed compactification before descent.

Section 13.2B proves the Kummer-normalization and equivariant-fan inputs.  It also proves that,
once the full unframed $(\mathrm{MPE})+(\mathrm{ACE})$ cusp package is supplied, finite
normalization and effective descent produce the paired-frame twist without a second
compactification theorem.  The first missing input and the resulting conditional fan-dependent
theorem are isolated there.  The required compactification is not proved.

**Proposition 13.2A.3 (the joining datum implies the stable slice).**  The datum
$(\mathrm{FTJ})_{v,Z}$ implies $(\mathrm{ICS})_{v,Z}$.  If the final rational-point clause in
item 3 is omitted, it implies the slightly weaker assertion obtained from clause 3 of
$(\mathrm{ICS})_{v,Z}$ by deleting the requirement that $W$ contain the specialization of
$P$.  This weaker assertion is still sufficient for Book 154, Lemma 5.2D and for Proposition
13.2A below.

**Proof.**  Apply Lemma 13.2A.2 to $\overline{\mathcal Y}$ and the semistable section together
with $P$ in the literal version or $y_{\mathrm{good}}$ in the weaker version, and put

$$
U=(\mathcal Y^{\mathrm{good}}_\kappa\setminus\overline Z_\kappa).
\tag{13.20}
$$

In the literal version use the reduction of $P$ as the imposed point in $U$; in the weaker
version use any closed point of $U$.  Relabel the marked good point as $P$ on the generic
curve.  The open (13.20) is dense.  Indeed the special fiber of
the smooth projective model is geometrically integral.  At its generic point the local ring of
$\overline{\mathcal Y}$ is a DVR with uniformizer $\pi$.  The ideal of the schematic closure of
a proper generic-fiber closed subset is $\pi$-saturated; if it vanished at that generic point,
successive division by $\pi$ and Krull intersection would make the generic-fiber ideal zero.
Thus $\overline Z_\kappa$ contains no special-fiber component.  The boundary likewise does not
contain the good open.

Let $\mathcal C$ be the resulting relative curve.  On its generic fiber remove the finite
intersection with the boundary and with $Z$, and call the result $C^\circ$.  It contains the
two marked generic points and maps immersively to $Y\setminus Z$.  Put

$$
W=\mathcal C_\kappa\cap U.
$$

It is nonempty, hence dense in the smooth connected special curve.  Every point of the finite
generic complement specializes into the boundary or $\overline Z_\kappa$, so its closure is
disjoint from $W$.  A closed point of the generic curve whose closure is contained in $W$
therefore extends through $\mathcal Y^{\mathrm{good}}$.  It carries the universal ordered
polarization, corrected auxiliary level, both exact paired frames, and the selected component;
its underlying abelian variety has good minimal reduction.  The completed-chart identification
places the semistable marked point in $V_{\mathrm{sp}}$ with its enhanced data.

Finally, the ample bundle and all cuts came from lattices in the global coefficient spaces.
Lemma 13.2A.2 gives a congruence neighborhood on which the special curve and $W$ are unchanged
and the marked generic points continue into their assigned neighborhoods.  This is precisely
the stability required in clauses 1--3. $\square$

There is a small but genuine finite-residue warning in the literal formulation.  The condition
that $W$ contain the specialization of a $k$-rational $P$ forces

$$
(\mathcal Y^{\mathrm{good}}_\kappa\setminus\overline Z_\kappa)(\kappa)\ne\varnothing.
\tag{13.21}
$$

Properness of $Z$ does not imply (13.21).  To see this in a form compatible with a global
$Z$, embed a projective closure by a global very ample bundle.  For every one of the finitely
many $\kappa$-points of the good special fiber choose a special-fiber hyperplane through that
point which does not contain the special fiber, and take the product of their equations.  Lift
that product to the global coefficient field.  Its generic zero locus $Z$ is proper, while its
closure contains every $\kappa$-point of the good special fiber.  Smoothness supplies many
$R$-lifts of each such point, and a lift can be chosen off the generic hypersurface.  Adding
$\pi$ times a general global section does not change the special equation and keeps any fixed
finite list of generic seeds off $Z$.  Thus the hypotheses preceding
$(\mathrm{ICS})_{v,Z}$ need not detect the failure.  The literal assertion cannot be a
theorem for arbitrary $Z$ over a fixed finite residue field without (13.21), an allowed
unramified residue extension, or deletion of the unnecessary requirement that $P$ specialize
inside $W$.  Book 154, Lemma 5.2D requires only that $W$ be nonempty; it does not require a
$\kappa$-point of $W$.

**Proposition 13.2A (conditional closure of the singleton moving input).**  Consider a
simultaneous approximation problem on $Y\setminus Z$ with one special place $v_0$.  Suppose
$(\mathrm{ICS})_{v_0,Z}$ holds there (or its weaker form from Proposition 13.2A.3, in which
$P$ need not specialize in $W$), every other exact packet may be repeated wholesale, and
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

Thus $(\mathrm{ICS})_{v_0,Z}$, and also the weaker form just specified, discharges the
one-special/all-other-good moving input, with no remaining Picard congruence, in any later
application satisfying the other hypotheses of the
proposition.  Lemmas 13.2A.1--13.2A.2 prove the stable relative-slicing part.  Thus the only
geometric input still to construct at this point is the exact finite-type joining theorem of
items 1--2 above.  Section 13.2B proves its Kummer-normalization and fan-construction
sublemmas, reduces the frame and twist operations to normalization and polarized descent, and
isolates the first absent relative Mumford--PEL equivalence as Required Theorem 13.2B.3a,
followed by the separate algebraic cusp-effectivity ledger $(\mathrm{ACE})$.  Required Theorem
13.2B.3, and hence even the weaker form of $(\mathrm{ICS})$ needed by Book 154, remains
conditional on those inputs.  For the literal form of $(\mathrm{ICS})$, (13.21) is an
additional necessary arithmetic input.

Here is the source audit.

- Theorem 8.1 constructs the Mumford family over the completion
  $R'[[t_1,z_2,\ldots,z_d]]$ at the actual tensor-ray orbit, and Theorem 8.2 constructs a
  point-centered valuation shell there.  They do not by themselves identify that completed
  chart with the boundary completion of one projective finite-presentation $R$-model containing
  $\mathcal Y^{\mathrm{good}}$.  For the paired-frame twist one must moreover normalize in the
  division monomials, choose a regular projective fan for the refined cusp lattice, extend the
  unramified twisting cocycle over all cusp labels, and descend the ample bundle.  Lemmas
  13.2B.1--13.2B.2 carry out normalization and fan construction, while Proposition 13.2B.3b
  proves the extension and descent steps conditional on the full unframed
  $(\mathrm{MPE})+(\mathrm{ACE})$ cusp package.  The first
  unproved assertion is Required Theorem 13.2B.3a: the inverse-to-Mumford equivalence in
  families.  Algebraic effectivity of the unframed cusp embeddings is the subsequent
  $(\mathrm{ACE})$ ledger.  A point-centered shell still reduces to one fixed boundary orbit,
  so shrinking that shell alone cannot produce the inverse image of a good special-fiber open.
- Book 58 algebraizes a proper formal scheme only after the whole compatible formal system and
  an ample formal line bundle have been supplied.  Here Theorem 8.1 supplies a proper formal
  **abelian family over** one completed toric base, not a proper formal compactification of the
  framed moduli base.  It therefore gives neither the missing cusp-to-interior gluing nor the
  descent datum for an ample bundle on that gluing.  Applying formal GAGA at that point would
  assume the principal input of $(\mathrm{FTJ})$.  Book 58 is used only for the projective
  Mumford family over an already completed base; it does not algebraize the moduli base or its
  gluing to the interior.
- Book 8 represents fixed-polynomial curve families by a Hilbert scheme.  Representability
  supplies a parameter space and its universal family; it does not prove that the open locus
  expressing the finite-type joining condition has an $R$-point.  A bare projective closure of
  the already quasi-projective integral model supplies neither compatibility with the completed
  cusp chart nor smoothness of the framed normalization.  Adding theta embeddings and structure
  graphs does not repair this: the schematic Hilbert closure need not realize a chosen fan, and
  equality with the desired completed deformation rings is precisely what would have to be
  proved.  Required Theorem 13.2B.3 asks for that fan-dependent toroidal construction directly.
  Once its smooth projective joining model is supplied, Lemmas 13.2A.1--13.2A.2 construct the
  required relative slice.
- Book 153's Bertini argument is over an infinite characteristic-zero field and controls the
  generic curve.  It contains no relative Bertini theorem over a DVR with finite residue field.
  Lemma 13.2A.1 supplies the missing finite-field count and Lemma 13.2A.2 supplies the relative
  lifting and congruence stability.
  Books 9 and 10 respectively control divisors on an already supplied relative curve and the
  descent of already supplied projective data; neither constructs the framed joining model.
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

### 13.2B Normalized fans and the toroidal joining boundary

We now separate the part of the compactification problem proved here from its first missing
moduli step.  A bare appeal to a toroidal compactification is insufficient: the fan must be regular
for the **refined** lattice seen by the two frames, normalization must be computed before
completion, the chosen fan charts must actually be embedded and glued to the moduli interior,
and the ample bundle must carry the same descent datum as the twisted scheme.  The fan and
normalization are proved below; Proposition 13.2B.3b proves the frame and twist descent once
the full unframed $(\mathrm{MPE})+(\mathrm{ACE})$ cusp package exists.  Required Theorem
13.2B.3a is the first missing theorem;
the downstream effectivity ledger is kept separate, and the resulting framed output is stated
as Required Theorem 13.2B.3.

Fix a field over which the corrected auxiliary source and the two paired source systems are
split.  A cusp branch $b$ of the selected component then consists of an isotropic direct
summand in the rank-two PEL lattice, its ordered polarization label, its corrected $N$-level
label, and, at each of $\mathfrak p$ and $\mathfrak q$, the isotropic line which the chosen
frame sends to the toric part of the boundary one-motive.  There are finitely many such labels
modulo the arithmetic group: after the isotropic line is fixed, the remaining label is an ideal
class together with data in finite level quotients.  Finiteness is therefore the ordinary
narrow-class finiteness already used in Book 156, followed by a finite choice at each level.

For a branch $b$, let $\mathfrak M_b^0$ be its Fourier lattice after the corrected auxiliary
$N$-division monomials have been inserted.  On the torus of the cusp, the boundary one-motive
has the form

$$
[I_b\xrightarrow{u_Q}T_b],
\qquad
x(u_Q(a))=Q^{ax}.
\tag{13.22}
$$

At $\mathfrak r\in\{\mathfrak p,\mathfrak q\}$ its torsion has the exact sequence

$$
0\longrightarrow T_b[\mathfrak r]
\longrightarrow[I_b\to T_b][\mathfrak r]
\longrightarrow I_b/\mathfrak r I_b\longrightarrow0.
\tag{13.23}
$$

Choosing the framed branch chooses the toric line in (13.23), a complementary vector, and its
division lift.  Choose bases in the two finite lattices in (13.23) and put the resulting
inclusion matrix in Smith normal form.  The equations $n_jP_j=u_Q(a_j)$, evaluated on a basis
of characters of $T_b$, then say in character coordinates that the lift is given by finitely
many equations

$$
X_j^{\,n_j}=\zeta_jQ^{\xi_j},
\qquad n_j\mid (Npq)^a,
\tag{13.24}
$$

where the roots of unity are etale at the place under consideration.  Define the **framed
Fourier lattice**

$$
\mathfrak M_b^{\mathrm{fr}}
=\mathfrak M_b^0+\sum_j\mathbf Z\,\frac{\xi_j}{n_j}
\subset \mathfrak M_b^0\otimes\mathbf Q.
\tag{13.25}
$$

This definition is independent of the displayed generators: it is the character lattice of
the connected Kummer torus in the normalization of that framed branch.  Changing a
complementary framed vector multiplies the $X_j$ by toric torsion and hence changes neither
the lattice nor the normalized algebra.  Its index over $\mathfrak M_b^0$ is supported only at
$Npq$ and is therefore a unit in $R$.

**Lemma 13.2B.1 (normalization in the division monomials).**  Let $R'/R$ be the recorded finite
etale extension splitting the unramified source systems at $v$ and all constant Kummer factors
in (13.24): for each $j$ it contains a compatible
$\alpha_j$ with $\alpha_j^{n_j}=\zeta_j$.  Since every $n_j$ is a unit in $R$, this is a
finite-etale constant-field condition; it is part of the recorded branch splitting, not a
later enlargement of the completion.  Put
$M=\mathfrak M_b^0$, $M'=\mathfrak M_b^{\mathrm{fr}}$, and let $\sigma$ be a rational
polyhedral cone in the common real cocharacter space.  Then the normalization of

$$
R'[\sigma^\vee\cap M]
$$

in the branch field defined by (13.24) is

$$
R'[\sigma^\vee\cap M'].
\tag{13.26}
$$

Normalization commutes with completion at every boundary orbit.  The completed universal
one-motive is (13.22), now with all division monomials in $M'$, and its two universal frames
are exactly the frames selected by the branch.  The chart (13.26) is smooth over $R'$ exactly
when $\sigma$ is regular for

$$
N_b^{\mathrm{fr}}=\operatorname{Hom}(M',\mathbf Z).
\tag{13.27}
$$

**Proof.**  Rescaling $X_j$ by $\alpha_j^{-1}$ removes the constants in (13.24).  The connected
part of the Kummer extension of the torus is then the isogeny of split tori induced by
$M\subset M'$.  Thus its coordinate algebra on the torus is $R'[M']$.  Every monomial $Q^{m'}$ with
$m'\in\sigma^\vee\cap M'$ is integral over the old chart, because a positive multiple of
$m'$ lies in $M$ and its corresponding monomial satisfies a monic equation.  Conversely, the
orders along the primitive rays of $\sigma$ are discrete valuations on the common torus
field.  An element integral over the old monoid algebra has nonnegative order for all those
valuations.  Its character support therefore lies in $\sigma^\vee$, and the torus
normalization restricts it to $M'$.  This proves (13.26).  It is the elementary saturation
proof of normality of a toric monoid algebra, not an assertion that an unramified cover stays
unramified at the boundary.

The algebra in (13.26) is finite over the old one.  Complete DVRs and their finite-type
algebras are excellent, so the integral closure of a finite algebra commutes with completion;
equivalently, the same ray-valuation argument applied to completed monomial series gives the
completed version directly.  Sequence (13.23) shows that adjoining precisely these monomials
constructs the chosen division lifts.  The Weil pairing on the one-motive sends their wedge to
the fixed determinant line, so the resulting frames are paired, not merely bases.  Finally a
toric chart over a regular base is smooth exactly when the primitive generators of each cone
extend to a basis of its cocharacter lattice.  Applied to (13.27), this proves the last
assertion. $\square$

We next construct the fan.  Write $C_b$ for the positive monodromy cone and
$\Gamma_b$ for the cusp stabilizer left after the unipotent translations have been absorbed in
the Fourier lattice.  It is a finite-index subgroup of the totally positive units satisfying
the selected level congruences.  Let $\Delta$ be the finite group generated by the Galois
descent of the corrected source and by the two finite frame deck groups.  It permutes the
finite set of cusp branches, their lattices, and their positive cones.

Write $b^\circ$ for the cusp label obtained from $b$ by forgetting only the two paired-frame
labels, and write $\Gamma_b^\circ$ for its stabilizer on the corrected auxiliary-level
component.  Then $\Gamma_b\subset\Gamma_b^\circ$ has finite index.  The frame deck
transformations identify the branches over $b^\circ$ and account for the finite quotient
$\Gamma_b^\circ/\Gamma_b$.  Thus a $\Delta$-equivariant collection of fans on the framed
branches descends, after forgetting the frame labels, to one
$\Gamma_b^\circ$-equivariant fan at the unframed cusp.  The equivariant barycentric
refinement used below removes inversions for this combined action, and the corrected
$N\geq3$ level is already neat; hence the same ray-fixing argument gives trivial stabilizers
for every nonzero cone under $\Gamma_b^\circ$.  The zero cone is of course stabilized by the
whole cusp group; it belongs to the interior torus, where freeness instead comes from the fine
neat-level moduli problem.

**Lemma 13.2B.2 (simultaneous regular projective marked-ray fan).**  There are fans
$\Sigma_b$ in $C_b\cup\{0\}$ such that:

1. $\Sigma_b$ is rational and regular for $N_b^{\mathrm{fr}}$, is locally finite, covers
   $C_b\cup\{0\}$, and has finitely many $\Gamma_b$-orbits;
2. the collection is preserved by $\Delta$, and every prescribed tensor valuation ray is a
   one-dimensional cone of the relevant fan;
3. every nonzero cone has trivial stabilizer in the neat cusp group; and
4. there is a $\Gamma_b$-invariant integral strictly convex piecewise-linear support function
   $h_b$, with the collection $(h_b)$ preserved by $\Delta$ after replacing it by a common
   positive multiple; and
5. on every nonzero cone there is an $I_b$-periodic rational polyhedral decomposition used by the
   Mumford quotient, compatible on faces and under $\Gamma_b\rtimes\Delta$, whose polarization
   support function is strictly convex for every nonzero monodromy form in that cone.

In particular the fans are simultaneously smooth and projective for the normalized framed
charts.

**Proof.**  We include the reduction-theoretic and toric steps.  Projectivize $C_b$ by any
positive rational linear functional.  Under the logarithmic map, totally positive units act
by a full lattice in the hyperplane where the sum of the coordinates is zero.  Hence the
projectivized quotient by $\Gamma_b$ is compact.  We first produce a projective fan without a
choice of fundamental-domain boundary.  Put $N=N_b^{\mathrm{fr}}$ and let $\Pi$ be the closed
convex hull in $C_b$ of $N\cap C_b$.  Every positive ray meets the boundary of $\Pi$ nearest
the origin.  Indeed, after moving its logarithmic direction into a fixed compact fundamental
set, take a fundamental parallelotope for $N$.  For a uniformly large multiple $tx$, all
vertices of the lattice parallelotope containing $tx$ remain positive; hence $tx$ is a convex
combination of positive lattice points and lies in $\Pi$.  A fixed positive linear functional
has a positive minimum on $N\cap C_b$, which gives the uniform lower radial bound.  The same bounds
show that only finitely many lattice points can lie on the nearest boundary over a compact set
of logarithmic directions.  Thus that boundary is locally a rational polyhedron.

Take the cones from the origin over its faces.  They meet along common faces and cover
$C_b\cup\{0\}$.  The construction is $\Gamma_b$-invariant.  It has finitely many cone orbits:
choose a positive supporting functional for a nearest face and move its logarithmic direction,
under the contragredient unit action, into a compact fundamental set in the dual positive cone.
Normalize it so that its minimum on $N\cap C_b$ is $1$.  The parallelotope argument above,
applied dually, bounds this normalizing scalar above and below.  Its coordinates are therefore
bounded away from zero and infinity, so every lattice point on the hyperplane $\lambda=1$
lies in one bounded subset of $N\otimes\mathbf R$.  There are only finitely many possible
vertex sets and hence finitely many face orbits.  If a face lies in the rational supporting hyperplane $\lambda=1$, set the
support function equal to $\lambda$ on its cone.  These pieces agree on common faces and form
the strictly upper-convex radial function of $\Pi$; reversing the sign gives the opposite
toric convention.  There are only finitely many denominators modulo $\Gamma_b$, so one common
multiple makes it integral.  This proves projectivity and local finiteness internally.

The finite group $\Delta$ carries $N\cap C_b$ for one branch to the corresponding set for the
conjugate branch, so these initial fans and support functions are already transported by
$\Delta$.  There are only finitely many marked rays modulo $\Gamma_b\rtimes\Delta$.  For each
orbit, take the common refinement of the star subdivisions at all of its rays.  On a compact
logarithmic fundamental set only finitely many stars occur; adding their transported rational
tent functions gives an invariant coherent support function for the common refinement.  Thus
all marked rays become one-dimensional cones without losing local finiteness, finite orbit
count, or projectivity.

We also impose the Mumford polyhedral data before desingularizing.  At one positive monodromy
form choose a coherent $I_b$-periodic rational polyhedral decomposition from the lower faces
of its quadratic support function and a generic periodic rational coherent triangulation
refining it, as in the proof of Theorem 8.1.  Strict
convexity is a finite list of strict rational linear inequalities modulo $I_b$, so the same
triangulation works on a rational open cone of monodromy forms.  Compactness of the logarithmic
quotient gives finitely many such cones modulo $\Gamma_b$, and transporting them gives the
$\Delta$-compatibility.  Subdivide by all their rational walls.  Equivalently, assign the
finitely many cell orbits rational heights and take the common lower-face refinement; the sum
of the transported lower-envelope functions proves coherence.  On a common face take the
common subdivision of the two periodic decompositions.  Thus the decompositions agree under
face restriction, and later fan refinements merely restrict a decomposition already chosen on
the parent cone.

The barycentric subdivision, equivalently successive equivariant star subdivisions at the
relative-interior barycenters in decreasing dimension, gives a coherent simplicial refinement.
It has the stronger regular-action property needed below.  A cone of the barycentric
refinement is a chain of parent faces, with at most one parent face of each dimension.  If a
face and one of its translates are both faces of one refined cone, their chains have the same
dimension pattern and hence are the same subchain.  Thus no cone contains two distinct
translates of any one face; in particular a group element stabilizing a cone fixes its chain
of parent faces and every ray, so there are no inversions.  This regular-action property is
preserved when one performs stellar subdivision simultaneously on an orbit whose distinct
members lie in no common cone: the result is the pullback of the single stellar subdivision on
the quotient conical complex.

It remains to make the fan regular without losing coherence.  For a simplicial cone with
primitive ray generators $e_1,\ldots,e_s$, put

$$
\mu(\sigma)=
[N_b^{\mathrm{fr}}\cap\operatorname{span}_{\mathbf R}(\sigma):
 \mathbf Ze_1+\cdots+\mathbf Ze_s].
\tag{13.28}
$$

Suppose the largest multiplicity is $m>1$, choose a cone of multiplicity $m$, and choose a
nonzero lattice point in its half-open fundamental parallelepiped.  Let $w$ be its primitive
multiple and let $\tau$ be the smallest face whose relative interior contains $w$.  If
$w=\sum_{i\in I}a_i e_i$ on $\tau$, then $0<a_i<1$.  Star subdivision at $\mathbf R_{\geq0}w$
replaces every containing simplicial cone $\eta$ by cones whose determinants are

$$
a_i\mu(\eta),\qquad i\in I.
$$

They are positive integers strictly smaller than $\mu(\eta)$.  Multiplicity of a face divides
the determinant of any full cone containing it, so no new cone of multiplicity $m$ is created,
and at least the chosen orbit of $m$-cones disappears.  Because inversions were removed, the
stabilizer of $\tau$ fixes its rays and $w$; consequently the subdivisions over the whole
$\Gamma_b\rtimes\Delta$-orbit agree.  By the regular-action property, distinct orbit members
lie in no common cone, so their subdivisions commute; the same
property persists afterward.  There are finitely many cone orbits, and every
subdivision creates only finitely many new orbits.  Induction first on the maximal
multiplicity and then on the number of orbits having that multiplicity therefore terminates
with a regular fan.  A small invariant rational tent function at each new ray preserves strict
convexity; clear the finitely many denominators on the quotient at the end.  Marked rays are
never removed and, being one-dimensional, are already regular.

It remains only to check freeness along the toroidal boundary.  The no-inversions property is
inherited by every refinement.  An element of the cusp stabilizer preserving a nonzero cone
therefore fixes each of its primitive rays.  On $N\subset F$ its infinite part is
multiplication by a totally positive unit; fixing one nonzero element forces that unit to be
$1$.  The residual finite
level permutation is killed by neatness.  Hence every cone stabilizer in the cusp group is
trivial away from the zero cone.  On the interior corresponding to the zero cone, the corrected
fine neat level supplies freeness.  This proves all five claims. $\square$

The normalization and fan construction stop here.  They produce the candidate monoid charts and
the combinatorics with which a toroidal compactification would have to be built; they do not
embed those charts into the Hilbert moduli space or algebraize their formal gluing to its
interior.  Before stating the resulting global theorem, we isolate the first moduli-theoretic
input which that construction would have to use.

Put

$$
P^0_{b^\circ,\sigma}=\sigma^\vee\cap\mathfrak M_b^0,
\qquad
U^0_{b^\circ,\sigma}=\operatorname{Spec}S'[P^0_{b^\circ,\sigma}],
\tag{13.28a}
$$

where $S'$ is either the split global coefficient base or its unramified complete-DVR base
change.  Its open torus is denoted $T_{b^\circ}^0$ and its toric boundary by
$\partial U^0_{b^\circ,\sigma}$.  A **$b^\circ$-labelled PEL degeneration over a normal excellent pair**
$(S,D)$ means a proper flat Mumford model with an open semiabelian group locus, whose
restriction to $S\setminus D$ is an abelian scheme in the corrected Hilbert--Blumenthal
functor, and whose totally toric part is identified with

$$
[I_b\xrightarrow{u_Q}T_b].
\tag{13.28b}
$$

The identification includes the ordered polarization, the corrected auxiliary level in the
one-motive sense, the periodic polyhedral model, and the cusp label.  Its monodromy is required
to lie in $\sigma$.  Arrows preserve every one of these data; in particular this is a groupoid
of degenerating objects, not the set of maps to the standalone toric scheme (13.28a).

> **Required Theorem 13.2B.3a (relative Mumford--PEL cusp equivalence;
> $(\mathrm{MPE})_{b^\circ}$).**  For every $b^\circ$ and $\sigma$, on normal excellent schemes complete
> along $D$, the Mumford construction applied to the one-motive (13.28b) is an equivalence
> between positive $b^\circ$-labelled one-motives with monodromy in $\sigma$ and
> $b^\circ$-labelled PEL degenerations.  It is fully faithful, commutes with base change within
> this category and with passage to normalization, and identifies the deformation functor at
> every boundary orbit with the completion of
> $U^0_{b^\circ,\sigma}$ there.

This is the exact first absent theorem.  Theorem 8.1 proves the forward construction for one
completed tensor-ray chart and proves its period-direction Kodaira--Spencer calculation.  It
does not recover an arbitrary degeneration from its one-motive, prove full faithfulness in
families, or prove the asserted equivalence uniformly over every cusp and cone.

Even after $(\mathrm{MPE})_{b^\circ}$, the following algebraic-effectivity ledger must be
discharged; call its conjunction $(\mathrm{ACE})_{b^\circ}$.

1. The formal equivalence is effective algebraically: there is a finite-presentation algebraic
   cusp embedding $\mathcal C^0_{b^\circ,\sigma}$ carrying the universal degeneration, and its
   completion along the indicated orbit is the corresponding completion of
   $U^0_{b^\circ,\sigma}$.  On the puncture the universal object is abelian and its classifying map
   lands in the corrected fine interior.
2. Two punctured cusp objects are isomorphic precisely through a face localization, an
   arithmetic change of cusp label, and the action of the corresponding cusp stabilizer
   $\Gamma_b^\circ$; there are no additional arrows.  Every generic PEL object over a trait
   acquires semiabelian reduction after a finite Galois extension.  On such an extension it has
   a unique such cusp label and positive monodromy vector.  The conjugate extensions agree on
   the common faces of their cones and carry effective descent to the original trait.  These
   assertions commute with the coefficient-field descent action.
3. The automorphy factors from the periodic theta construction are algebraic on
   $\mathcal C^0_{b^\circ,\sigma}$, agree under the identifications in item 2, and turn an integral
   strictly convex support function into a relatively ample boundary line.  They agree on the
   puncture with a fixed positive power of a chosen descent-stable global ample moduli line on
   the fine interior.  On the proper gluing supplied by items 1--2, a common positive tensor
   combination of these two lines is ample.

None of these three statements follows formally from $(\mathrm{MPE})_{b^\circ}$: in particular,
Book 58 cannot algebraize one nonproper formal cusp chart before the proper formal moduli base
and its ample line have been constructed.  They are placed after $(\mathrm{MPE})_{b^\circ}$ because
the source audit stops at the first missing theorem rather than pretending that its later
consequences have been proved.

Assuming $(\mathrm{MPE})_{b^\circ}+(\mathrm{ACE})_{b^\circ}$, the unframed quotient is no
longer mysterious.  Glue the $\mathcal C^0_{b^\circ,\sigma}$ by face localizations and then by
the exact change-of-cusp arrows of item 2 of $(\mathrm{ACE})_{b^\circ}$.  Local finiteness and
the finite number of $\Gamma_b^\circ$-orbits give a finite atlas by choosing finite affine
covers on orbit representatives; the no-inversions and
nonzero-cone stabilizer conclusion of Lemma 13.2B.2 makes the boundary quotient a scheme rather
than a residual stack, while the corrected fine neat level gives the same conclusion on the
interior.  The same exact-overlap assertion identifies its
puncture with an open of the corrected fine interior, so ordinary scheme gluing attaches that
interior.  A common-face calculation proves separatedness.  For a DVR, item 2
of $(\mathrm{ACE})_{b^\circ}$
produces its monodromy vector after a finite Galois semistable extension, and completeness of
$\Sigma_b$ puts that vector in a cone.  The toric valuative criterion gives an extension
there; the common-face compatibility and effective descent in that item return it to the original
DVR, while the same common-face calculation gives uniqueness.  Thus the glued
unframed scheme is proper.  The last sentence of item 3 of $(\mathrm{ACE})_{b^\circ}$ and the
support functions of Lemma 13.2B.2 give an ample line on the whole glued scheme; Book 8 then
identifies the resulting proper morphism as projective.  This paragraph is a deduction from
$(\mathrm{MPE})_{b^\circ}+(\mathrm{ACE})_{b^\circ}$; it is not a proof of either input.

We now state the framed output with the fan included in its hypotheses.

**Required Theorem 13.2B.3 (fan-dependent framed toroidal gluing and algebraization;
$(\mathrm{TCG})_\Sigma$).**  Let the corrected fine component and its two paired-frame cover be
split over a finite coefficient extension, and let
$\Sigma=(\Sigma_b)_b$ be the $\Delta$-equivariant collection furnished by Lemma 13.2B.2 for the
normalized lattices $\mathfrak M_b^{\mathrm{fr}}$.  The following objects and comparisons must
be constructed.

1. For every $(b,\sigma)$, construct the algebraic cusp embedding or toroidal modification of
   the **degenerating PEL moduli problem** associated with $\sigma$, not merely the standalone
   toric scheme
   $$
   \operatorname{Spec}R'[\sigma^\vee\cap\mathfrak M_b^{\mathrm{fr}}].
   \tag{13.29}
   $$
   These cusp embeddings must be compatible under face localization, change of cusp label,
   $\Gamma_b$, and $\Delta$, and their punctured degenerating loci must be identified with the
   corresponding locus of the framed abelian interior.  The universal boundary object must be
   the one-motive (13.22) with its ordered polarization, corrected auxiliary level, and both
   paired frames; its projective Mumford model must be compatible on every overlap.

2. Glue those algebraic cusp embeddings to the good interior to obtain a separated
   finite-presentation model $\overline{\mathcal Y}'_\Sigma$.  Prove, rather than infer from a
   chosen projective closure, that for every point $x$ on the orbit belonging to
   $(b,\sigma)$ there is a canonical completed-local comparison
   $$
   \widehat{\mathcal O}_{\overline{\mathcal Y}'_\Sigma,x}
   \simeq
   \widehat{
     \bigl(R'[\sigma^\vee\cap\mathfrak M_b^{\mathrm{fr}}]\bigr)_{\mathfrak p_x}
   },
   \tag{13.30}
   $$
   with the evident face and cusp identifications, and that the completed universal object is
   the normalized Mumford object of Lemma 13.2B.1.  In particular, normalization in the
   division monomials must occur before completion.  The boundary must be exhausted by these
   charts.  Completeness of $\Sigma$ must imply properness, and regularity for
   $N_b^{\mathrm{fr}}$ must imply smoothness.

3. Construct from the support functions $h_b$ and the compatible periodic theta data a line
   bundle $\mathcal L_\Sigma$ on the glued model.  Prove that its formal restrictions are the
   Mumford theta bundles, that a positive power is relatively ample, and that its generic
   restriction is a global ample bundle available to Book 154.  This is an algebraization and
   positivity assertion on the **moduli base**; algebraization of the projective Mumford family
   over one already complete ring does not imply it.

4. Extend the corrected-source and paired-frame descent cocycle to the cusp embeddings, the
   glued model, the universal boundary objects, and a linearization of a common positive power
   of $\mathcal L_\Sigma$.  Prove effective descent both over the global coefficient field and
   over the unramified local splitting extension $R'/R$, with compatible generic fibers.  The
   descended output must be one projective global compactification and one smooth projective
   $R$-model containing $\mathcal Y^{\mathrm{good}}$, with the selected tensor-ray section
   meeting its prescribed normalized branch without enlarging the completion field or changing
   its valuation, Kummer, enhanced-line, sign, or frame data.

This is the exact fan-dependent theorem needed for $(\mathrm{FTJ})$.  The word “construct” in
item 1 is load-bearing.  The monoid schemes (13.29) and the formal Mumford families do not come
with algebraic maps to a common compactified moduli base.  Nor does a schematic closure in a
Hilbert scheme choose the fan $\Sigma$ or force (13.30): matching tangent dimensions, recording
structure graphs, and normalizing the closure do not prove that its completed local rings are
the prescribed monoid completions or that its boundary equivalence relation is exhausted by
face and cusp identifications.  Book 58 algebraizes a proper formal scheme over a fixed
complete base only after that formal scheme and an ample formal bundle are supplied; it does
not create the missing compactified base.  Thus Lemmas 13.2B.1--13.2B.2 do not prove Required
Theorem 13.2B.3, and no permitted earlier source has been shown here to prove it.

The framing and twisting steps themselves can nevertheless be removed from the missing-input
list.

**Proposition 13.2B.3b (normalization and twisting reduce the framed theorem to the unframed
cusp package).**  Suppose Required Theorem 13.2B.3a and the ledger $(\mathrm{ACE})$ are
supplied for the corrected unframed component, compatibly for the global split coefficient
base and the unramified local base $R'/R$.  Then Required Theorem 13.2B.3 holds for the
two-prime twist and the fans of Lemma 13.2B.2.  In particular, adjoining the paired frames,
regularizing for their refined lattices, and descending the arithmetic twist require no
further compactification theorem.

**Proof.**  First work over the split base.  Use the same rational cones $\sigma$ in the
unframed lattices $\mathfrak M_b^0$; after one common positive multiple, the support functions
of Lemma 13.2B.2 are integral there as well.  Because the fan collection is invariant under
the frame deck groups contained in $\Delta$, forgetting the frame label gives one well-defined
fan at each unframed cusp, rather than competing decompositions there.  Required Theorem
13.2B.3a, $(\mathrm{ACE})$, and the preceding gluing paragraph give a projective normal
unframed toroidal model

$$
\overline{\mathcal H}^{\,0}_\Sigma
\tag{13.30a}
$$

whose completed $b,\sigma$-chart is the completion of
$S'[\sigma^\vee\cap\mathfrak M_b^0]$ and whose completed universal object is (13.22) without
the two additional frames.  Here normality is not an extra hypothesis: the interior is smooth,
the boundary completions are completions of normal saturated monoid algebras, and normality
descends from those completions for the excellent finite-presentation local rings in question.

Let $\mathcal Y'$ be the split paired-frame cover of the interior and define

$$
\overline{\mathcal Y}'_\Sigma
=\operatorname{Norm}_{\mathcal Y'}
  \bigl(\overline{\mathcal H}^{\,0}_\Sigma\bigr),
\tag{13.30b}
$$

the normalization in the finite product of branch function fields of $\mathcal Y'$.  The base
and (13.30a) are excellent, so this normalization is finite.  It is therefore projective and
proper over the coefficient base, and its restriction to the interior is exactly
$\mathcal Y'$ rather than an extra cover, since the latter is finite etale and hence normal
over the normal interior.  Write
$\nu:\overline{\mathcal Y}'_\Sigma\to\overline{\mathcal H}^{\,0}_\Sigma$ for this finite map.
This is normalization of the toroidal moduli model constructed from the cusp embeddings, not
normalization of a schematic Hilbert closure.

Fix a branch over the $b,\sigma$-orbit.  Excellence makes finite normalization commute with
completion, and Lemma 13.2B.1 computes that normalization before completion.  Hence

$$
\widehat{\mathcal O}_{\overline{\mathcal Y}'_\Sigma,x}
\simeq
\widehat{
  \bigl(S'[\sigma^\vee\cap\mathfrak M_b^{\mathrm{fr}}]\bigr)_{\mathfrak p_x}},
\tag{13.30c}
$$

not the normalization of an already completed and possibly unidentified closure.  Face
localizations commute with normalization.  A change of cusp or frame branch acts on the
generic branch field and therefore, by the universal property of normalization, extends
uniquely to these charts.  Thus (13.30c) has exactly the face, $\Gamma_b$, and $\Delta$
compatibilities asserted in (13.30), and the inverse image of the unframed boundary exhausts
the framed boundary.  Concretely, let
$\mathcal C^{\mathrm{fr}}_{b,\sigma}$ be the normalization of
$\mathcal C^0_{b^\circ,\sigma}$ in the restricted generic frame cover, equipped with the
distinguished boundary orbit labelled by $b$.  These normalized embeddings, rather than the
bare monoid spectra, are the charts of (13.30b).

The pulled-back Mumford model carries the generic division points.  In (13.30c) their
coordinates are the monomials in $\mathfrak M_b^{\mathrm{fr}}$ from (13.24).  Sequence
(13.23) and Lemma 13.2B.1 therefore extend them uniquely as the selected two paired frames of
the boundary one-motive.  The ordered polarization and corrected auxiliary level were already
present on (13.30a); their pairing identities hold on the dense puncture and hence on the
normal chart.  The periodic Mumford models agree on overlaps because they did unframed and
normalization is functorial.  This proves item 1 and the universal-object part of item 2 of
Required Theorem 13.2B.3.

The interior is smooth.  At a boundary point, (13.30c) is the completed local ring of a toric
chart for a cone regular in $N_b^{\mathrm{fr}}$, hence is formally smooth over the split
coefficient base.  Smoothness for a finite-presentation morphism is detected after faithfully
flat completion, so $\overline{\mathcal Y}'_\Sigma$ is smooth.  Properness was retained under
the finite normalization.  This proves the remaining assertions of item 2.

Let $\mathcal L^0_\Sigma$ be the ample moduli--boundary line furnished by item 3 of
$(\mathrm{ACE})$ and the support functions $h_b$.  Its finite pullback
$\nu^*\mathcal L^0_\Sigma$ is ample.  On every completed chart it is the pullback of the
Mumford theta bundle, hence is the theta bundle for the normalized one-motive.  This proves
item 3 before descent.

It remains to descend, and here no extension theorem across a boundary is needed.  Let
$\mathscr G$ be the finite semilinear Galois descent group; its action is obtained by composing
Galois transport with the prescribed deck transformations, and its image is contained in the
finite symmetry group $\Delta$ used to construct the fans.  Every
element $\delta$ of $\mathscr G$ acts semilinearly on
the generic branch algebra, carries $(b,\sigma)$ to
$(\delta b,\delta\sigma)$, and preserves the unframed compactification by
$(\mathrm{MPE})+(\mathrm{ACE})$.  It therefore acts uniquely on (13.30b).  Uniqueness of
normalization makes the products of these extensions equal to the extension of the product, so
the generic cocycle remains a cocycle on the whole compactification and on its universal boundary
objects: for the latter assertion, full faithfulness in Required Theorem 13.2B.3a extends the
generic isomorphisms of Mumford models uniquely, and uniqueness preserves their triple cocycle.
Replace the ample line, if necessary, by

$$
\mathcal L^{\mathrm{lin}}_\Sigma
=\bigotimes_{\delta\in\Delta}
  \delta^*\nu^*\mathcal L^0_\Sigma.
\tag{13.30d}
$$

Permutation of the factors gives a canonical $\Delta$-linearization, whose restriction is the
required $\mathscr G$-linearization.  This tensor product is ample, and its formal restrictions
are common positive powers of the transported Mumford theta bundles.  On the interior the deck
transformations preserve the underlying unframed moduli polarization, so
$\mathcal L^{\mathrm{lin}}_\Sigma$ restricts to a positive power of the chosen global ample
moduli line, as required for Book 154.  Book 10 now gives
effective descent of the scheme, universal object, and
linearized line both over the global coefficient field and over the finite etale extension
$R'/R$.  Projectivity, properness, and smoothness descend; Book 8 descends ampleness.  Since
normalization and this construction commute with the finite etale base changes under
consideration, and fpqc descent is unique, the generic fiber of the local descent is the base
change of the global compactification.  Over the local base the interior of (13.30b) is the
finite etale good model $\mathcal Y^{\mathrm{good}}_{R'}$, so its descent contains
$\mathcal Y^{\mathrm{good}}$ as the required open.

Finally let $y_{\mathrm{sp}}$ be the selected framed tensor-ray point over the original
completion.  Over $R'$ its valuation map lies on the marked ray, so the monomial valuative
criterion extends it to the corresponding branch of (13.30c).  The division monomials are
the Kummer coordinates already carried by $y_{\mathrm{sp}}$; no new root or field is chosen.
The extension is unique, hence invariant under its existing descent cocycle, and descends to
an $R$-section.  Because its generic point was not changed, neither its valuation and Kummer
shells nor its enhanced line, sign, or two exact frames change.  This proves item 4 and the
proposition. $\square$

Thus the paired-frame cover is not the first unresolved step.  The first unresolved step is
Required Theorem 13.2B.3a: the relative inverse-to-Mumford equivalence.  Books 119 and 120
explicitly leave compactification in the split case outside their scope; Book 58 algebraizes
only an already proper formal scheme equipped with an ample formal line; Books 8 and 10
respectively test positivity and descend objects already constructed.  None supplies
$(\mathrm{MPE})_{b^\circ}$.  The later $(\mathrm{ACE})_{b^\circ}$ clauses therefore have not
even been reached.  Accordingly
Proposition 13.2B.3b is a genuine reduction, but Required Theorem 13.2B.3 and
$(\mathrm{FTJ})$ remain conditional.

**Proposition 13.2B.4 (conditional handoff to the framed joining datum).**  If Required
Theorem 13.2B.3 holds for the collection $\Sigma$ of Lemma 13.2B.2, then items 1--2 of
$(\mathrm{FTJ})_{v,Z}$ hold.  For every proper closed $Z\subset Y$, the resulting model also
satisfies the weaker form of item 3 in which one chooses an arbitrary closed point of the
nonempty good special-fiber complement.  If the extra residue-point condition (13.21) holds in
the assigned good neighborhood, the literal marked-$P$ form of item 3 holds.

**Proof.**  Items 1, 2, and 4 of Required Theorem 13.2B.3 give the global compactification, its
smooth projective $R$-model, the completed normalized branch, and the selected section with its
exact local ledger.  Item 3 gives a relatively ample bundle compatible with the global generic
fiber.  After taking a sufficiently high power it is relatively very ample, and
$$
H^0(\overline{\mathcal Y}_\Sigma,\mathcal L_\Sigma^n)\otimes_R k
=
H^0(\overline Y_{\Sigma,k},\mathcal L_{\Sigma,k}^n).
\tag{13.31}
$$
The module on the left is finite and torsion-free, hence is an $R$-lattice in Book 154's global
coefficient space.

Let $\overline Z$ be the schematic closure of $Z$.  Its ideal is saturated for the
uniformizer.  At the generic point of a special-fiber component, repeated division by the
uniformizer and Krull intersection would otherwise force the generic-fiber ideal to vanish.
Thus $\overline Z$ contains no component of the special fiber.  The descended model is smooth
with geometrically connected generic fiber; its Stein factor is therefore $R$, and its
geometric special fiber is connected and regular, hence integral.  Its good interior is dense,
so
$$
\mathcal Y^{\mathrm{good}}_\kappa\setminus\overline Z_\kappa
\tag{13.32}
$$
is nonempty and contains a closed point.  This is the weaker item 3.  A marked $R$-section
reducing in (13.32) exists only under the additional condition already isolated in
(13.21). $\square$

**Corollary 13.2B.5 (conditional stable slice and packet reduction).**  Assume Required
Theorem 13.2B.3.  Then the weaker stable integral connecting-slice assertion used by Book 154
follows from Proposition 13.2A.3 and Lemmas 13.2A.1--13.2A.2.  If (13.21) is also satisfied,
the literal form of $(\mathrm{ICS})_{v,Z}$ follows.  Under the further repeatability,
flexibility, and realized normal-closure hypotheses of Proposition 13.2A, these assertions
reduce the one-special/all-other-good packet to Book 154, Corollary 5.2E.

This is a conditional reduction, not a proof of $(\mathrm{FTJ})$, $(\mathrm{ICS})$, or the
singleton moving theorem.  The finite-field Bertini argument, DVR slicing, Kummer
normalization, fan construction, repeatable-packet reduction, and normal-sheet preservation
remain available.  Proposition 13.2B.3b also leaves no separate frame-normalization or twist
descent gap.  The missing implication is Required Theorem 13.2B.3, whose first absent premise
is the unframed Mumford--PEL cusp theorem of Required Theorem 13.2B.3a.

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

**Level one is not the tower.**  For a Tate parameter of positive valuation, finite flatness
at level $p^r$ requires $p^r\mid v(q_0)$.  No fixed parameter satisfies this at every level,
and the selected level-$p$ model is ordinary, not local--local.  A characteristic-zero
finite-flat replacement must therefore be a good ordinary interior point.

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

At the coefficient prime, Proposition 8.4A separates residual finite flatness from the full
tower and proves that the selected multiplicative residual model can only have an ordinary
good replacement.  Proposition 8.4B constructs that replacement over $\mathbf Q_p$ by
Serre--Tate theory from a trace-one elliptic curve over $\mathbf F_p$, and Lemma 8.4B.1
constructs that curve from Book 117's ring-class reciprocity and potential-good-reduction
package.  Thus the good ordinary base-field seed is unconditional for $p\geq7$.

Ordinary reduction is open by partial Hasse invariants. Nonordinary reduction is retained on an open residue tube despite being closed in the special fiber. Semistability is retained in the full-dimensional chart by fixed positive valuation shells. Exact torsion representations and both frames are locally constant through finite etale isomorphism schemes, after only the completion extensions explicitly allowed in the datum. Proposition 3.2 and Theorem 12.1 ensure that every intersection is witnessed on the same geometrically connected twist.

Finally, good reduction, ordinary or local--local type, semistability, toric rank, and finite flatness survive finite extension. Splitness can improve, frames need not descend, and valuations rescale. Theorem 13.1 and Corollary 13.2 therefore provide all five nonempty local-open inputs required by simultaneous Moret--Bailly specialization in the unramified odd-prime, monodromy-admissible catalog range.  For an exact singleton mixed packet, Section 13.2A proves the finite-residue relative Bertini and stable complete-intersection steps.  Section 13.2B proves normalization of the paired-frame cusp lattices and constructs a simultaneous regular projective equivariant fan.  Proposition 13.2B.3b further proves that finite normalization, regularity of the refined chart, the corrected-source and paired-frame cocycle, and an ample linearized tensor product descend once the unframed toroidal model exists.  What it does **not** prove is the first unframed step: Required Theorem 13.2B.3a must identify degenerating PEL families with the Mumford one-motive, fully faithfully and uniformly over every cusp and cone.  Only after that theorem comes the separate $(\mathrm{ACE})$ ledger: algebraic effectivity, exact cusp overlaps and trait coverage, and compatible theta positivity.  Required Theorem 13.2B.3, $(\mathrm{FTJ})_{v_0,Z}$, even the weaker stable integral slice used by Book 154, and the singleton moving input therefore remain conditional.  The literal stronger form with a marked $P$ specializing in $W$ additionally requires its separate residue-point condition (13.21). The other qualifications—an externally fixed nonsquare polarization class, a dyadic coefficient prime, an unramified-only frame not realized over an unramified field, or two incompatible prescribed Tate Kummer classes—remain explicit changes of scope.

For a fixed smooth geometrically connected twist, Proposition 9.3 additionally gives
base-field points at all sufficiently large good places.  This uniform statement is designed
for auxiliary Chebotarev certificates; it makes no descent assertion at a prescribed small
place.
