# Jacobians of Modular Curves

## Contents

1. [Why pass from the modular curve to its Jacobian?](#1-why-pass-from-the-modular-curve-to-its-jacobian)
   - [The arithmetic problem](#11-the-arithmetic-problem)
   - [The Jacobian $J_0(N)$](#12-the-jacobian-j_0n)
   - [Abel--Jacobi maps at rational cusps](#13-abel--jacobi-maps-at-rational-cusps)
   - [Changing the base cusp](#14-changing-the-base-cusp)
2. [Hecke operators with their variance visible](#2-hecke-operators-with-their-variance-visible)
   - [The incoming correspondence](#21-the-incoming-correspondence)
   - [Divisors, the Jacobian, and Tate modules](#22-divisors-the-jacobian-and-tate-modules)
   - [Diamonds and differentials](#23-diamonds-and-differentials)
   - [Level operators and Atkin--Lehner involutions](#24-level-operators-and-atkin--lehner-involutions)
3. [Polarization and adjoints](#3-polarization-and-adjoints)
   - [Why an adjoint needs a polarization](#31-why-an-adjoint-needs-a-polarization)
   - [Transpose correspondences](#32-transpose-correspondences)
   - [The Hecke and diamond formulas](#33-the-hecke-and-diamond-formulas)
   - [Consequences for pairings and stable pieces](#34-consequences-for-pairings-and-stable-pieces)
4. [Cuspidal divisor classes](#4-cuspidal-divisor-classes)
   - [Rational and geometric cusps](#41-rational-and-geometric-cusps)
   - [The cuspidal subgroup](#42-the-cuspidal-subgroup)
   - [Modular units and Manin--Drinfeld](#43-modular-units-and-manin--drinfeld)
   - [Hecke action on cusp differences](#44-hecke-action-on-cusp-differences)
5. [The prime-level cuspidal calculation](#5-the-prime-level-cuspidal-calculation)
   - [Why divisibility is not enough](#51-why-divisibility-is-not-enough)
   - [The eta quotient and its divisor](#52-the-eta-quotient-and-its-divisor)
   - [The converse and exact order](#53-the-converse-and-exact-order)
   - [Small primes and examples](#54-small-primes-and-examples)
6. [The Shimura subgroup](#6-the-shimura-subgroup)
   - [Forgetting a generator](#61-forgetting-a-generator)
   - [Descent characters and Cartier duality](#62-descent-characters-and-cartier-duality)
   - [Interaction with the polarization](#63-interaction-with-the-polarization)
   - [What is deliberately postponed](#64-what-is-deliberately-postponed)
7. [Néron models and specialization](#7-néron-models-and-specialization)
   - [The extension problem](#71-the-extension-problem)
   - [Identity component and component group](#72-identity-component-and-component-group)
   - [Extension of Hecke endomorphisms](#73-extension-of-hecke-endomorphisms)
   - [Specializing finite subgroup schemes](#74-specializing-finite-subgroup-schemes)
8. [Good reduction away from the level](#8-good-reduction-away-from-the-level)
   - [The relative Picard scheme](#81-the-relative-picard-scheme)
   - [Torsion and Tate modules at a good prime](#82-torsion-and-tate-modules-at-a-good-prime)
   - [Hecke and Frobenius after reduction](#83-hecke-and-frobenius-after-reduction)
   - [A counterexample at the residue characteristic](#84-a-counterexample-at-the-residue-characteristic)
9. [Semistable reduction at prime level](#9-semistable-reduction-at-prime-level)
   - [The two components and their graph](#91-the-two-components-and-their-graph)
   - [The toric identity component](#92-the-toric-identity-component)
   - [Supersingular divisor lattices](#93-supersingular-divisor-lattices)
   - [The monodromy pairing](#94-the-monodromy-pairing)
10. [The component group at prime level](#10-the-component-group-at-prime-level)
    - [The discriminant of the supersingular lattice](#101-the-discriminant-of-the-supersingular-lattice)
    - [Its order](#102-its-order)
    - [Hecke and Atkin--Lehner action](#103-hecke-and-atkin--lehner-action)
    - [The cuspidal class specializes to a generator](#104-the-cuspidal-class-specializes-to-a-generator)
11. [Reducing the Abel--Jacobi map](#11-reducing-the-abel--jacobi-map)
    - [At a good prime](#111-at-a-good-prime)
    - [At the level prime](#112-at-the-level-prime)
    - [Cusps and components](#113-cusps-and-components)
    - [What specialization can and cannot prove](#114-what-specialization-can-and-cannot-prove)
12. [Hecke-stable subvarieties and quotients](#12-hecke-stable-subvarieties-and-quotients)
    - [From a stable image to an abelian subvariety](#121-from-a-stable-image-to-an-abelian-subvariety)
    - [Quotients and connected kernels](#122-quotients-and-connected-kernels)
    - [Induced polarizations](#123-induced-polarizations)
    - [Saturation and a cautionary example](#124-saturation-and-a-cautionary-example)
13. [Quotients by Hecke ideals](#13-quotients-by-hecke-ideals)
    - [The image ideal and its abelian image](#131-the-image-ideal-and-its-abelian-image)
    - [Connected Hecke quotients](#132-connected-hecke-quotients)
    - [Tate modules and localization](#133-tate-modules-and-localization)
    - [Coefficient rings and eigenspaces](#134-coefficient-rings-and-eigenspaces)
14. [Optimal and winding quotients](#14-optimal-and-winding-quotients)
    - [Abstract quotient data](#141-abstract-quotient-data)
    - [Existence of an optimal representative](#142-existence-of-an-optimal-representative)
    - [The winding construction](#143-the-winding-construction)
    - [Duality between quotients and subvarieties](#144-duality-between-quotients-and-subvarieties)
15. [Finite subgroups, rational torsion, and low levels](#15-finite-subgroups-rational-torsion-and-low-levels)
    - [Finite subgroup schemes versus rational points](#151-finite-subgroup-schemes-versus-rational-points)
    - [Two good primes](#152-two-good-primes)
    - [Vanishing Jacobians](#153-vanishing-jacobians)
    - [Elliptic prime levels](#154-elliptic-prime-levels)
16. [The prime-level arithmetic package](#16-the-prime-level-arithmetic-package)
    - [The package](#161-the-package)
    - [A worked prime-level ledger](#162-a-worked-prime-level-ledger)
    - [Interfaces for later arithmetic](#163-interfaces-for-later-arithmetic)
    - [Conclusion](#164-conclusion)

## 1. Why pass from the modular curve to its Jacobian?

### 1.1 The arithmetic problem

A point of $X_0(N)$ remembers an elliptic curve together with a cyclic subgroup of order $N$. That moduli interpretation makes rational isogenies visible, but the curve itself has no addition law. If two rational points have the same reduction, or if a correspondence sends one point to a sum of several points, there is no intrinsic way to subtract the resulting data on $X_0(N)$.

The Jacobian supplies exactly that missing linearity. A point $x$ on a curve determines a degree-one divisor, and the difference of two points has degree zero. Passing to divisor classes turns subtraction into a group operation and turns a many-valued correspondence into a homomorphism. Properness, reduction, duality, and finite subgroup schemes can then be brought to bear on a problem that began with one rational point.

This passage loses information: two distinct points can have the same Abel--Jacobi image, and a genus-zero curve has trivial Jacobian. Its value is therefore not that it replaces the curve, but that it extracts the part of the curve accessible to abelian methods. The guiding diagram is

$$
X_0(N)(K)\xrightarrow{x\mapsto[x]-[\infty]}
J_0(N)(K)\longrightarrow
\text{reductions, quotients, and finite Hecke modules}.
$$

We shall build every arrow in this diagram and keep track of the choices hidden in it.

### 1.2 The Jacobian $J_0(N)$

Let $X_0(N)$ denote the smooth proper geometrically connected modular curve over $\mathbf Q$. Its Jacobian is

$$
J_0(N)=\operatorname{Pic}^0_{X_0(N)/\mathbf Q}.
$$

For every extension $K/\mathbf Q$, the $K$-points of the Picard scheme are degree-zero geometric line-bundle classes which descend as Picard classes to $K$; if the relevant Brauer obstruction vanishes, they may be represented by line bundles, and then by divisors, defined over $K$. Over an algebraic closure one may simply write

$$
J_0(N)(\overline{\mathbf Q})
=\operatorname{Div}^0(X_0(N)_{\overline{\mathbf Q}})/\operatorname{Prin}(X_0(N)_{\overline{\mathbf Q}}).
$$

The distinction between a rational divisor and a rational divisor class matters. A Galois-invariant geometric class need not possess a Galois-invariant divisor representative. Cuspidal differences avoid this issue when the cusps themselves are rational.

The dimension is the genus of $X_0(N)$. Thus $J_0(N)=0$ at genus zero, while at genus one a rational cusp identifies $X_0(N)$ with its own Jacobian. In higher genus the Abel--Jacobi image is a curve inside a larger abelian variety.

### 1.3 Abel--Jacobi maps at rational cusps

The Jacobian parametrizes degree-zero classes, while a point has degree one. To bridge the mismatch one must choose a degree-one base divisor. Modular curves provide unusually convenient choices: $0$ and $\infty$ are rational cusps of $X_0(N)$ for every $N$.

For a rational cusp $b$, define

$$
\iota_b:X_0(N)\longrightarrow J_0(N),
\qquad x\longmapsto[x]-[b]. \tag{1.1}
$$

This is a morphism over $\mathbf Q$, not merely a rule on closed points. It sends $b$ to the identity. Its importance is the pointed Albanese property: if $A/\mathbf Q$ is an abelian variety and $f:X_0(N)\to A$ satisfies $f(b)=0$, there is a unique homomorphism $F:J_0(N)\to A$ with $f=F\circ\iota_b$.

The proof explains why divisor classes are the right construction. Extend $f$ additively to sufficiently large effective divisors. It is constant on a complete linear system because a projective space admits no nonconstant map to an abelian variety. It therefore descends through a large symmetric power to the Picard variety, and the normalization at $b$ forces the descended map to be a homomorphism.

For genus at least one, $\iota_b$ is injective on geometric points. Indeed, if $[x]-[b]=[y]-[b]$, then $x-y$ is principal. A nonconstant function with divisor $x-y$ would have degree one and identify the curve with $\mathbf P^1$, contrary to positive genus. This argument also shows the exact exception: on a genus-zero modular curve the target is zero and every point has the same image.

### 1.4 Changing the base cusp

Let $b$ and $b'$ be rational cusps. Then

$$
\iota_{b'}(x)=\iota_b(x)+[b]-[b']. \tag{1.2}
$$

Thus changing the basepoint translates the map by a rational point of the Jacobian. It does not alter $J_0(N)$, its origin, its polarization, or any homomorphism induced by a correspondence. It does alter statements about the image of an individual point.

At prime level put

$$
c_p=[0]-[\infty]\in J_0(p)(\mathbf Q). \tag{1.3}
$$

Then $\iota_0=\iota_\infty-c_p$. Since the Atkin--Lehner involution $w_p$ exchanges the two cusps,

$$
w_p\bigl(\iota_\infty(x)\bigr)
=\iota_\infty(w_px)-c_p. \tag{1.4}
$$

Formula (1.4) is a useful warning. An automorphism of the pointed curve would commute with its Abel--Jacobi map. But $w_p$ does not preserve the chosen base cusp, so equivariance holds only after a translation. Later we shall prove that this translation is torsion and compute its exact order.

## 2. Hecke operators with their variance visible

### 2.1 The incoming correspondence

A Hecke operator is not a map of curves: it lists several isogeny-neighbors. Fix a prime $q\nmid N$ and let $Z_q$ classify triples $(E,C_N,D_q)$, where $D_q\subset E[q]$ is cyclic of order $q$. There are two maps

$$
\alpha(E,C_N,D_q)=(E,C_N),
$$

$$
\beta(E,C_N,D_q)
=(E/D_q,(C_N+D_q)/D_q).
$$

We use the incoming convention throughout: $\beta$ is the declared source, $\alpha$ the declared target, and

$$
\boxed{T_q=\alpha_*\beta^*.} \tag{2.1}
$$

Thus $T_q[x]$ is the sum, with ramification and automorphism multiplicities, of the $q+1$ points which admit a cyclic $q$-isogeny *to* $x$. It is not an average. Reversing the two legs gives the transpose correspondence, not a harmless rewriting of (2.1).

The convention is tested on a graph. If $f:X\to Y$ is finite, its graph declared from $X$ to $Y$ acts by $f_*$; its transpose acts by $f^*$. Consequently $f_*f^*=[\deg f]$ on $J_Y$, whereas $f^*f_*$ need not be scalar. Any convention that makes both composites scalar has lost the fiber geometry.

### 2.2 Divisors, the Jacobian, and Tate modules

For a finite correspondence $X\xleftarrow{s}Z\xrightarrow{t}Y$, define

$$
\Gamma_*D=t_*s^*D. \tag{2.2}
$$

Norms carry principal divisors to principal divisors, so (2.2) descends to

$$
\Gamma_J=t_*s^*:J_X\longrightarrow J_Y. \tag{2.3}
$$

It also preserves degree zero: pullback multiplies degree by $\deg s$, while pushforward preserves total degree over the ground field. Applied to (2.1), this constructs $T_q\in\operatorname{End}_{\mathbf Q}(J_0(N))$.

Every endomorphism acts covariantly on torsion and on the covariant Tate module

$$
T_\ell J_0(N)=\varprojlim_mJ_0(N)[\ell^m](\overline{\mathbf Q}).
$$

The Kummer identification

$$
T_\ell J_0(N)\simeq
H^1(X_0(N)_{\overline{\mathbf Q}},\mathbf Z_\ell(1)) \tag{2.4}
$$

intertwines (2.3) with pullback along $s$ followed by trace along $t$. Because the correspondence is defined over $\mathbf Q$, all these actions commute with Galois. The same abstract operator may have different kernels on divisors, $J_0(N)$, and a Tate module; “the Hecke algebra” must therefore mean either an abstract correspondence algebra or its stated image.

### 2.3 Diamonds and differentials

On $X_1(N)$ let the point-map diamond be

$$
\langle a\rangle(E,P)=(E,aP),
\qquad a\in(\mathbf Z/N\mathbf Z)^\times. \tag{2.5}
$$

In the right-translation normalization compatible with (2.1), the central spherical operator is

$$
S_q=\langle q\rangle^{-1}. \tag{2.6}
$$

The inverse in (2.6) records variance: right translation precomposes level, whereas (2.5) multiplies the chosen point. On $X_0(N)$ the usual diamonds are trivial because multiplying a generator does not change its cyclic subgroup. We nevertheless retain (2.6) when discussing $X_1(N)$ or a character quotient; prematurely setting the diamond to one puts inverses on the wrong side of later adjoint formulas.

Invariant differentials are contravariant. Pullback by an Abel--Jacobi map identifies

$$
H^0(J_X,\Omega^1)\simeq H^0(X,\Omega^1).
$$

Under this identification the pullback of $\Gamma_J=t_*s^*$ is

$$
\Gamma_J^*=s_*t^*:H^0(Y,\Omega^1)\longrightarrow H^0(X,\Omega^1), \tag{2.7}
$$

the action of the transpose correspondence. For $X_0(N)$ and $q\nmid N$, the spherical correspondence is symmetric, so (2.7) is the familiar Hecke action on weight-two cusp forms. For level with a diamond character, the central correction in the transpose must remain visible.

### 2.4 Level operators and Atkin--Lehner involutions

If $q\mid N$ exactly once, the oriented level operator $U_q$ has $q$ forward branches. It is not obtained from the $q+1$-branch correspondence by deleting one term, and its transpose is a distinct opposite operator $V_q$. At level $N=p$, the semistable geometry will later show how $U_p$ acts on the torus and component group, but no good-prime quadratic relation is being asserted at $p$.

For an exact divisor $Q\mid N$, the Atkin--Lehner map $w_Q$ sends an isogeny datum to the appropriate quotient and dual datum. It is an involution on $X_0(N)$ and hence on $J_0(N)$. Its graph transpose equals the graph of its inverse, so

$$
w_Q^\dagger=w_Q^{-1}=w_Q. \tag{2.8}
$$

At prime level, $w_p(0)=\infty$ and $w_p(\infty)=0$, whence

$$
w_p(c_p)=-c_p. \tag{2.9}
$$

The distinction among $T_q$, $U_q$, and $w_Q$ is geometric. The first is a spherical many-valued relation away from level, the second is an oriented relation at level, and the third is an actual automorphism. Their degrees, transposes, and integral extensions are correspondingly different.

## 3. Polarization and adjoints

### 3.1 Why an adjoint needs a polarization

The dual of an endomorphism of an abelian variety acts on the dual abelian variety, not on the original one. To speak of an adjoint one needs a self-duality. For a Jacobian, the theta construction supplies the canonical principal polarization

$$
\lambda_N:J_0(N)\xrightarrow{\sim}J_0(N)^\vee. \tag{3.1}
$$

Although a theta divisor requires choices and may move under translation, its associated homomorphism (3.1) is independent of those choices and descends to $\mathbf Q$. For $u\in\operatorname{End}^0(J_0(N))$, define the Rosati adjoint

$$
u^\dagger=\lambda_N^{-1}u^\vee\lambda_N. \tag{3.2}
$$

It reverses products and is involutive. On Tate modules it is characterized by the Weil pairing

$$
e_{\lambda_N}(ux,y)=e_{\lambda_N}(x,u^\dagger y). \tag{3.3}
$$

The adjective “principal” matters: (3.2) is then an integral endomorphism whenever $u$ is, rather than merely a rational one obtained by inverting an isogeny.

### 3.2 Transpose correspondences

The decisive geometric theorem is

$$
(\Gamma^t)_J=(\Gamma_J)^\dagger. \tag{3.4}
$$

**Proof strategy.** Reduce to a correspondence with one normal component. Pullback of line bundles and norm are dual under the Poincaré bundle. Reversing the two legs exchanges those operations, while the theta polarizations identify each Jacobian with its dual.

**Proof.** Write $\Gamma_J=t_*s^*$. Duality of pullback and norm gives $(s^*)^\vee=s_*$ and $(t_*)^\vee=t^*$ after making the canonical Jacobian identifications. Therefore

$$
\lambda_X^{-1}(t_*s^*)^\vee\lambda_Y
=s_*t^*,
$$

which is precisely the pull--push attached to $\Gamma^t$. Linearity treats a correspondence with several components and multiplicities. $\square$

The same proof, read on cohomology, is the projection formula for Poincaré duality. Thus one transpose operation controls theta, Weil, cup-product, and differential adjoints at once.

### 3.3 The Hecke and diamond formulas

For $q\nmid N$, the inverse-double-coset computation gives

$$
T_q^\dagger=S_q^{-1}T_q. \tag{3.5}
$$

Since $S_q=\langle q\rangle^{-1}$ in the point-map convention, this may also be written

$$
T_q^\dagger=\langle q\rangle T_q \tag{3.6}
$$

on $X_1(N)$. On $J_0(N)$ the diamond is trivial, and hence

$$
T_q^\dagger=T_q. \tag{3.7}
$$

For the point-map diamond itself, transpose of its graph is the graph of the inverse automorphism, so

$$
\langle a\rangle^\dagger=\langle a\rangle^{-1}. \tag{3.8}
$$

Atkin--Lehner formula (2.8) gives $w_Q^\dagger=w_Q$. At a level prime, $U_q^\dagger=V_q$; without an additional local identity, one must not replace $V_q$ by $U_q$ or a guessed scalar multiple.

These formulas depend on notation. If diamonds had been defined by $P\mapsto a^{-1}P$, every displayed diamond would invert. What is invariant is the statement that transpose correspondence equals Rosati adjoint.

### 3.4 Consequences for pairings and stable pieces

Suppose a commutative Hecke algebra $\mathbb T$ acting on $J_0(N)$ is stable under Rosati. Then the orthogonal complement of a $\mathbb T$-stable abelian subvariety is again $\mathbb T$-stable. Indeed, if $B\subset J$ and $x$ is orthogonal to $B$, then for $t\in\mathbb T$ and $b\in B$,

$$
e(tx,b)=e(x,t^\dagger b)=1.
$$

This produces complementary factors up to isogeny. It does not produce an integral direct sum: the intersection of a subvariety with its orthogonal complement can be a nontrivial finite group scheme.

On a simultaneous character space of $X_1(N)$, (3.6) pairs a character $\chi$ with its contragredient. A nonreal diamond character need not yield a self-paired two-dimensional piece. On $X_0(N)$ the absence of a diamond correction makes the Hecke operators self-adjoint, but self-adjointness still does not imply that their reductions modulo a prime are diagonalizable.

## 4. Cuspidal divisor classes

### 4.1 Rational and geometric cusps

Let $\operatorname{Cusp}_0(N)$ be the reduced finite cusp scheme of $X_0(N)$. Over $\overline{\mathbf Q}$ its points are the $\Gamma_0(N)$-orbits in $\mathbf P^1(\mathbf Q)$. A representative $a/d$ with $d\mid N$ has residue field

$$
\mathbf Q(\zeta_{h_d}),
\qquad h_d=\gcd(d,N/d). \tag{4.1}
$$

Thus $0$ and $\infty$ are rational for every $N$, and all cusps are rational when $N$ is squarefree. For nonsquarefree $N$, a rational fraction representing a geometric cusp need not define a $\mathbf Q$-rational point. This is why the words “cuspidal divisor” and “rational cuspidal divisor” cannot be interchanged.

Let $\operatorname{Div}^0_{\mathrm{cusp}}$ be the group of geometric degree-zero divisors supported on cusps. Its Galois invariants map to $J_0(N)(\mathbf Q)$, but the image is most cleanly described through the Picard scheme when a divisor class has no invariant divisor representative.

### 4.2 The cuspidal subgroup

The **geometric cuspidal subgroup** is

$$
C_0(N)_{\mathrm{geom}}
=\operatorname{im}\left(
\operatorname{Div}^0_{\mathrm{cusp}}
\longrightarrow J_0(N)(\overline{\mathbf Q})
\right). \tag{4.2}
$$

The **rational cuspidal subgroup** is the subgroup of $J_0(N)(\mathbf Q)$ generated by degree-zero divisors made from rational cusps and Galois traces of geometric cusps. It is contained in the Galois-fixed part of (4.2), but equality is not automatic: taking invariants need not commute with taking a quotient by principal divisors.

At prime level there are exactly two cusps and both are rational, so no ambiguity remains:

$$
C_0(p)=\langle c_p\rangle,
\qquad c_p=[0]-[\infty]. \tag{4.3}
$$

The point of Manin--Drinfeld is that (4.2) is finite. The result is surprising because a general difference of two rational points on a positive-genus curve has infinite order. Modular cusps are special because modular units provide enough principal relations among them.

### 4.3 Modular units and Manin--Drinfeld

A **modular unit** on a modular curve is a nonzero rational function whose zeros and poles are all cuspidal. Its divisor lies in $\operatorname{Div}^0_{\mathrm{cusp}}$. To prove that every cuspidal difference is torsion, it is enough to prove that divisors of modular units form a finite-index sublattice of $\operatorname{Div}^0_{\mathrm{cusp}}$.

We give the construction rather than citing the conclusion. Pass first to a full-level curve $X(M)$ with $M$ divisible by $N$ and $M\ge3$. For every nonzero $a=(a_1,a_2)\in M^{-1}\mathbf Z^2/\mathbf Z^2$, the Siegel unit $g_a$ is defined on the upper half-plane by a convergent product beginning

$$
g_a(\tau)=
-q^{\frac12B_2(a_1)}
e^{\pi i a_2(a_1-1)}
(1-q^{a_1}e^{2\pi ia_2})
\prod_{n\ge1}(1-q^{n+a_1}e^{2\pi ia_2})
(1-q^{n-a_1}e^{-2\pi ia_2}), \tag{4.4}
$$

with $B_2(T)=T^2-T+1/6$. A fixed power, depending only on $M$, removes the multiplier and is a rational function on $X(M)$. Formula (4.4), after applying a matrix carrying a chosen cusp to $\infty$, computes its order at every cusp. The orders are rational multiples of Bernoulli values; after the fixed power they are integers.

Why do these divisors have full rank? If a degree-zero cusp divisor paired to zero with all the Bernoulli order vectors obtained from (4.4), finite Fourier inversion on $(\mathbf Z/M\mathbf Z)^2$ would force every coefficient of the divisor to be equal. Degree zero then forces every coefficient to vanish. Hence the divisors of the powered $g_a$ span

$$
\operatorname{Div}^0_{\mathrm{cusp}}(X(M))\otimes\mathbf Q.
$$

Now use the degeneracy map $\pi:X(M)\to X_0(N)$. Given a degree-zero cusp divisor $D$ downstairs, pull it back. Some positive multiple of $\pi^*D$ is the divisor of a product $u$ of powered Siegel units. Taking the field norm gives a modular unit $\operatorname{Nm}_\pi(u)$ downstairs, and

$$
\operatorname{div}(\operatorname{Nm}_\pi u)
=\pi_*\operatorname{div}(u)
=m\pi_*\pi^*D
=m(\deg\pi)D. \tag{4.5}
$$

Thus a nonzero integer kills the class of every degree-zero cuspidal divisor. Since the cusp set is finite, its image in the Jacobian is a finite group. This proves Manin--Drinfeld. The proof also explains the theorem's shape: full level supplies enough explicit units, and pullback followed by norm transports their principal relations through degeneracy.

### 4.4 Hecke action on cusp differences

Hecke correspondences preserve the cusp locus, so $C_0(N)_{\mathrm{geom}}$ is Hecke stable. At prime level and $q\ne p$, a Tate-parameter calculation with the incoming correspondence gives

$$
T_qc_p=(q+1)c_p. \tag{4.6}
$$

Here multiplicities matter. Above either standard cusp the $q+1$ cyclic subgroups consist of one subgroup in the component direction and $q$ occurrences in the multiplicative direction after accounting for cusp widths; their images yield the same degree-zero difference with total coefficient $q+1$.

At the level prime, in the standard incoming orientation,

$$
U_pc_p=c_p, \tag{4.7}
$$

and (2.9) gives $w_pc_p=-c_p$. These are integral identities on the cyclic subgroup generated by $c_p$. They foreshadow an Eisenstein pattern, but we shall not define or analyze the ideal generated by such relations here. Our present task is geometric: construct the finite module and compute it exactly.

## 5. The prime-level cuspidal calculation

### 5.1 Why divisibility is not enough

Let $p$ be prime and write

$$
n_p=\operatorname{num}\left(\frac{p-1}{12}\right)
=\frac{p-1}{\gcd(p-1,12)}, \tag{5.1}
$$

where $\operatorname{num}(a/b)$ means the positive numerator in lowest terms. We shall prove

$$
\boxed{\operatorname{ord}(c_p)=n_p.} \tag{5.2}
$$

The discriminant quotient $\Delta(p\tau)/\Delta(\tau)$ has divisor $(p-1)([\infty]-[0])$. It therefore proves only that the order divides $p-1$. That is far too weak: at $p=17$ it gives $16$, while the exact order is $4$. Even producing a function with divisor $n_pc_p$ proves only an upper bound. Exactness requires showing that every principal multiple of $c_p$ is divisible by $n_p$.

The denominator $12$ is not accidental. It records the multiplier of the eta function, together with the fact that a weight-zero eta quotient must have trivial rational character. Ignoring the character can incorrectly improve the answer by a factor of two.

### 5.2 The eta quotient and its divisor

Recall

$$
\eta(\tau)=q^{1/24}\prod_{m\ge1}(1-q^m),
\qquad q=e^{2\pi i\tau},
$$

and put

$$
k_p=\frac{24}{\gcd(p-1,12)}. \tag{5.3}
$$

This is the least positive **even** integer $k$ such that $24\mid k(p-1)$. Consider

$$
u_p(\tau)=\left(\frac{\eta(p\tau)}{\eta(\tau)}\right)^{k_p}. \tag{5.4}
$$

The two eta exponents in (5.4) sum to zero, so the weight is zero. The eta transformation law shows that a quotient with exponents $(-k,k)$ is invariant under $\Gamma_0(p)$ precisely when the two congruences

$$
-k+pk\equiv0\pmod {24},
\qquad -pk+k\equiv0\pmod {24} \tag{5.5}
$$

hold and the rational character condition $p^k\in(\mathbf Q^\times)^2$ holds. The congruences say $24\mid k(p-1)$; the character condition says $k$ is even. Thus $k_p$ is minimal, and $u_p$ is a rational modular unit on $X_0(p)$.

At $\infty$, whose local parameter is $q$, the product gives

$$
\operatorname{ord}_\infty(u_p)
=\frac{k_p(p-1)}{24}=n_p. \tag{5.6}
$$

There are only two cusps. Since a rational function has divisor of degree zero and $u_p$ has no zero or pole on the upper half-plane,

$$
\operatorname{div}(u_p)
=n_p([\infty]-[0])=-n_pc_p. \tag{5.7}
$$

One can also check the order at $0$ directly. The width there is $p$, and the transformation $\tau\mapsto-1/(p\tau)$ exchanges the two eta factors; the factor $(-i\tau)^{1/2}$ cancels because the total weight is zero. The remaining power is the negative of (5.6). Equation (5.7) proves $n_pc_p=0$.

### 5.3 The converse and exact order

We now prove that no smaller positive multiple is principal.

There is no hidden field-of-definition issue. If a function over $\overline{\mathbf Q}$ has divisor $m([\infty]-[0])$, then every Galois conjugate differs from it by a nonzero constant. Those constants form a cocycle, and Hilbert's theorem 90 permits a rescaling after which the function is defined over $\mathbf Q$. It is therefore enough to classify rational modular units with this divisor.

**Theorem 5.1.** If a rational function $f$ on $X_0(p)$ satisfies

$$
\operatorname{div}(f)=m([\infty]-[0]),
$$

then $n_p\mid m$.

**Proof strategy.** We use the same Siegel units which proved Manin--Drinfeld, but now retain their transformation characters rather than merely taking a large common power. At full level the orders of Siegel units give a Fourier basis for cusp divisors. Invariance under the Borel subgroup defining $X_0(p)$ leaves one degree-zero direction. The distribution relation identifies that direction with the eta quotient. Trivial descent character then imposes exactly the congruence and parity conditions of (5.5).

**Proof.** Pull $f$ back to $X(p)$. We need the integral, rather than merely rational, form of the Siegel-unit calculation. We record it as a two-cusp descent lemma:

$$
\left\{
f\in\mathbf Q(X_0(p))^\times:
\operatorname{supp}(\operatorname{div}f)\subseteq\{0,\infty\}
\right\}
=
\left\{
C\left(\frac{\eta(p\tau)}{\eta(\tau)}\right)^k:
\begin{array}{c}
C\in\mathbf Q^\times,\quad k\in\mathbf Z,\\
24\mid k(p-1),\\
k\text{ is even}
\end{array}
\right\}. \tag{5.8}
$$

Here is the lattice calculation behind the lemma. Modulo constants, products of the $g_a$ form a lattice whose divisor map is the Bernoulli order matrix from (4.4). Restrict that matrix to divisors constant on the fibers over each of the two $\Gamma_0(p)$ cusps. Integral row subtraction along the unipotent orbits leaves one degree-zero column; no division or averaging is used. The Siegel-unit distribution relation for that column is

$$
\prod_{a=1}^{p-1}g_{(0,a/p)}(\tau)
=C_p\left(\frac{\eta(p\tau)}{\eta(\tau)}\right)^2, \tag{5.9}
$$

where $C_p\ne0$ is a constant. Indeed,

$$
\prod_{a=1}^{p-1}(1-\zeta_p^aX)
=\frac{1-X^p}{1-X},
$$

and applying this with $X=q^n$ to the two factors in every Siegel product gives (5.9); the Bernoulli initial powers give $q^{(p-1)/12}$ on both sides. Thus the surviving integral column is the square of the eta quotient. The only remaining conditions are descent through the deck Borel and triviality of the multiplier. The eta transformation formula gives

$$
24\mid k(p-1),
\qquad
p^k\in(\mathbf Q^\times)^2. \tag{5.10}
$$

The second condition says that $k$ is even. Conversely these two conditions make the eta quotient a rational function on the coarse curve, so the lattice calculation loses neither roots nor an unnoticed finite index. Its order at $\infty$ is

$$
m=\frac{k(p-1)}{24}. \tag{5.11}
$$

The least positive $k$ satisfying (5.10) is $k_p$. Hence $k_p\mid k$, and (5.11) gives $n_p\mid m$. $\square$

Combining the theorem with (5.7) proves (5.2). Notice where exactness entered: the divisor calculation supplied a relation, while the multiplier calculation proved that every relation is a multiple of it.

### 5.4 Small primes and examples

Formula (5.2) includes the small primes as a statement about the smooth proper coarse curve:

| $p$ | $(p-1)/12$ in lowest terms | $n_p$ | conclusion |
|---:|---:|---:|---|
| $2$ | $1/12$ | $1$ | $J_0(2)=0$ and $c_2=0$ |
| $3$ | $1/6$ | $1$ | $J_0(3)=0$ and $c_3=0$ |
| $5$ | $1/3$ | $1$ | $J_0(5)=0$ and $c_5=0$ |
| $7$ | $1/2$ | $1$ | $J_0(7)=0$ and $c_7=0$ |
| $11$ | $5/6$ | $5$ | $c_{11}$ has exact order $5$ |
| $13$ | $1$ | $1$ | $J_0(13)=0$ and $c_{13}=0$ |
| $17$ | $4/3$ | $4$ | $c_{17}$ has exact order $4$ |
| $19$ | $3/2$ | $3$ | $c_{19}$ has exact order $3$ |

The coarse curves at $p=2,3$ have stack stabilizers which make a uniform integral eta argument awkward, but their genus-zero conclusion verifies the formula directly. The eta proof above may safely be read for $p\ge5$; the remaining primes are the displayed direct cases.

The example $p=13$ is instructive. The rational number $(p-1)/12$ is integral, but its numerator is $1$, not $12$. The two cusps on the genus-zero curve are linearly equivalent, so their difference vanishes. Conversely, at $p=11$ the discriminant quotient only gives $10c_{11}=0$, while the eta character calculation cuts the exact answer to $5$.

## 6. The Shimura subgroup

### 6.1 Forgetting a generator

The cyclic subgroup recorded by $X_0(N)$ may have many generators, recorded upstairs by $X_1(N)$. Let

$$
\pi:X_1(N)\longrightarrow X_0(N) \tag{6.1}
$$

be the forgetful map on smooth proper curves. It induces pullback and norm

$$
\pi^*:J_0(N)\longrightarrow J_1(N),
\qquad
\pi_*:J_1(N)\longrightarrow J_0(N), \tag{6.2}
$$

with

$$
\pi_*\pi^*=[\deg\pi]. \tag{6.3}
$$

The **Shimura subgroup** is the finite group scheme

$$
\Sigma(N)=\ker\bigl(\pi^*:J_0(N)\to J_1(N)\bigr). \tag{6.4}
$$

Equation (6.3) proves finiteness: $\Sigma(N)$ is killed by $\deg\pi$. Scheme-theoretic kernel is essential. In residue characteristics dividing its order it can be nonreduced, and its geometric points do not determine it.

Why should a pullback kernel exist at all? A line bundle downstairs can become trivial upstairs because a trivialization acquires a descent character under the deck group. The Shimura subgroup measures precisely that failure of faithful pullback.

### 6.2 Descent characters and Cartier duality

Away from ramification, the deck group is

$$
\Delta_N=(\mathbf Z/N\mathbf Z)^\times/\{\pm1\}. \tag{6.5}
$$

If $L\in\ker\pi^*$ and a trivialization of $\pi^*L$ is chosen, every deck transformation changes it by a scalar. The scalars form a character

$$
\chi_L:\Delta_N\longrightarrow\mathbf G_m. \tag{6.6}
$$

Changing the trivialization does not change $\chi_L$. At a ramified cusp or elliptic point, descent requires $\chi_L$ to be trivial on the corresponding inertia subgroup. Thus there is an injection

$$
\Sigma(N)\hookrightarrow D(\Delta_N), \tag{6.7}
$$

where $D(\Delta_N)$ is the diagonalizable group with character group $\Delta_N$, and the image is cut out by the inertia relations.

Cartier dualizing reverses the arrow. There is a canonical surjection from the constant group scheme attached to $\Delta_N$ onto $\Sigma(N)^D$; its kernel is generated by the inertia subgroups occurring in the compactified cover, together with any relation forced by connected components. In particular, $\Sigma(N)$ is of multiplicative type and $\Sigma(N)^D$ is finite constant over $\mathbf Q$. This is the structural description needed later. It is more accurate than asserting that the full deck-character group always survives: ramification can kill characters.

At prime level this description is exact. Let $p\ge5$ and put $d=(p-1)/2$. The cyclic deck group $\Delta_p$ has order $d$. The compactified cover is unramified at the cusps: the corresponding cusp widths upstairs and downstairs agree. Its inertia is generated by the order-two elliptic stabilizer when $2\mid d$ and the order-three elliptic stabilizer when $3\mid d$. Thus the subgroup generated by all inertia has order $\gcd(d,6)$, and

$$
\Sigma(p)^D\simeq
\Delta_p/\langle\text{inertia}\rangle
\simeq\mathbf Z/n_p\mathbf Z,
\qquad
n_p=\frac d{\gcd(d,6)}
=\operatorname{num}\left(\frac{p-1}{12}\right). \tag{6.8}
$$

Equivalently, as a group scheme over $\mathbf Q$,

$$
\boxed{\Sigma(p)\simeq\mu_{n_p}.} \tag{6.9}
$$

This is an isomorphism of group schemes, not an assertion that all of its points are rational. It also determines only the geometric descent structure; it does not yet determine the Hecke annihilator or the pairing with the cuspidal subgroup.

### 6.3 Interaction with the polarization

The canonical principal polarization identifies the Cartier dual of a finite subgroup of $J_0(N)$ with a finite quotient of $J_0(N)$. Concretely, if $G\subset J=J_0(N)$, the composite

$$
J\xrightarrow{\lambda_N}J^\vee\longrightarrow G^D \tag{6.10}
$$

has kernel $G^\perp$, the orthogonal complement for the Weil pairing. Hence

$$
J/G^\perp\simeq G^D. \tag{6.11}
$$

Applied to $G=\Sigma(N)$, this places the constant Cartier dual of the multiplicative-type Shimura subgroup naturally on the quotient side of the principally polarized Jacobian. At prime level the cuspidal subgroup is constant, while the Shimura subgroup is of multiplicative type; their appearance as opposite objects under duality is therefore natural even before any theorem identifies their precise pairing.

The cover $X_1(N)\to X_0(N)$ is Hecke equivariant away from $N$, so $\Sigma(N)$ is stable under those Hecke operators and diamonds. This stability is formal from (6.4). Determining the exact annihilator in the Hecke algebra is not formal.

### 6.4 What is deliberately postponed

We have defined $\Sigma(N)$, proved its finiteness, described its Cartier dual through deck characters and inertia, and obtained $\Sigma(p)\simeq\mu_{n_p}$ at prime level. We do **not** determine its full Hecke annihilator, identify its pairing or intersection with the cuspidal subgroup, or analyze congruences detected by that intersection. Those are Eisenstein questions.

This boundary is important. Multiplicative type is a geometric descent statement; an assertion that $T_q$ acts as $q+1$ or that a particular ideal annihilates $\Sigma(N)$ is arithmetic information about the Hecke algebra. The former belongs here, the latter requires a separate arithmetic analysis.

## 7. Néron models and specialization

### 7.1 The extension problem

Let $R$ be a discrete valuation ring with fraction field $K$ and residue field $k$, and let $A/K$ be an abelian variety. Even if a proper model of a curve defining $A$ is singular, one wants to extend points and homomorphisms of $A$ across the closed point. An arbitrary proper model is unsuitable because its singular locus destroys the group law.

The Néron model $\mathcal A/R$ is the smooth separated group scheme of finite type with generic fiber $A$ characterized by

$$
\operatorname{Hom}_R(\mathcal Y,\mathcal A)
\simeq\operatorname{Hom}_K(\mathcal Y_K,A) \tag{7.1}
$$

for every smooth $R$-scheme $\mathcal Y$. Taking $\mathcal Y=\operatorname{Spec}R$ gives

$$
\mathcal A(R)=A(K). \tag{7.2}
$$

The model need not be proper. Failure of properness is exactly what permits tori to occur in bad reduction.

For $A=J_0(N)$ we write $\mathcal J/R$. A regular proper model of $X_0(N)$ has a relative degree-zero Picard functor; after removing its nonseparated part and taking the smooth separated quotient, its identity component agrees with $\mathcal J^0$. This gives the bridge from the geometry of the special curve to the Néron model of its Jacobian.

### 7.2 Identity component and component group

The special fiber has an open connected subgroup $\mathcal A_k^0$. The quotient

$$
\Phi_A=\mathcal A_k/\mathcal A_k^0 \tag{7.3}
$$

is a finite étale group scheme, the component group. Over a henselian DVR, reduction gives

$$
A(K)=\mathcal A(R)\longrightarrow\Phi_A(k). \tag{7.4}
$$

Its kernel consists of points whose sections meet the identity component. The map need not be onto for an arbitrary residue field; over a finite field it is onto because torsors under a connected algebraic group have rational points.

If $A$ has semistable reduction, then $\mathcal A_k^0$ is semiabelian:

$$
0\longrightarrow T\longrightarrow\mathcal A_k^0
\longrightarrow B\longrightarrow0, \tag{7.5}
$$

with $T$ a torus and $B$ an abelian variety. Good reduction means $T=0$ and $\Phi_A=0$. Purely toric reduction means $B=0$. A trivial component group does not by itself imply good reduction.

### 7.3 Extension of Hecke endomorphisms

Every $K$-endomorphism $u:A\to A$ extends uniquely to an $R$-endomorphism of the Néron model. Indeed, $\mathcal A$ is smooth, so the generic map $\mathcal A_K\to A$ extends by (7.1); uniqueness makes it a group homomorphism. Consequently every Hecke operator, diamond, and Atkin--Lehner involution of $J_0(N)$ acts on

$$
\mathcal J_k^0,\qquad T,\qquad B,\qquad\Phi_{J_0(N)}. \tag{7.6}
$$

This conclusion does not require the curve correspondence itself to extend flatly. Extending an endomorphism of the generic abelian variety is automatic; computing its special-fiber action from a curve correspondence is not. For that computation one needs a controlled integral correspondence or a description on the dual graph.

Rosati adjoints also extend. When the canonical polarization extends as a polarization of a semiabelian degeneration, its monodromy pairing identifies the special actions of $u$ and $u^\dagger$ as adjoints on the character and cocharacter lattices.

### 7.4 Specializing finite subgroup schemes

Let $G\subset A$ be finite of order prime to $\operatorname{char}k$. When $A$ has good reduction, its schematic closure in the abelian scheme is finite étale; sections then specialize without collision. At semistable reduction the closure can meet the torus or different components, and a subgroup of order divisible by the residue characteristic can acquire connected parts.

For a point $P\in A(K)$ of order $m$ prime to $\operatorname{char}k$, reduction into the smooth special fiber is injective on the cyclic group it generates. If $P$ reduced to zero, it would lie in the formal kernel, on which multiplication by $m$ is an automorphism. Thus $P=0$.

This is the safe specialization principle:

$$
A(K)[m]\hookrightarrow\mathcal A_k(k^s)[m]
\quad\text{when }(m,\operatorname{char}k)=1. \tag{7.7}
$$

It says nothing about residue-characteristic torsion. The failure is genuine rather than technical: a finite flat group such as $\mu_p$ in characteristic $p$ has only one geometric point although it has rank $p$.

## 8. Good reduction away from the level

### 8.1 The relative Picard scheme

Let $q\nmid N$. If also $q\nmid6$, the coarse curve has a smooth proper model $\mathcal X_0(N)/\mathbf Z_q$, and its relative Picard identity component

$$
\operatorname{Pic}^0_{\mathcal X_0(N)/\mathbf Z_q} \tag{8.1}
$$

is an abelian scheme with generic fiber $J_0(N)$ and special fiber $J_{\mathcal X_0(N)_{\mathbf F_q}}$. By uniqueness it is the Néron model. In residue characteristics $2$ and $3$, one instead works on the smooth proper moduli stack or a prime-to-$q$ rigid cover and descends the invariant Picard factor after checking stabilizers; one must not simply call the naive coarse quotient smooth. This gives the same conclusion: $J_0(N)$ has good reduction at every $q\nmid N$.

In the smooth coarse range a rational cusp extends to a section, and the relative divisor $[x]-[b]$ defines a relative Abel--Jacobi map; at $2$ and $3$ one makes the same construction upstairs before descent. Formation of the relative Picard object, the polarization, and prime-to-$q$ torsion commute with base change. At a good prime there is therefore no correction term between the generic Jacobian and the appropriate special Picard factor.

### 8.2 Torsion and Tate modules at a good prime

For $\ell\ne q$, the finite group schemes $\mathcal J[\ell^r]$ are étale over $\mathbf Z_q$, and specialization identifies their geometric generic and special fibers. Passing to inverse limits gives

$$
T_\ell J_0(N)\simeq
T_\ell\mathcal J_{\overline{\mathbf F}_q}. \tag{8.2}
$$

When the smooth coarse model is available, the right side is the Tate module of $J_{\mathcal X_0(N)_{\overline{\mathbf F}_q}}$; in the small-characteristic stack construction it means the descended invariant Picard factor.

Inertia at $q$ acts trivially. Write $J_0(N)(\mathbf F_q)$ here for $\mathcal J_{\mathbf F_q}(\mathbf F_q)$. For rational torsion, (7.7) gives

$$
J_0(N)(\mathbf Q)_{\mathrm{tors}}[q']
\hookrightarrow J_0(N)(\mathbf F_q), \tag{8.3}
$$

where $[q']$ denotes the prime-to-$q$ part.

Over the unramified field $\mathbf Q_q$, the formal logarithm shows more when $q>2$: the kernel of reduction has no torsion. Thus

$$
J_0(N)(\mathbf Q)_{\mathrm{tors}}
\hookrightarrow J_0(N)(\mathbf F_q)
\qquad(q>2,\ q\nmid N). \tag{8.4}
$$

The restriction $q>2$ is not decorative; shallow two-adic formal groups can contain torsion not controlled by the first-order logarithm.

### 8.3 Hecke and Frobenius after reduction

For $r\nmid Nq$, the $T_r$ correspondence extends with finite locally free legs over $\mathbf Z_q$. Norm and pullback commute with base change, so its action specializes to the same incoming pull--push on the special curve. The same holds for diamonds and Atkin--Lehner maps whose integral moduli description is defined at $q$.

Let $F_q$ denote arithmetic Frobenius on the covariant Tate module. In the $\Gamma_0$ case the good-fiber correspondence calculation gives

$$
F_q^2-T_qF_q+q=0 \tag{8.5}
$$

on $T_\ell J_0(N)$ for $\ell\ne q$. This is an operator identity on the whole Tate module; it is not automatically the characteristic polynomial on a chosen piece until that piece is known to have dimension two.

The convention matters. On untwisted first cohomology it is geometric Frobenius which satisfies the displayed Hecke polynomial. The Tate twist in (2.4) converts that statement into (8.5) for arithmetic Frobenius on the covariant Tate module.

### 8.4 A counterexample at the residue characteristic

It is tempting to extend (8.2) to $\ell=q$. That is false. Even for an ordinary elliptic curve with good reduction, the $q$-divisible group of the special fiber has a connected multiplicative part and an étale part. Geometric points see the étale part but not the full connected thickness. Consequently

$$
A[q^r](\overline{\mathbf Q}_q)
\quad\text{and}\quad
\mathcal A_k[q^r](\overline{\mathbf F}_q)
$$

need not have the same point sets, although the finite flat group schemes fit into a meaningful integral theory.

Similarly, a rational point of $q$-power order may reduce to zero over a sufficiently ramified local field. Good reduction alone protects prime-to-$q$ torsion; the stronger rational injection (8.4) uses that the base is the unramified field $\mathbf Q_q$ and $q>2$. These distinctions will matter when two auxiliary good primes are used to bound rational torsion.

## 9. Semistable reduction at prime level

### 9.1 The two components and their graph

Fix a prime $p\ge5$. The semistable moduli stack at $\Gamma_0(p)$-level has two principal components, each a Frobenius twist of the level-one stack. On the coarse curve their normalizations are copies of $X_0(1)\simeq\mathbf P^1$, and they meet over the supersingular classes. To justify local intersection calculations one may pull back to an auxiliary fine prime-to-$p$ level. The components of that auxiliary cover are higher-level curves, not copies of $\mathbf P^1$; after the calculation one descends the relevant invariant lattice to $X_0(p)$. At a lifted crossing the completed local equation is

$$
\widehat{\mathcal O}\simeq
W(\overline{\mathbf F}_p)[[x,y]]/(xy-p). \tag{9.1}
$$

One component parametrizes $\ker F$, the other the Verschiebung direction. The involution $w_p$ exchanges them. If $\sigma$ denotes the permutation of supersingular classes induced by $p$-power Frobenius, then, after orienting every edge from the first component to the second,

$$
w_p(e_s)=-e_{\sigma(s)}.
$$

The minus sign reverses the edge, while $\sigma$ records that quotienting a supersingular curve by Frobenius replaces it by its Frobenius twist. Suppressing $\sigma$ would incorrectly make $w_p$ scalar on the entire character lattice.

The dual graph $\mathcal G_p$ has two vertices $v_0,v_\infty$, one for each component, and one edge $e_s$ for each supersingular isomorphism class $s$. Every edge joins the two vertices. If there are $r$ supersingular classes, then

$$
H_1(\mathcal G_p,\mathbf Z)
=\left\{\sum_sa_se_s:\sum_sa_s=0\right\}, \tag{9.2}
$$

a free group of rank $r-1$. The genus formula is visible here: because both normalized components have genus zero, the genus of the generic curve is $r-1$ after stack weights and exceptional resolutions are correctly included.

On the coarse model, the points $j=0$ and $1728$ can have stabilizers. Rather than pretending that every coarse node has thickness one, define

$$
w_s=\frac{\#\operatorname{Aut}(E_s)}2
\in\{1,2,3}. \tag{9.3}
$$

Usually $w_s=1$; $w_s=2$ at the supersingular class $j=1728$, and $w_s=3$ at $j=0$. These weights contain exactly the quotient information lost when auxiliary rigidification is removed.

The literal minimal regular coarse model can contain short rational chains resolving quotient singularities at these exceptional classes. Such trees do not contribute cycles to the dual graph, but contracting them to weighted edges changes the integral length by $w_s$. All character-lattice and component-group statements below refer either to the rigidified model followed by descent or, equivalently, to this weighted contraction. They do not assert that an unrigidified coarse fiber literally has only two irreducible components in every presentation.

### 9.2 The toric identity component

For a semistable curve, the identity component of the Jacobian's special fiber is an extension of the product of the Jacobians of the normalized components by the graph torus. Here both components are projective lines, so their Jacobians vanish. Consequently $J_0(p)$ has purely toric reduction at $p$:

$$
\mathcal J_{\overline{\mathbf F}_p}^0=T_p. \tag{9.4}
$$

The torus need not split over $\mathbf F_p$; its splitting and Frobenius action remember how the supersingular points are permuted. It does split over a finite unramified extension, and geometrically

$$
X^*(T_p)\simeq H_1(\mathcal G_p,\mathbf Z). \tag{9.5}
$$

This statement follows directly from gluing line bundles. A degree-zero line bundle on the nodal curve pulls back trivially to each normalized $\mathbf P^1$ after its component degrees are fixed. What remains is a nonzero scalar identifying the two fibers over each node. Simultaneous rescaling on the two components removes one common parameter, leaving a torus of dimension $r-1$. A character records an integral product of gluing scalars whose total exponent is zero, exactly (9.2).

The cocharacter lattice is

$$
X_*(T_p)=\operatorname{Hom}(X^*(T_p),\mathbf Z). \tag{9.6}
$$

It is not canonically the same integral lattice as $X^*(T_p)$ until the monodromy pairing is supplied. Confusing characters with cocharacters would erase the component group, which measures the failure of that pairing to be unimodular.

### 9.3 Supersingular divisor lattices

Let $S_p$ be the set of supersingular elliptic-curve classes over $\overline{\mathbf F}_p$ and put

$$
X_p=\operatorname{Div}^0(S_p)
=\left\{\sum_{s\in S_p}a_s[s]:\sum_sa_s=0\right\}. \tag{9.7}
$$

Orient every edge from $v_0$ to $v_\infty$. Then (9.2) identifies $X^*(T_p)$ with $X_p$. Reversing every orientation multiplies this identification by $-1$ but changes neither the pairing nor its cokernel.

Prime-to-$p$ Hecke correspondences act on $S_p$ by supersingular isogenies. With the incoming convention, $T_q[s]$ is the weighted sum of sources of cyclic $q$-isogenies ending at $s$. The automorphism weights make this action adjoint for the pairing below. It preserves degree and hence $X_p$.

This is the meeting point of two geometries. In characteristic zero, $T_q$ is a correspondence on the modular curve. In characteristic $p$, the same integral correspondence becomes an adjacency operator on supersingular vertices. Extension to the Néron model ensures that the resulting action on $X_p$ is the character-lattice action of the original endomorphism.

### 9.4 The monodromy pairing

The canonical polarization gives an injective homomorphism

$$
\mu_p:X^*(T_p)\longrightarrow X_*(T_p) \tag{9.8}
$$

whose associated symmetric form is the monodromy pairing. In the supersingular-divisor normalization it is

$$
\left\langle\sum_sa_s[s],\sum_sb_s[s]\right\rangle
=\sum_sw_sa_sb_s. \tag{9.9}
$$

The coefficient is $w_s$, not $1/w_s$. On a rigidified regular model every lifted edge has length one; passing to the coarse quotient combines an orbit of edges and gives the stabilizer weight (9.3). This derivation fixes the normalization.

The pairing is positive definite on $X_p$. If $x=\sum a_s[s]$ is nonzero, then

$$
\langle x,x\rangle=\sum_sw_sa_s^2>0.
$$

It is usually not perfect. The exact sequence

$$
0\longrightarrow X_p
\xrightarrow{x\mapsto\langle x,-\rangle}
X_p^\vee
\longrightarrow\Phi_p(\overline{\mathbf F}_p)
\longrightarrow0 \tag{9.10}
$$

identifies its discriminant group with the geometric component group of the Néron model. Formula (9.10) is the precise sense in which the component group records monodromy.

## 10. The component group at prime level

### 10.1 The discriminant of the supersingular lattice

Enumerate $S_p=\{s_1,\ldots,s_r\}$ and write $w_i=w_{s_i}$. A basis of $X_p$ is

$$
e_i=[s_i]-[s_r],\qquad1\le i<r.
$$

Its Gram matrix is

$$
G_{ij}=w_i\delta_{ij}+w_r. \tag{10.1}
$$

The matrix determinant lemma gives

$$
\det G
=\left(\prod_{i=1}^rw_i\right)
\left(\sum_{i=1}^r\frac1{w_i}\right). \tag{10.2}
$$

For clarity, factor the diagonal matrix $D=\operatorname{diag}(w_1,\ldots,w_{r-1})$ from $G=D+w_r\mathbf1\mathbf1^t$. Then

$$
\det(G)=\det(D)
\left(1+w_r\mathbf1^tD^{-1}\mathbf1\right),
$$

which simplifies to (10.2). By (9.10), this determinant is $\#\Phi_p(\overline{\mathbf F}_p)$.

### 10.2 Its order

The supersingular mass formula is

$$
\sum_{s\in S_p}\frac1{w_s}=\frac{p-1}{12}. \tag{10.3}
$$

There is at most one weight $3$ term, occurring when $j=0$ is supersingular, and at most one weight $2$ term, occurring when $j=1728$ is supersingular. All other weights are one. Multiplying (10.3) by the product of the exceptional weights clears exactly the reduced denominator of $(p-1)/12$. Therefore (10.2) gives

$$
\boxed{\#\Phi_p(\overline{\mathbf F}_p)
=\operatorname{num}\left(\frac{p-1}{12}\right)=n_p.} \tag{10.4}
$$

When $r\ge2$, the Smith normal form of (10.1) is

$$
\operatorname{diag}(1,\ldots,1,n_p). \tag{10.5}
$$

Indeed, away from the possible weights $2$ and $3$, differences of unit-weight basis vectors produce unit minors of all lower sizes; the remaining exceptional cases are checked by the same row and column subtractions, and $2$ and $3$ are coprime. If $r=1$, the lattice has rank zero and the component group is already trivial. In every case,

$$
\Phi_p(\overline{\mathbf F}_p)\simeq\mathbf Z/n_p\mathbf Z. \tag{10.6}
$$

Equations (10.4)--(10.6) are asserted for the Néron model of $J_0(p)$ with $p\ge5$. They are not unchanged formulas for $p^2$-level, for $J_1(p)$, or for an unrepaired singular coarse surface.

### 10.3 Hecke and Atkin--Lehner action

For every prime $q\ne p$, the integral $T_q$ correspondence acts on the weighted graph and therefore on the cokernel (9.10). Directly counting the two degeneracy maps on component degrees gives

$$
T_q=(q+1)\quad\text{on }\Phi_p. \tag{10.7}
$$

The involution $w_p$ exchanges the two vertices and reverses orientation. On $X_p$ and $X_p^\vee$ its action is negative the Frobenius permutation $\sigma$, not generally scalar $-1$. The vertex-difference class is fixed by $\sigma$ and changes sign when the vertices are exchanged, so the induced action on the cyclic component group is nevertheless scalar:

$$
w_p=-1\quad\text{on }\Phi_p. \tag{10.8}
$$

In the standard incoming level orientation, the special-fiber degeneracy calculation gives

$$
U_p=1\quad\text{on }\Phi_p. \tag{10.9}
$$

These formulas require the standard $\Gamma_0(p)$ integral model and unnormalized operators. A differently oriented $U_p$ is its opposite correspondence and must be recalculated. Nor does (10.9) assert a good-prime Frobenius polynomial at $p$.

The adjoint relation is consistent with monodromy: $T_q$ is self-adjoint on $J_0(p)$ and the scalar $q+1$ is self-adjoint; $w_p$ is a self-adjoint involution; and the actions induced on characters and cocharacters are adjoint for (9.9).

### 10.4 The cuspidal class specializes to a generator

The cusps $0$ and $\infty$ extend to sections of the regular model and meet the smooth loci of the two different principal components. Thus the horizontal divisor $[0]-[\infty]$ has component multidegree $(1,-1)$. Under the graph description of the relative Picard functor, its specialization is the class measuring the difference of the two vertices.

In the basis used for (10.1), elementary row reduction shows that this vertex-difference class has order $\det G=n_p$ in the discriminant group. Therefore

$$
\operatorname{sp}_p(c_p)
\text{ generates }\Phi_p(\overline{\mathbf F}_p). \tag{10.10}
$$

There is a second useful verification. Chapter 5 showed that $c_p$ has order $n_p$, while (10.4) gives the same order for $\Phi_p$. The explicit multidegree calculation shows the specialization is nontrivial in every nontrivial quotient of the cyclic discriminant group; hence it is an isomorphism on the cyclic group it generates:

$$
\langle c_p\rangle\xrightarrow{\sim}
\Phi_p(\overline{\mathbf F}_p). \tag{10.11}
$$

Equality of the two cardinalities alone would not prove (10.11); the component calculation is indispensable.

## 11. Reducing the Abel--Jacobi map

### 11.1 At a good prime

Let $q\nmid N$, choose a rational cusp $b$, and assume a justified smooth proper curve model over $\mathbf Z_q$ has been chosen. This is automatic for the coarse model when $q\nmid6N$; at $2$ and $3$ the same construction is read on a rigid cover and descended only after the stabilizers have been checked. The divisor of two sections defines a morphism

$$
\widetilde\iota_b:\mathcal X_0(N)\longrightarrow\mathcal J,
\qquad x\longmapsto[x]-[b], \tag{11.1}
$$

whose two fibers are the Abel--Jacobi maps of the generic and special curves. Hence for $x\in X_0(N)(\mathbf Q_q)$,

$$
\operatorname{red}(\iota_b(x))
=\widetilde\iota_{\bar b}(\bar x). \tag{11.2}
$$

No smoothness assumption on the section is needed beyond the smoothness of the total family, which is already available at a good prime. If two rational points have distinct Abel--Jacobi reductions, they were distinct upstairs. The converse fails: distinct points may reduce to the same point, and their divisor difference can lie nontrivially in the formal group.

For genus at least one, injectivity of the geometric Abel map gives a useful implication:

$$
\widetilde\iota_{\bar b}(\bar x)=0
\quad\Longrightarrow\quad
\bar x=\bar b. \tag{11.3}
$$

It is false in genus zero, where the special Jacobian is zero.

### 11.2 At the level prime

At $p\mid N$, the curve model is not smooth, so (11.1) does not extend over the singular nodes merely by invoking the Néron property. It does extend from the smooth locus of the regular model, because that locus is a smooth $\mathbf Z_p$-scheme.

A section through a strict semistable local equation $xy=p$ cannot meet the node: if $v(x),v(y)\ge0$ are integral and sum to one, exactly one is zero. Thus every $\mathbf Z_p$-section of a regular semistable model meets its smooth locus. At an exceptional coarse supersingular class, it may meet one of the rational components introduced by resolving a quotient singularity rather than one of the two principal components. The generic Abel--Jacobi point nevertheless has a well-defined reduction in the Néron model.

There are two layers of its reduction:

$$
J_0(p)(\mathbf Q_p)
\longrightarrow\Phi_p(\mathbf F_p),
$$

which records the component, and, after that component is translated to the identity,

$$
\mathcal J_p^0(\mathbf F_p)=T_p(\mathbf F_p),
$$

which records gluing data at the supersingular nodes. Knowing only the first layer is generally insufficient to recover the reduced divisor class.

### 11.3 Cusps and components

Take $b=\infty$. The cusp $\infty$ meets its own principal component, so

$$
\operatorname{sp}_p(\iota_\infty(\infty))=0.
$$

The cusp $0$ meets the other component, and

$$
\operatorname{sp}_p(\iota_\infty(0))
=\operatorname{sp}_p(c_p), \tag{11.4}
$$

the generator of $\Phi_p$. Thus the Abel--Jacobi map distinguishes the two cusps in the component group exactly when $n_p>1$.

For a noncuspidal rational point $x$ with ordinary, nonexceptional reduction, its reduction lies on the Frobenius or Verschiebung principal component according to the connected or étale type of its order-$p$ subgroup. Relative to $\infty$, this determines whether the component-group image of $\iota_\infty(x)$ is $0$ or the vertex-difference class, with the sign fixed by the labeling of the two cusps. At an exceptional supersingular coarse class, one must instead record the position on the resolution chain, or equivalently use the weighted graph; a binary principal-component label is insufficient. In either case the toric coordinate still depends on the actual reduced point, not only on its component.

The Atkin--Lehner relation (1.4) is compatible with reduction: $w_p$ exchanges the components and acts by $-1$ on $\Phi_p$, while subtracting $c_p$ shifts the chosen origin from one cusp component to the other.

### 11.4 What specialization can and cannot prove

Specialization is strongest when combined with a quotient. Suppose $\varphi:J_0(p)\to A$ is a quotient extending to Néron models. If the image of $\iota_\infty(x)$ is known to be torsion or to lie in a controlled finite subgroup, its reductions at good primes constrain it. At $p$, the component image supplies an additional congruence determined by which branch contains $\bar x$.

But three shortcuts are invalid:

- equality in the component group does not imply equality in the Néron special fiber, because points can differ in the torus;
- equality in the special fiber does not imply equality in the generic fiber, because the formal kernel can be nonzero;
- reduction of a $p$-power finite group cannot be read from its geometric special-fiber points.

The productive method is to combine independent pieces: component information at the level prime, injective torsion reduction at auxiliary good primes, and Hecke-stable quotients which discard irrelevant parts of the Jacobian. The following chapters construct those quotients carefully.

## 12. Hecke-stable subvarieties and quotients

### 12.1 From a stable image to an abelian subvariety

Let $J=J_0(N)$ and let $\mathbb T\subset\operatorname{End}(J)$ be a chosen commutative image algebra. If $f:A\to J$ is a homomorphism of abelian varieties, its scheme-theoretic image is connected and proper, hence an abelian subvariety. Thus sums of images of endomorphisms are again abelian subvarieties: for $t_1,\ldots,t_r\in\mathbb T$,

$$
B=\operatorname{im}\left(J^r\to J,
(x_i)\mapsto\sum_it_ix_i\right) \tag{12.1}
$$

is connected.

If $B\subset J$ is $\mathbb T$-stable, every $t\in\mathbb T$ restricts to an endomorphism of $B$ and descends to the quotient $J/B$. Stability must hold scheme-theoretically, not only on rational points. A finite set of rational points can be stable without its Zariski closure being the intended connected factor.

The principal polarization constructs a complement up to isogeny. Let

$$
B^\perp=\ker\left(J\xrightarrow{\lambda_N}J^\vee
\longrightarrow B^\vee\right)^0. \tag{12.2}
$$

Then $B\cap B^\perp$ is finite and addition gives an isogeny

$$
B\times B^\perp\longrightarrow J. \tag{12.3}
$$

If $\mathbb T$ is Rosati stable and $B$ is $\mathbb T$-stable, then $B^\perp$ is also stable. This is the geometric source of Hecke decompositions up to isogeny.

### 12.2 Quotients and connected kernels

For an abelian subvariety $B\subset J$, the fppf quotient

$$
q:J\longrightarrow A=J/B \tag{12.4}
$$

is an abelian variety, and $\ker q=B$ is connected. We call such a quotient **optimal** for the specified quotient factor. The word does not mean that its degree is smallest; a positive-dimensional-kernel quotient is not an isogeny at all. It means that no finite subgroup remains hidden in the kernel after the connected part has been removed.

An arbitrary surjective homomorphism $f:J\to A'$ has kernel $K$ with identity component $K^0$. It factors as

$$
J\longrightarrow J/K^0\longrightarrow A', \tag{12.5}
$$

where the first map has connected kernel and the second is an isogeny. Thus every specified surjection has a canonical optimalization, determined by $K^0$. This does not make an optimal quotient unique from the target isogeny class alone: different quotient subspaces of $J$ can have isogenous targets. Uniqueness requires the rational factor, equivalently the connected kernel, to have been fixed.

At the level of Tate modules, (12.4) gives, for every prime $\ell$ in characteristic zero, an exact sequence

$$
0\longrightarrow T_\ell B
\longrightarrow T_\ell J
\longrightarrow T_\ell A
\longrightarrow0. \tag{12.6}
$$

Thus $T_\ell B$ is saturated in $T_\ell J$. Connectedness of the kernel is exactly what removes a finite lattice cokernel.

### 12.3 Induced polarizations

Restricting the principal polarization of $J$ to $B$ gives

$$
\lambda_B:B\longrightarrow B^\vee. \tag{12.7}
$$

It is a polarization but is rarely principal. Its kernel is $B\cap B^\perp$ with the appropriate scheme structure. On the quotient $A=J/B$, the dual map

$$
q^\vee:A^\vee\hookrightarrow J^\vee\simeq J \tag{12.8}
$$

identifies $A^\vee$ with the annihilator of $B$, whose identity component is $B^\perp$. Hence $A$ is isogenous to $(B^\perp)^\vee$, and the restricted polarization on $B^\perp$ transports to a polarization of $A$ after a finite isogeny.

There is generally no principal polarization on $A$ whose pullback is simply $\lambda_N$. Indeed, $q^*L_A$ is trivial along $B$, whereas an ample theta line bundle on $J$ cannot be. What descends is the appropriate rational polarization or a positive integral multiple after the finite intersection $B\cap B^\perp$ is cleared.

For a Hecke-stable quotient, the descended action and the dual subvariety action are adjoint: if $t_Aq=qt$, then

$$
q^\vee t_A^\vee=t^\vee q^\vee. \tag{12.9}
$$

After the theta identification, $t^\vee$ becomes $t^\dagger$. This is why quotient stability naturally corresponds to adjoint stability of a subvariety.

### 12.4 Saturation and a cautionary example

There are two different objects attached to an ideal $I\subset\mathbb T$:

$$
I(T_\ell J)=\sum_{t\in I}t(T_\ell J),
$$

and

$$
T_\ell(IJ),
\qquad IJ=\sum_{t\in I}t(J). \tag{12.10}
$$

The second is the saturation of the geometric image contributed by $I$; the first can have finite index in it. They agree after tensoring with $\mathbf Q_\ell$, but not necessarily integrally.

The simplest counterexample is $I=(\ell)$ acting on a nonzero abelian variety $J$. Geometrically $[\ell]:J\to J$ is surjective, so $IJ=J$ and $T_\ell(IJ)=T_\ell J$. Algebraically,

$$
I(T_\ell J)=\ell T_\ell J,
$$

which is not saturated. Thus an ideal quotient of a lattice cannot be identified blindly with the Tate module of the corresponding abelian quotient. Connected geometric images and saturated lattices must be formed before reduction.

## 13. Quotients by Hecke ideals

### 13.1 The image ideal and its abelian image

Fix the acting Hecke algebra

$$
\mathbb T=\operatorname{im}\bigl(
\mathbb T^{\mathrm{abs}}\to\operatorname{End}_{\mathbf Q}(J)
\bigr). \tag{13.1}
$$

Using the image algebra makes its action faithful. Let $I\subset\mathbb T$ be an ideal generated by $t_1,\ldots,t_r$. Define

$$
IJ=\operatorname{im}\left(J^r\to J,
(x_i)\mapsto\sum_it_ix_i\right). \tag{13.2}
$$

This does not depend on the chosen generators. It is an abelian subvariety because the source is connected. Since $\mathbb T$ is commutative, $IJ$ is Hecke stable.

The notation $J[I]$ means something different:

$$
J[I]=\bigcap_{t\in I}\ker(t:J\to J). \tag{13.3}
$$

It can have a positive-dimensional identity component and a finite component group. The image $IJ$ is generated by what elements of $I$ hit; the annihilator $J[I]$ consists of what every element kills. Interchanging them reverses the intended quotient.

### 13.2 Connected Hecke quotients

Define the connected Hecke quotient

$$
J_I=J/IJ. \tag{13.4}
$$

Its kernel is connected by construction. If $t,t'\in\mathbb T$ have the same class modulo $I$, their difference maps $J$ into $IJ$, so they induce the same endomorphism of $J_I$. Thus $J_I$ carries a canonical action of

$$
\mathbb T/I\longrightarrow\operatorname{End}(J_I). \tag{13.5}
$$

This map need not be injective; the faithful coefficient ring of the quotient is its image. Likewise $J_I$ may be zero even when $\mathbb T/I$ is nonzero as an abstract ring.

Dualizing (13.4) gives

$$
J_I^\vee\hookrightarrow J^\vee\simeq J. \tag{13.6}
$$

Its image is the connected abelian subvariety annihilated by the adjoint ideal

$$
I^\dagger=\{t^\dagger:t\in I\}. \tag{13.7}
$$

More precisely, it is the identity component of $J[I^\dagger]$. If $I$ is Rosati stable, quotient and subvariety descriptions use the same ideal, but they remain dual objects rather than literally the same embedded variety.

### 13.3 Tate modules and localization

From the exact sequence defining $J_I$,

$$
0\longrightarrow T_\ell(IJ)
\longrightarrow T_\ell J
\longrightarrow T_\ell J_I
\longrightarrow0. \tag{13.8}
$$

After tensoring with $\mathbf Q_\ell$, semisimplicity in the isogeny category gives

$$
V_\ell J_I
\simeq V_\ell J/I(V_\ell J), \tag{13.9}
$$

where $I(V_\ell J)$ is the vector-space span of the images of $I$. Integrally, (13.9) must be replaced by (13.8); Section 12.4 explains the possible saturation gap.

Let $\mathfrak m$ be a maximal ideal of $\mathbb T$ containing a coefficient prime $\ell$. Localization produces the direct local packet

$$
(T_\ell J)_\mathfrak m
=T_\ell J\otimes_{\mathbb T}\mathbb T_\mathfrak m. \tag{13.10}
$$

It retains every characteristic-zero eigensystem passing through $\mathfrak m$, including generalized extensions; it is not the ordinary eigenspace killed by $\mathfrak m$. Localization is exact, so it can be applied to (13.8). But identifying the result with a quotient by $I(T_\ell J)_\mathfrak m$ still requires the relevant image lattice to be saturated.

### 13.4 Coefficient rings and eigenspaces

Suppose a quotient $A$ of $J$ carries a faithful action of an order $\mathcal O$ in a number field $E$. Then

$$
T_\ell A
$$

is a module over $\mathcal O\otimes\mathbf Z_\ell$, and

$$
V_\ell A
$$

is a module over $E\otimes\mathbf Q_\ell$. Decomposing the latter product cuts rational Hecke eigenspaces. These factors are Galois stable because the Hecke and Galois actions commute.

Three freeness statements must not be conflated:

1. $T_\ell A$ is free over $\mathbf Z_\ell$;
2. it is torsion-free over $\mathcal O\otimes\mathbf Z_\ell$;
3. it is free of a specified rank over a local Hecke algebra.

The first is automatic for an abelian variety. The second needs compatibility with the coefficient action and may be checked componentwise. The third is a multiplicity theorem and is not implied by faithfulness. In particular, the existence of a Hecke quotient does not by itself produce a two-dimensional representation over a coefficient field.

## 14. Optimal and winding quotients

### 14.1 Abstract quotient data

Many arithmetic arguments single out a Hecke-stable rational subspace $W\subset H_1(X_0(N)(\mathbf C),\mathbf Q)$ or, dually, a collection of weight-two differentials. The corresponding rational idempotent in the semisimple endomorphism algebra cuts an abelian factor only up to isogeny. To obtain an actual map from the curve one needs an actual quotient

$$
q:J_0(N)\twoheadrightarrow A. \tag{14.1}
$$

Composing with the pointed Abel map gives

$$
X_0(N)\xrightarrow{\iota_\infty}J_0(N)
\xrightarrow{q}A. \tag{14.2}
$$

Changing the base cusp translates (14.2) by the image of a cuspidal torsion point. The homomorphism $q$ is unchanged.

The correct integral representative of the rational factor is the optimal quotient: require $\ker q$ to be connected. Without this condition, one can postcompose by arbitrarily many isogenies, changing finite kernels, polarizations, and integral Tate lattices while preserving the same rational factor.

### 14.2 Existence of an optimal representative

Let $e\in\operatorname{End}^0(J)$ be an idempotent defining the desired quotient isogeny class. Choose an integer $m>0$ with $me\in\operatorname{End}(J)$ and put

$$
B=\operatorname{im}(m(1-e):J\to J). \tag{14.3}
$$

Then $B$ is an abelian subvariety, and

$$
A_e=J/B \tag{14.4}
$$

has connected kernel. On rational Tate modules, $V_\ell A_e=eV_\ell J$. Changing $m$ changes neither $B$ nor the quotient up to unique isomorphism compatible with $J$, because every nonzero multiple of $1-e$ has the same connected image.

This proves existence. Alternatively, begin with any quotient representing the factor and replace its kernel by its identity component as in (12.5). The two constructions agree. If the rational factor is Hecke stable, $B$ is Hecke stable and the Hecke action descends to $A_e$.

### 14.3 The winding construction

The path from $0$ to $\infty$ defines a relative modular symbol. Integration against holomorphic differentials turns it into a rational Hecke-module vector, the **winding element**

$$
e_{\mathrm w}\in H_1(X_0(N)(\mathbf C),\mathbf Q), \tag{14.5}
$$

normalized by

$$
\int_{e_{\mathrm w}}\omega
=-\int_0^{i\infty}\omega. \tag{14.6}
$$

The sign is a convention fixed by the orientation from $0$ to $\infty$. Define its annihilator in the acting Hecke algebra by

$$
I_{\mathrm w}=\{t\in\mathbb T:t e_{\mathrm w}=0\}. \tag{14.7}
$$

The **winding quotient** at this structural level is

$$
J_{\mathrm w}=J_0(N)/I_{\mathrm w}J_0(N). \tag{14.8}
$$

Section 13.1 shows that the denominator is an abelian subvariety, so (14.8) exists and has connected kernel. The action of $\mathbb T/I_{\mathrm w}$ descends. We require no formula here for $I_{\mathrm w}$, no claim about its Eisenstein support, and no rank theorem for $J_{\mathrm w}(\mathbf Q)$. Those are later arithmetic inputs, not part of the construction.

### 14.4 Duality between quotients and subvarieties

Let $q:J\twoheadrightarrow A$ be optimal. Duality gives an injection

$$
q^\vee:A^\vee\hookrightarrow J^\vee,
$$

and the principal polarization turns it into an abelian subvariety

$$
B_A=\lambda_N^{-1}(q^\vee A^\vee)\subset J. \tag{14.9}
$$

Conversely, an abelian subvariety $B\subset J$ gives the optimal quotient $J/B^\perp$, whose dual subvariety is $B$ up to the restriction polarization. These operations exchange quotient and subvariety formulations.

If $q$ is Hecke equivariant, then $B_A$ is stable under the Rosati-adjoint Hecke action. For $J_0(N)$ away from level, $T_q^\dagger=T_q$, so no visible twist occurs. For a diamond-character setting, the adjoint diamond and central factors from Chapter 3 are compulsory.

The finite group $B\cap B^\perp$ measures the failure of the two formulations to split integrally. Rational Tate spaces decompose,

$$
V_\ell J=V_\ell B\oplus V_\ell B^\perp,
$$

but integral Tate lattices can be glued along the torsion of that finite intersection. This is the same saturation issue seen from the polarization side.

## 15. Finite subgroups, rational torsion, and low levels

### 15.1 Finite subgroup schemes versus rational points

A finite subgroup scheme $G\subset J_0(N)$ carries more information than the abstract group $G(\overline{\mathbf Q})$, and much more than $G(\mathbf Q)$. For example, a constant group $\mathbf Z/m\mathbf Z$ has all of its geometric generators visible over a suitable unramified extension, while its Cartier dual $\mu_m$ is multiplicative and has few rational points unless roots of unity are present. The cuspidal subgroup at prime level is generated by a rational point and is constant; the Shimura subgroup is of multiplicative type.

If $G$ is Hecke stable, every $t\in\mathbb T$ acts on its coordinate algebra, its Cartier dual, and its geometric points. These actions determine one another only when the group scheme structure is retained. In characteristic dividing $\#G$, the reduced geometric point set can lose the connected part entirely.

For a rational torsion point $P$, its Zariski closure in a good Néron model is finite flat; if its order is prime to the residue characteristic, the closure is finite étale. At a bad semistable prime, the section can specialize into the torus, a nonidentity component, or both after translation. The component image is a quotient of the cyclic group generated by $P$, not a complete record of it.

### 15.2 Two good primes

Let $A/\mathbf Q$ be an abelian quotient of $J_0(N)$, and let $q,r>2$ be distinct primes not dividing $N$. Good reduction and the unramified formal-group argument give injections

$$
A(\mathbf Q)_{\mathrm{tors}}\hookrightarrow A(\mathbf F_q),
\qquad
A(\mathbf Q)_{\mathrm{tors}}\hookrightarrow A(\mathbf F_r). \tag{15.1}
$$

Consequently

$$
\#A(\mathbf Q)_{\mathrm{tors}}\mid
\gcd\bigl(\#A(\mathbf F_q),\#A(\mathbf F_r)\bigr). \tag{15.2}
$$

More precisely, each finite abelian invariant factor of $A(\mathbf Q)_{\mathrm{tors}}$ embeds into both finite groups. Point counts alone give the order bound (15.2), while group structures can sharpen it.

Over a general number field or at a ramified local place, use the safer prime-to-residue statement. For a prime $\ell$, choose a good place whose residue characteristic is not $\ell$; then the $\ell$-primary rational torsion injects. With two good places $v,w$, one obtains

$$
v_\ell\#A(K)_{\mathrm{tors}}
\le
\begin{cases}
\min(v_\ell\#A(k_v),v_\ell\#A(k_w)),
&\ell\ne\operatorname{char}k_v,\operatorname{char}k_w,\\
v_\ell\#A(k_w),&\ell=\operatorname{char}k_v\ne\operatorname{char}k_w,
\end{cases} \tag{15.3}
$$

and the analogous exchanged bound. Claiming the gcd in this generality without the stronger formal-kernel hypothesis would be unjustified.

For a Hecke quotient, the point counts can be computed from Frobenius on its Tate module:

$$
\#A(\mathbf F_q)=\det(1-F_q\mid V_\ell A),
\qquad\ell\ne q. \tag{15.4}
$$

The good-prime relation (8.5) and the coefficient-ring decomposition then convert Hecke eigenvalues into explicit factors of (15.4), once dimensions and multiplicities have been established.

### 15.3 Vanishing Jacobians

The levels

$$
N=1,2,3,4,5,6,7,8,9,10,12,13,16,18,25 \tag{15.5}
$$

have $X_0(N)$ of genus zero. Therefore

$$
J_0(N)=0. \tag{15.6}
$$

This is a useful counterexample to the slogan that the Jacobian captures rational points. These curves can have rich families of noncuspidal rational points and nontrivial Hecke correspondences, yet every degree-zero divisor class vanishes. Abelian methods begin only when the genus is positive.

At prime level, (15.5) includes $p=2,3,5,7,13$. The cuspidal formula gives $n_p=1$ in exactly these cases. Thus the modular-unit calculation and the geometric vanishing agree, including the apparently exceptional level $13$.

### 15.4 Elliptic prime levels

The curves $X_0(11)$, $X_0(17)$, and $X_0(19)$ have genus one. Choosing $\infty$ as origin identifies each curve with its Jacobian. The other cusp is then a rational torsion point of exact orders

$$
5,\qquad4,\qquad3, \tag{15.7}
$$

respectively. At the level prime, the Néron component group has the same order and the cusp specializes to its generator.

For $N=11$ one may use the model

$$
E:y^2+y=x^3-x^2-10x-20. \tag{15.8}
$$

The point $P=(5,5)$ lies on $E$ and represents the nonzero cusp difference in a suitable pointed identification. The eta calculation proves that $P$ has order $5$. Direct counting gives

$$
\#E(\mathbf F_3)=5,
\qquad
\#E(\mathbf F_5)=5. \tag{15.9}
$$

Both are good primes greater than two. Equations (15.1)--(15.2) show that $E(\mathbf Q)_{\mathrm{tors}}$ has order dividing $5$; since it contains $P$, one obtains

$$
J_0(11)(\mathbf Q)_{\mathrm{tors}}
=\langle c_{11}\rangle\simeq\mathbf Z/5\mathbf Z. \tag{15.10}
$$

This is a complete torsion calculation using only the cuspidal divisor and two reductions. At levels $17$ and $19$, (15.7) proves the existence and exact order of the cuspidal subgroup but does not by itself classify every rational torsion point; such a classification requires additional arithmetic input.

## 16. The prime-level arithmetic package

### 16.1 The package

We collect the conclusions in a form designed for arithmetic use.

**Prime-level Jacobian package.** Let $p\ge5$ be prime, let

$$
J=J_0(p),\qquad
c=[0]-[\infty],\qquad
n=\operatorname{num}\left(\frac{p-1}{12}\right).
$$

Then:

1. $J=\operatorname{Pic}^0(X_0(p))$, with pointed Abel map $\iota_\infty(x)=[x]-[\infty]$ and $\iota_0=\iota_\infty-c$.
2. The incoming Hecke operator at $q\ne p$ is $T_q=\alpha_*\beta^*$, acting compatibly on divisors, $J$, finite torsion, covariant Tate modules, and twisted first cohomology.
3. The canonical principal polarization gives $T_q^\dagger=T_q$, $w_p^\dagger=w_p$, and $U_p^\dagger=V_p$ before any special level relation is imposed.
4. The rational cuspidal subgroup is cyclic and the Shimura subgroup is its multiplicative-type counterpart:

   $$
   C_0(p)=\langle c\rangle\simeq\mathbf Z/n\mathbf Z,
   \qquad
   \Sigma(p)\simeq\mu_n.
   $$

   No assertion about their intersection or Hecke annihilator is included.

5. For $q\ne p$, $T_qc=(q+1)c$; moreover $U_pc=c$ and $w_pc=-c$ in the standard orientation.
6. $J$ has good reduction away from $p$. For $q\nmid p\ell$, arithmetic Frobenius on $T_\ell J$ satisfies

   $$
   F_q^2-T_qF_q+q=0.
   $$

7. At $p$, $J$ has purely toric semistable reduction. Its geometric character lattice is

   $$
   X_p=\operatorname{Div}^0(S_p),
   $$

   with monodromy pairing

   $$
   \langle a,b\rangle=\sum_{s\in S_p}w_sa_sb_s.
   $$

8. The component group is cyclic of order $n$, and specialization maps $c$ to a generator:

   $$
   \langle c\rangle\xrightarrow{\sim}\Phi_p(\overline{\mathbf F}_p).
   $$

9. On $\Phi_p$, $T_q$ acts by $q+1$, $U_p$ by $1$, and $w_p$ by $-1$.
10. Every Hecke-stable abelian subvariety has a connected quotient, every Hecke ideal $I$ defines $J_I=J/IJ$, and the dual of $J_I$ is the subvariety cut out by the Rosati-adjoint ideal. Rational Tate modules realize the expected quotient; integral Tate modules require saturation.

Every hypothesis in this package has a purpose. Prime level makes the special fiber a two-vertex graph; $p\ge5$ avoids the exceptional coarse-stack analysis at $2$ and $3$; the incoming convention fixes $U_p$ and all adjoints; and the word “geometric” on the component group permits the supersingular calculation before descent is discussed.

### 16.2 A worked prime-level ledger

Take $p=17$. Then

$$
n=\operatorname{num}(16/12)=4.
$$

The eta exponent is

$$
k_{17}=24/\gcd(16,12)=6,
$$

and

$$
\operatorname{div}\left(\frac{\eta(17\tau)}{\eta(\tau)}\right)^6
=4([\infty]-[0]).
$$

The two supersingular classes have weights $3$ and $1$: $j=0$ is supersingular because $17\equiv2\pmod3$, while $j=1728$ is not because $17\equiv1\pmod4$. The mass is

$$
\frac13+1=\frac43=\frac{17-1}{12}.
$$

The rank-one lattice $X_{17}$ is generated by $[s_1]-[s_2]$, and its monodromy self-pairing is

$$
3+1=4.
$$

Thus $c_{17}$ has order $4$, $\Phi_{17}\simeq\mathbf Z/4\mathbf Z$, and specialization identifies their generators. For every $q\ne17$,

$$
T_qc_{17}=(q+1)c_{17},
\qquad
T_q=(q+1)\text{ on }\Phi_{17}.
$$

This example displays the same integer four in three forms: an eta multiplier, a weighted graph discriminant, and the order of a rational divisor class. The agreement is structural, not numerology.

### 16.3 Interfaces for later arithmetic

Suppose $x\in X_0(p)(\mathbf Q)$ is a noncuspidal point. The map

$$
x\longmapsto\iota_\infty(x)\in J_0(p)(\mathbf Q) \tag{16.1}
$$

turns the geometric point into an element on which Hecke operators, reduction, and quotient maps can act. At the level prime, the branch containing the reduction of $x$ determines its image in $\Phi_p$ relative to the base cusp. At a good prime, any torsion image specializes injectively. Passing to an optimal or winding quotient retains a specified Hecke packet and preserves a connected kernel.

Thus a later argument may form the composite

$$
X_0(p)\xrightarrow{\iota_\infty}J_0(p)
\twoheadrightarrow J_I \tag{16.2}
$$

and compare its values in several reductions. Duality permits the same construction to be phrased as projection onto a Hecke-stable subvariety. The coefficient ring acts on every Tate module of the quotient, while localization isolates a residual packet without pretending that it is already a single eigenline.

What has not been supplied is equally precise. We have not identified a particular Eisenstein ideal, computed its index, proved multiplicity one at its maximal ideals, or classified rational prime-degree isogenies. The finite cuspidal and Shimura structures, component group, and quotient formalism are now ready for those arguments, but do not prejudge them.

### 16.4 Conclusion

The Jacobian turns the boundary of a modular curve into arithmetic. Choosing a rational cusp makes a point into a degree-zero class; changing the cusp translates by a torsion class whose exact order is visible in the multiplier of a modular unit. Incoming Hecke correspondences then act on that class with the same variance on divisors, Jacobians, Tate modules, and reduction. The theta polarization converts geometric transpose into Rosati adjoint and keeps diamonds and Atkin--Lehner operators on their correct sides.

At a prime level, the bad fiber sharpens rather than destroys this structure. Its two rational components meet along the supersingular locus. Their dual graph is the character lattice of the torus in the Néron identity component, the automorphism weights define the monodromy pairing, and the discriminant of that pairing is the component group. The mass formula turns its order into

$$
\operatorname{num}\left(\frac{p-1}{12}\right),
$$

exactly the order obtained independently from the eta quotient. The cusp difference specializes to a generator, so the characteristic-zero boundary and the characteristic-$p$ component geometry are joined by an isomorphism of finite cyclic groups.

Finally, connected Hecke quotients make this information portable. They retain the required coefficient actions, admit exact Tate-module sequences, possess dual subvariety formulations, and expose the finite saturation errors that an isogeny-only description would conceal. A rational point on $X_0(p)$ can now be sent into a controlled Hecke module, reduced at good and bad primes, and compared with cuspidal and component classes. That is the arithmetic mechanism for which $J_0(p)$ was introduced.
