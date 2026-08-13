# Jacobians and $H^1$ of Curves

## Contents

1. [From divisor classes to a geometric group](#1-from-divisor-classes-to-a-geometric-group)
   - [Standing hypotheses and conventions](#11-standing-hypotheses-and-conventions)
   - [Why the Picard group is not yet enough](#12-why-the-picard-group-is-not-yet-enough)
   - [The route through the book](#13-the-route-through-the-book)
2. [Divisors, line bundles, and degree](#2-divisors-line-bundles-and-degree)
   - [Divisors and principal relations](#21-divisors-and-principal-relations)
   - [From divisors to line bundles](#22-from-divisors-to-line-bundles)
   - [Degree and the components of the Picard group](#23-degree-and-the-components-of-the-picard-group)
   - [Riemann--Roch as the engine](#24-riemann--roch-as-the-engine)
3. [Families and the relative Picard problem](#3-families-and-the-relative-picard-problem)
   - [What a family of line bundles means](#31-what-a-family-of-line-bundles-means)
   - [The scalar ambiguity and rigidification](#32-the-scalar-ambiguity-and-rigidification)
   - [Descent and the Picard functor](#33-descent-and-the-picard-functor)
   - [Points of the Picard scheme versus line bundles](#34-points-of-the-picard-scheme-versus-line-bundles)
4. [Constructing the Picard scheme](#4-constructing-the-picard-scheme)
   - [Symmetric powers and effective divisors](#41-symmetric-powers-and-effective-divisors)
   - [The large-degree Abel map](#42-the-large-degree-abel-map)
   - [Representability and components](#43-representability-and-components)
   - [Tangent spaces and unobstructed deformations](#44-tangent-spaces-and-unobstructed-deformations)
5. [The Jacobian as an abelian variety](#5-the-jacobian-as-an-abelian-variety)
   - [Definition and group structure](#51-definition-and-group-structure)
   - [Smoothness, dimension, and connectedness](#52-smoothness-dimension-and-connectedness)
   - [Properness](#53-properness)
   - [Geometric points and Galois descent](#54-geometric-points-and-galois-descent)
6. [The Abel--Jacobi map and its universal property](#6-the-abel--jacobi-map-and-its-universal-property)
   - [Choosing degree one](#61-choosing-degree-one)
   - [The Albanese universal property](#62-the-albanese-universal-property)
   - [Changing the base divisor](#63-changing-the-base-divisor)
   - [When no degree-one divisor exists](#64-when-no-degree-one-divisor-exists)
7. [First examples](#7-first-examples)
   - [Genus zero](#71-genus-zero)
   - [An elliptic curve is its own Jacobian](#72-an-elliptic-curve-is-its-own-jacobian)
   - [Hyperelliptic divisor classes](#73-hyperelliptic-divisor-classes)
   - [A singular warning](#74-a-singular-warning)
8. [Functoriality for maps of curves](#8-functoriality-for-maps-of-curves)
   - [Pullback and norm](#81-pullback-and-norm)
   - [Variance and the degree formula](#82-variance-and-the-degree-formula)
   - [Divisors and projection formulas](#83-divisors-and-projection-formulas)
   - [Separable and inseparable maps](#84-separable-and-inseparable-maps)
9. [Torsion and Tate modules](#9-torsion-and-tate-modules)
   - [Multiplication and its kernel](#91-multiplication-and-its-kernel)
   - [Prime-to-characteristic torsion](#92-prime-to-characteristic-torsion)
   - [The covariant Tate module](#93-the-covariant-tate-module)
   - [Continuous arithmetic Galois action](#94-continuous-arithmetic-galois-action)
10. [Kummer theory identifies the Tate module](#10-kummer-theory-identifies-the-tate-module)
    - [The finite-level calculation](#101-the-finite-level-calculation)
    - [Compatibility in the tower](#102-compatibility-in-the-tower)
    - [The integral identification](#103-the-integral-identification)
    - [Untwisted and rational formulations](#104-untwisted-and-rational-formulations)
11. [Dual abelian varieties and the Poincaré bundle](#11-dual-abelian-varieties-and-the-poincaré-bundle)
    - [Why a second Picard construction appears](#111-why-a-second-picard-construction-appears)
    - [The normalized Poincaré bundle](#112-the-normalized-poincaré-bundle)
    - [Biduality](#113-biduality)
    - [Homomorphisms from line bundles](#114-homomorphisms-from-line-bundles)
12. [Polarizations and theta](#12-polarizations-and-theta)
    - [Positive self-duality](#121-positive-self-duality)
    - [The theta divisor](#122-the-theta-divisor)
    - [The canonical principal polarization](#123-the-canonical-principal-polarization)
    - [Why the construction is canonical](#124-why-the-construction-is-canonical)
13. [Weil pairings and cup products](#13-weil-pairings-and-cup-products)
    - [The finite Weil pairing](#131-the-finite-weil-pairing)
    - [Comparison with the curve cup product](#132-comparison-with-the-curve-cup-product)
    - [Passage to Tate modules](#133-passage-to-tate-modules)
    - [Signs, twists, and adjoints](#134-signs-twists-and-adjoints)
14. [Algebraic correspondences](#14-algebraic-correspondences)
    - [From a cycle to a homomorphism](#141-from-a-cycle-to-a-homomorphism)
    - [Graphs, transposes, and composition](#142-graphs-transposes-and-composition)
    - [Compatibility with cohomology](#143-compatibility-with-cohomology)
    - [A worked graph correspondence](#144-a-worked-graph-correspondence)
15. [Endomorphisms, Rosati involutions, and isogenies](#15-endomorphisms-rosati-involutions-and-isogenies)
    - [The endomorphism algebra](#151-the-endomorphism-algebra)
    - [Rosati as geometric adjoint](#152-rosati-as-geometric-adjoint)
    - [Isogenies, kernels, and degrees](#153-isogenies-kernels-and-degrees)
    - [Semisimplicity up to isogeny](#154-semisimplicity-up-to-isogeny)
16. [Good reduction and integral families](#16-good-reduction-and-integral-families)
    - [Relative Jacobians over a base](#161-relative-jacobians-over-a-base)
    - [A precise good-reduction statement](#162-a-precise-good-reduction-statement)
    - [Extending maps and correspondences](#163-extending-maps-and-correspondences)
    - [Limits of the integral picture](#164-limits-of-the-integral-picture)
17. [From a geometric correspondence to a Galois representation](#17-from-a-geometric-correspondence-to-a-galois-representation)
    - [The commuting actions](#171-the-commuting-actions)
    - [The modular and Shimura correspondence pattern](#172-the-modular-and-shimura-correspondence-pattern)
    - [Extracting finite-dimensional representations](#173-extracting-finite-dimensional-representations)
    - [Conclusion](#174-conclusion)

## 1. From divisor classes to a geometric group

### 1.1 Standing hypotheses and conventions

Throughout, $C$ is a smooth proper geometrically connected curve of genus $g$ over a field $k$. We fix a separable closure $k^s$, put $\bar k=k^s$, and write

$$
\bar C=C_{k^s},\qquad G_k=\operatorname{Gal}(k^s/k),
$$

and let $G_k$ act arithmetically. Thus over a finite field arithmetic Frobenius acts on roots of unity by $\zeta\mapsto\zeta^q$; geometric Frobenius is its inverse. Cohomology always means étale cohomology when that qualification matters. A prime $\ell$ used for torsion or cohomology is different from $\operatorname{char}k$.

If an argument requires all closed points to be rational, we pass further from $k^s$ to an algebraic closure $\Omega$. The extension $\Omega/k^s$ is purely inseparable. It is a universal homeomorphism on base-changed schemes and therefore changes neither prime-to-characteristic étale cohomology nor the $G_k$-action; geometric properties such as properness, smoothness, dimension, and ampleness may also be checked after this faithfully flat extension. This small distinction matters over an imperfect separably closed field.

Three established bodies of theory are used with their full hypotheses. For smooth proper curves, the relative Picard theorem supplies representability, base change, degree components, the Abel--Jacobi and Albanese constructions, norms, and the canonical theta polarization. The theory of abelian schemes supplies dual abelian varieties, Poincaré bundles, finite flat torsion, isogenies, and Weil pairings. The cohomology of curves supplies Kummer sequences, trace maps, smooth proper base change, Poincaré duality, and the fact that geometric $H^1$ with $\mathbf Z/\ell^m\mathbf Z$-coefficients is free of rank $2g$. We recall the constructions needed to compare these theories, but we do not silently enlarge their hypotheses. In particular, torsion is treated scheme-theoretically until $\ell$ is assumed invertible, and correspondence normalizations are assumed smooth whenever pullback and norm are used through an intermediate curve.

We use a covariant Tate-module convention:

$$
T_\ell A=\varprojlim_m A[\ell^m](k^s),
$$

where the transition map is multiplication by $\ell$. A homomorphism $A\to B$ therefore induces $T_\ell A\to T_\ell B$. This choice is simple, but it forces a visible Tate twist in the comparison with curve cohomology. Our main identification will be

$$
T_\ell J\simeq H^1(\bar C,\mathbf Z_\ell(1)). \tag{1.1}
$$

No twist will be silently absorbed into a dual or into the Galois action.

### 1.2 Why the Picard group is not yet enough

A degree-zero divisor modulo principal divisors looks at first like an adequate invariant. It is an abelian group, it is functorial, and Riemann--Roch shows that it has exactly $g$ geometric parameters. Yet later arithmetic needs more than a group of classes. It needs families of classes varying algebraically, kernels of multiplication as finite schemes, tangent spaces, reduction over valuation rings, and maps induced by cycles. An abstract group cannot remember any of these.

The Jacobian solves this problem by turning degree-zero divisor classes into the points of a smooth proper connected group variety. That change of category is decisive. The finite subgroup $J[n]$ retains infinitesimal information when the characteristic divides $n$; for $n$ prime to the characteristic it becomes a finite étale carrier of Galois action. A divisor correspondence on two curves becomes a homomorphism of their Jacobians, and hence an operator on a finite free $\ell$-adic module.

There is a second reason to work with the variety rather than only its geometric points. Descent is not the assertion that a Galois-invariant divisor class is represented by a line bundle over $k$. Such a class can have a Brauer obstruction. The Picard scheme packages the descended class correctly even when no individual line bundle descends.

### 1.3 The route through the book

We begin with divisors because they make degree, principal relations, and concrete examples transparent. We then allow the curve to be tested by arbitrary base schemes. This reveals the scalar ambiguity in families of line bundles and leads to the relative Picard functor. Symmetric powers and Riemann--Roch give an explicit construction of its components and show that the identity component is an abelian variety of dimension $g$.

After choosing a degree-one divisor, the curve maps to its Jacobian by Abel--Jacobi. Its universal property explains why every map from the curve to an abelian variety factors through $J$. Pullback and norm then translate maps of curves into homomorphisms in opposite directions.

The second half connects geometry to cohomology. Kummer theory identifies finite torsion with $H^1(\mu_n)$ and the Tate module with twisted integral $H^1$. The Poincaré bundle and theta divisor give the canonical principal polarization. Its Weil pairing is the cup-product pairing in geometric clothing. Finally, algebraic correspondences act compatibly on all these objects, producing the finite-dimensional Galois representations that later geometric Hecke operators will control.

## 2. Divisors, line bundles, and degree

### 2.1 Divisors and principal relations

On a smooth curve every closed point has a discrete valuation. A divisor is a finite sum

$$
D=\sum_{x\in C^{(1)}}n_x[x],\qquad n_x\in\mathbf Z.
$$

For $f\in k(C)^\times$, its principal divisor is

$$
\operatorname{div}(f)=\sum_x\operatorname{ord}_x(f)[x].
$$

Properness supplies the product formula

$$
\deg\operatorname{div}(f)=
\sum_x[k(x):k]\operatorname{ord}_x(f)=0. \tag{2.1}
$$

This is the first place where properness matters. On an affine curve a function may have zeros with no visible poles because the poles lie at the missing boundary. The degree of $D$ is

$$
\deg D=\sum_x n_x[k(x):k],
$$

and (2.1) makes degree insensitive to principal modification.

The divisor class group is

$$
\operatorname{Cl}(C)=\operatorname{Div}(C)/\operatorname{Prin}(C).
$$

Smoothness is equally important: it makes all local rings at closed points discrete valuation rings. For a singular curve, Weil divisors and line bundles need not coincide, and the connected Picard object can acquire a linear part rather than being proper.

### 2.2 From divisors to line bundles

To a divisor $D$ associate the invertible subsheaf $\mathcal O_C(D)$ of the constant sheaf $k(C)$ whose local sections $f$ satisfy $\operatorname{div}(f)+D\geq0$. Multiplication by a rational function gives

$$
\mathcal O_C(D)\simeq\mathcal O_C(D+\operatorname{div}(f)).
$$

Conversely, a nonzero rational section of a line bundle $L$ has a divisor $D$ and identifies $L$ with $\mathcal O_C(D)$. Such a rational section exists because the generic fiber of $L$ is one-dimensional over $k(C)$. Hence

$$
\operatorname{Div}(C)/\operatorname{Prin}(C)
\xrightarrow{\sim}\operatorname{Pic}(C), \tag{2.2}
$$

where $\operatorname{Pic}(C)$ denotes isomorphism classes of line bundles under tensor product.

The proof also explains why divisors are useful but not primary in families. Choosing a rational section is harmless over a single integral curve; it cannot generally be made coherently after arbitrary base change. Line bundles descend well, while chosen rational sections do not.

### 2.3 Degree and the components of the Picard group

Equation (2.2) transfers degree to a homomorphism

$$
\deg:\operatorname{Pic}(C)\longrightarrow\mathbf Z.
$$

Its kernel is denoted $\operatorname{Pic}^0(C)$ at the level of actual line bundles. Over a nonclosed field the image need not be all of $\mathbf Z$: the positive generator of the image is the index of the curve. Thus a geometrically connected curve may have no divisor of degree one and no rational point.

After base change to the algebraic closure $\Omega$, every closed point is rational and the degree map is surjective. The geometric fibers

$$
\operatorname{Pic}^d(C_\Omega)=\{[L]:\deg L=d\}
$$

are torsors under $\operatorname{Pic}^0(C_\Omega)$. There is no preferred identification of $\operatorname{Pic}^d$ with $\operatorname{Pic}^0$ until a degree-$d$ class is chosen. This elementary observation will later explain both the basepoint dependence of Abel--Jacobi and the surprising canonicity of the theta polarization.

### 2.4 Riemann--Roch as the engine

For a line bundle $L$ of degree $d$, Riemann--Roch says

$$
h^0(C,L)-h^0(C,\omega_C\otimes L^{-1})=d+1-g. \tag{2.3}
$$

If $d>2g-2$, the second term vanishes, so every such $L$ has exactly $d+1-g$ independent global sections. In particular it has a nonzero section, whose zero divisor is effective of degree $d$. Thus every sufficiently positive line bundle is represented by an effective divisor.

The numerical constancy in (2.3) does more than prove existence. In families it makes the pushforward of a universal high-degree line bundle locally free, and its projectivization parametrizes nonzero sections up to scale. The fiber over $L$ is the complete linear system

$$
|L|\simeq\mathbf P(H^0(C,L)),
$$

of dimension $d-g$. This projective-space fiber is the geometric mechanism behind representability and properness of the Jacobian.

## 3. Families and the relative Picard problem

### 3.1 What a family of line bundles means

Let $T$ be a $k$-scheme and write $C_T=C\times_kT$. A first attempt would assign

$$
T\longmapsto\operatorname{Pic}(C_T).
$$

This does not represent the desired moduli problem. A line bundle pulled back from $T$ is constant along every geometric fiber, yet it changes the class in $\operatorname{Pic}(C_T)$. The fibers cannot detect that change. The correct raw functor is therefore

$$
\underline{\operatorname{Pic}}^{\mathrm{pre}}_{C/k}(T)
=\operatorname{Pic}(C_T)/\operatorname{Pic}(T), \tag{3.1}
$$

where $\operatorname{Pic}(T)$ maps by pullback along $C_T\to T$.

Formula (3.1) captures the intended pointwise equivalence but may fail descent as a presheaf. The relative Picard functor $\operatorname{Pic}_{C/k}$ is its fppf sheafification. The topology is not ornament: line bundles and their isomorphisms descend faithfully flatly, and a class may exist locally on $T$ before it has a global representative.

### 3.2 The scalar ambiguity and rigidification

Suppose first that $C$ has a $k$-rational point $P$. A line bundle $L$ on $C_T$ can be **rigidified at $P$** by an isomorphism

$$
\alpha:(P\times1_T)^*L\xrightarrow{\sim}\mathcal O_T.
$$

Tensoring $L$ with the pullback of a line bundle on $T$ changes its fiber at $P$ by that same line bundle. Rigidification removes precisely this ambiguity. Moreover, an automorphism of a line bundle on a proper geometrically connected fiber is scalar, and the rigidification forces that scalar to be one. The moduli problem has lost its unwanted automorphisms and can carry a universal line bundle normalized along $P\times\operatorname{Pic}_{C/k}$.

Without a rational point one can rigidify along a suitable finite locally free divisor, chosen so that restriction detects scalar automorphisms, or work directly with fppf descent. The answer exists independently of any rigidification, but a universal line bundle on $C\times\operatorname{Pic}_{C/k}$ need not. This distinction will matter when we use the Poincaré bundle: a canonical Poincaré bundle always exists on an abelian variety times its dual, while a universal bundle on $C$ times its Picard scheme may require a normalization or may be obstructed.

### 3.3 Descent and the Picard functor

The group law on $\operatorname{Pic}_{C/k}$ is induced by tensor product; inverse is dualization; the identity is $\mathcal O_C$. Degree is locally constant in flat families and defines open-and-closed subfunctors $\operatorname{Pic}^d_{C/k}$. The degree-zero subfunctor is the component containing the identity after geometric base change.

Why sheafification is essential can be seen over the ground field. A $G_k$-invariant class $[\bar L]\in\operatorname{Pic}(\bar C)$ comes with isomorphisms $\sigma^*\bar L\simeq\bar L$, but choices of these isomorphisms may fail the cocycle condition by scalars. The resulting class in $\operatorname{Br}(k)$ is the obstruction to descending $\bar L$ as an actual line bundle. The fppf Picard functor remembers the descended moduli point even when the representative does not descend.

### 3.4 Points of the Picard scheme versus line bundles

There are consequently three groups that must not be conflated:

$$
\operatorname{Pic}(C),\qquad
\operatorname{Pic}_{C/k}(k),\qquad
\operatorname{Pic}(\bar C)^{G_k}.
$$

The last two agree for the represented Picard functor, while the first maps into them. The low-degree descent sequence contains

$$
0\longrightarrow\operatorname{Pic}(C)\longrightarrow
\operatorname{Pic}(\bar C)^{G_k}
\xrightarrow{\delta}\operatorname{Br}(k)\longrightarrow\operatorname{Br}(C). \tag{3.2}
$$

Thus the image consists exactly of invariant geometric classes with zero Brauer obstruction. If $C$ has a $k$-point, pullback $\operatorname{Br}(k)\to\operatorname{Br}(C)$ is injective, so $\delta=0$ and the distinction disappears. In general it does not.

A Severi--Brauer conic gives the standard warning. Geometrically it is $\mathbf P^1$ and its invariant geometric Picard group is $\mathbf Z$, generated by the geometric class of $\mathcal O(1)$. If the conic is nonsplit, that class need not be represented by a line bundle of degree one over $k$; only a positive multiple descends. Its Jacobian is nevertheless trivial because the degree-zero component is a point.

## 4. Constructing the Picard scheme

### 4.1 Symmetric powers and effective divisors

The symmetric power $C^{(d)}=C^d/S_d$ parametrizes effective relative divisors of degree $d$. For a geometric point,

$$
x_1+\cdots+x_d\longmapsto
\mathcal O_C(x_1+\cdots+x_d)
$$

defines the Abel map

$$
a_d:C^{(d)}\longrightarrow\operatorname{Pic}^d_{C/k}. \tag{4.1}
$$

This is an explicit bridge from a known projective scheme to the desired moduli space. When $C$ is smooth, $C^{(d)}$ is smooth of dimension $d$: locally, the elementary symmetric functions give regular parameters even along diagonals. The source is projective and geometrically connected.

For small $d$, the fibers of $a_d$ jump. A special line bundle can have more sections than a general one. This is not a defect; the jumping loci encode the geometry of special divisors. For construction, however, large degree is better because Riemann--Roch makes every fiber uniform.

### 4.2 The large-degree Abel map

Take $d\geq2g-1$. For every geometric line bundle $L$ of degree $d$, $H^1(C,L)=0$ and $h^0(C,L)=d+1-g$. Formation of global sections commutes with base change in families. At this stage regard $\operatorname{Pic}^d$ as the fppf sheaf, not yet as a scheme. After an fppf cover $T'\to T$, a $T$-valued Picard class is represented by a line bundle $\mathcal L$ on $C_{T'}$. Write $\pi_{T'}:C_{T'}\to T'$. Then

$$
E=(\pi_{T'})_*\mathcal L
$$

is locally free of rank $d+1-g$, and the pullback of the Abel map over this class is the projective bundle $\mathbf P(E)$ parametrizing a section up to scale. Twisting $\mathcal L$ from the base twists $E$ by the same line bundle and leaves $\mathbf P(E)$ unchanged. Thus the construction is independent of the local representative and descends on overlaps.

Consequently $a_d$ is smooth, proper, and surjective, with geometric fibers $\mathbf P^{d-g}$. The calculation predicts the target dimension:

$$
\dim\operatorname{Pic}^d=d-(d-g)=g. \tag{4.2}
$$

It also describes the equivalence relation on effective divisors: two lie in the same fiber exactly when they are linearly equivalent.

### 4.3 Representability and components

We now state the construction theorem in the form used throughout.

**Picard representability theorem.** The fppf sheaf $\operatorname{Pic}_{C/k}$ is represented by a separated scheme locally of finite type over $k$. It is a disjoint union of open-and-closed degree components $\operatorname{Pic}^d_{C/k}$. Each component is smooth of dimension $g$ and is a torsor under the identity component $\operatorname{Pic}^0_{C/k}$.

**Proof strategy.** This is the field case of the relative Picard theorem recalled in Section 1.1. We indicate how its construction specializes, both to identify the resulting points and to record where the nontrivial quotient theorem enters. Use $C^{(d)}$ for $d\geq2g-1$ as a smooth projective presentation of the already defined Picard sheaf. Linear equivalence is represented by the projective-space fibers described above. The relative theorem proves that this fppf quotient is a separated scheme; it is not legitimate to assume a universal bundle on an already represented $\operatorname{Pic}^d$ in order to prove representability. Tensor product and duality then transport the construction from one high-degree component to every degree.

More explicitly, begin on the known scheme $C^{(d)}$. The relation sheaf

$$
R_d=C^{(d)}\times_{\operatorname{Pic}^d}C^{(d)}
$$

records pairs of effective divisors whose rigidified line bundles are isomorphic. The isomorphism functor is represented because rigidification removes scalar stabilizers. In high degree both projections are locally projective-space bundles of constant dimension. Affine invariant neighborhoods give local quotients; uniqueness of rigidified isomorphisms gives their descent cocycle; and properness makes the isomorphism relation closed after scalars have been fixed. These local quotients glue to the separated representing scheme. The same construction identifies the pullback over every local line-bundle representative with $\mathbf P(E)$, so it proves rather than presupposes the description in Section 4.2. This is the nontrivial representability step. The later tangent-space calculation supplies smoothness rather than being used to manufacture the quotient.

The theorem is stronger than a bijection on geometric points. It says that a morphism $T\to\operatorname{Pic}_{C/k}$ is a family of line-bundle classes on $C_T$, with its necessary descent data, and that this statement survives arbitrary extension of the ground field.

### 4.4 Tangent spaces and unobstructed deformations

The geometry of the Picard scheme can also be read infinitesimally. Let $L$ be a line bundle after a separably closed or algebraically closed extension $K/k$, and let $R=K[\varepsilon]/(\varepsilon^2)$. A lift of $L$ to $C_R$ is obtained by changing transition functions $g_{ij}$ to

$$
g_{ij}(1+\varepsilon a_{ij}).
$$

The cocycle condition says that $(a_{ij})$ is a Čech $1$-cocycle in $\mathcal O_{\bar C}$, and changing trivializations adds a coboundary. Hence

$$
T_{[L]}\operatorname{Pic}_{C/k}\simeq H^1(\bar C,\mathcal O_{\bar C}). \tag{4.3}
$$

Obstructions to extending through a square-zero thickening lie in $H^2(\bar C,\mathcal O_{\bar C})$, which vanishes because $\bar C$ is a curve. Thus the Picard scheme is smooth. Serre duality gives

$$
\dim H^1(\bar C,\mathcal O_{\bar C})
=\dim H^0(\bar C,\omega_{\bar C})=g,
$$

recovering (4.2) for a reason that will later echo in $\ell$-adic cohomology.

## 5. The Jacobian as an abelian variety

### 5.1 Definition and group structure

The **Jacobian** of $C$ is

$$
J=\operatorname{Pic}^0_{C/k},
$$

the identity component of the Picard scheme. Tensor product is its addition, dualization its inverse, and $[\mathcal O_C]$ its identity. This definition does not require a rational point or a degree-one divisor.

The notation $\operatorname{Pic}^0$ has two nearby meanings. For the scheme it means the identity component. Over $k^s$, its points are precisely degree-zero line-bundle classes, so

$$
J(k^s)=\operatorname{Pic}^0(\bar C). \tag{5.1}
$$

Over $k$, actual degree-zero line bundles may form a proper subgroup of $J(k)$ because of (3.2).

### 5.2 Smoothness, dimension, and connectedness

By (4.3), $J$ is smooth of dimension $g$. It is geometrically connected by construction: after base change to $k^s$ it is the connected component containing the identity. Since formation of the Picard identity component commutes with separable base change for our smooth proper curve, no new components appear.

This also shows why one cannot define $J$ as the kernel of degree on $k$-points. Connectedness and dimension are geometric properties, invisible in an abstract kernel. The scheme definition retains them and makes $J[n]$ meaningful even when it has few rational points.

### 5.3 Properness

Smooth connected group schemes need not be proper: the additive and multiplicative groups are counterexamples. The missing fact for $J$ comes from complete linear systems.

**Theorem.** The Jacobian $J$ is proper over $k$, hence is an abelian variety of dimension $g$.

**Proof strategy.** First prove properness after extending to the algebraic closure $\Omega$; properness descends. Choose a line bundle $M$ of large degree $d\geq2g-1$. Translation by $M$ identifies $J_\Omega$ with $\operatorname{Pic}^d_{C_\Omega}$. The Abel map $C_\Omega^{(d)}\to\operatorname{Pic}^d_{C_\Omega}$ is a surjective projective bundle. Since the source is proper, the target is proper.

For the last implication, the morphism $C_\Omega^{(d)}\to\operatorname{Spec}\Omega$ is proper and factors through the separated finite-type scheme $\operatorname{Pic}^d_{C_\Omega}$. A surjective proper morphism is universally closed; after any base change, a closed subset of $\operatorname{Pic}^d$ pulls back to a closed subset and its image is closed. Thus $\operatorname{Pic}^d$ is universally closed, separated, and of finite type, hence proper. Translation transfers properness to $J_\Omega$, and faithfully flat descent returns it to $k$.

The proof exposes the role of every hypothesis. Smoothness identifies divisors with line bundles and controls symmetric powers. Properness of $C$ makes $C^{(d)}$ proper. Geometric connectedness gives a single identity component with constant genus.

### 5.4 Geometric points and Galois descent

The equality (5.1) is canonical and $G_k$-equivariant. If $\sigma\in G_k$ and $L$ is a line bundle on $\bar C$, then

$$
\sigma\cdot[L]=[(1_C\times\sigma^{-1})^*L]
$$

under the usual left-action convention; equivalently it is the descent action induced by the $k$-scheme $J$. Writing the inverse explicitly prevents confusion between the action on functions and pullback on geometric objects.

Because $J$ is separated,

$$
J(k)=J(k^s)^{G_k}. \tag{5.2}
$$

Equations (5.1)--(5.2) do **not** say that every element is represented by a degree-zero line bundle on $C$. They say that every invariant geometric moduli point descends as a point of the representing scheme. The further lifting to an actual line bundle is governed by the Brauer obstruction in (3.2). This distinction is one of the principal benefits of having constructed a scheme rather than stopping with divisor classes.

## 6. The Abel--Jacobi map and its universal property

### 6.1 Choosing degree one

The Jacobian parametrizes degree-zero classes, but a point $x$ of the curve naturally determines the degree-one bundle $\mathcal O_C(x)$. To reach degree zero one must choose an origin in the degree-one Picard torsor. Let $D_0$ be a $k$-rational divisor of degree one. It need not be effective and need not be a $k$-rational point. The formula

$$
u_{D_0}:C\longrightarrow J,
\qquad x\longmapsto[\mathcal O_C(x-D_0)] \tag{6.1}
$$

defines a $k$-morphism. In family language, the diagonal in $C\times C$ supplies $\mathcal O(\Delta)$, and tensoring by the pullback of $\mathcal O(-D_0)$ gives a relative degree-zero class. If $D_0=P$ is a rational point, then $u_P(P)=0$.

A degree-one divisor is an exact hypothesis for the displayed divisor formula and for the normalization used below, not a harmless convenience. Curves of positive genus can have index greater than one. The weaker datum actually needed merely to translate the Abel map into $J$ is a point $\xi\in\operatorname{Pic}^1_{C/k}(k)$: translation by $-\xi$ gives

$$
u_\xi:C\longrightarrow\operatorname{Pic}^1_{C/k}
\xrightarrow{t_{-\xi}}J. \tag{6.2}
$$

Such a Picard-scheme point need not be represented by a degree-one line bundle on $C$, because it may have the Brauer obstruction of (3.2). Thus existence of $u_\xi$ is controlled by the period torsor $\operatorname{Pic}^1$, whereas existence of $D_0$ is the stronger index-one condition. When $D_0$ exists, its class supplies $\xi$ and (6.2) is (6.1).

### 6.2 The Albanese universal property

The importance of $u_{D_0}$ is not that it embeds every curve—it need not in genus zero—but that it is universal for maps to abelian varieties.

For a divisor $D=\sum n_x[x]$ and a morphism $f:C\to A$ to a commutative group variety, define

$$
f_*(D)=\sum_x n_x\operatorname{Tr}_{k(x)/k}(f(x))\in A(k), \tag{6.3}
$$

where the trace means the sum of Galois conjugates after a separable splitting, with the corresponding finite morphism interpretation in general. When $D_0=P$ is rational, (6.3) is simply $f(P)$.

**Albanese theorem.** Let $A$ be an abelian variety and $f:C\to A$ a morphism satisfying $f_*(D_0)=0$. There is a unique homomorphism of abelian varieties $F:J\to A$ such that

$$
f=F\circ u_{D_0}. \tag{6.4}
$$

Without the normalization, every $f$ has a unique expression

$$
f=t_a\circ F\circ u_{D_0},
\qquad a=f_*(D_0), \tag{6.5}
$$

where $t_a$ denotes translation.

**Proof strategy.** Extend the rule on points additively to effective divisors, show that it is constant on complete linear systems, and descend it through a large symmetric power.

Choose $d\geq2g-1$. Addition in $A$ gives a morphism

$$
f^{(d)}:C^{(d)}\longrightarrow A,
\qquad x_1+\cdots+x_d\longmapsto\sum_i f(x_i).
$$

If two effective divisors $E,E'$ are linearly equivalent, they lie in one projective-space fiber $|L|$ of the Abel map. Every morphism from projective space to an abelian variety is constant: restricting to a line reduces to the fact that an abelian variety contains no rational curves. Thus $f^{(d)}$ is constant on the fibers and descends to $\operatorname{Pic}^d$. Translating by $dD_0$ gives $F:J\to A$.

The normalization makes the descended map take $0$ to $0$. A morphism between abelian varieties carrying identity to identity is a homomorphism: compare $F(x+y)$ with $F(x)+F(y)$ and apply the rigidity lemma to their difference on $J\times J$. Equation (6.4) follows on degree-one classes, and uniqueness follows because the classes $u_{D_0}(x)$ generate $J$: every degree-zero divisor is a difference of effective divisors after adding a sufficiently positive divisor.

The universal property turns an apparently arbitrary moduli variety into the natural abelian quotient of the curve. It will later force correspondence actions constructed from divisors to agree with those constructed functorially from maps.

### 6.3 Changing the base divisor

Let $D_1$ be another $k$-rational divisor of degree one. Then

$$
u_{D_1}(x)=u_{D_0}(x)+[D_0-D_1]. \tag{6.6}
$$

Thus changing the base divisor translates the Abel--Jacobi map; it does not change the Jacobian or its group law. The induced homomorphism in the universal property is independent of this translation after the normalization is adjusted.

This is a useful model for a recurring phenomenon. Objects built from a chosen origin in a Picard torsor may depend on the choice as maps or divisors, while their associated homomorphisms depend only on translation-invariant data. The theta divisor will exhibit exactly this behavior.

### 6.4 When no degree-one divisor exists

Even when no degree-one divisor exists, the canonical Abel map lands in the torsor:

$$
C\longrightarrow\operatorname{Pic}^1_{C/k},
\qquad x\longmapsto[\mathcal O_C(x)]. \tag{6.7}
$$

If $\operatorname{Pic}^1_{C/k}(k)$ contains a point $\xi$, translation gives $u_\xi$ even if $\xi$ is Brauer-obstructed and has no line-bundle representative on $C$. What is unavailable in that case is the divisor normalization (6.3). If $\operatorname{Pic}^1_{C/k}(k)=\varnothing$, the torsor itself, rather than $J$, is the natural Albanese target with no chosen origin. After a field extension supplying a degree-one Picard class, it becomes isomorphic to $J$; two such isomorphisms differ by translation. One must not choose a geometric basepoint, write a map to $J_{k^s}$, and then claim that it descends unchanged. Its Galois discrepancy is precisely the cocycle defining the torsor $\operatorname{Pic}^1$.

For all group-theoretic constructions—torsion, Tate modules, duality, and endomorphisms—$J$ itself remains defined over $k$. Only the pointed Abel--Jacobi map requires the extra choice.

## 7. First examples

### 7.1 Genus zero

For $C=\mathbf P^1$, every divisor class is determined by degree and

$$
\operatorname{Pic}(\mathbf P^1)\simeq\mathbf Z,
\qquad J=0.
$$

The same conclusion holds for every smooth proper geometrically connected genus-zero curve, including a nonsplit conic: its geometric Jacobian is a point, so descent gives a point. What changes is the degree map on actual line bundles. A nonsplit conic may have only even degrees. This cleanly separates $J$, which records the connected degree-zero geometry, from the arithmetic of the degree components.

Cohomologically, $H^1(\bar C,\mathbf Z_\ell)=0$, anticipating the rank formula $2g$ and the Tate-module comparison.

### 7.2 An elliptic curve is its own Jacobian

Let $E/k$ be an elliptic curve with identity $O$. The map

$$
E\longrightarrow\operatorname{Pic}^0_{E/k},
\qquad P\longmapsto[\mathcal O_E(P-O)] \tag{7.1}
$$

is an isomorphism of abelian varieties. It is a homomorphism by the divisor relation

$$
(P)+(Q)-(P+Q)-(O)=\operatorname{div}(f)
$$

for the rational function obtained from the line through $P,Q$ and the appropriate vertical line in a plane cubic model. It is nonconstant between smooth proper genus-one curves and has degree one, hence is an isomorphism.

Here the last assertion deserves a scheme-theoretic check in positive characteristic. If $\mathcal O_E(P-O)$ is trivial, then either $P=O$ or a rational function has the single simple pole $O$; the latter would give a degree-one map $E\to\mathbf P^1$ and force $E$ to have genus zero. Thus the geometric kernel has only the identity. The differential of (7.1) is the Abel-map differential

$$
T_OE\longrightarrow H^1(E,\mathcal O_E),
$$

which is dual under Serre duality to evaluation of an invariant differential at $O$ and is therefore nonzero. The homomorphism is separable, so its kernel is étale; an étale kernel with one geometric point is trivial. A homomorphism of elliptic curves with trivial kernel is a degree-one isogeny and hence an isomorphism.

Under (7.1), the abstract tensor law on line bundles becomes the chord-and-tangent law. The example is more than reassurance: every construction below—torsion, Weil pairing, dual isogeny, and polarization—specializes to the familiar elliptic-curve construction.

### 7.3 Hyperelliptic divisor classes

Let $C$ be given over a field of characteristic not two by

$$
y^2=f(x),
$$

with a rational point $\infty$ at infinity and hyperelliptic involution $\iota(x,y)=(x,-y)$. The function $x-a$ has divisor

$$
\operatorname{div}(x-a)=P+\iota(P)-2\infty
$$

when $P$ lies over $a$ away from branching. Hence in $J$

$$
[P-\infty]+[\iota(P)-\infty]=0. \tag{7.2}
$$

A typical class can be represented in reduced form by

$$
D=P_1+\cdots+P_r-r\infty,
\qquad 0\leq r\leq g,
$$

with no pair $P_i,\iota(P_i)$ and with the usual qualification at ramification points. Riemann--Roch reduces longer effective parts by finding a function with prescribed poles. Thus a $g$-dimensional variety appears concretely as unordered collections of at most $g$ points modulo the cancellations (7.2).

If $P$ is a branch point, then $P=\iota(P)$ and

$$
2[P-\infty]=0.
$$

Differences of branch points therefore give visible two-torsion. For a degree $2g+1$ model with all branch points geometric, these classes generate the expected $(\mathbf Z/2\mathbf Z)^{2g}$ subject to the single global relation among branch divisors.

### 7.4 A singular warning

If a smooth elliptic curve degenerates to a nodal cubic, degree-zero line bundles on the singular curve form a group whose connected part is $\mathbf G_m$; for a cuspidal cubic it is $\mathbf G_a$. These generalized Jacobians are not proper. Thus the assertion that $\operatorname{Pic}^0$ is an abelian variety genuinely uses smoothness of the curve. Later good-reduction statements will require a smooth proper family, not merely a proper flat family with singular fibers.

## 8. Functoriality for maps of curves

### 8.1 Pullback and norm

Let $f:C\to C'$ be a nonconstant morphism of smooth proper geometrically connected curves. It is finite and flat. Pullback of line bundles gives

$$
f^*:J_{C'}\longrightarrow J_C. \tag{8.1}
$$

The arrow reverses direction because line bundles are contravariant.

The map in the other direction is the norm. For a relative Cartier divisor $D$ on $C$, push its closed points forward with residue degrees and set

$$
\operatorname{Nm}_f(\mathcal O_C(D))
=\mathcal O_{C'}(f_*D). \tag{8.2}
$$

Equivalently, for a line bundle $L$ one may define

$$
\operatorname{Nm}_f(L)
=\det(f_*L)\otimes\det(f_*\mathcal O_C)^{-1}. \tag{8.3}
$$

The determinant formula works in families and shows compatibility with base change. It induces a covariant homomorphism

$$
f_*=\operatorname{Nm}_f:J_C\longrightarrow J_{C'}. \tag{8.4}
$$

We use $f_*$ when emphasizing covariance and $\operatorname{Nm}_f$ when emphasizing line bundles.

### 8.2 Variance and the degree formula

The fundamental identity is

$$
f_*f^*=[\deg f]_{J_{C'}}. \tag{8.5}
$$

For a divisor $D'$ on $C'$, flat pullback followed by pushforward gives $(\deg f)D'$, including ramification and residue multiplicities. Passing to line-bundle classes proves (8.5).

The opposite composite $f^*f_*$ on $J_C$ is generally not multiplication by $\deg f$. For a double cover with involution $\iota$, it is $1+\iota^*$ on divisor classes. The two composites coincide with scalar multiplication only in special situations. This counterexample is the fastest test of any proposed variance convention.

If maps compose, then

$$
(g\circ f)^*=f^*g^*,
\qquad (g\circ f)_*=g_*f_*.
$$

Thus pullback is contravariant and norm is covariant, while both give covariant maps on Tate modules once the corresponding Jacobian homomorphism has been chosen.

### 8.3 Divisors and projection formulas

For a rational function $h$ on $C$, the field norm satisfies

$$
f_*\operatorname{div}(h)=\operatorname{div}(N_{k(C)/k(C')}h),
$$

so pushforward respects principal equivalence. Flat pullback and proper pushforward satisfy

$$
f_*f^*D'=(\deg f)D' \tag{8.6}
$$

for every divisor $D'$ on $C'$. There is no ordinary intersection product of two divisors on a curve, so a surface-style formula involving $f^*D'\cdot D$ would be misplaced here. The line-bundle projection formula is

$$
\operatorname{Nm}_f(L\otimes f^*M)
\simeq\operatorname{Nm}_f(L)\otimes M^{\otimes\deg f}. \tag{8.7}
$$

The normalizing factor in (8.3) is what makes (8.7) and $\operatorname{Nm}_f(\mathcal O_C)=\mathcal O_{C'}$ hold simultaneously.

Under Abel--Jacobi maps based at degree-one divisors, the norm sends the class of $x-D_0$ to the class of $f_*x-f_*D_0$. Proper pushforward preserves degree over the ground field, so $f_*D_0$ again has degree one. In contrast, flat pullback multiplies degree by $\deg f$. Thus $u_{f_*D_0}\circ f=f_*\circ u_{D_0}$ when $x$ is interpreted as its relative degree-one divisor; confusing pushforward with pullback reverses precisely this degree calculation.

### 8.4 Separable and inseparable maps

No separability hypothesis was used in the divisor definition of the norm. If $f$ is purely inseparable of degree $p^r$, prime-to-$p$ étale cohomology sees $f^*$ as an isomorphism, while

$$
f_*=(\deg f)(f^*)^{-1}
$$

on that cohomology. The same relation follows from (8.5) on prime-to-$p$ Tate modules. At $p$-primary torsion, however, the kernel schemes can be nonreduced and geometric points lose information. The later Tate-module comparison deliberately excludes $\ell=p$.

## 9. Torsion and Tate modules

### 9.1 Multiplication and its kernel

For an abelian variety $A$ of dimension $g$, multiplication by a nonzero integer $n$ is a finite flat surjective homomorphism

$$
[n]:A\longrightarrow A
$$

of degree $n^{2g}$. Its scheme-theoretic kernel is the finite flat commutative group scheme $A[n]$, of rank $n^{2g}$. The rank statement remains true when the characteristic divides $n$, even though the number of geometric points can drop.

The differential of $[n]$ at the identity is multiplication by $n$ on $\operatorname{Lie}A$. Therefore $[n]$ is étale exactly when $n$ is invertible in $k$. This tangent calculation is the clean reason for the prime-to-characteristic boundary.

Applied to $J$, we obtain $J[n]$. It is a group scheme, not merely the abstract subgroup of torsion points. The distinction is crucial at the characteristic and harmless but still conceptually useful away from it.

### 9.2 Prime-to-characteristic torsion

If $n$ is prime to $\operatorname{char}k$, then $J[n]$ is finite étale of rank $n^{2g}$. Over $k^s$ it is therefore constant and

$$
J[n](k^s)\simeq(\mathbf Z/n\mathbf Z)^{2g}. \tag{9.1}
$$

noncanonically. Descent gives a continuous action of $G_k$ on this finite module. No choice of basis is canonical; choosing one turns the action into a matrix representation only up to conjugacy.

At $n=p=\operatorname{char}k$, the claim fails. For example, an ordinary elliptic curve has a connected multiplicative part and an étale part in $E[p]$, whereas a supersingular elliptic curve has no nonzero geometric $p$-torsion points. Both group schemes still have rank $p^2$. This is why (9.1) cannot be extrapolated to the residue characteristic.

### 9.3 The covariant Tate module

Fix $\ell\ne\operatorname{char}k$. The maps

$$
[\ell]:J[\ell^{m+1}](k^s)\longrightarrow J[\ell^m](k^s)
$$

are surjective, and we define

$$
T_\ell J=\varprojlim_mJ[\ell^m](k^s). \tag{9.2}
$$

It is a free $\mathbf Z_\ell$-module of rank $2g$. Indeed each level is free of rank $2g$ over $\mathbf Z/\ell^m\mathbf Z$, and compatible choices of lifts of a basis give a basis in the inverse limit. Set

$$
V_\ell J=T_\ell J\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

A homomorphism $\varphi:A\to B$ sends a compatible tower $(x_m)$ to $(\varphi(x_m))$ and hence induces $T_\ell\varphi:T_\ell A\to T_\ell B$. This is why our Tate module is called covariant. The dual module $\operatorname{Hom}(T_\ell A,\mathbf Z_\ell)$ is naturally contravariant.

### 9.4 Continuous arithmetic Galois action

Every $J[\ell^m]$ is defined over $k$, so $G_k$ acts compatibly on all levels. The inverse limit topology makes

$$
\rho_{J,\ell}:G_k\longrightarrow
\operatorname{Aut}_{\mathbf Z_\ell}(T_\ell J)
\simeq\operatorname{GL}_{2g}(\mathbf Z_\ell) \tag{9.3}
$$

continuous: reduction modulo $\ell^m$ has finite image and open kernel. We use the arithmetic action inherited from $k^s$. Over $\mathbf F_q$, the element acting on coordinates by $x\mapsto x^q$ is arithmetic Frobenius; an eigenvalue statement formulated for geometric Frobenius must invert the operator.

The cyclotomic module is

$$
\mathbf Z_\ell(1)=\varprojlim_m\mu_{\ell^m}(k^s),
$$

with the same power transition maps. Arithmetic Frobenius acts on it by multiplication by $q$. This convention will make all pairing formulas $G_k$-equivariant without inserting inverse characters.

## 10. Kummer theory identifies the Tate module

### 10.1 The finite-level calculation

We now prove the central bridge. Let $n$ be invertible in $k$. On $\bar C$ the Kummer sequence

$$
1\longrightarrow\mu_n\longrightarrow\mathbf G_m
\xrightarrow{[n]}\mathbf G_m\longrightarrow1 \tag{10.1}
$$

is exact on the étale site. Its long exact sequence contains

$$
\bar k^\times\xrightarrow{[n]}\bar k^\times
\longrightarrow H^1(\bar C,\mu_n)
\longrightarrow\operatorname{Pic}(\bar C)
\xrightarrow{[n]}\operatorname{Pic}(\bar C). \tag{10.2}
$$

Because $\bar k$ is separably closed and $n$ is invertible, every element of $\bar k^\times$ has an $n$th root. Exactness therefore gives a canonical injection with image the $n$-torsion:

$$
H^1(\bar C,\mu_n)
\xrightarrow{\sim}\operatorname{Pic}(\bar C)[n]. \tag{10.3}
$$

Every torsion line bundle has degree zero, since $\mathbf Z$ has no torsion. Combining (5.1) and (10.3) yields the canonical $G_k$-equivariant isomorphism

$$
\kappa_n:J[n](k^s)
\xrightarrow{\sim}H^1(\bar C,\mu_n). \tag{10.4}
$$

Concretely, an $n$-torsion line bundle $L$ together with an isomorphism $L^{\otimes n}\simeq\mathcal O$ defines a $\mu_n$-torsor of compatible trivializations. Changing the chosen isomorphism by a scalar does not alter the class because that scalar has an $n$th root. This explains both the map and its canonicity.

The use of $\bar C$ is decisive. Over $C$ itself, Kummer begins with $k^\times/k^{\times n}$, and arithmetic torsors from the ground field appear. Thus $J[n](k)$ is not generally $H^1(C,\mu_n)$.

### 10.2 Compatibility in the tower

An inverse-limit identification requires more than separate isomorphisms. The coefficient transition

$$
\mu_{\ell^{m+1}}\longrightarrow\mu_{\ell^m},
\qquad\zeta\longmapsto\zeta^\ell \tag{10.5}
$$

fits into a morphism of Kummer sequences whose middle map on $\mathbf G_m$ is the identity on the source copy and $[\ell]$ on the appropriate target copy. Naturality of the connecting maps shows that the square

$$
\begin{array}{ccc}
J[\ell^{m+1}](k^s)&\xrightarrow{\kappa_{\ell^{m+1}}}&H^1(\bar C,\mu_{\ell^{m+1}})\\
\downarrow[\ell]&&\downarrow(\zeta\mapsto\zeta^\ell)\\
J[\ell^m](k^s)&\xrightarrow{\kappa_{\ell^m}}&H^1(\bar C,\mu_{\ell^m})
\end{array} \tag{10.6}
$$

commutes.

One may see this on torsors. If $L^{\ell^{m+1}}\simeq\mathcal O$, then $[\ell]L=L^{\otimes\ell}$ is killed by $\ell^m$. Raising an $\ell^{m+1}$st-root trivialization to its $\ell$th power produces exactly the torsor attached to $L^{\otimes\ell}$.

### 10.3 The integral identification

Taking inverse limits in (10.6) gives

$$
T_\ell J
\xrightarrow{\sim}
\varprojlim_mH^1(\bar C,\mu_{\ell^m}). \tag{10.7}
$$

For a smooth proper curve the finite cohomology groups are free of rank $2g$ over $\mathbf Z/\ell^m\mathbf Z$, and the reduction maps are surjective. Hence there is no derived inverse-limit correction, and by definition of continuous $\ell$-adic cohomology the right side is

$$
H^1(\bar C,\mathbf Z_\ell(1)).
$$

We have proved the promised canonical, functorial, $G_k$-equivariant identification

$$
\boxed{T_\ell J\simeq H^1(\bar C,\mathbf Z_\ell(1)).} \tag{10.8}
$$

Compatibility with finite coefficients is exact:

$$
T_\ell J/\ell^mT_\ell J
\simeq J[\ell^m](k^s)
\simeq H^1(\bar C,\mu_{\ell^m}). \tag{10.9}
$$

No torsion correction occurs because $H^2(\bar C,\mathbf Z_\ell(1))\simeq\mathbf Z_\ell$ is torsion-free.

### 10.4 Untwisted and rational formulations

Tensoring (10.8) by $\mathbf Z_\ell(-1)$ gives

$$
H^1(\bar C,\mathbf Z_\ell)
\simeq T_\ell J(-1). \tag{10.10}
$$

Poincaré duality gives another canonical formulation:

$$
H^1(\bar C,\mathbf Z_\ell)
\simeq\operatorname{Hom}_{\mathbf Z_\ell}(T_\ell J,\mathbf Z_\ell), \tag{10.11}
$$

where (10.11) will be identified with (10.10) using the canonical principal polarization. Before a polarization is introduced, the most intrinsic general abelian-variety statement replaces $J$ on the right side by its dual.

After inverting $\ell$,

$$
V_\ell J\simeq H^1(\bar C,\mathbf Q_\ell(1)),
\qquad
H^1(\bar C,\mathbf Q_\ell)\simeq V_\ell J(-1). \tag{10.12}
$$

All are isomorphisms of continuous arithmetic $G_k$-representations. If one instead defines a “Tate module” as the dual of (9.2), the untwisted $H^1$ appears directly; that is a different convention, not a contradiction.

## 11. Dual abelian varieties and the Poincaré bundle

### 11.1 Why a second Picard construction appears

A line bundle on an abelian variety $A$ can vary algebraically under translation. The degree-zero families are themselves parametrized by an abelian variety

$$
A^\vee=\operatorname{Pic}^0_{A/k},
$$

called the **dual abelian variety**. Its geometric points are algebraically trivial line bundles on $A_{k^s}$, not arbitrary line bundles. Algebraic triviality means belonging to the connected component of $\mathcal O_A$ in the Picard scheme; numerical degree zero on curves is its one-dimensional special case.

The construction answers a duality problem. A homomorphism into $A^\vee$ is a family of line bundles on $A$, varying multiplicatively in the parameter. Such families are the geometric analogues of bilinear characters. Unlike the dual of a vector space, $A^\vee$ has the same dimension as $A$ but is not canonically isomorphic to it in general.

### 11.2 The normalized Poincaré bundle

There is a universal line bundle $\mathcal P_A$ on $A\times A^\vee$, uniquely normalized by

$$
\mathcal P_A|_{\{0\}\times A^\vee}\simeq\mathcal O,
\qquad
\mathcal P_A|_{A\times\{0\}}\simeq\mathcal O. \tag{11.1}
$$

Its restriction to $A\times\{\eta\}$ represents the point $\eta\in A^\vee$. The two normalizations eliminate pullbacks from either factor. The theorem of the square gives compatible isomorphisms

$$
(m_A\times1)^*\mathcal P_A
\simeq p_{13}^*\mathcal P_A\otimes p_{23}^*\mathcal P_A,
$$

and similarly in the second variable. Thus $\mathcal P_A$ is a biextension: it is additive, in the line-bundle sense, in each argument.

This Poincaré bundle is canonical over $k$. It should not be confused with a universal line bundle on $C\times J$, whose normalization may require a point of $C$ or other rigidifying data. Once $J$ is an abelian variety, $J\times J^\vee$ has identity sections on both sides, so (11.1) is always available.

### 11.3 Biduality

Fixing $a\in A$ and restricting $\mathcal P_A$ to $\{a\}\times A^\vee$ gives an algebraically trivial line bundle on $A^\vee$. Hence there is a homomorphism

$$
\iota_A:A\longrightarrow A^{\vee\vee}. \tag{11.2}
$$

**Biduality theorem.** The map $\iota_A$ is an isomorphism.

**Proof strategy.** Use the universal property twice and let the normalization determine the sign. The Poincaré bundle on $A\times A^\vee$, viewed with the factors reversed, is a family of algebraically trivial line bundles on $A^\vee$ parametrized by $A$. It produces (11.2). Applying the same construction to $A^\vee$ produces a map in the reverse direction.

Pull both composite families back to $A\times A^\vee$. On every slice through an identity they have the normalization (11.1), and on every other geometric slice they represent the original point of the appropriate Picard variety. The see-saw principle says that two line bundles with these fiberwise identifications and identity normalizations are isomorphic. The composites therefore induce the identity universal family, hence are identity morphisms by representability. This proves biduality without first choosing a polarization.

The argument also proves functoriality. For $f:A\to B$, its dual

$$
f^\vee:B^\vee\longrightarrow A^\vee,
\qquad L\longmapsto f^*L \tag{11.3}
$$

is contravariant, and $f^{\vee\vee}$ identifies with $f$.

### 11.4 Homomorphisms from line bundles

For a line bundle $L$ on $A$, define

$$
\lambda_L:A\longrightarrow A^\vee,
\qquad
a\longmapsto t_a^*L\otimes L^{-1}. \tag{11.4}
$$

The theorem of the square makes $\lambda_L$ a homomorphism. Tensor product adds homomorphisms, and translation does not change them:

$$
\lambda_{L\otimes M}=\lambda_L+\lambda_M,
\qquad
\lambda_{t_b^*L}=\lambda_L. \tag{11.5}
$$

The second identity is the mechanism by which choices of origins will disappear. Moreover $\lambda_L^\vee=\lambda_L$ under biduality: homomorphisms arising from line bundles are symmetric.

Not every line bundle gives an isogeny. If $L$ is pulled back from a quotient, translations along the connected kernel leave it unchanged and $\lambda_L$ has positive-dimensional kernel. An ample line bundle makes $\lambda_L$ an isogeny, but the converse without a positivity condition is false: the inverse of an ample line bundle is anti-ample and induces $-\lambda_L$, still an isogeny. A line bundle with finite $\lambda_L$ is called nondegenerate. A polarization requires the positive, ample component among such symmetric isogenies; finiteness alone does not supply positivity.

## 12. Polarizations and theta

### 12.1 Positive self-duality

A **polarization** of $A$ is a homomorphism $\lambda:A\to A^\vee$ that becomes $\lambda_L$ for an ample line bundle $L$ after extension to an algebraic closure. It is **principal** if it is an isomorphism. Its degree is the rank of its finite kernel. If $\lambda_L$ has finite kernel, abelian Riemann--Roch gives

$$
\deg\lambda_L=\chi(L)^2
=\left(\frac{c_1(L)^g}{g!}\right)^2. \tag{12.1}
$$

When $L$ is ample this hypothesis holds, and the right side is positive. Thus a principal polarization is not just an abstract self-duality. It is a positive self-duality with volume one. An arbitrary isomorphism $A\simeq A^\vee$ need not be a polarization.

Polarizations also control complements and adjoints. They turn a map into a transpose with respect to a positive geometric form, exactly as an inner product does in linear algebra, although the construction remains algebraic over every field.

### 12.2 The theta divisor

Assume first that $g\geq1$ and work over the algebraic closure $\Omega$. The Abel image

$$
W_{g-1}=\{[\mathcal O(E)]:E\geq0,\ \deg E=g-1\}
\subset\operatorname{Pic}^{g-1}_{C_\Omega} \tag{12.2}
$$

is an effective divisor. Indeed $C^{(g-1)}$ has dimension $g-1$, while $\operatorname{Pic}^{g-1}$ has dimension $g$, and the Abel map is generically finite onto its image. Equivalently,

$$
W_{g-1}=\{[L]:h^0(C_\Omega,L)>0\}.
$$

The divisor structure, including its multiplicities, is supplied by determinant of cohomology. Let $p:C_\Omega\times\operatorname{Pic}^{g-1}\to\operatorname{Pic}^{g-1}$ and choose a normalized universal bundle $\mathcal U$. Locally on the Picard variety, $Rp_*\mathcal U$ is represented by a two-term complex of vector bundles

$$
E^0\xrightarrow{d}E^1.
$$

Riemann--Roch gives Euler characteristic zero, so after adding the same trivial summand to both terms their ranks agree. The determinant $\det(d)$ is a section of $(\det E^0)^{-1}\otimes\det E^1$. Its zero scheme is exactly the locus where $H^0(C_\Omega,L)$, equivalently $H^1(C_\Omega,L)$, is nonzero. It is not the zero section because a general degree-$(g-1)$ bundle has no section. Since the Picard variety is smooth, this nonzero determinant defines an effective Cartier divisor with the desired geometric support. Changing the local two-term resolution multiplies the determinant by a unit and canonically identifies its determinant line, so the local divisors glue. This is the theta divisor with its scheme-theoretic multiplicity; a set-theoretic Abel image would not suffice for the intersection calculation below.

Choose a line bundle $M$ of degree $g-1$. Translation by $M^{-1}$ identifies $\operatorname{Pic}^{g-1}$ with $J$, and transports $W_{g-1}$ to a divisor $\Theta_M$ on $J$. Different choices of $M$ translate this divisor:

$$
\Theta_{M'}=t_{[M'\otimes M^{-1}]}^*\Theta_M. \tag{12.3}
$$

The divisor itself is therefore not canonical. Its associated homomorphism is, by (11.5).

### 12.3 The canonical principal polarization

Define

$$
\lambda_C=\lambda_{\mathcal O_J(\Theta_M)}:J\longrightarrow J^\vee. \tag{12.4}
$$

Equation (12.3) makes this independent of $M$. It is called the **canonical principal polarization** of the Jacobian.

We now explain principality rather than treating it as a label. Write $W_d$ for the image of $C^{(d)}$ in $\operatorname{Pic}^d$ and translate every $W_d$ into $J$. The decisive point is to retain diagonal and inseparable multiplicities. Fix $0\leq d\leq g-1$, choose an effective divisor $E$ of degree $N\gg0$, and let $\mathcal L$ be a normalized universal degree-$d$ bundle on $C_\Omega\times\operatorname{Pic}^d$. Pushing forward

$$
0\longrightarrow\mathcal L
\longrightarrow\mathcal L(E)
\longrightarrow\mathcal L(E)|_E
\longrightarrow0
$$

gives a map of vector bundles

$$
p_*\mathcal L(E)\longrightarrow p_*(\mathcal L(E)|_E) \tag{12.5}
$$

of ranks $N+d+1-g$ and $N$. Its kernel at $[L]$ is $H^0(C_\Omega,L)$. Hence $W_d$, with its Abel-image scheme structure, is the locus where (12.5) has rank at most $N+d-g$. It has the expected codimension $g-d$: the Abel map $C^{(d)}\to W_d$ is generically one-to-one because a general effective divisor of degree at most $g-1$ has only its canonical section.

The maximal-minor resolution of (12.5) computes the degeneracy cycle as

$$
[W_d]=c_{g-d}\bigl(p_*(\mathcal L(E)|_E)-p_*\mathcal L(E)\bigr).
$$

The virtual bundle in parentheses is $-Rp_*\mathcal L$, independently of $E$. The curve Riemann--Roch calculation of its Chern classes is short enough to record. Write

$$
c_1(\mathcal L)=d\eta+\xi,
$$

where $\eta$ is the class of a point on $C_\Omega$ and $\xi$ has one degree in the curve direction and one in the Picard direction. In

$$
\operatorname{ch}(Rp_*\mathcal L)
=p_*\bigl(\exp(d\eta+\xi)\operatorname{td}(C_\Omega)\bigr),
$$

only $d\eta$, $(1-g)\eta$, and $\xi^2/2$ have the required curve degree. The first two give the rank $d+1-g$; contraction of $\xi^2/2$ by the divisor--differential pairing is $-c_1(\Theta_M)$. Higher positive-degree Chern-character terms vanish because the curve contributes no higher degree. Thus, for $V=-Rp_*\mathcal L$,

$$
\operatorname{ch}(V)=g-d-1+c_1(\Theta_M),
\qquad
c(V)=\exp(c_1(\Theta_M)).
$$

It follows that

$$
[W_d]=\frac{c_1(\Theta_M)^{g-d}}{(g-d)!}. \tag{12.6}
$$

Because this is a determinantal-cycle computation, it includes the multiplicities along diagonals and remains valid in every characteristic. At $d=0$, $W_0$ is the reduced origin, so (12.6) gives

$$
c_1(\Theta_M)^g=g![0]. \tag{12.7}
$$

An effective divisor on an abelian variety is nef: translate it away from a chosen curve and compute a nonnegative intersection. A nef line bundle has zero top self-intersection when its connected translation stabilizer is positive-dimensional, because its numerical class then descends to a quotient of smaller dimension. Equation (12.7) therefore makes the stabilizer finite. The abelian Nakai criterion makes $\mathcal O(\Theta_M)$ ample, so $\lambda_C$ is an isogeny. Abelian Riemann--Roch gives

$$
\chi(\mathcal O(\Theta_M))
=\frac{c_1(\Theta_M)^g}{g!}=1.
$$

Now, and only now, (12.1) applies and gives $\deg\lambda_C=1$. Its finite flat kernel has rank one and is therefore trivial, so $\lambda_C$ is an isomorphism. This order avoids using the degree formula before nondegeneracy has been proved.

For $g=1$, $W_0$ is the origin in $\operatorname{Pic}^0$, and (12.4) is the usual principal polarization of an elliptic curve. For $g=0$, $J=0$ and its unique self-map is the principal polarization by convention.

### 12.4 Why the construction is canonical

Three possible choices must be separated.

First, an Abel--Jacobi map uses a degree-one divisor and changes by translation. Second, writing theta as a divisor on $J_{k^s}$ uses a degree-$(g-1)$ class and also changes by translation. Third, a particular symmetric theta divisor may require choosing a theta characteristic. None of these choices changes $\lambda_C$.

For $\sigma\in G_k$, the conjugate of $\Theta_M$ is $\Theta_{\sigma M}$ and hence a translate of $\Theta_M$. Therefore $\sigma(\lambda_C)=\lambda_C$, so the homomorphism descends uniquely to $k$. This proves canonicity even when no degree-one or degree-$(g-1)$ line bundle exists over $k$.

The word “canonical” applies to the polarization homomorphism, not to a preferred theta divisor. Confusing those claims leads to false descent assertions.

## 13. Weil pairings and cup products

### 13.1 The finite Weil pairing

Let $A$ be an abelian variety and let $n$ be invertible in $k$. The normalized Poincaré biextension gives a perfect Cartier pairing

$$
e_n:A[n]\times A^\vee[n]\longrightarrow\mu_n. \tag{13.1}
$$

We fix the following order convention. The first variable lies in $A[n]$, the second in $A^\vee[n]$, and $e_n(x,\eta)$ is the scalar carrying the torsion trivialization obtained by translating first in the $A$-direction by $x$ and then in the $A^\vee$-direction by $\eta$ to the trivialization obtained in the reverse order. Interchanging the two routes replaces the value by its inverse. This convention is fixed independently of a later identification $A\simeq A^\vee$.

For a polarization $\lambda:A\to A^\vee$, put

$$
e_{\lambda,n}(x,y)=e_n(x,\lambda(y)). \tag{13.2}
$$

If $\lambda$ is principal, this is a perfect alternating pairing on $A[n]$. It is bilinear, $G_k$-equivariant, and satisfies

$$
e_{\lambda,n}(\sigma x,\sigma y)
=\sigma e_{\lambda,n}(x,y). \tag{13.3}
$$

For a homomorphism $f:A\to B$, Poincaré functoriality gives

$$
e_n(fx,\eta)=e_n(x,f^\vee\eta). \tag{13.4}
$$

This is the finite-level source of every adjoint formula below.

### 13.2 Comparison with the curve cup product

For $n$ invertible, define the twisted intersection pairing

$$
q_n:H^1(\bar C,\mu_n)\times H^1(\bar C,\mu_n)
\longrightarrow\mu_n \tag{13.5}
$$

by cup product followed by the trace

$$
H^2(\bar C,(\mathbf Z/n\mathbf Z)(2))
\xrightarrow{\operatorname{Tr}_{\bar C}}
(\mathbf Z/n\mathbf Z)(1)=\mu_n.
$$

Here the trace lowers the Tate twist by one because a curve has dimension one. Graded commutativity makes $q_n(\alpha,\beta)=q_n(\beta,\alpha)^{-1}$ in multiplicative notation. Its alternation at even $n$ is part of the geometric self-intersection calculation, not a consequence of the sign alone.

**Comparison theorem.** With (13.1) ordered as specified and $\lambda_C$ defined by (12.4), the Kummer isomorphism satisfies

$$
q_n(\kappa_nx,\kappa_ny)=e_{\lambda_C,n}(x,y). \tag{13.6}
$$

**Proof strategy.** Both sides measure the same failure of two $n$th-root trivializations to commute. We compare them first for line bundles represented by disjoint degree-zero divisors and then extend by bilinearity.

Write $x=[D]$ and $y=[E]$, move the supports apart, and choose rational functions

$$
\operatorname{div}(f)=nD,
\qquad \operatorname{div}(g)=nE.
$$

The Kummer torsor of $x$ is obtained by taking local $n$th roots of a rational trivialization of $\mathcal O(D)$ whose $n$th power is $f$; similarly for $y$. Choose an étale cover on which both roots exist and write their transition functions as $\mu_n$-valued Čech $1$-cocycles $(a_{ij})$ and $(b_{ij})$. The cup cocycle is $(a_{ij}\otimes b_{jk})$. Resolving it at the codimension-one points in the supports of $D$ and $E$, then applying the curve trace, gives the ratio

$$
\frac{f(E)}{g(D)}\in\mu_n,\qquad
f(E)=\prod_P f(P)^{\operatorname{ord}_P(E)},
$$

with the analogous convention for $g(D)$. Weil reciprocity gives

$$
f(\operatorname{div}g)=g(\operatorname{div}f),
\qquad f(E)^n=g(D)^n,
$$

so the displayed ratio is indeed an $n$th root of unity. Scaling $f$ or $g$ has no effect because $D$ and $E$ have degree zero. Replacing, for example, $D$ by $D+\operatorname{div}h$ replaces $f$ by $fh^n$; Weil reciprocity gives $g(\operatorname{div}h)=h(\operatorname{div}g)=h(E)^n$, so numerator and denominator acquire the same factor. The other changes are identical. Thus the cohomological value is well defined and is computed entirely by these local commutators.

It remains to identify the geometric commutator with the same calculation, including the sign forced by the Abel map. Pull the normalized Poincaré bundle on $J\times J^\vee$ back along

$$
u_{D_0}\times\lambda_C:C\times J\longrightarrow J\times J^\vee
$$

after making a geometric degree-one choice. In the notation of the Albanese theorem, the identity factorization of $u_{D_0}$ says

$$
-\,(u_{D_0}^*)^\vee\lambda_C=1_J.
$$

Dualizing and using the symmetry of $\lambda_C$ gives

$$
u_{D_0}^*\lambda_C=[-1]_J. \tag{13.6a}
$$

This is the established Abel--theta sign for the conventions $u_{D_0}(x)=\mathcal O(x-D_0)$ and $\lambda_L(a)=t_a^*L\otimes L^{-1}$. The see-saw principle therefore identifies the displayed pullback not with the normalized universal degree-zero bundle $\mathcal U$ on $C\times J$, but with its dual $\mathcal U^\vee$. On the slice indexed by $[E]$ it represents $\mathcal O(-E)$. Omitting this dual is the usual source of a wrong sign in the comparison theorem.

Now compute the biextension commutator using $\mathcal U^\vee$. Off the supports of $D$ and $E$, use the inverse rational trivializations supplied by $f$ and $g$. Along the route “first $x$, then $\lambda_C(y)$,” the change across $E$ contributes $f(E)$; along the reverse route the change across $D$ contributes $g(D)$. Their quotient, with the convention of Section 13.1, is

$$
\frac{f(E)}{g(D)}.
$$

The inverse universal bundle and the inverse in (13.6a) have already been incorporated in these two transition calculations; inserting another minus sign would count the same inversion twice. Translation of the degree-one choice tensors both families by a base pullback and leaves the commutator unchanged. Hence the Poincaré commutator of $x$ and $\lambda_C(y)$ is exactly the cup-product value above, not merely equal to it up to sign.

This proves (13.6) for divisor representatives with disjoint support. The moving lemma on a smooth curve supplies such representatives for any pair of degree-zero classes, and every prime-to-characteristic torsion class is a degree-zero divisor class. Bilinearity then proves the theorem. Notice that the argument proves compatibility, not merely that two perfect alternating forms exist: perfect alternating forms of rank $2g$ are not unique without a chosen symplectic basis.

This proof also diagnoses convention changes. Reversing the Poincaré commutator or defining $\lambda_L(a)=L\otimes t_a^*L^{-1}$ replaces both $e_{\lambda,n}$ and the displayed comparison by their inverses. The mathematical pairing is unchanged; the written sign is not.

### 13.3 Passage to Tate modules

The Poincaré biextension makes the finite pairings compatible with multiplication in the torsion towers. Taking their inverse limit gives a continuous pairing

$$
e_{\lambda,\ell}:T_\ell A\times T_\ell A
\longrightarrow\mathbf Z_\ell(1). \tag{13.7}
$$

It is perfect over $\mathbf Z_\ell$ exactly when $T_\ell\lambda:T_\ell A\to T_\ell A^\vee$ is an isomorphism; this holds whenever $\ell\nmid\deg\lambda$, and in particular for a principal polarization. For a general polarization it becomes perfect after tensoring with $\mathbf Q_\ell$, but its integral discriminant can contain the $\ell$-primary part of $\ker\lambda$. This qualification prevents a nonprincipal polarization from being mistaken for an integral self-duality.

For the Jacobian, (13.6) passes to the limit and says

$$
e_{\lambda_C,\ell}(x,y)
=\operatorname{Tr}_{\bar C}
\bigl(\kappa x\smile\kappa y\bigr), \tag{13.8}
$$

where

$$
\kappa:T_\ell J\xrightarrow{\sim}H^1(\bar C,\mathbf Z_\ell(1))
$$

and the right side lies in $\mathbf Z_\ell(1)$ because cup product has twist two and trace lowers it to twist one.

For the principally polarized Jacobian, perfectness of (13.7) yields

$$
T_\ell J\xrightarrow{\sim}(T_\ell J)^\vee(1),
\qquad
(T_\ell J)^\vee\simeq T_\ell J(-1). \tag{13.9}
$$

Combining (13.9) with (10.8) recovers the untwisted dual formulation

$$
H^1(\bar C,\mathbf Z_\ell)
\simeq(T_\ell J)^\vee. \tag{13.10}
$$

At finite level the same statement is

$$
H^1(\bar C,\mathbf Z/\ell^m\mathbf Z)
\simeq\operatorname{Hom}
\bigl(J[\ell^m](k^s),\mathbf Z/\ell^m\mathbf Z\bigr), \tag{13.11}
$$

with the Galois action on the Hom module given by $(\sigma\varphi)(x)=\sigma(\varphi(\sigma^{-1}x))$; the cyclotomic twist has already been canceled by the Weil pairing.

### 13.4 Signs, twists, and adjoints

The pairing (13.7) is alternating and $G_k$-equivariant, not scalar-valued with trivial action. In particular,

$$
e_{\lambda_C,\ell}(\sigma x,\sigma y)
=\chi_\ell(\sigma)e_{\lambda_C,\ell}(x,y)
$$

after choosing a $\mathbf Z_\ell$-basis of $\mathbf Z_\ell(1)$, where $\chi_\ell$ is the cyclotomic character. For $g=1$, this gives $\det T_\ell E=\chi_\ell$; in dimension $g$, the representation lands in the group of symplectic similitudes with multiplier $\chi_\ell$.

Poincaré duality on untwisted cohomology is usually written

$$
H^1(\bar C,\mathbf Z_\ell)\times
H^1(\bar C,\mathbf Z_\ell(1))\longrightarrow\mathbf Z_\ell. \tag{13.12}
$$

It is the evaluation pairing between (13.10) and (10.8). The alternating pairing (13.8) is obtained by twisting both inputs instead. These are two formulations of one duality, not two independent forms.

If $u:J_C\to J_{C'}$ is a homomorphism, its adjoint relative to the canonical polarizations is

$$
u^\dagger=\lambda_C^{-1}u^\vee\lambda_{C'}:J_{C'}\to J_C. \tag{13.13}
$$

Then

$$
e_{C',\ell}(T_\ell u(x),y)
=e_{C,\ell}(x,T_\ell u^\dagger(y)). \tag{13.14}
$$

The cup-product adjoint has the same direction and no extra sign: both arguments have degree one, but adjointness moves a pullback past trace through the projection formula rather than swapping the two cup factors.

## 14. Algebraic correspondences

### 14.1 From a cycle to a homomorphism

Let $C$ and $C'$ be smooth proper geometrically connected curves over a perfect field $k$. A finite correspondence from $C$ to $C'$ is a finite integral linear combination of integral curves $\Gamma_i\subset C\times C'$ finite and surjective over the relevant components. For one integral component, let $\widetilde\Gamma$ be its normalization and write

$$
\begin{array}{ccc}
&\widetilde\Gamma&\\
p\swarrow&&\searrow q\\
C&&C'.
\end{array}
$$

The induced homomorphism of Jacobians, covariant from source to target, is

$$
\Gamma_J=q_*p^*:J_C\longrightarrow J_{C'}. \tag{14.1}
$$

Extend this linearly in the multiplicities. On a divisor $D$ whose support meets the correspondence properly, (14.1) pulls $D$ to $\widetilde\Gamma$ and pushes it to $C'$. Principal divisors remain principal because norm carries rational functions to rational functions. Formula (14.1) therefore agrees with the direct action on divisor classes.

The perfectness assumption ensures that the normalization is a smooth curve. More general cycle-theoretic definitions remove it, but the normalization formula then requires regularity qualifications. The arithmetic applications motivating this book occur over perfect fields.

### 14.2 Graphs, transposes, and composition

If $f:C\to C'$ is finite, the graph $\Gamma_f\subset C\times C'$ has $p=1_C$ and $q=f$. Therefore

$$
(\Gamma_f)_J=f_*.
$$

Its transpose has the projections reversed and acts by

$$
(\Gamma_f^t)_J=f^*.
$$

Thus the graph test fixes the variance: a graph acts by norm or pushforward, its transpose by pullback.

For $\Gamma:C\dashrightarrow C'$ and $\Delta:C'\dashrightarrow C''$, define $\Delta\circ\Gamma$ by intersecting the pullbacks of the cycles in $C\times C'\times C''$ and pushing to $C\times C''$, with intersection multiplicities. Projection formulas give

$$
(\Delta\circ\Gamma)_J=\Delta_J\circ\Gamma_J. \tag{14.2}
$$

Vertical and horizontal components act trivially on degree-zero Picard varieties: their action factors through the Picard group of a point. Hence arbitrary divisor correspondences modulo such components give the same homomorphisms as finite dominant representatives.

Transpose is the polarization adjoint:

$$
(\Gamma^t)_J=(\Gamma_J)^\dagger. \tag{14.3}
$$

To prove this, decompose into integral components and use (13.4). Pullback and norm are dual under the Poincaré bundles, while the canonical polarizations are the theta self-dualities. Equivalently, (14.3) can be checked after applying a prime-to-characteristic Tate module, where it is Poincaré duality's projection formula; a homomorphism of abelian varieties vanishing on all $\ell^m$-torsion is zero.

### 14.3 Compatibility with cohomology

The same correspondence acts on cohomology by

$$
\Gamma_H=q_*p^*:
H^1(\bar C,\mathbf Z_\ell(1))
\longrightarrow
H^1(\bar C',\mathbf Z_\ell(1)), \tag{14.4}
$$

where $q_*$ is cohomological trace. The Kummer identifications make the square

$$
\begin{array}{ccc}
T_\ell J_C&\xrightarrow{T_\ell\Gamma_J}&T_\ell J_{C'}\\
\downarrow\kappa_C&&\downarrow\kappa_{C'}\\
H^1(\bar C,\mathbf Z_\ell(1))&\xrightarrow{\Gamma_H}&H^1(\bar C',\mathbf Z_\ell(1))
\end{array} \tag{14.5}
$$

commute.

**Proof.** Pullback compatibility follows directly from naturality of the Kummer sequence: pulling back an $n$-torsion line bundle pulls back its root-trivialization torsor. For a finite flat map $q$, the multiplicative norm on units and the norm on line bundles form a morphism of Kummer sequences after applying cohomological trace. Over the étale locus the coefficient norm multiplies over the sheets; the finite-flat norm supplies the extension across the branch locus and builds in the ramification multiplicities. Thus no unsupported uniqueness assertion at a branch point is needed. In the Kummer long exact sequence the resulting square is

$$
\begin{array}{ccc}
H^1(\widetilde\Gamma,\mu_n)&\longrightarrow&\operatorname{Pic}(\widetilde\Gamma)[n]\\
\downarrow q_*&&\downarrow\operatorname{Nm}_q\\
H^1(C',\mu_n)&\longrightarrow&\operatorname{Pic}(C')[n].
\end{array}
$$

It commutes at every finite level. Composing with $p^*$ and taking inverse limits proves (14.5).

Consequently composition, transpose, Galois descent, and reduction modulo $\ell^m$ agree on the Jacobian and cohomological sides. In particular,

$$
\langle\Gamma_Ha,b\rangle_{C'}
=\langle a,(\Gamma^t)_Hb\rangle_C, \tag{14.6}
$$

with the pairings and twists of Chapter 13.

### 14.4 A worked graph correspondence

Let $f:C\to D$ be finite of degree $d$. Regard $\Gamma_f$ as a correspondence $C\dashrightarrow D$ and $\Gamma_f^t$ as one from $D$ to $C$. Then

$$
\Gamma_f\circ\Gamma_f^t
$$

acts on $J_D$ and $H^1(\bar D)$ as $f_*f^*=[d]$. In the opposite order,

$$
\Gamma_f^t\circ\Gamma_f
$$

acts on $J_C$ as $f^*f_*$. If $f$ is a Galois cover with group $G$, then

$$
f^*f_*=\sum_{\sigma\in G}\sigma^*. \tag{14.7}
$$

For a double cover with involution $\iota$, (14.7) is $1+\iota^*$. The anti-invariant part is killed, so the operator is not $[2]$ unless that part vanishes. This worked example simultaneously checks composition order, transpose, norm variance, and the meaning of multiplicity in a correspondence.

If the graph is defined over $k$, every arrow in (14.5) commutes with $G_k$. If it is defined only over an extension, it gives only an operator commuting with the smaller Galois group. Summing its Galois conjugates produces a descended cycle and a $G_k$-equivariant operator; invariance of eigenvalues alone would not supply descent.

## 15. Endomorphisms, Rosati involutions, and isogenies

### 15.1 The endomorphism algebra

For an abelian variety $A/k$, write

$$
\operatorname{End}^0_k(A)
=\operatorname{End}_k(A)\otimes_{\mathbf Z}\mathbf Q.
$$

The integral endomorphism ring is a finite free abelian group. Here is the finiteness input. More generally, for abelian varieties $A$ and $B$, pull the normalized Poincaré bundle on $B\times B^\vee$ back along $f\times1_{B^\vee}$ for $f:A\to B$. Its normalized mixed line-bundle class on $A\times B^\vee$ recovers $f$ by Poincaré representability and biduality. This embeds $\operatorname{Hom}_k(A,B)$ into the Néron--Severi group of $A\times B^\vee$, which is finitely generated. The Hom group is torsion-free: if $nf=0$, then $f$ factors through the finite affine group scheme $B[n]$. Every morphism from the proper geometrically connected variety $A$ to an affine scheme is constant because its coordinate functions are global regular functions on $A$; as a homomorphism, $f$ is therefore zero. Thus $\operatorname{Hom}_k(A,B)$, and in particular $\operatorname{End}_k(A)$, is finite free. Consequently $\operatorname{End}^0_k(A)$ is a finite-dimensional $\mathbf Q$-algebra.

Every endomorphism acts covariantly on $T_\ell A$ and $V_\ell A$. If it is defined over $k$, that action commutes with $G_k$, giving

$$
\operatorname{End}_k(A)
\longrightarrow
\operatorname{End}_{\mathbf Z_\ell[G_k]}(T_\ell A). \tag{15.1}
$$

The map is injective. If an endomorphism kills $T_\ell A$, it kills $A[\ell^m](k^s)$ for every $m$. The union $A[\ell^\infty](k^s)$ is Zariski dense. Indeed, let $H$ be its Zariski closure; it is a closed subgroup. The union is $\ell$-divisible, while the image $[\ell](H)$ is closed because $H$ is proper. Since $[\ell](H)$ contains the dense torsion union, it equals $H$; multiplication by $\ell$ is therefore surjective on $H(k^s)$, including on its finite component group. If $Q=A/H$ had positive dimension, choose a nonzero $y\in Q[\ell](k^s)$ and lift it to $x\in A(k^s)$. Then $\ell x\in H(k^s)$, so choose $h\in H(k^s)$ with $\ell h=\ell x$. Now $x-h\in A[\ell](k^s)\subset H(k^s)$, whence $x\in H(k^s)$ and $y=0$, a contradiction. Thus $H=A$. The kernel of our endomorphism is closed and contains this dense union, so the endomorphism is zero. We do not assert that (15.1) is surjective over an arbitrary field; that is a much deeper arithmetic statement and is not needed here.

For a Jacobian, correspondences defined over $k$ supply a distinguished subalgebra of $\operatorname{End}_k(J)$. Vertical and horizontal cycle components lie in its kernel. Different cycles can induce the same endomorphism, so the correspondence ring and the endomorphism ring should not be identified.

### 15.2 Rosati as geometric adjoint

Fix a polarization $\lambda:A\to A^\vee$. For $u\in\operatorname{End}^0(A)$ define

$$
u^\dagger=\lambda^{-1}u^\vee\lambda. \tag{15.2}
$$

This is the **Rosati involution**. It reverses products,

$$
(uv)^\dagger=v^\dagger u^\dagger,
\qquad (u^\dagger)^\dagger=u.
$$

The inverse in (15.2) is interpreted in the isogeny category unless $\lambda$ is principal. For a Jacobian with its canonical principal polarization it is an actual integral endomorphism whenever $u$ is.

On $V_\ell A$, Rosati is adjoint for the Weil form:

$$
e_\lambda(ux,y)=e_\lambda(x,u^\dagger y). \tag{15.3}
$$

For $u=\Gamma_J$ on a Jacobian, (14.3) says that $u^\dagger$ is induced by the transpose correspondence. This is precisely the amount of Rosati theory needed for geometric operator algebras: transpose cycles become adjoint operators, and a symmetric correspondence gives a Rosati-self-adjoint endomorphism.

The deeper positivity properties of Rosati are not needed here. For later correspondence arguments, the essential facts are the algebraic identities (15.2)--(15.3): transpose reverses composition and is adjoint for the polarized pairing.

### 15.3 Isogenies, kernels, and degrees

An **isogeny** $\varphi:A\to B$ is a surjective homomorphism with finite kernel. For abelian varieties of equal dimension, each of the following implies the others: $\varphi$ is an isogeny; $\ker\varphi$ is finite; $\varphi$ is finite and dominant. Its degree is

$$
\deg\varphi=\operatorname{rank}(\ker\varphi), \tag{15.4}
$$

the scheme-theoretic rank, not the number of geometric kernel points. It is separable exactly when its kernel is étale; then the geometric kernel has $\deg\varphi$ points. Purely inseparable isogenies show why geometric counting is unsafe in positive characteristic.

The dual map $\varphi^\vee:B^\vee\to A^\vee$ is again an isogeny of the same degree. With chosen polarizations its adjoint is

$$
\varphi^\dagger=\lambda_A^{-1}\varphi^\vee\lambda_B:B\to A.
$$

If $\varphi^*\lambda_B=m\lambda_A$ in the symmetric Hom group, then

$$
\varphi^\dagger\varphi=[m]_A,
\qquad
\varphi\varphi^\dagger=[m]_B. \tag{15.5}
$$

One should not impose (15.5) with $m=\deg\varphi$ in arbitrary dimension; for multiplication $[n]$ on a $g$-dimensional variety, the degree is $n^{2g}$ while the polarization multiplier is $n^2$.

For $\ell\ne\operatorname{char}k$, $T_\ell\varphi$ is injective with finite cokernel, and

$$
\#\operatorname{coker}(T_\ell\varphi)
=\ell^{v_\ell(\deg\varphi)}. \tag{15.6}
$$

To see the formula, factor the finite kernel into its $\ell$-primary and prime-to-$\ell$ parts. The prime-to-$\ell$ part induces an isomorphism on every $\ell^m$-torsion group. If the $\ell$-primary part has rank $\ell^a$, the exact sequences of finite étale $\ell$-power torsion show, for all sufficiently large $m$, that the index of

$$
T_\ell\varphi(T_\ell A)\subseteq T_\ell B
$$

is $\ell^a$. Since finite flat kernel rank is the isogeny degree, $a=v_\ell(\deg\varphi)$, proving (15.6). Consequently $V_\ell\varphi$ is an isomorphism, and $T_\ell\varphi$ is an isomorphism when $\ell\nmid\deg\varphi$. This is why objects considered only up to isogeny have identical rational Tate representations.

### 15.4 Semisimplicity up to isogeny

The isogeny category of abelian varieties is semisimple: every abelian subvariety admits a complementary abelian subvariety up to finite intersection. Here is the geometric argument needed later.

Let $B\subset A$ be an abelian subvariety and choose a polarization $\lambda$ on $A$. The composite

$$
B\hookrightarrow A\xrightarrow{\lambda}A^\vee
\longrightarrow B^\vee \tag{15.7}
$$

is the polarization induced on $B$, hence an isogeny. Let $B'$ be the identity component of the kernel of $A\to B^\vee$. Then $B\cap B'$ is finite by (15.7), and dimensions add to $\dim A$. The addition map

$$
B\times B'\longrightarrow A
$$

is therefore an isogeny. Thus inclusions split after tensoring Hom groups with $\mathbf Q$.

To pass from this complement statement to algebra, take any homomorphism in the isogeny category. Its connected kernel and its image are abelian subvarieties; replacing source and target by isogenous products with complements expresses the map as an isomorphism on one factor and zero on the other. Hence kernels and images split in the isogeny category. Dimensions strictly decrease along a proper nonzero subobject, so every object has finite length. Together with the finite-dimensionality of Hom spaces proved in Section 15.1, this makes the isogeny category semisimple. In particular $\operatorname{End}^0(A)$ is a finite-dimensional semisimple $\mathbf Q$-algebra.

If $e\in\operatorname{End}^0(A)$ is idempotent, clear denominators and take the connected image of the resulting integral endomorphism. The complement construction shows that its inclusion into $A$ realizes $e$ in the isogeny category, so idempotents cut out abelian subvarieties up to isogeny. This statement does **not** imply that the $G_k$-representation $V_\ell A$ is semisimple for every possible ground field; that requires additional arithmetic hypotheses. What is available unconditionally is geometric splitting in the isogeny category and the corresponding splitting of $V_\ell A$ whenever an algebraic idempotent has been supplied.

## 16. Good reduction and integral families

### 16.1 Relative Jacobians over a base

The preceding constructions have relative forms, but their cleanest integral behavior requires clean fibers. Let $S$ be a connected locally noetherian scheme and let

$$
\pi:\mathcal C\longrightarrow S
$$

be smooth and proper of relative dimension one with geometrically connected fibers. The fppf relative Picard functor has an identity component

$$
\mathcal J=\operatorname{Pic}^0_{\mathcal C/S}
$$

represented by an abelian scheme over $S$. Its formation commutes with arbitrary base change, and its fiber at a geometric point $s$ is the Jacobian of $\mathcal C_s$. The tangent bundle along the identity is $R^1\pi_*\mathcal O_{\mathcal C}$, locally free of rank equal to the locally constant genus.

A relative degree-one divisor supplies an Abel--Jacobi map $\mathcal C\to\mathcal J$. Without one, the relative $\operatorname{Pic}^1$ is a $\mathcal J$-torsor. The canonical polarization nevertheless exists relatively: it can be constructed fppf-locally from theta and descends because translations do not alter the associated homomorphism.

### 16.2 A precise good-reduction statement

Let $R$ be a henselian discrete valuation ring with fraction field $K$ and residue field $\kappa$. Suppose $\mathcal C/R$ is smooth proper with geometrically connected fibers, and let $C=\mathcal C_K$. Then

$$
\mathcal J=\operatorname{Pic}^0_{\mathcal C/R}
$$

is an abelian scheme whose generic fiber is $J_C$ and whose special fiber is $J_{\mathcal C_\kappa}$. In particular $J_C$ has good reduction.

If $\ell$ is invertible in $R$, every $\mathcal J[\ell^m]$ is finite étale over $R$. After passing to a strict henselization, finite étale sections specialize uniquely, so inertia acts trivially on $T_\ell J_C$. Smooth proper base change gives the same conclusion cohomologically. With the specialization map taken in its canonical special-to-generic direction, it gives an isomorphism

$$
T_\ell J_{\mathcal C_{\bar\kappa}}
\simeq H^1(\mathcal C_{\bar\kappa},\mathbf Z_\ell(1))
\xrightarrow{\operatorname{sp}}
H^1(C_{K^s},\mathbf Z_\ell(1))
\simeq T_\ell J_C. \tag{16.1}
$$

Its inverse is the frequently used generic-to-special identification. Writing the arrow as in (16.1) keeps it consistent with the generization map on proper higher direct images. This statement requires $\ell\ne\operatorname{char}\kappa$.

The converse “unramified Tate module implies good reduction” is a separate criterion for abelian varieties and requires its own hypotheses. It is not needed for the forward integral passage here.

### 16.3 Extending maps and correspondences

A $K$-morphism of generic curves does not automatically extend to arbitrary chosen models. Under the present smooth proper hypothesis, a morphism that extends to an $R$-morphism $\mathcal C\to\mathcal C'$ induces pullback and norm on the relative Jacobians, compatible with both fibers and with specialization on prime-to-residue Tate modules.

For a correspondence, a convenient sufficient hypothesis is an $R$-scheme $\mathcal Z$ equipped with finite locally free maps

$$
\mathcal C\xleftarrow{p}\mathcal Z\xrightarrow{q}\mathcal C'
$$

whose generic fiber is the desired correspondence and whose relevant fibers are curves. Then

$$
q_*p^*:\mathcal J_{\mathcal C}\longrightarrow\mathcal J_{\mathcal C'}
$$

is defined over $R$ and specializes to the same pull--norm formula. Flatness prevents hidden vertical components, and finite local freeness makes the norm commute with base change. More general cycle closures can be used only after controlling excess intersection and vertical terms.

### 16.4 Limits of the integral picture

If the special fiber is nodal, $\operatorname{Pic}^0$ may be semiabelian rather than proper; if it has worse singularities, additive parts can appear. If the total family is merely proper and flat, the identity component need not be an abelian scheme. If $\ell$ equals the residue characteristic, $\mathcal J[\ell^m]$ need not be étale and inertia is not read from geometric torsion alone.

These are structural boundaries, not technical nuisances. Integral models of particular arithmetic curves, their singular fibers, and extension of their special correspondences demand additional geometry. Here we retain only the smooth proper good-reduction case, which is exactly the setting in which the Jacobian, prime-to-residue Tate module, and curve cohomology specialize without correction.

## 17. From a geometric correspondence to a Galois representation

### 17.1 The commuting actions

We can now assemble the bridge. Let $C/k$ be smooth proper and geometrically connected, let $J$ be its Jacobian, and fix $\ell\ne\operatorname{char}k$. A finite self-correspondence $\Gamma$ defined over $k$ gives

$$
\Gamma_J\in\operatorname{End}_k(J),
$$

and hence a continuous endomorphism

$$
T_\ell\Gamma_J\in
\operatorname{End}_{\mathbf Z_\ell[G_k]}(T_\ell J). \tag{17.1}
$$

Under Kummer, (17.1) is exactly

$$
(p_2)_*p_1^*:
H^1(\bar C,\mathbf Z_\ell(1))
\longrightarrow H^1(\bar C,\mathbf Z_\ell(1)). \tag{17.2}
$$

Thus geometry and arithmetic commute:

$$
\begin{array}{ccc}
T_\ell J&\xrightarrow{\Gamma}&T_\ell J\\
\sigma\downarrow&&\downarrow\sigma\\
T_\ell J&\xrightarrow{\Gamma}&T_\ell J.
\end{array}
$$

Transpose correspondence is adjoint for the Weil form and cup product. Composition of correspondences is composition of operators in the same order. These two facts are the indispensable bookkeeping behind geometric operator algebras.

### 17.2 The modular and Shimura correspondence pattern

Call any associative algebra generated by finite self-correspondences on $C$ a **Hecke-type correspondence algebra** for the purposes of this abstract discussion. The algebra need not be commutative in general; in the standard arithmetic applications one singles out a commuting subalgebra generated by correspondences away from the level and residue characteristic. We do not construct a particular modular or quaternionic curve here. The point is to make the geometric output completely explicit once its finite maps have been constructed.

The basic pattern already captures the correspondences used on modular and Shimura curves. Suppose a second smooth proper curve $C_r$ comes with two finite maps

$$
\alpha,\beta:C_r\rightrightarrows C.
$$

The cycle obtained by mapping $C_r$ to $C\times C$ through $(\alpha,\beta)$ acts by

$$
T_r=\beta_*\alpha^*:J_C\longrightarrow J_C. \tag{17.3a}
$$

Its transpose acts by $\alpha_*\beta^*$ and is the Rosati adjoint of $T_r$. On a modular curve, $\alpha$ and $\beta$ are the two degeneracy maps that forget or quotient the auxiliary cyclic subgroup. On a quaternionic Shimura curve, the analogous pair changes the local lattice or level structure at the auxiliary place. Once smooth proper models and finite maps are available, no new comparison theorem is required: (14.5) identifies (17.3a) with the pull--trace action on $H^1$. If the two maps and their moduli interpretation are defined over $k$, the operator commutes with $G_k$; if only their sum or double-coset cycle descends, it is that descended cycle which gives the $G_k$-equivariant operator.

If $\mathbb T\subset\operatorname{Corr}(C,C)$ is defined over $k$, there are compatible homomorphisms

$$
\mathbb T\longrightarrow\operatorname{End}_k(J)
\longrightarrow\operatorname{End}_{\mathbf Z_\ell[G_k]}(T_\ell J) \tag{17.3}
$$

and

$$
\mathbb T\longrightarrow
\operatorname{End}_{\mathbf Z_\ell[G_k]}
H^1(\bar C,\mathbf Z_\ell(1)). \tag{17.4}
$$

The two actions agree under (10.8). If $\mathbb T$ is stable under transpose, transpose becomes Rosati on $J$ and adjoint on cohomology.

This does not say that $\mathbb T$ acts faithfully. A cycle factoring through a point acts trivially on $J$ and $H^1$, and further relations may occur. It also does not say that every operator is diagonalizable. Integral algebras may have congruences and nilpotents after reduction.

### 17.3 Extracting finite-dimensional representations

Tensor (17.3) with $\mathbf Q_\ell$. The vector space

$$
V_\ell J=T_\ell J\otimes\mathbf Q_\ell
\simeq H^1(\bar C,\mathbf Q_\ell(1)) \tag{17.5}
$$

has dimension $2g$ and carries commuting continuous actions of $G_k$ and $\mathbb T$. Therefore every algebraic idempotent

$$
e\in\mathbb T\otimes\mathbf Q_\ell
$$

cuts out a finite-dimensional $G_k$-stable summand $eV_\ell J$. For generalized eigenspaces, one must first pass to the finite-dimensional image

$$
\mathbb T_{V,\ell}
=\operatorname{im}\bigl(\mathbb T\otimes\mathbf Q_\ell
\longrightarrow\operatorname{End}_{\mathbf Q_\ell}(V_\ell J)\bigr).
$$

If this image is commutative, then after a finite scalar extension $E/\mathbf Q_\ell$ its Artinian primary decomposition splits $V_\ell J\otimes E$ into simultaneous generalized eigenspaces. Each primary projector is a polynomial in correspondence operators, so it commutes with $G_k$; its summand is therefore $G_k$-stable and carries a continuous action. Localization of the abstract correspondence algebra is enough only after passing to the local factor that acts through this finite-dimensional image. With that qualification, a commuting family of modular or Shimura correspondences produces the desired finite-dimensional $\ell$-adic representations. Geometry supplies their Galois stability; determining that a chosen factor has dimension two, or identifying its Frobenius polynomials, requires arithmetic analysis of the particular curve and eigensystem.

At finite level, reduction of (17.3) gives

$$
\mathbb T\longrightarrow
\operatorname{End}_{(\mathbf Z/\ell^m\mathbf Z)[G_k]}
J[\ell^m](k^s),
$$

identified by Kummer with the action on $H^1(\bar C,\mu_{\ell^m})$. Hence integral lattices, residual modules, and rational eigenspaces all arise from the same geometric correspondences. Additional arithmetic arguments are needed to determine their dimensions, Frobenius polynomials, ramification, or irreducibility.

### 17.4 Conclusion

The Jacobian begins with the elementary observation that divisors of degree zero can be added. Its real force appears only after that group is allowed to vary in families. Rigidification removes scalar ambiguity, descent retains classes with no global representative, and large symmetric powers turn Riemann--Roch into a construction of a smooth proper connected group variety of dimension $g$.

The Abel--Jacobi map explains why this variety is the universal abelian recipient of the curve; pullback and norm explain its two variances. Kummer theory then identifies its prime-to-characteristic torsion, level by level and with arithmetic Galois action, with the first cohomology of roots of unity. The covariant convention leaves the twist visible:

$$
T_\ell J\simeq H^1(\bar C,\mathbf Z_\ell(1)),
\qquad
(T_\ell J)^\vee\simeq H^1(\bar C,\mathbf Z_\ell).
$$

The theta divisor supplies more than an isomorphism with the dual: it supplies the canonical positive principal polarization. Its Weil pairing is cup product followed by the curve trace, with exactly one surviving Tate twist. Consequently transpose cycles are simultaneously Rosati adjoints on $J$ and Poincaré adjoints on $H^1$.

This compatibility completes the geometric passage to representation theory. A correspondence defined over the ground field acts on $J$, on every torsion level, on $T_\ell J$, and on $H^1$, and all these actions agree and commute with $G_k$. A Hecke-type algebra of such cycles can therefore cut finite-dimensional continuous Galois representations out of the cohomology of a curve. In modular and Shimura settings, the moduli construction of the curves and their finite degeneracy maps supplies exactly the geometric input to this theorem. The bridge is complete: divisors have become abelian geometry, abelian geometry has become cohomology, and cohomology has become arithmetic representation.
