# Hecke Correspondences on Curves and Jacobians

## Contents

1. [From a relation to an operator](#1-from-a-relation-to-an-operator)
   - [Why maps are not enough](#11-why-maps-are-not-enough)
   - [Standing conventions](#12-standing-conventions)
   - [Finite correspondences and multiplicity](#13-finite-correspondences-and-multiplicity)
   - [The graph test](#14-the-graph-test)
2. [The calculus of finite correspondences](#2-the-calculus-of-finite-correspondences)
   - [Composition by fiber product](#21-composition-by-fiber-product)
   - [Flatness, excess intersection, and normalization](#22-flatness-excess-intersection-and-normalization)
   - [Transpose and degrees](#23-transpose-and-degrees)
   - [A first counterexample to scalar composition](#24-a-first-counterexample-to-scalar-composition)
3. [Divisors, Picard groups, and Jacobians](#3-divisors-picard-groups-and-jacobians)
   - [Pulling and pushing divisors](#31-pulling-and-pushing-divisors)
   - [The induced Jacobian homomorphism](#32-the-induced-jacobian-homomorphism)
   - [Projection formulas and composition](#33-projection-formulas-and-composition)
   - [Polarization adjoints](#34-polarization-adjoints)
4. [Cohomology and Tate modules](#4-cohomology-and-tate-modules)
   - [Pullback followed by trace](#41-pullback-followed-by-trace)
   - [Poincaré duality and transpose](#42-poincaré-duality-and-transpose)
   - [The covariant Tate-module comparison](#43-the-covariant-tate-module-comparison)
   - [Galois equivariance and descent](#44-galois-equivariance-and-descent)
5. [Modular Hecke correspondences](#5-modular-hecke-correspondences)
   - [The cyclic-isogeny moduli problem](#51-the-cyclic-isogeny-moduli-problem)
   - [The two degeneracy maps](#52-the-two-degeneracy-maps)
   - [Diamonds and scalar correspondences](#53-diamonds-and-scalar-correspondences)
   - [Primes in the level and the operator $U_q$](#54-primes-in-the-level-and-the-operator-u_q)
6. [Quaternionic Shimura correspondences](#6-quaternionic-shimura-correspondences)
   - [Changing Eichler level](#61-changing-eichler-level)
   - [Right translation and the missing forgetful map](#62-right-translation-and-the-missing-forgetful-map)
   - [The PEL isogeny interpretation](#63-the-pel-isogeny-interpretation)
   - [Stacks, coarse curves, and multiplicity](#64-stacks-coarse-curves-and-multiplicity)
7. [Agreement with adelic double cosets](#7-agreement-with-adelic-double-cosets)
   - [The orientation of the adelic span](#71-the-orientation-of-the-adelic-span)
   - [The right-coset calculation](#72-the-right-coset-calculation)
   - [Composition and coset multiplicities](#73-composition-and-coset-multiplicities)
   - [Normalizations and central character](#74-normalizations-and-central-character)
8. [One Hecke algebra, several realizations](#8-one-hecke-algebra-several-realizations)
   - [Abstract and image algebras](#81-abstract-and-image-algebras)
   - [Simultaneous actions](#82-simultaneous-actions)
   - [Adjoints and commuting families](#83-adjoints-and-commuting-families)
   - [Old-level maps](#84-old-level-maps)
9. [Integral extension and specialization](#9-integral-extension-and-specialization)
   - [Good integral data](#91-good-integral-data)
   - [Extending the two legs](#92-extending-the-two-legs)
   - [Specialization of cycles and operators](#93-specialization-of-cycles-and-operators)
   - [Proper smooth base change](#94-proper-smooth-base-change)
10. [Frobenius and Verschiebung](#10-frobenius-and-verschiebung)
    - [Four Frobenius conventions](#101-four-frobenius-conventions)
    - [Relative Frobenius and its transpose](#102-relative-frobenius-and-its-transpose)
    - [Action on the Jacobian and cohomology](#103-action-on-the-jacobian-and-cohomology)
    - [A convention table](#104-a-convention-table)
11. [The modular congruence relation](#11-the-modular-congruence-relation)
    - [The special-fiber subgroup scheme](#111-the-special-fiber-subgroup-scheme)
    - [The two components and their multiplicities](#112-the-two-components-and-their-multiplicities)
    - [Derivation of the correspondence identity](#113-derivation-of-the-correspondence-identity)
    - [The exact polynomial in every realization](#114-the-exact-polynomial-in-every-realization)
12. [The quaternionic good-prime relation](#12-the-quaternionic-good-prime-relation)
    - [Integral PEL hypotheses](#121-integral-pel-hypotheses)
    - [The local subgroup calculation](#122-the-local-subgroup-calculation)
    - [The resulting polynomial](#123-the-resulting-polynomial)
    - [What the theorem does not cover](#124-what-the-theorem-does-not-cover)
13. [Level primes, old level, and boundaries](#13-level-primes-old-level-and-boundaries)
    - [Why $U_q$ has no automatic good-prime polynomial](#131-why-u_q-has-no-automatic-good-prime-polynomial)
    - [Degeneracy adjunction](#132-degeneracy-adjunction)
    - [The old image and its Gram matrix](#133-the-old-image-and-its-gram-matrix)
    - [Nonexamples and failure modes](#134-nonexamples-and-failure-modes)
14. [Three worked geometries](#14-three-worked-geometries)
    - [$X_0(N)$](#141-x_0n)
    - [An elliptic quotient](#142-an-elliptic-quotient)
    - [A compact Shimura curve](#143-a-compact-shimura-curve)
15. [The common Hecke-action theorem](#15-the-common-hecke-action-theorem)
    - [Statement](#151-statement)
    - [Proof](#152-proof)
    - [The boundary with Galois-representation extraction](#153-the-boundary-with-galois-representation-extraction)
    - [Conclusion](#154-conclusion)

## 1. From a relation to an operator

### 1.1 Why maps are not enough

An endomorphism of a curve assigns one output to each input. A Hecke operation must do something different: from an elliptic curve it forms every quotient by a subgroup of a prescribed order, and from a lattice it forms every neighbor of a prescribed relative position. There is no preferred quotient or neighbor. The choices themselves form another curve, and the correct geometric object is therefore a span

$$
X\xleftarrow{\ s\ }Z\xrightarrow{\ t\ }Y.
$$

The letter $s$ means **declared source leg** and $t$ means **declared target leg**. The induced covariant operation will always be

$$
[Z]_* = t_*s^*.
$$

This convention is the spine of the book. It applies to divisors, degree-zero Picard varieties, Jacobian Tate modules, and first étale cohomology. A diagram drawn with its arrows in the opposite visual order does not change the declaration: source is the leg pulled back, target is the leg traced forward.

The need for this precision becomes acute in the adelic tower. Right multiplication by $h$ changes level. The span involving level intersection has two equally natural orientations, and reversing it changes $KhK$ into $Kh^{-1}K$. We orient it so that its pull--push action is the unnormalized right-coset operator already established on automorphic modules.

### 1.2 Standing conventions

Unless a relative base is displayed, $X,Y$, and $Z$ are proper curves over a field $k$. Curves called smooth are geometrically smooth, and connected curves called geometrically connected remain connected over a separable closure $k^s$. A prime $\ell$ used in cohomology is different from $\operatorname{char}k$.

A finite map between smooth proper connected curves is finite flat. This is the clean setting for pullback, norm, and trace. Over an arithmetic base we shall require finite locally free legs when base change of these operations matters. Proper but nonflat closures can acquire vertical components; finite generic fibers alone do not rule them out.

Our Tate module is covariant:

$$
T_\ell A=\varprojlim_n A[\ell^n](k^s),
$$

and a homomorphism $A\to B$ induces $T_\ell A\to T_\ell B$. For the Jacobian $J_X$,

$$
T_\ell J_X\simeq H^1(X_{k^s},\mathbf Z_\ell(1)),
\qquad
H^1(X_{k^s},\mathbf Z_\ell)\simeq T_\ell J_X(-1).
$$

The Galois action is arithmetic. Over $\mathbf F_q$, the element $\sigma_q:x\mapsto x^q$ is arithmetic Frobenius; geometric Frobenius is $\sigma_q^{-1}$. Arithmetic Frobenius acts on $\mathbf Z_\ell(1)$ by $q$.

At a split hyperspecial place of residue cardinality $q$, the undecorated $T_q$ is the unnormalized double-coset sum of degree $q+1$. The central operator $S_q$ is the one-coset translation by the scalar uniformizer. Its local polynomial is

$$
P_q(X)=X^2-T_qX+qS_q.
$$

On a central-character space, $S_q$ becomes the appropriate diamond or central-character scalar. At a prime in the level, $U_q$ denotes an oriented degree-$q$ correspondence and is never silently substituted for $T_q$.

### 1.3 Finite correspondences and multiplicity

A **finite effective correspondence** from $X$ to $Y$ is a proper curve $Z$, possibly disconnected, with finite maps

$$
s:Z\to X,\qquad t:Z\to Y.
$$

An integral correspondence may equivalently be represented by an integral curve in $X\times Y$ finite over both factors, together with its normalization. A general finite correspondence is an integral linear combination

$$
\Gamma=\sum_i m_i[Z_i],\qquad m_i\in\mathbf Z.
$$

The integers $m_i$ are part of the object. If two components have the same image in $X\times Y$, they do not collapse to one component: their coefficients add. If a generically finite map from a chosen parameter curve onto its cycle image has degree $e$, the image occurs with multiplicity $e$.

The requirement that both legs be finite is stronger than properness. A vertical component $\{x\}\times Y$ is proper but not finite over $X$ unless $Y$ is zero-dimensional. Such components act trivially on $H^1$ and on degree-zero Picard varieties, but allowing them too early obscures degree and composition. We begin with genuinely finite legs and mention vertical corrections only when specialization produces them.

Finite flatness solves a different problem from finiteness. It guarantees a well-behaved pullback of Cartier divisors and a norm commuting with arbitrary base change. Over a field, smoothness of the curves supplies flatness automatically. Over a DVR, it must be demanded or proved.

### 1.4 The graph test

Let $f:X\to Y$ be finite. Its graph, declared as a correspondence from $X$ to $Y$, has $s=1_X$ and $t=f$. It acts by

$$
[\Gamma_f]_* = f_*.
$$

The transpose graph is a correspondence from $Y$ to $X$ and acts by

$$
[\Gamma_f^t]_* = f^*.
$$

This test detects almost every variance mistake. In particular,

$$
\Gamma_f\circ\Gamma_f^t
$$

acts on $Y$ as $f_*f^*=[\deg f]$, whereas the reverse composite acts on $X$ as $f^*f_*$ and need not be scalar. If a proposed convention makes both composites multiplication by $\deg f$, it has erased the geometry of the fibers.

## 2. The calculus of finite correspondences

### 2.1 Composition by fiber product

Suppose

$$
X\xleftarrow{s}Z\xrightarrow{t}Y,
\qquad
Y\xleftarrow{u}W\xrightarrow{v}V
$$

are finite correspondences. A composable pair is a point of $Z\times_YW$, where the fiber product uses $t$ and $u$. Its two outer maps are finite, so it gives a correspondence from $X$ to $V$ after normalization and retention of scheme-theoretic multiplicity.

Cycle-theoretically,

$$
[W]\circ[Z]
=(p_{XV})_*
\bigl(p_{XY}^*[Z]\cdot p_{YV}^*[W]\bigr).
$$

The intersection product is not ornamental. If two branches meet nontransversely, the length of their local tensor product is the number with which the resulting component must occur. Set-theoretic composable pairs forget exactly the multiplicities that convolution remembers.

**Composition theorem.** For divisors modulo principal divisors, Jacobians, and prime-to-characteristic étale cohomology,

$$
([W]\circ[Z])_*=[W]_*\circ[Z]_*.
$$

**Proof strategy.** Pull everything to the fiber product, exchange flat pullback with proper pushforward in the Cartesian square, and apply the projection formula. The intersection multiplicity makes this base-change identity remain correct when components collide.

For finite flat legs, write the fiber square as

$$
\begin{array}{ccc}
Z\times_YW&\xrightarrow{\tilde t}&W\\
\downarrow\tilde u&&\downarrow u\\
Z&\xrightarrow{t}&Y.
\end{array}
$$

Then $u^*t_*=\tilde t_*\tilde u^*$ on divisor classes and on the corresponding trace maps. Hence

$$
v_*u^*t_*s^*
=v_*\tilde t_*\tilde u^*s^*,
$$

which is the pull--push formula for the outer legs. The same identity on cohomology follows from trace base change. $\square$

### 2.2 Flatness, excess intersection, and normalization

Why normalize an integral component? A curve in $X\times Y$ can be singular even when $X$ and $Y$ are smooth. Divisors and traces are cleanest on its normalization $Z^\nu$. The finite maps $Z^\nu\to X,Y$ retain the function-field degrees and all ramification indices. Normalization does not remove a coefficient already present in the cycle.

If all legs are finite flat, the fiber product is a local complete intersection of the expected dimension and its scheme lengths supply the correct coefficients automatically. Without flatness, a fiber product can contain a component supported entirely over a special point or special fiber. Such an excess component may act trivially on generic-fiber $H^1$ yet contribute to a special-fiber cycle. This is why extending a generic correspondence by taking its raw schematic closure is not enough for a specialization theorem.

A useful counterexample is supplied by two sections of a surface over a DVR which agree only in the closed fiber. Their generic intersection is empty, while their special-fiber intersection has positive length. A rule that specializes the reduced generic intersection would miss it; a rule that intersects closures records it. Hecke correspondences at good primes are arranged to be finite locally free, so this pathology does not arise. At level primes it can and does arise through intersecting branches.

### 2.3 Transpose and degrees

The transpose $Z^t$ interchanges $s$ and $t$. It reverses composition:

$$
(W\circ Z)^t=Z^t\circ W^t.
$$

If $X,Y,Z$ are geometrically connected, define

$$
d_s=\deg(s),\qquad d_t=\deg(t).
$$

On $H^0$, the operator $t_*s^*$ multiplies constants by $d_t$. On top cohomology, pullback by $s$ contributes $d_s$ while trace by $t$ preserves the normalized fundamental trace. These endpoint checks are valuable: the degree visible on constants belongs to the target leg, not automatically to the source leg.

For a Hecke correspondence at an unramified split prime, both legs usually have degree $q+1$. At an Iwahori prime, the oriented $U_q$ leg has degree $q$. On coarse curves these statements mean generic degrees. Ramification at cusps or elliptic points can change geometric fiber cardinalities without changing the degree counted with multiplicity.

### 2.4 A first counterexample to scalar composition

Let $f:X\to Y$ be a Galois double cover with involution $\iota$. Then

$$
f^*f_*=1+\iota^*
$$

on $J_X$ and on $H^1(X)$. The anti-invariant part is killed. Thus $f^*f_*$ is not $[2]$ unless the anti-invariant part vanishes. In the other order,

$$
f_*f^*=[2]
$$

on $J_Y$.

This elementary example anticipates the distinction between a Hecke operator and its transpose. Even when the two have the same generic degree, their composites need not be interchangeable. Self-adjointness arises from a polarization and, often, a central correction; it is not a consequence of equal degrees.

## 3. Divisors, Picard groups, and Jacobians

### 3.1 Pulling and pushing divisors

Let $s:Z\to X$ and $t:Z\to Y$ be finite maps of smooth proper curves. For a closed point $x$ of $X$, flat pullback is

$$
s^*[x]=\sum_{z\mapsto x}e(z/x)[z],
$$

where $e(z/x)$ is the ramification index. Proper pushforward is

$$
t_*[z]=[k(z):k(t(z))][t(z)].
$$

Consequently

$$
\Gamma_*D=t_*s^*D
$$

is a divisor on $Y$. Field norm gives

$$
t_*\operatorname{div}(g)
=\operatorname{div}(N_{k(Z)/k(Y)}g),
$$

so principal divisors go to principal divisors. The action descends to Picard groups.

Degree behaves predictably:

$$
\deg(t_*s^*D)=d_s\deg(D).
$$

Notice that $d_s$, rather than $d_t$, occurs here: pullback creates $d_s$ points counted with multiplicity, and pushforward preserves total degree over the ground field. This is compatible with the earlier $H^0$ test because divisor covariance and function trace test different ends of the correspondence.

### 3.2 The induced Jacobian homomorphism

Degree-zero classes remain degree zero, so the correspondence induces

$$
\Gamma_J=t_*s^*:J_X\longrightarrow J_Y.
$$

Here $s^*$ is pullback of line bundles and $t_*$ is the norm. For a line bundle $L$ on $Z$,

$$
\operatorname{Nm}_t(L)
=\det(t_*L)\otimes\det(t_*\mathcal O_Z)^{-1}.
$$

This formula works in families and is the reason finite local freeness is so valuable integrally. It also shows that the construction is a homomorphism of abelian varieties rather than merely a map on geometric divisor classes.

If the correspondence is defined over $k$, then $\Gamma_J$ is defined over $k$. A Galois-stable set of geometric components is insufficient unless the multiplicities and descent isomorphisms are stable as well. Summing the Galois conjugates gives a descended correspondence, but can multiply or merge components.

### 3.3 Projection formulas and composition

For a finite map $f:C\to D$, the norm projection formula is

$$
\operatorname{Nm}_f(L\otimes f^*M)
\simeq \operatorname{Nm}_f(L)\otimes M^{\otimes\deg f}.
$$

Its additive shadow is $f_*f^*=[\deg f]$ on Jacobians. Together with flat base change, it proves

$$
(\Delta\circ\Gamma)_J=\Delta_J\circ\Gamma_J.
$$

This proof also explains multiplicity. If one component of the fiber product maps with generic degree $e$ to its image, its norm is applied $e$ times. Replacing the scheme fiber product by its set of irreducible images would lose this factor and break composition.

### 3.4 Polarization adjoints

Every Jacobian has its canonical principal polarization

$$
\lambda_X:J_X\xrightarrow{\sim}J_X^\vee.
$$

For $u:J_X\to J_Y$, define its polarized adjoint by

$$
u^\dagger=\lambda_X^{-1}u^\vee\lambda_Y:J_Y\to J_X.
$$

**Transpose-adjoint theorem.** For a finite correspondence $\Gamma:X\dashrightarrow Y$,

$$
(\Gamma^t)_J=(\Gamma_J)^\dagger.
$$

**Proof strategy.** It suffices to treat one normalized component. Pullback and norm are dual under the Poincaré bundle. The theta polarizations identify each Jacobian with its dual, so reversing the two legs gives the dual homomorphism with exactly the displayed conjugation by polarizations.

The consequence is stronger than formal duality. A symmetric cycle gives a Rosati-self-adjoint endomorphism. If the transpose differs from the original correspondence by a central or diamond automorphism, that automorphism remains in the adjoint formula. It must not be suppressed merely because it acts as a scalar after a character is chosen.

## 4. Cohomology and Tate modules

### 4.1 Pullback followed by trace

Let $\Lambda$ be a finite ring of order prime to $\operatorname{char}k$, or let it be $\mathbf Z_\ell$ or $\mathbf Q_\ell$. A finite map of smooth proper curves has pullback and trace

$$
f^*:H^1(D,\Lambda)\to H^1(C,\Lambda),
\qquad
f_*:H^1(C,\Lambda)\to H^1(D,\Lambda).
$$

The trace is characterized by agreement with summing sheets over the étale locus and by the projection formula

$$
f_*(f^*a\smile b)=a\smile f_*b.
$$

Thus a correspondence acts by

$$
\Gamma_H=t_*s^*:H^1(X_{k^s},\Lambda)
\longrightarrow H^1(Y_{k^s},\Lambda).
$$

Pull--trace, not trace--pull, is our consistent variance. The graph of $f$ acts by $f_*$ and its transpose by $f^*$, exactly as on Jacobians.

### 4.2 Poincaré duality and transpose

Poincaré duality pairs

$$
H^1(X,\mathbf Z_\ell)
\times H^1(X,\mathbf Z_\ell(1))
\longrightarrow\mathbf Z_\ell.
$$

The projection formula gives

$$
\langle\Gamma_Ha,b\rangle_Y
=\langle a,(\Gamma^t)_Hb\rangle_X.
$$

No additional sign appears. Although both cohomology classes have degree one, adjunction moves pullback past trace; it does not swap the two cup factors. If one separately interchanges the arguments, graded commutativity introduces the familiar alternating sign.

Suppose $\Gamma^t=A\circ\Gamma$ for an automorphism $A$. Then $\Gamma^*=A\Gamma$ in the corresponding realization, with the order dictated by the cycle identity. At a spherical place, $A$ is often $S_q^{-1}$; at Iwahori level the transpose is generally a genuinely different operator $V_q$.

### 4.3 The covariant Tate-module comparison

Kummer theory identifies

$$
T_\ell J_X\simeq H^1(X_{k^s},\mathbf Z_\ell(1)).
$$

Under this identification, the square

$$
\begin{array}{ccc}
T_\ell J_X&\xrightarrow{T_\ell\Gamma_J}&T_\ell J_Y\\
\downarrow&&\downarrow\\
H^1(X_{k^s},\mathbf Z_\ell(1))&\xrightarrow{\Gamma_H}&
H^1(Y_{k^s},\mathbf Z_\ell(1))
\end{array}
$$

commutes. Pullback compatibility follows from naturality of Kummer. Norm compatibility follows because the norm on units, norm on line bundles, and cohomological trace form a morphism of Kummer sequences. Ramification multiplicities are already built into the finite-flat norm.

Untwisting changes Frobenius eigenvalues but not the geometric operator:

$$
H^1(X_{k^s},\mathbf Z_\ell)
\simeq T_\ell J_X(-1).
$$

It is therefore unsafe to quote one characteristic polynomial simultaneously on $T_\ell J$ and untwisted $H^1$ without converting the twist.

### 4.4 Galois equivariance and descent

If the two legs and the cycle multiplicities are defined over $k$, then pullback and trace commute with $G_k$. Hence

$$
\Gamma_H\in
\operatorname{End}_{\Lambda[G_k]}H^1(X_{k^s},\Lambda),
$$

and similarly

$$
T_\ell\Gamma_J\in
\operatorname{End}_{\mathbf Z_\ell[G_k]}T_\ell J_X.
$$

This commuting-square statement is the source of the later common Hecke and Galois action. It does not yet select an eigensystem or a two-dimensional summand.

If a cycle is defined only over $k'/k$, its operator commutes only with $G_{k'}$. A characteristic polynomial invariant under $G_k$ does not descend the operator. Descent requires the cycle, or its class with compatible descent data, to be invariant.

## 5. Modular Hecke correspondences

### 5.1 The cyclic-isogeny moduli problem

Fix a modular curve $X_H$ with level of conductor $N$, compactified by generalized elliptic curves, and choose enough auxiliary prime-to-$N$ level that the moduli problem is fine. Statements then descend to the stack and, with the qualifications below, to its coarse curve.

Let $q\nmid N$ be prime. Define $Z_q$ to classify tuples

$$
(E,\eta,D),
$$

where $(E,\eta)$ is an $H$-level elliptic curve and $D\subset E[q]$ is a cyclic finite locally free subgroup of rank $q$. Away from $q$, this means a line in the two-dimensional $\mathbf F_q$-space $E[q]$. There are $q+1$ such lines.

The quotient isogeny $\phi_D:E\to E/D$ is prime to $N$, so it transports the $H$-level. On the open curve both projections are finite étale of degree $q+1$. On the compactification they remain finite, though they may ramify at cusps.

### 5.2 The two degeneracy maps

The two maps are explicitly

$$
\alpha(E,\eta,D)=(E,\eta),
$$

and

$$
\beta(E,\eta,D)=(E/D,\eta_D).
$$

The first forgets the subgroup. The second quotients by it and transports level through $\phi_D$ on prime-to-$q$ torsion. Both operations extend over cusps using stable cyclic subgroups and the canonical contraction of generalized elliptic curves.

Which is source and which is target is a convention, not a feature of the picture. We orient the Hecke span to match the right-adelic operator in Chapter 7. Thus the declared source and target will be specified together with the adelic element. Equivalently, if one insists that $\alpha$ is source and $\beta$ is target, the corresponding adelic label may be $h^{-1}$ rather than $h$. The operator is never inferred from the left-to-right appearance of the diagram.

For the standard modular labeling adopted below, $T_q$ is the operator that agrees with the characteristic double coset $K\operatorname{diag}(q,1)K$ and has degree $q+1$ on constants. In the right-action convention of Chapter 7, the declared source is $\beta$ and the declared target is $\alpha$, so

$$
T_q=\alpha_*\beta^*.
$$

This explicit declaration is essential: the opposite pull--push is the transpose correspondence and differs from $T_q$ by the central factor described in Section 7.4.

### 5.3 Diamonds and scalar correspondences

On a $\Gamma_1(N)$ curve define, for $a\in(\mathbf Z/N\mathbf Z)^\times$,

$$
\langle a\rangle(E,P)=(E,aP).
$$

For full level, the analogous right action changes the chosen basis by the corresponding scalar or diagonal matrix, subject to the fixed Weil-pairing component. For $\Gamma_0(N)$, scalar multiplication preserves the cyclic subgroup and the usual diamond action is trivial unless extra nebentype data have been retained.

With the right-translation and pull--trace conventions fixed above, the central spherical operator of Books 89--90 is realized geometrically by

$$
S_q=\langle q\rangle^{-1}.
$$

The inverse is forced, not cosmetic: adelic right translation changes a covariant level point by precomposition, while $\langle a\rangle$ was defined by the point map $P\mapsto aP$. Equivalently, transpose must satisfy $T_q^*=S_q^{-1}T_q$. The abstract spherical polynomial remains

$$
X^2-T_qX+qS_q.
$$

On a space where the point-map diamond $\langle q\rangle$ has eigenvalue $\chi(q)$, $S_q$ therefore has eigenvalue $\chi(q)^{-1}$. Changing the moduli convention from $P$ to $a^{-1}P$ replaces every diamond by its inverse. Nothing mathematical changes, but every displayed identification with $S_q$ must change with it.

A central correspondence has one sheet. It need not be the identity: it can permute determinant components, alter a polarization similitude, or act by a nebentype scalar. Only after restricting to a central-character space may it be replaced by that scalar.

### 5.4 Primes in the level and the operator $U_q$

Suppose $q\mid N$ and, for clarity, write $N=Mq$ with $q\nmid M$. A point of $X_0(Mq)$ carries $(E,C_M,C_q)$. The two level maps to $X_0(M)$ are

$$
\delta_0(E,C_M,C_q)=(E,C_M),
$$

$$
\delta_1(E,C_M,C_q)=
(E/C_q,(C_M+C_q)/C_q).
$$

At fixed $K_0(q)$ level the oriented local correspondence attached to $\operatorname{diag}(q,1)$ has $q$ right cosets. Its unnormalized operator is $U_q$; constants have eigenvalue $q$. Its transpose is the opposite operator $V_q$, not generally a central multiple of $U_q$.

In characteristic $q$, $C_q$ may be connected or étale and the degeneracy maps can be inseparable on components. The hyperspecial $q+1$-neighbor calculation is no longer the local geometry. Consequently the good-prime polynomial cannot be carried over by replacing $T_q$ with $U_q$.

## 6. Quaternionic Shimura correspondences

### 6.1 Changing Eichler level

Let $B/F$ be a quaternion algebra split at exactly one real place and division globally, and let $K\subset B^\times(\mathbf A_{F,f})$ be a neat compact open arising from Eichler or PEL level. The Shimura curve is proper. At a finite place $\mathfrak q$ where $B$ is split and $K_{\mathfrak q}$ is hyperspecial, choose an integral splitting and

$$
h=h_{\mathfrak q}\sim
\begin{pmatrix}\varpi_{\mathfrak q}&0\\0&1\end{pmatrix}.
$$

Put

$$
K_h=K\cap hKh^{-1}.
$$

The inclusion $K_h\subset K$ gives a finite forgetful map

$$
\pi:X_{K_h}\to X_K.
$$

At neat characteristic-zero level its degree is

$$
[K:K_h]=q+1,
$$

where $q=|\mathcal O_F/\mathfrak q|$. With Iwahori level the analogous index is $q$.

### 6.2 Right translation and the missing forgetful map

Right adelic translation is

$$
R_h:X_{K_h}\longrightarrow X_{h^{-1}K_hh},
\qquad [z,g]\longmapsto[z,gh].
$$

It does **not** land directly on $X_K$. Rather,

$$
h^{-1}K_hh=h^{-1}Kh\cap K\subset K.
$$

Only after applying the forgetful map

$$
\pi_h:X_{h^{-1}K_hh}\to X_K
$$

does one obtain the second leg

$$
r_h=\pi_h\circ R_h:X_{K_h}\to X_K.
$$

Suppressing $\pi_h$ is not harmless shorthand: it gives $R_h$ the wrong codomain and conceals the conjugation direction. The two geometric maps are therefore

$$
X_K\xleftarrow{\pi}X_{K_h}
\xrightarrow{r_h}X_K.
$$

In Chapter 7 we declare the orientation that makes its action equal to $[KhK]$ rather than $[Kh^{-1}K]$.

### 6.3 The PEL isogeny interpretation

Under a PEL realization, a point of $X_{K_h}$ is an abelian variety with endomorphism action, polarization class, determinant condition, prime-to-$\mathfrak q$ level, and one additional finite subgroup of the relative position selected by $h$. The map $\pi$ forgets that subgroup. The map $r_h$ quotients by it and transports every part of the PEL datum.

The subgroup is not arbitrary. It is stable under the relevant order, has the rank prescribed by the local lattice quotient, and is isotropic or self-dual to the extent required for the quotient polarization. At a split hyperspecial place these conditions reduce locally to choosing a line in a two-dimensional residue space, hence $q+1$ possibilities.

This moduli interpretation proves algebraicity and supplies integral extension at good places. The adelic description proves independence from auxiliary trivializations. They are complementary descriptions of the same correspondence.

### 6.4 Stacks, coarse curves, and multiplicity

If the level is neat, every object has trivial stabilizer and the preceding maps are maps of schemes. If the level is not neat, the natural correspondence lives on smooth Deligne--Mumford stacks. Passing to coarse curves can introduce ramification at elliptic points. Generic degree remains the double-coset index, but a geometric fiber can have fewer distinct points because stabilizers identify them.

The correct integral multiplicity is the orbit multiplicity inherited from the finite level cover. One may compute it by passing to a neat normal cover, performing pull--push there, and descending with the full finite group action. Equivalently, one may use representable trace on the stack, or work on coarse curves while retaining ramification indices. Bare groupoid cardinality, which weights an isomorphism class by the reciprocal of its automorphism group, is not the primitive integral Hecke sum. Counting one representative per coarse isomorphism class generally undercounts.

This is the geometric analogue of stabilizer-weighted Brandt matrices. The unnormalized correspondence itself is integral; reciprocal stabilizer orders enter mass pairings and adjoints, not the primitive right-coset sum.

## 7. Agreement with adelic double cosets

### 7.1 The orientation of the adelic span

Let

$$
X_K=G(F)\backslash(\mathcal X\times G(\mathbf A_f)/K)
$$

denote either a Shimura curve or, with its boundary understood, an adelic modular curve. Put $K_h=K\cap hKh^{-1}$ and retain the maps

$$
\pi:X_{K_h}\to X_K,
\qquad
r_h=\pi_h\circ R_h:X_{K_h}\to X_K.
$$

On the finite automorphic modules of the earlier theory, the characteristic double coset acts by

$$
([KhK]f)(g)=\sum_{aK\subset KhK}f(ga).
$$

To obtain this formula by pull--push, we declare

$$
s=r_h,\qquad t=\pi,
$$

and define

$$
\boxed{\mathcal T_h=\pi_*r_h^*.} \tag{7.1}
$$

Thus the visually right-hand map is the source leg. If one instead declares $\pi$ to be the source, the resulting operator is the inverse-double-coset correspondence. Both are legitimate, but only (7.1) matches the fixed right-translation convention without an inversion.

In a modular cyclic-isogeny presentation, this declaration may orient an isogeny from its quotient back to its source. The underlying two maps remain the explicitly defined forgetful and quotient maps. The operator label records the declared orientation, not a claim that one elliptic curve is intrinsically the source.

### 7.2 The right-coset calculation

Choose right-coset representatives

$$
KhK=\coprod_{i=1}^d a_iK,
\qquad d=[K:K\cap hKh^{-1}].
$$

**Adelic comparison theorem.** On any finite automorphic function module with the right-translation convention, the pull--trace operator $\pi_*r_h^*$ is exactly $[KhK]$.

**Proof strategy.** A trace fiber of $\pi$ is indexed before stabilizer quotient by $K/K_h$. Pullback through $r_h$ evaluates the original function after right multiplication by $h$. The products $uh$, for $u\in K/K_h$, are precisely the right cosets in $KhK$.

Indeed, for an adelic representative $g$,

$$
(\pi_*r_h^*f)(g)
=\sum_{u\in K/K_h}(r_h^*f)(gu)
=\sum_{u\in K/K_h}f(guh).
$$

The stabilizer of $hK$ under left multiplication by $K$ is $K\cap hKh^{-1}=K_h$, so $u\mapsto uhK$ gives a bijection

$$
K/K_h\xrightarrow{\sim}KhK/K.
$$

Replacing the $u$ by the resulting $a_i$ gives

$$
(\pi_*r_h^*f)(g)=\sum_i f(ga_i).
$$

For a nontrivial weight, rewriting $ga_i$ in chosen global class representatives inserts exactly the rational weight matrices already present in the adelic formula. For a central character, central right translation commutes through the sum. $\square$

The proof also handles stabilizers. On a neat cover the trace is an ordinary sum of $d$ terms. Descending through the finite deck group groups those terms into stabilizer orbits but retains each orbit size as its multiplicity. The equivalent representable stack trace therefore still has degree $d$, even when the coarse fiber has fewer distinct points. Reciprocal stabilizer weights enter the mass pairing used for adjoints, not this integral transfer.

### 7.3 Composition and coset multiplicities

Let $C=KhK$ and $D=KjK$. Their convolution is

$$
\mathbf1_C*\mathbf1_D
=\sum_E m(C,D;E)\mathbf1_E,
$$

with $\operatorname{vol}(K)=1$. The integer

$$
m(C,D;E)
=\operatorname{vol}\{x\in C:x^{-1}e\in D\},
\qquad e\in E,
$$

counts right $K$-cosets with multiplicity.

On the geometric side, composing the spans takes their fiber product over $X_K$. A point is a pair of consecutive level modifications; several pairs can yield the same final modification. The scheme length of the corresponding component is exactly $m(C,D;E)$. Hence

$$
\mathcal T_h\mathcal T_j
=\sum_E m(C,D;E)\mathcal T_E.
$$

**Why the multiplicities agree.** Work first on the adelic uniformization. A composable pair is represented by $(x,y)\in C\times D$, and its final right translation is $xy$. Dividing by the intermediate right $K$-action identifies precisely the pairs occurring in the convolution integral. Because $K$ has volume one, every right coset contributes one. Algebraization preserves degrees and local lengths. At stacky points the same groupoid quotient introduces the same stabilizer ratios on both sides. Thus the analytic, moduli, and finite-set counts coincide.

This proves more than equality of eigenvalues. It gives equality of operator algebras before choosing an eigenvector.

### 7.4 Normalizations and central character

The comparison just proved uses the unnormalized finite sum. It has the following diagnostics:

- a spherical $T_q$ has $q+1$ terms and sends constants to $(q+1)$ times constants;
- an Iwahori $U_q$ has $q$ terms and sends constants to $q$ times constants;
- a scalar $S_q$ has one term;
- convolution is computed with $\operatorname{vol}(K)=1$.

The average $(q+1)^{-1}T_q$ and the spectral normalization $q^{-1/2}T_q$ are different operators. If either is used, every polynomial and adjoint formula must be rescaled.

At a spherical split place,

$$
(KhK)^{-1}=z_q^{-1}KhK
$$

for the central scalar $z_q$ represented locally by $\varpi_qI$. Consequently

$$
T_q^*=S_q^{-1}T_q
$$

for the mass or polarized pairing, before central specialization. On a character space $S_q$ is a scalar, but it remains in the local polynomial

$$
X^2-T_qX+qS_q.
$$

## 8. One Hecke algebra, several realizations

### 8.1 Abstract and image algebras

Let $\Sigma$ contain the primes of algebra or PEL ramification, nonhyperspecial level, auxiliary polarization degree, and any coefficient primes intentionally excluded. Define the abstract away-from-$\Sigma$ algebra

$$
\mathbb T^{\Sigma,\mathrm{abs}}_{\mathbf Z}
=\mathbf Z[T_v,S_v,S_v^{-1}:v\notin\Sigma],
$$

interpreted as the restricted tensor product of the local spherical algebras. Each generator is the geometric correspondence oriented as in Chapter 7.

For a realization $M$, its **image algebra** is

$$
\mathbb T^{\Sigma}(M)
=\operatorname{im}\bigl(
\mathbb T^{\Sigma,\mathrm{abs}}\to\operatorname{End}(M)
\bigr).
$$

The abstract algebra and an image algebra need not be isomorphic. A genus-zero curve has zero $H^1$, so its cohomological image algebra is zero even though its moduli correspondences and abstract double-coset algebra are nontrivial. On a fixed finite module, infinitely many abstract generators necessarily satisfy additional relations.

### 8.2 Simultaneous actions

For a proper smooth curve $X$ with Jacobian $J$, every integral correspondence acts compatibly on

$$
\operatorname{Div}(X),\quad
\operatorname{Pic}(X),\quad
J,\quad
J[\ell^n],\quad
T_\ell J,\quad
H^1(X_{k^s},\mathbf Z_\ell(1)),\quad
H^1(X_{k^s},\mathbf Q_\ell).
$$

Under Kummer, the Tate-module and twisted-cohomology actions are identical. The divisor action descends to the Jacobian because principal divisors are preserved. The same abstract Hecke algebra also acts on the corresponding automorphic modules through right-coset sums, and Chapter 7 identifies the geometric spans with those double cosets. When the adelic quotient is a finite class set, this specializes exactly to the stabilizer-sensitive construction of Books 89--90.

The phrase “one Hecke algebra acts” means that all maps originate from the same abstract correspondence algebra. It does not mean that the kernels in every realization coincide. We may form a common faithful image by mapping diagonally to a product of endomorphism rings, but even that depends on which realizations are included.

### 8.3 Adjoints and commuting families

Transpose is an anti-involution of the correspondence algebra. On Jacobians it becomes Rosati; on cohomology it becomes Poincaré adjoint; on finite automorphic modules it becomes inverse double coset under the mass pairing. Thus one geometric operation explains all three adjoint formulas.

At distinct places, correspondences commute because their level modifications occur in separate restricted-product factors. At one hyperspecial split place, the local lattice-neighbor calculation makes the spherical algebra commutative. At Iwahori level the whole local algebra need not commute, and $U_q^*=V_q$ with $V_q$ generally distinct.

Central operators commute everywhere. After a central character is fixed they become known scalars, but before that they can permute connected components. Component permutation is part of the geometry and cannot be reconstructed after the center has been discarded.

### 8.4 Old-level maps

Let $K'\subset K$. Forgetting level gives $\pi:X_{K'}\to X_K$. Pullback and trace induce

$$
\pi^*:J_K\to J_{K'},
\qquad
\pi_*:J_{K'}\to J_K,
$$

and similarly on cohomology, with

$$
\pi_*\pi^*=[\deg\pi].
$$

If $a$ is an admissible right-translation element giving another level map $r_a:X_{K'}\to X_K$, the elementary old image is

$$
\operatorname{im}(\pi^*)+\operatorname{im}(r_a^*)
\subset J_{K'}
$$

or the analogous submodule of $H^1(X_{K'})$. Away from the changed place, these maps intertwine Hecke operators.

No direct-sum or saturation claim is formal. The two images can intersect, and an integral orthogonal complement need not split. We retain only the geometrically proved old image and the adjunction formulas of Chapter 13.

## 9. Integral extension and specialization

### 9.1 Good integral data

Let $R$ be a henselian DVR with fraction field $K$, residue field $k$ of cardinality $q$, and residue characteristic $p$. A good setting consists of:

1. a smooth proper relative curve $\mathscr X/R$ with geometrically connected fibers;
2. a correspondence
   $$
   \mathscr X\xleftarrow{\mathscr s}\mathscr Z
   \xrightarrow{\mathscr t}\mathscr X
   $$
   whose legs are finite locally free;
3. a coefficient prime $\ell\ne p$;
4. moduli and level data unramified at $p$, with level modification prime to $p$ unless the correspondence is the deliberately studied $p$th one.

For modular curves this includes primes away from the level and auxiliary rigidification, with compactification smooth. For quaternionic curves it also requires the algebra and PEL datum to be unramified, a self-dual lattice, hyperspecial local level, polarization degree prime to $p$, and the correct unramified determinant local model.

Saying only “$p$ does not divide the quaternion discriminant” is insufficient. Auxiliary PEL ramification or nonself-dual level can still spoil good reduction.

### 9.2 Extending the two legs

At a prime away from the degree of a modular level change, cyclic subgroups form a finite étale scheme and quotients commute with base change. The forgetful and quotient maps therefore extend over $R$. On compactifications, stable generalized elliptic curves supply the same extension at cusps.

For a PEL curve, the prime-to-$p$ subgroup selected by $h$ is finite étale, stable under the endomorphism order, and compatible with polarization. Quotienting by it preserves the determinant condition and the hyperspecial $p$-adic lattice. Hence both the inclusion-of-level leg and the translated-then-forgotten leg extend.

Finite local freeness is decisive. It ensures constant scheme-theoretic degree, defines norm on relative Picard schemes, and makes both norm and trace commute with base change. A proper extension that is merely generically finite does not suffice.

### 9.3 Specialization of cycles and operators

Write $X_\eta$ and $X_s$ for the geometric generic and special fibers. Base change gives a special correspondence

$$
X_s\xleftarrow{s_s}Z_s\xrightarrow{t_s}X_s.
$$

Because the legs are finite locally free, no hidden vertical component appears and multiplicities are the fiber lengths of the same finite algebra. On relative Jacobians,

$$
(t_*s^*)_s=(t_s)_*(s_s)^*.
$$

The same formula holds for divisors and Picard groups.

For cohomology, trace base change gives a commutative square

$$
\begin{array}{ccc}
H^1(X_{\bar\eta},\mathbf Q_\ell)&\xrightarrow{t_*s^*}&
H^1(X_{\bar\eta},\mathbf Q_\ell)\\
\downarrow\mathrm{sp}&&\downarrow\mathrm{sp}\\
H^1(X_{\bar s},\mathbf Q_\ell)&\xrightarrow{(t_s)_*(s_s)^*}&
H^1(X_{\bar s},\mathbf Q_\ell).
\end{array} \tag{9.1}
$$

Thus a cycle relation proved on the special fiber becomes an operator relation on the generic fiber once specialization is an isomorphism.

### 9.4 Proper smooth base change

Smooth proper base change makes the vertical maps in (9.1) isomorphisms for $\ell\ne p$. It also shows that inertia acts trivially on generic-fiber $H^1$. The relative Jacobian is an abelian scheme, and prime-to-$p$ torsion specializes isomorphically.

**Specialization theorem.** Under the hypotheses of Section 9.1, every polynomial relation among the specialized correspondences on $H^1(X_{\bar s},\mathbf Q_\ell)$ holds for their generic-fiber operators under the canonical specialization identification.

**Proof.** Pullback commutes with arbitrary base change, trace does so for finite locally free maps, and proper smooth base change identifies the two cohomology groups. Therefore every word in the correspondence operators commutes with specialization. Apply this to the polynomial relation. $\square$

If the model is only semistable, proper base change alone compares the generic fiber with nearby cycles, not directly with ordinary $H^1$ of the special fiber. Vanishing cycles and monodromy can intervene. This is the principal reason the theorem does not cover $U_q$ at a level prime.

## 10. Frobenius and Verschiebung

### 10.1 Four Frobenius conventions

Let $X/\mathbf F_q$ be a smooth proper curve. Four related operations must be separated.

The absolute scheme Frobenius raises functions to their $q$th powers. The relative Frobenius

$$
F_{X/\mathbf F_q}:X\to X^{(q)}
$$

is a morphism over $\mathbf F_q$ after the Frobenius twist is recorded. Since the base is $\mathbf F_q$, there is a canonical identification $X^{(q)}\simeq X$, but retaining the twist while deriving formulas prevents type errors.

Arithmetic Galois Frobenius is

$$
\sigma_q:x\mapsto x^q
$$

on $\overline{\mathbf F}_q$. Geometric Galois Frobenius is $\phi_q=\sigma_q^{-1}$. On geometric points of an abelian variety defined over $\mathbf F_q$, the covariant Tate-module action of $\sigma_q$ agrees with its algebraic $q$-power Frobenius endomorphism.

On untwisted cohomology, functoriality is contravariant. Because

$$
T_\ell J_X\simeq H^1(X,\mathbf Z_\ell(1)),
$$

the same arithmetic element acts on untwisted $H^1$ by the Tate-module Frobenius divided by $q$.

### 10.2 Relative Frobenius and its transpose

For an elliptic curve or abelian variety $A/\mathbf F_q$, relative Frobenius and Verschiebung are isogenies

$$
F:A\to A^{(q)},
\qquad
V:A^{(q)}\to A
$$

satisfying

$$
V\circ F=[q]_A,
\qquad
F\circ V=[q]_{A^{(q)}}.
$$

After identifying twists over $\mathbf F_q$, on $V_\ell A$ one has

$$
V=qF^{-1}. \tag{10.1}
$$

For a curve, the graph of $F_X$ and its transpose induce adjoint maps on the Jacobian. Under the canonical polarization, the transpose is the Verschiebung-type endomorphism. For the right-action Hecke span, the special-fiber identity has the transpose graph first and the $S_q$-twisted forward graph second. It becomes the operator identity

$$
V+S_qF=qF^{-1}+S_qF. \tag{10.2}
$$

### 10.3 Action on the Jacobian and cohomology

Let $F$ denote arithmetic Frobenius on $T_\ell J_X$. Then the corresponding actions are:

$$
\begin{array}{c|c}
\text{realization}&\text{arithmetic Frobenius}\\ \hline
T_\ell J_X&F\\
H^1(X,\mathbf Z_\ell(1))&F\\
H^1(X,\mathbf Z_\ell)&q^{-1}F.
\end{array}
$$

Geometric Frobenius on untwisted $H^1$ is the inverse of $q^{-1}F$, hence

$$
\phi_q=qF^{-1}. \tag{10.3}
$$

For an elliptic curve with trivial central factor, (10.3) is Verschiebung on the Tate module after the cohomological identification. Its eigenvalues have complex size $q^{1/2}$, while arithmetic Frobenius on untwisted $H^1$ has their reciprocals. Both statements are correct because the conventions differ by inversion and twist.

### 10.4 A convention table

Suppose the right-action operator $T$ satisfies the good-prime relation for geometric Frobenius $G$ on untwisted cohomology:

$$
G^2-TG+qS=0. \tag{10.4}
$$

Let $F$ be arithmetic Frobenius on $T_\ell J$ and put $A=q^{-1}F$ for arithmetic Frobenius on untwisted $H^1$. Since $G=A^{-1}=qF^{-1}$, the equivalent monic polynomials are

| Space and operator | Polynomial |
|---|---|
| $T_\ell J$ or $H^1(1)$, arithmetic $F$ | $X^2-S^{-1}TX+qS^{-1}$ |
| untwisted $H^1$, arithmetic $A=q^{-1}F$ | $X^2-q^{-1}S^{-1}TX+q^{-1}S^{-1}$ |
| untwisted $H^1$, geometric $G=A^{-1}$ | $X^2-TX+qS$ |

The first two rows use that $S$ is invertible, as it is for a central correspondence. Multiplying either by $S$ gives a useful nonmonic integral form. On an eigenspace where $S$ acts by $s$, the determinant on the Tate module is $q/s$, while the determinant of geometric Frobenius on untwisted $H^1$ is $qs$.

For trivial diamond $S=1$, the first and third polynomials coincide. This accidental symmetry is why the pull--push reversal remains invisible on $X_0(N)$ and appears only when the central action is retained.

## 11. The modular congruence relation

### 11.1 The special-fiber subgroup scheme

Let $q\nmid N$ and take a fine auxiliary level prime to $q$. The modular curve $\mathscr X_H$ has smooth proper reduction at $q$. The generic Hecke correspondence $\mathscr Z_q$ classifies a cyclic subgroup $D\subset E[q]$ and extends as a finite locally free correspondence over the localization at $q$.

We now study its special fiber rather than merely quoting a polynomial. Over the ordinary locus of a characteristic-$q$ elliptic curve,

$$
0\longrightarrow E[q]^0\longrightarrow E[q]
\longrightarrow E[q]^{\mathrm{et}}\longrightarrow0
$$

has connected and étale factors of rank $q$. The unique connected cyclic subgroup is

$$
\ker(F_{E/k}),
$$

and quotient by it is relative Frobenius

$$
E\longrightarrow E^{(q)}.
$$

The opposite generic direction is described by the dual isogeny, Verschiebung. On a fixed-source presentation this direction appears after a Frobenius twist; on a fixed-target presentation it is literally the transpose Frobenius isogeny. These are the two generic branches of the special-fiber moduli problem.

At a supersingular point the connected--étale splitting disappears. That does not create a third one-dimensional component. The closures of the two ordinary branches meet there, and local deformation theory determines their intersection multiplicity. Auxiliary fine level ensures this is a scheme-local calculation rather than a quotient by automorphisms.

### 11.2 The two components and their multiplicities

Let $\mathcal F$ denote the graph of relative Frobenius on the special modular curve, oriented in the declared source--target coordinates $(\beta,\alpha)$, and let $\mathcal V=\mathcal F^t$. This point about coordinates resolves an apparent reversal. On the connected-kernel locus the quotient map itself is Frobenius, but it is the source leg $\beta$; the image of that branch in source--target order is therefore the transpose graph, with no central correction. On the opposite branch, comparison of the transported prime-to-$q$ level uses the dual isogeny and multiplication by $q$. In the right-translation convention this contributes $S_q=\langle q\rangle^{-1}$ to the forward graph.

The special correspondence has the cycle decomposition

$$
\boxed{
[\mathscr Z_{q,s}]=[\mathcal F^t]+S_q[\mathcal F].} \tag{11.1}
$$

There is no coefficient $q$ in front of either cycle. The factor $q$ appears when the transpose Frobenius acts: its isogeny is Verschiebung and satisfies $V=qF^{-1}$ on prime-to-$q$ Tate modules. Taking transpose in (11.1) gives $S_q^{-1}$ times the original cycle, exactly as the inverse-double-coset formula requires.

Why do both components occur with multiplicity one? On the ordinary locus the moduli deformation parameter together with the choice of the connected or opposite canonical direction gives a generically reduced branch. Each branch maps generically isomorphically to the corresponding Frobenius graph. A generic point therefore has local length one. Since cycle multiplicity is determined at the generic point of a component, the supersingular intersections do not alter those coefficients.

The total degree still equals $q+1$. The Frobenius graph and its transpose do not each have degree one with respect to both legs. Frobenius is purely inseparable of degree $q$, while its graph has one projection of degree one and the other of degree $q$. Depending on the declared orientation, the two components contribute degrees $1$ and $q$. Thus (11.1) passes the $q+1$ degree test without an extra cycle coefficient.

### 11.3 Derivation of the correspondence identity

We give the derivation in four steps.

**Step 1: identify the dense ordinary branches with the declared orientation.** Over an ordinary elliptic curve, the rank-$q$ subgroup chosen by the integral moduli problem has either connected or opposite type. In the connected case, $D=\ker F$ and the quotient is $F:E\to E^{(q)}$. Since $\beta$ is the declared source and $\alpha$ the declared target, this quotient branch maps to the transpose Frobenius graph. In the opposite case, dualizing the quotient identifies the other branch with the forward Frobenius graph. Hence the two reduced one-dimensional loci have precisely the two orientations occurring in (11.1).

**Step 2: compute transported level.** Let $P$ be a prime-to-$q$ level point. The connected-kernel branch is already the transpose graph of the point map $(E,P)\mapsto(E^{(q)},F(P))$, so it carries no diamond. On the opposite branch, if $P'$ is the level point on the quotient, the identity $F(P')=qP$ shows that the source level is obtained by multiplying the Frobenius-transported level by $q^{-1}$. This is $\langle q\rangle^{-1}=S_q$. For full level the same calculation is performed on the whole basis and its Weil pairing. Thus both the position and the exponent of $S_q$ are consequences of the declared span.

**Step 3: determine multiplicities.** The ordinary locus is dense in every component. The local moduli rings at its generic points are reduced, and each of the two maps to the relevant Frobenius graph has generic degree one. Thus both coefficients are one.

**Step 4: close across supersingular points and cusps.** Properness of the compactified correspondence makes the closure unique. Equality of cycles on a dense open determines equality globally because any difference would be supported in dimension zero, which cannot be a one-cycle. At cusps, Tate-curve quotients yield the same two Frobenius directions. At supersingular points the two closures meet, but their intersection changes the geometry of the total curve, not their generic cycle coefficients.

These steps prove (11.1) as a cycle identity on the special fiber. Applying the pull--push functor gives

$$
T_q=V+S_qF. \tag{11.2}
$$

Using $V=qF^{-1}$ yields

$$
T_q=qF^{-1}+S_qF. \tag{11.3}
$$

Multiplication by $F$ gives the integral, generally nonmonic relation on the covariant Tate module

$$
\boxed{S_qF^2-T_qF+q=0.} \tag{11.4}
$$

Equivalently, geometric Frobenius $G=qF^{-1}$ on untwisted cohomology satisfies the polynomial in the normalization of Books 89--90:

$$
\boxed{G^2-T_qG+qS_q=0.} \tag{11.5}
$$

This is a derivation from the special-fiber moduli description: the two terms arise from the two subgroup-scheme directions, the central factor from transported level, and the factor $q$ from Frobenius--Verschiebung duality. It also explains why the abstract Hecke polynomial belongs directly to geometric Frobenius on untwisted cohomology for this right-action convention.

### 11.4 The exact polynomial in every realization

Let $\ell\ne q$. Smooth proper base change transports the cycle identity, and hence both (11.4) and (11.5), from the special fiber to generic cohomology. Since $S_q$ is invertible, the covariant Tate-module and twisted-cohomology relation has the monic form

$$
\boxed{
F_{q,\mathrm{arith}}^2
-S_q^{-1}T_qF_{q,\mathrm{arith}}
+qS_q^{-1}=0
\quad\text{on }T_\ell J\simeq H^1(1).} \tag{11.6}
$$

On any subspace on which $T_q$ and $S_q$ act by scalars $t_q$ and $s_q$, Frobenius is annihilated by

$$
X^2-s_q^{-1}t_qX+qs_q^{-1}.
$$

If that Frobenius-stable subspace is two-dimensional and the quadratic is its full characteristic polynomial, its determinant is $q/s_q$, not merely $q$. On a larger scalar-Hecke subspace, the minimal polynomial divides the displayed quadratic; the operator relation alone does not assert dimension two. For $\Gamma_1(N)$, if the point-map diamond $\langle q\rangle$ acts by $\chi(q)$, then $s_q=\chi(q)^{-1}$ and the Tate-module determinant is $q\chi(q)$. For $X_0(N)$ with no extra character, $s_q=1$.

On untwisted $H^1$, arithmetic Frobenius $A_q$ satisfies

$$
A_q^2-q^{-1}S_q^{-1}T_qA_q
+q^{-1}S_q^{-1}=0. \tag{11.7}
$$

Geometric Frobenius $G_q=A_q^{-1}$ satisfies

$$
G_q^2-T_qG_q+qS_q=0,
$$

which is (11.5). Equations (11.5)--(11.7) are equivalent, not competing normalizations. If an author calls $x\mapsto x^q$ geometric Frobenius, the names exchange; the operator formulas do not. The safe statement always names the action and the twist.

**Worked check: $X(1)$.** Its $H^1$ and Jacobian vanish, so (11.4) is vacuous there even though the correspondence exists. On divisors, constants see degree $q+1$, and the identity

$$
q+1=1+q
$$

is the endpoint shadow of the Frobenius and transpose degrees. A rich correspondence need not produce weight-two cohomology.

## 12. The quaternionic good-prime relation

### 12.1 Integral PEL hypotheses

Let $X_K$ be a compact quaternionic Shimura curve with a PEL realization over its reflex field. Fix a finite place $v$ of good reduction corresponding to a split place $\mathfrak q$ of $F$, and assume that the chosen unramified local identification gives the same residue field on both sides. Write

$$
q=|\kappa(v)|=|\mathcal O_F/\mathfrak q|.
$$

Assume:

- the quaternionic and auxiliary PEL algebras and involutions are unramified at $v$;
- the polarization lattice is self-dual and its degree is prime to the residue characteristic;
- $K_{\mathfrak q}$ is hyperspecial and all auxiliary level at the residue characteristic is hyperspecial;
- the determinant local model is the smooth one-dimensional unramified model;
- the prime-to-residue level is neat, or the argument is made on the stack and descended through a tame neat cover.

Under these hypotheses the integral curve is smooth proper, and the $\mathfrak q$-neighbor correspondence extends with finite locally free legs. These assumptions are part of the theorem. A bare statement about the discriminant of the quaternion algebra would not justify them.

### 12.2 The local subgroup calculation

At $\mathfrak q$, the endomorphism-stable Tate lattice is locally a rank-two module over $\mathcal O_{F_\mathfrak q}$. The hyperspecial Hecke modification chooses a rank-one quotient of its residue space, hence $q+1$ choices. Over the residue field of cardinality $q$, the relevant $p$-divisible group with its order action has two extremal modifications selected by the Hodge filtration: the Frobenius direction and its dual Verschiebung direction.

The determinant condition ensures that these are one-dimensional branches rather than higher-dimensional strata. Polarization identifies the dual modification and records its similitude. With the source leg declared to be right translation and the target leg forgetful, the transpose Frobenius branch has no central correction, while transport through the dual modification contributes the central scalar correspondence $S_\mathfrak q$ to the forward branch.

On the $\mu$-ordinary PEL locus, therefore, the specialized Hecke cycle is

$$
[\mathscr Z_{\mathfrak q,s}]
=[\mathcal F_\mathfrak q^t]
+S_\mathfrak q[\mathcal F_\mathfrak q]. \tag{12.1}
$$

The proof of multiplicity one is the same generic-local argument as in the modular case. The local model for the additional minuscule modification is the rank-one $\operatorname{GL}_2$ model. Along its two generic strata it is reduced, and each stratum maps with generic degree one to the appropriate Frobenius graph. After an unramified strict-henselian base change, let $\widehat R$ be the completed valuation ring. At a point where the strata meet, the completed local equation has the semistable form

$$
\widehat R[[x,y]]/(xy-u\varpi_v)
$$

for a unit $u$. Its special fiber is therefore the union of the two reduced branches $x=0$ and $y=0$, each with coefficient one. The complement of the $\mu$-ordinary locus is finite on a curve, so equality of one-cycles extends across it.

This argument is not merely analogy with modular curves. It uses the integral PEL moduli problem: the two subgroup types arise from the local $p$-divisible group with endomorphisms, the central factor from the polarization similitude, and reducedness from the unramified local model.

### 12.3 The resulting polynomial

Let $F_\mathfrak q$ be arithmetic Frobenius acting on the covariant Tate module of the Jacobian of the special fiber. The transpose branch is Verschiebung and satisfies

$$
V_\mathfrak q=qF_\mathfrak q^{-1}.
$$

Applying the correspondence action to (12.1) gives

$$
T_\mathfrak q
=qF_\mathfrak q^{-1}+S_\mathfrak qF_\mathfrak q,
$$

hence

$$
\boxed{
F_\mathfrak q^2
-S_\mathfrak q^{-1}T_\mathfrak qF_\mathfrak q
+qS_\mathfrak q^{-1}=0.} \tag{12.2}
$$

Equivalently, geometric Frobenius $G_\mathfrak q=qF_\mathfrak q^{-1}$ on untwisted cohomology satisfies

$$
G_\mathfrak q^2-T_\mathfrak qG_\mathfrak q
+qS_\mathfrak q=0. \tag{12.3}
$$

Smooth proper base change transports these relations to the generic fiber for every $\ell$ different from the residue characteristic. On a subspace where the two Hecke operators act by $t_\mathfrak q,s_\mathfrak q$, arithmetic Frobenius on $T_\ell J$ is annihilated by

$$
X^2-s_\mathfrak q^{-1}t_\mathfrak qX
+qs_\mathfrak q^{-1},
$$

while geometric Frobenius on untwisted $H^1$ is annihilated by

$$
X^2-t_\mathfrak qX+qs_\mathfrak q.
$$

Either is the characteristic polynomial only after a separate two-dimensionality statement; no such extraction is being made here. The central eigenvalue can encode a reduced-norm character or PEL multiplier. It is not automatically one.

### 12.4 What the theorem does not cover

Relations (12.2)--(12.3) are not asserted at:

- a place where the quaternion algebra is division;
- an Iwahori or deeper level place;
- a place where the auxiliary PEL algebra or polarization lattice is ramified;
- a place where the integral model is merely semistable;
- the coefficient prime when prime-to-characteristic étale comparison is unavailable in the stated form.

At a division place there is no $q+1$-neighbor spherical correspondence. At Iwahori level the local modification is oriented and has $q$ branches. At a semistable place nearby cycles, rather than ordinary special-fiber cohomology, control the generic fiber. None of these failures is repaired by retaining the same formal polynomial.

## 13. Level primes, old level, and boundaries

### 13.1 Why $U_q$ has no automatic good-prime polynomial

At hyperspecial level, the local moduli space remembers a vertex in the lattice tree and the $q+1$ neighbors are symmetric. At $K_0(q)$ level it remembers an oriented edge. The operator $U_q$ follows the $q$ forward continuations; its transpose $V_q$ follows the reverse direction. The Weyl element that exchanges directions is not in the level.

Geometrically, the integral $X_0(q)$-type model has two components meeting at supersingular points. The degeneracy maps restrict through Frobenius and Verschiebung on different components, but the model is not smooth. Smooth proper base change cannot identify generic cohomology with ordinary cohomology of this reducible special fiber. The good-prime derivation therefore breaks in two places: the local correspondence is different, and the specialization theorem has different hypotheses.

A $U_q$ eigenvalue can satisfy a relation after imposing ordinarity, newness, or a local representation type. Those are extra theorems. They do not follow from the hyperspecial congruence relation by formal substitution.

### 13.2 Degeneracy adjunction

Let $\alpha,\beta:X_{K_0(q)}\to X_K$ be the two degeneracy maps. Pullback gives

$$
\delta=(\alpha^*,\beta^*):
H^1(X_K)^{\oplus2}\longrightarrow H^1(X_{K_0(q)}).
$$

Trace gives the adjoint column

$$
\delta^*=\binom{\alpha_*}{\beta_*}
$$

with respect to Poincaré pairings, provided the source and target measures or polarizations are normalized compatibly. Thus

$$
\delta^*\delta=
\begin{pmatrix}
\alpha_*\alpha^*&\alpha_*\beta^*\\
\beta_*\alpha^*&\beta_*\beta^*
\end{pmatrix}. \tag{13.1}
$$

The diagonal entries are the degrees. The off-diagonal entries are explicit Hecke correspondences, with a central or transpose correction determined by orientation. Formula (13.1), rather than a memorized matrix with unstated normalization, is the reliable Gram-matrix statement.

The same construction holds on Jacobians. Transpose of a degeneracy graph is its polarization adjoint, so every entry of (13.1) has the same meaning on Tate modules and cohomology.

### 13.3 The old image and its Gram matrix

Define the geometrically proved old image by

$$
H^1(X_{K_0(q)})^{\mathrm{old},K}
=\alpha^*H^1(X_K)+\beta^*H^1(X_K).
$$

It is stable under Hecke operators away from $q$, because those correspondences base-change through both degeneracy maps. The analogous abelian subvariety is the image of

$$
J_K\times J_K\longrightarrow J_{K_0(q)},
\qquad (x,y)\longmapsto\alpha^*x+\beta^*y.
$$

Up to isogeny, polarizations provide a complementary abelian subvariety. Integrally, the image can fail to be saturated and the orthogonal complement need not split. We therefore do not define a canonical integral new direct summand here. The precise old/new representation theory requires further algebra beyond the geometric adjunction just proved.

### 13.4 Nonexamples and failure modes

Several plausible extensions are false.

First, a finite correspondence on the generic fiber need not extend finite flatly. Its closure may gain vertical components. Second, a proper regular model need not be smooth; a nodal special fiber has vanishing cycles. Third, a coarse level map need not be étale even when the stack map is, because stabilizers change. Fourth, the reduced points of a characteristic-$q$ subgroup do not determine its finite-flat subgroup scheme. Fifth, equality of two correspondences on ordinary geometric points does not determine their cycle multiplicities unless generic reducedness is proved.

Finally, $T_q$ and $U_q$ are not two names for the same operator. The first is spherical of degree $q+1$ at a prime away from level; the second is oriented of degree $q$ at a level prime. Their adjoints and integral fibers are different.

## 14. Three worked geometries

### 14.1 $X_0(N)$

Let $q\nmid N$. A point of the correspondence is

$$
(E,C_N,D_q),
$$

with $C_N$ cyclic of rank $N$ and $D_q$ cyclic of rank $q$. The maps are

$$
\alpha(E,C_N,D_q)=(E,C_N),
$$

$$
\beta(E,C_N,D_q)=
(E/D_q,(C_N+D_q)/D_q).
$$

Because $(N,q)=1$, the image of $C_N$ remains cyclic of rank $N$. Both generic degrees are $q+1$. The Hecke endomorphism on $J_0(N)$ is the oriented pull--norm operation matching $K_0(N)\operatorname{diag}(q,1)K_0(N)$.

There is no nontrivial diamond factor in the basic $\Gamma_0$ realization, so

$$
F_q^2-T_qF_q+q=0
$$

on $T_\ell J_0(N)$ at good $q$. On untwisted $H^1$, the same monic polynomial belongs to geometric Frobenius; arithmetic Frobenius has the divided polynomial of (11.7).

**Concrete degree check.** Take a divisor class represented by a noncuspidal point $(E,C_N)$. Because the declared source is $\beta$, pulling to the correspondence lists the $q+1$ cyclic isogenies whose quotient is $(E,C_N)$, counted with automorphism and ramification multiplicity; pushing along $\alpha$ returns their source points. Thus $T_q$ is an incoming-neighbor sum, not an average. The outgoing quotient-neighbor sum is its transpose and equals $S_q^{-1}T_q$ in the spherical convention. At an elliptic point some sources can be isomorphic, but their occurrences remain separate multiplicities.

If $q\mid N$, the same formula is unavailable. The $U_q$ correspondence has $q$ forward choices and the integral model is semistable rather than smooth.

### 14.2 An elliptic quotient

Suppose an idempotent or a geometrically defined quotient map cuts an elliptic curve $A$ from $J_0(N)$ up to isogeny, and that the quotient is stable under the away-from-$N$ Hecke algebra. Then every $T_q$ and $S_q$ descends to $A$. Because $\operatorname{End}^0(A)$ acts faithfully on $V_\ell A$, the relation

$$
F_q^2-S_q^{-1}T_qF_q+qS_q^{-1}=0
$$

holds on the two-dimensional $V_\ell A$.

If $T_q$ acts on $A$ by the integer $a_q$ and $S_q=1$, then

$$
\det(X-F_q\mid V_\ell A)=X^2-a_qX+q.
$$

This is not inferred from the dimension alone. It follows because the correspondence relation descends through the quotient and because the determinant of Frobenius on the polarized Tate module is $q$. The Weil pairing gives the determinant: $F_q$ scales it by the action of arithmetic Frobenius on $\mathbf Z_\ell(1)$, namely $q$.

An actual elliptic curve over the ground field cannot acquire a nontrivial factor $s_q$ in this determinant: its Weil pairing forces $\det(F_q\mid V_\ell A)=q$, so the preceding elliptic example necessarily has $s_q=1$. Nontrivial nebentype occurs instead on a two-dimensional coefficient-field factor cut from the Tate module of a typically higher-dimensional modular quotient. Such a factor can be paired with its contragredient rather than with itself; once a later eigensystem argument proves that the quadratic relation is its full characteristic polynomial, its Tate-module determinant is $q/s_q$. With $S_q=\langle q\rangle^{-1}$ and diamond eigenvalue $\chi(q)$, this is $q\chi(q)$. This distinction prevents the central factor from being incorrectly attached to the Tate module of an elliptic curve.

### 14.3 A compact Shimura curve

Let $B/\mathbf Q$ be the indefinite quaternion algebra ramified at $2$ and $3$, and choose neat Eichler level $M$ prime to $6$. The resulting Shimura curve $X_K$ is compact. At a prime $q\nmid6M$, $B_q\simeq M_2(\mathbf Q_q)$ and $K_q$ is hyperspecial. The correspondence is

$$
X_K\xleftarrow{\pi}X_{K\cap hKh^{-1}}
\xrightarrow{\pi_h\circ R_h}X_K,
\qquad h\sim\operatorname{diag}(q,1).
$$

It has $q+1$ sheets before stabilizer quotient. Under a good PEL realization it extends over $\mathbf Z_q$ and specializes to transpose Frobenius plus the $S_q$-twisted forward graph. Hence geometric Frobenius $G_q$ on untwisted cohomology satisfies

$$
G_q^2-T_qG_q+qS_q=0
$$

for $\ell\ne q$. Arithmetic Frobenius $F_q$ on $T_\ell J_K$ instead satisfies

$$
F_q^2-S_q^{-1}T_qF_q+qS_q^{-1}=0.
$$

At $q=2$ or $3$, the algebra is division and there is no such spherical neighbor correspondence. At $q\mid M$, the level is Iwahori or deeper and the model is not the good hyperspecial one. This one example displays all three local regimes without conflating them.

## 15. The common Hecke-action theorem

### 15.1 Statement

We assemble the constructions in the form needed for the next stage.

**Common Hecke-action theorem.** Let $X$ be a modular curve or a compact quaternionic Shimura curve over a number field $E$, with the following data.

1. The chosen union of components is stable under the away-from-$\Sigma$ correspondences, descends to $E$, and is smooth proper and geometrically described at a neat level, or is treated as a tame stack with descent through a neat cover. A single component may be used only when these correspondences preserve it.
2. A finite set $\Sigma$ contains every place of algebra, level, PEL, polarization, component, and coefficient ramification.
3. For $v\notin\Sigma$, the local group is split hyperspecial, the unnormalized correspondences $T_v,S_v$ extend over a smooth proper integral model, and $S_v$ is the central scalar correspondence.
4. The adelic tower uses right multiplication, and the geometric span is oriented by $\mathcal T_h=\pi_*r_h^*$.

Then the abstract algebra

$$
\mathbb T^{\Sigma,\mathrm{abs}}
=\mathbf Z[T_v,S_v,S_v^{-1}:v\notin\Sigma]
$$

acts compatibly on divisors modulo principal divisors, the Picard group, the Jacobian $J_X$, every prime-to-characteristic torsion group, $T_\ell J_X$, and $H^1(X_{\overline E},\mathbf Z_\ell)$ and $H^1(X_{\overline E},\mathbf Q_\ell)$. It also acts by the same right-double-coset formulas on the corresponding automorphic modules. In the finite class-set realizations of Books 89--90, this assertion includes the full stabilizer and right-coset multiplicities, rather than a set-theoretic orbit count. More precisely:

$$
T_h=\pi_*r_h^*=[KhK]
$$

with all right-coset multiplicities retained;

$$
(T_h)^*=T_{h^{-1}}
$$

under the appropriate mass, Poincaré, or polarized pairing, including every central factor;

the Jacobian and twisted-cohomology actions agree under

$$
T_\ell J_X\simeq H^1(X_{\overline E},\mathbf Z_\ell(1));
$$

and every geometric Hecke operator commutes with $G_E$.

At every good place $v$ of residue cardinality $q_v$, geometric Frobenius $G_v$ on untwisted $H^1$ commutes with the Hecke action and satisfies the polynomial in the normalization of Books 89--90:

$$
\boxed{
G_v^2-T_vG_v+q_vS_v=0.} \tag{15.1}
$$

Arithmetic Frobenius $F_v$ on $T_\ell J_X\simeq H^1(1)$ satisfies the equivalent relation

$$
F_v^2-S_v^{-1}T_vF_v+q_vS_v^{-1}=0. \tag{15.2}
$$

On a subspace on which $T_v=t_v$ and $S_v=s_v$, geometric Frobenius is annihilated by

$$
X^2-t_vX+q_vs_v,
$$

whereas arithmetic Frobenius on the covariant Tate module is annihilated by

$$
X^2-s_v^{-1}t_vX+q_vs_v^{-1}.
$$

When a later argument proves that such a subspace is two-dimensional, the relevant quadratic becomes its characteristic polynomial. The present theorem asserts the operator identities on the entire cohomology and does not infer two-dimensionality.

Arithmetic Frobenius on untwisted $H^1$ satisfies the further converted polynomial of (11.7). The theorem makes no analogous assertion for $U_v$ at a level prime.

The acting algebras in the several realizations are the images of $\mathbb T^{\Sigma,\mathrm{abs}}$ and may have different kernels.

### 15.2 Proof

**Proof strategy.** There are four independent assertions: construction, adelic comparison, compatibility among geometric realizations, and the good-prime relation. Keeping them separate prevents a circular argument in which the desired Frobenius polynomial is used to identify the Hecke operator.

For construction, each compact-open double coset supplies a common intersection level and two finite legs. Pullback along the declared source and norm or trace along the target defines the operator on every geometric realization. Fiber products and projection formulas show that composition equals cycle composition with scheme-theoretic multiplicity.

For adelic comparison, Section 7.2 identifies a trace fiber with $K/K_h$ and sends $u$ to the right coset $uhK$. The pull--trace sum is therefore exactly the unnormalized operator $[KhK]$. The same quotient calculation, including stabilizer orbit sizes, identifies geometric composition multiplicities with convolution structure constants.

For compatibility, norm and trace form a morphism of Kummer sequences, giving the Tate-module/cohomology square. Poincaré bundle functoriality identifies transpose with Rosati, while the cohomological projection formula identifies it with Poincaré adjoint. Definition over $E$ makes all pullbacks and traces Galois equivariant.

Finally, at a good place the integral moduli problem extends the correspondence with finite locally free legs. In the declared right-action orientation its special fiber is the sum of the transpose Frobenius graph and the $S_v$-twisted forward graph. The two components have multiplicity one by the reduced ordinary or unramified-minuscule local model. If $F_v$ is arithmetic Frobenius on the covariant Tate module, the transpose acts as Verschiebung $q_vF_v^{-1}$. Hence

$$
T_v=q_vF_v^{-1}+S_vF_v.
$$

This gives (15.2), and substituting $G_v=q_vF_v^{-1}$ gives (15.1). Smooth proper base change transfers both relations to the generic fiber. $\square$

### 15.3 The boundary with Galois-representation extraction

The theorem provides a finite-dimensional space with commuting actions

$$
G_E\longrightarrow
\operatorname{Aut}_{\mathbf Q_\ell}
H^1(X_{\overline E},\mathbf Q_\ell),
\qquad
\mathbb T^{\Sigma,\mathrm{abs}}\longrightarrow
\operatorname{End}_{\mathbf Q_\ell}
H^1(X_{\overline E},\mathbf Q_\ell),
$$

an integral lattice from $T_\ell J_X$, polarized adjunction, unramified good-place action, and the exact Frobenius polynomial in the full Hecke algebra.

It does not choose an eigensystem, localize the Hecke algebra, prove that a localized summand has dimension two, construct a residual representation, or establish ramification and local--global compatibility at the excluded places. Those are logically subsequent operations. In particular, a maximal ideal of the Hecke algebra and the representation attached to it have not been selected here.

The distinction between abstract and image algebras remains important at that boundary. Localization must specify which integral image algebra acts on which lattice, and faithfulness cannot be inferred from the existence of the correspondence action.

### 15.4 Conclusion

A Hecke operator begins as a failure of uniqueness. There are $q+1$ cyclic quotients or lattice neighbors, and geometry records all of them in a curve with two finite maps. Pulling from the declared source and tracing to the declared target turns that relation into a covariant operator. Fiber products compose the relations; scheme lengths retain multiplicity; transpose reverses them and becomes the adjoint simultaneously for mass, Poincaré duality, and the canonical polarization.

The adelic and geometric descriptions now meet exactly. The common intersection level is the parameter curve, right translation supplies one leg, and the indispensable forgetful map returns it to the original level. With the orientation fixed, its pull--trace action is the integral right-coset sum $[KhK]$, not an average and not the inverse double coset. Central translations remain visible as $S_q$, becoming diamond or character values only after specialization.

Good reduction adds the decisive arithmetic relation. In characteristic $q$, the subgroup moduli problem separates into the Frobenius direction and its dual Verschiebung direction. Their cycle multiplicities are one; their degrees are $1$ and $q$; transported level contributes $S_q$; and $V=qF^{-1}$. These facts, rather than analogy, produce

$$
G_q^2-T_qG_q+qS_q=0
$$

for geometric Frobenius $G_q$ on untwisted cohomology, exactly in the abstract spherical normalization. On the covariant Tate module, arithmetic Frobenius $F_q$ instead satisfies

$$
F_q^2-S_q^{-1}T_qF_q+qS_q^{-1}=0.
$$

Smooth proper base change carries both identities back to characteristic zero. The visible Tate twist and the inverse-double-coset adjoint explain the conversion; omitting either is precisely what would put the diamond on the wrong side.

At level primes the oriented $U_q$ correspondence, its distinct adjoint, and the semistable special fiber mark a genuine boundary. Old images and their adjunction are geometrically available, but a good-prime polynomial and an integral old/new splitting are not automatic.

We have therefore reached the promised common platform: one abstract Hecke algebra acts on automorphic functions, divisors, Jacobians, Tate modules, and étale cohomology; all actions have the same multiplicities and central normalization; the geometric actions commute with Galois; and good Frobenius satisfies the Hecke polynomial. What remains is no longer to build the correspondence, but to extract and analyze the Galois representations carried by its eigensystems.
