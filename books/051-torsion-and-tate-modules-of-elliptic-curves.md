# Torsion and Tate Modules of Elliptic Curves

## Contents

1. [Multiplication on an elliptic curve](#1-multiplication-on-an-elliptic-curve)
   - [Why multiplication is geometric](#11-why-multiplication-is-geometric)
   - [Finiteness and degree](#12-finiteness-and-degree)
   - [The differential and separability](#13-the-differential-and-separability)
   - [Isogenies as the natural generalization](#14-isogenies-as-the-natural-generalization)
2. [Torsion in every characteristic](#2-torsion-in-every-characteristic)
   - [Three meanings of $E[n]$](#21-three-meanings-of-en)
   - [Prime-to-characteristic torsion](#22-prime-to-characteristic-torsion)
   - [What happens at the characteristic](#23-what-happens-at-the-characteristic)
   - [Frobenius and Verschiebung](#24-frobenius-and-verschiebung)
   - [Division polynomials as coordinates for torsion](#25-division-polynomials-as-coordinates-for-torsion)
   - [Rational two-torsion and a counterexample](#26-rational-two-torsion-and-a-counterexample)
3. [Galois actions on finite torsion](#3-galois-actions-on-finite-torsion)
   - [Why torsion produces representations](#31-why-torsion-produces-representations)
   - [Continuity at finite level](#32-continuity-at-finite-level)
   - [Residual representations and invariant lines](#33-residual-representations-and-invariant-lines)
   - [Rational points versus rational subgroups](#34-rational-points-versus-rational-subgroups)
   - [Traces, determinants, and characteristic polynomials](#35-traces-determinants-and-characteristic-polynomials)
   - [Changing the ground and coefficient fields](#36-changing-the-ground-and-coefficient-fields)
4. [The Weil pairing](#4-the-weil-pairing)
   - [Why torsion carries an alternating form](#41-why-torsion-carries-an-alternating-form)
   - [Divisors and the construction](#42-divisors-and-the-construction)
   - [Bilinearity and alternation](#43-bilinearity-and-alternation)
   - [Nondegeneracy](#44-nondegeneracy)
   - [Galois equivariance](#45-galois-equivariance)
   - [Compatibility as the level varies](#46-compatibility-as-the-level-varies)
   - [The group-scheme pairing in every characteristic](#47-the-group-scheme-pairing-in-every-characteristic)
5. [Tate modules and their topology](#5-tate-modules-and-their-topology)
   - [The inverse-limit idea](#51-the-inverse-limit-idea)
   - [Freeness of rank two](#52-freeness-of-rank-two)
   - [The Galois representation and continuity](#53-the-galois-representation-and-continuity)
   - [The cyclotomic module](#54-the-cyclotomic-module)
   - [The tower of torsion fields](#55-the-tower-of-torsion-fields)
6. [Duality and the Tate twist](#6-duality-and-the-tate-twist)
   - [Passing the pairing to the limit](#61-passing-the-pairing-to-the-limit)
   - [Self-duality](#62-self-duality)
   - [Matrix form and determinant](#63-matrix-form-and-determinant)
   - [Orthogonal lines and quotient characters](#64-orthogonal-lines-and-quotient-characters)
7. [Isogenies and functoriality](#7-isogenies-and-functoriality)
   - [Dual isogenies](#71-dual-isogenies)
   - [Kernels and quotient curves](#72-kernels-and-quotient-curves)
   - [Maps on torsion and Tate modules](#73-maps-on-torsion-and-tate-modules)
   - [Pairing compatibility and contravariance](#74-pairing-compatibility-and-contravariance)
   - [A degree-two isogeny in coordinates](#75-a-degree-two-isogeny-in-coordinates)
   - [Integral lattices at primes dividing the degree](#76-integral-lattices-at-primes-dividing-the-degree)
8. [Cyclic isogenies and reducibility](#8-cyclic-isogenies-and-reducibility)
   - [Why invariant lines are geometric](#81-why-invariant-lines-are-geometric)
   - [The equivalence for prime degree](#82-the-equivalence-for-prime-degree)
   - [Composite cyclic kernels](#83-composite-cyclic-kernels)
   - [Rational torsion is stronger](#84-rational-torsion-is-stronger)
   - [The dual isogeny and the two characters](#85-the-dual-isogeny-and-the-two-characters)
   - [The scheme-theoretic boundary](#86-the-scheme-theoretic-boundary)
9. [Good reduction and specialization](#9-good-reduction-and-specialization)
   - [Why prime-to-residue torsion survives](#91-why-prime-to-residue-torsion-survives)
   - [The specialization theorem](#92-the-specialization-theorem)
   - [Unramified representations](#93-unramified-representations)
   - [Frobenius and point counts](#94-frobenius-and-point-counts)
   - [A worked good-reduction count](#95-a-worked-good-reduction-count)
   - [Isogeny invariance at good places](#96-isogeny-invariance-at-good-places)
10. [Bad reduction and inertia](#10-bad-reduction-and-inertia)
    - [Multiplicative reduction revisited](#101-multiplicative-reduction-revisited)
    - [Residual inertia and discriminant divisibility](#102-residual-inertia-and-discriminant-divisibility)
    - [A Tate-curve example](#103-a-tate-curve-example)
    - [What additive reduction does imply](#104-what-additive-reduction-does-imply)
    - [What additive reduction does not imply](#105-what-additive-reduction-does-not-imply)
11. [At the residue characteristic](#11-at-the-residue-characteristic)
    - [Why $\ell=p$ is a different problem](#111-why-ellp-is-a-different-problem)
    - [Torsion on a good integral model](#112-torsion-on-a-good-integral-model)
    - [Connected and étale directions](#113-connected-and-étale-directions)
    - [The formal multiplication series](#114-the-formal-multiplication-series)
    - [Mixed characteristic and finite-flat representations](#115-mixed-characteristic-and-finite-flat-representations)
    - [Multiplicative reduction at the coefficient prime](#116-multiplicative-reduction-at-the-coefficient-prime)
    - [Equal characteristic](#117-equal-characteristic)
12. [From a curve to a residual representation](#12-from-a-curve-to-a-residual-representation)
    - [The global package](#121-the-global-package)
    - [Local statements away from $\ell$](#122-local-statements-away-from-ell)
    - [The Frey-type curve](#123-the-frey-type-curve)
    - [The places above two and above $\ell$](#124-the-places-above-two-and-above-ell)
    - [Reducibility as the remaining geometric branch](#125-reducibility-as-the-remaining-geometric-branch)
    - [The complete output](#126-the-complete-output)
    - [Conclusion](#127-conclusion)

## 1. Multiplication on an elliptic curve

### 1.1 Why multiplication is geometric

An elliptic curve $E$ over a field $K$ is simultaneously a smooth projective curve and a commutative group. The integers therefore act on it: for $n\in\mathbf Z$, the map

$$
[n]:E\longrightarrow E,\qquad P\longmapsto nP
$$

is a morphism of algebraic groups. Its kernel is the source of torsion, but the kernel cannot be understood correctly until the map itself is understood as a morphism. The decisive facts are that $[n]$ is finite of degree $n^2$ when $n\ne0$, and that its separability depends exactly on whether the characteristic divides $n$.

This geometric starting point prevents two later mistakes. First, the equation $nP=O$ may have fewer than $n^2$ geometric solutions in positive characteristic even though the kernel has degree $n^2$. Second, a kernel defined over $K$ need not have all of its points defined over $K$. Degree, geometric points, and rational points are three different measurements.

The maps satisfy

$$
[m]\circ[n]=[mn],\qquad [m]+[n]=[m+n],
$$

where addition of morphisms uses the group law on $E$. Translation by any geometric point is an automorphism. These elementary identities allow information near the origin to control the map everywhere.

### 1.2 Finiteness and degree

The map $[n]$ is nonconstant for $n\ne0$. The clean proof is contained in the degree calculation below: pullback of a positive-degree symmetric line bundle has positive degree $n^2\deg\mathcal L$, whereas pullback by a constant map has degree zero. A nonconstant morphism between smooth projective curves is finite, so $[n]$ is finite.

To calculate its degree, use a symmetric ample divisor. The divisor $(O)$ has degree one and the line bundle $\mathcal L=\mathcal O_E(3O)$ gives the plane cubic embedding. The theorem of the square on an elliptic curve gives

$$
[n]^*\mathcal L\cong\mathcal L^{\otimes n^2}. \tag{1.1}
$$

Taking degrees yields

$$
\deg[n]\,\deg\mathcal L=n^2\deg\mathcal L,
$$

and hence

$$
\deg[n]=n^2. \tag{1.2}
$$

Here is a concrete proof of the identity behind (1.1). For a divisor $D$ representing a symmetric line bundle, meaning $[-1]^*D\sim D$, the theorem of the square says

$$
[a+b]^*D+[a-b]^*D\sim2[a]^*D+2[b]^*D.
$$

Starting with $[0]^*D=0$ and $[1]^*D=D$, induction gives $[n]^*D\sim n^2D$. The quadratic degree is thus forced by the compatibility of addition and inversion, not by a coordinate accident.

The kernel of $[n]$, denoted $E[n]$, is consequently a finite commutative subgroup scheme of degree $n^2$. Over a field its coordinate algebra has dimension $n^2$. This statement remains true when the visible geometric points are fewer.

### 1.3 The differential and separability

Let $\omega$ be a nonzero invariant differential on $E$. Translation invariance and the group law imply

$$
[n]^*\omega=n\omega. \tag{1.3}
$$

One proves this first for positive $n$ by pulling $\omega$ back under the addition map: if $m:E\times E\to E$, then $m^*\omega=\operatorname{pr}_1^*\omega+\operatorname{pr}_2^*\omega$. Restricting along the diagonal and inducting gives (1.3); negative $n$ follows from $[-1]^*\omega=-\omega$.

A finite morphism of smooth curves is separable precisely when its differential is not identically zero. Therefore

$$
[n]\text{ is separable}\quad\Longleftrightarrow\quad
n\ne0\text{ in }K. \tag{1.4}
$$

Equivalently, if $p=\operatorname{char}K>0$, then $[n]$ is separable exactly when $p\nmid n$. In characteristic zero every nonzero multiplication map is separable.

When $[n]$ is separable, every geometric fiber has $n^2$ distinct points, because translation identifies every fiber with $E[n]$ and a finite separable map of degree $n^2$ has that many geometric points. Thus for an algebraic closure $\overline K$,

$$
|E[n](\overline K)|=n^2
\quad\text{if }\gcd(n,\operatorname{char}K)=1. \tag{1.5}
$$

If $p\mid n$, the degree remains $n^2$ but inseparable multiplicities occur. The differential detects precisely why counting distinct points no longer measures the kernel.

### 1.4 Isogenies as the natural generalization

The multiplication maps belong to a broader class. An **isogeny** $\varphi:E\to E'$ is a nonconstant morphism of elliptic curves preserving the origin. It is automatically a finite surjective group homomorphism. Its degree is the degree of the underlying finite morphism, and it is separable exactly when its differential at the origin is nonzero.

If $\varphi$ is separable, then

$$
\deg\varphi=|\ker\varphi(\overline K)|. \tag{1.6}
$$

Without separability, the right side must be replaced by the degree of the kernel scheme. The Frobenius morphism of an elliptic curve in characteristic $p$ is the model counterexample: it has degree $p$ and can have only the identity in its geometric kernel.

This language will become useful twice. Finite torsion is the kernel of an isogeny $[n]$, while rational cyclic isogenies correspond to Galois-stable cyclic directions inside torsion. The same geometry therefore controls both representations and quotients.

## 2. Torsion in every characteristic

### 2.1 Three meanings of $E[n]$

Torsion is often introduced as the set of solutions of $nP=O$. That description is adequate only when $n$ is invertible in the ground field. In general three objects must be separated:

$$
E[n]\quad\text{as a finite subgroup scheme},\qquad
E[n](\overline K),\qquad
E[n](K). \tag{2.1}
$$

The first has degree $n^2$. The second is the group of geometric points and may be smaller. The third is the subgroup fixed by the absolute Galois group when the torsion is separable. A statement about one of these objects is not automatically a statement about the others.

The distinction is already visible in characteristic $p$. The group scheme $\mu_p$ has coordinate algebra $K[T]/(T^p-1)=K[T]/((T-1)^p)$, hence degree $p$, but

$$
\mu_p(\overline K)=\{1\}.
$$

Likewise the infinitesimal additive group $\alpha_p$, defined by $T^p=0$, has degree $p$ and only its identity as a geometric point. Nonreduced structure stores multiplicity invisible to point counting.

We will use elementary subgroup-scheme language to state the correct result, but systematic finite-flat models over valuation rings belong later. Here the base is a field unless explicitly stated otherwise.

### 2.2 Prime-to-characteristic torsion

Let $n\ge1$ be prime to $\operatorname{char}K$. Then $[n]$ is separable of degree $n^2$, so $E[n]$ is finite étale. Over a separably closed field it is constant. Its abstract group can be determined one prime at a time.

**Theorem 2.1 (structure of separable torsion).** If $K$ is separably closed and $n$ is prime to $\operatorname{char}K$, then

$$
E[n](K)\cong(\mathbf Z/n\mathbf Z)^2. \tag{2.2}
$$

**Proof strategy.** Count the kernel of each prime-power multiplication map and use the exactness of successive multiplication. The only finite abelian group of order $\ell^{2r}$ with exactly $\ell^2$ elements killed by $\ell$ and exponent $\ell^r$ is $(\mathbf Z/\ell^r\mathbf Z)^2$.

**Proof.** Fix $\ell\mid n$ and write $r=v_\ell(n)$. Separability gives

$$
|E[\ell^s](K)|=\ell^{2s}
$$

for every $s\ge1$. Multiplication by $\ell$ maps $E[\ell^{s+1}]$ onto $E[\ell^s]$: every point in the target has $\ell^2$ preimages because the fiber is a translate of $E[\ell]$. The group $E[\ell^r]$ has exponent exactly $\ell^r$, for otherwise it would equal $E[\ell^{r-1}]$ and have too few elements. The classification of finite abelian $\ell$-groups now gives two cyclic factors, both of length $r$. Taking the product over primes dividing $n$ proves (2.2). $\square$

The same statement holds over an algebraic closure. In the prime-to-characteristic case every torsion point is separable, so it is already defined over the separable closure. Thus no purely inseparable extension creates new such points.

### 2.3 What happens at the characteristic

Assume now that $K$ has characteristic $p>0$. The map $[p]$ has zero differential, so it is inseparable. Its kernel scheme still has degree $p^2$, but its group of geometric points has either $p$ elements or one element. These alternatives define the two possible $p$-ranks of an elliptic curve.

The curve is **ordinary** if

$$
E[p](\overline K)\cong\mathbf Z/p\mathbf Z,
$$

and **supersingular** if $E[p](\overline K)=0$. Here $0$ means the group consisting only of the origin. At every level,

$$
E[p^r](\overline K)\cong
\begin{cases}
\mathbf Z/p^r\mathbf Z,&E\text{ ordinary},\\
0,&E\text{ supersingular}.
\end{cases} \tag{2.3}
$$

The proof uses the inseparable-separable factorization of $[p^r]$. Its separable degree is $p^r$ in the ordinary case and $1$ in the supersingular case. The number of geometric points in the kernel equals that separable degree. Compatibility under multiplication by $p$ then determines the abstract groups.

If $n=p^rm$ with $(m,p)=1$, the primary decomposition of the kernel gives

$$
E[n](\overline K)\cong
\begin{cases}
(\mathbf Z/m\mathbf Z)^2\oplus\mathbf Z/p^r\mathbf Z,
&E\text{ ordinary},\\
(\mathbf Z/m\mathbf Z)^2,&E\text{ supersingular}.
\end{cases} \tag{2.4}
$$

Neither group has $n^2$ elements when $r>0$. The missing degree is nonreduced scheme structure. For an ordinary curve, the schematic shape of the $p$-power kernel has a connected multiplicative direction and an étale direction; for a supersingular curve it is entirely connected. This observation will return when the coefficient prime equals the residue characteristic.

### 2.4 Frobenius and Verschiebung

The ordinary--supersingular dichotomy becomes more transparent when multiplication by $p$ is factored. Let $E/K$ be in characteristic $p$. The relative Frobenius

$$
F:E\longrightarrow E^{(p)}
$$

raises functions to their $p$th powers relative to the Frobenius twist of the coefficients. It is purely inseparable of degree $p$. Its dual is the **Verschiebung**

$$
V:E^{(p)}\longrightarrow E,
$$

and duality gives

$$
V\circ F=[p]_E,
\qquad F\circ V=[p]_{E^{(p)}}. \tag{2.5}
$$

Thus the inseparable degree of $[p]$ is at least $p$. The remaining factor $V$ is separable for an ordinary curve and inseparable for a supersingular curve. In the ordinary case $\ker V$ has $p$ distinct geometric points, which pull back to the visible cyclic direction of $E[p]$. In the supersingular case both $F$ and $V$ are inseparable, so $[p]$ has separable degree one.

Iterating gives the point counts in (2.3). More conceptually, ordinary curves divide the total degree $p^{2r}$ into inseparable degree $p^r$ and separable degree $p^r$; supersingular curves place the entire degree in the inseparable part. This factorization is also why the two cases behave differently in families of residue characteristic $p$.

The notation $E^{(p)}$ matters over a nonperfect field. Frobenius does not generally define a $K$-endomorphism $E\to E$ with the same coefficients; it maps to the Frobenius twist. Over a finite field one can iterate until the coefficient twist returns, producing the Frobenius endomorphism used in point counts.

### 2.5 Division polynomials as coordinates for torsion

Abstract finiteness is enough for representation theory, but explicit curves require equations for torsion. Suppose for simplicity that

$$
E:y^2=x^3+Ax+B,\qquad \operatorname{char}K\ne2,3.
$$

The division polynomials begin

$$
\psi_1=1,\qquad \psi_2=2y,\qquad
\psi_3=3x^4+6Ax^2+12Bx-A^2,
$$

and are defined recursively by

$$
\begin{aligned}
\psi_{2m+1}&=\psi_{m+2}\psi_m^3-\psi_{m-1}\psi_{m+1}^3,\\
\psi_{2m}&=\frac{\psi_m}{2y}
\left(\psi_{m+2}\psi_{m-1}^2-\psi_{m-2}\psi_{m+1}^2\right).
\end{aligned} \tag{2.6}
$$

Put

$$
\phi_n=x\psi_n^2-\psi_{n+1}\psi_{n-1}.
$$

For $P$ away from the poles of the displayed expression,

$$
x([n]P)=\frac{\phi_n(P)}{\psi_n(P)^2}. \tag{2.7}
$$

If $n$ is odd, $\psi_n$ is a polynomial in $x$ of degree $(n^2-1)/2$; its roots are exactly the $x$-coordinates of nonzero $n$-torsion when $n$ is prime to the characteristic. If $n$ is even, $\psi_n/(2y)$ has degree $(n^2-4)/2$ in $x$, and the factor $2y$ accounts for nonzero two-torsion.

These formulas should be used with their hypotheses. If the characteristic divides $n$, $\psi_n$ can acquire multiple roots or even degenerate, reflecting inseparability. If the characteristic is $2$ or $3$, the general Weierstrass division polynomials must be used. Division polynomials are coordinate tools, not substitutes for the finite-morphism argument.

### 2.6 Rational two-torsion and a counterexample

On a short equation in characteristic different from $2$, a point equals its inverse precisely when $y=0$. Hence the nonzero points of $E[2]$ are

$$
(e_i,0),
$$

where the $e_i$ are the roots of $x^3+Ax+B$. Thus one rational root gives one rational point of order two, and complete splitting gives

$$
E[2](K)\cong(\mathbf Z/2\mathbf Z)^2.
$$

The Legendre curve

$$
E_\lambda:y^2=x(x-1)(x-\lambda)
$$

has full rational two-torsion whenever $\lambda\in K\setminus\{0,1\}$ and $\operatorname{char}K\ne2$. This visible basis will later illustrate both reducibility and good-reduction specialization.

In characteristic $2$, the rule “two-torsion means $y=0$” is false. For

$$
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,
$$

negation is $(x,y)\mapsto(x,-y-a_1x-a_3)$, so a two-torsion point satisfies $a_1x+a_3=0$. More importantly, a supersingular curve may have no nonzero geometric two-torsion at all, although its kernel scheme $E[2]$ has degree four. This is the simplest place where the equation, the characteristic, and the scheme-point distinction must be read together.

## 3. Galois actions on finite torsion

### 3.1 Why torsion produces representations

Fix a separable closure $K^s$ and write

$$
G_K=\operatorname{Gal}(K^s/K).
$$

Every automorphism in $G_K$ acts on the coordinates of points and commutes with the group law. Consequently it preserves $E[n](K^s)$. If $n$ is prime to $\operatorname{char}K$, Theorem 2.1 makes this group a free module of rank two over $\mathbf Z/n\mathbf Z$, and choosing a basis gives

$$
\rho_{E,n}:G_K\longrightarrow
\operatorname{GL}_2(\mathbf Z/n\mathbf Z). \tag{3.1}
$$

We use column vectors, and the columns of $\rho_{E,n}(\sigma)$ are the coordinates of the images of the chosen basis vectors. This convention will govern every later matrix formula.

The representation is canonical only up to conjugacy. Replacing a basis by a matrix $B$ changes it to

$$
\rho'_{E,n}(\sigma)=B^{-1}\rho_{E,n}(\sigma)B. \tag{3.2}
$$

Properties such as determinant, trace, reducibility, and the isomorphism class of the module do not depend on the basis.

### 3.2 Continuity at finite level

Give $G_K$ its profinite topology and the finite group $\operatorname{GL}_2(\mathbf Z/n\mathbf Z)$ the discrete topology. Then $\rho_{E,n}$ is continuous.

Indeed, the coordinates of the finitely many torsion points generate a finite separable extension

$$
K(E[n])/K.
$$

The subgroup fixing that field is open in $G_K$ and lies in the kernel. Conversely, the kernel fixes every torsion point and hence fixes the torsion field. Thus

$$
\ker\rho_{E,n}=\operatorname{Gal}(K^s/K(E[n]))
$$

is open. For a map from a profinite group to a finite discrete group, openness of the kernel is exactly continuity.

This proof also identifies the image:

$$
\operatorname{im}\rho_{E,n}\cong
\operatorname{Gal}(K(E[n])/K). \tag{3.3}
$$

The torsion field is Galois because it is the fixed field of the kernel, or directly because the full set of torsion points is stable under every $K$-embedding.

### 3.3 Residual representations and invariant lines

For a prime $\ell\ne\operatorname{char}K$, write

$$
\overline\rho_{E,\ell}:G_K\longrightarrow
\operatorname{GL}_2(\mathbf F_\ell) \tag{3.4}
$$

for the action on $E[\ell]$. It is **reducible over $\mathbf F_\ell$** if $E[\ell]$ contains a one-dimensional $G_K$-stable subspace. Otherwise it is irreducible. Reducibility over $\mathbf F_\ell$ is stronger than reducibility after extending scalars to $\overline{\mathbf F}_\ell$; the latter only guarantees a stable line defined over some finite coefficient extension.

If $L\subset E[\ell]$ is stable, a basis beginning with a generator of $L$ gives

$$
\overline\rho_{E,\ell}(\sigma)=
\begin{pmatrix}
\psi_1(\sigma)&*\\
0&\psi_2(\sigma)
\end{pmatrix}. \tag{3.5}
$$

The star may represent a nonsplit extension. A triangular representation is reducible; it is a direct sum only when a second stable line exists. Tate curves provide the fundamental local example: their multiplicative line is always stable, but the extension splits only when the Tate parameter is an $\ell$th power.

### 3.4 Rational points versus rational subgroups

A point $P\in E[\ell]$ is $K$-rational when every $\sigma$ fixes $P$. The line $\mathbf F_\ell P$ is $K$-rational as a subgroup when Galois merely preserves it. In the second situation there is a character $\psi:G_K\to\mathbf F_\ell^\times$ such that

$$
\sigma P=\psi(\sigma)P.
$$

Thus a rational subgroup need not have a rational generator. For $\ell=2$ there is no distinction because $\mathbf F_2^\times=1$. For every odd $\ell$ the distinction is real.

For example, the canonical subgroup $\mu_\ell$ on a split Tate curve is defined over $K$, but a generator is rational only if $K$ contains a primitive $\ell$th root of unity. Its Galois character is cyclotomic. This example is worth retaining: “rational cyclic isogeny” will mean a Galois-stable kernel, not a chosen rational torsion point.

### 3.5 Traces, determinants, and characteristic polynomials

Although a matrix depends on a basis, its characteristic polynomial does not. For $\sigma\in G_K$, write

$$
P_{E,n,\sigma}(X)=X^2-\operatorname{tr}(\rho_{E,n}(\sigma))X
+\det(\rho_{E,n}(\sigma)). \tag{3.6}
$$

Both coefficients are conjugacy invariants. When $n=\ell$, reducibility does not force this polynomial to split for every element over an arbitrary smaller coefficient field unless the invariant line is itself defined over that field. For reducibility over $\mathbf F_\ell$, however, every matrix in an adapted basis is triangular and

$$
P_{E,\ell,\sigma}(X)
=(X-\psi_1(\sigma))(X-\psi_2(\sigma)).
$$

The converse using one element is useful but asymmetric. If the characteristic polynomial of a single Galois element is irreducible over $\mathbf F_\ell$, then the full representation is irreducible over $\mathbf F_\ell$, because a stable line would give an eigenvalue in that field. If every characteristic polynomial splits, the representation need not be reducible: different elements can preserve different lines. Reducibility is a common invariant-line condition, not an element-by-element eigenvalue condition.

At good finite-residue places, Chapter 9 will produce a canonical polynomial independent not only of the basis but, after lifting to integers, of the coefficient prime $\ell$. That compatibility turns elementary point counts into information about an entire family of representations.

### 3.6 Changing the ground and coefficient fields

Two scalar changes occur in applications and answer different questions. If $L/K$ is an algebraic extension inside $K^s$, then

$$
G_L\subseteq G_K
$$

and the torsion representation over $L$ is the restriction of the representation over $K$. A line that is not $G_K$-stable can become stable under $G_L$. Geometrically, an isogeny absent over $K$ can descend over $L$. Thus irreducibility over $K$ need not persist after ground-field extension.

If instead one extends the coefficient field from $\mathbf F_\ell$ to a finite field $k'/\mathbf F_\ell$, the Galois group does not change and one forms

$$
E[\ell]\otimes_{\mathbf F_\ell}k'.
$$

The original representation is **absolutely irreducible** when this module remains irreducible over an algebraic closure of $\mathbf F_\ell$. Reducibility over $\mathbf F_\ell$ means a rational $\ell$-isogeny by Theorem 8.1. Reducibility only after coefficient extension instead gives a Galois-stable eigenline in the scalar extension, not necessarily a subgroup of $E[\ell]$ of order $\ell$ defined over $K$.

Finite extension of the ground field also interacts with torsion fields in a controlled way:

$$
L(E[n])=L\,K(E[n])
$$

inside a common separable closure. Therefore the image over $L$ is the subgroup of the image over $K$ corresponding to the intersection $L\cap K(E[n])$. In particular, base extension cannot enlarge the Galois image; coefficient extension can change the visibility of invariant subspaces without changing the image as an abstract group.

Finally, separability hypotheses remain attached to the field characteristic. A purely inseparable extension in characteristic $p$ does not create new prime-to-$p$ torsion points, because those points are already separable. It can change equations and Frobenius twists, but it cannot repair the missing geometric $p$-torsion of a supersingular curve. This is another reason to separate base change from coefficient change.

## 4. The Weil pairing

### 4.1 Why torsion carries an alternating form

The abstract group $(\mathbf Z/n\mathbf Z)^2$ has many automorphisms, but torsion on an elliptic curve has more structure than an abstract rank-two module. The principal polarization defined by the origin produces a canonical alternating pairing

$$
e_n:E[n]\times E[n]\longrightarrow\mu_n. \tag{4.1}
$$

When $n$ is prime to the characteristic, this pairing is perfect on geometric points. It forces every Galois matrix to be a symplectic similitude, and in dimension two its multiplier is its determinant. The cyclotomic determinant theorem will therefore emerge from geometry rather than from a coordinate calculation.

We first construct the pairing over an algebraically closed field with $n$ invertible. The construction has a scheme-theoretic extension when $n$ is not invertible, but geometric perfectness then cannot mean a bijection between groups of $n^2$ points. We will not disguise that failure by using the same point-counting proof.

### 4.2 Divisors and the construction

For $P\in E[n]$, choose a degree-zero divisor $D_P$ whose divisor class corresponds to $P$ under

$$
E\xrightarrow{\sim}\operatorname{Pic}^0(E),\qquad
P\longmapsto[(P)-(O)].
$$

Because $nP=O$, the divisor $nD_P$ is principal. Choose a rational function $f_P$ with

$$
\operatorname{div}(f_P)=nD_P. \tag{4.2}
$$

For $P,Q\in E[n]$, move the divisors within their linear equivalence classes so that their supports are disjoint and avoid the zeros and poles of the relevant functions. If $f$ is a function and $D=\sum_Rm_R(R)$ is a divisor disjoint from $\operatorname{div}(f)$, put

$$
f(D)=\prod_R f(R)^{m_R}.
$$

Our sign convention for the **Weil pairing** is

$$
e_n(P,Q)=\frac{f_P(D_Q)}{f_Q(D_P)}. \tag{4.3}
$$

Weil reciprocity,

$$
f(\operatorname{div}g)=g(\operatorname{div}f), \tag{4.4}
$$

shows that (4.3) is unchanged when a divisor is replaced by a linearly equivalent one. Multiplying either $f_P$ or $f_Q$ by a constant has no effect because the opposite divisor has degree zero. Hence the value depends only on $P$ and $Q$.

To see that it lies in $\mu_n$, translate the divisor data by an $n$-torsion point and apply reciprocity. Equivalently, bilinearity below gives

$$
e_n(P,Q)^n=e_n(nP,Q)=e_n(O,Q)=1.
$$

This last argument uses bilinearity, so the construction and that property are best proved together.

### 4.3 Bilinearity and alternation

**Theorem 4.1.** The pairing $e_n$ is bilinear and alternating:

$$
\begin{aligned}
e_n(P_1+P_2,Q)&=e_n(P_1,Q)e_n(P_2,Q),\\
e_n(P,Q_1+Q_2)&=e_n(P,Q_1)e_n(P,Q_2),\\
e_n(P,P)&=1.
\end{aligned} \tag{4.5}
$$

In particular $e_n(P,Q)=e_n(Q,P)^{-1}$.

**Proof strategy.** Addition in $E$ is addition in $\operatorname{Pic}^0(E)$. Thus divisor representatives for $P_1+P_2$ differ from $D_{P_1}+D_{P_2}$ by a principal divisor. Functions witnessing this difference contribute the same factor to numerator and denominator by Weil reciprocity. Alternation is then visible directly from the quotient in (4.3).

**Proof.** Choose $D_{P_1+P_2}=D_{P_1}+D_{P_2}+\operatorname{div}h$. A compatible choice is

$$
f_{P_1+P_2}=f_{P_1}f_{P_2}h^n
$$

up to a scalar. Substituting in (4.3), the $f_{P_i}$ terms produce the desired product. The remaining term is

$$
\frac{h(D_Q)^n}{f_Q(\operatorname{div}h)}.
$$

By (4.2) and reciprocity,

$$
f_Q(\operatorname{div}h)=h(\operatorname{div}f_Q)=h(nD_Q)=h(D_Q)^n,
$$

so it cancels. This proves additivity in the first variable. The same argument, or the quotient symmetry, proves additivity in the second. Setting $Q=P$ in (4.3) gives $1$ after choosing the same divisor and function in numerator and denominator. Finally,

$$
1=e_n(P+Q,P+Q)=e_n(P,Q)e_n(Q,P)
$$

because the diagonal terms are $1$. $\square$

Alternating is stronger than skew-symmetric when $n$ is even. The identity $e_n(P,P)=1$ is part of the theorem, not a consequence of $e_n(P,P)^2=1$.

### 4.4 Nondegeneracy

**Theorem 4.2 (perfectness).** Suppose $n$ is prime to $\operatorname{char}K$ and $K$ is algebraically closed. For every nonzero $P\in E[n]$, there exists $Q\in E[n]$ with $e_n(P,Q)\ne1$. Equivalently,

$$
E[n]\xrightarrow{\sim}\operatorname{Hom}(E[n],\mu_n),\qquad
P\longmapsto(Q\mapsto e_n(P,Q)) \tag{4.6}
$$

is an isomorphism.

**Proof strategy.** A character of the kernel of an isogeny is the descent datum on a trivial line bundle along the quotient isogeny. It therefore gives a point in the kernel of the dual isogeny. Applying this kernel-duality principle to $[n]$, and then identifying $E$ with its dual by the origin polarization, proves perfectness. The divisor formula (4.3) is the resulting evaluation pairing.

**Proof.** Let $E^\vee=\operatorname{Pic}^0(E)$ and let

$$
\lambda:E\longrightarrow E^\vee,\qquad
P\longmapsto[t_P^*\mathcal O_E(O)\otimes\mathcal O_E(O)^{-1}].
$$

Under $E\simeq\operatorname{Pic}^0(E)$, this map sends $P$ to the class of $(P)-(O)$, up to the sign fixed by choosing $t_P$ instead of $t_{-P}$. It is therefore an isomorphism.

We recall the kernel-duality argument. Let $\varphi:A\to B=A/H$ be an isogeny with finite kernel scheme $H$. A rigidified degree-zero line bundle $L$ on $B$ belongs to $\ker(\varphi^\vee)$ precisely when $\varphi^*L$ is trivial. Choose a trivialization after a faithfully flat base change. Translation by $h\in H$ changes it by a unit $\chi(h)$, and compatibility of two translations gives

$$
\chi(h+h')=\chi(h)\chi(h').
$$

Thus $\chi$ is a character $H\to\mathbf G_m$. Conversely, such a character twists the descent datum on the trivial line bundle over $A$ and descends it to a rigidified line bundle on $B$ whose pullback is trivial. These constructions are inverse and commute with base change. Hence

$$
(\ker\varphi)^D\simeq\ker(\varphi^\vee),
$$

with Cartier evaluation as the perfect pairing between the two kernels.

For $\varphi=[n]_E$, pullback of degree-zero line bundles shows that $\varphi^\vee=[n]_{E^\vee}$. The origin polarization therefore gives an isomorphism $E[n]^D\simeq E[n]$. There is a harmless sign to fix here: using $t_P$ rather than $t_{-P}$ identifies the adjoint with the negative of the identification obtained from the other convention. We choose the sign for which Cartier evaluation, expressed through the translation trivializations determined by $D_P$ and $f_P$, is (4.3). Reversing this choice would replace every value by its inverse and would change neither perfectness nor any determinant conclusion. With this convention, (4.6) is an isomorphism. Since $n$ is invertible, both group schemes are finite étale, so the scheme-theoretic isomorphism is the asserted perfect pairing on geometric points. $\square$

Choose a point $P$ of exact order $n$. Perfectness supplies $Q$ such that $e_n(P,Q)$ has exact order $n$: otherwise $e_n(P,Q)^{n/d}=1$ for every $Q$ for some proper divisor $d$, and nondegeneracy would force $(n/d)P=0$. Thus one can choose a basis $(P,Q)$ satisfying

$$
e_n(P,Q)=\zeta_n \tag{4.7}
$$

for any chosen primitive $n$th root after rescaling $Q$. Such a basis is called symplectic.

### 4.5 Galois equivariance

Now let $K$ be arbitrary and $n$ prime to its characteristic. The divisor construction commutes with every $\sigma\in G_K$: applying $\sigma$ to a defining function and divisor gives defining data for $\sigma P$. Therefore

$$
e_n(\sigma P,\sigma Q)=\sigma(e_n(P,Q)). \tag{4.8}
$$

Define the mod-$n$ cyclotomic character by

$$
\sigma(\zeta)=\zeta^{\chi_n(\sigma)}
\qquad(\zeta\in\mu_n). \tag{4.9}
$$

If $(P,Q)$ is symplectic and $A=\rho_{E,n}(\sigma)$ in the column convention, bilinearity gives

$$
e_n(\sigma P,\sigma Q)=e_n(P,Q)^{\det A}. \tag{4.10}
$$

Equivariance gives the same value as $e_n(P,Q)^{\chi_n(\sigma)}$. Since $e_n(P,Q)$ is primitive,

$$
\det\rho_{E,n}=\chi_n. \tag{4.11}
$$

This proof is basis-independent, although a symplectic basis makes it visible. It works for every elliptic curve and every $n$ prime to the characteristic, regardless of reduction.

### 4.6 Compatibility as the level varies

The pairings at different levels are compatible with multiplication. If $m,n\ge1$, both prime to the characteristic, and $P,Q\in E[mn]$, then

$$
e_{mn}(P,Q)^m=e_n(mP,mQ). \tag{4.12}
$$

The clean proof uses functoriality of the Poincaré biextension under multiplication by $m$: pulling back in both variables changes its commutator trivialization by the $m$th power and gives (4.12) as an equality of pairings. On prime-to-characteristic geometric points, the exponent can be checked on a symplectic basis: both sides are the same power of a primitive $mn$th root. Thus the displayed formula is not being inferred from the existence of one convenient basis; it is the pointwise shadow of the functorial group-scheme identity.

In particular, if $\ell P_{r+1}=P_r$ and $\ell Q_{r+1}=Q_r$, then

$$
e_{\ell^{r+1}}(P_{r+1},Q_{r+1})^\ell
=e_{\ell^r}(P_r,Q_r). \tag{4.13}
$$

This exact exponent is what permits passage to an inverse limit. Omitting it would confuse the transition map $\mu_{\ell^{r+1}}\to\mu_{\ell^r}$ with an inclusion.

When the characteristic divides $n$, a canonical group-scheme pairing still exists and expresses the principal polarization. Its perfectness is schematic. The pairing on geometric points alone can be degenerate simply because there are too few points; for instance $\mu_p(\overline K)$ is trivial in characteristic $p$. All point-level perfectness statements in this chapter therefore retain the hypothesis $p\nmid n$.

### 4.7 The group-scheme pairing in every characteristic

The preceding final sentence deserves a theorem, because it is the form needed at the residue characteristic. Let $E/S$ be an elliptic scheme. Multiplication by $n$ is finite locally free of degree $n^2$, so $E[n]$ is a finite locally free commutative group scheme even where $n$ is not invertible. The origin defines a principal polarization

$$
\lambda:E\xrightarrow{\sim}E^\vee.
$$

The kernel-duality argument used in Theorem 4.2 works over the base $S$ and without a separability assumption. Applied to $[n]$, it gives

$$
E[n]^D\xrightarrow{\sim}E^\vee[n]
\xrightarrow[\lambda^{-1}]{\sim}E[n]. \tag{4.14}
$$

Cartier evaluation under (4.14) is a bilinear pairing

$$
e_n:E[n]\times_SE[n]\longrightarrow\mu_n. \tag{4.15}
$$

It is alternating because the origin polarization is symmetric: the commutator biextension changes to its inverse when the variables are exchanged and is canonically trivial on the diagonal. It is perfect because (4.14) is an isomorphism. All of this commutes with arbitrary base change.

**Theorem 4.3 (schematic Weil duality).** For every elliptic scheme $E/S$ and every $n\geq1$, (4.15) is a perfect alternating pairing of finite locally free group schemes. If $n$ is invertible on $S$, taking geometric points recovers Theorems 4.1 and 4.2. If $n$ is not invertible, perfectness means the isomorphism (4.14), not a nondegenerate pairing on point sets.

**Proof.** The construction of the dual elliptic scheme and its Poincaré line bundle identifies the Cartier dual of the kernel of an isogeny with the kernel of the dual isogeny, by the descent calculation in Theorem 4.2. Since $[n]^\vee=[n]$ after the origin polarization, evaluation gives (4.15) and makes its adjoint the isomorphism (4.14). Symmetry of the polarization gives alternation. Base change preserves the Poincaré bundle, the multiplication kernels, and the descent construction. $\square$

This theorem explains the ordinary characteristic-$p$ picture. The Cartier dual of the étale group $\mathbf Z/p^r\mathbf Z$ is $\mu_{p^r}$, so a visible étale direction and an invisible multiplicative direction are paired. In the supersingular case both the torsion group and its dual are connected. A perfect schematic pairing can therefore have a trivial pairing on all geometric points without any contradiction.

## 5. Tate modules and their topology

### 5.1 The inverse-limit idea

A single representation on $E[\ell]$ remembers torsion only modulo $\ell$. To retain every $\ell$-power level simultaneously, one records a compatible tower of division points. Fix a prime

$$
\ell\ne\operatorname{char}K.
$$

The **$\ell$-adic Tate module** is

$$
T_\ell E=\varprojlim_r E[\ell^r](K^s), \tag{5.1}
$$

where the transition map is multiplication by $\ell$. Thus an element is a sequence

$$
x=(P_1,P_2,\ldots),\qquad \ell P_{r+1}=P_r.
$$

Scalar multiplication by $a\in\mathbf Z_\ell$ is defined levelwise using the residue of $a$ modulo $\ell^r$. The construction is canonical and requires no basis.

The inverse limit is not the union of the finite torsion groups. A torsion point has finite order; a nonzero Tate-module element is an infinitely divisible compatible direction. This distinction is analogous to the difference between an integer and its compatible residues modulo all powers of $\ell$.

### 5.2 Freeness of rank two

**Theorem 5.1.** If $\ell\ne\operatorname{char}K$, then

$$
T_\ell E\cong\mathbf Z_\ell^2. \tag{5.2}
$$

**Proof strategy.** Begin with a basis at level one and lift it successively through the surjective multiplication maps. At each stage the lifts generate because their reductions generate, and cardinality forces independence.

**Proof.** Choose a basis $P_1,Q_1$ of $E[\ell]$. Suppose $P_r,Q_r$ form a basis of $E[\ell^r]$. Surjectivity of

$$
[\ell]:E[\ell^{r+1}]\to E[\ell^r]
$$

provides lifts $P_{r+1},Q_{r+1}$. Each lift has exact order $\ell^{r+1}$. If

$$
aP_{r+1}+bQ_{r+1}=0,
$$

then multiplication by $\ell$ and the basis property at level $r$ show that $a$ and $b$ are divisible by $\ell^r$. Write $a=\ell^ra_0$ and $b=\ell^rb_0$. The points $\ell^{r-1}P_r$ and $\ell^{r-1}Q_r$ form a basis of $E[\ell]$, so the original relation forces $a_0$ and $b_0$ to be divisible by $\ell$. Thus the two lifts are independent over $\mathbf Z/\ell^{r+1}\mathbf Z$. Their generated subgroup has order $\ell^{2r+2}$, equal to the order of $E[\ell^{r+1}]$, so they form a basis. The compatible sequences $P=(P_r)$ and $Q=(Q_r)$ give a basis of the inverse limit. $\square$

Reduction at level $r$ gives a canonical isomorphism

$$
T_\ell E/\ell^rT_\ell E\xrightarrow{\sim}E[\ell^r]. \tag{5.3}
$$

In particular,

$$
T_\ell E/\ell T_\ell E\cong E[\ell]. \tag{5.4}
$$

The **rational Tate module** is

$$
V_\ell E=T_\ell E\otimes_{\mathbf Z_\ell}\mathbf Q_\ell, \tag{5.5}
$$

a two-dimensional $\mathbf Q_\ell$-vector space. The lattice $T_\ell E$ retains integral divisibility data that $V_\ell E$ forgets.

### 5.3 The Galois representation and continuity

Galois acts on every level and commutes with the transition maps, hence acts on the inverse limit. Choosing a $\mathbf Z_\ell$-basis yields

$$
\rho_{E,\ell}:G_K\longrightarrow\operatorname{GL}_2(\mathbf Z_\ell). \tag{5.6}
$$

The topology on $T_\ell E$ is its $\ell$-adic topology, equivalently the inverse-limit topology. The representation is continuous because its reduction modulo $\ell^r$ is the continuous finite representation on $E[\ell^r]$ for every $r$. The inverse images of the principal congruence subgroups

$$
1+\ell^rM_2(\mathbf Z_\ell)
$$

are therefore open and form a neighborhood basis at the identity.

This argument is stronger than saying that each vector has an open stabilizer. A Tate-module vector is an infinite compatible sequence and can have a small or even trivial stabilizer. Continuity concerns congruence neighborhoods, not pointwise openness at the infinite level.

Tensoring gives a continuous action on $V_\ell E$. Reducing the stable lattice gives $\overline\rho_{E,\ell}$. A different integral basis conjugates the representation by $\operatorname{GL}_2(\mathbf Z_\ell)$; a different basis of $V_\ell E$ may conjugate by all of $\operatorname{GL}_2(\mathbf Q_\ell)$ and can change which lattice appears as the reduction. For an elliptic curve the geometric lattice $T_\ell E$ is canonical even though its coordinates are not.

### 5.4 The cyclotomic module

The compatible roots of unity form

$$
\mathbf Z_\ell(1)=\varprojlim_r\mu_{\ell^r}, \tag{5.7}
$$

with transition maps $\zeta\mapsto\zeta^\ell$. It is free of rank one over $\mathbf Z_\ell$. Galois acts through the $\ell$-adic cyclotomic character

$$
\chi_\ell:G_K\longrightarrow\mathbf Z_\ell^\times, \tag{5.8}
$$

whose reduction modulo $\ell^r$ is $\chi_{\ell^r}$. For any $\mathbf Z_\ell$-module $M$ with continuous Galois action, set

$$
M(1)=M\otimes_{\mathbf Z_\ell}\mathbf Z_\ell(1).
$$

Negative twists use the dual rank-one module $\mathbf Z_\ell(-1)$. A twist changes the Galois action, not the underlying rank.

Passing (4.11) through the inverse limit gives

$$
\det\rho_{E,\ell}=\chi_\ell. \tag{5.9}
$$

Reducing gives $\det\overline\rho_{E,\ell}=\overline\chi_\ell$. Thus the determinant is known before any local reduction analysis.

### 5.5 The tower of torsion fields

The fields

$$
K\subseteq K(E[\ell])\subseteq K(E[\ell^2])\subseteq\cdots \tag{5.10}
$$

form a Galois tower. Their union is the field cut out by $T_\ell E$, and its Galois group over $K$ is the image of $\rho_{E,\ell}$ as a compact subgroup of $\operatorname{GL}_2(\mathbf Z_\ell)$. More precisely,

$$
\operatorname{im}\rho_{E,\ell}
\cong\varprojlim_r\operatorname{Gal}(K(E[\ell^r])/K). \tag{5.11}
$$

The transition maps on the Galois groups need not be surjective onto every abstract subgroup one might imagine; they are the restriction maps arising from the actual nested fields. Compactness follows either from this inverse limit or from closedness of the image of the compact group $G_K$.

Reduction modulo $\ell$ forgets the kernel

$$
\operatorname{im}\rho_{E,\ell}\cap
(1+\ell M_2(\mathbf Z_\ell)).
$$

Consequently a residual representation can be trivial or reducible while the full $\ell$-adic image is large. Conversely, irreducibility of $E[\ell]$ implies irreducibility of $V_\ell E$: a $G_K$-stable line in $V_\ell E$ intersects the canonical lattice in a saturated rank-one submodule, whose reduction supplies a stable residual line after choosing a primitive generator. The reverse implication can fail because two distinct $\ell$-adic characters may become equal modulo $\ell$ and create new residual subspaces.

This tower viewpoint explains why continuity is indispensable. The representation is not merely a compatible family of abstract actions; its image records a profinite Galois group and its congruence filtration records successive torsion fields.

## 6. Duality and the Tate twist

### 6.1 Passing the pairing to the limit

Compatibility (4.13) turns the finite Weil pairings into a continuous pairing

$$
e_\ell:T_\ell E\times T_\ell E\longrightarrow\mathbf Z_\ell(1), \tag{6.1}
$$

defined by

$$
e_\ell((P_r),(Q_r))=(e_{\ell^r}(P_r,Q_r))_r.
$$

It is $\mathbf Z_\ell$-bilinear, alternating, perfect, and Galois equivariant. Perfectness follows by reducing modulo every $\ell^r$: if a vector pairs trivially with everything, its image at every finite level is zero by finite-level nondegeneracy, so the vector is zero. Surjectivity of the induced duality map follows from finite-level surjectivity and completeness.

The target must be $\mathbf Z_\ell(1)$ rather than $\mathbf Z_\ell$ with trivial action. Roots of unity are not generally fixed by Galois. Forgetting the twist would turn the equivariance formula into a false invariance claim.

### 6.2 Self-duality

Write

$$
(T_\ell E)^*=\operatorname{Hom}_{\mathbf Z_\ell}(T_\ell E,\mathbf Z_\ell)
$$

with contragredient action

$$
(\sigma f)(x)=\sigma\bigl(f(\sigma^{-1}x)\bigr);
$$

the action on the scalar $\mathbf Z_\ell$ here is trivial. The Weil pairing gives a canonical isomorphism

$$
T_\ell E\xrightarrow{\sim}(T_\ell E)^*(1),\qquad
x\longmapsto(y\mapsto e_\ell(x,y)). \tag{6.2}
$$

After tensoring,

$$
V_\ell E\cong(V_\ell E)^*(1). \tag{6.3}
$$

At residual level,

$$
E[\ell]\cong E[\ell]^*(1). \tag{6.4}
$$

This is the correct self-duality: the representation is not ordinarily isomorphic to its untwisted dual. Taking determinants in (6.2) is consistent with $\det T_\ell E=\mathbf Z_\ell(1)$.

### 6.3 Matrix form and determinant

Choose a symplectic basis and let

$$
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

Galois equivariance becomes

$$
\rho(\sigma)^tJ\rho(\sigma)=\chi_\ell(\sigma)J. \tag{6.5}
$$

For every $2\times2$ matrix $A$ over a commutative ring,

$$
A^tJA=(\det A)J. \tag{6.6}
$$

Comparing (6.5) and (6.6) proves the determinant formula once again. In higher-dimensional symplectic spaces a similitude multiplier need not equal the determinant; dimension two is special.

If the basis is not symplectic, the pairing matrix is $uJ$ for some unit $u\in\mathbf Z_\ell^\times$, and the same calculation applies. Thus the formula does not depend on choosing compatible primitive roots or a normalized symplectic basis.

### 6.4 Orthogonal lines and quotient characters

Every line in a two-dimensional alternating space is its own orthogonal complement. Suppose the residual representation has a stable line on which $G_K$ acts through $\psi$. The quotient is then determined by the determinant:

$$
E[\ell]/L\cong\mathbf F_\ell(\overline\chi_\ell\psi^{-1}). \tag{6.7}
$$

In a basis adapted to $L$,

$$
\overline\rho_{E,\ell}\sim
\begin{pmatrix}
\psi&*\\0&\overline\chi_\ell\psi^{-1}
\end{pmatrix}. \tag{6.8}
$$

This simple identity is one of the most useful consequences of the Weil pairing. Once one constituent of a reducible elliptic-curve representation is known, the other is forced. The extension class remains extra information and need not vanish.

## 7. Isogenies and functoriality

### 7.1 Dual isogenies

Torsion modules should vary naturally with the elliptic curve. Isogenies provide the relevant maps. If $\varphi:E\to E'$ is an isogeny of degree $d$, there is a unique **dual isogeny**

$$
\widehat\varphi:E'\longrightarrow E
$$

satisfying

$$
\widehat\varphi\circ\varphi=[d]_E,\qquad
\varphi\circ\widehat\varphi=[d]_{E'}. \tag{7.1}
$$

The construction comes from pullback of degree-zero line bundles. Identifying each elliptic curve with its dual by the origin polarization, the dual morphism of abelian varieties becomes $\widehat\varphi$. The two identities follow from the norm-pullback relation for divisors.

Degrees multiply under composition, so (7.1) gives

$$
(\deg\varphi)(\deg\widehat\varphi)=d^2.
$$

In fact $\deg\widehat\varphi=d$. Separability need not agree: in characteristic $p$, Frobenius and Verschiebung illustrate how inseparability can be distributed between a map and its dual.

### 7.2 Kernels and quotient curves

If $\varphi$ is separable, its geometric kernel has $d$ points. Conversely, a finite subgroup scheme $C\subset E$ determines a quotient elliptic curve $E/C$ and an isogeny

$$
\pi:E\longrightarrow E/C
$$

with kernel $C$ and degree equal to the degree of $C$. Over a nonclosed field, the quotient and map descend to $K$ precisely when the subgroup scheme is defined over $K$.

When $d$ is prime to $\operatorname{char}K$, every degree-$d$ kernel is finite étale, so it is determined by its geometric points with their Galois action. When the characteristic divides $d$, a set of geometric points does not determine the kernel. A subgroup consisting set-theoretically only of $O$ may still have positive degree and yield a nontrivial inseparable isogeny.

This is the exact boundary of the familiar slogan “an isogeny is determined by its kernel.” The slogan is true for the kernel scheme. It is true for the set of geometric kernel points only in the separable case.

### 7.3 Maps on torsion and Tate modules

Because $\varphi$ commutes with multiplication, it induces compatible Galois-equivariant maps

$$
\varphi:E[n]\longrightarrow E'[n],\qquad
T_\ell\varphi:T_\ell E\longrightarrow T_\ell E'. \tag{7.2}
$$

If $(n,d)=1$, choose integers $a,b$ with $ad+bn=1$. On $E[n]$, the map $[a]\widehat\varphi$ is inverse to $\varphi$, since

$$
[a]\widehat\varphi\varphi=[ad]=[1-bn]=[1].
$$

Thus

$$
\varphi:E[n]\xrightarrow{\sim}E'[n]
\quad\text{when }(n,d)=1. \tag{7.3}
$$

For every $\ell\ne\operatorname{char}K$, the map on rational Tate modules is an isomorphism, because (7.1) makes its inverse $d^{-1}T_\ell\widehat\varphi$. On integral Tate modules it is injective with finite cokernel. The cokernel has order

$$
\ell^{v_\ell(d)}. \tag{7.4}
$$

To justify the exact exponent, use the compatibility of the Weil pairing below: in symplectic bases the determinant of $T_\ell\varphi$ generates the same ideal as $d$, and the index of the image of an injective endomorphism of a rank-two $\mathbf Z_\ell$-lattice is the absolute value of its determinant.

Consequently isogenous elliptic curves have isomorphic $\ell$-adic rational representations for every $\ell$ different from the field characteristic. Their integral lattices can differ at primes dividing the isogeny degree, and their residual representations at such primes need not be isomorphic.

### 7.4 Pairing compatibility and contravariance

The Weil pairing is functorial in the form

$$
e_n^{E'}(\varphi P,Q')
=e_n^E(P,\widehat\varphi Q') \tag{7.5}
$$

for $P\in E[n]$ and $Q'\in E'[n]$. This follows from pulling divisor functions back along $\varphi$ and using the defining relation between $\varphi$ and its dual. Taking $Q'=\varphi Q$ gives

$$
e_n^{E'}(\varphi P,\varphi Q)
=e_n^E(P,Q)^d. \tag{7.6}
$$

At Tate-module level the same formulas hold with values in $\mathbf Z_\ell(1)$. They show that the dual of $T_\ell\varphi$ under the self-dualities (6.2) is $T_\ell\widehat\varphi$. Thus covariance of points and contravariance of linear duals fit together exactly.

Functoriality also respects composition:

$$
T_\ell(\psi\circ\varphi)=T_\ell\psi\circ T_\ell\varphi,\qquad
\widehat{\psi\circ\varphi}=\widehat\varphi\circ\widehat\psi. \tag{7.7}
$$

The reversed order in the second identity is the usual reversal under duality.

### 7.5 A degree-two isogeny in coordinates

Assume $\operatorname{char}K\ne2$ and let

$$
E:y^2=x^3+ax^2+bx
$$

with $b(a^2-4b)\ne0$. The point $T=(0,0)$ has order two. The quotient by $\langle T\rangle$ is

$$
E':y^2=x^3-2ax^2+(a^2-4b)x, \tag{7.8}
$$

and the isogeny away from $O,T$ is

$$
\varphi(x,y)=
\left(x+a+\frac b x,
y\left(1-\frac b{x^2}\right)\right). \tag{7.9}
$$

Substitution verifies that the image lies on $E'$. The only poles occur at $O$ and $T$, and the map extends over them with both points in the kernel. Its degree is two, so there can be no further kernel point.

For

$$
E:y^2=x^3-x,
$$

this gives

$$
E':y^2=x^3+4x.
$$

The stable line generated by $(0,0)$ is the representation-theoretic shadow of the isogeny. Notice that $E[2]$ may contain two other points only over an extension; a rational kernel of order two does not imply full rational two-torsion.

### 7.6 Integral lattices at primes dividing the degree

The phrase “isogenous curves have the same Tate module” is true only after tensoring with $\mathbf Q_\ell$ when $\ell$ divides the isogeny degree. The integral defect can be described exactly. Let

$$
M=T_\ell\varphi:T_\ell E\longrightarrow T_\ell E'.
$$

Choose bases and take the Smith normal form

$$
UMV=\begin{pmatrix}\ell^a&0\\0&\ell^b\end{pmatrix},
\qquad 0\leq a\leq b,
$$

with $U,V$ invertible over $\mathbf Z_\ell$. Pairing compatibility gives $\det(M)$ equal to the degree $d$ up to a unit, so

$$
a+b=v_\ell(d),\qquad
\operatorname{coker}M\cong
\mathbf Z/\ell^a\mathbf Z\oplus
\mathbf Z/\ell^b\mathbf Z. \tag{7.10}
$$

This proves the index formula (7.4) and also records the possible shapes of the defect. For a separable cyclic isogeny of degree $\ell$, the pair is $(0,1)$: one primitive Tate direction survives integrally and the other is multiplied by $\ell$. For multiplication $[\ell]$, whose degree is $\ell^2$, the pair is $(1,1)$.

The reduction modulo $\ell$ explains why residual representations may change. In the cyclic case, $M$ has rank one modulo $\ell$; its kernel is the line corresponding to the isogeny kernel and its image is related to the dual-isogeny line on $E'[\ell]$. Although $V_\ell E$ and $V_\ell E'$ are the same rational representation, the two lattices sit at adjacent vertices in the lattice graph of that representation. Their mod-$\ell$ extensions can point in opposite directions.

Semisimplification removes this lattice dependence. Here is the integral reason, which avoids treating equality of characteristic polynomials as a substitute for a lattice argument. If $L$ and $L'$ are two stable lattices in the same rational representation, rescale one so that $L'\subset L$. Put $M=L/L'$. Reduction of the short exact sequence gives

$$
0\longrightarrow M[\ell]\longrightarrow L'/\ell L'
\longrightarrow L/\ell L\longrightarrow M/\ell M
\longrightarrow0. \tag{7.11}
$$

In the Grothendieck group of finite-length $\mathbf Z_\ell[G_K]$-modules, the two exact sequences

$$
0\to M[\ell]\to M\xrightarrow{\ell}\ell M\to0,
\qquad
0\to\ell M\to M\to M/\ell M\to0
$$

show that $M[\ell]$ and $M/\ell M$ have the same composition factors. Equation (7.11) therefore gives the same composition factors for $L'/\ell L'$ and $L/\ell L$. A chain of such inclusions handles arbitrary commensurable lattices. Their semisimplifications consequently agree. In the degree-$\ell$ situation, the common constituents are precisely the kernel character $\psi$ and the forced quotient character $\overline\chi_\ell\psi^{-1}$ from (6.8). What can change is the extension class joining them.

This lattice calculation is also the reason one must not invert the degree too early. Rationalizing makes functoriality simple, but it erases the kernel line that detects a rational isogeny and the finite index that controls residual congruences.

## 8. Cyclic isogenies and reducibility

### 8.1 Why invariant lines are geometric

A reducible two-dimensional representation can look like a statement about a chosen basis. For elliptic-curve torsion it has a basis-free geometric meaning: an invariant line is a finite subgroup of the curve, and quotienting by it produces an isogeny. This translation is a central bridge between Galois representations and the arithmetic geometry of elliptic curves.

The hypotheses matter. Let $\ell$ be prime and assume

$$
\ell\ne\operatorname{char}K. \tag{8.1}
$$

Then $E[\ell]$ is finite étale, so subgroup schemes of degree $\ell$ correspond exactly to $G_K$-stable subgroups of $E[\ell](K^s)$ of order $\ell$. Without (8.1), a connected kernel can have no nonzero geometric point and hence no corresponding line.

### 8.2 The equivalence for prime degree

**Theorem 8.1 (isogeny-line equivalence).** Under (8.1), the following are equivalent:

1. $E$ admits an isogeny of degree $\ell$ defined over $K$.
2. $E[\ell](K^s)$ contains a $G_K$-stable line.
3. $\overline\rho_{E,\ell}$ is reducible over $\mathbf F_\ell$.

**Proof.** If $\varphi:E\to E'$ has degree $\ell$, it is separable by (8.1). Its kernel has $\ell$ geometric points and is Galois stable because $\varphi$ is defined over $K$. Hence it is a stable line. Conditions 2 and 3 are the definition of reducibility.

Conversely, a stable line $L$ determines a finite étale subgroup scheme $C\subset E[\ell]$ over $K$: descent is effective because the finite set and all of its group operations are Galois stable. The quotient $E/C$ and quotient map are defined over $K$. Their degree is the degree of $C$, namely $\ell$. $\square$

The theorem asserts existence of a rational isogeny, not of a rational point of order $\ell$. If Galois acts on the kernel through a nontrivial character, no generator is rational. It also does not assert that the representation splits: the quotient line of a triangular matrix need not lift to a stable complement.

### 8.3 Composite cyclic kernels

For a positive integer $N$ prime to $\operatorname{char}K$, a **cyclic subgroup of order $N$** means a finite étale subgroup whose geometric points form $\mathbf Z/N\mathbf Z$. Inside

$$
E[N](K^s)\cong(\mathbf Z/N\mathbf Z)^2,
$$

such a subgroup is generated by a primitive vector, equivalently it is a rank-one direct summand. It is defined over $K$ exactly when Galois preserves it.

Thus cyclic degree-$N$ isogenies correspond to stable rank-one direct summands of $E[N]$. Merely finding a stable subgroup of order dividing $N$ is insufficient, and over the nonfield ring $\mathbf Z/N\mathbf Z$ the word “line” can be misleading. For example, the subgroup generated by $(2,0)$ in $(\mathbf Z/4\mathbf Z)^2$ has order two and is not a direct summand of rank one over $\mathbf Z/4\mathbf Z$.

Primary decomposition reduces the condition to compatible cyclic subgroups in $E[\ell^{v_\ell(N)}]$. The quotient isogeny has degree $N$. Under the standing prime-to-characteristic hypothesis its dual kernel is also geometrically cyclic, because it is the Cartier dual of the original cyclic kernel; its Galois character is the cyclotomic twist of the inverse kernel character. When the characteristic divides the degree, “cyclic” must instead be defined scheme-theoretically and this point-set conclusion is unavailable.

### 8.4 Rational torsion is stronger

Three increasingly strong conditions are often conflated:

$$
\begin{array}{c}
\text{a stable cyclic subgroup of order }\ell,\\
\text{a $K$-rational point of order }\ell,\\
\text{full rational }E[\ell].
\end{array}
$$

The first gives an isogeny. The second makes the kernel character trivial. The third makes the entire representation trivial. For an odd prime the implications cannot be reversed in general.

The Weil pairing supplies a useful obstruction to the last condition. If all of $E[n]$ is $K$-rational and $n$ is prime to the characteristic, take a symplectic basis. Galois equivariance then fixes a primitive $n$th root of unity, so

$$
\mu_n\subset K. \tag{8.2}
$$

Thus, for example, an elliptic curve over $\mathbf Q$ cannot have full rational $3$-torsion because $\mathbf Q$ does not contain a primitive cube root of unity. One rational $3$-isogeny causes no such contradiction.

### 8.5 The dual isogeny and the two characters

Suppose $E$ has a $K$-rational $\ell$-isogeny $\varphi:E\to E'$ with kernel character $\psi$. In an adapted basis, (6.8) shows that the quotient character is $\overline\chi_\ell\psi^{-1}$. The dual isogeny has kernel equal to the corresponding quotient direction in $E'[\ell]$, so its kernel character is

$$
\overline\chi_\ell\psi^{-1}. \tag{8.3}
$$

This is also a direct consequence of the pairing compatibility (7.5): the kernel of $\widehat\varphi$ is dual to the kernel of $\varphi$, with the cyclotomic twist supplied by $\mu_\ell$.

The extension entries for $E[\ell]$ and $E'[\ell]$ need not agree. An isogeny of degree $\ell$ is not an isomorphism on integral $\ell$-torsion, and it can exchange which of two extensions is visible. On $V_\ell$ the two curves are isomorphic, but reduction of different stable lattices can yield nonisomorphic residual extensions. Semisimplifications retain the same two characters:

$$
E[\ell]^{\mathrm{ss}}\cong E'[\ell]^{\mathrm{ss}}
\cong\mathbf F_\ell(\psi)\oplus
\mathbf F_\ell(\overline\chi_\ell\psi^{-1}). \tag{8.4}
$$

Thus rational isogeny preserves the residual constituents but may alter the way they are glued.

### 8.6 The scheme-theoretic boundary

Theorem 8.1 assumes $\ell\ne\operatorname{char}K$ for a structural reason, not merely to simplify notation. When $\ell=\operatorname{char}K$, an isogeny of degree $\ell$ may have a connected kernel with no nonzero geometric point. It then produces no invariant line in a two-dimensional point representation, because that point representation does not exist.

Relative Frobenius is the basic example. For an elliptic curve in characteristic $p$,

$$
F:E\longrightarrow E^{(p)}
$$

has degree $p$ and connected kernel. On geometric points its kernel consists only of the origin. Its dual Verschiebung may have an étale cyclic kernel in the ordinary case and a connected kernel in the supersingular case. The two degree-$p$ isogenies are equally genuine even though only one may be visible as a subgroup of points.

The right all-characteristic statement is therefore:

**Theorem 8.2 (subgroup-scheme form).** Isogenies $E\to E'$ of degree $n$ over $K$, up to isomorphism of the target, correspond to finite subgroup schemes $C\subset E$ of rank $n$ defined over $K$. The quotient is $E/C$, and the dual kernel is $C^D$ under the canonical kernel pairing.

**Proof.** The kernel of an isogeny is finite locally free of rank equal to its degree. Conversely, the faithfully flat quotient of an elliptic curve by a finite subgroup scheme is represented by an elliptic curve, and the quotient map has kernel $C$ and degree $\operatorname{rank}C$. A morphism with the same kernel factors uniquely through the quotient and induces a degree-one map of the targets, hence an isomorphism. Kernel duality identifies the kernel of the dual isogeny with $C^D$. $\square$

When $n$ is prime to the characteristic, finite locally free groups of rank $n$ killed by $n$ are étale, so Galois-stable geometric subgroups recover the same theorem. At the characteristic, only the subgroup-scheme formulation survives. This distinction also clarifies the phrase “rational subgroup”: it means a subgroup scheme defined over $K$ in arbitrary characteristic, while a Galois-stable set of geometric points is an equivalent description only in the étale case.

## 9. Good reduction and specialization

### 9.1 Why prime-to-residue torsion survives

Let $K$ be complete for a normalized discrete valuation, with ring $R$, residue field $k$, and residue characteristic exponent $p$. Suppose $E/K$ has good reduction. Book 49 then supplies a smooth proper group curve

$$
\mathcal E\longrightarrow\operatorname{Spec}R
$$

whose generic fiber is $E$ and whose special fiber $\widetilde E/k$ is an elliptic curve.

One expects torsion of order prime to $p$ to pass unchanged between the two fibers. The reason is differential: if $(n,p)=1$, then $[n]$ has invertible differential on the entire smooth family. Its kernel is therefore étale, so torsion points cannot collide under reduction. At $p$ the differential is no longer invertible and collision becomes possible; that case requires a separate chapter.

### 9.2 The specialization theorem

Fix an embedding of the maximal unramified extension $K^{\mathrm{nr}}$ into $K^s$, and identify its residue field with a separable closure $k^s$. Let $R^{\mathrm{sh}}$ be the strict henselization of $R$ inside $K^{\mathrm{nr}}$.

**Theorem 9.1 (prime-to-$p$ specialization).** If $E/K$ has good reduction and $(n,p)=1$, reduction induces a canonical isomorphism

$$
E[n](K^{\mathrm{nr}})\xrightarrow{\sim}
\widetilde E[n](k^s). \tag{9.1}
$$

Moreover every point of $E[n](K^s)$ is already defined over $K^{\mathrm{nr}}$. Hence

$$
E[n](K^s)\xrightarrow{\sim}\widetilde E[n](k^s) \tag{9.2}
$$

equivariantly for the quotient $G_K/I_K\cong G_k$.

**Proof strategy.** Show that the kernel of $[n]$ on the good model is finite étale of rank $n^2$. A finite étale object over a strictly henselian local ring is a disjoint union of copies of the base, so its generic and special geometric points are canonically the same. This simultaneously proves bijective specialization and unramifiedness.

**Proof.** On the smooth group curve $\mathcal E$, the differential of $[n]$ on the relative tangent line is multiplication by $n$, a unit in $R$. Translation identifies the differential at every point with the differential at the identity. Thus $[n]$ is étale. Fiberwise it is finite of degree $n^2$. Properness makes it proper, and a proper quasi-finite morphism is finite. Therefore

$$
\mathcal E[n]=\ker([n]:\mathcal E\to\mathcal E)
$$

is finite étale of rank $n^2$ over $R$.

Base change to $R^{\mathrm{sh}}$. Every finite étale algebra over a strictly henselian local ring is a finite product of copies of that ring: residue points lift uniquely by the henselian property, and idempotents separate the lifts. Consequently the $n^2$ sections of $\mathcal E[n]$ over $R^{\mathrm{sh}}$ specialize bijectively to its $n^2$ points over $k^s$. Their generic points give all of $E[n]$, because the generic fiber also has exactly $n^2$ geometric points. Thus every geometric torsion point is unramified and (9.1)--(9.2) follow. The construction commutes with the action of $G_K/I_K$ on both the strict henselization and its residue field, proving equivariance. $\square$

This proof uses only the elementary finite étale kernel of multiplication on a smooth family. It does not classify integral models of arbitrary finite group schemes.

### 9.3 Unramified representations

Taking $n=\ell^r$ in Theorem 9.1, with $\ell\ne p$, shows that inertia acts trivially at every level. Passing to the inverse limit gives

$$
\rho_{E,\ell}|_{I_K}=1. \tag{9.3}
$$

Thus good reduction implies that $T_\ell E$ is unramified for every coefficient prime away from the residue characteristic. The same is true of $E[\ell]$.

The converse—that unramifiedness of one prime-to-$p$ Tate module forces good reduction—is a deeper good-reduction criterion. It is important, but it is not needed to prove the specialization direction and should not be smuggled into that proof. The direction established here already supplies the local property most often used for a curve whose minimal equation is known to have unit discriminant.

Unramifiedness does not mean triviality. Frobenius can act nontrivially on the special-fiber torsion. Good reduction removes inertia; it leaves the arithmetic of the residue curve fully visible.

### 9.4 Frobenius and point counts

Assume now that $k=\mathbf F_q$. We use **arithmetic Frobenius** to mean the element acting on $k^s$ by

$$
x\longmapsto x^q. \tag{9.4}
$$

The same coordinate formula defines the Frobenius endomorphism $\pi$ of $\widetilde E$. Under specialization, arithmetic Frobenius acts on $T_\ell E$ as $\pi$ acts on $T_\ell\widetilde E$.

Let

$$
a_q=q+1-|\widetilde E(\mathbf F_q)|. \tag{9.5}
$$

Then for every $\ell\ne p$,

$$
\det\bigl(X-\rho_{E,\ell}(\operatorname{Frob}_q)\bigr)
=X^2-a_qX+q. \tag{9.6}
$$

**Proof strategy.** The kernel of $1-\pi$ consists exactly of the rational points. Its degree therefore gives the point count. The dual of Frobenius is Verschiebung, their composite is $[q]$, and their sum is multiplication by an integer $a_q$. These relations give the quadratic equation for $\pi$.

**Proof.** The fixed points of $\pi$ are precisely $\widetilde E(\mathbf F_q)$, so

$$
\ker(1-\pi)=\widetilde E(\mathbf F_q).
$$

The map $1-\pi$ is separable because its differential is $1$; hence

$$
\deg(1-\pi)=|\widetilde E(\mathbf F_q)|. \tag{9.7}
$$

Let $\widehat\pi$ be the dual isogeny. Since $\deg\pi=q$, duality gives $\widehat\pi\pi=[q]$. To identify $\pi+\widehat\pi$, recall that homomorphisms $E\to E^\vee$ fixed by duality correspond to divisor classes in the Néron--Severi group. For an elliptic curve, degree induces

$$
\operatorname{NS}(E)=\operatorname{Pic}(E)/\operatorname{Pic}^0(E)
\xrightarrow{\sim}\mathbf Z,
$$

because a divisor class has degree zero exactly when it lies in $\operatorname{Pic}^0(E)$. Under the origin polarization, the symmetric endomorphism associated with degree $a$ is $[a]$. Hence there is a unique integer $a$ such that

$$
\pi+\widehat\pi=[a]. \tag{9.8}
$$

Now duality of homomorphisms and distributivity of composition give

$$
(1-\widehat\pi)(1-\pi)
=[1]-[a]+[q]=[q+1-a].
$$

The dual of $1-\pi$ is $1-\widehat\pi$. By the defining property of a dual isogeny, the left side is $[\deg(1-\pi)]$. Equality of multiplication endomorphisms therefore gives

$$
\deg(1-\pi)=1-a+q.
$$

Comparison with (9.5) and (9.7) gives $a=a_q$, while multiplying (9.8) by $\pi$ gives

$$
\pi^2-[a_q]\pi+[q]=0. \tag{9.9}
$$

Apply $T_\ell$ and write $A=T_\ell(\pi)$. The determinant of $A$ is $q$, either from $\widehat\pi\pi=[q]$ or from the cyclotomic determinant, since arithmetic Frobenius raises prime-to-$p$ roots of unity to the $q$th power. For a $2\times2$ invertible matrix,

$$
A+(\det A)A^{-1}=(\operatorname{tr}A)I.
$$

The relation $A+qA^{-1}=a_qI$, obtained from (9.8), therefore gives $\operatorname{tr}A=a_q$. This proves the exact characteristic polynomial (9.6), not merely a polynomial that annihilates $A$. $\square$

The same degree form proves the Hasse bound without an analytic estimate. For integers $m,n$, duality gives

$$
\deg([m]-[n]\pi)=m^2-a_qmn+qn^2\ge0
$$

for all integers $m,n$. If $a_q^2>4q$, the real quadratic $X^2-a_qX+q$ is negative on a nonempty open interval. Choose a rational number $m/n$ in that interval and multiply by $n^2$; the displayed degree would be negative, a contradiction. Hence

$$
|a_q|\le2\sqrt q. \tag{9.10}
$$

Thus the Frobenius eigenvalues have product $q$, sum $a_q$, and complex absolute value $\sqrt q$.

### 9.5 A worked good-reduction count

Consider

$$
E:y^2=x^3-x
$$

over $\mathbf Q_5$. Its discriminant is $64$, a $5$-adic unit, so it has good reduction. Counting over $\mathbf F_5$ gives one affine point above each of $x=0,1,4$, two above each of $x=2,3$, and the point at infinity. Hence

$$
|E(\mathbf F_5)|=8,\qquad a_5=5+1-8=-2.
$$

For every $\ell\ne5$, inertia at $5$ acts trivially and arithmetic Frobenius has characteristic polynomial

$$
X^2+2X+5. \tag{9.11}
$$

Modulo $\ell$, the same polynomial describes Frobenius on $E[\ell]$. For $\ell=3$ it becomes $X^2-X+2$, irreducible over $\mathbf F_3$; this local irreducibility of one Frobenius element implies that the restricted representation cannot have a Frobenius-stable line over $\mathbf F_3$, though it says nothing by itself about representations at other curves or primes.

### 9.6 Isogeny invariance at good places

Let $E$ and $E'$ be isogenous over a number field or a local field, and suppose both have good reduction at a finite-residue place. For every $\ell$ away from the residue characteristic, the isogeny identifies $V_\ell E$ with $V_\ell E'$ as Galois representations. Therefore their Frobenius characteristic polynomials agree:

$$
X^2-a_q(E)X+q=X^2-a_q(E')X+q.
$$

It follows that

$$
|\widetilde E(\mathbf F_q)|=|\widetilde E'(\mathbf F_q)|. \tag{9.12}
$$

This conclusion can also be seen by reducing an isogeny of degree prime to the residue characteristic and comparing its finite kernel and cokernel on rational points, but the Tate-module argument treats all degrees uniformly after choosing an auxiliary $\ell$ not dividing the relevant characteristics.

The converse over a finite field is also true: equality of the Frobenius polynomial places two elliptic curves in the same isogeny class. Proving that converse requires constructing an isogeny from the endomorphism data and is not needed here. The forward direction already shows that $a_q$ is an isogeny invariant, while the precise group structure of $E(\mathbf F_q)$ need not be.

## 10. Bad reduction and inertia

### 10.1 Multiplicative reduction revisited

Good reduction suppresses inertia. Multiplicative reduction makes inertia visible in one unipotent direction. The previous volume gives the complete local description, and the general pairing theory now explains why its determinant is cyclotomic.

Let $K$ be a complete discretely valued field with finite residue field of characteristic $p$, let $E/K$ have multiplicative reduction, and let $\ell\ne p$. Let $q_E$ be its Tate parameter after the unramified splitting extension, let

$$
m=v(q_E)=v(\Delta_{\min}),
$$

and let $\eta$ be the unramified quadratic splitting character. A suitable basis gives

$$
\rho_{E,\ell}(\sigma)=
\begin{pmatrix}
\eta(\sigma)\chi_\ell(\sigma)&\eta(\sigma)c_{q_E,\ell}(\sigma)\\
0&\eta(\sigma)
\end{pmatrix}. \tag{10.1}
$$

On inertia, both $\eta$ and $\chi_\ell$ are trivial, and

$$
\rho_{E,\ell}(\sigma)=
\begin{pmatrix}
1&m\,t_\ell(\sigma)\\0&1
\end{pmatrix}. \tag{10.2}
$$

Here $t_\ell:I_K\to\mathbf Z_\ell$ is the $\ell$-primary tame character with the root conventions of the preceding volume. The determinant of (10.1) is $\eta^2\chi_\ell=\chi_\ell$, as the Weil pairing requires.

### 10.2 Residual inertia and discriminant divisibility

Reducing (10.2) modulo $\ell$ gives

$$
\overline\rho_{E,\ell}(\sigma)=
\begin{pmatrix}
1&\overline m\,\overline t_\ell(\sigma)\\0&1
\end{pmatrix}. \tag{10.3}
$$

Therefore

$$
\overline\rho_{E,\ell}|_{I_K}=1
\quad\Longleftrightarrow\quad
\ell\mid v(\Delta_{\min}). \tag{10.4}
$$

This is an assertion about inertia, not about the full local representation. When $\ell\mid m$, the unit part of $q_E$ can leave a nonzero unramified extension class detected by Frobenius. Nor does (10.4) say that the $\ell$-adic representation is unramified: over $\mathbf Q_\ell$, the nonzero integer $m$ never vanishes, so (10.2) always has nontrivial monodromy.

The $\ell$-adic inertia invariants have dimension one, wild inertia is trivial, and the conductor exponent is one. Residually it is one if $\ell\nmid m$ and zero if $\ell\mid m$. This difference is exactly why a large minimal discriminant exponent can disappear from a residual conductor.

### 10.3 A Tate-curve example

Take $K=\mathbf Q_7$ and $q_E=7^6\cdot2$. The Tate curve has split multiplicative reduction and

$$
v(\Delta_{\min})=6.
$$

For $\ell=3$, inertia acts integrally by

$$
\begin{pmatrix}1&6t_3\\0&1\end{pmatrix},
$$

so the residual action on inertia is trivial. Nevertheless the exact sequence

$$
0\to\mu_3\to E[3]\to\mathbf Z/3\mathbf Z\to0
$$

does not split over $\mathbf Q_7$ merely from this divisibility: splitting requires $q_E$ to be a cube. Its valuation is divisible by three, but its residue unit $2$ is not a cube in $\mathbf F_7^\times$, whose cubes are $1$ and $-1$. This separates unramifiedness, reducibility, and splitting in one calculation.

### 10.4 What additive reduction does imply

Additive reduction is not a single representation-theoretic shape. Two conditional statements, whose hypotheses are often established by a separate potential-reduction argument, are immediate from the theory already proved here.

If $E$ acquires good reduction over a finite extension $L/K$, then Theorem 9.1 makes $T_\ell E$ unramified over $L$ for every $\ell\ne p$. Hence an open subgroup of $I_K$ acts trivially and the inertia image on $T_\ell E$ is finite. This conclusion uses potential good reduction as a hypothesis; integrality of $j(E)$ is a necessary numerical sign of that possibility, but the construction of the good model is a separate theorem and is not being assumed silently.

If $v(j(E))<0$, the converse Tate-uniformization theorem from the preceding book does apply: $E$ is a quadratic twist of a Tate curve. When the reduction over $K$ is additive rather than multiplicative, the twisting character is ramified. After restricting to the splitting field, inertia has the unipotent Tate shape; over $K$ it is multiplied by the ramified quadratic scalar.

These alternatives give useful qualitative control once the relevant potential-reduction hypothesis has been proved. They do not give a universal integral matrix, conductor exponent, or residual inertia criterion from $v(\Delta_{\min})$ alone. In particular, this book never infers potential good reduction merely by reversing the easy implication that good reduction makes $j$ integral.

### 10.5 What additive reduction does not imply

No general conclusion of reducibility follows from additive reduction. A quadratic twist of a good curve may be additive while its residual representation remains irreducible; another additive curve may possess a rational isogeny and hence a reducible representation. Reduction type and global invariant lines answer different questions.

Nor does additive reduction force residual ramification for every $\ell\ne p$. A finite inertia image can collapse after reduction modulo a prime dividing its order. Conversely, residual ramification can persist even when coarse invariants look similar. In residue characteristics $2$ and $3$, wild inertia can contribute additional behavior not visible in the node-versus-cusp trichotomy.

One should therefore resist formulas that replace additive reduction by a single starred matrix. Precise conductor exponents require finer reduction types and ramification filtrations. The justified conclusions here are potential good or potential multiplicative behavior, finite versus unipotent inertia after suitable extension, and the absence of a universal reducibility statement.

## 11. At the residue characteristic

### 11.1 Why $\ell=p$ is a different problem

Let $K$ be complete with residue characteristic $p>0$. Away from $p$, multiplication by $\ell^r$ is étale on a good model, roots of unity are unramified, and specialization preserves all torsion. At $p$, every one of these statements can fail. The linear term of the formal multiplication series is divisible by $p$, $p$-power roots of unity are ramified in mixed characteristic, and the special fiber can have fewer geometric $p$-torsion points than the generic fiber.

There are also two distinct ambient characteristics. If $\operatorname{char}K=0$, multiplication by $p^r$ on the generic elliptic curve remains separable, and

$$
T_pE\cong\mathbf Z_p^2. \tag{11.1}
$$

If $\operatorname{char}K=p$, the geometric-point inverse limit has rank one for an ordinary curve and rank zero for a supersingular curve. Calling it a two-dimensional $p$-adic representation would be false.

The correct replacement for prime-to-$p$ specialization is finite-flat geometry. A finite locally free group scheme keeps its rank when points collide, and Cartier duality keeps the Weil pairing perfect even when the geometric-point pairing becomes trivial. This is why finite-flat groups and their duality are indispensable parts of the present theory.

### 11.2 Torsion on a good integral model

Suppose $E/K$ has good reduction, and let $\mathcal E/R$ be its smooth proper elliptic model. Multiplication by every positive integer $n$ is finite locally free of degree $n^2$. To recall the argument, a symmetric relatively ample line bundle $L$ satisfies

$$
[n]^*L\simeq L^{\otimes n^2}
$$

up to a line bundle from the base. Thus $[n]$ is fiberwise finite of degree $n^2$, and properness makes it finite. For flatness, the source and target fibers are smooth curves, hence Cohen--Macaulay and regular of the same dimension; finite miracle flatness applies on every fiber, and the fiberwise flatness criterion applies over $R$. This is also the multiplication theorem for abelian schemes proved in the finite-flat theory. Therefore

$$
\mathcal E[n]=\ker([n]:\mathcal E\to\mathcal E)
$$

is finite locally free of rank $n^2$ over $R$. No invertibility hypothesis on $n$ is used.

For $n=p^r$, the generic fiber in mixed characteristic is finite étale, while the special fiber can be nonreduced. They are nevertheless fibers of one rank-$p^{2r}$ group. The origin polarization extends over $R$, and Theorem 4.3 gives a perfect alternating pairing

$$
e_{p^r}:\mathcal E[p^r]\times_R\mathcal E[p^r]
\longrightarrow\mu_{p^r}. \tag{11.2}
$$

Thus good reduction supplies more than a generic Galois representation: it supplies a canonical finite-flat model of every finite torsion layer, compatible with multiplication, duality, and base change.

This model explains why reduction of point sets fails. Specialization is the base change of group schemes

$$
\mathcal E[p^r]\longmapsto\widetilde E[p^r],
$$

and preserves rank. It is not generally a bijection between generic and special geometric points. Distinct generic points may meet in a connected infinitesimal subgroup of the special fiber. Their lost separation is recorded by nilpotents in the special coordinate algebra.

### 11.3 Connected and étale directions

Assume that $R$ is henselian and that the residue field $k$ is perfect. Every finite locally free commutative group $G/R$ then has a functorial connected--étale sequence

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0, \tag{11.3}
$$

where $G^0$ has connected special fiber and $G^{\mathrm{et}}$ is finite étale. Henselianity lifts the special-fiber idempotents; perfection identifies the reduced component quotient as geometrically étale.

Apply this to $G=\mathcal E[p^r]$. Over an algebraic closure of $k$, an ordinary special fiber has

$$
0\longrightarrow\mu_{p^r}\longrightarrow
\widetilde E[p^r]\longrightarrow
\mathbf Z/p^r\mathbf Z\longrightarrow0. \tag{11.4}
$$

The sequence records the connected multiplicative part and the étale quotient. Because $\overline k$ is perfect, the reduced subgroup of the special fiber maps isomorphically to the étale quotient and gives a canonical splitting of this special-fiber connected--étale sequence. Identifying that reduced cyclic group with a particular copy of $\mathbf Z/p^r\mathbf Z$ still requires a generator. More importantly, the special-fiber splitting need not lift to a splitting of the connected--étale sequence over $R$. The geometric points see only the reduced étale factor, giving $\widetilde E[p^r](\overline k)\cong\mathbf Z/p^r\mathbf Z$. Cartier duality reverses (11.4), and the principal polarization makes the full sequence self-dual in this reversed sense.

For a supersingular special fiber, $\widetilde E[p^r]$ is connected, and its Cartier dual is connected as well. It is local-local rather than multiplicative or étale. Its group of geometric points is trivial although its rank is $p^{2r}$. In particular, it is generally false to replace it by $\alpha_{p^r}\times\alpha_{p^r}$: rank, connectedness, and tangent dimension do not determine the Hopf law.

These alternatives can be seen from $[p]=V\circ F$. Relative Frobenius has purely inseparable degree $p$, while Verschiebung has degree $p$. If $V$ is separable, its kernel has $p$ geometric points and the curve is ordinary. If $V$ is inseparable, $[p]$ has separable degree one and the curve is supersingular. Iteration gives separable degree $p^r$ in the ordinary case and one in the supersingular case. In the ordinary case multiplication by $p$ maps the visible $p^r$-torsion onto the visible $p^{r-1}$-torsion with kernel of order $p$, so the visible group is cyclic of order $p^r$. This supplies the detailed proof of the point assertions in Chapter 2.

### 11.4 The formal multiplication series

Let $E/K$ have an integral Weierstrass equation and let $T=-x/y$ be the formal parameter at the origin. Its formal group has a multiplication series

$$
[p](T)=pT+c_2T^2+c_3T^3+\cdots. \tag{11.5}
$$

If $p$ is invertible, the linear coefficient makes $[p]$ locally invertible. In residue characteristic $p$, that coefficient vanishes after reduction, so the first nonzero higher term controls the kernel near the origin.

For a good special fiber in characteristic $p$, after a suitable parameter the reduced series begins

$$
[p](T)=uT^{p^h}+\text{higher terms},\qquad u\ne0, \tag{11.6}
$$

where $h=1$ for ordinary reduction and $h=2$ for supersingular reduction. No formal-group classification is hidden here. In a local parameter, relative Frobenius has initial term a unit times $T^p$. Since $[p]=V\circ F$, the initial degree of $[p]$ is $p$ when $V$ is separable, which is exactly the ordinary case. When $V$ is inseparable, it too has initial degree $p$; the composite then has initial degree $p^2$. Its total degree is already $p^2$, so no larger initial degree is possible. This proves the two stated heights from the factorization in Section 2.4.

The **height** explains the point counts. Height one leaves an étale direction outside the connected formal kernel; height two uses the full degree $p^2$ in the connected direction, leaving no nonzero geometric $p$-torsion.

The formula also explains why the reduction map on $p$-torsion cannot be treated by the proof of Theorem 9.1. The kernel of $[p]$ on the integral model is not étale. Distinct generic points can specialize to the same special point, with their separation retained in infinitesimal structure.

### 11.5 Mixed characteristic and finite-flat representations

Suppose $\operatorname{char}K=0$ and the residue characteristic is $p$. Then $E[p^r](K^s)\cong(\mathbf Z/p^r)^2$ and $T_pE$ is free of rank two. The Weil pairing gives

$$
\det\rho_{E,p}=\chi_p
$$

exactly as before. What changes is local ramification. The character $\chi_p$ is ramified, and even good reduction does not imply that $T_pE$ is unramified.

At finite level, however, good reduction gives the canonical model $\mathcal E[p^r]$ of Section 11.2. In particular $E[p]$ is **finite flat over $R$**: its finite étale generic group scheme is the generic fiber of a finite locally free commutative group over $R$. This does not mean unramified. The group $\mu_p$ is finite flat over $R$, while its generic points carry the ramified mod-$p$ cyclotomic character.

The connected--étale sequence of $\mathcal E[p^r]$ provides an integral filtration in the ordinary-reduction case. Supersingular reduction has no étale special-fiber quotient. These integral alternatives should not be inferred merely from reduction of a chosen matrix: different lattices in one rational representation can have different special fibers.

For a Tate curve there is still an exact sequence

$$
0\longrightarrow\mathbf Z_p(1)
\longrightarrow T_pE_q
\longrightarrow\mathbf Z_p\longrightarrow0, \tag{11.7}
$$

whose extension class is the $p$-adic Kummer class of $q$. Both the cyclotomic line and roots of the unit part of $q$ can be ramified. The tame inertia matrix from Chapter 10 is therefore unavailable.

For good reduction, the formal group controls those generic $p$-power points that approach the origin. Ordinary and supersingular reduction lead to genuinely different connected--étale behavior. Describing the resulting representation with complete precision requires theories beyond the elementary specialization argument. The safe conclusions at this stage are rank two in mixed characteristic, cyclotomic determinant, failure of prime-to-$p$ unramifiedness, and sensitivity to the formal group.

### 11.6 Multiplicative reduction at the coefficient prime

Finite flatness can occur even when the curve itself has multiplicative reduction and hence has no smooth proper elliptic model. Let $K$ have mixed characteristic $(0,p)$, let $E/K$ have multiplicative reduction, and put

$$
m=v(\Delta_{\min}).
$$

After the unramified splitting extension, Tate uniformization gives

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0. \tag{11.8}
$$

Its extension class is the Kummer class of the Tate parameter $q$, with $v(q)=m$. This class comes from an integral $\mu_p$-torsor exactly when it has a unit representative modulo $p$th powers. Writing $q=\pi^m u$ gives

$$
[q]\text{ has a unit representative}
\quad\Longleftrightarrow\quad p\mid m. \tag{11.9}
$$

When $m=ps$, write $q=(\pi^s)^pa$ with $a\in R^\times$. For each $i\in\mathbf Z/p\mathbf Z$, take

$$
\mathcal G_i=\operatorname{Spec}R[T_i]/(T_i^p-a^i)
$$

and form their disjoint union. Multiplication uses $T_iT_j$ and divides by $a$ whenever $i+j$ crosses $p$. Since $a$ is a unit, this defines a finite locally free group of rank $p^2$. Its kernel over the zero component is $\mu_p$, its component label gives the constant quotient, and on the generic fiber $T_i=z$ corresponds to the Tate parameter $(\pi^s)^iz$. This proves sufficiency in (11.9). Conversely, pulling an integral extension back along $1\in\mathbf Z/p\mathbf Z$ gives a $\mu_p$-torsor over $R$, so its generic Kummer class must be represented by a unit. We have proved the exact statement available from Tate uniformization:

$$
\begin{aligned}
&\text{the distinguished Tate sequence (11.8), with its specified }\mu_p
\text{ subgroup and constant quotient,}\\
&\hspace{35mm}\text{extends over }R
\quad\Longleftrightarrow\quad p\mid v(\Delta_{\min}).
\end{aligned} \tag{11.10}
$$

In particular, the divisibility supplies a finite-flat model of the generic representation $E[p]$. The converse for the bare existence of some finite-flat model is stronger than (11.10). Even over an unramified extension of $\mathbf Q_p$ with $p$ odd, the distinct residual characters do not by themselves classify the schematic closures of the two lines in every possible model. Such a necessity statement requires an additional classification theorem and is not asserted here.

An unramified quadratic twist descends the constructed model through a finite étale sign and does not alter the sufficient divisibility criterion. At $p=2$ the residual cyclotomic character is trivial, so even the generic character distinction disappears; (11.10) still classifies the distinguished twisted Tate extension, but no abstract necessity follows. Ramified bases can admit still more integral models.

### 11.7 Equal characteristic

If $K$ itself has characteristic $p$, define the geometric-point $p$-adic inverse limit by the same formula. For an ordinary curve,

$$
\varprojlim_rE[p^r](K^s)\cong\mathbf Z_p,
$$

while for a supersingular curve it is zero. This module records only the étale part. It is not the object obtained by pretending that the prime-to-characteristic theorem remains valid.

For every $\ell\ne p$, nothing pathological occurs: $T_\ell E$ is free of rank two, the Weil pairing is perfect, the determinant is cyclotomic, and good reduction gives unramifiedness. Equal characteristic is therefore not itself the problem; equality between the torsion prime and the field characteristic is.

## 12. From a curve to a residual representation

### 12.1 The global package

Let $F$ be a number field, let $E/F$ be an elliptic curve, and let $\ell$ be a prime. Since $\operatorname{char}F=0$, the group $E[\ell](\overline F)$ is always a two-dimensional $\mathbf F_\ell$-vector space. Choosing a basis gives a continuous representation

$$
\overline\rho_{E,\ell}:G_F\longrightarrow
\operatorname{GL}_2(\mathbf F_\ell), \tag{12.1}
$$

well defined up to conjugacy, with

$$
\det\overline\rho_{E,\ell}=\overline\chi_\ell. \tag{12.2}
$$

This construction packages the arithmetic of $E$ into linear algebra. A place of good reduction away from $\ell$ gives unramifiedness. A multiplicative place away from $\ell$ gives a controlled unipotent inertia action. A stable line is equivalent to a rational $\ell$-isogeny. The Weil pairing supplies duality and determinant without any local calculation.

The representation is not automatically irreducible. Establishing irreducibility is a separate arithmetic problem, often translated by Theorem 8.1 into excluding rational isogenies. Nor does the construction alone determine behavior at places above $\ell$; that is where integral connected--étale information becomes essential.

### 12.2 Local statements away from $\ell$

Let $v$ be a finite place of $F$ with residue characteristic $p_v\ne\ell$. Restrict (12.1) to a decomposition group $G_{F_v}$.

If $E$ has good reduction at $v$, then

$$
\overline\rho_{E,\ell}|_{I_v}=1. \tag{12.3}
$$

If the residue field has size $q_v$, arithmetic Frobenius satisfies

$$
\det\left(X-\overline\rho_{E,\ell}(\operatorname{Frob}_v)\right)
\equiv X^2-a_vX+q_v\pmod\ell, \tag{12.4}
$$

where

$$
a_v=q_v+1-|\widetilde E(k_v)|.
$$

If $E$ has multiplicative reduction, put $m_v=v(\Delta_{\min})$. Then

$$
\overline\rho_{E,\ell}|_{I_v}\sim
\begin{pmatrix}1&\overline m_v\,\overline t_\ell\\0&1\end{pmatrix}. \tag{12.5}
$$

In particular it is unramified exactly when $\ell\mid m_v$. Split versus nonsplit reduction changes an unramified quadratic character on the diagonal but not this inertial formula.

At additive places no comparably uniform formula follows from the coarse reduction label. Potential behavior gives qualitative control, but precise residual ramification requires more data.

### 12.3 The Frey-type curve

Let $A,B\in F^\times$, put $C=A+B\ne0$, and consider

$$
E_{A,B}:y^2=x(x-A)(x+B). \tag{12.6}
$$

Its three nonzero two-torsion points are rational. Direct calculation gives

$$
\begin{aligned}
c_4&=16(A^2+AB+B^2),\\
\Delta&=16A^2B^2C^2,\\
j&=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}.
\end{aligned} \tag{12.7}
$$

These formulas connect the representation to the local equation theory. Suppose $A,B,C$ are integral at a place $v$ of odd residue characteristic and exactly one has positive valuation, so the other two are units. Then the displayed equation is integral and minimal, $c_4$ is a unit, and the curve has multiplicative reduction. If, for example, $v(A)>0$, then

$$
v(\Delta_{\min})=2v(A). \tag{12.8}
$$

At places dividing none of $2ABC$, the discriminant is a unit and the curve has good reduction.

Now specialize to

$$
A=a^\ell,\qquad B=b^\ell,\qquad C=c^\ell,\qquad
a^\ell+b^\ell=c^\ell, \tag{12.9}
$$

with a primitive triple and $\ell\ge5$. At an odd place $v\mid abc$, exactly one factor is divisible, and

$$
v(\Delta_{\min})=2\ell\,v(abc) \tag{12.10}
$$

with the evident interpretation that only the divisible factor contributes. Thus $\ell$ divides the minimal discriminant exponent. At such a place whose residue characteristic differs from $\ell$, the $\ell$-adic representation has nontrivial multiplicative monodromy, while (12.5) shows that the residual representation is unramified. A place above $\ell$ belongs instead to the residue-characteristic analysis of Section 12.4.

This disappearance of ramification is not mysterious cancellation. The integral inertia matrix contains the collision thickness $m_v$ in its off-diagonal entry, and reduction modulo $\ell$ kills it because the Diophantine exponent divides that thickness.

### 12.4 The places above two and above $\ell$

At places above $2$, the raw equation (12.6) is not enough. One must first make the explicit integral change appropriate to the parity pattern and prove minimality. Under the common normalization in which $2$ is a uniformizer, $v(A)\ge4$, $B$ is a unit, and $B-A\equiv1\pmod4$, the change

$$
x=4x',\qquad y=8y'+4x'
$$

gives

$$
y'^2+x'y'=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x', \tag{12.11}
$$

with

$$
v(\Delta_{\min})=2v(A)-8
$$

when $v(A)>4$. Only after this calculation may the multiplicative inertia criterion be applied. Different parity patterns require their own verified coordinate changes.

At a place $v\mid\ell$, the coefficient prime equals the residue characteristic. The representation remains two-dimensional because the number field has characteristic zero, and its determinant remains cyclotomic, but good reduction does not imply unramifiedness and the tame multiplicative formula does not apply.

There is nevertheless an exact finite-level conclusion. If $E$ has good reduction at $v$, the group $E[\ell]$ is the generic fiber of the finite locally free group $\mathcal E[\ell]$ over $\mathcal O_{F_v}$. Thus $\overline\rho_{E,\ell}|_{G_{F_v}}$ is finite flat. If $E$ has multiplicative reduction and

$$
\ell\mid v(\Delta_{\min}), \tag{12.12}
$$

the construction leading to (11.10), followed by finite étale descent in the nonsplit case, supplies a finite-flat model of $E[\ell]$ over $\mathcal O_{F_v}$. This is a sufficient condition over an arbitrary mixed-characteristic DVR. We do not reverse it for the abstract representation: failure of (12.12) rules out the distinguished Tate extension in its displayed order, but excluding every differently filtered model requires additional classification.

For the exponentiated Frey curve at a place $v\mid abc$ above $\ell$, formula (12.10) supplies the divisibility (12.12). Hence its residual representation is finite flat there even though the curve has multiplicative reduction. If $v\nmid abc$ and the curve has good reduction, finite flatness follows from the good model instead. The construction, unlike an abstract necessity statement, does not require $F_v/\mathbf Q_\ell$ to be unramified. The dyadic case retains the filtration caveat of Section 11.6, although the same divisibility still gives the distinguished model.

### 12.5 Reducibility as the remaining geometric branch

For the Frey-type curve and $\ell\ge5$, reducibility of $\overline\rho_{E,\ell}$ is equivalent to a rational cyclic isogeny of degree $\ell$. The visible rational two-torsion does not itself create a stable line in $E[\ell]$; torsion at different primes must not be conflated.

If the representation is reducible, it has the form

$$
\overline\rho_{E,\ell}\sim
\begin{pmatrix}
\psi&*\\0&\overline\chi_\ell\psi^{-1}
\end{pmatrix}. \tag{12.13}
$$

Determining whether such a rational $\ell$-isogeny can exist is not settled by the local torsion theory alone. It becomes a problem about rational points on modular curves and the arithmetic of their Jacobians. The achievement of the present theory is to isolate that remaining branch exactly: all representation-theoretic ambiguity has been translated into a concrete geometric subgroup.

### 12.6 The complete output

Starting with a nonzero-discriminant elliptic curve over a number field and a prime $\ell$, the construction now provides the following coherent data:

$$
\begin{array}{c|c}
\text{input from the curve}&\text{representation-theoretic output}\\ \hline
E[\ell]&\text{a continuous two-dimensional }\mathbf F_\ell\text{-module}\\
e_\ell&\det\overline\rho_{E,\ell}=\overline\chi_\ell\\
\text{good reduction at }v\nmid\ell&\text{unramifiedness and a Frobenius polynomial}\\
\text{multiplicative reduction at }v\nmid\ell&\text{unipotent inertia controlled by }v(\Delta_{\min})\\
\ell\mid v(\Delta_{\min})&\text{trivial residual inertia at that multiplicative place}\\
\text{a stable line in }E[\ell]&\text{a rational cyclic }\ell\text{-isogeny}\\
\text{good reduction at }v\mid\ell&\text{the finite-flat model }\mathcal E[\ell]\\
\text{multiplicative }v\mid\ell&\text{the sufficient construction (11.10) when }\ell\mid v(\Delta_{\min}).
\end{array} \tag{12.14}
$$

Every row has an exact hypothesis. Prime-to-characteristic separability is what makes geometric torsion rank two. The Weil pairing is what forces the cyclotomic determinant. Smooth proper reduction is what kills inertia away from the residue characteristic. Tate uniformization is what turns multiplicative degeneration into a Kummer extension. Subgroup descent is what turns reducibility into an isogeny.

### 12.7 Conclusion

Torsion is the finite shadow of multiplication on an elliptic curve, and the Tate module is the coherent limit of all those shadows. Their rank two is a separability theorem, not a formal consequence of the degree $n^2$. In positive characteristic the kernel scheme retains that degree while geometric points can lose an entire direction or both visible directions. Keeping scheme, geometric, and rational torsion distinct is therefore the first condition for a correct theory.

The Weil pairing supplies the organizing symmetry. It is alternating, perfect at levels prime to the characteristic, compatible through the tower, and equivariant under Galois. From it come the cyclotomic determinant and the twisted self-duality of every elliptic-curve Tate module. Isogenies respect that duality; away from their degree they preserve torsion exactly, and at their degree they change the integral lattice in a measured way. A rational cyclic kernel becomes a stable line, so reducibility acquires a geometric meaning.

Reduction then turns geometry into local Galois behavior. Good reduction preserves prime-to-residue torsion point for point and makes inertia trivial. Frobenius on the special fiber records both point counts and the characteristic polynomial of the representation. Multiplicative reduction contributes one Kummer-theoretic unipotent direction, whose residual survival is governed by the divisibility of the minimal discriminant exponent. Additive reduction admits no comparable one-line formula. At the residue characteristic, pointwise specialization is replaced by a finite-flat torsion model, its connected--étale sequence, and schematic Weil duality.

For a Frey-type curve these principles assemble into a precise two-dimensional residual representation: its determinant is cyclotomic, it is unramified at good places away from $\ell$, its multiplicative inertia is explicitly controlled, and under the stated coefficient-prime hypotheses its local representation at $\ell$ is finite flat. Its possible reducibility is exactly the existence of a rational $\ell$-isogeny. The arithmetic curve has thereby been converted into a linear object without losing the geometry that governs it. That conversion is the essential role of torsion and Tate modules in the arithmetic of elliptic curves.
