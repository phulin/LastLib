# Modular Curves and Rational Isogenies

## Contents

1. [The classification problem behind a rational isogeny](#1-the-classification-problem-behind-a-rational-isogeny)
   - [From torsion linear algebra to a curve](#11-from-torsion-linear-algebra-to-a-curve)
   - [Standing hypotheses and conventions](#12-standing-hypotheses-and-conventions)
   - [Four notions that must remain distinct](#13-four-notions-that-must-remain-distinct)
2. [The three level problems](#2-the-three-level-problems)
   - [Why level is a subgroup-scheme condition](#21-why-level-is-a-subgroup-scheme-condition)
   - [The problems $Y_0(N)$ and $Y_1(N)$](#22-the-problems-y_0n-and-y_1n)
   - [Full level and the Weil-pairing component](#23-full-level-and-the-weil-pairing-component)
   - [Exact characteristic hypotheses](#24-exact-characteristic-hypotheses)
   - [Worked comparisons and counterexamples](#25-worked-comparisons-and-counterexamples)
3. [Fine spaces, coarse curves, and descent](#3-fine-spaces-coarse-curves-and-descent)
   - [Why automorphisms obstruct a universal curve](#31-why-automorphisms-obstruct-a-universal-curve)
   - [The fine ranges](#32-the-fine-ranges)
   - [What a coarse rational point actually says](#33-what-a-coarse-rational-point-actually-says)
   - [Neutrality criteria and the exceptional automorphism locus](#34-neutrality-criteria-and-the-exceptional-automorphism-locus)
   - [Field of moduli is not automatically field of definition](#35-field-of-moduli-is-not-automatically-field-of-definition)
4. [The open curves and their natural maps](#4-the-open-curves-and-their-natural-maps)
   - [Forgetting structure](#41-forgetting-structure)
   - [Degeneracy maps](#42-degeneracy-maps)
   - [Atkin--Lehner involutions](#43-atkin--lehner-involutions)
   - [Duality as geometry](#44-duality-as-geometry)
5. [Compactification and cusps](#5-compactification-and-cusps)
   - [Why smooth elliptic curves are not enough](#51-why-smooth-elliptic-curves-are-not-enough)
   - [Néron polygons and stable level](#52-néron-polygons-and-stable-level)
   - [Tate parameters and cusp widths](#53-tate-parameters-and-cusp-widths)
   - [The fields of definition of cusps](#54-the-fields-of-definition-of-cusps)
   - [Maps at the boundary](#55-maps-at-the-boundary)
6. [Rational cyclic subgroups and rational isogenies](#6-rational-cyclic-subgroups-and-rational-isogenies)
   - [The exact equivalence away from the characteristic](#61-the-exact-equivalence-away-from-the-characteristic)
   - [A subgroup versus a generator](#62-a-subgroup-versus-a-generator)
   - [Reducible residual representations](#63-reducible-residual-representations)
   - [Kernel characters and the dual isogeny](#64-kernel-characters-and-the-dual-isogeny)
   - [Composite level and cyclicity](#65-composite-level-and-cyclicity)
7. [Low-level curves and explicit coordinates](#7-low-level-curves-and-explicit-coordinates)
   - [$X(1)$ and the first rational parametrizations](#71-x1-and-the-first-rational-parametrizations)
   - [$X_0(2)$ and $X_0(3)$](#72-x_02-and-x_03)
   - [$X_0(5)$ and what a formula proves](#73-x_05-and-what-a-formula-proves)
   - [Genus zero does not mean trivial arithmetic](#74-genus-zero-does-not-mean-trivial-arithmetic)
8. [Integral models away from and at the level](#8-integral-models-away-from-and-at-the-level)
   - [Good primes](#81-good-primes)
   - [The standard integral $X_0(p)$ model](#82-the-standard-integral-x_0p-model)
   - [Frobenius and Verschiebung branches](#83-frobenius-and-verschiebung-branches)
   - [The more delicate $X_1(p)$ model](#84-the-more-delicate-x_1p-model)
   - [Exact regularity and semistability scope](#85-exact-regularity-and-semistability-scope)
9. [Specializing rational points](#9-specializing-rational-points)
   - [Properness turns points into sections](#91-properness-turns-points-into-sections)
   - [Interior and cuspidal reduction](#92-interior-and-cuspidal-reduction)
   - [Specialization to components at the level prime](#93-specialization-to-components-at-the-level-prime)
   - [Auxiliary-prime point counts](#94-auxiliary-prime-point-counts)
   - [Local tests for a rational $p$-isogeny](#95-local-tests-for-a-rational-p-isogeny)
10. [Genus and the geometry of scarcity](#10-genus-and-the-geometry-of-scarcity)
    - [The canonical divisor calculation](#101-the-canonical-divisor-calculation)
    - [The genus formula for $X_0(N)$](#102-the-genus-formula-for-x_0n)
    - [Prime levels](#103-prime-levels)
    - [What genus does and does not prove](#104-what-genus-does-and-does-not-prove)
11. [From a Frey-type curve to a modular point](#11-from-a-frey-type-curve-to-a-modular-point)
    - [The reducibility branch](#111-the-reducibility-branch)
    - [The resulting point and its reduction data](#112-the-resulting-point-and-its-reduction-data)
    - [Choosing a base cusp](#113-choosing-a-base-cusp)
    - [The Abel--Jacobi doorway](#114-the-abel--jacobi-doorway)
12. [The geometric dictionary](#12-the-geometric-dictionary)
    - [From residual reducibility to geometry](#121-from-residual-reducibility-to-geometry)
    - [A hypothesis ledger](#122-a-hypothesis-ledger)
    - [Conclusion](#123-conclusion)

## 1. The classification problem behind a rational isogeny

### 1.1 From torsion linear algebra to a curve

Let $E$ be an elliptic curve over a field $K$, and let $p$ be a prime different from $\operatorname{char}K$. The group $E[p](K^s)$ is a two-dimensional vector space over $\mathbf F_p$. If the Galois action preserves a line $L$, then $L$ is not merely linear algebra: it is the geometric kernel of a degree-$p$ isogeny. The central problem of this book is to give that observation a global parameter space.

The first temptation is to classify equations for $E$ together with coordinates of points in $L$. That would be badly adapted to the problem. Coordinate changes obscure isomorphism, a generator of $L$ need not be rational, and in characteristic $p$ the kernel may be nonreduced and have too few geometric points. The correct object records the elliptic curve and its finite subgroup scheme up to isomorphism. Its compactification also records how both degenerate.

This leads to three related curves. The open curve $Y_0(N)$ remembers a cyclic subgroup of order $N$; $Y_1(N)$ remembers a generator; full level remembers an ordered basis of the entire $N$-torsion. Their compactifications are denoted $X_0(N)$, $X_1(N)$, and $X(N)$. The notation hides two categorical layers: in general there is a moduli stack, which remembers automorphisms, and a coarse curve, which remembers geometric isomorphism classes. Rational-point arguments must know which layer is being used.

Our endpoint is a geometric dictionary. Under the appropriate characteristic and descent hypotheses,

$$
\overline\rho_{E,p}\text{ reducible over }\mathbf F_p
\quad\Longleftrightarrow\quad
E\text{ has a }K\text{-rational cyclic }p\text{-isogeny}
\quad\Longrightarrow\quad
X_0(p)(K)\text{ has a noncuspidal point}. \tag{1.1}
$$

The reverse implication in the last arrow needs care because a point on a coarse space can have a field-of-moduli obstruction. Much of the book exists to make every qualification in (1.1) visible rather than leaving it inside a slogan.

### 1.2 Standing hypotheses and conventions

All fields come with a chosen separable closure $K^s$ and absolute Galois group $G_K$. An elliptic curve includes its identity section. If $N$ is invertible in $K$, then $E[N]$ is finite étale of rank $N^2$ and

$$
E[N](K^s)\simeq(\mathbf Z/N\mathbf Z)^2.
$$

At a characteristic dividing $N$, statements are made about finite locally free subgroup schemes and effective Cartier divisors, never merely about geometric point sets. A subgroup scheme of rank $N$ is called cyclic away from $N$ when its geometric points are cyclic of order $N$; at a level characteristic, cyclicity means the Drinfeld divisor condition described in Chapter 2.

The symbols $Y_0(N)$ and $X_0(N)$ will normally denote coarse curves over $\mathbf Z$ or the relevant field. Their stack versions will be called the $\Gamma_0(N)$ moduli stack. When a statement needs a universal family, it is made on the stack or on a fine auxiliary cover. This convention is essential: $[-1]$ preserves every cyclic subgroup, so bare $\Gamma_0(N)$ level never removes the generic automorphism.

For a discrete valuation ring $R$ we write $K$ for its fraction field and $k$ for its residue field. “Reduction of a point” always refers to a specified proper integral model. A rational point on an abstract generic-fiber curve has no intrinsic reduction until such a model is chosen.

### 1.3 Four notions that must remain distinct

Four conditions occur repeatedly:

1. a subgroup scheme $C\subset E[N]$ is defined over $K$;
2. the abstract geometric subgroup $C(K^s)$ is stable under $G_K$;
3. $C$ has a generator in $E(K)$;
4. the geometric isomorphism class of $(E,C)$ is fixed by $G_K$.

When $N$ is invertible, conditions 1 and 2 are equivalent by finite étale descent. Condition 3 is stronger: if $P$ generates $C(K^s)$, Galois may act through a nontrivial character

$$
\psi:G_K\longrightarrow(\mathbf Z/N\mathbf Z)^\times,
\qquad \sigma P=\psi(\sigma)P. \tag{1.2}
$$

Condition 4 says only that the coarse moduli point is rational. It supplies isomorphisms $(E,C)^\sigma\simeq(E,C)$ but not necessarily a compatible cocycle and hence not necessarily a model over $K$.

At characteristic dividing $N$, even the passage from 1 to a statement about point sets breaks down. The group scheme $\mu_p$ in characteristic $p$ has rank $p$ and only one geometric point. It can be a genuine isogeny kernel although no nonzero geometric point generates it. This counterexample will guard every later use of the word “cyclic.”

## 2. The three level problems

### 2.1 Why level is a subgroup-scheme condition

Level structure is designed to retain a finite part of an elliptic curve while the curve varies in a family. A definition based only on points over the ground field is not stable under base change: a generator may appear after an extension, and distinct points can coalesce in characteristic dividing the level. Finite locally free subgroup schemes have constant rank, commute with base change, and retain nilpotent thickness. They are therefore the correct objects.

Let $E\to S$ be an elliptic curve. When $N$ is invertible on $S$, $E[N]$ is finite étale, so étale-locally it is the constant module $(\mathbf Z/N\mathbf Z)^2$. In that setting the subgroup-scheme definitions reduce to familiar finite-module language. When $N$ is not invertible, the same definitions must be strengthened by divisor conditions so that the intended rank is not lost in a nonreduced fiber.

### 2.2 The problems $Y_0(N)$ and $Y_1(N)$

A $\Gamma_0(N)$-structure on $E/S$ is a cyclic finite locally free subgroup scheme

$$
C\subset E[N]
$$

of rank $N$. If $N$ is invertible on $S$, this means that after an étale cover of $S$, the subgroup is generated by a point of exact order $N$. Over a field $K$ with $\operatorname{char}K\nmid N$, it is equivalent to a $G_K$-stable cyclic subgroup of $E[N](K^s)$.

When a residue characteristic divides $N$, one asks locally for a section $P$ such that

$$
C=\sum_{a\in\mathbf Z/N\mathbf Z}[aP] \tag{2.1}
$$

as effective Cartier divisors. This is cyclicity in the Drinfeld sense. The equality counts scheme-theoretic multiplicity; it does not assert that the sections $aP$ are distinct. On a generalized elliptic curve one also requires the divisor to meet every irreducible component. That ampleness condition becomes indispensable at the boundary.

A $\Gamma_1(N)$-structure remembers the generator rather than only its span. Away from $N$ it is a section $P\in E[N](S)$ having exact order $N$ on every geometric fiber. At level characteristics it is a Drinfeld point: the divisor in (2.1) is required to be a finite locally free subgroup divisor of rank $N$. The forgetful transformation is

$$
(E,P)\longmapsto(E,\langle P\rangle). \tag{2.2}
$$

Over a field of characteristic prime to $N$, the fiber of this map above $(E,C)$ consists of the $\varphi(N)$ generators of $C$, subject on coarse curves to possible identifications by automorphisms. Thus $Y_1(N)$ is the oriented version of $Y_0(N)$.

### 2.3 Full level and the Weil-pairing component

When $N$ is invertible, a full level-$N$ structure is an isomorphism

$$
\alpha:(\mathbf Z/N\mathbf Z)^2_S\xrightarrow{\sim}E[N]. \tag{2.3}
$$

Writing $P=\alpha(1,0)$ and $Q=\alpha(0,1)$, the Weil pairing produces a primitive root

$$
e_N(P,Q)\in\mu_N(S). \tag{2.4}
$$

A basis change by $g\in\operatorname{GL}_2(\mathbf Z/N\mathbf Z)$ raises this root to the power $\det g$. Consequently the full-level space over $\mathbf Q$ is not one geometrically connected curve with a forgotten determinant. Its components are organized by primitive $N$th roots of unity. Fixing $e_N(P,Q)=\zeta_N$ selects the component naturally defined over $\mathbf Q(\zeta_N)$ and analytically uniformized by $\Gamma(N)$.

There is an immediate arithmetic obstruction. If both $P$ and $Q$ are $K$-rational, Galois equivariance of the Weil pairing forces the primitive root $e_N(P,Q)$ to lie in $K$. Thus full rational level $N$ implies

$$
\mu_N\subset K. \tag{2.5}
$$

Over $\mathbf Q$, for example, no elliptic curve has a rational ordered basis of its full $3$-torsion. This does not prohibit a rational $3$-isogeny or even a rational point of order $3$; it prohibits only full level. The three moduli problems measure genuinely different strengths of rationality.

At characteristics dividing $N$, a homomorphism $\alpha:(\mathbf Z/N\mathbf Z)^2\to E[N]$ is a Drinfeld basis when

$$
\sum_{a\in(\mathbf Z/N\mathbf Z)^2}[\alpha(a)]=E[N] \tag{2.6}
$$

as effective Cartier divisors. It need not be an isomorphism of group schemes. On a supersingular curve in characteristic $p$, all values may have the same underlying point while (2.6) still records total length $p^2$. This explains why the prime-to-level definition cannot simply be copied into level characteristic.

### 2.4 Exact characteristic hypotheses

The elementary descriptions may be summarized as follows.

| Level datum | If $\operatorname{char}K\nmid N$ | If $\operatorname{char}K\mid N$ |
|---|---|---|
| $\Gamma_0(N)$ | stable cyclic subgroup of $E[N](K^s)$ | cyclic finite locally free subgroup scheme; point set is insufficient |
| $\Gamma_1(N)$ | $K$-rational point of exact order $N$ | Drinfeld point/divisor of exact order |
| full level | ordered basis of $E[N](K^s)$ with descent | Drinfeld basis; not generally a group-scheme isomorphism |
| degree-$p$ isogeny versus line | equivalent for $p\ne\operatorname{char}K$ | false as a point-set statement |

In particular, the representation $G_K\to\operatorname{GL}_2(\mathbf F_p)$ on $E[p](K^s)$ is two-dimensional only for $p\ne\operatorname{char}K$. The rational-isogeny/reducibility equivalence in Chapter 6 always carries that hypothesis.

### 2.5 Worked comparisons and counterexamples

Suppose $K$ has characteristic different from $2$ and

$$
E:y^2=x(x-a)(x-b)
$$

with $a,b\in K$ distinct and nonzero. The three nonzero points of $E[2]$ are rational. Each gives both a $\Gamma_1(2)$-structure and a $\Gamma_0(2)$-structure; there is no difference because a group of order two has a unique nonidentity generator.

For an odd prime $p$, take a stable line $C\subset E[p]$ on which Galois acts through a nontrivial character $\psi$. Then $(E,C)$ defines $\Gamma_0(p)$ level over $K$, but no nonzero point of $C$ is $K$-rational. Hence it gives a $K$-object for $Y_0(p)$ and none for $Y_1(p)$. This is not an exceptional pathology; it is the typical distinction between a rational isogeny and rational torsion.

For a characteristic-$p$ counterexample, let $E$ be ordinary over an algebraically closed field of characteristic $p$. Its connected subgroup $\ker F$ has rank $p$ but only the identity as a geometric point. The quotient by it is the relative Frobenius, an isogeny of degree $p$. No one-dimensional subspace of the geometric point group describes this kernel. This is precisely why the later equivalence excludes $p=\operatorname{char}K$.

## 3. Fine spaces, coarse curves, and descent

### 3.1 Why automorphisms obstruct a universal curve

A fine moduli space must carry a universal object whose pullback classifies every family uniquely. An object with a nontrivial automorphism contradicts this uniqueness. Every elliptic curve has $[-1]$, so the $j$-line is only a coarse space. Adding a cyclic subgroup does not help: $[-1]$ preserves every subgroup. Thus $Y_0(N)$ is intrinsically a coarse curve attached to a stack with generic stabilizer $\{\pm1\}$.

A chosen generator usually kills $[-1]$, since $-P=P$ only for order at most two. A full basis is still more rigid. This is why $X_1(N)$ and $X(N)$ often possess universal families in ranges where $X_0(N)$ cannot.

The special values $j=0$ and $1728$ require additional care in characteristic different from $2$ and $3$, because the geometric automorphism group is larger. In characteristics $2$ and $3$ the stabilizer picture is more complicated still. A statement about coarse points that ignores these loci has silently assumed away its hardest descent cases.

### 3.2 The fine ranges

Over $\mathbf Z[1/N]$, full level $N\ge3$ kills automorphisms and gives a fine moduli scheme after a Weil-pairing component is selected over its cyclotomic base. The $\Gamma_1(N)$ problem is fine for $N\ge4$ over $\mathbf Z[1/N]$. The small levels retain automorphisms. Bare $\Gamma_0(N)$ is never fine because $[-1]$ survives.

These are prime-to-level assertions. At a prime dividing $N$, a Drinfeld basis can collapse set-theoretically and fail to rigidify an object. Therefore a level which is fine on the generic fiber need not yield a fine integral problem at the level prime. A prime-to-level auxiliary structure, customarily full level $M\ge3$ with $(M,N)=1$, restores rigidity for local calculations.

On a fine space $Y$, a $K$-rational point really does pull the universal family back to an elliptic curve with the stated level over $K$. This simple sentence is one of the chief benefits of rigidification.

### 3.3 What a coarse rational point actually says

For the explicit Galois-cocycle calculation in this section, assume that $N$ is invertible in $K$. At a level characteristic the same stack-versus-coarse distinction remains, but descent must be formulated for finite locally free subgroup schemes in the relevant flat topology; a calculation using only $K^s$-points does not see connected level.

Let $x\in Y_0(N)(K)$ be a rational point of the coarse curve, and choose a geometric point above it represented by $(E,C)$ over $K^s$. Rationality of $x$ says that for every $\sigma\in G_K$ there exists an isomorphism

$$
\phi_\sigma:(E,C)^\sigma\xrightarrow{\sim}(E,C). \tag{3.1}
$$

It does not say that the $\phi_\sigma$ can be chosen to satisfy

$$
\phi_{\sigma\tau}=\phi_\sigma\,{}^\sigma\!\phi_\tau. \tag{3.2}
$$

The defect in (3.2) is a $2$-cocycle with values in the geometric automorphism group $\operatorname{Aut}(E,C)$. The point is represented by a pair over $K$ exactly when this gerbe is neutral, equivalently when compatible descent data exist. This is the precise descent obstruction behind the phrase “coarse rational point.”

Concretely, choose arbitrary isomorphisms $\phi_\sigma$. Then

$$
a_{\sigma,\tau}
=\phi_\sigma\,{}^\sigma\!\phi_\tau\,\phi_{\sigma\tau}^{-1}
\in\operatorname{Aut}(E,C). \tag{3.3}
$$

Changing the $\phi_\sigma$ changes $a_{\sigma,\tau}$ by a coboundary. When the automorphism group is abelian and its Galois action has been fixed, the class lies in the corresponding second cohomology set or group. In general it is a nonabelian gerbe class. Vanishing means that the $\phi_\sigma$ can be adjusted to satisfy (3.2), after which effective descent produces $(E_0,C_0)/K$.

This calculation also explains why a rational lift to a fine cover resolves the problem. On the fine cover there are no stabilizers, so the only possible $a_{\sigma,\tau}$ is the identity. Conversely, the existence of a geometric lift whose Galois orbit does not close over $K$ is not enough; the lift itself must be $K$-rational or carry compatible descent.

Once a representative $(E_0,C_0)$ over $K$ exists and $N$ is invertible, $C_0(K^s)$ is $G_K$-stable and the quotient isogeny $E_0\to E_0/C_0$ is defined over $K$. Thus the issue lies before the isogeny: it is the existence of the representative, not descent of the quotient from an already descended subgroup scheme.

### 3.4 Neutrality criteria and the exceptional automorphism locus

There are several exact ways to remove the obstruction.

- If the moduli problem is fine, a rational point has a representative by universality.
- If $N$ is invertible in $K$ and one is given an actual elliptic curve $E/K$ and a $G_K$-stable subgroup $C\subset E[N](K^s)$, finite étale descent constructs the pair directly; no coarse-space argument is needed.
- If $N$ is invertible in $K$, $\operatorname{char}K\ne2,3$, $j(E)\notin\{0,1728\}$, and a coarse point of $Y_0(N)$ has that $j$-value, then it has a representative over $K$.

The last assertion deserves proof. Assume that $N$ is invertible in $K$. Choose an elliptic curve $E_0/K$ with the given $j$-invariant and an isomorphism $f:E\to E_{0,K^s}$. Put $C_0=f(C)$. The coarse invariance (3.1) says that $C_0^\sigma$ is carried to $C_0$ by an automorphism of $E_{0,K^s}$. Away from $j=0,1728$, every such automorphism is $\pm1$, and both preserve every subgroup. Therefore $C_0^\sigma=C_0$. Finite étale descent gives $C_0$ over $K$.

More generally, the same proof works whenever every geometric automorphism of $E_0$ preserves $C_0$. At the exceptional $j$-values this can be checked subgroup by subgroup. If it fails, rationality of the coarse point alone is not a license to choose a $K$-model.

### 3.5 Field of moduli is not automatically field of definition

The obstruction is often invisible over familiar arithmetic fields because the point under study was constructed from an elliptic curve already defined over that field. That is exactly the situation for a Frey curve: reducibility produces an actual stable subgroup inside an actual $E/K$, so the associated point has no descent ambiguity.

The distinction matters in the reverse direction. Starting from an arbitrary $x\in Y_0(N)(K)$, one may conclude unconditionally only that a geometric isomorphism class has field of moduli $K$. To conclude that $x$ is a $K$-rational isogeny, one must cite neutrality, a fine lift, the generic-automorphism criterion, or an explicit representative.

Twists illustrate why coarse data forget information. Curves with the same $j$-invariant become isomorphic over $K^s$ but need not be isomorphic over $K$. A coarse point can therefore remain fixed while the descended object changes by a twist. For $\Gamma_0$ level, $[-1]$ acts trivially on the subgroup as an unoriented object; for $\Gamma_1$ level it usually changes a generator to its negative. The two moduli problems consequently have different descent behavior even above the same underlying $j$-value.

## 4. The open curves and their natural maps

### 4.1 Forgetting structure

The inclusions of congruence conditions give maps

$$
Y(N)\longrightarrow Y_1(N)\longrightarrow Y_0(N)\longrightarrow Y(1). \tag{4.1}
$$

On objects, they retain the first basis vector, retain only its span, and finally forget the subgroup. Over a field of characteristic prime to $N$, the geometric degree of the last map is the number of cyclic order-$N$ direct summands of $(\mathbf Z/N\mathbf Z)^2$, namely

$$
N\prod_{q\mid N}\left(1+\frac1q\right). \tag{4.2}
$$

This is a generic degree on coarse curves. At elliptic points, an automorphism can identify choices; at cusps, the compactified map ramifies. Neither phenomenon changes the function-field degree.

The map $Y_1(N)\to Y_0(N)$ records the loss of orientation. Away from exceptional automorphisms, its geometric fiber has $\varphi(N)/2$ points on coarse curves because $P$ and $-P$ define isomorphic $\Gamma_1$ objects through $[-1]$ when one passes to coarse isomorphism classes. On stacks the subgroup has $\varphi(N)$ generators and the stabilizer bookkeeping retains the missing factor. This is a useful reminder that stack degree and naive coarse fiber cardinality need not coincide.

### 4.2 Degeneracy maps

Let $M$ and $n$ be coprime. A cyclic subgroup $C\subset E[Mn]$ has canonical primary pieces

$$
C_M=C[M],\qquad C_n=C[n],\qquad C=C_M\oplus C_n, \tag{4.3}
$$

of ranks $M$ and $n$. There are two basic maps from level $Mn$ to level $M$:

$$
\alpha(E,C)=(E,C_M), \tag{4.4}
$$

and

$$
\beta(E,C)=\bigl(E/C_n,\ \text{image of }C_M\bigr). \tag{4.5}
$$

The first forgets the $n$-part. The second quotients by it and transports the coprime $M$-part. Because $(M,n)=1$, the quotient map is an isomorphism on $M$-torsion, so the transported subgroup has the right rank and cyclicity.

These maps extend to compactifications, with canonical contractions of unused polygon components. At primes not dividing $Mn$ they are maps between smooth integral models. At a prime dividing $n$, they see connected and étale subgroup schemes and need not be étale.

Over $\mathbf C$, the same maps arise from inclusions and conjugates of congruence subgroups. Writing

$$
E_\tau=\mathbf C/(\mathbf Z+\mathbf Z\tau),
$$

a cyclic subgroup can be represented by a primitive vector in $(\mathbf Z/N\mathbf Z)^2$, and changing the lattice basis acts through $\operatorname{SL}_2(\mathbf Z)$. Consequently

$$
Y_0(N)(\mathbf C)\simeq\Gamma_0(N)\backslash\mathfrak H,
\qquad
\Gamma_0(N)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}:c\equiv0\pmod N
\right\}, \tag{4.6a}
$$

with the usual orbifold meaning at elliptic fixed points. Similarly $\Gamma_1(N)$ fixes a chosen primitive vector and $\Gamma(N)$ fixes a full basis. The analytic quotient proves connectedness of the standard component and makes indices computable; the algebraic moduli problem supplies descent, integral models, and rational points. Neither description replaces the other.

### 4.3 Atkin--Lehner involutions

Suppose $Q$ is an exact divisor of $N$:

$$
Q\mid N,\qquad (Q,N/Q)=1. \tag{4.6}
$$

Write $C_Q=C[Q]$ and $C_{N/Q}=C[N/Q]$, so that $C=C_Q\oplus C_{N/Q}$. The Atkin--Lehner involution $w_Q$ quotients by $C_Q$ and installs the dual $Q$-kernel together with the transported complementary level:

$$
w_Q(E,C)=\left(E/C_Q,(E[Q]/C_Q)\oplus\overline C_{N/Q}\right). \tag{4.7}
$$

Here $E[Q]/C_Q$ is identified with the kernel of the dual isogeny $E/C_Q\to E$, and $\overline C_{N/Q}$ is the image of $C_{N/Q}$. The coprimality in (4.6) is what lets the two pieces be handled independently. Applying the construction twice returns an isomorphic pair, so it induces an involution on the coarse curve.

At prime level,

$$
w_p(E,C)=\bigl(E/C,E[p]/C\bigr). \tag{4.8}
$$

Thus $w_p$ exchanges an isogeny with its dual. For squarefree $N$, the involutions $w_q$ for $q\mid N$ commute, and their products give $w_Q$ for all exact divisors $Q$.

### 4.4 Duality as geometry

Let $\varphi:E\to E'=E/C$ be a separable cyclic isogeny of degree $N$. Its dual satisfies

$$
\widehat\varphi\circ\varphi=[N]_E,
\qquad
\varphi\circ\widehat\varphi=[N]_{E'}. \tag{4.9}
$$

The kernel of $\widehat\varphi$ is $E[N]/C$ after transport through $\varphi$. Hence the two projections

$$
\pi_1(E,C)=E,\qquad \pi_2(E,C)=E/C. \tag{4.10}
$$

are exchanged by $w_N$:

$$
\pi_1\circ w_N=\pi_2,\qquad \pi_2\circ w_N=\pi_1. \tag{4.11}
$$

This identity is more than symmetry of a diagram. It will identify the two branches of the bad fiber at a prime level, exchange the two standard cusps, and interchange the two characters occurring in a reducible residual representation.

## 5. Compactification and cusps

### 5.1 Why smooth elliptic curves are not enough

The open modular curve is not proper. Analytically, a lattice $\mathbf Z+\mathbf Z\tau$ degenerates as $\operatorname{Im}\tau$ tends to infinity. Algebraically, a family of elliptic curves over the fraction field of a DVR can acquire multiplicative reduction. If we merely add a point to the parameter curve, no object would live above that point and the moduli interpretation would stop exactly where properness begins to be useful.

The remedy is to enlarge the classified objects. A generalized elliptic curve over a base is a proper flat family whose geometric fibers are smooth elliptic curves or Néron polygons, with a group law on the smooth locus acting on the whole curve. An $m$-gon is a cycle of $m$ projective lines. Its smooth locus is an extension

$$
1\longrightarrow\mathbf G_m\longrightarrow E^{\mathrm{sm}}
\longrightarrow\mathbf Z/m\mathbf Z\longrightarrow0. \tag{5.1}
$$

The compactifications $X_0(N)$ and $X_1(N)$ classify generalized elliptic curves with stable level, again as stacks before coarse spaces are taken. Their boundary points are the **cusps**. Properness is not an afterthought: it is the theorem that every generic level object has a unique stable limit after the allowed finite base change, with descent when the original object possesses compatible descent data.

### 5.2 Néron polygons and stable level

On a smooth fiber, a cyclic subgroup of rank $N$ is automatically an effective divisor of degree $N$. On a polygon, it could lie entirely in the identity component $\mathbf G_m$ and ignore the other components. Then one could insert or contract unused components without changing the recorded subgroup, destroying separatedness.

Stable level solves this problem by ampleness. A $\Gamma_0(N)$ subgroup

$$
C\subset E^{\mathrm{sm}}
$$

must be cyclic finite locally free of rank $N$, and its divisor must meet every irreducible component of every geometric fiber. A $\Gamma_1(N)$ generator is required to generate such an ample divisor. The condition makes the polygon size part of the level data.

For example, on a Tate degeneration a subgroup can be concentrated in the multiplicative direction, represented by roots of unity, or can project nontrivially to the component group. The two possibilities lead to different cusps and, at prime level, are exchanged by the dual-isogeny involution.

At prime level the two basic subgroups can be seen explicitly. On $E_q=\mathbf G_m/q^{\mathbf Z}$, the classes of the $p$th roots of unity form $\mu_p$. After adjoining $q^{1/p}$, the class of $q^{1/p}$ generates another cyclic subgroup. Quotienting by the first gives

$$
E_q/\mu_p\simeq E_{q^p}, \tag{5.1a}
$$

while quotienting by the second gives

$$
E_q/\langle q^{1/p}\rangle\simeq E_{q^{1/p}}. \tag{5.1b}
$$

These equations are to be read over rings where the displayed roots exist. They show why one boundary map raises a parameter to the $p$th power while the other requires a $p$th root. They also make duality concrete: the dual of the first quotient has kernel in the component direction of $E_{q^p}$.

For composite $N$, a subgroup generated by $\zeta_N^a q^{b/N}$ has multiplicative and component orders that together must produce order $N$. The stable polygon has enough components for the generated divisor to meet them all. Different pairs $(a,b)$ can yield the same cusp after changing the Tate trivialization; the congruence subgroup orbit is exactly the equivalence relation.

### 5.3 Tate parameters and cusp widths

Near a cusp, the Tate curve supplies a punctured universal neighborhood:

$$
E_q=\mathbf G_m/q^{\mathbf Z},\qquad 0<|q|<1. \tag{5.2}
$$

Its $N$-torsion is represented after adjoining the necessary roots by

$$
\zeta_N^a q^{b/N},\qquad (a,b)\in(\mathbf Z/N\mathbf Z)^2. \tag{5.3}
$$

The exponent $a$ records multiplicative torsion, while $b$ records motion in the component direction. This is the local source of the cusp labels.

Let $\Gamma$ be the congruence subgroup defining a connected complex modular curve. The stabilizer of $\infty$ in $\operatorname{SL}_2(\mathbf Z)$ is generated, up to sign, by

$$
T=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

The **width** $w_c$ of the cusp represented by $\gamma\infty$ is the least positive $w$ for which $\gamma T^w\gamma^{-1}$ lies in $\Gamma$ modulo the central sign. A local parameter on the coarse curve is

$$
q_c=e^{2\pi i\tau/w_c}. \tag{5.4}
$$

Equivalently, after rigidifying automorphisms, the completed local ring is a power-series ring in $q_c$. A finite level map has local form

$$
q_c\longmapsto u\,q_{c'}^e,\qquad e=\frac{w_{c'}}{w_c}, \tag{5.5}
$$

for a unit $u$. Thus a map which is étale on the open curve can ramify at a cusp. Cusp width measures precisely that ramification.

For $\Gamma_0(N)$, a cusp represented by $a/c$ with $\gcd(a,c)=1$ has width

$$
w_{a/c}=\frac{N}{\gcd(N,c^2)}. \tag{5.5a}
$$

Indeed, the lower-left entry of $\gamma T^w\gamma^{-1}$ is $-c^2w$, so membership in $\Gamma_0(N)$ is exactly the divisibility $N\mid c^2w$. At $\infty$ one has $c=0$ and width $1$; at $0$ one has $c=1$ and width $N$. This calculation anticipates why the two Tate directions at prime level have ramification indices $1$ and $p$.

### 5.4 The fields of definition of cusps

Analytically, geometric cusps are $\Gamma$-orbits in $\mathbf P^1(\mathbf Q)$. Their rationality is arithmetic rather than merely topological. The Tate description gives an exact procedure: represent the level by a primitive vector or basis in $(\mathbf Z/N\mathbf Z)^2$, let

$$
\operatorname{Gal}(\mathbf Q(\zeta_N)/\mathbf Q)
\simeq(\mathbf Z/N\mathbf Z)^\times
$$

act through its cyclotomic action on the multiplicative coordinate in (5.3), and take the fixed field of the stabilizer of the level orbit. This recipe gives the residue field of the cusp and works uniformly for $\Gamma_1$ and full level, where a single oversimplified formula is unsafe.

For $X_0(N)$ there is a convenient closed form. A cusp may be represented by $a/d$ with $d\mid N$ and $\gcd(a,d)=1$. Put

$$
h_d=\gcd(d,N/d). \tag{5.6}
$$

The numerator is taken modulo the equivalence appropriate to $h_d$, and the corresponding closed cusp has residue field

$$
\mathbf Q(\zeta_{h_d}). \tag{5.7}
$$

The total number of geometric cusps is therefore

$$
c_\infty(N)=\sum_{d\mid N}\varphi\!\left(\gcd(d,N/d)\right). \tag{5.8}
$$

In particular, if $N$ is squarefree then $h_d=1$ for every divisor $d$, so every cusp of $X_0(N)$ is rational over $\mathbf Q$. The cusps $0$ and $\infty$ are rational for every $N$. At nonsquarefree level, not every cusp need be rational; treating all rational boundary fractions as $\mathbf Q$-rational scheme points confuses analytic representatives with residue fields.

For $X_1(N)$, cusp fields are subfields of $\mathbf Q(\zeta_N)$ determined by the stabilizer of the chosen generator data. Some standard cusps descend farther because an automorphism of the polygon compensates for cyclotomic Galois action. The stabilizer recipe, rather than the assertion “all cusps are cyclotomic of full degree,” is the exact statement.

The exact-divisor involutions respect this arithmetic. If a cusp of $X_0(N)$ has denominator type $d\mid N$, then $w_Q$ sends it to denominator type

$$
d'=\frac{Qd}{\gcd(Q,d)^2}. \tag{5.9}
$$

At each prime dividing the exact divisor $Q$, this replaces the exponent of $d$ by its complement in the exponent of $N$; at the other primes it leaves the exponent unchanged. Consequently $\gcd(d,N/d)=\gcd(d',N/d')$, so $w_Q$ preserves the cusp residue-field degree. For $Q=N$ it sends $d$ to $N/d$, and in particular $w_N$ exchanges $0$ and $\infty$.

### 5.5 Maps at the boundary

The maps of Chapter 4 extend over the cusps because quotienting a generalized elliptic curve by a stable finite subgroup again gives a generalized elliptic curve after the canonical contraction. Their moduli meaning remains visible.

At prime level, the cusp $\infty$ can be represented by the Tate curve with subgroup $\mu_p$. Quotienting by $\mu_p$ sends the Tate parameter to $q^p$. The other standard cusp is represented, after adjoining $q^{1/p}$, by a subgroup generated in the component direction; quotienting it sends the parameter in the inverse direction. Consequently $w_p$ exchanges $0$ and $\infty$.

This calculation supplies a useful counterexample to a common shortcut. The two projections $X_0(p)\rightrightarrows X(1)$ both have generic degree $p+1$, but their maps on completed cusp neighborhoods can have different ramification indices. Generic degree does not determine boundary behavior.

## 6. Rational cyclic subgroups and rational isogenies

### 6.1 The exact equivalence away from the characteristic

We now prove the bridge for which the moduli curves were built.

**Theorem 6.1 (subgroup--isogeny equivalence).** Let $K$ be a field, let $N\ge1$ satisfy $\operatorname{char}K\nmid N$, and let $E/K$ be an elliptic curve. The following data are equivalent:

1. a cyclic finite étale subgroup scheme $C\subset E[N]$ of rank $N$ defined over $K$;
2. a $G_K$-stable cyclic subgroup $C(K^s)\subset E[N](K^s)$ of order $N$;
3. a separable cyclic isogeny $\varphi:E\to E'$ of degree $N$ defined over $K$, with source $E$.

**Proof strategy.** Finite étale descent handles the passage between schemes and Galois sets. The quotient construction turns a subgroup scheme into an isogeny. Conversely, the scheme-theoretic kernel of a separable isogeny has the required geometric points.

**Proof.** Since $N$ is invertible, $E[N]$ is finite étale. The equivalence between finite étale schemes over $K$ and finite continuous $G_K$-sets identifies closed subgroup schemes with stable subgroups and proves $1\Longleftrightarrow2$.

Given $C$, the quotient elliptic curve $E/C$ and quotient map

$$
\pi_C:E\longrightarrow E/C
$$

are defined over $K$ because the entire quotient construction descends with $C$. Its degree is the rank of $C$, namely $N$, and it is separable because $N$ is prime to the characteristic. Its geometric kernel is cyclic, proving $1\Longrightarrow3$.

Conversely, if $\varphi$ is a separable cyclic isogeny of degree $N$, its scheme-theoretic kernel is finite étale of rank $N$. It lies in $E[N]$, since the dual identity gives $[N]=\widehat\varphi\varphi$, and it is defined over $K$ because $\varphi$ is. Its geometric points are cyclic by hypothesis. This proves $3\Longrightarrow1$. $\square$

Thus an actual pair $(E,C)/K$ gives a $K$-valued object of the $\Gamma_0(N)$ stack and hence a noncuspidal point of the coarse curve $Y_0(N)(K)$. Conversely, a coarse rational point yields such an isogeny only after the descent issue of Chapter 3 has been resolved.

### 6.2 A subgroup versus a generator

A $\Gamma_1(N)$ structure is stronger. Let $C$ be as in Theorem 6.1 and choose a geometric generator $P$. There is a unique character

$$
\psi_C:G_K\longrightarrow(\mathbf Z/N\mathbf Z)^\times
$$

such that

$$
\sigma P=\psi_C(\sigma)P. \tag{6.1}
$$

The subgroup is defined over $K$ for every such character; a generator is rational exactly when $\psi_C=1$. Therefore

$$
\begin{aligned}
Y_0(N)&:\quad\text{the cyclic direction is rational},\\
Y_1(N)&:\quad\text{a chosen nonzero vector in that direction is rational}.
\end{aligned} \tag{6.2}
$$

For example, a subgroup isomorphic to $\mu_p$ over a characteristic-zero field is defined over $K$, while a generator is rational only when $K$ contains the relevant primitive $p$th root of unity. This gives a rational $p$-isogeny without a rational point of order $p$.

### 6.3 Reducible residual representations

Let $p\ne\operatorname{char}K$. Choosing a basis of $E[p](K^s)$ gives

$$
\overline\rho_{E,p}:G_K\longrightarrow\operatorname{GL}_2(\mathbf F_p). \tag{6.3}
$$

The representation is reducible **over $\mathbf F_p$** when it has a $G_K$-stable $\mathbf F_p$-line. Reducibility only after extending scalars to $\overline{\mathbf F}_p$ is weaker and need not give a subgroup of order $p$ defined over $K$.

**Theorem 6.2 (prime-degree dictionary).** For $p\ne\operatorname{char}K$, the following are equivalent:

1. $\overline\rho_{E,p}$ is reducible over $\mathbf F_p$;
2. $E[p]$ contains a $G_K$-stable line;
3. $E$ has a $K$-rational cyclic isogeny of degree $p$;
4. the $\Gamma_0(p)$ stack has a $K$-object with underlying curve $E$.

**Proof.** Conditions 1 and 2 are the definition of reducibility. A line has $p$ elements and is cyclic, so Theorem 6.1 gives $2\Longleftrightarrow3$. Recording its kernel is exactly the object in 4. $\square$

The theorem does not say that the representation is a direct sum. In a basis beginning with the kernel line it has the form

$$
\overline\rho_{E,p}(\sigma)=
\begin{pmatrix}
\psi(\sigma)&*\\
0&\overline\chi_p(\sigma)\psi(\sigma)^{-1}
\end{pmatrix}, \tag{6.4}
$$

where the determinant is cyclotomic. The upper-right entry can define a nonsplit extension.

### 6.4 Kernel characters and the dual isogeny

Let $\varphi:E\to E'$ be a rational $p$-isogeny and let $\psi$ be the character on $\ker\varphi$. The Weil pairing identifies the quotient direction with the twisted dual of the kernel line. Hence the character on $\ker\widehat\varphi$ is

$$
\overline\chi_p\psi^{-1}. \tag{6.5}
$$

Geometrically, $w_p$ replaces $(E,\ker\varphi)$ by $(E',\ker\widehat\varphi)$. Representation-theoretically, it exchanges the two diagonal characters in (6.4). This is the exact connection between the Atkin--Lehner involution and dual isogeny.

One must not infer that $E[p]$ and $E'[p]$ are isomorphic as extensions. A degree-$p$ isogeny changes the integral $p$-torsion lattice. Their semisimplifications have the same two characters, but the extension classes can differ.

### 6.5 Composite level and cyclicity

When $N$ is composite and prime to the characteristic, a cyclic subgroup of order $N$ is a rank-one direct summand of $(\mathbf Z/N\mathbf Z)^2$. Merely having a stable subgroup of order dividing $N$ is not enough. For example, the subgroup generated by $(2,0)$ in $(\mathbf Z/4\mathbf Z)^2$ has order two and is not a cyclic level-$4$ subgroup.

Primary decomposition gives

$$
C=\bigoplus_{q\mid N} C[q^{v_q(N)}]. \tag{6.6}
$$

The subgroup is cyclic of order $N$ exactly when each primary part is cyclic of full order. Galois stability can be checked on these characteristic primary pieces. This explains both the exact-divisor decomposition used by Atkin--Lehner operators and the need to state cyclicity rather than only rank.

## 7. Low-level curves and explicit coordinates

### 7.1 $X(1)$ and the first rational parametrizations

The coarse curve $X(1)$ is $\mathbf P^1$ with coordinate $j$, and the unique cusp is $j=\infty$. A nonconstant map $X_0(N)\to X(1)$ is therefore an explicit rational function once a coordinate on a genus-zero $X_0(N)$ is chosen. Such a formula does three jobs: it produces families of rational isogenies, locates cusps through poles, and displays ramification above the elliptic values $0$ and $1728$.

It does not produce a universal elliptic curve on the coarse $X_0(N)$. Nor does every rational parameter necessarily yield a nonsingular elliptic curve: the parameter values at poles are cusps. The formula classifies coarse isomorphism data on the open locus.

### 7.2 $X_0(2)$ and $X_0(3)$

Choose a coordinate $t$ on $X_0(2)\simeq\mathbf P^1$ so that

$$
j=\frac{(t+16)^3}{t}. \tag{7.1}
$$

The Atkin--Lehner involution is

$$
w_2(t)=\frac{2^{12}}{t}, \tag{7.2}
$$

and therefore the $j$-invariant of the quotient curve is

$$
j' = j(w_2t)=\frac{(t+256)^3}{t^2}. \tag{7.3}
$$

The two poles $t=0,\infty$ are the two cusps. A rational $t$ away from them gives a coarse rational $2$-isogeny class; because an order-two subgroup has a unique nonzero generator, $X_0(2)$ and the corresponding point-structure problem are especially close.

Similarly choose a coordinate on $X_0(3)$ with

$$
j=\frac{(t+27)(t+3)^3}{t}. \tag{7.4}
$$

Then

$$
w_3(t)=\frac{3^6}{t},\qquad
j'=\frac{(t+27)(t+243)^3}{t^3}. \tag{7.5}
$$

The kernel generator need not be rational. The coordinate parametrizes cyclic subgroups, not necessarily rational $3$-torsion points.

### 7.3 $X_0(5)$ and what a formula proves

A standard coordinate on the genus-zero curve $X_0(5)$ gives

$$
j=\frac{(t^2+10t+5)^3}{t},\qquad
w_5(t)=\frac{5^3}{t}. \tag{7.6}
$$

Consequently the quotient $j$-invariant is obtained by substituting $125/t$. The formula displays infinitely many rational $j$-invariants with a rational cyclic $5$-isogeny. It does not say that the kernel has a rational generator, and it does not identify two parameters that may be related by twisting at an exceptional automorphism point without a descent check.

As a worked use, take any $t\in\mathbf Q^\times$ for which the displayed $j$ is neither $0$ nor $1728$. The generic-automorphism criterion of Section 3.4 produces an elliptic curve over $\mathbf Q$ with a rational cyclic subgroup of order $5$. Applying $w_5$ gives its quotient curve. Thus the coordinate, the descent criterion, and duality together produce the actual isogeny, rather than the coordinate formula doing all three jobs by itself.

### 7.4 Genus zero does not mean trivial arithmetic

The curves $X_0(2)$, $X_0(3)$, and $X_0(5)$ are rational, but their integral geometry at the level prime still detects connected and dual subgroup directions and supersingular collision. For $p=5$ this falls under the rigidified two-component theorem of Section 8.2; at $p=2,3$ stack stabilizers and coarse quotient singularities require separate local analysis, so no identical regular two-component model is being asserted. Their maps to the $j$-line ramify, and their open subsets omit cusps. Genus measures the canonical geometry of the generic fiber; it does not measure the complexity of the moduli problem at bad primes.

Conversely, a high-genus curve can have obvious rational cusps. Positive genus does not remove the boundary. The arithmetic problem is to show that noncuspidal rational points are rare or absent, a task requiring more than the genus calculation alone.

## 8. Integral models away from and at the level

### 8.1 Good primes

Let $\ell\nmid N$. Over $\mathbf Z_\ell$, the $N$-torsion of an elliptic curve is finite étale. On a fine auxiliary cover, the compactified modular curve is smooth and proper over $\mathbf Z_\ell$, and its boundary is a finite étale relative divisor after the harmless cyclotomic base needed to split cusp fields. On the stack the same smooth proper statement holds without auxiliary rigidification.

For a coarse curve one must account for stabilizers. In characteristics not dividing their orders, the quotient is tame and the resulting coarse curve is smooth after the standard construction. In small characteristics, one should either retain the stack or work upstairs on a rigid cover. The safe good-prime assertion is therefore:

> after adding prime-to-$\ell$ rigidifying level, the compactified level-$N$ curve is smooth proper over $\mathbf Z_\ell$; statements invariant under the finite auxiliary group descend once stabilizers have been checked.

This is enough for reduction of rational points and point counting.

### 8.2 The standard integral $X_0(p)$ model

At the prime $p$ dividing the level, $E[p]$ is not étale. The standard compactified $\Gamma_0(p)$ problem over $\mathbf Z_p$ is nevertheless proper and flat when cyclicity is interpreted by finite locally free subgroup schemes and stable generalized elliptic curves.

To state its local geometry without quotient ambiguity, add a fine full level $M\ge3$ with $(M,p)=1$, and assume $p\ge5$. The resulting rigidified model is regular and semistable. Its geometric special fiber has two smooth principal components meeting transversely at the supersingular points. At a crossing, the strict henselian completed local ring is

$$
W(\overline{\mathbf F}_p)[[x,y]]/(xy-p). \tag{8.1}
$$

The quotient has dimension two and maximal ideal generated by the images of $x$ and $y$, so its embedding dimension equals its dimension; hence the total space is regular. Its special fiber is $xy=0$, a normal crossing. Regularity of the total space does not mean smoothness over $\mathbf Z_p$: the special fiber is reducible and singular at its crossings.

Here is the moduli reason for two, rather than an arbitrary number of, principal components. Over an ordinary characteristic-$p$ elliptic curve, a cyclic subgroup scheme of rank $p$ has either connected or étale generic type in the ordinary deformation. Each choice deforms along a one-dimensional smooth branch. At a supersingular curve there is no ordinary direct sum separating the choices; the two deformation conditions meet. A local deformation calculation supplies one parameter for each choice and the relation that their product is the base uniformizer, giving (8.1). This proves both the branch count and the transverse multiplicity one.

The two components are each identified, up to the auxiliary level and Frobenius twist, with the level-$M$ modular curve in characteristic $p$. Therefore their genera and rational points can be studied on a good lower-level curve. This feature is later useful when a section is known to land on one component: the level-$p$ problem has specialized to a prime-to-$p$ problem plus a Frobenius label.

### 8.3 Frobenius and Verschiebung branches

Over the ordinary locus in characteristic $p$, an elliptic curve has a connected subgroup of rank $p$ and an étale subgroup of rank $p$. The connected one is $\ker F$ for relative Frobenius

$$
F:E\longrightarrow E^{(p)}, \tag{8.2}
$$

while the étale direction is described through the kernel of Verschiebung

$$
V:E^{(p)}\longrightarrow E. \tag{8.3}
$$

Thus one component of the special fiber parametrizes $(E,\ker F)$. The other parametrizes the dual, étale branch, after the appropriate Frobenius twist. The Atkin--Lehner involution exchanges them because it exchanges an isogeny with its dual.

At a supersingular point, both $F$ and $V$ are inseparable and the ordinary connected--étale separation disappears. The two components meet there. Equation (8.1) is the deformation-theoretic record of precisely this collision.

It is safer to speak of a Frobenius branch and a Verschiebung branch than to call both subgroups literal subgroups of the same fixed curve without a twist. Relative Frobenius changes the source to $E^{(p)}$, and Verschiebung returns from that twist.

### 8.4 The more delicate $X_1(p)$ model

The $\Gamma_1(p)$ problem asks for a Drinfeld generator, not merely its cyclic subgroup. Over the ordinary special fiber, generators of the étale direction and generators of the connected direction behave very differently. Over the connected direction, several sections can coalesce scheme-theoretically. The forgetful map to $X_0(p)$ is therefore ramified at the level prime and is not a finite étale cover of the two-component model.

The standard compactified $\Gamma_1(p)$ moduli problem is proper and flat, but one must not infer that its naive coarse model over $\mathbf Z_p$ is regular or semistable from the generic fine-moduli statement. After adjoining suitable cyclotomic ramification, normalizing, and resolving, its stable reduction is described by Igusa-type components and their intersections. The exact configuration depends on the level and on whether stack or coarse space is retained.

For the purposes of rational torsion in this book, the justified scope is narrower:

- away from $p$, $X_1(p)$ has smooth proper reduction after ordinary rigidification;
- at $p$, the Drinfeld model is proper and flat;
- specialization of a rational generator is interpreted as a section of a finite locally free subgroup divisor;
- no two-component or unramified semistability claim for $X_1(p)$ is made.

This is enough to distinguish rational torsion from a rational subgroup without importing the full stable-reduction theory of $X_1(p)$.

### 8.5 Exact regularity and semistability scope

The two-component theorem is asserted here only for squarefree depth-one $\Gamma_0(p)$ level, $p\ge5$, after prime-to-$p$ auxiliary rigidification. Removing the auxiliary level passes to a quotient by a finite group. On the stack the quotient retains the correct semistable local structure; on the coarse surface, fixed points may create quotient singularities and a minimal regular model can require resolution.

The theorem is not asserted unchanged for $p=2,3$, for $p^2\mid N$, for $\Gamma_1(p^r)$, or for arbitrary coarse integral models. Properness and flatness survive much more generally than regularity and semistability. Normality is also weaker than regularity: normalizing a coarse model need not resolve its quotient singularities.

These qualifications are not technical debris. Reduction arguments use different properties for different steps:

| Needed conclusion | Sufficient geometric input |
|---|---|
| a $K$-point extends uniquely over a DVR | properness and separatedness |
| a reduction point lies on a well-defined special fiber | a chosen proper integral model |
| branches meet transversely | semistable local equation such as $xy-p$ |
| intersection theory on the surface | regularity, or an explicit resolution |
| smooth specialization and uncomplicated point counts | smooth proper reduction |

Using the weakest sufficient hypothesis keeps the later arguments correct at both good and level primes.

## 9. Specializing rational points

### 9.1 Properness turns points into sections

Let $R$ be a DVR with fraction field $K$, and let $\mathscr X/R$ be a proper separated model of a modular curve. The valuative criterion gives a bijection

$$
\mathscr X(R)\xrightarrow{\sim}X(K). \tag{9.1}
$$

Existence uses properness; uniqueness uses separatedness. Thus every rational point has a canonical specialization

$$
\operatorname{red}:X(K)\longrightarrow\mathscr X_k(k). \tag{9.2}
$$

This statement applies even when the special fiber is reducible or singular. Smoothness is not needed to extend the section. If $R$ is replaced by the ring of integers of an unramified or ramified extension, the section base-changes compatibly.

For a nonproper open curve $Y$, the same assertion is false. A point of $Y(K)$ may approach a missing cusp. Compactification is exactly what records that limit. Therefore every reduction argument about rational isogenies belongs naturally on $X_0(N)$, even when its generic point lies in $Y_0(N)$.

### 9.2 Interior and cuspidal reduction

Assume first that the residue characteristic $\ell$ does not divide $N$, and work on a fine smooth proper model or its justified coarse quotient. Let $x$ be represented by $(E,C)/K$.

If $E$ has good reduction, its smooth proper model carries a finite étale closure of $C$, so the section reduces to a smooth elliptic curve with cyclic subgroup. Hence $\operatorname{red}(x)$ is noncuspidal.

If $E$ has multiplicative reduction, its stable limit is a Néron polygon and the level closure lies in the smooth locus after the stable contraction. Hence $x$ reduces to a cusp. More invariantly,

$$
v(j(E))<0\quad\Longrightarrow\quad
\operatorname{red}(x)\text{ is cuspidal} \tag{9.3}
$$

after passing to the stable model. Conversely, a section reducing to the boundary has degenerating generalized elliptic source and therefore nonintegral $j$ after the corresponding stable extension.

Additive potentially good reduction is a warning. Its $j$-invariant is integral and, after finite extension, its stable fiber is a smooth elliptic curve rather than a polygon. It should not be called cuspidal merely because a chosen Weierstrass equation has singular special fiber. The modular compactification uses the stable generalized elliptic curve, not an arbitrary nonminimal cubic.

The level itself can affect the field over which the stable point is visible, but not the interior-versus-boundary distinction once the stable object exists. A coarse point again requires care: the reduction of its coarse section exists, while interpreting it as a level object may require passing to the stack or a rigid cover.

### 9.3 Specialization to components at the level prime

Now let the residue characteristic equal the prime level $p$, under the semistable scope of Section 8.2. A section of the rigidified $X_0(p)$ model can specialize to:

- a smooth point on the Frobenius component;
- a smooth point on the Verschiebung component;
- a supersingular crossing;
- a cusp on one of the components.

On the ordinary locus, the closure $\mathcal C$ of the generic kernel decides the branch. If its special fiber is connected, it is the Frobenius-type subgroup and the section lies on the Frobenius component. If it is étale, the dual description places it on the Verschiebung component. At a supersingular curve, the two branches meet and the coarse connected--étale label no longer separates them.

The local equation $xy=p$ makes the section behavior explicit. Let $e_R=v_R(p)$ for the normalized valuation of $R$. If a section through the completed neighborhood has parameters $x_0,y_0\in R$ satisfying $x_0y_0=p$, then

$$
v_R(x_0)+v_R(y_0)=e_R. \tag{9.4}
$$

Over an unramified DVR, $e_R=1$, so one valuation is zero and the other is one; the section meets exactly one branch away from the crossing and cannot pass through the node. Over a ramified DVR, $e_R>1$ and both valuations can be positive, so a section can specialize to the crossing. Equivalently, if the valuation is extended with the normalization $v(p)=1$, the positive values can be fractional. This is why a branch assertion must specify the valuation normalization, the valuation ring, and the base change.

Atkin--Lehner exchanges the two smooth branches and the two ordinary subgroup types. It fixes or permutes supersingular crossings according to duality of the corresponding supersingular isogeny.

### 9.4 Auxiliary-prime point counts

Let $K$ be a number field and $v$ a finite place of residue field $k_v$ with cardinality $q$. Suppose $v\nmid N$ and $X_0(N)$ has good reduction at $v$ in the precise sense of Section 8.1. Every $K$-rational point reduces to a $k_v$-point:

$$
X_0(N)(K)\longrightarrow X_0(N)(k_v). \tag{9.5}
$$

This simple map yields several useful constraints.

First, if a specified union of components, residue classes, or noncuspidal locus contains no $k_v$-point, then no global point can reduce there. Second, reductions at several primes can be combined: a global point must choose compatible residue classes at every chosen place. Third, a morphism such as $j:X_0(N)\to\mathbf P^1$ lets one count points above a prescribed reduction of $j(E)$ rather than count the entire curve.

The reduction map is not generally injective. Distinct $K$-points may lie in the same residue disk. Therefore

$$
\#X_0(N)(K)\le \#X_0(N)(k_v)
$$

does not follow from properness alone. Injectivity requires extra information, often obtained later from a Jacobian or from a formal immersion. Point counting in this book supplies local exclusions and residue classes, not a global cardinality bound by itself.

For a smooth projective genus-$g$ special fiber,

$$
\bigl|\#X_0(N)(\mathbf F_q)-(q+1)\bigr|\le 2g\sqrt q. \tag{9.6}
$$

This estimates the size of the target but does not identify which points are cuspidal or which lie above a chosen $j$-value. The moduli interpretation refines the raw estimate.

### 9.5 Local tests for a rational $p$-isogeny

Let $E/K$ have a $K$-rational $p$-isogeny, with $p$ distinct from the residue characteristic $\ell$ at a good place $v$. Reduction preserves the kernel line. Arithmetic Frobenius on $E[p]$ must therefore have an eigenvalue in $\mathbf F_p$. If

$$
X^2-a_vX+q_v \tag{9.7}
$$

is the Frobenius polynomial, a necessary condition is that it have a root in $\mathbf F_p$. For odd $p$, this is equivalent to

$$
a_v^2-4q_v\text{ is a square in }\mathbf F_p. \tag{9.8}
$$

Here zero counts as a square. In characteristic two the discriminant-square reformulation is invalid, so the root condition in (9.7) must be tested directly. For every $p$, one good place at which (9.7) is irreducible modulo $p$ rules out a rational $p$-isogeny.

This criterion is one-way. If the polynomial splits at a single place, the two Frobenius eigenlines need not be stable under the full global Galois group. Even splitting at many sampled places is evidence, not by itself a proof of global reducibility.

As a concrete exclusion, consider

$$
E:y^2=x^3-x
$$

over $\mathbf Q$. At $5$ it has good reduction and $\#E(\mathbf F_5)=8$, so $a_5=-2$. For $p=3$, the Frobenius polynomial is

$$
X^2+2X+5\equiv X^2-X+2\pmod3. \tag{9.8a}
$$

Its discriminant is $1-8\equiv2\pmod3$, a nonsquare. Hence $E[3]$ has no globally stable $\mathbf F_3$-line and $E$ admits no rational $3$-isogeny. One good reduction computation has excluded a global modular point attached to this particular elliptic curve.

For contrast, the same curve has the rational point $(0,0)$ of order two. Its order-two line survives at every odd good prime, and every Frobenius polynomial splits modulo $2$. The distinction is visible without computing an isogeny formula.

Rational torsion gives a stronger congruence. If $P\in E(K)$ has exact order $p$ and $v\nmid p$ is a good place, specialization is injective on $p$-torsion, so

$$
p\mid\#\widetilde E(k_v). \tag{9.9}
$$

A rational subgroup without a rational generator need not satisfy (9.9): Frobenius may act on the line by a nontrivial scalar. The correct $X_0$ test is the root condition in (9.7), equivalently (9.8) for odd $p$, while (9.9) is an $X_1$ test. This local distinction mirrors the global moduli distinction exactly.

At a multiplicative place $v\nmid p$, a point on $X_0(p)$ reduces to a cusp. The Tate description can refine which cusp by comparing the stable line with the multiplicative line $\mu_p$ and the component direction. Thus the same global modular point carries both good-prime Frobenius constraints and bad-prime cusp data.

## 10. Genus and the geometry of scarcity

### 10.1 The canonical divisor calculation

The complex curve $X_\Gamma$ attached to a finite-index subgroup of $\operatorname{PSL}_2(\mathbf Z)$ is a branched cover of $X(1)\simeq\mathbf P^1$. Ramification occurs above the elliptic points of orders $2$ and $3$ and above the cusp. This makes Riemann--Hurwitz an efficient genus calculation.

Let

$$
\mu=[\operatorname{PSL}_2(\mathbf Z):\overline\Gamma],
$$

let $e_2$ and $e_3$ be the numbers of elliptic orbits of orders $2$ and $3$, and let $c$ be the number of cusps. The canonical divisor degree is

$$
2g(X_\Gamma)-2
=\frac{\mu}{6}-\frac{e_2}{2}-\frac{2e_3}{3}-c. \tag{10.1}
$$

Equivalently,

$$
g(X_\Gamma)
=1+\frac{\mu}{12}-\frac{e_2}{4}-\frac{e_3}{3}-\frac c2. \tag{10.2}
$$

**Proof strategy.** Apply Riemann--Hurwitz to $X_\Gamma\to X(1)$. Away from the three special orbits the cover is unramified. Above an order-$m$ elliptic point, a point with trivial stabilizer has ramification $m$, while an elliptic point of $X_\Gamma$ cancels that ramification. At the cusp, the sum of cusp widths is $\mu$. Substituting these contributions and using $g(X(1))=0$ gives (10.1).

To make the accounting explicit, the total ramification above the order-two orbit is

$$
\frac{\mu-e_2}{2}, \tag{10.2a}
$$

because the $e_2$ unramified elliptic points use one sheet each and the remaining sheets occur in pairs. Above the order-three orbit it is

$$
\frac{2(\mu-e_3)}{3}. \tag{10.2b}
$$

If the cusp widths are $w_1,\ldots,w_c$, then $\sum_iw_i=\mu$ and the cusp ramification is

$$
\sum_i(w_i-1)=\mu-c. \tag{10.2c}
$$

Riemann--Hurwitz gives

$$
2g-2=-2\mu
+\frac{\mu-e_2}{2}
+\frac{2(\mu-e_3)}{3}
+(\mu-c),
$$

which simplifies to (10.1). Thus every term in the genus formula has a geometric source: area/index, elliptic stabilizers, or boundary widths.

The calculation explains the asymptotic shape. The positive term grows with the index; elliptic corrections are bounded in many level families, while cusp corrections grow more slowly than the index. High level therefore forces the canonical divisor to become positive and eventually large.

### 10.2 The genus formula for $X_0(N)$

For $\Gamma_0(N)$,

$$
\mu_0(N)=N\prod_{q\mid N}\left(1+\frac1q\right), \tag{10.3}
$$

and the cusp number is (5.8). Hence

$$
g(X_0(N))
=1+\frac{\mu_0(N)}{12}
-\frac{e_2(N)}4-\frac{e_3(N)}3-\frac{c_\infty(N)}2. \tag{10.4}
$$

The elliptic counts can be described as congruence counts:

$$
e_2(N)=\#\{x\bmod N:x^2+1\equiv0\bmod N\}, \tag{10.5}
$$

$$
e_3(N)=\#\{x\bmod N:x^2+x+1\equiv0\bmod N\}, \tag{10.6}
$$

with the standard small-prime conventions built into the congruences. These formulas make clear why the elliptic correction depends only on splitting behavior of $-1$ and $-3$ at primes dividing the level.

The cusp term is not negligible at small level, but for squarefree $N$ it is simply $2^{\omega(N)}$. Meanwhile $\mu_0(N)$ is of order $N$ times a mild Euler factor. Thus genus grows broadly linearly with level along prime levels and faster than the number of obvious boundary points.

### 10.3 Prime levels

For a prime $p>3$,

$$
\mu_0(p)=p+1,\qquad c_\infty(p)=2, \tag{10.7}
$$

and

$$
e_2(p)=1+\left(\frac{-1}{p}\right),\qquad
e_3(p)=1+\left(\frac{-3}{p}\right). \tag{10.8}
$$

Therefore

$$
g(X_0(p))
=\frac{p+1}{12}-\frac14\left(1+\left(\frac{-1}{p}\right)\right)
-\frac13\left(1+\left(\frac{-3}{p}\right)\right). \tag{10.9}
$$

The expression is an integer because the residue class of $p$ modulo $12$ coordinates the two Legendre symbols. It gives genus zero for

$$
p=2,3,5,7,13,
$$

and genus one for

$$
p=11,17,19.
$$

Thereafter positive genus is the rule and grows with $p$. These examples explain the transition from rational parametrizations to genuinely global curve arithmetic.

For $X_1(N)$, the same canonical formula (10.2) applies with the index, elliptic stabilizers, and cusp orbits of $\Gamma_1(N)$. For $N\ge5$, its image in $\operatorname{PSL}_2(\mathbf Z)$ is torsion-free, so the elliptic corrections vanish. The growth of the index is quadratic in $N$ up to Euler factors, reflecting how much stronger a chosen generator is than an unoriented cyclic subgroup.

### 10.4 What genus does and does not prove

Genus zero often permits a rational parameter once a rational cusp is chosen. Genus one replaces parametrization by the arithmetic of an elliptic curve. Genus at least two signals that the canonical bundle is positive and that rational points should be rigid rather than form a one-parameter family.

But genus alone does not classify rational points. A high-genus curve can have many explicitly known cusps, and a canonical-divisor calculation does not exclude isolated noncuspidal points. General finiteness theorems could prove finiteness over number fields, but the final prime-isogeny classification sought later requires an effective and structural argument. It will use the modular Jacobian, reduction, and special quotients rather than appeal to a general finiteness theorem as its decisive step.

This division of labor is important. The present chapter explains why scarcity is geometrically plausible and supplies exact genus data. It does not claim the list of possible prime degrees. That classification belongs after the arithmetic machinery of the next volumes.

## 11. From a Frey-type curve to a modular point

### 11.1 The reducibility branch

Let $K$ be a number field and let $p\ge5$ be prime. Consider a Frey-type elliptic curve

$$
E_{A,B}:y^2=x(x-A)(x+B),\qquad A+B=C, \tag{11.1}
$$

with nonzero discriminant. In the exponentiated situation one has

$$
A=a^p,\qquad B=b^p,\qquad C=c^p. \tag{11.2}
$$

The earlier local theory determines its reduction and the residual representation

$$
\overline\rho_{E,p}:G_K\longrightarrow\operatorname{GL}_2(\mathbf F_p). \tag{11.3}
$$

Suppose this representation is reducible over $\mathbf F_p$. Choose its stable line $L$. Because $\operatorname{char}K=0$, $E[p]$ is finite étale and $L$ descends to a cyclic subgroup scheme

$$
C_L\subset E[p]
$$

of rank $p$. Quotienting gives an isogeny

$$
\varphi_L:E\longrightarrow E/C_L \tag{11.4}
$$

defined over $K$. The pair $(E,C_L)$ is an actual $K$-object, so it determines a noncuspidal point

$$
x_L\in Y_0(p)(K)\subset X_0(p)(K). \tag{11.5}
$$

There is no coarse descent obstruction here: the pair was constructed before the coarse point. This is the most direct direction of the geometric dictionary.

The line need not have a rational generator, so $x_L$ need not lift to $Y_1(p)(K)$. Confusing these curves would impose a false rational-torsion condition on the Frey curve.

### 11.2 The resulting point and its reduction data

At a finite place $v\nmid p$ of good reduction for $E$, the point $x_L$ reduces to a noncuspidal point of $X_0(p)(k_v)$, and Frobenius preserves the reduced line. Thus (9.8) holds:

$$
a_v(E)^2-4q_v\text{ is a square modulo }p. \tag{11.6}
$$

At a multiplicative place $v\nmid p$, the stable elliptic curve degenerates to a polygon, so $x_L$ reduces to a cusp. After the unramified extension that splits the multiplicative reduction, the Tate extension

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z\longrightarrow0 \tag{11.7}
$$

describes whether the stable line approaches the multiplicative or component direction, possibly after the splitting extension. This determines the cusp orbit and how $w_p$ exchanges it with the dual direction.

For the exponentiated curve, an odd place dividing exactly one of $a,b,c$ is multiplicative, with minimal discriminant exponent divisible by $p$. The residual inertia can therefore become trivial even though the elliptic curve has multiplicative reduction. The modular point still reduces to a cusp: cuspidal reduction records degeneration of the elliptic curve, whereas residual unramifiedness records the reduction of the inertia matrix modulo $p$. The two statements concern different objects and are perfectly compatible.

For instance, if $v(a)=m>0$ while $b$ and $c$ are units at an odd place, then the Frey-type discriminant calculation gives

$$
v(\Delta_{\min})=2pm. \tag{11.6a}
$$

The Tate inertia matrix on $E[p]$ has off-diagonal entry proportional to this exponent, so it vanishes modulo $p$. Yet $v(j)<0$, and the stable elliptic curve is still a polygon. Thus the representation is unramified at $v$ while the modular point is cuspidal. This worked comparison prevents “unramified residual representation” from being mistaken for “good reduction of the elliptic curve.”

At a place above $p$, the point specializes on the proper integral $X_0(p)$ model. If the underlying stable fiber is a smooth ordinary elliptic curve and the kernel closure is connected or étale, it selects the Frobenius or Verschiebung component. A smooth supersingular specialization can land at their intersection only when the ramification of the section permits it; over an unramified DVR the local equation of Section 9.3 prevents a section from passing through that node. Multiplicative reduction instead gives a cusp on one of the components. No prime-to-$p$ point-set argument is valid there.

These data can be displayed as a single chain:

$$
\begin{array}{ccccc}
\overline\rho_{E,p}\text{ reducible}
&\Longrightarrow&C_L\subset E[p]
&\Longrightarrow&x_L\in Y_0(p)(K)\\
&&&&\downarrow\\
&&&&
\begin{cases}
\text{noncuspidal modular point at good }v\nmid p,\\
\text{cusp at multiplicative }v\nmid p,\\
\text{level-model branch, crossing, or cusp at }v\mid p.
\end{cases}
\end{array} \tag{11.8}
$$

### 11.3 Choosing a base cusp

The curve $X_0(N)$ has the rational cusp $\infty$, represented by the multiplicative subgroup in the standard Tate degeneration. It supplies a basepoint defined over $\mathbf Q$ and hence over every extension field. Choosing it turns a point into a degree-zero divisor:

$$
P\longmapsto (P)-(\infty). \tag{11.9}
$$

For squarefree $N$, all $X_0(N)$ cusps are rational, but $\infty$ remains the canonical choice because it is compatible with the standard Tate parameter. At nonsquarefree level other cusps may be defined only over cyclotomic fields; a sum of their Galois orbit is rational but has higher degree.

On $X_1(N)$, the rationality field of a chosen cusp must be checked from its stabilizer. If no convenient $K$-rational cusp is available, one can choose a $K$-rational divisor of positive degree and obtain a Picard map after accounting for that degree. For the prime-isogeny problem, $X_0(p)$ and its rational cusp avoid this complication.

### 11.4 The Abel--Jacobi doorway

Let

$$
J_0(N)=\operatorname{Pic}^0(X_0(N))
$$

be the Jacobian. The rational cusp defines the Abel--Jacobi map

$$
\iota_\infty:X_0(N)\longrightarrow J_0(N),\qquad
P\longmapsto[(P)-(\infty)]. \tag{11.10}
$$

This map is defined over $\mathbf Q$. If the genus is positive, it embeds the curve over an algebraic closure; for genus zero the Jacobian is zero and it carries no information.

Proper integral models let both $P$ and $\infty$ specialize. Where the Jacobian has a suitable integral model, the divisor class specializes as well. This is the doorway to comparing rational modular points through reduction and finite subgroups of the Jacobian.

We stop at the doorway. The structure of $J_0(N)$, its cuspidal subgroup, its quotients, and the arithmetic of its reduction belong to the next volume. The special operator ideal that eventually controls rational points belongs after that. Defining (11.10) here makes the handoff exact without importing their conclusions.

## 12. The geometric dictionary

### 12.1 From residual reducibility to geometry

We can now state the complete geometric output in a reusable form.

**Theorem 12.1 (geometric reducibility dictionary).** Let $K$ be a number field, $E/K$ an elliptic curve, and $p$ a prime. Then the following are equivalent:

1. $\overline\rho_{E,p}$ is reducible over $\mathbf F_p$;
2. $E[p](K^s)$ contains a $G_K$-stable line;
3. $E$ contains a cyclic finite étale subgroup scheme $C$ of rank $p$ defined over $K$;
4. there is a separable degree-$p$ isogeny $E\to E/C$ defined over $K$;
5. there is a $K$-object of the $\Gamma_0(p)$ moduli stack with underlying elliptic curve $E$.

Any of these data produces a noncuspidal point $x\in X_0(p)(K)$. Conversely, a noncuspidal coarse point produces such data if and only if its moduli gerbe is neutral; this holds in particular if the point lifts to the stack over $K$, if a representative is explicitly given, or, in characteristic different from $2,3$, if its $j$-value is not $0$ or $1728$.

If $C$ is generated geometrically by $P$, the point lifts to a $K$-object of $Y_1(p)$ exactly when the kernel character is trivial, equivalently $P\in E(K)$. The dual isogeny corresponds to $w_p(x)$, and its kernel character is $\overline\chi_p\psi^{-1}$ when the original kernel character is $\psi$.

At a finite place $v\nmid p$, the reduction data are:

$$
\begin{array}{c|c|c}
\text{reduction of }E&\text{reduction of }x&\text{constraint}\\ \hline
\text{good}&\text{noncuspidal}&
X^2-a_vX+q_v\text{ has a root in }\mathbf F_p\\
\text{multiplicative}&\text{cuspidal}&
\text{Tate line determines the cusp orbit}\\
\text{additive potentially good}&
\text{interior after stable extension}&
\text{no automatic global invariant line}.
\end{array} \tag{12.1}
$$

At $v\mid p$, a proper finite-flat level model replaces point-set torsion. Under the squarefree rigidified $X_0(p)$ hypotheses, a smooth ordinary kernel closure selects the Frobenius or Verschiebung component, smooth supersingular reduction lies at their intersection when the ramification of the section permits it, and multiplicative reduction gives a cusp on one of the components.

### 12.2 A hypothesis ledger

The logical dependencies of the dictionary are compact enough to audit.

| Statement | Exact hypothesis or qualification |
|---|---|
| $E[N](K^s)\simeq(\mathbf Z/N)^2$ | $\operatorname{char}K\nmid N$ |
| stable geometric subgroup $\Leftrightarrow$ subgroup scheme | finite étale torsion, hence $\operatorname{char}K\nmid N$ |
| stable line $\Leftrightarrow$ rational $p$-isogeny | $p\ne\operatorname{char}K$ and reducibility over $\mathbf F_p$ |
| $X_0$ versus $X_1$ | stable subgroup versus fixed generator |
| coarse $K$-point gives a $K$-object | only when its descent gerbe is neutral |
| all $X_0(N)$ cusps rational | true for squarefree $N$, false in general |
| good reduction implies interior specialization | prime-to-level stable subgroup on a good elliptic model |
| multiplicative reduction implies a cusp | on the stable generalized-elliptic compactification |
| two-component fiber at $p$ | depth-one $\Gamma_0(p)$, $p\ge5$, after prime-to-$p$ rigidification |
| same claim for $X_1(p)$ | not asserted; the integral geometry is more ramified |
| reduction map is injective | not from properness alone |
| high genus classifies rational points | false; it explains scarcity but does not prove the prime-degree list |

This ledger is as important as the equivalences. Every attractive but false shortcut in the subject results from deleting one of its right-hand entries.

### 12.3 Conclusion

A rational cyclic isogeny is a piece of Galois-stable geometry. Away from the characteristic, its kernel is at once a finite étale subgroup scheme, a cyclic subgroup of geometric torsion, and an invariant line in a two-dimensional residual representation. Remembering only the line produces $\Gamma_0$ level; remembering a vector produces $\Gamma_1$ level. The difference is the kernel character, not a change of terminology.

Modular curves make this correspondence vary. Their stack records families and automorphisms, while their coarse curve provides the proper one-dimensional space on which rational points can be studied. The distinction prevents a field of moduli from being mistaken for a field of definition. In the direction needed for a Frey curve, the ambiguity disappears because the elliptic curve and stable line are already defined before the modular point is formed.

Compactification preserves the arithmetic when the elliptic curve degenerates. Néron polygons, ample level divisors, and Tate parameters turn multiplicative reduction into a cusp with a computable width and rationality field. Properness turns every rational point into a section over a DVR. Away from the level, good reduction yields ordinary point-counting and Frobenius tests. At the level prime, finite-flat subgroup schemes replace geometric point sets, and the semistable $X_0(p)$ fiber separates Frobenius from Verschiebung until they meet at supersingular points.

The canonical-divisor calculation explains why these curves change character as the level grows: rational parametrizations at the smallest levels give way to positive genus and geometric rigidity. Yet geometry alone does not provide the final list of prime isogeny degrees. The rational cusp $\infty$ now supplies the Abel--Jacobi map

$$
X_0(p)\longrightarrow J_0(p),\qquad P\longmapsto[(P)-(\infty)],
$$

and every rational reducibility point comes equipped with the reduction data needed to use it. The next stage is arithmetic on that Jacobian. What has been completed here is the exact passage into that stage: residual reducibility has become a rational modular-curve point, duality has become an involution, local behavior has become specialization data, and every hypothesis governing those translations remains visible.
