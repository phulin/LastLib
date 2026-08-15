# Modular Curves $X_0(N)$ and $X_1(N)$

## Contents

1. [The classification problem behind a rational isogeny](#1-the-classification-problem-behind-a-rational-isogeny)
   - [From torsion linear algebra to a curve](#11-from-torsion-linear-algebra-to-a-curve)
   - [Standing hypotheses and conventions](#12-standing-hypotheses-and-conventions)
   - [Four notions that must remain distinct](#13-four-notions-that-must-remain-distinct)
   - [The logical route through the book](#14-the-logical-route-through-the-book)
2. [The three level problems](#2-the-three-level-problems)
   - [Why level is a subgroup-scheme condition](#21-why-level-is-a-subgroup-scheme-condition)
   - [The problems $Y_0(N)$ and $Y_1(N)$](#22-the-problems-y_0n-and-y_1n)
   - [Full level and the Weil-pairing component](#23-full-level-and-the-weil-pairing-component)
   - [Exact characteristic hypotheses](#24-exact-characteristic-hypotheses)
   - [Worked comparisons and counterexamples](#25-worked-comparisons-and-counterexamples)
   - [Level structures over a fixed elliptic curve](#26-level-structures-over-a-fixed-elliptic-curve)
   - [Galois characters carried by level](#27-galois-characters-carried-by-level)
3. [Fine spaces, coarse curves, and descent](#3-fine-spaces-coarse-curves-and-descent)
   - [Why automorphisms obstruct a universal curve](#31-why-automorphisms-obstruct-a-universal-curve)
   - [The fine ranges](#32-the-fine-ranges)
   - [What a coarse rational point actually says](#33-what-a-coarse-rational-point-actually-says)
   - [Neutrality criteria and the exceptional automorphism locus](#34-neutrality-criteria-and-the-exceptional-automorphism-locus)
   - [Field of moduli is not automatically field of definition](#35-field-of-moduli-is-not-automatically-field-of-definition)
   - [Construction of the stacks and coarse curves](#36-construction-of-the-stacks-and-coarse-curves)
   - [Twisting and effective descent in concrete terms](#37-twisting-and-effective-descent-in-concrete-terms)
4. [The open curves and their natural maps](#4-the-open-curves-and-their-natural-maps)
   - [Forgetting structure](#41-forgetting-structure)
   - [Degeneracy maps](#42-degeneracy-maps)
   - [Atkin--Lehner involutions](#43-atkin--lehner-involutions)
   - [Duality as geometry](#44-duality-as-geometry)
   - [Degrees and ramification of the natural maps](#45-degrees-and-ramification-of-the-natural-maps)
   - [The analytic double-coset picture](#46-the-analytic-double-coset-picture)
5. [Compactification and cusps](#5-compactification-and-cusps)
   - [Why smooth elliptic curves are not enough](#51-why-smooth-elliptic-curves-are-not-enough)
   - [Néron polygons and stable level](#52-néron-polygons-and-stable-level)
   - [Tate parameters and cusp widths](#53-tate-parameters-and-cusp-widths)
   - [The fields of definition of cusps](#54-the-fields-of-definition-of-cusps)
   - [Maps at the boundary](#55-maps-at-the-boundary)
   - [The boundary divisor and the completed cusp package](#56-the-boundary-divisor-and-the-completed-cusp-package)
   - [Counting and descending $X_0(N)$ cusps](#57-counting-and-descending-x_0n-cusps)
6. [Rational cyclic subgroups and rational isogenies](#6-rational-cyclic-subgroups-and-rational-isogenies)
   - [The exact equivalence away from the characteristic](#61-the-exact-equivalence-away-from-the-characteristic)
   - [A subgroup versus a generator](#62-a-subgroup-versus-a-generator)
   - [Reducible residual representations](#63-reducible-residual-representations)
   - [Kernel characters and the dual isogeny](#64-kernel-characters-and-the-dual-isogeny)
   - [Composite level and cyclicity](#65-composite-level-and-cyclicity)
   - [Fibers of the $j$-map and fixed-source rationality](#66-fibers-of-the-j-map-and-fixed-source-rationality)
   - [The exact rational-point statement](#67-the-exact-rational-point-statement)
   - [Writing quotient isogenies on Weierstrass equations](#68-writing-quotient-isogenies-on-weierstrass-equations)
7. [Low-level curves and explicit coordinates](#7-low-level-curves-and-explicit-coordinates)
   - [$X(1)$ and the first rational parametrizations](#71-x1-and-the-first-rational-parametrizations)
   - [$X_0(2)$ and $X_0(3)$](#72-x_02-and-x_03)
   - [$X_0(5)$ and what a formula proves](#73-x_05-and-what-a-formula-proves)
   - [Genus zero does not mean trivial arithmetic](#74-genus-zero-does-not-mean-trivial-arithmetic)
   - [Checking the parametrizations and their cusps](#75-checking-the-parametrizations-and-their-cusps)
   - [An explicit rational $2$-isogeny family](#76-an-explicit-rational-2-isogeny-family)
8. [Integral models away from and at the level](#8-integral-models-away-from-and-at-the-level)
   - [Good primes](#81-good-primes)
   - [The standard integral $X_0(p)$ model](#82-the-standard-integral-x_0p-model)
   - [Frobenius and Verschiebung branches](#83-frobenius-and-verschiebung-branches)
   - [The more delicate $X_1(p)$ model](#84-the-more-delicate-x_1p-model)
   - [Exact regularity and semistability scope](#85-exact-regularity-and-semistability-scope)
   - [Degeneracy maps and cusps on the special fiber](#86-degeneracy-maps-and-cusps-on-the-special-fiber)
   - [Why the supersingular equation is $xy=p$](#87-why-the-supersingular-equation-is-xyp)
9. [Specializing rational points](#9-specializing-rational-points)
   - [Properness turns points into sections](#91-properness-turns-points-into-sections)
   - [Interior and cuspidal reduction](#92-interior-and-cuspidal-reduction)
   - [Specialization to components at the level prime](#93-specialization-to-components-at-the-level-prime)
   - [Auxiliary-prime point counts](#94-auxiliary-prime-point-counts)
   - [Local tests for a rational $p$-isogeny](#95-local-tests-for-a-rational-p-isogeny)
   - [Combining several places without overclaiming](#96-combining-several-places-without-overclaiming)
   - [Specialization of the kernel character](#97-specialization-of-the-kernel-character)
10. [Genus and the geometry of scarcity](#10-genus-and-the-geometry-of-scarcity)
    - [The canonical divisor calculation](#101-the-canonical-divisor-calculation)
    - [The genus formula for $X_0(N)$](#102-the-genus-formula-for-x_0n)
    - [Prime levels](#103-prime-levels)
    - [What genus does and does not prove](#104-what-genus-does-and-does-not-prove)
    - [Checked low-level genus data](#105-checked-low-level-genus-data)
11. [From a Frey-type curve to a modular point](#11-from-a-frey-type-curve-to-a-modular-point)
    - [The reducibility branch](#111-the-reducibility-branch)
    - [The resulting point and its reduction data](#112-the-resulting-point-and-its-reduction-data)
    - [Choosing a base cusp](#113-choosing-a-base-cusp)
    - [The Abel--Jacobi doorway](#114-the-abel--jacobi-doorway)
    - [The exact handoff to modular Jacobians](#115-the-exact-handoff-to-modular-jacobians)
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

### 1.4 The logical route through the book

The construction has four layers, and their order matters. We first define the level problems on smooth elliptic curves. We then compactify them by generalized elliptic curves with ample Drinfeld level. After that we pass from the moduli stacks to coarse projective curves. Only at the last stage do we interpret rational points and reduce them at finite places. Reversing this order creates familiar errors: treating a coarse point as a universal family, treating a geometric torsion point as a finite flat subgroup, or trying to specialize a point on a nonproper curve.

The direct geometric foundations are already available. Generalized elliptic curves, Néron polygons, Drinfeld generators, contraction, quotient isogenies, and Tate cusp charts have been established. Proper compactified modular stacks and their coarse curves, including the distinction between universal objects on stacks and invariant maps on coarse curves, have also been constructed. At a prime level, the regular rigidified integral model and its Frobenius--Verschiebung special fiber are known. Finally, the Hodge line and the $q$-expansion theory provide a reliable way to compare cusp widths, discriminants, and finite maps, although modular-form arguments will be used here only when they clarify the geometry of the curves themselves.

What is new in this volume is the synthesis needed for rational isogenies. In particular, we shall prove rather than merely quote:

- the equivalence among a stable cyclic subgroup, a quotient isogeny, and a reducible prime torsion representation;
- the distinction between an unoriented subgroup and a rational generator;
- the effect of duality on the two kernel characters;
- the classification and arithmetic of cusps needed for $X_0(N)$ and $X_1(N)$;
- the degree, ramification, and genus calculations used to recognize the small curves;
- the exact sense in which a rational point of the stack, a rational point of the coarse curve, and a rational isogeny agree or fail to agree;
- the specialization constraints at good primes, multiplicative primes, and the level prime.

The last item in the list is not a classification of all rational points. The present book prepares the curve on which that classification takes place. The Jacobian, its Hecke action, and the arithmetic quotients used to prove global scarcity belong to subsequent books. Here they will appear only at the final handoff, through the Abel--Jacobi map based at the rational cusp $\infty$.

There is also a convention about the word **rational**. A subgroup scheme $C\subset E$ over $K$ is rational if it is defined over $K$; its individual geometric generators need not be. An isogeny is rational if the morphism and both elliptic curves are defined over $K$. A point of a coarse curve is rational if its residue field is $K$. These three meanings are related, but they are not interchangeable without proof. The fixed-source statements in Chapter 6 give the clean equivalence needed for Galois representations. The discussion of coarse points in Chapters 3 and 6 records the remaining descent issue exactly.

## 2. The three level problems

### 2.1 Why level is a subgroup-scheme condition

Level structure is designed to retain a finite part of an elliptic curve while the curve varies in a family. A definition based only on points over the ground field is not stable under base change: a generator may appear after an extension, and distinct points can coalesce in characteristic dividing the level. Finite locally free subgroup schemes have constant rank, commute with base change, and retain nilpotent thickness. They are therefore the correct objects.

Let $E\to S$ be an elliptic curve. When $N$ is invertible on $S$, $E[N]$ is finite étale, so étale-locally it is the constant module $(\mathbf Z/N\mathbf Z)^2$. In that setting the subgroup-scheme definitions reduce to familiar finite-module language. When $N$ is not invertible, the same definitions must be strengthened by divisor conditions so that the intended rank is not lost in a nonreduced fiber.

There are three stability demands behind this choice. The datum must descend when a generator exists only after a cover; it must specialize when distinct torsion points collide; and it must admit a quotient elliptic curve functorially in the base. A finite locally free subgroup scheme satisfies all three. A list of rational points satisfies none in general.

Rank replaces cardinality. If $C\to S$ is finite locally free of rank $N$, every fiber has scheme-theoretic length $N$, even when its support has fewer points. On a smooth relative curve, $C$ is an effective Cartier divisor. This turns the generator condition into an equality of divisors and makes it a closed algebraic condition in families.

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

| Level datum                    | If $\operatorname{char}K\nmid N$          | If $\operatorname{char}K\mid N$                                       |
| ------------------------------ | ----------------------------------------- | --------------------------------------------------------------------- |
| $\Gamma_0(N)$                  | stable cyclic subgroup of $E[N](K^s)$     | cyclic finite locally free subgroup scheme; point set is insufficient |
| $\Gamma_1(N)$                  | $K$-rational point of exact order $N$     | Drinfeld point/divisor of exact order                                 |
| full level                     | ordered basis of $E[N](K^s)$ with descent | Drinfeld basis; not generally a group-scheme isomorphism              |
| degree-$p$ isogeny versus line | equivalent for $p\ne\operatorname{char}K$ | false as a point-set statement                                        |

In particular, the representation $G_K\to\operatorname{GL}_2(\mathbf F_p)$ on $E[p](K^s)$ is two-dimensional only for $p\ne\operatorname{char}K$. The rational-isogeny/reducibility equivalence in Chapter 6 always carries that hypothesis.

The distinction is not that degree-$p$ isogenies disappear in characteristic $p$. Relative Frobenius is a degree-$p$ isogeny, and so is Verschiebung. What disappears is the description of every kernel by a one-dimensional subspace of a two-dimensional geometric point set. In characteristic $p$, the group $E[p](K^s)$ can have $p$, $1$, or other point-set behavior depending on the ordinary or supersingular type, while the group scheme always has rank $p^2$.

Separability must also remain explicit. An isogeny of degree prime to the characteristic is automatically separable because its kernel is étale. In degree equal to the characteristic, Frobenius is purely inseparable. The dual identities still hold scheme-theoretically, but a geometric kernel count no longer computes the degree.

The level-$N$ table applies one prime at a time when $N$ has mixed characteristic behavior. If the base has residue characteristic $p\mid N$, the prime-to-$p$ part is étale and the $p$-primary part is finite flat. The full integral structure is their product, with a Drinfeld condition only where pointwise generation fails. This mixed decomposition is often the most efficient way to verify hypotheses.

### 2.5 Worked comparisons and counterexamples

Suppose $K$ has characteristic different from $2$ and

$$
E:y^2=x(x-a)(x-b)
$$

with $a,b\in K$ distinct and nonzero. The three nonzero points of $E[2]$ are rational. Each gives both a $\Gamma_1(2)$-structure and a $\Gamma_0(2)$-structure; there is no difference because a group of order two has a unique nonidentity generator.

For an odd prime $p$, take a stable line $C\subset E[p]$ on which Galois acts through a nontrivial character $\psi$. Then $(E,C)$ defines a $K$-object of the $\Gamma_0(p)$ stack, but no nonzero point of $C$ is $K$-rational. Hence it has a noncuspidal coarse image in $Y_0(p)(K)$ but no corresponding $K$-object of the $\Gamma_1(p)$ stack. This is not an exceptional pathology; it is the typical distinction between a rational isogeny and rational torsion.

For a characteristic-$p$ counterexample, let $E$ be ordinary over an algebraically closed field of characteristic $p$. Its connected subgroup $\ker F$ has rank $p$ but only the identity as a geometric point. The quotient by it is the relative Frobenius, an isogeny of degree $p$. No one-dimensional subspace of the geometric point group describes this kernel. This is precisely why the later equivalence excludes $p=\operatorname{char}K$.

### 2.6 Level structures over a fixed elliptic curve

Before allowing the curve itself to vary, it is useful to isolate the finite parameter space of level structures on one elliptic curve. Let $E/S$ be an elliptic curve and assume first that $N$ is invertible on $S$. The group scheme $E[N]$ is finite étale. Consequently its sheaf of sections, its sheaf of exact-order sections, and its sheaf of cyclic direct summands are represented by finite étale $S$-schemes. This assertion is local for the étale topology, where $E[N]$ becomes the constant module $(\mathbf Z/N\mathbf Z)^2$, and there it reduces to a finite set.

The exact-order locus is both open and closed. Indeed, a section $P$ has exact order $N$ precisely when, for every prime $q\mid N$, the section $[N/q]P$ is nonzero. In a finite étale scheme the equality of two sections is open and closed, so these finitely many inequalities cut out an open-and-closed subscheme. Similarly, a rank-$N$ cyclic subgroup is a direct summand étale-locally, and direct summands form a finite union of components of the subgroup parameter scheme.

Over an algebraically closed field of characteristic prime to $N$, the number of exact-order points is

$$
N^2\prod_{q\mid N}\left(1-\frac1{q^2}\right). \tag{2.7}
$$

To prove this, use the Chinese remainder theorem and count primitive vectors in $(\mathbf Z/q^r\mathbf Z)^2$. There are $q^{2r}$ vectors in total and $q^{2(r-1)}$ divisible by $q$, so the primitive count is $q^{2r}-q^{2r-2}$. Multiplication over the prime powers gives (2.7).

Every cyclic direct summand has exactly

$$
\varphi(N)=N\prod_{q\mid N}\left(1-\frac1q\right)
$$

generators. Dividing (2.7) by $\varphi(N)$ gives the number of cyclic order-$N$ direct summands:

$$
\frac{N^2\prod_{q\mid N}(1-q^{-2})}
{N\prod_{q\mid N}(1-q^{-1})}
=N\prod_{q\mid N}\left(1+\frac1q\right). \tag{2.8}
$$

This calculation will reappear as the generic degree of $X_0(N)\to X(1)$. It also separates the two forgetful maps: the point-level cover counts primitive vectors, while the cyclic-level cover counts the lines they generate.

At a prime dividing $N$, the finite parameter space still exists, but the proof cannot use étale point sets. A rank-$N$ subgroup divisor lies in the relative Hilbert scheme of length-$N$ subschemes of $E$. Containing the identity, being stable under inversion and addition, and being killed by $N$ are closed conditions: each says that a morphism from a finite scheme factors through a closed subscheme. Drinfeld cyclicity is imposed after adjoining a candidate generator by the equality

$$
\prod_{a\bmod N}(T-t_{aP})=F_C(T)
$$

in a smooth local coordinate, where $F_C$ is the monic equation of the subgroup divisor. Equality of the coefficients is closed. Taking the fppf sheaf quotient by $(\mathbf Z/N\mathbf Z)^\times$ forgets the local generator. This is the integral replacement for dividing a set of primitive vectors by the number of its generators; no assertion that the quotient morphism is flat is being made.

For generalized elliptic curves, one adds ampleness. On any stratum of fixed polygon size, ampleness is the condition that the component image of the subgroup be surjective. It is open and closed on that stratum. The resulting parameter space is finite on each fixed stratum, but it need not be proper while the underlying polygon is held fixed: a component-direction point may approach a node and force a change to a larger polygon. Compactified moduli permit precisely that change. This explains why a level structure over a fixed curve is only one local ingredient in the global modular curve.

### 2.7 Galois characters carried by level

Level structures remember representations as well as finite schemes. Let $K$ have characteristic prime to $N$, let $C\subset E[N](K^s)$ be a $G_K$-stable cyclic subgroup, and choose a generator $P$. Since every other generator is $aP$ for a unique $a\in(\mathbf Z/N\mathbf Z)^\times$, there is a continuous character

$$
\psi_C:G_K\longrightarrow(\mathbf Z/N\mathbf Z)^\times,\qquad
\sigma(P)=\psi_C(\sigma)P. \tag{2.9}
$$

Changing $P$ to $aP$ does not change $\psi_C$ because the coefficient group is abelian. Thus the character belongs to the oriented line itself, even though the subgroup can be defined without a generator. The smallest extension over which a generator becomes rational is the fixed field of $\ker\psi_C$.

When $N=p$ is prime, extend $P$ to a basis $(P,Q)$ of $E[p]$. The matrix of Galois has upper triangular form

$$
\rho_{E,p}(\sigma)=
\begin{pmatrix}
\psi_C(\sigma)&b(\sigma)\\
0&\theta(\sigma)
\end{pmatrix}. \tag{2.10}
$$

The Weil pairing determines the second diagonal character. Since

$$
e_p(\sigma P,\sigma Q)
=\sigma e_p(P,Q)
=e_p(P,Q)^{\overline\chi_p(\sigma)},
$$

while bilinearity gives the left side as $e_p(P,Q)^{\psi_C(\sigma)\theta(\sigma)}$, one has

$$
\theta=\overline\chi_p\psi_C^{-1}. \tag{2.11}
$$

The function $b$ is not generally a character. The cocycle identity for matrices says that it represents an extension of the quotient character by the kernel character. It can be nonzero even though the representation is reducible. Thus $X_0(p)$ detects an invariant filtration, not a splitting.

The determinant formula is basis-independent:

$$
\det\rho_{E,p}=\overline\chi_p. \tag{2.12}
$$

It is simply the Galois action on the Weil pairing. This proves at the same time the cyclotomic obstruction to full rational level and the character formula for the dual isogeny.

For composite $N$, $C$ is a free rank-one $\mathbf Z/N\mathbf Z$-module, so (2.9) remains valid. Its reduction modulo each prime power gives the characters of the primary parts. A global generator is rational exactly when the full character is trivial, equivalently when every primary character is trivial. It is possible for a subgroup to have rational generators modulo each prime separately over different extensions but no generator over $K$; the fields must be combined, and the single character (2.9) records the compatibility.

Finally, reducibility must be stated over the coefficient field in question. A two-dimensional $\mathbf F_p$-representation may acquire an invariant line over $\mathbf F_{p^2}$ without having one over $\mathbf F_p$. Such an eigenline does not define a subgroup of order $p$ in the constant $\mathbf F_p$-module $E[p](K^s)$. Rational $p$-isogenies correspond to $\mathbf F_p$-lines and therefore to reducibility over $\mathbf F_p$, not merely absolute triangularizability after scalar extension.

## 3. Fine spaces, coarse curves, and descent

### 3.1 Why automorphisms obstruct a universal curve

A fine moduli space must carry a universal object whose pullback classifies every family uniquely. An object with a nontrivial automorphism contradicts this uniqueness. Every elliptic curve has $[-1]$, so the $j$-line is only a coarse space. Adding a cyclic subgroup does not help: $[-1]$ preserves every subgroup. Thus $Y_0(N)$ is intrinsically a coarse curve attached to a stack with generic stabilizer $\{\pm1\}$.

A chosen generator usually kills $[-1]$, since $-P=P$ only for order at most two. A full basis is still more rigid. This is why $X_1(N)$ and $X(N)$ often possess universal families in ranges where $X_0(N)$ cannot.

The special values $j=0$ and $1728$ require additional care in characteristic different from $2$ and $3$, because the geometric automorphism group is larger. In characteristics $2$ and $3$ the stabilizer picture is more complicated still. A statement about coarse points that ignores these loci has silently assumed away its hardest descent cases.

The local quotient $[Y/G]\to Y/G$ is the model. The stack remembers the stabilizer $G_y$ of a point, while the coarse scheme remembers only its orbit. A universal family on $Y$ descends to the quotient stack with its equivariant structure. It descends to the scheme quotient only if every stabilizer acts trivially on the fiber object, which inversion does not do on an elliptic curve.

Functions behave differently from families. Every invariant function on $Y$ descends to $Y/G$, so the $j$-invariant and the source and target maps of an isogeny descend to coarse curves. The universal elliptic curve generally does not. This is why explicit rational functions on $X_0(N)$ are legitimate even though a universal Weierstrass equation on the whole coarse curve is not.

### 3.2 The fine ranges

Over $\mathbf Z[1/N]$, full level $N\ge3$ kills automorphisms and gives a fine moduli scheme after a Weil-pairing component is selected over its cyclotomic base. The $\Gamma_1(N)$ problem is fine for $N\ge4$ over $\mathbf Z[1/N]$. The small levels retain automorphisms. Bare $\Gamma_0(N)$ is never fine because $[-1]$ survives.

These are prime-to-level assertions. At a prime dividing $N$, a Drinfeld basis can collapse set-theoretically and fail to rigidify an object. Therefore a level which is fine on the generic fiber need not yield a fine integral problem at the level prime. A prime-to-level auxiliary structure, customarily full level $M\ge3$ with $(M,N)=1$, restores rigidity for local calculations.

On a fine space $Y$, a $K$-rational point really does pull the universal family back to an elliptic curve with the stated level over $K$. This simple sentence is one of the chief benefits of rigidification.

The automorphism calculation explains the bounds. An origin-preserving automorphism of an elliptic curve has finite order. If it fixes a full basis of $E[N]$ with $N\ge3$, its action on the prime-to-characteristic Tate module is a finite-order matrix congruent to the identity modulo $N$. The principal congruence subgroup of level at least three is torsion-free, so the automorphism is the identity. For a point $P$ of exact order $N\ge4$, let a nonidentity automorphism $g$ fix $P$. The possible element orders are $2,3,4,6$, including for the larger automorphism groups in characteristics $2$ and $3$. In order two one has $g=[-1]$, so $2P=0$. In order three the relation $1+g+g^2=0$ gives $3P=0$. In orders four and six, respectively $g^2=[-1]$ and $g^3=[-1]$, again giving $2P=0$. Every case contradicts the exact order of $P$. This proves point-level rigidity over all of $\mathbf Z[1/N]$, not only in characteristics different from $2$ and $3$.

At $N=2$, inversion fixes the full two-torsion and every point of order two. At $N=3$, exceptional automorphisms can fix point-level data. These are real exclusions, not artifacts of the proof. At a level prime, a Drinfeld generator can specialize to the identity as a geometric point while retaining length $N$ as a divisor, so the prime-to-level fixed-point argument no longer applies.

Representability also needs an atlas, not only trivial automorphisms. The projective framing construction supplies a scheme atlas. When inertia is trivial, the stack is a sheaf and descent of the framed universal family produces the representing scheme. Thus “fine” combines rigidity with effective geometric construction.

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

### 3.6 Construction of the stacks and coarse curves

We now collect the construction that justifies the notation used throughout the book. Let $\Gamma$ be $\Gamma_0(N)$ or $\Gamma_1(N)$, and begin over $\mathbf Z[1/N]$. Define $\mathcal Y(\Gamma)$ by smooth elliptic curves with the corresponding level and define $\mathcal X(\Gamma)$ by generalized elliptic curves with ample level. The latter is not obtained by adding a set of abstract points; its objects at the boundary are the polygonal families of Chapter 5.

**Theorem 3.1 (compactified modular objects).** The following assertions hold.

1. $\mathcal X(\Gamma)$ is a proper normal algebraic stack of relative dimension one over $\mathbf Z[1/N]$, with finite separated diagonal.
2. Its smooth-elliptic open is $\mathcal Y(\Gamma)$ and is schematically dense.
3. There is a projective coarse curve

   $$
   \pi:\mathcal X(\Gamma)\longrightarrow X(\Gamma),
   $$

   characterized by the usual orbit and universal mapping properties.
4. The boundary is a finite effective Cartier divisor on the stack. On a framed cusp branch its completed ring is $A[[t]]$ and its ideal is $(t)$.
5. Forgetful maps, quotient-isogeny maps, and changes of generator extend to the compactification and descend to the coarse curves.

For $\Gamma_0(N)$ and $\Gamma_1(N)$ we write the coarse curves as $X_0(N)$ and $X_1(N)$ and their opens as $Y_0(N)$ and $Y_1(N)$.

**Proof strategy.** An ample level divisor bounds the number of components of every polygon. A high power of its line bundle embeds every object in one of finitely many projective Hilbert schemes. Properness is then a valuative extension theorem. To construct the coarse curve one adds auxiliary full level only on an arithmetic open where that auxiliary order is invertible, normalizes its boundary branches, and retains the decontraction carrying the auxiliary basis. The resulting local finite quotients glue by their coarse universal property.

**Proof.** Let $D$ be the level divisor, of degree $N$ for point or cyclic level. Since $D$ has positive degree on every component, a geometric polygon has at most $N$ components. For a uniform integer $m$, the line bundle $\mathcal O(mD)$ has positive degree large enough on every component to separate points, tangent vectors, and the two branches at each node. The normalization exact sequence for a polygon proves this component by component. Thus it gives a projective embedding with one of finitely many Hilbert polynomials.

Inside the corresponding finite union of Hilbert schemes, being a smooth genus-one curve or a polygonal genus-one curve is locally closed. The identity, action, subgroup, and generator data are represented by sections and finite Hilbert schemes. The group identities and Drinfeld divisor equalities are closed equations, while ampleness is open on each component stratum. Choosing a basis of the pushforward of $\mathcal O(mD)$ gives a scheme atlas; changing the basis gives the quotient presentation. Automorphisms preserving ample level form a finite separated scheme, so the diagonal is finite and separated. This proves algebraicity and finite presentation.

For properness, take a level object over the fraction field of a DVR over $\mathbf Z[1/N]$. After finite extension, the elliptic curve has good or split multiplicative reduction. In the good case $N$ is invertible and the level extends uniquely inside the finite étale group $E[N]$. In the multiplicative case, Tate uniformization determines the component image of the level and hence the unique polygon on which its divisor is ample. These constructions give existence. The ample line bundle reconstructs the curve as a relative Proj, so a generic level-preserving isomorphism extends uniquely; this gives separated uniqueness. On the elliptic locus the deformation is one-dimensional and smooth, while a framed cusp has completed ring $A[[t]]$ with $A$ finite étale over the base. These charts prove normality.

It remains to construct the coarse scheme without making a false global auxiliary-level assertion. Cover the arithmetic base by the opens on which $2$ and $3$ are respectively invertible. On the first use auxiliary full level $4$, and on the second use auxiliary full level $3$. Add that level on the smooth locus and normalize the projective closure. At a boundary branch the auxiliary basis lives on its canonical decontraction $E'\to E$; it is not required to be ample on the original $\Gamma$-polygon. The normalized branch scheme $Y_M$ is projective and has no object automorphisms. The finite change-of-basis group $G_M$ acts, and on the corresponding arithmetic open there is an equivalence

$$
\mathcal X(\Gamma)\simeq[Y_M/G_M]. \tag{3.4}
$$

The invariant-theoretic quotient $Y_M/G_M$ is projective and has the coarse universal property. On the overlap the two quotients are uniquely isomorphic because they are coarse for the same stack; these isomorphisms satisfy the cocycle condition and glue to $X(\Gamma)$. Thus no single auxiliary integer is being treated as invertible over all of $\mathbf Z[1/N]$.

On a framed cusp, the boundary is $t=0$ in $A[[t]]$; since $t$ is a non-zero-divisor, these local equations glue to a Cartier divisor. Quotient and contraction of generalized elliptic curves commute with base change, so the natural maps exist on the stack. Composing with a coarse map and invoking its universal property gives the descended maps of coarse curves. $\square$

This theorem explains two conventions that will recur. A universal generalized elliptic curve exists on $\mathcal X(\Gamma)$ and on $Y_M$, not in general on $X(\Gamma)$. Conversely, every natural map whose value is only an isomorphism class, such as the two maps to the $j$-line, does descend to $X(\Gamma)$. Statements about families belong upstairs; statements about rational points and finite maps can be made downstairs once descent of individual objects has been addressed.

### 3.7 Twisting and effective descent in concrete terms

The abstract cocycle of Section 3.3 becomes familiar when the only automorphisms are signs. Suppose $\operatorname{char}K\ne2,3$ and $j\notin\{0,1728\}$. Any two $K$-models with invariant $j$ are quadratic twists of one another. Over $K^s$, choose an isomorphism

$$
f:E_{K^s}\xrightarrow{\sim}E'_{K^s}.
$$

For $\sigma\in G_K$, the element

$$
c_\sigma=f^{-1}\,{}^\sigma f
$$

lies in $\{\pm1\}$. Associativity gives $c_{\sigma\tau}=c_\sigma c_\tau$, so $c$ is a quadratic character. Conversely, twisting by a quadratic character changes the descent datum by these signs.

Now let $C\subset E[N](K^s)$ be a cyclic subgroup. The sign automorphism fixes $C$ as a subgroup, even though it reverses every generator of order greater than two. Consequently simultaneous quadratic twisting of $(E,C)$ preserves the subgroup descent condition. This is why the generic $\Gamma_0$ obstruction is milder than the $\Gamma_1$ obstruction. For a point-level pair $(E,P)$, the sign sends $P$ to $-P$, and a twist can alter the field of definition of the chosen generator.

This observation gives a concrete proof of the generic neutrality criterion. Let a coarse $Y_0(N)$ point with nonexceptional $j$ be rational over $K$. Choose any model $E/K$ with that $j$ and identify the geometric source with $E_{K^s}$. Galois carries the corresponding subgroup $C$ to one isomorphic to it. The only source automorphisms are signs, and signs do not change $C$. Hence $\sigma C=C$ for every $\sigma$. Finite étale descent gives $C/K$. No second cohomology calculation remains.

At an exceptional invariant the larger automorphism group acts nontrivially on some subgroups. The concrete object is then the finite set

$$
\operatorname{Aut}(E_{K^s})\backslash
\{\text{cyclic order-}N\text{ subgroups of }E[N]\}. \tag{3.5}
$$

A coarse point is a Galois-fixed element of this orbit set. A rational subgroup is a Galois-fixed element before the quotient. The map from fixed subgroups to fixed orbits need not be bijective for an arbitrary finite group action. Thus the exceptional check is genuinely an orbit-lifting problem.

If a lift exists, descent is effective. Indeed, a stable finite étale subgroup corresponds to a stable finite subset with its addition law; the equivalence between finite étale schemes and continuous Galois sets descends it uniquely. The quotient $E/C$ is then formed over $K$, and its base change to $K^s$ is the expected geometric quotient. There is no further obstruction attached to the target.

The same reasoning works over a DVR at a prime away from $N$. A subgroup stable on the generic fiber has a unique finite étale closure inside the smooth $N$-torsion of the integral elliptic curve. At a level prime, finite étale descent is replaced by finite-flat closure and the Drinfeld divisor condition. The conceptual order remains the same: first descend the subgroup scheme, then form the quotient. Descending only a coarse source--target pair of $j$-invariants is not a substitute for descending the kernel.

This concrete analysis will let us use coarse curves efficiently without pretending they are fine. Whenever the elliptic curve and stable subgroup are constructed first, as in a reducible Galois representation, the coarse point is harmless. Whenever one starts from an arbitrary coarse point, one performs the orbit-lifting check before speaking of a rational isogeny.

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

At the boundary, retaining a smaller piece of level can make its divisor fail to meet every component of the original polygon. The forgetful operation then includes the canonical contraction of all components invisible to the retained divisor. On smooth fibers this contraction is the identity. Thus the arrows in (4.1) are honest morphisms of compactified moduli problems, not merely rational maps extended after the fact.

Composition is independent of the order of forgetting. If one retains subgroup divisors $D\subset D'$, the component subgroup seen by $D$ is contained in that seen by $D'$. Contracting first to the $D'$-components and then to the $D$-components equals the direct contraction to the $D$-components by uniqueness of relative Proj. This supplies strict compatibility among all change-of-level maps.

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

The subgroup in (4.7) has the correct rank. The dual kernel has rank $Q$, the transported complementary subgroup has rank $N/Q$, and their intersection is trivial because their ranks are coprime. Their direct sum is therefore cyclic of rank $N$. Applying the construction again quotients by the dual kernel and recovers $E$; the complementary subgroup is transported back. This proves $w_Q^2=1$ on isomorphism classes.

If $Q_1$ and $Q_2$ are coprime exact divisors, quotienting by $C_{Q_1}$ and $C_{Q_2}$ commutes. The dual replacements occur in independent primary factors, so

$$
w_{Q_1}w_{Q_2}=w_{Q_1Q_2}=w_{Q_2}w_{Q_1}. \tag{4.8a}
$$

For nonsquarefree $N$, only exact divisors admit this clean decomposition. An arbitrary divisor can share primes with its complement, and then the proposed dual part can intersect the transported level. The exact-divisor hypothesis is therefore structural rather than conventional.

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

To prove the kernel description, restrict $\varphi$ to $E[N]$. The dual identity shows that its image lies in $\ker\widehat\varphi$. Its kernel is $C$, so it induces a monomorphism

$$
E[N]/C\longrightarrow\ker\widehat\varphi.
$$

Both sides have rank $N$: the left side has rank $N^2/N$, and the right side has rank $\deg\widehat\varphi=N$. Hence the monomorphism is an isomorphism. This rank argument works scheme-theoretically and does not require all torsion points to be distinct.

At composite level, $w_N$ is still defined by the full cyclic subgroup. For a partial exact divisor $Q$, only the $Q$-primary part is dualized and the complementary part is transported through the quotient. The coprimality condition ensures that transport is an isomorphism on the complementary torsion. Without it, the quotient could alter both pieces and the displayed construction would not square to the identity.

Duality also controls differentials. If $\omega'$ is an invariant differential on $E'$, then $\varphi^*\omega'$ is an invariant differential on $E$. Pulling back once more through the dual gives multiplication by $N$. At a prime dividing the residue characteristic, one of these pullbacks can vanish on the special fiber while the other carries the complementary factor. This is the infinitesimal source of the two parameters in the equation $xy=p$ developed in Chapter 8.

### 4.5 Degrees and ramification of the natural maps

The maps above are finite after compactification. This follows abstractly because a fixed generalized elliptic curve admits only finitely many level structures on each bounded component stratum, while properness turns a quasi-finite map into a finite one. Their generic degrees can be computed on an elliptic curve without exceptional automorphisms.

For the source projection

$$
\pi_1:X_0(N)\longrightarrow X(1),
$$

the generic fiber consists of the cyclic direct summands of $E[N]$. Formula (2.8) gives

$$
\deg\pi_1=N\prod_{q\mid N}\left(1+\frac1q\right). \tag{4.12}
$$

Since $\pi_2=\pi_1\circ w_N$ and $w_N$ is an automorphism, $\pi_2$ has the same degree. At prime level this degree is $p+1$, the number of lines in $\mathbf P^1(\mathbf F_p)$.

For $N>2$, the generic degree of

$$
X_1(N)\longrightarrow X_0(N)
$$

is $\varphi(N)/2$. The subgroup has $\varphi(N)$ generators, but $(E,P)$ and $(E,-P)$ are isomorphic through $[-1]$ on the coarse point-level curve. Away from the loci with larger automorphism groups, no other generators are identified. Equivalently, the generic deck group is

$$
(\mathbf Z/N\mathbf Z)^\times/\{\pm1\}. \tag{4.13}
$$

For $N=2$ the quotient notation must be read separately and the degree is one. On stacks, the generator torsor has the full unit group; the lost factor two is stored in inertia rather than in the coarse degree.

Finite does not mean étale. Three independent sources of ramification occur.

First, an elliptic curve with an exceptional automorphism can identify several level structures. This creates ramification above $j=0$ or $1728$ in characteristic different from $2$ and $3$. Second, cusp width creates boundary ramification. If $t$ and $s$ are genuine local uniformizers and the map has

$$
t=u s^e,\qquad u\in A[[s]]^\times, \tag{4.14}
$$

then $e$ is the ramification index. Third, in residue characteristic dividing a level, a finite étale generic map can acquire inseparable Frobenius components.

The degree is recovered by summing ramification indices over any geometric fiber in characteristic zero. At the cusps of $X_0(N)\to X(1)$ this gives the identity

$$
\sum_{c}w_c
=N\prod_{q\mid N}\left(1+\frac1q\right). \tag{4.15}
$$

One can prove (4.15) either from the finite-map degree or directly from the double-coset decomposition of $\Gamma_0(N)\backslash\operatorname{SL}_2(\mathbf Z)$ by parabolic orbits. In the latter proof, each right coset lies in exactly one cusp orbit, and the orbit length is the cusp width. Thus the widths partition the set of cosets.

At prime level the two cusps already account for the degree: their widths are $1$ and $p$, whose sum is $p+1$. The equality does not mean that the entire map is unramified elsewhere; elliptic points contribute ramification to Riemann--Hurwitz, but their fibers contain correspondingly more unramified points so that every fiber still has total degree $p+1$.

These calculations are also a consistency test for any proposed coordinate formula. Its numerator and denominator must make the rational map to the $j$-line have degree (4.12); the orders of its poles must reproduce the cusp widths; and applying $w_N$ must exchange the source and quotient $j$-functions.

### 4.6 The analytic double-coset picture

Over $\mathbf C$, the algebraic maps can be seen directly on lattices. Write

$$
E_\tau=\mathbf C/(\mathbf Z\tau+\mathbf Z),\qquad \tau\in\mathfrak H.
$$

The subgroup generated by the class of $1/N$ is cyclic of order $N$. A change of oriented lattice basis by

$$
\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{SL}_2(\mathbf Z)
$$

preserves this subgroup precisely when $c\equiv0\pmod N$. This proves the analytic identification with $\Gamma_0(N)\backslash\mathfrak H$. Preserving the generator itself imposes $c\equiv0$ and $d\equiv1\pmod N$, equivalently the usual $\Gamma_1(N)$ condition after the chosen row-versus-column convention is fixed.

The fiber of the forgetful map can be identified with a coset space. The group $\operatorname{SL}_2(\mathbf Z/N\mathbf Z)$ acts transitively on primitive vectors and on cyclic direct summands. The stabilizer of the standard line is the upper triangular subgroup, so

$$
\Gamma_0(N)\backslash\operatorname{SL}_2(\mathbf Z)
$$

is in bijection with the projective line $\mathbf P^1(\mathbf Z/N\mathbf Z)$, understood as primitive pairs modulo multiplication by a unit. Counting it prime-power by prime-power gives (2.8).

Degeneracy maps are also lattice maps. At prime level, the source map keeps

$$
\Lambda_\tau=\mathbf Z\tau+\mathbf Z,
$$

while quotienting by the subgroup generated by $1/p$ replaces the lattice by

$$
\Lambda_\tau+\mathbf Z\frac1p
=\mathbf Z\tau+\mathbf Z\frac1p.
$$

After multiplying the lattice by $p$, the quotient is isomorphic to $E_{p\tau}$. A different representative of the cyclic subgroup gives an equivalent fractional-linear formula. The Atkin--Lehner matrix

$$
W_p=\begin{pmatrix}0&-1\\p&0\end{pmatrix} \tag{4.16}
$$

has determinant $p$ rather than one, but it normalizes $\Gamma_0(p)$ inside $\operatorname{GL}_2^+(\mathbf Q)$. Its action $\tau\mapsto-1/(p\tau)$ exchanges the source lattice with the quotient lattice and therefore realizes the dual-isogeny involution.

For a general exact divisor $Q\mid N$, one chooses an integral matrix of determinant $Q$ whose lower-left entry is divisible by $N$ and whose remaining entries satisfy the Bézout relation forced by $(Q,N/Q)=1$. Different choices differ by left and right multiplication by $\Gamma_0(N)$, so they induce the same involution on the quotient. Squaring gives a scalar matrix modulo the congruence action, proving $w_Q^2=1$ on the coarse curve.

The boundary appears by adjoining $\mathbf P^1(\mathbf Q)$ to $\mathfrak H$. A cusp is a double orbit of a primitive rational direction. Its width is the size of the orbit of a lift under the parabolic translation subgroup. This explains simultaneously why cusp widths sum to the index, why exact-divisor matrices permute denominator types, and why the finite maps ramify only through parabolic stabilizers at the boundary.

The analytic description proves the complex topological assertions and supplies the index computations. It does not by itself construct a curve over $\mathbf Q$, extend a quotient through a bad fiber, or decide whether a rational coarse point has a rational representative. Those are algebraic descent statements proved in the surrounding chapters. The two descriptions agree because they classify the same complex elliptic curves with the same finite subgroup data.

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

Regularity of the extended map follows directly from the completed parameters. A morphism of punctured discs could a priori have a pole at the origin, but the quotient formulas express the target parameter as $q^p$, $t$, or $t^p$, all elements of the source power-series ring. Properness gives an extension abstractly; the Tate calculation identifies its ramification and proves that the modular quotient is the extension obtained.

Contraction is needed for the forgetful map from the component cusp. The source $p$-gon carries the component generator in its smooth locus. After forgetting the subgroup, the stable unlevelled moduli problem retains only a one-gon. Contracting the other components produces period $t^p$. Omitting this contraction would map to a generalized curve outside the chosen unlevelled compactification.

The same uniqueness lets formal formulas globalize. Two stack morphisms that agree on the dense elliptic locus agree everywhere because the target is separated. Hence a quotient computed on a Tate cover is not merely a local model; it determines the global boundary value of the degeneracy map.

### 5.6 The boundary divisor and the completed cusp package

Let $\mathcal C_\Gamma$ denote the complement of the elliptic locus in the compactified stack. A framed cusp chart is a power-series disc

$$
\operatorname{Spf}A[[t]], \tag{5.10}
$$

carrying a Tate generalized elliptic curve whose unlevelled period is $q=t^w$. The integer $w$ is the cusp width. The boundary is cut out by $t$, so it is an effective Cartier divisor. If two framed charts overlap, both parameters cut out the same reduced complement of the dense elliptic open and have order one there; their ratio is a unit. Hence the Cartier ideals glue.

On a coarse curve the actual uniformizer can be a power of $t$. Suppose a tame effective stabilizer of order $e$ acts by $t\mapsto\zeta_e t$. Then

$$
A[[t]]^{\mu_e}=A[[t^e]]. \tag{5.11}
$$

Thus $u=t^e$ is the coarse uniformizer, and pullback of the reduced coarse cusp has multiplicity $e$ on the framed chart. This quotient exponent is conceptually distinct from the modular cusp width $w$, which measures the map to the unlevelled Tate parameter. Both can occur in one composite map, and confusing them produces an incorrect ramification index.

At prime cyclic level there are exactly two framed boundary types. They can be written in compatible parameters as

$$
(E_q,\mu_p),\qquad
(E_{t^p},\langle t\rangle). \tag{5.12}
$$

For the first type, the source and quotient maps to $X(1)$ satisfy

$$
\pi_1^*q=q,\qquad \pi_2^*q=q^p. \tag{5.13}
$$

For the second,

$$
\pi_1^*q=t^p,\qquad \pi_2^*q=t. \tag{5.14}
$$

The proof is the quotient calculation on $\mathbf G_m$: quotient by $\mu_p$ is induced by $u\mapsto u^p$ and changes the period to $q^p$, whereas quotient by the class of $t$ enlarges the period lattice from $t^{p\mathbf Z}$ to $t^{\mathbf Z}$. The $p$-gon model is required in the second formula so that $[t]$ remains in the smooth locus on specialization.

Equations (5.13)--(5.14) prove several claims at once. The two cusp widths for the source map are $1$ and $p$. The quotient map reverses them. The Atkin--Lehner involution exchanges the two charts. The discriminant of the source Tate curve has order $1$ in $q$ on the first chart and order $p$ in $t$ on the second. Finally, both maps are regular at the boundary: every pulled-back parameter is a genuine power series with no negative exponent.

For $X_1(N)$, a cusp chart also records a generator. If the component image of the generator has order $d\mid N$, write $N=de$ and use the $d$-gon Tate model with $q=t^d$. After a finite flat coefficient extension the generator has the form

$$
P=[\zeta_N^a t]. \tag{5.15}
$$

Its multiples visit each component $e$ times. The indices of the multiples on one fixed component differ by $d$, so their toric coordinates differ by powers of $\zeta_N^{ad}$. They fill the full rank-$e$ multiplicative divisor precisely when this is a Drinfeld primitive $e$th root, equivalently

$$
\gcd(a,e)=1. \tag{5.15a}
$$

Thus the pair $(d,a)$, subject to $d\mid N$ and (5.15a), gives the framed $X_1(N)$ cusp labels; changing the polygon framing gives the finite equivalence relation already used in the stabilizer recipe of Section 5.4. Cyclotomic Galois sends $a$ to $ua$ when $\zeta_N\mapsto\zeta_N^u$, and the residue field of the descended cusp is exactly the fixed field of the stabilizer of its framing orbit. This makes the recipe of Section 5.4 effective without incorrectly claiming that every $X_1(N)$ cusp has the full cyclotomic residue field. The formula includes the extremes $d=1$, where (5.15a) is the usual primitive-root condition, and $d=N$, where $e=1$ and the generator runs once around every component.

The completed chart also proves proper boundary uniqueness. A generic Tate level determines its component image and hence $d$. Choosing fewer components would force the generator into a node; choosing more would make its divisor nonample. Once $d$ is fixed, the framed deformation parameter is unique up to a unit. Thus the cusp is not an arbitrary point added to the curve: it is the unique extension of the level object with exactly the polygon seen by its divisor.

We shall use the following completed cusp package without further reconstruction:

1. every geometric cusp has a finite framing with ring $A[[t]]$;
2. the reduced stack boundary is $t=0$;
3. the unlevelled period is $q=t^w$;
4. the residue field is obtained by descending the discrete level labels under their cyclotomic stabilizer;
5. forgetful, quotient, and Atkin--Lehner maps are determined by their Tate period formulas;
6. after a tame coarse quotient, one replaces $t$ by the invariant uniformizer $t^e$.

These six statements are sufficient for all later arguments about cusp rationality, specialization, ramification, and genus.

### 5.7 Counting and descending $X_0(N)$ cusps

We now justify the closed formula of Section 5.4. Represent a geometric cusp by a primitive column $(a,c)^t$, or the fraction $a/c$. Put

$$
d=\gcd(c,N).
$$

The value of $d$ is preserved, up to replacing $c$ by an equivalent representative with the same gcd, by the $\Gamma_0(N)$ action. Elementary row operations using matrices with lower-left entry divisible by $N$ reduce the denominator to the divisor $d$. Thus every orbit has a representative $a/d$ with $d\mid N$ and $(a,d)=1$.

For fixed $d$, two numerators give the same cusp exactly through the residual congruence measured by

$$
h_d=\gcd(d,N/d). \tag{5.16}
$$

More explicitly, the allowed upper-triangular changes alter $a$ by multiplication by a unit and addition of a multiple whose effective modulus is $h_d$. After the sign already present in the modular action is accounted for, the remaining primitive labels form a torsor under $(\mathbf Z/h_d\mathbf Z)^\times$. Hence there are $\varphi(h_d)$ geometric cusps of denominator type $d$.

One can verify this reduction prime by prime. Let $N=q^r$ and $d=q^i$. A primitive denominator direction has valuation $i$ after the action of $\Gamma_0(q^r)$. The numerator ambiguity that survives has modulus

$$
q^{\min(i,r-i)}.
$$

Thus the number of labels is $\varphi(q^{\min(i,r-i)})$. The Chinese remainder theorem multiplies these independent local label sets, and summing over all divisor types gives

$$
c_\infty(N)=\sum_{d\mid N}\varphi(\gcd(d,N/d)). \tag{5.17}
$$

The width calculation is compatible with the same classification. For a representative $a/d$ with $(a,d)=1$, the formula

$$
w_{a/d}=\frac{N}{\gcd(N,d^2)} \tag{5.18}
$$

depends only on the denominator type. Therefore

$$
\sum_{d\mid N}
\varphi(h_d)\frac{N}{\gcd(N,d^2)}
=N\prod_{q\mid N}\left(1+\frac1q\right). \tag{5.19}
$$

This identity may be checked multiplicatively. For $N=q^r$, split the sum at $i\le r/2$ and $i\ge r/2$, substitute $h_{q^i}=q^{\min(i,r-i)}$, and use $\sum_{j=0}^m\varphi(q^j)=q^m$. The result is $q^r+q^{r-1}$, the local factor in the index. Products over primes give (5.19).

The field of definition comes from the toric part of the Tate level. On the denominator-$d$ branch, the surviving label is a primitive $h_d$th root of unity. Galois sends

$$
\zeta_{h_d}\longmapsto\zeta_{h_d}^{u},\qquad
u\in(\mathbf Z/h_d\mathbf Z)^\times,
$$

and this action is simply transitive on the $\varphi(h_d)$ labels. Consequently these geometric cusps form one closed point with residue field $\mathbf Q(\zeta_{h_d})$ for each denominator type, with the evident splitting when $h_d=1$ or $2$. Its geometric degree is $\varphi(h_d)$, exactly the summand in (5.17).

For example, take $N=9$. The divisor types $1,3,9$ have

$$
h_1=1,\qquad h_3=3,\qquad h_9=1.
$$

There are four geometric cusps: two rational cusps of types $1$ and $9$, and one closed cusp of type $3$ with residue field $\mathbf Q(\zeta_3)$ and two geometric points. Their widths are $9,1,1$ for the corresponding geometric points, so the total width is $9+1+1+1=12$, equal to the index of $\Gamma_0(9)$.

For squarefree $N$, $d$ and $N/d$ are coprime for every divisor $d$, so $h_d=1$. There are $2^{\omega(N)}$ cusps and every one is rational. For nonsquarefree $N$, the example above shows exactly how cyclotomic cusp fields appear. The result is a scheme-theoretic statement about closed boundary points, not merely a count of fractions in $\mathbf P^1(\mathbf Q)$.

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

The forgetful map from point level to cyclic level records this character geometrically. Over the locus with no exceptional automorphisms, its geometric deck group is $(\mathbf Z/N\mathbf Z)^\times/\{\pm1\}$ on coarse curves. The field generated by a chosen lift is controlled by the image of $\psi_C$, modulo the sign already identified coarsely. On the stack, where $P$ and $-P$ remain distinct objects unless an isomorphism is displayed, the full unit action is retained.

For $p=2$ the distinction collapses: the nonzero point of a subgroup of order two is its unique generator, so a rational subgroup has a rational point. For every odd prime the distinction can be nontrivial. It is therefore unsafe to infer rational torsion from a rational isogeny except at degree two or after proving $\psi_C=1$.

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

Here is the pairing proof of (6.5). Let $L=\ker\varphi\subset E[p]$ and let $L'=\ker\widehat\varphi\subset E'[p]$. The image of $E[p]$ under $\varphi$ is $L'$, and the induced quotient map identifies $E[p]/L$ with $L'$. The determinant of $E[p]$ is the cyclotomic character by the Weil pairing. Therefore the character of the quotient line is the determinant divided by the character of $L$, giving $\overline\chi_p\psi^{-1}$.

Equivalently, choose $P$ spanning $L$ and $Q$ whose image spans $L'$. The value $e_p(P,Q)$ is a primitive root after choosing compatible lifts. Galois acts on it cyclotomically, while bilinearity makes the exponent the product of the two line characters. Their product must be $\overline\chi_p$.

The formula has a useful fixed-point consequence. If an isogeny is isomorphic to its dual under an Atkin--Lehner fixed point, then the unordered pair of characters is stable under exchange. This does not force $\psi^2=\overline\chi_p$ unless the isomorphism also identifies the two labeled lines. Coarse fixed points can carry an automorphism exchanging source and target, so labels must be retained before drawing a character equation.

### 6.5 Composite level and cyclicity

When $N$ is composite and prime to the characteristic, a cyclic subgroup of order $N$ is a rank-one direct summand of $(\mathbf Z/N\mathbf Z)^2$. Merely having a stable subgroup of order dividing $N$ is not enough. For example, the subgroup generated by $(2,0)$ in $(\mathbf Z/4\mathbf Z)^2$ has order two and is not a cyclic level-$4$ subgroup.

Primary decomposition gives

$$
C=\bigoplus_{q\mid N} C[q^{v_q(N)}]. \tag{6.6}
$$

The subgroup is cyclic of order $N$ exactly when each primary part is cyclic of full order. Galois stability can be checked on these characteristic primary pieces. This explains both the exact-divisor decomposition used by Atkin--Lehner operators and the need to state cyclicity rather than only rank.

If $N=MN'$ with $(M,N')=1$, the idempotents supplied by Bézout split every $\mathbf Z/N\mathbf Z$-module:

$$
C=C[M]\oplus C[N'].
$$

Both summands are characteristic in $C$, so a Galois-stable $C$ has stable primary pieces. Conversely, stable cyclic pieces of coprime orders have a stable direct sum, and that sum is cyclic because a pair of generators combines through the Chinese remainder theorem to a generator of order $MN'$.

Quotients can be taken in either order. If $C=C_M\oplus C_{N'}$, then

$$
(E/C_M)/\overline C_{N'}\simeq E/C
\simeq(E/C_{N'})/\overline C_M. \tag{6.6a}
$$

Both composites are quotients by the same subgroup on the dense source, so the universal property identifies them. This commutativity underlies the composition of degeneracy maps and the commuting Atkin--Lehner involutions at squarefree level.

At a characteristic dividing $N$, primary decomposition still makes sense for finite locally free commutative group schemes when the orders are coprime. What fails is the reduction of cyclicity to geometric generators. Each primary factor must satisfy its own Drinfeld divisor condition, and the product divisor must retain ampleness on the chosen generalized elliptic curve.

### 6.6 Fibers of the $j$-map and fixed-source rationality

The cleanest rational-point statement fixes the source elliptic curve. Let $E/K$ be an elliptic curve, assume $\operatorname{char}K\nmid N$, and consider the geometric fiber of

$$
j:Y_0(N)\longrightarrow Y(1) \tag{6.7}
$$

over $j(E)$. Over $K^s$, its points are not literally the cyclic subgroups of $E[N]$; they are their orbits under $\operatorname{Aut}(E_{K^s})$. Indeed, choosing an isomorphism from the source of a represented pair to $E_{K^s}$ identifies its subgroup with one in $E[N]$, and changing that isomorphism applies an automorphism of $E_{K^s}$.

Galois acts on these automorphism orbits. Therefore a $K$-rational coarse point above $j(E)$ is exactly a $G_K$-stable orbit

$$
\operatorname{Aut}(E_{K^s})\cdot C \tag{6.8}
$$

of cyclic order-$N$ subgroups. It is represented by a $K$-rational isogeny with source $E$ exactly when this orbit contains a $G_K$-stable subgroup. This criterion is necessary by taking the kernel. It is sufficient by finite étale descent and Theorem 6.1.

For $j(E)\notin\{0,1728\}$ in characteristic different from $2$ and $3$, the automorphism group is $\{\pm1\}$. Both signs fix every subgroup as a set, so every orbit (6.8) is a singleton. We obtain the promised fixed-source equivalence.

**Theorem 6.3 (fixed-source fiber).** Let $K$ have characteristic prime to $N$, let $E/K$ satisfy $\operatorname{Aut}(E_{K^s})=\{\pm1\}$, and let $x$ be a noncuspidal $K$-point of $Y_0(N)$ with $j(x)=j(E)$. Then there is a unique $G_K$-stable cyclic subgroup $C\subset E[N](K^s)$ representing $x$, and hence a cyclic degree-$N$ isogeny $E\to E/C$ over $K$. Conversely every such isogeny produces such a point.

**Proof.** The point $x$ is a Galois-stable automorphism orbit of cyclic subgroups. Under the hypothesis that the automorphism group is $\{\pm1\}$, the orbit of any subgroup is the singleton consisting of that subgroup. Hence its Galois-stability is ordinary stability of $C$. Finite étale descent constructs the subgroup scheme over $K$, and quotienting constructs the isogeny. The converse sends an isogeny to its kernel pair and then to its coarse point. If two subgroups give the same point, an automorphism $\pm1$ carries one to the other, so they are equal. $\square$

At $j=0$ or $1728$, the theorem is replaced by the orbit criterion (6.8). An automorphism of order $3$, $4$, or $6$ can move one cyclic subgroup to another. A Galois-stable orbit need not have a specified stable member merely by set theory. In a concrete application one resolves the issue in one of three ways: exhibit the subgroup directly, lift the point to the moduli stack, or calculate the finite automorphism orbit and show that it contains a stable subgroup. This is a finite exceptional check, not a reason to weaken the fixed-source theorem away from the exceptional fibers.

The point-level fiber has a parallel but sharper description. Its geometric points above $E$ are automorphism orbits of exact-order points $P\in E[N]$. The sign automorphism sends $P$ to $-P$, so even in the generic automorphism range the orbit has two elements for $N>2$. A rational coarse point of $Y_1(N)$ therefore need not select a rational generator; a $K$-object of the $\Gamma_1(N)$ stack does. This is why rational torsion is best stated with the actual pair $(E,P)$ rather than inferred from the coarse point without checking the sign descent.

### 6.7 The exact rational-point statement

We can now state the endpoint without suppressing its categorical level.

**Theorem 6.4 (rational isogenies and modular points).** Let $K$ be a field with $\operatorname{char}K\nmid N$.

1. Isomorphism classes of $K$-objects of the open stack $\mathcal Y_0(N)$ are exactly isomorphism classes of cyclic separable degree-$N$ isogenies over $K$, where two isogenies are identified by isomorphisms of their sources and targets compatible with the maps.
2. Every such object has a noncuspidal image in $Y_0(N)(K)$.
3. A noncuspidal coarse point $x\in Y_0(N)(K)$ comes from a rational cyclic isogeny if and only if its moduli gerbe is neutral. For a chosen elliptic curve $E/K$ with $j(E)=j(x)$, it has a representative with source $E$ if and only if the automorphism orbit (6.8) contains a $G_K$-stable subgroup. Thus neutrality is equivalent to this condition for at least one $K$-model of the source invariant.
4. If $\operatorname{char}K\ne2,3$ and $j(x)\notin\{0,1728\}$, neutrality is automatic and the rational isogeny can be chosen with any prescribed $K$-model of the source having $j$-invariant $j(x)$.
5. For a fixed elliptic curve $E/K$ and a prime $p\ne\operatorname{char}K$, the existence of the stack object with source $E$, the existence of the rational $p$-isogeny, and reducibility of $E[p]$ over $\mathbf F_p$ are equivalent.

**Proof.** An object $(E,C)$ gives the quotient isogeny $E\to E/C$. Conversely, a cyclic separable isogeny gives $(E,\ker\varphi)$. Formation of quotients and kernels shows that these constructions are inverse up to the stated isomorphisms, proving 1. The coarse map gives 2. Effective descent says that a coarse point has a representing object exactly when its gerbe is neutral, while Section 6.6 gives the fixed-source orbit criterion for each chosen $K$-model, proving 3. The generic automorphism calculation makes every subgroup orbit a singleton and makes twisting by signs harmless, proving 4. Finally, for prime $p$, a cyclic subgroup is an $\mathbf F_p$-line in $E[p](K^s)$; Theorem 6.2 proves 5. $\square$

Thus the familiar slogan has an exact reading:

$$
\boxed{
\begin{array}{c}
E[p]\text{ reducible over }\mathbf F_p\\
\Longleftrightarrow\\
E\text{ has a }K\text{-rational cyclic }p\text{-isogeny}\\
\Longleftrightarrow\\
\text{a }K\text{-object of }\mathcal Y_0(p)\text{ with source }E
\end{array}}
\tag{6.9}
$$

and every line in the box has a noncuspidal image on the coarse curve $Y_0(p)$. The reverse passage from an arbitrary coarse rational point uses the neutrality clause. This is the precise correspondence required in rational-isogeny arguments: it is an equivalence for the actual elliptic curve and its subgroup, with no hidden demand for a rational generator.

### 6.8 Writing quotient isogenies on Weierstrass equations

The quotient construction is intrinsic, but explicit equations are useful for examples. Assume for simplicity that $K$ has characteristic different from $2$ and $3$, write

$$
E:y^2=x^3+Ax+B,
$$

and let $C\subset E(K^s)$ be a finite subgroup stable under $G_K$. For a variable point $P$, define

$$
X(P)=x(P)+\sum_{Q\in C\setminus\{0\}}
\bigl(x(P+Q)-x(Q)\bigr), \tag{6.10}
$$

$$
Y(P)=y(P)+\sum_{Q\in C\setminus\{0\}}
\bigl(y(P+Q)-y(Q)\bigr). \tag{6.11}
$$

These are rational functions on $E$. Translation by $R\in C$ permutes the terms in the full sums over $Q\in C$. The omitted constants merely normalize the functions at the identity. Therefore

$$
X(P+R)=X(P),\qquad Y(P+R)=Y(P). \tag{6.12}
$$

They lie in the invariant subfield $K^s(E)^C$.

The invariant subfield has degree $|C|$ in $K^s(E)$. Indeed, translations by elements of $C$ give $|C|$ distinct automorphisms of the function field, so the fixed-field theorem gives

$$
[K^s(E):K^s(E)^C]=|C|. \tag{6.13}
$$

The functions $X$ and $Y$ have poles only at points of $C$: $X$ has pole order two and $Y$ pole order three on the quotient. Riemann--Roch on the genus-one curve shows that they generate the fixed field and satisfy one Weierstrass relation

$$
Y^2=X^3+A'X+B'. \tag{6.14}
$$

After completing the square and cube, the coefficients are uniquely determined. The map

$$
\varphi_C:E\longrightarrow E',\qquad P\longmapsto(X(P),Y(P)) \tag{6.15}
$$

has function-field degree $|C|$ and is constant exactly on the $C$-orbits, so its kernel is $C$ and $E'$ is the quotient $E/C$.

Why are $A'$ and $B'$ in $K$? Galois permutes the points of the stable subgroup $C$, so it fixes the symmetric sums (6.10)--(6.11). Hence $X,Y\in K(E)$ and their relation has coefficients in $K$. This is an explicit version of quotient descent. A rational generator was never chosen; stability of the whole subgroup is enough.

The dual isogeny can be recovered from the quotient kernel. Since $\varphi_C$ has degree $N$, pullback of divisors shows that multiplication by $N$ factors through it. The induced map $E'\to E$ is $\widehat\varphi_C$, and comparison on function fields proves

$$
\widehat\varphi_C\varphi_C=[N]. \tag{6.16}
$$

Degree gives $\deg\widehat\varphi_C=N$, and its kernel is the image of $E[N]$ in $E'$, namely $E[N]/C$.

In characteristic dividing $N$, the sums over geometric points in (6.10)--(6.11) are not a valid construction for a nonreduced kernel. The quotient still exists scheme-theoretically, but one must use the finite locally free subgroup and its fppf quotient. This is another sharp boundary between convenient equations and the integral moduli problem.

The next chapter specializes these formulas to a rational point of order two, where every term can be simplified by hand. That example will verify both a quotient equation and the $X_0(2)$ parametrization.

## 7. Low-level curves and explicit coordinates

### 7.1 $X(1)$ and the first rational parametrizations

The coarse curve $X(1)$ is $\mathbf P^1$ with coordinate $j$, and the unique cusp is $j=\infty$. A nonconstant map $X_0(N)\to X(1)$ is therefore an explicit rational function once a coordinate on a genus-zero $X_0(N)$ is chosen. Such a formula does three jobs: it produces families of rational isogenies, locates cusps through poles, and displays ramification above the elliptic values $0$ and $1728$.

It does not produce a universal elliptic curve on the coarse $X_0(N)$. Nor does every rational parameter necessarily yield a nonsingular elliptic curve: the parameter values at poles are cusps. The formula classifies coarse isomorphism data on the open locus.

The identification $X(1)\simeq\mathbf P^1_j$ can be seen algebraically. In characteristic different from $2$ and $3$, write an elliptic curve as

$$
y^2=x^3+Ax+B,\qquad 4A^3+27B^2\ne0.
$$

The change $(x,y)=(u^2x',u^3y')$ sends $(A,B)$ to $(u^{-4}A,u^{-6}B)$. The invariant ratio

$$
j=1728\frac{4A^3}{4A^3+27B^2}
$$

classifies geometric isomorphism classes. The missing discriminant-zero orbit becomes $j=\infty$, giving the projective line. Integral generalized Weierstrass equations extend this coarse invariant across characteristics $2$ and $3$, although the stack stabilizers there are larger than this short equation displays.

A rational function $j(t)$ on a genus-zero modular curve is therefore the forgetful map itself. Its degree counts cyclic subgroups on a generic elliptic curve, its zeros and $1728$-points record exceptional automorphism ramification, and its poles record cusps with their widths. These three checks will keep the explicit formulas tied to the moduli problem.

The genus calculation in Chapter 10 is independent of the formulas and proves that the listed low-level curves have genus zero. The coordinates below can also be obtained directly by putting a curve with the required cyclic subgroup into a torsion normal form, forming the quotient, and eliminating the Weierstrass coefficients. Section 7.6 carries out this elimination at level two. At levels three and five we record the resulting invariant formulas and verify their degree, cusp orders, involution, and ramification; these checks identify the normalized modular map once the genus-zero coordinate is fixed.

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

These two levels display the first two ways a genus-zero modular parameter can behave. At level two the subgroup and its generator carry the same rational information. At level three the subgroup can descend while its two generators are exchanged by Galois. The coarse curves can both be projective lines even though their point-level covers encode different fields.

The pole orders also distinguish source from quotient. For $X_0(2)$ they are $1$ and $2$; for $X_0(3)$ they are $1$ and $3$. An Atkin--Lehner involution must exchange those cusps and therefore has the form $c/t$ after the coordinate is normalized. Matching the quotient $j$-function determines $c=2^{12}$ and $3^6$, respectively. Thus the constants in the involutions are fixed by modular normalization rather than an arbitrary choice of Möbius transformation.

### 7.3 $X_0(5)$ and what a formula proves

A standard coordinate on the genus-zero curve $X_0(5)$ gives

$$
j=\frac{(t^2+10t+5)^3}{t},\qquad
w_5(t)=\frac{5^3}{t}. \tag{7.6}
$$

Consequently the quotient $j$-invariant is obtained by substituting $125/t$. The formula displays infinitely many rational $j$-invariants with a rational cyclic $5$-isogeny. It does not say that the kernel has a rational generator, and it does not identify two parameters that may be related by twisting at an exceptional automorphism point without a descent check.

As a worked use, take any $t\in\mathbf Q^\times$ for which the displayed $j$ is neither $0$ nor $1728$. The generic-automorphism criterion of Section 3.4 produces an elliptic curve over $\mathbf Q$ with a rational cyclic subgroup of order $5$. Applying $w_5$ gives its quotient curve. Thus the coordinate, the descent criterion, and duality together produce the actual isogeny, rather than the coordinate formula doing all three jobs by itself.

The two cusps are again $t=0$ and $t=\infty$. The first is a simple pole of $j$, while the second is a pole of order five because the numerator has degree six. This matches the widths $1$ and $5$. The numerator roots are the points above $j=0$; their triple multiplicity records order-three ramification except where an elliptic stabilizer survives. Substitution by $125/t$ exchanges the pole orders and yields the quotient invariant (7.7).

The parameter also separates isogeny from torsion. A rational $t$ produces a rational subgroup after the descent check, but the kernel character may be any character into $\mathbf F_5^\times$. A lift to $X_1(5)$ would choose one of the four generators and is a genuinely stronger rationality condition.

### 7.4 Genus zero does not mean trivial arithmetic

The curves $X_0(2)$, $X_0(3)$, and $X_0(5)$ are rational, but their integral geometry at the level prime still detects connected and dual subgroup directions and supersingular collision. After a prime-to-level branch cover kills automorphisms, the two-component theorem of Section 8.2 applies even at $p=2,3$. What fails without further calculation at those small primes is the identical assertion for the unrigidified coarse surface: wild stabilizers can change its invariant local ring. Their maps to the $j$-line ramify, and their open subsets omit cusps. Genus measures the canonical geometry of the generic fiber; it does not measure the complexity of the moduli problem at bad primes.

Conversely, a high-genus curve can have obvious rational cusps. Positive genus does not remove the boundary. The arithmetic problem is to show that noncuspidal rational points are rare or absent, a task requiring more than the genus calculation alone.

There are therefore two independent axes of complexity. The generic-fiber axis is measured by genus and controls rational parametrization, canonical divisors, and Jacobians. The integral axis is measured by the level at the residue characteristic and controls connected group schemes, component crossings, and quotient singularities. A curve can be simple on one axis and difficult on the other.

This distinction explains the order of the next chapters. We first establish the integral models needed to specialize points, even for genus-zero curves. Only afterward do we calculate genus and explain why global point sets become scarce. Neither analysis substitutes for the other.

### 7.5 Checking the parametrizations and their cusps

The displayed formulas can be audited without appealing to their historical derivation. The first check is degree. For $p=2,3,5$, the rational function $j(t)$ has degrees $3,4,6$, respectively, exactly $p+1$. This is the generic degree of $X_0(p)\to X(1)$. In each case the two poles have orders $1$ and $p$, matching the two cusp widths.

For $p=2$,

$$
j(t)=\frac{(t+16)^3}{t}
$$

has a pole of order one at $t=0$ and, since it behaves like $t^2$ at infinity, a pole of order two at infinity. Under $t\mapsto2^{12}/t$, direct simplification gives

$$
j\left(\frac{2^{12}}t\right)
=\frac{(t+256)^3}{t^2}.
$$

Thus the involution exchanges the order-one and order-two cusps and interchanges source and quotient.

For $p=3$,

$$
j(t)=\frac{(t+27)(t+3)^3}{t}
$$

has pole orders one and three. Substitution of $3^6/t$ gives

$$
j\left(\frac{3^6}t\right)
=\frac{(t+27)(t+243)^3}{t^3}.
$$

The equality follows by factoring

$$
\frac{3^6}{t}+27=\frac{27(t+27)}t,\qquad
\frac{3^6}{t}+3=\frac{3(t+243)}t
$$

and cancelling the total power of $3$ against the denominator $3^6/t$.

For $p=5$, substitution is just as informative:

$$
j\left(\frac{125}t\right)
=\frac{(t^2+250t+3125)^3}{t^5}. \tag{7.7}
$$

Indeed,

$$
\left(\frac{125}t\right)^2
+10\left(\frac{125}t\right)+5
=\frac{5(t^2+250t+3125)}{t^2},
$$

and the factor $5^3=125$ cancels against the transformed denominator. The pole orders are one and five, and $t\mapsto125/t$ exchanges them.

The second check is ramification above $j=0$ and $1728$. Zeros visible in the numerators occur with multiplicity three except for the factors forced by an elliptic point that survives on $X_0(p)$. For instance, on $X_0(3)$ the factor $(t+3)^3$ is a triple zero while $(t+27)$ is simple. This is the algebraic shadow of order-three orbifold ramification. To check the remaining branch points, differentiate $j(t)$ and compare the zero divisor of $dj$ with Riemann--Hurwitz. Since every zero and pole is explicit, the total ramification degree must be $2(p+1)-2$ for a map $\mathbf P^1\to\mathbf P^1$ of degree $p+1$. The visible cusp and elliptic contributions exhaust that number.

The third check is modular, not merely algebraic. At a parameter value $t_0$ away from $0$ and $\infty$, the ordered pair

$$
(j(t_0),j(w_pt_0)) \tag{7.8}
$$

is the source and target invariant of a geometric cyclic $p$-isogeny. The involution identity makes the same pair appear in reverse order at $w_pt_0$. If $t_0\in K$ and the corresponding coarse point is neutral, Theorem 6.4 turns this geometric pair into an isogeny over $K$. Away from $j=0,1728$, neutrality is automatic.

Finally, a parametrization describes twists only after a choice of source model. Given $j(t_0)\in K$, choose an elliptic curve $E/K$ with that invariant. The stable subgroup supplied by Theorem 6.3 determines a quotient. Quadratic twisting $E$ and the quotient by the same character preserves the geometric modular point and yields another isogeny over $K$. Thus a single $t_0$ parametrizes a geometric isogeny class together with its simultaneous twists, not one distinguished Weierstrass equation. This is exactly what a coarse modular curve should remember.

### 7.6 An explicit rational $2$-isogeny family

The level-two case can be derived directly from a Weierstrass equation. Let $K$ have characteristic different from $2$, and suppose $E/K$ has a rational point of order two. Move that point to $(0,0)$ and write

$$
E_{a,b}:y^2=x^3+ax^2+bx,\qquad b(a^2-4b)\ne0. \tag{7.9}
$$

The discriminant condition says that the cubic has no repeated root. The map

$$
\varphi(x,y)=\left(x+a+\frac bx,
y\left(1-\frac b{x^2}\right)\right) \tag{7.10}
$$

extends across the apparent poles to an isogeny

$$
E_{a,b}\longrightarrow
E'_{a,b}:Y^2=X^3-2aX^2+(a^2-4b)X. \tag{7.11}
$$

To verify the equation, put $X=x+a+b/x=y^2/x^2$ and $Y=y(1-b/x^2)$. Substituting $y^2=x(x^2+ax+b)$ and clearing $x^4$ reduces both sides of (7.11) to the same polynomial in $x$. The map has a pole only at $x=0$, where $(0,0)$ and the identity map to the identity of $E'$. Away from those two points, the quadratic equation

$$
x^2+(a-X)x+b=0
$$

shows that a generic target point has two preimages. Hence the map has degree two and kernel $\{O,(0,0)\}$.

The invariants of (7.9) are

$$
c_4=16(a^2-3b),\qquad
\Delta=16b^2(a^2-4b). \tag{7.12}
$$

Therefore

$$
j(E_{a,b})
=256\frac{(a^2-3b)^3}{b^2(a^2-4b)}. \tag{7.13}
$$

Introduce the scale-invariant parameter

$$
t=16\frac{a^2-4b}{b}. \tag{7.14}
$$

Then

$$
t+16=16\frac{a^2-3b}{b},
$$

and (7.13) becomes

$$
j(E_{a,b})=\frac{(t+16)^3}{t}. \tag{7.15}
$$

This derives the $X_0(2)$ formula rather than assuming it. Scaling $x=u^2x'$ and $y=u^3y'$ changes $(a,b)$ to $(a/u^2,b/u^4)$ and leaves $t$ unchanged, as a modular parameter should.

For the quotient (7.11), the same calculation with

$$
a'=-2a,\qquad b'=a^2-4b
$$

gives

$$
t'=16\frac{(a')^2-4b'}{b'}
=\frac{2^{12}}t. \tag{7.16}
$$

Thus the explicit quotient realizes the Atkin--Lehner formula. Applying the construction again yields an isogeny whose composite with $\varphi$ is multiplication by two, up to the evident isomorphism of the twice-quotiented curve with $E$.

The excluded values have the expected modular meaning. The condition $b=0$ makes the displayed point singular, while $a^2-4b=0$ makes the cubic singular. In terms of $t$, these are the two cusps $t=\infty$ and $t=0$. Every other value gives a smooth geometric isogeny. Over a ground field, the parameter produces an actual rational isogeny whenever the corresponding coarse point is neutral; for level two the unique nonzero kernel point makes the fixed-source descent especially transparent.

## 8. Integral models away from and at the level

### 8.1 Good primes

Let $\ell\nmid N$. Over $\mathbf Z_\ell$, the $N$-torsion of an elliptic curve is finite étale. On a fine auxiliary cover, the compactified modular curve is smooth and proper over $\mathbf Z_\ell$, and its boundary is a finite étale relative divisor after the harmless cyclotomic base needed to split cusp fields. On the stack the same smooth proper statement holds without auxiliary rigidification.

For a coarse curve one must account for stabilizers. In characteristics not dividing their orders, the quotient is tame and the resulting coarse curve is smooth after the standard construction. In small characteristics, one should either retain the stack or work upstairs on a rigid cover. The safe good-prime assertion is therefore:

> after adding prime-to-$\ell$ rigidifying level, the compactified level-$N$ curve is smooth proper over $\mathbf Z_\ell$; statements invariant under the finite auxiliary group descend once stabilizers have been checked.

This is enough for reduction of rational points and point counting.

The deformation proof is short. Across a nilpotent thickening in residue characteristic $\ell\nmid N$, the elliptic curve has a one-dimensional smooth deformation space. Its finite étale $N$-torsion and every chosen subgroup or generator lift uniquely, because finite étale schemes are invariant under nilpotent thickening. Thus level introduces no new tangent or obstruction direction. At a cusp, the Tate parameter gives a power-series ring over the unramified coefficient algebra. These two kinds of charts cover the compactification, proving smoothness on the fine cover.

The coarse qualification cannot be omitted. If a tame stabilizer of order $e$ acts on a fine local parameter $t$, it can be linearized and the invariant ring is $k[[t^e]]$, still regular. If the stabilizer order equals the residue characteristic, linearization by averaging fails. The stack remains smooth because smoothness is checked on its atlas, while the coarse invariant ring requires a direct calculation. For reduction arguments that use only the coarse proper point and maps between coarse curves, regularity may be unnecessary; for tangent or formal-immersion arguments, one works on the verified regular chart.

### 8.2 The standard integral $X_0(p)$ model

At the prime $p$ dividing the level, $E[p]$ is not étale. The standard compactified $\Gamma_0(p)$ problem over $\mathbf Z_p$ is nevertheless proper and flat when cyclicity is interpreted by finite locally free subgroup schemes and stable generalized elliptic curves.

To state its local geometry without quotient ambiguity, add a prime-to-$p$ rigidifying branch cover, such as full level $M\ge3$ with $(M,p)=1$, whose compactified unlevelled curve is smooth over the base. The resulting rigidified model is regular and semistable. This assertion is valid also for $p=2$ and $p=3$ after the branch data kill every automorphism; the small-prime difficulty reappears only when one takes an unrigidified coarse quotient. Its geometric special fiber has two smooth principal components meeting transversely at the supersingular points. At a crossing, the strict henselian completed local ring is

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

There is no third ordinary branch. Project a rank-$p$ subgroup $C\subset E[p]$ to the maximal étale quotient. The image has rank either $1$ or $p$. In the first case, $C$ lies in the connected rank-$p$ subgroup and equals $\ker F$. In the second, it maps isomorphically to the étale quotient and is the Verschiebung direction after the Frobenius-twist identification. Primality of $p$ rules out an intermediate rank.

Each direction deforms smoothly. In an ordinary deformation, the connected subgroup is canonical and lifts uniquely. For the étale branch, dualize: its dual kernel is connected on the quotient, so deform the quotient with its canonical connected subgroup and dualize back. This gives one smooth parameter on each branch and explains why the only singular points of the special fiber are the supersingular collisions.

### 8.4 The more delicate $X_1(p)$ model

The $\Gamma_1(p)$ problem asks for a Drinfeld generator, not merely its cyclic subgroup. Over the ordinary special fiber, generators of the étale direction and generators of the connected direction behave very differently. Over the connected direction, several sections can coalesce scheme-theoretically. The forgetful map to $X_0(p)$ is therefore ramified at the level prime and is not a finite étale cover of the two-component model.

Define the normalized compactified $\Gamma_1(p)$ model by taking the generic generator cover of the rigidified $X_0(p)$ curve and normalizing the latter in that finite function-field extension. The base is excellent, so normalization is finite. Hence the new model is proper. Its affine coordinate rings inject into their characteristic-zero generic fibers and are therefore torsion-free over the DVR; torsion-free modules over a DVR are flat. This proves properness and flatness of the normalized Drinfeld model and identifies it with the compactified generator functor by the valuative uniqueness of the level divisor.

One must not infer that its naive coarse model over $\mathbf Z_p$ is regular or semistable from the generic fine-moduli statement. After adjoining suitable cyclotomic ramification, normalizing, and resolving, its component normalizations are Igusa-type curves. Over the ordinary locus the generator cover is an $\mathbf F_p^\times$-torsor. At a supersingular point its normalized parameter has the form $h=u^{p-1}$, so the cover is tamely ramified of index $p-1$ there. The full intersection configuration depends on the level and on whether stack or coarse space is retained.

For the purposes of rational torsion in this book, the justified scope is narrower:

- away from $p$, $X_1(p)$ has smooth proper reduction after ordinary rigidification;
- at $p$, the Drinfeld model is proper and flat;
- specialization of a rational generator is interpreted as a section of a finite locally free subgroup divisor;
- no two-component or unramified semistability claim for $X_1(p)$ is made.

This is enough to distinguish rational torsion from a rational subgroup without importing the full stable-reduction theory of $X_1(p)$.

### 8.5 Exact regularity and semistability scope

The two-component theorem is asserted here for squarefree depth-one $\Gamma_0(p)$ level after a prime-to-$p$ branch cover that kills automorphisms and has smooth unlevelled compactification. It holds on that fine cover at every prime. Removing the auxiliary level passes to a quotient by a finite group. On the stack the quotient retains the correct semistable local structure in smooth charts; on the coarse surface, fixed points may create quotient singularities and a minimal regular model can require resolution.

The theorem is not asserted unchanged for the unrigidified coarse curves at $p=2,3$, for $p^2\mid N$, for $\Gamma_1(p^r)$, or for arbitrary coarse integral models. Properness and flatness survive much more generally than regularity and semistability. Normality is also weaker than regularity: normalizing a coarse model need not resolve its quotient singularities.

These qualifications are not technical debris. Reduction arguments use different properties for different steps:

| Needed conclusion                                      | Sufficient geometric input               |
| ------------------------------------------------------ | ---------------------------------------- |
| a $K$-point extends uniquely over a DVR                | properness and separatedness             |
| a reduction point lies on a well-defined special fiber | a chosen proper integral model           |
| branches meet transversely                             | semistable local equation such as $xy-p$ |
| intersection theory on the surface                     | regularity, or an explicit resolution    |
| smooth specialization and uncomplicated point counts   | smooth proper reduction                  |

Using the weakest sufficient hypothesis keeps the later arguments correct at both good and level primes.

### 8.6 Degeneracy maps and cusps on the special fiber

The two components are not anonymous copies of the lower-level curve. Their modular labels determine the restrictions of both degeneracy maps. Let $X$ be the unlevelled rigidified modular curve in characteristic $p$, and identify the normalizations of the two components with $X$ in the usual Frobenius-twisted manner. Then

$$
\begin{array}{c|cc}
&\pi_1&\pi_2\\ \hline
C_F&\operatorname{id}&F_X\\
C_V&F_X&\operatorname{id}.
\end{array} \tag{8.4}
$$

On $C_F$ the universal subgroup is $\ker F_E$. Forgetting it returns $E$, while quotienting returns $E^{(p)}$. This gives the first row. On $C_V$ write the object as $(E^{(p)},\ker V_E)$. Its source is the Frobenius twist and its quotient is $E$, giving the second row. These equalities hold on the dense ordinary locus. Since all four entries are morphisms between proper separated curves, they extend over the supersingular points and cusps.

The scheme-theoretic degree is essential. Absolute Frobenius is bijective on geometric points over an algebraically closed perfect field, but it has degree $p$ on a smooth curve. Thus each degeneracy map has one degree-one component and one purely inseparable degree-$p$ component in the special fiber, consistent with its generic degree $p+1$.

The two standard cusps lie on different components. The one-gon cusp $(E_q,\mu_p)$ belongs to the connected or Frobenius component. The $p$-gon cusp $(E_{t^p},\langle t\rangle)$ belongs to the component or Verschiebung branch. Neither is a supersingular crossing. Their local formulas are

$$
\begin{array}{c|cc}
&\pi_1^*q&\pi_2^*q\\ \hline
(E_q,\mu_p)&q&q^p\\
(E_{t^p},\langle t\rangle)&t^p&t.
\end{array} \tag{8.5}
$$

Modulo $p$, the maps $q\mapsto q^p$ and $t\mapsto t^p$ are Frobenius, while the other entries are identities. Hence the cusp calculation and the component table are the same theorem viewed in local and global coordinates.

At a supersingular crossing the completed ring is

$$
R[[x,y]]/(xy-p).
$$

The component ideals in the special fiber are $(x)$ and $(y)$. Their local intersection multiplicity is

$$
\operatorname{length}R[[x,y]]/(xy-p,x,y)=1. \tag{8.6}
$$

If the geometric supersingular divisor has degree $s$, then on the fine regular surface

$$
C_F\cdot C_V=s. \tag{8.7}
$$

The full special fiber is the principal divisor $C_F+C_V=\operatorname{div}(p)$. Intersecting it with either component gives zero, so

$$
C_F^2=C_V^2=-s. \tag{8.8}
$$

These equalities belong to the fine regular surface. A stack intersection would include stabilizer weights. A tame coarse quotient of effective order $e$ can turn $xy=p$ into a thick node $XY=p^e$; its minimal regular resolution inserts a chain of $e-1$ rational curves. One must resolve first and only then use the fiber relation on that coarse regular surface.

The Atkin--Lehner involution exchanges the two rows of (8.4), the two cusp rows of (8.5), and the two components in (8.8). This supplies a stringent check on every label. If a proposed model makes both cusps lie on one component, gives Frobenius on both restrictions of one degeneracy map, or assigns unequal self-intersections to the exchanged components without an arithmetic descent reason, it is incompatible with the modular involution.

### 8.7 Why the supersingular equation is $xy=p$

The crossing equation is the decisive local argument, so we record its proof in the form needed here. Let

$$
\phi_0:E_0\longrightarrow E'_0
$$

be the degree-$p$ quotient at a supersingular point over a perfect field $k$. Its kernel and the kernel of its dual are local of rank $p$. Let $R=W(k)$, or the corresponding unramified complete coefficient ring.

A rigidified elliptic curve has a one-parameter deformation space over $R$. The reason is that first-order deformations form $H^1(E_0,T_{E_0})$, a one-dimensional vector space, while obstructions lie in $H^2(E_0,T_{E_0})=0$. Prime-to-$p$ rigidifying level lifts uniquely and removes automorphisms. Thus source and target deformations each have a power-series parameter.

On the deformation space of the isogeny, trivialize the Hodge lines of source and target by invariant differentials $\eta$ and $\eta'$. There are unique functions $x$ and $y$ such that

$$
\phi^*\eta'=x\eta,\qquad
\widehat\phi^*\eta=y\eta'. \tag{8.9}
$$

The dual-isogeny identity forces the relation. Indeed,

$$
(\widehat\phi\phi)^*\eta
=\phi^*(y\eta')=xy\eta,
$$

whereas $\widehat\phi\phi=[p]$ and pullback by $[p]$ multiplies an invariant differential by $p$. Therefore

$$
xy=p. \tag{8.10}
$$

It remains to prove that there is no second relation. This is exactly the supersingular isogeny-deformation theorem established for the prime-level integral model. We recall its decisive coefficient argument so that the imported conclusion and its hypotheses remain visible. Complete the source and target curves at their identities and choose formal parameters $T,T'$ compatible with the differential frames. Strict coordinate changes remove every homogeneous term whose degree is not a power of $p$: the intermediate binomial coefficients $\binom ni$, $0<i<n$, generate the unit ideal in $\mathbf Z_{(p)}$ unless $n$ is a power of $p$. The formal groups and the two maps may therefore be written in $p$-typical coordinates. After unit normalization their leading terms are

$$
f(T)=xT+T^p+\sum_{r\ge2}a_rT^{p^r},\qquad
g(T')=yT'+(T')^p+\sum_{r\ge2}b_r(T')^{p^r}. \tag{8.11}
$$

They must respect the two formal group laws and satisfy

$$
g(f(T))=[p](T). \tag{8.12}
$$

At degree one, (8.12) is precisely $xy=p$. At degree $p$, the two homomorphism identities express the deformation parameters of the source and target formal groups in terms of $x$ and $y$. Inductively at degree $p^r$, order the new unknowns as the source-law coefficient, the coefficient of $f$, the target-law coefficient, and the coefficient of $g$. Modulo the maximal ideal the resulting linear system is triangular. Its diagonal entries are powers of the leading $T^p$ coefficients of the two special isogenies or of the $T^{p^2}$ coefficient of $[p]$ on the supersingular formal group. All are units: the last is exactly the height-two condition. Thus every new coefficient is determined without division by $p$. The composition equation at the next degree has no independent remainder, since its first possible coefficient is killed by the same height-two unit. Induction proves that every higher coefficient of $f$, $g$, and the two deformed formal group laws is determined by $x,y$, and that $xy=p$ is the only relation.

Conversely, over

$$
B=R[[x,y]]/(xy-p),
$$

the same unit-triangular recursion constructs compatible formal group homomorphisms to every infinitesimal order. The deformation theory of a supersingular elliptic curve agrees with that of its height-two formal group: both are formally smooth of dimension one, and the tangent map is the nonzero pairing with the square of an invariant differential. The inverse-function recursion therefore recovers unique source and target elliptic deformations. The series $f$ reduces to a unit times $T^p$, so Weierstrass preparation cuts out a finite locally free kernel of rank $p$. Quotienting the source elliptic curve by this kernel algebraizes the formal homomorphism and produces the target deformation. Thus $B$ represents the isogeny deformation functor. Prime-to-$p$ branch data lift uniquely and eliminate any further quotient by automorphisms, giving

$$
\widehat{\mathcal O}_{\mathscr X,z}\simeq R[[x,y]]/(xy-p). \tag{8.13}
$$

Changing the differential frames rescales $x$ and $y$ by inverse units. Hence the ideals $(x)$ and $(y)$ and the isomorphism class of the ring do not depend on those choices.

Modulo $p$, equation (8.10) becomes $xy=0$. On the branch $x=0$, the pullback of differentials under $\phi$ vanishes and the kernel is Frobenius-like. On $y=0$, the dual pullback vanishes and the original kernel is Verschiebung-like. At $x=y=0$ both directions are local, which is precisely the supersingular collision.

Finally, the total ring is regular. In the regular local ring $R[[x,y]]$, the element $xy-p$ is not in the square of the maximal ideal because its $-p$ term is a regular parameter. The hypersurface therefore has embedding dimension two and dimension two. Its special fiber $k[[x,y]]/(xy)$ is a node, and the two branches meet with length one. This proves every local assertion used in Sections 8.2, 8.6, and 9.3.

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

For a scheme point, (9.1) is literal. For a stack object, the valuative criterion can require a finite extension to eliminate monodromy before the object extends. Its coarse point nevertheless extends over the original valuation ring because the coarse curve is proper. Thus one must distinguish reduction of the coarse point from an integral representative of the level object. Passing to a rigidified finite cover supplies the latter after the indicated extension.

If the special point has residue field larger than $k$, it is not an $R$-section. A $K$-rational point over the original DVR specializes to a $k$-rational point, but after extending $K$ and normalizing $R$ the residue field can enlarge. Cusp labels and supersingular points can then split. All branch statements below are made after specifying the valuation ring on which the section and the chosen fine model coexist.

Compatibility with finite maps is automatic. If $f:\mathscr X\to\mathscr Y$ is a morphism of proper separated $R$-models, then

$$
\operatorname{red}(f(x))=f_k(\operatorname{red}(x)). \tag{9.2a}
$$

This follows by uniqueness of the extension of the generic section. We shall apply it to $j$, the two degeneracy maps, and Atkin--Lehner involutions.

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

### 9.6 Combining several places without overclaiming

A single good place can disprove reducibility, but a collection of places is usually needed to locate a modular point. Let $S$ be a finite set of places of good reduction away from $Np$. For each $v\in S$, let

$$
\mathcal R_v\subset X_0(p)(k_v)
$$

be the residue classes compatible with the prescribed reduction of $E$ and with a Frobenius-stable line. A global isogeny point must lie in the inverse image of every $\mathcal R_v$ under reduction. At a multiplicative place one replaces $\mathcal R_v$ by the compatible cusp orbit. At a place above $p$ one uses the component or crossing data from Section 9.3.

This produces a diagonal constraint

$$
X_0(p)(K)\longrightarrow
\prod_{v\in S}X_0(p)(k_v),\qquad
x\longmapsto(\operatorname{red}_v x)_v. \tag{9.10}
$$

The image lies in $\prod_v\mathcal R_v$. The constraint is rigorous but generally not injective. Several rational points can occupy the same tuple of residue discs, just as several $p$-adic numbers can share finitely many residue classes. To deduce uniqueness, one needs a global mechanism controlling differences of points, typically a Jacobian calculation or a formal-immersion argument.

There is a second limitation. Frobenius splitting at every tested place is necessary for a global invariant line, but finite testing does not prove that one line is preserved by the entire Galois group. Different Frobenius elements can preserve different lines. Even if every sampled characteristic polynomial splits, the subgroup generated by the sampled matrices can act irreducibly. A proof of reducibility needs either the actual subgroup, a structural image theorem, or enough global information to show that all elements preserve one common line.

The common-line issue is elementary in linear algebra. Two diagonalizable matrices in $\operatorname{GL}_2(\mathbf F_p)$ can each have eigenlines but share none. For example, take

$$
A=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
B=\begin{pmatrix}0&1\\1&0\end{pmatrix}
$$

for odd $p$. Each characteristic polynomial splits, but the eigenlines of $A$ are the coordinate axes and those of $B$ are the diagonal lines. The group they generate has no common invariant line. Local splitting tests detect the conjugacy class of one Frobenius element at a time; reducibility is a simultaneous invariant-subspace condition.

Nevertheless, the tests are powerful in the negative direction. If one Frobenius polynomial is irreducible, the representation is irreducible. If a purported $X_1(p)$ point violates $p\mid\#E(k_v)$ at one good place, the purported rational generator cannot exist. If local Tate data force incompatible cusps at two places under a known global involution or rational function, the modular point is excluded. These deductions use only necessity and hence require no injectivity assertion.

The correct workflow is therefore:

1. construct the global modular point from an actual stable subgroup when it exists;
2. record its allowed residue classes at every chosen place;
3. use local calculations to exclude classes;
4. invoke later global geometry only when one needs to prove that the surviving residue data contain at most one rational point.

This separation prevents local evidence from being mistaken for a global rational-point theorem.

### 9.7 Specialization of the kernel character

The kernel character $\psi_C$ refines the statement that a line is stable. At a finite place $v\nmid p$ of good reduction, the finite étale group $E[p]$ extends over the valuation ring and inertia acts trivially. Therefore $\psi_C$ is unramified at $v$, and

$$
\psi_C(\operatorname{Frob}_v)
$$

is one of the roots of $X^2-a_vX+q_v$ modulo $p$. The other root is

$$
q_v\,\psi_C(\operatorname{Frob}_v)^{-1}, \tag{9.11}
$$

in agreement with the cyclotomic determinant. Thus the root test of Section 9.5 is the character equation with the choice of root forgotten.

If $C$ has a rational generator, then $\psi_C=1$. At every good $v\nmid p$, one root of the Frobenius polynomial is therefore $1$, and

$$
1-a_v+q_v\equiv0\pmod p.
$$

Since $1-a_v+q_v=\#E(k_v)$, this recovers (9.9). Conversely, the congruence at one place shows only that Frobenius at that place fixes a nonzero vector; it does not make the global kernel character trivial.

At a split multiplicative place $v\nmid p$, Tate uniformization gives an exact sequence

$$
0\longrightarrow\mu_p
\longrightarrow E[p]
\longrightarrow\mathbf Z/p\mathbf Z
\longrightarrow0. \tag{9.12}
$$

Inertia acts on the multiplicative line through $\overline\chi_p$ and on the quotient trivially. If the extension splits over the relevant field, these give the two obvious stable lines. If it does not split, the quotient need not lift to an actual stable complementary line. The multiplicative line always exists and corresponds to the $\mu_p$ cusp direction; a component-direction line exists precisely when the extension class permits it after the chosen extension. This is why cusp type contains more information than the fact of multiplicative reduction alone.

For a Tate parameter $q$, the extension class is the Kummer class of $q$ in $K_v^\times/(K_v^\times)^p$. If $q$ acquires a $p$th root, the class of that root defines the component line. Quotient by the two directions gives $E_{q^p}$ and $E_{q^{1/p}}$, respectively. The local character and the cusp coordinate are therefore two descriptions of the same Tate extension.

At $v\mid p$, geometric point characters no longer control the integral kernel. Let $\mathcal C$ be the finite flat closure of $C$ in a semistable elliptic model when such a closure is part of the specified modular model. If $\mathcal C_k$ is connected on an ordinary special fiber, the modular section lies on the Frobenius branch; if it is étale, it lies on the Verschiebung branch. The generic character can be studied through this finite flat model, but one must not identify connectedness of the special fiber with a pointwise statement about $C(K_v^s)$. A connected group such as $\mu_p$ has a full generic set of $p$ points in characteristic zero and only one geometric special point.

Duality preserves the local bookkeeping. The dual kernel character is $\overline\chi_p\psi_C^{-1}$. At a good place, it selects the other Frobenius root. At a Tate place, it exchanges multiplicative and component directions. At the level prime, it exchanges connected and étale ordinary closures and hence the two components of the integral model. The same formula is visible in Galois matrices, in finite flat group schemes, and in the Atkin--Lehner involution.

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

There is a second derivation from the Hodge line, which connects the genus calculation to integral modular forms. On a fine torsion-free modular curve, the discriminant gives

$$
\lambda^{12}\simeq\mathcal O(W),
$$

where $W$ is the cusp divisor weighted by widths. Since the widths sum to $\mu$,

$$
\deg\lambda=\frac\mu{12}. \tag{10.2d}
$$

Logarithmic Kodaira--Spencer gives

$$
\lambda^2\simeq\omega_X(D), \tag{10.2e}
$$

where $D$ is the reduced cusp divisor. Taking degrees yields

$$
\frac\mu6=2g-2+c,
$$

which is (10.1) when $e_2=e_3=0$. If elliptic stabilizers remain, the Hodge line lives naturally on the stack. Passing to the coarse curve subtracts the fractional stabilizer contributions $e_2/2$ and $2e_3/3$, recovering the full formula. Thus Riemann--Hurwitz and Hodge theory agree term by term: weighted discriminant gives the index, reduced boundary gives $c$, and stabilizer characters give the elliptic corrections.

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

To justify (10.5), an order-two elliptic point on the upper half-plane is fixed by a conjugate of

$$
S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

A cyclic subgroup is preserved by this automorphism exactly when its line in $(\mathbf Z/N\mathbf Z)^2$ is an eigenline. Writing the line with slope $x$ gives $x^2+1=0$. The same argument for an order-three element gives $x^2+x+1=0$. Hence the congruence counts are stabilizer counts, not accidental formulas.

The Chinese remainder theorem reduces them to prime powers. For an odd prime $q$, a root of either polynomial whose derivative is nonzero modulo $q$ lifts uniquely through all powers of $q$. The exceptional derivatives explain the special conventions at $2$ and $3$: no order-two elliptic point survives when $4\mid N$, and no order-three point survives when $9\mid N$. These local facts, multiplied over the prime factors of $N$, determine $e_2(N)$ and $e_3(N)$ completely.

Substituting the four independently computed quantities into Riemann--Hurwitz proves (10.4). In particular, there is no assumption that the cover is unramified away from cusps: the elliptic correction terms are precisely the missing ramification contributions above $0$ and $1728$.

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

The expression is an integer because the residue class of $p$ modulo $12$ coordinates the two Legendre symbols. Together with direct calculations at $p=2,3$, it gives genus zero for

$$
p=2,3,5,7,13,
$$

and genus one for

$$
p=11,17,19.
$$

Thereafter positive genus is the rule and grows with $p$. These examples explain the transition from rational parametrizations to genuinely global curve arithmetic.

For $X_1(N)$, the same canonical formula (10.2) applies with the index, elliptic stabilizers, and cusp orbits of $\Gamma_1(N)$. For $N\ge5$, its image in $\operatorname{PSL}_2(\mathbf Z)$ is torsion-free, so the elliptic corrections vanish. The growth of the index is quadratic in $N$ up to Euler factors, reflecting how much stronger a chosen generator is than an unoriented cyclic subgroup.

The prime formulas for $e_2$ and $e_3$ follow because a quadratic congruence over $\mathbf F_p$ has $1+(D/p)$ roots when its discriminant $D$ is nonzero. The discriminants are $-4$ and $-3$, giving (10.8). The primes $2$ and $3$ are excluded from this Legendre-symbol calculation because the discriminants vanish or the orbifold orders meet the characteristic. Direct stabilizer counts give

$$
(\mu,c,e_2,e_3)=(3,2,1,0)\text{ for }N=2,
$$

and

$$
(\mu,c,e_2,e_3)=(4,2,0,1)\text{ for }N=3.
$$

Substitution in (10.2) gives genus zero in both cases, independently of the parametrizations in Chapter 7.

The formula also shows why prime genus grows in steps. The main term rises by roughly $p/12$, but the two Legendre symbols periodically subtract $1/2$ or $2/3$. These bounded corrections can change the order of the first few genera but cannot prevent eventual growth.

### 10.4 What genus does and does not prove

Genus zero often permits a rational parameter once a rational cusp is chosen. Genus one replaces parametrization by the arithmetic of an elliptic curve. Genus at least two signals that the canonical bundle is positive and that rational points should be rigid rather than form a one-parameter family.

But genus alone does not classify rational points. A high-genus curve can have many explicitly known cusps, and a canonical-divisor calculation does not exclude isolated noncuspidal points. General finiteness theorems could prove finiteness over number fields, but the final prime-isogeny classification sought later requires an effective and structural argument. It will use the modular Jacobian, reduction, and special quotients rather than appeal to a general finiteness theorem as its decisive step.

This division of labor is important. The present chapter explains why scarcity is geometrically plausible and supplies exact genus data. It does not claim the list of possible prime degrees. That classification belongs after the arithmetic machinery of the next volumes.

When $g=0$ and a rational cusp exists, the curve is isomorphic to $\mathbf P^1$ over the ground field, so noncuspidal rational points form a one-parameter family unless the open conditions remove all rational values. When $g=1$, choosing a rational cusp identifies the curve with an elliptic curve, and rational points form a finitely generated group over a number field. When $g\ge2$, the Abel--Jacobi map places the curve inside a higher-dimensional group but does not turn its points into a subgroup.

These statements explain the appropriate tools but do not execute them. Even in genus one, determining the Mordell--Weil group is additional arithmetic. In genus at least two, a finiteness theorem does not identify the points needed for an isogeny classification. The later modular argument exploits Hecke-stable quotients and special cuspidal classes, which remember far more than the bare genus.

### 10.5 Checked low-level genus data

It is worth carrying out enough cases to verify every correction term. For $p>3$, the congruence $x^2+1=0$ has two solutions when $p\equiv1\pmod4$ and none when $p\equiv3\pmod4$. Likewise $x^2+x+1=0$ has two solutions when $p\equiv1\pmod3$ and none when $p\equiv2\pmod3$. Hence the prime-level genus depends only on $p\bmod12$:

$$
\begin{array}{c|c|c|c}
p\bmod12&e_2&e_3&g(X_0(p))\\ \hline
1&2&2&(p-13)/12\\
5&2&0&(p-5)/12\\
7&0&2&(p-7)/12\\
11&0&0&(p+1)/12.
\end{array} \tag{10.10}
$$

For example, $p=13$ lies in the first row and gives genus zero; $p=17$ lies in the second and gives genus one; $p=19$ lies in the third and gives genus one; $p=23$ lies in the fourth and gives genus two. The next cases are

$$
\begin{array}{c|rrrrrrrr}
p&5&7&11&13&17&19&23&29\\ \hline
g(X_0(p))&0&0&1&0&1&1&2&2,
\end{array}
$$

and

$$
g(X_0(31))=2,\qquad
g(X_0(37))=2,\qquad
g(X_0(41))=3. \tag{10.11}
$$

These values check the apparently nonmonotone occurrence of genus zero at $13$ after genus one at $11$. The elliptic correction at $13$ is unusually large: both order-two and order-three elliptic points survive.

For composite $N$, the congruence descriptions (10.5)--(10.6) are evaluated by the Chinese remainder theorem. At an odd prime power $q^r$, a simple root modulo $q$ lifts uniquely to $q^r$. For the order-two equation there are no roots modulo $4$, so $4\mid N$ forces $e_2(N)=0$. For the order-three equation there are no roots modulo $9$, so $9\mid N$ forces $e_3(N)=0$. At primes $q\nmid6$, the existence of roots is controlled by the quadratic characters of $-1$ and $-3$. Multiplying the local root counts gives the global count.

Consider $N=11$. Here

$$
\mu_0(11)=12,\quad c_\infty(11)=2,\quad e_2=e_3=0,
$$

so

$$
g(X_0(11))=1+1-1=1.
$$

For $N=13$ one has $\mu_0(13)=14$, two cusps, and $e_2=e_3=2$, giving

$$
1+\frac{14}{12}-\frac24-\frac23-1=0.
$$

For a composite comparison take $N=14$. The index is

$$
14\left(1+\frac12\right)\left(1+\frac17\right)=24.
$$

Since $14$ is squarefree, it has four cusps. The congruence $x^2+1=0$ has no solution modulo $7$, and $x^2+x+1=0$ has solutions modulo $7$ but none modulo $2$ in the order-three orbifold calculation compatible with $\Gamma_0(14)$; equivalently the global elliptic counts are zero. Hence

$$
g(X_0(14))=1+\frac{24}{12}-\frac42=1. \tag{10.12}
$$

The cusp number itself also deserves checking. For $N=q^r$,

$$
c_\infty(q^r)
=\sum_{i=0}^r\varphi(q^{\min(i,r-i)}). \tag{10.13}
$$

When $r=1$ this is $2$. When $r=2$ it is $2+\varphi(q)=q+1$. Thus $X_0(q^2)$ has $q+1$ geometric cusps, not merely the two visible fractions $0$ and $\infty$. The intermediate cusps have denominator type $q$ and residue field $\mathbf Q(\zeta_q)$ as a closed orbit. This example ties the genus correction directly to the cusp-field calculation of Section 5.4.

Every number in these examples follows from the same four inputs: index, order-two orbits, order-three orbits, and cusps. No list of genera is being used as an unexplained table.

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

The rationality of $\infty$ is visible in the Tate chart. Its cyclic subgroup is $\mu_N$, defined over $\mathbf Q$ as a group scheme even though its individual generators need not be rational. Since $\Gamma_0$ level forgets a generator, the entire cusp object descends. This is another instance of the difference between $X_0$ and $X_1$.

The choice of base cusp affects the Abel--Jacobi map by translation. Replacing $\infty$ by another rational cusp $c$ changes $[(P)-(\infty)]$ to $[(P)-(c)]$, differing by the fixed cuspidal class $[(c)-(\infty)]$. The canonical Tate normalization makes $\infty$ preferable, but no geometric injectivity statement depends on that choice.

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

For completeness, when $g(X_0(N))>0$ the Abel--Jacobi map is injective on geometric points. If

$$
[(P)-(\infty)]=[(Q)-(\infty)],
$$

then $(P)-(Q)$ is principal. A rational function with this divisor would define a degree-one morphism from $X_0(N)$ to $\mathbf P^1$. Such a morphism is an isomorphism, forcing genus zero. Therefore $P=Q$ when the genus is positive.

The differential is also injective. Dually, it is enough that some regular differential be nonzero at each point $P$. For genus one, every nonzero regular differential is nowhere vanishing. For genus at least two, if all regular differentials vanished at $P$, then $h^0(K_X-P)=h^0(K_X)=g$. Riemann--Roch would give $h^0(P)=2$, producing a degree-one function and again forcing genus zero. Hence the canonical system has no base point. A proper injective immersion of a smooth curve is a closed immersion, proving the assertion.

This geometric injectivity does not make reduction injective on $K$-points after passing through a quotient of the Jacobian. Nor does it identify the image of $X_0(N)(K)$ inside $J_0(N)(K)$. Those are arithmetic questions. The value of the embedding is that differences of curve points become elements of a group, where specialization, finite subgroups, and quotients can be compared.

### 11.5 The exact handoff to modular Jacobians

The passage to the Jacobian uses only data already constructed here. The source curve is proper and geometrically connected. The cusp $\infty$ is rational. Hence $(P)-(\infty)$ is a rational divisor of degree zero for every $P\in X_0(N)(K)$, and its class is a $K$-point of $\operatorname{Pic}^0$. No Hecke action, Néron model, or Mordell--Weil theorem is needed to define this class.

Three later questions are now well posed.

First, what is the kernel of $\iota_\infty$ on rational points or on a residue disc? On a curve of positive genus the map is a geometric embedding over an algebraic closure, but arithmetic quotients of the Jacobian can identify images. Answering this requires the structure of $J_0(N)$ and selected quotients.

Second, how does the divisor class specialize? A proper regular model of the curve sends the two sections to horizontal divisors. Their difference defines a class in the relative Picard functor, and the Néron mapping property compares it with the special fiber of the Jacobian. Component groups and cusp specialization enter here. The integral geometry of Chapters 8 and 9 supplies the source-side data, but the Jacobian-side model is new work.

Third, when does reduction in the Jacobian force equality of points on the curve? A formal-immersion argument compares cotangent maps at the cusp, while a Mordell--Weil or Eisenstein quotient controls the rational Jacobian points. Neither conclusion follows from properness or point counting alone. Section 9.4 deliberately stopped short of injectivity for exactly this reason.

The modular point arising from a reducible Frey representation enters this later machinery with unusually rich local labels: its good-prime Frobenius roots, its multiplicative cusp types, its level-prime component, and its Atkin--Lehner dual. These labels constrain the specialization of its Abel--Jacobi class. The present book has proved that the labels belong to one global point; the next books analyze the group in which its divisor class lives.

This boundary of responsibility prevents a hidden circular argument. We have not used a fact about $J_0(N)$ to construct $X_0(N)$, prove the isogeny dictionary, or calculate the bad fiber. Conversely, later Jacobian arguments may import the complete curve package established here without rebuilding generalized elliptic curves or re-proving the rational-isogeny equivalence.

## 12. The geometric dictionary

### 12.1 From residual reducibility to geometry

We can now state the complete geometric output in a reusable form.

**Theorem 12.1 (geometric reducibility dictionary).** Let $K$ be a number field, $E/K$ an elliptic curve, and $p$ a prime. Then the following are equivalent:

1. $\overline\rho_{E,p}$ is reducible over $\mathbf F_p$;
2. $E[p](K^s)$ contains a $G_K$-stable line;
3. $E[p]$ contains a cyclic finite étale subgroup scheme $C$ of rank $p$ defined over $K$;
4. there is a separable degree-$p$ isogeny $E\to E/C$ defined over $K$;
5. there is a $K$-object of the $\Gamma_0(p)$ moduli stack with underlying elliptic curve $E$.

Any of these data produces a noncuspidal point $x\in X_0(p)(K)$. Conversely, a noncuspidal coarse point produces such data if and only if its moduli gerbe is neutral; this holds in particular if the point lifts to the stack over $K$, if a representative is explicitly given, or, in characteristic different from $2,3$, if its $j$-value is not $0$ or $1728$.

If $C$ is generated geometrically by $P$, the pair lifts to a $K$-object of the $\Gamma_1(p)$ stack exactly when the kernel character is trivial, equivalently $P\in E(K)$. The dual isogeny corresponds to $w_p(x)$, and its kernel character is $\overline\chi_p\psi^{-1}$ when the original kernel character is $\psi$.

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

| Statement                                                         | Exact hypothesis or qualification                                                                                      |
| ----------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| $E[N](K^s)\simeq(\mathbf Z/N\mathbf Z)^2$                         | $\operatorname{char}K\nmid N$                                                                                          |
| stable geometric subgroup $\Leftrightarrow$ subgroup scheme       | finite étale torsion, hence $\operatorname{char}K\nmid N$                                                              |
| stable line $\Leftrightarrow$ rational $p$-isogeny                | $p\ne\operatorname{char}K$ and reducibility over $\mathbf F_p$                                                         |
| $X_0$ versus $X_1$                                                | stable subgroup versus fixed generator                                                                                 |
| coarse $K$-point gives a $K$-object                               | only when its descent gerbe is neutral                                                                                 |
| all $X_0(N)$ cusps rational                                       | true for squarefree $N$, false in general                                                                              |
| good reduction implies interior specialization                    | prime-to-level stable subgroup on a good elliptic model                                                                |
| multiplicative reduction implies a cusp                           | on the stable generalized-elliptic compactification                                                                    |
| two-component fiber at $p$                                        | depth-one $\Gamma_0(p)$ after a prime-to-$p$ branch cover killing automorphisms; valid at small $p$ on that fine cover |
| same fine statement on the unrigidified coarse surface at $p=2,3$ | not automatic; wild invariant rings require a direct calculation                                                       |
| same claim for $X_1(p)$                                           | not asserted; the integral geometry is more ramified                                                                   |
| reduction map is injective                                        | not from properness alone                                                                                              |
| high genus classifies rational points                             | false; it explains scarcity but does not prove the prime-degree list                                                   |

This ledger is as important as the equivalences. Every attractive but false shortcut in the subject results from deleting one of its right-hand entries.

### 12.3 Conclusion

A rational cyclic isogeny is a piece of Galois-stable geometry. Away from the characteristic, its kernel is at once a finite étale subgroup scheme, a cyclic subgroup of geometric torsion, and an invariant line in a two-dimensional residual representation. Remembering only the line produces $\Gamma_0$ level; remembering a vector produces $\Gamma_1$ level. The difference is the kernel character, not a change of terminology.

Modular curves make this correspondence vary. Their stack records families and automorphisms, while their coarse curve provides the proper one-dimensional space on which rational points can be studied. The distinction prevents a field of moduli from being mistaken for a field of definition. In the direction needed for a Frey curve, the ambiguity disappears because the elliptic curve and stable line are already defined before the modular point is formed.

Compactification preserves the arithmetic when the elliptic curve degenerates. Néron polygons, ample level divisors, and Tate parameters turn multiplicative reduction into a cusp with a computable width and rationality field. Properness turns every rational point into a section over a DVR. Away from the level, good reduction yields ordinary point-counting and Frobenius tests. At the level prime, finite-flat subgroup schemes replace geometric point sets, and the semistable rigidified $X_0(p)$ fiber separates Frobenius from Verschiebung until they meet at supersingular points; coarse quotient singularities remain separately visible.

The canonical-divisor calculation explains why these curves change character as the level grows: rational parametrizations at the smallest levels give way to positive genus and geometric rigidity. Yet geometry alone does not provide the final list of prime isogeny degrees. The rational cusp $\infty$ now supplies the Abel--Jacobi map

$$
X_0(p)\longrightarrow J_0(p),\qquad P\longmapsto[(P)-(\infty)],
$$

and every rational reducibility point comes equipped with the reduction data needed to use it. The next stage is arithmetic on that Jacobian. What has been completed here is the exact passage into that stage: residual reducibility has become a rational modular-curve point, duality has become an involution, local behavior has become specialization data, and every hypothesis governing those translations remains visible.
