# Étale Sheaves and Cohomology on Curves

## Contents

1. [From coverings to cohomology](#1-from-coverings-to-cohomology)
   - [The new problem](#11-the-new-problem)
   - [Standing conventions](#12-standing-conventions)
   - [A map of the theory](#13-a-map-of-the-theory)
2. [The small étale site](#2-the-small-étale-site)
   - [Objects, coverings, and refinement](#21-objects-coverings-and-refinement)
   - [Sheaves of sets, groups, and modules](#22-sheaves-of-sets-groups-and-modules)
   - [Representable sheaves and basic examples](#23-representable-sheaves-and-basic-examples)
   - [Why the Zariski site is insufficient](#24-why-the-zariski-site-is-insufficient)
3. [Geometric stalks and exactness](#3-geometric-stalks-and-exactness)
   - [Étale neighborhoods](#31-étale-neighborhoods)
   - [Enough geometric points](#32-enough-geometric-points)
   - [Exactness and sheafification](#33-exactness-and-sheafification)
   - [Strictly henselian local schemes](#34-strictly-henselian-local-schemes)
4. [Lisse and constructible sheaves](#4-lisse-and-constructible-sheaves)
   - [Local systems and monodromy](#41-local-systems-and-monodromy)
   - [Constructibility on a curve](#42-constructibility-on-a-curve)
   - [Extension across missing points](#43-extension-across-missing-points)
   - [Finite and $\ell$-adic terminology](#44-finite-and-ell-adic-terminology)
5. [Global sections and derived cohomology](#5-global-sections-and-derived-cohomology)
   - [The failure of exactness](#51-the-failure-of-exactness)
   - [Injective resolutions and flasque sheaves](#52-injective-resolutions-and-flasque-sheaves)
   - [Čech cohomology and descent data](#53-čech-cohomology-and-descent-data)
   - [Low degrees and acyclic covers](#54-low-degrees-and-acyclic-covers)
6. [The first cohomology group](#6-the-first-cohomology-group)
   - [Torsors and $H^1$](#61-torsors-and-h1)
   - [Extensions and Yoneda classes](#62-extensions-and-yoneda-classes)
   - [Long exact sequences](#63-long-exact-sequences)
   - [Comparison with fundamental-group cohomology](#64-comparison-with-fundamental-group-cohomology)
7. [Images, higher images, and Leray](#7-images-higher-images-and-leray)
   - [Inverse and direct image](#71-inverse-and-direct-image)
   - [Higher direct images](#72-higher-direct-images)
   - [The Leray spectral sequence in low degree](#73-the-leray-spectral-sequence-in-low-degree)
   - [Finite étale maps and trace](#74-finite-étale-maps-and-trace)
8. [Cohomology with compact support](#8-cohomology-with-compact-support)
   - [Extension by zero](#81-extension-by-zero)
   - [Compactification independence](#82-compactification-independence)
   - [Localization and missing points](#83-localization-and-missing-points)
   - [Ordinary versus compactly supported classes](#84-ordinary-versus-compactly-supported-classes)
9. [Kummer theory and first computations](#9-kummer-theory-and-first-computations)
   - [The Kummer sequence](#91-the-kummer-sequence)
   - [Units, divisors, and the Picard group](#92-units-divisors-and-the-picard-group)
   - [Affine and projective lines](#93-affine-and-projective-lines)
   - [Smooth proper curves](#94-smooth-proper-curves)
10. [Dimension and finiteness on curves](#10-dimension-and-finiteness-on-curves)
    - [Cohomological dimension](#101-cohomological-dimension)
    - [Constructibility and finiteness](#102-constructibility-and-finiteness)
    - [A devissage on strata](#103-a-devissage-on-strata)
11. [Base change in families](#11-base-change-in-families)
    - [Proper base change for curves](#111-proper-base-change-for-curves)
    - [Reduction to a strictly henselian trait](#112-reduction-to-a-strictly-henselian-trait)
    - [Smooth base change and local acyclicity](#113-smooth-base-change-and-local-acyclicity)
    - [What the hypotheses prevent](#114-what-the-hypotheses-prevent)
12. [Arithmetic action and Hochschild–Serre](#12-arithmetic-action-and-hochschildserre)
    - [The action on geometric cohomology](#121-the-action-on-geometric-cohomology)
    - [The Hochschild–Serre sequence](#122-the-hochschildserre-sequence)
    - [Arithmetic and geometric Frobenius](#123-arithmetic-and-geometric-frobenius)
13. [Products, classes, and the trace](#13-products-classes-and-the-trace)
    - [Cup products and signs](#131-cup-products-and-signs)
    - [Tate twists and coefficient pairings](#132-tate-twists-and-coefficient-pairings)
    - [Cycle and fundamental classes](#133-cycle-and-fundamental-classes)
    - [The degree-two trace](#134-the-degree-two-trace)
14. [Poincaré duality for proper curves](#14-poincaré-duality-for-proper-curves)
    - [Statement and normalization](#141-statement-and-normalization)
    - [The constant-coefficient calculation](#142-the-constant-coefficient-calculation)
    - [Perfectness for lisse sheaves](#143-perfectness-for-lisse-sheaves)
    - [Consequences and tests](#144-consequences-and-tests)
15. [Open-curve duality and Euler characteristics](#15-open-curve-duality-and-euler-characteristics)
    - [Duality with compact support](#151-duality-with-compact-support)
    - [Boundary terms](#152-boundary-terms)
    - [Euler characteristics](#153-euler-characteristics)
    - [The dimension $2g$](#154-the-dimension-2g)
16. [Finite maps and correspondences](#16-finite-maps-and-correspondences)
    - [Pullback, trace, and projection](#161-pullback-trace-and-projection)
    - [Correspondence variance](#162-correspondence-variance)
    - [Composition and transpose](#163-composition-and-transpose)
    - [Endomorphisms of $H^1$](#164-endomorphisms-of-h1)
17. [From finite coefficients to $\ell$-adic cohomology](#17-from-finite-coefficients-to-ell-adic-cohomology)
    - [Inverse systems and the Milnor sequence](#171-inverse-systems-and-the-milnor-sequence)
    - [Lattices and rational local systems](#172-lattices-and-rational-local-systems)
    - [Integral duality and torsion warnings](#173-integral-duality-and-torsion-warnings)
    - [Continuous Galois representations](#174-continuous-galois-representations)
18. [Semistable curves over a field](#18-semistable-curves-over-a-field)
    - [Nodes, normalization, and the dual graph](#181-nodes-normalization-and-the-dual-graph)
    - [The normalization calculation](#182-the-normalization-calculation)
    - [Arithmetic genus and the lost half of a loop](#183-arithmetic-genus-and-the-lost-half-of-a-loop)
    - [Duality at a node](#184-duality-at-a-node)
    - [Sheaves and correspondences on a nodal curve](#185-sheaves-and-correspondences-on-a-nodal-curve)
19. [Semistable reduction and local Galois action](#19-semistable-reduction-and-local-galois-action)
    - [The trait and its three fibers](#191-the-trait-and-its-three-fibers)
    - [The local calculation at $xy=\pi$](#192-the-local-calculation-at-xypi)
    - [Invariant cycles and monodromy](#193-invariant-cycles-and-monodromy)
    - [Unramified and semistable representations](#194-unramified-and-semistable-representations)
    - [Frobenius, monodromy, and correspondences](#195-frobenius-monodromy-and-correspondences)
20. [The cohomological representation attached to a curve](#20-the-cohomological-representation-attached-to-a-curve)
    - [Construction and functoriality](#201-construction-and-functoriality)
    - [The commuting-action theorem](#202-the-commuting-action-theorem)
    - [Good and semistable places](#203-good-and-semistable-places)
    - [Conclusion](#204-conclusion)

## 1. From coverings to cohomology

### 1.1 The new problem

Finite étale covering theory turns a locally constant finite object into a finite set or module with continuous monodromy. That dictionary is exact as far as it goes, but it records only the fibers of an object and their transport. It does not measure the obstruction to choosing compatible local sections, the ways a torsor can fail to have a global point, or the two-dimensional intersection phenomena that occur on a curve. These are cohomological questions.

The guiding construction is global sections. If $X$ is a scheme and $\mathcal F$ is a sheaf of abelian groups on its small étale site, then

$$
\Gamma(X,\mathcal F)=\mathcal F(X)
$$

is left exact but usually not right exact. Its right derived functors are the étale cohomology groups $H^i_{\mathrm{\acute et}}(X,\mathcal F)$. Degree zero gives global sections; degree one classifies gluing failures such as torsors; degree two receives cup products and, on a smooth proper curve, carries the trace that turns cohomology into a duality theory.

This book develops that theory for curves, where its essential geometry is visible without the full machinery required in higher dimension. Smooth proper curves provide the clean form of the theory; open curves force compact support and residues; semistable curves show exactly how graph cycles, component cohomology, and vanishing cycles fit together. The endpoint is not merely a list of groups. For a smooth proper geometrically connected curve $C$ over a field $k$ and a prime $\ell$ invertible in $k$, we shall construct a finite-dimensional continuous representation

$$
G_k\longrightarrow
\operatorname{GL}\bigl(H^1_{\mathrm{\acute et}}(C_{k^s},\mathbf Q_\ell)\bigr),
$$

equipped with pullbacks, traces, cup products, duality, and actions of algebraic correspondences. At a place where $C$ has good reduction we will prove that this representation is unramified. At a place where $C$ has semistable reduction we will identify its invariant cycles, its nilpotent monodromy, and the component and graph pieces on which every extending correspondence acts. This is precisely the package from which later geometric representations are extracted.

### 1.2 Standing conventions

Schemes are locally noetherian whenever constructibility or finiteness is discussed. A **curve over $k$** is a separated scheme of finite type over $k$, pure of dimension one unless explicitly allowed to have zero-dimensional components. Smooth curves are geometrically regular; a smooth proper curve called geometrically connected remains connected after base change to a separable closure $k^s$. We write $\bar C=C_{k^s}$ and $G_k=\operatorname{Gal}(k^s/k)$.

A positive integer $n$ is **invertible on $X$** when multiplication by $n$ is a unit in every local ring of $X$. If $X$ lies over a field of characteristic $p$, this means $p\nmid n$. A coefficient ring $\Lambda$ is usually $\mathbf Z/n\mathbf Z$, a finite extension of $\mathbf Z/\ell^r\mathbf Z$, $\mathbf Z_\ell$, or $\mathbf Q_\ell$, always with $\ell$ invertible on the schemes under consideration unless stated otherwise. Prime-to-characteristic hypotheses are never implicit.

For $n$ invertible, put $\Lambda(1)=\mu_n$ when $\Lambda=\mathbf Z/n\mathbf Z$. If $\Lambda$ is a finite $\mathbf Z/n\mathbf Z$-algebra, put $\Lambda(1)=\mu_n\otimes_{\mathbf Z/n\mathbf Z}\Lambda$. Define $\Lambda(r)=\Lambda(1)^{\otimes r}$ for $r\geq0$, with negative twists defined by duals. For $\ell$-adic coefficients,

$$
\mathbf Z_\ell(1)=\varprojlim_m\mu_{\ell^m},
\qquad
\mathbf Q_\ell(1)=\mathbf Z_\ell(1)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

Thus arithmetic Frobenius at a finite field acts on $\mathbf Q_\ell(1)$ by $q$, and geometric Frobenius by $q^{-1}$. This convention will control every trace and duality formula below.

Unless variance matters, we abbreviate $H^i_{\mathrm{\acute et}}$ to $H^i$. Ordinary cohomology and compactly supported cohomology $H_c^i$ are kept visibly distinct. A dual $\mathcal F^\vee$ means $\mathcal Hom_\Lambda(\mathcal F,\Lambda)$ and behaves as expected without derived corrections when $\mathcal F$ is lisse finite free.

### 1.3 A map of the theory

The argument has four layers. First comes local-to-global algebra: the small étale site, stalks at geometric points, constructible sheaves, derived global sections, torsors, and higher direct images. Second comes smooth curve geometry: compactification, Kummer theory, finiteness, base change, cycle classes, and the trace in degree two. Third comes duality and representation theory: perfect pairings, Euler characteristics, correspondences, inverse limits, and continuous Galois actions. Fourth comes semistable geometry: normalization, dual graphs, invariant cycles, tame monodromy, and the interaction of specialization with correspondences.

The foundational burden is deliberately separated from the curve calculations. Book 21 constructs derived and continuous cohomology, proves the finiteness and completion statements used here, and supplies the Galois and product formalism. Book 22 proves proper and smooth base change and local acyclicity. Book 23 constructs compact support, trace, purity, and duality, including the dualizing complex of a nodal curve. We recall those results with their hypotheses and normalizations; we do not rebuild their general proofs. Our task is to extract their precise consequences in dimension one, compute the groups and maps, and prove the smooth, open, and semistable curve theorems in the form later arithmetic arguments actually use.

Several tempting shortcuts are unsafe. Cohomology of a lisse sheaf is not always group cohomology of $\pi_1$: that comparison requires an étale $K(\pi,1)$ condition or a range in which the universal pro-étale cover is acyclic. Proper base change and smooth base change solve different problems. An inverse limit of finite cohomology groups can carry a $\varprojlim^1$ correction. A finite correspondence is contravariant on one leg and covariant by trace on the other. We shall make these qualifications part of the construction rather than repairs added at the end.

## 2. The small étale site

### 2.1 Objects, coverings, and refinement

The Zariski topology sees open subsets but cannot locally adjoin a root of an étale polynomial. Covering theory showed that such roots are the natural local coordinates of arithmetic geometry. The small étale site builds them into the notion of neighborhood.

For a scheme $X$, the category $X_{\mathrm{\acute et}}$ has as objects étale morphisms $U\to X$ and as morphisms the $X$-morphisms between them. A family $\{U_i\to U\}$ is a covering when each map is étale and the images jointly cover the underlying topological space of $U$. Because étale maps are open, this is equivalent to joint surjectivity.

Fiber products exist in the site: if $V\to U$ and $W\to U$ are étale, so is $V\times_UW\to X$. Pulling a covering back along any morphism again gives a covering. Composites of coverings are coverings. These facts are the geometric content needed for the sheaf axioms.

The adjective **small** means that objects are étale over the fixed scheme $X$, rather than all schemes mapping to $X$. Finite étale objects form a smaller subsite which is sufficient for finite locally constant sheaves but not for sheaves that change at a divisor. An open immersion is étale, so ordinary Zariski localization remains present.

### 2.2 Sheaves of sets, groups, and modules

A presheaf $\mathcal F$ assigns data $\mathcal F(U)$ contravariantly to every étale $U\to X$. It is a sheaf if, for every covering $\{U_i\to U\}$, the sequence of sets

$$
\mathcal F(U)\longrightarrow\prod_i\mathcal F(U_i)
\rightrightarrows
\prod_{i,j}\mathcal F(U_i\times_UU_j)
$$

is an equalizer. Thus local sections which agree on pairwise overlaps glue uniquely. For groups, abelian groups, rings, or modules the same condition is imposed on underlying sets, and the glued operations are forced by uniqueness.

If $\Lambda$ is a ring, the constant presheaf $U\mapsto\Lambda$ is generally not a sheaf: a disconnected $U$ should admit independently chosen values on its components. Its sheafification is the **constant sheaf** $\underline\Lambda$, whose sections over a sufficiently nice $U$ are locally constant functions $U\to\Lambda$. Confusing the constant presheaf with its sheafification already gives the wrong answer on a disjoint union.

Sheaves of abelian groups on $X_{\mathrm{\acute et}}$ form an abelian category. Kernels are computed objectwise. Cokernels require sheafifying the objectwise quotient, because a section may exist only locally. This asymmetry is the seed of cohomology: surjectivity of sheaves is local surjectivity, not necessarily surjectivity on global sections.

### 2.3 Representable sheaves and basic examples

Any $X$-scheme $Y$ defines a presheaf

$$
h_Y(U)=\operatorname{Hom}_X(U,Y).
$$

Étale descent for morphisms says that $h_Y$ is a sheaf. In particular, an étale cover is recoverable from the sheaf it represents. This is the first assurance that passing to sheaves loses no geometric information.

The structure sheaf is

$$
\mathcal O_X(U)=\Gamma(U,\mathcal O_U).
$$

For an integer $n$ invertible on $X$, the sheaf $\mu_n$ assigns the $n$th roots of unity in $\Gamma(U,\mathcal O_U)^\times$. It is represented by the finite étale group scheme cut out by $T^n-1$. The sheaf $\mathbf G_m$ assigns $\Gamma(U,\mathcal O_U)^\times$; it is represented by the multiplicative group and is not finite.

A quasi-coherent $\mathcal O_X$-module $M$ defines an étale sheaf by $U\mapsto\Gamma(U,M|_U)$. Étale descent makes this a sheaf, but its étale cohomology agrees with its Zariski cohomology. Torsion local systems behave differently: their étale cohomology sees finite covers invisible in the Zariski topology.

### 2.4 Why the Zariski site is insufficient

Let $K$ be a field and $L/K$ a nontrivial finite separable extension. The one-point Zariski space $\operatorname{Spec}K$ has no nontrivial open cover, but $\operatorname{Spec}L\to\operatorname{Spec}K$ is an étale cover. Descent along it records the action of $G_K$.

The Kummer equation gives a more geometric example. If $a\in K^\times$ and $n$ is invertible, the equation $T^n=a$ may have no solution over $K$ or on any Zariski neighborhood, yet it has one after a finite étale extension whenever $a$ is separably solvable. The resulting obstruction is the class of $a$ in

$$
H^1(K,\mu_n)\cong K^\times/(K^\times)^n.
$$

Thus the site is chosen to make the relevant equations locally soluble. It is neither an arbitrary enlargement nor merely a new language for the same open sets.

## 3. Geometric stalks and exactness

### 3.1 Étale neighborhoods

On an ordinary topological space, a stalk tests behavior arbitrarily near a point. A scheme point with residue field $\kappa(x)$ is too coarse for étale localization because separable residue extensions carry monodromy. The correct point is a geometric point $\bar x:\operatorname{Spec}\Omega\to X$ with $\Omega$ separably closed.

An étale neighborhood of $\bar x$ is a pair $(U,\bar u)$ consisting of an étale $U\to X$ and a lift $\bar u:\operatorname{Spec}\Omega\to U$. Pointed refinements form a filtered category. The stalk is

$$
\mathcal F_{\bar x}=\varinjlim_{(U,\bar u)}\mathcal F(U).
$$

Filteredness is decisive: two representatives become comparable after a common pointed refinement, and exactness of filtered colimits of abelian groups will make stalks exact.

Equivalently, the neighborhood system is represented in the limit by the strict localization

$$
X_{(\bar x)}=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{X,\bar x}.
$$

For a sheaf with suitable continuity, the stalk is its section set on this limit. The strict henselization is not usually an object of the small site, but it is the geometric local probe generated by all pointed étale neighborhoods.

### 3.2 Enough geometric points

The central exactness criterion is the analogue of the elementary fact that a continuous function is determined pointwise.

**Theorem.** A morphism $\mathcal F\to\mathcal G$ of étale sheaves of sets on $X$ is an isomorphism if and only if every map on geometric stalks is an isomorphism. A sequence of sheaves of abelian groups is exact if and only if it is exact on every geometric stalk.

**Proof strategy.** A failure of injectivity or local surjectivity is witnessed by a section over some étale $U$. Choose a geometric point where the failure persists, then pass between a stalk statement and a sufficiently small pointed neighborhood.

**Proof.** If two sections of $\mathcal F(U)$ have equal images, their germs agree at every geometric point of $U$. At each point they therefore agree on some étale neighborhood. These neighborhoods cover $U$, and the sheaf uniqueness axiom makes the sections equal. Thus stalkwise injectivity implies injectivity.

For surjectivity, take $s\in\mathcal G(U)$. At each geometric point $\bar u$ of $U$, stalkwise surjectivity gives a germ of $\mathcal F$ mapping to $s_{\bar u}$. By the definition of the filtered colimit, after shrinking to a pointed étale neighborhood $V_{\bar u}\to U$ this germ is represented by a section mapping exactly to $s|_{V_{\bar u}}$. The $V_{\bar u}$ cover $U$, so the map is locally surjective, which is precisely surjectivity as a map of sheaves. Applying these arguments to kernels and cokernels proves the exactness claim. $\square$

Geometric points are therefore **enough points** for the étale topos. Ordinary scheme points do not suffice with a single choice of residue field: different separable embeddings over the same point detect different branches.

### 3.3 Exactness and sheafification

The stalk of a sheafification equals the stalk of the original presheaf. Consequently sheafification of abelian presheaves is exact: an exact sequence can be checked after taking stalks, where filtered colimits are exact. This fact explains why cokernels in sheaves remain manageable even though they are not computed objectwise.

For a short exact sequence

$$
0\longrightarrow\mathcal F'\longrightarrow\mathcal F
\longrightarrow\mathcal F''\longrightarrow0,
$$

the last arrow says that a section of $\mathcal F''$ lifts **étale locally**. It need not lift globally. The incompatibility of local lifts on overlaps will become its connecting class in $H^1(X,\mathcal F')$.

A useful counterexample is the Kummer map $\mathbf G_m\xrightarrow{n}\mathbf G_m$. When $n$ is invertible, it is surjective as a map of étale sheaves because an invertible function acquires an $n$th root after an étale cover. It is generally not surjective on sections over $X$. This is exactly why the Kummer sequence is short exact as sheaves and cohomologically nontrivial globally.

### 3.4 Strictly henselian local schemes

Let $S=\operatorname{Spec}R$ with $R$ strictly henselian local and closed geometric point $\bar s$. Every finite étale cover of $S$ splits, so every lisse finite sheaf is constant. More generally, for any étale sheaf $\mathcal F$, its stalk $\mathcal F_{\bar s}$ captures sections after allowing all pointed étale neighborhoods.

This local simplicity is the engine behind base-change arguments. A theorem asserting that a constructible complex has the same cohomology before and after specializing can be tested on strict henselizations. The geometry has not disappeared: it has been concentrated into how the generic fiber meets a strictly henselian trait.

In fact the terminal object of the small étale site of $S$ is projective: any étale covering of $S$ has a member meeting the closed point, and strict henselianity gives that member a section. A locally lifted global section can therefore be pulled back along this section to a global lift. Thus global sections are exact and

$$
H^q(S,\mathcal F)=0\qquad(q>0)
$$

for every abelian étale sheaf $\mathcal F$. This does not say that the étale topos is merely the category of sets—sheaves can still distinguish the generic open—but it makes strict local schemes cohomologically acyclic for global sections.

## 4. Lisse and constructible sheaves

### 4.1 Local systems and monodromy

Book 19 identified finite locally constant sheaves on a connected locally noetherian $X$ with finite continuous modules for $\pi_1(X,\bar x)$. We retain the left-monodromy convention. For a finite ring $\Lambda$, a **lisse $\Lambda$-sheaf** is a locally constant sheaf whose stalk is a finite $\Lambda$-module; it is lisse free of rank $r$ when its stalk is free of rank $r$.

Thus a lisse free sheaf corresponds, after a basepoint choice, to

$$
\rho:\pi_1(X,\bar x)\longrightarrow\operatorname{GL}_r(\Lambda)
$$

with open kernel. Tensor products and finite-free duals match the corresponding operations on representations. If $\Lambda=\mathbf Z/n\mathbf Z$, the cyclotomic local system $\Lambda(1)=\mu_n$ need not be constant over the arithmetic scheme, though it becomes constant after adjoining the relevant roots of unity.

Local constancy is stronger than having isomorphic stalks. A sheaf can have stalks of the same cardinality while its transition maps degenerate near a closed point. The lisse condition includes coherent local trivializations, and therefore controlled monodromy.

### 4.2 Constructibility on a curve

Lisse sheaves cannot model data which are locally constant away from finitely many bad points and change there. Constructibility solves this problem by allowing finitely many strata.

A sheaf $\mathcal F$ of finite $\Lambda$-modules on a noetherian scheme $X$ is **constructible** if $X$ admits a finite partition into locally closed subschemes $X=\coprod X_\alpha$ such that $\mathcal F|_{X_\alpha}$ is lisse. On a noetherian curve, after separating generic points of components and finitely many closed points, this says simply: there is a dense open $j:U\hookrightarrow X$ on which $\mathcal F$ is lisse, and the remaining stalks are finite.

This formulation is powerful because it supports induction. Put $i:Z=X\setminus U\hookrightarrow X$. There is a natural exact sequence

$$
0\longrightarrow j_!j^*\mathcal F
\longrightarrow\mathcal F
\longrightarrow i_*i^*\mathcal F
\longrightarrow0
$$

This is exact without an extra extension hypothesis. On a geometric stalk the first map is the identity over $U$ and zero over $Z$, while the last map is zero over $U$ and the identity over $Z$. Cohomology of $\mathcal F$ is thereby separated into a lisse open part and finite skyscraper terms.

### 4.3 Extension across missing points

Let $j:U\hookrightarrow C$ be a dense open immersion of a normal connected curve and let $\mathcal L$ be lisse on $U$. Three extensions answer different questions.

The direct image $j_*\mathcal L$ has stalk at a geometric boundary point $\bar x$

$$
(j_*\mathcal L)_{\bar x}\cong
\mathcal L_{\bar\eta}^{I_x},
$$

where $I_x$ is the local inertia group after choosing a geometric generic point and a branch. Thus $j_*$ retains sections which extend invariantly around the puncture. The extension by zero $j_!\mathcal L$ has zero stalk at $x$ and remembers that support must remain inside $U$. The intermediate behavior between them is measured by the quotient of inertia invariants appearing at the boundary.

For example, a nontrivial Kummer local system on $\mathbf G_m$ may have no inertia invariants at $0$ or $\infty$, so $j_*\mathcal L$ already has zero boundary stalks. A constant sheaf has full invariants, and $j_!\Lambda\to j_*\Lambda$ has a copy of $\Lambda$ at every missing geometric point. These examples explain why compact support cannot be defined by ordinary direct image.

### 4.4 Finite and $\ell$-adic terminology

An $\ell$-adic sheaf is not literally a sheaf of abstract $\mathbf Z_\ell$-modules obtained by forgetting topology. The safe starting object is an inverse system

$$
\mathcal L=(\mathcal L_m)_{m\geq1},
\qquad
\mathcal L_m\text{ lisse over }\mathbf Z/\ell^m\mathbf Z,
$$

with compatible identifications

$$
\mathcal L_{m+1}/\ell^m\mathcal L_{m+1}\cong\mathcal L_m.
$$

It is a lisse $\mathbf Z_\ell$-sheaf of rank $r$ if its stalk system is isomorphic to $(\mathbf Z/\ell^m\mathbf Z)^r$. Equivalently it gives a continuous representation on a finite free $\mathbf Z_\ell$-module. A lisse $\mathbf Q_\ell$-sheaf is obtained by inverting $\ell$ in such a lattice locally; different lattices can yield the same rational local system.

Constructible $\ell$-adic complexes require compatible finite-level constructibility and boundedness. We shall construct the needed groups by inverse limits and state the topology and $\varprojlim^1$ conditions explicitly rather than treating $\mathbf Z_\ell$ as a finite discrete coefficient ring.

## 5. Global sections and derived cohomology

### 5.1 The failure of exactness

Global sections preserve kernels because a global section satisfying a local equation satisfies it globally. They do not preserve cokernels because local lifts may disagree. Thus

$$
\Gamma(X,-):\operatorname{Sh}(X_{\mathrm{\acute et}},\mathbf{Ab})
\longrightarrow\mathbf{Ab}
$$

is left exact. Its right derived functors are defined by

$$
H^i(X,\mathcal F)=R^i\Gamma(X,\mathcal F).
$$

Before using this definition, one should know what problem the derived functor solves. It replaces $\mathcal F$ by a resolution whose terms have enough globally liftable sections, applies $\Gamma$, and records the failure of exactness as the cohomology of the resulting complex.

### 5.2 Injective resolutions and flasque sheaves

The category of étale sheaves of abelian groups has enough injectives. Choose an exact complex

$$
0\longrightarrow\mathcal F\longrightarrow I^0
\longrightarrow I^1\longrightarrow I^2\longrightarrow\cdots
$$

with every $I^q$ injective and set

$$
H^i(X,\mathcal F)=H^i\bigl(\Gamma(X,I^\bullet)\bigr).
$$

Any two injective resolutions are homotopy equivalent in a way unique up to homotopy, so the groups and all induced maps are canonical.

A sheaf is **flasque** if every restriction map along an inclusion-like localization is surjective in the relevant site-theoretic sense. Injective sheaves are flasque and flasque sheaves are acyclic for global sections. Godement-type resolutions built from products of geometric stalks provide another concrete acyclic resolution. Their use clarifies why enough points matter: one embeds a sheaf into a product of skyscraper sheaves whose sections can be extended independently.

The abstract resolution is not an excuse to hide geometry. It guarantees existence and functoriality; computations still come from covers, localization, and special geometric acyclicity.

### 5.3 Čech cohomology and descent data

For an étale covering $\mathfrak U=\{U_a\to X\}$, form the multiple intersections

$$
U_{a_0\cdots a_p}=U_{a_0}\times_X\cdots\times_XU_{a_p}.
$$

The alternating restriction maps define the Čech complex

$$
\check C^p(\mathfrak U,\mathcal F)=
\prod_{a_0,\ldots,a_p}\mathcal F(U_{a_0\cdots a_p}).
$$

Its degree-zero kernel is $\Gamma(X,\mathcal F)$. A degree-one cocycle is a family $g_{ab}$ on pairwise overlaps satisfying $g_{bc}-g_{ac}+g_{ab}=0$ on triple overlaps; coboundaries change local trivializations. This is exactly descent data.

There is always a natural map $\check H^i(\mathfrak U,\mathcal F)\to H^i(X,\mathcal F)$, and after taking the filtered colimit over covers it is an isomorphism in degree one for abelian sheaves. In higher degree one needs acyclicity conditions or hypercovers; one cannot simply decree that a single Čech complex computes all derived cohomology.

### 5.4 Low degrees and acyclic covers

If every finite intersection $U_{a_0\cdots a_p}$ has $H^q(-,\mathcal F)=0$ for $q>0$, the Čech-to-derived spectral sequence

$$
E_1^{p,q}=
\prod_{a_0,\ldots,a_p}H^q(U_{a_0\cdots a_p},\mathcal F)
\Longrightarrow H^{p+q}(X,\mathcal F)
$$

collapses and the cover computes cohomology. This criterion is often more useful than an unconditional comparison theorem.

For a finite Galois étale cover $Y\to X$ with group $G$ that trivializes a lisse sheaf $\mathcal L$, the Čech nerve has components indexed by powers of $G$. If the higher cohomology of the pulled-back sheaf on $Y$ vanishes in the degrees considered, the Čech complex becomes the continuous group-cochain complex. Without that acyclicity, a spectral sequence remains and group cohomology alone misses geometric classes on $Y$.

## 6. The first cohomology group

### 6.1 Torsors and $H^1$

Degree one has a geometric meaning independent of resolutions. Let $\mathcal A$ be a sheaf of abelian groups. An $\mathcal A$-torsor is a sheaf $P$ with an $\mathcal A$-action which is locally nonempty and for which

$$
\mathcal A\times P\longrightarrow P\times P,
\qquad (a,p)\longmapsto(a+p,p),
$$

is an isomorphism. Locally, choosing a point identifies $P$ with $\mathcal A$; globally there may be no preferred origin.

**Theorem.** Isomorphism classes of $\mathcal A$-torsors form an abelian group canonically isomorphic to $H^1(X,\mathcal A)$.

**Proof strategy.** Trivialize a torsor on a cover and compare chosen origins on overlaps. Conversely glue local copies of $\mathcal A$ using a cocycle.

Choose $p_a\in P(U_a)$. On $U_a\times_XU_b$ there is a unique $g_{ab}\in\mathcal A$ with $p_a=g_{ab}+p_b$. Associativity gives $g_{ab}+g_{bc}=g_{ac}$. Replacing $p_a$ by $h_a+p_a$ changes $g$ by the Čech coboundary $h_a-h_b$. Thus the torsor determines a class in $H^1$. Conversely a cocycle uses translations by $g_{ab}$ to glue the sheaves $\mathcal A|_{U_a}$; the cocycle identity is precisely the compatibility on triple overlaps. Refinement makes the constructions independent of the chosen cover. The contracted product of torsors supplies the group law. $\square$

For nonabelian $\mathcal G$, the same construction yields a pointed set $H^1(X,\mathcal G)$ rather than an abelian group. The order of factors in the cocycle matters. We use the abelian theory unless explicitly stated.

### 6.2 Extensions and Yoneda classes

Another appearance of degree one is algebraic. In the abelian category of étale sheaves of $\Lambda$-modules,

$$
\operatorname{Ext}^1(\underline\Lambda,\mathcal F)
$$

classifies short exact sequences

$$
0\longrightarrow\mathcal F\longrightarrow\mathcal E
\longrightarrow\underline\Lambda\longrightarrow0
$$

up to the usual equivalence. Since $\Gamma(X,\mathcal F)=\operatorname{Hom}(\underline\Lambda,\mathcal F)$, derived functors give

$$
\operatorname{Ext}^1(\underline\Lambda,\mathcal F)
\cong H^1(X,\mathcal F).
$$

Concretely, send an extension to the torsor of lifts of $1\in\Lambda$.

The point is not that every class is mysteriously an extension. A local lift of $1$ supplies a local splitting; differences of splittings are sections of $\mathcal F$ and form exactly the cocycle of the torsor. The Baer sum of extensions matches addition in cohomology.

For a lisse sheaf, an extension can remain lisse or acquire singularities depending on the category in which Ext is taken. Ext in all constructible sheaves permits boundary behavior that Ext in lisse sheaves forbids. This distinction is essential on an open curve.

### 6.3 Long exact sequences

Given

$$
0\longrightarrow\mathcal F'
\longrightarrow\mathcal F
\longrightarrow\mathcal F''\longrightarrow0,
$$

injective resolutions yield the long exact sequence

$$
0\to H^0(X,\mathcal F')\to H^0(X,\mathcal F)
\to H^0(X,\mathcal F'')
\xrightarrow{\delta}H^1(X,\mathcal F')\to\cdots.
$$

The boundary $\delta$ is concrete. For $s\in\mathcal F''(X)$, the sheaf of lifts of $s$ to $\mathcal F$ is an $\mathcal F'$-torsor; its class is $\delta(s)$. Hence $s$ lifts globally exactly when $\delta(s)=0$.

At the next stage, a class in $H^1(X,\mathcal F'')$ lifts to an $\mathcal F$-torsor precisely when its obstruction in $H^2(X,\mathcal F')$ vanishes. Naturality follows either from maps of resolutions or by mapping torsors and their lift gerbes. This interpretation will make the Kummer and localization sequences readable rather than formal strings.

### 6.4 Comparison with fundamental-group cohomology

Let $X$ be connected with geometric point $\bar x$, and let $\mathcal L$ be the lisse sheaf associated with a finite continuous $\pi_1(X,\bar x)$-module $M$. There is a canonical comparison

$$
H^i_{\mathrm{cts}}(\pi_1(X,\bar x),M)
\longrightarrow H^i(X,\mathcal L).
$$

It is an isomorphism for $i=0$ and $i=1$. Degree zero is the monodromy dictionary. In degree one, both sides classify $M$-torsors which become trivial on a finite étale cover: a torsor under a finite lisse sheaf is itself finite étale over $X$, and its descent cocycle is a continuous crossed homomorphism.

Higher degrees require more. There is a Cartan--Leray spectral sequence for a pro-cover playing the role of a universal étale cover,

$$
H^p_{\mathrm{cts}}\bigl(\pi_1(X),H^q(\widetilde X,\mathcal L)\bigr)
\Longrightarrow H^{p+q}(X,\mathcal L).
$$

If $\widetilde X$ is acyclic for the relevant finite coefficients, $X$ is an étale $K(\pi,1)$ and the comparison is an isomorphism in all degrees. Smooth affine curves over an algebraically closed field have this property for finite coefficients prime to the characteristic. Proper curves do not: $\mathbf P^1_{\bar k}$ has trivial fundamental group but $H^2(\mathbf P^1_{\bar k},\mu_n)\cong\mathbf Z/n\mathbf Z$. This is the decisive counterexample to an unrestricted comparison.

For $X=\operatorname{Spec}K$, the small étale topos is the classifying topos of $G_K$, so

$$
H^i(X,\mathcal L)=H^i_{\mathrm{cts}}(G_K,M)
$$

in every degree for discrete torsion coefficients. This is the exact bridge to continuous Galois cohomology developed earlier.

## 7. Images, higher images, and Leray

### 7.1 Inverse and direct image

A morphism $f:X\to Y$ must relate local data on the two sites. The inverse image $f^*$ pulls a sheaf on $Y$ to one on $X$ and is exact for sheaves of abelian groups on étale sites. For a representable sheaf it agrees with geometric base change. The direct image is

$$
(f_*\mathcal F)(V)=\mathcal F(V\times_YX)
$$

for étale $V\to Y$. It is right adjoint to $f^*$ and therefore left exact.

At a geometric point $\bar y$ the stalk of $f_*\mathcal F$ is not generally the cohomology of the geometric fiber. It is a colimit over étale neighborhoods of $\bar y$ of sections on their pullbacks. A properness or base-change theorem is needed to identify this local limit with fiber cohomology.

For an open immersion $j$, $j_*$ keeps sections on punctured neighborhoods. For a closed immersion $i$, $i_*$ is exact and simply regards a sheaf on the closed subscheme as one supported there. These two operations form the localization formalism used on curves.

### 7.2 Higher direct images

Because $f_*$ is left exact, define

$$
R^qf_*\mathcal F
$$

as its right derived functors. These are sheaves on $Y_{\mathrm{\acute et}}$. Their value is local cohomological variation in the family $f$: under suitable hypotheses,

$$
(R^qf_*\mathcal F)_{\bar y}\cong
H^q(X_{\bar y},\mathcal F|_{X_{\bar y}}).
$$

The displayed formula is a theorem, not the definition. Without properness, cohomology can escape to infinity; without local acyclicity, vanishing cycles can appear under specialization.

When $f$ is finite, it is affine and its geometric fibers are finite schemes. If $f$ is finite, then $f_*$ is exact on étale sheaves: locally over an étale $V$, the finite $V$-scheme $X_V$ decomposes into a finite collection of local pieces after strict localization, and products over a finite set preserve exactness. Hence

$$
R^qf_*=0\qquad(q>0)
$$

for finite $f$. This simple vanishing will make finite maps exceptionally well behaved.

### 7.3 The Leray spectral sequence in low degree

The equality $\Gamma(X,\mathcal F)=\Gamma(Y,f_*\mathcal F)$ is a composite of left exact functors. The resulting Grothendieck spectral sequence is

$$
E_2^{p,q}=H^p(Y,R^qf_*\mathcal F)
\Longrightarrow H^{p+q}(X,\mathcal F).
$$

Its low-degree edge gives the five-term exact sequence

$$
0\to H^1(Y,f_*\mathcal F)
\to H^1(X,\mathcal F)
\to H^0(Y,R^1f_*\mathcal F)
\to H^2(Y,f_*\mathcal F)
\to H^2(X,\mathcal F).
$$

The middle map restricts a global class to every local fiber. Its image consists of fiber classes that vary as a global section and whose transgression vanishes. This interpretation is often more useful than the entire spectral sequence.

For the structure map $X\to\operatorname{Spec}k$, after base change to $k^s$ the Leray sequence becomes Hochschild--Serre. For a finite morphism, the vanishing of higher direct images reduces Leray to

$$
H^i(X,\mathcal F)\cong H^i(Y,f_*\mathcal F).
$$

### 7.4 Finite étale maps and trace

Let $f:Y\to X$ be finite étale of constant degree $d$. For a sheaf $\mathcal F$ of $\Lambda$-modules on $X$, the stalk of $f_*f^*\mathcal F$ is the direct sum of one copy of $\mathcal F_{\bar x}$ for each point of $Y_{\bar x}$. Summing coordinates defines the trace

$$
\operatorname{Tr}_f:f_*f^*\mathcal F\longrightarrow\mathcal F.
$$

The unit $\mathcal F\to f_*f^*\mathcal F$ is the diagonal. Their composite is multiplication by $d$. Passing to cohomology gives restriction and corestriction,

$$
f^*:H^i(X,\mathcal F)\to H^i(Y,f^*\mathcal F),
\qquad
f_*:H^i(Y,f^*\mathcal F)\to H^i(X,\mathcal F),
$$

with $f_*f^*=d$. If $f$ is Galois with group $G$, then $f^*f_*=\sum_{g\in G}g^*$.

For a finite étale map between connected curves, this trace agrees under the degree-one fundamental-group comparison with group-cohomological corestriction. Transitivity follows by summing sheets in stages. The projection formula

$$
f_*(f^*a\smile b)=a\smile f_*b
$$

will later fix the correct action of correspondences.

Trace also commutes with base change. In a Cartesian square

$$
\begin{array}{ccc}
Y'&\xrightarrow{g'}&Y\\
\downarrow f'&&\downarrow f\\
X'&\xrightarrow{g}&X
\end{array}
$$

with $f$ finite étale, the geometric fibers of $f'$ are the pulled-back fibers of $f$, so summing their coordinates gives

$$
g^*\operatorname{Tr}_f
=\operatorname{Tr}_{f'}g'^*.
$$

Consequently restriction and corestriction commute with arbitrary extension of the base scheme. This finite étale base-change statement requires no proper-base-change theorem; it follows directly from the definition on stalks.

## 8. Cohomology with compact support

### 8.1 Extension by zero

An open curve has classes whose behavior at missing points matters. Ordinary cohomology permits support to approach the boundary. Compactly supported cohomology must exclude it.

For an open immersion $j:U\hookrightarrow X$, the extension by zero $j_!\mathcal F$ is left adjoint to $j^*$ and has stalks

$$
(j_!\mathcal F)_{\bar x}=
\begin{cases}
\mathcal F_{\bar x},&\bar x\in U,\\
0,&\bar x\notin U.
\end{cases}
$$

It is exact for sheaves of abelian groups. If $X$ is proper over $k$, define

$$
H_c^i(U,\mathcal F)=H^i(X,j_!\mathcal F).
$$

The definition encodes support through a sheaf operation rather than through a topological compactness notion, which would behave poorly over nonarchimedean fields.

### 8.2 Compactification independence

For a separated curve $U$ of finite type over $k$, a compactification $j:U\hookrightarrow\bar U$ exists with $\bar U$ proper; for a smooth curve one may take the unique smooth proper model after normalizing and resolving the one-dimensional singularities. The group $H^i(\bar U,j_!\mathcal F)$ is independent of this choice.

**Proof strategy.** Compare two compactifications using the closure of the diagonal in their product, then pass to a proper scheme dominating both. Proper pushforward preserves extension by zero along the common open.

Concretely, if $p:\bar U'\to\bar U$ is proper and is the identity over $U$, then sections of $j'_!\mathcal F$ over a geometric neighborhood sum to zero off $U$, and properness prevents additional support from escaping. One gets

$$
Rp_*j'_!\mathcal F\cong j_!\mathcal F.
$$

Proper base change, proved below in the finite-coefficient curve setting, identifies the stalks at boundary points and completes the comparison. Thus $H_c^i$ is intrinsic, although a compactification is a useful computational device.

### 8.3 Localization and missing points

Let $j:U\hookrightarrow C$ be open with closed complement $i:Z\hookrightarrow C$. There is a short exact sequence

$$
0\longrightarrow j_!j^*\mathcal F
\longrightarrow\mathcal F
\longrightarrow i_*i^*\mathcal F
\longrightarrow0
$$

when $\mathcal F$ has the evident extension behavior, and more generally the localization triangle gives the same long exact formalism. For a sheaf $\mathcal F$ on $C$ it yields

$$
\cdots\to H_c^r(U,j^*\mathcal F)
\to H^r(C,\mathcal F)
\to H^r(Z,i^*\mathcal F)
\to H_c^{r+1}(U,j^*\mathcal F)\to\cdots.
$$

When $k$ is separably closed, $Z$ is a finite collection of points and a finite sheaf on $Z$ has only degree-zero cohomology. For a connected proper curve and constant $\Lambda$ this gives

$$
0\to H_c^0(U,\Lambda)\to\Lambda
\xrightarrow{\Delta}\Lambda^{Z}
\to H_c^1(U,\Lambda)
\to H^1(C,\Lambda)\to0
$$

and $H_c^2(U,\Lambda)\cong H^2(C,\Lambda)$. If $U\ne C$ is connected, $H_c^0(U,\Lambda)=0$ and the boundary contributes $|Z|-1$ new degree-one classes.

### 8.4 Ordinary versus compactly supported classes

Derived adjunction gives a natural map $j_!\mathcal F\to Rj_*\mathcal F$ and hence

$$
H_c^i(U,\mathcal F)\longrightarrow H^i(U,\mathcal F).
$$

It is seldom an isomorphism on an open curve. For $U=\mathbf A^1_{\bar k}$ and prime-to-characteristic $\Lambda$, ordinary cohomology has $H^0=\Lambda$ and no positive-degree classes, while compactly supported cohomology has $H_c^2=\Lambda(-1)$ and no other groups. Compact support moves the fundamental class into view.

For $\mathbf G_m$, ordinary cohomology is

$$
H^0(\mathbf G_m,\Lambda)=\Lambda,
\qquad H^1(\mathbf G_m,\Lambda)=\Lambda(-1),
$$

where the twist is visible over nonclosed ground fields. Compactly supported cohomology is

$$
H_c^1(\mathbf G_m,\Lambda)=\Lambda,
\qquad H_c^2(\mathbf G_m,\Lambda)=\Lambda(-1).
$$

These groups will pair across complementary degrees.

## 9. Kummer theory and first computations

### 9.1 The Kummer sequence

Assume $n$ is invertible on $X$. Étale locally every unit has an $n$th root, so the sequence

$$
1\longrightarrow\mu_n\longrightarrow\mathbf G_m
\xrightarrow{n}\mathbf G_m\longrightarrow1
$$

is exact on $X_{\mathrm{\acute et}}$. Its long exact sequence begins

$$
\Gamma(X,\mathcal O_X^\times)\xrightarrow{n}
\Gamma(X,\mathcal O_X^\times)
\to H^1(X,\mu_n)
\to H^1(X,\mathbf G_m)\xrightarrow{n}\cdots.
$$

Line bundles are $\mathbf G_m$-torsors, hence $H^1(X,\mathbf G_m)=\operatorname{Pic}(X)$. We obtain the canonical short exact sequence

$$
0\longrightarrow
\Gamma(X,\mathcal O_X^\times)/\Gamma(X,\mathcal O_X^\times)^n
\longrightarrow H^1(X,\mu_n)
\longrightarrow\operatorname{Pic}(X)[n]
\longrightarrow0. \tag{9.1}
$$

The sequence need not split canonically. Its left term classifies equations $T^n=u$; its right term records line bundles whose $n$th power has been trivialized.

If $n$ is not invertible, the power map is not étale locally surjective in this form and $\mu_n$ may be nonreduced. The étale Kummer sequence then fails; replacing it requires a finer topology and lies outside the coefficient regime of this book.

### 9.2 Units, divisors, and the Picard group

Let $C$ be a smooth proper geometrically connected curve over an algebraically closed field. Its global units are $k^\times$, which is divisible for $n$ prime to the characteristic. Therefore (9.1) gives

$$
H^1(C,\mu_n)\cong\operatorname{Pic}(C)[n].
$$

The degree map $\operatorname{Pic}(C)\to\mathbf Z$ has torsion-free target, so the right side lies in $\operatorname{Pic}^0(C)$. We use only divisor and line-bundle language here; representability of $\operatorname{Pic}^0$ and its polarization belong to the next book.

For an open curve $U=C\setminus Z$, units can have zeros and poles at $Z$. The divisor sequence

$$
1\to k^\times\to\Gamma(U,\mathcal O_U^\times)
\xrightarrow{\operatorname{div}}
\bigoplus_{z\in Z}\mathbf Z[z]
\to\operatorname{Pic}(C)\to\operatorname{Pic}(U)\to0
$$

shows how boundary loops enter Kummer cohomology. A rational function whose divisor is supported on $Z$ gives a $\mu_n$-torsor on $U$, ramified at the omitted points in the compactification.

### 9.3 Affine and projective lines

Over an algebraically closed field $k$ with $n$ invertible,

$$
\operatorname{Pic}(\mathbf A^1)=0,
\qquad k[t]^\times=k^\times=(k^\times)^n.
$$

Hence $H^1(\mathbf A^1,\mu_n)=0$. For prime-to-characteristic coefficients, cohomological dimension of a smooth affine curve is one, so higher Kummer cohomology also vanishes. This agrees with the absence of prime-to-characteristic finite étale covers of $\mathbf A^1$ in characteristic zero, while in positive characteristic it deliberately says nothing about $p$-primary Artin--Schreier covers.

For $\mathbf G_m$, units are $k^\times t^{\mathbf Z}$ and the Picard group is zero, giving

$$
H^1(\mathbf G_m,\mu_n)\cong\mathbf Z/n\mathbf Z,
$$

generated by the cover $u^n=t$.

For $\mathbf P^1$, the unit term vanishes modulo powers and $\operatorname{Pic}(\mathbf P^1)=\mathbf Z$ has no $n$-torsion, so $H^1(\mathbf P^1,\mu_n)=0$. Continuing the Kummer sequence and using the Brauer group of an algebraically closed projective line gives

$$
H^2(\mathbf P^1,\mu_n)\cong
\operatorname{Pic}(\mathbf P^1)/n\cong\mathbf Z/n\mathbf Z.
$$

The class of $\mathcal O(1)$ is the fundamental degree-two class. This computation already proves that proper étale cohomology contains information not encoded by the fundamental group.

### 9.4 Smooth proper curves

For any smooth proper geometrically connected $C/k$ with $k$ algebraically closed, Kummer gives

$$
0\to\operatorname{Pic}(C)/n
\to H^2(C,\mu_n)
\to\operatorname{Br}(C)[n]\to0.
$$

The Brauer group of such a curve is zero. One proof passes to its function field, uses residues at closed points, and observes that an unramified Brauer class has zero residues and hence comes from the algebraically closed constant field. Consequently degree induces

$$
H^2(C,\mu_n)\cong\mathbf Z/n\mathbf Z. \tag{9.2}
$$

Indeed $\operatorname{Pic}^0(C)$ is divisible by $n$ when $n$ is invertible, so $\operatorname{Pic}(C)/n$ is measured exactly by degree modulo $n$.

Equation (9.2) is the origin of the trace map. A closed point has cycle class equal to its degree in $\mathbf Z/n\mathbf Z$; over an algebraically closed field every closed point has degree one. The full dimension of $H^1(C,\Lambda)$ will follow from duality and the genus calculation below.

## 10. Dimension and finiteness on curves

### 10.1 Cohomological dimension

Let $k$ be separably closed of characteristic $p$, and let $\mathcal F$ be a constructible torsion sheaf on a curve $C/k$, killed by an integer prime to $p$. Then

$$
H^i(C,\mathcal F)=0\qquad(i>2).
$$

If $C$ is smooth affine, then $H^i(C,\mathcal F)=0$ for $i>1$. The proper bound two reflects the fundamental class; removing a point kills the top ordinary cohomology.

**Proof strategy.** Reduce constructible sheaves to lisse sheaves on a smooth dense open and skyscraper sheaves at finitely many points. For an affine smooth curve, finite étale covers and normalization reduce lisse coefficients to constant ones, while Kummer-style divisor sequences and prime-to-$p$ purity give dimension one. A proper curve is obtained by adjoining finitely many points, and localization adds at most one degree.

The prime-to-$p$ restriction is essential to this package. In characteristic $p$, Artin--Schreier phenomena can make $H^1$ with $p$-primary coefficients infinite, and wild ramification invalidates the purity and tame-local arguments used below. Some affine vanishing bounds survive for $p$-torsion, but neither the proof nor the finiteness conclusions above extend unchanged.

### 10.2 Constructibility and finiteness

**Finiteness theorem for curves.** Let $C$ be a separated curve of finite type over a separably closed field and let $\mathcal F$ be a constructible sheaf of finite $\Lambda$-modules, where $|\Lambda|$ is prime to the characteristic. Then every $H^i(C,\mathcal F)$ and $H_c^i(C,\mathcal F)$ is finite, and all vanish outside $0\leq i\leq2$.

This is the dimension-one specialization of the finiteness theorem in Book 21. Its proof is geometric, not a consequence of finite stalks alone. The curve-specific reduction chooses a dense smooth open $U$ on which $\mathcal F$ is lisse and a finite étale cover $V\to U$ trivializing it. The Čech-to-derived spectral sequence reduces finiteness to constant-coefficient cohomology of finite covers of $U$ and their iterated fiber products. Compactification and normalization reduce those terms to smooth curves. Kummer theory controls degrees zero and two, while divisor classes and the finite $n$-torsion of degree-zero divisor classes control degree one. Boundary localization contributes only finite sums of finite stalks.

This reasoning also proves constructibility of $R^qf_*\mathcal F$ in the curve situations needed later: stratify the base so that the finite combinatorial data, local monodromy, and ranks of the relevant cohomology groups are constant. The theorem is therefore stable under the devissages used in base change.

### 10.3 A devissage on strata

The standard induction deserves to be explicit. Suppose $j:U\hookrightarrow C$ is a dense open on which $\mathcal F$ is lisse and $i:Z\hookrightarrow C$ is the finite complement. The adjunction map $j_!j^*\mathcal F\to\mathcal F$ is an isomorphism on $U$; its kernel and cokernel are supported on $Z$. A sheaf supported on $Z$ is a finite direct sum of sheaves induced from finite Galois modules of residue fields, and over a separably closed base it has only degree-zero cohomology.

It remains to treat $j_!\mathcal L$. A finite étale cover trivializes $\mathcal L$, and the trace/restriction formalism makes it a direct summand after multiplying by the degree when that degree is invertible in $\Lambda$. When it is not, use a finite filtration of the monodromy module and the Čech spectral sequence rather than dividing by the degree. In either case the terms involve constant finite coefficients on finite covers, so finiteness follows.

This proof explains two common errors. One cannot always split by averaging over the monodromy group because its order may be divisible by $\ell$. And finite generation of divisor groups by itself does not prove finiteness of $H^1$; one needs the finite $n$-torsion and the compactification-localization argument.

## 11. Base change in families

### 11.1 Proper base change for curves

Suppose $f:X\to S$ is proper, $\mathcal F$ is a constructible sheaf of finite $\Lambda$-modules on $X$, and $\Lambda$ has order invertible on $S$. For a geometric point $\bar s\to S$, restriction to the fiber gives the base-change map

$$
(R^qf_*\mathcal F)_{\bar s}
\longrightarrow H^q(X_{\bar s},\mathcal F|_{X_{\bar s}}). \tag{11.1}
$$

For proper families of curves, (11.1) is an isomorphism for every $q$. More generally, after any base change $g:S'\to S$, the canonical morphism

$$
g^*R^qf_*\mathcal F
\longrightarrow R^qf'_*g'^*\mathcal F \tag{11.2}
$$

is an isomorphism. Here $f'$ and $g'$ are the pullbacks of $f$ and $g$.

The statement says that proper cohomology has no information hidden in arbitrarily small neighborhoods of the fiber. Properness supplies the missing compactness: a support or relation that exists nearby cannot disappear by running off to infinity.

Book 22 proves this comparison in the required constructible range. We recall its curve proof architecture because it explains every later application. The decisive point is not invariance from the generic fiber to the special fiber; that assertion is false for a singular degeneration. What must be compared is the cohomology of the special fiber with the filtered colimit of cohomology over all étale neighborhoods of that fiber. Properness turns a cover near the fiber into a cover over a neighborhood of the base point, and finite presentation lets cocycles, refinements, and relations spread out. Constructibility and the curve dimension bound make all the data finite. This is the content of the strict-local proper lemma recalled next.

### 11.2 Reduction to a strictly henselian trait

Write $S_{(\bar s)}$ for the strict localization and $X_{(\bar s)}=X\times_SS_{(\bar s)}$. By the definition of a stalk and continuity of étale cohomology under filtered inverse limits of affine schemes,

$$
(R^qf_*\mathcal F)_{\bar s}
=\varinjlim_{(V,\bar v)}
H^q(X_V,\mathcal F)
\cong H^q(X_{(\bar s)},\mathcal F).
$$

Thus (11.1) follows from the following strict-local assertion.

**Strict-local proper lemma.** If $S$ is noetherian and strictly local, $s$ is its closed geometric point, $f:X\to S$ is proper with one-dimensional fibers, and $\mathcal F$ is constructible finite torsion, then restriction is an isomorphism

$$
H^q(X,\mathcal F)\xrightarrow{\sim}
H^q(X_s,\mathcal F|_{X_s})
$$

for every $q$.

The proof supplied in Book 22 computes derived cohomology by finite truncated étale hypercovers. For any fixed $q$, a class on $X_s$ is represented by finitely many étale maps of finite presentation, finitely many sections of $\mathcal F$, and finitely many cocycle identities through a finite simplicial degree depending on $q$. Every one of these data spreads to an étale neighborhood in $X$. The spread-out maps initially cover only $X_s$. If their images failed to cover $X$ over every neighborhood of $s$, the complement would have closed image in $S$ because $f$ is proper; that closed image would avoid $s$, so it would disappear after shrinking about $s$. Hence, after one common shrinking, the maps form a hypercover of the whole inverse image of a neighborhood of $s$. This is the surjectivity mechanism.

For injectivity, a witnessing cochain and the refinement on which its identities hold are again finitely presented étale data. They spread out, and the same proper-image argument makes the refinement cover over a neighborhood of $s$. The strict-local section property then returns the data over $S$. Sheaves supported on zero-dimensional strata reduce to exactness of finite pushforward; stratifying $\mathcal F$ and using localization completes the constructible devissage. These observations verify that the hypotheses in the theorem from Book 22 apply to the curve families used here.

The theorem is stable under replacing $S$ by any $S'\to S$, which gives (11.2). The same finite data spread over a finite stratification of $S$, so $R^qf_*\mathcal F$ is constructible. Notice what the theorem does not say: generic and special fiber cohomology need not agree, and no division by the degree of a cover is part of the conclusion.

### 11.3 Smooth base change and local acyclicity

Proper base change controls pushforward along a proper map. Smooth base change addresses a different issue: whether a sheaf acquires vanishing cycles as the base varies. A morphism $f:X\to S$ is **locally acyclic relative to $\mathcal F$** if, after strict localization at a geometric point $x$ above $s$, the cohomology of a nearby geometric fiber maps to the local cohomology without producing an extra specialization cone. Informally, local topology does not change in the family.

Book 22 proves that if $f$ is smooth and $\mathcal F$ is lisse with finite coefficients invertible on $S$, then $f$ is universally locally acyclic relative to $\mathcal F$. In relative dimension one, the decisive local calculation is transparent. Étale locally near a chosen geometric point, a smooth morphism admits an étale map to $\mathbf A_S^1$. Compactifying to $\mathbf P_S^1$, proper base change computes the two fiberwise classes, while localization at infinity cancels the top class of the affine neighborhood. A finite étale neighborhood trivializes $\mathcal F$, so the same calculation on its Čech nerve gives the lisse case. The argument survives every pullback of $S$, which is exactly the universal qualifier.

Consequently, for a smooth morphism and lisse prime-to-characteristic coefficients, the strict-local specialization maps defining nearby and vanishing cycles commute with arbitrary base change and have zero vanishing-cycle cone. This is the smooth-base-change statement being used here; it does not assert that ordinary cohomology of an arbitrary nonproper fiber is constant in a family. If $f$ is also proper, proper base change turns the local statement into the global conclusion that $R^qf_*\mathcal F$ is lisse and that its stalks are the fiber cohomology groups. For a smooth proper family of geometrically connected curves over a connected base,

$$
R^0f_*\Lambda\cong\Lambda,
\qquad R^2f_*\Lambda\cong\Lambda(-1),
$$

and $R^1f_*\Lambda$ is lisse of constant rank $2g$, where $g$ is the common genus.

This gives a geometric explanation of smooth proper specialization: no singularity creates a vanishing cycle, and properness prevents a cycle from escaping through a boundary.

### 11.4 What the hypotheses prevent

Each hypothesis has a visible failure mode. In the family $xy=t$, the generic fiber is smooth while the special fiber has a node. A loop collapses at $t=0$, producing a vanishing cycle; smooth base change cannot apply. For a family of punctured curves whose missing section collides with another, cohomology can change despite smoothness of the total open family unless support and boundary are controlled; properness is missing.

If coefficients have residue characteristic $p$, the smooth affine-line homotopy argument fails because Artin--Schreier covers can vary wildly. If $\mathcal F$ is merely constructible and its singular locus moves across fibers, smoothness of $f$ does not make it locally acyclic relative to $\mathcal F$. Finally, proper base change alone does not say $R^qf_*\mathcal F$ is lisse: proper singular families can have constructible higher direct images with jumps.

## 12. Arithmetic action and Hochschild–Serre

### 12.1 The action on geometric cohomology

Let $X/k$ be a scheme of finite type. Every $\sigma\in G_k$ acts on $X_{k^s}$ through the base field and therefore acts functorially on its étale site. If $\mathcal F$ is defined over $k$, its pullback to $X_{k^s}$ carries descent isomorphisms. Combining pullback by $\sigma$ with descent gives

$$
\sigma:H^i(X_{k^s},\mathcal F)\longrightarrow
H^i(X_{k^s},\mathcal F).
$$

At finite coefficient level the group is finite, so the action is automatically continuous once each stabilizer is shown open. Every class and every finite portion of a resolution descends to a finite separable extension of $k$, which supplies such an open stabilizer. For $\ell$-adic cohomology, continuity will follow from the inverse-limit topology.

The action is contravariant with respect to the geometric automorphism: cohomology uses pullback. Our convention is the standard left Galois action induced by the left action of $G_k$ on coefficients and geometric points. Changing a chosen identification of $k^s$ conjugates the representation but not its isomorphism class.

### 12.2 The Hochschild–Serre sequence

The structure morphism factors through the geometric fiber and Galois descent. The associated spectral sequence is

$$
E_2^{a,b}=H^a_{\mathrm{cts}}
\bigl(G_k,H^b(X_{k^s},\mathcal F)\bigr)
\Longrightarrow H^{a+b}(X,\mathcal F). \tag{12.1}
$$

Its low-degree form is

$$
0\to H^1(k,H^0(\bar X,\mathcal F))
\to H^1(X,\mathcal F)
\to H^1(\bar X,\mathcal F)^{G_k}
\to H^2(k,H^0(\bar X,\mathcal F))
\to H^2(X,\mathcal F).
$$

This separates arithmetic classes pulled up from the field from geometric classes fixed by Galois. A fixed geometric class need not descend: the transgression in $H^2(k,H^0)$ is its obstruction.

If $k$ is finite, $G_k\cong\widehat{\mathbf Z}$ has prime-to-characteristic cohomological dimension one. For a finite module $M$ and arithmetic Frobenius $F$, one has

$$
H^0(k,M)=\ker(F-1),
\qquad H^1(k,M)=\operatorname{coker}(F-1),
$$

and higher groups vanish in the relevant torsion category. Thus (12.1) becomes a very explicit comparison of invariants and coinvariants.

### 12.3 Arithmetic and geometric Frobenius

For $k=\mathbf F_q$, arithmetic Frobenius is

$$
F_{\mathrm{arith}}:x\longmapsto x^q
$$

on $k^s$. Geometric Frobenius is its inverse $F_{\mathrm{geom}}=F_{\mathrm{arith}}^{-1}$. Both occur in the literature; formulas are meaningless unless the direction is stated.

Our Galois action uses arithmetic Frobenius as the element of $G_k$. It acts on $\mathbf Z_\ell(1)$ by multiplication by $q$. Consequently it acts on $\mathbf Z_\ell(-1)$ by $q^{-1}$. Geometric Frobenius acts oppositely. The trace isomorphism

$$
H^2(\bar C,\mathbf Q_\ell(1))\cong\mathbf Q_\ell
$$

is $G_k$-equivariant with trivial action on the right; equivalently

$$
H^2(\bar C,\mathbf Q_\ell)\cong\mathbf Q_\ell(-1).
$$

Thus arithmetic Frobenius has eigenvalue $q^{-1}$ on untwisted $H^2$ in this pullback convention, while geometric Frobenius has eigenvalue $q$. Many point-counting formulas are written using geometric Frobenius precisely so the top eigenvalue is $q$.

## 13. Products, classes, and the trace

### 13.1 Cup products and signs

Tensoring resolutions and using the diagonal of the site constructs cup products

$$
H^i(X,\mathcal F)\times H^j(X,\mathcal G)
\longrightarrow H^{i+j}(X,\mathcal F\otimes_\Lambda\mathcal G).
$$

At Čech level, if $a$ and $b$ are cochains, the product restricts $a$ to the first vertices and $b$ to the last vertices, then applies the coefficient pairing. The differential satisfies

$$
d(a\smile b)=da\smile b+(-1)^i a\smile db.
$$

Hence the product descends to cohomology, is associative, and is functorial under pullback. If coefficients commute, it is graded-commutative:

$$
a\smile b=(-1)^{ij}b\smile a
$$

after interchanging coefficient factors. In characteristic two the sign does not force $a\smile a=0$; alternating statements need a separate argument.

Compact support admits the variants

$$
H_c^i(X,\mathcal F)\times H^j(X,\mathcal G)
\to H_c^{i+j}(X,\mathcal F\otimes\mathcal G)
$$

and a product with both factors compactly supported. Extension by zero ensures the resulting support remains proper.

### 13.2 Tate twists and coefficient pairings

For a lisse finite free $\Lambda$-sheaf $\mathcal F$, evaluation gives

$$
\mathcal F\otimes\mathcal F^\vee(1)\longrightarrow\Lambda(1).
$$

The twist is unavoidable. The trace lives naturally on $H^2(C,\Lambda(1))$, not on $H^2(C,\Lambda)$ with values in the trivial module. Omitting it makes the pairing fail Galois equivariance.

More generally, a perfect coefficient pairing $\mathcal F\otimes\mathcal G\to\Lambda(1)$ induces cohomological pairings in complementary degrees. Exactness of dualization requires finite projectivity. If a finite module has $\ell$-torsion over a nonfield coefficient ring, $\mathcal Hom(-,\Lambda)$ alone may not be the derived dual; our clean perfectness statements therefore use finite free sheaves or field coefficients, with integral torsion discussed separately.

### 13.3 Cycle and fundamental classes

Let $C$ be a smooth curve and let $x\hookrightarrow C$ be a closed point. The coefficient order is invertible in the local ring by our standing hypotheses; no condition on the residue degree of $x$ is needed. A local equation of $x$ defines, by Kummer theory on the punctured strict local ring, a boundary class

$$
\operatorname{cl}(x)\in H_x^2(C,\Lambda(1)).
$$

Purity in codimension one says this local cohomology group is canonically $\Lambda$, generated by the class of a uniformizer. To see the normalization, on a strict henselian DVR with uniformizer $t$, the Kummer torsor $u^n=t$ on the punctured spectrum has boundary $1\in\mathbf Z/n\mathbf Z$. Replacing $t$ by a unit times $t$ does not change the boundary because units extend. Thus the generator is intrinsic.

Mapping local cohomology to global cohomology gives the cycle class of $x$. Divisors map additively, and a principal divisor maps to zero by the localization boundary applied to its global rational function. Hence the construction factors through

$$
\operatorname{Pic}(C)\longrightarrow H^2(C,\Lambda(1)),
$$

which is exactly the Kummer first Chern class modulo the coefficient order.

### 13.4 The degree-two trace

Let $C$ be smooth proper geometrically connected over a separably closed field and let $\Lambda=\mathbf Z/n\mathbf Z$ with $n$ invertible. Kummer theory identified

$$
H^2(C,\Lambda(1))\cong\operatorname{Pic}(C)/n
\xrightarrow{\deg}\Lambda.
$$

The resulting isomorphism

$$
\operatorname{Tr}_C:H^2(C,\Lambda(1))\xrightarrow{\sim}\Lambda \tag{13.1}
$$

is the trace map. It sends the class of a geometric point to $1$. Over a nonclosed field it is defined on geometric cohomology and is Galois equivariant; for a closed point of degree $d$, corestriction sends its geometric cycle class to $d$.

If $f:D\to C$ is a finite map of smooth proper curves, the cohomological trace is normalized so that

$$
\operatorname{Tr}_C(f_*\alpha)=\operatorname{Tr}_D(\alpha),
\qquad
f_*f^*=(\deg f)
$$

on cohomology. For a point class, this is the ordinary degree formula. These equations uniquely fix the normalization and will later settle correspondence composition.

## 14. Poincaré duality for proper curves

### 14.1 Statement and normalization

Let $C$ be a smooth proper geometrically connected curve over a separably closed field $k$, let $\Lambda$ be a finite field of characteristic $\ell\ne\operatorname{char}k$, and let $\mathcal F$ be a lisse finite-dimensional $\Lambda$-sheaf. Cup product, evaluation, and trace give

$$
H^i(C,\mathcal F)\times
H^{2-i}(C,\mathcal F^\vee(1))
\longrightarrow\Lambda. \tag{14.1}
$$

**Poincaré duality for curves.** The groups in (14.1) are finite-dimensional, vanish outside $0\leq i\leq2$, and the pairing is perfect for $i=0,1,2$.

For $\Lambda=\mathbf Z/\ell^m\mathbf Z$ and $\mathcal F$ lisse finite free, the same adjoint maps are isomorphisms of finite $\Lambda$-modules. The field case is conceptually clearest; the ring case follows by devissage through multiplication by $\ell$ while preserving the trace normalization.

Book 23 proves this theorem from purity, trace, and Verdier duality. We now unpack the dimension-one mechanism and its consequences. Constant coefficients reduce the middle pairing to divisors, residues, and curve reciprocity. Finite descent and the projection formula then explain why the same pairing is perfect for an arbitrary lisse finite free sheaf. This discussion verifies normalizations and supplies curve-specific tests; it is not a reconstruction of the general duality theorem.

### 14.2 The constant-coefficient calculation

For $i=0$ and $i=2$, connectedness and trace give

$$
H^0(C,\Lambda)=\Lambda,
\qquad H^2(C,\Lambda(1))=\Lambda,
$$

and the pairing is multiplication. The reversed endpoint follows after twisting.

The middle degree requires detection of every class. Choose a nonempty affine open $U=C\setminus Z$. Prime-to-characteristic affine cohomological dimension makes the localization sequence end in

$$
H^1(U,\Lambda(1))\xrightarrow{\partial}
\bigoplus_{z\in Z}\Lambda
\xrightarrow{\sum}H^2(C,\Lambda(1))\to0. \tag{14.2}
$$

The last map sums local residues because a point class has trace one. Kummer theory identifies $H^1(U,\Lambda(1))$ with units modulo powers together with torsion line bundles; its boundary is the vector of valuations modulo $\ell$. Thus (14.2) is the cohomological form of the statement that a principal divisor has total degree zero.

The needed detection statement is the **curve reciprocity lemma**:

$$
H^1(C,\mathbf Z/n\mathbf Z)\times H^1(C,\mu_n)
\xrightarrow{\smile,\operatorname{Tr}}\mathbf Z/n\mathbf Z
$$

is nondegenerate in both variables. Its proof uses only divisors, residues, and Riemann--Roch. Represent the Kummer class by a divisor $D$ and a rational function $f$ with $\operatorname{div}(f)=nD$. Trivialize the cyclic étale torsor representing the other class above the support of $D$. The cup product is the sum of the resulting local Kummer symbols. Changing $f$, $D$, or the local trivializations changes that sum by the symbol of a principal divisor, which is zero because the product of local tame symbols of two rational functions is $1$.

Detection is a finite-group calculation. Choose a finite Galois étale cover $Y\to C$ trivializing the torsors under consideration, with group $G$. Use the exact divisor complexes

$$
1\to k^\times\to k(Y)^\times
\xrightarrow{\operatorname{div}}\operatorname{Div}(Y)
\to\operatorname{Pic}(Y)\to0
$$

and

$$
0\to\operatorname{Div}^0(Y)\to\operatorname{Div}(Y)
\xrightarrow{\deg}\mathbf Z\to0.
$$

Hilbert's theorem in degree one makes $k(Y)^\times$ exact at the first descent obstruction. Because the cover is étale and $k$ is separably closed, $\operatorname{Div}(Y)$ is a direct sum of free permutation modules $\mathbf Z[G]$; its Tate cohomology vanishes. Riemann--Roch supplies the remaining moving step: every divisor class may be represented away from a prescribed finite set, while prescribed local valuation data subject to the principal-divisor relation can be tested after adding a sufficiently positive divisor.

Apply a complete $G$-resolution to the two divisor complexes. On a permutation summand, the local-symbol map is the evident perfect evaluation between a point above $C$ and its character. Hilbert 90 removes the rational-function obstruction, the product formula removes the single sum-of-residues relation, and the Riemann--Roch moving step shows that the mapping cone has no remaining homology. The resulting chain comparison identifies characters of the torsor group with character duals of the $n$-torsion divisor classes. Since the chain map is the sum of local symbols, this identification is exactly cup product followed by trace. It follows that each nonzero class has a local-symbol detector, proving the curve reciprocity lemma.

Finiteness from Chapter 10 now turns nondegeneracy in both variables into perfectness. The proof is not a cardinality-only argument: the local symbols and the Riemann--Roch moving step construct a detector for a nonzero class.

There is a useful alternative consistency check. For $C=\mathbf P^1$, both $H^1$ groups vanish and endpoint duality is exactly the degree isomorphism. Cutting a general $C$ at finitely many points and applying (14.2) shows that adding a handle creates two mutually paired degree-one directions, anticipating the dimension $2g$.

### 14.3 Perfectness for lisse sheaves

Let $\mathcal F$ be lisse. Choose a connected finite Galois cover $p:D\to C$ with group $G$ such that $p^*\mathcal F$ is constant with stalk $M$. The following finite descent lemma is the curve-level specialization of the descent step in Book 23.

**Finite descent lemma.** Suppose constant-coefficient duality on $D$ is compatible with the $G$-action and with restriction and trace. Then it implies duality on $C$ for the local system associated with every $\Lambda$-module $M$ which is finite free over $\Lambda$ and carries a $G$-action.

The point requiring care is equivariant finiteness. Because $D\to C$ is a finite étale $G$-torsor and $C$ is proper, a finite étale hypercover of $C$ pulls back to one on which $G$ acts freely in every simplicial degree. After truncation above the curve cohomological dimension, its cochain complex represents $R\Gamma(D,\Lambda)$ by a bounded complex $K$ of finite projective $\Lambda[G]$-modules. This is stronger than merely representing it by finite $\Lambda$-modules, and it is what prevents spurious group-cohomology or Tate-cohomology terms when $\ell$ divides $|G|$.

Constant duality on $D$ gives a $G$-equivariant quasi-isomorphism

$$
K\simeq R\operatorname{Hom}_\Lambda(K(1),\Lambda)[-2].
$$

Descent expresses $R\Gamma(C,\mathcal F)$ as the $G$-equivariant total complex formed from $K$ and $M$. Since every term of $K$ is projective over $\Lambda[G]$, ordinary tensor--Hom adjunction computes the derived functors; no averaging and no complete resolution are allowed or needed. The group algebra is a symmetric Frobenius algebra: the map taking the coefficient of the identity gives a perfect pairing

$$
\Lambda[G]\times\Lambda[G]\longrightarrow\Lambda,
\qquad (a,b)\longmapsto [1](ab).
$$

Together with $M\otimes M^\vee\to\Lambda$, this pairing identifies the $\Lambda$-linear dual of the descent complex for $M$ with the descent complex for $M^\vee$. Combining this termwise identification with the displayed quasi-isomorphism for $K$ gives

$$
R\Gamma(C,\mathcal F)
\simeq
R\operatorname{Hom}_\Lambda
\bigl(R\Gamma(C,\mathcal F^\vee(1)),\Lambda\bigr)[-2].
$$

The chain pairing just constructed is cup product followed by trace. Indeed, on the free summand $\Lambda[G]$ it sums the contributions of the geometric sheets. That is exactly the finite étale trace of Section 7.4, and the tensor--Hom adjunction gives the projection formula

$$
\operatorname{Tr}_D(p^*a\smile b)
=\operatorname{Tr}_C(a\smile p_*b).
$$

Thus neither a norm factor nor an inverse action has entered. Taking cohomology proves the finite descent lemma, including when $\ell\mid |G|$.

Apply the lemma to $M$. For coefficient rings rather than fields, a short exact sequence

$$
0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0
$$

dualizes in reverse. The two long exact cohomology sequences are adjoint because cup product is compatible with connecting homomorphisms. If duality holds for two terms, the five lemma gives it for the third. This exact devissage completes the proof.

The same chain construction, combined with the open--closed exact sequence of Section 4.2 and the codimension-one purity calculation of Section 13.3, proves the constructible form needed on a proper curve: lisse pieces are treated by finite descent, point-supported pieces by the trace pairing on their stalks, and the two are glued by adjoint localization sequences. This is why the open-curve argument below does not silently assume that $j_!\mathcal F$ is lisse at the boundary.

### 14.4 Consequences and tests

Endpoint duality identifies

$$
H^2(C,\mathcal F)\cong
H^0(C,\mathcal F^\vee(1))^\vee.
$$

Thus top cohomology vanishes exactly when the twisted dual has no global invariant. For a geometrically nontrivial rank-one local system $\mathcal L$ with neither $\mathcal L$ nor $\mathcal L^{-1}(1)$ constant geometrically, both $H^0$ and $H^2$ vanish; all cohomology is concentrated in degree one.

For constant $\Lambda$, the pairing on $H^1(C,\Lambda)$ takes values in $\Lambda(-1)$ before applying a chosen twist identification. Graded commutativity makes it alternating when $\ell$ is odd. When $\ell=2$, alternation follows from the geometric self-intersection calculation for degree-one classes, not from the sign alone.

If $C$ and the sheaf descend to $k$, the pairing is $G_k$-equivariant:

$$
\langle\sigma a,\sigma b\rangle=\sigma\langle a,b\rangle.
$$

After trace to the trivial coefficient on $H^2(C,\Lambda(1))$, the scalar pairing is invariant. This compatibility is the global curve analogue of the Tate-twisted local pairings developed in local Galois cohomology.

## 15. Open-curve duality and Euler characteristics

### 15.1 Duality with compact support

Let $U$ be a smooth geometrically connected curve over a separably closed field and let $\mathcal F$ be lisse with finite field coefficients prime to the characteristic. The correct complementary pairing is

$$
H_c^i(U,\mathcal F)\times
H^{2-i}(U,\mathcal F^\vee(1))
\longrightarrow\Lambda. \tag{15.1}
$$

It is perfect. Ordinary cohomology on both sides would be wrong: a class circling a puncture is paired with a compactly supported path toward that puncture.

To prove (15.1), choose a smooth proper compactification $j:U\hookrightarrow C$. The pairing is the proper-curve pairing between $j_!\mathcal F$ and $Rj_*\mathcal F^\vee(1)$. At a boundary point, strict local purity identifies the cone of $j_!\to Rj_*$ with the two-term inertia complex. For $\ell$-primary coefficients with $\ell\ne\operatorname{char}k$, wild inertia is pro-$p$ and taking its invariants is exact; the remaining $\ell$-cohomological direction is the procyclic tame quotient. Continuous cohomology pairs its invariants with twisted coinvariants. Hence the boundary cones are dual even when the sheaf has wild monodromy. Proper duality on $C$, combined with the localization triangles, gives a morphism between long exact sequences whose boundary terms and middle proper terms are perfect. The five lemma yields (15.1).

The exclusion concerns coefficients of characteristic $p$, not wild ramification of an $\ell$-adic sheaf. For $p$-primary coefficients, wild inertia is no longer cohomologically invisible and this two-term argument fails.

### 15.2 Boundary terms

Suppose $U=C\setminus Z$ and $\mathcal F$ is lisse. At $z\in Z$, let $I_z$ act on a nearby geometric stalk $M$. The ordinary direct image has stalk $M^{I_z}$, and the first local higher direct image is $H^1(I_z,M)$. If wild inertia acts trivially, this latter group is the appropriately twisted coinvariant module for tame inertia. Thus localization relates global cohomology in the tame case to the finite collections

$$
M^{I_z},
\qquad M_{I_z}(-1),
$$

which are dual under evaluation when $M$ is finite free.

For constant $M=\Lambda$, inertia is trivial. Each puncture contributes a copy of $\Lambda$ to the quotient $j_*\Lambda/j_!\Lambda$, but the global diagonal relation removes one. This recovers the $|Z|-1$ boundary contribution to $H_c^1$. For a sheaf with no inertia invariants, the degree-zero boundary term disappears, but $H^1(I_z,M)$ may still record tame monodromy.

### 15.3 Euler characteristics

For a finite-dimensional coefficient field define

$$
\chi(C,\mathcal F)=\sum_i(-1)^i\dim_\Lambda H^i(C,\mathcal F),
$$

and similarly $\chi_c(U,\mathcal F)$. Long exact sequences make Euler characteristic additive. For constant coefficients on a smooth proper genus-$g$ curve,

$$
\chi(C,\Lambda)=2-2g. \tag{15.2}
$$

For $U=C\setminus Z$ with $r=|Z|$ geometric points,

$$
\chi_c(U,\Lambda)=2-2g-r. \tag{15.3}
$$

Indeed localization subtracts one degree-zero skyscraper contribution for each missing point.

For a lisse sheaf $\mathcal F$ of rank $d$, the Grothendieck--Ogg--Shafarevich formula is

$$
\chi_c(U,\mathcal F)=d\,\chi_c(U,\Lambda)
-\sum_{z\in Z}\operatorname{Swan}_z(\mathcal F). \tag{15.4}
$$

Thus in the tame case the compactly supported Euler characteristic is simply $d\,\chi_c(U,\Lambda)$, even when tame inertia has few invariants. The invariant deficits $d-\dim M^{I_z}$ appear instead when one computes $\chi(C,j_*\mathcal F)$; together with Swan conductors they form the local Artin conductor. Systematic conductor theory belongs elsewhere, but distinguishing these two formulas prevents tame boundary monodromy from being counted twice.

### 15.4 The dimension $2g$

For a smooth proper geometrically connected curve, $H^0(C,\Lambda)=\Lambda$ and duality gives $H^2(C,\Lambda)=\Lambda(-1)$, each of dimension one. Combining this with (15.2),

$$
2-\dim H^1(C,\Lambda)=2-2g,
$$

so

$$
\dim_\Lambda H^1(C,\Lambda)=2g. \tag{15.5}
$$

The geometric input behind (15.2) can be given algebraically. Choose a nonconstant separable map $C\to\mathbf P^1$ and apply Riemann--Hurwitz together with localization at its branch points. Away from the branch locus the cover is finite étale, so trace computes the Euler characteristic by degree. At each ramification point the deficit is the ramification contribution. Riemann--Hurwitz says precisely that the total deficit changes $2\deg(f)$ into $2-2g$. Thus (15.2) is not imported from topology; it follows from finite-map cohomology and the algebraic ramification formula.

For $\ell^m$ coefficients, use

$$
0\longrightarrow\mathbf Z/\ell^{m-1}\mathbf Z
\xrightarrow{\ell}\mathbf Z/\ell^m\mathbf Z
\longrightarrow\mathbf Z/\ell\mathbf Z\longrightarrow0.
$$

The induced map on $H^2$ is the injective coefficient map between the free rank-one trace modules. The long exact sequence therefore makes reduction

$$
H^1(C,\mathbf Z/\ell^m\mathbf Z)\longrightarrow
H^1(C,\mathbf Z/\ell\mathbf Z)
$$

surjective. Applying the same argument to

$$
0\longrightarrow\mathbf Z/\ell\mathbf Z
\xrightarrow{\ell^{m-1}}\mathbf Z/\ell^m\mathbf Z
\longrightarrow\mathbf Z/\ell^{m-1}\mathbf Z\longrightarrow0
$$

shows that reduction to level $m-1$ is surjective. Composing that reduction with the coefficient injection from level $m-1$ is multiplication by $\ell$, so the kernel of reduction to level one is exactly $\ell H^1(C,\mathbf Z/\ell^m\mathbf Z)$. Induction on $m$, Nakayama's lemma, and the length supplied by the first exact sequence show that $H^1(C,\mathbf Z/\ell^m\mathbf Z)$ is free of rank $2g$. This argument, rather than perfectness alone, excludes shorter cyclic summands. The finite-level freeness is what makes the later inverse limit a $\mathbf Z_\ell$-lattice of rank $2g$.

## 16. Finite maps and correspondences

### 16.1 Pullback, trace, and projection

Let $f:C\to D$ be a finite nonconstant morphism of smooth proper geometrically connected curves over a field. Such a map is finite flat. Pullback exists for every coefficient sheaf:

$$
f^*:H^i(D,\mathcal F)\longrightarrow H^i(C,f^*\mathcal F).
$$

If $f$ is étale, the trace was the sum over geometric sheets. Ramification prevents that description at branch points, but purity and proper duality extend it uniquely to a trace

$$
f_*:H^i(C,f^*\mathcal F)\longrightarrow H^i(D,\mathcal F)
$$

for lisse finite coefficients, characterized by the projection formula and by the ordinary field trace over the étale locus. The complement of that locus is finite. Localization and purity show that an extension across it exists and is unique because local cycle classes must be sent with their residue-field degrees.

The essential identities are

$$
f_*f^*=(\deg f)\operatorname{id}
$$

and

$$
f_*(f^*a\smile b)=a\smile f_*b. \tag{16.1}
$$

They hold at finite coefficient level and survive inverse limits. On top cohomology, $f^*$ multiplies the fundamental class by $\deg f$, while $f_*$ preserves trace. On $H^0$ of connected curves, $f^*$ fixes constants and $f_*$ multiplies them by $\deg f$; if the source has several connected components, pullback is the corresponding diagonal. These endpoint tests rule out the common error of interchanging the two normalizations.

If $f$ is purely inseparable in positive characteristic, it is a universal homeomorphism and induces an equivalence on prime-to-characteristic étale sites. Hence $f^*$ is an isomorphism on the cohomology considered here. Its degree is a power of the characteristic and therefore a unit in $\Lambda$; the compatible trace is $\deg(f)(f^*)^{-1}$. Thus the formulas remain valid even though no geometric étale sheets exist.

### 16.2 Correspondence variance

For the correspondence discussion assume that the ground field is perfect, as it is in the arithmetic applications later in the series. Then the normalization of an integral curve is smooth. A finite correspondence from $C$ to $D$ is a finite $\mathbf Z$-linear combination of integral curves

$$
\Gamma\subset C\times D
$$

finite and surjective over the components in question. Let

$$
p_C:\Gamma^\nu\to C,\qquad p_D:\Gamma^\nu\to D
$$

be the maps from the normalization. The induced covariant action from source to target is

$$
\Gamma_*=(p_D)_*p_C^*:
H^1(C,\Lambda)\longrightarrow H^1(D,\Lambda). \tag{16.2}
$$

The formula is contravariant along the source leg and covariant by trace along the target leg. Reversing these arrows produces an operator in the opposite direction.

For coefficient local systems, (16.2) requires a morphism $p_C^*\mathcal F\to p_D^*\mathcal G$ on $\Gamma^\nu$. Without such coefficient data there is no canonical action between unrelated local systems. Constant coefficients need no additional choice.

The graph $\Gamma_f\subset C\times D$ of a finite map $f:C\to D$ acts by $f_*$. Its transpose $\Gamma_f^t\subset D\times C$ acts by $f^*$. This quick test fixes the variance of every later correspondence formula.

### 16.3 Composition and transpose

Let $\Gamma:C\dashrightarrow D$ and $\Delta:D\dashrightarrow E$ be finite correspondences. Their composite is obtained from the fiber product over $D$, with intersection multiplicities and proper pushforward to $C\times E$:

$$
\Delta\circ\Gamma
=(p_{CE})_*\bigl(p_{CD}^*\Gamma\cdot p_{DE}^*\Delta\bigr).
$$

When all intersections are transverse, its points are simply composable pairs. In general the multiplicities are necessary for functoriality. Repeated use of proper pushforward, flat pullback on the finite curve legs, and the projection formula proves

$$
(\Delta\circ\Gamma)_*=\Delta_*\circ\Gamma_*.
$$

The transpose correspondence interchanges the two factors. Poincaré duality makes it adjoint:

$$
\langle\Gamma_*a,b\rangle_D
=\langle a,(\Gamma^t)_*b\rangle_C. \tag{16.3}
$$

Indeed, expand $\Gamma_*$ as trace after pullback and apply (16.1). Equation (16.3) is the cohomological origin of adjoint Hecke operators, though no particular modular correspondence is needed here.

A useful example is $\Gamma_f^t\circ\Gamma_f$ for a finite map $f:C\to D$. Acting on $H^1(C)$ it is $f^*f_*$, not generally multiplication by $\deg f$; fibers can connect different sheets. The opposite composition $\Gamma_f\circ\Gamma_f^t$ acts on $H^1(D)$ as $f_*f^*=\deg f$. This counterexample prevents an unjustified symmetry between the two compositions.

### 16.4 Endomorphisms of $H^1$

For $C=D$, finite correspondences form a ring under addition and composition, and

$$
\Gamma\longmapsto\Gamma_*|_{H^1(C,\Lambda)}
$$

is a ring homomorphism with the composition order fixed above. Our definition has already excluded vertical and horizontal components by requiring finiteness and dominance over both factors. If one enlarges the cycle group to include them, their degree-one action is zero: they factor cohomologically through a point. Thus $H^1$ naturally isolates the genuinely moving part.

If $C$, $\Gamma$, and all coefficient maps are defined over $k$, then $\Gamma_*$ commutes with $G_k$. If $\Gamma$ is defined only over a finite extension, its Galois conjugates give conjugate operators. Summing the conjugates descends an operator to $k$.

Finite-level actions are compatible under reduction $\Lambda_{m+1}\to\Lambda_m$. They will therefore act continuously on the $\ell$-adic inverse limit. This is the precise mechanism needed later: geometry supplies correspondences; cohomology converts them into endomorphisms commuting with arithmetic Galois action.

## 17. From finite coefficients to $\ell$-adic cohomology

### 17.1 Inverse systems and the Milnor sequence

Fix a prime $\ell$ invertible on $X$. Book 21 shows why it is unsafe to define $\ell$-adic cohomology by writing a sheaf $\mathbf Z_\ell$ and applying ordinary discrete-sheaf cohomology: that loses the topology and can give the wrong derived limit. We use its continuous construction, beginning with the system $\Lambda_m=\mathbf Z/\ell^m\mathbf Z$ and the derived inverse limit

$$
R\Gamma(X,\mathbf Z_\ell)
=R\varprojlim_m R\Gamma(X,\Lambda_m).
$$

There is a Milnor exact sequence

$$
0\longrightarrow
\varprojlim\nolimits_m^1 H^{i-1}(X,\Lambda_m)
\longrightarrow H^i(X,\mathbf Z_\ell)
\longrightarrow\varprojlim_m H^i(X,\Lambda_m)
\longrightarrow0. \tag{17.1}
$$

The correction is not decorative. It measures failure of inverse limit to be exact. If the inverse system is Mittag--Leffler—for example, if its terms are finite, since the descending images in each fixed term eventually stabilize—then $\varprojlim^1=0$. For finite constructible cohomology on curves, this applies, and therefore

$$
H^i(X,\mathbf Z_\ell)\cong
\varprojlim_mH^i(X,\mathbf Z/\ell^m\mathbf Z). \tag{17.2}
$$

The limit carries its profinite topology, not the discrete topology.

For compact support, use $R\Gamma(\bar X,j_!(-))$ level by level before taking the derived limit. Compactification independence and all localization maps are compatible with reduction, so (17.1)--(17.2) have compact-support analogues.

### 17.2 Lattices and rational local systems

Let $\mathcal T=(\mathcal T_m)$ be a lisse $\mathbf Z_\ell$-sheaf of rank $r$, with $\mathcal T_m=\mathcal T/\ell^m$. Define

$$
H^i(X,\mathcal T)=
H^i\left(R\varprojlim_mR\Gamma(X,\mathcal T_m)\right).
$$

Finiteness again gives the Mittag--Leffler property. On each connected component, a lisse $\mathbf Q_\ell$-sheaf $\mathcal V$ has compact monodromy and therefore admits a globally stable lattice $\mathcal T$. One sets

$$
H^i(X,\mathcal V)=H^i(X,\mathcal T)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

This does not depend on the lattice: two stable lattices are commensurable, and their quotient is finite $\ell$-power torsion, which disappears after tensoring with $\mathbf Q_\ell$. The resulting vector spaces are finite-dimensional for constructible $\mathcal V$ on curves.

Reduction modulo $\ell^m$ need not always commute with cohomology. From

$$
0\to\mathcal T\xrightarrow{\ell^m}\mathcal T
\to\mathcal T/\ell^m\to0
$$

one obtains

$$
0\to H^i(X,\mathcal T)/\ell^m
\to H^i(X,\mathcal T/\ell^m)
\to H^{i+1}(X,\mathcal T)[\ell^m]\to0. \tag{17.3}
$$

Thus an isomorphism with reduction of integral cohomology requires the next integral group to be torsion-free. For a smooth proper curve with constant coefficients, all groups are torsion-free and (17.3) gives the expected compatibility. For general local systems, torsion can occur and must not be suppressed.

### 17.3 Integral duality and torsion warnings

Finite-level Poincaré pairings pass compatibly to the inverse limit:

$$
H^i(C,\mathcal T)\times
H^{2-i}(C,\mathcal T^\vee(1))
\longrightarrow\mathbf Z_\ell.
$$

If the relevant integral cohomology groups are finite free, this pairing is perfect. In general, the free quotients pair perfectly, while torsion in one degree is paired by a linking form with torsion in the adjacent complementary degree. The derived statement is cleanest:

$$
R\Gamma(C,\mathcal T)
\simeq
R\operatorname{Hom}_{\mathbf Z_\ell}
\bigl(R\Gamma(C,\mathcal T^\vee(1)),\mathbf Z_\ell\bigr)[-2].
$$

After tensoring with $\mathbf Q_\ell$, torsion vanishes and one obtains unconditional perfect pairings

$$
H^i(C,\mathcal V)\times
H^{2-i}(C,\mathcal V^\vee(1))
\longrightarrow\mathbf Q_\ell. \tag{17.4}
$$

For constant coefficients on a genus-$g$ curve,

$$
H^0(C,\mathbf Z_\ell)=\mathbf Z_\ell,\qquad
H^1(C,\mathbf Z_\ell)\cong\mathbf Z_\ell^{\,2g},\qquad
H^2(C,\mathbf Z_\ell)=\mathbf Z_\ell(-1).
$$

These are isomorphisms of modules; the middle Galois action is generally nontrivial over a nonclosed field.

### 17.4 Continuous Galois representations

Let $C/k$ be smooth proper and geometrically connected. Each finite group

$$
H^i(C_{k^s},\mathbf Z/\ell^m\mathbf Z)
$$

has a continuous $G_k$-action, and the reduction maps are equivariant. Their inverse limit is therefore a profinite $\mathbf Z_\ell$-module with continuous action: continuity means that the inverse image of the stabilizer of every finite-level class is open. For $i=1$ it is finite free of rank $2g$, so

$$
\rho_{C,\ell}:G_k\longrightarrow
\operatorname{GL}_{2g}(\mathbf Z_\ell)
$$

is continuous for the $\ell$-adic topology. Inverting $\ell$ gives

$$
\rho_{C,\ell,\mathbf Q}:G_k\longrightarrow
\operatorname{GL}\bigl(H^1(C_{k^s},\mathbf Q_\ell)\bigr).
$$

More generally, if a lisse $\mathbf Z_\ell$-sheaf $\mathcal T$ on $C$ is defined over $k$, its descent maps act compatibly on every finite group $H^i(C_{k^s},\mathcal T/\ell^m)$. The inverse limit therefore gives a continuous action on the finitely generated $\mathbf Z_\ell$-module $H^i(C_{k^s},\mathcal T)$, and inverting $\ell$ gives a continuous finite-dimensional representation on $H^i(C_{k^s},\mathcal V)$. Unlike the constant-coefficient case, its integral cohomology may have torsion and its $H^1$ dimension need not be $2g$ times the rank; Euler characteristics and the invariant spaces in degrees zero and two determine the correction.

If $k$ is finite, either arithmetic or geometric Frobenius topologically generates $G_k$. Our convention describes the action of arithmetic Frobenius; converting a characteristic polynomial written for geometric Frobenius requires replacing the operator by its inverse. Duality gives the invariant pairing

$$
H^1(\bar C,\mathbf Q_\ell)\times
H^1(\bar C,\mathbf Q_\ell(1))\to\mathbf Q_\ell,
$$

so the representation is canonically dual to its Tate-twisted dual.

## 18. Semistable curves over a field

Smoothness made the preceding duality statements look inevitable: there was one fundamental class, one top trace, and an even-dimensional middle group. A nodal curve is the first test of which features came from properness and which came from smoothness. Properness still gives finite cohomology and base change. A node, however, joins two branches and inserts a graph into the geometry. The graph contributes to $H^1$, while reducible components contribute independently to $H^2$. Ordinary constant-coefficient Poincaré duality therefore cannot survive unchanged.

This chapter computes the static cohomology of a semistable fiber. The next chapter studies how such a fiber sits below a smooth generic curve. Keeping those two problems separate is essential: normalization computes the singular fiber, whereas inertia and vanishing cycles compare it with the generic fiber.

### 18.1 Nodes, normalization, and the dual graph

Let $C$ be a connected proper curve over a separably closed field $k$. We call $C$ **semistable** if it is reduced and its only singularities are ordinary double points. Étale locally at such a point its completed local equation has the form

$$
xy=0.
$$

Let

$$
\nu:\widetilde C=\coprod_{v\in V}C_v\longrightarrow C
$$

be the normalization. Each $C_v$ is a smooth proper connected curve. Let $E$ be the set of nodes. The **dual graph** $\Gamma$ has one vertex $v$ for each normalized component and one edge $e$ for each node. The endpoints of $e$ are the components containing the two branches above that node. A self-node gives a loop, and two components may be joined by several edges. These possibilities must be retained: loops and parallel edges are exactly what create graph cohomology.

Choose an orientation of every edge. The cellular cochain complex with coefficients in a ring $\Lambda$ is

$$
C^0(\Gamma,\Lambda)=\Lambda^V
\xrightarrow{d}
C^1(\Gamma,\Lambda)=\Lambda^E,
$$

where

$$
(da)_e=a_{t(e)}-a_{s(e)}.
$$

Changing an orientation multiplies the corresponding edge coordinate by $-1$ and does not change the cohomology. Since $C$ is connected,

$$
H^0(\Gamma,\Lambda)=\Lambda,
\qquad
\operatorname{rank}H^1(\Gamma,\Lambda)
=b_1(\Gamma)=|E|-|V|+1
$$

when $\Lambda$ is a field or a discrete valuation ring. This first Betti number counts independent circuits, not nodes. A tree can have many nodes and still has $b_1=0$.

### 18.2 The normalization calculation

The reason the graph enters cohomology is visible directly on sheaves. A locally constant function on $C$ is a locally constant function on each $C_v$ whose two values above every node agree. Hence there is an exact sequence

$$
0\longrightarrow\Lambda_C
\longrightarrow\nu_*\Lambda_{\widetilde C}
\xrightarrow{\delta}
\bigoplus_{e\in E}i_{e*}\Lambda
\longrightarrow0. \tag{18.1}
$$

After orienting an edge, $\delta$ takes the value on its terminal branch minus the value on its initial branch. The quotient is canonical even though this identification with $\Lambda$ changes sign when the orientation changes. The map $\nu$ is finite, so it has no higher direct images on the sheaves under consideration. Taking cohomology of (18.1) therefore gives

$$
0\to\Lambda
\to\Lambda^V
\xrightarrow d\Lambda^E
\to H^1(C,\Lambda)
\to\bigoplus_{v\in V}H^1(C_v,\Lambda)
\to0, \tag{18.2}
$$

and

$$
H^2(C,\Lambda)
\xrightarrow{\sim}
\bigoplus_{v\in V}H^2(C_v,\Lambda). \tag{18.3}
$$

The first three terms of (18.2) are the cellular complex of $\Gamma$. We obtain the canonical short exact sequence

$$
0\longrightarrow H^1(\Gamma,\Lambda)
\longrightarrow H^1(C,\Lambda)
\longrightarrow\bigoplus_{v\in V}H^1(C_v,\Lambda)
\longrightarrow0. \tag{18.4}
$$

It generally has no canonical splitting. A splitting would require choices of paths through the graph or choices of how to lift component classes across the nodes. The exact sequence, not a preferred direct sum, is the functorial object.

For $\Lambda=\mathbf Z/\ell^m\mathbf Z$, every term in (18.4) is finite free: graph cohomology is free and every smooth component contributes a free group of rank twice its genus. Passing compatibly through $m$ gives

$$
0\longrightarrow H^1(\Gamma,\mathbf Z_\ell)
\longrightarrow H^1(C,\mathbf Z_\ell)
\longrightarrow\bigoplus_v H^1(C_v,\mathbf Z_\ell)
\longrightarrow0. \tag{18.5}
$$

There is no derived-limit correction because all finite-level groups are finite. In particular,

$$
\operatorname{rank}_{\mathbf Z_\ell}H^1(C,\mathbf Z_\ell)
=b_1(\Gamma)+2\sum_v g_v. \tag{18.6}
$$

Equation (18.3) has a different flavor. Since each component has its own fundamental class,

$$
H^2(C,\mathbf Z_\ell)
\cong\mathbf Z_\ell(-1)^V. \tag{18.7}
$$

Thus a reducible connected curve has several ordinary top classes. Connectedness controls $H^0$; irreducible components control $H^2$.

If $C$ is defined over a nonclosed field, the calculation is made after separable base change. The ground-field Galois group permutes vertices, edges, and normalized components, and all maps in (18.2)--(18.7) are equivariant. Over a finite field, arithmetic or geometric Frobenius therefore acts on the graph complex by its permutation of the geometric components and nodes, and acts on the component cohomology by the usual pullback action.

### 18.3 Arithmetic genus and the lost half of a loop

The arithmetic genus of a connected proper nodal curve satisfies

$$
g_a(C)=\sum_v g_v+b_1(\Gamma). \tag{18.8}
$$

One proves this from the analogous normalization sequence for the structure sheaf: the cokernel at every node has dimension one, and the incidence map removes $|V|-1$ independent constants. Comparing (18.6) with (18.8) gives

$$
\dim H^1(C,\mathbf Q_\ell)
=2g_a(C)-b_1(\Gamma). \tag{18.9}
$$

A smooth curve of genus $g$ has dimension $2g$. A singular semistable curve of the same arithmetic genus has lost one degree-one class for each independent graph circuit. The graph itself restores one class per circuit, but a smooth handle has two degree-one directions. The other direction is not cohomology of the static singular fiber; it will appear as a vanishing class in a smoothing.

Examples make the formula tangible.

If $C$ is a tree of projective lines, then every $g_v$ and $b_1(\Gamma)$ is zero, so $H^1(C,\Lambda)=0$. It may have many nodes, but no circuit survives.

If $C$ is a polygon of $r$ projective lines, then $b_1(\Gamma)=1$ and

$$
H^1(C,\Lambda)=\Lambda.
$$

The same answer occurs for an irreducible rational curve with one node: the normalization is $\mathbf P^1$, and the self-node gives one loop edge. This rank-one group is the simplest proof that smooth Poincaré duality cannot be copied onto a nodal curve.

If two smooth curves of genera $g_1$ and $g_2$ meet in one node, the graph is a single edge joining two vertices and is a tree. Hence

$$
H^1(C,\Lambda)
\cong H^1(C_1,\Lambda)\oplus H^1(C_2,\Lambda)
$$

noncanonically as modules and canonically through (18.4). Its rank is $2g_1+2g_2=2g_a(C)$. A smoothing has no vanishing rank in this compact-type case, even though its special fiber is singular.

### 18.4 Duality at a node

For a smooth proper connected curve, the dualizing complex is $\Lambda(1)[2]$ and the trace makes $H^1$ self-dual up to twist. At a node this identification fails. The irreducible nodal rational curve has rank-one $H^1$; over odd coefficients no alternating form on a rank-one free module can be perfect. The failure is not a defect of cohomology. It says that the constant sheaf is not the orientation object of the singular curve.

Book 23 supplies the correct dualizing complex $\omega_C^\bullet$. Dualizing (18.1) gives a triangle

$$
\bigoplus_{e\in E}i_{e*}\Lambda
\longrightarrow
\nu_*\Lambda(1)[2]
\longrightarrow
\omega_C^\bullet
\longrightarrow
\bigoplus_{e\in E}i_{e*}\Lambda[1]. \tag{18.10}
$$

The first map is the difference of the two branch fundamental classes. Its signs match the incidence map in the graph complex. Verdier duality then gives a perfect identity

$$
R\Gamma\bigl(C,R\mathcal Hom(K,\omega_C^\bullet)\bigr)
\simeq
R\operatorname{Hom}_\Lambda(R\Gamma(C,K),\Lambda) \tag{18.11}
$$

for bounded constructible finite coefficients. The component pairings and the vertex-edge incidence pairing are the visible pieces of (18.11). The node term supplies the part that an alternating pairing on $H^1(C,\Lambda)$ alone cannot see.

There is still a scalar trace, but it is the counit associated with $\omega_C^\bullet$, not an assertion that the multi-dimensional group in (18.7) is canonically one-dimensional. On component fundamental classes it sums the component traces with the incidence correction prescribed by (18.10). This distinction is vital whenever a singular fiber is substituted into a smooth formula.

### 18.5 Sheaves and correspondences on a nodal curve

The normalization method is not restricted to constant coefficients. If $\mathcal F$ is lisse finite free on the whole nodal curve, then

$$
0\longrightarrow\mathcal F
\longrightarrow\nu_*\nu^*\mathcal F
\longrightarrow\bigoplus_{e\in E}i_{e*}\mathcal Q_e
\longrightarrow0, \tag{18.12}
$$

where $\mathcal Q_e$ is the quotient of the two branch fibers by the diagonal gluing supplied by $\mathcal F$. After choices, the resulting degree-zero and degree-one terms form a cellular complex on $\Gamma$ with local coefficients. Formula (18.4) is the constant case. For a constructible sheaf one first separates the smooth open strata, the nodes, and any additional singular support; (18.12) then combines with the standard support filtration. No claim of a uniform rank is possible without knowing the branch gluing and the component monodromy.

A finite correspondence between nodal proper curves acts by the same pull-then-trace rule as in the smooth case whenever its normalized legs are finite and the coefficient morphism is specified. On normalization it acts on the cohomology of components. At nodes it acts on branch values, hence on the graph complex. Functoriality of (18.12) shows that the two actions fit into a map of the exact sequences (18.4). A correspondence that collapses a component or is supported at a point has zero action on the moving degree-one component, but it can affect degree zero or the collection of top component classes.

If the correspondence and curve descend to a field $k$, the component and graph actions commute with $G_k$. If a correspondence on a generic smooth curve extends to a semistable model, this static action will be the special-fiber shadow of its action on generic cohomology. The extension hypothesis matters: a generic correspondence always acts on the generic representation, but without a controlled closure its specialization may acquire vertical components and need not be described by a naive map of dual graphs.

## 19. Semistable reduction and local Galois action

A semistable special fiber is not merely a singular curve waiting to be computed. It is the record of how a smooth curve degenerates. Proper base change identifies cohomology near the closed point with cohomology of that singular fiber, but smooth local acyclicity fails at the nodes. The failure produces inertia and a nilpotent operator on the generic $H^1$.

The aim of this chapter is a curve-specific semistable comparison. It is obtained by combining the proper comparison and duality theorems of Books 22 and 23 with the explicit two-branch calculation at each node. No assertion here applies when the coefficient prime equals the residue characteristic.

### 19.1 The trait and its three fibers

Let $R$ be a strictly henselian discrete valuation ring with fraction field $K$, uniformizer $\pi$, and separably closed residue field $k$ of characteristic $p$. Let

$$
f:\mathcal C\longrightarrow\operatorname{Spec}R
$$

be proper and flat. Assume that $\mathcal C$ is regular, the geometric generic fiber $C_{\bar K}$ is smooth and connected, and the special fiber $C_0$ is reduced with ordinary double points. Étale locally at every node, the family has equation

$$
xy=\pi. \tag{19.1}
$$

These are the strict semistable hypotheses. Let $\Gamma$ be the dual graph of $C_0$ and let $g_v$ be the genera of its normalized components. Flatness keeps the arithmetic genus constant, so if the generic genus is $g$, then

$$
g=\sum_v g_v+b_1(\Gamma). \tag{19.2}
$$

There are three cohomological objects that must not be conflated:

$$
R\Gamma(\mathcal C,\Lambda),
\qquad
R\Gamma(C_0,\Lambda),
\qquad
R\Gamma(C_{\bar K},\Lambda).
$$

Proper base change identifies the first with the second because the base is strictly local. It also constructs a specialization map

$$
\operatorname{sp}:H^i(C_0,\Lambda)
\longrightarrow H^i(C_{\bar K},\Lambda). \tag{19.3}
$$

The direction is from special to generic: it is the generization map of the proper higher direct image. The map need not be an isomorphism. On the smooth locus of $f$, local acyclicity says there is no defect. Thus every defect in (19.3) is supported at the nodes.

For a smooth model there are no nodes, $R^if_*\Lambda$ is lisse, and (19.3) is an isomorphism. Since the base is strictly henselian, this says that inertia acts trivially on generic cohomology. That is the good-reduction case. The semistable case replaces trivial inertia by a precisely controlled unipotent action.

### 19.2 The local calculation at $xy=\pi$

The equation (19.1) contains the entire local mechanism. The punctured special fiber has two branches, $x=0$ and $y=0$. A section on the normalization descends exactly when its two values at the origin agree. This is the local source of the difference map in (18.1).

The punctured generic fiber is an annulus. With prime-to-$p$ coefficients it has one degree-one Kummer class. One may represent it by extracting compatible $\ell^m$th roots of $x$; since $xy=\pi$, extracting roots of $y$ gives the negative class after the constant class of $\pi$ is accounted for. The boundary of this annular class is the difference of the two branch residues. Thus the local comparison is governed by the two-term complex

$$
\Lambda^{\{\text{branches}\}}
\xrightarrow{(a,b)\mapsto b-a}
\Lambda^{\{\text{node}\}}. \tag{19.4}
$$

To pass from one node to the whole curve, cover $\mathcal C$ by the smooth locus and small node neighborhoods. The smooth pieces contribute no vanishing cohomology. The overlap maps assemble the local difference maps (19.4) into the incidence map

$$
\Lambda^V\longrightarrow\Lambda^E
$$

of the dual graph. A node therefore does not automatically contribute an independent global vanishing class. Relations at vertices remove the tree edges; precisely $b_1(\Gamma)$ independent annular classes remain.

This also gives a dimension check. By (18.6) and (19.2),

$$
\dim H^1(C_0,\mathbf Q_\ell)
=2\sum_vg_v+b_1(\Gamma),
$$

whereas

$$
\dim H^1(C_{\bar K},\mathbf Q_\ell)
=2g=2\sum_vg_v+2b_1(\Gamma).
$$

The difference is $b_1(\Gamma)$, exactly the number of global annular classes. For a nodal cubic the special rank is one and the generic elliptic rank is two. For two smooth components joined by one node, the graph is a tree and no rank is lost.

### 19.3 Invariant cycles and monodromy

Fix $\ell\ne p$ and put

$$
V=H^1(C_{\bar K},\mathbf Q_\ell).
$$

Let $I_K\subset G_K$ be inertia. The $\ell$-primary tame character is

$$
t_\ell:I_K\longrightarrow\mathbf Z_\ell(1).
$$

The node calculation proves the following theorem.

**Semistable curve theorem.** Under the strict semistable hypotheses of Section 19.1:

1. wild inertia acts trivially on $V$;
2. there is a canonical nilpotent map

   $$
   N:V\longrightarrow V(-1),
   \qquad N^2=0,
   $$

   such that, after the natural tensor contraction with $t_\ell(\sigma)$,

   $$
   \rho(\sigma)=1+t_\ell(\sigma)N
   \qquad(\sigma\in I_K);
   \tag{19.5}
   $$

3. specialization induces an isomorphism

   $$
   H^1(C_0,\mathbf Q_\ell)
   \xrightarrow{\sim}V^{I_K}=\ker N;
   \tag{19.6}
   $$

4. $\operatorname{rank}N=b_1(\Gamma)$.

Here (19.5) is intrinsic despite its compact notation: $t_\ell(\sigma)$ has twist $(1)$ and $N$ has twist $(-1)$, so their product is an endomorphism of $V$.

**Proof strategy.** First compute the action locally on the annulus, then glue the local classes through the incidence complex.

On a smooth chart, universal local acyclicity makes inertia trivial. On a node chart, compatible roots of $x$ describe the tame tower of the annulus. Wild inertia has pro-$p$ image and cannot act nontrivially on this prime-to-$p$ tower. A tame generator changes a chosen root by a root of unity, so its action is a transvection. Its logarithm is the rank-one local map from the annular class to the branch-difference class. A transvection has square-zero logarithm.

Gluing all node charts gives a sum of these local logarithms. The incidence relations at vertices show that its independent image has dimension $b_1(\Gamma)$; the composite of two local logarithms is zero because the first lands in the graph subspace on which every local logarithm vanishes. Hence $N^2=0$ and (19.5) follows.

The same gluing complex compares special classes with invariant generic classes. Its kernel is the graph cohomology and its quotient is the direct sum of component $H^1$ groups, exactly as in (18.4). Thus the map to $\ker N$ has the same graph subobject and component quotient. It is an isomorphism on both, hence an isomorphism in the middle. This proves (19.6). Finally the dimension difference computed in Section 19.2 gives $\operatorname{rank}N=b_1(\Gamma)$. $\square$

The proof produces a useful filtration

$$
0\subset W_0\subset W_1\subset W_2=V, \tag{19.7}
$$

where $W_1=\ker N=V^{I_K}$ and $W_0$ is the graph subspace. Its graded pieces are

$$
\operatorname{Gr}_0^W V\cong H^1(\Gamma,\mathbf Q_\ell),
$$

$$
\operatorname{Gr}_1^W V
\cong\bigoplus_vH^1(C_v,\mathbf Q_\ell),
$$

$$
\operatorname{Gr}_2^W V
\cong H_1(\Gamma,\mathbf Q_\ell)(-1). \tag{19.8}
$$

The map $N$ induces an isomorphism

$$
\operatorname{Gr}_2^W V
\xrightarrow{\sim}
\operatorname{Gr}_0^W V(-1). \tag{19.9}
$$

For a strict semistable model the edge pairing identifies graph homology with the dual of graph cohomology and gives (19.9). If a nonregular model has equations $xy=\pi^{n_e}$, the edge lengths $n_e$ enter that pairing; rationally the same filtration remains, while integral saturation can change. This is why the clean theorem above assumes a regular total space and states the comparison first over $\mathbf Q_\ell$.

Poincaré duality on the generic curve is compatible with this filtration. In the untwisted form the alternating pairing is

$$
V\times V\longrightarrow\mathbf Q_\ell(-1).
$$

Differentiating inertia invariance gives the skew-adjoint relation

$$
\langle Nx,y\rangle+\langle x,Ny\rangle=0, \tag{19.10}
$$

with the evident twists. The graph pieces in degrees $0$ and $2$ pair with one another, and the component piece carries the direct sum of the smooth component pairings. This recovers, on the generic fiber, the dualizing-complex correction seen on the singular fiber.

### 19.4 Unramified and semistable representations

A continuous $\ell$-adic representation of $G_K$ is **unramified** if inertia acts trivially. It is **semistable in the curve-theoretic prime-to-$p$ sense** used here if inertia acts unipotently with square-zero logarithm as in (19.5). This terminology describes the representation produced by a semistable curve; it should not be confused with coefficient-prime theories used when $\ell=p$.

If $\mathcal C/R$ is smooth proper, smooth proper base change gives

$$
H^1(C_0,\mathbf Q_\ell)
\xrightarrow{\sim}H^1(C_{\bar K},\mathbf Q_\ell),
$$

and the right side is unramified. This is the cohomological good-reduction theorem.

For a strict semistable model, (19.5) shows that the representation is unramified precisely when $N=0$. By the rank formula, this is equivalent to

$$
b_1(\Gamma)=0,
$$

or equivalently to $\Gamma$ being a tree. Thus a semistable curve of **compact type** has unramified $H^1$ even when the curve itself has bad reduction.

This gives an important counterexample to a tempting converse. Let the special fiber be two smooth positive-genus curves meeting transversely in one point. Its graph is a tree, so $H^1$ is unramified, but the special fiber is reducible and the curve does not have good reduction in that model. Cohomology detects the toric loop part of the degeneration, not every singularity of the curve.

If a curve becomes semistable only after a finite extension $K'/K$, restriction to $G_{K'}$ has the form (19.5). Hence inertia over $K$ acts quasi-unipotently: after an open subgroup its action is unipotent. A finite residual action may remain before the extension. One must therefore distinguish “unramified over $K$,” “semistable over $K$,” and “potentially semistable after a finite extension.”

The coefficient restriction remains visible. None of these arguments applies to $\ell=p$: the tame character no longer captures the relevant local cohomology, wild inertia is not cohomologically negligible, and the inverse systems used here are not a substitute for a residue-characteristic comparison theory.

### 19.5 Frobenius, monodromy, and correspondences

Suppose now that $R$ is henselian with finite residue field $\mathbf F_q$; make the preceding construction after strict henselization. A lift of residue-field Frobenius acts on $V$, on the geometric special fiber, and on its dual graph. The filtration (19.7) is stable under this action.

Let $F_{\mathrm{arith}}$ and $F_{\mathrm{geom}}=F_{\mathrm{arith}}^{-1}$ denote arithmetic and geometric Frobenius. After choosing a basis of the twist in which $N$ is viewed as a matrix, the tame relation gives

$$
F_{\mathrm{arith}}NF_{\mathrm{arith}}^{-1}=qN,
\qquad
F_{\mathrm{geom}}NF_{\mathrm{geom}}^{-1}=q^{-1}N. \tag{19.11}
$$

Intrinsically, (19.11) says that $N:V\to V(-1)$ has exactly the Frobenius covariance imposed by its twist. On $\operatorname{Gr}_0^W$, Frobenius acts through the finite combinatorial action on the graph. On $\operatorname{Gr}_1^W$, it acts on the $H^1$ of the normalized components. The top graph piece is the dual graph-homology action with the twist $(-1)$. These statements determine the semistable Frobenius action up to the extensions in (19.7); no semisimplicity is asserted.

Every correspondence on the generic curve defined over $K$ commutes with $G_K$, hence with inertia, Frobenius, and $N$. If it extends to a properly supported correspondence of semistable models and its closure has controlled normalized legs, it also acts on the special normalization and dual graph. The invariant-cycle isomorphism (19.6) then fits into a commutative square

$$
\begin{array}{ccc}
H^1(C_0,\mathbf Q_\ell)&\xrightarrow{\operatorname{sp}}&V^{I_K}\\
\downarrow\Gamma_*&&\downarrow\Gamma_*\\
H^1(C_0,\mathbf Q_\ell)&\xrightarrow{\operatorname{sp}}&V^{I_K}.
\end{array} \tag{19.12}
$$

The action preserves (19.7), acts separately on graph and component graded pieces, and commutes with (19.9). Transpose remains adjoint for the generic Poincaré pairing and, on the special fiber, for the dualizing-complex pairing. If the closure acquires vertical components, these must be retained in the special correspondence; discarding them can destroy (19.12).

## 20. The cohomological representation attached to a curve

The constructions can now be assembled without hiding their coefficient topology, their variance, or their behavior at bad places. The central object is $H^1$ of the geometric smooth proper curve. Its importance comes from the structures that meet there: Galois descent, the alternating cup product, specialization, and the pull-push action of correspondences.

### 20.1 Construction and functoriality

Let $C/k$ be smooth, proper, and geometrically connected of genus $g$, and let $\ell\ne\operatorname{char}k$. Define

$$
T_\ell(C)=
H^1_{\mathrm{\acute et}}(C_{k^s},\mathbf Z_\ell)
=\varprojlim_m
H^1_{\mathrm{\acute et}}(C_{k^s},\mathbf Z/\ell^m\mathbf Z)
$$

and

$$
V_\ell(C)=T_\ell(C)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

This notation is cohomological: $T_\ell(C)$ is the integral cohomology lattice, not a torsion-point module. The finite-level groups are finite and their reductions are surjective, so the derived-limit correction vanishes. Chapter 15 proved finite-level freeness, hence

$$
T_\ell(C)\cong\mathbf Z_\ell^{,2g},
\qquad
\dim_{\mathbf Q_\ell}V_\ell(C)=2g. \tag{20.1}
$$

Descent gives a continuous action

$$
\rho_{C,\ell}:G_k\longrightarrow
\operatorname{GL}(T_\ell(C))
$$

and therefore a continuous rational representation on $V_\ell(C)$. Continuity is not an extra theorem after the limit: the stabilizer of every class modulo $\ell^m$ is open, and the congruence quotients define the topology of the lattice.

Cup product gives a perfect alternating $G_k$-equivariant pairing

$$
V_\ell(C)\times V_\ell(C)
\longrightarrow\mathbf Q_\ell(-1). \tag{20.2}
$$

Equivalently, after choosing a basis of $\mathbf Q_\ell(-1)$, the representation is symplectic up to the inverse cyclotomic multiplier. The twist is not removable from the canonical statement.

A morphism $f:C\to D$ gives contravariant pullback

$$
f^*:V_\ell(D)\longrightarrow V_\ell(C).
$$

If $f$ is nonconstant, it is finite and trace gives

$$
f_*:V_\ell(C)\longrightarrow V_\ell(D),
$$

with

$$
f_*f^*=(\deg f)\operatorname{id},
\qquad
\langle f^*x,y\rangle_C=\langle x,f_*y\rangle_D. \tag{20.3}
$$

All maps preserve the integral lattices and are $G_k$-equivariant when $f$ is defined over $k$.

### 20.2 The commuting-action theorem

Let $\operatorname{Corr}_k(C)$ be a ring of algebraic self-correspondences on $C$ generated by cycles whose moving components are finite over both factors. A component supported on a point times $C$, or on $C$ times a point, acts trivially on $H^1$ and may be included without changing the following statement. For a moving integral component with normalized projections

$$
C\xleftarrow{p_1}\Gamma^\nu\xrightarrow{p_2}C,
$$

define

$$
[\Gamma]_*=(p_2)_*p_1^*.
$$

**Commuting-action theorem.** The space $V_\ell(C)$ has the following compatible structures:

1. a continuous $2g$-dimensional action of $G_k$;
2. an action of $\operatorname{Corr}_k(C)$ by $\mathbf Q_\ell$-linear endomorphisms;
3. the perfect pairing (20.2), for which transpose correspondences are adjoint.

The two actions commute. Equivalently, there is a ring homomorphism

$$
\operatorname{Corr}_k(C)
\longrightarrow
\operatorname{End}_{\mathbf Q_\ell[G_k]}(V_\ell(C)), \tag{20.4}
$$

and

$$
\langle[\Gamma]_*x,y\rangle
=\langle x,[{}^t\Gamma]_*y\rangle. \tag{20.5}
$$

**Proof.** Pullback and trace were constructed at every finite coefficient level and commute with coefficient reduction. Their inverse limits therefore preserve $T_\ell(C)$ and act continuously on it. Composition of correspondences agrees with composition of pull-push maps by the projection formula and the refined multiplicities in the fiber product. Since the cycle, both projections, and all trace maps descend to $k$, functoriality of the descent action gives

$$
\sigma[\Gamma]_*=[\Gamma]_*\sigma
$$

for every $\sigma\in G_k$. Finally, moving pullback across the cup product by the projection formula turns $[\Gamma]_*$ into the pull-push map for the transposed cycle, proving (20.5). $\square$

The field of definition is essential. If $\Gamma$ is defined only over $k'/k$, its operator commutes with $G_{k'}$, not automatically with $G_k$. Galois invariance of a characteristic polynomial is weaker than descent of the cycle and does not supply (20.4). Summing the Galois conjugates produces a descended operator, but can destroy properties such as idempotence.

For a lisse rational coefficient sheaf $\mathcal V$, the same construction works only after a coefficient morphism

$$
p_1^*\mathcal V\longrightarrow p_2^*\mathcal V
$$

has been specified. A geometric cycle alone does not canonically identify unrelated pulled-back local systems. Constant coefficients are special precisely because this datum is automatic.

### 20.3 Good and semistable places

Suppose $k$ is a global field, or more generally that $C$ is viewed over the fraction field of a henselian discrete valuation ring at a place $v$ of residue characteristic $p\ne\ell$.

If $C$ extends to a smooth proper curve over the valuation ring, smooth proper base change shows that $V_\ell(C)$ is unramified at $v$. Its Frobenius action is identified with that on the geometric special fiber. With geometric Frobenius $F_v$, the local cohomological polynomial is naturally written

$$
P_v(T)=\det\bigl(1-TF_v\mid V_\ell(C)\bigr). \tag{20.6}
$$

Using arithmetic Frobenius replaces $F_v$ by $F_v^{-1}$. The top cohomology convention from Chapter 12 gives geometric Frobenius eigenvalue $q_v$ on $H^2$, so there is no ambiguity once (20.6) is fixed.

If $C$ has strict semistable reduction, inertia acts by

$$
\rho(\sigma)=1+t_\ell(\sigma)N,
\qquad N^2=0,
$$

and

$$
\operatorname{rank}N=b_1(\Gamma_v). \tag{20.7}
$$

The invariant space is the cohomology of the geometric special fiber:

$$
V_\ell(C)^{I_v}
\cong H^1(C_{\bar v},\mathbf Q_\ell). \tag{20.8}
$$

Its graph, component, and vanishing pieces are given by (19.7)--(19.9). A local polynomial for the semistable representation uses the invariant space,

$$
P_v(T)=\det\bigl(1-TF_v\mid V_\ell(C)^{I_v}\bigr), \tag{20.9}
$$

with geometric Frobenius. Formula (20.9) records the unramified quotient of the local action; the omitted information is exactly the nilpotent map $N$.

Every correspondence defined over the local field commutes with inertia and Frobenius, hence preserves $V^{I_v}$ and commutes with $N$. If it extends over a semistable model, it acts on the graph and component descriptions of the graded pieces. Therefore (20.6) and (20.9) may be decomposed into simultaneous correspondence-stable factors whenever an actual idempotent acts over the chosen coefficient field. An integral splitting requires the idempotent denominators to be $\ell$-adic units.

No assertion of purity, a point-counting trace formula, or independence of $\ell$ is needed to obtain this commuting local structure. Those are distinct theorems. The present result supplies the representation, the Frobenius convention, the inertia operator, and the correspondence algebra on which such theorems can later operate.

### 20.4 Conclusion

Étale cohomology begins with a modest failure: local lifts of a sheaf section need not glue globally. Following that failure through torsors, derived sections, localization, and higher direct images reveals the global geometry of a curve. Geometric stalks make exactness local, constructibility makes the groups finite, and compact support records what occurs at omitted points. Kummer theory turns units and divisors into classes, while purity identifies the local class of a point. Their sum is the degree-two trace.

The trace is the pivot of the smooth theory. Cup product followed by trace pairs complementary degrees, explains the rank $2g$, and makes pullback adjoint to pushforward. On open curves, compact support and residue sum supply the missing boundary half of duality. Passing through finite $\ell^m$-coefficients preserves topology and exposes every possible derived-limit and torsion correction before rationalization.

Semistable curves show the exact frontier of those smooth formulas. Normalization separates component cohomology from graph cohomology. The dualizing complex corrects ordinary Poincaré duality at a node. In a smoothing, each graph circuit has a second, vanishing direction; tame inertia acts by a transvection, its logarithm has rank $b_1(\Gamma)$, and special-fiber cohomology is the invariant-cycle space. Good reduction is the case of trivial inertia, while compact-type bad reduction shows that unramified $H^1$ does not by itself certify a smooth model.

The final object

$$
V_\ell(C)=H^1_{\mathrm{\acute et}}(C_{k^s},\mathbf Q_\ell)
$$

is therefore more than a vector space of dimension $2g$. It is a continuous Galois representation with a Tate-twisted alternating pairing, functorial pullbacks and traces, and a commuting action of algebraic correspondences. At good places it carries unramified Frobenius; at semistable places it carries commuting Frobenius and nilpotent monodromy. This joint Galois--correspondence structure is the reusable cohomological realization of a curve.
