# Generalized Elliptic Curves and Level Structures

## Contents

1. [Why elliptic curves need a boundary](#1-why-elliptic-curves-need-a-boundary)
   - [The moduli problem at a cusp](#11-the-moduli-problem-at-a-cusp)
   - [Conventions and recalled foundations](#12-conventions-and-recalled-foundations)
   - [What the boundary must remember](#13-what-the-boundary-must-remember)
2. [Néron polygons](#2-néron-polygons)
   - [The standard $n$-gon](#21-the-standard-n-gon)
   - [The smooth group and its action](#22-the-smooth-group-and-its-action)
   - [Torsion and component arithmetic](#23-torsion-and-component-arithmetic)
   - [Forms and automorphisms](#24-forms-and-automorphisms)
3. [Generalized elliptic curves](#3-generalized-elliptic-curves)
   - [The definition](#31-the-definition)
   - [Fiberwise geometry and the smooth locus](#32-fiberwise-geometry-and-the-smooth-locus)
   - [Descent and base change](#33-descent-and-base-change)
   - [Rigidity of the action](#34-rigidity-of-the-action)
4. [Divisors that see the components](#4-divisors-that-see-the-components)
   - [Sums of sections](#41-sums-of-sections)
   - [The ampleness criterion](#42-the-ampleness-criterion)
   - [Orbit divisors](#43-orbit-divisors)
   - [Component bounds](#44-component-bounds)
5. [Finite subgroup divisors and Drinfeld generators](#5-finite-subgroup-divisors-and-drinfeld-generators)
   - [Why pointwise generation fails](#51-why-pointwise-generation-fails)
   - [Full sets of sections](#52-full-sets-of-sections)
   - [Drinfeld generators](#53-drinfeld-generators)
   - [Behavior when the order is invertible](#54-behavior-when-the-order-is-invertible)
6. [Full, $\Gamma_1$, and $\Gamma_0$ level](#6-full-gamma_1-and-gamma_0-level)
   - [$\Gamma_1(N)$-structures](#61-gamma_1n-structures)
   - [$\Gamma_0(N)$-structures](#62-gamma_0n-structures)
   - [Full level and the Weil pairing](#63-full-level-and-the-weil-pairing)
   - [Comparison and forgetful maps](#64-comparison-and-forgetful-maps)
7. [Level on a polygon](#7-level-on-a-polygon)
   - [The component calculation](#71-the-component-calculation)
   - [The prime-level alternatives](#72-the-prime-level-alternatives)
   - [Full prime level](#73-full-prime-level)
   - [Automorphisms and rigidity](#74-automorphisms-and-rigidity)
8. [Contraction of generalized elliptic curves](#8-contraction-of-generalized-elliptic-curves)
   - [The problem solved by contraction](#81-the-problem-solved-by-contraction)
   - [Fiberwise contraction](#82-fiberwise-contraction)
   - [Relative construction and uniqueness](#83-relative-construction-and-uniqueness)
   - [Equivariance and level](#84-equivariance-and-level)
9. [Quotients and isogenies at the boundary](#9-quotients-and-isogenies-at-the-boundary)
   - [Quotients of the smooth group](#91-quotients-of-the-smooth-group)
   - [Extension across the nodes](#92-extension-across-the-nodes)
   - [The two degree-$p$ quotient formulas](#93-the-two-degree-p-quotient-formulas)
   - [Duality and degree bookkeeping](#94-duality-and-degree-bookkeeping)
10. [Tate curves as cusp coordinates](#10-tate-curves-as-cusp-coordinates)
    - [The one-gon chart](#101-the-one-gon-chart)
    - [The $n$-gon model](#102-the-n-gon-model)
    - [Sections and specialization](#103-sections-and-specialization)
    - [The deformation parameter](#104-the-deformation-parameter)
11. [Tate charts with level](#11-tate-charts-with-level)
    - [Full level](#111-full-level)
    - [$\Gamma_1(N)$ cusp charts](#112-gamma_1n-cusp-charts)
    - [$\Gamma_0(p)$ cusp charts](#113-gamma_0p-cusp-charts)
    - [Change of cusp coordinate](#114-change-of-cusp-coordinate)
12. [Prime-level moduli interpretations](#12-prime-level-moduli-interpretations)
    - [The three fibered moduli problems](#121-the-three-fibered-moduli-problems)
    - [Representability of level over a fixed curve](#122-representability-of-level-over-a-fixed-curve)
    - [Boundary strata and their closures](#123-boundary-strata-and-their-closures)
    - [Fine and stacky behavior](#124-fine-and-stacky-behavior)
13. [Degeneracy maps at prime level](#13-degeneracy-maps-at-prime-level)
    - [Forgetting and quotienting](#131-forgetting-and-quotienting)
    - [The two cusp formulas](#132-the-two-cusp-formulas)
    - [Compatibility with contraction and base change](#133-compatibility-with-contraction-and-base-change)
    - [What the formulas predict](#134-what-the-formulas-predict)
14. [The completed boundary package](#14-the-completed-boundary-package)
    - [A dependency-closed theorem summary](#141-a-dependency-closed-theorem-summary)
    - [The boundary passed to compactification](#142-the-boundary-passed-to-compactification)
    - [Conclusion](#143-conclusion)

## 1. Why elliptic curves need a boundary

### 1.1 The moduli problem at a cusp

An elliptic curve is proper, but the family of all elliptic curves is not. The simplest witness is a Tate curve. If $R$ is a complete discrete valuation ring and $q\in R$ has positive valuation, the generic fiber $E_q$ is smooth, while its minimal integral cubic has special fiber

$$
y^2+xy=x^3,
$$

a nodal rational curve. Refusing this fiber would mean that a perfectly meaningful one-parameter family has no limit in the moduli problem. Accepting the nodal cubic without further structure would lose the group law on the smooth fibers and, after ramified base change, would hide the cycle of components that measures the valuation of $q$.

The right boundary object is a generalized elliptic curve. Its total curve is allowed to be a cycle of projective lines, its smooth locus remains a commutative group, and that group acts on the whole curve by translations. The action is the organizing datum: it marks the identity component, rotates the other components, and makes torsion and level meaningful at the boundary.

Level structure creates a second difficulty. Away from its order, a level-$N$ basis is literally a basis of the $N$-torsion points. At a prime dividing $N$, torsion sections may collide. On $\mu_p$ in characteristic $p$, every geometric section can be the identity even though the group scheme has rank $p$. The integral definition must remember the divisor cut out by all sections with multiplicity, not merely the set of their values. Drinfeld structures do exactly this.

This book develops the boundary objects and the integral level notions together. The endpoint is not yet a compactified modular stack or a coarse modular curve. It is the complete geometric input for constructing them: polygons, generalized elliptic curves, ample level divisors, contractions, quotient isogenies, Tate cusp charts, and the prime-level moduli interpretations.

### 1.2 Conventions and recalled foundations

All schemes are locally noetherian when a relative contraction or a finite-presentation assertion is used; statements defined fiberwise or by descent remain valid over arbitrary bases after the indicated limit argument. For $E\to S$ we write $E^{\mathrm{sm}}$ for the largest open on which the structural morphism is smooth. A geometric fiber means a fiber over an algebraically closed field. A finite locally free scheme has constant rank only locally on the base.

We use the following established background. Proper flat families of curves, effective Cartier divisors, relative ampleness, relative Proj, and relative Hilbert schemes of finite subschemes have their usual meanings. On a smooth relative curve, a finite locally free closed subscheme is an effective Cartier divisor, and sums of sections commute with arbitrary base change. Finite locally free commutative group schemes, Cartier duality, elliptic-curve torsion, the Weil pairing, and quotients by finite subgroup schemes are also available. Descent of schemes, line bundles, group laws, sections, and morphisms is effective for faithfully flat quasi-compact covers.

Two earlier local results will be used in concrete form. The Tate curve with parameter $q$ has equation

$$
y^2+xy=x^3+a_4(q)x+a_6(q),
$$

where $a_4,a_6\in q\mathbf Z[[q]]$, and

$$
\Delta(q)=q\prod_{r\geq1}(1-q^r)^{24}.
$$

It is uniformized by $\mathbf G_m/q^{\mathbf Z}$. If $q=t^n$, resolution of its node produces a cycle of $n$ components, and the class of a parameter $u$ meets the component numbered $v_t(u)$ modulo $n$. These facts connect the formal cusp coordinate with the polygonal boundary.

No assertion below uses a later compactification theorem. When a moduli stack is mentioned, only stackhood and the relative parameter spaces already supplied by the general theory of moduli stacks are used. Properness, regularity, coarse spaces, and special-fiber intersection theorems belong to the next stages of the theory.

### 1.3 What the boundary must remember

Four pieces of information survive degeneration and must be kept simultaneously.

First, the identity survives as a section through the smooth locus. Second, the smooth points retain a group law, but the singular nodes do not belong to the group. Third, translation must extend to the complete curve; otherwise the components have no intrinsic relation to the group. Fourth, a level divisor must meet every component. A subgroup supported only on the identity component may be perfectly finite and flat, yet it cannot rigidify or embed the invisible components.

These requirements explain the form of every later definition. They also prevent three tempting substitutes. A stable genus-one curve remembers the node but not necessarily the translation action. A smooth group scheme remembers local points but omits the proper boundary. A collection of torsion sections remembers too little when sections collide. A generalized elliptic curve with an ample Drinfeld divisor retains all three geometric layers.

There is a useful valuative picture behind this list. Let $K$ be the fraction field of a DVR and suppose an elliptic curve over $K$ has split multiplicative reduction. Its smooth model has identity component $\mathbf G_m$, but it is not proper. Completing it by one node gives a one-gon, while after a ramified extension of index $n$ the minimal regular completion has $n$ components. The generic elliptic curve did not acquire new dimension; the valuation scale acquired $n$ distinguishable residue classes. The polygon stores those classes. A level point whose Tate parameter has valuation prime to $n$ visits them all, while a root of unity stays on the identity component. Ampleness is exactly the demand that the chosen level retain the whole new valuation scale.

The theory also distinguishes a boundary object from a compactification. A boundary object is an individual permitted degeneration together with its symmetries. A compactification is a global geometric object representing all such families and satisfying a valuative extension theorem. Constructing the first is necessary but not sufficient for the second. The present book proves the stability, descent, boundedness, and formal-chart statements that make the later global construction possible.

## 2. Néron polygons

### 2.1 The standard $n$-gon

Let $S$ be a scheme and $n\geq1$. Take copies $P_i\simeq\mathbf P^1_S$ indexed by $i\in\mathbf Z/n\mathbf Z$, with standard sections $0_i$ and $\infty_i$. Glue $\infty_i$ to $0_{i+1}$. The pushout exists because the gluing loci are disjoint effective Cartier divisors. The resulting curve is the **standard Néron $n$-gon** $C_n\to S$.

The morphism $C_n\to S$ is proper, flat, and finitely presented. Every geometric fiber is connected and has arithmetic genus one. Indeed, normalization is the disjoint union of $n$ projective lines. The normalization exact sequence

$$
0\longrightarrow\mathcal O_{C_n}
\longrightarrow\bigoplus_i\mathcal O_{P_i}
\longrightarrow\bigoplus_i\mathcal O_{S,i}\longrightarrow0
$$

has the last map given by the differences of the values on the two branches at each node. On a geometric fiber its cokernel on global sections is one-dimensional: constants on all components must agree, while the cycle contributes one first cohomology class. Hence $h^0=h^1=1$ and the arithmetic genus is one.

For $n=1$, the two sections $0$ and $\infty$ of one projective line are identified. This is the nodal cubic up to a choice of plane embedding. For $n\geq2$, adjacent components meet transversely. The dual graph is a cycle with $n$ vertices. The graph is not extra data: the group action below gives it a cyclic origin.

The curve is Gorenstein. The completed local ring at a node is $A[[x,y]]/(xy)$ over an affine base ring $A$, a hypersurface and hence Gorenstein. On the normalization, the relative dualizing sheaf consists of rational differentials with at most simple poles above each node and opposite residues on the two branches. The forms $dz_i/z_i$ have residue $1$ at $0_i$ and $-1$ at $\infty_i$, so they glue cyclically. This gives

$$
\omega_{C_n/S}\simeq\mathcal O_{C_n}.
$$

The triviality explains why the arithmetic genus remains one no matter how many rational components occur. Each added component is balanced by one added node.

### 2.2 The smooth group and its action

Removing the nodes from each component leaves one copy of $\mathbf G_m$. Thus

$$
C_n^{\mathrm{sm}}\simeq\mathbf G_{m,S}\times(\mathbf Z/n\mathbf Z)_S.
$$

Write a point as $(u,i)$. Multiplication

$$
(u,i)(v,j)=(uv,i+j)
$$

makes the smooth locus a commutative smooth separated group with identity $(1,0)$. It acts on $C_n$: on the normalization, $(u,i)$ sends the component $P_j$ to $P_{i+j}$ and sends its affine coordinate $z$ to $uz$. Scaling fixes $0$ and $\infty$, so the maps respect the gluing and descend.

The action is transitive on components. Its identity component is $\mathbf G_m\times\{0\}$, and its component group is the constant cyclic group $\mathbf Z/n\mathbf Z$. On every component the identity component acts with open orbit $\mathbf G_m$ and fixes the two boundary nodes.

This formula proves that a polygon is more than a semistable curve. The component labels, their cyclic order, the distinguished identity component, and the toric coordinate all arise from one action. Any construction at a cusp that changes the polygon must respect this action if it is to remain modular.

The formula also proves uniqueness of the standard action once the identity component and orientation are fixed. Translation by $(u,0)$ must act as multiplication by $u$ on the identity component. A translation carrying component $0$ to component $i$ transports that coordinate to component $i$. Compatibility at $0$ and $\infty$ forces the same scaling on adjacent branches. Induction around the cycle determines the action everywhere.

### 2.3 Torsion and component arithmetic

Multiplication by $N$ on the smooth group is

$$
[N](u,i)=(u^N,Ni).
$$

Consequently its kernel fits into

$$
0\longrightarrow\mu_N
\longrightarrow C_n^{\mathrm{sm}}[N]
\longrightarrow(\mathbf Z/n\mathbf Z)[N]
\longrightarrow0.
$$

The last group has order $\gcd(N,n)$. Therefore

$$
\operatorname{rank}C_n^{\mathrm{sm}}[N]
=N\gcd(N,n). \tag{2.1}
$$

This elementary formula is one of the main safeguards of the subject. The kernel on a singular generalized elliptic curve does not automatically have rank $N^2$. It has that rank precisely when $N\mid n$. If it is also to meet every component, multiplication by $N$ must kill the entire component group, so $n\mid N$. Both conditions together force $n=N$.

More generally, let $P=(a,r)$ be a section killed by $N$. Then $a^N=1$ and $Nr=0$ in $\mathbf Z/n\mathbf Z$. The divisor

$$
D_P=\sum_{b\in\mathbf Z/N\mathbf Z}[bP]
$$

meets precisely the components in the subgroup generated by $r$. It meets every component exactly when $r$ generates $\mathbf Z/n\mathbf Z$. In that case $n\mid N$. This is the source of the boundary divisibility condition for $\Gamma_1(N)$ and $\Gamma_0(N)$.

If $r$ has order $d$, the orbit visits $d$ components and visits each one $N/d$ times. When the residue characteristic divides $N/d$, these repetitions can form a nonreduced multiplicative divisor. The same formula therefore accounts for component coverage and infinitesimal thickness. It is unsafe to replace it by the claim that the orbit has $N$ distinct points.

### 2.4 Forms and automorphisms

A Néron $n$-gon over a field need not be presented with labeled components or split tangent branches. By definition it is a curve that becomes isomorphic to $C_n$ after a finite separable extension, together with the descended generalized elliptic action. The component group can therefore be a twisted cyclic étale group, and a one-gon can have a nonsplit torus as its smooth identity component. For the cusp charts used later, an étale cover supplies the split form and descent remembers the twisting.

The group automorphisms of a split $n$-gon that induce the identity on the component group include

$$
(u,i)\longmapsto(c^iu,i),\qquad c\in\mu_n.
$$

There is also inversion $(u,i)\mapsto(u^{-1},-i)$, which extends to the proper curve and reverses the polygon. These formulas explain both normalization of boundary level points and residual stabilizers. For example, a point $(a,1)$ of order $n$ can be sent to $(1,1)$ by choosing $c=a^{-1}$.

An automorphism of a generalized elliptic curve is required to preserve the identity, the group law on the smooth locus, and the action on the whole curve. Agreement on the smooth locus implies agreement everywhere because the smooth locus is schematically dense in every fiber and the curve is separated. Thus automorphisms can be computed on the group, provided one checks that they preserve the gluing at the nodes.

For example, on the split one-gon inversion exchanges the two branches of the node. Over a field where those branches are conjugate, Galois can act through the same exchange; the identity component is then a nonsplit torus. This is the boundary shadow of nonsplit multiplicative reduction. After the quadratic étale extension separating the branches, the form becomes the standard one-gon. Splitness twists the torus and orientation, not the geometric polygon size.

## 3. Generalized elliptic curves

### 3.1 The definition

A **generalized elliptic curve** over a scheme $S$ consists of:

- a proper, flat, finitely presented morphism $\pi:E\to S$ whose geometric fibers are connected curves of arithmetic genus one;
- a section $e:S\to E^{\mathrm{sm}}$;
- a commutative group structure on $E^{\mathrm{sm}}$ with identity $e$;
- an action

$$
m:E^{\mathrm{sm}}\times_SE\longrightarrow E
$$

restricting to the group law on $E^{\mathrm{sm}}$;
- the requirement that every geometric fiber is either a smooth elliptic curve or a Néron polygon, and that $E^{\mathrm{sm}}$ acts transitively on the irreducible components of every geometric fiber.

An isomorphism preserves all these data. A morphism called an isogeny later will be allowed to be finite and noninvertible, but an arrow in the moduli groupoid is always an isomorphism.

The action is explicitly included. Without it, a family of polygonal curves with a marked smooth point need not carry a compatible group law in families. Transitivity excludes tails or components disjoint from all translates of the identity component. Smooth elliptic fibers are included as the case in which the whole curve is its smooth group.

### 3.2 Fiberwise geometry and the smooth locus

The singular locus of a generalized elliptic curve is finite and unramified over the base on every stratum of fixed polygon size. Fiberwise it consists of the nodes. The complement $E^{\mathrm{sm}}$ is a smooth relative curve, and its identity component $E^{\mathrm{sm},0}$ is either an elliptic curve on the smooth locus of the base or a one-dimensional torus on a polygonal fiber.

On a geometric $n$-gon there is an exact sequence

$$
0\longrightarrow\mathbf G_m
\longrightarrow E^{\mathrm{sm}}
\longrightarrow\mathbf Z/n\mathbf Z
\longrightarrow0. \tag{3.1}
$$

The sequence can be twisted before passing to an algebraic closure, but its ranks and the transitive component action descend. The number $n$ is locally constant on a locally closed stratification of the singular base, not necessarily on all of $S$. A family may be smooth generically and polygonal specially.

The arithmetic genus and transitivity rule out several nearby degenerations. A chain of projective lines has a tree as dual graph and hence arithmetic genus zero. A cycle with an attached tail has genus one, but the smooth group cannot act transitively on all components while preserving the unique branching component. A cuspidal cubic has genus one and a smooth locus isomorphic to $\mathbf G_a$, but it is not a Néron polygon and is excluded because its degeneration is not semistable. These counterexamples show that no one clause of the definition makes the others redundant.

The dualizing sheaf of every geometric fiber is trivial. On the normalization of a polygon, a differential with simple poles at $0$ and $\infty$ and opposite residues glues around the cycle; in the coordinate $z$ it is $dz/z$. Translation preserves it. Thus the Hodge line

$$
\omega_{E/S}=e^*\Omega^1_{E^{\mathrm{sm}}/S}
$$

is the natural continuation of the invariant-differential line across the boundary. We use the line here only to compare Tate parameters; modular forms built from it belong to a later book.

The component group need not be represented by one finite étale group over a base on which polygon size jumps. On a stratum of fixed size $n$, the quotient $E^{\mathrm{sm}}/E^{\mathrm{sm},0}$ is finite étale of rank $n$. Near a specialization from a smooth fiber to a polygon, the identity component changes from proper to affine, so no global exact sequence with constant ranks should be asserted across both loci. Rank calculations below are made fiberwise and then promoted to the locally closed fixed-size strata.

### 3.3 Descent and base change

**Theorem 3.1 (descent).** Generalized elliptic curves form an fpqc stack, and their formation is stable under arbitrary base change.

**Proof strategy.** Descend the curve first, then the open smooth locus, then the algebraic operations. Check the geometric fiber conditions only after all structures exist.

**Proof.** Proper flat finitely presented schemes descend effectively. Smoothness commutes with base change and is fpqc local, so the opens $E_i^{\mathrm{sm}}$ descend to the smooth open of the descended curve. The identity, multiplication, inversion, and action descend because morphisms into a separated descended scheme satisfy fpqc descent. The group and action identities are equalities of morphisms and may be checked after the cover.

After a geometric base change, the given cover becomes faithfully flat. Being a smooth genus-one curve or a reduced cycle of projective lines with ordinary nodes is preserved and reflected by such field extension. Transitivity on the finite set of components is likewise geometric. Thus the descended object satisfies the definition. Isomorphisms descend uniquely, proving the prestack and effectivity assertions. Every step commutes with a further base change. $\square$

This theorem permits all later definitions to be checked after a convenient fppf cover. In particular, a cyclic subgroup may acquire a generator and a polygon may acquire labeled split components after such a cover without changing the intrinsic statement.

There is also useful diagonal control, but boundedness alone does not make the unlevelled diagonal proper. For two generalized elliptic curves $E,E'$ over $S$ with bounded component numbers, the isomorphism functor is representable, separated, quasi-finite, and of finite presentation. To see representability, choose auxiliary relatively ample bundles of bounded degree and embed both curves by high powers after a cover. An isomorphism is represented by its graph in $E\times_SE'$. Bounded component numbers bound the graph Hilbert polynomials, while being a graph whose two projections are inverse isomorphisms is open in the corresponding finite union of Hilbert schemes. Preserving the identity and action is closed. The construction descends from the cover. Fiberwise automorphism groups are finite, and density of the smooth locus gives separatedness.

The functor need not be proper. Over a discrete valuation ring, two polygonal models of the same generic elliptic curve can differ by contracting special-fiber components. Their generic fibers are isomorphic, but that isomorphism cannot extend to an isomorphism of the two proper models because their special fibers have different numbers of irreducible components. Level structures will restore properness of the diagonal only when their ample divisors forbid precisely these contractions. This distinction is essential in the moduli argument below.

### 3.4 Rigidity of the action

Several arguments extend maps from the smooth locus to the full curve. The needed principle is simple.

**Proposition 3.2 (density rigidity).** Let $S$ be locally noetherian, let $X\to S$ be flat and finitely presented with geometrically reduced one-dimensional fibers, and let $U\subset X$ meet every irreducible component in a fiberwise dense open. If $Y\to S$ is separated, two $S$-morphisms $X\to Y$ agreeing on $U$ agree everywhere.

**Proof.** The equalizer is closed because $Y$ is separated. Its defining ideal restricts to zero on $U$. Since $X$ is locally noetherian, an open is schematically dense if it contains every associated point of $X$. For a flat finitely presented morphism, each associated point of $X$ lies over an associated point of $S$ and is an associated point of the corresponding fiber. A reduced one-dimensional fiber has only the generic points of its irreducible components as associated points. The hypothesis on $U$ puts all of these points in $U$. Thus $U$ is schematically dense, the defining ideal is zero, and the equalizer is all of $X$. $\square$

The reducedness hypothesis cannot be dropped without replacement. A nilpotent function can vanish at every ordinary point of a nonreduced fiber. Generalized elliptic fibers are reduced, so density applies to maps of their curves. Finite level divisors can be nonreduced, however; equality there must be equality of Cartier ideals. The theory uses density for maps and divisor equality for level, never a point-set test in place of either.

For a generalized elliptic curve, $E^{\mathrm{sm}}$ has the required density. Consequently the extension of translation, an isogeny, or an automorphism across the nodes is unique if it exists. Associativity of an extended action may also be checked on the dense smooth locus. This converts many boundary proofs into an existence calculation on standard polygons followed by descent.

## 4. Divisors that see the components

### 4.1 Sums of sections

Let $C\to S$ be a relative curve and let $P:S\to C^{\mathrm{sm}}$ be a section. Its image is an effective Cartier divisor: locally a smooth parameter cuts it out by one non-zero-divisor. For finitely many sections, repetitions allowed, define

$$
\sum_i[P_i]
$$

by multiplying their ideal equations. The result is a relative effective Cartier divisor, finite locally free of degree equal to the number of terms. If sections collide, their multiplicities remain visible. The construction commutes with arbitrary base change.

On a group curve, a homomorphism from a constant finite abelian group $H$ to $E^{\mathrm{sm}}(S)$ therefore has an associated divisor

$$
D_\alpha=\sum_{h\in H}[\alpha(h)]. \tag{4.1}
$$

The divisor, rather than its support, is the integral record of the homomorphism. In characteristic $p$, the zero homomorphism from $\mathbf Z/p\mathbf Z$ gives $p[e]$, which can equal the nonreduced subgroup $\mu_p$ inside a suitable smooth group. Set-theoretically there is only one point; scheme-theoretically there are $p$ units of length.

### 4.2 The ampleness criterion

For a proper geometric curve whose irreducible components are $C_i$, an invertible sheaf $\mathcal L$ is ample if and only if

$$
\deg(\mathcal L|_{C_i})>0
\quad\text{for every }i. \tag{4.2}
$$

Necessity follows because an ample power embeds the curve and hence has positive degree on every component. For sufficiency, choose $m$ large enough that $\mathcal L^m$ has degree at least $2p_a(C)+1$ on every connected subcurve. The exact sequence obtained by removing one point and the vanishing of $H^1$ then show that sections separate points and tangent directions, including points on different components. Thus a high power is very ample.

In a proper flat family of semistable curves, the same criterion is fiberwise: $\mathcal L$ is relatively ample precisely when its degree is positive on every irreducible component of every geometric fiber. The forward implication is immediate. Conversely, positivity is open in the finite component stratification, and relative Serre theory turns a uniform high power into a closed immersion locally on a quasi-compact base.

Apply this to an effective Cartier divisor $D$ supported in the smooth locus of a generalized elliptic curve. Since

$$
\deg(\mathcal O_E(D)|_{C_i})
=\operatorname{length}(D\cap C_i),
$$

we obtain:

**Proposition 4.1.** The divisor $D$ is relatively ample if and only if it meets every irreducible component of every geometric fiber.

This is why ampleness belongs in the definition of compactified level. It is a concrete component-visibility condition, not an extra positivity convention.

For a polygon the proof is numerical. If $D$ has multidegree $(d_0,\ldots,d_{n-1})$, then

$$
\chi(\mathcal O_E(rD))=r\sum_i d_i
$$

because the arithmetic genus is one. If some $d_i=0$, every map defined by powers of $D$ contracts $C_i$, so ampleness fails. If all $d_i>0$, then for $r$ large the restriction to every component separates its two nodes and tangent directions. The normalization exact sequence glues these sections subject to one value condition at each node and yields a closed immersion.

### 4.3 Orbit divisors

Let $P\in E^{\mathrm{sm}}(S)$ satisfy $NP=e$. Its orbit divisor is

$$
D_P=\sum_{a\in\mathbf Z/N\mathbf Z}[aP]. \tag{4.3}
$$

It is stable under translation by $P$. It need not be a subgroup scheme merely because $NP=e$: if the sections collide, the scheme structure of their sum must be compatible with multiplication and inversion. Requiring $D_P$ to be a finite locally free subgroup divisor is the Drinfeld condition introduced in the next chapter.

When $D_P$ is a subgroup divisor, the components it meets form a subgroup of the component group. Translation by $P$ permutes these components transitively. Hence $D_P$ is ample if and only if the image of $P$ generates the component group of every polygonal fiber.

The same statement holds for a finite subgroup divisor $C\subset E^{\mathrm{sm}}$: it is ample exactly when its image in the component group is surjective. This version is intrinsic and does not require a generator.

### 4.4 Component bounds

An ample degree-$d$ divisor meets every component with positive length, so a polygon carrying it has at most $d$ components. Thus a $\Gamma_1(N)$ or $\Gamma_0(N)$ divisor bounds the number of components by $N$, and full level bounds it by $N^2$ even before the sharper torsion calculation is used.

This bound has two consequences. First, the relevant generalized elliptic curves lie in a bounded algebraic piece of the stack of all generalized elliptic curves. Second, a common high power of the level line bundle embeds every object in one projective Hilbert family. The parameter-space results for projective curves then show that level conditions are finite-presentation conditions.

The bound does not say that every number up to $d$ occurs. Group arithmetic is sharper: for cyclic level $N$, the polygon size divides $N$; for full level it is exactly $N$. We prove those statements after giving the correct integral definition.

For a counterexample to omitting ampleness, take $C_{100}$ and the subgroup $\mu_5$ in its identity component. It is finite locally free, cyclic in the Drinfeld sense, and killed by $5$, yet its divisor has degree zero on $99$ components. Allowing it as compactified $\Gamma_0(5)$ level would create boundary types of arbitrarily large size unrelated to the level. Ampleness rules out exactly this pathology.

## 5. Finite subgroup divisors and Drinfeld generators

### 5.1 Why pointwise generation fails

Suppose $N$ is invertible on a field. A cyclic subgroup of order $N$ has $N$ distinct geometric points, and a generator is a point of exact order $N$. This description collapses when the characteristic divides $N$. The group $\mu_p$ over a field of characteristic $p$ has rank $p$ but only the identity as a geometric point. Nevertheless it is the correct multiplicative cyclic subgroup in ordinary and Tate geometry.

The remedy is to compare effective divisors. If $G$ is a finite locally free subgroup of a smooth relative curve, then $G$ is an effective Cartier divisor. A list of sections fills $G$ when its sum, counted with repetitions, equals that Cartier divisor. This equality tests nilpotent base directions and survives all base changes.

### 5.2 Full sets of sections

Let $G\subset E^{\mathrm{sm}}$ be a finite locally free subgroup of rank $d$, and let $(P_h)_{h\in H}$ be sections indexed by a set $H$ of size $d$. They form a **full set of sections** of $G$ if

$$
\sum_{h\in H}[P_h]=G \tag{5.1}
$$

as effective Cartier divisors on $E^{\mathrm{sm}}$.

Equality can be tested after a faithfully flat base change. It is also closed in families: in a local smooth parameter, both sides are cut out by monic degree-$d$ polynomials, and equality is equality of their coefficients. If $d$ is invertible and $G$ is étale, (5.1) holds exactly when the $P_h$ are the distinct geometric points of $G$.

More explicitly, near a section choose a smooth coordinate $T$. A finite flat divisor of rank $d$ has a monic equation

$$
F(T)=T^d+c_1T^{d-1}+\cdots+c_d.
$$

The sum of sections with coordinates $t_h$ has equation $\prod_h(T-t_h)$. Fullness is the finite system

$$
c_i=(-1)^ie_i((t_h)_h),\qquad 1\leq i\leq d. \tag{5.3}
$$

These polynomial equations remain valid when all $t_h$ coincide. They prove directly that fullness is closed and commutes with arbitrary scalar extension.

In characteristic $p$, take $G=\mu_p\subset\mathbf G_m$ with coordinate $z$ at the identity. Its equation is $z^p-1=(z-1)^p$. The constant homomorphism $\mathbf Z/p\mathbf Z\to\mu_p$ sends every index to $1$, and its divisor is $p[1]$, cut out by $(z-1)^p$. Thus it is a full set of sections even though its underlying set has one point. This calculation is the local model for collisions at a cusp.

### 5.3 Drinfeld generators

Let $C\subset E^{\mathrm{sm}}$ be finite locally free, commutative, killed by $N$, and of rank $N$. A section $P\in C(S)$ is a **Drinfeld generator** if

$$
\sum_{a\in\mathbf Z/N\mathbf Z}[aP]=C \tag{5.2}
$$

as Cartier divisors. The group $C$ is **cyclic of order $N$** if it admits a Drinfeld generator fppf-locally on $S$.

The locality clause is essential. A cyclic subgroup can have no global generator because its generators form a torsor under $(\mathbf Z/N\mathbf Z)^\times$. Requiring a global generator would define a $\Gamma_1$ structure, not a $\Gamma_0$ structure.

The condition $NP=e$ is part of the input: the subgroup $C$ is killed by $N$ and $P$ is a section of $C$. It should not be inferred merely from a pointwise count of the terms in (5.2), because those terms can coincide. The divisor equality adds the genuinely integral assertion that the indexed multiples of $P$, with all infinitesimal multiplicities retained, fill $C$.

The unit group acts on generators by $P\mapsto aP$. Fppf-locally any two generators differ in this way. On an étale geometric fiber this is the elementary fact about a cyclic group. On a connected multiplicative fiber it is the same statement for the universal character of $\mu_N$. Since the generator equations are finite and flat, the fiberwise statement descends. Thus passing from a generator to its cyclic subgroup is genuinely the quotient by $(\mathbf Z/N\mathbf Z)^\times$ in the fppf topology.

Drinfeld generation is stable under arbitrary base change and descends fppf-locally. Inversion sends a generator to a generator, and multiplication by $a\in(\mathbf Z/N\mathbf Z)^\times$ does likewise. Hence the generator sheaf is acted on by the unit group, and its fppf quotient is the cyclic-subgroup problem.

### 5.4 Behavior when the order is invertible

**Proposition 5.1.** If $N$ is invertible on $S$, a finite locally free group $C$ killed by $N$ is cyclic of rank $N$ in the Drinfeld sense if and only if étale-locally it is the constant group $\mathbf Z/N\mathbf Z$. A Drinfeld generator is then an ordinary generator on every geometric fiber.

**Proof.** Multiplication by $N$ has invertible differential on a smooth group, so $C$ is finite étale. After an étale cover it is constant. The divisor equality (5.2) says that the $N$ translates $aP$ list all $N$ points without repetition. This is equivalent to $P$ having exact order $N$. Conversely, an exact-order generator lists the group and gives the divisor equality. $\square$

Thus Drinfeld's definition is not a competing generic notion. It is a divisor-theoretic extension of the usual one that remains meaningful when points collide. This compatibility will allow every integral moduli problem below to restrict to the classical level problem over $\mathbf Z[1/N]$.

Two examples delimit the definition. On $\mathbf G_m$ in characteristic $p$, the identity section is a Drinfeld generator of $\mu_p$, because $p[1]=\mu_p$. On the constant group $\mathbf Z/p\mathbf Z$, the section $1$ is an ordinary generator and its translates are disjoint. Cartier duality exchanges these two cyclic groups. A cyclic rank-$p$ group over a DVR can interpolate between connected and étale special behavior, and the divisor definition treats that interpolation without choosing a type in advance.

## 6. Full, $\Gamma_1$, and $\Gamma_0$ level

### 6.1 $\Gamma_1(N)$-structures

A **$\Gamma_1(N)$-structure** on a generalized elliptic curve $E/S$ is a section $P\in E^{\mathrm{sm}}[N](S)$ such that

$$
C_P=\sum_{a\in\mathbf Z/N\mathbf Z}[aP]
$$

is a finite locally free subgroup divisor of rank $N$ and is relatively ample on $E$. Equivalently, $P$ is a Drinfeld generator of the cyclic subgroup $C_P$ and that subgroup meets every component of every geometric fiber.

Every clause is needed. The equation $NP=e$ alone does not prevent an orbit divisor from having the wrong infinitesimal structure. Drinfeld generation supplies the integral order condition. Ampleness prevents a polygon from carrying arbitrary extra components unseen by $P$.

For example, on a smooth elliptic curve in characteristic $p$, the equation $pP=e$ alone permits the zero section. Its divisor $p[e]$ need not be the desired cyclic subgroup slice of $E[p]$. For $\Gamma_1(p)$ it must first be a subgroup divisor of rank $p$; for full level the required divisor has rank $p^2$. The definition distinguishes an integral cyclic direction from the entire torsion kernel.

An isomorphism $(E,P)\to(E',P')$ is an isomorphism of generalized elliptic curves carrying $P$ to $P'$. Pullback preserves the divisor equality and ampleness, so these objects form a stack. Over $\mathbf Z[1/N]$ the section is simply a point of exact order $N$ whose component image generates the polygonal component group.

### 6.2 $\Gamma_0(N)$-structures

A **$\Gamma_0(N)$-structure** on $E/S$ is a finite locally free cyclic subgroup

$$
C\subset E^{\mathrm{sm}}
$$

of rank $N$ whose divisor is relatively ample on $E$. Cyclic means that fppf-locally there is a Drinfeld generator $P$ satisfying $C=\sum_a[aP]$.

The passage from $\Gamma_1$ to $\Gamma_0$ forgets the generator:

$$
(E,P)\longmapsto(E,C_P). \tag{6.1}
$$

The unit group $(\mathbf Z/N\mathbf Z)^\times$ acts by $P\mapsto aP$, and fppf-locally the fibers of (6.1) are its orbits. Stabilizers can occur in bad characteristic on the level of geometric points, but the divisor definition and the quotient sheaf retain the correct scheme structure.

The involution $[-1]$ preserves every subgroup $C$. Hence $\Gamma_0(N)$ does not generally remove the generic elliptic involution. This explains why its natural moduli object remains stacky even at large level, unless an auxiliary rigidifying level is added.

There is no preferred generator hidden in $C$. If generators exist over a cover $S'\to S$, their descent cocycle takes values in $(\mathbf Z/N\mathbf Z)^\times$. A nontrivial cocycle produces a cyclic subgroup over $S$ with no global generator. The distinction is analogous to a line bundle versus a chosen basis: the rank-one object can descend when a trivialization does not.

### 6.3 Full level and the Weil pairing

A **full $\Gamma(N)$-structure** is a homomorphism

$$
\alpha:(\mathbf Z/N\mathbf Z)^2\longrightarrow E^{\mathrm{sm}}(S),
\qquad (a,b)\longmapsto aP+bQ, \tag{6.2}
$$

such that

$$
D_\alpha=\sum_{(a,b)}[aP+bQ]
$$

equals $E^{\mathrm{sm}}[N]$ as a finite locally free Cartier divisor and is ample on $E$. The equality asserts in particular that the displayed kernel is finite locally free of rank $N^2$; this must not be assumed for an arbitrary polygon.

If a primitive $N$th root $\zeta_N$ has been fixed on the base in the Drinfeld sense, the structure is **symplectic** when

$$
e_N(P,Q)=\zeta_N. \tag{6.3}
$$

Here the Weil pairing is the perfect alternating pairing of finite locally free group schemes. When $N$ is not invertible, (6.3) is an equality of sections of $\mu_N$, not a statement about distinct roots in geometric point sets.

The phrase “primitive in the Drinfeld sense” means that the powers of $\zeta_N$ fill $\mu_N$ as a divisor. Over $\mathbf Z[\zeta_N]$ the identity

$$
\prod_{a=0}^{N-1}(T-\zeta_N^a)=T^N-1
$$

is integral. After reduction at a divisor of $N$, several factors can coincide, but the equality of monic polynomials survives. Thus the symplectic equation retains its meaning at precisely the fibers where ordinary primitive roots cease to be a set of $N$ distinct points.

Over $\mathbf Z[1/N]$, $E[N]$ is étale of rank $N^2$, and the divisor equality says precisely that $P,Q$ are a basis. With a symplectic normalization, changing the basis acts through $\operatorname{SL}_2(\mathbf Z/N\mathbf Z)$; without it, the determinant changes the chosen primitive root through the cyclotomic action.

Alternation shows that either basis vector generates an isotropic cyclic subgroup, while the quotient direction is Cartier dual to it. At a cusp this becomes the pairing between $\mu_N$ and $\mathbf Z/N\mathbf Z$. The full-level definition is therefore already adapted to the quotient isogenies constructed later.

### 6.4 Comparison and forgetful maps

Full level yields several cyclic levels. The first vector gives a $\Gamma_1(N)$-structure, and its generated divisor gives a $\Gamma_0(N)$-structure, provided it is ample. On a smooth elliptic curve this ampleness is automatic. On a polygon it is not: a full basis can have one vector entirely in the identity component while the other sees all components. Thus a forgetful map to $\Gamma_1(N)$ may require choosing a primitive vector whose component image is surjective, or contracting the components invisible to the chosen vector. Chapter 8 makes that correction canonical.

Likewise, forgetting all level leaves a generalized elliptic curve, while quotienting by a cyclic subgroup produces a second one after the boundary extension of Chapter 9. These operations are the geometric origin of degeneracy maps. On smooth fibers they are the usual forgetful and quotient constructions; the purpose of contraction and Tate charts is to prove that they remain meaningful at cusps.

## 7. Level on a polygon

### 7.1 The component calculation

Let $k$ be algebraically closed and let $E=C_n$. A cyclic subgroup $C$ of rank $N$ has a component image $H\subset\mathbf Z/n\mathbf Z$. If $C$ is ample, $H$ is all of $\mathbf Z/n\mathbf Z$. Therefore $n$ divides $N$: the rank of a finite group mapping surjectively to a group of order $n$ is divisible by $n$.

For a $\Gamma_1(N)$ point $P=(a,r)$, ampleness says that $r$ generates $\mathbf Z/n\mathbf Z$. Since $NP=e$, one has $Nr=0$, again giving $n\mid N$. Conversely, if $n\mid N$, points with component generator can occur after a suitable fppf extension, and their orbit divisor meets every component.

For the converse, write $N=ne$ and pass fppf-locally to a base carrying a Drinfeld primitive $N$th root $\xi$. Take

$$
P=(\xi,1)\in C_n^{\mathrm{sm}}.
$$

The point has order $N$. Its orbit visits each component $e$ times; on a fixed component the toric coordinates differ by powers of $\xi^n$, whose divisor fills $\mu_e$. Hence the full orbit is a cyclic subgroup divisor of rank $N$ and is ample. Thus every divisor $n$ of $N$ really can occur at the boundary.

For full level, formula (2.1) and the divisor equality give

$$
N\gcd(N,n)=N^2,
$$

so $N\mid n$. Ampleness of the full kernel says that $[N]$ kills every component, so $n\mid N$. Hence:

**Theorem 7.1 (polygon sizes).** On a geometric polygonal fiber:

- $\Gamma_1(N)$ or $\Gamma_0(N)$ level forces $n\mid N$;
- full $\Gamma(N)$ level forces $n=N$.

The proof uses ranks as well as supports. Looking only at the set of torsion points in bad characteristic would not justify the equality.

For composite $N$, cyclic level can therefore have several cusp widths. If $N=6$, the possible polygon sizes are $1,2,3,6$. On a $2$-gon an ample orbit visits the two components three times each; on a $3$-gon it visits the three components twice each. Full level still permits only the $6$-gon because the kernel-rank equation supplies the reverse divisibility. Prime level is special because the divisor lattice has only two elements.

### 7.2 The prime-level alternatives

Let $p$ be prime. The divisors of $p$ are $1$ and $p$, so a polygon with $\Gamma_1(p)$ or $\Gamma_0(p)$ level has exactly one of two forms.

On a one-gon, the smooth locus is $\mathbf G_m$. A cyclic subgroup of rank $p$ is the multiplicative subgroup $\mu_p$ after an fppf base change. A $\Gamma_1(p)$ generator is a Drinfeld primitive $p$th root. In characteristic $p$, all its sections can specialize to the identity, but their sum is the divisor $\mu_p$.

On a $p$-gon, ampleness forces the subgroup to map isomorphically onto the component group. A generator has the form $(a,1)$ after choosing a component orientation, with $a^p=1$. The automorphism $(u,i)\mapsto(a^{-i}u,i)$ sends it to $(1,1)$. Thus the geometric standard form is

$$
P=(1,1),\qquad
C=\langle(1,1)\rangle. \tag{7.1}
$$

We call these the **multiplicative cusp type** and the **component cusp type**. They are not two arbitrary charts; they exhaust prime-level boundary fibers.

In characteristic $p$ their group schemes have opposite behavior. On the one-gon, $C=\mu_p$ is connected. On the $p$-gon, $C\to\Phi_E$ is an isomorphism and is étale after splitting the component group. This connected-versus-component dichotomy later becomes the two branches of prime-level special-fiber geometry.

### 7.3 Full prime level

Full $\Gamma(p)$ level forces a $p$-gon. Its $p$-torsion fits into

$$
0\longrightarrow\mu_p
\longrightarrow E^{\mathrm{sm}}[p]
\longrightarrow\mathbf Z/p\mathbf Z
\longrightarrow0. \tag{7.2}
$$

After an fppf base change, choose a Drinfeld primitive root $\zeta_p$ and a lift of the component generator. Polygon automorphisms normalize a symplectic basis to

$$
P=(\zeta_p,0),\qquad Q=(1,1). \tag{7.3}
$$

The divisor generated by $P,Q$ is the whole $p$-torsion and meets every component. The Weil pairing normalization agrees with

$$
e_p(P,Q)=\zeta_p,
$$

the multiplicative-coordinate formula for Tate curves. Thus full level separates naturally into one toric direction and one component direction at the cusp.

### 7.4 Automorphisms and rigidity

An automorphism preserving ample level is determined on a dense collection of smooth sections and hence on the whole curve. Full level $N\geq3$ kills automorphisms when $N$ is invertible: on a smooth fiber an origin-preserving automorphism acting trivially on a basis of $E[N]$ is trivial, and on an $N$-gon the basis fixes the toric and component directions. Fiberwise triviality and separatedness then give global triviality.

Here is the matrix argument on a smooth fiber. An automorphism of finite order acts on the prime-to-characteristic Tate module. If it fixes $E[N]$ with $N\geq3$, its matrix is congruent to the identity modulo $N$. A finite-order integral matrix in the principal congruence subgroup of level $N\geq3$ is the identity: for a prime dividing its order, expand the first nonzero congruence term of the corresponding prime-power relation and obtain a contradiction modulo the next power of $N$. Faithfulness of the Tate-module action then makes the curve automorphism trivial.

The exclusions are real. Full level $2$ is preserved by $[-1]$. A $\Gamma_1(N)$ point can retain exceptional automorphisms at small $N$. Every $\Gamma_0(N)$ subgroup is preserved by $[-1]$. At primes dividing $N$, triviality must be checked on the full finite-flat divisor, not inferred from the number of geometric sections.

For prime $p\geq5$ with $p$ invertible in the ground field, a $\Gamma_1(p)$ structure has no nontrivial automorphism. On a smooth fiber, let $g$ fix a point of exact order $p$. The finite group of origin-preserving automorphisms has order divisible only by $2$ and $3$, including in the exceptional characteristics $2$ and $3$. Its action on the prime-to-characteristic Tate module is faithful, and $g-1$ has determinant $\deg(g-1)$. For nontrivial $g$, this degree is a product of powers of $2$ and $3$: equivalently, on the quadratic cyclotomic representation it is the norm of $\zeta-1$, and the extra automorphisms in characteristics $2$ and $3$ still have $2$- or $3$-power degree. Thus $g-1$ is invertible on $E[p]$, contradicting the fixed point. On a $p$-gon, write an automorphism in split coordinates. Fixing the generator fixes its component class and then its toric coordinate, so the automorphism is the identity. On a one-gon, the only possible nontrivial origin-preserving polygon automorphism is inversion, and it cannot fix a point of exact odd order $p$. Hence the automorphism is trivial in every case.

No such blanket assertion is valid in characteristic $p$. A Drinfeld generator may have the identity as its only geometric value while its orbit divisor still has length $p$. Inversion can then fix the displayed section, and exceptional automorphisms of a smooth fiber can also survive collapsed level. On the component-type $p$-gon the nonzero component class still gives rigidity, but the multiplicative cusp need not. Integral moduli statements must therefore retain stack language unless stabilizers have been checked scheme-theoretically on the particular stratum.

## 8. Contraction of generalized elliptic curves

### 8.1 The problem solved by contraction

Suppose level data see only some components of a polygon. Simply forgetting part of a full basis can leave a divisor of degree $N$ supported on a proper subset of an $N$-gon. Such an object is not a $\Gamma_1(N)$ generalized elliptic curve because ampleness fails. Deleting the unseen components would destroy properness. Contraction replaces each connected chain of unseen components by a node and retains the visible components.

The input is most naturally an open subgroup $G\subset E^{\mathrm{sm}}$ whose geometric fibers are unions of components and which contains the identity component. Equivalently, $G$ is the inverse image of a subgroup of the finite component group. We seek a proper curve $E_G$ and a map

$$
c_G:E\longrightarrow E_G
$$

that is an isomorphism on $G$, contracts every component not met by $G$, and has $E_G^{\mathrm{sm}}=G$.

### 8.2 Fiberwise contraction

On the standard $n$-gon, let $H\subset\mathbf Z/n\mathbf Z$ have order $d$. The visible components are those indexed by $H$. Between consecutive visible components lies a chain of $n/d-1$ invisible projective lines. Contract each such chain to one ordinary node. The result is a $d$-gon.

One algebraic construction uses a divisor $D$ supported at one smooth point on every visible component and no invisible component. The line bundle $\mathcal L=\mathcal O_E(D)$ has positive degree on visible components and degree zero on each invisible chain. On a rational chain, a multidegree-zero line bundle trivialized at one endpoint is trivial. Therefore a sufficiently high power of $\mathcal L$ is generated, separates points off the zero-degree chains, and is constant on each such chain. The morphism defined by its sections contracts exactly those chains. Its image has one ordinary node per chain because the two endpoint tangent directions remain distinct.

The group $G=\mathbf G_m\times H$ preserves the set of zero-degree chains and acts on the image. Its action is transitive on the $d$ retained components. The smooth locus of the image is precisely $G$, since the contracted chains become nodes and no point of a retained smooth component is altered.

The new singularity is ordinary. If a zero-degree chain has endpoint parameters $x$ and $y$, sections constant on the chain identify the endpoint values, while a section vanishing through the chain records the product $xy$. The completed image ring is $k[[x,y]]/(xy)$ on the special fiber. In a one-parameter smoothing it is $A[[x,y]]/(xy-a)$, where $a$ is the product of the smoothing parameters along the chain. Contraction creates a node, not a cusp.

### 8.3 Relative construction and uniqueness

**Theorem 8.1 (contraction).** Let $E/S$ be a generalized elliptic curve and let $G\subset E^{\mathrm{sm}}$ be an open subgroup which is fiberwise a union of components and meets every fiber. Locally on a locally noetherian base, there is a generalized elliptic curve $E_G/S$ and a proper map

$$
c_G:E\to E_G
$$

with the following properties:

1. $c_G$ is an isomorphism over $G$ and identifies $G$ with $E_G^{\mathrm{sm}}$;
2. on every geometric fiber it contracts exactly the irreducible components disjoint from $G$;
3. it is $G$-equivariant and commutes with arbitrary base change;
4. it is unique up to unique isomorphism.

**Proof strategy.** Build a semiample line bundle with degree positive exactly on the visible components. Cohomology and base change, not merely the formal base-change property of Proj, will make its section algebra relative. Its Proj has a universal property that supplies gluing, equivariance, and uniqueness.

**Proof.** Shrink first to a quasi-compact neighborhood in $S$. Through a smooth point of any visible component, smoothness supplies a section after an étale base change. Noetherian induction over the finitely many component strata, extending each such section to an actual neighborhood and shrinking so that it remains in $G$, produces finitely many sections meeting every visible component in every fiber. Their sum, with collisions allowed, is a relative Cartier divisor $D$ supported in $G$ whose degree is positive precisely on the visible components. This construction takes place on open neighborhoods; the component stratification is used only to prove that finitely many choices suffice. Put $\mathcal L=\mathcal O_E(D)$. On an invisible connected chain, $\mathcal L$ has multidegree zero and is trivial after its value at either attaching point is fixed.

For a sufficiently divisible $m$, the normalization exact sequence on every polygon shows three facts, uniformly on the chosen bounded stratum: $\mathcal L^m$ is generated relative to $S$; $R^1\pi_*\mathcal L^{mr}=0$ for every $r>0$; and multiplication is surjective in sufficiently high degrees. The cohomology-and-base-change theorem then says that $\pi_*\mathcal L^{mr}$ is finite locally free and commutes with arbitrary base change for $r>0$. After replacing the grading by a high Veronese, the algebra

$$
\mathcal A=\bigoplus_{r\geq0}\pi_*\mathcal L^{mr}
$$

is finitely generated. Put $E_G=\operatorname{Proj}_S\mathcal A$. Because the positive graded pieces of $\mathcal A$ have just been proved to commute with base change, this particular Proj construction commutes with arbitrary base change. The fiberwise calculation of Section 8.2 shows that the induced map is an isomorphism on $G$, is constant exactly on each connected invisible chain, and has polygonal image fibers. The normalization calculation also gives $(c_G)_*\mathcal O_E=\mathcal O_{E_G}$.

This yields the needed universal property. If $f:E\to X$ is a morphism to a separated $S$-space that is constant on every invisible chain in every geometric fiber, then $f$ factors uniquely through $c_G$. Existence is affine-local on $X$ and follows from $(c_G)_*\mathcal O_E=\mathcal O_{E_G}$; uniqueness follows because $c_G$ is surjective. Translation by an element of $G$ preserves the set of invisible chains, so the universal property descends the $G$-action to $E_G$. The group identities hold on the dense smooth locus and hence everywhere by Proposition 3.2.

On overlaps, two local constructions contract the same chains and are isomorphisms on $G$. Applying the universal property in both directions gives inverse isomorphisms, and uniqueness gives the cocycle condition. The local targets therefore glue. The same argument proves uniqueness over $S$ and compatibility with every base change. $\square$

The noetherian hypothesis is used only to choose a uniform semiample power. Approximation extends the result to bases on which the curve, subgroup, and component stratification descend to a noetherian model.

Here are the cohomological details used in the proof. On a retained component, $\mathcal L^m$ has positive degree and no first cohomology for $m$ large; on an invisible rational chain it is trivial. The normalization exact sequence describes a global section as component sections with matching endpoint values. Evaluation at the two ends of every positive-degree component is surjective once $m$ is large, so the matching map is surjective and the first cohomology vanishes. The same description shows that sections separate every two points not on the same invisible chain and are constant along such a chain. Multiplication is surjective in high degree on the positive-degree components; surjectivity of endpoint evaluation lets one impose the gluing conditions without losing it. This proves finite generation and all the base-change assertions used above without importing another contraction theorem.

### 8.4 Equivariance and level

Let $D\subset E^{\mathrm{sm}}$ be a finite subgroup divisor, and let $G_D$ be the union of components met by $D$. Then $G_D$ is an open subgroup: the component images of a subgroup form a subgroup. The contraction $E\to E_{G_D}$ makes the image of $D$ ample, because it meets every retained component. It changes neither $D$ nor its Drinfeld scheme structure, since the map is an isomorphism on $G_D$.

As a concrete example, start with full level on a $6$-gon and retain a point whose component class has order $2$. Its orbit divisor sees components $0$ and $3$. Contraction collapses each of the two chains of two intervening components to a node, producing a $2$-gon. The same point now has ample $\Gamma_1(6)$ level: its six orbit terms distribute with length three on each retained component. Forgetting level without this contraction would leave a nonample divisor on the original $6$-gon.

Thus forgetting part of level is a two-step operation:

$$
(E,\text{large level})
\longmapsto(E,D)
\longmapsto(E_{G_D},D). \tag{8.1}
$$

The second arrow is forced precisely when $D$ is not already ample. This construction commutes with base change and isomorphisms, so it defines a morphism of the corresponding moduli stacks. On smooth fibers every component is visible and contraction is the identity.

Contraction is idempotent. Once invisible components are removed, the same divisor is ample and a second contraction changes nothing. If $D\subset D'$ are subgroup divisors, the components seen by $D$ form a subgroup of those seen by $D'$, and the contraction from $E_{G_{D'}}$ to $E_{G_D}$ composes to the direct contraction from $E$. Iterated forgetful maps are therefore independent of the order in which excess level is discarded.

## 9. Quotients and isogenies at the boundary

### 9.1 Quotients of the smooth group

Let $C\subset E^{\mathrm{sm}}$ be finite locally free. The fppf quotient $E^{\mathrm{sm}}/C$ is a smooth separated commutative group over $S$. On a smooth elliptic fiber it is the smooth locus of the usual quotient elliptic curve. On a polygonal fiber, write

$$
a=\operatorname{rank}(C\cap E^{\mathrm{sm},0}),
\qquad b=\#\operatorname{im}(C\to\Phi_E).
$$

Then $ab=\operatorname{rank}C$ after a geometric base change, and the quotient component group has order $n/b$. The identity torus quotient by its multiplicative subgroup of rank $a$ is again a torus, with local coordinate map $z\mapsto z^a$ in the split form.

This predicts the proper quotient: an $n$-gon should map to an $(n/b)$-gon. Components identified by the image of $C$ become one component, while the toric degree records the part of the isogeny inside each component.

If $C=\mu_a$ lies in the identity component, then $b=1$ and the target still has $n$ components; the map has degree $a$ on each normalized component. If $C$ maps isomorphically to a component subgroup of order $b$, then $a=1$ and groups of $b$ components are identified. These extremes explain the two prime quotient formulas.

### 9.2 Extension across the nodes

**Theorem 9.1 (boundary quotient).** Let $E/S$ be a generalized elliptic curve and $C\subset E^{\mathrm{sm}}$ a finite locally free subgroup. There is a generalized elliptic curve $E/C$ and a finite morphism

$$
\varphi_C:E\longrightarrow E/C
$$

whose restriction to the smooth locus is the quotient homomorphism. It has degree $\operatorname{rank}C$, is compatible with arbitrary base change, and is unique.

**Proof.** The subgroup $C$ acts on the whole curve through the generalized elliptic action. Fppf-locally, an ample orbit divisor makes $E$ projective, so the finite-quotient theorem produces the categorical scheme quotient $E/C$ and a finite surjection $E\to E/C$. These local quotients descend uniquely because the quotient is characterized by its invariant morphisms. Its restriction to the smooth locus is the smooth separated group quotient $E^{\mathrm{sm}}/C$. What remains is to identify the boundary fibers and prove the stronger arbitrary-base-change assertion, since a general invariant-ring quotient supplies only flat base change automatically.

Over the smooth-elliptic stratum, this quotient is the usual elliptic-curve quotient. Over a fixed polygon stratum, further fppf localization splits the component group, identifies $C\cap E^{\mathrm{sm},0}$ with $\mu_a$, and labels the cyclic image of $C$ in the component group.

On normalizations, the multiplicative part acts with quotient coordinate $z\mapsto z^a$, while the component part identifies the $b$ components in each orbit. The construction also works in a smoothing, where a completed étale neighborhood of a source node has the form

$$
A[[x,y]]/(xy-r).
$$

The multiplicative subgroup acts with weights $1$ and $-1$. Its quotient is given integrally by

$$
A[[X,Y]]/(XY-r^a)
\longrightarrow A[[x,y]]/(xy-r),
\qquad X\longmapsto x^a,\quad Y\longmapsto y^a. \tag{9.1a}
$$

This statement remains true when $a$ is not invertible: the weight-zero monomials are generated by $x^a$, $y^a$, and $xy=r$. The component part then identifies the labeled node charts in each orbit. Thus the local target is proper with smooth locus $E^{\mathrm{sm}}/C$; its geometric polygonal fiber has $n/b$ components, and none of the source components is contracted. The degree on the dense smooth locus is $ab=\operatorname{rank}C$.

The normalization maps and the node maps agree on their common punctured neighborhoods, so they glue. A change of splitting produces the same homomorphism on the dense smooth locus. Proposition 3.2 therefore gives unique descent isomorphisms and the cocycle condition. The formulas on normalizations and (9.1a) are defined over the base ring and commute with every scalar extension; after descent they prove arbitrary base-change compatibility. Uniqueness again follows from agreement on the dense smooth locus. $\square$

The quotient is finite locally free on the smooth locus, where the subgroup acts freely, but it need not be flat at a node. For example, the toric map has completed local form

$$
k[[X,Y]]/(XY)\longrightarrow k[[x,y]]/(xy),
\qquad X\longmapsto x^a,\quad Y\longmapsto y^a.
$$

The closed fiber over the target node has length $2a-1$, not $a$, when $a>1$. Thus the degree in Theorem 9.1 is the generic degree on the curve, equivalently the degree on the dense smooth locus; no flatness at the boundary is being asserted.

No component contraction is part of this finite quotient: a finite morphism cannot contract an irreducible component. Contraction enters only afterward in a composite operation if some newly retained level divisor fails to see all components of the quotient curve.

### 9.3 The two degree-$p$ quotient formulas

Tate uniformization makes the two prime-level quotient types explicit.

First let $C=\mu_p\subset E_q$. The map $u\mapsto u^p$ has kernel $\mu_p$ and sends $q^{\mathbf Z}$ to $(q^p)^{\mathbf Z}$. Hence

$$
E_q/\mu_p\simeq E_{q^p}. \tag{9.1}
$$

Second write $q=t^p$ and let $C$ be generated by the class of $t$. Quotienting $K^\times/q^{\mathbf Z}$ by that class replaces the period group $t^{p\mathbf Z}$ by $t^{\mathbf Z}$. Therefore

$$
E_{t^p}/\langle t\rangle\simeq E_t. \tag{9.2}
$$

Both formulas respect invariant differentials up to the expected degree. In (9.1), $du/u$ pulls back under $u\mapsto u^p$ to $p\,du/u$; in (9.2), the map is induced by the identity on $\mathbf G_m$ and changes only the period lattice.

They also match the torsion exact sequence. In (9.1) the multiplicative kernel is removed, so the component lift in the target has period $q^p$. In (9.2) the component lift is killed, enlarging the period lattice from $t^{p\mathbf Z}$ to $t^{\mathbf Z}$; the dual kernel on the quotient is multiplicative. No degree disappears in characteristic $p$ even when the multiplicative kernel has only one geometric point.

At the boundary, (9.1) keeps a one-gon and raises the smoothing parameter to its $p$th power. Formula (9.2) sends the $p$-gon model of $E_{t^p}$ to the one-gon model of $E_t$, mapping all $p$ source components finitely onto the target component through their component-subgroup orbits. These are the two local branches of the prime-level quotient map.

### 9.4 Duality and degree bookkeeping

On smooth elliptic fibers, the dual isogeny of $E\to E/C$ has kernel Cartier dual to $C$ under the Weil pairing. If $\varphi:E\to E/C$, then $\ker(\widehat\varphi)$ represents the characters of $C$, and the Weil pairing identifies it with the corresponding quotient direction in $E[p]$. The identities

$$
\widehat\varphi\varphi=[p],
\qquad
\varphi\widehat\varphi=[p]
$$

hold on the smooth elliptic locus, and both isogenies have degree $p$.

The Tate formulas display the two directions without hiding a model change. Generically, the dual of

$$
E_q\longrightarrow E_{q^p},\qquad [u]\longmapsto[u^p],
$$

is induced by the identity on $\mathbf G_m$, from periods $q^{p\mathbf Z}$ to $q^{\mathbf Z}$. Its kernel is generated by the class of $q$ in $E_{q^p}$. Conversely, the dual of the identity-induced map $E_{t^p}\to E_t$ is $[u]\mapsto[u^p]$ and has multiplicative kernel $\mu_p$.

The first dual kernel approaches the node of the one-gon model of $E_{q^p}$; it is not a finite locally free subgroup of that model's smooth locus. To retain it as level, one replaces the target by the appropriate $p$-gon model. Thus duality exchanges the multiplicative and component directions only together with the contraction or resolution dictated by the level divisor. Whenever both maps extend between chosen proper models, density rigidity extends the two displayed composite identities from the smooth locus. The generic degrees still multiply to $p^2$, while the special polygon maps distribute that degree between toric and component directions.

## 10. Tate curves as cusp coordinates

### 10.1 The one-gon chart

Let $A$ be a ring complete for an ideal and let $q\in A$ be topologically nilpotent. The integral $q$-series $a_4(q)$ and $a_6(q)$ converge $q$-adically and define

$$
\operatorname{Tate}(q):
y^2+xy=x^3+a_4(q)x+a_6(q). \tag{10.1}
$$

Its discriminant is $q$ times a unit. Over $A[1/q]$ it is an elliptic curve. Over $q=0$ it is the standard split one-gon. The smooth locus carries the group law induced by multiplicative uniformization, and that action extends to the nodal cubic. Thus (10.1), not merely its generic fiber, is a generalized elliptic curve over the formal base.

The special-fiber action is also visible without series. Its normalization is $\mathbf P^1$, its smooth locus is $\mathbf G_m$, and multiplication fixes the omitted pair $0,\infty$ setwise. It therefore descends after those two points are identified. Over each infinitesimal quotient $A/(q^r)$, density gives at most one extension of the generic group law; compatibility in $r$ yields the formal action.

The invariant differential is

$$
\omega=\frac{dx}{2y+x},
$$

and uniformization pulls it back to $du/u$. The chosen coordinate $q$ therefore includes a trivialization of the Hodge line. Replacing that trivialization by a unit changes the formal cusp coordinate by a unit, while the divisor $q=0$ remains the boundary.

### 10.2 The $n$-gon model

Put $q=t^n$. The minimal cubic $\operatorname{Tate}(t^n)$ still has a one-gon special fiber, but its node has thickness $n$. Successive blowups resolve the local equation $UV=t^n$ into a cycle of $n$ rational components. Removing exceptional components not needed for relative minimality and retaining the translation action gives a generalized elliptic curve

$$
\operatorname{Tate}_n(t)\longrightarrow\operatorname{Spec}\mathbf Z[[t]] \tag{10.2}
$$

with generic fiber $E_{t^n}$ and special fiber the standard $n$-gon.

The construction is canonical up to the residual polygon automorphisms once the identity component and the orientation corresponding to positive valuation are fixed; the standard component framing of Section 10.4 removes that finite ambiguity. It commutes with base change. On the completed local ring at a node, adjacent components have equation

$$
xy=t,
$$

whereas contracting the entire cycle back to the cubic multiplies the $n$ local passages and recovers thickness $t^n=q$.

The component count follows inductively from the local equation. Blow up $UV=t^n$ at $U=V=t=0$. One chart has the same form with exponent $n-1$, and the other chart contributes one exceptional projective line. Repeating reaches exponent one. Globally, the two ends of the resulting chain attach to the two normalization branches of the one-gon and close into a cycle. Every component has multiplicity one, so the result is a generalized elliptic polygon rather than a multiple fiber.

### 10.3 Sections and specialization

On the generic fiber of $\operatorname{Tate}_n(t)$, a multiplicative parameter $u$ defines a point modulo $t^{n\mathbf Z}$. If

$$
u=\varepsilon t^a,\qquad \varepsilon\in A^\times,\quad 0\leq a<n,
$$

then its section meets component $a$ of the special $n$-gon, and its coordinate within that component reduces to $\overline\varepsilon\in\mathbf G_m$. This follows from the valuation description of components on a Tate curve and remains true universally because the regular model is built by the same successive blowups.

In particular, the class of $t$ meets the next component and has order $n$ since $t^n=q$. A root of unity $\zeta$ has valuation zero and remains on the identity component. Thus

$$
[\zeta]\rightsquigarrow(\overline\zeta,0),
\qquad [t]\rightsquigarrow(1,1). \tag{10.3}
$$

These two specializations are exactly the toric and component basis vectors of full level on a polygon.

More generally, $u=\varepsilon t^a$ and $u'=\varepsilon' t^{a'}$ specialize to the same smooth point precisely when $a=a'$ and $\overline\varepsilon=\overline\varepsilon'$. If $a\ne a'$, they meet different components; if the unit residues differ, they meet different points on one component. When $u/u'\in1+tA[[t]]$, they have the same special point but different infinitesimal jets. Thus the Tate coordinate separates component, residue, and formal information in three successive layers.

### 10.4 The deformation parameter

The formal parameter $t$ has a moduli meaning. A **standard component framing** of the split $n$-gon is an identification of the special fiber with the standard polygon, respecting the identity and action; equivalently, it gives the component labels, cyclic orientation, and the standard smooth points $(1,i)$. The standard points are essential: without them the automorphisms $(u,i)\mapsto(c^iu,i)$ would remain. Consider a deformation with this special-fiber framing. The normalization is a cycle of copies of $\mathbf P^1$, each marked at $0$, $\infty$, and $1$. A projective line with those three marks is rigid. Before the group action is imposed, the only deformation choices are therefore the node equations $x_i y_{i+1}=t_i$ and changes of the branch coordinates by units.

Translation carries the $i$th node to the next and identifies the equations, so all $t_i$ become one parameter after the unique coordinate changes preserving the three standard marks. Calling the remaining parameter $t$, gluing the normalized components with equations $x_i y_{i+1}=t$ gives $\operatorname{Tate}_n(t)$. Contracting the cycle to the one-gon multiplies the $n$ passages and gives $q=t^n$.

This calculation also proves universality over Artinian thickenings. Given a square-zero extension, lift the single element $t$ and use the displayed node equations; the three-pointed normalized components have no deformation, so a lift exists. Two lifts with the same $t$ differ only by branch-coordinate units, which the standard-point framing removes. Induction over the nilpotent filtration gives a unique isomorphism with the pullback of (10.2). Equivalently, formal functions on the proper semistable curve are functions on its normalization whose endpoint values agree, so the local isomorphisms glue uniquely.

At the tangent-space level an unstructured $n$-gon has one local smoothing direction at each node, and translation identifies them cyclically. Only the class of $t$ survives. The explicit lifting just given shows that there are no obstructions, rather than merely predicting their vanishing from the tangent-space count.

Thus the standard-component-framed deformation functor is represented by $\operatorname{Spf}\mathbf Z[[t]]$. If the standard point, orientation, or labeling is forgotten, finite automorphisms act on $t$ and the resulting local object is a quotient chart. Level structures often supply exactly the missing labels and thereby turn the formal chart into a fine one.

## 11. Tate charts with level

### 11.1 Full level

Let $N\geq2$, put $q=t^N$, and work over a base carrying a Drinfeld primitive root $\zeta_N$. On $\operatorname{Tate}_N(t)$ define

$$
P=[\zeta_N],\qquad Q=[t]. \tag{11.1}
$$

Both are killed by $N$. The Tate torsion exact sequence identifies $P$ with the multiplicative subgroup and $Q$ with a lift of the component generator. Its divisor formula gives

$$
\sum_{a,b}[aP+bQ]=E^{\mathrm{sm}}[N].
$$

On the special fiber, $bQ$ meets component $b$, while varying $a$ fills the rank-$N$ multiplicative divisor on that component. Hence the full divisor is ample. The multiplicative-coordinate Weil pairing gives

$$
e_N(P,Q)=\zeta_N.
$$

Thus

$$
(\operatorname{Tate}_N(t),[\zeta_N],[t]) \tag{11.2}
$$

is the standard symplectic full-level cusp object over $\mathbf Z[\zeta_N][[t]]$.

Every framed full-level deformation of a standard $N$-gon is obtained from this object. The underlying framed curve determines $t$ by Section 10.4. Full level identifies the multiplicative kernel with $\mu_N$ and chooses its primitive generator, while its second vector fixes the component orientation. Before a full cusp label is fixed, replacing the second vector by $Q+aP$ gives one of finitely many different labels. For one fixed label, normalization to $P=[\zeta_N]$ and $Q=[t]$ leaves no choice, so the corresponding chart is universal. The other labels give neighboring charts or, after labels are forgotten, the relevant finite quotient action.

The distinction between versal and universal is caused only by residual automorphisms. A framed basis kills them for $N\geq3$ in the invertible-level range. If one remembers merely the subgroup generated by $Q$, then replacing $Q$ by $aQ$ changes the component orientation and gives the same cyclic subgroup. The same power-series ring can therefore appear with different finite quotient groups in full, point, and cyclic moduli.

The divisor equality in (11.2) can be checked on components. On component $b$, the points $aP+bQ$ have toric coordinates $\zeta_N^a$. Their sum is cut out by $Z^N-1$, hence equals $\mu_N$ translated to that component. Summing over $b$ gives rank $N$ on each of $N$ components, total rank $N^2$. Containment in $E^{\mathrm{sm}}[N]$ is clear, and equal finite locally free ranks give equality. The polynomial argument retains every multiplicity at primes dividing $N$.

### 11.2 $\Gamma_1(N)$ cusp charts

For a $\Gamma_1(N)$ boundary point, let $d$ be the order of the image of $P$ in the component group. The component calculation gives $d\mid N$. Write $N=de$. On a $d$-gon, the standard Tate presentation has $q=t^d$. A point with component generator is represented generically by

$$
P=[\zeta_N^a t], \tag{11.3}
$$

after a finite flat base change that supplies the necessary root of unity. The condition $P^N\in q^{\mathbf Z}$ is automatic because

$$
(\zeta_N^a t)^N=t^N=(t^d)^e=q^e.
$$

Its orbit meets every component, and the repetitions within each component give the correct Drinfeld multiplicity $e$.

Conversely, let $P$ be a $\Gamma_1(N)$ point on a $d$-gon. Choose the Tate coordinate so that the component of $P$ is $1$. Then $P=[ut]$ for a unit $u$. The equation $[N]P=e_E$ says $u^Nt^N=q^e$, hence $u^N=1$. Fppf-locally $u=\zeta_N^a$. This proves that (11.3) gives all cusp charts; the Drinfeld generator condition then imposes the coprimality condition below.

Primitivity of the total Drinfeld divisor is exactly the condition

$$
\gcd(a,e)=1. \tag{11.3a}
$$

Indeed, the orbit terms lying on component $b$ have indices $b+kd$, and the ratio between consecutive such terms is $P^d=[\zeta_N^{ad}]$. This element has exact Drinfeld order $e$ precisely when $\zeta_N^{ad}$ is a primitive $e$th root, equivalently when $\gcd(a,e)=1$. Its $e$ translates then cut out the full rank-$e$ multiplicative divisor on that component. Repeating over the $d$ components gives the required rank-$N$ orbit divisor and also shows that $P$ has exact order $de=N$. The proof is the polynomial identity for the divisor of $Z^e-1$, so it remains valid when roots collide in residue characteristic dividing $e$. For $d=N$ the condition is vacuous, while for $d=1$ it is the usual primitive-root condition.

The parameter $t$ is determined only up to coordinate changes preserving $P$. Replacing $t$ by $\xi t$ changes $P=[\zeta_N^at]$ by the multiplicative torsion factor $\xi$. It preserves the point exactly when that factor is allowed by the generator data. Thus the finite stabilizer of a cusp can be read from the class of $(a,1)$ in the Tate torsion extension. Cusp width is the residual ramification after this stabilizer is accounted for.

For prime $p$, there are only two cases:

$$
\begin{array}{c|c|c|c}
\text{type}&\text{curve}&\text{point}&\text{Tate period}\\ \hline
\text{multiplicative}&\operatorname{Tate}_1(q)&[\zeta_p]&q,\\
\text{component}&\operatorname{Tate}_p(t)&[t]&t^p.
\end{array} \tag{11.4}
$$

The first chart naturally carries the cyclotomic generator data; the second naturally carries the component orientation. Their different widths are the geometric reason a single parameter on the unlevelled cusp pulls back with different ramification indices.

For $p$ invertible, the table can be read on distinct points. In the first row the $p$ points are roots of unity on one component. In the second row one point lies on each of the $p$ components. In characteristic $p$, the first row collapses to a length-$p$ divisor at the identity, while the second row retains its component separation. The chart remains flat because length, not point count, is constant.

### 11.3 $\Gamma_0(p)$ cusp charts

For $\Gamma_0(p)$, forget the chosen generator in (11.4). The two standard objects are

$$
(\operatorname{Tate}_1(q),\mu_p)
\quad\text{and}\quad
(\operatorname{Tate}_p(t),\langle t\rangle). \tag{11.5}
$$

The first is defined over $\mathbf Z[[q]]$: the subgroup $\mu_p$ exists without choosing a primitive root. The second is already defined over $\mathbf Z[[t]]$ by the orbit divisor of the section $[t]$; its generators are $[t^u]$ for $u\in(\mathbf Z/p\mathbf Z)^\times$. For fixed $t$, the graph subgroup generated by $[\zeta_p^a t]$ is generally different. It is obtained from the standard family after the cusp-coordinate change $t\mapsto\zeta_p^a t$ over a base carrying $\zeta_p$, not by declaring the two subgroup divisors equal. In the special fiber the first subgroup lies on the sole component, while the second maps isomorphically to the $p$ components.

**Theorem 11.1 (prime cusp completeness).** Every geometric $\Gamma_0(p)$ boundary point, and every formal deformation after choosing the standard component framing and normalizing its component subgroup, is fppf-locally obtained from exactly one of the two types in (11.5). Within that normalization, the parameter $q$ or $t$ is unique.

**Proof.** Theorem 7.1 restricts the polygon size to $1$ or $p$, so the two types cannot overlap. On the one-gon, a cyclic rank-$p$ subgroup of the smooth torus is fppf-locally $\mu_p$ and descends uniquely as that kernel. On the $p$-gon, ampleness makes the component map an isomorphism. Choose a temporary generator. In split coordinates its specialization has the form $(c,1)$, and the polygon automorphism $(u,i)\mapsto(c^{-i}u,i)$ normalizes it to $(1,1)$, the specialization of $[t]$. The corresponding change in a deformation is the cusp-coordinate normalization described above. Section 10.4 then supplies the unique parameter $q$ or $t$. Changing the temporary generator changes the component framing but not the cyclic object, so fppf descent removes that choice. $\square$

No third chart can be hidden by a nonsplit form. After a finite étale extension, the tangent branches and component group split and the theorem applies. Descent can twist the automorphisms of one of the two standard charts, but it cannot change the rank of the subgroup's image in the component group. Thus forms alter descent data, not the two-type classification.

Neither standard subgroup requires a chosen primitive generator. In the first chart, it is the kernel of $[p]$ on the smooth identity torus. In the second, it is the finite subgroup divisor generated by the globally defined section $[t]$; replacing $[t]$ by $[t^u]$ for $u\in(\mathbf Z/p\mathbf Z)^\times$ leaves that divisor unchanged. These intrinsic descriptions prove that both charts live over the stated integral bases.

### 11.4 Change of cusp coordinate

The Tate parameter is canonical only after a cusp framing. Replacing $t$ by $\epsilon t$ with $\epsilon^n=1$ leaves $q=t^n$ fixed but rotates the chosen lift of a component generator by a multiplicative torsion point. Reversing the polygon sends the multiplicative coordinate to its inverse and reverses the component labels. A full symplectic basis restricts these changes; a cyclic subgroup permits more of them.

Consequently, formal charts on an unrigidified moduli stack are quotients of power-series discs by finite stabilizers. This is not yet a construction of the compactified stack; it is the local moduli statement needed for that construction. On a fine full-level or sufficiently rigid $\Gamma_1$ chart, the stabilizer is trivial and the parameter disc itself is the completed local moduli space.

The width can be recovered intrinsically. Let $I$ be the ideal of the boundary in a framed chart and let $J$ be the pullback of the unlevelled boundary ideal. On an $n$-gon chart, $J=I^n$ up to a unit because $q=t^n$. Hence the ramification index along the boundary is the polygon size. This statement does not depend on the chosen generator of $I$.

The unlevelled cusp parameter is always $q$. On a component-type $p$-gon chart it pulls back as

$$
q=t^p. \tag{11.6}
$$

This equality is both analytic and geometric: analytically it is the Tate period, and geometrically it is the product of the $p$ identical node-smoothing passages around the polygon.

If $t'=ut+O(t^2)$ with $u$ a unit, then $(t')^p=u^pt^p+O(t^{p+1})$. The order of the pulled-back boundary ideal is still $p$. Thus cusp width does not depend on the chosen formal coordinate; it is the valuation of the pulled-back unlevelled discriminant, since $\Delta=q$ times a unit.

## 12. Prime-level moduli interpretations

### 12.1 The three fibered moduli problems

For a prime $p$, define groupoids over schemes as follows:

$$
\begin{aligned}
\overline{\mathcal M}(p)(S)&=
\{(E/S,P,Q):\text{symplectic full }\Gamma(p)\text{ level}\},\\
\overline{\mathcal M}_1(p)(S)&=
\{(E/S,P):\Gamma_1(p)\text{ level}\},\\
\overline{\mathcal M}_0(p)(S)&=
\{(E/S,C):\Gamma_0(p)\text{ level}\}.
\end{aligned} \tag{12.1}
$$

The first problem is taken over a base on which the chosen primitive Weil-pairing value is defined. Arrows are isomorphisms preserving every displayed datum. The open subcategories where $E$ is smooth are the classical elliptic-curve level problems.

These are fppf stacks. Generalized elliptic curves descend by Theorem 3.1. Sections and finite locally free subgroup schemes descend. The divisor equalities defining Drinfeld generation are fpqc local, as is cyclicity after a cover. Relative ampleness descends faithfully flatly. Hence descent data for level objects are effective.

Their diagonals are finite. The bounded underlying isomorphism functor is separated, quasi-finite, and of finite presentation by Section 3.3, and preservation of the level sections or subgroup divisor is a closed condition. It remains to prove properness. Over a valuation ring, take the closure of the graph of a generic isomorphism preserving level. Normalize the closures of the components and contract every rational special-fiber component carrying only its two nodal branches and no part of the level divisor. The result is the common stable marked model on both sides: a component is contracted exactly when the level divisor has degree zero on it. Ampleness gives positive degree on every component, so neither original model loses a component and both already equal the common model. The generic isomorphism therefore extends, uniquely by density of the smooth locus. The level-preserving isomorphism functor satisfies the valuative criterion for properness; being proper and quasi-finite of finite presentation, it is finite. For $\Gamma_1(p)$ and full level at rigid values of $p$, it is often trivial; for $\Gamma_0(p)$ it retains at least the familiar involution when that involution is nontrivial.

The notation anticipates compactification, but no properness claim is hidden in it. A global valuative proof must still show that every generic object extends, after permitted base change, to one of these generalized objects and that two extensions are uniquely isomorphic. Tate charts provide the local candidates, contraction corrects a nonample specialization, and properness of the curve extends the underlying sections. Those are inputs to the later global theorem, not a substitute for it.

The boundary descriptions are intrinsic. They do not depend on choosing a Tate coordinate: the multiplicative and component types are distinguished by the rank of the image of the level subgroup in the component group. Tate coordinates merely exhibit their universal deformations.

### 12.2 Representability of level over a fixed curve

Fix a generalized elliptic curve $E/S$ whose polygonal fibers have bounded component number. The functor of $p$-torsion sections is represented by

$$
E^{\mathrm{sm}}[p]=[p]^{-1}(e).
$$

It is separated, locally of finite presentation, and quasi-finite over $S$. On the smooth stratum it is the finite locally free elliptic $p$-torsion. On a fixed $n$-gon stratum, (3.1) identifies its toric kernel with $\mu_p$ and its component kernel with a finite étale group, so it is finite there as well. It need not be finite across a specialization where the polygon size changes: torsion points can approach a node and leave the smooth open.

Inside this section scheme, the $\Gamma_1(p)$ condition is the intersection of:

- the closed condition that the orbit divisor equals a finite subgroup divisor of rank $p$;
- on a fixed polygon stratum, the open-and-closed condition that its component image is surjective;
- the open condition of relative ampleness, equivalent here to meeting all components.

The monic equations of Section 5.2 show that the divisor condition is closed. Hence the $\Gamma_1(p)$ functor over the fixed curve is represented by a separated quasi-finite scheme of finite presentation, and its restriction to any fixed smooth or polygon stratum is finite. It is not generally proper over all of $S$. For example, a component-direction point on a Tate curve can specialize to the node of the one-gon model; after adjoining a $p$th root of the Tate parameter, the correct extension lives on the resolved $p$-gon. This is precisely why forgetting level and extending level use contraction in opposite directions rather than leaving the underlying generalized curve fixed.

For $\Gamma_0(p)$, finite length-$p$ subgroup divisors lie in the relative Hilbert scheme of the proper curve $E$. Requiring the divisor to lie in $E^{\mathrm{sm}}$ is open. The requirements of containing the identity, being stable under inversion and addition, and being killed by $p$ are closed equations on that open parameter space. To impose cyclicity, form the scheme of pairs $(C,P)$ satisfying the Drinfeld generator equation and take its fppf quotient by $(\mathbf Z/p\mathbf Z)^\times$. Descent of generators identifies this quotient with cyclic subgroup divisors, so it represents the desired subfunctor without a pointwise classification. Ampleness is open-and-closed on a fixed component stratum because it is surjectivity of the component image. The resulting functor is separated, quasi-finite, and of finite presentation over the fixed-curve base, and finite after restriction to a fixed smooth or polygon stratum.

To justify the subgroup equations, let $\mathcal C$ be the universal length-$p$ divisor. Containment of the identity is vanishing of its ideal along $e$. Inversion stability is equality of $[-1]^{-1}\mathcal C$ and $\mathcal C$. Addition stability says that the composite

$$
\mathcal C\times_S\mathcal C\longrightarrow E^{\mathrm{sm}}
$$

factors through $\mathcal C$; because the source is finite over the parameter space, this is a closed vanishing condition. The equation $[p]|_{\mathcal C}=e$ is closed as well. These scheme equations detect infinitesimal subgroups that pointwise tests would miss.

On the generator cover, a candidate $P$ is quasi-finite over the subgroup parameter space, and equation (5.3) cuts out the locus where its translates fill $\mathcal C$. The unit group acts on this locus. Local generators of one subgroup differ by that action, so the fppf quotient is exactly the cyclic-subgroup functor. This proves representability of cyclicity without classifying geometric point sets.

For full level, use the product of two section schemes and impose the divisor equality with $E^{\mathrm{sm}}[p]$ and the Weil-pairing equation. These are closed conditions; ampleness is open and, by the rank calculation, forces $p$ components on singular fibers. Thus full level has the same separated, quasi-finite finite-presentation representability over a fixed curve and is finite on each fixed stratum.

These assertions deliberately distinguish stratumwise finiteness from global properness. Passing to the closure of a level point in the Hilbert space can put its limit at a node; resolving to the polygon seen by its component image changes the generalized curve. The compactified level problem permits that changed curve, but the functor of levels on one fixed $E$ does not. A global valuative and deformation analysis is therefore still required for properness or regularity.

They do prove algebraicity once combined with the bounded framed-curve charts: add a basis of a high pushforward of the ample level line, place the embedded curve in its Hilbert scheme, and impose the action and level equations. Changing the basis is a general-linear torsor. The quotient gives an algebraic stack of finite presentation with finite diagonal. This is the exact global conclusion available before properness is addressed.

### 12.3 Boundary strata and their closures

The singular locus in $\overline{\mathcal M}_1(p)$ and $\overline{\mathcal M}_0(p)$ has two geometric types, each of which can have several components distinguished by cusp labels:

$$
\mathcal C_\mu: n=1,\ C=\mu_p,
\qquad
\mathcal C_{\mathrm{comp}}: n=p,\ C\to\Phi_E\text{ is an isomorphism}. \tag{12.2}
$$

On $\Gamma_1(p)$ the first includes a chosen Drinfeld primitive generator and the second a chosen component generator. On full level there is only the $p$-gon stratum, with both directions chosen.

The Tate charts prove that each framed boundary stratum is an effective Cartier boundary locally: it is cut out by $q$ on the one-gon chart and by $t$ on the $p$-gon chart. The map to the unlevelled one-gon cusp has order one on the first chart and order $p$ on the second because $q=t^p$.

The Cartier statement includes flat infinitesimal directions. In $A[[t]]$, multiplication by $t$ is a non-zero-divisor even when $A$ has nilpotents. Thus the boundary has no embedded infinitesimal component in the framed chart. Quotienting by a finite stabilizer may change the coarse local equation, which is why the assertion is made first on the stack chart.

Specialization may move from a smooth curve to either boundary type, but it cannot move between the two types while remaining inside the boundary over a connected reduced base without passing through a change in the component group. The ranks of the subgroup's component image distinguish them. Over nonreduced bases the formal charts, rather than only geometric points, retain the distinction.

When the residue characteristic differs from $p$, both subgroup schemes are étale, so connectedness does not distinguish them. Their component images still do: the one-gon type has trivial component image, while the $p$-gon type maps onto $\mathbf Z/p\mathbf Z$. In characteristic $p$, the same invariant becomes the connected-versus-component distinction. Component image is therefore the uniform definition.

### 12.4 Fine and stacky behavior

Over $\mathbf Z[1/p]$, full level for $p\geq3$ removes automorphisms, and $\Gamma_1(p)$ does so for $p\geq5$. On this invertible-level locus the bounded projective construction gives fine moduli schemes with universal generalized elliptic curves. At a component-type $p$-gon, the nonzero component generator kills inversion, and a full basis fixes both the toric and component directions.

Trivial stabilizers make the stack a sheaf, but do not alone make that sheaf a scheme. Symmetrize the ample level divisor and take a high power of its line bundle. Its theta group is a central extension of a finite group scheme by scalar homotheties $\mathbf G_m$; in particular, its quotient by the center is finite. A theta frame gives a projective frame of the high pushforward, so theta-framed level curves form a locally closed quasi-projective Hilbert parameter scheme. Theta frames differ by the finite automorphism group of the standard extension. The finite-quotient theorem for quasi-projective schemes, proved in the prior stack theory, constructs the quotient as a scheme. Since the level has already killed inertia, this quotient represents the level sheaf rather than merely its coarse orbit functor, and the descended family is universal. Thus each fine assertion uses rigidity, the projective parameter construction, and a genuine finite scheme quotient.

In characteristic $p$, Drinfeld sections can collide. A displayed $\Gamma_1(p)$ generator may then equal the identity as a geometric section even though its orbit divisor has length $p$, and a full pair can likewise collapse on a smooth height-two fiber. Such data need not kill origin-preserving automorphisms. The integral moduli problems in (12.1) must therefore be treated as stacks unless a separate stabilizer calculation proves rigidity on the stratum under discussion. The component-type cusp is rigid for $p\geq3$, but the multiplicative cusp can retain inversion when its generator specializes to the identity.

$\Gamma_0(p)$ retains $[-1]$. Its natural object is therefore a stack even when $p$ is large. One may impose an auxiliary full level $M\geq3$, with $M$ invertible, obtain a fine cover, and recover the original problem as a finite quotient by the change-of-level group. The universal generalized elliptic curve exists on the stack; it need not descend to a future coarse curve because stabilizers act nontrivially on it.

Small primes require separate statements even away from the residue characteristic. At full level $2$, inversion fixes the basis. For $\Gamma_1(2)$ and $\Gamma_1(3)$ special elliptic curves can retain automorphisms. No fine-moduli assertion in this book silently includes those cases or the bad-characteristic collision strata.

## 13. Degeneracy maps at prime level

### 13.1 Forgetting and quotienting

On a smooth elliptic curve with a cyclic subgroup $C$ of order $p$, there are two natural maps to the moduli of elliptic curves:

$$
\pi_1(E,C)=E,
\qquad
\pi_2(E,C)=E/C. \tag{13.1}
$$

For the unlevelled target used here, a polygon is put in its canonical one-gon model: apply Theorem 8.1 with $G=E^{\mathrm{sm},0}$. Thus at the generalized boundary, $\pi_1$ forgets $C$ and contracts every polygon to its identity component. The second map first uses the boundary quotient of Theorem 9.1 and then applies the same one-gon contraction to the quotient. More generally, if a target retains some level, its level divisor determines the open subgroup of components to retain; this recovers the same rule without ambiguity.

Both operations are functorial in the base. They preserve isomorphisms and commute with fppf descent. Consequently they define morphisms of the prime-level moduli stacks before any coarse spaces are constructed.

On the smooth locus, the two maps are interchanged by sending a cyclic isogeny to its dual. At the boundary, the multiplicative and component directions are Cartier dual, but the dual subgroup can meet a node of the currently chosen model. Replacing that model by the polygon on which the dual level is ample swaps the two cusp types. This duality, including the required model change, is encoded in (9.1) and (9.2), not imposed afterward.

For $\Gamma_1(p)$, forgetting the generator but retaining its subgroup gives the map to $\Gamma_0(p)$. Multiplying the generator by $a\in(\mathbf Z/p\mathbf Z)^\times$ gives the diamond action. Quotienting by that action recovers the cyclic-subgroup problem in the fppf sense.

From full level $(P,Q)$ one obtains further maps by retaining a primitive linear combination and contracting to the components it sees. Retaining only its generated subgroup gives a cyclic-level map. Different primitive combinations label different cusps, but once the resulting divisor is fixed the map is canonical because contraction depends only on its component image.

### 13.2 The two cusp formulas

Evaluate (13.1) on the two standard $\Gamma_0(p)$ cusp charts.

For the multiplicative type $(E_q,\mu_p)$,

$$
\pi_1(E_q,\mu_p)=E_q,
\qquad
\pi_2(E_q,\mu_p)=E_{q^p}. \tag{13.2}
$$

Thus on unlevelled Tate parameters,

$$
\pi_1^*(q)=q,
\qquad
\pi_2^*(q)=q^p. \tag{13.3}
$$

For the component type $(E_{t^p},\langle t\rangle)$,

$$
\pi_1(E_{t^p},\langle t\rangle)=E_{t^p},
\qquad
\pi_2(E_{t^p},\langle t\rangle)=E_t. \tag{13.4}
$$

Hence

$$
\pi_1^*(q)=t^p,
\qquad
\pi_2^*(q)=t. \tag{13.5}
$$

In (13.4), the source $E_{t^p}$ carries the $p$-gon model $\operatorname{Tate}_p(t)$. The target of $\pi_1$ is its contracted one-gon with the same generic Tate period $t^p$, while the target of $\pi_2$ is the one-gon of period $t$. Thus the four equalities are identities of formal generalized elliptic curves with the indicated models, not merely formulas for $j$-invariants. They include the subgroup, the necessary model change, and the invariant-differential behavior.

The discriminant product provides a numerical check:

$$
v(\Delta(E_{q^p}))=p\,v(q),
\qquad
v(\Delta(E_t))=v(t).
$$

The multiplicative quotient multiplies collision thickness by $p$ because its degree lies in the torus. The component quotient divides the original thickness $v(t^p)=p\,v(t)$ by $p$ because its degree lies in the polygon. Both isogenies have degree $p$, but they act on different geometric directions.

After passing to the compatible level-bearing models of Section 9.4, composing either quotient with its dual gives multiplication by $p$. On multiplicative coordinates one map raises $u$ to $u^p$ and the dual enlarges the period lattice by a $p$th root; in the component case the order is reversed. Pullback for the composite multiplies invariant differentials by $p$, confirming the degree and duality on the completed charts.

### 13.3 Compatibility with contraction and base change

There are two possible concerns. A quotient might be formed before or after extending the base, and a contraction might be inserted in different orders. Both are resolved by uniqueness on the dense smooth locus.

**Proposition 13.1.** Finite subgroup quotients and component contractions commute with arbitrary base change. If two composites have the same quotient homomorphism on the smooth locus and contract the same geometric components, they are uniquely isomorphic.

**Proof.** Theorem 9.1 proves base change for quotients from the normalization and node formulas, and Theorem 8.1 proves it for contractions using cohomology and base change for the section algebra. On standard polygons the targets and contracted components are computed by quotient component groups, so the two composites agree fiberwise. The quotient universal property on the smooth group and the contraction universal property then produce an isomorphism of the proper targets. It is unique because it is fixed on the dense smooth locus. $\square$

This proposition is what makes the Tate calculations global moduli formulas. They may be verified after completing at a cusp and then descend to every family carrying the corresponding level type.

### 13.4 What the formulas predict

The formulas predict the two branches that later appear in the special fiber of a prime-level integral model. One branch has multiplicative subgroup $\mu_p$ and the quotient map raises $q$ to $q^p$. The other has component subgroup and the forgetful map already has $q=t^p$. Their roles are exchanged by the dual isogeny.

This prediction is not yet a theorem about regularity, irreducible components, or their intersection multiplicities. Establishing those facts requires constructing the compactified stack and its coarse model, analyzing completed local rings at characteristic $p$, and normalizing the relevant strata. What has been proved here is the exact modular meaning and cusp-coordinate behavior that such an analysis must recover.

## 14. The completed boundary package

### 14.1 A dependency-closed theorem summary

The theory developed in this book can be used through the following chain of proved statements.

1. The standard $n$-gon is a proper flat genus-one curve with smooth group $\mathbf G_m\times\mathbf Z/n\mathbf Z$ acting transitively on components.
2. Generalized elliptic curves are precisely the smooth elliptic and polygonal fibers equipped with the compatible smooth group and translation action; they satisfy fpqc descent.
3. A finite divisor in the smooth locus is ample exactly when it meets every component.
4. Drinfeld generation is equality of effective Cartier divisors. It specializes to ordinary generation when the order is invertible and remains valid when sections collide.
5. $\Gamma_1(N)$ is an ample Drinfeld generator, $\Gamma_0(N)$ an ample cyclic subgroup, and full level a divisor-theoretic basis of the entire $N$-torsion, optionally normalized by the Weil pairing.
6. On an $n$-gon, $E^{\mathrm{sm}}[N]$ has rank $N\gcd(N,n)$. Hence cyclic level forces $n\mid N$, while full level forces $n=N$.
7. Contraction removes exactly the components invisible to a chosen open smooth subgroup and is canonical, equivariant, and compatible with base change.
8. Quotients by finite subgroup schemes extend across polygonal fibers, with toric degree and component quotient accounting for the total degree.
9. The Tate model $\operatorname{Tate}_n(t)$ has period $q=t^n$, special fiber an $n$-gon, and component specialization determined by the valuation of the multiplicative parameter.
10. Prime cyclic level has exactly two cusp types: $(E_q,\mu_p)$ and $(E_{t^p},\langle t\rangle)$. Their quotient formulas are $E_q/\mu_p=E_{q^p}$ and $E_{t^p}/\langle t\rangle=E_t$.

Every imported ingredient has a stated source in the preceding theory: relative ampleness and Proj for contraction, descent for the stack assertions, finite group schemes and Cartier divisors for Drinfeld level, elliptic torsion and the Weil pairing for full level, and Tate uniformization for the cusp formulas. No compactification or later integral-model theorem has been used as a premise.

The hypotheses remain visible in the summary. Rank formulas are geometric-fiber statements. Relative contraction uses finite presentation and a bounded component stratification. Ordinary bases of torsion require the order to be invertible, whereas Drinfeld divisors do not. Formal universality uses the standard component framing; forgetting it introduces finite quotient actions. Prime-level completeness uses primality in reducing the divisor list to $1,p$.

### 14.2 The boundary passed to compactification

The next construction may now begin with an exact functor rather than a collection of desired geometric points. Over a test scheme $S$, its objects are generalized elliptic curves with one of the level structures defined here. The level divisor bounds polygon size and supplies a relative polarization. Projective parameter spaces therefore give bounded charts. Descent makes the charts independent of frames. Tate models give completed charts at every cusp. Contraction makes forgetful maps land in the correct moduli problem, and quotient isogenies define the second degeneracy map.

Several tasks deliberately remain outside this book: proving properness of the resulting compactified stacks, constructing coarse modular curves, resolving exceptional automorphism loci, proving regularity or semistability at the level prime, and computing component intersections. Those are not gaps in the present statements. They are later conclusions whose hypotheses and local inputs have now been constructed.

The boundary data are sufficiently rigid to constrain those later conclusions. A proposed prime-level model must contain exactly the two cyclic cusp types, must pull the unlevelled parameter back as $q$ or $t^p$ according to type, and must realize the degeneracy maps by (13.2)--(13.5). Any model failing these tests has lost either the subgroup divisor, the polygonal components, or the quotient isogeny.

### 14.3 Conclusion

An elliptic curve approaching a cusp does not lose its group law; the group retreats to the smooth locus and leaves a cyclic arrangement of components behind. A generalized elliptic curve records both pieces and the translation action that binds them. The standard $n$-gon is therefore not a decorative boundary fiber. Its toric direction, component group, and nodes are the three geometric shadows of the Tate quotient $\mathbf G_m/q^{\mathbf Z}$.

Level structure must survive the same passage. Distinct torsion points can collide, so an integral basis or generator is a statement about Cartier divisors. Drinfeld's definition retains multiplicity, and ampleness forces the divisor to see the whole polygon. From these two conditions follow the divisibility of polygon size, the two prime cyclic cusp types, and the toric/component decomposition of full level.

Contraction and quotient complete the geometry. Contraction removes components made invisible by forgetting level, while quotient isogenies extend the smooth-group quotient across the nodes. Tate charts then turn these constructions into exact formulas: $q=t^n$ measures the passage around an $n$-gon, $[\zeta_N]$ gives the toric level direction, $[t]$ gives the component direction, and the two prime quotients send the period to $q^p$ or to $t$.

The resulting package is the required foundation for compactified modular geometry. It supplies the objects, their integral level data, their bounded projective control, their cusp deformations, and their prime-level maps in one continuous theory. The boundary is no longer an added set of cusps; it is a moduli-theoretic continuation of elliptic curves, torsion, and isogenies through degeneration.
