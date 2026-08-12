# Compactified Modular Stacks and Coarse Modular Curves

## Contents

1. [The three spaces in modular geometry](#1-the-three-spaces-in-modular-geometry)
   - [Why compactification is a moduli problem](#11-why-compactification-is-a-moduli-problem)
   - [Standing conventions and natural bases](#12-standing-conventions-and-natural-bases)
   - [Stacks, fine covers, and coarse curves](#13-stacks-fine-covers-and-coarse-curves)
2. [The compactified modular functors](#2-the-compactified-modular-functors)
   - [The unlevelled stack](#21-the-unlevelled-stack)
   - [Full, point, and cyclic level](#22-full-point-and-cyclic-level)
   - [Morphisms and the smooth open](#23-morphisms-and-the-smooth-open)
   - [Why the boundary definition is forced](#24-why-the-boundary-definition-is-forced)
3. [Algebraicity and finite diagonal](#3-algebraicity-and-finite-diagonal)
   - [Boundedness supplied by level](#31-boundedness-supplied-by-level)
   - [Framed projective charts](#32-framed-projective-charts)
   - [The diagonal and inertia](#33-the-diagonal-and-inertia)
   - [The algebraicity theorem](#34-the-algebraicity-theorem)
4. [Properness: filling the missing cusp](#4-properness-filling-the-missing-cusp)
   - [The valuative problem](#41-the-valuative-problem)
   - [Potentially good reduction](#42-potentially-good-reduction)
   - [Multiplicative reduction and polygon size](#43-multiplicative-reduction-and-polygon-size)
   - [Existence, uniqueness, and properness](#44-existence-uniqueness-and-properness)
5. [Fine rigidified covers](#5-fine-rigidified-covers)
   - [Auxiliary full level](#51-auxiliary-full-level)
   - [Killing automorphisms](#52-killing-automorphisms)
   - [Representability and projectivity](#53-representability-and-projectivity)
   - [Change of auxiliary level](#54-change-of-auxiliary-level)
6. [Finite quotients and coarse modular curves](#6-finite-quotients-and-coarse-modular-curves)
   - [The change-of-level action](#61-the-change-of-level-action)
   - [Construction of the quotient scheme](#62-construction-of-the-quotient-scheme)
   - [The coarse universal property](#63-the-coarse-universal-property)
   - [Independence and projectivity](#64-independence-and-projectivity)
7. [Cusps and their divisor](#7-cusps-and-their-divisor)
   - [The boundary as a closed substack](#71-the-boundary-as-a-closed-substack)
   - [Tate parameters and cusp widths](#72-tate-parameters-and-cusp-widths)
   - [The Cartier divisor theorem](#73-the-cartier-divisor-theorem)
   - [The cusp on the coarse curve](#74-the-cusp-on-the-coarse-curve)
8. [Exceptional automorphisms](#8-exceptional-automorphisms)
   - [Generic and exceptional inertia](#81-generic-and-exceptional-inertia)
   - [Rigidification by the generic involution](#82-rigidification-by-the-generic-involution)
   - [Completed local rings in the tame case](#83-completed-local-rings-in-the-tame-case)
   - [Characteristics two and three](#84-characteristics-two-and-three)
9. [Stack and coarse geometry compared](#9-stack-and-coarse-geometry-compared)
   - [Points, functions, and residue fields](#91-points-functions-and-residue-fields)
   - [Base change and the tame boundary](#92-base-change-and-the-tame-boundary)
   - [Line bundles and stabilizer characters](#93-line-bundles-and-stabilizer-characters)
   - [Dualizing and Hodge lines](#94-dualizing-and-hodge-lines)
10. [Universal cyclic isogenies](#10-universal-cyclic-isogenies)
    - [Construction on the moduli stack](#101-construction-on-the-moduli-stack)
    - [Descent from a fine cover](#102-descent-from-a-fine-cover)
    - [What descends to a coarse curve](#103-what-descends-to-a-coarse-curve)
    - [Duality and the two cusp formulas](#104-duality-and-the-two-cusp-formulas)
11. [Degeneracy maps and coarse correspondences](#11-degeneracy-maps-and-coarse-correspondences)
    - [Forgetting and quotienting](#111-forgetting-and-quotienting)
    - [Extension across the boundary](#112-extension-across-the-boundary)
    - [Passage to coarse curves](#113-passage-to-coarse-curves)
    - [Graphs and finite correspondences](#114-graphs-and-finite-correspondences)
12. [Normalization and changes of level](#12-normalization-and-changes-of-level)
    - [Finite maps between compactified stacks](#121-finite-maps-between-compactified-stacks)
    - [Normality of finite group quotients](#122-normality-of-finite-group-quotients)
    - [Normalize after base change](#123-normalize-after-base-change)
    - [Limits of the present construction](#124-limits-of-the-present-construction)
13. [The compactified modular-curve package](#13-the-compactified-modular-curve-package)
    - [The main construction theorem](#131-the-main-construction-theorem)
    - [A hypothesis ledger](#132-a-hypothesis-ledger)
    - [Worked comparisons](#133-worked-comparisons)
    - [Dependency closure](#134-dependency-closure)
14. [Conclusion](#14-conclusion)
   - [The completed passage from objects to curves](#141-the-completed-passage-from-objects-to-curves)
   - [What the coarse curve remembers](#142-what-the-coarse-curve-remembers)
   - [Final synthesis](#143-final-synthesis)

## 1. The three spaces in modular geometry

### 1.1 Why compactification is a moduli problem

The affine modular curve parametrizes smooth elliptic curves with level structure. It is not proper. A one-parameter family can run toward a Tate curve whose discriminant tends to zero, and the missing limit is a cusp. Adding one abstract point for each limiting orbit would compactify the underlying set, but it would not answer the questions needed in geometry. Which generalized curve occurs at that point? How does level specialize? What is the local parameter? Which automorphisms survive? Does a quotient isogeny extend? Which objects descend after the automorphisms are forgotten?

The correct compactification is therefore constructed at the level of families. Book 110 supplied the boundary objects: generalized elliptic curves, ample Drinfeld level structures, contractions, quotients by finite subgroup schemes, and Tate charts. The present book assembles those objects into proper algebraic stacks, covers the stacks by fine schemes after adding rigidifying level, takes finite quotients to obtain coarse schemes, and measures exactly what is lost in that final passage.

There are three spaces, not one:

$$
\begin{array}{ccccc}
Y & \longrightarrow & \overline{\mathcal M}(\Gamma)
& \xrightarrow{\pi} & X(\Gamma).\\
\text{fine cover} && \text{moduli stack} && \text{coarse curve}
\end{array} \tag{1.1}
$$

The fine cover carries an honest universal generalized elliptic curve because its auxiliary level kills automorphisms. The stack carries the universal object tautologically and remembers every stabilizer. The coarse curve is a scheme universal for maps from the stack to schemes or algebraic spaces, but it generally carries no universal elliptic curve. Keeping these three roles separate is the main discipline of compactified modular geometry.

### 1.2 Standing conventions and natural bases

A generalized elliptic curve and its level structures have the meanings established in Book 110. In particular, a cyclic subgroup is finite locally free and admits a Drinfeld generator fppf-locally, and every level divisor on a singular fiber is required to be ample. The word cusp means a geometric point at which the generalized elliptic curve is a Néron polygon.

For an integer $N\geq1$ we consider the familiar types

$$
\Gamma(N),\qquad \Gamma_1(N),\qquad \Gamma_0(N).
$$

The integral functors are defined over $\mathbf Z$, using Drinfeld divisors. The main compactified-stack and coarse-curve theorems of this book are over the **good-level base**

$$
B_\Gamma=\operatorname{Spec}\mathbf Z[1/N] \tag{1.2a}
$$

for point and cyclic level, with the evident modification for $N=1$. Full symplectic level also includes a chosen primitive $N$th root and is defined over the corresponding cyclotomic finite etale base; without a fixed pairing, the similitude version is defined over $\mathbf Z[1/N]$. The Drinfeld definitions over primes dividing $N$ remain essential because they identify the correct closure and cusp branches, but constructing and analyzing the integral model at those primes is the next stage. Whenever a statement uses averaging by an additional finite group, its order is separately inverted or a tame hypothesis is stated.

All stacks are fppf stacks. Algebraic stacks are locally of finite presentation over their stated base and have representable diagonal. A coarse space is characterized by its geometric-orbit and categorical universal properties. We use the phrase **coarse modular curve** for the proper one-dimensional coarse scheme over $B_\Gamma$ attached to a modular stack. The phrase does not by itself assert a model at primes removed from $B_\Gamma$; extending across those primes and proving regular or semistable local equations require the later integral-model analysis.

The direct prerequisites are used in precise places. Book 8 supplies ample line bundles, relative Proj, Hilbert parameter spaces, and finite quotients of quasi-projective schemes. Book 11 supplies normalization and the rule that ramified base change may require renormalization. Book 13 supplies algebraic stacks, rigidification, finite quotient stacks, and coarse-space descent. Book 110 supplies every generalized-elliptic and cusp calculation used here.

### 1.3 Stacks, fine covers, and coarse curves

It is useful to distinguish the universal properties before constructing anything.

A fine moduli scheme $Y$ represents a set-valued functor. For every scheme $T$, maps $T\to Y$ correspond to objects over $T$, not merely to geometric isomorphism classes. Consequently the identity map of $Y$ selects a universal object.

A moduli stack $\mathcal X$ represents a groupoid-valued functor. Its identity is again a universal object, but an object over $T$ may have automorphisms. Those automorphisms form the inertia group over the corresponding point. A scheme can represent this groupoid only when all inertia is trivial.

A coarse map $\pi:\mathcal X\to X$ has two properties:

1. over every algebraically closed field, $X$ classifies isomorphism classes of objects of $\mathcal X$;
2. every map from $\mathcal X$ to an algebraic space factors uniquely through $X$.

The second property is stronger than set-theoretic classification. It says that regular functions and morphisms invariant under every change of presentation come from the coarse space. It does not say that objects descend.

The basic local model is a finite quotient. If a finite group $G$ acts on a fine scheme $Y$, then

$$
[Y/G]\longrightarrow Y/G \tag{1.2}
$$

is coarse. The left side remembers the stabilizer $G_y$ of a point; the right side remembers only its orbit. Every global construction below is reduced to this model after adding auxiliary level.

Two elementary examples clarify the extremes. If $G$ acts freely, then $Y\to Y/G$ is a torsor and $[Y/G]\simeq Y/G$; stack and coarse space coincide. If $G$ acts trivially, then $[Y/G]$ is a $G$-gerbe over $Y$, while its coarse space is still $Y$. In the second example the underlying parameter has not been ramified at all, even though every point has stabilizer $G$. Modular stacks combine the two behaviors: the generic involution can act trivially on a local $j$-parameter, while an exceptional residual automorphism acts effectively on the deformation direction.

There is also a practical test for proposed universal constructions. A morphism from the stack to a fixed scheme descends automatically to the coarse curve. A family over the stack descends only if its descent datum has trivial stabilizer action. Thus the $j$-invariant descends, but the universal elliptic curve usually does not. A line bundle occupies the intermediate position: its underlying pointwise isomorphism class is not enough; one must compute the one-dimensional character through which each stabilizer acts on its fiber.

## 2. The compactified modular functors

### 2.1 The unlevelled stack

The unlevelled compactified stack $\overline{\mathcal M}_{1,1}$ assigns to a scheme $S$ the groupoid of generalized elliptic curves $E\to S$. An arrow is an isomorphism preserving the identity, the group law on $E^{\mathrm{sm}}$, and its action on $E$. The open substack $\mathcal M_{1,1}$ consists of smooth elliptic curves.

This definition is intentionally more rigid than “proper genus-one curve with a section.” The translation action distinguishes the group-compatible polygon from unrelated semistable genus-one curves. On a geometric $n$-gon it recovers the extension

$$
0\longrightarrow\mathbf G_m\longrightarrow E^{\mathrm{sm}}
\longrightarrow\mathbf Z/n\mathbf Z\longrightarrow0. \tag{2.1}
$$

Without a level divisor, polygon size is unbounded. Thus the entire stack of all generalized elliptic curves is a union of bounded algebraic pieces rather than one quasi-compact finite-type object. The usual stable compactification of the unlevelled elliptic stack contracts every polygon to a one-gon. Equivalently, one uses the stable generalized elliptic curve attached to the divisor $3[e]$. In this book $\overline{\mathcal M}_{1,1}$ denotes that stable one-gon compactification.

The contraction is canonical. The divisor $3[e]$ meets only the identity component. Book 110 proves that relative Proj contracts all other components, commutes with base change, and is unique. The result has smooth fibers or one-gons. Hence no polygon-size ambiguity remains in the unlevelled compactification.

### 2.2 Full, point, and cyclic level

For a level type $\Gamma$, define $\overline{\mathcal M}(\Gamma)$ as follows.

- For $\Gamma_1(N)$ an object is $(E,P)$, where $P\in E^{\mathrm{sm}}[N](S)$ is a Drinfeld generator of a finite locally free cyclic subgroup of rank $N$, and its orbit divisor $\sum_{a\bmod N}[aP]$ is ample.
- For $\Gamma_0(N)$ an object is $(E,C)$, where $C\subset E^{\mathrm{sm}}$ is a finite locally free cyclic subgroup of rank $N$ and its divisor is ample.
- For $\Gamma(N)$ an object is $(E,P,Q)$ whose indexed sums fill $E^{\mathrm{sm}}[N]$ as a divisor, whose full torsion divisor is ample, and, in the symplectic version, for which $e_N(P,Q)$ is the chosen Drinfeld primitive root.

Arrows preserve all displayed data. The smooth opens $\mathcal M(\Gamma)$ are obtained by requiring $E/S$ to be elliptic. On the smooth open, ampleness is automatic because there is only one component. If $N$ is invertible, Drinfeld generation becomes ordinary exact-order generation, so these opens recover the classical moduli problems.

On a geometric $n$-gon,

$$
\operatorname{rank}E^{\mathrm{sm}}[N]=N\gcd(N,n). \tag{2.2}
$$

It follows that cyclic level forces $n\mid N$, whereas full level forces $n=N$. The proof is worth recalling because it prevents an incorrect compactification. Cyclic ampleness makes the component image surjective, so $n$ divides the subgroup rank $N$. For full level, equality with the entire kernel gives $N\gcd(N,n)=N^2$, hence $N\mid n$; ampleness makes multiplication by $N$ kill the component group, hence $n\mid N$.

### 2.3 Morphisms and the smooth open

Forgetting level does not always mean leaving the underlying polygon unchanged. If a retained divisor sees only a subgroup of the component group, the invisible components must be contracted. Thus every forgetful map is understood as

$$
(E,\text{large level})\longmapsto(E,D)
\longmapsto(E_{G_D},D), \tag{2.3}
$$

where $G_D$ is the union of components met by $D$. The construction is compatible with arbitrary base change and isomorphisms. It therefore defines a morphism of stacks.

For cyclic level there are two maps to the unlevelled compactification:

$$
\pi_1(E,C)=\operatorname{st}(E),\qquad
\pi_2(E,C)=\operatorname{st}(E/C), \tag{2.4}
$$

where $\operatorname{st}$ contracts to the one-gon model when necessary. Book 110 proves that $E/C$ exists as a generalized elliptic curve and that the quotient is finite of generic degree $N$. These two maps extend the usual source and target maps of a cyclic isogeny.

The smooth open is dense in every modular stack considered here. On a Tate chart the boundary is $q=0$ or $t=0$, so its complement is schematically dense. On an arbitrary connected chart, a whole component contained in the boundary would classify only polygons; the deformation $xy=t$ smooths each node and shows that such a component meets the elliptic locus. This density lets identities proved for smooth elliptic curves extend to the compactification whenever both sides are morphisms between separated targets.

### 2.4 Why the boundary definition is forced

Three weaker definitions fail.

First, requiring only $NP=0$ admits the zero section in characteristic dividing $N$. It says nothing about the length-$N$ subgroup divisor. Drinfeld generation repairs this by the equality

$$
\sum_{a\bmod N}[aP]=C. \tag{2.5}
$$

Second, requiring a finite cyclic subgroup but omitting ampleness permits, for example, $\mu_5$ on the identity component of a $100$-gon. Polygon size would then be unbounded at fixed level and no finite-type compactification could result.

Third, contracting every degeneration to a one-gon before recording level loses component-direction points. At prime level $p$, the class of $t$ on $E_{t^p}$ specializes to the next component of a $p$-gon. On the contracted one-gon it approaches the node and no longer lies in the smooth locus. Resolving to the $p$-gon is therefore part of extending the level, not a discretionary regularization.

These failures show that generalized curve, divisor-theoretic level, and ampleness form one definition. None can be reconstructed safely from geometric point sets afterward.

## 3. Algebraicity and finite diagonal

### 3.1 Boundedness supplied by level

Let $D$ be an ample level divisor of degree $d$. On a polygon, $D$ has positive degree on every component. Consequently there are at most $d$ components. This numerical observation supplies the boundedness needed for algebraicity.

Choose a sufficiently large integer $m$, depending only on $d$. The line bundle

$$
\mathcal L=\mathcal O_E(mD) \tag{3.1}
$$

has vanishing first cohomology on every geometric fiber and separates length-two subschemes. Indeed, on the normalization of a polygon its restriction to every component has degree at least $m$. For $m\geq3$, sections separate two smooth points, tangent directions, and the two branches at every node; the normalization exact sequence imposes only matching values at nodes. The same conclusion holds for a smooth genus-one fiber by the degree criterion. Upper semicontinuity and the finite list of component distributions make one $m$ work in families.

Thus $\mathcal L$ is relatively very ample, $\pi_*\mathcal L$ is locally free after the usual base-change stratification, and its rank and Hilbert polynomial range over a finite list determined by $d$. Taking a finite disjoint union of the corresponding Hilbert schemes handles that list. No unbounded parameter space is being invoked.

The numerical calculation is especially transparent in genus one. If $D$ has total degree $d$ on a geometric fiber and positive degree on every component, then for every $r>0$,

$$
\chi(E,\mathcal O_E(rD))=rd. \tag{3.1a}
$$

For $r$ large, $H^1(E,\mathcal O_E(rD))=0$. On a smooth fiber this follows from duality, since the dual bundle has negative degree. On a polygon, pull back to the disjoint normalization. Each component restriction has nonnegative degree and at least one positive degree on every connected subcurve; the only compatible section of the dual is zero. The normalization exact sequence then gives the same vanishing. Consequently $h^0=rd$ and the embedding has fixed linear Hilbert polynomial.

To see separation at a node, let $x$ and $y$ be the two preimages on the normalization. A section on the polygon is a tuple of component sections whose values at $x$ and $y$ agree under the gluing. Positive degree supplies sections with prescribed first-order value on either branch, and another section adjusts the common value. For $m$ uniformly large, these sections distinguish the two tangent directions in $k[[X,Y]]/(XY)$. This is why positivity on every component embeds the singular curve rather than merely its normalization.

The finite list of multidegrees also controls the graphs of the group law and level maps. Their Hilbert polynomials in the fixed projective products are bounded because translation preserves degree. Hence the graph parameter spaces used below are finite unions of Hilbert schemes, not an unbounded space of all maps.

For the unlevelled stable stack, $D=3[e]$ on the contracted one-gon model plays the same role. It has degree three on every fiber and gives the Weierstrass cubic embedding.

### 3.2 Framed projective charts

Fix one Hilbert polynomial and choose a basis of $\pi_*\mathcal L$. The basis embeds the family into a fixed projective space. Book 8 constructs a projective Hilbert scheme carrying the universal embedded curve. Within it the required conditions are locally closed:

- flat connected genus-one fibers and nodal-or-smooth geometry are open conditions inside the appropriate closed Hilbert locus;
- the identity section is represented by the relative smooth locus;
- graphs of multiplication and the action belong to bounded Hilbert schemes;
- group identities and preservation of the embedded curve are closed equalities of morphisms;
- the finite level divisor belongs to a length-$d$ Hilbert scheme;
- subgroup, Drinfeld, pairing, and torsion conditions are closed polynomial conditions;
- ampleness is the open condition that the divisor meet every geometric component.

The last assertion is also closed on each fixed polygon stratum, because failure to meet a component is constant in the finite component group. Hence the desired framed objects form a finite-type locally closed scheme $H$.

Changing the basis acts through $G=\operatorname{GL}_r$. Every unframed family acquires a basis after passing to its frame bundle, a $G$-torsor. Two framed objects represent the same unframed object exactly when they differ by this action. Therefore the moduli stack is locally

$$
[H/G]. \tag{3.2}
$$

Since $G$ is smooth affine, $H\to[H/G]$ is a smooth surjective atlas. This proves algebraicity once the diagonal is known to be representable.

### 3.3 The diagonal and inertia

Given two objects $(E,\alpha)$ and $(E',\alpha')$ over a scheme $T$, their isomorphism functor is a closed subfunctor of the projective isomorphism scheme determined by (3.1). Preservation of the identity, group law, action, and level is expressed by equalities of morphisms, so it is closed. Thus the diagonal is representable and separated.

It is also finite. On every geometric fiber an origin-preserving automorphism of a smooth elliptic curve is finite. On a polygon, an automorphism preserving the generalized-elliptic action and ample level is determined by its action on the torus and the finite component group, so again only finitely many occur. The isomorphism scheme is affine because it sits in a projective linear group, and it is proper by the extension property for isomorphisms of stable marked genus-one curves: after passing to a DVR, an isomorphism on the generic fiber preserves the ample divisor and therefore extends to the Proj model. An affine proper quasi-finite morphism is finite.

The finiteness proof uses boundedness. Without a component bound, the disjoint collection of automorphism schemes over all polygon sizes need not be quasi-compact. Level or stable contraction supplies exactly the missing bound.

The geometric fiber of the inertia stack at $(E,\alpha)$ is

$$
\operatorname{Aut}(E,\alpha). \tag{3.3}
$$

This group may be nontrivial even when it acts trivially on the deformation parameter. That distinction becomes important at coarse points.

### 3.4 The algebraicity theorem

**Theorem 3.1.** The stable unlevelled stack $\overline{\mathcal M}_{1,1}$ and each compactified level stack $\overline{\mathcal M}(\Gamma)$ are algebraic stacks of finite presentation over $B_\Gamma$. Their diagonals are finite and separated. They are smooth, hence flat and normal, of pure relative dimension one. The smooth-elliptic locus is open and dense, and its boundary has pure relative codimension one.

**Proof.** The bounded ample divisor gives finitely many framed Hilbert parameter schemes. Section 3.2 makes each desired moduli condition locally closed and produces a smooth atlas. Section 3.3 proves that the diagonal is finite and separated. Finite presentation follows from the finite equations and the finite list of Hilbert polynomials. Smoothness of $E/S$ is open, so the elliptic locus is open; density was proved in Section 2.3. On a Tate chart the boundary is cut out by one non-zero-divisor, giving relative codimension one.

On the elliptic locus, level is finite etale over the smooth relative curve $\mathcal M_{1,1}$; for the unlevelled problem this is the identity statement. At a boundary point, choose the finite etale framing of Book 110. The completed local ring of the framed algebraic chart is $A[[t]]$, where $A$ is finite etale over the stated base. Thus the completed structural map is formally smooth of relative dimension one. For morphisms of finite presentation, smoothness can be tested after completion at geometric points, so the boundary charts are smooth as well. The elliptic locus and these boundary neighborhoods cover the stack. It follows that the stack is smooth, flat, and of pure relative dimension one.

For completeness, normality can also be read directly from the same charts. The ring $A$ is excellent and normal, hence so is $A[[t]]$. The uncompleted local ring is excellent, its completion is faithfully flat, and normality descends from that completion. It then descends through the etale framing and is local for the smooth topology. Finally, $t$ is one relative parameter, so $t=0$ has pure relative codimension one. $\square$

The theorem is deliberately over the good-level base. The same Drinfeld functor is defined integrally, but algebraic closure, normality, and special-fiber structure at primes dividing $N$ require additional deformation calculations. This separation prevents the later integral-model theory from being assumed prematurely.

## 4. Properness: filling the missing cusp

### 4.1 The valuative problem

An algebraic compactification becomes proper only when every punctured one-parameter family has a boundary value. Let $R$ be a valuation ring with fraction field $K$, and let $(E_K,\alpha_K)$ be an elliptic curve with level over $K$. The valuative criterion for a proper algebraic stack asks, after a finite extension of $K$ and replacement of $R$ by a dominating valuation ring if necessary, for an extension to an object over $R$. Uniqueness is tested up to a unique isomorphism after common domination.

Passing to a finite extension is not an evasion. A stack point can have monodromy, and the valuative criterion for algebraic stacks naturally permits a finite extension that kills it. For a coarse scheme the resulting point will descend by the coarse universal property and properness.

It is enough to work with discrete valuation rings in the noetherian finite-presentation setting. Given a valuation ring of higher rank, all coefficients of the elliptic equation, the finitely many level equations, and a candidate extension occur in a finitely generated subalgebra. A specialization chain reduces the check to rank-one valuation rings. Conversely, extensions over these approximations pass to the filtered limit. This reduction is what lets Tate parameters and regular curve models do the geometric work.

Separatedness has its own valuative meaning. If two extensions are generically isomorphic, the isomorphism is a point of the finite diagonal over the generic point of $\operatorname{Spec}R$. Properness of that finite morphism extends it, and separatedness makes the extension unique. Thus once existence is established, there is no second boundary value hidden behind the same generic family.

The needed elliptic reduction statement has two outcomes after finite extension: good reduction or split multiplicative reduction. For dependency closure, the next lemma proves it from Weierstrass coefficients and the Tate inverse series. We then extend the level in each outcome.

**Lemma 4.0 (potential semistability in genus one).** Let $K$ be the fraction field of a complete DVR and let $E/K$ be an elliptic curve. After a finite extension of $K$, the curve has good or split multiplicative reduction.

**Proof.** The sign of $v(j(E))$ separates the two constructions.

Suppose first that $v(j)<0$. The inverse Tate series gives a unique $q$ with $v(q)>0$ and $j(E_q)=j(E)$. Indeed,

$$
j(q)^{-1}=q+O(q^2)
$$

has an inverse convergent on the maximal ideal. Over an algebraic closure, elliptic curves with the same $j$ are isomorphic. The isomorphism is a solution of finitely many algebraic coefficient equations, so it is defined over a finite extension; this formulation also covers residue characteristics $2$ and $3$ without using the language of quadratic twists. After that extension $E\simeq E_q$, which has split multiplicative reduction by the integral Tate equation.

Now suppose $v(j)\geq0$. Start with an integral minimal generalized Weierstrass equation and invariants $c_4,c_6,\Delta$. We use the following integral reconstruction step, including its small-characteristic content.

> Let $\rho$ have positive valuation $h$ in a finite extension. If a generalized
> Weierstrass equation has $v(c_4)\geq4h$, $v(c_6)\geq6h$, and
> $v(\Delta)\geq12h$, then, after a further finite extension, admissible
> translations of $x$ and $y$ put its coefficients in valuation at least
> $ih$ in weights $i=1,2,3,4,6$. Dividing the weight-$i$ coefficient by
> $\rho^i$ then gives another integral equation, with invariants
> $\rho^{-4}c_4$, $\rho^{-6}c_6$, and $\rho^{-12}\Delta$.

Here is the coefficient argument. Reduce the cubic and adjoin the coordinates of its singular point; translating that point to $(0,0)$ kills the constant and linear terms modulo the maximal ideal. Adjoin a slope of the repeated tangent and make the admissible change $y\mapsto y+sx$; this kills the remaining quadratic tangent term. The identities

$$
b_2=a_1^2+4a_2,\quad
b_4=a_1a_3+2a_4,\quad
b_6=a_3^2+4a_6,
$$

together with $c_4=b_2^2-24b_4$, $c_6=-b_2^3+36b_2b_4-216b_6$, and the discriminant identity then determine successively the weighted residues of $a_1,a_2,a_3,a_4,a_6$. Repeat this calculation through the finitely many valuation layers below $h,2h,3h,4h,6h$. If a residue does not yet vanish, adjoining a root of the corresponding monic tangent or translation polynomial and repeating the admissible translation makes it vanish. Only finitely many weighted residues occur, so all required elements lie in one finite extension and the result is

$$
v(a_1)\geq h,\quad v(a_2)\geq2h,\quad v(a_3)\geq3h,
\quad v(a_4)\geq4h,\quad v(a_6)\geq6h. \tag{4.0a}
$$

This uses no division by $2$ or $3$; those primes are exactly why the singular-point and repeated-tangent translations precede the weighted division. Substituting $x=\rho^2x'$ and $y=\rho^3y'$ proves the reconstruction step.

After a finite ramified extension, choose $\rho$ with

$$
12v(\rho)=v(\Delta). \tag{4.0b}
$$

The invariant identities give

$$
v(c_4^3/\Delta)=v(j)\geq0,
\qquad
v(c_6^2/\Delta)=v(j-1728)\geq0, \tag{4.0c}
$$

and hence $v(c_4)\geq4v(\rho)$ and $v(c_6)\geq6v(\rho)$. The reconstruction step gives an integral equation with invariants $\rho^{-4}c_4$, $\rho^{-6}c_6$, and $\rho^{-12}\Delta$. The last is a unit. Its projective cubic is therefore smooth, so $E$ has good reduction.

For a noncomplete henselian DVR the same finite equations descend from the completion after a finite extension; a general DVR is handled after henselization, which is faithfully flat. Thus a finite extension suffices in every valuative case used here. $\square$

The proof also recovers the sharper dichotomy: integral $j$ leads to potentially good reduction, while negative $j$ leads to potentially multiplicative reduction. The further finite extension in the latter case splits the two branches of the node.

### 4.2 Potentially good reduction

Assume $E_K$ extends to an elliptic curve $E/R$. We are proving properness over $B_\Gamma$, so $N$ is invertible in $R$. Consequently $E[N]\to\operatorname{Spec}R$ is finite etale of rank $N^2$. After a finite extension of $K$ and normalization of $R$, all the finitely many torsion sections occurring in the level become rational. Because a finite morphism is proper, each of these sections extends uniquely over the new valuation ring.

For cyclic level, a split generic subgroup is generated by one of the extended sections; the union of its $N$ disjoint translates is a finite etale subgroup of rank $N$. For point and full level, the generator or basis extends in the same way. The group, torsion, and Weil-pairing equations are equalities between sections of separated finite schemes, so equality on the generic point implies equality over the valuation ring. The Drinfeld divisor equalities reduce here to the ordinary lists of distinct torsion sections and hence extend as well.

This good-level argument intentionally uses etaleness. At a prime dividing $N$, schematic closure of a generic subgroup requires a separate finite-flat analysis; torsion-freeness of a closure alone does not prove all the needed subgroup and base-change assertions. Those primes are outside the properness theorem of this book.

There is only one component, so every nonempty finite level divisor is ample. Hence good reduction supplies an object of the compactified level stack.

### 4.3 Multiplicative reduction and polygon size

After finite extension, split multiplicative reduction is described by a Tate parameter $q\in K$ with $v(q)>0$. Write $q=t^n$ after a further extension, choosing $n$ to match the component image required by the level. The model $\operatorname{Tate}_n(t)$ has special fiber an $n$-gon, and a point represented by

$$
u=\varepsilon t^a
$$

meets component $a\bmod n$.

For a $\Gamma_1(N)$ point or a cyclic subgroup, its component image has some order $n$ dividing $N$. After extending scalars to split the subgroup and extract the needed root of $q$, choose the $n$-gon model. The orbit divisor meets all $n$ components and is therefore ample. Its scheme structure extends by the monic Drinfeld equations. Those equations remain meaningful even in residue characteristic dividing $N$, which is why this valuative description will still identify the later integral closure.

Write $N=ne$. On the split $n$-gon a standard generator has the form

$$
P=(\xi,1), \tag{4.1a}
$$

where $\xi$ is a Drinfeld primitive $N$th root after an fppf extension. The multiples of $P$ visit every component $e$ times. On one component their toric coordinates differ by powers of $\xi^n$, and the resulting degree-$e$ divisor fills $\mu_e$. Hence the orbit has rank $ne=N$, is a subgroup divisor, and has positive degree $e$ on every component. This verifies generation and ampleness simultaneously.

Conversely, if an extension existed on an $m$-gon, ampleness would make the component image all of $\mathbf Z/m\mathbf Z$, so $m\mid N$. The order of that image is fixed by the generic monodromy of the subgroup, forcing $m=n$. Polygon size is therefore unique, not merely one convenient choice.

For full level, the rank calculation forces $n=N$. One basis vector specializes in the toric direction and the other in the component direction. After a suitable fppf extension the standard form is

$$
P=(\zeta_N,0),\qquad Q=(1,1) \tag{4.1}
$$

on the $N$-gon. Their indexed divisor is the full $N$-torsion and meets every component.

This argument proves more than existence of a limiting point. It determines the model on which the level remains in the smooth locus. Choosing fewer components would push a component-direction point into a node; choosing more would violate ampleness.

### 4.4 Existence, uniqueness, and properness

**Theorem 4.1.** Each stack $\overline{\mathcal M}(\Gamma)$ is proper over $B_\Gamma$. The same holds for $\overline{\mathcal M}_{1,1}$ over $\mathbf Z$.

**Proof strategy.** Finite presentation and separatedness are already known. It remains to prove the existence part of the valuative criterion, then uniqueness.

**Proof.** Lemma 4.0 gives the good and split multiplicative cases after finite extension. Sections 4.2 and 4.3 extend the curve and the level in each case. For the unlevelled problem, contract any polygon to its stable one-gon.

For uniqueness, suppose two extensions become objects over a common dominating valuation ring. On the generic fiber they are isomorphic. The ample level divisor, or $3[e]$ in the stable unlevelled case, gives each extension as relative Proj of its section algebra. The generic isomorphism identifies the divisors and their section algebras inside the common function field. Integral closure across the valuation ring and equality in sufficiently high degrees identify the two Proj models. Equivalently, the finite separated diagonal is proper, so the generic isomorphism extends uniquely. Thus the valuative criterion holds. $\square$

The theorem is a stack theorem. It allows stabilizers at the limiting object. The valuative argument was written in divisor-theoretic language so it also identifies the candidates for integral closure at a level prime, but properness of that integral model is not being claimed here.

## 5. Fine rigidified covers

### 5.1 Auxiliary full level

To turn the stack into a scheme chart that is finite rather than merely smooth, add a second full level on the **smooth** modular curve. Choose an integer $M\geq3$ invertible on the base and, when useful, coprime to $N$. Put

$$
U_M=\mathcal M(\Gamma)\times_{\mathcal M_{1,1}}\mathcal M(M). \tag{5.1}
$$

An object of $U_M$ is a smooth $\Gamma$-object together with a full $M$-basis. If a symplectic basis is used, the base also carries the prescribed Weil-pairing value. The map $U_M\to\mathcal M(\Gamma)$ is finite etale, and full level $M\geq3$ kills automorphisms.

One must not compactify this cover by requiring the two levels to be ample on the same polygon. Full level $M$ forces an $M$-gon, whereas cyclic level $N$ forces polygon size dividing $N$. When $(M,N)=1$, those conditions can be incompatible. The correct construction retains the finite extension of the smooth modular function algebra and normalizes at the boundary.

The modular meaning of a normalization branch must nevertheless be stated. Over a Tate chart, adjoining the auxiliary basis also adjoins a root of the smoothing parameter. The resulting generalized curve $E'$ is the unique **decontraction** of the original compactified curve $E$ on which the full $M$-divisor is ample. It carries full level $M$ and a compatible contraction

$$
E'\longrightarrow E. \tag{5.1a}
$$

Book 13 constructs this finite decontraction datum, and Book 110 identifies it in the Tate charts. Thus a boundary point of the auxiliary compactification is not merely an unlabeled branch of a function field: it is a decontracted generalized elliptic curve with rigid full level and its contraction to the original $\Gamma$-object. Forgetting (5.1a) would leave room for special-fiber automorphisms that do not extend to the generic auxiliary basis.

Book 13's finite decontraction construction represents these data by a fine quasi-projective scheme $Y_M$ and gives a representable finite surjective map

$$
f_M:Y_M\longrightarrow\overline{\mathcal M}(\Gamma). \tag{5.2}
$$

The elliptic part is $U_M$. At the boundary the finite choices are precisely the decontractions, roots of the Tate parameter, roots of unity, and full bases just described. Since the target is proper, the finite scheme $Y_M$ is proper over the base. A proper quasi-projective scheme is projective. It is normal: this holds on $U_M$, while the completed local rings on the boundary branches are the normal rings in the following calculation. Excellence and faithful flatness of completion return normality of the algebraic local rings. Equivalently, $Y_M$ is the normalization of any projective closure of $U_M$ in its finite modular function algebra; Book 11 makes that normalization finite.

Locally, suppose the original framed cusp has completed ring $A[[q]]$. An auxiliary branch has a parameter $s$ with

$$
q=s^r \tag{5.2a}
$$

and a finite cyclotomic coefficient extension $A'/A$. The branch ring $A'[[s]]$ is finite over $A[[q]]$: it is generated by a finite $A$-basis of $A'$ and by $1,s,\ldots,s^{r-1}$. Its generic fiber is the selected auxiliary-level function-field branch. When $A'$ is normal, integral closedness of the power-series ring identifies it with the completed normalization. This verifies finiteness at precisely the new points, the cusps.

Surjectivity follows from properness. The image of $Y_M$ is closed and contains the dense smooth open after the finite etale extension that supplies an auxiliary basis. Every irreducible component of the compactified stack meets the smooth open, so the image contains every component and hence every boundary orbit.

The normalization description also explains a boundary point of $Y_M$. It is a branch of auxiliary smooth level approaching the original compactified $\Gamma$-object, represented by the decontraction (5.1a). The auxiliary basis is ample on $E'$, not necessarily on the original polygon $E$. Its contraction records the normalization branch and its monodromy while returning the original boundary object.

### 5.2 Killing automorphisms

**Lemma 5.1.** The normalized compactification $Y_M$ of the smooth auxiliary full-level cover has no residual object automorphisms.

**Proof.** On the dense smooth open, an automorphism fixing a basis of $E[M]$ acts trivially on $M$-torsion. An origin-preserving elliptic automorphism has finite order. If an odd prime $\ell$ divides $M$, its faithful action on the $\ell$-adic Tate module lies in $1+\ell M_2(\mathbf Z_\ell)$; if $M$ has no odd prime divisor, then $4\mid M$ and the action lies in $1+4M_2(\mathbf Z_2)$. Both congruence groups are torsion-free. Indeed, after reducing to an element of prime order, the first nonzero term in the binomial expansion of $(1+\ell^aB)^r-1$ has strictly smaller $\ell$-adic valuation than the later terms, for odd $\ell$ with $a\geq1$ and for $\ell=2$ with $a\geq2$. It therefore cannot vanish unless $B=0$. Faithfulness of the Tate-module action gives the identity automorphism.

At a boundary point, use the decontracted curve $E'$ of (5.1a). Its ample full $M$-basis fixes both the toric and component directions. Book 110's polygon calculation therefore makes every automorphism of $(E',\text{full }M\text{-level})$ the identity. Compatibility with the contraction then fixes the entire auxiliary object. This direct special-fiber argument is necessary: a new automorphism of one special fiber need not extend to the generic point of an arbitrary family, so density alone would not rule it out. $\square$

The bound is sharp in the relevant sense: inversion fixes full level two. Smaller point levels can also retain exceptional automorphisms.

### 5.3 Representability and projectivity

The construction already makes $Y_M$ a normal projective scheme. Lemma 5.1 explains its modular fineness. It carries the universal decontracted curve with full $M$-level, its contraction, and therefore the pullback of the tautological generalized elliptic curve with the original $\Gamma$-data. Over the dense smooth open the contraction is the identity. At the boundary the auxiliary basis lives on the decontraction rather than being forced onto an incompatible original polygon.

Projectivity follows because the finite map to the proper stack makes $Y_M$ proper and its Hilbert construction makes it quasi-projective. The normal-projective-closure description gives the same scheme by the boundary calculation above.

This proves:

**Theorem 5.2.** On a base on which $M\geq3$ is invertible, adjoining auxiliary full level $M$ on the smooth locus and taking normalized projective closure with its boundary decontraction produces a projective fine scheme $Y_M$, finite and surjective over the restricted compactified stack. It carries the universal decontraction with full $M$-level, its contraction, and the pullback compactified $\Gamma$-data.

No universal object has yet been asserted on the eventual coarse quotient. The universal object on $Y_M$ is the datum from which descent obstructions will be read.

### 5.4 Change of auxiliary level

Two auxiliary levels $M$ and $M'$ give different normalized fine covers but not different coarse curves. On the common smooth open, add both levels and normalize its projective closure. Denote the result by $Y''$. There are finite equivariant maps

$$
Y''\longrightarrow Y_M,\qquad Y''\longrightarrow Y_{M'}. \tag{5.3}
$$

Every invariant map from either fine cover to an algebraic space pulls back to the same invariant map on $Y''$. The finite quotient universal property then identifies the two orbit schemes. This common-refinement argument will prove independence without choosing coordinates or comparing rings one cusp at a time.

Auxiliary level is therefore a construction device. It rigidifies the moduli problem, provides a projective scheme on which a finite group acts, and is removed by a categorical quotient.

## 6. Finite quotients and coarse modular curves

### 6.1 The change-of-level action

Throughout Sections 6.1--6.3, restrict to an open of $B_\Gamma$ on which the chosen $M$ is invertible. Let $Y_M$ be the normalized fine cover there. The finite change-of-basis group $G_M$ acts on its dense smooth open by changing the auxiliary basis while leaving the original $\Gamma$-data fixed. Every such automorphism extends uniquely to the normalization, so $G_M$ acts on all of $Y_M$. In the symplectic case it preserves the chosen Weil pairing; in the similitude formulation the determinant acts simultaneously on the cyclotomic datum.

There is an equivalence

$$
\overline{\mathcal M}(\Gamma)\simeq[Y_M/G_M]. \tag{6.1}
$$

Over the smooth locus this is the usual torsor proof: the sheaf of auxiliary bases is a $G_M$-torsor, and equivariant descent forgets that basis. At the boundary, a quotient-stack object consists fppf-locally of the decontraction (5.1a), its full $M$-basis, and its contraction to the original $\Gamma$-curve. Changing the basis permutes exactly these finite choices. Descent of the contraction therefore returns a $\Gamma$-object. Conversely, Book 13's finite decontraction construction gives such data fppf-locally on every $\Gamma$-object, and two choices differ by a unique element of $G_M$. The overlap elements satisfy the torsor cocycle. These two constructions are inverse, proving (6.1) as an equivalence of groupoids rather than merely a bijection on geometric points. The Tate branch rings $A'[[s]]/A[[q]]$ computed in Section 5.1 verify the same statement on completed boundary charts.

At a point $y\in Y_M$, the stabilizer in $G_M$ is naturally the automorphism group of the underlying $\Gamma$-object together with its action on the chosen branch. Thus (6.1) retains exactly the inertia that auxiliary level removed.

### 6.2 Construction of the quotient scheme

Because $Y_M$ is projective, it is quasi-projective. Book 8's finite quotient theorem constructs the scheme

$$
X(\Gamma)=Y_M/G_M, \tag{6.2}
$$

and the map $Y_M\to X(\Gamma)$ is finite and surjective. On a $G_M$-stable affine $\operatorname{Spec}A\subset Y_M$, the quotient is

$$
\operatorname{Spec}A^{G_M}. \tag{6.3}
$$

The inclusion $A^{G_M}\subset A$ is integral because every $a\in A$ satisfies

$$
\prod_{g\in G_M}(T-ga), \tag{6.4}
$$

a monic polynomial with invariant coefficients. Finite generation makes the integral map finite. Stable affine quotients glue, giving (6.2).

The stable affine neighborhoods can be constructed from an ample bundle. Let $y\in Y_M$. Choose, in a high power of an ample line bundle, a section whose affine nonvanishing locus contains the finite orbit $G_My$. Multiplying its translates gives an invariant section

$$
s_G=\prod_{g\in G_M}g(s). \tag{6.4a}
$$

whose nonvanishing locus is invariant, affine, and contains the orbit. These opens cover $Y_M$. On an overlap obtained by localizing at an invariant element $f$,

$$
(A_f)^{G_M}=(A^{G_M})_f. \tag{6.4b}
$$

Therefore the affine quotients glue. This is the scheme-level reason quasi-projectivity suffices for a finite quotient.

The quotient is projective. One proof takes an ample line bundle $\mathcal L$ on $Y_M$, tensors all its translates, and obtains a $G_M$-linearized ample line bundle

$$
\mathcal A=\bigotimes_{g\in G_M}g^*\mathcal L. \tag{6.5}
$$

A suitable power descends to an ample bundle on the quotient. Equivalently, a finite surjective image of a projective scheme is projective in this setting.

The quotient is also normal. On every invariant affine chart this is Lemma 12.1 applied to the normal ring upstairs, componentwise if the group permutes components. It is flat over $B_\Gamma$: an invariant subring of a torsion-free algebra is torsion-free, and over the Dedekind bases in Section 1.2 finite-type torsion-free modules are flat. These properties are local on the base and therefore survive the gluing below.

### 6.3 The coarse universal property

**Theorem 6.1.** On the open base fixed in Section 6.1, the map

$$
\pi:\overline{\mathcal M}(\Gamma)\longrightarrow X(\Gamma) \tag{6.6}
$$

is a coarse moduli map.

**Proof.** Using (6.1), a map from the stack to an algebraic space $Z$ pulls back to a $G_M$-invariant map $Y_M\to Z$. On every stable affine chart, the invariant-ring universal property gives a unique map $\operatorname{Spec}A^{G_M}\to Z$. These maps agree on overlaps and give a unique map $X(\Gamma)\to Z$. This proves categorical universality.

Over an algebraically closed field, two points of $Y_M$ map to the same quotient point exactly when their orbit closures meet. Finite-group orbits are already closed, so this happens exactly when they lie in the same orbit. Such an orbit is precisely one isomorphism class of $\Gamma$-objects. Thus geometric isomorphism classes map bijectively to geometric points of $X(\Gamma)$. $\square$

The proof also explains why the stack-to-coarse map need not be representable: its fiber over a coarse point retains the classifying stack of the stabilizer.

### 6.4 Independence and projectivity

The coarse universal property makes $X(\Gamma)$ independent, up to unique isomorphism, of $M$, of the projective closure, and of every common refinement used in the construction. Any two candidates receive the stack and are universal for the same maps, so their universal arrows are inverse.

One auxiliary integer need not be invertible on the entire natural arithmetic base. This causes no global gap. The two opens $\operatorname{Spec}\mathbf Z[1/2]$ and $\operatorname{Spec}\mathbf Z[1/3]$ cover $\operatorname{Spec}\mathbf Z$. Use auxiliary level $4$ on the first and level $3$ on the second. Their coarse quotients agree uniquely over $\mathbf Z[1/6]$ and therefore glue. The same construction works after finite base change. Notice that this gives local quotient presentations; it does not falsely assert one global presentation $[Y_M/G_M]$ when no single $M$ is invertible on the entire base.

More explicitly, let $B'$ be the disjoint union of these two opens after base change to $B_\Gamma$. Then $B'\to B_\Gamma$ is faithfully flat, and the disjoint union of the level-$4$ and level-$3$ fine curves is projective over $B'$ and finite surjective over $\overline{\mathcal M}(\Gamma)_{B'}$. Thus arguments on ordinary projective curves may always be made after this faithfully flat base cover and descended. What is unavailable in general is a single projective fine curve over $B_\Gamma$ carrying one constant auxiliary level.

There is also a direct global projectivity check which avoids asking local auxiliary polarizations to agree. On the stable unlevelled stack, the generalized Weierstrass invariants give

$$
\overline{\mathcal M}_{1,1}\longrightarrow\mathbf P^1_{\mathbf Z},
\qquad E\longmapsto[c_4(E)^3:\Delta(E)]. \tag{6.6a}
$$

Admissible coordinate changes multiply both entries by the same twelfth power, and they never vanish simultaneously on a smooth or nodal generalized elliptic curve. On the smooth chart their ratio is the $j$-invariant, while the Tate equation sends the cusp to $[1:0]$. The coarse universal property on the two auxiliary opens therefore factors (6.6a) through a global map $X(1)\to\mathbf P^1_{\mathbf Z}$. It is proper and quasi-finite: over an algebraically closed field, $j$ classifies elliptic curves and there is one nodal orbit at infinity. Hence it is finite. The local invariant quotients are normal by Lemma 12.1 below, so $X(1)$ is normal; its dense characteristic-zero fiber has the usual $j$ as a coordinate, making the finite map birational. A finite birational map to the normal integral scheme $\mathbf P^1_{\mathbf Z}$ is an isomorphism. Thus $X(1)=\mathbf P^1_{\mathbf Z}$ without importing a later modular-form calculation.

For general $\Gamma$, forgetting level and contracting invisible components is representable, proper, and quasi-finite: a fixed stable generalized elliptic curve has only finitely many decontractions and finite level choices. Properness follows from the valuative extension already proved, and quasi-finiteness from the component and torsion bounds. Hence the induced coarse map

$$
X(\Gamma)\longrightarrow X(1)_{B_\Gamma} \tag{6.6b}
$$

is finite, as can be checked on the finite auxiliary covers. A finite morphism to the projective line is projective. Thus the glued coarse curve is globally projective even when no single auxiliary integer is invertible on the whole base.

On every auxiliary open, the coarse curve is the finite quotient of a proper fine cover and is therefore proper, normal, and flat. These properties are local on the base, so the glued $X(\Gamma)$ has them as well. Global projectivity follows from the finite map (6.6b) to $\mathbf P^1_{B_\Gamma}$. Its geometric fibers have dimension one: this may be checked on an auxiliary fine cover, where the elliptic deformation parameter on the smooth locus and the one-parameter Tate charts at the boundary give pure dimension one.

We have constructed a projective coarse modular curve over $B_\Gamma$. At wild exceptional quotient points, projectivity says nothing by itself about the completed invariant ring. At primes outside $B_\Gamma$, no integral coarse model has yet been claimed. Projectivity is global; regularity and integral extension are local questions.

## 7. Cusps and their divisor

### 7.1 The boundary as a closed substack

Let

$$
\mathcal C(\Gamma)=
\overline{\mathcal M}(\Gamma)\setminus\mathcal M(\Gamma) \tag{7.1}
$$

first as the closed complement on underlying substacks; Section 7.3 gives it its canonical Cartier structure. The locus where the universal generalized elliptic curve is smooth is open, so the complement is closed. The level bound leaves only finitely many polygon sizes, and after a finite framing the level and automorphism data on a polygon form a finite scheme over the base. Hence the boundary stack is proper, flat, and quasi-finite over $B_\Gamma$: on a framed chart it is $t=0$ in $A[[t]]$, hence is $\operatorname{Spec}A$ with $A$ finite etale over the base. Its pullback to every fine cover is finite. It is important not to call the morphism $\mathcal C(\Gamma)\to B_\Gamma$ finite: a finite morphism of algebraic stacks is representable, whereas a cusp can retain nontrivial inertia. Its coarse cusp, constructed below, is finite over the base.

Geometrically, its connected pieces are classified by Tate level data modulo automorphisms. For $\Gamma_1(N)$ a cusp may be represented after finite extension by a pair of Tate parameters

$$
(q,u),\qquad u=\zeta_N^a q^{b/N}, \tag{7.2}
$$

with the component image generated by $b$ after reducing to the polygon selected by the orbit. Full level records a toric and a component vector; cyclic level forgets the generator and retains its orbit under $(\mathbf Z/N\mathbf Z)^\times$.

This description is used only after a finite cover that chooses roots and an orientation. The cusp itself is the descended orbit, so its residue field can be smaller than the field on which a displayed Tate generator exists.

### 7.2 Tate parameters and cusp widths

Choose a cusp and pass to a fine cover that fixes its component orientation, level basis, and invariant differential. There is a formal parameter $t$ and a Tate model with period

$$
q=t^w, \tag{7.3}
$$

where $w$ is the cusp width. The completed framed chart is

$$
\operatorname{Spf}A[[t]], \tag{7.4}
$$

and the boundary is $t=0$. Here $A$ is the finite coefficient ring needed for the root of unity and discrete level labels. Changing the framing acts through a finite group on $A[[t]]$.

The number $w$ is intrinsic. It is the ramification index of the map to the unlevelled Tate parameter, or equivalently the smallest positive translation in the parabolic stabilizer of the cusp. Algebraically it is characterized by (7.3) up to multiplication of $t$ by a unit. If $t'=ut+O(t^2)$ with $u\in A^\times$, then $(t')^w$ differs from $t^w$ by a unit, so the Cartier boundary and its multiplicity are unchanged.

One can recover $w$ without choosing an analytic uniformization. Travel once around the polygon and multiply the local smoothing parameters at its nodes. Contraction to the stable one-gon identifies that product with $q$ up to a unit. If translation identifies the relevant node parameters with $t$ and there are $w$ passages in the level orbit, their product is $t^w$. Thus cusp width is simultaneously a component count, a ramification index, and a Cartier-divisor multiplicity.

The coefficient ring $A$ is part of the cusp chart. A primitive root, component orientation, or generator may require a finite extension. Galois can change these labels while fixing the underlying cusp orbit. Passing from $A[[t]]$ to the invariant ring changes both residue field and uniformizer; the coarse cusp is not obtained merely by erasing the labels from the notation.

For prime cyclic level, the two charts from Book 110 give the basic check. At the multiplicative cusp,

$$
(E_q,\mu_p),\qquad q=q,
$$

while at the component cusp,

$$
(E_{t^p},\langle t\rangle),\qquad q=t^p. \tag{7.5}
$$

Thus the forgetful map has boundary order $1$ on the first chart and $p$ on the second.

### 7.3 The Cartier divisor theorem

**Theorem 7.1.** The boundary $\mathcal C(\Gamma)$ is a relative effective Cartier divisor on the compactified modular stack. Its equations on the framed Tate charts glue to a canonical global divisor.

**Proof.** On the framed chart $\operatorname{Spf}A[[t]]$, the ideal is $(t)$. Multiplication by $t$ is injective even if $A$ has nilpotents: if $t\sum a_nt^n=0$, comparison of coefficients gives every $a_n=0$. Hence $t$ is a non-zero-divisor and defines an effective Cartier divisor.

On the overlap of two cusp charts, both equations cut out the complement of the same dense smooth locus. Their ratio has neither zero nor pole: in the common total quotient ring each vanishes to order one along the framed boundary. Thus the ratio is a unit. The principal ideals agree and descend through the frame-change relation. Away from the boundary the ideal is the unit ideal, so the local Cartier ideals glue globally. $\square$

Write the resulting divisor as $\mathrm{Cusp}_{\Gamma}$. The pullback under a map of levels records cusp width. If $q=t^w$, then

$$
f^*\mathrm{Cusp}_{1}=w\,\mathrm{Cusp}_{\Gamma} \tag{7.6}
$$

on that branch. This is an equality of Cartier divisors, not merely of sets.

### 7.4 The cusp on the coarse curve

The quotient of the framed cusp locus, equivalently the scheme-theoretic image of the cusp stack in the coarse curve, is a finite closed subscheme

$$
C(\Gamma)\subset X(\Gamma). \tag{7.7}
$$

On a quotient chart $[\operatorname{Spec}B/G]$, its ideal downstairs is the contraction of the boundary ideal to $B^G$. Set-theoretically it is exactly the image of $t=0$. After strict henselization and completion at a tame geometric cusp, the stabilizer fixes the coefficient field, its effective image is cyclic of order $e$, and a linearized parameter has action $t\mapsto\zeta t$. On that completed chart one has

$$
B^G\simeq A[[t^e]],\qquad C(\Gamma)=(t^e). \tag{7.8}
$$

Thus the reduced coarse cusp is Cartier with uniformizer $u=t^e$. Pulling it back gives $e$ times the stack divisor on the fine chart.

In wild characteristic, invariants need not be exact and coarse formation need not commute with a nonflat base change. It is therefore unsafe to assert globally that the scheme-theoretic image of the stack Cartier divisor is Cartier with the same multiplicity. The canonical statements valid without tameness are: the cusp is finite, its reduced support is the boundary image, and its pullback to every fine Tate chart is $t=0$. Cartier and multiplicity statements on the coarse curve require the stated invariant-ring calculation.

## 8. Exceptional automorphisms

### 8.1 Generic and exceptional inertia

Over an algebraically closed field of characteristic different from $2$ and $3$, every elliptic curve has the involution $[-1]$. For generic $j$ this is the full automorphism group. At $j=1728$ it grows to a group of order $4$, and at $j=0$ to a group of order $6$. The coarse $j$-line identifies all objects with the same $j$ but records none of these groups.

Level intersects these automorphism groups. Full level $N\geq3$ with $N$ invertible kills them. A $\Gamma_1(N)$ point often kills them but not at all small levels or in bad characteristic. Every $\Gamma_0(N)$ subgroup is preserved by $[-1]$, so cyclic-level stacks generally retain at least the generic involution.

At a polygon, inversion reverses the component group and the toric coordinate. A component generator can rule it out, while a multiplicative Drinfeld generator that collapses to the identity in characteristic $p$ may not. Thus stabilizers must be computed on the finite-flat level divisor, not inferred from the number of visible geometric points.

### 8.2 Rigidification by the generic involution

Suppose $[-1]$ is a central subgroup of inertia throughout the moduli problem. Rigidification forms

$$
\overline{\mathcal M}(\Gamma)\mathbin{\!\sslash\!}\{\pm1\}. \tag{8.1}
$$

It leaves objects locally unchanged and quotients every isomorphism sheaf by the indicated involution. On a quotient chart $[Y/G]$ on which this central subgroup acts trivially on the parameter scheme, rigidification replaces $G$ by $G/\{\pm1\}$.

The phrase “acts trivially on the parameter scheme” is crucial. Generic inversion acts nontrivially on the universal elliptic curve but trivially on its $j$-deformation parameter. It is ineffective inertia for the base deformation. Rigidification removes this generic gerbe without changing the coarse curve.

After rigidification, the residual stabilizer in characteristic different from $2,3$ is trivial generically, of order $2$ above $j=1728$, and of order $3$ above $j=0$. These are the exceptional automorphism loci. For level problems, take the subgroup that also preserves the level; the residual order can decrease.

The Weierstrass equation displays why the generic involution is ineffective on the base. In characteristic different from $2$ and $3$, write

$$
E_{a,b}:y^2=x^3+ax+b,\qquad
\Delta=-16(4a^3+27b^2). \tag{8.1a}
$$

Changing variables by $x=u^2x'$ and $y=u^3y'$ sends $(a,b)$ to $(u^{-4}a,u^{-6}b)$. The scalar $u=-1$ changes neither coefficient, although it acts as inversion on the elliptic curve. Thus $[-1]$ is visible on the universal object and invisible on the two coefficient parameters.

At $j=1728$ one has $b=0$ and $a\neq0$. After using scaling to hold $a$ fixed, $b$ is a transverse deformation parameter. The extra order-four automorphism acts on $b$ through a character whose quotient by $\{\pm1\}$ has order two. At $j=0$ one has $a=0$ and $b\neq0$; the transverse parameter $a$ carries a residual character of order three. This coefficient computation predicts the invariant squares and cubes in the coarse completed rings below.

### 8.3 Completed local rings in the tame case

Let $x$ be a geometric point of a fine cover above an exceptional point, let $H$ be its stabilizer after removing ineffective inertia, and take the completed local ring in the geometric fiber. Write

$$
R_x\simeq k[[t]] \tag{8.2}
$$

be the completed local ring of the fine curve. Assume $|H|$ is invertible in $k$. Every finite-order automorphism of $k[[t]]$ is linearizable. Indeed, if $h(t)=a_ht+O(t^2)$, averaging

$$
u=\frac1{|H|}\sum_{h\in H}a_h^{-1}h(t) \tag{8.3}
$$

gives $u=t+O(t^2)$ and $h(u)=a_hu$. Thus $u$ is another uniformizer and the action is through a character $H\to k^\times$.

If the effective character has image of order $e$, then

$$
k[[u]]^H=k[[u^e]]. \tag{8.4}
$$

To prove this, write a series $f=\sum c_nu^n$. Invariance under a generator with eigenvalue $\zeta$ forces $c_n=0$ unless $e\mid n$. Conversely every series in $u^e$ is invariant. Hence the coarse completed local ring is regular, with parameter $u^e$, while the stack retains the stabilizer and the root parameter $u$.

This calculation explains the exceptional stack/coarse comparison. The coarse curve can be smooth even though the coarse map has nontrivial stabilizer behavior. The stack has fractional local degrees and stabilizer-weighted divisors; the coarse curve has an ordinary DVR whose parameter is the invariant power.

For the rigidified unlevelled stack in characteristic different from $6$, the preceding Weierstrass calculation gives, on geometric fibers,

$$
\widehat{\mathcal O}_{X(1),1728}\simeq k[[u^2]],
\qquad
\widehat{\mathcal O}_{X(1),0}\simeq k[[v^3]], \tag{8.5}
$$

where $u$ and $v$ are stack parameters after a finite framing. The symbols $u^2$ and $v^3$ are themselves uniformizers downstairs; the invariant rings are regular. The exponents do not mean that the coarse curve has a singularity. They measure the difference between a stack parameter and a coarse parameter.

For a level stack, first intersect the exceptional automorphism group with the subgroup fixing the chosen level. If the intersection is trivial, the fine and coarse completed rings coincide. If it has effective order $e$, the same $e$th-power calculation applies. This is why exceptional ramification depends on the level problem, not only on the value of $j$.

### 8.4 Characteristics two and three

The tame proof uses division by $|H|$. In characteristics $2$ and $3$, the exceptional automorphism group can be non-linearly reductive or nonetale, and the averaging coordinate does not exist. Three conclusions must be separated.

First, the coarse scheme still exists by the finite quotient construction. Second, flat base change of invariants remains valid, but arbitrary base change can fail. Third, regularity of the invariant ring cannot be inferred from (8.4); it requires a direct calculation of the actual deformation action.

There is an additional subtlety: even an etale stabilizer of order divisible by the characteristic is not linearly reductive, so counting its geometric automorphisms does not justify averaging or exactness of invariants. The finite diagonal records the whole stabilizer and its deformation action, and the quotient presentation must retain both.

This is the exact boundary of the current theorem. Exceptional characteristics are included in the proper stack and coarse-scheme constructions, but their detailed regularity and special-fiber equations are not smuggled in from the tame calculation.

## 9. Stack and coarse geometry compared

### 9.1 Points, functions, and residue fields

Let $\pi:\mathcal X\to X$ be a compactified modular coarse map. A geometric point of $X$ is an isomorphism class, while a geometric point of $\mathcal X$ is an object together with its automorphism group. Thus the map on geometric isomorphism classes is bijective, but the fiber category need not be a point.

Functions behave better. On a finite chart $[Y/G]$, one has

$$
\mathcal O_X=(q_*\mathcal O_Y)^G. \tag{9.1}
$$

Hence a function on the stack is precisely an invariant function on a fine cover, and it descends uniquely to the coarse curve. This is the local algebra behind the categorical universal property.

Residue fields record field-of-moduli effects. A cusp may admit a Tate generator only after adjoining roots of unity or a root of $q$, while its orbit under the change-of-level group can be defined over a smaller field. The coarse residue field is the invariant field of the orbit. It need not be a field over which a universal representative exists; a field of moduli need not be a field of definition when stabilizers obstruct descent.

### 9.2 Base change and the tame boundary

For a flat morphism $T\to S$, finite-group invariants commute with scalar extension:

$$
A^G\otimes_ST\simeq(A\otimes_ST)^G. \tag{9.2}
$$

This follows because invariants are an equalizer and flat tensor product preserves equalizers of modules. Therefore formation of the coarse modular curve commutes with flat base change.

If $G$ is linearly reductive, invariants are a direct summand. Then (9.2) holds for arbitrary base change. A constant finite group of order invertible on the base is linearly reductive by the Reynolds operator

$$
a\longmapsto\frac1{|G|}\sum_{g\in G}ga. \tag{9.3}
$$

This is the tame case.

Without linear reductivity, tensor product can destroy the kernel defining invariants. Consequently the coarse space of the base-changed stack can differ from the base change of the original coarse space. The stack itself commutes with base change because its moduli problem does; the loss occurs only after invariants are taken.

### 9.3 Line bundles and stabilizer characters

Let $\mathcal L$ be a line bundle on $\mathcal X$. If $\mathcal L\simeq\pi^*L$ for a line bundle $L$ on $X$, every stabilizer acts trivially on the fiber of $\mathcal L$: it acts over the identity of the coarse point and hence trivially on a pulled-back one-dimensional vector space.

In the tame case the converse holds. On $[\operatorname{Spec}A/G]$, let $M$ be the equivariant rank-one projective module corresponding to $\mathcal L$. If every stabilizer acts trivially on fibers, the adjunction

$$
A\otimes_{A^G}M^G\longrightarrow M \tag{9.4}
$$

is an isomorphism after checking on geometric fibers. Exactness of invariants and Nakayama's lemma then make it an isomorphism locally. The invariant modules glue to a line bundle downstairs.

Thus:

**Proposition 9.1.** On a tame compactified modular stack, a line bundle descends to the coarse curve if and only if every geometric stabilizer acts trivially on its fiber.

If the stabilizer characters have exponent dividing $m$, then $\mathcal L^m$ descends. This is why a sufficiently divisible power of a natural modular line often exists on the coarse curve even when the line itself does not.

### 9.4 Dualizing and Hodge lines

The Hodge line on the stack is

$$
\omega=e^*\Omega^1_{E^{\mathrm{sm}}/\mathcal X}. \tag{9.5}
$$

It exists because the universal generalized elliptic curve exists on the stack. An automorphism acts on the invariant differential and hence on the fiber of $\omega$. At an exceptional elliptic curve this character can be nontrivial, so $\omega$ need not descend to the coarse curve.

The cusp parameter relates $\omega$ to the dualizing geometry. On a Tate chart the invariant differential $du/u$ trivializes $\omega$, while $dt$ measures the cotangent direction to the base. A change of framing acts on both. The stack-theoretic Kodaira--Spencer relation identifies the logarithmic cotangent line with a fixed tensor power of $\omega$ on the good deformation locus; the precise global modular-form theory is developed later, but the descent criterion already predicts that a suitable power is needed on the coarse curve.

The dualizing sheaf of the coarse curve is a different object. At a tame quotient $u=t^e$, one has

$$
du=e t^{e-1}dt. \tag{9.6}
$$

The factor $t^{e-1}$ records the exceptional stabilizer contribution. Ignoring it would identify stack differentials with coarse differentials and give incorrect divisor degrees. The comparison is an invariant-ring calculation, not an equality of universal bundles.

## 10. Universal cyclic isogenies

### 10.1 Construction on the moduli stack

On $\overline{\mathcal M}_0(N)$ there is a universal pair $(\mathcal E,\mathcal C)$ in the stack-theoretic sense. Book 110's quotient theorem gives a generalized elliptic curve $\mathcal E/\mathcal C$ and a finite morphism

$$
\Phi:\mathcal E\longrightarrow\mathcal E/\mathcal C \tag{10.1}
$$

whose restriction to the smooth locus is the fppf quotient. It has generic degree $N$ and commutes with arbitrary base change.

The degree qualification matters at nodes. If the kernel has multiplicative rank $a$, the completed map can be

$$
k[[X,Y]]/(XY)\longrightarrow k[[x,y]]/(xy),\qquad
X\mapsto x^a,\quad Y\mapsto y^a. \tag{10.2}
$$

The fiber over the node has length $2a-1$, so the map need not be finite flat there. Its degree is the degree on the dense smooth locus, and no stronger flatness is asserted.

The quotient is unique because two extensions agree on the schematically dense smooth locus and the target is separated. This uniqueness is what makes (10.1) a universal construction rather than a chartwise choice.

### 10.2 Descent from a fine cover

Let $Y_M\to\overline{\mathcal M}_0(N)$ be a normalized fine auxiliary-level cover. On $Y_M$ there is an honest universal isogeny

$$
\Phi_{Y_M}:E_{Y_M}\longrightarrow E_{Y_M}/C_{Y_M}. \tag{10.3}
$$

For $g\in G_M$, the deck transformation changes the auxiliary branch but not the underlying cyclic subgroup. There are canonical isomorphisms

$$
g^*E_{Y_M}\simeq E_{Y_M},\qquad
g^*(E_{Y_M}/C_{Y_M})\simeq E_{Y_M}/C_{Y_M}. \tag{10.4}
$$

under which $g^*\Phi_{Y_M}$ equals $\Phi_{Y_M}$. These isomorphisms come functorially from changing the auxiliary basis and from the universal property of the quotient by $C_{Y_M}$, so they satisfy the cocycle condition over arbitrary, including nonreduced, test schemes. Thus the source, target, and morphism carry descent data along the action groupoid.

Effective descent produces (10.1) on the quotient stack. This is the precise descent of the universal isogeny: it descends from the auxiliary fine scheme to the original moduli stack, independently of the auxiliary level.

### 10.3 What descends to a coarse curve

The universal isogeny generally does **not** descend as a morphism between two families of generalized elliptic curves over $X_0(N)$. The obstruction is inertia. At a point $(E,C)$, inversion preserves $C$ and acts nontrivially on both $E$ and $E/C$. A family pulled back from the coarse curve would have trivial stabilizer action, contradicting this nontrivial action.

Equivalently, inspect the descent cocycle on the fine cover. The two pullbacks of $E_{Y_M}$ to $Y_M\times_{X_0(N)}Y_M$ are isomorphic. On the relation component indexed by inversion, that isomorphism is $[-1]$. Descent to a scheme would force an element fixing the base point to act as the identity on the descended fiber. Since $[-1]$ is not the identity morphism of the curve, this descent datum belongs to the quotient stack, not to the scheme quotient.

Rigidifying the moduli stack by $\{\pm1\}$ does not automatically solve the problem. Rigidification identifies object isomorphisms that differ by inversion; it does not turn inversion into the identity morphism of the underlying elliptic curve. The universal curve still fails to be a family on the rigidified coarse base unless it is replaced by an object on which the central involution acts trivially.

What always descends is the induced morphism of moduli:

$$
\pi_1,\pi_2:\overline{\mathcal M}_0(N)
\longrightarrow\overline{\mathcal M}_{1,1}. \tag{10.5}
$$

Composing with the coarse $j$-line gives maps to a scheme, so the coarse universal property yields unique maps

$$
\bar\pi_1,\bar\pi_2:X_0(N)\longrightarrow X(1). \tag{10.6}
$$

On any open where stabilizers are trivial, the universal curves and isogeny do descend, and (10.6) is induced by them. Globally one should speak of the universal isogeny on the stack and the source/target maps on the coarse curve.

This distinction is not a defect. The coarse curve was designed to classify orbits, not to trivialize their automorphisms.

### 10.4 Duality and the two cusp formulas

On the smooth locus, the dual isogeny satisfies

$$
\widehat\Phi\Phi=[N],\qquad
\Phi\widehat\Phi=[N]. \tag{10.7}
$$

Whenever the source and target polygonal models are chosen so that both kernels lie in the smooth loci, density extends these identities across the boundary.

At prime level $p$, the multiplicative cusp has

$$
E_q/\mu_p\simeq E_{q^p}, \tag{10.8}
$$

induced by $u\mapsto u^p$. The component cusp has

$$
E_{t^p}/\langle t\rangle\simeq E_t, \tag{10.9}
$$

induced by the identity on $\mathbf G_m$ and enlargement of the period lattice. Duality exchanges these directions. It may also require replacing a one-gon by a $p$-gon so that the dual kernel remains in the smooth locus.

Equations (10.8) and (10.9) verify the descent maps on completed cusp charts and determine their boundary multiplicities.

## 11. Degeneracy maps and coarse correspondences

### 11.1 Forgetting and quotienting

The two degeneracy maps on cyclic level are the source and target operations already defined:

$$
\pi_1(E,C)=\operatorname{st}(E),\qquad
\pi_2(E,C)=\operatorname{st}(E/C). \tag{11.1}
$$

For point level, forgetting the generator but retaining its subgroup gives

$$
\overline{\mathcal M}_1(N)\longrightarrow
\overline{\mathcal M}_0(N). \tag{11.2}
$$

The group $(\mathbf Z/N\mathbf Z)^\times$ acts by $P\mapsto aP$, and the fppf quotient is the cyclic-subgroup problem because local Drinfeld generators of the same subgroup differ by a unit.

For full level, retaining a primitive linear combination $aP+bQ$ may make its divisor nonample on the original $N$-gon. Contracting to the components it sees produces the correct point-level target. Functoriality of contraction makes this a morphism of stacks.

### 11.2 Extension across the boundary

The main issue is not defining the maps on smooth elliptic curves but showing that they do not become rational at cusps. Quotient and contraction solve this.

For prime cyclic level, the completed formulas are

$$
\begin{array}{c|cc}
&\pi_1^*q&\pi_2^*q\\ \hline
(E_q,\mu_p)&q&q^p\\
(E_{t^p},\langle t\rangle)&t^p&t.
\end{array} \tag{11.3}
$$

Each entry lies in the completed local ring of the source chart. Hence both maps extend regularly across the boundary. Since the construction commutes with base change and is unique on the dense smooth locus, the formal formulas glue to global stack morphisms.

For composite level the same argument uses the toric rank $a$ and component-image order $b$ with $ab=N$. Quotienting changes the toric coordinate by degree $a$ and the component period by index $b$. The exact exponent depends on the cusp type, but it is determined by the subgroup extension

$$
0\to C\cap E^{\mathrm{sm},0}\to C\to\operatorname{im}(C\to\Phi_E)\to0. \tag{11.4}
$$

### 11.3 Passage to coarse curves

Every morphism of compactified modular stacks induces a morphism of their coarse curves after composing with the target coarse map. Indeed, if $F:\mathcal X\to\mathcal Y$, then

$$
\mathcal X\xrightarrow{F}\mathcal Y\to Y
$$

is a map to an algebraic space, so it factors uniquely through $X$. Thus all forgetful, quotient, and diamond-orbit maps descend.

Compatibility is automatic. If two composites of stack maps agree, their induced maps of coarse spaces agree by uniqueness. In particular the two degeneracy maps and diamond actions satisfy on coarse curves all relations already proved on the stack.

Finiteness can be checked on compatible fine covers. A change-of-level map is representable and has finite fibers because an automorphism preserving the larger level injects into the automorphism group preserving the retained level, and only finitely many larger level structures occur on a fixed generalized curve. It is proper: its graph is closed because the target has finite separated diagonal, while the source is proper over the base. Thus it is proper and quasi-finite, hence finite. Taking finite quotients on compatible covers shows that the standard induced maps between compactified coarse modular curves are finite.

### 11.4 Graphs and finite correspondences

The pair $(\bar\pi_1,\bar\pi_2)$ gives a proper map

$$
X_0(N)\longrightarrow X(1)\times X(1). \tag{11.5}
$$

Its scheme-theoretic image is the cyclic-isogeny correspondence. On the smooth locus it classifies pairs of elliptic curves linked by a cyclic degree-$N$ isogeny. At the boundary its branches are determined by the Tate formulas.

If a target coarse curve is not normal, it can be safer to retain the normalization of the graph image. Book 11's normalization mapping property then gives finite maps to both factors whenever the coordinate extensions are finite. The normalization remembers branches that a singular coarse image might identify.

The correspondence descends even when the universal isogeny does not. It records source and target isomorphism classes, which are coarse data; it does not attempt to choose a representative curve over every coarse point.

## 12. Normalization and changes of level

### 12.1 Finite maps between compactified stacks

Let $\Gamma'$ denote a finer finite-index level type than $\Gamma$, with the usual contraction inserted after forgetting level. The induced map

$$
\overline{\mathcal M}(\Gamma')\longrightarrow
\overline{\mathcal M}(\Gamma) \tag{12.1}
$$

is representable, proper, and quasi-finite. Representability follows from injectivity on level-preserving automorphisms together with the level-parameter schemes of Book 110. Properness follows from the closed-graph argument just used, or directly from the valuative extension property. Quasi-finiteness follows from finite level choices over a fixed curve together with uniqueness of the contraction selected by the retained divisor. Hence it is finite.

At a cusp, finiteness is visible from $q=t^w$: the inclusion of complete local rings $A[[q]]\to A'[[t]]$ is finite when $A'/A$ is finite and $t$ satisfies $T^w-q=0$. This calculation also gives the ramification index along the cusp divisor.

The map need not be etale. It ramifies at cusps through $w$, at exceptional automorphism points through stabilizers, and in residue characteristic dividing the level through nonetale torsion.

### 12.2 Normality of finite group quotients

**Lemma 12.1.** Let $A$ be a normal domain and let a finite group $G$ act on $A$. Then $A^G$ is normal.

**Proof.** Its fraction field is $\operatorname{Frac}(A)^G$. Let $x$ in that field be integral over $A^G$. Since $A$ is integral over $A^G$, transitivity makes $x$ integral over $A$. Normality gives $x\in A$. Being in the invariant fraction field, it is fixed by $G$, so $x\in A^G$. $\square$

Consequently a quotient of a normal fine modular curve by a constant finite change-of-level group is normal. The hypothesis belongs on the fine cover. A quotient construction does not repair nonnormality already present upstairs.

For reduced schemes with several components, apply the lemma componentwise after accounting for the permutation action. The quotient can identify components, but its normalization is obtained from invariant subrings in the product of their function fields.

### 12.3 Normalize after base change

Normality need not survive arbitrary base change. If $X(\Gamma)$ is normal over a Dedekind base and $S'\to S$ is ramified, the base change can acquire singular or nonnormal local rings. The safe construction is

$$
X(\Gamma)_{S'}^{\mathrm{new}}
=\operatorname{Norm}\bigl((X(\Gamma)\times_SS')_{\mathrm{red}}\bigr) \tag{12.2}
$$

in the generic function algebra selected by the level problem.

Book 11 proves that normalization is finite over the excellent arithmetic bases in use. It also proves the universal property that makes maps from normal sources factor uniquely through (12.2). Thus level-change and degeneracy maps extend to the normalized base changes whenever their generic maps land in the chosen function fields.

Coarse formation and base change must also be ordered carefully. In the tame case they commute. In the wild case one should base-change the stack, form its coarse space, and compare that result with the normalization of the old coarse base change. Equality requires an invariant-ring calculation; it is not formal.

### 12.4 Limits of the present construction

The construction has produced proper compactified stacks, projective fine covers, projective coarse curves, cusp divisors, and extended maps. It has not proved that every integral coarse curve is regular or smooth away from level, nor has it described the special fiber at a prime dividing the level as a union of regular components.

Those assertions require completed local deformation rings at bad-level points, normalization of their branches, and resolution or semistable analysis. The tame quotient calculation of Chapter 8 cannot replace that work in wild characteristic. Likewise, the generic degree of a boundary isogeny does not imply finite flatness at its nodes.

This boundary is logically important. Properness is a valuative statement, coarse representability is an invariant-theory statement, and regularity is a local commutative-algebra statement. Proving the first two does not silently prove the third.

## 13. The compactified modular-curve package

### 13.1 The main construction theorem

**Theorem 13.1 (compactified stack and coarse curve).** Let $\Gamma$ be one of the full, point, or cyclic level types defined by ample Drinfeld data, and work over the good-level base $B_\Gamma$ specified in Section 1.2. Then:

1. $\overline{\mathcal M}(\Gamma)$ is a smooth, hence flat and normal, proper algebraic stack of pure relative dimension one and finite presentation, with finite separated diagonal;
2. its open dense substack $\mathcal M(\Gamma)$ classifies smooth elliptic curves with the same level;
3. Zariski-locally on $B_\Gamma$, after choosing an auxiliary full level $M\geq3$ invertible there and its boundary decontraction, there is a projective fine moduli scheme $Y_M$ finite and surjective over the restricted stack; these fine curves form one projective cover after a faithfully flat disjoint-union base change, and whenever one such $M$ is invertible on all of $B_\Gamma$, the cover is global over $B_\Gamma$;
4. on every such open, for the finite change-of-level group $G_M$,

   $$
   \overline{\mathcal M}(\Gamma)\simeq[Y_M/G_M],
   \qquad X(\Gamma)=Y_M/G_M;
   $$

5. the local quotients glue uniquely to a normal flat projective coarse modular curve $X(\Gamma)$ of pure relative dimension one, independent of every auxiliary choice;
6. the stack boundary is a flat proper quasi-finite relative effective Cartier divisor, locally cut out by a Tate parameter; its pullback to a fine cover and its coarse image are finite over the base, and the coarse image is Cartier with the computed invariant parameter on tame completed charts;
7. universal cyclic isogenies descend from fine covers to the moduli stack, while their source and target maps always descend to coarse curves;
8. at tame exceptional automorphism points, the completed local ring on the geometric coarse fiber is the invariant subring of the framed stack chart, explicitly $k[[t^e]]$ when the effective stabilizer acts by $t\mapsto\zeta_et$.

**Proof.** Algebraicity, smoothness, dimension, normality, and finite diagonal are Theorem 3.1. Properness is Theorem 4.1. The local fine projective covers are Theorem 5.2 applied wherever the chosen $M$ is invertible. The quotient-stack presentation, faithfully flat cover, gluing, and global projectivity are Theorem 6.1 and Section 6.4. The boundary assertions are Theorem 7.1 and Section 7.4. Chapters 10 and 11 prove isogeny and degeneracy descent. The invariant complete-local calculation is Section 8.3. Every item retains the hypotheses stated there. $\square$

### 13.2 A hypothesis ledger

The following distinctions summarize where the arguments change.

| Hypothesis | Consequence | Not implied |
|---|---|---|
| ample level divisor | bounded polygon size and projective parameter control | trivial stabilizers |
| full auxiliary level $M\geq3$, $M$ invertible | fine scheme and universal family | a universal family on the coarse quotient |
| proper stack with finite diagonal | valuative compactification and separated isomorphisms | regular coarse local rings |
| finite group quotient of a projective scheme | projective coarse scheme | compatibility with every base change |
| linearly reductive stabilizers | exact invariants and arbitrary coarse base change | absence of exceptional stack structure |
| trivial stabilizer character on a line | tame descent of that line | descent of the universal curve |
| normal fine cover | normal constant-group quotient | stability under ramified base change |
| generic degree $N$ boundary quotient | degree of the isogeny on the dense smooth locus | finite flatness at nodes |

This ledger is part of the theorem package: removing one hypothesis changes the conclusion, rather than merely weakening a proof technique.

### 13.3 Worked comparisons

**The unlevelled curve.** Over a base where $2$ and $3$ are invertible, the stable stack retains generic $\{\pm1\}$ inertia. Its coarse curve is the projective $j$-line. Rigidification removes the generic involution, leaving residual stabilizer of order $2$ at $j=1728$ and order $3$ at $j=0$. The coarse coordinate is an invariant power of a stack deformation coordinate at these points.

**Full level.** If $N\geq3$ is invertible and the pairing datum is fixed, full level kills inertia. No auxiliary quotient is needed: the compactified stack is already a fine projective scheme. Its universal generalized elliptic curve exists globally. At a cusp the singular fiber is an $N$-gon and a framed completed chart has $q=t^N$ relative to the unlevelled one-gon parameter.

**Cyclic prime level.** The stack $\overline{\mathcal M}_0(p)$ retains inversion. It has two cusp types. At $(E_q,\mu_p)$ the quotient degeneracy map sends $q$ to $q^p$. At $(E_{t^p},\langle t\rangle)$ it sends the period to $t$, while the forgetful map has $q=t^p$. These two branches descend to the coarse curve, although the universal degree-$p$ isogeny generally remains only on the stack.

**Integral continuation.** In characteristic dividing the level, geometric torsion points do not determine the finite group schemes. Drinfeld divisors specify the correct candidate closure, but the proper normal integral stack and its local rings are not conclusions of Theorem 13.1. In characteristic dividing only a stabilizer order, which can occur on $B_\Gamma$, the compactified stack and coarse curve do exist, while tame base-change and line-bundle descent statements are withheld unless linear reductivity is proved.

### 13.4 Dependency closure

No compactification conclusion has been imported from a later book. The projective parameter and finite quotient arguments are exactly the results of Book 8. The normalization statements and ramified-base-change warning are exactly the results of Book 11. The quotient-stack, rigidification, finite auxiliary decontraction, coarse universal property, and tame descent criteria are exactly the results of Book 13. The polygon arithmetic, Drinfeld level, contraction, boundary quotient, Tate deformation, and cusp formulas are exactly the results of Book 110.

The only ordinary background beyond those books is the valuative criterion for proper algebraic stacks and the elementary algebra of generalized Weierstrass coordinate changes. Lemma 4.0 proves potential semistability from that coefficient algebra and the Tate inverse series, including the weighted reconstruction step in residue characteristics $2$ and $3$. The finite-group invariant calculations needed at issue were also proved explicitly here. No regularity or special-fiber theorem from a later stage has been used.

## 14. Conclusion

### 14.1 The completed passage from objects to curves

The compactification begins with one geometric fact: a degenerating elliptic curve retains a group on its smooth locus and records valuation classes in a polygon. Drinfeld divisors allow level to survive collisions, and ampleness forces that level to see every component. These conditions bound the boundary and turn it into a finite-presentation moduli problem.

Projective embeddings then provide algebraic charts. The valuative analysis fills every punctured family by a good or Tate boundary object and proves properness. Auxiliary full level removes automorphisms and gives projective fine schemes locally on the arithmetic base, and globally whenever one auxiliary order is invertible everywhere. Finite change-of-level quotients restore the original moduli problem and glue to its projective coarse curve.

Thus the route is

$$
\text{generalized objects}
\longrightarrow\text{proper moduli stack}
\longleftarrow\text{fine projective cover}
\longrightarrow\text{coarse projective curve}. \tag{14.1}
$$

Every arrow has a different meaning: classification with symmetry, rigidification by extra data, and invariant-theoretic forgetting.

### 14.2 What the coarse curve remembers

The coarse curve remembers geometric isomorphism classes, invariant functions, maps to other coarse spaces, cusp orbits, and the source and target of universal isogenies. It remembers cusp widths through invariant local parameters and exceptional automorphisms through quotient exponents in completed local rings.

It does not generally remember a universal elliptic curve, a universal cyclic isogeny as a family, or a line bundle on which inertia acts nontrivially. Those objects live naturally on the stack. A fine cover carries them honestly but depends on auxiliary level. The stack is the unique level at which they are both canonical and independent of that auxiliary choice.

### 14.3 Final synthesis

Compactified modular geometry is not the act of adjoining missing points to an affine curve. It is the controlled passage from degenerating elliptic families to a proper groupoid, from that groupoid to rigid projective coordinates, and from those coordinates to invariant coarse geometry. The cusp divisor is locally one Tate equation; its width records how level winds around the polygon. The universal quotient isogeny extends because quotient and contraction are intrinsic on generalized elliptic curves. Exceptional automorphisms remain visible as inertia and become invariant-power parameters only after passage to the coarse curve.

The completed package is therefore precise and reusable: proper compactified modular stacks with finite diagonal, projective fine rigidified covers, projective coarse modular curves, canonical cusp divisors, descended source and target maps, and exact stack/coarse comparison at tame exceptional loci, together with explicit warnings at wild loci and after ramified base change. This is the geometric foundation on which integral local models, modular forms, and modular Jacobians can be built without losing either the boundary or its symmetries.
