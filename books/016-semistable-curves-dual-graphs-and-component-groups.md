# Semistable Curves, Dual Graphs, and Component Groups

## Contents

1. [Degeneration remembered as a graph](#1-degeneration-remembered-as-a-graph)
   - [The three layers of a special fiber](#11-the-three-layers-of-a-special-fiber)
   - [Standing conventions](#12-standing-conventions)
   - [A first degeneration](#13-a-first-degeneration)
2. [Nodes and their relative local models](#2-nodes-and-their-relative-local-models)
   - [The geometric node](#21-the-geometric-node)
   - [Smoothing parameters and thickness](#22-smoothing-parameters-and-thickness)
   - [Regular and nonregular total spaces](#23-regular-and-nonregular-total-spaces)
   - [Split and nonsplit nodes](#24-split-and-nonsplit-nodes)
3. [Semistable and stable families](#3-semistable-and-stable-families)
   - [Fiberwise definitions and relative hypotheses](#31-fiberwise-definitions-and-relative-hypotheses)
   - [Stability from the dualizing line](#32-stability-from-the-dualizing-line)
   - [Contraction and uniqueness](#33-contraction-and-uniqueness)
4. [Normalization and the conductor](#4-normalization-and-the-conductor)
   - [Separating branches](#41-separating-branches)
   - [The conductor square](#42-the-conductor-square)
   - [Functions, units, and line bundles](#43-functions-units-and-line-bundles)
   - [Differentials and arithmetic genus](#44-differentials-and-arithmetic-genus)
5. [Dual graphs, genera, and descent data](#5-dual-graphs-genera-and-descent-data)
   - [The geometric dual graph](#51-the-geometric-dual-graph)
   - [Orientations and chain groups](#52-orientations-and-chain-groups)
   - [Thicknesses, residue degrees, and Galois action](#53-thicknesses-residue-degrees-and-galois-action)
6. [Divisors and Laplacians on graphs](#6-divisors-and-laplacians-on-graphs)
   - [Multidegrees as vertex divisors](#61-multidegrees-as-vertex-divisors)
   - [Chip-firing and the Laplacian](#62-chip-firing-and-the-laplacian)
   - [Reduced Laplacians and spanning trees](#63-reduced-laplacians-and-spanning-trees)
   - [Examples and warnings](#64-examples-and-warnings)
7. [Cycle lattices and weighted graph Jacobians](#7-cycle-lattices-and-weighted-graph-jacobians)
   - [Homology and the edge-length pairing](#71-homology-and-the-edge-length-pairing)
   - [The discriminant group](#72-the-discriminant-group)
   - [Comparison with subdivision](#73-comparison-with-subdivision)
   - [Exact computations](#74-exact-computations)
   - [Discriminant pairing and weighted potentials](#75-discriminant-pairing-and-weighted-potentials)
8. [Generalized Jacobians of nodal curves](#8-generalized-jacobians-of-nodal-curves)
   - [Gluing line bundles across nodes](#81-gluing-line-bundles-across-nodes)
   - [The torus--abelian exact sequence](#82-the-torus--abelian-exact-sequence)
   - [Characters, loops, and nonsplit tori](#83-characters-loops-and-nonsplit-tori)
9. [Relative Picard geometry over a valuation ring](#9-relative-picard-geometry-over-a-valuation-ring)
   - [The degree-zero functor and its defect](#91-the-degree-zero-functor-and-its-defect)
   - [Vertical divisors and nonseparatedness](#92-vertical-divisors-and-nonseparatedness)
   - [The separated quotient and its identity component](#93-the-separated-quotient-and-its-identity-component)
   - [The valuative meaning of separation](#94-the-valuative-meaning-of-separation)
10. [Specialization of divisor classes](#10-specialization-of-divisor-classes)
    - [From horizontal divisors to multidegrees](#101-from-horizontal-divisors-to-multidegrees)
    - [Vertical correction and the component class](#102-vertical-correction-and-the-component-class)
    - [Specialization formulas](#103-specialization-formulas)
11. [Monodromy pairings](#11-monodromy-pairings)
    - [Why characters and cocharacters differ](#111-why-characters-and-cocharacters-differ)
    - [The local contribution of a node](#112-the-local-contribution-of-a-node)
    - [Intersection theory recovers the pairing](#113-intersection-theory-recovers-the-pairing)
12. [Component groups and the graph theorem](#12-component-groups-and-the-graph-theorem)
    - [The component group](#121-the-component-group)
    - [The graph description](#122-the-graph-description)
    - [Consequences and counterexamples](#123-consequences-and-counterexamples)
    - [Four model calculations](#124-four-model-calculations)
13. [Base change, resolution, and saturation](#13-base-change-resolution-and-saturation)
    - [Ramified base change](#131-ramified-base-change)
    - [Subdivision and stabilization](#132-subdivision-and-stabilization)
    - [Descent and residue extensions](#133-descent-and-residue-extensions)
    - [Saturation is arithmetic data](#134-saturation-is-arithmetic-data)
14. [Finite maps and correspondences](#14-finite-maps-and-correspondences)
    - [Maps of components and harmonicity](#141-maps-of-components-and-harmonicity)
    - [Pullback, norm, and adjunction](#142-pullback-norm-and-adjunction)
    - [Correspondences and component groups](#143-correspondences-and-component-groups)
15. [A calculation package for arithmetic curves](#15-a-calculation-package-for-arithmetic-curves)
    - [The regular split algorithm](#151-the-regular-split-algorithm)
    - [The weighted and nonsplit algorithm](#152-the-weighted-and-nonsplit-algorithm)
    - [Reusable formulas](#153-reusable-formulas)
    - [Conclusion](#154-conclusion)

## 1. Degeneration remembered as a graph

### 1.1 The three layers of a special fiber

A smooth curve can acquire singularities when reduced modulo a prime. At first this appears to destroy information: one smooth object is replaced by several components meeting at singular points. Semistable reduction is useful because the destruction is controlled. Every singularity is a node, every node has two branches, and the incidence pattern is a finite graph. The graph does not replace the components. It records how they are attached.

Three layers must be kept simultaneously. The normalized components retain ordinary curve theory and their Jacobians. The dual graph retains the new cycles created by gluing. The local equation at each node retains an integer thickness measuring how strongly the branches collide in the family. Forgetting any layer gives false conclusions. Two special fibers can have isomorphic reduced curves but different thicknesses and hence different component groups. Two curves can have the same graph but components of different genera and hence different identity components. A nonsplit node can have the same geometric graph as a split node but descend to a different torus.

The main theme is that line bundles translate these three layers into a group-theoretic structure:

$$
\begin{array}{c}
\text{Jacobians of normalized components}\\
\text{cycles of the dual graph}\\
\text{edge thicknesses}
\end{array}
\quad\rightsquigarrow\quad
\begin{array}{c}
\text{abelian part of the identity component}\\
\text{toric character lattice}\\
\text{monodromy pairing and component group}.
\end{array}
$$

The earlier theories of divisors, normalization, regular models, blowups, intersection pairings, descent, and coherent cohomology supply the geometric foundation. The reducible Picard construction needed here is proved below rather than inferred from the earlier smooth-curve case. These ingredients are then assembled into a numerical and functorial account of semistable degeneration.

### 1.2 Standing conventions

Unless a broader base is explicitly stated, $R$ is a henselian discrete valuation ring with fraction field $K$, uniformizer $\pi$, residue field $k$, and normalized valuation $v(\pi)=1$. We write $\bar k$ for a separable closure. A curve over $R$ is proper, flat, and finitely presented of relative dimension one, with geometrically connected fibers. Its generic fiber is denoted $C$ and its special fiber $X$.

Statements about the geometric dual graph are made after extension to $\bar k$. This convention handles nonrational components and nonsplit nodes honestly. The group $G_k=\operatorname{Gal}(\bar k/k)$ acts on vertices, unoriented edges, and oriented branches. A formula over $k$ is obtained by descent, not by pretending that every node is rational.

A graph may have multiple edges and loops. Each unoriented edge $e$ has two orientations $e$ and $\bar e$, with initial and terminal vertices $o(e)$ and $t(e)$. A loop has the same initial and terminal vertex but still has two branches and can contribute a cycle. Graphs are finite and connected unless stated otherwise.

For a model whose completed local equation at a node is $xy=u\pi^{n_e}$, in the sense made precise in §2.2, the positive integer $n_e$ is its thickness. Units do not change it. When the total space is regular, every geometric node has thickness one. Weighted formulas are needed precisely because stable or contracted models need not have regular total space.

### 1.3 A first degeneration

Consider two smooth proper curves $Y_1$ and $Y_2$ over $k$, glued transversely at $r$ pairs of rational points. The dual graph has two vertices and $r$ parallel edges:

```text
          e1
       +------+
       |      |
   v1  +------+
       |  e2  |  v2
       +------+
          ...
```

Its first Betti number is $r-1$. The connected degree-zero Picard group of the nodal curve is an extension of $J(Y_1)\times J(Y_2)$ by a torus of dimension $r-1$. If every edge has thickness one, the component group of a regular smoothing has order $r$. Thus the same $r$ appears in two different ways: $r-1$ counts independent gluing parameters, while a determinant of their integral pairing equals $r$.

For $r=1$ the graph is a tree. Gluing creates no torus and the component group is trivial, even though the special fiber is reducible. This is the first warning against equating “reducible reduction” with “nontrivial components of the Jacobian.” For $r=2$, one cycle appears and the component group has order two. If the two nodes have thicknesses $a$ and $b$, its order becomes $a+b$. The reduced special fiber alone cannot see this change.

## 2. Nodes and their relative local models

### 2.1 The geometric node

The node is the mildest singularity capable of joining two branches. Over an algebraically closed field its completed local ring is

$$
k[[x,y]]/(xy).
$$

Its normalization is $k[[x]]\oplus k[[y]]$. The two summands are the two branches, and the conductor consists of pairs vanishing at both origins. A function descends exactly when its two values at the origins agree.

This description is intrinsic. If $A$ is the completed local ring of a reduced curve at a node and $\widetilde A$ its normalization, then $\widetilde A/A$ has length one after geometric base change. Conversely, a reduced plane double point with two distinct tangent directions has this completed form. The distinct directions matter: $y^2-x^3=0$ is a cusp, has only one branch, and is not nodal.

A self-intersection of one irreducible component still gives two branches. Its edge is a loop. Deleting loops from the graph would preserve vertex degrees but destroy the arithmetic genus and toric rank. Thus incidence matrices must be allowed to have columns whose boundary is zero.

### 2.2 Smoothing parameters and thickness

Let a node occur in a flat family. The shape of the total space at that node is not a convention but a theorem, proved as the completed local model at a node in Book 9, Theorem 10.5, and we record it in the form used throughout this book.

Let $\mathcal X\to\operatorname{Spec}R$ be a curve in the sense of §1.2 and let $q\in\mathcal X$ be a closed point of the special fiber at which the geometric special fiber has an ordinary double point. Put

$$
\Lambda=\widehat{R^{\mathrm{sh}}},
$$

the completion of a strict henselization of $R$: a complete discrete valuation ring with the same uniformizer $\pi$ and with separably closed residue field $\bar k$. If $k$ is already separably closed one may take $\Lambda=\widehat R$. Write $\tilde q$ for a point of $\mathcal X_\Lambda=\mathcal X\times_R\operatorname{Spec}\Lambda$ above $q$; there are $[\kappa(q):k]$ of them, permuted transitively by $G_k$, and they are the geometric edges of the orbit of $q$. The cited theorem gives an isomorphism of $\Lambda$-algebras

$$
\widehat{\mathcal O}_{\mathcal X_\Lambda,\tilde q}\simeq\Lambda[[x,y]]/(xy-a),
\qquad a\in\mathfrak m_\Lambda,
$$

so the completed equation of the family at the node is $xy=a$ with $a$ in the maximal ideal of the base. The element $a$ is the smoothing parameter. Over a general base its vanishing locus is exactly the locus of the base over which the node persists; over our discrete valuation ring $a$ is never invertible, and $a\neq0$ says that the generic fiber is smooth at the node while $a=0$ says that the singularity propagates.

The same theorem shows that the ideal $a\Lambda$ depends only on the $\Lambda$-algebra $\widehat{\mathcal O}_{\mathcal X_\Lambda,\tilde q}$, being the ideal cut out on the base by the non-smooth locus of the family. Hence one may write $a=u\pi^n$ with $u\in\Lambda^\times$ and $n\geq1$, and the integer

$$
n=v(a)=\operatorname{length}_\Lambda\bigl(\Lambda/a\Lambda\bigr)
$$

depends only on the family and the node, not on the coordinates chosen. A change $x\mapsto ux$ removes the unit, so the essential local model is

$$
A_n=\Lambda[[x,y]]/(xy-\pi^n). \tag{2.1}
$$

The integer $n$ is the thickness. It does not depend on the auxiliary base $\Lambda$: strict henselization and completion of a discrete valuation ring leave a uniformizer a uniformizer, so the normalized valuation of $\Lambda$ restricts to that of $R$, and the same $n$ is obtained from $\widehat R$ whenever the node is already split over $k$. Nor does it depend on which point $\tilde q$ above $q$ is chosen: $G_k$ acts on $\mathcal X_\Lambda$ over $R$, semilinearly over $\Lambda$, and its action preserves the valuation, so it carries the smoothing parameter at one point of the orbit to one of the same valuation at another. This is what licenses the convention of §1.2, which reads the thickness off the completed local equation. Thickness is also the intersection multiplicity of the two branches after an appropriate regular resolution has separated their history. Geometrically, an edge of length $n$ is the compressed record of a chain of $n$ unit edges.

Only the completed equation is used in this book: every later appeal to the local model, whether to test regularity of the total space, to add lengths under contraction, or to compute the monodromy contribution of a node, is a statement about $A_n$ and its completed stalks. The stronger étale-local assertion, that the family is étale locally $xy=a$ inside a smooth relative surface, is an approximation statement that Book 9 explicitly does not prove and that is not needed here.

Thickness is not a multiplicity of the special fiber. The equation $xy=\pi^n$ still has reduced special fiber $xy=0$. It measures singularity of the total space and the rate of smoothing. Confusing these notions leads, for example, to the incorrect claim that every reduced nodal fiber has unit monodromy.

### 2.3 Regular and nonregular total spaces

Regularity of the total space at a node may be tested on the model (2.1). Indeed $\mathcal O_{\mathcal X,q}\to\mathcal O_{\mathcal X_\Lambda,\tilde q}$ is flat and local, its fiber over the closed point is the separable residue extension $\bar k/\kappa(q)$, and $\mathfrak m_q$ generates the target maximal ideal; passing further to the completion $A_n$ changes nothing either. Neither step alters the dimension or the minimal number of generators of the maximal ideal, so the three rings are regular together. The maximal ideal of $A_n$ at the closed point is generated by $x,y,\pi$. Its defining equation has a linear term in the regular local ambient ring exactly when $n=1$. Hence

$$
A_n\text{ is regular at the node}\quad\Longleftrightarrow\quad n=1. \tag{2.2}
$$

For $n>1$, the total space is normal but singular. Successive blowups and removal of redundant components resolve it. The resulting reduced normal-crossing fiber replaces the weighted edge by

```text
v0 -- w1 -- w2 -- ... -- w(n-1) -- vn
```

with $n$ edges of thickness one and $n-1$ exceptional rational components. The chain has no new cycle; it changes the integral metric, not the first Betti number.

This distinction lets two useful models coexist. A stable model contracts every unstable rational chain and is canonical, but may have equations $xy=\pi^n$ and a singular total space. A regular semistable model expands every such edge into unit segments, but may contain many rational components of valence two and is not stable. Calculations must either use the expanded unweighted graph or the contracted weighted graph. Mixing the vertices of one with the edge lengths of the other gives a wrong lattice.

### 2.4 Split and nonsplit nodes

Over $k$, the two branches of a node need not be individually defined. The preimage of a node $q$ in the normalization has coordinate algebra a quadratic étale $\kappa(q)$-algebra. It is split when this algebra is $\kappa(q)\times\kappa(q)$ and nonsplit when it is a quadratic field extension.

After extension to $\bar k$, every node splits and gives an ordinary geometric edge. Descent remembers how $G_k$ permutes its orientations. At a nonsplit self-node, an element may fix the edge and reverse its orientation. On the cycle lattice this acts by $-1$, so the descended one-dimensional torus is nonsplit. Its geometric component group can be cyclic while its $k$-rational subgroup is smaller.

Residue degree is separate again. A closed split node of degree $f$ produces $f$ geometric edges permuted transitively after separable extension. In an intersection computation over $k$, that orbit contributes a factor $f$. The safest procedure is therefore:

1. form the full geometric graph;
2. perform lattice constructions equivariantly;
3. descend the resulting torus or finite group.

Taking a quotient graph first can lose orientation reversal, stabilizers, and residue degrees.

## 3. Semistable and stable families

### 3.1 Fiberwise definitions and relative hypotheses

A nodal curve over a field is a proper, geometrically connected, reduced curve whose only geometric singularities are nodes. A nodal family is a proper flat finitely presented family all of whose geometric fibers are nodal. These conditions imply that the family is Gorenstein and that its relative dualizing sheaf is invertible and compatible with base change. That implication is fiberwise and needs no model of the total space: the local ring of a fiber at a node becomes $\bar k[[x,y]]/(xy)$ after completion and geometric base change, a hypersurface and hence Gorenstein, and the Gorenstein property descends along those faithfully flat maps, so the family is Gorenstein in the sense of Book 9, §9.4. Invertibility of the relative dualizing sheaf, its compatibility with base change, and its branch-and-residue description on fibers are then the results of Book 9, §§9.3--10.4; the last of these uses the completed local model of a node recalled in §2.2, and nothing stronger.

Terminology varies, so we fix it. A semistable curve is a nodal curve in which every rational irreducible component meets the rest of the curve and the markings, if any, in at least two branches. A stable curve requires at least three. A semistable model over $R$ has smooth generic fiber and semistable special fiber. A regular semistable model additionally has regular total space; its special fiber is then a reduced normal-crossing divisor and all thicknesses are one.

A rational component meeting the rest once is a rational tail. It contributes neither genus nor graph cycles and produces avoidable nonuniqueness, so semistability excludes it. A rational component meeting the rest twice is a bridge component. It is harmless for regularity and records metric length, but has a positive-dimensional automorphism group and is contracted by stabilization.

Semistability is not equivalent to regularity. The stable equation $xy=\pi^5$ has a nodal special fiber and may satisfy stability globally, yet its total space is singular. Conversely, resolving it gives a regular semistable model whose inserted two-pointed rational components are not stable.

### 3.2 Stability from the dualizing line

Let $X$ be a nodal curve with marked smooth points, and let $Y_v$ be the normalization of one irreducible component. If $g_v$ is its genus and $n_v$ counts incident branches and markings geometrically, then the normalization and residue description of the dualizing sheaf gives

$$
\deg\bigl(\omega_X(\text{marks})|_{Y_v}\bigr)
=2g_v-2+n_v. \tag{3.1}
$$

This one formula explains stability. The pointed dualizing line is ample exactly when every component has positive degree. A genus-zero component therefore needs at least three special branches; a genus-one component needs at least one; a component of genus at least two needs none. The finite-automorphism definition and the ampleness definition agree.

The proof is local at nodes. Pulling the dualizing line to the normalization permits a simple pole at each preimage of a node. Each branch adds one to the degree. Markings add one in the same fashion. Ordinary canonical degree contributes $2g_v-2$, proving (3.1). On a proper curve, positivity on every component is equivalent to ampleness.

For unmarked curves of arithmetic genus at least two, stability makes the moduli problem separated because no rational bridge can move or be inserted arbitrarily. For genus one an unmarked smooth curve has translations, so a marking or another rigidifying structure is needed for the usual stable pointed theory.

### 3.3 Contraction and uniqueness

Starting from a semistable curve, contract every rational component on which the pointed dualizing line has degree zero. These are precisely rational bridge components. The contraction exists by the relative projective construction associated with a sufficiently large power of the dualizing line. It is an isomorphism elsewhere and replaces each maximal bridge chain by one node.

For completeness, the required semiampleness follows from the curve theory already available. On every positive-degree component, a sufficiently large power of the pointed dualizing line has degree greater than the dualizing degree after subtracting any length-two subscheme. The componentwise vanishing criterion then makes global sections generate and separate points there. On a degree-zero rational bridge, the restriction is trivial, and the node-gluing condition forces every global section to be constant along the whole maximal bridge chain. Thus the morphism defined by a large power separates precisely the points not joined through such a chain. Its image is a proper nodal curve, and the local conductor description shows that the two surviving end branches are glued to one node. Taking the relative Proj of the section algebra gives the contraction in families and commutes with base change. No general contraction theorem is being assumed.

If a chain contains $m$ unit edges, its contraction produces a node of thickness $m$. More generally, contracting consecutive weighted edges adds their lengths:

$$
n_{\mathrm{new}}=n_1+\cdots+n_r. \tag{3.2}
$$

This additivity can be checked by resolving the local surface singularity in reverse or by comparing the intersection matrix of the chain. It is the first appearance of the metric nature of thickness.

The local calculation is inductive. Contract the last rational bridge in a chain and choose parameters $x$ and $y$ on the two surviving end branches. At the two adjacent nodes the unit-thickness equations identify the two branch parameters through one factor of $\pi$ each; eliminating a coordinate on the intervening projective line replaces the two equations by $xy=\pi^2$. Repeating the elimination multiplies the right side by one further factor of $\pi$ at each unit edge. Starting with weighted equations replaces a block of $n_i$ factors by $\pi^{n_i}$, so the final equation is $xy=\pi^{n_1+\cdots+n_r}$. This proves (3.2), including the coefficient rather than only the shape of the contracted node.

For a smooth generic curve of genus at least two, whenever stable reduction exists over $R$, the stable model is unique. Any isomorphism on generic fibers extends because the relative dualizing line is ample and its pluricanonical algebra determines the model. Regular nodal models are not unique: blowing up a smooth point of the special fiber creates a rational tail and leaves the generic fiber unchanged. Under our convention that semistability excludes rational tails, that blowup is no longer semistable. Likewise, blowing up a unit-thickness node produces a nonreduced total transform, not a subdivision by two reduced unit edges. Subdivision is legitimate when it resolves a pre-existing thick node, and stabilization then removes the resulting valence-two bridge chain. These distinctions prevent birational nonuniqueness from being confused with nonuniqueness inside the fixed semistable category.

## 4. Normalization and the conductor

### 4.1 Separating branches

Let $X$ be a nodal curve over a field and $\nu:\widetilde X\to X$ its normalization. The map is finite and an isomorphism away from the nodes. Over a geometric node $q$, its inverse image consists of two points $q^+$ and $q^-$. The normalization should be thought of as cutting every edge of the dual graph at its midpoint.

Normalization of the special fiber is not normalization of the total space. For $xy=\pi^n$, the total space is already normal, even when $n>1$, whereas the special fiber $xy=0$ normalizes to its two branches. This distinction is essential in families: normalizing the total space generally does not provide simultaneous normalization of all fibers.

The conductor ideal

$$
\mathfrak c=\operatorname{Ann}_{\mathcal O_X}
(\nu_*\mathcal O_{\widetilde X}/\mathcal O_X)
$$

is the largest ideal of $\mathcal O_X$ that is also an ideal of $\nu_*\mathcal O_{\widetilde X}$. At a split node it is $(x,y)$ downstairs and $(x)\oplus(y)$ upstairs. Thus its closed subscheme is the node downstairs and the two branch points upstairs.

### 4.2 The conductor square

Let $D\subset X$ be the conductor subscheme and $\widetilde D\subset\widetilde X$ its inverse image. There is a cartesian and cocartesian square

```text
  D~  ------>  X~
  |             |
  |             | normalization
  v             v
  D   ------>   X
```

The square says that $X$ is recovered by gluing the pairs of conductor points in $\widetilde X$. Affinely, if $A\subset\widetilde A$ is the normalization and $I$ the conductor, then

$$
A\simeq \widetilde A\times_{\widetilde A/I} A/I. \tag{4.1}
$$

For a split node this is the elementary identity

$$
k[[x,y]]/(xy)
\simeq
(k[[x]]\oplus k[[y]])
\times_{k\oplus k} k,
$$

where $k\to k\oplus k$ is diagonal. Formula (4.1) makes descent of functions and line bundles explicit and remains valid over nonsplit residue fields.

### 4.3 Functions, units, and line bundles

For split rational nodes the normalization sequence for functions is

$$
0\longrightarrow\mathcal O_X
\longrightarrow\nu_*\mathcal O_{\widetilde X}
\longrightarrow\bigoplus_q k_q
\longrightarrow0, \tag{4.2}
$$

where the last map takes the difference of branch values. Multiplicatively one has

$$
1\longrightarrow\mathcal O_X^\times
\longrightarrow\nu_*\mathcal O_{\widetilde X}^\times
\longrightarrow\bigoplus_q i_{q,*}k_q^\times
\longrightarrow1, \tag{4.3}
$$

with quotient given by the ratio of branch values. Over a nonsplit node, the last term is the quotient of the units of the quadratic branch algebra by diagonal units. This quotient is a torus after descent, not canonically a copy of the multiplicative group.

A line bundle on $X$ is therefore a line bundle on $\widetilde X$ together with, at every node, an identification between its two branch fibers. Changing trivializations on normalized components changes these identifications by vertex scalars. The remaining gluing parameters are exactly graph cycles.

The proof uses the conductor square. Trivialize a line bundle near $\widetilde D$ and $D$; a gluing isomorphism constructs a projective rank-one module over the fiber product (4.1). Conversely, restricting a line bundle gives compatible pieces. Faithfully flat descent removes the temporary splitting and trivializations.

There is a useful exactness check behind this argument. Suppose first that every normalized component is geometrically connected and every node is split. Taking cohomology in (4.3) begins with

$$
1\longrightarrow k^\times
\longrightarrow(k^\times)^V
\xrightarrow{\delta}(k^\times)^E
\longrightarrow\operatorname{Pic}(X)
\longrightarrow\prod_v\operatorname{Pic}(Y_v)
\longrightarrow1. \tag{4.4}
$$

Here $\delta((c_v))_e=c_{t(e)}/c_{o(e)}$. Its kernel is the diagonal because the graph is connected. Every component line bundle can be glued, which gives surjectivity on the right. The cokernel of $\delta$ is a torus whose character lattice is the kernel of the additive boundary map. This passage from multiplicative gluing to integral cycles will be used repeatedly.

Over a general field the same sequence is first written after separable extension. Galois descent then replaces split powers of $\mathbf G_m$ by tori and replaces a product indexed by geometric components by the descended product. Exactness survives because line bundles and their gluing isomorphisms descend effectively. The geometric calculation therefore determines not only a dimension but the full character action.

### 4.4 Differentials and arithmetic genus

The dualizing sheaf consists of differentials on $\widetilde X$ allowed simple poles at branch points, subject to opposite residues:

$$
\omega_X=
\left\{\eta\in
\nu_*\Omega^1_{\widetilde X}
\left(\sum_q(q^++q^-)\right):
\operatorname{res}_{q^+}(\eta)
+\operatorname{res}_{q^-}(\eta)=0\text{ for every }q\right\}. \tag{4.5}
$$

Taking Euler characteristics in (4.2) gives, for a geometrically connected nodal curve,

$$
p_a(X)=\sum_{v\in V}g_v+b_1(\Gamma). \tag{4.6}
$$

Indeed each geometric node lowers $\chi$ by one, while passing from the disjoint normalization to a connected curve corrects by the number of components minus one. The combination is $|E|-|V|+1=b_1(\Gamma)$.

Formula (4.6) explains why loops and parallel edges cannot be discarded. It also predicts the dimension of the generalized Jacobian: the component Jacobians contribute $\sum g_v$, and the graph torus contributes $b_1(\Gamma)$.

## 5. Dual graphs, genera, and descent data

### 5.1 The geometric dual graph

For $X_{\bar k}$, define a vertex $v$ for each irreducible component of its normalization and an edge $e$ for each node. The endpoints are the components containing the two branches. If both branches lie on the same component, $e$ is a loop. Attach the genus weight

$$
g_v=p_a(Y_v)
$$

to the normalized component $Y_v$, and attach thickness $n_e$ to the edge when $X$ occurs as a special fiber of a family.

The resulting object is a weighted metrized graph with integral lengths. Its total genus is

$$
g(\Gamma)=\sum_v g_v+b_1(\Gamma), \tag{5.1}
$$

equal to the arithmetic genus of the curve. Stabilization removes genus-zero vertices of valence two and adds adjacent lengths. It removes genus-zero tails as well, though a semistable model has none.

For a family over a more general base, the combinatorial type may jump. Nodes form finite unramified strata only after suitable stratification, and components need not extend globally. The lattice descriptions below are therefore fiberwise unless a constant split dual graph is explicitly assumed.

### 5.2 Orientations and chain groups

Choose one orientation for each geometric edge. Let

$$
C_1(\Gamma,\mathbf Z)=\bigoplus_{e\in E}\mathbf Z e,
\qquad
C_0(\Gamma,\mathbf Z)=\bigoplus_{v\in V}\mathbf Z v.
$$

The boundary map is

$$
\partial(e)=t(e)-o(e). \tag{5.2}
$$

Changing the chosen orientation replaces $e$ by $-e$ and changes no intrinsic construction. The cycle lattice is

$$
H_1(\Gamma,\mathbf Z)=\ker\partial, \tag{5.3}
$$

and the augmentation $\epsilon(\sum a_vv)=\sum a_v$ has kernel

$$
\operatorname{Div}^0(\Gamma).
$$

For a connected graph the chain complex gives

$$
0\longrightarrow H_1(\Gamma,\mathbf Z)
\longrightarrow C_1
\xrightarrow{\partial}C_0
\xrightarrow{\epsilon}\mathbf Z
\longrightarrow0. \tag{5.4}
$$

Thus $\operatorname{rank}H_1=|E|-|V|+1$. A loop has zero boundary and immediately supplies a cycle generator.

### 5.3 Thicknesses, residue degrees, and Galois action

The group $G_k$ acts on the geometric chain complex. If an element reverses an edge, it sends its oriented generator to its negative. Thickness is constant on every orbit. The pairing and all maps below are $G_k$-equivariant.

One can also compute directly with closed nodes over $k$. If $e$ is a closed node of residue degree $f_e=[\kappa(e):k]$ and thickness $n_e$, its orbit contributes

$$
f_en_e \tag{5.5}
$$

to the descended intersection or length sum whenever the coefficient is constant on that orbit. Formula (5.5) is bookkeeping, not a replacement for the geometric graph: an orbit may connect conjugate vertices or reverse a loop, behavior that a single unoriented quotient edge does not record.

If $k$ is finite, Frobenius acts on vertices and edges. The geometric component group is a finite abelian group with this action. The group of $k$-rational components is its Frobenius-fixed subgroup, which can have smaller order. The same distinction holds for the torus: its character lattice carries Frobenius, and splitness means that action is trivial.

## 6. Divisors and Laplacians on graphs

### 6.1 Multidegrees as vertex divisors

A line bundle $L$ on a reducible nodal curve has a degree on each normalized component. Its multidegree is

$$
\underline{\deg}(L)=\sum_v\deg(L|_{Y_v})v\in C_0(\Gamma,\mathbf Z). \tag{6.1}
$$

The total degree is its augmentation. Degree zero on every component is stronger than total degree zero. The identity component of the Picard group consists of multidegree zero classes, while other total-degree-zero multidegrees label discrete pieces before vertical equivalence is imposed.

A horizontal divisor $D$ on a regular model has multidegree

$$
d_v=(D\cdot Y_v), \tag{6.2}
$$

including residue degrees in the intersection number. If $D$ has degree zero on the generic fiber, then $\sum_vd_v=0$. Moving $D$ by a vertical divisor changes this vector by a graph Laplacian.

### 6.2 Chip-firing and the Laplacian

Give $C_1$ the standard inner product in which oriented edges are orthonormal. The adjoint of $\partial$ is the coboundary

$$
\delta:C_0\longrightarrow C_1,
\qquad
(\delta f)(e)=f(t(e))-f(o(e)).
$$

The graph Laplacian is

$$
\Delta=\partial\delta. \tag{6.3}
$$

Thus

$$
(\Delta f)(v)=\sum_{e\text{ incident to }v}
\bigl(f(v)-f(v_e)\bigr), \tag{6.4}
$$

with parallel edges counted separately and loops contributing zero. Our sign makes $\Delta$ positive semidefinite. The surface intersection matrix of a regular reduced special fiber is $-\Delta$.

Adding the vertical divisor $\sum_v f(v)Y_v$ changes multidegree by $-\Delta f$ under the intersection convention of (6.2). Combinatorially, firing $v$ subtracts its valence from $v$ and adds one chip at the other end of every incident nonloop edge. The sign does not affect the quotient.

For a connected graph, $\ker\Delta$ consists of constant functions. The proof is the energy identity

$$
\langle f,\Delta f\rangle
=\sum_{e\in E}(f(t(e))-f(o(e)))^2. \tag{6.5}
$$

### 6.3 Reduced Laplacians and spanning trees

The graph Jacobian, also called the critical group, is

$$
K(\Gamma)=\operatorname{Div}^0(\Gamma)/\Delta C_0(\Gamma,\mathbf Z). \tag{6.6}
$$

It is finite for connected $\Gamma$. Choose a vertex $v_0$ and delete its row and column from the Laplacian matrix. The resulting reduced Laplacian $\Delta_{v_0}$ presents $K(\Gamma)$, so

$$
|K(\Gamma)|=\det(\Delta_{v_0}). \tag{6.7}
$$

The determinant is independent of $v_0$ and equals the number of spanning trees.

To see the last statement, write $\Delta=BB^t$ for the incidence matrix $B$. After deleting one row, the Cauchy--Binet formula expresses the determinant as a sum over sets of $|V|-1$ edges. The corresponding minor is $0$ unless those edges form a spanning tree, and is $\pm1$ when they do. Squaring removes the sign. This proof also shows why multiple edges count separately and loops never belong to a spanning tree.

The quotient (6.6) is independent of the choice of base vertex even though a reduced matrix is not. Indeed $C_0/\mathbf Z\mathbf 1$ and $\operatorname{Div}^0$ are dual lattices under the vertex pairing, and $\Delta$ induces a full-rank map between them. Choosing $v_0$ merely chooses a basis of the first lattice. This basis-free form is essential when a residue-field symmetry moves every vertex.

There is also a perfect discriminant pairing

$$
K(\Gamma)\times K(\Gamma)\longrightarrow\mathbf Q/\mathbf Z. \tag{6.8}
$$

Given degree-zero divisors $d,d'$, choose $a\in C_0\otimes\mathbf Q$ with $\Delta a=d$ and set $\langle d,d'\rangle=a\cdot d'\bmod\mathbf Z$. Changing $a$ by a constant does nothing because $d'$ has degree zero; changing either divisor by an integral Laplacian changes the value by an integer. Nonsingularity follows from invertibility of the reduced Laplacian over $\mathbf Q$. This is the graph form of the corrected component pairing.

### 6.4 Examples and warnings

For a tree, the only spanning tree is the graph itself, so $K(\Gamma)=0$. For a cycle with $m$ unit edges, $K(\Gamma)\simeq\mathbf Z/m\mathbf Z$. For two vertices joined by $r$ edges,

$$
\Delta=\begin{pmatrix}r&-r\\-r&r\end{pmatrix},
\qquad K(\Gamma)\simeq\mathbf Z/r\mathbf Z. \tag{6.9}
$$

A single vertex with one loop has $\Delta=(0)$ and $\operatorname{Div}^0=0$, so (6.6) is trivial. Yet its cycle lattice has rank one. There is no contradiction: the unit loop corresponds, after regular expansion, to a one-edge polygon whose component group is trivial but whose generalized Jacobian has a one-dimensional torus.

The ordinary Laplacian is suited to unit edges. Replacing an edge of thickness $n$ by $n$ parallel edges is wrong: parallel edges increase conductance, whereas thickness is length in series. The correct operation is subdivision into a chain, or equivalently use of the weighted cycle pairing developed next.

## 7. Cycle lattices and weighted graph Jacobians

### 7.1 Homology and the edge-length pairing

Let every edge have positive integral length $n_e$. On $C_1(\Gamma,\mathbf Z)$ define

$$
\langle e,e'\rangle_n=
\begin{cases}
n_e,&e=e',\\
0,&e\ne e'.
\end{cases} \tag{7.1}
$$

Restricting to the cycle lattice $X=H_1(\Gamma,\mathbf Z)$ gives a positive definite integral pairing

$$
q_n:X\times X\longrightarrow\mathbf Z. \tag{7.2}
$$

It induces an injective map

$$
\mu_n:X\longrightarrow X^\vee=\operatorname{Hom}(X,\mathbf Z),
\qquad x\longmapsto q_n(x,-). \tag{7.3}
$$

Positive definiteness makes the cokernel finite. Notice the direction: the character and cocharacter lattices have the same rank, but the metric supplies a generally nonunimodular inclusion between them.

### 7.2 The discriminant group

Define the weighted graph Jacobian by

$$
K(\Gamma,n)=\operatorname{coker}(\mu_n). \tag{7.4}
$$

Equivalently, inside $X\otimes\mathbf Q$ let

$$
X^\#=\{z:q_n(z,X)\subseteq\mathbf Z\}.
$$

Then

$$
K(\Gamma,n)\simeq X^\#/X. \tag{7.5}
$$

This discriminant description is canonical and is the one that matches monodromy. When every $n_e=1$, it is canonically isomorphic to the critical group (6.6), though the two presentations use different lattices.

If $b_1(\Gamma)=0$, both lattices in (7.3) vanish and the group is trivial. A reducible tree-like fiber therefore has no geometric component group. If $b_1>0$, the order is the determinant of any Gram matrix of $q_n$ in an integral cycle basis.

### 7.3 Comparison with subdivision

Replace an edge $e$ of length $n_e$ by a chain of $n_e$ unit edges, introducing valence-two vertices. Call the subdivided graph $\Gamma^{\mathrm{sub}}$. Collapsing each chain identifies

$$
H_1(\Gamma^{\mathrm{sub}},\mathbf Z)
\simeq H_1(\Gamma,\mathbf Z), \tag{7.6}
$$

because a cycle has the same coefficient on every edge of a chain. Its unit-edge squared length along that chain is $n_e$ times the coefficient squared. Hence (7.6) is an isometry from the unit pairing to $q_n$, and

$$
K(\Gamma,n)\simeq K(\Gamma^{\mathrm{sub}}). \tag{7.7}
$$

This proves invariance under passing between a nonregular weighted stable model and its regular semistable resolution. It also proves length additivity under contraction of bridge chains.

### 7.4 Exact computations

For a weighted cycle with successive lengths $n_1,\ldots,n_r$, the cycle lattice is generated by $e_1+\cdots+e_r$. Therefore

$$
K(\Gamma,n)\simeq
\mathbf Z/(n_1+\cdots+n_r)\mathbf Z. \tag{7.8}
$$

For two vertices joined by $r$ parallel edges of lengths $n_1,\ldots,n_r$, the cycle lattice consists of tuples $(a_i)$ with $\sum a_i=0$. A determinant calculation gives

$$
|K(\Gamma,n)|
=\sum_{i=1}^r\prod_{j\ne i}n_j. \tag{7.9}
$$

More generally,

$$
|K(\Gamma,n)|
=\sum_{T\text{ spanning tree}}\prod_{e\notin T}n_e. \tag{7.10}
$$

One proof applies the ordinary spanning-tree theorem after subdivision and counts spanning trees of the expanded graph. For a fixed spanning tree $T$ of the contracted graph, every chain belonging to $T$ must be included in full. In each chain belonging to $E\setminus T$, exactly one of its $n_e$ unit edges must be omitted, giving $n_e$ choices. Multiplying those choices and summing over $T$ gives (7.10). Equivalently, Cauchy--Binet applied to the cycle matrix gives the same formula.

The invariant factors, not merely the order, matter. They are obtained from the Smith normal form of a Gram matrix: if its determinantal divisors are $d_i$, the successive invariant factors are $d_i/d_{i-1}$. An order calculation alone cannot distinguish $\mathbf Z/4\mathbf Z$ from $(\mathbf Z/2\mathbf Z)^2$.

### 7.5 Discriminant pairing and weighted potentials

The finite group (7.5) carries a canonical perfect symmetric pairing

$$
K(\Gamma,n)\times K(\Gamma,n)
\longrightarrow\mathbf Q/\mathbf Z,
\qquad
([x],[y])\longmapsto q_n(x,y)\bmod\mathbf Z, \tag{7.11}
$$

where $x,y\in X^\#$. It is well defined because pairing an element of $X$ with $X^\#$ is integral. If a class pairs trivially with every class, dual-lattice duality puts its representative back in $X$, proving perfectness. For a weighted cycle of total length $N$, after identifying the group with $\mathbf Z/N\mathbf Z$, this pairing is

$$
(a,b)\longmapsto\frac{ab}{N}\bmod\mathbf Z. \tag{7.12}
$$

There is a vertex-potential description as well. Put $D_n=\operatorname{diag}(n_e)$ and define over $\mathbf Q$

$$
\Delta_n=\partial D_n^{-1}\partial^t. \tag{7.13}
$$

An edge of length $n_e$ therefore has conductance $1/n_e$. Given $d\in\operatorname{Div}^0(\Gamma)$, solve $\Delta_nu=d$ modulo constants. The energy $u^td'$ gives the same rational component pairing as subdivision into unit edges. In particular, for $d=v-w$, the value $u(v)-u(w)$ is the effective resistance between $v$ and $w$.

The matrix (7.13) has rational entries, so its naive cokernel over $\mathbf Z$ is not the weighted graph Jacobian. One must clear denominators with the correct edge lattice and then saturate, or use the integral cycle pairing (7.2). This warning is important in weighted coarse models: reciprocal weights are right for potentials, while direct weights are right for the monodromy lattice. The two descriptions agree only after the integral lattices have been matched.

## 8. Generalized Jacobians of nodal curves

### 8.1 Gluing line bundles across nodes

Let $X$ be a proper geometrically connected nodal curve over an algebraically closed field. A multidegree-zero line bundle pulls back to a degree-zero line bundle on every normalized component. Conversely, choose such component line bundles. At each node, gluing their two branch fibers requires a nonzero scalar. Vertexwise changes of trivialization alter all adjacent scalars, so the genuine freedom is

$$
(\mathbf G_m)^E/
\operatorname{im}\bigl((\mathbf G_m)^V\bigr), \tag{8.1}
$$

where $(c_v)$ maps to $(c_{t(e)}/c_{o(e)})_e$. The diagonal scalar is the kernel of this vertex action. Its character lattice is $H_1(\Gamma,\mathbf Z)$.

The dimension count is

$$
|E|-|V|+1=b_1(\Gamma).
$$

On a tree every gluing scalar can be removed successively from the leaves. Around a cycle, the product of gluing scalars survives. This elementary gauge calculation is the geometric source of the graph torus.

### 8.2 The torus--abelian exact sequence

The identity component $\operatorname{Pic}^0(X)$ is a smooth connected commutative algebraic group, the generalized Jacobian. Normalization gives an exact sequence

$$
0\longrightarrow T_\Gamma
\longrightarrow\operatorname{Pic}^0(X)
\longrightarrow\prod_{v\in V}J(Y_v)
\longrightarrow0, \tag{8.2}
$$

where

$$
X^*(T_\Gamma)\simeq H_1(\Gamma,\mathbf Z). \tag{8.3}
$$

Surjectivity follows because componentwise degree-zero bundles can be glued after choosing branch identifications. The kernel consists of trivial component bundles with gluing scalars, which is the torus just computed. Exactness can also be obtained from cohomology of the multiplicative normalization sequence (4.3).

Consequently

$$
\dim\operatorname{Pic}^0(X)
=\sum_vg_v+b_1(\Gamma)=p_a(X). \tag{8.4}
$$

The group is proper exactly when $\Gamma$ is a tree. Thus compact type means that the dual graph is a tree; reducibility alone does not prevent the Jacobian from remaining an abelian variety.

### 8.3 Characters, loops, and nonsplit tori

Over a general residue field, (8.2) descends. The product of component Jacobians must be interpreted orbitwise, with restriction of scalars when components are defined over extensions. The torus is characterized by its $G_k$-lattice

$$
X^*(T_\Gamma)=H_1(\Gamma_{\bar k},\mathbf Z). \tag{8.5}
$$

A torus is split if and only if this action is trivial. A geometrically irreducible curve with one split self-node gives a split multiplicative torus. If Frobenius reverses the two branches, it acts by $-1$ on the loop generator and the torus is nonsplit.

This distinction persists in point counts. Over a finite field with $q$ elements, the split one-dimensional torus has $q-1$ rational points and the nonsplit norm-one torus has $q+1$. Both have geometric dimension one and the same unoriented geometric graph. Orientation descent supplies the missing sign.

## 9. Relative Picard geometry over a valuation ring

### 9.1 The degree-zero functor and its defect

Let $f:\mathcal X\to\operatorname{Spec}R$ be a proper flat nodal model with smooth geometrically connected generic fiber $C$. The relative Picard sheaf assigns to $T/R$ line bundles on $\mathcal X_T$ modulo pullback from $T$. We now construct its representing group object in the present projective curve setting.

That last assertion needs an argument because the earlier Picard theorem treated smooth curves with geometrically integral fibers, not reducible nodal fibers. We give the missing construction. First pass to a strict henselization. Choose smooth closed points on every geometric component of the special fiber and lift them to horizontal sections. One section rigidifies line bundles; the sum of sufficiently many such sections has positive degree on every component. The finite collection is defined over a finite étale stage, and summing its conjugates produces a descended horizontal divisor $H$ with the same positivity. A sufficiently positive multiple of $H$ is relatively ample, so the nodal model is projective.

Fix a geometric multidegree $d=(d_v)$. After tensoring by a sufficiently large multiple of $H$, every line bundle of multidegree $d$ has vanishing first cohomology on every connected union of components and is generated by global sections. The componentwise vanishing criterion follows from duality: a section of the dual bundle would have negative degree on the maximal connected union on which it is nonzero, with one forced zero at every boundary branch. Semicontinuity makes one multiple work in a neighborhood of the special fiber.

Effective Cartier divisors with the resulting Hilbert polynomial form the open Cartier locus $Q$ in the projective Hilbert scheme. Over $Q$, cohomology and base change make the complete linear system a projective bundle of fixed rank. On a reducible curve not every nonzero section is regular: a section may vanish identically on a component. Accordingly, the relation between two Cartier divisors is the open subspace $U$ of that projective bundle on which the universal section is a non-zero-divisor on every fiber. Its two maps $U\rightrightarrows Q$ send a section to its original and its zero divisor, and they present precisely linear equivalence.

The open relation has local slices. At a geometric point, sections vanishing identically on a fixed component form a proper linear subspace. There are only finitely many components, so their complement is a nonempty open set of regular sections. Choose one such section. After trivializing the locally free bundle of sections, choose linear functionals whose common kernel is its line. Shrink the base so that the kernel remains a line and its universal section remains a non-zero-divisor on every component. The resulting line selects one Cartier divisor in every nearby complete linear system. These slices cover $Q$ fppf-locally. The relation gives unique transition isomorphisms on overlaps, and transitivity gives their cocycle. Effective faithfully flat descent glues the slices. Thus the fppf sheaf of rigidified line bundles of multidegree $d$ is represented by a scheme locally of finite presentation. The use of the open $U$, rather than the whole projective bundle, is exactly what permits nonseparatedness. Varying $d$ and descending from the strict henselization represents the whole relative Picard sheaf $P$.

The same construction also proves smoothness. Across a square-zero extension with ideal $I$, automorphisms, deformations, and obstructions of a rigidified line bundle lie respectively in

$$
H^0(\mathcal X_s,I\mathcal O),\qquad
H^1(\mathcal X_s,I\mathcal O),\qquad
H^2(\mathcal X_s,I\mathcal O).
$$

Rigidification removes the first group and the last vanishes because the fibers are curves. Hence $P$ is smooth. This proves the representability and smoothness used below rather than extending the smooth-fiber theorem past its hypotheses.

There are two degree-zero conditions. Total degree zero is the condition visible on the generic fiber. Multidegree zero requires degree zero on every geometric component of every special fiber. The latter defines the open identity component, whose special fiber is the generalized Jacobian in (8.2).

The total-degree-zero Picard object need not be separated over $R$. A vertical divisor is generically empty, so its line bundle is trivial on $C$; nevertheless it can have nonzero multidegree on the special fiber. Such a divisor provides two sections of the Picard object that agree generically but differ specially.

### 9.2 Vertical divisors and nonseparatedness

Assume first that $\mathcal X$ is regular with split reduced special fiber $\sum_vY_v$. For a vertical divisor

$$
V=\sum_va_vY_v,
$$

the special multidegree of $\mathcal O(V)$ is

$$
\bigl(V\cdot Y_w\bigr)_w=-\Delta(a)_w. \tag{9.1}
$$

The whole fiber is principal, cut out by $\pi$, so adding a constant to every $a_v$ changes no line bundle. Thus vertical divisors modulo the total fiber form the vertex lattice modulo constants, and their multidegrees are the Laplacian image.

The schematic closure of the generic identity in the total-degree-zero Picard object records precisely these generically trivial vertical classes. Quotienting by this closure removes nonseparatedness. The word schematic matters: if the lattice image is not saturated after a map or base change, its finite closure contains information invisible on rational vector spaces.

### 9.3 The separated quotient and its identity component

Let $P$ denote the total-degree-zero relative Picard object and $E$ the schematic closure of its generic identity section. In the regular semistable case the quotient

$$
P/E \tag{9.2}
$$

is smooth and separated and has the extension property for line bundles from smooth test spaces. It is the canonical smooth separated model of the generic Jacobian in this setting. Its identity component has special fiber (8.2), and its group of geometric connected components is finite.

Here is the construction and the separation argument. Work first over a strict henselization and write the reduced special fiber as $\sum_vY_v$. Every vertical divisor $A=\sum_va_vY_v$ gives an $R$-point $\mathcal O(A)$ of $P$ whose generic value is the identity. Conversely, if a line bundle has trivial generic restriction, a generic trivialization is a rational section; regularity of $\mathcal X$ makes its divisor vertical, so the bundle is of this form. If two vertical divisors give the same line bundle, their difference is the divisor of a rational function with no horizontal zero or pole. Its restriction to the proper geometrically connected generic curve is constant, so the difference is a multiple of the principal full fiber. Consequently the special points of $E$ are the vertex lattice modulo constants, and their multidegrees are exactly $-\Delta C_0$. This is also the schematic closure: an infinitesimal deformation in that closure which is zero generically lies in the torsion of $R^1f_*\mathcal O_{\mathcal X}$, and that module is finite free by cohomology and base change. Hence no embedded infinitesimal directions have been omitted.

Translation by these vertical line bundles identifies the multidegree charts of $P$ in each $\Delta C_0$-orbit. Choose representatives for the finitely many orbits in $\operatorname{Div}^0/\Delta C_0$ and glue their smooth Picard charts using these translations. The cocycle is addition of vertical divisors, so the gluing is effective; changing representatives gives the same quotient. This explicitly represents the fppf quotient $P/E$. It is smooth because the charts are smooth.

It is separated by the valuative criterion. Over any dominating discrete valuation ring, lift two sections fppf-locally to $P$. If their quotient is generically trivial, a rational trivialization defines a vertical Cartier divisor on the base-changed curve, even when ramification has made its total space singular. The corresponding point lies in the base change of the schematic closure $E$, so the two sections agree in the quotient. Conversely, equality in the quotient is visibly produced by such a vertical Cartier divisor. The same argument gives the extension property. If $T/R$ is smooth, then $\mathcal X_T$ is regular; fppf-locally on $T$, a rational section of a generic line bundle has a Cartier closure and therefore extends the bundle. Two extensions differ vertically and become equal after quotienting. Thus every generic morphism $T_K\to\operatorname{Pic}^0(C)$ extends uniquely to $T\to P/E$.

All constructions commute with unramified descent, so the quotient and its extension property descend from the strict henselization. For a nonregular thick model, resolve first; the generic Picard variety is unchanged, and Chapter 7 shows that compression of the exceptional chains records exactly the same quotient through the weighted cycle pairing.

This statement is deliberately scoped. It identifies the model supplied by the Picard quotient and its special fiber; the general construction and uniqueness theory for smooth separated models of arbitrary abelian varieties belongs later. For Jacobians of regular semistable curves, the quotient description is enough to calculate every component.

The component calculation can now be proved directly. Every total-degree-zero multidegree is an element of $\operatorname{Div}^0(\Gamma)$. Tensoring by a vertical line bundle changes it by $\Delta C_0$. Hence the components of the separated quotient are indexed by the critical group. Within multidegree zero, normalization and the conductor sequence give the connected generalized Jacobian. Thus the quotient separates into

$$
\text{a connected semiabelian identity component}
\quad\text{and}\quad
\text{a finite graph quotient}. \tag{9.3}
$$

The regularity hypothesis enters at one exact point: it identifies every vertical component with a Cartier divisor and its multidegree with an integral Laplacian column. On a thick model those components may fail to be Cartier at the node. Resolving restores Cartier divisors; compressing the answer replaces the unit pairing by the length pairing.

### 9.4 The valuative meaning of separation

The quotient can be understood without coordinates. Suppose two line bundles on $\mathcal X$ become isomorphic on the generic fiber. Their ratio is generically trivial. On a regular integral surface, a rational trivializing section has divisor supported on the special fiber, so the ratio is $\mathcal O(\sum a_vY_v)$. Thus every failure of uniqueness in extending a generic class comes from a vertical divisor.

Two such extensions determine the same point of the separated quotient because their difference lies in $E$. Conversely, if their special multidegrees differ by a class not in the Laplacian image, no vertical divisor relates them; their images occupy distinct components. This proves the valuative dichotomy

$$
\begin{array}{c}
\text{same generic line bundle and Laplacian-related multidegrees}\\
\Longrightarrow\text{same point after separation},\\
\text{nonzero class in }K(\Gamma)\\
\Longrightarrow\text{distinct special components}.
\end{array} \tag{9.4}
$$

Existence and uniqueness play different roles. Properness of the curve helps extend divisors after moving their support, while separation makes an extension unique only after vertical ambiguity is removed. The finite residual ambiguity is not a defect of separation: it is the genuine component group. In the nonregular case the same statement holds after resolution, with weighted monodromy remembering which exceptional chains were contracted.

If the total space is nonregular, resolve it first or use the equivalent weighted graph. Applying (9.1) directly to the components of $xy=\pi^n$ as though their intersection were transverse of multiplicity one loses the factor $n$.

## 10. Specialization of divisor classes

### 10.1 From horizontal divisors to multidegrees

Let $D=\sum_Pm_PP$ be a degree-zero divisor on $C$. After a finite unramified extension if needed, move $D$ so that the closures of its points meet the special fiber in its smooth locus. Its closure $\overline D$ on a regular semistable model has multidegree

$$
\rho(D)=\sum_v(\overline D\cdot Y_v)v
\in\operatorname{Div}^0(\Gamma). \tag{10.1}
$$

If $D$ is principal, its rational function has a vertical divisor in addition to the horizontal closure. Intersecting the principal divisor with every $Y_v$ shows that $\rho(D)$ lies in the Laplacian image. Therefore (10.1) induces, after passage to the fraction field $K^{\mathrm{sh}}$ of a strict henselization,

$$
J(K^{\mathrm{sh}})\longrightarrow\Phi(\bar k)
\simeq K(\Gamma). \tag{10.2}
$$

The map is independent of the chosen moving representative. It is the component specialization map.

### 10.2 Vertical correction and the component class

Given $d=\rho(D)$, solve over $\mathbf Q$ the balancing equation

$$
\Delta a=d,
\qquad \sum_va_v=0. \tag{10.3}
$$

Connectedness makes the solution unique. The corrected divisor

$$
\overline D+\sum_va_vY_v \tag{10.4}
$$

has intersection zero with every component, up to the chosen sign convention. It is integral exactly when $d$ is a Laplacian of an integral vertex function. Thus the obstruction to integral correction is precisely the class of $d$ in $K(\Gamma)$.

Denominators in (10.3) are not arbitrary. They divide the exponent of the critical group, hence its order, and can be read from cofactors of the Laplacian. This connects the corrected local intersection pairings of arithmetic surfaces to component groups.

### 10.3 Specialization formulas

If a $K$-rational point $P$ specializes to the smooth locus of $Y_v$ and $Q$ to that of $Y_w$, then

$$
\operatorname{sp}([P-Q])=[v-w]\in K(\Gamma). \tag{10.5}
$$

For two components joined by $r$ unit edges, this class generates $\mathbf Z/r\mathbf Z$. For a polygon with $m$ unit edges, the difference between adjacent component labels gives a generator of $\mathbf Z/m\mathbf Z$.

If a closed point has residue degree $f$, its closure meets the geometric fiber in a Galois orbit of $f$ points, so its specialization is the orbit sum of the corresponding vertices. A formula using only the closed component without the factor $f$ gives the wrong total degree.

Specialization to the component group is weaker than specialization to the whole special fiber of the Jacobian. Two divisor classes can have the same component but differ in the torus or in the product of component Jacobians. Conversely, vanishing in all component Jacobians does not force vanishing in the component group. The three layers from Chapter 1 remain distinct.

## 11. Monodromy pairings

### 11.1 Why characters and cocharacters differ

The torus $T$ in the identity component has character lattice $X^*(T)$. Its dual lattice is $X_*(T)=\operatorname{Hom}(X^*(T),\mathbf Z)$. Smoothing supplies a finite-index map between them, not an automatic integral identification.

For a semistable Jacobian the identifications are

$$
X^*(T)\simeq H_1(\Gamma,\mathbf Z),
\qquad
X_*(T)\simeq H_1(\Gamma,\mathbf Z)^\vee. \tag{11.1}
$$

In this book the monodromy homomorphism is constructed directly from the smoothing parameters and the intersection pairing:

$$
\mu:X^*(T)\longrightarrow X_*(T). \tag{11.2}
$$

Its associated bilinear form is symmetric and positive definite. The graph theorem below proves, without assuming autoduality or a polarization theorem from a later book, that the finite failure of (11.2) to be an isomorphism is the component group. Identifying characters and cocharacters by choosing a rational basis would erase exactly that finite index.

### 11.2 The local contribution of a node

Choose orientations on the geometric edges. A cycle $a=\sum_ea_ee$ records exponents of gluing parameters around nodes. For another cycle $b=\sum_eb_ee$, local deformation theory gives

$$
q(a,b)=\sum_{e\in E}n_ea_eb_e. \tag{11.3}
$$

Thus each node contributes independently, weighted by its thickness. Reversing an orientation changes both coefficients and leaves the product unchanged. Formula (11.3) is $G_k$-invariant and descends.

One way to see the coefficient $n_e$ is to resolve $xy=\pi^{n_e}$. A cycle crossing the resulting chain uses every one of its $n_e$ unit edges with the same coefficient, so the unit pairing sums to $n_ea_eb_e$. This also proves that the unit in the local smoothing parameter does not affect monodromy.

For calculations over $k$ using closed edge orbits, a constant coefficient on an orbit contributes $[\kappa(e):k]n_ea_eb_e$. If orientation is reversed by descent, one must first express the cycle in the geometric lattice; a naive orbit coefficient need not exist.

### 11.3 Intersection theory recovers the pairing

On a regular semistable model the component intersection matrix is the negative vertex Laplacian. The exact chain sequence (5.4), together with the unit edge pairing, identifies the discriminant of the vertex intersection lattice with the discriminant of the cycle lattice. This is an integral duality between cuts and cycles.

Concretely, choose a spanning tree. Every non-tree edge determines a fundamental cycle and hence a basis of $H_1$. The Gram matrix of these cycles has diagonal entries equal to their total lengths and off-diagonal entries equal to signed lengths of their shared paths. Its determinant equals a reduced intersection determinant. This proves that the monodromy pairing can be calculated either from nodes or from vertical intersections.

The equality is stronger than equality of determinants: it identifies the discriminant groups and their pairings. It is compatible with subdivision, Galois action, and maps of curves. This compatibility is what makes graph computations legitimate in arithmetic applications rather than merely numerical coincidences.

## 12. Component groups and the graph theorem

### 12.1 The component group

Let $\mathcal J$ be the smooth separated model of the generic Jacobian supplied by the Picard quotient in the semistable setting. Its special fiber has identity component $\mathcal J_k^0$, and

$$
\Phi=\mathcal J_k/\mathcal J_k^0 \tag{12.1}
$$

is the component group. Over $\bar k$ it is a finite constant abelian group; over $k$ it is a finite étale group with Galois action. We write $\Phi(\bar k)$ for the geometric component group and $\Phi(k)=\Phi(\bar k)^{G_k}$ when $k$ is perfect.

The identity component is semiabelian:

$$
0\longrightarrow T_\Gamma
\longrightarrow\mathcal J_k^0
\longrightarrow\prod_vJ(Y_v)
\longrightarrow0. \tag{12.2}
$$

The toric rank is $b_1(\Gamma)$. Good reduction requires both toric rank zero and trivial component group, together with the resulting abelian identity component. A trivial component group alone does not imply good reduction: a one-loop fiber of thickness one has a torus but trivial $\Phi$.

### 12.2 The graph description

**Semistable graph theorem, in Raynaud form.** Let $\mathcal X/R$ be a proper semistable model of a smooth geometrically connected curve, and assume either that $\mathcal X$ is regular or that every node is assigned its thickness. Let $\Gamma$ be the geometric dual graph and $n=(n_e)$. Then there is a canonical $G_k$-equivariant exact sequence

$$
0\longrightarrow H_1(\Gamma,\mathbf Z)
\xrightarrow{\mu_n}
H_1(\Gamma,\mathbf Z)^\vee
\longrightarrow\Phi(\bar k)
\longrightarrow0, \tag{12.3}
$$

where

$$
\mu_n(a)(b)=\sum_en_ea_eb_e. \tag{12.4}
$$

For a regular model all $n_e=1$, and equivalently

$$
\Phi(\bar k)\simeq
\operatorname{Div}^0(\Gamma)/\Delta C_0(\Gamma,\mathbf Z). \tag{12.5}
$$

**Proof strategy.** There are four comparisons, and each is integral. First, the multiplicative conductor sequence says that the torus in the generalized Jacobian has character lattice $H_1(\Gamma,\mathbf Z)$. This is an equality of Galois lattices, not only of ranks.

Second, work on a regular semistable resolution. A vertical divisor $A=\sum a_vY_v$ has multidegree $-\Delta a$. The separated Picard quotient therefore identifies two total-degree-zero multidegrees exactly when their difference lies in $\Delta C_0$. Its geometric components are consequently (12.5). No rational coefficients have entered: the failure of an integral vertical correction is retained.

Third, compare the vertex quotient to graph homology. The unit edge lattice $C_1$ contains the cut lattice $\delta C_0$ and the cycle lattice $H_1$. They are orthogonal over $\mathbf Q$, but their integral direct sum can have finite index. Dualizing the exact chain sequence shows that this index quotient is simultaneously

$$
\operatorname{Div}^0/\Delta C_0
\quad\text{and}\quad
H_1^\vee/H_1, \tag{12.6}
$$

where the second inclusion uses the unit edge pairing. This is the integral cut--cycle duality behind the theorem.

Fourth, resolve a node $xy=\pi^{n_e}$. Its edge becomes a chain of $n_e$ unit edges. A cycle has equal coefficient on every segment, so its self- and cross-pairings acquire the factor $n_e$. Contracting the chain therefore changes the unit inclusion into $\mu_n$ without changing either the generic Jacobian or its separated smooth model. This proves (12.3)--(12.4).

Every step is canonical under permutation and reversal of geometric edges. Descent gives the $G_k$-equivariant sequence. This argument also explains why a quotient graph over $k$, a rational cycle space, or an unweighted stable graph is not enough.

### 12.3 Consequences and counterexamples

The order formula is

$$
|\Phi(\bar k)|
=\det(q_n)
=\sum_{T\text{ spanning tree}}\prod_{e\notin T}n_e. \tag{12.7}
$$

For compact type, $\Gamma$ is a tree and $\Phi=0$. For a weighted cycle, $\Phi$ is cyclic of order the total length. In particular, the regular polygon with $m$ components has component group $\mathbf Z/m\mathbf Z$.

The group need not be cyclic. A graph with one vertex and two loops of lengths $a$ and $b$ has diagonal cycle pairing $\operatorname{diag}(a,b)$ and

$$
\Phi\simeq\mathbf Z/a\mathbf Z\oplus\mathbf Z/b\mathbf Z. \tag{12.8}
$$

If $a=b=1$, the group is trivial despite toric rank two. If $a=b=2$, it is not cyclic although its order is four.

Nor does geometric order determine rational components. For a nonsplit polygon, Frobenius may act by $x\mapsto-x$ on $\mathbf Z/m\mathbf Z$. The rational subgroup then has order $\gcd(2,m)$, not $m$. Statements used over the ground field must retain the descent action.

### 12.4 Four model calculations

The simplest irreducible degeneration has one normalized component $Y$ and one self-node of thickness $n$. Its graph has one vertex and one loop. Thus

$$
0\longrightarrow\mathbf G_m
\longrightarrow\mathcal J_k^0
\longrightarrow J(Y)\longrightarrow0,
\qquad
\Phi(\bar k)\simeq\mathbf Z/n\mathbf Z. \tag{12.9}
$$

At $n=1$ the component group vanishes, but the torus remains. This example isolates the difference between connectedness of the special model and properness of its identity component. If Frobenius reverses the loop, the torus is nonsplit and Frobenius acts by $-1$ on $\mathbf Z/n\mathbf Z$.

Next take two components joined by three nodes of thicknesses $a,b,c$. Orient all edges in the same direction and use cycle basis $e_1-e_3,e_2-e_3$. The monodromy matrix is

$$
Q=\begin{pmatrix}a+c&c\\c&b+c\end{pmatrix},
\qquad
\det Q=ab+ac+bc. \tag{12.10}
$$

Its first invariant factor is

$$
d_1=\gcd(a+c,b+c,c)=\gcd(a,b,c),
$$

and the second is $(ab+ac+bc)/d_1$. Thus

$$
\Phi(\bar k)\simeq
\mathbf Z/d_1\mathbf Z\oplus
\mathbf Z/\bigl((ab+ac+bc)/d_1\bigr)\mathbf Z. \tag{12.11}
$$

For unit thicknesses this is $\mathbf Z/3\mathbf Z$; common thickness can make two nontrivial invariant factors appear. This is a typical two-component calculation in which recording only the number of nodes is insufficient.

Third, let the graph be a tree and allow arbitrary positive genera on its vertices. Then $T_\Gamma=0$ and $\Phi=0$, while

$$
\mathcal J_k^0\simeq\prod_vJ(Y_v). \tag{12.12}
$$

The special curve can be highly reducible, but its generalized Jacobian is proper. A separating node contributes neither monodromy nor a component-group generator. Removing that node disconnects the curve, which is the graph-theoretic test for compact type.

Finally, suppose two components meet at one closed node of residue degree two which splits into two geometric nodes. The geometric graph is a two-edge cycle, so its component group has order two and its toric rank is one. Frobenius exchanges the two edges. Depending on whether it also exchanges the vertices, its action on the cycle generator is respectively $-1$ or $+1$. The closed incidence picture “one node between two components” misses both the geometric cycle and its sign. Expanding to the geometric graph before taking invariants gives the correct answer.

These calculations also test specialization. A point reducing to the first component and a point reducing to the second give the vertex difference. In the three-edge example this class has an order determined by the Smith form of $Q$, not merely by $ab+ac+bc$. In the compact-type example it is always killed by an integral vertical correction.

## 13. Base change, resolution, and saturation

### 13.1 Ramified base change

Let $R'/R$ be a finite extension of ramification index $e$. Substituting $\pi=u(\pi')^e$ into $xy=\pi^n$ gives, up to a unit,

$$
xy=(\pi')^{en}. \tag{13.1}
$$

Thus every edge length is multiplied by $e$. After normalization and regular resolution, an edge of length $n$ becomes a chain of $en$ unit edges. The cycle lattice is canonically unchanged, while the monodromy pairing becomes

$$
q_{R'}=e q_R. \tag{13.2}
$$

If residue extension creates no new splitting, the geometric component-group order changes by

$$
|\Phi_{R'}|=e^{b_1(\Gamma)}|\Phi_R|. \tag{13.3}
$$

This formula concerns geometric groups and uniform scaling of all edge lengths. A residue extension can additionally split components or nodes and change the visible Galois action, though the graph after passage to a common separable closure is unchanged.

There is a sharper integral statement. Write $X=H_1(\Gamma,\mathbf Z)$ and regard $qX\subset X^\vee$. Scaling gives inclusions

$$
eqX\subset qX\subset X^\vee,
$$

hence an exact sequence

$$
0\longrightarrow X/eX
\xrightarrow{\ q\ }
\Phi_{R'}(\bar k)
\longrightarrow\Phi_R(\bar k)
\longrightarrow0. \tag{13.4}
$$

The first arrow sends the class of $x$ to the class of $q(x)$ modulo $eqX$. It is injective because $q$ is injective, and exactness follows by taking successive quotients. Formula (13.3) is the order of (13.4). The sequence need not split: base change can enlarge existing invariant factors rather than append a visibly separate copy of $(\mathbf Z/e\mathbf Z)^{b_1}$. This exact sequence is often more useful than the order formula when tracking a torsion class through ramified extension.

### 13.2 Subdivision and stabilization

Resolution subdivides; stabilization contracts valence-two genus-zero vertices. Both preserve the cycle lattice and its metric pairing when lengths are transported correctly. Hence they preserve the component group.

A blowup at a node of a regular semistable fiber does not simply subdivide it while keeping the fiber reduced: the total transform introduces multiplicities, and further minimalization may be required. The clean subdivision statement refers to resolving a thick node or to admissible semistable modification with its correct reduced model. A blowup at a smooth point introduces a rational tail, which semistable contraction removes and which contributes no cycle.

These cautions explain why arbitrary birational pictures are not interchangeable. The invariant is not the bare incidence graph of every intermediate fiber; it is the cycle lattice with the length pairing induced by the semistable model.

### 13.3 Descent and residue extensions

Under an unramified extension, thicknesses remain unchanged. The geometric graph is the same, but a larger residue field may split vertex and edge orbits. The finite étale component group base-changes, and its rational points become invariants under the smaller Galois group.

For a nonsplit node that splits over a quadratic unramified extension, the geometric edge already existed before extension; what changes is that its two orientations become separately visible. The torus becomes split, while the geometric monodromy pairing and component group do not change. This is why “number of components over $k$” is not a reliable input to the graph theorem.

### 13.4 Saturation is arithmetic data

For a homomorphism of free lattices $u:L\to M$, the saturation of its image is

$$
\operatorname{Sat}(uL)=M\cap(uL\otimes\mathbf Q).
$$

The quotient $\operatorname{Sat}(uL)/uL$ is finite and measures the failure of primitivity. Rational linear algebra sees only the saturated subspace and loses this quotient.

Monodromy itself is a saturation problem: $\mu_n(X)$ has full rank in $X^\vee$, and

$$
\Phi=X^\vee/\mu_n(X). \tag{13.5}
$$

Finite maps and correspondences introduce further lattice images. Even if a map is an isomorphism after tensoring with $\mathbf Q$, its integral cokernel can contribute torsion to a component group. One must compute Smith invariants or prove primitivity; rank and determinant over a field are insufficient.

## 14. Finite maps and correspondences

### 14.1 Maps of components and harmonicity

Let $f:\mathcal X\to\mathcal Y$ be a finite flat morphism of semistable curves over the same discrete valuation ring. To read it on dual graphs we impose the precise admissibility condition used in this chapter: nodes map to nodes, their inverse images contain no smooth points, and after strict henselization the map at a node $e$ above $e'$ has compatible coordinates

$$
\mathcal Y:\ uv=\pi^{n_{e'}},\qquad
\mathcal X:\ xy=\pi^{n_e},\qquad
f^*u=\alpha x^{m_e},\quad f^*v=\beta y^{m_e},
\tag{14.1}
$$

where $\alpha,\beta$ are units and $m_e\geq1$. Exchanging the two branches merely reverses both orientations. Comparing the two smoothing equations gives

$$
n_{e'}=m_en_e. \tag{14.2}
$$

For a map between bases of ramification index $r$, the comparison is $m_en_e=rn_{e'}$; all formulas below are applied after putting both models over one base. A component $Y_v$ of the source maps to a component $Z_w$ of the target with degree $d_v$, and $m_e$ is the ramification degree at the corresponding branch.

Flatness forces the harmonicity relation

$$
\sum_{\substack{e\ni v\\e\mapsto e'}}m_e=d_v, \tag{14.3}
$$

independent of the chosen target branch at $w$. Indeed, restrict the finite flat map of components to the fiber over that branch point. The sum of the ramification indices in the fiber equals the component degree. This is conservation of degree at a vertex. Over nonclosed residue fields the same formula is made on the geometric graph; a closed-point version also multiplies each summand by its residue degree.

A finite generic map need not extend to a finite map between chosen models. Normalize the target in the source function field, resolve, and stabilize as needed. The induced graph map is then attached to that controlled extension, not to an arbitrary rational map of special fibers.

### 14.2 Pullback, norm, and adjunction

The finite map supplies pullback and norm on line bundles,

$$
f^*:\operatorname{Pic}(\mathcal Y)\to\operatorname{Pic}(\mathcal X),
\qquad
\operatorname{Nm}_f:\operatorname{Pic}(\mathcal X)\to\operatorname{Pic}(\mathcal Y), \tag{14.4}
$$

with

$$
\operatorname{Nm}_f\circ f^*=[d] \tag{14.5}
$$

when $f$ has constant degree $d$. The norm used here is not an additional input: for finite locally free $f$ it is

$$
\operatorname{Nm}_f(L)=
\det(f_*L)\otimes\det(f_*\mathcal O_{\mathcal X})^{-1}.
$$

After trivializing $L$, transition units act on the finite locally free algebra by multiplication; taking determinants proves multiplicativity, base-change compatibility, and (14.5). On vertex divisors, pullback weights inverse images by component and residue degrees; pushforward multiplies by residue degrees and local degrees. Harmonicity ensures that Laplacian-equivalent divisors remain equivalent, so both maps descend to graph Jacobians and component groups.

The variance on cycle lattices must be stated carefully. Orient edges compatibly. Define

$$
f_*:H_1(\Gamma_{\mathcal X},\mathbf Z)
\longrightarrow H_1(\Gamma_{\mathcal Y},\mathbf Z),
\qquad e\longmapsto e', \tag{14.6}
$$

and

$$
f^*:H_1(\Gamma_{\mathcal Y},\mathbf Z)
\longrightarrow H_1(\Gamma_{\mathcal X},\mathbf Z),
\qquad e'\longmapsto\sum_{e\mapsto e'}m_e e. \tag{14.7}
$$

The first is a chain map and therefore preserves cycles. Harmonicity is exactly what makes the boundary of the second expression vanish when the input is a cycle. These names describe the graph maps: on torus character lattices, $f^*$ is induced contravariantly by the norm map, whereas $f_*$ is induced contravariantly by pullback of line bundles.

With the monodromy pairings they are adjoint:

$$
q_{\mathcal X}(f^*a,b)=q_{\mathcal Y}(a,f_*b). \tag{14.8}
$$

Indeed, the contribution of an edge $e$ on the left is

$$
n_em_ea_{e'}b_e=n_{e'}a_{e'}b_e
$$

by (14.2), and grouping by $e'$ gives the right side. Moreover $f_*f^*=d$ on cycles: the sum of the $m_e$ above any geometric target edge is the generic degree, by harmonicity at either endpoint.

Dualizing gives the actual maps on the monodromy cokernels. Pullback on component groups is induced by

$$
f_*^*:H_1(\Gamma_{\mathcal Y})^\vee
\longrightarrow H_1(\Gamma_{\mathcal X})^\vee,
$$

and norm is induced by

$$
f^{*\vee}:H_1(\Gamma_{\mathcal X})^\vee
\longrightarrow H_1(\Gamma_{\mathcal Y})^\vee.
$$

Adjunction says respectively that these maps carry $\mu_{\mathcal Y}H_1(\Gamma_{\mathcal Y})$ into $\mu_{\mathcal X}H_1(\Gamma_{\mathcal X})$ and conversely. Hence they descend, and norm after pullback is multiplication by $d$ on the component group as well as on the generic Jacobian. This proves the integral functoriality; no passage to a rational cycle space is involved.

### 14.3 Correspondences and component groups

A finite correspondence from $X$ to itself is represented by

$$
X\xleftarrow{\alpha}Z\xrightarrow{\beta}X
$$

and acts on the Jacobian by

$$
T=\beta_*\alpha^*. \tag{14.9}
$$

If both maps extend in a controlled way to semistable models, the same formula acts on normalized component Jacobians, graph homology, and the component group. The transpose correspondence

$$
T^t=\alpha_*\beta^* \tag{14.10}
$$

is adjoint for the monodromy pairing.

This yields a practical rule. Compute the action first on oriented edges with all local and residue degrees, verify that it preserves cycles, and then take the adjoint or cokernel. An action on vertices alone can miss loop cycles. An action on the rational cycle space can miss a nonsaturated image. An action computed after forgetting orientation can give the wrong sign at nonsplit nodes.

No extension hypothesis is needed for existence of the action on components. Pullback and norm define the generic homomorphism of Jacobians. Apply the extension property of Chapter 9 to the smooth separated model itself: the generic homomorphism extends uniquely, and uniqueness makes it a group homomorphism. It therefore acts on the identity component and on $\Phi$.

The model hypothesis is needed only for the edge formula. If a generic correspondence does not extend finitely to the chosen models, normalize its graph and take a common regular domination. Pullback, pushforward, and the projection formula there compute the same extended homomorphism; uniqueness of extension proves independence of the domination. A direct formula on edges is asserted only when the finite part has the admissible local form (14.1). This distinction avoids smuggling in a semistable-reduction theorem for finite maps.

## 15. A calculation package for arithmetic curves

### 15.1 The regular split algorithm

Suppose the residue field is separably closed and $\mathcal X/R$ is regular semistable. The entire calculation can be organized as follows.

1. List normalized components $Y_v$, their genera, and all nodes, retaining loops and multiple edges.
2. Choose edge orientations and form the incidence matrix $B$.
3. Compute $\Delta=BB^t$. Delete one row and column to present the critical group.
4. Use Smith normal form, not only the determinant, to obtain invariant factors.
5. Identify the torus character lattice with $\ker B=H_1(\Gamma,\mathbf Z)$.
6. Restrict the unit edge pairing to this kernel; its cokernel gives the same component group.
7. For a degree-zero divisor, intersect its closure with components and reduce the resulting vector modulo $\Delta\mathbf Z^V$.

The semiabelian identity component is

$$
0\to\mathbf G_m^{b_1}\to\mathcal J_k^0
\to\prod_vJ(Y_v)\to0, \tag{15.1}
$$

and the geometric component group is the critical group just computed.

### 15.2 The weighted and nonsplit algorithm

For a stable or nonregular model, attach to each geometric edge the valuation of its smoothing parameter. Work after a common separable residue extension, retaining the Galois action. Form the cycle lattice and the Gram matrix

$$
Q=Z^t\operatorname{diag}(n_e)Z, \tag{15.2}
$$

where the columns of $Z$ are an integral cycle basis expressed in the oriented-edge basis. Then

$$
\Phi(\bar k)=\operatorname{coker}(Q), \tag{15.3}
$$

and $G_k$ acts through its signed permutation action on edges. The torus is the one whose character lattice is this signed cycle lattice. Ground-field component classes are Galois invariants, not the entire geometric cokernel.

If preferred, subdivide each length-$n_e$ edge into $n_e$ unit edges and use the regular algorithm. The two answers agree. For closed-node calculations over $k$, include residue degrees, but use the geometric graph whenever an orbit can reverse orientation.

### 15.3 Reusable formulas

For a connected semistable geometric fiber:

$$
p_a(X)=\sum_vg_v+b_1(\Gamma), \tag{15.4}
$$

$$
X^*(T)=H_1(\Gamma,\mathbf Z), \tag{15.5}
$$

$$
q(a,b)=\sum_en_ea_eb_e, \tag{15.6}
$$

$$
\Phi(\bar k)=\operatorname{coker}
\left(H_1(\Gamma,\mathbf Z)
\xrightarrow{q}H_1(\Gamma,\mathbf Z)^\vee\right), \tag{15.7}
$$

$$
|\Phi(\bar k)|=
\sum_{T\text{ spanning tree}}\prod_{e\notin T}n_e. \tag{15.8}
$$

For a regular model, also

$$
\Phi(\bar k)=
\operatorname{Div}^0(\Gamma)/\Delta\mathbf Z^V. \tag{15.9}
$$

For a degree-zero horizontal divisor $D$ meeting smooth points,

$$
\operatorname{sp}([D])=
\left[(\overline D\cdot Y_v)_v\right]\in\Phi(\bar k). \tag{15.10}
$$

Under ramified base change of index $e$ with no combinatorial splitting,

$$
q\mapsto eq,
\qquad
|\Phi|\mapsto e^{b_1}|\Phi|. \tag{15.11}
$$

Under a finite map, pullback and norm are adjoint for $q$, and their composite is multiplication by the generic degree. These formulas are the exact input later needed for modular-curve special fibers, specialization of cuspidal divisors, actions of finite correspondences, and calculations of components of Jacobians.

### 15.4 Conclusion

A semistable degeneration does not reduce a curve to a graph. It separates the curve into geometry on normalized components and arithmetic in their gluing. The normalized Jacobians form the abelian part. Graph cycles form the torus character lattice. Smoothing thicknesses turn that lattice into a metrized integral lattice. Its discriminant is the component group.

This synthesis explains why regularity, splitting, and saturation can never be treated as cosmetic. Regularity decides whether every edge has unit length. Splitting decides whether the graph torus is split and whether geometric components are rational. Residue degrees decide the multiplicity of closed intersections. Saturation decides which finite quotient survives after rational identities have forgotten integral index.

The central exact sequence

$$
0\longrightarrow H_1(\Gamma,\mathbf Z)
\longrightarrow H_1(\Gamma,\mathbf Z)^\vee
\longrightarrow\Phi(\bar k)
\longrightarrow0
$$

therefore carries more than a determinant. It links local node equations, global line bundles, vertical intersection theory, base change, and finite correspondences. Once its edge lengths and descent action are recorded correctly, a singular special fiber becomes a precise calculator for the toric and component behavior of the generic Jacobian.
