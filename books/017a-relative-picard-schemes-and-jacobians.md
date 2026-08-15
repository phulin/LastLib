# Relative Picard Schemes and Jacobians

## Contents

- [1. From line bundles to a geometric group](#1-from-line-bundles-to-a-geometric-group)
  - [1.1 The moduli problem](#11-the-moduli-problem)
  - [1.2 Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
  - [1.3 What must be rigidified](#13-what-must-be-rigidified)
- [2. The relative Picard sheaf](#2-the-relative-picard-sheaf)
  - [2.1 Presheaves, sheafification, and variance](#21-presheaves-sheafification-and-variance)
  - [2.2 Rigidification along a section](#22-rigidification-along-a-section)
  - [2.3 Descent and the Brauer obstruction](#23-descent-and-the-brauer-obstruction)
  - [2.4 Group law and base change](#24-group-law-and-base-change)
- [3. Representability for smooth relative curves](#3-representability-for-smooth-relative-curves)
  - [3.1 High-degree divisor charts](#31-high-degree-divisor-charts)
  - [3.2 The quotient construction](#32-the-quotient-construction)
  - [3.3 The representability theorem](#33-the-representability-theorem)
  - [3.4 Removing the section](#34-removing-the-section)
- [4. Degree components and the Jacobian](#4-degree-components-and-the-jacobian)
  - [4.1 Relative degree](#41-relative-degree)
  - [4.2 Picard components as torsors](#42-picard-components-as-torsors)
  - [4.3 The identity component](#43-the-identity-component)
  - [4.4 Genus zero and genus one](#44-genus-zero-and-genus-one)
- [5. Infinitesimal geometry](#5-infinitesimal-geometry)
  - [5.1 Lifting line bundles](#51-lifting-line-bundles)
  - [5.2 Tangent and cotangent spaces](#52-tangent-and-cotangent-spaces)
  - [5.3 Smoothness and dimension](#53-smoothness-and-dimension)
  - [5.4 The formal group at the identity](#54-the-formal-group-at-the-identity)
- [6. Universal line bundles and the see-saw principle](#6-universal-line-bundles-and-the-see-saw-principle)
  - [6.1 The Poincare bundle](#61-the-poincare-bundle)
  - [6.2 The see-saw principle](#62-the-see-saw-principle)
  - [6.3 Biextension identities](#63-biextension-identities)
- [7. Abel maps](#7-abel-maps)
  - [7.1 The pointed Abel--Jacobi map](#71-the-pointed-abel--jacobi-map)
  - [7.2 Higher Abel maps and their fibers](#72-higher-abel-maps-and-their-fibers)
  - [7.3 Differentials of Abel maps](#73-differentials-of-abel-maps)
  - [7.4 Generation of the Jacobian](#74-generation-of-the-jacobian)
- [8. Theta divisors and the canonical polarization](#8-theta-divisors-and-the-canonical-polarization)
  - [8.1 Why a divisor should yield duality](#81-why-a-divisor-should-yield-duality)
  - [8.2 Construction by determinant of cohomology](#82-construction-by-determinant-of-cohomology)
  - [8.3 The homomorphism attached to theta](#83-the-homomorphism-attached-to-theta)
  - [8.4 Principality](#84-principality)
  - [8.5 Independence of choices and base change](#85-independence-of-choices-and-base-change)
- [9. The Albanese property](#9-the-albanese-property)
  - [9.1 Pointed maps to abelian schemes](#91-pointed-maps-to-abelian-schemes)
  - [9.2 Existence and uniqueness of factorization](#92-existence-and-uniqueness-of-factorization)
  - [9.3 The unpointed Albanese torsor](#93-the-unpointed-albanese-torsor)
- [10. Finite maps, pullback, and norm](#10-finite-maps-pullback-and-norm)
  - [10.1 Pullback on Picard schemes](#101-pullback-on-picard-schemes)
  - [10.2 The norm of a line bundle](#102-the-norm-of-a-line-bundle)
  - [10.3 Degree and composition formulas](#103-degree-and-composition-formulas)
  - [10.4 Adjointness under the canonical polarization](#104-adjointness-under-the-canonical-polarization)
- [11. Correspondences](#11-correspondences)
  - [11.1 From spans of curves to homomorphisms](#111-from-spans-of-curves-to-homomorphisms)
  - [11.2 Composition and transpose](#112-composition-and-transpose)
  - [11.3 Divisorial correspondences](#113-divisorial-correspondences)
  - [11.4 Symmetry and Rosati adjoints](#114-symmetry-and-rosati-adjoints)
- [12. Nodal curves and generalized Jacobians](#12-nodal-curves-and-generalized-jacobians)
  - [12.1 Line bundles through normalization](#121-line-bundles-through-normalization)
  - [12.2 The torus--abelian exact sequence](#122-the-torus--abelian-exact-sequence)
  - [12.3 Multidegrees and connected components](#123-multidegrees-and-connected-components)
  - [12.4 Relative nodal families](#124-relative-nodal-families)
- [13. Semistable specialization over a valuation ring](#13-semistable-specialization-over-a-valuation-ring)
  - [13.1 Why total degree is not separated](#131-why-total-degree-is-not-separated)
  - [13.2 Vertical line bundles and the Laplacian](#132-vertical-line-bundles-and-the-laplacian)
  - [13.3 The separated quotient](#133-the-separated-quotient)
  - [13.4 Functoriality on special fibers](#134-functoriality-on-special-fibers)
- [14. Descent, twists, and failure modes](#14-descent-twists-and-failure-modes)
  - [14.1 Descent of Picard data](#141-descent-of-picard-data)
  - [14.2 Curves without rational points](#142-curves-without-rational-points)
  - [14.3 Hypotheses that cannot be dropped](#143-hypotheses-that-cannot-be-dropped)
- [15. The complete Jacobian package](#15-the-complete-jacobian-package)
  - [15.1 A functorial summary](#151-a-functorial-summary)
  - [15.2 Conclusion](#152-conclusion)

## 1. From line bundles to a geometric group

### 1.1 The moduli problem

For one proper smooth curve $C$ over a field, divisor theory turns addition of points into tensor product of line bundles. The quotient of divisors by rational functions is the group $\operatorname{Pic}(C)$. This group is already rich, but arithmetic geometry asks for more than its abstract elements. One wants the line-bundle classes to vary in families, to specialize, to possess tangent spaces, and to admit maps induced by morphisms of curves. In other words, one wants a geometric object whose points are line bundles.

There are three obstacles. A line bundle on $C_T=C\times_S T$ may be changed by pulling back a line bundle from $T$ without changing any fiberwise class. Line bundles and their isomorphisms descend faithfully flatly, but a compatible family of relative classes need not have one global representative. Finally, every line bundle has scalar automorphisms, so an attempted universal family is not unique until those scalars are removed.

The relative Picard sheaf solves the first two problems by quotienting and sheafifying. A rigidification solves the third. Representability then turns the sheaf into a group scheme. Its degree-zero identity component is the **Jacobian**. The Jacobian remembers the first coherent cohomology of the curve, carries a canonical principal polarization, and is both the Picard and Albanese object of the curve. These structures explain why maps and correspondences of curves act linearly on a proper commutative group.

The theory has a second face at bad fibers. For a nodal curve the connected Picard group is no longer proper: loops in the dual graph contribute a torus. In a semistable family, vertical divisors make the total-degree-zero Picard object nonseparated. Keeping these phenomena visible will prevent smooth statements from being applied outside their range.

### 1.2 Standing hypotheses and notation

The base $S$ is locally noetherian unless a statement explicitly permits a more general base. A **smooth relative curve** is a smooth, proper, finitely presented morphism

$$
f:C\longrightarrow S
$$

whose geometric fibers are connected and one-dimensional. Their genus is

$$
g(s)=\dim_{\kappa(\bar s)}H^1(C_{\bar s},\mathcal O_{C_{\bar s}}).
$$

It is locally constant, so discussions may be made on an open-and-closed part of $S$ on which it equals $g$. A chosen section is denoted $e:S\to C$. Smooth proper curves with a section are projective: the effective Cartier divisor $e(S)$ has positive degree on every fiber, and a sufficiently high power of its associated line bundle is relatively very ample.

For $T\to S$, write $C_T=C\times_S T$ and $f_T:C_T\to T$. The symbol $\operatorname{Pic}(X)$ means isomorphism classes of line bundles on $X$. The relative object will always carry a subscript, as in $\operatorname{Pic}_{C/S}$. Tensor product is written additively only after passage to the representing group scheme. The neutral line bundle is $\mathcal O$.

The results on divisors, relative Riemann--Roch, Serre duality, and symmetric powers established earlier are used in their relative forms. Thus $R^1f_*\mathcal O_C$ is locally free of rank $g$ and commutes with arbitrary base change, and

$$
(R^1f_*\mathcal O_C)^\vee\simeq f_*\omega_{C/S}.
$$

For a nodal family, $\omega_{C/S}$ means the relative dualizing line bundle and the necessary Gorenstein hypothesis will be stated.

The dependency boundary is precise. The divisor, duality, and Abel-differential package comes from Book 9; the nodal normalization, graph-lattice, and semistable Picard-quotient theorems come from Book 16; effective faithfully flat descent comes from Book 10; and finite cohomology, arbitrary base change in the stated vanishing range, smooth Picard representability with a section, and dual abelian schemes come from Book 15. This book reconstructs the Picard and Jacobian package needed for its catalog scope, but does not appeal to the later theories of general abelian schemes or Néron models.

### 1.3 What must be rigidified

Suppose $\mathcal L$ is a line bundle on $C_T$ and $\mathcal M$ is a line bundle on $T$. On every geometric fiber of $C_T/T$, the bundles $\mathcal L$ and $\mathcal L\otimes f_T^*\mathcal M$ are isomorphic. A relative moduli problem must therefore identify them. This is not merely convenient: without the quotient, the base contributes an irrelevant copy of $\operatorname{Pic}(T)$ at every test scheme.

If $e$ is present, a class has a canonical normalized representative

$$
\mathcal L^{\mathrm{rig}}
=\mathcal L\otimes f_T^*(e_T^*\mathcal L)^{-1},
$$

together with the evident trivialization along $e_T$. An automorphism of a line bundle is multiplication by a unit on $C_T$. Since geometrically connected reduced fibers give

$$
(f_T)_*\mathcal O_{C_T}=\mathcal O_T
$$

universally, an automorphism that is the identity along $e_T$ is the identity everywhere. Rigidification thus changes a moduli groupoid with scalar automorphisms into a set-valued functor. It does not force locally defined line bundles to glue globally; that is why sheafification remains necessary.

## 2. The relative Picard sheaf

### 2.1 Presheaves, sheafification, and variance

The naive relative Picard presheaf on $S$-schemes is

$$
T\longmapsto
\operatorname{Pic}(C_T)/f_T^*\operatorname{Pic}(T). \tag{2.1}
$$

A map $T'\to T$ pulls line bundles back, so (2.1) is contravariant in the test scheme. Tensor product makes it a presheaf of abelian groups. Its fppf sheafification is denoted

$$
\operatorname{Pic}_{C/S}.
$$

One may equivalently use fpqc sheafification here. Indeed line bundles have effective fpqc descent, and every fpqc descent question is affine-locally reduced to finitely many data. The fppf and fpqc sheaves associated to (2.1) agree for this proper finitely presented family.

Why can (2.1) fail to be a sheaf? Relative classes on an fppf cover $T_i\to T$ may be represented by $\mathcal L_i$, while the comparison over $T_i\times_TT_j$ is valid only after tensoring by a line bundle from the overlap. These base bundles can form a nontrivial two-cocycle. Sheafification remembers the compatible relative class even if no $\mathcal L$ on $C_T$ represents it.

### 2.2 Rigidification along a section

Let $\mathscr P_e(T)$ be the set of pairs $(\mathcal L,\alpha)$ where $\mathcal L$ is a line bundle on $C_T$ and

$$
\alpha:e_T^*\mathcal L\xrightarrow{\sim}\mathcal O_T
$$

is a rigidification, modulo isomorphisms respecting $\alpha$. Tensor product makes $\mathscr P_e$ an abelian-group functor.

**Rigidification theorem.** The fppf sheaf associated to $\mathscr P_e$ is canonically isomorphic to $\operatorname{Pic}_{C/S}$.

**Proof.** Forgetting $\alpha$ gives a relative Picard class. Conversely, normalize any representative by the formula in Section 1.3. If $\mathcal L$ is replaced by $\mathcal L\otimes f_T^*\mathcal M$, then its normalization is canonically isomorphic to the old normalization: the factor $f_T^*\mathcal M$ is cancelled by the inverse of its restriction along $e_T$. Thus normalization depends only on the relative class wherever a representative exists.

On overlaps, isomorphisms between normalized bundles are unique because a rigidified scalar automorphism is trivial. Their triple cocycle is therefore automatic once it holds as a relative class. Effective descent for line bundles produces the rigidified bundle after an fppf refinement. The two constructions are inverse as sheaves. $\square$

This theorem is the precise reason a section produces a universal line bundle later. Without a section the Picard sheaf can still be representable, but its universal relative class need not be represented by one line bundle on the product.

### 2.3 Descent and the Brauer obstruction

The gap between a relative class and an actual line bundle is measured by a gerbe of local representatives. In elementary terms, choose an fppf cover $T_i\to T$, representatives $\mathcal L_i$, and comparison isomorphisms on double overlaps. On triple overlaps their product is multiplication by a unit $u_{ijk}$. The units form a $\mathbf G_m$-valued two-cocycle. Its class vanishes exactly when the comparisons can be rescaled to satisfy the cocycle and the $\mathcal L_i$ descend.

For a proper flat family with universally $f_*\mathcal O_C=\mathcal O_S$, the low-degree descent sequence takes the form

$$
0\longrightarrow\operatorname{Pic}(T)
\longrightarrow\operatorname{Pic}(C_T)
\longrightarrow\operatorname{Pic}_{C/S}(T)
\xrightarrow{\delta}\operatorname{Br}(T)
\longrightarrow\operatorname{Br}(C_T). \tag{2.2}
$$

Here $\operatorname{Br}$ denotes the fppf cohomological Brauer group $H^2(-,\mathbf G_m)$. Exactness at the middle terms follows directly from the cocycle construction: $\delta$ is the obstruction just described; if it vanishes, a representative exists; and two representatives differ by pullback from $T$. A section kills the obstruction because pullback along $e_T$ splits $\operatorname{Br}(T)\to\operatorname{Br}(C_T)$. Thus every relative class is represented uniquely by a rigidified line bundle when a section is fixed.

The warning is concrete. A conic over a field can possess a degree-one point of its Picard sheaf even when it has no degree-one line bundle defined over the field. The point is a descent class whose Brauer obstruction is the conic class. Geometric points alone do not detect this distinction.

### 2.4 Group law and base change

Tensor product, dualization, and the trivial bundle define natural transformations

$$
m:\operatorname{Pic}_{C/S}\times_S\operatorname{Pic}_{C/S}
\longrightarrow\operatorname{Pic}_{C/S},
$$

$$
i:\operatorname{Pic}_{C/S}\longrightarrow\operatorname{Pic}_{C/S},
\qquad 0:S\longrightarrow\operatorname{Pic}_{C/S}.
$$

The group identities hold on representatives and therefore after sheafification. For every $S'\to S$, the defining functor gives a canonical isomorphism of sheaves

$$
\operatorname{Pic}_{C/S}\times_SS'
\xrightarrow{\sim}
\operatorname{Pic}_{C_{S'}/S'}. \tag{2.3}
$$

This assertion precedes representability: both sides have the same values after pulling a test scheme over $S'$ back to $S$. Once represented, (2.3) becomes an isomorphism of group schemes. Base-change compatibility is therefore built into the construction rather than checked only on geometric points.

## 3. Representability for smooth relative curves

### 3.1 High-degree divisor charts

The Picard functor is unbounded because degrees range through all integers. Fixing a degree makes it finite-dimensional, and high degree makes it accessible through effective divisors. Let $C/S$ be smooth projective of genus $g$, initially with a section. The symmetric power $C^{(d)}$ represents effective relative Cartier divisors of degree $d$, and its universal divisor defines the Abel transformation

$$
a_d:C^{(d)}\longrightarrow\operatorname{Pic}^d_{C/S},
\qquad D\longmapsto\mathcal O(D). \tag{3.1}
$$

If $d\geq2g-1$, relative Riemann--Roch and duality give, for every degree-$d$ line bundle $L$ on a geometric fiber,

$$
H^1(C_s,L)=0,
\qquad h^0(C_s,L)=d+1-g. \tag{3.2}
$$

The first equality follows because $L^{-1}\otimes\omega$ has negative degree. Coherent base change upgrades (3.2): for a family $\mathcal L$ of such bundles on $C_T$, $(f_T)_*\mathcal L$ is locally free of rank $d+1-g$ and commutes with arbitrary base change. Its projective bundle of one-dimensional spaces of sections parametrizes divisors mapping to $\mathcal L$. Thus $a_d$ is fppf-surjective and its fibers are projective spaces of dimension $d-g$.

The bound is exact for uniform vanishing. At $d=2g-2$, the canonical bundle has nonzero $H^1$, so the dimensions of spaces of sections cannot be forced to be constant over all of $\operatorname{Pic}^{2g-2}$.

### 3.2 The quotient construction

Two effective divisors $D,E$ have the same image under (3.1) exactly when $\mathcal O(D-E)$ is pulled back from the base, or, after rigidification, when their line bundles are isomorphic. This relation can be constructed without presupposing a Picard scheme. Put $Q=C^{(d)}$, let $\Delta$ be its universal divisor, and write

$$
p:C\times_SQ\longrightarrow Q,
\qquad \mathcal E=p_*\mathcal O(\Delta).
$$

For $d\geq2g-1$, $\mathcal E$ is locally free of rank $d+1-g$ and has arbitrary base change. With our convention that projective space parametrizes lines of sections, the projective bundle $\mathbf P_Q(\mathcal E)$ parametrizes a divisor $D$ together with a nonzero section of $\mathcal O(D)$ up to scalar. Taking its zero divisor gives a second map to $Q$. Thus

$$
R_d=\mathbf P_Q(\mathcal E)
\rightrightarrows Q \tag{3.3}
$$

represents pairs $(D,E)$ with isomorphic rigidified line bundles. The map $R_d\to Q\times_SQ$ is a monomorphism: once $D$ and $E$ are fixed, a section with zero divisor $E$ is unique up to scalar. It is proper, hence a closed immersion. Consequently (3.3) is a closed equivalence relation, and either projection is a projective-space bundle of relative dimension $d-g$.

It remains to explain why this particular quotient is a scheme. After an fppf base change, choose $d-g$ disjoint sections $x_1,\ldots,x_{d-g}$ of $C/S$. On the open locus where evaluation

$$
\mathcal E\longrightarrow
\bigoplus_{i=1}^{d-g}\mathcal O(\Delta)|_{x_i}
$$

is surjective, its kernel is a line. Its unique projective section selects one divisor in each complete linear system. Such opens cover $Q$: on a geometric fiber, choose the $x_i$ successively away from the base locus, lowering the dimension of the section space by one each time. The selected slices are invariant under (3.3). On overlaps, the relation gives their unique transition isomorphism, and transitivity gives the triple cocycle. Effective faithfully flat descent glues the slices to a separated finitely presented quotient representing degree-$d$ rigidified line bundles. This is the quotient construction used below; it does not assume a general theorem about arbitrary equivalence relations.

For any $m$, choose $n\geq0$ with $m+n\geq\max\{2g-1,0\}$. Tensoring by $\mathcal O(ne)$ identifies the degree-$m$ and degree-$(m+n)$ functors. Thus one high-degree construction produces every component, including the genus-zero case where a symmetric power still has nonnegative degree.

### 3.3 The representability theorem

**Relative Picard theorem.** Let $C\to S$ be a smooth proper finitely presented curve with geometrically connected fibers. Then $\operatorname{Pic}_{C/S}$ is represented by a separated $S$-scheme locally of finite presentation. There is a decomposition into open-and-closed subschemes

$$
\operatorname{Pic}_{C/S}=\coprod_{d\in\mathbf Z}\operatorname{Pic}^d_{C/S}. \tag{3.4}
$$

Each $\operatorname{Pic}^d_{C/S}$ is smooth and proper of relative dimension $g$, and formation of all these schemes commutes with arbitrary base change.

**Proof.** With a section, Sections 3.1--3.2 construct each component and identify its functor. In high degree the Abel map $q:C^{(d)}\to\operatorname{Pic}^d$ is proper and surjective. Hence $\operatorname{Pic}^d\to S$ is universally closed: after any $T\to S$, the image in $T$ of a closed subset $Z\subset\operatorname{Pic}^d_T$ equals the image of the closed subset $q_T^{-1}Z$ of the proper $T$-scheme $C_T^{(d)}$. The quotient is separated and finitely presented, so it is proper.

For a square-zero extension with ideal $I$, the exact sequence $1+I\mathcal O\to\mathcal O^\times\to\mathcal O_0^\times$ puts the obstruction to lifting a line bundle in $H^2(C_0,I\mathcal O_{C_0})$. This group vanishes because the fibers are curves. Thus the representing morphism is formally smooth, and finite presentation makes it smooth. The first-order deformation space is $H^1(C_s,\mathcal O_{C_s})$, of dimension $g$, so the relative dimension is $g$. Chapter 5 will identify these deformation spaces canonically in families.

All ingredients commute with base change: symmetric powers and universal divisors do, the vanishing (3.2) gives arbitrary coherent base change, and quotient descent is unique. This proves the claim with a section. The next section descends the result without one. $\square$

One should not infer that the whole disjoint union is of finite type over $S$: it has infinitely many degree components. It is locally of finite presentation, while every fixed component is proper and finitely presented.

### 3.4 Removing the section

The tempting shortcut is to use the fpqc cover $C\to S$. After that base change the diagonal is a section, and the two resulting Picard schemes have canonical overlap isomorphisms. Those isomorphisms do give an algebraic-space descent datum, but they do not by themselves prove that its descent is a scheme: Book 10 deliberately does not assert unrestricted effective descent for schemes. We instead choose a cover for which its finite-cover scheme criterion applies.

Work Zariski-locally on $S$. The relative multisection construction of Book 15 gives a relative effective Cartier divisor

$$
i:D\longrightarrow C
$$

whose structure map $D\to S$ is finite locally free and surjective. Briefly, one chooses a finite separable divisor on a geometric fiber, lifts its points after an étale neighborhood to disjoint sections, and descends the sum of their conjugates; shrinking the base makes the resulting divisor finite locally free of positive rank. After the finite locally free base change $D\to S$, the map

$$
D\longrightarrow C_D=C\times_SD,
\qquad x\longmapsto(i(x),x),
$$

is a section; denote it by $e_D$. Sections 3.1--3.3 therefore construct every component
$P_D^d=\operatorname{Pic}^d_{C_D/D}$ as a smooth proper $D$-scheme. The component $P_D^0$ is a smooth proper group scheme with geometrically connected fibers: over an algebraically closed field, every degree-zero divisor class is a difference of two effective divisors of one sufficiently large degree, so it lies in the image of the connected scheme $C^{(n)}\times C^{(n)}$. The complete-group projectivity theorem makes $P_D^0$ projective over $D$. Translation by $\mathcal O(de_D)$, using its dual when $d<0$, identifies $P_D^0$ with $P_D^d$. Hence every $P_D^d$ is projective, in particular finitely presented and quasi-projective, over $D$.

On $D\times_SD$, the two pullbacks of $P_D^d$ represent the same intrinsic degree-$d$ Picard sheaf and are therefore canonically isomorphic. Uniqueness gives the cocycle on $D\times_SD\times_SD$. Book 10 first descends this datum to an algebraic space. Its finite-locally-free-cover criterion then applies: the norm of any relatively ample line bundle upstairs is relatively ample on the algebraic-space descent, so that descent is a scheme. Applying the criterion separately to every $d$ gives schemes $P^d/S$; their disjoint union represents $\operatorname{Pic}_{C/S}$. The constructions on different Zariski neighborhoods agree by the same representing property and therefore glue over the original base.

The group law, degree decomposition, smoothness, properness of each component, and separatedness descend because each is a morphism, an equality of morphisms, or a property fpqc local on the base. The universal property is checked after $D\to S$ and descends by full faithfulness. This proves the theorem without a section using precisely the finite-cover effectivity result, not general scheme descent.

What need not descend is the universal line bundle on $C\times_S\operatorname{Pic}_{C/S}$. Its local versions may differ by pullbacks from the Picard factor, and their triple discrepancy is precisely a Brauer class. Representability of the Picard sheaf and existence of a Poincare bundle are distinct assertions.

## 4. Degree components and the Jacobian

### 4.1 Relative degree

For a line bundle $L$ on a smooth proper geometric fiber, degree may be defined by divisors or by Euler characteristic:

$$
\deg L=\chi(L)-\chi(\mathcal O_C). \tag{4.1}
$$

In a flat family of line bundles the Euler characteristic is locally constant. Hence a relative class over $T$ has a degree locally constant on $T$, unchanged by tensoring with a pullback from $T$. This gives a morphism of fppf sheaves

$$
\deg:\operatorname{Pic}_{C/S}\longrightarrow\mathbf Z_S, \tag{4.2}
$$

where $\mathbf Z_S$ is the constant locally constant group scheme. Its inverse image of $d$ is $\operatorname{Pic}^d_{C/S}$.

Degree is additive, $\deg(L\otimes M)=\deg L+\deg M$, and changes sign under duality. These facts follow either from divisors after a faithfully flat extension where divisors exist, or from additivity of Euler characteristic and Riemann--Roch. The latter proof also applies uniformly in families.

### 4.2 Picard components as torsors

Define

$$
J_{C/S}=\operatorname{Pic}^0_{C/S}.
$$

Tensor product gives an action

$$
J_{C/S}\times_S\operatorname{Pic}^d_{C/S}
\longrightarrow\operatorname{Pic}^d_{C/S}. \tag{4.3}
$$

**Torsor theorem.** For every integer $d$, $\operatorname{Pic}^d_{C/S}$ is an fppf torsor under $J_{C/S}$.

**Proof.** The map

$$
J\times\operatorname{Pic}^d\longrightarrow
\operatorname{Pic}^d\times\operatorname{Pic}^d,
\qquad(M,L)\longmapsto(M\otimes L,L)
$$

has inverse $(L_1,L_2)\mapsto(L_1\otimes L_2^{-1},L_2)$, so the action is simply transitive wherever the degree-$d$ component has a section. Such sections exist fppf-locally: after a smooth cover the curve has a section, and $\mathcal O(de)$ gives a line bundle of degree $d$ for $d\geq0$, with its dual for $d<0$. Thus (4.3) is a torsor. $\square$

A torsor can have no global section. Consequently $\operatorname{Pic}^d(S)$ may contain a sheaf class even when no actual degree-$d$ line bundle exists on $C$. If a degree-$d$ line bundle $L_0$ does exist, tensoring with $L_0$ identifies $J$ with $\operatorname{Pic}^d$, but the identification depends on $L_0$.

### 4.3 The identity component

The scheme $J_{C/S}$ is proper, smooth, and finitely presented with geometrically connected fibers. It is a commutative group scheme. The complete-group projectivity theorem therefore makes it an **abelian scheme** of relative dimension $g$.

Projectivity is not being inferred from the later polarization. The complete-group theorem is the foundational algebraic-group result that a smooth proper group scheme with geometrically connected fibers over a locally noetherian base is projective locally on the base. It is proved by the cubical-line-bundle construction and faithfully flat descent, independently of Jacobian autoduality, so it applies before theta or the dual abelian scheme is introduced.

Connectedness deserves proof. Over an algebraically closed field, every degree-zero divisor class can be written as

$$
(p_1+\cdots+p_n)-(q_1+\cdots+q_n)
$$

for $n$ large. Hence it lies in the image of the connected variety $C^{(n)}\times C^{(n)}$ under subtraction. The image contains the identity and all geometric points of $\operatorname{Pic}^0$, so the latter is connected. Geometric connectedness then descends and persists in families.

The notation $\operatorname{Pic}^0$ has two compatible meanings in the smooth case: the kernel of degree and the identity component. They diverge for reducible nodal curves, where total degree zero allows nonzero multidegrees on components. Chapter 12 will keep them separate.

### 4.4 Genus zero and genus one

If $g=0$, the Jacobian has relative dimension zero and geometrically connected fibers. A smooth proper dimension-zero connected group over a field is a point, so $J\simeq S$. Degree components can nevertheless encode descent: for a nonsplit conic, $\operatorname{Pic}^1$ is a trivial torsor as a sheaf scheme, while its distinguished sheaf point need not come from a line bundle on the conic because of (2.2).

If $g=1$ and a section $e$ is chosen, the Abel map

$$
C\longrightarrow J,
\qquad p\longmapsto\mathcal O(p-e)
$$

is an isomorphism. On each geometric fiber it is a nonconstant map between smooth proper genus-one curves sending $e$ to zero. A degree-zero bundle $\mathcal O(p-e)$ determines $p$, so the map is injective on geometric points. Its cotangent map at $p$ is the evaluation map

$$
H^0(C,\omega_C)\longrightarrow\omega_C|_p.
$$

The description follows by moving a local equation of the point to first order and pairing the resulting principal part with a differential. Both sides are one-dimensional, and a nonzero differential on a genus-one curve has canonical divisor of degree zero and hence vanishes nowhere. The cotangent map is therefore an isomorphism, excluding a hidden purely inseparable degree. The Abel map has degree one. A proper morphism that is an isomorphism on every geometric fiber is an isomorphism. Thus a pointed genus-one curve obtains its group law from its Jacobian. An unpointed genus-one curve is instead a torsor under its Jacobian.

## 5. Infinitesimal geometry

### 5.1 Lifting line bundles

The geometry of the Picard scheme is governed by the simplest coherent sheaf on the curve. Let $T_0\hookrightarrow T$ be a square-zero closed immersion with ideal $I$, and put $C_0=C_T\times_TT_0$. There is an exact sequence of sheaves of abelian groups

$$
1\longrightarrow1+I\mathcal O_{C_0}
\longrightarrow\mathcal O_{C_T}^{\times}
\longrightarrow\mathcal O_{C_0}^{\times}
\longrightarrow1. \tag{5.1}
$$

Because $I^2=0$, multiplication identifies $1+I\mathcal O_{C_0}$ with the additive sheaf $I\mathcal O_{C_0}$. The cohomology sequence says:

- the obstruction to lifting a line bundle from $C_0$ to $C_T$ lies in $H^2(C_0,I\mathcal O_{C_0})$;
- if a lift exists, its isomorphism classes form a torsor under $H^1(C_0,I\mathcal O_{C_0})$;
- automorphisms inducing the identity below lie in $H^0(C_0,I\mathcal O_{C_0})$.

For a curve, coherent $H^2$ vanishes. Thus every line bundle lifts locally on $T$. Rigidification along $e$ removes the scalar part of the automorphism group. This is the deformation-theoretic source of smoothness.

### 5.2 Tangent and cotangent spaces

Take $T=\operatorname{Spec}k[\epsilon]/(\epsilon^2)$ and $T_0=\operatorname{Spec}k$. A deformation of the trivial bundle is represented on an open cover by transition functions

$$
1+\epsilon a_{ij}.
$$

The cocycle relation is $a_{ij}+a_{jk}+a_{ki}=0$, and changing trivializations by $1+\epsilon b_i$ changes $(a_{ij})$ by a coboundary. Therefore

$$
T_0J_{C/k}\simeq H^1(C,\mathcal O_C). \tag{5.2}
$$

Relatively, the Lie bundle is

$$
\operatorname{Lie}(J/S)\simeq R^1f_*\mathcal O_C. \tag{5.3}
$$

Duality gives the cotangent bundle at the identity:

$$
\omega_J:=0_J^*\Omega^1_{J/S}
\simeq f_*\omega_{C/S}. \tag{5.4}
$$

Both identifications commute with arbitrary base change. Formula (5.4) is one of the most useful bridges in the theory: invariant differentials on the Jacobian are exactly regular differentials on the curve.

### 5.3 Smoothness and dimension

**Smoothness theorem.** Every $\operatorname{Pic}^d_{C/S}\to S$ is smooth of relative dimension $g$.

**Proof.** The obstruction group in Section 5.1 vanishes for every square-zero extension, so the functor has the infinitesimal lifting property. The representing morphism is finitely presented, hence formally smooth implies smooth. Its relative tangent space is $H^1(C_s,\mathcal O_{C_s})$, of dimension $g$ on every geometric fiber. Smooth morphisms have relative dimension equal to tangent dimension, giving the claim. Translation by a local degree-$d$ point carries the calculation from $J$ to $\operatorname{Pic}^d$. $\square$

For singular proper curves, the same $H^2$ argument gives formal smoothness once the Picard functor is represented and locally of finite presentation. For a nodal curve, properness can fail because gluing parameters contribute a torus. A nonreduced curve can contribute a unipotent affine part and can destroy cohomological flatness in a relative family. Thus $H^2=0$ controls infinitesimal lifting, but by itself does not supply representability, separatedness, properness, or base-change control.

### 5.4 The formal group at the identity

Let $T_0=\operatorname{Spec}A\to S$, and let $T=\operatorname{Spec}A'\to S$ be a square-zero thickening, so that $A'\twoheadrightarrow A$ has kernel $I$. The kernel of

$$
J(T)\longrightarrow J(T_0)
$$

over the identity point is canonically

$$
H^1(C_{T_0},\mathcal O_{C_{T_0}})\otimes_A I. \tag{5.5}
$$

The group law is addition to first order because

$$
(1+a)(1+b)=1+(a+b)
$$

when $ab=0$. For higher nilpotent thickenings, successive square-zero quotients filter the formal completion $\widehat J_0$ with graded pieces controlled by $R^1f_*\mathcal O_C$. This does not make the formal group globally additive: higher terms depend on the curve and, in positive characteristic, encode subtle height phenomena. The safe conclusion is the canonical first-order identification (5.3), not a choice of global formal coordinates.

## 6. Universal line bundles and the see-saw principle

### 6.1 The Poincare bundle

Assume that $e:S\to C$ is fixed. Since the rigidified Picard functor is represented, the identity map of $\operatorname{Pic}_{C/S}$ corresponds to a universal rigidified line bundle

$$
\mathcal P_C
\quad\text{on}\quad
C\times_S\operatorname{Pic}_{C/S}, \tag{6.1}
$$

normalized by

$$
\mathcal P_C|_{e\times\operatorname{Pic}}\simeq\mathcal O_{\operatorname{Pic}}.
$$

Its restriction to $C\times J$ is also called the Poincare bundle. For every $T\to S$ and every $x:T\to\operatorname{Pic}_{C/S}$, the pullback $(1_C,x)^*\mathcal P_C$ is the rigidified line bundle represented by $x$.

The normalization makes $\mathcal P_C$ unique, not merely unique up to a line bundle from the Picard factor. Indeed two universal bundles differ by such a pullback, and restriction along $e$ trivializes the difference. Every base change of $\mathcal P_C$ has the same universal and normalization properties, so uniqueness identifies it with the Poincare bundle of the base-changed curve.

Without $e$, local Poincare bundles exist after the fpqc cover $C\to S$, but their discrepancy can define a nonzero Brauer class on the Picard scheme. Statements using an actual universal bundle will therefore either assume a rigidifying section or be formulated after a faithfully flat cover and descended intrinsically.

### 6.2 The see-saw principle

Universal bundles are useful because a line bundle on a product is often determined by its restrictions to the two directions.

**See-saw principle.** Let $X\to S$ be proper and flat with geometrically connected reduced fibers and a section $e$, and let $Y\to S$ be any scheme. Suppose the class of a line bundle $\mathcal L$ on $X\times_SY$ is the zero section of $\operatorname{Pic}_{X/S}(Y)$. Equivalently, it is pulled back from $Y$ after an fppf cover of $Y$. Then there is a unique isomorphism

$$
\mathcal L\simeq p_Y^*(e\times1_Y)^*\mathcal L. \tag{6.2}
$$

**Proof.** On an fppf cover $Y'\to Y$, the hypothesis gives $\mathcal L|_{X\times Y'}\simeq p_{Y'}^*\mathcal M'$. Restriction along $e\times Y'$ identifies $\mathcal M'$ with $(e\times1)^*\mathcal L|_{Y'}$. After this identification, the isomorphism is rigidified along $e$. Any two such rigidified isomorphisms differ by a global unit on $X\times Y'$ equal to one along $e$; universal equality $(p_{Y'})_*\mathcal O=\mathcal O_{Y'}$ makes that unit one. The local isomorphisms therefore agree on double overlaps and descend uniquely. $\square$

If $S$ is a field and $Y$ is reduced, it is enough to assume triviality on every geometric fiber $X_y$: the classifying morphism $Y\to\operatorname{Pic}_{X/S}$ then agrees with the zero morphism on all geometric points, and reducedness plus separatedness makes the two morphisms equal. This fiberwise criterion is false for nonreduced $Y$; a nonzero tangent vector of the Picard scheme gives a line bundle over the dual numbers that is trivial on its only geometric fiber but not pulled back from the dual-number base.

A symmetric version says that a line bundle on $X\times_SY$ trivial on $e\times Y$ and $X\times y_0$ is determined by the induced morphism $Y\to J_X$. This is the mechanism behind biextensions and Albanese factorization.

### 6.3 Biextension identities

Let $m:J\times_SJ\to J$ be addition and $p_1,p_2$ the projections. Universality and tensor product give a canonical isomorphism on $C\times J\times J$:

$$
(1_C\times m)^*\mathcal P_C
\simeq
(1_C\times p_1)^*\mathcal P_C
\otimes
(1_C\times p_2)^*\mathcal P_C. \tag{6.3}
$$

Both sides represent the tensor product of the two universal degree-zero classes and have the same rigidification. Associativity of (6.3) follows from uniqueness. Similarly, pullback by inversion on $J$ changes $\mathcal P_C$ to its dual.

These identities express that $\mathcal P_C$ is linear in the Picard variable. The Poincare bundle on $J\times_SJ^\vee$ is linear in both group variables and is a biextension; its pullback along $j_e\times1$ is $\mathcal P_C|_{C\times J}$. After the canonical identification $J\simeq J^\vee$, this gives a biextension on $J\times J$, not a group law on the curve variable. The word records genuine coherence: the two distributive structures agree on fourfold products because normalized universal line bundles with the same fiberwise interpretation are uniquely isomorphic.

## 7. Abel maps

### 7.1 The pointed Abel--Jacobi map

A section $e$ permits a point to be compared with the origin. The diagonal $\Delta\subset C\times_SC$ and the divisor $e\times C$ define the line bundle

$$
\mathcal O_{C\times C}(\Delta-e\times C),
$$

rigidified along $e$ after tensoring by a line bundle from the second factor. Its class gives the **Abel--Jacobi map**

$$
j_e:C\longrightarrow J,
\qquad p\longmapsto\mathcal O_C(p-e). \tag{7.1}
$$

It sends $e$ to $0$. Changing the base point from $e$ to $e'$ translates the map by the constant class $\mathcal O(e-e')$:

$$
j_{e'}(p)=j_e(p)+[\mathcal O(e-e')]. \tag{7.2}
$$

Thus the embedded curve depends on the base point by translation, while induced homomorphisms and the canonical polarization will not.

### 7.2 Higher Abel maps and their fibers

For $d\geq0$, the universal divisor gives

$$
a_d:C^{(d)}\longrightarrow\operatorname{Pic}^d_{C/S},
\qquad D\longmapsto\mathcal O(D). \tag{7.3}
$$

After translating by $\mathcal O(-de)$ one obtains

$$
j_e^{(d)}:C^{(d)}\longrightarrow J,
\qquad D\longmapsto\mathcal O(D-de). \tag{7.4}
$$

For a geometric point $[L]\in\operatorname{Pic}^d$, the fiber is the complete linear system

$$
a_d^{-1}([L])=\mathbf P(H^0(C,L)), \tag{7.5}
$$

where the chosen projective-space convention parametrizes one-dimensional subspaces. It is empty if $L$ has no nonzero section. For $d\geq2g-1$, it has constant dimension $d-g$ and varies as a projective bundle after a local universal bundle is chosen.

For $d=g$, Riemann--Roch says every degree-$g$ line bundle has a section, so $a_g$ is surjective. Its generic fiber has dimension zero because a generic degree-$g$ line bundle has exactly one section. Thus $C^{(g)}\to\operatorname{Pic}^g$ is generically birational on every geometric fiber. At special bundles with $h^0>1$, the fiber expands; this is why the Abel map is not generally an isomorphism.

### 7.3 Differentials of Abel maps

Let $D$ be an effective divisor on a smooth fiber $C/k$. First-order motions of $D$ are

$$
T_DC^{(d)}\simeq H^0(D,\mathcal O_D(D)). \tag{7.6}
$$

From

$$
0\longrightarrow\mathcal O_C
\longrightarrow\mathcal O_C(D)
\longrightarrow\mathcal O_D(D)
\longrightarrow0
$$

one obtains a connecting map

$$
\delta_D:H^0(D,\mathcal O_D(D))
\longrightarrow H^1(C,\mathcal O_C). \tag{7.7}
$$

**Differential theorem.** Under (5.2) and (7.6), $d a_d$ is $\delta_D$. Under Serre duality its transpose is restriction

$$
H^0(C,\omega_C)\longrightarrow H^0(D,\omega_C|_D). \tag{7.8}
$$

**Proof.** Move a local equation $t$ of $D$ to $t+\epsilon u$. The ratio of the old and new local generators is $1+\epsilon(u/t)$ on a punctured neighborhood. These ratios form the Cech cocycle defining the boundary in (7.7), hence the infinitesimal line-bundle class. Pairing $u/t$ with a regular differential and taking residues evaluates the differential on the principal part; this is exactly restriction to $D$. $\square$

For $d=1$, (7.8) says that pullback by $j_e$ identifies invariant differentials on $J$ with differentials on $C$:

$$
j_e^*:H^0(J,\Omega^1_{J/k})
\xrightarrow{\sim}H^0(C,\omega_C). \tag{7.9}
$$

Relatively, adjunction gives a map

$$
j_e^*:\omega_J\longrightarrow f_*\omega_{C/S},
$$

and it is the identity under (5.4). Equivalently, $f^*\omega_J\to\Omega^1_{C/S}$ is the differential of $j_e$.

### 7.4 Generation of the Jacobian

**Generation theorem.** The smallest closed subgroup scheme of $J$ containing $j_e(C)$ is $J$.

**Proof.** It is enough to check after geometric base change. Every degree-zero divisor class can be represented as $D-ne$ with $D$ effective of degree $n$ for sufficiently large $n$: choose a divisor representative $E$, then add a sufficiently large multiple of $e$ so that Riemann--Roch gives a section of $\mathcal O(E+ne)$. Therefore every geometric point of $J$ is a sum of points $j_e(p_i)$. A closed subgroup containing the curve contains all such sums, hence all geometric points of $J$; since $J$ is reduced, it is all of $J$. $\square$

This theorem is the uniqueness engine for Albanese maps and for identities between homomorphisms of Jacobians: it suffices to verify them after precomposition with $j_e$.

## 8. Theta divisors and the canonical polarization

### 8.1 Why a divisor should yield duality

The Jacobian parametrizes line bundles on $C$. Its dual abelian scheme $J^\vee$ parametrizes algebraically trivial line bundles on $J$. To compare the two, one needs a construction that turns a degree-zero bundle on $C$ into an algebraically trivial bundle on $J$. The locus of degree $g-1$ bundles possessing a section does exactly this. Tensoring a variable bundle by a fixed degree-zero class moves that locus, and the difference between the moved and original divisor defines a point of $J^\vee$.

Over an algebraically closed field, let

$$
W_{g-1}=\{[L]\in\operatorname{Pic}^{g-1}(C):H^0(C,L)\ne0\}. \tag{8.1}
$$

It is the image of $a_{g-1}:C^{(g-1)}\to\operatorname{Pic}^{g-1}$. The source has dimension $g-1$, the target has dimension $g$, and a generic degree-$(g-1)$ effective divisor has a unique section. Thus the image should be a divisor. Merely taking the set-theoretic image is inadequate in a family; the determinant of cohomology supplies the correct scheme structure and base-change behavior.

For $g=0$, $J$ is trivial and its unique polarization is principal. In Sections 8.2--8.5 assume $g\geq1$.

### 8.2 Construction by determinant of cohomology

Assume first that $e$ is fixed, so a universal bundle $\mathcal U$ exists on

$$
C\times_S\operatorname{Pic}^{g-1}_{C/S}.
$$

Let $p$ denote projection to $\operatorname{Pic}^{g-1}$. Locally on the base, $Rp_*\mathcal U$ is represented by a two-term complex of vector bundles

$$
E^0\xrightarrow{d}E^1. \tag{8.2}
$$

Riemann--Roch gives Euler characteristic zero, so $E^0$ and $E^1$ have the same rank after adding a common trivial summand. The determinant

$$
\det(d)\in
\Gamma\bigl(\operatorname{Pic}^{g-1},
(\det E^0)^{-1}\otimes\det E^1\bigr) \tag{8.3}
$$

has zero locus exactly where (8.2) has cohomology, equivalently where $H^0(C_s,L)\ne0$; by duality this is also where $H^1(C_s,L)\ne0$. Changing the two-term model multiplies (8.3) by a unit and canonically identifies its determinant line. Thus the local zero loci glue to an effective Cartier divisor $\Theta\subset\operatorname{Pic}^{g-1}$.

The determinant is not identically zero on a geometric fiber. Indeed the section locus is the proper image of $C^{(g-1)}$, of dimension $g-1$, inside the $g$-dimensional variety $\operatorname{Pic}^{g-1}$. It cannot fill that variety. Consequently some degree-$(g-1)$ line bundle has no section. The determinant is therefore a non-zero-divisor on every smooth fiber; flatness and the local criterion for a relative effective Cartier divisor show that (8.3) defines a relative Cartier divisor.

Its geometric points are exactly (8.1), with determinantal multiplicity. Translation by $\mathcal O(-(g-1)e)$ identifies $\operatorname{Pic}^{g-1}$ with $J$ and carries $\Theta$ to a divisor $\Theta_e$ on $J$. Different choices of the universal bundle twist the determinant line by a pullback from the parameter space in a way that does not alter the associated homomorphism constructed next.

### 8.3 The homomorphism attached to theta

For a line bundle $M$ on an abelian scheme $A/S$, define

$$
\phi_M:A\longrightarrow A^\vee,
\qquad
x\longmapsto t_x^*M\otimes M^{-1}. \tag{8.4}
$$

Here $t_x(y)=y+x$. This convention matters for the sign in the Albanese formula below.

The theorem of the square gives

$$
t_{x+y}^*M\otimes M^{-1}
\simeq
(t_x^*M\otimes M^{-1})\otimes
(t_y^*M\otimes M^{-1}),
$$

after the corresponding bundles are interpreted universally on $A\times A$. Thus $\phi_M$ is a homomorphism. Tensoring $M$ by a line bundle algebraically equivalent to zero does not change $\phi_M$, and translating $M$ does not change it either: the extra translation factors cancel by the square identity.

Take $A=J$ and $M=\mathcal O_J(\Theta_e)$. The resulting map

$$
\lambda_C=\phi_{\mathcal O(\Theta_e)}:J\longrightarrow J^\vee \tag{8.5}
$$

will be shown in the next section to be a principal polarization. At this stage it is a homomorphism; ampleness and principality are conclusions, not inputs.

There is a useful formula for the family of bundles represented by $\lambda_C$. If $x\in J(T)$ corresponds to a rigidified degree-zero bundle $L_x$ on $C_T$, then $\lambda_C(x)$ is the algebraically trivial bundle on $J_T$ obtained by comparing the determinants of cohomology of $\mathcal U\otimes L_x$ and $\mathcal U$. This determinant description shows directly that (8.5) commutes with arbitrary base change.

### 8.4 Principality

The crucial assertion is stronger than ampleness.

**Principal polarization theorem.** The homomorphism $\lambda_C:J\to J^\vee$ is an isomorphism.

**Proof.** It suffices to work on a geometric fiber, because a homomorphism of abelian schemes that is an isomorphism on every geometric fiber is an isomorphism. We first establish the intersection calculation that also proves ampleness.

Let $k$ be algebraically closed, put $W_d=a_d(C^{(d)})$, and translate $W_d$ to $J$. The determinantal construction of Section 8.2 gives the **Poincare cycle formula**

$$
[W_d]=\frac{c_1(\mathcal O(\Theta))^{g-d}}{(g-d)!},
\qquad 0\leq d\leq g-1. \tag{8.6}
$$

Here is the intersection calculation, including its multiplicities. Choose an effective divisor $E$ of degree $N\gg0$ and a normalized universal line bundle $\mathcal L$ on $C\times\operatorname{Pic}^d$. The exact sequence for $E$ gives a map of vector bundles

$$
p_*\mathcal L(E)\longrightarrow p_*(\mathcal L(E)|_E) \tag{8.7}
$$

of ranks $N+d+1-g$ and $N$. Its kernel at $[L]$ is $H^0(C,L)$. Thus $W_d$, with the Abel-image scheme structure, is the locus where (8.7) has rank at most $N+d-g$. Its expected codimension is $g-d$, and it has that codimension because $C^{(d)}\to W_d$ is generically one-to-one: a general effective divisor of degree $d\leq g-1$ has only its canonical section.

The maximal-minor resolution of (8.7) now computes its cycle as the degree-$(g-d)$ Chern class of the virtual bundle

$$
p_*(\mathcal L(E)|_E)-p_*\mathcal L(E).
$$

Its $K$-class is $-Rp_*\mathcal L$, independently of $E$. The curve case of Riemann--Roch computes its Chern character explicitly. Write the first Chern class of the normalized universal bundle as $d\eta+\xi$, where $\eta$ is the class of a point on $C$ and $\xi$ has one degree in the curve direction and one in the Picard direction. In

$$
\operatorname{ch}(Rp_*\mathcal L)
=p_*\bigl(\exp(d\eta+\xi)\operatorname{td}(C)\bigr),
$$

In relative dimension one the displayed identity follows directly by resolving $\mathcal L(E)$ and $\mathcal L(E)|_E$ into finite locally free sheaves, applying additivity of the Chern character to their divisor exact sequence, and then splitting the finite divisor $E$; no higher-dimensional Riemann--Roch input is hidden here. Only $d\eta$, the degree-one term $(1-g)\eta$ of $\operatorname{td}(C)$, and $\xi^2/2$ have curve degree two. The first two give the rank $d+1-g$. Contraction of $\xi^2/2$ by the Serre-duality pairing is $-c_1(\Theta)$; this sign also follows from the determinant line $(\det E^0)^{-1}\det E^1=\mathcal O(\Theta)$. All higher Chern-character terms vanish. Hence for $V=-Rp_*\mathcal L$,

$$
\operatorname{ch}(V)=g-d-1+c_1(\Theta),
\qquad c(V)=\exp(c_1(\Theta)).
$$

Therefore $c_r(V)=c_1(\Theta)^r/r!$. Taking $r=g-d$ proves (8.6). The calculation is an identity of determinantal cycles, so it retains diagonal and inseparable lengths and is valid in every characteristic.

At $d=0$, $W_0$ is the reduced origin, so (8.6) gives

$$
c_1(\mathcal O(\Theta))^g=g![0]. \tag{8.8}
$$

An effective divisor on an abelian variety is nef: translate it so that it does not contain a given curve, and its intersection with that curve is nonnegative. A nef line bundle on an abelian variety has positive top self-intersection exactly when its translation stabilizer is finite. Indeed, a positive-dimensional connected stabilizer makes the numerical class descend to a quotient of smaller dimension and forces the top power to vanish; conversely the kernel of the associated homomorphism is the stabilizer scheme. The abelian Nakai criterion now says that a nef class with finite stabilizer is ample: after quotienting by the connected stabilizer the descended class is ample, and a finite stabilizer leaves the quotient dimension unchanged. Thus (8.8) makes $\mathcal O(\Theta)$ ample and $\lambda_C$ an isogeny.

We use the following numerical identity for an ample line bundle $M$ on a $g$-dimensional abelian variety:

$$
\operatorname{length}\ker(\phi_M)
=\left(\frac{c_1(M)^g}{g!}\right)^2
=\chi(M)^2. \tag{8.9}
$$

For clarity, this identity is scheme-theoretic. The theorem of the cube gives $[n]^*M\equiv M^{\otimes n^2}$. Applying the intersection form to the graph of $\phi_M$ and the zero section computes their intersection as the square of $c_1(M)^g/g!$; that intersection is the full finite group-scheme kernel, with local intersection length at infinitesimal points. Riemann--Roch identifies $c_1(M)^g/g!$ with $\chi(M)$. Thus (8.9) counts inseparable and nonreduced kernel structure as well as geometric points.

For $M=\mathcal O(\Theta)$, (8.8) and Riemann--Roch give $\chi(M)=1$. Formula (8.9) gives a finite flat kernel of rank one, so the kernel is trivial and $\lambda_C$ is an isomorphism. Fiberwise ampleness of the theta line is relative ampleness over $S$, so this is a principal polarization in families. $\square$

This proof uses scheme-theoretic lengths, so it does not fail when the characteristic divides an integer occurring in a multiplication map. A bijection on geometric points alone would not exclude an infinitesimal kernel.

### 8.5 Independence of choices and base change

Changing $e$ translates $\Theta_e$. Changing the universal line bundle tensors the theta line by an algebraically trivial line bundle and a base pullback. Each operation leaves $\phi_M$ unchanged. Hence $\lambda_C$ is independent of the base point and of every auxiliary normalization. It descends from an fpqc cover on which $C$ has a section, giving a canonical map even for an unpointed curve.

The determinant construction, translation, and dual abelian scheme all commute with arbitrary base change. Therefore

$$
\lambda_{C_{S'}/S'}=\lambda_{C/S}\times_SS' \tag{8.10}
$$

for every $S'\to S$. The Jacobian is canonically self-dual through $\lambda_C$. The adjective **canonical** refers to the homomorphism, not to a uniquely chosen symmetric theta divisor: theta divisors can differ by translation, especially before a theta characteristic is chosen.

The sign relating this self-duality to the chosen Abel map is also canonical. Pullback of algebraically trivial line bundles along $j_e$ gives $j_e^*:J^\vee\to J$, and

$$
j_e^*\circ\lambda_C=[-1]_J. \tag{8.11}
$$

To verify (8.11), let $x$ be represented by a normalized degree-zero line bundle $L_x$ on $C$. Restrict to $C\times J$ the determinant comparison defining $t_x^*\mathcal O(\Theta)\otimes\mathcal O(\Theta)^{-1}$. The exact sequence for adding the moving point $p$ identifies the resulting normalized bundle on $C$ with $L_x^{-1}$. The comparison is functorial in $x$, so see-saw upgrades the fiber calculation to an identity of the two homomorphisms. In genus one, $t_x^{-1}(e)=-x$, so the divisor difference $(-x)-(e)$ represents the inverse of $x-e$; this visible case confirms the sign.

## 9. The Albanese property

### 9.1 Pointed maps to abelian schemes

The Picard property classifies line bundles on $C$. The Albanese property classifies maps from $C$ into abelian schemes. A priori these are opposite kinds of universal problem. The canonical self-duality of $J$ joins them.

Let $A/S$ be an abelian scheme and let $u:C\to A$ satisfy $u\circ e=0_A$. Pullback of rigidified algebraically trivial line bundles gives a homomorphism

$$
u^*:A^\vee\longrightarrow J. \tag{9.1}
$$

Dualize and use the bidual isomorphism $A\simeq A^{\vee\vee}$ and the principal polarization of $J$ to define

$$
u_*=-\,(u^*)^\vee\circ\lambda_C:J\longrightarrow A. \tag{9.2}
$$

The direction and sign are worth checking. Pullback is contravariant on Picard varieties, duality reverses it again, and $\lambda_C$ changes $J$ into $J^\vee$. The minus sign is forced by (8.11) for the convention $j_e(p)=\mathcal O(p-e)$.

### 9.2 Existence and uniqueness of factorization

**Albanese theorem.** For every pointed morphism $u:(C,e)\to(A,0)$ there is a unique homomorphism of abelian schemes $\widetilde u:J\to A$ such that

$$
u=\widetilde u\circ j_e. \tag{9.3}
$$

It is the homomorphism (9.2), and its formation commutes with base change.

**Proof.** Pull the Poincare bundle of $A\times A^\vee$ back along $u\times1$. By definition it is the family of degree-zero bundles on $C$ classified by $u^*:A^\vee\to J$. A polarization homomorphism is symmetric under biduality, so dualizing (9.2) gives

$$
u_*^*=-\lambda_C\circ u^*:A^\vee\longrightarrow J^\vee.
$$

After pullback along $j_e$, (8.11) gives

$$
j_e^*u_*^*=-(j_e^*\lambda_C)u^*=u^*.
$$

Thus $u$ and $u_*\circ j_e$ induce the same normalized family of line bundles parametrized by $A^\vee$. The see-saw principle identifies those families, and the bidual map $A\to A^{\vee\vee}$ is an isomorphism, so the two morphisms to $A$ are equal. This proves existence.

If $v,w:J\to A$ both satisfy (9.3), then $v-w$ vanishes on $j_e(C)$. It vanishes on the closed subgroup generated by that image, which is all of $J$ by Section 7.4. Thus $v=w$. Every construction used in (9.2) is compatible with base change, proving the last assertion. $\square$

Two immediate consequences clarify the roles of pullback and norm. First, the map on invariant differentials induced by $\widetilde u$ is the unique map whose pullback along $j_e$ equals $u^*$. Second, any identity between homomorphisms out of $J$ can be checked on the curve, where it often reduces to a divisor calculation.

### 9.3 The unpointed Albanese torsor

Without a section there is no canonical map $C\to J$ sending a chosen point to zero. There is instead a canonical map to the degree-one Picard torsor:

$$
a_1:C\longrightarrow\operatorname{Pic}^1_{C/S},
\qquad p\longmapsto\mathcal O(p), \tag{9.4}
$$

understood as an fppf relative class when a universal divisor is available only locally. Via the principal polarization, $\operatorname{Pic}^1$ is the Albanese torsor $\operatorname{Alb}^1_{C/S}$ under $J$.

Its universal property is affine rather than pointed: if $P$ is a torsor under an abelian scheme $A$ and $u:C\to P$ is a morphism, there is a unique pair consisting of a homomorphism $J\to A$ and an equivariant map $\operatorname{Pic}^1\to P$ through which $u$ factors. After an fppf cover choose points on $C$ and $P$; the pointed Albanese theorem constructs the factorization. Changing the chosen points translates both torsors by matching amounts, so uniqueness glues it. This formulation separates the absence of a rational point from the existence of the Jacobian itself.

## 10. Finite maps, pullback, and norm

### 10.1 Pullback on Picard schemes

Let

$$
h:C\longrightarrow D
$$

be an $S$-morphism between smooth proper curves. Pullback of line bundles defines

$$
h^*:\operatorname{Pic}_{D/S}\longrightarrow\operatorname{Pic}_{C/S}. \tag{10.1}
$$

It respects tensor products and arbitrary base change. If $h$ is finite locally free of constant degree $n$, then

$$
\deg(h^*L)=n\deg L, \tag{10.2}
$$

so (10.1) restricts to $h^*:J_D\to J_C$.

Under the standing smooth-family hypotheses, every finite $S$-morphism $h:C\to D$ is finite locally free. Affine-locally on $D$, write $B\to M$ for the finite algebra $h_*\mathcal O_C$. Both $B$ and $M$ are flat over the base because $D/S$ and $C/S$ are smooth. On every geometric fiber, $M_s$ is the finite algebra of a nonconstant finite map between smooth curves; it is torsion-free over each discrete valuation ring of $D_s$ and hence flat. The fiberwise flatness criterion makes $M$ flat over $B$. Being finite and finitely presented, it is locally free, with rank locally constant on $S$. Thus the finite locally free theory below covers every finite map between the smooth relative curves of this book.

Mere fiberwise finiteness of a morphism not already known to be finite is insufficient in a broader family, so finite local freeness must then be verified separately. Constant maps do not induce the degree formula (10.2), though ordinary pullback still exists.

### 10.2 The norm of a line bundle

Pullback is contravariant. A finite locally free map also has a covariant operation. For a line bundle $L$ on $C_T$, define

$$
\operatorname{Nm}_h(L)
=\det(h_*L)\otimes\det(h_*\mathcal O_C)^{-1}. \tag{10.3}
$$

Since $h$ has rank $n$, both direct images in (10.3) are locally free of rank $n$. The determinant quotient is a line bundle on $D_T$. If $L=h^*M$, the projection formula gives

$$
h_*h^*M\simeq h_*\mathcal O_C\otimes M,
$$

and therefore

$$
\operatorname{Nm}_h(h^*M)\simeq M^{\otimes n}. \tag{10.4}
$$

The definition appears not to be multiplicative because determinants of tensor products of arbitrary $h_*L$ do not directly compare. Multiplicativity is local on $D$ and may be checked where $h$ is the spectrum of a finite free algebra $B/A$ and $L$ is generated by one element after a faithfully flat cover. Transition functions $b\in B^\times$ act on $B$ by multiplication, and their determinants are the algebra norm $N_{B/A}(b)$. Since $N(bb')=N(b)N(b')$, the transition functions for (10.3) multiply. Descent yields canonical isomorphisms

$$
\operatorname{Nm}_h(L\otimes L')
\simeq\operatorname{Nm}_h(L)\otimes\operatorname{Nm}_h(L'). \tag{10.5}
$$

Thus norm defines a homomorphism

$$
h_*:=\operatorname{Nm}_h:\operatorname{Pic}_{C/S}
\longrightarrow\operatorname{Pic}_{D/S}. \tag{10.6}
$$

For a relative Cartier divisor $E$ finite over $D$, local equations show

$$
\operatorname{Nm}_h\mathcal O_C(E)
\simeq\mathcal O_D(h_*E), \tag{10.7}
$$

where residue degrees and scheme-theoretic multiplicities occur in the pushforward divisor.

### 10.3 Degree and composition formulas

The norm satisfies four structural identities:

$$
\deg\operatorname{Nm}_h(L)=\deg L, \tag{10.8}
$$

$$
\operatorname{Nm}_h\circ h^*=[n], \tag{10.9}
$$

$$
\operatorname{Nm}_{k\circ h}
=\operatorname{Nm}_k\circ\operatorname{Nm}_h, \tag{10.10}
$$

and norm commutes with arbitrary base change. Formula (10.8) follows from (10.7) after representing a line bundle by a difference of divisors fppf-locally; pushforward preserves total degree. Formula (10.9) is (10.4). For (10.10), determinants in a tower can be checked on transition units, where it is transitivity of the algebra norm. The same local description proves base change because determinants of finite locally free modules commute with tensor product.

Consequently norm restricts to $h_*:J_C\to J_D$. If $h$ is separable or ramified, no alteration is needed. If it is purely inseparable in characteristic $p$, the norm remains valid while the differential trace may vanish; a proof based only on tangent spaces would therefore miss information. The determinant definition handles all finite locally free maps uniformly.

### 10.4 Adjointness under the canonical polarization

Pullback and norm are adjoint with respect to the canonical polarizations:

$$
(h^*)^\vee\circ\lambda_C
=\lambda_D\circ h_*. \tag{10.11}
$$

Equivalently,

$$
h_*=\lambda_D^{-1}(h^*)^\vee\lambda_C. \tag{10.12}
$$

**Proof.** Both sides of (10.11) are maps $J_C\to J_D^\vee$. Evaluate their universal line bundles on $J_C\times J_D$. The left side pulls the Poincare bundle back through $h^*$ in the $J_D$ variable; on curve representatives this replaces a bundle $M$ on $D$ by $h^*M$. The right side first norms a bundle $L$ on $C$ and pairs it with $M$. The determinant projection formula gives the canonical equality

$$
\langle h^*M,L\rangle_C
=\langle M,\operatorname{Nm}_hL\rangle_D, \tag{10.13}
$$

for the determinant-of-cohomology pairing defining theta. Explicitly, for two degree-zero families $L_1,L_2$ on the same curve it is the normalized line

$$
\langle L_1,L_2\rangle=
\det Rf_*(L_1\otimes L_2)\otimes
(\det Rf_*L_1)^{-1}\otimes
(\det Rf_*L_2)^{-1}\otimes
\det Rf_*\mathcal O.
$$

The projection formula for $h_*$ and transitivity of determinant identify the two displayed pairings, including their rigidifications. The normalizations agree at the identity, so see-saw upgrades this equality to an isomorphism of universal bundles. Hence the homomorphisms agree. $\square$

On cotangent spaces, (10.11) is the familiar adjunction between pullback of differentials and trace. The group-scheme identity is stronger and remains meaningful when the differential trace is degenerate.

## 11. Correspondences

### 11.1 From spans of curves to homomorphisms

A map of curves gives pullback in one direction and norm in the other. A correspondence combines the two. Let $C,D,Z$ be smooth proper relative curves and suppose

$$
C\xleftarrow{\alpha}Z\xrightarrow{\beta}D \tag{11.1}
$$

has finite locally free arrows. Its action on Jacobians is

$$
T_Z=\beta_*\alpha^*:J_C\longrightarrow J_D. \tag{11.2}
$$

This convention is covariant in the right arrow and contravariant in the left. On a divisor class $[E]$ it is

$$
[E]\longmapsto[\beta_*\alpha^*E]. \tag{11.3}
$$

Residue-field degrees and ramification multiplicities are included in pullback and pushforward. Formula (11.3) may be checked after a faithfully flat extension where the divisor splits into sections, but the norm construction shows that the result descends and is independent of a divisor representative.

If $Z$ is a disjoint union, its action is the sum of the actions of the components. Formal integral combinations of finite correspondences therefore act by the same integral combination of homomorphisms. Negative coefficients use inversion on the Jacobian.

### 11.2 Composition and transpose

Suppose $C\xleftarrow{\alpha}Z\xrightarrow{\beta}D$ and $D\xleftarrow{\gamma}W\xrightarrow{\delta}E$ are finite locally free correspondences. Their composite is based on $Z\times_DW$. This fiber product need not be smooth, but no normalization is needed: both projections remain finite locally free, so pullback and determinant norm are defined directly on it and retain its nilpotent and intersection multiplicities. Over a field its associated one-dimensional cycle gives the equivalent divisor description with the same local lengths.

Flat base change for pullback and norm gives

$$
T_{W}\circ T_Z=T_{Z\circ W}. \tag{11.4}
$$

The decisive square is cartesian:

```text
Z x_D W  ----->  W
    |              |
    |              | gamma
    v              v
    Z  --------->  D.
          beta
```

Pulling a divisor across one side and pushing down the other gives the same cycle as pushing and then pulling, with lengths supplied by the tensor-product local rings. This is the divisor form of the base-change identity used in (11.4).

The transpose correspondence is

$$
D\xleftarrow{\beta}Z\xrightarrow{\alpha}C, \tag{11.5}
$$

and acts by $T_Z^t=\alpha_*\beta^*$.

### 11.3 Divisorial correspondences

Many correspondences arise not from a smooth middle curve but from a relative Cartier divisor

$$
\Gamma\subset C\times_SD
$$

finite locally free over both factors. Restricting the line bundle $\mathcal O(\Gamma)$ to $C\times\{d\}$ gives a family of divisor classes on $C$, hence a morphism $D\to\operatorname{Pic}_{C/S}$. After subtracting the class at a base point, the Albanese theorem extends it uniquely to a homomorphism

$$
J_D\longrightarrow J_C. \tag{11.6}
$$

With the convention (11.2), (11.6) is the action of the transposed geometric span. The apparent reversal reflects that a divisor on $C\times D$ is a family of line bundles on $C$ parametrized by $D$.

Two divisorial correspondences differing by a divisor pulled back from either factor induce the same homomorphism on Jacobians. A pullback from $C$ gives a constant map in the $D$ variable, killed by subtracting the base value; a pullback from $D$ is trivial as a relative class on $C$. Thus homomorphisms depend on the correspondence modulo these **degenerate correspondences**.

Conversely, with chosen base points, a homomorphism $J_D\to J_C$ pulls the Poincare bundle back through the two Abel maps and yields a relative divisor class on $C\times D$. This gives the useful correspondence dictionary

$$
\frac{\operatorname{Pic}(C\times D)}
{p_C^*\operatorname{Pic}(C)+p_D^*\operatorname{Pic}(D)}
\simeq\operatorname{Hom}(J_D,J_C), \tag{11.7}
$$

for smooth proper geometrically connected curves over a field, interpreted with the correct orientation and after rigidifying along both base points. Surjectivity follows from Poincare and Albanese universality; injectivity is the see-saw principle.

### 11.4 Symmetry and Rosati adjoints

For principally polarized Jacobians, define the adjoint of $u:J_C\to J_D$ by

$$
u^\dagger=\lambda_C^{-1}u^\vee\lambda_D:J_D\to J_C. \tag{11.8}
$$

Applying (10.11) twice gives

$$
(\beta_*\alpha^*)^\dagger
=\alpha_*\beta^*. \tag{11.9}
$$

Thus transposing a correspondence is exactly taking its polarization adjoint. A symmetric correspondence acts by a self-adjoint endomorphism. Composition reverses under adjoint:

$$
(uv)^\dagger=v^\dagger u^\dagger,
\qquad (u^\dagger)^\dagger=u. \tag{11.10}
$$

These identities are scheme-theoretic and compatible with base change. They are not merely statements about complex points or about one cohomology theory. This is why geometric correspondences can later be transported reliably to every realization of the Jacobian.

## 12. Nodal curves and generalized Jacobians

### 12.1 Line bundles through normalization

Smoothness made the Jacobian proper. To understand exactly what fails at a node, let $X/k$ be a proper geometrically connected nodal curve and

$$
\nu:\widetilde X=\coprod_{v\in V}X_v\longrightarrow X
$$

its normalization after extending to an algebraic closure. Each node $q$ has two branches $q^+$ and $q^-$. A line bundle on $X$ is a collection of line bundles $L_v$ on the $X_v$ together with identifications

$$
(L_{o(e)})_{q^+}\xrightarrow{\sim}(L_{t(e)})_{q^-}
$$

for all edges $e$ of the dual graph $\Gamma$.

After trivializing the branch fibers, each identification is a scalar in $k^\times$. Rescaling $L_v$ by a vertex scalar changes adjacent edge scalars. The multiplicative normalization sequence is

$$
1\longrightarrow\mathcal O_X^\times
\longrightarrow\nu_*\mathcal O_{\widetilde X}^\times
\longrightarrow\bigoplus_{e\in E}i_{e,*}\mathbf G_m
\longrightarrow1, \tag{12.1}
$$

with the last map the ratio of branch values. Its cohomology turns the gluing description into an exact sequence of Picard groups. The part surviving vertex rescaling is one copy of $\mathbf G_m$ for each independent cycle of $\Gamma$.

### 12.2 The torus--abelian exact sequence

Let $\operatorname{Pic}^0(X)$ now mean the identity component of the Picard scheme. It is the **generalized Jacobian**. Normalization gives an exact sequence of smooth connected algebraic groups

$$
0\longrightarrow T_\Gamma
\longrightarrow\operatorname{Pic}^0(X)
\longrightarrow\prod_{v\in V}J(X_v)
\longrightarrow0, \tag{12.2}
$$

where

$$
X^*(T_\Gamma)\simeq H_1(\Gamma,\mathbf Z). \tag{12.3}
$$

**Proof.** Pullback to the normalization sends a line bundle of componentwise degree zero to degree-zero bundles on all $X_v$. It is surjective because arbitrary branch-fiber identifications glue any chosen component bundles. Its kernel consists of trivial bundles on all components with edge gluing scalars, modulo vertex rescaling:

$$
(\mathbf G_m)^E/\operatorname{im}((\mathbf G_m)^V).
$$

The connectedness of $\Gamma$ makes the diagonal the kernel of the vertex map. Dualizing its character sequence identifies the quotient torus character lattice with the kernel of the graph boundary, namely $H_1(\Gamma,\mathbf Z)$. $\square$

It follows that

$$
\dim\operatorname{Pic}^0(X)
=\sum_vg(X_v)+b_1(\Gamma)=p_a(X). \tag{12.4}
$$

The generalized Jacobian is proper exactly when $T_\Gamma=0$, equivalently when $\Gamma$ is a tree. Such a nodal curve is said to be of compact type. Reducibility by itself does not destroy properness.

Over a nonclosed field, (12.2) descends. The torus is characterized by the Galois module $H_1(\Gamma_{\bar k},\mathbf Z)$. Branch interchange can act by $-1$, producing a nonsplit torus even when the unoriented graph looks unchanged.

### 12.3 Multidegrees and connected components

A line bundle on $X_{\bar k}$ has a multidegree

$$
\underline{\deg}(L)=(\deg L|_{X_v})_{v\in V}\in\mathbf Z^V. \tag{12.5}
$$

Total degree is the sum of these integers. The identity component consists of multidegree zero, not merely total degree zero. Indeed multidegree is locally constant in families of line bundles on a fixed nodal curve, and every multidegree-zero class lies in the connected group (12.2).

Thus the total-degree-zero Picard scheme has components indexed geometrically by

$$
\operatorname{Div}^0(\Gamma)
=\{(d_v)\in\mathbf Z^V:\sum_vd_v=0\}. \tag{12.6}
$$

It is generally not of finite type. For two components meeting in one node, the pairs $(n,-n)$ give infinitely many components even though the generalized Jacobian is simply the product of the two component Jacobians. In a varying family, vertical line bundles can identify some of these components generically; this is the source of nonseparatedness studied next.

### 12.4 Relative nodal families

Let $X\to S$ be proper, flat, finitely presented, and nodal with geometrically connected fibers. Nodal morphisms are Gorenstein, so the dualizing line bundle exists and commutes with base change. The relative Picard sheaf is represented locally around every finite collection of multidegrees by a smooth group scheme locally of finite presentation. The infinitesimal proof is the same as in Chapter 5: $H^2(\mathcal O)$ vanishes, and $R^1f_*\mathcal O_X$ is locally free of rank the arithmetic genus.

The union of fiberwise identity components is an open subgroup

$$
\operatorname{Pic}^0_{X/S}\subset\operatorname{Pic}_{X/S}. \tag{12.7}
$$

Its fibers are generalized Jacobians and hence extensions of abelian varieties by tori. It is a semiabelian scheme when the toric ranks vary locally constantly; across a smoothing the toric rank can jump, so the total smooth group still has semiabelian fibers but need not be an extension by one torus of constant rank over all of $S$.

At a smooth fiber, (12.7) is an abelian variety. At a nodal fiber, the torus records the cycles created by gluing. The invariant cotangent space remains

$$
H^0(X_s,\omega_{X_s}),
$$

whose normalization description allows simple poles with opposite residues at paired branches. The residue parameters dualize precisely the graph-cycle directions of the torus.

## 13. Semistable specialization over a valuation ring

### 13.1 Why total degree is not separated

Let $R$ be a henselian discrete valuation ring, $S=\operatorname{Spec}R$, and let $\mathcal X/S$ be a regular proper semistable curve with smooth geometrically connected generic fiber $C$. After passing to the strict henselization, write the split geometric special fiber as

$$
\mathcal X_{\bar s}=\sum_{v\in V}Y_v.
$$

A vertical divisor $V=\sum_va_vY_v$ on this strict-henselian base is empty on the generic fiber, so $\mathcal O_{\mathcal X}(V)$ is generically trivial. It can nevertheless have a nonzero special multidegree. Therefore two sections of the total-degree-zero Picard object can agree generically and differ at the closed point. The diagonal is not closed: the object is nonseparated. All lattice calculations below are equivariant for the residue-field Galois action and hence descend to $R$; without splitting, an individual $Y_v$ need not itself be a divisor over the ground ring.

This does not contradict separatedness of the Picard scheme for a smooth family. The special fiber here is reducible, and degree zero on the generic curve imposes only total degree zero after specialization. It does not force multidegree zero.

### 13.2 Vertical line bundles and the Laplacian

Let $\Gamma$ be the dual graph and let $\Delta$ be its graph Laplacian with the convention

$$
(\Delta a)_v=\sum_{e=vw}(a_v-a_w).
$$

The intersection calculation on the regular surface gives

$$
\deg\bigl(\mathcal O(V)|_{Y_w}\bigr)
=(V\cdot Y_w)=-(\Delta a)_w. \tag{13.1}
$$

To prove it, distinct components meeting at a node have intersection one, while the whole fiber is principal and has zero intersection with every $Y_w$. Therefore

$$
Y_w^2=-\#\{\text{branches from }w\text{ to other components}\},
$$

while a loop contributes zero to the graph Laplacian because both branches lie on the same component. Expanding $V\cdot Y_w$ yields (13.1). Adding a constant to all $a_v$ adds a multiple of the whole fiber and changes no line bundle.

Thus generically trivial vertical line bundles change multidegree by $\operatorname{im}\Delta$. The quotient

$$
\frac{\operatorname{Div}^0(\Gamma)}{\Delta\mathbf Z^V} \tag{13.2}
$$

is finite; it is the graph Jacobian or critical group. It measures the multidegree ambiguity that vertical twisting cannot remove.

### 13.3 The separated quotient

Let $P$ be the total-degree-zero relative Picard scheme and let $E$ be the schematic closure in $P$ of the generic identity. Quotienting by this flat closure removes precisely the vertical ambiguity:

$$
P^{\mathrm{sep}}=P/E. \tag{13.3}
$$

For a regular semistable curve, the semistable Picard-quotient theorem established for this exact henselian setting shows that $E$ is flat, that the fppf quotient is represented, and that it is smooth and separated over $R$. It has generic fiber $J_C$ and the extension property for line-bundle classes from smooth $R$-schemes. Its special identity component is the generalized Jacobian (12.2), and its geometric component group is

$$
\Phi\simeq
\operatorname{Div}^0(\Gamma)/\Delta\mathbf Z^V. \tag{13.4}
$$

The proof separates two issues. Within a fixed multidegree, normalization identifies the connected group with the generalized Jacobian. Twisting by vertical divisors identifies multidegrees differing by a Laplacian. Hence (13.4) indexes the remaining components. If two extensions of the same generic line bundle are compared, their ratio is generically trivial; regularity lets a rational trivialization have a Cartier divisor supported on the special fiber, so the ratio lies in $E$. This proves uniqueness in the separated quotient. Existence is obtained after moving a generic divisor away from the singular points and taking its closure.

If a node has thickness greater than one or the total space is not regular, its component need not be Cartier and (13.1) cannot be used unchanged. Resolving inserts a chain of components; compressing the resulting unit-length graph produces the weighted length pairing. The weighted graph, not the reduced incidence graph alone, controls the quotient.

### 13.4 Functoriality on special fibers

Suppose a finite map of smooth generic curves extends to a finite flat map of regular semistable models after controlled modification. Pullback and norm preserve generically trivial line bundles, so they descend through (13.3). On special identity components they act on the normalization Jacobians and graph tori; on component groups they act by pullback and pushforward of graph divisors.

The graph maps satisfy harmonicity: the sum of branch degrees above any chosen branch at a vertex equals the degree on the component. This identity is exactly what makes Laplacian-equivalent divisors remain equivalent. Under the edge-length pairing, graph pullback and pushforward are adjoint. Thus the special-fiber formula is the combinatorial shadow of (10.11).

A correspondence extending to semistable models acts by the same pull--push rule on generalized Jacobians and component groups. Its transpose is adjoint. If the correspondence does not extend finitely to the chosen models, one must pass to a common dominating semistable model before reading an action from the graph; the generic Jacobian homomorphism itself remains well defined.

## 14. Descent, twists, and failure modes

### 14.1 Descent of Picard data

Every construction in this book is compatible with faithfully flat descent, but the pieces descend for different reasons:

- line bundles and their rigidifications descend effectively from cocycles;
- the representing property gives canonical overlap isomorphisms for local Picard schemes, while Section 3.4 proves scheme effectivity componentwise by a finite locally free multisection and Book 10's norm-ampleness criterion;
- group laws, Abel maps, norms, and correspondence maps descend as morphisms satisfying equations;
- smoothness, properness, separatedness, and finite presentation descend as properties of morphisms;
- polarizations descend through their relatively ample line bundles locally, while the associated homomorphism descends intrinsically even if a theta divisor does not;
- universal line bundles may be obstructed by a Brauer class and therefore require a section or an explicit rigidification.

This list prevents a common circularity. One does not claim that a locally constructed scheme represents the global functor merely because its fibers look right. The overlap isomorphisms must satisfy the triple cocycle, a specific criterion from Book 10 must prove that the algebraic-space descent is a scheme, and full faithfulness must then verify the universal property. For the smooth Picard scheme, that specific criterion is the finite-cover argument of Section 3.4.

### 14.2 Curves without rational points

Let $C/k$ be a smooth proper geometrically connected curve with no $k$-point. The Jacobian $J$ still exists over $k$, as do all Picard torsors $\operatorname{Pic}^d$. After a finite separable extension possessing a point, one may identify $\operatorname{Pic}^d$ with $J$ by translation. Galois conjugation changes that identification by a $J$-valued cocycle, whose torsor class records the failure of a degree-$d$ base bundle to descend.

There are three increasingly strong notions:

1. a $k$-point of the Picard **scheme**, which is an fppf relative class;
2. an actual line bundle of degree $d$ on $C$, requiring the Brauer obstruction (2.2) to vanish;
3. an effective divisor of degree $d$, requiring that line bundle to possess a nonzero section.

They need not coincide. The Abel image lies only in the third locus. Riemann--Roch ensures that every class of degree at least $2g-1$ has a section after it is represented by a line bundle, but it does not erase its Brauer obstruction over the ground field. After fppf base change all three distinctions can disappear, which is why the relative Picard sheaf is the correct moduli object.

The canonical polarization is unaffected. It is constructed after an fpqc extension with a point, is independent of the point, and descends uniquely. The unpointed Albanese map lands in a torsor rather than forcing a nonexistent origin.

### 14.3 Hypotheses that cannot be dropped

The principal theorems have sharp boundaries.

**Properness.** On an affine smooth curve, line bundles can be governed by behavior at a missing boundary, coherent cohomology need not give a proper parameter space, and principal divisors need not balance. Generalized Jacobians of open curves require a modulus and are different objects.

**Geometric connectedness.** If fibers have several connected components, $f_*\mathcal O_C$ is not $\mathcal O_S$. Scalar rigidification along one section does not control automorphisms on the other components, and degree becomes a vector indexed by connected components.

**Smoothness.** For a nodal curve, $\operatorname{Pic}^0$ acquires a torus and may cease to be proper. For a cusp, the connected Picard group has a unipotent additive part rather than a torus. Nonreduced curves can contribute further unipotent directions and can violate the relative cohomological-flatness hypotheses used above. The phrase “Jacobian is an abelian variety” therefore requires a smooth proper curve, or compact-type hypotheses in a controlled nodal case.

**Flatness and finite presentation.** Without flatness, Euler characteristics and degrees can jump and the relative Picard functor need not have the stated components. Without finite presentation, infinitesimal smoothness does not automatically become smoothness and descent need not preserve bounded geometry.

**A section.** A section is unnecessary for representability or for the canonical polarization. It is necessary for the simple identification with rigidified line bundles, for a globally normalized Poincare bundle, and for a pointed Abel map $C\to J$. Replacing “no section” by “choose a geometric point” without descent would lose arithmetic information.

**Finite local freeness.** The determinant norm (10.3) requires $h_*L$ to be finite locally free of constant rank. For a merely proper or generically finite map, a derived determinant can sometimes replace it, but formulas then require additional perfectness and ramification hypotheses. No such extension is implicit here.

**Characteristic.** No argument assumes characteristic zero. Scheme-theoretic kernel lengths in the proof of principality handle inseparable isogenies, and determinant norms handle purely inseparable finite maps. Arguments using only tangent spaces or geometric points would not suffice in positive characteristic.

## 15. The complete Jacobian package

### 15.1 A functorial summary

Let $C\to S$ be a smooth proper finitely presented curve of genus $g$ with geometrically connected fibers. The theory developed above provides the following mutually compatible package.

The fppf sheaf of line bundles modulo base pullbacks is represented by

$$
\operatorname{Pic}_{C/S}=\coprod_{d\in\mathbf Z}\operatorname{Pic}^d_{C/S}.
$$

Every component is smooth and proper of relative dimension $g$, commutes with arbitrary base change, and is a torsor under the abelian scheme

$$
J_{C/S}=\operatorname{Pic}^0_{C/S}.
$$

At the identity,

$$
\operatorname{Lie}(J/S)=R^1f_*\mathcal O_C,
\qquad
\omega_J=f_*\omega_{C/S}.
$$

A section $e$ supplies a normalized Poincare bundle and Abel maps

$$
C^{(d)}\longrightarrow\operatorname{Pic}^d,
\qquad
D\longmapsto\mathcal O(D),
$$

with differential the cohomology boundary and dual differential restriction of regular differentials. The pointed map $j_e:C\to J$ generates $J$ and is initial among pointed maps from $C$ to abelian schemes.

The theta determinant gives a canonical principal polarization

$$
\lambda_C:J\xrightarrow{\sim}J^\vee,
$$

independent of the section and compatible with every base change. With $t_x(y)=y+x$ and $j_e(p)=\mathcal O(p-e)$, its sign is $j_e^*\lambda_C=[-1]_J$, so Albanese factorization uses the minus sign in (9.2). For a finite map $h:C\to D$, automatically finite locally free under the standing smooth-family hypotheses, pullback and norm satisfy

$$
\operatorname{Nm}_h h^*=[\deg h],
\qquad
(h^*)^\vee\lambda_C=\lambda_D\operatorname{Nm}_h.
$$

Consequently a correspondence $C\xleftarrow{\alpha}Z\xrightarrow{\beta}D$ acts by $\beta_*\alpha^*$, composition agrees with composition of correspondences, and transpose agrees with polarization adjoint.

For nodal curves, the same Picard language identifies the exact correction:

$$
0\longrightarrow T_\Gamma
\longrightarrow\operatorname{Pic}^0(X)
\longrightarrow\prod_vJ(X_v)
\longrightarrow0,
\qquad X^*(T_\Gamma)=H_1(\Gamma,\mathbf Z).
$$

Over a valuation ring, vertical divisors cause nonseparatedness, the separated quotient removes their schematic closure, and the remaining component group is the graph Jacobian, with weighted edge lengths when the model is not regular.

### 15.2 Conclusion

The passage from a curve to its Jacobian is not merely the replacement of divisors by divisor classes. It is a sequence of geometric corrections. Quotienting removes line bundles imported from the base. Sheafification remembers descent classes without insisting on a global representative. Rigidification removes scalar automorphisms. High-degree divisors make the functor finite-dimensional and representable. The identity component then isolates a proper smooth group carrying exactly the first coherent cohomology of the curve.

The Abel map returns the curve to that group. Its differential is the boundary of a divisor sequence, and duality identifies the transpose with restriction of differentials. The theta divisor turns this infinitesimal relation into a global principal polarization, making the Jacobian canonically self-dual. Self-duality converts the Picard classification of line bundles into the Albanese classification of maps. Norms and pullbacks then become adjoints, so finite maps and correspondences act with the correct covariance and transpose.

Degeneration does not destroy this structure; it reveals its limits. A node contributes a multiplicative gluing parameter for each graph cycle. Vertical divisors account for nonseparated extensions, and the graph Laplacian records the finite component group left after separation. Thus smooth Jacobians, generalized Jacobians, and semistable component groups are three layers of one Picard construction. Together they form the functorial geometric language needed to carry curves, divisors, differentials, finite maps, and correspondences into the theory of abelian varieties.
