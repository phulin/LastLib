# Finite Flat Commutative Group Schemes

## Contents

1. [The finite-flat category](#1-the-finite-flat-category)
   - [Why an integral group is more than its generic points](#11-why-an-integral-group-is-more-than-its-generic-points)
   - [Hopf algebras of finite projective rank](#12-hopf-algebras-of-finite-projective-rank)
   - [Order and rank](#13-order-and-rank)
   - [Base change as a structural requirement](#14-base-change-as-a-structural-requirement)
2. [Basic constructions and their limits](#2-basic-constructions-and-their-limits)
   - [Products and fiber products](#21-products-and-fiber-products)
   - [Kernels](#22-kernels)
   - [Images and coimages](#23-images-and-coimages)
   - [Quotients and torsors](#24-quotients-and-torsors)
   - [Exact sequences and rank multiplicativity](#25-exact-sequences-and-rank-multiplicativity)
3. [Standard families](#3-standard-families)
   - [Constant groups](#31-constant-groups)
   - [Diagonalizable groups](#32-diagonalizable-groups)
   - [Roots of unity](#33-roots-of-unity)
   - [Additive infinitesimal groups](#34-additive-infinitesimal-groups)
   - [A family changing from étale to connected](#35-a-family-changing-from-étale-to-connected)
   - [Mixed products and extensions](#36-mixed-products-and-extensions)
4. [Multiplication and torsion kernels](#4-multiplication-and-torsion-kernels)
   - [Why multiplication by an integer is geometric](#41-why-multiplication-by-an-integer-is-geometric)
   - [Elementary computations](#42-elementary-computations)
   - [Prime-power decomposition](#43-prime-power-decomposition)
   - [When order kills the group](#44-when-order-kills-the-group)
   - [Tangent space as a diagnostic, not a classifier](#45-tangent-space-as-a-diagnostic-not-a-classifier)
   - [Exact sequences among the standard groups](#46-exact-sequences-among-the-standard-groups)
5. [Fibers over fields](#5-fibers-over-fields)
   - [Artinian geometry at the identity](#51-artinian-geometry-at-the-identity)
   - [Reduced, smooth, and étale](#52-reduced-smooth-and-étale)
   - [The connected-étale sequence over a perfect field](#53-the-connected-étale-sequence-over-a-perfect-field)
   - [Frobenius as a separator](#54-frobenius-as-a-separator)
   - [Three rank-$p$ fibers](#55-three-rank-p-fibers)
6. [Finite étale groups and Galois modules](#6-finite-étale-groups-and-galois-modules)
   - [Why geometric points work in the étale case](#61-why-geometric-points-work-in-the-étale-case)
   - [The equivalence over a field](#62-the-equivalence-over-a-field)
   - [Unramified modules from a henselian DVR](#63-unramified-modules-from-a-henselian-dvr)
   - [Specialization of points](#64-specialization-of-points)
7. [Henselian local bases and connected-étale structure](#7-henselian-local-bases-and-connected-étale-structure)
   - [Lifting the special-fiber decomposition](#71-lifting-the-special-fiber-decomposition)
   - [The local connected-étale sequence](#72-the-local-connected-étale-sequence)
   - [Maximality and rank](#73-maximality-and-rank)
   - [Base change and completion](#74-base-change-and-completion)
8. [Schematic closure over a DVR](#8-schematic-closure-over-a-dvr)
   - [The extension problem](#81-the-extension-problem)
   - [Finiteness and flatness of the closure](#82-finiteness-and-flatness-of-the-closure)
   - [Saturated Hopf ideals and uniqueness](#83-saturated-hopf-ideals-and-uniqueness)
   - [Intersections, sums, and generated subgroups](#84-intersections-sums-and-generated-subgroups)
   - [Extending generic morphisms](#85-extending-generic-morphisms)
   - [Images over a DVR](#86-images-over-a-dvr)
9. [Local models and their generic fibers](#9-local-models-and-their-generic-fibers)
   - [Finite flat groups over a local ring](#91-finite-flat-groups-over-a-local-ring)
   - [The DVR lattice picture](#92-the-dvr-lattice-picture)
   - [The generic-fiber and special-fiber functors](#93-the-generic-fiber-and-special-fiber-functors)
   - [Two models of one generic additive group](#94-two-models-of-one-generic-additive-group)
   - [Constant and multiplicative models in mixed characteristic](#95-constant-and-multiplicative-models-in-mixed-characteristic)
   - [Criteria that restore uniqueness](#96-criteria-that-restore-uniqueness)
   - [Beyond DVRs](#97-beyond-dvrs)
10. [Torsion on abelian schemes](#10-torsion-on-abelian-schemes)
    - [Why a proper smooth group enters a finite theory](#101-why-a-proper-smooth-group-enters-a-finite-theory)
    - [Why multiplication is finite flat](#102-why-multiplication-is-finite-flat)
    - [Elliptic curves](#103-elliptic-curves)
    - [Subgroups and isogenies](#104-subgroups-and-isogenies)
    - [Rational subgroups versus subgroup schemes](#105-rational-subgroups-versus-subgroup-schemes)
11. [Closing generic subgroups in abelian schemes](#11-closing-generic-subgroups-in-abelian-schemes)
    - [Reduction to a finite ambient torsion group](#111-reduction-to-a-finite-ambient-torsion-group)
    - [Closure and quotient isogenies](#112-closure-and-quotient-isogenies)
    - [Elliptic cyclic subgroups](#113-elliptic-cyclic-subgroups)
    - [Intersections of torsion subgroup schemes](#114-intersections-of-torsion-subgroup-schemes)
    - [Good reduction and torsion](#115-good-reduction-and-torsion)
12. [Exact calculus over arithmetic bases](#12-exact-calculus-over-arithmetic-bases)
    - [Subobjects](#121-subobjects)
    - [Quotients](#122-quotients)
    - [Extensions](#123-extensions)
    - [Annihilators and primary parts](#124-annihilators-and-primary-parts)
    - [Homomorphisms and base change](#125-homomorphisms-and-base-change)
    - [Internal linear constructions](#126-internal-linear-constructions)
    - [Rank bookkeeping](#127-rank-bookkeeping)
13. [Models of finite Galois modules](#13-models-of-finite-galois-modules)
    - [From a generic group to a representation](#131-from-a-generic-group-to-a-representation)
    - [The category of models of a fixed module](#132-the-category-of-models-of-a-fixed-module)
    - [Submodules](#133-submodules)
    - [Extensions and exact models](#134-extensions-and-exact-models)
    - [Scalar extension](#135-scalar-extension)
    - [A precise finite-flat model category](#136-a-precise-finite-flat-model-category)
14. [Structural synthesis](#14-structural-synthesis)
    - [The three layers of a finite-flat object](#141-the-three-layers-of-a-finite-flat-object)
    - [A safe construction protocol](#142-a-safe-construction-protocol)
    - [Hypotheses and what they buy](#143-hypotheses-and-what-they-buy)
    - [What exactness means](#144-what-exactness-means)
    - [The boundary with duality](#145-the-boundary-with-duality)
    - [Conclusion](#146-conclusion)

## 1. The finite-flat category

### 1.1 Why an integral group is more than its generic points

A finite group over a field can often be described by finitely many points carrying a Galois action. Over an arithmetic ring that description is incomplete. Points may collide under specialization, and the collision is recorded by nilpotents rather than by a smaller group. The basic example is

$$
\mu_p=\operatorname{Spec}R[T]/(T^p-1)
$$

over a discrete valuation ring of residue characteristic $p$. Its generic fiber in characteristic zero is étale. Its special fiber is defined by $(T-1)^p$ and has one geometric point of length $p$. Any category meant to carry torsion through specialization must preserve that length and the group law on the thickened point.

Throughout, a **finite flat commutative group scheme** over a scheme $S$ means a commutative $S$-group scheme whose structure morphism is finite locally free. Thus finite presentation is included. On an affine open $S=\operatorname{Spec}R$, such a group is

$$
G=\operatorname{Spec}A,
$$

where $A$ is a commutative, cocommutative Hopf $R$-algebra that is finite projective as an $R$-module. We write its structure maps as

$$
\Delta:A\longrightarrow A\otimes_RA,\qquad
\varepsilon:A\longrightarrow R,\qquad
\iota:A\longrightarrow A.
$$

The word *commutative* refers to the represented group and therefore to cocommutativity of $\Delta$; the coordinate algebra is commutative for every affine group scheme. We abbreviate the category to $\mathrm{FFCG}(S)$. Morphisms are homomorphisms of $S$-group schemes.

This convention avoids a genuine pathology. Over an arbitrary nonnoetherian ring, a finite flat module need not be finitely presented and hence need not be locally free. Over a noetherian ring, or over a local ring for a finitely generated flat module, the shorter phrase “finite flat” has the same force. The categorical definition nevertheless keeps the finiteness needed for rank, descent, and quotients visible.

### 1.2 Hopf algebras of finite projective rank

The affine correspondence identifies $\mathrm{FFCG}(\operatorname{Spec}R)$ contravariantly with finite projective commutative, cocommutative Hopf $R$-algebras. A morphism $f:G\to H$ corresponds to a Hopf map

$$
f^*:\mathcal O(H)\longrightarrow\mathcal O(G).
$$

Closed subgroup schemes reverse to surjective Hopf maps. If $I\subset A$ defines a closed subscheme, it defines a subgroup precisely when

$$
\Delta(I)\subset I\otimes A+A\otimes I,\qquad
\varepsilon(I)=0,\qquad \iota(I)\subset I.
$$

Such an $I$ is a Hopf ideal. These conditions express closure under multiplication, inclusion of the identity, and closure under inverse. They are scheme-theoretic: checking them on geometric points would miss $\alpha_p$ and $\mu_p$.

The counit splits the unit map $R\to A$. Hence

$$
A\simeq R\oplus A^+,\qquad A^+=\ker\varepsilon,
$$

as $R$-modules. In particular every nonempty fiber has positive rank. Unlike a general finite locally free scheme, a finite locally free group scheme cannot disappear over a component of its base: its identity section is always present.

The finite projective condition is not decorative. It makes tensor products, dual modules, ranks, and all Hopf identities compatible with arbitrary base change. It also ensures that fiber length, rather than the number of points, is conserved.

### 1.3 Order and rank

The **order** of $G$ is the locally constant function

$$
|G|:S\longrightarrow\mathbf Z_{>0},\qquad
s\longmapsto\dim_{\kappa(s)}\mathcal O(G_s).
$$

On a connected base it is a single positive integer, also called the rank of $G$. If $S$ is disconnected, a statement such as “$G$ has order $n$” asserts constancy and cannot be inferred merely from finite local freeness.

For every geometric point $\bar s\to S$,

$$
|G|(s)=\operatorname{length}(G_{\bar s}).
$$

This is not generally $|G(\bar s)|$. Over an algebraically closed field, translations identify the local Artinian rings at all points, so

$$
\operatorname{rank}G
=|G(\bar s)|\,\operatorname{length}\mathcal O_{G_{\bar s},e}.
$$

Thus the number of geometric points divides the order, and equality holds exactly when the fiber is reduced. The formula explains in one line why $\underline{\mathbf Z/p\mathbf Z}$, $\mu_p$, and $\alpha_p$ all have order $p$ in characteristic $p$ although their point sets are radically different.

### 1.4 Base change as a structural requirement

For every map $S'\to S$, base change gives a functor

$$
\mathrm{FFCG}(S)\longrightarrow\mathrm{FFCG}(S'),\qquad
G\longmapsto G_{S'}.
$$

On affine coordinates it sends $A$ to $A\otimes_RR'$. No flatness of $S'\to S$ is required. The rank function pulls back, and the Hopf maps are obtained by tensoring. Products and scheme-theoretic kernels commute with arbitrary base change because they are fiber products.

Faithfully flat base change also detects the structure. A morphism of finite locally free group schemes is an isomorphism if it becomes one after such a cover. Finite projectivity, a Hopf-ideal equality, and a torsor identity all descend. By contrast, a subgroup found only in one geometric fiber does not automatically descend; its ideal needs descent data.

The resulting principle will govern the whole book: construct scheme-theoretically, prove flatness on coordinate algebras, and only then use fibers to interpret the result.

## 2. Basic constructions and their limits

### 2.1 Products and fiber products

Finite flat groups are stable under finite products. If $G=\operatorname{Spec}A$ and $H=\operatorname{Spec}B$ over $R$, then

$$
G\times_RH=\operatorname{Spec}(A\otimes_RB),
$$

with the tensor-product Hopf structure. Since tensor products of finite projective modules are finite projective,

$$
|G\times H|=|G|\,|H|
$$

pointwise on the base.

More generally, a fiber product $G\times_QH$ of group schemes is representable and affine. It need not be finite flat merely because $G,H,Q$ are: the relative tensor product of their coordinate algebras can acquire torsion. It is finite flat when, for example, one of the maps to $Q$ is finite locally free. This distinction between products over the base and fiber products over another group will recur in kernels.

### 2.2 Kernels

For $f:G\to H$, the kernel is the fiber product

$$
\ker f=G\times_{H,e_H}S.
$$

It is always a closed affine subgroup. If $B=\mathcal O(H)$, $A=\mathcal O(G)$, and $B^+=\ker\varepsilon_B$, then

$$
\mathcal O(\ker f)=A/Af^*(B^+).
$$

When $G$ is finite, the kernel is finite. It is not formally finite flat: a quotient of a finite projective module can have base torsion. It belongs to $\mathrm{FFCG}(S)$ precisely when this quotient algebra is finite locally free. Useful sufficient conditions are:

- it is flat and finitely presented over the base;
- the base is noetherian and it is flat;
- the base is a DVR and its coordinate algebra is torsion-free;
- $f$ is faithfully flat between finite locally free group schemes.

The last case follows because $G\to H$ is then a torsor under its kernel. It is a serious error to omit the flatness conclusion and infer it merely from closedness.

An explicit failure will be useful later. Over $R=k[[t]]$ of characteristic $p$, consider

$$
f:G_1\longrightarrow G_t,\qquad x\longmapsto tx,
$$

where $G_1$ and $G_t$ are defined in §9.4. The kernel has coordinate algebra

$$
R[X]/(X^p-X,tX).
$$

Its generic fiber is the identity, whereas its special fiber is all of the order-$p$ étale group $G_{1,k}$. The class of $X$ is $t$-torsion, so this finite closed subgroup is not flat. Both source and target of $f$ are finite flat. This counterexample prevents us from treating arbitrary kernels as objects of $\mathrm{FFCG}(R)$.

### 2.3 Images and coimages

For an affine morphism $f:G\to H$, the schematic image as a closed subscheme is defined by

$$
\operatorname{SIm}(f)=\operatorname{Spec}\bigl(\mathcal O(H)/\ker f^*\bigr).
$$

Over a field, $\ker f^*$ is a Hopf ideal, so this is a closed subgroup. Over a general base, tensoring an injection can destroy injectivity, and Hopf stability is not automatic. It follows under a purity hypothesis on the inclusion of the image algebra into $\mathcal O(G)$; flat cokernel is sufficient. Flat base change then commutes with formation of the image, while arbitrary base change need not.

In the finite-flat category, the safest definition of an image is therefore a **flat image factorization**

$$
G\xrightarrow{q}I\xrightarrow{j}H
$$

in which $I$ is finite locally free, $q$ is faithfully flat, and $j$ is a closed immersion. When such a factorization exists, it is unique up to unique isomorphism. Indeed $I$ is the quotient of $G$ by $\ker q$, and its closed immersion has the required schematic image. Over a field it always exists. Over a DVR, closing the generic image always produces a finite-flat closed subgroup $I\subset H$ through which $f$ factors, but the induced map $G\to I$ need not be faithfully flat; §8.6 gives the exact criterion and a counterexample. Over an arbitrary base even flatness of the schematic image is an additional theorem or hypothesis, not part of the category axioms.

### 2.4 Quotients and torsors

Let $N\hookrightarrow G$ be a finite locally free closed subgroup. Because $G$ is commutative, $N$ is normal. The faithfully flat sheaf quotient $G/N$ is represented by an affine group scheme, and

$$
G\longrightarrow G/N
$$

is an $N$-torsor, finite locally free of rank $|N|$. If $G$ is finite locally free, then so is $G/N$. On affine coordinates, with $A=\mathcal O(G)$ and $C=\mathcal O(N)$, the quotient algebra is the invariant subalgebra

$$
B=A^{\operatorname{co}C}
=\{a\in A:\rho(a)=a\otimes1\},
$$

and the decisive identity is

$$
A\otimes_BA\xrightarrow{\sim}A\otimes_RC.
$$

This identity says that two points of $G$ over the same quotient point differ uniquely by a point of $N$, locally for the faithfully flat topology.

The quotient presheaf $T\mapsto G(T)/N(T)$ is generally not represented by $G/N$ without sheafification. For example, the exact sequence

$$
1\longrightarrow\mu_n\longrightarrow\mathbf G_m
\xrightarrow{[n]}\mathbf G_m\longrightarrow1
$$

is faithfully flat exact, although not every unit of every ring is an $n$th power. Representability concerns locally liftable cosets, not pointwise surjectivity.

### 2.5 Exact sequences and rank multiplicativity

A sequence in $\mathrm{FFCG}(S)$

$$
0\longrightarrow G'\xrightarrow{i}G\xrightarrow{q}G''\longrightarrow0
$$

is **exact** when $i$ identifies $G'$ with the scheme-theoretic kernel of $q$ and $q$ is faithfully flat, equivalently when $G''$ represents the faithfully flat sheaf quotient $G/G'$. Then $G\to G''$ is a $G'$-torsor, and arbitrary base change preserves exactness.

If the orders are constant on a connected component, torsor descent gives

$$
|G|=|G'|\,|G''|.
$$

This is the finite-flat form of Lagrange's theorem. Its proof does not count points: after the faithfully flat cover $G\to G''$, the torsor is the projection $G\times G'\to G$, whose rank is visibly $|G'|$, and rank descends.

Exactness has useful two-out-of-three consequences. If $G'$ and $G''$ are finite locally free and $G\to G''$ is a torsor under $G'$, then $G$ is finite locally free. If $G$ and $G'$ are finite locally free and the quotient theorem applies, then $G''$ is finite locally free. None of these conclusions follows from exactness of abstract groups of geometric points.

## 3. Standard families

### 3.1 Constant groups

For a finite abelian group $M$, the constant group scheme

$$
\underline M_S=\coprod_{m\in M}S
$$

is finite étale and finite locally free of order $|M|$. Its coordinate algebra is the product $R^M$. For a connected test scheme $T$, its $T$-points are $M$; for disconnected $T$, they are locally constant maps from $T$ to $M$. Thus even a constant group scheme is a functor, not literally one fixed set on all tests.

If $N\subset M$, then

$$
0\to\underline N\to\underline M\to\underline{M/N}\to0
$$

is exact. This example behaves like elementary finite-group theory because all components remain disjoint. It is the étale pole of the subject.

### 3.2 Diagonalizable groups

For a finite abelian group $M$, put

$$
D_S(M)=\operatorname{Spec}R[M],
$$

where $R[M]$ has basis $X^m$ and

$$
\Delta(X^m)=X^m\otimes X^m,\qquad
\varepsilon(X^m)=1,\qquad
\iota(X^m)=X^{-m}.
$$

Then $D(M)$ is finite locally free of order $|M|$, and

$$
D(M)(C)=\operatorname{Hom}(M,C^\times).
$$

A homomorphism $M\to N$ induces $D(N)\to D(M)$: character groups reverse arrows. The functor $D$ takes a short exact sequence of finite abelian groups to a short exact sequence of finite flat group schemes in the reversed order. This follows directly from group algebras and the quotient theorem. The relation between constant and diagonalizable groups will become a duality in the next volume; here they are simply two independent standard constructions.

### 3.3 Roots of unity

The most important diagonalizable example is

$$
\mu_n=D(\mathbf Z/n\mathbf Z)
=\operatorname{Spec}R[T]/(T^n-1).
$$

Its coordinate algebra is free with basis $1,T,\ldots,T^{n-1}$, so $\mu_n$ is finite flat of order $n$ over every base. If $n$ is invertible on $S$, the derivative $nT^{n-1}$ is a unit along $T^n=1$, and $\mu_n$ is finite étale. If the residue characteristic divides $n$, it may be nonreduced.

Over a field $k$ of characteristic $p$,

$$
\mu_p=\operatorname{Spec}k[u]/(u^p),\qquad u=T-1,
$$

with

$$
\Delta(u)=u\otimes1+1\otimes u+u\otimes u.
$$

There is only one geometric point, but its local ring has length $p$. The quadratic term in the coproduct remembers that this infinitesimal group came from multiplication.

### 3.4 Additive infinitesimal groups

In characteristic $p$, Frobenius on $\mathbf G_a$ has kernel

$$
\alpha_p=\operatorname{Spec}k[T]/(T^p),
$$

with primitive coproduct

$$
\Delta(T)=T\otimes1+1\otimes T.
$$

It too has order $p$ and one geometric point, but it is not $\mu_p$. Over the dual numbers both have one-dimensional tangent space, so even first-order infinitesimal data do not distinguish them; their full Hopf laws do.

More generally, over a ring of characteristic $p$, every additive polynomial

$$
P(T)=a_0T+a_1T^p+\cdots+a_rT^{p^r}
$$

defines a homomorphism $P:\mathbf G_a\to\mathbf G_a$. If its leading coefficient is a unit, its kernel is finite locally free of order $p^r$. It is étale where $a_0$ is a unit and may become connected where $a_0$ vanishes. These families provide controlled mixed behavior over a single base.

### 3.5 A family changing from étale to connected

Let $R=k[[t]]$ have characteristic $p$, and define

$$
G_a=\ker(F-a:\mathbf G_a\to\mathbf G_a)
=\operatorname{Spec}R[T]/(T^p-aT).
$$

For every $a\in R$, this is free of order $p$. If $a=1$, the derivative is $-1$, so $G_1$ is finite étale. If $a=t^{p-1}$, the generic fiber is also étale, but the special fiber is $\alpha_p$.

The generic fibers of $G_1$ and $G_{t^{p-1}}$ are isomorphic: over $K=k((t))$, multiplication by $t$ carries solutions of $x^p=x$ to solutions of $y^p=t^{p-1}y$. Yet the integral models are not isomorphic, since one special fiber is étale and the other connected. This example will be our basic warning that a generic finite group can admit several finite-flat models.

### 3.6 Mixed products and extensions

Products such as

$$
\mu_p\times\underline{\mathbf Z/p\mathbf Z},\qquad
\alpha_p\times\mu_p
$$

are legitimate finite flat groups in characteristic $p$, of order $p^2$. The first has $p$ connected components, each of length $p$; the second is connected of length $p^2$. Equal rank therefore says almost nothing about connectedness.

There are also nonsplit extensions

$$
0\to G'\to G\to G''\to0.
$$

Even when $G'$ and $G''$ are constant or diagonalizable, $G$ need not be their product. Exactness supplies the rank $|G'||G''|$, not a splitting. A splitting is a homomorphism $G''\to G$ right inverse to the quotient, and its existence is a separate descent question.

## 4. Multiplication and torsion kernels

### 4.1 Why multiplication by an integer is geometric

For a commutative group scheme $G$, repeated addition defines

$$
[n]:G\longrightarrow G
$$

for every $n\in\mathbf Z$. Its kernel

$$
G[n]=\ker[n]
$$

is the $n$-torsion subgroup scheme. Because kernels and $[n]$ commute with arbitrary base change,

$$
G[n]_{S'}\simeq G_{S'}[n].
$$

This identity is stronger than the corresponding statement about points. It transports all nilpotent structure in the torsion fiber.

If $G$ itself is finite locally free, then $G[n]$ is finite but may fail to be flat unless one proves the relevant quotient algebra flat. If $[n]:G\to G$ is faithfully flat, however, its kernel is finite locally free and

$$
0\to G[n]\to G\xrightarrow{[n]}G\to0
$$

is faithfully flat exact. This situation occurs for abelian schemes, though those schemes themselves are not finite.

### 4.2 Elementary computations

For the additive and multiplicative groups,

$$
\mathbf G_a[n]=\ker(x\mapsto nx),\qquad
\mathbf G_m[n]=\mu_n.
$$

If $n$ is zero on the base, $[n]$ on $\mathbf G_a$ is the zero map and its kernel is all of $\mathbf G_a$, which is not finite. Thus the notation $G[n]$ never by itself guarantees finiteness.

For a constant finite abelian group $M$,

$$
\underline M[n]=\underline{M[n]}.
$$

For a diagonalizable group, arrow reversal gives

$$
D(M)[n]\simeq D(M/nM).
$$

Indeed a character $M\to C^\times$ is killed by $n$ precisely when it factors through $M/nM$. Consequently $\mu_m[n]\simeq\mu_{\gcd(m,n)}$ after interpreting the evident cyclic quotient; its rank is $\gcd(m,n)$ over every base, even where it is nonreduced.

### 4.3 Prime-power decomposition

Suppose a finite flat commutative group $G$ is killed by an integer $N=ab$ with $(a,b)=1$. Choose integers $r,s$ with $ra+sb=1$. Then

$$
e_a=[sb],\qquad e_b=[ra]
$$

are complementary idempotent endomorphisms of $G$, with images $G[a]$ and $G[b]$ in the appropriate order. The map

$$
G[a]\times G[b]\longrightarrow G
$$

given by addition is an isomorphism, with inverse formed from these idempotents. This proof is scheme-theoretic because it is an identity of endomorphisms, not a decomposition of geometric points.

Iterating yields the canonical primary decomposition

$$
G\simeq\prod_{\ell\mid N}G[\ell^{v_\ell(N)}].
$$

It permits local questions to be reduced to prime-power order. The difficult prime is the residue characteristic; prime-to-residue-characteristic parts tend to be étale, while the primary part at the residue characteristic can carry connected infinitesimal structure.

### 4.4 When order kills the group

There is a scheme-theoretic analogue of Lagrange's theorem. If $G$ is a finite locally free commutative group scheme of constant order $N$, then

$$
[N]_G=0.
$$

The proof uses the finite-flat summation law. If $X\to T$ is finite locally free of rank $N$ and $H/T$ is commutative, a section $u:X\to H$ has a functorial sum $\Sigma_{X/T}(u)\in H(T)$. On a split cover $X=\coprod_{i=1}^NT$ it is the ordinary sum of the $N$ component sections; in general it is obtained from the degree-$N$ symmetric power, and the symmetric polynomial formulas descend it. This construction commutes with base change.

Apply it after any $T\to S$ to $X=G_T$ and the identity map $u:G_T\to G_T$. Let $a\in G(T)$ and translate the source by $a$. Functoriality of the sum under automorphisms of $X$ says

$$
\Sigma(u\circ\tau_a)=\Sigma(u).
$$

But $u\circ\tau_a=u+a$, so additivity of finite-flat summation gives

$$
\Sigma(u\circ\tau_a)=\Sigma(u)+Na.
$$

Hence $Na=0$. This holds naturally for every $T$ and every $a\in G(T)$, so the Yoneda principle gives $[N]_G=0$. The argument sums the whole finite scheme with multiplicity; it never replaces it by its geometric point set.

If rank varies on a disconnected base, $G$ is killed on each clopen rank stratum by the corresponding order, and one common multiple kills it globally. In applications to abelian schemes we will usually retain an explicitly chosen annihilator $n$, since that identifies the particular ambient kernel $A[n]$ in which closure is taken.

### 4.5 Tangent space as a diagnostic, not a classifier

Let $I_e=\ker(\varepsilon:\mathcal O(G)\to R)$. The conormal module at the identity is $I_e/I_e^2$, and its dual is the tangent module $\operatorname{Lie}(G)$. For $G[n]$, the differential of $[n]$ is multiplication by $n$ on $\operatorname{Lie}(G)$. Thus, where $n$ is invertible, an $n$-torsion kernel of a smooth group has zero tangent space and is étale when it is finite flat.

In characteristic dividing $n$, the differential may vanish and infinitesimal torsion becomes possible. Yet the tangent space is only first order: $\alpha_p$ and $\mu_p$ have the same tangent dimension. Rank, full coordinate algebra, and coproduct remain indispensable.

### 4.6 Exact sequences among the standard groups

Concrete exact sequences show how the abstract definitions behave when the order is not invertible. For positive integers $a,b$, raising to the $a$th power gives

$$
0\longrightarrow\mu_a\longrightarrow\mu_{ab}
\xrightarrow{[a]}\mu_b\longrightarrow0.
$$

The last map is faithfully flat: on coordinates, $R[V]/(V^b-1)$ maps to $R[T]/(T^{ab}-1)$ by $V\mapsto T^a$, and the target is free with basis $1,T,\ldots,T^{a-1}$. The kernel equation is $T^a=1$. Thus exactness and the rank identity $ab=a\cdot b$ hold over every base, including residue characteristics dividing $ab$.

In characteristic $p$, write

$$
\alpha_{p^r}=\ker(F^r:\mathbf G_a\to\mathbf G_a)
=\operatorname{Spec}k[T]/(T^{p^r}).
$$

Frobenius gives

$$
0\longrightarrow\alpha_p\longrightarrow\alpha_{p^r}
\xrightarrow{F}\alpha_{p^{r-1}}\longrightarrow0.
$$

On coordinate rings the map sends the target coordinate to $T^p$, and $k[T]/(T^{p^r})$ is free of rank $p$ over $k[T^p]/(T^{p^r})$. The sequence is faithfully flat exact although every group in it has only one geometric point. It is a compact demonstration that the torsor and rank definitions, rather than pointwise exactness, are indispensable.

## 5. Fibers over fields

### 5.1 Artinian geometry at the identity

Let $G$ be a finite group scheme over a field $k$. Its coordinate algebra is finite-dimensional and therefore Artinian. It decomposes uniquely as a product of local Artinian algebras, so $G$ is a finite disjoint union of connected open-and-closed subschemes. The component containing the identity is denoted

$$
G^0.
$$

It is a closed subgroup scheme. Multiplication maps the connected scheme $G^0\times G^0$ into the component containing the identity, and inversion preserves that component. Every component becomes a translate of $G^0$ after a field extension over which it has a point.

This decomposition separates two kinds of information. The identity component measures infinitesimal and local behavior; the component quotient measures discrete behavior. Neither can be recovered merely from the order. A connected finite scheme can have arbitrarily large length at one point, while an étale group of the same order has that many geometric points.

### 5.2 Reduced, smooth, and étale

For a finite type scheme over a field, finite étale means finite, flat, and geometrically reduced. For a finite group scheme, translations make smoothness uniform: it is enough to test the cotangent space at the identity after extension to an algebraic closure. Thus the following are equivalent:

1. $G$ is finite étale over $k$;
2. $G_{\bar k}$ is reduced;
3. $G_{\bar k}$ is a disjoint union of $|G|$ points;
4. $\operatorname{Lie}(G_{\bar k})=0$.

The implication from the tangent condition uses the Artinian local structure. If $A$ is a local Artinian algebra over an algebraically closed field with maximal ideal $\mathfrak m$ and $\mathfrak m/\mathfrak m^2=0$, Nakayama gives $\mathfrak m=0$. Translation then handles every point.

If $k$ is perfect, reducedness over $k$ already implies geometric reducedness, so a reduced finite group scheme is étale. This fails over an imperfect field. A reduced purely inseparable field algebra becomes nonreduced after passing to an algebraic closure. Perfectness may therefore be omitted only when geometric reducedness is stated directly.

### 5.3 The connected-étale sequence over a perfect field

Assume now that $k$ is perfect. The identity component $G^0$ is finite connected, and the quotient theorem produces an exact sequence

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0,
$$

where $G^{\mathrm{et}}=G/G^0$ is finite étale. Its rank is the number of geometric connected components, and

$$
|G|=|G^0|\,|G^{\mathrm{et}}|.
$$

The quotient is maximal among finite étale quotients: every map from $G$ to a finite étale group kills $G^0$, because the image of a connected scheme containing the identity lies in the identity component, which for an étale scheme is a point. Dually in the categorical, not Cartier-dual, sense, $G^0$ is the kernel of the maximal discrete quotient.

The sequence need not split over $k$. After a separable extension the étale quotient becomes constant, but lifting its points may still define nontrivial torsors under $G^0$. Even when it splits, the splitting is additional structure and need not be canonical.

Without perfection, $G/G^0$ need not be étale in the desired geometric sense. One may still form the component quotient under standard finite-group-scheme results, but inseparable residue extensions obstruct the clean connected–étale conclusion. We will retain the perfectness hypothesis whenever this exact sequence is used.

### 5.4 Frobenius as a separator

In characteristic $p$, relative Frobenius

$$
F_{G/k}:G\longrightarrow G^{(p)}
$$

is an isomorphism for finite étale $G$. Its kernel measures an infinitesimal layer of a nonétale group. For $\mathbf G_a$ and $\mathbf G_m$ the kernels are $\alpha_p$ and $\mu_p$ respectively.

Repeated Frobenius often filters a connected $p$-group by smaller infinitesimal pieces. We do not classify those pieces here. The point is methodological: Frobenius sees structure that geometric points do not, but even its kernel does not by itself identify the group. The additive and multiplicative kernels again provide the counterexample.

### 5.5 Three rank-$p$ fibers

Over an algebraically closed field of characteristic $p$, compare

$$
\underline{\mathbf Z/p\mathbf Z},\qquad \mu_p,\qquad \alpha_p.
$$

The first is étale, has $p$ points, and has trivial identity component. The last two are connected and have one point. Their conormal spaces both have dimension one, but their coproducts differ. Therefore each successive invariant—order, point count, connectedness, tangent space—adds information, yet none before the full Hopf structure classifies even this elementary list.

This hierarchy is essential when a generic étale representation specializes. The special fiber may become any mixture of étale components and connected local structure while preserving total rank.

## 6. Finite étale groups and Galois modules

### 6.1 Why geometric points work in the étale case

The warning against geometric points has one important boundary. For a finite étale scheme over a field, geometric points carry all the scheme structure because there are no nilpotents and every residue extension is separable. The missing datum is descent, encoded by the absolute Galois group.

Let $k^s$ be a separable closure of $k$ and

$$
\Gamma_k=\operatorname{Gal}(k^s/k).
$$

If $G$ is finite étale and commutative over $k$, then

$$
M=G(k^s)
$$

is a finite abelian group with a continuous action of $\Gamma_k$. Continuity means every element has an open stabilizer; it is automatic for an action on a finite set once the action arises from a finite extension.

### 6.2 The equivalence over a field

**Theorem 6.1.** The functor

$$
G\longmapsto G(k^s)
$$

is an equivalence between finite étale commutative group schemes over $k$ and finite discrete abelian groups with continuous $\Gamma_k$-action.

**Proof strategy.** After scalar extension to $k^s$, a finite étale group scheme is constant. Its geometric points therefore determine it there. The descent datum on the constant scheme is exactly a continuous action of $\Gamma_k$ compatible with the group law.

More explicitly, a finite $\Gamma_k$-module $M$ is fixed pointwise by an open normal subgroup, so the action factors through a finite Galois extension $L/k$. Begin with the constant group $\underline M_L$. The finite group $\operatorname{Gal}(L/k)$ acts semilinearly on its coordinate algebra $L^M$, and the invariant algebra descends it to a finite étale $k$-algebra. Compatibility with addition descends the Hopf maps. Conversely, the canonical descent datum on $G_{k^s}$ yields the Galois action on its points. The two constructions are inverse by effective Galois descent. $\square$

Ranks become cardinalities under this equivalence, kernels and quotients become kernels and quotients of modules, and exact sequences agree. This is precisely because every object is étale. It would be false for all finite group schemes: both $\alpha_p(k^s)$ and $\mu_p(k^s)$ are trivial as abstract groups.

### 6.3 Unramified modules from a henselian DVR

Let $R$ be a henselian DVR with fraction field $K$ and residue field $k$. Finite étale schemes over $R$ are equivalent to finite étale schemes over $k$ by reduction. Their generic fibers correspond to finite étale $K$-schemes whose Galois action is unramified, meaning inertia acts trivially on geometric points.

For commutative groups, the same statement reads:

$$
\left\{\begin{array}{c}
\text{finite étale commutative}\ R\text{-groups}
\end{array}\right\}
\simeq
\left\{\begin{array}{c}
\text{finite }\Gamma_k\text{-modules}
\end{array}\right\}
\simeq
\left\{\begin{array}{c}
\text{finite unramified }\Gamma_K\text{-modules}
\end{array}\right\}.
$$

Henselianity is what lifts idempotents and finite étale algebras uniquely. Without it, a finite étale special fiber need not determine a unique global finite étale object. This equivalence concerns the étale subcategory only; a ramified generic module may still possess a finite-flat, nonétale integral model.

### 6.4 Specialization of points

For a finite étale group over a henselian DVR, geometric generic points and geometric special points are canonically related after choosing compatible separable closures, and inertia is exactly what disappears in specialization. For a general finite flat group, there is no bijection of point sets to specialize: several generic points can meet one nonreduced special point.

The correct specialization is the base-change functor

$$
G\longmapsto G_k,
$$

which preserves rank and all Hopf operations. Only after proving $G_k$ étale may one replace that fiber by its geometric points. This order of operations prevents the common but false inference that constant generic rank implies constant point count.

## 7. Henselian local bases and connected-étale structure

### 7.1 Lifting the special-fiber decomposition

Let $(R,\mathfrak m,k)$ be a henselian local ring and let $G$ be finite locally free over $R$. A finite $R$-algebra is a product of finite local $R$-algebras according to the idempotents of its special fiber: henselianity lifts those idempotents uniquely. Thus the open-and-closed components of $G_k$ lift uniquely to open-and-closed subschemes of $G$.

Assume in addition that $k$ is perfect. Let $G^0$ be the lifted component containing the identity of $G_k$. The group operations preserve it. This can be checked after reduction: multiplication and inversion send the corresponding special component into itself, and uniqueness of the lifted idempotent decomposition forces the same factorization over $R$.

The notation requires care. $G^0$ is characterized by having connected special fiber. Its generic fiber need not be connected. For instance, $\mu_p$ over a mixed-characteristic DVR has connected special fiber but étale, usually disconnected, generic fiber.

### 7.2 The local connected-étale sequence

Under the hypotheses just stated—$R$ henselian local, $G$ finite locally free and commutative, and $k$ perfect—the quotient theorem gives

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0.
$$

Here $G^0$ is finite locally free with connected special fiber, and $G^{\mathrm{et}}$ is finite étale over $R$.

To justify the last assertion, first reduce the quotient sequence modulo $\mathfrak m$. Its quotient is $(G_k)^{\mathrm{et}}$, hence étale over the perfect field $k$. The quotient $G^{\mathrm{et}}$ is finite locally free. Its module of relative differentials is finite, and its reduction modulo $\mathfrak m$ vanishes. Nakayama's lemma gives vanishing over $R$, so the quotient is unramified; finite locally free plus unramified is finite étale.

This sequence is functorial. A homomorphism $G\to H$ sends $G^0$ into $H^0$ because the special-fiber identity component maps into the identity component. It therefore induces a map on étale quotients. The construction also commutes with local homomorphisms of henselian local rings that preserve the relevant perfect-residue setting.

### 7.3 Maximality and rank

The quotient $G^{\mathrm{et}}$ is the maximal finite étale quotient of $G$. To see this, let $u:G\to E$ with $E$ finite étale. The identity section of $E$ is open and closed. Its inverse image in $G^0$ is therefore open and closed and contains the entire connected special fiber. The complement is finite over the local base and has empty special fiber, hence is empty by Nakayama's lemma. Thus $u|_{G^0}$ is trivial, so $u$ factors uniquely through $G/G^0$.

The rank formula reads

$$
|G|=|G^0|\,|G^{\mathrm{et}}|.
$$

It measures how much of the order lies in the connected special fiber and how much survives as an unramified discrete quotient. This is often the first structural invariant of a finite-flat model.

The sequence may fail to split, and even a splitting of the special fiber need not lift. A split product is therefore never implicit in the superscript “et.” Moreover, if the residue field is imperfect, the clean étaleness assertion can fail; if the local ring is not henselian, the special-fiber idempotents need not lift. Both hypotheses serve distinct purposes.

### 7.4 Base change and completion

Passing from a noetherian local ring to its completion is faithfully flat. A finite locally free group remains so, and morphisms, exact sequences, and ranks can be checked after completion. If the residue field is perfect, the connected–étale sequence of the completion is the pullback of that over the henselization whenever both are defined.

Completion can simplify coefficients, but it does not turn a generic-fiber morphism into an integral one automatically. Nor does an isomorphism after passing only to the fraction field descend. Faithful flatness helps when the objects and morphisms already exist before base change; it does not manufacture descent data for a morphism defined solely upstairs.

## 8. Schematic closure over a DVR

### 8.1 The extension problem

Let $R$ be a DVR with uniformizer $\pi$ and fraction field $K$. Let $G$ be a finite flat commutative $R$-group, and let

$$
H_K\hookrightarrow G_K
$$

be a closed subgroup of the generic fiber. The basic integral question is whether $H_K$ extends to a finite flat subgroup of $G$. The answer is canonical: take its scheme-theoretic closure.

Write $G=\operatorname{Spec}A$ and let $I_K\subset A_K=A\otimes_RK$ be the Hopf ideal of $H_K$. Define the contracted ideal

$$
I=A\cap I_K\subset A_K
$$

and put $\overline H=\operatorname{Spec}(A/I)$. It is the smallest closed subscheme of $G$ whose generic fiber contains $H_K$, and its generic fiber equals $H_K$.

### 8.2 Finiteness and flatness of the closure

**Theorem 8.1.** In the preceding situation, $\overline H$ is a finite flat closed subgroup scheme of $G$, and formation of $\overline H$ commutes with flat extensions of DVRs.

**Proof strategy.** Finiteness is inherited from the finite ambient scheme; flatness comes from saturation; Hopf stability is proved only after the quotient has been shown torsion-free.

Set $C=A/I$. Since $I$ is the contraction of $I_K$, the natural map

$$
C\longrightarrow A_K/I_K
$$

is injective. Hence $C$ is $R$-torsion-free. It is finite because it is a quotient of the finite $R$-module $A$. A finite torsion-free module over a DVR is free, so $C$ is finite flat.

It remains to prove that $I$ is a Hopf ideal. Because $C$ is finite free, the quotient sequence

$$
0\to I\to A\to C\to0
$$

splits as $R$-modules. Consequently

$$
\ker(A\otimes A\to C\otimes C)=I\otimes A+A\otimes I.
$$

For $x\in I$, the image of $\Delta(x)$ in $(C\otimes C)_K$ vanishes because $I_K$ is a Hopf ideal. The module $C\otimes C$ is torsion-free, so its image already vanishes over $R$. This proves the coproduct condition. Likewise $\varepsilon(x)$ and the image of $\iota(x)$ vanish after passing to $K$; torsion-freeness of $R$ and contraction of $I$ give the counit and antipode conditions. Thus $I$ is Hopf.

For a flat extension $R\to R'$ of DVRs, contraction commutes with scalar extension because the relevant quotient sequence remains exact and saturated. Equivalently, both candidates are finite flat closed subschemes with the same generic fiber, and the uniqueness argument of the next section identifies them. $\square$

The order of the proof matters. Generic Hopf stability alone cannot be pulled back through a tensor product until the quotient is known torsion-free. Saturation supplies exactly that missing injectivity.

### 8.3 Saturated Hopf ideals and uniqueness

An ideal $I\subset A$ is **saturated** if $A/I$ is torsion-free, equivalently if

$$
\pi a\in I\quad\Longrightarrow\quad a\in I.
$$

Contracting an ideal from $A_K$ produces a saturated ideal, and every saturated ideal is recovered from its generic extension:

$$
I=A\cap I_K.
$$

It follows that the closure is the unique finite flat closed subgroup $H\hookrightarrow G$ with generic fiber $H_K$. Indeed the ideal of any such $H$ is saturated and has generic extension $I_K$, hence equals $A\cap I_K$.

Uniqueness is relative to the fixed ambient model $G$. It does not say that an abstract generic group has only one finite-flat model. Nor does it hold among nonflat closed subgroup schemes: one may add equations supported on the special fiber without changing the generic fiber. Flatness excludes precisely these vertical thickenings and shrinkings.

### 8.4 Intersections, sums, and generated subgroups

Let $H_{1,K},H_{2,K}\subset G_K$ and let $H_1,H_2\subset G$ be their closures. The closure of the generic intersection is the flat closure of the scheme-theoretic intersection $H_1\cap H_2$. The raw intersection need not be flat because its coordinate algebra is a tensor product over $\mathcal O(G)$ and may acquire torsion. Saturating its ideal repairs it.

Likewise, the image of $H_1\times H_2\to G$ under addition should be replaced by its flat schematic image. Over the generic fiber this is the subgroup sum $H_{1,K}+H_{2,K}$; its closure gives the corresponding finite flat subgroup over $R$. These qualifications are not pedantry: intersections and images are exactly where torsion can enter an otherwise finite-free calculation.

The operations are compatible with flat base change and obey the expected order relations. Rank inequalities follow from exact sequences, but an equality such as

$$
|H_1+H_2|\,|H_1\cap H_2|=|H_1|\,|H_2|
$$

requires the relevant intersection and image to mean their finite-flat versions and follows by applying rank multiplicativity to the kernel and image of $H_1\times H_2\to G$.

### 8.5 Extending generic morphisms

Suppose $G$ and $H$ are finite flat over $R$. A morphism $f_K:G_K\to H_K$ has a graph, a closed subgroup of $(G\times H)_K$. Its closure $\Gamma\subset G\times H$ is finite flat. The first projection $\Gamma\to G$ is an isomorphism on generic fibers, but it need not be an isomorphism over $R$. Thus $f_K$ need not extend.

If the first projection is an isomorphism—equivalently, if the graph closure is the graph of an $R$-morphism—then the extension exists. It is unique: two maps $G\to H$ agreeing generically induce equal maps on coordinate algebras because $\mathcal O(G)$ is torsion-free. Hence the generic-fiber functor is faithful but generally not full.

A useful sufficient condition is that the schematic graph closure project isomorphically, which may be checked after a faithfully flat base change. In the finite étale unramified category over a henselian DVR, every generic morphism between extendable unramified objects does extend uniquely, because the category is already equivalent to residue-field Galois modules. Outside that subcategory, integrality imposes genuine constraints.

### 8.6 Images over a DVR

For a morphism $f:G\to H$ of finite flat $R$-groups, take the schematic image $I_K$ of $f_K$ over the field $K$ and close it in $H$. The result $I$ is finite flat. The map $f$ factors through $I$: on coordinate rings, functions vanishing on $I$ vanish after pullback generically and hence vanish in the torsion-free algebra $\mathcal O(G)$.

The induced map $G\to I$ need **not** be faithfully flat. The equal-characteristic morphism $G_1\to G_t$ of §9.4, given generically by multiplication by $t$, is a generic-fiber isomorphism but is not an integral isomorphism. Its generic image closure is all of $G_t$. Were $G_1\to G_t$ faithfully flat, its equal rank would make it finite locally free of rank one and hence an isomorphism, a contradiction.

Thus closure produces a useful **flat schematic image object**, but not automatically an image factorization in the exact category. The factorization

$$
G\twoheadrightarrow I\hookrightarrow H
$$

with faithfully flat first arrow exists precisely when the induced map to $I$ is faithfully flat; equivalently, its coordinate algebra is faithfully flat over $\mathcal O(I)$. This holds for admissible quotient maps and after quotienting by a finite-flat kernel when the resulting map is known to identify with the closure. It does not hold for every morphism. The distinction is why finite flat group schemes over a DVR do not form an abelian category under all morphisms.

## 9. Local models and their generic fibers

### 9.1 Finite flat groups over a local ring

Let $(R,\mathfrak m,k)$ be local. The coordinate algebra of a finite flat group is finite free. Thus every object has a well-defined integer order

$$
|G|=\dim_k\mathcal O(G_k),
$$

and any chosen lift of a $k$-basis of the special fiber can be tested for being an $R$-basis by Nakayama's lemma. This turns many local constructions into matrix calculations, but the chosen basis has no intrinsic meaning. The Hopf operations, augmentation ideal, and rank do.

A closed subgroup $H\subset G$ is finite flat precisely when its coordinate quotient is flat. Over a general local ring, flatness of this finite quotient makes it free. If the base is noetherian, no separate finite-presentation argument is needed. Thus the hard part of constructing local subgroup schemes is almost always flatness, not finiteness.

Reduction modulo $\mathfrak m$ preserves order but not point count or connectedness. Generic and special fibers are different views of one free Hopf algebra, not independent groups that happen to have equal rank.

### 9.2 The DVR lattice picture

Over a DVR $R$, a finite flat Hopf algebra $A$ is an $R$-lattice in the finite-dimensional Hopf $K$-algebra $A_K$. Conversely, an $R$-lattice $A\subset A_K$ defines a finite flat model when it contains $1$, is an $R$-subalgebra, and is stable under coproduct, counit, and antipode in the sense

$$
\Delta(A)\subset A\otimes_RA,\qquad
\varepsilon(A)\subset R,\qquad
\iota(A)\subset A.
$$

Different stable lattices in the same generic Hopf algebra can give different models. Two lattices are commensurable: each lies between a power of $\pi$ times the other and its inverse scaling. But a change of lattice need not respect the unit and Hopf maps, so classification is subtler than classification of free modules.

For a finite $R$-algebra, flatness is equivalent to injectivity into its generic fiber. This is why schematic closure works so cleanly over a DVR and why the same proof does not automatically generalize to higher-dimensional bases, where torsion-free need not imply flat.

### 9.3 The generic-fiber and special-fiber functors

There are base-change functors

$$
G\longmapsto G_K,\qquad G\longmapsto G_k.
$$

Both preserve products, torsion kernels when those kernels are finite flat, and faithfully flat exact sequences. Both preserve order. Their qualitative behavior differs sharply.

The generic-fiber functor is faithful: if two morphisms $G\to H$ agree over $K$, their pullbacks $\mathcal O(H)\to\mathcal O(G)$ agree because $\mathcal O(G)$ is torsion-free. It is not generally full, as an isomorphism between two generic fibers may fail to preserve the chosen integral Hopf lattices. It is not injective on isomorphism classes: distinct integral models can have isomorphic generic fibers.

The special-fiber functor is neither faithful nor conservative in comparable generality. A morphism divisible by $\pi$ at the level of a suitable coordinate difference may reduce to zero without being zero. Two nonisomorphic models can also have isomorphic special fibers. What specialization reliably preserves is the full base-changed Hopf algebra and its length, not enough data to reconstruct the original lattice.

### 9.4 Two models of one generic additive group

Return to $R=k[[t]]$ in characteristic $p$. Let

$$
G_1=\operatorname{Spec}R[X]/(X^p-X),
$$

$$
G_t=\operatorname{Spec}R[Y]/(Y^p-t^{p-1}Y),
$$

with primitive coordinates. Both are finite flat of order $p$. The substitution $Y=tX$ gives an isomorphism over $K=k((t))$.

It cannot extend to an isomorphism over $R$. The special fiber of $G_1$ is finite étale, whereas that of $G_t$ is $\alpha_p$. Equivalently, an inverse would require division by $t$, which does not preserve the integral lattice. This example proves simultaneously that the generic-fiber functor is not full and not essentially injective.

There is nevertheless a nonisomorphic integral morphism $G_1\to G_t$ in one direction, reflected by inclusion of one Hopf lattice in another. Its generic fiber is an isomorphism, while its special fiber is the zero map from an étale group to a connected group. Its scheme-theoretic kernel has trivial generic fiber and special fiber $G_{1,k}$, so it is not flat. This single morphism proves that arbitrary kernels and cokernels need not remain in the finite-flat category. The generic category has forgotten this valuation depth completely.

### 9.5 Constant and multiplicative models in mixed characteristic

Let $R$ be a mixed-characteristic DVR of residue characteristic $p$ containing a primitive $p$th root of unity $\zeta_p$. Then the generic fiber of $\mu_p$ is split étale and hence isomorphic to the constant group $\underline{\mathbf Z/p\mathbf Z}_K$. Over $R$, however,

$$
\mu_p\not\simeq\underline{\mathbf Z/p\mathbf Z}_R.
$$

Their special fibers distinguish them: $\mu_p$ is connected and nonreduced, while the constant group is étale with $p$ components. Thus even in characteristic zero on the generic fiber, and even for a split representation, integral models need not be unique.

This phenomenon is not a defect. The choice of model records how generic torsion approaches the special fiber. Different models correspond to different integral extension behavior, precisely the information needed in arithmetic deformation conditions.

### 9.6 Criteria that restore uniqueness

Several uniqueness statements coexist and must not be confused.

First, inside a **fixed finite flat ambient group** $G$, a generic closed subgroup has a unique finite flat closed extension: its schematic closure. Second, a morphism between fixed models has at most one extension from the generic fiber. Third, in the finite étale subcategory over a henselian DVR, an unramified generic object has a unique finite étale model, and its morphisms extend uniquely.

None of these says that an abstract ramified or residue-characteristic generic group has a unique finite-flat model. Uniqueness can sometimes be recovered from extra hypotheses—for example, requiring the model to be finite étale, specifying an embedding into a fixed ambient torsion group, or imposing a rigidity theorem in a restricted range of ramification. Such extra criteria must be named. Generic isomorphism alone is insufficient.

### 9.7 Beyond DVRs

Let $S$ be a Dedekind scheme. At every closed point, the local ring is a DVR, so closure, saturation, and rank arguments can be performed locally. A generic subgroup of a finite flat $S$-group has a closure that is finite over $S$ and torsion-free. Over a Dedekind domain, finite torsion-free modules are projective, so the closure is finite locally free. The local closures glue because they are all defined by contraction of the same generic ideal.

Over a higher-dimensional normal base, a finite torsion-free module need not be locally free. The schematic closure of a generic subgroup is still finite and torsion-free, but may fail to be flat along codimension at least two. Reflexive hulls can repair module-theoretic depth while destroying algebra or Hopf compatibility. Thus the clean closure theorem is genuinely one-dimensional unless stronger hypotheses are supplied.

## 10. Torsion on abelian schemes

### 10.1 Why a proper smooth group enters a finite theory

An abelian scheme $A\to S$ is proper and smooth with geometrically connected fibers, so it is far from finite. Its multiplication kernels, however, are the principal source of finite flat group schemes in arithmetic geometry. The surrounding smooth proper group provides enough rigidity to prove flatness and enough geometry to produce pairings and isogenies later.

Let $A/S$ have relative dimension $g$. For every integer $n\ge1$, multiplication

$$
[n]:A\longrightarrow A
$$

is a finite locally free, faithfully flat morphism of degree $n^{2g}$. Consequently

$$
A[n]=\ker[n]
$$

is a finite flat commutative group scheme of order $n^{2g}$, and

$$
0\to A[n]\to A\xrightarrow{[n]}A\to0
$$

is exact for the faithfully flat topology.

### 10.2 Why multiplication is finite flat

The proof has several geometric ingredients. Fiberwise, $[n]$ is an isogeny of abelian varieties: it is proper, has finite kernel, and is surjective. Proper and quasi-finite implies finite. Translation makes the local behavior uniform, and the standard degree calculation for an abelian variety gives degree $n^{2g}$ on every geometric fiber.

Flatness follows from the fiberwise constant degree together with the Cohen–Macaulay regularity supplied by smooth source and target, or equivalently from the standard isogeny theorem for abelian schemes. Once $[n]$ is finite locally free, its kernel is the base change along the identity section and is therefore finite locally free of the same degree. This proof does not require $n$ invertible on $S$.

If $n$ is invertible on $S$, the differential of $[n]$ is multiplication by $n$ and is an isomorphism. Hence $A[n]$ is finite étale. When a residue characteristic divides $n$, the kernel may have connected nonreduced fibers, but its order remains $n^{2g}$.

### 10.3 Elliptic curves

For an elliptic scheme $E/S$, the formula becomes

$$
|E[n]|=n^2.
$$

Over a field of characteristic prime to $n$, $E[n]$ is finite étale and over a separable closure its points form $(\mathbf Z/n\mathbf Z)^2$. This recovers the familiar two-dimensional torsion module, now as the geometric points of a scheme whose integral specializations remain meaningful.

In characteristic $p$, the connected–étale sequence of $E[p]$ detects the ordinary or supersingular character. Over a perfect algebraically closed field, an ordinary elliptic curve has connected part of order $p$ of multiplicative type and étale quotient of order $p$:

$$
0\to\mu_p\to E[p]\to\underline{\mathbf Z/p\mathbf Z}\to0.
$$

The sequence records the structure needed here; a splitting should not be silently assumed over a smaller field or base. For a supersingular elliptic curve, $E[p]$ is connected of order $p^2$. It contains subtler infinitesimal structure and is not generally the product $\alpha_p\times\alpha_p$. Thus the abstract group of geometric $p$-torsion points—trivial in the supersingular case—does not measure the order of the kernel.

### 10.4 Subgroups and isogenies

Let $H\hookrightarrow A$ be a finite locally free subgroup of an abelian scheme. The faithfully flat quotient sheaf $A/H$ is represented by an abelian scheme, and

$$
A\longrightarrow A/H
$$

is an isogeny with kernel $H$. The quotient map is finite locally free of degree $|H|$. Properness descends, smoothness follows after the torsor cover, and the fibers remain geometrically connected group varieties.

Conversely, the kernel of an isogeny of abelian schemes is finite locally free. Thus finite flat subgroup schemes and isogenies are two views of the same operation. The rank formula becomes the degree formula

$$
\deg(A\to A/H)=|H|.
$$

The theorem uses representability of quotients by finite locally free subgroup schemes in the abelian-scheme setting. A mere finite closed subgroup that is not flat does not meet its hypotheses.

### 10.5 Rational subgroups versus subgroup schemes

Over a field where $n$ is invertible, a Galois-stable subgroup of $A[n](k^s)$ corresponds to a finite étale subgroup scheme by the Galois-module equivalence. In residue characteristic dividing $n$, a subgroup of geometric points can see only the étale part. It cannot specify a connected subgroup such as $\mu_p$ or $\alpha_p$.

Therefore “a rational subgroup” has two possible meanings. It may mean a Galois-stable subgroup of geometric points in the étale case, or it may mean a subgroup scheme defined over the field. Only the second meaning is safe in arbitrary characteristic. The passage between them requires an étaleness hypothesis.

## 11. Closing generic subgroups in abelian schemes

### 11.1 Reduction to a finite ambient torsion group

Let $R$ be a DVR, $K$ its fraction field, and $A/R$ an abelian scheme. Suppose

$$
H_K\hookrightarrow A_K
$$

is a finite commutative subgroup scheme killed by an integer $n$. Then $H_K$ lies in $A_K[n]$. Since $A[n]$ is finite flat over $R$, we can take the schematic closure of $H_K$ inside this finite ambient group.

By Theorem 8.1 the closure $H$ is finite flat over $R$. Because $A[n]\hookrightarrow A$ is closed, closure inside $A[n]$ agrees with closure inside $A$. We have therefore proved:

**Theorem 11.1.** A finite generic-fiber subgroup of an abelian scheme over a DVR, together with an integer annihilating it, extends uniquely to a finite flat closed subgroup of the abelian scheme.

This proof is stronger and cleaner than trying to show directly that a closure in a proper scheme is quasi-finite. The multiplication kernel supplies finiteness before closure is taken.

### 11.2 Closure and quotient isogenies

With $H$ as above, the quotient $A/H$ is an abelian scheme and

$$
A\longrightarrow A/H
$$

extends the generic isogeny $A_K\to A_K/H_K$. Its degree is $|H_K|=|H|$. Thus a generic isogeny whose kernel sits in an abelian scheme extends through the closure of its kernel, provided both source and the chosen abelian model are in place.

This does not assert that every homomorphism between arbitrary abelian varieties over $K$ extends to arbitrarily chosen integral models. Proper smooth models and their extension properties matter. Here the quotient is constructed from a subgroup of the fixed abelian scheme, so the extension is intrinsic.

### 11.3 Elliptic cyclic subgroups

Let $E/R$ be an elliptic scheme and let $C_K\subset E_K[n]$ be a finite étale cyclic subgroup of order $n$ over $K$. Its closure $C\subset E[n]$ is finite flat of order $n$. If $n$ is invertible in $R$, $E[n]$ is étale and $C$ is the unique finite étale extension. If the residue characteristic divides $n$, $C$ can specialize to a connected or mixed group even though $C_K$ is étale.

The quotient $E/C$ is again an elliptic scheme, and the map $E\to E/C$ is an isogeny of degree $n$. This is the integral meaning of extending a cyclic isogeny. The special-fiber kernel must be read as a group scheme; its geometric point count may be smaller than $n$.

### 11.4 Intersections of torsion subgroup schemes

If $H_K\subset A_K[m]$ and $J_K\subset A_K[n]$, both may be placed in $A_K[\operatorname{lcm}(m,n)]$. Their closures can then be intersected and saturated inside one finite flat ambient group. The resulting flat intersection is the closure of $H_K\cap J_K$. Their flat sum is the closure of the image under addition.

This common-ambient method is important: uniqueness of closure applies only after the ambient integral model has been fixed. It also gives clean rank identities from the exact sequence

$$
0\to H\cap J\to H\times J\to H+J\to0,
$$

where intersection and sum mean the saturated finite-flat constructions. Hence

$$
|H\cap J|\,|H+J|=|H|\,|J|.

$$

### 11.5 Good reduction and torsion

An elliptic curve over $K$ with an elliptic scheme model over $R$ has good reduction. Its prime-to-residue-characteristic torsion extends étale, and specialization can be understood through unramified Galois modules. Residue-characteristic torsion also extends, but generally only as a finite flat group scheme. Its connected part contains arithmetic information invisible in the generic étale point set.

This is the bridge from the torsion theory of elliptic curves to integral representation theory: the generic fiber supplies a Galois module, while the finite flat closure supplies the permitted behavior at the residue characteristic.

## 12. Exact calculus over arithmetic bases

### 12.1 Subobjects

For a general base $S$, a **finite-flat subgroup** of $G\in\mathrm{FFCG}(S)$ means a closed subgroup $H\hookrightarrow G$ that is itself finite locally free over $S$. This adjective cannot be dropped. A finite closed subgroup may have a coordinate algebra with torsion and lie outside the category.

Intersections of finite-flat subgroups are closed and finite, but need not be flat on an arbitrary base. Whenever their scheme-theoretic intersection is flat and finitely presented, it is the categorical pullback in $\mathrm{FFCG}(S)$. Over a field this is automatic. Over a DVR or Dedekind scheme, saturation produces the appropriate finite-flat intersection.

The same warning applies to kernels. Thus $\mathrm{FFCG}(S)$ is not naively an abelian category for arbitrary $S$: one must verify that algebraic kernels, images, and quotients remain flat.

### 12.2 Quotients

Quotients behave better once the subgroup is known finite flat. If $H\hookrightarrow G$ is a finite-flat subgroup, the quotient $G/H$ exists, is finite locally free, and gives an exact sequence

$$
0\to H\to G\to G/H\to0.
$$

Its formation commutes with arbitrary base change because the represented torsor quotient base-changes. It is unsafe to prove this by commuting a raw invariant equalizer with a nonflat tensor product; invariants need not commute with such tensoring in isolation. One should base-change the quotient and torsor, then recover the invariant description.

Successive quotients satisfy the expected third-isomorphism law. If $H\subset J\subset G$ are finite-flat subgroups and the inclusions are compatible, then $J/H$ is a finite-flat subgroup of $G/H$ and

$$
(G/H)/(J/H)\simeq G/J.
$$

The proof is the universal property of faithfully flat sheaf quotients, with representability provided by finite local freeness.

### 12.3 Extensions

An extension of $G''$ by $G'$ is a faithfully flat exact sequence

$$
0\to G'\to G\to G''\to0.
$$

If the end terms are finite locally free, then so is $G$, because the torsor becomes $G''\times G'$ after a faithfully flat cover and finite local freeness descends. Orders multiply. Pullback along $H''\to G''$ and pushout along a suitable quotient map $G'\to H'$ preserve finite flatness when the resulting sheaf quotient is represented by the finite-flat quotient theorem.

The middle term is not determined by the end terms. A split extension is their product, but nonsplit extensions record genuinely new integral information. This observation is the categorical reason that a local condition on representations must be stable under extensions rather than merely list simple objects.

### 12.4 Annihilators and primary parts

If $G$ is killed by $N$, every subgroup, quotient, and extension constructed above is killed by $N$ or by a controlled product of annihilators. Coprime primary decompositions commute with base change and exact sequences. Therefore the full category of $N$-torsion objects decomposes as a product of its prime-power subcategories.

Over a local base of residue characteristic $p$, the prime-to-$p$ subcategory is finite étale when the groups arise as kernels in smooth groups or, more generally, when multiplication by the relevant prime is étale. The $p$-primary subcategory retains the connected phenomena. One should prove étaleness from the cotangent criterion or a structural theorem, not merely from the order being prime to a point count.

### 12.5 Homomorphisms and base change

For finite locally free $G,H$, the functor of group homomorphisms is constrained by finitely many equations among finite projective coordinate modules. Equality of two morphisms can be checked after faithfully flat base change. Over a domain, it can also be checked on the generic fiber when the coordinate algebra of the source is torsion-free.

Existence does not descend from a single generic fiber or geometric fiber. A morphism after a faithfully flat cover descends only when its two pullbacks agree. A Galois-equivariant map of generic geometric points extends to finite étale models over a henselian DVR, but a map between nonétale finite-flat models must also preserve their Hopf lattices.

### 12.6 Internal linear constructions

The coordinate algebra $A$, augmentation ideal $A^+$, conormal module $A^+/(A^+)^2$, module dual $A^\vee$, tensor powers, exterior powers, and determinant line are finite projective whenever the indicated quotient is locally free. They commute with arbitrary base change in the finite projective cases. These constructions are useful for ranks, invariant differentials, tangent spaces, and determinant calculations.

The module dual $A^\vee$ also carries natural convolution operations derived from $\Delta$, but turning it into the coordinate algebra of a dual group and proving biduality requires a separate theory. We use no such identification here. Similarly, a perfect pairing $G\times H\to\mu_n$ may be studied through its induced maps, but the systematic duality formalism is postponed. This boundary prevents an unproved “dual” from being used to justify exactness or flatness.

### 12.7 Rank bookkeeping

On every connected component where ranks are constant, the reliable formulas are

$$
|G\times H|=|G|\,|H|,
$$

$$
|G|=|H|\,|G/H|,
$$

and, for an exact sequence,

$$
|G|=|G'|\,|G''|.
$$

For a flat image factorization $G\twoheadrightarrow I\hookrightarrow H$,

$$
|G|=|\ker f|\,|I|.
$$

For finite-flat subgroup sums over a DVR or field,

$$
|H+J|\,|H\cap J|=|H|\,|J|.
$$

Every formula follows from a torsor rank calculation. None should be proved by counting geometric points unless all groups involved have first been shown étale.

## 13. Models of finite Galois modules

### 13.1 From a generic group to a representation

Let $R$ be a DVR with fraction field $K$, and assume that a positive integer $N$ is invertible in $K$. Every finite $K$-group scheme killed by $N$ that is finite étale corresponds to a finite discrete $\Gamma_K$-module. In mixed characteristic $(0,p)$, this applies in particular to all finite group schemes of $p$-power order over $K$, since characteristic zero makes them étale.

If $G$ is a finite flat $R$-group killed by $N$, its generic fiber therefore yields

$$
M_G=G(K^s)
$$

with continuous Galois action. The integral group $G$ is a **finite-flat model** of this generic module. It contains more information than $M_G$: its special fiber records the allowed collision and infinitesimal structure.

### 13.2 The category of models of a fixed module

Fix a finite $\Gamma_K$-module $M$, and let $G_M/K$ be its finite étale group scheme. A finite-flat model of $M$ is a pair

$$
(G,\eta),\qquad
G\in\mathrm{FFCG}(R),\quad
\eta:G_K\xrightarrow{\sim}G_M.
$$

A morphism $(G,\eta)\to(H,\theta)$ is a morphism $f:G\to H$ whose generic fiber satisfies

$$
\theta\circ f_K=\eta
$$

when the underlying fixed generic object is the same; for models of varying modules, the right side is replaced by the chosen Galois-module map. Because the generic-fiber functor is faithful, there is at most one integral morphism lifting a given generic map.

There may be several objects and no morphism realizing a chosen generic isomorphism between them. The models $G_1$ and $G_t$ of §9.4 and the constant/multiplicative pair of §9.5 are concrete witnesses. Hence “the finite-flat model” is meaningful only after a uniqueness theorem or an ambient closure construction has been specified.

### 13.3 Submodules

Let $(G,\eta)$ model $M$, and let $M'\subset M$ be a Galois-stable subgroup. It determines a generic subgroup $G_{M'}\subset G_K$. Over a DVR, its schematic closure $G'\subset G$ is finite flat and is the unique finite-flat subgroup of this fixed $G$ with generic fiber $M'$. The quotient $G/G'$ models $M/M'$.

Thus a chosen finite-flat model makes its generic Galois module closed under submodules and quotients:

$$
0\to G'\to G\to G/G'\to0
$$

models

$$
0\to M'\to M\to M/M'\to0.
$$

The assertion depends on the DVR closure theorem. Over a higher-dimensional base, closure of a submodule may be torsion-free without being flat. Over a field there is no integral issue.

### 13.4 Extensions and exact models

Suppose

$$
0\to M'\to M\to M''\to0
$$

is an exact sequence of finite Galois modules and $G$ is a finite-flat model of $M$. Closing $M'$ inside $G$ produces an exact finite-flat sequence whose quotient models $M''$. Therefore every subquotient of an already modeled representation inherits a model.

The converse extension problem is harder: given models $G'$ and $G''$, not every generic extension of their generic fibers need extend to a finite-flat middle term with those prescribed end models. Existence of such a middle term is a genuine integral condition. When it exists, the middle term is finite flat by torsor descent and has order $|G'||G''|$.

This asymmetry is fundamental for deformation theory. Closure makes subquotients stable inside an existing model, while constructing new extensions imposes equations not visible from the generic module alone.

### 13.5 Scalar extension

For an extension of DVRs $R\to R'$ with fraction fields $K\to K'$, base change sends a model of $M$ to a model of the restricted $\Gamma_{K'}$-module. Exact sequences, orders, connected–étale decompositions under the relevant residue hypotheses, and subgroup closures under flat extensions are preserved.

Descent in the other direction requires data. A model over $R'$ descends only when its two pullbacks to $R'\otimes_RR'$ are compatibly isomorphic and satisfy the cocycle condition. Even if its generic module descends, the integral Hopf lattice may not. Thus potential existence after ramified extension is weaker than existence over $R$.

### 13.6 A precise finite-flat model category

For a fixed DVR $R$ and integer $N$, define $\mathcal M_R(N)$ as follows:

- objects are finite locally free commutative $R$-group schemes killed by $N$;
- morphisms are homomorphisms of $R$-group schemes;
- exact sequences are faithfully flat exact sequences;
- a finite-flat subobject is a closed subgroup that is finite locally free;
- cokernels are represented finite-flat quotients.

When $R$ is a DVR, schematic closure ensures that generic subgroups of a fixed object have finite-flat extensions, and finite-flat quotients provide cokernels for admissible closed immersions. Arbitrary morphisms need not have finite-flat kernels or faithfully flat image factorizations, so $\mathcal M_R(N)$ is best regarded as an exact category with the displayed faithfully flat exact sequences, not as an abelian category. The generic-fiber functor

$$
\mathcal M_R(N)\longrightarrow
\{\text{finite étale }K\text{-groups killed by }N\}
$$

is faithful and exact, though not generally full or essentially injective. If $N$ is invertible in $K$, composing with geometric points lands in finite continuous $\Gamma_K$-modules killed by $N$.

This is the precise environment in which finite-flat models of residual representations live: not as bare Galois modules, and not as arbitrary finite schemes, but as finite projective Hopf lattices with a controlled exact structure.

We stop at that categorical boundary. Deciding whether a representation admits a model, comparing all of its possible models, and turning existence into a deformation condition require additional representation-theoretic input. The present theory supplies the geometric objects and the exact operations those later questions are allowed to use.

## 14. Structural synthesis

### 14.1 The three layers of a finite-flat object

A finite flat commutative group scheme over a local arithmetic base carries three simultaneous layers:

$$
\begin{array}{c}
\text{generic finite group and its Galois action},\\
\text{integral finite projective Hopf lattice},\\
\text{special finite group scheme with connected and étale parts}.
\end{array}
$$

The generic layer is often étale and representation-theoretic. The special layer may be nonreduced. The integral layer relates them and is not determined by either one alone. Rank is the conserved quantity passing through all three.

### 14.2 A safe construction protocol

The recurring constructions can be organized into a reliable sequence.

To form a kernel, take the scheme-theoretic fiber over the identity and prove its coordinate algebra flat. To form an image over a DVR, take the generic schematic image and close it. To form a quotient, first verify that the subgroup is finite locally free and then use the represented faithfully flat sheaf quotient. To extend a generic subgroup, contract its Hopf ideal and prove saturation before Hopf stability. To interpret geometric points, first prove the relevant fiber étale.

Each step has a different purpose. Representability creates the scheme, flatness preserves rank, Hopf stability preserves the group law, and the torsor property supplies exactness. Combining them prematurely is the source of most false statements in the subject.

### 14.3 Hypotheses and what they buy

The principal hypotheses used in this book have sharply separated roles.

Finite presentation turns finite flat modules into finite locally free ones over arbitrary bases. Noetherianity often supplies finite presentation automatically. Locality turns finite projective modules into free modules. A DVR turns finite torsion-free modules into free modules and makes saturation equivalent to flat closure. The Dedekind condition globalizes that one-dimensional argument. Henselianity lifts idempotents and finite étale objects from the residue field. Perfection of the residue field makes reduced finite fibers geometrically reduced and gives a clean étale component quotient.

None is a universal decoration. Dropping finite presentation permits nonprojective finite flat modules. Dropping the DVR or Dedekind condition breaks the implication from torsion-free to flat. Dropping henselianity obstructs lifting components. Dropping perfection allows inseparable reduced fibers that are not étale.

### 14.4 What exactness means

Exactness is sheaf-theoretic, not pointwise. In

$$
0\to H\to G\to Q\to0,
$$

$H$ is the scheme-theoretic kernel, $G\to Q$ is faithfully flat, and $Q$ is the represented sheaf quotient. The map $G(T)\to Q(T)$ may fail to be surjective. Once exactness is established, ranks multiply and arbitrary base change preserves the sequence.

This definition treats constant, étale, multiplicative, and infinitesimal groups uniformly. It explains why Frobenius can be surjective as a morphism of faithfully flat sheaves while failing on points of a nonperfect field, and why $\mu_p$ can be a nontrivial kernel with only one geometric point.

### 14.5 The boundary with duality

Finite projective coordinate algebras admit module duals, convolution, determinant lines, and perfect-pairing questions. These constructions already explain why finite-flat groups are stable under many linear operations and why their tangent and cotangent modules behave well under base change. They do not yet supply a full dual group formalism.

In particular, constant and diagonalizable examples stand opposite one another, and torsion on abelian schemes carries natural pairings, but no argument here depends on identifying one as the dual of the other. Keeping this boundary explicit ensures that closure, exactness, and rank have been proved directly rather than borrowed from an undeveloped duality theorem.

### 14.6 Conclusion

Finite flat commutative group schemes are the integral form of finite arithmetic symmetry. Their generic fibers can look like ordinary finite Galois modules, while their special fibers may condense those points into connected infinitesimal groups. The finite projective Hopf algebra is the object that holds both pictures together: it preserves order through specialization, carries the law on every test ring, and makes base change exact and visible.

Over fields, the theory separates connected local structure from finite étale Galois modules. Over henselian local rings with perfect residue field, that separation lifts to a connected–étale sequence. Over DVRs and Dedekind bases, saturation turns generic subgroup schemes into unique finite-flat closures inside fixed ambient models. This closure theorem propagates finite-flat structure to subobjects, flat images, quotients, and torsion subgroups of abelian and elliptic schemes.

The resulting category is exact enough for arithmetic use without pretending to be simpler than it is. A generic representation may have several integral models; a pointwise quotient may omit torsors; a closed kernel may need a flatness proof; and a special fiber of order $n$ may have fewer than $n$ points. Once these distinctions are respected, the standard operations become stable, rank formulas become trustworthy, and finite-flat models provide a precise language for the integral behavior of residual representations.
