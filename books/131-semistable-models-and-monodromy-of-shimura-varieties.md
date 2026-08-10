# Semistable Models and Monodromy of Shimura Varieties

## Contents

1. [Bad reduction as controlled geometry](#1-bad-reduction-as-controlled-geometry)
   - [The problem left by good integral models](#11-the-problem-left-by-good-integral-models)
   - [Standing arithmetic and cohomological conventions](#12-standing-arithmetic-and-cohomological-conventions)
   - [The exact scope of the construction](#13-the-exact-scope-of-the-construction)
2. [Parahoric PEL data and bad-prime moduli](#2-parahoric-pel-data-and-bad-prime-moduli)
   - [A periodic lattice chain](#21-a-periodic-lattice-chain)
   - [The moduli problem](#22-the-moduli-problem)
   - [Representability, generic fiber, and properness](#23-representability-generic-fiber-and-properness)
   - [The local-model diagram](#24-the-local-model-diagram)
3. [The rank-two Iwahori local model](#3-the-rank-two-iwahori-local-model)
   - [Incidence of two lines](#31-incidence-of-two-lines)
   - [The nodal chart](#32-the-nodal-chart)
   - [Components and their intersection](#33-components-and-their-intersection)
   - [Thickness and ramified variants](#34-thickness-and-ramified-variants)
4. [The bad quaternionic curve](#4-the-bad-quaternionic-curve)
   - [Construction of the integral curve](#41-construction-of-the-integral-curve)
   - [Regularity and semistability](#42-regularity-and-semistability)
   - [The global component graph](#43-the-global-component-graph)
   - [A two-component calculation](#44-a-two-component-calculation)
5. [A unitary surface with one bad direction](#5-a-unitary-surface-with-one-bad-direction)
   - [Why one direction can degenerate independently](#51-why-one-direction-can-degenerate-independently)
   - [Local equations and regularity](#52-local-equations-and-regularity)
   - [The two surface components](#53-the-two-surface-components)
   - [Intersection data](#54-intersection-data)
6. [Two bad directions and semistable regularization](#6-two-bad-directions-and-semistable-regularization)
   - [The product-of-nodes singularity](#61-the-product-of-nodes-singularity)
   - [The small resolution](#62-the-small-resolution)
   - [Strict semistability of the resolved charts](#63-strict-semistability-of-the-resolved-charts)
   - [Components, double curves, and triple points](#64-components-double-curves-and-triple-points)
   - [The choice of diagonal](#65-the-choice-of-diagonal)
7. [Base change, alterations, and descent](#7-base-change-alterations-and-descent)
   - [What finite extension changes](#71-what-finite-extension-changes)
   - [Resolving thick curve nodes](#72-resolving-thick-curve-nodes)
   - [Semistable alteration in the present surface charts](#73-semistable-alteration-in-the-present-surface-charts)
   - [Finite descent data](#74-finite-descent-data)
8. [Strata and incidence complexes](#8-strata-and-incidence-complexes)
   - [The ordered strata](#81-the-ordered-strata)
   - [Restriction and Gysin maps](#82-restriction-and-gysin-maps)
   - [The curve graph and the surface dual complex](#83-the-curve-graph-and-the-surface-dual-complex)
   - [A product-incidence calculation](#84-a-product-incidence-calculation)
9. [Nearby cycles on the bad models](#9-nearby-cycles-on-the-bad-models)
   - [Local nearby-cycle stalks](#91-local-nearby-cycle-stalks)
   - [The quaternionic curve complex](#92-the-quaternionic-curve-complex)
   - [The one-direction surface complex](#93-the-one-direction-surface-complex)
   - [The two-direction surface complex](#94-the-two-direction-surface-complex)
   - [Coefficients from PEL geometry](#95-coefficients-from-pel-geometry)
10. [Weight and monodromy filtrations](#10-weight-and-monodromy-filtrations)
    - [The logarithm of inertia](#101-the-logarithm-of-inertia)
    - [Curves: three graded pieces](#102-curves-three-graded-pieces)
    - [Surfaces: five possible graded pieces](#103-surfaces-five-possible-graded-pieces)
    - [When the weight filtration is the monodromy filtration](#104-when-the-weight-filtration-is-the-monodromy-filtration)
    - [Integral lattices and saturation](#105-integral-lattices-and-saturation)
11. [Conductor and type for quaternionic curves](#11-conductor-and-type-for-quaternionic-curves)
    - [The conductor formula](#111-the-conductor-formula)
    - [Graph computation at split semistable level](#112-graph-computation-at-split-semistable-level)
    - [Two-dimensional constituents and special type](#113-two-dimensional-constituents-and-special-type)
    - [Finite and nonsplit descent](#114-finite-and-nonsplit-descent)
12. [Conductor and type for unitary surfaces](#12-conductor-and-type-for-unitary-surfaces)
    - [Ranks of $N$ and $N^2$](#121-ranks-of-n-and-n2)
    - [One bad direction](#122-one-bad-direction)
    - [Two bad directions](#123-two-bad-directions)
    - [Jordan blocks, conductor, and Euler factor](#124-jordan-blocks-conductor-and-euler-factor)
    - [The rank-two Hecke constituent](#125-the-rank-two-hecke-constituent)
13. [Hecke correspondences and functorial monodromy](#13-hecke-correspondences-and-functorial-monodromy)
    - [Extension away from the bad prime](#131-extension-away-from-the-bad-prime)
    - [Action on strata and nearby cycles](#132-action-on-strata-and-nearby-cycles)
    - [Projectors and coefficient fields](#133-projectors-and-coefficient-fields)
    - [The local--global compatibility package](#134-the-local--global-compatibility-package)
14. [The semistable bad-prime theorem](#14-the-semistable-bad-prime-theorem)
    - [Unified construction and computation](#141-unified-construction-and-computation)
    - [Hypothesis ledger and failure modes](#142-hypothesis-ledger-and-failure-modes)
    - [Conclusion](#143-conclusion)

## 1. Bad reduction as controlled geometry

### 1.1 The problem left by good integral models

At a hyperspecial prime, the integral PEL moduli space is smooth. Its special fiber therefore has no local memory beyond ordinary specialization, and inertia acts trivially on prime-to-residue-characteristic cohomology. A prime at which the level stabilizes a nontrivial lattice chain is different. The Hodge filtration must move compatibly through that chain. The resulting local model has several components, and their intersections create vanishing cycles.

This book turns that failure of smoothness into usable arithmetic. For the quaternionic curves, the essential singular fiber is nodal and the total space is regular. For the compact unitary surfaces used in the modèles étranges construction, one or two rank-two directions can be parahoric. One bad direction gives a regular strict normal-crossings model. Two bad directions first give a product of nodes whose total space is singular; an explicit small modification replaces it by strict semistable charts.

The route is thus

$$
\text{lattice chain}
\longrightarrow \text{PEL local model}
\longrightarrow \text{semistable strata}
\longrightarrow R\Psi
\longrightarrow (r,N)
\longrightarrow \text{conductor and local type}.
$$

Each arrow retains information that the next numerical invariant may forget. The conductor remembers a rank and a wild correction. The local type also remembers finite inertia, the nilpotent operator, Frobenius, and, in degree two, whether $N^2$ is nonzero.

### 1.2 Standing arithmetic and cohomological conventions

Let $R$ be a henselian excellent discrete valuation ring with fraction field $K$, uniformizer $\pi$, and perfect residue field $k$ of characteristic exponent $p$. When weights or Frobenius eigenvalues are discussed, $k=\mathbf F_q$ is finite. Fix $\ell\ne p$ and write

$$
E_\ell=\mathbf Q_\ell,\qquad \Lambda_\ell=\mathbf Z_\ell.
$$

All geometric fibers are taken after fixed separable closures. Geometric Frobenius is denoted by $F$. The Tate twist is normalized so that $F$ acts on $E_\ell(1)$ by $q^{-1}$. Accordingly the monodromy operator has the typed form

$$
N:V\longrightarrow V(-1),\qquad FNF^{-1}=q^{-1}N.
$$

A proper flat $R$-scheme of relative dimension $d\le2$ is **strictly semistable** if its total space is regular and, étale locally, it is

$$
\operatorname{Spec}R[t_1,\ldots,t_{d+1}]/(t_1\cdots t_r-\pi)
$$

for $1\le r\le d+1$, with unused coordinates smooth. Its geometric special fiber is $Y=\bigcup_{i\in I}Y_i$, and

$$
Y^{(a)}=\coprod_{i_1<\cdots<i_a}Y_{i_1}\cap\cdots\cap Y_{i_a}.
$$

The ordering of $I$ fixes signs in incidence maps; the resulting cohomology is independent of it.

The normalization, blowup, regular-model, graph, component-group, and low-dimensional nearby-cycle results established earlier are used with their stated hypotheses. We recall every formula that enters a calculation. The generic quaternionic and unitary PEL spaces, their selected canonical components, and their universal families are the ones already constructed. No later automorphic decomposition is assumed.

### 1.3 The exact scope of the construction

Bad integral models are not uniform across all parahoric groups. We treat exactly the rank-two minuscule factors occurring in the selected quaternionic curve and compact unitary surface data. At the bad place we assume the integral datum has been verified to reduce, under Morita equivalence, to one or two periodic chains of rank-two lattices. The determinant, isotropy, and any wedge condition must cut out the flat incidence model defined below. This is a hypothesis about the actual integral datum, not a consequence of its generic fiber.

Three cases result:

1. a quaternionic curve with one Iwahori chain;
2. a unitary surface with one Iwahori direction and one hyperspecial direction;
3. a unitary surface with two Iwahori directions.

We also allow finite extension of $K$ followed by normalization and the explicit semistable modifications of Chapter 7. This is a semistable alteration when the generic variety is replaced by a finite cover. It is not called a model of the original generic variety. Arbitrary ramified unitary local models, deeper lattice chains, nonflat naive determinant loci, and wild singularities are outside the theorem. Their exclusion is necessary because their nearby cycles are not determined by the charts proved here.

## 2. Parahoric PEL data and bad-prime moduli

### 2.1 A periodic lattice chain

At a hyperspecial place a single self-dual lattice is enough. An Iwahori level remembers a neighboring pair, and the Hodge filtration must be compatible with both. This is the smallest parahoric refinement capable of producing a node.

Let $U_0$ and $U_1$ be free rank-two $R$-modules with maps

$$
\alpha:U_0\longrightarrow U_1,
\qquad
\beta:U_1\longrightarrow U_0
$$

such that

$$
\beta\alpha=\pi\operatorname{id}_{U_0},
\qquad
\alpha\beta=\pi\operatorname{id}_{U_1}.
\tag{2.1}
$$

After bases are chosen, the standard chain is

$$
\alpha=\begin{pmatrix}1&0\\0&\pi\end{pmatrix},
\qquad
\beta=\begin{pmatrix}\pi&0\\0&1\end{pmatrix}.
\tag{2.2}
$$

Over $K$, both maps are isomorphisms, so the two filtration lines determine one another. Over $k$, each map has rank one, and two limiting choices appear. That rank drop is the source of the two components.

For the PEL datum, $U_i$ is the Morita multiplicity module in the active factor of a self-dual periodic lattice chain $\Lambda_i$. The other algebra factors are fixed by the determinant condition. In the unitary case the duality identifies the chain with its opposite and the line conditions below are already the residual polarization conditions. If an actual datum has an additional wedge or spin equation, our flat-local-model hypothesis says that equation neither enlarges nor shrinks the incidence scheme.

### 2.2 The moduli problem

The bad-prime moduli problem must record the integral isogeny rather than merely a subgroup in a generic fiber. For an $R$-scheme $S$, an object consists of PEL abelian schemes

$$
(A_0,\iota_0,\lambda_0,\eta^p),
\qquad
(A_1,\iota_1,\lambda_1,\eta^p_1),
$$

and an $\mathcal O$-linear isogeny

$$
\phi:A_0\longrightarrow A_1
\tag{2.3}
$$

whose kernel has the finite locally free type prescribed by $\Lambda_0\subset\Lambda_1$. The polarizations satisfy

$$
\phi^\vee\lambda_1\phi=c\lambda_0
\tag{2.4}
$$

for the scalar $c$ determined by the chain, and the prime-to-$p$ levels correspond under $\phi$. Both Lie algebras satisfy the PEL determinant law. Equivalently, one may specify the finite locally free, $\mathcal O$-stable, isotropic kernel $H\subset A_0[p^a]$ of the prescribed rank and put $A_1=A_0/H$.

Why insist on finite local freeness? A schematic subgroup of the right generic rank can acquire torsion in its coordinate algebra and cease to define an isogeny in the special fiber. Flatness is exactly what keeps the degree constant. Why impose the determinant law at both vertices? At a bad prime the algebra can fail to be semisimple modulo $p$; a condition at only one vertex need not control the other Lie algebra.

At neat prime-to-$p$ level, automorphisms are trivial. At coarser level the same construction gives a finite quotient stack; all geometric calculations are first made on a fine cover.

For a unitary surface with two bad directions, the object contains the two commuting isogeny steps, or equivalently a square of four PEL abelian schemes. The cocycle condition identifies the two composites. On de Rham homology this becomes the product of two incidence problems.

### 2.3 Representability, generic fiber, and properness

**Theorem 2.1 (parahoric PEL representability).** Assume neat prime-to-$p$ level and the flat-local-model hypothesis of Section 1.3. The one-chain and two-chain functors are represented by projective $R$-schemes of finite presentation. Their generic fibers are the selected quaternionic or unitary Shimura varieties at the corresponding parahoric level. They carry the universal isogeny chain.

**Proof strategy.** The finite subgroup is placed in a projective Hilbert scheme, the PEL equations cut out a closed locus, and compactness supplies the valuative criterion.

**Proof.** Begin with the fine PEL parameter scheme with sufficiently rigid projective frames on the abelian schemes. The relative Hilbert scheme of subschemes of $A_0[p^a]$ is projective. Being a subgroup, being stable under each generator of $\mathcal O$, having a fixed finite locally free Hilbert polynomial, and being isotropic for the polarization pairing are closed conditions. The quotient by such a finite locally free subgroup exists as an abelian scheme, and (2.4) plus the determinant identities are closed. Thus the framed functor is represented by a quasi-projective scheme; removing the frames by the free change-of-frame action gives the fine moduli scheme.

Over $K$, the prescribed kernel is étale after passage to a suitable level cover and is exactly a parahoric level flag. Hence the generic fiber is the required Shimura variety.

It remains to prove properness. Let $K'$ be the fraction field of a valuation ring $R'$ over $R$ and take a $K'$-point. After a finite extension, semiabelian reduction gives a semiabelian extension of its abelian variety. A nonzero toric part supplies a rational isotropic subspace stable under the PEL algebra, hence a proper rational parabolic of the adjoint group. Compactness, equivalently anisotropy modulo center in the selected data, excludes it. Thus the abelian scheme has good reduction. The schematic closure of the generic kernel in the finite flat group $A_0[p^a]$ has torsion-free coordinate algebra over the valuation ring and is therefore flat; the group, algebra-stability, and isotropy identities extend by closure. The quotient and all tensors extend. Uniqueness follows from separatedness and rigidity. Descent from the finite extension is effective because the extension is unique. The valuative criterion proves properness. Projectivity follows from proper quasi-projectivity. $\square$

The theorem does not assert that the model is smooth. Its singularities are precisely the content of the local-model calculation.

### 2.4 The local-model diagram

To compare a moduli singularity with linear algebra, add frames to the de Rham modules at every lattice vertex. This gives

$$
\mathscr M
\xleftarrow{\ p\ }
\widetilde{\mathscr M}
\xrightarrow{\ q\ }
M^{\mathrm{loc}}.
\tag{2.5}
$$

The map $p$ is a torsor under the smooth integral automorphism group of the lattice chain. The map $q$ sends an abelian isogeny chain to its framed Hodge submodules.

**Proposition 2.2 (local-model principle).** Under the flat-local-model hypothesis, both $p$ and $q$ are smooth. Consequently $\mathscr M$ and $M^{\mathrm{loc}}$ have isomorphic strict henselian completed local rings after adjoining formal power-series variables. In the curve and surface cases their relative dimensions agree, so the completed singular factors are exactly those displayed in Chapters 3, 5, and 6.

**Proof.** Smoothness of $p$ is the lifting property for frames under a smooth group torsor. For $q$, consider a square-zero thickening $S_0\hookrightarrow S$. Deformation theory of abelian schemes identifies lifts with lifts of their Hodge direct summands inside the evaluated de Rham modules. Compatibility with the isogenies is exactly compatibility with the lattice-chain maps; the algebra, polarization, and determinant conditions are exactly the equations of $M^{\mathrm{loc}}$. A lifted local-model point therefore gives a lifted PEL chain, locally on $S$, and a frame lifts smoothly. This is formal smoothness. Finite presentation turns it into smoothness. The assertion on completed local rings is the standard consequence of two smooth maps through a common framed point. $\square$

This proof is why the actual flat local model must be known. A naive determinant scheme with an extra vertical component would give the wrong completed ring.

## 3. The rank-two Iwahori local model

### 3.1 Incidence of two lines

Define $M^{\mathrm{Iw}}$ over $R$ by

$$
M^{\mathrm{Iw}}(S)=\left\{(L_0,L_1):
L_i\subset U_i\otimes\mathcal O_S\text{ line subbundles},
\ \alpha L_0\subset L_1,
\ \beta L_1\subset L_0\right\}.
\tag{3.1}
$$

It is closed in $\mathbf P(U_0)\times_R\mathbf P(U_1)$, hence projective. Over $K$, $L_1=\alpha L_0$, so its generic fiber is $\mathbf P^1_K$. The special fiber is more informative. The rank-one maps $\bar\alpha$ and $\bar\beta$ have complementary kernel and image. A line away from the kernel determines the other line, but at the kernel there are two limiting branches.

The incidence formulation is preferable to a single determinant equation. It records both vertices, is invariant under change of lattice-chain bases, and carries the universal filtration data needed to extend the PEL isogeny.

### 3.2 The nodal chart

**Proposition 3.1 (Iwahori chart).** The scheme $M^{\mathrm{Iw}}$ is regular, flat, and semistable over $R$. It is smooth except at one point of the special fiber, where an affine neighborhood is

$$
\operatorname{Spec}R[x,y]/(xy-\pi).
\tag{3.2}
$$

**Proof.** Use the bases of (2.2). Near the exceptional pair, write

$$
L_0=R(x,1),\qquad L_1=R(1,y).
$$

The condition $\alpha L_0\subset L_1$ says $(x,\pi)$ is proportional to $(1,y)$, hence $xy=\pi$. The condition involving $\beta$ gives the same equation. The remaining standard affine charts eliminate one line coordinate uniquely and are smooth.

The ring in (3.2) is flat because it is torsion-free over the DVR. At its closed point its maximal ideal is generated by $x,y$, since $\pi=xy$; its dimension is two and its embedding dimension is two, so it is regular. The special fiber is $xy=0$, two smooth branches meeting transversely. This proves the assertion. $\square$

The word “singular” must now be used carefully. The morphism to $R$ is not smooth at the crossing, and the special fiber is singular, but the total space is regular. Nearby cycles arise from failure of smoothness, not from singularity of the total space.

### 3.3 Components and their intersection

The special fiber of $M^{\mathrm{Iw}}$ consists of two copies of $\mathbf P^1_k$, denoted $C_0$ and $C_1$. One corresponds to choosing the limiting line at the first lattice vertex; the other corresponds to the second. They meet once and transversely. Locally they are $x=0$ and $y=0$.

If the local model is pulled back by a smooth morphism of relative dimension $a$, the two components become smooth of dimension $a+1$ and meet along a smooth locus of dimension $a$. The normal bundles of the intersection inside the two components are dual: from $xy=\pi$, $x$ cuts one branch and $y$ the other, while their tensor product is the trivial normal direction defined by $\pi$.

For a proper regular curve model whose special fiber is globally $Y_0+Y_1$, the fiber relation gives

$$
Y_0^2=-(Y_0\cdot Y_1),\qquad
Y_1^2=-(Y_0\cdot Y_1).
\tag{3.3}
$$

If the intersections are geometric points $s$ with residue degrees $f_s$, then

$$
(Y_0\cdot Y_1)=\sum_s f_s.
\tag{3.4}
$$

Thus the component matrix is the negative Laplacian of the two-vertex multigraph.

### 3.4 Thickness and ramified variants

After a ramified base change of index $e$, equation (3.2) becomes

$$
xy=u(\pi')^e.
$$

Absorbing the unit gives thickness $e$. For $e>1$ the total space is not regular. Its minimal semistable resolution inserts a chain of $e-1$ rational components and replaces the weighted edge by $e$ unit edges. The cycle rank is unchanged, but the integral edge pairing is multiplied by $e$.

This separates rational and integral monodromy. Tensoring with $E_\ell$, subdivision changes no rank. On $\Lambda_\ell$, the monodromy map may acquire a larger cokernel, and that cokernel is visible in the component group. Thickness therefore belongs in every integral type calculation even when the Artin conductor is unchanged.

## 4. The bad quaternionic curve

### 4.1 Construction of the integral curve

Let $(G,X)$ be the quaternionic PEL datum with one active real factor, compact adjoint quotient, neat level away from $p$, and the rank-two parahoric chain of Chapter 2 at $p$. Let

$$
\mathscr C_{\mathrm{Iw}}/R
$$

be the fine moduli scheme of the PEL isogeny (2.3), restricted to the selected canonical component union. Theorem 2.1 makes it projective and identifies its generic fiber with the parahoric Shimura curve.

This moduli construction is important even when one can describe the generic curve by a double quotient. It extends the universal isogeny, the order action, the polarization, and prime-to-$p$ level simultaneously. Those structures later make Hecke actions on nearby cycles canonical.

### 4.2 Regularity and semistability

**Theorem 4.1 (semistable quaternionic model).** Under the stated local-model hypothesis, $\mathscr C_{\mathrm{Iw}}$ is a regular projective flat curve over $R$ with reduced nodal special fiber. At every geometric node its completed strict henselian local ring is

$$
R^{\mathrm{sh}}[[x,y]]/(xy-\pi).
\tag{4.1}
$$

In particular it is strictly semistable.

**Proof.** Projectivity is Theorem 2.1. Flatness and the local equation are smooth-local properties. Proposition 2.2 transfers them from $M^{\mathrm{Iw}}$, and Proposition 3.1 proves them there. Because the moduli dimension and local-model dimension are both one, the formally smooth variables are absorbed into étale coordinates and (4.1) is the singular factor. Away from the crossing stratum, the local model is smooth. Thus the total space is regular everywhere and the special fiber is a reduced normal-crossings divisor. $\square$

At quotient level, take a fine normal subgroup of the prime-to-$p$ level. If the quotient group acts freely on the integral model, the quotient remains semistable étale locally. If it has fixed points in the special fiber, the coarse quotient can have quotient singularities. Nearby-cycle calculations should then be made equivariantly on the fine cover and descended; silently treating the coarse space as regular is not valid.

### 4.3 The global component graph

Write the geometric special fiber as

$$
Y=\bigcup_{v\in V}Y_v
$$

and let $\Sigma$ be its set of geometric nodes. The local model labels each branch by one of the two vertices of the lattice chain, but global connected components with the same label need not be connected to one another. The correct dual graph $\Gamma$ has a vertex for every irreducible component and an edge for every geometric node, including loops and multiple edges.

The arithmetic genus formula is

$$
g(C)=\sum_{v\in V}g(Y_v)+b_1(\Gamma).
\tag{4.2}
$$

The toric rank of the special identity component of the Jacobian is $b_1(\Gamma)$. With unit thickness, the monodromy pairing on

$$
X_\Gamma=H_1(\Gamma,\mathbf Z)
$$

is

$$
q(a,b)=\sum_{e\in E(\Gamma)}a_eb_e.
\tag{4.3}
$$

The geometric component group is

$$
\Phi(\bar k)=\operatorname{coker}\left(
X_\Gamma\xrightarrow{q}X_\Gamma^\vee\right).
\tag{4.4}
$$

These statements retain the Galois action on oriented edges. A nonsplit node may reverse an orientation and hence act by $-1$ on a cycle.

### 4.4 A two-component calculation

Suppose, as frequently happens in the rank-two local model, that $Y=Y_0\cup Y_1$ and the components meet transversely in $m$ geometric points. Then $\Gamma$ has two vertices and $m$ parallel edges. Hence

$$
b_1(\Gamma)=m-1,
\tag{4.5}
$$

and the component intersection matrix is

$$
\begin{pmatrix}-m&m\\m&-m\end{pmatrix}.
\tag{4.6}
$$

Choose cycles $c_i=e_i-e_m$ for $1\le i<m$. Their Gram matrix has diagonal entries $2$ and off-diagonal entries $1$. Its determinant is $m$, and its Smith form is

$$
\operatorname{diag}(1,\ldots,1,m).
$$

Therefore

$$
\Phi(\bar k)\simeq\mathbf Z/m\mathbf Z.
\tag{4.7}
$$

For $m=1$ the fiber is reducible but the graph is a tree, so both monodromy rank and component group vanish. This example prevents the common error of replacing “independent cycles” by “number of nodes.”

If the closed nodes have residue degrees $f_s$, then the geometric graph is formed after residue extension, while over $k$ the intersection number is $\sum f_s$. Frobenius on (4.7) must be computed from its signed permutation action, not from the integer $m$ alone.

## 5. A unitary surface with one bad direction

### 5.1 Why one direction can degenerate independently

The compact unitary surface has two active signature-$(1,1)$ multiplicity planes. At a good prime each contributes a projective line to the local model. If only the first lattice is replaced by an Iwahori chain, the second line still varies smoothly. The bad local model is therefore

$$
M^{\mathrm{Iw}}\times_R\mathbf P^1_R.
\tag{5.1}
$$

This product is not merely a dimension count. Morita decomposition separates the two algebra idempotent factors, and the common similitude condition relates determinant lines without coupling their infinitesimal line choices. The flat-local-model hypothesis asserts exactly this independence.

Let $\mathscr S_{\mathrm{Iw},\mathrm{hyp}}$ denote the selected proper unitary PEL moduli surface with the first direction parahoric and the second hyperspecial.

### 5.2 Local equations and regularity

**Theorem 5.1.** The surface $\mathscr S_{\mathrm{Iw},\mathrm{hyp}}$ is projective, regular, flat, and strictly semistable over $R$. At a point of its double locus it is étale locally

$$
\operatorname{Spec}R[x,y,z]/(xy-\pi),
\tag{5.2}
$$

where $z$ is a smooth parameter.

**Proof.** Theorem 2.1 gives projectivity. The local-model diagram transfers the product chart (3.2) with the affine coordinate $z$ on $\mathbf P^1$. The maximal ideal at the crossing is generated by $x,y,z$, while the local dimension is three, so the total space is regular. Its special fiber $xy=0$ is reduced, with two smooth components meeting transversely. This is the strict semistable chart with $r=2$ and relative dimension two. $\square$

No triple point occurs in this case. Consequently $N^2=0$ on every cohomology group, although $N$ on middle cohomology may be nonzero.

### 5.3 The two surface components

Write

$$
Y=Y_0\cup Y_1,
\qquad D=Y_0\cap Y_1.
$$

The components are smooth projective surfaces over $\bar k$ and $D$ is a disjoint union of smooth projective curves. Moduli-theoretically, $Y_0$ and $Y_1$ record which lattice vertex contains the limiting Hodge line, while $D$ records the rank-drop locus where both limiting descriptions coexist.

The dual complex is an interval for each connected incidence pair. It has no second homology. It follows already at the combinatorial level that the extreme weight-zero and weight-four terms in $H^2$ vanish. The possible middle monodromy comes instead from $H^1(D)$ and from the failure of restriction and Gysin maps to exhaust it.

This is the first place where the surface theory differs from the curve graph. A double curve contains its own cohomology. Counting connected components of $D$ sees only $H^0(D)$ and cannot determine $N$ on $H^2$.

### 5.4 Intersection data

Because $Y_0+Y_1$ is the principal divisor of $\pi$, restricting to $D$ gives

$$
N_{D/Y_0}\otimes N_{D/Y_1}\simeq\mathcal O_D.
\tag{5.3}
$$

Equivalently, the two self-intersection classes of $D$ in the components are negatives of one another. The Gysin maps

$$
i_{a*}:H^j(D,E_\ell)\longrightarrow H^{j+2}(Y_a,E_\ell)(1)
$$

are adjoint to restrictions under Poincaré duality. Their signs in the weight complex are opposite.

For $j=0$, $i_{a*}(1)$ is the divisor class $[D]$ on $Y_a$. For $j=1$, the image measures how the Jacobian of $D$ maps into degree-three component cohomology. These maps, rather than the bare genus of $D$, determine which double-curve classes survive as monodromy blocks.

## 6. Two bad directions and semistable regularization

### 6.1 The product-of-nodes singularity

With Iwahori chains in both active directions, the local model is the product

$$
M^{\mathrm{Iw}}\times_RM^{\mathrm{Iw}}.
$$

Near the product of the two crossing points its completed local ring is

$$
A=R[[x,y,u,v]]/(xy-\pi,uv-\pi).
\tag{6.1}
$$

It is flat of relative dimension two, but it is not regular at the closed origin. Indeed the local dimension is three, while modulo the square of the maximal ideal both defining equations have the same linear term $-\pi$; equivalently, after eliminating $\pi$ the tangent cone is $xy-uv=0$ in four variables. The embedding dimension is four.

The special fiber has four local components, obtained by choosing one of $x,y$ and one of $u,v$ to vanish. All four meet at the origin. Four components cannot meet normally in a regular threefold: a strict semistable surface permits at most three. Thus the raw product model cannot be fed directly into the strict semistable nearby-cycle formula.

### 6.2 The small resolution

The singularity has two natural small resolutions, corresponding to the two diagonals of the square of components. Choose the blowup

$$
\rho:\widetilde X=\operatorname{Bl}_{(x,u)}\operatorname{Spec}A
\longrightarrow\operatorname{Spec}A.
\tag{6.2}
$$

**Proposition 6.1 (explicit resolution).** The scheme $\widetilde X$ is regular and strictly semistable over $R$. The morphism $\rho$ is projective and birational, is an isomorphism away from the origin, and its exceptional fiber over the origin is $\mathbf P^1_k$. It introduces no exceptional divisor.

**Proof.** The blowup has two affine charts. On the $x$-chart write $u=xt$. In the fraction ring, the relations give

$$
x y=\pi=x t v,
$$

and cancellation of the nonzerodivisor $x$ gives $y=tv$. Thus the chart is

$$
R[[x,t,v]]/(xtv-\pi).
\tag{6.3}
$$

On the $u$-chart write $x=us$. Cancellation similarly gives $v=sy$, and the chart is

$$
R[[u,s,y]]/(usy-\pi).
\tag{6.4}
$$

Both rings are regular: at their deepest closed points the uniformizer is the product of the three displayed parameters, so those parameters generate a maximal ideal of dimension three. Their special fibers are unions of three coordinate planes meeting normally. The charts cover the blowup, proving regularity and strict semistability.

The blowup is projective and birational by construction. The ideal $(x,u)$ is invertible away from the origin on the ordinary double-point factor, so the map is an isomorphism there. Over the origin the homogeneous ratio $[x:u]$ is free, giving $\mathbf P^1$. Since this exceptional locus has dimension one inside a threefold, it has codimension two and is not a divisor. $\square$

The cancellation used in the proof is legitimate because $A$ embeds in its generic-fiber domain. Performing the same manipulation in an arbitrary quotient with embedded components would be invalid.

### 6.3 Strict semistability of the resolved charts

Equations (6.3) and (6.4) are the deepest strict semistable chart in relative dimension two:

$$
abc=\pi.
\tag{6.5}
$$

At a generic point of one component, the morphism is smooth. Along a double curve, two parameters vanish and the third is a unit, reducing étale locally to $ab=\pi$. At a triple point all three vanish. Hence the local nearby-cycle ranks are respectively

$$
1,\qquad (1,1),\qquad (1,2,1)
$$

in cohomological degrees beginning at zero.

On the model with labeled chain vertices, the equations $x=0$ and $u=0$ define two globally labeled Weil component divisors near every product-node point. The sum of their ideal sheaves is coherent and has completed stalk $(x,u)$. Blowing up this ideal globalizes (6.2); away from the product-node locus it is already invertible. If no global labeling has been chosen, pass to the finite cover on which the component divisors are labeled, perform the construction equivariantly, and retain the descent action as in Chapter 7.

### 6.4 Components, double curves, and triple points

The raw product special fiber has components indexed by the four vertices of a square:

    (0,1) -------- (1,1)
      |                |
      |                |
    (0,0) -------- (1,0)

The small resolution does not add a surface component. It replaces each fourfold incidence point by an exceptional $\mathbf P^1$ and chooses a diagonal, thereby triangulating the square. Locally, one pair of opposite components becomes disjoint, while the other pair meets along the exceptional curve. Each of the two resulting triangles represents a triple point incidence in the dual complex.

Thus $Y^{(1)}$ is the disjoint union of the four strict-transform surfaces, $Y^{(2)}$ is the disjoint union of their double curves, including the curves created by the chosen diagonal, and $Y^{(3)}$ is the finite set of triple points. All are smooth. The restriction and Gysin maps among them contain the complete cohomological effect of the resolution.

The exceptional $\mathbf P^1$ lies inside the special fiber but is a double curve, not a component of the special fiber divisor. Confusing these two roles would add a false vertex to the dual complex.

### 6.5 The choice of diagonal

Blowing up $(y,u)$ gives the other small resolution. The two resolutions are related by a flop of the exceptional $\mathbf P^1$. Neither is canonically preferred by the singular local equation. A labeled PEL lattice chain can prefer one through its orientation; without a label, both are auxiliary semistable models.

The generic fibers are canonically identical, so their $E_\ell$-cohomology and monodromy representation are identical. On the special side, changing the diagonal performs an elementary subdivision of the dual square. Cellular cohomology is unchanged, and the two weight complexes are connected by pull--push through a common blowup. Proper functoriality of nearby cycles identifies their abutments. Integral lattices require more care: the comparison must use the actual pull--push maps and cannot be inferred only from equality of rational ranks.

## 7. Base change, alterations, and descent

### 7.1 What finite extension changes

Let $R'/R$ be a finite extension of ramification index $e$ and residue degree $f$. A unit-thickness node becomes thickness $e$:

$$
xy=\pi\quad\rightsquigarrow\quad xy=u(\pi')^e.
\tag{7.1}
$$

An unramified extension can split components and nodes but does not change geometric thickness. A ramified extension scales every edge length. If the extension is used to kill a finite inertial action, the resulting strict semistable model computes the unipotent operator only after restriction to $G_{K'}$; the original representation must retain the finite descent action.

Normalization is mandatory after base change. Normality and regularity need not survive a ramified tensor product. The sequence is

$$
\mathscr X_{R'}
\longleftarrow (\mathscr X_{R'})^{\mathrm{nor}}
\longleftarrow \mathscr X^{\mathrm{ss}},
\tag{7.2}
$$

where the last arrow is the explicit resolution appropriate to the local charts.

### 7.2 Resolving thick curve nodes

Consider $A_n=R[[x,y]]/(xy-\pi^n)$. For $n>1$, blow up the closed point and normalize the charts. One chart reduces the exponent by one along the strict transform and creates an exceptional rational component; repeating produces

    Y_0 -- E_1 -- E_2 -- ... -- E_(n-1) -- Y_1.

Each adjacent pair has local equation $ab=\pi$. Induction on $n$ proves termination: the sum of the remaining thicknesses drops by one at each new exceptional link. The exceptional components have genus zero and valence two.

A cycle crossing the original edge crosses every one of the $n$ unit segments with the same coefficient. Hence its pairing contribution becomes

$$
a_eb_e+\cdots+a_eb_e=n a_eb_e.
\tag{7.3}
$$

This proves both invariance under subdivision and scaling of the integral monodromy pairing under ramified base change.

### 7.3 Semistable alteration in the present surface charts

For one bad direction, first resolve every thick node as in Section 7.2 and take its product with the smooth direction. Every chart is then $ab=\pi$ with one smooth parameter.

For two bad directions, resolve the two thicknesses to unit chains. At each product of crossing points the local ring is again (6.1). Apply one of the small resolutions of Section 6.2. Because the singular points are disjoint after the chain resolutions, these blowups commute. The outcome is a proper strict semistable surface over $R'$.

**Proposition 7.1.** Suppose that after a finite extension the PEL local model is a product of one or two split rank-two chains with equations of the form $xy=(\pi')^n$. Then normalization, chain resolution, and the small resolutions above produce a proper strictly semistable model. If the finite extension changed the generic field, the resulting morphism to the original model is a semistable alteration; it is a modification only after base change.

**Proof.** The curve-chain construction gives unit nodal charts. Products with smooth charts are strict semistable. Products of two nodes have only the isolated singularities (6.1), and Proposition 6.1 resolves each into charts $abc=\pi'$. All operations are projective. They are isomorphisms on the generic fiber after the chosen field extension. Properness is preserved under base change, normalization is finite over an excellent base, and projective modification preserves properness. $\square$

No general semistable reduction theorem for arbitrary threefolds is hidden here. The proposition is proved only for the displayed toroidal charts.

### 7.4 Finite descent data

Assume $K'/K$ is finite Galois with group $\Delta$ and $\mathscr X^{\mathrm{ss}}/R'$ is a chosen semistable alteration. The action of $G_K$ on generic cohomology is described by a Weil--Deligne pair $(r,N)$ after restricting to an open inertia subgroup. For an element $w$ of the Weil group,

$$
r(w)Nr(w)^{-1}=|w|N.
\tag{7.4}
$$

Here $|w|$ is the unramified norm character, with the Tate twist understood. In particular the finite inertial action commutes with $N$. It permutes components, reverses oriented edges when branches are exchanged, and acts on the cohomology of every stratum.

Different semistable resolutions need not admit the group action without further blowups. A common equivariant domination supplies canonical descent on cohomology. One must not quotient the dual graph or dual complex before forming its signed chain complex: stabilizers and orientation reversal affect invariants.

## 8. Strata and incidence complexes

### 8.1 The ordered strata

For a strict semistable model $Y=\bigcup_{i\in I}Y_i$, choose an order on $I$. The strata $Y^{(a)}$ record intersections of exactly $a$ chosen components, as disjoint unions. In a curve only $Y^{(1)}$ and $Y^{(2)}$ occur. In a surface, $Y^{(1)}$ consists of surfaces, $Y^{(2)}$ of double curves, and $Y^{(3)}$ of triple points.

The disjoint-union convention matters. If two components meet in several connected curves, each curve is a separate edge in the dual complex. If a component meets itself after descent, the two geometric branches still give the correct incidence maps after passage to $\bar k$.

### 8.2 Restriction and Gysin maps

Dropping one component from an intersection gives closed immersions between strata. Alternating pullbacks define restriction maps $\rho$; alternating codimension-one pushforwards define Gysin maps $\gamma$. Their signs satisfy

$$
\rho^2=0,\qquad \gamma^2=0,\qquad
\rho\gamma+\gamma\rho=0.
\tag{8.1}
$$

The first two identities pair the two orders in which components can be dropped. The mixed identity follows from the self-intersection formula and the relation that the total special fiber is principal. Poincaré duality makes $\rho$ and $\gamma$ adjoint, up to the displayed signs and Tate twists.

These maps are computational, not decorative. A local double curve supplies possible vanishing cycles, but a class contributes to global monodromy only if it survives the adjacent restriction and Gysin maps.

### 8.3 The curve graph and the surface dual complex

For a curve, the complex

$$
H^0(Y^{(1)},E_\ell)
\xrightarrow{\rho}
H^0(Y^{(2)},E_\ell)
\tag{8.2}
$$

is the cellular cochain complex of the dual graph $\Gamma$. Its cokernel is $H^1(\Gamma,E_\ell)$, and the kernel of the dual Gysin map is $H_1(\Gamma,E_\ell)(-1)$.

For a surface, the degree-zero restriction row

$$
H^0(Y^{(1)})\longrightarrow H^0(Y^{(2)})
\longrightarrow H^0(Y^{(3)})
\tag{8.3}
$$

is the cellular cochain complex of the dual complex $\Delta(Y)$. Consequently the extreme middle-cohomology terms are

$$
H^2(\Delta(Y),E_\ell),
\qquad
H_2(\Delta(Y),E_\ell)(-2).
\tag{8.4}
$$

The dual complex controls $N^2$, but it does not control all of $N$: $H^1$ of double curves contributes additional length-two blocks.

### 8.4 A product-incidence calculation

Suppose globally the two parahoric directions have dual graphs $\Gamma_1$ and $\Gamma_2$, and the strata factor compatibly. Before triangulation the incidence space is the square complex $\Gamma_1\times\Gamma_2$; the small resolution triangulates each square without changing its homotopy type. Künneth gives

$$
H_2(\Delta,E_\ell)\simeq
H_1(\Gamma_1,E_\ell)\otimes
H_1(\Gamma_2,E_\ell).
\tag{8.5}
$$

Thus

$$
\dim H_2(\Delta)=b_1(\Gamma_1)b_1(\Gamma_2).
\tag{8.6}
$$

**Proof.** Graphs have homology only in degrees zero and one. The degree-two Künneth sum therefore has only $H_1\otimes H_1$. Triangulation is a cellular subdivision, inducing a chain-homotopy equivalence. $\square$

This calculation explains geometrically why two independent curve monodromies can create $N^2\ne0$ on a surface. If either graph is a tree, the extreme term vanishes even though triple points can occur locally.

## 9. Nearby cycles on the bad models

### 9.1 Local nearby-cycle stalks

Let $x$ lie on exactly $r$ components of a strict semistable model. Put

$$
C_x=\operatorname{coker}\left(
E_\ell\xrightarrow{1\mapsto(1,\ldots,1)}E_\ell^r
\right).
$$

The local semistable calculation gives

$$
(R^a\Psi E_\ell)_x
\simeq\bigwedge^a C_x(-a),
\qquad 0\le a\le r-1.
\tag{9.1}
$$

**Proof.** In the chart $t_1\cdots t_r=\pi$, the geometric generic punctured neighborhood is tamely equivalent to a torus of rank $r-1$. The product equation supplies the one diagonal relation among Kummer classes. Continuous cohomology of its maximal pro-$\ell$ tame group is the exterior algebra on $C_x(-1)$. Smooth coordinates contribute no higher cohomology. $\square$

Wild inertia acts trivially in a strict semistable chart. The action on each sheaf $R^a\Psi$ is trivial, but the full complex can have nontrivial unipotent inertia through extensions among these sheaves.

### 9.2 The quaternionic curve complex

At a smooth point of the special curve, only $R^0\Psi=E_\ell$ occurs. At a node,

$$
R^0\Psi=E_\ell,
\qquad
R^1\Psi=E_\ell(-1).
\tag{9.2}
$$

Globally $R^1\Psi$ is a skyscraper sheaf on the geometric node set. The weight complex glues those generators through the vertex--edge incidence map. Consequently one node need not give one global monodromy block: separating nodes die in the graph homology.

Proper comparison identifies

$$
R\Gamma(Y,R\Psi E_\ell)
\simeq R\Gamma(C_{\bar K},E_\ell).
\tag{9.3}
$$

The specialization map from ordinary $H^1(Y)$ lands in $\ker N$, and in the strict semistable curve case it identifies $H^1(Y)$ with inertia invariants.

### 9.3 The one-direction surface complex

For $Y=Y_0\cup Y_1$ with double curve $D$, the only higher local sheaf is $R^1\Psi$, locally constant of rank one along $D$ with twist $(-1)$. There is no $R^2\Psi$ because there are no triple points.

In degree two, candidate monodromy classes arise from $H^1(D)(-1)$ and their duals. The relevant maps are the alternating restrictions

$$
H^1(Y_0)\oplus H^1(Y_1)\longrightarrow H^1(D)
\tag{9.4}
$$

and the adjoint Gysin map

$$
H^1(D)(-1)\longrightarrow
H^3(Y_0)(-1)\oplus H^3(Y_1)(-1).
\tag{9.5}
$$

The surviving quotient on the restriction side is dual to the surviving kernel on the Gysin side. Their common dimension is the number of length-two monodromy blocks in $H^2$.

### 9.4 The two-direction surface complex

At a double curve the local stalks are $E_\ell$ and $E_\ell(-1)$. At a triple point they are

$$
E_\ell,\qquad E_\ell(-1)^2,\qquad E_\ell(-2)
\tag{9.6}
$$

in degrees zero, one, and two. The two degree-one generators correspond to three branches modulo their sum; their exterior product gives degree two.

Globally, triple-point generators are joined to double-curve and component cohomology by $\rho+\gamma$. The extreme survivors are (8.4). In particular, merely counting triple points overestimates $\operatorname{rank}N^2$ whenever their zero-cycles bound in the dual complex.

The small resolution replaces the non-semistable fourfold meeting by two triple-incidence simplices. Formula (9.1) now applies everywhere. Proper birational comparison with the common generic fiber proves that the resulting abutment is the cohomology of the original parahoric Shimura surface.

### 9.5 Coefficients from PEL geometry

Let $\mathcal L_\ell$ be a lisse $E_\ell$-sheaf obtained by an integral algebraic construction from the universal prime-to-$p$ Tate module, and suppose it extends lisse over the chosen semistable model. Then

$$
(R^a\Psi\mathcal L_\ell)_x
\simeq \mathcal L_{\ell,x}\otimes
\bigwedge^a C_x(-a).
\tag{9.7}
$$

This follows by trivializing $\mathcal L_\ell$ étale locally and applying (9.1). If the universal abelian scheme itself has only semiabelian reduction and the coefficient sheaf is ramified along a component, (9.7) is false; its inertia complex must be combined with the geometric Kummer complex. Constant coefficients, which are the inputs for the following cohomological realizations, have no such defect.

Integral coefficients require saturation checks. The local groups in (9.1) are free over $\mathbf Z/\ell^n$, but global kernels and cokernels of incidence maps can have torsion.

## 10. Weight and monodromy filtrations

### 10.1 The logarithm of inertia

On a strict semistable model inertia is unipotent. For $\sigma$ in a sufficiently small open subgroup of inertia,

$$
\rho(\sigma)=\exp(t_\ell(\sigma)N).
\tag{10.1}
$$

Thus for curves $N^2=0$ and

$$
\rho(\sigma)=1+t_\ell(\sigma)N,
$$

while for surfaces $N^3=0$ and

$$
\rho(\sigma)=1+t_\ell(\sigma)N+
\frac{t_\ell(\sigma)^2}{2}N^2.
\tag{10.2}
$$

The nilpotence bounds follow from the maximum number of components meeting: two for curves and three for surfaces. At $\ell=2$, (10.2) is a rational formula; preservation of a chosen lattice is not automatic because of the denominator.

### 10.2 Curves: three graded pieces

For $V=H^1(C_{\bar K},E_\ell)$, the weight spectral sequence yields

$$
\operatorname{gr}_0^M V=H^1(\Gamma,E_\ell),
$$

$$
\operatorname{gr}_1^M V=
\bigoplus_{v}H^1(Y_v,E_\ell),
$$

$$
\operatorname{gr}_2^M V=
H_1(\Gamma,E_\ell)(-1).
\tag{10.3}
$$

There are no possible higher differentials in total degree one. The graph pairing identifies

$$
N:\operatorname{gr}_2^M V
\xrightarrow{\sim}
\operatorname{gr}_0^M V(-1).
\tag{10.4}
$$

Hence this is the monodromy filtration centered at one and

$$
\operatorname{rank}N=b_1(\Gamma).
\tag{10.5}
$$

The component cohomology is killed by $N$. It contributes unramified length-one blocks, while every graph cycle contributes one length-two block.

### 10.3 Surfaces: five possible graded pieces

For $V=H^2(S_{\bar K},E_\ell)$, the stratum filtration has possible indices $0$ through $4$:

$$
0\subset M_0\subset M_1\subset M_2
\subset M_3\subset M_4=V.
\tag{10.6}
$$

The extreme terms are

$$
\operatorname{gr}_0^M V\simeq H^2(\Delta(Y),E_\ell),
$$

$$
\operatorname{gr}_4^M V\simeq
H_2(\Delta(Y),E_\ell)(-2).
\tag{10.7}
$$

The odd terms are the surviving restriction and Gysin subquotients of $H^1(Y^{(2)})$. The middle term contains compatible classes in $H^2(Y^{(1)})$ and the triple-point correction. Monodromy has maps

$$
N:\operatorname{gr}_{a}^M\to
\operatorname{gr}_{a-2}^M(-1),
\qquad
N^2:\operatorname{gr}_4^M\to
\operatorname{gr}_0^M(-2).
\tag{10.8}
$$

The full $E_1$ complex, rather than a dimension slogan, determines these subquotients. This matters when component surfaces have nonalgebraic middle cohomology or double curves have positive genus.

### 10.4 When the weight filtration is the monodromy filtration

Assume $k$ is finite. The component surfaces and curves are smooth and proper, so their cohomology is pure of its usual weight. Tate twists shift weights by two. Terms of different weights admit no nonzero Frobenius-equivariant differential after semisimplifying Frobenius, so the weight spectral sequence degenerates at $E_2$ in the present dimensions.

To identify its filtration with the canonical monodromy filtration, it remains to prove nondegeneracy of the symmetric restriction--Gysin pairings. At the extremes this is the cellular intersection pairing on the dual complex; on the odd pieces it is Poincaré duality on double curves modulo mutually orthogonal image and kernel subspaces. Duality shows that the induced maps have equal source and target dimensions. The local monodromy maps are identities on matching stratum summands, and nondegeneracy makes them isomorphisms on the surviving quotients. Therefore

$$
N^a:\operatorname{gr}_{2+a}^M V
\xrightarrow{\sim}
\operatorname{gr}_{2-a}^M V(-a)
\qquad(a=1,2).
\tag{10.9}
$$

This proves the monodromy--weight identification for these strict semistable curves and surfaces under the stated purity and pairing hypotheses. Over a general perfect residue field, the same stratum filtration and monodromy maps exist, but the word “weight” is not assigned without a Frobenius weight theory.

### 10.5 Integral lattices and saturation

Let $T=H^m(X_{\bar K},\Lambda_\ell)$ modulo torsion. The rational filtration meets $T$ in a canonical lattice filtration, but (10.4) and (10.9) need not be integral isomorphisms. For curves, the integral map is

$$
H_1(\Gamma,\mathbf Z_\ell)
\xrightarrow{q}
H_1(\Gamma,\mathbf Z_\ell)^\vee,
\tag{10.10}
$$

and its cokernel is the $\ell$-primary graph discriminant. For surfaces, the analogous finite quotients are discriminants of the incidence and restriction--Gysin lattices.

If a Hecke projector is defined only after dividing by an integer divisible by $\ell$, its image lattice may be nonsaturated. Rational local type is still well defined, but no canonical integral type lattice follows. Every integral conclusion later is therefore conditional on the relevant projector and incidence images being saturated.

## 11. Conductor and type for quaternionic curves

### 11.1 The conductor formula

For an $E_\ell$-representation $V$ of $G_K$, the Artin conductor exponent is

$$
a(V)=\dim V-\dim V^{I_K}+\operatorname{Sw}(V).
\tag{11.1}
$$

After quasi-unipotent reduction, write the Weil--Deligne representation as $(r,N)$. Then

$$
V^{I_K}=(\ker N)^{r(I_K)},
$$

so

$$
a(V)=\dim V-\dim(\ker N)^{r(I_K)}+
\operatorname{Sw}(r).
\tag{11.2}
$$

For a strict semistable model over $K$, $r$ is trivial on inertia and the Swan term vanishes. Hence

$$
a(V)=\operatorname{rank}N.
\tag{11.3}
$$

The simple formula is not valid before finite descent has been restored.

### 11.2 Graph computation at split semistable level

Apply (11.3) and (10.5) to the quaternionic curve:

$$
a\left(H^1(C_{\bar K},E_\ell)\right)
=b_1(\Gamma).
\tag{11.4}
$$

For two components meeting in $m$ points this is $m-1$. The local Euler polynomial is

$$
P(T)=\det\left(1-FT\mid\ker N\right).
\tag{11.5}
$$

Specialization identifies $\ker N$ with $H^1(Y,E_\ell)$. Its normalization sequence filters it by $H^1(\Gamma)$ and $\bigoplus H^1(Y_v)$, so Frobenius on both the incidence graph and the normalized components is needed to compute (11.5).

The conductor does not determine the component group. Thickness scales the integral pairing and can enlarge (4.4) while leaving $b_1(\Gamma)$ unchanged.

### 11.3 Two-dimensional constituents and special type

Let $W$ be a two-dimensional $G_K$- and Hecke-stable subquotient of $H^1$. Since $N^2=0$, either $N|_W=0$ or it has rank one. In the second case choose a basis $e_0,e_1$ with

$$
Ne_1=e_0,\qquad Ne_0=0.
\tag{11.6}
$$

If finite inertia is trivial, $W$ has one length-two unipotent block and

$$
a(W)=1.
\tag{11.7}
$$

Its Weil--Deligne type is special: after an unramified character twist, the nilpotent operator is the standard nonzero operator on a two-dimensional special representation. This is the precise geometric content behind the phrase “Steinberg type.” The twist and Frobenius eigenvalue are not determined by $N$ alone; they are read from $F$ on $\ker N$.

If $N|_W=0$, the semistable geometry only says that the unipotent part is absent. At strict level $W$ is unramified; after descent it may still have nontrivial finite inertia.

### 11.4 Finite and nonsplit descent

Suppose strict semistability is reached over $K'/K$. The finite group can permute graph vertices and edges, and can reverse an edge orientation. On the graph pieces,

$$
r(I_K)\curvearrowright H^1(\Gamma,E_\ell),
\qquad
r(I_K)\curvearrowright H_1(\Gamma,E_\ell)(-1),
$$

dually. Formula (11.2), not (11.4), gives the conductor over $K$.

A nonsplit multiplicative rank-two constituent still has nonzero $N$ and conductor one when its finite character is unramified, but Frobenius acts with the opposite sign on its graph line. A ramified quadratic finite character can increase the codimension of invariants without changing the rank of $N$. Wild descent contributes the Swan term. These distinctions are exactly why the local type is the pair $(r,N)$ together with Frobenius, rather than the integer conductor.

## 12. Conductor and type for unitary surfaces

### 12.1 Ranks of $N$ and $N^2$

Let

$$
V=H^2(S_{\bar K},E_\ell),
\qquad r_1=\operatorname{rank}N,
\qquad r_2=\operatorname{rank}N^2.
$$

If $n_j$ is the number of Jordan blocks of length $j$, elementary Jordan theory gives

$$
n_3=r_2,
\qquad n_2=r_1-2r_2,
\qquad n_1=\dim V-2r_1+r_2.
\tag{12.1}
$$

Indeed a length-three block contributes ranks $2$ and $1$ to $N$ and $N^2$, a length-two block contributes $1$ and $0$, and a length-one block contributes neither. Thus $r_1$ alone does not determine the local type.

Under monodromy--weight,

$$
r_2=\dim H_2(\Delta(Y),E_\ell),
\tag{12.2}
$$

and $n_2$ is the dimension of the primitive surviving double-curve term.

### 12.2 One bad direction

For $Y=Y_0\cup Y_1$ there are no triple points and the dual complex has no $H_2$. Therefore

$$
N^2=0.
\tag{12.3}
$$

Let

$$
Q_D=\operatorname{coker}\left(
H^1(Y_0)\oplus H^1(Y_1)\xrightarrow{\rho}H^1(D)
\right).
\tag{12.4}
$$

Duality identifies $Q_D^\vee(-1)$ with the kernel of the Gysin map (9.5). Monodromy is an isomorphism between these two surviving pieces. Consequently

$$
\operatorname{rank}N=\dim Q_D.
\tag{12.5}
$$

This formula is exact under the degeneration statement of Section 10.4. If $D$ is a union of rational curves, then $H^1(D)=0$ and this source of middle monodromy vanishes. If $D$ has positive genus, its entire $H^1$ still need not survive: restrictions from the two components can exhaust it.

### 12.3 Two bad directions

The two-direction resolution can have both length-two and length-three blocks. In the product-incidence situation of Section 8.4,

$$
r_2=b_1(\Gamma_1)b_1(\Gamma_2).
\tag{12.6}
$$

This agrees with the tensor calculation. If $V_i=H^1(C_i)$ has monodromy $N_i$, then on $V_1\otimes V_2$,

$$
N=N_1\otimes1+1\otimes N_2,
$$

and, since $N_i^2=0$,

$$
N^2=2N_1\otimes N_2.
\tag{12.7}
$$

Over $E_\ell$ the factor $2$ does not affect rank. It matters integrally at $\ell=2$.

Outside a global product decomposition, (12.6) is replaced by the homology of the actual dual complex and the actual double-curve restriction--Gysin complex. The local product chart alone does not force a global tensor factorization.

### 12.4 Jordan blocks, conductor, and Euler factor

At split strict semistable level,

$$
a(V)=r_1.
\tag{12.8}
$$

After finite descent,

$$
a(V)=\dim V-\dim(\ker N)^{r(I_K)}+
\operatorname{Sw}(r).
\tag{12.9}
$$

The local Euler polynomial is

$$
P(V,T)=\det\left(
1-FT\mid(\ker N)^{r(I_K)}
\right).
\tag{12.10}
$$

A complete report of the middle-degree type therefore includes

$$
r|_{I_K},\quad N,\quad r_2,\quad
\operatorname{Sw}(r),\quad
F\text{ on }(\ker N)^{r(I_K)}.
\tag{12.11}
$$

Two length-two blocks and one length-three block both give $r_1=2$, but only the latter has $r_2=1$. Two representations with the same Jordan blocks can have different Euler factors. The conductor is a necessary summary, not a classification.

### 12.5 The rank-two Hecke constituent

Let $W$ be a two-dimensional Hecke-isotypic subquotient of $H^2$ stable under $G_K$. Dimensional reasons force $N^2|_W=0$. Hence the alternatives are again

$$
N|_W=0
\quad\text{or}\quad
\operatorname{rank}N|_W=1.
$$

At split strict level, the second has conductor one and special Weil--Deligne type after the appropriate unramified twist. The presence of length-three blocks in the full surface cohomology does not imply that a chosen two-dimensional constituent has $N^2\ne0$; it cannot. Instead such blocks must lie in larger Hecke constituents or decompose after coefficient extension into pieces on which the Hecke algebra is not simultaneously isolating two dimensions.

This observation is the precise bridge to local--global compatibility: geometry supplies the operator on full cohomology, while a Hecke projector determines which part of that operator belongs to the automorphic constituent.

## 13. Hecke correspondences and functorial monodromy

### 13.1 Extension away from the bad prime

Let $g\in G(\mathbf A_f^p)$. Changing prime-to-$p$ level gives a diagram of parahoric PEL moduli schemes

$$
\mathscr X_K
\xleftarrow{p_1}
\mathscr X_{K\cap gKg^{-1}}
\xrightarrow{p_2}
\mathscr X_K.
\tag{13.1}
$$

The maps are finite étale at fine level. The universal prime-to-$p$ isogeny respects the $p$-adic lattice chain because its degree is prime to $p$. Hence both maps extend across the bad fiber and preserve the local-model stratification up to permutation.

The induced Hecke operator is the normalized pull--push

$$
T_g=(p_2)_*p_1^*.
\tag{13.2}
$$

Normalization factors must be fixed consistently with the generic Hecke algebra; multiplying an operator by a degree does not affect commutation with monodromy but does affect integral lattices.

### 13.2 Action on strata and nearby cycles

Nearby cycles are functorial for pullback and proper pushforward. Therefore (13.1) acts on

$$
R\Gamma(Y,R\Psi E_\ell)
$$

and commutes with inertia, Frobenius, and $N$. On the weight complex it acts by the induced finite maps of component surfaces, double curves, triple points, and their cohomology. Projection formulas make it commute with the restriction--Gysin differential.

Consequently every $E_r$ page is a Hecke module and all monodromy filtrations are Hecke-stable. A calculation can therefore be performed before or after applying an idempotent, provided the idempotent is defined over the chosen coefficient field and the relevant functor is exact.

At the bad prime itself, a degeneracy correspondence can change the lattice chain and need not be finite étale. Its extension must be constructed from the explicit PEL isogeny diagram and checked against the local model. No general integral $p$-Hecke action is inferred here.

### 13.3 Projectors and coefficient fields

Let $\mathbb T^p$ be the commutative Hecke algebra away from $p\ell$. For an idempotent $e\in\mathbb T^p\otimes E_\ell$,

$$
eN=Ne,
\qquad eF=Fe.
\tag{13.3}
$$

Thus $(r,N)$ restricts to $eV$. If $e$ exists only after extending $E_\ell$, all dimensions and conductors are unchanged by that coefficient extension. If $e$ is only a generalized eigenspace projector rather than an idempotent in the integral algebra, the rational constituent is still well defined, but an integral direct summand need not be.

The conductor is additive in short exact sequences of Weil--Deligne representations. Hence one may compute it on a semisimplified Hecke decomposition, while extension data between equal Hecke eigensystems can still matter for integral lattices.

### 13.4 The local--global compatibility package

For a Hecke-isolated constituent $W$, the geometry supplies the following data at the bad prime:

1. the finite inertial action on the relevant stratum subquotient;
2. the nilpotent map induced by the restriction--Gysin complex;
3. $\operatorname{rank}N$ and, in full surface degree two, $\operatorname{rank}N^2$;
4. the Artin and Swan conductors from (11.2) or (12.9);
5. geometric Frobenius on inertia invariants, hence the local Euler polynomial;
6. the integral monodromy discriminant when the Hecke and incidence lattices are saturated.

For a two-dimensional constituent with trivial finite inertia, nonzero $N$ is precisely special type and gives conductor exponent one. Zero $N$ gives unramified type. With finite inertia present, the same dichotomy concerns only the unipotent part and must be combined with $r|_{I_K}$.

This package is geometric input to a local--global comparison theorem. Identifying it with the parameter of a particular automorphic representation also uses the automorphic decomposition and local representation theory; those are separate dependencies and are not assumed here.

## 14. The semistable bad-prime theorem

### 14.1 Unified construction and computation

**Theorem 14.1 (semistable models and monodromy package).** Let $R$ and $\ell$ be as in Section 1.2. Let $\mathscr X_K$ be either the selected compact quaternionic Shimura curve or the selected compact unitary modèles étranges surface. Assume:

- a PEL realization and selected canonical component union have been fixed;
- the adjoint datum is anisotropic modulo center and the prime-to-$p$ level is neat;
- at $p$, every active bad factor is the verified rank-two periodic lattice chain (2.1), with flat local model $M^{\mathrm{Iw}}$;
- the remaining active factor, if any, is hyperspecial with smooth projective-line local model;
- in the two-direction surface case, a labeling or finite cover permits one of the small resolutions of Chapter 6;
- coefficient sheaves, when used, extend lisse over the semistable model.

Then:

1. the parahoric PEL functor is represented by a projective flat model carrying the universal isogeny chain;
2. the quaternionic curve is regular strictly semistable with node charts $xy=\pi$;
3. the one-direction unitary surface is regular strictly semistable with charts $xy=\pi$ times a smooth parameter;
4. the two-direction raw surface has product-node charts, and blowing up a chosen branch ideal gives a projective strict semistable modification with charts $xyz=\pi$;
5. after the finite base changes allowed in Chapter 7, normalization and the explicit chain and small resolutions give a semistable alteration, with the finite descent action retained;
6. nearby cycles are computed from component, double-curve, and triple-point strata by the restriction--Gysin complex;
7. on curve $H^1$, $N^2=0$, $\operatorname{rank}N=b_1(\Gamma)$, and at split strict level the conductor is $b_1(\Gamma)$;
8. on surface $H^2$, $N^3=0$, the extreme $N^2$ term is controlled by $H_2(\Delta(Y))$, the length-two primitive term by surviving $H^1$ of double curves, and the Jordan counts are (12.1);
9. at split strict level $a(H^m)=\operatorname{rank}N$; over the original field the exact formula is (12.9), including finite inertia and Swan conductor;
10. prime-to-$p$ Hecke correspondences act on the stratum complex and commute with Frobenius and monodromy, so the complete type restricts to every rational Hecke constituent.

**Proof.** Statements 1--4 are Theorems 2.1, 4.1, 5.1, and Proposition 6.1. Statement 5 is Proposition 7.1 together with finite descent. The local exterior-algebra calculation (9.1), resolved by the ordered incidence complex, proves statement 6. The curve weight complex and graph pairing prove statement 7. The surface weight complex, duality, and the monodromy--weight identification prove statement 8. The Artin conductor formula proves statement 9. Functoriality of nearby cycles and proper pull--push proves statement 10. $\square$

### 14.2 Hypothesis ledger and failure modes

Every hypothesis has a visible failure mode.

If the determinant locus is not the flat incidence model, the moduli scheme can have extra vertical components or nilpotents. If a lattice chain is deeper than Iwahori, more components and different singularities appear. If the two unitary directions are coupled by an unverified integral condition, their local model need not be a product.

If anisotropy is dropped, semiabelian boundary points can occur and the proper moduli argument must be replaced by a compactification theory. If the level quotient has fixed points, the coarse model can have quotient singularities. If a ramified base change is not followed by normalization, even normality can fail. If the product of nodes is left unresolved, four components meet at one point and the strict semistable nearby-cycle formula does not apply.

If components or nodes are nonsplit, the geometric incidence complex must retain the signed Galois action. If a coefficient sheaf is ramified along the special divisor, the tensor formula (9.7) is false. If the residue field is not finite, the monodromy filtration exists but Frobenius weights are not assigned by the argument of Section 10.4. If integral images are not saturated, rational monodromy does not determine the integral type lattice.

Finally, neither a reducible fiber nor a triple point alone forces monodromy. Curve monodromy counts graph cycles, not edges. Surface $N^2$ counts surviving two-cycles in the dual complex, not triple points. Double-curve monodromy counts a restriction--Gysin subquotient, not the sum of the genera.

### 14.3 Conclusion

Bad reduction in these Shimura varieties is controlled because the active integral linear algebra has rank two. A neighboring pair of lattices produces an incidence of two lines, and that incidence produces the node $xy=\pi$. One bad direction gives the entire semistable geometry of a quaternionic curve or a normal crossing of two unitary surface components. Two bad directions produce the product of two nodes; its small resolution, calculated chart by chart, replaces an impermissible fourfold meeting by triple normal crossings.

Once the model is strict semistable, its arithmetic memory is distributed across its strata. Components retain their own cohomology. Double curves supply possible length-two monodromy. Triple incidences and the topology of the dual complex supply possible length-three blocks. Restriction and Gysin maps decide which local generators survive globally. The logarithm of tame inertia then turns that incidence geometry into $N$, while finite descent restores the part of inertia that semistable base change temporarily removed.

For curves the answer is the weighted graph pairing: graph cycles are exactly the special blocks, their rank is the conductor at split semistable level, and their integral discriminant is component data. For surfaces the answer is a five-step filtration: double-curve cohomology governs the first monodromy rank and dual-complex two-cycles govern the square of monodromy. The conductor records the first rank but not the second, the finite inertial action, or Frobenius.

Prime-to-$p$ Hecke correspondences preserve every layer of this construction. Therefore the geometric pair $(r,N)$, its conductor, its Frobenius polynomial, and—when saturation permits—its integral monodromy lattice pass to the Hecke constituents used in local--global compatibility. This is the complete bad-prime counterpart of smooth proper comparison: not constancy of cohomology, but an explicit account of exactly how it changes.
