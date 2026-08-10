# Néron Models and Component Groups

## Contents

1. [The integral extension problem](#1-the-integral-extension-problem)
   - [Why a new model is needed](#11-why-a-new-model-is-needed)
   - [Conventions and the local-global viewpoint](#12-conventions-and-the-local-global-viewpoint)
   - [Three guiding examples](#13-three-guiding-examples)
2. [The Néron mapping property](#2-the-néron-mapping-property)
   - [Definition and first consequences](#21-definition-and-first-consequences)
   - [Uniqueness and testing the property](#22-uniqueness-and-testing-the-property)
   - [Good reduction](#23-good-reduction)
   - [Why smooth test spaces are exact](#24-why-smooth-test-spaces-are-exact)
3. [Smoothening integral models](#3-smoothening-integral-models)
   - [Weak Néron models](#31-weak-néron-models)
   - [Dilatations and the defect of a section](#32-dilatations-and-the-defect-of-a-section)
   - [The smoothening theorem](#33-the-smoothening-theorem)
   - [What smoothening does not yet provide](#34-what-smoothening-does-not-yet-provide)
4. [Existence of Néron models](#4-existence-of-néron-models)
   - [The extension sheaf](#41-the-extension-sheaf)
   - [Representability from a weak model](#42-representability-from-a-weak-model)
   - [The existence theorem for abelian varieties](#43-the-existence-theorem-for-abelian-varieties)
   - [Gluing over a Dedekind base](#44-gluing-over-a-dedekind-base)
5. [Group structure and functoriality](#5-group-structure-and-functoriality)
   - [Extending the group law](#51-extending-the-group-law)
   - [Homomorphisms, products, and endomorphisms](#52-homomorphisms-products-and-endomorphisms)
   - [Isogenies and their limitations](#53-isogenies-and-their-limitations)
   - [Dual abelian varieties and polarizations](#54-dual-abelian-varieties-and-polarizations)
6. [Identity components and component groups](#6-identity-components-and-component-groups)
   - [The open identity subgroup](#61-the-open-identity-subgroup)
   - [The finite étale component group](#62-the-finite-étale-component-group)
   - [Reduction and the component map](#63-reduction-and-the-component-map)
   - [The structure of the connected special fiber](#64-the-structure-of-the-connected-special-fiber)
7. [Reduction types and basic calculations](#7-reduction-types-and-basic-calculations)
   - [Good, semistable, and additive reduction](#71-good-semistable-and-additive-reduction)
   - [Elliptic curves](#72-elliptic-curves)
   - [Products and unramified twists](#73-products-and-unramified-twists)
   - [What the component group can and cannot detect](#74-what-the-component-group-can-and-cannot-detect)
8. [Change of the valuation ring](#8-change-of-the-valuation-ring)
   - [The canonical base-change morphism](#81-the-canonical-base-change-morphism)
   - [Unramified base change](#82-unramified-base-change)
   - [Ramified base change](#83-ramified-base-change)
   - [Descent and Galois action](#84-descent-and-galois-action)
9. [The Picard route to the Néron model](#9-the-picard-route-to-the-neron-model)
   - [Regular curve models and relative line bundles](#91-regular-curve-models-and-relative-line-bundles)
   - [The closure of the generic identity](#92-the-closure-of-the-generic-identity)
   - [The Raynaud quotient theorem](#93-the-raynaud-quotient-theorem)
   - [Independence of the regular model](#94-independence-of-the-regular-model)
10. [Intersection theory and components of Jacobians](#10-intersection-theory-and-components-of-jacobians)
    - [The weighted intersection complex](#101-the-weighted-intersection-complex)
    - [The component-group formula](#102-the-component-group-formula)
    - [Specialization of divisor classes](#103-specialization-of-divisor-classes)
    - [Nonreduced fibers and the index](#104-nonreduced-fibers-and-the-index)
11. [Semistable Jacobians](#11-semistable-jacobians)
    - [The connected special fiber](#111-the-connected-special-fiber)
    - [The graph formula](#112-the-graph-formula)
    - [Weighted nodes and regular resolution](#113-weighted-nodes-and-regular-resolution)
    - [Four exact examples](#114-four-exact-examples)
12. [Morphisms, specialization, and pairings](#12-morphisms-specialization-and-pairings)
    - [Maps induced by curves](#121-maps-induced-by-curves)
    - [Maps on component groups](#122-maps-on-component-groups)
    - [The component pairing for Jacobians](#123-the-component-pairing-for-jacobians)
    - [Prime-to-residue-characteristic torsion](#124-prime-to-residue-characteristic-torsion)
13. [Global Néron models](#13-global-neron-models)
    - [Localization at the bad places](#131-localization-at-the-bad-places)
    - [Sections and arithmetic component maps](#132-sections-and-arithmetic-component-maps)
    - [Exact global bookkeeping](#133-exact-global-bookkeeping)
    - [The reusable comparison package](#134-the-reusable-comparison-package)
14. [Conclusion](#14-conclusion)
   - [The mathematical package](#141-the-mathematical-package)
   - [The boundary with monodromy theory](#142-the-boundary-with-monodromy-theory)

## 1. The integral extension problem

### 1.1 Why a new model is needed

Let $R$ be a discrete valuation ring with fraction field $K$. An abelian variety $A/K$ is already smooth, proper, and connected, but these adjectives describe only its generic geometry. Arithmetic questions ask whether a $K$-point specializes, whether a homomorphism survives reduction, and which connected component receives the specialization of a divisor class. To ask any of these questions geometrically, one needs an $R$-scheme with generic fiber $A$.

There are many integral models and none of the obvious requirements selects the right one. A projective closure is proper but usually singular. Resolving it gives a regular model but not a group scheme. If $A$ has bad reduction, no abelian scheme over $R$ can have generic fiber $A$. Properness is therefore too rigid, while an arbitrary smooth model is not canonical enough.

The decisive idea is to characterize the model by the maps it receives. A smooth $R$-scheme $T$ has no vertical singularity obstructing extension. A map $T_K\to A$ should consequently extend uniquely to the desired model. The resulting universal property simultaneously does three jobs:

$$
\begin{array}{c}
\text{generic points extend}\qquad
\text{generic homomorphisms extend}\qquad
\text{different constructions become canonically identical}.
\end{array}
$$

The model characterized this way is the **Néron model**. Its failure to be proper is not a defect. At bad reduction, nonproper connected algebraic groups and additional connected components are precisely the geometric record of degeneration.

This book develops the theory in the order demanded by that idea. We first isolate the mapping property, then prove existence by smoothening and representability, and only afterward analyze the special fiber. The final chapters identify the Néron model of a Jacobian with a separated relative Picard quotient and recover its component group from the intersection matrix of a regular curve model.

### 1.2 Conventions and the local-global viewpoint

A **Dedekind scheme** in this book is a connected normal noetherian scheme of dimension one. It is assumed excellent whenever normalization or smoothening is used. Its generic point is $\eta$ and its function field is $K$. For a closed point $s$, the local ring $\mathcal O_{S,s}$ is a discrete valuation ring, its residue field is $k(s)$, and $S_s=\operatorname{Spec}\mathcal O_{S,s}$.

Most proofs are local. We then write

$$
S=\operatorname{Spec}R,
$$

where $R$ is an excellent discrete valuation ring with fraction field $K$, uniformizer $\pi$, and residue field $k$. The strict henselization is $R^{\mathrm{sh}}$, with fraction field $K^{\mathrm{sh}}$ and separably closed residue field $k^s$. Henselianity will always be stated when lifting $k$-points is used.

An **abelian variety** is a smooth proper geometrically connected group variety over a field. An **abelian scheme** is its relative analogue: a smooth proper finitely presented group scheme with geometrically connected fibers. Book 38 supplies dual abelian schemes, isogenies, polarizations, and the extension theorem when both generic varieties already have abelian-scheme models. Here the generic abelian variety may have bad reduction, so proper models are not assumed.

For a smooth group scheme $\mathcal A/S$ of finite type, $\mathcal A_s^0$ denotes the connected component of the identity in the fiber. Later we construct an open subgroup scheme $\mathcal A^0\subseteq\mathcal A$ whose special fiber is $\mathcal A_s^0$. The component group is

$$
\Phi_A=\mathcal A_s/\mathcal A_s^0.
$$

It is a finite étale $k$-group scheme. The abstract geometric group is $\Phi_A(k^s)$, carrying its natural Galois action. We do not identify $\Phi_A(k)$ with the whole geometric group unless that action is trivial.

The regular-model input comes from Books 10 and 12. Thus a smooth projective curve over $K$ admits a regular proper model after the stated excellence hypotheses, and a semistable fiber has a geometric dual graph whose edge lengths record node thickness. The vertical intersection and negativity theorem used for nonreduced fibers is the arithmetic-surface result of Book 11. Book 36 supplies relative Picard schemes and generalized Jacobians. We recall the necessary notation at the point of use rather than duplicating those constructions.

### 1.3 Three guiding examples

The first example is good reduction. Suppose $A$ extends to an abelian scheme $\mathcal B/R$. Then $\mathcal B$ itself will be the Néron model. Its special fiber is connected and proper, so

$$
\mathcal B^0=\mathcal B,
\qquad \Phi_A=0.
$$

The second example is a split multiplicative elliptic curve. Its minimal regular curve model has special fiber a polygon of $n$ rational curves. The Néron model is the smooth locus of that regular model. Its connected special fiber is $\mathbf G_m$, while its components form a cycle:

```text
identity component -- 1 -- 2 -- ... -- (n-1) -- back to 0
```

Consequently

$$
\mathcal E_k^0\simeq\mathbf G_m,
\qquad
\Phi_E(k^s)\simeq\mathbf Z/n\mathbf Z.
$$

The Néron model is smooth but not proper: properness would force the multiplicative group in the special fiber to become an elliptic curve, which is impossible.

The third example is a semistable Jacobian. If the geometric special fiber of a regular semistable curve has normalized components $Y_v$ and dual graph $\Gamma$, then

$$
0\longrightarrow T_\Gamma
\longrightarrow\mathcal J_k^0
\longrightarrow\prod_vJ(Y_v)
\longrightarrow0,
$$

with $X^*(T_\Gamma)=H_1(\Gamma,\mathbf Z)$. Its component group is the graph Jacobian. Here a single degeneration separates into three visible pieces: ordinary Jacobians of components, a torus from graph cycles, and a finite component group from the integral defect of the graph pairing.

These examples already show why neither the identity component nor the component group alone determines reduction. A one-loop graph of thickness one gives a nontrivial torus but trivial component group. Conversely, knowing only the order of the component group loses its Galois action and its functorial maps.

## 2. The Néron mapping property

### 2.1 Definition and first consequences

The definition is designed to make every smooth integral test family behave as if the target were proper, while retaining a smooth target.

**Definition 2.1.** Let $X/K$ be a smooth separated scheme of finite type. A **Néron model** of $X$ over $S$ is a smooth separated $S$-scheme $\mathcal X$ of finite type, together with an identification $\mathcal X_K\simeq X$, such that for every smooth $S$-scheme $T$ of finite type, restriction induces a bijection

$$
\operatorname{Hom}_S(T,\mathcal X)
\xrightarrow{\sim}
\operatorname{Hom}_K(T_K,X). \tag{2.1}
$$

When one permits $\mathcal X$ to be only locally of finite type, it is called a **Néron lft-model**. Abelian varieties have finite-type Néron models; the distinction matters for some tori and other nonproper groups.

Taking $T=S$ in (2.1) gives

$$
\mathcal X(S)\simeq X(K). \tag{2.2}
$$

Thus every rational point extends uniquely to a section. More generally, after replacing $S$ by any étale $S$-scheme $S'$, the same property gives $\mathcal X(S')\simeq X(K(S'))$ componentwise. This explains why unramified points are built into the model.

Separatedness is necessary for uniqueness. Smoothness of the target is necessary for the identity map $\mathcal X_K\to X$ to qualify as a test extension and for the special fiber to have stable infinitesimal geometry. Finite type is a boundedness conclusion, not a harmless convention; Chapter 4 proves it for abelian varieties.

**Proposition 2.2.** Formation of a Néron model commutes with restriction to a nonempty open subscheme of $S$.

**Proof.** Let $U\subseteq S$. The restriction $\mathcal X_U$ is smooth, separated, and of finite type. A smooth $U$-scheme $T$ is locally a smooth $S$-scheme after shrinking an ambient finite-presentation model around $T$: smoothness is open. Applying (2.1) on these neighborhoods and using uniqueness glues the extensions. Hence $\mathcal X_U$ has the mapping property. $\square$

The converse gluing statement requires local models at the omitted closed points and is proved in Section 4.4.

### 2.2 Uniqueness and testing the property

The first reward of a universal property is canonical uniqueness.

**Theorem 2.3 (uniqueness).** If $\mathcal X$ and $\mathcal X'$ are Néron models of the same $X/K$, there is a unique $S$-isomorphism $\mathcal X\simeq\mathcal X'$ inducing the identity on $X$.

**Proof.** Use $T=\mathcal X$ in the mapping property of $\mathcal X'$ to extend the generic identity to $f:\mathcal X\to\mathcal X'$. Reverse the roles to obtain $g$. Both $gf$ and the identity on $\mathcal X$ extend the same generic map, so uniqueness in (2.1) gives $gf=1$. Similarly $fg=1$. $\square$

Several smaller tests suffice to verify the property. They are useful because a construction usually first controls sections over unramified valuation rings.

**Proposition 2.4 (local test).** Let $R$ be henselian and let $\mathcal X/R$ be smooth and separated with generic fiber $X$. Suppose that:

1. for every finite étale extension $R'/R$, the map $\mathcal X(R')\to X(K')$ is bijective;
2. for every smooth affine $R$-scheme $T$ and generic map $u_K:T_K\to X$, the map extends on an open subset containing every generic point of $T_k$.

Then $\mathcal X$ has the Néron mapping property.

**Proof strategy.** The first condition supplies values at closed geometric points of the special fiber. The second supplies an extension in codimension one. Smoothness of $T$ makes its local rings regular, and separatedness makes local extensions agree.

Let $U\subseteq T$ be the maximal open on which $u_K$ extends. By condition 2, $U$ contains the generic fiber and the generic points of $T_k$; hence $T\setminus U$ has codimension at least two. At a point $t$ of this complement, choose an étale map from a neighborhood of $t$ to affine space over $R$. Successively intersect with general relative curves through $t$. Their strict henselizations are spectra of discrete valuation rings unramified over smooth local rings. Condition 1 gives compatible values at their closed points.

Because $\mathcal X$ is smooth, these values lift through every nilpotent neighborhood; because it is separated, two lifts agreeing on the punctured neighborhood agree. The regular local ring $\mathcal O_{T,t}$ is the intersection of its height-one localizations, so the coordinate functions of an affine neighborhood of the image lie in $\mathcal O_{T,t}$. Thus the map extends across $t$. Repeating removes the complement. Uniqueness follows since $T_K$ is schematically dense in the flat scheme $T$ and $\mathcal X$ is separated. $\square$

The intersection argument in the last paragraph is the familiar Hartogs principle for maps whose target is smooth and whose graph is already controlled in codimension one. It cannot be applied to a singular test space: a rational map can meet an exceptional branch in codimension two with no unique continuation.

### 2.3 Good reduction

An abelian variety $A/K$ has **good reduction** if it extends to an abelian scheme over $R$. The mapping property makes that extension canonical.

**Theorem 2.5.** An abelian scheme $\mathcal A/R$ is the Néron model of its generic fiber.

**Proof strategy.** Properness extends a generic map along every valuation centered on a smooth test scheme; the group structure removes possible codimension-two indeterminacy.

Let $T/R$ be smooth and $u_K:T_K\to\mathcal A_K$. The closure of its graph in $T\times_R\mathcal A$ is proper over $T$. At every height-one point of $T$, the local ring is a discrete valuation ring, so the valuative criterion of properness gives an extension. Thus the rational map is defined away from codimension at least two.

It remains to eliminate that indeterminacy. Étale-locally on $T$, choose a section $t_0$ through a point in question and translate $u_K$ by the extended value of $u_K(t_0)$. The translated map takes $t_0$ to the identity. Apply the rigidity lemma for maps into an abelian scheme to differences

$$
u(x+y)-u(x)-u(y)
$$

on suitable smooth relative curves through the point. It shows that the graph closure is invariant under enough local translations to carry its domain of definition across the point. Equivalently, a translation-invariant codimension-two indeterminacy subset in a smooth connected fiber is either empty or the whole fiber; it cannot be the whole fiber because the map is defined at its generic points. Hence $u_K$ extends everywhere. Uniqueness follows from separatedness and density. $\square$

**Corollary 2.6.** If the Néron model $\mathcal A/R$ of an abelian variety is proper, then $A$ has good reduction and $\mathcal A$ is an abelian scheme.

**Proof.** A proper smooth finite-type group scheme has a finite étale relative component scheme. Its generic fiber is connected, so that component scheme has degree one over the connected base. Hence every geometric fiber is connected. Thus $\mathcal A$ is an abelian scheme. The converse is Theorem 2.5. $\square$

This criterion is stronger than connectedness of the special fiber. A connected special fiber may contain a torus or a unipotent group and therefore fail to be proper.

### 2.4 Why smooth test spaces are exact

One might try to demand extension from every flat $S$-scheme. That condition is too strong. Let a regular model be blown up at a special point. The blowup is flat but not smooth over $S$ along parts of its exceptional geometry, and a generic map can approach different limiting points along different branches. A universal extension target should not be required to identify such incompatible limits.

At the other extreme, testing only $S$-valued points is too weak. Two smooth separated models can have the same $R$-sections but differ after an unramified residue extension, or they can agree on sections while representing different families over a positive-dimensional test scheme. The full smooth-site property detects residue descent, infinitesimal variation, and compatibility in families.

There is also a useful functorial consequence.

**Proposition 2.7.** Let $\mathcal X$ be the Néron model of $X$. For every smooth $S$-scheme $T$, the set of generic maps $T_K\to X$ is already an étale sheaf in $T$, and $\mathcal X$ represents it.

**Proof.** Morphisms to the separated $K$-scheme $X$ satisfy étale descent. The mapping property identifies this sheaf with $T\mapsto\operatorname{Hom}_S(T,\mathcal X)$, which is represented by $\mathcal X$. $\square$

This sheaf-theoretic formulation will turn smoothening data into an actual model.

## 3. Smoothening integral models

### 3.1 Weak Néron models

Existence begins with a less ambitious object that extends unramified points but not yet arbitrary smooth families.

**Definition 3.1.** A **weak Néron model** of a smooth $K$-scheme $X$ is a smooth separated $R$-scheme $W$ of finite type with generic fiber an open subscheme of $X$, such that

$$
W(R^{\mathrm{sh}})\xrightarrow{\sim}X(K^{\mathrm{sh}}). \tag{3.1}
$$

If $X$ is proper, every $K^{\mathrm{sh}}$-point has a center on any proper $R$-model. The task is to modify that model so every center lies in its smooth locus. Book 10 supplies proper flat models and the blowup technology; here we choose the centers according to the relative smoothness defect.

The use of $R^{\mathrm{sh}}$ captures all finite unramified extensions at once. Every point involved is defined over some finite étale subextension because the schemes are of finite presentation. Thus (3.1) is equivalent to bijectivity over every finite étale extension after allowing a common refinement.

### 3.2 Dilatations and the defect of a section

Let $X/R$ be flat of finite type and let $Z\subseteq X_k$ be a closed subscheme. Blow up the ideal $(\pi,\mathcal I_Z)$ and take the open chart on which the pullback of that ideal is generated by $\pi$. This open is the **dilatation** $X'\to X$ of $Z$ in $X$. It is characterized by the following property:

$$
T\to X\text{ factors through }X'
\Longleftrightarrow
T_k\to X_k\text{ factors through }Z \tag{3.2}
$$

for every flat $R$-scheme $T$.

On an affine chart $X=\operatorname{Spec}B$ with $I_Z=(\pi,f_1,\ldots,f_r)$, the dilatation is the flat part of

$$
B[t_1,\ldots,t_r]/(f_i-\pi t_i). \tag{3.3}
$$

Indeed a map from a flat algebra sends $f_i$ into $(\pi)$ precisely when it admits unique quotients $t_i=f_i/\pi$. This proves (3.2). The generic fiber is unchanged because $\pi$ is invertible there.

To see progress, let $a:\operatorname{Spec}R'\to X$ be a section after a finite unramified extension, with special point $x$. Pull back the relative differentials and write the torsion part of $a^*\Omega^1_{X/R}$ as

$$
\bigoplus_iR'/\pi^{e_i}R'.
$$

Define the defect

$$
\delta(a)=\sum_i e_i. \tag{3.4}
$$

It vanishes exactly when $X/R$ is smooth at the special point of the section. If $Z$ contains the non-smooth locus through which $a_k$ factors and $a'$ is the lifted section on the dilatation, the relations $f_i=\pi t_i$ remove at least one power of $\pi$ from a nonzero elementary divisor. Hence

$$
\delta(a')<\delta(a) \tag{3.5}
$$

unless the lifted center is already smooth.

The inequality is the local engine of smoothening. A blind sequence of blowups need not improve relative smoothness, while dilatation divides precisely the equations that vanish too strongly along every offending section.

### 3.3 The smoothening theorem

**Theorem 3.2 (Néron smoothening).** Let $R$ be an excellent discrete valuation ring and let $X/R$ be flat, separated, and of finite type with smooth generic fiber. Assume that the set of $K^{\mathrm{sh}}$-points of $X_K$ has centers on $X$; this holds when $X$ is proper. There is a finite sequence of dilatations

$$
X_n\longrightarrow X_{n-1}\longrightarrow\cdots\longrightarrow X_0=X
$$

with centers in the non-smooth special loci such that the smooth locus $W=(X_n)_{\mathrm{sm}}$ satisfies

$$
W(R^{\mathrm{sh}})=X_K(K^{\mathrm{sh}}). \tag{3.6}
$$

In particular every smooth proper $K$-scheme has a weak Néron model.

**Proof strategy.** Dilatations preserve the generic fiber and every section lifts uniquely by (3.2). The integer defect decreases along an offending section. The essential finiteness point is to make this decrease uniform over all sections.

For a point $x$ of the special fiber, the elementary divisors of the relative Jacobian matrix are upper semicontinuous on the constructible set of sections centered at $x$. Because $X_k$ is noetherian and quasi-compact, finitely many locally closed strata control all possible defect vectors. Choose as center the reduced closure of the strata on which the lexicographically largest vector occurs. After dilatation, (3.5) strictly lowers that vector for every section centered in the chosen stratum; sections elsewhere do not acquire a larger vector because the modification is an isomorphism away from the center.

The defect vectors belong to a finite product of nonnegative integers ordered lexicographically. At each stage the maximum decreases. No infinite decreasing sequence exists, so after finitely many stages every lifted section has defect zero. Its center lies in the smooth locus. Conversely an $R^{\mathrm{sh}}$-section of the smooth locus gives a generic point, and uniqueness of all lifts follows from separatedness. This proves (3.6). $\square$

Excellence enters by making the non-smooth locus closed under the completion and approximation steps implicit in the Jacobian stratification. Properness is used only to ensure that generic points have centers. Consequently the theorem applies more broadly whenever boundedness supplies centers on a chosen model.

### 3.4 What smoothening does not yet provide

A weak Néron model is not usually a group. Start with a projective closure of an abelian variety and smoothen it. Addition is a rational map on the resulting model, but it need not extend between the chosen charts. Nor does (3.1) alone control maps from a smooth surface or a family with positive-dimensional special fiber.

This gap is genuine. The smooth locus of a proper regular model of a genus-one curve without a chosen origin is a torsor-like object, not canonically a group. Even when an origin exists, different smooth charts may be required to contain the reductions of $x$, $y$, and $x+y$.

The cure is not another arbitrary blowup. It is to regard every generic map into $A$ as an element of one sheaf and use translations to build compatible charts representing that sheaf. Smoothening supplies a bounded atlas; the group law supplies the transition maps. Chapter 4 carries out this passage.

## 4. Existence of Néron models

### 4.1 The extension sheaf

Let $j:\operatorname{Spec}K\to S$ be the generic inclusion and let $A/K$ be an abelian variety. On the category of smooth $S$-schemes define

$$
\mathscr N_A(T)=\operatorname{Hom}_K(T_K,A). \tag{4.1}
$$

Because morphisms into a separated scheme descend étale-locally, $mathscr N_A$ is a sheaf for the étale topology. Pointwise addition of maps makes it a sheaf of abelian groups. A Néron model is exactly a smooth separated finite-type $S$-scheme representing this sheaf.

This formulation prevents a circular construction of the group law. We first represent the sheaf. Its addition, inverse, and identity then become morphisms by representability. The generic group identities automatically extend because two morphisms representing the same transformation are equal.

A weak Néron model $W$ gives a morphism of sheaves

$$
h_W\longrightarrow\mathscr N_A, \tag{4.2}
$$

where $h_W(T)=\operatorname{Hom}_S(T,W)$. It is not generally surjective, but it is an étale-local atlas near every special geometric point: after strict henselization, a generic point extends to $W$ by (3.1), and smoothness spreads that section over an étale neighborhood.

### 4.2 Representability from a weak model

We isolate the construction that turns the atlas into a scheme.

**Theorem 4.1 (group extension representability).** Let $G/K$ be a smooth separated group variety. Suppose:

1. $G$ has a weak Néron model $W$ of finite type;
2. finitely many translates of the generic open $W_K\subseteq G$ cover $G$;
3. the closures of the graphs of multiplication and inversion admit smoothenings compatible with the projections to those translates.

Then the sheaf $T\mapsto\operatorname{Hom}_K(T_K,G)$ on smooth $R$-schemes is represented by a smooth separated group scheme $\mathcal G$ locally of finite type. If the translate classes required in the special fiber form a finite set, $\mathcal G$ is of finite type.

**Proof.** Choose points $g_1,\ldots,g_r$ over a finite unramified extension so that $G=\bigcup_i(g_i+W_K)$ after that extension. Enlarge the extension to be Galois and include all conjugates. Descent turns the disjoint union of the translated weak charts into a smooth $R$-space $U$ with a generically surjective map to $G$.

For two charts $U_i,U_j$, consider the generic isomorphism induced by translation on the overlap of their generic images. Take the closure of its graph in $U_i\times_RU_j$, smoothen it, and retain the open on which both projections are étale. Over $R^{\mathrm{sh}}$ these projections identify exactly those sections having the same generic image: the weak extension property gives existence, and separatedness of $G$ gives uniqueness. Thus these overlap spaces define an étale equivalence relation

$$
R_U\rightrightarrows U. \tag{4.3}
$$

The relation is effective. Indeed, on affine étale neighborhoods of a special point, the two projections are open immersions after shrinking because they are generically isomorphisms and induce bijections on strict-henselian sections. The local quotients are therefore obtained by gluing open subschemes. The cocycle follows from equality of the corresponding generic translations and separatedness. Gluing all charts gives a smooth $R$-scheme $\mathcal G$.

The same graph construction for multiplication shows that the generic product maps on $U_i\times U_j$ are compatible with (4.3) and descend to $\mathcal G\times_R\mathcal G\to\mathcal G$. Inversion and the identity descend similarly. Associativity and the group identities hold generically; both sides are morphisms from a flat scheme to a separated scheme, so they hold everywhere.

By construction, every generic map from a smooth $T$ lands étale-locally in a chart and extends there. The overlap relation glues the local extensions, proving the mapping property. The diagonal of $\mathcal G$ is the descended closure of the generic diagonal and is closed, so $\mathcal G$ is separated. It is locally of finite type because the charts are. If only finitely many special translate classes occur, finitely many charts cover $\mathcal G$, making it finite type. $\square$

The third hypothesis is not an extra existence assumption in the applications: Theorem 3.2 supplies those smoothenings. It is stated to expose the two inputs. Smoothening provides charts; the generic group law tells us exactly how to glue them.

### 4.3 The existence theorem for abelian varieties

**Theorem 4.2 (existence).** Let $R$ be an excellent discrete valuation ring and $A/K$ an abelian variety. Then $A$ has a Néron model $\mathcal A/R$. It is a smooth separated group scheme of finite type. Its formation is unique up to unique isomorphism.

**Proof strategy.** Properness gives a weak model and a finite translate cover. The remaining point is finite type of the represented group.

Choose a projective flat $R$-model $X$ of $A$ and apply Theorem 3.2 to obtain a weak model $W$. Since $A$ is quasi-compact, finitely many translates of the nonempty open $W_K$ cover $A$. Smoothen the closures of the required multiplication, inverse, and overlap graphs. Theorem 4.1 produces a Néron lft-model $\mathcal A$.

We prove quasi-compactness. Choose a symmetric ample divisor $H$ on $A$. Every translate chart meets a fixed finite affine cover of $A$ cut out by sections of powers of $H$. For an $R^{\mathrm{sh}}$-section $a$, its reduction class relative to $W$ is measured by the orders with which the translated sections of $H$ vanish along the closure of $a$. Properness of $X$ bounds these orders on each affine chart, and the theorem of the square gives

$$
v_H(a+b)+v_H(a-b)=2v_H(a)+2v_H(b)+O(1), \tag{4.4}
$$

where the bounded term depends only on the chosen finite presentation. Hence every section class is represented by one of finitely many valuation vectors. Two sections with the same vector lie in a common translated weak chart after an unramified refinement. Thus only finitely many translate classes are needed in the special fiber.

The final clause of Theorem 4.1 makes $\mathcal A$ finite type. Uniqueness is Theorem 2.3. $\square$

The boundedness argument is where properness of the generic group is decisive. For a split torus, valuations of coordinates can be arbitrary integers; its Néron lft-model generally has infinitely many components. For an abelian variety, an ample divisor turns translation into a quadratic boundedness relation and rules out such an infinite escape.

### 4.4 Gluing over a Dedekind base

Let $S$ now be an excellent Dedekind scheme and $A/K$ an abelian variety. Spread $A$ and its group law to an abelian scheme over a nonempty open $U\subseteq S$. The complement is finite after shrinking $U$ inside any fixed quasi-compact base. At each $s\in S\setminus U$, Theorem 4.2 constructs a Néron model over $S_s$.

**Theorem 4.3 (global existence).** The local Néron models over $S_s$ and the abelian scheme over $U$ glue uniquely to a smooth separated finite-type group scheme $\mathcal A/S$ satisfying the Néron mapping property.

**Proof.** Each local model restricts on the generic point to $A$. Over the overlap with $U$, both it and the abelian scheme are Néron models; Theorem 2.3 gives a unique isomorphism. Unique isomorphisms satisfy the cocycle condition, so the schemes and group laws glue.

For a smooth $S$-scheme $T$ and a generic map $T_K\to A$, the local mapping properties give extensions over $T_U$ and every $T\times_SS_s$. They agree generically, hence agree on overlaps by separatedness. The extensions glue to $T\to\mathcal A$. Uniqueness is again generic density. Finite type is local on $S$ and follows from the local construction. $\square$

Thus the existence problem is genuinely local at the closed points, while the answer is globally canonical.

## 5. Group structure and functoriality

### 5.1 Extending the group law

Although the construction already supplied a group law, the mapping property gives a shorter conceptual proof and will be reused for every generic operation.

Let $\mathcal A$ be the Néron model of $A$. The product $\mathcal A\times_S\mathcal A$ is smooth over $S$. Generic addition

$$
m_K:A\times_KA\longrightarrow A
$$

therefore extends uniquely to $m:\mathcal A\times_S\mathcal A\to\mathcal A$. Generic inversion extends from the smooth test scheme $\mathcal A$, and the generic identity gives a section $e:S\to\mathcal A$. The two associativity morphisms from $\mathcal A^3$ agree generically and hence globally. The unit, inverse, and commutativity identities extend in the same way.

This argument proves more than existence: there is only one group structure on a Néron model compatible with the generic group. It also shows why generic identities survive without separate special-fiber calculations.

### 5.2 Homomorphisms, products, and endomorphisms

**Theorem 5.1 (functoriality).** Let $A$ and $B$ be abelian varieties over $K$ with Néron models $\mathcal A$ and $\mathcal B$. Every $K$-homomorphism $f:A\to B$ extends uniquely to an $S$-homomorphism

$$
\mathcal f:\mathcal A\longrightarrow\mathcal B. \tag{5.1}
$$

Composition, sums, zero maps, and multiplication maps are preserved.

**Proof.** The source $\mathcal A$ is smooth, so the mapping property of $\mathcal B$ extends $f$. The two morphisms

$$
\mathcal f\circ m_{\mathcal A},
\qquad
m_{\mathcal B}\circ(\mathcal f\times\mathcal f)
$$

agree generically and therefore agree globally. Thus $\mathcal f$ is a homomorphism. Every compatibility follows by applying uniqueness to the corresponding generic equality. $\square$

**Proposition 5.2.** The Néron model of $A\times_KB$ is $\mathcal A\times_S\mathcal B$.

**Proof.** Products preserve smoothness, separatedness, and finite type. For smooth $T/S$,

$$
\operatorname{Hom}_S(T,\mathcal A\times\mathcal B)
=\operatorname{Hom}_S(T,\mathcal A)\times\operatorname{Hom}_S(T,\mathcal B),
$$

which the two mapping properties identify with maps to $A\times B$. $\square$

Consequently

$$
\operatorname{End}_K(A)\xrightarrow{\sim}
\operatorname{End}_S(\mathcal A). \tag{5.2}
$$

This is an equality of rings. It is stronger than the normal-base extension theorem of Book 38 because $\mathcal A$ need not be proper.

### 5.3 Isogenies and their limitations

If $f:A\to B$ is an isogeny, its extension $\mathcal f:\mathcal A\to\mathcal B$ need not be an isogeny of $S$-group schemes. It can fail to be finite, flat, or surjective on special components. This is one of the most important boundary statements in the subject.

The generic quasi-inverse relation remains valid. Choose $f':B\to A$ and an integer $n>0$ such that

$$
f'f=[n]_A,
\qquad ff'=[n]_B.
$$

Then uniqueness gives

$$
\mathcal f'\mathcal f=[n]_{\mathcal A},
\qquad
\mathcal f\mathcal f'=[n]_{\mathcal B}. \tag{5.3}
$$

These identities control kernel and cokernel after inverting primes dividing $n$, but they do not make $\ker\mathcal f$ finite flat. For example, two isogenous elliptic curves can have different component groups, so a finite flat quotient description of the whole Néron models would force false component counts.

**Proposition 5.3.** If $n$ is invertible on $S$, multiplication $[n]$ is étale on $\mathcal A$. Its kernel $\mathcal A[n]$ is quasi-finite, separated, and étale, but it need not be finite unless $A[n]$ has no points escaping through the boundary of $\mathcal A$.

**Proof.** The differential of $[n]$ on the smooth group scheme is multiplication by the unit $n$, hence an isomorphism. Thus $[n]$ and its identity fiber are étale. Quasi-finiteness follows from zero-dimensional generic and special fibers of the kernel. Finiteness can fail because $\mathcal A$ is not proper. $\square$

In the good-reduction case $\mathcal A$ is proper, and Book 38 recovers a finite locally free kernel of rank $n^{2g}$. Bad reduction requires separate attention to the identity component and components.

### 5.4 Dual abelian varieties and polarizations

The dual $A^\vee$ has its own Néron model $\mathcal A^\vee_{\mathrm N}$. This notation is intentionally different from a relative dual of $\mathcal A$: a nonproper smooth group scheme does not generally possess a dual abelian scheme.

A polarization $\lambda:A\to A^\vee$ extends uniquely to

$$
\lambda_{\mathcal A}:\mathcal A\longrightarrow\mathcal A^\vee_{\mathrm N}. \tag{5.4}
$$

If $lambda$ is principal, the generic inverse extends as well, and the two composites are identities. Hence:

**Proposition 5.4.** A principal polarization induces an isomorphism between the Néron models of $A$ and $A^\vee$.

The statement is about Néron models, not about extending a theta divisor or a relatively ample line bundle. At bad reduction the Néron model is not proper, so there is no relative polarization in the abelian-scheme sense. What extends canonically is the homomorphism. This distinction becomes essential when component pairings are introduced in Chapter 12.

## 6. Identity components and component groups

### 6.1 The open identity subgroup

The special fiber of a smooth finite-type group scheme can be disconnected even though the generic fiber is connected. To separate continuous degeneration from discrete jumps, we isolate the components containing the identity.

**Proposition 6.1.** Let $\mathcal G/S$ be a smooth group scheme of finite type over a Dedekind scheme, with connected generic fiber. There is a unique open subgroup scheme $\mathcal G^0\subseteq\mathcal G$ such that

$$
(\mathcal G^0)_s=(\mathcal G_s)^0
$$

for every geometric point $s$ of $S$. It contains the entire generic fiber.

**Proof.** For a smooth morphism of finite presentation, the union of the fiberwise connected components meeting a given section is open. Apply this to the identity section. Translation shows that this open is stable under multiplication and inversion: the product of two connected subsets containing the identity is connected and contains the identity, and inversion preserves it. The generic fiber is connected, so it is entirely included. Uniqueness is forced fiberwise. $\square$

For a Néron model $\mathcal A$, the subgroup $\mathcal A^0$ is smooth, separated, and of finite type, but usually not proper. It is often called the **connected Néron model**.

### 6.2 The finite étale component group

Let $R$ be local with residue field $k$. Define the fppf quotient on the special fiber by

$$
\Phi_A=\mathcal A_k/\mathcal A_k^0. \tag{6.1}
$$

**Theorem 6.2.** The quotient $\Phi_A$ is represented by a finite étale commutative $k$-group scheme. After a separable closure,

$$
\Phi_A(k^s)=\pi_0(\mathcal A_{k^s})
$$

is the finite abstract group of geometric connected components.

**Proof.** A smooth algebraic group over a field has finitely many connected components because it is of finite type. Its identity component is geometrically connected, open, closed, and normal. Translation makes every other component a torsor under it. The quotient sheaf is therefore represented by a finite reduced zero-dimensional group scheme after $k^s$-base change, hence by a finite étale group scheme over $k$. Galois descent identifies its geometric points with the components and their natural action. $\square$

Finiteness here depends on finite type of the Néron model. A Néron lft-model can have an infinite component group, locally constant but not finite.

### 6.3 Reduction and the component map

Assume $R$ is henselian. By the mapping property,

$$
A(K)=\mathcal A(R). \tag{6.2}
$$

Reduction followed by the quotient gives the **component map**

$$
c_A:A(K)\longrightarrow\Phi_A(k). \tag{6.3}
$$

Its kernel consists exactly of sections whose special point lies in $\mathcal A_k^0$:

$$
A^0(K):=\mathcal A^0(R)=\ker c_A. \tag{6.4}
$$

The equality uses Hensel's lemma. If an $R$-section reduces to $\mathcal A_k^0$, it factors through the open $\mathcal A^0$. Conversely this is immediate.

One must not automatically place a zero at the right of

$$
0\longrightarrow A^0(K)\longrightarrow A(K)
\xrightarrow{c_A}\Phi_A(k). \tag{6.5}
$$

A $k$-rational point of the quotient labels a component defined over $k$, but that component is a torsor under $\mathcal A_k^0$ and can lack a $k$-point. If $k$ is finite, Lang's theorem makes every such torsor trivial; if $k$ is separably closed, the assertion is obvious. In either case $c_A$ is surjective and

$$
A(K)/A^0(K)\simeq\Phi_A(k). \tag{6.6}
$$

Over a general residue field, the cokernel injects into the pointed set $H^1(k,\mathcal A_k^0)$ by the torsor boundary.

Functoriality is immediate. A homomorphism $f:A\to B$ maps identity components into identity components because the image of a connected group containing the identity is connected. It therefore induces

$$
\Phi_f:\Phi_A\longrightarrow\Phi_B,
\qquad
c_B\circ f=\Phi_f\circ c_A. \tag{6.7}
$$

### 6.4 The structure of the connected special fiber

Over a perfect field $k$, the connected smooth algebraic group $\mathcal A_k^0$ has a canonical structural filtration. Chevalley's theorem gives

$$
0\longrightarrow L
\longrightarrow\mathcal A_k^0
\longrightarrow B\longrightarrow0, \tag{6.8}
$$

where $B$ is an abelian variety and $L$ is a connected smooth affine group. Since $\mathcal A_k^0$ is commutative, the maximal smooth connected unipotent subgroup $U\subseteq L$ has torus quotient:

$$
0\longrightarrow U\longrightarrow L\longrightarrow T\longrightarrow0. \tag{6.9}
$$

**Proof of the filtration.** Choose a normal projective compactification of the connected group. The stabilizer of the boundary is affine; quotienting by the maximal connected affine normal subgroup produces a complete connected group, hence an abelian variety. This proves (6.8). For a connected commutative affine group over a perfect field, the unipotent radical is smooth and the reductive quotient is a torus, proving (6.9). Uniqueness follows from maximality in both steps. $\square$

Write

$$
a(A)=\dim B,\qquad t(A)=\dim T,\qquad u(A)=\dim U.
$$

Smoothness keeps total dimension constant, so

$$
\dim A=a(A)+t(A)+u(A). \tag{6.10}
$$

These integers separate three kinds of reduction. The abelian part retains proper geometry, the torus records multiplicative degeneration, and the unipotent part records genuinely additive degeneration. Over an imperfect residue field one must use the maximal smooth connected affine subgroup and allow the unipotent quotient to become split only after a purely inseparable extension; none of the later graph formulas will assume such a splitting.

## 7. Reduction types and basic calculations

### 7.1 Good, semistable, and additive reduction

The filtration of Section 6.4 gives intrinsic terminology.

An abelian variety has **semistable reduction** if $U=0$, so the connected special fiber is semiabelian:

$$
0\longrightarrow T\longrightarrow\mathcal A_k^0
\longrightarrow B\longrightarrow0. \tag{7.1}
$$

It has **purely toric reduction** if $B=0$ as well. It has **additive reduction** when $U\ne0$. Good reduction means that the whole Néron model is an abelian scheme, not merely that $U=T=0$ in one informally chosen model.

**Proposition 7.1.** The following are equivalent:

1. $A$ has good reduction;
2. its Néron model is proper;
3. $\mathcal A_k^0$ is an abelian variety and $\Phi_A=0$.

**Proof.** The equivalence of 1 and 2 is Corollary 2.6. Good reduction plainly implies 3. Conversely, under 3 the special fiber is connected and proper. Properness of a smooth finite-type morphism can be checked by the valuative criterion. A generic point of $\mathcal A$ approaching the special fiber has a limit in the proper identity fiber; translation by a section through that limit covers every valuation. Thus no boundary point is missing, and $\mathcal A/R$ is proper. $\square$

The condition $\Phi_A=0$ alone is much weaker: a semiabelian connected special fiber can still contain a torus. Likewise $U=T=0$ without control of components is not by itself the formulation one should use.

### 7.2 Elliptic curves

Let $E/K$ be an elliptic curve. Its minimal regular proper model exists by the regular-model and contraction results of Book 10, and the Néron description is especially concrete.

**Theorem 7.2.** Let $\mathcal C/R$ be the minimal regular proper model of $E$, with the origin extended to a section. Its smooth locus $\mathcal C_{\mathrm{sm}}$ is the Néron model $\mathcal E$ of $E$.

**Proof.** Let $\mathcal U=\mathcal C_{\mathrm{sm}}$. Resolve the closure of the graph of generic addition in $\mathcal C\times_R\mathcal C\times_R\mathcal C$. Above $\mathcal U\times_R\mathcal U$, either projection from the resolution can have only vertical exceptional curves. If such a curve were contracted by one projection and not the other, its image would be a vertical exceptional curve of the first kind in $\mathcal C$, contradicting minimality. The two projections therefore identify the graph with a morphism $\mathcal U\times_R\mathcal U\to\mathcal U$. The same argument extends inversion; the group identities follow from generic density.

Now let $T/R$ be smooth and $T_K\to E$ a generic map. Properness of $\mathcal C$ extends it at every height-one point of $T$. Resolve the remaining graph indeterminacy. Any exceptional divisor maps vertically into $\mathcal C$. If it met a nonsmooth point of a fiber, translating the map by a local section through a nearby smooth point would produce a vertical exceptional curve in the relatively minimal model, by the same contraction argument. Hence the rational map lands in $\mathcal U$ and has no indeterminacy. It extends uniquely to $T\to\mathcal U$ because $\mathcal U$ is separated and $T_K$ is dense. Thus $\mathcal U$ has the Néron mapping property. $\square$

The three familiar cases now have a uniform form over an algebraic closure of $k$:

| reduction | $\mathcal E_k^0$ | geometric component group |
|---|---|---|
| good | elliptic curve | $0$ |
| multiplicative | $\mathbf G_m$ | cyclic, determined by the polygon |
| additive | $\mathbf G_a$ | finite, determined by the fiber configuration |

For split multiplicative reduction with an $n$-gon, $\Phi_E(k^s)=\mathbf Z/n\mathbf Z$. For nonsplit multiplicative reduction, the same geometric cyclic group carries the sign action arising from reversal of the polygon; the torus is the corresponding nonsplit one-dimensional torus. The rational component group is the invariant subgroup, not automatically all of $\mathbf Z/n\mathbf Z$.

### 7.3 Products and unramified twists

Products give immediate checks on every invariant. From Proposition 5.2,

$$
(\mathcal A\times\mathcal B)^0
=\mathcal A^0\times\mathcal B^0,
\qquad
\Phi_{A\times B}\simeq\Phi_A\times\Phi_B. \tag{7.2}
$$

The abelian, toric, and unipotent ranks add. Thus component groups need not be cyclic even in elementary examples: the product of two multiplicative elliptic curves with polygon lengths $m$ and $n$ has geometric component group

$$
\mathbf Z/m\mathbf Z\oplus\mathbf Z/n\mathbf Z.
$$

An unramified twist changes descent without changing geometric reduction. Suppose $A$ becomes isomorphic to $B$ over a finite unramified extension and the descent cocycle acts on $\Phi_B(k^s)$. Then $\Phi_A(k^s)$ is the same abstract group with the twisted Galois action. Its invariant subgroup can shrink even though its order and geometric fiber configuration are unchanged.

This is the cleanest warning against recording only a Kodaira symbol, graph, or group order over the ground field. Arithmetic specialization uses the finite étale group scheme, including its descent action.

### 7.4 What the component group can and cannot detect

The component group measures the failure of the special fiber to be connected. It does not measure the failure of the connected component to be proper. Hence

$$
\Phi_A=0\not\Longrightarrow\text{good reduction}. \tag{7.3}
$$

A one-loop semistable Jacobian with edge length one has trivial component group and toric rank one.

Nor is $\Phi_A$ an isogeny invariant. An isogeny induces a map of component groups, but its kernel and cokernel can be nontrivial at primes dividing the isogeny degree. The quasi-inverse identities (5.3) imply only that both are killed by a suitable integer. We will make this precise in Section 12.2.

Finally, $\Phi_A$ does not contain the full specialization of a point. The reduction of $P\in A(K)$ first lands in $\mathcal A_k(k)$; its image in $\Phi_A(k)$ remembers only the connected component. Inside the identity component there remain abelian, toric, and possibly unipotent coordinates. For Jacobians, these correspond respectively to divisor classes on normalized components, gluing parameters around graph cycles, and singular or nonreduced contributions.

## 8. Change of the valuation ring

### 8.1 The canonical base-change morphism

Let $R'/R$ be a finite extension of discrete valuation rings, with fraction fields $K'/K$. If $\mathcal A$ and $\mathcal A'$ are the Néron models of $A$ and $A_{K'}$, respectively, then $\mathcal A_{R'}$ is a smooth test scheme for $\mathcal A'$. The generic identity extends uniquely to

$$
h_{R'/R}:\mathcal A\times_RR'\longrightarrow\mathcal A'. \tag{8.1}
$$

Uniqueness gives transitivity in towers. The arrow has no automatic inverse: the mapping property is stable under étale change but not under ramification. On special fibers, (8.1) induces

$$
\Phi_A\times_kk'\longrightarrow\Phi_{A_{K'}}. \tag{8.2}
$$

Neither injectivity nor surjectivity is automatic when the extension is ramified.

### 8.2 Unramified base change

**Theorem 8.1.** If $R'/R$ is finite étale, then (8.1) is an isomorphism and

$$
\Phi_{A_{K'}}\simeq\Phi_A\times_kk'. \tag{8.3}
$$

**Proof.** If $T/R'$ is smooth, it is smooth over $R$. An $R'$-map $T\to\mathcal A_{R'}$ is an $R$-map $T\to\mathcal A$ whose generic restriction is $K'$-linear. Hence the Néron property of $\mathcal A$ gives

$$
\operatorname{Hom}_{R'}(T,\mathcal A_{R'})
\simeq\operatorname{Hom}_{K'}(T_{K'},A_{K'}).
$$

Thus $\mathcal A_{R'}$ is a Néron model, so uniqueness identifies it with $\mathcal A'$. Components commute with field extension, proving (8.3). $\square$

Passing to a strict henselization therefore reveals the geometric components without changing them. In particular $\Phi_A(k^s)$ is calculated on the strict-henselian model and retains its descent action over $k$.

### 8.3 Ramified base change

Ramification changes relative smoothness. The regular equation $xy=\pi$ becomes $xy=u(\pi')^e$. For $e>1$ the new total space is singular, and its resolution inserts a chain.

For a semistable Jacobian let $X=H_1(\Gamma,\mathbf Z)$ and let $q:X\hookrightarrow X^\vee$ be the edge-length map. If the geometric graph does not split further, ramification of index $e$ replaces $q$ by $eq$. Thus

$$
\Phi_{A_{K'}}(k^s)=X^\vee/eqX,\qquad
\Phi_A(k^s)=X^\vee/qX, \tag{8.4}
$$

and the nested lattices give

$$
0\longrightarrow X/eX\xrightarrow{q}\Phi_{A_{K'}}(k^s)
\longrightarrow\Phi_A(k^s)\longrightarrow0. \tag{8.5}
$$

Consequently $|\Phi_{A_{K'}}|=e^{\operatorname{rank}X}|\Phi_A|$. Outside the semistable setting, ramification may also alter a unipotent part; the old component group alone cannot determine the result.

### 8.4 Descent and Galois action

For a finite unramified Galois extension, Theorem 8.1 transports the descent datum to every special-fiber layer. In particular

$$
\Phi_A(k)=\Phi_A(k^s)^{G_k}. \tag{8.6}
$$

The torus descends through its character lattice, where branch reversal can act by $-1$. Smoothness, separatedness, finite type, and the mapping property all descend because extensions are unique. For ramified descent one must instead compare with (8.1); the base-changed model need not already be Néron.

## 9. The Picard route to the Néron model

### 9.1 Regular curve models and relative line bundles

Let $C/K$ be a smooth proper geometrically connected curve, $J=\operatorname{Pic}^0_{C/K}$, and $\mathcal X/R$ a regular proper flat model. Write $P=\operatorname{Pic}_{\mathcal X/R}$ and let $P^{[0]}$ denote the part whose generic restriction has degree zero.

A vertical divisor is empty generically, so its line bundle represents the generic identity while possibly changing special multidegree. Call $\mathcal X$ **Picard-admissible** when the needed part of $P^{[0]}$ is represented by a smooth group scheme locally of finite type and commutes with strict henselization. Regular semistable models satisfy this. Cohomological flatness in degree zero also suffices; if it fails, one first smoothens the Picard sheaf. The final separated quotient is unaffected.

### 9.2 The closure of the generic identity

Let $E\subseteq P^{[0]}$ be the schematic closure of the generic identity. Over a strict henselization, it is represented by vertical line bundles

$$
\mathcal O_{\mathcal X}\left(\sum_i a_i\Gamma_i\right), \tag{9.1}
$$

modulo multiples of the whole fiber.

**Lemma 9.1.** Two line bundles on $\mathcal X$ with isomorphic generic restrictions differ, after a base pullback, by a vertical Cartier divisor.

**Proof.** A generic isomorphism is a rational section of their ratio. Its divisor has no horizontal part and is therefore supported on the special fiber. Scaling by $K^\times$ changes it by a multiple of the principal whole fiber. $\square$

**Lemma 9.2.** The fppf quotient

$$
Q=P^{[0]}/E \tag{9.2}
$$

is separated.

**Proof.** Two valuation-ring sections agreeing generically differ, after local lifting to $P^{[0]}$, by a generically trivial line bundle. Lemma 9.1 puts that difference in $E$. The valuative criterion therefore makes the diagonal closed. $\square$

Schematic closure matters: visible vertical points can form a nonsaturated subgroup and give the wrong finite quotient.

### 9.3 The Raynaud quotient theorem

**Theorem 9.3.** For a Picard-admissible regular proper model, $Q$ is the Néron model $\mathcal J$ of $J$. Its identity component is the image of the multidegree-zero Picard subgroup.

**Proof strategy.** Extension comes from closing divisors on the regular surface; uniqueness is exactly division by $E$.

The Picard deformation obstruction lies in $H^2$ of a curve and vanishes, so $Q$ is smooth and locally of finite type. Chapter 10 proves that only finitely many components remain. Its generic fiber is $J$.

Let $T/R$ be smooth and $T_K\to J$ a map. Étale-locally it is represented by a divisor on $C\times_KT_K$. Move its support away from singular points and close it in $\mathcal X\times_RT$. Regularity makes the resulting codimension-one class invertible after an étale refinement, and $H^2=0$ lifts it through infinitesimal neighborhoods. The local Picard extensions differ on overlaps by generically trivial bundles, hence by $E$ through Lemma 9.1. They glue uniquely to $T\to Q$. This proves the Néron property. Multidegree zero is the connected generalized Jacobian, proving the final assertion. $\square$

This proves, rather than assumes, the separated-Picard identification used for semistable Jacobians in Books 12 and 36.

### 9.4 Independence of the regular model

If $\mathcal X'\to\mathcal X$ blows up a special point, pullback introduces only the exceptional vertical class beyond the old Picard classes. It belongs to the closure of the generic identity, so

$$
P^{[0]}_{\mathcal X/R}/E_{\mathcal X}
\simeq P^{[0]}_{\mathcal X'/R}/E_{\mathcal X'}. \tag{9.3}
$$

Any two regular models have a common regular domination by Book 10. Thus the quotient is model-independent, as uniqueness of the Néron model also requires.

## 10. Intersection theory and components of Jacobians

### 10.1 The weighted intersection complex

Over a strict henselization write

$$
\mathcal X_k=\sum_{i\in I}m_i\Gamma_i. \tag{10.1}
$$

Define

$$
M(a)_i=\sum_ja_j(\Gamma_j\cdot\Gamma_i),\qquad
\Lambda=\{d\in\mathbf Z^I:\sum_im_id_i=0\}. \tag{10.2}
$$

The whole fiber is principal, so $M(\mathbf Z^I)\subseteq\Lambda$.

**Lemma 10.1.** The intersection form is negative semidefinite with rational kernel spanned by $(m_i)$. Hence $M(\mathbf Z^I)$ has finite index in $\Lambda$.

**Proof.** The negativity theorem for a connected fiber from Book 11 says that the vertical intersection matrix is negative semidefinite and that its rational radical is exactly the line generated by the whole-fiber multiplicity vector. Hence its rank is $|I|-1$. The lattice $\Lambda$ also has rank $|I|-1$, so the inclusion $M(\mathbf Z^I)\subseteq\Lambda$ has finite index. $\square$

### 10.2 The component-group formula

**Theorem 10.2.** There is a canonical Galois-equivariant isomorphism

$$
\Phi_J(k^s)\simeq\Lambda/M(\mathbf Z^I). \tag{10.3}
$$

**Proof.** A generic-degree-zero line bundle has multidegree $d$ with $\sum m_id_i=0$. Horizontal divisors through smooth component points realize all of $\Lambda$ after an étale extension. Twisting by $\sum a_j\Gamma_j$ changes multidegree by $M(a)$. The Raynaud quotient identifies exactly these twists, while each fixed multidegree is a translate of the connected generalized Jacobian. Lemma 10.1 gives finiteness and descent gives equivariance. $\square$

Equivalently, $\Phi_J(k^s)$ is the torsion in the cokernel of the intersection matrix. Smith normal form, rather than the determinant alone, gives its invariant factors.

### 10.3 Specialization of divisor classes

For a degree-zero divisor $D$ whose closure meets the fiber smoothly, put

$$
\rho(D)=((\overline D\cdot\Gamma_i))_i\in\Lambda. \tag{10.4}
$$

If $D=\operatorname{div}(f)$, then $\operatorname{div}_{\mathcal X}(f)=\overline D+\sum a_i\Gamma_i$, so $\rho(D)=-M(a)$. Therefore

$$
J(K^{\mathrm{sh}})\longrightarrow\Lambda/M(\mathbf Z^I) \tag{10.5}
$$

is the component map. If $P,Q$ specialize on $\Gamma_i,\Gamma_j$, then $c_J([P-Q])=[e_i-e_j]$. A nonrational closed point contributes its full Galois-orbit sum.

Solving $M(a)=-\rho(D)$ over $\mathbf Q$ gives a vertical correction orthogonal to every component. It is integral exactly when the component class vanishes.

### 10.4 Nonreduced fibers and the index

The weights $m_i$ cannot be omitted. Every horizontal divisor satisfies

$$
\deg(D_K)=\sum_im_i(D\cdot\Gamma_i). \tag{10.6}
$$

Thus $\delta=\gcd_i(m_i)$ divides every rational divisor degree. If $C(K)\ne\varnothing$, a section forces $\delta=1$; over a henselian ring with algebraically closed residue field, moving horizontal divisors proves that $\delta$ equals the index. When $\delta>1$, the unsmoothed Picard object can fail cohomological flatness, but the smoothened quotient and formula (10.3) remain valid.

## 11. Semistable Jacobians

### 11.1 The connected special fiber

Assume $\mathcal X/R$ is regular semistable. Let $Y_v$ be the normalized geometric components and $\Gamma$ the dual graph. Gluing line bundles across nodes gives

$$
0\longrightarrow T_\Gamma\longrightarrow\mathcal J_k^0
\longrightarrow\prod_vJ(Y_v)\longrightarrow0,\qquad
X^*(T_\Gamma)=H_1(\Gamma,\mathbf Z). \tag{11.1}
$$

Thus the Jacobian has semistable reduction, toric rank $b_1(\Gamma)$, and abelian rank $\sum_vg(Y_v)$. These add to $g(C)$.

### 11.2 The graph formula

Choose orientations and let $\Delta$ be the graph Laplacian. The negative intersection matrix is $\Delta$, so

$$
\Phi_J(k^s)\simeq\operatorname{Div}^0(\Gamma)/\Delta\mathbf Z^V. \tag{11.2}
$$

The unit edge pairing restricts to $q:H_1(\Gamma,\mathbf Z)\to H_1(\Gamma,\mathbf Z)^\vee$.

**Theorem 11.1.** There is a canonical exact sequence

$$
0\longrightarrow H_1(\Gamma,\mathbf Z)\xrightarrow{q}
H_1(\Gamma,\mathbf Z)^\vee\longrightarrow\Phi_J(k^s)\longrightarrow0. \tag{11.3}
$$

**Proof.** Rationally the edge space is the orthogonal sum of cycle and cut spaces. Integrally their sum can have finite index. Computing that index first after quotienting by cuts and then after applying the boundary identifies it both with $H_1^\vee/qH_1$ and with $\operatorname{Div}^0/\Delta\mathbf Z^V$. Use (11.2). $\square$

### 11.3 Weighted nodes and regular resolution

A node $xy=u\pi^{n_e}$ resolves to a chain of $n_e$ unit edges. A cycle has the same coefficient on every segment, so the pairing compresses to

$$
q_n(a,b)=\sum_en_ea_eb_e. \tag{11.4}
$$

The cycle lattice is unchanged, and

$$
0\to H_1(\Gamma,\mathbf Z)\xrightarrow{q_n}
H_1(\Gamma,\mathbf Z)^\vee\to\Phi_J(k^s)\to0. \tag{11.5}
$$

Thus weighted stable and resolved regular models give the same group.

### 11.4 Four exact examples

For a tree, $H_1=0$, so $T_\Gamma=\Phi_J=0$ and $\mathcal J_k^0=\prod_vJ(Y_v)$.

For one loop of length $n$,

$$
0\to\mathbf G_m\to\mathcal J_k^0\to J(Y)\to0,\qquad
\Phi_J(k^s)\simeq\mathbf Z/n\mathbf Z. \tag{11.6}
$$

For two vertices joined by $r$ unit edges, $\Phi_J\simeq\mathbf Z/r\mathbf Z$ and the toric rank is $r-1$.

For one vertex with loops of lengths $a,b$,

$$
\Phi_J(k^s)\simeq\mathbf Z/a\mathbf Z\oplus\mathbf Z/b\mathbf Z. \tag{11.7}
$$

Galois reversal of a loop acts by $-1$ on its summand and torus character.

## 12. Morphisms, specialization, and pairings

### 12.1 Maps induced by curves

Let $f:C\to D$ be finite between smooth proper curves. Pullback and norm give

$$
f^*:J_D\longrightarrow J_C,\qquad
f_*:J_C\longrightarrow J_D,\qquad
f_*f^*=[\deg f]. \tag{12.1}
$$

The Néron property extends these maps and their identity uniquely. No extension of $f$ between chosen regular models is needed for existence.

To calculate the special maps, choose regular models dominated by a resolution of the closure of the graph of $f$. Pullback and norm preserve generically trivial vertical classes and descend through the Raynaud quotients. On normalized components they are ordinary pullback and norm. On graph cycles they are harmonic pullback and pushforward, weighted by branch degrees. Thus the Néron homomorphism always exists, but an action read from a special-fiber graph is valid only after the curve map has been extended in this controlled way.

### 12.2 Maps on component groups

Every homomorphism $u:A\to B$ induces $\Phi_u:\Phi_A\to\Phi_B$. Suppose $v:B\to A$ satisfies

$$
vu=[n]_A,\qquad uv=[n]_B. \tag{12.2}
$$

The same equations hold on components.

**Proposition 12.1.** The kernel and cokernel of $\Phi_u$ are killed by $n$. For every prime $\ell\nmid n$, $\Phi_u$ is an isomorphism on the $\ell$-primary parts.

**Proof.** If $\Phi_u(x)=0$, then $nx=\Phi_v\Phi_u(x)=0$. In the cokernel, $ny=\Phi_u\Phi_v(y)$ vanishes. After localization away from $n$, $n^{-1}\Phi_v$ is an inverse. $\square$

Applied to an isogeny, this proves exactly the safe isogeny invariance: only primes dividing a quasi-inverse integer can change components. It does not assert that the map of Néron models is finite flat.

### 12.3 The component pairing for Jacobians

Let $X=H_1(\Gamma,\mathbf Z)$ and let $q_n:X\hookrightarrow X^\vee$ be the weighted positive form. Its discriminant group $\Phi=X^\vee/q_nX$ has a canonical pairing

$$
\langle\ ,\ \rangle_\Phi:\Phi\times\Phi\longrightarrow\mathbf Q/\mathbf Z. \tag{12.3}
$$

For lifts $x,y\in X^\vee$, define

$$
\langle\bar x,\bar y\rangle_\Phi
=y(q_n^{-1}x)\bmod\mathbf Z. \tag{12.4}
$$

Changing either lift changes the value by an integer.

**Proposition 12.2.** This pairing is symmetric, nondegenerate, Galois invariant, and makes graph pullback adjoint to graph pushforward.

**Proof.** Symmetry follows from symmetry of $q_n$. If $\bar x$ pairs integrally with every $y$, then $q_n^{-1}x$ lies in the double dual $X$, so $x\in q_nX$. Thus the pairing is nondegenerate. Galois permutes or reverses edges and preserves every product $a_eb_e$. Finally the branch-degree calculation gives

$$
q_C(f^*a,b)=q_D(a,f_*b),
$$

which descends to the discriminant groups. $\square$

Under the principal polarization of a Jacobian, (12.3) is the component-level duality pairing. The analogous construction for arbitrary semistable abelian varieties requires the general monodromy pairing developed in the next book; no broader perfection claim is used here.

### 12.4 Prime-to-residue-characteristic torsion

Let $R$ be henselian of residue characteristic $p$, and let $(n,p)=1$. Multiplication by $n$ has invertible differential on the smooth group $\mathcal A$. It is therefore an automorphism on every successive infinitesimal neighborhood of the identity.

**Proposition 12.3.** Reduction is injective on unramified $n$-torsion:

$$
A(K^{\mathrm{sh}})[n]\hookrightarrow\mathcal A_k(k^s)[n]. \tag{12.5}
$$

**Proof.** A torsion section reducing to the identity lies in the formal group, where multiplication by $n$ is an automorphism; it must be zero. Translating the difference of two sections reduces general injectivity to this case. $\square$

The component of such a point belongs to $\Phi_A(k^s)[n]$. Statement (12.5) concerns $K^{\mathrm{sh}}$-rational torsion, equivalently inertia invariants. It does not assert that all prime-to-$p$ torsion is unramified.

## 13. Global Néron models

### 13.1 Localization at the bad places

Let $S$ be an excellent Dedekind scheme and $\mathcal A/S$ the Néron model of $A/K$. There is a maximal open $U$ on which $\mathcal A$ is an abelian scheme. If $S$ is quasi-compact, $S\setminus U$ is finite.

For every closed $s$,

$$
\mathcal A\times_SS_s
\simeq\text{the Néron model over }\mathcal O_{S,s}. \tag{13.1}
$$

This follows from restriction and uniqueness. Reduction type, identity component, and component group are therefore local calculations. Good places contribute no component group.

### 13.2 Sections and arithmetic component maps

The global mapping property gives

$$
\mathcal A(S)=A(K). \tag{13.2}
$$

Every rational point specializes canonically at every closed place. Collecting the local component maps produces

$$
c:A(K)\longrightarrow
\bigoplus_{s\in S\setminus U}\Phi_{A,s}(k(s)). \tag{13.3}
$$

Its kernel consists of sections meeting the identity component everywhere. For a Jacobian, the $s$-entry is found by closing a degree-zero divisor in a regular $S_s$-model and reducing its intersection vector modulo the vertical intersection matrix. A principal divisor maps to zero because its horizontal closure and vertical correction form one principal divisor on the surface.

### 13.3 Exact global bookkeeping

There is an exact sequence

$$
0\longrightarrow\mathcal A^0(S)\longrightarrow A(K)
\xrightarrow{c}\bigoplus_s\Phi_{A,s}(k(s)). \tag{13.4}
$$

No terminal zero is implied. Even when every local component is rational, a global point need not realize an arbitrary tuple of local components. Such a conclusion requires a separate approximation or descent theorem.

Nor is $\prod_s|\Phi_{A,s}|$ by itself a class number, regulator, or Selmer order. Global formulas also involve measures, invariant differentials, and cohomology. The Néron theory supplies the exact local finite groups and canonical maps into them.

### 13.4 The reusable comparison package

The conclusions needed later can now be stated in one place.

**Theorem 13.1.** Let $S$ be an excellent Dedekind scheme with function field $K$.

1. Every abelian variety $A/K$ has a unique smooth separated finite-type Néron model $\mathcal A/S$.
2. Homomorphisms, products, and principal polarizations extend uniquely.
3. At a closed point $s$, $\mathcal A_s^0$ is smooth and connected and $\Phi_{A,s}$ is finite étale.
4. Over a henselian local ring, $A(K)=\mathcal A(R)$ and the kernel of the component map is $\mathcal A^0(R)$; the map is onto when the residue field is finite or separably closed.
5. For a Jacobian and a Picard-admissible regular model, $\mathcal J=P^{[0]}/E$.
6. If $\mathcal X_{k^s}=\sum m_i\Gamma_i$, then

   $$
   \Phi_J(k^s)\simeq
   \{d\in\mathbf Z^I:\sum m_id_i=0\}
   \big/
   \{(\sum_ja_j(\Gamma_j\cdot\Gamma_i))_i:a_j\in\mathbf Z\}.
   $$

7. In the semistable case, $\mathcal J_s^0$ is an extension of normalized-component Jacobians by the graph torus, and $\Phi_J$ is the discriminant group of the weighted cycle pairing.

**Proof.** Items 1--4 are Theorems 4.2--4.3, 5.1, 6.2, and Section 6.3. Item 5 is Theorem 9.3, item 6 is Theorem 10.2, and item 7 is (11.1) and Theorem 11.1 with Section 11.3. $\square$

Every clause commutes with unramified base change. Ramified base change instead carries the canonical comparison (8.1), and in the semistable case scales the edge-length pairing.

## 14. Conclusion

### 14.1 The mathematical package

The Néron model solves an extension problem that neither an arbitrary proper model nor an arbitrary regular model can solve. It is smooth enough to receive maps from every smooth integral test family, separated enough to make extensions unique, and flexible enough to exist at bad reduction. Smoothening a projective model first captures every unramified point. Translation and graph gluing turn those charts into the representative of the full extension sheaf. Properness of the generic abelian variety supplies the boundedness making that representative finite type.

The universal property then organizes generic algebra: group laws, homomorphisms, products, endomorphisms, and principal polarizations extend uniquely. Isogenies extend too, but need not remain finite flat on integral models; their effect on components is controlled only away from primes dividing a quasi-inverse integer.

The special fiber separates continuous and discrete degeneration. Its identity component has abelian, toric, and unipotent layers. Its finite étale quotient records connected components with residue-field descent. Rational points specialize canonically, and over a henselian ring the kernel of their component map is exactly the connected Néron subgroup.

For Jacobians the construction is explicit. A regular curve model supplies a relative Picard object; quotienting by the schematic closure of the generic identity removes precisely vertical ambiguity. The intersection matrix presents the component group. In the semistable case, normalized components give the abelian part, graph cycles give the torus, and edge thicknesses give the integral pairing whose discriminant is the component group.

### 14.2 The boundary with monodromy theory

The component group is not the toric rank, geometric components are not automatically rational, and ramified base change is not ordinary scalar extension of a fixed smooth model. These distinctions are now encoded in canonical geometric objects rather than informal reduction pictures.

The next layer studies inertia on Tate modules, the character and cocharacter lattices of a general semistable abelian variety, conductor formulas, and quasi-unipotence. The present book supplies the objects that make those questions precise: the Néron model, its connected special fiber, its component group, and the exact comparison with regular curve models. Together they are the integral language in which good, multiplicative, additive, and semistable reduction can be distinguished without ambiguity.
