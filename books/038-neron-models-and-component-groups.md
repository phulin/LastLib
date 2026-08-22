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
9. [The Picard route to the Néron model](#9-the-picard-route-to-the-néron-model)
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
13. [Global Néron models](#13-global-néron-models)
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

An **abelian variety** is a smooth proper geometrically connected group variety over a field. An **abelian scheme** is its relative analogue: a smooth proper finitely presented group scheme with geometrically connected fibers. Book 35 supplies dual abelian schemes, isogenies, polarizations, and the extension theorem when both generic varieties already have abelian-scheme models. Here the generic abelian variety may have bad reduction, so proper models are not assumed.

For a smooth group scheme $\mathcal A/S$ of finite type, $\mathcal A_s^0$ denotes the connected component of the identity in the fiber. Later we construct an open subgroup scheme $\mathcal A^0\subseteq\mathcal A$ whose special fiber is $\mathcal A_s^0$. The component group is

$$
\Phi_A=\mathcal A_s/\mathcal A_s^0.
$$

It is a finite étale $k$-group scheme. The abstract geometric group is $\Phi_A(k^s)$, carrying its natural Galois action. We do not identify $\Phi_A(k)$ with the whole geometric group unless that action is trivial.

The regular-model input comes from Books 11 and 16. Thus a smooth projective curve over $K$ admits a regular proper model after the stated excellence hypotheses, and a semistable fiber has a geometric dual graph whose edge lengths record node thickness. Book 17a supplies relative Picard schemes and generalized Jacobians. Book 35 supplies abelian schemes, duality, isogenies, and polarizations. The one intersection-theoretic fact needed for a nonreduced fiber is proved directly in Section 10.1 from the principal-fiber relation, so no undeclared intersection-theory volume is being imported.

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

The property may be checked on smooth affine test schemes, but it cannot be checked only on unramified points or in codimension one.

**Proposition 2.4 (affine test).** A smooth separated $S$-model $\mathcal X$ of $X$ has the Néron mapping property if and only if (2.1) is bijective for every smooth affine $S$-scheme of finite type.

**Proof.** Necessity is immediate. Conversely, cover a smooth finite-type test scheme $T$ by smooth affine opens $T_i$. A generic map extends to every $T_i$ by hypothesis. On $T_i\cap T_j$ the two extensions agree on the schematically dense generic fiber; separatedness of $\mathcal X$ makes them equal. They therefore glue. The same density argument proves uniqueness. $\square$

There is no stronger pointwise shortcut. Let $T=\mathbf A_R^1$ with coordinate $x$. The formula

$$
T_K\longrightarrow\mathbf P^1_K,
\qquad x\longmapsto[x:\pi]
$$

is a morphism because $\pi$ is invertible on the generic fiber. It extends at every height-one point of $T$ but not at the closed codimension-two point $(x,\pi)$: there the pair $(x,\pi)$ does not generate an invertible ideal, and the two height-one specializations give incompatible values. Nevertheless $\mathbf P^1_R(R')\to\mathbf P^1_K(K')$ is bijective for every valuation ring $R'$ finite étale over $R$, by properness. Thus extension of all unramified points, even together with codimension-one extension, does not imply the Néron property. This example is why the construction below must control whole smooth families rather than only their sections.

### 2.3 Good reduction

An abelian variety $A/K$ has **good reduction** if it extends to an abelian scheme over $R$. The mapping property makes that extension canonical.

The key input for good reduction is the extension theorem traditionally called Weil's extension lemma.

**Lemma 2.5 (Weil extension over a regular base).** Let $T$ be a regular noetherian scheme, let $V\subseteq T$ be a schematically dense open containing every codimension-one point, and let $\mathcal B\to T$ be an abelian scheme. Every section of $\mathcal B$ over $V$ extends uniquely to a section over $T$.

**Proof.** The missing set has codimension at least two. Work Zariski-locally on $T$ and choose a polarization

$$
\lambda:\mathcal B\longrightarrow\mathcal B^\vee;
$$

Book 35 constructs both the dual abelian scheme and this finite locally free isogeny. Let $b_V$ be the given section and put $y_V=\lambda(b_V)$. By the Poincaré description of $\mathcal B^\vee$, $y_V$ is a rigidified algebraically trivial line bundle $L_V$ on $\mathcal B_V$.

The total space $\mathcal B$ is regular because it is smooth over the regular scheme $T$. Removing the inverse image of $T\setminus V$ removes only points of codimension at least two. On a regular noetherian scheme Cartier divisors extend uniquely across such a subset, so restriction gives

$$
\operatorname{Pic}(\mathcal B)\xrightarrow{\sim}
\operatorname{Pic}(\mathcal B_V).
$$

Thus $L_V$ extends to a line bundle $L$ on $\mathcal B$. Its rigidification extends as well: the restriction of $L$ to the identity section is trivial off a codimension-two subset of the regular scheme $T$, and the same Cartier-divisor argument makes it trivial on all of $T$. The classifying morphism $T\to\operatorname{Pic}_{\mathcal B/T}$ lands in the open-and-closed degree-zero component because it does so on the dense open $V$. Hence $L$ defines a section $y:T\to\mathcal B^\vee$ extending $y_V$.

Form the finite $T$-scheme

$$
Z=T\times_{y,\mathcal B^\vee,\lambda}\mathcal B.
$$

The section $b_V$ gives a section of $Z_V$. Its schematic closure $Z_0\subseteq Z$ is finite over $T$ and generically has degree one. Affine-locally its coordinate algebra is an integral $\mathcal O_T$-subalgebra of the function field of $T$. Normality of $T$ therefore forces that algebra to be $\mathcal O_T$. Consequently $Z_0\simeq T$, and its inclusion in $Z$ is the required lift $b:T\to\mathcal B$. Two lifts agree on the dense open $V$ and hence everywhere by separatedness. $\square$

The proof explains why abelian targets are special: polarization converts the rational section into a line bundle, and regularity extends line bundles across codimension two. Neither step exists for the map to $\mathbf P^1$ above.

**Theorem 2.6.** An abelian scheme $\mathcal A/R$ is the Néron model of its generic fiber.

**Proof.** Let $T/R$ be smooth and $u_K:T_K\to\mathcal A_K$. Smoothness makes $T$ regular, and $u_K$ is a section over $T_K$ of the abelian scheme $\mathcal A\times_RT\to T$. Properness extends that section at every height-one point of $T$, by the valuative criterion. Apply Lemma 2.5 to the maximal extension open. The section extends over all of $T$, and separatedness gives uniqueness. $\square$

**Lemma 2.6A (relative components via Stein factorization).** Let $R$ be an integrally closed noetherian domain with fraction field $K$, and let $G$ be a proper smooth $R$-scheme of finite type whose generic fiber is geometrically connected. Then every geometric fiber of $G\to\operatorname{Spec}R$ is geometrically connected; if moreover $G$ is a group scheme over $R$, it is an abelian scheme in the sense that all its fibers are abelian varieties.

**Proof.** Apply Stein factorization to $f:G\to S=\operatorname{Spec}R$ in the form proved in Book 9, Theorem 9.3: with

$$
S'=\operatorname{Spec}_S(f_\ast\mathcal O_G),
$$

the induced morphism $p:S'\to S$ is finite and the factor $g:G\to S'$ is proper, surjective, satisfies $g_\ast\mathcal O_G=\mathcal O_{S'}$, and has nonempty connected fibers. Write $B=\Gamma(S,f_\ast\mathcal O_G)=H^0(G,\mathcal O_G)$, a finite $R$-algebra with $S'=\operatorname{Spec}B$ because $S$ is affine.

First compute the generic fiber. For any field extension, cohomology of a proper scheme commutes with flat base change of fields, so

$$
H^0(G_K,\mathcal O_{G_K})=B\otimes_RK.
$$

The generic fiber $G_K$ is smooth, proper, and geometrically connected over $K$. Its ring of global functions is finite-dimensional over $K$, being the degree-zero part of a Stein factorization over $K$; equivalently, $B\otimes_RK$ is a finite $K$-algebra. Scalar extension along $K\subseteq\bar K$ identifies it with $H^0(G_{\bar K},\mathcal O)$, where geometric reducedness rules out nilpotents and geometric connectedness rules out decompositions into products of fields other than $\bar K$ itself. Hence $B\otimes_RK\otimes_K\bar K=\bar K$, forcing $\dim_K(B\otimes_RK)=1$; so $B$ is a finite torsion-free $R$-module of rank one, and $B\otimes_RK=K$.

Thus $B$ is a fractional ideal inside $K$, closed under multiplication and integral over $R$. Every element of $B$, being integral over $R$ and lying in $K$, belongs to $R$ because $R$ is integrally closed. Since conversely $R\subseteq B$, we get $B=R$ and $p:S'\to S$ is an isomorphism.

By Book 9, part (3) of the cited theorem, every fiber of $g$ is connected and nonempty; with $p$ an isomorphism these are the fibers of $f$. For geometric connectedness, extend scalars on a fiber $G_s$ to an algebraic closure $\overline{\kappa(s)}$: base change along fields preserves properness, and the identification $H^0(G_s,\mathcal O)=\kappa(s)$ pulls back to $H^0(G_{\bar s},\mathcal O)=\overline{\kappa(s)}$, so Book 9, part (4), applied over $\overline{\kappa(s)}$, shows $G_{\bar s}$ connected. If $G$ is a group scheme, each fiber is then a proper smooth connected group variety, that is, an abelian variety. $\square$

**Corollary 2.7.** If the Néron model $\mathcal A/R$ of an abelian variety is proper, then $A$ has good reduction and $\mathcal A$ is an abelian scheme.

**Proof.** The generic fiber of $\mathcal A$ is $A$, geometrically connected by hypothesis, and $\mathcal A$ is proper, smooth, and of finite type over the integrally closed domain $R$. Lemma 2.6A shows that every geometric fiber of $\mathcal A$ is connected, so $\mathcal A$ is an abelian scheme; this is precisely good reduction. The converse is Theorem 2.6. $\square$

This criterion is stronger than connectedness of the special fiber. A connected special fiber may contain a torus or a unipotent group and therefore fail to be proper.

### 2.4 Why smooth test spaces are exact

One might try to demand extension from every flat $S$-scheme. That condition is too strong. Let a regular model be blown up at a special point. The blowup is flat but not smooth over $S$ along parts of its exceptional geometry, and a generic map can approach different limiting points along different branches. A universal extension target should not be required to identify such incompatible limits.

At the other extreme, testing only $S$-valued points is too weak. Two smooth separated models can have the same $R$-sections but differ after an unramified residue extension, or they can agree on sections while representing different families over a positive-dimensional test scheme. The full smooth-site property detects residue descent, infinitesimal variation, and compatibility in families.

There is also a useful functorial consequence.

**Proposition 2.8.** Let $\mathcal X$ be the Néron model of $X$. For every smooth $S$-scheme $T$, the set of generic maps $T_K\to X$ is already an étale sheaf in $T$, and $\mathcal X$ represents it.

**Proof.** Morphisms to the separated $K$-scheme $X$ satisfy étale descent. The mapping property identifies this sheaf with $T\mapsto\operatorname{Hom}_S(T,\mathcal X)$, which is represented by $\mathcal X$. $\square$

This sheaf-theoretic formulation will turn smoothening data into an actual model.

## 3. Smoothening integral models

### 3.1 Weak Néron models

Existence begins with a less ambitious object that extends unramified points but not yet arbitrary smooth families.

**Definition 3.1.** A **weak Néron model** of a smooth $K$-scheme $X$ is a smooth separated $R$-scheme $W$ of finite type with generic fiber an open subscheme of $X$, such that

$$
W(R^{\mathrm{sh}})\xrightarrow{\sim}X(K^{\mathrm{sh}}). \tag{3.1}
$$

If $X$ is proper, every $K^{\mathrm{sh}}$-point has a center on any proper $R$-model. The task is to modify that model so every center lies in its smooth locus. Book 11 supplies proper flat models and the blowup technology; here we choose the centers according to the relative smoothness defect.

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

**Proof.** At stage $r$, use the Fitting ideals of $\Omega^1_{X_r/R}$ to give the non-smooth locus in $(X_r)_k$ its canonical Jacobian subscheme structure, and dilate that closed subscheme. Every section with non-smooth center factors through it modulo $\pi$. Property (3.2) therefore lifts the section uniquely, and the local elementary-divisor calculation (3.3)--(3.5) strictly decreases $\delta(a)$ until the center of that particular section is smooth.

To prove uniform termination, replace $R^{\mathrm{sh}}$ temporarily by its completion $\widehat R^{\mathrm{sh}}$.

It remains to prove that one stage works uniformly for all sections. For each $n$, sections modulo $\pi^{n+1}$ form the finite-type Greenberg scheme $\operatorname{Gr}_n(X)$ over $k^s$; this is the standard finite-level restriction-of-scalars construction for a finite-type scheme over a complete DVR. The inverse limit

$$
\operatorname{Gr}(X)=\varprojlim_n\operatorname{Gr}_n(X)
$$

is the space of formal sections. It is quasi-compact because it is an inverse limit of quasi-compact spectral spaces. For every $r$, let $U_r\subseteq\operatorname{Gr}(X)$ consist of sections whose lift to $X_r$ has smooth center. Smoothness is detected at a finite jet level, so $U_r$ is open. The sets are increasing, and the strict defect decrease shows that every formal section belongs to some $U_r$. Quasi-compactness gives

$$
\operatorname{Gr}(X)=U_0\cup\cdots\cup U_N=U_N
$$

for one $N$. Hence after finitely many dilatations every completed strict-henselian section has smooth center.

The centers were defined by Fitting ideals on the original $R$-models, so the finite initial sequence through $X_N$ is already defined over $R$. Every original $K^{\mathrm{sh}}$-point had a center by hypothesis and lifts uniquely through that sequence; comparison with the completion shows that its final center is smooth. Conversely a section of the smooth locus gives a generic point, and separatedness gives injectivity. This proves (3.6). Excellence guarantees the regularity and completion comparison used in passing to $\widehat R^{\mathrm{sh}}$. $\square$

Properness is used only to supply centers. The same argument applies whenever the chosen set of points is bounded on one finite-type model.

### 3.4 What smoothening does not yet provide

A weak Néron model is not usually a group. Start with a projective closure of an abelian variety and smoothen it. Addition is a rational map on the resulting model, but it need not extend between the chosen charts. Nor does (3.1) alone control maps from a smooth surface or a family with positive-dimensional special fiber.

This gap is genuine. The smooth locus of a proper regular model of a genus-one curve without a chosen origin is a torsor-like object, not canonically a group. Even when an origin exists, different smooth charts may be required to contain the reductions of $x$, $y$, and $x+y$.

The cure is not another arbitrary blowup. It is to regard every generic map into $A$ as an element of one sheaf and use translations to build compatible charts representing that sheaf. Smoothening supplies a bounded atlas; the group law supplies the transition maps. Chapter 4 carries out this passage.

### 3.5 Auxiliary tools

The smoothening process and its group-theoretic application in Chapter 4 consume four precise inputs which are recorded here once: an open-immersion criterion for étale radicial morphisms, Lang's theorem over finite fields with its torsor corollary, Weil restriction along finite locally free maps for quasi-projective targets, and quasi-compactness of the formal-section space used for uniform termination.

**Lemma 3.3 (étale radicial implies open immersion).** Let $f:X\to Y$ be a morphism that is étale and radicial (that is, universally injective). Then $f$ is an open immersion.

**Proof.** Étaleness makes $f$ flat and locally of finite presentation, and an étale morphism is open, so the image of $f$ is an open subset $V\subseteq Y$. Radicialness says that for every field-valued point of $Y$ the fiber has at most one point; in particular $f$ is injective on underlying points and each residue field extension $\kappa(y)\subseteq\kappa(x)$ over $y=f(x)$ is purely inseparable. Étaleness makes it separable as well, so

$$
\kappa(f(x))=\kappa(x)
$$

at every point. Fix $x\in X$, write $(A,\mathfrak m,k)=\mathcal O_{Y,f(x)}$ and $B=\mathcal O_{X,x}$. Then $B$ is a flat local $A$-algebra of finite presentation, the fiber $B/\mathfrak mB$ is the local ring of the singleton fiber, and the residue-field identity gives $B/\mathfrak mB=k$, generated by the image of $1$. Nakayama's lemma over the flat local map $A\to B$ then shows that the structure map $A\to B$ is surjective; being also flat and local, it is faithfully flat on its image, so its kernel is zero because $K\otimes_AB=0$ forces $K=0$. Thus $A\xrightarrow{\sim}B$. Hence $f$ induces isomorphisms on all stalks and is a homeomorphism onto the open subset $V$, so $f$ identifies $X$ with the open subscheme $V$. $\square$

**Lemma 3.4 (Lang's theorem over finite fields).** Let $k=\mathbf F_q$ be a finite field and let $G$ be a connected smooth $k$-group scheme of finite type. Let $F_G:G\to G$ be the absolute Frobenius endomorphism and let

$$
L_G:G\longrightarrow G,\qquad x\longmapsto F_G(x)\cdot x^{-1}
$$

be the Lang morphism. Then $L_G$ is étale and surjective. Consequently every torsor under $G_{k^s}$ descended to $k$ is trivial: the pointed set $H^1(k,G)$ is a singleton.

**Proof.** Étaleness. In characteristic $p$ the absolute Frobenius acts as the $p$-th power on functions, hence pulls back relative differentials to zero. The differential of $L_G$ at the identity is therefore

$$
d(L_G)_e=d(F_G)_e-\mathrm{id}=-\mathrm{id},
$$

an automorphism of the tangent space. The same computation applies at every point: composing $L_G$ with left translation by $F_G(x)^{-1}$ gives the morphism $y\mapsto F_G(yx)(yx)^{-1}$, which at $x$ has differential still of the form minus the identity transported by translations, because the added factor $F_G(x)$ is a constant and multiplication is a smooth map with surjective differential. Hence $L_G$ is étale.

Surjectivity. The image $I=L_G(G)(k^s)\subseteq G(k^s)$ contains the image of a nonempty open subscheme, since $L_G$ is étale and therefore open. Moreover $I$ is a subgroup of $G(k^s)$: if $y_i=F_G(x_i)x_i^{-1}$ for $i=1,2$, then

$$
y_1y_2^{-1}=F_G(x_1x_2^{-1})(x_1x_2^{-1})^{-1},
$$

as follows by expanding both sides. The complement of a subgroup is a union of cosets; since $I$ contains an open set, every coset is open, so the complement is open and $I$ is closed as well as open in the topological space underlying $G_{k^s}$. That space is connected because $k^s/k$ is purely inseparable and $G$ is geometrically connected over the perfect field $k$. A nonempty clopen subset of a connected space is everything, so $I=G(k^s)$.

Torsors. Let $X$ be a torsor under $G$ over $k$. After pullback to $k^s$ it becomes isomorphic to $G_{k^s}$; choose an equivariant trivialization and let $x\in X(k^s)$ be the point corresponding to the identity. Writing the right translation convention so that $\sigma(x)=xa_\sigma$ defines

$$
a_\sigma=\sigma(x)x^{-1}\in G(k^s),
$$

the identities $\sigma\tau(x)=\sigma(\tau(x))$ give exactly the cocycle relation

$$
a_{\sigma\tau}=a_\sigma\,\sigma(a_\tau).
$$

The scheme $X$ is of finite type over $k$, so both the chosen point and the Galois action are defined over some finite subextension $k'$; hence $\sigma\mapsto a_\sigma$ factors through the finite cyclic quotient $\operatorname{Gal}(k'/k)$, whose generator is the image of the Frobenius $F$. Replacing the base point $x$ by $x'=xb$ with $b\in G(k^s)$ changes the generating value to

$$
a'_\sigma=\sigma(xb)(xb)^{-1}=a_\sigma\,\sigma(b)\,b^{-1},
$$

so in particular $a'_F=a_F\,L_G(b)$. By surjectivity of $L_G$ choose $b$ with $L_G(b)=a_F^{-1}$; then $a'_F=1$. A cocycle factoring through a finite cyclic group is uniquely determined by its value at the generator, so $a'=1$ identically. Unwinding the definitions, $a'_\sigma=1$ says exactly that $x'$ is fixed by every $\sigma\in\operatorname{Gal}(k^s/k)$, and the fixed field of the full Galois group is $k$; hence $x'\in X(k)$. Every torsor has a $k$-point and $H^1(k,G)$ is a singleton. $\square$

In Chapter 6 this corollary is applied to the connected smooth group $\mathcal A_k^0$ acting on the components of the special fiber. Note what the proof does not use: neither properness of $G$ nor any classification theory. Only étaleness of Frobenius-twisted subtraction, openness of images, and connectedness enter.

**Lemma 3.5 (quasi-projective Weil restriction).** Let $p:S'\to S$ be finite locally free and let $X'$ be a quasi-projective $S'$-scheme, that is, locally closed in $\mathbf P(\mathcal V)$ for a finite locally free module $\mathcal V$ on $S'$. Then the functor

$$
T\longmapsto \operatorname{Hom}_{S'}(T\times_SS',X')
$$

is representable by a quasi-projective $S$-scheme $\operatorname{Res}_{S'/S}(X')$. If $X'\to S'$ is smooth, separated, or of finite presentation, so is $\operatorname{Res}_{S'/S}(X')\to S$.

**Proof.** Book 26, Theorem 20.1 proves representability when $X'$ is affine, together with compatibility with base change and with fiber products whenever the functors involved are representable. Extend to quasi-projective targets in two steps.

First, projective space restricts representably. For a test $T\to S$ with $T'=T\times_SS'$, a $T'$-point of $\mathbf P(\mathcal V)$ is an invertible quotient of $p^\ast\mathcal V\otimes_{\mathcal O_{S'}}\mathcal O_{T'}$. Since $p$ is finite locally free, the functor $p_\ast$ on quasi-coherent sheaves is exact and faithful, and quotients of $p^\ast\mathcal V\otimes\mathcal O_{T'}$ that are invertible correspond, through the trace pairing, to invertible direct summands of

$$
(p_\ast\mathcal O_{S'})^{\vee}\otimes_{\mathcal O_S}\mathcal V^{\vee}\otimes_{\mathcal O_T}\mathcal O_T,
$$

that is, to $T$-points of the projective bundle $\mathbf P\bigl((p_\ast\mathcal O_{S'})^{\vee}\otimes\mathcal V^{\vee}\bigr)$ over $S$. Hence $\operatorname{Res}_{S'/S}(\mathbf P(\mathcal V))$ is represented by a projective bundle.

Second, locally closed subschemes restrict representably. Let $X'\subseteq Y'$ be an open immersion into a scheme on which restriction is already represented, and cover $Y'$ by affines $U'_i=\operatorname{Spec}B_i$ such that $X'\cap U'_i=\operatorname{Spec}(B_i/f_i)$ for finitely many equations. By the affine case, each $\operatorname{Res}_{S'/S}(U'_i)$ is represented; the condition that a $T'$-map to $U'_i$ extend to one landing in $X'\cap U'_i$ says exactly that the pulled-back functions $f_i$ vanish, which is a closed-and-open-defining equation inside $\operatorname{Res}_{S'/S}(U'_i)$. These conditions glue over the overlaps of the cover because they express the same functor. Applying this twice — first to realize $X'$ as a locally closed subscheme of $\mathbf P(\mathcal V)$, then to each standard affine chart of projective space — represents the whole functor by a locally closed subscheme of the representing projective bundle. Hence $\operatorname{Res}_{S'/S}(X')$ is a quasi-projective $S$-scheme.

For the final assertions: separatedness transfers because the diagonal of the restricted functor is the restriction of the diagonal, closed immersions being preserved by the equation-cutting above. Finite presentation transfers because all coordinate rings entering the affine construction are finite projective modules, so finitely many equations remain finitely many. Smoothness follows from the infinitesimal criterion applied to the functor: a square-zero thickening of test schemes induces thickenings after base change by $p$, obstructions to lifting maps to the smooth $X'$ vanish on both sides simultaneously, and tangent spaces are identified by restriction of scalars on derivations. $\square$

This supplies the non-affine input used in Chapter 4: the charts constructed there are built as closures inside products of quasi-projective models, and their parameter spaces are Weil restrictions along finite locally free maps arising from finite étale descent data.

**Lemma 3.6 (quasi-compactness of the Greenberg limit).** Let $R$ be a complete discrete valuation ring with perfect residue field $k$ and let $X$ be a quasi-compact $R$-scheme. For $n\ge0$ let $\operatorname{Gr}_n(X)$ be the set of sections of $X\times_R R/\pi^{n+1}$, regarded as a $k$-scheme via the standard Greenberg construction for affine charts, and let $\operatorname{Gr}(X)=\varprojlim_n\operatorname{Gr}_n(X)$. Then $\operatorname{Gr}(X)$ is quasi-compact.

**Proof.** Choose a finite affine open cover $X=\bigcup_i X_i$, $X_i=\operatorname{Spec}B_i$. Each $\operatorname{Gr}_n(X_i)$ is affine of finite type over $k$: its coordinate ring is obtained by adjoining one variable per generator of $B_i$ and cutting out the ideal of relations levelwise modulo $\pi^{n+1}$, which remains finitely generated. The transition $\operatorname{Gr}_{n+1}(X_i)\to\operatorname{Gr}_n(X_i)$ is affine, and surjective because a section modulo $\pi^{n+1}$ lifts one step at a time by Hensel's lemma applied to the finitely many coordinate equations. Hence each

$$
G_i=\varprojlim_n\operatorname{Gr}_n(X_i)
$$

is an affine $k$-scheme, being an inverse limit of affine $k$-schemes along affine transitions.

A section $\operatorname{Spec}R^{\wedge}\to X$ is exactly a family of compatible formal sections over the $X_i$, two families being identified when they agree on every pairwise overlap $X_{ij}$. Since $X$ is separated, the equalizer of two morphisms into $X$ is closed; applied to the two projections from the product, agreement on $X_{ij}$ cuts out a closed subscheme of $G_i\times_kG_j$. Therefore $\operatorname{Gr}(X)$ identifies with the closed subscheme of the affine scheme $\prod_iG_i$ cut out by all these pairwise conditions. A closed subscheme of an affine scheme is quasi-compact. $\square$

With these tools available, the proof of Theorem 3.2 above may be read as complete: the appeal to "the standard finite-level restriction-of-scalars construction" is Lemma 3.6, the openness of $U_r$ is the jet-level detection already argued, and the completion comparison uses excellence exactly as stated.

## 4. Existence of Néron models

### 4.1 The extension sheaf

Let $j:\operatorname{Spec}K\to S$ be the generic inclusion and let $A/K$ be an abelian variety. On the category of smooth $S$-schemes define

$$
\mathscr N_A(T)=\operatorname{Hom}_K(T_K,A). \tag{4.1}
$$

Because morphisms into a separated scheme descend étale-locally, $\mathscr N_A$ is a sheaf for the étale topology. Pointwise addition of maps makes it a sheaf of abelian groups. A Néron model is exactly a smooth separated finite-type $S$-scheme representing this sheaf.

This formulation prevents a circular construction of the group law. We first represent the sheaf. Its addition, inverse, and identity then become morphisms by representability. The generic group identities automatically extend because two morphisms representing the same transformation are equal.

A weak Néron model $W$ gives a morphism of sheaves

$$
h_W\longrightarrow\mathscr N_A, \tag{4.2}
$$

where $h_W(T)=\operatorname{Hom}_S(T,W)$. It is not generally surjective, but it is an étale-local atlas near every special geometric point: after strict henselization, a generic point extends to $W$ by (3.1), and smoothness spreads that section over an étale neighborhood.

### 4.2 Representability from a weak model

We isolate the construction that turns the atlas into a scheme.

**Lemma 4.1A (centers for graph closures).** Let $U,V$ be smooth separated $R$-schemes of finite type satisfying the full weak extension property over strict henselization,

$$
U(R^{\mathrm{sh}})=U_K(K^{\mathrm{sh}}),
\qquad
V(R^{\mathrm{sh}})=V_K(K^{\mathrm{sh}}),
$$

and let $\Gamma\subseteq U\times_RV$ be the schematic closure of a locally closed subscheme $\Gamma_K$ of the generic fiber. Then:

1. $\Gamma$ is flat over $R$;
2. every $K^{\mathrm{sh}}$-point of $\Gamma_K$ extends, uniquely, to an $R^{\mathrm{sh}}$-point of $\Gamma$, so the center hypothesis of Theorem 3.2 holds for $\Gamma$.

In particular the hypothesis applies to closures inside $U\times_RV$ of graphs of generic isomorphisms between opens of a smooth separated variety, whose generic fibers are smooth.

**Proof.** Flatness. Over a discrete valuation ring a finite-type scheme is flat exactly when its coordinate rings have no $\pi$-torsion. Let $I$ be the ideal of $\Gamma$ in an affine chart of $U\times_RV$ with coordinate ring $B$, flat over $R$. If $\pi f$ lies in $I$, then $\pi f$ vanishes on $\Gamma_K$; since $\pi$ is invertible after localizing to the generic fiber, $f$ vanishes on $\Gamma_K$, which means $f$ lies in the kernel of $B\to B\otimes_RK$, and that kernel is exactly $I$ because $\Gamma$ is the schematic closure of its generic fiber. So $B/I$ has no $\pi$-torsion and $\Gamma$ is flat.

Centers. Let $\xi\in\Gamma_K(K^{\mathrm{sh}})\subseteq(U\times_RV)_K(K^{\mathrm{sh}})$ and let $x,y$ be its two coordinate points, in $U_K(K^{\mathrm{sh}})$ and $V_K(K^{\mathrm{sh}})$ respectively. By the weak extension property there are unique sections $\sigma_U:\operatorname{Spec}R^{\mathrm{sh}}\to U$ extending $x$ and $\sigma_V$ extending $y$; their product is a section $\sigma$ of $U\times_RV$ extending the point $\xi$ of the open subscheme $\Gamma_K$ of $\Gamma$. The preimage $\sigma^{-1}\Gamma$ is a closed subset containing the generic point; dually, since $\operatorname{Spec}R^{\mathrm{sh}}$ has underlying space two points with only one nontrivial open, any open or closed subset containing the generic point is everything. Hence $\sigma$ factors through the closed subscheme $\Gamma$, giving the required extension. Uniqueness follows from separatedness of $U\times_RV$: two extensions agreeing generically are equal. This produces a center for every $K^{\mathrm{sh}}$-point of the smooth generic fiber $\Gamma_K$ of the flat model $\Gamma$, which is precisely the hypothesis of Theorem 3.2 beyond properness. $\square$

The lemma converts boundedness data into smoothening input: once finitely many charts satisfy the full weak extension property, all overlap and graph closures between them inherit it and can be smoothened without further hypotheses.

**Theorem 4.1 (bounded group extension).** Let $G/K$ be a smooth separated group variety. Suppose:

1. $G$ has a weak Néron model $W$ of finite type;
2. finitely many translates of the generic open $W_K\subseteq G$ cover $G$;
3. the closures of the graphs of multiplication, inversion, and the translate overlaps admit smoothenings compatible with their projections.

Then the sheaf $T\mapsto\operatorname{Hom}_K(T_K,G)$ on smooth $R$-schemes is represented by a smooth separated group scheme $\mathcal G$ locally of finite type. If the translate classes required in the special fiber form a finite set, $\mathcal G$ is of finite type.

**Proof.** First pass to a finite extension over which a finite translate cover of $G$ is defined, enlarge it to a Galois extension, and include every conjugate chart. The graph smoothenings descend the resulting charts to a smooth $R$-space $U$ with a generically surjective map to $G$. A translate need not itself extend as an $R$-section; this is why one descends its graph rather than pretending that translation already exists integrally.

For two charts $U_i,U_j$, consider the generic isomorphism induced by translation on the overlap of their generic images. Take the closure of its graph $\Gamma_{ij}$ in $U_i\times_RU_j$. Lemma 4.1A verifies the center hypothesis of Theorem 3.2 for this closure — it is flat with smooth generic fiber, and every generic point extends by the weak extension property of the two charts — so Theorem 3.2 supplies the smoothening; retain the open on which both projections are étale. Over $R^{\mathrm{sh}}$ these projections identify exactly those sections having the same generic image: the weak extension property gives existence, and separatedness of $G$ gives uniqueness. Thus these overlap spaces define an étale equivalence relation

$$
R_U\rightrightarrows U. \tag{4.3}
$$

The relation is effective. Indeed, on affine étale neighborhoods of a special point, each projection is étale and radicial: two geometric points or two infinitesimal lifts with the same generic map coincide by separatedness and the weak extension property. By Lemma 3.3 an étale radicial morphism is an open immersion. The local quotients are therefore ordinary gluings along open subschemes. Equality of the generic translations gives the cocycle, again by separatedness. Gluing the charts gives a smooth $R$-scheme $\mathcal G$.

The same graph construction for multiplication shows that the generic product maps on $U_i\times U_j$ are compatible with (4.3) and descend to $\mathcal G\times_R\mathcal G\to\mathcal G$. Inversion and the identity descend similarly. Associativity and the group identities hold generically; both sides are morphisms from a flat scheme to a separated scheme, so they hold everywhere.

By construction, every generic map from a smooth $T$ lands étale-locally in a chart and extends there. The overlap relation glues the local extensions, proving the mapping property. The diagonal is closed because two charts are identified only where their generic maps agree and the graph closures were taken inside separated products. Thus $\mathcal G$ is separated and locally of finite type. If only finitely many special translate classes occur, finitely many charts cover $\mathcal G$, making it finite type. $\square$

The third hypothesis is not an extra existence assumption in the applications: Theorem 3.2 supplies the smoothenings, and Lemma 4.1A verifies its center hypothesis for every graph closure between charts that individually satisfy the full weak extension property. Smoothening provides charts; the generic group law tells us exactly how to glue them.

### 4.3 The existence theorem for abelian varieties

**Theorem 4.2 (existence).** Let $R$ be an excellent discrete valuation ring and $A/K$ an abelian variety. Then $A$ has a Néron model $\mathcal A/R$. It is a smooth separated group scheme of finite type. Its formation is unique up to unique isomorphism.

**Proof strategy.** Properness gives a weak model and also bounds the integral translate charts. The latter point is what distinguishes an abelian variety from a torus.

Choose a projective flat $R$-model $X$ of $A$ and apply Theorem 3.2 to obtain a weak model $W$. Since $A$ is quasi-compact, finitely many geometric translates of the nonempty open $W_K$ cover $A$. Smoothen the closures of their translate, multiplication, inverse, and overlap graphs. Theorem 4.1 produces a Néron lft-model $\mathcal A$.

It remains to show that only finitely many integral charts occur. Use the formal-section space from the proof of Theorem 3.2 after completing $R^{\mathrm{sh}}$; Lemma 3.6 makes it quasi-compact. Two identifications feed the argument. First, since the chosen projective model $X$ is proper over $R$, the valuative criterion applied to the discrete valuation ring $R^{\mathrm{sh}}$ with fraction field $K^{\mathrm{sh}}$ identifies points of $A$ over $K^{\mathrm{sh}}$ with sections of $X$ over $R^{\mathrm{sh}}$, and separatedness makes the identification unique; over the completion the same holds for $\widehat R^{\mathrm{sh}}$ and its fraction field. Excellence guarantees that passage between $R^{\mathrm{sh}}$ and $\widehat R^{\mathrm{sh}}$ changes nothing here, because a section over the completion of an excellent henselian DVR descends to a neighborhood, and both schemes are separated. Second, each graph chart in the lft-model contains an open cylinder of formal sections — those whose center lies in the chart's open smooth locus — because the chart is smooth and extension within it is unique. These cylinders cover the formal-section space by the mapping property built into the gluing: every formal section represents a generic map into $A$, which lands in some translate of $W_K$ and hence in some chart. A finite subcollection therefore covers it.

Every geometric point of the special fiber of the lft-model lifts to a formal section by smoothness, so the same finite collection covers the whole special fiber. Its generic fiber is the quasi-compact variety $A$, for which finitely many generic chart opens suffice as well. The complement of these finitely many charts has empty generic and special fibers and is therefore empty. Each selected chart and transition is defined over a finite étale subextension; adjoining its finite Galois orbit descends the finite collection to $R$. Hence finitely many finite-type charts cover $\mathcal A$.

Thus $\mathcal A$ is of finite type. Uniqueness is Theorem 2.3. $\square$

Properness is decisive in the boundedness paragraph because it gives a center on one quasi-compact special fiber for every unramified point. For a split torus, coordinate valuations range through all integers and no finite family of integral charts covers them; its Néron lft-model can have infinitely many components.

### 4.4 Gluing over a Dedekind base

Let $S$ now be an excellent Dedekind scheme and $A/K$ an abelian variety. Spread $A$ and its group law to an abelian scheme over a nonempty open $U\subseteq S$. The complement is finite after shrinking $U$ inside any fixed quasi-compact base. At each $s\in S\setminus U$, Theorem 4.2 constructs a Néron model over $S_s$.

**Theorem 4.3 (global existence).** The local Néron models over $S_s$ and the abelian scheme over $U$ glue uniquely to a smooth separated finite-type group scheme $\mathcal A/S$ satisfying the Néron mapping property.

**Proof.** One cannot glue a scheme over $S_s$ directly to a scheme over $U$ along the generic point, because that point is not an open overlap. We first spread every local model. Its coordinate charts, group law, inverse, identity, smoothness, and separated diagonal are all finite-presentation data. Hence the Néron model over $S_s$ descends to a smooth separated finite-type group scheme $\mathcal A^{(s)}$ over an open neighborhood $V_s$ of $s$.

The generic identification with $A$ also spreads. After shrinking $V_s$ while retaining $s$, it identifies $\mathcal A^{(s)}$ with the abelian scheme over $V_s\cap U$: an isomorphism and its inverse are finitely many morphisms and identities, so they spread from the generic point after deleting finitely many closed points. Choose the $V_s$ to contain no other point of $S\setminus U$. The schemes over $U$ and the finitely many $V_s$ now glue along genuine open overlaps. Their overlap isomorphisms are unique after localization at the generic point, so they satisfy the cocycle and preserve the group laws.

For the mapping property, let $T/S$ be smooth and start with $T_K\to A$. Theorem 2.6 extends it over $T_U$. The local Néron property at $s$ extends it over the whole base change $T\times_SS_s$. Morphisms between finitely presented schemes commute with the filtered limit of the open neighborhoods of $s$, so this latter morphism descends to $T_{V'_s}$ for some smaller open neighborhood $V'_s\subseteq V_s$ of $s$. The two extensions agree over $T_{U\cap V'_s}$ by generic density and separatedness, and hence glue. Doing this for the finitely many bad points produces an extension over all of $T$. Uniqueness is the same density argument. Finite type, smoothness, and separatedness are local on $S$. This proves the theorem. $\square$

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

This is an equality of rings. It is stronger than the normal-base extension theorem of Book 35 because $\mathcal A$ need not be proper.

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

In the good-reduction case $\mathcal A$ is proper, and Book 35 recovers a finite locally free kernel of rank $n^{2g}$. Bad reduction requires separate attention to the identity component and components.

### 5.4 Dual abelian varieties and polarizations

The dual $A^\vee$ has its own Néron model $\mathcal A^\vee_{\mathrm N}$. This notation is intentionally different from a relative dual of $\mathcal A$: a nonproper smooth group scheme does not generally possess a dual abelian scheme.

A polarization $\lambda:A\to A^\vee$ extends uniquely to

$$
\lambda_{\mathcal A}:\mathcal A\longrightarrow\mathcal A^\vee_{\mathrm N}. \tag{5.4}
$$

If $\lambda$ is principal, the generic inverse extends as well, and the two composites are identities. Hence:

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

A $k$-rational point of the quotient labels a component defined over $k$, but that component is a torsor under $\mathcal A_k^0$ and can lack a $k$-point. If $k$ is finite, $\mathcal A_k^0$ is connected and smooth over $k$, so Lemma 3.4 makes every such torsor trivial; if $k$ is separably closed, the assertion is obvious. In either case $c_A$ is surjective and

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

where $B$ is an abelian variety and $L$ is a connected smooth affine group. Since $\mathcal A_k^0$ is commutative, the torus quotient of $L$ is described by the following lemma, which we prove in full; together with the abelian step discussed after it, this gives

$$
0\longrightarrow U\longrightarrow L\longrightarrow T\longrightarrow0. \tag{6.9}
$$

**Lemma 6.3A (torus quotient of a commutative affine group).** Let $k$ be any field and let $L$ be a smooth connected affine commutative $k$-group scheme of finite type. There is a canonical exact sequence

$$
0\longrightarrow N\longrightarrow L\longrightarrow T\longrightarrow0,
$$

where $T$ is a torus (possibly trivial) and $N$ is a unipotent closed subgroup; $L\to T$ is a maximal torus quotient of $L$, unique up to canonical isomorphism. One has $\dim N=\dim N_{\mathrm{red}}^0$, and $N_{\mathrm{red}}^0$ is the largest smooth connected unipotent subgroup of $L$.

**Proof.** _Faithful representations._ For every finite-dimensional faithful representation $\rho:L\to\operatorname{GL}(V)$ — such representations exist because $L$ is affine of finite type: finitely many coordinate functions, closed under the finitely many translates appearing in their comultiplication expansions, span a translation-stable subspace $V$, and the resulting action is a closed immersion since those functions separate points and tangent vectors — consider the induced map on associated graded. Over an algebraic closure, the commuting image of $L$ stabilizes a complete flag: by induction on $\dim V$, a commuting family of automorphisms of a finite-dimensional vector space over an algebraically closed field has a common eigenvector, namely an eigenspace of one member, which is stable under the others. Passing to associated graded, the image of $L$ in $\prod_i\operatorname{GL}(V_i/V_{i-1})$ lands in the diagonal torus and, being commutative, connected, and smooth there, it is a torus $D_V$. Define

$$
\theta_V:L\longrightarrow D_V
$$

as this diagonalization map. Its kernel is unipotent: an element acting trivially on every graded piece of a stabilized flag is upper triangular with unit diagonal.

_The universal quotient._ Among all the diagonalization maps $\theta_V$, choose one whose target $D_V$ has maximal dimension; such exists because $\dim D_V\leq\dim L$ for every $V$. Set

$$
T=D_V,
\qquad
N=\ker\theta_V,
$$

giving an exact sequence $0\to N\to L\to T\to0$ with $T$ a torus and $N$ unipotent. The pair is independent of choices up to canonical isomorphism: any two maximal torus quotients $T_1,T_2$ of $L$ dominate one another, because the composite $T_1\to L/N_2\to T_2$ of the first quotient with a section-realizing map has dense image, being nonzero on each character direction by maximality of $\dim T_1$, and symmetrically for $T_2\to T_1$; mutual dominance of tori of equal dimension is an isomorphism, a morphism of tori with dense image being surjective and a surjective endomorphism appearing twice around a loop being an isomorphism on character lattices. Hence $T$ deserves to be called the maximal torus quotient of $L$, and $N$ its canonical unipotent kernel.

_Dimensions and smooth subgroups._ Dimension is unchanged by infinitesimal thickenings of kernels, so $\dim N=\dim N_{\mathrm{red}}^0$. Over a perfect field the reduction of a group scheme of finite type is a smooth subgroup, because it is geometrically reduced, and the identity component $N_{\mathrm{red}}^0$ is then a smooth connected unipotent subgroup. Conversely, if $H\subseteq L$ is any smooth connected unipotent subgroup, then every $\theta_V(H)$ is simultaneously unipotent and a subgroup of a torus, hence trivial; so $H\subseteq N$, and being smooth and connected, $H\subseteq N_{\mathrm{red}}^0$. $\square$

In characteristic zero every group scheme of finite type is smooth, so $N=U$ is smooth and (6.9) is exact with smooth terms. In characteristic $p$ the kernel $N$ can carry an infinitesimal core — the map $x\mapsto x^p$ on $\mathbf G_m$ has kernel $\boldsymbol\mu_p$ — and the honest statement is the one just proved: the torus quotient $T$ is canonical, the unipotent kernel is canonical up to infinitesimal thickening, and the dimension bookkeeping below involves only dimensions, for which the distinction is invisible. None of the later graph formulas distinguishes a unipotent kernel from its smooth identity component.

**The abelian step.** It remains to produce the sequence (6.8). The construction is the boundary-stabilizer method, and we carry out its steps explicitly. One classical input is used, isolated here so that its content is explicit. _(Equivariant completion with polarizable boundary.)_ A connected algebraic group $G$ over a field admits an open immersion into a complete variety $C$ such that the boundary $D=C\setminus G$ supports an effective ample Cartier divisor, again denoted $D$. This is the theorem of Nagata and Rosenlicht in its equivariant form; it is the analytic heart of Chevalley's theorem. Granting it, the rest is elementary.

Let $G=\mathcal A_k^0$ and fix such a pair $(C,D)$. Consider the Chow variety parametrizing effective divisors in the numerical class of $mD$ for fixed large $m$; it is a quasi-projective scheme, being a component of a Hilbert-scheme-type parameter space of cycles on the projective variety $C$. The action map

$$
G\longrightarrow\operatorname{Chow}(C),\qquad g\longmapsto[gD]
$$

sends $g$ to the translate of $D$. Its image is a constructible subset, and its closure is complete, being a closed subset of the proper Chow variety of all cycles in that class. Let $H_1$ be the stabilizer of the point representing this closed orbit closure; by the fundamental property of group actions on varieties, the orbit map induces an identification of the closure with the homogeneous space $G/H_1$, so $G/H_1$ is complete.

The stabilizer of $D$ itself,

$$
H=\{g\in G: gD=D\},
$$

is a closed subgroup scheme of $G$, the condition $g^\ast D=D$ being represented by equations among the finitely many sections cutting out $D$. It is affine: since $mD$ is very ample for suitable $m$, the finite-dimensional space $W=H^0(C,\mathcal O_C(mD))$ carries the linear representation of $H$ induced by pullback, and $H$ preserves the divisor $mD$, hence the line spanned by the $m$-th power of the canonical section of $\mathcal O_C(D)$; so $H$ embeds into the stabilizer of a line in $\operatorname{GL}(W)$, a linear group. Thus $H$ is affine.

Now iterate. Each application of the construction produces a closed subgroup $H_1\supseteq H$ with $H$ affine and $G/H_1$ complete. Consider the class of normal subgroups $M\triangleleft G$ that arise as kernels of homomorphisms from $G$ onto complete quotients and contain one of these affine stabilizers; each such $M$ is itself affine, since it is contained in an affine stabilizer of the construction that produced it, and closed subgroups of affine groups are affine. Choose $L$ in this class of maximal dimension; maxima exist because all dimensions are bounded by $\dim G$. Then $L$ is affine and normal, and

$$
B=G/L
$$

is complete, being the quotient through which $L$ was defined. It remains to identify $B$. Every morphism from a complete connected variety to an affine scheme is constant, because global functions on a complete connected variety reduce to constants; hence every homomorphism from $B$ to any affine group scheme is trivial, so $B$ carries no characters and no affine quotients. Moreover $B$ is commutative by the rigidity lemma of Book 35: the commutator map $B\times B\to B$ restricts on $\{e\}\times B$ to the constant map with value $e$, and rigidity over the field base forces it to factor through that base. A smooth proper group variety with geometrically connected fibers is precisely an abelian variety in the sense of Book 35, Chapter 1. This proves (6.8).

Two properties of this filtration are recorded for later use. First, uniqueness: if

$$
0\to L'\to\mathcal A_k^0\to B'\to0
$$

is another such sequence, the composite homomorphism $L'\to B$ has image that is both a quotient of an affine group, hence affine, and a closed subgroup of the complete group $B$, hence complete; an affine complete connected group is a point, so $L'$ dies in $B$ and factors through $L$. Symmetry gives the reverse factorization, and dimension equality upgrades the resulting isogenies to isomorphisms. Second, functoriality: a homomorphism of connected smooth commutative groups sends unipotent subgroups to unipotent subgroups and, by universality of the torus quotient of Lemma 6.3A and maximality in (6.8), induces compatible homomorphisms on all three graded pieces. $\square$

Write

$$
a(A)=\dim B,\qquad t(A)=\dim T,\qquad u(A)=\dim U,
$$

where $U=N_{\mathrm{red}}^0$ is the smooth connected unipotent kernel of Lemma 6.3A; by that lemma the choice of $U$ versus $N$ does not affect any of these dimensions.

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

**Proof.** The equivalence of 1 and 2 is Corollary 2.7, and good reduction plainly implies 3. Conversely, under 3 both fibers of the smooth separated finite-type morphism $\mathcal A\to\operatorname{Spec}R$ are proper: the generic fiber is $A$ and the special fiber equals the assumed abelian identity component.

We recall the fiberwise properness argument over a valuation base. Choose a compactification $\mathcal A\hookrightarrow\overline{\mathcal A}$ and replace it by the schematic closure of the generic fiber, so that it is proper and flat over $R$ and $\mathcal A$ is dense. Since $A$ is proper, its open immersion into $\overline{\mathcal A}_K$ is also closed; density makes it the whole generic fiber. Stein factorization gives connected fibers for $\overline{\mathcal A}$: its finite Stein factor is birational over the normal local base because the generic fiber is geometrically connected, and hence equals $\operatorname{Spec}R$. The open immersion $\mathcal A_k\hookrightarrow\overline{\mathcal A}_k$ is proper, hence closed, because $\mathcal A_k$ is proper and the target is separated. It is nonempty, so connectedness makes it the whole special fiber. The boundary has neither a generic nor a special point and is empty. Therefore $\mathcal A$ is proper. This gives 2 and completes the equivalence. $\square$

The condition $\Phi_A=0$ alone is much weaker: a semiabelian connected special fiber can still contain a torus. Likewise $U=T=0$ without control of components is not by itself the formulation one should use.

### 7.2 Elliptic curves

Let $E/K$ be an elliptic curve. Its minimal regular proper model exists by the regular-model and contraction results of Book 11, and the Néron description is especially concrete.

**Theorem 7.2.** Let $\mathcal C/R$ be the minimal regular proper model of $E$, with the origin extended to a section. Its smooth locus $\mathcal C_{\mathrm{sm}}$ is the Néron model $\mathcal E$ of $E$.

**Proof.** Put $\mathcal U=\mathcal C_{\mathrm{sm}}$. We first record where sections of $\mathcal C$ land. After strict henselization, if a section $P$ meets the special fiber, intersection with the principal fiber gives

$$
1=(P\cdot\mathcal C_k)=\sum_jm_j(P\cdot\Gamma_j).
$$

All summands are nonnegative integers. Thus $P$ meets one multiplicity-one component transversely and avoids every other component; the special fiber is regular at that point and the morphism is smooth there. Properness of $\mathcal C$ gives a center for every point of $E(K^{\mathrm{sh}})$, so

$$
\mathcal U(R^{\mathrm{sh}})=E(K^{\mathrm{sh}}).
$$

Let $\mathcal E$ be the Néron model supplied by Theorem 4.2. Compactify $\mathcal E$ over $R$, take the closure of its proper generic fiber, normalize, and resolve without changing the regular open $\mathcal E$. Book 11 gives a regular proper model $\mathcal Y$ containing $\mathcal E$ as an open subscheme. Relative minimality gives a unique morphism $\mathcal Y\to\mathcal C$ inducing the identity on $E$; restrict it to $f:\mathcal E\to\mathcal C$.

The morphism $f$ factors through $\mathcal U$. Indeed every geometric point of $\mathcal E_k$ lifts, after strict henselization, to a section because $\mathcal E$ is smooth. Its image is a section of $\mathcal C$, and the preceding intersection calculation puts its special point in $\mathcal U$. Hence the inverse image of the closed complement $\mathcal C\setminus\mathcal U$ has no geometric point and is empty.

Conversely, the generic identity $\mathcal U_K=E\to E$ extends by the Néron property to $g:\mathcal U\to\mathcal E$. Both $fg$ and $1_{\mathcal U}$ agree on the dense generic fiber, as do $gf$ and $1_{\mathcal E}$; separatedness makes both pairs equal. Thus $f$ and $g$ are inverse isomorphisms, proving that $\mathcal U$ is the Néron model. $\square$

The three familiar cases now have a uniform form over an algebraic closure of $k$:

| reduction      | $\mathcal E_k^0$ | geometric component group                     |
| -------------- | ---------------- | --------------------------------------------- |
| good           | elliptic curve   | $0$                                           |
| multiplicative | $\mathbf G_m$    | cyclic, determined by the polygon             |
| additive       | $\mathbf G_a$    | finite, determined by the fiber configuration |

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

The component map induced by the canonical base-change morphism (8.1) is

$$
i_e:X^\vee/qX\longrightarrow X^\vee/eqX,
\qquad [x]\longmapsto[ex]. \tag{8.5}
$$

It is injective: if $ex\in eqX$, then $x\in qX$. Its cokernel is $X^\vee/eX^\vee$, so

$$
0\longrightarrow\Phi_A(k^s)\xrightarrow{i_e}
\Phi_{A_{K'}}(k^s)
\longrightarrow X^\vee/eX^\vee\longrightarrow0. \tag{8.6}
$$

There is also a different natural map, obtained by reducing a class modulo the larger lattice $qX$:

$$
0\longrightarrow X/eX\xrightarrow{q}\Phi_{A_{K'}}(k^s)
\xrightarrow{\pi_e}\Phi_A(k^s)\longrightarrow0. \tag{8.7}
$$

The maps satisfy $\pi_ei_e=[e]$ on the old group and $i_e\pi_e=[e]$ on the new group. Thus (8.7) is not the component map of (8.1); it is the contraction quotient supplied by the nested monodromy lattices. Both sequences give

$$
|\Phi_{A_{K'}}|=e^{\operatorname{rank}X}|\Phi_A|. \tag{8.8}
$$

For a polygon this says that the base-change map $\mathbf Z/n\mathbf Z\to\mathbf Z/en\mathbf Z$ is multiplication by $e$, whereas $\pi_e$ is reduction modulo $n$. Outside the semistable setting, ramification may also alter a unipotent part; the old component group alone cannot determine the result.

### 8.4 Descent and Galois action

For a finite unramified Galois extension, Theorem 8.1 transports the descent datum to every special-fiber layer. In particular

$$
\Phi_A(k)=\Phi_A(k^s)^{G_k}. \tag{8.9}
$$

The torus descends through its character lattice, where branch reversal can act by $-1$. Smoothness, separatedness, finite type, and the mapping property all descend because extensions are unique. For ramified descent one must instead compare with (8.1); the base-changed model need not already be Néron.

## 9. The Picard route to the Néron model

### 9.1 Regular curve models and relative line bundles

Let $C/K$ be a smooth proper geometrically connected curve, $J=\operatorname{Pic}^0_{C/K}$, and $\mathcal X/R$ a regular proper flat model. Write $P^{[0]}$ for the degree-zero relative Picard object: the fppf sheaf associating to an $R$-scheme $T$ the group of line bundles on $\mathcal X\times_RT$ whose restriction to the generic fiber has degree zero. In the presence of nonreduced fibers this object need not be smooth, and its naive charts need not be separated from one another, so we record precisely how it is represented as a scheme and which replacement is used beyond the smooth and nodal cases of Book 17a.

The construction is by gluing smooth charts, in the manner of Book 16. First, boundedness: vertical divisors $\sum_ia_i\Gamma_i$ change the special multidegree of a line bundle by the image of the intersection matrix, and only finitely many multidegree classes are needed because the coefficients range over a fixed finite set of representatives modulo that image; fix one finite set of multidegrees covering the degree-zero orbits. Second, each multidegree class is carried by a smooth quasi-projective $R$-scheme: choose a relatively ample line bundle $H$; relative Serre vanishing kills $H^1$ on every fiber for large twists and lets every line bundle in the class be presented as a difference of two effective Cartier divisors with Hilbert polynomials from one fixed finite list; such divisors form opens in relative Hilbert schemes, and, as in the high-degree quotient construction of Book 17a, pairs of them modulo linear equivalence form smooth quasi-projective charts. Third, translation by vertical line bundles identifies the charts: tensoring with $\mathcal O_{\mathcal X}(\sum_ia_i\Gamma_i)$ maps a chart of one multidegree isomorphically onto an open of another, the cocycle being addition of vertical divisors. Because these transition maps are isomorphisms between schemes, the glued object is a scheme — not merely a sheaf — locally of finite presentation, and it represents $P^{[0]}$. This mirrors exactly the separated Picard quotient construction of Book 16, where the gluing is shown to be effective and the resulting scheme smooth whenever the charts are.

Call $\mathcal X$ **Picard-admissible** when the required degree-zero charts are already a smooth group scheme locally of finite type and commute with strict henselization. Regular semistable models satisfy this by Book 16, and cohomological flatness in degree zero also suffices.

In general let $P^\natural$ denote the **Raynaud smoothening** of these charts. The Picard-smoothening theorem is the group form of Theorem 3.2, applied chart by chart with the center hypothesis supplied by Lemma 4.1A: perform compatible dilatations along the non-smooth loci in each bounded chart, use tensor product to transport the dilatations to all translates so that the gluing isomorphisms remain defined, and take the filtered union over the finite multidegree set. Each smoothened chart is a smooth $R$-scheme by Theorem 3.2 — its generic fiber $J$ is smooth, it is flat and of finite type, and every generic point extends by the weak extension property established in the preceding paragraph — so the glued result $P^\natural$ is a smooth group scheme locally of finite type, represented as an honest scheme at every stage. The closure of the generic identity in it is flat, and its separated quotient is unchanged by the preliminary dilatations. It also has the required universal feature: a morphism from a smooth $R$-scheme to the Picard object whose generic image lies in $J$ factors fppf-locally through $P^\natural$. All operations are canonical because two smoothenings have a common further smoothening. If $\mathcal X$ is Picard-admissible, no dilatation is needed and $P^\natural=P^{[0]}$.

A vertical divisor is empty generically, so its line bundle represents the generic identity while possibly changing special multidegree. Smoothening changes its integral chart but does not change its generic class or the equivalence relation generated by such vertical bundles.

### 9.2 The closure of the generic identity

Let $E\subseteq P^\natural$ be the schematic closure of the generic identity. Over a strict henselization, it is represented by the smoothened charts of vertical line bundles

$$
\mathcal O_{\mathcal X}\left(\sum_i a_i\Gamma_i\right), \tag{9.1}
$$

modulo multiples of the whole fiber.

**Lemma 9.1.** Two line bundles on $\mathcal X$ with isomorphic generic restrictions differ, after a base pullback, by a vertical Cartier divisor. The same assertion holds fppf-locally after base change by a smooth $R$-scheme $T$: the difference is represented by a divisor supported on $\mathcal X_k\times_kT_k$, with coefficients locally constant on its component strata.

**Proof.** A generic isomorphism is a rational section of the ratio line bundle. Its divisor has no horizontal part and is therefore supported on the special fiber. Scaling by $K^\times$ changes it by a multiple of the principal whole fiber. For the relative assertion, $\mathcal X\times_RT$ is regular because it is smooth over the regular scheme $\mathcal X$. The same divisor argument applies; after an fppf refinement of $T$, the irreducible vertical components and their coefficients are constant in the family. A factor pulled back from $T$ is invisible in the relative Picard functor. $\square$

**Lemma 9.2.** The fppf quotient

$$
Q=P^\natural/E. \tag{9.2}
$$

is separated.

**Proof.** The smoothening theorem makes $E$ flat and étale; translation makes its action free. Choose representatives of the vertical multidegree orbits on any finite collection of charts. Translation by $E$ glues their open smooth images, so the fppf quotient is represented locally; these local quotients glue because changing a representative is another translation by $E$.

Two valuation-ring sections agreeing generically differ, after local lifting to Picard charts before smoothening, by a generically trivial line bundle. Lemma 9.1 puts that difference in $E$. The valuative criterion therefore makes the diagonal of the quotient closed. $\square$

Schematic closure matters: visible vertical points can form a nonsaturated subgroup and give the wrong finite quotient.

### 9.3 The Raynaud quotient theorem

**Theorem 9.3 (Raynaud quotient).** For every regular proper model $\mathcal X/R$, with $P^\natural$ understood as above, the quotient $Q$ is the Néron model $\mathcal J$ of $J$. Its identity component is the image of the smoothened multidegree-zero Picard subgroup. For a Picard-admissible model this reads $\mathcal J=P^{[0]}/E$.

**Proof strategy.** Extension comes from closing divisors on the regular surface; uniqueness is exactly division by $E$.

The construction of $P^\natural$ makes $Q$ smooth and locally of finite type, and Lemma 9.2 makes it separated. Its generic fiber is $J$.

Let $T/R$ be smooth and $T_K\to J$ a map. Fppf-locally on $T$ it is represented by a line bundle and, after the high-degree divisor construction, by a difference of relative divisors on $C\times_KT_K$. Move their support apart and close them in $\mathcal X\times_RT$. This fiber product is regular because it is smooth over the regular scheme $\mathcal X$; hence the codimension-one closures are Cartier and their difference is a line bundle extending the generic class. It defines a local map to the Picard object, which factors locally through $P^\natural$ by the smoothening property. The local extensions differ on overlaps by generically trivial bundles, hence by $E$ through Lemma 9.1. They descend uniquely to $T\to Q$. This proves the Néron mapping property.

Theorem 4.2 has already constructed the Néron model $\mathcal J$ as a scheme. Applying its mapping property on smooth charts of $Q$, and the property just proved in the reverse direction, gives inverse maps $Q\rightleftarrows\mathcal J$. Thus $Q$ is that finite-type scheme. The smoothened multidegree-zero chart contains the identity and is connected; every other fixed-multidegree chart is its translate. Its image is therefore exactly $Q^0$. In the semistable case this connected chart is the generalized Jacobian described in Book 16; for a nonreduced fiber it may also contain a unipotent part. $\square$

In the regular semistable case, Book 16 already constructed this separated Picard quotient and proved its extension property directly from divisors and vertical line bundles; Book 17a imported that result for its specialization chapter. The theorem here does not serve as a premise for those earlier books. It identifies their independently constructed quotient with the Néron model by the universal property and extends the method to arbitrary regular models by inserting the explicit group-smoothening step.

### 9.4 Independence of the regular model

If $\mathcal X'\to\mathcal X$ blows up a special point, pullback introduces only the exceptional vertical class beyond the old Picard classes. It belongs to the closure of the generic identity, so

$$
(P^\natural_{\mathcal X/R})/E_{\mathcal X}
\simeq(P^\natural_{\mathcal X'/R})/E_{\mathcal X'}. \tag{9.3}
$$

Any two regular models have a common regular domination by Book 11. Thus the quotient is model-independent, as uniqueness of the Néron model also requires.

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

**Proof.** We include the intersection argument so that the dependency is closed. For $i\ne j$, put

$$
b_{ij}=(\Gamma_i\cdot\Gamma_j)\geq0.
$$

These are sums of local intersection lengths, including residue degrees. The whole fiber is the principal divisor of $\pi$, so for every $i$,

$$
0=(\mathcal X_k\cdot\Gamma_i)
=m_i\Gamma_i^2+\sum_{j\ne i}m_jb_{ij}. \tag{10.3}
$$

For $V=\sum_i a_i\Gamma_i$, substitute (10.3) into $V^2$ and group unordered pairs. One obtains the weighted Laplacian identity

$$
V^2=-\sum_{i<j}m_im_jb_{ij}
\left(\frac{a_i}{m_i}-\frac{a_j}{m_j}\right)^2. \tag{10.4}
$$

Thus the form is negative semidefinite. The support of the fiber is connected: Stein factorization of the proper model is finite over the normal local base and has generic fiber $\operatorname{Spec}K$, hence is the base itself. Therefore equality in (10.4) forces all $a_i/m_i$ to be equal. The rational kernel is exactly $\mathbf Q(m_i)$ and the matrix has rank $|I|-1$.

Finally, (10.3) says $M(\mathbf Z^I)\subseteq\Lambda$. Both are lattices of rank $|I|-1$, so the index is finite. $\square$

### 10.2 The component-group formula

**Theorem 10.2.** There is a canonical Galois-equivariant isomorphism

$$
\Phi_J(k^s)\simeq\Lambda/M(\mathbf Z^I). \tag{10.5}
$$

**Lemma 10.2A (moving a germ to a horizontal divisor).** Let $\mathcal X$ be a regular projective flat $R^{\mathrm{sh}}$-scheme of relative dimension one with special fiber $\sum_im_i\Gamma_i$, and let $x_i\in\Gamma_i(k^s)$ be a point at which $\mathcal X$ is regular and which lies on no component other than $\Gamma_i$. Then there is an effective horizontal Cartier divisor $H_i$ on $\mathcal X$ whose support passes through $x_i$, meets the special fiber only in smooth points lying on single components, and satisfies

$$
(H_i\cdot\Gamma_j)=
\begin{cases}
1 & j=i,\\
0 & j\neq i.
\end{cases}
$$

**Proof.** The point $x_i$ is a regular point of the two-dimensional local scheme $\mathcal X$, and $\Gamma_i$ is cut out near $x_i$ by one element $t$ of a regular system of parameters $(t,u)$, with

$$
\pi=t^{m_i}\cdot\bar u(t,u)
$$

in the complete local ring $\widehat{\mathcal O}_{\mathcal X,x_i}\cong k^s[[t,u]]$, where $\bar u(0,0)\neq0$ because the coefficient of $\Gamma_i$ in the special fiber is exactly $m_i$. Choose a finite totally ramified extension $R'/R^{\mathrm{sh}}$ of degree $m_i$ with uniformizer $\Pi$, $\Pi^{m_i}=\pi$; such extensions exist over the strict henselization for every degree, separably. Define a local homomorphism

$$
k^s[[t,u]]\longrightarrow R'
\qquad\text{by}\qquad
t\mapsto\Pi,
\qquad
u\mapsto b,
$$

where $b\in R'$ is chosen by Hensel's lemma so that $\bar u(\Pi,b)=1$: this is possible because $\bar u(0,0)\neq0$, so $\bar u(\Pi,b)$ is invertible and congruent to it modulo $\Pi$. Under this map $\pi$ maps to $\Pi^{m_i}$, so the map descends to a local morphism

$$
\sigma:\operatorname{Spec}R'\longrightarrow\mathcal X
$$

whose special point is $x_i$ and whose generic point is a closed point $P_i$ of the generic fiber curve $C_{K^{\mathrm{sh}}}$ of degree

$$
[\text{residue field of }P_i:K^{\mathrm{sh}}]=m_i.
$$

Let $H_i$ be the schematic closure of $P_i$ in $\mathcal X$. Because $\mathcal X$ is regular, the closure of an effective Cartier divisor of the generic fiber is an effective Cartier divisor; $H_i$ is horizontal, meeting the special fiber only along its reduction, which is supported at $x_i$. The standard identity for horizontal Cartier divisors on a flat regular model,

$$
(H_i\cdot\mathcal X_k)=\deg(P_i),
$$

follows from computing the divisor of $\pi$ restricted to the curve $H_i$, which has degree equal to the generic degree. Since the reduction meets no component other than $\Gamma_i$,

$$
m_i(H_i\cdot\Gamma_i)=\sum_jm_j(H_i\cdot\Gamma_j)=\deg(P_i)=m_i,
$$

and hence $(H_i\cdot\Gamma_j)=\delta_{ij}$. $\square$

**Proof of Theorem 10.2.** A generic-degree-zero line bundle has multidegree $d$ with $\sum m_id_i=0$, by intersecting its divisor with the principal whole fiber. Conversely every $d\in\Lambda$ occurs. Work over the strict henselization and choose for each $i$ a point $x_i$ of $\Gamma_i$ that is regular in the total space and lies on no other component; such points exist because $\Gamma_i$ has finitely many crossings. Lemma 10.2A supplies an effective horizontal Cartier divisor $H_i$ meeting $\Gamma_i$ once, at $x_i$, and no other component. Its generic degree is therefore $m_i$. Then the signed divisor $\sum_i d_iH_i$ has intersection vector $d$ and generic degree $\sum_i m_id_i=0$. This proves realization; descent replaces a point by its finite Galois-orbit sum when necessary.

Twisting by $\sum a_j\Gamma_j$ changes multidegree by $M(a)$. Lemma 9.1 shows that these, and only these, are the generically trivial twists killed in the Raynaud quotient. Each fixed multidegree chart has the same connected identity group after smoothening, so the remaining connected components are exactly $\Lambda/M(\mathbf Z^I)$. Lemma 10.1 makes the quotient finite, and the construction is invariant under the residue Galois action. $\square$

Equivalently, $\Phi_J(k^s)$ is the torsion in the cokernel of the intersection matrix. Smith normal form, rather than the determinant alone, gives its invariant factors.

### 10.3 Specialization of divisor classes

For a degree-zero divisor $D$ whose closure meets the fiber smoothly, put

$$
\rho(D)=((\overline D\cdot\Gamma_i))_i\in\Lambda. \tag{10.6}
$$

If $D=\operatorname{div}(f)$, then $\operatorname{div}_{\mathcal X}(f)=\overline D+\sum a_i\Gamma_i$, so $\rho(D)=-M(a)$. Therefore

$$
J(K^{\mathrm{sh}})\longrightarrow\Lambda/M(\mathbf Z^I) \tag{10.7}
$$

is the component map. If $P,Q$ specialize on $\Gamma_i,\Gamma_j$, then $c_J([P-Q])=[e_i-e_j]$. A nonrational closed point contributes its full Galois-orbit sum.

Solving $M(a)=-\rho(D)$ over $\mathbf Q$ gives a vertical correction orthogonal to every component. It is integral exactly when the component class vanishes.

### 10.4 Nonreduced fibers and the index

The weights $m_i$ cannot be omitted. Every horizontal divisor satisfies

$$
\deg(D_K)=\sum_im_i(D\cdot\Gamma_i). \tag{10.8}
$$

Thus $\delta=\gcd_i(m_i)$ divides every rational divisor degree. If $C(K)\ne\varnothing$, a section forces $\delta=1$; over a henselian ring with algebraically closed residue field, moving horizontal divisors proves that $\delta$ equals the index. When $\delta>1$, the unsmoothed Picard object can fail cohomological flatness, but the smoothened quotient and formula (10.5) remain valid.

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

Under the principal polarization of a Jacobian, (12.3) is the component-level duality pairing. Our graph convention uses the positive edge-length form $q_n$; the surface intersection matrix is its negative on the corresponding vertical lattice, so formulas written directly with intersections acquire the compensating minus sign. The analogous construction for arbitrary semistable abelian varieties requires the general monodromy pairing developed in the next book; no broader perfection claim is used here.

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

Although $S_s$ is a localization rather than an open subscheme, this still follows from finite presentation. A smooth finite-type test scheme over $\mathcal O_{S,s}$, together with its generic map, descends to some open neighborhood of $s$ in $S$. The global mapping property extends the descended map there, and two choices agree after further shrinking. Passing back to the localization proves the local mapping property; uniqueness identifies the base change with the local Néron model. Reduction type, identity component, and component group are therefore local calculations. Good places contribute no component group.

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
5. For a Jacobian and any regular proper model, $\mathcal J=P^\natural/E$; when the degree-zero Picard object is already smooth, this is $P^{[0]}/E$.
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
