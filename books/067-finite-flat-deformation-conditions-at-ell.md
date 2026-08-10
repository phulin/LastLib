# Finite Flat Deformation Conditions at $\ell$

## Contents

1. [The local deformation problem at the coefficient prime](#1-the-local-deformation-problem-at-the-coefficient-prime)
   - [Why the place above $\ell$ is different](#11-why-the-place-above-ell-is-different)
   - [Fields, coefficients, and residual data](#12-fields-coefficients-and-residual-data)
   - [Four layers of integral information](#13-four-layers-of-integral-information)
   - [Chosen and existential residual hypotheses](#14-chosen-and-existential-residual-hypotheses)
2. [Finite-flat lifts and their invariance](#2-finite-flat-lifts-and-their-invariance)
   - [The definition forced by coefficient change](#21-the-definition-forced-by-coefficient-change)
   - [Strict equivalence](#22-strict-equivalence)
   - [Residual changes of basis](#23-residual-changes-of-basis)
   - [Reduction and arbitrary coefficient base change](#24-reduction-and-arbitrary-coefficient-base-change)
   - [What these invariance results do not say](#25-what-these-invariance-results-do-not-say)
3. [Framed, unframed, and determinant deformation functors](#3-framed-unframed-and-determinant-deformation-functors)
   - [Why three functors are needed](#31-why-three-functors-are-needed)
   - [The unframed finite-flat functor](#32-the-unframed-finite-flat-functor)
   - [The framed functor](#33-the-framed-functor)
   - [Fixed determinant](#34-fixed-determinant)
   - [Chosen-model enhancements](#35-chosen-model-enhancements)
4. [Exact constructions and the boundary of extension closure](#4-exact-constructions-and-the-boundary-of-extension-closure)
   - [The exact model category](#41-the-exact-model-category)
   - [Subobjects and quotients](#42-subobjects-and-quotients)
   - [Direct sums, summands, and coefficient actions](#43-direct-sums-summands-and-coefficient-actions)
   - [Cartier duals and determinant twists](#44-cartier-duals-and-determinant-twists)
   - [Extensions supplied integrally](#45-extensions-supplied-integrally)
   - [Why arbitrary generic extensions do not follow formally](#46-why-arbitrary-generic-extensions-do-not-follow-formally)
5. [The finite-flat tangent space](#5-the-finite-flat-tangent-space)
   - [A tangent vector as a self-extension](#51-a-tangent-vector-as-a-self-extension)
   - [Integral self-extensions and their generic image](#52-integral-self-extensions-and-their-generic-image)
   - [Linearity despite model nonuniqueness](#53-linearity-despite-model-nonuniqueness)
   - [Identification with the tangent functor](#54-identification-with-the-tangent-functor)
   - [Framed and fixed-determinant tangents](#55-framed-and-fixed-determinant-tangents)
6. [Dual tangent conditions](#6-dual-tangent-conditions)
   - [Why ambient local duality is not enough](#61-why-ambient-local-duality-is-not-enough)
   - [The orthogonal condition](#62-the-orthogonal-condition)
   - [What Cartier duality does not prove](#63-what-cartier-duality-does-not-prove)
   - [Self-duality only with a compatible pairing](#64-self-duality-only-with-a-compatible-pairing)
   - [Dimension identities](#65-dimension-identities)
7. [Lifting through small extensions](#7-lifting-through-small-extensions)
   - [Two lifting problems, not one](#71-two-lifting-problems-not-one)
   - [The ambient obstruction](#72-the-ambient-obstruction)
   - [The extra integral obstruction](#73-the-extra-integral-obstruction)
   - [Torsors of lifts and automorphisms](#74-torsors-of-lifts-and-automorphisms)
   - [Formal smoothness criteria and failures](#75-formal-smoothness-criteria-and-failures)
8. [Fiber products and the existential condition](#8-fiber-products-and-the-existential-condition)
   - [Why models need not glue to prove membership](#81-why-models-need-not-glue-to-prove-membership)
   - [The common-ambient closure lemma](#82-the-common-ambient-closure-lemma)
   - [Exact comparison for framed lifts](#83-exact-comparison-for-framed-lifts)
   - [Modelled functors remain different](#84-modelled-functors-remain-different)
   - [Tangent finiteness](#85-tangent-finiteness)
9. [Pro-representability and closed deformation rings](#9-pro-representability-and-closed-deformation-rings)
   - [The framed universal ring](#91-the-framed-universal-ring)
   - [The unframed ring and automorphisms](#92-the-unframed-ring-and-automorphisms)
   - [Why the representing map is a quotient](#93-why-the-representing-map-is-a-quotient)
   - [Complete coefficient rings](#94-complete-coefficient-rings)
   - [Compatible model systems](#95-compatible-model-systems)
10. [Changing the local field](#10-changing-the-local-field)
    - [Restriction and integral base change](#101-restriction-and-integral-base-change)
    - [Unramified base change](#102-unramified-base-change)
    - [Ramified base change and potential finite flatness](#103-ramified-base-change-and-potential-finite-flatness)
    - [Descent data](#104-descent-data)
    - [Tangents under restriction](#105-tangents-under-restriction)
11. [Examples and boundary cases](#11-examples-and-boundary-cases)
    - [Constant groups and roots of unity](#111-constant-groups-and-roots-of-unity)
    - [Ordinary Kummer extensions](#112-ordinary-kummer-extensions)
    - [The uniformizer boundary for fixed endpoints](#113-the-uniformizer-boundary-for-fixed-endpoints)
    - [Good-reduction elliptic curves](#114-good-reduction-elliptic-curves)
    - [Neither unramified nor a generic extension rule](#115-neither-unramified-nor-a-generic-extension-rule)
12. [Standard endpoint models and the Kummer boundary](#12-standard-endpoint-models-and-the-kummer-boundary)
    - [Why the endpoint models are retained](#121-why-the-endpoint-models-are-retained)
    - [Extensions as flat cohomology](#122-extensions-as-flat-cohomology)
    - [Representability and rank of the middle term](#123-representability-and-rank-of-the-middle-term)
    - [Flat Kummer theory over a DVR](#124-flat-kummer-theory-over-a-dvr)
    - [The valuation direction](#125-the-valuation-direction)
    - [The boundary of the conclusion](#126-the-boundary-of-the-conclusion)
13. [Universal rings and dimension bookkeeping](#13-universal-rings-and-dimension-bookkeeping)
    - [From tangent subspaces to minimal presentations](#131-from-tangent-subspaces-to-minimal-presentations)
    - [Obstructions and relation bounds](#132-obstructions-and-relation-bounds)
    - [Framing directions](#133-framing-directions)
    - [Rank two with fixed determinant](#134-rank-two-with-fixed-determinant)
    - [The ambient upper bound and exceptional invariants](#135-the-ambient-upper-bound-and-exceptional-invariants)
    - [Characteristic two](#136-characteristic-two)
14. [Low-ramification rigidity and integral classification](#14-low-ramification-rigidity-and-integral-classification)
    - [The decisive range and the three inputs](#141-the-decisive-range-and-the-three-inputs)
    - [Raynaud full faithfulness](#142-raynaud-full-faithfulness)
    - [Why roots of unity do not contradict rigidity](#143-why-roots-of-unity-do-not-contradict-rigidity)
    - [The covariant divided Fontaine--Laffaille category](#144-the-covariant-divided-fontaine--laffaille-category)
    - [The coefficient-normal-form theorem](#145-the-coefficient-normal-form-theorem)
    - [Why the classification has the stated compatibilities](#146-why-the-classification-has-the-stated-compatibilities)
    - [Coefficient enhancement and coefficient quotients](#147-coefficient-enhancement-and-coefficient-quotients)
    - [Cyclotomic determinant forces type $(0,1)$](#148-cyclotomic-determinant-forces-type-01)
15. [Normal forms, determinant, and the tangent complex](#15-normal-forms-determinant-and-the-tangent-complex)
    - [Splitting the unramified embeddings](#151-splitting-the-unramified-embeddings)
    - [The based normal form and its $5f$ parameters](#152-the-based-normal-form-and-its-5f-parameters)
    - [The single determinant equation](#153-the-single-determinant-equation)
    - [Gauge transformations and generic frames](#154-gauge-transformations-and-generic-frames)
    - [The tangent complex](#155-the-tangent-complex)
    - [The fixed-determinant and framed dimensions](#156-the-fixed-determinant-and-framed-dimensions)
16. [Small extensions and the residual-shape audit](#16-small-extensions-and-the-residual-shape-audit)
    - [Explicit lifting through a small extension](#161-explicit-lifting-through-a-small-extension)
    - [Formal smoothness without ambient $H^2$-vanishing](#162-formal-smoothness-without-ambient-h2-vanishing)
    - [The residual centralizer table](#163-the-residual-centralizer-table)
    - [Irreducible self-twists and the case $\ell=3$](#164-irreducible-self-twists-and-the-case-ell3)
    - [Why equal-character semisimplification is impossible](#165-why-equal-character-semisimplification-is-impossible)
    - [Ordinary Kummer classes: hardly ramified and valuation](#166-ordinary-kummer-classes-hardly-ramified-and-valuation)
    - [Stable-line enhancements are not components](#167-stable-line-enhancements-are-not-components)
17. [The finite-flat local ring package](#17-the-finite-flat-local-ring-package)
    - [The low-weight theorem](#171-the-low-weight-theorem)
    - [The general theorem outside the comparison range](#172-the-general-theorem-outside-the-comparison-range)
    - [A checklist for global deformation data](#173-a-checklist-for-global-deformation-data)
    - [Conclusion](#174-conclusion)

## 1. The local deformation problem at the coefficient prime

### 1.1 Why the place above $\ell$ is different

Away from the residue characteristic, a finite representation extends across a valuation ring precisely when the relevant inertia is absent: finite groups of invertible order are étale, and étale objects are rigid over a henselian discrete valuation ring. At a place above $\ell$, that principle stops being an adequate guide. The generic fiber is still étale because the local field has characteristic zero, but the special fiber of an $\ell$-power-order model may be connected and nonreduced. Ramification of the generic representation can therefore be the visible trace of perfectly good integral geometry.

The simplest witness is $\mu_\ell$. Over a field of characteristic zero it has $\ell$ distinct geometric points, acted on through the mod-$\ell$ cyclotomic character. Over a residue field of characteristic $\ell$, all those points meet at the identity. The model is finite locally free of rank $\ell$ throughout. Thus the representation is generally ramified, yet it satisfies the integral condition that matters at $\ell$.

Deformation theory asks whether this phenomenon persists when the coefficient field is thickened to an Artinian local ring. The resulting condition has three jobs. It must be intrinsic—independent of a matrix presentation. It must survive coefficient reduction and gluing. Finally, it must have a tangent and obstruction theory precise enough to enter a global deformation problem. Each job is complicated by the fact that a generic representation may possess several nonisomorphic integral models.

This book develops those three jobs in that order. We first define
finite-flat lifts and establish their invariance. We then extract the integral
part of the ordinary cohomological tangent space. The decisive formal result
is that the existential framed condition is pro-representable: coefficient
fiber products can be modeled by closing one generic fiber product inside
the product of two supplied models. This argument needs neither uniqueness
nor a classification of models. We then state the established low-weight
integral classification over unramified bases for $\ell>2$, explain the
infrastructure on which it rests, and use it to establish
formal smoothness and the exact rank-two type-$(0,1)$ dimension. The final
ordinary Kummer chart makes the reducible boundary explicit.

### 1.2 Fields, coefficients, and residual data

Fix a prime $\ell$ and a finite extension

$$
K/\mathbf Q_\ell.
$$

Write

$$
R=\mathcal O_K,\qquad \mathfrak m_K=(\pi),\qquad k_K=R/\mathfrak m_K,
$$

and let $e=e(K/\mathbf Q_\ell)$ and $f=[k_K:\mathbf F_\ell]$. Choose a separable closure $K^s$ and put $G_K=\operatorname{Gal}(K^s/K)$. Because $K$ has characteristic zero, every finite group scheme over $K$ is étale. This mixed-characteristic hypothesis will remain in force unless explicitly stated otherwise.

Let $E/\mathbf Q_\ell$ be a finite extension with ring of integers $\mathcal O$, uniformizer $\varpi$, and finite residue field $k=\mathcal O/\varpi$. The letter $k$ always refers to the coefficient residue field; $k_K$ refers to the residue field of $K$. We work in the category $\operatorname{Art}_{\mathcal O}$ of local Artinian $\mathcal O$-algebras $A$ with specified residue field $k$. Its maximal ideal is $\mathfrak m_A$. Every such $A$ is finite, so all representations into $\operatorname{GL}_d(A)$ are given the discrete topology.

Fix a continuous residual representation

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_d(k),
$$

and let $\bar V=k^d$ with its induced action. A lift over $A$ is a free $A$-module $V_A$ of rank $d$, equipped with a continuous $A$-linear $G_K$-action and an identification $V_A\otimes_Ak\simeq\bar V$. In the fixed residual basis this is a homomorphism $\rho_A:G_K\to\operatorname{GL}_d(A)$ reducing exactly to $\bar\rho$.

The preceding theory enters in five precise forms. Book 48 supplies marked
finite-flat models, saturated closure of a generic subgroup in a fixed
model, represented quotients, coefficient actions, and Cartier duality.
Book 30 supplies finiteness and Euler characteristics for local Galois
cohomology. Book 64 supplies strict equivalence, adjoint tangent spaces, and
the complete matrix obstruction across a small extension. Book 65 supplies
the fiber-product criteria for hulls and universal rings. In the
unramified low-weight range, Book 59 supplies the exact contravariant
Fontaine--Laffaille anti-equivalence, unramified base change, and the
admissible-annihilator construction for nonflat coefficient quotients. The
chapters below recall each hypothesis at its point of use and prove the new
finite-flat deformation statements from these inputs.

The adjoint module is

$$
\operatorname{ad}\bar\rho=\operatorname{End}_k(\bar V),
\qquad g\cdot X=\bar\rho(g)X\bar\rho(g)^{-1}.
$$

When a determinant is fixed and $\ell\nmid d$, its linearized coefficient module is

$$
\operatorname{ad}^0\bar\rho=\ker(\operatorname{tr}:\operatorname{ad}\bar\rho\to k).
$$

The qualification $\ell\nmid d$ matters when passing from framed to ordinary fixed-determinant tangents. In the two-dimensional applications below we assume $\ell$ odd, so trace splits and no characteristic-two anomaly is hidden.

Two routine-looking conventions carry real mathematical content. First, $A$ is a coefficient ring, whereas $R$ is the base of the group scheme. There is usually no ring map $A\to R$. An $A$-action therefore means endomorphisms of the group object, not scalar multiplication on its coordinate algebra as an $R$-module. Second, freeness is imposed on the generic $A$-module $V_A$. The coordinate ring of its model has $R$-rank $|A|^d$, but it is not an $A$-module of rank $d$ in any literal coordinate-algebra sense.

For example, over $A=k[\epsilon]$ a rank-$d$ lift has $|k|^{2d}$ generic points. The endomorphism $\epsilon$ of its model is square zero, and its generic image and kernel both have $|k|^d$ points. Flatness of their raw scheme-theoretic image and kernel is not automatic; saturated closure is what recovers the two residual layers. This elementary example foreshadows why the tangent condition must be phrased in the exact model category.

### 1.3 Four layers of integral information

The theory is reliable only if four objects are kept apart.

$$
\begin{array}{c|l}
\text{layer}&\text{datum}\\ \hline
\text{representation}&V_A\text{ with its }A[G_K]\text{-module structure},\\
\text{chosen model}&(\mathcal G_A,\iota_A,\alpha_A),\\
\text{existence}&\text{at least one such model exists},\\
\text{uniqueness}&\text{all such models are uniquely isomorphic over the generic fiber}.
\end{array}
$$

Here $\mathcal G_A$ is a finite locally free commutative $R$-group scheme, $\alpha_A:A\to\operatorname{End}_R(\mathcal G_A)$ is a coefficient action, and $\iota_A$ identifies its generic geometric points with $V_A$. Finite local freeness concerns the coordinate algebra over $R$; it does not say that $\mathcal G_A$ is a vector bundle or an affine-space module scheme. The $A$-action is a ring of group-scheme endomorphisms.

The representation determines its finite étale generic group, but it need not determine an integral Hopf lattice. For example, if $K$ contains $\mu_\ell$, the constant group $\underline{\mathbf Z/\ell\mathbf Z}$ and $\mu_\ell$ have isomorphic generic fibers but nonisomorphic special fibers. One is étale and the other is connected. A statement proved using one model cannot silently be transferred to the other.

There is, however, an important intermediate uniqueness. If a generic subgroup is embedded in a fixed finite-flat ambient model, its schematic closure is the unique finite-flat subgroup of that ambient model with the prescribed generic fiber. Much of the exact calculus below rests on this ambient uniqueness rather than on uniqueness of the ambient model itself.

### 1.4 Chosen and existential residual hypotheses

We will use two versions of the initial condition.

The **chosen-model datum** consists of a $k$-linear finite-flat model

$$
(\overline{\mathcal G},\bar\iota,\bar\alpha)
$$

of $\bar V$. A lift with chosen reduction model will be required to reduce, in the exact model sense, to this particular object. This version has a cleaner obstruction theory because one knows which integral point is being thickened.

The **existential residual hypothesis** merely says that $\bar V$ admits some $k$-linear finite-flat model. It is basis independent and is the condition normally imposed on a residual representation. It is weaker data. If models are nonunique, the existential deformation problem is the image of a groupoid of modelled lifts, not the deformation theory of one distinguished integral object.

Neither version should be confused with choosing only a model of the underlying abelian group. A generic $A$-action need not extend to an arbitrary selected model, because the generic-fiber functor is not full. What is true is existential: the product-and-closure construction in §2.1 produces some $A$-linear model whenever the underlying finite Galois module has a finite-flat model.

It is useful to picture the forgetful maps as

$$
\{\text{modelled framed lifts}\}
\longrightarrow
\{\text{framed lifts}\}
\longrightarrow
\{\text{strict-equivalence classes}\}.
$$

The first arrow forgets an integral lattice; the second forgets a basis lifting the residual basis. The first can have several disconnected fibers even when the second is well behaved. The second is governed by matrix centralizers; the first is governed by integral automorphisms and model comparison. Keeping these two sources of ambiguity separate will make the later Schlessinger argument transparent.

## 2. Finite-flat lifts and their invariance

### 2.1 The definition forced by coefficient change

A deformation condition must be stable under every morphism of Artinian coefficient rings. This requirement dictates that coefficients act on the integral model itself. Merely asking the underlying abelian representation to be the generic fiber of a group scheme would leave no functorial way to interpret a quotient $A\to B$.

**Definition 2.1 (finite-flat lift).** Let $A\in\operatorname{Art}_{\mathcal O}$ and let $V_A$ be a free rank-$d$ $A$-module with continuous $A$-linear $G_K$-action. An **$A$-linear finite-flat model** of $V_A$ is a triple $(\mathcal G_A,\iota_A,\alpha_A)$ where

- $\mathcal G_A$ is a finite locally free commutative group scheme over $R$;
- $\alpha_A:A\to\operatorname{End}_R(\mathcal G_A)$ is a unital ring homomorphism;
- $\iota_A:\mathcal G_A(K^s)\xrightarrow{\sim}V_A$ is an $A[G_K]$-linear isomorphism.

The lift $V_A$, or its matrix presentation $\rho_A$, is **finite flat** if such a model exists.

Since $V_A$ is free of rank $d$, every model has rank $|A|^d$ over $R$. Its generic fiber is automatically finite étale. The action convention is covariant: $a\in A$ acts as multiplication by $a$ on generic points. The adjective “finite flat” always includes finite presentation, hence finite local freeness over the DVR.

The definition is existential. The set-valued deformation functor below remembers $\rho_A$ but forgets which $\mathcal G_A$ proves the condition. We will explicitly restore the model when a construction requires it.

The coefficient action is real extra structure on a chosen model, but it does not strengthen the existential property.

**Coefficient-saturation lemma.** Suppose the underlying finite abelian $G_K$-module of $V_A$ has a finite-flat model $\mathcal G$, without a selected $A$-action. Then $V_A$ has an $A$-linear finite-flat model.

**Proof.** Form the finite product

$$
\mathcal P=\prod_{a\in A}\mathcal G.
$$

On generic points embed $V_A$ by

$$
j(v)=(av)_{a\in A}.
$$

The coordinate indexed by $1$ shows that $j$ is injective. Let $\mathcal H$ be the schematic closure of $j(V_A)$ in $\mathcal P$; saturation over the DVR makes $\mathcal H$ finite flat with generic module $V_A$.

For $b\in A$, define an endomorphism $T_b$ of $\mathcal P$ by

$$
(T_bx)_a=x_{ab}.
$$

It sends $j(v)$ to $j(bv)$, so it preserves $\mathcal H$. On the generic fiber of $\mathcal H$, the identities

$$
T_{b+c}=T_b+T_c,\qquad
T_{bc}=T_bT_c,qquad T_1=1
$$

hold because they are the corresponding scalar identities on $V_A$. Generic-fiber faithfulness makes them hold on $\mathcal H$. Hence $b\mapsto T_b|_{\mathcal H}$ is the required action. $\square$

This proof does not claim that any scalar extends to the original $\mathcal G$. It replaces $\mathcal G$ by a saturated closure in a larger ambient product. The resulting group has rank $|V_A|=|A|^d$, not the much larger rank of $\mathcal P$.

### 2.2 Strict equivalence

Strict equivalence is conjugacy by

$$
\Gamma_A=\ker(\operatorname{GL}_d(A)\to\operatorname{GL}_d(k)).
$$

Suppose $\rho_A'$ is obtained from $\rho_A$ by $P\in\Gamma_A$. The matrix $P$ is an $A[G_K]$-isomorphism from the module of $\rho_A$ to that of $\rho_A'$. If $(\mathcal G_A,\iota_A,\alpha_A)$ models the first, then

$$
(\mathcal G_A,P\circ\iota_A,\alpha_A)
$$

models the second. No extension of $P$ as a new endomorphism of $\mathcal G_A$ is required: $P$ is used only to change the generic identification. Thus finite flatness is invariant under strict equivalence.

This elementary proof is worth isolating. A common but unsafe alternative is to claim that every generic change of basis extends to a fixed model. Generic fullness is false at residue-characteristic torsion. Transporting the identification proves invariance without making that false assertion.

### 2.3 Residual changes of basis

Let $S\in\operatorname{GL}_d(k)$ and put $\bar\rho^S=S\bar\rho S^{-1}$. Choose a lift $\widetilde S\in\operatorname{GL}_d(\mathcal O)$, or separately in each test ring. Conjugation gives an isomorphism between the deformation problems of $\bar\rho$ and $\bar\rho^S$. Different lifts of $S$ differ by a strict matrix, so they induce the same map on unframed classes.

On modules, this is simply transport across the residual isomorphism $S:\bar V\to\bar V^S$. The same generic-identification argument proves:

**Proposition 2.2.** Finite flatness of residual representations and of their lifts is invariant under change of residual basis. The induced bijection of unframed finite-flat deformation functors is canonical up to the unique natural identification supplied by strict equivalence.

For framed functors, a residual basis is part of the datum. A change of residual basis identifies two framed problems but is not an automorphism of one fixed framed problem. This is exactly the same distinction as for unrestricted deformations.

### 2.4 Reduction and arbitrary coefficient base change

Let $A\to B$ be a morphism of finite coefficient rings and suppose $V_A$ is finite flat. At the generic level the new module is

$$
V_B=B\otimes_AV_A.
$$

To construct its model safely, choose a finite presentation $A^m\twoheadrightarrow B$. It induces a surjection $V_A^m\twoheadrightarrow V_B$ with $G_K$-stable kernel $N$. Start from $\mathcal G_A^m$, close the generic subgroup attached to $N$ inside it, and take the represented finite-flat quotient $\mathcal Q$.

For $b\in B$, multiplication by $b$ on the finite $A$-module $B$ lifts, after choosing images of the standard basis, to an $A$-linear endomorphism of $A^m$. Tensoring with $V_A$ gives a matrix of scalar endomorphisms of $\mathcal G_A^m$. Its generic map preserves $N$, so its integral map preserves the saturated closure of $N$ and descends to $\mathcal Q$. Different lifts induce the same endomorphism on the generic quotient and hence the same endomorphism of $\mathcal Q$ by generic-fiber faithfulness. Addition, multiplication, and the unit law for these endomorphisms hold generically and therefore integrally. They give the required $B$-action. The generic fiber is $V_B$, so $\mathcal Q$ has rank $|V_B|=|B|^d$.

This proves more than flat coefficient extension.

**Theorem 2.3 (coefficient base change).** If $V_A$ is finite flat, then $B\otimes_AV_A$ is finite flat for every homomorphism of finite commutative coefficient rings $A\to B$.

For a quotient $B=A/I$, the construction is especially transparent. Close the generic subgroup $IV_A\subset V_A$ in a chosen model and quotient. One must not replace this saturated closure by a raw scheme-theoretic image of $I$, which can have vertical torsion and fail to be flat.

Taking $B=k$ proves compatibility with residual reduction. In particular every finite-flat lift reduces to a finite-flat residual representation. Composition is functorial at the level of the existential predicate, because both iterated and direct scalar extension model canonically isomorphic generic modules. At the chosen-model level the resulting integral models need not be canonically identical unless one fixes compatible presentations or works in the model groupoid.

Here is the quotient case in more detail. Let $B=A/I$ and let $\mathcal G$ model $V_A$. The generic subgroup $IV_A$ is stable under $A$ and under $G_K$. Its closure $\mathcal I$ in $\mathcal G$ is therefore stable under every scalar endomorphism: for $a\in A$, the two maps from $\mathcal I$ to $\mathcal G$ obtained by inclusion followed by $a$ and by the restriction of $a$ agree on the generic fiber, hence agree integrally. The quotient $\mathcal G/\mathcal I$ exists and is finite flat. Every $i\in I$ acts trivially on its generic fiber, and faithfulness forces it to act trivially on the whole quotient. The action therefore factors through $B$. This argument simultaneously proves flatness, the coefficient relation, and independence from representatives of $B$.

For a non-surjective $A\to B$, a free presentation of $B$ is not canonical. Suppose two presentations give models $\mathcal Q$ and $\mathcal Q'$. They need not be canonically isomorphic as integral groups, but both have generic module $B\otimes_AV_A$. Since the deformation condition records existence, this is enough. If later work needs a chosen scalar-extension model, the presentation and the comparison data must be retained. Functoriality of the set-valued predicate should not be upgraded to functoriality of a silently selected model.

### 2.5 What these invariance results do not say

The preceding theorems establish the properties needed to define a subfunctor, but no more.

They do not select a canonical model of a lift. They do not imply that a model over $B$ descends along $A\to B$. They do not make the generic-fiber functor full. They do not say that formation of the chosen model commutes strictly with every coefficient fiber product. Finally, they do not imply that the existential finite-flat locus is closed in an ambient deformation space.

These omissions are substantive. Base change is an operation on a supplied model; descent requires integral descent data. Closedness is a compactness statement about all possible models, and fiber-product gluing must reconcile their reductions. Both issues return later.

## 3. Framed, unframed, and determinant deformation functors

### 3.1 Why three functors are needed

The finite-flat condition constrains the representation, not the manner in which bases are forgotten. Consequently it can be imposed on each of the standard deformation problems. The framed problem is technically clean because it is a set of matrix homomorphisms. The unframed problem is intrinsic but retains strict automorphisms in the background. Fixing a determinant removes a one-dimensional character direction, provided the prescribed determinant has been chosen compatibly over the coefficient base.

No new equivalence relation should be invented for finite flatness. In particular, two lifts are not declared equivalent merely because some choices of their integral models are isomorphic. They are equivalent exactly when their representations are strictly conjugate. Models witness membership in the condition; they do not redefine the ambient notion of deformation.

### 3.2 The unframed finite-flat functor

Define

$$
D_{\bar\rho}^{\mathrm{fl}}(A)=
\{\text{finite-flat lifts }\rho_A\text{ of }\bar\rho\}/\text{strict equivalence}.
$$

Proposition 2.2 makes this well defined, and Theorem 2.3 gives its action on a map $A\to B$. Thus it is a covariant subfunctor

$$
D_{\bar\rho}^{\mathrm{fl}}\subseteq D_{\bar\rho}.
$$

At $k$ it has one point precisely when $\bar\rho$ is finite flat. If the residual representation is not finite flat, the functor is empty on every coefficient ring, because reduction preserves finite flatness. Hence all deformation-theoretic discussion assumes the existential residual hypothesis.

The definition depends only on the $k[G_K]$-module $\bar V$ with its residual identification, not on a chosen model. This is the version that naturally becomes a local condition in a global problem.

Functoriality can be checked on a composable pair $A\to B\to C$. The representation obtained in one step is canonically

$$
C\otimes_A V_A\simeq C\otimes_B(B\otimes_AV_A).
$$

Theorem 2.3 shows that both are finite flat. Strict equivalence is preserved by applying coefficient maps entrywise. Hence the two induced maps on deformation classes agree exactly, even though the witness models built from two different presentations may not. This is an instructive instance in which a functor of properties exists more canonically than a functor of witnesses.

### 3.3 The framed functor

The framed finite-flat functor is

$$
D_{\bar\rho}^{\square,\mathrm{fl}}(A)=
\{\rho_A:G_K\to\operatorname{GL}_d(A):
\rho_A\bmod\mathfrak m_A=\bar\rho, \rho_A\text{ finite flat}\}.
$$

There is no quotient. Its forgetful map to $D_{\bar\rho}^{\mathrm{fl}}$ has fibers equal to congruence-group orbits, with stabilizers the strict centralizers of the lifted representation. Adding a finite-flat model to a framed representation is still additional data: the frame rigidifies the generic module, not the integral Hopf lattice.

Framing is especially valuable in representability arguments. Matrices glue exactly over coefficient fiber products, whereas unframed classes glue only after controlling comparison automorphisms. It does not, by itself, solve model nonuniqueness.

### 3.4 Fixed determinant

Fix a continuous character

$$
\delta:G_K\longrightarrow\mathcal O^\times
$$

whose reduction is $\det\bar\rho$. Let $\delta_A$ denote its specialization to $A$. Define

$$
D_{\bar\rho}^{\mathrm{fl},\delta}(A)
=\{[\rho_A]\in D_{\bar\rho}^{\mathrm{fl}}(A):
\det\rho_A=\delta_A\},
$$

and similarly $D_{\bar\rho}^{\square,\mathrm{fl},\delta}$. Determinant is invariant under every conjugation, so strict conjugators are not required to have determinant one.

At first order the determinant condition is trace zero. When $\ell\nmid d$, the scalar line splits from the adjoint module and the unframed tangent naturally lies in $H^1(K,\operatorname{ad}^0\bar\rho)$. When $\ell\mid d$, the correct tangent is

$$
\ker\bigl(H^1(K,\operatorname{ad}\bar\rho)
\xrightarrow{\operatorname{tr}}H^1(K,k)\bigr),
$$

not automatically $H^1(K,\operatorname{ad}^0\bar\rho)$. We retain this caveat even though the main two-dimensional theorem assumes $\ell$ odd.

### 3.5 Chosen-model enhancements

Fix a residual model $\overline{\mathcal G}$. One may define a groupoid whose objects over $A$ are finite-flat lifts together with a selected $A$-linear model and an identification of its coefficient reduction with $\overline{\mathcal G}$. Arrows are integral model isomorphisms compatible with the generic frame and the residual identification. Denote it schematically by

$$
\mathfrak D_{\bar\rho,\overline{\mathcal G}}^{\mathrm{fl}}(A).
$$

The notation is deliberately groupoid-valued. A model can have integral automorphisms, and forgetting the model can identify different objects. Its connected components map to $D_{\bar\rho}^{\mathrm{fl}}(A)$, but the map need be neither injective nor surjective if the reduction model is fixed too rigidly.

The enhanced problem is nevertheless the correct place to formulate integral obstructions. The existential problem is recovered only after taking the union of the images over residual model classes, or after a uniqueness theorem proves that there is just one class.

One can also retain less data. For example, an ordinary deformation problem may remember only a multiplicative subgroup model and not the entire middle model. Such an intermediate enhancement is a separate moduli problem. Forgetting the subgroup can fail to be injective when two ordinary lines specialize to the same residual line. Thus every auxiliary structure should be recorded at the level where it is used and forgotten only after its image has been analyzed.

## 4. Exact constructions and the boundary of extension closure

### 4.1 The exact model category

Fix a finite coefficient ring $A$. Consider finite locally free commutative $R$-group schemes with $A$-action and étale generic fiber. The appropriate short exact sequences are

$$
0\longrightarrow\mathcal G_1\longrightarrow\mathcal G
\longrightarrow\mathcal G_2\longrightarrow0
$$

in which the first map identifies the scheme-theoretic kernel and the second is faithfully flat, equivalently $\mathcal G_2$ represents the faithfully flat quotient. These sequences remain exact after arbitrary base change, and their generic geometric points form exact sequences of $A[G_K]$-modules.

This is an exact category, not an abelian category. A raw scheme-theoretic kernel of an arbitrary morphism can acquire a special-fiber component and fail to be flat. Likewise, a closure of the generic image need not be the faithfully flat image of the original map. The declared exact sequences are precisely those for which the integral and generic exact structures agree.

Rank provides a quick diagnostic but not a proof of exactness. In an admissible sequence,

$$
|\mathcal G|=|\mathcal G_1|\,|\mathcal G_2|.
$$

If a morphism is generically an isomorphism between groups of equal rank but collapses something on the special fiber, its raw kernel has generic rank one and a larger special fiber; it cannot be flat. Rank constancy detects the failure, while the saturated generic kernel discards the vertical component and returns the correct finite-flat subobject.

### 4.2 Subobjects and quotients

Let $\mathcal G$ model $V$ and let $W\subseteq V$ be an $A[G_K]$-submodule. The corresponding finite étale generic subgroup has a schematic closure $\mathcal H\subseteq\mathcal G$. On coordinate rings, contraction of the generic Hopf ideal makes the quotient torsion free; over the DVR $R$, finite torsion-free modules are free. Hence $\mathcal H$ is finite flat. Its uniqueness inside $\mathcal G$ follows from saturation.

Because $W$ is stable under $A$, every scalar endomorphism preserves $\mathcal H$ generically and therefore integrally. The represented quotient $\mathcal G/\mathcal H$ inherits an $A$-action and models $V/W$. We obtain:

**Proposition 4.1.** Finite-flat coefficient modules are closed under $G_K$-stable submodules and quotients. Given an ambient model, the submodel is its unique saturated closure and the quotient model is then determined.

The final phrase is relative to the ambient model. A different model of $V$ can induce a different model of $W$.

The same construction treats filtrations. Given

$$
0=W_0\subset W_1\subset\cdots\subset W_r=V,
$$

close every $W_i$ in one ambient model $\mathcal G$. Saturation makes the inclusions compatible, and successive represented quotients model $W_i/W_{i-1}$. This is much stronger than separately choosing models of the graded pieces: it remembers how the pieces meet in the special fiber. Ordinary finite-flat representations use exactly such a two-step filtration.

### 4.3 Direct sums, summands, and coefficient actions

Products of finite-flat commutative groups are finite flat, and for a finite family products and direct sums agree. Thus $V_1\oplus V_2$ is finite flat whenever both summands are. Conversely, a direct summand of a finite-flat module is a stable submodule, so Proposition 4.1 applies.

Idempotents illustrate the safe method. If $e\in\operatorname{End}_{A[G_K]}(V)$, one should not assert that the raw image of an extension of $e$ is flat—there may not even be an extension of $e$ to the chosen model. Instead close $eV$ in the ambient model and take the complementary generic submodule in the same way. The two closures give finite-flat models of the summands; only in a rigid setting must they split the original integral model.

Restriction of coefficient scalars merely forgets some endomorphisms. Extension of coefficients uses the closure-and-quotient construction of §2.4. These two operations concern the coefficient ring and must not be confused with extending the local field, which changes the valuation ring and the acting Galois group.

### 4.4 Cartier duals and determinant twists

Suppose $V$ is killed by $n$. Since $K$ has characteristic zero, $n$ is invertible in $K$, and Cartier duality sends a chosen model $\mathcal G$ to a model $\mathcal G^D$ of

$$
V^*(1)=\operatorname{Hom}(V,\mu_n(K^s)).
$$

The coefficient action becomes contragredient; commutativity of $A$ removes the order reversal. Duality reverses finite-flat exact sequences and carries closures to annihilators inside the dual ambient model.

For a rank-two free $A$-module, a perfect alternating pairing

$$
V_A\times V_A\longrightarrow A(1)
$$

identifies $V_A$ with $V_A^*(1)$ and forces $\det V_A$ to be cyclotomic. But the generic pairing alone need not extend to arbitrary chosen models. A self-dual integral statement requires a perfect Cartier pairing on the model, as occurs for torsion of a polarized abelian scheme. Nor does general Cartier duality construct exterior powers. Determinant conditions remain separate deformation data unless an integral pairing supplies them.

### 4.5 Extensions supplied integrally

An extension of models

$$
0\to\mathcal G_1\to\mathcal G\to\mathcal G_2\to0
$$

has a finite-flat middle term and produces a generic extension

$$
0\to V_1\to V\to V_2\to0.
$$

Pullback, represented pushout, and Baer sum remain inside the exact category whenever they are formed using finite-flat subgroups and represented quotients. Thus the image of integral extension classes in generic $\operatorname{Ext}^1$ is an additive subgroup. Coefficient scalars act by pushout on the subobject or pullback on the quotient, making the image a module over the appropriate coefficient field.

To see the Baer sum geometrically, begin with two extensions of $\mathcal G_2$ by $\mathcal G_1$. Their product is an extension of $\mathcal G_2\times\mathcal G_2$ by $\mathcal G_1\times\mathcal G_1$. Pull back along the diagonal of the quotient and push out along addition on the kernel. Every arrow named here exists in the exact category: the pullback of a faithfully flat quotient is faithfully flat, and the pushout is the represented quotient by the anti-diagonal kernel. This construction proves additivity before any passage to generic cohomology.

The inverse extension is obtained by pushing out along $-1$ on the subobject. The split extension is the product. Hence the isomorphism classes of extensions with fixed endpoint models form an abelian group. When endpoint models vary, the generic images still form a group because all constructions can be carried out after taking direct sums, as in the tangent proof below.

Conversely, if the generic middle term $V$ already has a model, closing $V_1$ inside that model recovers an integral exact sequence. This useful converse begins with a model of the middle term, not merely models of the two endpoints.

### 4.6 Why arbitrary generic extensions do not follow formally

Separate finite-flat models of $V_1$ and $V_2$ do not, by the exact constructions alone, produce a model for every class in

$$
\operatorname{Ext}^1_{A[G_K]}(V_2,V_1)
$$

The missing datum is an integral middle term. This is not a technical nuisance; it is the source of the tangent restriction.

For a concrete preview, take $K=\mathbf Q_\ell$ with $\ell>2$. Both $k(1)$ and the trivial line $k$ have the models $\mu_\ell$ and $\underline{\mathbf Z/\ell\mathbf Z}$. Kummer theory identifies

$$
H^1(K,k(1))\simeq K^\times/(K^\times)^\ell.
$$

Extensions coming from units have integral finite-flat realizations between the standard multiplicative and constant endpoint models. The class of a uniformizer does not arise from an extension of those two selected models. Chapter 12 proves this directly by flat Kummer theory. This is a counterexample to closure under arbitrary generic extensions in a fixed endpoint-model category. It is not, by itself, a proof that the middle representation has no other finite-flat model; that stronger conclusion would require an independent rigidity theorem for its induced endpoint models.

The correct slogan is therefore one-directional: finite-flat representations are closed under subquotients of a supplied finite-flat middle term and under extensions supplied in the exact integral category. No closure under arbitrary generic extensions follows from separate endpoint models. In a fixed endpoint category, the Kummer calculation shows that such closure can fail.

## 5. The finite-flat tangent space

### 5.1 A tangent vector as a self-extension

Let $k[\epsilon]=k[\epsilon]/(\epsilon^2)$. Every lift of $\bar\rho$ to the dual numbers has a unique expression

$$
\rho_\epsilon(g)=(1+\epsilon c(g))\bar\rho(g).
$$

Multiplicativity says that $c$ is a continuous cocycle with values in $\operatorname{ad}\bar\rho$, and strict conjugation changes $c$ by a coboundary. Thus the ambient unframed tangent space is $H^1(K,\operatorname{ad}\bar\rho)$.

There is another description which is better suited to integral geometry. Regard $V_\epsilon$ as a $k[G_K]$-module. Multiplication by $\epsilon$ gives an exact sequence

$$
0\longrightarrow\epsilon V_\epsilon
\longrightarrow V_\epsilon
\longrightarrow V_\epsilon/\epsilon V_\epsilon
\longrightarrow0.
$$

Freeness over $k[\epsilon]$ identifies both endpoints with $\bar V$, and the extension class is exactly $[c]\in\operatorname{Ext}^1_{k[G_K]}(\bar V,\bar V)$. Conversely, a self-extension becomes a free $k[\epsilon]$-module when $\epsilon$ is defined as inclusion followed by projection. This is the familiar equivalence between first-order deformations and self-extensions.

The integral tangent problem is now visible: which self-extensions admit a compatible exact sequence of finite-flat models?

The cocycle and extension descriptions agree concretely. Choose the obvious $k$-linear section of $V_\epsilon\to\bar V$. Its failure to be $G_K$-equivariant is measured by $\epsilon c(g)$. Replacing the section by one differing through an endomorphism $X$ changes $c$ by the coboundary $gXg^{-1}-X$. No choice survives in the extension class. An integral splitting would be much stronger: it would require a morphism of finite-flat groups, and generic fullness does not provide one. The tangent condition asks for an integral extension, not an integral splitting.

### 5.2 Integral self-extensions and their generic image

An **integral finite-flat self-extension** of $\bar V$ consists of a finite-flat exact sequence

$$
0\longrightarrow\mathcal G_1\xrightarrow{i}\mathcal H
\xrightarrow{q}\mathcal G_0\longrightarrow0,
$$

generic identifications of $\mathcal G_0$ and $\mathcal G_1$ with $\bar V$, and a $k[\epsilon]$-action on $\mathcal H$ for which

$$
\epsilon=i\circ u\circ q
$$

with $u:\mathcal G_0\to\mathcal G_1$ inducing the identity of $\bar V$ generically. Faithfulness forces $u$ to be unique if it exists. Equivalently, one may require directly that the generic points of $\mathcal H$ form a free $k[\epsilon]$-module of rank $d$ and that the integral $k[\epsilon]$-action realizes it.

Taking generic fibers sends such an object to a class in $H^1(K,\operatorname{ad}\bar\rho)$. We define

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
$$

to be the set of generic cohomology classes arising in this way, allowing all endpoint models compatible with $\bar V$. This is the existential finite-flat tangent condition.

If a residual model $\overline{\mathcal G}$ is fixed, define

$$
H^1_{\mathrm{fl},\overline{\mathcal G}}
(K,\operatorname{ad}\bar\rho)
$$

by requiring $\mathcal G_0=\mathcal G_1=\overline{\mathcal G}$ with the displayed generic identifications. This chosen-model subspace can be strictly smaller than the existential one. Equality follows from a uniqueness theorem for residual models, but should not otherwise be presumed.

The coefficient endomorphism $\epsilon$ is essential. A finite-flat exact sequence with generic endpoints isomorphic to $\bar V$ need not by itself realize a free dual-number module: the two copies must be identified so that multiplication by $\epsilon$ is quotient, followed by that identification, followed by inclusion. Dropping this compatibility would define a larger extension space with independently chosen endpoints.

### 5.3 Linearity despite model nonuniqueness

At first sight the existential image could be a mere union of subspaces indexed by models. The exact closure calculus shows that it is actually a $k$-linear subspace.

**Theorem 5.1.** The subset

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
\subseteq H^1(K,\operatorname{ad}\bar\rho)
$$

is a $k$-linear subspace.

**Proof strategy.** Construct Baer sums without identifying the endpoint models. Put two integral middle terms into one direct-sum ambient model, perform the generic pullback and pushout there, and use saturated closure and represented quotient to keep every intermediate object finite flat.

**Proof.** The split self-extension has the product model, so zero is present. Suppose $\xi_1$ and $\xi_2$ are represented by finite-flat $k[\epsilon]$-linear middle terms $\mathcal H_1$ and $\mathcal H_2$. Their direct product models the direct sum of the two generic self-extensions. The Baer sum first pulls back along the diagonal

$$
\bar V\longrightarrow\bar V\oplus\bar V
$$

on the quotient side. Close the resulting generic fiber product inside $\mathcal H_1\times\mathcal H_2$. Next push out the subobject $\bar V\oplus\bar V$ along addition. This is achieved by closing the generic kernel of addition and taking the represented quotient. The coefficient action preserves every generic subgroup involved, hence every closure. The resulting finite-flat middle term has generic class $\xi_1+\xi_2$.

For $a\in k$, scalar multiplication of a class is the pushout along $a:\bar V\to\bar V$ on the subobject. Perform the same closure-and-quotient construction inside a supplied model. It gives an integral representative of $a\xi$. Therefore the image is closed under addition and scalar multiplication. $\square$

This proof is stronger than the assertion that each chosen-model image is a subspace. It explains why varying endpoint models does not destroy linearity: two choices can always be compared inside a larger direct-sum ambient object, where closure is unique.

### 5.4 Identification with the tangent functor

**Theorem 5.2 (finite-flat tangent theorem).** Under the canonical ambient identification

$$
D_{\bar\rho}(k[\epsilon])\simeq
H^1(K,\operatorname{ad}\bar\rho),
$$

the subset $D_{\bar\rho}^{\mathrm{fl}}(k[\epsilon])$ is exactly

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho).
$$

**Proof strategy.** A finite-flat dual-number lift supplies an exact integral sequence by closing its generic $\epsilon$-multiple. In the reverse direction, the nilpotent endomorphism attached to an integral self-extension supplies the dual-number coefficient action.

**Proof.** Let $\mathcal H$ model a free $k[\epsilon]$-lift. Close the generic subgroup $\epsilon V_\epsilon$ inside $\mathcal H$. The quotient is finite flat, and generic multiplication by $\epsilon$ factors through quotient and subobject. Since the $k[\epsilon]$-action already exists on $\mathcal H$, the resulting exact sequence is an integral self-extension of the required kind.

Conversely, from an integral self-extension define $\epsilon=i\circ u\circ q$. Exactness gives $q\circ i=0$, so $\epsilon^2=0$. Together with the $k$-action this defines a $k[\epsilon]$-action. Its generic module is the free dual-number module corresponding to the extension class. Hence the middle group is a finite-flat model of the first-order lift. The constructions respect generic isomorphism and strict conjugacy. $\square$

The theorem identifies a deformation-theoretic tangent with an image of integral extension classes. It does not assert that every integral model of the middle term reduces to a preselected residual model, nor that the tangent condition alone determines higher-order finite-flatness.

Finite extension of the coefficient field behaves as expected. Scalar extension of an integral self-extension sends $H^1_{\mathrm{fl}}$ into the finite-flat tangent after extending $k$. Conversely, restriction of coefficients and closure of the canonical generic copy recover the original condition. This statement concerns the coefficient field; extension of the local field changes both the valuation ring and the acting Galois group and is treated in Chapter 10.

### 5.5 Framed and fixed-determinant tangents

Let

$$
Z^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
=\{c\in Z^1(K,\operatorname{ad}\bar\rho):[c]\in H^1_{\mathrm{fl}}\}.
$$

Then

$$
t^{\square,\mathrm{fl}}_{\bar\rho}
=Z^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho).
$$

All coboundaries lie in this space: strict conjugation of the split finite-flat lift remains finite flat. Consequently there is an exact sequence

$$
0\to H^0(K,\operatorname{ad}\bar\rho)
\to\operatorname{ad}\bar\rho
\to Z^1_{\mathrm{fl}}
\to H^1_{\mathrm{fl}}\to0.
$$

When dimensions are finite,

$$
\dim t^{\square,\mathrm{fl}}
=\dim H^1_{\mathrm{fl}}+d^2-h^0(K,\operatorname{ad}\bar\rho).
$$

For a fixed determinant $\delta$, the framed tangent consists of the trace-zero cocycles in $Z^1_{\mathrm{fl}}$. If $\ell\nmid d$, the unframed tangent is

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
\cap H^1(K,\operatorname{ad}^0\bar\rho),
$$

viewed under the trace splitting. We abbreviate this space to

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}^0\bar\rho).
$$

If $\ell\mid d$, the correct fixed-determinant tangent is instead the intersection of $H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)$ with the kernel of trace on $H^1$. This distinction is integral to the definition, not a cosmetic correction.

As a check, every coboundary is trace zero, even if the matrix producing it is not. It represents the split finite-flat extension written in a different lifting basis. Thus fixed determinant never means quotienting only by determinant-one changes of basis. When $\ell\mid d$, the coboundaries coming from matrices of nonzero trace are precisely what invalidates the naive formula $H^1(\operatorname{ad}^0)$.

## 6. Dual tangent conditions

### 6.1 Why ambient local duality is not enough

Local Tate duality gives a perfect pairing

$$
H^1(K,M)\times H^1(K,M^*(1))
\longrightarrow k
$$

for every finite-dimensional $k[G_K]$-module $M$, after choosing the usual coefficient-valued evaluation. It follows formally that every subspace has an orthogonal complement. It does not follow formally that the orthogonal complement of an integral condition is another integral condition. That assertion needs Cartier duality on models and compatibility between integral and generic cup products.

The perfectness, twist, and restriction--corestriction adjunction used here
are the finite-module local duality theorem established in Book 31. Book 30
supplies the finiteness and Euler characteristic used in the numerical
formulas below. Neither source identifies an arbitrary integral extension
condition with its annihilator; that additional comparison is exactly the
issue isolated in this chapter.

This distinction is especially important at $\ell$. The unramified subspace is not generally self-complementary for $\ell$-primary modules, and the finite-flat subspace is not the unramified subspace. An Euler characteristic computes the dimension of ambient $H^1$ but cannot locate the integral subspace inside it.

### 6.2 The orthogonal condition

For any finite-flat tangent condition $L_{\mathrm{fl}}(M)\subset H^1(K,M)$, define its **Tate-dual condition** by

$$
L_{\mathrm{fl}}^\vee(M^*(1))
=L_{\mathrm{fl}}(M)^\perp.
$$

This definition is always exact and basis independent. It is the condition that should be used in a dual Selmer structure even when no geometric description has been proved.

There is also a candidate geometric condition: choose Cartier-dual endpoint models and take generic images of integral extension classes in the dual exact category. We denote it by

$$
H^1_{\mathrm{fl,geom}}(K,M^*(1)).
$$

The two spaces are not identified by notation. The equality between them is a theorem with hypotheses.

### 6.3 What Cartier duality does not prove

Cartier duality reverses an admissible short exact sequence of finite flat
groups.  This supplies a duality on *objects and arrows* in the exact model
category.  It does not turn an extension of $\mathcal G_2$ by $\mathcal G_1$
into a torsor under one fixed group on $\operatorname{Spec}R$, and it does not
identify the Baer pairing on such extensions with the local Tate cup product.
Consequently no exact-annihilator assertion follows from Cartier duality
alone.

There is one unconditional compatibility.  If two generic classes actually
come from integral torsors under Cartier-dual groups and their cup product is
formed by the Cartier evaluation pairing, the resulting Brauer class extends
over $R$ and therefore has zero local invariant.  This proves an orthogonality
containment for that particular torsor problem.  Equality would additionally
require a duality theorem with supports and an order calculation for the
same cohomology theory.  Neither is a consequence of the exact-category
arguments in Chapters 4 and 5.

For the remainder of this book, the dual local condition therefore means the
orthogonal space defined in §6.2.  We do not identify an arbitrary geometric
self-extension space with a Tate annihilator.  The explicit Kummer calculation
later is obtained directly from flat cohomology and does not need such an
identification.

### 6.4 Self-duality only with a compatible pairing

Even when $M\simeq M^*(1)$ generically, self-duality of the tangent condition requires the isomorphism to extend to a perfect integral pairing and to carry the selected extension theory to its Cartier dual. A generic accidental isomorphism is insufficient.

Suppose that a chosen model $\mathcal M$ has a perfect pairing

$$
\mathcal M\times\mathcal M\longrightarrow\mu_{\ell,R}
$$

and that integral self-extensions are stable under the induced adjoint duality.
This gives a duality between two integral extension categories.  Only after a
separate comparison with the local cup product may one call either tangent
space the exact annihilator of the other.

For a two-dimensional representation with cyclotomic determinant, the alternating form gives $V\simeq V^*(1)$. It does not identify $\operatorname{ad}^0V$ with its Tate dual: the trace pairing gives

$$
(\operatorname{ad}^0V)^*(1)\simeq\operatorname{ad}^0V(1)
$$

when $\ell$ is odd. Thus the dual tangent condition lives naturally on a twist. Any assertion of literal self-orthogonality must include an additional twist-identification and its integral compatibility.

### 6.5 Dimension identities

Let $M$ be a finite-dimensional $k[G_K]$-module and $L\subset H^1(K,M)$. Perfectness gives

$$
\dim_kL+\dim_kL^\perp=h^1(K,M).
$$

The local Euler characteristic and Tate duality yield

$$
h^1(K,M)=h^0(K,M)+h^0(K,M^*(1))
+[K:\mathbf Q_\ell]\dim_kM.
$$

Therefore

$$
\dim L-h^0(K,M)
=h^0(K,M^*(1))+[K:\mathbf Q_\ell]\dim M
-\dim L^\perp.
$$

This identity is unconditional once $L^\perp$ is defined. A numerical formula for $\dim L$ requires an independent calculation of $L$ or of its orthogonal; it does not emerge from Euler characteristic alone. In particular, there is no universal tangent-dimension formula for finite-flat deformations over arbitrarily ramified $K$.

For $M=\operatorname{ad}^0\bar\rho$ in dimension two and odd characteristic, the trace form gives $M^*(1)\simeq M(1)$ and hence

$$
h^1(K,M)=h^0(K,M)+h^0(K,M(1))
+3[K:\mathbf Q_\ell].
$$

This ambient number still does not locate $H^1_{\mathrm{fl}}$. In the unramified odd rank-two range, Chapter 15 computes the exact finite-flat dimension from the integral classification and its gauge complex; that calculation is independent of the ambient Euler characteristic.

## 7. Lifting through small extensions

### 7.1 Two lifting problems, not one

Let

$$
0\longrightarrow I\longrightarrow A'\longrightarrow A\longrightarrow0
$$

be a small extension in $\operatorname{Art}_{\mathcal O}$, so $\mathfrak m_{A'}I=0$ and $I$ is a finite-dimensional $k$-space. Given a finite-flat deformation over $A$, one may ask:

1. does its generic representation lift to $A'$?
2. does some generic lift admit a finite-flat $A'$-linear model compatible with the model over $A$?

The first is the ambient representation problem. The second is an integral lifting problem. The first can be solvable while the second is not. Treating them as one question is the most common source of an incorrect assertion that finite-flat deformation rings are always smooth.

### 7.2 The ambient obstruction

Choose provisional matrix lifts of $\rho_A(g)$ to $A'$. Their multiplicative defect is a continuous $2$-cocycle, whose class is

$$
\operatorname{ob}_{\mathrm{rep}}(\rho_A,A'/A)
\in H^2(K,\operatorname{ad}\bar\rho)\otimes_k I.
$$

It vanishes exactly when the representation lifts. With fixed determinant,
determinant-preserving provisional lifts give a class in

$$
H^2(K,\operatorname{ad}^0\bar\rho)\otimes_k I.
$$

This obstruction target remains correct when $\ell\mid d$: the multiplicative
defect of determinant-preserving provisional matrices is trace zero. What
fails in that characteristic is the scalar/trace-zero splitting used to
describe unframed ambiguity and tangent classes, not the construction of the
framed fixed-determinant obstruction class.

If a lift exists, framed matrix lifts form a torsor under $Z^1(K,\operatorname{ad}\bar\rho)\otimes I$. Rigidified unframed lifts form a torsor under $H^1(K,\operatorname{ad}\bar\rho)\otimes I$. These are ambient statements and contain no integral geometry.

### 7.3 The extra integral obstruction

The integral problem is not literally a deformation of the coordinate algebra of
$\mathcal G_A$ along $A'\to A$.  The group schemes live over $R$, not over
$\operatorname{Spec}A$, and a free rank-$d$ lift over $A'$ has order
$|A'|^d$, whereas $\mathcal G_A$ has order $|A|^d$.  Thus the sought model is
a larger finite-flat group equipped with an $A'$-action whose coefficient
quotient is the given model.  Treating $A'\to A$ as a base change of Hopf
algebras would keep the rank fixed and is incorrect.

For a rigidified model $\mathcal G_A$, define the **integral lifting
obstruction** simply as the failure of the following groupoid to be nonempty:
its objects are $A'$-linear finite-flat models $\mathcal G_{A'}$ of generic
lifts together with an identification of the coefficient quotient by
$\ker(A'\to A)$ with $\mathcal G_A$.  This is an honest obstruction problem,
but in this generality it need not be represented by one canonical vector
space.  A classification theorem may replace it by an explicit complex or by
linear algebra; absent such a theorem, no group denoted
$\operatorname{Ob}^2_{\mathrm{int}}$ has been constructed.

The ambient class $\operatorname{ob}_{\mathrm{rep}}$ must vanish whenever this
groupoid is nonempty, but its vanishing is not sufficient in general.  It only
produces a generic $A'$-representation.  One must still construct a
finite-flat group of the larger order, extend the coefficient action, and
identify its coefficient reduction with the selected model.  For the
existential functor the question is weaker: it asks for some model downstairs
and some compatible model upstairs.  Different downstairs models can lead to
different answers, so a chosen-model obstruction cannot be promoted to an
intrinsic obstruction class without a comparison theorem.

### 7.4 Torsors of lifts and automorphisms

Suppose a chosen model lifts and a separate integral classification theorem
proves homogeneity. Then modelled framed lifts reducing to the chosen object
may form a torsor under an integral cocycle space

$$
Z^1_{\mathrm{fl},\mathcal G_A}(K,\operatorname{ad}\bar\rho)\otimes_k I.
$$

and, after rigidified strict equivalence, under

$$
H^1_{\mathrm{fl},\mathcal G_A}(K,\operatorname{ad}\bar\rho)\otimes_k I.
$$

These displays are conditional conclusions, not definitions of the two
spaces: the spaces and their action must be supplied by the classification
theorem. The word “rigidified” means that the reduction is identified with the fixed modelled object. If this identification is forgotten, automorphisms of the $A$-object can identify points of the torsor. The coarse fiber of

$$
D_{\bar\rho}^{\mathrm{fl}}(A')\to D_{\bar\rho}^{\mathrm{fl}}(A)
$$

need not itself be a torsor.

Infinitesimal automorphisms are integral endomorphisms fixed by $G_K$. They map to $H^0(K,\operatorname{ad}\bar\rho)\otimes I$, but the map need not be surjective when a generic centralizer fails to extend to the chosen Hopf lattice. In a full-faithfulness regime it is an isomorphism. This is another place where generic faithfulness, which gives uniqueness, cannot replace generic fullness, which gives existence.

### 7.5 Formal smoothness criteria and failures

A finite-flat deformation functor is formally smooth if every object lifts across every small extension. A sufficient chosen-model criterion is:

- the ambient obstruction in $H^2$ vanishes for every object;
- the integral model obstruction vanishes whenever the ambient one does;
- compatible endpoint models can be chosen after lifting;
- automorphisms do not spoil the required set-valued gluing.

Vanishing of $H^2(K,\operatorname{ad}\bar\rho)$ supplies only the first item. Conversely, ambient $H^2$ may be nonzero while the obstruction map is identically zero on a restricted finite-flat problem. Formal smoothness is a property of the lifting maps, not of the ambient cohomology group in isolation.

Singularity can arise from collision of model components, from a nonzero
integral obstruction, or from determinant and filtration equations. Ramified
bases permit additional integral lattices and are particularly prone to such
behavior. At this level of generality no smoothness is asserted. Chapters
14--16 invoke the low-weight classification and prove it by explicit lifting
for the full rank-two functor in the unramified odd range.

The elementary ring $\mathcal O[[X]]/(X^2)$ is a useful analogy. Its tangent space has one direction, just like $\mathcal O[[X]]$, but the direction does not lift freely through every thicker ring. Likewise, identifying a finite-flat tangent subspace proves neither that its vectors integrate indefinitely nor that the corresponding local ring has no higher equations.

## 8. Fiber products and the existential condition

### 8.1 Why models need not glue to prove membership

The most delicate formal question is whether finite flatness survives a coefficient fiber product. Let

$$
A'\longrightarrow A\longleftarrow A''
$$

be maps in $\operatorname{Art}_{\mathcal O}$ for which the ordinary ring fiber
product is again an object of the coefficient category, and set

$$
B=A'\times_AA''.
$$

A framed $B$-representation is the same thing as two framed branch
representations whose matrices agree over $A$. No module-patching theorem is
needed in that case: the glued matrices act on $B^d$. For unframed modules
with a separately supplied comparison isomorphism, the familiar patching
statement is available when one leg is surjective. Suppose both branch
representations are finite flat. Their selected models need not agree after
coefficient reduction to $A$. There may be no integral isomorphism between
those reductions, so trying to glue the two selected Hopf algebras is the
wrong problem.

The set-valued condition asks only whether the fiber-product representation has some model. The product of the branch models gives a single ambient group in which that new generic module can be closed. Model nonuniqueness is therefore bypassed rather than denied.

This distinction is central:

$$
\begin{array}{c|c}
\text{problem}&\text{data that must be produced}\\ \hline
\text{gluing chosen models}&\text{one model restricting to the two chosen witnesses},\\
\text{gluing existential membership}&\text{some model of the fiber-product representation}.
\end{array}
$$

Only the second problem is needed for the ordinary set-valued finite-flat deformation functor.

### 8.2 The common-ambient closure lemma

**Lemma 8.1 (fiber-product membership).** Let $V_B$ be a finite free
$B$-representation. If its scalar extensions

$$
V'=A'\otimes_BV_B,\qquad V''=A''\otimes_BV_B
$$

are finite flat, then $V_B$ is finite flat. Conversely, base change of a
finite-flat $B$-representation to either branch is finite flat.

In particular, two framed branch representations whose matrices agree over
$A$ glue to a representation on $B^d$, and that representation is finite flat
if and only if both branches are finite flat.

**Proof strategy.** Embed $V_B$ into the direct sum of the branch modules, close it inside the product of any two branch models, and restrict the product coefficient action to the fiber-product coefficient ring.

Choose $A'$- and $A''$-linear models $\mathcal G'$ and $\mathcal G''$. Their product $\mathcal P=\mathcal G'\times_R\mathcal G''$ is finite flat and has generic module $V'\oplus V''$. The natural map

$$
V_B\longrightarrow V'\oplus V'',\qquad v\longmapsto(v',v'')
$$

is injective and $G_K$-equivariant. Close its generic finite étale subgroup inside $\mathcal P$ and call the closure $\mathcal H$. The DVR closure theorem makes $\mathcal H$ finite flat. Its generic points are exactly $V_B$.

The product model carries an action of $A'\times A''$. Restrict it along the injective ring map $B\to A'\times A''$. Every element of $B$ preserves $V_B$ on the generic fiber: the equality of its two images in $A$ is precisely the condition defining the fiber product. To see that the ambient endomorphism restricts to $\mathcal H$, pull back the defining ideal of $\mathcal H$ along the map $\mathcal H\to\mathcal P$. It vanishes after tensoring with $K$ and therefore vanishes already, because $\mathcal H$ is $R$-flat. Addition and multiplication of the restricted endomorphisms agree with the ring laws generically and hence integrally. This gives a $B$-action on $\mathcal H$. Since $V_B\simeq B^d$, the rank is

$$
|\mathcal H|=|B|^d.
$$

The converse is Theorem 2.3. $\square$

No rank calculation for a raw fiber product of group schemes appears in this proof. Such a raw fiber product could have torsion. The construction first forms a harmless product over $R$ and then takes the saturated closure of the desired generic subgroup.

### 8.3 Exact comparison for framed lifts

The ambient framed deformation functor preserves every coefficient fiber
product that exists in the test category exactly because matrices do. Lemma
8.1 shows that membership in the finite-flat subfunctor can be checked
branchwise. Therefore the comparison map

$$
D_{\bar\rho}^{\square,\mathrm{fl}}(B)
\longrightarrow
D_{\bar\rho}^{\square,\mathrm{fl}}(A')
\times_{D_{\bar\rho}^{\square,\mathrm{fl}}(A)}
D_{\bar\rho}^{\square,\mathrm{fl}}(A'')
$$

is a bijection for every such diagram. In particular it is a bijection for
all diagrams with a surjective leg that occur in the Schlessinger criteria.

Injectivity is inherited from the ambient framed functor: two $B$-valued matrix homomorphisms with the same two projections are equal. Surjectivity uses Lemma 8.1. Notice what has not been proved. The closure model over $B$ need not reduce to the originally chosen model on either branch. Exact gluing holds for representations satisfying an existential property, not for a moduli groupoid retaining the witnesses.

The same argument works after fixing a determinant. Determinants commute with coefficient fiber products, so two branch representations with determinant $\delta$ glue to a representation with determinant $\delta$. It also works for intersections with any other framed condition whose defining property is preserved by the common-ambient construction.

### 8.4 Modelled functors remain different

If chosen models are part of the objects, Lemma 8.1 is not enough. A modelled fiber product must restrict to the two selected branch models, and the closure $\mathcal H$ need not do so. One then needs one of three additional inputs:

- an integral comparison isomorphism between the two reductions;
- a classification whose model groupoid satisfies effective descent;
- a common ambient model prescribed before the two branches are chosen.

These are strong statements and are useful when one needs a compatible torsion tower or a moduli interpretation. They are not prerequisites for pro-representing the existential representation functor on Artinian rings.

This observation resolves a common logical tangle. Nonuniqueness of integral models is real, and selected models may fail to glue. Nevertheless the image property can be homogeneous because a new witness may be constructed from both old witnesses. An image of a poorly behaved moduli space need not usually be closed, but here the exact-category closure theorem supplies the missing fiber-product operation directly on the image functor.

### 8.5 Tangent finiteness

The tangent of the framed condition is

$$
Z^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho),
$$

and the unframed tangent is the subspace

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
\subseteq H^1(K,\operatorname{ad}\bar\rho).
$$

For $K/\mathbf Q_\ell$ finite and $k$ finite, local Galois cohomology with finite coefficients is finite. Hence both tangent spaces are finite-dimensional. Fixed determinant replaces them by the trace-kernel versions described in §5.5. No formula for their dimensions is used here.

## 9. Pro-representability and closed deformation rings

### 9.1 The framed universal ring

We can now prove representability without classifying finite-flat group schemes.

**Theorem 9.1 (framed finite-flat representability).** Let $K/\mathbf Q_\ell$ be finite, let $k$ be finite of characteristic $\ell$, let $\mathcal O$ be a complete Noetherian local coefficient ring with residue field $k$, and let

$$
\bar\rho:G_K\to\operatorname{GL}_d(k)
$$

be finite flat. Then the framed existential finite-flat deformation functor is pro-representable by a complete Noetherian local $\mathcal O$-algebra

$$
R_{\bar\rho}^{\square,\mathrm{fl}}.
$$

For every determinant lift $\delta$, the fixed-determinant framed functor is pro-representable by

$$
R_{\bar\rho}^{\square,\mathrm{fl},\delta}.
$$

**Proof strategy.** Verify the fiber-product conditions directly, use local cohomology for tangent finiteness, and apply the representability theorem for framed representations.

The residual value is a singleton because $\bar\rho$ is finite flat. Exact
fiber-product gluing is §8.3. Its surjectivity gives (H1), its split
first-order instance gives (H2), and its injectivity on a small
self-fiber-product gives (H4). Tangent finiteness is §8.5 and gives (H3).
Thus all four representability hypotheses, rather than only the three hull
hypotheses, hold. Intersecting with the closed determinant equation preserves
every property. $\square$

The theorem does not assert formal smoothness. It constructs a ring which may have several components or nilpotent relations. It also does not construct a universal finite-flat group scheme of infinite order. The universal object is a compatible system of representations over the Artinian quotients of the ring.

### 9.2 The unframed ring and automorphisms

For unframed classes, the remaining issue is the ordinary strict-conjugacy problem. Finite flatness is invariant under strict equivalence, and the common-ambient proof is unaffected if one first changes a branch representative by a strict matrix. Thus the finite-flat subfunctor inherits the same automorphism analysis as the ambient deformation functor.

**Theorem 9.2 (unframed finite-flat representability).** Under the hypotheses of Theorem 9.1, assume in addition

$$
\operatorname{End}_{k[G_K]}(\bar V)=k.
$$

Then $D_{\bar\rho}^{\mathrm{fl}}$ and every fixed-determinant variant $D_{\bar\rho}^{\mathrm{fl},\delta}$ are pro-representable by complete Noetherian local rings

$$
R_{\bar\rho}^{\mathrm{fl}},\qquad
R_{\bar\rho}^{\mathrm{fl},\delta}.
$$

**Proof.** The scalar-centralizer theorem for unframed representations proves that comparison automorphisms lift and that the unframed ambient functor satisfies the required uniqueness condition. Given compatible finite-flat branch classes, choose representatives whose reductions agree by using such a strict comparison. Strict invariance preserves branchwise finite flatness, and Lemma 8.1 models their matrix fiber product. Tangent finiteness follows from Theorem 5.2. The determinant equation is stable throughout. $\square$

If the residual centralizer is larger, the framed ring still exists. The unframed finite-flat functor may have a hull, but a universal coarse ring is not asserted. A chosen stable line or another rigidification can sometimes restore representability; it changes the functor and must be named.

### 9.3 Why the representing map is a quotient

Let $R^{\square}$ represent the ambient framed deformation functor and let $S=R^{\square,\mathrm{fl}}$. Inclusion of functors corresponds to a continuous local map

$$
R^{\square}\longrightarrow S.
$$

We claim it is surjective. This makes finite flatness a closed condition in the precise formal sense.

First, injectivity of $h_S(k[\epsilon])\to h_{R^{\square}}(k[\epsilon])$ implies that the relative cotangent map

$$
\frac{\mathfrak m_{R^{\square}}}
{\mathfrak m_{R^{\square}}^2+\mathfrak m_{\mathcal O}R^{\square}}
\longrightarrow
\frac{\mathfrak m_S}
{\mathfrak m_S^2+\mathfrak m_{\mathcal O}S}
$$

is surjective. Lift a finite set of generators on the right to $R^{\square}$. Induction on $n$ then shows that the image of $R^{\square}$ is dense in $S$: every element of $S$ can be approximated modulo $\mathfrak m_S^n$ by a polynomial in the lifted generators and coefficients from $\mathcal O$.

Because $k$ is finite, a complete Noetherian local ring is the inverse limit of finite Artinian quotients and is compact. The continuous image of the compact ring $R^{\square}$ in the Hausdorff ring $S$ is closed. A dense closed image is all of $S$. Therefore

$$
S\simeq R^{\square}/I_{\mathrm{fl}}
$$

for a closed ideal $I_{\mathrm{fl}}$. The same proof applies to the fixed-determinant and unframed rings whenever they exist.

This argument proves closedness from representability and monomorphism. It does not say that a parameter space of all models is proper, nor does it require such a space.

### 9.4 Complete coefficient rings

Let $B$ be a complete Noetherian local $\mathcal O$-algebra with residue field $k$, and let

$$
\rho_B:G_K\to\operatorname{GL}_d(B)
$$

be continuous. We say that $\rho_B$ is **levelwise finite flat** if every Artinian reduction

$$
\rho_{B,n}:G_K\to\operatorname{GL}_d(B/\mathfrak m_B^n)
$$

is finite flat. This definition is intrinsic and makes no choice of models.

**Proposition 9.3.** A continuous framed representation $\rho_B$ is levelwise finite flat if and only if its classifying map

$$
R_{\bar\rho}^{\square}\longrightarrow B
$$

factors through $R_{\bar\rho}^{\square,\mathrm{fl}}$.

**Proof.** If the map factors, each composition to $B/\mathfrak m_B^n$ is a point of the represented finite-flat functor. Conversely, levelwise membership gives compatible maps from $R^{\square,\mathrm{fl}}$ to all $B/\mathfrak m_B^n$. Compatibility holds because the representations themselves form a compatible system and the representing bijections are natural. Taking inverse limits gives a continuous map to $B$. $\square$

The proposition concerns representations, not witnesses. It is possible that every level admits a model while no compatible sequence of selected models has been constructed. The universal ring does not erase this distinction.

### 9.5 Compatible model systems

A **compatible finite-flat model system** for $\rho_B$ consists of models $\mathcal G_n$ of $\rho_{B,n}$ and integral identifications between the coefficient reduction of $\mathcal G_{n+1}$ and $\mathcal G_n$, satisfying transitivity. Its ranks are

$$
|\mathcal G_n|=|B/\mathfrak m_B^n|^d,
$$

and hence grow with $n$. Such a system is not one finite group scheme over $R$.

Levelwise finite flatness does not by itself choose a compatible system. A tower of nonempty model groupoids can have transition functors whose images miss one another. Compatibility follows under extra hypotheses such as:

- uniqueness of models with their generic identifications;
- properness together with an effective inverse-limit theorem for the model groupoid;
- an explicit linear classification commuting with coefficient reduction;
- construction inside a fixed compatible ambient torsion tower.

Good-reduction abelian varieties supply the last situation: their $\ell^n$-torsion groups already form a compatible system. None of these hypotheses is built into Theorems 9.1 and 9.2.

This separation is useful downstream. A global deformation ring needs a local condition on its Artinian representation points, for which levelwise existential finite flatness is enough. A construction of a Barsotti--Tate group, an integral period object, or a geometric family needs compatible models and must invoke an additional theorem.

## 10. Changing the local field

### 10.1 Restriction and integral base change

Let $L/K$ be a finite extension inside $K^s$, with valuation ring $R_L$. If $\mathcal G/R$ models $V$, then

$$
\mathcal G_{R_L}=\mathcal G\times_RR_L
$$

is finite locally free, inherits every coefficient endomorphism, and has generic module $V|_{G_L}$. Hence restriction defines natural maps

$$
D_{\bar\rho}^{\mathrm{fl}}(A)
\longrightarrow
D_{\bar\rho|_{G_L}}^{\mathrm{fl}}(A)
$$

and similarly for framed and fixed-determinant problems. No unramified hypothesis is needed in this direction.

Exact sequences, Cartier duality, and finite products commute with this base change. Schematic closure of a generic subgroup commutes with the flat map of valuation rings: contraction of the generic ideal followed by tensoring remains saturated. Consequently all constructions made within a chosen model transport coherently to $L$.

### 10.2 Unramified base change

If $L/K$ is unramified, the ramification index does not change and the special fiber is extended through the finite separable field extension $k_L/k_K$. Connectedness, étaleness, rank, and perfectness of Cartier pairings are preserved. Inertia groups agree under the standard embedding, so an unramified extension does not erase genuine inertia action.

In a separately proved full-faithfulness regime, a model over $R_L$ descends to $R$ when its generic representation comes from $G_K$ and the canonical Galois descent maps exist generically: fullness extends those maps and faithfulness forces their cocycle identities. If $L/K$ is unramified Galois and the model is stable under the semilinear action of $\operatorname{Gal}(L/K)$, effective finite flat descent gives the downstairs model. At this level of generality no such theorem is assumed; Chapter 14 states Raynaud full faithfulness in the precise low-ramification range where it applies.

The stability hypothesis must not be omitted. Even over an unramified extension, an arbitrarily selected upstairs model is not automatically equipped with descent data when models are nonunique.

### 10.3 Ramified base change and potential finite flatness

Ramified extension changes the valuation scale. New saturated Hopf lattices may appear, and a representation not finite flat over $K$ may become finite flat over $L$. This **potentially finite-flat** property is strictly weaker.

An auxiliary prime-to-$\ell$ example proves strictness for finite Galois modules, though it lies outside the fixed coefficient category $\operatorname{Art}_{\mathcal O}$. Let $q\ne\ell$ be odd and let a ramified quadratic character

$$
\eta:G_K\to\{\pm1\}\subset\mathbf F_q^\times
$$

act on the line $\mathbf F_q$. Its order is prime to the residue characteristic, so any finite-flat model would be étale and the character would be unramified. No such model exists over $K$. After restriction to the ramified quadratic extension cut out by $\eta$, the line is trivial and has a constant model.

Thus restriction preserves finite flatness, while reflection is false in the broader category even for one-dimensional representations. Within the $\ell$-primary deformation problem, restriction certainly sends $H^1_{\mathrm{fl}}(K,M)$ into $H^1_{\mathrm{fl}}(L,M)$; identifying it with the inverse image of the upstairs condition requires an integral descent theorem and is not asserted from restriction alone.

### 10.4 Descent data

An $R_L$-model $\mathcal H$ descends through the finite faithfully flat map $R\to R_L$ precisely when it carries an isomorphism

$$
p_1^*\mathcal H\xrightarrow{\sim}p_2^*\mathcal H
$$

over $R_L\otimes_RR_L$ satisfying the cocycle condition over the triple tensor product. The Hopf structure, coefficient action, and generic identification must all be compatible. In a Galois extension this may be written as semilinear isomorphisms $\gamma^*\mathcal H\simeq\mathcal H$, but the tensor-product formulation remains the accurate one in the ramified case.

A $G_K$-representation supplies descent maps on the generic fiber. Faithfulness shows that integral extensions of those maps, if they exist, are unique and automatically satisfy the cocycle identity. It does not prove that they exist. Full faithfulness or explicit stable lattice data supplies existence; without one of them, descent is not justified.

For a base-changed model $\mathcal G_{R_L}$, the descent datum is canonical, so descent returns $\mathcal G$. This tautological case is often the only one needed in a preservation argument. In the reverse direction, beginning with an arbitrary model of the restricted representation supplies no reason for its Hopf lattice to be stable under $\operatorname{Gal}(L/K)$. A semilinear action on generic points proves stability of the generic algebra, not of the integral lattice inside it.

### 10.5 Tangents under restriction

Restriction of cocycles gives a commutative square

$$
\begin{array}{ccc}
H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)&\longrightarrow&
H^1(K,\operatorname{ad}\bar\rho)\\
\downarrow&&\downarrow\operatorname{res}\\
H^1_{\mathrm{fl}}(L,\operatorname{ad}\bar\rho)&\longrightarrow&
H^1(L,\operatorname{ad}\bar\rho).
\end{array}
$$

The left arrow exists because integral self-extensions base-change. Corestriction need not preserve the finite-flat tangent without an integral norm or Weil-restriction construction satisfying the relevant rank and coefficient hypotheses. Under a finite étale extension of valuation rings, Weil restriction and trace on torsors often supply it; for ramified extensions it must be checked separately.

Local Tate duality makes restriction adjoint to corestriction. Therefore descent results for the primal finite-flat condition translate into norm statements for the dual condition only when the corresponding integral operations have been proved. No equality of tangent dimensions under field extension follows merely from the generic restriction map.

## 11. Examples and boundary cases

### 11.1 Constant groups and roots of unity

The constant group

$$
\underline{\mathbf Z/\ell^n\mathbf Z}_R
$$

models the trivial $G_K$-module $\mathbf Z/\ell^n\mathbf Z$. It is finite étale even though its rank is divisible by the residue characteristic. The group

$$
\mu_{\ell^n}=\operatorname{Spec}R[T]/(T^{\ell^n}-1)
$$

models $\mathbf Z/\ell^n\mathbf Z(1)$. It is finite flat but its special fiber is connected and nonreduced. Cartier duality exchanges the two models.

If $K$ contains all $\ell^n$th roots of unity, their generic modules are both trivial and the generic groups are isomorphic. The integral groups remain nonisomorphic because their special fibers have different connected--étale type. This is the standard example of model nonuniqueness when ramification is large enough: containing $\mu_\ell$ forces $e(K/\mathbf Q_\ell)$ to be divisible by $\ell-1$.

These examples also show why coefficients must be tracked. An action of a finite ring $A$ on a generic direct sum of cyclotomic lines need not preserve an arbitrarily chosen product of constant and multiplicative models. Existence of some $A$-linear model follows from closure and quotient, but a selected model may have fewer integral endomorphisms than its generic fiber.

### 11.2 Ordinary Kummer extensions

Consider extensions

$$
0\longrightarrow k(1)\longrightarrow V_c
\longrightarrow k\longrightarrow0.
$$

After choosing $k$ over $\mathbf F_\ell$, their classes lie in

$$
H^1(K,k(1))\simeq
(K^\times/(K^\times)^\ell)\otimes_{\mathbf F_\ell}k.
$$

The endpoint models are the coefficient scalar extension
$\mu_\ell\otimes_{\mathbf F_\ell}k$ and the constant additive $k$-group;
the tensor symbol denotes extension in the exact category of finite-flat
coefficient groups, not base change of the valuation ring. In the standard
ordinary model category, integral extensions correspond to flat Kummer
torsors over $R$. More precisely, the same evaluation-at-$1$ calculation as
in Chapter 12 gives

$$
\operatorname{Ext}^1_{k\text{-fppf}}
(\underline{k},\mu_\ell\otimes_{\mathbf F_\ell}k)
\simeq H^1_{\mathrm{fppf}}(R,\mu_\ell)
\otimes_{\mathbf F_\ell}k.
$$

The flat Kummer sequence

$$
1\to\mu_\ell\to\mathbf G_m
\xrightarrow{(\cdot)^\ell}\mathbf G_m\to1
$$

and $\operatorname{Pic}(R)=0$ give

$$
H^1_{\mathrm{fppf}}(R,\mu_\ell)
\simeq R^\times/(R^\times)^\ell.
$$

Its generic image is therefore the unit subspace

$$
\bigl(R^\times/(R^\times)^\ell\bigr)
\otimes_{\mathbf F_\ell}k
\subset
\bigl(K^\times/(K^\times)^\ell\bigr)
\otimes_{\mathbf F_\ell}k.
$$

One way to see the extension is to choose $u\in R^\times$ and consider the torsor $T^\ell=u$. Its coordinate algebra is finite free over $R$ even when its special fiber is nonreduced. The contracted product with the multiplicative endpoint produces the ordinary middle group. Multiplying two units corresponds to Baer addition of Kummer classes. If $u$ is an $\ell$th power, the torsor has an integral section and the extension splits.

**Worked example.** For $K=\mathbf Q_\ell$ and odd $\ell$, write

$$
\mathbf Q_\ell^\times=\ell^{\mathbf Z}\times
\mu_{\ell-1}\times(1+\ell\mathbf Z_\ell).
$$

The $\ell$th-power map is an automorphism on $\mu_{\ell-1}$, while

$$
(1+\ell\mathbf Z_\ell)/(1+\ell\mathbf Z_\ell)^\ell
$$

is one-dimensional over $\mathbf F_\ell$. Hence

$$
\dim_k (R^\times/(R^\times)^\ell)\otimes k=1,
$$

whereas $K^\times/(K^\times)^\ell$ has an additional valuation direction. The standard-endpoint ordinary extension classes form a line inside a two-dimensional ambient Kummer space.

For a general finite extension $K/\mathbf Q_\ell$, the unit quotient has dimension $[K:\mathbf Q_\ell]$ plus a possible root-of-unity contribution. The exact number depends on whether $\mu_\ell\subset K$. This dependence is one reason no ramification-free universal formula should be quoted.

### 11.3 The uniformizer boundary for fixed endpoints

Let $K=\mathbf Q_\ell$, $\ell>2$, take $k=\mathbf F_\ell$, and let $c_\ell$ be the Kummer class of the uniformizer $\ell$. It defines a generic extension

$$
0\to k(1)\to V_{c_\ell}\to k\to0.
$$

Both endpoints have standard finite-flat models, but $V_{c_\ell}$ is not the generic fiber of an extension of those selected models.

**Proof.** The valuation of $\ell$ is one, so its class is not represented by a unit and is not in the image of $H^1_{\mathrm{fppf}}(R,\mu_\ell)$. Chapter 12 proves that this image is exactly the set of generic extensions arising from admissible sequences

$$
0\longrightarrow\mu_\ell\longrightarrow\mathcal H
\longrightarrow\underline{\mathbf F_\ell}\longrightarrow0.
$$

Consequently no such sequence has generic class $c_\ell$. $\square$

This conclusion is deliberately relative to the endpoint models. If
$V_{c_\ell}$ had some finite-flat model, closure of its cyclotomic line and
the resulting quotient would supply rank-$\ell$ endpoint models, but the
exact-category argument alone would not identify them with $\mu_\ell$ and
the constant group. Upgrading the relative exclusion to an intrinsic
non-finite-flatness theorem requires the low-ramification rigidity stated in
Chapter 14.

Chapter 14 supplies exactly that missing rigidity when $K/\mathbf Q_\ell$
is unramified and $\ell>2$. In that range the endpoint models are unique, so
the uniformizer class is intrinsically not finite flat. The qualification in
the preceding paragraph remains necessary for ramified bases.

### 11.4 Good-reduction elliptic curves

Let $E/K$ have good reduction, so it extends to an elliptic scheme $\mathcal E/R$. Multiplication by $\ell^n$ is finite locally free, and

$$
\mathcal E[\ell^n]
$$

models $E[\ell^n](K^s)$. The Weil pairing is a perfect Cartier pairing

$$
\mathcal E[\ell^n]\times\mathcal E[\ell^n]
\longrightarrow\mu_{\ell^n},
$$

so the generic representation has cyclotomic determinant and an integral self-duality.

For ordinary good reduction, the special fiber has a connected multiplicative direction and an étale direction. The corresponding exact sequence need not split over $R$, and its extension class is part of the integral information. For supersingular reduction, the special $\ell$-torsion is connected of rank $\ell^2$. In both cases the generic representation is two-dimensional and can be ramified.

The distinction persists through higher torsion. The groups $\mathcal E[\ell^n]$ form compatible finite-flat models, and reduction modulo $\ell^m$ is represented by the appropriate saturated subgroup and quotient. Their ranks are $\ell^{2n}$. Cartier duality and the principal polarization identify every layer with its dual, compatibly with transition maps. Thus good reduction supplies not only isolated witnesses but an entire compatible tower suitable for a complete coefficient representation.

If $C\subset E[\ell^n](K^s)$ is a stable subgroup, its closure in $\mathcal E[\ell^n]$ is finite flat and models $C$; the quotient models the generic quotient. This is the principal geometric source of the subquotient constructions used in modularity arguments.

Good reduction is sufficient, not necessary, for an individual torsion representation to be finite flat. Conversely, finite flatness of one torsion layer does not by itself prove good reduction of the elliptic curve. Such converses require separate reduction criteria.

### 11.5 Neither unramified nor a generic extension rule

Two short examples locate the condition.

- It is not unramifiedness: $\mu_\ell$ is finite flat and its generic character is cyclotomic, hence ramified for $K=\mathbf Q_\ell$.
- It is not true that arbitrary generic extensions of selected finite-flat models extend integrally: the uniformizer class of §11.3 does not extend between the standard multiplicative and constant endpoints.

There is also a prime-to-$\ell$ contrast for finite group schemes whose rank is invertible on $R$. Every such finite-flat model is étale, so its generic inertia action is trivial. At $\ell$-power rank, connected degeneration becomes possible. This contrast concerns the rank of the group scheme, not the order of the image of a character.

## 12. Standard endpoint models and the Kummer boundary

### 12.1 Why the endpoint models are retained

Kummer theory gives an explicit integral calculation only after the endpoint models have been named. Let $R$ be a complete DVR of mixed characteristic $(0,\ell)$, with fraction field $K$, and put

$$
\Lambda_n=\mathbf Z/\ell^n\mathbf Z.
$$

The standard endpoint models are

$$
\mathcal M_n=\mu_{\ell^n},
\qquad
\mathcal C_n=\underline{\Lambda_n}_R.
$$

They are finite locally free of rank $\ell^n$, carry their evident $\Lambda_n$-actions, and are Cartier dual. Their generic modules are $\Lambda_n(1)$ and $\Lambda_n$. A **standard ordinary extension** is an admissible sequence of fppf sheaves of $\Lambda_n$-modules

$$
0\longrightarrow\mathcal M_n\longrightarrow\mathcal H
\longrightarrow\mathcal C_n\longrightarrow0. \tag{12.1}
$$

The endpoint identifications are part of the object. This precision is necessary because another finite-flat model of either generic line, when one exists, defines a different integral extension problem. The calculation below classifies (12.1); it does not classify all models of its generic middle module.

### 12.2 Extensions as flat cohomology

Work in the abelian category of fppf sheaves of $\Lambda_n$-modules on $\operatorname{Spec}R$. The constant sheaf $\mathcal C_n$ is free of rank one in this category. For every sheaf $\mathcal F$ of $\Lambda_n$-modules, evaluation at $1$ gives a natural equality

$$
\operatorname{Hom}_{\Lambda_n}(\mathcal C_n,\mathcal F)
=\Gamma(R,\mathcal F). \tag{12.2}
$$

Apply both sides to an injective resolution of $\mathcal F$. The cohomology of the right-hand complex is, by definition, fppf cohomology, while the cohomology of the left-hand complex is Ext. Thus

$$
\operatorname{Ext}^i_{\Lambda_n\text{-fppf}}
(\mathcal C_n,\mathcal F)
\simeq H^i_{\mathrm{fppf}}(R,\mathcal F) \tag{12.3}
$$

for every $i\ge0$. In degree one and with $\mathcal F=\mathcal M_n$, this identifies the extension classes (12.1) with

$$
H^1_{\mathrm{fppf}}(R,\mu_{\ell^n}). \tag{12.4}
$$

The $\Lambda_n$-linear category matters. It forces $[\ell^n]=0$ on the middle sheaf and makes the constant quotient the free rank-one coefficient object. An extension merely in abelian fppf sheaves would be a different problem.

### 12.3 Representability and rank of the middle term

An abstract sheaf extension in (12.1) is represented by a finite-flat group scheme; this point deserves a proof because it is what turns cohomology into an integral model.

Let $q:\mathcal H\to\mathcal C_n$ be a sheaf extension and let

$$
\mathcal P=q^{-1}(1).
$$

Translation by $\mathcal M_n$ makes $\mathcal P$ an $\mathcal M_n$-torsor. It is locally nonempty for the fppf topology because $q$ is an epimorphism of fppf sheaves. Choose an fppf cover $R\to R'$ and a section $h\in\mathcal P(R')$. Since the extension is $\Lambda_n$-linear, the assignment $a\mapsto ah$ is a splitting of the constant quotient over $R'$. Consequently

$$
\mathcal H_{R'}\simeq
\mathcal M_{n,R'}\times\mathcal C_{n,R'} \tag{12.5}
$$

as a sheaf, compatibly with its group law and coefficient action.

The right side is represented by a finite locally free affine group of rank $\ell^{2n}$. Its two pullbacks to $R'\otimes_RR'$ carry the descent isomorphism supplied by the original sheaf $\mathcal H$. Affine descent is effective: the equalizer of the two semilinear maps on the finite projective coordinate algebra is a finite projective $R$-algebra, and multiplication, unit, comultiplication, counit, inverse, and the $\Lambda_n$-action descend because all their compatibility equations can be checked after the faithfully flat base change. Thus $\mathcal H$ is represented by a finite locally free commutative group scheme of rank $\ell^{2n}$.

Conversely, every admissible sequence (12.1) is an extension in the sheaf category, so (12.4) classifies exactly the standard ordinary extensions. Pullback and represented pushout agree with the usual operations on sheaf extensions; under (12.4), Baer sum is addition in cohomology.

### 12.4 Flat Kummer theory over a DVR

The fppf Kummer sequence is exact even though $\ell$ is not invertible in $R$:

$$
1\longrightarrow\mu_{\ell^n}\longrightarrow\mathbf G_m
\xrightarrow{(\cdot)^{\ell^n}}\mathbf G_m\longrightarrow1. \tag{12.6}
$$

The only nonformal point is local surjectivity. Given a unit $u$ over an $R$-algebra $S$, the algebra

$$
S[T]/(T^{\ell^n}-u)
$$

is finite free of rank $\ell^n$, and $T$ is a unit there. Its spectrum is therefore an fppf cover on which $u$ has an $\ell^n$th root. The long exact sequence gives

$$
0\longrightarrow R^\times/(R^\times)^{\ell^n}
\longrightarrow H^1_{\mathrm{fppf}}(R,\mu_{\ell^n})
\longrightarrow\operatorname{Pic}(R)[\ell^n]\longrightarrow0.
$$

Every invertible module over the local ring $R$ is free, so $\operatorname{Pic}(R)=0$. Hence

$$
H^1_{\mathrm{fppf}}(R,\mu_{\ell^n})
\simeq R^\times/(R^\times)^{\ell^n}. \tag{12.7}
$$

Over $K$, the same argument gives

$$
H^1(K,\Lambda_n(1))
\simeq K^\times/(K^\times)^{\ell^n}. \tag{12.8}
$$

The generic-fiber map sends (12.7) to the subgroup represented by units, and it is injective. Indeed, if $u\in R^\times$ and $u=x^{\ell^n}$ in $K$, then $0=v_K(u)=\ell^n v_K(x)$, so $x\in R^\times$. Combining (12.4), (12.7), and (12.8) proves:

**Theorem 12.1 (standard endpoint calculation).** The generic classes of admissible extensions (12.1) are exactly

$$
R^\times/(R^\times)^{\ell^n}
\subseteq K^\times/(K^\times)^{\ell^n}. \tag{12.9}
$$

Every class in this subgroup has a finite-flat middle group of rank $\ell^{2n}$, and every such middle group is killed by $\ell^n$ and carries the stated endpoint identifications.

### 12.5 The valuation direction

Choose a uniformizer $\pi$. The valuation gives a split decomposition of abelian groups

$$
K^\times\simeq\pi^{\mathbf Z}\times R^\times,
$$

and therefore

$$
K^\times/(K^\times)^{\ell^n}
\simeq
(\mathbf Z/\ell^n\mathbf Z)[\pi]
\oplus R^\times/(R^\times)^{\ell^n}. \tag{12.10}
$$

Theorem 12.1 identifies the second summand with standard ordinary extensions. The first is excluded: if $\pi=u x^{\ell^n}$ for a unit $u$, then

$$
1=v_K(\pi)=\ell^n v_K(x),
$$

which is impossible. Thus the Kummer extension class of a uniformizer is a concrete generic extension of the two generic endpoint modules which does not extend to the two selected endpoint models.

This proof works over every mixed-characteristic DVR and for every $n\ge1$. It uses no presentation of an arbitrary finite-flat group scheme and no uniqueness assertion about solutions of semilinear equations.

### 12.6 The boundary of the conclusion

Theorem 12.1 is a theorem about a fixed exact category: the kernel is $\mu_{\ell^n}$ and the quotient is the constant group. It must not be silently changed into an intrinsic classification of generic middle representations.

Indeed, suppose a generic extension $V$ admits some finite-flat model $\mathcal H$. Closing its cyclotomic submodule in $\mathcal H$ and taking the represented quotient produces an admissible sequence

$$
0\longrightarrow\mathcal G_1\longrightarrow\mathcal H
\longrightarrow\mathcal G_0\longrightarrow0,
$$

where the generic fibers of $\mathcal G_1$ and $\mathcal G_0$ are cyclotomic and trivial. The closure theorem does not identify $\mathcal G_1$ with $\mu_{\ell^n}$ or $\mathcal G_0$ with the constant group. Such an identification would be a separate rigidity or classification theorem, and at sufficiently ramified fields it is false without further hypotheses: constant and multiplicative groups can already have isomorphic generic fibers when the relevant roots of unity lie in $K$.

Accordingly, the valuation calculation is used later only for the endpoint-rigidified ordinary chart. The full existential finite-flat condition remains governed by Chapters 2--9. This separation is precisely what permits the general representability theorem without pretending that all integral models have been classified.

For unramified $K$ and $\ell>2$, the rigidity and comparison theorems of Chapter 14 remove this
particular ambiguity: full faithfulness identifies the two endpoint models
with the standard ones, so the valuation direction is the intrinsic très
ramifiée non-finite-flat class. Outside that range, the endpoint-relative
formulation above is the strongest conclusion proved here.

## 13. Universal rings and dimension bookkeeping

### 13.1 From tangent subspaces to minimal presentations

Representability gives a complete local ring, but it does not make that ring smooth. Let

$$
L_{\mathrm{fl}}^\delta
\subseteq H^1(K,\operatorname{ad}\bar\rho)
$$

denote the unframed fixed-determinant finite-flat tangent space, interpreted as the trace kernel when $\ell\mid d$. Assume the scalar-centralizer hypothesis so that the unframed fixed-determinant ring exists, and put

$$
r=\dim_k L_{\mathrm{fl}}^\delta.
$$

The cotangent-space calculation for a represented functor gives a minimal presentation

$$
R_{\bar\rho}^{\mathrm{fl},\delta}
\simeq
\mathcal O[[X_1,\ldots,X_r]]/J, \tag{13.1}
$$

where

$$
J\subseteq
(\mathfrak m_{\mathcal O},X_1,\ldots,X_r)^2
+\mathfrak m_{\mathcal O}\mathcal O[[X_1,\ldots,X_r]]
$$

after the variables have been chosen minimally relative to $\mathcal O$. More simply, no relation in $J$ has a nonzero relative linear term.

Equation (13.1) says exactly what the tangent calculation controls: the number of generators. It says nothing by itself about the number of relations, reducedness, irreducible components, or Krull dimension. A one-dimensional tangent may belong to either $\mathcal O[[X]]$ or $\mathcal O[[X]]/(X^2)$.

### 13.2 Obstructions and relation bounds

For an ambient representation lift across a small extension with kernel $I$, the obstruction lies in

$$
H^2(K,\operatorname{ad}\bar\rho)\otimes_k I.
$$

The finite-flat condition can cut out a smaller obstruction theory, but Chapter 7 deliberately did not invent one in general. If a particular model classification supplies a complete functorial obstruction space $O_{\mathrm{fl}}^\delta$, with compatible lift torsors and an effective universal obstruction, then the minimal relation space satisfies

$$
\dim_k J/\mathfrak n J
\leq\dim_k O_{\mathrm{fl}}^\delta. \tag{13.2}
$$

Here

$$
P=\mathcal O[[X_1,\ldots,X_r]],
\qquad
\mathfrak n=\mathfrak m_{\mathcal O}P+(X_1,\ldots,X_r)
$$

is the source and its maximal ideal in the chosen minimal presentation (13.1), so $J/\mathfrak nJ$ is the minimal relation space.

The hypotheses attached to this inequality are substantive. A vector space containing necessary obstruction classes but not detecting all failures gives no such bound. Nor does vanishing of ambient $H^2$ automatically prove that integral models lift: the model obstruction may remain.

When every finite-flat object lifts across every small extension, the functor is formally smooth. In that case $J=0$. The proof uses the lifting criterion for maps out of a power-series ring: successively lift the universal point through the quotients by powers of the maximal ideal. Formal smoothness makes every relation removable, and completeness gives

$$
R_{\bar\rho}^{\mathrm{fl},\delta}
\simeq\mathcal O[[X_1,\ldots,X_r]]. \tag{13.3}
$$

Thus the two ingredients in a power-series conclusion are:

$$
\boxed{\text{formal smoothness}+\text{a correct tangent dimension}.}
$$

Neither ingredient implies the other.

### 13.3 Framing directions

Let

$$
h^0=\dim_kH^0(K,\operatorname{ad}\bar\rho)
=\dim_k\operatorname{End}_{k[G_K]}(\bar V).
$$

The exact sequence of §5.5 gives

$$
\dim_k t_{\bar\rho}^{\square,\mathrm{fl}}
=
\dim_kH^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
+d^2-h^0. \tag{13.4}
$$

For fixed determinant with $\ell\nmid d$, the same formula becomes

$$
\dim_k t_{\bar\rho}^{\square,\mathrm{fl},\delta}
=
\dim_kH^1_{\mathrm{fl}}(K,\operatorname{ad}^0\bar\rho)
+d^2-h^0. \tag{13.5}
$$

The term added by framing is $d^2-h^0$, not always $d^2-1$. It is the dimension of the strict-conjugacy orbit. If the residual endomorphisms are scalar, then $h^0=1$ and framing adds $d^2-1$ variables.

Under the scalar-centralizer hypothesis, the forgetful map from framed to unframed deformations is formally smooth with relative formal fiber the completion of $\operatorname{PGL}_d$ at the identity. Consequently there is a noncanonical isomorphism

$$
R_{\bar\rho}^{\square,\mathrm{fl},\delta}
\simeq
R_{\bar\rho}^{\mathrm{fl},\delta}
[[Y_1,\ldots,Y_{d^2-1}]]. \tag{13.6}
$$

**Proof strategy.** Lift an unframed deformation and then lift its frame. Two frames differ by an element of the congruence subgroup of $\operatorname{GL}_d$; scalar changes act trivially on the representation. The scalar-centralizer theorem says there are no further stabilizer directions.

Over a small extension, every matrix congruent to the identity lifts entrywise, so frames lift. The quotient of the matrix Lie algebra by scalars has dimension $d^2-1$. The smooth group scheme $\operatorname{PGL}_d$ has a formal coordinate system of that dimension at the identity. Choosing such coordinates trivializes the formal torsor and gives (13.6). The isomorphism depends on the coordinate choice; the relative dimension does not. $\square$

Fixed determinant does not reduce the number of framing variables. Conjugation preserves determinant, and strict conjugators are not required to have determinant one.

### 13.4 Rank two with fixed determinant

Assume now

$$
d=2,\qquad \ell>2,\qquad
\operatorname{End}_{k[G_K]}(\bar V)=k.
$$

Then the scalar line and trace-zero adjoint split:

$$
\operatorname{ad}\bar\rho
=k\cdot I\oplus\operatorname{ad}^0\bar\rho,
$$

and

$$
H^0(K,\operatorname{ad}^0\bar\rho)=0.
$$

Write

$$
r_{\mathrm{fl}}=
\dim_kH^1_{\mathrm{fl}}
(K,\operatorname{ad}^0\bar\rho).
$$

The unframed fixed-determinant ring has $r_{\mathrm{fl}}$ minimal generators, and the framed ring has $r_{\mathrm{fl}}+3$. If the unframed condition is formally smooth, then

$$
R_{\bar\rho}^{\mathrm{fl},\delta}
\simeq\mathcal O[[X_1,\ldots,X_{r_{\mathrm{fl}}}]], \tag{13.7}
$$

$$
R_{\bar\rho}^{\square,\mathrm{fl},\delta}
\simeq
\mathcal O[[X_1,\ldots,X_{r_{\mathrm{fl}}},
Y_1,Y_2,Y_3]]. \tag{13.8}
$$

The number three is a framing count. It is not a contribution from $[K:\mathbf Q_\ell]$ and it is not removed by fixing determinant.

### 13.5 The ambient upper bound and exceptional invariants

Local Euler characteristic and Tate duality give

$$
h^1(K,\operatorname{ad}^0\bar\rho)
=
3[K:\mathbf Q_\ell]
+h^0(K,\operatorname{ad}^0\bar\rho)
+h^0(K,\operatorname{ad}^0\bar\rho(1)).
$$

Under the scalar-centralizer and oddness hypotheses this becomes

$$
h^1(K,\operatorname{ad}^0\bar\rho)
=
3[K:\mathbf Q_\ell]
+h^0(K,\operatorname{ad}^0\bar\rho(1)). \tag{13.9}
$$

Therefore

$$
0\le r_{\mathrm{fl}}
\le
3[K:\mathbf Q_\ell]
+h^0(K,\operatorname{ad}^0\bar\rho(1)). \tag{13.10}
$$

The last invariant is an exceptional term. It is nonzero exactly when there is a $G_K$-map

$$
\bar V\longrightarrow\bar V(1)
$$

with trace-zero adjoint interpretation. It cannot be discarded merely because $\bar V$ is absolutely irreducible: the two irreducible representations can be twists of one another.

The expected type-$(0,1)$ tangent dimension $[K:\mathbf Q_\ell]$ is much smaller than the ambient $3[K:\mathbf Q_\ell]$. Equation (13.9) does not prove that expected value. It only checks that any proposed finite-flat formula fits inside the ambient space.

### 13.6 Characteristic two

When $\ell=2$ and $d=2$, the identity matrix has trace zero. Thus

$$
k\cdot I\subseteq\operatorname{ad}^0\bar\rho,
$$

and the direct sum used above fails. The fixed-determinant tangent is

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
\cap\ker\bigl(H^1(\operatorname{tr})\bigr),
$$

not automatically $H^1_{\mathrm{fl}}(K,\operatorname{ad}^0\bar\rho)$. Scalar infinitesimal automorphisms can lie in the trace-zero module, and subtraction of one from a centralizer dimension can be wrong.

The representability theorems of Chapter 9 remain available for framed problems in characteristic two, and for unframed problems under the usual scalar-centralizer hypothesis. What is unavailable is the simplified trace splitting and every dimension conclusion derived from it. No power-series theorem in this book silently includes $\ell=2$.

## 14. Low-ramification rigidity and integral classification

### 14.1 The decisive range and the three inputs

The general theory deliberately allowed a generic representation to have
several integral models. That caution remains indispensable over a ramified
base. The range needed for the rank-two calculation is much more rigid.
From now through §17.1 we assume

$$
K/\mathbf Q_\ell\text{ is unramified of degree }f,
\qquad R=\mathcal O_K=W(k_K),
\qquad \ell>2. \tag{14.1}
$$

Thus the absolute ramification index is $e(K)=1<\ell-1$. Three integral
ingredients become available:

- Raynaud full faithfulness identifies every morphism between finite-flat
  $\ell$-power group schemes with the corresponding morphism of generic
  fibers;
- the torsion Fontaine--Laffaille--Raynaud classification identifies the
  entire finite-flat category contravariantly with exact filtered
  divided-Frobenius linear algebra of weights $0$ and $1$;
- Matlis duality for a finite coefficient algebra converts that
  contravariant description into free coefficient-linear coordinates.

These inputs do different jobs. Raynaud's theorem removes model ambiguity
and extends coefficient endomorphisms. The classification theorem supplies
exactness, duality, and the admissible-annihilator operation representing a
nonflat coefficient quotient. Matlis duality reverses the arrows a second
time. It is this last step, rather than naive tensoring of the
contravariant module, that produces the free modules and line charts used
below.

The first two ingredients are the deep integral theorems established in the
preceding classification theory. Reproducing their crystalline and
syntomic constructions would duplicate that theory. We do prove the
coefficient-normal-form theorem deduced from them, because that deduction
is precisely where variance and nonflat coefficient reduction can
otherwise be lost. All subsequent tangent and lifting arguments are then
carried out directly in those coordinates.

The strict inequality in (14.1) matters twice. It is the hypothesis in the
Raynaud theorem, and it puts the weight interval $[0,1]$ inside the
Fontaine--Laffaille full-faithfulness range because

$$
1-0=1\leq \ell-2.
$$

This includes $\ell=3$. It does not include $\ell=2$, and no result below
silently does so.

### 14.2 Raynaud full faithfulness

We first isolate the rigidity theorem in the form needed throughout the
calculation.

**Theorem 14.1 (Raynaud low-ramification full faithfulness).** Let $R'$ be
the valuation ring of a finite extension $K'/\mathbf Q_\ell$ with absolute
ramification index

$$
e(K')<\ell-1.
$$

If $\mathcal G$ and $\mathcal H$ are finite flat commutative $R'$-group
schemes of $\ell$-power order, then restriction to the generic fiber is a
bijection

$$
\operatorname{Hom}_{R'}(\mathcal G,\mathcal H)
\xrightarrow{\ \sim\ }
\operatorname{Hom}_{K'}(\mathcal G_{K'},\mathcal H_{K'}). \tag{14.2}
$$

Equivalently, after identifying finite étale generic fibers with finite
$G_{K'}$-modules, every equivariant homomorphism of generic point modules
extends uniquely to the integral group schemes.

The word **full** is decisive. Generic-fiber faithfulness alone proves that
an extension, if it exists, is unique. The theorem also proves existence.
It immediately yields the following consequences.

**Corollary 14.2 (unique model and unique structure).** Under the hypotheses
of Theorem 14.1:

1. two finite-flat models of one fixed generic finite étale group are
   uniquely isomorphic through the prescribed generic identification;
2. every generic automorphism or endomorphism extends uniquely;
3. every algebraic identity among generic endomorphisms holds among their
   integral extensions;
4. a generic perfect pairing into $\mu_{\ell^n}$ extends uniquely to a
   Cartier pairing, and a generic isomorphism with a Cartier dual extends
   to an integral isomorphism.

**Proof.** For the first assertion, extend the generic isomorphism in one
direction and its inverse in the other. Their composites restrict to the
identity on the generic fiber, so faithfulness makes the composites the
integral identities. The second assertion is (14.2). For the third, extend
the endomorphisms occurring in both sides of the proposed identity; the two
composites agree generically and therefore agree integrally. For the final
assertion, regard a pairing as a map to a Cartier dual, use the compatibility
of Cartier duality with generic fibers from Book 47, and apply the first
three assertions. $\square$

Since $e(K)=1$, Corollary 14.2 applies to every model in our deformation
problem, at every Artinian coefficient level. Consequently the groupoid of
finite-flat representations equipped with a selected model maps
equivalently to the groupoid of finite-flat representations for which a
model merely exists. A fixed generic representation has one model up to a
unique generic-compatible isomorphism. The distinction maintained in
Chapters 1--13 has not disappeared in general; it has been resolved by a
theorem under (14.1).

### 14.3 Why roots of unity do not contradict rigidity

The standard nonuniqueness example is

$$
\underline{\mathbf Z/\ell\mathbf Z}_R
\quad\text{and}\quad
\mu_\ell.
$$

If $K$ contains $\zeta_\ell$, their generic $G_K$-modules are both trivial,
while their special fibers are respectively étale and connected. This does
not contradict Theorem 14.1. The extension

$$
\mathbf Q_\ell(\zeta_\ell)/\mathbf Q_\ell
$$

is totally ramified of degree $\ell-1$. Any finite extension containing it
has absolute ramification index at least $\ell-1$; in fact that index is a
multiple of $\ell-1$. It lies exactly outside the strict inequality in the
theorem.

For an unramified $K$, the standard $\Lambda_n$-valued cyclotomic and
trivial lines therefore have unique models: $\mu_{\ell^n}$ and the constant
$\Lambda_n$-group, respectively. Coefficient extensions have the unique
scalar-extended models.

This observation will later turn the endpoint-relative Kummer calculation
of Chapter 12 into an intrinsic exclusion of the valuation class.

### 14.4 The covariant divided Fontaine--Laffaille category

Raynaud gives rigidity but not coordinates. Coordinates come from the
integral torsion classification. We first define its linear side in a form
that never divides an element of a torsion module by $\ell$.

For $A\in\operatorname{Art}_{\mathcal O}$ put

$$
S_A=R\otimes_{\mathbf Z_\ell}A.
$$

The unramifiedness of $R$ makes $S_A$ finite étale of rank $f$ over $A$.
Let $\sigma$ act by Witt-vector Frobenius on $R$ and trivially on $A$.

A **coefficient-flat divided Fontaine--Laffaille object of weights
$[0,1]$** is a triple

$$
\mathcal M=(M,L,\Phi) \tag{14.3}
$$

with the following data:

- $M$ is a finite projective $S_A$-module;
- $L\subset M$ is an $S_A$-direct summand;
- after defining

  $$
  D_L(M)=
  \frac{L\oplus M}
  {\langle(\ell x,-x):x\in L\rangle}, \tag{14.4}
  $$

  the divided Frobenius is an $S_A$-linear isomorphism

  $$
  \Phi:S_A\otimes_{\sigma,S_A}D_L(M)
  \xrightarrow{\ \sim\ }M. \tag{14.5}
  $$

A normal decomposition $M=L\oplus N$ identifies $D_L(M)$ with $L\oplus N$:
if $y=y_L+y_N$, then

$$
[x,y]\longmapsto(x+\ell y_L,y_N). \tag{14.6}
$$

Thus $D_L(M)$ is projective of the same rank as $M$. Formula (14.4), not an
expression $F/\ell$ on a torsion module, is the integral meaning of divided
Frobenius. Once a normal decomposition is chosen, the first block of the
matrix of $\Phi$ records the weight-one divided map and the second records
the weight-zero map. Invertibility of (14.5) is strong divisibility.

A morphism $u:(M,L,\Phi)\to(M',L',\Phi')$ is an $S_A$-linear map carrying
$L$ into $L'$ and satisfying

$$
u\Phi=\Phi'(1\otimes D(u)). \tag{14.7}
$$

Admissible exact sequences are exact on $M$ and on $L$, with projective
quotients. Normal decompositions show that $D_L$ preserves such sequences.
The case $L=0$ is pure weight zero and corresponds to the étale part. The
case $L=M$ is pure weight one and corresponds to multiplicative type.
Intermediate direct summands and nonblock-diagonal Frobenius matrices include
connected and mixed objects; the category is not an ordinary-only category.
Tate twisting shifts both filtration indices and generic realization, giving
the corresponding categories with weights in an interval $[a,b]$; only the
interval length $b-a$ enters the full-faithfulness bound below.

The word **covariant** here conceals a step which must be made explicit. Let

$$
\omega_A=\operatorname{Hom}_{\mathbf Z_\ell}
(A,\mathbf Q_\ell/\mathbf Z_\ell)
$$

be the coefficient Matlis module and put

$$
\omega_{S_A}=R\otimes_{\mathbf Z_\ell}\omega_A.
$$

The trace pairing for the finite unramified algebra
$R/\mathbf Z_\ell$ identifies $\omega_{S_A}$ with the Matlis module of
$S_A$. Therefore

$$
N\longmapsto N^\dagger
=\operatorname{Hom}_{S_A}(N,\omega_{S_A}) \tag{14.8}
$$

is an exact duality on finite-length $S_A$-modules. If $B=A/I$, then

$$
\omega_B=\omega_A[I]. \tag{14.9}
$$

This identity is the algebraic reason a quotient of the generic
representation becomes ordinary tensor reduction after the contravariant
classified object has been dualized. Before dualizing, the correct object
is the admissible annihilator, not a tensor product.

Dualizing the strict Hodge sequence and its normal divided-Frobenius map
transports the established contravariant structure to triples
$(M,L,\Phi)$. In rank two with one Hodge direction, the dual Hodge quotient
and the dual Hodge submodule are both lines. In an adapted normal
decomposition, the new divided-Frobenius matrix is the transpose inverse of
the old normal matrix, with the Frobenius indices shifted. This makes the
arrow covariant and preserves invertibility. Formula (14.4) is the
coordinate-free record of the transported divided map.

This construction fixes the normalization used below: a map of finite-flat
groups induces a map in the same direction on $\mathcal M$, the trivial
line has weight zero, and the cyclotomic line has weight one. Ordinary
tensor reduction on the covariant module will be a theorem, not a
convention.

If a finite unramified coefficient extension splits $S_A$, its factors are
indexed by embeddings $\tau:k_K\hookrightarrow k'$ and

$$
M=\prod_\tau M_\tau,
\qquad
L=\prod_\tau L_\tau.
$$

The integer

$$
r_\tau=\operatorname{rank}L_\tau
$$

is the filtration rank at $\tau$. Frobenius cyclically permutes these
factors.

### 14.5 The coefficient-normal-form theorem

The following theorem is the precise bridge needed for deformation theory.
Its rank-two hypothesis is intentional. The general contravariant
anti-equivalence is already available; the free covariant chart is needed
here only in height two.

**Theorem 14.3 (rank-two coefficient normal form).** Assume (14.1), fix a
finite-flat residual representation $\bar V$ of dimension two over $k$, and
suppose its unique residual filtered object has one Hodge direction at every
residue embedding. For every $A\in\operatorname{Art}_{\mathcal O}$, the
following groupoids are equivalent:

1. finite-flat $A[G_K]$-modules $V_A$ free of rank two and reducing to
   $\bar V$, with their generic markings;
2. coefficient-flat triples $(M,L,\Phi)$ of §14.4, with $M$ projective of
   rank two over $S_A$, $L$ and $M/L$ projective of rank one on every
   factor, and a fixed identification with the residual triple.

The equivalence is covariant and generically fully faithful. If $B=A/I$,
then

$$
\mathcal M_B\simeq\mathcal M_A\otimes_A B. \tag{14.10}
$$

It commutes with finite unramified ground-field extension, finite étale
coefficient extension, and their descent data. Conversely every triple in
(2) has generic realization free of rank two over $A$ and gives a unique
marked finite-flat model. Write $T_A(\mathcal M)$ for that covariant generic
realization.

For such a triple, the internal coefficient-linear dual is

$$
\mathcal M^D=
\operatorname{Hom}_{S_A}(M,S_A(1)) \tag{14.11}
$$

with annihilator filtration and inverse-adjoint divided Frobenius. Its
generic realization is

$$
T_A(\mathcal M^D)
\simeq\operatorname{Hom}_A(T_A(\mathcal M),A)(1), \tag{14.12}
$$

and its filtration rank is $2-r_\tau$. This internal dual is not the
ordinary Cartier dual when $A$ is non-Gorenstein.

**Proof strategy.** Begin with the established contravariant torsion
classification, use its admissible annihilators for coefficient quotients,
and then apply the exact Matlis duality (14.8). Freeness is proved by a
Nakayama-and-length argument. Finally dualize the strict normal map to
obtain the divided map (14.5).

**Proof.** Let $C_A$ be the contravariant divided filtered object attached to
a model of $V_A$. The $A$-action on the model gives a commuting $A$-action
on $C_A$. Put

$$
M_A=\operatorname{Hom}_{S_A}(C_A,\omega_{S_A}). \tag{14.13}
$$

The torsion classification is exact and its realization is fully faithful.
For $B=A/I$, it represents $V_A/IV_A$ not by a naive tensor product of
$C_A$, but by the terminal admissible $I$-killed subobject
$C_A[I]_{\mathrm{adm}}$. Restriction of Matlis-dual functionals gives a
natural comparison

$$
\operatorname{Hom}_{S_B}
(C_A[I]_{\mathrm{adm}},\omega_{S_B})
\longleftarrow M_A/IM_A. \tag{14.14}
$$

We prove simultaneously that $M_A$ is projective and that (14.14) is an
isomorphism. Factor $A\twoheadrightarrow k$ into principal small
extensions and induct on the length of $A$. For one step
$A\twoheadrightarrow B$ with kernel $J$, the free representation has the
coefficient exact sequence

$$
0\longrightarrow J\otimes_k\bar V
\longrightarrow V_A\longrightarrow V_B\longrightarrow0. \tag{14.14a}
$$

The classification turns it into a strict exact sequence with arrows
reversed; Matlis duality reverses them again. Full faithfulness identifies
the first arrow with multiplication by $J$. Consequently the kernel of
$M_A\to M_B$ is exactly $J\otimes_k\bar M$, and the local flatness
criterion gives

$$
M_A\otimes_A B\xrightarrow{\sim}M_B. \tag{14.14b}
$$

For completeness, choose a basis of the free $B$-module $M_B$ supplied by
the induction hypothesis and lift it to $M_A$. Any relation among the
lifts has coefficients in $J$. Its image in the first term of the dual of
(14.14a) is the corresponding relation among a residual basis, so every
coefficient is zero. The lifts are therefore a basis of $M_A$. This proves
freeness at the small step. Iteration proves (14.14) and (14.10) for every
ideal $I$.

After a finite étale coefficient extension splitting $S_A$, the argument
applies on each factor and gives rank two. Faithfully flat descent makes
$M_A$ projective of rank two over $S_A$ before splitting. Notice that the
proof used the admissible annihilator and the exact coefficient sequence;
it never identified $C_A[I]_{\mathrm{adm}}$ with the raw annihilator
$C_A[I]$.

The strict Hodge sequence for $C_A$ and its strict normal
divided-Frobenius isomorphism dualize exactly. The residual Hodge ranks are
one by hypothesis. Exactness, (14.14), and Nakayama show that the transported
Hodge term and quotient are projective of rank one at every Artinian level.
Writing the transported structure using the quotient (14.4) gives an
isomorphism $\Phi$ as in (14.5). A normal decomposition verifies directly
that the two constructions are inverse: dualizing twice recovers $C_A$, and
the transpose-inverse normal matrix recovers the original strong-divisibility
map.

Conversely, start with $(M,L,\Phi)$. Matlis duality reconstructs an
admissible contravariant torsion object. The integral classification
represents it by a finite-flat group. The same length calculation and
Nakayama show that its generic realization is free of rank two over $A$.
Full faithfulness on the contravariant side and exactness of Matlis duality
give full faithfulness and covariance here. Ground-field and finite étale
coefficient descent commute with every construction used. This proves the
equivalence and all stated compatibilities.

For the internal dual, projectivity of $M$ makes (14.11) exact. The
annihilator filtration and inverse-adjoint matrix give another
coefficient-flat triple, with complementary filtration ranks. The generic
comparison follows from tensor--Hom adjunction and full faithfulness.
Ordinary Cartier duality instead uses the Pontryagin dualizing module
$\omega_A$; replacing it by $A$ is legitimate only after a Gorenstein
self-duality has been chosen. This proves the final assertions. $\square$

For type $(0,1)$, exterior multiplication gives a rank-one weight-one
object. Under a normal decomposition its divided-Frobenius scalar is
$\det\Phi$, and

$$
T_A(\det\mathcal M)\simeq\det_A T_A(\mathcal M). \tag{14.15}
$$

This rank-two assertion needs no general exterior-power theory. The
alternating map $M\times M\to\det M$ is perfect, its generic realization is
the ordinary determinant pairing, and full faithfulness identifies the
rank-one target.

### 14.6 Why the classification has the stated compatibilities

Theorem 14.3 is a consequence of established integral infrastructure, but
its proof architecture explains why each clause is trustworthy and why
simpler substitutes fail.

The contravariant construction from a group scheme begins with its crystalline
Dieudonné object, evaluated on the canonical divided-power thickenings of
the unramified base. The Hodge sequence cuts out $L$, while Frobenius and
Verschiebung supply the two adjacent divided maps. Their integral relation
is encoded by the usual strict normal map. Matlis duality then reverses the
arrow without choosing a self-duality of the coefficient ring. In rank two,
the transported Hodge quotient and Hodge submodule both have rank one;
$D_L(M)$ and (14.5) record the resulting covariant structure. This is why
the chart remains valid over non-Gorenstein test rings.

The reverse construction associates a finite flat group sheaf to a torsion
filtered module by the integral Fontaine--Laffaille syntomic construction.
Its representability and finite flatness are substantial theorems. They use
the fundamental crystalline comparison sequence and the strict weight
bound to control integral denominators. The quasi-inverse comparison is
proved on the integral crystalline and syntomic sites and then descended.
It is not obtained by selecting a solution of one semilinear equation, nor
by defining an operator $F/\ell$ on an $\ell$-torsion module.

Exactness is proved simultaneously with the comparison. On the group side
one uses faithfully flat exact sequences, not arbitrary raw kernels or
images. On the linear side one uses exactness of both $M$ and its Hodge
submodule $L$. The comparison identifies these exact structures. As a
result, connected, étale, multiplicative, and mixed pieces survive the
same theorem; there is no need to split an object into Frobenius-stable
filtration subquotients, which generally do not exist.

Compatibility through all $\ell^n$-torsion levels comes from carrying out
the construction in the torsion crystalline category and using devissage
in $n$. No rationalization is involved. The bound on the weight interval
makes the comparison morphisms integral at each step, so the transition
from level $n+1$ to level $n$ agrees with coefficient reduction.

Ordinary Cartier duality is visible on the crystalline object through its
evaluation pairing into roots of unity. Separately, dualizing a finite
projective coefficient-flat module into the weight-one coefficient object
gives the internal $A$-linear dual in (14.11). Its annihilator filtration
gives complementary ranks, and inverse-adjoint divided Frobenius gives the
dual structure. Exactness of ordinary Cartier duality is inherited from
Book 47; generic compatibility of the internal coefficient-linear dual was
proved in Theorem 14.3. Determinants in rank two are
then exterior pairings into a rank-one weight-one object; the determinant
of a divided-Frobenius matrix is therefore the correct scalar, not a formal
analogy with ordinary semilinear algebra.

Finally, coefficient actions are endomorphisms in the classified category.
A quotient $A\to A/I$ is implemented integrally on group schemes by the
saturated coefficient quotient of Chapter 2. On the contravariant filtered
object it is the admissible annihilator, not tensor product. Equation
(14.14) proves that Matlis duality converts precisely that object into
$M/IM$. Thus the absence of a hidden $\operatorname{Tor}$ term is proved,
not assumed. The length and Nakayama argument then gives projectivity of
$M$, $L$, and $M/L$. This is the coefficient-flatness that allows line and
matrix coordinates below.

This overview names the essential constructions and the reason for every
compatibility used later. The deep representability and comparison theorems
remain inputs. The deformation consequences, beginning with the next lemma,
will be proved directly.

### 14.7 Coefficient enhancement and coefficient quotients

The first consequence combines Raynaud rigidity with the covariant
classification.

**Lemma 14.4 (coefficient enhancement and uniqueness).** Let $A$ be an
Artinian coefficient ring and let $V_A$ be a finite free $A[G_K]$-module.
If the underlying finite $G_K$-module has a finite-flat model $\mathcal G$,
then assertions 1 and 2 below hold in every rank. If $V_A$ has rank two and
its residual object has one Hodge direction at each embedding, all four
assertions hold:

1. every scalar $a\in A$ extends uniquely to an endomorphism of $\mathcal G$;
2. these extensions give the unique $A$-action on $\mathcal G$ compatible
   with the generic action;
3. $\mathcal M_A$ is an $S_A$-linear
   coefficient-flat object, functorial under all coefficient quotients;
4. for $B=A/I$,

   $$
   \mathcal M_B\simeq\mathcal M_A\otimes_A B. \tag{14.16}
   $$

**Proof.** The additive group of $V_A$ has $\ell$-power order. For each
$a\in A$, multiplication by $a$ is a $G_K$-equivariant endomorphism of its
finite étale generic group. Theorem 14.1 extends it uniquely to
$[a]_{\mathcal G}\in\operatorname{End}_R(\mathcal G)$.

For $a,b\in A$, the two integral maps

$$
[a+b]_{\mathcal G}
\quad\text{and}\quad
[a]_{\mathcal G}+[b]_{\mathcal G}
$$

agree generically, as do $[ab]_{\mathcal G}$ and
$[a]_{\mathcal G}[b]_{\mathcal G}$. The extensions of $0$ and $1$ are the
zero and identity maps for the same reason. Generic faithfulness therefore
proves all ring laws. It also proves uniqueness of the action.

Apply Theorem 14.3. Functoriality carries the $A$-action to an $S_A$-module
structure, and its length--Nakayama argument gives coefficient-flatness.
For a quotient $B=A/I$, the admissible-annihilator calculation (14.14)
identifies the saturated coefficient quotient of $\mathcal G$ with ordinary
tensor reduction on the covariant module, giving (14.16). $\square$

In the range (14.1), this lemma is stronger than the general
coefficient-saturation construction of §2.1: it does not replace the model
by a closure in a large product. The unique model itself carries every
coefficient endomorphism. The general construction remains necessary
outside the Raynaud range.

### 14.8 Cyclotomic determinant forces type $(0,1)$

The normal form in the next chapter uses a line in every unramified factor.
That line is a consequence of the determinant condition, not an additional
Hodge-type hypothesis.

**Lemma 14.5 (type forced by the determinant).** Let $\bar V$ be
two-dimensional, finite flat, and satisfy

$$
\det\bar V=k(1). \tag{14.17}
$$

Then its residual filtered object has one Hodge direction at every
embedding, so Theorem 14.3 applies to its rank-two finite-flat deformations.
If $V_A$ is such a deformation with $\det V_A=A(1)$, its classified object
$\mathcal M_A$ has

$$
\operatorname{rank}_{S_A}M=2,
\qquad
r_\tau=\operatorname{rank}L_\tau=1
\quad\text{for every }\tau. \tag{14.18}
$$

**Proof.** Exterior multiplication and the residual determinant identification
give a perfect alternating $G_K$-equivariant pairing

$$
\bar V\times\bar V\longrightarrow k(1), \tag{14.19}
$$

or equivalently an isomorphism

$$
\bar V\xrightarrow{\ \sim\ }\bar V^*(1). \tag{14.20}
$$

Compose the pairing with the nonzero field trace
$k\to\mathbf F_\ell$. Nondegeneracy of the trace pairing makes the result a
perfect pairing of the underlying $\mathbf F_\ell$-spaces into
$\mathbf F_\ell(1)$. Raynaud full faithfulness extends its adjoint generic
isomorphism to the ordinary Cartier dual of the unique residual model. The
torsion classification carries Cartier duality to the
Cartier-normalized filtered dual, whose Hodge rank is $2-r_\tau$. Hence
self-duality gives

$$
r_\tau=2-r_\tau.
$$

Therefore $r_\tau=1$ for every embedding at the residual level. Theorem
14.3 now applies and makes the transported Hodge term of every lift a
direct-summand line. If the lifted determinant is cyclotomic, the perfect
$A$-linear alternating pairing identifies the covariant object with its
internal dual (14.11), so the same rank equation holds at the lifted level.
Coefficient reduction (14.10) preserves the conclusion. $\square$

The same argument works for residual, Artinian, and higher $\ell^n$ levels.
It treats ordinary and supersingular objects uniformly.

## 15. Normal forms, determinant, and the tangent complex

### 15.1 Splitting the unramified embeddings

We now calculate deformations of a fixed residual representation

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_2(k),
\qquad
\det\bar\rho=\bar\chi_\ell, \tag{15.1}
$$

assumed finite flat. Raynaud rigidity and the integral torsion
classification attach to it one residual object $\bar{\mathcal M}$ up to
unique isomorphism. Lemma 14.5 verifies the Hodge-rank hypothesis needed to
apply Theorem 14.3 to its deformations.

Choose once and for all a finite unramified extension of the coefficient
ring large enough to contain every residue embedding of $k_K$. Faithfully
flat scalar extension then gives

$$
S_A\simeq\prod_{i\in\mathbf Z/f\mathbf Z}A, \tag{15.2}
$$

with $\sigma$ carrying factor $i$ to factor $i+1$. All constructions are
equivariant under descent, and tangent dimensions are unchanged by this
faithfully flat extension. We may therefore calculate with the split
factors and then descend the result.

Lemma 14.5 first gives filtration rank one for the residual object. In any
coefficient deformation, $L$ and $M/L$ remain projective and their ranks are
locally constant; since every Artinian test ring here is local, reduction to
the residual object forces the same rank one even before the determinant is
fixed at the lifted level. Thus the data in factor $i$ are

$$
M_i=A^2,
\qquad
L_i\subset M_i\text{ a direct-summand line},
\qquad
\Phi_i:D_{L_i}(M_i)\xrightarrow{\ \sim\ }M_{i+1}. \tag{15.3}
$$

The cyclic shift is the linear shadow of Witt Frobenius. It must remain in
every change-of-basis formula.

### 15.2 The based normal form and its $5f$ parameters

Choose bases $\bar e_i,\bar f_i$ of the residual factors with

$$
\bar L_i=k\bar e_i,
$$

and choose fixed lifts $e_i,f_i$. A **based lift** includes identifications
$M_i\simeq A^2$ reducing to these residual bases. Every direct-summand line
lifting $\bar L_i$ is uniquely the graph

$$
L_i=A(e_i+x_i f_i),
\qquad x_i\in\mathfrak m_A. \tag{15.4}
$$

Use $e_i+x_if_i,f_i$ as a normal decomposition. Formula (14.6) gives the
corresponding divided source basis. Relative to that basis and the chosen
basis of $M_{i+1}$, $\Phi_i$ is an arbitrary invertible lift of the residual
matrix:

$$
\Phi_i=\widetilde{\bar\Phi}_i+
\begin{pmatrix}
a_{i,11}&a_{i,12}\\
a_{i,21}&a_{i,22}
\end{pmatrix},
\qquad a_{i,rs}\in\mathfrak m_A. \tag{15.5}
$$

It remains invertible because its determinant is a unit modulo
$\mathfrak m_A$. Conversely, (15.4) and any matrices (15.5) define an
object (15.3). Strong divisibility contributes no further equation:
invertibility of $\Phi_i$ is the strong-divisibility condition itself.

Thus each factor contributes one line parameter and four matrix parameters.
The completed based presentation space is formally smooth of relative
dimension

$$
f+4f=5f. \tag{15.6}
$$

A complement was used to write a matrix, but it is not part of the object.
Changing it changes the divided basis through the functor $D_L$. Most
importantly, $\Phi_i$ is primitive structure on $D_{L_i}(M_i)$. At no point
is it defined by dividing a Frobenius operator by $\ell$ on a torsion
module.

### 15.3 The single determinant equation

The determinant condition is one cyclic equation, not one equation per
embedding. We prove both assertions.

First consider a rank-one weight-one object. After choosing bases, write its
divided-Frobenius scalars as

$$
q_i\in A^\times,
\qquad i\in\mathbf Z/f\mathbf Z.
$$

An isomorphism to a second object with scalars $q_i'$ is a collection of
units $b_i$ satisfying

$$
b_{i+1}q_i=q_i'b_i. \tag{15.7}
$$

Starting from $b_0$, the first $f-1$ equations determine the other $b_i$.
The last equation is soluble precisely when

$$
\prod_iq_i=\prod_iq_i'. \tag{15.8}
$$

Thus the cyclic product is the complete isomorphism invariant of a
rank-one weight-one object in split coordinates.

For a rank-two type-$(0,1)$ object, exterior multiplication carries the
normal divided basis to the determinant line. The determinant scalar in
factor $i$ is therefore

$$
q_i=\det\Phi_i. \tag{15.9}
$$

This does not depend on the chosen complement. Replacing a complement
vector by itself plus a multiple of the filtration vector changes the
second exterior factor by a multiple of the first, whose wedge is zero.
It also follows directly from the determinant compatibility (14.15).

Choose bases of the cyclotomic rank-one object and write its scalars as
$c_i$. Put

$$
c_\chi=\prod_i c_i\in\mathcal O^\times. \tag{15.10}
$$

Equations (15.8)--(15.9) show that fixed cyclotomic determinant is exactly

$$
\boxed{\prod_{i=0}^{f-1}\det\Phi_i=c_\chi.} \tag{15.11}
$$

There is only one equation because the other $f-1$ scalar discrepancies
are removed by the units $b_i$ in (15.7).

The equation has surjective derivative at every residual point. If
$\dot\Phi_i$ is a first-order variation, its logarithmic derivative is

$$
\lambda((\dot\Phi_i)_i)
=
\sum_i\operatorname{tr}
(\bar\Phi_i^{-1}\dot\Phi_i). \tag{15.12}
$$

Given $t\in k$, take

$$
\dot\Phi_0=\bar\Phi_0
\begin{pmatrix}t&0\\0&0\end{pmatrix},
\qquad
\dot\Phi_i=0\quad(i\ne0).
$$

Then $\lambda=t$. Hence the fixed-determinant based space is a smooth
hypersurface of relative dimension

$$
5f-1. \tag{15.13}
$$

This calculation is also the infinitesimal form of the determinant
correction used in Chapter 16.

### 15.4 Gauge transformations and generic frames

The bases of the $M_i$ are auxiliary. Put

$$
\mathscr H_A=\prod_{i\in\mathbf Z/f\mathbf Z}\operatorname{GL}(M_i).
$$

For the deformation problem one uses its congruence subgroup, consisting of
tuples reducing to the identity on the chosen residual factors. Equivalently,
all tangent and completed-local calculations use the formal completion of
$\mathscr H$ at the identity; its relative dimension is $4f$.

If $g_i:M_i\to M_i$ changes the basis and sends $L_i$ to $g_iL_i$, it
induces canonically

$$
\widetilde g_i=D(g_i):D_{L_i}(M_i)
\xrightarrow{\ \sim\ }D_{g_iL_i}(M_i).
$$

The gauge action is

$$
\boxed{
\Phi_i\longmapsto
 g_{i+1}\Phi_i\widetilde g_i^{-1}.} \tag{15.14}
$$

The target index $i+1$ is essential. Independent conjugations
$g_i\Phi_i g_i^{-1}$ would not describe an isomorphism of
Fontaine--Laffaille objects.

In bases adapted to the source and target lines, $g_i$ is block upper
triangular and $D(g_i)$ multiplies its upper-right block by $\ell$ while
leaving the diagonal blocks unchanged. Hence
$\det D(g_i)=\det g_i$. Taking determinants in (15.14) gives

$$
\det\Phi_i\longmapsto
(\det g_{i+1})(\det\Phi_i)(\det g_i)^{-1}. \tag{15.15}
$$

The product telescopes, proving directly that (15.11) is gauge-invariant.
The stabilizer of a point is its automorphism group in the classified
category. By generic full faithfulness in Theorem 14.3,

$$
\operatorname{Aut}_{\mathsf{MF}}(\mathcal M)
\simeq
\operatorname{Aut}_{A[G_K]}(T_A(\mathcal M)), \tag{15.16}
$$

and at the residual point its tangent algebra is

$$
\operatorname{End}_{\mathsf{MF}}(\bar{\mathcal M})
\simeq
\operatorname{End}_{k[G_K]}(\bar V). \tag{15.17}
$$

Write

$$
h=\dim_k\operatorname{End}_{k[G_K]}(\bar V). \tag{15.18}
$$

A framed Galois deformation includes, in addition, a basis of
$T_A(\mathcal M)$ lifting the fixed residual basis. The space of such
bases contributes four smooth parameters. Gauge acts simultaneously on the
internal bases and on this generic frame. The action on the pair is free:
a stabilizer fixing the generic frame induces the identity on
$T_A(\mathcal M)$ and is therefore the identity by full faithfulness.
This is how framing kills the entire stabilizer, including nonscalar
stabilizers at a split point.

More precisely, based data together with a generic frame, modulo the action
of $\mathscr H_A$, form the framed finite-flat deformation groupoid.
Essential surjectivity follows by applying Theorem 14.3 to a finite-flat
representation and choosing bases of its projective factors. A morphism of
two classified objects is, after those choices, exactly a tuple $(g_i)_i$
satisfying (15.14); generic full faithfulness says that there are no further
morphisms. Requiring compatibility with the generic frame makes such a
tuple unique. Thus the quotient description is an equivalence of groupoids,
not merely a dimension heuristic.

### 15.5 The tangent complex

We now turn the preceding parameter and gauge calculations into the exact
tangent dimensions. At the residual object define

$$
C^0=\bigoplus_i\operatorname{End}_k(\bar M_i), \tag{15.19}
$$

and

$$
C^1=
\bigoplus_i\operatorname{Hom}_k
(\bar L_i,\bar M_i/\bar L_i)
\oplus
\bigoplus_i\operatorname{End}_k(\bar M_{i+1}). \tag{15.20}
$$

The first summand records the derivative of the line and the second the
derivative of the divided-Frobenius matrix. Consequently

$$
\dim_kC^0=4f,
\qquad
\dim_kC^1=f+4f=5f. \tag{15.21}
$$

Differentiating the gauge action gives a map

$$
d:C^0\longrightarrow C^1. \tag{15.22}
$$

For $X=(X_i)_i$, its line component sends

$$
x\in\bar L_i\longmapsto X_i(x)\bmod\bar L_i,
$$

and its matrix component is

$$
X_{i+1}\bar\Phi_i-
\bar\Phi_i\widetilde X_i, \tag{15.23}
$$

where $\widetilde X_i$ is the differential of the canonical map induced by
$D$ while the line moves. Formula (15.23) is the linearization of (15.14),
so it includes the variation of the divided source; it is not ordinary
conjugation.

An element lies in $\ker d$ exactly when it is an infinitesimal
automorphism of $\bar{\mathcal M}$. Full faithfulness gives

$$
\ker d\simeq\operatorname{End}_{k[G_K]}(\bar V),
\qquad
\dim_k\ker d=h. \tag{15.24}
$$

Every first-order based deformation is an element of $C^1$, and two such
deformations define the same unframed deformation exactly when their
difference is an infinitesimal gauge transformation. The exact
classification therefore identifies the unrestricted finite-flat tangent
with

$$
\operatorname{coker}d.
$$

It follows that

$$
\boxed{
\dim_kH^1_{\mathrm{fl}}(K,\operatorname{ad}\bar\rho)
=5f-(4f-h)=f+h.} \tag{15.25}
$$

This is an equality for the full existential finite-flat condition because
Raynaud has identified that condition with the unique-model classified
condition.

### 15.6 The fixed-determinant and framed dimensions

The differential $\lambda:C^1\to k$ in (15.12) is surjective. It vanishes
on $\operatorname{im}d$: differentiating (15.15) gives a telescoping cyclic
sum. Thus the fixed-determinant unframed tangent is

$$
\ker\lambda/\operatorname{im}d.
$$

Using (15.21) and (15.24),

$$
\boxed{
\dim_kH^1_{\mathrm{fl}}
(K,\operatorname{ad}^0\bar\rho)
=(5f-1)-(4f-h)=f+h-1.} \tag{15.26}
$$

Here $\ell>2$ permits the trace splitting which identifies the ordinary
fixed-determinant tangent with the displayed trace-zero cohomological
notation. The quotient calculation itself is the primary statement.

For the framed tangent, add the four-dimensional variation of the generic
basis before taking the gauge quotient. The resulting gauge differential

$$
C^0\longrightarrow
\ker\lambda\oplus\operatorname{End}_k(\bar V) \tag{15.27}
$$

is injective. Indeed, an element in its kernel is an infinitesimal
automorphism acting trivially on the generic frame, hence is zero by
(15.17). Therefore

$$
\boxed{
\dim_k t^{\square,\mathrm{fl},\chi_\ell}_{\bar\rho}
=(5f-1)+4-4f=f+3.} \tag{15.28}
$$

Equivalently, framing adds

$$
4-h
$$

directions to the coarse fixed-determinant tangent, and

$$
(f+h-1)+(4-h)=f+3. \tag{15.29}
$$

The cancellation of $h$ is structural. Split and irreducible residual
points have the same framed tangent dimension even though their unframed
coarse tangents differ.

## 16. Small extensions and the residual-shape audit

### 16.1 Explicit lifting through a small extension

Tangent dimensions become power-series dimensions only after higher-order
liftability has been proved. Here that proof is completely explicit.

Let

$$
0\longrightarrow I\longrightarrow B\longrightarrow A\longrightarrow0
\tag{16.1}
$$

be a small extension, and let a finite-flat rank-two deformation over $A$
with determinant $\chi_\ell$ be given. Raynaud and Theorem 14.3 attach to it
one type-$(0,1)$ object. Choose based split-factor data as in (15.3).

First lift each line. In the chart (15.4), choose any
$\widetilde x_i\in\mathfrak m_B$ mapping to $x_i$. Then

$$
\widetilde L_i=B(e_i+\widetilde x_if_i)
$$

is a direct-summand line lifting $L_i$.

Second lift every entry of every matrix $\Phi_i$ arbitrarily to a matrix
$\widetilde\Phi_i$ over $B$. Its determinant reduces to a unit, so it is a
unit. Hence every $\widetilde\Phi_i$ is invertible and the lifted data are
strongly divisible.

Third correct the sole determinant equation. The ratio

$$
u=
\frac{c_\chi}{\prod_i\det\widetilde\Phi_i}
\in1+I \tag{16.2}
$$

reduces to $1$. Replace one matrix, say the zeroth, by

$$
\widetilde\Phi_0
\operatorname{diag}(u,1)
=
\widetilde\Phi_0
\begin{pmatrix}u&0\\0&1\end{pmatrix}. \tag{16.3}
$$

Its reduction is unchanged, its determinant is multiplied by $u$, and
(15.11) now holds exactly. No other equation is disturbed.

Finally suppose the original deformation was framed. The generic
realization of the lifted coefficient-flat object is free of rank two over
$B$ and reduces to the original generic module by (14.10). Lift the two
vectors of the generic frame. Nakayama's lemma makes them a basis, or
equivalently the surjection

$$
\operatorname{GL}_2(B)\longrightarrow\operatorname{GL}_2(A)
$$

lifts the frame.

The split calculation is intrinsic. Without splitting $S_B$, lines lift
because the relative Grassmannian of direct-summand lines is smooth, and
invertible divided-Frobenius maps lift because the relevant general linear
group is smooth. For the determinant correction, rank-one isomorphism
classes are measured by the norm from the finite étale algebra $S_B$ to
$B$. On $1+I S_B$ the norm is

$$
1+x\longmapsto1+\operatorname{Tr}_{S_k/k}(x).
$$

The trace map of a finite étale algebra is surjective after reduction to
$k$, hence surjective by Nakayama. Thus the required correction exists
downstairs as well; after splitting it is exactly (16.3). This proves that
the construction descends and does not depend on a distinguished embedding.

**Theorem 16.1 (explicit finite-flat liftability).** Under (14.1), every
rank-two finite-flat deformation with fixed determinant $\chi_\ell$ lifts
through every small extension. The same is true with a generic frame. Hence
the framed fixed-determinant finite-flat functor is formally smooth for
every permitted residual shape. The unframed set-valued functor is also
surjective on small extensions, whether or not it is pro-representable.

**Proof.** The four constructions above produce the required classified
object and frame. Theorem 14.3 realizes it as a finite-flat group scheme,
and (14.15) plus (15.11) gives the prescribed generic determinant. Every
Artinian surjection factors into small extensions, so successive lifting
gives the full formal smoothness assertion. $\square$

### 16.2 Formal smoothness without ambient $H^2$-vanishing

Theorem 16.1 proves that the obstruction map for this finite-flat condition
is zero. It does not claim that the ambient obstruction group is zero. The
distinction is already visible at $\ell=3$.

Let a nonsplit finite-flat residual representation fit into

$$
0\longrightarrow k(1)\xrightarrow{i}\bar V
\xrightarrow{q}k\longrightarrow0. \tag{16.4}
$$

When $\ell=3$, the square of the mod-$3$ cyclotomic character is trivial, so
$k(2)=k$. Twisting $i$ by $1$ gives an injection

$$
i(1):k=k(2)\longrightarrow\bar V(1).
$$

The composite

$$
\bar V\xrightarrow{q}k\xrightarrow{i(1)}\bar V(1) \tag{16.5}
$$

is nonzero. In an adapted basis it is the off-diagonal rank-one map, so its
trace is zero. Hence

$$
H^0(K,\operatorname{ad}^0\bar V(1))\ne0. \tag{16.6}
$$

Since $\ell$ is odd, the trace pairing identifies the Tate dual of
$\operatorname{ad}^0\bar V$ with
$\operatorname{ad}^0\bar V(1)$. Local Tate duality therefore gives

$$
H^2(K,\operatorname{ad}^0\bar V)\ne0. \tag{16.7}
$$

Nevertheless the line, matrix, determinant, and frame construction of
§16.1 lifts every finite-flat point. The ambient $H^2$ contains possible
obstructions for unrestricted determinant-preserving representations; the
finite-flat obstruction map into it vanishes. There is no contradiction.

### 16.3 The residual centralizer table

We now audit every residual shape. Enlarge the coefficient field when
necessary so that irreducible constituents are absolutely defined. The
invariant formulas (15.26)--(15.28) descend to the original coefficient
field.

| Residual shape | $h$ | Fixed-determinant coarse tangent | Framed tangent |
|---|---:|---:|---:|
| Absolutely irreducible, including supersingular | $1$ | $f$ | $f+3$ |
| Nonsplit extension of distinct characters | $1$ | $f$ | $f+3$ |
| Split sum of distinct characters | $2$ | $f+1$ | $f+3$ |
| Equal-character semisimplification | -- | impossible | impossible |

For an absolutely irreducible representation, Schur's lemma gives $h=1$.
The word supersingular describes the finite-flat special-fiber shape; it
does not remove the Hodge line in each Fontaine--Laffaille factor and does
not change the centralizer.

Suppose next that

$$
0\longrightarrow\chi_1\longrightarrow\bar V
\longrightarrow\chi_2\longrightarrow0,
\qquad \chi_1\ne\chi_2. \tag{16.8}
$$

If the extension is nonsplit, an endomorphism preserves the unique
$\chi_1$-line. The off-diagonal equivariant Hom between the distinct
characters is zero, while the two diagonal scalars $a,b$ act on the
extension class by $a-b$. Since the class is nonzero, $a=b$. Thus every
endomorphism is scalar and $h=1$.

If (16.8) is split, the two independent diagonal scalars survive, while the
off-diagonal Homs vanish. Hence $h=2$. Its coarse fixed-determinant tangent
has dimension $f+1$, but the full framed tangent remains $f+3$. The usual
scalar-centralizer hypothesis for a coarse universal unframed ring fails.
There may be a hull or a universal ring after adding structure, but no
coarse universal unframed ring is asserted in general.

The first two rows exhaust the Schur cases permitted by the determinant.
Both have the same $f$-dimensional unframed tangent and both lift by the same
construction. There is no Schur residual counterexample in this range.

### 16.4 Irreducible self-twists and the case $\ell=3$

The reducible map (16.5) should not be used to discuss an irreducible
representation. For an absolutely irreducible $\bar V$, Schur's lemma gives

$$
H^0(K,\operatorname{ad}\bar V(1))
\simeq\operatorname{Hom}_{G_K}(\bar V,\bar V(1)), \tag{16.9}
$$

which is zero unless

$$
\bar V\simeq\bar V(1). \tag{16.10}
$$

If an irreducible self-twist (16.10) occurs, a nonzero map is an
isomorphism. Its trace lies in $H^0(K,k(1))$, which is zero for unramified
$K$ and $\ell>2$ because the mod-$\ell$ cyclotomic character is nontrivial.
Thus the map lies in
$H^0(K,\operatorname{ad}^0\bar V(1))$, and the ambient trace-zero $H^2$ is
nonzero by local duality.

For $\ell>3$, determinants in (16.10) would give
$\bar\chi_\ell^2=1$, impossible on inertia. At $\ell=3$ that determinant
argument no longer excludes a self-twist because
$\bar\chi_3^2=1$. It may therefore contribute an exceptional ambient
$H^2$. Whether it occurs or not, $h=1$ and Theorem 16.1 proves the same
finite-flat formal smoothness and dimensions. The irreducible conclusion
comes from its own self-twist analysis, not from the quotient--inclusion
construction for (16.4).

### 16.5 Why equal-character semisimplification is impossible

It remains to justify the last row of the table. Suppose for contradiction
that a finite-flat $\bar V$ with cyclotomic determinant has a filtration

$$
0\longrightarrow\psi\longrightarrow\bar V
\longrightarrow\psi\longrightarrow0, \tag{16.11}
$$

allowing either the split or nonsplit case. Close the stable line in the
unique finite-flat model. Raynaud identifies both rank-one endpoint models
with the unique model of $\psi$. Exactness of the underlying torsion
Fontaine--Laffaille anti-equivalence turns (16.11) into an exact sequence of
filtered modules; Matlis duality reverses it back on the covariant side.

Let $s_\tau\in\{0,1\}$ be the filtration rank of that rank-one object at
$\tau$. Exactness on $L$ makes the filtration rank of the middle object

$$
2s_\tau,
$$

which is even. Lemma 14.5, on the other hand, makes the rank of the middle
object equal to one at every $\tau$. This is impossible. Thus neither a
scalar split representation nor a nonsplit self-extension of one character
can be a finite-flat residual base point with cyclotomic determinant in the
range (14.1).

This argument uses filtration multiplicity and exactness, so it remains
valid after enlarging the coefficient field. It does not rely on a list of
tame inertia exponents.

### 16.6 Ordinary Kummer classes: hardly ramified and valuation

Consider the standard ordinary orientation

$$
0\longrightarrow k(1)\longrightarrow\bar V_c
\longrightarrow k\longrightarrow0. \tag{16.12}
$$

Common unramified twists transport the same calculation. Kummer theory gives

$$
H^1(K,k(1))
\simeq
\bigl(K^\times/(K^\times)^\ell\bigr)
\otimes_{\mathbf F_\ell}k. \tag{16.13}
$$

For unramified $K$ and $\ell>2$, choose a uniformizer $\pi=\ell$. Then

$$
K^\times=\pi^{\mathbf Z}\times\mu_{\ell^f-1}\times U^1,
\qquad U^1=1+\ell R. \tag{16.14}
$$

The middle factor has order prime to $\ell$. The logarithm identifies the
pro-$\ell$ group $U^1$ with the additive group $\ell R$, and taking
$\ell$th powers corresponds to multiplication by $\ell$. Therefore

$$
\dim_k
\bigl(R^\times/(R^\times)^\ell\bigr)\otimes k=f, \tag{16.15}
$$

while the valuation of $\pi$ supplies one additional ambient Kummer
direction:

$$
\dim_kH^1(K,k(1))=f+1. \tag{16.16}
$$

Chapter 12 proves that extensions between the $\mathbf F_\ell$-linear
standard endpoints are exactly the unit classes. Extending coefficients as
in §11.2 gives the endpoints
$\mu_\ell\otimes_{\mathbf F_\ell}k$ and $\underline{k}$ and tensors that
unit space with $k$. Raynaud now makes this coefficient-linear endpoint
calculation intrinsic. If $\bar V_c$ had any finite-flat model, closure of
its cyclotomic line and the represented quotient would have generic fibers
$k(1)$ and $k$. Their coefficient-linear models are unique, so they must be
these scalar-extended standard models. The middle object would then be one
of the scalar-extended standard extensions classified in Chapter 12. Hence

$$
\boxed{
H^1_{\mathrm{fl}}(K,k(1))
=
\bigl(R^\times/(R^\times)^\ell\bigr)\otimes k,} \tag{16.17}
$$

an $f$-dimensional subspace.

The unit subspace is the **hardly ramified**, or **peu ramifiée**, subspace
in this orientation. The terminology means exactly that the Kummer class
has zero valuation coordinate; it does not mean unramified, since principal
units can give ramified extensions. A class with nonzero valuation
coordinate is **très ramifiée** and is not a finite-flat residual base
point. For the standard
$\Lambda_n=\mathbf Z/\ell^n\mathbf Z$ endpoints, the higher-level statement
is

$$
R^\times/(R^\times)^{\ell^n}
\subset K^\times/(K^\times)^{\ell^n}, \tag{16.18}
$$

and the inverse limit of the unit groups has $\mathbf Z_\ell$-rank $f$.
Finite coefficient extensions give the corresponding statement by scalar
extension.
Thus the ordinary unit calculation agrees with, but does not replace, the
$f$-dimensional full Schur tangent calculation.

### 16.7 Stable-line enhancements are not components

At the split residual point $k(1)\oplus k$, one may remember a selected
stable line, fix its two diagonal characters, and retain the standard
endpoint models. This defines an enhanced ordinary functor. The unit classes
(16.17) give it $f$ unframed extension parameters.

If an upper-triangular generic frame is retained as well, the finite-flat
cocycle space includes the coboundary direction. Since

$$
H^0(K,k(1))=0,
$$

that coboundary space is one-dimensional. The fixed-diagonal framed
upper-triangular enhancement therefore has tangent dimension $f+1$. By
contrast, the full framed fixed-determinant functor has tangent dimension
$f+3$. The two remaining directions move away from the fixed-diagonal
upper-triangular locus.

There may also be two choices of stable residual line at a split point.
They are two objects, or two charts, in a line-enhanced moduli problem.
Forgetting the line sends them to the same underlying split representation.
This does not produce two components of the full finite-flat deformation
space. The full framed functor has already been proved formally smooth at
that point, and §17.1 identifies its completed local ring with one regular
power-series ring. An enhancement records extra discrete data; forgetting
that data is not a decomposition of the full ring.

## 17. The finite-flat local ring package

### 17.1 The low-weight theorem

Only now do we pass from the explicit lifting and tangent calculations to
universal rings. The representability results of Chapter 9, built from the
coefficient-ring and Schlessinger theory of Books 62 and 64--65, convert formal
smoothness plus the calculated tangent dimension into a power-series ring.

**Theorem 17.1 (finite-flat local rings over an unramified base).** Let
$K/\mathbf Q_\ell$ be unramified of degree $f$, let $\ell>2$, and let

$$
\bar\rho:G_K\longrightarrow\operatorname{GL}_2(k)
$$

be finite flat with determinant $\bar\chi_\ell$. Fix the determinant
$\chi_\ell$, and put

$$
h=\dim_k\operatorname{End}_{k[G_K]}(\bar V).
$$

Then:

1. Raynaud full faithfulness makes the finite-flat model unique and extends
   every coefficient action; the covariant torsion Fontaine--Laffaille
   classification of Theorem 14.3 applies at every Artinian and
   $\ell^n$-torsion level;
2. the unframed fixed-determinant tangent has dimension

   $$
   \dim_kH^1_{\mathrm{fl}}
   (K,\operatorname{ad}^0\bar\rho)=f+h-1;
   $$

3. the framed fixed-determinant tangent has dimension $f+3$;
4. the framed functor is pro-representable and formally smooth for every
   permitted residual shape, with

   $$
   \boxed{
   R_{\bar\rho}^{\square,\mathrm{fl},\chi_\ell}
   \simeq
   \mathcal O[[Z_1,\ldots,Z_{f+3}]];}
   \tag{17.1}
   $$

5. if $h=1$, the unframed functor is pro-representable and formally smooth,
   with

   $$
   \boxed{
   R_{\bar\rho}^{\mathrm{fl},\chi_\ell}
   \simeq
   \mathcal O[[X_1,\ldots,X_f]],}
   \tag{17.2}
   $$

   and noncanonically

   $$
   R_{\bar\rho}^{\square,\mathrm{fl},\chi_\ell}
   \simeq
   R_{\bar\rho}^{\mathrm{fl},\chi_\ell}
   [[Y_1,Y_2,Y_3]]; \tag{17.3}
   $$
6. for a split sum of distinct characters, $h=2$, the coarse tangent has
   dimension $f+1$, the framed ring is still (17.1), and a coarse universal
   unframed ring is not asserted in general;
7. equal-character semisimplification cannot occur, and in the standard
   ordinary case the permitted residual extension classes are precisely the
   $f$-dimensional unit, or peu ramifiée, subspace.

All displayed power-series isomorphisms are noncanonical.

**Proof.** The general framed representability theorem is Theorem 9.1. The
explicit construction of §16.1 proves formal smoothness without using an
ambient obstruction group. The tangent dimension is (15.28). The
power-series criterion of Books 62 and 65 therefore gives (17.1).

If $h=1$, Theorem 9.2 gives unframed pro-representability. Forgetting a
frame after the lift constructed in §16.1 proves unframed formal smoothness,
and (15.26) gives tangent dimension $f$. The same power-series criterion
gives (17.2). The scalar-centralizer framing theorem supplies the three
relative framing variables in (17.3).

The split row and its centralizer calculation are §16.3. The impossibility
and Kummer assertions are §§16.5--16.6. $\square$

The Schur cases are the absolutely irreducible case, including the
supersingular shape, and a nonsplit extension of distinct characters. Both
have $h=1$ and both satisfy (17.2). Exceptional ambient $H^2$ at $\ell=3$
does not create a counterexample. There is no Schur counterexample in the
range of Theorem 17.1.

At a split ordinary point, (17.1) is a regular local domain. The two
stable-line enhancements of §16.7 therefore cannot be intersecting
components of the full framed ring. They are separate rigidifications
mapping into the same smooth formal space.

### 17.2 The general theorem outside the comparison range

For an arbitrary finite extension $K/\mathbf Q_\ell$, Chapters 2--13 still
give an exact intrinsic local condition. Let $\delta$ be a fixed determinant
lift. The framed finite-flat functor is represented by a quotient of the
ambient framed deformation ring. Under the scalar-centralizer hypothesis
the unframed functor is represented as well. If

$$
r_{\mathrm{fl},\delta}
=\dim_k t_{\bar\rho}^{\mathrm{fl},\delta,\mathrm{unfr}},
$$

then the unframed ring has a minimal presentation

$$
R_{\bar\rho}^{\mathrm{fl},\delta}
\simeq
\mathcal O[[X_1,\ldots,X_{r_{\mathrm{fl},\delta}}]]/J. \tag{17.4}
$$

In rank two with $\ell>2$ and scalar residual endomorphisms,

$$
R_{\bar\rho}^{\square,\mathrm{fl},\delta}
\simeq
R_{\bar\rho}^{\mathrm{fl},\delta}
[[Y_1,Y_2,Y_3]]. \tag{17.5}
$$

Equations (17.4)--(17.5) are the strongest general ring statements proved
without the low-ramification classification. The relation ideal $J$ must be
retained until an independent integral lifting theorem removes it. A tangent
count does not remove it. Nor does vanishing of an ambient $H^2$ prove that
integral models lift, while nonvanishing of ambient $H^2$ does not prevent a
restricted obstruction map from being zero.

Raynaud full faithfulness itself applies whenever $e(K)<\ell-1$, but the
explicit $f$-cycle normal form used in Chapters 15--16 requires the
unramified torsion Fontaine--Laffaille package. No power-series formula from
Theorem 17.1 is asserted for a ramified field merely because its models are
unique.

### 17.3 A checklist for global deformation data

To use the local condition in a global deformation problem, record the
following data and conclusions.

1. Specify $K$, $\ell$, the coefficient category, the residual basis, and a
   determinant lift.
2. Define finite flatness through an $A$-linear integral model and retain
   stability under every coefficient map, as in Chapter 2.
3. Specify whether the problem is framed, unframed, or enhanced by a stable
   line or endpoint models. These are different functors.
4. For general $K$, use the tangent subspace
   $H^1_{\mathrm{fl}}$ and the Tate-orthogonal condition of Chapter 6; do not
   infer it from ambient Euler characteristic alone.
5. Under (14.1), use

   $$
   f+h-1\quad\text{unframed fixed determinant},
   \qquad
   f+3\quad\text{framed fixed determinant}.
   $$

6. At a split residual point use $h=2$ and do not attach a coarse universal
   unframed ring without a separate representability argument.
7. In the standard ordinary Kummer orientation, retain the $f$ unit
   directions and exclude the valuation direction. A line-enhanced chart is
   not a component of the full framed ring.
8. At $\ell=3$, do not claim ambient $H^2=0$. Use the explicit finite-flat
   lifting theorem instead.
9. Outside the unramified odd range, keep the relation ideal in (17.4) until
   the relevant integral classification and liftability have been supplied.

This checklist separates four logically independent facts: existence and
uniqueness of models, representability of the representation functor,
calculation of its tangent, and formal smoothness. In the range (14.1),
Raynaud supplies the first, Chapters 2--9 the second, the tangent complex the
third, and the small-extension construction the fourth.

### 17.4 Conclusion

Finite flatness at the coefficient prime is an integral condition on a
Galois representation, not a synonym for unramifiedness and not an ambient
cohomological vanishing condition. In general it is existential and must be
handled through saturated closure, exact models, and coefficient-compatible
gluing. In the low-ramification range, Raynaud full faithfulness turns that
existential condition into a unique-model condition and extends every
coefficient endomorphism.

Over an unramified base with $\ell>2$, the established torsion
Fontaine--Laffaille--Raynaud classification then gives exact covariant
linear algebra at every torsion level. Cyclotomic determinant forces one
Hodge line at each of the $f$ embeddings. A line and an invertible divided-
Frobenius matrix contribute $5f$ based parameters, the determinant imposes
one smooth cyclic equation, and the $4f$ gauge directions leave tangent
dimensions $f+h-1$ unframed and $f+3$ framed. Lines, matrices, the determinant,
and the generic frame lift explicitly through every small extension.

Consequently every framed residual shape has one smooth
$(f+3)$-variable local ring, while every Schur residual shape has a smooth
$f$-variable unframed ring. Ordinary unit classes occupy the expected
$f$-dimensional peu ramifiée subspace; the valuation class is excluded, and
stable-line rigidifications do not split the full ring into components.
This is the finite-flat local condition required for the later global
deformation problem.
