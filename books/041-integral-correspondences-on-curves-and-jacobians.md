# Integral Correspondences on Curves and Jacobians

## Contents

1. [The integral problem](#1-the-integral-problem)
   - [Why generic correspondences are not enough](#11-why-generic-correspondences-are-not-enough)
   - [Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
   - [The four layers of the theory](#13-the-four-layers-of-the-theory)
   - [The route through the book](#14-the-route-through-the-book)
2. [Generic correspondences and their algebra](#2-generic-correspondences-and-their-algebra)
   - [Pullback, norm, and the graph test](#21-pullback-norm-and-the-graph-test)
   - [Cycles, harmless components, and normalization](#22-cycles-harmless-components-and-normalization)
   - [Composition](#23-composition)
   - [Transpose and generic duality](#24-transpose-and-generic-duality)
3. [Closing a correspondence on regular models](#3-closing-a-correspondence-on-regular-models)
   - [The scheme-theoretic closure](#31-the-scheme-theoretic-closure)
   - [Normalization and regular domination](#32-normalization-and-regular-domination)
   - [When finite models exist](#33-when-finite-models-exist)
   - [Vertical ambiguity and a warning about composition](#34-vertical-ambiguity-and-a-warning-about-composition)
4. [Extension to Néron models](#4-extension-to-néron-models)
   - [The universal extension](#41-the-universal-extension)
   - [Identity components and component groups](#42-identity-components-and-component-groups)
   - [Unramified base change and localization](#43-unramified-base-change-and-localization)
   - [Extension of generic duality](#44-extension-of-generic-duality)
5. [The separated Picard calculation](#5-the-separated-picard-calculation)
   - [Why the Picard model is nonseparated](#51-why-the-picard-model-is-nonseparated)
   - [Pullback through a resolved correspondence](#52-pullback-through-a-resolved-correspondence)
   - [Norm after resolution](#53-norm-after-resolution)
   - [Comparison with the Néron extension](#54-comparison-with-the-néron-extension)
   - [The finite locally free case](#55-the-finite-locally-free-case)
6. [Component groups from intersection lattices](#6-component-groups-from-intersection-lattices)
   - [The weighted component presentation](#61-the-weighted-component-presentation)
   - [Pullback matrices](#62-pullback-matrices)
   - [Pushforward matrices and projection](#63-pushforward-matrices-and-projection)
   - [Birational invariance](#64-birational-invariance)
   - [A calculation protocol](#65-a-calculation-protocol)
7. [Semistable graphs and harmonic maps](#7-semistable-graphs-and-harmonic-maps)
   - [From intersections to graph lattices](#71-from-intersections-to-graph-lattices)
   - [Harmonicity from finite flatness](#72-harmonicity-from-finite-flatness)
   - [Pullback and pushforward on cycles](#73-pullback-and-pushforward-on-cycles)
   - [Normalized components and the connected part](#74-normalized-components-and-the-connected-part)
   - [Descent and saturation](#75-descent-and-saturation)
8. [Duality and adjunction on components](#8-duality-and-adjunction-on-components)
   - [The discriminant pairing](#81-the-discriminant-pairing)
   - [Adjoint maps descend to discriminant groups](#82-adjoint-maps-descend-to-discriminant-groups)
   - [Agreement with polarization duality](#83-agreement-with-polarization-duality)
   - [Self-adjoint operators](#84-self-adjoint-operators)
9. [Specialization of divisors and correspondences](#9-specialization-of-divisors-and-correspondences)
   - [Closing a divisor class](#91-closing-a-divisor-class)
   - [Specialization commutes with a resolved action](#92-specialization-commutes-with-a-resolved-action)
   - [Vertical corrections and rational pairings](#93-vertical-corrections-and-rational-pairings)
   - [Composition after specialization](#94-composition-after-specialization)
10. [Base change and change of models](#10-base-change-and-change-of-models)
    - [Étale and unramified change](#101-étale-and-unramified-change)
    - [Ramified change](#102-ramified-change)
    - [Compatibility of correspondence actions with ramification](#103-compatibility-of-correspondence-actions-with-ramification)
    - [Subdivision, contraction, and stable models](#104-subdivision-contraction-and-stable-models)
    - [Global compatibility](#105-global-compatibility)
11. [Exact examples](#11-exact-examples)
    - [A graph and its transpose](#111-a-graph-and-its-transpose)
    - [One loop](#112-one-loop)
    - [Two components joined by parallel edges](#113-two-components-joined-by-parallel-edges)
    - [Two loops and nonsaturated images](#114-two-loops-and-nonsaturated-images)
    - [Compact type and good reduction of the graph part](#115-compact-type-and-good-reduction-of-the-graph-part)
    - [Good reduction](#116-good-reduction)
12. [Integral correspondence and Hecke algebras](#12-integral-correspondence-and-hecke-algebras)
    - [The operator algebra](#121-the-operator-algebra)
    - [Integral structures preserved by the action](#122-integral-structures-preserved-by-the-action)
    - [The finite-flat locus and bad places](#123-the-finite-flat-locus-and-bad-places)
    - [Ideals, quotients, and component support](#124-ideals-quotients-and-component-support)
    - [A criterion for a well-defined integral Hecke action](#125-a-criterion-for-a-well-defined-integral-hecke-action)
13. [The complete correspondence package](#13-the-complete-correspondence-package)
    - [The main theorem](#131-the-main-theorem)
    - [What can and cannot be read from a curve model](#132-what-can-and-cannot-be-read-from-a-curve-model)
    - [A reusable local calculation](#133-a-reusable-local-calculation)
    - [Conclusion](#134-conclusion)

## 1. The integral problem

### 1.1 Why generic correspondences are not enough

Let $S$ be a Dedekind scheme with function field $K$. On a smooth proper curve over $K$, a finite correspondence is a remarkably efficient object: it is a curve in a product, it acts on divisor classes by pullback followed by norm, and its transpose is adjoint for the canonical polarization of the Jacobian. Arithmetic applications, however, ask questions that live over the closed points of $S$. Does the operator preserve the connected part of a Jacobian after reduction? What does it do to the component group? Can one calculate that action from the components of a regular model? Does transposition remain adjunction after specialization?

The generic cycle alone does not answer these questions. If one simply closes it in a product of integral models, the closure need not be regular, and its projections need not be finite or flat. A vertical component can appear in the intersection used to compose two closures. A ramified change of base can make a previously regular model singular. These are genuine geometric effects, not failures of notation.

There are two complementary solutions. The first is canonical and group-theoretic. A generic correspondence gives a homomorphism of Jacobians, and every homomorphism of abelian varieties extends uniquely to their Néron models. This route proves existence, uniqueness, composition, and independence of all choices. The second is geometric and computational. Close the correspondence, normalize, resolve, and use pullback, proper pushforward, intersection theory, and the separated relative Picard quotient. This route calculates specialization and component groups. Much of this book is devoted to proving that the two routes give the same map.

The guiding square is

$$
\begin{array}{ccc}
J_C&\xrightarrow{\Gamma_J}&J_D\\
\downarrow&&\downarrow\\
\mathcal J_C&\xrightarrow{\mathcal \Gamma}&\mathcal J_D,
\end{array}
$$

where the upper arrow is defined from the generic cycle and the lower arrow is its unique integral extension. The vertical arrows mean “take the Néron model,” not a morphism from the generic fiber to the model. On special fibers, the lower arrow preserves identity components and therefore induces a finite-group map

$$
\Phi(\Gamma):\Phi_{J_C}\longrightarrow\Phi_{J_D}.
$$

Our task is to make every arrow in this picture explicit and to prove all compatibilities needed for integral Hecke actions.

### 1.2 Standing hypotheses and notation

Unless stated otherwise, $S$ is an excellent connected Dedekind scheme, $eta=\operatorname{Spec}K$ is its generic point, and a **regular model** of a smooth proper geometrically connected $K$-curve $C$ is a regular, proper, flat $S$-scheme $\mathcal X$ with generic fiber $C$. Local arguments take place over an excellent discrete valuation ring $R$ with fraction field $K$, uniformizer $\pi$, and residue field $k$. We pass to the strict henselization when geometric components are required. Excellence is used for finite normalization and resolution of the surfaces that arise from closures.

For a curve $C/K$, write $J_C=\operatorname{Pic}^0_{C/K}$ and write $\mathcal J_C$ for its Néron model. At a closed point $s$ of $S$,

$$
\Phi_{C,s}=\mathcal J_{C,s}/\mathcal J_{C,s}^0
$$

is its finite étale component group. We distinguish the group scheme $\Phi_{C,s}$ from its geometric points $\Phi_{C,s}(k^s)$ and from its rational points. All assertions about geometric dual graphs are made after a separable residue extension. Thus residue degrees, permutation of components, and reversal of branches remain visible through descent.

A finite correspondence from $C$ to $D$ will be written

$$
C\xleftarrow{\alpha}H\xrightarrow{\beta}D, \tag{1.1}
$$

where $H$ is a smooth proper curve, possibly a disjoint union with integer multiplicities understood linearly, and both maps are finite. This presentation includes the normalization of every integral cycle in $C\times_KD$ when the ground field is perfect. More generally, we take (1.1) as the definition of the correspondences used here; it keeps all hypotheses on pullback and norm visible. Its action is

$$
\Gamma_J=\beta_*\alpha^*:J_C\longrightarrow J_D. \tag{1.2}
$$

Here $f^*$ denotes pullback of line bundles and $f_*$ denotes the norm. The transpose interchanges $\alpha$ and $\beta$ and acts by

$$
(\Gamma^t)_J=\alpha_*\beta^*. \tag{1.3}
$$

These variance conventions will never change.

### 1.3 The four layers of the theory

An integral correspondence has four related but distinct layers.

First is the cycle layer. The closure of the generic cycle is a horizontal codimension-one cycle in $\mathcal X\times_S\mathcal Y$. It remembers the generic relation but may be singular.

Second is the divisor layer. After choosing a regular model $\mathcal H$ of $H$ dominating the closure, the two projections become proper morphisms

$$
\mathcal X\xleftarrow{a}\mathcal H\xrightarrow{b}\mathcal Y. \tag{1.4}
$$

Cartier pullback and proper pushforward then act on horizontal divisors and interact with vertical intersections through the projection formula.

Third is the Picard layer. The degree-zero relative Picard object of a regular curve model is usually nonseparated because vertical line bundles are generically trivial. Quotienting by the schematic closure of the generic identity gives the Néron model. Consequently the operation $b_*a^*$ descends even though different resolutions introduce different vertical divisors.

Fourth is the combinatorial layer. The vertical intersection matrix presents the component group. In the semistable case, the same finite group is the discriminant group of the weighted cycle lattice of the dual graph. Maps in (1.4) act by harmonic pullback and pushforward, which are adjoint for the edge-length pairing.

No single layer replaces the others. The Néron property establishes a canonical map without calculating it. The regular model calculates specializations but depends on choices before vertical classes are removed. The graph gives a finite algorithm only in the semistable range and only after thickness and descent data have been retained.

### 1.4 The route through the book

We first reconstruct generic correspondences carefully enough to fix composition and transpose. We then prove that closures admit common regular dominations and identify exactly what can go wrong with naive closure. The Néron mapping property gives the canonical integral extension, while the separated Picard construction proves that a resolved pull–norm calculation produces that same extension.

The middle of the book develops two computational forms. For arbitrary regular models, component groups are presented by weighted intersection lattices, and the action is obtained from pullback and projection. For semistable models, dual graphs turn the action into integral linear algebra on vertices, edges, and cycles. We prove adjunction for both the generic polarization and the finite component pairing, then analyze composition, base change, specialization of divisor classes, and several exact examples.

The final chapters package these results into integral correspondence algebras. The outcome is the precise foundation needed for Hecke operators: one integral action simultaneously controls Néron models, connected special fibers, component groups, invariant differentials, and every unramified localization, while transpose supplies the correct adjoint.

## 2. Generic correspondences and their algebra

### 2.1 Pullback, norm, and the graph test

Before extending anything, the generic convention must be forced rather than guessed. Let $f:C\to D$ be a finite morphism of degree $d$ between smooth proper geometrically connected curves. Pullback and norm give

$$
f^*:J_D\longrightarrow J_C,
\qquad
f_*:J_C\longrightarrow J_D. \tag{2.1}
$$

For a divisor $E$ on $D$, finite flatness gives $f_*f^*E=dE$, including ramification and residue degrees. Hence

$$
f_*f^*=[d]_{J_D}. \tag{2.2}
$$

The reverse composite is generally not scalar. If $f$ is a Galois cover with group $G$, then

$$
f^*f_*=\sum_{g\in G}g^*. \tag{2.3}
$$

For a double cover this is $1+\iota^*$, which kills the anti-invariant part. Formula (2.3) is the standard check against reversing the variance.

The graph $\Gamma_f\subset C\times D$ is a correspondence from $C$ to $D$. Its normalization is $C$, with projections $1_C$ and $f$, so it acts by $f_*$. Its transpose acts by $f^*$. Thus a graph acts covariantly by norm, while a transposed graph acts contravariantly by pullback.

For (1.1), formula (1.2) preserves degree zero. Indeed $\alpha^*$ multiplies degree by $\deg\alpha$, while $\beta_*$ preserves the degree of zero-cycles over $K$; zero remains zero. Principal divisors remain principal because

$$
\beta_*\operatorname{div}(h)
=\operatorname{div}(N_{K(H)/K(D)}h).
$$

The action is therefore well-defined on $J_C$.

### 2.2 Cycles, harmless components, and normalization

Let $Z$ be an integral curve in $C\times D$ finite and surjective over $C$. To define a map toward $J_D$ by the normalization formula, it must also be generically finite over $D$; a component mapping to a point of $D$ acts trivially on $J_D$. Assuming both projections are dominant, the normalization $H\to Z$ is finite. Over a perfect field, the normal proper curve $H$ is smooth, so it gives (1.1).

If $Z$ has multiplicity $n$, its action is multiplied by $n$. Extending by differences gives a homomorphism from the group of finite cycle correspondences to homomorphisms of Jacobians. Components of the form $C\times\{y\}$ or $\{x\}\times D$ act trivially on degree-zero Picard varieties: the action factors through the Picard variety of a point. This explains why intersection-theoretic composition may be simplified by discarding such components after their multiplicities have been accounted for.

The normalization is not cosmetic. A singular correspondence curve can have several branches above one point, and pullback along the singular curve need not be described by Cartier divisors without qualifications. Normalization separates those branches. Ramification indices in pullback and field degrees in norm then supply exactly the multiplicities that the cycle action requires.

### 2.3 Composition

Suppose

$$
C\xleftarrow{\alpha}H\xrightarrow{\beta}D,
\qquad
D\xleftarrow{\gamma}L\xrightarrow{\delta}E
$$

are finite correspondences. Their composite cycle is obtained in $C\times D\times E$ by intersecting the inverse images of the two cycles and pushing the resulting one-cycle to $C\times E$. Equivalently, normalize the one-dimensional components of $H\times_D L$ and retain their scheme-theoretic multiplicities.

**Theorem 2.1 (composition law).** With the preceding conventions,

$$
(\Delta\circ\Gamma)_J=\Delta_J\circ\Gamma_J. \tag{2.4}
$$

**Proof strategy.** The fiber product is the geometric place where the middle pullback and norm meet. The assertion is the projection formula, with lengths at nontransverse points producing the intersection multiplicities.

On the locus where all maps are étale and the two cycles meet transversely, a point $x$ is sent through every pair $(h,l)$ satisfying $\beta(h)=\gamma(l)$. Both sides of (2.4) sum the resulting points $\delta(l)$ with the same residue degrees. The complement is finite. At a point of ramification or nontransverse intersection, the local ring of $H\times_D L$ has a finite length on each isolated branch. The norm of a local parameter counts that length, while cycle composition assigns it as intersection multiplicity. Thus the equality holds on divisors. Principal divisors are respected on both sides, so it descends to Jacobians. Linearity handles arbitrary integer combinations. $\square$

Composition is in the displayed order: first $\Gamma$, then $\Delta$. This matters once correspondence algebras are identified with endomorphism algebras.

### 2.4 Transpose and generic duality

Let $\lambda_C:J_C\xrightarrow{\sim}J_C^\vee$ be the canonical principal polarization. For a homomorphism $u:J_C\to J_D$, define

$$
u^\dagger=\lambda_C^{-1}u^\vee\lambda_D:J_D\longrightarrow J_C. \tag{2.5}
$$

Pullback and norm for a finite map are dual under the Poincaré bundles. Consequently

$$
(f_*)^\dagger=f^*,
\qquad
(f^*)^\dagger=f_*. \tag{2.6}
$$

Applying (2.6) twice to (1.2) gives

$$
(\Gamma_J)^\dagger
=(\beta_*\alpha^*)^\dagger
=\alpha_*\beta^*
=(\Gamma^t)_J. \tag{2.7}
$$

Thus transpose is not merely a visual reversal of the cycle; it is the adjoint determined by the canonical polarizations. Since dualization reverses composition,

$$
(\Delta\circ\Gamma)^t=\Gamma^t\circ\Delta^t. \tag{2.8}
$$

These identities will extend integrally because both sides of each identity are homomorphisms of Néron models with the same generic fiber.

## 3. Closing a correspondence on regular models

### 3.1 The scheme-theoretic closure

Let $\mathcal X$ and $\mathcal Y$ be regular proper models of $C$ and $D$. An integral generic correspondence $Z\subset C\times_KD$ has a scheme-theoretic closure

$$
\overline Z\subset\mathcal X\times_S\mathcal Y. \tag{3.1}
$$

It is proper over $S$, because the ambient product is proper. It has no irreducible component contained entirely in a closed fiber: by definition every irreducible component is the closure of a generic component. Over a discrete valuation ring, its coordinate rings are torsion-free as modules over the base. Hence $\overline Z$ is flat over $S$. Globally, flatness follows locally at each closed point because torsion-free modules over a discrete valuation ring are flat.

The total dimension of $\overline Z$ is two. It is therefore an arithmetic surface, but generally not a regular one. Even if $\mathcal X$ and $\mathcal Y$ are regular, their fiber product has relative dimension two, and a divisor inside it can acquire singularities where the generic correspondence meets bad fibers.

The projections

$$
\overline Z\longrightarrow\mathcal X,
\qquad
\overline Z\longrightarrow\mathcal Y \tag{3.2}
$$

are proper and generically finite. They need not be finite. A vertical curve in $\overline Z$ may be contracted to a point of one chosen model. Nor need they be flat: different special components can carry different degrees. These failures are the main reason one cannot define the integral correspondence by repeating the generic finite-flat formula on the raw closure.

### 3.2 Normalization and regular domination

Normalize $\overline Z$. Excellence makes the normalization finite, so it remains proper over $S$. Its generic fiber is the normalization $H$ of $Z$. Resolve the resulting normal surface without changing the generic fiber. We obtain a regular proper model $\mathcal H$ and proper morphisms

$$
\begin{array}{ccc}
&\mathcal H&\\
a\swarrow&&\searrow b\\
\mathcal X&&\mathcal Y
\end{array} \tag{3.3}
$$

extending $\alpha$ and $\beta$.

**Proposition 3.1 (regular extension of a correspondence).** Every finite generic correspondence between smooth proper curves admits a diagram (3.3). Any two such diagrams admit a common regular domination.

**Proof.** The closure, finite normalization, and resolution just described give existence for every integral component; take disjoint unions and multiplicities for a general correspondence. For two choices $\mathcal H_1$ and $\mathcal H_2$, the generic identity on $H$ gives a birational map between them. Take the closure of its graph in $\mathcal H_1\times_S\mathcal H_2$, normalize, and resolve. The resulting regular surface maps properly and birationally to both. $\square$

The common domination is the mechanism behind independence of resolution. Pulling a divisor to a further blowup changes it by controlled exceptional terms; those terms are vertical and disappear in the separated Picard quotient.

### 3.3 When finite models exist

The diagram becomes much simpler if $a$ and $b$ are finite flat. A finite morphism between regular flat curves over $S$ is flat when the source is Cohen--Macaulay and every fiber has pure dimension one: this is the dimension criterion for flatness. Thus finiteness plus absence of isolated vertical components often gives finite local freeness.

One systematic construction starts with a target model $\mathcal X$ and a finite map $H\to C$. Normalize $\mathcal X$ in $K(H)$. Excellence makes the normalization finite over $\mathcal X$, and it is flat over $S$. It may be singular, however. Resolving it destroys finiteness by introducing exceptional curves. Hence one usually has either a finite normal model or a regular proper model, not automatically both.

This tradeoff should be kept explicit:

$$
\begin{array}{c}
\text{finite normalization: direct norms, possible singularities},\\
\text{regular resolution: Cartier intersection theory, possible contractions}.
\end{array}
$$

At good places or in well-designed moduli problems, finite locally free extensions often exist and give the cleanest formulas. At bad places, the resolved diagram (3.3) is the reliable general object.

### 3.4 Vertical ambiguity and a warning about composition

Suppose two generic correspondences have been closed in products of fixed models. The closure of their generic composite need not equal the cycle obtained by intersecting the two closures. The integral intersection can contain components supported entirely in a special fiber. It can also have embedded contributions at a nontransverse meeting. After pushforward, these terms are vertical cycles in the endpoint product.

This does not contradict the generic composition law. A vertical correspondence has empty generic fiber and acts trivially on the generic Jacobian. After passage to the Néron extension, two integral constructions with the same generic homomorphism must agree. But a raw equality of cycles on the chosen models is too much to expect.

The safe principle is therefore:

1. use generic cycles to define the algebra and its composition;
2. use the Néron property to extend its operators canonically;
3. use resolved closures to calculate those operators on special fibers;
4. regard vertical excess terms as part of the calculation, not as new generic operators.

Later we will prove that vertical terms change relative line bundles only within the closure of the generic identity, so they vanish in the separated quotient.

## 4. Extension to Néron models

### 4.1 The universal extension

The central existence theorem is formally short but mathematically powerful.

**Theorem 4.1 (integral extension theorem).** Let $\Gamma:C\dashrightarrow D$ be a finite correspondence. Its Jacobian homomorphism extends uniquely to an $S$-homomorphism

$$
\mathcal \Gamma:\mathcal J_C\longrightarrow\mathcal J_D. \tag{4.1}
$$

The construction is additive in $\Gamma$, compatible with composition and identity correspondences, and independent of all curve models and resolutions.

**Proof.** The Néron model $\mathcal J_C$ is smooth over $S$. Apply the Néron mapping property of $\mathcal J_D$ to the generic map

$$
(\mathcal J_C)_K=J_C\xrightarrow{\Gamma_J}J_D.
$$

This gives a unique $S$-morphism $\mathcal \Gamma$. It preserves the identity because its generic fiber does and the two sections agree on the schematically dense generic point. Similarly, the two morphisms

$$
\mathcal \Gamma(x+y),\qquad
\mathcal \Gamma(x)+\mathcal \Gamma(y)
$$

from $\mathcal J_C\times_S\mathcal J_C$ to $\mathcal J_D$ agree generically and hence everywhere by separatedness. Thus $\mathcal \Gamma$ is a homomorphism.

Addition, composition, and identity can all be checked on generic fibers; uniqueness then proves them integrally. Since no model was used in the construction, independence is immediate. $\square$

In particular there is a ring homomorphism for self-correspondences,

$$
\operatorname{Corr}(C)\longrightarrow
\operatorname{End}_S(\mathcal J_C), \tag{4.2}
$$

with multiplication given by generic composition. It need not be injective: a nonzero cycle may act trivially on $J_C$.

### 4.2 Identity components and component groups

A homomorphism of smooth group schemes sends the identity component of every geometric fiber into the identity component. Indeed the image of a connected scheme containing the identity is connected and contains the identity. Therefore (4.1) restricts to

$$
\mathcal \Gamma^0:\mathcal J_C^0\longrightarrow\mathcal J_D^0 \tag{4.3}
$$

and induces

$$
\Phi(\Gamma):\Phi_C\longrightarrow\Phi_D. \tag{4.4}
$$

Both operations respect addition and composition. If $\Gamma$ and $\Delta$ satisfy an identity such as

$$
\Delta_J\Gamma_J=[n]_{J_C}, \tag{4.5}
$$

then the same identity holds on Néron models, identity components, and component groups.

**Corollary 4.2 (prime-to-$n$ control).** Suppose $u:J_C\to J_D$ and $v:J_D\to J_C$ are correspondence homomorphisms with $vu=[n]$ and $uv=[n]$. Then the kernel and cokernel of $\Phi(u)$ are killed by $n$. For every prime $\ell\nmid n$, $\Phi(u)$ is an isomorphism on the $\ell$-primary parts.

**Proof.** If $\Phi(u)x=0$, then $nx=\Phi(v)\Phi(u)x=0$. In the cokernel, $ny=\Phi(u)\Phi(v)y$ is zero. After localization at a prime not dividing $n$, $n^{-1}\Phi(v)$ is an inverse. $\square$

This is the correct integral consequence of an isogeny relation. The extended map of Néron models need not be finite or flat, so stronger claims require extra hypotheses.

### 4.3 Unramified base change and localization

Let $S'\to S$ be étale. Néron models commute with this base change, so uniqueness gives a commutative square

$$
\begin{array}{ccc}
\mathcal J_C\times_SS'&\xrightarrow{\mathcal \Gamma\times S'}&
\mathcal J_D\times_SS'\\
\Vert&&\Vert\\
\mathcal J_{C_{K'}}&\xrightarrow{\mathcal \Gamma_{K'}}&
\mathcal J_{D_{K'}}.
\end{array} \tag{4.6}
$$

Consequently the geometric component map is equivariant for the residue Galois action, and rational component maps are obtained by taking invariants only when the usual descent identification applies.

Localization at a closed point is another instance of restriction. Thus a global correspondence operator on Néron models localizes to the operator obtained from the same generic cycle over the local discrete valuation ring. This permits all component calculations to be performed one bad place at a time.

Ramified base change is different. There is a canonical morphism from the base change of the old Néron model to the new Néron model, but it need not be an isomorphism. The correspondence operators commute with these canonical comparison morphisms because both composites have the same generic fiber. We return to the consequences in Chapter 10.

### 4.4 Extension of generic duality

The dual abelian varieties $J_C^\vee$ and $J_D^\vee$ have Néron models, and generic dual homomorphisms extend uniquely. The canonical principal polarizations extend to homomorphisms

$$
\mathcal \lambda_C:\mathcal J_C\longrightarrow\mathcal J_C^\vee,
\qquad
\mathcal \lambda_D:\mathcal J_D\longrightarrow\mathcal J_D^\vee. \tag{4.7}
$$

Because the polarizations are principal, their generic inverses extend as well, and uniqueness shows that $\mathcal \lambda_C$ and $\mathcal \lambda_D$ are isomorphisms of the corresponding Néron models. This assertion concerns the Néron models; it does not turn an arbitrary proper or Picard model into a principally polarized abelian scheme at bad reduction.

**Theorem 4.3 (integral transpose identity).** The extensions of a correspondence and its transpose satisfy

$$
\mathcal \lambda_C\,\mathcal \Gamma^t
=\mathcal \Gamma^\vee\,\mathcal \lambda_D. \tag{4.8}
$$

Equivalently, $\mathcal \Gamma^t$ is the integral extension of the polarized adjoint of $\Gamma$.

**Proof.** Both sides of (4.8) are homomorphisms $\mathcal J_D\to\mathcal J_C^\vee$. Their generic fibers agree by (2.7). The target is separated, or directly the Néron uniqueness principle applies, so the homomorphisms agree over $S$. $\square$

Passing to identity components and component groups gives the corresponding duality diagrams. A perfect numerical pairing on component groups is not asserted in arbitrary reduction without additional hypotheses. In the semistable Jacobian case, the weighted graph discriminant pairing is perfect, and Chapter 8 will turn (4.8) into an explicit adjunction formula.

## 5. The separated Picard calculation

### 5.1 Why the Picard model is nonseparated

The universal extension proves that an integral operator exists, but to calculate it from (3.3) we need the Picard description of the Néron model. Work locally over a discrete valuation ring $R$. Let $\mathcal X$ be a regular proper flat model of $C$, and let

$$
P_{\mathcal X}^{[0]}
$$

denote the part of the relative Picard object whose generic restriction has degree zero. A vertical Cartier divisor $V$ has empty generic restriction, so $\mathcal O_{\mathcal X}(V)$ lies over the generic identity. Different vertical divisors can have different multidegrees on the special fiber. Thus the generic identity has acquired a whole vertical closure, and $P_{\mathcal X}^{[0]}$ is generally nonseparated.

Let $E_{\mathcal X}$ be the schematic closure of the generic identity. The Raynaud quotient is

$$
Q_{\mathcal X}=P_{\mathcal X}^{[0]}/E_{\mathcal X}. \tag{5.1}
$$

Under the standard admissibility hypotheses for regular models, including the regular semistable case, $Q_{\mathcal X}$ is the Néron model $\mathcal J_C$. If a preliminary smoothening of the Picard object is required, the same separated quotient is obtained.

Two facts explain the quotient. First, two line bundles with isomorphic generic restrictions differ, after a pullback from the base, by a vertical divisor: a generic isomorphism is a rational section of their ratio, and its divisor has no horizontal part. Second, any two sections of the Picard object agreeing generically must become equal in a separated target. Thus killing $E_{\mathcal X}$ is both necessary and sufficient.

### 5.2 Pullback through a resolved correspondence

Let $a:\mathcal H\to\mathcal X$ be one projection in (3.3). Cartier pullback gives

$$
a^*:P_{\mathcal X}^{[0]}\longrightarrow P_{\mathcal H}^{[0]}. \tag{5.2}
$$

It preserves the closure of the generic identity. Indeed a vertical divisor pulls back to a vertical Cartier divisor, and schematic closure is preserved after taking the induced morphism of group functors. Therefore (5.2) descends to

$$
\overline a^*:Q_{\mathcal X}\longrightarrow Q_{\mathcal H}. \tag{5.3}
$$

On generic fibers this is $\alpha^*:J_C\to J_H$. Since both quotients are Néron models, (5.3) is exactly the unique Néron extension of $\alpha^*$.

This observation also covers a birational modification $r:\mathcal X'\to\mathcal X$ that is an isomorphism generically. The generic Jacobian map is the identity, so

$$
\overline r^*:Q_{\mathcal X}\xrightarrow{\sim}Q_{\mathcal X'} \tag{5.4}
$$

is the canonical identification. Exceptional line bundles belong to the vertical closure and do not create new Néron data.

### 5.3 Norm after resolution

If $b:\mathcal H\to\mathcal Y$ is finite locally free, the determinant norm of line bundles gives a morphism

$$
b_*:P_{\mathcal H}^{[0]}\longrightarrow P_{\mathcal Y}^{[0]} \tag{5.5}
$$

that commutes with base change and carries vertical divisors to vertical divisors. It therefore descends to $Q_{\mathcal H}\to Q_{\mathcal Y}$.

In the general resolved diagram, $b$ is proper and generically finite but can contract vertical curves. A determinant norm on every line bundle is then not the right primitive construction. There are two equivalent safe routes.

The first route uses the generic norm $\beta_*:J_H\to J_D$ and extends it uniquely to the Néron models. The second route acts on a horizontal divisor $A$ on $\mathcal H$ by proper cycle pushforward $b_*A$. Regularity of $\mathcal Y$ turns the resulting codimension-one cycle into a Cartier divisor. If $A$ is changed by a principal divisor, its pushforward changes by the divisor of the field norm; if it is changed by a vertical divisor, its pushforward is vertical or zero. Thus the divisor operation descends through the separated quotient wherever horizontal representatives exist. Such representatives exist locally in the Picard topology and the local maps glue by separatedness.

We obtain a canonical morphism

$$
\overline b_*:Q_{\mathcal H}\longrightarrow Q_{\mathcal Y} \tag{5.6}
$$

whose generic fiber is $\beta_*$. The first route proves existence for all families; the second proves the divisor formula and shows how to calculate it.

### 5.4 Comparison with the Néron extension

Combine (5.3) and (5.6):

$$
Q_{\mathcal X}\xrightarrow{\overline a^*}Q_{\mathcal H}
\xrightarrow{\overline b_*}Q_{\mathcal Y}. \tag{5.7}
$$

**Theorem 5.1 (Picard–Néron comparison).** Assume the chosen regular models are Picard-admissible, or replace their degree-zero Picard objects by the smoothened objects having the same separated quotients. Under the identifications $Q_{\mathcal X}=\mathcal J_C$ and $Q_{\mathcal Y}=\mathcal J_D$, the composite (5.7) is the integral correspondence $\mathcal \Gamma$ of Theorem 4.1.

**Proof.** The generic fiber of (5.7) is $\beta_*\alpha^*=\Gamma_J$. The Néron extension of this generic homomorphism is unique. $\square$

Although the proof is brief, its consequences are substantial. The map calculated using a resolved closure is independent of the closure, normalization, resolution, and horizontal representatives. On a common regular domination, all discrepancies are vertical; quotienting by the closures $E$ removes them. Composition of resolved diagrams agrees even if their raw cycle composition has vertical excess, because the two Picard maps have the same generic composite.

### 5.5 The finite locally free case

When the correspondence extends as

$$
\mathcal X\xleftarrow{a}\mathcal H\xrightarrow{b}\mathcal Y
$$

with both maps finite locally free, no resolution caveat remains. Pullback and determinant norm are defined in families, commute with every base change, and give

$$
\mathcal \Gamma=\operatorname{Nm}_b\circ a^*. \tag{5.8}
$$

If $a$ has constant degree $r$, then

$$
\operatorname{Nm}_a\circ a^*=[r]. \tag{5.9}
$$

The equality holds on relative Picard functors and hence on Néron models and every special-fiber layer. Formula (5.8) is the ideal situation for integral moduli correspondences: it makes base change automatic and exposes no hidden vertical geometry.

Finite flatness is a sufficient hypothesis, not a necessary one. Requiring it in all bad fibers would incorrectly exclude correspondences whose Jacobian operators extend perfectly well but whose chosen curve models require exceptional components.

## 6. Component groups from intersection lattices

### 6.1 The weighted component presentation

We now calculate (4.4) over a strict henselian discrete valuation ring. Let

$$
\mathcal X_k=\sum_{i\in I}m_iX_i \tag{6.1}
$$

be the geometric special fiber of a regular proper model. Put

$$
M_{\mathcal X}=(X_i\cdot X_j)_{i,j},
\qquad
\Lambda_{\mathcal X}
=\left\{d\in\mathbf Z^I:\sum_i m_id_i=0\right\}. \tag{6.2}
$$

The whole fiber is principal, so $M_{\mathcal X}\mathbf Z^I\subseteq\Lambda_{\mathcal X}$. The vertical intersection form is negative semidefinite with rational kernel spanned by $m=(m_i)$; consequently the two lattices have the same rank and the quotient is finite. The component group is

$$
\Phi_C(k^s)
\simeq\Lambda_{\mathcal X}/M_{\mathcal X}\mathbf Z^I. \tag{6.3}
$$

If $A$ is a degree-zero horizontal divisor meeting the fiber properly, define

$$
\rho_{\mathcal X}(A)=((A\cdot X_i))_{i\in I}. \tag{6.4}
$$

Degree constancy gives $\sum_i m_i(A\cdot X_i)=\deg A_K=0$, so (6.4) lies in $\Lambda_{\mathcal X}$. If $A=\operatorname{div}(h)$ generically, the full divisor on $\mathcal X$ is $A+\sum a_iX_i$, and intersecting with every component gives

$$
\rho_{\mathcal X}(A)=-M_{\mathcal X}a. \tag{6.5}
$$

Thus its class in (6.3) depends only on the generic divisor class and is exactly its Néron component.

### 6.2 Pullback matrices

Let $f:\mathcal U\to\mathcal X$ be a proper generically finite morphism of regular models. Write the components of $\mathcal U_k$ as $U_a$. For each target component, Cartier pullback has a vertical expansion

$$
f^*X_i=\sum_a e_{ai}U_a. \tag{6.6}
$$

The nonnegative integer $e_{ai}$ is a valuation ramification multiplicity; it can be nonzero even when $U_a$ is contracted to a point on $X_i$. Let $E_f=(e_{ai})$.

There is also a degree matrix for components that dominate components. If $U_a$ maps onto $X_i$, put

$$
d_{ai}=[K(U_a):K(X_i)], \tag{6.7}
$$

including constant-field degree, and set it to zero otherwise. For a line bundle $L$ on $\mathcal X$, restriction and degree give

$$
\deg(f^*L|_{U_a})=
\sum_i d_{ai}\deg(L|_{X_i}). \tag{6.8}
$$

Thus the matrix $D_f=(d_{ai})$ carries multidegrees on $\mathcal X$ to multidegrees on $\mathcal U$. In particular it defines

$$
f^\Phi:\Lambda_{\mathcal X}\longrightarrow\Lambda_{\mathcal U}. \tag{6.9}
$$

The notation anticipates descent to components.

The essential compatibility is

$$
D_fM_{\mathcal X}=M_{\mathcal U}E_f. \tag{6.10}
$$

To prove it, take the $a,i$ entry. The left side is the degree on $U_a$ of $f^*\mathcal O_{\mathcal X}(X_i)$. The right side is

$$
\left(\sum_b e_{bi}U_b\cdot U_a\right),
$$

which is the same degree because (6.6) is the Cartier pullback divisor. Hence (6.10) holds. It shows that (6.9) carries the image of the target intersection matrix into the image of the source matrix and therefore descends to

$$
f^\Phi:\Phi_{J_X}\longrightarrow\Phi_{J_U}. \tag{6.11}
$$

This is precisely the component map of the Jacobian pullback $f_K^*$.

### 6.3 Pushforward matrices and projection

For proper pushforward, the clean formula begins with horizontal divisors. Let $A$ be a horizontal divisor on $\mathcal U$. By projection,

$$
(f_*A\cdot X_i)=(A\cdot f^*X_i)
=\sum_a e_{ai}(A\cdot U_a). \tag{6.12}
$$

Thus $E_f^t$ sends the component intersection vector of $A$ to that of $f_*A$:

$$
f_\Phi=E_f^t:\Lambda_{\mathcal U}\longrightarrow\Lambda_{\mathcal X}. \tag{6.13}
$$

The map respects the degree-zero conditions. One way to see this is to apply (6.12) to the full fibers and use preservation of the generic degree under proper pushforward. It respects matrix images because the transpose of (6.10), together with symmetry of the intersection matrices, gives

$$
M_{\mathcal X}D_f^t=E_f^tM_{\mathcal U}. \tag{6.14}
$$

Hence (6.13) descends to the component group and equals the map induced by the generic norm $f_{K,*}$.

For a resolved correspondence (3.3), the component action is therefore

$$
\Phi(\Gamma)=b_\Phi\,a^\Phi. \tag{6.15}
$$

All matrices are integral. Passing to rational component spaces before taking the quotient would lose the saturation defect that is the component group itself.

### 6.4 Birational invariance

Suppose $r:\mathcal X'\to\mathcal X$ is a point blowup. Its generic degree is one and its generic Jacobian map is the identity. Hence $r^\Phi$ and $r_\Phi$ are inverse isomorphisms on component groups. This can also be seen directly.

The exceptional curve adds one generator to the vertical lattice and one negative direction to the intersection form. Total pullback is orthogonal to the exceptional curve. In the presentation (6.3), the new generator and its relation cancel, leaving the same finite quotient. Iterating proves invariance under regular birational modification.

Consequently (6.15) is independent of the selected resolution. On a common domination, the two matrix calculations are conjugate by these canonical birational identifications. This is the lattice counterpart of the Picard–Néron comparison.

### 6.5 A calculation protocol

For a correspondence at a bad place, the following order prevents the usual mistakes.

First pass to a strict henselian base if geometric components are wanted, but retain the residue Galois action. Resolve the normalized closure and record every special-fiber multiplicity.

Second compute $M_{\mathcal X}$, $M_{\mathcal H}$, and $M_{\mathcal Y}$. Off-diagonal entries come from residue-weighted local intersections; diagonal entries are forced by the fiber relations. Check that each multiplicity vector spans the rational kernel.

Third compute component degrees $D_a,D_b$ and pullback multiplicities $E_a,E_b$. Verify (6.10) for both maps. This is a strong check on omitted residue or ramification factors.

Fourth form $b_\Phi a^\Phi$ and reduce it modulo the relevant matrix images. Compute Smith normal forms if invariant factors are needed.

Finally verify generic relations such as $f_*f^*=[\deg f]$ on the finite quotients. A failure usually signals that a contracted component, residue degree, or fiber multiplicity has been lost.

## 7. Semistable graphs and harmonic maps

### 7.1 From intersections to graph lattices

Suppose the models are semistable. After geometric residue extension, let $G_X$ be the dual graph of $\mathcal X_k$. A vertex represents a normalized component, an edge represents a node, and a loop represents a self-node. If a stable model has local equation

$$
xy=u\pi^{n_e},
$$

attach length $n_e$ to the edge. A regular semistable model has all lengths one; resolving a thick node replaces its edge by a chain of $n_e$ unit edges.

Choose orientations. The cycle lattice is

$$
X(G_X)=H_1(G_X,\mathbf Z), \tag{7.1}
$$

and the edge-length pairing is

$$
q_X(c,c')=\sum_{e}n_ec_ec'_e. \tag{7.2}
$$

It is positive definite on the cycle lattice. The semistable component theorem gives

$$
0\longrightarrow X(G_X)
\xrightarrow{q_X}X(G_X)^\vee
\longrightarrow\Phi_C(k^s)\longrightarrow0. \tag{7.3}
$$

The connected special fiber fits into

$$
0\longrightarrow T_X\longrightarrow\mathcal J_{C,k}^0
\longrightarrow\prod_vJ(X_v^\nu)\longrightarrow0,
\qquad X^*(T_X)=X(G_X). \tag{7.4}
$$

Thus a correspondence can be calculated separately on normalized-component Jacobians and on the graph torus, with the same graph map controlling the finite component quotient.

### 7.2 Harmonicity from finite flatness

Let $f:\mathcal U\to\mathcal X$ be finite flat between semistable curves and assume nodes map to nodes after a suitable semistable modification. A component $U_v$ maps to $X_w$ with degree $d_v$. For an oriented branch $e'$ at $w$, sum the local branch degrees $m_e$ over branches $e$ at $v$ mapping to $e'$. Flatness gives

$$
\sum_{e\mapsto e'}m_e=d_v, \tag{7.5}
$$

independent of $e'$. This is harmonicity.

**Proof.** Choose a smooth point of the branch $e'$ near the node. Its inverse image on $U_v$ is a finite divisor of total degree $d_v$. As the point approaches the node along that branch, flatness preserves the length of the fiber, while the local maps on the branches contribute their ramification degrees $m_e$. Their sum is therefore $d_v$. The same total degree is obtained on every branch. $\square$

The smoothing equations impose the corresponding metric relation. It should be derived from the local parameters rather than memorized, because ramification of the base changes edge lengths. Over the same base, an admissible local map sends branch parameters to units times powers, and equality of the two pulled-back smoothing equations makes the branch degrees and thicknesses compatible.

### 7.3 Pullback and pushforward on cycles

Harmonicity defines integral maps

$$
f^*:X(G_X)\longrightarrow X(G_U),
\qquad
f_*:X(G_U)\longrightarrow X(G_X). \tag{7.6}
$$

For pullback, lift an oriented edge with its local branch multiplicities. Relation (7.5) makes the boundary of a lifted cycle vanish at every vertex. Pushforward sends an oriented source edge to its target edge with the appropriate residue and local degrees; reversal changes the sign. Loops must be retained, since their boundary is already zero and they can carry the entire toric action.

The decisive identity is

$$
q_U(f^*c,d)=q_X(c,f_*d). \tag{7.7}
$$

**Proof strategy.** Expand both sides edge by edge. Each target edge contribution on the right is distributed among its inverse branches on the left. Harmonicity supplies conservation of degree and the local smoothing equations supply equality of metric weights.

Indeed the coefficient of $c_{e'}d_e$ on the left is the pullback multiplicity of $e'$ along $e$, multiplied by the source length. The local parameter relation identifies this product with the pushforward multiplicity of $e$ times the target length, which is the coefficient on the right. Summing over all oriented edges proves (7.7). $\square$

For a resolved correspondence, define the covariant graph-lattice map

$$
u_\Gamma=\beta_*\alpha^*:X(G_C)\longrightarrow X(G_D), \tag{7.8}
$$

and let

$$
v_\Gamma=\alpha_*\beta^*:X(G_D)\longrightarrow X(G_C). \tag{7.9}
$$

The second is the graph map of the transpose, and (7.7) says that $u_\Gamma$ and $v_\Gamma$ are adjoint. Because $X(G)$ is the character lattice of the graph torus while torus morphisms act contravariantly on characters, one must not identify a Néron homomorphism with a single character-lattice arrow without stating the variance. On the discriminant presentation, the covariant component map attached to $\Gamma$ is induced by the dual map

$$
v_\Gamma^\vee:X(G_C)^\vee\longrightarrow X(G_D)^\vee. \tag{7.10}
$$

Adjunction gives $v_\Gamma^\vee q_C=q_Du_\Gamma$, so (7.10) carries $q_CX(G_C)$ into $q_DX(G_D)$. Its map on the cokernels of (7.3) is $\Phi(\Gamma)$.

### 7.4 Normalized components and the connected part

A finite map between semistable curves also maps normalizations of special components. On their Jacobians it induces the ordinary pullback and norm. Together with (7.6), these maps fit into a diagram of semiabelian extensions

$$
\begin{array}{ccccccccc}
0&\to&T_C&\to&\mathcal J_{C,k}^0&\to&\prod_vJ(C_v^\nu)&\to&0\\
&&\downarrow&&\downarrow&&\downarrow&&\\
0&\to&T_D&\to&\mathcal J_{D,k}^0&\to&\prod_wJ(D_w^\nu)&\to&0.
\end{array} \tag{7.11}
$$

For a correspondence, compose the pullback diagram for $\alpha$ with the norm diagram for $\beta$. The middle arrow is the special fiber of $\mathcal \Gamma^0$. Equality can be checked on the generic fiber through the Néron property, or on line bundles by gluing across nodes.

The extension class in (7.4) means that the middle map is not generally the direct product of the torus map and normalized-component maps. Diagram (7.11), rather than a noncanonical splitting, is the correct integral statement.

### 7.5 Descent and saturation

All graph constructions must be performed on the geometric graph with its Galois action. A nonsplit node may be fixed while its two orientations are reversed; the resulting action on a loop generator is $-1$. A closed node of residue degree $r$ can split into an orbit of $r$ edges. Taking a quotient graph first can lose both phenomena.

Likewise, the cycle lattice must remain integral. The image of a graph map can be nonsaturated. Tensoring with $\mathbf Q$ remembers its rank and rational adjoint but erases the finite quotient

$$
\operatorname{Sat}(uX)/uX.
$$

That quotient can contribute directly to kernels or cokernels on component groups. Smith normal form, not rational diagonalization, is the correct computational operation.

## 8. Duality and adjunction on components

### 8.1 The discriminant pairing

Let $X$ be a free abelian group and let $q:X\hookrightarrow X^\vee$ be a symmetric positive definite integral map. Its discriminant group

$$
\Phi_q=X^\vee/qX
$$

has a pairing

$$
\langle\ ,\ \rangle_q:\Phi_q\times\Phi_q
\longrightarrow\mathbf Q/\mathbf Z. \tag{8.1}
$$

For lifts $x,y\in X^\vee$, put

$$
\langle\bar x,\bar y\rangle_q
=y(q^{-1}x)\bmod\mathbf Z. \tag{8.2}
$$

Changing $x$ by $qz$ changes the value by $y(z)\in\mathbf Z$, and similarly in the other variable. Symmetry follows from symmetry of $q$. If $\bar x$ pairs trivially with all $y$, then $q^{-1}x$ belongs to the double dual $X$, so $x\in qX$. Thus the pairing is perfect.

For a semistable Jacobian, take $X=H_1(G,\mathbf Z)$ and $q$ equal to the edge-length pairing. The result is the canonical component pairing

$$
\Phi_C(k^s)\times\Phi_C(k^s)
\longrightarrow\mathbf Q/\mathbf Z. \tag{8.3}
$$

It is Galois invariant because Galois permutes edges and may reverse both coefficients on an edge, leaving their product unchanged.

### 8.2 Adjoint maps descend to discriminant groups

Suppose $u:X\to Y$ and $v:Y\to X$ satisfy

$$
q_Y(ux,y)=q_X(x,vy). \tag{8.4}
$$

The adjunction identity is equivalently

$$
v^\vee q_X=q_Yu.
$$

Thus $v^\vee:X^\vee\to Y^\vee$ induces the covariant discriminant map denoted $\Phi(u)$, while $u^\vee:Y^\vee\to X^\vee$ induces $\Phi(v)$. They remain adjoint:

$$
\langle\Phi(u)\xi,\eta\rangle_Y
=\langle\xi,\Phi(v)\eta\rangle_X. \tag{8.5}
$$

To verify (8.5), choose dual-lattice lifts and use (8.4) after extending scalars to $\mathbf Q$. The difference between either side and that rational equality is integral, so the equality survives modulo $\mathbf Z$.

Apply this to graph pullback and pushforward using (7.7). We obtain

$$
\langle f^*x,y\rangle_U
=\langle x,f_*y\rangle_X. \tag{8.6}
$$

For a correspondence $\Gamma=\beta_*\alpha^*$, reverse the two adjunctions to find

$$
\langle\Phi(\Gamma)x,y\rangle_D
=\langle x,\Phi(\Gamma^t)y\rangle_C. \tag{8.7}
$$

This is the finite component-group shadow of the generic Rosati identity.

### 8.3 Agreement with polarization duality

The canonical principal polarization identifies a Jacobian with its dual on the generic fiber. Its integral extension relates the Néron models, and in the semistable case the induced component duality is exactly (8.3).

**Theorem 8.1 (three-level adjunction).** Let $C$ and $D$ have semistable reduction and let $\Gamma:C\dashrightarrow D$ be a finite correspondence. Then transpose is adjoint at all three levels:

1. on generic Jacobians for the canonical polarizations;
2. on the toric cycle lattices for the weighted monodromy pairings;
3. on component groups for the discriminant pairings.

**Proof.** The generic statement is (2.7). Resolve the correspondence compatibly with semistable models. Edgewise projection proves the lattice statement (7.7) for each finite map, hence for their pull–norm composite. The discriminant statement follows from (8.5). Independence of resolution follows from subdivision invariance and the uniqueness of the Néron extension. $\square$

This theorem is stronger than a determinant identity. It controls actual finite-group homomorphisms and their kernels, including nonsaturated phenomena invisible over $\mathbf Q$.

### 8.4 Self-adjoint operators

If $\Gamma=\Gamma^t$, then $\Gamma_J$ is Rosati self-adjoint and $\Phi(\Gamma)$ is self-adjoint for (8.3). More generally, if a correspondence algebra carries the involution $T\mapsto T^t$, its action on the component group is a module with a perfect invariant pairing:

$$
\langle Tx,y\rangle=\langle x,T^ty\rangle. \tag{8.8}
$$

Self-adjointness does not imply diagonalizability over $\mathbf Z$ or modulo a prime. A finite self-adjoint operator can have repeated elementary divisors, and reduction of an integral algebra can acquire nilpotents. What adjunction supplies is exact control of annihilators: for a subgroup $M$ stable under the algebra, its orthogonal complement is stable under the transposed algebra.

## 9. Specialization of divisors and correspondences

### 9.1 Closing a divisor class

Let $R$ be strict henselian and let $A=\sum_Pn_P[P]$ be a degree-zero divisor on $C$. After replacing each closed point by its geometric orbit, take its horizontal closure $\overline A$ in a regular model $\mathcal X$. By moving within its divisor class when necessary, we may arrange that it meets the special fiber in its smooth locus and avoids the finitely many points at which a resolved correspondence is not well behaved.

Its component is represented by

$$
\rho_{\mathcal X}(A)=
((\overline A\cdot X_i))_i. \tag{9.1}
$$

The weighted sum of these entries is zero. A different horizontal representative of the same generic class changes (9.1) by $M_{\mathcal X}a$ for an integral vertical vector $a$, by (6.5). Hence

$$
\operatorname{sp}_{\mathcal X}([A])
=[\rho_{\mathcal X}(A)]\in\Phi_C(k^s). \tag{9.2}
$$

If $P$ and $Q$ specialize to smooth points on components $X_i$ and $X_j$, then $[P-Q]$ specializes to $[e_i-e_j]$ in a reduced geometric fiber. If the points have nontrivial residue fields, the vector is the sum over the full geometric orbit. Forgetting that orbit changes both degree and Galois equivariance.

### 9.2 Specialization commutes with a resolved action

Let (3.3) resolve a correspondence. Begin with $A$ as above. Its generic pullback $\alpha^*A$ has a horizontal closure on $\mathcal H$. The difference between that closure and $a^*\overline A$ is vertical: they agree generically. Thus their component vectors define the same class. Proper pushforward by $b$ then gives a horizontal divisor representing $\beta_*\alpha^*A$; any discrepancy is again vertical.

Projection formula (6.12) gives

$$
\rho_{\mathcal Y}(\beta_*\alpha^*A)
\equiv E_b^tD_a\rho_{\mathcal X}(A)
\pmod{M_{\mathcal Y}\mathbf Z^{I_Y}}. \tag{9.3}
$$

Here $D_a$ is the multidegree pullback matrix from (6.8), and $E_b$ is the component pullback matrix from (6.6). Therefore

$$
\operatorname{sp}_D(\Gamma_J[A])
=\Phi(\Gamma)\operatorname{sp}_C([A]). \tag{9.4}
$$

**Theorem 9.1 (specialization compatibility).** For every finite correspondence, the square

$$
\begin{array}{ccc}
J_C(K^{\mathrm{sh}})&\xrightarrow{\Gamma_J}&J_D(K^{\mathrm{sh}})\\
\downarrow\operatorname{sp}_C&&\downarrow\operatorname{sp}_D\\
\Phi_C(k^s)&\xrightarrow{\Phi(\Gamma)}&\Phi_D(k^s)
\end{array} \tag{9.5}
$$

commutes. If a resolved model is used, its lower arrow is calculated by (9.3).

**Proof.** The Néron homomorphism sends a section to a section and commutes with reduction, proving the square abstractly. The divisor argument above proves that the resolved formula calculates the same square. $\square$

### 9.3 Vertical corrections and rational pairings

The component class can also be detected by failure of integral balancing. Given the vector $d=\rho_{\mathcal X}(A)$, solve

$$
M_{\mathcal X}v=-d \tag{9.6}
$$

over $\mathbf Q$. A solution exists because $m\cdot d=0$, and it is unique modulo the whole fiber. The rational vertical divisor

$$
\Psi(A)=\sum_iv_iX_i
$$

makes $\overline A+\Psi(A)$ orthogonal to every component. It can be chosen integral exactly when the component class (9.2) vanishes.

For two degree-zero divisors $A,B$ with disjoint generic support, the corrected local intersection

$$
(\overline A\cdot\overline B)
-(\Psi(A)\cdot\Psi(B)) \tag{9.7}
$$

is symmetric and independent of adding whole fibers to the corrections. Projection gives

$$
\langle f^*A,B\rangle
=\langle A,f_*B\rangle. \tag{9.8}
$$

For a correspondence this yields adjunction with its transpose. In the semistable case, the fractional part of the rational correction pairing is the discriminant pairing (8.3). Thus the intersection and graph descriptions are two presentations of the same component duality.

### 9.4 Composition after specialization

Let $\Gamma:C\dashrightarrow D$ and $\Delta:D\dashrightarrow E$. Resolve each correspondence separately; there is no need to construct a single model on which every raw closure composition is exact. The specialization maps satisfy

$$
\Phi(\Delta\circ\Gamma)
=\Phi(\Delta)\Phi(\Gamma), \tag{9.9}
$$

because both sides are reductions of the same generic composite. If common regular dominations are chosen, (9.9) can also be proved by inserting the component matrices and using (6.10)--(6.14). Exceptional matrices cancel through the birational identifications.

This explains the correct role of vertical excess intersections. They may change a representative matrix before quotienting, but their contribution lies in the image of the vertical intersection matrix. They therefore vanish in the component quotient and cannot violate (9.9).

## 10. Base change and change of models

### 10.1 Étale and unramified change

Under an étale base change $S'\to S$, regularity is preserved, Néron models base-change, and finite locally free correspondence diagrams remain finite locally free. Geometric components may split into smaller Galois orbits, but the geometric graph and its pairing are obtained by scalar extension with descent data retained.

For a closed point, an unramified extension of discrete valuation rings leaves every node thickness unchanged. It can split a nonsplit node or a nongeometric component, making more vertices and orientations visible over the new residue field. The finite étale group $\Phi_C$ simply base-changes. Thus

$$
\Phi_C(k')=\Phi_C(k^s)^{G_{k'}} \tag{10.1}
$$

when the residue setting permits the usual invariant description. The correspondence action commutes with this Galois action.

Residue-field splitting is not multiplication of the component group. The underlying geometric finite group is unchanged; only the subgroup of rational points can grow. Similarly, a nonsplit torus becomes split without changing its geometric character lattice.

### 10.2 Ramified change

Let $R'/R$ have ramification index $e$. Base-changing a local node equation gives

$$
xy=u\pi^n
\quad\longmapsto\quad
xy=u'(\pi')^{en}. \tag{10.2}
$$

After normalization and resolution, every geometric edge length is multiplied by $e$. The cycle lattice is unchanged if no new combinatorial splitting occurs, while

$$
q_{R'}=e q_R. \tag{10.3}
$$

Writing $X=H_1(G,\mathbf Z)$, the inclusions $eqX\subset qX\subset X^\vee$ give an exact sequence

$$
0\longrightarrow X/eX
\xrightarrow{q}
\Phi_{C_{K'}}(k^s)
\longrightarrow\Phi_C(k^s)
\longrightarrow0. \tag{10.4}
$$

The sequence need not split. Its order consequence is

$$
|\Phi_{C_{K'}}|=e^{b_1(G)}|\Phi_C|. \tag{10.5}
$$

These formulas require semistable reduction and unchanged geometric combinatorics apart from scaling. Outside that range, normalization can split components and additive parts can change; the old component group alone does not determine the new one.

### 10.3 Compatibility of correspondence actions with ramification

There is a canonical comparison morphism

$$
\mathcal J_C\times_RR'\longrightarrow\mathcal J_{C_{K'}}. \tag{10.6}
$$

For a correspondence, the square formed by (10.6) for $C$ and $D$ commutes. Both composites extend the base-changed generic homomorphism, and uniqueness supplies the equality.

In the semistable lattice description, multiplying both source and target pairings by $e$ preserves the adjunction identity

$$
e q_D(\Gamma x,y)=e q_C(x,\Gamma^ty). \tag{10.7}
$$

Thus the maps induced on the enlarged discriminant groups remain transposes. The new kernels contributed by $X/eX$ are stable under the correspondence algebra, and the action on them is the reduction modulo $e$ of the action on the cycle lattice.

### 10.4 Subdivision, contraction, and stable models

Resolving a thick node subdivides an edge of length $n$ into $n$ unit edges. A cycle has the same coefficient on every segment, so its pairing contribution remains $ncc'$. Subdivision therefore preserves the cycle lattice with its metric pairing and hence preserves the component group and all correspondence actions.

Conversely, contracting a chain of valence-two rational components adds its edge lengths. This also preserves the metrized cycle lattice. A map of stable graphs should therefore be interpreted metrically, whereas a map of regular graphs can be interpreted on the expanded unit-edge chains.

Blowing up a smooth point of a fiber is different: it creates a rational tail rather than subdividing a cycle edge. That tail contributes no graph homology and disappears under stabilization. Blowing up a node in an arbitrary model can introduce multiplicities in the total transform; one must not redraw it as a reduced subdivision without checking the fiber divisor. The general intersection presentation of Chapter 6 remains valid through this intermediate stage.

### 10.5 Global compatibility

Let $S$ be an excellent Dedekind scheme and let $U\subset S$ be the open on which both Jacobians have good reduction and the correspondence admits a finite locally free model. On $U$, formula (5.8) gives the relative operator. At each point of $S\setminus U$, the Néron extension gives the unique local operator and Chapters 6--9 calculate it. These maps glue because they agree on the generic fiber.

For rational points, collecting local component maps gives a commutative diagram

$$
\begin{array}{ccc}
J_C(K)&\xrightarrow{\Gamma_J}&J_D(K)\\
\downarrow&&\downarrow\\
\displaystyle\bigoplus_{s\notin U}\Phi_{C,s}(k(s))
&\xrightarrow{\oplus\Phi_s(\Gamma)}&
\displaystyle\bigoplus_{s\notin U}\Phi_{D,s}(k(s)).
\end{array} \tag{10.8}
$$

No surjectivity of the vertical arrows is implied. Global points need not realize arbitrary tuples of local components.

## 11. Exact examples

### 11.1 A graph and its transpose

Let $f:C\to D$ be finite of degree $d$. The graph correspondence acts by $f_*$ and its transpose by $f^*$. On Néron models,

$$
\mathcal f_*\mathcal f^*=[d]_{\mathcal J_D}, \tag{11.1}
$$

so on component groups

$$
\Phi(f_*)\Phi(f^*)=[d]_{\Phi_D}. \tag{11.2}
$$

Suppose $d$ is prime to $|\Phi_D|$. Then $[d]$ is an automorphism of $\Phi_D$, and $d^{-1}\Phi(f_*)$ is a left inverse of $\Phi(f^*)$. This does not force either map to be an isomorphism unless a corresponding relation in the other order is available.

If $f$ is a double cover with involution $\iota$, then

$$
\mathcal f^*\mathcal f_*=1+\mathcal \iota^*. \tag{11.3}
$$

The same identity holds on toric lattices and component groups. On an anti-invariant component class, the right side vanishes. Replacing it by multiplication by two would therefore give a wrong integral action.

### 11.2 One loop

Let $C$ have semistable reduction with dual graph consisting of one vertex and one loop of length $n$. Then

$$
X(G)=\mathbf Z,
\qquad q=[n],
\qquad \Phi_C(k^s)=\mathbf Z/n\mathbf Z. \tag{11.4}
$$

An integral self-correspondence acts on the cycle lattice by multiplication by some integer $a$. Its transpose acts by the same integer because a rank-one symmetric pairing has the same adjoint. The induced component action is

$$
x\longmapsto ax\pmod n. \tag{11.5}
$$

If the loop is nonsplit, Galois can act by $x\mapsto-x$ on both the cycle lattice and component group. Multiplication by $a$ commutes with this action, but the rational subgroup is

$$
(\mathbf Z/n\mathbf Z)^{x\mapsto-x}
=\{x:2x=0\}, \tag{11.6}
$$

which can be much smaller than the geometric group.

Under ramified base change of index $e$, the new component group is $\mathbf Z/en\mathbf Z$. The reduction map to the old group is reduction modulo $n$, and its kernel has order $e$, agreeing with (10.4).

### 11.3 Two components joined by parallel edges

Let the special fiber have two normalized components joined by $r$ unit edges. Its graph has first Betti number $r-1$, and

$$
\Phi_C\simeq\mathbf Z/r\mathbf Z. \tag{11.7}
$$

At the vertex-divisor level, the Laplacian is

$$
\begin{pmatrix}r&-r\\-r&r\end{pmatrix}, \tag{11.8}
$$

so the degree-zero vector $(1,-1)$ has order $r$. A divisor $P-Q$ with $P$ reducing to the first component and $Q$ to the second generates the component group when both points are geometric and smooth.

Suppose a self-correspondence induces on vertex divisors the matrix

$$
A=\begin{pmatrix}a&b\\b&a\end{pmatrix}. \tag{11.9}
$$

It preserves total degree and sends $(1,-1)$ to $(a-b)(1,-1)$. Thus its component action is multiplication by $a-b$ modulo $r$. The row sum $a+b$ controls total degree and disappears from degree-zero components. This elementary calculation illustrates why a vertex action must be reduced on the correct lattice rather than read from total degrees.

If the edges have lengths $n_1,\ldots,n_r$, a cycle basis $e_i-e_r$ has Gram matrix

$$
Q_{ij}=\begin{cases}
n_i+n_r,&i=j,\\
n_r,&i\ne j.
\end{cases} \tag{11.10}
$$

Its determinant is

$$
\sum_{j=1}^r\prod_{i\ne j}n_i. \tag{11.11}
$$

Smith normal form, not (11.11) alone, determines the component group.

### 11.4 Two loops and nonsaturated images

Let the graph have one vertex and two loops of lengths $a$ and $b$. Then

$$
q=\begin{pmatrix}a&0\\0&b\end{pmatrix},
\qquad
\Phi_C\simeq\mathbf Z/a\mathbf Z\oplus\mathbf Z/b\mathbf Z. \tag{11.12}
$$

Consider a cycle-lattice operator

$$
T=\begin{pmatrix}1&1\\0&2\end{pmatrix}. \tag{11.13}
$$

It defines an endomorphism of the discriminant presentation only when $T^tq$ maps compatibly with $qT^\dagger$ for an integral adjoint arising from a geometric transpose. For $a=b=n$, the adjoint for $q=nI$ is $T^t$, and the induced component map is reduction of $T$ modulo $n$.

The image of $T$ in $\mathbf Z^2$ has index two. Over $\mathbf Q$ it is an isomorphism, but modulo an even $n$ its cokernel has a nontrivial $2$-part. This is the simplest model of a nonsaturated correspondence image: rational invertibility does not imply integral invertibility on components.

### 11.5 Compact type and good reduction of the graph part

If the dual graph is a tree, then $H_1(G,\mathbf Z)=0$ and $\Phi_C=0$. Every correspondence acts trivially on the toric and component layers. It still acts nontrivially on

$$
\mathcal J_{C,k}^0\simeq\prod_vJ(C_v^\nu), \tag{11.14}
$$

through pullback and norm among normalized components.

Thus “trivial component action” does not mean “trivial specialization.” It records only the discrete quotient. In compact type, all specialized information is carried by the abelian identity component. In a one-loop fiber of length one, the component group is also trivial, but a torus survives. These two cases have the same component group and different connected reduction.

### 11.6 Good reduction

If $\mathcal X$ and $\mathcal Y$ are smooth proper curves over $R$ and the correspondence extends through finite locally free maps, the Jacobian models are abelian schemes and their component groups vanish. Formula (5.8) specializes directly to the correspondence of smooth special fibers.

For every prime $\ell$ invertible in $R$, the action on $T_\ell J_C$ specializes to the action on the Tate module of the special Jacobian. The integral Néron discussion adds no correction term because there is no vertical separation defect. This example is the boundary case against which the bad-reduction formulas should be checked.

## 12. Integral correspondence and Hecke algebras

### 12.1 The operator algebra

Let $\mathbb T_0$ be a ring generated by finite self-correspondences on $C$, with relations imposed at the level of generic cycles or their actions on $J_C$. The integral extension theorem gives a ring homomorphism

$$
\mathbb T_0\longrightarrow
\operatorname{End}_S(\mathcal J_C). \tag{12.1}
$$

At every closed point it induces compatible actions on

$$
\mathcal J_{C,s}^0,
\qquad
\Phi_{C,s},
\qquad
X^*(T_s)
$$

when the connected special fiber has toric part $T_s$. In the semistable case the last module is the graph cycle lattice. All actions are integral: no denominator is introduced merely to extend a correspondence.

If $\mathbb T_0$ is stable under transpose, it is a ring with anti-involution

$$
T\longmapsto T^t,
\qquad
(UV)^t=V^tU^t. \tag{12.2}
$$

The canonical polarization and component pairings satisfy

$$
\langle Tx,y\rangle=\langle x,T^ty\rangle. \tag{12.3}
$$

In common Hecke situations the distinguished generators are symmetric or are paired by a simple involution. The theory here does not require commutativity.

### 12.2 Integral structures preserved by the action

A smooth group scheme $\mathcal J/S$ has a locally free Lie algebra

$$
\operatorname{Lie}(\mathcal J/S)=e^*\mathcal T_{\mathcal J/S}
$$

and a locally free module of invariant differentials

$$
\omega_{\mathcal J/S}=e^*\Omega^1_{\mathcal J/S}. \tag{12.4}
$$

Every correspondence endomorphism acts covariantly on the Lie algebra by its differential and contravariantly on invariant differentials by pullback. Thus (12.1) supplies natural integral lattices in the generic tangent and cotangent representations.

At a semistable point, the exact sequence (7.4) yields corresponding maps on the torus and normalized-component abelian varieties. On character groups the variance is contravariant, so it must be matched carefully with the covariant map on the torus itself. The component group is covariant under the Néron homomorphism.

For a prime $\ell$ distinct from the residue characteristic, every generic correspondence also acts on $T_\ell J_C$. This action is compatible with the Néron operator and with unramified specialization. At the residue characteristic, the Néron model and its Lie algebra remain meaningful, but geometric torsion points do not by themselves describe the full finite flat torsion. No prime-to-characteristic argument should be silently transferred to that case.

### 12.3 The finite-flat locus and bad places

There is often a dense open $U\subset S$ over which the curves are smooth and the correspondence diagram is finite locally free. On $U$, the action is literally pullback followed by determinant norm. At a finite set of bad places, normalized closures and regular resolutions calculate the same global Néron endomorphism.

This gives a practical division of labor:

$$
\begin{array}{c|c}
\text{place in }U&\text{relative pull--norm on abelian schemes}\\
\hline
\text{place outside }U&\text{Néron extension plus intersection or graph calculation}.
\end{array} \tag{12.5}
$$

The algebra relations do not have to be reproved separately at bad places. Since they hold generically, uniqueness forces them on Néron models. Geometry at a bad place is needed to compute the resulting operator, not to establish that the abstract relation survives.

### 12.4 Ideals, quotients, and component support

Let $I\subset\mathbb T_0$ be an ideal. The subgroups

$$
\Phi[I]=\{x\in\Phi:Ix=0\},
\qquad
I\Phi=\langle tx:t\in I,x\in\Phi\rangle \tag{12.6}
$$

are finite and computable from the integral component matrices. Rational eigenspace calculations cannot determine them when saturation is at issue.

If $I$ is stable under transpose, the perfect semistable component pairing gives

$$
(I\Phi)^\perp=\Phi[I^t]. \tag{12.7}
$$

Indeed $x$ is orthogonal to every $ty$ exactly when $t^tx=0$ for every $t\in I$. When $I=I^t$, annihilator subgroups and quotient duals are thereby linked. This identity is often the finite arithmetic content behind self-dual Hecke modules.

One must distinguish the image of an idempotent in $\mathbb T_0\otimes\mathbf Q$ from an integral direct summand. A rational idempotent may require a denominator, and its intersection with an integral Néron or component lattice can fail to be a direct summand. The denominator and the saturation quotient must be controlled before an “integral eigenspace” is asserted.

### 12.5 A criterion for a well-defined integral Hecke action

The preceding theory can be summarized as a checklist internal to the mathematics.

**Theorem 12.1 (integral correspondence algebra package).** Let $C/K$ be a smooth proper geometrically connected curve over the function field of an excellent Dedekind scheme, and let $\mathbb T_0$ be generated by finite self-correspondences presented by smooth normalization curves. Then:

1. every $T\in\mathbb T_0$ acts uniquely on the Néron model $\mathcal J_C$;
2. all generic additive and multiplicative relations hold on $\mathcal J_C$, its identity components, and its component groups;
3. over a finite locally free locus the action is relative pullback followed by norm;
4. at every remaining place a normalized resolved closure calculates the same action through intersection matrices;
5. in the semistable case the action is the map on the weighted graph discriminant induced by the dual of the transpose graph-lattice map, equivalently by the adjoint pair attached to the correspondence;
6. unramified base change commutes with the action, while ramified base change commutes through the canonical Néron comparison;
7. transpose is the polarized adjoint generically and the discriminant adjoint on semistable component groups.

**Proof.** Items 1 and 2 are Theorem 4.1. Item 3 is Section 5.5. Items 4 and 5 are Theorem 5.1, formula (6.15), and (7.3)--(7.10). Item 6 follows from Sections 4.3 and 10. Item 7 is Theorems 4.3 and 8.1. $\square$

This theorem is the precise meaning of an integral Hecke action in the present setting. It asserts an action on canonical integral geometry, not merely a collection of operators on a rational cohomology space.

## 13. The complete correspondence package

### 13.1 The main theorem

We collect the theory in a form usable without repeating the construction.

**Theorem 13.1 (integral correspondences on curves and Jacobians).** Let $S$ be an excellent connected Dedekind scheme with function field $K$. Let $C$ and $D$ be smooth proper geometrically connected $K$-curves, and let

$$
\Gamma=(C\xleftarrow{\alpha}H\xrightarrow{\beta}D)
$$

be a finite correspondence with $H$ smooth and proper.

1. The generic formula $\Gamma_J=\beta_*\alpha^*$ defines a homomorphism $J_C\to J_D$. It is additive, respects cycle composition, and has polarized adjoint $(\Gamma^t)_J$.
2. The homomorphism extends uniquely to $\mathcal \Gamma:\mathcal J_C\to\mathcal J_D$. It preserves identity components and induces $\Phi(\Gamma):\Phi_C\to\Phi_D$ at every closed point.
3. Given regular models $\mathcal X,\mathcal Y$, the closure of every integral component of $\Gamma$ is proper and flat over $S$. After finite normalization and resolution it admits a regular domination $\mathcal X\leftarrow\mathcal H\to\mathcal Y$; any two choices have a common regular domination.
4. Pullback and proper pushforward through such a domination descend through the separated relative Picard quotients and give $\mathcal \Gamma$. Exceptional and vertical excess terms lie in the closures of the generic identities.
5. If a geometric special fiber of $\mathcal X$ is $\sum m_iX_i$, then

   $$
   \Phi_C(k^s)=
   \{d\in\mathbf Z^I:\sum m_id_i=0\}/M_{\mathcal X}\mathbf Z^I.
   $$

   For a resolved correspondence, pullback is represented by component-degree matrices, pushforward by the transpose of divisor-pullback multiplicity matrices, and their composite gives $\Phi(\Gamma)$.
6. If the curves are semistable, their component groups are discriminants of the weighted cycle pairings. The covariant graph-lattice operator is $u_\Gamma=\beta_*\alpha^*$, including branch and residue degrees; the component map is induced on dual lattices by $v_\Gamma^\vee$, where $v_\Gamma=\alpha_*\beta^*$ is its adjoint. This discriminant map is $\Phi(\Gamma)$.
7. Transpose is adjoint for canonical polarizations, weighted cycle pairings, and semistable component pairings. All these statements are Galois equivariant.
8. Specialization of divisor classes commutes with $\Gamma$. Étale base change commutes directly; ramified base change commutes through canonical Néron comparison maps and scales semistable edge lengths by the ramification index.

**Proof.** Generic pullback, norm, composition, and duality were proved in Chapter 2. Chapter 3 proves the closure and domination statements. Chapter 4 gives the unique Néron extension. Chapter 5 identifies it with the resolved Picard construction. Chapter 6 proves the intersection-lattice formulas and their birational invariance. Chapters 7 and 8 give the semistable and adjoint descriptions. Chapters 9 and 10 prove specialization and base-change compatibility. $\square$

Every hypothesis has a visible function. Smooth proper generic curves have Jacobians and finite norms with the stated behavior. Excellence makes normalization finite and resolution available. Regular models make vertical components Cartier and permit intersection matrices. Semistability is invoked only for graph tori and perfect discriminant pairings, not for the existence of the Néron extension.

### 13.2 What can and cannot be read from a curve model

A curve model can calculate a Néron correspondence only after its geometry has been controlled. A finite locally free diagram gives direct pull–norm. A normalized resolved closure gives a correct intersection calculation. An arbitrary raw closure, by contrast, may hide contracted components, nonflat degree, or vertical excess.

The component group alone also has limits. It does not determine the connected special fiber. A tree and a unit loop can both have trivial component group, while one has abelian compact-type reduction and the other has a torus. The order of a component group does not determine its invariant factors, and the geometric group does not determine its rational points without the residue Galois action.

Similarly, a rational graph action does not determine an integral component action. Saturation indices and denominators of rational idempotents are finite arithmetic data. The integral lattices and their Smith forms must be retained.

### 13.3 A reusable local calculation

At a closed point, one can now calculate a correspondence without ambiguity.

Choose regular models and resolve the normalized closure. Record special-fiber multiplicities, residue fields, and every contracted component. Form the vertical intersection matrices and verify their one-dimensional rational radicals. Compute the divisor-pullback matrices $E$ and component-degree matrices $D$, checking

$$
DM_X=M_HE.
$$

Form $E_b^tD_a$ and pass to the finite cokernels. In the semistable case, one may instead compute on oriented geometric edges, verify harmonicity, retain thicknesses, restrict to integral cycle lattices, and pass to discriminants. The two calculations agree.

Test the answer against generic identities, transpose adjunction, and Galois equivariance. If a relation fails, the error lies before the quotient: typically an omitted residue degree, a copied rather than transformed edge length, or a lost exceptional component.

### 13.4 Conclusion

A finite correspondence begins as a one-dimensional relation between generic curves. Its integral meaning is not the naive closure of that relation, but the canonical homomorphism it induces on the Néron models of their Jacobians. Closure, normalization, and resolution supply a geometric representative; the separated Picard quotient removes exactly the vertical ambiguity introduced by those choices.

Intersection theory then turns the special fiber into a finite calculation. Component multiplicities impose the degree-zero lattice, the vertical intersection matrix records generically trivial twists, and their quotient is the component group. In semistable reduction, the same information becomes the weighted cycle lattice of the dual graph. Harmonic pullback and pushforward act on that lattice, and their adjunction descends to its finite discriminant.

The generic and integral theories therefore form one continuous structure. Composition survives because Néron extension is unique. Specialization commutes because resolved pull–norm respects vertical equivalence. Transpose survives as adjunction for polarizations, monodromy pairings, and component groups. Base change is exact in the unramified direction and controlled by metric scaling and canonical comparison in the ramified direction.

This is the integral correspondence package required for Hecke actions. A correspondence algebra acts on the Néron model, its connected reduction, its toric lattice, its component group, and its tangent and cotangent lattices, with all relations and adjoints intact. The geometry of bad fibers does not destroy the generic operators; it refines them into integral, connected, and finite layers that can be calculated separately and then reassembled canonically.
