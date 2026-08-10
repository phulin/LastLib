# Global Galois Cohomology and Selmer Groups

## Contents

1. [The global cohomological arena](#1-the-global-cohomological-arena)
   - [From one local field to all places](#11-from-one-local-field-to-all-places)
   - [Absolute Galois groups and geometric points](#12-absolute-galois-groups-and-geometric-points)
   - [Decomposition groups and completions](#13-decomposition-groups-and-completions)
   - [Archimedean places](#14-archimedean-places)
   - [Choosing the finite set $S$](#15-choosing-the-finite-set-s)
2. [Ramification restricted to $S$](#2-ramification-restricted-to-s)
   - [The maximal extension $K_S$](#21-the-maximal-extension-k_s)
   - [The quotient $G_{K,S}$](#22-the-quotient-g_ks)
   - [Modules and the ramification criterion](#23-modules-and-the-ramification-criterion)
   - [Enlarging $S$](#24-enlarging-s)
   - [A first example over $\mathbf Q$](#25-a-first-example-over-mathbf-q)
3. [Global cohomology and its size](#3-global-cohomology-and-its-size)
   - [Continuous cohomology in the restricted quotient](#31-continuous-cohomology-in-the-restricted-quotient)
   - [Finiteness with exact hypotheses](#32-finiteness-with-exact-hypotheses)
   - [Cohomological dimension and the real-place exception](#33-cohomological-dimension-and-the-real-place-exception)
   - [Inflation back to the absolute group](#34-inflation-back-to-the-absolute-group)
   - [Finite fields, lattices, and vector spaces](#35-finite-fields-lattices-and-vector-spaces)
4. [Localization](#4-localization)
   - [Why a global class has local shadows](#41-why-a-global-class-has-local-shadows)
   - [Construction and independence of choices](#42-construction-and-independence-of-choices)
   - [Localization in low degrees](#43-localization-in-low-degrees)
   - [Products, sums, and restricted products](#44-products-sums-and-restricted-products)
   - [The archimedean modification](#45-the-archimedean-modification)
5. [Unramified classes and local conditions](#5-unramified-classes-and-local-conditions)
   - [The condition outside $S$](#51-the-condition-outside-s)
   - [Why a local condition is a subgroup](#52-why-a-local-condition-is-a-subgroup)
   - [Unramified, relaxed, and strict conditions](#53-unramified-relaxed-and-strict-conditions)
   - [Kummer conditions](#54-kummer-conditions)
   - [Finite-flat-shaped conditions](#55-finite-flat-shaped-conditions)
   - [Changing and comparing local conditions](#56-changing-and-comparing-local-conditions)
6. [Selmer structures and Selmer kernels](#6-selmer-structures-and-selmer-kernels)
   - [The assembly problem](#61-the-assembly-problem)
   - [Definition of a Selmer structure](#62-definition-of-a-selmer-structure)
   - [The kernel and fiber-product formulations](#63-the-kernel-and-fiber-product-formulations)
   - [Built-in conditions outside $S$](#64-built-in-conditions-outside-s)
   - [Varying the local conditions](#65-varying-the-local-conditions)
   - [Basic exact sequences from the definition](#66-basic-exact-sequences-from-the-definition)
7. [Morphisms and exact coefficient sequences](#7-morphisms-and-exact-coefficient-sequences)
   - [Compatibility is extra data](#71-compatibility-is-extra-data)
   - [Functoriality of Selmer groups](#72-functoriality-of-selmer-groups)
   - [Cartesian local conditions](#73-cartesian-local-conditions)
   - [The left-hand defect](#74-the-left-hand-defect)
   - [The lifting defect](#75-the-lifting-defect)
   - [A usable exactness criterion](#76-a-usable-exactness-criterion)
8. [Changing the number field](#8-changing-the-number-field)
   - [Restriction and places above places](#81-restriction-and-places-above-places)
   - [Corestriction and summation](#82-corestriction-and-summation)
   - [Induced local conditions](#83-induced-local-conditions)
   - [Shapiro and decomposition over places](#84-shapiro-and-decomposition-over-places)
   - [Restriction--corestriction checks](#85-restriction--corestriction-checks)
9. [Dual Selmer structures](#9-dual-selmer-structures)
   - [Local duality turns permission into annihilation](#91-local-duality-turns-permission-into-annihilation)
   - [Finite coefficients and exact orthogonals](#92-finite-coefficients-and-exact-orthogonals)
   - [The dual Selmer structure](#93-the-dual-selmer-structure)
   - [Natural pairs of conditions](#94-natural-pairs-of-conditions)
   - [What local duality does not prove globally](#95-what-local-duality-does-not-prove-globally)
10. [Kummer theory, units, and class groups](#10-kummer-theory-units-and-class-groups)
    - [Restricted ramification in Kummer coordinates](#101-restricted-ramification-in-kummer-coordinates)
    - [$S$-units and the $S$-class group](#102-s-units-and-the-s-class-group)
    - [The multiplicative Selmer structure](#103-the-multiplicative-selmer-structure)
    - [Ordinary and narrow phenomena at real places](#104-ordinary-and-narrow-phenomena-at-real-places)
    - [A calculation over $\mathbf Q$](#105-a-calculation-over-mathbf-q)
11. [Elliptic curves and character groups](#11-elliptic-curves-and-character-groups)
    - [The $n$-Selmer group of an elliptic curve](#111-the-n-selmer-group-of-an-elliptic-curve)
    - [Why the local Kummer image is the right condition](#112-why-the-local-kummer-image-is-the-right-condition)
    - [The basic Mordell--Weil exact sequence](#113-the-basic-mordell--weil-exact-sequence)
    - [Unramified character groups](#114-unramified-character-groups)
    - [Strict and relaxed auxiliary primes](#115-strict-and-relaxed-auxiliary-primes)
12. [Limits and topological coefficients](#12-limits-and-topological-coefficients)
    - [Why finite-level notation cannot simply be reused](#121-why-finite-level-notation-cannot-simply-be-reused)
    - [Lattices](#122-lattices)
    - [Discrete torsion modules](#123-discrete-torsion-modules)
    - [Vector-space coefficients](#124-vector-space-coefficients)
    - [Infinite-level local conditions and duality](#125-infinite-level-local-conditions-and-duality)
13. [Adjoint Selmer groups and deformation tangents](#13-adjoint-selmer-groups-and-deformation-tangents)
    - [The global tangent cocycle](#131-the-global-tangent-cocycle)
    - [Local deformation conditions as subspaces](#132-local-deformation-conditions-as-subspaces)
    - [The tangent space is a Selmer group](#133-the-tangent-space-is-a-selmer-group)
    - [Fixed determinant and the trace-zero adjoint](#134-fixed-determinant-and-the-trace-zero-adjoint)
    - [The dual tangent condition](#135-the-dual-tangent-condition)
14. [The reusable global dictionary](#14-the-reusable-global-dictionary)
    - [A construction protocol](#141-a-construction-protocol)
    - [Dictionary of objects and maps](#142-dictionary-of-objects-and-maps)
    - [Exactness audit](#143-exactness-audit)
    - [Conclusion](#144-conclusion)

## 1. The global cohomological arena

### 1.1 From one local field to all places

Local Galois cohomology describes the arithmetic visible from a single completion. A global object, however, must satisfy all local requirements at once. This is already apparent in elementary equations: an element of $K^\times$ has a valuation at every finite place and a sign at every real place, but those local data cannot be prescribed independently. Selmer theory is the language for imposing many local tests on one global cohomology class.

There are two separate tasks. First one must restrict the global Galois group so that only finitely many places can carry ramification. This produces a cohomology group of manageable size. Then one cuts that group further by prescribing, at each relevant place, which local classes are allowed. The first operation is built into $G_{K,S}$; the second is encoded by a Selmer structure. Confusing them is a common source of redundant or incorrect local conditions.

Throughout, $K$ is a number field, $\overline K$ is a fixed algebraic closure, and

$$
G_K=\operatorname{Gal}(\overline K/K).
$$

All finite modules are discrete continuous modules. Thus their action factors through a finite quotient. Continuous cohomology, restriction, corestriction, connecting maps, cup products, and Shapiro's lemma are used in the forms established earlier.

### 1.2 Absolute Galois groups and geometric points

A place $v$ of $K$ does not by itself determine a subgroup of $G_K$. To obtain one, choose an extension $\overline v$ of $v$ to $\overline K$. Equivalently, for a finite place choose a $K$-embedding

$$
\iota_{\overline v}:\overline K\hookrightarrow \overline{K_v}
$$

whose induced absolute value extends $v$. For an archimedean place use an embedding into $\mathbf C$, with complex-conjugate embeddings representing the same place. The stabilizer

$$
D_{\overline v}=\{g\in G_K:g\overline v=\overline v\}
$$

is the **decomposition group**. At a finite place it is canonically isomorphic, after the choice, to $G_{K_v}$. Its inertia subgroup $I_{\overline v}$ corresponds to $I_{K_v}$.

The word “canonically” here is relative to the chosen geometric place. If $\overline v'=g\overline v$, then

$$
D_{\overline v'}=gD_{\overline v}g^{-1},
\qquad
I_{\overline v'}=gI_{\overline v}g^{-1}.
$$

Consequently decomposition groups are conjugacy classes of subgroups, not distinguished subgroups. This mild ambiguity is exactly matched by conjugation invariance of cohomology.

### 1.3 Decomposition groups and completions

At a finite place, why does a completion have the same local Galois group as the chosen decomposition group? The fixed field of $D_{\overline v}$ in $\overline K$ is the henselization of $K$ determined by $\overline v$. Passing from that henselization to its completion $K_v$ induces an equivalence on finite separable extensions. Equivalently, every finite separable extension of $K_v$ is obtained by completing a finite extension of $K$, and compatible embeddings and morphisms descend in the same way. Restriction therefore identifies $D_{\overline v}$ with $G_{K_v}$ relative to the chosen geometric place.

At a finite unramified place the quotient

$$
D_{\overline v}/I_{\overline v}\simeq
\operatorname{Gal}(\overline{k_v}/k_v)\simeq\widehat{\mathbf Z}
$$

is generated topologically by arithmetic Frobenius. We retain the convention that arithmetic Frobenius acts on $\overline{k_v}$ by $x\mapsto x^{q_v}$. If a representation is unramified at $v$, only this quotient acts on its coefficient module.

For a finite extension $L/K$, a choice of a place $w$ of $L$ above $v$ amounts, after compatible geometric choices, to a double-coset component. This fact later explains why restricting a global class from $K$ to $L$ produces one localization for every $w\mid v$, rather than a single local class.

### 1.4 Archimedean places

At a complex place, $G_{K_v}=G_{\mathbf C}=1$, so positive-degree local cohomology vanishes. At a real place,

$$
G_{K_v}=G_{\mathbf R}=\operatorname{Gal}(\mathbf C/\mathbf R)=\langle c\rangle\simeq C_2.
$$

For a $C_2$-module $M$,

$$
H^1(\mathbf R,M)=\ker(1+c)/\operatorname{im}(c-1).
$$

It is killed by $2$, and it vanishes when multiplication by $2$ is invertible on $M$. Thus archimedean places matter only to the $2$-primary theory, but in that theory they cannot be discarded.

Ordinary cohomology of $C_2$ is periodic in positive degrees. Global statements that are meant to stop in degree two therefore use **modified cohomology** at real places: replace ordinary local $H^i$ by Tate cohomology $\widehat H^i(C_2,M)$. In degree one there is no change,

$$
\widehat H^1(C_2,M)=H^1(C_2,M),
$$

so the definition of a Selmer group needs no alteration. The modification becomes essential in degree zero and in global duality sequences. Complex places contribute zero in the modified convention as well.

### 1.5 Choosing the finite set $S$

The set $S$ is the bookkeeping device that separates finitely many exceptional places from the uniform unramified world. We always take $S$ finite and containing every archimedean place. For a finite module $M$, a safe cohomological choice also contains

* every finite place whose residue characteristic divides $|M|$;
* every finite place at which the $G_K$-action on $M$ is ramified;
* every place at which a later local condition is not the unramified one.

If $M$ is a vector space over a finite field $k$ of characteristic $\ell$, “coefficient-characteristic places” means the places above $\ell$. For an $\ell$-adic lattice the same convention applies. A theorem may require fewer places, but this enlarged $S$ is stable under the standard constructions and makes finiteness and cohomological-dimension statements clean.

There is no mathematical virtue in taking $S$ minimal. Enlarging $S$ allows more ramification globally and transfers a formerly automatic unramified condition into an explicit local choice. A correct Selmer group is unchanged if the transferred condition is imposed at the new place. We will prove this independence rather than treat it as a notational slogan.

## 2. Ramification restricted to $S$

### 2.1 The maximal extension $K_S$

To encode “unramified outside $S$” in a single profinite group, take the compositum in $\overline K$ of all finite extensions of $K$ unramified at every finite place outside $S$. Its Galois closure has the same property, so the resulting field $K_S$ is Galois over $K$. It is the **maximal extension unramified outside $S$**.

Because all archimedean places belong to $S$, real places are allowed to become complex in $K_S$. If one instead forbids complexification, one obtains a different quotient and the narrow/ordinary distinction reappears. Our convention is the standard one for Selmer theory: infinity lies inside $S$, and any desired sign restriction is imposed explicitly as a real local condition.

Write

$$
G_{K,S}=\operatorname{Gal}(K_S/K).
$$

It carries the Krull topology. Equivalently, if $F$ runs through the finite Galois extensions of $K$ contained in $K_S$, then

$$
G_{K,S}\simeq\varprojlim_F\operatorname{Gal}(F/K)
$$

as a profinite group, with the finite Galois groups discrete. Thus every cohomology group below is continuous cohomology for this topology. The kernel $N_S$ introduced next is closed, so $G_{K,S}$ is also the topological quotient $G_K/N_S$, not merely an abstract quotient.

If $\overline v$ is a geometric place, the image of $D_{\overline v}$ in $G_{K,S}$ is again called a decomposition group. The homomorphism $G_{K_v}\simeq D_{\overline v}\to G_{K,S}$ is what defines localization. For $v\in S$ its inertia is not forced to vanish. For $v\notin S$, inertia maps trivially and the image decomposition group is a quotient of $G_{k_v}\simeq\widehat{\mathbf Z}$. Nothing in the definition of localization requires the local homomorphism to be injective.

### 2.2 The quotient $G_{K,S}$

Let $N_S=\operatorname{Gal}(\overline K/K_S)$. Then

$$
1\longrightarrow N_S\longrightarrow G_K
\longrightarrow G_{K,S}\longrightarrow1. \tag{2.1}
$$

The subgroup $N_S$ is the closed normal subgroup generated by all inertia groups $I_{\overline v}$ for finite $v\notin S$. Indeed, killing those inertia groups forces every finite quotient to be unramified away from $S$, while every such finite quotient kills them. This description is the bridge between the field-theoretic and representation-theoretic meanings of restricted ramification.

One should not say that $G_{K,S}$ is generated only by decomposition groups at places in $S$. Frobenius elements at the infinitely many places outside $S$ still carry essential information. What has been removed outside $S$ is inertia, not the entire local Galois action.

### 2.3 Modules and the ramification criterion

Let $M$ be a finite discrete $G_K$-module. The following conditions are equivalent:

1. the action of $G_K$ on $M$ factors through $G_{K,S}$;
2. $N_S$ acts trivially on $M$;
3. $I_{\overline v}$ acts trivially on $M$ for every finite $v\notin S$;
4. the representation $G_K\to\operatorname{Aut}(M)$ is unramified outside $S$.

The equivalence is not merely terminology. By the description of $N_S$, condition 3 says precisely that the closed normal subgroup killed in (2.1) lies in the kernel of the action. This proves $3\Rightarrow1$; the reverse implication is immediate.

For a discrete torsion module $A=\bigcup A_n$, the same equivalence holds provided “unramified outside $S$” means that every inertia group outside $S$ acts trivially on all of $A$. It is not enough that every element be ramified at only finitely many places depending on the element. A single quotient $G_{K,S}$ requires one uniform finite set.

**Counterexample.** Let $A$ be the direct sum of quadratic characters ramified at one new prime each. Every element of $A$ lies in a finite subsum and is ramified at finitely many primes, but no finite $S$ makes the whole action factor through $G_{K,S}$. Pointwise finite ramification is weaker than uniformly bounded ramification.

### 2.4 Enlarging $S$

If $S\subseteq S'$, then $K_S\subseteq K_{S'}$ and restriction gives a natural surjection

$$
G_{K,S'}\twoheadrightarrow G_{K,S}. \tag{2.2}
$$

Thus a $G_{K,S}$-module becomes a $G_{K,S'}$-module by inflation. The corresponding inflation map

$$
H^i(G_{K,S},M)\longrightarrow H^i(G_{K,S'},M)
$$

need not be an isomorphism: new global classes may ramify at the newly admitted primes. The original group is recovered by requiring the new localizations to remain unramified. In degree one this assertion is especially transparent and will be proved in Section 6.4.

The direction of (2.2) is worth checking. A larger $S'$ permits a larger field $K_{S'}$, hence has a larger Galois group over $K$ mapping onto the smaller restricted group. “More permitted ramification” means “more Galois classes,” not a smaller symmetry group.

### 2.5 A first example over $\mathbf Q$

Take $M=\mathbf Z/2\mathbf Z$ with trivial action and $S=\{2,\infty\}$. Then

$$
H^1(G_{\mathbf Q,S},M)
=\operatorname{Hom}_{\mathrm{cont}}(G_{\mathbf Q,S},\mathbf Z/2\mathbf Z)
$$

classifies quadratic extensions unramified at every odd prime. By the square-class description, such an extension is generated by the square root of a class represented by

$$
-1,\quad 2,\quad -2,
$$

or $1$. Hence this $H^1$ is two-dimensional over $\mathbf F_2$. The real place is not cosmetic: the class of $-1$ complexifies it. Imposing the strict condition at infinity removes that class, while permitting the full real local group retains it.

## 3. Global cohomology and its size

### 3.1 Continuous cohomology in the restricted quotient

For a discrete continuous $G_{K,S}$-module $M$, put

$$
H^i(K_S/K,M)=H^i(G_{K,S},M),
$$

and usually abbreviate it to $H^i(G_{K,S},M)$. The notation $H^i(K,M)$ continues to mean $H^i(G_K,M)$. These groups should not be silently identified: inflation relates them, and in low degree it becomes an isomorphism only under a specific vanishing condition on $N_S$.

Degree zero is

$$
H^0(G_{K,S},M)=M^{G_{K,S}}=M^{G_K}
$$

when the action factors through $G_{K,S}$. Degree one classifies $M$-torsors whose splitting fields are unramified outside $S$ after the action on $M$ has been trivialized. Degree two contains global extension obstructions. Selmer groups live inside degree one, but degree zero and degree two control their behavior in exact coefficient sequences.

### 3.2 Finiteness with exact hypotheses

The global theory is useful because restricted ramification turns finite coefficients into finite cohomology.

**Finiteness theorem.** Let $K$ be a number field, let $M$ be a finite discrete $G_{K,S}$-module, and suppose that $S$ is finite, contains the archimedean places, and contains every finite place whose residue characteristic divides $|M|$. Then $H^i(G_{K,S},M)$ is finite for every $i\geq0$.

The inclusion of coefficient-characteristic places is a clean sufficient hypothesis. Specialized finiteness results sometimes omit some of them, but no such sharpening will be used without being stated.

Here is the mechanism. After a finite extension unramified outside $S$, the action on $M$ becomes trivial. Inflation--restriction then reduces degree one to continuous homomorphisms into a finite group. Restricted ramification and bounded exponent allow only finitely many such abelian extensions; global class field theory expresses them through a finite ray-class quotient together with a finitely generated $S$-unit group. Higher degrees are controlled by finite cohomological dimension away from the real $2$-primary tail and by finite-group cohomology at that tail. Devissage through the prime-primary parts of $M$ completes the argument.

Without restricted ramification, finiteness fails dramatically. For example,

$$
H^1(G_{\mathbf Q},\mathbf Z/2\mathbf Z)
$$

contains the class of $\mathbf Q(\sqrt p)$ for every prime $p$ and is infinite. The finite set $S$ is therefore a mathematical hypothesis, not just a convenience for writing a direct sum.

### 3.3 Cohomological dimension and the real-place exception

Let $M$ be $\ell$-primary and assume that $S$ contains the places above $\ell$ and infinity. If either $\ell$ is odd or $K$ is totally imaginary, then

$$
H^i(G_{K,S},M)=0\qquad(i>2). \tag{3.1}
$$

For $\ell=2$ and a real place, ordinary cohomology does not vanish above degree two because $C_2$ has periodic $2$-primary cohomology. In that case $G_{K,S}$ has virtual $2$-cohomological dimension two: after passage to a totally imaginary finite extension, the higher groups vanish. Equivalently, the only higher-degree tail comes from real decomposition groups.

This is why later global duality uses a modified complex at infinity. It would be false to state (3.1) for arbitrary $2$-primary $M$ over a field with real embeddings. For example, with trivial $M=\mathbf Z/2\mathbf Z$,

$$
H^i(\mathbf R,M)\simeq\mathbf Z/2\mathbf Z
$$

for every $i>0$, and this periodic phenomenon cannot be erased by notation.

### 3.4 Inflation back to the absolute group

Apply inflation--restriction to (2.1). Since $N_S$ acts trivially on a module that factors through $G_{K,S}$, the beginning is

$$
0\to H^1(G_{K,S},M)\xrightarrow{\inf}H^1(K,M)
\xrightarrow{\operatorname{res}}H^1(N_S,M)^{G_{K,S}}
\to H^2(G_{K,S},M). \tag{3.2}
$$

Thus inflation is injective in degree one. Its image consists of classes trivial on $N_S$, equivalently classes unramified outside $S$. For torsors this means that, after accounting for the coefficient action, no new inertia appears away from $S$.

The same statement should not be promoted to all degrees without checking the higher cohomology of $N_S$. Degree one is special because the five-term sequence supplies an unconditional injection.

### 3.5 Finite fields, lattices, and vector spaces

If $M$ is finite-dimensional over a finite field $k$, all $H^i(G_{K,S},M)$ in the finite range are finite-dimensional $k$-vector spaces. A local condition must then be specified as a $k$-subspace if linear Selmer theory is intended; an arbitrary additive subgroup need not respect scalar multiplication.

Let $\mathcal O$ be the integers of a finite extension $E/\mathbf Q_\ell$, with uniformizer $\varpi$, and let $T$ be a finite free $\mathcal O$-module with continuous $G_{K,S}$-action. Its topology is profinite, not discrete. Under the usual continuous-cohomology definition and with $S$ containing the places above $\ell$, the groups $H^i(G_{K,S},T)$ for $i=0,1,2$ are finitely generated $\mathcal O$-modules. One obtains them from the finite quotients $T/\varpi^mT$, but an inverse limit may carry a $\varprojlim^1$ correction unless the transition systems satisfy the required Mittag--Leffler condition.

For $V=T\otimes_{\mathcal O}E$, continuous cohomology is finite-dimensional over $E$, and in this setting

$$
H^i(G_{K,S},T)\otimes_{\mathcal O}E
\simeq H^i(G_{K,S},V)
$$

in the standard finite range. These assertions are not licenses to treat $T$, $V$, and $V/T$ as the same topological coefficient object. Their cochains and duals live in different categories.

## 4. Localization

### 4.1 Why a global class has local shadows

A global torsor can be inspected after scalar extension to every completion. This gives the most important map in Selmer theory:

$$
\operatorname{loc}_v:H^i(G_{K,S},M)\longrightarrow H^i(K_v,M).
$$

At a place in $S$, this is restriction to the chosen decomposition group. At a place outside $S$, it may be described either by inflating to $G_K$ and restricting to $G_{K_v}$, or by restricting along the homomorphism $G_{K_v}\to G_{K,S}$. Inertia lies in the kernel of the latter map.

Localization does not assert a local--global principle. Its kernel may be nonzero, and describing its cokernel requires global duality beyond the present book. At this stage the map is a testing device: a Selmer group consists of global classes whose shadows pass prescribed tests.

### 4.2 Construction and independence of choices

Choose a geometric place $\overline v$. The associated homomorphism $G_{K_v}\to G_{K,S}$ gives restriction on continuous cochains and hence $\operatorname{loc}_{\overline v}$. Replacing $\overline v$ by $g\overline v$ conjugates the homomorphism by $g$.

Conjugation induces the identity on cohomology after transporting coefficients by the action of $g$. Explicitly in degree one, if $z$ is a cocycle, the cocycle obtained from the conjugate embedding differs from the transported cocycle by a coboundary. Therefore the localization map is independent of the geometric choice up to the unique canonical conjugacy identification.

This is the correct invariance statement. There is usually no literal equality between maps whose targets were built from different embeddings. Once a representative $G_{K_v}$ and the canonical conjugacy transport are understood, it is harmless to write $\operatorname{loc}_v$.

### 4.3 Localization in low degrees

In degree zero, localization is the inclusion

$$
M^{G_K}\longrightarrow M^{G_{K_v}}.
$$

In degree one, a cocycle $z:G_{K,S}\to M$ is simply restricted to $G_{K_v}$. If the action is trivial, this sends a global character to its local character. In Kummer theory it sends a global square or $n$th-power class to the corresponding class in $K_v^\times/K_v^{\times n}$. In degree two it sends a global obstruction to the obstruction after completion.

Localization commutes with coefficient maps and connecting homomorphisms. Given a short exact sequence $0\to A\to B\to C\to0$, every square

$$
\begin{array}{ccc}
H^i(G_{K,S},C)&\xrightarrow{\delta}&H^{i+1}(G_{K,S},A)\\
\downarrow\operatorname{loc}_v&&\downarrow\operatorname{loc}_v\\
H^i(K_v,C)&\xrightarrow{\delta_v}&H^{i+1}(K_v,A)
\end{array}
$$

commutes. This formal fact is what allows Kummer images and deformation tangent conditions to assemble globally.

### 4.4 Products, sums, and restricted products

For a finite set $\Sigma$ of places there is no distinction between the direct product and direct sum as an abstract group:

$$
\prod_{v\in\Sigma}H^i(K_v,M)
=\bigoplus_{v\in\Sigma}H^i(K_v,M).
$$

We normally use a product when thinking of simultaneous localization and a direct sum when forming a quotient target in an exact sequence.

Over all places, the distinction is essential. For $H^1$ define the restricted product with respect to unramified subgroups by

$$
\prod_v' H^1(K_v,M)
=\left\{(x_v):x_v\in H^1(K_v,M),\qquad
x_v\in H^1_{\mathrm{ur}}(K_v,M)\text{ for almost all }v\right\}. \tag{4.1}
$$

For finite $M$, a global class localizes into (4.1). If $M$ factors through $G_{K,S}$, then it is unramified at every finite $v\notin S$, not merely almost every one. On passing to quotients by local conditions that equal the unramified subgroup almost everywhere, the natural target is the **direct sum**

$$
\bigoplus_v H^1(K_v,M)/\mathcal L_v, \tag{4.2}
$$

because a global class has only finitely many nonzero quotient components. Replacing (4.2) by an unrestricted product changes the object and is generally wrong.

For finite coefficients every local $H^1$ is given the discrete topology, and (4.1) carries the restricted-product topology in which $\prod_{v\notin T}H^1_{\mathrm{ur}}(K_v,M)$ is an open subgroup for every finite $T$. This topology matters when Pontryagin duality is later applied. The direct sum (4.2), by contrast, is being used here as an algebraic target with finite support.

### 4.5 The archimedean modification

For degree-one Selmer theory use ordinary $H^1(K_v,M)$ at every place; at a real place this already equals $\widehat H^1(K_v,M)$. When a basic exact sequence reaches degree zero or degree two and is intended to interface with global duality, adopt the uniform modified notation

$$
H^i_+(K_v,M)=
\begin{cases}
\widehat H^i(G_{\mathbf R},M),&v\text{ real},\\
0,&v\text{ complex},\\
H^i(K_v,M),&v\text{ finite}.
\end{cases}
$$

Thus the archimedean terms are Tate-modified in every degree. In this book all Selmer kernels use degree one, so the modified and ordinary real groups agree and no ambiguity remains. The notation $H^i_+$ appears only to mark where a later modified global sequence differs from an ordinary one.

## 5. Unramified classes and local conditions

### 5.1 The condition outside $S$

Let $v$ be finite and let $M$ be unramified at $v$. The **unramified local cohomology** is

$$
H^1_{\mathrm{ur}}(K_v,M)
=\ker\left(H^1(K_v,M)\longrightarrow H^1(I_v,M)\right). \tag{5.1}
$$

Inflation--restriction for

$$
1\to I_v\to G_{K_v}\to G_{k_v}\to1
$$

identifies it with

$$
H^1(G_{k_v},M)
\simeq M/(\operatorname{Frob}_v-1)M, \tag{5.2}
$$

where arithmetic Frobenius is used. The first equality in (5.2) should be read as inflation onto the subgroup (5.1). A class is unramified precisely when inertia sees no cocycle.

If $x\in H^1(G_{K,S},M)$ and $v\notin S$, then $G_{K_v}\to G_{K,S}$ kills $I_v$, so

$$
\operatorname{loc}_v(x)\in H^1_{\mathrm{ur}}(K_v,M). \tag{5.3}
$$

This proves the slogan that the conditions outside $S$ are built into $G_{K,S}$. It also shows why adding a separate quotient by $H^1_{\mathrm{ur}}$ at every $v\notin S$ contributes only zero to the localization map.

When $M$ is ramified at $v$, one may still define (5.1), and inflation--restriction gives

$$
H^1_{\mathrm{ur}}(K_v,M)
=\operatorname{im}\bigl(H^1(G_{k_v},M^{I_v})\to H^1(K_v,M)\bigr).
$$

The simple Frobenius quotient is then $M^{I_v}/(\operatorname{Frob}_v-1)M^{I_v}$, not $M/(\operatorname{Frob}_v-1)M$.

### 5.2 Why a local condition is a subgroup

Many arithmetic problems do not ask whether a local class is zero. They ask whether it comes from an integral point, remains unramified, has a prescribed ramification shape, or belongs to a deformation family. Each property cuts out a subset of $H^1(K_v,M)$. To be compatible with addition of torsors and with kernel constructions, that subset must be an additive subgroup.

A **local condition** on $M$ at $v$ is therefore a subgroup

$$
\mathcal L_v\subseteq H^1(K_v,M).
$$

If $M$ is a module over a ring $R$ and one wants an $R$-linear Selmer group, $\mathcal L_v$ is required to be an $R$-submodule. In particular, for a finite coefficient field $k$, it must be a $k$-vector subspace. This qualification matters: an additive subgroup of a vector space over $\mathbf F_{\ell^f}$ need only be $\mathbf F_\ell$-linear.

Before choosing $\mathcal L_v$, one should identify the local arithmetic question. The notation alone does not make an arbitrary subgroup natural, functorial, or exact in coefficients.

### 5.3 Unramified, relaxed, and strict conditions

Three conditions occur in nearly every Selmer argument:

$$
\begin{aligned}
\mathcal L_v^{\mathrm{ur}}&=H^1_{\mathrm{ur}}(K_v,M),\\
\mathcal L_v^{\mathrm{rel}}&=H^1(K_v,M),\\
\mathcal L_v^{\mathrm{str}}&=0.
\end{aligned} \tag{5.4}
$$

The relaxed condition imposes no test, because the quotient by it is zero. The strict condition requires the global class to vanish locally. The unramified condition permits the Frobenius direction but forbids inertia.

These names describe relative strength:

$$
0\subseteq H^1_{\mathrm{ur}}(K_v,M)\subseteq H^1(K_v,M).
$$

The middle inclusion can be either equality or strict. For example, if $v\nmid \ell$, $M$ is an unramified one-dimensional $\mathbf F_\ell$-module, and the Frobenius eigenvalue avoids both $1$ and $q_v$, then both the unramified group and the ramified direction may vanish. Conversely, for $M=\mu_\ell$ with $v\nmid\ell$ and $q_v\equiv1\pmod\ell$, Kummer theory exhibits distinct unit and valuation directions.

At a real place strict means zero and relaxed means all of $H^1(\mathbf R,M)$. There is no useful inertia definition there. At a complex place the two coincide because $H^1$ vanishes.

### 5.4 Kummer conditions

Suppose a short exact sequence of local objects gives a connecting map

$$
\delta_v:X(K_v)/nX(K_v)\longrightarrow H^1(K_v,M).
$$

The image is a **Kummer local condition**. Its form solves a descent problem: a cohomology class is allowed exactly when the corresponding torsor is obtained by dividing a genuine local point by $n$.

For $M=\mu_n$ and $X=\mathbf G_m$, Kummer theory gives an isomorphism

$$
K_v^\times/K_v^{\times n}\xrightarrow{\sim}H^1(K_v,\mu_n),
$$

so the full Kummer image is relaxed. More refined multiplicative conditions come from subgroups such as $\mathcal O_v^\times/\mathcal O_v^{\times n}$. At a finite place $v\nmid n$, the unit image is the unramified subgroup under the usual identification. At $v\mid n$, the unit image is generally larger than the unramified subgroup; calling it “unramified” there would erase the principal-unit contribution.

For an elliptic curve $E/K_v$ and $M=E[n]$, the connecting map

$$
E(K_v)/nE(K_v)\hookrightarrow H^1(K_v,E[n]) \tag{5.5}
$$

has a proper image in general. It is the defining local condition for the $n$-Selmer group.

### 5.5 Finite-flat-shaped conditions

At a place above the coefficient characteristic, an unramified condition is often too small and a relaxed condition too large. An integral model can single out classes extending across the valuation ring. Whenever an earlier finite-flat construction supplies a map from an integral cohomology group into $H^1(K_v,M)$, its image is a **finite-flat-shaped local condition**.

Concretely, if $M$ is the generic fiber of a finite flat commutative group model $\mathcal M/\mathcal O_v$, the available condition has the form

$$
H^1_{\mathrm{fl}}(K_v,M)
=\operatorname{im}\left(
H^1_{\mathrm{fppf}}(\mathcal O_v,\mathcal M)
\longrightarrow H^1(K_v,M)
\right). \tag{5.6}
$$

For $\mathcal M=\mu_n$, flat Kummer theory identifies (5.6) with the unit image $\mathcal O_v^\times/\mathcal O_v^{\times n}$, including at $v\mid n$ where the model is not étale. This example shows why the condition is integral rather than merely unramified.

The word “shaped” records the logical boundary. We use only what has already been justified: the existence of the relevant image subgroup and its stability under stated coefficient maps. We do not infer from the generic-fiber representation alone that such a subgroup exists canonically, nor that it is exact in every short exact sequence. Different integral models with the same generic fiber can impose different integral conditions.

This is an important counterexample to a tempting principle. Local conditions are not determined solely by the abstract vector space $H^1(K_v,M)$. They may remember an integral lattice, a group model, or a geometric lifting problem.

### 5.6 Changing and comparing local conditions

If $\mathcal L_v\subseteq\mathcal L'_v$, then the second condition is weaker. The quotient map

$$
H^1(K_v,M)/\mathcal L_v\twoheadrightarrow
H^1(K_v,M)/\mathcal L'_v
$$

measures the directions newly permitted. For a finite set $T$ of places where two systems differ, the local discrepancy is

$$
\bigoplus_{v\in T}\mathcal L'_v/\mathcal L_v.
$$

No global class need realize every element of this discrepancy. Selmer theory records the intersection of this local enlargement with the image of global localization. This observation leads to exact comparison sequences without invoking a global duality theorem.

## 6. Selmer structures and Selmer kernels

### 6.1 The assembly problem

We now have a finite global group and a family of local tests. The central construction should retain precisely those global classes whose localization belongs to every allowed subgroup. A kernel does exactly this and also exposes which exactness statements are formal.

There are two equivalent styles. One can work over all places, requiring the unramified condition almost everywhere, or choose a controlling finite set $S$ and regard the outside conditions as already enforced by $G_{K,S}$. The second is leaner in calculations; the first makes independence of $S$ visible.

### 6.2 Definition of a Selmer structure

Let $M$ be a finite $G_K$-module. A **Selmer structure** $\mathcal L$ on $M$ consists of local subgroups

$$
\mathcal L_v\subseteq H^1(K_v,M)
$$

for all places $v$, such that $\mathcal L_v=H^1_{\mathrm{ur}}(K_v,M)$ for all but finitely many finite $v$. At complex places the group is necessarily zero. At real places $\mathcal L_v$ is a subgroup of ordinary $H^1$, equivalently of $\widehat H^1$.

A **controlling set** for $(M,\mathcal L)$ is a finite set $S$ containing infinity, the coefficient-characteristic and ramified places of $M$, and every place at which $\mathcal L_v$ is not unramified. Then $M$ factors through $G_{K,S}$.

If coefficients are in a ring $R$, an $R$-linear Selmer structure requires every $\mathcal L_v$ to be an $R$-submodule. Without that phrase, the resulting group is only an abelian group.

### 6.3 The kernel and fiber-product formulations

For a controlling set $S$, define

$$
H^1_{\mathcal L}(K,M)
=\ker\left(
H^1(G_{K,S},M)\xrightarrow{\rho_{\mathcal L}}
\bigoplus_{v\in S}
H^1(K_v,M)/\mathcal L_v
\right). \tag{6.1}
$$

This is the **Selmer group** attached to $\mathcal L$. In all-places notation the same group is

$$
\ker\left(
H^1(K,M)\longrightarrow
\bigoplus_vH^1(K_v,M)/\mathcal L_v
\right), \tag{6.2}
$$

The map in (6.2) is well defined because both the module and every individual global cocycle are unramified almost everywhere. If $S$ is controlling, membership in this kernel forces the class to be unramified at every finite $v\notin S$. By the degree-one inflation statement (3.2) and the description of $N_S$ as the closed normal subgroup generated by those inertia groups, the class then inflates uniquely from $H^1(G_{K,S},M)$. This proves that (6.1) and (6.2) define the same group.

Equivalently, if

$$
\operatorname{loc}_S:H^1(G_{K,S},M)\to
\prod_{v\in S}H^1(K_v,M),
$$

then

$$
H^1_{\mathcal L}(K,M)
=H^1(G_{K,S},M)
\times_{\prod_{v\in S}H^1(K_v,M)}
\prod_{v\in S}\mathcal L_v. \tag{6.3}
$$

Formula (6.3) says that a Selmer group is an inverse image, not a quotient and not an intersection of unrelated ambient groups.

### 6.4 Built-in conditions outside $S$

Suppose $S\subseteq S'$ are both controlling sets and impose the unramified condition at every $v\in S'\setminus S$. Then inflation identifies

$$
H^1(G_{K,S},M)
\simeq
\left\{x\in H^1(G_{K,S'},M):
\operatorname{loc}_v(x)\in H^1_{\mathrm{ur}}(K_v,M)
\text{ for }v\in S'\setminus S\right\}. \tag{6.4}
$$

**Proof strategy.** Both sides are best compared inside $H^1(K,M)$. By (3.2), inflation identifies each restricted group with the global classes trivial on the corresponding ramification kernel. Passing from $S$ to $S'$ removes from that kernel the inertia groups at $S'\setminus S$. Requiring the new local classes to restrict trivially to those inertia groups restores exactly the old kernel. This proves (6.4).

Consequently (6.1) is independent of the controlling set. The phrase “outside $S$ is built in” is now an equality, not an informal convention.

### 6.5 Varying the local conditions

Let $\mathcal L_v\subseteq\mathcal L'_v$ for every $v$, with equality outside a finite set. Then there is an exact sequence

$$
0\longrightarrow H^1_{\mathcal L}(K,M)
\longrightarrow H^1_{\mathcal L'}(K,M)
\xrightarrow{\lambda}
\bigoplus_v\mathcal L'_v/\mathcal L_v. \tag{6.5}
$$

The map $\lambda$ localizes a class and reduces its components modulo the smaller conditions. Exactness is immediate: its kernel consists precisely of classes satisfying $\mathcal L$.

There is no formal surjectivity at the right of (6.5). Its cokernel is the failure of arbitrary allowed local directions to be simultaneously global. Appending a zero and calling (6.5) short exact would amount to asserting a local--global theorem that has not been proved.

As a useful special case, changing a place from strict to relaxed gives

$$
0\to H^1_{\mathrm{str}}(K,M)\to H^1_{\mathrm{rel}}(K,M)
\to H^1(K_v,M),
$$

with the other local conditions held fixed. The image is the localization of the relaxed Selmer group, which may be a proper subgroup of the ambient local cohomology.

### 6.6 Basic exact sequences from the definition

Write

$$
Q_{\mathcal L}(M)=\bigoplus_{v\in S}H^1(K_v,M)/\mathcal L_v.
$$

The definition gives the exact sequence

$$
0\longrightarrow H^1_{\mathcal L}(K,M)
\longrightarrow H^1(G_{K,S},M)
\xrightarrow{\rho_{\mathcal L}}Q_{\mathcal L}(M)
\longrightarrow \operatorname{coker}(\rho_{\mathcal L})
\longrightarrow0. \tag{6.6}
$$

This four-term sequence and the comparison sequence (6.5) are the basic global-to-local exact sequences available from definitions and ordinary cohomology. Connecting maps from coefficient sequences provide further exact fragments in Chapter 7.

Nothing here identifies $\operatorname{coker}(\rho_{\mathcal L})$ with the dual of another Selmer group. Nothing asserts that the sum of local invariants is the only obstruction. Those are global duality statements reserved for the next stage.

## 7. Morphisms and exact coefficient sequences

### 7.1 Compatibility is extra data

Let $f:M\to N$ be a homomorphism of $G_{K,S}$-modules. It induces global and local cohomology maps, but it induces a Selmer map only if

$$
f_{*,v}(\mathcal L_v^M)\subseteq\mathcal L_v^N
\qquad\text{for every }v. \tag{7.1}
$$

This condition is not automatic. A coefficient map can carry an unramified class to an unramified class, but an integral Kummer image need not map into a chosen integral condition unless the underlying geometric or integral maps are compatible. Likewise, an arbitrary choice of vector subspaces has no reason to be preserved.

The need for (7.1) is conceptual: a Selmer structure is part of the object. The pair $(M,\mathcal L)$, not the module $M$ alone, is functorial.

### 7.2 Functoriality of Selmer groups

Under (7.1), localization gives a commutative square

$$
\begin{array}{ccc}
H^1(G_{K,S},M)&\longrightarrow&Q_{\mathcal L^M}(M)\\
\downarrow f_*&&\downarrow \overline f_*\\
H^1(G_{K,S},N)&\longrightarrow&Q_{\mathcal L^N}(N).
\end{array}
$$

Taking kernels yields

$$
f_*:H^1_{\mathcal L^M}(K,M)\longrightarrow
H^1_{\mathcal L^N}(K,N). \tag{7.2}
$$

Composition and identity maps behave as expected. Thus modules equipped with compatible local conditions form a category in which the Selmer group is a covariant functor. It is not an exact functor in general.

### 7.3 Cartesian local conditions

Consider a short exact sequence

$$
0\longrightarrow A\xrightarrow{i}B\xrightarrow{j}C\longrightarrow0. \tag{7.3}
$$

Fix one finite controlling set for all three modules and all three systems of local conditions; every direct sum in this chapter is over that set.

Suppose local conditions are compatible with both maps. The condition on $A$ is **cartesian with respect to $i$ and $\mathcal L^B$** if

$$
\mathcal L_v^A=i_{*,v}^{-1}(\mathcal L_v^B) \tag{7.4}
$$

for every $v$. This equality is stronger than $i_*(\mathcal L_v^A)\subseteq\mathcal L_v^B$. It says that no class of $A$ becomes allowable only after being viewed in $B$.

At the other side one wants

$$
j_{*,v}(\mathcal L_v^B)
=\mathcal L_v^C\cap\operatorname{im}\bigl(H^1(K_v,B)\to H^1(K_v,C)\bigr). \tag{7.5}
$$

This is the exactness condition appropriate to local classes that actually lift to $B$. Requiring $j_*(\mathcal L_v^B)=\mathcal L_v^C$ is stronger and can fail merely because a local $C$-class has a nonzero boundary in $H^2(K_v,A)$.

### 7.4 The left-hand defect

Even before considering classes of $C$, exactness can fail at the middle Selmer group. Let

$$
P_v=i_{*,v}^{-1}(\mathcal L_v^B)\subseteq H^1(K_v,A).
$$

If $b\in H^1_{\mathcal L^B}(K,B)$ maps to zero in $H^1(K,C)$, choose $a\in H^1(G_{K,S},A)$ mapping to $b$. Its localizations lie in $P_v$, but need not lie in $\mathcal L_v^A$. The tuple

$$
\bigl(\operatorname{loc}_v(a)\bmod\mathcal L_v^A\bigr)_v
\in\bigoplus_vP_v/\mathcal L_v^A \tag{7.6}
$$

is the **left-hand local defect**.

Changing $a$ by the global connecting image of $c\in H^0(G_{K,S},C)$ changes (7.6) by the localization of $\delta(c)$. Hence the defect is well defined modulo those diagonal connecting classes. Its vanishing means that a preimage can be chosen in $H^1_{\mathcal L^A}(K,A)$. In particular, the cartesian equality (7.4) kills the local defect.

There is also a degree-zero qualification. A global invariant $c\in H^0(C)$ maps by $\delta$ into the $A$-Selmer group only when every $\delta_v(c)$ lies in $\mathcal L_v^A$. Define

$$
H^0_{\mathcal L}(K,C;A)
=\{c\in H^0(K,C):\delta_v(c)\in\mathcal L_v^A\text{ for all }v\}. \tag{7.7}
$$

Then the sequence begins honestly as

$$
H^0(K,B)\to H^0_{\mathcal L}(K,C;A)
\xrightarrow{\delta}H^1_{\mathcal L^A}(K,A).
$$

### 7.5 The lifting defect

Now let $c\in H^1_{\mathcal L^C}(K,C)$. The first obstruction to lifting $c$ globally is its connecting class

$$
\delta(c)\in H^2(G_{K,S},A). \tag{7.8}
$$

If (7.8) is nonzero, no global $B$-lift exists. Suppose it vanishes and choose such a lift $b\in H^1(G_{K,S},B)$. At every $v$, $j_*(\operatorname{loc}_v b)=\operatorname{loc}_v c\in\mathcal L_v^C$, but $\operatorname{loc}_v b$ need not lie in $\mathcal L_v^B$.

The tuple of classes

$$
(\operatorname{loc}_v b\bmod\mathcal L_v^B)_v
$$

lies in

$$
\bigoplus_v j_{*,v}^{-1}(\mathcal L_v^C)/\mathcal L_v^B. \tag{7.9}
$$

Changing the global lift $b$ by the image of $a\in H^1(G_{K,S},A)$ changes (7.9) by the diagonal localization of $i_*(a)$. Thus (7.9), modulo that global image, is a well-defined **lifting defect**. It vanishes exactly when some global lift satisfies every $B$-local condition.

This two-stage description is the safe general replacement for a nonexistent automatic long exact sequence of Selmer groups: first test the global $H^2$ boundary, then test whether a global lift can be adjusted into all local subgroups simultaneously.

### 7.6 A usable exactness criterion

Under explicit hypotheses the familiar exact fragment does hold. Assume:

1. every global invariant of $C$ has local boundary in $\mathcal L^A$;
2. the local conditions are cartesian as in (7.4);
3. for every $c\in H^1_{\mathcal L^C}(K,C)$ with $\delta(c)=0$, the lifting defect (7.9) vanishes.

Then ordinary cohomology and the preceding diagram chases give

$$
H^0(K,B)\to H^0(K,C)\xrightarrow{\delta}
H^1_{\mathcal L^A}(K,A)\to
H^1_{\mathcal L^B}(K,B)\to
H^1_{\mathcal L^C}(K,C)\xrightarrow{\delta}H^2(G_{K,S},A), \tag{7.10}
$$

exact through $H^1_{\mathcal L^C}(K,C)$. The final arrow lands in $H^2(G_{K,S},A)$ and records the remaining global lifting obstruction; no surjectivity onto $H^2$ is asserted. A convenient sufficient form of condition 3 is exactness of the relevant global-to-local lifting square; it must be proved in the application.

**Worked warning.** Give $A$ the strict condition and $B$ the relaxed condition at one place, even when $i_*$ is injective on local $H^1$. Then $P_v$ in (7.6) can be all of $H^1(K_v,A)$ while $\mathcal L_v^A=0$. A $B$-Selmer class lying globally in the image of $A$ need not come from the strict $A$-Selmer group. Thus exactness fails for a reason visible before any global duality enters.

## 8. Changing the number field

### 8.1 Restriction and places above places

Let $L/K$ be finite. Choose $S$ large enough to contain infinity, the coefficient-characteristic and ramified places of $M$, and every finite place ramified in $L/K$. Let $S_L$ be the places of $L$ above $S$. Then $L\subseteq K_S$, and

$$
G_{L,S_L}=\operatorname{Gal}(K_S/L)
$$

is an open subgroup of $G_{K,S}$ after choosing a common maximal extension. Restriction gives

$$
\operatorname{res}_{L/K}:H^i(G_{K,S},M)\to H^i(G_{L,S_L},M). \tag{8.1}
$$

Locally, one global place $v$ splits into all $w\mid v$. Compatibility of decomposition groups gives a commutative square with the bottom map

$$
H^i(K_v,M)\longrightarrow\prod_{w\mid v}H^i(L_w,M),
\qquad x\longmapsto(\operatorname{res}_{L_w/K_v}x)_w. \tag{8.2}
$$

The product in (8.2) is finite. Omitting all but one $w$ destroys the field-independent content of restriction.

If $L/K$ is ramified outside a previously selected $S$, enlarge $S$ first. Otherwise $L$ need not lie in $K_S$ and the open-subgroup description is invalid, though absolute-Galois restriction still exists.

### 8.2 Corestriction and summation

For finite $L/K$, corestriction runs in the opposite direction:

$$
\operatorname{cor}_{L/K}:H^i(G_{L,S_L},M)\to H^i(G_{K,S},M). \tag{8.3}
$$

On local components above $v$, compatibility takes the form

$$
(x_w)_{w\mid v}\longmapsto
\sum_{w\mid v}\operatorname{cor}_{L_w/K_v}(x_w). \tag{8.4}
$$

The sum is essential. Corestriction is additive transfer, and all primes above $v$ contribute. For Kummer classes (8.4) corresponds to the product of local norms under multiplicative notation.

Restriction followed by corestriction satisfies

$$
\operatorname{cor}_{L/K}\circ\operatorname{res}_{L/K}
=[L:K]
$$

on cohomology. If $L/K$ is Galois, the reverse composite is the sum of the conjugate actions. These formulas provide immediate consistency checks for induced local conditions.

### 8.3 Induced local conditions

Given a Selmer structure $\mathcal L$ over $K$, at a place $w$ above an exceptional place $v$ the most direct restricted condition is

$$
\mathcal L^{\operatorname{res}}_w
=\operatorname{im}\bigl(\mathcal L_v\to H^1(L_w,M)\bigr)
\qquad(w\mid v). \tag{8.5}
$$

At all but finitely many places one takes the full unramified subgroup over $L_w$, which contains the restriction of the unramified subgroup over $K_v$. Taking the literal image in (8.5) at every unramified place need not give the full unramified subgroup and can differ from it infinitely often; it would then fail the almost-everywhere condition in our definition of a Selmer structure. One may instead take the subgroup generated by the image together with additional geometrically allowed classes at the exceptional places. The choice changes the Selmer problem and must be named.

For corestriction, conditions $\mathcal M_w$ over $L$ are compatible with $\mathcal L_v$ over $K$ if

$$
\sum_{w\mid v}\operatorname{cor}_{L_w/K_v}(\mathcal M_w)
\subseteq\mathcal L_v. \tag{8.6}
$$

Then restriction or corestriction carries Selmer groups in the expected direction. Unramified conditions satisfy these compatibilities at unramified places. Kummer conditions do so when restriction of points and norm or trace maps on the underlying objects supply the required maps.

### 8.4 Shapiro and decomposition over places

Let $N$ be a finite $G_L$-module and put

$$
\operatorname{Ind}_{G_L}^{G_K}N
=\{f:G_K\to N:f(hg)=h f(g)\}.
$$

Shapiro's lemma gives

$$
H^i(K,\operatorname{Ind}_{G_L}^{G_K}N)
\simeq H^i(L,N). \tag{8.7}
$$

At a place $v$ of $K$, restriction of the induced module decomposes according to the places above $v$:

$$
\left.\operatorname{Ind}_{G_L}^{G_K}N\right|_{G_{K_v}}
\simeq\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{L_w}}^{G_{K_v}}N_w. \tag{8.8}
$$

Here compatible geometric places and double-coset representatives identify the relevant conjugate of $G_{L_w}$ with a subgroup of $G_{K_v}$, and $N_w$ denotes $N$ transported by that representative. Changing the representatives changes (8.8) only by the canonical conjugacy identifications already used for localization.

Applying local Shapiro turns (8.8) into

$$
H^i(K_v,\operatorname{Ind}_{L}^{K}N)
\simeq\bigoplus_{w\mid v}H^i(L_w,N_w). \tag{8.9}
$$

Thus a family of local conditions $\mathcal M_w$ on the transported local modules $N_w$ induces the direct-sum condition $\bigoplus_{w\mid v}\mathcal M_w$ on the left of (8.9). Global and local Shapiro then identify the corresponding Selmer groups. This is the precise reason that induction converts change of field into change of coefficients without losing the decomposition over places.

### 8.5 Restriction--corestriction checks

Two cautions keep field change honest. First, an image condition such as (8.5) may be smaller than the natural condition independently defined over $L_w$. For example, not every local point over $L_w$ descends from a point over $K_v$. Second, a strict condition is preserved by restriction, but a restricted class may become zero even if the original class was nonzero; restriction need not inject on a Selmer group.

As a worked check, take trivial $M=\mathbf Z/n\mathbf Z$. A global character $\chi$ restricts to $G_L$, and its local components are the restrictions at every $w$. Corestricting the restricted character multiplies it by $[L:K]$. If $n$ divides $[L:K]$, this composite can vanish even for nonzero $\chi$. Field extension may therefore kill classes for purely cohomological reasons, not because local conditions were mischosen.

## 9. Dual Selmer structures

### 9.1 Local duality turns permission into annihilation

A local condition describes permitted classes. Tate local duality converts it into the classes on the dual module that detect none of those permitted directions. This is the correct notion of a dual local condition.

Let $M$ be finite, killed by $n$, and assume the local duality hypotheses: at nonarchimedean places $n$ is prime to the characteristic of the local field, automatic for number fields, and at real places use the finite Tate pairing. Put

$$
M^*(1)=\operatorname{Hom}(M,\mu_n).
$$

For finite $v$, Book 31 supplies a perfect pairing

$$
\langle\ ,\ \rangle_v:
H^1(K_v,M)\times H^1(K_v,M^*(1))
\longrightarrow\mathbf Q/\mathbf Z. \tag{9.1}
$$

At a real place the analogous pairing uses Tate cohomology of $C_2$; in degree one this has the same underlying group as ordinary $H^1$. Complex places contribute zero.

### 9.2 Finite coefficients and exact orthogonals

For a subgroup $\mathcal L_v\subseteq H^1(K_v,M)$ define

$$
\mathcal L_v^\perp
=\{y\in H^1(K_v,M^*(1)):
\langle x,y\rangle_v=0\text{ for every }x\in\mathcal L_v\}. \tag{9.2}
$$

Perfectness implies the exact identities

$$
|\mathcal L_v|\,|\mathcal L_v^\perp|
=|H^1(K_v,M)|,
\qquad
(\mathcal L_v^\perp)^\perp=\mathcal L_v. \tag{9.3}
$$

For vector spaces over a finite field, after using the trace to the prime field if necessary, orthogonals are vector subspaces and dimensions add to the ambient dimension. The subgroup definition (9.2), rather than a guessed dimension, determines the dual condition.

### 9.3 The dual Selmer structure

Given a Selmer structure $\mathcal L$ on $M$, its **dual Selmer structure** $\mathcal L^\perp$ on $M^*(1)$ is the family of exact local orthogonals (9.2). The dual Selmer group is

$$
H^1_{\mathcal L^\perp}(K,M^*(1))
=\ker\left(
H^1(G_{K,S},M^*(1))\to
\bigoplus_{v\in S}
H^1(K_v,M^*(1))/\mathcal L_v^\perp
\right). \tag{9.4}
$$

Choose $S$ to control both $M$ and its Tate dual. Away from $S$, where the residue characteristic does not divide $n$ and both modules are unramified, the unramified subgroups are exact orthogonal complements. Hence $\mathcal L^\perp$ is again unramified almost everywhere and is a genuine Selmer structure.

At coefficient-characteristic places, the unramified subgroup need not be its own complementary condition. This is one reason those places lie in $S$ and their conditions are specified individually.

### 9.4 Natural pairs of conditions

Perfectness immediately gives

$$
(0)^\perp=H^1(K_v,M^*(1)),
\qquad
H^1(K_v,M)^\perp=0. \tag{9.5}
$$

Thus strict and relaxed conditions exchange. Away from the residue characteristic, unramified conditions on unramified dual modules exchange with unramified conditions. Kummer images for dual isogenies are orthogonal when the local connecting maps and the relevant geometric pairing satisfy the compatibility proved by local duality. Integral finite-flat-shaped conditions have the expected orthogonal only when the integral dual models establish it; generic-fiber duality alone is insufficient.

Restriction and corestriction are adjoint:

$$
\langle\operatorname{res}x,y\rangle_w
=\langle x,\operatorname{cor}y\rangle_v.
$$

Consequently a restriction-induced condition is orthogonal to the appropriate corestriction-kernel condition. This relation is often more useful than trying to identify the two groups by dimension.

### 9.5 What local duality does not prove globally

The construction of (9.4) is entirely local. It does **not** prove a perfect pairing

$$
H^1_{\mathcal L}(K,M)\times
H^1_{\mathcal L^\perp}(K,M^*(1))\to\mathbf Q/\mathbf Z.
$$

Indeed there is no evident sum of local pairings on two global classes: every summand vanishes because each localization lies in an orthogonal pair, and obtaining a meaningful global exact sequence requires a subtler compact-support construction. Nor does local perfectness imply equality of the two Selmer orders or any numerical difference formula.

Identifying global-to-local cokernels or deriving any numerical comparison between the two global kernels requires the global duality theory of the next book. Here we have constructed the two kernels and proved only that their local conditions are exact orthogonals. That is precisely the input the later global theorem will relate.

## 10. Kummer theory, units, and class groups

### 10.1 Restricted ramification in Kummer coordinates

Kummer theory turns the abstract ramification restriction into valuations. Since a number field has characteristic zero, the sequence

$$
1\longrightarrow\mu_n\longrightarrow\overline K^\times
\xrightarrow{(\cdot)^n}\overline K^\times\longrightarrow1
$$

is exact for every $n\geq1$. Hilbert's theorem 90 gives

$$
H^1(K,\mu_n)\simeq K^\times/K^{\times n}. \tag{10.1}
$$

No assumption $\mu_n\subset K$ is needed for (10.1); that assumption is needed only when replacing $\mu_n$ by the constant module $\mathbf Z/n\mathbf Z$.

Let $S$ contain infinity and every place dividing $n$. A Kummer class represented by $a\in K^\times$ is unramified at a finite $v\notin S$ exactly when

$$
v(a)\equiv0\pmod n. \tag{10.2}
$$

Indeed write $a=\pi_v^r u$. Since $n$ is prime to the residue characteristic, the class of the unit $u$ lies in the unramified Kummer direction, while $r\bmod n$ measures the tame inertia contribution. Thus

$$
H^1(G_{K,S},\mu_n)
\simeq
\frac{\{a\in K^\times:v(a)\in n\mathbf Z\text{ for every finite }v\notin S\}}
{K^{\times n}}. \tag{10.3}
$$

Formula (10.3) is a worked translation of the definition of $G_{K,S}$. It also shows why places above $n$ are exceptional: there the unit filtration contains ramified $n$-power information, so the simple prime-to-residue-characteristic argument is unavailable.

### 10.2 $S$-units and the $S$-class group

Let $S_f$ be the finite places in $S$. The ring of $S$-integers and its units are

$$
\mathcal O_{K,S}=\{a\in K:v(a)\geq0\text{ for }v\notin S_f\},
\qquad
\mathcal O_{K,S}^\times=\{a\in K^\times:v(a)=0\text{ for }v\notin S_f\}.
$$

Its ideal class group is denoted $\operatorname{Cl}(\mathcal O_{K,S})$. Sending a class in (10.3) to the ideal

$$
\mathfrak a=\prod_{v\notin S_f}\mathfrak p_v^{v(a)/n}
$$

gives a well-defined $n$-torsion ideal class, because

$$
(a)=\mathfrak a^n\cdot\prod_{v\in S_f}\mathfrak p_v^{v(a)}.
$$

The kernel consists of $S$-unit classes. One obtains the fundamental exact sequence

$$
0\longrightarrow
\mathcal O_{K,S}^\times/(\mathcal O_{K,S}^\times)^n
\longrightarrow H^1(G_{K,S},\mu_n)
\longrightarrow\operatorname{Cl}(\mathcal O_{K,S})[n]
\longrightarrow0. \tag{10.4}
$$

To see surjectivity, represent an $n$-torsion $S$-ideal class by $\mathfrak a$. Then $\mathfrak a^n=(a)$ in the group of ideals away from $S$, and $a$ supplies the desired Kummer class. Changing $\mathfrak a$ by a principal $S$-ideal changes $a$ by an $S$-unit times an $n$th power, exactly the kernel in (10.4).

Sequence (10.4) proves finiteness in this example: Dirichlet's theorem makes the first term finite modulo $n$, and the $S$-class group is finite.

### 10.3 The multiplicative Selmer structure

There are two related ways to read (10.4). If ramification is relaxed at the places of $S_f$, then all of $H^1(G_{K,S},\mu_n)$ is the multiplicative $S$-Selmer group, and (10.4) records $S$-units and the $S$-class group.

Alternatively, choose a larger controlling set but impose at every finite $v$ the image

$$
\mathcal L_v^{\mathrm{unit}}
=\operatorname{im}\left(\mathcal O_v^\times/\mathcal O_v^{\times n}
\to K_v^\times/K_v^{\times n}\right). \tag{10.5}
$$

At the selected places one may relax (10.5), allowing arbitrary valuation, to recover $S$-units. At places outside $S$, (10.5) agrees with the unramified condition because $v\nmid n$. The Selmer kernel says exactly that all forbidden valuations are divisible by $n$.

When no finite place is relaxed, the same argument gives

$$
0\to\mathcal O_K^\times/(\mathcal O_K^\times)^n
\to H^1_{\mathcal L^{\mathrm{unit}}}(K,\mu_n)
\to\operatorname{Cl}(K)[n]\to0. \tag{10.6}
$$

Thus the class group does not equal the multiplicative Selmer group; it is its quotient by global units. Forgetting the unit term is a basic but serious error.

### 10.4 Ordinary and narrow phenomena at real places

For odd $n$, $H^1(\mathbf R,\mu_n)=0$. For even $n$, signs survive. Under

$$
H^1(\mathbf R,\mu_n)\simeq\mathbf R^\times/\mathbf R^{\times n},
$$

the group has order two and is detected by the sign. Taking the relaxed real condition permits negative representatives; taking the strict real condition requires the global Kummer class to be a local $n$th power and hence positive at that embedding.

Consequently strict conditions at all real places lead to narrow variants of (10.4) and (10.6). The kernel uses totally positive units, and the quotient is controlled by a narrow $S$-class group. These groups need not agree with their ordinary counterparts. A real quadratic field with no unit of norm $-1$ supplies the standard counterexample: sign patterns cannot all be corrected by global units, and the narrow class group is larger.

This example explains both archimedean conventions. Including real places in $S$ permits complexification; choosing relaxed or strict local $H^1$ then decides whether it is allowed in the Selmer problem.

### 10.5 A calculation over $\mathbf Q$

Let $n=2$ and let $S_f$ be a finite set of rational primes containing $2$. Since $\mathbf Z[S_f^{-1}]$ has trivial class group, (10.4) gives

$$
H^1(G_{\mathbf Q,S},\mu_2)
\simeq \mathbf Z[S_f^{-1}]^\times/
\mathbf Z[S_f^{-1}]^{\times2}.
$$

The unit group is generated by $-1$ and the primes in $S_f$, so the square classes of

$$
-1\quad\text{and}\quad p\in S_f
$$

form an $\mathbf F_2$-basis. Thus the dimension is $1+|S_f|$. With $S_f=\{2\}$ this recovers the four classes $1,-1,2,-2$ from Section 2.5.

Imposing the strict real condition removes the negative square classes and lowers the dimension by one. Imposing the strict condition also at $2$ is more restrictive than requiring even $2$-adic valuation: the unit classes in $\mathbf Q_2^\times/\mathbf Q_2^{\times2}$ must vanish too. This distinguishes strict, unit, and unramified conditions in a concrete setting.

## 11. Elliptic curves and character groups

### 11.1 The $n$-Selmer group of an elliptic curve

Let $E/K$ be an elliptic curve and $n\geq1$. The multiplication sequence

$$
0\longrightarrow E[n]\longrightarrow E(\overline K)
\xrightarrow{[n]}E(\overline K)\longrightarrow0
$$

gives global and local Kummer maps

$$
\delta:E(K)/nE(K)\hookrightarrow H^1(K,E[n]),
$$

$$
\delta_v:E(K_v)/nE(K_v)\hookrightarrow H^1(K_v,E[n]).
$$

Define

$$
\mathcal L_v^E=\operatorname{im}(\delta_v).
$$

The **$n$-Selmer group** is

$$
\operatorname{Sel}_n(E/K)
=H^1_{\mathcal L^E}(K,E[n]). \tag{11.1}
$$

A controlling set contains infinity, the places dividing $n$, and the places of bad reduction. Outside it, $E[n]$ is unramified and the Kummer image agrees with the unramified subgroup. Hence (11.1) may be computed from $H^1(G_{K,S},E[n])$ using only finitely many explicit quotient conditions.

### 11.2 Why the local Kummer image is the right condition

A class in $H^1(K,E[n])$ represents a choice of local $n$-division data with a Galois twisting. Its image in $H^1(K,E)$ is the associated principal homogeneous space under $E$. From the local long exact sequence,

$$
\operatorname{im}(\delta_v)
=\ker\bigl(H^1(K_v,E[n])\to H^1(K_v,E)[n]\bigr). \tag{11.2}
$$

Thus the Kummer condition says that the local $E[n]$-class produces the trivial local $E$-torsor. This is stronger than being unramified at bad or coefficient-characteristic places and weaker than vanishing as an $E[n]$-class.

At a complex place both groups vanish in degree one. At a real place the component group of $E(\mathbf R)$ can contribute $2$-torsion when $n$ is even. Dropping the real condition can therefore change a $2$-Selmer group.

### 11.3 The basic Mordell--Weil exact sequence

Global Kummer theory and (11.2) give an exact sequence using only ordinary cohomology:

$$
0\longrightarrow E(K)/nE(K)
\longrightarrow\operatorname{Sel}_n(E/K)
\longrightarrow\Sha(E/K)[n]
\longrightarrow0, \tag{11.3}
$$

where

$$
\Sha(E/K)=\ker\left(H^1(K,E)\to\prod_vH^1(K_v,E)\right).
$$

**Proof strategy.** Map a Selmer class in $H^1(K,E[n])$ to $H^1(K,E)[n]$. By its defining local Kummer conditions, the image vanishes in every $H^1(K_v,E)$, hence lies in $\Sha(E/K)[n]$. The kernel is the global Kummer image $E(K)/nE(K)$. Conversely, an $n$-torsion class in $\Sha$ lifts through the global Kummer long exact sequence and every such lift satisfies the local Kummer condition by (11.2). This proves exactness and surjectivity.

The finiteness of $H^1(G_{K,S},E[n])$ proves that $\operatorname{Sel}_n(E/K)$ is finite. Sequence (11.3) then shows that $E(K)/nE(K)$ and $\Sha(E/K)[n]$ are finite. It does not prove that the whole Tate--Shafarevich group is finite.

### 11.4 Unramified character groups

For the trivial module $M=\mathbf Z/n\mathbf Z$,

$$
H^1(G_{K,S},M)
=\operatorname{Hom}_{\mathrm{cont}}(G_{K,S},\mathbf Z/n\mathbf Z). \tag{11.4}
$$

It is the group of cyclic characters of exponent dividing $n$ unramified outside $S$. If the strict condition is imposed at a place $v$, the character is trivial on the entire decomposition group there, so $v$ splits completely in the corresponding cyclic extension. If only the unramified condition is imposed, inertia is trivial but Frobenius may remain nontrivial.

With $S$ consisting only of archimedean places and with strict conditions at real places, global class field theory identifies (11.4) with the $n$-torsion character group of the ordinary ideal class group. Relaxing real places instead sees the narrow version. Thus unramified character Selmer groups are dual in the elementary character-group sense to class-group quotients, even before any general global cohomological duality theorem is invoked.

### 11.5 Strict and relaxed auxiliary primes

Let $T$ be a finite set disjoint from a controlling set $S$. Enlarge to $S\cup T$. At $v\in T$ one may keep the unramified condition, relax it, or make it strict. The comparison sequence (6.5) shows exactly what changes:

$$
0\to H^1_{\mathrm{ur}}(K,M)
\to H^1_{\mathrm{rel},T}(K,M)
\to\bigoplus_{v\in T}H^1(K_v,M)/H^1_{\mathrm{ur}}(K_v,M). \tag{11.5}
$$

The last map need not be onto. Replacing relaxed by strict gives a map from the relaxed Selmer group into $\bigoplus_{v\in T}H^1(K_v,M)$ whose kernel is the strict group.

This simple maneuver is the algebraic prototype of auxiliary-prime arguments: relaxation permits new local ramified directions, while strictness forces a localization to disappear. Any claim about how many dimensions change requires information about the localization image, and later global duality is what makes such numerical comparisons systematic.

## 12. Limits and topological coefficients

### 12.1 Why finite-level notation cannot simply be reused

Finite modules are discrete, their local cohomology groups are finite, and every subgroup is closed. None of these facts survives unchanged for an $\ell$-adic lattice, a discrete divisible module, or a vector space over a local field. The symbols $H^1$ and $\ker$ remain meaningful, but topology determines which cochains, limits, duals, and quotient groups are intended.

The safe principle is to define each infinite-level object in its own coefficient category and only then compare it with finite levels. An equality such as

$$
H^1(K,T)=\varprojlim_m H^1(K,T/\varpi^mT)
$$

is a theorem under hypotheses, not the definition in every context.

### 12.2 Lattices

Let $T$ be a finite free $\mathcal O$-module with its $\varpi$-adic topology and continuous $G_{K,S}$-action. Define $H^1(G_{K,S},T)$ using continuous cochains with topological coefficients, or equivalently by a derived inverse-limit construction that retains any $\varprojlim^1$ term. If the transition maps on invariants satisfy the Mittag--Leffler condition, the expected comparison with finite quotients holds.

A lattice local condition is a **closed** $\mathcal O$-submodule

$$
\mathcal L_v(T)\subseteq H^1(K_v,T).
$$

The corresponding Selmer group is the kernel of the continuous map to the finite product of topological quotients. It is closed in $H^1(G_{K,S},T)$ and, under the standard finiteness hypotheses, finitely generated over $\mathcal O$.

Suppose conditions $\mathcal L_v(T/\varpi^mT)$ are compatible under reduction and cartesian:

$$
\mathcal L_v(T/\varpi^mT)
=\text{inverse image of }\mathcal L_v(T/\varpi^{m-1}T).
$$

Then, subject to the same inverse-limit exactness hypotheses,

$$
H^1_{\mathcal L}(K,T)
\simeq\varprojlim_m H^1_{\mathcal L_m}(K,T/\varpi^mT). \tag{12.1}
$$

Without cartesianness or Mittag--Leffler control, kernels need not commute with the inverse limit in the asserted form.

### 12.3 Discrete torsion modules

Put $V=T\otimes_{\mathcal O}E$ and $A=V/T$. The module $A$ is discrete and $\varpi$-primary, with

$$
A=\varinjlim_m A[\varpi^m].
$$

Continuous cohomology with discrete coefficients commutes with this filtered union:

$$
H^i(G_{K,S},A)
\simeq\varinjlim_mH^i(G_{K,S},A[\varpi^m]). \tag{12.2}
$$

A torsion local condition $\mathcal L_v(A)$ is usually the union or image of compatible finite-level conditions. To conclude that the Selmer kernel is the direct limit of finite Selmer groups, one must check that the local quotient maps and their kernels commute with the filtered colimit. Filtered colimits of abelian groups are exact, so this works for genuinely compatible image conditions; it can fail if an independently defined infinite-level condition is larger than the union.

The resulting Selmer group is typically a discrete cofinitely generated $\mathcal O$-module, not a finite group. Its Pontryagin dual is compact. Statements about its corank belong to this topological category.

### 12.4 Vector-space coefficients

For $V=T\otimes E$, define a local condition as an $E$-subspace

$$
\mathcal L_v(V)\subseteq H^1(K_v,V).
$$

Often it is obtained by tensoring a saturated lattice condition:

$$
\mathcal L_v(V)=\mathcal L_v(T)\otimes_{\mathcal O}E.
$$

Then, under finite generation and compatibility,

$$
H^1_{\mathcal L}(K,V)
\simeq H^1_{\mathcal L}(K,T)\otimes_{\mathcal O}E. \tag{12.3}
$$

If the lattice condition is not saturated, tensoring forgets finite-index information. Different lattices can therefore yield the same vector-space Selmer group but different integral Selmer groups.

Every $H^1(K_v,V)$ in the relevant number-field setting is finite-dimensional over $E$, and the global Selmer group is finite-dimensional. It carries its natural finite-dimensional topology. This is the coefficient regime used for characteristic-zero deformation tangent calculations; residual tangent spaces instead use a finite field.

### 12.5 Infinite-level local conditions and duality

For a lattice $T$, its natural local Tate partner is the discrete module

$$
D(T)=\operatorname{Hom}_{\mathrm{cont}}(T,\mathbf Q_\ell/\mathbf Z_\ell)(1),
$$

up to the chosen coefficient-ring trace convention. Local pairings identify compact and discrete cohomology groups by Pontryagin duality. If $\mathcal L_v(T)$ is closed, its annihilator in $H^1(K_v,D(T))$ is exact; taking an algebraic orthogonal without closure can give the wrong bidual.

For $V$, the partner is $V^*(1)$ and the pairing is $E$-bilinear after applying the local invariant and coefficient trace. Orthogonals of $E$-subspaces are again $E$-subspaces. These finite-dimensional dual conditions agree with the rationalizations of integral orthogonals only when the chosen lattices and local conditions are compatible.

As at finite level, these are local statements. Pontryagin duality at every place does not by itself produce a global perfect pairing of infinite-level Selmer groups.

## 13. Adjoint Selmer groups and deformation tangents

### 13.1 The global tangent cocycle

Let $k$ be a finite field of characteristic $\ell$, and let

$$
\overline\rho:G_{K,S}\longrightarrow\operatorname{GL}(W)
$$

be a continuous representation on a finite-dimensional $k$-space. Consider a first-order lift to $k[\varepsilon]/(\varepsilon^2)$. After choosing the underlying module, it can be written

$$
\rho_\varepsilon(g)=\bigl(1+\varepsilon c(g)\bigr)\overline\rho(g).
$$

The homomorphism condition is equivalent to

$$
c(gh)=c(g)+\overline\rho(g)c(h)\overline\rho(g)^{-1}.
$$

Thus $c$ is a cocycle with values in

$$
\operatorname{ad}(\overline\rho)=\operatorname{End}_k(W),
$$

where $G_{K,S}$ acts by conjugation. Changing the lift by an infinitesimal conjugation changes $c$ by a coboundary. Unrestricted first-order deformation classes are therefore modeled by

$$
H^1(G_{K,S},\operatorname{ad}(\overline\rho)). \tag{13.1}
$$

The word “modeled” is deliberate: representability, automorphisms, and obstruction theory require their own hypotheses. The cocycle calculation itself is elementary and exact.

### 13.2 Local deformation conditions as subspaces

A global deformation problem rarely permits every local first-order lift. At each $v\in S$, a local condition—unramified, fixed inertial type, ordinary, finite-flat-shaped, or another already constructed lifting condition—has a tangent image

$$
\mathcal L_v\subseteq
H^1(K_v,\operatorname{ad}(\overline\rho)). \tag{13.2}
$$

If the local deformation condition is stable under the $k$-linear first-order operations, $\mathcal L_v$ is a $k$-subspace. This linearity must be proved from the local problem; a set of allowable lifts need not have a linear tangent image without suitable deformation-functor axioms.

Outside $S$, requiring the deformation to remain unramified gives $H^1_{\mathrm{ur}}$. Thus all local tangent requirements form a Selmer structure on the adjoint module.

### 13.3 The tangent space is a Selmer group

A global first-order class $[c]$ satisfies the specified local deformation problems exactly when

$$
\operatorname{loc}_v[c]\in\mathcal L_v
\qquad(v\in S).
$$

Consequently the global tangent space is

$$
H^1_{\mathcal L}
\bigl(K,\operatorname{ad}(\overline\rho)\bigr). \tag{13.3}
$$

This identification is the endpoint of the global Selmer framework. It explains why local deformation theory produces subspaces, why restricted ramification produces $G_{K,S}$, and why a kernel rather than a direct sum assembles the global problem.

For framed deformations one does not quotient by all infinitesimal conjugations at the framed places, so the tangent space acquires additional local coboundary directions. Those directions must be added according to the framing convention; they are not hidden inside the unframed Selmer group (13.3).

### 13.4 Fixed determinant and the trace-zero adjoint

The differential of determinant is trace. If the determinant is fixed, the cocycle takes values in

$$
\operatorname{ad}^0(\overline\rho)
=\{X\in\operatorname{End}_k(W):\operatorname{tr}X=0\}. \tag{13.4}
$$

When the characteristic of $k$ divides $\dim W$, scalar endomorphisms may lie in $\operatorname{ad}^0$, so trace zero is not the same as quotienting out scalars. The local fixed-determinant tangent spaces must be subspaces of $H^1(K_v,\operatorname{ad}^0)$, and the global fixed-determinant tangent space is their Selmer group.

If a short exact sequence relating scalar, adjoint, and trace-zero modules is used, Chapter 7 applies: local conditions must be checked for cartesianness, and correction terms cannot be dismissed merely because the coefficient modules form an exact sequence.

### 13.5 The dual tangent condition

The finite Tate dual of the adjoint module is

$$
\operatorname{ad}(\overline\rho)^*(1).
$$

The trace pairing often identifies $\operatorname{ad}(\overline\rho)^*$ with $\operatorname{ad}(\overline\rho)$, giving a twisted adjoint module, but degeneracies and trace-zero quotients must be checked in the coefficient characteristic. Define

$$
\mathcal L_v^\perp\subseteq
H^1\bigl(K_v,\operatorname{ad}(\overline\rho)^*(1)\bigr)
$$

as the exact annihilator of the tangent subspace (13.2). The resulting group

$$
H^1_{\mathcal L^\perp}
\bigl(K,\operatorname{ad}(\overline\rho)^*(1)\bigr) \tag{13.5}
$$

is the **dual tangent Selmer group**.

It models the dual local directions that later measure failure of global lifting and the need for auxiliary primes. At this stage (13.5) is a well-defined Selmer kernel assembled from local orthogonals. No dimension formula comparing (13.3) and (13.5) has yet been established.

## 14. The reusable global dictionary

### 14.1 A construction protocol

A reliable Selmer construction proceeds in the following order.

1. Fix $K$, $\overline K$, the coefficient category, and a continuous $G_K$-module $M$.
2. Choose $S$ containing infinity, coefficient-characteristic places, ramified places of $M$, and every place with a non-unramified condition.
3. Verify that $M$ factors through $G_{K,S}$; equivalently, inertia outside $S$ acts trivially.
4. Choose geometric places only to define decomposition maps, and record that changing them acts by canonical conjugacy.
5. Specify a subgroup $\mathcal L_v\subseteq H^1(K_v,M)$ at every exceptional place. Require a subspace or submodule when linearity is intended.
6. Form the kernel (6.1), using direct sums of local quotients and remembering that unramified conditions outside $S$ are built in.
7. For a coefficient morphism, check image compatibility. For a short exact sequence, additionally audit cartesianness, degree-zero boundaries, global $H^2$ boundaries, and local lifting defects.
8. For a field extension, include every place above each place and use sums of local corestrictions.
9. For a dual condition, take exact local orthogonals under Tate pairings; do not infer a global pairing.
10. At lattice or torsion level, state topology, closure, and the limit hypotheses before passing between finite levels.

This order keeps ramification, localization, and local permission logically distinct.

### 14.2 Dictionary of objects and maps

| datum | meaning | indispensable qualification |
|---|---|---|
| $S$ | finite exceptional set | contains infinity and, for the standard finiteness theory, coefficient-characteristic and ramified places |
| $K_S/K$ | maximal extension unramified outside $S$ | ramification restriction concerns finite places; real complexification is allowed by our convention |
| $G_{K,S}$ | $\operatorname{Gal}(K_S/K)$ | quotient of $G_K$ by the closed normal subgroup generated by inertia outside $S$ |
| $D_{\overline v}$ | decomposition group | determined only up to conjugacy; cohomology is canonically transported |
| $\operatorname{loc}_v$ | restriction to the local Galois group | outside $S$ its image is unramified |
| $H^1_{\mathrm{ur}}$ | kernel of restriction to inertia | for ramified $M$, use $M^{I_v}$ in the Frobenius formula |
| $\mathcal L_v$ | allowed local classes | subgroup; a vector subspace only when coefficient linearity is required |
| $H^1_{\mathcal L}(K,M)$ | global classes passing every local test | kernel of the map to a direct sum of local quotients |
| relaxed / strict | all of $H^1$ / zero | exact orthogonals of one another |
| Kummer condition | image of local division of points | need not equal unramified at coefficient-characteristic or bad places |
| $\mathcal L_v^\perp$ | local Tate annihilator | exact subgroup, with real Tate modification when $2$-primary |
| restriction | base change from $K$ to $L$ | produces a component at every $w\mid v$ |
| corestriction | transfer from $L$ to $K$ | sums local corestrictions over all $w\mid v$ |
| Shapiro | change of field as induced coefficients | local induced module decomposes over places above $v$ |
| $T$, $V$, $V/T$ | compact lattice, vector space, discrete torsion | cohomology, limits, and duality use different topological categories |

### 14.3 Exactness audit

The exact sequences proved here come from three elementary sources:

* the long exact sequence of ordinary continuous cohomology;
* the definition of a Selmer group as a kernel;
* diagram chases comparing local subgroups and quotient maps.

They include the defining sequence (6.6), the comparison sequence (6.5), the coefficient sequence (7.10) under its stated hypotheses, the $S$-unit/class-group sequence (10.4), and the elliptic-curve sequence (11.3). None uses Poitou--Tate duality.

Before claiming exactness for a new coefficient sequence, check four distinct points:

1. Does the coefficient map preserve every local condition?
2. Is the source condition the full inverse image of the middle condition?
3. Does a globally liftable target class have a lift satisfying all middle local conditions?
4. At real $2$-primary places, is ordinary or modified cohomology intended in each degree?

Failure at the second point creates the defect (7.6). Failure at the third creates (7.9), even when the global $H^2$ boundary vanishes. Therefore arbitrary assignments of local conditions do not form exact functors.

What remains beyond this audit is sharply defined. A theorem identifying the cokernel in (6.6), relating it to (9.4), or deriving a numerical difference between a Selmer group and its dual is a global duality theorem. Those statements have not been assumed here.

### 14.4 Conclusion

Global Galois cohomology begins by removing unwanted inertia. The quotient $G_{K,S}$ remembers every Frobenius outside $S$ while allowing ramification only at finitely many controlled places. Its cohomology with finite coefficients is finite under explicit hypotheses, and localization carries each global class to compatible shadows in the completions. Choices of geometric places introduce only canonical conjugacy, while real places contribute a genuine $2$-primary phenomenon that requires Tate modification outside degree one.

A Selmer structure adds arithmetic meaning to this finite global arena. Unramified, strict, relaxed, Kummer, and integral conditions are subgroups of local $H^1$, and their global assembly is the inverse image of their product, equivalently the kernel of a map to local quotients. This kernel description explains independence of the controlling set, comparison under stronger and weaker conditions, and the exact correction terms required when coefficients vary. Restriction, corestriction, and Shapiro show that the construction survives change of number field only when all places above a place are retained.

Kummer theory makes the framework concrete: valuations produce restricted ramification, units form the kernel, and class-group torsion forms the quotient. Elliptic curves replace units by local points and yield the familiar finite $n$-Selmer group between Mordell--Weil classes and locally trivial torsors. Character groups record cyclic extensions, while adjoint modules turn first-order global deformations into Selmer classes cut out by local tangent subspaces.

Finally, local Tate duality attaches to every permitted direction its exact annihilator. The resulting dual Selmer group is now defined, including the archimedean and topological qualifications needed at finite, lattice, torsion, and vector-space levels. The global relation between the two kernels has deliberately not been anticipated. What has been achieved is the complete reusable input for that relation: controlled ramification, canonical localization, precise local conditions, honest exactness criteria, change of field, and dual orthogonals assembled into one global language.
