# Poitou–Tate Duality

## Contents

- [1. The defect in prescribing local classes](#1-the-defect-in-prescribing-local-classes)
  - [1.1 Local freedom and global dependence](#11-local-freedom-and-global-dependence)
  - [1.2 The reciprocity-shaped obstruction](#12-the-reciprocity-shaped-obstruction)
  - [1.3 The three layers of the theorem](#13-the-three-layers-of-the-theorem)
- [2. Coefficients, places, and duals](#2-coefficients-places-and-duals)
  - [2.1 Standing hypotheses](#21-standing-hypotheses)
  - [2.2 The Tate-twisted dual](#22-the-tate-twisted-dual)
  - [2.3 Modified cohomology at infinity](#23-modified-cohomology-at-infinity)
  - [2.4 Local packages and their topology](#24-local-packages-and-their-topology)
  - [2.5 What the standing hypotheses buy](#25-what-the-standing-hypotheses-buy)
- [3. Compact support as a mapping cone](#3-compact-support-as-a-mapping-cone)
  - [3.1 Why a cone is the right object](#31-why-a-cone-is-the-right-object)
  - [3.2 The cochain construction](#32-the-cochain-construction)
  - [3.3 The localization long exact sequence](#33-the-localization-long-exact-sequence)
  - [3.4 Independence, signs, and coefficient sequences](#34-independence-signs-and-coefficient-sequences)
  - [3.5 Low-degree meaning and a first calculation](#35-low-degree-meaning-and-a-first-calculation)
  - [3.6 Enlarging the boundary](#36-enlarging-the-boundary)
- [4. Global reciprocity and the global trace](#4-global-reciprocity-and-the-global-trace)
  - [4.1 Summing local invariants](#41-summing-local-invariants)
  - [4.2 Why global cup products have sum zero](#42-why-global-cup-products-have-sum-zero)
  - [4.3 The compactly supported global trace](#43-the-compactly-supported-global-trace)
  - [4.4 From vanishing to a cochain pairing](#44-from-vanishing-to-a-cochain-pairing)
- [5. Perfect global duality](#5-perfect-global-duality)
  - [5.1 The duality theorem](#51-the-duality-theorem)
  - [5.2 The finite-level engine](#52-the-finite-level-engine)
  - [5.3 Proof of perfectness](#53-proof-of-perfectness)
  - [5.4 What the proof actually uses](#54-what-the-proof-actually-uses)
  - [5.5 The real 2-primary tail](#55-the-real-2-primary-tail)
- [6. The Poitou--Tate exact sequence](#6-the-poitou--tate-exact-sequence)
  - [6.1 Every map in the finite-$S$ sequence](#61-every-map-in-the-finite-s-sequence)
  - [6.2 Exactness, not merely a dimension count](#62-exactness-not-merely-a-dimension-count)
  - [6.3 Annihilators of localization images](#63-annihilators-of-localization-images)
  - [6.4 The all-places form](#64-the-all-places-form)
  - [6.5 Endpoint and degree checks](#65-endpoint-and-degree-checks)
  - [6.6 Perfect pairings on local--global kernels](#66-perfect-pairings-on-local--global-kernels)
- [7. Finite, compact, and discrete coefficients](#7-finite-compact-and-discrete-coefficients)
  - [7.1 Pontryagin variance](#71-pontryagin-variance)
  - [7.2 Lattices and discrete torsion partners](#72-lattices-and-discrete-torsion-partners)
  - [7.3 Vector-space duality](#73-vector-space-duality)
  - [7.4 Where products and closures enter](#74-where-products-and-closures-enter)
  - [7.5 Why the limit comparison is exact](#75-why-the-limit-comparison-is-exact)
  - [7.6 The topological exact sequence](#76-the-topological-exact-sequence)
  - [7.7 Rationalization and the vector-space sequence](#77-rationalization-and-the-vector-space-sequence)
  - [7.8 Infinite-level Selmer conditions](#78-infinite-level-selmer-conditions)
- [8. Selmer structures under global duality](#8-selmer-structures-under-global-duality)
  - [8.1 Orthogonal local permissions](#81-orthogonal-local-permissions)
  - [8.2 The Selmer Poitou--Tate sequence](#82-the-selmer-poitou--tate-sequence)
  - [8.3 Exact orthogonality of the localization defect](#83-exact-orthogonality-of-the-localization-defect)
  - [8.4 Comparing two Selmer structures](#84-comparing-two-selmer-structures)
  - [8.5 What is perfect and what is not](#85-what-is-perfect-and-what-is-not)
- [9. Euler characteristics and the numerical formula](#9-euler-characteristics-and-the-numerical-formula)
  - [9.1 The global Euler characteristic](#91-the-global-euler-characteristic)
  - [9.2 The Greenberg--Wiles order formula](#92-the-greenberg--wiles-order-formula)
  - [9.3 Finite coefficient fields](#93-finite-coefficient-fields)
  - [9.4 Self-dual modules and parity cautions](#94-self-dual-modules-and-parity-cautions)
  - [9.5 A detailed derivation of the dimension formula](#95-a-detailed-derivation-of-the-dimension-formula)
  - [9.6 Lattices, torsion modules, and rational dimensions](#96-lattices-torsion-modules-and-rational-dimensions)
- [10. A calculus of local conditions](#10-a-calculus-of-local-conditions)
  - [10.1 Strict, relaxed, and unramified conditions](#101-strict-relaxed-and-unramified-conditions)
  - [10.2 Enlarging the controlling set](#102-enlarging-the-controlling-set)
  - [10.3 Adding and removing one condition](#103-adding-and-removing-one-condition)
  - [10.4 A counterexample to naive dimension subtraction](#104-a-counterexample-to-naive-dimension-subtraction)
- [11. Restriction, corestriction, and extension of fields](#11-restriction-corestriction-and-extension-of-fields)
  - [11.1 Adjointness place by place](#111-adjointness-place-by-place)
  - [11.2 Compatibility of global duality](#112-compatibility-of-global-duality)
  - [11.3 Induced Selmer conditions and Shapiro](#113-induced-selmer-conditions-and-shapiro)
- [12. Arithmetic examples](#12-arithmetic-examples)
  - [12.1 Kummer theory and class groups](#121-kummer-theory-and-class-groups)
  - [12.2 The product formula as the first exact sequence](#122-the-product-formula-as-the-first-exact-sequence)
  - [12.3 Elliptic Selmer groups](#123-elliptic-selmer-groups)
  - [12.4 Failure of an unrestricted local--global principle](#124-failure-of-an-unrestricted-local--global-principle)
  - [12.5 A complete quadratic count over the rationals](#125-a-complete-quadratic-count-over-the-rationals)
  - [12.6 Why modified degree zero is smaller](#126-why-modified-degree-zero-is-smaller)
- [13. Adjoint modules and deformation conditions](#13-adjoint-modules-and-deformation-conditions)
  - [13.1 Fixed determinant and the trace-zero adjoint](#131-fixed-determinant-and-the-trace-zero-adjoint)
  - [13.2 Tangent conditions and their duals](#132-tangent-conditions-and-their-duals)
  - [13.3 Why the dual Selmer dimension counts missing equations](#133-why-the-dual-selmer-dimension-counts-missing-equations)
  - [13.4 What auxiliary primes must accomplish](#134-what-auxiliary-primes-must-accomplish)
- [14. The global-duality dictionary](#14-the-global-duality-dictionary)
  - [14.1 A construction protocol](#141-a-construction-protocol)
  - [14.2 Formula and variance table](#142-formula-and-variance-table)
  - [14.3 Final synthesis](#143-final-synthesis)

## 1. The defect in prescribing local classes

### 1.1 Local freedom and global dependence

The preceding theory gives two apparently conflicting impressions. Local Tate duality says that each finite local cohomology group has a perfect partner. Global cohomology says that a class over a number field has a localization at every completion. It is tempting to combine these facts by treating the localizations as independent coordinates. They are not independent.

The elementary model is the divisor of a rational number. Given integers $n_v$, almost all zero, there need not be an element $a\in K^\times$ with $v(a)=n_v$ at every finite place. Even for a principal divisor one has a degree relation, and the ideal class group supplies a further obstruction. Similarly, a family

$$
(x_v)_{v\in S}\in\bigoplus_{v\in S}H^1(K_v,M)
$$

need not be the localization of a global class. The obstruction cannot be read at one place: it is detected by pairing the whole family against global classes for a dual module and summing the answers.

This suggests the central question of the book. Let $M$ be a finite Galois module and let $M^\vee(1)$ be its Tate-twisted dual. Is the failure of $(x_v)$ to globalize measured exactly by the function

$$
y\longmapsto\sum_{v\in S}\langle x_v,\operatorname{loc}_v y\rangle_v,
\qquad
y\in H^1(G_{K,S},M^\vee(1))?
$$

There are three demands hidden in the word “exactly.” Every global family must give the zero functional. Every zero functional must come from a global family. And the endpoint kernels and cokernels in degrees zero and two must also be identified. The first demand follows from reciprocity; the second is the hard perfectness assertion; the third forces the full exact sequence rather than a middle-degree slogan.

### 1.2 The reciprocity-shaped obstruction

For local classes $x_v\in H^r(K_v,M)$ and $y_v\in H^{2-r}(K_v,M^\vee(1))$, the local pairing is

$$
\langle x_v,y_v\rangle_v
=\operatorname{inv}_v(x_v\smile y_v)\in\mathbf Q/\mathbf Z.
$$

Suppose both classes arise by localization from global classes $x$ and $y$. Naturality of cup products gives

$$
\langle\operatorname{loc}_v x,\operatorname{loc}_v y\rangle_v
=\operatorname{inv}_v\bigl(\operatorname{loc}_v(x\smile y)\bigr).
$$

Global Brauer reciprocity says that the sum of the local invariants of a global Brauer class is zero. Hence

$$
\sum_v\langle\operatorname{loc}_v x,\operatorname{loc}_v y\rangle_v=0. \tag{1.1}
$$

This is the reason a sum, rather than a list, occurs. It is also the reason the target is $\mathbf Q/\mathbf Z$: the local Brauer invariants have this common coordinate, and global reciprocity supplies their unique global relation.

Equation (1.1) proves only containment in an annihilator. The content of global duality is the reverse containment. A family satisfying every reciprocity test really has no further hidden obstruction. In linear algebra that would follow from finite-dimensional perfect pairings. Here the spaces arise from different profinite groups, infinity requires modification, and the relevant cochain object is a cone. Establishing perfectness therefore occupies the structural center of the argument.

### 1.3 The three layers of the theorem

It helps to separate three statements that are often compressed under one name.

First comes a cochain construction. The cone of global localization records a global cochain together with local data trivializing its localization. Its cohomology is compactly supported Galois cohomology.

Second comes perfect duality:

$$
H_c^i(G_{K,S},M)\times
H^{3-i}(G_{K,S},M^\vee(1))
\longrightarrow\mathbf Q/\mathbf Z. \tag{1.2}
$$

This is a theorem about finite groups, not merely a pairing. Its proof combines local duality, the global Brauer sequence, class field theory, and finite-level devissage.

Third, substituting (1.2) into the cone long exact sequence gives the Poitou--Tate sequence. Selmer exact sequences and numerical formulas are consequences of that sequence. Keeping the layers separate prevents circular reasoning: the named exact sequence will not be invoked to prove the perfectness from which it is derived.

## 2. Coefficients, places, and duals

### 2.1 Standing hypotheses

Throughout the finite-coefficient theory, $K$ is a number field and $S$ is a finite set of places containing:

* every archimedean place;
* every finite place whose residue characteristic divides the exponent of $M$;
* every finite place where the action on $M$ is ramified.

The coefficient module $M$ is a finite discrete continuous $G_{K,S}$-module. If $nM=0$, set

$$
M'=M^\vee(1)=\operatorname{Hom}(M,\mu_n), \tag{2.1}
$$

with action $(g\phi)(m)=g\phi(g^{-1}m)$. The notation is independent of the chosen annihilating $n$: embedding all roots of unity into $\mathbf Q/\mathbf Z(1)$ gives equivalently

$$
M'=\operatorname{Hom}(M,\mathbf Q/\mathbf Z(1)).
$$

It too is finite and unramified outside $S$. The evaluation map $M\times M'\to\mu_n$ is perfect, and biduality identifies $(M')'\simeq M$.

The assumptions on $S$ are deliberately strong and stable. They ensure finiteness of the global cohomology groups, vanishing of unwanted unramified degree-two groups outside $S$, and clean localization. A smaller $S$ can sometimes be used, but then every omitted coefficient-characteristic place must be audited separately. A finite set is essential: without restricted ramification, $H^1(K,M)$ can be infinite even when $M$ is finite.

### 2.2 The Tate-twisted dual

Why not use $\operatorname{Hom}(M,\mathbf Q/\mathbf Z)$? Local invariant maps consume a class in

$$
H^2(K_v,\mathbf Q/\mathbf Z(1)),
$$

the torsion Brauer group. Therefore evaluation must land in $\mathbf Q/\mathbf Z(1)$. The twist is dictated by the target of the invariant map, not added as a normalization after the fact.

Variance matters. A map $f:M\to N$ induces

$$
f':N'\longrightarrow M',\qquad f'(\lambda)=\lambda\circ f.
$$

Cup products then satisfy

$$
\langle f_*x,y\rangle_v=\langle x,f'_*y\rangle_v. \tag{2.2}
$$

This reversal is structural: confusing $f'$ with a map $M'\to N'$ reverses every dual exact sequence.

For a finite field $k$ of characteristic $\ell$ and a finite-dimensional $k$-module $M$, one often chooses an identification of the $\ell$-primary roots of unity with $k(1)$ and writes $M^*(1)$, where $M^*=\operatorname{Hom}_k(M,k)$. The underlying Pontryagin dual and the $k$-linear dual agree only after fixing a nonzero additive character $k\to\mathbf Q/\mathbf Z$. Dimension formulas do not depend on that choice; actual pairings do.

### 2.3 Modified cohomology at infinity

At a finite place, put

$$
\widetilde H^i(K_v,M)=H^i(K_v,M).
$$

At a complex place, put $\widetilde H^i(K_v,M)=0$ in every degree. At a real place, with $G_{K_v}=\langle c\rangle\simeq C_2$, put

$$
\widetilde H^i(K_v,M)=\widehat H^i(C_2,M), \tag{2.3}
$$

the Tate cohomology group in every integral degree. Explicitly,

$$
\widehat H^{2j}(C_2,M)=M^{c=1}/(1+c)M,
$$

$$
\widehat H^{2j+1}(C_2,M)=\ker(1+c)/(c-1)M. \tag{2.4}
$$

Thus $\widetilde H^1=H^1$ at a real place, while degree zero is modified. If $2$ is invertible on $M$, all groups in (2.3) vanish. The convention is invisible for odd-order coefficients but indispensable for 2-primary coefficients.

Local duality at a real place is then the perfect Tate pairing

$$
\widetilde H^i(K_v,M)\times
\widetilde H^{2-i}(K_v,M')\longrightarrow\tfrac12\mathbf Z/\mathbf Z
\subset\mathbf Q/\mathbf Z. \tag{2.5}
$$

The invariant sends the nonzero class of $\operatorname{Br}(\mathbf R)$ to $1/2$. At a complex place both sides are zero. Replacing $\widehat H^0$ by ordinary $H^0$ would destroy perfectness at the left endpoint of the global sequence.

**Example.** For $M=\mathbf Z/2\mathbf Z$ with trivial real action,

$$
\widehat H^i(\mathbf R,M)\simeq\mathbf Z/2\mathbf Z
$$

in every degree. Ordinary cohomology has $H^0=M$ and a periodic positive tail, but no negative degrees. The complete Tate complex supplies precisely the two-sided periodic object needed by the cone.

### 2.4 Local packages and their topology

For finite $S$, define

$$
P_S^i(M)=\bigoplus_{v\in S}\widetilde H^i(K_v,M). \tag{2.6}
$$

This is a finite direct sum of finite discrete groups, hence also a finite product. We use the direct-sum notation because it remains correct when $S$ varies and because local invariants are summed.

The pairing

$$
P_S^i(M)\times P_S^{2-i}(M')\longrightarrow\mathbf Q/\mathbf Z,
\qquad
((x_v),(y_v))\longmapsto\sum_{v\in S}\langle x_v,y_v\rangle_v \tag{2.7}
$$

is perfect. This follows place by place from local Tate duality. Notice that its second degree is $2-i$, whereas global compact-support duality uses $3-i$. The shift by one comes from the localization cone.

For a finite abelian group $A$, write

$$
A^D=\operatorname{Hom}(A,\mathbf Q/\mathbf Z).
$$

At finite level no topology is visible, but this notation anticipates Pontryagin duality. A map $u:A\to B$ dualizes to $u^D:B^D\to A^D$. Every later arrow into a superscript $D$ will be checked against this reversal.

### 2.5 What the standing hypotheses buy

The conditions on $S$ are not ceremonial. Each one removes a different ambiguity in the global theorem.

If a finite place $v$ dividing $n$ were omitted, the prime-to-residue-characteristic description of unramified local cohomology would no longer control the full local group. If a ramified place of $M$ were omitted, the map from the local decomposition group to $G_{K,S}$ would kill inertia even though inertia acts nontrivially on $M$. If an archimedean place were omitted, the product formula would lose a term, and at a real place that term can be nonzero for $2$-primary coefficients. Finally, finiteness of $S$ is what turns the local package into a finite group and the global restricted-ramification groups into finite groups in the relevant degrees.

There are two useful boundary cases. When $n$ is odd, every real modified group vanishes because multiplication by $2$ is invertible on $M$. The exact sequence still includes the real places conceptually, but they contribute zero. When $K$ is totally imaginary, there is no periodic real tail at all, even for $2$-primary coefficients. In either case the ordinary cohomological dimension is two in the torsion range under discussion. Over a field with real embeddings and $2$-primary coefficients, one must instead retain the modified convention throughout.

The theorem concerns finite discrete modules over a number field. It is not the corresponding theorem for a global function field in characteristic $p$ with $p$-primary coefficients: roots of unity then fail to furnish the required dual, and first cohomology can be infinite. Nor does it cover a finite noncommutative group as coefficient object; cup product and Pontryagin duality require an abelian module. These are changes of theory, not harmless variations of notation.

We will use four related but distinct degree conventions:

| object | complementary degree | reason |
|---|---:|---|
| local cohomology | $2-i$ | local invariant lives in degree $2$ |
| compact support versus global cohomology | $3-i$ | the localization cone contributes one shift |
| the local term inside the global sequence | $2-i$ | it is paired place by place |
| a Selmer condition in degree $1$ | $1$ | degree one is its own local complement |

This table is a useful diagnostic. A shift of three belongs to a compact-support/global pairing, never to a local pairing. A shift of two belongs to local duality and to the obstruction map out of a local package.

## 3. Compact support as a mapping cone

### 3.1 Why a cone is the right object

A global cochain whose localizations vanish as cochains is too rigid. A global cohomology class is locally zero when each localized cocycle is a coboundary, and the chosen local primitives matter in one lower degree. The object must therefore store a global cochain $x$ together with local cochains $y_v$ satisfying

$$
\operatorname{loc}_v(x)=dy_v.
$$

This is exactly what a shifted mapping cone records. The shift is responsible for the degree $3-i$ in global duality and for the placement of the dual groups in the exact sequence.

### 3.2 The cochain construction

Let $C^\bullet(G_{K,S},M)$ be the continuous inhomogeneous cochain complex. At finite places use $C^\bullet(K_v,M)$. At a real place choose a complete resolution of $C_2$ and its Tate cochain complex $\widehat C^\bullet(K_v,M)$; at a complex place use an acyclic zero complex. A comparison from ordinary nonnegative cochains to the complete resolution yields a localization morphism

$$
\lambda:C^\bullet(G_{K,S},M)\longrightarrow
C_S^\bullet(M):=\bigoplus_{v\in S}\widetilde C^\bullet(K_v,M). \tag{3.1}
$$

Different complete resolutions and comparison maps are homotopy equivalent, so the resulting cohomology is canonical.

Define the compactly supported complex by

$$
C_c^\bullet(G_{K,S},M)=\operatorname{Cone}(\lambda)[-1]. \tag{3.2}
$$

With the convention used here,

$$
C_c^q=C^q(G_{K,S},M)\oplus C_S^{q-1}(M),
$$

$$
d_c(x,y)=(dx,\lambda(x)-dy). \tag{3.3}
$$

Indeed $d_c^2=0$. A cocycle is a global cocycle $x$ together with local primitives $y$ of its localization. Put

$$
H_c^q(G_{K,S},M)=H^q(C_c^\bullet(G_{K,S},M)).
$$

The adjective “compactly supported” reflects the arithmetic analogy with cohomology of an open arithmetic curve: classes are globally defined but equipped with trivializations along the deleted places.

### 3.3 The localization long exact sequence

The distinguished triangle

$$
C_c^\bullet(M)\longrightarrow C^\bullet(G_{K,S},M)
\xrightarrow{\lambda}C_S^\bullet(M)
\longrightarrow C_c^\bullet(M)[1]
$$

gives

$$
\cdots\to H_c^i(G_{K,S},M)\to H^i(G_{K,S},M)
\xrightarrow{\operatorname{loc}}P_S^i(M)
\xrightarrow{\partial_c}H_c^{i+1}(G_{K,S},M)\to\cdots. \tag{3.4}
$$

The boundary has a concrete description. A local cocycle $y\in C_S^i(M)$ represents an element of $P_S^i(M)$, and

$$
\partial_c[y]=[(0,y)]
$$

in the cone. It vanishes precisely when there are a global cocycle $x$ and a local cochain $z$ with $y=\lambda(x)-dz$. Thus the cone boundary measures failure to arise globally, allowing equality up to local coboundary as it should.

When there is real 2-primary cohomology, the long exact sequence extends in both directions through the periodic real Tate groups. In particular one should not assert $H_c^0=0$: it is dual to the possible ordinary global $H^3$ tail. What makes the familiar finite sequence begin with $0\to H^0$ is instead that, in degrees above two, global restriction is an isomorphism onto the sum of the real Tate tails. The adjacent terms cancel canonically. If $2$ is invertible on $M$, or if $K$ has no real places, both tails vanish outright.

### 3.4 Independence, signs, and coefficient sequences

Changing a geometric place conjugates localization. Conjugation acts by a cochain homotopy after transporting coefficients, so the cones are canonically quasi-isomorphic. Compact support is therefore independent of the auxiliary embeddings.

For a short exact sequence $0\to M_1\to M_2\to M_3\to0$, the global and local cochain rows are exact and compatible. Taking cones produces a short exact sequence of compact-support complexes and hence a long exact sequence in $H_c^i$. This exactness is essential for devissage in the proof of perfectness.

The sign in (3.3) is also essential. It ensures that cup products on cones obey the graded Leibniz rule. Using $(dx,\lambda x+dy)$ without changing the cone convention makes $d_c^2$ nonzero. Later exact-sequence arrows are insensitive to replacing the entire cone by an isomorphic sign convention, but mixing conventions inside one proof is not.

### 3.5 Low-degree meaning and a first calculation

The cone is less abstract when read degree by degree. In degree one, a class of $H_c^1$ is represented by a global cocycle together with local degree-zero elements correcting its localization. Its image in $H^1(G_{K,S},M)$ is therefore a global class locally trivial at every place in $S$. The kernel of that map records compatible local corrections of the zero global cocycle. In degree two, a compactly supported class consists of a global obstruction together with local one-cochains trivializing its localizations. This is the degree that will detect failure of a local degree-one family to globalize.

If every archimedean modified term vanishes, the beginning of the long exact sequence reads

$$
0\longrightarrow H_c^0(M)\longrightarrow H^0(M)
\longrightarrow P_S^0(M)\longrightarrow H_c^1(M)
\longrightarrow H^1(M). \tag{3.5}
$$

Because $S$ contains a finite place and the map on degree-zero invariants is the diagonal inclusion, $H_c^0(M)=0$. This argument is deliberately not used at a real $2$-primary place, where negative modified degrees intervene before $H_c^0$. There the correct conclusion is obtained only after the periodic tail is paired and cancelled.

For $M=\mu_n$, degree three has an especially concrete meaning. The segment

$$
H^2(G_{K,S},\mu_n)\longrightarrow P_S^2(\mu_n)
\longrightarrow H_c^3(G_{K,S},\mu_n)
$$

says that a compactly supported degree-three class is a family of local Brauer classes modulo those coming globally, together with the harmless real-tail correction. Global reciprocity identifies the quotient with $\tfrac1n\mathbf Z/\mathbf Z$. The next chapter turns this observation into the global trace.

### 3.6 Enlarging the boundary

Suppose $S\subset S'$ are two admissible sets. The global groups change as well as the local sum: $G_{K,S'}$ permits ramification at the new places, whereas $G_{K,S}$ does not. Consequently the relative term is not simply the full local cochain complex. At a new finite place where $M$ is unramified, it is the cone of unramified local cochains mapping to all local cochains:

$$
C^\bullet_{\mathrm{ur}}(K_v,M)
=C^\bullet(G_{k_v},M)
\longrightarrow C^\bullet(K_v,M). \tag{3.6}
$$

The relative cones for $v\in S'\setminus S$ fit with the two compact-support cones in a natural exact triangle. This formulation simultaneously records the newly permitted inertia cocycles and avoids counting the unramified direction twice.

In degree one the consequence is concrete:

$$
H^1(G_{K,S},M)\hookrightarrow H^1(G_{K,S'},M),
$$

and its image consists exactly of the classes whose localizations at every $v\in S'\setminus S$ are unramified. Thus imposing the unramified condition at the new places recovers the old global problem. The same statement on the dual side follows from the unramified orthogonality theorem. “Built into the global group” and “imposed as a local condition” are therefore equivalent only after the relative localization argument; they are not literally the same definition.

## 4. Global reciprocity and the global trace

### 4.1 Summing local invariants

For every place $v$ there is an invariant map

$$
\operatorname{inv}_v:H^2(K_v,\mathbf Q/\mathbf Z(1))\longrightarrow\mathbf Q/\mathbf Z.
$$

At a nonarchimedean place this is the usual Brauer invariant, normalized so that restriction to a finite extension multiplies the invariant by the local degree and corestriction preserves it. At a real place its image is $\{0,1/2\}$, with the nontrivial quaternion class sent to $1/2$. At a complex place the Brauer group vanishes.

Global class field theory gives the exact Brauer sequence

$$
0\longrightarrow\operatorname{Br}(K)
\longrightarrow\bigoplus_v\operatorname{Br}(K_v)
\xrightarrow{\sum_v\operatorname{inv}_v}\mathbf Q/\mathbf Z
\longrightarrow0. \tag{4.1}
$$

In particular, a global Brauer class has only finitely many nonzero localizations and their invariants sum to zero.

### 4.2 Why global cup products have sum zero

Take $x\in H^r(G_{K,S},M)$ and $y\in H^{2-r}(G_{K,S},M')$. Evaluation after cup product gives

$$
x\smile y\in H^2(G_{K,S},\mu_n).
$$

Here evaluation lands in $\mu_n$ because $nM=0$; only after applying a local invariant do we include $\tfrac1n\mathbf Z/\mathbf Z$ into $\mathbf Q/\mathbf Z$. Inflate the cup-product class to $G_K$ and interpret it in the $n$-torsion Brauer group. At a finite $v\notin S$, both coefficients and both classes are unramified. The cup product lies in unramified degree two, which vanishes because the Brauer group of the finite residue field is zero. Hence only places in $S$ contribute. Applying (4.1) gives

$$
\sum_{v\in S}\operatorname{inv}_v
\bigl(\operatorname{loc}_v x\smile\operatorname{loc}_v y\bigr)=0. \tag{4.2}
$$

At real places (4.2) uses the invariant normalization just stated; for 2-primary classes the term can be $1/2$ and cannot be discarded. This proves that the image of global localization in degree $r$ annihilates the image in complementary degree $2-r$.

**Counterexample to a placewise claim.** A global quaternion algebra may be nonsplit at two places. Its local invariant is $1/2$ at each of them, not zero place by place; only the sum is zero. Reciprocity therefore gives a global relation among local pairings, not individual vanishing.

### 4.3 The compactly supported global trace

Reciprocity becomes a duality theorem only after it is turned into a trace map. Begin with the coefficient $\mu_n$. The localization long exact sequence contains

$$
H^2(G_{K,S},\mu_n)\longrightarrow
\bigoplus_{v\in S}\widetilde H^2(K_v,\mu_n)
\longrightarrow H_c^3(G_{K,S},\mu_n)
\longrightarrow H^3(G_{K,S},\mu_n). \tag{4.3}
$$

The sum of the local invariants kills the image of the first arrow. It therefore descends to a map

$$
\operatorname{tr}_{K,S}:H_c^3(G_{K,S},\mu_n)
\longrightarrow \tfrac1n\mathbf Z/\mathbf Z. \tag{4.4}
$$

This map is an isomorphism. To see surjectivity, choose a finite place in $S$. The local invariant on $H^2(K_v,\mu_n)$ has image $\tfrac1n\mathbf Z/\mathbf Z$, so every target value is represented by a local class. For injectivity, suppose a local family has invariant sum zero. Extend it by zero outside $S$. The Brauer exact sequence produces a global Brauer class with precisely those localizations. Because every component outside $S$ is zero, that class is unramified outside $S$ and lies in the image of $H^2(G_{K,S},\mu_n)$. Thus its class in the cokernel vanishes. If real $2$-primary terms continue beyond degree two, the final arrow in (4.3) maps isomorphically onto the real periodic tail; hence it contributes no additional kernel. This proves injectivity in every case covered by the standing convention.

Passing through the inclusions $\mu_n\subset\mu_{mn}$ makes the traces compatible. Their direct limit gives

$$
\operatorname{tr}_{K,S}:H_c^3(G_{K,S},\mathbf Q/\mathbf Z(1))
\xrightarrow{\sim}\mathbf Q/\mathbf Z. \tag{4.5}
$$

The trace does not depend on enlarging $S$. At a new finite place the compact-support triangle adds the local term, but a class coming from the old compact-support group has zero new coordinate; the invariant sum is unchanged. This compatibility is what later permits passage between a fixed controlling set and the all-places sequence.

Compactly supported cup product is now forced. Evaluation $M\otimes M'\to\mu_n$ and the cone product give

$$
H_c^i(G_{K,S},M)\times H^{3-i}(G_{K,S},M')
\longrightarrow H_c^3(G_{K,S},\mu_n).
$$

Composing with (4.4) gives the global pairing. This formulation isolates the normalization in one map and makes functoriality in both coefficients immediate from functoriality of cup product.

### 4.4 From vanishing to a cochain pairing

Cohomological vanishing is not enough to construct a pairing on a cone. One needs a cochain homotopy witnessing that the composite

$$
C^\bullet(G_{K,S},\mu_n)
\longrightarrow C_S^\bullet(\mu_n)
\xrightarrow{\sum\operatorname{inv}_v}\tfrac1n\mathbf Z/\mathbf Z[-2]
$$

is null-homotopic. The Brauer exact sequence and the global fundamental class provide such a homotopy; two choices differ by a homotopy and induce the same pairing on cohomology.

Combine this null-homotopy with the cup product and evaluation. For cone representatives $(x,a)$ and a global cocycle $y$, the resulting value consists schematically of

$$
\sum_{v\in S}\operatorname{inv}_v(a_v\smile\operatorname{loc}_v y)
$$

plus the chosen homotopy applied to $x\smile y$. The second term corrects the fact that $a$ is only a local trivialization. The Leibniz rule and (3.3) show that coboundaries pair trivially. Thus one obtains canonical pairings, identical to cup product followed by the trace (4.4),

$$
H_c^i(G_{K,S},M)\times H^{3-i}(G_{K,S},M')
\longrightarrow\mathbf Q/\mathbf Z. \tag{4.6}
$$

The degree is now transparent: $a$ has local degree $i-1$, so it pairs locally with degree $3-i$ to total degree two.

## 5. Perfect global duality

### 5.1 The duality theorem

**Global duality theorem.** Under the hypotheses of Section 2.1, all groups in (4.6) are finite, and for every integer $i$ the pairing induces an isomorphism

$$
H_c^i(G_{K,S},M)\xrightarrow{\sim}
H^{3-i}(G_{K,S},M')^D. \tag{5.1}
$$

The real terms are understood through the complete Tate complexes of Section 2.3. In the ordinary cohomological range this says that compactly supported degree $i$ is the exact Pontryagin dual of global degree $3-i$ for the twisted dual coefficient.

Before proving the theorem, it is worth locating the difficulty. Local duality proves that the local vertical terms are dual. Reciprocity proves that the global images are orthogonal. Neither proves that an arbitrary functional on global cohomology comes from compact support. Surjectivity in (5.1) is a finite-level global theorem.

### 5.2 The finite-level engine

The phrase “finite level” refers to finite coefficients, not to replacing the absolute groups by a single finite quotient. Although the action on $M$ factors through a finite Galois extension, the kernel still carries the cohomology of units and roots of unity. Discarding that kernel would discard the very classes on which the invariant is evaluated.

We prove the comparison in five steps. The details matter because they also prove compatibility with connecting maps.

**Step 1: the global class formation.** Let $L/K$ be finite Galois, with group $\Delta$. Write $J_L$ for the idèle group and $C_L=J_L/L^\times$ for the idèle class group. The exact sequence

$$
1\longrightarrow L^\times\longrightarrow J_L
\longrightarrow C_L\longrightarrow1 \tag{5.2}
$$

is a sequence of $\Delta$-modules. The module $J_L$ is assembled from local multiplicative groups induced from decomposition subgroups. More precisely, after choosing one place $w$ over each place $v$ of $K$, the relevant cohomology of its restricted factors is computed by the modules induced from $\Delta_w$ with coefficient $L_w^\times$. Shapiro's lemma therefore turns its cohomology into the sum of local cohomology groups, including every $w\mid v$.

Global reciprocity supplies a fundamental class

$$
u_{L/K}\in H^2(\Delta,C_L) \tag{5.3}
$$

whose restriction to a decomposition subgroup agrees with the local fundamental class after passage through (5.2). Its normalization is fixed by the local invariant: for every subgroup $H\subseteq\Delta$, the restriction to $H$ generates a cyclic group of order $|H|$. Corestriction preserves the invariant, while restriction multiplies it by the extension degree. These two rules make the classes compatible in towers.

**Step 2: Tate--Nakayama for lattices.** If $X$ is a finitely generated free abelian $\Delta$-module, cup product with $u_{L/K}$ gives

$$
\widehat H^q(\Delta,X)\xrightarrow{\sim}
\widehat H^{q+2}(\Delta,X\otimes C_L). \tag{5.4}
$$

Here is the proof rather than merely the name of the result. For $X=\mathbf Z[\Delta/H]$, Shapiro reduces (5.4) to the trivial lattice over $H$. In two adjacent degrees that assertion is exactly the norm-index theorem and the fact that $\operatorname{res}_H u_{L/K}$ has order $|H|$. A complete resolution is two-sided, so the long exact sequence propagates those two degrees to every degree. For general $X$, embed it in a finite sum $P$ of regular permutation lattices so that $P/X$ is again free over $\mathbf Z$. The long exact sequences for

$$
0\longrightarrow X\longrightarrow P\longrightarrow P/X\longrightarrow0
$$

shift the assertion one degree at a time. A permutation surjection onto $X$ shifts in the opposite direction. The two shifts and the permutation calculation prove (5.4) for every lattice. Because cup product commutes with boundaries with the graded sign, these are isomorphisms of exact sequences, not isolated isomorphisms of groups.

**Step 3: localization produces the third degree.** Tensor (5.2) with $X$ and compare its global terms with the induced local terms. The adelic middle term becomes the local cochain package by Shapiro. The quotient term is shifted by two through (5.4), and taking the cone of global-to-local localization supplies one further shift. Evaluation against the dual lattice therefore gives a comparison of complexes with complementary degree three. On the trivial lattice this comparison is the elementary Kummer calculation: units and ideal classes occupy degree one, Brauer classes occupy degree two, and the last cokernel is measured by the sum of invariants. Thus the abstract class-formation comparison has exactly the trace normalization of Section 4.

**Step 4: passage from lattices to a finite module.** Let $M$ be killed by $n$ and let $\Delta$ act through a splitting field. The permutation lattice $X_0=\mathbf Z[M]$ maps onto $M$ by $[m]\mapsto m$. Its kernel $X_1$ is free over $\mathbf Z$, giving

$$
0\longrightarrow X_1\longrightarrow X_0\longrightarrow M\longrightarrow0. \tag{5.5}
$$

One must not dualize this sequence into $L^\times$ and simply assert exactness: a finite extension's multiplicative group is not divisible. Instead pass through all finite splitting fields to the multiplicative group of a separable closure. The $n$th-power map there is surjective, so the obstruction to extending a character of the finite quotient vanishes. Applying the character dual is then exact at $M$, and its left term is

$$
\operatorname{Hom}(M,\mu_n)=M'.
$$

The lattice comparisons for $X_0$ and $X_1$, together with the two adjoint long exact sequences of (5.5), give the comparison for $M$ by the five lemma. This is a finite resolution of length one; no infinite repetition of induced embeddings is being hidden.

**Step 5: passage to continuous cohomology.** A continuous cochain with finite coefficients has finite image and is locally constant. Any finite collection of cochains, coboundaries, and chosen primitives therefore factors through some finite quotient. Consequently continuous cohomology is the filtered colimit of the finite-level calculations. Inflation on one side is adjoint to norm on the other; the degree factor in the inflation of the fundamental class is exactly cancelled by restriction--corestriction. Filtered colimits are exact, and character duality turns them into inverse limits. Since all cohomology groups that survive are finite, no completion or derived-limit term appears.

The outcome is a functorial comparison

$$
R\Gamma_c(G_{K,S},M)\xrightarrow{\sim}
R\operatorname{Hom}\bigl(R\Gamma(G_{K,S},M'),\mathbf Q/\mathbf Z\bigr)[-3]. \tag{5.6}
$$

This notation abbreviates the preceding explicit cochain construction. Since $\mathbf Q/\mathbf Z$ is injective, taking cohomology of the right side introduces no extension term. Its degree-$i$ group is exactly $H^{3-i}(G_{K,S},M')^D$.

### 5.3 Proof of perfectness

We now assemble the finite-coefficient engine on the absolute restricted group.

**Proof of the global duality theorem.**

1. **Finiteness.** Restricted ramification and the inclusion in $S$ of primes dividing $n$ imply that $H^q(G_{K,S},M)$ is finite in the low-degree range. Local groups are finite. The cone long exact sequence makes $H_c^q$ finite there, while the real periodic terms are finite in every degree.

2. **The natural comparison.** The null-homotopy of Section 4 makes the cup-product map a morphism from compact-support cohomology to the Pontryagin dual of complementary global cohomology. Compatibility with coefficient boundaries follows from the graded Leibniz rule. Thus the maps (5.1) form a morphism of long exact sequences, rather than a collection of unrelated pairings.

3. **Class-formation comparison.** The lattice calculation and the idèle sequence identify the cone with the character dual complex shifted by three. For $\mathbf Z/n\mathbf Z$ and $\mu_n$, this is visibly the Kummer, ideal-class, and Brauer calculation; the last map is the sum of invariants.

4. **Finite-module devissage.** The length-one permutation-lattice resolution (5.5), exact character duality after passage to the separable closure, and the five lemma prove (5.6) for every finite $M$.

5. **Real places.** When $2\mid n$, the argument uses complete resolutions at real decomposition groups throughout. Their two-periodic Tate pairings are perfect, and the real fundamental class has invariant $1/2$. Thus devissage includes, rather than deletes, the real tail.

This proves (5.1). In particular the pairing is nondegenerate on both sides; finiteness makes it a perfect pairing. $\square$

### 5.4 What the proof actually uses

The proof has four arithmetic inputs, each with a distinct job.

* Local Tate duality makes every local pairing perfect.
* The Brauer exact sequence makes the sum of invariants the only degree-two global relation.
* The global norm-index theorem makes cup product with the fundamental class an isomorphism, not just a map.
* Restricted-ramification finiteness keeps every comparison group finite, so Pontryagin duality is exact and nondegeneracy becomes perfectness.

Removing any one changes the conclusion. Local perfectness alone gives only orthogonality. Reciprocity alone gives only one containment. A pairing of infinite groups can be nondegenerate without identifying the full continuous dual. And without the real Tate modification, the 2-primary complex has an unaccounted periodic tail.

### 5.5 The real 2-primary tail

The treatment of a real place deserves a final audit because two different operations are involved. Locally, ordinary $H^i(C_2,M)$ is replaced by $\widehat H^i(C_2,M)$. Globally, ordinary $H^i(G_{K,S},M)$ is retained. For a 2-primary module the latter need not vanish for $i>2$. Instead, restriction induces isomorphisms

$$
H^i(G_{K,S},M)\xrightarrow{\sim}
\bigoplus_{v\text{ real}}\widehat H^i(K_v,M),
\qquad i\ge3. \tag{5.7}
$$

The same statement holds for $M'$. This follows by passing to a totally imaginary extension of degree a power of two, using cohomological dimension two there, and applying restriction--corestriction and the complete-resolution sequence for the real decomposition groups. Said geometrically, every high-degree class is supported at the real boundary.

Now inspect the cone sequence before degree zero:

$$
H^{-1}(G_{K,S},M)\to P_S^{-1}(M)
\to H_c^0(G_{K,S},M)
\to H^0(G_{K,S},M). \tag{5.8}
$$

The first group is zero, while duality identifies $H_c^0(M)$ with $H^3(M')^D$. Under this identification the middle arrow is dual to the isomorphism (5.7) for $M'$ in degree three. It is therefore an isomorphism. The next arrow is zero, and the following map $H^0(M)\to P_S^0(M)$ is injective. At the other end, the same cancellation shows that $P_S^2(M)\to H^0(M')^D$ is surjective even though $H^3(M)$ itself may be nonzero.

This explains precisely why the nine visible terms remain exact for 2-primary coefficients. The periodic groups have not been declared zero; they cancel through canonical restriction isomorphisms immediately outside the displayed range. Any proof that simply says the global cohomological dimension is two over a field with real places has missed this phenomenon.

## 6. The Poitou--Tate exact sequence

### 6.1 Every map in the finite-$S$ sequence

Insert (5.1) into (3.4). The result is the exact sequence

$$
\begin{aligned}
0\to{}&H^0(G_{K,S},M)
\xrightarrow{\operatorname{loc}}P_S^0(M)
\xrightarrow{\alpha_0}H^2(G_{K,S},M')^D\\
\to{}&H^1(G_{K,S},M)
\xrightarrow{\operatorname{loc}}P_S^1(M)
\xrightarrow{\alpha_1}H^1(G_{K,S},M')^D\\
\to{}&H^2(G_{K,S},M)
\xrightarrow{\operatorname{loc}}P_S^2(M)
\xrightarrow{\alpha_2}H^0(G_{K,S},M')^D
\to0.
\end{aligned} \tag{6.1}
$$

The endpoint zeroes include the real modification. All groups are finite.

The maps $\alpha_i$ are not mysterious connecting arrows. For $x=(x_v)\in P_S^i(M)$,

$$
\alpha_i(x)(y)=\sum_{v\in S}
\langle x_v,\operatorname{loc}_v y\rangle_v,
\qquad
y\in H^{2-i}(G_{K,S},M'). \tag{6.2}
$$

Thus $\alpha_i$ lands in the dual of degree $2-i$. The maps following a dual global group are the cone boundary transported through (5.1); equivalently, they are dual to the corresponding localization map for $M'$, with the sign dictated by the cone. Changing all those signs coherently gives an isomorphic exact sequence. Kernels and annihilators are sign-independent.

In degree zero, note that $P_S^0$ uses $\widehat H^0$ at real places and zero at complex places, not ordinary invariants. In degree one there is no difference at real places. In degree two the real Tate group is again $\widehat H^0$ by periodicity.

### 6.2 Exactness, not merely a dimension count

We prove the central exactness assertion explicitly. Let $x\in P_S^1(M)$. If $x=\operatorname{loc}(a)$ for a global $a$, then (4.2) gives

$$
\alpha_1(x)(b)=0
$$

for every global $b$ with coefficients in $M'$. Hence $\operatorname{im}(\operatorname{loc})\subseteq\ker(\alpha_1)$.

Conversely, if $\alpha_1(x)=0$, then the cone class $\partial_c(x)\in H_c^2(M)$ pairs trivially with every element of $H^1(M')$. Perfectness (5.1) forces $\partial_c(x)=0$. Exactness of (3.4) then gives $x\in\operatorname{im}(\operatorname{loc})$. Therefore

$$
\operatorname{im}\bigl(H^1(G_{K,S},M)\to P_S^1(M)\bigr)
=\ker\alpha_1. \tag{6.3}
$$

The same argument works in degrees zero and two. This is stronger than comparing orders: it identifies the actual subgroup of locally realizable families.

### 6.3 Annihilators of localization images

Use the perfect local pairing $P_S^i(M)\times P_S^{2-i}(M')$. Formula (6.2) and exactness give the exact annihilator identity

$$
\operatorname{im}\bigl(H^i(G_{K,S},M)\to P_S^i(M)\bigr)^\perp
=\operatorname{im}\bigl(H^{2-i}(G_{K,S},M')\to P_S^{2-i}(M')\bigr). \tag{6.4}
$$

Indeed the right side is contained in the annihilator by reciprocity. Both are kernels of the adjoint map supplied by (6.1), or, equivalently, local perfectness and (6.3) prove the reverse inclusion. Biduality gives the symmetric statement with $M$ and $M'$ exchanged.

This is the clean answer to the motivating question: the only constraints on local data are the pairings against global dual classes. No additional cardinality argument is needed, and no weaker “same order” statement is substituted for equality of subgroups.

### 6.4 The all-places form

There is also a form without a fixed ramification set. For $i=1$, define the restricted product

$$
P^1(M)=\prod_v' H^1(K_v,M)
$$

with respect to $H^1_{\mathrm{ur}}(K_v,M)$ at almost all finite places and with the modified convention at infinity. For degree zero the corresponding object is the full product of the local degree-zero groups; for degree two it is the direct sum, because unramified degree two vanishes at almost all places. Give $P^1(M)$ its restricted-product topology.

The passage from finite $S$ to all places is a mixed limit, not a uniform direct limit. The discrete global cohomology groups are obtained by allowing larger finite ramification sets, their Pontryagin duals therefore form inverse limits, $P^0(M)$ is the inverse limit of the finite products under projection, and $P^1(M)$ is the union of the open packages in which the coordinates outside a finite set are unramified. Compatibility of localization, invariant maps, and these transition maps yields the unrestricted sequence

$$
\begin{aligned}
0\to{}&H^0(K,M)\to P^0(M)\to H^2(K,M')^D
\to H^1(K,M)\to P^1(M)\\
\to{}&H^1(K,M')^D\to H^2(K,M)\to P^2(M)
\to H^0(K,M')^D\to0. \tag{6.5}
\end{aligned}
$$

Here $H^i(K,M)$ means absolute Galois cohomology; these groups need not be finite. The arrows involving duals are continuous Pontryagin-dual arrows, and exactness is topological: images are closed and equal to kernels. Formula (6.5) should not be obtained by either taking a direct limit term by term or replacing every finite direct sum in (6.1) by an unrestricted product. Degree one needs the restricted product, degree two a direct sum, and degree zero a product.

For deformation and Selmer problems, (6.1) is usually preferable: one fixes a finite $S$, retains finite groups, and records the unramified conditions outside $S$ in the definition of $G_{K,S}$.

### 6.5 Endpoint and degree checks

Several quick specializations detect most indexing errors in (6.1).

Take $M=\mu_n$, so $M'=\mathbf Z/n\mathbf Z$. The last three nonzero terms are

$$
H^2(G_{K,S},\mu_n)\longrightarrow
\bigoplus_{v\in S}\widetilde H^2(K_v,\mu_n)
\longrightarrow H^0(G_{K,S},\mathbf Z/n\mathbf Z)^D
\longrightarrow0. \tag{6.6}
$$

If the action on $\mathbf Z/n\mathbf Z$ is trivial, the last group is canonically $\tfrac1n\mathbf Z/\mathbf Z$. The second arrow is the sum of local invariants. Thus (6.6) recovers the $n$-torsion part of the Brauer exact sequence, restricted to classes unramified outside $S$. This verifies that the last dual is $H^0(M')^D$, not $H^0(M)^D$, and that there is no twist missing.

At the left end, take $M=\mathbf Z/n\mathbf Z$, so $M'=\mu_n$. The map

$$
P_S^0(\mathbf Z/n\mathbf Z)\to H^2(G_{K,S},\mu_n)^D
$$

pairs a tuple of local constants with global Brauer classes. Exactness says that the only locally constant tuples invisible to all such classes are diagonal global constants. This is the degree-zero shadow of the same reciprocity law.

For the middle, the source of $\alpha_1$ is local degree one and its testing group is global degree one. Since $1+(1)=2$, their cup product lands in the Brauer group. If a displayed version places $H^2(M')^D$ after $P_S^1(M)$, it has forgotten the local complementary degree. If it places $H^0(M')^D$ there, it has applied the compact-support shift twice.

Finally, $P_S^0$ and $P_S^2$ are not generally dual to themselves: they are perfect partners after replacing $M$ by $M'$. The real terms are two-periodic, while complex terms are zero in the modified packages. Ordinary complex invariants reappear later in the Euler correction, not as a local Tate cohomology group in (6.1).

### 6.6 Perfect pairings on local--global kernels

The compact-support pairing has a familiar global quotient. Define

$$
\Sha_S^i(K,M)=
\ker\left(H^i(G_{K,S},M)\longrightarrow P_S^i(M)\right). \tag{6.7}
$$

The subscript is important: this is the kernel for the chosen restricted-ramification problem and the modified local package at $S$. When the outside unramified conditions are understood, it agrees with the corresponding all-places kernel in the low degrees used here.

For $i=1,2$, there is a canonical perfect pairing

$$
\Sha_S^i(K,M)\times
\Sha_S^{3-i}(K,M')\longrightarrow\mathbf Q/\mathbf Z. \tag{6.8}
$$

To construct it, take $x\in\Sha_S^i(K,M)$. Exactness of the cone sequence lifts $x$ to a compactly supported class $\widetilde x\in H_c^i(K,M)$. Pair $\widetilde x$ with $y\in\Sha_S^{3-i}(K,M')$ by (4.6). A second lift differs from an element coming from $P_S^{i-1}(M)$. Its pairing with $y$ is the sum of local pairings against $\operatorname{loc}y$, hence zero. The value is therefore independent of the lift.

For perfectness, global duality identifies $H_c^i(K,M)$ with the full dual of $H^{3-i}(K,M')$. The annihilator of $\Sha_S^{3-i}(K,M')$ consists, by (6.4), exactly of the image of $P_S^{i-1}(M)$ inside $H_c^i(K,M)$. Quotienting by that image gives $\Sha_S^i(K,M)$ on the left and the full dual of $\Sha_S^{3-i}(K,M')$ on the right. Thus

$$
\Sha_S^i(K,M)\xrightarrow{\sim}
\Sha_S^{3-i}(K,M')^D. \tag{6.9}
$$

This pairing is genuinely global: neither entry is a local family. It is also the precise theorem behind many finite-level pairings on locally trivial torsors. It does not imply that either kernel vanishes, and self-duality of $M$ does not by itself make the pairing alternating.

## 7. Finite, compact, and discrete coefficients

### 7.1 Pontryagin variance

The finite sequence hides all topological distinctions because every finite group is simultaneously compact and discrete. Later applications use three coefficient regimes, and the correct duality exchanges rather than identifies them.

For a locally compact abelian group $A$, define

$$
A^D=\operatorname{Hom}_{\mathrm{cont}}(A,\mathbf Q/\mathbf Z)
$$

with the compact-open topology. Then:

* the dual of a discrete torsion group is compact;
* the dual of a compact group is discrete;
* finite groups lie in both categories;
* a closed subgroup $B\subseteq A$ has annihilator $(A/B)^D\subseteq A^D$;
* a quotient by a nonclosed subgroup is not the object duality expects.

If $u:A\to B$ is continuous, $u^D:B^D\to A^D$ reverses direction. Moreover,

$$
(\ker u)^D\simeq A^D/\overline{\operatorname{im}(u^D)},
\qquad
(\operatorname{coker}u)^D\simeq\ker(u^D) \tag{7.1}
$$

under the usual locally compact hypotheses. The closure in (7.1) is unnecessary for finite groups and dangerous to omit at infinite level.

### 7.2 Lattices and discrete torsion partners

Let $E/\mathbf Q_\ell$ be finite, $\mathcal O$ its integers, and $T$ a finite free $\mathcal O$-module with continuous $G_{K,S}$-action and its $\varpi$-adic topology. Its natural Tate partner is the discrete module

$$
D(T)=\operatorname{Hom}_{\mathcal O}(T,E/\mathcal O)(1). \tag{7.2}
$$

Every $\mathcal O$-linear map here is continuous, and the Hom group is given the discrete topology. Choose an additive character $\psi_E:E/\mathcal O\to\mathbf Q_\ell/\mathbf Z_\ell$ of conductor $\mathcal O$; equivalently, use the field trace scaled by a generator of the inverse different. Composing evaluation with $\psi_E$ identifies (7.2), as a topological abelian group with its $\mathcal O$-action retained, with the Pontryagin dual of $T$. Using the unscaled trace in a ramified coefficient extension can give the wrong annihilator lattice. Write $T_m=T/\varpi^mT$ and $D_m=D(T)[\varpi^m]$. Finite-level perfectness gives

$$
H_c^i(G_{K,S},T_m)\simeq
H^{3-i}(G_{K,S},D_m)^D. \tag{7.3}
$$

Taking inverse limits on the left and direct limits on the right yields, under the standard Mittag--Leffler hypotheses,

$$
H_c^i(G_{K,S},T)\simeq
H^{3-i}(G_{K,S},D(T))^D. \tag{7.4}
$$

The left side is compact or finitely generated $\mathcal O$-adic; the right side is the dual of a discrete torsion group. Formula (7.4) is not obtained by calling $T$ discrete. Continuous cochains, inverse limits, and possible $\varprojlim^1$ terms must be retained until the Mittag--Leffler condition removes them.

Conversely, if $A$ is a discrete cofinitely generated $\mathcal O$-module, its partner

$$
T(A)=\operatorname{Hom}_{\mathcal O}(A,E/\mathcal O)(1)
$$

is compact with the inverse-limit topology. The order formulas at finite level become corank and characteristic-ideal statements only after controlling finite subgroups and inverse limits; no such refinement is automatic from a finite cardinality identity.

### 7.3 Vector-space duality

Put $V=T\otimes_{\mathcal O}E$ and

$$
V^*(1)=\operatorname{Hom}_E(V,E)(1).
$$

After tensoring finite-level duality and using finite generation, one obtains perfect $E$-bilinear pairings

$$
H_c^i(G_{K,S},V)\times
H^{3-i}(G_{K,S},V^*(1))\longrightarrow E. \tag{7.5}
$$

The target $E$ is obtained by extending the $\mathbf Q_\ell$-valued invariant to $E$; the character $\psi_E$ chosen above is needed only when comparing integral pairings with Pontryagin duality. All cohomology groups in the relevant range are finite-dimensional $E$-spaces, so algebraic and continuous duals coincide.

Integral information is nevertheless lost. Two lattice local conditions of different finite index may span the same $E$-subspace. Therefore a vector-space dimension formula cannot recover the precise order formula for lattices or finite quotients.

### 7.4 Where products and closures enter

For finite $S$, a product over $S$ causes no topological problem. Over all places, however, the local lattice groups form restricted products, and local torsion groups may be discrete direct limits. A global localization image is to be compared with a **closed** annihilator. At finite level closedness is automatic; at lattice level it follows from finite generation and continuity in the standard setting.

This yields a safe rule. Prove the desired orthogonality and exactness for $T/\varpi^mT$, verify compatible cartesian local conditions, then pass to the inverse/direct limit while checking closure. Starting with an abstract infinite direct product and taking an algebraic dual produces many discontinuous characters and gives the wrong sequence.

### 7.5 Why the limit comparison is exact

The phrase “under the standard Mittag--Leffler hypotheses” in (7.4) can be made precise in the present setting. Let

$$
T_m=T/\varpi^mT,\qquad
A_m=D(T)[\varpi^m].
$$

For every fixed $i$, the groups $H^i(G_{K,S},T_m)$, $H_c^i(G_{K,S},T_m)$, and their local analogues are finite. In an inverse system of finite groups, the images in any fixed level form a descending chain of subgroups and therefore stabilize. Hence these systems satisfy the Mittag--Leffler condition even when the transition maps themselves are not surjective.

For continuous cohomology with compact coefficients there is a short exact comparison

$$
0\longrightarrow
\varprojlim_m{}^1 H^{i-1}(G_{K,S},T_m)
\longrightarrow H^i(G_{K,S},T)
\longrightarrow\varprojlim_m H^i(G_{K,S},T_m)
\longrightarrow0. \tag{7.6}
$$

The first term vanishes by the preceding stabilization. The same argument works place by place and for the finite direct sum over $S$. Taking cones commutes with the inverse limit because the degreewise systems are Mittag--Leffler, so

$$
H_c^i(G_{K,S},T)\simeq
\varprojlim_m H_c^i(G_{K,S},T_m). \tag{7.7}
$$

On the discrete side, every continuous cochain with values in $D(T)$ has finite image on compact subsets and lands in some $A_m$. Filtered colimits are exact, giving

$$
H^j(G_{K,S},D(T))\simeq
\varinjlim_m H^j(G_{K,S},A_m). \tag{7.8}
$$

Pontryagin duality exchanges the direct limit on the right of (7.8) with the inverse limit of the finite duals. Combining (7.7), (7.8), and finite-level duality proves (7.4) without an unexamined limit step.

The same proof applies with the roles reversed. If $A$ is a discrete cofinitely generated $\mathcal O$-module, put

$$
D(A)=\operatorname{Hom}_{\mathrm{cont}}(A,E/\mathcal O)(1),
$$

with the compact topology and with the same conductor-one additive character used to compare with the canonical Pontryagin dual. Then

$$
H_c^i(G_{K,S},A)\simeq
H^{3-i}(G_{K,S},D(A))^D. \tag{7.9}
$$

If $A=V/T$, its compact partner is the actual dual lattice $T^*(1)=\operatorname{Hom}_{\mathcal O}(T,\mathcal O)(1)$, after incorporating the inverse different into the scalar character. A merely commensurable lattice gives a pairing with a finite-index defect; it is not an exact integral dual.

### 7.6 The topological exact sequence

Substituting (7.4) into the localization long exact sequence gives the compact--discrete analogue of (6.1):

$$
\begin{aligned}
0\to{}&H^0(K,T)\to P_S^0(T)\to H^2(K,D(T))^D\\
\to{}&H^1(K,T)\to P_S^1(T)\to H^1(K,D(T))^D\\
\to{}&H^2(K,T)\to P_S^2(T)\to H^0(K,D(T))^D\to0.
\end{aligned} \tag{7.10}
$$

All global groups here mean restricted-ramification cohomology. The local packages use continuous cohomology with the compact coefficient $T$ and complete real complexes when $\ell=2$. The sequence is exact in the category of locally compact $\mathcal O$-modules: every arrow is continuous, every displayed image is closed, and quotient topologies agree with the subspace topology on the next kernel.

Closedness can be proved rather than assumed. Each image is the inverse limit of images between finite groups. The inverse limit is compact, its target is Hausdorff, and a compact image in a Hausdorff group is closed. On the discrete dual side every subgroup is closed. This argument also explains why a finite controlling set is convenient; an all-places restricted product requires a separate local-compactness check.

There is a companion sequence with $A$ discrete and $D(A)$ compact. It has the same shape, with the two coefficient objects exchanged and every Pontryagin-dual arrow reversed. One should not obtain it by erasing the superscript $D$ in (7.10): compact and discrete topologies are part of the statement.

The annihilator identity survives unchanged in form. For $i=0,1,2$,

$$
\overline{\operatorname{im}\bigl(H^i(K,T)\to P_S^i(T)\bigr)}^\perp
=\operatorname{im}\bigl(H^{2-i}(K,D(T))\to P_S^{2-i}(D(T))\bigr). \tag{7.11}
$$

The bar is redundant in the finite-$S$ lattice setting by the preceding closedness proof, but it records the correct general principle.

### 7.7 Rationalization and the vector-space sequence

Let $V=T\otimes_{\mathcal O}E$. Finite generation gives

$$
H^i(K,T)\otimes_{\mathcal O}E\simeq H^i(K,V),
\qquad
H_c^i(K,T)\otimes_{\mathcal O}E\simeq H_c^i(K,V), \tag{7.12}
$$

and likewise locally. The first assertion follows from the long sequence of $0\to T\to V\to V/T\to0$ after observing that the divisible parts become zero on tensoring with $E$; equivalently it follows from continuous cochains and flatness once finite generation is known. The cone description then proves the compact-support assertion.

The compatible finite traces give

$$
\operatorname{tr}_{K,S}:H_c^3(K,E(1))\xrightarrow{\sim}E. \tag{7.13}
$$

Cup product followed by this trace yields the perfect pairing (7.5). Its associated exact sequence is

$$
\begin{aligned}
0\to{}&H^0(K,V)\to P_S^0(V)\to H^2(K,V^*(1))^*\\
\to{}&H^1(K,V)\to P_S^1(V)\to H^1(K,V^*(1))^*\\
\to{}&H^2(K,V)\to P_S^2(V)\to H^0(K,V^*(1))^*\to0,
\end{aligned} \tag{7.14}
$$

where $^*$ now means the algebraic $E$-linear dual. Every group is finite-dimensional, so algebraic and continuous linear duals agree. At an archimedean place the modified groups vanish because $2$ is invertible in $E$, but ordinary degree-zero invariants will still contribute to the Euler and Selmer dimension formulas.

Rationalization loses finite index. If $L_T\subset H^1(K_v,T)$ is not saturated, then $L_T\otimes E$ is unchanged after replacing $L_T$ by its saturation. Thus (7.14) sees dimensions and exact rational orthogonals, while (7.10) remembers integral indices and torsion.

### 7.8 Infinite-level Selmer conditions

A lattice local condition is a closed submodule

$$
\mathcal L_v(T)\subseteq H^1(K_v,T).
$$

Its exact orthogonal is a subgroup of $H^1(K_v,D(T))$. If the conditions are obtained from cartesian finite-level conditions, then

$$
\mathcal L_v(T)=\varprojlim_m\mathcal L_v(T_m),
\qquad
\mathcal L_v(T)^\perp=\varinjlim_m\mathcal L_v(T_m)^\perp. \tag{7.15}
$$

The corresponding Selmer groups commute with these limits because finite products, kernels, and the Mittag--Leffler systems above are exact. Global duality therefore gives the same orthogonality and comparison sequences as at finite level, interpreted topologically.

For a discrete quotient $A=V/T$, the condition propagated from an $E$-subspace $\mathcal L_v(V)$ is normally the image of $\mathcal L_v(V)$ in $H^1(K_v,A)$; for the lattice it is the preimage of $\mathcal L_v(V)$. If $\mathcal L_v(V)$ and $\mathcal L_v(V^*(1))$ are exact orthogonals, boundary adjointness in the coefficient triples gives

$$
\mathcal L_v(T)^\perp=\mathcal L_v(D(T)),
\qquad
\mathcal L_v(A)^\perp=\mathcal L_v(T^*(1)). \tag{7.16}
$$

These equalities can fail for raw reduction of a nonsaturated integral condition. A simple warning is an unramified rank-one lattice on which Frobenius acts by $\alpha\ne1$ but $\alpha\equiv1\pmod\varpi$. The rational unramified group can vanish while the integral quotient $T/(\alpha-1)T$ is nonzero. Propagation by image and preimage keeps this finite congruence in the correct coefficient category.

## 8. Selmer structures under global duality

### 8.1 Orthogonal local permissions

Let $\mathcal L=(\mathcal L_v)_{v\in S}$ be a Selmer structure on $M$, with

$$
\mathcal L_v\subseteq\widetilde H^1(K_v,M).
$$

At real places this is ordinary $H^1$, since modified and ordinary degree one agree. Define the exact annihilator

$$
\mathcal L_v^\perp=
\{y\in\widetilde H^1(K_v,M'):
\langle x,y\rangle_v=0\text{ for every }x\in\mathcal L_v\}. \tag{8.1}
$$

Local perfectness gives

$$
|\mathcal L_v|\,|\mathcal L_v^\perp|
=|\widetilde H^1(K_v,M)|, \tag{8.2}
$$

but (8.1), not (8.2), is the definition. Equality of orders cannot determine which subgroup is orthogonal.

Write

$$
H^1_{\mathcal L}(K,M)=
\ker\left(H^1(G_{K,S},M)\to
\bigoplus_{v\in S}\widetilde H^1(K_v,M)/\mathcal L_v\right), \tag{8.3}
$$

and define $H^1_{\mathcal L^\perp}(K,M')$ similarly. Outside $S$ both structures are unramified; under our hypotheses the unramified subgroups are exact orthogonals.

### 8.2 The Selmer Poitou--Tate sequence

Set

$$
Q_{\mathcal L}(M)=
\bigoplus_{v\in S}\widetilde H^1(K_v,M)/\mathcal L_v. \tag{8.4}
$$

There is an exact sequence

$$
\begin{aligned}
0\to{}&H^1_{\mathcal L}(K,M)
\to H^1(G_{K,S},M)
\xrightarrow{\lambda_{\mathcal L}}Q_{\mathcal L}(M)\\
\xrightarrow{\theta_{\mathcal L}}{}&
H^1_{\mathcal L^\perp}(K,M')^D
\xrightarrow{\delta_{\mathcal L}}H^2(G_{K,S},M)
\xrightarrow{\operatorname{loc}}P_S^2(M)\\
\to{}&H^0(G_{K,S},M')^D\to0.
\end{aligned} \tag{8.5}
$$

Every map has a direct description. The first two come from the definition of the Selmer kernel. For $\bar x=(x_v+\mathcal L_v)$,

$$
\theta_{\mathcal L}(\bar x)(y)
=\sum_{v\in S}\langle x_v,\operatorname{loc}_v y\rangle_v. \tag{8.6}
$$

This is well defined because $\operatorname{loc}_v y\in\mathcal L_v^\perp$. To define $\delta_{\mathcal L}$, extend a character of the subgroup $H^1_{\mathcal L^\perp}(K,M')$ to $H^1(G_{K,S},M')$; divisibility of $\mathbf Q/\mathbf Z$ makes extension possible. Apply the map from $H^1(G_{K,S},M')^D$ to $H^2(G_{K,S},M)$ in (6.1). Two extensions differ by a character annihilating the dual Selmer group, which local perfectness identifies with a character coming from the local subgroups $\mathcal L_v$; exactness of (6.1) kills that difference. Thus $\delta_{\mathcal L}$ is canonical.

The tail of (8.5) is sometimes unnecessary in applications, but suppressing it can conceal an $H^2$ obstruction. In particular $\theta_{\mathcal L}$ need not be surjective.

### 8.3 Exact orthogonality of the localization defect

The most frequently used part of (8.5) is

$$
\operatorname{coker}(\lambda_{\mathcal L})
\simeq
\ker\left(
H^1_{\mathcal L^\perp}(K,M')^D
\to H^2(G_{K,S},M)
\right). \tag{8.7}
$$

Thus the dual Selmer group controls the failure of localization to fill the allowed quotient, but the cokernel is only the subgroup of its dual killed by $\delta_{\mathcal L}$. It is incorrect in general to identify the whole dual Selmer dual with the localization cokernel.

There is also an exact annihilator formulation. Pair $Q_{\mathcal L}(M)$ perfectly with

$$
\bigoplus_{v\in S}\mathcal L_v^\perp
$$

using local duality. Then

$$
\operatorname{im}(\lambda_{\mathcal L})^\perp
=\operatorname{im}\left(
H^1_{\mathcal L^\perp}(K,M')
\to\bigoplus_{v\in S}\mathcal L_v^\perp
\right). \tag{8.8}
$$

This identifies a subgroup, not merely its order. It says precisely which linear tests cut out the global localization image.

### 8.4 Comparing two Selmer structures

Suppose $\mathcal L_v\subseteq\mathcal L'_v$ for every $v$. Then $(\mathcal L'_v)^\perp\subseteq\mathcal L_v^\perp$. Put

$$
\Delta_v=\mathcal L'_v/\mathcal L_v.
$$

A diagram chase using (8.5) gives the exact comparison sequence

$$
\begin{aligned}
0\to{}&H^1_{\mathcal L}(K,M)
\to H^1_{\mathcal L'}(K,M)
\to\bigoplus_{v\in S}\Delta_v\\
\to{}&H^1_{\mathcal L^\perp}(K,M')^D
\to H^1_{(\mathcal L')^\perp}(K,M')^D
\to0.
\end{aligned} \tag{8.9}
$$

The middle map sends a local relaxation class to its pairing functional on the stricter dual Selmer group. Exactness at $\bigoplus\Delta_v$ says that a collection of newly permitted local directions globalizes exactly when it annihilates every class in the old dual Selmer group that remains locally invisible under the relaxed dual conditions.

Taking orders in (8.9) gives

$$
\frac{|H^1_{\mathcal L'}(K,M)|}{|H^1_{\mathcal L}(K,M)|}
\cdot
\frac{|H^1_{(\mathcal L')^\perp}(K,M')|}
{|H^1_{\mathcal L^\perp}(K,M')|}
=\prod_{v\in S}\frac{|\mathcal L'_v|}{|\mathcal L_v|}. \tag{8.10}
$$

The first ratio alone need not equal the local product; the dual Selmer ratio is the correction.

### 8.5 What is perfect and what is not

The notation “dual Selmer group” can suggest a perfect pairing

$$
H^1_{\mathcal L}(K,M)\times
H^1_{\mathcal L^\perp}(K,M')\longrightarrow\mathbf Q/\mathbf Z.
$$

There is no such pairing in general. If both entries are global, reciprocity makes the sum of their local pairings zero; the most obvious proposed pairing is identically zero. The word “dual” refers to the local conditions and to their complementary roles in the exact sequence, not to a direct perfect pairing between the two degree-one kernels.

Three perfect pairings do occur, and they should not be conflated.

First, each full local group $H^1(K_v,M)$ pairs perfectly with $H^1(K_v,M')$. Second, the quotient $H^1(K_v,M)/\mathcal L_v$ pairs perfectly with $\mathcal L_v^\perp$. Third, the local--global kernels $\Sha_S^1(K,M)$ and $\Sha_S^2(K,M')$ pair perfectly by (6.8). The Selmer sequence is assembled from the first two; the third comes from quotienting compact-support duality.

There is nevertheless an exact dual relation attached to a Selmer structure. Put

$$
D_{\mathcal L}(M)=
\operatorname{coker}\left(
H^1(G_{K,S},M)\longrightarrow Q_{\mathcal L}(M)
\right).
$$

Then (8.7) identifies

$$
D_{\mathcal L}(M)^D
\simeq
\operatorname{coker}\left(
\Sha_S^1(K,M')\longrightarrow
H^1_{\mathcal L^\perp}(K,M')
\right). \tag{8.11}
$$

Indeed the kernel of the map from the dual Selmer dual to $H^2(K,M)$ is dual to the quotient of the dual Selmer group by those classes that are locally zero everywhere; those locally zero classes are exactly $\Sha_S^1(K,M')$. Thus the localization defect is perfectly paired with the dual Selmer classes modulo the everywhere locally trivial ones. This is the precise replacement for the nonexistent direct pairing of the two Selmer groups.

**Counterexample to direct perfectness.** Take every primal condition to be relaxed. Then $H^1_{\mathcal L}(K,M)=H^1(G_{K,S},M)$, while every dual condition is strict, so the dual Selmer group is $\Sha_S^1(K,M')$. Their orders are generally different, and the reciprocity sum on the two global groups is zero. No perfect pairing between them can exist unless special accidental equalities hold.

## 9. Euler characteristics and the numerical formula

### 9.1 The global Euler characteristic

Let $r_1$ and $r_2$ be the numbers of real and complex places of $K$. When $M$ has odd order, or when $K$ is totally imaginary, ordinary global cohomology has no real 2-primary tail and

$$
\chi(G_{K,S},M)
=\frac{|H^0(G_{K,S},M)|\,|H^2(G_{K,S},M)|}
{|H^1(G_{K,S},M)|}. \tag{9.1}
$$

The global Euler characteristic formula is

$$
\chi(G_{K,S},M)
=\frac{\displaystyle\prod_{v\text{ real}}|H^0(K_v,M)|}
{|M|^{r_1+r_2}}. \tag{9.2}
$$

Every archimedean correction is visible: a complex place contributes $|M|^{-1}$, while a real place contributes $|H^0(K_v,M)|/|M|$. The right side is independent of $S$ once $S$ satisfies the standing hypotheses.

**Proof.** It is enough to work one prime $\ell$ at a time, because cohomology and both sides split into primary parts. For an $\ell$-primary module define the additive Euler exponent

$$
e_{K,S}(M)=
\sum_{i=0}^2(-1)^i\operatorname{length}_{\mathbf Z_\ell}
H^i(G_{K,S},M)
-\sum_{v\text{ real}}\operatorname{length}_{\mathbf Z_\ell}H^0(K_v,M)
+(r_1+r_2)\operatorname{length}_{\mathbf Z_\ell}M. \tag{9.2a}
$$

In the real $2$-primary case the first sum means the finite determinant obtained after cancelling the periodic tails. Long exact coefficient sequences show that $e_{K,S}$ is additive in short exact sequences.

Two elementary reductions determine this additive function. First, if $L/K$ is finite inside the maximal extension unramified outside $S$ and $S_L$ is the set above $S$, the finite-index Euler characteristic identity gives

$$
e_{L,S_L}(M)=[L:K]\,e_{K,S}(M). \tag{9.2b}
$$

To prove it, choose coset representatives for $G_{L,S_L}$ in $G_{K,S}$ and filter the induced cochain resolution by those representatives. Every global term occurs $[L:K]$ times. Grouping the infinite places above a fixed infinite place gives the same factor in the archimedean correction; a real place that becomes complex contributes through the complete real complex before cancellation. Thus the equality holds also in the modified case.

Second, after a finite extension $L/K$ inside the same restricted extension, every simple constituent of $M$ becomes trivial and $\mu_\ell\subset L$. Additivity reduces the calculation over $L$ to $\mathbf Z/\ell\mathbf Z$, identified with $\mu_\ell$ after choosing a root of unity. Kummer theory gives

$$
0\longrightarrow
\mathcal O_{L,S_L}^\times/
\mathcal O_{L,S_L}^{\times\ell}
\longrightarrow H^1(G_{L,S_L},\mu_\ell)
\longrightarrow\operatorname{Cl}(\mathcal O_{L,S_L})[\ell]
\longrightarrow0. \tag{9.2c}
$$

The degree-two Kummer sequence contains the quotient
$\operatorname{Cl}(\mathcal O_{L,S_L})/\ell$ and the $\ell$-torsion Brauer term. The class-group kernel and quotient have the same order, so they cancel in the alternating product. The finite-place valuation directions in the $S_L$-unit group cancel the finite local Brauer directions. Dirichlet's unit theorem leaves rank $r_1(L)+r_2(L)-1$, the roots of unity supply the missing degree-zero factor, and the sum-of-invariants relation removes one Brauer factor. What remains is

$$
\chi(G_{L,S_L},\mathbf Z/\ell\mathbf Z)
=\ell^{-r_2(L)}
$$

when the coefficient is trivial at every real place, exactly the right side of (9.2). The same calculation with complete real groups gives the modified determinant at $\ell=2$.

Thus $e_{L,S_L}(M)=0$. Equation (9.2b) gives $[L:K]e_{K,S}(M)=0$, and the exponent is an integer, so $e_{K,S}(M)=0$. Exponentiating proves (9.2). This argument also proves independence of $S$: adding a finite place adds one unit valuation direction and one local Brauer direction, which cancel. $\square$

If $M$ has 2-primary torsion and $K$ has real places, ordinary cohomology has a two-periodic tail and an infinite alternating product is meaningless. In this case define the **modified Euler determinant** by taking the localization triangle with complete real Tate complexes and cancelling the restriction isomorphisms (5.7) in the two periodic tails. The remaining finite determinant is exactly the right side of (9.2). Thus (9.2) is still the precise modified determinant formula, but its left side is not the three-term ratio (9.1). In applications, the order formula below is the safest low-degree expression of this determinant and remains valid with modified local groups.

For a $k$-vector space $M$ of dimension $m$, away from the real 2-primary exception, (9.2) becomes

$$
h^0-h^1+h^2
=\sum_{v\text{ real}}\dim_k H^0(K_v,M)
-(r_1+r_2)m. \tag{9.3}
$$

The common abbreviation $-r_2m$ is valid only when every real complex conjugation acts trivially on $M$.

### 9.2 The Greenberg--Wiles order formula

The numerical consequence used most often is

$$
\boxed{
\frac{|H^1_{\mathcal L}(K,M)|}
{|H^1_{\mathcal L^\perp}(K,M')|}
=
\frac{|H^0(G_{K,S},M)|}
{|H^0(G_{K,S},M')|}
\prod_{v\in S}
\frac{|\mathcal L_v|}{|H^0(K_v,M)|}.}
\tag{9.4}
$$

At real places $H^0(K_v,M)$ in the denominator is ordinary invariants, while $\mathcal L_v\subseteq H^1(K_v,M)=\widehat H^1(K_v,M)$. At a complex place $\mathcal L_v=0$ and $|H^0(K_v,M)|=|M|$, so the complex correction is not zero. These are the archimedean terms most often lost in a compressed formula.

To derive (9.4), take alternating orders in (8.5), use local perfectness (8.2), and eliminate the degree-two terms with the final three arrows of (6.1). The remaining global degree-zero factors have opposite coefficients because dualization reverses exact sequences. Applying the local Euler characteristic at finite places and the modified real calculation simplifies the expression to (9.4). Thus the formula is a consequence of exactness and perfect pairings, not an independent counting coincidence.

### 9.3 Finite coefficient fields

Suppose $M$ is a finite-dimensional vector space over a finite field $k$, all local conditions are $k$-subspaces, and $M'=M^*(1)$. Taking $\log_{|k|}$ of (9.4) gives

$$
\boxed{
\begin{aligned}
\dim_k H^1_{\mathcal L}(K,M)
-\dim_k H^1_{\mathcal L^\perp}(K,M^*(1))
={}&\dim_k H^0(K,M)-\dim_k H^0(K,M^*(1))\\
&+\sum_{v\in S}
\left(\dim_k\mathcal L_v-\dim_kH^0(K_v,M)\right).
\end{aligned}}
\tag{9.5}
$$

Formula (9.5) is the deformation-theoretic dimension formula. It compares a global tangent space with its dual obstruction space using only invariants and local tangent dimensions.

**Worked check over $\mathbf Q$.** Let $k$ have odd characteristic and let $M=k$ be trivial. Take $S=\{\ell,\infty\}$ and the relaxed condition at $\ell$. Then

$$
\dim H^1(\mathbf Q_\ell,k)=2,\qquad
\dim H^0(\mathbf Q_\ell,k)=1.
$$

At infinity, $H^1(\mathbf R,k)=0$ but $H^0(\mathbf R,k)=k$, contributing $-1$. Globally $H^0(\mathbf Q,k)$ contributes $+1$, and $H^0(\mathbf Q,k^*(1))=0$. The right side is $1+(2-1)+(0-1)=1$. Omitting infinity would give the wrong answer by one.

### 9.4 Self-dual modules and parity cautions

Suppose a perfect $G_K$-equivariant pairing identifies

$$
M\simeq M^*(1).
$$

If every $\mathcal L_v$ is its own exact orthogonal, then the two Selmer groups in (9.5) are the same group, and the right side must vanish. This is a useful consistency check on local dimension calculations.

It does not by itself imply that the common dimension is even. Parity requires an additional alternating global pairing on the Selmer group and control of its radical. In characteristic two, alternating and skew-symmetric are not equivalent, real Tate terms can contribute, and scalar submodules can make a trace pairing degenerate on a trace-zero adjoint. Self-duality is therefore a relation of coefficient modules, not an automatic parity theorem.

### 9.5 A detailed derivation of the dimension formula

Because (9.5) is used repeatedly, we record the bookkeeping rather than asking the reader to trust cancellation. Write

$$
h^i(M)=\dim_kH^i(G_{K,S},M),
\qquad \widetilde h_v^i(M)=\dim_k\widetilde H^i(K_v,M),
$$

and put $h_v^0(M)=\dim_kH^0(K_v,M)$ for ordinary local invariants and $l_v=\dim_k\mathcal L_v$. Exact local duality gives

$$
\widetilde h_v^1(M')=\widetilde h_v^1(M),
\qquad
\dim\mathcal L_v^\perp=\widetilde h_v^1(M)-l_v. \tag{9.6}
$$

Take dimensions in the first five terms of (8.5). If $c$ denotes the dimension of the image of $\delta_{\mathcal L}$, exactness gives

$$
h^1_{\mathcal L}(M)-h^1(M)
+\sum_v(\widetilde h_v^1(M)-l_v)
-h^1_{\mathcal L^\perp}(M')+c=0. \tag{9.7}
$$

The tail of (8.5) gives

$$
c-h^2(M)+\sum_v\widetilde h_v^2(M)-h^0(M')=0. \tag{9.8}
$$

Substitute (9.8) into (9.7):

$$
\begin{aligned}
h^1_{\mathcal L}(M)-h^1_{\mathcal L^\perp}(M')
={}&h^1(M)-h^2(M)-h^0(M')\\
&-\sum_v\widetilde h_v^1(M)+\sum_vl_v+\sum_v\widetilde h_v^2(M).
\end{aligned} \tag{9.9}
$$

At each finite place, local duality identifies $\widetilde h_v^2(M)$ with ordinary $h_v^0(M')$, while the local Euler formula controls $h_v^0(M)-\widetilde h_v^1(M)+\widetilde h_v^2(M)$. If there is no real 2-primary exception, insert (9.3) for the global combination in (9.9). The coefficient-characteristic contributions $[K_v:\mathbf Q_\ell]\dim M$ sum to $[K:\mathbf Q]\dim M$ and cancel the corresponding global term. At a real place the local contribution becomes $-h_v^0(M)$, and at a complex place it becomes $-\dim M=-h_v^0(M)$.

In the real 2-primary case one must instead use the modified Euler determinant of Section 9.1. Truncate the localization triangle in a high degree and cancel the global and real Tate terms through the restriction isomorphisms (5.7); the two-periodic tail then contributes zero to the finite determinant. The remaining low-degree equality is exactly the replacement for (9.3) needed in (9.9), with the real contribution again equal to $-h_v^0(M)$. This does not assert a three-term ordinary Euler formula in the exceptional case. In either case, what survives is

$$
h^0(M)-h^0(M')+\sum_v(l_v-h_v^0(M)),
$$

which is exactly (9.5).

This calculation also explains why $H^2$ must not be dropped prematurely. It cancels only after the tail of the exact sequence and the Euler formulas have been used. Assuming $H^2=0$ without proof can accidentally produce the correct-looking answer in one example while losing the global invariant or an archimedean term in another.

### 9.6 Lattices, torsion modules, and rational dimensions

Let $T$ be a finite free $\mathcal O$-module, let $V=T\otimes E$, and suppose local conditions are propagated compatibly through $T$, $V$, and $A=V/T$. Since an order is not defined for an infinite compact or cofinitely generated group, there are three different numerical statements.

First, the finite formula (9.4) applies without change to every quotient $T/\varpi^mT$. It records exact integral indices, including bounded torsion. If the local conditions are cartesian, these formulas are compatible in $m$.

Second, after tensoring with $E$, the Euler formula is

$$
\sum_{i=0}^2(-1)^i\dim_E H^i(G_{K,S},V)
=\sum_{v\text{ real}}\dim_E H^0(K_v,V)
-(r_1+r_2)\dim_E V. \tag{9.10}
$$

There is no real periodic exception here because $2$ is invertible in $E$. Complex places contribute $-\dim_E V$ through the second term, even though their modified local cohomology groups vanish.

Third, for $E$-subspace conditions $\mathcal L_v(V)$ and their exact orthogonals,

$$
\begin{aligned}
\dim_E H^1_{\mathcal L}(K,V)
-\dim_E H^1_{\mathcal L^\perp}(K,V^*(1))
={}&\dim_EH^0(K,V)-\dim_EH^0(K,V^*(1))\\
&+\sum_{v\in S}
\left(\dim_E\mathcal L_v(V)-\dim_EH^0(K_v,V)\right).
\end{aligned} \tag{9.11}
$$

This follows either by repeating the argument of Section 9.5 with (7.14), or by dividing the finite-level length formula by $m$ and taking the stable leading coefficient. The latter method shows exactly what is discarded: bounded kernels and cokernels contribute $O(1)$ to the length, whereas free ranks contribute a term linear in $m$.

For $A=V/T$, the meaningful invariant is $\mathcal O$-corank. Under propagated conditions and finite-cotorsion hypotheses, its corank is the dimension of the corresponding $V$-Selmer group, up to the contribution of divisible classes arising from adjacent $H^0$ terms in the coefficient sequence. One must inspect those terms before writing an equality. This is why a rational dimension formula is safer than declaring that every torsion Selmer group has the same corank as a chosen lattice group has rank.

**Counterexample to recovering integral data rationally.** Replace a saturated line $L\subset H^1(K_v,T)$ by $\varpi L$. Both span the same subspace of $H^1(K_v,V)$, so (9.11) cannot distinguish them. At finite level their indices differ by $|k|$, and (9.4) detects the discrepancy. Rational and integral numerical formulas answer different questions.

## 10. A calculus of local conditions

### 10.1 Strict, relaxed, and unramified conditions

At a place $v$, the strict condition is $0$ and the relaxed condition is all of $H^1(K_v,M)$. Local perfectness gives

$$
0^\perp=H^1(K_v,M'),
\qquad
H^1(K_v,M)^\perp=0. \tag{10.1}
$$

Thus relaxing a primal condition makes the dual condition strict.

If $v\nmid n$, both $M$ and $M'$ are unramified, then

$$
H^1_{\mathrm{ur}}(K_v,M)^\perp
=H^1_{\mathrm{ur}}(K_v,M'). \tag{10.2}
$$

The proof separates containment from size. The cup product of two unramified classes inflates from the residue-field Galois group, whose cohomological dimension for these coefficients is one; their degree-two product is therefore zero. Thus the right side lies in the orthogonal. On the other hand,

$$
H^1_{\mathrm{ur}}(K_v,M)\simeq
M/(\operatorname{Frob}_v-1)M
$$

has order $|H^0(K_v,M)|$. The prime-to-$n$ local Euler formula and local duality show that the orthogonal has order $|H^0(K_v,M')|$, exactly the order of $H^1_{\mathrm{ur}}(K_v,M')$. Containment and equal order prove (10.2).

This fails without the hypotheses. For a concrete coefficient-characteristic example, let $K_v$ contain $\mu_p$ and take $M=\mathbf F_p$ with trivial action. The unramified line in $H^1(K_v,\mathbf F_p)$ consists of characters factoring through residue Frobenius. Under the Kummer identification

$$
H^1(K_v,\mu_p)\simeq K_v^\times/K_v^{\times p},
$$

its annihilator is the image of $\mathcal O_v^\times$, because an unramified character is determined by its value on a uniformizer and vanishes on units. This unit subgroup has dimension $[K_v:\mathbf Q_p]+1$, whereas the unramified Kummer subgroup is only one-dimensional. Thus the orthogonal contains many ramified unit directions. At a ramified module, the Frobenius calculation must moreover use inertia invariants and need not be self-complementary.

### 10.2 Enlarging the controlling set

Let $S\subseteq S'$ satisfy the standing conditions, and suppose $M$ is already unramified outside $S$. Inflation gives

$$
H^1(G_{K,S},M)\hookrightarrow H^1(G_{K,S'},M).
$$

Its image consists exactly of classes whose localization at every $v\in S'\setminus S$ is unramified. Hence a Selmer problem is unchanged by enlarging $S$ and imposing $H^1_{\mathrm{ur}}$ at each new place. The dual problem is unchanged as well by (10.2).

The point is not merely notational. Enlarging $S$ replaces a global ramification prohibition by an explicit local condition. Exactness asserts that these two constructions have the same kernel.

### 10.3 Adding and removing one condition

Suppose $\mathcal L$ and $\mathcal L'$ differ only at $w$, with $\mathcal L_w\subseteq\mathcal L'_w$. Then (8.9) becomes

$$
0\to H^1_{\mathcal L}
\to H^1_{\mathcal L'}
\to\mathcal L'_w/\mathcal L_w
\to H^1_{\mathcal L^\perp}(M')^D
\to H^1_{(\mathcal L')^\perp}(M')^D\to0. \tag{10.3}
$$

Over a finite field,

$$
\begin{aligned}
&\dim H^1_{\mathcal L'}-\dim H^1_{\mathcal L}
+\dim H^1_{(\mathcal L')^\perp}-\dim H^1_{\mathcal L^\perp}\\
&\hspace{35mm}=\dim\mathcal L'_w-\dim\mathcal L_w.
\end{aligned} \tag{10.4}
$$

If the local quotient is one-dimensional, either the primal Selmer dimension rises by one, or the dual Selmer dimension falls by one, with intermediate behavior determined by the localization map. This exact alternative is the numerical heart of auxiliary-prime arguments.

### 10.4 A counterexample to naive dimension subtraction

Suppose $\mathcal L_w=0$ and $\mathcal L'_w$ is a one-dimensional line. It is false that the larger Selmer group must gain one dimension. If every global class localizes to zero at $w$, the map

$$
H^1_{\mathcal L'}\to\mathcal L'_w
$$

can be zero, so the primal Selmer groups are equal. Exactness then forces the dual Selmer group to lose one dimension instead. Conversely, if a global class fills the new line, the primal dimension grows and the dual need not change.

The local dimension measures available room; the global localization image decides who uses it. Formula (10.4) keeps both effects and is therefore stronger than subtracting codimensions by hand.

## 11. Restriction, corestriction, and extension of fields

### 11.1 Adjointness place by place

Let $L/K$ be finite, and let $w\mid v$. Local restriction and corestriction satisfy

$$
\langle\operatorname{res}_{w/v}x,y\rangle_w
=\langle x,\operatorname{cor}_{w/v}y\rangle_v. \tag{11.1}
$$

This follows from the projection formula for cup products and the normalization

$$
\operatorname{inv}_v(\operatorname{cor}_{w/v}z)=\operatorname{inv}_w(z).
$$

For a fixed $v$, restriction produces a tuple over all $w\mid v$, while corestriction back to $K_v$ is the sum of the local corestrictions. Omitting that sum breaks (11.1) globally.

At a real place that becomes complex, the target modified local cohomology is zero. Corestriction from the complex place is correspondingly zero, and the complete-resolution comparison retains compatibility at 2-primary coefficients.

### 11.2 Compatibility of global duality

Global restriction and corestriction are adjoint under compact-support duality:

$$
\langle\operatorname{res}_{L/K}x,y\rangle_L
=\langle x,\operatorname{cor}_{L/K}y\rangle_K. \tag{11.2}
$$

Here $x\in H_c^i(K,M)$ and $y\in H^{3-i}(L,M')$, with coefficients restricted to $G_L$ on the left. To prove the formula, expand the left side into local invariants, group the places $w$ above each $v$, use (11.1), and then use the global projection formula. The fundamental classes are compatible under restriction and corestriction, so the null-homotopies used in Section 4 match.

Consequently every square in the finite-$S$ exact sequence commutes with the appropriate restriction or corestriction arrow. On dual terms the direction reverses. For example, restriction on $H^1(K,M')$ dualizes to a map

$$
H^1(L,M')^D\longrightarrow H^1(K,M')^D,
$$

which aligns with corestriction on the primal side.

### 11.3 Induced Selmer conditions and Shapiro

Shapiro identifies

$$
H^i(L,M)\simeq
H^i\bigl(K,\operatorname{Ind}_{G_L}^{G_K}M\bigr). \tag{11.3}
$$

Locally, the restriction of the induced module decomposes over all $w\mid v$. Therefore a Selmer condition over $L$ induces the direct sum of its conditions at those $w$, not a single arbitrarily chosen component. The Tate dual of an induced finite module is the induced Tate dual, and the induced local conditions remain exact orthogonals.

These compatibilities are sufficient for later deformation problems. They allow tangent and dual tangent spaces to be compared after finite base change, provided ramification sets are enlarged to contain the primes ramified in $L/K$ and every chosen local condition is transported over all places above it. No blanket equality of Selmer dimensions under restriction should be expected: kernels of restriction, inflation--restriction terms, and new local conditions can all contribute.

## 12. Arithmetic examples

### 12.1 Kummer theory and class groups

Assume $n$ is invertible outside $S$. Kummer theory gives

$$
H^1(G_{K,S},\mu_n)
\simeq
\{a\in K^\times:v(a)\equiv0\pmod n\text{ for }v\notin S\}/K^{\times n}. \tag{12.1}
$$

Imposing the unramified Kummer condition outside $S$ yields the exact sequence

$$
0\to\mathcal O_{K,S}^\times/\mathcal O_{K,S}^{\times n}
\to H^1(G_{K,S},\mu_n)
\to\operatorname{Cl}(\mathcal O_{K,S})[n]\to0. \tag{12.2}
$$

The dual module is $(\mu_n)'\simeq\mathbf Z/n\mathbf Z$. Its $H^1$ classes are cyclic characters. The dual Selmer condition says that the character annihilates the local Kummer subgroup under local reciprocity. Global duality identifies the failure of prescribed local $n$th-power classes to come from a global element with such global characters. Thus ideal-class obstructions and reciprocity characters are two descriptions of the same defect.

**Worked example over $\mathbf Q$.** Let $n=2$ and $S=\{2,\infty\}$. The restricted square classes are represented by $1,-1,2,-2$. At the real place, the sign class is nontrivial and the modified Tate group is $\mathbf Z/2\mathbf Z$. A local specification that demands a negative real sign while choosing incompatible $2$-adic Hilbert symbols is rejected by the sum of the two invariants. Ignoring the real term would incorrectly accept it.

### 12.2 The product formula as the first exact sequence

Take $M=\mu_n$ and pair with $M'=\mathbf Z/n\mathbf Z$. A local character $\chi_v$ corresponds by local reciprocity to a character of $K_v^\times$. Pairing a Kummer class $a_v$ with $\chi_v$ evaluates that character on $a_v$. If $a\in K^\times$ is global and $\chi$ is a global character, (4.2) becomes

$$
\sum_v\chi_v(a)=0\quad\text{in }\tfrac1n\mathbf Z/\mathbf Z, \tag{12.3}
$$

or multiplicatively, the product of the local character values is one. The middle exactness of (6.1) says that these reciprocity tests are complete.

For $n=2$, (12.3) is the Hilbert reciprocity law for quadratic Hilbert symbols. A quaternion algebra cannot ramify at exactly one place; it may ramify at any finite even set. This is both a concrete example of the annihilator theorem and a warning that the obstruction is global rather than attached to a distinguished completion.

### 12.3 Elliptic Selmer groups

Let $E/K$ be an elliptic curve and let $n$ be positive. The Weil pairing identifies

$$
E[n]'\simeq E[n]
$$

after using the principal polarization. At every place, the Kummer map

$$
E(K_v)/nE(K_v)\longrightarrow H^1(K_v,E[n])
$$

has image $\mathcal L_v$. Local Tate duality and the compatibility of the Weil pairing with connecting maps show

$$
\mathcal L_v^\perp=\mathcal L_v. \tag{12.4}
$$

The resulting Selmer group is $\operatorname{Sel}_n(E/K)$. Formula (8.8) says that the localization image of global $E[n]$-classes inside the quotients by local points is cut out exactly by global $E[n]$-classes satisfying the same Kummer conditions. This is the cohomological source of the Cassels-type dual obstruction.

The principal polarization does not imply that $|\operatorname{Sel}_n(E/K)|$ is a square. Rational $n$-torsion, divisible parts, and radicals of the induced pairing contribute. What duality guarantees here is exact self-orthogonality of local Kummer images and the global exact sequence; a perfect alternating pairing on a further quotient requires additional work.

The familiar exact sequence

$$
0\longrightarrow E(K)/nE(K)
\longrightarrow\operatorname{Sel}_n(E/K)
\longrightarrow\Sha(E/K)[n]\longrightarrow0 \tag{12.5}
$$

separates two sources of Selmer classes. The first consists of global points divided locally; the second consists of torsors that are locally soluble everywhere but not globally soluble. Poitou--Tate duality does not assert that $\Sha(E/K)$ vanishes. Rather, it organizes its finite-level duality and explains why the same local Kummer images occur on both sides.

### 12.4 Failure of an unrestricted local--global principle

Two counterexamples clarify the scope of the theorem. First, at infinitely many places where $M$ is unramified, choose a local class outside $H^1_{\mathrm{ur}}(K_v,M)$. Every coordinate is individually legitimate, but the resulting family is not in the restricted product. No global finite-coefficient cocycle can produce it, because a continuous cocycle has a finite splitting field and is ramified at only finitely many places. The restricted product in (6.5) is therefore forced by arithmetic.

Second, even a finite family can fail. Let $n=2$ and prescribe local Brauer invariants equal to $1/2$ at one place and zero everywhere else. Each coordinate is represented by a local quaternion algebra. There is no global quaternion algebra with these localizations, because the sum of invariants is $1/2$. Prescribing $1/2$ at a second place removes the reciprocity obstruction, and exactness of the Brauer sequence then produces a global class.

The two failures are different. The first violates the topology and ramification support required even to enter the global sequence. The second lies in the correct direct sum but fails the unique global reciprocity test. Once both requirements are met, perfectness says there is no third kind of obstruction.

### 12.5 A complete quadratic count over the rationals

Take $M=\mu_2=\mathbf Z/2\mathbf Z$ over $\mathbf Q$ and $S=\{2,\infty\}$. Restricted Kummer theory gives

$$
H^1(G_{\mathbf Q,S},\mu_2)
=\langle -1,2\rangle
\subset\mathbf Q^\times/\mathbf Q^{\times2},
$$

so the global group has four elements represented by $1,-1,2,-2$. Locally,

$$
|\mathbf Q_2^\times/\mathbf Q_2^{\times2}|=8,
\qquad
|\mathbf R^\times/\mathbf R^{\times2}|=2.
$$

Thus the degree-one local package has sixteen elements. The global localization map is injective: if one of the four global classes is a square both in $\mathbf Q_2$ and in $\mathbf R$, its $2$-adic valuation and sign force it to be the trivial class.

Local Hilbert pairings make the sixteen-element package self-dual. The image of the four-element global group has annihilator of order four. Reciprocity puts the image of the dual global group inside that annihilator, and the exact annihilator theorem says the inclusion is equality. Consequently a pair of local square classes $(a_2,a_\infty)$ comes from a restricted global square class exactly when

$$
(a_2,b)_2\,(a_\infty,b)_\infty=1
$$

for every $b\in\{1,-1,2,-2\}$. Three nontrivial tests are listed, but only two are independent because the testing group has dimension two. This small calculation displays the whole middle of the exact sequence: a four-element global image inside a sixteen-element local space, cut out by a four-element family of dual characters.

The real coordinate is decisive. For example, $(-1,-1)_\infty=-1$. Dropping the infinite place changes an actual Hilbert-symbol equation, not merely an Euler correction.

### 12.6 Why modified degree zero is smaller

Let $M=\mathbf Z/4\mathbf Z$ with trivial action at a real place. Ordinary invariants give

$$
H^0(\mathbf R,M)=\mathbf Z/4\mathbf Z,
$$

but the modified group is

$$
\widehat H^0(\mathbf R,M)
=M/(1+c)M=M/2M\simeq\mathbf Z/2\mathbf Z.
$$

Likewise

$$
\widehat H^1(\mathbf R,M)=M[2]\simeq\mathbf Z/2\mathbf Z.
$$

The real local pairing between these two groups is perfect and takes values in $\{0,1/2\}$. If ordinary $H^0$ were inserted into the left endpoint of (6.1), it would have twice the order of its proposed dual partner. No global argument could repair that local mismatch. This example is the quickest test that the archimedean modification has been applied in degree zero as well as in positive degrees.

## 13. Adjoint modules and deformation conditions

### 13.1 Fixed determinant and the trace-zero adjoint

Let $k$ be a finite field of characteristic $\ell$ and

$$
\bar\rho:G_{K,S}\to\operatorname{GL}(W)
$$

a continuous representation. Unrestricted first-order deformations are measured by $H^1(K,\operatorname{ad}(\bar\rho))$. With fixed determinant, the coefficient module is

$$
M=\operatorname{ad}^0(\bar\rho)
=\{X\in\operatorname{End}_k(W):\operatorname{tr}X=0\}. \tag{13.1}
$$

The trace pairing $\operatorname{tr}(XY)$ identifies the full adjoint with its linear dual. On $\operatorname{ad}^0$ it is perfect when $\ell\nmid\dim W$. If $\ell\mid\dim W$, scalar matrices lie in $\operatorname{ad}^0$ and form a radical; then the dual is a quotient of the full adjoint rather than automatically the same trace-zero module. This distinction must be settled before writing $M^*(1)\simeq M(1)$.

For the common two-dimensional case with $\ell\ne2$, the trace pairing is perfect on $\operatorname{ad}^0$, so

$$
M^*(1)\simeq\operatorname{ad}^0(\bar\rho)(1). \tag{13.2}
$$

The twist remains present even though the untwisted module is self-dual.

### 13.2 Tangent conditions and their duals

A local deformation condition at $v$ has a tangent subspace

$$
\mathcal L_v\subseteq H^1(K_v,M).
$$

Typical examples include:

* unramified deformations, with tangent $H^1_{\mathrm{ur}}$;
* a strict condition, with tangent zero;
* an unrestricted local problem, with full tangent space;
* fixed inertial or minimally ramified conditions, whose tangent spaces are intermediate subspaces;
* integral conditions at $v\mid\ell$, whose tangent spaces must be computed from the integral problem rather than guessed from generic-fiber ramification.

At an unramified place $v\nmid\ell$, Frobenius makes the numerical behavior especially transparent:

$$
\dim_kH^1_{\mathrm{ur}}(K_v,M)
=\dim_kH^0(K_v,M).
$$

Thus an unramified condition contributes zero to the local sum in (13.4). A strict condition contributes $-h^0(K_v,M)$, while a relaxed condition contributes

$$
\dim H^1(K_v,M)-h^0(K_v,M)
=h^0(K_v,M^*(1))
$$

by the prime-to-$\ell$ local Euler formula. These three values are the basic local entries in fixed-determinant dimension calculations.

For a two-dimensional odd representation over $\mathbf Q$ with $\ell\ne2$, complex conjugation acts on $\operatorname{ad}^0$ with a one-dimensional fixed line and a two-dimensional negative space. Since real $H^1$ vanishes for odd coefficients, the infinite place contributes $-1$ to (13.4). This is the familiar “oddness” correction, now seen as an ordinary $H^0(\mathbf R,M)$ term rather than an unexplained global constant.

The global tangent space is $H^1_{\mathcal L}(K,M)$. Its dual local condition is the exact annihilator $\mathcal L_v^\perp$ in $H^1(K_v,M^*(1))$, and the dual Selmer group is

$$
H^1_{\mathcal L^\perp}(K,M^*(1)). \tag{13.3}
$$

Formula (9.5) now reads

$$
\dim H^1_{\mathcal L}(K,M)-\dim H^1_{\mathcal L^\perp}(K,M^*(1))
=h^0(K,M)-h^0(K,M^*(1))
+\sum_{v\in S}(\dim\mathcal L_v-h^0(K_v,M)). \tag{13.4}
$$

All terms on the right are accessible from the residual representation and local tangent calculations. This is why global duality is the numerical bridge from local deformation conditions to a global deformation problem. Construction of deformation rings belongs later; here only their cohomological tangent and obstruction accounting is needed.

### 13.3 Why the dual Selmer dimension counts missing equations

Let

$$
q=\dim_kH^1_{\mathcal L^\perp}(K,M^*(1)).
$$

Choose a basis $y_1,\dots,y_q$. Each $y_j$ defines, through its localizations and the pairings (8.6), a linear functional on newly allowed local directions. Exactness says that these are precisely the independent reciprocity constraints preventing arbitrary local tangent data from being globalized.

Suppose one enlarges the local problem at new primes by one-dimensional quotients $\Delta_w$. The comparison map in (8.9) is

$$
\bigoplus_w\Delta_w
\longrightarrow H^1_{\mathcal L^\perp}(K,M^*(1))^D, \tag{13.5}
$$

and its matrix has entries given by local Tate pairings between a chosen new direction at $w$ and $\operatorname{loc}_w(y_j)$. To eliminate the old dual Selmer group, this matrix must have rank $q$. Therefore at least $q$ independent one-dimensional local directions are required. If exactly $q$ are chosen and the pairing matrix is nonsingular, the new orthogonal dual Selmer group is zero.

This is an exact rank statement, not a heuristic count. Fewer than $q$ one-dimensional local quotients cannot surject onto a $q$-dimensional dual, while $q$ suffice only when their localization functionals are independent. The existence of primes with the required independent functionals is a separate arithmetic selection problem.

### 13.4 What auxiliary primes must accomplish

The later Taylor--Wiles construction chooses auxiliary primes with carefully controlled Frobenius and local deformation conditions. At the present stage, global duality tells us only the specification those primes must meet:

1. each prime should supply a known local quotient $\Delta_w$, commonly one-dimensional;
2. localization of dual Selmer classes should pair nontrivially with that quotient;
3. across the chosen primes, the resulting functionals should span the full dual Selmer dual;
4. the change in the primal Selmer group is then governed exactly by (8.9) and (10.4).

Thus $q$ counts the minimum number of independent local equations needed to kill the dual obstruction space, not automatically the number of arbitrary primes. Prime selection, congruence conditions, and the construction of patched objects are not part of global duality and will be developed only when their additional inputs are available.

## 14. The global-duality dictionary

### 14.1 A construction protocol

A reliable use of global duality proceeds in this order.

1. Fix the coefficient category: finite discrete, compact lattice, discrete torsion, or finite-dimensional local-field vector space.
2. For finite $M$, form $M'=\operatorname{Hom}(M,\mathbf Q/\mathbf Z(1))$; for a lattice, use the discrete partner (7.2); for a vector space, use $V^*(1)$.
3. Choose finite $S$ containing infinity, coefficient-characteristic places, ramified places of both modules, and every non-unramified local condition.
4. Use $\widehat H^i(C_2,-)$ at real places and zero modified cohomology at complex places. Never remove real places merely because they vanish for odd coefficients.
5. Normalize every local invariant so corestriction preserves it and the sum of invariants of a global Brauer class is zero.
6. Define compact support as $\operatorname{Cone}(C_{\mathrm{glob}}\to C_{\mathrm{loc}})[-1]$ with a fixed sign convention.
7. Use perfectness $H_c^i(M)\simeq H^{3-i}(M')^D$ to identify cone boundaries, then read exactness from the localization long exact sequence.
8. Define dual local conditions as exact annihilators. At infinite level require primal conditions to be closed.
9. Use (8.5) for kernels and cokernels, (8.8) for annihilators, and (9.4) or (9.5) for orders or dimensions.
10. When changing $S$, a field, or local conditions, transport every place and use restriction/corestriction adjointness before comparing dimensions.

### 14.2 Formula and variance table

| object or map | exact role | qualification that cannot be dropped |
|---|---|---|
| $M'=M^\vee(1)$ | local and global dual coefficient | dual reverses coefficient arrows; twist comes from the Brauer target |
| $P_S^i(M)$ | sum of modified local groups | $\widehat H^i$ at real places, zero at complex places |
| $C_c^\bullet$ | cone of localization shifted by $-1$ | shift produces complementary global degree $3-i$ |
| $\sum\operatorname{inv}_v$ | global reciprocity functional | real nonzero class has invariant $1/2$ |
| $H_c^i(M)\simeq H^{3-i}(M')^D$ | perfect global duality | finiteness and restricted ramification are part of the theorem |
| $\alpha_i$ | local family paired against global dual classes | target is $H^{2-i}(M')^D$ |
| image of localization | locally realizable families | equals the exact annihilator of the dual localization image |
| $\mathcal L_v^\perp$ | dual local condition | defined by annihilation, not by complementary order |
| $Q_{\mathcal L}$ | forbidden local quotient | its cokernel maps into, but need not equal, the whole dual Selmer dual |
| strict / relaxed | $0$ / all local $H^1$ | exact orthogonals are relaxed / strict |
| unramified | kernel of restriction to inertia | self-orthogonal only under the usual unramified prime-to-coefficient hypotheses |
| Greenberg--Wiles formula | difference of primal and dual Selmer sizes | includes all ordinary $H^0(K_v,M)$ denominators, including infinity |
| restriction | base change of a class | produces components at every $w\mid v$ |
| corestriction | transfer back | sums over $w\mid v$ and is adjoint to restriction |
| lattice duality | compact $T$ versus discrete $D(T)$ | inverse/direct limits, closure, and $\varprojlim^1$ must be controlled |

The three formulas most often reused are

$$
H_c^i(G_{K,S},M)\simeq H^{3-i}(G_{K,S},M')^D, \tag{14.1}
$$

$$
\operatorname{im}(H^i(G_{K,S},M)\to P_S^i(M))^\perp
=\operatorname{im}(H^{2-i}(G_{K,S},M')\to P_S^{2-i}(M')), \tag{14.2}
$$

and

$$
\dim H^1_{\mathcal L}(M)-\dim H^1_{\mathcal L^\perp}(M^*(1))
=h^0(M)-h^0(M^*(1))
+\sum_{v\in S}(\dim\mathcal L_v-h_v^0(M)). \tag{14.3}
$$

Each answers a different question: (14.1) identifies a dual object, (14.2) identifies a subgroup, and (14.3) identifies a numerical difference. None should be substituted for another.

### 14.3 Final synthesis

Local Tate pairings turn a local class into a functional, but global reciprocity couples those functionals across all places. The sum of local invariants vanishes on global cup products, so every global family lies in a reciprocity annihilator. Compactly supported cohomology records the failure of localization at the cochain level, and its mapping-cone shift explains why global degree $i$ meets dual degree $3-i$ while local degree $i$ meets degree $2-i$.

The decisive theorem is perfectness. Its proof passes through finite Galois levels, induced local modules, the idele-class sequence, compatible local and global fundamental classes, and the norm-index theorem. It shows that reciprocity supplies all global relations, not merely some of them. Substitution into the cone long exact sequence produces the full nine-term sequence, including its degree-zero and degree-two endpoints and its real-place modifications.

Selmer structures then become exact linear algebra inside arithmetic cohomology. A local permission has an exact dual prohibition; the failure of permitted local data to globalize is paired with the dual Selmer group; and changing one condition moves dimension between the primal and dual sides according to a five-term comparison sequence. The Euler characteristic and Greenberg--Wiles formulas retain the global invariant terms, every local tangent dimension, and every archimedean correction.

For adjoint modules, the primal Selmer group is the global tangent space and the dual Selmer group measures independent reciprocity constraints. Its dimension is therefore the minimum number of independent one-dimensional local directions that must be made available before those constraints can be eliminated. Global duality provides this exact count and the pairing matrix that must have full rank. Later arguments will choose primes realizing that matrix; the present theory explains why that is the right task.

The reusable conclusion is consequently sharper than a dimension formula. Global localization images are exact annihilators, compact and discrete coefficient theories are true Pontryagin partners, real places remain visible at the prime two, and every change of conditions has a dual correction. These statements provide the global cohomological accounting needed for deformation theory without concealing any kernel, cokernel, twist, topology, or archimedean term.
