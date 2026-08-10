# Taylor–Wiles Systems

## Contents

1. [From auxiliary primes to finite-level algebra](#1-from-auxiliary-primes-to-finite-level-algebra)
   - [The exchange that the algebra must remember](#11-the-exchange-that-the-algebra-must-remember)
   - [Three actions and three logically different maps](#12-three-actions-and-three-logically-different-maps)
   - [A system and a realization of it](#13-a-system-and-a-realization-of-it)
   - [Standing conventions](#14-standing-conventions)
2. [The base deformation and Hecke data](#2-the-base-deformation-and-hecke-data)
   - [Coefficients and complete local rings](#21-coefficients-and-complete-local-rings)
   - [The global ring and the local base](#22-the-global-ring-and-the-local-base)
   - [The base Hecke pair](#23-the-base-hecke-pair)
   - [The covariance ledger](#24-the-covariance-ledger)
3. [Diamond groups and their algebras](#3-diamond-groups-and-their-algebras)
   - [Exact-level diamond groups](#31-exact-level-diamond-groups)
   - [Augmentation and its ideal](#32-augmentation-and-its-ideal)
   - [One completed group algebra for every level](#33-one-completed-group-algebra-for-every-level)
   - [Level ideals, ranks, and regular sequences](#34-level-ideals-ranks-and-regular-sequences)
   - [What the chosen coordinates do and do not mean](#35-what-the-chosen-coordinates-do-and-do-not-mean)
4. [Auxiliary deformation rings](#4-auxiliary-deformation-rings)
   - [The arithmetic datum at level $N$](#41-the-arithmetic-datum-at-level-n)
   - [Local Taylor–Wiles factors](#42-local-taylorwiles-factors)
   - [The global auxiliary ring](#43-the-global-auxiliary-ring)
   - [Augmentation recovers the original problem](#44-augmentation-recovers-the-original-problem)
   - [Tangent counts, defects, and relation bounds](#45-tangent-counts-defects-and-relation-bounds)
5. [Hecke algebras, modules, and the comparison map](#5-hecke-algebras-modules-and-the-comparison-map)
   - [The acting Hecke algebra](#51-the-acting-hecke-algebra)
   - [The commuting module structures](#52-the-commuting-module-structures)
   - [Local–global compatibility and $R_N\to\mathbb T_N$](#53-localglobal-compatibility-and-r_ntomathbb-t_n)
   - [Surjectivity and faithfulness are different assertions](#54-surjectivity-and-faithfulness-are-different-assertions)
6. [Descent through augmentation](#6-descent-through-augmentation)
   - [Deformation-ring descent](#61-deformation-ring-descent)
   - [Module coinvariant control](#62-module-coinvariant-control)
   - [Hecke-algebra control](#63-hecke-algebra-control)
   - [The exact isomorphism criteria](#64-the-exact-isomorphism-criteria)
7. [Invariants, coinvariants, and the norm](#7-invariants-coinvariants-and-the-norm)
   - [The two constructions](#71-the-two-constructions)
   - [The norm comparison](#72-the-norm-comparison)
   - [Free and projective diamond modules](#73-free-and-projective-diamond-modules)
   - [Why characteristic dividing the group order is different](#74-why-characteristic-dividing-the-group-order-is-different)
8. [Freeness, balancedness, and uniform size](#8-freeness-balancedness-and-uniform-size)
   - [A genuinely free diamond module](#81-a-genuinely-free-diamond-module)
   - [Equal coefficient rank with a nonfree action](#82-equal-coefficient-rank-with-a-nonfree-action)
   - [Balanced modules](#83-balanced-modules)
   - [Uniform ranks, cardinalities, and generator counts](#84-uniform-ranks-cardinalities-and-generator-counts)
9. [Fixed presentations of the finite levels](#9-fixed-presentations-of-the-finite-levels)
   - [The diamond presentation $S_\infty$](#91-the-diamond-presentation-s_infty)
   - [A fixed deformation presentation $R_\infty$](#92-a-fixed-deformation-presentation-r_infty)
   - [Lifting the diamond coordinates](#93-lifting-the-diamond-coordinates)
   - [Minimality versus uniform padding](#94-minimality-versus-uniform-padding)
10. [Nonnested auxiliary sets and comparison across levels](#10-nonnested-auxiliary-sets-and-comparison-across-levels)
    - [Why nested Taylor–Wiles sets cannot persist](#101-why-nested-taylorwiles-sets-cannot-persist)
    - [A worked pair of nonnested levels](#102-a-worked-pair-of-nonnested-levels)
    - [Presentation maps are not arithmetic transition maps](#103-presentation-maps-are-not-arithmetic-transition-maps)
    - [Common finite shadows and pseudo-transitions](#104-common-finite-shadows-and-pseudo-transitions)
    - [When genuine transition maps may be added](#105-when-genuine-transition-maps-may-be-added)
11. [Framed and unframed systems](#11-framed-and-unframed-systems)
    - [Why frames enter](#111-why-frames-enter)
    - [The variable ledger](#112-the-variable-ledger)
    - [Removing smooth variables](#113-removing-smooth-variables)
    - [Branch compatibility](#114-branch-compatibility)
12. [Duality and adjoints](#12-duality-and-adjoints)
    - [Coefficient-valued and group-ring-valued pairings](#121-coefficient-valued-and-group-ring-valued-pairings)
    - [Diamond inversion and Hecke adjoints](#122-diamond-inversion-and-hecke-adjoints)
    - [Descent of perfect pairings](#123-descent-of-perfect-pairings)
    - [Duality data across a presentation system](#124-duality-data-across-a-presentation-system)
13. [Support, annihilators, depth, and faithfulness](#13-support-annihilators-depth-and-faithfulness)
    - [Annihilators from the factorized action](#131-annihilators-from-the-factorized-action)
    - [Support and finite Hecke quotients](#132-support-and-finite-hecke-quotients)
    - [Depth over the diamond algebra](#133-depth-over-the-diamond-algebra)
    - [The hypotheses exported to patching](#134-the-hypotheses-exported-to-patching)
14. [Where the module axioms come from](#14-where-the-module-axioms-come-from)
    - [Definite quaternionic modules](#141-definite-quaternionic-modules)
    - [Cohomological modules](#142-cohomological-modules)
    - [Why the abstract package is deliberately conditional](#143-why-the-abstract-package-is-deliberately-conditional)
15. [Failure modes](#15-failure-modes)
    - [Nonfree diamond action](#151-nonfree-diamond-action)
    - [Coefficient torsion and bad reduction](#152-coefficient-torsion-and-bad-reduction)
    - [Varying ranks and unbounded presentations](#153-varying-ranks-and-unbounded-presentations)
    - [Missing augmentation control](#154-missing-augmentation-control)
    - [Incompatible local branches](#155-incompatible-local-branches)
    - [False transitions between unrelated levels](#156-false-transitions-between-unrelated-levels)
16. [Taylor–Wiles data and Taylor–Wiles systems](#16-taylorwiles-data-and-taylorwiles-systems)
    - [A Taylor–Wiles datum at one level](#161-a-taylorwiles-datum-at-one-level)
    - [A presentation-compatible Taylor–Wiles system](#162-a-presentation-compatible-taylorwiles-system)
    - [A stronger transitioned system](#163-a-stronger-transitioned-system)
    - [The axiom ledger](#164-the-axiom-ledger)
17. [The arithmetic existence theorem](#17-the-arithmetic-existence-theorem)
    - [The deformation-side theorem](#171-the-deformation-side-theorem)
    - [Proof of the theorem](#172-proof-of-the-theorem)
    - [The automorphic hypotheses still to be supplied](#173-the-automorphic-hypotheses-still-to-be-supplied)
    - [Final synthesis](#174-final-synthesis)

## 1. From auxiliary primes to finite-level algebra

### 1.1 The exchange that the algebra must remember

Taylor–Wiles primes are chosen to turn an invisible global obstruction into visible local symmetry. Begin with a global deformation problem whose tangent space is a Selmer group and whose reciprocity defect is measured by a dual Selmer group. Write $W$ for its residual tangent coefficient. Put

$$
q(\mathcal D)
=\dim_k H^1_{\mathcal L^\perp}(K,W^*(1)),
$$

and abbreviate $q=q(\mathcal D)$. The construction of the preceding theory gives, for every $N\geq 1$, a set $Q_N$ of $q$ auxiliary places. At each $v\in Q_N$, the residue cardinality satisfies

$$
q_v\equiv 1\pmod{\ell^N},
$$

residual Frobenius has distinct eigenvalues, and a chosen eigenline supports a tame character through a cyclic quotient of order $\ell^N$. The resulting local condition gains one primal tangent direction and removes one dual local condition. The $q$ selected localization functionals kill the entire dual Selmer group.

The finite-level algebra must retain both sides of this exchange. On one side it has an auxiliary deformation ring with no surviving absolute dual Selmer obstruction. On the other it has an action of a product of finite cyclic $\ell$-groups. Augmentation sets every tame character equal to one and returns to the original deformation problem. The purpose of a Taylor–Wiles system is to package this information so precisely that later arguments need not remember which primes were used or which geometric space produced the module.

At level $N$ the schematic picture is

$$
\begin{array}{ccccc}
\mathcal O[\Delta_N]&\longrightarrow&R_N&\longrightarrow&\mathbb T_N\\
&&&&\mathrel{\lhook\joinrel\longrightarrow}\operatorname{End}_{\mathcal O}(M_N),
\end{array}
\tag{1.1}
$$

together with a fixed local-base map $R_{\mathrm{loc}}\to R_N$. The first arrow records tame diamond characters. The second is the deformation-to-Hecke comparison. The last is the faithful action when $\mathbb T_N$ is defined as an image algebra. Every arrow points from scalars toward the object on which those scalars act.

At augmentation, one seeks a compatible diagram

$$
\begin{array}{ccc}
R_N/\mathfrak a_NR_N&\longrightarrow&\mathbb T_N/\mathfrak a_N\mathbb T_N\\
\downarrow&&\downarrow\\
R&\longrightarrow&\mathbb T,
\end{array}
\tag{1.2}
$$

and a comparison

$$
M_N/\mathfrak a_NM_N\longrightarrow M.
\tag{1.3}
$$

The deformation-side vertical map is an isomorphism for the enhanced local condition constructed from a chosen regular eigenline. The other two comparisons are control assertions about the chosen automorphic or cohomological realization. They do not follow from the existence of $Q_N$.

### 1.2 Three actions and three logically different maps

The notation in (1.1) is compact enough to conceal important distinctions. We name all of them now.

First, the group $\Delta_N$ acts on $M_N$. For a left action this is equivalently an $\mathcal O$-algebra homomorphism

$$
d_N:\mathcal O[\Delta_N]\longrightarrow
\operatorname{End}_{\mathcal O}(M_N).
\tag{1.4}
$$

Second, a specified commutative family of Hecke correspondences acts on $M_N$. Its image is a finite algebra $\mathbb T_N$, with an injective map

$$
h_N:\mathbb T_N\hookrightarrow
\operatorname{End}_{\mathcal O}(M_N).
\tag{1.5}
$$

Third, the universal deformation gives an action of $R_N$ only after a comparison homomorphism

$$
\pi_N:R_N\longrightarrow\mathbb T_N
\tag{1.6}
$$

has been constructed. The resulting map to endomorphisms is the composite

$$
r_N=h_N\circ\pi_N:R_N\longrightarrow
\operatorname{End}_{\mathcal O}(M_N).
\tag{1.7}
$$

These are not three names for one action. The compatibility demanded at an auxiliary prime is

$$
d_N=h_N\circ\pi_N\circ\lambda_N,
\tag{1.8}
$$

where

$$
\lambda_N:\mathcal O[\Delta_N]\longrightarrow R_N
\tag{1.9}
$$

is the deformation-side diamond map. If local reciprocity and geometric diamond operators use opposite conventions, the chosen identification of $\Delta_N$ must include inversion before (1.8) is asserted. A convention error here is not repaired by commutativity.

The ring map $R_N\to\operatorname{End}_{\mathcal O}(M_N)$ encodes an $R_N$-module structure. It does not, by itself, specify the Hecke algebra as an intermediate image, the independent geometric origin of the diamond action, or the equality (1.8). Those pieces are separate data and separate theorems.

### 1.3 A system and a realization of it

There are two useful levels of abstraction.

A **finite-level datum** names one auxiliary set, its diamond group, its deformation ring, its Hecke algebra, and its module, together with every structural and comparison map. It is the correct unit for checking local–global compatibility and augmentation.

A **system** names such a datum for every $N$, fixes uniform ranks and presentation bounds, and places all diamond groups and deformation rings under common power-series sources. The word “system” does not automatically mean that there are maps

$$
R_{N+1}\longrightarrow R_N,
\qquad
M_{N+1}\longrightarrow M_N.
$$

For independently chosen sets $Q_N$, such maps ordinarily have no arithmetic meaning. Common presentations supply comparability without inventing functoriality.

Finally, a **realization theorem** proves that modules coming from a particular source satisfy the module-side axioms: diamond freeness or balancedness, control modulo augmentation, a compatible Hecke action, uniform rank, and perfect pairings when duality is included. The definition of a system must not be confused with such a theorem. Arithmetic deformation theory constructs the rings and their numerical properties. Geometry and automorphic theory must still construct the modules and verify their control properties.

### 1.4 Standing conventions

Fix a prime $\ell$, a finite field $k$ of characteristic $\ell$, and a complete discrete valuation ring

$$
(\mathcal O,\varpi,k)
$$

with fraction field $E$. All complete local $\mathcal O$-algebras have residue field $k$, all homomorphisms between them are continuous local $\mathcal O$-algebra homomorphisms, and all modules are left modules unless stated otherwise. Completed tensor products are taken over $\mathcal O$ at the displayed closed points.

The clean arithmetic model is a fixed-determinant, absolutely irreducible rank-two residual representation over an odd-characteristic field. The abstract algebra below does not depend on rank two, but every use of the prime-selection theorem presupposes the exact image, determinant, and local-condition hypotheses under which that theorem was proved.

We use exact-level diamond quotients. Thus every local factor has order $\ell^N$, even if the maximal $\ell$-power quotient of the residue-field units is larger. This convention is what makes the cardinality formula uniform.

For an ideal $I\subset A$ and an $A$-module $X$, the notation $X/IX$ means $A/I\otimes_A X$. This is a coinvariant construction when $I$ is an augmentation ideal. Invariants will always be written with a superscript and will never be substituted silently for this quotient.

## 2. The base deformation and Hecke data

### 2.1 Coefficients and complete local rings

The base coefficient ring is more than a place to store numbers. Its closed point fixes the residual representation, its topology makes universal deformations continuous, and its uniformizer separates characteristic zero from residual characteristic. We therefore keep the structural maps visible:

$$
\mathcal O\longrightarrow A\longrightarrow k
$$

for every complete local coefficient algebra $A$. The second arrow is the residue map; it is not generally an $\mathcal O$-algebra splitting of the first.

Finite group rings $\mathcal O[\Delta_N]$ are complete local rings in this setting because $\Delta_N$ is a finite $\ell$-group. Their maximal ideal is

$$
(\varpi,\mathfrak a_N),
$$

where $\mathfrak a_N$ is the augmentation ideal. They are finite free, hence flat, over $\mathcal O$. None of these properties implies that a module of the same $\mathcal O$-rank is free over the group ring.

### 2.2 The global ring and the local base

Let $\mathcal D$ be the original global deformation problem. Its unframed universal ring is denoted

$$
R=R_{\mathcal D}.
$$

If a set $T$ of local places is framed, let

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v\in T,\mathcal O}
R_v^{\square,\mathcal D_v}
\tag{2.1}
$$

be the completed tensor product of the chosen framed local condition rings. The partially framed global ring receives the structural map

$$
R_{\mathrm{loc}}\longrightarrow R^{\square_T}.
\tag{2.2}
$$

The direction in (2.2) is forced by universality: a global deformation restricts to a local deformation, so a test algebra receiving the global universal family also receives every local universal family. The global ring is an algebra over the local base.

One may work unframed, framed, or partially framed, but the convention must remain fixed across levels. In the main notation $R_N$ will mean the version being patched, and $R$ its augmentation quotient. When a distinction matters, superscripts will be restored.

The local base must also be fixed across $N$. Local conditions at the original ramification set remain on the same components. Auxiliary local factors vary with $Q_N$; their diamond part is supplied by $\mathcal O[\Delta_N]$, while their formally smooth eigenvalue and frame coordinates can be placed in a fixed collection of power-series variables after enumerating $Q_N$. This is a presentation choice, not an identification of the local fields.

### 2.3 The base Hecke pair

Let $M$ be the localized integral module at the original level. It may be a module of functions on a finite quaternionic class set or an appropriate integral cohomology module. Choose a commutative family of Hecke operators and define

$$
\mathbb T
=\operatorname{im}\left(
\mathbb T^{\mathrm{abs}}\longrightarrow
\operatorname{End}_{\mathcal O}(M)
\right).
\tag{2.3}
$$

Thus $M$ is faithful over $\mathbb T$ by definition:

$$
\operatorname{Ann}_{\mathbb T}(M)=0.
\tag{2.4}
$$

If $M$ is finite free over $\mathcal O$, then $\mathbb T$ is a finite torsion-free $\mathcal O$-module and hence finite free. If $M$ has $\varpi$-torsion, the same conclusion is unavailable.

A family representation over $\mathbb T$, together with verified local conditions, supplies a homomorphism

$$
\pi:R\longrightarrow\mathbb T.
\tag{2.5}
$$

A determinant or Cayley–Hamilton family supplies (2.5) only after a theorem upgrades it, on the residually absolutely irreducible block, to a genuine representation satisfying the represented deformation problem.

Surjectivity of (2.5) usually comes from the fact that $\mathbb T$ is generated by good-prime Hecke operators whose values are traces and determinants of universal Frobenius elements. This is an argument about the selected generating family. It is not a consequence of the word “Hecke.”

### 2.4 The covariance ledger

The following table fixes the direction and role of every base-level map.

| Map | Meaning | Consequence |
|---|---|---|
| $\mathcal O\to R_{\mathrm{loc}}$ | coefficient structure | local rings use the fixed residual field |
| $R_{\mathrm{loc}}\to R^{\square_T}$, or to the fixed version denoted $R$ when that structural map is defined | restriction of a global deformation to local places | the selected global ring is an $R_{\mathrm{loc}}$-algebra |
| $R\to\mathbb T$ | the Hecke-valued family satisfies the deformation problem | $M$ acquires an $R$-action through $\mathbb T$ |
| $\mathbb T\hookrightarrow\operatorname{End}_{\mathcal O}(M)$ | definition of the acting image algebra | $M$ is faithful over $\mathbb T$ |
| $R\to\operatorname{End}_{\mathcal O}(M)$ | composite of the preceding two maps | its kernel equals $\ker(R\to\mathbb T)$ when $M$ is $\mathbb T$-faithful |

There is no arrow $\mathbb T\to R$ in the input. Producing an inverse to $R\twoheadrightarrow\mathbb T$ is the conclusion of a later comparison argument, not part of the system.

## 3. Diamond groups and their algebras

### 3.1 Exact-level diamond groups

Let $Q_N$ be a Taylor–Wiles set of cardinality $q$. For $v\in Q_N$, the congruence $q_v\equiv1\pmod{\ell^N}$ gives the exact-level quotient

$$
\Delta_v(N)
=k(v)^\times/(k(v)^\times)^{\ell^N}
\simeq\mathbf Z/\ell^N\mathbf Z.
\tag{3.1}
$$

Define

$$
\Delta_N=\Delta_{Q_N}
=\prod_{v\in Q_N}\Delta_v(N).
\tag{3.2}
$$

Then

$$
|\Delta_N|=\ell^{Nq}.
\tag{3.3}
$$

The isomorphism

$$
\Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q
\tag{3.4}
$$

requires an ordering of $Q_N$ and a generator of every cyclic factor. Neither choice comes from the abstract group, and neither identifies primes at different levels.

If $\ell^{a_v}$ is the exact $\ell$-power dividing $q_v-1$, the maximal local diamond group has order $\ell^{a_v}$, which can be strictly larger than $\ell^N$. The exact-level group in (3.1) is its canonical quotient of order $\ell^N$. Passing from the maximal convention to the exact-level convention is a quotient on groups and hence a quotient on group algebras. The tangent contribution remains one-dimensional, but ranks and cardinalities change. A system must choose one convention globally; every formula below uses the exact-level convention.

### 3.2 Augmentation and its ideal

Put

$$
\Lambda_N=\mathcal O[\Delta_N].
\tag{3.5}
$$

The augmentation is

$$
\epsilon_N:\Lambda_N\longrightarrow\mathcal O,
\qquad
\sum_{\delta\in\Delta_N}a_\delta[\delta]
\longmapsto
\sum_{\delta\in\Delta_N}a_\delta.
\tag{3.6}
$$

Its kernel is the augmentation ideal

$$
\mathfrak a_N=\ker(\epsilon_N).
\tag{3.7}
$$

If $\delta_{N,1},\ldots,\delta_{N,q}$ are the chosen cyclic generators, then

$$
\mathfrak a_N
=([\delta_{N,1}]-1,\ldots,[\delta_{N,q}]-1).
\tag{3.8}
$$

These $q$ elements minimally generate $\mathfrak a_N$ relative to $\mathcal O$, because their images form a basis of

$$
\mathfrak a_N/
(\varpi\mathfrak a_N+\mathfrak a_N^2).
\tag{3.9}
$$

Augmentation is covariant on scalar rings and contravariant on the corresponding character-valued deformation problems: setting the universal diamond character equal to one gives a quotient of the auxiliary universal ring.

### 3.3 One completed group algebra for every level

Fix the pro-$\ell$ group

$$
\Gamma=\mathbf Z_\ell^q
$$

with ordered topological generators $\gamma_1,\ldots,\gamma_q$. Its completed group algebra is

$$
S_\infty=\mathcal O[[\Gamma]]
\simeq\mathcal O[[z_1,\ldots,z_q]],
\qquad
\gamma_i\longmapsto1+z_i.
\tag{3.10}
$$

For each $N$, define

$$
\mathfrak c_N=\bigl(
(1+z_1)^{\ell^N}-1,\ldots,
(1+z_q)^{\ell^N}-1
\bigr).
\tag{3.11}
$$

Then

$$
S_N:=S_\infty/\mathfrak c_N
\simeq\mathcal O[\Gamma/\ell^N\Gamma].
\tag{3.12}
$$

After the choices in (3.4), there is an isomorphism

$$
\iota_N:S_N\xrightarrow{\sim}\Lambda_N,
\qquad
1+z_i\longmapsto[\delta_{N,i}].
\tag{3.13}
$$

Equivalently, there is a chosen surjection

$$
\alpha_N:S_\infty\twoheadrightarrow\Lambda_N
\tag{3.14}
$$

with kernel $\mathfrak c_N$. Under augmentation, the ideal

$$
\mathfrak a_\infty=(z_1,\ldots,z_q)
\tag{3.15}
$$

maps onto $\mathfrak a_N$.

The standard quotients do have canonical transition maps

$$
S_{N+1}\twoheadrightarrow S_N
\tag{3.16}
$$

induced by $\Gamma/\ell^{N+1}\Gamma\twoheadrightarrow\Gamma/\ell^N\Gamma$. Transporting (3.16) through chosen isomorphisms gives comparison maps between $\Lambda_{N+1}$ and $\Lambda_N$. Those transported maps depend on the orderings and generators; they do not come from a relation between $Q_{N+1}$ and $Q_N$.

By the definition of a completed group algebra, the standard system has a canonical isomorphism

$$
S_\infty
\xrightarrow{\sim}
\varprojlim_N\mathcal O[\Gamma/\ell^N\Gamma]
=\varprojlim_NS_N.
\tag{3.17}
$$

Concretely, a compatible family of finite group-ring elements determines, to every finite group precision, the coefficients of one continuous $\mathcal O$-valued measure on $\Gamma$; expansion at the ordered generators writes that measure uniquely as a power series in the $z_i$. The transition maps in (3.17) are genuine because the quotients of the fixed group $\Gamma$ are nested. After transport to the arithmetic algebras $\Lambda_N$, the same inverse-limit display depends on all coordinate choices and still carries no maps between the auxiliary deformation rings.

### 3.4 Level ideals, ranks, and regular sequences

The ring $S_\infty$ is regular local of dimension $q+1$. The $q$ elements in (3.11) form a regular sequence.

To see this, adjoin the variables one at a time. In

$$
\mathcal O[[z_1,\ldots,z_q]],
$$

the element $(1+z_i)^{\ell^N}-1$ is a monic polynomial of degree $\ell^N$ in $z_i$. Quotienting by it leaves a finite free module with basis

$$
1,z_i,\ldots,z_i^{\ell^N-1}
$$

over the power-series ring in the remaining variables. In particular it is a non-zero-divisor at the stage when it is imposed. Induction proves regularity of the sequence and gives

$$
\operatorname{rank}_{\mathcal O}S_N=\ell^{Nq}.
\tag{3.18}
$$

Thus $S_N$ is a one-dimensional complete-intersection local ring, finite flat over $\mathcal O$. Its special fiber is highly nonreduced:

$$
S_N/\varpi S_N
\simeq
k[z_1,\ldots,z_q]/(z_1^{\ell^N},\ldots,z_q^{\ell^N}).
\tag{3.19}
$$

The nilpotent tangent directions in (3.19) are precisely the residual shadows of finite diamond characters. They are expected and must not be mistaken for coefficient torsion.

### 3.5 What the chosen coordinates do and do not mean

The maps $\alpha_N$ solve a comparison problem: every finite diamond algebra becomes a quotient of one fixed ring. They do not assert any of the following:

- that the places in $Q_N$ occur in $Q_{N+1}$;
- that local decomposition groups at different levels are identified;
- that an auxiliary deformation at level $N+1$ restricts to one at level $N$;
- that a module at level $N+1$ maps to a module at level $N$;
- that the selected cyclic generators have arithmetic significance beyond their finite local quotients.

Changing a generator $\delta_{N,i}$ to $\delta_{N,i}^u$, with $u\in(\mathbf Z/\ell^N\mathbf Z)^\times$, requires a chosen lift $\widetilde u\in\mathbf Z_\ell^\times$ on the ambient completed algebra and changes the coordinate by

$$
z_i\longmapsto(1+z_i)^{\widetilde u}-1.
\tag{3.20}
$$

Different lifts give the same automorphism of the level-$N$ quotient but need not give the same automorphism of $S_\infty$.

Swapping the chosen local eigenline inverts the diamond character and corresponds to

$$
z_i\longmapsto(1+z_i)^{-1}-1.
\tag{3.21}
$$

Both are continuous coordinate automorphisms. They show that the common presentation is robust under honest changes of convention, but they also show why it is noncanonical.

## 4. Auxiliary deformation rings

### 4.1 The arithmetic datum at level $N$

Return to a fixed global deformation problem $\mathcal D$ for a residual representation

$$
\bar\rho:G_{K,S}\longrightarrow\operatorname{GL}_2(k)
$$

with fixed determinant $\delta$. Put

$$
W=\operatorname{ad}^0\bar\rho,
\qquad
W'=W^*(1).
$$

Let $Q_N$ be a Taylor–Wiles set. In addition to the set of places, its arithmetic datum includes, for every $v\in Q_N$,

1. a split regular residual Frobenius with eigenvalues $\bar\alpha_v\ne\bar\beta_v$ in $k$;
2. a choice of the $\bar\alpha_v$-eigenline;
3. the exact quotient $\Delta_v(N)$ of the residue-field units;
4. a reciprocity convention identifying the universal tame character with the group-like elements of $\mathcal O[\Delta_v(N)]$.

These choices define an enlarged global deformation problem $\mathcal D_{Q_N}$. At the old places it uses the conditions of $\mathcal D$. At $v\in Q_N$ it permits diagonal tame ramification on the chosen line, places the inverse character on the other line so that determinant remains fixed, and retains an unramified Frobenius-eigenvalue parameter. Outside $S\cup Q_N$ it remains unramified.

Write

$$
R_N=R_{\mathcal D_{Q_N}}
\tag{4.1}
$$

for the unframed universal ring, or $R_N^{\square_T}$ when a fixed framing convention is in force. The notation $R_N$ records an auxiliary deformation problem, not merely the integer $N$; changing $Q_N$ changes the represented problem even when the abstract diamond group remains isomorphic.

### 4.2 Local Taylor–Wiles factors

At a single auxiliary place, choose a lift $\widetilde\alpha_v\in\mathcal O^\times$ of the selected residual eigenvalue. If $X_v$ varies its unramified value and $\boldsymbol\theta_v$ is the universal tame character, the two characters on the selected decomposition have the form

$$
\chi_{v,1}=\eta_{X_v}\boldsymbol\theta_v,
\qquad
\chi_{v,2}=\delta\chi_{v,1}^{-1}.
\tag{4.2}
$$

The unframed local ring is therefore

$$
R_v^{\mathrm{TW}}
\simeq\mathcal O[\Delta_v(N)][[X_v]].
\tag{4.3}
$$

If a full local matrix frame is retained, two further coordinates record the position of the two lifted eigenlines:

$$
R_v^{\square,\mathrm{TW}}
\simeq\mathcal O[\Delta_v(N)][[X_v,U_v,V_v]].
\tag{4.4}
$$

The relative dimensions over the diamond algebra are one and three. The difference of two between (4.3) and (4.4) is an eigenline-position difference. It is not another pair of diamond variables.

Augmentation kills $\boldsymbol\theta_v$ and gives the chosen unramified branch:

$$
R_v^{\mathrm{TW}}/\mathfrak a_vR_v^{\mathrm{TW}}
\simeq\mathcal O[[X_v]],
\tag{4.5}
$$

$$
R_v^{\square,\mathrm{TW}}/\mathfrak a_vR_v^{\square,\mathrm{TW}}
\simeq\mathcal O[[X_v,U_v,V_v]].
\tag{4.6}
$$

Distinct residual eigenvalues are essential in these statements. They make the ordered eigenspace decomposition lift uniquely. With scalar Frobenius, augmentation of an enhanced line-valued problem need not be the original unramified problem, because the extra line may survive after its character becomes trivial.

Combining the auxiliary places gives

$$
R_{Q_N}^{\mathrm{TW,loc}}
\simeq
\Lambda_N[[X_1,\ldots,X_q]],
\tag{4.7}
$$

after ordering $Q_N$, and

$$
R_{Q_N}^{\square,\mathrm{TW,loc}}
\simeq
\Lambda_N[[X_1,U_1,V_1,\ldots,X_q,U_q,V_q]].
\tag{4.8}
$$

These displayed isomorphisms identify coordinates, not places. At another level the symbol $X_i$ refers to the $i$th place in a newly chosen ordering.

### 4.3 The global auxiliary ring

The universal local characters induce the structural homomorphism

$$
\lambda_N:\Lambda_N\longrightarrow R_N.
\tag{4.9}
$$

If the original framed local factors are assembled in $R_{\mathrm{loc}}$, restriction of the global universal deformation also gives

$$
\rho_{\mathrm{loc},N}:R_{\mathrm{loc}}\longrightarrow R_N.
\tag{4.10}
$$

The two images commute because all rings are commutative and both maps are $\mathcal O$-linear. Equivalently, there is a map from the completed tensor product

$$
R_{\mathrm{loc}}\widehat\otimes_{\mathcal O}\Lambda_N
\longrightarrow R_N.
\tag{4.11}
$$

When the auxiliary framed local factors themselves are part of the local base, the source is enlarged by the variables in (4.8). It is useful to distinguish this variable-rich finite-level local base from the fixed old-place ring $R_{\mathrm{loc}}$.

The homomorphism (4.9) sends the group-like element attached to the $i$th chosen generator to the value of tame inertia on the selected local eigenline. It is not merely an action on the universal ring from outside; the diamond character is a coefficient of the universal representation itself.

The tangent local condition at $v\in Q_N$ is the full two-dimensional space

$$
L_v^{\mathrm{TW}}=H^1(K_v,W),
$$

whereas the old condition was its one-dimensional unramified line. The exact Tate orthogonal changes from an unramified line in $H^1(K_v,W')$ to zero. For a killing set,

$$
H^1_{\mathcal L_{Q_N}^\perp}(K,W')=0.
\tag{4.12}
$$

Equation (4.12) is the arithmetic reason a uniformly bounded global presentation exists. It says nothing about a Hecke module until such a module has been constructed.

### 4.4 Augmentation recovers the original problem

Let $\mathfrak a_N R_N$ denote the ideal generated by the image of $\mathfrak a_N$ under (4.9). There is a canonical quotient homomorphism

$$
R_N\longrightarrow R_N/\mathfrak a_NR_N.
\tag{4.13}
$$

Equivalently, in the complete local category,

$$
R_N/\mathfrak a_NR_N
=R_N\widehat\otimes_{\Lambda_N,\epsilon_N}\mathcal O.
$$

The completion adds nothing after quotienting by the finitely generated augmentation ideal, but the tensor notation makes the scalar specialization explicit.

For the enhanced regular branch just described, the quotient represents the original problem. Hence there is a canonical isomorphism

$$
\boxed{R_N/\mathfrak a_NR_N\xrightarrow{\sim}R.}
\tag{4.14}
$$

The proof is worth stating because it identifies the exact hypothesis behind the isomorphism.

**Proposition 4.1 (deformation descent).** Suppose every auxiliary residual Frobenius has distinct eigenvalues in $k$, the enhanced local condition chooses one eigenline, and augmentation makes the universal tame character trivial. Then (4.14) holds. The same statement holds with a fixed collection of compatible frames.

**Proof.** Let $A$ be an Artinian local $\mathcal O$-algebra with residue field $k$. An $A$-valued point of the augmented auxiliary problem has trivial tame character at every $v\in Q_N$, so it is unramified there. Deleting the enhanced eigenspace labels gives an $A$-valued point of $\mathcal D$.

Conversely, an $A$-valued lift in $\mathcal D$ is unramified at $v\in Q_N$. Its Frobenius characteristic polynomial reduces to a product of two coprime linear factors. Idempotent lifting therefore produces a unique ordered direct-sum decomposition lifting the selected residual eigenline and its complement. Giving the selected line the trivial tame character makes the lift an augmented object of $\mathcal D_{Q_N}$. The two constructions are inverse and commute with change of $A$. Thus the represented functors are naturally isomorphic. Uniqueness of representing rings gives (4.14). Compatible frames are simply carried along. $\square$

If the enhanced structure is not uniquely recoverable from the unramified lift, the same construction gives at best a natural transformation and a corresponding map of rings. It does not give an isomorphism. This is why the regular-eigenline hypothesis belongs in the descent theorem rather than in a footnote.

### 4.5 Tangent counts, defects, and relation bounds

Let

$$
\Delta(\mathcal D)
=\dim_kH^1_{\mathcal L}(K,W)
-\dim_kH^1_{\mathcal L^\perp}(K,W')
\tag{4.15}
$$

be the numerical defect of the original problem. Every Taylor–Wiles place enlarges the primal local tangent by one, so

$$
\Delta(\mathcal D_{Q_N})
=\Delta(\mathcal D)+q.
\tag{4.16}
$$

When (4.12) holds, the enlarged primal tangent dimension is

$$
\dim_kH^1_{\mathcal L_{Q_N}}(K,W)
=\Delta(\mathcal D)+q.
\tag{4.17}
$$

For an unpadded killing set, the Poitou–Tate comparison sequence also shows

$$
\dim_kH^1_{\mathcal L_{Q_N}}(K,W)
=\dim_kH^1_{\mathcal L}(K,W).
\tag{4.18}
$$

In particular, if the original problem is balanced, both sides of (4.18) equal $q$. The equality is a consequence of balance and exact killing; it is not the definition of $q$.

Relation counts require more care because the diamond algebra is not smooth over $\mathcal O$. Its $q$ equations in (3.11) must be kept in the base rather than forgotten. Let $B_N$ denote the finite-level local base obtained from

$$
R_{\mathrm{loc}}\widehat\otimes_{\mathcal O}\Lambda_N
$$

by adjoining the fixed number of auxiliary eigenvalue and frame coordinates dictated by the chosen convention. Under the complete, effective, and relative Selmer-complex compatibility hypotheses of Book 68, there is a presentation

$$
B_N[[x_1,\ldots,x_{g_{\mathrm{rel},N}}]]
\twoheadrightarrow R_N
\tag{4.19}
$$

whose number of variables is the exact relative tangent dimension. Neither that dimension nor the corresponding relaxed dual Selmer dimension is automatically constant as the auxiliary primes vary. What the arithmetic argument gives without an additional constant-rank theorem is a uniform bound; fixed presentations are obtained from that bound by honest padding.

The absolute vanishing (4.12) must not be substituted mechanically for the relative relation bound. Placing local rings in the base changes the primal condition to a strict condition there and changes the dual condition to a relaxed one. The resulting relative dual Selmer group can be nonzero even when (4.12) vanishes.

More explicitly, let $T$ be the fixed set of old places in $R_{\mathrm{loc}}$, and let $U_N$ be the set of **all** places whose full local factors are placed in the finite-level base $B_N$. For the convention used in the definition of $B_N$ above,

$$
U_N=T\cup Q_N.
$$

A presentation that leaves the auxiliary smooth coordinates among the relative variables has a different local tangent condition. The diamond algebra is still in its base, so fixing the base kills the tame line at an auxiliary place but retains the unramified line. That partially fixed condition is not modeled by simply putting $U_N=T$ in the strict formulas below. One must use the kernel of the local tangent map to the chosen base: it is zero for a full local factor and is the unramified line for the diamond-only auxiliary factor. The two conventions give equivalent total presentations after all variables and equations are counted, but their relative generator and obstruction ledgers differ and must not be mixed. We use the full-local-factor convention in (4.19)–(4.24).

Let $F_N\subseteq U_N$ be the places at which actual local frames are retained, let $\mathcal L_{Q_N,U_N}^0$ be strict at every place of $U_N$, and put

$$
q_{\mathrm{rel},N}
:=q_{U_N}(\mathcal D_{Q_N})
=\dim_kH^1_{(\mathcal L_{Q_N,U_N}^0)^\perp}(K,W').
\tag{4.20}
$$

This is the relaxed-at-the-actual-base dual dimension of the enlarged problem. It is the Book 68 relative obstruction number for $\mathcal D_{Q_N}$ with the full local-base set $U_N=T\cup Q_N$. It is distinct from the old-base-only number

$$
q_T(\mathcal D_{Q_N})
=\dim_kH^1_{(\mathcal L_{Q_N,T}^0)^\perp}(K,W'),
$$

from the absolute prime-selection number

$$
q(\mathcal D)=\dim_kH^1_{\mathcal L^\perp}(K,W'),
$$

and from the original relative obstruction number

$$
q_T(\mathcal D)
=\dim_kH^1_{(\mathcal L_T^0)^\perp}(K,W').
$$

The absolute number $q(\mathcal D)$ chooses how many Taylor–Wiles primes are needed. The number $q_T(\mathcal D_{Q_N})$ is the old-base cohomological number of Book 68, but it is not by itself a complete relation bound for the exact-level Taylor–Wiles functor over $\mathcal O$: the $q$ finite diamond equations must also be represented in its local obstruction theory or counted separately. Placing the full auxiliary factors in $B_N$ moves those equations and all auxiliary local directions into the base, and $q_{\mathrm{rel},N}$ is then the applicable relative bound in (4.19). For the diamond-only auxiliary base, the finite equations again lie in the base, while the relative local condition at $Q_N$ is the unramified line and, on the enhanced regular branch, recovers the original $q_T(\mathcal D)$. No equality among these numbers is implicit outside the specified comparison.

Write

$$
A_{\mathrm{gauge}}=\operatorname{ad}\bar\rho
$$

for the full infinitesimal change-of-basis module, even in the fixed-determinant problem. In the standard nonempty partially framed convention, the exact relative tangent count is

$$
g_{\mathrm{rel},N}
=h^1_{\mathcal L_{Q_N},U_N^0}(K,W)
+\sum_{v\in F_N}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}),
\tag{4.21}
$$

with the frame correction omitted or adjusted when a different represented convention is used. If $b_{\mathrm{rel},N}$ denotes the minimal number of relations in the corresponding relative presentation, complete effective obstruction theory gives

$$
b_{\mathrm{rel},N}\leq q_{\mathrm{rel},N}.
\tag{4.22}
$$

In that same nonempty partially framed convention, the numerical difference is determined by global duality:

$$
\begin{aligned}
g_{\mathrm{rel},N}-q_{\mathrm{rel},N}
={}&h^0(K,W)-h^0(K,W')\\
&+\sum_{v\notin U_N}
\bigl(\dim_kL_{Q_N,v}-h^0(K_v,W)\bigr)
-\sum_{v\in U_N}h^0(K_v,W)\\
&+\sum_{v\in F_N}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}).
\end{aligned}
\tag{4.23}
$$

The sums range over the controlling set, including archimedean places outside $U_N$. In an unframed Schur convention, the two final gauge terms are omitted; other represented conventions use the same correction as in (4.21). Because the old base and frame convention are fixed, every auxiliary place has the same regular local contribution, and $|Q_N|=q$, the convention-adjusted right side is independent of the identities of the auxiliary primes. This is the precise compatibility between the uniform presentation and the numerical defect.

Constancy of the difference in (4.23) does not make either term constant. Uniform boundedness follows instead from the comparison of dual Selmer structures. The absolute enlarged dual group is zero by (4.12), while the condition defining $q_{\mathrm{rel},N}$ differs only by relaxation at the places whose local directions have been moved into the base. The comparison sequence therefore injects the latter group into

$$
\bigoplus_{v\in U_N}H^1(K_v,W')/L_{Q_N,v}^\perp.
$$

The target dimensions are uniformly bounded: the old summands are fixed and, in the full-local-base convention, there are exactly $q$ auxiliary summands, each of one fixed regular local dimension. Thus the nonnegative integers $q_{\mathrm{rel},N}$ are uniformly bounded. Equation (4.23) then bounds $g_{\mathrm{rel},N}$ as well. Put

$$
q_{\mathrm{rel}}^{\max}=\max_N q_{\mathrm{rel},N},
\qquad
g=\max_N g_{\mathrm{rel},N}.
$$

If (4.23) has constant value $c_{\mathrm{rel}}$, then $g=c_{\mathrm{rel}}+q_{\mathrm{rel}}^{\max}$. Enlarge (4.19) to $g$ variables by sending each extra variable to zero. This adds exactly $g-g_{\mathrm{rel},N}$ linear relations. Since $b_{\mathrm{rel},N}\leq q_{\mathrm{rel},N}$, the padded kernel can be generated by at most

$$
b_{\mathrm{rel},N}+g-g_{\mathrm{rel},N}
\leq q_{\mathrm{rel},N}
+q_{\mathrm{rel}}^{\max}-q_{\mathrm{rel},N}
=q_{\mathrm{rel}}^{\max}
$$

elements. Thus one may take the uniform padded relation bound $b=q_{\mathrm{rel}}^{\max}$. If a separate theorem proves the exact relative dimensions constant, no variable padding is needed.

At the absolute unframed level, the minimal number of topological $\mathcal O$-algebra generators of $R_N$ is the tangent dimension in (4.17), namely $\Delta(\mathcal D)+q$. This statement counts variables, including the $q$ diamond tangent directions. It does not say that the kernel of an absolute power-series presentation has no local equations.

Likewise, a relation-free presentation over $\Lambda_N$ does not mean a relation-free presentation over $\mathcal O$. The $q$ level equations in (3.11) remain present. The safe numerical ledger is

$$
\begin{array}{c|c}
\text{quantity}&\text{source}\\ \hline
q=q(\mathcal D)&\dim_kH^1_{\mathcal L^\perp}(K,W')\\
|Q_N|&q\\
|\Delta_N|&\ell^{Nq}\\
\Delta(\mathcal D_{Q_N})&\Delta(\mathcal D)+q\\
q_T(\mathcal D)&\text{original old-base relative obstruction number}\\
q_T(\mathcal D_{Q_N})&\text{level-$N$ old-base cohomological number; not the full exact-level relation bound by itself}\\
q_{\mathrm{rel},N}=q_{U_N}(\mathcal D_{Q_N})&\text{relative obstruction bound at level }N\\
\text{exact relative variables in (4.19)}&g_{\mathrm{rel},N}\\
\text{exact minimal relations in (4.19)}&b_{\mathrm{rel},N}\leq q_{\mathrm{rel},N}\\
\text{uniform padded variables and relations}&g,\ \leq b.
\end{array}
\tag{4.24}
$$

Every row has a different meaning.

## 5. Hecke algebras, modules, and the comparison map

### 5.1 The acting Hecke algebra

At level $Q_N$, let $M_N$ be the localized integral module selected by the residual eigensystem. Choose a commuting family of Hecke operators away from the bad and auxiliary places, together with the diamond operators and any auxiliary-place operators needed to specify the local branch. Define

$$
\mathbb T_N
=\operatorname{im}\left(
\mathbb T_N^{\mathrm{abs}}\longrightarrow
\operatorname{End}_{\mathcal O}(M_N)
\right).
\tag{5.1}
$$

This image convention gives an injective action map

$$
h_N:\mathbb T_N\hookrightarrow
\operatorname{End}_{\mathcal O}(M_N)
\tag{5.2}
$$

and therefore

$$
\operatorname{Ann}_{\mathbb T_N}(M_N)=0.
\tag{5.3}
$$

If an application instead uses a quotient of an abstract correspondence algebra, faithfulness must be added as a hypothesis. Finiteness of the algebra, commutativity of its generators, and faithfulness of its action are three separate assertions.

Assume first that $M_N$ is finite torsion-free over $\mathcal O$. Then it is finite free over the DVR, and $\mathbb T_N$, being an $\mathcal O$-submodule of its endomorphism algebra, is finite torsion-free and hence finite free over $\mathcal O$. If $M_N$ contains coefficient torsion, $\mathbb T_N$ is still finite when $M_N$ is finite, but flatness over $\mathcal O$ need not follow.

### 5.2 The commuting module structures

There are initially two geometric actions on $M_N$:

$$
d_N:\Lambda_N\longrightarrow\operatorname{End}_{\mathcal O}(M_N)
\tag{5.4}
$$

from diamonds and

$$
h_N:\mathbb T_N\longrightarrow\operatorname{End}_{\mathcal O}(M_N)
\tag{5.5}
$$

from the acting Hecke algebra. We require the diamond operators to lie in the chosen commutative Hecke algebra. Equivalently, there is a structural map

$$
j_N:\Lambda_N\longrightarrow\mathbb T_N
\tag{5.6}
$$

such that

$$
d_N=h_N\circ j_N.
\tag{5.7}
$$

Thus $M_N$ is simultaneously a finite $\Lambda_N$-module and a faithful finite $\mathbb T_N$-module. These actions commute because the first factors through the second. If one chooses not to adjoin diamond operators to $\mathbb T_N$, then $M_N$ instead carries commuting actions of two algebras; the tensor-product algebra they generate must be used in place of $\mathbb T_N$ in the comparison package.

Finite generation has several levels:

- $M_N$ is finite over $\mathcal O$ at each fixed level;
- it is automatically finite over $\Lambda_N$, because any finite set of $\mathcal O$-generators also generates over the larger scalar ring;
- it is finite over $\mathbb T_N$ because $\mathcal O\subseteq\mathbb T_N$ and $M_N$ is finite over $\mathcal O$;
- freeness over $\Lambda_N$ or $\mathbb T_N$ is an additional property.

The standard module axiom is freeness of a fixed rank over $\Lambda_N$. A weaker version uses balancedness. Neither follows from finite generation.

### 5.3 Local–global compatibility and $R_N\to\mathbb T_N$

Suppose a continuous representation

$$
\rho_{\mathbb T_N}:G_{K,S\cup Q_N}
\longrightarrow\operatorname{GL}_2(\mathbb T_N)
\tag{5.8}
$$

has been constructed. A determinant or Cayley–Hamilton family may be used here only after the residually absolutely irreducible upgrade to such a matrix representation has been proved. To invoke universality, one must verify all of the following:

1. reduction of (5.8) is the fixed residual representation;
2. its determinant is the prescribed determinant;
3. at every old bad place it lies on the chosen local deformation branch;
4. at every $v\in Q_N$ it has the selected ordered eigenline and the permitted tame form;
5. the tame character in item 4 agrees with the geometric diamond action under the fixed reciprocity convention.

Only after these checks does universality give

$$
\pi_N:R_N\longrightarrow\mathbb T_N.
\tag{5.9}
$$

The auxiliary diamond square is then

$$
\begin{array}{ccc}
\Lambda_N&\xrightarrow{\lambda_N}&R_N\\
\mathllap{j_N}\searrow&&\swarrow\mathrlap{\pi_N}\\
&\mathbb T_N.&
\end{array}
\tag{5.10}
$$

Commutativity of (5.10) is the finite-level form of local–global compatibility at the auxiliary places. It implies equality of the two diamond actions on $M_N$:

$$
d_N=h_N\circ\pi_N\circ\lambda_N.
\tag{5.11}
$$

At a good place $w\notin S\cup Q_N$, local–global compatibility usually identifies the characteristic polynomial of arithmetic Frobenius with a fixed Hecke polynomial. Those identities construct the trace and determinant coefficients used in (5.8). At an auxiliary place, a good-prime polynomial is not enough: one needs the ordered local factor and its tame character.

### 5.4 Surjectivity and faithfulness are different assertions

The map (5.9) is surjective when the image of $R_N$ contains a set of algebra generators of $\mathbb T_N$. A common sufficient condition is that $\mathbb T_N$ be generated by:

- good-prime operators that occur as traces or determinant coefficients of $\rho_{\mathbb T_N}$;
- the diamond operators, which occur through $\lambda_N$;
- selected auxiliary operators whose eigenvalues are coordinates of the chosen local branch.

Under that stated generating hypothesis,

$$
\boxed{R_N\twoheadrightarrow\mathbb T_N.}
\tag{5.12}
$$

Surjectivity does not say that $R_N$ acts faithfully on $M_N$. If $\mathbb T_N$ acts faithfully, then

$$
\operatorname{Ann}_{R_N}(M_N)=\ker(\pi_N).
\tag{5.13}
$$

Thus faithfulness over $R_N$ is equivalent to injectivity of $\pi_N$, and in the presence of (5.12) it is equivalent to $R_N\simeq\mathbb T_N$. That is precisely the conclusion a later comparison argument is designed to prove. It must not be included among the elementary finite-level consequences.

Nor does faithfulness over $\mathbb T_N$ imply freeness over $\mathbb T_N$. A faithful module can need several generators or have nontrivial syzygies. The Taylor–Wiles system records faithfulness, diamond freeness or balancedness, and Hecke freeness as distinct entries.

## 6. Descent through augmentation

### 6.1 Deformation-ring descent

The deformation comparison is the strongest of the three augmentation statements because it comes from an equality of deformation problems. Proposition 4.1 gives

$$
R_N/\mathfrak a_NR_N\xrightarrow{\sim}R.
\tag{6.1}
$$

More generally, suppose only that trivializing the auxiliary characters defines a closed subproblem whose objects map to the original problem. Contravariance then gives a surjection

$$
R\twoheadrightarrow R_N/\mathfrak a_NR_N.
\tag{6.2}
$$

This is the direction induced by forgetting the enhanced line. A map in the direction desired for the downward comparison,

$$
R_N/\mathfrak a_NR_N\longrightarrow R,
\tag{6.3}
$$

requires a functorial enhancement of every original deformation. It is surjective when that enhancement realizes the original problem as a closed subproblem of the augmented auxiliary problem. The two ring maps are inverse exactly when forgetting and enhancing are inverse natural transformations on every Artinian local coefficient algebra. Consequently no surjection in either direction may be inferred merely from a set-theoretic correspondence of objects.

This criterion separates two possible failures. Some original unramified lifts may admit no compatible enhanced line, or a lift may admit several. Regular residual Frobenius rules out both failures on the selected branch and gives the canonical isomorphism (6.1).

### 6.2 Module coinvariant control

Regard $\mathcal O$ as a $\Lambda_N$-module through augmentation. The diamond coinvariants are

$$
(M_N)_{\Delta_N}
=\mathcal O\otimes_{\Lambda_N}M_N
=M_N/\mathfrak a_NM_N.
\tag{6.4}
$$

A geometric level-lowering construction should give a surjective homomorphism

$$
c_N:M_N\twoheadrightarrow M
\tag{6.5}
$$

on which every diamond element acts trivially. It therefore factors uniquely through

$$
\bar c_N:M_N/\mathfrak a_NM_N\longrightarrow M.
\tag{6.6}
$$

The exact control statement is

$$
\boxed{\ker(c_N)=\mathfrak a_NM_N,}
\tag{6.7}
$$

or equivalently

$$
\boxed{M_N/\mathfrak a_NM_N\xrightarrow{\sim}M.}
\tag{6.8}
$$

Freeness of $M_N$ over $\Lambda_N$ does not construct $c_N$ and does not prove (6.7). It only calculates the source of (6.6). If $M_N$ is free of rank $r$, then its coinvariants are free of rank $r$ over $\mathcal O$. Hence a surjective map (6.6) is an isomorphism whenever $M$ is also $\mathcal O$-free of rank $r$. This is a useful criterion, but the surjection and the rank of $M$ are genuine inputs.

### 6.3 Hecke-algebra control

To compare Hecke algebras, fix compatible abstract Hecke generators at high and base level. Here $\mathfrak a_N\mathbb T_N$ denotes the ideal generated by $j_N(\mathfrak a_N)$. Level lowering sends each retained high-level operator to the corresponding base-level operator, and every diamond operator to $1$. It therefore induces a homomorphism

$$
\theta_N:\mathbb T_N/\mathfrak a_N\mathbb T_N
\longrightarrow\mathbb T.
\tag{6.9}
$$

If the selected base Hecke algebra is generated by the descended operators, (6.9) is surjective:

$$
\mathbb T_N/\mathfrak a_N\mathbb T_N
\twoheadrightarrow\mathbb T.
\tag{6.10}
$$

It need not be injective. Reduction of a faithful image algebra can cease to act faithfully after a nonflat quotient of its scalar ring. An element of $\mathbb T_N$ may act on $M_N$ by a matrix whose entries lie in $\mathfrak a_N$, without belonging to $\mathfrak a_N\mathbb T_N$. Its class then survives algebraically in the source of (6.9) but acts trivially on coinvariants.

Assuming module control (6.8), the action of the source of (6.9) on $M$ has image exactly $\mathbb T$. Therefore

$$
\ker(\theta_N)
=\operatorname{Ann}_{\mathbb T_N/\mathfrak a_N\mathbb T_N}(M).
\tag{6.11}
$$

Consequently

$$
\boxed{
\mathbb T_N/\mathfrak a_N\mathbb T_N\xrightarrow{\sim}\mathbb T
}
\tag{6.12}
$$

if and only if the quotient algebra acts faithfully on $M$. If $M_N$ is finite projective over $\Lambda_N$, a sufficient condition is that the inclusion

$$
\mathbb T_N\hookrightarrow\operatorname{End}_{\Lambda_N}(M_N)
\tag{6.13}
$$

remain injective after tensoring with $\mathcal O$ through augmentation. Projectivity identifies the base change of the endomorphism ring with $\operatorname{End}_{\mathcal O}(M_N/\mathfrak a_NM_N)$. This is a saturation or base-change condition; it is not a consequence of finite flatness over $\mathcal O$.

### 6.4 The exact isomorphism criteria

The three descent statements can now be summarized without ambiguity.

**Theorem 6.1 (augmentation criteria).** Let a level-$N$ datum have maps (4.9), (5.9), a functorial enhancement giving (6.3), and a level-lowering map (6.5). Assume compatible Hecke generators define (6.9).

1. The map $R_N/\mathfrak a_NR_N\to R$ is an isomorphism if and only if the functorial enhancement is a natural isomorphism from the original deformation functor to the augmented auxiliary deformation functor on every Artinian coefficient algebra.
2. The map $M_N/\mathfrak a_NM_N\to M$ is an isomorphism if and only if $c_N$ is surjective and $\ker(c_N)=\mathfrak a_NM_N$.
3. If item 2 holds and $\mathbb T$ is the acting image on $M$, then $\mathbb T_N/\mathfrak a_N\mathbb T_N\to\mathbb T$ is an isomorphism if and only if $\mathbb T_N/\mathfrak a_N\mathbb T_N$ acts faithfully on $M$.

**Proof.** Item 1 is the uniqueness theorem for representing rings applied to the displayed natural transformation. Item 2 is the first isomorphism theorem after factoring $c_N$ through coinvariants. For item 3, compatible generators show that the image of the quotient algebra on $M$ is $\mathbb T$; its kernel is precisely the annihilator. $\square$

When all three maps are isomorphisms, the square

$$
\begin{array}{ccc}
R_N/\mathfrak a_NR_N&\longrightarrow&
\mathbb T_N/\mathfrak a_N\mathbb T_N\\
\downarrow\wr&&\downarrow\wr\\
R&\longrightarrow&\mathbb T
\end{array}
\tag{6.14}
$$

commutes, and the descended action of $R$ on $M$ factors through $\mathbb T$. The square records compatibility; it does not prove that either horizontal arrow is an isomorphism.

## 7. Invariants, coinvariants, and the norm

### 7.1 The two constructions

Let $G$ be a finite group and let $A=\mathcal O[G]$. For an $A$-module $X$, the invariants are

$$
X^G
=\{x\in X:gx=x\text{ for every }g\in G\}
=\operatorname{Hom}_A(\mathcal O,X),
\tag{7.1}
$$

where $\mathcal O$ has the trivial $G$-action. This construction is left exact because it is a Hom.

The coinvariants are

$$
X_G
=\mathcal O\otimes_AX
=X/(g-1:g\in G)X.
\tag{7.2}
$$

This construction is right exact because it is a tensor product. For $G=\Delta_N$, equation (7.2) is exactly

$$
X_G=X/\mathfrak a_NX.
$$

Invariants are a submodule and coinvariants are a quotient. Their variances, exactness properties, and universal meanings differ. An argument that descends level by quotienting by the diamond augmentation ideal is an argument about coinvariants.

### 7.2 The norm comparison

Define the norm element

$$
\mathcal N_G=\sum_{g\in G}[g]\in A.
\tag{7.3}
$$

It satisfies

$$
h\mathcal N_G=\mathcal N_G
\qquad(h\in G)
$$

and

$$
\mathcal N_G(g-1)=0.
$$

Consequently multiplication by $\mathcal N_G$ induces a natural homomorphism

$$
\overline{\mathcal N}_G:X_G\longrightarrow X^G,
\qquad
[x]\longmapsto\mathcal N_Gx.
\tag{7.4}
$$

There is also a natural map

$$
q_X:X^G\longrightarrow X_G
\tag{7.5}
$$

obtained by inclusion followed by quotient. The composites satisfy

$$
q_X\circ\overline{\mathcal N}_G=|G|\operatorname{id}_{X_G},
\qquad
\overline{\mathcal N}_G\circ q_X=|G|\operatorname{id}_{X^G}.
\tag{7.6}
$$

If $|G|$ is a unit in $\mathcal O$, averaging by $|G|^{-1}\mathcal N_G$ shows that both maps are isomorphisms for every $X$. For a Taylor–Wiles diamond group, $|G|$ is a power of $\ell$ and is not a unit. Formula (7.6) then proves no such general identification.

### 7.3 Free and projective diamond modules

The norm nevertheless gives the right comparison on free modules.

**Proposition 7.1.** If $X$ is finite free over $A=\mathcal O[G]$, then (7.4) is an isomorphism of $\mathcal O$-modules. The same holds for a finite projective $A$-module.

**Proof.** For $X=A$, the coinvariants are generated freely over $\mathcal O$ by the class of $1$. An element of the regular module is invariant precisely when all its coefficients in the group basis are equal, so

$$
A^G=\mathcal O\mathcal N_G.
$$

The norm map sends $[1]$ to $\mathcal N_G$ and is an isomorphism. Direct sums prove the free case. Both invariants and coinvariants commute with finite direct sums, and naturality makes the assertion pass to direct summands, proving the projective case. $\square$

For $G=\Delta_N$, the ring $A$ is local. Hence every finite projective $A$-module is free, so projectivity does not enlarge the class in this particular setting. It remains useful to state the projective version because duality and change of coefficients can place the same argument over a semilocal group algebra.

The group algebra is also a symmetric Frobenius $\mathcal O$-algebra. The coefficient-of-the-identity pairing

$$
A\times A\longrightarrow\mathcal O,
\qquad
(a,b)\longmapsto\text{the coefficient of }1\text{ in }ab
\tag{7.7}
$$

identifies $A$ with $\operatorname{Hom}_{\mathcal O}(A,\mathcal O)$ as an $A$-bimodule, with the appropriate inversion on one group action. For projective modules this Frobenius identification, together with the norm, explains why invariants and coinvariants carry dual information. The Frobenius property of the ring alone does not make (7.4) an isomorphism for every module.

### 7.4 Why characteristic dividing the group order is different

There are modules for which invariants and coinvariants even have different dimensions. Let

$$
G=C_\ell\times C_\ell
$$

and work over $k$. Writing $x=g_1-1$ and $y=g_2-1$ gives

$$
k[G]\simeq k[x,y]/(x^\ell,y^\ell).
\tag{7.8}
$$

Let

$$
X=(x,y)
$$

be the maximal ideal of this algebra. Then

$$
X_G=X/(x,y)X=X/X^2
$$

has $k$-dimension two, represented by $x$ and $y$. On the other hand,

$$
X^G=\{m\in X:xm=ym=0\}
$$

is the one-dimensional socle spanned by

$$
x^{\ell-1}y^{\ell-1}.
$$

Thus

$$
\dim_kX_G=2,
\qquad
\dim_kX^G=1.
\tag{7.9}
$$

This example rules out any unqualified passage between the two. In the Taylor–Wiles setting the safe alternatives are:

- use coinvariants because augmentation is a tensor quotient;
- assume diamond projectivity or freeness and use Proposition 7.1;
- work with a perfect group-ring-valued pairing that descends by base change;
- prove a separate norm or cohomological comparison in the particular realization.

## 8. Freeness, balancedness, and uniform size

### 8.1 A genuinely free diamond module

Let

$$
X_N=\Lambda_N^{\oplus r}.
\tag{8.1}
$$

This is the diagnostic model for a free diamond action. It has

$$
\operatorname{rank}_{\Lambda_N}X_N=r,
\qquad
\operatorname{rank}_{\mathcal O}X_N=r\ell^{Nq}.
\tag{8.2}
$$

Its coinvariants are

$$
(X_N)_{\Delta_N}
\simeq\mathcal O^{\oplus r},
\tag{8.3}
$$

and its invariants are

$$
(X_N)^{\Delta_N}
\simeq(\mathcal O\mathcal N_{\Delta_N})^{\oplus r}.
\tag{8.4}
$$

The norm map identifies (8.3) with (8.4). The minimal number of $\Lambda_N$-generators is exactly $r$, and

$$
\operatorname{Tor}_i^{\Lambda_N}(X_N,k)=0
\qquad(i>0).
\tag{8.5}
$$

If $M_N$ satisfies the free diamond axiom, it has precisely these numerical properties. To prove the axiom in a geometric realization one usually shows that auxiliary level structures form a free $\Delta_N$-torsor after the relevant localization and that stabilizers do not introduce extra fixed points. Counting the fibers is only the beginning of that proof.

### 8.2 Equal coefficient rank with a nonfree action

Equal ranks do not determine a group action. Take $q=N=1$, so

$$
\Delta_1\simeq C_\ell,
\qquad
\operatorname{rank}_{\mathcal O}\Lambda_1=\ell.
$$

Let

$$
Y=\mathcal O^{\oplus\ell}
$$

with the trivial $\Delta_1$-action. Then

$$
\operatorname{rank}_{\mathcal O}Y
=\operatorname{rank}_{\mathcal O}\Lambda_1.
\tag{8.6}
$$

After reduction modulo $\varpi^s$, the two finite sets even have the same cardinality:

$$
|Y/\varpi^sY|
=|\Lambda_1/\varpi^s\Lambda_1|
=|\mathcal O/\varpi^s|^\ell.
\tag{8.7}
$$

Nevertheless $Y$ is not free of rank one over $\Lambda_1$. Its coinvariants are all of $Y$ and therefore have $\mathcal O$-rank $\ell$, while the coinvariants of a rank-one free module have rank one. Equivalently, the augmentation ideal annihilates $Y$, so the action is not faithful.

This example is deliberately elementary. It shows why an equality of class-set cardinalities, coefficient ranks, or generic dimensions cannot replace a torsor argument, a basis construction, a projectivity theorem, or an exact descent calculation.

### 8.3 Balanced modules

In cohomological settings a single module need not be diamond-free even when the relevant complex has the correct size. A useful weaker condition can be stated entirely in terms of a minimal presentation.

Let $(A,\mathfrak m_A,k)$ be a Noetherian local ring and let $X$ be a finite $A$-module. Define

$$
d_A(X)
=\dim_k(X/\mathfrak m_AX)
-\dim_k\operatorname{Tor}_1^A(X,k).
\tag{8.8}
$$

We call $X$ **balanced over $A$** when

$$
d_A(X)\geq0.
\tag{8.9}
$$

This module-theoretic word is unrelated to the equality $\Delta(\mathcal D)=0$ for a global deformation problem. The former compares generators with first syzygies; the latter compares primal and dual Selmer dimensions. Whenever both occur, the ambient object will be named.

This definition has a concrete presentation meaning.

**Proposition 8.1 (square-presentation criterion).** A finite $A$-module $X$ is balanced if and only if it admits a presentation

$$
A^d\longrightarrow A^d\longrightarrow X\longrightarrow0
\tag{8.10}
$$

for some $d$.

**Proof.** Let

$$
d_0=\dim_kX/\mathfrak m_AX
$$

and choose a minimal surjection $A^{d_0}\twoheadrightarrow X$ with kernel $K$. Tensoring its exact sequence with $k$ gives

$$
\operatorname{Tor}_1^A(X,k)\xrightarrow{\sim}K/\mathfrak m_AK,
\tag{8.11}
$$

because the induced map $k^{d_0}\to X/\mathfrak m_AX$ is an isomorphism. Thus

$$
d_1:=\dim_k\operatorname{Tor}_1^A(X,k)
$$

is the minimal number of generators of $K$. If $d_1\leq d_0$, choose a surjection $A^{d_0}\twoheadrightarrow K$, padding a minimal generating set with zeros, and compose with $K\hookrightarrow A^{d_0}$. This gives (8.10) with $d=d_0$.

Conversely, from any square presentation with $d$ generators, first replace the second map by a minimal surjection with $d_0\leq d$. Its kernel is generated by at most $d$ elements, and canceling every unit entry in a presentation matrix removes one source and one target summand. A minimal square-or-smaller presentation remains, so $d_1\leq d_0$. Hence $d_A(X)\geq0$. $\square$

A finite free module of rank $r$ is balanced with defect $r$. Balancedness is strictly weaker than freeness: (8.10) does not say that the first map is zero, injective, or given by a regular matrix. In a Taylor–Wiles system the two common module hypotheses are therefore:

$$
\text{strong: }M_N\text{ is }\Lambda_N\text{-free of rank }r,
\tag{8.12}
$$

or

$$
\text{weak: }M_N\text{ is balanced over }\Lambda_N
\text{ with a uniform square size }d.
\tag{8.13}
$$

The weak condition is designed for two-term cohomological phenomena. If the natural object occupies a longer cohomological range, it should be retained as a bounded complex rather than forced into (8.13).

### 8.4 Uniform ranks, cardinalities, and generator counts

Uniformity means uniformity in the correct scale. For a free diamond system of rank $r$,

$$
\operatorname{rank}_{\mathcal O}M_N
=r|\Delta_N|
=r\ell^{Nq},
\tag{8.14}
$$

so the coefficient rank is supposed to grow with $N$. The normalized rank

$$
\frac{\operatorname{rank}_{\mathcal O}M_N}{|\Delta_N|}=r
\tag{8.15}
$$

is constant. For every $s\geq1$,

$$
|M_N/\varpi^sM_N|
=|\mathcal O/\varpi^s|^{r\ell^{Nq}}.
\tag{8.16}
$$

At augmentation, (8.14) collapses to

$$
\operatorname{rank}_{\mathcal O}(M_N/\mathfrak a_NM_N)=r.
\tag{8.17}
$$

Thus exact module control forces $\operatorname{rank}_{\mathcal O}M=r$.

For a balanced system, the appropriate uniform quantities are

$$
d_{0,N}=\dim_kM_N/\mathfrak m_{\Lambda_N}M_N,
\qquad
d_{1,N}=\dim_k\operatorname{Tor}_1^{\Lambda_N}(M_N,k),
\tag{8.18}
$$

together with bounds

$$
d_{1,N}\leq d_{0,N}\leq d
\tag{8.19}
$$

independent of $N$. Uniform boundedness, rather than equality of coefficient ranks, makes it possible to place presentations in a common finite set at every fixed precision.

The deformation-side uniform quantities are the fixed cardinality $q=q(\mathcal D)$, the defect formula (4.16), and uniform padded bounds $g$ and $b$. In the full-local-factor convention of Section 4.5, the exact relative counts $g_{\mathrm{rel},N}$, $q_{\mathrm{rel},N}$, and $b_{\mathrm{rel},N}$ may vary with $N$ even though (4.23) fixes their numerical difference. A system should record which counts are exact minima and which are padded upper bounds. Minimality is intrinsic; a uniform padded presentation is a choice made for comparison.

## 9. Fixed presentations of the finite levels

### 9.1 The diamond presentation $S_\infty$

The first common source has already been constructed:

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]],
\qquad
S_\infty\twoheadrightarrow\Lambda_N
\tag{9.1}
$$

with kernel $\mathfrak c_N$. The composite

$$
S_\infty\xrightarrow{\alpha_N}\Lambda_N
\xrightarrow{\lambda_N}R_N
\tag{9.2}
$$

places the diamond coefficients of every $R_N$ under one power-series source. Similarly, the action on $M_N$ is the composite

$$
S_\infty\longrightarrow\Lambda_N
\longrightarrow\operatorname{End}_{\mathcal O}(M_N).
\tag{9.3}
$$

The ideal $\mathfrak c_N$ acts by zero at level $N$, while $\mathfrak a_\infty$ specializes to the augmentation ideal. These two ideals serve different purposes:

$$
\mathfrak c_N:\text{ impose finite diamond level},
\qquad
\mathfrak a_\infty:\text{ impose trivial diamond character}.
\tag{9.4}
$$

### 9.2 A fixed deformation presentation $R_\infty$

Let $s_{\mathrm{aux}}=q$ when the unframed auxiliary local factors (4.7) are used, and let $s_{\mathrm{aux}}=3q$ when the framed factors (4.8) are used. Thus $s_{\mathrm{aux}}$ counts the auxiliary smooth coordinates after the diamond coordinates have been removed. Suppose the relative presentation (4.19) requires at most $g$ further global generators over the resulting finite-level local base. Put

$$
G=s_{\mathrm{aux}}+g,
$$

or choose a larger fixed value of $G$ if honest padding is desired. Define

$$
R_\infty
=R_{\mathrm{loc}}[[z_1,\ldots,z_q,x_1,\ldots,x_G]].
\tag{9.5}
$$

Here and throughout this chapter, $g$ uses the first convention of Section 4.5: the auxiliary smooth coordinates lie in $B_N$ and are therefore excluded from $g$. Under the alternative convention, those $s_{\mathrm{aux}}$ coordinates are already counted among the relative variables and must not be added a second time.

There is a fixed structural map

$$
S_\infty\longrightarrow R_\infty
\tag{9.6}
$$

that sends each $z_i$ to the identically named variable. A **compatible finite-level presentation** is a chosen surjection

$$
\beta_N:R_\infty\twoheadrightarrow R_N
\tag{9.7}
$$

such that:

1. its restriction to $R_{\mathrm{loc}}$ is (4.10);
2. $\beta_N(z_i)=\lambda_N([\delta_{N,i}]-1)$;
3. the diagram with (9.2) and (9.6) commutes;
4. $\mathfrak c_NR_\infty\subseteq\ker(\beta_N)$, where the extension uses (9.6).

The variables $x_i$ consist first of the uniformly enumerated auxiliary eigenvalue coordinates, then of the auxiliary frame coordinates if retained, and finally of the $g$ remaining global relative generators. If fewer than $G$ are needed at a particular level, the unused variables are sent to zero or to chosen dependent elements.

One can equivalently absorb the $z_i$ into a ring denoted $R_{\mathrm{loc}}[[y_1,\ldots,y_{q+G}]]$ and specify the $S_\infty$-map separately. Formula (9.5) is preferable because it visibly distinguishes diamond coordinates from every other variable.

### 9.3 Lifting the diamond coordinates

Why can the maps (9.7) be chosen? The structural map $R_{\mathrm{loc}}\to R_N$ and the $q$ specified diamond elements already determine the images of the first coordinates. The finite-level local base contributes $s_{\mathrm{aux}}$ further smooth coordinates, and the relative cotangent calculation contributes at most $g$ global generators beyond that base. Choose and order lifts of all these elements, and send $x_1,\ldots,x_G$ to them. The universal mapping property of a power-series ring gives (9.7), and topological Nakayama gives surjectivity.

Every step contains a choice:

- an ordering and generators for $\Delta_N$;
- lifts of cotangent vectors;
- an assignment of auxiliary smooth coordinates to the fixed $x_i$;
- padding when a nonminimal bound is used.

The resulting map is a presentation, not an arithmetic morphism from an infinite-level deformation problem. Different choices are related by continuous coordinate changes when both are minimal; padded presentations can also contain removable linear variables.

The induced augmented presentation is

$$
R_\infty/\mathfrak a_\infty R_\infty
=R_{\mathrm{loc}}[[x_1,\ldots,x_G]]
\twoheadrightarrow R.
\tag{9.8}
$$

Compatibility with (6.1) means that reducing (9.7) by $\mathfrak a_\infty$ gives (9.8), up to the chosen coordinate identification.

### 9.4 Minimality versus uniform padding

Let $G_N^{\min}$ be the dimension of the relative cotangent space of $R_N$ over the fixed old-place base after the prescribed diamond coordinates have been removed. It counts both the auxiliary smooth directions and the remaining global directions. A minimal presentation of the form (9.7) uses exactly $G_N^{\min}$ variables. Uniform patchable presentations require only a bound

$$
G_N^{\min}\leq G.
\tag{9.9}
$$

If the tangent formula proves equality independent of $N$, one should take that exact value. If it proves only a bound, padding is honest so long as it is recorded.

The same distinction applies to relations. Begin with an exact relative presentation

$$
R_N\simeq
B_N[[x_1,\ldots,x_{g_{\mathrm{rel},N}}]]
/(f_{N,1},\ldots,f_{N,b_{\mathrm{rel},N}}).
$$

Passing to a fixed source with $g\geq g_{\mathrm{rel},N}$ variables requires adding $g-g_{\mathrm{rel},N}$ variables **and** the same number of linear relations killing them. It is not accomplished by merely appending zero relations. Section 4.5 proves that, with the specific bounds there, the resulting kernel still has at most $b$ generators. Only after the source has been fixed may one append zero entries to a chosen generating list to make its displayed length exactly $b$; doing so does not make $b$ the minimal relation count. A later depth argument may use the number of equations in a chosen regular ambient ring, so it must know whether it has an exact height statement, an upper bound, or merely a padded display.

In the main convention of Section 9.2, the chosen coordinates identify

$$
R_\infty/\mathfrak c_NR_\infty
\simeq B_N[[y_1,\ldots,y_g]].
\tag{9.10}
$$

After the simultaneous padding above, the induced kernel in (9.10) is generated by at most $b$ elements. Equivalently, generators may be chosen so that

$$
\ker(\beta_N)
=\mathfrak c_NR_\infty+(f_{N,1},\ldots,f_{N,b}),
\tag{9.11}
$$

where some displayed $f_{N,i}$ may be zero only after all unused source variables have already been killed by genuine linear relations. Thus the full kernel has the $q$ fixed finite-level equations in $\mathfrak c_N$ and at most $b$ additional relative equations; $b$ does not count the level equations twice.

The numerical defect from (4.16) controls the difference between appropriate generator and obstruction bounds. It does not assert that the displayed relations form a regular sequence. That conclusion belongs to the later commutative-algebra argument.

## 10. Nonnested auxiliary sets and comparison across levels

### 10.1 Why nested Taylor–Wiles sets cannot persist

For a fixed finite place $v$, the integer

$$
a_v=v_\ell(q_v-1)
$$

is finite. The congruence $q_v\equiv1\pmod{\ell^N}$ holds only when $N\leq a_v$. Therefore one fixed nonempty set of places cannot satisfy the level condition for arbitrarily large $N$.

If every $Q_N$ has the same finite cardinality $q$ and

$$
Q_N\subseteq Q_{N+1},
$$

then equality of cardinalities forces $Q_N=Q_{N+1}$. Repeating this would force every place in $Q_1$ to satisfy congruences of unbounded depth, which is impossible. Hence a nonempty Taylor–Wiles sequence of fixed cardinality cannot be nested indefinitely.

This elementary observation has a major categorical consequence: restriction of ramification sets does not produce a tower

$$
\cdots\longrightarrow R_{N+1}\longrightarrow R_N\longrightarrow\cdots.
$$

The two global rings represent deformation problems with different new ramification places. Neither problem is naturally a subproblem of the other.

### 10.2 A worked pair of nonnested levels

Take $q=2$ and choose disjoint auxiliary sets

$$
Q_2=\{v_1,v_2\},
\qquad
Q_3=\{w_1,w_2\}.
\tag{10.1}
$$

Choose generators

$$
\delta_{2,i}\in\Delta_{v_i}(2),
\qquad
\delta_{3,i}\in\Delta_{w_i}(3)
\qquad(i=1,2).
$$

Then the common ring

$$
S_\infty=\mathcal O[[z_1,z_2]]
$$

has quotient maps

$$
z_i\longmapsto[\delta_{2,i}]-1
\quad\text{into }\mathcal O[\Delta_{Q_2}],
\tag{10.2}
$$

and

$$
z_i\longmapsto[\delta_{3,i}]-1
\quad\text{into }\mathcal O[\Delta_{Q_3}].
\tag{10.3}
$$

The standard quotient $S_3\twoheadrightarrow S_2$ can be transported to a chosen algebra map

$$
\mathcal O[\Delta_{Q_3}]
\longrightarrow\mathcal O[\Delta_{Q_2}],
\qquad
[\delta_{3,i}]\longmapsto[\delta_{2,i}].
\tag{10.4}
$$

Map (10.4) compares two abstractly presented group algebras. It does not arise from a map $k(w_i)^\times\to k(v_i)^\times$, from a relation between decomposition groups, or from a level-forgetting morphism. In particular, it supplies no map $R_3\to R_2$ and no map $M_3\to M_2$.

Likewise, chosen surjections

$$
R_\infty\twoheadrightarrow R_2,
\qquad
R_\infty\twoheadrightarrow R_3
\tag{10.5}
$$

place both rings under one ambient presentation. The kernels are unrelated ideals subject to common numerical bounds. A common source is not a transition arrow between its quotients.

### 10.3 Presentation maps are not arithmetic transition maps

There are three increasingly strong notions of comparison.

1. **Common source.** There are surjections $S_\infty\to\Lambda_N$ and $R_\infty\to R_N$ for every $N$.
2. **Chosen presentation comparison.** Standard quotient maps among the $S_N$ are transported through chosen coordinates, and finite truncations of the $R_N$ and $M_N$ are identified after passing to a subsequence.
3. **Genuine transition.** There are maps between the actual rings, modules, or geometric spaces, compatible with their arithmetic moduli meanings.

The first is part of an ordinary Taylor–Wiles presentation system. The second is a device for arranging inverse systems of finite shadows. The third occurs only when additional geometry supplies it. A proof may not move from one row to the next without new data.

Even a chosen algebra map $\Lambda_{N+1}\to\Lambda_N$ need not extend to $R_{N+1}\to R_N$. An extension would have to send the universal representation ramified at $Q_{N+1}$ to a deformation allowed to ramify at $Q_N$, and there is no reason for such a representation to become unramified at the places of $Q_{N+1}\setminus Q_N$ or to acquire ramification at $Q_N\setminus Q_{N+1}$.

### 10.4 Common finite shadows and pseudo-transitions

Common presentations are enough to manufacture coherent finite comparison objects without inventing arithmetic maps. We describe the construction precisely.

Let

$$
\mathfrak n_\infty=(\varpi,z_1,\ldots,z_q)\subset S_\infty
$$

and let $\mathfrak m_\infty$ be the maximal ideal of $R_\infty$. For $d\geq1$, put

$$
C_d=S_\infty/\mathfrak n_\infty^d,
\qquad
A_d=R_\infty/\mathfrak m_\infty^d.
\tag{10.6}
$$

These are finite rings because $k$ is finite. For every fixed $d$, one has

$$
\mathfrak c_N\subseteq\mathfrak n_\infty^d
\tag{10.7}
$$

for all sufficiently large $N$. Indeed, in

$$
(1+z_i)^{\ell^N}-1
=\sum_{j=1}^{\ell^N}\binom{\ell^N}{j}z_i^j,
$$

the terms with $j\geq d$ already lie in $\mathfrak n_\infty^d$, while for each fixed $j<d$ the $\varpi$-adic valuations of the binomial coefficients tend to infinity with $N$.

For a level $N$ with a presentation $\beta_N$, define its precision-$d$ shadows by

$$
R_{N,d}=R_N/\mathfrak m_\infty^dR_N,
\tag{10.8}
$$

$$
M_{N,d}=M_N/\mathfrak m_\infty^dM_N,
\tag{10.9}
$$

and let $\mathbb T_{N,d}$ be the image of $\mathbb T_N$ on $M_{N,d}$. The ideal in (10.8) means the image under $\beta_N$, and the action in (10.9) is the composite $R_\infty\to R_N\to\operatorname{End}(M_N)$.

Because the structural map $S_\infty\to R_\infty$ carries $\mathfrak n_\infty$ into $\mathfrak m_\infty$, one has

$$
\mathfrak n_\infty^dM_N
\subseteq\mathfrak m_\infty^dM_N.
$$

Thus, if $M_N$ is generated by at most $d_0$ elements over $S_\infty$, then $M_{N,d}$ is a quotient of the one fixed finite module $C_d^{d_0}$. This inclusion is the small but essential link between the ring precision in (10.8) and the module finiteness used below.

If augmentation maps are retained in the finite diagram, their targets must be truncated too. The quotient maps $R_N\to R$, $\mathbb T_N\to\mathbb T$, and $M_N\to M$ carry the displayed precision ideal into the corresponding $d$th maximal-ideal filtration at base level, so they induce maps to the finite shadows of $R$, $\mathbb T$, and $M$. An untruncated base object is not silently inserted into a finite diagram.

Assume the rings are quotients of the fixed $R_\infty$ and the modules have at most $d_0$ generators over $S_\infty$. For fixed precision $d$, there are only finitely many isomorphism classes of the resulting diagrams

$$
C_d\longrightarrow R_{N,d}\longrightarrow\mathbb T_{N,d}
\longrightarrow\operatorname{End}(M_{N,d}),
\tag{10.10}
$$

including any fixed finite list of named operators and any additional structure that is actually defined on these quotients. Here the endomorphism ring records the action on the named module; it is not an extra object required to admit a surjective reduction map, since an arbitrary endomorphism need not preserve the next filtration kernel. Reduction data consist of the quotient maps on $C_d$, $R_{N,d}$, $\mathbb T_{N,d}$, and $M_{N,d}$ together with compatibility of the named actions. The reason for finiteness is elementary: $R_{N,d}$ is a quotient of the finite ring $A_d$, $M_{N,d}$ is a quotient of the finite module $C_d^{d_0}$, and there are only finitely many ideals, submodules, homomorphisms, and functions on finite sets.

An infinite away-from-bad-set Hecke family cannot be included all at once in this finite-pigeonhole assertion. Enumerate the common labels as $t_1,t_2,\ldots$ and, at precision $d$, retain only $t_1,\ldots,t_d$. If a label is undefined at a finite number of levels because its place belongs to $Q_N$, first pass beyond those levels. Diagonalizing over the pairs consisting of a precision and a label then preserves every named operator eventually. Equivalently, one may begin with a proved uniformly finite generating family. Pairings require the separate truncation check of Section 12.4; a bilinear form on $M_N$ does not automatically descend to the quotient in (10.9).

The compactness assertion can now be stated without suppressing either its hypotheses or its exactness boundary.

**Proposition 10.1 (coherent finite-shadow stabilization).** Suppose that:

1. every $R_N$ is a quotient of the fixed complete local ring $R_\infty$;
2. every $M_N$ is generated by at most $d_0$ elements over $S_\infty$;
3. for precision $d$, only finitely many named operators and structural maps are retained, and each retained structure descends to (10.8)--(10.10);
4. the residue field $k$ is finite.

Then there are a cofinal sequence $N_1<N_2<\cdots$, finite diagrams $\mathscr D_d$, and surjective reduction maps

$$
\mathscr D_{d+1}\twoheadrightarrow\mathscr D_d
\tag{10.11}
$$

such that, for every $j\geq d$, the precision-$d$ diagram at level $N_j$ is isomorphic to $\mathscr D_d$. The isomorphisms can be chosen to commute with reduction and to preserve every retained label. If a pairing or a short exact sequence is to be part of $\mathscr D_d$, its descent and its claimed perfectness or exactness must be verified before it is included.

**Proof.** For fixed $d$, the ring $A_d$ is finite. Its quotients form a finite set. The module $C_d^{d_0}$ is finite, so it has only finitely many quotients, and between any fixed finite rings and modules there are only finitely many homomorphisms. The acting image $\mathbb T_{N,d}$ and every finite list of named actions therefore range over finitely many possibilities. Hence the marked precision-$d$ diagrams have only finitely many isomorphism classes.

Choose an infinite set of levels on which the marked precision-one diagram is constant. Inside it choose an infinite subset on which the marked precision-two diagram, together with its reduction to precision one, is constant. Continue inductively. Taking the diagonal levels gives $N_1<N_2<\cdots$. At stage $d+1$, choose the representative so that its reduction is the representative already chosen at stage $d$; this gives (10.11) and compatible isomorphisms from all later selected levels.

The reduction maps on the displayed rings and modules are surjective because they are quotient maps. That fact does not make every named short exact sequence remain exact: tensoring with a quotient is right exact but can create a left-hand $\operatorname{Tor}_1$. Likewise, a pairing on $M_N$ need not annihilate the two precision kernels. Exact sequences and pairings may therefore be marked in the finite diagrams only after the relevant Tor vanishing, strictness, or pairing-kernel condition has been checked. $\square$

The maps in (10.11) are **pseudo-transitions** for the original levels: they are transition maps among stabilized presentation shadows, built using selected isomorphisms. They are not maps from $R_{N_{j+1}}$ to $R_{N_j}$ or from $M_{N_{j+1}}$ to $M_{N_j}$. Recording this distinction is enough for a later inverse-limit construction. No ultrafilter is needed when the coefficient residue field is finite and the stated uniform bounds hold.

### 10.5 When genuine transition maps may be added

Sometimes one begins with a genuinely nested tower of geometric levels and finite quotient groups $D_N$, independently of the Taylor–Wiles prime sets. Then pullback, trace, or quotient maps can give actual transitions. A transitioned system may include maps

$$
\Lambda_{N+1}\twoheadrightarrow\Lambda_N,
\qquad
R_{N+1}\longrightarrow R_N,
\qquad
\mathbb T_{N+1}\longrightarrow\mathbb T_N,
\qquad
M_{N+1}\longrightarrow M_N,
\tag{10.12}
$$

subject to commutative diagrams and transitivity. Each map must be justified by its own moduli or correspondence construction. The mere existence of the standard quotient $S_{N+1}\to S_N$ justifies only the first comparison after choices.

For the independent Taylor–Wiles sets supplied by prime selection, the presentation-compatible formulation is the honest one. It contains exactly the comparability needed later and no fictitious arithmetic tower.

## 11. Framed and unframed systems

### 11.1 Why frames enter

An unframed deformation class forgets a basis up to strict conjugacy. A framed deformation retains enough basis data to remove that quotient and is therefore easier to represent and to compare with products of local deformation rings. The cost is a collection of smooth coordinates with no arithmetic meaning of their own.

Let the residual representation have dimension $d$, and recall

$$
A_{\mathrm{gauge}}=\operatorname{ad}\bar\rho
$$

be the full infinitesimal change-of-basis module, even when determinant is fixed. If $T$ is a nonempty set of framed places and a $T$-framed object means a global lift with one lifted local basis at every $v\in T$, modulo simultaneous global strict conjugacy, then the tangent fiber over the unframed functor has dimension

$$
c_T=d^2|T|-h^0(K,A_{\mathrm{gauge}}).
\tag{11.1}
$$

Indeed, the $|T|$ frames contribute $d^2|T|$ infinitesimal matrix coordinates. A global strict change of basis contributes $d^2$ directions, while its invariant subspace of dimension $h^0(K,A_{\mathrm{gauge}})$ was already absent from the coboundary space. The net difference from the unframed tangent is (11.1).

For an absolutely irreducible rank-two representation,

$$
h^0(K,\operatorname{ad}\bar\rho)=1,
$$

so

$$
c_T=4|T|-1.
\tag{11.2}
$$

With one global frame, this gives the familiar three variables. Formula (11.2) must not be replaced by three variables for every framed place.

Under the scalar-centralizer and representability hypotheses that make the frame torsor smooth, there is a noncanonical isomorphism

$$
R_N^{\square_T}
\simeq R_N[[w_1,\ldots,w_{c_T}]].
\tag{11.3}
$$

The same formula holds at the base level with $R$ in place of $R_N$, and augmentation carries the left side of (11.3) to the base framed ring.

### 11.2 The variable ledger

Several types of variables can occur simultaneously, and none should be counted twice.

| Source | Number in the rank-two regular branch | Meaning |
|---|---:|---|
| diamond factor at each $v\in Q_N$ | $1$ finite direction | tame character, represented by $\Lambda_N$ |
| unframed auxiliary local ring | $1$ smooth variable | selected Frobenius eigenvalue $X_v$ |
| framed auxiliary local ring beyond unframed | $2$ smooth variables | positions $U_v,V_v$ of the lifted eigenlines |
| one global full frame | $3$ smooth variables | strict global basis directions |
| $T$ local frames modulo global conjugacy | $4|T|-1$ smooth variables | formula (11.2) |
| global variables over the chosen local base | $g_{\mathrm{rel},N}$ | strict Selmer tangent plus centralizer correction |

The one-global-frame row is the case $|T|=1$ of the partial-framing row, not an additional summand. Likewise, the framed auxiliary local coordinates belong inside the local base when those places are included there; the global relative count then measures only what remains over that base.

If the factor (4.4) is included inside the local base, its $X_v,U_v,V_v$ variables are already present and must not be added again among the global variables. If the auxiliary places are not locally framed, only $X_v$ belongs to their unframed factor. The finite diamond direction is never one of the smooth $X_v,U_v,V_v$ coordinates.

The global relative count must use the actual finite-level base from Section 4.5. With $U_N$ the places whose full local factors lie in that base and, in the standard nonempty partially framed convention, $F_N\subseteq U_N$ the places carrying retained frames, it is

$$
g_{\mathrm{rel},N}
=h^1_{\mathcal L_{Q_N},U_N^0}(K,W)
+\sum_{v\in F_N}h^0(K_v,A_{\mathrm{gauge}})
-h^0(K,A_{\mathrm{gauge}}).
\tag{11.4}
$$

Here $U_N^0$ means that the tangent condition is made strict at every place whose full local ring has been put in the base. Formula (11.4) is (4.21), repeated to make the framing ledger explicit. In an unframed Schur convention the two gauge-invariant terms are omitted; other represented conventions use their own exact correction. For the full auxiliary base used in Section 4.5, $U_N=T\cup Q_N$. If the base contains only the old full local factors together with the diamond subalgebra at $Q_N$, one must instead use the partially fixed local condition that retains the unramified line, as explained before (4.20); substituting $U_N=T$ into (11.4) would count the tame direction twice. The convention-appropriate relative count, not the absolute tangent dimension (4.17), is the one used in the presentation.

### 11.3 Removing smooth variables

The word “harmless” has a precise scope. If

$$
B\simeq A[[w_1,\ldots,w_c]],
\tag{11.5}
$$

then $w_1,\ldots,w_c$ form a $B$-regular sequence and

$$
B/(w_1,\ldots,w_c)\simeq A.
\tag{11.6}
$$

For a finite $A$-module $X$, the extended module

$$
X_B=B\widehat\otimes_AX
$$

satisfies

$$
\operatorname{depth}_B X_B
=\operatorname{depth}_A X+c.
\tag{11.7}
$$

Conversely, specializing a sequence known to be $X_B$-regular decreases depth by exactly $c$. Thus smooth frame variables can be added to make deformation functors representable and removed after all dimension and depth statements have been shifted by their exact number.

The module in this statement is the scalar extension $X_B$, or another module on which the frame variables have separately been proved regular. A ring isomorphism $B\simeq A[[w_1,\ldots,w_c]]$ alone gives no module regularity. In particular, if an original automorphic module $M$ is merely viewed as a $B$-module through the specialization $B\twoheadrightarrow A$, then every $w_i$ annihilates $M$ and the sequence is not $M$-regular. A framed module argument must therefore use a compatible scalar extension such as $B\widehat\otimes_A M$, or prove the needed regularity by an independent theorem, before applying the depth shift.

It is unsafe to call variables harmless when their number varies with $N$, when the specialization sequence is not regular on the module, or when a putative frame coordinate actually selects a different local component. A Taylor–Wiles system fixes the framing convention and its count once.

### 11.4 Branch compatibility

At every old place in the ramification set, the local component used in $R_{\mathrm{loc}}$ must be independent of $N$. If level $N$ uses one irreducible component of a local deformation ring and level $N+1$ uses another, there is no fixed local base and no reason for the same $R_\infty$ to control both.

At a Taylor–Wiles place, switching the ordered residual eigenline changes the enhanced local problem. Because the two lines are regular, swapping them gives an isomorphic local ring after inverting the diamond character as in (3.21) and replacing the Frobenius coordinate accordingly. A presentation system may absorb this change only if it records the coordinate automorphism. Silently treating the two branches as identical reverses the diamond action in (5.10).

Frames do not repair incompatible components. They remove conjugation ambiguity within a chosen component. Component selection, determinant normalization, reciprocity normalization, and framing are four different pieces of local data.

## 12. Duality and adjoints

### 12.1 Coefficient-valued and group-ring-valued pairings

Pairings serve two purposes in a Taylor–Wiles system. They control adjoints of Hecke operators, and they prevent duality from degenerating as the auxiliary level varies. There are two useful strengths.

An $\mathcal O$-valued pairing between finite free modules is a bilinear map

$$
b_N:M_N\times M_N'\longrightarrow\mathcal O
\tag{12.1}
$$

that is **perfect** when it induces isomorphisms

$$
M_N\xrightarrow{\sim}\operatorname{Hom}_{\mathcal O}(M_N',\mathcal O),
\qquad
M_N'\xrightarrow{\sim}\operatorname{Hom}_{\mathcal O}(M_N,\mathcal O).
\tag{12.2}
$$

The second module may use the dual coefficient system and inverse central character. A self-pairing is an extra identification $M_N'=M_N$, not a consequence of perfectness.

For clean augmentation, a stronger group-ring-valued pairing is preferable. Let

$$
\iota_N:\Lambda_N\longrightarrow\Lambda_N,
\qquad
[\delta]\longmapsto[\delta^{-1}]
\tag{12.3}
$$

be the standard involution. A pairing

$$
H_N:M_N\times M_N'\longrightarrow\Lambda_N
\tag{12.4}
$$

is sesquilinear when

$$
H_N(ax,y)=aH_N(x,y),
\qquad
H_N(x,ay)=H_N(x,y)\iota_N(a).
\tag{12.5}
$$

It is $\Lambda_N$-perfect when the induced map

$$
M_N'\xrightarrow{\sim}
\operatorname{Hom}_{\Lambda_N}(M_N,\Lambda_N)
\tag{12.6}
$$

is an isomorphism after twisting the scalar action by $\iota_N$. Such a pairing in particular forces both modules to have the same projective rank when one is projective.

### 12.2 Diamond inversion and Hecke adjoints

For an $\mathcal O$-valued pairing, the natural diamond compatibility is

$$
b_N(\delta x,y)=b_N(x,\delta^{-1}y).
\tag{12.7}
$$

It reflects reversal of a deck transformation in a finite correspondence. It also shows directly that an $\mathcal O$-valued pairing pairs coinvariants on one side with invariants on the other: if $y$ is invariant, then

$$
b_N((\delta-1)x,y)=0.
$$

For a Hecke operator $t$ on $M_N$, an adjoint $t^*$ on $M_N'$ satisfies

$$
b_N(tx,y)=b_N(x,t^*y),
\tag{12.8}
$$

or the analogous identity for $H_N$. Perfectness makes $t^*$ unique. The adjoint may be an inverse double coset or a central-unit multiple of the named operator. At an oriented auxiliary level it can be a different operator. Accordingly, a system records an involution or an isomorphism

$$
*:\mathbb T_N\xrightarrow{\sim}\mathbb T_N'
\tag{12.9}
$$

and the identity (12.8). It calls an operator self-adjoint only when $t^*=t$ under the selected normalization.

If the same module occurs on both sides and every chosen Hecke generator is self-adjoint, (12.2) gives a $\mathbb T_N$-equivariant self-duality. This does not make $M_N$ free over $\mathbb T_N$, and it does not make $\mathbb T_N$ Gorenstein without an additional rank-one statement.

### 12.3 Descent of perfect pairings

Suppose (12.4) is $\Lambda_N$-perfect. Applying augmentation gives

$$
\overline H_N:
(M_N/\mathfrak a_NM_N)
\times
(M_N'/\mathfrak a_NM_N')
\longrightarrow\mathcal O,
\tag{12.10}
$$

defined by

$$
\overline H_N([x],[y])
=\epsilon_N(H_N(x,y)).
\tag{12.11}
$$

Sesquilinearity makes (12.11) well defined. If $M_N$ and $M_N'$ are finite projective over $\Lambda_N$, base change of (12.6) along $\epsilon_N$ shows that (12.10) is perfect. Under module control it therefore becomes a perfect pairing

$$
M\times M'\longrightarrow\mathcal O.
\tag{12.12}
$$

For an $\mathcal O$-valued pairing alone, the immediate descended pairing is between

$$
(M_N)_{\Delta_N}
\quad\text{and}\quad
(M_N')^{\Delta_N}.
\tag{12.13}
$$

Perfectness before descent identifies

$$
(M_N')^{\Delta_N}
\simeq
\operatorname{Hom}_{\mathcal O}
\bigl((M_N)_{\Delta_N},\mathcal O\bigr).
\tag{12.14}
$$

Thus (12.13) is perfect when $(M_N)_{\Delta_N}$ is $\mathcal O$-projective. Without this hypothesis, coefficient torsion in the coinvariants lies in the left radical, so perfectness can fail. Identifying the second term with coinvariants also requires the norm comparison of Proposition 7.1 or another proved theorem. When both modules are diamond-free, the symmetric Frobenius structure of $\Lambda_N$ and the norm produce the desired identification and the descended pairing is perfect. Without projectivity, (7.9) shows that invariants and coinvariants can fail to agree even dimensionally.

Hecke adjointness descends because every diamond becomes $1$, and the quotient maps on the Hecke algebras respect $*$. If $\theta_N$ has a kernel, the descended pairing sees only the acting image $\mathbb T$; it cannot restore invisible elements of $\mathbb T_N/\mathfrak a_N\mathbb T_N$.

### 12.4 Duality data across a presentation system

At different auxiliary levels, pairings live on unrelated modules. Before including them among the finite diagrams of Section 10.4, one must choose quotients on which they are defined.

For a $\Lambda_N$-valued pairing (12.4), the diamond-adic shadows provide a canonical choice. Put

$$
P_{N,d}=M_N/\mathfrak n_\infty^dM_N,
\qquad
P'_{N,d}=M_N'/\mathfrak n_\infty^dM_N'.
$$

For $N$ sufficiently large relative to $d$, equation (10.7) identifies

$$
\Lambda_N/\mathfrak n_\infty^d\Lambda_N\simeq C_d.
$$

The involution preserves $\mathfrak n_\infty^d$, so sesquilinearity makes $H_N$ descend to

$$
P_{N,d}\times P'_{N,d}\longrightarrow C_d.
$$

These are finite modules of uniformly bounded generator number and can be stabilized alongside (10.10). If $H_N$ is $\Lambda_N$-perfect and the modules are projective, base change makes every such descended pairing perfect.

An $\mathcal O$-valued pairing alone does not automatically descend to either the $\mathfrak m_\infty$-adic quotient (10.9) or to both diamond-adic quotients just displayed. It naturally pairs coinvariants with invariants at augmentation, as in (12.13), but an arbitrary intermediate quotient needs a separately specified dual shadow. Thus a presentation-compatible system that retains only coefficient-valued pairings must supply pairing-compatible finite models as extra data; finite-pigeonhole stabilization does not create them.

After such pairing shadows have been chosen, compatibility means that the reduction of the precision-$(d+1)$ pairing equals the precision-$d$ pairing under the selected pseudo-transition isomorphisms.

There is no direct formula

$$
H_{N+1}|_{M_N}=H_N
$$

unless a genuine inclusion or quotient between $M_{N+1}$ and $M_N$ has been constructed. A common normalization of Hecke adjoints, diamond inversion, and base-level descent is enough for a presentation-compatible system.

Uniform group-ring perfectness has useful finite consequences. If $M_N$ is $\Lambda_N$-free of rank $r$, then its dual is free of rank $r$, every diamond-adic pairing shadow above is self-dual in the corresponding sense, and no pairing determinant acquires an unbounded nonunit factor. In geometric applications this uniformity must be checked against stabilizer denominators, polarization degrees, and torsion in cohomology.

## 13. Support, annihilators, depth, and faithfulness

### 13.1 Annihilators from the factorized action

Assume

$$
R_N\xrightarrow{\pi_N}\mathbb T_N
\xrightarrow{h_N}\operatorname{End}_{\mathcal O}(M_N)
\tag{13.1}
$$

with $h_N$ injective. Then

$$
\operatorname{Ann}_{R_N}(M_N)=\ker(\pi_N).
\tag{13.2}
$$

The proof is immediate but decisive: an element of $R_N$ kills $M_N$ exactly when its image in the faithfully acting algebra $\mathbb T_N$ is zero. If $\pi_N$ is surjective, then

$$
R_N/\operatorname{Ann}_{R_N}(M_N)
\simeq\mathbb T_N.
\tag{13.3}
$$

Thus $M_N$ is faithful over $R_N$ if and only if $\pi_N$ is injective. In the usual surjective comparison, $R_N$-faithfulness is already a ring-equality statement. It cannot be assumed merely because $M_N$ is large over the diamond algebra.

At the base level the same calculation gives

$$
\operatorname{Ann}_{R}(M)=\ker(R\to\mathbb T).
\tag{13.4}
$$

Augmentation control makes (13.2) and (13.4) compatible, but kernels need not commute with quotient unless the exact control diagrams have been verified.

### 13.2 Support and finite Hecke quotients

For a finite $R_N$-module,

$$
\operatorname{Supp}_{R_N}(M_N)
=V(\operatorname{Ann}_{R_N}(M_N)).
\tag{13.5}
$$

Under (13.3), this is the image of

$$
\operatorname{Spec}\mathbb T_N\longrightarrow\operatorname{Spec}R_N.
\tag{13.6}
$$

If $\mathbb T_N$ is finite flat over $\mathcal O$, every irreducible component in its support has a characteristic-zero generic point. If it merely is finite with coefficient torsion, vertical components may occur.

Full support means

$$
\sqrt{\operatorname{Ann}_{R_N}(M_N)}
=\sqrt{0}.
\tag{13.7}
$$

It does not imply faithfulness when $R_N$ is nonreduced: a nilpotent ideal can annihilate $M_N$ without changing the underlying support. The zeroth Fitting ideal has the same topological support, and

$$
\operatorname{Ann}_{R_N}(M_N)^s
\subseteq\operatorname{Fitt}_0^{R_N}(M_N)
\subseteq\operatorname{Ann}_{R_N}(M_N)
\tag{13.8}
$$

when $s$ generators suffice. Vanishing of the Fitting ideal implies faithfulness over a reduced ring, but not over an arbitrary nonreduced ring. A system should therefore record the actual annihilator or a hypothesis strong enough to eliminate its nilpotent part.

### 13.3 Depth over the diamond algebra

The ring $\Lambda_N$ is a one-dimensional complete intersection, finite flat over $\mathcal O$. If $M_N$ is free over $\Lambda_N$, then

$$
\operatorname{depth}_{\Lambda_N}M_N
=\operatorname{depth}\Lambda_N=1.
\tag{13.9}
$$

Viewed as an $S_\infty$-module through $S_\infty\twoheadrightarrow\Lambda_N$, it has a length-$q$ free resolution obtained from the Koszul complex on the regular sequence $\mathfrak c_N$. Thus

$$
\operatorname{pd}_{S_\infty}M_N=q,
\qquad
\operatorname{depth}_{S_\infty}M_N=1.
\tag{13.10}
$$

The second equality also follows from Auslander–Buchsbaum because $S_\infty$ has dimension $q+1$. These finite-level depths are supposed to remain small: the level equations cut out $q$ directions. A later limiting construction removes their finite-order character and changes the relevant depth calculation.

Balancedness alone gives the square presentation (8.10), not (13.9) or (13.10). The first map in that presentation can have large kernel, and the module can contain coefficient torsion. Any depth conclusion in the balanced setting must be proved from the complex or from an additional Cohen–Macaulay hypothesis.

Depth over $R_N$, $\mathbb T_N$, and $\Lambda_N$ are also different assertions. A finite map permits comparison of the depth of the same module only after the relevant maximal ideals have the same radical. It does not identify the depths of the rings themselves.

### 13.4 The hypotheses exported to patching

The finite-level package should export, without proving any infinite-level conclusion, the following support and homological information.

1. **Diamond size.** Either $M_N$ is $\Lambda_N$-free of fixed rank $r$, or it has a balanced square presentation of uniformly bounded size.
2. **Coefficient control.** The modules are $\mathcal O$-torsion-free in the free-module version. In the balanced module version, coefficient torsion is retained rather than silently discarded, and any uniform exponent bound used later is stated separately. A perfect-complex version must record its own amplitude and finite-generation hypotheses.
3. **Factorized action.** The $R_N$-action is the composite through $\mathbb T_N$, and $\mathbb T_N$ acts faithfully.
4. **Annihilator identity.** Equation (13.2) holds; no $R_N$-faithfulness is claimed unless separately proved.
5. **Presentation bound.** The rings are quotients of one $R_\infty$ with uniform generator and relation bounds tied to the numerical defect.
6. **Augmentation control.** The three comparisons in Chapter 6 are recorded as isomorphisms or as surjections with named kernels.
7. **Duality, when included.** Perfect pairings and adjoint involutions are compatible with augmentation and with the pairing-compatible finite-shadow pseudo-transitions of Section 12.4. A balanced module with coefficient torsion cannot carry an ordinary perfect $\mathcal O$-valued pairing; a derived-duality formulation belongs to a separately stated perfect-complex system.
8. **Branch stability.** The old local components and frame counts do not vary with $N$.

These hypotheses are the raw material for later depth, support, and freeness arguments. They do not themselves prove that a limiting module is free over $S_\infty$, faithful over a limiting deformation ring, or that $R$ equals $\mathbb T$.

## 14. Where the module axioms come from

### 14.1 Definite quaternionic modules

For a totally definite quaternion algebra, a fixed-weight automorphic module is built from functions on a finite class set with values in an integral weight lattice. This source explains why the strongest Taylor–Wiles module axioms are plausible.

Adding auxiliary level replaces a point by its possible residue-field level structures. When the relevant stabilizers act freely, these structures form a $\Delta_N$-torsor. Functions on a free finite torsor are copies of the regular representation, so after localization one expects

$$
M_N\simeq\Lambda_N^{\oplus r}.
\tag{14.1}
$$

The proof must check stabilizers, the central quotient, the chosen local eigenspace, and localization. The equality

$$
|X_{Q_N}|=|\Delta_N||X|
$$

does not prove (14.1), as Section 8.2 shows.

The Hecke algebra is naturally defined as the image on the finite module, so faithfulness is automatic at that stage. Away-from-level double cosets commute with diamonds. Local operators at $Q_N$ select the same ordered branch used on the deformation side. A Galois family and local–global compatibility then produce $R_N\twoheadrightarrow\mathbb T_N$.

Finite-sum or mass pairings can yield perfect duality, but denominators from stabilizers must be units or removed by a different integral normalization. Adjointness may send a level operator to its opposite rather than to itself. These facts account for every clause of the duality axiom.

### 14.2 Cohomological modules

For modular or Shimura curves, the natural object is cohomology rather than functions on a finite set. A finite étale diamond cover has a deck action, but cohomology of the cover is not automatically the regular representation tensored with cohomology downstairs. The Cartan–Leray or Hochschild–Serre spectral sequence contains higher group cohomology, and those terms are especially visible when $\ell$ divides $|\Delta_N|$.

Coefficient torsion creates a second difficulty. The localized degree-one group may fail to be $\mathcal O$-free, base change can acquire extra classes, and Poincaré duality may pair a torsion group with an Ext term rather than supply a perfect pairing on one lattice. In a favorable degree range, vanishing of adjacent localized cohomology and torsion-freeness collapse the complex to a free or balanced module. Otherwise the correct finite-level object is a perfect complex with a controlled amplitude.

Hecke correspondences commute with the Galois action and have transposes under Poincaré duality. This gives the adjoint structure. A family representation over the localized Hecke algebra follows from the appropriate irreducibility and local compatibility theorems, not from the mere presence of commuting actions on cohomology.

Augmentation control is likewise geometric. It may follow from a comparison between the auxiliary cover and the base curve, together with a vanishing theorem that turns derived coinvariants into ordinary coinvariants. If higher group homology survives, the correct statement is derived and (6.8) can fail for the middle cohomology module alone.

### 14.3 Why the abstract package is deliberately conditional

The definite and cohomological sources emphasize different strengths.

| Source | Typical strength | Main obstruction |
|---|---|---|
| finite definite module | direct diamond freeness can be visible | stabilizers, central quotients, integral pairing denominators |
| curve cohomology | duality and Galois action are geometric | torsion, adjacent cohomology, derived diamond descent |
| abstract datum | exact covariance and numerical bookkeeping | supplies no geometric theorem by itself |

The abstract axioms are therefore not a disguised proof that every automorphic construction works. Each axiom isolates one theorem an application must supply:

- a torsor or projectivity theorem for diamond freeness;
- a cohomological amplitude theorem for balancedness;
- a level-lowering theorem for coinvariant control;
- saturation for Hecke-algebra control;
- a family representation and local–global theorem for $R_N\to\mathbb T_N$;
- an integral duality theorem for perfect pairings;
- multiplicity and rank calculations for uniformity.

Once supplied, these facts enter the later algebra only through the named rings, modules, maps, ranks, and pairings. The particular modular curve, Shimura curve, or quaternionic class set has then done its job and can recede from the argument.

## 15. Failure modes

### 15.1 Nonfree diamond action

Suppose a finite auxiliary-level module has the expected coefficient rank

$$
\operatorname{rank}_{\mathcal O}M_N
=r|\Delta_N|.
\tag{15.1}
$$

This equation is necessary for $\Lambda_N$-freeness of rank $r$, but Section 8.2 proves that it is not sufficient. A geometric version of the same failure occurs when a group of deck transformations has fixed points. The total number of points can accidentally equal the number in a free union of orbits, while some orbits are shorter and others occur with extra multiplicity. The permutation module then has the right rank and the wrong stabilizers.

Three tests detect the problem.

First, coinvariants of a rank-$r$ free module have $\mathcal O$-rank $r$. A larger coinvariant module rules out freeness immediately. Second, a free module has vanishing higher Tor:

$$
\operatorname{Tor}_1^{\Lambda_N}(M_N,k)=0.
\tag{15.2}
$$

Third, every nonzero free module is faithful over $\Lambda_N$. If a nontrivial diamond element acts as the identity on all of $M_N$, freeness is impossible.

Even these tests have different strengths. Correct coinvariant rank and faithfulness do not in general prove projectivity. Vanishing of $\operatorname{Tor}_1$ for a finite module over a local ring does prove flatness, and finite flatness then gives freeness, but the vanishing must be established over the full group ring rather than over $\mathcal O$.

If diamond freeness fails but the module is balanced, a square presentation may still be usable. If the balance defect is negative, the module alone has too many first syzygies; one must enlarge the cohomological object to the complex from which it came or strengthen the geometric hypotheses.

### 15.2 Coefficient torsion and bad reduction

Suppose $0\ne x\in M_N$ satisfies $\varpi x=0$. Several standard implications fail at once.

The module is not $\Lambda_N$-free because $\Lambda_N$ is $\mathcal O$-flat. The image algebra $\mathbb T_N$ is finite, but its embedding in $\operatorname{End}_{\mathcal O}(M_N)$ no longer places it inside the endomorphisms of an $\mathcal O$-lattice. It can have coefficient torsion, so it need not be finite flat over $\mathcal O$. Reduction modulo $\varpi$ is no longer the special fiber of a torsion-free family; it can mix pre-existing torsion with genuine reduction of characteristic-zero classes.

Perfect $\mathcal O$-valued duality on $M_N$ also fails because a finite module with torsion cannot be isomorphic to its $\mathcal O$-dual into the torsion-free ring $\mathcal O$. The correct duality can involve

$$
\operatorname{Hom}_{\mathcal O}(M_N, E/\mathcal O)
$$

or a derived dual with Ext terms. Replacing that structure by an ordinary perfect pairing discards the torsion rather than controlling it.

There are two honest remedies. One can prove torsion vanishing after localization and return to the module version, or retain a bounded complex of finite free modules whose cohomology contains the torsion. A uniform exponent bound on torsion is useful but does not turn the cohomology module into a free diamond module.

### 15.3 Varying ranks and unbounded presentations

The coefficient rank of a free diamond module grows as $\ell^{Nq}$, but its normalized rank is fixed. A failure of uniformity means that

$$
r_N
=\frac{\operatorname{rank}_{\mathcal O}M_N}{|\Delta_N|}
\tag{15.3}
$$

varies without control, or that the minimal square-presentation size in the balanced setting is unbounded.

This prevents finite-shadow stabilization. At a fixed precision $d$, modules requiring arbitrarily many generators are not quotients of one finite module $C_d^{d_0}$. The finiteness argument underlying (10.10) disappears, so there is no diagonal subsequence theorem of the stated form.

Varying rank can have genuine arithmetic causes: old multiplicities introduced by auxiliary level, several local types surviving localization, boundary classes, or a failure of multiplicity one. It should not be hidden by adding arbitrary free summands, because doing so changes the Hecke action, pairings, and augmentation quotient. The correct response is to isolate a stable local type, redefine the module as a complex with stable Euler characteristic, or acknowledge that the collection is not a Taylor–Wiles system of the chosen rank.

Unbounded deformation presentations cause the analogous ring-side failure. If the number of global variables or relations grows with $N$ after the $q$ diamond directions have been removed, no fixed $R_\infty$ controls the levels. The dual Selmer killing theorem is designed precisely to prevent this growth on the deformation side.

### 15.4 Missing augmentation control

There are three independent ways augmentation can fail.

On deformation rings, the quotient may remember an enhanced eigenline. Then $R_N/\mathfrak a_NR_N$ represents a cover of the original deformation problem rather than the problem itself. This occurs at scalar residual Frobenius or when the local branch has not been chosen compatibly.

On modules, there may be a surjection

$$
M_N/\mathfrak a_NM_N\twoheadrightarrow M
$$

with nonzero kernel. Extra old classes or boundary classes can survive after every diamond is set to one. Equal ranks rule out this kernel only when both source and target are known torsion-free and the map is already known to be surjective.

On Hecke algebras, a further saturation failure can remain even when module control holds. Here is a concrete model. Let

$$
A=\mathcal O[C_\ell],
\qquad
s=[g]-1,
\qquad
X=A^2.
$$

Inside $\operatorname{End}_A(X)$ let

$$
u=sE_{12}
$$

and let

$$
B=A[u]
$$

be the acting image algebra. It acts faithfully on $X$ by definition. Modulo the augmentation ideal, $s$ acts as zero, so $u$ acts as zero on

$$
X/sX\simeq\mathcal O^2.
$$

Nevertheless $u$ need not lie in $sB$: writing

$$
B=A\oplus Au,
\qquad u^2=0,
$$

the class of $u$ cannot be expressed as $s$ times an element of the second summand because that would require $1$ to lie in the image of $s$ modulo the annihilator of $s$. Hence $B/sB$ contains a nonzero nilpotent class acting trivially on the coinvariants. Its acting image is only $\mathcal O$. This is exactly the kernel measured in (6.11).

Thus one must state separately whether each augmentation comparison is a surjection or an isomorphism. Writing all three with the same equality sign conceals different theorems.

### 15.5 Incompatible local branches

Suppose a local deformation ring at an old ramified place has two components $C_1$ and $C_2$, and the finite-level global problems alternate between them. Even if their tangent dimensions agree, the common local base changes with $N$. A power-series source built over $C_1$ cannot present a ring whose universal local representation lies only on $C_2$ unless there is a specified comparison between the components.

The same danger occurs at auxiliary primes when ordered eigenlines are changed without applying inversion to diamonds. If one level sends $[\delta]$ to the tame character on the first line and another sends it to the character on the second line, the two conventions differ by

$$
[\delta]\longmapsto[\delta]^{-1}.
$$

Failing to record this change makes the diamond square (5.10) fail to commute at one level.

Determinant conventions can create a subtler branch mismatch. With fixed unramified determinant, the second tame character must be the inverse of the first. Permitting the same character on both lines defines a different determinant problem. No common presentation choice repairs a change in the represented functor.

The audit is therefore local before it is global: fix each old component, each determinant, each reciprocity normalization, and each ordered auxiliary eigenline; then choose common coordinates.

### 15.6 False transitions between unrelated levels

The final failure is categorical rather than numerical. From

$$
\Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q
$$

and

$$
\Delta_{N+1}\simeq(\mathbf Z/\ell^{N+1}\mathbf Z)^q
$$

one can choose a group quotient $\Delta_{N+1}\twoheadrightarrow\Delta_N$. It does not follow that auxiliary representations, Hecke modules, or geometric spaces descend along it. The quotient remembers only the abstract cyclic coordinates, not the primes at which the characters live.

Using such a chosen group quotient as if it were arithmetic can lead to false claims that ramification disappears, Hecke operators at different primes agree, or pairings restrict. The correct statements are:

- the standard diamond presentation rings form a genuine inverse system;
- the finite shadows chosen in Section 10.4 form a genuine inverse system;
- the original arithmetic levels form only a family under common sources, unless additional transition data have been proved.

This distinction is not an inconvenience to be suppressed. It is the mechanism that lets a Taylor–Wiles system remain both comparable and honest.

## 16. Taylor–Wiles data and Taylor–Wiles systems

### 16.1 A Taylor–Wiles datum at one level

We now collect the preceding structures into one definition. Fix a base package

$$
\mathscr B=(\mathcal O,k,R_{\mathrm{loc}},R,\mathbb T,M)
\tag{16.1}
$$

with maps

$$
R_{\mathrm{loc}}\longrightarrow R
\xrightarrow{\pi}\mathbb T
\xrightarrow{h}\operatorname{End}_{\mathcal O}(M),
\tag{16.2}
$$

where $h$ is injective and $\pi$ is surjective when the selected Hecke generators are known to lie in its image.

Here $R$ denotes the framed, partially framed, or unframed version fixed for the entire package. If no structural map from a framed local tensor product to the unframed ring has been constructed, one either works with the corresponding partially framed $R$ or takes the displayed fixed base to be $\mathcal O$. The notation in (16.2) never asserts a local-base map that the selected deformation functor does not possess.

**Definition 16.1 (Taylor–Wiles datum at level $N$).** A controlled Taylor–Wiles datum of cardinality $q$ and level $N$ over $\mathscr B$ consists of the following objects and properties.

**(TW1) Auxiliary arithmetic.** There is an ordered set

$$
Q_N=\{v_{N,1},\ldots,v_{N,q}\}
$$

of places, disjoint from the original ramification set, with

$$
q_v\equiv1\pmod{\ell^N}
$$

and a selected regular residual Frobenius eigenline at every $v$. There are exact-level cyclic groups $\Delta_v(N)$ and

$$
\Delta_N=\prod_{v\in Q_N}\Delta_v(N),
\qquad
\Lambda_N=\mathcal O[\Delta_N].
\tag{16.3}
$$

Generators $\delta_{N,i}$ and a reciprocity normalization are part of the datum.

**(TW2) Rings and covariance.** There are complete Noetherian local $\mathcal O$-algebras $R_N$ and $\mathbb T_N$ and homomorphisms

$$
\begin{array}{ccccc}
R_{\mathrm{loc}}&\longrightarrow&R_N&\xrightarrow{\pi_N}&\mathbb T_N,\\
&&\mathord\uparrow\lambda_N&&\mathord\uparrow j_N\\
&&\Lambda_N&=&\Lambda_N,
\end{array}
\tag{16.4}
$$

with

$$
\pi_N\circ\lambda_N=j_N.
\tag{16.5}
$$

The map $\pi_N$ is surjective in a full datum. If it is only a named comparison map, the datum is called **preliminary** and the missing surjectivity is recorded.

**(TW3) Module and factorized actions.** There is a finite $\mathcal O$-module $M_N$ and an injective action map

$$
h_N:\mathbb T_N\hookrightarrow
\operatorname{End}_{\mathcal O}(M_N).
\tag{16.6}
$$

The deformation and diamond actions are exactly

$$
h_N\circ\pi_N
\quad\text{and}\quad
h_N\circ j_N,
\tag{16.7}
$$

respectively. Thus no second, unverified $R_N$-action or diamond action is being conflated with the displayed ones.

**(TW4) Augmentation control.** With $\mathfrak a_N=\ker(\Lambda_N\to\mathcal O)$, there are compatible isomorphisms

$$
R_N/\mathfrak a_NR_N\xrightarrow{\sim}R,
\tag{16.8}
$$

$$
\mathbb T_N/\mathfrak a_N\mathbb T_N
\xrightarrow{\sim}\mathbb T,
\tag{16.9}
$$

and

$$
M_N/\mathfrak a_NM_N\xrightarrow{\sim}M.
\tag{16.10}
$$

They make (6.14) commute and intertwine the actions. A **weakly controlled datum** permits one or more of (16.8)–(16.10) to be only a surjection, but it must name the kernel and state which criterion of Theorem 6.1 remains to be proved. In the deformation-ring case, a downward surjection includes the functorial enhancement that produces (6.3); the forgetful transformation alone produces the reverse map (6.2).

**(TW5) Diamond size.** Either

$$
M_N\text{ is finite free of a fixed rank }r\geq1\text{ over }\Lambda_N,
\tag{16.11}
$$

or $M_N$ is balanced over $\Lambda_N$ with a square presentation of a specified size at most $d$. The two versions are not interchangeable.

**(TW6) Deformation-theoretic control.** The enlarged dual Selmer group vanishes, the defect is

$$
\Delta(\mathcal D_{Q_N})=\Delta(\mathcal D)+q,
\tag{16.12}
$$

and $R_N$ has the prescribed generator and relation bounds over the selected finite-level local base. If this cohomological structure is not part of the abstract application, the same numerical bounds may be listed directly together with their source.

**(TW7) Presentation coordinates.** There are chosen quotient maps

$$
S_\infty\twoheadrightarrow\Lambda_N,
\qquad
R_\infty\twoheadrightarrow R_N
\tag{16.13}
$$

compatible with diamonds and the local base, with $\mathfrak c_N=\ker(S_\infty\to\Lambda_N)$ and $\mathfrak c_NR_\infty\subseteq\ker(R_\infty\to R_N)$.

**(TW8) Duality data.** When duality is required, there is either a perfect self-pairing of one of the two types in Chapter 12 or a companion module $M_N'$ with its own acting Hecke algebra $\mathbb T_N'$, faithful action, diamond structure, size condition, and augmentation control. In the paired case the adjoint is an isomorphism $\mathbb T_N\xrightarrow{\sim}\mathbb T_N'$; it is not merely a formal symbol attached to $M_N'$. The diamond involution, augmentation pairing, frame normalization, and pairing-compatible finite shadows required by Section 12.4 are all specified.

The word “controlled” in Definition 16.1 refers to the exact augmentation identities. It does not assert $R_N\simeq\mathbb T_N$. Indeed,

$$
\operatorname{Ann}_{R_N}(M_N)=\ker\pi_N
$$

is allowed to be nonzero.

### 16.2 A presentation-compatible Taylor–Wiles system

A single datum contains no information about dependence on $N$. The following definition supplies precisely the common structure needed to compare infinitely many independent auxiliary levels.

**Definition 16.2 (presentation-compatible Taylor–Wiles system).** A Taylor–Wiles system over $\mathscr B$ consists of controlled data $\mathscr X_N$ for all $N\geq1$, together with the following uniform and comparison data.

1. **Fixed arithmetic size.** The number $q=|Q_N|$ is independent of $N$, and

   $$
   \Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q
   $$

   through the named orderings and generators.

2. **Fixed diamond source.** One ring

   $$
   S_\infty=\mathcal O[[z_1,\ldots,z_q]]
   $$

   maps to every $\Lambda_N$ with kernel $\mathfrak c_N$.

3. **Fixed deformation source.** One local power-series ring

   $$
   R_\infty
   =R_{\mathrm{loc}}[[z_1,\ldots,z_q,x_1,\ldots,x_G]]
   $$

   maps surjectively to every $R_N$, compatibly with $S_\infty$ and $R_{\mathrm{loc}}$. Here $s_{\mathrm{aux}}=q$ for unframed auxiliary local factors and $s_{\mathrm{aux}}=3q$ for framed ones, and $G=s_{\mathrm{aux}}+g$ or is a larger declared padding bound. The kernels have the form (9.11): besides the $q$ level equations in $\mathfrak c_N$, the relative relation count is uniformly bounded by a fixed $b$.

4. **Uniform module size.** In the free version, all $M_N$ have the same $\Lambda_N$-rank $r$. In the balanced module version, their square presentations have size at most one fixed $d$. A perfect-complex version requires a separate amplitude axiom and is not obtained merely by calling one cohomology module balanced.

5. **Uniform Hecke specification.** The away-from-$S$ generators have common labels whenever the corresponding place is not auxiliary, the auxiliary generators occupy $q$ ordered slots, and the maps $R_N\to\mathbb T_N$ and adjoint operations use those labels compatibly. Every fixed place is absent from $Q_N$ for all sufficiently large $N$, so each common label is eventually defined. An infinite labeled family is retained by the countable diagonal procedure of Section 10.4, or is replaced by a proved uniformly finite generating family. This is compatibility of presentations and polynomials, not equality of operators at different auxiliary primes.

6. **Fixed frames and branches.** The old local base, old local components, determinant, and old framing set are independent of $N$. At the varying auxiliary places, the same framed or unframed convention is used in all $q$ ordered slots, so the number of auxiliary smooth framing variables is independent of $N$ even though the places themselves are not. Every change of auxiliary generator or eigenline is recorded by a coordinate automorphism.

7. **Coherent finite shadows.** There is a cofinal sequence

   $$
   N_1<N_2<\cdots
   $$

   and, for every precision $d$, a finite diagram $\mathscr D_d$ of the form (10.10), with surjective reduction maps

   $$
   \mathscr D_{d+1}\twoheadrightarrow\mathscr D_d.
   \tag{16.14}
   $$

   For every $j\geq d$, the precision-$d$ shadow of $\mathscr X_{N_j}$ is equipped with an isomorphism to $\mathscr D_d$. These isomorphisms commute with reduction in $d$, preserve the first $d$ entries of every enumerated Hecke family and the truncated augmentation maps, and preserve pairings only through the pairing-compatible shadows specified in Section 12.4.

Item 7 can be replaced by the uniform finiteness hypotheses of Section 10.4 together with the declaration that a diagonal subsequence will be chosen before taking limits. Including the coherent shadows in the definition makes the system immediately ready for that operation and removes any ambiguity about what “compatible across levels” means.

No maps $R_{N_{j+1}}\to R_{N_j}$ or $M_{N_{j+1}}\to M_{N_j}$ occur in Definition 16.2. The maps (16.14) belong to the chosen finite models $\mathscr D_d$.

### 16.3 A stronger transitioned system

When arithmetic or geometry genuinely supplies maps among levels, one may add them.

**Definition 16.3 (transitioned Taylor–Wiles system).** A transitioned system is a presentation-compatible system equipped with homomorphisms and semilinear module maps

$$
\tau^R_{m,n}:R_m\longrightarrow R_n,
\qquad
\tau^{\mathbb T}_{m,n}:\mathbb T_m\longrightarrow\mathbb T_n,
\qquad
\tau^M_{m,n}:M_m\longrightarrow M_n
\tag{16.15}
$$

for $m\geq n$, together with specified group-algebra maps $\Lambda_m\to\Lambda_n$, such that:

$$
\tau_{n,n}=\operatorname{id},
\qquad
\tau_{m,n}\circ\tau_{l,m}=\tau_{l,n}
\quad(l\geq m\geq n),
\tag{16.16}
$$

all squares involving $R_{\mathrm{loc}}$, diamonds, $R\to\mathbb T$, and augmentation commute, and

$$
\tau^M_{m,n}(t x)
=\tau^{\mathbb T}_{m,n}(t)\tau^M_{m,n}(x).
\tag{16.17}
$$

Pairings must satisfy their displayed pullback or trace formula, including any degree factor. These conditions define an actual inverse or direct system according to the stated map directions.

Definition 16.3 is stronger, not more correct. It should be used only when the maps in (16.15) have been constructed. Independent Taylor–Wiles prime sets naturally satisfy Definition 16.2 instead.

### 16.4 The axiom ledger

The origin of every axiom can now be displayed in one ledger.

| Axiom | Content | Deformation-side input | Module-side input |
|---|---|---|---|
| TW1 | $Q_N$, regular eigenlines, $\Delta_N$ | prime selection and local calculation | none |
| TW2 | $\Lambda_N\to R_N\to\mathbb T_N$ | $\Lambda_N\to R_N$ | family representation, Hecke generators |
| TW3 | factorized action on $M_N$ | names the desired universal action | commuting diamonds and Hecke action |
| TW4a | $R_N/\mathfrak a_NR_N\simeq R$ | uniqueness of the augmented local branch | none |
| TW4b | $M_N/\mathfrak a_NM_N\simeq M$ | none | level-lowering control |
| TW4c | $\mathbb T_N/\mathfrak a_N\mathbb T_N\simeq\mathbb T$ | none | compatible generators and saturation |
| TW5 | free or balanced diamond module | none | torsor, projectivity, or cohomological amplitude theorem |
| TW6 | defect and ring presentation bounds | Poitou–Tate and obstruction theory | none |
| TW7 | common $S_\infty$ and $R_\infty$ | generator choices and uniform bounds | compatible action on finite shadows |
| TW8 | conditional perfect pairing and adjoints | none | integral duality and correspondence reversal |
| SYS1 | ranks and cardinalities uniform in $N$ | fixed $q$ | multiplicity and rank theorem |
| SYS2 | pseudo-transitions among finite shadows | finite presentation bounds | finite generation and compatible named data |

This table is also a diagnostic. If an application cites only the auxiliary-prime theorem, it has established TW1, TW4a, the deformation part of TW6, and the ring portion of TW7. It has not established the module rows.

## 17. The arithmetic existence theorem

### 17.1 The deformation-side theorem

We finish by stating exactly what the arithmetic construction supplies and exactly what remains conditional.

Let $K$ be a number field, let $\ell$ be odd, let $k$ be a finite field of characteristic $\ell$, and let $\mathcal O$ be a complete discrete valuation ring of mixed characteristic with residue field $k$. Let

$$
\bar\rho:G_{K,S}\longrightarrow\operatorname{GL}_2(k)
$$

be absolutely irreducible, fix a determinant lift, and put

$$
W=\operatorname{ad}^0\bar\rho,
\qquad
W'=W^*(1).
$$

Assume:

1. the original global deformation problem $\mathcal D$ and all chosen local conditions are representable;
2. their tangent conditions have the exact Tate orthogonals used in the global duality formula;
3. the split Taylor–Wiles image conditions hold, including the no-$\ell$-quotient, $H^1$-vanishing, no-trivial-quotient, and split regular detection clauses;
4. the selected local eigenvalues lie in $k$;
5. the old local components and framing convention are fixed;
6. for every auxiliary problem used below, the local and global obstruction theories are complete, effective, and cohomologically controlled relative to the chosen finite-level local base whenever relation bounds are claimed.

Put

$$
q=q(\mathcal D)
=\dim_kH^1_{\mathcal L^\perp}(K,W').
\tag{17.1}
$$

**Theorem 17.1 (deformation-side Taylor–Wiles system).** Under these hypotheses, for every $N\geq1$ there is an auxiliary set $Q_N$ and an auxiliary deformation ring $R_N$ with the following properties.

1. The set has cardinality $q$, every $v\in Q_N$ satisfies $q_v\equiv1\pmod{\ell^N}$, and residual Frobenius is split regular with a chosen eigenline.
2. With exact-level quotients,

   $$
   \Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q,
   \qquad
   |\Delta_N|=\ell^{Nq}.
   $$

3. There are structural maps

   $$
   \Lambda_N\longrightarrow R_N,
   \qquad
   R_{\mathrm{loc}}\longrightarrow R_N.
   $$

4. Augmentation gives a canonical isomorphism

   $$
   R_N/\mathfrak a_NR_N\xrightarrow{\sim}R.
   $$

5. The enlarged dual Selmer group vanishes, and

   $$
   \Delta(\mathcal D_{Q_N})
   =\Delta(\mathcal D)+q.
   $$

   Its unframed Selmer tangent has dimension $\Delta(\mathcal D)+q$; for an unpadded killing set this equals the original unframed Selmer tangent dimension. A framed ring has the additional, separately recorded gauge correction of Chapter 11.
6. The rings have uniform padded generator and relation bounds over their full finite-level local bases; the exact relative counts in that convention are allowed to vary with $N$. After choosing orderings, cyclic generators, and cotangent lifts, there are compatible surjections from fixed rings

   $$
   S_\infty=\mathcal O[[z_1,\ldots,z_q]],
   $$

   and

   $$
   R_\infty
   =R_{\mathrm{loc}}[[z_1,\ldots,z_q,x_1,\ldots,x_G]],
   $$

   where $s_{\mathrm{aux}}=q$ in the unframed auxiliary convention and $s_{\mathrm{aux}}=3q$ in the framed convention, and where $G=s_{\mathrm{aux}}+g$ with any additional padding recorded explicitly.

   For these chosen presentations, the kernel has the form (9.11): the $q$ equations in $\mathfrak c_N$ impose finite diamond level and at most $b$ further equations give the padded relative presentation.

7. The sets $Q_N$ may be chosen pairwise disjoint. No transition maps between the resulting $R_N$ are asserted. Their presentation shadows admit coherent pseudo-transitions after a diagonal subsequence.

Thus the objects supplied by arithmetic satisfy all deformation-side entries of the axiom ledger. They form the deformation skeleton of a presentation-compatible Taylor–Wiles system.

### 17.2 Proof of the theorem

**Proof.** If $q=0$, take $Q_N=\varnothing$ for every $N$; the dual Selmer group already vanishes, all auxiliary assertions are empty, and the fixed presentations are the original ones with no diamond variables. Assume henceforth that $q>0$. Choose a nonzero class in the original dual Selmer group. The split image hypotheses ensure that its restriction cuts out a nontrivial elementary abelian extension over the residual and cyclotomic fixed field. The no-trivial-quotient clause separates that extension from the higher cyclotomic layer. A split regular element detects a nonzero diagonal projection of the class, and the fiber-product compatibility criterion combines this detector with trivial action on $\ell^N$th roots of unity. Chebotarev then supplies a place $v$ whose residue cardinality is $1$ modulo $\ell^N$, whose residual Frobenius has the selected regular form, and whose localization detects the chosen class.

At such a place the quotient between the new and old primal tangent conditions is one-dimensional, and the new dual condition is strict. The localization map on the current dual Selmer space is nonzero with one-dimensional target, hence surjective. Its kernel has dimension one less. Repeat the construction inside that kernel, adding all previously chosen places to the avoidance set. After exactly $q$ steps the dual Selmer group is zero. This proves item 1 and the vanishing in item 5. Adding all places used at earlier values of $N$ to the next avoidance set makes the $Q_N$ pairwise disjoint.

For each selected place, the exact quotient of the residue-field units is cyclic of order $\ell^N$. Their product proves item 2. The chosen eigenline and reciprocity convention give the local ring (4.3), or (4.4) in the framed convention. Completed products give the structural diamond map, and restriction of the universal global representation gives the local-base map in item 3.

Augmentation makes every tame character trivial. Distinct residual eigenvalues make the ordered lifted eigenspace unique for every unramified lift. Proposition 4.1 therefore identifies the augmented auxiliary functor with the original functor, proving item 4.

Each auxiliary place changes the local contribution to the global numerical formula by one. Since there are $q$ places and the new dual group vanishes, equations (4.16)–(4.18) prove the rest of item 5.

Complete effective obstruction theory bounds relations by $q_{\mathrm{rel},N}=q_{U_N}(\mathcal D_{Q_N})$, while the tangent calculation gives $g_{\mathrm{rel},N}$. Absolute dual Selmer vanishing injects the relative group into the uniformly bounded sum of local quotients displayed after (4.23), so the $q_{\mathrm{rel},N}$ are uniformly bounded. Formula (4.23) then bounds the $g_{\mathrm{rel},N}$, and the simultaneous variable-and-relation padding of Section 4.5 supplies fixed bounds $g$ and $b$. Choose an ordering and generator for each cyclic local group. This produces $S_\infty\twoheadrightarrow\Lambda_N$. Choose lifts of the padded cotangent spanning sets to obtain $R_\infty\twoheadrightarrow R_N$. These choices prove item 6; they do not create maps between different $R_N$.

Finally, nonnestedness follows from the finite value of $v_\ell(q_v-1)$ at a fixed place. The finite-shadow argument of Section 10.4 applies to the fixed presentations and gives item 7. $\square$

### 17.3 The automorphic hypotheses still to be supplied

Theorem 17.1 does not produce $\mathbb T_N$ or $M_N$. To extend its deformation skeleton to a controlled Taylor–Wiles system, an application must supply the following assertions for every $N$.

**(A1) Integral modules.** A localized module $M_N$ is finite over $\mathcal O$. Coefficient torsion is excluded in the free version and retained explicitly in the balanced module version. If the available theorem controls only a perfect complex, the application must either prove that the selected cohomology module is balanced or invoke a separately formulated complex-valued system.

**(A2) Diamond structure.** The exact group $\Delta_N$ acts with the same reciprocity normalization as the tame character in $R_N$. The module is free of a fixed $\Lambda_N$-rank $r$, or balanced with a uniform square-presentation bound. This must be proved by a torsor, projectivity, or cohomological-amplitude argument.

**(A3) Hecke structure.** A specified commutative Hecke family, including diamonds and the operators selecting the auxiliary local branches, has acting image $\mathbb T_N$. Away-from-$S$ operators carry common labels whenever their places are not auxiliary, and the auxiliary operators occupy the $q$ ordered slots of $Q_N$. Defining the image makes its action faithful; it does not make $M_N$ free over $\mathbb T_N$.

**(A4) Family representation.** A representation over $\mathbb T_N$ satisfies every old and auxiliary local condition. It may be obtained from a determinant or Cayley–Hamilton family only after the residually absolutely irreducible upgrade to a genuine matrix representation has been proved. Its tame characters equal the diamond operators, and its good-prime polynomials equal the chosen Hecke polynomials. Universality gives $R_N\to\mathbb T_N$; the named Hecke generators must then prove surjectivity.

**(A5) Control.** Level lowering proves

$$
M_N/\mathfrak a_NM_N\xrightarrow{\sim}M.
$$

Compatible generators give a surjection on Hecke algebras, and a saturation or faithful-reduction theorem proves

$$
\mathbb T_N/\mathfrak a_N\mathbb T_N
\xrightarrow{\sim}\mathbb T.
$$

The second isomorphism cannot be inferred solely from the first.

**(A6) Uniform multiplicity.** The rank $r$, or the balanced presentation bound, is independent of $N$. Old multiplicities, central-character components, and boundary contributions have been removed or shown to be constant.

**(A7) Duality, when invoked.** If the selected system includes TW8, the modules carry perfect pairings with diamond inversion and the exact Hecke adjoint normalization. A paired module has the full companion data required by TW8. The pairings descend to the fixed base pairing and remain compatible in the pairing shadows of Section 12.4; this compatibility is an input, not a consequence of finite cardinality. If coefficient torsion is retained and only derived duality is available, the application must use a separately formulated perfect-complex system rather than assert an ordinary perfect $\mathcal O$-valued pairing on $M_N$.

**(A8) Fixed local choices.** The same old local branches, determinant, framing convention, and Hecke normalization occur at every level. Auxiliary eigenline swaps are accompanied by the required inversion coordinate change.

**Theorem 17.2 (assembly criterion).** Under the hypotheses of Theorem 17.1, suppose (A1)–(A8) hold. Then the tuples

$$
(Q_N,\Delta_N,\Lambda_N,R_N,\mathbb T_N,M_N)
$$

form controlled Taylor–Wiles data. After choosing the common presentations and passing to the diagonal subsequence of Section 10.4, they form a presentation-compatible Taylor–Wiles system in the sense of Definition 16.2.

**Proof.** Theorem 17.1 supplies TW1, the deformation half of TW2, TW4a, TW6, and the ring half of TW7. Assertions (A1)–(A4) supply TW3 and complete the commuting triangle TW2; the generating clause in (A4) gives the required surjection $R_N\twoheadrightarrow\mathbb T_N$. Assertion (A5) supplies TW4b and TW4c with the exact isomorphism criteria of Theorem 6.1. Assertions (A2) and (A6) give TW5 and uniform module size. Assertion (A7) gives TW8 whenever duality is included in the selected package. Assertion (A8) makes the common local base and frame count legitimate.

At every fixed precision, the rings and modules now range over finitely many diagrams because the sources and generator bounds are fixed. Truncate the augmentation targets, include only the finite initial segment of an enumerated Hecke family, and, when TW8 is present, use the pairing-compatible quotients supplied by (A7). The diagonal stabilization argument then produces the coherent shadows required by Definition 16.2, without producing or asserting maps among the original arithmetic levels. $\square$

### 17.4 Final synthesis

A Taylor–Wiles system is a disciplined record of an exchange. Global dual Selmer classes are removed one at a time by local tame directions. Those directions are stored in finite diamond groups whose group algebras are standard quotients of one completed power-series ring. Augmentation reverses the exchange: the tame characters become trivial, the auxiliary deformation problem becomes the original one, and—when geometry supplies exact control—the auxiliary module and its Hecke algebra descend to their base-level counterparts.

The heart of the definition is covariance. The diamond algebra maps into the deformation ring and the Hecke algebra; the deformation ring maps to the Hecke algebra; the Hecke algebra maps faithfully into module endomorphisms. The $R_N$-action is the composite through $\mathbb T_N$, while the geometric and deformation-theoretic diamond actions are required to coincide. Annihilators, support, and faithfulness can then be read directly from the kernels of these named maps.

The second essential feature is honest comparison across $N$. The auxiliary sets are normally nonnested and may be pairwise disjoint. Their rings and modules do not form an arithmetic tower. Chosen generators place the diamond algebras under $S_\infty$, cotangent lifts place the deformation rings under $R_\infty$, and finite-shadow stabilization creates pseudo-transitions among common presentation models. These choices provide coherence without pretending that unrelated primes are functorially connected.

The final feature is the separation of theorem from axiom. Prime selection, local deformation theory, global duality, and obstruction bounds construct the deformation skeleton and prove its augmentation identity. A particular automorphic realization must still prove diamond freeness or balancedness, uniform multiplicity, Hecke and Galois compatibility, exact module and algebra control, and, when TW8 is invoked, integral duality. Once those results have been supplied, every geometric detail is compressed into a finite set of rings, modules, maps, ranks, presentations, and pairings.

That compressed package is the endpoint: finite at every level, uniform in all numerical directions, explicit about every choice, and coherent without false transitions. It contains exactly the data from which the later limiting construction can begin.
