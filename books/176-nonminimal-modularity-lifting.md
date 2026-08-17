# Finite-Set Ihara Avoidance and Nonminimal Modularity Lifting

This volume is the modularity-lifting application of the one-prime comparison developed in
the preceding books. Its first output is a pointwise theorem: once an actual one-prime
automorphic carrier has the represented local condition, support, and reciprocity required
below, every characteristic-zero point satisfying the asserted open branch conditions is
automorphic; in particular, a special-conductor conclusion retains nonzero monodromy. Its
second output is the exact several-place hypothesis package for a proof by geometric level change when
one place splits into many: either one verifies an ordered chain of one-prime applications, or
one supplies a genuinely joint cube. For the joint route, mixed exactness, product residue
through the integral iterated-switch
Beck--Chevalley datum, joint support, augmentation, and reciprocity remain distinct
hypotheses. For one named point, the torsion-free top of the actual final cube gives a smaller
carrier, but occurrence of the global component through that point is still required.

Neither theorem is logically forced by the statement in the FLT blueprint. The standard
Taylor--Wiles--Kisin proof has a third finite-set route: after solvable base change it patches
the desired local problem and an Ihara-avoidance problem simultaneously, then transfers full
support from the irreducible avoidance ring through their common special fiber. That route
does not form the several-place old--new cube. Section 1.5 records its exact input.
Section 1.5A proves its whole-ring finite-recovery consequence and applies it to a broad
target-unipotent ring surjecting onto the minimal ring. One target instance then supplies
both the finite special fibre needed to construct the lift and automorphy of the resulting
point. Section 1.5B proves the scalar paired local-ring calculation and the common residual
automorphic shadows. Section 1.5C explains why patching first to an arbitrary global
quotient cannot prove component specialization or avoidance support. Section 1.5D gives the
correct source-patching argument: patch over the Cohen--Macaulay local presentation source,
prove the avoidance action faithful there, transfer support across the common special fiber,
and then recover the finite-level action with nilpotent kernel from module coinvariants. This
proves the single reusable componentwise Ihara-avoidance theorem $({\rm CIAV}_P)$. The same
section formulates two prepared applications. They begin with an actual automorphic packet,
not with a placeholder for a future finite-set argument, and they distinguish the module-level
conclusion needed for automorphy from the stronger optional equality of augmented acting
images.

There is also a smaller definite-side fact relevant to the optional exact-minimal argument.
For scalar parallel weight two, the two-map Ihara lemma on a totally definite quaternionic
class set follows directly from strong approximation away from the changed finite place.
Section 1.6 proves that result and its integral saturation consequence. It then isolates why
this does not by itself lower an upper eigensystem to minimal level: injectivity controls the
old source once that source exists, whereas the application first needs to prove that the
minimal source is nonzero. Section 1.7 checks the actual Frey target-extra places against
Mazur principle and full outside-$\ell$ level optimization. It proves the finite-set induction
from the exact one-place theorem, and identifies the additional arithmetic-model theorem
required by that optional route.

The discussion of incidence complexes below serves these application theorems. It never
forms a tensor product of full global one-prime cohomology complexes: the common global
multiplicity carrier is inserted once, and only genuinely local or relative factors may be
multiplied.

## Contents

- [1. The modularity-lifting application](#1-the-modularity-lifting-application)
  - [1.1 Minimal and nonminimal deformation spaces](#11-minimal-and-nonminimal-deformation-spaces)
  - [1.2 What one changed place must provide](#12-what-one-changed-place-must-provide)
  - [1.3 The finite-set demand from the FLT argument](#13-the-finite-set-demand-from-the-flt-argument)
  - [1.4 The application routes and their boundary](#14-the-application-routes-and-their-boundary)
  - [1.5 The direct finite-set Ihara-avoidance route](#15-the-direct-finite-set-ihara-avoidance-route)
  - [1.5A The finite-fibre consequence and the target-minimal quotient](#15a-the-finite-fibre-consequence-and-the-target-minimal-quotient)
  - [1.5B The scalar paired rings and the exact patched boundary](#15b-the-scalar-paired-rings-and-the-exact-patched-boundary)
  - [1.5C Balanced patching, vertical cross-cotangents, and avoidance support](#15c-balanced-patching-vertical-cross-cotangents-and-avoidance-support)
  - [1.5D The source-patching CIAV theorem and prepared applications](#15d-the-source-patching-ciav-theorem-and-prepared-applications)
  - [1.6 Definite Ihara and the minimal-support boundary](#16-definite-ihara-and-the-minimal-support-boundary)
  - [1.7 Outside-ell level optimization and the actual Frey set](#17-outside-ell-level-optimization-and-the-actual-frey-set)
- [2. Local conventions and the three congruence regimes](#2-local-conventions-and-the-three-congruence-regimes)
  - [2.1 Frobenius, Hecke operators, and monodromy](#21-frobenius-hecke-operators-and-monodromy)
  - [2.2 Special representations and conductor](#22-special-representations-and-conductor)
  - [2.3 Scalar tame variation forces q congruent to one](#23-scalar-tame-variation-forces-q-congruent-to-one)
  - [2.4 Generic, scalar, and vexing level change](#24-generic-scalar-and-vexing-level-change)
- [3. The one-prime datum without hidden global hypotheses](#3-the-one-prime-datum-without-hidden-global-hypotheses)
  - [3.1 Residual and coefficient-prime data](#31-residual-and-coefficient-prime-data)
  - [3.2 The represented local condition at the changed place](#32-the-represented-local-condition-at-the-changed-place)
  - [3.3 Automorphic carriers and faithful orders](#33-automorphic-carriers-and-faithful-orders)
  - [3.4 What is deliberately not part of the definition](#34-what-is-deliberately-not-part-of-the-definition)
- [4. The imported one-prime level-change package](#4-the-imported-one-prime-level-change-package)
  - [4.1 The exact residual kernel](#41-the-exact-residual-kernel)
  - [4.2 The abelian Ihara hypothesis](#42-the-abelian-ihara-hypothesis)
  - [4.3 Consequences after the hypothesis is supplied](#43-consequences-after-the-hypothesis-is-supplied)
  - [4.4 The six lowering conditions](#44-the-six-lowering-conditions)
- [5. The one-prime type complex](#5-the-one-prime-type-complex)
  - [5.1 Primary and companion lattices](#51-primary-and-companion-lattices)
  - [5.2 The incidence complex and its Tor term](#52-the-incidence-complex-and-its-tor-term)
  - [5.3 The scalar-twist face](#53-the-scalar-twist-face)
  - [5.4 Support is not faithfulness](#54-support-is-not-faithfulness)
- [6. The conditional one-prime R=T theorem](#6-the-conditional-one-prime-rt-theorem)
  - [6.1 The explicit comparison hypotheses](#61-the-explicit-comparison-hypotheses)
  - [6.2 Full support and the reduced image](#62-full-support-and-the-reduced-image)
  - [6.3 The reduced comparison and the full-equality criterion](#63-the-reduced-comparison-and-the-full-equality-criterion)
  - [6.4 Descent to finite level and fixed characters](#64-descent-to-finite-level-and-fixed-characters)
- [7. The modularity-lifting conclusion](#7-the-modularity-lifting-conclusion)
  - [7.1 The one-prime application theorems](#71-the-one-prime-application-theorems)
  - [7.2 Recovery of an automorphic representation](#72-recovery-of-an-automorphic-representation)
  - [7.3 Coefficient extension](#73-coefficient-extension)
  - [7.4 Solvable base change and descent](#74-solvable-base-change-and-descent)
  - [7.5 Exact exceptional boundaries](#75-exact-exceptional-boundaries)
- [8. The several-place application boundary](#8-the-several-place-application-boundary)
  - [8.1 Why two saturated edges do not make a saturated square](#81-why-two-saturated-edges-do-not-make-a-saturated-square)
  - [8.2 The mixed Ihara module](#82-the-mixed-ihara-module)
  - [8.3 Top-degree concentration is equivalent to mixed vanishing](#83-top-degree-concentration-is-equivalent-to-mixed-vanishing)
  - [8.4 Ordered quotient cubes and higher mixed classes](#84-ordered-quotient-cubes-and-higher-mixed-classes)
  - [8.5 Product residue is a derived comparison](#85-product-residue-is-a-derived-comparison)
  - [8.6 A genuinely joint support criterion](#86-a-genuinely-joint-support-criterion)
  - [8.7 When joint augmentation is formal](#87-when-joint-augmentation-is-formal)
  - [8.8 The exact proved boundary](#88-the-exact-proved-boundary)
- [9. The finite-set application theorems](#9-the-finite-set-application-theorems)
  - [9.1 What iteration actually proves](#91-what-iteration-actually-proves)
  - [9.2 The hypotheses for a simultaneous theorem](#92-the-hypotheses-for-a-simultaneous-theorem)
  - [9.3 The potential-modularity application](#93-the-potential-modularity-application)
  - [9.4 The FLT boundary](#94-the-flt-boundary)
- [10. Scope and conclusion](#10-scope-and-conclusion)
  - [10.1 The direct finite-set theorem](#101-the-direct-finite-set-theorem)
  - [10.2 The geometric alternative](#102-the-geometric-alternative)
  - [10.3 Final synthesis](#103-final-synthesis)

## 1. The modularity-lifting application

### 1.1 Minimal and nonminimal deformation spaces

Let $F$ be a totally real field, let $\ell$ be an odd prime, and let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{1.1}
$$

be a continuous absolutely irreducible representation over a finite field of characteristic
$\ell$. A minimal modularity-lifting theorem fixes a determinant and one represented local
condition at every place, then identifies the universal deformation ring with the faithful
Hecke order for the matching automorphic problem. It propagates automorphy through that one
global deformation problem.

A nonminimal theorem changes at least one local condition. Even at one place $v\nmid\ell$,
this introduces three questions which the minimal equality does not answer. The new local
component must be represented integrally. An automorphic carrier must meet that component at
the primitive integral scale. Finally the deformation action on that carrier must be faithful,
not merely nonzero at characteristic-zero points.

The relevant comparison therefore has the form

$$
R_v^{\mathrm{nm}}\longrightarrow\mathbb T_v^{\mathrm{nm}},
\tag{1.2}
$$

where the arrow is furnished by an order-valued Galois representation. Reciprocity gives
surjectivity. The mathematical content of nonminimal modularity lifting is injectivity.
Equality of generic fibers, equality of dimensions, or equality of one congruence length does
not prove it.

### 1.2 What one changed place must provide

One changed place has a coherent geometric model. The two maps from hyperspecial level to
Iwahori level form an incidence complex. Its primary form detects the chosen packet; its
companion is needed for integral adjunction. Nearby cycles identify its extreme term with a
graph lattice, and node uniformization compares that graph lattice with a definite
quaternionic carrier. On the deformation side a line-enhanced special condition records the
same orientation and monodromy relation.

These descriptions have to agree before patching. In particular, the following assertions
are different:

1. the two degeneracy maps are injective after reduction;
2. their integral image is saturated;
3. a selected type preserves that image;
4. the graph residue has coefficient one;
5. the selected deformation component is in the support;
6. the deformation ring acts faithfully.

The first five can lead to the sixth only after a reducedness or nilpotent-control argument.
The purpose of this book is to keep these stages separate and then apply the supported
one-prime comparison to characteristic-zero modularity, before stating the exact extra data
needed for the same application at several places.

### 1.3 The finite-set demand from the FLT argument

The modularity-lifting theorem used in the FLT blueprint is stated for a finite set $S$ of
prime-to-$\ell$ places. A representation is allowed a controlled tame special condition at
every member of $S$. Thus a one-prime theorem is not by itself the endpoint required there.
One needs either a simultaneous finite-set theorem or an iteration in which every hypothesis
is reverified after every change of level. A simultaneous theorem need not be proved by a
several-place incidence cube: it can instead come from direct patching at the final finite
local problem, as in Section 1.5.

For two places the automorphic object is a square, not two unrelated arrows. Its total
complex measures the intersection of the two old images. Edgewise saturation does not
determine that intersection. The first mixed kernel will be isolated in Chapter 8. It is a
conclusion that must be proved; it is not included in any definition of a locally admissible
place. In the downstream construction, one selected base place is required to split completely
in a totally real extension $F'/F$ of positive even degree. It already produces $[F':F]$
active places, with $[F':F]\ge2$, before any specialization-dependent bad places are added.
Thus a geometric level-change proof has a genuinely several-place issue even when no new bad
reduction is discovered. This does not make mixed cubical exactness a hypothesis of every
possible proof of the blueprint theorem.

### 1.4 The application routes and their boundary

The application has five routes, and their hypotheses must not be exchanged. The later
one-place discussion separates the scalar line-special family from the generic and vexing
families, whose carriers must be constructed independently. With several active places, one
may instead verify an ordered chain of one-place comparisons. A simultaneous all-point route
would require $({\rm FACE}_P)$, $({\rm CUBE}_P)$, $({\rm MIX}_P)$,
$({\rm PROD}_P)$, $({\rm JSUP}_P)$, $({\rm AUG}_P)$, and
$({\rm REC}_P)$; on the iterated-switch route $({\rm PROD}_P)$ includes the integral
Beck--Chevalley datum $({\rm IBC}_P)$. For one named point, a smaller possible route uses the
torsion-free top of an actual final cube and occurrence of the one global component through
that point. These alternatives motivate the constructions of the later chapters but are not
used in the direct theorem below. The fifth route is the direct paired patching comparison
$({\rm IAV}_S)$ of Section 1.5; it proves the finite-set theorem without first proving any of
the cubical hypotheses. Section 1.5A records a second consequence: when its desired ring is
the broad unipotent ring containing an unramified minimal quotient, exact recovery makes the
whole desired ring finite and transfers that finiteness and pointwise automorphy to the
minimal quotient.

The unconditional algebra used by these routes has two parts. First, once the exact one-prime
geometric, reciprocity, and support hypotheses are stated separately, a short annihilator
argument identifies the reduced finite-level deformation ring with the faithful finite Hecke
order. This is enough for characteristic-zero modularity because a map to a DVR kills
nilpotents. In the scalar-residual line-special range, Book 175 now closes the
scheme-theoretic one-prime comparison when the coherent clean unpadded auxiliary system is
retained: its enhanced balanced presentation has the same number of absolute variables as the
diamond source, and equal-variable rigidity makes the patched one-prime action faithful. Exact
marked augmentation then gives full finite-level $R=T$ and
all characteristic-zero enhanced tangent--Selmer vanishings. Without such a coherent
auxiliary system, global reducedness, equivalently the branchwise torsion-cotangent condition,
remains the exact alternative input.
Second, for a finite ordered cube the total complex is reduced formally to successive
quotient-new cubes. For two places its first homology is identified exactly with a mixed Ihara
kernel; for three or more places the later kernels live on iterated-new quotients.

The geometric routes require arithmetic inputs beyond the local deformation theory. The core
finite-level comparison depends on the actual automorphic localization, the separate
type-incidence and type-Ihara hypotheses, the one-boundary support datum, and the exact
reciprocity order. The scalar family also uses an effective global ray quotient and strict
twist identities. Book 174 constructs the strict one-place quotient. A several-place
geometric argument would additionally have to construct a joint quotient and enlarge the
fixed spectator datum by its actual conductor places; this issue is outside the direct
source-patching theorem. The
richer level-changing and component package additionally depends on a
finite family of abelian Ihara vanishings, primitive type residue, and typed node
uniformization when a switched carrier is used. The finite-set package further requires
vanishing of all mixed homology, a coefficient-one product-residue comparison, joint
component support, and simultaneous augmentation. The statements below never insert these
assertions into the word “clean” or into a local definition. The one-prime and finite-set
theorems are therefore stated with their exact conditional inputs.

For one already named characteristic-zero point there is a smaller finite-level theorem.
The torsion-free top of the actual global cube is a canonical joint carrier even when mixed
torsion survives. Pointwise modularity then needs simultaneous branch verification,
reciprocity on that carrier, and support on the single global component through the point.
This does not prove the stronger mixed, Beck--Chevalley, or all-component support theorems and
does not commute torsion-free quotient formation through nonflat augmentation.

### 1.5 The direct finite-set Ihara-avoidance route

The automorphy-lifting argument cited by the FLT blueprint does not begin by changing the
level at the members of $S$ one at a time. Let $\rho$ be the lift to be proved automorphic
and let $\rho_0$ be an automorphic lift of the same residual representation. After a solvable
totally real base change, its direct finite-set input $({\rm IAV}_S)$ has the following four
parts.

1. The determinants of $\rho$ and $\rho_0$ agree; above $\ell$ the two lifts have the same
   regular Fontaine--Laffaille weights and the required crystalline or finite-flat condition;
   and the residual image supplies the Taylor--Wiles prime-selection and descent hypotheses.
   After the solvable base change, both prime-to-$\ell$ inertia actions are unipotent, and at
   every place where either lift ramifies the residual local representation is trivial and
   the residue cardinality is congruent to one modulo $\ell$.
2. Over the complete tensor product of the local deformation rings, construct the desired
   raw problem $R^{\rm loc}$, with tame characteristic polynomial $(X-1)^2$, and the raw
   avoidance problem $R^{{\rm loc},\prime}$, with polynomial
   $(X-\zeta_\ell)(X-\zeta_\ell^{-1})$. Their literal special fibers are identified. The
   avoidance ring is flat and integral; the reduced horizontal desired quotient is flat and
   equidimensional, and the two horizontal desired components specialize bijectively to the
   two minimal components of the common, generally nonreduced, special fiber. Theorem 1.1C
   proves these assertions. The raw desired ring itself is not asserted flat.
3. Patch synchronized Taylor--Wiles systems over the **local presentation sources**
   $P_\infty^\bullet=R_{\rm loc}^\bullet[[\mathbf y]]$, retaining the exact balanced
   equality $\dim P_\infty^\bullet=\dim S_\infty^{\rm fr}$ with every partial-frame
   variable included, and retain the finite action images. The
   avoidance source is a Cohen--Macaulay domain, so the full-depth avoidance module is
   faithful. Reduction modulo the uniformizer transfers full support to the desired
   module; the horizontal component bijection then lifts it to every desired component.
   Section 1.5D proves this source-patching step. It never asks an arbitrary quotient by
   global relations to preserve local components.
4. Descend that support statement to the original finite-level deformation problem, recover
   automorphy of $\rho$ over the solvable extension, and apply the separately verified
   solvable automorphic descent.

Here is the support-transfer step in a form that does not hide any arithmetic input. If
$A$ is a noetherian local ring with an element $\varpi$ and $B=A/\varpi A$, say that
specialization is **component-bijective** if every $\mathfrak p\in\operatorname{Min}(A)$
has a unique prime $\overline{\mathfrak p}$ minimal over
$\mathfrak p+(\varpi)$, this prime is minimal over $(\varpi)$, and

$$
\mathfrak p\longmapsto\overline{\mathfrak p}/(\varpi)
\tag{1.3}
$$

is a bijection from $\operatorname{Min}(A)$ to $\operatorname{Min}(B)$. This is the exact
meaning of the component-bijection phrase in item 2; equality of the numbers of components
without the specialization map is not enough.

**Proposition 1.1 (paired special-fiber support transfer).** Let $\mathcal O$ be a complete
DVR with uniformizer $\varpi$. Let $R_\infty^{\rm des}$ and
$R_\infty^{\rm av}$ be complete noetherian local $\mathcal O$-algebras, equipped with a
fixed identification

$$
B\simeq R_\infty^{\rm des}/\varpi
 \simeq R_\infty^{\rm av}/\varpi .
\tag{1.4}
$$

Let $M_\infty^{\rm des}$ and $M_\infty^{\rm av}$ be finite modules over the respective
rings and suppose that their actions reduce to one $B$-action under an isomorphism

$$
M_\infty^{\rm des}/\varpi M_\infty^{\rm des}
\simeq
M_\infty^{\rm av}/\varpi M_\infty^{\rm av}.
\tag{1.5}
$$

Assume:

1. $\operatorname{Supp}_{R_\infty^{\rm av}}M_\infty^{\rm av}
   =\operatorname{Spec}R_\infty^{\rm av}$;
2. the support of $M_\infty^{\rm des}$ is a union of irreducible components of
   $\operatorname{Spec}R_\infty^{\rm des}$; and
3. specialization on $R_\infty^{\rm des}$ is component-bijective in the sense of (1.3).

Then

$$
\operatorname{Supp}_{R_\infty^{\rm des}}M_\infty^{\rm des}
=\operatorname{Spec}R_\infty^{\rm des}.
\tag{1.6}
$$

**Proof.** Let $\mathfrak q$ be any prime of $B$ and let
$\widetilde{\mathfrak q}^{\rm av}$ be its inverse image in $R_\infty^{\rm av}$. Full
support makes $(M_\infty^{\rm av})_{\widetilde{\mathfrak q}^{\rm av}}$ nonzero. If its
quotient by $\varpi$ were zero, Nakayama's lemma over the local ring
$(R_\infty^{\rm av})_{\widetilde{\mathfrak q}^{\rm av}}$ would make the module zero.
Thus (1.5) has full support over $B$.

Suppose that the desired support omits the component defined by
$\mathfrak p\in\operatorname{Min}(R_\infty^{\rm des})$, and let
$\overline{\mathfrak p}$ be its prime in (1.3). Full support of (1.5) places
$\overline{\mathfrak p}$ in the support of $M_\infty^{\rm des}$. Since that support is a
union of components, some included minimal prime $\mathfrak p'$ is contained in
$\overline{\mathfrak p}$. The latter is minimal over $(\varpi)$, hence also minimal over
$\mathfrak p'+(\varpi)$. Component-bijectivity sends both $\mathfrak p$ and
$\mathfrak p'$ to $\overline{\mathfrak p}/(\varpi)$, so $\mathfrak p'=\mathfrak p$,
contrary to omission. Every component occurs, proving (1.6). $\square$

This proposition is purely topological: (1.6) says that the desired action is nearly
faithful, not faithful through nilpotent thickenings. That is exactly what a
characteristic-zero automorphy statement needs once exact control has recovered the
finite-level module. Indeed, suppose the desired source $B_\infty$ and patched module
$L_\infty$ retain

$$
 B_\infty/\mathfrak a_\infty B_\infty\simeq R^{\rm des},
 \qquad
 L_\infty/\mathfrak a_\infty L_\infty\simeq M^{\rm des}.
\tag{1.7}
$$

Full support descends through these two isomorphisms by Nakayama's lemma. If
$\mathbb T^{\rm des}$ denotes the actual image of $R^{\rm des}$ on $M^{\rm des}$, then

$$
R^{\rm des}\twoheadrightarrow\mathbb T^{\rm des},
\qquad
\ker(R^{\rm des}\to\mathbb T^{\rm des})^n=0
\quad\text{for some }n.
\tag{1.8}
$$

Indeed, the kernel is the annihilator of a full-support finite module and hence lies in the
nilradical. Every map from $R^{\rm des}$ to a characteristic-zero domain kills this kernel
and factors through the finite automorphic action. This is Book 145, Corollary 17.4. No
quotient of the patched acting image occurs in the argument. Exact augmented acting-image
equality is stronger and requires the separate saturation hypothesis of Book 145,
Corollary 17.5.

There is one stronger finiteness consequence, useful whenever a later construction needs a
finite special fibre, which does not require scheme-theoretic $R=\mathbb T$.

**Lemma 1.1A (nilpotent recovery preserves finiteness).** Let $A$ be a noetherian
$\mathcal O$-algebra and let $A\twoheadrightarrow C$ be a quotient whose kernel $J$ is
nilpotent. If $C$ is finite as an $\mathcal O$-module, then $A$ is finite as an
$\mathcal O$-module. In particular, $A/\varpi A$ is a finite-dimensional $k$-algebra.

**Proof.** Choose $n$ with $J^n=0$. Each quotient
$J^i/J^{i+1}$ is a finite $A/J=C$-module: it is finitely generated because $A$ is
noetherian, and $J$ acts trivially on it. The filtration

$$
0=J^n\subset J^{n-1}\subset\cdots\subset J\subset A
\tag{1.8a}
$$

therefore has $\mathcal O$-finite successive quotients. Hence $A$ is
$\mathcal O$-finite. $\square$

**Corollary 1.1B (full-support finite recovery).** Let $R$ be a noetherian
$\mathcal O$-algebra acting on a finite free $\mathcal O$-module $M$, and let
$\mathbb T$ be its image in $\operatorname {End}_{\mathcal O}(M)$. If
$\operatorname {Supp}_R(M)=\operatorname {Spec}R$, then
$\ker(R\to\mathbb T)$ is nilpotent. Consequently $R$ is finite over $\mathcal O$, and every
map from $R$ to a characteristic-zero field factors through $\mathbb T$.

**Proof.** Full support puts $\operatorname {Ann}_R(M)$ in the nilradical. Since $R$ is
noetherian, this annihilator is nilpotent. The image $\mathbb T$ is finite over
$\mathcal O$ because it is an $\mathcal O$-submodule of the finite free module
$\operatorname {End}_{\mathcal O}(M)$. Lemma 1.1A makes $R$ finite. A map to a field kills
the nilpotent kernel and therefore factors through $\mathbb T$. $\square$

Thus the nilpotent recovery (1.8), together with Corollary 1.1B, proves finiteness of the
**whole** desired ring, including its nilpotent
thickening, whenever the finite Hecke action is $\mathcal O$-finite. This does not make the
canonical map injective. It says only that topological full support plus exact recovery is
strong enough for a finite-special-fibre argument. A finite collection of generic points,
or generic finiteness after inverting $\varpi$, is not enough; for example
$\mathcal O[[x]]/(\varpi x)$ has one finite generic branch but infinite special fibre.

Theorem 1.1C below proves the paired raw local rings, their common scheme-theoretic residual
fiber, avoidance integrality and Cohen--Macaulayness, and the horizontal desired component
bijection. Proposition 1.1D proves common Taylor--Wiles prime selection, identifies the
definite automorphic modules modulo $\varpi$, and retains exact recovery. The remaining step
is not a new automorphic-component theorem. The quotient-first formulation creates that
failure of implication by replacing the local presentation source with an arbitrary quotient
by global relations. Sections 1.5C--1.5D keep the source action instead. The balanced Wiles count
makes its dimension equal to the diamond-source dimension; the avoidance source is a domain,
so its finite action quotient cannot have a nonzero kernel. The common special fiber then
transfers support, and the horizontal component bijection lifts it to the reduced desired
source. This proves $({\rm CIAV}_P)$ in Theorem 1.1H.

Book 67 supplies the tame equations but stops before the scalar calculation proved here.
Books 143--145 supply the prime selection, synchronized shadows, source support, and
module-level recovery, while Book 152 supplies the actual paired definite modules. Book 146
explains why component hopping cannot be inferred after taking an arbitrary quotient, and
Book 172 proves the sharp-source mechanism for a regular minimal source. Section 1.5D
specializes the newer paired source theorems to the reducible desired source and the integral
avoidance source.

In particular, the preferred route is not the all-component boundary-occurrence theorem of
Chapter 8. It requires neither the mixed Ihara modules (8.5), product residue, an
iterated-switch Beck--Chevalley cube, type-Ihara, nor constant-row abelian Ihara. Those are
prerequisites only for the geometric alternatives. For the potential-modularity application
$S=P_{\rm act}$ means the whole actual active set, including every dyadic place above the
distinguished base place; the paired construction must be simultaneous on that entire set.
It may be invoked only after the further base change has made the residual local
representations trivial and $q_w\equiv1\pmod\ell$ at every $w\in P_{\rm act}$.

### 1.5A The finite-fibre consequence and the target-minimal quotient

There is a second application of the same theorem which is logically different from level
lowering. Let $F$ be a totally real field on which the places above $2\ell$ split completely,
and suppose that both $\bar\rho|_{G_F}$ and
$\bar\rho|_{G_{F(\zeta_\ell)}}$ are absolutely irreducible. Let $P$ be a finite set of
non-dyadic places away from $\ell$ at which an actual upper automorphic packet is special
while the minimal problem is unramified. At every $v\in P$ require
$\bar\rho|_{G_{F_v}}$ to be trivial and $q_v\equiv1\pmod\ell$. Define the **broad unipotent
problem** $\mathcal D_F^{\rm uni}(P)$ as follows:

1. at places above $2$ it imposes the same named dyadic signed-special quotient as the
   minimal problem;
2. at places above $\ell$ it imposes the same selected weight-$\{0,1\}$ finite-flat quotient;
3. away from $P\cup\{w:w\mid2\ell\}$ it is unramified; and
4. at every $v\in P$ it imposes only the tame-unipotent closure, with inertial characteristic
   polynomial $(X-1)^2$, and imposes no chosen nonzero-monodromy line, special sign, or
   Steinberg-branch equation.

Write its represented ring as $R_F^{\rm uni}(P)$. Setting every inertia generator equal to
the identity is a closed condition at each $v\in P$. Consequently the exact signed-special
minimal functor is a closed subfunctor and there is a canonical surjection

$$
R_F^{\rm uni}(P)\twoheadrightarrow R_F^{\rm SP}.
\tag{1.8b}
$$

Both the upper special packet and every future minimal point lie in the broad problem. This
ring must not be confused with the enhanced sign-selected special ring attached to the upper
packet. In the latter ring the line, sign, and Frobenius-incidence equation remain part of
the closed special branch even on its $N=0$ boundary. An arbitrary unramified lift need not
satisfy that incidence equation, so in general there is no map from the exact upper special
ring onto $R_F^{\rm SP}$; this is the local functoriality obstruction recorded in Book 170,
Section 14.2.

The point of the broad problem is that the upper packet supplies an actual automorphic point
before any minimal point is known, while the quotient (1.8b) contains every minimal point that
may later be constructed. The prepared target theorem in Section 1.5D starts from that upper
packet, uses its primitive definite transfer to produce the nonzero common residual module,
and patches the broad desired source against the avoidance source. Its module-level recovery
gives the map from $R_F^{\rm uni}(P)$ to the finite Hecke action a nilpotent kernel. Lemma
1.1A then makes the whole broad ring finite, and (1.8b) passes the finite-special-fibre and
pointwise-automorphy conclusions to the minimal quotient. No minimal point is an antecedent
of this construction.

Patching only the upper packet's exact sign-selected special component would not suffice:
the broad desired and avoidance sources must be carried together. The direct source-patching
argument is independent of the optional level-lowering route
$({\rm DLO}_P)+({\rm CLN}_{\min})$, which remains useful only when the stronger clean minimal
$R=\mathbb T$ datum is wanted.

### 1.5B The scalar paired rings and the exact patched boundary

We now construct the local pair which was left as item 2 of $({\rm IAV}_S)$. The distinction
between a literal represented ring and its reduced horizontal quotient is essential. It is
also the reason that the argument must be carried out with framed rings at the scalar residual
point.

Let $r>2$ be the coefficient residue characteristic, let $(\mathcal O,(\varpi),k)$ be a
complete coefficient DVR containing a primitive $r$th root $\zeta$, and let $Q$ be the
cardinality of a prime-to-$r$ residue field, with $Q\equiv1\pmod r$. After the scalar twist
used in the IAV preparation, suppose that the residual tame pair is

$$
\overline F=\overline T=1.
\tag{1.8c}
$$

Fix an unramified determinant with $\det F=d\equiv1\pmod\varpi$ and $\det T=1$. In the
cyclotomic normalization $d=Q$. More generally Hensel's lemma gives a unique $b\equiv1$
with $b^2=d/Q$, so the only change below is that the two special Frobenius roots are $Qb,b$.

**Theorem 1.1C (the scalar paired tame rings).** In the setting above, let
$A_{\rm des}$ be the literal framed tame deformation ring with inertial characteristic
polynomial $(Z-1)^2$, and let $A_{\rm av}$ be the literal framed ring with inertial
characteristic polynomial

$$
(Z-\zeta)(Z-\zeta^{-1}).
\tag{1.8d}
$$

Then:

1. there is a canonical identification of complete local $k$-algebras

   $$
   A_{\rm des}/\varpi\simeq A_{\rm av}/\varpi=:B;
   \tag{1.8e}
   $$

2. $A_{\rm av}$ is $\mathcal O$-flat, Cohen--Macaulay, and integral of relative dimension
   three;
3. $A_{\rm des}$ has exactly two horizontal minimal primes, the unramified prime $U$ and
   the special prime $S$; its reduced quotient is $\mathcal O$-flat, Cohen--Macaulay, and
   equidimensional of relative dimension three, but is not a complete intersection; and
4. $B$ has exactly two minimal primes $\overline U,\overline S$, and specialization sends
   $U$ to $\overline U$ and $S$ to $\overline S$. Thus specialization is
   component-bijective on the horizontal topology.

The common ring $B$ is generally nonreduced, and $A_{\rm des}$ itself need not be flat or
reduced. In particular, replacing $A_{\rm des}$ by its reduced flat quotient destroys the
scheme-theoretic equality (1.8e), although it preserves the displayed bijection of minimal
primes.

**Proof.** Write

$$
F=aI+X,
\qquad
X=\begin{pmatrix}x&y\\ z&-x\end{pmatrix},
\qquad
a^2-(x^2+yz)=d.
\tag{1.8f}
$$

Since $a\equiv1$ and $2$ is a unit, the last equation eliminates $a$ uniquely. For the
avoidance ring put

$$
c={\zeta+\zeta^{-1}\over2},\qquad
h={\zeta-\zeta^{-1}\over2},\qquad
T=cI+Y,qquad
Y=\begin{pmatrix}u&v\\ w&-u\end{pmatrix}.
\tag{1.8g}
$$

The polynomial in (1.8d) divides $Z^r-1$, and $Q\equiv1\pmod r$, so $T^Q=T$. The tame
relation is therefore $[F,T]=0$. The determinant and commutator equations give

$$
A_{\rm av}\simeq
{\mathcal O[[x,y,z,u,v,w]]\over
 (u^2+vw-h^2,\;xv-yu,\;zu-xw,\;yw-zv)}.
\tag{1.8h}
$$

The last three equations are the $2$-by-$2$ minors of the matrix with rows
$(x,y,z)$ and $(u,v,w)$. The rank-at-most-one determinantal quotient is a
Cohen--Macaulay domain by its Eagon--Northcott resolution. The quadric equation is a
non-zero-divisor there and remains regular modulo $\varpi$, so the resulting quotient is
Cohen--Macaulay and $\varpi$ remains a non-zero-divisor. On the generic fiber $Y$ lies on
the geometrically integral quadric $u^2+vw=h^2$ and $X=tY$. This proves integrality,
flatness, Cohen--Macaulayness, and relative dimension three.

For the desired ring put $T=I+Y$. Cayley--Hamilton turns the inertial characteristic
polynomial into $u^2+vw=0$, while the tame relation is

$$
(aI+X)Y=QY(aI+X).
\tag{1.8i}
$$

Reducing (1.8h) and (1.8i) modulo $\varpi$ gives in both cases

$$
B\simeq
{k[[x,y,z,u,v,w]]\over
 (u^2+vw,\;xv-yu,\;zu-xw,\;yw-zv)},
\tag{1.8j}
$$

which proves (1.8e). The common fiber is not reduced. Indeed, with

$$
\beta=\operatorname {tr}(XY)=2xu+yw+zv,
\tag{1.8k}
$$

commutation gives $2XY=\beta I$, hence $\beta^2=0$ because $\det Y=0$. It is not the zero
class: over $k[\alpha,\gamma]/(\alpha^2,\gamma^2)$ take
$X=\alpha\operatorname {diag}(1,-1)$ and
$Y=\gamma\operatorname {diag}(1,-1)$.

One minimal prime of (1.8j) is

$$
\overline U=(u,v,w).
\tag{1.8l}
$$

Off $Y=0$, a nonzero nilpotent in $\mathfrak {sl}_2$ has one-dimensional traceless
centralizer, so $X$ and $Y$ lie on the same isotropic line. The closure of this locus is the
second prime $\overline S$. Its irreducibility is visible from

$$
X=\lambda n(r_0,s_0),\qquad
Y=\mu n(r_0,s_0),\qquad
n(r_0,s_0)=
\begin{pmatrix}r_0s_0&-r_0^2\\s_0^2&-r_0s_0\end{pmatrix}.
\tag{1.8m}
$$

Every point either has $Y=0$ or belongs to this closure. Hence $\overline U$ and
$\overline S$ are exactly the minimal primes of $B$.

The desired generic fiber likewise has two pieces. On $U=(Y)$, Frobenius is arbitrary with
fixed determinant, giving $\mathcal O[[x,y,z]]$. On the nonzero-$Y$ locus, (1.8i) forces the
Frobenius roots to be $Qb,b$; its closure $S$ is integral of relative dimension three. Its
special fiber has unique minimal prime $\overline S$: the trace equation
$\operatorname {tr}F=(Q+1)b$ and the determinant force $x^2+yz=0$ modulo $\varpi$, and the
saturated incidence forces $\operatorname {tr}(XY)=0$. The two primes in (1.8l)--(1.8m)
exhaust the special fiber, so there is no vertical minimal prime. The reduced ring embeds in

$$
A_{\rm des}/U\times A_{\rm des}/S.
\tag{1.8n}
$$

Both factors are torsion-free over the DVR, so the reduced ring is torsion-free and hence
flat. It is also Cohen--Macaulay. Indeed, put
$\epsilon=(Q-1)b/2$. The unramified component is the regular ring
$A_{\rm des}/U=\mathcal O[[x,y,z]]$, and its intersection with the special component is

$$
A_{\rm des}/(U+S)
\simeq\mathcal O[[x,y,z]]/(x^2+yz-\epsilon^2),
$$

a flat Cohen--Macaulay hypersurface of dimension three. The special component is flat of
dimension four. Its special fiber is the affine cone over the rational normal scroll
$S(2,2)$: the parametrization (1.8m) identifies its ideal with the two-by-two minors of

$$
\begin{pmatrix}-y&x&-v&u\\x&z&u&w\end{pmatrix}.
$$

This ideal has the expected height three, and its signed Eagon--Northcott complex
$0\to R^3\to R^8\to R^6\to R$ is exact; Auslander--Buchsbaum therefore gives depth three
for the quotient. Thus the special fiber is Cohen--Macaulay, and the regular element
$\varpi$ makes $A_{\rm des}/S$ Cohen--Macaulay of dimension four. The union sequence

$$
0\longrightarrow A_{\rm des}^{\rm red}
\longrightarrow A_{\rm des}/U\oplus A_{\rm des}/S
\longrightarrow A_{\rm des}/(U+S)\longrightarrow0
$$

and the depth lemma now give depth four for $A_{\rm des}^{\rm red}$. It is not a complete
intersection. Since $\varpi$ is regular, its reduced special fiber would otherwise be a
complete intersection; but in the
six-variable regular residual ambient ring its height-three ideal has the five independent
quadratic minimal generators $u^2+vw$, $\operatorname {tr}(XY)$, and the three entries of
$[X,Y]$ (as well as the higher incidence equations). Thus its minimal number of generators
is greater than its height. This proves the component and Cohen--Macaulay assertions.

Finally, taking traces in (1.8i) gives

$$
(Q-1)\operatorname {tr}(FY)=0.
\tag{1.8o}
$$

The reduction of this torsion element is the nonzero nilpotent (1.8k), while it vanishes on
both horizontal generic components. This proves the final raw-versus-reduced warning.
$\square$

The framed qualification is forced. Both raw rings have six-dimensional residual tangent
space: three trace-zero Frobenius directions and three trace-zero inertia directions. The
linearized tame relation vanishes because $Q=1$ in $k$. At the trivial residual point the
centralizer is all of $M_2(k)$ and strict conjugation has zero differential, so no represented
coarse unframed ring is obtained by subtracting three framing variables. This is precisely
the exceptional case which Book 67 leaves open; the distinct-residual-Frobenius hypothesis of
Book 138, Theorem 10.2 also does not apply.

For a finite active set $P$, completed tensor product gives $2^{|P|}$ desired horizontal
components and one geometrically integral avoidance component, and the product specialization
is component-bijective. Here the unchanged coefficient-prime, dyadic, determinant, and frame
factors must be restricted to the same geometrically integral or formally smooth selected
components. If an unchanged factor has several components, the assertion is made
componentwise rather than calling the whole avoidance product irreducible. Book 64's
completed-product flatness and dimension theorems justify this passage.

The automorphic congruence is equally explicit. For $v\in P$, let $\theta_v$ be the order
$r$ character of the $r$-part of $k(v)^\times$ sending a chosen generator to $\zeta$, and put

$$
L_v^{\rm av}
=\operatorname {Ind}_{B(k(v))}^{\operatorname {GL}_2(k(v))}
 (\theta_v\otimes\theta_v^{-1}),
\qquad
L_v^{\rm des}
=\operatorname {Ind}_{B(k(v))}^{\operatorname {GL}_2(k(v))}1.
\tag{1.8p}
$$

These are the integral principal and Iwahori-incidence lattices of Book 138. Since
$\overline\theta_v=1$, finite induction gives a canonical equivariant isomorphism

$$
L_v^{\rm av}/\varpi\simeq L_v^{\rm des}/\varpi.
\tag{1.8q}
$$

Tensoring (1.8q) over $P$ and using the same definite class set proves the corresponding
mod-$\varpi$ identification of automorphic modules. At non-neat level one uses Book 152's
effective stabilizer condition; it is not legitimate to commute arbitrary stabilizer
invariants with reduction. Deep Taylor--Wiles levels are disjoint from $P$, so the same
torsor and diamond action occur on both sides.

**Proposition 1.1D (what synchronizes formally).** Assume the residual image hypotheses of
Book 143, including its detector and padding conditions, and the clean definite class-set and
local-compatibility hypotheses required by Books 145 and 152. Assume also one of the
varying-$Q_N$ uniform-rank alternatives of Book 152, Proposition 20.6. For the paired
problems of Theorem 1.1C:

1. their residual local deformation functors are identically embedded in the same
   unrestricted matrix deformation functor; hence their strict-at-$T$ relative Selmer
   structures are identical and one Taylor--Wiles set $Q_N$ kills both relative dual Selmer
   groups at every depth;
2. the finite-level desired and avoidance modules have the common reduction (1.8q), with the
   same away Hecke operators and Taylor--Wiles diamonds;
3. Book 152, Proposition 20.6 passes to a cofinal constant-rank family, and Book 144's
   finite-shadow diagonalization patches the two systems simultaneously; their patched
   reductions are identified after base change to the common nilpotent residual quotient,
   not necessarily before that base change; and
4. Book 152's exact diamond coinvariants and the marked inverse-limit construction retain
   exact module and intermediate represented-ring recovery. The recovered finite action has
   nilpotent kernel once source support is known; exact acting-image recovery is the stronger
   optional conclusion under Book 145, Corollary 17.5. Book 109 then gives descent only under
   its stated cyclic-tower, selectedness on every controlled component, invariance,
   attachment, irreducibility, and local-antecedent hypotheses.

**Proof.** Equation (1.8e) comes from two conditions on the same residual tame matrices, so
its identification commutes with the forgetful maps to the unrestricted functor. Book 143,
Proposition 15.1 identifies the tangent images and Tate orthogonals inside the same local
cohomology groups; Theorem 15.2 then chooses one $Q_N$ for the common strict relative
structure. Equations (1.8p)--(1.8q) identify the finite modules before localization; the
common residual Hecke idempotent and the one coefficient-independent projective stabilizer
group in Book 152 preserve the identification after localization and at deep level. Theorem
20.5 gives fixed-$Q_N$ freeness and coinvariants. Proposition 20.6 supplies the cofinal
constant rank needed to include both finite presentations, bases, actions, and augmentation
maps in one finite shadow. Book 144, Lemma 18.1 and Theorem 18.2 then preserve every marked
map, including the ring and module augmentation maps, and the residual module comparison
after base change to the common quotient. Once Proposition 1.1G supplies the sharp source
dimensions and Theorem 1.1H proves source support by Book 145, Theorem 17.3, Corollary 17.4
consumes these retained recovery maps to obtain the finite-level nilpotent kernel.
Corollary 17.5 is optional. $\square$

This proposition does not create the nonzero residual localization required by Theorem 20.5.
In Theorem 1.1J it comes from a primitive definite vector in the actual avoidance reference
packet; in Theorem 1.1K it comes from a primitive definite vector in the actual upper desired
packet. The marked reduction transports that one nonzero vector to the common residual
module. Without one of those actual packets, nonvanishing is not available. Even when it is
available, it does not prove full support on an arbitrary quotient, which is why the choice of
patching ambient ring matters.

If one first forms the global relation quotients in the notation of Book 145, one obtains

$$
R_\infty^{\bullet}
=R_{{\rm loc}}^{\bullet}[[\mathbf z,\mathbf x]]/
 (f_1^{\bullet},\ldots,f_b^{\bullet}),
\qquad \bullet\in\{{\rm des},{\rm av}\}.
\tag{1.8r}
$$

The congruences $f_i^{\rm des}\equiv f_i^{\rm av}\pmod\varpi$ do not control minimal
primes. Even the flat domain $\mathcal O[[x,y]]/(xy-\varpi)$ has two special-fiber
components, and quotienting a flat local source by $\varpi x$ creates a vertical component.
Thus the quotient-first argument would require the additional assertion

$$
({\rm PGC}_P):\qquad
\operatorname {Min}(R_\infty^{\rm des})
\longrightarrow
\operatorname {Min}(R_\infty^{\rm des}/\varpi)
\text{ is the specialization bijection induced by Theorem 1.1C.}
\tag{1.8s}
$$

and would separately require the avoidance support assertion

$$
\operatorname {Supp}_{R_\infty^{\rm av}}M_\infty^{\rm av}
=\operatorname {Spec}R_\infty^{\rm av}.
\tag{1.8t}
$$

Nonvanishing and integrality of $R_{\rm loc}^{\rm av}$ do not prove (1.8t) for this quotient.
The elementary model $R=\mathcal O[[x,y]]/(xy)$ with $M=R/(x)$ is flat over
$\mathcal O$, equidimensional, and maximal Cohen--Macaulay on its support, but misses the
component $(y)$. Section 1.5C retains these countermodels because they rule out a tempting
but invalid proof. Section 1.5D then bypasses both (1.8s) and (1.8t): it patches the module
as a module over $P_\infty^\bullet$ itself. The balanced dimension equality and the domain
property of $P_\infty^{\rm av}$ make its action faithful; the desired source's local
specialization theorem then transfers that faithful support. Thus $({\rm PGC}_P)$ is not an
extra input to the preferred proof, and $({\rm ACT}^{\rm av}_P)$ is proved on the correct
source.

### 1.5C Balanced patching, vertical cross-cotangents, and avoidance support

This subsection explains why patching after taking the global relation quotient does not by
itself prove component specialization or full support. First dispose of the raw-versus-
horizontal distinction from Theorem 1.1C. The nilradical $N_{\rm des}$ of the raw desired
local ring vanishes after inverting $\varpi$, because its generic fiber is the reduced union
of the unramified and special components. Since the ring is noetherian, every element of
$N_{\rm des}$ is therefore killed by a power of $\varpi$. Every finite-level automorphic
module, and hence the patched module, is $\mathcal O$-torsion-free, so its action kills
$N_{\rm des}$. Moreover

$$
B=A_{\rm des}/\varpi\twoheadrightarrow A_{\rm des}^{\rm red}/\varpi
\tag{1.8u}
$$

has nilpotent kernel and is a homeomorphism on spectra. Thus one may retain the raw ring for
the exact residual comparison while simultaneously marking its horizontal reduced quotient
for the depth calculation; Theorem 1.1C proves that quotient is Cohen--Macaulay. Quotienting
the later global ring by the image of
$N_{\rm des}$ again changes only a nilpotent ideal. This proves that the raw/reduced issue
introduces no additional _topological_ support hypothesis; it does not prove preservation of
components under the global relation ideal.

Now write the synchronized raw presentations as

$$
\begin{aligned}
 P_\infty^\bullet&=R_{\rm loc}^\bullet[[\mathbf z,\mathbf x]],\\
 R_\infty^\bullet&=P_\infty^\bullet/I_\infty^\bullet,\\
 A_\infty^\bullet&=R_\infty^\bullet/
       \operatorname {Ann}_{R_\infty^\bullet}M_\infty^\bullet,
 \qquad \bullet\in\{{\rm des},{\rm av}\}.
\end{aligned}
\tag{1.8v}
$$

The diagonal construction in Proposition 1.1D gives a complete local residual quotient
$C_\infty$ and surjections with nilpotent kernels

$$
P_\infty^{\rm des}/\varpi\twoheadrightarrow C_\infty
\twoheadleftarrow P_\infty^{\rm av}/\varpi,
\tag{1.8w}
$$

together with the base-changed module isomorphism

$$
\bigl(M_\infty^{\rm des}/\varpi\bigr)
 \otimes_{P_\infty^{\rm des}/\varpi}C_\infty
\xrightarrow{\sim}
\bigl(M_\infty^{\rm av}/\varpi\bigr)
 \otimes_{P_\infty^{\rm av}/\varpi}C_\infty,
\tag{1.8x}
$$

including the residual Hecke and diamond actions. It does not identify either the
un-base-changed module reductions or the two relation ideals. The former identification is
available only if both nilpotent kernels annihilate the corresponding reductions.

**Proposition 1.1E (the exact output of balanced patching).** Impose the sharp relation
count, depth, finite-over-diamond, and clean-control hypotheses of Books 144--145 on both
systems in (1.8v). Then:

1. the common-quotient diagram (1.8w)--(1.8x), the finite-shadow maps, and the exact augmentations can be
   retained simultaneously;
2. each $M_\infty^\bullet$ is Cohen--Macaulay on its support and, under the sharp dimension
   equality, maximal Cohen--Macaulay over $R_\infty^\bullet$; that support is a union of
   irreducible components under Book 145's equidimensionality and catenarity hypotheses;
3. the actual residual automorphic occurrence makes $M_\infty^{\rm av}$ nonzero and hence
   puts at least one avoidance component in its support; but
4. these conclusions imply neither $({\rm PGC}_P)$ nor avoidance full support.

**Proof.** The first two clauses are precisely finite-shadow diagonalization and the sharp
dimension theorem of Books 144--145. The third is Nakayama applied to the nonzero residual
vector exhibited after Proposition 1.1D. For the last clause, the following two models
satisfy strictly stronger commutative-algebra properties than those conclusions and still
fail the respective assertions. $\square$

First let

$$
C=\mathcal O[[x,y]]/(xy-\varpi),\qquad s=x+y,
\qquad S=\mathcal O[[s]],\qquad M=C.
\tag{1.8y}
$$

The ring $C$ is a two-dimensional regular local domain: its maximal ideal is generated by
$x,y$, since $\varpi=xy$. Moreover

$$
C\simeq S[[y]]/(y^2-sy+\varpi)
\tag{1.8z}
$$

is finite free of rank two over $S$. Thus $M$ is faithful, $S$-free, maximal
Cohen--Macaulay, and has full support. Nevertheless

$$
C/\varpi\simeq k[[x,y]]/(xy)
\tag{1.8aa}
$$

has two minimal primes. One horizontal component of a regular patched ring has split into
two vertical branches. In the presentation $f=xy-\varpi$, the relative differential

$$
df=y\,dx+x\,dy
\tag{1.8ab}
$$

vanishes at their intersection. This is the relevant _vertical cross-cotangent_
degeneracy. Book 175's equal-variable rigidity controls a characteristic-zero branch and
can even prove that the total ring is regular; it does not rule out (1.8y).

For an excellent, $\mathcal O$-flat, equidimensional ring $C$, the component assertion needed
here can therefore be written without patching terminology as

$$
\text{unique horizontal specialization for }C:\quad
\begin{cases}
(C/\mathfrak p)/\varpi\text{ has a unique minimal prime }
   \mathfrak q_{\mathfrak p}/\mathfrak p
   \text{ for every }\mathfrak p\in\operatorname {Min}(C),\\
\mathfrak q_{\mathfrak p}\text{ is minimal over }(\varpi),
   \text{ and the }\mathfrak q_{\mathfrak p}\text{ are distinct as }\mathfrak p\text{ varies.}
\end{cases}
\tag{1.8ac}
$$

Indeed, every prime minimal over $(\varpi)$ contains a minimal prime $\mathfrak p$ of $C$
and is then minimal over $\mathfrak p+(\varpi)$; uniqueness and distinctness in (1.8ac)
therefore give both surjectivity and injectivity of the specialization map. Applied to
$C=R_\infty^{\rm des}$, this is exactly the vertical part of
$({\rm PGC}_P)$ after the local labels of Theorem 1.1C are fixed. A convenient stronger
sufficient theorem would say that the Cartier divisor $(\varpi)$ is irreducible on the
normalization of every horizontal component and that the contractions of these divisors
are distinct. Neither a regular-sequence presentation, normality of the total ring, the
sharp dimension count, nor branchwise characteristic-zero cotangent control proves this;
(1.8y) is already regular and normal.

The support assertion is independent. Set

$$
C'=\mathcal O[[x,y]]/(xy),\qquad S'=\mathcal O[[y]],
\qquad M'=C'/(x)\simeq S'.
\tag{1.8ad}
$$

Here $C'$ is an equidimensional Cohen--Macaulay hypersurface obtained from an integral local
source by one global relation. The module $M'$ is nonzero, free over the diamond source
$S'$, maximal Cohen--Macaulay as a $C'$-module, and its faithful acting image is exactly $S'$.
It even has the exact marked recovery

$$
M'/yM'\simeq\mathcal O.
\tag{1.8ae}
$$

But $\operatorname {Supp}_{C'}M'=V(x)$ and so it misses the component $V(y)$. Thus residual
occurrence, balanced freeness, an integral local source, sharp dimension, Cohen--Macaulayness,
and exact augmentation still do not prove avoidance full support. Once Book 145 has proved
that the support is a union of components, full avoidance occurrence means

$$
\text{full avoidance occurrence}:\qquad
(M_\infty^{\rm av})_{\mathfrak p}\ne0
\quad\text{for every }
\mathfrak p\in\operatorname {Min}(R_\infty^{\rm av}).
\tag{1.8af}
$$

It is equivalent to (1.8t) under those hypotheses. Calling the module _nearly faithful_
does not prove (1.8af): in the equidimensional reduced setting, nearly faithful already
means that every minimal component occurs and is the desired conclusion. One must instead
prove an automorphic component theorem, or prove independently that the actual avoidance
patched ring is irreducible.

These examples prove a negative statement about the **quotient-first** architecture, not
about Ihara avoidance. Books 143--145 also retain the action of the larger local
presentation source $P_\infty^\bullet$. On that source the balanced dimension equality is
strong enough to prove the avoidance action faithful before any quotient-component question
is asked. The two countermodels do not contradict this: $C'$ in (1.8ad) is reducible, while
the avoidance source is a domain; and (1.8y) fails the unique-horizontal-specialization
property required of the desired source. We now give that argument.

### 1.5D The source-patching CIAV theorem and prepared applications

The preceding counterexamples concern patching after the local sources have been divided by
global relation ideals. The paired source theorems of Books 143--145 and 152 make that
detour unnecessary. They retain the two local presentation sources, the common residual
module, and the module augmentation in one construction. The support theorem is then applied
before finite-level specialization. This order is decisive: a domain argument proves
faithfulness on the avoidance source, and the common special fibre transports that support to
every horizontal desired component.

For a finite active set $P$, let $R_{\rm loc}^{\rm des,raw}$ be the literal completed product
of the desired local rings and put

$$
R_{\rm loc}^{\rm des}
=(R_{\rm loc}^{\rm des,raw})^{\rm red},
\qquad
R_{\rm loc}^{\rm av}
=\widehat\bigotimes_{v\in P}A_{{\rm av},v}
 \widehat\otimes R_{\rm loc}^{\rm fixed}.
\tag{1.8ag}
$$

Here $R_{\rm loc}^{\rm fixed}$ contains the common determinant, coefficient-prime, dyadic,
unramified, and frame factors. Each of its factors is restricted to one named formally
smooth or geometrically integral Cohen--Macaulay component. The active desired and avoidance
factors are those of Theorem 1.1C.

**Lemma 1.1F (geometry of the finite scalar pair).** The three rings in (1.8ag) have the
following properties.

1. $R_{\rm loc}^{\rm av}$ is an $\mathcal O$-flat Cohen--Macaulay domain.
2. $R_{\rm loc}^{\rm des}$ is $\mathcal O$-flat, reduced, equidimensional, and
   Cohen--Macaulay, of the same dimension as $R_{\rm loc}^{\rm av}$, and specialization
   induces a bijection

   $$
   \operatorname {Min}(R_{\rm loc}^{\rm des})
   \xrightarrow{\sim}
   \operatorname {Min}(R_{\rm loc}^{\rm des}/\varpi).
   \tag{1.8ah}
   $$

3. There is a common complete local residual quotient $C_{\rm loc}$ and surjections

   $$
   R_{\rm loc}^{\rm av}/\varpi\twoheadrightarrow C_{\rm loc},
   \qquad
   R_{\rm loc}^{\rm des}/\varpi\twoheadrightarrow C_{\rm loc}
   \tag{1.8ah0}
   $$

   with nilpotent kernels. The nilradical $\mathcal N$ of
   $R_{\rm loc}^{\rm des,raw}$ satisfies $\mathcal N[1/\varpi]=0$ and hence
   $\varpi^a\mathcal N=0$ for some $a$.

**Proof.** Theorem 1.1C proves each assertion for one active factor, including the literal
common special fibre and the labelled specialization of the unramified and special
components. Completed tensor product with the selected unchanged factors preserves
flatness, dimension, Cohen--Macaulayness, and the domain or equidimensional reduced property.
For several active factors, the product labels give the $2^{|P|}$ desired horizontal
components and the corresponding special-fibre components, so the specialization map is
bijective. Passing from the literal common fibre to either horizontal reduction kills only a
nilpotent ideal and gives (1.8ah0). Finally, the raw desired generic fibre is already the
reduced union of its horizontal components. Noetherianity then makes its nilradical
coefficient-power torsion, as in Book 145, Lemma 17.2. $\square$

We now place the finite-level arithmetic data into the precise paired framework. Let $T$ be
the nonempty set of old framed places, with $m=|T|$, and put $d_F=[F:\mathbf Q]$. The strict
relative dual Selmer group is

# $$V_T^0

H^1_{(\mathcal L_T^0)^\perp}
\left(F,\operatorname {ad}^0\bar\rho(1)\right),
\qquad
q_T^0=\dim_kV_T^0.
\tag{1.8ai0}
$$

Strictness is imposed on the primal problem at $T$; the dual condition at $T$ is therefore
relaxed. This is the obstruction group that must be killed when the complete old local rings
are retained in the presentation source.

**Proposition 1.1G (the synchronized sharp source patch).** Suppose the desired and
avoidance problems have the same absolutely irreducible residual representation and
determinant, and that at every conditioned place their residual local functors are identified
by a square commuting with the two embeddings into the unrestricted residual deformation
functor, as in Book 143, (15.0). Suppose their local products satisfy Lemma 1.1F. Assume
the split-image hypotheses of Book 143, Theorem 15.2, together with the nonempty full detector
fibres for every nonzero surviving subspace of $V_T^0$ and the separately nonempty padding
fibre required there. Assume also that $T$ contains every old finite place with nonzero local
defect, that all remaining finite defects vanish, that
$H^0(F,\operatorname {ad}^0\bar\rho(1))=0$, and that oddness contributes $-1$ at every real
place. Choose

$$
h\ge q_T^0,
\qquad
q_0=h+m-1-d_F\ge0.
\tag{1.8ai1}
$$

Suppose moreover that at every $Q_N$ the two definite coefficient systems satisfy every
hypothesis of Book 152, Theorem 20.5. Thus they live on the same clean class groupoid; the
one projective arithmetic stabilizer group attached to each object before choosing
coefficients has order prime to $\ell$; their active lattices and central characters have a
marked common reduction; the Taylor--Wiles levels are disjoint from $P$; the primary and
companion systems are perfectly paired with the declared adjoints; and the common residual
Hecke localization satisfies $\bar P_{Q_N,0}\ne0$. Finally assume one of the two uniformity
routes in Book 152, Proposition 20.6: either the conditional minimal-control maps identify all
oriented modules with fixed minimal modules, or the positive ranks $r_N$ are bounded and the
uniform presentation and finite-shadow hypotheses of Proposition 20.6(3) hold. Retain the
source and local--global actions, the intermediate patched deformation rings, and their
represented-ring augmentation maps in the finite-level data, and assume those marked maps
recover the represented finite-level rings exactly after specialization.

Then there are single ordered sets $Q_N$ of cardinality $h$ and synchronized patched modules

$$
M_\infty^{\rm des},
\qquad
M_\infty^{\rm av}
\tag{1.8ai2}
$$

with the following properties. Put

$$
\begin{aligned}
P_\infty^{\rm des,raw}
 &=R_{\rm loc}^{\rm des,raw}[[y_1,\ldots,y_{q_0}]],&
P_\infty^{\rm des}
 &=R_{\rm loc}^{\rm des}[[y_1,\ldots,y_{q_0}]],\\
P_\infty^{\rm av}
 &=R_{\rm loc}^{\rm av}[[y_1,\ldots,y_{q_0}]],&
S_\infty^{\rm fr}
 &=\mathcal O[[z_1,\ldots,z_h,w_1,\ldots,w_{4m-1}]].
\end{aligned}
\tag{1.8ai}
$$

After passage to the cofinal constant-rank subsequence supplied by Book 152, Proposition
20.6, the modules in (1.8ai2) are finite free of the same positive rank over
$S_\infty^{\rm fr}$, and their source actions factor through finite images

$$
\begin{aligned}
&S_\infty^{\rm fr}\hookrightarrow A_\infty^{\rm av}
 \subseteq\operatorname {End}_{S_\infty^{\rm fr}}(M_\infty^{\rm av}),
&&P_\infty^{\rm av}\twoheadrightarrow R_\infty^{\rm av}
 \twoheadrightarrow A_\infty^{\rm av},\\
&S_\infty^{\rm fr}\hookrightarrow A_\infty^{\rm des}
 \subseteq\operatorname {End}_{S_\infty^{\rm fr}}(M_\infty^{\rm des}),
&&P_\infty^{\rm des,raw}\twoheadrightarrow R_\infty^{\rm des,raw}
 \twoheadrightarrow A_\infty^{\rm des}.
\end{aligned}
\tag{1.8aj}
$$

Writing $C_\infty=C_{\rm loc}[[\bar y_1,\ldots,\bar y_{q_0}]]$, there is a specified
isomorphism only after base change to this common nilpotent quotient:

$$
\bigl(M_\infty^{\rm des}/\varpi\bigr)
 \otimes_{P_\infty^{\rm des}/\varpi}C_\infty
\xrightarrow{\sim}
\bigl(M_\infty^{\rm av}/\varpi\bigr)
 \otimes_{P_\infty^{\rm av}/\varpi}C_\infty.
\tag{1.8aj1}
$$

This isomorphism is compatible with diamonds, frames, Hecke operators, local intertwiners,
pairings, and adjoints. No un-base-changed residual module isomorphism is asserted unless the
two nilpotent kernels separately annihilate the module reductions.
The raw desired nilradical acts trivially. If $\mathfrak a$ is the ideal generated by the
diamond variables and by precisely those added frame variables specialized at base level,
then the marked module augmentations are exact:

$$
M_\infty^\bullet/\mathfrak aM_\infty^\bullet
\xrightarrow{\sim}M_0^\bullet.
\tag{1.8aj0}
$$

The intermediate represented deformation rings specialize through the marked ring maps to the
corresponding finite-level problems; in particular the paired diagonal path retains

$$
R_\infty^{\rm des,raw}/\mathfrak aR_\infty^{\rm des,raw}
\xrightarrow{\sim}R_0^{\rm des},
\qquad
R_\infty^{\rm av}/\mathfrak aR_\infty^{\rm av}
\xrightarrow{\sim}R_0^{\rm av}.
\tag{1.8aj2}
$$

No equality between
$A_\infty^\bullet/\mathfrak aA_\infty^\bullet$ and the action on
$M_0^\bullet$ is asserted.

Finally,

$$
\dim P_\infty^{\rm des}
=\dim P_\infty^{\rm av}
=\dim S_\infty^{\rm fr}
=h+4m.
\tag{1.8ak}
$$

**Proof strategy.** Prime selection is performed once on the common strict relative Selmer
group. The actual definite modules are then constructed at those same levels before taking
any limit. Their marked common reduction forces the two positive ranks to agree. A single
paired diagonal path retains that identification, all source actions, and module
augmentation. Only after these steps do the dimension count and source-support theorem
enter.

**Proof.** The commuting residual squares make the two tangent images inside unrestricted
local cohomology literally equal. Book 143, Proposition 15.1 therefore identifies the two
strict-at-$T$ residual Selmer structures and all their localization functionals. The
nonempty detector fibres in Book 143, Theorem 15.2 choose the first $q_T^0$ members of one
ordered $Q_N$ and kill the common obstruction space; its separate padding fibre supplies the
remaining members without reviving either dual group. Because $T$ is nonempty, contains the
full old finite defect, the remaining finite defects vanish, the global $H^0$ term is zero,
and each real place contributes $-1$, the complete formula of Book 143, (15.8) reduces to

$$
g_{T,Q_N}
=h+m-1-d_F=q_0.
\tag{1.8ak0}
$$

The old local factors already contain their full framed tangent directions. In particular,
the six residual tangent directions of a scalar active place are not counted a second time in
$q_0$.

Book 152, Theorem 20.5 now applies separately to each fixed $Q_N$. It produces modules free
of the same positive fixed-$Q_N$ rank
$r_N=\dim_k\bar P_{Q_N,0}$ over the common diamond algebra, their intrinsic common residual
module, and the exact orbit-sum coinvariants. The projective arithmetic stabilizer is defined
from the class groupoid before either coefficient system is chosen; its prime-to-$\ell$ order
makes invariant formation commute with reduction on both sides. Cleanliness makes each
diamond fibre a torsor, and $\bar P_{Q_N,0}\ne0$ makes $r_N$ positive.

The fixed-$Q_N$ theorem does not compare $r_N$ as $N$ varies. Under the uniformity
hypothesis in the proposition, Book 152, Proposition 20.6 either identifies every rank with
the rank of one fixed minimal module or passes to a cofinal subsequence on which the bounded
positive ranks are a single integer $r$. In the latter case it simultaneously retains all
finite marked shadows. This is the uniform-rank input required by Book 144.

Include the ordered sources, the common-quotient base-changed residual module, all frame coordinates, pairings,
operators, the module augmentations, and the assumed represented-ring recovery maps in one
paired shadow. Book 144, Theorem 18.2
produces one cofinal sequence and one diagonal path, giving (1.8ai2), the base-changed
comparison (1.8aj1), (1.8aj0), and (1.8aj2). Book 144, Lemma 18.1 ensures that every named
mark is retained along that path. The theorem also scalar-extends by all $4m-1$ partial-frame
coordinates. These are four
matrix directions at each old framed place modulo one global scalar, whereas the $h$
variables $z_i$ are the distinct diamond directions.

Every fixed-determinant framed local factor away from $\ell$ has relative dimension three,
and a selected factor at $v\mid\ell$ has relative dimension
$[F_v:\mathbf Q_\ell]+3$. Consequently

$$
\dim R_{\rm loc}^{\rm des}
=\dim R_{\rm loc}^{\rm av}
=1+3m+d_F.
$$

Adding $q_0$ source variables gives

$$
(1+3m+d_F)+(h+m-1-d_F)
=h+4m
=1+h+(4m-1),
$$

which proves (1.8ak). The source action images are finite over
$S_\infty^{\rm fr}$ because they lie in endomorphism rings of finite free modules. Finally
$\mathcal N$ is killed by a power of $\varpi$ by Lemma 1.1F, while
$M_\infty^{\rm des}$ is $\mathcal O$-torsion-free. Hence $\mathcal N$ acts trivially and the
desired source action factors through $P_\infty^{\rm des}$. $\square$

The equality of dimensions is now attached to the correct ambient rings. It says nothing
about an arbitrary global quotient and it does not identify an augmented acting image. Its
purpose is to put the paired sources and modules exactly in the hypotheses of the following
support theorem.

**Theorem 1.1H (finite-set componentwise Ihara avoidance, $({\rm CIAV}_P)$).** Under
Proposition 1.1G, the avoidance and desired source actions satisfy

$$
A_\infty^{\rm av}=P_\infty^{\rm av},
\qquad
\operatorname {Supp}_{P_\infty^{\rm av}}M_\infty^{\rm av}
=\operatorname {Spec}P_\infty^{\rm av},
\tag{1.8al}
$$

and

$$
A_\infty^{\rm des}=P_\infty^{\rm des},
\qquad
\operatorname {Supp}_{P_\infty^{\rm des}}M_\infty^{\rm des}
=\operatorname {Spec}P_\infty^{\rm des}.
\tag{1.8am}
$$

The annihilator of $M_\infty^{\rm des}$ in
$P_\infty^{\rm des,raw}$ is exactly its coefficient-power nilradical. If the source actions
factor through intermediate patched deformation rings, then the avoidance intermediate ring
is the avoidance source and the reduction of the desired intermediate ring is
$P_\infty^{\rm des}$. More precisely,

$$
\operatorname {Ann}_{R_\infty^{\rm des,raw}}(M_\infty^{\rm des})
=\sqrt0_{R_\infty^{\rm des,raw}}.
\tag{1.8am1}
$$

Let $R^{\rm des}$ and $M^{\rm des}$ be the represented finite-level ring and module recovered
by the marked ring augmentation and (1.8aj0), and let

$$
R^{\rm des}\longrightarrow\mathbb T^{\rm des}
\subseteq\operatorname {End}_{\mathcal O}(M^{\rm des})
\tag{1.8an}
$$

be the actual finite-level action. Then the kernel of (1.8an) is nilpotent. Every
characteristic-zero point of $R^{\rm des}$ factors through $\mathbb T^{\rm des}$ and hence is
automorphic with the local conditions represented by the desired problem. Since
$\mathbb T^{\rm des}$ is finite over $\mathcal O$, the whole noetherian ring
$R^{\rm des}$ is finite over $\mathcal O$.

No mixed old--new cube, type-Ihara theorem, node comparison, vertical-cotangent condition, or
acting-image augmentation-saturation hypothesis occurs in this statement.

**Proof strategy.** On the avoidance side, maximal depth over an equal-dimensional domain
kills the source annihilator. Common residual support then passes to the desired special
fibre. The unique-horizontal specialization of Lemma 1.1F lifts it to every desired
component, and reducedness kills the desired annihilator. At finite level one repeats only
the support argument on module coinvariants; this produces a nilpotent kernel without
identifying the quotient of the patched acting image.

**Proof.** We specialize Book 145, Theorem 17.3. In its notation take

$$
S=S_\infty^{\rm fr},
\quad
P^{\rm av}=P_\infty^{\rm av},
\quad
P^{\rm des,raw}=P_\infty^{\rm des,raw},
\quad
P^{\rm des}=P_\infty^{\rm des}.
$$

Lemma 1.1F supplies the flat Cohen--Macaulay avoidance domain, the flat reduced
equidimensional Cohen--Macaulay desired source, the bijection of horizontal and special
minimal primes, and the coefficient-power raw nilradical. Proposition 1.1G supplies the
common nilpotent quotient and the base-changed residual module isomorphism (1.8aj1), the
positive-rank $S$-free patched modules, and the finite source action images.

For completeness, the avoidance faithfulness begins with

# $$\operatorname {depth}_{P_\infty^{\rm av}}M_\infty^{\rm av}

\operatorname {depth}_{S_\infty^{\rm fr}}M_\infty^{\rm av}
=h+4m.
\tag{1.8ao}
$$

A nonzero annihilator in the domain would make the support have dimension at most
$h+4m-1$, contradicting depth at most dimension of support. This proves (1.8al).
Reduction modulo $\varpi$ preserves full support by Nakayama. Base change to $C_\infty$
cannot kill a nonzero localization because the quotient kernels are nilpotent. The isomorphism
(1.8aj1) then transfers full support to the desired base change, and the second nilpotent
quotient carries it back to the desired residual source. The desired module
is maximal Cohen--Macaulay because its depth is again $h+4m$. Book 145, Lemma 17.1 lifts full
special-fibre support through the unique-horizontal bijection, and reducedness makes the
desired action faithful. Book 145, Lemma 17.2 makes the raw nilradical act trivially.
These are exactly the remaining conclusions of Theorem 17.3 and prove (1.8am), including the
intermediate-ring identity (1.8am1).

It remains to explain why finite-level recovery needs no acting-image saturation. The marked
ring and module isomorphisms give

$$
R_\infty^{\rm des,raw}/\mathfrak aR_\infty^{\rm des,raw}
\simeq R^{\rm des},
\qquad
M_\infty^{\rm des}/\mathfrak aM_\infty^{\rm des}
\simeq M^{\rm des}.
\tag{1.8ap}
$$

Equation (1.8am1) gives full topological support over the intermediate ring, and this support
descends to full support of $M^{\rm des}$ over $R^{\rm des}$ by Nakayama. Book 145,
Corollary 17.4 therefore identifies the kernel of (1.8an) with the
annihilator of a full-support module and proves that it is nilpotent. At the recovered
definite level this is also precisely Book 152, Proposition 20.7: source support implies a
nilpotent kernel in the finite action. A homomorphism to a characteristic-zero field kills
nilpotents, so it factors through the actual automorphic action. Finally, Book 152,
Theorem 20.5 makes $M^{\rm des}$ finite free over $\mathcal O$; its acting image is therefore
$\mathcal O$-finite. The finiteness clause of Book 145, Corollary 17.4, equivalently Lemma
1.1A, makes $R^{\rm des}$ finite. $\square$

**Corollary 1.1I (optional exact acting-image augmentation).** In Theorem 1.1H, suppose in
addition that

# $$A_\infty^{\rm des}\cap\mathfrak a\operatorname {End}_{S_\infty^{\rm fr}}(M_\infty^{\rm des})

\mathfrak aA_\infty^{\rm des}.
\tag{1.8aq}
$$

Then Book 145, Corollary 17.5 gives

$$
A_\infty^{\rm des}/\mathfrak aA_\infty^{\rm des}
\xrightarrow{\sim}\mathbb T^{\rm des}.
\tag{1.8ar}
$$

The analogous statement holds on the avoidance side under its analogous saturation
condition. Neither (1.8aq) nor (1.8ar) is used in Theorem 1.1H, in pointwise automorphy, or
in finite recovery.

The prepared applications differ only in how they obtain the field and the actual nonzero
residual packet. Once such a packet is supplied, the antecedents have the following exact
sources.

| prepared antecedent                                                                                                                                                           | theorem which supplies it                                                                                                                                                                                                                                                            |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| coefficient places split, active residual actions trivial, $q_v\equiv1\pmod\ell$, selected inertial actions unipotent, and protected completions retained                     | Book 109, Corollary 14.5 in auxiliary mode and Corollary 14.6 in target mode, with selectedness required at every component over the entire controlled set $P\cup Z$, including split dyadic and coefficient-prime places                                                            |
| the paired scalar desired and avoidance rings, common nilpotent residual quotient, avoidance domain, and unique horizontal specialization on the desired source               | Theorem 1.1C and Lemma 1.1F, after the prepared field has put every active place in the trivial-residual, $q_v\equiv1\pmod\ell$ chart                                                                                                                                                |
| one ordered Taylor--Wiles set killing the common strict-at-$T$ relative dual Selmer group and the complete variable count $q_0$                                               | Book 143, Proposition 15.1 and Theorem 15.2, after the residual local functors are identically embedded in the unrestricted functor, the detector and padding fibres are nonempty, $T$ contains the full old finite defect, and the remaining terms in (15.8) have the stated values |
| nonzero common residual localization                                                                                                                                          | the actual reference or upper packet supplies a primitive definite eigenvector; Book 152, Proposition 20.1 identifies its marked reduction with the intrinsic common residual module                                                                                                 |
| two positive-rank definite systems at each fixed $Q_N$, with intrinsic common residual module, exact orbit-sum coinvariants, pairings, adjoints, and finite recovered actions | Book 152, Theorem 20.5, once the preceding nonvanishing and coefficient-independent prime-to-$\ell$ stabilizer condition hold                                                                                                                                                        |
| one fixed positive rank on a cofinal family, together with retention of all marked finite shadows                                                                             | Book 152, Proposition 20.6, from either uniform minimal control or the stated bounded-rank and finite-presentation hypotheses                                                                                                                                                        |
| one paired diagonal path, common-quotient base-changed residual patched module, full frame coordinates, and exact module coinvariants                                         | Book 144, Lemma 18.1 and Theorem 18.2                                                                                                                                                                                                                                                |
| exact recovery of the intermediate represented ring after diamond and frame specialization                                                                                    | the represented-ring augmentation is explicit application data in Proposition 1.1G; Book 144, Lemma 18.1 retains the marked map, and Book 145, Corollary 17.4 consumes the resulting isomorphism                                                                                     |
| equality of the presentation-source and frame-source dimensions                                                                                                               | Book 69's strict-relative tangent formula combined with Book 143's full defect formula, specialized in Proposition 1.1G                                                                                                                                                              |
| faithful avoidance source, full desired support, raw nilradical control, and reduction of intermediate deformation rings                                                      | Book 145, Theorem 17.3                                                                                                                                                                                                                                                               |
| nilpotent recovered finite-level kernel, pointwise factorization, and whole-ring finiteness from recovery of the intermediate desired ring and its module                     | Book 145, Corollary 17.4; Book 152, Proposition 20.7 gives the corresponding source-support implication on a recovered module                                                                                                                                                        |
| exact augmented acting-image equality, when desired                                                                                                                           | Book 145, Corollary 17.5, under the additional saturation (1.8aq)                                                                                                                                                                                                                    |
| descent of an upper packet attached to a representation already defined over the bottom field                                                                                 | Book 109, Proposition 14.4, under its selected-safe local and cyclic hypotheses                                                                                                                                                                                                      |

This table is intentionally packet-dependent. The field construction does not create an
automorphic reference packet, and a packet does not by itself prove clean stabilizers,
compatible local lattices, or represented local--global actions. The next two theorems state
the two ways those data enter.

**Theorem 1.1J (prepared auxiliary application).** Let
$F=F_0\subset\cdots\subset F_s=L$ be an auxiliary-mode tower supplied by Book 109,
Corollary 14.5 for a residual representation $\bar\rho$, a finite active set $P$, and the
declared protected set $Z$. Let $\rho$ be a characteristic-zero lift over $F$. Assume:

1. restriction to $G_L$ preserves absolute residual irreducibility and the required joint
   residual--cyclotomic image; $\rho|_{G_L}$ has the declared determinant and regular
   coefficient-prime condition, and has unipotent inertia at every member of $P$; moreover
   the bottom local parameters of $\rho$ are selected-safe on the entire controlled set
   $P\cup Z$, including every protected split dyadic and coefficient-prime component;
2. there is an actual parallel-weight-two cuspidal packet $\pi_0$ over $L$, with attached
   representation $\rho_0$, such that $\bar\rho_0=\bar\rho|_{G_L}$, the determinants and
   coefficient-prime conditions agree, and at every $v\in P$ the packet realizes the
   avoidance type with tame eigencharacters $\zeta_\ell,\zeta_\ell^{-1}$;
3. $\pi_0$ has a transfer to a totally definite quaternion algebra at clean common levels;
   the projective arithmetic stabilizer of each class-groupoid object, defined independently
   of either coefficient system, has order prime to $\ell$; the levels carry the exact desired
   and avoidance lattices of (1.8p), compatible central characters, primary--companion
   pairings, named Hecke operators, and local--global source actions; at every selected
   $Q_N$, an old or regularly refined primitive vector gives
   $\bar P_{Q_N,0}\ne0$, and the ranks satisfy one of the uniformity alternatives of Book
   152, Proposition 20.6; and
4. every unchanged dyadic, coefficient-prime, determinant, and ramification factor is one
   common named formally smooth or geometrically integral selected component; the residual
   desired and avoidance functors are identified compatibly with their embeddings into the
   unrestricted functor; the full strict-relative defect, detector, padding, and finite-shadow
   hypotheses of Proposition 1.1G hold; and the intermediate represented deformation rings
   and modules recover under the marked augmentation.

Then Books 143, 144, 145, and 152 construct every antecedent of Theorem 1.1H over $L$.
Consequently $({\rm CIAV}_P)$ holds over $L$, every characteristic-zero desired point is
automorphic over $L$, and in particular $\rho|_{G_L}$ is automorphic when it is a point of
the desired problem.

If the preparation and the resulting packet satisfy the selected-safe cyclic hypotheses of
Book 109, Proposition 14.4, then the automorphic packet attached to $\rho|_{G_L}$ descends
through the displayed tower to a packet attached to $\rho$ over $F$.

**Proof.** Corollary 14.5 gives the scalar local situation needed in Theorem 1.1C:
the residual action is trivial and the residue cardinality is one modulo $\ell$ at each
active place; it also keeps coefficient places split and realizes the protected completions.
Clauses 1 and 4 place every repeated split component and every nonsplit controlled component
in the selected trace-comparable range of Book 109, Proposition 14.4.
The packet $\pi_0$ is an actual avoidance point, not a numerical proxy. At each $Q_N$,
transfer its old or regularly refined packet to the declared definite algebra and choose a
nonzero eigenvector. After finite coefficient extension, scale that vector so that it is
primitive in the integral lattice. Its reduction is nonzero in the residual Hecke
localization. The marked lattice isomorphisms (1.8q) place the same residual vector in the
intrinsic common module, proving $\bar P_{Q_N,0}\ne0$. Book 152, Proposition 20.6 then
supplies the cofinal constant-rank family from the uniformity alternative in clause 3.

Theorem 1.1C and Lemma 1.1F give the paired local sources. Book 143, Theorem 15.2 chooses the
common prime sets. Book 152, Theorem 20.5 constructs the paired positive-rank finite-level
modules and their module coinvariants. Book 144, Lemma 18.1 and Theorem 18.2 patch their
common-quotient base changes along one marked path. Proposition 1.1G records the resulting
dimensions and actions, and Book 145,
Theorem 17.3 and Corollary 17.4 give Theorem 1.1H. Thus the desired point defined by
$\rho|_{G_L}$ factors through the actual automorphic action.

For descent, the arithmetic representation $\rho$ is already defined over $F$. Book 109,
Proposition 14.4 verifies the local extension fibres, determinant and central character,
real-place selector, irreducibility, attachment, and quotient-character corrections at every
cyclic step. Under its selected-safe hypothesis it therefore descends the upper packet and
attaches the result to $\rho$. $\square$

**Theorem 1.1K (prepared target application).** Let
$F=F_0\subset\cdots\subset F_s=L$ be a target-mode tower supplied by Book 109,
Corollary 14.6 for a controlled set $P\cup Z$. Thus every place above $2\ell$ and every additional protected split place
splits completely in $L$, the joint residual--cyclotomic image is preserved, and at the finite
active set $P$ one has

$$
\bar\rho|_{G_{L_v}}=1,
\qquad
q_v\equiv1\pmod\ell.
\tag{1.8as}
$$

Assume there is an actual parallel-weight-two cuspidal upper packet $\Pi^{\rm up}$ over $L$
which is a point of the broad tame-unipotent problem
$\mathcal D_L^{\rm uni}(P)$ of Section 1.5A. Require that:

1. at every $v\in P$, $\Pi_v^{\rm up}$ is special with the declared determinant and has a
   primitive vector in the desired lattice $L_v^{\rm des}$;
2. at places above $2$, it has the protected named dyadic signed-special factor, and at
   places above $\ell$, its stable lattice realizes the protected selected
   weight-$\{0,1\}$ finite-flat factor;
3. every component above the entire controlled set $P\cup Z$, including every split dyadic
   and coefficient-prime component, is selected and trace-comparable; if the upper packet is
   obtained from a packet over $F$, that bottom packet is selected-safe on $P\cup Z$ in the
   precise sense of Book 109, Proposition 14.4; away from the controlling set it is
   unramified, its attached residual representation is $\bar\rho|_{G_L}$, and every generic
   factor lies in the integral local--global compatibility range; and
4. its transfer to the totally definite quaternion algebra is taken at clean common levels;
   the projective arithmetic stabilizer of each class-groupoid object is independent of the
   coefficient system and has order prime to $\ell$; the levels carry exact desired and
   avoidance coefficient lattices, compatible central characters, primary--companion
   pairings, and the represented source actions; at every $Q_N$ a primitive old or regular
   refinement proves $\bar P_{Q_N,0}\ne0$; one of the uniform-rank alternatives in Book 152,
   Proposition 20.6 holds; the residual local functors are identically embedded in the
   unrestricted functor; the complete strict-relative defect, detector, padding, and
   finite-shadow hypotheses of Proposition 1.1G hold; and the intermediate represented rings
   and modules recover under augmentation.

Then the common residual definite module is nonzero, the paired systems of
Proposition 1.1G exist, and Theorem 1.1H applies to the broad desired problem. In particular,

$$
R_L^{\rm uni}(P)\longrightarrow\mathbb T_L^{\rm uni}(P)
\tag{1.8at}
$$

has nilpotent kernel, $R_L^{\rm uni}(P)$ is finite over $\mathcal O$, and every
characteristic-zero point of the broad problem is automorphic. The quotient

$$
R_L^{\rm uni}(P)\twoheadrightarrow R_L^{\rm SP}
\tag{1.8au}
$$

therefore has finite special fibre, and every characteristic-zero point of
$R_L^{\rm SP}$ is automorphic.

**Proof strategy.** The upper packet is used once, to create the common residual
localization. It is not a minimal point and it is not used to prove finiteness of a ring
already known to contain such a point. After this seed is fixed, source patching proves a
whole-ring statement; only then is the minimal quotient considered.

**Proof.** Corollary 14.6 makes every completion above $2\ell$ equal to the original
protected completion. Hence the named dyadic signed-special quotient and the selected
finite-flat coefficient-prime quotient are literally unchanged, including their frame and
determinant factors. Clause 3 ensures that these repeated components, and every other
component over $P\cup Z$, lie in the selected trace-comparable range required by Book 109,
Proposition 14.4. Its disjointness clause preserves both residual irreducibility
conditions.
Equation (1.8as) puts every active place in the scalar chart of Theorem 1.1C.

At each $Q_N$, transfer the old or regularly refined form of $\Pi^{\rm up}$ to the totally
definite quaternion algebra and choose a nonzero simultaneous eigenvector. Scale it inside
its stable integral eigenline until it is primitive. Its reduction is nonzero, and primary
localization at its residual Hecke ideal remains nonzero. The local reductions (1.8q), the
coefficient-independent prime-to-$\ell$ stabilizer condition, and Book 152, Proposition 20.1
identify this reduction with the intrinsic common residual module. Thus
$\bar P_{Q_N,0}\ne0$ is proved from the actual upper packet rather than assumed. Book 152,
Proposition 20.6 then supplies the fixed-rank cofinal family from clause 4.

Theorem 1.1C supplies the local pair, Book 143, Theorem 15.2 supplies one set of
Taylor--Wiles primes for both sides, Book 152, Theorem 20.5 supplies the paired definite
modules, and Book 144, Lemma 18.1 and Theorem 18.2 supply the synchronized patch and its
common-quotient base-changed residual comparison. Theorem 1.1H, through
Book 145, Theorem 17.3 and Corollary 17.4, gives the nilpotent kernel in (1.8at) and makes the
whole broad ring finite. The map (1.8au) is obtained by imposing trivial inertia at every
member of $P$, so its special fibre is a quotient of a finite-dimensional $k$-algebra.
Finally, a characteristic-zero point of $R_L^{\rm SP}$ is also a point of
$R_L^{\rm uni}(P)$ after precomposition with (1.8au). This composite kills the nilpotent
kernel of (1.8at) and factors through $\mathbb T_L^{\rm uni}(P)$.

There is no circularity. The only characteristic-zero input is the independently supplied
upper packet on the broad problem. Finiteness is proved for the entire broad ring before any
point of the minimal quotient is selected, and automorphy of a later minimal point uses that
already established whole-ring factorization. $\square$

**Corollary 1.1L (finite special fibre and pointwise minimal automorphy).** Under
Theorem 1.1K,

$$
\dim_k(R_L^{\rm SP}/\varpi)<\infty.
$$

For every homomorphism $x:R_L^{\rm SP}\to E$ to a characteristic-zero field, the composite

$$
R_L^{\rm uni}(P)\twoheadrightarrow R_L^{\rm SP}\xrightarrow{x}E
$$

factors through the finite action $\mathbb T_L^{\rm uni}(P)$. Thus a later construction may
use the finite special fibre to produce or isolate a minimal point and then invoke the same
prepared target comparison to prove its automorphy. This is the precise pointwise
factorization, and no second patch is required.

Theorems 1.1J and 1.1K are criteria for future arithmetic use. They assert no auxiliary or
target packet beyond the actual packet appearing in their hypotheses. Their content is that,
once such a packet and its explicit local and definite data are supplied, all remaining
patching antecedents and all nilpotent finite-level recovery are already furnished by earlier
books.

### 1.6 Definite Ihara and the minimal-support boundary

The definite seed problem arising later has a feature absent from the curve-switch route.
Let $F$ be totally real, let $D/F$ be ramified at every real place and split at a finite place
$v\nmid\ell$, and write

$$
U=U^v\operatorname{GL}_2(\mathcal O_{F_v}),
\qquad
U_0(v)=U^vK_0(v).
\tag{1.9}
$$

Use scalar parallel-weight-two coefficients and a fixed central character, and let
$(\mathcal O,(\varpi),k)$ be a complete coefficient DVR. For
$A\in\{\mathcal O,k\}$, let $M_A(U)$ and $M_A(U_0(v))$ be the definite class-set modules of
Book 83. With Book 84's right-translation convention, the two endpoint maps give

$$
d_v:M_A(U)^{\oplus2}\longrightarrow M_A(U_0(v)).
\tag{1.10}
$$

Let $M_A(U)^{\rm nr}$ denote the span of the functions which factor through reduced norm.
For a residual maximal ideal $\mathfrak m$ of the common away Hecke algebra, say that
$\mathfrak m$ is **non-norm** if

$$
M_k(U)^{\rm nr}_{\mathfrak m}=0.
\tag{1.11}
$$

This is the exact definite substitute for the word non-Eisenstein in the following statement.
In the application it follows from the absolutely irreducible attached residual
representation: a reduced-norm character has reducible two-dimensional transfer, so it cannot
have the same good Hecke traces.

**Theorem 1.2 (definite class-set Ihara and saturation).** In the setting above, if
$\mathfrak m$ is non-norm, then

$$
(d_v\otimes_A k)_{\mathfrak m}:
M_k(U)_{\mathfrak m}^{\oplus2}\longrightarrow
M_k(U_0(v))_{\mathfrak m}
\tag{1.12}
$$

is injective. If the relevant primary class-set summands are finite free over
$\mathcal O$, then $(d_v)_{\mathfrak m}$ is injective with
$\mathcal O$-torsion-free cokernel. Thus its image is saturated. The same assertion may be
applied successively at a finite set of changed places, provided the non-norm and finite-free
hypotheses are retained at every intermediate level.

**Proof.** Put $H=\operatorname{SL}_1(D)$. The norm quadric of $D$ is isotropic over
$F_v$ because $D_v\simeq M_2(F_v)$. The integral norm-quadric approximation lemma proved in
Book 118, Section 6.2 is stated with an isotropic completion outside the finite places at
which approximation is prescribed; its proof does not require that completion to be
archimedean. Applied with the omitted completion $v$, it gives

$$
H(\mathbf A_{F,f})=H(F)H(F_v)U^{1,v},
\qquad U^{1,v}=U^v\cap H(\mathbf A_{F,f}^v).
\tag{1.13}
$$

Indeed, density modulo the open compact $U^{1,v}$ gives the displayed equality. This is
strong approximation **away from $v$**; total definiteness does not obstruct it because the
omitted split finite group $H(F_v)\simeq\operatorname{SL}_2(F_v)$ is noncompact.

Suppose $(f,g)$ lies in the kernel of (1.10) over $k$. If
$\omega_v=\operatorname{diag}(\varpi_v,1)$ in the chosen splitting, the endpoint relation is,
up to the fixed harmless central/right-translation normalization,

$$
f(x)=-g(x\omega_v).
\tag{1.14}
$$

The $U$-invariance of $f$ and $g$ consequently makes $f$ invariant under both $U$ and
$\omega_vU\omega_v^{-1}$. Their local norm-one subgroups generate
$\operatorname{SL}_2(F_v)$: the two adjacent maximal compact stabilizers generate the
type-preserving group of the Bruhat--Tits tree. Equation (1.13) and left $D^\times(F)$-
invariance now make $f$ invariant under $H(\mathbf A_{F,f})$. Hence $f$ factors through
reduced norm: placewise reduced norm has exact kernel
$H(\mathbf A_{F,f})\subset D^\times(\mathbf A_{F,f})$, while the rational and level factors
give exactly the corresponding idele-class quotient. Equation (1.14) gives the same
conclusion for $g$. The localized kernel is therefore
contained in $(M_k(U)^{\rm nr}_{\mathfrak m})^{\oplus2}$, which is zero by (1.11). This proves
(1.12).

For the integral assertion, take the finite-free primary summands of source and target.
Residual injectivity and Smith normal form over the DVR say that every nonzero invariant
factor of $d_v$ is a unit. Thus the integral map is injective and its cokernel has no
$\varpi$-torsion. A finite torsion module over a DVR has nonzero $\varpi$-torsion, so the
cokernel is torsion-free. Successive application proves the last sentence. $\square$

Theorem 1.2 removes a real hypothesis from the direct-definite route: unlike the curve
cohomology map of Book 139, the scalar definite degeneracy map needs no abelian-Ihara or
congruence-kernel assumption. It does **not**, however, prove level lowering. Its source is
the already existing lower-level module. It says that this source embeds primitively in the
oriented module; it does not say that a residual maximal ideal occurring only in the upper
module occurs in the source. Book 152, Theorem 16.1 exposes the same distinction: even when
the Gram operator splits the old image, the assertion that the selected oriented factor has
no support in the old quotient is a separate support theorem.

This failure of implication survives finite freeness, pairings, and upper-side patching. Here is a
minimal countermodel to any formal deduction from those properties. Let $\mathcal O$ be a
DVR and take

$$
M^{\min}=0,
\qquad M^{\rm up}=\mathcal O,
\qquad \mathbb T^{\rm up}=\mathcal O,
\tag{1.15}
$$

with the faithful scalar action and the perfect multiplication pairing on $M^{\rm up}$. The
map $(M^{\min})^{\oplus2}\to M^{\rm up}$ is injective with saturated image, so it satisfies the
formal conclusion of definite Ihara. Give the upper order the Weil--Deligne matrices

$$
N=\begin{pmatrix}0&\varpi\\0&0\end{pmatrix},
\qquad
\phi=\begin{pmatrix}q_v&0\\0&1\end{pmatrix};
\tag{1.16}
$$

then $\phi N\phi^{-1}=q_vN$ for arithmetic Frobenius, the generic monodromy is nonzero, and its residual monodromy is
zero. Thus the upper module is finite free, paired, faithful and nonzero, and the residual
local parameter is unramified, while the minimal localization is still zero. This is not an
arithmetic counterexample to level lowering; it proves that neither finite-module algebra,
residual monodromy vanishing, definite Ihara, nor patching of the upper system alone can imply
the required minimal occurrence.

For a finite target-extra set $P$, write $({\rm DLO}_P)$ for the first genuinely arithmetic
input:

$$
\boxed{
M^{\rm up}_{\mathfrak m}/\varpi\ne0
\quad\Longrightarrow\quad
M^{\min}_{\mathfrak m}/\varpi\ne0,}
\tag{1.17}
$$

with the same away Hecke system and the exact represented minimal local conditions, proved
either simultaneously or along an ordered chain whose hypotheses are reverified after every
removal. A paired-patching proof may instead construct upper and minimal local rings with a
common closed fiber and synchronized automorphic Taylor--Wiles modules. Proposition 1.1 then
transfers support without a pre-existing characteristic-zero minimal point. But the
mod-$\varpi$ module identification on the minimal side, or an equivalent theorem that the
upper residual block lies in the old support, is precisely the arithmetic content of
$({\rm DLO}_P)$; it does not follow from common local-ring equations.

This statement concerns a comparison whose output is an actual nonzero **minimal
automorphic module**. Theorem 1.1K and Corollary 1.1L follow a different route: they patch
the larger unipotent problem, prove that whole ring finite, and pass finiteness through its
minimal quotient. A point constructed afterward is automorphic through the already proved
broad support; this route does not assert $({\rm DLO}_P)$ or construct the clean minimal
module.

The later seed notation $({\rm DMS}_P)$ should therefore be read as

$$
({\rm DMS}_P)=({\rm DLO}_P)+({\rm CLN}_{\min}),
\tag{1.18}
$$

where $({\rm CLN}_{\min})$ is the verification on the resulting nonzero minimal localization
of the exact Book 173 hypotheses: stabilizer cleanliness, primary--companion perfectness,
generic reducedness of the acting order, branchwise integral Galois attachment, clean
diamond torsors, and exact module and acting-image augmentation. Books 83--85, 152, and
170--173 provide the individual constructions and implications once their displayed
arithmetic hypotheses and a nonzero minimal carrier are present. Book 172 cannot create the
carrier: its patched positive rank is inherited from residual occurrence at minimal level.

The optional exact-minimal route therefore begins only after the
specialization-dependent minimal localization has been shown nonzero. Transfers between
inner forms, Galois attachment, and conditional curve-geometric lowering all presuppose an
actual carrier and do not create it. Total definiteness simplifies the Ihara calculation,
but $({\rm DLO}_{P_{\rm tar}})$ remains the additional arithmetic input for this route. The
preferred target-IAV route instead has the boundary stated in Section 1.5A.

### 1.7 Outside-$\ell$ level optimization and the actual Frey set

The preceding boundary can be made substantially narrower. Let $F$ be an even-degree
prepared totally real field, let $\Pi^{\rm up}$ be an actual upper target packet, and let
$\bar\rho_F=\bar\rho|_{G_F}$. The actual target-extra set is

$$
P_{\rm tar}=
\{v\nmid2\ell:\Pi^{\rm up}_v\text{ is special of conductor one while the represented
minimal problem is unramified at }v\}.
\tag{1.19}
$$

Thus every $v\in P_{\rm tar}$ has the following exact local record:

1. $\bar\rho_F|_{G_{F_v}}$ is unramified, because the Frey residual representation is
   unramified away from $2\ell$;
2. $\Pi^{\rm up}_v$ is an unramified twist of Steinberg, because the specialized
   Hilbert--Blumenthal factor is semistable of toric rank one there; and
3. if $\alpha_v$ is the unramified twisting scalar, the two residual arithmetic-Frobenius
   roots are $\bar\alpha_v$ and $q_v\bar\alpha_v$.

In particular the residual Frobenius semisimplification has a repeated root exactly when
$q_v\equiv1\pmod\ell$; the actual residual matrix can be scalar or a nonsemisimple
repeated-root matrix. The congruence $q_v\equiv-1\pmod\ell$ has distinct roots for odd
$\ell$: it obstructs a one-sign Gram formula, but it remains in the ordinary unrefined
Mazur-principle range.

In a split preparation, (1.19) consists of any retained multiplicative places above $3$ and
the accidental semistable places discovered only after specialization. A controlled place
above $3$ is completely split, so $q_v=3$ and,
for $\ell\ge7$, it satisfies $q_v\not\equiv1\pmod\ell$. An accidental place has no such
congruence restriction. It may therefore lie in either the regular or scalar regime. The
dyadic places are not in (1.19), because the target problem retains their primitive
signed-special condition. A multiplicative coefficient-prime place is not repaired by
level lowering: unless the good finite-flat replacement was made before specialization, the
target path has not started.

Here is the exact one-place theorem which would settle both congruence regimes. It is useful
to state its spectator clause, since that clause is what makes a finite-set argument honest.

**Required theorem $({\rm FLO}_v)$ (outside-$\ell$ level optimization with spectators).**
Let $F$ be totally real, $\ell\ge3$, and let
$\bar r:G_F\to\operatorname{GL}_2(k)$ be absolutely irreducible, with
$\bar r|_{G_{F(\zeta_\ell)}}$ absolutely irreducible when the cyclotomic extension is
quadratic. Let $v\nmid\ell$ and suppose that

1. $\bar r|_{G_{F_v}}$ is unramified;
2. a cohomological cuspidal packet $\pi$ of parallel weight two gives $\bar r$ and has a
   vector fixed by $K_0(v)K^v$, where $K^v$ is a declared compact open away from $v$; and
3. the declared determinant is the canonical lift of the residual determinant.

Then, after finite coefficient extension, there is a cohomological cuspidal packet $\pi'$ of
the same weight and declared determinant which gives $\bar r$, has a $K^v$-fixed vector with
and is spherical at $v$.

The standard published level-optimization theorem does **not** prove this statement in both
congruence regimes. When $q_v\not\equiv1\pmod\ell$, Mazur principle proves the conclusion:
if the lower system did not occur, the invariant-cycle filtration would force Frobenius to be
scalar on the residual global block, whereas the special local parameter has the two distinct
roots $\bar\alpha_v,q_v\bar\alpha_v$. The even-degree proof uses a parity-compatible
quaternionic curve; the already retained dyadic special factor is an available
essentially-square-integrable spectator in the Frey application.

When $q_v\equiv1\pmod\ell$, the Frobenius contradiction disappears. The optimal general
level-optimization conclusion is only that a congruent output is spherical **or** an
unramified special representation. The auxiliary $q_z\equiv-1\pmod\ell$ construction in the
standard even-degree proof removes a parity hypothesis in the regular theorem; it does not
force the scalar output to be spherical. Accordingly write

$$
({\rm FLO}_v)=
\begin{cases}
({\rm MP}_v),&q_v\not\equiv1\pmod\ell,\\
({\rm SLO}_v),&q_v\equiv1\pmod\ell,
\end{cases}
\tag{1.20}
$$

where $({\rm MP}_v)$ is the usual Mazur-principle theorem with fixed away level and
$({\rm SLO}_v)$ is the genuinely stronger application-specific scalar-support assertion that
an occurring Iwahori-level output is spherical rather than remaining on any special or
scalar-tame conductor-one branch. The latter needs an additional arithmetic hypothesis or
proof; it is not a consequence of the standard level-optimization theorem.

The spectator clause causes no hidden local loss in the Frey application. At a dyadic
place, primitive residual monodromy has conductor one, so a packet giving the same residual
representation and retaining Iwahori level cannot become spherical; its invariant line and
sign are read from that residual local representation. At a place above $\ell$, $K^v$
preserves hyperspecial **automorphic level**. This does not by itself prove that a stable
Galois lattice for the output is finite flat with the selected model: Book 129 identifies
finite-flat models only after finite flatness has been supplied. That branchwise integral
attachment is deliberately part of $({\rm CLN}_{\min})$, not of the occurrence assertion
DLO. A not-yet-lowered target-extra spectator need only retain Iwahori invariants. If it
becomes spherical early, that is harmless and the place is deleted from the remaining set.
If its characteristic-zero Iwahori factor changes branch, the next application still meets
the $K_0(v)$ hypothesis of $({\rm FLO}_v)$; no induction step assumes that the current factor
remains the original Steinberg representation.

**Proposition 1.3 (finite-set reduction to $({\rm FLO}_v)$).** If
$({\rm FLO}_v)$ holds with the displayed spectator clause at every current member of
$P_{\rm tar}$, then $({\rm DLO}_{P_{\rm tar}})$ holds.

**Proof.** Order the finite set as $v_1,\ldots,v_t$. Begin with
$\Pi_0=\Pi^{\rm up}$. Apply $({\rm FLO}_{v_1})$ with hyperspecial level at no target-extra
place yet and Iwahori level at $v_2,\ldots,v_t$. The output $\Pi_1$ is spherical at $v_1$
and has the same residual representation and the declared level at every spectator. Inductively,
apply $({\rm FLO}_{v_i})$ to the current packet, omitting any later place which has already
become spherical. Every application preserves hyperspecial level at the previously removed
places and does not increase level elsewhere. The final packet $\Pi_t$ is spherical at all
of $P_{\rm tar}$, retains the signed-special residual localization, and remains hyperspecial
at the coefficient prime. The finite-flat attachment at that prime remains in
$({\rm CLN}_{\min})$.

Since $[F:\mathbf Q]$ is even, transfer $\Pi_t$ to the quaternion algebra ramified at every
real place and no finite place. Its finite components are unchanged. A fresh neat definite
class-set lattice contains the rational packet eigenline; scaling a generator to be primitive
gives a nonzero reduction in the exact minimal localization. This is (1.17). $\square$

This proposition proves that no genuinely simultaneous level-lowering theorem is needed once
the one-place theorem preserves spectators: ordinary induction is sufficient. The remaining
arithmetic hypothesis is the application-shaped $({\rm MP}_v)$. Books 21--22 give the
general invariant-cycle algebra, Books 104 and 125--129 transfer and attach packets already
known to occur, and Books 139 and 176 give the relevant saturation statements; none of these
conclusions alone implies $({\rm MP}_v)$. Book 140's lowering theorem assumes that the
component and normalized-branch obstructions vanish and excludes scalar, self-twist, and
vexing identifications, so it does not imply $({\rm SLO}_v)$ in the excluded cases. To obtain
$({\rm MP}_v)$ one first needs the ordinary totally-real Mazur principle with fixed away level.
In this application the existing dyadic special factor supplies the finite ramification needed
for the even-degree curve, while the argument must establish the localized integral
invariant-cycle filtration, residual isotypy, and the Frobenius--$U_v$ relation yielding the
distinct-root contradiction. One must then either show that no accidental target place has
$q_v\equiv1\pmod\ell$, or prove a scalar Mazur-principle theorem for the actual residual block
under explicit enhanced-line, component, branch, duality, and support hypotheses strong enough
to force the spherical alternative. Under those hypotheses Proposition 1.3 proves
$({\rm DLO}_{P_{\rm tar}})$. The separately defined $({\rm CLN}_{\min})$ conditions must still
be checked before one may write $({\rm DMS}_{P_{\rm tar}})$.

## 2. Local conventions and the three congruence regimes

### 2.1 Frobenius, Hecke operators, and monodromy

Fix geometric Frobenius $\Phi_v$. At a good place $v$ the Galois and automorphic polynomial
is

$$
X^2-T_vX+q_vS_v,
\qquad
\det\rho(\Phi_v)=q_vS_v.
\tag{2.1}
$$

The operators are unnormalized right double cosets, and the adjoint convention is

$$
T_v^*=S_v^{-1}T_v.
\tag{2.2}
$$

If $F_v$ denotes geometric Frobenius on a Weil--Deligne representation, the monodromy
normalization is

$$
F_vNF_v^{-1}=q_v^{-1}N.
\tag{2.3}
$$

With arithmetic Frobenius $\phi_v=F_v^{-1}$, equation (2.3) becomes
$\phi_vN\phi_v^{-1}=q_vN$. Both conventions occur naturally, but a proof must invert the
Frobenius roots, Hecke polynomial, and monodromy relation together. All formulas below use
(2.1)--(2.3).

The old pull--norm Gram operator is

$$
G_v=
\begin{pmatrix}
q_v+1&T_v\\
S_v^{-1}T_v&q_v+1
\end{pmatrix},
\qquad
D_v=(q_v+1)^2-S_v^{-1}T_v^2.
\tag{2.4}
$$

On a central square-root branch put $a_v=S_v^{-1/2}T_v$. A signed vector has Gram factor

$$
c_v^\varepsilon=q_v+1-\varepsilon a_v.
\tag{2.5}
$$

The scalar factor (2.5) is used only when an integral sign summand has independently been
constructed. Otherwise the full matrix (2.4) is the invariant object.

### 2.2 Special representations and conductor

Let $\operatorname{Sp}_2$ denote the two-dimensional special Weil--Deligne representation
with unramified scalar inertia and rank-one monodromy. If $\chi$ is a scalar tame character,
the conductor of $\chi\otimes\operatorname{Sp}_2$ has two distinct forms:

$$
a(\chi\otimes\operatorname{Sp}_2)=
\begin{cases}
1,&a(\chi)=0,\\
2,&a(\chi)=1.
\end{cases}
\tag{2.6}
$$

Indeed, for unramified $\chi$ the inertia invariants have dimension two and the rank-one
monodromy contributes one. If $\chi$ has tame conductor one, the scalar inertia character is
nontrivial, so the Weil space has no inertia invariants. The tame Artin term is then its full
dimension two, and the monodromy correction on inertia invariants is zero.

Thus the conductor-two family relevant here is not obtained by imposing a different rank on
$N$. It is obtained by scalar twisting a conductor-one special parameter by a conductor-one
tame character. At the trivial character the same relative family returns to conductor one.

### 2.3 Scalar tame variation forces q congruent to one

The congruence condition for this scalar family is forced by elementary local arithmetic.

**Lemma 2.1 (existence of an $\ell$-power conductor-one tame character).** Let
$v\nmid\ell$. A nontrivial character of $\ell$-power order and conductor one exists on
$F_v^\times$ only if

$$
q_v\equiv1\pmod\ell.
\tag{2.7}
$$

Conversely, if $\ell\mid q_v-1$, the residue-field units have a nontrivial $\ell$-power
quotient and hence such a character after a suitable coefficient extension.

**Proof.** A conductor-one tame character is trivial on $1+\mathfrak m_v$, so its ramified
part factors through
$\mathcal O_{F_v}^\times/(1+\mathfrak m_v)\simeq k_v^\times$. This cyclic group has order
$q_v-1$. It has a nontrivial $\ell$-power quotient exactly when $\ell\mid q_v-1$.
$\square$

The line-enhanced special equations give the same restriction at a scalar residual point.
With arithmetic Frobenius, choose a basis adapted to the monodromy line and write

$$
N=\begin{pmatrix}0&m\\0&0\end{pmatrix},
\qquad
\phi_v=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
\tag{2.8}
$$

The relation $\phi_vN=q_vN\phi_v$ gives

$$
m(a-q_vd)=0,
\qquad mc=0.
\tag{2.9}
$$

On the closure of the locus $m\ne0$ one has $a=q_vd$ and $c=0$. If residual Frobenius is
scalar and invertible, then $\bar a=\bar d\ne0$, so $(q_v-1)\bar d=0$. Again (2.7) follows.

### 2.4 Generic, scalar, and vexing level change

Three local regimes must not be combined.

| regime                               | arithmetic congruence        | integral object                                                                                             | conclusion available before patching                                                                                                                                                                                                                                           |
| ------------------------------------ | ---------------------------- | ----------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| generic unramified-to-special change | $q_v\not\equiv\pm1\pmod\ell$ | separated old roots and a signed one-prime Gram block                                                       | conditional level raising and integral curve--definite comparison from Book 140                                                                                                                                                                                                |
| scalar tame twist                    | $q_v\equiv1\pmod\ell$        | enhanced line, sign, Book 174's strict global ray quotient $\Delta_v$, and $\Lambda_v=\mathcal O[\Delta_v]$ | Book 174's strict type complex under $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$, support under $({\rm SUP}_v)$, and exact twist augmentation; constant Ihara and primitive residue are separately required only for the corrected component filtration and extreme residue |
| vexing sign collision                | $q_v\equiv-1\pmod\ell$       | full primary--companion block and full Gram matrix                                                          | one-prime block statements; no scalar $\ell$-power twist face                                                                                                                                                                                                                  |

The first row changes an unramified packet to a conductor-one special packet. The second row
varies a special packet between conductor one and conductor two. Lemma 2.1 shows that no datum
can simultaneously require a nontrivial scalar $\ell$-power conductor-one character and
$q_v\not\equiv1\pmod\ell$. In the third row both signed Gram factors can be nonunits, so a
single factor such as (2.5) cannot replace the full Smith module of (2.4).

## 3. The one-prime datum without hidden global hypotheses

### 3.1 Residual and coefficient-prime data

We first define the arithmetic objects. We do not include the theorems needed to compare them.
Let $\ell\ge7$, let $(\mathcal O,\varpi,k,E)$ be a coefficient DVR, and let (1.1) be totally
odd. Require

$$
\bar\rho|_{G_{F(\zeta_\ell)}}
\quad\text{to be absolutely irreducible}.
\tag{3.1}
$$

Retain also the adjoint-invariant vanishing required by the chosen Taylor--Wiles problem,
for example

$$
H^0\!\left(F,\operatorname{ad}^0\bar\rho(1)\right)=0.
\tag{3.1a}
$$

Fix a determinant compatible with a parallel-weight-two central character. At each
$w\mid\ell$, require $F_w/\mathbf Q_\ell$ to be unramified and impose the represented
finite-flat weight-$\{0,1\}$ condition on every Artinian quotient. At every unchanged place
away from $\ell$, impose the exact represented minimal condition: unramified, a fixed
prime-to-$\ell$ type, or a named special closure with every line, sign, determinant, and
monodromy label retained.

Assume a residual automorphic packet occurs in a proper compact weight-two quaternionic or
PEL-curve realization with exactly these unchanged local data. The localization is
non-Eisenstein, and fine level is neat or every stabilizer used in descent has order invertible
in $\mathcal O$.

These conditions define the global residual problem. They do not imply Ihara injectivity,
node uniformization, component support, reducedness of a patched source, or a ring equality.

### 3.2 The represented local condition at the changed place

Fix $v\nmid\ell$. A **geometric one-prime datum at $v$** records:

1. the hyperspecial and standard Iwahori PEL levels and their two degeneracy maps;
2. a represented line-enhanced special local deformation condition;
3. a monodromy line, orientation, sign, determinant, and any fixed prime-to-$\ell$ scalar
   inertia character;
4. primary and companion integral type lattices with their perfect pairing; and
5. the chosen local regime from Section 2.4.

For the scalar line-special package used in Chapters 6--7, the fixed prime-to-$\ell$ scalar
character in item 3 is trivial, exactly as in Book 175, Section 2.2. A broader datum may retain
a nontrivial one only when it is supplied as a named global rigid twist whose determinant line
is trait-pulled; the strict $\ell$-power quotient below does not globalize or compute an
otherwise arbitrary prime-to-$\ell$ local character.

In the scalar-twist regime it uses the strict quotient
$\Delta_v=C_{\ell^{\operatorname{ord}_\ell(q_v-1)}}$ and global character constructed in
Book 174, (2.2a)--(2.2d), not a local abstract character or an arbitrary cyclic quotient.
Its local field is $F_v(\pi_v^{1/|\Delta_v|})$, its vertical unit is $1$, and any additional
conductor places are fixed spectators. Put

$$
\Lambda_v=\mathcal O[\Delta_v],
\qquad
\boldsymbol\chi_v:G_F\longrightarrow\Lambda_v^\times.
\tag{3.2}
$$

Because $\Delta_v$ is an $\ell$-group, its group-like elements are congruent to one at the
augmentation maximal ideal. Thus the twist varies characteristic-zero tame characters while
retaining the declared residual representation.

If $\delta^{(1)}$ is the conductor-one determinant, the universal determinant is

$$
\delta^{(2)}=\delta^{(1)}\boldsymbol\chi_v^2.
\tag{3.3}
$$

The square is forced by the rank. Omitting it would compare two different fixed-determinant
problems. The local datum also requires $q_v\equiv1\pmod\ell$, as proved in Lemma 2.1.

At a scalar residual point, the represented line-incidence chart has the form

$$
A_{\mathrm{inc}}
=R_0[[m,u,c]]/(mu,mc),
\tag{3.3a}
$$

where $m$ is the monodromy coordinate and $u,c$ are the two incidence failures. The selected
special component is the schematic closure of the locus with the named line and nonzero
monodromy:

$$
A_{\mathrm{sp}}=A_{\mathrm{inc}}/(u,c)
\simeq R_0[[m]].
\tag{3.3b}
$$

The base $R_0$ retains the unramified and tame Kummer directions. The closure necessarily
contains its boundary $m=0$, because nonzero monodromy is open rather than a condition stable
under all Artinian quotients. Consequently every characteristic-zero conductor assertion
below includes the separate condition that the specialized monodromy be nonzero.

Augmentation of the scalar character returns this conductor-one **line-special** problem,
with its line, sign, Kummer directions, and monodromy closure. It does not return an arbitrary
unramified minimal problem. There is a map to a neutral minimal boundary only when an actual
inclusion of represented functors supplies the corresponding quotient of rings.

### 3.3 Automorphic carriers and faithful orders

Let $P_v^0$ and $P_v^1$ be the primary lattices at the lower and edge levels, after all fixed
types and auxiliary levels have been imposed. The two degeneracy maps give

$$
C_v^{\mathrm{pri}}
=\left[(P_v^0)^{\oplus2}\xrightarrow{d_v}P_v^1\right]
\tag{3.4}
$$

in degrees $0,1$. The companion complex is the adjoint dual with the inverse character. Its
presence is essential when a primary projector is not self-adjoint or when the two integral
Steinberg lattices are opposite nonsplit extensions.

Call the following package $({\rm AUT}_v)$: the localization is nonzero and non-Eisenstein;
the displayed primary and companion lattices are finite free and perfectly paired; their
line, sign, determinant, central, and stabilizer data are the actual ones; and every generic
factor lies in the verified Galois-attachment and local--global compatibility range. This
package can be realized directly on the curve-new carrier. Switching to a definite lattice is
a further comparison. In the clean constant-coefficient block it requires Book 140's
datum-specific node uniformization and Book 125 component-routing source condition, together
with $({\rm AIH}_{\mathscr F})$; Book 140 then proves generic support and common-kernel
equality, rather than assuming them. A typed switch uses the proved $({\rm TPE}_v)$ and
additionally requires the accompanying $({\rm TIC}_v)$ incidence hypothesis,
$({\rm TIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$,
$({\rm NU}_{\rm type})$, and Book 125's decomposition on the actual common principal cover
with full routing or a separating component projector. Under $({\rm AIH}_{\mathscr F})$,
$({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, and that Book 125
source condition, Book 174, Proposition 6.3 proves the typed generic-residue kernel equality;
it is not a further hypothesis.

The Hecke algebra is the faithful image on the direct sum of the primary and companion
carriers. It is generated by the verified good traces, the fixed determinant, and only those
named local or diamond operators proved to belong to the trace or structural order. At a
retained finite level, Book 170 then supplies a map

$$
R_v^{\mathrm{nm}}\twoheadrightarrow\mathbb T_v^{\mathrm{nm}}
\tag{3.5}
$$

only after every generic branch has the required integral Galois realization and local--global
compatibility. The direction in (3.5) is contravariant: the Hecke-valued family is a point of
the universal deformation problem.

### 3.4 What is deliberately not part of the definition

The following statements are hypotheses or conclusions, never clauses in the geometric datum:

- the finite family of constant-coefficient abelian Ihara vanishings
  $({\rm AIH}_{\mathscr F})$;
- the proved typed parahoric extension and ramified nearby-cycle comparison $({\rm TPE}_v)$,
  and the separate actual-incidence and coarse-descent hypothesis $({\rm TIC}_v)$;
- the crossed-coefficient residual type-Ihara theorem
  $({\rm TIH}_{\mathscr F})$;
- saturation of the old image and freeness of its quotient;
- vanishing of the integral primitive type-residue obstruction $({\rm PRI}_{\rm type})$ at
  every retained level;
- typed node uniformization $({\rm NU}_{\rm type})$ and equality of integral curve and
  definite orders;
- vanishing of a Néron component group or of the independent branch Smith correction;
- the one-prime boundary and depth datum $({\rm SUP}_v)$, which proves support on every
  selected deformation component;
- reducedness or faithfulness of the patched deformation source;
- vanishing of a mixed kernel at two changed places; and
- joint support on a product of local components.

This separation fixes the logical order of the conclusions. Book 139's corrected
constant-coefficient filtration may be used only under constant abelian Ihara. Formation of
the projective typed new quotient additionally requires the typed parahoric extension, type
incidence, and type-Ihara hypotheses. A one-prime support theorem remains valid without
finite-set mixed vanishing, but it gives no simultaneous finite-set conclusion.

## 4. The imported one-prime level-change package

Chapters 4--6 recall the one-prime level-change results. Book 139 supplies the
constant-coefficient tree kernel and conditional saturated Ihara package; Book 174 supplies
the actual typed incidence complexes, primitive residues, enhanced component support, and
strict augmentation; Book 175 supplies the scalar line-special finite-level comparison and
characteristic-zero modularity. Chapter 7 applies those results and isolates the formal
generic and vexing variant. Chapters 8--9 then formulate and prove the exact conditional
several-place application statements.

### 4.1 The exact residual kernel

Book 139, Theorem 6.1 identifies the residual constant-coefficient kernel with
$H^1(\Gamma^v,k)^\Delta$. Its congruence-character submodule is Eisenstein; after the
declared non-Eisenstein localization, the kernel is the localized $\Delta$-invariant
noncongruence quotient displayed in Book 139, (6.8a). It is not zero by formal tree
contractibility.

### 4.2 The abelian Ihara hypothesis

The vanishing $({\rm AIH}_{\mathscr F})$ must hold at every actual constant flag level used in
the construction. Under it, Book 139, Theorems 7.1, 10.2, 12.1, and 14.1 give saturation,
component control, new-quotient duality, and the exact Gram package. None is a typed Ihara
theorem.

### 4.3 Consequences after the hypothesis is supplied

Only after $({\rm AIH}_{\mathscr F})$ is supplied may a constant old image be called primitive
and its quotient finite free. Book 174 separately requires $({\rm TIC}_v)$ and
$({\rm TIH}_{\mathscr F})$ for the primary and companion type shadows.

### 4.4 The six lowering conditions

Book 139's Néron component module and branch Smith correction remain in the corrected
filtration. They are not identified with coefficient-base Tor and are not discarded when the
typed complex is formed. When a modularity-lifting application lowers a $v$-new residual
eigensystem to hyperspecial level, the clean lowering criterion of Book 140, Theorem 12.1 is
used in the following six grouped clauses, in addition to the saturated one-prime face already
required in Sections 4.1--4.3:

1. the localized residual block is non-Eisenstein and stable under the Hecke adjoint;
2. the residual Poincaré pairing on that block and its adjoint is perfect and pairs the top
   graph quotient with the saturated bottom submodule;
3. the full residual monodromy operator vanishes on the localized new block, not merely on
   its semisimplification;
4. both integral correction terms are clean: the localized Néron component obstruction has
   no residual contribution and the normalized-branch Smith module has no residual torsion;
5. the normalization middle term is exactly the two lower-level branches, with no stabilizer
   or coefficient torsion; and
6. the localized block is nonzero, and no scalar, self-twist, or vexing identification merges
   it with an Eisenstein block or with a different adjoint block.

These clauses are sufficient for the uniform lowering argument. They are not consequences of
vanishing residual monodromy alone, and they are rechecked whenever a previous level change
alters the spectator tuple.

## 5. The one-prime type complex

### 5.1 Primary and companion lattices

The actual primary and companion sheaves, their flag representations, and the coefficient-one
incidence maps are those of Book 174, Chapters 3--4. For later compatibility we denote the
resulting strict complexes by $C_v^+$ and $C_v^-$.

### 5.2 The incidence complex and its Tor term

**Imported theorem 5.1.** Under the proved $({\rm TPE}_v)$, the actual-incidence descent
$({\rm TIC}_v)$, and the independently supplied residual injectivity
$({\rm TIH}_{\mathscr F})$, the unit-minor argument of Book 174, Theorem 5.2 proves split
amplitude and projectivity of the one-prime new cohomology over the declared coefficient
base. Book 174 states that theorem through Lemma 5.1, which derives the required residual
injectivity from $({\rm AIH}_{\mathscr F})$ in the projector range and retains the additional
quotient-new injection (5.0d) in the nonbanal range. Assuming $({\rm TIH}_{\mathscr F})$
directly is the logically equivalent input at this step; it must not be credited to constant
Ihara alone. Consequently all coefficient-base Tor vanishes. This does not imply the mixed
two-place vanishing defined in Chapter 8.

### 5.3 The scalar-twist face

Book 174, Section 2.2 constructs the strict global ray quotient, and Chapter 9 proves the
scalar-twist identity with the exact determinant square. A character fiber of a group algebra
is not assumed flat.

### 5.4 Support is not faithfulness

Book 174, Theorem 8.3 gives full topological support under the separate five-clause datum
$({\rm SUP}_v)$. For a noetherian source $R$ and carrier $M$ this says only

$$
\operatorname{Ann}_R(M)\subseteq\sqrt{(0)}.
\tag{5.7}
$$

It does not kill nilpotents or prove a full ring equality.

## 6. The conditional one-prime R=T theorem

The results recalled in this chapter concern the scalar-residual line-special problem of
Book 175, hence $q_v\equiv1\pmod\ell$. They do not upgrade the generic distinct-root row or the
$q_v\equiv-1\pmod\ell$ vexing row of Section 2.4; those ranges require their own balanced
presentation, supported module, and coherent auxiliary theorem. The formal reduced-image
argument itself is more general: once such an actual carrier, full support, and finite
reciprocity have independently been supplied, Lemma 6.1 applies. Theorem 7.1A states that
conditional application without attributing its carrier to Book 175.

### 6.1 The explicit comparison hypotheses

For compatibility with earlier citations, the one-prime package consists of the following
separate inputs, in exactly the sense of Books 174--175:

1. $({\rm AUT}_v)$: the actual non-Eisenstein primary--companion automorphic localization;
2. $({\rm TYPE}_v)$: the proved $({\rm TPE}_v)$, together with $({\rm TIC}_v)$ and
   $({\rm TIH}_{\mathscr F})$ at every retained shadow;
3. $({\rm SUP}_v)$: the marked boundary, unique-component, nonzero-carrier, and depth datum of
   Book 174;
4. $({\rm REC}_v)$: one order-valued representation on every generic branch, all-Artinian
   factorization through the represented local conditions, and generation of the faithful order
   by the verified operators;
5. $({\rm RAY}_v)$ for a scalar family: the strict quotient
   $\Delta_v=C_{\ell^{\operatorname{ord}_\ell(q_v-1)}}$ of Book 174,
   (2.2a)--(2.2d), with its conductor spectators, strict twist identities, and determinant
   square; and
6. $({\rm AUX}_Q)$ when auxiliary patching is used: clean auxiliary torsors and exact
   augmentation of represented rings, primary and companion complexes, modules, actions, and
   pairings, with zero positive diamond-algebra Tor. The faithful acting-order quotient is a
   canonical surjection at each isolated level. For a coherent unpadded system at every depth,
   Book 175, Proposition 5.2 proves $({\rm GR}_v)$ and full base $R=T$ by equal-variable rigidity;
   Corollary 4.5 then derives injectivity of the acting-order quotient rather than assuming it.

The richer curve-to-definite component comparison additionally retains
$({\rm AIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, and, when used,
$({\rm NU}_{\rm type})$. Those hypotheses are not folded into $({\rm SUP}_v)$.

### 6.2 Full support and the reduced image

**Lemma 6.1 (full support and reduced image).** This is Book 175,
Lemma 4.1. If $R$ is noetherian, $M$ is finite with full support, and the faithful acting image
$T$ is reduced, then

$$
\ker(R\twoheadrightarrow T)=\sqrt{(0)},\qquad R_{\rm red}\simeq T.
\tag{6.3}
$$

### 6.3 The reduced comparison and the full-equality criterion

**Theorem 6.2 (scalar line-special finite-level reduced $R=T$).** Under
the six applicable inputs in Section 6.1, Book 175, Theorem 4.2 gives

$$
\boxed{(R^{\rm nm})_{\rm red}\xrightarrow{\sim}\mathbb T^{\rm nm}.}
\tag{6.4}
$$

The finite Hecke order is reduced because it is $\mathcal O$-torsion-free with semisimple reduced
generic fiber. No reducedness of an abstract patched acting image is inferred.

**Corollary 6.3 (full equality criterion).** Book 175, Corollary 4.3 says
that the finite-level comparison is a full isomorphism exactly when the selected global source is
reduced. Local-chart reducedness and minimal $R=T$ do not imply that condition.

**Corollary 6.3a (balanced coherent scalar one-prime $R=T$).** If the
$({\rm AUX}_Q)$ systems in Section 6.1 form the coherent unpadded tower at every depth, Book
175, Proposition 5.2 proves

$$
R_\infty^{\rm nm}=\mathbb T_\infty^{\rm nm},
\qquad
R^{\rm nm}=\mathbb T^{\rm nm}.
\tag{6.5}
$$

The patched ring is regular, its primary module is nonzero finite free over it, and the finite
ring is a finite free complete intersection over $\mathcal O$. Every characteristic-zero
enhanced fixed-condition tangent--Selmer group vanishes, including the line term at a
monodromy-zero point. The strict ray twist transports the statement to the scalar family and
every retained fixed-character fiber.

### 6.4 Descent to finite level and fixed characters

Book 175, Chapter 5 proves the balanced coherent patch theorem and the exact augmentation
boundary. Its Chapter 6 treats the scalar fixed-character fibers without commuting reduction
through a nonflat character quotient and records why the vexing full block has no scalar
augmentation theorem. Without a coherent auxiliary tower, only the scalar reduced comparison
and the source-reducedness criterion of Corollary 6.3 are available from Book 175.

## 7. The modularity-lifting conclusion

### 7.1 The one-prime application theorems

**Theorem 7.1 (conditional scalar line-special modularity lifting).** This
is Book 175, Theorem 7.1. Assume $q_v\equiv1\pmod\ell$ and the applicable hypotheses of
Section 6.1. Every characteristic-zero point of the represented scalar line-special problem
whose specialized rank-one monodromy is nonzero is attached to a cuspidal
parallel-weight-two automorphic representation with the same determinant, coefficient-prime
finite-flat condition, unchanged local components, and selected line, sign, scalar character,
and special component. The conductor exponent is one on the augmentation character and two on
a retained nontrivial scalar-character fiber. The reduced comparison still factors a
monodromy-zero characteristic-zero point through the faithful order, but Book 175, Theorem
7.1 does not attach to that factorization the displayed special-conductor conclusion.

For the conductor-one conclusion alone, $({\rm RAY}_v)$ may be omitted and the application
may start directly from the represented conductor-one line-special ring, exactly as in Book
175, Theorem 7.1. This is not an augmentation to an arbitrary unramified minimal problem.

**Theorem 7.1A (conditional generic and vexing one-place application).** Let $v\nmid\ell$
lie in the generic regime $q_v\not\equiv\pm1\pmod\ell$ or in the vexing regime
$q_v\equiv-1\pmod\ell$. Let $R_v$ be the noetherian represented fixed-determinant deformation ring for
the exact local component to be reached. Suppose that:

1. an actual finite primary--companion carrier $M_v$ for that component has been constructed,
   with the applicable $({\rm AUT}_v)$, $({\rm TYPE}_v)$, and $({\rm SUP}_v)$ data;
2. every constant, typed, residue, node, component, and lowering assertion used to construct
   that carrier satisfies its separately named hypothesis from Chapters 3--5, including the
   six clauses of Section 4.4 when lowering occurs;
3. $({\rm REC}_v)$ gives a surjection from $R_v$ onto the faithful image
   $\mathbb T_v$ on $M_v$, and $\mathbb T_v$ is $\mathcal O$-torsion-free with reduced
   generic fiber; and
4. in the vexing regime, either the full primary--companion block is retained with all its
   labels, or an integral signed direct factor and its support have been independently
   constructed. No sign projector available only after inverting $\varpi$ is used.

Then

$$
(R_v)_{\rm red}\xrightarrow{\sim}\mathbb T_v,
\tag{7.1a}
$$

and every characteristic-zero point of $R_v$ is attached to a cuspidal
parallel-weight-two automorphic representation with the same determinant, coefficient-prime
condition, and named local data. A selected generic special point with nonzero rank-one
monodromy has conductor exponent one. In the vexing regime the conclusion remembers a sign
only when the integral signed factor in clause 4 has been constructed; there is no scalar
$\ell$-power twist family there.

**Proof.** Full support identifies the kernel of
$R_v\twoheadrightarrow\mathbb T_v$ with the carrier annihilator. The target is reduced by
the torsion-free reduced-generic criterion, so Lemma 6.1 gives (7.1a). A point over a domain
kills the nilradical and therefore factors through the faithful order. The order-valued
representation and the verified branch labels recover the automorphic representation and its
local data. The conductor statement is the unramified special case of (2.6). $\square$

### 7.2 Recovery of an automorphic representation

A point over a DVR kills the nilradical and therefore factors through (6.4). The actual faithful
carrier and Book 170's order-valued representation recover the eigenpacket and its Galois
representation. Bad-place conclusions come from prior integral local factorization, not from
good Frobenius traces. In the generic or vexing application, the same sentence uses (7.1a)
instead of (6.4).

### 7.3 Coefficient extension

Book 175 retains coefficient extension only after selecting the residual factor and base-changing
every represented local problem, type lattice, pairing, complex, and faithful order. Raw
uniformizer lengths scale with ramification.

### 7.4 Solvable base change and descent

Book 175, Section 7.3 imports solvable descent only after irreducibility, local antecedents,
image criteria, and cyclic descent are checked at every step. Splitting one base place into
several active places creates the finite-set problem below.

### 7.5 Exact exceptional boundaries

The scalar line-special theorem remains conditional, starts uniformly at
$\ell\ge7$, and excludes Eisenstein and primitive-wild localizations. It proves reduced
finite-level $R=T$ from the base one-prime hypotheses, and full patched and finite $R=T$ when the
coherent unpadded $({\rm AUX}_Q)$ tower is also retained. In the absence of that tower, global
source reducedness remains the exact alternative. Theorem 7.1A does not extend Book 175 to a
new scalar family: it is the formal reduced-image application to a separately constructed
generic or vexing carrier satisfying all of its displayed hypotheses. In particular, the
vexing full block cannot be replaced by a single sign without an integral projector and
support theorem. These are mathematical boundaries of the inputs, not new hypotheses hidden
in the application.

## 8. The several-place application boundary

### 8.1 Why two saturated edges do not make a saturated square

Let $v$ and $w$ be two active places, with every other place frozen at an actual spectator
level. Write $M_{ab}$ for the localized carrier with hyperspecial or Iwahori level according
to $a,b\in\{0,1\}$. The two $v$-maps and two $w$-maps form a commutative square and hence a
three-term total incidence complex

$$
C_{v,w}^+:
M_{00}^{\oplus4}
\longrightarrow
M_{10}^{\oplus2}\oplus M_{01}^{\oplus2}
\longrightarrow M_{11}.
\tag{8.1}
$$

The sign in the second differential is the usual product orientation. Suppose every one-place
row is injective and saturated. This controls each old image separately, but not

$$
\operatorname{im}(d_v)\cap\operatorname{im}(d_w)\subseteq M_{11}.
\tag{8.2}
$$

This failure already occurs in the exact incidence shape over a field. Take
$M_{00}=k$, $M_{10}=M_{01}=k^3$, and $M_{11}=k^7$. Let both lower two-map
differentials embed $k^2$ as the first two coordinates. Identify each top source
$k^3\oplus k^3$ with $k^6$ so that the lower-left $k^4$ has image
$U_0=\langle a_1,a_2,a_4,a_5\rangle$. Map the first top source injectively onto
$\langle e_1,\ldots,e_6\rangle$ and the second injectively onto
$\langle e_1,e_2,e_3,e_4,e_5,e_7\rangle$, carrying both copies of $U_0$ to
$U=\langle e_1,e_2,e_4,e_5\rangle$. All four edge differentials are
split injective and the square commutes, but the two top images intersect in dimension five,
whereas the lower-left image has dimension four. Thus the total complex has a one-dimensional
middle class. The product of the two Bruhat--Tits trees is contractible before an arithmetic
quotient is taken, but stabilizer cohomology can create exactly such a class after the
quotient. Contractibility alone therefore does not prove exactness of (8.1).

### 8.2 The mixed Ihara module

Reduce modulo the maximal ideal. First take the $v$-row cokernels

$$
N_{v\mid b,k}
=\operatorname{coker}\left(
M_{0b,k}^{\oplus2}\longrightarrow M_{1b,k}
\right),
\qquad b=0,1.
\tag{8.3}
$$

The two $w$-maps induce

$$
\overline d_{w\mid v}:
N_{v\mid0,k}^{\oplus2}\longrightarrow N_{v\mid1,k}.
\tag{8.4}
$$

Define the **mixed Ihara obstruction**

$$
\operatorname{Ob}_{v,w}
=\ker\overline d_{w\mid v}.
\tag{8.5}
$$

Filtering the bicomplex first in the $v$-direction gives

$$
H^0(C_{v,w}^+\otimes k)=0,
\qquad
H^1(C_{v,w}^+\otimes k)
\simeq\operatorname{Ob}_{v,w},
\tag{8.6}
$$

and

$$
H^2(C_{v,w}^+\otimes k)
\simeq\operatorname{coker}\overline d_{w\mid v}.
\tag{8.7}
$$

The opposite filtration identifies the same group with
$\ker\overline d_{v\mid w}$. Equivalently,

$$
\operatorname{Ob}_{v,w}\simeq
\frac{
\operatorname{im}(d_w)\cap\operatorname{im}(d_v)
}{
\operatorname{im}(d_vd_w)
}
\quad\text{inside }M_{11,k}.
\tag{8.8}
$$

The one-place theorem proves injectivity before the first cokernel in (8.3) is taken. It does
not prove injectivity of (8.4), whose coefficient is now a global $v$-new quotient. Calling
that quotient an ordinary spectator coefficient system would assume precisely the theorem
being sought.

### 8.3 Top-degree concentration is equivalent to mixed vanishing

The remaining algebra is exact and useful.

**Lemma 8.1 (two-place concentration criterion).** Let $(A,\mathfrak n,k)$ be local and let
$C=[P^0\to P^1\to P^2]$ be a complex of finite free $A$-modules. If
$H^0(C\otimes_Ak)=0$, then $C$ is homotopy equivalent to a finite free module in degree two
if and only if $H^1(C\otimes_Ak)=0$.

**Proof.** Split unit entries from the two differentials until a minimal free complex remains.
Both residual differentials of that minimal complex are zero. Its residual degree-zero and
degree-one cohomology are therefore its degree-zero and degree-one modules. The two vanishing
conditions force those modules to be zero. Only a finite free degree-two module remains.
Conversely, a complex homotopy equivalent to a degree-two free module has no lower residual
cohomology. $\square$

Applying the lemma to (8.1) and using (8.6) gives

$$
C_{v,w}^+\simeq N_{v,w}^+[-2]
\quad\Longleftrightarrow\quad
\operatorname{Ob}_{v,w}=0,
\tag{8.9}
$$

where $N_{v,w}^+$ is finite free over the face algebra. Under this equivalent condition the
two total boundaries are primitive and every required face Tor group for this complex
vanishes. If the primary and companion total cubes carry the product of the one-place perfect
adjunctions with their required total shift, the companion's unique surviving module is then
the full dual of $N_{v,w}^+$.

**Mixed-vanishing hypothesis.** For each geometric pair from Chapter 3, with its actual
spectator tuple and auxiliary shadow and with both primary and companion systems retained,
require

$$
\operatorname{Ob}_{v,w}=0
\tag{8.10}
$$

This condition is additional to the one-prime hypotheses. When it holds, (8.9) gives
top-degree concentration, primitivity of both total boundaries, all face-Tor vanishings for
this complex, and the stated primary--companion duality; none of these conclusions is asserted
without (8.10).

### 8.4 Ordered quotient cubes and higher mixed classes

The two-place calculation has a finite-set version which is entirely formal once one actual
global cube has been constructed. It separates that formal construction from the additional
mixed-exactness hypotheses required after successive quotient formation.

Let $(A,\mathfrak n,k)$ be local, let $P=\{v_1,\ldots,v_r\}$ be ordered, and let
$\mathscr C_P$ be a strict $P$-fold incidence diagram of finite free $A$-modules. In each
direction its two-term differential includes the two degeneracy legs, so the multiplicities
are the powers of two visible in (8.1). Write $C_P=\operatorname{Tot}(\mathscr C_P)$. Assume
first that every raw $v_1$-edge is split injective. At each spectator vertex
$\epsilon\in\{0,1\}^{P\setminus\{v_1\}}$, let

$$
N_{v_1\mid\epsilon}
=\operatorname{coker}(d_{v_1\mid\epsilon}).
\tag{8.11}
$$

Commutativity of the cube makes these cokernels into a strict
$(P\setminus\{v_1\})$-cube, denoted $N_{v_1\mid\bullet}$.

The existence of the underlying level cube is more formal than its exactness. Fix one
prime-to-$P$ level and, at each $v\in P$, the adjacent hyperspecial and Iwahori levels. On the
full routed component union, or on a union proved stable under every required route, Books
123--124 construct the forgetful level maps and the right-translation maps defining the two
degeneracy legs. For $v\ne w$ the corresponding adelic elements lie in different restricted
product factors. Hence they commute, and the transitivity squares for forgetting level commute
as well. This common-carrier assertion is already integral in the definite class-set model:
Book 84, Section 11.9 constructs the single map
$\Delta_P:M(U)^{\oplus 2^{|P|}}\to M(U_0(P))$ and factors every entry of
$\Delta_P^*\Delta_P$ into its one-place Gram entries. Book 152, Proposition 11.1 likewise
constructs all regular-refinement idempotents on that one $2^{|P|}$-fold source. These are
genuine upstream owners of the multi-prime source and its commuting operators; neither theorem
proves that the sum of the two upper old images is primitive, that an induced map on a
quotient-new module is injective, or that the full oriented module is old. On a common fine
refinement the associated coefficient systems of Book 174 are
obtained from one finite generic cover. Provided that the product coefficient representation
and its effective descent have actually been supplied, tensoring those coefficient
representations and their intertwiners therefore gives a coherent $P$-cube of generic curves,
coefficient systems, and pull maps. A common cellular subdivision represents its derived
cohomology cube strictly. The trace maps give the companion cube; transitivity of pullback and
trace, together with the product orientation, gives the cubical primary--companion adjunction.

This construction is conditional on the actual joint coefficient descent and component
routing. In particular, separate scalar ray covers do not construct their product cover. It
also constructs only $({\rm CUBE}_P)$: commutation of two geometric level modifications does
not say that the resulting total cohomology complex is exact. The same cellular proof as Book
174, Proposition 4.1 makes every vertex perfect over one common coefficient algebra; after the
no-character localization, the fiber-concentration argument gives finite projective vertex
modules. Extension through the bad integral model at a face uses the proved actual-row theorem
$({\rm PNS}_v)_{\rm act}$ of Book 122, Corollary 9.11, together with
$({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$ for that exact spectator tuple; the generic
cube does not prove the latter two. None of these statements identifies the total
cube with a tensor product of its full global one-prime cohomology complexes.

**Proposition 8.2 (ordered quotient-cube reduction).** There is a natural quasi-isomorphism

$$
C_P
\simeq
\operatorname{Tot}(N_{v_1\mid\bullet})[-1].
\tag{8.12}
$$

Repeat the construction in the order $v_1,\ldots,v_r$. Suppose that, at every later step
$i=2,\ldots,r$ and every remaining spectator vertex, the induced two-map differential on the
already formed
$(v_1,\ldots,v_{i-1})$-new quotient is injective after reduction to $k$. Then every such
integral differential is split injective, the final iterated quotient $N_P$ is finite free over
$A$, and

$$
C_P\simeq N_P[-r].
\tag{8.13}
$$

Consequently, for every $A$-algebra $B$,

$$
C_P\otimes_A^LB
\simeq (N_P\otimes_AB)[-r],
\qquad
\operatorname{Tor}_j^A(N_P,B)=0\quad(j>0).
\tag{8.14}
$$

**Proof.** In the $v_1$-direction, each two-term edge complex is quasi-isomorphic to its
cokernel in degree one. These quotient maps commute with every remaining face map, so they give
an objectwise quasi-isomorphism of finite cubical diagrams. Totalizing gives (8.12). At the next
step the terms are finite projective, hence finite free because $A$ is local. Residual
injectivity exhibits a unit maximal minor, so elementary operations split the induced map and
make its cokernel finite free. Induction gives (8.13). A finite free top quotient has no positive
Tor, which proves (8.14). $\square$

**Cubically compatible contraction criterion.** There is a useful stronger formal certificate
which explains exactly when the recursive hypothesis descends automatically. Suppose every
raw edge of the $P$-cube has a chosen
retraction and every such retraction commutes with all forward maps and retractions in the
transverse directions. Splitting the first direction then makes all transverse maps and
retractions descend to its quotient cube. The descended retractions again split every edge,
so induction applies in every ordering and gives (8.13)--(8.14). We call this a **cubically
compatible contraction**. Its conclusion is stronger than a collection of unrelated split
edges: it is the compatibility of the retractions with the whole cube that makes every
iterated-new edge split. The commuting refinement idempotents on Book 152's common source do
not by themselves supply these retractions on the actual oriented quotient cube. In the
stronger unit-Gram range, however, Book 84's placewise Gram factorization and commuting local
correspondences give the canonical pull--trace retractions on its common definite cube; when
their compatibility has been retained at every spectator face, they form precisely such a
cubical contraction. This source-closed case does not include a selected nonunit
level-raising face.

The successive edge hypothesis in Proposition 8.2 is a convenient sufficient certificate. For
$r\ge3$ it is not asserted to be necessary: differentials in the remaining directions can
cancel homology produced by an individual quotient edge. The exact condition after the first
split direction is obtained by defining

$$
\operatorname{Ob}_{P;v_1}^j
=H^j\!\left(\operatorname{Tot}(N_{v_1\mid\bullet})\otimes_Ak\right),
\qquad 0\le j<r-1.
\tag{8.14a}
$$

The same minimal-complex argument as in Lemma 8.1, now in length $r$, and (8.12) give the
equivalence

$$
C_P\simeq N_P[-r]\text{ for a finite free }N_P
\quad\Longleftrightarrow\quad
\operatorname{Ob}_{P;v_1}^j=0\text{ for every }0\le j<r-1.
\tag{8.14b}
$$

By (8.12), $\operatorname{Ob}_{P;v_1}^j\simeq H^{j+1}(C_P\otimes_Ak)$. Thus the individual
presentations depend on the first direction, but their simultaneous vanishing does not.
Indeed, after all unit entries have been split, the differentials of the residual minimal
complex vanish modulo $\mathfrak n$. Its lower residual cohomology is therefore exactly its
collection of lower modules. Vanishing in every degree below $r$ deletes those modules and
leaves a finite free module in degree $r$. Conversely, top-degree concentration kills every
group in (8.14a). Thus (8.14a), rather than all individual ordered edge kernels, is the exact
joint obstruction family. Proposition 8.2 gives one cancellation-free way to make it vanish.

If the companion total cube is the strict perfect adjoint dual with the one shift in every
direction, then

$$
C_P^-\simeq R\operatorname{Hom}_A(C_P^+,A)[-|P|]\simeq N_P^\vee,
\qquad C_P^+=C_P.
$$

Thus the primary survives in cohomological degree $|P|$ and the adjoint norm companion in
degree zero, exactly as in the one-place convention; no second mixed vanishing is needed.
Separate facewise pairings do not suffice: their compatibility with every cubical sign and
quotient map is part of $({\rm CUBE}_P)$.

For $r=2$, the first induced residual map is exactly (8.4), so Proposition 8.2 says that the
only new homological assertion after the raw one-prime edges have been split is
$\operatorname{Ob}_{v,w}=0$. For $r\ge3$, the exact higher assertions are the joint groups
(8.14a). Under the cancellation-free ordered certificate, the next kernel is a degeneracy map
on a **double-new quotient**, and later kernels live on the corresponding iterated-new
quotients. Thus pairwise vanishing on the original carrier cannot be substituted either for
(8.14a) or for the stronger recursive condition in Proposition 8.2.

There is nevertheless a proved generic reduction. After extending the fraction field
so that the relevant finite Hecke blocks split, Book 125 gives, at every vertex,

$$
H^1[\Pi]\simeq
W_\Pi\otimes
P_\Pi^{P}\otimes
\bigotimes_{v\in P}\Pi_v^{K_{v,\epsilon_v}},
\tag{8.14c}
$$

where $P_\Pi^{P}=\bigotimes_{u\notin P}\Pi_u^{K_u}$ is the fixed spectator factor and the
two-dimensional global multiplicity module $W_\Pi$ occurs **once**. The level maps
at $v$ act only on the $v$-factor. In a typed row the displayed invariant space is replaced by
the corresponding local type-Hom factor; restricted tensor factorization and the conclusion
are unchanged. Define the explicit common global carrier

$$
G_{\Pi,P}=W_\Pi\otimes P_\Pi^P.
\tag{8.14c'}
$$

It is inserted once, while the $D_{\Pi,v}$ below are genuinely local factors. Thus the packet
block of the total cube is

$$
C_P[\Pi]_E\simeq
G_{\Pi,P}\otimes
\operatorname{Tot}\!\left(\boxtimes_{v\in P}D_{\Pi,v}\right),
\tag{8.14d}
$$

with $D_{\Pi,v}$ the local two-term old--new incidence complex. Under the applicable
one-place hypotheses each $D_{\Pi,v}$ is concentrated in degree one, or is acyclic when the
packet is old in that direction. The field-valued Kunneth theorem therefore puts (8.14d) in
degree $|P|$, or makes it zero. Consequently

$$
H^i(C_P)\otimes_{\mathcal O}E=0\qquad(i<|P|).
\tag{8.14e}
$$

So every lower integral homology group is $\varpi$-power torsion. For coefficient reduction
alone, the universal-coefficient sequence over the DVR is

$$
0\longrightarrow H^i(C_P)\otimes_{\mathcal O}k
\longrightarrow H^i(C_P\otimes_{\mathcal O}^Lk)
\longrightarrow
\operatorname{Tor}_1^{\mathcal O}(H^{i+1}(C_P),k)
\longrightarrow0.
\tag{8.14f}
$$

This is the coefficient-change sequence of Book 7a, Section 11.3. When the common face base is
$\mathcal O$, it describes the residual mixed groups. For a
larger local face algebra $A$, however, the groups used in (8.14a) are
$H^i(C_P\otimes_A^Lk)$ and are governed by the full hyper-Tor spectral sequence over $A$;
(8.14f) alone neither identifies them nor proves projectivity over $A$. Thus characteristic-zero
restricted tensor factorization proves the lower $\varpi$-power-torsion statement, but killing
that torsion and every face-algebra Tor shadow remains the integral mixed-Ihara assertion.

At two places and after all character and auxiliary variables have actually been specialized
to the coefficient DVR, the remaining assertion has a sharper form.

**Proposition 8.2A (the exact DVR mixed-saturation criterion).** Let
$A=\mathcal O$ be a DVR and suppose all four aggregate edge maps of the two-place square are
split injections. In the top vertex put

$$
U=\operatorname{im}(d_{v\mid1}),\qquad
V=\operatorname{im}(d_{w\mid1}),\qquad
L=\operatorname{im}(d_vd_w)=\operatorname{im}(d_wd_v),
\tag{8.14g}
$$

with the powers of two in the sources understood. If
$C_{v,w}^+\otimes_{\mathcal O}E$ has no cohomology below degree two, then

$$
H^0(C_{v,w}^+)=H^1(C_{v,w}^+)=0,
\qquad
Q_{v,w}:=H^2(C_{v,w}^+)=M_{11}/(U+V),
\tag{8.14h}
$$

and there is a canonical isomorphism

$$
\operatorname{Ob}_{v,w}
\simeq
\operatorname{Tor}^{\mathcal O}_1(Q_{v,w},k)
\simeq Q_{v,w}[\varpi].
\tag{8.14i}
$$

Consequently the following conditions are equivalent:

$$
\operatorname{Ob}_{v,w}=0;
\quad Q_{v,w}\text{ is }\mathcal O\text{-torsion-free};
\quad U+V\subset M_{11}\text{ is saturated}.
\tag{8.14j}
$$

**Proof.** The usual intersection description gives

$$
H^1(C_{v,w}^+)=(U\cap V)/L.
$$

The lower and upper edge splittings make $L$ a direct summand of both $U$ and $V$.
Hence $(U\cap V)/L$ is torsion-free: if $\varpi x\in L$ with
$x\in U\cap V$, saturation of $L$ in $U$ gives $x\in L$. Generic concentration makes this
same module torsion, so it is zero. The degree-zero assertion follows from either split first
edge. The universal-coefficient sequence (8.14f) now identifies the residual degree-one
cohomology with $\operatorname{Tor}_1^{\mathcal O}(Q_{v,w},k)$. Over a DVR this is
$Q_{v,w}[\varpi]$. Finally, the cokernel of the inclusion
$U+V\subset M_{11}$ is torsion-free exactly when that inclusion is saturated. $\square$

**Commuting-old-projector criterion.** There is also a sharp positive criterion which does not
use generic concentration. Retain the split-edge notation and hypotheses of Proposition 8.2A except for generic concentration.
Suppose there are commuting idempotents
$e_v,e_w\in\operatorname{End}_{\mathcal O}(M_{11})$ with images $U,V$ and

$$
\operatorname{im}(e_ve_w)=L.
\tag{8.14j'}
$$

Then $e_ve_w$ is the projector onto $U\cap V$, while
$e_v+e_w-e_ve_w$ is the projector onto $U+V$. Hence $U\cap V=L$, the sum $U+V$ is a direct
summand, and the total square is homotopy equivalent to the finite free module
$M_{11}/(U+V)$ in degree two. In a unit-Gram range the one-place formula
$d_v(d_v^*d_v)^{-1}d_v^*$ supplies candidate old projectors, but invertibility of the two
Gram operators separately proves neither that these projectors commute on the common top
vertex nor that their product has image $L$. Those are precisely the cubical hypotheses which
the countermodel below is allowed to violate. On Book 84's common definite degeneracy cube,
the placewise Gram formula and disjoint-place commutation verify them when both coordinate
Gram operators are units on every required face. Thus the criterion genuinely proves mixed
exactness in that unit-Gram range; it does not settle the nonunit faces for which the
level-raising congruence is being detected.

Thus, over the final coefficient DVR, an honest proof of mixed-Ihara vanishing is exactly an
integral **sum-of-old-images primitivity theorem**. Edgewise primitivity and generic packet
factorization do not prove it. Here is a countermodel retaining both of those facts. Let
$\mathcal O$ have uniformizer $\varpi$, let the two top edge sources be $\mathcal O^6$, and
let the top vertex be $\mathcal O^8$ with basis $e_1,\ldots,e_8$. Embed the first source as

$$
U=\langle e_1,e_2,e_3,e_4,e_5,e_6\rangle
$$

and the second as

$$
V=\langle e_1,e_2,e_3+\varpi e_7,e_4,e_5,e_6+\varpi e_8\rangle.
\tag{8.14k}
$$

Both are direct summands. Take the common lower image
$L=\langle e_1,e_2,e_4,e_5\rangle$ and use the corresponding coordinate split injections
from $\mathcal O^4$ into both top sources. The resulting incidence square commutes and every
edge is split. Integrally, $U\cap V=L$, whereas

$$
M_{11}/(U+V)\simeq(\mathcal O/\varpi)^{\oplus2}.
\tag{8.14l}
$$

The total complex is acyclic after inverting $\varpi$, but modulo $\varpi$ the two top images
coincide in dimension six and the mixed obstruction has dimension two. This is the exact
torsion phenomenon that a several-place geometric theorem must exclude. It also shows why
the field-valued counterexample in Section 8.1 is not the only issue: even generic
top-degree concentration plus integral splitting of every edge leaves a mixed saturation
defect.

There is nevertheless an unconditional finite-level carrier for characteristic-zero
questions. It does not assert mixed exactness and does not commute silently with nonflat
coefficient changes.

**Proposition 8.2B (the canonical torsion-free joint carrier).** Let $C_P^+$ be one actual
finite free $\mathcal O$-valued global incidence cube and put $r=|P|$. Define

$$
Q_P=H^r(C_P^+)
=C_P^{+,r}/\operatorname{im}(d^{r-1}),
\qquad
Q_P^{\rm tf}=Q_P/Q_P[\varpi^\infty],
\tag{8.14m}
$$

and, on the strict adjoint side,

$$
K_P^-=ker\!\left(
(d^{r-1})^\vee:(C_P^{+,r})^\vee
\longrightarrow(C_P^{+,r-1})^\vee
\right).
\tag{8.14n}
$$

Then $Q_P^{\rm tf}$ and $K_P^-$ are finite free over $\mathcal O$, and evaluation gives a
canonical perfect pairing

$$
Q_P^{\rm tf}\times K_P^-\longrightarrow\mathcal O.
\tag{8.14o}
$$

The module $Q_P^{\rm tf}$ is stable for the primary Hecke action, while $K_P^-$ is stable for
the adjoint action and evaluation intertwines the two by the declared adjoint involution.
After extending to a splitting field, their packet blocks are the top cohomology of
(8.14d) and its adjoint dual. In particular the common factor
$G_{\Pi,P}=W_\Pi\otimes P_\Pi^P$ occurs once, not once for every member of $P$.

**Proof.** The first module in (8.14n) is a submodule of a finite free module over a DVR, so
it is finite free. Left exactness of $\operatorname{Hom}_{\mathcal O}(-,\mathcal O)$ gives

$$
K_P^-\simeq\operatorname{Hom}_{\mathcal O}(Q_P,\mathcal O).
$$

The structure theorem over a DVR identifies this with the dual of $Q_P^{\rm tf}$ and makes
evaluation perfect. Functoriality gives Hecke stability. Torsion dies after inverting
$\varpi$, so (8.14d) identifies the generic packet blocks and retains its single global
multiplicity factor. $\square$

Proposition 8.2B is not a substitute for $({\rm MIX}_P)$ in a patched or universal
coefficient argument: formation of torsion-free quotient and of a kernel need not commute
with a nonflat character or diamond quotient. It is, however, an actual common global
finite-level carrier on which a pointwise characteristic-zero comparison can be attempted.
It is constructed from the joint cube before reciprocity is invoked and avoids any tensor
product of full one-place global cohomology complexes.

There is one stronger certificate under which mixed exactness really is formal. Suppose one
common base $A$, one finite projective common global carrier $G_P$, and local-factor complexes
$L_v$ have been constructed, together with an independently proved quasi-isomorphism

$$
C_P
\simeq
G_P\otimes_A^LL_{v_1}\otimes_A^L\cdots\otimes_A^LL_{v_r},
\tag{8.15}
$$

and $L_v\simeq N_v[-1]$ with every $N_v$ finite projective over that same $A$. Then (8.15)
immediately gives

$$
C_P
\simeq
\left(G_P\otimes_AN_{v_1}\otimes_A\cdots\otimes_AN_{v_r}\right)[-|P|].
\tag{8.16}
$$

If $G_P$ and the $N_v$ are projective only over different bases, the Künneth spectral sequence
instead contains their cross-Tor groups; projectivity over one base does not imply projectivity
over another. Book 140, Section 14.2 records the corresponding conditional external-product route.
Neither Book 140 nor the one-prime projectivity theorem constructs (8.15) for the actual global
automorphic cube. Therefore a definition of the cubical datum must not include (8.15) and then
list mixed exactness as though it were a second independent consequence: either (8.15) and the
common-base projectivity are proved, in which case mixed exactness follows formally, or the
successive quotient-new injectivities of Proposition 8.2 must be proved directly.

Here $L_v$ in (8.15) cannot silently be replaced by the full global one-prime cohomology
complex. On a packet which is new at every member of $P$, the latter contains the common
multiplicity factor $W_\Pi$. Tensoring $r$ such global complexes over the coefficient field produces
$W_\Pi^{\otimes r}$, whereas (8.14d) contains only one copy of $W_\Pi$. Already when
$\dim W_\Pi=2$ and $r=2$ the proposed tensor has a rank-four $W_\Pi^{\otimes2}$ multiplicity
factor while the actual joint block has the rank-two factor $W_\Pi$. A valid external-product
theorem must therefore be relative to an explicit common global carrier or must use the local
factors $D_{\Pi,v}$ with the global multiplicity inserted once. Mere agreement of the
coefficient ring $A$ is not a common-base theorem of this strength.

### 8.5 Product residue is a derived comparison

Mixed exactness concerns the automorphic incidence cube. The product-residue problem concerns
a different cube: the normalization, graph, component, and branch-correction complexes of the
semistable models. The Tor groups of these two cubes must not be identified.

There is no literal multi-node fiber over the original arithmetic base merely because the
active places are distinct. In fact this is not just an omission from the preceding source
chain. If $v\ne w$ are closed points of $\operatorname{Spec}\mathcal O_F$, their ideals are
comaximal and

$$
\operatorname{Spec}k(v)\times_{\operatorname{Spec}\mathcal O_F}
\operatorname{Spec}k(w)=\varnothing.
\tag{8.16a}
$$

Thus a curve over an open of $\operatorname{Spec}\mathcal O_F$ has separate $v$- and
$w$-fibers, not a closed stratum on which both nearby-cycle functors can be iterated. Book
122 constructs the semistable model over one of those traits while every other active level is
a spectator. A higher-dimensional interpolation with independent parameters
$t_v,t_w$ could have a common closed stratum, but constructing it and comparing its coordinate
traits with the arithmetic models would itself be a new theorem. It cannot be denoted into
existence as an ``actual arithmetic multi-node model.''

The intrinsic arithmetic replacement is an iterated inner-form-switching cube. Let $B$ be
the one-split-place quaternion algebra, let $\tau$ be its split real place, and assume every
member of $P$ is split in $B$. For $I\subseteq P$ there is a unique quaternion algebra $B_I$
with ramification set

$$
\operatorname{Ram}(B_I)
=\operatorname{Ram}(B)\mathbin\triangle I
\mathbin\triangle
\begin{cases}
\{\tau\},&|I|\text{ odd},\\
\varnothing,&|I|\text{ even}.
\end{cases}
\tag{8.16b}
$$

The parity is correct at every vertex. Even vertices are again split at $\tau$ and carry
curves; odd vertices are totally definite. An edge $I\to I\cup\{v\}$ toggles exactly $v$
and $\tau$, which is the one-prime switch of Book 140, read in the reverse direction by its
adjoint when necessary. Formula (8.16b) proves that the **final inner form** is independent of
the order. It does not prove that the integral edge maps commute.

**Proposition 8.2C (generic packet Beck--Chevalley).** Suppose every edge of (8.16b) lies in
Book 140's packet-comparison range and all component routes have been fixed. After extending
the fraction field to split the finite packet blocks, the two paths around every face carry a
packet to the same packet on $B_{I\cup\{v,w\}}$. Thus

$$
({\rm BC}_{v,w})_E
\quad\text{on packet labels and generic supports.}
\tag{8.16c}
$$

and on every curve vertex the global multiplicity module occurs once.

**Proof.** Away from $v,w,\tau$ neither path changes the packet. The finite local changes at
$v$ and $w$ commute in the restricted tensor product, and the two toggles at $\tau$ cancel.
Quaternionic occurrence multiplicity one makes the resulting packet label unique. Book 125's
decomposition places
one $W_\Pi$ in each curve block; no tensor product of the two full one-place curve blocks is
formed. $\square$

It does not choose a canonical scalar between the two composite lattice maps and does not
construct a chain homotopy. The integral Beck--Chevalley theorem required here is the
following exact geometric assertion. Construct one routed perfect object
$\mathcal G_I$ for every $B_I$, one integral residue/switch map on every edge, and, for every
two-face, a quasi-isomorphism between the two composite functors

$$
b_{I;v,w}:\operatorname{Res}_w\operatorname{Res}_v(\mathcal G_I)
\xrightarrow{\sim}
\operatorname{Res}_v\operatorname{Res}_w(\mathcal G_I),
\tag{8.16d}
$$

compatible with the coefficient-one extreme maps, Néron component modules, branch Smith
modules, adjoints, and component routes. The two-face comparisons must be normalized under
reversal and commute on disjoint faces; on every three-face they must satisfy the usual braid
coherence. These relations make the endpoint comparison independent of a word in adjacent
transpositions in the homotopy $2$-category. They do not, by themselves, construct a
homotopy-coherent higher cube in a chosen chain model. If the comparisons in (8.16d) are
represented by chain homotopies, a three-face also needs a specified degree $-2$ filler between
the two braid homotopies, and four or more directions require the analogous fillers for all
higher permutohedral boundaries. Equality of the composites in the derived category does not
choose those fillers.

The complete two-face, braid, and higher-filler system is the iterated-switch
Beck--Chevalley datum $({\rm IBC}_P)$ used below. Book 7a, Sections 11.1 and 12.3 proves
functoriality under pasting and the formal derived comparison once the cartesian squares and
their higher base-change maps have been supplied. Books 22 and 122 give the individual
coordinate objects, and Book 140 gives conditional coordinate switches. The application
therefore requires in addition the routed system (8.16d), with its integral residue
normalization, branch and component terms, and coherence in every required dimension; the
abstract Beck--Chevalley assembly applies only after these data have been constructed.

For each $v\in P$, let $K_v^{\rm comp}$ be the strict one-place component complex and write

$$
\rho_v:S_v^{\rm comp}\longrightarrow T_v^{\rm comp}
\tag{8.17}
$$

for its extreme residue arrow. The full complex retains the coefficient-one extreme residue,
the Néron component module, and the normalized-branch Smith correction. Let
$K_P^{\rm geom}$ be the corresponding total component object supplied either by
$({\rm IBC}_P)$ or by a separately constructed higher-dimensional comparison model, and write
$\rho_P^{\rm geom}:S_P^{\rm geom}\to T_P^{\rm geom}$ for the corresponding connecting map in
$K_P^{\rm geom}$. Here $S_v^{\rm comp},T_v^{\rm comp},S_P^{\rm geom}$, and
$T_P^{\rm geom}$ mean the full derived source and target objects with the component and branch
correction pieces retained, not merely their extreme graded modules. After compatible
orientations and component routing have been chosen, require all displayed source and target
objects to be perfect over the common base $A$.

There is a second common-base requirement before tensoring. The symbols
$S_v^{\rm comp},T_v^{\rm comp}$ in the next display must be verified **local relative
factors**, with the common global packet, spectator, and component carrier removed and then
inserted only once in the product. If instead they are the full global one-place component
objects, their tensor product duplicates that common carrier exactly as in the rank warning
after (8.16). In that case (8.18) must be replaced by a proved relative tensor product over an
explicit common global component algebra. Perfectness over the coefficient ring $A$ alone does
not supply this factorization. Subject to that requirement, and suppressing the one common
carrier from the notation, the local arrows define

$$
S_P^{\rm loc}
=S_{v_1}^{\rm comp}\otimes_A^L\cdots\otimes_A^LS_{v_r}^{\rm comp},
\qquad
T_P^{\rm loc}
=T_{v_1}^{\rm comp}\otimes_A^L\cdots\otimes_A^LT_{v_r}^{\rm comp},
\qquad
\rho_P^{\rm loc}=\rho_{v_1}\otimes_A^L\cdots\otimes_A^L\rho_{v_r}.
\tag{8.18}
$$

A simultaneous residue theorem must construct Beck--Chevalley comparison quasi-isomorphisms

$$
\beta_P^S:S_P^{\rm loc}\xrightarrow{\sim}S_P^{\rm geom},
\qquad
\beta_P^T:T_P^{\rm loc}\xrightarrow{\sim}T_P^{\rm geom}.
\tag{8.19}
$$

The exact comparison defect is the derived morphism

$$
\delta_P^{\rm res}
=\beta_P^T\circ\rho_P^{\rm loc}
-\rho_P^{\rm geom}\circ\beta_P^S
\in\operatorname{Hom}_{D(A)}(S_P^{\rm loc},T_P^{\rm geom}).
\tag{8.20}
$$

Product residue is precisely the assertion that (8.19) exists with the correct component
routing and orientations and that $\delta_P^{\rm res}=0$, with a coherent chain homotopy when
the comparison is used inside a larger cube. Nodewise coefficients $1$ and $-1$ determine the
coordinate maps but do not construct (8.19) or kill (8.20).

Even the generic packet Beck--Chevalley statement (8.16c) cannot kill this integral defect.
For a minimal countermodel, take a DVR $\mathcal O$ and $k=\mathcal O/\varpi$. The object
$k$ is perfect over $\mathcal O$, and

$$
\operatorname{Hom}_{D(\mathcal O)}(k,k[1])
=\operatorname{Ext}^1_{\mathcal O}(k,k)\simeq k.
\tag{8.20a}
$$

A nonzero class in (8.20a) becomes zero after tensoring with $E$. Hence two composites can
agree generically, and can even have the same maps on their extreme ordinary tensor factors,
while differing by a nonzero integral derived class. The Néron and branch-Smith torsion in
the arithmetic complex provides exactly the kind of target in which such a class can live.
Thus $({\rm IBC}_P)$ must kill the derived class, not merely identify the final packet or inner
form.

The derived tensors in (8.18) are essential. For example, over $A=k[[t]]$ one has

$$
\operatorname{Tor}_1^A(k,k)\simeq k.
\tag{8.21}
$$

Indeed, tensoring the free resolution
$0\to A\xrightarrow{t}A\to k\to0$ with $k$ makes its differential zero.
Thus even two identity maps on coefficient-one copies of $k=A/(t)$ have a derived product with
a nonzero additional term. An ordinary tensor product would erase it. In the arithmetic
application the analogous terms can be built from the Néron component modules and the branch
Smith modules. They are genuine semistable intersection data. They are not the unwanted mixed
homology of the automorphic new cube, and they may be set to zero only when an explicit
Tor-independence theorem says so.

A one-place residue theorem compares only one coordinate edge of the switching cube and
therefore does not construct (8.19). Hence $({\rm PROD}_P)$, equivalently the
residue-compatible part of $({\rm IBC}_P)$, is a genuinely several-place theorem even after
$({\rm MIX}_P)$ has been proved. A literal simultaneous-fiber formulation is unavailable on
the original arithmetic base by (8.16a).

### 8.6 A genuinely joint support criterion

Once a finite projective top carrier $M_P$ has been constructed, the formal support argument is
short. Book 145, Sections 11.1--11.4 proves the general support--annihilator and associated-prime
formalism used below; the additional arithmetic hypothesis is occurrence on a specified
product component. Let $R_P$ be the
represented product deformation ring and regard $M_P$ as its finite
module through the deformation action. If, for every irreducible
component $\Xi$ of $\operatorname{Spec}(R_P)_{\rm red}$, there is a prime
$\mathfrak q_\Xi\in\Xi$ such that

1. $\Xi$ is the only irreducible component through $\mathfrak q_\Xi$;
2. $(M_P)_{\mathfrak q_\Xi}\ne0$; and
3. $(M_P)_{\mathfrak q_\Xi}$ has depth $\dim(R_P)_{\mathfrak q_\Xi}$,

then the one-boundary support argument of Book 174 applies verbatim and gives

$$
\operatorname{Supp}_{R_P}(M_P)=\operatorname{Spec}R_P.
\tag{8.22}
$$

Indeed, failure to contain the generic point of $\Xi$ would make the localized support have
dimension smaller than the displayed depth. This contradicts
$\operatorname{depth}M\le\dim\operatorname{Supp}M$.

For the actual potential-modularity application, which asks about one named
characteristic-zero point rather than every point of $R_P$, full support is stronger than the
annihilator argument needs.

**Pointed joint-support lemma.** Let $x:R_P\to D$ be a map to a domain, let $M_P$ be a
finite $R_P$-module, and let $\mathbb T_P$ be the faithful image of $R_P$ on $M_P$. Suppose
there is an irreducible component $\Xi$ through $x$, with minimal prime
$\mathfrak p_\Xi\subseteq\ker x$, such that

$$
\mathfrak p_\Xi\in\operatorname{Supp}_{R_P}(M_P).
\tag{8.22a}
$$

Then $x$ factors canonically through $\mathbb T_P$. Under the same catenary/equidimensional
hypotheses used in the depth argument for (8.22), it is enough to verify the three conditions
preceding (8.22) at one unique-component prime $\mathfrak q_\Xi$ on this particular $\Xi$.

**Proof.** If $I=\operatorname{Ann}_{R_P}(M_P)$, condition (8.22a) says
$I\subseteq\mathfrak p_\Xi$. Hence

$$
I\subseteq\mathfrak p_\Xi\subseteq\ker x,
$$

so $x$ factors through $R_P/I=\mathbb T_P$. The depth argument used for (8.22), applied only
to $\Xi$, proves (8.22a). $\square$

This is still a genuinely simultaneous support assertion: $\Xi$ is the one global component
carrying the complete tuple of local labels at all members of $P$. It merely removes the
irrelevant demand to cover other product components when the downstream theorem has already
fixed one point. In particular, it does not follow from the separate projections of $\Xi$ or
from one-place support on unrelated carriers.

The hypotheses are joint. Surjectivity after projection to every one-place component set does
not imply them. A concrete reduced local example makes the failure visible. Let $k$ have
characteristic at least seven and put

$$
R=
k[[x,y]]/\bigl(xy(x-y)(x-2y)\bigr).
\tag{8.23}
$$

The four displayed linear factors are distinct primes, so this hypersurface is reduced.
Label its four branches by $(0,0),(0,1),(1,0),(1,1)$ in the order
$x,y,x-y,x-2y$. The module

$$
M=R/\bigl(x(x-2y)\bigr)
\tag{8.24}
$$

is supported on the two diagonal branches. Its support projects onto both labels in each
coordinate, but it misses both off-diagonal product components. Thus even projected support for
one common module is weaker than (8.22); separate one-prime support theorems on different
carriers are weaker still. Full support therefore requires a nonzero boundary class and the
maximal-depth comparison at every actual product component; another application of the
one-place lemma does not give these joint hypotheses.

There is a second, stronger formal certificate, but it makes the required comparison explicit.
For perfect complexes $E_1,\ldots,E_r$ over one noetherian ring $R$, residue-field Kunneth gives

$$
\operatorname{Supp}_R(E_1\otimes_R^L\cdots\otimes_R^LE_r)
=\bigcap_i\operatorname{Supp}_R(E_i).
\tag{8.24a}
$$

Indeed, after tensoring at a prime with its residue field, a tensor product of nonzero bounded
complexes of finite-dimensional vector spaces is nonzero. Hence joint support would be formal
if every one-place supported complex had first been pulled to the same product deformation
ring $R_P$, retained full support there, and an actual quasi-isomorphism from their relative
derived tensor to $C_P$ had been proved. Separate support over the different rings $R_v$, or an
ordinary tensor over the coefficient ring, satisfies none of those premises. Formula (8.24a)
therefore gives a valid common-base route but no pairwise-to-joint shortcut.

### 8.7 When joint augmentation is formal

There is also a sharp formal boundary for augmentation. Let

$$
\Delta_P=\prod_{v\in P_{\rm sc}}\Delta_v,
\qquad
\Lambda_P=\mathcal O[\Delta_P]
\simeq\bigotimes_{v\in P_{\rm sc}}\mathcal O[\Delta_v],
\tag{8.25}
$$

where the tensor product is over $\mathcal O$.

**Proposition 8.3 (strict joint ray quotient).** Let $P_{\rm sc}\subseteq P$ be finite. Fix a
protected set $S_0$ containing the entire active set $P$, the places above $\ell$, and every
place already ramified in the global datum. For each $v\in P_{\rm sc}$ there is a global character

$$
c_v:G_F\longrightarrow
\Delta_v=C_{e_v},\qquad e_v=\ell^{\operatorname{ord}_\ell(q_v-1)},
                                                               \tag{8.25a}
$$

whose localization at $v$ is the residue-unit quotient

$$
F_v^\times\longrightarrow k_v^\times
 \longrightarrow k_v^\times/(k_v^\times)^{e_v}\simeq C_{e_v},
                                                               \tag{8.25b}
$$

with a chosen uniformizer sent to $1$, and whose localization at every
$w\in S_0\setminus\{v\}$ is trivial. The product character

$$
c_P=(c_v)_{v\in P_{\rm sc}}:G_F\longrightarrow\Delta_P       \tag{8.25c}
$$

is surjective. For the least common multiple $\mathfrak f_P$ of its coordinate conductors,
it is therefore an effective quotient

$$
\operatorname{Cl}_{\mathfrak f_P}(F)\twoheadrightarrow\Delta_P.
                                                               \tag{8.25d}
$$

At every active place $w\in P\setminus\{v\}$ the character $c_v$ is trivial. At $v$, all
coordinates except $c_v$ are trivial and the completed field is
$F_v(\pi_v^{1/e_v})$ with vertical Kummer unit $1$. Every additional place in
$\mathfrak f_P$ is inserted in the fixed spectator datum, its local condition is transported
by the product twist, and all auxiliary sets are chosen disjoint from these places.

**Proof.** For a fixed $v$, prescribe (8.25b) at $v$ and the zero class at
$S_0\setminus\{v\}$. The exponent $e_v$ is odd, so Book 6, Theorem 6.1 and the non-Wang
alternative immediately following it globalize this tuple. Its order is exactly $e_v$
because its localization at $v$
has that order. At inertia over $v$, the combined character has image precisely the
$v$th coordinate subgroup of $\Delta_P$. Those coordinate subgroups generate $\Delta_P$,
proving surjectivity. Global reciprocity then factors (8.25c) through the ray class group of
its conductor, retaining all unit, sign, and central relations. Local Kummer theory gives
the asserted completed fields. $\square$

Coordinatewise, Book 122, Proposition 9.9 identifies the pullback of $c_v$ with the
automorphic determinant line by canonical component reciprocity. Tensoring those
identifications shows that the product line attached to (8.25c) is the actual trait-pulled
global coefficient system, not merely a product of local formulas.

Consequently, at the $v$-face every other scalar-ray coordinate is locally trivial and is a
genuine spectator, and the whole product ray is trivial at every non-scalar active place.
Book 122, Proposition 9.10 therefore applies to that face with precisely
the single strict local Kummer field in (8.25b), rather than an unspecified compositum of
several ramified ray characters.

Now suppose one actual untwisted component-routed cube $C_P^0$ and its companion have already
been constructed for the common product coefficient descent, and that every face is
equivariant for the tautological product character attached to (8.25c). Define the twisted
global datum by transporting the conditions at its additional conductor places as in the
proposition. The coordinate scalar twists commute and are trivial at the other active places.
Only on this supplied joint cube does iterating Book 174, Chapter 9 give the strict
product-twist identities

$$
R_P^{\rm tw}\simeq R_P^0\widehat\otimes_{\mathcal O}\Lambda_P,
\qquad
C_P^{\rm tw}\simeq
\Lambda_P\otimes_{\mathcal O}C_P^0,
\tag{8.26}
$$

with inverse product twist on the companion side. If the actual cube has already been
concentrated in a finite-free top module, the same identities hold for that top module,
pairing, deformation action, and named Hecke generators. Then joint fixed-prime augmentation
is formal. The twisted top module is free over $\Lambda_P$, so all positive augmentation Tor
vanishes. Coefficient extraction in the product group basis gives

$$
\mathbb T_P^{\rm tw}
\simeq\Lambda_P\otimes_{\mathcal O}\mathbb T_P^0.
\tag{8.27}
$$

Quotienting any subset of the tensor factors by augmentation therefore gives the corresponding
face, and the result is independent of the order. This is exactly the several-place analogue
of Book 174's one-place proof.

An arbitrary collection of separately chosen one-place ray quotients would not prove this: a
group can map onto each of two cyclic groups while its map to their product has only diagonal
image. Proposition 8.3 prevents that defect by imposing cross-local triviality before applying
the local--global theorem; inertia at the selected places then supplies every coordinate
subgroup. Without that simultaneous construction, the correct coefficient algebra would be
the group algebra of the actual image, not the tensor product in (8.25).

If $P_{\rm sc}$ is empty, the fixed-prime product-twist issue is vacuous. In particular, the
controlled places produced by splitting a generic base place remain in the distinct-root
regime; they do not create a scalar ray-quotient problem merely by becoming several places.
A joint ray quotient is needed only for the scalar subset that actually occurs after
specialization.

Auxiliary augmentation has a separate formal reduction. Under its ordered-distinct-root
hypotheses, Book 143, Section 10.3 applies with the represented product problem as its original
finite controlling set, so its functorial argument gives ring augmentation. For the
automorphic complexes one needs the full hypotheses used in Book 174, Proposition 9.1 at every
vertex: one common effective Taylor--Wiles $\Delta_Q$-torsor, the compatible ordered-root
idempotents and old/new comparison at $Q$, the required branchwise Galois and local--global
compatibility, and the fixed-place type hypotheses. If every face map is equivariant for that
same package, the regular cellular model and the auxiliary oldspace calculation give
objectwise, and coherently in all fixed-place directions,

$$
R_{P,Q}\widehat\otimes_{\mathcal O[\Delta_Q]}\mathcal O\simeq R_P,
\qquad
C_{P,Q}^{\pm}\otimes_{\mathcal O[\Delta_Q]}^L\mathcal O
\simeq C_{P,\varnothing}^{\pm}.
\tag{8.27a}
$$

Totalization commutes with this derived base change. If $({\rm MIX}_P)$ has already made the
top module projective over the same auxiliary algebra, its positive augmentation Tor also
vanishes and (8.27a) gives exact augmentation of the top module, action, and pairing. This is
an objectwise use of one global auxiliary package, not a tensor product of one-prime
cohomology complexes.
It still gives only the canonical quotient on faithful acting images until base faithfulness
is known.

Nor does exact augmentation of modules prove exact augmentation of faithful acting images.
For a minimal algebraic warning, take $A=k[[t]]$, $M=A^2$, and let one generator act by

$$
N=\begin{pmatrix}0&t\\0&0\end{pmatrix}.
\tag{8.28}
$$

The acting order generated by $1$ and $N$ is free of rank two over $A$, and $M$ is free over
$A$. After setting $t=0$, however, the actual acting image on $M\otimes_Ak$ consists only of
scalars, whereas the base change of the old acting order still has a nonzero square-zero
generator. Formation of the acting image has acquired a kernel. The auxiliary package imported
through Book 174 proves represented-ring, primary and companion complex, module, action,
pairing, and Tor-compatible augmentation for a clean one-active-place problem, but only a
canonical surjection on acting images. Book 175 proves that surjection injective from base
generic rigidity, equivalently from global reducedness and full base $R=T$, and its balanced
coherent patch proves that generic rigidity rather than assuming it. The same
two-surjection argument is formal for a finite active set once a full base equality for that
set has already been proved. Before such faithfulness is known, (8.28) shows that exact
acting-image augmentation is neither a consequence of module augmentation nor an input needed
for a direct finite-level reduced comparison: the base faithful order can instead be defined
anew on the augmented carrier.

### 8.8 The exact proved boundary

The formal reductions above settle what follows once one-prime hypotheses are granted.

- Once one common product coefficient system and all component routes are supplied, the
  underlying generic level cube and its adjoint companion are constructed formally from the
  global level tower. This does not construct an external-product comparison or the integral
  iterated-switch datum $({\rm IBC}_P)$. Distinct arithmetic fibers have empty intersection
  by (8.16a), so there is no literal multi-trait fiber on the original base.
- Raw one-prime split injectivity constructs the first quotient cube, but it does not prove
  injectivity on that quotient. For a pair, the first irreducible assertion is precisely
  $\operatorname{Ob}_{v,w}=0$. After specialization to the coefficient DVR, Proposition
  8.2A identifies this assertion exactly with saturation of the sum of the two top old images;
  the countermodel (8.14k)--(8.14l) shows that edgewise splitting and generic exactness do not
  imply that saturation. Commuting old projectors whose product is the lower composite do
  prove it, and a cubically compatible system of edge retractions proves all recursive
  quotient-new splittings. Book 84 supplies these compatibilities on its common definite cube
  in the fully unit-Gram range, but separate one-place projectors do not supply them on the
  nonunit level-changing faces.
- A genuine external-product quasi-isomorphism over one common base, together with the stated
  projectivity or cross-Tor vanishing, would prove mixed exactness formally. Such a
  quasi-isomorphism is additional several-place data and does not follow from one-prime
  projectivity. Restricted tensor factorization proves only the generic concentration
  (8.14e): the lower integral homology is $\varpi$-power torsion, while residual hyper-Tor over
  a larger face base remains to be controlled.
- Local coefficient-one residues identify the coordinate maps, but they do not construct the
  comparisons (8.19), kill the derived defect (8.20), or erase the component and branch Tor in
  (8.21). Formula (8.16b) constructs the parity-correct final inner forms and (8.16c) proves
  order independence of generic packet labels, while the torsion class (8.20a) shows why this
  does not imply integral derived Beck--Chevalley. Pairwise comparison maps and three-face
  endpoint braid identities still do not provide the higher fillers required to totalize a
  homotopy-coherent switch cube.
- Joint boundary nonvanishing and depth imply support formally by (8.22), but separate
  one-place support gives neither joint boundary witness. For one named downstream point, the
  pointed joint-support lemma requires only the one product component through that point, not
  every component of the product ring.
- Proposition 8.3 constructs the scalar product ray quotient; on an already constructed
  routed cube equivariant for it, the iterated strict twist gives (8.26)--(8.27). Arbitrary
  separately chosen ray quotients would not. A common auxiliary
  package satisfying the full
  vertexwise hypotheses of Book 174, Proposition 9.1 gives coherent complex and module
  augmentation by (8.27a), with only the stated acting-image quotient.

These are seven logically distinct assertions. Generic packet factorization controls
the rational packet block and inserts the global multiplicity once. Mixed sum-primitivity
kills an integral automorphic torsion class. Iterated-switch Beck--Chevalley transports the
component and branch complexes with higher coherence. The torsion-free pointed quotient gives
a smaller finite-level carrier without either of the preceding integral theorems. Simultaneous
augmentation produces the actual specialized cube from a supplied equivariant family but
neither its reciprocity map nor its support. Finite-set reciprocity supplies the
deformation-to-faithful-order surjection only
after all generic branches on that carrier have been checked. Finally, component occurrence
places the relevant carrier annihilator inside the prime of the named point. No one of these
assertions is a reformulation of another.

For a specialization-dependent active set, the finite-set criterion of Section 9.2 applies
only after constructing the common coefficient cube and proving its recursive mixed
vanishings, the product-residue comparison, and joint support. When scalar fibers
occur, Proposition 8.3 supplies the joint ray quotient and the strict twist is then formed on
that actual cube. Auxiliary augmentation is formal from one common package as above. Book 170
supplies finite-set reciprocity formally once one actual
joint carrier, every generic product branch has all simultaneous local labels and the integral
coefficient-prime realization, and exact trace/structural generation has been verified; its
reduced-order argument then supplies the all-Artinian local factorizations. Separate one-prime
reciprocity statements do not verify those joint hypotheses. These inputs give reduced $R=T$
and pointwise modularity; source reducedness or
another nilpotent-control theorem is still required for a full scheme-theoretic equality. A
validated ordered one-prime chain remains an alternative, but every intermediate carrier must
satisfy the complete one-prime hypotheses anew.

There is also a strictly smaller **pointwise finite-level route**. Proposition 8.2B constructs
the actual torsion-free top quotient $Q_P^{\rm tf}$ and its adjoint carrier directly from the
one global cube, with $W_\Pi$ inserted once. If the generic simultaneous branch labels on
that carrier are verified, Book 170 may then be applied to its faithful image; only after that
actual carrier and branch verification does $({\rm REC}_P)$ enter. The pointed support lemma
then factors one named characteristic-zero point as soon as the single global component
through it lies in the carrier support. This route neither proves $({\rm MIX}_P)$ nor commutes
the torsion-free quotient through a nonflat augmentation. Product residue is needed only if
it is the chosen method for identifying that component and proving its boundary witness.

For logical minimality, the final annihilator argument consumes only an actual finite
projective carrier over the named coefficient base, the relevant full or pointed support, and
reciprocity to its faithful order. Product residue is listed among the simultaneous hypotheses because it is the intended
geometric comparison that identifies the product component and transports the boundary data
used to prove joint support. If those labels and joint support are established independently,
the annihilator lemma does not use product residue a second time.

## 9. The finite-set application theorems

### 9.1 What iteration actually proves

Suppose a one-prime theorem is applied at $v$ and then at $w$. The second application is valid
only if every hypothesis is checked on the new intermediate carrier. In particular, one must
recheck the actual automorphic localization, $({\rm TIC})$ at the active place,
$({\rm TIH}_{\mathscr F})$, $({\rm SUP})$, reciprocity, and the applicable ray or auxiliary
augmentation datum with the new actual spectator tuple. If the step invokes constant saturation,
the component filtration, an extreme residue, lowering, or a switched carrier, the applicable
$({\rm AIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, and
$({\rm NU}_{\rm type})$ hypotheses must also be rechecked there. Reducedness is rechecked
only when a full ring equality, rather than pointwise modularity through the reduced
comparison, is required.

If those facts are independently available at each intermediate stage, iteration proves an
ordered chain of one-prime conclusions. It does not prove that the result is independent of
the ordering, and it does not identify that chain with the top homology of (8.1). A statement
that each place was clean in the original lower packet is insufficient because the first new
quotient changes the coefficient module seen at the second place.

For lowering, the order is even more visibly significant. Removing one level can expose
component torsion or a branch Smith class at another place. Thus a valid ordered argument must
record its actual intermediate modules, not merely the original local Galois restrictions.

This gives an exact ordered theorem: if an initial residual packet is automorphic and the
complete hypotheses of Theorem 7.1 or Theorem 7.1A, according to the local regime, hold
successively for an exhibited sequence of represented one-place changes, automorphy propagates
by induction. The conclusion belongs to that sequence; pairwise hypotheses at the initial
level do not prove it.

### 9.2 The hypotheses for a simultaneous theorem

For a finite set $P$, the intended simultaneous geometric construction requires one global
cubical carrier with all faces. The following hypotheses give its exact input; the bare
annihilator step has the smaller input just recorded in Section 8.8.

**Face hypotheses $({\rm FACE}_P)$.** Every actual face, with every spectator tuple and
auxiliary shadow, satisfies all applicable one-prime hypotheses in Section 6.1 and, for a
generic or vexing face, all clauses of Theorem 7.1A. This includes
both constant and type-Ihara families and the Book 125 routed-cover source condition whenever
the typed generic-residue conclusion is used; a condition verified only before another
quotient-new operation is not reused afterward.

**Cubical comparison $({\rm CUBE}_P)$.** The face maps come from one global automorphic level
cube, with strict commuting face maps, finite projective terms over the declared common base,
the primary--companion adjunction, and coherent comparison maps for every coefficient change
and subset of $P$. The level-tower argument preceding Proposition 8.2 constructs this cube once
one actual product coefficient descent and all component routes have been supplied. Proposition
8.3 supplies the scalar ray part of that descent, but not the simultaneous component routes.
This clause does not call the total
complex exact.
If mixed exactness is to be proved through (8.15), the external-product comparison must
separately be a quasi-isomorphism for one explicitly retained common global carrier and
local-factor or genuinely relative complexes; that carrier and their top modules must be
projective over the same common base, or all cross-Tor groups must vanish. Full global
one-prime complexes cannot be tensored over the coefficient ring because
that duplicates the common packet multiplicity, as (8.14c)--(8.14d) show. Abstract one-prime
complexes with matching ranks do not supply the required relative comparison.

**Mixed exactness $({\rm MIX}_P)$.** At every retained shadow, the primary total complex is
concentrated in degree $|P|$ and its top cohomology is finite projective over the face base.
For two places this includes $\operatorname{Ob}_{v,w}=0$ in (8.10). For three or more places
it is exactly the vanishing of the joint obstruction groups (8.14a). It may be proved by the
sufficient successive quotient-new injectivities of Proposition 8.2 or by an external-product
and higher-fold Tor-independent argument. Pairwise two-face vanishing on the original carrier
is not asserted to imply the higher conditions. When $({\rm CUBE}_P)$ gives
the strict cubical primary--companion adjunction used after Proposition 8.2, concentration on
the primary side gives the companion norm complex concentrated in degree zero with the dual
module; without that coherence both sides must be checked.

**Product residue $({\rm PROD}_P)$.** Since distinct closed arithmetic fibers have empty
intersection by (8.16a), first construct either a new higher-dimensional comparison object
with proved specialization maps to every arithmetic trait, or the parity-correct
$({\rm IBC}_P)$ system (8.16b)--(8.16d) of iterated residue and inner-form-switching functors.
The coefficient-one product of the local extreme residues is then the global connecting
morphism on that object: the comparison
$\beta_P^S,\beta_P^T$ of (8.19) is constructed with the correct orientations and component
routing, and the derived defect class (8.20) vanishes with the required cubical coherence in
every dimension. For a chain-level model this includes the specified three-face fillers and
all higher fillers described after (8.16d), not just pairwise equality in the derived category
or path independence of the endpoint. The derived tensor of the component complexes retains every
Néron component module and every branch Smith correction. These component Tor groups are
genuine semistable invariants and are not the same as unwanted Tor over the automorphic face
algebra.

**Joint support $({\rm JSUP}_P)$.** The patched total carrier, and every retained finite
quotient used in the conclusion, has full topological support over the corresponding global
deformation ring restricted to the entire named product of local components. In particular,
for the finite-level ring and total primary--companion carrier defined below, this means
$\operatorname{Supp}_{R_P}(M_P)=\operatorname{Spec}R_P$. Equivalently, one may prove the
patched assertion together with the exact residue-fiber comparison that carries nonvanishing
to each finite quotient. Full support after projection to every one-place factor, or merely
onto the local product base, is weaker: a module supported only on diagonal product components
can have surjective support under every projection, and distinct global components can lie
over the same local product component.

**Simultaneous augmentation $({\rm AUG}_P)$.** At scalar active places use the effective joint
global ray quotient of Proposition 8.3, with every local, unit, central, and archimedean
compatibility built in. Its strict product twist gives (8.26)--(8.27) for the
represented rings, total primary and companion complexes, top modules, pairings, actions, and
faithful orders; augmenting any subset of scalar factors gives the corresponding face and all
orders of specialization commute. Thus the scalar arithmetic part is constructed; the
auxiliary and cubical coherence clauses below remain separate.

At Taylor--Wiles primes, the represented rings, total primary and companion cubes, top modules,
actions, and pairings augment exactly, with zero positive diamond-algebra Tor and coherently
with every fixed-prime specialization. On the augmented carrier, the base faithful order
$\mathbb T_P$ is defined anew. Only the canonical surjection from the augmented auxiliary
acting order to $\mathbb T_P$ is used here. Its injectivity follows formally from a full base
$R_P=\mathbb T_P$ equality by the two-surjection argument of Book 175; it is not inferred from
module augmentation and is not required for the direct finite-level reduced comparison below.
It must be supplied separately only if one tries to descend an acting-order equality from a
patch before base faithfulness has been proved. Character quotients remain nonflat unless the
strict product-twist identities provide the stated free model.

**Finite-set reciprocity $({\rm REC}_P)$.** No new multi-place trace-descent theorem is needed
once the joint carrier exists. Book 170, Theorem 16.1 is already formulated for a finite
controlling set. In the standing absolutely irreducible, fixed-determinant setup, and retaining
its controlled-type and integral-comparison hypotheses, it proves the following implication.
If the faithful image on $M_P$ is
$\mathcal O$-torsion-free with reduced generic fiber, every generic factor is a noncharacter
weight-two packet in the attachment range, every one of those factors satisfies all the named
local conditions at all members of $P$ and the integral coefficient-prime condition, and the
verified universal trace and determinant coefficients together with the represented type,
line, sign, and diamond structural parameters map to and generate the whole finite faithful
order, then one Hecke-valued representation factors simultaneously
through every represented local condition and every Artinian quotient, and universality gives

$$
R_P\twoheadrightarrow\mathbb T_P.
\tag{9.0}
$$

Thus $({\rm REC}_P)$ is the verification of these hypotheses on the actual joint carrier, not
an additional Carayol-descent construction. Separate one-place carriers do not verify that
every generic factor of $\mathbb T_P$ has all local labels simultaneously, and trace generation
does not automatically include an adjoined line, sign, or diamond operator.

Let $R_P$ represent the resulting finite-level product deformation problem after the marked
augmentations, let $M_P$ be its total primary--companion carrier, and let $\mathbb T_P$ be the
faithful image on $M_P$.

**Theorem 9.1 (conditional finite-level finite-set nonminimal modularity lifting).** Assume
$({\rm FACE}_P)$, $({\rm CUBE}_P)$, $({\rm MIX}_P)$,
$({\rm PROD}_P)$, $({\rm JSUP}_P)$, $({\rm AUG}_P)$, and
$({\rm REC}_P)$. Then

$$
\boxed{(R_P)_{\mathrm{red}}\xrightarrow{\sim}\mathbb T_P.}
\tag{9.1}
$$

Every characteristic-zero point of $R_P$ is automorphic with the exact determinant,
coefficient-prime finite-flat condition, and named local data. At each nontrivial
scalar-character fiber with nonzero monodromy, the local conductor exponent is two.

For a tuple of scalar characters $(\chi_v)_{v\in P_{\rm sc}}$, “exact determinant” means
$\delta^{(1)}\prod_{v\in P_{\rm sc}}\chi_v^2$; no character direction is varied while the
determinant is held fixed. If, additionally,

$$
({\rm RED}_P):\qquad R_P\text{ is reduced},
\tag{9.2}
$$

then the canonical map $R_P\to\mathbb T_P$ is a full isomorphism.
Conversely, a full isomorphism forces $R_P$ to be reduced because the finite Hecke order is
reduced, so $({\rm RED}_P)$ is the exact finite-level criterion.

**Proof strategy.** The cubical hypotheses first construct a genuine integral finite-set
carrier without discarding mixed homology or Tor. Joint support and finite-set reciprocity
then put the problem in the exact situation of Lemma 6.1.

**Proof.** Hypotheses $({\rm CUBE}_P)$ and $({\rm MIX}_P)$ replace the total complex by its
finite projective top module. The product-residue hypothesis identifies its component labels,
and simultaneous augmentation supplies the finite-level carrier; its faithful image is then
defined directly on that carrier.
By $({\rm JSUP}_P)$ the carrier has support $\operatorname{Spec}R_P$. By
$({\rm REC}_P)$ there is a surjection from $R_P$ to its faithful Hecke image; the target is
reduced because it is torsion-free and embeds generically in a product of packet fields.
Lemma 6.1 gives (9.1).

A characteristic-zero point kills the nilradical and hence factors through $\mathbb T_P$.
The order-valued representation and type systems recover the automorphic representation and
its integral local data as in Chapter 7. Under (9.2), the reduced comparison is the full
equality. $\square$

The theorem is conditional on genuinely simultaneous assertions. It does not derive
$({\rm MIX}_P)$, $({\rm PROD}_P)$, or $({\rm JSUP}_P)$ from pairwise one-prime data.
At patched level, joint support alone again gives only containment of the carrier annihilator
in the nilradical. A patched reduced comparison requires the patched acting image to be
independently reduced; a full patched equality follows from reducedness of the patched source
or another theorem killing that annihilator. Neither assertion is part of the finite-level
theorem.

There is a smaller theorem for the actual downstream situation, where one
characteristic-zero point has already been named. It uses the honest joint carrier of
Proposition 8.2B and therefore does not tensor global one-place complexes.

**Theorem 9.2 (pointed finite-set lifting from the torsion-free top).** Work after every fixed
character used in the conclusion has been specialized to a coefficient DVR $\mathcal O$.
Let $x:R_P\to D$ be the characteristic-zero point to be lifted, with $D$ a domain. Assume the
following facts, in this order.

1. One actual component-routed global cube $C_P^+$ and its strict adjoint cube have been
   constructed at the final finite level. Put $M_{P,x}=Q_P^{\rm tf}$ and retain $K_P^-$ as
   its perfectly paired adjoint carrier, as in Proposition 8.2B. The primary carrier is
   nonzero.
2. On this one carrier, not on separate one-place carriers, the generic packet decomposition
   has been checked. Every generic factor retained by $M_{P,x}$ is a noncharacter
   weight-two packet in the attachment range and has simultaneously the named determinant,
   type, line, sign, monodromy, and local component at every member of $P$, together with the
   required integral coefficient-prime realization. The companion calculation on $K_P^-$ is
   identified with the primary one by the declared perfect pairing and adjoint involution; it
   is not inserted as a second copy of the primary deformation action. Every open condition
   asserted for the named point is also checked at $x$: in particular, at a special place the
   represented component is only the closure of the nonzero-monodromy locus, so a claimed
   special conductor requires that the monodromy entry ideal not be contained in $\ker x$.
3. Let $\mathbb T_{P,x}$ be the faithful image on this carrier. After the preceding carrier
   and branch verification, the trace, determinant, and structural generators satisfy the
   hypotheses of Book 170. Thus finite-set reciprocity gives the surjection
   $R_P\twoheadrightarrow\mathbb T_{P,x}$.
4. There is an irreducible component $\Xi_x$ through $x$ whose generic point belongs to
   $\operatorname{Supp}_{R_P}(M_{P,x})$.

Then $x$ factors through $\mathbb T_{P,x}$ and is automorphic with all the named local data.

**Proof.** Proposition 8.2B constructs $M_{P,x}$ from the actual joint cube, makes it finite
free over $\mathcal O$, and shows packetwise that the global multiplicity module occurs once.
Only then does clause 3 apply Book 170 and make it an $R_P$-module with faithful image
$\mathbb T_{P,x}$. Clause 4 and the pointed joint-support lemma give

$$
\operatorname{Ann}_{R_P}(M_{P,x})
\subseteq\mathfrak p_{\Xi_x}\subseteq\ker x.
$$

Hence $x$ factors through the faithful image. Specializing its order-valued representation
and using the branch verification in clause 2 recovers the required automorphic packet and
local conditions. $\square$

Theorem 9.2 proves neither mixed exactness nor a ring equality. If the final cube is obtained
by scalar or Taylor--Wiles specialization rather than constructed directly, the applicable
part of $({\rm AUG}_P)$ must first produce that actual cube; torsion-free quotient formation is
not commuted formally through a nonflat augmentation. Likewise $({\rm PROD}_P)$ is required
when product residue is the method used to identify $\Xi_x$ and transport its boundary
witness, but it is not consumed again by the pointed annihilator argument. Thus Theorem 9.2 is
conditional on the actual joint-component occurrence in clause 4 and on the carrier-specific
branch verification required before clause 3. Under exactly those hypotheses its proof gives
the stated pointwise factorization and automorphy conclusion; it does not prove mixed exactness
or a ring equality.

### 9.3 The potential-modularity application

The immediate potential-modularity application produces a geometric specialization whose extra
semistable places are known only after the specialization has been chosen. Its lower residual
packet must then be moved to the exact local datum of the target Tate module.

The required input is consequently one of the following forms:

1. the direct finite-set package $({\rm IAV}_S)$ of Section 1.5 is constructed for the
   specialized target and its automorphic residual reference; or
2. the specialization has exactly one active place and satisfies every explicit hypothesis of
   the applicable one-prime conclusion in Chapter 7; or
3. an ordered finite chain is exhibited, and every one-prime hypothesis is verified anew at
   each intermediate level; or
4. the all-point simultaneous theorem, Theorem 9.1, is used after all of its displayed
   hypotheses have been independently proved for the actual specialization; or
5. for the one already named Tate-module point, the pointed form of Theorem 9.2 is used
   after constructing one actual final global cube, verifying simultaneous generic branch
   data and finite-set reciprocity on its torsion-free top carrier, and proving support on the
   one global component through that point.

Separate local cleanliness does not establish either simultaneous theorem. In particular,
Theorem 9.1 may not be cited as though (8.10), product residue, and joint support
followed from the one-prime sources. Theorem 9.2 does not require mixed saturation or product
residue unless those are used to construct or support its carrier, but separate one-place
occurrence still does not prove its pointed joint-support clause.
The direct route avoids both assertions. Theorem 1.1C and Proposition 1.1D construct its
local pair and synchronized residual systems. Proposition 1.1E explains why quotient-first
balanced patching does not suffice. Proposition 1.1G instead constructs the expanded sharp
source patch. Theorem 1.1C and Lemma 1.1F supply unique horizontal specialization; Theorem
1.1H consumes it to prove full desired and avoidance support and faithfulness. Its exact
downstream conclusion is module augmentation together with a
nilpotent finite-level kernel. Thus the direct route has no remaining component theorem and
does not require an acting-image saturation statement.

### 9.4 The FLT boundary

The FLT blueprint asks for modularity lifting when $F$ is totally real of even degree,
$\ell\ge5$ is unramified in $F$, the determinant is cyclotomic, and $S$ is a finite set of
places away from $\ell$. It imposes flatness above $\ell$ and, for $v\in S$, expresses the
tame restriction by the trace-two condition on the kernel
$J_v=\ker(I_v\to k(v)^\times)$. The bounded
package of this book covers the coefficient-prime range $\ell\ge7$ and only those instances
of the tame condition that have first been replaced by an exact represented condition with
all lines, signs, determinant, scalar character, and monodromy labels retained. This
finite-set blueprint range is therefore broader than Theorem 7.1 unless $|S|\le1$, an actual
verified one-prime chain is supplied, $({\rm IAV}_S)$ has been constructed, every hypothesis
of Theorem 9.1 has been proved, or for one named lift the pointed carrier, branch, reciprocity,
and support hypotheses of Theorem 9.2 have been proved.
The blueprint's residual hypothesis is modularity at level $\Gamma_1(S)$ and its conclusion
is modularity at that level; in the present language the corresponding compact localization,
transfer, and local antecedents must be supplied by $({\rm AUT}_v)$ in the one-place case or
$({\rm FACE}_P)$ and $({\rm REC}_P)$ in the finite-set case, rather than inferred from
residual traces alone.

For a selected scalar character $\chi$ whose target determinant must be cyclotomic, the
conductor-one base determinant is chosen as
$\delta^{(1)}=\epsilon_{\rm cyc}\chi^{-2}$ after the needed coefficient extension, so that
the $\chi$-fiber of (3.3) has determinant $\epsilon_{\rm cyc}$. One cannot keep every fiber
of a nontrivial scalar-twist family cyclotomic while also retaining the genuine twist
identity.

The one-prime theorem is nevertheless the correct local building block. It fixes the
Frobenius convention, distinguishes conductor-one level raising from conductor-two scalar
twisting, retains the determinant square, and identifies every hypothesis that must survive
in a chain. What remains for a simultaneous application of the blueprint depends on the
proof route. The geometric-cube route needs mixed integral control at finitely many
semistable places, joint support, and finite-set reciprocity. The direct Ihara-avoidance route
instead uses the paired finite-set local-ring comparison and synchronized residual
automorphic shadows proved in Section 1.5B and the sharp source patch of Section 1.5D.
Theorem 1.1C and Lemma 1.1F supply unique horizontal specialization. Theorem 1.1H consumes
that geometry to prove full support and faithfulness, then recovers the desired finite-level
module with nilpotent ring kernel.
Finite-level reduced $R=T$ suffices for characteristic-zero modularity; exact equality of the
acting image is the stronger optional conclusion of Corollary 1.1I and is not needed here.

For a theorem making **every** lift in the product problem automorphic, the full-support route
of Theorem 9.1 still requires the mixed and product-residue package used to construct its
projective family. For the one representation already supplied by the FLT or
potential-modularity application, Theorem 9.2 shows that the logically minimal simultaneous
gate is narrower: an actual final joint cube, its torsion-free top carrier, simultaneous
generic branch verification, finite-set reciprocity on that carrier, and occurrence of the
single product component through the point.

The ordered alternative requires that after each completed change the next actual automorphic
localization have support on the represented component of the named target, with its type and
reciprocity hypotheses reverified on that new carrier. The pointed cube instead requires the
single joint assertion

$$
\mathfrak p_{\Xi_x}\in\operatorname{Supp}_{R_P}(Q_P^{\rm tf}),
\tag{9.3}
$$

together with simultaneous branch verification before reciprocity. Thus these routes remove
the all-components demand, but do not by themselves prove the blueprint theorem. The direct
$({\rm IAV}_S)$ route removes this occurrence problem by proving patched component coverage
through the common special fiber; Theorem 1.1H proves its exact source-patched component
theorem under the displayed residual-image, local-factor, definite-module, and control
hypotheses.

## 10. Scope and conclusion

### 10.1 The direct finite-set theorem

The direct argument has a simple logical order. The prepared field first places every active
prime in the scalar tame chart while preserving the selected dyadic, coefficient-prime,
determinant, and ramification components. An actual automorphic reference or upper packet
then supplies a primitive definite eigenvector. Its nonzero reduction produces the common
residual localization from which both coefficient systems are built. No minimal point is
needed at this stage.

The desired and avoidance local rings have different generic geometry but the same residual
geometry. Theorem 1.1C gives their common nilpotent residual quotient, and Lemma 1.1F proves
that the avoidance source is a Cohen--Macaulay domain while the reduced desired source is
Cohen--Macaulay with unique horizontal specialization. This specialization theorem belongs
to the local geometry; it is an input to the support argument, not a consequence of support.

The global construction preserves that distinction. Book 143 selects one ordered family of
Taylor--Wiles primes from the common embedded residual functor and the complete strict-relative
defect formula. Book 152 constructs the desired and avoidance modules at each fixed
auxiliary set. Its varying-set theorem either uses uniform minimal control or passes to a
cofinal constant-rank family while retaining every marked finite shadow. Book 144 then
patches the two systems along one path. Their residual modules are compared only after base
change to the common nilpotent quotient, while their source actions, pairings, adjoints,
frames, and module coinvariants remain marked integrally.

Theorem 1.1H applies Book 145 to these paired sources. Equal depth and dimension force the
avoidance module to be faithful over the avoidance domain. Full residual support crosses the
common nilpotent quotient, and Lemma 1.1F's unique-horizontal specialization lifts that support
to every desired component. Reducedness then makes the desired source action faithful. The
finite-level conclusion passes through the intermediate ring
$R_\infty^{\rm des,raw}$: exact recovery of that ring and of the module gives a nilpotent
kernel in the finite Hecke action. Corollary 1.1B therefore makes the whole desired ring
finite and makes every characteristic-zero point automorphic. Exact augmentation of the
patched acting image is stronger and remains the optional conclusion of Corollary 1.1I.

The prepared criteria separate the two arithmetic uses of this theorem. Theorem 1.1J starts
with an automorphic avoidance reference packet over the auxiliary prepared field and descends
the desired packet when the selected-safe cyclic hypotheses hold. Theorem 1.1K starts with an
upper packet on the broad tame-unipotent problem. Its primitive transfer proves residual
nonvanishing, the source theorem makes the broad ring finite, and the quotient to the minimal
problem has finite special fibre. For a minimal point
$x:R_L^{\rm SP}\to E$, it is the composite

$$
R_L^{\rm uni}(P)\twoheadrightarrow R_L^{\rm SP}\xrightarrow{x}E
$$

that factors through the finite automorphic action. Finiteness is established before such a
point is chosen, so the construction is noncircular.

The normalizations used in this argument remain fixed throughout. Frobenius is geometric in
the deformation polynomials; the local matrix calculation explicitly inverts it when
arithmetic Frobenius is used. Scalar twisting changes the determinant by the square of the
character. The $h$ diamond variables are distinct from the $4m-1$ partial-frame variables,
and the strict-relative formula is evaluated before either family is added to the source.
These conventions give the equality of source dimensions on which the depth argument rests.

### 10.2 The geometric alternative

Geometric level change addresses a different problem. At one place its incidence complex
compares the two old maps with the new quotient. At several places the corresponding object
is a cube, and edgewise saturation does not control the intersections of old images. For two
places the first obstruction is the first homology of the incidence square; over the
coefficient DVR it is the torsion in the quotient by the sum of the two old images. Thus
primitivity of each old image separately does not imply the required primitivity of their
sum.

Higher-dimensional cubes introduce the analogous iterated-new homology and residual
hyper-Tor terms. A geometric proof for all points must also compare the integral residue
descriptions on different faces, retain their higher coherence, construct a joint carrier,
and prove support on every relevant product component. A proof for one named point can use
the torsion-free top of the actual cube and ask only for the component through that point,
but the carrier, its simultaneous branch labels, reciprocity action, and component occurrence
still have to be established on that same object.

These cubical conditions are neither consequences nor hypotheses of the direct source-patching
theorem. They become relevant only when modularity is transported by old--new geometry.
Conversely, the direct theorem does not prove mixed exactness or product residue; it avoids
them by patching the final desired and avoidance deformation problems from the outset. The
two methods therefore have complementary scopes. The geometric method follows level change
through an incidence cube, whereas componentwise Ihara avoidance proves whole-source support
through common residual geometry.

### 10.3 Final synthesis

At one changed place, nonminimal modularity lifting is governed by one incidence complex.
The two degeneracy maps identify the old lattice, the companion system records the integral
adjoint, nearby cycles supply the graph residue, and the represented local ring names the
desired component. Once the actual automorphic carrier, support, and reciprocity action have
been supplied, the annihilator argument identifies the deformation-to-Hecke kernel with the
nilradical. Characteristic-zero points therefore factor through the automorphic action.
Full scheme-theoretic equality requires the additional reducedness or equal-variable input
stated in the one-place theorem.

Several-place geometric level change replaces that incidence complex by a cube. Mixed
homology, product residue, higher coherence, and joint component support belong to this
geometric method because they control intersections among the old images. They are meaningful
and useful when one follows automorphic forms through successive level changes, but they are
not needed for componentwise Ihara avoidance. A pointed cube can reduce the support demand to
one global component, though it still requires an actual carrier carrying all local labels at
once.

The direct finite-set theorem starts from different geometry. Theorem 1.1C and Lemma 1.1F
give the paired local sources and prove unique horizontal specialization. Proposition 1.1G
constructs synchronized source patches after the full residual, defect, rank, and recovery
hypotheses have been verified. Theorem 1.1H consumes the local specialization theorem:
faithfulness over the avoidance domain transfers residual support to every desired horizontal
component, and reducedness gives faithfulness on the desired source. Module coinvariants and
the intermediate represented ring then produce a nilpotent finite-level kernel. Exact
acting-image augmentation is optional.

The prepared auxiliary criterion turns an actual avoidance reference packet into automorphy
of every desired characteristic-zero point over the prepared field and descends the resulting
packet under the selected-safe cyclic hypotheses. The prepared target criterion uses an
actual upper packet only to seed the common residual module. It proves the broad unipotent
ring finite before a minimal point is chosen. If
$x:R_L^{\rm SP}\to E$ is later produced, the composite

$$
R_L^{\rm uni}(P)\twoheadrightarrow R_L^{\rm SP}\xrightarrow{x}E
$$

factors through the finite automorphic action. Thus the same source patch supplies both the
finite special fibre used to locate a minimal point and the automorphy of that point.

The mathematical conclusion is therefore precise. One-place level change, several-place
cubical level change, and direct componentwise Ihara avoidance are distinct proof mechanisms.
The first studies one incidence complex, the second studies its higher intersections, and the
third transports whole-source support across common residual geometry. For the prepared
finite-set applications of this book, the third mechanism gives the required finiteness and
pointwise automorphy without any mixed cube, node comparison, type-Ihara input, or augmented
acting-image equality.
