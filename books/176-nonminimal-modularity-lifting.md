# Nonminimal Modularity Lifting

This volume is the modularity-lifting application of the one-prime comparison developed in
the preceding books. Its first output is a pointwise theorem: once an actual one-prime
automorphic carrier has the represented local condition, support, and reciprocity required
below, every characteristic-zero point satisfying the asserted open branch conditions is
automorphic; in particular, a special-conductor conclusion retains nonzero monodromy. Its
second output is the exact several-place interface needed when one place splits into many: either one verifies
an ordered chain of one-prime applications, or one supplies a genuinely joint cube. For the
joint route, mixed exactness, product residue through the integral iterated-switch
Beck--Chevalley datum, joint support, augmentation, and reciprocity remain distinct
hypotheses. For one named point, the torsion-free top of the actual final cube gives a smaller
carrier, but occurrence of the global component through that point is still required.

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
  - [9.3 The potential-modularity consumer](#93-the-potential-modularity-consumer)
  - [9.4 The FLT boundary](#94-the-flt-boundary)
- [10. Dependencies and conclusion](#10-dependencies-and-conclusion)
  - [10.1 Exact source ledger](#101-exact-source-ledger)
  - [10.2 Logical and normalization checks](#102-logical-and-normalization-checks)
  - [10.3 The first unresolved inputs](#103-the-first-unresolved-inputs)
  - [10.4 Final synthesis](#104-final-synthesis)

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
is reverified after every change of level.

For two places the automorphic object is a square, not two unrelated arrows. Its total
complex measures the intersection of the two old images. Edgewise saturation does not
determine that intersection. The first mixed kernel will be isolated in Chapter 8. It is a
conclusion that must be proved; it is not included in any definition of a locally admissible
place. In the downstream construction, one selected base place is required to split completely
in a totally real extension $F'/F$ of positive even degree. It already produces $[F':F]$
active places, with $[F':F]\ge2$, before any specialization-dependent bad places are added.
The several-place issue is therefore present even when no new bad reduction is discovered.

### 1.4 The application routes and their boundary

The application has four routes, and their hypotheses must not be exchanged. With one active
place, Theorem 7.1 applies to the scalar line-special family and Theorem 7.1A gives the
corresponding conditional generic or vexing application on an independently constructed
carrier. With several active places, a fully verified ordered chain applies those one-place
results successively. Theorem 9.1 is instead an all-point simultaneous theorem, conditional
on $({\rm FACE}_P)$, $({\rm CUBE}_P)$, $({\rm MIX}_P)$,
$({\rm PROD}_P)$, $({\rm JSUP}_P)$, $({\rm AUG}_P)$, and
$({\rm REC}_P)$; on the iterated-switch route $({\rm PROD}_P)$ includes the integral
Beck--Chevalley datum $({\rm IBC}_P)$. Finally, Theorem 9.2 treats one named point by using
the torsion-free top of the actual final cube and the pointed occurrence of the one global
component through that point.

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

The arithmetic inputs are not all presently theorems in the declared source chain. The core
finite-level comparison depends on the actual automorphic localization, the separate
type-incidence and type-Ihara hypotheses, the one-boundary support datum, and the exact
reciprocity order. The scalar family also uses an effective global ray quotient and strict
twist identities; Book 174 constructs the strict one-place quotient and Proposition 8.3 below
constructs the joint quotient, so their existence is no longer an external arithmetic input.
Using them still enlarges the fixed spectator datum by their actual conductor places. The
richer level-changing and component package additionally depends on a
finite family of abelian Ihara vanishings, primitive type residue, and typed node
uniformization when a switched carrier is used. The finite-set package further requires
vanishing of all mixed homology, a coefficient-one product-residue comparison, joint
component support, and simultaneous augmentation. The statements below never insert these
assertions into the word “clean” or into a local definition. The one-prime and finite-set
theorems are therefore stated with their exact conditional inputs.

For one already named characteristic-zero point there is a smaller finite-level interface.
The torsion-free top of the actual global cube is a canonical joint carrier even when mixed
torsion survives.  Pointwise modularity then needs simultaneous branch verification,
reciprocity on that carrier, and support on the single global component through the point.
This does not prove the stronger mixed, Beck--Chevalley, or all-component support theorems and
does not commute torsion-free quotient formation through nonflat augmentation.

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

| regime | arithmetic congruence | integral object | conclusion available before patching |
|---|---|---|---|
| generic unramified-to-special change | $q_v\not\equiv\pm1\pmod\ell$ | separated old roots and a signed one-prime Gram block | conditional level raising and integral curve--definite comparison from Book 140 |
| scalar tame twist | $q_v\equiv1\pmod\ell$ | enhanced line, sign, Book 174's strict global ray quotient $\Delta_v$, and $\Lambda_v=\mathcal O[\Delta_v]$ | Book 174's strict type complex under $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$, support under $({\rm SUP}_v)$, and exact twist augmentation; constant Ihara and primitive residue are separately required only for the corrected component filtration and extreme residue |
| vexing sign collision | $q_v\equiv-1\pmod\ell$ | full primary--companion block and full Gram matrix | one-prime block statements; no scalar $\ell$-power twist face |

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
character in item 3 is trivial, exactly as in Book 175, Section 2.2.  A broader datum may retain
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

This separation makes failure localizable. If constant abelian Ihara is missing, one stops
before using Book 139's corrected constant-coefficient filtration. If the typed parahoric
extension, type incidence, or type-Ihara is missing, one stops before forming the projective
typed new quotient. If a
one-prime support statement is available but a finite-set mixed kernel is not, one retains
the one-prime theorem and stops before a simultaneous finite-set conclusion.

## 4. The imported one-prime level-change package

Chapters 4--6 record the one-prime import boundary. Book 139 supplies the
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

The compatibility aliases in this chapter concern the scalar-residual line-special problem of
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

**Lemma 6.1 (full support and reduced image; compatibility alias).** This is Book 175,
Lemma 4.1. If $R$ is noetherian, $M$ is finite with full support, and the faithful acting image
$T$ is reduced, then

$$
\ker(R\twoheadrightarrow T)=\sqrt{(0)},\qquad R_{\rm red}\simeq T.
\tag{6.3}
$$

### 6.3 The reduced comparison and the full-equality criterion

**Theorem 6.2 (scalar line-special finite-level reduced $R=T$; compatibility alias).** Under
the six applicable inputs in Section 6.1, Book 175, Theorem 4.2 gives

$$
\boxed{(R^{\rm nm})_{\rm red}\xrightarrow{\sim}\mathbb T^{\rm nm}.}
\tag{6.4}
$$

The finite Hecke order is reduced because it is $\mathcal O$-torsion-free with semisimple reduced
generic fiber. No reducedness of an abstract patched acting image is inferred.

**Corollary 6.3 (full equality criterion; compatibility alias).** Book 175, Corollary 4.3 says
that the finite-level comparison is a full isomorphism exactly when the selected global source is
reduced. Local-chart reducedness and minimal $R=T$ do not imply that condition.

**Corollary 6.3a (balanced coherent scalar one-prime $R=T$; compatibility alias).** If the
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

**Theorem 7.1 (conditional scalar line-special modularity lifting; compatibility alias).** This
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
finite-level $R=T$ from the base one-prime ledger, and full patched and finite $R=T$ when the
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

No current one-prime source proves

$$
\operatorname{Ob}_{v,w}=0
\tag{8.10}
$$

uniformly for every geometric pair from Chapter 3 satisfying the explicit one-prime
hypotheses, every actual spectator tuple, every auxiliary shadow, and both primary and
companion systems. Equation (8.10) is the first finite-set gap.

### 8.4 Ordered quotient cubes and higher mixed classes

The two-place calculation has a finite-set version which is entirely formal once one actual
global cube has been constructed. It is useful to state it because it identifies exactly which
part is not supplied by the one-prime theorem.

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
are unchanged.  Define the explicit common global carrier

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

This is the coefficient-change sequence of Book 14, Section 11.3. When the common face base is
$\mathcal O$, it describes the residual mixed groups. For a
larger local face algebra $A$, however, the groups used in (8.14a) are
$H^i(C_P\otimes_A^Lk)$ and are governed by the full hyper-Tor spectral sequence over $A$;
(8.14f) alone neither identifies them nor proves projectivity over $A$. Thus characteristic-zero
restricted tensor factorization proves the lower $\varpi$-power-torsion statement, but killing
that torsion and every face-algebra Tor shadow remains the integral mixed-Ihara assertion.

At two places and after all character and auxiliary variables have actually been specialized
to the coefficient DVR, the remaining assertion has a sharper form.

**Proposition 8.2A (the exact DVR mixed-saturation criterion).**  Let
$A=\mathcal O$ be a DVR and suppose all four aggregate edge maps of the two-place square are
split injections.  In the top vertex put

$$
U=\operatorname{im}(d_{v\mid1}),\qquad
V=\operatorname{im}(d_{w\mid1}),\qquad
L=\operatorname{im}(d_vd_w)=\operatorname{im}(d_wd_v),
\tag{8.14g}
$$

with the powers of two in the sources understood.  If
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

**Proof.**  The usual intersection description gives

$$
H^1(C_{v,w}^+)=(U\cap V)/L.
$$

The lower and upper edge splittings make $L$ a direct summand of both $U$ and $V$.
Hence $(U\cap V)/L$ is torsion-free: if $\varpi x\in L$ with
$x\in U\cap V$, saturation of $L$ in $U$ gives $x\in L$.  Generic concentration makes this
same module torsion, so it is zero.  The degree-zero assertion follows from either split first
edge.  The universal-coefficient sequence (8.14f) now identifies the residual degree-one
cohomology with $\operatorname{Tor}_1^{\mathcal O}(Q_{v,w},k)$.  Over a DVR this is
$Q_{v,w}[\varpi]$.  Finally, the cokernel of the inclusion
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
integral **sum-of-old-images primitivity theorem**.  Edgewise primitivity and generic packet
factorization do not prove it.  Here is a countermodel retaining both of those facts.  Let
$\mathcal O$ have uniformizer $\varpi$, let the two top edge sources be $\mathcal O^6$, and
let the top vertex be $\mathcal O^8$ with basis $e_1,\ldots,e_8$.  Embed the first source as

$$
U=\langle e_1,e_2,e_3,e_4,e_5,e_6\rangle
$$

and the second as

$$
V=\langle e_1,e_2,e_3+\varpi e_7,e_4,e_5,e_6+\varpi e_8\rangle.
\tag{8.14k}
$$

Both are direct summands.  Take the common lower image
$L=\langle e_1,e_2,e_4,e_5\rangle$ and use the corresponding coordinate split injections
from $\mathcal O^4$ into both top sources.  The resulting incidence square commutes and every
edge is split.  Integrally, $U\cap V=L$, whereas

$$
M_{11}/(U+V)\simeq(\mathcal O/\varpi)^{\oplus2}.
\tag{8.14l}
$$

The total complex is acyclic after inverting $\varpi$, but modulo $\varpi$ the two top images
coincide in dimension six and the mixed obstruction has dimension two.  This is the exact
torsion phenomenon that a several-place geometric theorem must exclude.  It also shows why
the field-valued counterexample in Section 8.1 is not the only issue: even generic
top-degree concentration plus integral splitting of every edge leaves a mixed saturation
defect.

There is nevertheless an unconditional finite-level carrier for characteristic-zero
questions.  It does not assert mixed exactness and does not commute silently with nonflat
coefficient changes.

**Proposition 8.2B (the canonical torsion-free joint carrier).**  Let $C_P^+$ be one actual
finite free $\mathcal O$-valued global incidence cube and put $r=|P|$.  Define

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

**Proof.**  The first module in (8.14n) is a submodule of a finite free module over a DVR, so
it is finite free.  Left exactness of $\operatorname{Hom}_{\mathcal O}(-,\mathcal O)$ gives

$$
K_P^-\simeq\operatorname{Hom}_{\mathcal O}(Q_P,\mathcal O).
$$

The structure theorem over a DVR identifies this with the dual of $Q_P^{\rm tf}$ and makes
evaluation perfect.  Functoriality gives Hecke stability.  Torsion dies after inverting
$\varpi$, so (8.14d) identifies the generic packet blocks and retains its single global
multiplicity factor. $\square$

Proposition 8.2B is not a substitute for $({\rm MIX}_P)$ in a patched or universal
coefficient argument: formation of torsion-free quotient and of a kernel need not commute
with a nonflat character or diamond quotient.  It is, however, an actual common global
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
semistable models. The two Tor ledgers must not be merged.

There is no literal multi-node fiber over the original arithmetic base merely because the
active places are distinct.  In fact this is not just an omission from the preceding source
chain.  If $v\ne w$ are closed points of $\operatorname{Spec}\mathcal O_F$, their ideals are
comaximal and

$$
\operatorname{Spec}k(v)\times_{\operatorname{Spec}\mathcal O_F}
\operatorname{Spec}k(w)=\varnothing.
\tag{8.16a}
$$

Thus a curve over an open of $\operatorname{Spec}\mathcal O_F$ has separate $v$- and
$w$-fibers, not a closed stratum on which both nearby-cycle functors can be iterated.  Book
122 constructs the semistable model over one of those traits while every other active level is
a spectator.  A higher-dimensional interpolation with independent parameters
$t_v,t_w$ could have a common closed stratum, but constructing it and comparing its coordinate
traits with the arithmetic models would itself be a new theorem.  It cannot be denoted into
existence as an ``actual arithmetic multi-node model.''

The intrinsic arithmetic replacement is an iterated inner-form-switching cube.  Let $B$ be
the one-split-place quaternion algebra, let $\tau$ be its split real place, and assume every
member of $P$ is split in $B$.  For $I\subseteq P$ there is a unique quaternion algebra $B_I$
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

The parity is correct at every vertex.  Even vertices are again split at $\tau$ and carry
curves; odd vertices are totally definite.  An edge $I\to I\cup\{v\}$ toggles exactly $v$
and $\tau$, which is the one-prime switch of Book 140, read in the reverse direction by its
adjoint when necessary.  Formula (8.16b) proves that the **final inner form** is independent of
the order.  It does not prove that the integral edge maps commute.

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
construct a chain homotopy.  The integral Beck--Chevalley theorem required here is the
following exact geometric assertion.  Construct one routed perfect object
$\mathcal G_I$ for every $B_I$, one integral residue/switch map on every edge, and, for every
two-face, a quasi-isomorphism between the two composite functors

$$
b_{I;v,w}:\operatorname{Res}_w\operatorname{Res}_v(\mathcal G_I)
\xrightarrow{\sim}
\operatorname{Res}_v\operatorname{Res}_w(\mathcal G_I),
\tag{8.16d}
$$

compatible with the coefficient-one extreme maps, Néron component modules, branch Smith
modules, adjoints, and component routes.  The two-face comparisons must be normalized under
reversal and commute on disjoint faces; on every three-face they must satisfy the usual braid
coherence. These relations make the endpoint comparison independent of a word in adjacent
transpositions in the homotopy $2$-category. They do not, by themselves, construct a
homotopy-coherent higher cube in a chosen chain model. If the comparisons in (8.16d) are
represented by chain homotopies, a three-face also needs a specified degree $-2$ filler between
the two braid homotopies, and four or more directions require the analogous fillers for all
higher permutohedral boundaries. Equality of the composites in the derived category does not
choose those fillers.

The complete two-face, braid, and higher-filler system is the iterated-switch
Beck--Chevalley datum $({\rm IBC}_P)$ used below. Book 14, Sections 11.1 and 13.3 proves
functoriality under pasting and the formal derived comparison once the cartesian squares and
their higher base-change maps have been supplied. Thus the abstract Beck--Chevalley assembly
is not a missing theorem. Books 22 and 122 supply the individual coordinate objects, and Book
140 supplies conditional coordinate switches; what no source constructs is the
application-specific routed system (8.16d), with its integral residue normalization, branch
and component terms, and coherence in every required dimension.

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
For a minimal countermodel, take a DVR $\mathcal O$ and $k=\mathcal O/\varpi$.  The object
$k$ is perfect over $\mathcal O$, and

$$
\operatorname{Hom}_{D(\mathcal O)}(k,k[1])
=\operatorname{Ext}^1_{\mathcal O}(k,k)\simeq k.
\tag{8.20a}
$$

A nonzero class in (8.20a) becomes zero after tensoring with $E$.  Hence two composites can
agree generically, and can even have the same maps on their extreme ordinary tensor factors,
while differing by a nonzero integral derived class.  The Néron and branch-Smith torsion in
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

No one-place residue theorem constructs (8.19): it compares only one coordinate edge of the
switching cube. Hence $({\rm PROD}_P)$, equivalently the residue-compatible part of
$({\rm IBC}_P)$, is a genuinely several-place theorem even after $({\rm MIX}_P)$ has been
proved. A literal simultaneous-fiber formulation is unavailable on the original arithmetic
base by (8.16a).

### 8.6 A genuinely joint support criterion

Once a finite projective top carrier $M_P$ has been constructed, the formal support argument is
short. Book 145, Sections 11.1--11.4 owns the general support--annihilator and
associated-prime formalism used below; the missing input here is arithmetic occurrence on a
specified product component, not a new commutative-algebra support theorem. Let $R_P$ be the
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

For the actual potential-modularity consumer, which asks about one named
characteristic-zero point rather than every point of $R_P$, full support is stronger than the
annihilator argument needs.

**Pointed joint-support lemma.**  Let $x:R_P\to D$ be a map to a domain, let $M_P$ be a
finite $R_P$-module, and let $\mathbb T_P$ be the faithful image of $R_P$ on $M_P$.  Suppose
there is an irreducible component $\Xi$ through $x$, with minimal prime
$\mathfrak p_\Xi\subseteq\ker x$, such that

$$
\mathfrak p_\Xi\in\operatorname{Supp}_{R_P}(M_P).
\tag{8.22a}
$$

Then $x$ factors canonically through $\mathbb T_P$. Under the same catenary/equidimensional
hypotheses used in the depth argument for (8.22), it is enough to verify the three conditions
preceding (8.22) at one unique-component prime $\mathfrak q_\Xi$ on this particular $\Xi$.

**Proof.**  If $I=\operatorname{Ann}_{R_P}(M_P)$, condition (8.22a) says
$I\subseteq\mathfrak p_\Xi$.  Hence

$$
I\subseteq\mathfrak p_\Xi\subseteq\ker x,
$$

so $x$ factors through $R_P/I=\mathbb T_P$.  The depth argument used for (8.22), applied only
to $\Xi$, proves (8.22a). $\square$

This is still a genuinely simultaneous support assertion: $\Xi$ is the one global component
carrying the complete tuple of local labels at all members of $P$.  It merely removes the
irrelevant demand to cover other product components when the downstream theorem has already
fixed one point.  In particular, it does not follow from the separate projections of $\Xi$ or
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
carriers are weaker still. The missing arithmetic input is a nonzero boundary class and the
maximal-depth comparison at every actual product component, not another application of the
one-place lemma.

There is a second, stronger formal certificate, but it makes the missing comparison explicit.
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
$w\in S_0\setminus\{v\}$ is trivial.  The product character

$$
c_P=(c_v)_{v\in P_{\rm sc}}:G_F\longrightarrow\Delta_P       \tag{8.25c}
$$

is surjective.  For the least common multiple $\mathfrak f_P$ of its coordinate conductors,
it is therefore an effective quotient

$$
\operatorname{Cl}_{\mathfrak f_P}(F)\twoheadrightarrow\Delta_P.
                                                               \tag{8.25d}
$$

At every active place $w\in P\setminus\{v\}$ the character $c_v$ is trivial. At $v$, all
coordinates except $c_v$ are trivial and the completed field is
$F_v(\pi_v^{1/e_v})$ with vertical Kummer unit $1$.  Every additional place in
$\mathfrak f_P$ is inserted in the fixed spectator datum, its local condition is transported
by the product twist, and all auxiliary sets are chosen disjoint from these places.

**Proof.**  For a fixed $v$, prescribe (8.25b) at $v$ and the zero class at
$S_0\setminus\{v\}$.  The exponent $e_v$ is odd, so Book 6, Theorem 6.1 and the non-Wang
alternative immediately following it globalize this tuple.  Its order is exactly $e_v$
because its localization at $v$
has that order.  At inertia over $v$, the combined character has image precisely the
$v$th coordinate subgroup of $\Delta_P$.  Those coordinate subgroups generate $\Delta_P$,
proving surjectivity.  Global reciprocity then factors (8.25c) through the ray class group of
its conductor, retaining all unit, sign, and central relations.  Local Kummer theory gives
the asserted completed fields. $\square$

Coordinatewise, Book 122, Proposition 9.9 identifies the pullback of $c_v$ with the
automorphic determinant line by canonical component reciprocity.  Tensoring those
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
image.  Proposition 8.3 prevents that defect by imposing cross-local triviality before applying
the local--global theorem; inertia at the selected places then supplies every coordinate
subgroup.  Without that simultaneous construction, the correct coefficient algebra would be
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
  iterated-switch datum $({\rm IBC}_P)$.  Distinct arithmetic fibers have empty intersection
  by (8.16a), so there is no literal multi-trait fiber on the original base.
- Raw one-prime split injectivity constructs the first quotient cube, but it does not prove
  injectivity on that quotient. For a pair, the first irreducible assertion is precisely
  $\operatorname{Ob}_{v,w}=0$.  After specialization to the coefficient DVR, Proposition
  8.2A identifies this assertion exactly with saturation of the sum of the two top old images;
  the countermodel (8.14k)--(8.14l) shows that edgewise splitting and generic exactness do not
  imply that saturation. Commuting old projectors whose product is the lower composite do
  prove it, and a cubically compatible system of edge retractions proves all recursive
  quotient-new splittings. Book 84 supplies these compatibilities on its common definite cube
  in the fully unit-Gram range, but separate one-place projectors do not supply them on the
  nonunit level-changing faces.
- A genuine external-product quasi-isomorphism over one common base, together with the stated
  projectivity or cross-Tor vanishing, would prove mixed exactness formally. Constructing that
  quasi-isomorphism is itself a several-place theorem and is not supplied by the one-prime
  sources. Restricted tensor factorization proves only the generic concentration (8.14e): the
  lower integral homology is $\varpi$-power torsion, while residual hyper-Tor over a larger
  face base remains to be controlled.
- Local coefficient-one residues identify the coordinate maps, but they do not construct the
  comparisons (8.19), kill the derived defect (8.20), or erase the component and branch Tor in
  (8.21). Formula (8.16b) constructs the parity-correct final inner forms and (8.16c) proves
  order independence of generic packet labels, while the torsion class (8.20a) shows why this
  does not imply integral derived Beck--Chevalley. Pairwise comparison maps and three-face
  endpoint braid identities still do not provide the higher fillers required to totalize a
  homotopy-coherent switch cube.
- Joint boundary nonvanishing and depth imply support formally by (8.22), but separate
  one-place support gives neither joint boundary witness.  For one named downstream point, the
  pointed joint-support lemma requires only the one product component through that point, not
  every component of the product ring.
- Proposition 8.3 constructs the scalar product ray quotient; on an already constructed
  routed cube equivariant for it, the iterated strict twist gives (8.26)--(8.27). Arbitrary
  separately chosen ray quotients would not. A common auxiliary
  package satisfying the full
  vertexwise hypotheses of Book 174, Proposition 9.1 gives coherent complex and module
  augmentation by (8.27a), with only the stated acting-image quotient.

These conclusions belong to seven different ledgers. Generic packet factorization controls
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

No declared prior source proves these missing assertions for the specialization-dependent
active set of Book 177. In the intended geometric route, only after the common coefficient
cube, its recursive mixed vanishings, the product-residue comparison, and joint support have
been constructed can one apply the finite-set criterion of Section 9.2. When scalar fibers
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
satisfy the complete one-prime ledger anew.

There is also a strictly smaller **pointwise finite-level route**.  Proposition 8.2B constructs
the actual torsion-free top quotient $Q_P^{\rm tf}$ and its adjoint carrier directly from the
one global cube, with $W_\Pi$ inserted once.  If the generic simultaneous branch labels on
that carrier are verified, Book 170 may then be applied to its faithful image; only after that
actual carrier and branch verification does $({\rm REC}_P)$ enter.  The pointed support lemma
then factors one named characteristic-zero point as soon as the single global component
through it lies in the carrier support.  This route neither proves $({\rm MIX}_P)$ nor commutes
the torsion-free quotient through a nonflat augmentation.  Product residue is needed only if
it is the chosen method for identifying that component and proving its boundary witness.

For logical minimality, the final annihilator argument consumes only an actual finite
projective carrier over the named coefficient base, the relevant full or pointed support, and
reciprocity to its faithful order. Product residue is listed in the simultaneous interface because it is the intended
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
cubical carrier with all faces. The following hypotheses give its exact interface; the bare
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
witness, but it is not consumed again by the pointed annihilator argument. Thus the first
unresolved theorem for this pointwise route is the actual joint-component occurrence in
clause 4, together with the carrier-specific branch verification needed before clause 3.

### 9.3 The potential-modularity consumer

The immediate potential-modularity consumer produces a geometric specialization whose extra
semistable places are known only after the specialization has been chosen. Its lower residual
packet must then be moved to the exact local datum of the target Tate module.

The presently justified interface is consequently one of the following forms:

1. the specialization has exactly one active place and satisfies every explicit hypothesis of
   the applicable one-prime conclusion in Chapter 7; or
2. an ordered finite chain is exhibited, and every one-prime hypothesis is verified anew at
   each intermediate level; or
3. the all-point simultaneous interface of Theorem 9.1 is used after all of its displayed
   hypotheses have been independently proved for the actual specialization; or
4. for the one already named Tate-module point, the pointed interface of Theorem 9.2 is used
   after constructing one actual final global cube, verifying simultaneous generic branch
   data and finite-set reciprocity on its torsion-free top carrier, and proving support on the
   one global component through that point.

Separate local cleanliness does not establish either simultaneous interface. In particular,
a consumer may not cite Theorem 9.1 as though (8.10), product residue, and joint support
followed from the one-prime sources. Theorem 9.2 does not require mixed saturation or product
residue unless those are used to construct or support its carrier, but separate one-place
occurrence still does not prove its pointed joint-support clause.

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
verified one-prime chain is supplied, every hypothesis of Theorem 9.1 has been proved, or for
one named lift the pointed carrier, branch, reciprocity, and support hypotheses of Theorem 9.2
have been proved.
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
in a chain. What remains for a simultaneous application of the blueprint is not a new kind
of arbitrary ramification. It is mixed integral control at finitely many semistable places,
joint support, and finite-set reciprocity. Finite-level reduced $R=T$ suffices for
characteristic-zero modularity; finite-level source reducedness is needed only if a full
scheme-theoretic equality is also demanded.

For a theorem making **every** lift in the product problem automorphic, the full-support route
of Theorem 9.1 still requires the mixed and product-residue package used to construct its
projective family. For the one representation already supplied by the FLT or
potential-modularity consumer, Theorem 9.2 shows that the logically minimal simultaneous
gate is narrower: an actual final joint cube, its torsion-free top carrier, simultaneous
generic branch verification, finite-set reciprocity on that carrier, and occurrence of the
single product component through the point.

## 10. Dependencies and conclusion

### 10.1 Exact source ledger

The direct mathematical sources used here have the following roles and retained limitations.

| source | result used | limitation retained here |
|---|---|---|
| Book 6 | odd-exponent local--global character theorem and ray-class factorization used in Proposition 8.3 | supplies the joint scalar ray quotient, not mixed geometric exactness or product support |
| Book 14 | coefficient-change universal-coefficient sequence, derived base-change morphisms, and compatibility under pasted squares | the formalism assembles supplied higher comparison maps; it does not construct the routed integral switching squares or prove their application-specific maps are quasi-isomorphisms |
| Book 22 | nearby cycles, normalization and graph/component complexes for a semistable curve over one trait | distinct closed arithmetic fibers have empty intersection, so its one-trait functor does not iterate literally across $P$ |
| Book 84 | one integral global $2^{|P|}$-fold degeneracy source at several definite-level primes and factorization of its Gram entries | constructs a common carrier and commuting maps, not primitivity of the sum of upper old images or exactness of the total quotient-new cube |
| Book 109 | recursive cyclic solvable descent selected by a representation already defined over the lower field | Galois invariance alone is not descent; irreducibility, image criteria, and full local antecedents are rechecked |
| Book 122 | the one-place Iwahori semistable PEL model, strict ray Kummer factors, completed actual-row tubes and $({\rm PNS}_v)_{\rm act}$, two branches, nodes, and integral component complex | treats one bad-residue trait with every other active level as spectator; supplies no iterated-switching Beck--Chevalley theorem |
| Book 123 | the global level tower, transitive forgetting maps, and right adelic level translations | constructs commuting generic level maps but no mixed integral exactness or simultaneous residue fiber |
| Book 124 | commutation of correspondences supported at distinct places, pull--trace adjunction, and common Hecke routing | commuting correspondences do not make their total cohomology cube exact or construct an inner-form-switching Beck--Chevalley comparison |
| Book 125 | restricted tensor factorization of a packet block with one global two-dimensional multiplicity module | proves the generic concentration (8.14e) and identifies the generic part of Proposition 8.2B's actual joint carrier, not integral mixed saturation or product-component support |
| Book 173 | neutral minimal modularity lifting and its coefficient-prime range | its equality is not applied to the conductor-one line-special ring with Kummer directions |
| Book 138 | enhanced special lines, primary and companion lattices, tame twists, and exceptional local charts | local lattices do not prove type incidence, type Ihara, primitive residue, or global support; primitive wild types are excluded |
| Book 139 | exact tree kernel of Theorem 6.1, and conditional saturation, duality, Gram, component, and branch sequences | after non-Eisenstein localization the exact kernel is the noncongruence quotient; its vanishing depends on $({\rm AIH}_{\mathscr F})$ at every actual constant flag level and is not a type-Ihara theorem |
| Book 140 | conditional one-prime integral level change, node/definite comparison, equality of faithful orders, signed Gram calculation, and the constant generic-support/common-kernel deduction from Book 125 plus the corrected filtration | gives the coordinate switches and generic packet-label compatibility used in (8.16c), but no integral Beck--Chevalley 2-isomorphism; retains datum-specific node uniformization, routing, abelian Ihara, and the branch Smith correction |
| Book 143 | functorial Taylor--Wiles represented-ring augmentation for an arbitrary original finite global problem | does not construct the automorphic product cube, its mixed exactness, or augmentation of a faithful acting image |
| Book 145 | exact support as the vanishing locus of the annihilator, component coverage, and associated-prime faithfulness criteria | formal support theory does not prove that the actual automorphic carrier occurs on the product component through the named point |
| Book 152 | several-prime regular-refinement idempotents on one global degeneracy source and exact multi-prime diamond augmentation under its hypotheses | splits and augments a supplied source; it expressly does not prove degeneracy injectivity, full oldness, or mixed sum-primitivity |
| Book 170 | order-valued Galois representation, factorization through represented local conditions, and the surjection (3.5) | requires every generic branch, integral coefficient-prime realization, reduced generic order, exact trace generation, and the conditional Book 140 comparison whenever used |
| Book 174 | enhanced one-prime type complex, typed generic-residue kernel equality from Book 125 after the typed filtration, scalar $q\equiv1$ family, primitive residue, one-prime support, exact fixed-prime augmentation, and auxiliary represented-ring/complex/module/pairing augmentation | $({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, $({\rm NU}_{\rm type})$, Book 125 applicability on the routed common cover, and $({\rm SUP}_v)$ retain their stated roles; support is topological and only one-place; auxiliary acting-order augmentation is only a surjection |
| Book 175 | in the scalar line-special range, finite-level reduced one-prime comparison, finite flatness from the balanced enhanced presentation, pointwise characteristic-zero modularity, and, under a coherent unpadded $({\rm AUX}_Q)$ tower, equal-variable full patched and finite $R=T$, all enhanced characteristic-zero tangent--Selmer vanishings, and exact auxiliary acting-order augmentation; the ray twist transports these to the scalar family | without a coherent auxiliary tower, full equality is equivalent to the isolated branchwise torsion-cotangent theorem; no theorem for the generic or vexing rows and no simultaneous finite-set theorem is supplied |

The exact direct-dependency row is

$$
176\mid 6,14,22,84,109,122,123,124,125,138,139,140,143,145,152,170,173,174,175.
\tag{10.0}
$$

Books 22 and 122 are used directly only for the one-trait boundary in Section 8.5; neither
supplies the asserted iterated-switch comparison, and (8.16a) rules out a literal common fiber
on the original arithmetic base. Book 125 is used directly for
(8.14c)--(8.14e), Proposition 8.2B, and also enters through Book 140's constant generic-support theorem and Book
174's typed generic-residue theorem. Book 84 is the owner of the integral common definite
degeneracy source, while Book 152 is used directly only for the several-prime regular-refinement
and augmentation boundary; neither supplies mixed exactness. Within Books 138--141,
163, and 170--176, Books 141 and 171--172 enter transitively through the type-support and
one-prime patching packages.
Book 164 is a downstream arithmetic synthesis, not a proof source. The mixed reduction
(8.3)--(8.10), the exact DVR criterion (8.14g)--(8.14j), the commuting-projector and cubical
contraction criteria, the torsion-free joint carrier, the parity inner-form cube, and the
pointed annihilator reduction are proved here. The remaining
sum-primitivity, integral Beck--Chevalley, and joint-component occurrence theorems are not
imported from a later consumer.

### 10.2 Logical and normalization checks

The proof order is rigid:

1. the represented local data are fixed without assuming Ihara or support;
2. the proved $({\rm TPE}_v)$, together with $({\rm TIC}_v)$ and
   $({\rm TIH}_{\mathscr F})$, gives the actual typed split
   one-prime quotient and coefficient-base Tor-vanishing;
3. independently, $({\rm AIH}_{\mathscr F})$ turns each constant tree kernel into residual
   injectivity and supplies Book 139's corrected filtration;
4. $({\rm PRI}_{\rm type})$ and, when used, $({\rm NU}_{\rm type})$ give the primitive
   residue and switched graph comparison, while $({\rm SUP}_v)$ gives full topological
   component support by its separate boundary-and-depth argument;
5. finite-level reciprocity gives a surjection to a faithful finite Hecke order, whose
   reducedness follows from its torsion-free semisimple generic action;
6. Lemma 6.1 identifies the finite-level kernel with the nilradical and proves reduced
   $R=T$;
7. characteristic-zero modularity follows because points over domains kill that nilradical;
8. for one active scalar line-special place, a coherent unpadded balanced $({\rm AUX}_Q)$
   tower invokes Book 175's equal-variable argument and upgrades the comparison to full patched
   and finite $R=T$;
   without that tower, source reducedness is the exact alternative, while for several active
   places the separate joint nilpotent problem remains; and
9. numerical consequences are derived only after the relevant comparison has been proved.

Thus no later ring equality proves an earlier Ihara or support statement, and no determinant
valuation is used to kill a deformation kernel. At two places, one-place injectivity is used
only to derive (8.6); it is not applied again to the quotient in (8.4). For a finite set,
the all-point route assumes joint support only after mixed exactness and product residue have
constructed and labelled the actual total carrier.  The pointed route has a different rigid
order: construct the actual final cube; form $Q_P^{\rm tf}$ with its adjoint dual $K_P^-$; verify all generic
product branches on that one carrier; only then invoke Book 170; and finally apply support on
the component through the named point.  Neither reciprocity nor support is stated on a
fictional tensor product of one-place global carriers.

The normalization ledger is equally fixed. Frobenius is geometric in (2.1); arithmetic
Frobenius is used only for the local matrix calculation (2.8)--(2.9) after explicit inversion.
The good polynomial, adjoint, Gram matrix, and monodromy relation are (2.1)--(2.4). Scalar
twisting changes the determinant by $\boldsymbol\chi_v^2$. Coefficient extension preserves
these equations, while uniformizer-normalized lengths scale with ramification.

### 10.3 The first unresolved inputs

The first unresolved input for the constant level-change rows is the finite family of
vanishings

$$
\left(H^1_{\mathrm{nc}}(\Gamma_D^v,k)^{\Delta_D}\right)_{\mathfrak m_D}=0
\quad(D\in\mathscr F_v(Q)).
\tag{10.1}
$$

Until (10.1) is proved in the declared odd-primary Shimura-curve range, the constant
saturation, corrected component filtration, and raising/lowering conclusions that use them
remain conditional. For the type rows, $({\rm TPE}_v)$ is proved by Book 174 from Book 122's
actual-row theorem. Book 174, Proposition 3.0B also proves $({\rm TIC}_v)$ once the clean
actual-stabilizer and unit-order coarse-descent datum has been verified; it is not an
additional unresolved theorem after those hypotheses are matched. The first independent
residual input is $({\rm TIH}_{\mathscr F})$, including the quotient-new injection (5.0d) in
the nonbanal row. Its split complex does not follow from (10.1). Coefficient-one extreme residues additionally require
$({\rm PRI}_{\rm type})$, and a switched graph--definite comparison additionally requires
$({\rm AIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$,
$({\rm NU}_{\rm type})$, Book 140's node-uniformization and Book 125 component-routing source
condition. In the constant clean block, generic support and common-kernel equality are
conclusions of Book 140, Section 8.3, relative to the separate abelian Ihara input. Under the
typed parahoric, type-Ihara, primitive-residue, and actual routed-cover hypotheses, the typed
generic-residue kernel equality is likewise the conclusion of Book 174, Proposition 6.3.
Neither generic comparison is a further hypothesis once its displayed inputs are granted.

For the core finite-level scalar theorem, the exact independent conditional inputs are
$({\rm AUT}_v)$, $({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$,
$({\rm SUP}_v)$, and $({\rm REC}_v)$, with
$({\rm AUX}_Q)$ whenever an auxiliary patch is used. Under $({\rm AUX}_Q)$ the represented
rings, both adjoint complexes, modules, actions, and pairings augment exactly. At an isolated
auxiliary level the acting-order map is initially only a surjection. If these data form the
coherent unpadded tower at every depth, Book 175, Proposition 5.2 proves $({\rm GR}_v)$ and
full base $R=T$ by equal-variable rigidity, after which the acting-order map is injective. The
finite-level reduced comparison uses the proved $({\rm TPE}_v)$ and the constructed strict
$({\rm RAY}_v)$ datum, and may instead be applied directly after augmentation without
requiring that injectivity. Thus Theorem 7.1 remains conditional on the core geometric and
reciprocity inputs even if (10.1) is proved. Conversely, once this core list is supplied, its
formal reduced comparison does not require one to smuggle $({\rm AIH}_{\mathscr F})$ or
$({\rm PRI}_{\rm type})$ into the word “support.” An argument formulated only for separated
roots does not supply the $q_v\equiv1\pmod\ell$ enhanced-line case.

Without the coherent auxiliary tower, the additional one-prime hypothesis for full
finite-level scheme-theoretic $R=T$ is precisely

$$
R^{\mathrm{sp},1}\text{ is reduced}.
\tag{10.1a}
$$

Neither local reducedness of the special chart nor minimal $R=T$ proves (10.1a).
Equivalently one may supply Book 175's branchwise torsion-cotangent theorem. With the coherent
unpadded balanced tower, however, Proposition 5.2 proves (10.1a), the full patched equality,
and every
enhanced characteristic-zero tangent--Selmer vanishing without assuming reducedness of either
patched ring. The flat dual-number countermodel in Book 175 shows why finite flatness and
topological support alone would not suffice.

For two or more places, the division of mathematical roles among the earlier sources separates
what is already proved from what is not. Book 84, Section 11.9 supplies the common integral several-prime degeneracy
source and its product Gram formula; Book 152, Proposition 11.1 owns its regular-refinement
source splitting; Book 14 owns coefficient-derived comparison and pasting; and Book 145 owns
the formal support implications. None of these proves the three arithmetic assertions below.
The closest aliases do not close them: Book 96, Section 12.4 explicitly warns that an integral
sum of old images can be nonsaturated; Book 140, Section 14.2 proves only the conditional
external-product implication after the common-carrier comparison and cross-Tor vanishing have
been supplied; and Book 156's two-prime product monodromy concerns a Hilbert--Blumenthal frame
torsor, not a Hecke incidence cube or a semistable component complex. Books 174--175 state a
strict one-place boundary, while Books 177 and 182 are downstream consumers. Thus the issue is
not a missing cross-reference to an equivalent theorem elsewhere in the manuscript.
The intended geometric route must first verify $({\rm FACE}_P)$ and
supply one joint coefficient descent and every component route at every spectator tuple and
auxiliary shadow. The global level tower then constructs $({\rm CUBE}_P)$ formally as in
Section 8.4. Given that cube,
the first additional homological obstruction at a pair is

$$
\operatorname{Ob}_{v,w}=0
\tag{10.2}
$$

for every actual spectator tuple and auxiliary shadow.  At the final coefficient-DVR level,
Proposition 8.2A proves the exact equivalence

$$
(10.2)
\quad\Longleftrightarrow\quad
M_{11}/\bigl(\operatorname{im}d_{v\mid1}
+\operatorname{im}d_{w\mid1}\bigr)
\text{ is }\mathcal O\text{-torsion-free}.
\tag{10.2a}
$$

Thus the first missing two-place homological theorem is the primitivity of this **sum** of
old images.  It is strictly stronger than primitivity of either summand, as
(8.14k)--(8.14l) proves.  Over a larger face algebra, the corresponding theorem must also
kill the maximal-ideal hyper-Tor shadows; coefficient-DVR saturation alone is insufficient.
The commuting-old-projector criterion after Proposition 8.2A and the cubically compatible
contraction criterion after Proposition 8.2 are valid sufficient routes, but their transverse
commutation and product-image hypotheses are exactly extra several-place data. Book 84's
product Gram entries verify them in the cubically compatible unit-Gram range, but not on the
selected nonunit level-changing faces; Book 152's source refinement idempotents likewise do
not verify them on the actual quotient-new cube.

After (10.2), the intended geometric support proof still needs $({\rm IBC}_P)$ and the
product-residue comparison to identify and transport the component boundary data.  The first
exact geometric assertion is the construction of the maps (8.16d), their normalized
two-face comparisons, three-face braid and chain-level fillers, all required higher coherence,
and vanishing of (8.20). Formula (8.16b) already settles quaternionic parity and
the final inner form, while (8.16c) settles only generic packet labels.  The torsion class
(8.20a) proves that those generic facts do not settle the integral theorem.  The resulting
joint-support assertion $({\rm JSUP}_P)$ must then still be proved. At three or more places,
pairwise versions of (10.2) do not replace the higher mixed homology and Tor-independence in
$({\rm MIX}_P)$. Simultaneous character and auxiliary specialization
$({\rm AUG}_P)$ is needed where those specializations are used. Proposition 8.3 supplies its
scalar ray quotient when $P_{\rm sc}\ne\varnothing$; (8.26) supplies strict product twisting
only after the routed joint cube has been constructed. Its
auxiliary part requires coherent exact augmentation of the total primary--companion cubes,
which follows from one common equivariant auxiliary package satisfying the full vertexwise
hypotheses of Book 174, Proposition 9.1 by (8.27a), but not acting-image injectivity for a
direct finite-level reduced comparison. Finite-set reciprocity
$({\rm REC}_P)$ is the further joint verification needed to apply Book 170 to the actual
faithful image; no new trace-descent theorem remains after that verification. Under this entire list, Theorem
9.1 proves finite-level reduced $R=T$ and pointwise modularity; full
finite-set $R=T$ additionally requires $R_P$ to be reduced. None of the simultaneous
mixed exactness, product-residue, or joint-support assertions follows from the present
one-prime source chain.

For the actual named point used downstream, Theorem 9.2 removes two unnecessarily strong
demands from this list.  Proposition 8.2B gives a canonical finite free top carrier even when
(10.2) fails, and the pointed support lemma needs only the global component through that
point.  The first exact unresolved theorem on this shorter route is therefore:

$$
\mathfrak p_{\Xi_x}\text{ for the component carrying the full }P_{\rm act}\text{-tuple lies in }
\operatorname{Supp}_{R_P}(Q_P^{\rm tf}).
\tag{10.2b}
$$

Before (10.2b) can be used, all simultaneous generic branch and structural labels on this
actual carrier must be verified; only then does Book 170 supply $({\rm REC}_{P,x})$.  Product
residue remains one possible route to (10.2b), but is not a formal premise of the annihilator
step.  Mixed exactness remains necessary for the stronger family, patching, and all-point
$R=T$ interface, not for the bare factorization of this one characteristic-zero point.

### 10.4 Final synthesis

Nonminimal modularity lifting at one place is governed by one incidence complex. The two
degeneracy maps identify the old lattice; the companion records the integral adjoint; nearby
cycles give a primitive graph residue; the enhanced local deformation ring names the special
component; and the order-valued Galois representation supplies the canonical surjection from
deformations to Hecke operators. Constant abelian Ihara, type incidence, type Ihara, primitive
residue, typed node uniformization, and support have different jobs and remain separately
named. For the core finite-level comparison, the actual typed complex, one-boundary support,
strict scalar twist, auxiliary control, and reciprocity hypotheses identify the
deformation-to-Hecke kernel with the nilradical. This proves reduced one-prime $R=T$ and hence
characteristic-zero modularity. Constant Ihara, primitive residue, and node uniformization
enter exactly when their richer level-change and component conclusions are invoked. Global
finite-level reducedness is the exact extra input for full finite-level $R=T$ if no coherent
auxiliary tower is available. In the scalar line-special range, when that tower is retained,
Book 175's equal-variable theorem proves full patched and finite one-prime $R=T$ and all
enhanced tangent--Selmer vanishings without a reducedness hypothesis.

The generic and vexing one-place application is deliberately separate. Theorem 7.1A proves
the same reduced-image and characteristic-zero factorization once an actual carrier with full
support and finite reciprocity has been constructed for the exact represented component. It
does not manufacture that carrier from the scalar theorem. At a vexing place it retains the
whole primary--companion block unless an integral signed direct factor and its support are
independently available.

The local arithmetic has a sharp division. Generic level raising with
$q_v\not\equiv\pm1\pmod\ell$ produces a conductor-one special packet. A scalar
$\ell$-power tame twist exists only at $q_v\equiv1\pmod\ell$ and moves a special packet from
conductor one to conductor two while changing the determinant by the square of the character.
At $q_v\equiv-1\pmod\ell$, the full primary--companion and Smith blocks must remain visible.

At several places the new object is a cube. Its first two-place defect is the explicit module
$\operatorname{Ob}_{v,w}$, the first homology of the total incidence square. Edgewise
saturation does not make it vanish. Over the final coefficient DVR it is exactly the
$\varpi$-torsion in the top joint-new quotient, so its vanishing is exactly primitivity of the
sum of the two top old images. The split-edge torsion countermodel proves that generic
concentration does not force this primitivity. Commuting old projectors or one cubically
compatible contraction would force the required splitting, but separate unit-Gram projectors
do not provide either certificate. Book 84 does provide the certificate on its common
definite cube when every required face remains in the compatible unit-Gram range; the missing
level-raising faces are precisely outside that conclusion. The global level tower constructs the coherent generic cube
once the joint coefficient descent and component routes are supplied, and packetwise
factorization concentrates its generic fiber in top degree. It leaves lower
$\varpi$-power-torsion homology and, over a larger face base, the corresponding residual
hyper-Tor problem. Distinct arithmetic fibers have no common closed stratum; product residue
must therefore be formulated through the parity-correct iterated-switch cube or a genuinely
new higher-dimensional interpolation. The final inner forms and generic packet labels commute,
but the integral Beck--Chevalley homotopies, their higher coherence, and joint component support are
further mixed conclusions, not definitions. Theorem 9.1 proves the all-point finite-set modularity conclusion
when the actual face package, derived global cube, mixed exactness, product residue, joint
support, simultaneous augmentation, and finite-set reciprocity are all supplied. Pairwise
one-prime data do not supply those hypotheses.

For the actual named point downstream, the canonical torsion-free top quotient and its
adjoint give a smaller honest carrier with the global module $W_\Pi$ occurring once. Theorem
9.2 reduces pointwise modularity to simultaneous branch verification on that carrier,
finite-set reciprocity invoked only afterward, and support on the single global component
through the point. This bypasses mixed saturation and product residue at the annihilator step,
but does not prove either missing theorem or allow nonflat augmentation to be ignored. The
source chain therefore gives a bounded
conditional but scheme-theoretically full scalar line-special one-prime theorem in the
coherent auxiliary range, together with an exact conditional finite-set interface, without
pretending that the unresolved geometric inputs are already available.
