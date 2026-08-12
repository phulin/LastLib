# Nonminimal Modularity Lifting

## Contents

- [1. The exact lifting problem](#1-the-exact-lifting-problem)
  - [1.1 Minimal and nonminimal deformation spaces](#11-minimal-and-nonminimal-deformation-spaces)
  - [1.2 What one changed place must provide](#12-what-one-changed-place-must-provide)
  - [1.3 The finite-set demand from the FLT argument](#13-the-finite-set-demand-from-the-flt-argument)
  - [1.4 The result and its boundary](#14-the-result-and-its-boundary)
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
- [4. Saturated Ihara theory and integral level change](#4-saturated-ihara-theory-and-integral-level-change)
  - [4.1 The exact residual kernel](#41-the-exact-residual-kernel)
  - [4.2 The abelian Ihara hypothesis](#42-the-abelian-ihara-hypothesis)
  - [4.3 Consequences after the hypothesis is supplied](#43-consequences-after-the-hypothesis-is-supplied)
  - [4.4 Component and branch corrections](#44-component-and-branch-corrections)
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
  - [7.1 The one-prime theorem](#71-the-one-prime-theorem)
  - [7.2 Recovery of an automorphic representation](#72-recovery-of-an-automorphic-representation)
  - [7.3 Coefficient extension](#73-coefficient-extension)
  - [7.4 Solvable base change and descent](#74-solvable-base-change-and-descent)
  - [7.5 Exact exceptional boundaries](#75-exact-exceptional-boundaries)
- [8. Two places and the first mixed obstruction](#8-two-places-and-the-first-mixed-obstruction)
  - [8.1 Why two saturated edges do not make a saturated square](#81-why-two-saturated-edges-do-not-make-a-saturated-square)
  - [8.2 The mixed Ihara module](#82-the-mixed-ihara-module)
  - [8.3 Top-degree concentration is equivalent to mixed vanishing](#83-top-degree-concentration-is-equivalent-to-mixed-vanishing)
  - [8.4 Further finite-set obligations](#84-further-finite-set-obligations)
- [9. The finite-set and downstream interfaces](#9-the-finite-set-and-downstream-interfaces)
  - [9.1 What iteration actually proves](#91-what-iteration-actually-proves)
  - [9.2 The hypotheses for a simultaneous theorem](#92-the-hypotheses-for-a-simultaneous-theorem)
  - [9.3 The potential-modularity consumer](#93-the-potential-modularity-consumer)
  - [9.4 The FLT boundary](#94-the-flt-boundary)
- [10. Dependencies and conclusion](#10-dependencies-and-conclusion)
  - [10.1 Exact source ledger](#101-exact-source-ledger)
  - [10.2 Logical and normalization checks](#102-logical-and-normalization-checks)
  - [10.3 The first unresolved inputs](#103-the-first-unresolved-inputs)
  - [10.4 Final synthesis](#104-final-synthesis)

## 1. The exact lifting problem

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
The purpose of this book is to keep these stages separate and then prove the formal passage
from a supported one-prime complex to an $R=T$ equality.

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
place.

### 1.4 The result and its boundary

The unconditional algebra in this book has two parts. First, once the exact one-prime
geometric, reciprocity, and support hypotheses are stated separately, a short annihilator
argument identifies the reduced finite-level deformation ring with the faithful finite Hecke
order. This is enough for characteristic-zero modularity because a map to a DVR kills
nilpotents. At patched level the same support argument controls the annihilator only up to the
nilradical: a patched reduced comparison additionally requires the patched acting image to be
reduced, while a full patched equality follows if the patched deformation source is reduced.
Neither reducedness assertion is supplied by the present source chain. Full finite-level
scheme-theoretic $R=T$ likewise requires the selected global deformation ring to be reduced.
Second, for two places the first homology of the total incidence square is identified exactly
with a mixed Ihara kernel.

The arithmetic inputs are not all presently theorems in the declared source chain. The core
finite-level comparison depends on the actual automorphic localization, the separate
type-incidence and type-Ihara hypotheses, the one-boundary support datum, and the exact
reciprocity order. The scalar family also needs an effective global ray quotient and strict
twist identities. The richer level-changing and component package additionally depends on a
finite family of abelian Ihara vanishings, primitive type residue, and typed node
uniformization when a switched carrier is used. The finite-set package further requires
vanishing of all mixed homology, a coefficient-one product-residue comparison, joint
component support, and simultaneous augmentation. The statements below never insert these
assertions into the word “clean” or into a local definition. The one-prime and finite-set
theorems are therefore stated with their exact conditional inputs.

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
| scalar tame twist | $q_v\equiv1\pmod\ell$ | enhanced line, sign, global ray quotient $\Delta_v$, and $\Lambda_v=\mathcal O[\Delta_v]$ | Book 174's strict type complex under $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$, support under $({\rm SUP}_v)$, and exact twist augmentation under the effective ray hypothesis; constant Ihara and primitive residue are separately required only for the corrected component filtration and extreme residue |
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

In the scalar-twist regime it also records an actual finite cyclic $\ell$-power quotient
$\Delta_v$ of a global ray group, not merely a local abstract character. Local inertia at
$v$ must factor through $k_v^\times$ and map onto $\Delta_v$, and the unit, central, and
archimedean compatibilities must hold. Put

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
package can be realized directly on the curve-new carrier. Switching a typed carrier to a
definite lattice is a further comparison: it separately requires Book 140's
node-uniformization, generic-support, and common-kernel hypotheses together with
$({\rm AIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, and
$({\rm NU}_{\rm type})$ for the actual type coefficients.

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
- extension and adjunction of the actual type systems through the incidence model
  $({\rm TIC}_v)$;
- the crossed-coefficient residual type-Ihara theorem
  $({\rm TIH}_{\mathscr F})$;
- saturation of the old image and freeness of its quotient;
- global primitive type residue $({\rm PRI}_{\rm type})$;
- typed node uniformization $({\rm NU}_{\rm type})$ and equality of integral curve and
  definite orders;
- vanishing of a Néron component group or of the independent branch Smith correction;
- the one-prime boundary and depth datum $({\rm SUP}_v)$, which proves support on every
  selected deformation component;
- reducedness or faithfulness of the patched deformation source;
- vanishing of a mixed kernel at two changed places; and
- joint support on a product of local components.

This separation makes failure localizable. If constant abelian Ihara is missing, one stops
before using Book 139's corrected constant-coefficient filtration. If type incidence or
type-Ihara is missing, one stops before forming the projective typed new quotient. If a
one-prime support statement is available but a finite-set mixed kernel is not, one retains
the one-prime theorem and stops before a simultaneous finite-set conclusion.

## 4. Saturated Ihara theory and integral level change

### 4.1 The exact residual kernel

The local tree calculates relations between the two degeneracy maps, but the arithmetic
quotient of that tree has first cohomology. Let $\Gamma^v$ be the norm-one $S$-arithmetic
group at the changing place, let $\Delta$ denote the component-routing quotient, and let

$$
H^1_{\mathrm{cong}}(\Gamma^v,k)
\subseteq H^1(\Gamma^v,k)
\tag{4.1}
$$

be the subgroup of characters continuous for the congruence topology. Put

$$
H^1_{\mathrm{nc}}(\Gamma^v,k)
=H^1(\Gamma^v,k)/H^1_{\mathrm{cong}}(\Gamma^v,k).
\tag{4.2}
$$

Book 139 proves, after the component and central routing has been performed, the exact formula

$$
\ker(d_v\otimes k)_{\mathfrak m}
\simeq
\left(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\right)_{\mathfrak m}.
\tag{4.3}
$$

The congruence-continuous part is Eisenstein and vanishes at the chosen non-Eisenstein
localization. Formula (4.3) shows why non-Eisensteinness alone is not enough: an abstract
finite character need not be continuous for the congruence topology.

### 4.2 The abelian Ihara hypothesis

The required additional input is the explicit vanishing

$$
\mathbf I(v,\mathfrak m):
\qquad
\left(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\right)_{\mathfrak m}=0.
\tag{4.4}
$$

We call (4.4) the **abelian Ihara hypothesis**. It is not part of the definition in Chapter 3.
It would follow from the appropriate localized abelian commensurator theorem, or from another
argument proving precisely the group in (4.4) zero. The tree, strong approximation, and
non-Eisenstein localization do not prove it from the currently declared sources.

For the flag resolution used by Book 174, one needs a finite family of such statements. If
$D$ ranges over the constant-coefficient vertex, edge, permutation, and adjoint-companion
curves with the actual tame spectator tuple and auxiliary level, the hypothesis is

$$
({\rm AIH}_{\mathscr F}):
\qquad
\left(H^1_{\mathrm{nc}}(\Gamma_D^v,k)^{\Delta_D}\right)_{\mathfrak m_D}=0
\quad\text{for every }D\in\mathscr F_v(Q).
\tag{4.4a}
$$

This is the first gap in proof order for the constant rows. Every later use of constant
“Ihara injectivity,” “saturated old image,” or the corrected normalization filtration is
conditional on (4.4a) with the actual spectator data. It does not imply the type-coefficient
injectivity introduced in Chapter 5.

### 4.3 Consequences after the hypothesis is supplied

Assume (4.4) for one constant-coefficient curve. Then (4.3) makes its residual degeneracy map
injective. Let
$M$ and $N$ be finite free $\mathcal O$-modules and let $d:M^{\oplus2}\to N$ be the integral
map. If $d\otimes k$ is injective, a maximal minor of $d$ is a unit. Elementary row and column
operations split off an identity block. Consequently

$$
0\longrightarrow M^{\oplus2}
\xrightarrow{d}N\longrightarrow Q\longrightarrow0
\tag{4.5}
$$

is exact with $Q$ finite free. Thus residual injectivity gives integral saturation; no
determinant calculation is used for that step.

Book 139 also identifies the orthogonal new lattice with $Q^\vee$, computes the Gram operator
(2.4), and relates the graph monodromy pairing to the Néron component group. Book 140 adds the
node-uniformization and generic-support hypotheses required to identify the graph lattice with
the definite quaternionic lattice and to identify their faithful integral Hecke orders.

The generic signed level-raising theorem further assumes

$$
q_v\not\equiv\pm1\pmod\ell.
\tag{4.6}
$$

This is the first row of Section 2.4. It is not a hypothesis for the scalar-twist family,
which instead belongs to $q_v\equiv1\pmod\ell$ and requires the enhanced type construction of
Book 174.

More explicitly, assume the conditional node-uniformization and generic-support hypotheses of
Book 140 and specialize the central operator to $S_v=1$; the general central branch is obtained
by the corresponding integral square-root normalization. Assume an integral separated sign
$\varepsilon$ and

$$
a_v-\varepsilon(q_v+1)\in\mathfrak m.
\tag{4.6a}
$$

Assume the localized residual lower carrier contains a primitive vector for the chosen
away-from-$v$ residue character and that the $U_v$ action and local type have Book 140's
normalization. Choose a primitive lift $x_0$ of that vector and put
$x_\varepsilon=(x_0,-\varepsilon x_0)$ in the old plane. Then
$G_vx_\varepsilon\in\varpi(M^{\oplus2})^\vee$. Saturation of $d$ and perfect duality make
$d^*:N\to(M^{\oplus2})^\vee$ surjective, so choose $z\in N$ with

$$
d^*z=\varpi^{-1}G_vx_\varepsilon.
\tag{4.6b}
$$

The integral vector

$$
y=d(x_\varepsilon)-\varpi z
\tag{4.6c}
$$

lies in $\ker d^*$. Its reduction is $d(x_\varepsilon)$, which is nonzero by residual Ihara
injectivity. Thus the congruence produces a genuine nonzero residual new class. The integral
$W_v$-projector puts it in the $W_v=-\varepsilon$ block, which is the
$U_v=\varepsilon$ block on the new quotient; finite flatness of the faithful new order then
supplies a characteristic-zero special packet. The proof order matters:
Ihara gives nonvanishing, saturation gives the integral correction, and the Gram congruence
is used only afterward.

### 4.4 Component and branch corrections

Saturation does not make every finite semistable correction disappear. There are at least
three different modules:

$$
\begin{array}{c|c}
\text{module}&\text{meaning}\\ \hline
\operatorname{coker}G_v&\text{old--new Gram congruence}\\
\operatorname{coker}\mu_\Gamma&\text{Néron component discriminant}\\
\mathcal C_{\mathrm{br},v}
=\operatorname{coker}\bigl(1-(F_v^*)^2\bigr)
&\text{normalized-branch Smith correction}.
\end{array}
\tag{4.7}
$$

The first is compatible with a signed congruence factor only after a primitive branch has
been selected. The second is a cokernel of graph monodromy. The third measures whether the
bottom graph lattice remains primitive in the normalized quotient. They can have related
support without being the same module or multiplicative correction factors.

Level raising uses a nonunit Gram factor to create a new residual class. Level lowering is
different: it requires zero residual monodromy together with separate control of both the
component group and $\mathcal C_{\mathrm{br},v}$. The one-prime modularity theorem below
retains these modules; it never deduces their vanishing from (4.4).

Here is the exact clean lowering implication. Let $\mathfrak n$ be a non-Eisenstein maximal
ideal occurring in the new quotient. Assume the applicable constant or typed Ihara and
incidence hypotheses, and:

1. $\mathfrak n$ is stable under the Hecke adjoint and the residual new block pairs perfectly
   with its adjoint block;
2. residual monodromy is zero on the full $\mathfrak n$-block, not merely on its
   semisimplification;
3. the component obstruction has no residual torsion:
   $$
   \operatorname{coker}(\mu_\Gamma)[\varpi]_{\mathfrak n}=0;
   $$
4. the independent branch obstruction has no residual torsion:
   $$
   \mathcal C_{\mathrm{br},v}[\varpi]_{\mathfrak n}=0;
   $$
5. the normalization middle piece is exactly the two lower-level branches, without
   stabilizer or coefficient torsion; and
6. the block is nonzero and no scalar, self-twist, or vexing identification merges it with an
   Eisenstein or different adjoint block.

Then the contracted away-from-$v$ residual eigensystem occurs at hyperspecial level and has a
characteristic-zero lower-level branch after coefficient extension. Indeed, conditions 3--4
make the graph monodromy map injective after reduction, so condition 2 kills the top graph
piece. Perfect adjoint duality kills the bottom graph piece. If the lower localization were
zero, condition 5 would kill the middle piece as well, contradicting condition 6.

This lowers an eigensystem; it does not turn the same characteristic-zero new packet into a
lower-level packet. Fixed-prime scalar augmentation is different again: it untwists a
character while retaining the line-special monodromy closure. At a typed scalar or vexing
place, all type-incidence, type-Ihara, primitive-residue, and adjoint-block hypotheses must be
verified for this lowering argument, together with typed node uniformization if the carrier
is switched to the definite side; the constant theorem does not supply them.

## 5. The one-prime type complex

### 5.1 Primary and companion lattices

At $q_v\equiv1\pmod\ell$, the two old Frobenius roots can collide, so an ordered root
projector is unavailable. Book 174 replaces it by an actual line-enhanced coefficient system.
The primary Steinberg lattice is a quotient of the finite flag permutation lattice by
constants; the companion is the augmentation kernel. In bases indexed by all flags except one,
their pairing matrix is the identity. Hence the pairing is perfect without division by
$q_v+1$.

At $q_v\equiv-1\pmod\ell$, the two lattices reduce to opposite nonsplit extensions. The full
primary--companion construction remains meaningful, but one cannot discard one signed factor
unless an integral sign block has independently been shown to be a direct summand. This is why
the complex (3.4), rather than a rational eigenspace, is the basic object.

Book 174 does not transfer endpoint injectivity from constant coefficients by a formal
diagram chase. It first assumes $({\rm TIC}_v)$: the quotient-primary and
augmentation-companion systems, their pull and norm maps, their adjunction, and their nearby
cycles extend through the actual parahoric incidence model. It then assumes the independent
crossed-coefficient condition $({\rm TIH}_{\mathscr F})$. For every residual primary or
companion coefficient object $\overline W$ in the actual flag diagram, this condition is

$$
\ker\!\left(
H^1(\Gamma_{D,0}^v,\overline W)\oplus
H^1(\Gamma_{D,1}^v,\overline W)
\longrightarrow H^1(\Gamma_{D,e}^v,\overline W)
\right)_{\mathfrak m_D}^{\Delta_D}=0.
\tag{5.0}
$$

A cocycle with coefficients in $\overline W$ is a crossed homomorphism, so the arithmetic
character calculation of Book 139 does not prove (5.0). The constant family
$({\rm AIH}_{\mathscr F})$ and the type family $({\rm TIH}_{\mathscr F})$ are both retained.

### 5.2 The incidence complex and its Tor term

Assume $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$ at every actual shadow. Then $d_v$ in
(3.4) is a split injection over the relevant complete local coefficient algebra $A$. Its
cokernel

$$
N_v^{\mathrm{new}}=\operatorname{coker}d_v
\tag{5.1}
$$

is finite projective and

$$
C_v^{\mathrm{pri}}\simeq N_v^{\mathrm{new}}[-1].
\tag{5.2}
$$

For an arbitrary $A$-algebra $B$, the universal-coefficient sequence is

$$
0\longrightarrow
H^0(C_v^{\mathrm{pri}})\otimes_AB
\longrightarrow
H^0(C_v^{\mathrm{pri}}\otimes_A^LB)
\longrightarrow
\operatorname{Tor}_1^A(N_v^{\mathrm{new}},B)
\longrightarrow0.
\tag{5.3}
$$

The degree-one group is $N_v^{\mathrm{new}}\otimes_AB$. Equation (5.3) identifies the exact
specialization defect. One must not replace the complex by its generic new quotient before
the Tor term has been proved zero.

In the one-prime type construction the quotient is projective over the face algebra, so the
Tor group vanishes for the specified one-prime augmentations. This assertion is stronger than
$\mathcal O$-freeness: the relevant Tor is over the character or acting base.

### 5.3 The scalar-twist face

In the scalar regime let $\Lambda_v$ and $\boldsymbol\chi_v$ be as in (3.2). Scalar twisting
gives a represented identity

$$
R_v^{\mathrm{sp},2}
\simeq
R_v^{\mathrm{sp},1}
\widehat\otimes_{\mathcal O}\Lambda_v,
\tag{5.4}
$$

with determinant (3.3). Augmentation $\epsilon_v:\Lambda_v\to\mathcal O$ gives

$$
R_v^{\mathrm{sp},2}
\widehat\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\simeq R_v^{\mathrm{sp},1}.
\tag{5.5}
$$

The type complexes, primary--companion pairings, graph residues, and named Hecke actions have
the same exact augmentation. Moreover the faithful acting order satisfies

$$
\mathbb T_v^{(2)}
\simeq\Lambda_v\otimes_{\mathcal O}\mathbb T_v^{(1)},
\qquad
\mathbb T_v^{(2)}/\mathfrak a_v\mathbb T_v^{(2)}
\simeq\mathbb T_v^{(1)},
\tag{5.6}
$$

where $\mathfrak a_v=\ker\epsilon_v$. The proof uses group-basis coefficient extraction, not
an inference from exact module augmentation.

Every nontrivial character factor in (5.4) with nonzero specialized monodromy has conductor
two by (2.6); the augmentation face with nonzero monodromy has conductor one. The represented
closure also contains monodromy-zero boundary points. The enhancement and the determinant
square persist on both sides.

### 5.4 Support is not faithfulness

The nodewise incidence calculation alone does not prove that the global type residue is
primitive. Book 174 assumes $({\rm PRI}_{\rm type})$: after localization and residual
specialization, the extreme primary and companion residue sequences remain exact without an
extra snake-lemma class from the nonsemisimple flag rows. Typed graph--definite comparison
further assumes $({\rm NU}_{\rm type})$, including coefficient actions, unit stabilizer
weights, routing, and coefficient-one scale.

The support datum $({\rm SUP}_v)$ is separate again. It retains the actual Taylor--Wiles
shadows with Book 141's split-regular detector input, a nonzero lower boundary carrier,
singularity of the correct same-coefficient Gram block, the full scalar or two-sign boundary
chart, uniqueness of the named component at each boundary prime, and equality of the local
dimensions used in the depth argument. Under
$({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$, and $({\rm SUP}_v)$, Book 174 proves that the
patched and finite-level primary--companion complexes meet every generic point of every named
one-prime component.

For a finite module $M$ over a noetherian ring $P$,

$$
\operatorname{Supp}_P(M)=V(\operatorname{Ann}_P M).
\tag{5.7}
$$

Full support therefore implies only

$$
\sqrt{\operatorname{Ann}_P M}=\sqrt{(0)}.
\tag{5.8}
$$

If $P$ is nonreduced, this need not be faithfulness. For example,
$k[\epsilon]/(\epsilon^2)$ acts on $k$ with full support and nonzero annihilator
$(\epsilon)$. Reducedness of the exact source, or an independent theorem controlling its
nilradical, is a separate input to the ring equality.

## 6. The conditional one-prime R=T theorem

### 6.1 The explicit comparison hypotheses

We now state the inputs without hiding any of them in the geometric datum. They have different
logical roles.

1. $({\rm AUT}_v)$ is the actual automorphic localization of Section 3.3 together with the
   residual and coefficient-prime data of Section 3.1.
2. $({\rm TYPE}_v)$ means $({\rm TIC}_v)$ and
   $({\rm TIH}_{\mathscr F})$ for every actual primary and companion shadow and spectator
   tuple.
3. $({\rm SUP}_v)$ is the five-clause one-boundary datum of Book 174: marked finite shadows
   satisfying Book 141's split-regular detector input, a nonzero lower minimal boundary
   carrier, singularity of the correct same-coefficient Gram block, the exact selected boundary
   chart with a unique named component through each witness, and equality of the local
   dimensions used in the depth argument.
4. $({\rm REC}_v)$ is the Book 170 reciprocity package on the actual finite carrier: integral
   Galois realization and exact local--global compatibility on every generic factor,
   all-Artinian finite-flat factorization above $\ell$, semisimplicity of the generic Hecke
   action, and generation of the faithful image by the verified trace, determinant, tame,
   line, sign, and diamond operators. No operator outside the proved trace or structural
   order is silently adjoined.
5. $({\rm RAY}_v)$, used for the scalar family, is an effective global ray quotient together
   with the strict twist identities (5.4)--(5.6) and determinant square (3.3).
6. $({\rm AUG}_Q)$, used when descending an auxiliary patch, is exact auxiliary augmentation
   on represented deformation rings, complexes, pairings, deformation actions, and faithful
   acting orders. Module augmentation alone is not the last assertion.

The core finite-level comparison uses items 1--4; the conductor-two scalar comparison adds
item 5, and a comparison obtained through auxiliary descent adds item 6. Three further inputs
belong to the richer integral level-change and component package: the finite constant family
$({\rm AIH}_{\mathscr F})$ for Book 139's corrected constant rows,
$({\rm PRI}_{\rm type})$ for coefficient-one extreme type residues, and
$({\rm NU}_{\rm type})$ when a switched graph--definite carrier is used. They are required
where Chapters 4--5 invoke those conclusions, but they are not retroactively inferred from
the core comparison. If the core faithful carrier itself is moved to the definite side, all
of these applicable comparison hypotheses must be added; otherwise the core theorem remains
on the curve-new primary--companion carrier.

Under $({\rm TYPE}_v)$, Book 174 gives a strict primary--companion complex whose new
cohomology is projective over the declared coefficient base. Under $({\rm SUP}_v)$ it gives
full topological support on the selected global deformation ring at patched and retained
finite levels. Under $({\rm REC}_v)$, Book 170 gives at finite level a canonical surjection

$$
f:R^{\mathrm{nm}}\twoheadrightarrow\mathbb T^{\mathrm{nm}},
\tag{6.1}
$$

and the target is the faithful image on that carrier. These conclusions are conditional on
the named items. In particular, neither full support nor source reducedness is part of the
geometric datum.

### 6.2 Full support and the reduced image

The precise commutative algebra needed here does not assume that the source is reduced.

**Lemma 6.1 (full support and a reduced faithful image).** Let $R$ be noetherian, let $M$ be
a finite $R$-module, and let $T$ be the image of $R$ in $\operatorname{End}(M)$. If

$$
\operatorname{Supp}_R(M)=\operatorname{Spec}R
\tag{6.2}
$$

and $T$ is reduced, then

$$
\ker(R\twoheadrightarrow T)=\sqrt{(0)}
\quad\text{and}\quad
R_{\mathrm{red}}\xrightarrow{\sim}T.
\tag{6.3}
$$

**Proof.** Put $I=\operatorname{Ann}_R(M)$. Full support gives
$V(I)=\operatorname{Spec}R$, so $I$ is contained in every prime and hence
$I\subseteq\sqrt{(0)}$. Conversely, a nilpotent element of $R$ maps to a nilpotent element
of the reduced ring $T$ and therefore maps to zero. Thus $\sqrt{(0)}\subseteq I$. Since $T$
is the faithful image on $M$, the kernel is exactly $I$. $\square$

The finite Hecke order in Section 6.1 is reduced. It acts on a finite free
$\mathcal O$-carrier and so is $\mathcal O$-torsion-free; after inverting $\varpi$, generic
semisimplicity embeds it into the product of its characteristic-zero packet fields. A
nilpotent in the order is zero in that product and hence is $\mathcal O$-torsion; it must
already be zero. This argument does not automatically apply to an abstract patched
inverse-limit acting algebra.

### 6.3 The reduced comparison and the full-equality criterion

**Theorem 6.2 (conditional finite-level one-prime reduced $R=T$).** Assume
$({\rm AUT}_v)$, $({\rm TYPE}_v)$, $({\rm SUP}_v)$, and $({\rm REC}_v)$, adding
$({\rm RAY}_v)$ in the scalar family and $({\rm AUG}_Q)$ when an auxiliary patch is
descended. At the empty auxiliary level, and at every retained finite auxiliary level for
which these hypotheses hold, reciprocity induces a canonical isomorphism

$$
\boxed{
\bigl(R^{\mathrm{nm}}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T^{\mathrm{nm}}.
}
\tag{6.4}
$$

In the scalar family this gives both

$$
\bigl(R^{\mathrm{sp},1}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T^{\mathrm{sp},1}
\quad\text{and}\quad
\bigl(R_{\Lambda_v}^{\mathrm{sp},2}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T_{\Lambda_v}^{\mathrm{sp},2}.
\tag{6.5}
$$

**Proof strategy.** The type theorem supplies full topological support, while reciprocity
supplies the faithful reduced image. Lemma 6.1 then identifies the possible kernel exactly,
rather than assuming it absent.

**Proof.** On the direct sum of the primary and companion finite carriers, the kernel of
(6.1) is the source annihilator because the target is its faithful image. Hypothesis
$({\rm SUP}_v)$ gives (6.2) at each retained finite level. The finite target is reduced by
the torsion-free semisimple-generic embedding above. Lemma 6.1 proves (6.4), hence (6.5).
$\square$

At patched level, Book 174 still gives

$$
\operatorname{Ann}_{R_\infty}H^*(C_\infty)
\subseteq\sqrt{(0)}.
\tag{6.5a}
$$

Let $\mathbb T_\infty$ be the actual image of $R_\infty$ on the patched carrier. If
$\mathbb T_\infty$ is independently known to be reduced, Lemma 6.1 gives
$(R_\infty)_{\rm red}\simeq\mathbb T_\infty$. If instead $R_\infty$ is independently known
to be reduced, (6.5a) makes the action faithful and gives the full equality
$R_\infty\simeq\mathbb T_\infty$. No preceding source proves either reducedness statement
for this line-special patched problem.

**Corollary 6.3 (full finite-level one-prime equality criterion).** Under the scalar
finite-level hypotheses of Theorem 6.2, the following are equivalent:

1. $R^{\mathrm{sp},1}$ is reduced;
2. $R^{\mathrm{sp},1}\xrightarrow{\sim}\mathbb T^{\mathrm{sp},1}$;
3. $R_{\Lambda_v}^{\mathrm{sp},2}\xrightarrow{\sim}\mathbb T_{\Lambda_v}^{\mathrm{sp},2}$.

**Proof.** The equivalence of 1 and 2 is (6.5), since the target is reduced. Equations
(5.4) and (5.6) identify the map in 3 with the map in 2 tensored with $\Lambda_v$.
The group algebra is finite free and faithfully flat over $\mathcal O$, so the tensor map is
injective exactly when the conductor-one map is injective. $\square$

The local chart $R_0[[m]]$ can be reduced while its global quotient is nonreduced.
Equidimensionality, Cohen--Macaulayness, and a reduced Hecke image do not rule out a nilpotent
thickening in the source. No theorem in the declared source chain proves this global
reducedness. Thus (6.4)--(6.5), not an unconditional full equality, are the source-closed
finite-level conclusions. The patched alternatives are exactly those stated after (6.5a).
No congruence length or cotangent determinant is used to kill either kernel.

### 6.4 Descent to finite level and fixed characters

Book 174 proves full support again at each retained finite level. Theorem 6.2 can therefore
be applied directly after auxiliary augmentation. This avoids the generally unsafe
assumption that taking a reduced quotient commutes with quotienting by an augmentation ideal.
Projectivity of the one-prime new module shows that the carrier has no higher coefficient-base
Tor; exactness of the acting image remains the separate marked hypothesis in Section 6.1.

In the scalar-twist case let
$\chi:\Delta_v\to\mathcal O_\chi^\times$ be a character valued in a finite extension DVR.
The map $\Lambda_v\to\mathcal O_\chi$ is usually not flat, so (6.6) is not obtained by
blindly tensoring (6.5). Strict twisting instead gives

$$
R^{\mathrm{sp},2}_\chi
\simeq R^{\mathrm{sp},1}\widehat\otimes_{\mathcal O}\mathcal O_\chi,
\qquad
\mathbb T^{\mathrm{sp},2}_\chi
\simeq\mathbb T^{\mathrm{sp},1}\otimes_{\mathcal O}\mathcal O_\chi.
\tag{6.5b}
$$

Let $K$ be the kernel of the conductor-one comparison. By Theorem 6.2, $K$ is the
nilradical, hence is a nilpotent ideal because the source is noetherian. The extension
$\mathcal O_\chi/\mathcal O$ is finite free, so the kernel after the base change (6.5b) is
$K\otimes_{\mathcal O}\mathcal O_\chi$ and remains nilpotent. The target in (6.5b) is
$\mathcal O_\chi$-torsion-free with reduced generic fiber: in characteristic zero the tensor
of the finite separable packet algebras is again a product of finite separable algebras.
Thus the target is reduced. Its kernel contains every source nilpotent and, being itself
nilpotent, is contained in the source nilradical. Therefore

$$
\bigl(R^{\mathrm{sp},2}_\chi\bigr)_{\mathrm{red}}
\xrightarrow{\sim}
\mathbb T^{\mathrm{sp},2}_\chi.
\tag{6.6}
$$

For $\chi\ne1$, a point with nonzero monodromy has conductor two; for $\chi=1$, such a point
has conductor one. The determinant specializes to $\delta^{(1)}\chi^2$ in both deformation
and automorphic problems. If the conductor-one source is reduced, Corollary 6.3 upgrades
(6.6) and all of its character fibers to full equalities.

## 7. The modularity-lifting conclusion

### 7.1 The one-prime theorem

We now state the arithmetic theorem supplied by the selected conductor-two scalar family. It
does not require the global deformation ring to be reduced.

**Theorem 7.1 (conditional one-prime nonminimal modularity lifting).** Let the residual,
coefficient-prime, unchanged local, and automorphic data satisfy Chapter 3. Let
$v\nmid\ell$ satisfy $q_v\equiv1\pmod\ell$, and choose an actual global quotient
$\Delta_v$, the enhanced line and $W_v$-sign, and the scalar-twist determinant (3.3). Assume
$({\rm AUT}_v)$, $({\rm TYPE}_v)$, $({\rm SUP}_v)$, $({\rm REC}_v)$, and
$({\rm RAY}_v)$, as defined in Section 6.1, and also $({\rm AUG}_Q)$ if the finite problem is
obtained by auxiliary descent.

Let $\mathcal O'/\mathcal O$ be finite and let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{7.0}
$$

be a characteristic-zero point of the exact represented deformation problem on a retained
nontrivial character fiber. Assume that $\rho$ has nonzero rank-one monodromy at $v$. Then
$\rho$ is attached to a cuspidal
parallel-weight-two automorphic representation with the same determinant, the integral
finite-flat condition above $\ell$, every unchanged named local component, and the selected
line, sign, scalar character, and special component at $v$. Its conductor exponent at $v$ is
two.

**Proof strategy.** A point of a deformation ring over a domain kills the nilradical.
The reduced comparison therefore places the point on the faithful Hecke order; the type
carrier and the order-valued Galois representation then recover the exact automorphic packet.

**Proof.** Universality gives
$x_\rho:R_\chi^{\mathrm{sp},2}\to\mathcal O'$. Since $\mathcal O'$ is a domain,
$x_\rho$ factors through the reduced quotient. Equation (6.6) identifies that quotient with
$\mathbb T_\chi^{\mathrm{sp},2}$. The resulting Hecke character occurs in the actual
primary--companion carrier because this order is its faithful image. The type construction
gives the selected local packet, while Book 170's Hecke-valued representation and the
universal property identify its Galois representation with $\rho$. Formula (2.6), the
nontrivial conductor-one scalar character, and the assumed nonzero monodromy give conductor
exponent two. $\square$

For the trivial character, the same proof gives a conductor-one line-special modularity
statement when monodromy is nonzero. For a generic unramified-to-special change or a
$q_v\equiv-1$ full block, the formal reduced-image argument remains valid if all the named
type, support, augmentation, and reciprocity hypotheses of Section 6.1 have been independently
proved for that exact problem. Books 139 and 174 do not turn those other regimes into the
selected conductor-two scalar theorem.

### 7.2 Recovery of an automorphic representation

The factorization used in the proof is

$$
R_\chi^{\mathrm{sp},2}
\longrightarrow
\bigl(R_\chi^{\mathrm{sp},2}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T_\chi^{\mathrm{sp},2}
\longrightarrow\mathcal O'.
\tag{7.0a}
$$

After inverting $\varpi$, the last character selects a characteristic-zero factor of the
finite reduced Hecke algebra and hence an eigenpacket in the actual primary or companion
carrier.

At every good place,

$$
\operatorname{charpol}(\rho(\Phi_w);X)
=X^2-x(T_w)X+q_wx(S_w).
\tag{7.1}
$$

The same polynomial belongs to the Galois representation attached to the selected
parallel-weight-two packet. Frobenius density and Brauer--Nesbitt identify the
characteristic-zero representations. To identify their integral lattices, scale an
intertwiner so that it maps one stable $\mathcal O'$-lattice into the other but not into its
$\varpi'$-multiple. Its reduction has nonzero image. Residual absolute irreducibility makes
that image the whole residual module, and Nakayama's lemma makes the lattice map an
isomorphism.

The bad-place conclusions do not follow from (7.1). They follow because the map (3.5) was
defined only after the Hecke-valued representation had been shown to factor through every
represented local condition on all Artinian quotients. At places above $\ell$, this is the
integral finite-flat condition, not merely a statement about rational Hodge--Tate weights.

### 7.3 Coefficient extension

Types, residual roots, and tame character values may require a finite extension
$\mathcal O'/\mathcal O$. Every represented local problem used here is required to commute
with that extension after the chosen residual factor has been selected. Primary and companion
lattices, pairings, complexes, and faithful orders base-change as well.

An isomorphism whose ordinary scalar extension has been proved descends by faithful flatness.
For the reduced comparison, it is safer to apply Lemma 6.1 directly to the
coefficient-extended represented problem: support and the torsion-free generic embedding both
base-change, whereas formation of a reduced quotient is not silently commuted with every
ramified base change. Fitting ideals extend. Raw uniformizer-normalized lengths scale by the
ramification index and must not be reported as unchanged numbers.

Coefficient extension does not change $F$, $q_v$, the local conductor, or the congruence in
Section 2.4. In particular, enlarging coefficients cannot create a nontrivial $\ell$-power
character of $k_v^\times$ when $q_v\not\equiv1\pmod\ell$.

### 7.4 Solvable base change and descent

The class-field-theoretic reduction used in the FLT strategy chooses a finite solvable Galois
extension with prescribed finite Galois completions at finitely many places and with
prescribed linear disjointness. This construction can simplify local conditions and preserve
residual image, but it does not supply automorphy or any Ihara statement.

Before applying Theorem 7.1 over such an extension $L/F$, one must recheck cyclotomic
absolute irreducibility, the coefficient-prime unramified and finite-flat conditions, the
exact represented local components, stabilizer orders, the effective global ray quotient,
and every instance of the hypotheses in Section 6.1 over $L$. If a local residue degree is
$f$, the scalar congruence is tested using $q_v^f$, not the original cardinality.

The restricted problem must also still have exactly one active fixed nonminimal place for
Theorem 7.1. If several places of $L$ above a base place acquire active conditions, they are a
finite-set problem: all but one must be placed in genuinely verified spectator conditions, an
ordered chain must be proved, or the simultaneous hypotheses of Theorem 9.1 must be supplied.
Solvable base change does not turn those several places into a single edge.

Automorphy over $L$ does not descend merely from Galois invariance. Book 109 applies through a
prime-cyclic tower only when the restricted Galois representation stays irreducible, cyclic
base change and its image criterion apply at every step, strong multiplicity one and Galois
attachment are compatible, the full local parameters have admissible antecedents, and the
representation already defined over the lower field selects the quotient-character
correction. Under those hypotheses, recursive cyclic descent returns an automorphic
representation over $F$ with the required local data.

Thus the Skinner--Wiles class-field-theoretic construction supplies a controlled solvable
field; the one-prime theorem supplies automorphy over that field; and solvable descent returns
to the base only after its independent hypotheses have been verified.

### 7.5 Exact exceptional boundaries

The theorem begins at $\ell=7$ because that is the uniform residual-image range of the
declared Taylor--Wiles package. It makes no assertion at five from absolute irreducibility
alone. At two, sign idempotents and the fixed-determinant tangent complex change; at three,
the available uniform image and type arguments also require replacement.

An Eisenstein or reducible residual localization is excluded. In that setting the tree can
have degree-zero or character kernels, and traces do not determine extension classes. A
primitive wild type is excluded because the integral primary--companion and incidence models
used here have not been constructed for it.

At $q_v\equiv1$, root collision is handled only by the represented enhanced line and type
system. At $q_v\equiv-1$, the full matrix and both extension orientations are retained. A
single signed congruence factor is not asserted. If the selected source is not reduced, full
support identifies the annihilator with its nilradical; Theorem 6.2 still proves the reduced
comparison and Theorem 7.1 still proves characteristic-zero modularity, but full $R=T$ is not
asserted.

## 8. Two places and the first mixed obstruction

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

Even over a field, two injective maps can have an intersection larger than the image coming
from the lower-left corner. The product of the two Bruhat--Tits trees is contractible before
an arithmetic quotient is taken. Stabilizer cohomology can leave a mixed class after the
quotient, so contractibility alone does not prove exactness of (8.1).

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
adjunctions, the companion top module is then the full dual of $N_{v,w}^+$.

No current one-prime source proves

$$
\operatorname{Ob}_{v,w}=0
\tag{8.10}
$$

uniformly for every geometric pair from Chapter 3 satisfying the explicit one-prime
hypotheses, every actual spectator tuple, every auxiliary shadow, and both primary and
companion systems. Equation (8.10) is the first finite-set gap.

### 8.4 Further finite-set obligations

Even a proof of (8.10) would not finish the finite-set theorem. Two additional comparisons
are needed.

First, the product of the local coefficient-one node residues must equal the global
component-to-normalization morphism on the actual arithmetic square. A formal tensor of two
one-place residue maps does not identify that global connecting morphism or its mixed
component Tor terms.

Second, a boundary class must spread to every generic point of the named product of local
components. Separate full support on the $v$-component and on the $w$-component does not imply
support on their product: a module can meet both projections while lying only on diagonal
components. A simultaneous depth argument on the product chart is required.

Only after a coherent global cube, mixed exactness, product residue, and joint support have
been proved can one apply the finite-set criterion of Section 9.2. Simultaneous exact
augmentation and finite-set reciprocity are further inputs. They give reduced $R=T$ and
pointwise modularity; source reducedness or another nilpotent-control theorem is still required
for a full scheme-theoretic equality.

## 9. The finite-set and downstream interfaces

### 9.1 What iteration actually proves

Suppose a one-prime theorem is applied at $v$ and then at $w$. The second application is valid
only if every hypothesis is checked on the new intermediate carrier. In particular, one must
recheck the actual automorphic localization, $({\rm TIC})$ at the active place,
$({\rm TIH}_{\mathscr F})$, $({\rm SUP})$, the effective ray quotient, reciprocity, and exact
augmentation with the new actual spectator tuple. If the step invokes constant saturation,
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
complete hypotheses of Theorem 7.1 hold successively for an exhibited sequence of represented
one-place changes, automorphy propagates by induction. The conclusion belongs to that sequence;
pairwise hypotheses at the initial level do not prove it.

### 9.2 The hypotheses for a simultaneous theorem

For a finite set $P$, a simultaneous theorem requires one global cubical carrier with all
faces. The following hypotheses state exactly what is needed.

**Face hypotheses $({\rm FACE}_P)$.** Every actual face, with every spectator tuple and
auxiliary shadow, satisfies all applicable one-prime hypotheses in Section 6.1. This includes
both constant and type-Ihara families; a condition verified only before another quotient-new
operation is not reused afterward.

**Cubical comparison $({\rm CUBE}_P)$.** The face maps come from one global automorphic level
cube. Its iterated base-change squares are cartesian in the required derived sense, and its
total complex is identified with the derived tensor product of the face complexes over the
declared common acting or character base. Abstract one-prime complexes with matching ranks do
not supply this identification.

**Mixed exactness $({\rm MIX}_P)$.** At every retained shadow, the total complex is
concentrated in degree $|P|$ and its top cohomology is finite projective over the face base.
For two places this includes $\operatorname{Ob}_{v,w}=0$ in (8.10). For three or more places
it includes all higher mixed homology and higher-fold Tor-independence. Pairwise two-face
vanishing is not asserted to imply the higher conditions.

**Product residue $({\rm PROD}_P)$.** The coefficient-one product of the local extreme
residues is the global connecting morphism on the actual arithmetic cube. The derived tensor
of the component complexes retains every Néron component module and every branch Smith
correction. These component Tor groups are genuine semistable invariants and are not the same
as unwanted Tor over the automorphic face algebra.

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

**Simultaneous augmentation $({\rm AUG}_P)$.** Fixed-prime and Taylor--Wiles augmentations are
exact, commute in every order, and identify the represented deformation rings, total
complexes, pairings, and faithful acting orders for every subset of $P$. Exactness of modules
alone is not exactness of acting images. At scalar places an effective joint global ray
quotient onto $\prod_{v\in P_{\rm sc}}\Delta_v$ is supplied with every local, unit, central,
and archimedean compatibility; separate one-place quotients do not imply that joint
surjection. The resulting strict product-twist identity identifies every retained character
fiber with the common line-special problem after the required finite coefficient extension.
This clause is stated separately because a character quotient of a group algebra need not be
flat.

**Finite-set reciprocity $({\rm REC}_P)$.** One Hecke-valued representation factors
simultaneously through every represented local condition on every generic branch and every
Artinian quotient. The verified trace, determinant, type, line, sign, and diamond operators
generate the finite faithful order, which is $\mathcal O$-torsion-free with reduced generic
fiber.

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
and simultaneous augmentation supplies the finite-level carrier and faithful acting image.
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

### 9.3 The potential-modularity consumer

The immediate potential-modularity consumer produces a geometric specialization whose extra
semistable places are known only after the specialization has been chosen. Its lower residual
packet must then be moved to the exact local datum of the target Tate module.

The presently source-closed interface is consequently one of two forms:

1. the specialization has exactly one active place and satisfies every explicit hypothesis of
   Theorem 7.1; or
2. an ordered finite chain is exhibited, and every one-prime hypothesis is verified anew at
   each intermediate level.

Theorem 9.1 gives a third, simultaneous interface only after all of its displayed hypotheses
have been independently proved for the actual specialization. Separate local cleanliness
does not establish those hypotheses. In particular, a consumer may not cite the conditional
finite-set target as though (8.10), product residue, and joint support followed from the
one-prime sources.

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
verified one-prime chain is supplied, or every hypothesis of Theorem 9.1 has been proved.
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

## 10. Dependencies and conclusion

### 10.1 Exact source ledger

The direct mathematical sources used here have the following roles and retained limitations.

| source | result used | limitation retained here |
|---|---|---|
| Book 109 | recursive cyclic solvable descent selected by a representation already defined over the lower field | Galois invariance alone is not descent; irreducibility, image criteria, and full local antecedents are rechecked |
| Book 173 | neutral minimal modularity lifting and its coefficient-prime range | its equality is not applied to the conductor-one line-special ring with Kummer directions |
| Book 138 | enhanced special lines, primary and companion lattices, tame twists, and exceptional local charts | local lattices do not prove type incidence, type Ihara, primitive residue, or global support; primitive wild types are excluded |
| Book 139 | exact tree kernel (4.3), and conditional saturation, duality, Gram, component, and branch sequences | residual injectivity depends on $({\rm AIH}_{\mathscr F})$ at every actual constant flag level; it is not a type-Ihara theorem |
| Book 140 | conditional one-prime integral level change, node/definite comparison, equality of faithful orders, and signed Gram calculation | also requires node uniformization and generic support; proves no unconditional several-prime theorem; keeps the branch Smith correction separate |
| Book 170 | order-valued Galois representation, factorization through represented local conditions, and the surjection (3.5) | requires every generic branch, integral coefficient-prime realization, reduced generic order, exact trace generation, and the conditional Book 140 comparison whenever used |
| Book 174 | enhanced one-prime type complex, scalar $q\equiv1$ family, primitive residue, one-prime support, and exact fixed-prime augmentation | $({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, $({\rm NU}_{\rm type})$, and $({\rm SUP}_v)$ are separately named hypotheses; support is topological and only one-place |
| Book 175 | finite-level reduced one-prime comparison and pointwise characteristic-zero modularity in the scalar family | full finite-level $R=T$ requires global reducedness; no patched reduced comparison follows without reducedness of the patched image, and no finite-set theorem is supplied |

The exact direct-dependency row is

$$
176\mid 109,173,138,139,140,170,175,174.
\tag{10.0}
$$

Within Books 138--141, 151, 163, and 170--176, Books 141, 151, and 171--172 enter transitively through the type-support
and one-prime patching packages. Book 163 is a downstream arithmetic synthesis, not a proof
source. The mixed reduction (8.3)--(8.10) is proved here; its missing vanishing, product
residue, and joint support are not imported from a later consumer.

### 10.2 Logical and normalization checks

The proof order is rigid:

1. the represented local data are fixed without assuming Ihara or support;
2. $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$ give the actual typed split
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
8. finite-level source reducedness, if independently supplied, upgrades that comparison to
   full $R=T$, whereas a patched reduced comparison first needs a reduced patched acting
   image and a full patched equality needs a reduced patched source; and
9. numerical consequences are derived only after the relevant comparison has been proved.

Thus no later ring equality proves an earlier Ihara or support statement, and no determinant
valuation is used to kill a deformation kernel. At two places, one-place injectivity is used
only to derive (8.6); it is not applied again to the quotient in (8.4). For a finite set,
joint support is assumed only after mixed exactness and product residue have constructed the
actual total carrier.

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
remain conditional. The type rows have a separate first obstruction:
$({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$. Their split complex does not follow from
(10.1). Coefficient-one extreme residues additionally require
$({\rm PRI}_{\rm type})$, and a switched graph--definite comparison additionally requires
$({\rm AIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$,
$({\rm NU}_{\rm type})$, and Book 140's node-uniformization, generic-support, and
common-kernel hypotheses.

For the core finite-level scalar theorem, the exact independent conditional inputs are
$({\rm AUT}_v)$, $({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$,
$({\rm SUP}_v)$, $({\rm REC}_v)$, and $({\rm RAY}_v)$, with
$({\rm AUG}_Q)$ whenever an auxiliary patch is descended. Thus Theorem 7.1 remains
conditional even if (10.1) is proved. Conversely, once this core list is supplied, its formal
reduced comparison does not require one to smuggle $({\rm AIH}_{\mathscr F})$ or
$({\rm PRI}_{\rm type})$ into the word “support.” An argument formulated only for separated
roots does not supply the $q_v\equiv1\pmod\ell$ enhanced-line case.

The additional one-prime hypothesis for full finite-level scheme-theoretic $R=T$ is precisely

$$
R^{\mathrm{sp},1}\text{ is reduced}.
\tag{10.1a}
$$

Neither local reducedness of the special chart nor minimal $R=T$ proves (10.1a).
At patched level, reduced $R=T$ instead requires the actual patched acting image to be
reduced; full patched $R=T$ follows from reducedness of the patched deformation ring or an
independent theorem killing its annihilator. The existing source chain proves neither.

For two or more places, one must first construct $({\rm FACE}_P)$ and the actual derived
global cube $({\rm CUBE}_P)$ at every spectator tuple and auxiliary shadow. Given that cube,
the first additional homological obstruction at a pair is

$$
\operatorname{Ob}_{v,w}=0
\tag{10.2}
$$

for every actual spectator tuple and auxiliary shadow. After (10.2),
$({\rm PROD}_P)$ and $({\rm JSUP}_P)$ are still required. At three or more places, pairwise
versions of (10.2) do not replace the higher mixed homology and Tor-independence in
$({\rm MIX}_P)$. Simultaneous character and auxiliary specialization
$({\rm AUG}_P)$---including an effective joint global ray quotient, strict product twisting,
and exact acting images---and finite-set reciprocity $({\rm REC}_P)$ are further inputs. Under this
entire list, Theorem 9.1 proves finite-level reduced $R=T$ and pointwise modularity; full
finite-set $R=T$ additionally requires $R_P$ to be reduced. None of the simultaneous
hypotheses follows from the present one-prime source chain.

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
finite-level reducedness is the exact extra input for full finite-level $R=T$; patched
reducedness has the separate boundary recorded in Section 6.3.

The local arithmetic has a sharp division. Generic level raising with
$q_v\not\equiv\pm1\pmod\ell$ produces a conductor-one special packet. A scalar
$\ell$-power tame twist exists only at $q_v\equiv1\pmod\ell$ and moves a special packet from
conductor one to conductor two while changing the determinant by the square of the character.
At $q_v\equiv-1\pmod\ell$, the full primary--companion and Smith blocks must remain visible.

At several places the new object is a cube. Its first two-place defect is the explicit module
$\operatorname{Ob}_{v,w}$, the first homology of the total incidence square. Edgewise
saturation does not make it vanish. Product residue and joint component support are further
mixed conclusions, not definitions. Theorem 9.1 proves the finite-set modularity conclusion
when the actual face package, derived global cube, mixed exactness, product residue, joint
support, simultaneous augmentation, and finite-set reciprocity are all supplied. Pairwise
one-prime data do not supply those hypotheses. The source chain therefore gives a bounded
conditional one-prime theorem and an exact conditional finite-set interface without
pretending that the unresolved geometric inputs are already available.
