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

Chapters 4--7 are an import boundary. Book 139 owns the constant-coefficient tree kernel and
conditional saturated Ihara package; Book 174 owns the actual typed incidence complexes,
primitive residues, enhanced component support, and strict augmentation; Book 175 owns the
finite-level reduced one-prime comparison and characteristic-zero modularity. The present book
uses those packages to formulate the new several-place problem in Chapters 8--9.

### 4.1 The exact residual kernel

Book 139, Theorem 6.1 identifies the residual constant-coefficient kernel with the localized
arithmetic congruence-character module. It is not zero by formal tree contractibility.

### 4.2 The abelian Ihara hypothesis

The vanishing $({\rm AIH}_{\mathscr F})$ must hold at every actual constant flag level used in
the construction. Under it, Book 139, Theorems 7.1, 10.2, 12.1, and 14.1 give saturation,
component control, new-quotient duality, and the exact Gram package. None is a typed Ihara
theorem.

### 4.3 Consequences after the hypothesis is supplied

Only after $({\rm AIH}_{\mathscr F})$ is supplied may a constant old image be called primitive
and its quotient finite free. Book 174 separately requires $({\rm TIC}_v)$ and
$({\rm TIH}_{\mathscr F})$ for the primary and companion type shadows.

### 4.4 Component and branch corrections

Book 139's Néron component module and branch Smith correction remain in the corrected
filtration. They are not identified with coefficient-base Tor and are not discarded when the
typed complex is formed.

## 5. The one-prime type complex

### 5.1 Primary and companion lattices

The actual primary and companion sheaves, their flag representations, and the coefficient-one
incidence maps are those of Book 174, Chapters 3--4. For later compatibility we denote the
resulting strict complexes by $C_v^+$ and $C_v^-$.

### 5.2 The incidence complex and its Tor term

**Imported theorem 5.1.** Under $({\rm TIC}_v)$ and
$({\rm TIH}_{\mathscr F})$, Book 174, Theorem 5.2 proves split amplitude and projectivity of the
one-prime new cohomology over the declared coefficient base. Consequently all coefficient-base
Tor vanishes. This does not imply the mixed two-place vanishing defined in Chapter 8.

### 5.3 The scalar-twist face

Book 174, Chapter 9 constructs the strict scalar-twist identity only after an effective global
ray quotient and the exact determinant-square identity have been supplied. A character fiber of
a group algebra is not assumed flat.

### 5.4 Support is not faithfulness

Book 174, Theorem 8.3 gives full topological support under the separate five-clause datum
$({\rm SUP}_v)$. For a noetherian source $R$ and carrier $M$ this says only

$$
\operatorname{Ann}_R(M)\subseteq\sqrt{(0)}.
\tag{5.7}
$$

It does not kill nilpotents or prove a full ring equality.

## 6. The conditional one-prime R=T theorem

### 6.1 The explicit comparison hypotheses

For compatibility with earlier citations, the one-prime package consists of the following
separate inputs, in exactly the sense of Books 174--175:

1. $({\rm AUT}_v)$: the actual non-Eisenstein primary--companion automorphic localization;
2. $({\rm TYPE}_v)$: $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$ at every retained shadow;
3. $({\rm SUP}_v)$: the marked boundary, unique-component, nonzero-carrier, and depth datum of
   Book 174;
4. $({\rm REC}_v)$: one order-valued representation on every generic branch, all-Artinian
   factorization through the represented local conditions, and generation of the faithful order
   by the verified operators;
5. $({\rm RAY}_v)$ for a scalar family: an effective global ray quotient, strict twist
   identities, and the determinant square; and
6. $({\rm AUG}_Q)$ when auxiliary patching is used: exact augmentation of deformation rings,
   complexes, pairings, actions, and faithful acting orders.

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

**Theorem 6.2 (conditional finite-level one-prime reduced $R=T$; compatibility alias).** Under
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

### 6.4 Descent to finite level and fixed characters

Book 175, Chapter 5 proves the conditional patched criterion and exact augmentation boundary.
Its Chapter 6 treats scalar and vexing fibers without commuting reduction through a nonflat
character quotient. Those conclusions are imported with their source-reducedness limitations.

## 7. The modularity-lifting conclusion

### 7.1 The one-prime theorem

**Theorem 7.1 (conditional one-prime nonminimal modularity lifting; compatibility alias).** This
is Book 175, Theorem 7.1. Under the exact Section 6.1 hypotheses, every characteristic-zero point
of the represented one-prime problem is attached to a cuspidal parallel-weight-two automorphic
representation with the same determinant, coefficient-prime finite-flat condition, unchanged
local components, and selected line, sign, scalar character, and special component. At a
nontrivial scalar-character fiber with nonzero monodromy, the conductor exponent is two.

### 7.2 Recovery of an automorphic representation

A point over a DVR kills the nilradical and therefore factors through (6.4). The actual faithful
carrier and Book 170's order-valued representation recover the eigenpacket and its Galois
representation. Bad-place conclusions come from prior integral local factorization, not from
good Frobenius traces.

### 7.3 Coefficient extension

Book 175 retains coefficient extension only after selecting the residual factor and base-changing
every represented local problem, type lattice, pairing, complex, and faithful order. Raw
uniformizer lengths scale with ramification.

### 7.4 Solvable base change and descent

Book 175, Section 7.3 imports solvable descent only after irreducibility, local antecedents,
image criteria, and cyclic descent are checked at every step. Splitting one base place into
several active places creates the finite-set problem below.

### 7.5 Exact exceptional boundaries

The one-prime theorem remains conditional in the scalar line-special range, starts uniformly at
$\ell\ge7$, excludes Eisenstein and primitive-wild localizations, and proves only reduced
finite-level $R=T$ unless global source reducedness is independently known. These are source
boundaries, not new hypotheses invented here.

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
and one-prime patching packages. Book 164 is a downstream arithmetic synthesis, not a proof
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
