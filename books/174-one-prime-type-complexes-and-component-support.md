# One-Prime Type Complexes and Component Support

## Contents

- [1. Purpose and logical status](#1-purpose-and-logical-status)
- [2. The clean one-prime datum](#2-the-clean-one-prime-datum)
- [3. Actual flag and type coefficient systems](#3-actual-flag-and-type-coefficient-systems)
- [4. Perfect cohomology and the one-prime complexes](#4-perfect-cohomology-and-the-one-prime-complexes)
- [5. Type Ihara and the localized abelian input](#5-type-ihara-and-the-localized-abelian-input)
- [6. Nearby cycles, graph terms, and the branch correction](#6-nearby-cycles-graph-terms-and-the-branch-correction)
- [7. The enhanced special component](#7-the-enhanced-special-component)
- [8. Support on the named component](#8-support-on-the-named-component)
- [9. Scalar twisting and exact augmentation](#9-scalar-twisting-and-exact-augmentation)
- [10. Determinant and adjoint ledger](#10-determinant-and-adjoint-ledger)
- [11. The reusable one-prime theorem](#11-the-reusable-one-prime-theorem)
- [12. Scope, dependencies, and boundaries](#12-scope-dependencies-and-boundaries)

## 1. Purpose and logical status

### 1.1 The object needed later

Let $F$ be totally real, let $\ell\geq7$, and let $v\nmid\ell$ be a finite place with
residue cardinality $q=q_v$. At hyperspecial and adjacent Iwahori level there are two
degeneracy maps. After applying the selected type coefficient system they give

$$
d_v^+:P_0^{+,\oplus2}\longrightarrow P_1^+.
\tag{1.1}
$$

The one-prime primary object is the strict complex

$$
C_v^+=\left[P_0^{+,\oplus2}\xrightarrow{d_v^+}P_1^+\right]
\tag{1.2}
$$

in cohomological degrees $0,1$. Its companion is the adjoint norm complex

$$
C_v^-=\left[P_1^-\xrightarrow{d_v^-}P_0^{-,\oplus2}\right].
\tag{1.3}
$$

The complex, rather than only its cokernel, is the stable object under a change of coefficient
ring. If $A\to B$ is not flat, the degree-zero cohomology of
$C_v^+\otimes_A^LB$ can contain

$$
\operatorname{Tor}_1^A(H^1(C_v^+),B).
\tag{1.4}
$$

The aim is a reusable one-place object with actual coefficient sheaves, strict projective
terms, the derived face maps, the corrected component complex, and exact one-place
augmentation. We do not develop arbitrary types or arbitrary PEL cohomology. The coefficient
systems are the quotient and augmentation Steinberg lattices and their scalar tame twists in
the compact weight-two curve range.

### 1.2 The exact Book 139 hypothesis

Let $\mathscr F_v(Q)$ be the finite diagram of constant-coefficient Shimura curves obtained by
replacing the quotient or augmentation Steinberg coefficient in the two vertex levels, the
edge level, and their adjoint companions by the permutation flag resolution. When a scalar
twist is present, pass to the actual global ray cover on which its rank-one system is trivial
and apply Shapiro; thus the diagram contains constant-coefficient curves with the real tame and
auxiliary spectator levels, not a nominal local character. Every object of this diagram has a
norm-one $S$-arithmetic group $\Gamma_D^v$, a prime-to-$\ell$ descent group $\Delta_D$, and the
relevant non-Eisenstein maximal ideal $\mathfrak m_D$.

**Hypothesis $({\rm AIH}_{\mathscr F})$.** For every $D\in\mathscr F_v(Q)$,

$$
\left(H^1_{\rm nc}(\Gamma_D^v,k)^{\Delta_D}\right)_{\mathfrak m_D}=0.
\tag{1.5}
$$

This is exactly Book 139's localized abelian Ihara condition
$({\rm AIH})_{v,\mathfrak m_D}$ at each constant level used by flag excision. Under (1.5),
Book 139, Theorem 14.1 gives residual injectivity, integral saturation, and its corrected
normalization and component filtration at each such level. It does not prove (1.5). Its missing
uniform theorem $({\rm AC}^{\rm loc}_\ell)$ would supply all these instances at once, but a full
congruence-subgroup property is stronger than is needed here.

Thus every conclusion imported from Book 139 is conditional on the finite list (1.5), not on a
fictitious future unconditional version of that book. A datum for which the listed vanishings
have been proved satisfies the constant-coefficient part of the hypotheses below; the separate
type conditions of Section 1.3 must still be checked. Non-Eisenstein localization and strong
approximation alone do not imply (1.5).

### 1.3 What is and is not proved here

This book proves the following one-place implications.  The labels
$({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$, and $({\rm PRI}_{\rm type})$ continue to name
three different assertions: incidence descent, residual old-map injectivity, and filtered
primitive residue.  For the actual quotient/augmentation rows they are proved below, in that
order, from the clean datum and $({\rm AIH}_{\mathscr F})$.  The hypotheses
$({\rm NU}_{\rm type})$ and $({\rm SUP}_v)$ remain separate: the first governs only the
graph--definite comparison and the second governs component support.

1. Book 122, Corollary 9.11 supplies the principal complete-local stabilizer calculation and
   the theorem $({\rm TPE}_v)$ below.  Proposition 3.0B proves the required coarse descent
   from the actual geometric stabilizers; the possibly nonunit order of the flag group is
   irrelevant.  Proposition 5.0B then uses the fixed/moving Bruhat decomposition, averaging
   only over the $q$-element affine orbit, to prove the quotient-new injection (5.0d) when
   $q\equiv-1\pmod\ell$.  Together with Proposition 5.0 this proves
   $({\rm TIH}_{\mathscr F})$ in every range covered by $({\rm AIH}_{\mathscr F})$.
2. The primary map is a split injection over the complete local coefficient algebra, so its
   new module is finite projective and every tame or auxiliary derived face has zero positive
   Tor.
3. The primary and companion complexes are perfect adjoint duals.
4. Proposition 6.0B applies type-Ihara only after Proposition 5.0B and proves the strict
   filtered-cofiber comparison (6.0d).  Thus the extreme nearby-cycle residues are primitive
   with coefficient one, while the normalized-branch correction
   $\mathcal C_{\mathrm{br},v}$ remains in the middle filtration.
5. On the actual component-routed principal cover, Book 125's characteristic-zero packet
   decomposition and the typed filtration prove equality of the curve-new and graph generic
   Hecke kernels; torsion-free contraction then identifies their integral faithful image
   orders, so no extra type-specific generic-residue or faithful-order hypothesis remains.
6. Under the explicit boundary-chart and depth hypotheses of Chapter 8, the complex has full
   topological support on the named enhanced special component; the scalar-twisted face
   additionally requires the genuine global ray quotient.
7. A genuine global scalar twist makes fixed-prime augmentation strict for deformation rings,
   complexes, new modules, pairings, and faithful acting orders.

These implications are not collapsed into one hypothesis.  Proposition 3.0B proves
$({\rm TIC}_v)$ from neatness and actual stabilizer descent, independently of (1.5).
Book 139 still treats only constant coefficients, for which cocycles are homomorphisms;
Proposition 5.0 first reduces the type assertion to the exact map (5.0d), and Proposition
5.0A identifies its nonbanal form with integral new-cokernel primitivity.  Proposition 5.0B
then proves that primitivity by comparing fixed evaluation with the normalized moving-orbit
trace.  Proposition 6.0 proves primitive type residue in the projector range, Proposition
6.0A removes the generic old quotient from the nonbanal problem, and Proposition 6.0B proves
the remaining filtered-cofiber comparison.  No rational flag projector is used in either
nonbanal argument.
Section 3.4 reduces the typed parahoric extension to the principal-node and stabilizer theorem
$({\rm PNS}_v)$.  For the coefficient rows of this book that theorem is now proved by Book
122, Corollary 9.11.  Normalization of the actual tower, its ray factor, and the
finite-wild/procyclic ramified nearby-cycle complex are proved.  Book 122, Proposition 9.3
proves $({\rm DLB}_1)$, and (9.29k)--(9.29l) prove the active full-Drinfeld normalization at
every finite depth and its intermediate invariant rings.  Equations (9.29r)--(9.29x) further
compute the raw higher branch set, inertia, inseparable residue degree, node-annular complexes,
and boundary stabilizers.  Equations (9.29b)--(9.29i),
(9.29n)--(9.29q), and Lemma 3.0A force the level-one stabilizers, exact wild-invariant
extreme lines, node routing, constant-extreme-line generization, multiplicity one,
and retained level-one Hecke route.  Book 122, Proposition 9.5 now computes the invariant
residue fields, Cartier multiplicities and active groups and reduces the normalized compositum
to the actual factorization of $T^c-\bar u^{-1}$ over each residue-compositum factor.
Proposition 9.6 factors every completed endpoint and blowup chart from its actual valuation,
leading coefficient, and tame subgroups; Proposition 9.7 gives the exact Milnor-tube formalism;
and Proposition 9.8 proves $({\rm RGC}_v)$.  Proposition 9.9 supplies the strict ray field
$F_v(\pi_v^{1/e_v})$, vertical unit $1$, endpoint triples
$(q_v-1,q_v(q_v-1),\gamma_L)$ and
$(q_v-1,q_v^2-1,\gamma_L),(q_v^2-1,q_v-1,\gamma_L)$.  If $h$ is the
order of $[\gamma_L]$, it gives the $e_v/h$ degree-$h$ factors of
$Z^{e_v}-\gamma_L^{-1}$ and the degree-$e_v/h$ active/ray intersection.  Proposition 9.10 computes the actual branch and conductor tubes and their
generization maps; Corollary 9.11 proves $({\rm KBL}_v)_{\rm act}$,
$({\rm BTK}_v)_{\rm act}$, $({\rm HDB}_v)_{\rm act}$, and
$({\rm PNS}_v)_{\rm act}$.  Proposition 9.4 supplies the actual-common-factor node routing,
multiplicity and expansion one, and Hecke/transpose compatibility.
The raw principal cover is explicitly wild.
Book 140 lists the same extension, pull--norm, and type-specific residual inputs. Its
constant-coefficient generic-support equality is proved in Book 140, Section 8.3, from Book
125. Proposition 6.3 below proves the typed generic-residue comparison from Book 125 after the
typed filtration has been established; it is not another hypothesis. Node uniformization
remains datum-specific.  Lemma 6.1A shows that the type transport is formal from a
superspecial classification formulated as an equivalence of flagged node groupoids; the
classification itself remains missing.  Chapter 7 proves the named local special closure, and
Section 8.2 proves that the minimal, boundary, and special problems may be patched on one
marked diagonal with their common boundary quotient retained.  The remaining relative
Cartier-switch transversality--nonvanishing of the lower boundary equation and formal
smoothness of the special relaxation, with its scalar-block analogue--is the separate
one-prime hypothesis $({\rm BCD}_v)$ isolated in Chapter 8. The book does not construct a
canonical chain map from a Galois cotangent complex to an automorphic Gram complex before
$R=T$. It does not delete a Néron component group or a branch correction, and it never promotes
one-place support to simultaneous support at several places.

## 2. The clean one-prime datum

### 2.1 Global and automorphic data

Let $(\mathcal O,\varpi,k,E)$ be a complete DVR, its uniformizer, residue field, and fraction
field, with $\operatorname{char}k=\ell\geq7$. Fix a continuous, totally odd representation

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{2.1}
$$

which is absolutely irreducible and remains absolutely irreducible over $F(\zeta_\ell)$. Fix
a determinant lift $\delta$. The conditions away from $v$ are those of the represented clean
minimal problem of Books 171--172.

Choose a division quaternion algebra split at exactly one real place and split at $v$. Choose a
proper correspondence-stable union of compact weight-two Shimura curves. The level is neat, or
is descended from a neat cover through a group of order invertible in $\mathcal O$. At $v$ the
lower level is hyperspecial and the upper level is the standard Iwahori. The rank-two PEL local
model is the verified incidence model of Book 122, so its strict completed nodal chart is

$$
xy=\pi_v.
\tag{2.2}
$$

All Hecke localizations are non-Eisenstein, contain no automorphic character packet, and are
paired with their adjoint companion localizations. Primary means the declared generalized
residual factor. Companion means its inverse-character adjoint factor; it never means a second
copy of the primary factor.

### 2.2 Coefficient algebras

At a scalar-twist place the ray quotient is chosen strictly, as follows.  Put

$$
e_v=\ell^{\operatorname{ord}_\ell(q_v-1)},\qquad
\Delta_v=C_{e_v}.                                         \tag{2.2a}
$$

Fix a protected finite set $S_0$ containing $v$, the places above $\ell$, and every place
already ramified in the clean datum.  Under local reciprocity prescribe at $v$ the quotient

$$
F_v^\times\longrightarrow k_v^\times
\longrightarrow k_v^\times/(k_v^\times)^{e_v}\simeq C_{e_v},
                                                               \tag{2.2b}
$$

where a uniformizer maps to $1$, and prescribe the trivial character at
$S_0\setminus\{v\}$.  Since $\ell\ge7$, the exponent $e_v$ is odd, so Book 6,
Theorem 6.1 and the non-Wang alternative immediately following it supply a global character

$$
c_v^{\rm ray}:G_F\longrightarrow\Delta_v                 \tag{2.2c}
$$

with these localizations.  Its order is exactly $e_v$.  Let $\mathfrak f_v$ be its conductor.
Then (2.2c) factors through the effective quotient
$\operatorname{Cl}_{\mathfrak f_v}(F)\twoheadrightarrow\Delta_v$; consequently all global-unit,
central, and archimedean compatibilities are satisfied rather than assumed.  Any additional
finite places in $\mathfrak f_v$ are inserted in the fixed spectator level, with the local
deformation condition transported by the same twist, and every Taylor--Wiles set is chosen
disjoint from them.  This finite enlargement is part of the clean datum.

Because $e_v\mid q_v-1$, Teichmuller lifting gives $\mu_{e_v}\subset F_v$.  The local field
cut out by (2.2b) is

$$
F_v'=F_v(\varpi_v),\qquad \varpi_v^{e_v}=\pi_v,            \tag{2.2d}
$$

so local inertia maps isomorphically onto $\Delta_v$ and the vertical Kummer unit is $1$.
This is the strict ray datum of Book 122, Proposition 9.9.  It is a construction of the
quotient used below, not the globalization of an arbitrary nominal local character.  Put

$$
\Lambda_v=\mathcal O[\Delta_v],
\qquad
\boldsymbol\chi_v:
G_F\xrightarrow{c_v^{\rm ray}}\Delta_v
\longrightarrow\Lambda_v^\times.
\tag{2.3}
$$

The coefficient line is, by definition, the pullback of this global Galois system.  Book 122,
Proposition 9.9 uses canonical component reciprocity to identify its generic pullback with the
automorphic line $\boldsymbol\chi_v^{\rm aut}\circ\det$.  Hence the determinant system is
trait-pulled at $v$ and the ray projection formula is available; no further geometric ray
identification is being assumed.

At Taylor--Wiles level $Q$, let $\Lambda_Q=\mathcal O[\Delta_Q]$ and

$$
A_Q=\Lambda_v\widehat\otimes_{\mathcal O}\Lambda_Q.
\tag{2.4}
$$

If no scalar twist is present, omit $\Lambda_v$. Because the groups are finite $\ell$-groups,
$A_Q$ is complete local. Let $\iota$ be the involution sending every group element to its
inverse. Fixed-prime augmentation is

$$
\epsilon_v:\Lambda_v\longrightarrow\mathcal O,
\tag{2.5}
$$

and is distinct from auxiliary augmentation $\epsilon_Q$.

### 2.3 Frobenius, determinant, and adjoints

Good Hecke operators are unnormalized right double cosets. For geometric Frobenius $\Phi_w$,
the Hecke-valued representation of Book 170 has polynomial

$$
X^2-T_wX+q_wS_w.
\tag{2.6}
$$

At $v$, pullback on one coefficient system is adjoint to finite-flat norm on the companion.
On either fixed coefficient system the same geometric pull and norm maps may be composed. Write

$$
T_{01}=r_0^+d_1^+,
\qquad
T_{10}=r_1^+d_0^+=T_{01}^*.
\tag{2.7}
$$

In the usual central orientation $T_{01}=T_v$ and
$T_{10}=S_v^{-1}T_v$. We do not force a symmetric matrix before choosing a square root of the
central operator.

For local deformation charts we use arithmetic Frobenius $\phi=\Phi_v^{-1}$ and a tame
generator $\tau$ satisfying

$$
\phi\tau\phi^{-1}=\tau^q.
\tag{2.8}
$$

Thus special monodromy satisfies $FNF^{-1}=qN$ for $F=\rho(\phi)$; with geometric
Frobenius the factor is $q^{-1}$. Scalar Galois twisting changes the determinant by

$$
\det(\rho\otimes\boldsymbol\chi_v)
=\det(\rho)\boldsymbol\chi_v^2.
\tag{2.9}
$$

The square in (2.9) is compulsory.

### 2.4 The three clean local ranges

The theorem keeps three cases separate.

| residue relation | retained local datum | forbidden shortcut |
|---|---|---|
| $q\not\equiv\pm1\pmod\ell$ | an enhanced special line and an integral sign block | none beyond the declared normalization |
| $q\equiv1\pmod\ell$ in the scalar-residual branch | the scalar flag, both line characters, Kummer directions, and an integral $W_v$-sign | a Frobenius-root projector |
| $q\equiv-1\pmod\ell$ | distinct special lines, the full Gram block, and both primary--companion extension orientations | division by either signed Gram factor |

Primitive wild types, noncompact boundary cohomology, $v\mid\ell$, and descent through an
$\ell$-divisible stabilizer are outside the theorem.
The middle row is the scalar-residual subrange treated in Section 7.2; a different congruent
nonsemisimple Frobenius shape requires its own represented enhanced chart.

## 3. Actual flag and type coefficient systems

### 3.1 The finite flag representation is not a cover of the integral model

Put

$$
K_v=\operatorname{GL}_2(\mathcal O_{F_v}),
\qquad
\overline K_v=\operatorname{GL}_2(k_v),
\qquad
X_v^{\mathrm{fl}}=\mathbf P^1(k_v).
\tag{3.1}
$$

Let

$$
P_v=\mathcal O[X_v^{\mathrm{fl}}],
\qquad
\mathbf1=\sum_{x\in X_v^{\mathrm{fl}}}e_x,
\qquad
\operatorname{aug}\!\left(\sum a_xe_x\right)=\sum a_x.
\tag{3.2}
$$

Book 138's two integral Steinberg lattices are

$$
\operatorname{St}_v^+=P_v/\mathcal O\mathbf1,
\qquad
\operatorname{St}_v^-=\ker(\operatorname{aug}:P_v\to\mathcal O).
\tag{3.3}
$$

They are free of rank $q$. The dot product descends to a perfect pairing

$$
\operatorname{St}_v^+\times\operatorname{St}_v^-
\longrightarrow\mathcal O.
\tag{3.4}
$$

No factor $1/(q+1)$ occurs. If $\ell\mid q+1$, constants form a submodule of the reduction of
$\operatorname{St}_v^-$ and a quotient of the reduction of $\operatorname{St}_v^+$; these are
oppositely oriented nonsplit extensions.

The set $X_v^{\mathrm{fl}}$ is the finite flag set used in the representation (3.2). It is not
the geometric fiber of a finite étale degree-$q+1$ cover of the semistable PEL model. At the
bad prime the integral flag moduli is the incidence local model, and its strata ramify and
coalesce. Treating it as a constant étale cover would make the nearby-cycle argument false.

### 3.2 Associated sheaves on the actual Shimura tower

Choose a normal principal subgroup separately inside each adjacent vertex group and the edge
group, then a finite common refinement for the two legs.  Take the effective finite Galois
closure of this finite generic diagram.  The objectwise principal covers have finite deck
groups $H_0,H_1,H_e$, and the common closure trivializes all of them.  No single open compact
subgroup is assumed normal in both adjacent maximal parahorics. If $W$ is a finite free
representation of one of these deck quotients, let

$$
\mathscr V_j(W)
\tag{3.5}
$$

denote the lisse sheaf obtained by effective finite-étale descent from the corresponding cover.
Equivalently, inflate $W$ to the relevant quotient of the common Galois group; its kernel acts
trivially, so this does not change the descended sheaf.
This is the associated sheaf of the torsor. It is not defined by applying an exactness claim to
ordinary invariants of an arbitrary group module; étale-locally on the base it is literally the
constant sheaf with fiber $W$, so descent is exact without averaging.

The permutation sheaf is $\mathscr V(P_v)$, and the exact representation sequences give exact
sequences of lisse sheaves

$$
0\longrightarrow\mathscr V(\mathcal O)
\longrightarrow\mathscr V(P_v)
\longrightarrow\mathscr V(\operatorname{St}_v^+)
\longrightarrow0,
\tag{3.6}
$$

$$
0\longrightarrow\mathscr V(\operatorname{St}_v^-)
\longrightarrow\mathscr V(P_v)
\longrightarrow\mathscr V(\mathcal O)
\longrightarrow0.
\tag{3.7}
$$

The two degeneracy legs are morphisms of the finite-level Shimura towers. The standard
intertwiners between the transported vertex and edge representations therefore give honest
maps between the sheaves (3.5). This, rather than a rational type projector, defines the two
maps used in (1.1).

### 3.3 Primary and companion twist typing

Let $\boldsymbol\chi_v^{\rm aut}$ be the unit-valued compact character obtained from
$\boldsymbol\chi_v$ by the fixed global reciprocity convention. Define

$$
W_v^+
=\operatorname{St}_v^+\otimes_{\mathcal O}A_Q
   (\boldsymbol\chi_v^{\rm aut}\circ\det),
\tag{3.8}
$$

$$
W_v^-
=\operatorname{St}_v^-\otimes_{\mathcal O}A_Q
   ((\boldsymbol\chi_v^{\rm aut})^{-1}\circ\det).
\tag{3.9}
$$

Auxiliary diamonds act regularly on the primary system and through $\iota$ on the companion.
The pairing (3.4) then gives an $A_Q$-perfect pairing

$$
W_v^+\times W_v^-\longrightarrow A_Q,
\qquad
\langle ax,by\rangle=a\,\iota(b)\langle x,y\rangle.
\tag{3.10}
$$

Equivalently, after viewing the companion through $\iota$, the pairing is $A_Q$-bilinear.
At a character $\chi$, the primary specializes to
$\operatorname{St}^+\otimes(\chi\circ\det)$ and the companion to
$\operatorname{St}^-\otimes(\chi^{-1}\circ\det)$. Pairing two copies carrying $\chi$ would
have the wrong diamond character and is not used.

Let $\mathscr S_j^+=\mathscr V_j(W_v^+)$ and
$\mathscr S_j^-=\mathscr V_j(W_v^-)$. The determinant and auxiliary ray data are included as
associated rank-one descent systems on the same tower; no nominal group with a central kernel is
allowed.

### 3.4 Extension through the incidence model

The generic sheaves need not be unramified along the bad fiber. Consequently Book 122's
constant-coefficient nearby-cycle complex cannot simply be tensored with $P_v$. The required
extension has a formal part, which is now proved, and one residue-prime local-model part.

Let $\mathcal X^\bullet$ denote the fine integral vertex--edge diagram and let
$\mathcal Y_\eta^\bullet\to\mathcal X_\eta^\bullet$ be the actual generic principal and ray
tower used to define (3.5). Define $\mathcal Y^\bullet$ by normalization, not by naming a
compact-open quotient. Book 122, Proposition 9.2 proves that every object
$\mathcal Y^a\to\mathcal X^a$ is finite locally free and that every degeneracy or Hecke map
carried by a finite fine integral base leg extends uniquely as a finite map; along such a leg
the common normalized top map is
an isomorphism. It also proves that the ray factor is ordinary finite-flat
base change on the ray-only axis and that its rank-one coefficient is geometrically constant.
It does not claim that ramified base change commutes with normalization of the principal
algebra; the combined normalization remains the actual object of Proposition 9.2. Thus the ray factor
satisfies

$$
R\Psi(\mathcal K\otimes A_Q(\boldsymbol\chi_v))
\simeq R\Psi(\mathcal K)\otimes A_Q(\boldsymbol\chi_v)      \tag{3.10a}
$$

with diagonal full inertia action, and (3.10a) commutes with pull, trace, Hecke routing, and
duality. Ramification of $\boldsymbol\chi_v$ has not been discarded; it occurs in the external
inertia action on the right.  For the automorphic determinant system this is the identification
proved from the strict global character in Book 122, Proposition 9.9.  A locally written
character $\boldsymbol\chi_v^{\rm aut}\circ\det$ would not by itself supply it.

For any supplied tame coefficient on a strict annulus at $x$, let $H_x$ be the
prime-to-$\ell$ kernel of its geometric tame annular monodromy on a fiber $W$, put
$M_x=W^{H_x}$, and let $T_x$ be the remaining pro-$\ell$ generator. Book 22, Theorem 3.2
computes the full stalk, including residue Galois, as

$$
K_x(W)=[M_x\xrightarrow{\ T_x-1\ }M_x].                  \tag{3.10b}
$$

If arithmetic Frobenius acts on $M_x$ by $A_x$ and conjugates the generator by its $q$th
power, it acts on the two terms of (3.10b) by

$$
A_x,\qquad A_x[q^{-1}]_{T_x}.                              \tag{3.10c}
$$

The normalization filtration is Book 22's normalization--conductor homotopy fiber (3.10),
formed from (3.10b), the full branch complexes, and the node-to-branch generization maps.  Its
restriction component contains the oriented endpoint difference $r_1-r_0$ and the actual
vertex, edge, and flag decomposition modules. For a branch map of expansion index $e$ on which
the prime-to-$\ell$ invariant summand is unchanged, pull and trace have chain entries
$(1,[e]_{T_x})$ and $([e]_{T_x},1)$, respectively. These formulas are adjoint on the
contragredient lattice and are equivariant for (3.10c).

This paragraph is a functorial calculation, not by itself an identification of the actual wild
subgroup, $W,H_x,T_x$, or their principal stabilizers.  Book 122, (9.29b)--(9.29e), shows that
the level-one principal fiber is generally wild, and (9.29n)--(9.29q) identify its exact
wild-invariant ledger.  Equations (9.29r)--(9.29x) identify the corresponding raw full-level
higher groups, node complexes, and boundary modules.  Proposition 9.5 additionally computes
the invariant-field, Cartier and active-group rows and gives the normalized-compositum
factorization rule.  The strict datum (2.2a)--(2.2d) is exactly the actual datum of Book 122,
Propositions 9.9--9.10.  Those propositions compute its Kummer factors, descend the branch
complexes and their generization maps, and retain rather than tame away the wild principal
action.

Book 122, Corollary 9.11 proves the resulting $({\rm PNS}_v)_{\rm act}$.  In completed local
rings it
identifies the common normalization's decomposition and inertia groups, oriented annular
homomorphisms, and branch modules with
the actual vertex--edge--flag stabilizers,
identifies the wild annular subgroup and proves that its exact invariants on every routed
node-to-node coefficient module are the lines in Lemma 3.0A, identifies those
node-to-node points with a unique multiplicity-one sheet for each extreme flag incidence, and
routes every other sheet, with its full decomposition action and
multiplicity, through the normalization-component term.  The common-normalization
isomorphism then proves expansion index one on the identified node sheets.  It also identifies the branch
generization chain maps and proves that every non-wild-invariant routed summand is supplied,
with no smoothness or tameness assertion, by its actual completed branch source.  Its properly
typed component contribution is $Rf_{v*}\mathcal C_v$, or
$i_{x*}R\Gamma(C_v,\mathcal C_v)$ only when $C_v$ is contracted to $x$.  Finally it constructs
the oriented restriction--Gysin cohomological correspondence; proper direct image alone is not
a trace. Book 122, Proposition 9.8 supplies that oriented correspondence, and Propositions
9.9--9.10 supply the arithmetic and completed-tube parts.  Thus no separately assumed
$({\rm HDB}_v)_{\rm act}$ or $({\rm BTK})_{\rm act}$ hypothesis remains for the coefficient
rows (3.6)--(3.9).

Book 122, Proposition 9.3 proves $({\rm DLB}_1)$, and (9.29k)--(9.29l) prove all active finite
Drinfeld normalization rings.  The level-one divisor equation forces a $q+1$-branch crossing with wild
unipotent inertia; the raw principal cover is not a tame node.  The following calculation shows
that the selected two coefficient rows nevertheless have tame node modules after exact wild
invariants.

**Lemma 3.0A (forced wild invariants and flag routing).**  Choose a
factor of the actual common principal completion above Book 122's level-one Drinfeld
completion.  Such a map is forced by normalization because the common generic algebra
dominates the level-one principal subfield used by the two coefficient representations.
Book 122, (9.29f)--(9.29i), then identifies its level-one vertex, edge, and flag Stein factors.
For a branch $L\in\mathbf P^1(k_v)$ let $U_L$ be the unipotent radical of its Borel stabilizer
and put $s_L=\sum_{M\ne L}e_M$.  Then

$$
P_v^{U_L}=\mathcal Oe_L\oplus\mathcal Os_L,               \tag{3.10d}
$$

$$
(\operatorname{St}_v^+)^{U_L}
=\mathcal O(e_L\bmod\mathbf1),
\qquad
(\operatorname{St}_v^-)^{U_L}
=\mathcal O(e_L-q^{-1}s_L).                               \tag{3.10e}
$$

The two displayed generators pair to $1$, and the remaining diagonal tame quotient fixes both.
The intrinsic geometric annular monodromy of these coefficient modules has wild image $U_L$;
the deeper generic kernel acts trivially because the modules are inflated from level one.
Consequently its exact wild invariants are (3.10e), and the node-annular complexes are the strict procyclic
complexes of Book 22, (3.12)--(3.14), with any global ray action added diagonally; this
conclusion does not assert that the principal cover is tame.  Book 122, (9.29s)--(9.29x),
identifies the wild subgroup, node-annular complex, and boundary stabilizer modules for a
selected branch of the raw full Drinfeld ring $D_n$.  Proposition 9.5 computes its invariant
branch field, Cartier multiplicity and group filtration.  Book 122, Proposition 9.9 supplies
the actual endpoint class $[\gamma_L]$ and factors the polynomials as
$Z^{e_v}-\gamma_L^{-1}$ with the resulting constant-field orbits; Proposition 9.10
constructs the conductor complexes and generization maps.

The fixed Bruhat orbit is the identity Iwahori sheet and is node-to-node with multiplicity and
expansion indices one.  On the moving Bruhat orbit, the sheet $a=0$ in Book 122,
(9.11)--(9.12), is the unique
node-to-node sheet.  Its saturated completed ring is $xy=\pi$, both ordered branch maps are
the identity, and its multiplicity and expansion indices are one.  On either constant extreme
line in (3.10e), its two generization maps are identity in degree zero and zero on the
independent vanishing term.  Every $a\ne0$ sheet
has a unit incidence coordinate and a smooth completed source, so its full complex is in the
normalization-component term.  These assertions commute with $U_v$, $U_v^t$, and residue
Frobenius on the level-one Stein factor by Book 122, (9.13)--(9.15), and with every
prime-to-$v$ retained Hecke route.  Book 122, Proposition 9.4 promotes this routing,
multiplicity and expansion one, and Hecke/transpose compatibility to the actual deeper common
factor.  Book 122, Proposition 9.10 identifies the equivariant component-pushforward branch
contribution after associated descent, and Proposition 9.8 supplies the oriented
restriction--Gysin map on its proper direct image.
For the full level-one coefficient module, Book 122, (9.29n)--(9.29p), identifies only the
node complex, the two boundary stabilizers, and the coefficient inclusion
$W^{U_L}\hookrightarrow W$.  It expressly does not identify the full conductor complexes or
turn that inclusion into a generization chain map: doing so by a second copy of procyclic
group cohomology already fails for the trivial coefficient.  Thus no averaging by $q-1$ or
underived replacement of the moving branch is implicit here.
In fact (9.29q) splits either Steinberg row as its extreme line plus the integral augmentation
module $Q_L$ of the affine $U_L$-orbit.  The latter has no $U_L$-invariants, vanishes from the
node complex, and survives as the degree-zero moving conductor term computed in Book 122,
(9.58).

**Proof.**  The group $U_L\simeq(k_v,+)$ fixes $L$ and acts simply transitively on its affine
complement.  Hence (3.10d).  Its order $q$ is a unit in $\mathcal O$ because $v\nmid\ell$, so
wild invariants are exact.  Taking invariants in the quotient and augmentation rows gives
(3.10e); the augmentation of $e_L-q^{-1}s_L$ is zero, and the flag-basis dot product with
$e_L$ is one.  The Borel preserves $L$ and permutes its complement, so its diagonal quotient
fixes both generators.  The monodromy representation itself factors through the level-one
annular quotient, whose wild image is $U_L$; the deeper generic kernel therefore acts
trivially.  Book 22, Section 3.6, now gives the full node-annular complex after wild
invariants.  The remaining statements are the saturated incidence calculation, the explicit
stabilizer restriction (9.29n)--(9.29p), and the variance check of Book 122, Sections 9.3--9.4.
Book 122, Proposition 9.4 supplies the actual-common-factor promotion by restricting the proper
flag legs to their finite loci around the nodes and applying common normalization there.
$\square$

Thus wild triviality on the two extreme lines, coefficient one, the constant-extreme-line
conductor/generization map,
multiplicity one, and the level-one residue-prime route are no longer independent parts of the
black box.  Book 122, (9.29j), makes the first depth jump explicit, while (9.29k)--(9.29l)
identify the resulting active normalization and its intermediate rings.  Equations
(9.29r)--(9.29x) give the raw higher branch/inertia/residue, node-annular, and boundary-module
ledger and exhibit the purely inseparable obstruction to commuting branch normalization with
wild invariants.  Proposition 9.5 computes the Frobenius-subfield discrepancy, Cartier
multiplicity and active group filtration and reduces the compositum to its Kummer
factorization. Propositions 9.6--9.7 give the endpoint and Milnor-tube formalism.
Propositions 9.9--9.10 insert the actual strict ray datum, factor its endpoint polynomials,
normalize the completed tubes, and compute the branch/conductor complexes and generization
maps.  Corollary 9.11 proves $({\rm PNS}_v)_{\rm act}$.  Proposition 9.8 proves
$({\rm RGC}_v)$ on the properly typed component direct images. Proposition 9.4 has already identified the
strict-transform routing and node coefficients.

**Typed conclusion $({\rm TPE}_v)$ (typed parahoric extension and local comparison).** The
following conclusions hold for the selected quotient/augmentation Steinberg systems.

1. The maps between the normalized principal levels above the two degeneracy legs are finite
   flat. Associated descent extends the two rows (3.6)--(3.9) as perfect constructible
   complexes with finite-free strict stalk terms, and their restrictions to the vertex, edge,
   branch, and flag strata are the actual stabilizer complexes.
2. At every strict geometric node, the full inertia-equivariant nearby-cycle complex for the
   tower is (3.10b)--(3.10c), inserted in the normalization--conductor homotopy fiber with the
   oriented cellular edge $e\mapsto(v_1-v_0)$ and the actual stabilizer flag rows
   (3.6)--(3.7). This comparison is
   compatible with both normalization branches and with the normalization filtration.
3. The comparison commutes with residue Galois action, the retained Hecke correspondences, and
   trace along each finite flat degeneracy map.

**Theorem $({\rm TPE}_v)$.** Under the standing fine-model hypotheses and the strict ray
choice (2.2a)--(2.2d), all three clauses of $({\rm TPE}_v)$ hold.  Thus normalization, the ray
twist, and the ramified strict-node complex are not hypotheses.  This is the actual-row
theorem $({\rm PNS}_v)_{\rm act}$ of Book 122, Corollary 9.11; no converse or arbitrary
principal-representation statement is claimed from the two Steinberg rows.

**Proof.** Proposition 9.2 of Book 122 supplies the actual normalized diagram and objectwise
finite local freeness; its common-normalization lemma makes the lifted interlevel maps
isomorphisms, hence finite flat. Book 122, Corollary 9.11 identifies its local decomposition
modules with the asserted stabilizer modules.  Its wild/tame calculation first identifies
the actual wild group $P_x$.  Take $P_x$-invariants by Book 22, (3.12)--(3.13); its finite
$p$-power image has unit order because $v\nmid\ell$.  Lemma 3.0A identifies the resulting
extreme lines for the two Steinberg rows, while every noninvariant routed summand remains in
its full branch complex.  Next take exact invariants under
$H_x$, whose finite image has order prime to $\ell$. The averaging idempotents are $A_Q$-linear,
so each invariant module is a finite projective $A_Q$-summand of the original free module and
is finite free because $A_Q$ is complete local. Apply (3.10b) termwise to
(3.6)--(3.7).  Apply the same rows to the branch complexes and to the generization maps
identified in Book 122, (9.55)--(9.58), then form Book 22's
normalization--conductor homotopy fiber.
Those rows split as underlying $\mathcal O$-modules, so the resulting strict total complexes
remain exact without taking invariants under the possibly nonunit-order flag group. Book 22,
(3.8), gives pull, trace,
expansion coefficients, orientation, and adjunction; (3.10c) gives residue Galois; and (3.10a)
adds the ray action diagonally. Hecke equivariance along a finite fine base leg extends by
uniqueness of normalization maps. For a retained proper nonfinite residue-prime leg, the
graph/regular-domination construction of Book 122, Section 9.3 gives proper functoriality, and
Propositions 9.4 and 9.8 there give compatibility with the principal decomposition data and
the oriented component correspondence. $\square$

**Proposition 3.0B $({\rm TIC}_v)$ (actual unit-order coarse descent).**  For the clean
one-prime datum of Chapter 2, every geometric stabilizer which occurs in passage from the fine
PEL diagram to a retained coarse curve has order invertible in $\mathcal O$.  Consequently
the exact rows and the normalization--conductor totalizations of $({\rm TPE}_v)$ descend
exactly.  This conclusion imposes no order condition on the principal flag group, on a line
stabilizer, or on the full deck group used to trivialize a coefficient system.

**Proof.**  The actual vertex, edge, principal, ray, and normalized flag objects used in
$({\rm PNS}_v)_{\rm act}$ carry the neat prime-to-$v$ PEL level fixed in Chapter 2.  A neat
center-detecting level has no automorphisms of a geometric PEL object: an effective
stabilizer has finite adjoint image, neatness makes that image trivial, and the rigid level
kills the remaining central scalar.  Adding a Drinfeld basis, an oriented subgroup, or a ray
trivialization can only decrease this automorphism group.  Thus every object of the fine
actual diagram has trivial geometric inertia.

For a retained coarse component, choose the normal fine cover already used in the definition
of $\mathscr F_v(Q)$.  A point stabilizer in its effective descent group is exactly the
automorphism group of the descended PEL tuple.  By the clean-level convention its effective
order divides the prime-to-$\ell$ group $\Delta_D$, so stalkwise invariants are exact.  On the
free locus no invariants calculation is needed: descent of the associated sheaf is fpqc-local
and hence exact.  These two loci cover the quotient stack, and the same argument applies to
every geometric point of a normalization stratum or conductor locus because its isotropy
injects into the stabilizer of the underlying PEL tuple.  A decomposition group which merely
permutes such points can be larger; its action is retained as transport among summands and is
not averaged.

The finite group which labels all flags plays a different role.  Its action constructs the
associated permutation sheaf on the fine torsor; exactness there is checked after pulling back
to the torsor.  Likewise the possibly nonunit part of $A_L$ remains in the procyclic node
complex, rather than being averaged away.  The only finite invariants used in the local tube
calculation are those of the wild group $U_L$, of order $q$, and $q$ is a unit because
$v\nmid\ell$.  Therefore neither the full flag group nor a possibly nonunit line stabilizer
enters coarse descent.  This proves the asserted unit-order descent and hence
$({\rm TIC}_v)$. $\square$

The separation from $({\rm PNS}_v)_{\rm act}$ remains useful.  The principal complete-local
calculation determines the actual tubes and stabilizer representations; Proposition 3.0B
proves that their exact integral incidence rows survive passage to the retained curves.

**Proposition 3.1 (coefficient-one flag incidence).** By $({\rm TIC}_v)$, the two sequences
(3.6)--(3.7) give exact distinguished triangles of perfect constructible complexes and are
adjoint under (3.10). On a
strict node, the oriented extreme residue maps in the combined coefficient and geometric
nearby-cycle complex have coefficients $1$ or $-1$; the complex is not $q+1$ constant copies.

**Proof.** The reduction of $({\rm TPE}_v)$ identifies restrictions of the associated
complexes with the actual vertex, edge, and flag stabilizer representations. The universal edge has two endpoints, so its cellular boundary
is $e\mapsto(v_1-v_0)$. After an orientation is chosen, its entries are $1,-1$. Tensor this
cellular resolution with the exact representation sequences

$$
0\to\mathcal O\mathbf1\to P_v\to\operatorname{St}_v^+\to0,
\qquad
0\to\operatorname{St}_v^-\to P_v\to\mathcal O\to0.
\tag{3.11}
$$

These sequences split as underlying $\mathcal O$-modules.  Applying them to the node and
branch complexes and taking the normalization--conductor homotopy fiber therefore preserves
the resulting exact triangles, although the rows need not split equivariantly after reduction. Expansion
index one makes the two extreme entries $1$ by Book 22, (3.8); all other sheets remain in the
middle normalization term. Finite-flat trace is adjoint to pullback, and (3.10c), together
with (3.4), gives
the companion assertion. Coarse descent is exact by Proposition 3.0B. No averaging over the
possibly nonunit-order flag group occurs. $\square$

The deformation-theoretic flag of Chapter 7 is different from both objects above. It is a line
direct summand of the rank-two Galois module and varies in a projective line over the coefficient
algebra. Thus three objects must not be conflated: the finite set
$\mathbf P^1(k_v)$ in (3.2), the PEL incidence model at residue characteristic $v$, and the
Galois invariant-line scheme at residue characteristic $\ell$.

## 4. Perfect cohomology and the one-prime complexes

### 4.1 Perfectness over the group algebra

For $j=0,1$, put

$$
K_j^\pm=R\Gamma(X_{j,\overline F},\mathscr S_j^\pm)_{\mathfrak m^\pm}.
\tag{4.1}
$$

Here $j=0$ is the hyperspecial vertex and $j=1$ the edge level. The localization on the minus
side is the adjoint companion localization.

**Proposition 4.1 (strict perfect cohomology).** Each $K_j^\pm$ is a perfect $A_Q$-complex.
It has a bounded representative by finite projective $A_Q$-modules, commutes with derived
coefficient change, and admits ranks bounded over $A_Q$ through the clean Taylor--Wiles tower.

**Proof.** On a complex uniformization, choose a finite CW decomposition of the compact curve
and lift it to the finite-level tower defining (3.5). Cellular cochains with a finite free
$A_Q$-local system are finite free $A_Q$-modules. Prime-to-$\ell$ descent and Hecke
localization take direct summands, hence finite projectives. Cellular pullback computes finite
coefficient change termwise, proving derived base change. At auxiliary level the clean deck
action is a free effective $\Delta_Q$-torsor. Counting cell orbits rather than cells makes the
ranks bounded over $A_Q$; this is the curve version of Book 152's regular-module argument.
$\square$

Perfectness alone does not make $H^1(K_j^\pm)$ projective. The following fiber argument is the
missing step.

**Lemma 4.2 (fiber concentration implies freeness).** Suppose the primary and companion
residual localizations contain no character packet. Then

$$
K_j^+\otimes_{A_Q}^Lk\quad\text{and}\quad
K_j^-\otimes_{A_Q}^Lk
\tag{4.2}
$$

have cohomology only in degree $1$. Consequently there are finite free $A_Q$-modules
$P_j^\pm$ and quasi-isomorphisms

$$
K_j^\pm\simeq P_j^\pm[-1].
\tag{4.3}
$$

**Proof.** A degree-zero section is invariant under the relevant arithmetic stabilizer. After
Shapiro on the flag resolution, such sections are norm characters and satisfy the Eisenstein
relations at all good places. The chosen localization removes them. Poincaré duality with
(3.10) identifies degree two on one side with the dual of degree zero on the other, so degree
two also vanishes.

Take a minimal strict finite-free representative of the perfect complex over the complete local
ring $A_Q$. Its differentials have entries in the maximal ideal. Reduction to $k$ therefore
has zero differentials. Since its reduction has only one nonzero cohomological degree, the
minimal representative has only one term. This proves (4.3) and the freeness of that term.
$\square$

This proof uses concentration after derived reduction, not merely vanishing of integral
$H^0$ and $H^2$. The latter alone would not imply projectivity over the nonregular group ring
$A_Q$.

### 4.2 Pull, norm, and the companion complex

The two geometric degeneracy legs and the intertwiners of Section 3.2 give pull maps on both
coefficient systems,

$$
p_v^+=(d_0^+,d_1^+):P_0^{+,\oplus2}\longrightarrow P_1^+,
\qquad
p_v^-=(d_0^-,d_1^-):P_0^{-,\oplus2}\longrightarrow P_1^-.
\tag{4.4}
$$

Thus $d_v^+$ in (1.1)--(1.2) is $p_v^+$.

Finite-flat norm gives reverse maps

$$
r_v^+:P_1^+\longrightarrow P_0^{+,\oplus2},
\qquad
r_v^-=(r_0^-,r_1^-)^t:P_1^-\longrightarrow P_0^{-,\oplus2}.
\tag{4.5}
$$

Thus $d_v^-$ in (1.3) is $r_v^-$.

The trace formula on the finite correspondence, with the inverse-character action in (3.9),
shows that $p_v^+$ is adjoint to $r_v^-$ and that $p_v^-$ is adjoint to $r_v^+$. Thus

$$
C_v^+=[P_0^{+,\oplus2}\xrightarrow{p_v^+}P_1^+],
\qquad
C_v^-=[P_1^-\xrightarrow{r_v^-}P_0^{-,\oplus2}]
$$

are strict perfect complexes and

$$
C_v^-\simeq R\operatorname{Hom}_{A_Q}(C_v^+,A_Q)[-1].
\tag{4.6}
$$

The shift and direction are essential. The companion is a norm complex from the edge to the
two vertices, not another pullback complex. We nevertheless retain the companion pull $p_v^-$:
it is needed for the cross-pairing Gram matrix. The formal string $r_v^-p_v^+$ is not a
composite, because $P_1^+$ and $P_1^-$ are different lattices.

### 4.3 Universal coefficient sequence

For an arbitrary $A_Q$-algebra $B$, derived base change has the hyper-Tor spectral sequence

$$
E_2^{-i,j}
=\operatorname{Tor}_i^{A_Q}(H^j(C_v^+),B)
\Longrightarrow H^{j-i}(C_v^+\otimes_{A_Q}^LB).
\tag{4.7}
$$

Over the nonregular group ring $A_Q$, this spectral sequence must not be replaced by a
universal short exact sequence before a projective-dimension bound is known. If
$H^0(C_v^+)=0$, however, the differential in (1.2) is injective and
$N_v=H^1(C_v^+)$ has the length-one projective resolution

$$
0\longrightarrow P_0^{+,\oplus2}\longrightarrow P_1^+
\longrightarrow N_v\longrightarrow0.
\tag{4.8}
$$

In that case $\operatorname{Tor}_i^{A_Q}(N_v,B)=0$ for $i>1$ and (4.7) degenerates to

$$
H^0(C_v^+\otimes_{A_Q}^LB)
\simeq\operatorname{Tor}_1^{A_Q}(N_v,B),
\qquad
H^1(C_v^+\otimes_{A_Q}^LB)
\simeq N_v\otimes_{A_Q}B.
\tag{4.9}
$$

Thus the familiar Tor formula is valid precisely after injectivity has supplied the displayed
projective resolution. Theorem 5.2 will prove more: $N_v$ itself is projective, so even the
Tor group in (4.9) vanishes. No assertion about Tor over a deformation ring follows from
freeness over $A_Q$.

## 5. Type Ihara and the localized abelian input

### 5.1 The residual type obstruction

For every coefficient object $\overline W$ in the residual primary or companion flag complex,
let

$$
K_D(\overline W)=\ker\!\left(
H^1(\Gamma_{D,0}^v,\overline W)\oplus
H^1(\Gamma_{D,1}^v,\overline W)
\longrightarrow H^1(\Gamma_{D,e}^v,\overline W)
\right)_{\mathfrak m_D}^{\Delta_D}.
\tag{5.0}
$$

The map is the oriented two-vertex restriction map on the Bruhat--Tits tree, with the actual
component routing. For constant $\overline W=k$, (5.0) is killed by
$({\rm AIH}_{\mathscr F})$ through Book 139. For a nontrivial type system, its cocycles are
crossed homomorphisms, so Book 139's constant-coefficient arithmetic-character calculation does
not apply.

**Condition $({\rm TIH}_{\mathscr F})$ (type Ihara).** For every quotient-primary and
augmentation-companion coefficient object that occurs in the finite flag diagram,

$$
K_D(\overline W)=0.
\tag{5.0a}
$$

The permutation terms are already constant-coefficient cohomology on actual flag subgroups by
Shapiro and belong to $\mathscr F_v(Q)$; no extra hypothesis is imposed on them.  Proposition
5.0 proves (5.0a) for both endpoints when $q+1$ is a coefficient unit and proves the
augmentation companion in every range.  In the nonbanal range it first leaves one exact
quotient-primary map; Proposition 5.0B proves that map simultaneously at every actual
spectator level.

Put $\overline P=k[\mathbf P^1(k_v)]$, let $\overline{\rm St}^{+}$ and
$\overline{\rm St}^{-}$ be its quotient and augmentation endpoints, and, with localization,
routing, and $\Delta_D$-invariants understood, write

$$
d_D(W):H^1(\Gamma_{D,0}^v,W)\oplus H^1(\Gamma_{D,1}^v,W)
\longrightarrow H^1(\Gamma_{D,e}^v,W),
\qquad
\mathcal Q_D(W)=\operatorname{coker}d_D(W).
\tag{5.0b}
$$

**Proposition 5.0 (exact permutation-resolution calculation).** Assume
$({\rm AIH}_{\mathscr F})$ and the no-character localizations of Chapter 2.  Then, at every
object of the residual flag diagram,

$$
K_D(\overline P)=K_D(k)=0,
\qquad
K_D(\overline{\rm St}^{-})=0,
\tag{5.0c}
$$

and there is a canonical isomorphism

$$
K_D(\overline{\rm St}^{+})
\simeq
\ker\!\left(
\mathcal Q_D(k)\xrightarrow{\,u_D\,}\mathcal Q_D(\overline P)
\right),
\tag{5.0d}
$$

where $u_D$ is induced by the constant-vector map.  In particular, if
$q+1\in\mathcal O^\times$, then $({\rm TIH}_{\mathscr F})$ follows from
$({\rm AIH}_{\mathscr F})$.  If $q\equiv-1\pmod\ell$, the quotient-primary endpoint is reduced
to injectivity of the displayed map $u_D$ on the actual localized new cokernels; Proposition
5.0B proves it.

**Proof.**  Shapiro identifies the $\overline P$ row with the direct sum of the actual
constant-coefficient flag-subgroup rows included in $\mathscr F_v(Q)$, so (1.5) kills its
kernel; it also kills the constant row.  At each vertex and edge localization, degree zero is
a character packet and vanishes.  Degree two vanishes by Poincare duality and the corresponding
adjoint degree-zero vanishing.  The two coefficient sequences therefore give short exact
sequences on degree-one curve cohomology.

For

$$
0\longrightarrow\overline{\rm St}^{-}
\longrightarrow\overline P\xrightarrow{\rm aug}k\longrightarrow0,
$$

degree-one cohomology with $\overline{\rm St}^{-}$ injects into degree-one cohomology with
$\overline P$ at both the source and target of $d_D$.  Hence its degeneracy kernel injects
into $K_D(\overline P)$ and is zero.  For

$$
0\longrightarrow k\xrightarrow{u}\overline P
\longrightarrow\overline{\rm St}^{+}\longrightarrow0,
$$

the snake lemma applied to the three degeneracy maps gives

$$
0\to K_D(k)\to K_D(\overline P)\to
K_D(\overline{\rm St}^{+})\to
\mathcal Q_D(k)\xrightarrow{u_D}\mathcal Q_D(\overline P),
$$

which proves (5.0d).  Exact prime-to-$\ell$ descent and localization commute with this
calculation.

If $q+1$ is a unit, then

$$
e_{\bf1}=(q+1)^{-1}u\circ\operatorname{aug}
\tag{5.0e}
$$

is an integral equivariant idempotent on $P_v$ and hence on
$P_v\otimes_{\mathcal O}A_Q$; its reduction is the corresponding idempotent on
$\overline P$.  Thus
$\overline P=k\mathbf1\oplus\ker(\operatorname{aug})$ and both
$\overline{\rm St}^{+}$ and $\overline{\rm St}^{-}$ identify with the second direct summand.
The type degeneracy maps are consequently direct summands of the Shapiro permutation maps,
so their kernels vanish.  Scalar and auxiliary $\ell$-power twists reduce to the same rows;
equivalently one may twist every arrow in the argument. $\square$

The qualification in the last sentence is real.  If $q\equiv-1\pmod\ell$, transitivity of
the flag action gives

$$
\operatorname{Hom}_{\overline K_v}(\overline P,k)=k\,\operatorname{aug},
\qquad
\operatorname{Hom}_{\overline K_v}(k,\overline P)=k\,u,
$$

but $\operatorname{aug}\circ u=q+1=0$ in $k$.  Hence the constant line is not a direct
summand of $\overline P$.  Two injective vertical maps in the constant and permutation rows
do not force the induced map on their quotients to be injective; (5.0d) is the additional
snake-lemma term treated in Proposition 5.0B.  Finite-group cohomology can describe the
nonsplit flag extension, but by itself it does not determine the map $u_D$ on the actual
arithmetic new cokernels.  Perfect duality
identifies (5.0d) with failure of the companion **norm** to be onto, whereas (5.0c) proves
injectivity of the companion **pull**.  These are different maps, so duality does not remove
the term.

The formal failure already occurs for vector spaces.  In the source exact row
$0\to k\to k^2\to k\to0$, use $a\mapsto(a,0)$ and $(a,b)\mapsto b$; in the target exact row
$0\to k^2\to k^3\to k\to0$, use $(a,b)\mapsto(a,b,0)$ and $(a,b,c)\mapsto c$.  The left,
middle, and right vertical maps

$$
k\longrightarrow k^2,\quad a\longmapsto(a,0),
\qquad
k^2\longrightarrow k^3,\quad(a,b)\longmapsto(a,b,0),
\qquad
k\longrightarrow k,\quad b\longmapsto0
$$

form a commutative diagram.  The first two are injective, but the induced map between the two
quotient copies of $k$ is zero.  Therefore
Shapiro injectivity on the constant and permutation rows, even together with exact coefficient
rows, cannot prove the quotient-primary assertion without proving injectivity of $u_D$ in
(5.0d).

The Cartan--Leray form of the same warning is also useful.  On a common principal cover with
deck group $H$, the terms are

$$
E_2^{a,b}=H^a\!\left(H,H^b(Y,k)\otimes_k W\right)
\Longrightarrow H^{a+b}(X,\mathscr V(W)).
$$

When $\ell\mid |H|$, derived invariants are not exact.  The problematic terms contain the
actual arithmetic cohomology $H^b(Y,k)$ and its localized new quotient; they are not determined
by the abstract groups $H^a(H,W)$.  Thus a finite-group cohomology calculation is a proof of
type-Ihara only if it also kills the derived-invariant term on the actual new quotient, which
is another formulation of the injectivity in (5.0d).

There is a still sharper formulation which uses both integral flag rows and makes clear that
no pull--trace identity has been overlooked.  Write

$$
\mathcal Q_D^\circ(W)=\operatorname{coker}d_D^\circ(W)
$$

for the corresponding integral new cokernel, before reduction modulo $\varpi$, for
$W=\mathcal O$ or $P_{\mathcal O}$.  Under $({\rm AIH}_{\mathscr F})$ the constant and
permutation old maps have a unit maximal minor.  Hence these two cokernels are projective over
the retained complete local coefficient algebra, their underlying $\mathcal O$-modules are
torsion free, and their reductions are the two cokernels in (5.0d).  Let

$$
U_D:\mathcal Q_D^\circ(\mathcal O)\longrightarrow
\mathcal Q_D^\circ(P_{\mathcal O}),
\qquad
V_D:\mathcal Q_D^\circ(P_{\mathcal O})\longrightarrow
\mathcal Q_D^\circ(\mathcal O)
\tag{5.0f}
$$

be induced by the constant-vector and augmentation maps.  They satisfy

$$
V_DU_D=(q+1)\operatorname{id}.                            \tag{5.0g}
$$

The coefficient algebra is $\mathcal O$-free, so (5.0g) makes $U_D$ injective.  It does not
make its image primitive when $q+1$ is a nonunit.

**Proposition 5.0A (the nonbanal new Bockstein).**  Suppose
$q\equiv-1\pmod\ell$ and retain the hypotheses of Proposition 5.0.  The augmentation row and
(5.0c) give an exact sequence

$$
0\longrightarrow\mathcal Q_D(\overline{\rm St}^{-})
\longrightarrow\mathcal Q_D(\overline P)
\xrightarrow{\,\operatorname{aug}_D\,}\mathcal Q_D(k)
\longrightarrow0.                                      \tag{5.0h}
$$

Because $\operatorname{aug}\circ u=q+1=0$ in $k$, there is a unique map

$$
\beta_D:\mathcal Q_D(k)\longrightarrow
\mathcal Q_D(\overline{\rm St}^{-})                    \tag{5.0i}
$$

whose composite with the first arrow of (5.0h) is $u_D$.  It is induced by the actual trivial
submodule $k\mathbf1\subset\overline{\rm St}^{-}$ of Book 138, (8.5).  The following are
equivalent:

1. the quotient-primary type-Ihara assertion at $D$;
2. injectivity of $u_D$ in (5.0d);
3. injectivity of the arithmetic new Bockstein $\beta_D$; and
4. $\mathcal Q_D^\circ(P_{\mathcal O})/U_D
   \mathcal Q_D^\circ(\mathcal O)$ has no $\varpi$-torsion.

**Proof.**  Apply the snake lemma to the augmentation coefficient row.  All three vertical
kernels vanish by (5.0c), giving (5.0h).  The factorization (5.0i) follows from
$\operatorname{aug}u=0$, and the first arrow in (5.0h) is injective, so $u_D$ and $\beta_D$
have the same kernel.  Proposition 5.0 identifies that kernel with
$K_D(\overline{\rm St}^{+})$.  Finally, reduction of (5.0f) is $u_D$.  Since $U_D$ is an
injection between $\mathcal O$-torsion-free finite modules, the kernel after reduction is

$$
\operatorname{Tor}_1^{\mathcal O}
\left(\operatorname{coker}U_D,k\right).
$$

It vanishes exactly when the image of $U_D$ is primitive, proving the last equivalence.
$\square$

The identity (5.0g) alone does not prove primitivity.  The rank-one model $U=q+1$, $V=1$
already satisfies it while $U$ has noninjective reduction.  The actual flag map has additional
two-orbit structure, and that structure supplies the required integral argument.

**Proposition 5.0B (nonbanal quotient-new injection).**  Suppose
$q\equiv-1\pmod\ell$ and assume $({\rm AIH}_{\mathscr F})$.  At every routed spectator level,
the Bockstein (5.0i) is injective.  Equivalently, the map in (5.0d) is injective and the
integral constant-vector map $U_D$ has primitive image.  Hence
$({\rm TIH}_{\mathscr F})$ holds for the actual quotient-primary and
augmentation-companion rows in the nonbanal range.

**Proof.**  Fix an oriented edge and let $L$ be its fixed endpoint in
$\mathbf P^1(k_v)$.  For $a=\sum_Ma_Me_M$ put

$$
\epsilon_L(a)=a_L,
\qquad
\mu_L(a)=q^{-1}\sum_{M\ne L}a_M.                       \tag{5.0j}
$$

Both maps are $B_L$-equivariant: $B_L$ fixes $L$ and permutes its affine complement.  They
are also compatible with transport, since
$\epsilon_{gL}(ga)=\epsilon_L(a)$ and $\mu_{gL}(ga)=\mu_L(a)$.  On the augmentation lattice,

$$
\mu_L(a)=-q^{-1}\epsilon_L(a)
\quad\text{for }a\in\overline{\rm St}^{-}.
$$

Because $q=-1$ in $k$, the two functionals agree there.  Denote their common restriction by
$\rho_L$.  The constant vector belongs to $\overline{\rm St}^{-}$ and

$$
\rho_L(\mathbf1)=1.                                    \tag{5.0k}
$$

Equivalently, reduction of the actual decomposition (9.29q) of Book 122 is

$$
\overline{\rm St}^{-}=k\mathbf1\oplus\overline Q_L,
\qquad \overline Q_L^{,U_L}=0,
$$

and $\rho_L$ is projection to the first summand.  This splitting is $B_L$-equivariant and
transport-equivariant in the flagged object, though it is not a splitting as an
$\overline K_v$-module.

We now apply this equality to the actual two-orbit Mackey square, not to the abstract
coefficient row.  Under

$$
\operatorname{Res}^{\overline K_v}_{B_L}\overline P
\simeq ke_L\oplus k[B_L/T_L],
$$

the first functional in (5.0j) is restriction to the identity double coset.  The second is
$q^{-1}$ times corestriction along the moving orbit $B_L/T_L$.  Its index is $q$, a unit in
$k$.  Shapiro identifies the corresponding vertex terms with the actual constant-coefficient
flag-subgroup terms.  The fixed-orbit and moving-orbit formulas for either degeneracy leg
therefore give, on degree-one cochains, the ordinary Mackey restriction--corestriction
identity with the two displayed functionals.  If the orientation is reversed their roles are
exchanged, but (5.0k) is unchanged.

Chase a possible kernel class through this square.  Let $[c]\in\mathcal Q_D(k)$ satisfy
$\beta_D[c]=0$, represent it by an edge class $c$, and choose vertex classes $z_0,z_1$ with
$\overline{\rm St}^{-}$ coefficients whose old image is the image of $c$.  Embed $z_0,z_1$
in the permutation rows and use Shapiro to write them as constant-coefficient classes on the
two actual one-step flag subgroups.  Their augmentations vanish.

Restrict to the edge and use the displayed Mackey decomposition.  The identity double coset
gives the fixed scalar equation through $\epsilon_L$; the moving double coset gives the
normalized scalar equation through $\mu_L$.  By (5.0k) these two equations agree.  Their
remaining difference is therefore a compatible pair of constant-coefficient classes on the
actual length-two flag subgroup.  In other words, the two-orbit chase gives a natural
injection

$$
\ker\beta_D\lhook\joinrel\longrightarrow K_{D_L^{(2)}}(k),       \tag{5.0l}
$$

where $D_L^{(2)}$ is the routed length-two flag object already contained in
$\mathscr F_v(Q)$.  This is the ordinary two-double-coset snake diagram: changing the chosen
permutation lifts alters the resulting pair by an old constant class, so (5.0l) is
well-defined; if that pair is old, the original edge class $c$ is old as well.  The fixed and
moving formulas above prove injectivity.

The right side of (5.0l) is zero by $({\rm AIH}_{\mathscr F})$.  Hence $\beta_D$ is
injective.  This calculation divides only by $q$.  Exact descent through $\Delta_D$,
localization, scalar twisting, and auxiliary diamonds commute with it.  Proposition 3.1
identifies the two double cosets with the actual geometric legs, so no formal replacement of
the flag diagram has occurred.  Proposition 5.0A now gives injectivity of (5.0d) and
primitivity of $U_D$.  The augmentation entry was already proved in (5.0c), so both clauses
of $({\rm TIH}_{\mathscr F})$ follow. $\square$

**Lemma 5.1 (residual type injectivity).** Assume $({\rm AIH}_{\mathscr F})$. Then

$$
p_v^+\otimes_{A_Q}k:
P_0^{+,\oplus2}\otimes k\longrightarrow P_1^+\otimes k
\tag{5.1}
$$

is injective. The companion pull $p_v^-\otimes k$ is injective as well. Equivalently, the
adjoint norms $r_v^-\otimes k$ and $r_v^+\otimes k$ are surjective. The actual tame and
auxiliary spectator levels are the ones occurring in $\mathscr F_v(Q)$.

**Proof.** Proposition 3.0B identifies the geometric degeneracy maps with the oriented
restriction maps in (5.0) and makes the two flag rows an exact adjoint diagram.  Proposition
5.0 supplies both entries in the projector range and the augmentation entry in every range;
Proposition 5.0B supplies the remaining nonbanal quotient entry.  Thus
$({\rm TIH}_{\mathscr F})$ is now established before it is used.  The resulting maps are the
asserted primary and companion maps.
Perfect transposition gives surjectivity of both norms. No rational projector or averaging is
used. $\square$

The named assertions should still not be conflated. The finite list (1.5) is indispensable
for Book 139's constant normalization filtration.  Proposition 5.0 is the formal coefficient
reduction, while Proposition 5.0B uses the additional actual fixed/moving Mackey identity.
Non-Eisenstein localization alone proves neither (1.5) nor that identity for an arbitrary
coefficient system.

### 5.2 Split exactness and all coefficient Tor

**Theorem 5.2 (one-prime split amplitude).** Under the hypotheses of Lemma 5.1, the primary
and companion pull sequences

$$
0\longrightarrow P_0^{+,\oplus2}
\xrightarrow{p_v^+}P_1^+
\longrightarrow N_v^+\longrightarrow0
\tag{5.2}
$$

and

$$
0\longrightarrow P_0^{-,\oplus2}
\xrightarrow{p_v^-}P_1^-
\longrightarrow N_v^-\longrightarrow0
\tag{5.2a}
$$

are split exact as sequences of $A_Q$-modules. The quotients $N_v^\pm$ are finite
projective, and

$$
C_v^+\simeq N_v^+[-1],
\qquad
C_v^-\simeq (N_v^+)^\vee,
\qquad
\ker r_v^-\simeq(N_v^+)^\vee,
\tag{5.3}
$$

and, for every $A_Q$-algebra $B$,

$$
\operatorname{Tor}_i^{A_Q}(N_v^+,B)=0\quad(i>0),
\qquad
C_v^+\otimes_{A_Q}^LB\simeq
(N_v^+\otimes_{A_Q}B)[-1].
\tag{5.4}
$$

**Proof.** The sources and targets of the two pull maps are finite free over the local ring
$A_Q$. Residual injectivity gives a maximal minor which is nonzero over $k$, hence a unit in
$A_Q$. Elementary operations put this minor into an identity block. Thus both pull maps are
split injections and their cokernels are projective. Equations (5.3)--(5.4) follow for the
primary complex by taking its quotient and adjoint dual. $\square$

The splitting is not Hecke canonical and is not an integral orthogonal old--new splitting.
The latter would require the Gram operator to be a unit. The theorem also says nothing about
$\operatorname{Tor}$ over the deformation ring acting through Book 170's reciprocity map.
For the actual rows, Propositions 5.0 and 5.0B replace its type-Ihara input by
$({\rm AIH}_{\mathscr F})$ in every range, including $q\equiv-1\pmod\ell$.

## 6. Nearby cycles, graph terms, and the branch correction

### 6.1 Primitive residue with type coefficients

Let $\Gamma_v$ be the oriented geometric dual graph of the Iwahori special fiber. Apply the
constructible flag-incidence complex of Proposition 3.1 to the normalization sequence. Let
$X_v^+$ be its primary cycle lattice and let $X_v^-$ be the companion cycle lattice.

Let $W_0\subset W_1\subset P_1^+$ be the bottom and normalization layers, put

$$
A_{\rm old}=p_v^+(P_0^{+,\oplus2}),
\qquad
L_v^+=W_1/A_{\rm old}\longrightarrow N_v^+,
\tag{6.0}
$$

and form the integral normalization complex

$$
\mathcal R_{v,A_Q}^+
=\left[
L_v^+\longrightarrow
N_v^+\xrightarrow{\,\operatorname{res}_v\,}
X_v^+(-1)
\right].
\tag{6.0a}
$$

The three terms are placed in degrees $0,1,2$. The arrows are the actual integral maps before
any exactness or coefficient-change assertion. Theorem 5.2 and
$A_{\rm old}\subset W_1\subset P_1^+$ make the first arrow injective, so
$H^0(\mathcal R_{v,A_Q}^+)=0$; only the next two homology groups can obstruct the desired
sequence. Define the primitive-residue obstruction by

$$
\operatorname{Ob}_{\rm PRI}(v)
=H^1(\mathcal R_{v,A_Q}^+)\oplus H^2(\mathcal R_{v,A_Q}^+).
\tag{6.0b}
$$

The first summand is the extra snake-lemma class between the normalization and graph layers;
the second is the failure of the top residue to be onto. Perfect primary--companion
transposition identifies their duals with, respectively, the extra companion class and the
kernel of the bottom companion residue.

**Condition $({\rm PRI}_{\rm type})$ (primitive type residue).** The precise assertion is

$$
\operatorname{Ob}_{\rm PRI}(v)=0
\tag{6.0c}
$$

at every retained spectator level. Equivalently, the top primary residue sequence obtained
from the integral constructible normalization diagram is exact, and its perfect transpose is
the exact bottom companion sequence. Thus the quotient by the normalization layer maps onto
$X_v^+(-1)$, and dually $X_v^-$ embeds into the bottom companion layer, with no additional
class from the nonsemisimple flag rows. Residual exactness alone is not substituted for this
integral assertion without an independent coefficient-flatness theorem.

This is stronger than the nodewise coefficient-one calculation of Proposition 3.1. Books
125, 138--141, 152, and 170--172 do not by themselves prove the vanishing (6.0c) for these
type coefficients.  Proposition 6.0 proves it in the integral-projector range.  Proposition
6.0B proves it in the remaining nonbanal range by establishing the exact filtered comparison
below; (6.0b) records the obstruction which that proof kills.

There is again a sharp projector/nonprojector distinction which the condition hides.  For
the following comparison assume $({\rm AIH}_{\mathscr F})$.  Proposition 3.0B supplies
$({\rm TIC}_v)$ and Propositions 5.0--5.0B supply $({\rm TIH}_{\mathscr F})$.  Let
$\mathcal R_{v,A_Q}(\mathbf1)$ and $\mathcal R_{v,A_Q}(P)$ denote the old-quotient
normalization complexes obtained from the constant and permutation rows at the corresponding
actual levels.  Under $({\rm AIH}_{\mathscr F})$ Book 139 makes the first complex exact in its
two obstruction degrees, and Shapiro makes the second a finite direct sum of such exact
complexes.  Their degree-zero maps are injective by the same constant/permutation old-map
theorem, so both complexes are in fact acyclic.  Functoriality of the
normalization--conductor totalization gives a natural comparison

$$
\vartheta_v:
\operatorname{Cone}\!\left(
\mathcal R_{v,A_Q}(\mathbf1)\xrightarrow{u}
\mathcal R_{v,A_Q}(P)
\right)
\longrightarrow \mathcal R_{v,A_Q}^{+}.
\tag{6.0d}
$$

The source is therefore acyclic.  Thus, in the nonbanal case, the primitive-residue target is
equivalently the assertion that (6.0d) is a quasi-isomorphism in degrees $1,2$.  This is the
precise filtered-cofiber comparison which is lost if one first
takes underived coefficient quotients, old cokernels, and normalization layers.  It is not a
calculation of the abstract finite flag group alone: its terms contain the actual routed
arithmetic old quotient and branch generization maps.

**Proposition 6.0 (projector-range primitive residue).** Use the proved $({\rm TPE}_v)$ and
$({\rm TIC}_v)$, and assume $({\rm AIH}_{\mathscr F})$.  If
$q+1\in\mathcal O^\times$, then $({\rm TIH}_{\mathscr F})$ and
$({\rm PRI}_{\rm type})$ both hold for the quotient-primary and augmentation-companion
systems, at every retained coefficient face.

**Proof.**  The idempotent (5.0e) is defined over $A_Q$ and commutes with the scalar twist,
the auxiliary diamonds, pull, trace, and the two maps in the flag resolution.  It therefore
splits the constant line and the common Steinberg summand not only on generic cohomology but
termwise in the strict normalized branch, node, and conductor complexes supplied by
$({\rm TPE}_v)$.  The entire normalization--conductor totalization, its filtration, and the
old-map cone are additive in this coefficient summand.  Shapiro identifies the permutation
totalization with the direct sum of the constant totalizations at the actual flag levels.
Book 139, applied under $({\rm AIH}_{\mathscr F})$, gives exact old maps and primitive extreme
residues on every one of those constant summands.  Passing to the complementary idempotent
summand proves residual type-Ihara and makes (6.0a) exact in degrees $1,2$.

This is a termwise $A_Q$-linear idempotent splitting of finite-projective strict
totalizations.  The Steinberg totalization is consequently an acyclic perfect direct summand,
so it remains acyclic after arbitrary derived coefficient change.  Thus no new obstruction
appears at a nonflat retained face.  Perfect transposition
gives the augmentation-companion statement. $\square$

When $q\equiv-1\pmod\ell$, no such conclusion follows from the projector argument.  The two flag
rows remain exact as rows of modules, but they are nonsplit equivariantly modulo $\varpi$.
The cone on the left of (6.0d) is a derived coefficient quotient; the three-term complex on
the right is formed after taking the actual old cokernel and its underived normalization
layers.  Proving that these operations agree requires the fixed/moving contraction used in
Proposition 5.0B.  Nodewise entries $\pm1$, finite freeness of the strict terms, and perfect
primary--companion duality construct $\vartheta_v$ and transpose its cone; by themselves they
do not force its cone to be acyclic.

One operation in this comparison can nevertheless be removed from the list of suspects.
Write $N_v(\mathbf1)$ and $N_v(P)$ for the middle, generic-new terms of the constant and
permutation normalization complexes.

**Proposition 6.0A (the generic old quotient already commutes).**  Under
$({\rm AIH}_{\mathscr F})$, the coefficient
row induces a split exact sequence of finite projective modules

$$
0\longrightarrow N_v(\mathbf1)
\longrightarrow N_v(P)
\longrightarrow N_v^+
\longrightarrow0.                                      \tag{6.0e}
$$

The same statement holds on every retained coefficient face, with derived base change.  Thus
the nonbanal defect in (6.0d) is not a further failure of the generic old cokernel to commute
with the quotient coefficient row.  It is exactly the failure, if any, of that coefficient
cofiber to be strict for the **global normalization filtration** and its graph-cycle residue.

**Proof.**  Proposition 3.0B identifies the sheaf maps with the actual routed
coefficient row.  Apply the quotient coefficient sequence to the two lower terms and the
Iwahori term of the old map.  Degree zero and degree two vanish at the chosen no-character
localizations, so these are short exact coefficient rows on degree-one cohomology.  The
constant and permutation vertical old maps are injective by
$({\rm AIH}_{\mathscr F})$ and Shapiro, and the quotient-primary vertical map is injective by
Proposition 5.0B in the nonbanal range and Proposition 5.0 otherwise.  The snake lemma
therefore gives (6.0e).  The unit-minor argument
makes all three cokernels projective; hence (6.0e) splits as a module sequence and survives
arbitrary derived coefficient change. $\square$

Equivalently, after (6.0e) the map $\vartheta_v$ is already a quasi-isomorphism on its middle
new term.  Its cone is the total defect of the two extreme filtered comparisons: the derived
quotient of the constant-to-permutation normalization layer versus $L_v^+$, and the derived
quotient of the constant-to-permutation graph complex versus $X_v^+(-1)$, with their actual
residue differential.  Book 122's completed tubes and Proposition 3.1 identify these maps on
each routed node and give their entries $\pm1$.  They do not say that taking global graph
cycles, global normalized-component cohomology, and the coefficient cofiber commute.  Those
are kernel and cohomology operations, so termwise split exactness over $\mathcal O$ is
insufficient when the flag row is nonsplit equivariantly.  A reusable proof of (6.0d) must
therefore be a filtered strictness theorem for the actual routed arithmetic totalization; a
second saturation proof for (6.0e), a local Smith calculation, or perfect transposition would
not address the remaining operation.

The formal obstruction exists even with unit matrices.  Over $k$, take
$0\to A\to B\to C\to0$ with $A=k$, $B=k^2$, $C=k$, maps
$a\mapsto(a,0)$ and $(x,y)\mapsto y$.  Put
$F^1A=0$, $F^1B=k(1,0)$, and $F^1C=C$.  Both maps are filtered and every nonzero matrix entry
is $1$, but the quotient filtration induced from $B$ has $F^1(B/A)=0$, not $F^1C=C$.
Equipping the dual row with the orthogonal filtrations adds perfect transposition without
repairing strictness.  Proposition 3.1 rules out nonunit **local incidence coefficients**; it
does not rule out this global filtered-cohomology phenomenon.

**Proposition 6.0B (nonbanal primitive filtered cofiber).**  Suppose
$q\equiv-1\pmod\ell$ and assume $({\rm AIH}_{\mathscr F})$.  The map $\vartheta_v$ in
(6.0d) is a filtered quasi-isomorphism at every retained coefficient face.  Consequently
$({\rm PRI}_{\rm type})$ holds for the quotient-primary and augmentation-companion systems.

**Proof.**  Type-Ihara has already been established in Proposition 5.0B, so Theorem 5.2 and
Proposition 6.0A may now be applied.  In particular, the generic old cokernels are finite
projective and the comparison is already an isomorphism on its middle new term.  We first work
on the raw strict totalizations, whose terms are finite projective, and prove the same
unit-minor statement on the normalization and graph ends.  Their filtered cokernels, including
$L_v^+$, will then be finite projective rather than being assumed so.

Use the strict normalization--conductor totalizations supplied by $({\rm TPE}_v)$ before
taking graph cycles.  On an oriented branch $L$, split the constant-vector map on the fixed
Bruhat summand by $\epsilon_L$ and on the moving summand by $\mu_L$, with the notation of
(5.0j).  Both are retractions because

$$
\overline{\rm St}^{-}=k\mathbf1\oplus\overline Q_L,
\qquad
\overline Q_L^{,U_L}=0,
\qquad
\epsilon_L(\mathbf1)=\mu_L(\mathbf1)=1.                \tag{6.0f}
$$

The actual tube formulas make these the only two contractions which occur.  On the fixed
node-to-node sheet, restriction and generization use $\epsilon_L$ with coefficient one.  On
the moving $U_L$-orbit, normalized trace uses $\mu_L$; the summand $Q_L$ has no node term and
remains in the normalization layer.  Thus the contractions preserve the three-step
normalization filtration.  They use $q^{-1}$ but never $(q+1)^{-1}$.

Reduce the filtered defect cone of $\vartheta_v$ to the residue field $k$.  On the companion
augmentation row, the overlap between the fixed and moving contractions is exactly

$$
\epsilon_L\big|_{\overline{\rm St}^{-}}
=\mu_L\big|_{\overline{\rm St}^{-}}=\rho_L,
$$

the identity used in Proposition 5.0B.  Hence the two local contractions glue across every
node and conductor generization.  The family is transport-equivariant in $L$, so it also
commutes with residue Galois and with the oriented graph boundary.  The primary defect is the
perfect transpose of this companion overlap under (3.10); no identification of
$\operatorname{St}^+$ with $\operatorname{St}^-$ is made.  Therefore the contraction kills
the associated graded defect not merely nodewise but on the global normalized-component and
graph complexes:

$$
\operatorname{gr}_j
\operatorname{Cone}(\vartheta_v)\otimes_{A_Q}k\simeq0
\qquad (j=0,1,2).                                      \tag{6.0g}
$$

The point at which a general filtered row can fail is precisely the compatibility on the
overlap.  Here it is the equality of fixed evaluation and the normalized $q$-orbit trace;
Proposition 5.0B has already shown that its global old-cokernel connecting map is zero.  Thus
the formal example preceding this proposition cannot occur in the actual flag totalization.

The filtration is finite, so (6.0g) makes the residual defect cone acyclic.  On each filtered
old map the residual contraction exhibits the required full-rank unit minor.  The same
elementary-operations argument as in Theorem 5.2 therefore makes its image a direct summand
and its cokernel finite projective.  The resulting defect cone is consequently a bounded
complex of finite projective modules over the complete local algebra $A_Q$.
Successively cancelling the unit minors visible after reduction, or equivalently applying
derived Nakayama to the cone and its truncations, makes it acyclic over $A_Q$.  Being a bounded
acyclic complex of projectives, it is split exact and remains acyclic after arbitrary derived
coefficient change.  This proves the filtered quasi-isomorphism on every retained face.

Finally, the two constant/permutation complexes on the left of (6.0d) are acyclic under
$({\rm AIH}_{\mathscr F})$.  Hence $\mathcal R_{v,A_Q}^+$ is acyclic in degrees $1,2$, which
is (6.0c).  Perfect primary--companion transposition gives the bottom companion assertion.
$\square$

**Proposition 6.1 (coefficient-one extreme residues).** Assume
$({\rm AIH}_{\mathscr F})$. Then the top primary residue and bottom companion residue are
primitive and give

$$
\operatorname{gr}_2N_v^+\simeq X_v^+(-1),
\qquad
\operatorname{gr}_0(N_v^+)^\vee\simeq X_v^-.
\tag{6.1}
$$

The maps commute with Hecke correspondences, branch reversal, and primary--companion
adjunction. The exact sequences commute with every retained derived coefficient change.

**Proof.** Proposition 3.1 computes the combined coefficient and geometric nearby cycles on
each node. An oriented node generator maps to its edge generator with coefficient $1$; reversing
orientation changes both signs. The inclusion
$A_{\rm old}\subset W_1\subset P_1^+$ gives an injection
$L_v^+\hookrightarrow N_v^+$, and functoriality of nearby cycles makes its composite with
$\operatorname{res}_v$ zero. Consequently
$H^1(\mathcal R_{v,A_Q}^+)=0$ says exactly that the image of $L_v^+$ is the kernel of the top
residue, while $H^2(\mathcal R_{v,A_Q}^+)=0$ says exactly that the top residue is onto.
Propositions 6.0 and 6.0B give (6.0c), so this is the integral exact sequence

$$
0\longrightarrow L_v^+\longrightarrow N_v^+
\xrightarrow{\,\operatorname{res}_v\,}X_v^+(-1)\longrightarrow0.
\tag{6.1a}
$$

The graph-cycle lattice $X_v^+$ is the kernel of an oriented boundary map between finite free
$\mathcal O$-chain lattices. It is therefore finite free over the DVR $\mathcal O$. Hence the
quotient in (6.1a) is $\mathcal O$-torsion-free, so $L_v^+$ is primitive in $N_v^+$ and the
top graded identification in (6.1) is integral. All three lattices are $\mathcal O$-free;
dualizing (6.1a) is therefore exact. The pull--norm and primary--companion adjunction supplied
by Proposition 3.0B identifies that dual with the bottom companion residue sequence and gives
the second identification in (6.1).

Conversely, either pair of exact primitive extreme sequences with the displayed graded
identifications makes the complex (6.0a) exact in degrees $1,2$, so it characterizes
$({\rm PRI}_{\rm type})$.  Proposition 6.0B proves split exactness at the level of perfect
filtered complexes, so nonflat retained coefficient change creates no Tor obstruction. Hecke,
branch-reversal, and adjunction compatibility comes from the maps supplied under
$({\rm TPE}_v)$ and Proposition 3.0B. No type-created finite index appears in
either extreme residue. The argument deliberately does not claim that a boundary matrix with
a nontrivial local system is automatically totally unimodular. $\square$

For the comparison with a switched definite module one needs the following datum-specific
refinement of Book 140's node hypothesis.

**Hypothesis $({\rm NU}_{\rm type})$.** Book 140's flagged groupoid target (5.9a) holds for
the chosen datum; its stabilizer weights are units; and the induced flag linearization sends an
oriented node generator with coefficient vector to the characteristic function of the
corresponding switched definite class with that same vector.

There are two logical layers in this formulation.  Even with constant coefficients, Book
140's Hypothesis 5.1 requires the superspecial PEL quasi-isogeny classification.  Its precise
flagged form is (5.9a): an equivalence from the node groupoid, with polarization, level,
automorphisms, active flag, branch routing, Frobenius, and Hecke correspondences retained, to
the switched definite double-coset groupoid.  Section 5.3 proves the formal double-coset
reduction only after that classification is granted.  The geometric equivalence is the
unproved layer.  Lemma 6.1A proves that transport of the primary and companion stabilizer
representations and their perfect pairing is then formal.  Neither the geometric
classification nor its flagged functor follows from rational Jacquet--Langlands or from the
local chart $xy=\pi_v$.

Consequently the constant-coefficient hypothesis in Book 140 does not by itself prove this
refinement; Book 140, Section 13.1 lists it as the extra input for a type-enhanced variant. Under
$({\rm NU}_{\rm type})$,

$$
X_v^+\xrightarrow{\sim}S_v^{\dagger,+}
\tag{6.2}
$$

is coefficient one and respects the paired mass form. This is a comparison of the graph
multiplicity lattice, not an isomorphism between all of $N_v^+$ and a definite module.

The representation-theoretic part of this hypothesis is nevertheless formal once the
geometric classification is stated at the correct level.

**Lemma 6.1A (flagged groupoid transport).** Use $({\rm TIC}_v)$ and suppose that Book
140's missing superspecial theorem (5.9a), an equivalence of the **flagged node groupoid** with
the switched definite double-coset groupoid, holds.  Here flagged means that the equivalence
retains the active rank-one incidence object, its two oriented deformation branches, its
automorphism action on the finite flag set, the polarization multiplier, and the prime-to-$v$
level.  With the Frobenius, Hecke, and component routing included in (5.9a), it implies
$({\rm NU}_{\rm type})$; no further theorem about
the quotient or augmentation representations is needed.

**Proof.**  On either groupoid the permutation coefficient is the free module on the active
finite flag functor.  A natural isomorphism of that functor transports its basis vectors with
coefficient one and intertwines every isotropy action.  The constant-vector and augmentation
maps are natural transformations of its free-module linearization.  Their cokernel and kernel
are therefore transported as the primary and companion modules.  The dot product on flag basis vectors is
also natural, so the perfect primary--companion pairing is preserved.  Full faithfulness
identifies automorphism groups, hence the stabilizer factors; their orders are units by
Proposition 3.0B.  The retained branch orientation, Frobenius, routing, and
Hecke correspondences give all remaining clauses of $({\rm NU}_{\rm type})$. $\square$

An equivalence or bijection which forgets the flag functor is insufficient.  Already for a
one-object groupoid $BH$, the underlying object, automorphism group, and mass do not distinguish
an $H$-module $W$ from $W\otimes\chi$.  Thus Book 140's unproved classification remains the
first node-uniformization theorem, but the type refinement is not a second independent
representation-classification problem: it is the functorial consequence of proving that
classification for flagged PEL nodes.

### 6.2 The corrected normalization filtration

Retain the bottom and normalization layers and the notation $A_{\rm old}$ and $L_v^+$ from
(6.0). Under $({\rm AIH}_{\mathscr F})$, Propositions 6.0 and 6.0B prove
$({\rm PRI}_{\rm type})$, so the map in (6.0) identifies $L_v^+$ with its displayed submodule
of $N_v^+$; thus

$$
L_v^+=W_1/A_{\rm old}\subset N_v^+.
\tag{6.3}
$$

The normalized-component map is a two-by-two block

$$
B_v^+=
\begin{pmatrix}
1&F_{01}^*\\
F_{10}^*&1
\end{pmatrix}.
\tag{6.4}
$$

The two entries retain central routing, type transport, and companion adjunction. Define

$$
\mathcal C_{\mathrm{br},v}^+=\operatorname{coker}B_v^+.
\tag{6.5}
$$

In the constant, trivial-central normalization $F_{01}^*=F_{10}^*=F_v^*$ and Smith
elimination gives

$$
\mathcal C_{\mathrm{br},v}
\simeq\operatorname{coker}(1-(F_v^*)^2).
\tag{6.6}
$$

One may use (6.6) only after making that normalization. Formula (6.5) is the invariant
definition.

**Theorem 6.2 (branch-corrected filtration).** Under
$({\rm AIH}_{\mathscr F})$, there are exact sequences

$$
0\longrightarrow (X_v^-)^\vee
\longrightarrow L_v^+
\longrightarrow\mathcal C_{\mathrm{br},v}^+
\longrightarrow0,
\tag{6.7}
$$

$$
0\longrightarrow L_v^+
\longrightarrow N_v^+
\longrightarrow X_v^+(-1)
\longrightarrow0.
\tag{6.8}
$$

The lattice $L_v^+$ is saturated in $N_v^+$. The first arrow in (6.7) need not be
saturated, and $\mathcal C_{\mathrm{br},v}^+$ need not vanish.

**Proof.** Apply the corrected normalization filtration supplied by Book 139 under
$({\rm AIH}_{\mathscr F})$ to every constant term in the flag resolution. Proposition 3.1 makes the
branch maps a morphism of the two exact type rows, and Lemma 5.1 makes the old quotient exact.
The top quotient is (6.1). In the middle layer, Smith reduction of the actual block (6.4)
gives (6.7). Saturation of $W_1/A_{\rm old}$ in the old quotient gives (6.8). No step replaces
$B_v^+$ by its determinant. $\square$

### 6.3 Raw and corrected component complexes

The primary--companion graph pairing gives

$$
\mu_v:X_v^+\longrightarrow(X_v^-)^\vee.
\tag{6.9}
$$

Its cokernel $\Phi_v^{\rm type}$ is the selected coefficient block of the geometric Néron
component module. Monodromy on the new quotient is the composite

$$
X_v^+\xrightarrow{\mu_v}(X_v^-)^\vee\longrightarrow L_v^+.
\tag{6.10}
$$

If $\Psi_v^{\rm type}$ is its cokernel, (6.7) gives

$$
0\longrightarrow\Phi_v^{\rm type}
\longrightarrow\Psi_v^{\rm type}
\longrightarrow\mathcal C_{\mathrm{br},v}^+
\longrightarrow0.
\tag{6.11}
$$

Thus there are two independent finite corrections. The graph discriminant is the component
module; the branch Smith module measures the failure of the bottom graph copy to be primitive
after quotienting by old classes. Neither is coefficient torsion in $N_v^+$, and neither may be
discarded in a later use of the one-place complex.

**Proposition 6.3 (typed generic-residue support and faithful orders).** Assume
$({\rm AIH}_{\mathscr F})$. Assume also that Book 125's automorphic decomposition applies on
the actual common principal cover, with the full component-routing Hecke algebra or a proved
separating component projector. Let $\mathbb T_{\mathrm{abs}}$ be the integral abstract
away-from-level Hecke algebra preserving the displayed lattices and put
$\mathbb T_{\mathrm{abs},E}=\mathbb T_{\mathrm{abs}}\otimes_{\mathcal O}E$. Then

$$
\ker\!\left(\mathbb T_{\mathrm{abs},E}
\longrightarrow\operatorname{End}(N_{v,E}^+)\right)
=
\ker\!\left(\mathbb T_{\mathrm{abs},E}
\longrightarrow\operatorname{End}(X_{v,E}^+)\right).
\tag{6.12}
$$

The same equality holds on the companion side. If $({\rm NU}_{\rm type})$ is also imposed,
the common kernel in (6.12) is the kernel on the selected typed switched-definite lattice.
In either comparison the faithful integral image orders are therefore canonically equal.
Thus the type-specific generic-residue and faithful-order comparisons are conclusions from
the already isolated typed inputs, not additional hypotheses.

**Proof.** The branch module $\mathcal C_{\mathrm{br},v}^+$ in (6.7) is finite over
$\mathcal O$, so it vanishes after tensoring with $E$. The component module
$\Phi_v^{\rm type}=\operatorname{coker}\mu_v$ is finite for the same reason: $\mu_v$ is the
positive edge-length pairing between equal-rank graph lattices. Hence (6.7)--(6.9) give

$$
L_{v,E}^+\simeq(X_{v,E}^-)^\vee\simeq X_{v,E}^+
\tag{6.13}
$$

as modules for the actual routed Hecke algebra. Equation (6.8) therefore expresses
$N_{v,E}^+$ as an extension of $X_{v,E}^+(-1)$ by $X_{v,E}^+$. The Tate twist changes the
residue Galois action, not the away-from-level Hecke action.

It remains to rule out a Hecke operator acting only through the extension class. On the common
principal cover, Book 125 decomposes characteristic-zero first cohomology into full automorphic
packet blocks and proves that the finite routed Hecke image is semisimple. Because the
associated type systems are obtained by exact characteristic-zero isotypic extraction from
that cover, their Hecke-stable subquotients are semisimple as well. Thus (6.8) splits as an
away-from-level Hecke module after inverting $\varpi$. Noncanonically,

$$
N_{v,E}^+\simeq X_{v,E}^+\oplus X_{v,E}^+(-1).
\tag{6.14}
$$

An abstract Hecke operator therefore kills $N_{v,E}^+$ exactly when it kills
$X_{v,E}^+$, proving (6.12). Perfect primary--companion adjunction gives the companion
equality. Under $({\rm NU}_{\rm type})$, (6.2) transports the same kernel to the typed
switched-definite lattice with the actual component and stabilizer routing. No integral
splitting and no disappearance of either finite correction is asserted.

Every lattice just used is finite free over $\mathcal O$. Consequently its integral
$\mathbb T_{\mathrm{abs}}$-kernel is the contraction of its generic kernel: if an integral
operator kills the generic fiber, its image in the endomorphism ring is $\mathcal O$-torsion
and hence zero. Contracting (6.12), and its companion or switched-definite version, identifies
the integral kernels. Quotienting the same abstract algebra by that common kernel identifies
the faithful image orders, with no residual congruence index. $\square$

## 7. The enhanced special component

### 7.1 Matrix, line, and schematic closure

Remove the fixed prime-to-$\ell$ scalar inertia character. Begin with the ambient framed
line-incidence problem: a rank-two representation, a line direct summand $L$, a sign, and a
nilpotent $N$ such that

$$
N^2=0,
\qquad
\operatorname{im}N\subseteq L\subseteq\ker N,
\qquad
FNF^{-1}=qN.
\tag{7.1}
$$

The determinant is fixed in the declared relative convention. On the open locus $N\ne0$, the
line is both $\operatorname{im}N$ and $\ker N$, Frobenius preserves it, and its two line
characters have ratio $q:1$ for arithmetic Frobenius. The enhanced special problem is the
schematic closure of this open locus with those character labels retained. The condition
$N\ne0$ itself is open and is not imposed on Artinian quotients.

In a basis adapted to $L$, write

$$
N=\begin{pmatrix}0&m\\0&0\end{pmatrix},
\qquad
F=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
\tag{7.2}
$$

Then (7.1) gives

$$
mc=0,
\qquad
m(a-qd)=0.
\tag{7.3}
$$

Put $u=a-qd$. After retaining the flag, character, frame, and Kummer coordinates in a complete
base $R_0$, the equations forced by monodromy alone give the bare incidence ring

$$
A_{\rm inc}=R_0[[m,u,c]]/(mu,mc).
\tag{7.4}
$$

This is an ambient monodromy-incidence ring, not by itself the represented enhanced special
deformation ring: the line-character and determinant equations remain part of $R_0$. The
schematic closure of $D(m)$ inside this ambient chart is not all of (7.4). Its ideal is the kernel of
$A_{\rm inc}\to(A_{\rm inc})_m$, namely $(u,c)$, so the named special component is

$$
A_{\rm sp}=A_{\rm inc}/(u,c)\simeq R_0[[m]].
\tag{7.5}
$$

Indeed $(mu,mc)=(m)\cap(u,c)$: the other component is the extraneous monodromy-zero incidence
branch with arbitrary Frobenius. Every support statement below uses (7.5), not the union
(7.4).

### 7.2 The scalar chart

Suppose the residual Frobenius is scalar. On an affine flag chart put

$$
L(z)=A(e_1+ze_2),
\qquad
P(z)=\begin{pmatrix}1&0\\z&1\end{pmatrix}.
\tag{7.6}
$$

Transporting the adapted matrices with line eigencharacters $qa$ and $a$ gives

$$
N(z)=
\begin{pmatrix}
-mz&m\\
-mz^2&mz
\end{pmatrix},
\tag{7.7}
$$

$$
F(z)=
\begin{pmatrix}
qa-bz&b\\
z((q-1)a-bz)&a+bz
\end{pmatrix}.
\tag{7.8}
$$

These equations retain the line when $m=0$. Scalar reduction forces
$qa\equiv a$ with $a$ a unit, hence

$$
q\equiv1\pmod\ell.
\tag{7.9}
$$

The flag coordinate $z$ does not remove the exceptional Kummer directions. If $x$ is the tame
scalar cocycle and $y$ the unramified cocycle, linearizing (2.8) gives

$$
(1-q)x=0,
\tag{7.10}
$$

while $y$ is unrestricted. Both coordinates belong to $R_0$. At a scalar point no integral
root projector is used; the represented line and the independently defined $W_v$-sign are the
selectors.

### 7.3 The vexing chart

If $q\equiv-1\pmod\ell$ and $\ell$ is odd, a scalar special Frobenius is impossible by
(7.9). The two line eigenvalues are distinct and opposite modulo $\varpi$. The local
deformation chart is therefore the distinct-line version of (7.5). The vexing feature is on the
integral automorphic side: both signed Gram factors can be nonunits and the reductions of
$\operatorname{St}^+$ and $\operatorname{St}^-$ have the opposite extensions described after
(3.4).

Accordingly the theorem retains the whole matrix (10.3) below, the full primary--companion
pair, and any $W_v$-summand that exists independently. It never divides by the other signed
factor to isolate one branch.

### 7.4 Scalar twisting and conductor

Let the conductor-one enhanced special problem have determinant $\delta^{(1)}$. The relative
conductor-two scalar-twist problem records $\boldsymbol\chi_v$ and has determinant

$$
\delta^{(2)}=\delta^{(1)}\boldsymbol\chi_v^2.
\tag{7.11}
$$

Twisting and untwisting preserve $L$, $N$, the sign, and the closure (7.5). Thus, for the
represented global problems with the recorded character,

$$
R^{(2)}\simeq R^{(1)}\widehat\otimes_{\mathcal O}\Lambda_v.
\tag{7.12}
$$

A nontrivial tame character of conductor one changes an unramified Steinberg twist of conductor
exponent one into a scalar ramified twist of conductor exponent two. Augmentation makes only the
scalar character trivial; it does not set $m=0$, forget the line, discard Kummer coordinates,
or pass to the extraneous incidence component.

## 8. Support on the named component

### 8.1 The support lemma

For $C\in D^b_{\mathrm f}(R)$ over a noetherian ring $R$, write

$$
\operatorname{Supp}_R C
=\{\mathfrak p:C\otimes_R^Lk(\mathfrak p)\ne0\}.
\tag{8.1}
$$

**Lemma 8.1 (one-boundary support).** Let $Z$ be a complete noetherian local ring and let
$C\in D^b_{\mathrm f}(Z)$ have finite cohomology. For every irreducible component $\Xi$ of
$\operatorname{Spec}Z_{\rm red}$ suppose there is a prime $\mathfrak q_\Xi\in\Xi$ such that:

1. $\Xi$ is the only irreducible component through $\mathfrak q_\Xi$;
2. $C_{\mathfrak q_\Xi}\ne0$; and
3. some $H^i(C)_{\mathfrak q_\Xi}$ has depth
   $\dim Z_{\mathfrak q_\Xi}$.

Then

$$
\operatorname{Supp}_ZC=\operatorname{Spec}Z
\quad\text{topologically},
\qquad
\sqrt{\operatorname{Ann}_ZH^*(C)}=\sqrt{(0)}.
\tag{8.2}
$$

**Proof.** If the generic point of $\Xi$ were not in the support, then after localizing at
$\mathfrak q_\Xi$ the support would be a proper closed subset of the unique component. Its
dimension would be smaller than $\dim Z_{\mathfrak q_\Xi}$. This contradicts
$\operatorname{depth}M\leq\dim\operatorname{Supp}M$ for the module in clause 3. Repeat for
every component. The radical equality is the support statement in ideal form. $\square$

The lemma proves topological support, not scheme-theoretic faithfulness. Nilpotents are not
detected by (8.2).

### 8.2 Boundary witnesses

Let $R_\infty^{\rm sp}$ be the patched global deformation ring with the named local factor
(7.5), and let $C_{\infty,v}^+$ be the patched one-prime complex. Write $({\rm SUP}_v)$ for
the following one-prime support datum. In this patched section, the proved
$({\rm TIC}_v)$ is used on every retained finite shadow, and
$({\rm TIH}_{\mathscr F})$ is either imposed there or supplied by
$({\rm AIH}_{\mathscr F})$ through Propositions 5.0--5.0B.

1. Taylor--Wiles sets are disjoint from $v$, kill the dual Selmer group, satisfy the
   split-regular detector input of Book 141, and
   retain both degeneracy maps, both type rows, the flag, sign, determinant, and companion
   pairing in every finite shadow.
2. The lower boundary problem is a clean minimal problem to which Book 172 applies; its patched
   module is nonzero and free over its regular scalar source.
3. At the boundary prime of each named local component, the special incidence equation makes
   the companion same-coefficient Gram block $G_v^-=r_v^-p_v^-$ singular over the residue
   field of that prime (equivalently, its primary transpose is singular there).
4. After removal of the same frame variables on both sides, the completed patched selected
   chart at that boundary is the lower patched chart with the monodromy coordinate $m$ and the
   displayed flag/Kummer coordinates; equivalently, the relative cotangent mapping fiber is the
   represented line-incidence complex of Chapter 7. The scalar chart retains all of $R_0$ and
   the vexing chart retains the full line block. For each global irreducible component, the
   boundary prime is chosen over the generic point of its lower component so that it is the
   unique component through that prime.
5. The patched coefficient source $S_\infty$ and $R_\infty^{\rm sp}$ have the same local
   dimension at these boundary primes.

Call clauses 1--3 the **boundary-carrier datum** and call clauses 4--5
$({\rm BCD}_v)$, the **boundary chart-and-dimension theorem**. Thus
$({\rm SUP}_v)$ means the boundary-carrier datum together with $({\rm BCD}_v)$. These are
geometric and Taylor--Wiles conditions, not a disguised assertion that the module already has
support.

The boundary-carrier part is source-closed once the clean datum has been matched. Book 141
supplies the adequacy and split-regular detector, and Book 143 applies it to the represented
nonminimal problem, with its recomputed dual Selmer group and $v$ in the finite avoidance set.
Book 152 and the marked-shadow construction used in Book 172 retain the two maps, coefficient
rows, and pairings, while Book 172 supplies the nonzero free lower carrier in clause 2. For
clause 3, the
special line-incidence equation (10.6) vanishes at the declared boundary. Equation (10.7) then
gives $D_v=0$ in its residue field. Since $D_v$ is the determinant of the square same-coefficient
Gram block, that block is singular. This proves precisely clause 3; it does not compare a
Galois cotangent complex with the automorphic complex.

The irreducible support input is $({\rm BCD}_v)$. Let
$R_{v,\partial}^{\rm sp}$ be the completion of the named local chart (7.5) along $m=0$, with
all of $R_0$ retained, and let $R_{v,\partial}^{\rm low}$ be its represented $m=0$ boundary.
After removing the same frame variables, $({\rm BCD}_v)$ asserts the completed Cartesian
identity

$$
\widehat{(R_\infty^{\rm sp})_{\mathfrak q}}
\simeq
\widehat{(R_\infty^{\rm low})_{\mathfrak p}}
\widehat\otimes_{R_{v,\partial}^{\rm low}}
R_{v,\partial}^{\rm sp},
\tag{8.2a}
$$

with precisely the monodromy, flag, and Kummer coordinates displayed in Chapter 7 and no
extraneous component. It also asserts the resulting equality

$$
\dim (S_\infty)_{\mathfrak p}
=\dim (R_\infty^{\rm sp})_{\mathfrak q}
\tag{8.2b}
$$

at the unique boundary prime on each global component. Books 138--146, 152, and 170--172 do
not prove (8.2a)--(8.2b) for the nonminimal typed problem. Book
172 explicitly says that adding ramification changes the local base, components, dual Selmer
group, and automorphic level complex and requires a new local support argument. Clause 4 is
false if the extraneous component of (7.4) is retained or if a scalar flag/Kummer coordinate is
deleted.

The word ``chart'' in $({\rm BCD}_v)$ should not be read as asking again for the elementary
local calculation of Chapter 7.  That calculation is source-closed.  On the named special
closure the completed local ring is $R_0[[m]]$ and its monodromy-zero boundary is $R_0$; in
the distinct-line case this is Book 138's clean special chart, and at a scalar point $R_0$
means the whole represented flag, unramified, tame-Kummer, determinant, and frame block of
(7.6)--(7.10).  The scalar ray factor is then ordinary completed tensor product with
$\Lambda_v$ by (7.12).  None of these local statements retains the extraneous $(u,c)$
component of (7.4).

One further part is already formal from the patching sources, provided all three problems are
patched in one marked diagram.  At a distinct-line point let $R_v^{\rm ur}$ be the enhanced
unramified ambient factor, let $u$ cut out the special-ratio boundary

$$
R_{v,\partial}=R_v^{\rm ur}/(u),
\qquad
R_v^{\rm sp}=R_{v,\partial}[[m]].                         \tag{8.2c}
$$

At each Taylor--Wiles level, Book 69, (13.6), equivalently Book 170, (13.1b) applied over the
same unrestricted framed local ring, gives the two **quotient** identities

$$
R_{Q}^{\partial}
\simeq R_Q^{\min}\widehat\otimes_{R_v^{\rm ur}}R_{v,\partial},
\qquad
R_Q^{\partial}
\simeq R_Q^{\rm sp}\widehat\otimes_{R_v^{\rm sp}}R_{v,\partial}.
\tag{8.2d}
$$

There is no ring map from the unramified global problem to the special global problem which
creates tame monodromy: both map only to their common boundary quotient.  Thus (8.2d) must not
be reversed by associativity of completed tensor products.

The Taylor--Wiles sets in (8.2d) may be chosen in common.  Choose a killing set for the first
of the finitely many residual condition problems, then choose additional primes for the next
problem while avoiding those already chosen.  Adding a Taylor--Wiles condition can only shrink
the preceding dual Selmer group, so its vanishing persists.  Iterate and pad to one fixed
cardinality as in Book 143, Section 12.4.  Include the three rings, both quotient maps, their
kernels, the modules, and all retained operators in one finite marked shadow.  Book 145,
Proposition 3.1 and Lemmas 4.1 and 5.1 then give a single coherent diagonal and preserve both
finite quotient identities.  Consequently one can, and below does, choose patched rings with

$$
R_\infty^{\partial}
\simeq R_\infty^{\min}/(u)
\simeq R_\infty^{\rm sp}/(m),                             \tag{8.2e}
$$

after the same frames are removed and with the corresponding full ideals in the scalar case.
This closes the simultaneous-marking and common-boundary **quotient** comparison.  It
does not give a section of either quotient and hence does not prove (8.2a).

The exact first missing reusable theorem is now narrower: it is a **relative
Cartier-switch transversality theorem** for the two arrows in (8.2e).  At the selected patched
primes, put

$$
A=\widehat{(R_\infty^{\min})_{\mathfrak r}},
\qquad
D=\widehat{(R_\infty^{\partial})_{\mathfrak p}},
\qquad
B=\widehat{(R_\infty^{\rm sp})_{\mathfrak q}}.
$$

In the distinct-line chart the required assertions are

$$
D\simeq A/(u),
\qquad u\ne0\text{ in the regular domain }A,
\qquad B\simeq D[[m]].                                   \tag{8.2f}
$$

The last isomorphism is noncanonical and means that the relaxation from the boundary condition
to the named special condition is formally smooth of relative dimension one, with $m$ its
relative parameter.  Equivalently, the relative cotangent mapping fiber is the actual
line-incidence condition complex and its relative obstruction map vanishes.  At a scalar point,
the coordinate $u$ and parameter $m$ in (8.2f) are replaced by equal-length boundary and
monodromy blocks: the first must be a regular sequence on $A$, and the second must give the
corresponding formally smooth power-series directions.  The blocks include the full flag,
unramified, tame-Kummer, determinant, and frame data.  One signed Gram factor is not a
substitute.

**Proposition 8.1A (formal completion of the boundary comparison).**  If (8.2f), or its scalar
block version, holds, then the completed chart (8.2a), the local-dimension equality (8.2b), and
the unique-component routing in clause 4 follow formally.

**Proof.**  Book 172 makes $A$ a regular domain finite free over its regular scalar source.
In the distinct-line case, $u\ne0$ is therefore a non-zero-divisor and every prime minimal
over $(u)$ has height one.  If $\mathfrak r_i$ is such a prime, then

$$
\mathfrak q_i=(\mathfrak r_i/(u),m)
\subset (A/(u))[[m]]
$$

lies on exactly the component indexed by $\mathfrak r_i$: no distinct minimal prime over
$(u)$ is contained in $\mathfrak r_i$.  Its contraction to the finite regular scalar source
has height one, while $\mathfrak q_i$ also has height one.  This proves (8.2b) and the required
routing.  Formula (8.2f) is (8.2a) after identifying the common boundary by (8.2e).  For equal
blocks of length $s$, quotienting by the regular boundary sequence lowers dimension by $s$ and
adjoining the $s$ monodromy variables restores it; the same minimal-prime argument gives unique
component routing. $\square$

Neither the available local-model sources nor the patching sources prove (8.2f).  Book 69,
(13.7), gives
the tangent comparison and Section 10.6 gives a formal-smoothness criterion, but no source
proves the required relative obstruction-map vanishing for this special-to-boundary map.
Book 143 explicitly warns that absolute dual-Selmer vanishing does not kill a relative
obstruction theory, and Book 145 preserves a marked comparison but does not manufacture a
section or formal smoothness.  Book 172 proves regularity only for the lower clean patched
problem; it does not prove that the image of $u$ is nonzero or that the monodromy relaxation is
unobstructed.  Thus (8.2f), with its scalar-block analogue, is precisely the remaining global
content of $({\rm BCD}_v)$.  No nonminimal or downstream $R=T$ statement is used to
manufacture it.

**Lemma 8.2 (nonzero boundary class).** Assume $({\rm TIH}_{\mathscr F})$ and the first three
clauses of $({\rm SUP}_v)$. Then
$C_{\infty,v}^+$ is nonzero at every declared boundary prime.

**Proof.** Work in the residue field of a declared boundary prime. Book 172 supplies a nonzero
lower companion block, and clause 3 makes its same-coefficient Gram operator

$$
G_v^-=r_v^-p_v^-
$$

singular. Choose $0\ne y^-\in\ker G_v^-$. In the scalar case $y^-$ lies in the full recorded
flag and $W_v$-block; in the vexing case it lies in the full two-by-two block. Lemma 5.1 makes
the relevant unit minor visible, and Theorem 5.2 makes $p_v^-$ split injective after every
coefficient specialization. Hence $p_v^-y^-\ne0$, while

$$
r_v^-p_v^-y^-=G_v^-y^-=0.
$$

Hence $p_v^-y^-$ is a nonzero element of
$\ker r_v^-\simeq(N_v^+)^\vee$. Perfect primary--companion duality therefore makes the
residual derived fiber of $C_{\infty,v}^+$ nonzero. This argument does not confuse the
primary old image with the primary new quotient, divide by a Gram factor, or invoke a
nonminimal $R=T$ theorem. $\square$

### 8.3 Maximal depth and support

**Theorem 8.3 (one-prime component support).** Assume
$({\rm TIH}_{\mathscr F})$ and $({\rm SUP}_v)$. Then

$$
\operatorname{Supp}_{R_\infty^{\rm sp}}C_{\infty,v}^+
=\operatorname{Spec}R_\infty^{\rm sp}
\tag{8.3}
$$

as topological spaces. The same is true for the companion complex and after descent to every
retained finite auxiliary level.

**Proof.** Apply the marked finite-shadow patching mechanism used in Book 172 to Book 152's
regular auxiliary modules, with the strict complexes and pairings also marked. It patches
(5.2) to a split injection over the regular scalar source $S_\infty$. Hence

$$
C_{\infty,v}^+\simeq N_{\infty,v}^+[-1]
\tag{8.4}
$$

with $N_{\infty,v}^+$ finite free over $S_\infty$. A regular system of parameters of the
localized scalar source is therefore $N_{\infty,v}^+$-regular. Clauses 4--5 identify its length
with $\dim R_{\infty,\mathfrak q}^{\rm sp}$, so

$$
\operatorname{depth}_{R_{\infty,\mathfrak q}^{\rm sp}}
(N_{\infty,v}^+)_{\mathfrak q}
=\dim R_{\infty,\mathfrak q}^{\rm sp}.
\tag{8.5}
$$

Lemma 8.2 supplies nonvanishing, while the named closure (7.5) and its line label make the
selected component unique through the declared boundary prime. Lemma 8.1 proves (8.3).
Derived primary--companion duality gives the same support on the companion side.

At finite level, the complex is the derived base change of the patched perfect complex. For a
prime $\mathfrak p$ of the finite quotient, its residue-field fiber is the same residue-field
fiber of the patched complex, hence is nonzero. This proves full finite-level support without
assuming ordinary flat base change over the deformation ring. $\square$

The theorem gives

$$
\operatorname{Ann}_{R_\infty^{\rm sp}}H^*(C_{\infty,v}^+)
\subseteq\sqrt{(0)}.
\tag{8.6}
$$

It does not make the annihilator zero. Killing it is part of the later nonminimal comparison.
Once $({\rm TIH}_{\mathscr F})$ is available, $({\rm PRI}_{\rm type})$ does not enter this
support proof.  The condition $({\rm AIH}_{\mathscr F})$ enters if it is used to supply
type-Ihara through Proposition 5.0B, and it is also required for the corrected residue and
normalization filtration of Chapter 6.

## 9. Scalar twisting and exact augmentation

### 9.1 Strict twisting of sheaves and complexes

Assume the effective global ray quotient of Section 2.2 has been chosen. Multiplication of
automorphic cochains by the global character
$\boldsymbol\chi_v^{\rm aut}(\det g)$ gives a strict equivalence between the conductor-one
coefficient system tensored with $\Lambda_v$ and the conductor-two system (3.8). Its inverse
uses $\boldsymbol\chi_v^{-1}$. It commutes with both degeneracy legs, their norm adjoints,
the flag resolution, and the node residue. Therefore

$$
C_v^{(2),+}
\simeq\Lambda_v\otimes_{\mathcal O}C_v^{(1),+}
\tag{9.1}
$$

as strict complexes, equivariantly for the represented-ring identity (7.12), and similarly on
the companion side with $\iota$.

Orbit sum on the regular group basis is fixed-prime augmentation. It is not trace or averaging.
Thus

$$
C_v^{(2),+}\otimes_{\Lambda_v,\epsilon_v}^L\mathcal O
\simeq C_v^{(1),+}.
\tag{9.2}
$$

### 9.2 Module Tor and pairings

Under $({\rm TIH}_{\mathscr F})$, combine (5.3) with (9.1):

$$
N_v^{(2),+}
\simeq\Lambda_v\otimes_{\mathcal O}N_v^{(1),+}.
\tag{9.3}
$$

Consequently

$$
N_v^{(2),+}\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\simeq N_v^{(1),+},
\qquad
\operatorname{Tor}_i^{\Lambda_v}(N_v^{(2),+},\mathcal O)=0
\quad(i>0).
\tag{9.4}
$$

The group-ring-valued pairing is normalized by coefficient extraction, so its orbit-sum
augmentation is exactly the conductor-one primary--companion pairing. A raw sum over every
element of $\Delta_v$ would introduce the nonunit $|\Delta_v|$ and is not used.

### 9.3 Deformation rings and faithful acting orders

Equation (7.12) gives

$$
R^{(2)}\widehat\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\simeq R^{(1)}.
\tag{9.5}
$$

Let $\mathbb T^{(i)}$ be the faithful image of the declared trace Hecke algebra together with
the coefficient algebra on the direct sum of the primary and companion new modules. Under the
strict twisting trivialization, every good $T_w$ is multiplied by the appropriate group-like
unit and every $S_w$ by its square. Since $\Lambda_v$ already acts by scalars, coefficient
extraction identifies

$$
\mathbb T^{(2)}
\simeq\Lambda_v\otimes_{\mathcal O}\mathbb T^{(1)}.
\tag{9.6}
$$

Faithfulness is checked directly: if an element of the right side kills
$\Lambda_v\otimes N_v^{(1),+}$ and its companion, each coefficient in the group basis kills the
conductor-one carrier, hence is zero in $\mathbb T^{(1)}$. Therefore

$$
\mathbb T^{(2)}/\ker(\epsilon_v)\mathbb T^{(2)}
\simeq\mathbb T^{(1)}.
\tag{9.7}
$$

Unlike an arbitrary module-base-change argument, (9.6) proves the assertion for the faithful
acting image. It depends on the global twist identity; without that identity, exact module
augmentation would not imply (9.7).

The same strict identities transport component support at the patched level and at every
retained finite auxiliary level. Write $R^{(i)}$ and $C_v^{(i),+}$ for either corresponding
pair. If the conductor-one complex has full support under $({\rm SUP}_v)$, then for a prime
$\mathfrak P$ of
$R^{(2)}\simeq R^{(1)}\widehat\otimes_{\mathcal O}\Lambda_v$,
with contraction $\mathfrak p$ to $R^{(1)}$,

$$
C_v^{(2),+}\otimes_{R^{(2)}}^L k(\mathfrak P)
\simeq
C_v^{(1),+}\otimes_{R^{(1)}}^L k(\mathfrak P)
\simeq
\left(C_v^{(1),+}\otimes_{R^{(1)}}^L k(\mathfrak p)\right)
\otimes_{k(\mathfrak p)}k(\mathfrak P).
\tag{9.8}
$$

The last line is the nonzero $k(\mathfrak p)$-fiber followed by a field extension. Hence the
conductor-two complex also has full topological support. This uses the represented-ring and
strict-complex twist identities together; support is not inferred from module augmentation
alone. The inverse-twist companion identity gives the same conclusion for $C_v^{(2),-}$.

### 9.4 Auxiliary augmentation on both adjoint sides

Fixed-prime augmentation and Taylor--Wiles augmentation solve different problems. The former
uses the global scalar twist of Sections 9.1--9.3. For the latter, let $Q$ be a clean
Taylor--Wiles set disjoint from $v$, let $\Lambda_Q=\mathcal O[\Delta_Q]$, and write
$\mathfrak a_Q$ for its augmentation ideal. In this subsection write $P_{Q,j}^{\pm}$,
$C_{Q,v}^{\pm}$, and $N_{Q,v}^{\pm}$ for the objects at $Q$, and omit $Q$ for the empty
auxiliary set. The residual Frobenius roots at every
$x\in Q$ are distinct. With the central normalization of Section 2.3, the auxiliary old Gram
determinant satisfies

$$
D_x=(q_x+1)^2-S_x^{-1}T_x^2
\equiv-\frac{(\alpha_x-\beta_x)^2}{\alpha_x\beta_x}
\pmod{\mathfrak m},
\tag{9.9}
$$

and is therefore a unit. The fixed type at $v$ is a spectator for these correspondences.

**Proposition 9.1 (exact auxiliary primary--companion augmentation).** Assume the clean
effective diamond-torsor hypotheses at $Q$, ordered distinct residual roots, the branchwise
generic old--new decomposition, newvector relation, Galois realization, and exact local
compatibility used in the chosen localization, and $({\rm TIH}_{\mathscr F})$ on the
retained levels. Then auxiliary augmentation gives
canonical isomorphisms

$$
R_{Q,v}^{(i)}/\mathfrak a_QR_{Q,v}^{(i)}
\xrightarrow{\sim}R_v^{(i)},
\tag{9.10}
$$

$$
P_{Q,j}^{\pm}/\mathfrak a_QP_{Q,j}^{\pm}
\xrightarrow{\sim}P_j^{\pm}
\qquad(j=0,1),
\tag{9.11}
$$

and hence strict derived isomorphisms

$$
C_{Q,v}^{\pm}\otimes_{\Lambda_Q}^{L}\mathcal O
\xrightarrow{\sim}C_v^{\pm},
\qquad
N_{Q,v}^{\pm}/\mathfrak a_QN_{Q,v}^{\pm}
\xrightarrow{\sim}N_v^{\pm}.
\tag{9.12}
$$

All positive $\Lambda_Q$-Tor groups in (9.12) vanish, the primary--companion pairing
augments to the base pairing, and auxiliary and fixed-prime augmentation commute. Here $i=1$
or $2$, with the effective global ray quotient of Section 2.2 imposed for the scalar-twisted
family $i=2$.

**Proof.** The represented auxiliary functor has a unique ordered enhancement after
augmentation because the two residual Frobenius roots at each $x\in Q$ are distinct. Book
143's global augmentation theorem for Taylor--Wiles deformation problems therefore gives (9.10),
with the line, sign, and type at the disjoint spectator place $v$ unchanged.

For each of the four strict cohomology complexes, cellular cochains on the clean
deep-to-oriented cover are finite free over $\Lambda_Q$, and orbit sum identifies their
derived coinvariants with the corresponding oriented-level complex. Lemma 4.2 concentrates
both localized complexes in degree one and makes the degree-one modules finite free over the
combined coefficient algebra. Thus the derived identity gives ordinary exact coinvariants at
the deep-to-oriented stage, with no hidden group-cohomology term.

It remains to pass from oriented to hyperspecial level at $x$. Formula (9.9) makes the two-map
Gram operator invertible. Hence the old map is split injective and saturated. Its complementary
new quotient is $\mathcal O$-torsion-free; after inverting $\varpi$, every genuine new
constituent satisfies the level-raising equation $D_x=0$, while $D_x$ is a unit at the chosen
localization. The new quotient is therefore zero. The two Hensel root idempotents split the
old source, and the chosen root selects one copy of the lower term. Repeating at the places of
$Q$ proves (9.11) on the primary side. Perfect adjunction gives the companion statement with
the inverse root and inverse diamonds.

The pull, norm, and type intertwiners occupy the fixed local factor at $v$ and commute with
the auxiliary correspondences. Thus (9.11) is an isomorphism of strict complexes. Theorem 5.2
makes the new modules projective over the combined coefficient algebra, which is finite free
over $\Lambda_Q$, so derived auxiliary specialization is ordinary and gives (9.12). The
group-ring-valued pairing uses the coefficient-extraction normalization of Book 152; applying
the ring augmentation and the orbit-sum identifications gives the base pairing with no factor
$|\Delta_Q|$. The two augmentation ideals lie in independent tensor factors, so the two orders
of specialization agree. $\square$

Let $\mathbb T_{Q,v}^{(i)}$ be the faithful acting image. Compatible generators always give a
surjection

$$
\mathbb T_{Q,v}^{(i)}/\mathfrak a_Q\mathbb T_{Q,v}^{(i)}
\twoheadrightarrow\mathbb T_v^{(i)}.
\tag{9.13}
$$

Proposition 9.1 does not assert that (9.13) is injective. Exact module augmentation does not
exclude an element whose matrices lie in $\mathfrak a_Q$ but which is not an augmentation
multiple inside the acting order. Book 175 proves that (9.13) becomes an isomorphism once the
base conductor-one deformation action is known to be faithful; under the reduced comparison
there, this is equivalent to its generic-rigidity theorem, or equivalently to global
reducedness. No separate
primary-versus-companion module gap remains.

## 10. Determinant and adjoint ledger

### 10.1 Determinant of the strict complex

For a cochain complex in degrees $0,1$, use

$$
\operatorname{Det}(C_v^+)
=\det(P_0^{+,\oplus2})\otimes\det(P_1^+)^{-1}.
\tag{10.1}
$$

Because $C_v^+\simeq N_v^+[-1]$,

$$
\operatorname{Det}(C_v^+)\simeq\det(N_v^+)^{-1}.
\tag{10.2}
$$

Equation (4.6) gives the same underlying determinant line for the companion complex. These are
formal determinant identities for the automorphic complexes; they do not identify this line
with a Galois cotangent determinant.

### 10.2 The full cross-pairing Gram operator

There are same-coefficient composites

$$
G_v^+=r_v^+p_v^+:
P_0^{+,\oplus2}\longrightarrow P_0^{+,\oplus2},
\qquad
G_v^-=r_v^-p_v^-:
P_0^{-,\oplus2}\longrightarrow P_0^{-,\oplus2}.
$$

They are transposes under the primary--companion pairing. Equivalently, they encode the
cross-pairing of the primary and companion old images. With the conventions of (2.7), either
block has matrix

$$
G_v
=\begin{pmatrix}
q+1&T_{01}\\
T_{10}&q+1
\end{pmatrix}.
\tag{10.3}
$$

In the standard central orientation this is

$$
G_v=
\begin{pmatrix}
q+1&T_v\\
S_v^{-1}T_v&q+1
\end{pmatrix},
\qquad
D_v=\det G_v=(q+1)^2-S_v^{-1}T_v^2.
\tag{10.4}
$$

If a central square root $s_v^2=S_v$ has been chosen and the second vertex basis is rescaled
accordingly, put $a_v=s_v^{-1}T_v$. Only in that rescaled block do the primitive sign vectors
give factors

$$
g_\varepsilon=q+1-\varepsilon a_v,
\qquad
D_v=(q+1-a_v)(q+1+a_v).
\tag{10.5}
$$

At $q\equiv-1\pmod\ell$ both factors can be nonunits, so the invariant datum is the full
cross-pairing matrix (10.3) and its Smith module. No identification
$\operatorname{St}^+\simeq\operatorname{St}^-$ has been made.

### 10.3 The local incidence equation and the no-cross-map rule

For arithmetic Frobenius with special eigenvalues $qa,a$, trace $t$, and determinant $d$, the
line-incidence resultant is

$$
qt^2-(q+1)^2d=0.
\tag{10.6}
$$

The same symmetric equation holds after inverting both eigenvalues for geometric Frobenius.
Under Book 170's reciprocity map, substitute the geometric Hecke data $t=T_v$ and $d=qS_v$;
then (10.6), after dividing by the unit $q$, is

$$
T_v^2-(q+1)^2S_v=-S_vD_v.
\tag{10.7}
$$

Thus the Galois incidence equation and the automorphic Gram determinant have the same image as
principal equations in the faithful Hecke order, up to the displayed unit. This scalar identity
comes from the common trace and determinant normalization.

There is no canonical pre-$R=T$ chain map between the local cotangent complex and the
automorphic degeneracy or Gram complex. In particular, (10.7) does not prove equality of their
determinant lines, Fitting modules, or multiplicity-scaled lengths. Such a comparison may be
made only after a later theorem identifies the relevant rings and primitive lattices, or after
an independent cross-determinant theorem is supplied. No such theorem is asserted here.

## 11. The reusable one-prime theorem

### 11.1 Statement

**Theorem 11.1 (conditional one-prime type complex and component support).** Assume the clean
datum of Chapter 2, use the proved $({\rm TPE}_v)$, and assume
$({\rm AIH}_{\mathscr F})$.  Proposition 3.0B proves $({\rm TIC}_v)$, Propositions
5.0--5.0B prove $({\rm TIH}_{\mathscr F})$ in both the projector and nonbanal ranges, and
Propositions 6.0--6.0B prove $({\rm PRI}_{\rm type})$ in both ranges. The generic-kernel and
faithful-order assertion in clause 6 additionally assumes Book 125's component-routing source
condition, and its switched-definite form assumes $({\rm NU}_{\rm type})$. Clause 11 also assumes the
effective auxiliary diamond torsors, ordered distinct residual roots, and the branchwise
generic old--new and local-compatibility hypotheses of Proposition 9.1. Then, for every clean
auxiliary level $Q$:

1. the primary and companion cohomology terms $P_j^\pm$ are finite free over $A_Q$ and carry
   perfect inverse-character adjoint pairings;
2. the strict complexes (1.2)--(1.3) satisfy
   $$
   C_v^-\simeq R\operatorname{Hom}_{A_Q}(C_v^+,A_Q)[-1];
   $$
3. the primary map is split injective over $A_Q$, its quotient $N_v^+$ is finite projective,
   and $C_v^+\simeq N_v^+[-1]$;
4. every derived change of the coefficient algebra is ordinary on $N_v^+$ and has zero
   positive Tor;
5. the extreme residue maps have coefficient one; if $({\rm NU}_{\rm type})$ also holds, so
   does the graph--definite type comparison (6.2);
6. the normalization and component data are (6.7)--(6.11), with
   $\mathcal C_{\mathrm{br},v}^+$ retained; under the additional source condition just stated,
   (6.12) gives equality of the typed curve-new and graph faithful image orders, and
   $({\rm NU}_{\rm type})$ transports that equality to the switched-definite order;
7. the scalar chart is the named closure (7.5) with its flag and Kummer directions, while the
   vexing chart retains the full Gram and primary--companion blocks;
8. for the strict global ray quotient of Section 2.2, scalar twist augmentation gives
   (9.2)--(9.7), changes the Galois determinant by $\boldsymbol\chi_v^2$, and forgets no
   enhancement;
9. if $({\rm SUP}_v)$ holds, the conductor-one primary and companion complexes have full
   topological support on the named enhanced special deformation component at patched and
   finite level; in the scalar row, (9.8) gives the same support
   on the conductor-two scalar-twisted component;
10. the determinant conventions are (10.1)--(10.7), with no pre-$R=T$ cross-chain
    isomorphism;
11. auxiliary augmentation gives (9.10)--(9.12) for the represented rings, both strict
    complexes, both new modules, their pairings, and both orders of fixed/auxiliary
    specialization. For faithful acting images it gives the canonical surjection (9.13), whose
    injectivity is deferred to the nonminimal comparison.

The theorem remains conditional on the finite family $({\rm AIH}_{\mathscr F})$.
The principal-node stabilizer theorem for these actual rows is unconditional by Book 122,
Corollary 9.11.  The quotient-new injection (5.0d) and filtered-cofiber comparison (6.0d) are
proved here in the nonbanal range and are not additional inputs. The
graph--definite comparison, scalar augmentation, and support clauses state their separate exact
hypotheses.  In particular $({\rm NU}_{\rm type})$ and $({\rm SUP}_v)$ do not follow from
$({\rm AIH}_{\mathscr F})$.
In particular, clause 9 does not infer support from the surjection
$R^{\rm sp}\twoheadrightarrow\mathbb T^{\rm sp}$ of Book 170.

### 11.2 Proof

**Proof.** Proposition 3.0B and Proposition 3.1 give the actual type coefficient
objects and their coefficient-one node complex. Proposition 4.1 and Lemma 4.2 give strict
finite-free middle cohomology; pull--norm adjunction gives clause 2. Lemma 5.1 applies the
type-Ihara theorem supplied by Propositions 5.0--5.0B, and the
unit-minor argument of Theorem 5.2 gives clauses 3--4. The Book 139 input enters clauses 5--6
through Theorem 6.2 and the filtered comparison of Propositions 6.0--6.0B.

Proposition 6.1 gives the first assertion of clause 5, and
$({\rm NU}_{\rm type})$ gives its
graph--definite assertion. The corrected filtration of
Theorem 6.2 and the cokernel sequence (6.11) give clause 6 without deleting either finite
module. Proposition 6.3 proves the conditional generic-kernel and integral faithful-order
assertions appended to that clause. Chapter 7 proves the two exceptional charts and the determinant-square rule. The
global twist identity for the strict ray quotient proves all parts of clause 8,
including faithful acting images. The depth-and-boundary proof of Theorem 8.3 gives the
conductor-one assertion of clause 9, and (9.8) transports it to the scalar-twisted face using
the same strict quotient. Proposition 9.1 proves clause 11 by represented-ring augmentation and
termwise primary--companion old--new control. Chapter 10 proves the normalization ledger and
explicitly stops before any cross-complex comparison. $\square$

## 12. Scope, dependencies, and boundaries

### 12.1 The reusable one-place interface

The output of this book is the typed pair

$$
C_v^+=[P_0^{+,\oplus2}\xrightarrow{p_v^+}P_1^+]
\simeq N_v^+[-1],
\qquad
C_v^-=[P_1^-\xrightarrow{r_v^-}P_0^{-,\oplus2}]
\simeq R\operatorname{Hom}(C_v^+,A_Q)[-1],
\tag{12.1}
$$

together with strict coefficient-change maps and, under $({\rm AIH}_{\mathscr F})$, the
coefficient-one extreme residue
and corrected component complex

$$
X_v^+\longrightarrow(X_v^-)^\vee\longrightarrow L_v^+.
\tag{12.2}
$$

The last complex retains $\Phi_v^{\rm type}$ and
$\mathcal C_{\mathrm{br},v}^+$ as distinct finite corrections. For the strict global scalar ray
quotient of Section 2.2, (9.1)--(9.7) add fixed-prime augmentation. Under $({\rm SUP}_v)$,
Theorem 8.3 adds topological support on the named conductor-one component; with that quotient,
(9.8) transports it to the conductor-two scalar-twisted component. At every clean auxiliary
set, Proposition 9.1 adds exact represented-ring, primary, companion, complex, and pairing
augmentation. Only injectivity of the auxiliary acting-order quotient (9.13) remains outside
this book.

This interface controls only the chosen place $v$. It contains no calculation of intersections
of old images at different places, no mixed-Ihara statement, and no simultaneous-component
support assertion. In particular, Theorem 8.3 cannot be iterated formally to obtain support on
an intersection of local conditions.

### 12.2 Direct dependency ledger

| source | exact use | boundary retained |
|---|---|---|
| Book 6 | odd-exponent local--global character theorem and ray-class/unit compatibility used for the strict quotient (2.2a)--(2.2d) | only the prescribed finite odd-exponent tuple is globalized; every added conductor place is retained in the datum |
| Book 17 | effective finite-etale principal covers, common refinements, and Galois closures | it constructs the generic cover, not its bad-fiber stabilizers |
| Book 21 | exact descent of finite-free representations to lisse coefficient sheaves | lisse generic descent does not extend the sheaf across the parahoric fiber |
| Book 22 | the full tame strict-node complex, exact reduction by finite wild image, semidirect residue-Galois action, normalization totalization, invariant-stable pull--trace (including every expansion-one sheet used here), and geometrically constant ray projection formula | it computes a supplied annular monodromy representation after its wild group is identified; it does not identify the principal PEL decomposition groups |
| Book 65 | perfect complexes, derived base change, Tor, and determinant conventions | applies only after strict projective models exist |
| Book 67 | represented enhanced special matrix-and-line condition and exceptional tangent directions | the flag and Kummer directions remain at scalar points |
| Book 69 | change of represented global deformation data by completed local base change, the exact tangent sequence, and the relative formal-smoothness criterion | it proves the common boundary quotients (8.2d), but not the application-specific relative obstruction vanishing in (8.2f) |
| Book 70 | depth, support, annihilator radicals, and Fitting cautions | topological support is not faithfulness |
| Books 118--119 | neat arithmetic stabilizers, center-detecting fine level, and triviality of automorphisms of the rigidified PEL tuple | ineffective central units are not geometric inertia; arbitrary non-neat coarse level still requires its actual stabilizers |
| Book 121 | free fine-level change, quotient-stack descent, and the distinction between a deck group and point stabilizers | a nonunit deck-group order is not inverted; only actual coarse stabilizers enter Proposition 3.0B |
| Book 122 | parahoric incidence model, node chart, finite-flat base degeneracy maps, actual objectwise finite-flat common principal/ray normalization, isomorphic lifted top legs, the proved level-one theorem $({\rm DLB}_1)$, all active finite-depth Drinfeld normalization/invariant rings (9.29k)--(9.29l), the explicit level-one divisor/Bruhat/node ledger, the raw higher branch/inertia/residue/node-annular and boundary-stabilizer ledger (9.29r)--(9.29x), Proposition 9.4's actual-common-factor routing and node coefficients, Proposition 9.5's invariant-field, Cartier, group and normalized-compositum reduction, Proposition 9.6's endpoint formalism, Proposition 9.7's Milnor-tube formalism, Proposition 9.8's $({\rm RGC}_v)$, Proposition 9.9's strict ray field/unit and endpoint factors, Proposition 9.10's completed tubes, and Corollary 9.11's $({\rm PNS}_v)_{\rm act}$ | arbitrary intermediate representations and arbitrary cyclic ray data remain outside Corollary 9.11; the actual rows of this book do not |
| Book 125 | characteristic-zero packet decomposition and semisimplicity for the full component-routing algebra on the common principal cover | Proposition 6.3 uses it only after the typed integral filtration has been proved; it supplies no typed extension or residue lattice |
| Book 138 | quotient primary and augmentation companion lattices, twists, type labels, and the derived parahoric coefficient-complex interface | outside the integral-projector range its representation rows do not by themselves prove (6.0d); Proposition 6.0B adds the actual fixed/moving contraction |
| Book 139 | Theorem 14.1 under localized $({\rm AIH})_{v,\mathfrak m}$ and its corrected branch filtration | this book assumes the finite family $({\rm AIH}_{\mathscr F})$; Book 139 neither proves it nor extends it to type coefficients |
| Book 140 | the datum-specific node-uniformization interface and the source-closed constant-coefficient generic-support proof | its constant-coefficient theorem does not prove the flagged superspecial groupoid classification or $({\rm BCD}_v)$; the nonbanal coefficient assertions (5.0d) and (6.0d) are proved here |
| Book 141 | adequacy and split-regular detector input for the Taylor--Wiles clause of $({\rm SUP}_v)$ | prime selection and patching do not follow from adequacy alone |
| Book 143 | Taylor--Wiles sets for the represented nonminimal problem, with $v$ avoided and the recomputed dual Selmer group killed; exact augmentation with ordered distinct residual roots | selection requires the full split-detector and exact local-orthogonal hypotheses; augmentation fails to recover an unenhanced problem if the ordered eigenspaces are not uniquely liftable |
| Book 145 | simultaneous finite marked diagrams, coherent diagonal patching, and Mittag--Leffler passage of retained quotient maps | it preserves the common-boundary quotient (8.2e), but creates neither a reverse section nor relative formal smoothness |
| Book 152 | effective auxiliary torsors, regular group modules, pairings, and compatible finite-level presentations | it does not itself perform the nonminimal patch; module augmentation alone does not imply acting-order augmentation |
| Book 170 | Hecke-valued representation, local factorization, and $R^{\rm sp}\twoheadrightarrow\mathbb T^{\rm sp}$ | no deformation faithfulness or component coverage follows from the surjection |
| Book 171 | exact global deformation datum and variance | conductor labels do not replace represented functors |
| Book 172 | retained Taylor--Wiles selection and marked patching mechanism, minimal $R=T$, and the nonzero free lower boundary carrier | no nonminimal equality is imported |

The exact direct-dependency row is therefore

```text
174 | 6, 17, 21, 22, 65, 67, 69, 70, 118, 119, 121, 122, 125, 138, 139, 140, 141, 143, 145, 152, 170, 171, 172
```

Book 139's transitive geometric prerequisites are Books 16, 38--39, 118, 122, and 124. Their
roles remain exactly those recorded there; they are not new unconditional Ihara inputs. No
later nonminimal comparison is used.

### 12.3 Status of the four delicate interfaces

The earlier gaps have the following exact status.

| interface | status in this book |
|---|---|
| primary/companion type control on curves | Book 22 proves the strict-node formalism and exact finite-wild reduction, while Book 122 constructs the normalized tower and ray factor, proves $({\rm DLB}_1)$, identifies every active finite-depth normalization ring, and computes the raw higher branch/inertia/residue/node-annular and boundary-stabilizer ledger. Its explicit divisor, stabilizer, and Bruhat equations prove the wild-invariant extreme lines and unique node sheet; Proposition 9.4 promotes routing, multiplicity, expansion one, and Hecke/transpose compatibility to the actual common factor. Propositions 9.5--9.8 give the general arithmetic/tube reduction and $({\rm RGC}_v)$. Proposition 9.9 chooses the actual ray quotient and computes its field, unit, valuations, leading coefficients, factors and intersection; Proposition 9.10 computes the completed tubes, actions and generization maps; Corollary 9.11 proves $({\rm PNS}_v)_{\rm act}$, and hence $({\rm TPE}_v)$. Proposition 3.0B proves actual unit-order coarse descent. Proposition 5.0 reduces type-Ihara to (5.0d), Proposition 5.0A identifies the exact Bockstein/primitivity obstruction, and Proposition 5.0B kills it by the fixed/moving Mackey contraction |
| primitive type residues | Proposition 6.0 proves them in the integral-projector range.  In the nonbanal range Proposition 6.0A first proves exactness of the generic new-module quotient row; Proposition 6.0B then contracts the associated graded defect of (6.0d) by the same fixed/moving identity and proves (6.0c).  The switched definite comparison still requires the distinct flagged node classification of Lemma 6.1A |
| faithful acting-image augmentation | fixed-prime augmentation is proved in Sections 9.1--9.3 by a genuine global twist and coefficient extraction; Proposition 9.1 proves auxiliary represented-ring, primary/companion complex, module, and pairing augmentation, while (9.13) remains only a surjection on auxiliary acting images until the base action is known faithful |
| cross determinant | unavailable and not claimed: (10.7) is only equality of principal scalar equations in the faithful Hecke order, not a chain map or determinant-line comparison |

The following logical boundaries remain in force.

| possible overreach | exact boundary |
|---|---|
| constant étale flag cover at the bad integral model | Section 3.4 uses the normalized principal tower and the finite-wild/procyclic node complex $[M\xrightarrow{T-1}M]$; Book 122, Proposition 9.4 proves actual-common-factor node routing and expansion one, Propositions 9.9--9.10 compute the actual ray factors and completed tubes, and Proposition 9.8 proves the oriented component correspondence; the special fiber is never replaced by $q+1$ copies |
| averaging over a group of nonunit order | Proposition 3.0B uses actual geometric stabilizers for coarse descent, and Propositions 5.0B and 6.0B average only over the $q$-element moving orbit, whose order is a unit |
| perfect cohomology versus projective cohomology | Lemma 4.2 uses residual fiber concentration and a minimal complex |
| unconditional use of Book 139 as type-Ihara | Constant terms use $({\rm AIH}_{\mathscr F})$; Proposition 5.0 performs the formal reduction and Proposition 5.0B separately proves the nonbanal type term from the actual Mackey square |
| composition across primary and companion lattices | Section 4 distinguishes $p_v^\pm$ and $r_v^\pm$; only same-coefficient Gram composites are formed |
| rational type projector | Lemma 5.1 uses integral flag excision |
| typed generic support before the filtration | Proposition 6.3 kills the two finite corrections only after inverting $\varpi$, uses Book 125's semisimple component-routed packet decomposition to prove equality of generic Hecke kernels, and contracts those kernels to equality of integral faithful image orders |
| coefficient Tor before projectivity | Theorem 5.2 first proves split injectivity and a projective quotient |
| deformation-ring Tor | Sections 4.3 and 5.2 explicitly exclude that inference |
| component module versus branch Smith module | Equations (6.7) and (6.11) retain both |
| a scalar Frobenius-selected line | Equations (7.6)--(7.10) retain the flag, characters, and Kummer directions |
| reduction of the vexing block to one signed factor | Chapters 7 and 10 retain the full matrix and both extension orientations |
| support inferred from $R\twoheadrightarrow\mathbb T$ | Theorem 8.3 assumes the explicit datum $({\rm SUP}_v)$ and uses boundary nonvanishing plus depth |
| topological support promoted to faithfulness | Equation (8.6) retains the nilradical |
| module augmentation promoted to acting-order augmentation | Equations (9.6)--(9.7) use the global twist and coefficient extraction at the fixed prime, while auxiliary augmentation stops at the surjection (9.13); Book 175 derives its injectivity from base faithfulness |
| a pre-$R=T$ cross-determinant isomorphism | Section 10.3 expressly forbids it |
| one-place support promoted to simultaneous support | Section 12.1 states the strict one-place boundary |

The bounded conditional theorem has no hidden internal implication left to supply. Its exact
external hypotheses are: $({\rm AIH}_{\mathscr F})$ for the constant rows and Book 139's
normalization filtration;
the flagged superspecial groupoid classification of Lemma 6.1A only for the switched
graph--definite comparison; the strict global ray choice (2.2a)--(2.2d) for scalar
augmentation and transport of support to the scalar-twisted face;
and $({\rm BCD}_v)$, in the relative Cartier-switch form (8.2f) after the source-closed local
chart, common-boundary quotient, and boundary carrier, only for component support.
Actual unit-order coarse descent, nonbanal quotient-new primitivity, and filtered cofiber
strictness are conclusions of Propositions 3.0B, 5.0B, and 6.0B, respectively.

### 12.4 Source-closure verdict

The six interfaces do not form one missing theorem.  The three one-prime type-algebra
interfaces are source-closed here; the flagged node classification and the relative boundary
comparison remain conditional for their separate uses.

The arithmetic constant-vector map, its new Bockstein, and the filtered normalization cofiber
are constructed in this book; Books 138--140 supply the local flag rows, constant saturation,
and consumer boundaries, while Books 175--177 only use the resulting conclusions.  The only global
node-to-definite formulation is Book 140's conditional superspecial construction; Books
118--124 construct the PEL functor, complex uniformization, local model, Hasse set, and node
routing, but no basic-locus quasi-isogeny equivalence.  For the boundary problem, Books 69,
143, and 145 do contain the generic datum-change, common-prime, and marked-diagram theorems.
(8.2d)--(8.2e) extract their actual common-boundary quotient consequence.  Their
formal-smoothness criteria do not prove the application-specific
relative obstruction vanishing in (8.2f).  The first two nonbanal statements are supplied by
Propositions 5.0B and 6.0B.  The flagged node equivalence and the
narrower Cartier-switch transversality assertion remain genuine conditional boundaries.

| interface | source-closure verdict | first exact obstruction or proof |
|---|---|---|
| type-coefficient extension | proved for the actual rows | the actual common normalized tower is constructed and objectwise finite flat. Book 122, Propositions 9.3--9.8 prove the active rings, group ledger, routing, general arithmetic reduction, tube formalism, and $({\rm RGC}_v)$. Proposition 9.9 supplies the strict ray field/unit, exact endpoint triples, the factor degrees determined by $[\gamma_L]$, and the actual intermediate intersection. Proposition 9.10 proves the completed tubes, cohomology, actions and generization maps; Corollary 9.11 proves $({\rm KBL}_v)_{\rm act}$, $({\rm BTK}_v)_{\rm act}$, $({\rm HDB}_v)_{\rm act}$ and $({\rm PNS}_v)_{\rm act}$ |
| type-Ihara | proved in every clean range under $({\rm AIH}_{\mathscr F})$ | Proposition 5.0 proves the augmentation companion in every range and both endpoints when $q+1$ is a unit.  For $q\equiv-1\pmod\ell$, Proposition 5.0A identifies the exact Bockstein/primitivity obstruction and Proposition 5.0B proves its vanishing by equating fixed evaluation with normalized moving-orbit trace |
| primitive residue | proved in every clean range under $({\rm AIH}_{\mathscr F})$ | Proposition 6.0 proves vanishing when $q+1$ is a unit.  Proposition 6.0A proves that the generic old cokernel commutes with the coefficient row, and Proposition 6.0B proves nonbanal strictness of the global normalization/graph filtration, so (6.0d) is a filtered quasi-isomorphism and $\operatorname{Ob}_{\rm PRI}(v)=0$ |
| node uniformization | blocked at one geometric classification | Book 140 still requires the superspecial PEL classification. Prime-to-$v$ level and component routing can change the global node groupoid without changing any completed local node chart, so the existing local models cannot prove it. Lemma 6.1A proves that if it is formulated as an equivalence of flagged node groupoids, transport of the quotient/augmentation stabilizer representations and coefficient-one pairing is formal, not a second theorem |
| generic support | proved in the constant clean special block, and proved for the typed block after the already isolated type inputs | Book 140, Section 8.3 proves the constant equality; Proposition 6.3 uses Book 125's semisimple component-routed decomposition and (6.7)--(6.9) to prove the typed generic kernel equality and integral faithful-order equality, without adding a new hypothesis |
| one-prime component support | after the proved $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$, blocked only at the nonminimal boundary comparison | $({\rm PNS}_v)_{\rm act}$ is proved; the boundary carrier and nonzero boundary class are proved in Sections 8.2--8.3; Chapter 7 proves the named local special closure, while (8.2d)--(8.2e) prove simultaneous patching of the common boundary quotient.  The exact remaining $({\rm BCD}_v)$ theorem is (8.2f): the lower boundary parameter (or scalar block) is transverse and the special relaxation is relatively formally smooth.  Proposition 8.1A then makes dimension balance and unique-component routing formal |

In particular, $({\rm DLB}_1)$, the active higher normalization rings, Proposition 9.5's
invariant-field/Cartier/group calculation, the actual Kummer and tube ledgers, and
$({\rm PNS}_v)_{\rm act}$ are proved, not hypotheses.  The algebra above removes type-Ihara
and primitive residue as later hypotheses in both the projector and nonbanal ranges.  It does
not prove the distinct flagged superspecial classification or the later support theorem.

### 12.5 Conclusion

The one-prime object is rigidly typed. Its primary coefficient is the quotient Steinberg
lattice on the actual Shimura tower; its companion is the augmentation lattice with inverse
twist. Their correctly typed pull and norm maps form perfect adjoint complexes. Under the exact
constant-row hypothesis $({\rm AIH}_{\mathscr F})$, the proved type-incidence and type-Ihara
statements place the primary complex in its new degree and make its new module projective over
every declared tame and auxiliary coefficient algebra.
Propositions 5.0 and 6.0 show that, when $q+1$ is a coefficient unit, constant Ihara supplies
type-Ihara and the integral flag projector also supplies primitive residue.  When
$q\equiv-1\pmod\ell$, Proposition 5.0A identifies the primary new-cokernel injection (5.0d)
with an arithmetic new-Bockstein/integral-primitivity theorem.  Proposition 5.0B proves it by
equating fixed evaluation with normalized trace over the $q$ moving flags, without dividing
by $q+1$.  After type-Ihara is established, Proposition 6.0A proves exactness of the generic
old quotient and Proposition 6.0B proves the primitive filtered-cofiber comparison (6.0d).

Under $({\rm AIH}_{\mathscr F})$, the bad fiber retains all of its
information: the extreme
residue has coefficient one, the raw graph discriminant remains the component module, and the
normalized branch map contributes the separate Smith module
$\mathcal C_{\mathrm{br},v}^+$. Scalar points retain their flag and
Kummer directions; vexing points retain the full Gram block. The separately stated support and
global-twist hypotheses give exactly the one-place support and augmentation conclusions they
justify. At auxiliary level, Proposition 9.1 gives exact augmentation of the represented ring,
both adjoint complexes, their new modules, and their pairing; the faithful acting-order map is
only the surjection (9.13) here.  The local special boundary chart and simultaneous patched
boundary quotient are source-closed.  Relative Cartier-switch transversality (8.2f) remains
precisely $({\rm BCD}_v)$; dimension balance and component routing follow from it by
Proposition 8.1A.
No stronger comparison is inferred.
