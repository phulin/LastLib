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
- [12. Scope, dependencies, and audit](#12-scope-dependencies-and-audit)

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

With each named hypothesis imposed only at the use stated below, this book proves the following
one-place implications. In particular, $({\rm TIC}_v)$ and
$({\rm TIH}_{\mathscr F})$ govern the strict type complexes;
$({\rm AIH}_{\mathscr F})$ governs the constant-coefficient flag terms and corrected
normalization filtration; $({\rm PRI}_{\rm type})$ governs global primitive extreme residues;
$({\rm NU}_{\rm type})$ governs only the graph--definite comparison; and $({\rm SUP}_v)$
separately governs component support.

1. The constant-coefficient theorem transfers through the actual flag resolution to the
   quotient primary and augmentation companion systems.
2. The primary map is a split injection over the complete local coefficient algebra, so its
   new module is finite projective and every tame or auxiliary derived face has zero positive
   Tor.
3. The primary and companion complexes are perfect adjoint duals.
4. The extreme nearby-cycle residues have coefficient one, but the normalized-branch
   correction $\mathcal C_{\mathrm{br},v}$ remains in the middle filtration.
5. Under the explicit boundary-chart and depth hypotheses of Chapter 8, the complex has full
   topological support on the named enhanced special component; the scalar-twisted face
   additionally requires the genuine global ray quotient.
6. A genuine global scalar twist makes fixed-prime augmentation strict for deformation rings,
   complexes, new modules, pairings, and faithful acting orders.

The type-incidence hypothesis $({\rm TIC}_v)$ and type-Ihara hypothesis
$({\rm TIH}_{\mathscr F})$ are not consequences of (1.5): Book 139 expressly treats constant
coefficients, for which cocycles are homomorphisms, whereas a nontrivial type local system has
crossed homomorphisms. Book 140 lists extension of the type sheaf, compatibility of pull and
norm, and type-specific residual Ihara as extra inputs. Its node uniformization and
generic-support assertions also remain datum-specific hypotheses. The boundary-chart and
local-dimension comparison used for component support is an additional one-prime hypothesis,
recorded exactly in Chapter 8. The book does not construct a canonical chain map from a Galois
cotangent complex to an automorphic Gram complex before $R=T$. It does not delete a Néron
component group or a branch correction, and it never promotes one-place support to simultaneous
support at several places.

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

At a scalar-twist place choose an effective cyclic $\ell$-power quotient $\Delta_v$ of a
global ray class group, with local inertia at $v$ mapping onto $\Delta_v$. This is an actual
global quotient: the unit, central, and archimedean compatibilities of Book 6 are part of the
choice. Put

$$
\Lambda_v=\mathcal O[\Delta_v],
\qquad
\boldsymbol\chi_v:G_F\longrightarrow\Lambda_v^\times.
\tag{2.3}
$$

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

Choose a common normal principal subgroup at $v$ contained in the two adjacent vertex groups
and the edge group. On the generic fibers it gives finite étale Shimura covers with finite deck
groups $H_0,H_1,H_e$. If $W$ is a finite free representation of one of these groups, let

$$
\mathscr V_j(W)
\tag{3.5}
$$

denote the lisse sheaf obtained by effective finite-étale descent from the corresponding cover.
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
extension is an additional piece of type geometry.

**Hypothesis $({\rm TIC}_v)$ (type-incidence compatibility).** On the quotient stack of the
fine parahoric PEL model, the actual principal-level tower extends over the local-model diagram,
with all geometric automorphism groups used for coarse descent of order invertible in
$\mathcal O$, and:

1. the sheaves (3.6)--(3.9) extend as constructible finite free coefficient complexes;
2. their pullbacks to the two normalization branches and node stratum are the associated
   complexes for the actual vertex, edge, and flag stabilizers;
3. both degeneracy pulls and finite-flat norms extend, preserve the two flag rows, and remain
   adjoint under (3.10); and
4. the combined geometric and coefficient nearby-cycle complex is the cellular flag
   resolution, compatible with the normalization filtration.

Book 122 supplies the constant-coefficient local model, but it does not prove this extension
for the nontrivial quotient and augmentation type systems. Book 140, Section 13.1, records
these same requirements as external hypotheses for a type-enhanced variant. No prime-to-$\ell$
condition is placed on the finite flag group: its order may be divisible by $\ell$ in the scalar
or vexing range, and no invariants under that group are averaged.

**Proposition 3.1 (coefficient-one flag incidence).** Under $({\rm TIC}_v)$, the two sequences
(3.6)--(3.7) remain exact in the constructible category and are adjoint under (3.10). On a
strict node, the oriented extreme residue maps in the combined coefficient and geometric
nearby-cycle complex have coefficients $1$ or $-1$; the complex is not $q+1$ constant copies.

**Proof.** By $({\rm TIC}_v)$ the calculation may be made before effective descent on the
actual fine local-model diagram. The universal edge has two endpoints, so its cellular boundary
is $e\mapsto(v_1-v_0)$. After an orientation is chosen, its entries are $1,-1$. Tensor this
cellular resolution with the exact representation sequences

$$
0\to\mathcal O\mathbf1\to P_v\to\operatorname{St}_v^+\to0,
\qquad
0\to\operatorname{St}_v^-\to P_v\to\mathcal O\to0.
\tag{3.11}
$$

These sequences split as underlying $\mathcal O$-modules, so totalization preserves exactness,
although they need not split equivariantly after reduction. The transpose cellular boundary,
together with (3.4), gives the companion assertion. Prime-to-$\ell$ descent is exact by the
stabilizer clause of $({\rm TIC}_v)$. This calculation proves the coefficient-one consequence;
it does not prove the existence clause that was explicitly assumed. $\square$

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

**Hypothesis $({\rm TIH}_{\mathscr F})$ (type Ihara).** For every quotient-primary and
augmentation-companion coefficient object that occurs in the finite flag diagram,

$$
K_D(\overline W)=0.
\tag{5.0a}
$$

This is the exact type-specific residual Ihara input missing from Books 138--141, 152, and 170--172. The
permutation terms are already constant-coefficient cohomology on actual flag subgroups by
Shapiro and belong to $\mathscr F_v(Q)$; no extra hypothesis is imposed on them. The type
hypothesis is stated for every actual spectator level because one instance does not propagate
automatically through the diagram.

**Lemma 5.1 (residual type injectivity).** Assume $({\rm TIC}_v)$ and
$({\rm TIH}_{\mathscr F})$. Then

$$
p_v^+\otimes_{A_Q}k:
P_0^{+,\oplus2}\otimes k\longrightarrow P_1^+\otimes k
\tag{5.1}
$$

is injective. The companion pull $p_v^-\otimes k$ is injective as well. Equivalently, the
adjoint norms $r_v^-\otimes k$ and $r_v^+\otimes k$ are surjective. The actual tame and
auxiliary spectator levels are the ones occurring in $\mathscr F_v(Q)$.

**Proof.** Hypothesis $({\rm TIC}_v)$ identifies the geometric degeneracy maps with the
oriented restriction maps in (5.0) and makes the two flag rows an exact adjoint diagram.
The constant entries and, by Shapiro, the permutation entries are the portion controlled by
$({\rm AIH}_{\mathscr F})$, but they do not imply the endpoint assertion. The quotient and
augmentation entries have zero kernel by $({\rm TIH}_{\mathscr F})$, and
$({\rm TIC}_v)$ identifies them with the asserted primary and companion maps.
Perfect transposition gives surjectivity of both norms. No rational projector or averaging is
used. $\square$

The two hypotheses cannot be merged. The finite list (1.5) is indispensable for Book 139's
constant normalization filtration, while (5.0a) is the independent crossed-coefficient
obstruction. Non-Eisenstein localization alone removes neither.

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

## 6. Nearby cycles, graph terms, and the branch correction

### 6.1 Primitive residue with type coefficients

Let $\Gamma_v$ be the oriented geometric dual graph of the Iwahori special fiber. Apply the
constructible flag-incidence complex of Proposition 3.1 to the normalization sequence. Let
$X_v^+$ be its primary cycle lattice and let $X_v^-$ be the companion cycle lattice.

**Hypothesis $({\rm PRI}_{\rm type})$ (primitive type residue).** After localization and
residual specialization, the top primary and bottom companion residue sequences obtained from
the constructible normalization diagram remain exact: the quotient by the normalization layer
maps onto $X_v^+(-1)$, and dually $X_v^-$ embeds into the bottom companion layer, with no
additional snake-lemma class from the nonsemisimple flag rows.

This is stronger than the nodewise coefficient-one calculation of Proposition 3.1. Books 138--141, 152, and 170--172 do not prove the required global exactness for these type coefficients; Book 140's
consumer ledger identifies precisely this primitive-residue or bottom-lattice input as still
missing.

**Proposition 6.1 (coefficient-one extreme residues).** Under $({\rm TIC}_v)$,
$({\rm AIH}_{\mathscr F})$, $({\rm TIH}_{\mathscr F})$, and
$({\rm PRI}_{\rm type})$, the top
primary residue and bottom companion residue are primitive and give

$$
\operatorname{gr}_2N_v^+\simeq X_v^+(-1),
\qquad
\operatorname{gr}_0(N_v^+)^\vee\simeq X_v^-.
\tag{6.1}
$$

The maps commute with $A_Q$-base change, Hecke correspondences, branch reversal, and
primary--companion adjunction.

**Proof.** Proposition 3.1 computes the combined coefficient and geometric nearby cycles on
each node. An oriented node generator maps to its edge generator with coefficient $1$; reversing
orientation changes both signs. Hypothesis $({\rm PRI}_{\rm type})$ says that, after forming the
global quotient and augmentation rows, no residual snake-lemma obstruction remains. Residual
exactness and Nakayama then make the integral top map a primitive surjection; perfect
primary--companion transposition makes the bottom map a primitive injection. Hence no
type-created finite index appears in either extreme residue. The argument deliberately does not
claim that a boundary matrix with a nontrivial local system is automatically totally
unimodular. $\square$

For the comparison with a switched definite module one needs the following datum-specific
refinement of Book 140's node hypothesis.

**Hypothesis $({\rm NU}_{\rm type})$.** The superspecial node bijection is equivariant for the
actual flag stabilizers and their primary and companion coefficient actions; its stabilizer
weights are units; and an oriented node generator with coefficient vector maps to the
characteristic function of the corresponding switched definite class with that same vector.

The constant-coefficient node theorem in Book 140 does not by itself prove this refinement;
Book 140, Section 13.1 lists it as the extra input for a type-enhanced variant. Under
$({\rm NU}_{\rm type})$,

$$
X_v^+\xrightarrow{\sim}S_v^{\dagger,+}
\tag{6.2}
$$

is coefficient one and respects the paired mass form. This is a comparison of the graph
multiplicity lattice, not an isomorphism between all of $N_v^+$ and a definite module.

### 6.2 The corrected normalization filtration

Let $W_0\subset W_1\subset P_1^+$ be the bottom and normalization layers. Put
$A_{\rm old}=p_v^+(P_0^{+,\oplus2})$ and

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

**Theorem 6.2 (branch-corrected filtration).** Under $({\rm TIC}_v)$,
$({\rm AIH}_{\mathscr F})$, $({\rm TIH}_{\mathscr F})$, and
$({\rm PRI}_{\rm type})$, there are exact sequences

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
the following one-prime support datum. In this patched section, $({\rm TIC}_v)$ and
$({\rm TIH}_{\mathscr F})$ are imposed on every retained finite shadow.

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

These are geometric and Taylor--Wiles hypotheses, not a support assumption. Book 141 supplies
the adequacy and detector input in clause 1; the clean patching package of Book 172 supplies
the Taylor--Wiles selection and the lower carrier in clauses 1--2. Books 138--146, 152, and
170--172 do not prove the boundary-chart and local-dimension assertions in clauses 4--5 for
this nonminimal typed problem. Clause 4 is false if the extraneous component of (7.4) is
retained or if a scalar flag/Kummer coordinate is deleted.

**Lemma 8.2 (nonzero boundary class).** Assume $({\rm TIC}_v)$,
$({\rm TIH}_{\mathscr F})$, and the first three clauses of $({\rm SUP}_v)$. Then
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

**Theorem 8.3 (one-prime component support).** Assume $({\rm TIC}_v)$,
$({\rm TIH}_{\mathscr F})$, and $({\rm SUP}_v)$. Then

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
Neither $({\rm AIH}_{\mathscr F})$ nor $({\rm PRI}_{\rm type})$ enters this support proof;
they are additionally required only when the corrected constant-row residue and normalization
filtration of Chapter 6 is invoked.

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

Under $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$, combine (5.3) with (9.1):

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
datum of Chapter 2, $({\rm TIC}_v)$, and $({\rm TIH}_{\mathscr F})$. Clauses 5--6 below also
assume $({\rm AIH}_{\mathscr F})$ and $({\rm PRI}_{\rm type})$. Then, for every clean
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
   $\mathcal C_{\mathrm{br},v}^+$ retained;
7. the scalar chart is the named closure (7.5) with its flag and Kummer directions, while the
   vexing chart retains the full Gram and primary--companion blocks;
8. if the effective global ray quotient of Section 2.2 exists, scalar twist augmentation gives
   (9.2)--(9.7), changes the Galois determinant by $\boldsymbol\chi_v^2$, and forgets no
   enhancement;
9. if $({\rm SUP}_v)$ holds, the conductor-one primary and companion complexes have full
   topological support on the named enhanced special deformation component at patched and
   finite level; if the effective global ray quotient also exists, (9.8) gives the same support
   on the conductor-two scalar-twisted component;
10. the determinant conventions are (10.1)--(10.7), with no pre-$R=T$ cross-chain
    isomorphism.

The theorem is conditional because neither the finite family $({\rm AIH}_{\mathscr F})$ nor
the type-incidence, type-Ihara, and primitive-residue inputs are unconditional. The
graph--definite comparison, scalar augmentation, and support clauses state their separate exact
hypotheses; none follows merely from $({\rm AIH}_{\mathscr F})$.
In particular, clause 9 does not infer support from the surjection
$R^{\rm sp}\twoheadrightarrow\mathbb T^{\rm sp}$ of Book 170.

### 11.2 Proof

**Proof.** Hypothesis $({\rm TIC}_v)$ and Proposition 3.1 give the actual type coefficient
objects and their coefficient-one node complex. Proposition 4.1 and Lemma 4.2 give strict
finite-free middle cohomology; pull--norm adjunction gives clause 2. Lemma 5.1 applies the
independent type-Ihara input, and the
unit-minor argument of Theorem 5.2 gives clauses 3--4. The Book 139 input enters clauses 5--6
through Theorem 6.2, not through the type-Ihara assertion.

Proposition 6.1, under $({\rm PRI}_{\rm type})$, gives the first assertion of clause 5, and
$({\rm NU}_{\rm type})$ gives its
graph--definite assertion. The corrected filtration of
Theorem 6.2 and the cokernel sequence (6.11) give clause 6 without deleting either finite
module. Chapter 7 proves the two exceptional charts and the determinant-square rule. The
global twist identity, when defined by the chosen ray quotient, proves all parts of clause 8,
including faithful acting images. The depth-and-boundary proof of Theorem 8.3 gives the
conductor-one assertion of clause 9, and (9.8) transports it to the scalar-twisted face under
the same ray hypothesis. Chapter 10 proves the normalization ledger and explicitly stops before
any cross-complex comparison. $\square$

## 12. Scope, dependencies, and audit

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

together with strict coefficient-change maps and, under $({\rm PRI}_{\rm type})$, the
coefficient-one extreme residue and corrected component complex

$$
X_v^+\longrightarrow(X_v^-)^\vee\longrightarrow L_v^+.
\tag{12.2}
$$

The last complex retains $\Phi_v^{\rm type}$ and
$\mathcal C_{\mathrm{br},v}^+$ as distinct finite corrections. When the global scalar ray
quotient exists, (9.1)--(9.7) add strict fixed-prime augmentation. Under $({\rm SUP}_v)$,
Theorem 8.3 adds topological support on the named conductor-one component; with the ray quotient,
(9.8) transports it to the conductor-two scalar-twisted component.

This interface controls only the chosen place $v$. It contains no calculation of intersections
of old images at different places, no mixed-Ihara statement, and no simultaneous-component
support assertion. In particular, Theorem 8.3 cannot be iterated formally to obtain support on
an intersection of local conditions.

### 12.2 Direct dependency ledger

| source | exact use | boundary retained |
|---|---|---|
| Book 6 | effective global ray quotient and unit compatibility | no arbitrary local character is globalized |
| Book 65 | perfect complexes, derived base change, Tor, and determinant conventions | applies only after strict projective models exist |
| Book 67 | represented enhanced special matrix-and-line condition and exceptional tangent directions | the flag and Kummer directions remain at scalar points |
| Book 70 | depth, support, annihilator radicals, and Fitting cautions | topological support is not faithfulness |
| Book 122 | constant-coefficient parahoric incidence model, node chart, nearby cycles, and the ramified-coefficient warning | type-coefficient extension is the separate hypothesis $({\rm TIC}_v)$ |
| Book 138 | quotient primary and augmentation companion lattices, twists, and type labels | no rational projector and no primitive wild type |
| Book 139 | Theorem 14.1 under localized $({\rm AIH})_{v,\mathfrak m}$ and its corrected branch filtration | this book assumes the finite family $({\rm AIH}_{\mathscr F})$; Book 139 neither proves it nor extends it to type coefficients |
| Book 140 | the datum-specific node-uniformization and generic-support interfaces | its constant-coefficient theorem does not prove $({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, $({\rm NU}_{\rm type})$, or $({\rm SUP}_v)$ |
| Book 152 | effective auxiliary torsors, regular group modules, pairings, and compatible finite-level presentations | it does not itself perform the nonminimal patch; module augmentation alone does not imply acting-order augmentation |
| Book 170 | Hecke-valued representation, local factorization, and $R^{\rm sp}\twoheadrightarrow\mathbb T^{\rm sp}$ | no deformation faithfulness or component coverage follows from the surjection |
| Book 141 | adequacy and split-regular detector input for the Taylor--Wiles clause of $({\rm SUP}_v)$ | prime selection and patching do not follow from adequacy alone |
| Book 171 | exact global deformation datum and variance | conductor labels do not replace represented functors |
| Book 172 | retained Taylor--Wiles selection and marked patching mechanism, minimal $R=T$, and the nonzero free lower boundary carrier | no nonminimal equality is imported |

The exact direct-dependency row is therefore

```text
174 | 6, 65, 67, 70, 122, 138, 139, 140, 151, 170, 141, 171, 172
```

Book 139's transitive geometric prerequisites are Books 16, 38--39, 118, 122, and 124. Their
roles remain exactly those recorded there; they are not new unconditional Ihara inputs. No
later nonminimal comparison is used.

### 12.3 Audit of the four delicate interfaces

The earlier gaps have the following exact status.

| interface | status in this book |
|---|---|
| primary/companion type control on curves | not supplied by Books 138--141, 152, and 170--172: $({\rm TIC}_v)$ assumes extension and adjunction on the actual incidence model, while $({\rm TIH}_{\mathscr F})$ is the missing crossed-coefficient residual Ihara theorem; Sections 3--5 derive strict complexes and split amplitude from these exact inputs |
| primitive type residues | not supplied by Books 138--141, 152, and 170--172: Proposition 3.1 proves nodewise coefficients $\pm1$, but global primitivity additionally assumes the exact residual normalization statement $({\rm PRI}_{\rm type})$; the switched definite comparison further requires $({\rm NU}_{\rm type})$ |
| faithful acting-image augmentation | proved in Section 9 by a genuine global twist and coefficient extraction, provided the effective ray quotient of Section 2.2 exists; it is not a formal consequence of Book 152's module augmentation |
| cross determinant | unavailable and not claimed: (10.7) is only equality of principal scalar equations in the faithful Hecke order, not a chain map or determinant-line comparison |

The broader failure audit is as follows.

| test | result |
|---|---|
| constant étale flag cover is used at the bad integral model | pass: Section 3.4 instead states the exact actual-tower hypothesis $({\rm TIC}_v)$ and computes its coefficient inertia |
| exactness is obtained by averaging over a group of nonunit order | pass: descent and the integral flag rows use no averaging |
| perfect cohomology is confused with projective cohomology | pass: Lemma 4.2 uses residual fiber concentration and a minimal complex |
| Book 139 is treated as unconditional or as a type-Ihara theorem | pass: constant terms use $({\rm AIH}_{\mathscr F})$, while nontrivial type terms use the separate $({\rm TIH}_{\mathscr F})$ |
| primary and companion maps are composed across different coefficient lattices | pass: Section 4 distinguishes $p_v^\pm$ and $r_v^\pm$; only same-coefficient Gram composites are formed |
| a rational type projector is used | pass: Lemma 5.1 uses integral flag excision |
| coefficient Tor is erased before projectivity | pass: Theorem 5.2 first proves split injectivity and a projective quotient |
| deformation-ring Tor is erased | pass: Sections 4.3 and 5.2 explicitly exclude that inference |
| the component module and branch Smith module are conflated | pass: (6.7) and (6.11) retain both |
| scalar Frobenius chooses its own line | pass: (7.6)--(7.10) retain the flag, characters, and Kummer directions |
| the vexing block is reduced to one signed factor | pass: Chapters 7 and 10 retain the full matrix and both extension orientations |
| support is inferred from $R\twoheadrightarrow\mathbb T$ | pass: Theorem 8.3 assumes the explicit datum $({\rm SUP}_v)$ and uses boundary nonvanishing plus depth |
| topological support is promoted to faithfulness | pass: (8.6) retains the nilradical |
| module augmentation is promoted formally to acting-order augmentation | pass: (9.6)--(9.7) use the global twist and coefficient extraction |
| a pre-$R=T$ cross-determinant isomorphism is asserted | pass: Section 10.3 expressly forbids it |
| one-place support is promoted to simultaneous support | pass: Section 12.1 states the strict one-place boundary |

The bounded conditional theorem has no hidden internal implication left to supply. Its exact
external hypotheses are: $({\rm AIH}_{\mathscr F})$ for the constant rows and Book 139's
normalization filtration; $({\rm TIC}_v)$ for extension, adjunction, and nearby-cycle
compatibility of the type systems; $({\rm TIH}_{\mathscr F})$ for their residual Ihara theorem;
$({\rm PRI}_{\rm type})$ for global primitive extreme residues; $({\rm NU}_{\rm type})$ only for
the switched graph--definite comparison; the effective global ray quotient only for scalar
augmentation and transport of support to the scalar-twisted face; and $({\rm SUP}_v)$ only for
component support. Books 138--141, 152, and 170--172 do not establish the last six in the
required typed nonminimal generality.

### 12.4 Conclusion

The one-prime object is rigidly typed. Its primary coefficient is the quotient Steinberg
lattice on the actual Shimura tower; its companion is the augmentation lattice with inverse
twist. Their correctly typed pull and norm maps form perfect adjoint complexes. Under the exact
type-incidence and type-Ihara hypotheses, the primary complex is concentrated in its new degree
and its new module is projective over every declared tame and auxiliary coefficient algebra.
The constant-Ihara and primitive-residue hypotheses are additionally required for the
nearby-cycle filtration of Chapter 6.

Under $({\rm PRI}_{\rm type})$, the bad fiber retains all of its information: the extreme
residue has coefficient one, the raw graph discriminant remains the component module, and the
normalized branch map contributes the separate Smith module
$\mathcal C_{\mathrm{br},v}^+$. Scalar points retain their flag and
Kummer directions; vexing points retain the full Gram block. The separately stated support and
global-twist hypotheses give exactly the one-place support and augmentation conclusions they
justify, and no stronger comparison is inferred.
