# Integral Level Change and Jacquet--Langlands Comparison

## Contents

1. [The integral comparison problem](#1-the-integral-comparison-problem)
   - [Rational packets and integral orders](#11-rational-packets-and-integral-orders)
   - [The three lattices](#12-the-three-lattices)
   - [Standing hypotheses](#13-standing-hypotheses)
   - [The result in advance](#14-the-result-in-advance)
2. [Conventions and inherited theorems](#2-conventions-and-inherited-theorems)
   - [Coefficient rings and duals](#21-coefficient-rings-and-duals)
   - [Hecke normalization](#22-hecke-normalization)
   - [The selected local range](#23-the-selected-local-range)
   - [The five prerequisite packages](#24-the-five-prerequisite-packages)
3. [Integral image algebras and packet lattices](#3-integral-image-algebras-and-packet-lattices)
   - [Faithful orders](#31-faithful-orders)
   - [Localization and adjunction](#32-localization-and-adjunction)
   - [Saturation and reduction](#33-saturation-and-reduction)
   - [A common-kernel criterion for equal orders](#34-a-common-kernel-criterion-for-equal-orders)
4. [Switching the two ramified places](#4-switching-the-two-ramified-places)
   - [The indefinite and definite algebras](#41-the-indefinite-and-definite-algebras)
   - [Local packets at the switched places](#42-local-packets-at-the-switched-places)
   - [The rational packet target](#43-the-rational-packet-target)
   - [Exceptional global characters](#44-exceptional-global-characters)
5. [The semistable curve and its node set](#5-the-semistable-curve-and-its-node-set)
   - [Hyperspecial and Iwahori curves](#51-hyperspecial-and-iwahori-curves)
   - [Two branches and their intersections](#52-two-branches-and-their-intersections)
   - [The switched-algebra description of nodes](#53-the-switched-algebra-description-of-nodes)
   - [Hecke equivariance of the node dictionary](#54-hecke-equivariance-of-the-node-dictionary)
6. [Graph lattices and definite forms](#6-graph-lattices-and-definite-forms)
   - [The incidence sequence](#61-the-incidence-sequence)
   - [Constants and the Eisenstein block](#62-constants-and-the-eisenstein-block)
   - [The integral node theorem](#63-the-integral-node-theorem)
   - [Pairings and monodromy](#64-pairings-and-monodromy)
7. [The saturated old map](#7-the-saturated-old-map)
   - [Degeneracy maps and adjoints](#71-degeneracy-maps-and-adjoints)
   - [Ihara injectivity](#72-ihara-injectivity)
   - [The free new quotient](#73-the-free-new-quotient)
   - [Quotient and orthogonal new lattices](#74-quotient-and-orthogonal-new-lattices)
8. [The integral Jacquet--Langlands lattice](#8-the-integral-jacquet--langlands-lattice)
   - [The monodromy multiplicity lattice](#81-the-monodromy-multiplicity-lattice)
   - [Comparison with the definite lattice](#82-comparison-with-the-definite-lattice)
   - [Generic support on the new quotient](#83-generic-support-on-the-new-quotient)
   - [Equality of localized Hecke orders](#84-equality-of-localized-hecke-orders)
9. [Congruence indices and their elimination](#9-congruence-indices-and-their-elimination)
   - [Where an index could enter](#91-where-an-index-could-enter)
   - [Trace duals and the monodromy discriminant](#92-trace-duals-and-the-monodromy-discriminant)
   - [The no-hidden-index theorem](#93-the-no-hidden-index-theorem)
   - [Coefficient extension and descent](#94-coefficient-extension-and-descent)
10. [The one-prime Gram calculation](#10-the-one-prime-gram-calculation)
    - [The exact matrix](#101-the-exact-matrix)
    - [Signed factors](#102-signed-factors)
    - [The Iwahori operator and sign](#103-the-iwahori-operator-and-sign)
    - [The exceptional congruences](#104-the-exceptional-congruences)
11. [Integral level raising](#11-integral-level-raising)
    - [From a Gram kernel to a new class](#111-from-a-gram-kernel-to-a-new-class)
    - [The support theorem](#112-the-support-theorem)
    - [Lifting the residual system](#113-lifting-the-residual-system)
    - [Exact congruence depth](#114-exact-congruence-depth)
12. [Integral level lowering](#12-integral-level-lowering)
    - [The correct residual question](#121-the-correct-residual-question)
    - [Normalization, residues, and components](#122-normalization-residues-and-components)
    - [The lowering theorem](#123-the-lowering-theorem)
    - [Why each hypothesis is necessary](#124-why-each-hypothesis-is-necessary)
13. [Types, twists, and nonmaximal local level](#13-types-twists-and-nonmaximal-local-level)
    - [Selected type lattices](#131-selected-type-lattices)
    - [Twisting and conductor cancellation](#132-twisting-and-conductor-cancellation)
    - [Dihedral local factors](#133-dihedral-local-factors)
    - [Boundaries of the selected theorem](#134-boundaries-of-the-selected-theorem)
14. [Several primes and order of operations](#14-several-primes-and-order-of-operations)
    - [Iterated one-prime change](#141-iterated-one-prime-change)
    - [Tensor-product degeneracy complexes](#142-tensor-product-degeneracy-complexes)
    - [Accumulated congruence ideals](#143-accumulated-congruence-ideals)
    - [Exceptional-prime bookkeeping](#144-exceptional-prime-bookkeeping)
15. [The complete comparison theorem](#15-the-complete-comparison-theorem)
    - [Statement](#151-statement)
    - [Proof](#152-proof)
    - [Dependency and normalization audit](#153-dependency-and-normalization-audit)
    - [Exact scope](#154-exact-scope)
16. [Conclusion](#16-conclusion)
   - [The established package](#161-the-established-package)
   - [The conceptual picture](#162-the-conceptual-picture)

## 1. The integral comparison problem

### 1.1 Rational packets and integral orders

Jacquet--Langlands transfer is a statement about irreducible representations over a field of characteristic zero. Arithmetic level change asks a finer question. It begins with an integral module on which Hecke correspondences act, changes a local level or an inner form, and asks whether the same residual eigensystem survives in the new integral module. The distinction is easy to miss because both questions have the same characteristic-zero eigenvalues away from a finite set of places.

Let $E$ be a finite extension of $\mathbf Q_\ell$, let $\mathcal O$ be its valuation ring, and let $K=\operatorname{Frac}(\mathcal O)=E$. Suppose two finite free $\mathcal O$-modules $L_1$ and $L_2$ carry the same abstract family of commuting Hecke operators. It can happen that

$$
L_1\otimes_{\mathcal O}E
\quad\text{and}\quad
L_2\otimes_{\mathcal O}E
$$

have exactly the same simple eigensystems while the two image algebras are different orders in the same product of fields. The elementary model is

$$
A_n=\{(a,b)\in\mathcal O^2:a\equiv b\pmod{\varpi^n}\}
\subsetneq \mathcal O^2.
$$

Both rings have generic fiber $E^2$. Their difference is invisible after inverting $\varpi$ and is measured by the finite quotient $\mathcal O/(\varpi^n)$. Thus rational transfer alone cannot justify an integral identification of Hecke orders.

The problem becomes sharper at a level-raising prime. The old and new characteristic-zero subspaces are complementary, but their integral lattices need not split. The failure to split is not an error: it is the congruence one wants. What must be excluded is a different phenomenon, namely a nonsaturated old image whose quotient has coefficient torsion. Such torsion can imitate a new residual class without lifting to a characteristic-zero new packet.

This book proves a conditional theorem showing that, in the clean weight-two Shimura-curve setting, the intended congruence survives and coefficient torsion does not imitate it. The decisive geometric input is saturated Ihara theory under Book 139's abelian Ihara condition. The decisive inner-form input is the datum-specific node uniformization identifying the monodromy lattice with the natural integral automorphic lattice on the switched definite quaternion algebra. Once those inputs and Book 125's generic support are placed in one diagram, the two faithful Hecke orders are images of the same abstract algebra with the same kernel. No finite congruence index remains between them.

### 1.2 The three lattices

Three integral objects occur, and none can be replaced by another without proof.

The first is the lower-level curve lattice

$$
M=H^1(X_U,\mathcal O).
$$

At a finite place $v\nmid\ell$, where the quaternion algebra is split and the level is hyperspecial, there are two degeneracy pullbacks to Iwahori level. They give

$$
d=(\pi_0^*,\pi_1^*):M^{\oplus2}\longrightarrow
N=H^1(X_{U_0(v)},\mathcal O).
\tag{1.1}
$$

The second object is the quotient lattice

$$
Q=N/d(M^{\oplus2}).
\tag{1.2}
$$

Only after localization at a clean non-Eisenstein maximal ideal **and** imposition of the abelian Ihara condition (1.5d) is the image in (1.1) known to be saturated from the declared sources. At that point $Q$ is free. It is the correct integral receptacle for the $v$-new quotient. Its orthogonal companion is

$$
N^\perp=\ker(d^*:N\to M^{\oplus2}),
\tag{1.3}
$$

and perfect duality identifies $N^\perp$ with $Q^\vee$ rather than with $Q$ itself.

The third object is the monodromy lattice

$$
X_v=H_1(\Gamma,\mathcal O),
\tag{1.4}
$$

where $\Gamma$ is the geometric dual graph of the Iwahori special fiber at $v$. It is the character lattice of the torus in the special fiber of the Jacobian. Its dual $X_v^\vee=H^1(\Gamma,\mathcal O)$ is the bottom graph piece in cohomology, and monodromy is the edge-length map

$$
q_\Gamma:X_v\longrightarrow X_v^\vee.
\tag{1.5}
$$

The finite cokernel of (1.5) is a component group, not a defect of saturation in (1.2).

There is nevertheless a second finite module in the quotient filtration.  If
$W_0\subset W_1\subset N_{\mathfrak m}$ is the bottom and middle part of the
semistable filtration and $A=d(M_{\mathfrak m}^{\oplus2})$, put

$$
L_0=W_{1,\mathfrak m}/A\subset Q_{\mathfrak m}.
\tag{1.5a}
$$

Projection of the old map to the two normalized branches is the map

$$
B_v=
\begin{pmatrix}1&F_v^*\\ F_v^*&1\end{pmatrix},
\qquad
\mathcal C_{\mathrm{br},v}=\operatorname{coker}(B_v).
\tag{1.5b}
$$

Under residual Ihara, $B_v$ is an equal-rank injection and

$$
0\longrightarrow X_v^\vee\longrightarrow L_0
\longrightarrow\mathcal C_{\mathrm{br},v}\longrightarrow0.
\tag{1.5c}
$$

Thus the component group $\operatorname{coker}(q_\Gamma)$ and the normalized-branch
Smith module $\mathcal C_{\mathrm{br},v}$ are independent corrections.  The first is a
defect of the graph pairing; the second is the failure of $A+W_0$ to be primitive in
$W_1$.  Neither is coefficient torsion in $Q$.

The integral Jacquet--Langlands lattice is (1.4), after the non-Eisenstein localization and the identification of graph edges with a definite quaternionic class set. It is not the entire cohomology group $N$, and it is not an arbitrarily chosen stable lattice in a generic representation. This choice respects the warning already visible locally: transfer compares a distinguished multiplicity line or type lattice, not full fixed spaces whose dimensions can be different on the two inner forms.

### 1.3 Standing hypotheses

We work in the following clean datum throughout, unless a section explicitly varies it.

1. $F$ is totally real.
2. $B/F$ is a division quaternion algebra split at exactly one real place $\tau$.
3. The finite place $v$ is split in $B$, is prime to $\ell$, and is outside the initial level and all ramification in the coefficient data.
4. The level $U=U^vU_v$ has $U_v\simeq\operatorname{GL}_2(\mathcal O_{F_v})$, while $U_0(v)=U^vI_v$ has standard Iwahori level at $v$.
5. The Shimura curves are proper and are taken at neat level, or are descended from neat level through a group of order invertible in $\mathcal O$.
6. The rank-two parahoric local model is the flat incidence model, so the Iwahori curve has regular semistable chart $xy=\varpi_v$.
7. The coefficient prime satisfies $\ell\ge7$, and $\mathcal O$ is a complete DVR of residue characteristic $\ell$ with residue field $k$.
8. The central character is fixed and unit valued. Most displayed formulas use the trivial-central block. For a nontrivial central character we retain the transpose central operator instead of forcing a symmetric formula.
9. The maximal ideal $\mathfrak m$ is non-Eisenstein in the operator-theoretic sense and is stable under the adjoint involution whenever self-duality is invoked.
10. Every finite local packet at a division place lies in the selected special or tame-dihedral range. Ramified dyadic positive-depth and primitive wild packets are not included.
11. The **abelian Ihara condition** of Book 139 holds:
    $$
    \bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}=0.
    \tag{1.5d}
    $$
    Here $\Gamma^v$ is the norm-one $S$-arithmetic group, $\Delta$ is the
    prime-to-$\ell$ component/fine-cover descent group, and
    $H^1_{\mathrm{nc}}$ is the quotient by congruence-continuous characters.
12. The superspecial node classification for the chosen PEL datum supplies the
    Hecke- and residue-Galois-equivariant node bijection (5.9), with the stated
    component routing, stabilizer weights, and coefficient-one normalization.
    This is the **node-uniformization hypothesis**.  It is automatic only when
    that moduli classification has been verified for the datum at hand.
13. The automorphic decomposition and rational semisimplicity theorem of Book
    125 applies to both curve levels, with the full component-routing algebra
    or a proved separating component projector. Together with the generic
    local old/new decomposition, this identifies $Q_E$ with the selected
    $v$-new packet sum. We call this the **generic-support input**. It is a
    direct prerequisite because rational Jacquet--Langlands for the totally
    definite algebra does not by itself prove occurrence in the indefinite
    curve.

The restrictions have distinct purposes. Properness removes cusp cohomology. Neatness removes stabilizer denominators. The condition $v\nmid\ell$ keeps the coefficient sheaf étale at the semistable prime. Non-Eisenstein localization kills only the congruence-continuous part of the tree kernel; hypothesis 11 kills the remaining localized noncongruence-character quotient. The selected-packet hypothesis is exactly the range in which local and global Jacquet--Langlands, conductor comparison, type lattices, and local factors have already been proved. Hypothesis 12 is datum-specific; hypothesis 13 records the additional direct prior-book input now included in the current dependency row.

Let $B^\dagger$ be the quaternion algebra obtained by switching the invariants at $v$ and $\tau$. Precisely,

$$
\operatorname{inv}_w(B^\dagger)=
\begin{cases}
\operatorname{inv}_w(B)+\frac12,&w=v,\tau,\\
\operatorname{inv}_w(B),&w\ne v,\tau,
\end{cases}
\quad\text{in }\mathbf Q/\mathbf Z.
\tag{1.6}
$$

Then $B^\dagger$ is totally definite, ramified at $v$, and agrees with $B$ at every other finite place. Toggling two invariants preserves the global sum-zero condition.

### 1.4 The result in advance

The main theorem has five layers.

First, conditional on (1.5d), the old map (1.1), localized at $\mathfrak m$, is injective with saturated image. Hence

$$
0\longrightarrow M_{\mathfrak m}^{\oplus2}
\xrightarrow{d}N_{\mathfrak m}
\longrightarrow Q_{\mathfrak m}\longrightarrow0
\tag{1.7}
$$

is an exact sequence of finite free $\mathcal O$-modules.

Second, the graph lattice is canonically the localized definite automorphic lattice:

$$
X_{v,\mathfrak m}\xrightarrow{\sim}
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}},
\tag{1.8}
$$

where the superscript means that the norm-character block has been removed by localization, not by dividing by its mass.

Third, the curve-new multiplicity lattice and the definite lattice have the same generic packets by global Jacquet--Langlands and the same integral Hecke kernel by (1.8). Their faithful localized image orders are therefore equal inside their common reduced generic algebra:

$$
\boxed{\mathbb T_{\mathrm{curve},\mathfrak m}^{v\text{-new}}
=\mathbb T_{B^\dagger,\mathfrak m}.}
\tag{1.9}
$$

This is the elimination of the possible Jacquet--Langlands congruence index.

The quotient filtration is not obtained by simply copying the two graph extremes.  It is

$$
0\to X_{v,\mathfrak m}^\vee\to L_0\to
\mathcal C_{\mathrm{br},v}\to0,
\qquad
0\to L_0\to Q_{\mathfrak m}\to X_{v,\mathfrak m}(-1)\to0,
\tag{1.9a}
$$

and quotient monodromy is the composite

$$
X_{v,\mathfrak m}\xrightarrow{q_\Gamma}X_{v,\mathfrak m}^\vee
\longrightarrow L_0.
\tag{1.9b}
$$

Its cokernel is an extension of $\mathcal C_{\mathrm{br},v}$ by the localized
component group.  This correction does not change the generic support or the acting-order
equality, but it must be retained in reduction and level lowering.

Finally, the Gram matrix

$$
d^*d=
\begin{pmatrix}
q_v+1&T_v\\
T_v&q_v+1
\end{pmatrix}
\tag{1.10}
$$

turns a signed congruence

$$
T_v\equiv\varepsilon(q_v+1)\pmod{\mathfrak m},
\qquad \varepsilon\in\{1,-1\},
\tag{1.11}
$$

into a nonzero residual $v$-new class, provided the sign is integrally separated. Conversely, a residual new system with zero monodromy lowers to hyperspecial level when both the component obstruction and the branch Smith obstruction have no residual torsion. These are conditional integral level-raising and level-lowering theorems proved below.

## 2. Conventions and inherited theorems

### 2.1 Coefficient rings and duals

Write

$$
(\mathcal O,\varpi,k,E)
$$

for the coefficient DVR, its uniformizer, residue field, and fraction field. A lattice means a finite free $\mathcal O$-module. If $L$ is a lattice, then

$$
L^\vee=\operatorname{Hom}_{\mathcal O}(L,\mathcal O).
$$

A perfect pairing is one inducing an isomorphism with the appropriate dual. Poincaré pairings carry a Tate twist and Hecke transpose. Since neither affects the elementary-divisor arguments, we display the twist only when monodromy is discussed, but the transpose is never suppressed.

For a Hecke-stable submodule $A\subset L$, its saturation is

$$
A^{\mathrm{sat}}=L\cap(A\otimes_{\mathcal O}E).
\tag{2.1}
$$

The quotient $L/A$ is torsion-free exactly when $A$ is saturated. Over a DVR, finite torsion-free modules are free. These facts will repeatedly turn geometric injectivity modulo $\varpi$ into exact integral sequences.

All characters used in integral type lattices are unit valued. This condition is necessary: an element and its inverse cannot both preserve a nonzero finite lattice if one acts by a nonunit scalar.

### 2.2 Hecke normalization

Let $\Sigma$ contain the coefficient place, $v$, the finite ramification of the quaternion algebras, the level, the central character, and every chosen local type. For $w\notin\Sigma$, put

$$
T_w=\mathbf1_{K_w\operatorname{diag}(\varpi_w,1)K_w},
\qquad
S_w=\mathbf1_{K_w\operatorname{diag}(\varpi_w,\varpi_w)K_w},
\tag{2.2}
$$

with $\operatorname{vol}(K_w)=1$. These are unnormalized right-double-coset operators. Their polynomial is

$$
P_w(X)=1-T_wX+q_wS_wX^2.
\tag{2.3}
$$

On the trivial-central quotient $S_w=1$. We retain $S_w$ until that quotient has actually been taken, because adjoints and twists can otherwise acquire an unnoticed inverse.

At the changing prime $v$, $T_v$ denotes the lower hyperspecial operator. The Iwahori operator is denoted $U_v$, and the involution interchanging the two degeneracy maps is denoted $W_v$. These are different operators. The formula (1.10) concerns $T_v$. In the trivial-central new block our sign convention is

$$
U_v=\varepsilon,
\qquad W_v=-\varepsilon.
\tag{2.5a}
$$

Thus either operator records the special sign once newness is known. Their actions on the old plane are not interchangeable.

Matching regular classes across a division place uses equality of characteristic polynomials. Orbital integrals match with geometric transfer factor $+1$, while the local spectral character identity has sign $-1$. At good split places the representations and Hecke operators are identical, so no sign appears in (2.3).

The Eisenstein ideal in the trivial-central block is generated by

$$
T_w-(q_w+1),\qquad S_w-1
\quad(w\notin\Sigma).
\tag{2.4}
$$

A maximal ideal is non-Eisenstein when at least one of these generators becomes a unit after localization. For a fixed nontrivial central character, (2.4) is replaced by the visibly twisted one-dimensional system. Nothing below relies on pretending that the twisted scalar is still $q_w+1$.

### 2.3 The selected local range

At a finite division place $u$, the selected correspondence has two families. The special family is

$$
\mu\circ\operatorname{Nrd}
\longleftrightarrow
\operatorname{St}\otimes(\mu\circ\det).
\tag{2.5}
$$

Its transfer-facing conductor is

$$
a_{\mathrm{sp}}(\mu)=
\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0.
\end{cases}
\tag{2.6}
$$

The value one in the unramified case records monodromy; it is not the raw depth of the division norm character.

The dihedral family is labelled by a tame admissible pair $(L/F_u,\theta)$, with the induction-normalized rectifier understood. Its conductor is

$$
a(\pi(L,\theta))
=v_u(\mathfrak d_{L/F_u})+f(L/F_u)a_L(\theta).
\tag{2.7}
$$

The same label, central character, conductor, Weil--Deligne datum, and local factors occur on both inner forms. Integral type multiplicity lines are finite free and correspond up to a unit. Under reduction, irreducibility of the full type additionally requires the relevant banal finite-quotient hypotheses. Our lattice comparison uses saturated multiplicity modules and therefore does not infer residual irreducibility merely from the existence of a stable lattice.

When the residue characteristic is two, unramified quadratic depth-zero data remain included. Ramified dyadic positive-depth and primitive wild packets are excluded. No later global argument enlarges this local range.

### 2.4 The five prerequisite packages

We use five established packages, each with its hypotheses retained.

Book 80, *Local Jacquet--Langlands for Special and Dihedral Packets*, gives (2.5)--(2.7), the regular character sign, twist and contragredient compatibility, and saturated integral type lines. We use it only for selected packets and only with unit-valued coefficient data.

Book 85, *Hecke Algebras and Congruences*, says that the faithful image of a commuting Hecke family on a finite free $\mathcal O$-module is finite free over $\mathcal O$. Localization at a maximal ideal preserves faithfulness; perfect adjoint pairings localize; congruence modules are measured by Fitting ideals; and equality of generic branches alone does not imply equality of orders.

Book 104, *Global Jacquet--Langlands*, gives a rational bijection from selected noncharacter packets on the totally definite algebra to their split cuspidal packets, with identical good-place Hecke polynomials, multiplicities, rationality fields, central characters, and exact local components. Norm characters form an exceptional global block and are removed before claiming a cuspidal bijection. The global theorem does not itself identify integral lattices, nor do we use it as an unproved transfer theorem for the indefinite algebra $B$.

Book 125, *Automorphic Decomposition of Shimura-Curve $H^1$*, gives the characteristic-zero packet decomposition and rational semisimplicity for the actual one-split-place quaternionic curve, with component routing and level multiplicities retained. Applied at hyperspecial and Iwahori level, it identifies the generic old quotient packet by packet. It does not prove integral splitting or saturation.

Book 139, *Ihara Theory and Saturated Degeneracy Maps on Shimura Curves*, computes the exact tree kernel.  Its congruence-continuous character part is Eisenstein, but residual injectivity is conditional on (1.5d).  Under that condition it gives saturation of the localized old image, the free quotient (1.2), perfect quotient--orthogonal duality, and the exact Gram matrix.  It also gives the corrected quotient filtration (1.9a), the Smith presentation

$$
\mathcal C_{\mathrm{br},v}
\simeq\operatorname{coker}\bigl(1-(F_v^*)^2:M_{\mathfrak m}\to M_{\mathfrak m}\bigr),
\tag{2.7a}
$$

and the quotient-monodromy cokernel sequence

$$
0\to\Phi_{J_{U_0(v)}}(\bar k_v)[\ell^\infty]_{\mathfrak m}
\otimes_{\mathbf Z_\ell}\mathcal O
\to\operatorname{coker}(X_v\to L_0)
\to\mathcal C_{\mathrm{br},v}\to0.
\tag{2.7b}
$$

These inputs do not, by themselves, prove (1.5d) or the node-uniformization hypothesis. Subject to those two explicit inputs, Book 125 and the generic filtration supply generic support, and Chapters 5--9 establish the integral graph--definite bridge and the resulting equality of image orders. No later statement will turn the conditional residual Ihara theorem into an unconditional one.

## 3. Integral image algebras and packet lattices

### 3.1 Faithful orders

Let

$$
\mathbb T^{\Sigma,\mathrm{abs}}_{\mathcal O}
=\mathcal O[T_w,S_w,S_w^{-1}:w\notin\Sigma]
\tag{3.1}
$$

be the restricted polynomial algebra, so every element involves finitely many places. If it acts on a lattice $L$, define

$$
\mathbb T(L)=
\operatorname{im}\bigl(
\mathbb T^{\Sigma,\mathrm{abs}}_{\mathcal O}
\longrightarrow\operatorname{End}_{\mathcal O}(L)
\bigr).
\tag{3.2}
$$

This image, rather than the abstract source, is the integral Hecke order. It is a finite $\mathcal O$-module because it lies in the finite module $\operatorname{End}_{\mathcal O}(L)$. It is torsion-free because the endomorphism module is torsion-free. Hence it is finite free.

Faithfulness is built into (3.2). If $\mathfrak m$ is a maximal ideal of the image, then $L_{\mathfrak m}\ne0$ and remains faithful over $\mathbb T(L)_{\mathfrak m}$. This avoids the false phenomenon of localizing an abstract algebra at a point outside the support of the chosen automorphic module.

The generic algebra need not be a product of fields unless reducedness is proved. In our applications characteristic-zero automorphic multiplicity one and the normality of the commuting Hecke operators give a reduced generic image. When only the integral comparison is at issue, the proofs below are formulated through kernels and do not require a choice of normalization of that generic algebra.

### 3.2 Localization and adjunction

Suppose $L$ and $L'$ have a perfect pairing

$$
\langle\ ,\ \rangle:L\times L'\to\mathcal O
\tag{3.3}
$$

and the Hecke generators satisfy

$$
\langle tx,y\rangle=\langle x,t^*y\rangle.
\tag{3.4}
$$

If $\mathfrak m^*$ is the image of $\mathfrak m$ under the adjoint involution, then (3.3) restricts to a perfect pairing

$$
L_{\mathfrak m}\times L'_{\mathfrak m^*}\to\mathcal O.
\tag{3.5}
$$

Indeed a finite algebra over a complete DVR is a product of its local factors. The idempotent for $\mathfrak m$ is adjoint to the idempotent for $\mathfrak m^*$, and distinct factors are orthogonal. Perfectness of the whole pairing therefore implies perfectness on each matching block.

When $\mathfrak m=\mathfrak m^*$, we call the block adjoint stable. This does not mean every generator is literally self-adjoint. At a nontrivial central character, $T_w^*=S_w^{-1}T_w$. Adjoint stability means that the maximal ideal is carried to itself under this declared involution.

### 3.3 Saturation and reduction

The following elementary lemma is the algebraic hinge of level change.

**Lemma 3.1 (residual criterion for a primitive image).** Let $f:P\to L$ be a map of finite free modules over a DVR. The following are equivalent:

1. $f\otimes k$ is injective;
2. $f$ is injective and $\operatorname{coker}f$ is torsion-free;
3. in Smith normal form, every nonzero elementary divisor of $f$ is a unit.

**Proof.** Choose bases putting $f$ in Smith form

$$
\operatorname{diag}(\varpi^{a_1},\ldots,\varpi^{a_r},0,\ldots,0).
$$

Reduction is injective precisely when there are $\operatorname{rank}P$ nonzero diagonal entries and each has exponent zero. That is exactly integral injectivity plus torsion-freeness of the cokernel. $\square$

Consequently residual Ihara injectivity proves more than rational injectivity. It proves, at once, that the old quotient is a lattice and that reduction modulo every $\varpi^n$ preserves the old exact sequence.

If $L$ is perfectly paired and $A\subset L$ is saturated, restriction gives a surjection $L^\vee\to A^\vee$. Its kernel is the annihilator $A^\perp$. Hence

$$
A^\perp\xrightarrow{\sim}(L/A)^\vee.
\tag{3.6}
$$

This is the exact relationship between quotient-new and orthogonal-new lattices. An integral direct-sum decomposition would require the restricted pairing on $A$ to be unimodular, which is deliberately false at a congruence prime.

### 3.4 A common-kernel criterion for equal orders

The next lemma will eliminate the apparent inner-form index.

**Lemma 3.2 (common generic support gives a common image order).** Let $A$ be an $\mathcal O$-algebra acting on two finite free modules $L_1,L_2$. Assume

$$
\ker\bigl(A_E\to\operatorname{End}_E(L_{1,E})\bigr)
=
\ker\bigl(A_E\to\operatorname{End}_E(L_{2,E})\bigr).
\tag{3.7}
$$

Then

$$
\ker\bigl(A\to\operatorname{End}_{\mathcal O}(L_1)\bigr)
=
\ker\bigl(A\to\operatorname{End}_{\mathcal O}(L_2)\bigr).
\tag{3.8}
$$

Therefore the two faithful image algebras are canonically isomorphic. If their common generic image is embedded in a product of eigenvalue fields using the same characters, the two image orders are equal as subrings of that product.

**Proof strategy.** A Hecke operator which is zero on one lattice is zero on its generic fiber. Common generic support makes it zero on the other generic fiber, and torsion-freeness of the second lattice makes it zero integrally. Then reverse the roles.

**Proof.** Let $a\in A$ kill $L_1$. Its image $a_E$ kills $L_{1,E}$, so (3.7) says it kills $L_{2,E}$. For $x\in L_2$, the vector $ax$ maps to zero in $L_{2,E}$. Since $L_2\hookrightarrow L_{2,E}$, one has $ax=0$. Thus $a$ kills $L_2$. Symmetry proves (3.8). Taking quotients of $A$ gives the claimed isomorphism. The last assertion follows because both quotients send the class of every $a\in A$ to the same tuple of eigenvalues. $\square$

No discriminant comparison and no assumed Gorenstein property appears in this lemma. What requires arithmetic work is the hypothesis (3.7): one must prove that the two generic modules contain exactly the same packets, including every bad local condition. That is the role of global Jacquet--Langlands in Chapter 4 and the monodromy analysis in Chapter 8.

Two examples delimit the lemma. Let $A=\mathcal O[X]$ act on $L_1=\mathcal O^2$ through $X=\operatorname{diag}(0,\varpi)$ and on $L_2=\mathcal O^2$ through the same endomorphism written in another integral basis. The generic kernels agree, so the image orders agree even though primitive eigenline generators need not correspond. Comparing normalized vectors would introduce irrelevant unit choices.

By contrast, let $X$ act by $0$ on $L_1=\mathcal O$ and by $\varpi$ on $L_2=\mathcal O$. Their residual characters agree, but their generic kernels are $(X)$ and $(X-\varpi)$. The image orders are not identified through $X$. Thus mod-$\varpi$ coincidence is insufficient: the theorem needs equality of characteristic-zero packet support.

## 4. Switching the two ramified places

### 4.1 The indefinite and definite algebras

The inner-form switch is forced by parity. The quaternion algebra $B$ is split at the distinguished real place $\tau$ and at $v$. To obtain a totally definite algebra ramified at $v$ while retaining all other finite localizations, one must also ramify at $\tau$. Formula (1.6) does exactly this.

Existence and uniqueness of $B^\dagger$ follow from the classification of quaternion algebras by local invariants. Every invariant is $0$ or $1/2$, only finitely many are nonzero, and their sum in $\mathbf Q/\mathbf Z$ is zero. Adding $1/2$ at two places preserves the sum. A second algebra with the same invariants is isomorphic to $B^\dagger$.

Choose compatible identifications

$$
B_w\simeq B_w^\dagger
\qquad(w\ne v,\tau).
\tag{4.1}
$$

At $v$ one has

$$
B_v\simeq M_2(F_v),
\qquad B_v^\dagger\text{ division},
\tag{4.2}
$$

while at $\tau$

$$
B_\tau\simeq M_2(\mathbf R),
\qquad B_\tau^\dagger\simeq\mathbf H.
\tag{4.3}
$$

Let $U^\dagger$ agree with $U$ away from $v$ under (4.1), and take

$$
U_v^\dagger=\mathcal O_{B_v^\dagger}^{\times}.
\tag{4.4}
$$

At infinity, parallel weight two on the curve side corresponds to the trivial algebraic representation on $B_\tau^{\dagger,\times}$, with the same central action. More general algebraic weights are handled by the highest-weight shift already built into the global correspondence, but the constant-coefficient Ihara theorem used here is the parallel-weight-two case.

### 4.2 Local packets at the switched places

A $v$-new curve packet has a discrete-series local component at $v$. In the minimal switch used for level raising, it is

$$
\operatorname{St}_v\otimes(\mu_v\circ\det)
\tag{4.5}
$$

with $\mu_v$ unramified and unit valued. Local Jacquet--Langlands sends (4.5) to

$$
\mu_v\circ\operatorname{Nrd}
\tag{4.6}
$$

on $B_v^{\dagger,\times}$. The raw maximal-order depth of (4.6) is zero, but its transfer-facing conductor is one. This is why the squarefree discriminant factor appears on the split side.

At $\tau$, the weight-two discrete series corresponds to the trivial compact type on $\mathbf H^\times$, again with the common central character. Thus switching $v$ and $\tau$ changes two local factors and leaves every other one unchanged.

For a selected dihedral component at $v$, the same argument uses the common admissible-pair label and the conductor (2.7). The definite level must then contain the distinguished division type, not merely the maximal compact. Conductor alone does not recover its fixed-vector multiplicity. Chapter 13 returns to this point.

### 4.3 The rational packet target

Global Jacquet--Langlands for the totally definite algebra $B^\dagger$ gives a precise rational target. A selected noncharacter packet $\Pi^\dagger$ transfers to a cuspidal representation $\pi$ of $\operatorname{GL}_2(\mathbf A_F)$. At $v$ its local factor is the special representation (4.5), at $\tau$ it is weight-two discrete series, and away from $v$ it has the local factors prescribed by $B$ and the chosen level. Its good polynomial is (2.3), with exactly the same coefficients as the definite packet.

It would be circular to declare at this point that the same packet already occurs in the $v$-new curve quotient. The rational global theorem being imported has a totally definite source; it does not by itself identify an integral lattice in the cohomology of the indefinite curve. The occurrence statement will instead be proved geometrically:

$$
\text{definite class-set packet}
\xleftrightarrow[\text{node uniformization}]{}
\text{graph packet}
\xleftrightarrow[\text{nonzero residue}]{}
\text{curve-new packet}.
\tag{4.7}
$$

The first arrow is the node-uniformization hypothesis, whose normalization and consequences are audited in Chapters 5 and 6. The second follows from Book 125's curve decomposition, the corrected semistable filtration, and local Iwahori newness in Section 8.3. Only then is global Jacquet--Langlands used to interpret the common packet as the unique split cuspidal representation $\pi$. This order avoids using a totally definite transfer theorem as an unproved indefinite occurrence theorem and avoids using the desired integral comparison to prove itself.

### 4.4 Exceptional global characters

A norm character on a definite quaternion algebra is a genuine discrete automorphic representation. Its formal local transfer at $v$ is Steinberg and at $\tau$ is discrete series, but at almost every other finite place it remains one dimensional. Such a tensor is not a cuspidal split automorphic representation. Therefore norm characters are not part of the noncharacter packet target of Section 4.3.

Integrally, one must not remove the character line by dividing by its mass unless that mass is a unit. The safe procedure is to localize at a non-Eisenstein maximal ideal. The Hecke action on a norm character satisfies the one-dimensional relations (2.4), with the stated central twist. Hence its localization at $\mathfrak m$ is zero. The quotient by the saturated character submodule and the localized full module then have the same non-Eisenstein factor.

This observation will be used twice. It removes constants from the graph incidence sequence without a denominator, and it aligns the source of global Jacquet--Langlands with the noncharacter part of the definite node module.

## 5. The semistable curve and its node set

### 5.1 Hyperspecial and Iwahori curves

The integral comparison becomes visible in the bad fiber of one curve. Let $R_v$ be the strict henselian valuation ring at $v$. Write

$$
\mathscr X/R_v
$$

for the smooth proper hyperspecial model and

$$
\mathscr C/R_v
$$

for the Iwahori model. Its generic fiber is $X_{U_0(v)}$. The two degeneracy maps extend to finite locally free maps

$$
\pi_0,\pi_1:\mathscr C\longrightarrow\mathscr X
\tag{5.1}
$$

of degree $q_v+1$.

The local model records an isogeny between two rank-two PEL objects. On the active de Rham factor there are two lines related by maps whose composites are multiplication by $\varpi_v$. On the exceptional affine chart the compatibility equation is

$$
xy=\varpi_v.
\tag{5.2}
$$

Because the local-model diagram is smooth and the relative dimension is one, (5.2) is also the completed strict henselian local equation of $\mathscr C$ at every node. It follows directly that $\mathscr C$ is regular: its maximal ideal at the closed point is generated by $x,y$, while its dimension is two. Its geometric special fiber is reduced, with two smooth branches meeting transversely.

Let

$$
Y=\mathscr C_{\bar k_v},
\qquad
\nu:\widetilde Y\to Y
$$

be the special fiber and its normalization. In the clean connected datum the normalization is the disjoint union of two Frobenius twists of the hyperspecial special curve:

$$
\widetilde Y=Y^{(0)}\amalg Y^{(1)}.
\tag{5.3}
$$

The restrictions of the degeneracy maps are

$$
\begin{array}{c|cc}
&\pi_0&\pi_1\\ \hline
Y^{(0)}&1&F_v\\
Y^{(1)}&F_v&1,
\end{array}
\tag{5.4}
$$

after the canonical Frobenius-twist identifications. The degree check is $1+q_v$: geometric Frobenius is bijective on points but has scheme-theoretic degree $q_v$.

The global special fiber may have several connected-component orbits. Everything below is applied orbit by orbit and then induced to a Hecke-stable union. The two-branch language means that every connected piece has the two normalized branches in (5.3); it does not discard component routing.

### 5.2 Two branches and their intersections

Let $\mathcal Z$ be the finite geometric node set at neat level. Orient every edge from the branch $Y^{(0)}$ to $Y^{(1)}$. The dual graph $\Gamma$ has two vertices on each connected piece and one edge for every point of $\mathcal Z$. Multiple edges are retained. If a residue Galois element exchanges the branches, it reverses orientation and therefore acts by a minus sign on the corresponding edge generator. In the tame nonneat case, every graph module and pairing below means the corresponding $\Delta$-invariant object on the fixed neat normal cover; one does not replace it by the naive coarse quotient graph.

For one connected piece, the cellular boundary is

$$
\partial:\mathbf Z[\mathcal Z]\longrightarrow
\mathbf Z\{y_0,y_1\},
\qquad
[z]\longmapsto y_1-y_0.
\tag{5.5}
$$

Thus

$$
H_1(\Gamma,\mathbf Z)
=\left\{\sum_{z\in\mathcal Z}a_z[z]:
\sum_za_z=0\right\}.
\tag{5.6}
$$

Formula (5.6) is the source of the definite lattice. Nodes, rather than components, carry the nonconstant automorphic data. Components contribute only the two vertex directions, which become Eisenstein under the away-from-$v$ Hecke action.

The edge pairing is

$$
q_\Gamma(a,b)=\sum_{z\in\mathcal Z}n_za_zb_z,
\tag{5.7}
$$

where $n_z$ is the thickness of the node on the neat model. In the original regular model $n_z=1$. Retaining $n_z$ makes the construction stable under ramified base change, when an edge is subdivided and the pairing is multiplied by the ramification index. After tame descent, restriction to $\Delta$-invariants produces the orbit and stabilizer factors of Section 6.4; formula (5.7) is not recomputed on a coarse graph with forgotten stabilizers.

### 5.3 The switched-algebra description of nodes

The nodes have a second description which is not visible in the equation $xy=\varpi_v$. They are superspecial incidence objects. Their prime-to-$v$ quasi-isogenies form the adelic class set of $B^\dagger$.

We now formulate the precise datum-specific statement and audit the construction it requires. Let $U^\dagger$ be the level of (4.4), including the same central and prime-to-$v$ data as $U$. Let $W^\dagger$ be the trivial compact weight at $\tau$ in parallel weight two. Put

$$
\mathcal X^\dagger
=(B^\dagger)^\times(F)\backslash
(B^\dagger)^\times(\mathbf A_f)/U^\dagger.
\tag{5.8}
$$

If a fixed central character is imposed, (5.8) is understood with its usual central quotient and transformation law.

**Hypothesis 5.1 (node uniformization for the chosen datum).** The
node-uniformization hypothesis of Section 1.3 is the assertion that there is a
canonical bijection, compatible with residue Galois action, component routing,
stabilizer weights, and all away-from-$v$ Hecke correspondences,

$$
\mathcal Z\xrightarrow{\sim}\mathcal X^\dagger.
\tag{5.9}
$$

At nonneat level the statement is required equivariantly on one fixed neat normal
cover and is descended by exact $\Delta$-invariants when the deck-group order is a
unit in $\mathcal O$. We do not infer regularity of a coarse quotient with fixed
points.

**Verification strategy.** A node is the point where the two possible rank-$q_v$ directions in the active height-two group cease to be distinct. The endomorphism algebra of this superspecial object changes local invariant at $v$ and at the unique split real place. This produces $B^\dagger$. Prime-to-$v$ level structures turn quasi-isogeny classes into the double quotient (5.8). The following argument records the normalization and inverse constructions that a proof of the hypothesis must supply; the four catalogued prerequisites do not themselves contain this superspecial classification.

**Verification.** Choose a geometric node $z$ and a representative PEL object $A_z$ with its polarization, endomorphisms, and prime-to-$v$ level. Let

$$
I_z=\operatorname{End}^0(A_z,\text{PEL data})^\times
$$

be its quasi-isogeny group. Away from $v$ the superspecial condition changes nothing, so the local endomorphism algebra is identified with $B_w$ and hence with $B_w^\dagger$. At $v$, the connected and étale directions have merged into the unique isoclinic height-two object. Its rational endomorphism algebra is the quaternion division algebra over $F_v$, so the local invariant is changed by $1/2$.

At the distinguished real place, the polarization involution makes the quasi-isogeny group compact modulo center. Thus its quaternion algebra is ramified at $\tau$. At every other real place $B$ was already ramified and remains so. The local invariants of $\operatorname{End}^0(A_z)$ are therefore exactly those of $B^\dagger$. Classification of quaternion algebras gives

$$
\operatorname{End}^0(A_z)\simeq B^\dagger.
\tag{5.10}
$$

Fix one base node $z_0$ and one identification in (5.10). A prime-to-$v$ quasi-isogeny from $A_{z_0}$ to another node transports the level structure and determines an element of $(B^\dagger)^\times(\mathbf A_f)$. Changing the quasi-isogeny on the left by a rational self-quasi-isogeny and on the right by the chosen level changes the element by $(B^\dagger)^\times(F)$ and $U^\dagger$. Hence a node gives a class in (5.8).

Conversely, an adelic class modifies the prime-to-$v$ Tate lattices of $A_{z_0}$ and the maximal $v$-adic lattice in its division isocrystal. The usual lattice-isogeny construction produces a PEL object in the same superspecial isogeny class with the transported level. Its two deformation directions give a node of the incidence model. Left and right changes produce an isomorphic object, so the construction descends to (5.8).

The two constructions are inverse because a prime-to-$v$ quasi-isogeny is determined by its action on all rational Tate modules together with the polarization multiplier, and the chosen $v$-adic maximal lattice fixes the remaining isogeny ambiguity. This proves bijectivity.

An away-from-$v$ double coset modifies exactly one prime-to-$v$ lattice. The same modification describes both the PEL correspondence on nodes and right multiplication on (5.8), proving Hecke equivariance. Geometric Frobenius acts on the isocrystal and level structure on both sides, proving Galois equivariance. $\square$

The verification uses the moduli interpretation of the already constructed semistable model and the stated superspecial quasi-isogeny classification. It does not assume the integral comparison that (5.9) is meant to establish. Conversely, without that classification the displayed construction is a proof sketch, not a consequence of rational Jacquet--Langlands; this is why (5.9) is an explicit hypothesis of the complete theorem.

### 5.4 Hecke equivariance of the node dictionary

It is worth checking the right-versus-left convention explicitly. Let

$$
U_w^\dagger g_wU_w^\dagger
=\coprod_i g_{w,i}U_w^\dagger
$$

at a good place $w$. On functions on the class set, the unnormalized operator is

$$
(T_wf)(x)=\sum_i f(xg_{w,i}).
\tag{5.11}
$$

On the node set, the correspondence sends a level structure to the finite collection obtained by quotienting by the $q_w+1$ admissible rank-one subgroups. Under the quasi-isogeny coordinate used in Hypothesis 5.1 these are precisely the right translates $xg_{w,i}$. Hence (5.11) is the graph-edge action.

The transpose correspondence uses $g_w^{-1}$. With the hyperspecial volume-one normalization,

$$
T_w^*=S_w^{-1}T_w.
\tag{5.12}
$$

The node pairing and the definite mass pairing have the same adjoint because both count the same finite correspondence with the same stabilizer weight. This observation will prevent a hidden central inverse in the Hecke-order comparison.

## 6. Graph lattices and definite forms

### 6.1 The incidence sequence

Put

$$
C_1=\mathcal O[\mathcal Z],
\qquad
C_0=\mathcal O[V(\Gamma)].
$$

For the oriented graph there is an exact sequence

$$
0\longrightarrow X_v
\longrightarrow C_1
\xrightarrow{\partial}C_0
\xrightarrow{\epsilon}H_0(\Gamma,\mathcal O)
\longrightarrow0.
\tag{6.1}
$$

Exactness follows from elementary graph theory. A one-chain lies in the kernel of $\partial$ exactly when its coefficient sum at each vertex is balanced, which is the definition of a cycle. The cokernel of $\partial$ identifies vertices in the same connected component and is therefore $H_0$.

Every away-from-$v$ Hecke correspondence acts on edges and vertices and commutes with $\partial$. Scheme-theoretic multiplicities are essential: replacing a degree-$q_w+1$ correspondence by its set of reduced images would break equivariance of (6.1).

The node dictionary identifies

$$
C_1\simeq S(B^\dagger,U^\dagger,\mathcal O),
\tag{6.2}
$$

the full finite module of definite forms of the stated weight and center. At neat level this is simply the function module on (5.8). With finite stabilizers it is the corresponding invariant weight module; the prime-to-$\ell$ hypothesis makes it finite free and preserves the mass pairing.

### 6.2 Constants and the Eisenstein block

On a connected two-vertex graph, $C_0$ and $H_0$ are generated by component functions. On a Hecke-stable union, let $P_w$ be the component-routing operator. A good Hecke correspondence satisfies

$$
T_w=(q_w+1)P_w,
\qquad S_w=P_w^2
\tag{6.2a}
$$

on these terms. Consequently the homology of the tail

$$
C_0\xrightarrow\epsilon H_0
$$

is annihilated by the routed Eisenstein ideal. In the trivial-routing block this is (2.4); on a component character $\eta$ it is
$T_w-(q_w+1)\eta_w(\varpi_w)$ and
$S_w-\eta_w(\varpi_w)^2$. A finite component permutation cannot simply be discarded: it must first be included through $P_w$ and then specialized to the chosen component block.

Localize (6.1) at the non-Eisenstein maximal ideal $\mathfrak m$. The vertex and connected-component terms vanish. Exactness gives

$$
\boxed{X_{v,\mathfrak m}\xrightarrow{\sim}C_{1,\mathfrak m}.}
\tag{6.3}
$$

No division by the number of nodes occurs. This matters when $\ell$ divides that number. The tempting projection

$$
f\longmapsto f-\frac{1}{|\mathcal Z|}\sum_zf(z)
$$

may be nonintegral, whereas localization of the exact incidence sequence is always legitimate.

The norm-character submodule of the definite space lies in the same one-dimensional Hecke block as constants. It therefore vanishes after the same localization. Combining (6.2) and (6.3) gives the desired noncharacter interpretation of $X_v$.

### 6.3 The integral node theorem

**Theorem 6.1 (integral node lattice).** Under the clean datum there is a canonical, Hecke- and Galois-equivariant isomorphism

$$
\boxed{
X_{v,\mathfrak m}
\simeq
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}}.}
\tag{6.4}
$$

It is compatible with finite flat coefficient extension, adjoint transpose, and reduction modulo every power of $\varpi$.

**Proof.** Hypothesis 5.1 identifies the edge module with the full definite function module and intertwines Hecke and Galois actions. Localization of the incidence sequence gives (6.3). Non-Eisenstein localization removes the norm-character block, so the right side of (6.3) is precisely the right side of (6.4).

All modules in (6.1) are finite free. Finite flat coefficient extension preserves exactness and the node bijection. The transpose compatibility is (5.12). Since (6.4) is an integral isomorphism, reduction modulo $\varpi^n$ preserves it for every $n$. $\square$

The theorem is stronger than equality of Brandt eigenvalues. It identifies the entire localized lattice, including generalized residual eigenspaces and nilpotent special-fiber action.

### 6.4 Pairings and monodromy

On the edge module define the weighted pairing

$$
\langle f,g\rangle_{\mathrm{edge}}
=\sum_{z\in\mathcal Z}\frac{n_z}{e_z}f(z)g(z),
\tag{6.5}
$$

where $e_z$ is the effective projective stabilizer order. At neat level $e_z=1$. Under tame descent this notation means the pairing obtained on the fixed neat cover and then restricted to exact $\Delta$-invariants; in an orbit basis it has the displayed unit stabilizer weights. The node-uniformization hypothesis includes equality with the definite mass pairing. Merely knowing the underlying sets are in bijection would not determine this normalization.

Restricting (6.5) to cycles gives the monodromy pairing (5.7). Hence the diagram

$$
\begin{array}{ccc}
X_{v,\mathfrak m}&\xrightarrow{q_\Gamma}&X_{v,\mathfrak m}^\vee\\
\downarrow\wr&&\downarrow\wr\\
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}}
&\xrightarrow{q_{\mathrm{mass}}}&
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc},\vee}
\end{array}
\tag{6.6}
$$

commutes, where the lower arrow means the form induced after the incidence localization, not an independently rescaled pairing.

The ambient graph-pairing cokernel is

$$
\operatorname{coker}(q_\Gamma)
\simeq
\Phi_{J_{U_0(v)}}(\bar k_v)[\ell^\infty]_{\mathfrak m}
\otimes_{\mathbf Z_\ell}\mathcal O.
\tag{6.7}
$$

Thus a nonzero component group is compatible with the lattice isomorphism (6.4). It measures failure of the restricted graph or mass pairing to be unimodular. It does not measure a discrepancy between the curve and definite Hecke orders. It is also not the whole cokernel of monodromy on $Q$: that cokernel has the additional quotient $\mathcal C_{\mathrm{br},v}$ in (2.7b).

There is a useful explicit audit. Suppose one connected special fiber has two vertices joined by $m$ unit edges. With cycle basis

$$
c_i=e_i-e_m\qquad(1\le i<m),
$$

the monodromy matrix is

$$
Q_m=
\begin{pmatrix}
2&1&\cdots&1\\
1&2&\cdots&1\\
\vdots&\vdots&\ddots&\vdots\\
1&1&\cdots&2
\end{pmatrix}.
\tag{6.8}
$$

Elementary row and column operations give

$$
\operatorname{SNF}(Q_m)=\operatorname{diag}(1,\ldots,1,m).
\tag{6.9}
$$

Thus $X_v$ has rank $m-1$ and the component group is cyclic of order $m$. The edge module has rank $m$; its missing constant direction is Eisenstein. Localization identifies its non-Eisenstein part with the cycle lattice without forming $1/m$. If $\ell\mid m$, the pairing is not perfect, but the lattice and Hecke-order comparison remain exact.

With edge thicknesses $n_1,\ldots,n_m$, the same basis gives

$$
Q_{ij}=
\begin{cases}
n_i+n_m,&i=j,\\
n_m,&i\ne j,
\end{cases}
\qquad
\det Q=\sum_{j=1}^m\prod_{i\ne j}n_i.
\tag{6.10}
$$

The determinant gives the order but not the invariant factors. For three edges all of thickness two, the Smith form is $\operatorname{diag}(2,6)$, not $\operatorname{diag}(1,12)$. This is why a higher-multiplicity congruence calculation must retain the full lattice map.

## 7. The saturated old map

### 7.1 Degeneracy maps and adjoints

Return to

$$
d=(\pi_0^*,\pi_1^*):M^{\oplus2}\to N.
$$

Poincaré duality identifies the adjoint with the two norm maps:

$$
d^*=\binom{\pi_{0,*}}{\pi_{1,*}}:N\to M^{\oplus2}.
\tag{7.1}
$$

The diagonal composites have degree $q_v+1$. The off-diagonal composites are the two orientations of the lower spherical correspondence. In the trivial-central block this gives

$$
d^*d=
\begin{pmatrix}
q_v+1&T_v\\
T_v&q_v+1
\end{pmatrix}.
\tag{7.2}
$$

Before central specialization, the lower-left entry is the transpose of the upper-right entry. All arguments about saturation use $d$ itself and are independent of whether (7.2) is symmetric.

### 7.2 Ihara injectivity

The local lattice tree at $v$ has two adjacent hyperspecial vertices and their Iwahori edge. The arithmetic group with the $v$-level removed has this edge as a fundamental domain. The Mayer--Vietoris sequence identifies the kernel of the two restriction maps with the image of the first cohomology of that arithmetic group.

With constant coefficients, this first cohomology consists of additive characters. Book 139 splits it into congruence-continuous characters and the quotient $H^1_{\mathrm{nc}}$. For a good Hecke operator, restriction--component transport--corestriction gives

$$
T_w\chi=(q_w+1)\chi,
\qquad S_w\chi=\chi
\tag{7.3}
$$

in the trivial-routing, trivial-central block **on the congruence-continuous submodule**. On a routed block the right sides contain $P_w$ as in (6.2a). No listed prerequisite proves (7.3) on every abstract finite character of $\Gamma^v$.

After non-Eisenstein localization, Book 139 identifies the remaining kernel exactly as

$$
\ker(d\otimes k)_{\mathfrak m}
\simeq
\bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}.
\tag{7.3a}
$$

The abelian Ihara condition (1.5d), not non-Eisensteinness alone, makes (7.3a) vanish.

Comparison between singular and étale cohomology identifies the tree restriction maps with the geometric pullbacks. Hence, under (1.5d),

$$
(d\otimes k)_{\mathfrak m}:
(M/\varpi M)_{\mathfrak m}^{\oplus2}
\longrightarrow
(N/\varpi N)_{\mathfrak m}
\tag{7.4}
$$

is injective.

The hypotheses are visible in this proof. Constant coefficients turn cocycles into characters. Neatness or prime-to-$\ell$ descent removes stabilizer cohomology. Non-Eisenstein localization kills the congruence-continuous character submodule, and (1.5d) kills the remaining noncongruence quotient. The theorem would not follow merely from the nonvanishing of a determinant in characteristic zero or from strong approximation.

### 7.3 The free new quotient

The cohomology of a smooth proper curve in characteristic zero is finite free over $\mathcal O$. Applying Lemma 3.1 to (7.4) yields the exact sequence

$$
0\longrightarrow M_{\mathfrak m}^{\oplus2}
\xrightarrow{d}N_{\mathfrak m}
\longrightarrow Q_{\mathfrak m}\longrightarrow0,
\tag{7.5}
$$

with $Q_{\mathfrak m}$ finite free. Moreover, for every $n\ge1$,

$$
0\to(M/\varpi^nM)_{\mathfrak m}^{\oplus2}
\to(N/\varpi^nN)_{\mathfrak m}
\to Q_{\mathfrak m}/\varpi^nQ_{\mathfrak m}\to0
\tag{7.6}
$$

is exact. This excludes every hidden coefficient-torsion class in the new quotient.

The quotient in (7.5) need not split inside $N_{\mathfrak m}$. At a level-raising congruence it should not split orthogonally. Saturation says only that the quotient is a genuine lattice.

### 7.4 Quotient and orthogonal new lattices

Let

$$
N_{\mathfrak m}^{\perp}=\ker d^*_{\mathfrak m}.
\tag{7.7}
$$

Perfect Poincaré duality and saturation give a canonical isomorphism

$$
N_{\mathfrak m}^{\perp}\xrightarrow{\sim}Q_{\mathfrak m}^\vee.
\tag{7.8}
$$

They also make $d^*:N_{\mathfrak m}\to(M_{\mathfrak m}^{\oplus2})^\vee$ surjective. Indeed restriction of functionals from a free module to a primitive submodule is surjective, and Poincaré duality identifies those functionals with elements of $N$.

This surjectivity is crucial for level raising. It permits a Gram-divisible old vector to be corrected by an integral vector of $N$, producing an actual element of $N^\perp$. Without saturation, the needed correction could exist only after dividing by $\varpi$.

## 8. The integral Jacquet--Langlands lattice

### 8.1 The monodromy multiplicity lattice

The nearby-cycle filtration on $N$ has extreme pieces

$$
\operatorname{gr}_0N=H^1(\Gamma,\mathcal O)=X_v^\vee,
\qquad
\operatorname{gr}_2N=X_v(-1),
\tag{8.1}
$$

and middle piece the cohomology of the two normalized branches. The old image comes from the good-reduction hyperspecial Jacobian, lies in $W_1$, and meets $W_0$ trivially. This does **not** imply that its sum with $W_0$ is saturated. Book 139 computes the correction. With $A=d(M_{\mathfrak m}^{\oplus2})$ and $L_0=W_{1,\mathfrak m}/A$, one has

$$
0\longrightarrow X_{v,\mathfrak m}^\vee
\longrightarrow L_0
\longrightarrow\mathcal C_{\mathrm{br},v}
\longrightarrow0,
\qquad
0\longrightarrow L_0
\longrightarrow Q_{\mathfrak m}
\longrightarrow X_{v,\mathfrak m}(-1)
\longrightarrow0.
\tag{8.2}
$$

The module $L_0$ is saturated and free, while the inclusion
$X_v^\vee\subset L_0$ is primitive exactly when
$\mathcal C_{\mathrm{br},v}=0$. Monodromy on $Q$, after cancelling the common
Tate twist, is

$$
X_{v,\mathfrak m}
\xrightarrow{q_\Gamma}
X_{v,\mathfrak m}^\vee
\longrightarrow L_0.
\tag{8.3}
$$

Consequently

$$
0\longrightarrow
\Phi_{J_{U_0(v)}}(\bar k_v)[\ell^\infty]_{\mathfrak m}
\otimes_{\mathbf Z_\ell}\mathcal O
\longrightarrow\operatorname{coker}(N_Q:X_v\to L_0)
\longrightarrow\mathcal C_{\mathrm{br},v}
\longrightarrow0.
\tag{8.3a}
$$

We call $X_{v,\mathfrak m}$ the **curve-new automorphic multiplicity lattice**. The terminology separates the automorphic multiplicity from the two extreme cohomological degrees in which it appears. A characteristic-zero special packet contributes one automorphic line but a two-step monodromy block to curve cohomology.

### 8.2 Comparison with the definite lattice

Combining the top quotient in (8.2) with Theorem 6.1 gives

$$
X_{v,\mathfrak m}
\simeq
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}}.
\tag{8.4}
$$

This is the integral Jacquet--Langlands comparison of lattices. It has three exact meanings.

First, every good Hecke operator acts by the same integral matrix on the two sides after the node basis is chosen. Second, the mass pairing is the ambient graph pairing with the same stabilizer and thickness factors. Third, reduction retains the full localized generalized eigenspace, not merely its semisimplification. The comparison is with $X_v$, not with the larger saturated bottom lattice $L_0$.

It does not assert

$$
Q_{\mathfrak m}\simeq
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}.
$$

The ranks are generally different because $Q$ is a cohomological realization with two monodromy extremes. The correct comparison is (8.4).

### 8.3 Generic support on the new quotient

We must still connect the curve multiplicity lattice to the representation-theoretic $v$-new quotient. After tensoring with $E$, automorphic decomposition and local newvector theory give

$$
Q_{\mathfrak m,E}
=\bigoplus_{\Pi\in\mathcal P_B^{v\text{-new}}(\mathfrak m)}
V_\Pi,
\tag{8.5}
$$

where $V_\Pi$ denotes the cohomological realization of the packet, with its one-dimensional automorphic multiplicity and two-dimensional monodromy block. Old packets have been removed by (7.5). This decomposition and its semisimplicity are the Book 125 input of Section 1.3, not a consequence of rational definite Jacquet--Langlands alone.

The finite module $\mathcal C_{\mathrm{br},v}$ disappears after tensoring with $E$, so (8.2) has generic graded pieces $X_v^\vee$ and $X_v(-1)$. Book 125 makes the retained characteristic-zero Hecke action semisimple, hence the filtration splits as a Hecke module. The generic graph pairing is perfect and Hecke-adjoint; on the adjoint-stable block the actions on $X_v$ and $X_v^\vee$ therefore have the same kernel. It follows directly that

$$
\ker\bigl(\mathbb T^{\Sigma,\mathrm{abs}}_E
\to\operatorname{End}_E(Q_{\mathfrak m,E})\bigr)
=
\ker\bigl(\mathbb T^{\Sigma,\mathrm{abs}}_E
\to\operatorname{End}_E(X_{v,\mathfrak m,E})\bigr).
\tag{8.6}
$$

Equivalently, one may read (8.6) packet by packet. The left kernel is the intersection of the eigencharacter kernels of the $v$-new packets, while the corrected generic filtration shows that the same characters occur on its graph subquotients. Global Jacquet--Langlands for $B^\dagger$ then identifies their common good-place character with the unique split cuspidal packet described in Section 4.3; it does not prove occurrence in the curve by itself.

Here is a local proof that no clean Iwahori packet is lost. Put $H=\operatorname{GL}_2(F_v)$, $K=\operatorname{GL}_2(\mathcal O_{F_v})$, and let $I\subset K$ be the standard Iwahori. An irreducible generic representation in the unramified Iwahori block has one of the two forms relevant here.

For an irreducible unramified principal series, the $I$-fixed space has dimension two and the $K$-fixed space has dimension one. The two degeneracy translates of the spherical line span the $I$-fixed space. Indeed they are fixed by the two adjacent hyperspecial vertex stabilizers. If the two lines coincided, their common vector would be fixed by the group generated by those stabilizers, hence by $H$; that would force a one-dimensional constituent, contrary to irreducibility of the principal series. Since the target has dimension two, the two lines form a basis. Such a packet is entirely old and disappears from $Q_E$.

For an unramified Steinberg twist, the $I$-fixed space is a line and the $K$-fixed space is zero. It is entirely new. Its centered special parameter has nonzero monodromy, so its top residue in $X_{v,E}(-1)$ is nonzero. Conversely a nonzero graph residue cannot arise from a good-reduction spherical packet, since good reduction has zero monodromy. At the reducible boundary of principal induction, the special quotient is exactly this Steinberg line and the character constituent is Eisenstein. This proves the equality of support in (8.6) throughout the clean special block.

### 8.4 Equality of localized Hecke orders

Define

$$
\mathbb T_{\mathrm{curve},\mathfrak m}^{v\text{-new}}
=\operatorname{im}\bigl(
\mathbb T^{\Sigma,\mathrm{abs}}_{\mathcal O}
\to\operatorname{End}_{\mathcal O}(Q_{\mathfrak m})
\bigr)
\tag{8.7}
$$

and

$$
\mathbb T_{B^\dagger,\mathfrak m}
=\operatorname{im}\bigl(
\mathbb T^{\Sigma,\mathrm{abs}}_{\mathcal O}
\to\operatorname{End}_{\mathcal O}
(S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}})
\bigr).
\tag{8.8}
$$

**Theorem 8.1 (integral Hecke-order comparison).** The common eigenvalue embedding identifies

$$
\boxed{
\mathbb T_{\mathrm{curve},\mathfrak m}^{v\text{-new}}
=\mathbb T_{B^\dagger,\mathfrak m}.}
\tag{8.9}
$$

Both are finite free over $\mathcal O$, and the equality respects adjoints, augmentations, finite flat coefficient extension, and every operator retained in the common abstract algebra.

This is an equality of the faithful images of the explicitly common
away-from-$\Sigma$ algebra (3.1). It does not identify $U_v$, $W_v$, a division
uniformizer operator, or a type projector unless that operator has separately
been adjoined on both sides and the node dictionary has been proved compatible
with it. A maximal ideal of an abstract larger Hecke algebra outside the support
of either module is not part of the statement.

**Proof.** The abelian Ihara condition makes $Q_{\mathfrak m}$ finite free. Equation (8.6), using Book 125's generic semisimplicity and the corrected filtration, supplies the common-generic-kernel hypothesis of Lemma 3.2 for $Q_{\mathfrak m}$ and $X_{v,\mathfrak m}$. Both are finite free over $\mathcal O$. Lemma 3.2 therefore identifies their integral image algebras. The node-uniformization hypothesis and Theorem 6.1 identify the latter image with (8.8), proving (8.9).

Finiteness and freeness follow from faithful action on finite free modules. The node correspondence gives the same transpose on both sides. An augmentation is evaluation of the common image order at one packet and is therefore preserved. Finite flat base change preserves the lattice isomorphism and the kernel equality. $\square$

The proof does not choose bases of eigenvectors and does not normalize one primitive vector against another. It compares faithful images of a common abstract algebra. This is why no unit ambiguity in a local type line becomes a global congruence index.

## 9. Congruence indices and their elimination

### 9.1 Where an index could enter

Let $A_E$ be the common reduced generic Hecke algebra. Rational Jacquet--Langlands embeds both integral orders into $A_E$. Without Theorem 8.1 one would know only that

$$
\mathbb T_{\mathrm{curve}}\otimes E
=A_E
=\mathbb T_{B^\dagger}\otimes E.
$$

Their intersection and sum could have finite quotients. A proposed comparison map scaled by $\varpi^n$ would still be an isomorphism over $E$ but would change the integral cokernel. Pairing discriminants alone would not fix the scale unless the relevant dual lattices were also compared.

The graph construction fixes the scale geometrically. An edge is a node with coefficient one. Under node uniformization it is the characteristic function of one definite class, again with coefficient one. Stabilizer weights occur in both pairings, not in the module identification. Thus (8.4) is primitive before any Hecke algebra is formed.

### 9.2 Trace duals and the monodromy discriminant

For a finite free order $T$ with reduced separable generic fiber, define its trace dual

$$
T^\sharp=\{x\in T_E:\operatorname{Tr}_{T_E/E}(xT)\subseteq\mathcal O\}.
\tag{9.1}
$$

The quotient $T^\sharp/T$ measures failure of the raw trace pairing to be perfect. It should not be confused with a failure of $T$ to be Gorenstein: Gorensteinness asks whether $T^\sharp$ is a principal fractional $T$-ideal, not whether it equals $T$ under this particular trace functional.

On the automorphic lattice, the analogous coefficient-pairing defect is the cokernel of the restricted mass pairing. Diagram (6.6) identifies it with the monodromy discriminant (6.7):

$$
\operatorname{coker}(q_{\mathrm{mass}})
\simeq\operatorname{coker}(q_\Gamma)
\simeq\Phi[\ell^\infty]_{\mathfrak m}\otimes\mathcal O.
\tag{9.2}
$$

This finite module can be nonzero. It appears on both sides of the graph--definite pairing comparison and hence does not create an index between the two Hecke orders. It is not automatically $T^\sharp/T$: identifying an order trace dual with a module pairing requires rank-one Hecke freeness or a separately normalized duality generator. The different finite module $\mathcal C_{\mathrm{br},v}$ belongs to the embedding $X_v^\vee\subset L_0$ in the curve quotient. It is not a defect of the graph--definite lattice map and is not identified with (9.2).

### 9.3 The no-hidden-index theorem

**Theorem 9.1 (elimination of congruence indices).** Place the two orders of Theorem 8.1 inside their common generic eigenvalue algebra. Then

$$
[\mathbb T_{\mathrm{curve},\mathfrak m}^{v\text{-new}}:
\mathbb T_{\mathrm{curve},\mathfrak m}^{v\text{-new}}
\cap\mathbb T_{B^\dagger,\mathfrak m}]
=1,
$$

$$
[\mathbb T_{B^\dagger,\mathfrak m}:
\mathbb T_{\mathrm{curve},\mathfrak m}^{v\text{-new}}
\cap\mathbb T_{B^\dagger,\mathfrak m}]
=1.
\tag{9.3}
$$

For every augmentation $\lambda$ of the common order, the cotangent module, augmented congruence ideal, normalization conductor, and branch-difference ideals computed from either realization agree. The semistable realization also carries two explicit finite modules: the graph discriminant (9.2) and the normalized-branch correction $\mathcal C_{\mathrm{br},v}$ in (8.2). Neither is an index between the two acting orders.

**Proof.** Equality (8.9) immediately gives (9.3). Every listed invariant is functorial in the augmented order itself, so it is identical for the two realizations. The ambient graph-pairing defect is (9.2), the separate quotient-filtration defect is $\mathcal C_{\mathrm{br},v}$, and saturation of (7.5) proves that no coefficient torsion in the old quotient contributes a third factor. $\square$

This theorem is not the assertion that every old--new congruence ideal is the unit ideal. Level raising produces nontrivial congruence ideals inside the common order. The assertion is that changing the realization from curve monodromy to definite forms neither multiplies nor divides those ideals by an unseen scalar.

### 9.4 Coefficient extension and descent

Let $\mathcal O'/\mathcal O$ be a finite extension of DVRs. Because every lattice in the comparison is finite free,

$$
X_{v,\mathfrak m}\otimes\mathcal O'
\simeq
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}
\otimes\mathcal O'
\tag{9.4}
$$

and the Hecke-order equality base changes. The Smith presentation (2.7a), the branch exact sequence (8.2), and the monodromy-cokernel extension (8.3a) base change as well. Fitting ideals extend. If the ramification index is $e$, uniformizer-normalized lengths multiply by $e$; the ideals themselves are the invariant statement.

Conversely, a faithfully flat extension detects equality. If two $\mathcal O$-submodules of the same finite $E$-space become equal after tensoring with $\mathcal O'$, their quotient tensors to zero and is therefore zero. Thus the comparison may be proved after an unramified extension splitting the residual eigenvalues or a ramified extension containing characteristic-zero coefficient fields and then descended.

Ramified extension at the geometric place $v$ is different. It multiplies edge thicknesses and enlarges the component group, while leaving the coefficient order unchanged. One must not confuse a coefficient-field ramification index with the geometric ramification index of the base trait.

## 10. The one-prime Gram calculation

### 10.1 The exact matrix

The old map contains the numerical level-change condition. The calculation must be made at the operator level before an eigencharacter is substituted.

In the trivial-central normalization, pull--norm adjunction gives

$$
G_v=d^*d=
\begin{pmatrix}
q_v+1&T_v\\
T_v&q_v+1
\end{pmatrix}.
\tag{10.1}
$$

The diagonal entries are the degrees of $\pi_0$ and $\pi_1$. The upper-right entry is the correspondence obtained by pulling through $\pi_1$ and tracing through $\pi_0$; the fiber product parametrizes the $q_v+1$ neighboring lattices, so it is the unnormalized spherical $T_v$. The other off-diagonal entry is its transpose. This proves (10.1) and also explains why averaging by $q_v+1$ would be the wrong convention.

If the central operator is retained, the invariant formula is

$$
G_v=
\begin{pmatrix}
q_v+1&T_v\\
S_v^{-1}T_v&q_v+1
\end{pmatrix},
\tag{10.2}
$$

after the standard identification of the two lower copies. Its determinant is

$$
D_v=(q_v+1)^2-S_v^{-1}T_v^2.
\tag{10.3}
$$

All signed formulas below specialize $S_v$ according to the fixed central character. The symmetric formulas use $S_v=1$.

### 10.2 Signed factors

Let $\lambda:\mathbb T(M)_{\mathfrak m}\to\mathcal O_\lambda$ be an integral characteristic-zero eigencharacter after a finite coefficient extension, and write

$$
a_v=\lambda(T_v).
$$

On the corresponding lower multiplicity line, (10.1) has determinant

$$
\Delta_v(\lambda)
=(q_v+1)^2-a_v^2
=(q_v+1-a_v)(q_v+1+a_v).
\tag{10.4}
$$

For $\varepsilon\in\{1,-1\}$ define

$$
c_v^\varepsilon=q_v+1-\varepsilon a_v.
\tag{10.5}
$$

The vector

$$
x_\varepsilon=(x,-\varepsilon x)
\tag{10.6}
$$

is an eigenvector of the Gram matrix with eigenvalue $c_v^\varepsilon$. Its companion $(x,\varepsilon x)$ has eigenvalue $c_v^{-\varepsilon}$.

If

$$
a_v\equiv\varepsilon(q_v+1)\pmod\varpi,
\tag{10.7}
$$

then $G_vx_\varepsilon$ is divisible by $\varpi$. Ihara injectivity says that $d(x_\varepsilon)$ is nevertheless nonzero modulo $\varpi$. Thus Gram degeneracy is not degeneracy of the old map. It is failure of the old pairing to remain unimodular.

If $q_v\not\equiv-1\pmod\ell$ and $\ell$ is odd, then under (10.7)

$$
c_v^{-\varepsilon}\equiv2(q_v+1)\not\equiv0\pmod\varpi.
\tag{10.8}
$$

Hence the determinant and the chosen signed factor have the same valuation. If $q_v\equiv-1\pmod\ell$, both factors can be nonunits and the determinant no longer isolates one sign.

The branch Smith correction is related but must not be counted as an
independent copy of the same signed congruence. On a simultaneous eigenline for
$F_v^*$, write $f_v=\lambda(F_v^*)$. The branch relation is

$$
a_v=f_v+q_vf_v^{-1},
\qquad
f_vc_v^\varepsilon
=-\varepsilon(f_v-\varepsilon)(f_v-\varepsilon q_v).
\tag{10.8a}
$$

Meanwhile the Smith operator for $\mathcal C_{\mathrm{br},v}$ is
$1-f_v^2$. If $f_v\equiv\varepsilon\pmod\varpi$,
$q_v\not\equiv1\pmod\ell$, and $2$ is a unit, then
$f_v-\varepsilon q_v$ and $1+\varepsilon f_v$ are units. Hence

$$
v_\varpi(c_v^\varepsilon)
=v_\varpi(1-\varepsilon f_v)
=v_\varpi(1-f_v^2).
\tag{10.8b}
$$

Thus, on a separated primitive rank-one branch, the branch Smith factor and
the signed Gram factor record the same local crossing. In higher multiplicity
one must compare their full Smith modules; one may neither delete
$\mathcal C_{\mathrm{br},v}$ from the filtration nor multiply its Fitting ideal
into the Gram ideal a second time.

### 10.3 The Iwahori operator and sign

The old plane also carries the Iwahori operator $U_v$. With the right-coset and central conventions of Section 2.2, it satisfies

$$
U_v^2-T_vU_v+q_vS_v=0
\tag{10.9}
$$

on the old quotient. To prove (10.9), decompose the product of the Iwahori double coset with itself. One part returns to the original oriented edge and contributes the central translate $q_vS_v$; the remaining part ranges over the hyperspecial neighbors and contributes $T_vU_v$. Moving terms gives the displayed relation.

On a trivial-central residual eigensystem satisfying (10.7), the two roots of (10.9) are

$$
\varepsilon,\qquad \varepsilon q_v.
\tag{10.10}
$$

Indeed their sum is $\varepsilon(q_v+1)$ and product is $q_v$. If $q_v\not\equiv1\pmod\ell$, these roots are distinct. Hensel factorization then gives integral idempotents in the localized old algebra, because the difference $\varepsilon(1-q_v)$ is a unit. These idempotents distinguish the two old stabilizations; they are not used to read the sign of the Gram vector (10.6).

The Gram sign is read from $W_v$. This involution exchanges the two degeneracy maps, so

$$
W_vd(x,-\varepsilon x)
=d(-\varepsilon x,x)
=-\varepsilon d(x,-\varepsilon x).
\tag{10.11}
$$

Because $2$ is a unit, the $W_v=\pm1$ projectors are integral. The correction in Section 11.1 may be made in the same $W_v=-\varepsilon$ block. On the genuinely new special line, (2.5a) identifies this with the $U_v=\varepsilon$ block.

On the genuinely new characteristic-zero quotient, local newvector theory gives

$$
U_v^2=S_v
\tag{10.12}
$$

in the selected special family. Thus $U_v=\varepsilon$ in the trivial-central sign block. Equation (10.12) is not imposed on the old plane, where the quadratic relation is (10.9).

### 10.4 The exceptional congruences

The two exclusions $q_v\not\equiv1$ and $q_v\not\equiv-1$ have different meanings.

If $q_v\equiv1\pmod\ell$, the two old roots in (10.10) coincide. Conditional on the abelian Ihara hypothesis, the full two-map old image remains saturated, and the $W_v$ sign projectors still exist because $2$ is a unit; however there is no integral projector selecting one ordered $U_v$ root. A theorem for an ordered local flag or a residually scalar local Galois representation needs an enhanced line/type datum. The full constant-coefficient theorem does not manufacture that datum.

If $q_v\equiv-1\pmod\ell$, the roots $\varepsilon$ and $-\varepsilon$ are distinct, but both signed Gram factors may vanish. An integral $U_v$-projector can still separate the old roots, yet the unrefined determinant (10.4) counts both Gram signs and the two scalar factors can share branch-Smith support. Exact congruence depth must be computed from the full Smith map in a separately proved selected local block, not from $\Delta_v$ or from one asserted scalar.

If $\ell=2$, the signs coincide. Neither the signed Gram decomposition nor branch reversal retains the required information. The clean theorem assumes $\ell\ge7$.

Finally, $\Delta_v=0$ in characteristic zero is not a finite level-raising congruence. It is the reducible boundary at which the generic old/new complement or the restricted old pairing degenerates. Removing it requires the generic-support/noncharacter hypothesis packet by packet; the phrase “non-Eisenstein” alone is not a proof that every scalar or vexing localization has disappeared. Globally scalar residual systems, residually scalar local systems with no chosen line, and the usual vexing primes are therefore outside every rank-one signed formula unless an enhanced integral type theorem is supplied.

## 11. Integral level raising

### 11.1 From a Gram kernel to a new class

We begin with an integral construction rather than an existence argument in a generic eigenspace.

Let $x\in M_{\mathfrak m}^{\oplus2}$ have primitive reduction and suppose

$$
G_vx\in\varpi(M_{\mathfrak m}^{\oplus2})^\vee.
\tag{11.1}
$$

Surjectivity of $d^*$ gives $z\in N_{\mathfrak m}$ such that

$$
d^*z=\varpi^{-1}G_vx.
\tag{11.2}
$$

If $x$ is a $W_v$-eigenvector, apply the corresponding integral $W_v$-projector to $z$. The maps $d^*$ and $G_v$ are $W_v$-equivariant, so equation (11.2) is preserved and $z$ has the same sign.

Set

$$
y=d(x)-\varpi z.
\tag{11.3}
$$

Then

$$
d^*y=G_vx-\varpi d^*z=0,
$$

so $y\in N_{\mathfrak m}^\perp$. Modulo $\varpi$ one has

$$
\bar y=\overline{d(x)}.
\tag{11.4}
$$

Residual Ihara injectivity makes (11.4) nonzero. Therefore a primitive Gram-kernel vector produces a nonzero residual orthogonal-new class.

For an eigenvector $x_0\in M$ and sign $\varepsilon$, take $x=(x_0,-\varepsilon x_0)$. Condition (11.1) is exactly the signed congruence (10.7). Equation (10.11) and the equivariant correction put $\bar y$ in the $W_v=-\varepsilon$ block, which is the $U_v=\varepsilon$ block after passage to the new quotient.

Every step is necessary. Ihara injectivity proves nonvanishing. Saturation proves surjectivity of $d^*$ and freeness of the quotient. Perfectness moves Gram divisibility to the orthogonal lattice. The sign projector identifies the local branch.

### 11.2 The support theorem

The construction extends from a chosen eigenvector to an arbitrary residual maximal ideal.

Put

$$
e_\varepsilon^{\mathrm{new}}
=\frac{1-\varepsilon W_v}{2}.
\tag{11.4a}
$$

This integral idempotent selects $W_v=-\varepsilon$. On the new special quotient it is the $U_v=\varepsilon$ sign block by (2.5a). Write $Q^\varepsilon=e_\varepsilon^{\mathrm{new}}Q$.

**Theorem 11.1 (residual level raising).** Let $\mathfrak m$ be a non-Eisenstein maximal ideal in the lower faithful Hecke order. Assume:

1. the abelian Ihara condition (1.5d), in addition to the geometric, neat/tame-descent, and non-Eisenstein hypotheses of Section 1.3;
2. the local central operator has been specialized to $S_v=1$; equivalently, the displayed sign normalization is the trivial-central one;
3. $q_v\not\equiv\pm1\pmod\ell$;
4. for some $\varepsilon\in\{1,-1\}$,
   $$
   T_v-\varepsilon(q_v+1)\in\mathfrak m;
   $$
5. the localized residual lower module contains a primitive vector on which the common away-from-$v$ algebra acts through $\mathbb T/\mathfrak m$;
6. the $U_v$ action and the selected local type are normalized as in Section 10.3.

Then the $v$-new sign-$\varepsilon$ quotient has a maximal ideal $\mathfrak n$ whose contraction to the away-from-$v$ lower algebra is $\mathfrak m$. Equivalently,

$$
(Q^\varepsilon)_{\mathfrak n}/\varpi
\ne0.
\tag{11.5}
$$

If the node-uniformization and generic-support hypotheses also hold, then under the integral Jacquet--Langlands comparison the same residual away-from-$v$ eigensystem occurs in

$$
S(B^\dagger,U^\dagger,k)_{\mathfrak n}^{\mathrm{nc}}.
\tag{11.6}
$$

**Proof strategy.** Apply the construction of Section 11.1 to the signed vector. The finite commuting Hecke algebra generated on its orbit has a simple residual quotient, which defines $\mathfrak n$. The order comparison transports it to the definite lattice.

**Proof.** Choose a nonzero vector $\bar x_0$ in the residual lower $\mathfrak m$-eigenspace and lift it primitively to $x_0\in M_{\mathfrak m}$. Put $x=(x_0,-\varepsilon x_0)$. Hypothesis 4 makes $G_vx$ divisible by $\varpi$ modulo the maximal ideal, and localization lets us perform (11.2)--(11.4) in the generalized $\mathfrak m$-block. The resulting $\bar y$ is nonzero and orthogonal-new.

Equation (10.11) and the equivariant correction show that $\bar y$ lies in the $W_v=-\varepsilon$ block. On the new quotient this is the $U_v=\varepsilon$ block by (2.5a). The finite-dimensional $k$-space generated by this component under the commuting Hecke image has a simple quotient. Its character defines a maximal ideal $\mathfrak n$ above $\mathfrak m$, proving (11.5).

The quotient $Q$ is torsion-free, so this residual class is not the boundary of coefficient torsion. Theorem 8.1 identifies the faithful new Hecke order with the definite order, and Theorem 6.1 identifies their residual modules. This gives (11.6). $\square$

Hypothesis 5 is automatic when one works with a field-valued residual eigensystem in the support of the faithful lower module; it is stated to distinguish a residual character from an empty maximal ideal of an abstract Hecke algebra.

### 11.3 Lifting the residual system

Theorem 11.1 already produces a nonzero localization of a finite free new lattice. It therefore produces characteristic-zero branches.

**Corollary 11.2 (characteristic-zero raised packet).** After a finite extension of $E$, there is a characteristic-zero eigencharacter

$$
\lambda^{\mathrm{new}}:
\mathbb T_{\mathrm{curve},\mathfrak n}^{v\text{-new}}
\longrightarrow\mathcal O'
\tag{11.7}
$$

reducing to $\mathfrak n$. Its automorphic packet is $v$-new of sign $\varepsilon$, and its switched definite packet has the same good Hecke eigenvalues.

**Proof.** The localized faithful order is finite flat over $\mathcal O$. Every maximal ideal of its special fiber contains a minimal prime not containing $\varpi$: otherwise a power of $\varpi$ would vanish on that component, contradicting torsion-freeness. The corresponding generic factor is a finite field extension of $E$. Normalize it, choose a prime above $\mathfrak n$, and enlarge $E$ so its integer ring contains the eigenvalues. Evaluation gives (11.7).

The integral sign idempotent places the branch in the $U_v=\varepsilon$ factor. Generic local newvector theory then identifies the local component as the selected Steinberg twist. The node comparison and Theorem 8.1 give the switched definite packet and equality of good eigenvalues. $\square$

The corollary asserts existence of some characteristic-zero raised packet. It does not say that a previously chosen target packet is that branch, and it does not promise a chosen congruence depth beyond the residual one.

### 11.4 Exact congruence depth

Exact depth requires several hypotheses which cannot be hidden in the word eigensystem. Assume that after extending coefficients the chosen lower branch lattice $L_\lambda\subset M$ is free of rank one, generated by a primitive vector $x_0$, and that its dual branch is also primitive. Assume also that the generic old and new summands are complementary on this localization. On the old plane, the Gram matrix diagonalizes in the signed basis because $2$ is a unit:

$$
(x_0,-\varepsilon x_0),
\qquad
(x_0,\varepsilon x_0).
$$

If $c_v^{-\varepsilon}$ is a unit, the Smith form has one nonunit elementary divisor, namely $c_v^\varepsilon$. Hence

$$
\operatorname{coker}(G_v|_{L_\lambda^{\oplus2}})_{\varepsilon}
\simeq\mathcal O_\lambda/(c_v^\varepsilon).
\tag{11.8}
$$

Formula (11.8) is the exact **Gram Smith module** without any Gorenstein or Hecke-freeness assertion. To identify it with the lattice-theoretic old--new congruence module, additionally require the unimodularity comparison of Book 85: the ambient pairing is perfect, the saturated generic old and orthogonal-new lattices are the two lattices being compared, and the restricted branch lattice maps to its full dual with no further index. Under that hypothesis,

$$
\operatorname{Fitt}_{\mathcal O_\lambda}
(C_v^\varepsilon)=(c_v^\varepsilon),
\qquad
\ell(C_v^\varepsilon)=v_\lambda(c_v^\varepsilon).
\tag{11.9}
$$

This proves exact lattice depth. To call the same ideal the **augmented Hecke congruence ideal**, require one further comparison: either rank-one freeness of the localized module over the acting Hecke order together with its perfect self-duality, or an independently constructed congruence functional identifying the lattice module with the augmentation module. Generic multiplicity one alone does not supply this condition.

If the branch has multiplicity greater than one, the full Smith normal form is required and the determinant records only the sum of elementary-divisor valuations. If both signed factors are nonunits, (11.8) is false without first projecting to an integral $U_v$ branch. The Smith module $\mathcal C_{\mathrm{br},v}$ remains present in the quotient filtration; in the separated rank-one case (10.8b) identifies its selected elementary divisor with $c_v^\varepsilon$, so its Fitting ideal must not be multiplied into (11.9) a second time.

Under Theorem 8.1, any augmented-order congruence invariant that has been identified under the preceding additional hypothesis is the same in the definite realization. Thus integral Jacquet--Langlands neither changes nor contributes an extra factor to (11.9); equality of acting orders does not by itself prove the prior Gram-to-augmentation identification.

**Worked sign calculation.** Take $q_v=2$, let $\ell=7$, and suppose a lower eigenbranch has $a_v\equiv3\pmod7$. Then $\varepsilon=1$ and

$$
c_v^+=3-a_v\in7\mathcal O,
\qquad
c_v^-=3+a_v\equiv6\pmod7.
$$

The companion factor is a unit. If $v_7(3-a_v)=n$, the signed Gram Smith module is $\mathcal O/(7^n)$ when $7$ is the coefficient uniformizer; under the unimodularity and augmentation hypotheses just stated, this is also the signed congruence module. The residual old vector $(x,-x)$ maps nontrivially to the $U_v=1$ new block. The switched definite order has exactly the same augmented depth once that identification has been made.

If instead $q_v=6$ and $\ell=7$, then $q_v\equiv-1$. A relation $a_v\equiv0$ makes both $7-a_v$ and $7+a_v$ nonunits. The determinant valuation is their sum and cannot be assigned to one sign. The primitive new quotient and definite order comparison still hold, but the scalar formula (11.9) must be replaced by the Smith form in a proved $U_v$-selected block.

## 12. Integral level lowering

### 12.1 The correct residual question

Level lowering is not the inverse of level raising. A characteristic-zero packet can be new and special at $v$ while its residual monodromy vanishes. The conclusion is not that the same characteristic-zero packet becomes unramified. It is that its residual away-from-$v$ eigensystem occurs at hyperspecial level.

Let $\mathfrak n$ be a non-Eisenstein maximal ideal of the $v$-new order, and let $\mathfrak m^{(v)}$ be its contraction to the common Hecke algebra away from $v$. The desired statement is

$$
M_{\mathfrak m^{(v)}}/\varpi\ne0.
\tag{12.1}
$$

Once (12.1) holds, finite flatness of the lower faithful order supplies a characteristic-zero lower-level branch after coefficient extension. No $U_v$ sign survives in the away-from-$v$ contraction unless a separate refinement is retained.

The geometric substitute for the phrase “residually unramified” is vanishing of the monodromy operator on the localized residual cohomology:

$$
\overline N_{\mathrm{mon}}=0
\quad\text{on }Q_{\mathfrak n}/\varpi.
\tag{12.2}
$$

Condition (12.2) concerns the full operator, not merely its semisimplification.

### 12.2 Normalization, residues, and components

The integral filtration before reduction is (8.2), not a filtration whose bottom is automatically $X_v^\vee$. Reduction of
$X_v^\vee\hookrightarrow L_0$ is injective exactly when the Tor boundary
$\mathcal C_{\mathrm{br},v}[\varpi]$ vanishes. Thus impose, in addition to component cleanliness,

$$
\mathcal C_{\mathrm{br},v}[\varpi]_{\mathfrak n}=0.
\tag{12.2a}
$$

Since the localized branch module is finite over the DVR, (12.2a) is equivalent to its vanishing. Under this condition the residual extreme pieces are

$$
X_{v,\mathfrak n}^\vee/\varpi,
\qquad
X_{v,\mathfrak n}(-1)/\varpi,
\tag{12.3}
$$

and monodromy is the reduction of $q_\Gamma$ followed by the now primitive inclusion into $L_0/\varpi$. If

$$
\Phi[\varpi]_{\mathfrak n}=0,
\tag{12.4}
$$

then (6.7), together with (12.2a), shows that quotient monodromy induces an isomorphism

$$
q_\Gamma\otimes k:
X_{v,\mathfrak n}/\varpi
\xrightarrow{\sim}
X_{v,\mathfrak n}^\vee/\varpi
\tag{12.5}
$$

is an isomorphism. Thus a nonzero top residue necessarily has nonzero monodromy.

Before quotienting, the middle piece comes from the cohomology of the two normalized branches. By (5.4) it is built from two copies of lower-level cohomology, with Frobenius interchanged. Its quotient by the projected old image is precisely the branch module $\mathcal C_{\mathrm{br},v}$. Consequently, if (12.1) fails the localized normalization term is zero; hypothesis (12.2a) is the uniform condition that prevents a residual Tor class from that quotient in the general argument.

There remains a possible bottom graph class, on which monodromy is automatically zero. Perfect Poincaré duality pairs the bottom piece at $\mathfrak n$ with the top piece at $\mathfrak n^*$. If the maximal ideal is adjoint stable and the residual pairing remains perfect, a nonzero bottom piece forces a nonzero top piece. This is the precise role of self-duality in the lowering argument.

Two small graphs make the component hypothesis concrete. For one loop of thickness $n$, monodromy is multiplication by $n$ and the component group is $\mathbf Z/n\mathbf Z$. If $\ell\nmid n$, zero residual monodromy forces the top residue to vanish. If $\ell\mid n$, every top residue has zero monodromy modulo $\ell$, so no lowering conclusion follows without more information.

For two vertices joined by $m$ unit edges, (6.9) shows that the graph-pairing kernel is controlled by the $\ell$-primary part of the cyclic component group of order $m$. The hypothesis $\Phi[\varpi]=0$ is exactly $\ell\nmid m$ in this example. Independently, the Smith form of $1-(F_v^*)^2$ controls whether the inclusion into $L_0$ stays injective after reduction. Both maps must be clean.

### 12.3 The lowering theorem

**Theorem 12.1 (integral level lowering).** Let $\mathfrak n$ be a maximal ideal occurring in the $v$-new quotient. Assume:

1. the clean semistable hypotheses and the abelian Ihara condition (1.5d), so that the old image is actually saturated and $Q$ is free;
2. $\mathfrak n$ is non-Eisenstein and stable under the Hecke adjoint;
3. Poincaré duality descends to a perfect Hecke-equivariant pairing between the residual $Q_{\mathfrak n}$ block and its adjoint block, and pairs the top graph quotient with the saturated bottom submodule;
4. residual monodromy vanishes as in (12.2);
5. the localized component obstruction vanishes as in (12.4);
6. the localized normalized-branch correction has no residual torsion as in (12.2a);
7. the normalization middle piece is exactly the two lower-level branches of (5.4), with no stabilizer or coefficient torsion;
8. the residual block is nonzero and no scalar, self-twist, or vexing-prime identification merges it with the Eisenstein branch.

Then the contracted away-from-$v$ eigensystem occurs at hyperspecial level:

$$
M_{\mathfrak m^{(v)}}/\varpi\ne0.
\tag{12.6}
$$

After a finite coefficient extension, it has a characteristic-zero lower-level lift.

**Proof strategy.** Suppose the lower localization vanished. The normalization contribution would vanish. Component and branch cleanliness would make monodromy an isomorphism from the top graph piece to the saturated bottom lattice. Vanishing monodromy would kill the top; perfect self-duality would then kill the bottom. The whole nonzero block would vanish, a contradiction.

**Proof.** Assume (12.6) is false. Exactness of localization and the branch table make the normalized-component contribution to $Q_{\mathfrak n}/\varpi$ zero. By hypotheses 4--6, reduction preserves $X_v^\vee\hookrightarrow L_0$, and (12.5) together with the factorization (8.3) forces the top graded piece to be zero: any nonzero top residue would map nontrivially to the saturated bottom.

Poincaré duality pairs the top graded piece of the $\mathfrak n^*$ block perfectly with the bottom piece of the $\mathfrak n$ block. Since $\mathfrak n=\mathfrak n^*$, the vanishing just proved forces the bottom piece to vanish. The bottom, top, and normalization quotient are zero, so $Q_{\mathfrak n}/\varpi=0$. This contradicts hypothesis 8 and the occurrence of $\mathfrak n$ in the faithful new module. Hence (12.6) holds.

The lower module is finite free over $\mathcal O$. Its nonzero residual localization has a maximal ideal of its faithful image algebra, and finite flatness supplies a characteristic-zero branch exactly as in Corollary 11.2. $\square$

The theorem is deliberately geometric. In any setting where another construction identifies residual inertia with the monodromy operator, genuine unramifiedness implies hypothesis 4. That interpretation is not needed for the proof.

### 12.4 Why each hypothesis is necessary

If only the semisimplification of monodromy vanishes, a nonzero unipotent extension can remain. It lies in the top-to-bottom map and need not lower.

If the component group has $\varpi$-torsion, a nonzero top residue can lie in the kernel of $q_\Gamma\otimes k$. It then has zero residual monodromy without coming from the normalized lower components.

If $\mathcal C_{\mathrm{br},v}$ has $\varpi$-torsion, the injection
$X_v^\vee\to L_0$ need not remain injective after reduction. A nonzero graph
monodromy class can then die at the second arrow of (8.3), even when the
component group is clean. This is independent of the first failure.

If the block is not adjoint stable, a bottom class can be paired with a top class in a different maximal ideal. Vanishing of the top in one block does not kill the bottom in the other.

If stabilizer orders are divisible by $\ell$, invariants on a fine cover need not be exact. Extra middle or graph classes can enter after descent.

If the residual block is scalar or Eisenstein, the tree character module can survive. Such a class may occur at Iwahori level for reasons unrelated to a cuspidal lower packet.

Finally, hypotheses 5 and 6 are sufficient rather than formally necessary in every refined situation. A stronger type-selected theorem can sometimes track a nonzero component or branch module and still lower a chosen branch. The present theorem states the uniform clean criterion proved by the displayed filtration.

## 13. Types, twists, and nonmaximal local level

### 13.1 Selected type lattices

Maximal level on $B_v^\dagger$ corresponds to the special family (4.5)--(4.6). A selected dihedral packet requires a distinguished compact-mod-center type

$$
(J_v,\Lambda_v)
\quad\longleftrightarrow\quad
(J_v^\dagger,\Lambda_v^\dagger).
\tag{13.1}
$$

Over a coefficient DVR with residue characteristic different from that of $F_v$, and for unit-valued labels, these types have finite free stable lattices. Their multiplicity modules

$$
\operatorname{Hom}_{J_v}(\Lambda_v,\Pi_v),
\qquad
\operatorname{Hom}_{J_v^\dagger}(\Lambda_v^\dagger,\Pi_v^\dagger)
\tag{13.2}
$$

are rank one over the coefficient field. Intersecting with the integral fixed module and saturating gives primitive rank-one $\mathcal O$-lattices, well defined up to a unit.

The graph-node construction with coefficients in $\Lambda_v^\dagger$ is valid only when the type sheaf extends over the full incidence model, pull and norm preserve it, every finite stabilizer order is a unit, and a type-specific residual Ihara theorem makes the selected old image primitive. The edge module is then a vector-valued definite function module. If, in addition, the type-specific generic residue theorem identifies the curve-new and graph packet supports, the incidence and common-kernel arguments prove analogues of Theorems 6.1 and 8.1. None of these type-coefficient assertions follows from the constant-coefficient abelian Ihara condition. They are explicit external hypotheses for the type-enhanced variant.

The unit ambiguity in a primitive local generator does not alter the global image order. Both sides remain images of the same abstract Hecke algebra, and Lemma 3.2 compares kernels rather than chosen basis vectors.

### 13.2 Twisting and conductor cancellation

Let $\chi$ be a unit-valued Hecke character. Twisting on the split curve side uses $\chi\circ\det$; twisting on the definite side uses $\chi\circ\operatorname{Nrd}$. Matching characteristic polynomials give

$$
\det g=\operatorname{Nrd}d,
$$

so the node dictionary, local transfer, and Hecke-order equality commute with twisting.

Conductors must be recomputed from the twisted label. For a special packet, replace $\mu$ by $\mu\chi$ in (2.6). For a dihedral packet, replace

$$
\theta\quad\text{by}\quad
\theta(\chi\circ N_{L/F_v})
\tag{13.3}
$$

in (2.7). Cancellation can lower the conductor. A maximum of the old conductor and twice the twist conductor is not a valid formula.

As a concrete check, let $\mu$ be a nontrivial tame quadratic character. The special packet has exponent two. Twisting by $\mu$ gives the unramified special packet, whose exponent is one. On the division side the raw depth drops to zero, but the transfer-facing exponent remains one. Every level ideal in the comparison must use this prepared exponent.

### 13.3 Dihedral local factors

For a tame admissible pair $(L/F_v,\theta)$, both inner-form members have conductor

$$
v_v(\mathfrak d_{L/F_v})+f(L/F_v)a_L(\theta).
\tag{13.4}
$$

The common parameter is $\operatorname{Ind}_{W_L}^{W_{F_v}}\theta$, with zero monodromy. Its standard Euler factor is one in the irreducible selected case, and its epsilon factor contains the quadratic induction constant. Equality of these local factors is part of the packet identification, not a consequence of (13.4).

At the semistable Iwahori prime used for the basic level-raising theorem, the new local component is special and has nonzero monodromy. A dihedral supercuspidal does not appear in the same two-branch Steinberg raising problem merely because its conductor happens to be two. To change into a dihedral type one must replace the Iwahori local model and Gram calculation by the corresponding type-enhanced model. The integral inner-form comparison remains available once that model supplies a saturated incidence complex.

### 13.4 Boundaries of the selected theorem

The basic one-prime semistable theorem includes the unramified special family at Iwahori level. Ramified special twists, unramified quadratic depth-zero packets, and tame positive-depth dihedral packets are included only in the conditional type-enhanced variant of Section 13.1, with its extension, pull--norm, stabilizer, type-Ihara, saturation, and generic-support hypotheses all imposed.

It excludes primitive wild packets and ramified dyadic positive-depth packets. The local character and type-lattice comparison used in Chapter 4 is not proved there. It also excludes a type projector that exists only after inverting $\varpi$: applying such a projector to a saturated full cohomology lattice can create a nonsaturated intersection.

Residual irreducibility of a reduced type is not automatic when $\ell$ divides $q_v-1$, $q_v+1$, or another tame normalizer order. The stable lattice and the Hecke-order comparison remain meaningful, but multiplicity-one statements after reduction require the banal or explicitly checked intertwining hypotheses.

## 14. Several primes and order of operations

### 14.1 Iterated one-prime change

Let $P=\{v_1,\ldots,v_r\}$ be a finite set of clean level-changing primes. One may apply the one-prime theorem successively. At stage $i$, localize the module obtained after the first $i-1$ changes and verify anew:

$$
\text{abelian Ihara, non-Eisensteinness, adjoint stability, node/support comparison, and sign separation.}
\tag{14.1}
$$

If these hypotheses persist, induction gives a free quotient at every stage. At stage $i$, the graph comparison identifies the relevant one-prime quotient with the definite algebra obtained by switching $v_i$ and $\tau$, while retaining the already imposed levels at the other finite places. These stagewise comparisons do not compose formally into one algebra ramified at every prime of $P$: quaternionic parity and the archimedean invariant must be recomputed for the proposed final inner form, and its node/packet comparison must be proved separately.

For lowering, component and branch-Smith cleanliness must also be checked at that stage. The order of primes can matter. Lowering at one prime can enlarge a residual multiplicity space at another, expose a component or branch module, or destroy an integral branch projector. A statement that each prime is clean in the original module is not by itself a proof that every intermediate module is clean.

### 14.2 Tensor-product degeneracy complexes

A simultaneous formulation uses the tensor product of the two-term local complexes

$$
C_v^\bullet:
M_v^{\oplus2}\xrightarrow{d_v}N_v.
\tag{14.2}
$$

For two primes the total complex is

$$
M^{\oplus4}
\longrightarrow
N_{v_1}^{\oplus2}\oplus N_{v_2}^{\oplus2}
\longrightarrow
N_{v_1v_2}.
\tag{14.3}
$$

The alternating signs come from orienting the square of local edges. There is, however, no canonical identification of (14.3) with a tensor product of abstract one-prime complexes merely because all terms are $\mathcal O$-free. A simultaneous theorem requires explicit cartesian base-change maps from the iterated global-level complexes and a quasi-isomorphism with the derived tensor product over the relevant common acting or augmentation base $A$.

Assume those comparison maps are isomorphisms and

$$
\operatorname{Tor}^{A}_j
\bigl(H^1(C_{v_i}^\bullet),H^1(C_{v_{i'}}^\bullet)\bigr)=0
\qquad(j>0)
\tag{14.3a}
$$

at every intermediate stage, with the analogous higher-fold conditions. Then the Kunneth spectral sequence has no higher terms and the total complex is exact in the expected degrees.

Under those hypotheses this gives a simultaneous saturated new quotient. If a one-prime cokernel is not flat over $A$, or an intermediate base-change square fails, a higher $\operatorname{Tor}_1$ term can enter (14.3) and imitate a multi-prime new class. Freeness over $\mathcal O$ alone does not rule this out, because the relevant Tor is over the acting/character base. Thus this chapter proves no unconditional several-prime theorem; it records the exact hypotheses under which the one-prime theorem may be iterated or totalized.

### 14.3 Accumulated congruence ideals

Assume at each $v\in P$ there is a rank-one branch, a separated sign $\varepsilon_v$, and a primitive signed factor

$$
c_v^{\varepsilon_v}=q_v+1-\varepsilon_va_v.
$$

If the simultaneous degeneracy complex satisfies the derived comparison and Tor-independence of Section 14.2, the pairings tensor unimodularly, every local Gram module has been identified with the relevant lattice congruence module, and the several-prime augmentation meets the branches transversely, then its signed Gram presentation is the tensor product of the local presentations. Fitting-ideal multiplicativity gives

$$
\operatorname{Fitt}(C_P)
=\prod_{v\in P}(c_v^{\varepsilon_v}).
\tag{14.4}
$$

Equivalently, lengths add:

$$
\ell(C_P)=\sum_{v\in P}v_\varpi(c_v^{\varepsilon_v}).
\tag{14.5}
$$

If a higher Tor group is nonzero, (14.4) is false; its contribution is governed by the determinant/Fitting identity of the resulting derived complex and need not be expressible as a naively multiplied “extra factor.” If multiplicities exceed one, each local scalar factor must be replaced by the Fitting ideal of the full local Smith module. Pairwise branch depths alone do not determine a many-branch augmentation ideal.

At any stage where the one-prime node and support hypotheses hold, integral Jacquet--Langlands introduces no further factor. A simultaneous final-inner-form assertion is not proved by multiplying these stagewise equalities; it additionally requires a valid global ramification set, a common packet support theorem, and a coefficient-one multi-node comparison for that inner form.

For two primes $v_1,v_2$ on rank-one branches, the signed Gram basis has four vectors indexed by $(\pm,\pm)$. On the selected $(\varepsilon_1,\varepsilon_2)$ vector the total Gram operator acts by

$$
c_{v_1}^{\varepsilon_1}c_{v_2}^{\varepsilon_2}.
\tag{14.6}
$$

If both companion factors are units and all the derived comparison, transversality, and acting-base flatness hypotheses hold, its congruence length is the sum of the two local valuations. If the first surviving module is nonflat over the common acting/augmentation base, derived tensoring with the second local complex can produce a $\operatorname{Tor}_1$ term even though both modules are $\mathcal O$-free. The determinant of the total derived complex, rather than a guessed additive correction, is then the invariant. This explains the Tor-independence clause in (14.4).

### 14.4 Exceptional-prime bookkeeping

For repeated use it is helpful to record the exact failure at each boundary.

| situation | conclusion that can fail | conclusion that remains |
|---|---|---|
| Eisenstein localization | congruence-character kernel vanishing | exact tree description of the kernel |
| failure of abelian Ihara (1.5d) | residual injectivity, saturation, free $Q$, raising, and order comparison through $Q$ | ambient graph, node, and branch-map calculations |
| $\ell$-divisible stabilizer | exact descent from a neat cover | comparison on the neat cover |
| $q_v\equiv1\pmod\ell$ | ordered old-root projector | conditional saturation of the full two-map image and $W_v$ signs |
| $q_v\equiv-1\pmod\ell$ | one-factor determinant formula | full Gram and branch Smith matrices and conditional order comparison |
| nonzero $\Phi[\varpi]_{\mathfrak n}$ | clean level lowering from zero monodromy | ambient graph discriminant sequence |
| nonzero $\mathcal C_{\mathrm{br},v}[\varpi]_{\mathfrak n}$ | injection of bottom graph monodromy after reduction and clean lowering | exact quotient filtration and extension (8.3a) |
| non-adjoint-stable block | bottom-to-top self-dual argument | duality with the adjoint block |
| nonunit type label | existence of a stable finite lattice | characteristic-zero local transfer |
| primitive wild type | selected local comparison | no assertion beyond the proved selected range |

The table distinguishes failure of a labelled refinement from failure of the full conditional lattice theorem. Once (1.5d) and the node/support hypotheses hold, $q_v\equiv\pm1$ does not invalidate full-map saturation or away-from-$v$ acting-order equality; it invalidates a simpler signed corollary.

## 15. The complete comparison theorem

### 15.1 Statement

We now collect the book's results in one reusable form.

**Theorem 15.1 (conditional integral level change and Jacquet--Langlands comparison).** Let $F,B,B^\dagger,v,U,U_0(v),U^\dagger,\mathcal O$, and $\mathfrak m$ satisfy the clean datum of Section 1.3, including the abelian Ihara condition (1.5d), node uniformization, and generic support. Use unnormalized right-double-coset operators, geometric class matching, the selected local Jacquet--Langlands normalization, and the fixed central/component block. Then:

1. the degeneracy map
   $$
   d_{\mathfrak m}:H^1(X_U,\mathcal O)_{\mathfrak m}^{\oplus2}
   \longrightarrow H^1(X_{U_0(v)},\mathcal O)_{\mathfrak m}
   $$
   is injective with saturated image;
2. its quotient $Q_{\mathfrak m}$ is finite free and its orthogonal new lattice is canonically $Q_{\mathfrak m}^\vee$;
3. the monodromy multiplicity lattice is canonically
   $$
   X_{v,\mathfrak m}=H_1(\Gamma,\mathcal O)_{\mathfrak m}
   \simeq S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}};
   $$
4. the edge pairing is the definite mass pairing, and its cokernel is the localized $\ell$-primary Néron component group;
5. the quotient filtration and monodromy are the exact sequences (8.2) and (8.3a), so the independent branch correction is
   $$
   \mathcal C_{\mathrm{br},v}
   \simeq\operatorname{coker}(1-(F_v^*)^2);
   $$
6. the $v$-new curve and switched definite faithful images of the common away-from-$\Sigma$ Hecke algebra are equal inside their common generic eigenvalue algebra;
7. every congruence, cotangent, conductor, normalization, and branch-difference ideal belonging to that common acting order is identical in the two realizations; no extra Jacquet--Langlands congruence index occurs, while the component and branch modules remain visible;
8. the old Gram operator is (10.1), or (10.2) before trivial-central specialization;
9. in the trivial-central normalization, under $q_v\not\equiv\pm1\pmod\ell$, the signed relation
   $$
   T_v\equiv\varepsilon(q_v+1)\pmod{\mathfrak m}
   $$
   produces a nonzero residual $v$-new packet of sign $\varepsilon$ and hence, after coefficient extension, a characteristic-zero raised packet on both inner forms;
10. on a primitive rank-one branch with unit companion factor, the Gram Smith ideal is
   $$
   (q_v+1-\varepsilon a_v);
   $$
   it is the lattice or augmented Hecke congruence ideal only under the additional unimodularity and congruence-functional hypotheses of Section 11.4;
11. a nonzero adjoint-stable residual new block with zero monodromy lowers to hyperspecial level when both
   $\Phi[\varpi]_{\mathfrak n}$ and
   $\mathcal C_{\mathrm{br},v}[\varpi]_{\mathfrak n}$ vanish and the stated normalization and nonexceptional hypotheses hold.

Every assertion is compatible with unit-valued twists, contragredients, finite flat coefficient extension, operators in the declared common algebra, and signed residue Galois action. Type-enhanced special or selected dihedral variants are included only under every additional hypothesis listed in Section 13.1. Several-prime variants are only the conditional iterations or derived-Tor-independent totalizations of Chapter 14.

### 15.2 Proof

**Proof strategy.** There are five steps, and none uses a conclusion from a later step. The abelian Ihara condition first turns Book 139's exact kernel calculation into a free new quotient. Node uniformization identifies the graph lattice with definite forms. Book 125's semisimplicity and the corrected generic filtration identify the generic kernels, while rational global transfer interprets the resulting packets. A common-kernel argument descends this support equality to integral Hecke orders. Finally, the Gram and corrected monodromy calculations give raising and lowering.

**Proof.** The exact tree criterion, hypothesis (1.5d), and Lemma 3.1 prove clauses 1 and 2. The regular semistable model gives the graph filtration and shows that old classes have no toric extreme, while Book 139's branch Smith calculation gives clause 5. The node-uniformization hypothesis identifies nodes with the $B^\dagger$ class set; localization of the routed incidence sequence proves clause 3. The equality of edge and mass pairings proves clause 4.

Book 125's semisimplicity and the generic form of (8.2) identify the characteristic-zero curve-new and graph kernels; Book 104 interprets the graph packets as selected noncharacter split packets. Lemma 3.2 and Theorem 6.1 prove clause 6. Clause 7 follows because all listed invariants are invariants of that common augmented order. The component group and $\mathcal C_{\mathrm{br},v}$ are explicit geometric modules, not order indices.

Pull--norm composition proves clause 8. For clause 9, use the signed Gram vector, surjectivity of $d^*$, and formula (11.3) to produce a nonzero residual orthogonal-new class. The integral sign projector selects its special branch. Finite flatness lifts its maximal ideal to a generic branch, and the order comparison transfers its away-from-$v$ system to $B^\dagger$. Smith reduction on a primitive rank-one branch proves the first assertion of clause 10; Book 85's unimodularity and congruence-functional criteria give exactly the additional identifications stated there.

For clause 11, assume the lower localization is zero. The normalization contribution then vanishes. Component cleanliness makes $q_\Gamma$ invertible after reduction, and branch cleanliness keeps $X_v^\vee\to L_0$ injective after reduction. Thus zero monodromy kills the top, and adjoint-stable perfect duality kills the bottom. The whole new block would vanish, a contradiction. Thus the lower block is nonzero. All compatibility assertions have already been checked for the constituent maps and pairings, so they hold for the assembled theorem. $\square$

### 15.3 Dependency and normalization audit

The logical sources and retained hypotheses are as follows.

| source package | result used | retained boundary | new conclusion here |
|---|---|---|---|
| Book 80: local Jacquet--Langlands | selected character identity, conductors, factors, integral type lines | special and tame-dihedral only; unit-valued labels; banal hypotheses when residual irreducibility is used | type-compatible switch at $v$ |
| Book 85: Hecke algebras and congruences | faithful finite image orders, localization, pairings, Fitting ideals, branch language | no automatic reducedness, Hecke freeness, Gorensteinness, or Gram-to-augmentation identification | common-kernel order equality; exact scalar ideals only under Section 11.4's extra hypotheses |
| Book 104: global Jacquet--Langlands | selected noncharacter packet bijection from the totally definite algebra, multiplicity, and good Hecke data | totally real algebraic weight; norm characters removed; rational comparison only | split interpretation of the graph packets after geometric occurrence is proved |
| Book 125: automorphic decomposition of Shimura-curve $H^1$ | packet decomposition and rational semisimplicity on the actual one-split-place curve at both levels | full component routing or a separating projector; characteristic zero only | generic old/new support on $Q_E$ |
| Book 139: conditional saturated Ihara theory | exact tree kernel, conditional primitive old image and free quotient, Gram matrix, graph discriminant, branch Smith correction | proper clean curves; constant coefficients; $v\nmid\ell$; neat or tame descent; non-Eisenstein localization plus the independent abelian Ihara condition (1.5d) | uses its corrected filtration in raising, lowering, and order comparison |
| node uniformization | superspecial nodes identified with the switched definite class set, including routing, weights, and coefficient-one scale | an explicit external hypothesis for the chosen PEL datum | integral graph--definite lattice map |

The direct-dependency audit adds Book 125's generic-support input to the local
Jacquet--Langlands, Hecke, global Jacquet--Langlands, and Ihara sources. The exact current row is

$$
140\mid80,85,104,125,139,
\tag{15.1a}
$$

and the theorem is additionally conditional on the datum-specific node-uniformization hypothesis and on Book 139's abelian Ihara condition. Book 139 in turn records its own direct prerequisites $16,38,39,124,118,122$; they are transitive rather than silently reproved here. The repository dependency table records both corrected rows.

The downstream interface is equally exact.

| consumer | valid output from this book | condition that the consumer must retain |
|---|---|---|
| Book 176 | one-prime special raising/lowering and common away-from-$v$ acting order | (1.5d), node/support hypotheses, both finite modules in (8.3a), and Section 11.4 before using a scalar as an augmented congruence ideal |
| Book 170 | free $Q$, equality of faithful inner-form trace orders, and geometric lowering criterion | freeness and order equality are conditional on abelian Ihara; lowering requires both $\Phi[\varpi]=0$ and $\mathcal C_{\mathrm{br},v}[\varpi]=0$ |
| Book 174 | coefficient-one constant graph--definite map $X_v\simeq S^\dagger$ | Book 140 does not give $\operatorname{gr}_0Q=X_v^\vee$; a type-coefficient primitive residue or bottom-lattice statement must be proved independently, together with type-Ihara |
| Book 175 | no inner-form order index and the signed Gram Smith factor | the factor is an augmented congruence ideal only under Section 11.4; scalar/vexing refinements and all fixed-prime Tor/augmentation statements require the separate Book 174 hypotheses |

In particular, no downstream patching or reciprocity argument can retroactively prove (1.5d), delete $\mathcal C_{\mathrm{br},v}$, or turn the conditional several-prime discussion into a theorem.

The normalization chain is equally rigid:

| datum | convention |
|---|---|
| good Hecke operator | unnormalized right double coset |
| good polynomial | $1-T_wX+q_wS_wX^2$ |
| adjoint | $T_w^*=S_w^{-1}T_w$ |
| class transfer | equal characteristic polynomial |
| orbital transfer | geometric sign $+1$ |
| local spectral transfer | one sign $-1$ at each ramified place |
| global sign | product $+1$ over the even ramification set |
| special conductor | $1$ if the twist is unramified, $2a(\mu)$ otherwise |
| old Gram matrix | diagonal $q_v+1$, off-diagonal $T_v$ and its transpose |
| signed factor | $q_v+1-\varepsilon a_v$ |
| ambient graph monodromy | weighted edge pairing $q_\Gamma:X_v\to X_v^\vee$ |
| quotient monodromy | $X_v\xrightarrow{q_\Gamma}X_v^\vee\to L_0$, with cokernel extension (8.3a) |

Changing a row requires changing every dependent formula. In particular, normalized Satake operators would rescale (10.1), a left-coset convention would transpose the off-diagonal entries, and arithmetic rather than geometric Frobenius would invert unramified labels.

### 15.4 Exact scope

The theorem proves a complete **conditional** one-prime integral level-change statement for the clean compact weight-two Shimura curves and their switched totally definite inner forms. Its conditions include the abelian Ihara vanishing which Book 139 leaves open and the datum-specific node classification, while generic support is imported from direct prerequisite Book 125. It covers the full two-map Iwahori lattice and its special sign blocks when the roots separate. Type-enhanced variants require the longer hypothesis list of Section 13.1, not merely extension of a type sheaf.

It does not cover Eisenstein maximal ideals, failure of (1.5d), coefficient characteristic equal to the residue characteristic at $v$, noncompact boundary cohomology, $\ell$-divisible stabilizers, primitive wild types, or a projector defined only over the fraction field. It does not turn torsion-freeness into an integral old--new direct sum. It does not assert that either the Néron component group or $\mathcal C_{\mathrm{br},v}$ vanishes.

At $q_v\equiv1\pmod\ell$, conditional full-image saturation and Hecke-order comparison remain valid, but an ordered root needs extra data. At $q_v\equiv-1\pmod\ell$, the full Gram and branch maps remain valid, but the determinant does not measure one sign. Scalar or vexing systems require a separately represented enhanced line/type problem. At higher multiplicity, the full Smith module replaces one scalar congruence factor. At several primes, iteration is valid only while every intermediate hypothesis persists; simultaneous statements require the explicit derived comparison and acting-base Tor-independence of Section 14.2.

These are the exact boundaries of the conditional theorem. In particular, proving (1.5d) uniformly is unfinished arithmetic work in Book 139's dependency closure, not a conclusion of this book.

## 16. Conclusion

### 16.1 The established package

Under the three explicit external conditions of Theorem 15.1, the integral comparison consists of five exact sequences and one equality of orders.

The old sequence is

$$
0\longrightarrow M_{\mathfrak m}^{\oplus2}
\xrightarrow{d}N_{\mathfrak m}
\longrightarrow Q_{\mathfrak m}\longrightarrow0,
$$

with every term free. Its dual new lattice is

$$
\ker d^*_{\mathfrak m}\simeq Q_{\mathfrak m}^\vee.
$$

The monodromy--component sequence is

$$
0\longrightarrow X_{v,\mathfrak m}
\xrightarrow{q_\Gamma}X_{v,\mathfrak m}^\vee
\longrightarrow\Phi[\ell^\infty]_{\mathfrak m}\otimes\mathcal O
\longrightarrow0.
$$

The corrected quotient filtration is

$$
0\longrightarrow X_{v,\mathfrak m}^\vee
\longrightarrow L_0
\longrightarrow\mathcal C_{\mathrm{br},v}
\longrightarrow0,
$$

$$
0\longrightarrow L_0
\longrightarrow Q_{\mathfrak m}
\longrightarrow X_{v,\mathfrak m}(-1)
\longrightarrow0,
$$

and quotient monodromy has cokernel

$$
0\longrightarrow\Phi[\ell^\infty]_{\mathfrak m}\otimes\mathcal O
\longrightarrow\operatorname{coker}(X_v\to L_0)
\longrightarrow\mathcal C_{\mathrm{br},v}
\longrightarrow0.
$$

The node theorem identifies

$$
X_{v,\mathfrak m}
\simeq S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}},
$$

and the faithful image orders satisfy

$$
\mathbb T_{\mathrm{curve},\mathfrak m}^{v\text{-new}}
=\mathbb T_{B^\dagger,\mathfrak m}.
$$

Each finite module has one source. Under abelian Ihara, the old quotient has no coefficient torsion. The Gram Smith module measures failure of orthogonal splitting and becomes the chosen congruence module only under the extra comparison of Section 11.4. The ambient graph cokernel is the component group. The inclusion of the bottom graph lattice has the independent Smith cokernel $\mathcal C_{\mathrm{br},v}$, though on a separated rank-one crossing it records the same selected local factor as the Gram map. There is no further module measuring an unexplained integral Jacquet--Langlands order index.

### 16.2 The conceptual picture

One local edge controls the whole theory. Its two vertices give the two degeneracy maps. The arithmetic group acting on the local tree identifies every relation between them and proves that its congruence-continuous part is Eisenstein. After non-Eisenstein localization the remaining kernel is the explicit noncongruence-character module (7.3a). Only the abelian Ihara condition makes the edge map primitive and its quotient a genuine lattice when the Gram determinant is a nonunit.

In the special fiber, the same edge becomes a node. Under the explicit superspecial node-uniformization hypothesis, the collection of nodes is the class set of the quaternion algebra obtained by ramifying at the changing finite place and at the formerly split real place. Cycles in the node graph are therefore definite automorphic forms with their natural integral scale. The edge-length pairing is the ambient graph monodromy pairing and the mass pairing on the definite class set. In the quotient $Q$ it is followed by $X_v^\vee\to L_0$, which exposes the branch correction.

Rational Jacquet--Langlands performs one precise task: it interprets a graph packet, already known to occur by Book 125 and the corrected generic filtration, as the unique selected split cuspidal packet. It does not prove occurrence in the indefinite curve. Once equality of generic support is supplied by that direct prerequisite, torsion-freeness descends equality of generic kernels to equality of integral kernels. That short argument eliminates the otherwise possible congruence index between two acting orders in the same generic algebra.

Finally, the old Gram matrix converts a signed Hecke congruence into a nonzero new residual class. Conditional saturation makes it live in a free quotient, and the integral order comparison carries its common away-from-$v$ eigensystem across the inner form. In the opposite direction, the corrected normalization and monodromy filtration show that a genuinely monodromy-free residual new block lowers only when both the component and branch-Smith obstructions are clean. Integral level raising and lowering are thus two consequences of the same geometry, but not formal inverses: raising uses failure of unimodularity, while lowering uses vanishing of monodromy after both finite obstructions have been exposed.

The resulting conditional package preserves the common faithful Hecke order, the primitive graph--definite multiplicity lattice, every already identified augmented congruence invariant, the selected local sign in the basic special range, the component module, and the branch correction. It makes no unconditional claim beyond Book 139's unresolved abelian Ihara boundary and no automatic type or several-prime extension.
