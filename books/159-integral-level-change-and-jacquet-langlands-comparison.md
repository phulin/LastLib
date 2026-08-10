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
   - [The four prerequisite packages](#24-the-four-prerequisite-packages)
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

This book proves that, in the clean weight-two Shimura-curve setting, the intended congruence survives and the false one does not. The decisive geometric input is saturated Ihara theory. The decisive inner-form input is that the monodromy lattice of the semistable curve is itself the natural integral automorphic lattice on the switched definite quaternion algebra. Once those two facts are placed in one diagram, the two faithful Hecke orders are images of the same abstract algebra with the same kernel. No finite congruence index remains between them.

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

Only after localization at a clean non-Eisenstein maximal ideal is the image in (1.1) known to be saturated. At that point $Q$ is free. It is the correct integral receptacle for the $v$-new quotient. Its orthogonal companion is

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

The restrictions have distinct purposes. Properness removes cusp cohomology. Neatness removes stabilizer denominators. The condition $v\nmid\ell$ keeps the coefficient sheaf étale at the semistable prime. Non-Eisenstein localization kills the actual tree kernel. The selected-packet hypothesis is exactly the range in which local and global Jacquet--Langlands, conductor comparison, type lattices, and local factors have already been proved.

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

The main theorem has four layers.

First, the old map (1.1), localized at $\mathfrak m$, is injective with saturated image. Hence

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

Fourth, the Gram matrix

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

into a nonzero residual $v$-new class, provided the sign is integrally separated. Conversely, a residual new system with zero monodromy lowers to hyperspecial level when the component and branch-collision obstructions vanish. These are the integral level-raising and level-lowering theorems proved below.

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

### 2.4 The four prerequisite packages

We use four established packages, each with its hypotheses retained.

Book 84, *Local Jacquet--Langlands*, gives (2.5)--(2.7), the regular character sign, twist and contragredient compatibility, and saturated integral type lines. We use it only for selected packets and only with unit-valued coefficient data.

Book 91, *Hecke Algebras and Congruences*, says that the faithful image of a commuting Hecke family on a finite free $\mathcal O$-module is finite free over $\mathcal O$. Localization at a maximal ideal preserves faithfulness; perfect adjoint pairings localize; congruence modules are measured by Fitting ideals; and equality of generic branches alone does not imply equality of orders.

Book 94, *Global Jacquet--Langlands*, gives a rational bijection from selected noncharacter packets on the totally definite algebra to their split cuspidal packets, with identical good-place Hecke polynomials, multiplicities, rationality fields, central characters, and exact local components. Norm characters form an exceptional global block and are removed before claiming a cuspidal bijection. The global theorem does not itself identify integral lattices, nor do we use it as an unproved transfer theorem for the indefinite algebra $B$.

Book 158, *Ihara Theory and Saturated Degeneracy Maps on Shimura Curves*, applies to the curves and coefficient range of Section 1.3. It gives residual injectivity of (1.1), saturation of its localized image, the free quotient (1.2), perfect quotient--orthogonal duality, the exact Gram matrix, the integral monodromy filtration, and identification of the monodromy cokernel with the localized Néron component group.

These inputs fit without a gap. What is not supplied by any one of them is the integral identification of the graph lattice with the switched definite automorphic lattice and the resulting equality of image orders. Chapters 5--9 establish precisely that missing bridge.

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

The first arrow is proved in Chapters 5 and 6. The second is proved from the semistable filtration and local Iwahori newness in Section 8.3. Only after those proofs will global Jacquet--Langlands be used to interpret the common packet as the unique split cuspidal representation $\pi$. This order avoids using an indefinite global transfer that is not among the stated prerequisites and avoids using the desired integral comparison to prove itself.

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

Let $\mathcal Z$ be the finite geometric node set. Orient every edge from the branch $Y^{(0)}$ to $Y^{(1)}$. The dual graph $\Gamma$ has two vertices on each connected piece and one edge for every point of $\mathcal Z$. Multiple edges are retained. If a residue Galois element exchanges the branches, it reverses orientation and therefore acts by a minus sign on the corresponding edge generator.

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

where $n_z$ is the thickness of the node. In the original regular model $n_z=1$. Retaining $n_z$ makes the construction stable under ramified base change, when an edge is subdivided and the pairing is multiplied by the ramification index.

### 5.3 The switched-algebra description of nodes

The nodes have a second description which is not visible in the equation $xy=\varpi_v$. They are superspecial incidence objects. Their prime-to-$v$ quasi-isogenies form the adelic class set of $B^\dagger$.

We now prove the precise statement. Let $U^\dagger$ be the level of (4.4), including the same central and prime-to-$v$ data as $U$. Let $W^\dagger$ be the trivial compact weight at $\tau$ in parallel weight two. Put

$$
\mathcal X^\dagger
=(B^\dagger)^\times(F)\backslash
(B^\dagger)^\times(\mathbf A_f)/U^\dagger.
\tag{5.8}
$$

If a fixed central character is imposed, (5.8) is understood with its usual central quotient and transformation law.

**Theorem 5.1 (node uniformization).** There is a canonical bijection, compatible with residue Galois action and all away-from-$v$ Hecke correspondences,

$$
\mathcal Z\xrightarrow{\sim}\mathcal X^\dagger.
\tag{5.9}
$$

At nonneat level the statement holds equivariantly on a neat cover and descends when the deck-group order is a unit in $\mathcal O$.

**Proof strategy.** A node is the point where the two possible rank-$q_v$ directions in the active height-two group cease to be distinct. The endomorphism algebra of this superspecial object changes local invariant at $v$ and at the unique split real place. This produces $B^\dagger$. Prime-to-$v$ level structures turn quasi-isogeny classes into the double quotient (5.8).

**Proof.** Choose a geometric node $z$ and a representative PEL object $A_z$ with its polarization, endomorphisms, and prime-to-$v$ level. Let

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

The proof uses only the moduli interpretation of the already constructed semistable model and the classification by local invariants. It does not assume the integral comparison that (5.9) is meant to establish.

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

On the node set, the correspondence sends a level structure to the finite collection obtained by quotienting by the $q_w+1$ admissible rank-one subgroups. Under the quasi-isogeny coordinate used in Theorem 5.1 these are precisely the right translates $xg_{w,i}$. Hence (5.11) is the graph-edge action.

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

On a connected two-vertex graph, $C_0$ and $H_0$ are generated by component functions. A good Hecke correspondence has degree $q_w+1$ on every component and central value prescribed by $S_w$. Consequently the homology of the tail

$$
C_0\xrightarrow\epsilon H_0
$$

is annihilated by the Eisenstein ideal (2.4). The same is true for a Hecke-stable union of component orbits: the only additional action is a finite permutation coming from the central component group, already included in the fixed central block.

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

**Proof.** Theorem 5.1 identifies the edge module with the full definite function module and intertwines Hecke and Galois actions. Localization of the incidence sequence gives (6.3). Non-Eisenstein localization removes the norm-character block, so the right side of (6.3) is precisely the right side of (6.4).

All modules in (6.1) are finite free. Finite flat coefficient extension preserves exactness and the node bijection. The transpose compatibility is (5.12). Since (6.4) is an integral isomorphism, reduction modulo $\varpi^n$ preserves it for every $n$. $\square$

The theorem is stronger than equality of Brandt eigenvalues. It identifies the entire localized lattice, including generalized residual eigenspaces and nilpotent special-fiber action.

### 6.4 Pairings and monodromy

On the edge module define the weighted pairing

$$
\langle f,g\rangle_{\mathrm{edge}}
=\sum_{z\in\mathcal Z}\frac{n_z}{e_z}f(z)g(z),
\tag{6.5}
$$

where $e_z$ is the effective projective stabilizer order. At neat level $e_z=1$. Under tame descent $e_z$ is a unit, so (6.5) is integral. The same formula is the definite mass pairing under (5.9).

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

The cokernel is

$$
\operatorname{coker}(q_\Gamma)
\simeq
\Phi_{J_{U_0(v)}}(\bar k_v)[\ell^\infty]_{\mathfrak m}
\otimes_{\mathbf Z_\ell}\mathcal O.
\tag{6.7}
$$

Thus a nonzero component group is compatible with the lattice isomorphism (6.4). It measures failure of the restricted monodromy or mass pairing to be unimodular. It does not measure a discrepancy between the curve and definite Hecke orders.

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

With constant coefficients, this first cohomology consists of additive characters. For a good Hecke operator, restriction--conjugation--corestriction gives

$$
T_w\chi=(q_w+1)\chi,
\qquad S_w\chi=\chi
\tag{7.3}
$$

in the trivial-central block. Therefore the entire kernel, including its nonsplit extensions, is Eisenstein. After localization at $\mathfrak m$ it vanishes.

Comparison between singular and étale cohomology identifies the tree restriction maps with the geometric pullbacks. Hence

$$
(d\otimes k)_{\mathfrak m}:
(M/\varpi M)_{\mathfrak m}^{\oplus2}
\longrightarrow
(N/\varpi N)_{\mathfrak m}
\tag{7.4}
$$

is injective.

The hypotheses are visible in this proof. Constant coefficients turn cocycles into characters. Neatness removes stabilizer cohomology. Non-Eisenstein localization kills the computed kernel. The theorem would not follow merely from the nonvanishing of a determinant in characteristic zero.

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

and middle piece the cohomology of the two normalized branches. The old image comes from the good-reduction hyperspecial Jacobian and has no toric part. Therefore passing to the saturated quotient $Q$ leaves the two extreme graph lattices unchanged:

$$
\operatorname{gr}_0Q_{\mathfrak m}=X_{v,\mathfrak m}^\vee,
\qquad
\operatorname{gr}_2Q_{\mathfrak m}=X_{v,\mathfrak m}(-1).
\tag{8.2}
$$

Monodromy on $Q$ is

$$
X_{v,\mathfrak m}(-1)
\xrightarrow{q_\Gamma}
X_{v,\mathfrak m}^\vee(-1).
\tag{8.3}
$$

We call $X_{v,\mathfrak m}$ the **curve-new automorphic multiplicity lattice**. The terminology separates the automorphic multiplicity from the two extreme cohomological degrees in which it appears. A characteristic-zero special packet contributes one automorphic line but a two-step monodromy block to curve cohomology.

### 8.2 Comparison with the definite lattice

Combining (8.2) with Theorem 6.1 gives

$$
X_{v,\mathfrak m}
\simeq
S(B^\dagger,U^\dagger,\mathcal O)_{\mathfrak m}^{\mathrm{nc}}.
\tag{8.4}
$$

This is the integral Jacquet--Langlands comparison of lattices. It has three exact meanings.

First, every good Hecke operator acts by the same integral matrix on the two sides after the node basis is chosen. Second, the mass pairing is the monodromy edge pairing with the same stabilizer and thickness factors. Third, reduction retains the full localized generalized eigenspace, not merely its semisimplification.

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

where $V_\Pi$ denotes the cohomological realization of the packet, with its one-dimensional automorphic multiplicity and two-dimensional monodromy block. Old packets have been removed by (7.5).

On each summand in (8.5), the top residue map to $X_{v,E}(-1)$ is nonzero. A special local component has nonzero monodromy, while a selected supercuspidal type at a deeper parahoric level contributes through its distinguished type residue. Conversely every generic eigenpacket of $X_{v,E}$ produces a summand of $Q_E$ because the edge class is the residue of the corresponding semistable packet. Therefore

$$
\ker\bigl(\mathbb T^{\Sigma,\mathrm{abs}}_E
\to\operatorname{End}_E(Q_{\mathfrak m,E})\bigr)
=
\ker\bigl(\mathbb T^{\Sigma,\mathrm{abs}}_E
\to\operatorname{End}_E(X_{v,\mathfrak m,E})\bigr).
\tag{8.6}
$$

One can also prove (8.6) packet by packet. The left kernel is the intersection of the eigencharacter kernels of the $v$-new packets. The right kernel is the intersection for the graph packets. The residue map gives both inclusions between these packet sets: a new special packet has nonzero top residue, and a graph eigenpacket is a graded constituent of the new quotient. Global Jacquet--Langlands for $B^\dagger$ then identifies their common good-place character with the unique split cuspidal packet described in Section 4.3.

Here is a local proof that no clean Iwahori packet is lost. Put $H=\operatorname{GL}_2(F_v)$, $K=\operatorname{GL}_2(\mathcal O_{F_v})$, and let $I\subset K$ be the standard Iwahori. An irreducible generic representation in the unramified Iwahori block has one of the two forms relevant here.

For an irreducible unramified principal series with distinct Satake roots, the $I$-fixed space has dimension two and the $K$-fixed space has dimension one. The two degeneracy translates of the spherical vector span the $I$-fixed space. Indeed, if $\mathcal B\subset H$ is the upper Borel, the two double cosets in $\mathcal B(F_v)\backslash H/I$ give a basis of the induced-model invariants, and the transition determinant from the two degeneracy vectors is the difference of the Satake roots. Such a packet is entirely old and disappears from $Q_E$.

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

**Proof.** Equation (8.6) supplies the common-generic-kernel hypothesis of Lemma 3.2 for $Q_{\mathfrak m}$ and $X_{v,\mathfrak m}$. Both are finite free over $\mathcal O$. Lemma 3.2 therefore identifies their integral image algebras. Theorem 6.1 identifies the latter image with (8.8), proving (8.9).

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

On the automorphic lattice, the analogous dual defect is the cokernel of the restricted mass pairing. Diagram (6.6) identifies it with the monodromy discriminant (6.7). Therefore every finite index visible in duality has a geometric name:

$$
\operatorname{coker}(q_{\mathrm{mass}})
\simeq\operatorname{coker}(q_\Gamma)
\simeq\Phi[\ell^\infty]_{\mathfrak m}\otimes\mathcal O.
\tag{9.2}
$$

This finite module can be nonzero. It appears on both sides of the integral comparison and hence does not create an index between the two Hecke orders.

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

For every augmentation $\lambda$ of the common order, the cotangent module, augmented congruence ideal, normalization conductor, and branch-difference ideals computed from either realization agree. The only additional finite module in the semistable realization is the explicitly displayed component module (9.2).

**Proof.** Equality (8.9) immediately gives (9.3). Every listed invariant is functorial in the augmented order itself, so it is identical for the two realizations. The semistable pairing defect is (9.2), while saturation of (7.5) proves that no old-quotient torsion contributes another factor. $\square$

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

and the Hecke-order equality base changes. Fitting ideals extend. If the ramification index is $e$, uniformizer-normalized lengths multiply by $e$; the ideals themselves are the invariant statement.

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

If $q_v\equiv1\pmod\ell$, the two old roots in (10.10) coincide. The full two-map old image remains saturated, but there is no integral projector selecting one ordered root. A theorem for an ordered local flag needs extra type data.

If $q_v\equiv-1\pmod\ell$, the roots $\varepsilon$ and $-\varepsilon$ are distinct, but both signed Gram factors may vanish. An integral $U_v$-projector can still separate the old roots, yet the unrefined determinant (10.4) counts both Gram signs. Exact congruence depth must be computed in a selected local block rather than from $\Delta_v$.

If $\ell=2$, the signs coincide. Neither the signed Gram decomposition nor branch reversal retains the required information. The clean theorem assumes $\ell\ge7$.

Finally, $\Delta_v=0$ in characteristic zero is not a level-raising congruence. It means the two old vectors are rationally dependent on that packet. In the clean constant-coefficient quaternionic setting such a packet belongs to the scalar or norm-character exception and is removed by non-Eisenstein localization.

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

1. the clean Ihara hypotheses of Section 1.3;
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

Under the integral Jacquet--Langlands comparison, the same residual eigensystem occurs in

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

Exact depth requires a rank-one hypothesis which cannot be hidden in the word eigensystem. Assume that after extending coefficients the chosen lower branch lattice $L_\lambda\subset M$ is free of rank one, generated by a primitive vector $x_0$, and that its dual branch is also primitive. On the old plane, the Gram matrix diagonalizes in the signed basis because $2$ is a unit:

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

By perfectness and primitivity, the Gram cokernel is the old--new congruence module on this signed branch. Therefore

$$
\operatorname{Fitt}_{\mathcal O_\lambda}
(C_v^\varepsilon)=(c_v^\varepsilon),
\qquad
\ell(C_v^\varepsilon)=v_\lambda(c_v^\varepsilon).
\tag{11.9}
$$

This proves exact depth. If the branch has multiplicity greater than one, the full Smith normal form is required and the determinant records only the sum of elementary-divisor valuations. If both signed factors are nonunits, (11.8) is false without first projecting to an integral $U_v$ branch.

Under Theorem 8.1 the same module and Fitting ideal are obtained in the definite realization. Thus integral Jacquet--Langlands neither changes nor contributes an extra factor to (11.9).

**Worked sign calculation.** Take $q_v=2$, let $\ell=7$, and suppose a lower eigenbranch has $a_v\equiv3\pmod7$. Then $\varepsilon=1$ and

$$
c_v^+=3-a_v\in7\mathcal O,
\qquad
c_v^-=3+a_v\equiv6\pmod7.
$$

The companion factor is a unit. If $v_7(3-a_v)=n$, the signed congruence module is $\mathcal O/(7^n)$ when $7$ is the coefficient uniformizer. The residual old vector $(x,-x)$ maps nontrivially to the $U_v=1$ new block. The switched definite form has exactly the same depth because the two acting orders and their augmentation ideals are equal.

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

The semistable filtration on $Q_{\mathfrak n}/\varpi$ has extreme pieces

$$
X_{v,\mathfrak n}^\vee/\varpi,
\qquad
X_{v,\mathfrak n}(-1)/\varpi,
\tag{12.3}
$$

and monodromy is the reduction of $q_\Gamma$. If

$$
\Phi[\varpi]_{\mathfrak n}=0,
\tag{12.4}
$$

then (6.7) shows that

$$
q_\Gamma\otimes k:
X_{v,\mathfrak n}/\varpi
\xrightarrow{\sim}
X_{v,\mathfrak n}^\vee/\varpi
\tag{12.5}
$$

is an isomorphism. Thus a nonzero top residue necessarily has nonzero monodromy.

The middle piece comes from the cohomology of the two normalized branches. By (5.4) it is built from two copies of lower-level cohomology, with Frobenius interchanged. Consequently, if (12.1) fails, the localized middle piece is zero.

There remains a possible bottom graph class, on which monodromy is automatically zero. Perfect Poincaré duality pairs the bottom piece at $\mathfrak n$ with the top piece at $\mathfrak n^*$. If the maximal ideal is adjoint stable and the residual pairing remains perfect, a nonzero bottom piece forces a nonzero top piece. This is the precise role of self-duality in the lowering argument.

Two small graphs make the component hypothesis concrete. For one loop of thickness $n$, monodromy is multiplication by $n$ and the component group is $\mathbf Z/n\mathbf Z$. If $\ell\nmid n$, zero residual monodromy forces the top residue to vanish. If $\ell\mid n$, every top residue has zero monodromy modulo $\ell$, so no lowering conclusion follows without more information.

For two vertices joined by $m$ unit edges, (6.9) shows that the only possible kernel of residual monodromy is the $\ell$-primary part of the cyclic component group of order $m$. The hypothesis $\Phi[\varpi]=0$ is exactly $\ell\nmid m$ in this example. It removes one explicit elementary divisor of the graph pairing.

### 12.3 The lowering theorem

**Theorem 12.1 (integral level lowering).** Let $\mathfrak n$ be a maximal ideal occurring in the $v$-new quotient. Assume:

1. the clean semistable and saturated Ihara hypotheses;
2. $\mathfrak n$ is non-Eisenstein and stable under the Hecke adjoint;
3. the Poincaré pairing on the residual localized block is perfect;
4. residual monodromy vanishes as in (12.2);
5. the localized component obstruction vanishes as in (12.4);
6. the normalization middle piece is exactly the two lower-level branches of (5.4), with no stabilizer or coefficient torsion;
7. the residual block is nonzero and no scalar or self-twist identification merges it with the Eisenstein branch.

Then the contracted away-from-$v$ eigensystem occurs at hyperspecial level:

$$
M_{\mathfrak m^{(v)}}/\varpi\ne0.
\tag{12.6}
$$

After a finite coefficient extension, it has a characteristic-zero lower-level lift.

**Proof strategy.** Suppose the lower localization vanished. The middle piece of the semistable filtration would vanish. Component control would make monodromy an isomorphism from the top graph piece to the bottom graph piece. Vanishing monodromy would kill the top; perfect self-duality would then kill the bottom. The whole nonzero block would vanish, a contradiction.

**Proof.** Assume (12.6) is false. Exactness of localization and the branch table make the normalized-component middle graded piece of $Q_{\mathfrak n}/\varpi$ zero. By hypotheses 4 and 5, the isomorphism (12.5) and the factorization of monodromy force the top graded piece to be zero: any nonzero top residue would map nontrivially to the bottom.

Poincaré duality pairs the top graded piece of the $\mathfrak n^*$ block perfectly with the bottom graded piece of the $\mathfrak n$ block. Since $\mathfrak n=\mathfrak n^*$, the vanishing just proved forces the bottom piece to vanish. All three graded pieces are zero, so $Q_{\mathfrak n}/\varpi=0$. This contradicts hypothesis 7 and the occurrence of $\mathfrak n$ in the faithful new module. Hence (12.6) holds.

The lower module is finite free over $\mathcal O$. Its nonzero residual localization has a maximal ideal of its faithful image algebra, and finite flatness supplies a characteristic-zero branch exactly as in Corollary 11.2. $\square$

The theorem is deliberately geometric. In any setting where another construction identifies residual inertia with the monodromy operator, genuine unramifiedness implies hypothesis 4. That interpretation is not needed for the proof.

### 12.4 Why each hypothesis is necessary

If only the semisimplification of monodromy vanishes, a nonzero unipotent extension can remain. It lies in the top-to-bottom map and need not lower.

If the component group has $\varpi$-torsion, a nonzero top residue can lie in the kernel of $q_\Gamma\otimes k$. It then has zero residual monodromy without coming from the normalized lower components.

If the block is not adjoint stable, a bottom class can be paired with a top class in a different maximal ideal. Vanishing of the top in one block does not kill the bottom in the other.

If stabilizer orders are divisible by $\ell$, invariants on a fine cover need not be exact. Extra middle or graph classes can enter after descent.

If the residual block is scalar or Eisenstein, the tree character module can survive. Such a class may occur at Iwahori level for reasons unrelated to a cuspidal lower packet.

Finally, hypothesis 5 is sufficient rather than formally necessary in every refined situation. A stronger type-selected theorem can sometimes track a nonzero component group and still lower a chosen branch. The present theorem states the uniform clean criterion actually proved by the displayed filtration.

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

The graph-node construction with coefficients in $\Lambda_v^\dagger$ is valid when the type sheaf extends over the incidence model and every finite stabilizer order is a unit. The edge module is then a vector-valued definite function module. The incidence sequence remains exact because its coefficient module is free, and non-Eisenstein localization again removes the vertex term. Thus Theorems 6.1 and 8.1 extend to these selected types under the stated extension hypothesis.

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

The selected integral theorem includes unramified special twists, ramified special twists with unit-valued labels, unramified quadratic depth-zero packets, and tame positive-depth dihedral packets whose type sheaves satisfy the prime-to-stabilizer conditions.

It excludes primitive wild packets and ramified dyadic positive-depth packets. The local character and type-lattice comparison used in Chapter 4 is not proved there. It also excludes a type projector that exists only after inverting $\varpi$: applying such a projector to a saturated full cohomology lattice can create a nonsaturated intersection.

Residual irreducibility of a reduced type is not automatic when $\ell$ divides $q_v-1$, $q_v+1$, or another tame normalizer order. The stable lattice and the Hecke-order comparison remain meaningful, but multiplicity-one statements after reduction require the banal or explicitly checked intertwining hypotheses.

## 14. Several primes and order of operations

### 14.1 Iterated one-prime change

Let $P=\{v_1,\ldots,v_r\}$ be a finite set of clean level-changing primes. One may apply the one-prime theorem successively. At stage $i$, localize the module obtained after the first $i-1$ changes and verify anew:

$$
\text{non-Eisensteinness, adjoint stability, saturation, and sign separation.}
\tag{14.1}
$$

If these hypotheses persist, induction gives a free quotient at every stage and an equality of the corresponding switched inner-form Hecke orders.

The order of primes can matter. Lowering at one prime can enlarge a residual multiplicity space at another, expose a component group, or destroy an integral branch projector. A statement that each prime is clean in the original module is not by itself a proof that every intermediate module is clean.

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

The alternating signs come from orienting the square of local edges. If every one-prime cokernel is flat over $\mathcal O$ and the base-change maps identify the intermediate modules, the Kunneth spectral sequence has no higher $\operatorname{Tor}$ terms and the total complex is exact in the expected degrees.

This gives a simultaneous saturated new quotient. If a one-prime cokernel has torsion, a higher $\operatorname{Tor}_1$ term enters (14.3) and can imitate a multi-prime new class. Thus the tensor-product theorem is not a formal consequence of generic old--new decomposition; one-prime flatness is its indispensable hypothesis.

### 14.3 Accumulated congruence ideals

Assume at each $v\in P$ there is a rank-one branch, a separated sign $\varepsilon_v$, and a primitive signed factor

$$
c_v^{\varepsilon_v}=q_v+1-\varepsilon_va_v.
$$

If the simultaneous degeneracy complex is Tor-independent and the pairings tensor perfectly, its signed Gram presentation is the tensor product of the local presentations. Fitting-ideal multiplicativity gives

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

If a higher Tor group is nonzero, its Fitting ideal is an additional factor and (14.4) is false. If multiplicities exceed one, each local scalar factor must be replaced by the Fitting ideal of the full local Smith module.

Integral Jacquet--Langlands introduces no further factor at any stage. The equality of orders is compatible with iteration because every step is a common-kernel comparison for the same surviving packet set.

For two primes $v_1,v_2$ on rank-one branches, the signed Gram basis has four vectors indexed by $(\pm,\pm)$. On the selected $(\varepsilon_1,\varepsilon_2)$ vector the total Gram operator acts by

$$
c_{v_1}^{\varepsilon_1}c_{v_2}^{\varepsilon_2}.
\tag{14.6}
$$

If both companion factors are units and the intermediate quotients are flat, its congruence length is the sum of the two local valuations. If the first quotient has $\varpi$-torsion, tensoring its presentation with the second local complex produces a $\operatorname{Tor}_1$ term. Its length is an extra summand. This direct calculation explains the Tor-independence clause in (14.4).

### 14.4 Exceptional-prime bookkeeping

For repeated use it is helpful to record the exact failure at each boundary.

| situation | conclusion that can fail | conclusion that remains |
|---|---|---|
| Eisenstein localization | Ihara injectivity and saturation | tree description of the kernel |
| $\ell$-divisible stabilizer | exact descent from a neat cover | comparison on the neat cover |
| $q_v\equiv1\pmod\ell$ | ordered old-root projector | saturation of the full two-map image |
| $q_v\equiv-1\pmod\ell$ | one-factor determinant formula | full Gram matrix and order comparison |
| nonzero $\Phi[\varpi]_{\mathfrak n}$ | clean level lowering from zero monodromy | exact monodromy--component sequence |
| non-adjoint-stable block | bottom-to-top self-dual argument | duality with the adjoint block |
| nonunit type label | existence of a stable finite lattice | characteristic-zero local transfer |
| primitive wild type | selected local comparison | no assertion beyond the proved selected range |

The table distinguishes failure of a labelled refinement from failure of the full lattice theorem. In particular, $q_v\equiv\pm1$ does not invalidate saturation or integral inner-form order equality; it invalidates a simpler signed corollary.

## 15. The complete comparison theorem

### 15.1 Statement

We now collect the book's results in one reusable form.

**Theorem 15.1 (integral level change and Jacquet--Langlands comparison).** Let $F,B,B^\dagger,v,U,U_0(v),U^\dagger,\mathcal O$, and $\mathfrak m$ satisfy the clean datum of Section 1.3. Use unnormalized right-double-coset operators, geometric class matching, the selected local Jacquet--Langlands normalization, and the fixed central character. Then:

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
5. the $v$-new curve and switched definite faithful Hecke orders are equal inside their common generic eigenvalue algebra;
6. every congruence, cotangent, conductor, normalization, and branch-difference ideal belonging to that common order is identical in the two realizations; no extra Jacquet--Langlands congruence index occurs;
7. the old Gram operator is (10.1), or (10.2) before trivial-central specialization;
8. in the trivial-central normalization, under $q_v\not\equiv\pm1\pmod\ell$, the signed relation
   $$
   T_v\equiv\varepsilon(q_v+1)\pmod{\mathfrak m}
   $$
   produces a nonzero residual $v$-new packet of sign $\varepsilon$ and hence, after coefficient extension, a characteristic-zero raised packet on both inner forms;
9. on a primitive rank-one branch with unit companion factor, the exact level-raising congruence ideal is
   $$
   (q_v+1-\varepsilon a_v);
   $$
10. a nonzero adjoint-stable residual new block with zero monodromy lowers to hyperspecial level when its localized component group has no $\varpi$-torsion and the stated normalization and nonexceptional hypotheses hold.

Every assertion is compatible with unit-valued twists, contragredients, finite flat coefficient extension, away-from-$v$ Hecke operators, and signed residue Galois action. Selected dihedral types are included when their integral type sheaves extend over the incidence construction with prime-to-$\ell$ stabilizers.

### 15.2 Proof

**Proof strategy.** There are five steps, and none uses a conclusion from a later step. Saturated Ihara theory first constructs the free new quotient. The node moduli problem then identifies the graph lattice with definite forms. Rational global transfer identifies generic support. A common-kernel argument descends this support equality to integral Hecke orders. Finally, the Gram and monodromy calculations give raising and lowering.

**Proof.** Residual Ihara injectivity and Lemma 3.1 prove clauses 1 and 2. The regular semistable model gives the graph filtration and shows that old classes have no toric extreme. Theorem 5.1 identifies nodes with the $B^\dagger$ class set; localization of the incidence sequence proves clause 3. The equality of edge and mass pairings proves clause 4.

The semistable residue map and the node comparison identify every characteristic-zero $v$-new curve packet with exactly one selected noncharacter definite packet and preserve all common Hecke characters. Hence the generic kernels on $Q$ and $X_v$ agree. Lemma 3.2 and Theorem 6.1 prove clause 5. Clause 6 follows because all listed invariants are invariants of that common augmented order, while the only pairing defect is the common component module.

Pull--norm composition proves clause 7. For clause 8, use the signed Gram vector, surjectivity of $d^*$, and formula (11.3) to produce a nonzero residual orthogonal-new class. The integral $U_v$ projector selects its sign. Finite flatness lifts its maximal ideal to a generic branch, and the order comparison transfers the branch to $B^\dagger$. Smith reduction on a primitive rank-one branch proves clause 9.

For clause 10, assume the lower localization is zero. The normalization middle piece then vanishes. Component control makes residual monodromy an isomorphism between the top and bottom graph pieces; zero monodromy kills the top, and adjoint-stable perfect duality kills the bottom. The whole new block would vanish, a contradiction. Thus the lower block is nonzero. All compatibility assertions have already been checked for the constituent maps and pairings, so they hold for the assembled theorem. $\square$

### 15.3 Dependency and normalization audit

The logical sources and retained hypotheses are as follows.

| source package | result used | retained boundary | new conclusion here |
|---|---|---|---|
| Book 84: local Jacquet--Langlands | selected character identity, conductors, factors, integral type lines | special and tame-dihedral only; unit-valued labels; banal hypotheses when residual irreducibility is used | type-compatible switch at $v$ |
| Book 91: Hecke algebras and congruences | faithful finite image orders, localization, pairings, Fitting ideals, branch language | no automatic reducedness, freeness over the Hecke algebra, or Gorensteinness | common-kernel order equality and exact congruence ideals |
| Book 94: global Jacquet--Langlands | selected noncharacter packet bijection from the totally definite algebra, multiplicity, and good Hecke data | totally real algebraic weight; norm characters removed; rational comparison only | split interpretation of the graph packets after geometric occurrence is proved |
| Book 158: saturated Ihara theory | residual injectivity, primitive old image, free quotient, Gram and monodromy--component sequence | proper clean curves; constant coefficients; $v\nmid\ell$; neat or tame descent; non-Eisenstein localization | integral node lattice, raising, lowering, and order comparison |

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
| monodromy | weighted edge pairing $q_\Gamma:X_v\to X_v^\vee$ |

Changing a row requires changing every dependent formula. In particular, normalized Satake operators would rescale (10.1), a left-coset convention would transpose the off-diagonal entries, and arithmetic rather than geometric Frobenius would invert unramified labels.

### 15.4 Exact scope

The theorem proves one-prime integral level change for the clean compact weight-two Shimura curves and their switched totally definite inner forms. It covers the full two-map Iwahori lattice, its special sign blocks when the roots separate, and selected type-enhanced variants satisfying the displayed extension and stabilizer hypotheses.

It does not cover Eisenstein maximal ideals, coefficient characteristic equal to the residue characteristic at $v$, noncompact boundary cohomology, $\ell$-divisible stabilizers, primitive wild types, or a projector defined only over the fraction field. It does not turn torsion-freeness into an integral old--new direct sum. It does not assert that the Néron component group vanishes.

At $q_v\equiv1\pmod\ell$, full-image saturation and Hecke-order comparison remain valid, but an ordered root needs extra data. At $q_v\equiv-1\pmod\ell$, the full Gram matrix remains valid, but its determinant does not measure one sign. At higher multiplicity, the full Smith module replaces one scalar congruence factor. At several primes, iteration is valid only while every intermediate clean hypothesis persists, or after a Tor-independent multi-prime complex has been proved.

These are theorem boundaries, not unfinished steps inside the proof.

## 16. Conclusion

### 16.1 The established package

The integral comparison now consists of three exact sequences and one equality of orders.

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

Each possible finite module has one source. The old quotient has no torsion. The Gram cokernel measures failure of orthogonal splitting and hence old--new congruence. The monodromy cokernel is the component group. There is no fourth module measuring an unexplained integral Jacquet--Langlands index.

### 16.2 The conceptual picture

One local edge controls the whole theory. Its two vertices give the two degeneracy maps. The arithmetic group acting on the local tree proves that every relation between them is Eisenstein. After non-Eisenstein localization the edge map is primitive, so its quotient is a genuine lattice even when the Gram determinant is a nonunit.

In the special fiber, the same edge becomes a node. The collection of nodes is the class set of the quaternion algebra obtained by ramifying at the changing finite place and at the formerly split real place. Cycles in the node graph are therefore definite automorphic forms with their natural integral scale. The edge-length pairing is simultaneously monodromy on the curve and the mass pairing on the definite class set.

Rational Jacquet--Langlands then performs one precise task: it proves that the graph packets and the curve-new packets have the same generic Hecke support. Torsion-freeness descends equality of generic kernels to equality of integral kernels. That short argument is what eliminates the otherwise possible congruence index between two orders in the same generic algebra.

Finally, the old Gram matrix converts a signed Hecke congruence into a nonzero new residual class. Saturation makes it lift from a free quotient, and the integral order comparison carries it across the inner form. In the opposite direction, the normalization and monodromy filtration show that a genuinely monodromy-free, component-clean residual new block must already occur at lower level. Integral level raising and lowering are thus two consequences of the same geometry, but not formal inverses: raising uses failure of unimodularity, while lowering uses vanishing of monodromy after every component obstruction has been exposed.

The resulting package is the required integral refinement of rational Jacquet--Langlands. It preserves the exact Hecke order, the primitive automorphic multiplicity lattice, the congruence ideal, the selected local sign and type, and the monodromy component module, with every exceptional case and normalization visible.
