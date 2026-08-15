# Integral Local Types and Type Lattices

## Contents

- [1. The integral local problem](#1-the-integral-local-problem)
  - [1.1 Why a rational type is not enough](#11-why-a-rational-type-is-not-enough)
  - [1.2 Standing notation and hypotheses](#12-standing-notation-and-hypotheses)
  - [1.3 The selected range](#13-the-selected-range)
  - [1.4 The route through the book](#14-the-route-through-the-book)
- [2. Inertial data and compact types](#2-inertial-data-and-compact-types)
  - [2.1 Weil--Deligne shapes](#21-weil--deligne-shapes)
  - [2.2 What a compact type must detect](#22-what-a-compact-type-must-detect)
  - [2.3 Principal, special, and dihedral labels](#23-principal-special-and-dihedral-labels)
  - [2.4 Twists, conductors, and central characters](#24-twists-conductors-and-central-characters)
- [3. Integral representation theory of finite level](#3-integral-representation-theory-of-finite-level)
  - [3.1 Stable lattices and the unit condition](#31-stable-lattices-and-the-unit-condition)
  - [3.2 Induction over a discrete valuation ring](#32-induction-over-a-discrete-valuation-ring)
  - [3.3 Dual lattices and companions](#33-dual-lattices-and-companions)
  - [3.4 Saturation and primitive multiplicity modules](#34-saturation-and-primitive-multiplicity-modules)
  - [3.5 Base change](#35-base-change)
- [4. Principal type lattices](#4-principal-type-lattices)
  - [4.1 The finite flag variety](#41-the-finite-flag-variety)
  - [4.2 Construction of the lattice](#42-construction-of-the-lattice)
  - [4.3 The type-detection theorem](#43-the-type-detection-theorem)
  - [4.4 Scalar and ordered boundary cases](#44-scalar-and-ordered-boundary-cases)
  - [4.5 Principal companions and pairings](#45-principal-companions-and-pairings)
- [5. Steinberg lattices and their companions](#5-steinberg-lattices-and-their-companions)
  - [5.1 Quotient and augmentation models](#51-quotient-and-augmentation-models)
  - [5.2 Perfect pairing without averaging](#52-perfect-pairing-without-averaging)
  - [5.3 Detection of special representations](#53-detection-of-special-representations)
  - [5.4 The first nonbanal phenomenon](#54-the-first-nonbanal-phenomenon)
- [6. Depth-zero dihedral type lattices](#6-depth-zero-dihedral-type-lattices)
  - [6.1 The nonsplit residue torus](#61-the-nonsplit-residue-torus)
  - [6.2 An integral cuspidal model](#62-an-integral-cuspidal-model)
  - [6.3 Inflation, compact induction, and detection](#63-inflation-compact-induction-and-detection)
  - [6.4 Duality and conjugation](#64-duality-and-conjugation)
- [7. Positive-depth tame dihedral lattices](#7-positive-depth-tame-dihedral-lattices)
  - [7.1 Simple characters and the finite Heisenberg quotient](#71-simple-characters-and-the-finite-heisenberg-quotient)
  - [7.2 The integral Heisenberg representation](#72-the-integral-heisenberg-representation)
  - [7.3 Extension by the tame torus](#73-extension-by-the-tame-torus)
  - [7.4 Maximal compact types](#74-maximal-compact-types)
  - [7.5 The primitive-wild boundary](#75-the-primitive-wild-boundary)
- [8. Reduction of type lattices](#8-reduction-of-type-lattices)
  - [8.1 Reduction commutes with the constructions](#81-reduction-commutes-with-the-constructions)
  - [8.2 The banal theorem](#82-the-banal-theorem)
  - [8.3 Principal congruences](#83-principal-congruences)
  - [8.4 Steinberg reduction at divisors of $Q+1$](#84-steinberg-reduction-at-divisors-of-q1)
  - [8.5 Dihedral reduction and honest limitations](#85-dihedral-reduction-and-honest-limitations)
- [9. Type selection in integral modules](#9-type-selection-in-integral-modules)
  - [9.1 Multiplicity modules](#91-multiplicity-modules)
  - [9.2 Evaluation and saturation](#92-evaluation-and-saturation)
  - [9.3 Adjoint selection](#93-adjoint-selection)
  - [9.4 Why an idempotent can fail](#94-why-an-idempotent-can-fail)
  - [9.5 From a type lattice to a parahoric coefficient complex](#95-from-a-type-lattice-to-a-parahoric-coefficient-complex)
- [10. Ordered principal deformation conditions](#10-ordered-principal-deformation-conditions)
  - [10.1 Tame generators and framed objects](#101-tame-generators-and-framed-objects)
  - [10.2 The rigid prime-to-$\ell$ case](#102-the-rigid-prime-to-ell-case)
  - [10.3 Congruence-tame characters](#103-congruence-tame-characters)
  - [10.4 Generic components and conductor](#104-generic-components-and-conductor)
- [11. Special and Steinberg deformation conditions](#11-special-and-steinberg-deformation-conditions)
  - [11.1 The unipotent incidence equations](#111-the-unipotent-incidence-equations)
  - [11.2 The clean level-raising chart](#112-the-clean-level-raising-chart)
  - [11.3 Nonzero monodromy and the open Steinberg locus](#113-nonzero-monodromy-and-the-open-steinberg-locus)
  - [11.4 Signs and companion branches](#114-signs-and-companion-branches)
- [12. Dihedral and fixed finite-type deformation conditions](#12-dihedral-and-fixed-finite-type-deformation-conditions)
  - [12.1 Rigidity of prime-to-$\ell$ inertia](#121-rigidity-of-prime-to-ell-inertia)
  - [12.2 The dihedral Frobenius intertwiner](#122-the-dihedral-frobenius-intertwiner)
  - [12.3 Smoothness in the clean case](#123-smoothness-in-the-clean-case)
  - [12.4 Congruent and wild boundaries](#124-congruent-and-wild-boundaries)
- [13. The fixed nonminimal local datum](#13-the-fixed-nonminimal-local-datum)
  - [13.1 What the datum records](#131-what-the-datum-records)
  - [13.2 Separation from the coefficient prime](#132-separation-from-the-coefficient-prime)
  - [13.3 Compatibility of a type lattice with a deformation condition](#133-compatibility-of-a-type-lattice-with-a-deformation-condition)
  - [13.4 Change of coefficients and ground field](#134-change-of-coefficients-and-ground-field)
- [14. The integral local-type package](#14-the-integral-local-type-package)
  - [14.1 Main theorem](#141-main-theorem)
  - [14.2 Hypothesis and failure ledger](#142-hypothesis-and-failure-ledger)
  - [14.3 Conclusion](#143-conclusion)

## 1. The integral local problem

### 1.1 Why a rational type is not enough

The characteristic-zero representation theory of $\mathrm{GL}_2$ over a local field assigns a compact type to a principal series, a special representation, or a selected dihedral supercuspidal. For arithmetic applications this is only the first half of the local problem. One must choose a lattice in that finite-dimensional type, reduce it modulo a coefficient uniformizer, pair it with the correct adjoint lattice, and know which deformation condition the resulting local module represents.

These operations do not follow formally from the characteristic-zero type. Two lattices in the same vector space are commensurable, but their reductions can have different extension structures. An idempotent that projects to a characteristic-zero isotypic summand may contain the reciprocal of a finite group order; if the coefficient residue characteristic divides that order, the projector is not integral. A self-dual characteristic-zero representation can have two visibly different integral models, one naturally a quotient and the other naturally a submodule. The Steinberg representation of a finite projective line will give the basic example.

The purpose of this book is to supply the missing integral layer. We construct finite free lattices for the principal, Steinberg, depth-zero dihedral, and positive-depth tame dihedral types. For each lattice we construct its **companion**, meaning the adjoint lattice that participates in a perfect integral pairing. We determine what survives after coefficient reduction, including the nonsemisimple cases. Finally, we write the local deformation conditions at a fixed prime away from the coefficient characteristic as represented matrix-and-line problems and match their generic points with the types.

The word “integral” therefore has three simultaneous meanings:

1. matrices for the compact type preserve a finite free module over a coefficient DVR;
2. type selection is performed inside an integral ambient module, with saturation where necessary;
3. the corresponding Galois condition is imposed on representations over Artinian coefficient rings, not merely on characteristic-zero points.

Confusing any two of these meanings loses information. A type lattice does not by itself prove that an automorphic module contains the type. A generic inertial parameter does not choose an integral deformation component. A rational perfect pairing does not identify two integral lattices unless primitivity has been checked.

### 1.2 Standing notation and hypotheses

Let $F$ be a nonarchimedean local field with

$$
\mathcal O_F,\qquad \mathfrak p_F=(\varpi_F),\qquad
k_F=\mathcal O_F/\mathfrak p_F,\qquad |k_F|=Q,
$$

and residue characteristic $p$. Put

$$
G=\mathrm{GL}_2(F),\qquad K=\mathrm{GL}_2(\mathcal O_F),
$$

and let $I\subset K$ be the standard Iwahori, the inverse image of the upper triangular Borel $B(k_F)$. For $n\geq1$, write $K(n)=1+\mathfrak p_F^nM_2(\mathcal O_F)$.

Let $E$ be a finite extension of $\mathbf Q_\ell$, with ring of integers $R$, uniformizer $\lambda$, and residue field $\kappa$. The standing prime separation is

$$
\ell\ne p.
\tag{1.1}
$$

We enlarge $E$ when necessary so that all character values and finite-group representations under discussion are defined over it, and we assume that $\kappa$ is a splitting field for the relevant finite quotients whenever an irreducibility statement after reduction is made. A **lattice** in a finite-dimensional $E$-space is a finite free $R$-submodule spanning that space. Character values used in a lattice construction are required to lie in $R^\times$.

For deformation theory, $\bar\rho:G_F\to\mathrm{GL}_2(\kappa)$ is continuous, and $\delta:G_F\to R^\times$ is a fixed lift of $\det\bar\rho$. Coefficient algebras are complete local Noetherian $R$-algebras or their Artinian quotients, with residue field $\kappa$. A framed deformation comes with a basis lifting the fixed residual basis. The assumption $\ell>2$ will be stated whenever the determinant derivative or trace-zero adjoint representation is used.

We use arithmetic Frobenius in the tame presentation

$$
\phi t\phi^{-1}=t^Q.
\tag{1.2}
$$

Accordingly, a unipotent tame representation written $\rho(t)=1+N$ satisfies

$$
FNF^{-1}=QN,\qquad F=\rho(\phi).
\tag{1.3}
$$

This convention agrees with the conductor formulas of the preceding local representation theory after the usual inversion between arithmetic and geometric Frobenius. We never change convention inside an argument.

### 1.3 The selected range

The compact types treated here are exactly the types required at the fixed nonminimal prime:

- principal types arising from two finite characters of $\mathcal O_F^\times$, with the explicit deformation chart restricted to the tame conductor-one case;
- twists of the Steinberg type by a unit-valued smooth character;
- depth-zero dihedral types from a regular character of $k_{F_2}^\times$, where $F_2/F$ is unramified quadratic;
- positive-depth types from a tame quadratic admissible pair.

The positive-depth construction includes ramified quadratic extensions only when they are tame. In residue characteristic two this excludes ramified quadratic extensions. More generally, a primitive wild supercuspidal whose leading stratum is not produced by a quadratic field character is outside the theorem. This exclusion is structural: the Heisenberg group, its torus extension, and its intertwining calculation would require data not present in the selected pair.

At the coefficient prime, the relevant integral notion is different. When $\ell>2$ and the local field is absolutely unramified with perfect residue field, the established integral Fontaine--Laffaille equivalence identifies height-two strongly divisible objects of Hodge type $(0,1)$ with stable lattices all of whose finite quotients are finite flat **and whose attached divided filtered objects have that Hodge type**. We use that result only to keep the two local conditions in one coherent global datum. It does not construct a compact type at the coefficient prime, and the compact type lattices constructed here do not prove finite flatness.

### 1.4 The route through the book

Chapters 2 and 3 translate the characteristic-zero inertial dictionary into an integral design problem and prove the general lattice lemmas. Chapters 4 and 5 construct principal and Steinberg lattices directly from finite flag varieties. Chapters 6 and 7 treat the two dihedral constructions. Chapters 8 and 9 study reduction, companions, multiplicity modules, and saturation.

The final movement passes from compact representations to Galois deformations. Chapters 10--12 give explicit principal, special, and dihedral deformation conditions. Chapter 13 combines a chosen type lattice, its adjoint, its generic inertial label, and its named deformation component into the fixed nonminimal datum. Chapter 14 records the package and every boundary needed to reuse it safely.

## 2. Inertial data and compact types

### 2.1 Weil--Deligne shapes

The preceding local theory classifies the selected characteristic-zero representations by two-dimensional Weil--Deligne data. We recall only the part needed to define types. Let $(r,N)$ be a Frobenius-semisimple parameter over $E$, with finite inertia image. In the selected range it has one of three shapes:

$$
r=\chi_1\oplus\chi_2,\quad N=0;
\tag{2.1}
$$

$$
(r,N)=\operatorname{Sp}_2(\mu),\quad N\ne0;
\tag{2.2}
$$

or

$$
r=\operatorname{Ind}_{W_L}^{W_F}\xi,\quad N=0,
\tag{2.3}
$$

where $L/F$ is separable quadratic and $\xi\ne\xi^s$ for the nontrivial $s\in\operatorname{Gal}(L/F)$. The corresponding smooth irreducible representations are, respectively, an irreducible principal series, a twist of Steinberg, and a selected dihedral supercuspidal. At the reducibility wall the same semisimple pair of Weil characters also gives a one-dimensional determinant character when $N=0$; nonzero $N$ distinguishes Steinberg.

The **inertial label** is the restriction $r|_{I_F}$ together with the information of whether the selected component has $N=0$ or $N\ne0$ when the inertia restriction is scalar. An inertial semisimplification alone cannot make this distinction. Nor can it remember an ordering of two characters that become equal modulo $\lambda$.

The Artin conductor in the three cases is

$$
a(\chi_1\oplus\chi_2)=a(\chi_1)+a(\chi_2),
\tag{2.4}
$$

$$
a(\operatorname{Sp}_2(\mu))=
\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0,
\end{cases}
\tag{2.5}
$$

and

$$
a_F(\operatorname{Ind}_{W_L}^{W_F}\xi)
=f(L/F)\bigl(a_L(\xi)+d(L/F)\bigr).
\tag{2.6}
$$

These formulas have already been proved from newvectors and from Weil--Deligne conductors. We retain them because they show why the central character is not enough to determine level. In (2.4), two ramified characters can have unramified product. In (2.5), an unramified Steinberg twist has conductor one although its inertia semisimplification is trivial.

### 2.2 What a compact type must detect

A compact $K$-type is a finite-dimensional smooth representation $\sigma$ of $K$. In this book the phrase **$\sigma$ detects a selected class $\mathfrak C$** means that for every irreducible smooth characteristic-zero representation $\pi$ in the principal, special, or selected dihedral range,

$$
\operatorname{Hom}_K(\sigma,\pi)\ne0
\quad\Longleftrightarrow\quad
\pi\in\mathfrak C,
\tag{2.7}
$$

with any stated unramified-twist ambiguity included in the definition of $\mathfrak C$. The multiplicity is one for the minimal types constructed below.

For scalar inertia, replace bare occurrence in (2.7) by occurrence in the Iwahori-new quotient with a specified Hecke sign. The finite Steinberg $K$-lattice is part of that enhanced detector, but bare finite-Steinberg occurrence is deliberately not called detection.

There are two reasons to formulate (2.7) only in the selected range. First, the characteristic-zero classification used to prove the reverse implication constructs depth-zero and tame quadratic supercuspidals but deliberately gives no quadratic label to primitive wild supercuspidals. Second, a nonminimal compact subgroup can occur in representations beyond the intended class. Minimality and the exact intertwining group are what turn occurrence into detection.

The proof pattern will be the same in every family. Construction gives the forward implication. For the reverse implication, Frobenius reciprocity turns a nonzero $K$-map into an intertwiner of the inducing datum. The Bruhat calculation in the principal case, the two-orbit calculation in the Steinberg case, or the exact-intertwining theorem in the dihedral case recovers the label. Multiplicity one is the assertion that only the defining double coset contributes.

### 2.3 Principal, special, and dihedral labels

For a principal label choose finite smooth characters

$$
\theta_1,\theta_2:\mathcal O_F^\times\longrightarrow E^\times.
$$

The unordered pair gives the characteristic-zero inertial class. When deformation components or congruences are involved we retain the ordered pair. If $\theta_2\theta_1^{-1}$ has conductor $n\geq1$, the principal type is induced from $K_0(\mathfrak p_F^n)$; at $n=1$ this is the familiar finite induction from the Iwahori. If the characters are equal, the minimal compact type is the scalar $K$-character. At Iwahori level the permutation lattice also contains the finite Steinberg quotient, displaying the two sides of the monodromy boundary.

For a special label choose a smooth unit-valued character $\mu:F^\times\to E^\times$. Its compact information is $\mu|_{\mathcal O_F^\times}$, while $\mu(\varpi_F)$ records the unramified twist and the sign of a chosen Frobenius branch. The Steinberg type is the finite Steinberg representation of $\mathrm{GL}_2(k_F)$, inflated to $K$ and twisted by $\mu\circ\det$.

In the scalar case this $K$-representation is a coefficient model, not by itself an exact detector of monodromy: it also occurs in the $K(1)$-fixed part of an unramified principal series. Exact special detection uses the Iwahori-new quotient and its Hecke sign, as constructed in Section 5.3. Thus the special datum is an enhanced type rather than a bare irreducible $K$-representation.

For a dihedral Weil--Deligne label choose a tame admissible pair $(L/F,\xi)$. Admissibility means that $\xi$ does not factor through $N_{L/F}$; at positive depth its first noncentral term must generate $L$. Replacing $\xi$ by $\xi^s$ does not change the pair. The selected local correspondence uses the rectified compact character

$$
\vartheta=\xi\Delta_{L/F,\xi},
\tag{2.8}
$$

where the tame rectifier satisfies

$$
\Delta_{L/F,\xi}|_{F^\times}=\omega_{L/F},\qquad
\Delta_{L/F,\xi^{-1}}=\Delta_{L/F,\xi}^{-1}.
\tag{2.9}
$$

The type is constructed from $\vartheta$, while its Weil--Deligne label is $\operatorname{Ind}_{W_L}^{W_F}\xi$. This distinction is forced by determinants:

$$
\vartheta|_{F^\times}
=\xi|_{F^\times}\omega_{L/F}
=\det\operatorname{Ind}_{W_L}^{W_F}\xi.
\tag{2.10}
$$

A norm twist

$$
\xi\longmapsto\xi(\chi\circ N_{L/F})
\tag{2.11}
$$

corresponds to twisting the resulting $G$-representation by $\chi\circ\det$; the rectifier is unchanged under this operation. The compact type is built from $\vartheta$ on the residue torus at depth zero and from its simple character plus a finite Heisenberg representation at positive depth.

### 2.4 Twists, conductors, and central characters

Every integral construction must commute with unit-valued twists. If $\xi:F^\times\to R^\times$, then $\xi\circ\det$ is an $R$-valued character of $K$ and

$$
\sigma_R\longmapsto\sigma_R\otimes_R R(\xi\circ\det)
\tag{2.12}
$$

preserves finite freeness, duality, and reduction. Its companion is twisted by $\xi^{-1}\circ\det$.

The central character of a principal type is $(\theta_1\theta_2)|_{\mathcal O_F^\times}$. The central character of the Steinberg twist is $\mu^2|_{\mathcal O_F^\times}$. For the compact-mod-center extension of a dihedral type it is $\vartheta|_{F^\times}=\xi|_{F^\times}\omega_{L/F}$, exactly the determinant of the normalized Weil parameter; the $K$-type sees its restriction to $\mathcal O_F^\times$. These identities follow by evaluating scalar matrices in the inducing data. They are necessary compatibility tests but not complete invariants: principal labels $(\theta,\theta^{-1})$ all have trivial compact central character, and special and scalar types can share the same inertial central character.

## 3. Integral representation theory of finite level

### 3.1 Stable lattices and the unit condition

The first obstruction to a stable lattice is elementary and decisive.

**Lemma 3.1 (unit criterion).** Let $H$ be a group, let $V$ be a finite-dimensional $E$-representation, and let $h\in H$ act by a scalar $a\in E^\times$. If $V$ contains a nonzero finite $H$-stable $R$-lattice, then $a\in R^\times$.

**Proof.** Let $L$ be stable. Since $hL=L$, multiplication by $a$ and by $a^{-1}$ both preserve $L$. Taking determinants on the nonzero free module $L$ gives $a^{\operatorname{rank}L}\in R$ and $a^{-\operatorname{rank}L}\in R$. Hence $v_R(a)=0$. $\square$

Finite-order character values are units, so compact inertia data satisfy the criterion after enlarging $E$. An arbitrary unramified quasicharacter need not: its value on $\varpi_F$ can be a nonunit. This is why our compact lattices remember the unramified scalar only when it is unit valued.

For a finite group $H$, every $E$-representation has some $H$-stable lattice. Choose any lattice $L_0$ and set

$$
L=\sum_{h\in H}hL_0.
\tag{3.1}
$$

This is a finite $R$-module spanning $V$, is torsion free, and is therefore free over the DVR $R$. The explicit constructions below are stronger: they select a natural lattice and a natural companion rather than merely proving existence.

### 3.2 Induction over a discrete valuation ring

Let $J\subset H$ have finite index, and let $\Lambda$ be a finite free $R[J]$-module. Define

$$
\operatorname{Ind}_J^H\Lambda
=\{f:H\to\Lambda:f(jh)=j f(h)\}.
\tag{3.2}
$$

Choosing representatives for $J\backslash H$ identifies (3.2), as an $R$-module, with a direct sum of $[H:J]$ copies of $\Lambda$. Thus it is finite free, and for every $R$-algebra $A$ there is a canonical isomorphism

$$
(\operatorname{Ind}_J^H\Lambda)\otimes_RA
\simeq
\operatorname{Ind}_J^H(\Lambda\otimes_RA).
\tag{3.3}
$$

No flatness hypothesis on $A$ is needed, because both sides are described by the same finite direct sum and the same permutation-and-matrix action.

**Proposition 3.2 (integral Frobenius reciprocity).** If $M$ is an $R[H]$-module, then

$$
\operatorname{Hom}_{R[H]}(\operatorname{Ind}_J^H\Lambda,M)
\simeq
\operatorname{Hom}_{R[J]}(\Lambda,M).
\tag{3.4}
$$

**Proof.** Compose an $H$-map with the copy of $\Lambda$ consisting of functions supported on $J$; this gives the map from left to right. Conversely, from $u:\Lambda\to M$ define

$$
\widetilde u(f)=\sum_{x\in J\backslash H}x^{-1}u(f(x)).
$$

The covariance of $f$ makes the sum independent of representatives, and a change of variables proves $H$-equivariance. Evaluation and this construction are inverse. The formula uses a sum, not an average, so no group order is inverted. $\square$

### 3.3 Dual lattices and companions

For a finite free $R$-module $L$ put

$$
L^\#=\operatorname{Hom}_R(L,R),
\qquad (h\varphi)(x)=\varphi(h^{-1}x).
\tag{3.5}
$$

The evaluation pairing $L\times L^\#\to R$ is perfect and $H$-invariant. In this book $L^\#$ is the **companion lattice** unless a more concrete isomorphic model is specified. This definition prevents the common mistake of calling $L$ self-dual merely because $L_E$ is isomorphic to $L_E^\vee$.

Finite induction has a perfect companion pairing. If $\Lambda^\#$ is the dual $J$-lattice, set

$$
\langle f,g\rangle
=\sum_{x\in J\backslash H}\langle f(x),g(x)\rangle.
\tag{3.6}
$$

The two covariance laws cancel, so the sum is well defined. Right translation permutes the cosets, so it is invariant. In a set of coset representatives it is an orthogonal sum of perfect pairings, hence perfect. Consequently

$$
(\operatorname{Ind}_J^H\Lambda)^\#
\simeq\operatorname{Ind}_J^H(\Lambda^\#).
\tag{3.7}
$$

Again no denominator occurs.

### 3.4 Saturation and primitive multiplicity modules

Let $M$ be a finite free $R$-module and $W\subset M_E$ an $E$-subspace. The integral part that remembers $W$ without a scalar ambiguity is

$$
M\cap W.
$$

It is already saturated: if $0\ne a\in R$ and $am\in M\cap W$ for $m\in M$, then $m\in W$ because $W$ is an $E$-space. Thus $M/(M\cap W)$ is torsion free. Over a DVR both modules are free, and the inclusion is locally a direct summand.

More generally, if a preliminary construction produces $L_0\subset M$, define its saturation by

$$
L_0^{\mathrm{sat}}
=M\cap(E L_0)
=\{m\in M:\text{some }0\ne a\in R\text{ has }am\in L_0\}.
\tag{3.8}
$$

**Lemma 3.3 (primitive line).** If $EL_0$ is one-dimensional, then $L_0^{\mathrm{sat}}$ is a free rank-one direct summand of $M$. Any two primitive generators differ by an element of $R^\times$.

**Proof.** Saturation makes the quotient torsion free. A finite torsion-free module over a DVR is free, so the short exact sequence splits as $R$-modules. The saturated module has rank one. If $x$ and $y$ are primitive generators, write $y=ax$ in the common $E$-line. Both inclusions $Rx\subseteq Ry$ and $Ry\subseteq Rx$ force $a,a^{-1}\in R$, hence $a\in R^\times$. $\square$

This lemma is the correct replacement for dividing a chosen vector by an unspecified scalar after passing to $E$. It will normalize type multiplicity lines and comparison maps.

### 3.5 Base change

Let $R\to R'$ be a finite extension of coefficient DVRs. Every explicit lattice in this book satisfies

$$
\sigma_{R'}=\sigma_R\otimes_RR'.
\tag{3.9}
$$

Finite induction commutes with this operation by (3.3), and companions commute because finite free duality gives

$$
L^\#\otimes_RR'\simeq(L\otimes_RR')^\#.
\tag{3.10}
$$

Perfect pairings remain perfect. Saturation also behaves well under a flat DVR extension: put a saturated inclusion into Smith normal form. All nonzero elementary divisors are units; they remain units in $R'$. Thus the quotient stays torsion free and the base-changed inclusion is saturated.

Reduction $R\to\kappa$ is not flat, so invariants and saturated images need not commute with it. The explicit induced lattices still reduce by (3.3), but isotypic projectors and multiplicity dimensions require a separate analysis in Chapter 8.

## 4. Principal type lattices

### 4.1 The finite flag variety

Let $\theta_1,\theta_2:\mathcal O_F^\times\to R^\times$ be finite smooth characters, put

$$
\beta=\theta_2\theta_1^{-1},
$$

and suppose that $\beta$ has conductor $n\geq1$. Set

$$
J_n=K_0(\mathfrak p_F^n)
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K:c\in\mathfrak p_F^n
\right\}.
$$

Define

$$
\vartheta_{12,n}(g)
=\theta_1(\det g)\beta(d),
\qquad
g=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in J_n.
\tag{4.1}
$$

This is a homomorphism. Indeed, the lower-right entry of $gg'$ is
$dd'+cb'=dd'(1+cb'/(dd'))$, and the last factor belongs to
$1+\mathfrak p_F^n$, where $\beta$ is trivial. The determinant factor
is multiplicative. On a scalar $zI_2$ the value is
$\theta_1(z)^2\beta(z)=\theta_1(z)\theta_2(z)$, so the central
character is correct.

The coset space

$$
X_n=J_n\backslash K\simeq\mathbf P^1(\mathcal O_F/\mathfrak p_F^n)
$$

is finite of cardinality $Q^{n-1}(Q+1)$. At $n=1$, $J_1=I$, and if
the two characters are tame then (4.1) becomes

$$
\vartheta_{12,1}
\begin{pmatrix}a&b\\c&d\end{pmatrix}
=\theta_1(\bar a)\theta_2(\bar d).
$$

Thus the projective line over the residue field is the first member of
a finite flag tower. The higher levels are the actual compact opens
needed for general principal characters. The tame level $n=1$ is
singled out later only because its deformation equations can be written
using one tame generator.

### 4.2 Construction of the lattice

Define

$$
\sigma_R(\theta_1,\theta_2)
=\operatorname{Ind}_{J_n}^K R(\vartheta_{12,n}).
\tag{4.2}
$$

It is free of rank $Q^{n-1}(Q+1)$. Its generic fiber is the principal
$K$-type attached to the inertial pair. Its reduction is not an abstract
semisimplification but the concrete module

$$
\sigma_R(\theta_1,\theta_2)\otimes_R\kappa
\simeq
\operatorname{Ind}_{J_n}^K\kappa(\overline\vartheta_{12,n}).
\tag{4.3}
$$

At $n=1$ this is the inflation of
$\operatorname{Ind}_{B(k_F)}^{\mathrm{GL}_2(k_F)}(\bar\theta_1\boxtimes\bar\theta_2)$.
Formula (4.3) is valid whether
or not the right side is semisimple.

**Proposition 4.1.** The lattice (4.2) is stable, finite free, compatible with every coefficient change, and generated by any function supported on $J_n$ whose value at $1$ is $1$.

**Proof.** Stability is built into right translation on the induced model. Choose representatives of $J_n\backslash K$; evaluation on them identifies the lattice with $R^{Q^{n-1}(Q+1)}$. Formula (3.3) proves coefficient compatibility. The function supported on $J_n$ is carried by right translates to the analogous basis functions on all cosets, so it generates. $\square$

### 4.3 The type-detection theorem

Assume that $\theta_1\ne\theta_2$, and retain $n=a(\theta_2\theta_1^{-1})$. Let $\mathfrak C(\theta_1,\theta_2)$ be the inertial class of irreducible principal series $i_B^G(\chi_1\boxtimes\chi_2)$ with $\chi_i|_{\mathcal O_F^\times}=\theta_i$, allowing independent unramified changes of the two inducing characters.

**Theorem 4.2 (principal detection).** In the selected characteristic-zero range,

$$
\dim_E\operatorname{Hom}_K
(\sigma_E(\theta_1,\theta_2),\pi)=1
$$

for $\pi\in\mathfrak C(\theta_1,\theta_2)$, and the Hom space is zero for a selected irreducible representation with a different inertial label.

**Proof strategy.** Twist away $\theta_1$, identify the required
$J_n$-eigenline with the minimal newvector line, and then use the
double-coset stabilizer calculation to recover the ratio character.
Supercuspidal and special alternatives are excluded by their exact
minimal intertwining data.

**Proof.** Twist the principal series by $\chi_1^{-1}\circ\det$. Its
two inducing characters now have unit restrictions $1$ and
$\beta=\theta_2\theta_1^{-1}$. The conductor calculation for principal
series gives minimal level $n$, and the compact double-coset calculation
at $K_0(\mathfrak p_F^n)$ gives a unique line on which
$\begin{psmallmatrix}a&b\\c&d\end{psmallmatrix}$ acts by $\beta(d)$.
Twisting back changes this character to (4.1). Frobenius reciprocity
therefore gives a nonzero $K$-map from (4.2), and uniqueness of the
minimal line gives multiplicity one.

Conversely, a nonzero map supplies a $J_n$-eigenvector with character
(4.1). Twist away $\theta_1$ again. On the stabilizer of each compact
double coset, the lower-right unit groups occur with depths $j$ and
$n-j$. Compatibility with $\beta$ is possible at the minimal endpoint
only when the two inducing unit characters have ratio $\beta$; the Weyl
endpoint replaces $\beta$ by $\beta^{-1}$ and merely interchanges the
pair. This is the same stabilizer calculation that proves the
principal conductor and uniqueness of its newvector. A special
representation has scalar inertial semisimplification, while the exact
intertwining group of a selected dihedral type is its quadratic
compact-mod-center subgroup. Neither can contain this non-scalar
minimal principal character. The representation is therefore in the
asserted principal class, and the endpoint calculation again gives
multiplicity one. $\square$

The same exact-intertwining calculation applied to (4.2) itself gives
$\operatorname{End}_{E[K]}(\sigma_E)=E$: only the identity double
coset survives. Since the action factors through a finite quotient and
characteristic zero is semisimple, $\sigma_E$ is absolutely
irreducible after the standing coefficient enlargement.

The theorem concerns characteristic-zero occurrence. After reduction, the Hom space can grow because compact invariants cease to be exact. Chapter 8 records the safe replacement.

### 4.4 Scalar and ordered boundary cases

If $\theta_1=\theta_2=\theta$, the minimal principal type is the
rank-one character $R(\theta\circ\det)$. At Iwahori level, however,
the natural incidence lattice is

$$
\operatorname{Ind}_I^KR(\theta\circ\det)
\simeq R(\theta\circ\det)\otimes_R R[\mathbf P^1(k_F)].
\tag{4.4}
$$

The permutation module is reducible even in characteristic zero: constants form the scalar type, and the quotient is the finite Steinberg type. Thus the pair of equal inertia characters does not choose between $N=0$ and $N\ne0$. The correct integral construction retains the exact sequence rather than declaring (4.4) to be one irreducible type.

When $\theta_1\ne\theta_2$ but $\bar\theta_1=\bar\theta_2$, the characteristic-zero type is regular while its reduction lies on the scalar boundary. The ordered pair remains meaningful over $R$, even though inertia alone no longer splits the residual representation. This is the congruence-tame situation. An ordered pair of Frobenius-stable lines must be retained on the deformation side; averaging by the character group would divide by an $\ell$-power.

### 4.5 Principal companions and pairings

The companion of (4.2) is

$$
\sigma_R(\theta_1,\theta_2)^\#
\simeq\operatorname{Ind}_{J_n}^K
R(\vartheta_{12,n}^{-1}).
\tag{4.5}
$$

The right side is exactly the principal lattice attached to the
ordered inverse label $(\theta_1^{-1},\theta_2^{-1})$, because its
ratio character is $\beta^{-1}$. Weyl conjugation instead exchanges
the two entries; that is a separate symmetry of the generic inertial
class.

The pairing is the finite coset sum

$$
\langle f,g\rangle
=\sum_{x\in J_n\backslash K}f(x)g(x).
\tag{4.6}
$$

It is perfect by (3.6). The Weyl conjugate $\sigma_R(\theta_2,\theta_1)$ is a different notion: over $E$ it is isomorphic to the primary type when the pair is regular, but it is not the adjoint unless the characters satisfy the corresponding inverse relation. We reserve **companion** for (4.5), because adjunction in a global pairing requires inversion, not merely Weyl interchange.

If a central character $\omega$ is fixed and $\theta_1\theta_2=\omega|_{\mathcal O_F^\times}$, then the companion naturally has central character $\omega^{-1}$. A pairing valued in a rank-one character module can twist this back to $\omega$; the twist must be written explicitly. No self-duality is inferred from equality of generic inertial multisets.

## 5. Steinberg lattices and their companions

### 5.1 Quotient and augmentation models

The Steinberg type is where characteristic-zero self-duality first separates into two integral models. Let

$$
X=\mathbf P^1(k_F),\qquad P_R=R[X],\qquad
\mathbf 1_X=\sum_{x\in X}[x].
$$

The finite group $\mathrm{GL}_2(k_F)$ acts by permuting $X$. Define the **quotient Steinberg lattice**

$$
\operatorname{St}_R^+=P_R/R\mathbf1_X
\tag{5.1}
$$

and the **augmentation Steinberg lattice**

$$
\operatorname{St}_R^-
=\ker\left(\varepsilon:P_R\longrightarrow R,
\ \sum a_x[x]\longmapsto\sum a_x\right).
\tag{5.2}
$$

Both are free of rank $Q$. Indeed $\mathbf1_X$ is primitive in $P_R$, so the quotient in (5.1) is free; the augmentation map is split as an $R$-module map by any basis vector. Their generic fibers are both the irreducible finite Steinberg representation.

Inflate these lattices to $K$. For a unit-valued smooth character $\mu:F^\times\to R^\times$, put

$$
\sigma_{\mathrm{St},R}^+(\mu)
=\operatorname{St}_R^+\otimes_RR(\mu\circ\det),
\tag{5.3}
$$

$$
\sigma_{\mathrm{St},R}^-(\mu^{-1})
=\operatorname{St}_R^-\otimes_RR(\mu^{-1}\circ\det).
\tag{5.4}
$$

The character may have higher conductor; then its determinant twist factors through a correspondingly deeper finite quotient of $K$. The projective-line factor remains unchanged.

### 5.2 Perfect pairing without averaging

Put the standard dot product on $P_R$:

$$
(\sum a_x[x],\sum b_x[x])=\sum_xa_xb_x.
\tag{5.5}
$$

Every vector in $\operatorname{St}_R^-$ is orthogonal to $\mathbf1_X$, so (5.5) descends to

$$
\operatorname{St}_R^+\times\operatorname{St}_R^-
\longrightarrow R.
\tag{5.6}
$$

**Proposition 5.1.** Pairing (5.6) is $\mathrm{GL}_2(k_F)$-invariant and perfect. Consequently

$$
(\operatorname{St}_R^+)^\#\simeq\operatorname{St}_R^-,
\qquad
(\sigma_{\mathrm{St},R}^+(\mu))^\#
\simeq\sigma_{\mathrm{St},R}^-(\mu^{-1}).
\tag{5.7}
$$

**Proof.** Permutations preserve the dot product, giving invariance. Dualizing

$$
0\longrightarrow R\mathbf1_X\longrightarrow P_R
\longrightarrow\operatorname{St}_R^+\longrightarrow0
$$

identifies $(\operatorname{St}_R^+)^\#$ with the functionals on $P_R$ vanishing on $\mathbf1_X$. Under the basis identification $P_R\simeq P_R^\#$, those are exactly the augmentation-zero vectors. Thus (5.6) identifies each lattice with the full dual of the other. Twisting gives the second assertion. $\square$

There is deliberately no factor $(Q+1)^{-1}$ in (5.6). Averaging would obscure the integral distinction precisely when $\ell\mid Q+1$.

### 5.3 Detection of special representations

Let $K'$ be the stabilizer of the vertex adjacent to the standard vertex across the edge stabilized by $I$. Thus

$$
I=K\cap K'.
$$

For a smooth representation $V$, the two inclusions of vertex invariants define the old subspace

$$
V^{I}_{\mathrm{old}}=V^K+V^{K'}\subseteq V^I,
$$

and the **Iwahori-new quotient** is

$$
V^I_{\mathrm{new}}=V^I/V^I_{\mathrm{old}}.
\tag{5.8}
$$

After a ramified scalar twist, the same definition uses the corresponding character eigenspaces rather than literal invariants. Integrally, the old image is saturated before the quotient is formed. Its adjoint construction uses the two opposite vertex maps and the companion lattice.

Let $\pi=\operatorname{St}_G\otimes(\mu\circ\det)$, where $\operatorname{St}_G$ is the smooth Steinberg representation of $G$. Its restriction to $K$ contains the inflation of the finite Steinberg representation with multiplicity one, but that occurrence alone is not exclusive to $\pi$.

**Theorem 5.2 (enhanced special detection).** In the selected characteristic-zero range with scalar compact character $\mu|_{\mathcal O_F^\times}$, one has

$$
\dim_E\pi^I_{\mathrm{new}}=1
\tag{5.9}
$$

for a special twist, while the corresponding twisted Iwahori-new quotient is zero for a determinant character, an irreducible principal series with the same scalar inertia, and every selected dihedral supercuspidal. Consequently the nonzero new line, together with its Hecke eigenvalue, detects the special twist and its unramified sign.

**Proof strategy.** Compute invariants at the two vertices and their common edge in the Bruhat tree. The old vertex lines fill the edge space for an unramified principal series, whereas Steinberg has an edge line and no vertex line.

**Proof.** The projective-line model of $\operatorname{St}_G$ has no $K$-fixed vector: a $K$-invariant locally constant function on $\mathbf P^1(F)$ is constant, hence zero modulo constants. It has a one-dimensional $I$-fixed space because $I$ has two orbits and quotienting by constants removes one dimension. The same statements hold for $K'$. Therefore its old subspace is zero and (5.9) follows.

A determinant character has one-dimensional invariant spaces at both vertices and at the edge, so the edge line is old. After twisting away $\mu\circ\det$, an irreducible principal series in this scalar inertial class is unramified and has a two-dimensional $I$-fixed space. Its $K$-fixed and $K'$-fixed lines are distinct: if they coincided, the vector would be fixed by the group generated by the adjacent vertex stabilizers, hence by $G$ modulo its center, forcing a one-dimensional constituent. The two lines therefore span $V^I$, and the new quotient vanishes.

A selected dihedral supercuspidal has no such twisted Iwahori eigenspace. Indeed a nonzero eigenspace, after the same determinant twist, would give a nonzero module for the Iwahori Hecke algebra and hence a subquotient generated from the Borel, whereas the exact compact-induction calculation for the selected dihedral type gives zero Jacquet module. Thus the new quotient is zero there as well.

The finite Steinberg $K$-type occurs in the $K(1)$-fixed module of that principal series, so bare occurrence would not prove the theorem. Newness removes exactly this old occurrence. On the surviving special line the Iwahori Hecke algebra acts through its sign character; the remaining normalized operator records $\mu(\varpi_F)$. This recovers the special twist up to precisely the recorded branch. $\square$

The phrase “enhanced type” refers to this new quotient and sign together with the quotient/augmentation coefficient lattices. It is this package, not bare finite-Steinberg occurrence, that matches nonzero monodromy.

### 5.4 The first nonbanal phenomenon

Reduction gives

$$
\overline{\operatorname{St}}^+
=\kappa[X]/\kappa\mathbf1_X,
\qquad
\overline{\operatorname{St}}^-
=\ker(\varepsilon:\kappa[X]\to\kappa).
\tag{5.10}
$$

If $\ell\nmid Q+1$, then

$$
\kappa[X]=\kappa\mathbf1_X\oplus\ker\varepsilon,
$$

and the two reductions are canonically isomorphic after multiplying by $(Q+1)^{-1}$. If $\ell\mid Q+1$, then $\mathbf1_X\in\ker\varepsilon$. Hence $\overline{\operatorname{St}}^-$ contains a trivial submodule, while the augmentation descends to a trivial quotient of $\overline{\operatorname{St}}^+$. The companion pairing remains perfect, but the two lattices have opposite extension orientations.

This example proves three general lessons. Generic self-duality need not give integral self-duality. Reduction of a type need not be irreducible. The correct adjoint object can be retained even when semisimplicity fails, because perfect duality is stronger and more stable than a decomposition into constituents.

## 6. Depth-zero dihedral type lattices

### 6.1 The nonsplit residue torus

Let $F_2/F$ be the unramified quadratic extension. Its residue field is $k_2$ with $|k_2|=Q^2$. Let $(F_2/F,\xi)$ be a depth-zero Weil--Deligne pair and put $\vartheta=\xi\Delta_{F_2/F,\xi}$. The rectifier is unramified here, so $\xi$ and $\vartheta$ have the same restriction to $\mathcal O_{F_2}^\times$. Choose an embedding

$$
k_2^\times\hookrightarrow\mathrm{GL}_2(k_F)
$$

through multiplication on the two-dimensional $k_F$-space $k_2$. A character

$$
\eta:k_2^\times\to R^\times
$$

is obtained from $\vartheta|_{\mathcal O_{F_2}^\times}$ and is **regular** when $\eta^Q\ne\eta$. Equivalently, it does not factor through the norm $k_2^\times\to k_F^\times$. The pair $\{\eta,\eta^Q\}$ is intrinsic; changing the $k_F$-basis conjugates the torus, and the nontrivial Galois automorphism exchanges the two characters.

The finite cuspidal representation $\rho_E(\eta)$ of $\mathrm{GL}_2(k_F)$ has dimension $Q-1$. The preceding local theory constructs it by a finite Deligne--Lusztig-style function model and proves

$$
\rho_E(\eta)\simeq\rho_E(\eta^Q),
\tag{6.1}
$$

with no other identifications among regular labels. We now isolate an integral model without importing any semisimplicity after reduction.

### 6.2 An integral cuspidal model

The preceding finite-field construction realizes the cuspidal representation as a minimal left ideal in the primitive block cut out by its explicit character table. We do not form a quotient of torus-induced functions by an orbit-sum relation; that tempting model has the wrong dimension. Choose an $E$-basis of the resulting minimal left ideal and let $L_0$ be its $R$-span. Define the orbit lattice

$$
\rho_R(\eta)
=\sum_{g\in\mathrm{GL}_2(k_F)}gL_0
\subset\rho_E(\eta).
\tag{6.2}
$$

It is finite, stable, and spans the cuspidal representation. It is torsion free as a submodule of an $E$-space, hence finite free over $R$. This construction does not divide by the order of the nonsplit torus; it therefore remains valid when $\ell$ divides $Q-1$ or $Q+1$. The choice is not claimed canonical. Its dual, however, is a definite companion once the primary lattice is fixed.

**Theorem 6.1 (integral depth-zero seed).** The module $\rho_R^+(\eta):=\rho_R(\eta)$ is a finite free $R[\mathrm{GL}_2(k_F)]$-lattice of rank $Q-1$ and spans $\rho_E(\eta)$. Once this primary lattice is chosen, define its inverse-label companion by

$$
\rho_R^-(\eta^{-1})=\rho_R^+(\eta)^\#.
\tag{6.3}
$$

Both lattices have explicit coefficient extensions and reductions, and evaluation pairs them perfectly.

**Proof.** Stability, finite freeness, and the generic fiber were proved in the orbit-lattice construction; the rank is the characteristic-zero dimension. Tensoring its chosen finite free action matrices defines its coefficient extension and reduction. This is a base-change convention for the chosen lattice, not a claim that repeating the noncanonical orbit construction over a larger coefficient field selects the same lattice.

The finite cuspidal character table shows that the contragredient of $\rho_E(\eta)$ is $\rho_E(\eta^{-1})$. Thus the generic fiber of the dual in (6.3) has the asserted inverse label, and evaluation is a perfect invariant pairing by construction. If an independently chosen orbit lattice is used for the inverse label, it is merely commensurable with $\rho_R^-(\eta^{-1})$; no integral isomorphism is asserted without an additional unit-index calculation. $\square$

The proof does not say that $\rho_R(\eta)\otimes\kappa$ is irreducible. That assertion requires a banality hypothesis recorded later.

### 6.3 Inflation, compact induction, and detection

Inflate $\rho_R^+(\eta)$ through $K\twoheadrightarrow\mathrm{GL}_2(k_F)$ and write

$$
\sigma_{0,R}^+(\eta)=\operatorname{Inf}\rho_R^+(\eta).
\tag{6.4}
$$

Extend the corresponding depth-zero inducing representation from $K$ to $F^\times K$ using the central character $\vartheta|_{F^\times}$, including the unramified rectifier value, and compactly induce to $G$. The resulting generic representation has normalized parameter $\operatorname{Ind}_{W_{F_2}}^{W_F}\xi$.

**Theorem 6.2 (depth-zero detection).** Among selected characteristic-zero irreducibles, $\sigma_{0,E}(\eta)$ occurs precisely in the unramified depth-zero dihedral class whose rectified compact character restricts on the residue torus to $\{\eta,\eta^Q\}$, and it occurs with multiplicity one. With the central extension just fixed, its normalized Weil--Deligne label is $\operatorname{Ind}_{W_{F_2}}^{W_F}\xi$.

**Proof.** Construction gives a nonzero map from the inflated finite cuspidal representation into the compact induction. By Frobenius reciprocity, its self-intertwining contributions are indexed by double cosets of $F^\times K$ in $G$. The depth-zero intertwining theorem says that a nonzero contribution forces the two associated vertices in the lattice tree to coincide; hence only the identity coset contributes. Within $K$, the finite cuspidal character table recovers the regular torus orbit $\{\eta,\eta^Q\}$. This proves multiplicity one and uniqueness of the label.

A principal or special representation has nonzero Jacquet module, whereas the finite cuspidal seed has vanishing finite unipotent coinvariants. Thus it cannot occur in those families. Exact intertwining for the positive-depth types separates them by depth. $\square$

### 6.4 Duality and conjugation

Equations (6.1) and (6.3) give, on the specified integral models,

$$
\sigma_{0,R}^+(\eta)^\#
=\sigma_{0,R}^-(\eta^{-1}).
\tag{6.5}
$$

The generic inverse label is also represented by $\eta^{-Q}$. A self-dual generic fiber occurs when $\eta^{-1}$ belongs to the orbit $\{\eta,\eta^Q\}$. Even then the primary lattice is not identified with its companion unless an integral intertwiner has unit determinant. Evaluation identifies the specified companion with the full dual; an independently chosen self-dual orbit lattice may differ by a genuine integral index.

## 7. Positive-depth tame dihedral lattices

### 7.1 Simple characters and the finite Heisenberg quotient

Let $L/F$ be tame quadratic and embedded in $A=M_2(F)$. Let $\xi:L^\times\to E^\times$ be a minimal positive-depth Weil--Deligne character and put

$$
\vartheta=\xi\Delta_{L/F,\xi}.
$$

We assume that the compact values of $\vartheta$ lie in $R^\times$; an unramified norm twist, invisible to the compact type, may be used to arrange the chosen normalization. The lattice chain $\mathfrak p_L^i$ determines hereditary orders $\mathfrak A\supset\mathfrak P$ in $A$ and compact groups

$$
H^1\subset J^1\subset J^0\subset K
$$

after conjugating the chain into standard position. The preceding tame type construction attaches to the first noncentral term of the rectified character $\vartheta$ a simple character

$$
\psi_\beta:H^1\longrightarrow R^\times.
\tag{7.1}
$$

The quotient $J^1/H^1$ is a finite $p$-group equipped with the alternating commutator form

$$
(\bar x,\bar y)\longmapsto
\psi_\beta([x,y]).
\tag{7.2}
$$

After dividing by its radical, this form is nondegenerate. The corresponding central extension is a finite Heisenberg group. Its unique irreducible representation with central character $\psi_\beta$ is the finite-dimensional core of the positive-depth type.

Tameness enters twice. It makes the leading centralizer exactly $L$, and it gives the exact intertwining group $L^\times J^1$. A primitive wild stratum can fail both assertions.

### 7.2 The integral Heisenberg representation

Choose a maximal isotropic subgroup $U/H^1$ of $J^1/H^1$ and extend $\psi_\beta$ to $U$. Define

$$
\eta_R=\operatorname{Ind}_U^{J^1}R(\widetilde\psi_\beta).
\tag{7.3}
$$

This is finite free. Its generic fiber is the irreducible Heisenberg representation by the Stone--von Neumann argument: any irreducible with the given central character contains a character of $U$, conjugation moves these characters transitively, and dimension comparison forces (7.3).

**Proposition 7.1.** The lattice $\eta_R$ is independent of the chosen maximal isotropic subgroup up to $J^1$-equivariant isomorphism after primitive normalization. It has companion $\eta_R(\psi_\beta^{-1})$, and its reduction is the corresponding induced module over $\kappa$.

**Proof.** Two polarizations give two induced models of the same generic irreducible. The finite Fourier intertwiner between them is a sum over a $p$-group. Its composite with the reverse intertwiner is multiplication by a power of $p$. Since $p\in R^\times$, rescaling by a unit makes the map an integral isomorphism. The coset-sum pairing (3.6) identifies the dual with the model having inverse central character. Reduction commutes with finite induction by (3.3). $\square$

The assertion would be false with no prime separation: in residue characteristic $p$ the Fourier scalar is not a unit and the Heisenberg representation has a different modular theory.

### 7.3 Extension by the tame torus

The group $J^0/J^1$ is a finite toric group of order prime to $p$. The rectified character $\vartheta$ prescribes its action and the action of $L^\times\cap J^0$. Over $E$, the Heisenberg representation extends to a representation $\Lambda_E(\vartheta)$ of $J^0$. Initially the extension operators are determined only up to scalars.

**Lemma 7.2 (integral torus extension).** After a finite extension of $E$, the extension operators can be scaled so that they preserve a finite free lattice $\Lambda_R^+(\vartheta)$ containing $\eta_R$. Any two primitive stable choices are commensurable, and their saturated intertwining line is unique up to $R^\times$.

**Proof.** The quotient $J^0/J^1$ is finite. Start with the lattice generated by the orbit of $\eta_R$ under representatives of that finite quotient and their inverses. It is finite, stable, and spans $\Lambda_E(\vartheta)$; unit-valued central scalars do not enlarge it by denominators. As a torsion-free finite module inside an $E$-space, it is free over $R$.

If $\Lambda$ and $\Lambda'$ are two choices, their common generic identity is a one-dimensional intertwining space by exact intertwining of the tame type. Intersect that line with $\operatorname{Hom}_R(\Lambda,\Lambda')$ and saturate. Lemma 3.3 gives a primitive map unique up to a unit. $\square$

The construction retains the extension class selected by the rectified tame-pair normalization. At positive depth it is not legitimate to specify only $\xi$ on the Weil torus and suppress either the rectifier or the projective extension ambiguity.

### 7.4 Maximal compact types

Define the positive-depth $K$-type

$$
\sigma_R^+(L,\xi)
=\operatorname{Ind}_{J^0}^{K}\Lambda_R^+(\vartheta).
\tag{7.4}
$$

It is finite free because $J^0$ has finite index in $K$. Define its companion to be

$$
\sigma_R^-(L,\xi^{-1})
=\sigma_R^+(L,\xi)^\#.
\tag{7.5}
$$

Its generic label is $\xi^{-1}$ because $\Delta_{L/F,\xi^{-1}}=\Delta_{L/F,\xi}^{-1}$, so the inverse rectified character is $\vartheta^{-1}$. The perfect pairing is again a finite coset sum. An independently chosen primary lattice for $\xi^{-1}$ is not silently identified with this companion.

This also constructs the type for a nonminimal positive-depth admissible pair. The minimal-twist theorem supplies

$$
\xi=\xi_0(\chi\circ N_{L/F})
$$

with $\xi_0$ minimal. Use (7.4) when $\xi_0$ still has positive depth, and use the inflated depth-zero seed of Chapter 6 when $L/F$ is unramified and $\xi_0$ has depth zero. Denote either chosen minimal primary lattice by $\sigma_R^+(L,\xi_0)$. Since the rectifier is unchanged by a norm twist, put

$$
\sigma_R^+(L,\xi)
=\sigma_R^+(L,\xi_0)\otimes_RR(\chi\circ\det|_K),
\tag{7.6}
$$

after enlarging coefficients so that the compact values of $\chi$ are units. The unramified value of $\chi$ belongs only to the compact-mod-center extension. Define the companion by duality, so it is the twist of the $\xi_0^{-1}$ companion by $\chi^{-1}\circ\det$. A different minimal-twist decomposition gives the same generic type by the tame equivalence theorem, but it need not select the identical integral lattice. The chosen decomposition is therefore part of the primary-lattice convention; the resulting choices are commensurable, and the specified dual remains exact.

**Theorem 7.3 (positive-depth detection).** In the selected characteristic-zero range, $\sigma_E^+(L,\xi)$ occurs with multiplicity one precisely in the tame dihedral inertial class with normalized Weil--Deligne label $(L,\xi)$, modulo Galois conjugation and unramified norm twist.

**Proof strategy.** Reduce occurrence to intertwining of $\Lambda_E(\vartheta)$ and use the leading simple character to recover the quadratic centralizer.

**Proof.** Assume first that $\xi$ is minimal. Occurrence in the compact induction attached to the direct pair $(L,\vartheta)$ is immediate from Frobenius reciprocity. Mackey decomposition expresses its multiplicity as a sum over $J^0\backslash K/J^0$ of intertwining spaces. Exact intertwining of the simple character forces an intertwiner to normalize the quadratic lattice chain and then to lie in $J^0$ after the allowed torus action has been accounted for. Thus only the identity double coset contributes and the multiplicity is one.

Conversely, occurrence in a selected irreducible supplies an intertwiner of the simple character. Its commutator pairing recovers the centralizer $L$, and its torus action recovers $\{\vartheta,\vartheta^s\}$ up to a norm character trivial on the compact part. Undoing the uniquely normalized tame rectifier recovers $\{\xi,\xi^s\}$ with the same ambiguity. The selected correspondence then identifies the normalized parameter as $\operatorname{Ind}_{W_L}^{W_F}\xi$.

For a nonminimal pair, twist (7.6) and the candidate representation by $\chi^{-1}\circ\det$. The minimal case applies to $\xi_0$, and twisting back preserves both occurrence multiplicity and the stated inertial ambiguity. $\square$

### 7.5 The primitive-wild boundary

Nothing in the preceding proof classifies primitive wild types. For such a representation, the first noncentral stratum need not have a quadratic field as centralizer. Even when a wild quadratic field occurs in residue characteristic two, the lattice-chain jumps and extension operators depend on the different and on additional choices. The finite Heisenberg quotient may still exist, but formulas (7.1)--(7.6) are not determined by a tame admissible pair.

It follows that this book makes no integral reduction, companion, multiplicity, or deformation-component claim for primitive wild supercuspidals. An abstract stable lattice exists in any finite-dimensional compact type, but existence alone does not supply the label, the perfect comparison, or the exact local deformation condition required here.

## 8. Reduction of type lattices

### 8.1 Reduction commutes with the constructions

Every primary and companion lattice constructed above is finite free. Therefore its perfect pairing remains perfect after reduction. Explicit finite induction gives

$$
(\operatorname{Ind}_J^H\Lambda_R)\otimes_R\kappa
\simeq
\operatorname{Ind}_J^H(\Lambda_R\otimes_R\kappa),
\tag{8.1}
$$

and finite free duality gives

$$
L^\#\otimes_R\kappa\simeq(L\otimes_R\kappa)^\#.
\tag{8.2}
$$

Thus reduction never destroys the integral object or its adjoint. What can fail is irreducibility, exactness of invariants, or constancy of a multiplicity.

The distinction is important. The phrase “the type reduces” means the left sides of (8.1)--(8.2) exist and retain their action and pairing. It does not mean that their Jordan--Hölder factors determine a unique characteristic-zero type.

### 8.2 The banal theorem

Let $\Gamma$ be a finite quotient through which a type and the relevant compact action factor. Call $\ell$ **banal for this datum** when

$$
\ell\nmid|\Gamma|
\tag{8.3}
$$

and the residue field is splitting for $\Gamma$.

**Theorem 8.1 (banal reduction).** Under (8.3), reduction is semisimple, invariants commute with arbitrary coefficient change, and an absolutely irreducible characteristic-zero type lattice reduces to an absolutely irreducible $\kappa$-representation with the corresponding reduced character.

**Proof.** The averaging operator

$$
e_H=|H|^{-1}\sum_{h\in H}h
$$

is defined over $R$ for every subgroup $H\subset\Gamma$. It is an idempotent whose image is the invariant module, so invariants commute with tensor products. Maschke's argument makes both $E[\Gamma]$ and $\kappa[\Gamma]$ semisimple.

For the last assertion, let $L$ be a stable lattice in an absolutely irreducible $E$-representation $V$. The reduction $L/\lambda L$ is semisimple. Its Brauer character on every element of $\Gamma$ is the reduction of the ordinary character of $V$, because every element has order prime to $\ell$ and its eigenvalues are roots of unity in $R^\times$. Over splitting fields with $\ell\nmid|\Gamma|$, the ordinary and Brauer irreducible-character tables coincide under this reduction. Linear independence of irreducible characters therefore forces $L/\lambda L$ to have exactly the one irreducible constituent corresponding to $V$, with multiplicity one. Hence it is absolutely irreducible. $\square$

This theorem is deliberately datum dependent. The order of a convenient large quotient can contain irrelevant factors, while a smaller quotient controlling a particular type may still be banal. Conversely, $\ell\ne p$ alone is not enough: $\ell$ may divide $Q-1$ or $Q+1$.

### 8.3 Principal congruences

Formula (4.3) gives the complete safe statement for principal reduction at every conductor: it is the explicit induction from $J_n$ and no semisimplicity is implicit. Under banality it is irreducible. In the tame level-one congruence case $\bar\theta_1=\bar\theta_2=\bar\theta$, it specializes to

$$
0\longrightarrow
\kappa(\bar\theta\circ\det)
\longrightarrow
\overline\sigma(\theta_1,\theta_2)
\longrightarrow
\overline{\operatorname{St}}^+
\otimes\kappa(\bar\theta\circ\det)
\longrightarrow0.
\tag{8.4}
$$

Here the middle term depends only on the reduced characters as a $K$-module, even though the two distinct lifts determine different characteristic-zero components. Sequence (8.4) is the reduction of the level-one permutation-module sequence and is exact because its integral quotient is free. At higher conductor one retains (4.3); there is no assertion that its modular extension structure is still a two-step scalar--Steinberg sequence.

The extension in (8.4) need not split. It splits when $Q+1$ is a unit in $\kappa$ by projecting onto constants with normalized averaging. When $\ell\mid Q+1$, such a projection is unavailable. Thus a congruent principal type must be selected by its lattice or by an enhanced line condition, not by the semisimplified reduction alone.

### 8.4 Steinberg reduction at divisors of $Q+1$

The calculation of Section 5.4 can be sharpened into exact sequences. If $\ell\mid Q+1$, constants lie in the augmentation kernel, giving

$$
0\longrightarrow\kappa
\longrightarrow\overline{\operatorname{St}}^-
\longrightarrow C\longrightarrow0,
\tag{8.5}
$$

while augmentation descends through the quotient by constants, giving

$$
0\longrightarrow C^\#
\longrightarrow\overline{\operatorname{St}}^+
\longrightarrow\kappa\longrightarrow0.
\tag{8.6}
$$

The unnamed middle constituent $C$ need not be described to see the essential orientation: (8.5) has a trivial submodule and (8.6) a trivial quotient, and perfect duality identifies the two sequences. Their semisimplifications agree, but their extension classes point in opposite directions.

This is precisely why the primary Steinberg lattice and its companion must both be carried through an integral pairing. Replacing both by one rational Steinberg space loses the information that controls adjoint degeneracy maps.

### 8.5 Dihedral reduction and honest limitations

For depth-zero and positive-depth dihedral types, reduction commutes with every finite induction and with the Heisenberg construction. Under banality, Theorem 8.1 preserves irreducibility. If a finite free ambient module also factors through the same banal quotient, the invariant-projector argument makes Hom commute with reduction, so a characteristic-zero multiplicity-one line reduces to a multiplicity-one line. Outside banality the reduced type can acquire additional subquotients or self-extensions, especially when $\ell$ divides a torus order or a normalizer index.

Two robust facts remain:

1. the primary and inverse-label companion are finite free and perfectly paired after reduction;
2. their reduced actions are the explicit reductions of the same inducing data.

No general irreducibility assertion is made in the nonbanal case. Nor do we infer that a mod-$\lambda$ constituent remembers whether its lift was principal or dihedral. Congruences between different characteristic-zero types are exactly what integral level change is designed to detect.

## 9. Type selection in integral modules

### 9.1 Multiplicity modules

Let $M$ be a finite free $R$-module with an action of a compact group $K$ factoring through a finite quotient at the level under consideration, and let $\sigma_R$ be a finite free type lattice. Define the primary multiplicity module

$$
\mathcal M_\sigma(M)=\operatorname{Hom}_{R[K]}(\sigma_R,M)
\tag{9.1}
$$

and the adjoint multiplicity module

$$
\mathcal M_{\sigma^\#}(M^\#)
=\operatorname{Hom}_{R[K]}(\sigma_R^\#,M^\#).
\tag{9.2}
$$

Over $E$, characteristic-zero multiplicity one often makes (9.1) a line. Integrally it can be a fractional line inside that $E$-space, and after reduction its dimension can jump. The lattice itself, rather than the dimension of its special fiber, is the stable object.

If $M$ carries a perfect $K$-invariant pairing with another lattice $M'$, composition gives

$$
\mathcal M_\sigma(M)\times
\mathcal M_{\sigma^\#}(M')\longrightarrow R.
\tag{9.3}
$$

Explicitly, for $f:\sigma_R\to M$ and $g:\sigma_R^\#\to M'$, choose a basis $e_i$ of $\sigma_R$ with dual basis $e_i^\#$ and set

$$
\langle f,g\rangle_{\mathrm{mult}}
=\sum_i\langle f(e_i),g(e_i^\#)\rangle_{M,M'}.
$$

This is the contraction with the identity tensor in $\sigma_R\otimes\sigma_R^\#$, so it is independent of the basis. Its $K$-invariance follows from invariance of both pairings. The multiplicity pairing need not be perfect. A scalar index can remain even though the generic multiplicity spaces are dual lines.

### 9.2 Evaluation and saturation

There is a canonical evaluation map

$$
\operatorname{ev}_\sigma:
\sigma_R\otimes_R\mathcal M_\sigma(M)
\longrightarrow M.
\tag{9.4}
$$

Let $M[\sigma]_E$ be the image after tensoring with $E$. Define the **saturated type-selected lattice** by

$$
M[\sigma]^{\mathrm{sat}}
=M\cap M[\sigma]_E.
\tag{9.5}
$$

**Proposition 9.1.** The quotient $M/M[\sigma]^{\mathrm{sat}}$ is torsion free. If the generic multiplicity is one and $\sigma_E$ is absolutely irreducible, then $\mathcal M_\sigma(M)$ is a free rank-one module whenever it is nonzero, its primitive generator is unique up to a unit, and (9.5) is independent of all scalar normalizations of a characteristic-zero projector.

**Proof.** The first assertion is the intersection argument of Section 3.4. Because both actions factor through a finite quotient, $\mathcal M_\sigma(M)$ is the kernel of finitely many equivariance maps from $\operatorname{Hom}_R(\sigma_R,M)$ to another finite free module. Its quotient is the image of that combined map and is torsion free, so the kernel is saturated and finite free. Flat localization identifies its generic fiber with $\operatorname{Hom}_{E[K]}(\sigma_E,M_E)$. Under multiplicity one a nonzero multiplicity module therefore has rank one and a primitive generator unique up to a unit. Absolute irreducibility makes every nonzero generic map $\sigma_E\to M_E$ injective, so all generators have the same generic type image. Scaling a rational projector changes only a preliminary lattice inside that image, not the intersection (9.5). $\square$

Saturation does not prove that a geometrically defined evaluation map has torsion-free cokernel before saturation, nor that it commutes with every nonflat base change. Those are additional exactness statements. What it does provide is the canonical integral lattice inside a known generic type summand.

### 9.3 Adjoint selection

Suppose $M$ and $M'$ are perfectly paired. Take saturated primary and companion images. Their annihilators are saturated, and the ambient pairing induces a pairing

$$
M[\sigma]^{\mathrm{sat}}\times
M'[\sigma^\#]^{\mathrm{sat}}\longrightarrow R.
\tag{9.6}
$$

If the induced generic multiplicity pairing (9.3) is nonzero and both multiplicity spaces are lines, primitive generators identify it with multiplication by an element $c\in R$, well defined up to $R^\times$. The multiplicity pairing is perfect exactly when $c$ is a unit. In general $v_R(c)$ measures a genuine congruence index; it cannot be removed by separately rescaling the two primitive generators.

For principal and dihedral types, the companion label is obtained by inverting the inducing character. For Steinberg, the quotient lattice pairs with the augmentation lattice. These are the adjoint objects that must accompany any primary type selection.

### 9.4 Why an idempotent can fail

If a finite quotient $\Gamma$ is banal, the usual character idempotent

$$
e_\sigma
=\frac{\dim\sigma}{|\Gamma|}
\sum_{g\in\Gamma}\operatorname{tr}(g^{-1}|\sigma)g
\tag{9.7}
$$

lies in $R[\Gamma]$ and selects the same summand as (9.5). If $\ell\mid|\Gamma|$, formula (9.7) may not be integral. Multiplying it by a denominator gives a correspondence, not an idempotent, and its image can fail to be saturated.

The remedy is not to pretend that the denominator is harmless. One retains the explicit type lattice, the Hom and evaluation maps, the companion lattice, and the saturation or a two-term comparison complex. This works equally for a congruence-tame principal type whose character group has $\ell$-power order and for the Steinberg boundary $\ell\mid Q+1$.

### 9.5 From a type lattice to a parahoric coefficient complex

A stable lattice is not yet a sheaf on a bad integral model. This distinction is harmless on
the characteristic-zero tower and decisive at residue-prime parahoric level. We record the
exact interface for the quotient and augmentation Steinberg pair, since it is the pair used by
the one-prime complex.

Put $G=\operatorname{GL}_2(k_F)$ and let $B\subset G$ be the upper triangular Borel. On the
generic fine hyperspecial curve, the actual Iwahori degeneracy cover has fiber $G/B$. Hence its
direct image of the constant sheaf is the permutation system

$$
P_R=R[G/B].                                                 \tag{9.8}
$$

The unit and trace on the finite-etale generic cover are respectively the constant-vector and
augmentation maps, so their quotient and kernel are exactly
$\operatorname{St}^+_R$ and $\operatorname{St}^-_R$. On the edge level, Mackey restriction is
the actual two-orbit decomposition

$$
\operatorname{Res}^{G}_{B}R[G/B]
\simeq R\oplus R[B/(B\cap sBs^{-1})],                      \tag{9.9}
$$

where the first summand is the fixed endpoint and the second, of rank $Q$, is the moving
length-two flag orbit. Thus (9.8)--(9.9) are realized by the length-one and length-two PEL flag
schemes, not by $Q+1$ formal copies of the base curve.

On generic fibers, applying associated-sheaf descent to

$$
0\to R\mathbf1\to P_R\to\operatorname{St}_R^+\to0,
\qquad
0\to\operatorname{St}_R^-\to P_R\xrightarrow{\rm aug}R\to0
                                                                    \tag{9.10}
$$

is exact because the torsor is etale-locally trivial. The two rows split as sequences of
underlying $R$-modules and are perfectly transposed by the dot product. No assertion about
invariants of $G$, $B$, or a flag stabilizer is used.

There is no analogous stalkwise argument on the bad special fiber. For example, if a
degree-$Q+1$ finite-flat flag cover has one geometric point of length $Q+1$ over a local-local
point, the etale pushforward of the constant sheaf has one rank-one stalk and the pull--trace
composite on that stalk is multiplication by $Q+1$. When $\ell\mid Q+1$, its trace is not a
surjection over $R$. Consequently neither an underived special-fiber pushforward nor the
phrase “finite flat” proves that the second row of (9.10) remains exact. This is the geometric
form of the nonbanal extension in Section 5.4.

The correct integral object is a constructible **complex**. Normalize the fine vertex--edge
diagram in the effective finite Galois closure of its objectwise generic principal covers and
retain the actual branch and flag decomposition
groups. For a supplied tame annular module, Book 22, Theorem 3.2 gives

$$
K_x(W)=[W^{H_x}\xrightarrow{\ T_x-1\ }W^{H_x}],            \tag{9.11}
$$

where $H_x$ is the prime-to-$\ell$ kernel of geometric annular monodromy and $T_x$ is its
pro-$\ell$ generator. Insert (9.11), the full branch complexes, and their generization maps
in Book 22's normalization--conductor homotopy fiber (3.10), and totalize with the two exact
rows (9.10). The terms are finite free even when the cohomology of $T_x-1$ has torsion. Pull
and trace on the expansion-one node sheets are the explicit norm maps of Book 22, (3.8), and the companion uses the
contragredient action. This produces the normalization filtration, residue-Galois action, and
adjunction without a rational type projector once the actual principal data have been
identified.

Book 122, Proposition 9.2 constructs this normalized principal/ray tower objectwise and proves
its object maps finite locally free and its lifted top legs isomorphisms. Its ray factor is geometrically constant and therefore
twists (9.11) diagonally by Book 22, (3.11). Proposition 9.3 proves $({\rm DLB}_1)$, and
(9.29k)--(9.29l) prove every active finite-depth normalization and intermediate invariant
ring, and (9.29r)--(9.29x) compute the raw higher branch, inertia, inseparable-residue,
node-annular, and boundary-stabilizer ledger. Equations (9.29b)--(9.29i) and (9.29n)--(9.29q) of Book 122 identify
the wild unipotent branch group, take its exact invariants by Book 22, (3.12)--(3.14), and
prove the unique multiplicity-one node sheet and the constant-extreme-line generization. Book 122,
Proposition 9.4 promotes the routing, multiplicity and expansion one, and Hecke/transpose route
to the actual common factor. Proposition 9.5 proves the reduced invariant branch fields,
Cartier multiplicities and active group filtrations, and reduces the normalized compositum to
the actual Kummer polynomial and intersection field. Proposition 9.6 factors the completed
endpoints from their actual valuations, leading coefficients, and tame subgroups; Proposition
9.7 gives the Milnor-tube construction; and Proposition 9.8 proves $({\rm RGC}_v)$.
For the permutation and two Steinberg rows, Proposition 9.9 constructs the strict ray datum
and computes its local field, unit, endpoint triples, Kummer factors and intersection field.
Proposition 9.10 computes the equivariantly descended branch-tube cohomology, actions and
generization maps from the normalized level-one factors; Corollary 9.11 proves
$({\rm KBL}_v)_{\rm act}$, $({\rm BTK}_v)_{\rm act}$,
$({\rm HDB}_v)_{\rm act}$ and $({\rm PNS}_v)_{\rm act}$. This conclusion is restricted to
the displayed rows, whose active action factors through $G_1$, whose spectators are etale at
$v$, and whose ray line is trait-pulled. A characteristic-zero occurrence theorem for a
different type still determines neither its annular group nor its completed branch tube.

## 10. Ordered principal deformation conditions

### 10.1 Tame generators and framed objects

We now turn the type labels into conditions on Galois representations. Let $A$ be an Artinian local $R$-algebra. At a prime of residue characteristic $p\ne\ell$, wild inertia has pro-$p$ image and cannot vary infinitesimally in an $\ell$-adic family. After its fixed finite part has been separated, the moving quotient is generated topologically by tame inertia $t$ and arithmetic Frobenius $\phi$ with relation (1.2).

An **ordered principal deformation** over $A$ consists of

$$
(\rho_A,L_{1,A},L_{2,A}),
\tag{10.1}
$$

where $\rho_A:G_F\to\mathrm{GL}_2(A)$ is a framed lift with determinant $\delta$, the $L_{i,A}$ are transverse rank-one direct summands lifting prescribed residual lines, and

$$
\rho_A(I_F)|_{L_{i,A}}=\theta_i,
\qquad
\rho_A(\phi)L_{i,A}=L_{i,A}.
\tag{10.2}
$$

Here $\theta_i:I_F\to R^\times$ are fixed finite characters satisfying

$$
\theta_i(\phi h\phi^{-1})=\theta_i(h)
\quad(h\in I_F),\qquad
\theta_1\theta_2=\delta|_{I_F}.
\tag{10.3}
$$

On the displayed tame generator, the first equation reads $\theta_i(t^Q)=\theta_i(t)$. Its full form is not decorative: it is exactly what permits a one-dimensional inertial character, including any already fixed wild part, to extend across Frobenius. In a basis adapted to the two lines,

$$
\rho_A(t)=
\begin{pmatrix}\theta_1(t)&0\\0&\theta_2(t)\end{pmatrix},
\qquad
\rho_A(\phi)=
\begin{pmatrix}a&0\\0&b\end{pmatrix},
\qquad ab=\delta(\phi).
\tag{10.4}
$$

Conversely, (10.4) satisfies the tame relation by (10.3), and continuity follows because the inertia characters have finite image. Thus the line-enhanced functor is described by closed matrix, determinant, and flag equations and is represented by a quotient of the universal framed deformation ring.

The lines are part of the object. Forgetting them can identify the two Weyl orderings or create a singular quotient at a scalar residual point. The compact principal lattice also retains an ordered inducing character when the two lifts are congruent, so the two sides carry the same amount of information.

### 10.2 The rigid prime-to-$\ell$ case

Suppose the finite inertia image has order prime to $\ell$ and

$$
\bar\theta_1\ne\bar\theta_2.
\tag{10.5}
$$

The two residual inertia idempotents are

$$
e_i=\frac{1}{|H|}\sum_{h\in H}\bar\theta_i(h)^{-1}h
$$

inside $\kappa[H]$. Their integral lifts are defined by the same formula, because $|H|$ is a unit. Hence every deformation with this fixed inertia has canonical direct summands $L_{1,A}$ and $L_{2,A}$; the enhancement adds no extra choice.

**Theorem 10.1 (clean principal chart).** Assume $\ell>2$, (10.3), and (10.5), fix the determinant, and assume that the residual representation has the displayed ordered principal shape. After choosing one $R$-valued reference lift, the framed ordered principal deformation ring is noncanonically formally smooth of relative dimension three:

$$
R^{\square,\mathrm{ps}(\theta_1,\theta_2),\delta}
\simeq R[[u,y,z]].
\tag{10.6}
$$

**Proof strategy.** One coordinate changes the ratio of the two unramified Frobenius eigenvalues, and two coordinates move the ordered transverse lines inside the fixed frame.

**Proof.** Since the idempotents lift uniquely, choose the two lifted lines first. The completed big cell of ordered transverse line pairs through the residual pair is formally smooth of dimension two: one graph coordinate moves each line, and transversality is open. In the adapted basis, inertia is fixed. Frobenius has diagonal entries $a,b$ with fixed product. Let $a_0$ be the first Frobenius eigenvalue of the reference lift. Then

$$
a=a_0(1+u),\qquad b=\delta(\phi)a^{-1}
$$

gives one formally smooth coordinate. Equations (10.3) make the tame relation automatic. These constructions are mutually inverse and lift across every small extension, proving (10.6). $\square$

The corresponding unframed tangent is one-dimensional. The other two variables are line-position, or equivalently framing-orbit, directions. This count is exact only because the residual characters separate the lines.

### 10.3 Congruence-tame characters

Assume now that $\theta_1$ and $\theta_2$ may have $\ell$-power order and

$$
\bar\theta_1=\bar\theta_2.
\tag{10.7}
$$

Inertia no longer supplies idempotents. Suppose instead that residual Frobenius has two distinct eigenvalues and fix their ordering. Hensel factorization of its characteristic polynomial gives two unique Frobenius-stable lines over every Artinian lift. We impose the two inertia characters on those lines literally. The same diagonal calculation as in Theorem 10.1 applies.

**Theorem 10.2 (congruence-tame chart).** Under the distinct residual Frobenius hypothesis and after choosing a compatible $R$-valued reference lift, the line-enhanced fixed-character functor is represented and is noncanonically formally smooth of relative dimension three over $R$, with presentation (10.6). If $\Delta$ is a finite $\ell$-group quotient of tame inertia on which the $Q$-power action is trivial, and the first character is allowed to be the tautological character of $\Delta$ while the second is forced by the determinant, then the completed local ring is

$$
R[\Delta][[u,y,z]],
\tag{10.8}
$$

completed at the chosen residual character.

**Proof.** Distinct residual Frobenius eigenvalues have unit difference, so the two spectral idempotents are polynomials in Frobenius with unit denominator. They lift uniquely and give the lines. On them, the chosen inertia characters and Frobenius scalars have the form (10.4); the determinant leaves one scalar parameter and the frame leaves two position parameters. This proves the fixed-character statement.

For the universal statement, the group algebra represents characters of $\Delta$: a local homomorphism sends each group basis element to the corresponding unit-valued character value. The $Q$-power relation is trivial on $\Delta$, so the tautological character satisfies (10.3). The same construction is therefore formally smooth relative to the completion of $R[\Delta]$ at the selected residual character. Conversely, a represented deformation recovers its tautological character, ordered lines, and the three coordinates. $\square$

The generic fiber of $R[\Delta]$ is a product of character fields. These components meet in the special fiber because all $\ell$-power characters reduce to the same character. A characteristic-zero central idempotent separates them only after dividing by $|\Delta|$. The line-enhanced ring and the lattice (4.2) retain the chosen component without that division.

### 10.4 Generic components and conductor

On the generic fiber of the ordered principal ring, the Weil--Deligne representation is

$$
\chi_1\oplus\chi_2,\qquad N=0,
$$

with $\chi_i|_{I_F}=\theta_i$. Its conductor is constant and equals

$$
a(\theta_1)+a(\theta_2).
\tag{10.9}
$$

For two nontrivial tame inverse characters this is $2$, even though the determinant is unramified. The principal type lattice $\sigma_R(\theta_1,\theta_2)$ detects precisely this generic inertial class in the selected representation theory.

Ordering is extra integral data. The Weyl element identifies the two ordered generic representations, but it need not identify their integral charts at a congruent residual point while preserving a chosen Frobenius line. Therefore the fixed nonminimal datum will record the ordering modulo only those symmetries realized by an integral isomorphism.

## 11. Special and Steinberg deformation conditions

### 11.1 The unipotent incidence equations

A scalar inertial semisimplification does not distinguish unramified representations from Steinberg representations. Monodromy supplies the missing coordinate. After a fixed scalar twist, write

$$
\rho_A(t)=1+N.
$$

Require $\operatorname{tr}N=\det N=0$. Cayley--Hamilton then gives $N^2=0$ over every coefficient algebra. With $F=\rho_A(\phi)$, the tame relation is equivalent to

$$
FNF^{-1}=QN,
\tag{11.1}
$$

because $(1+N)^Q=1+QN$. Define the **unipotent incidence functor** by the closed equations

$$
\operatorname{tr}N=\det N=0,\qquad
FNF^{-1}=QN,\qquad \det F=\delta(\phi),
\tag{11.2}
$$

together with a direct-summand line $L$ satisfying

$$
\operatorname{im}N\subseteq L\subseteq\ker N.
\tag{11.3}
$$

Matrix and projective-line coordinates show directly that this enhanced functor is represented. It contains the divisor $N=0$ and the rank-one monodromy locus. It need not be smooth at their intersection.

To see why no uniform smoothness statement is possible, put

$$
F=(1+\epsilon X)\bar F,\qquad
N=\bar N+\epsilon Y,\qquad \epsilon^2=0.
$$

Linearization gives

$$
\bar NY+Y\bar N=0
\tag{11.4}
$$

and

$$
[X,Q\bar N]+\bar F Y\bar F^{-1}-QY=0,
\tag{11.5}
$$

plus the determinant and flag derivatives. At $\bar N=0$, equation (11.4) disappears and (11.5) asks that $Y$ lie in the $Q$-eigenspace of $\operatorname{Ad}(\bar F)$. That eigenspace jumps when Frobenius roots collide or their ratio becomes $Q$. The incidence equations, rather than a generic dimension slogan, are the exact condition at exceptional points.

### 11.2 The clean level-raising chart

Suppose $\bar\rho$ is unramified and $\bar F$ has distinct eigenvalues $\bar\alpha,\bar\beta$ with

$$
\bar\alpha=Q\bar\beta.
\tag{11.6}
$$

Choose the $\bar\alpha$-line. Fix an unramified character $\psi$ satisfying

$$
\psi^2\chi_\ell=\delta,
\tag{11.7}
$$

where $\chi_\ell(\phi)=Q$ in the arithmetic convention. The enhanced special condition consists of extensions

$$
0\longrightarrow A(\psi\chi_\ell)
\longrightarrow V_A
\longrightarrow A(\psi)
\longrightarrow0
\tag{11.8}
$$

with the chosen line. The extension is allowed to split.

Assume

$$
Q\not\equiv1\pmod\ell.
\tag{11.9}
$$

The required cohomology calculation can be made directly from the tame presentation. For every Artinian coefficient algebra $A$ one has

$$
H^1(F,A(1))\simeq A.
\tag{11.10}
$$

Indeed wild inertia has pro-$p$ image and has no positive cohomology on the finite $\ell$-primary module $A(1)$. On the tame $\ell$-quotient, inertia acts trivially on $A(1)$ and arithmetic Frobenius acts by $Q$. A cocycle is determined by

$$
x=c(t),\qquad y=c(\phi).
$$

The relation $\phi t\phi^{-1}=t^Q$ imposes no further condition: both sides give $Qx$. A coboundary leaves $x$ unchanged and replaces $y$ by $y+(Q-1)a$. Since $Q-1$ is a unit under (11.9), there is a unique representative with $y=0$, while $x$ is arbitrary. This proves (11.10), functorially in $A$. Under Kummer theory $x$ is the uniformizer direction; the same conclusion follows from $F^\times=\varpi_F^{\mathbf Z}\times\mathcal O_F^\times$, because the principal units are pro-$p$ and $\ell\nmid Q-1$ removes the residue-unit direction.

**Theorem 11.1 (clean special chart).** Under (11.6)--(11.9), and relative to the split residual extension with its chosen ordered line, the framed enhanced special ring is

$$
R^{\square,\mathrm{sp},\delta}
\simeq R[[m,y,z]].
\tag{11.11}
$$

The coordinate $m$ is the extension, or monodromy, coordinate. The divisor $m=0$ is the unramified intersection, and $m\ne0$ on the generic fiber is the Steinberg locus.

**Proof.** Distinct residual roots give a unique lift of each generalized eigenspace by Hensel factorization of the Frobenius characteristic polynomial. In the resulting ordered basis, the two diagonal characters are fixed and (11.10) identifies the extension class with one element $m\in\mathfrak m_A$, since the residual extension is split. This is represented by $R[[m]]$.

To return to the fixed frame, write the ordered line pair in the completed big cell of $\mathbf P^1\times\mathbf P^1$ through the residual pair. The two graph coordinates $y,z\in\mathfrak m_A$ determine the pair uniquely, and transversality is automatic in this formal neighborhood. Conjugating the triangular representation in the adapted basis by the corresponding big-cell matrix constructs a framed deformation. Conversely, its two eigenlines recover $y,z$, and its tame cocycle recovers $m$. These constructions are inverse and functorial in $A$, proving (11.11). $\square$

Nonzero monodromy is open on the generic fiber, not a closed Artinian deformation condition when $\bar N=0$. The represented closed condition is the entire chart (11.11), including its unramified divisor.

### 11.3 Nonzero monodromy and the open Steinberg locus

If $\bar N\ne0$, its image equals its kernel and gives a unique residual line. Every lift remains rank one because one matrix entry is already a unit lift of a nonzero residual entry. Nonvanishing is then preserved under all coefficient quotients.

Fixing the unramified Steinberg character gives the shape

$$
\rho_A\sim
\begin{pmatrix}
\psi\chi_\ell&c_A\\0&\psi
\end{pmatrix},
\qquad \bar c|_{I_F}\ne0.
\tag{11.12}
$$

**Proposition 11.2 (minimal nonzero-monodromy chart).** Assume $Q\not\equiv1\pmod\ell$ and fix the two diagonal characters in (11.12). The unframed deformation functor with nonzero residual monodromy has one point over every Artinian coefficient algebra up to strict equivalence. Its framed fixed-determinant ring is formally smooth of relative dimension three.

**Proof.** In the tame cocycle calculation above, the inertia value $x=c(t)$ is a unit because its reduction is nonzero. A strict diagonal conjugation rescales it by an arbitrary unit congruent to $1$, so it has a unique normalization lifting the fixed residual value. The Frobenius value $y=c(\phi)$ is a coboundary because $Q-1$ is a unit; a strict upper-triangular conjugation removes it. Thus the unframed lift is unique.

Its centralizer is the scalar subgroup: an endomorphism commuting with both distinct diagonal characters and the nonzero extension must have equal diagonal entries and zero off-diagonal entry. The orbit of the representation in the fixed frame is therefore the formal quotient $\widehat{\mathrm{GL}}_2/\widehat{\mathbf G}_m$, which is smooth of dimension $4-1=3$. These three orbit coordinates give the framed ring $R[[x_1,x_2,x_3]]$. $\square$

This minimal nonzero-monodromy condition and the level-raising chart solve different problems. The former has nonzero residual monodromy and is closed under coefficient quotients. The latter begins with unramified residual data and must include the monodromy-zero divisor.

### 11.4 Signs and companion branches

The compact Steinberg type sees $\mu|_{\mathcal O_F^\times}$ but not the value of the unramified twist at $\varpi_F$. A local Hecke operator supplies two roots on the old space. Under the present normalization, one root selects the Steinberg sign and the other is the companion stabilization. Their product is fixed by the central character.

On the integral representation side, the primary quotient lattice $\operatorname{St}_R^+$ is paired with the augmentation companion $\operatorname{St}_R^-$. On the deformation side, the chosen line in (11.8) fixes the orientation of the $Q$-ratio. These are compatible distinctions but not identical objects: the first concerns adjunction in a compact module, the second concerns a Galois flag. A complete fixed datum records both.

The extra clean exclusion $Q\not\equiv-1\pmod\ell$ is not needed for representability of (11.11). It is needed when the two old Hecke roots and their Gram factors must remain separately integral. We therefore include it only in conclusions that require sign-separated type selection.

## 12. Dihedral and fixed finite-type deformation conditions

### 12.1 Rigidity of prime-to-$\ell$ inertia

Let $H$ be a finite quotient of inertia of order prime to $\ell$, and fix an integral representation

$$
\tau:H\longrightarrow\mathrm{GL}_2(R)
\tag{12.1}
$$

compatible with the determinant and with Frobenius conjugation. We first prove the rigidity statement underlying all clean finite types.

**Lemma 12.1 (infinitesimal rigidity).** Every lift of $\bar\tau$ to an Artinian local $R$-algebra is strictly conjugate to $\tau$, and the conjugating element is unique modulo the centralizer of $\tau(H)$.

**Proof.** For a square-zero extension $A'\twoheadrightarrow A$ with kernel $J$, the difference between two lifts is a $1$-cocycle of $H$ with values in $J\otimes\operatorname{ad}\bar\tau$. Averaging a cocycle over $H$ gives a contracting homotopy because $|H|$ is a unit. Hence $H^1(H,J\otimes\operatorname{ad}\bar\tau)=0$, so the lifts are conjugate. Two conjugating elements differ by an element centralizing the lifted action; infinitesimally its ambiguity is $(J\otimes\operatorname{ad}\bar\tau)^H$, the Lie algebra of the centralizer. Induction through square-zero quotients proves both assertions over every Artinian coefficient algebra. $\square$

Thus a fixed prime-to-$\ell$ inertial representation has no infinitesimal inertia parameter. Only its position in the frame and its Frobenius intertwiner can vary.

### 12.2 The dihedral Frobenius intertwiner

For an unramified quadratic dihedral label, restriction to inertia has two characters

$$
\xi,\qquad\xi^Q,
\tag{12.2}
$$

and Frobenius exchanges their lines. In an adapted basis,

$$
\tau(t)=
\begin{pmatrix}\xi(t)&0\\0&\xi^Q(t)\end{pmatrix},
\qquad
F=\begin{pmatrix}0&a\\b&0\end{pmatrix}.
\tag{12.3}
$$

The tame relation is immediate, and the fixed determinant gives $-ab=\delta(\phi)$. Changing the adapted basis rescales $a$ and $b$ inversely. With determinant fixed there is therefore no genuine unframed infinitesimal parameter when the dihedral representation is irreducible.

For a ramified tame quadratic pair the inertia description contains the quadratic permutation and a deeper simple character rather than just (12.2). Nevertheless, its finite image and normalized Frobenius intertwiner are fixed by the type. When their order is prime to $\ell$, Lemma 12.1 applies verbatim.

**Proposition 12.2 (label recovery).** In the clean dihedral case, the fixed Weil inertial representation together with the Frobenius intertwiner recovers the tame parameter pair $(L,\xi)$ up to $F$-isomorphism, Galois conjugation, and unramified norm twist. The compact type is then recovered from the rectified character $\vartheta=\xi\Delta_{L/F,\xi}$.

**Proof.** In the unramified case, the two inertia characters recover the regular orbit $\{\xi,\xi^Q\}$, and the fact that Frobenius exchanges them recovers the nonsplit unramified quadratic torus. At positive depth, the last nontrivial inertia layer carries the commutator form whose centralizer is $L$; its character recovers the leading term of $\xi$. The fixed torus extension recovers the remaining compact part. A character invisible on the compact part is unramified and enters through a norm twist. These are exactly the equivalences of the parameter pair. The rectifier is a functorial function of that pair in the selected correspondence, so it then recovers the direct compact character and hence the type. $\square$

### 12.3 Smoothness in the clean case

Let $C$ be the centralizer in $\mathrm{GL}_2$ of $\tau(H)$. Fix one Frobenius intertwiner $F_0$. Every other intertwiner is $cF_0$ with $c\in C$. Moving the copy of $\tau$ in the fixed frame contributes the conjugacy orbit $\mathrm{GL}_2/C$.

Because $|H|$ is invertible, the $H$-module is semisimple over every infinitesimal lift. Its centralizer is the unit group of a product of matrix endomorphism algebras on the isotypic summands, hence is smooth. Thus both the centralizer torsor and the conjugacy orbit used below are legitimate smooth formal schemes.

**Theorem 12.3 (fixed finite-type chart).** Assume $\ell>2$, $|H|$ is prime to $\ell$, and fix a compatible integral reference pair $(\tau,F_0)$ whose determinant is $\delta$. For the residual representation obtained from this pair, the framed deformation functor with this fixed finite inertia type and determinant is noncanonically represented by

$$
R[[x_1,x_2,x_3]].
$$

**Proof strategy.** Rigidity identifies the functor with a conjugacy orbit times a centralizer torsor; fixing determinant removes one smooth scalar direction.

**Proof.** Lemma 12.1 makes every inertia lift conjugate to $\tau$. The choice of conjugate in the fixed frame is formally the orbit $\mathrm{GL}_2/C$, of dimension $4-\dim C$. Once inertia is fixed, Frobenius belongs to the smooth torsor $CF_0$, of dimension $\dim C$. Their product has dimension four. The determinant map on the Frobenius torsor has surjective derivative: scalar multiplication changes determinant by twice the scalar tangent, and $2$ is a unit. Imposing the fixed determinant therefore cuts one smooth equation. The resulting dimension is

$$
(4-\dim C)+\dim C-1=3.
$$

The same description lifts across every small extension, proving formal smoothness. $\square$

For an irreducible clean dihedral residual representation, the unframed fixed-determinant tangent is zero. The three dimensions are framing directions. For a reducible finite type the centralizer is larger, but the cancellation in the proof still gives the framed dimension three.

### 12.4 Congruent and wild boundaries

If the inertia quotient has order divisible by $\ell$, Lemma 12.1 fails: the averaging homotopy is unavailable and $H^1(H,\operatorname{ad}\bar\tau)$ can be nonzero. A line-enhanced incidence problem can still be represented by matrices and relations, as in Chapter 10, but there is no blanket smoothness theorem.

If the type is primitive wild, the more basic problem is that the chosen tame quadratic data do not define its inertia representation or Frobenius extension. One would need a new integral stratum, its extension class, an exact intertwining theorem, and a component calculation. None is inferred from conductor or from the existence of a characteristic-zero supercuspidal.

Thus Theorem 12.3 applies to the clean prime-to-$\ell$ dihedral types constructed in Chapters 6--7. Congruent dihedral types may be retained as explicit incidence data when supplied, but they are not included in the smooth fixed nonminimal theorem without a separate calculation.

## 13. The fixed nonminimal local datum

### 13.1 What the datum records

A local condition adequate for integral level change must record more than a conductor exponent. At a fixed prime $v\nmid\ell$, define a **controlled nonminimal datum**

$$
\mathfrak D_v=(\tau_v,\sigma_{v,R}^+,\sigma_{v,R}^-,
\mathcal R_v,\mathcal C_v,\mathfrak o_v),
\tag{13.1}
$$

where:

1. $\tau_v$ is the selected Weil--Deligne inertial label, including the monodromy alternative;
2. $\sigma_{v,R}^+$ is the primary principal, Steinberg, or tame dihedral type lattice;
3. $\sigma_{v,R}^-=(\sigma_{v,R}^+)^\#$ is its explicit companion;
4. $\mathcal R_v$ is the represented framed fixed-determinant deformation condition;
5. $\mathcal C_v$ is the named generic component or line-enhanced chart, together with its monodromy stratification when the chart contains a boundary divisor;
6. $\mathfrak o_v$ records an ordering, special line, Iwahori-new quotient, or Frobenius sign when it is not intrinsic.

The datum is **clean** if the applicable smoothness theorem above holds, the primary and companion are perfectly paired, and any sign separation additionally required satisfies $Q_v\not\equiv\pm1\pmod\ell$. It is **congruence controlled** if a line-enhanced ring and saturated type lattice are specified even though an averaging projector is not integral.

The conductor follows from the datum; it does not define it. Two components can have the same inertial semisimplification and conductor but different monodromy rank or line orientation.

### 13.2 Separation from the coefficient prime

Let $w\mid\ell$. Here compact type theory at a prime $v\nmid\ell$ is not the relevant integral classification. Under the precise hypotheses

$$
\ell>2,\qquad
F_w=W(k)[1/\ell],\qquad k\text{ perfect},
\tag{13.2}
$$

the established integral Fontaine--Laffaille theorem gives an anti-equivalence between height-two strongly divisible lattices of Hodge type $(0,1)$ and rank-two stable coefficient lattices whose every open-ideal quotient has a finite-flat model of the attached divided-filtered type. It preserves duality, stable lines, unramified base change, and compatible quotients. When the lattice carries an actual perfect alternating pairing, duality transports that pairing and hence its determinant character; determinant preservation is not asserted from Hodge type alone.

The exact phrase “every open-ideal quotient” matters. A rational representation with Hodge--Tate weights $0$ and $1$ does not select a stable integral lattice, and finite flatness at one torsion level does not construct compatible models at all levels. The prior finite-flat theory also distinguishes schematic closure in a fixed ambient group from classification of all integral models.

Consequently a global local-condition tuple has two disjoint entries:

```text
place w dividing ell:  compatible finite-flat type (0,1) system
fixed place v away:    compact type lattice + companion + named component
```

Neither row implies the other. The first depends on the unramified-base and weight hypotheses of integral Fontaine--Laffaille theory. The second depends on $p_v\ne\ell$ and the finite-level compact constructions of this book.

### 13.3 Compatibility of a type lattice with a deformation condition

We can now state the local matching assertion without confusing generic and integral information.

**Theorem 13.1 (familywise compatibility).** Let $\mathfrak D_v$ be one of the controlled data constructed above. For every characteristic-zero point $x$ of its associated generic locus, the selected local correspondence attaches an irreducible smooth representation $\pi_x$ satisfying the associated detection condition: primary-type occurrence in the principal and dihedral cases, and a nonzero sign-selected Iwahori-new line on the nonzero-monodromy locus of the special chart. Conversely, within the selected principal, special, and tame dihedral range, that detection condition forces the Weil--Deligne parameter to have label $\tau_v$, up to the ordering or unramified twist explicitly retained in $\mathfrak o_v$. The monodromy-zero divisor in the closure of a special chart is a recorded boundary, not part of its Steinberg detection locus.

**Proof.** For the non-scalar ordered principal data included in the theorem, equations (10.2)--(10.4) give the split parameter with inertia $\theta_1\oplus\theta_2$ and $N=0$. The selected local correspondence gives the corresponding irreducible principal series, and Theorem 4.2 gives occurrence and recovery. A scalar split chart must instead retain its reducibility stratification from Section 4.4; it is not silently inserted into this non-scalar assertion.

For the special chart, a point with $m\ne0$ has rank-one monodromy and fixed scalar inertial character. It therefore corresponds to the Steinberg twist with the recorded unramified branch; Theorem 5.2 detects it through the sign-selected new line. The divisor $m=0$ is not relabelled Steinberg, because its monodromy vanishes.

For a clean dihedral datum, Proposition 12.2 first recovers the Weil parameter pair $(L,\xi)$ from inertia and Frobenius, then applies the selected tame rectifier to recover the compact character $\vartheta=\xi\Delta_{L/F,\xi}$. Theorems 6.2 and 7.3 give occurrence and the converse for the resulting compact type. These three cases exhaust the selected range and preserve the stated unramified-twist ambiguities. $\square$

The theorem is characteristic zero. The integral content is that the primary and companion lattices exist, reduce explicitly, and define saturated selection maps without requiring a nonintegral projector. It does not assert that every abstract ambient module contains the selected type; nonvanishing is a separate global input.

### 13.4 Change of coefficients and ground field

Finite extension of the coefficient DVR preserves every controlled datum once the chosen primary lattice is base-changed by convention. The type and its specified companion tensor by (3.9)--(3.10), the pairing stays perfect, and the defining deformation equations base change. This does not claim that rerunning a noncanonical orbit-lattice construction over the larger field selects the same lattice. A primitive multiplicity line remains primitive under flat coefficient extension.

Reduction to a quotient coefficient ring preserves the explicit type action and the line-enhanced deformation equations. It need not preserve the dimension of invariants. In the nonbanal case one therefore reduces the lattice and its evaluation map, not a rational idempotent.

Ground-field extension is subtler. Restricting a Weil--Deligne parameter to $W_{F'}$ can split a dihedral induction, change a conductor, or turn a special sign into a different unramified normalization. A tame quadratic field can become split. The correct type over $F'$ is the type of the restricted parameter, reconstructed from its actual inertial and monodromy data. It is not obtained by blindly tensoring the old compact representation, because $\mathrm{GL}_2(\mathcal O_{F'})$ is a different group.

At the coefficient prime, unramified ground-field base change is covered by the prior Fontaine--Laffaille equivalence under (13.2). Ramified base change is outside that theorem. The two restrictions prevent an unjustified claim that all local conditions persist under an arbitrary solvable extension.

## 14. The integral local-type package

### 14.1 Main theorem

The constructions can now be assembled into the precise package promised by the catalog.

**Theorem 14.1 (integral local types and type lattices).** Let $F$ be a nonarchimedean local field of residue characteristic $p$, let $R$ be the ring of integers in a finite extension of $\mathbf Q_\ell$, and assume $p\ne\ell$. Enlarge the coefficient field so that all selected character values occur in $R^\times$. Then:

1. For every non-scalar principal label $(\theta_1,\theta_2)$, put $n=a(\theta_2\theta_1^{-1})$. The induced module

   $$
   \sigma_R(\theta_1,\theta_2)
   =\operatorname{Ind}_{J_n}^KR(\vartheta_{12,n})
   $$

   is finite free, detects the selected principal inertial class in characteristic zero, and has companion obtained by inverting both characters. At tame level $n=1$ it is the usual Iwahori induction; for a scalar label the minimal principal type is the rank-one determinant character, while the Iwahori incidence module also records the scalar--Steinberg boundary.

2. The primary Steinberg lattice is the projective-line quotient $R[X]/R\mathbf1_X$. Its companion is the augmentation kernel. Their pairing is perfect over $R$, including when $\ell\mid Q+1$, and their reductions have the opposite extension orientations (8.5)--(8.6).

3. A regular depth-zero quadratic parameter character produces a finite free cuspidal lattice, and every selected positive-depth tame admissible pair produces a finite free maximal compact type from its minimal seed and the determinant twist (7.6). A positive-depth minimal seed uses the integral Heisenberg construction; an unramified depth-zero minimal seed uses Chapter 6. The normalized Weil character $\xi$ is first changed to the direct compact character $\vartheta=\xi\Delta_{L/F,\xi}$; these types then detect exactly the selected dihedral classes. Once a primary lattice is fixed, its defined dual companion has inverse admissible label. No independently chosen inverse-label orbit lattice is identified with that companion.

4. All specified primary and companion constructions commute with finite coefficient extension and with reduction as explicit modules. Under the datum-specific banality hypothesis, reduction preserves semisimplicity, irreducibility, and invariants; it also preserves multiplicity one when the ambient module factors through the same banal quotient. Without banality, only the explicit reduction and perfect companion pairing are asserted.

5. In a finite free ambient module, intersection with the generic type summand gives a canonical saturated type-selected lattice. Under generic multiplicity one its primitive multiplicity line is unique up to a coefficient unit. A character idempotent may replace this construction only when its denominator is a unit.

6. For $\ell>2$, the clean non-scalar ordered principal, split-residual enhanced special, nonzero-residual-monodromy special, and prime-to-$\ell$ fixed finite-type conditions are represented by the matrix-and-line problems of Chapters 10--12. After the stated compatible reference lifts and residual regularity hypotheses are fixed, their framed fixed-determinant rings are noncanonically formally smooth of relative dimension three. Non-scalar congruence-tame principal components are represented by the enhanced chart over the completed local factor of $R[\Delta]$ without averaging; a scalar component retains the boundary stratification of Section 4.4.

7. A controlled fixed nonminimal datum consists of the inertial and monodromy label, primary lattice, adjoint companion, named deformation condition and component or stratified chart, and every required ordering, newness condition, or sign. Its associated characteristic-zero locus matches the representations selected by the enhanced type datum; a monodromy-zero boundary divisor is retained but is not relabelled Steinberg. Conductor is a consequence of this datum, not a substitute for it.

8. On the characteristic-zero parahoric tower, the quotient and augmentation Steinberg rows
   are the actual unit/trace rows of the projective-line flag cover. Their bad-fiber extension
   is the normalization--conductor complex of Section 9.5. Book 122 proves
   $({\rm DLB}_1)$ and every
   active finite-depth normalization ring and the raw higher
   branch/inertia/residue/node-annular and boundary-stabilizer ledger; its explicit Drinfeld
   divisor and Bruhat equations force the wild-invariant extreme lines,
   constant-extreme-line generization, unique node routing,
   multiplicity one, and level-one residue-prime Hecke compatibility. Proposition 9.4 of
   Book 122 promotes the routing, multiplicity and expansion one, and Hecke/transpose route to
   the actual common factor. Its Proposition 9.5 supplies the invariant-field, Cartier and
   group calculation and the normalized-compositum reduction. Propositions 9.6--9.8 add the
   endpoint and Milnor-tube formalisms and the proved oriented restriction--Gysin
   correspondence. Proposition 9.9 supplies the strict ray arithmetic and factors, Proposition
   9.10 computes the actual descended tube complexes, and Corollary 9.11 proves
   $({\rm PNS}_v)_{\rm act}$. The strict terms are finite free and preserve residue Galois,
   pull, trace, and adjunction. No assertion is made here for a different principal
   representation or an arbitrary local cyclic ray datum.

9. Primitive wild supercuspidal types, ramified quadratic types in residue characteristic two, and general congruent dihedral component calculations are excluded. No assertion about their lattices, reduction multiplicities, or deformation smoothness follows from this theorem.

**Proof.** Parts 1--3 are Theorems 4.2, 5.2, 6.1--6.2, and 7.3 together with the perfect pairings (4.6), (5.6), and (7.5). Part 4 is Chapter 8 and the finite free base-change results of Chapter 3. Part 5 is Proposition 9.1 and Lemma 3.3. Part 6 is Theorems 10.1--10.2 and 11.1, Proposition 11.2, and Theorem 12.3. Part 7 is Definition (13.1) and Theorem 13.1, including the rectifier reconciliation of Proposition 12.2. Part 8 is Section 9.5 and Book 122, Propositions 9.8--9.10 and Corollary 9.11. Part 9 is the boundary proved in Sections 7.5 and 12.4. $\square$

### 14.2 Hypothesis and failure ledger

Every hypothesis in the main theorem has a visible job.

| Hypothesis or datum                                | What it supplies                                                 | What fails without it                                                                                                  |
| -------------------------------------------------- | ---------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| $p\ne\ell$                                         | $p$-group Fourier scalars are units                              | Heisenberg and additive Fourier models need not stay semisimple or primitive                                           |
| unit-valued characters                             | stable action in both directions                                 | a nonunit scalar and its inverse cannot preserve a finite lattice                                                      |
| non-scalar ratio character of conductor $n$        | minimal $J_n$ principal detection                                | the scalar case has only a rank-one minimal type, while its Iwahori incidence module also meets the Steinberg boundary |
| normalized tame rectifier                          | agreement of compact central character with the Weil determinant | the parameter character and direct compact character are misidentified                                                 |
| tame admissible quadratic pair                     | quadratic centralizer and exact intertwining                     | primitive wild strata require additional data                                                                          |
| prime-to-$\ell$ finite inertia                     | averaging rigidity                                               | inertia deformations and component crossings can appear                                                                |
| distinct residual lines or roots                   | unique integral ordering                                         | the coarse flag-forgetting space can be singular                                                                       |
| $Q\not\equiv1\pmod\ell$ in the clean special chart | one free Kummer parameter and distinct ratio                     | unit classes and line descent can add tangents                                                                         |
| $Q\not\equiv-1\pmod\ell$ for sign separation       | distinct integral old branches                                   | two signs can meet modulo $\lambda$                                                                                    |
| banality for the controlling quotient              | exact invariants and irreducible reduction                       | multiplicities can jump and extensions appear                                                                          |
| saturation                                         | torsion-free quotient and primitive image                        | a rational projector can leave a congruence index                                                                      |
| explicit companion                                 | integral adjunction                                              | generic self-duality forgets extension orientation                                                                     |
| named component and ordering                       | exact deformation problem                                        | inertial semisimplification can merge different loci                                                                   |

The direct prerequisites enter with matching hypotheses. The local representation theory of $\mathrm{GL}_2(F)$ supplies the characteristic-zero principal, special, and tame dihedral classification, newvectors, conductors, exact intertwining, and the selected local correspondence; it explicitly excludes primitive wild construction. The small-height finite-flat theory supplies schematic closure, duality, and the warning that a generic representation does not determine an integral model. The torsion Fontaine--Laffaille theory supplies exactness and full faithfulness only for weights $[0,1]$, $\ell>2$, perfect residue field, and an unramified base. Its integral equivalence and base-change theorem supplies compatible finite-flat quotients under those same hypotheses. Books 17 and 21 supply finite-etale associated covers and exact lisse-sheaf descent. Book 22 supplies the strict procyclic node complex and exact finite-wild reduction. Book 122 supplies the objectwise finite-flat common normalization, its isomorphic lifted top legs, the ray factor, proved $({\rm DLB}_1)$, all active finite-depth normalization rings, the raw higher branch/inertia/residue/node-annular and boundary-stabilizer ledger, Propositions 9.5--9.8's invariant-field, endpoint, tube, and correspondence formalisms, Proposition 9.9's strict actual ray arithmetic, Proposition 9.10's completed-tube calculation, and Corollary 9.11's actual-row principal node theorem. No result from a later book is used as a proof input.

Several tempting shortcuts are therefore invalid:

- equality of inertial semisimplifications does not imply equality of deformation components;
- equality of conductors does not imply equality of types;
- an isomorphism of generic type spaces does not identify their lattices;
- a perfect pairing after inverting $\lambda$ does not prove an integral pairing perfect;
- reduction of an irreducible type need not remain irreducible;
- a characteristic-zero projector need not act on the integral module;
- a compact type occurrence does not prove that a chosen global component is nonzero;
- finite flatness at the coefficient prime is not a compact type condition away from it.

Each repair has been constructed in the book: retain monodromy and flags, use the full type label, choose primary and companion lattices, normalize primitive lines by saturation, reduce the explicit induced model, and impose represented matrix-and-line deformation conditions.

### 14.3 Conclusion

The integral theory of local types is not obtained by placing the adjective “integral” before a characteristic-zero classification. It is a coupled structure. The compact representation contributes a finite free primary lattice. Duality contributes a possibly different companion. Reduction contributes an actual module with extension orientation, not merely a list of constituents. Saturation places the generic type summand correctly inside an ambient arithmetic lattice. The deformation problem contributes inertia, monodromy, a named component, and any ordering or sign that reduction can no longer recover.

For principal types, the finite flag variety gives an induced lattice whose congruent reductions visibly meet the scalar boundary. For Steinberg, quotient and augmentation models expose the first nonbanal dual pair. For depth-zero and positive-depth dihedral types, finite Fourier and Heisenberg constructions produce lattices whose inverse labels are exact companions. At clean primes, averaging proves rigidity; at congruence primes, enhanced lines replace averaging. In every case the use of a sum rather than an average preserves the perfect adjoint pairing.

The resulting fixed nonminimal datum can now be stated without ambiguity:

$$
\boxed{
\text{inertial and monodromy label}
+\text{ primary type lattice}
+\text{ companion lattice}
+\text{ named integral deformation component}
}.
$$

This package is stable under the coefficient operations actually proved, interfaces cleanly with the separate finite-flat type $(0,1)$ condition at the coefficient prime, and stops exactly before primitive wild supercuspidals. It is the integral local language needed for subsequent level change, adjoint comparison, and componentwise deformation arguments.
