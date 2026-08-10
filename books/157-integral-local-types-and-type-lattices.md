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
FNF^{-1}=QN,qquad F=\rho(\phi).
\tag{1.3}
$$

This convention agrees with the conductor formulas of the preceding local representation theory after the usual inversion between arithmetic and geometric Frobenius. We never change convention inside an argument.

### 1.3 The selected range

The compact types treated here are exactly the types required at the fixed nonminimal prime:

- principal types arising from two finite characters of $\mathcal O_F^\times$, with the detailed integral deformation chart given in the tame conductor-one case;
- twists of the Steinberg type by a unit-valued smooth character;
- depth-zero dihedral types from a regular character of $k_{F_2}^\times$, where $F_2/F$ is unramified quadratic;
- positive-depth types from a tame quadratic admissible pair.

The positive-depth construction includes ramified quadratic extensions only when they are tame. In residue characteristic two this excludes ramified quadratic extensions. More generally, a primitive wild supercuspidal whose leading stratum is not produced by a quadratic field character is outside the theorem. This exclusion is structural: the Heisenberg group, its torus extension, and its intertwining calculation would require data not present in the selected pair.

At the coefficient prime, the relevant integral notion is different. When $\ell>2$ and the local field is absolutely unramified with perfect residue field, the established integral Fontaine--Laffaille equivalence identifies height-two objects of Hodge type $(0,1)$ with stable lattices all of whose finite quotients are finite flat. We use that result only to keep the two local conditions in one coherent global datum. It does not construct a compact type at the coefficient prime, and the compact type lattices constructed here do not prove finite flatness.

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
r=\operatorname{Ind}_{W_L}^{W_F}\theta,\quad N=0,
\tag{2.3}
$$

where $L/F$ is separable quadratic and $\theta\ne\theta^s$ for the nontrivial $s\in\operatorname{Gal}(L/F)$. The corresponding smooth irreducible representations are, respectively, an irreducible principal series, a twist of Steinberg, and a selected dihedral supercuspidal. At the reducibility wall the same semisimple pair of Weil characters also gives a one-dimensional determinant character when $N=0$; nonzero $N$ distinguishes Steinberg.

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
a_F(\operatorname{Ind}_{W_L}^{W_F}\theta)
=f(L/F)\bigl(a_L(\theta)+d(L/F)\bigr).
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

For a tame principal label choose characters

$$
\theta_1,\theta_2:k_F^\times\longrightarrow E^\times.
$$

Inflate them to $\mathcal O_F^\times$. The unordered pair gives the characteristic-zero inertial class. When deformation components or congruences are involved we retain the ordered pair. If $\theta_1\ne\theta_2$, the principal type is the finite induction from the Iwahori. If the characters are equal, the scalar $K$-character and the finite Steinberg twist are two different compact types associated with the two sides of the monodromy boundary.

For a special label choose a smooth unit-valued character $\mu:F^\times\to E^\times$. Its compact information is $\mu|_{\mathcal O_F^\times}$, while $\mu(\varpi_F)$ records the unramified twist and the sign of a chosen Frobenius branch. The Steinberg type is the finite Steinberg representation of $\mathrm{GL}_2(k_F)$, inflated to $K$ and twisted by $\mu\circ\det$.

In the scalar case this $K$-representation is a coefficient model, not by itself an exact detector of monodromy: it also occurs in the $K(1)$-fixed part of an unramified principal series. Exact special detection uses the Iwahori-new quotient and its Hecke sign, as constructed in Section 5.3. Thus the special datum is an enhanced type rather than a bare irreducible $K$-representation.

For a dihedral label choose a tame admissible pair $(L/F,\theta)$. Admissibility means that $\theta$ does not factor through $N_{L/F}$; at positive depth its first noncentral term must generate $L$. Replacing $\theta$ by $\theta^s$ does not change the pair. A norm twist

$$
\theta\longmapsto\theta(\chi\circ N_{L/F})
\tag{2.8}
$$

corresponds to twisting the resulting $G$-representation by $\chi\circ\det$. The compact type is built from the residue torus at depth zero and from a simple character plus a finite Heisenberg representation at positive depth.

### 2.4 Twists, conductors, and central characters

Every integral construction must commute with unit-valued twists. If $\xi:F^\times\to R^\times$, then $\xi\circ\det$ is an $R$-valued character of $K$ and

$$
\sigma_R\longmapsto\sigma_R\otimes_R R(\xi\circ\det)
\tag{2.9}
$$

preserves finite freeness, duality, and reduction. Its companion is twisted by $\xi^{-1}\circ\det$.

The central character of a principal type is $(\theta_1\theta_2)|_{\mathcal O_F^\times}$. The central character of the Steinberg twist is $\mu^2|_{\mathcal O_F^\times}$. For the direct dihedral type it is $\theta|_{F^\times}$, with the rectifying character inserted when one passes to the normalized local correspondence. These identities follow by evaluating scalar matrices in the inducing data. They are necessary compatibility tests but not complete invariants: principal labels $(\theta,\theta^{-1})$ all have trivial compact central character, and special and scalar types can share the same inertial central character.

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

Let $\theta_1,\theta_2:k_F^\times\to R^\times$ and inflate them to $\mathcal O_F^\times$. Define a character of the Iwahori by

$$
\vartheta_{12}
\begin{pmatrix}a&b\\c&d\end{pmatrix}
=\theta_1(\bar a)\theta_2(\bar d).
\tag{4.1}
$$

This is a homomorphism because $c\in\mathfrak p_F$ and reduction makes the diagonal entries of a product multiply independently. It is trivial on the pro-$p$ radical of $I$.

The coset space $I\backslash K$ is the projective line $\mathbf P^1(k_F)$ and has $Q+1$ elements. Thus all of the integral questions are finite. The Weyl element exchanges the two characters and the two Bruhat cells. This is the compact shadow of normalized parabolic induction.

For characters of higher conductor one uses the corresponding compact open subgroup and its finite quotient. The lattice arguments of this chapter remain unchanged. The tame case is singled out because it is the fixed conductor-two principal condition used below and because its deformation equations can be written with one tame generator.

### 4.2 Construction of the lattice

Define

$$
\sigma_R(\theta_1,\theta_2)
=\operatorname{Ind}_I^K R(\vartheta_{12}).
\tag{4.2}
$$

It is free of rank $Q+1$. Its generic fiber is the familiar principal $K$-type. Its reduction is not an abstract semisimplification but the concrete module

$$
\sigma_R(\theta_1,\theta_2)\otimes_R\kappa
\simeq
\operatorname{Ind}_{B(k_F)}^{\mathrm{GL}_2(k_F)}
(\bar\theta_1\boxtimes\bar\theta_2),
\tag{4.3}
$$

inflated to $K$. This exact formula is valid whether or not the right side is semisimple.

**Proposition 4.1.** The lattice (4.2) is stable, finite free, compatible with every coefficient change, and generated by any function supported on $I$ whose value at $1$ is $1$.

**Proof.** Stability is built into right translation on the induced model. Choose representatives of $I\backslash K$; evaluation on them identifies the lattice with $R^{Q+1}$. Formula (3.3) proves coefficient compatibility. The function supported on $I$ is carried by right translates to the analogous basis functions on all cosets, so it generates. $\square$

### 4.3 The type-detection theorem

Assume first that $\theta_1\ne\theta_2$. Let $\mathfrak C(\theta_1,\theta_2)$ be the inertial class of irreducible principal series $i_B^G(\chi_1\boxtimes\chi_2)$ with $\chi_i|_{\mathcal O_F^\times}=\theta_i$, allowing unramified twists of the two inducing characters.

**Theorem 4.2 (principal detection).** In the selected characteristic-zero range,

$$
\dim_E\operatorname{Hom}_K
(\sigma_E(\theta_1,\theta_2),\pi)=1
$$

for $\pi\in\mathfrak C(\theta_1,\theta_2)$, and the Hom space is zero for a selected irreducible representation with a different inertial label.

**Proof strategy.** Restrict a principal series to $K$, use Iwasawa decomposition, and then use the two Bruhat cells to recover the unordered character pair. Supercuspidal and special alternatives are excluded by their exact minimal intertwining data.

**Proof.** In the compact picture of $i_B^G(\chi_1\boxtimes\chi_2)$, the standard function supported on the Iwahori Bruhat cell transforms under $I$ by $\vartheta_{12}$. Its $K$-span is a quotient of (4.2), so Frobenius reciprocity gives a nonzero map from the type. The multiplicity is the dimension of the $\vartheta_{12}$-eigenspace for $I$. The two-cell calculation gives one such eigenline when the two characters are distinct.

Conversely, a nonzero map supplies a nonzero $I$-eigenvector. The Jacquet calculation for the selected classification recovers the two torus characters from that eigenvector; the Weyl cell allows only their interchange. A special representation with scalar inertial semisimplification cannot contain this regular character, and exact intertwining of a selected dihedral type is confined to its quadratic compact-mod-center subgroup. Thus the representation is in the asserted principal class. The same two-cell calculation proves multiplicity one. $\square$

The theorem concerns characteristic-zero occurrence. After reduction, the Hom space can grow because compact invariants cease to be exact. Chapter 8 records the safe replacement.

### 4.4 Scalar and ordered boundary cases

If $\theta_1=\theta_2=\theta$, then

$$
\sigma_R(\theta,\theta)
\simeq R(\theta\circ\det)\otimes_R R[\mathbf P^1(k_F)].
\tag{4.4}
$$

The permutation module is reducible even in characteristic zero: constants form the scalar type, and the quotient is the finite Steinberg type. Thus the pair of equal inertia characters does not choose between $N=0$ and $N\ne0$. The correct integral construction retains the exact sequence rather than declaring (4.4) to be one irreducible type.

When $\theta_1\ne\theta_2$ but $\bar\theta_1=\bar\theta_2$, the characteristic-zero type is regular while its reduction lies on the scalar boundary. The ordered pair remains meaningful over $R$, even though inertia alone no longer splits the residual representation. This is the congruence-tame situation. An ordered pair of Frobenius-stable lines must be retained on the deformation side; averaging by the character group would divide by an $\ell$-power.

### 4.5 Principal companions and pairings

The companion of (4.2) is

$$
\sigma_R(\theta_1,\theta_2)^\#
\simeq
\sigma_R(\theta_1^{-1},\theta_2^{-1}).
\tag{4.5}
$$

The pairing is the finite coset sum

$$
\langle f,g\rangle
=\sum_{x\in I\backslash K}f(x)g(x).
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

**Theorem 5.2 (enhanced special detection).** In the selected characteristic-zero class with scalar compact character $\mu|_{\mathcal O_F^\times}$, one has

$$
\dim_E\pi^I_{\mathrm{new}}=1
\tag{5.9}
$$

for a special twist, while the Iwahori-new quotient is zero for a determinant character and for an irreducible unramified principal series. Consequently the nonzero new line, together with its Hecke eigenvalue, detects the special twist and its unramified sign.

**Proof strategy.** Compute invariants at the two vertices and their common edge in the Bruhat tree. The old vertex lines fill the edge space for an unramified principal series, whereas Steinberg has an edge line and no vertex line.

**Proof.** The projective-line model of $\operatorname{St}_G$ has no $K$-fixed vector: a $K$-invariant locally constant function on $\mathbf P^1(F)$ is constant, hence zero modulo constants. It has a one-dimensional $I$-fixed space because $I$ has two orbits and quotienting by constants removes one dimension. The same statements hold for $K'$. Therefore its old subspace is zero and (5.9) follows.

A determinant character has one-dimensional invariant spaces at both vertices and at the edge, so the edge line is old. An irreducible unramified principal series has a two-dimensional $I$-fixed space. Its $K$-fixed and $K'$-fixed lines are distinct: if they coincided, the vector would be fixed by the group generated by the adjacent vertex stabilizers, hence by $G$ modulo its center, forcing a one-dimensional constituent. The two lines therefore span $V^I$, and the new quotient vanishes.

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

Let $F_2/F$ be the unramified quadratic extension. Its residue field is $k_2$ with $|k_2|=Q^2$. Choose an embedding

$$
k_2^\times\hookrightarrow\mathrm{GL}_2(k_F)
$$

through multiplication on the two-dimensional $k_F$-space $k_2$. A character

$$
\eta:k_2^\times\to R^\times
$$

is **regular** when $\eta^Q\ne\eta$. Equivalently, it does not factor through the norm $k_2^\times\to k_F^\times$. The pair $\{\eta,\eta^Q\}$ is intrinsic; changing the $k_F$-basis conjugates the torus, and the nontrivial Galois automorphism exchanges the two characters.

The finite cuspidal representation $\rho_E(\eta)$ of $\mathrm{GL}_2(k_F)$ has dimension $Q-1$. The preceding local theory constructs it by a finite Deligne--Lusztig-style function model and proves

$$
\rho_E(\eta)\simeq\rho_E(\eta^Q),
\tag{6.1}
$$

with no other identifications among regular labels. We now isolate an integral model without importing any semisimplicity after reduction.

### 6.2 An integral cuspidal model

The finite cuspidal construction gives an $E$-space of functions with orbit-sum relations and an explicit action of $\mathrm{GL}_2(k_F)$. Choose an $E$-basis and let $L_0$ be its $R$-span. Define the orbit lattice

$$
\rho_R(\eta)
=\sum_{g\in\mathrm{GL}_2(k_F)}gL_0
\subset\rho_E(\eta).
\tag{6.2}
$$

It is finite, stable, and spans the cuspidal representation. It is torsion free as a submodule of an $E$-space, hence finite free over $R$. This construction does not divide by the order of the nonsplit torus; it therefore remains valid when $\ell$ divides $Q-1$ or $Q+1$. The choice is not claimed canonical. Its dual, however, is a definite companion once the primary lattice is fixed.

**Theorem 6.1 (integral depth-zero seed).** The module $\rho_R(\eta)$ is a finite free $R[\mathrm{GL}_2(k_F)]$-lattice of rank $Q-1$. It spans $\rho_E(\eta)$, commutes with coefficient extension and reduction, and satisfies

$$
\rho_R(\eta)^\#\simeq\rho_R(\eta^{-1}).
\tag{6.3}
$$

**Proof.** Stability, finite freeness, and the generic fiber were proved in the orbit-lattice construction; the rank is the characteristic-zero dimension. Tensoring a chosen finite free action matrix gives its coefficient extension and its reduction.

The finite cuspidal character table shows that the contragredient of $\rho_E(\eta)$ is $\rho_E(\eta^{-1})$. Define the inverse-label integral model to be $\rho_R(\eta)^\#$ under this identification. Evaluation is then a perfect invariant pairing by construction and gives (6.3). If an independently chosen orbit lattice is used for the inverse label, the two inverse-label lattices are commensurable; a primitive saturated intertwiner compares them, uniquely up to $R^\times$. $\square$

The proof does not say that $\rho_R(\eta)\otimes\kappa$ is irreducible. That assertion requires a banality hypothesis recorded later.

### 6.3 Inflation, compact induction, and detection

Inflate $\rho_R(\eta)$ through $K\twoheadrightarrow\mathrm{GL}_2(k_F)$ and write

$$
\sigma_{0,R}(\eta)=\operatorname{Inf}\rho_R(\eta).
\tag{6.4}
$$

Extend the corresponding depth-zero inducing representation from $K$ to $F^\times K$ using a unit-valued central character compatible with $\eta|_{k_F^\times}$, and compactly induce to $G$. The resulting generic representation is the depth-zero dihedral supercuspidal attached to the unramified admissible pair.

**Theorem 6.2 (depth-zero detection).** Among selected characteristic-zero irreducibles, $\sigma_{0,E}(\eta)$ occurs precisely in the unramified depth-zero dihedral class labelled by $\{\eta,\eta^Q\}$, and it occurs with multiplicity one.

**Proof.** Construction gives a nonzero map from the inflated finite cuspidal representation into the compact induction. By Frobenius reciprocity, its self-intertwining contributions are indexed by double cosets of $F^\times K$ in $G$. The depth-zero intertwining theorem says that a nonzero contribution forces the two associated vertices in the lattice tree to coincide; hence only the identity coset contributes. Within $K$, the finite cuspidal character table recovers the regular torus orbit $\{\eta,\eta^Q\}$. This proves multiplicity one and uniqueness of the label.

A principal or special representation has nonzero Jacquet module, whereas the finite cuspidal seed has vanishing finite unipotent coinvariants. Thus it cannot occur in those families. Exact intertwining for the positive-depth types separates them by depth. $\square$

### 6.4 Duality and conjugation

Equations (6.1) and (6.3) give

$$
\sigma_{0,R}(\eta)^\#
\simeq\sigma_{0,R}(\eta^{-1})
\simeq\sigma_{0,R}(\eta^{-Q}).
\tag{6.5}
$$

The first is the companion relation; the second is Galois conjugation of the inverse label. A self-dual generic fiber occurs when $\eta^{-1}$ belongs to the orbit $\{\eta,\eta^Q\}$. Even then the chosen lattice is identified with its companion only after an integral intertwiner has been normalized primitively. The evaluation pairing identifies the chosen inverse-label model with the full dual; comparison with any independently chosen self-dual model is unique up to $R^\times$ by Lemma 3.3.

## 7. Positive-depth tame dihedral lattices

### 7.1 Simple characters and the finite Heisenberg quotient

Let $L/F$ be tame quadratic and embedded in $A=M_2(F)$. Let $\theta:L^\times\to E^\times$ be a minimal positive-depth admissible character with unit values. The lattice chain $\mathfrak p_L^i$ determines hereditary orders $\mathfrak A\supset\mathfrak P$ in $A$ and compact groups

$$
H^1\subset J^1\subset J^0\subset K
$$

after conjugating the chain into standard position. The preceding tame type construction attaches to the first noncentral term of $\theta$ a simple character

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

The group $J^0/J^1$ is a finite toric group of order prime to $p$. The admissible character $\theta$ prescribes its action and the action of $L^\times\cap J^0$. Over $E$, the Heisenberg representation extends to a representation $\Lambda_E(\theta)$ of $J^0$. Initially the extension operators are determined only up to scalars.

**Lemma 7.2 (integral torus extension).** After a finite extension of $E$, the extension operators can be scaled so that they preserve a finite free lattice $\Lambda_R(\theta)$ containing $\eta_R$. Any two primitive stable choices are commensurable, and their saturated intertwining line is unique up to $R^\times$.

**Proof.** The quotient $J^0/J^1$ is finite. Start with the lattice generated by the orbit of $\eta_R$ under finitely many chosen extension operators. It is finite and spans $\Lambda_E(\theta)$. Each group element has finite order modulo the unit-valued central character, so Lemma 3.1 shows that its eigenvalues are units; the generated module is stable under inverses. Removing torsion gives a finite free stable lattice.

If $\Lambda$ and $\Lambda'$ are two choices, their common generic identity is a one-dimensional intertwining space by exact intertwining of the tame type. Intersect that line with $\operatorname{Hom}_R(\Lambda,\Lambda')$ and saturate. Lemma 3.3 gives a primitive map unique up to a unit. $\square$

The construction retains the extension class selected by the tame admissible-pair normalization. At positive depth it is not legitimate to specify only $\theta$ on the torus and suppress a possible projective extension ambiguity before that normalization has been fixed.

### 7.4 Maximal compact types

Define the positive-depth $K$-type

$$
\sigma_R(L,\theta)
=\operatorname{Ind}_{J^0}^{K}\Lambda_R(\theta).
\tag{7.4}
$$

It is finite free because $J^0$ has finite index in $K$. Its companion is

$$
\sigma_R(L,\theta)^\#
\simeq\sigma_R(L,\theta^{-1}),
\tag{7.5}
$$

where the inverse label includes the dual normalized extension class. The perfect pairing is again a finite coset sum.

**Theorem 7.3 (positive-depth detection).** In the selected characteristic-zero range, $\sigma_E(L,\theta)$ occurs with multiplicity one precisely in the tame dihedral inertial class of $(L,\theta)$, modulo Galois conjugation and unramified norm twist.

**Proof strategy.** Reduce occurrence to intertwining of $\Lambda_E(\theta)$ and use the leading simple character to recover the quadratic centralizer.

**Proof.** Occurrence in the compact induction attached to $(L,\theta)$ is immediate from Frobenius reciprocity. Mackey decomposition expresses its multiplicity as a sum over $J^0\backslash K/J^0$ of intertwining spaces. Exact intertwining of the simple character forces an intertwiner to normalize the quadratic lattice chain and then to lie in $J^0$ after the allowed torus action has been accounted for. Thus only the identity double coset contributes and the multiplicity is one.

Conversely, occurrence in a selected irreducible supplies an intertwiner of the simple character. Its commutator pairing recovers the centralizer $L$, and its torus action recovers $\{\theta,\theta^s\}$ up to a norm character trivial on the compact part. The selected classification then identifies the representation as the corresponding tame dihedral supercuspidal. $\square$

### 7.5 The primitive-wild boundary

Nothing in the preceding proof classifies primitive wild types. For such a representation, the first noncentral stratum need not have a quadratic field as centralizer. Even when a wild quadratic field occurs in residue characteristic two, the lattice-chain jumps and extension operators depend on the different and on additional choices. The finite Heisenberg quotient may still exist, but formulas (7.1)--(7.5) are not determined by a tame admissible pair.

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

is defined over $R$ for every subgroup $H\subset\Gamma$. It is an idempotent whose image is the invariant module, so invariants commute with tensor products. Maschke's argument makes both $E[\Gamma]$ and $\kappa[\Gamma]$ semisimple. Because $R$ and $\kappa$ are splitting and $|\Gamma|$ is a unit, the primitive central idempotents are integral and reduce bijectively; hence an irreducible block remains irreducible. $\square$

This theorem is deliberately datum dependent. The order of a convenient large quotient can contain irrelevant factors, while a smaller quotient controlling a particular type may still be banal. Conversely, $\ell\ne p$ alone is not enough: $\ell$ may divide $Q-1$ or $Q+1$.

### 8.3 Principal congruences

Formula (4.3) gives the complete safe statement for principal reduction. If $\bar\theta_1\ne\bar\theta_2$ and the controlling quotient is banal, the reduction is irreducible. If $\bar\theta_1=\bar\theta_2=\bar\theta$, then

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

Here the middle term depends only on the reduced characters as a $K$-module, even though the two distinct lifts determine different characteristic-zero components. Sequence (8.4) is the reduction of the permutation-module sequence and is exact because every term is obtained from finite free lattices.

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

For depth-zero and positive-depth dihedral types, reduction commutes with every finite induction and with the Heisenberg construction. Under banality, Theorem 8.1 preserves irreducibility and multiplicity one. Outside banality the reduced type can acquire additional subquotients or self-extensions, especially when $\ell$ divides a torus order or a normalizer index.

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

The pairing need not be perfect before saturation. A scalar index can remain even though the generic multiplicity spaces are dual lines.

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

**Proposition 9.1.** The quotient $M/M[\sigma]^{\mathrm{sat}}$ is torsion free. If the generic multiplicity is one and $\sigma_E$ is absolutely irreducible, then the saturated multiplicity line is unique up to a unit, and (9.5) is independent of all scalar normalizations of a characteristic-zero projector.

**Proof.** The first assertion is the intersection argument of Section 3.4. Under multiplicity one, the generic Hom space is a line. Its intersection with the finite free Hom module, followed by saturation, is a primitive rank-one module by Lemma 3.3. Scaling a rational projector changes only the preliminary sublattice in the same generic image, not the intersection (9.5). $\square$

Saturation does not prove that a geometrically defined evaluation map has torsion-free cokernel before saturation, nor that it commutes with every nonflat base change. Those are additional exactness statements. What it does provide is the canonical integral lattice inside a known generic type summand.

### 9.3 Adjoint selection

Suppose $M$ and $M'$ are perfectly paired. Take saturated primary and companion images. Their annihilators are saturated, and the ambient pairing induces a pairing

$$
M[\sigma]^{\mathrm{sat}}	imes
M'[\sigma^\#]^{\mathrm{sat}}longrightarrow R.
\tag{9.6}
$$

If the induced generic pairing is nonzero and both multiplicity spaces are lines, its determinant is an element $c\in R$, well defined up to $R^\times$. The pairing is perfect exactly when $c$ is a unit. In general $v_R(c)$ measures a genuine congruence index; it cannot be removed by separately rescaling the two lattices without changing primitivity.

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
\theta_i^Q=\theta_i,qquad
\theta_1\theta_2=\delta|_{I_F}.
\tag{10.3}
$$

The first equation is not decorative: it is exactly what permits a one-dimensional inertial character to extend across Frobenius. In a basis adapted to the two lines,

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

**Theorem 10.1 (clean principal chart).** Assume $\ell>2$, (10.3), and (10.5), and fix the determinant. The framed ordered principal deformation ring is formally smooth of relative dimension three:

$$
R^{\square,\mathrm{ps}(\theta_1,\theta_2),\delta}
\simeq R[[u,y,z]].
\tag{10.6}
$$

**Proof strategy.** One coordinate changes the ratio of the two unramified Frobenius eigenvalues, and two coordinates move the ordered transverse lines inside the fixed frame.

**Proof.** Since the idempotents lift uniquely, choose the two lifted lines first. The completed big cell of ordered transverse line pairs through the residual pair is formally smooth of dimension two: one graph coordinate moves each line, and transversality is open. In the adapted basis, inertia is fixed. Frobenius has diagonal entries $a,b$ with fixed product. Choose a lift $a_0$ of the first residual eigenvalue. Then

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

**Theorem 10.2 (congruence-tame chart).** Under the distinct residual Frobenius hypothesis, the line-enhanced fixed-character functor is represented and formally smooth of relative dimension three over $R$, with presentation (10.6). If $\Delta$ is a finite $\ell$-group quotient of tame inertia on which the $Q$-power action is trivial, and the first character is allowed to be the tautological character of $\Delta$ while the second is forced by the determinant, then the completed local ring is

$$
R[\Delta][[u,y,z]],
\tag{10.8}
$$

completed at the chosen residual character.

**Proof.** Distinct residual Frobenius eigenvalues have unit difference, so the two spectral idempotents are polynomials in Frobenius with unit denominator. They lift uniquely and give the lines. On them, the chosen inertia characters and Frobenius scalars have the form (10.4); the determinant leaves one scalar parameter and the frame leaves two position parameters. This proves the fixed-character statement.

For the universal statement, the group algebra represents characters of $\Delta$. The $Q$-power relation is trivial on $\Delta$, so the tautological character satisfies (10.3). The same construction is therefore formally smooth relative to $R[\Delta]$. Conversely, a represented deformation recovers its tautological character, ordered lines, and the three coordinates. $\square$

The generic fiber of $R[\Delta]$ is a product of character fields. These components meet in the special fiber because all $\ell$-power characters reduce to the same character. A characteristic-zero central idempotent separates them only after dividing by $|\Delta|$. The line-enhanced ring and the lattice (4.2) retain the chosen component without that division.

### 10.4 Generic components and conductor

On the generic fiber of the ordered principal ring, the Weil--Deligne representation is

$$
\chi_1\oplus\chi_2,qquad N=0,
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
\rho_A(t)=1+N,qquad N^2=0,
$$

and $F=\rho_A(\phi)$. The tame relation is equivalent to

$$
FNF^{-1}=QN,
\tag{11.1}
$$

because $(1+N)^Q=1+QN$. Define the **unipotent incidence functor** by the closed equations

$$
N^2=0,qquad \operatorname{tr}N=\det N=0,qquad
FNF^{-1}=QN,qquad \det F=\delta(\phi),
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
F=(1+\epsilon X)\bar F,qquad
N=\bar N+\epsilon Y,qquad \epsilon^2=0.
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

Local Kummer theory gives

$$
H^1(F,R(1))
\simeq\widehat{F^\times}_{\ell}\otimes_{\mathbf Z_\ell}R
\simeq R.
\tag{11.10}
$$

Indeed $F^\times=\varpi_F^{\mathbf Z}\times\mathcal O_F^\times$; the pro-$p$ principal units have trivial pro-$\ell$ completion, and (11.9) removes an $\ell$-part from $k_F^\times$. The uniformizer contributes one copy of $\mathbf Z_\ell$.

**Theorem 11.1 (clean special chart).** Under (11.6)--(11.9), the framed enhanced special ring is

$$
R^{\square,\mathrm{sp},\delta}
\simeq R[[m,y,z]].
\tag{11.11}
$$

The coordinate $m$ is the extension, or monodromy, coordinate. The divisor $m=0$ is the unramified intersection, and $m\ne0$ on the generic fiber is the Steinberg locus.

**Proof.** Distinct residual roots lift the chosen line uniquely. With diagonal characters fixed, extension classes are $H^1(F,R(1))$ and lift freely across small coefficient extensions by (11.10); this supplies $m$. Strict changes of frame modulo the scalar stabilizer contribute two independent coboundary directions, denoted $y,z$. The construction from $(m,y,z)$ and the recovery of the coordinates are inverse. $\square$

Nonzero monodromy is open on the generic fiber, not a closed Artinian deformation condition when $\bar N=0$. The represented closed condition is the entire chart (11.11), including its unramified divisor.

### 11.3 Nonzero monodromy and the open Steinberg locus

If $\bar N\ne0$, its image equals its kernel and gives a unique residual line. Every lift remains rank one because one matrix entry is already a unit multiple of the residual primitive entry. Nonvanishing is then preserved under all coefficient quotients.

Fixing the unramified Steinberg character gives the shape

$$
\rho_A\sim
\begin{pmatrix}
\psi\chi_\ell&c_A\\0&\psi
\end{pmatrix},
\qquad \bar c|_{I_F}\ne0.
\tag{11.12}
$$

When $Q\not\equiv1\pmod\ell$, diagonal strict conjugation normalizes the primitive tame extension, and upper-triangular strict conjugation removes the remaining Frobenius coboundary. Thus the unframed condition is rigid. The framed fixed-determinant ring is formally smooth of relative dimension three, all three variables being framing directions.

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

**Proof.** For a square-zero extension $A'\twoheadrightarrow A$ with kernel $J$, the difference between two lifts is a $1$-cocycle of $H$ with values in $J\otimes\operatorname{ad}\bar\tau$. Averaging a cocycle over $H$ gives a contracting homotopy because $|H|$ is a unit. Hence $H^1(H,J\otimes\operatorname{ad}\bar\tau)=0$, so the lifts are conjugate. The ambiguity consists exactly of $H$-invariant endomorphisms, the Lie algebra of the centralizer. Induction on the length of the Artinian ring proves the result. $\square$

Thus a fixed prime-to-$\ell$ inertial representation has no infinitesimal inertia parameter. Only its position in the frame and its Frobenius intertwiner can vary.

### 12.2 The dihedral Frobenius intertwiner

For an unramified quadratic dihedral label, restriction to inertia has two characters

$$
\vartheta,\qquad\vartheta^Q,
\tag{12.2}
$$

and Frobenius exchanges their lines. In an adapted basis,

$$
\tau(t)=
\begin{pmatrix}\vartheta(t)&0\\0&\vartheta^Q(t)\end{pmatrix},
\qquad
F=\begin{pmatrix}0&a\\b&0\end{pmatrix}.
\tag{12.3}
$$

The tame relation is immediate, and the fixed determinant gives $-ab=\delta(\phi)$. Changing the adapted basis rescales $a$ and $b$ inversely. With determinant fixed there is therefore no genuine unframed infinitesimal parameter when the dihedral representation is irreducible.

For a ramified tame quadratic pair the inertia description contains the quadratic permutation and a deeper simple character rather than just (12.2). Nevertheless, its finite image and normalized Frobenius intertwiner are fixed by the type. When their order is prime to $\ell$, Lemma 12.1 applies verbatim.

**Proposition 12.2 (label recovery).** In the clean dihedral case, the fixed inertial representation together with the Frobenius intertwiner recovers the tame admissible pair up to $F$-isomorphism, Galois conjugation, and unramified norm twist.

**Proof.** In the unramified case, the two inertia characters recover the regular orbit $\{\vartheta,\vartheta^Q\}$, and the fact that Frobenius exchanges them recovers the nonsplit unramified quadratic torus. At positive depth, the last nontrivial inertia layer carries the commutator form whose centralizer is $L$; its character recovers the leading term of $\theta$. The fixed torus extension recovers the remaining compact part of $\theta$. A character invisible on the compact part is unramified and enters through a norm twist. These are exactly the equivalences of the tame pair. $\square$

### 12.3 Smoothness in the clean case

Let $C$ be the centralizer in $\mathrm{GL}_2$ of $\tau(H)$. Fix one Frobenius intertwiner $F_0$. Every other intertwiner is $cF_0$ with $c\in C$. Moving the copy of $\tau$ in the fixed frame contributes the conjugacy orbit $\mathrm{GL}_2/C$.

**Theorem 12.3 (fixed finite-type chart).** Assume $\ell>2$, $|H|$ is prime to $\ell$, and a compatible integral Frobenius intertwiner exists. Then the framed fixed-determinant deformation ring is formally smooth of relative dimension three.

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
5. $\mathcal C_v$ is the named generic component or line-enhanced chart;
6. $\mathfrak o_v$ records an ordering, special line, Iwahori-new quotient, or Frobenius sign when it is not intrinsic.

The datum is **clean** if the applicable smoothness theorem above holds, the primary and companion are perfectly paired, and any sign separation additionally required satisfies $Q_v\not\equiv\pm1\pmod\ell$. It is **congruence controlled** if a line-enhanced ring and saturated type lattice are specified even though an averaging projector is not integral.

The conductor follows from the datum; it does not define it. Two components can have the same inertial semisimplification and conductor but different monodromy rank or line orientation.

### 13.2 Separation from the coefficient prime

Let $w\mid\ell$. Here compact type theory at a prime $v\nmid\ell$ is not the relevant integral classification. Under the precise hypotheses

$$
\ell>2,qquad
F_w=W(k)[1/\ell],\qquad k\text{ perfect},
\tag{13.2}
$$

the established integral Fontaine--Laffaille theorem gives an anti-equivalence between height-two strongly divisible lattices of Hodge type $(0,1)$ and rank-two stable coefficient lattices whose every open-ideal quotient has a finite-flat model. It preserves duality, determinant, stable lines, unramified base change, and compatible quotients.

The exact phrase “every open-ideal quotient” matters. A rational representation with Hodge--Tate weights $0$ and $1$ does not select a stable integral lattice, and finite flatness at one torsion level does not construct compatible models at all levels. The prior finite-flat theory also distinguishes schematic closure in a fixed ambient group from classification of all integral models.

Consequently a global local-condition tuple has two disjoint entries:

```text
place w dividing ell:  compatible finite-flat type (0,1) system
fixed place v away:    compact type lattice + companion + named component
```

Neither row implies the other. The first depends on the unramified-base and weight hypotheses of integral Fontaine--Laffaille theory. The second depends on $p_v\ne\ell$ and the finite-level compact constructions of this book.

### 13.3 Compatibility of a type lattice with a deformation condition

We can now state the local matching assertion without confusing generic and integral information.

**Theorem 13.1 (familywise compatibility).** Let $\mathfrak D_v$ be one of the controlled data constructed above. For every characteristic-zero point $x$ of its named generic component, the selected local correspondence attaches an irreducible smooth representation $\pi_x$ satisfying the associated detection condition: primary-type occurrence in the principal and dihedral cases, and a nonzero sign-selected Iwahori-new line in the special case. Conversely, within the selected principal, special, and tame dihedral range, that detection condition forces the Weil--Deligne parameter to have label $\tau_v$, up to the ordering or unramified twist explicitly retained in $\mathfrak o_v$.

**Proof.** For an ordered principal datum, equations (10.2)--(10.4) give the split parameter with inertia $\theta_1\oplus\theta_2$ and $N=0$. The selected local correspondence gives the corresponding principal series, and Theorem 4.2 gives occurrence and recovery.

For the special chart, a point with $m\ne0$ has rank-one monodromy and fixed scalar inertial character. It therefore corresponds to the Steinberg twist with the recorded unramified branch; Theorem 5.2 detects it through the sign-selected new line. The divisor $m=0$ is not relabelled Steinberg, because its monodromy vanishes.

For a clean dihedral datum, Proposition 12.2 recovers the tame admissible pair from inertia and Frobenius. Theorems 6.2 and 7.3 give occurrence and the converse. These three cases exhaust the selected range and preserve the stated unramified-twist ambiguities. $\square$

The theorem is characteristic zero. The integral content is that the primary and companion lattices exist, reduce explicitly, and define saturated selection maps without requiring a nonintegral projector. It does not assert that every abstract ambient module contains the selected type; nonvanishing is a separate global input.

### 13.4 Change of coefficients and ground field

Finite extension of the coefficient DVR preserves every controlled datum. The type and companion tensor by (3.9)--(3.10), the pairing stays perfect, and the defining deformation equations base change. A primitive multiplicity line remains primitive under flat coefficient extension.

Reduction to a quotient coefficient ring preserves the explicit type action and the line-enhanced deformation equations. It need not preserve the dimension of invariants. In the nonbanal case one therefore reduces the lattice and its evaluation map, not a rational idempotent.

Ground-field extension is subtler. Restricting a Weil--Deligne parameter to $W_{F'}$ can split a dihedral induction, change a conductor, or turn a special sign into a different unramified normalization. A tame quadratic field can become split. The correct type over $F'$ is the type of the restricted parameter, reconstructed from its actual inertial and monodromy data. It is not obtained by blindly tensoring the old compact representation, because $\mathrm{GL}_2(\mathcal O_{F'})$ is a different group.

At the coefficient prime, unramified ground-field base change is covered by the prior Fontaine--Laffaille equivalence under (13.2). Ramified base change is outside that theorem. The two restrictions prevent an unjustified claim that all local conditions persist under an arbitrary solvable extension.

## 14. The integral local-type package

### 14.1 Main theorem

The constructions can now be assembled into the precise package promised by the catalog.

**Theorem 14.1 (integral local types and type lattices).** Let $F$ be a nonarchimedean local field of residue characteristic $p$, let $R$ be the ring of integers in a finite extension of $\mathbf Q_\ell$, and assume $p\ne\ell$. Enlarge the coefficient field so that all selected character values occur in $R^\times$. Then:

1. For every regular tame principal label $(\theta_1,\theta_2)$, the induced module

   $$
   \sigma_R(\theta_1,\theta_2)
   =\operatorname{Ind}_I^KR(\theta_1\boxtimes\theta_2)
   $$

   is finite free, detects the selected principal inertial class in characteristic zero, and has companion obtained by inverting both characters.

2. The primary Steinberg lattice is the projective-line quotient $R[X]/R\mathbf1_X$. Its companion is the augmentation kernel. Their pairing is perfect over $R$, including when $\ell\mid Q+1$, and their reductions have the opposite extension orientations (8.5)--(8.6).

3. A regular depth-zero quadratic character produces a finite free cuspidal lattice, and every positive-depth tame admissible pair produces a finite free maximal compact type through the integral Heisenberg construction. These types detect exactly the selected dihedral classes. Their companions have inverse admissible labels.

4. All primary and companion constructions commute with finite coefficient extension and with reduction as explicit modules. Under the datum-specific banality hypothesis, reduction preserves semisimplicity, irreducibility, invariants, and multiplicity one. Without banality, only the explicit reduction and perfect companion pairing are asserted.

5. In a finite free ambient module, intersection with the generic type summand gives a canonical saturated type-selected lattice. Under generic multiplicity one its primitive multiplicity line is unique up to a coefficient unit. A character idempotent may replace this construction only when its denominator is a unit.

6. For $\ell>2$, the clean ordered principal, special, and prime-to-$\ell$ fixed finite-type conditions are represented by the matrix-and-line problems of Chapters 10--12. Their framed fixed-determinant rings are formally smooth of relative dimension three under the stated residual regularity hypotheses. Congruence-tame principal characters are represented by the enhanced chart over $R[\Delta]$ without averaging.

7. A controlled fixed nonminimal datum consists of the inertial and monodromy label, primary lattice, adjoint companion, named deformation condition and component, and every required ordering, newness condition, or sign. Its characteristic-zero points match the representations selected by the associated enhanced type datum. Conductor is a consequence of this datum, not a substitute for it.

8. Primitive wild supercuspidal types, ramified quadratic types in residue characteristic two, and general congruent dihedral component calculations are excluded. No assertion about their lattices, reduction multiplicities, or deformation smoothness follows from this theorem.

**Proof.** Parts 1--3 are Theorems 4.2, 5.2, 6.1--6.2, and 7.3 together with the perfect pairings (4.6), (5.6), and (7.5). Part 4 is Chapter 8 and the finite free base-change results of Chapter 3. Part 5 is Proposition 9.1 and Lemma 3.3. Part 6 is Theorems 10.1--10.2, 11.1, and 12.3. Part 7 is Definition (13.1) and Theorem 13.1. Part 8 is the boundary proved in Sections 7.5 and 12.4. $\square$

### 14.2 Hypothesis and failure ledger

Every hypothesis in the main theorem has a visible job.

| Hypothesis or datum | What it supplies | What fails without it |
|---|---|---|
| $p\ne\ell$ | $p$-group Fourier scalars are units | Heisenberg and additive Fourier models need not stay semisimple or primitive |
| unit-valued characters | stable action in both directions | a nonunit scalar and its inverse cannot preserve a finite lattice |
| regular principal characters | minimal principal detection | the scalar permutation module splits into scalar and Steinberg pieces |
| tame admissible quadratic pair | quadratic centralizer and exact intertwining | primitive wild strata require additional data |
| prime-to-$\ell$ finite inertia | averaging rigidity | inertia deformations and component crossings can appear |
| distinct residual lines or roots | unique integral ordering | the coarse flag-forgetting space can be singular |
| $Q\not\equiv1\pmod\ell$ in the clean special chart | one free Kummer parameter and distinct ratio | unit classes and line descent can add tangents |
| $Q\not\equiv-1\pmod\ell$ for sign separation | distinct integral old branches | two signs can meet modulo $\lambda$ |
| banality for the controlling quotient | exact invariants and irreducible reduction | multiplicities can jump and extensions appear |
| saturation | torsion-free quotient and primitive image | a rational projector can leave a congruence index |
| explicit companion | integral adjunction | generic self-duality forgets extension orientation |
| named component and ordering | exact deformation problem | inertial semisimplification can merge different loci |

The direct prerequisites enter with matching hypotheses. The local representation theory of $\mathrm{GL}_2(F)$ supplies the characteristic-zero principal, special, and tame dihedral classification, newvectors, conductors, exact intertwining, and the selected local correspondence; it explicitly excludes primitive wild construction. The small-height finite-flat theory supplies schematic closure, duality, and the warning that a generic representation does not determine an integral model. The torsion Fontaine--Laffaille theory supplies exactness and full faithfulness only for weights $[0,1]$, $\ell>2$, perfect residue field, and an unramified base. Its integral equivalence and base-change theorem supplies compatible finite-flat quotients under those same hypotheses. No result from a later book is used as a proof input.

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
