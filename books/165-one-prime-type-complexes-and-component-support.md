# One-Prime Type Complexes and Component Support

## Contents

- [1. Why one fixed prime requires a complex](#1-why-one-fixed-prime-requires-a-complex)
  - [1.1 The gap between minimal and nonminimal comparison](#11-the-gap-between-minimal-and-nonminimal-comparison)
  - [1.2 Three integral defects](#12-three-integral-defects)
  - [1.3 The conductor-one to conductor-two transition](#13-the-conductor-one-to-conductor-two-transition)
  - [1.4 The route through the book](#14-the-route-through-the-book)
- [2. The clean one-prime datum](#2-the-clean-one-prime-datum)
  - [2.1 Global coefficients and residual representation](#21-global-coefficients-and-residual-representation)
  - [2.2 The fixed prime and its special component](#22-the-fixed-prime-and-its-special-component)
  - [2.3 Automorphic carriers and localizations](#23-automorphic-carriers-and-localizations)
  - [2.4 What clean means](#24-what-clean-means)
- [3. Two-term algebra for level change](#3-two-term-algebra-for-level-change)
  - [3.1 Conventions for complexes](#31-conventions-for-complexes)
  - [3.2 The universal coefficient sequence](#32-the-universal-coefficient-sequence)
  - [3.3 Saturation and concentration](#33-saturation-and-concentration)
  - [3.4 Minimal models over local rings](#34-minimal-models-over-local-rings)
- [4. The fixed-prime degeneracy complex](#4-the-fixed-prime-degeneracy-complex)
  - [4.1 The two degeneracy maps](#41-the-two-degeneracy-maps)
  - [4.2 The cone and its cohomology](#42-the-cone-and-its-cohomology)
  - [4.3 Adjoints and the Gram operator](#43-adjoints-and-the-gram-operator)
  - [4.4 What the cone remembers](#44-what-the-cone-remembers)
- [5. Primary and companion type lattices](#5-primary-and-companion-type-lattices)
  - [5.1 Occurrence and adjunction are different tasks](#51-occurrence-and-adjunction-are-different-tasks)
  - [5.2 Primitive multiplicity lattices](#52-primitive-multiplicity-lattices)
  - [5.3 The companion pairing](#53-the-companion-pairing)
  - [5.4 Why rational projectors are forbidden](#54-why-rational-projectors-are-forbidden)
- [6. Construction of the one-prime type complex](#6-construction-of-the-one-prime-type-complex)
  - [6.1 The type functors](#61-the-type-functors)
  - [6.2 The primary complex](#62-the-primary-complex)
  - [6.3 The companion complex](#63-the-companion-complex)
  - [6.4 Independence of auxiliary presentations](#64-independence-of-auxiliary-presentations)
- [7. Amplitude and the Tor terms](#7-amplitude-and-the-tor-terms)
  - [7.1 Perfect amplitude in two adjacent degrees](#71-perfect-amplitude-in-two-adjacent-degrees)
  - [7.2 Specialization without a flatness assumption](#72-specialization-without-a-flatness-assumption)
  - [7.3 The obstruction module](#73-the-obstruction-module)
  - [7.4 Criteria for ordinary base change](#74-criteria-for-ordinary-base-change)
- [8. Old, new, primary, and companion lattices](#8-old-new-primary-and-companion-lattices)
  - [8.1 Four objects and two dualities](#81-four-objects-and-two-dualities)
  - [8.2 Quotient-new versus orthogonal-new](#82-quotient-new-versus-orthogonal-new)
  - [8.3 Type selection commutes with the saturated quotient](#83-type-selection-commutes-with-the-saturated-quotient)
  - [8.4 A lattice diagram with no hidden finite term](#84-a-lattice-diagram-with-no-hidden-finite-term)
- [9. Determinant lines of the type complex](#9-determinant-lines-of-the-type-complex)
  - [9.1 The determinant line and its canonical generic section](#91-the-determinant-line-and-its-canonical-generic-section)
  - [9.2 Primary--companion duality of determinants](#92-primary--companion-duality-of-determinants)
  - [9.3 The signed Gram factor](#93-the-signed-gram-factor)
  - [9.4 Fitting ideals and exact lengths](#94-fitting-ideals-and-exact-lengths)
- [10. The local deformation component](#10-the-local-deformation-component)
  - [10.1 The enhanced special closure](#101-the-enhanced-special-closure)
  - [10.2 The monodromy-zero boundary](#102-the-monodromy-zero-boundary)
  - [10.3 The conductor-two locus](#103-the-conductor-two-locus)
  - [10.4 The augmentation point](#104-the-augmentation-point)
- [11. Component support](#11-component-support)
  - [11.1 Support of a perfect complex](#111-support-of-a-perfect-complex)
  - [11.2 Generic support from local type occurrence](#112-generic-support-from-local-type-occurrence)
  - [11.3 Closure and full selected-component support](#113-closure-and-full-selected-component-support)
  - [11.4 Topological support is not faithfulness](#114-topological-support-is-not-faithfulness)
- [12. Saturation on the selected component](#12-saturation-on-the-selected-component)
  - [12.1 Height-one tests](#121-height-one-tests)
  - [12.2 Elimination of type-lattice indices](#122-elimination-of-type-lattice-indices)
  - [12.3 Component groups remain separate](#123-component-groups-remain-separate)
  - [12.4 The saturation theorem](#124-the-saturation-theorem)
- [13. Exact augmentation](#13-exact-augmentation)
  - [13.1 Derived augmentation](#131-derived-augmentation)
  - [13.2 Vanishing of the augmentation Tor term](#132-vanishing-of-the-augmentation-tor-term)
  - [13.3 Recovery of the minimal complex](#133-recovery-of-the-minimal-complex)
  - [13.4 Ring, module, pairing, and determinant control](#134-ring-module-pairing-and-determinant-control)
- [14. Compatibility with Taylor--Wiles patching](#14-compatibility-with-taylor--wiles-patching)
  - [14.1 Fixed-prime complexes at varying auxiliary level](#141-fixed-prime-complexes-at-varying-auxiliary-level)
  - [14.2 Finite shadows and coherent limits](#142-finite-shadows-and-coherent-limits)
  - [14.3 Patched amplitude and support](#143-patched-amplitude-and-support)
  - [14.4 Augmentation after patching](#144-augmentation-after-patching)
- [15. Exact numerical comparisons](#15-exact-numerical-comparisons)
  - [15.1 The determinant divisor](#151-the-determinant-divisor)
  - [15.2 Cotangent, type, and congruence modules](#152-cotangent-type-and-congruence-modules)
  - [15.3 A discrete-valuation calculation](#153-a-discrete-valuation-calculation)
  - [15.4 Multiplicity and companion discriminants](#154-multiplicity-and-companion-discriminants)
- [16. Exceptional cases and theorem boundaries](#16-exceptional-cases-and-theorem-boundaries)
  - [16.1 Eisenstein and reducible systems](#161-eisenstein-and-reducible-systems)
  - [16.2 Colliding roots and signs](#162-colliding-roots-and-signs)
  - [16.3 Small coefficient primes and stabilizers](#163-small-coefficient-primes-and-stabilizers)
  - [16.4 Nonreduced components and wild types](#164-nonreduced-components-and-wild-types)
- [17. The one-prime component-support theorem](#17-the-one-prime-component-support-theorem)
  - [17.1 Statement](#171-statement)
  - [17.2 Proof](#172-proof)
  - [17.3 Dependency ledger](#173-dependency-ledger)
  - [17.4 Hostile audit](#174-hostile-audit)
- [18. Conclusion](#18-conclusion)
  - [18.1 The established package](#181-the-established-package)

## 1. Why one fixed prime requires a complex

### 1.1 The gap between minimal and nonminimal comparison

The minimal deformation--Hecke problem over a totally real field ends with an unusually rigid picture. Under the clean hypotheses, the minimal deformation ring and the faithful minimal Hecke algebra are equal, the common ring is a one-dimensional complete intersection finite flat over the coefficient ring, and the minimal automorphic module is free over it. This is the strongest possible starting point for adding ramification at one finite prime. It is not, however, the conclusion for the ramified problem.

Changing one local condition changes three objects at once. The local deformation ring acquires a new component or a thickened boundary. The automorphic carrier acquires a type condition and an old--new comparison. The numerical argument acquires one extra local determinant. None of these changes is obtained by replacing a superscript ``minimal'' with ``nonminimal.'' In particular, the minimal automorphic module is a module, while the natural fixed-prime comparison is a two-term complex.

The reason for using a complex is elementary. Let

$$
d:M^{\oplus2}\longrightarrow N
$$

be the two-map degeneracy homomorphism from lower level to Iwahori level. Even when $d$ is injective and its quotient is free over the coefficient DVR, changing the coefficient ring can create a kernel unless the specialization is flat over every ring acting on the family. The correct specialized object is not obtained by tensoring the quotient alone. It is obtained by tensoring the cone

$$
[M^{\oplus2}\xrightarrow{d}N].
$$

Its extra cohomology is precisely the relevant Tor group. Thus the complex does not complicate a module argument; it names the error term that a module argument would otherwise suppress.

This book constructs the fixed-prime degeneracy and type complex, proves its exact amplitude, identifies every possible Tor term, determines its component support, compares its determinant with the old Gram and local deformation determinants, and proves exact augmentation on the selected conductor-two special component. The result is the local--global complex required for one-prime nonminimal patching. The actual patched equality of deformation and Hecke rings belongs to the next stage.

### 1.2 Three integral defects

Three defects must be kept separate.

The first is a **saturation defect**. A rational type projector can cut out the correct characteristic-zero representation while producing a lattice of finite index in the primitive integral type lattice. Reduction then creates a false class. Saturated Ihara theory removes this defect for the full degeneracy image, and primary--companion type theory removes it for the selected multiplicity lattices.

The second is a **specialization defect**. Suppose a two-term perfect complex has cohomology $H^0$ and $H^1$. After quotienting the base ring by an ideal, the specialized degree-zero cohomology can contain

$$
\operatorname{Tor}_1(H^1,\text{new base}).
$$

This term can be nonzero even when all original modules are free over the coefficient DVR. Freeness over one ring says nothing about flatness over another acting deformation ring.

The third is a **component defect**. A module can meet every irreducible component and still have a nilpotent annihilator. Thus full topological support is not the same as faithfulness. The present book proves support on the selected local component and height-one saturation. A later patching argument must still use depth or an equal-dimension mechanism to kill a possible scheme-theoretic annihilator.

These defects have different measurements:

$$
\begin{array}{c|c}
\text{defect}&\text{measurement}\cr\hline
\text{saturation}&A^{\mathrm{sat}}/A\cr
\text{specialization}&\operatorname{Tor}_1(H^1,-)\cr
\text{component}&\operatorname{Ann}(H^*)\text{ and its radical.}
\end{array}
$$

A determinant can detect codimension-one size in favorable circumstances, but it does not identify which of these three defects produced that size. The construction below identifies them before any length comparison is made.

### 1.3 The conductor-one to conductor-two transition

Fix a finite place $v$ away from the coefficient prime. The minimal datum at $v$ is an unramified twist of the special representation

$$
\operatorname{St}\otimes(\mu\circ\det),
$$

with $\mu$ unramified. Its conductor exponent is one: the exponent records nonzero monodromy even though the twisting character is unramified. A tame character $\chi$ of conductor exponent one produces

$$
\operatorname{St}\otimes((\mu\chi)\circ\det),
$$

whose conductor exponent is two. This is the selected nonminimal family.

The tame character varies in a finite local character algebra $\Lambda_v$, and the augmentation

$$
\epsilon:\Lambda_v\longrightarrow\mathcal O
$$

sends the universal tame character to $1$. At the automorphic level the conductor-two primary type specializes to the conductor-one minimal special datum. At the deformation level the enhanced conductor-two special component specializes to the named minimal special component. These assertions require integral line, sign, and companion data. They are false if the local type is remembered only as an unordered characteristic-zero isomorphism class.

The word **augmentation** in this book always means this tame-character specialization. It is unrelated to the Taylor--Wiles diamond augmentation at auxiliary primes, although both are homomorphisms from group-like coefficient algebras to $\mathcal O$. When both occur, we write $\epsilon_v$ for the fixed-prime augmentation and $\epsilon_Q$ for the auxiliary augmentation.

### 1.4 The route through the book

Chapters 2 and 3 fix the arithmetic datum and the two-term homological algebra. Chapter 4 forms the degeneracy cone. Chapters 5 and 6 place primary and companion type lattices into that cone without denominators. Chapter 7 proves perfect amplitude and writes the specialization Tor sequence explicitly. Chapter 8 distinguishes old, quotient-new, orthogonal-new, primary, and companion objects.

Chapters 9 and 10 construct the determinant line and the enhanced local special component. Chapters 11 and 12 prove generic and closed component support and eliminate height-one lattice indices. Chapter 13 proves exact augmentation, including the vanishing of the only possible Tor correction. Chapter 14 shows that the construction survives the nonnested auxiliary levels of patching. Chapter 15 gives the exact numerical comparisons. Chapters 16 and 17 record exceptional cases, the main theorem, its dependencies, and a hostile audit.

## 2. The clean one-prime datum

### 2.1 Global coefficients and residual representation

Let $F$ be totally real. Let $\ell\geq7$, and let $(\mathcal O,\varpi,k,E)$ be a complete DVR, its uniformizer, residue field, and fraction field, with residue characteristic $\ell$. Fix

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
$$

which is continuous, totally odd, absolutely irreducible, and remains absolutely irreducible over $F(\zeta_\ell)$. Fix a determinant lift

$$
\delta:G_F\longrightarrow\mathcal O^\times.
$$

We retain the clean minimal local conditions and automorphic realization of the minimal totally real comparison. In particular there is a canonical equality

$$
R^{\min}=\mathbb T^{\min}
$$

of finite flat one-dimensional complete-intersection $\mathcal O$-algebras, and the primary minimal module $M^{\min}$ is finite free of positive rank over this ring. The companion module is paired perfectly with it, with the declared inverse-double-coset adjoints.

The equality is an input, not something reproved from a one-prime determinant. This logical order matters. The fixed-prime complex will be compared with its minimal augmentation using the already established minimal ring. It will not use the desired nonminimal ring equality, which has not yet been proved.

### 2.2 The fixed prime and its special component

Fix a finite place $v\nmid\ell$. Write $q_v$ for the residue-field cardinality. We assume that the local residual representation lies on a named enhanced special boundary with the following data:

1. a scalar finite inertial character $\bar\xi_v$ of order prime to $\ell$;
2. a chosen invariant residual line;
3. a sign $\varepsilon_v\in\{1,-1\}$ in the fixed central normalization;
4. a tame $\ell$-power quotient $\Delta_v$ and its tautological character;
5. a represented fixed-determinant enhanced special local ring $R_v^{\mathrm{sp},2}$ for the conductor-two closure;
6. a represented minimal special quotient $R_v^{\mathrm{sp},1}$ obtained by the tame augmentation.

The superscripts record conductor exponents, not powers. On every nontrivial-character generic factor of $R_v^{\mathrm{sp},2}$, scalar finite inertia is $\xi_v\chi_v$, monodromy has nonzero rank one, and the conductor exponent is two. The trivial-character factor selected by augmentation has $\chi_v=1$ and conductor exponent one. Thus $R_v^{\mathrm{sp},2}$ denotes the relative tame-twist incidence family; the superscript names its nontrivial-character locus and does not assert that conductor exponent two is constant on every horizontal factor.

We assume the sign is integrally separated. In the standard Iwahori normalization this includes

$$
q_v\not\equiv\pm1\pmod\ell.
$$

The two exclusions have different uses. The congruence $q_v\not\equiv1$ separates the two old Frobenius roots. The congruence $q_v\not\equiv-1$ makes the companion signed Gram factor a unit when the selected factor vanishes. Neither is needed for the full two-map saturation theorem, but both are needed for the scalar signed comparison stated below.

### 2.3 Automorphic carriers and localizations

Choose the compact weight-two quaternionic realization used in the minimal theorem. At $v$ choose:

- a minimal special primary lattice $\sigma_v^{\min}$ and companion $\sigma_v^{\min,\dagger}$;
- a conductor-two primary lattice $\sigma_v^{(2)}$ and companion $\sigma_v^{(2),\dagger}$ over the tame character algebra $\Lambda_v=\mathcal O[\Delta_v]$;
- primitive pairings between each primary and companion lattice;
- an integral sign or ordered-line enhancement.

At every auxiliary level $Q$ away from $v$, let $M_Q^{\min}$ be the primary lower-level module and $N_Q$ the module at the fixed Iwahori or type level. All modules are localized at one non-Eisenstein maximal ideal and at its adjoint companion. We suppress this localization from notation.

Two rings act and must not be conflated. Put

$$
A_Q=\Lambda_v\widehat\otimes_{\mathcal O}\Lambda_Q,
$$

where $\Lambda_Q$ is the auxiliary diamond group ring, with $\Lambda_Q=\mathcal O$ when $Q$ is empty. This is the coefficient base over which the terms of the type complex are projective and over which derived specialization and Tor are computed. The commuting faithful Hecke image is denoted $\mathbb T_{Q,v}^{(2)}$. Its spectrum indexes automorphic branches and is the ring on which component support is measured. No freeness over this Hecke order is assumed.

The saturated Ihara theorem applies to the two degeneracy maps. Thus

$$
0\longrightarrow (M_Q^{\min})^{\oplus2}
\xrightarrow{d_Q}N_Q
\longrightarrow Q_Q^{\mathrm{new}}\longrightarrow0
\tag{2.1}
$$

is exact as a sequence of finite free $\mathcal O$-modules. The quotient is not assumed flat over a deformation ring or a fixed-prime type algebra. That missing assertion is exactly why the cone remains necessary.

The integral inner-form comparison identifies the graph multiplicity lattice with the appropriate definite type multiplicity lattice and identifies their faithful Hecke orders. It does not identify $Q_Q^{\mathrm{new}}$ with the definite module: the former is cohomological, whereas the latter is the monodromy multiplicity lattice.

### 2.4 What clean means

For this book, the one-prime datum is **clean** when all of the following hold.

1. The global and minimal hypotheses of the minimal comparison hold with $\ell\geq7$.
2. The fixed-prime residual localization is non-Eisenstein and adjoint stable.
3. Fine level is neat, or descent is through stabilizers of order invertible in $\mathcal O$.
4. The full two-map degeneracy image is saturated.
5. The primary and companion type multiplicity lattices are primitive and paired perfectly.
6. The faithful acting order is finite flat over $\mathcal O$ with reduced generic fiber; every characteristic-zero branch lies in the controlled local range, and full local--global compatibility identifies its inertia, sign, invariant line, Frobenius return, and monodromy. The universal primary type distinguishes the selected special family—conductor two on nontrivial tame-character factors and the named conductor-one special datum on the augmentation factor—from the remaining controlled branches.
7. The fixed-prime enhanced local rings are represented, $\mathcal O$-flat, and generically reduced on the selected components.
8. Tame augmentation identifies the represented conductor-two boundary with the named minimal special component.
9. The selected and companion signs are separated integrally.
10. Every auxiliary-level module used later is free over its Taylor--Wiles group ring, with exact auxiliary augmentation and a compatible primary--companion pairing.
11. The universal tame type is free over $\Lambda_v$, its augmentation is the named minimal special type, and its primary--companion incidence terms are finite projective over every coefficient base $A_Q$ used below.
12. The faithful acting image is augmentation-saturated: if $\mathcal Q$ is the direct sum of the surviving primary and companion cohomology modules and $\mathfrak a_v=\ker(\Lambda_v\to\mathcal O)$, then
    $$
    \mathbb T_{Q,v}^{(2)}\cap
    \ker\bigl(\operatorname{End}_{\Lambda_v}(\mathcal Q)
    \to\operatorname{End}_{\mathcal O}(\mathcal Q/\mathfrak a_v\mathcal Q)\bigr)
    =\mathfrak a_v\mathbb T_{Q,v}^{(2)}.
    \tag{2.2}
    $$
13. The linearized enhanced-special incidence lattice and the automorphic type-incidence lattice are primitive integral lattices in the same generic local deformation space.

No primitive wild type, $\ell$-divisible stabilizer, residual scalar system, or projector defined only over $E$ is included. A theorem may remain true in one of those situations, but it is not a consequence of the packages used here.

Conditions 11--13 are finite integral conditions, not disguised ring equalities. Condition 11 is checked on the explicit tame-character model. Condition 12 is an intersection calculation in a finite endomorphism lattice and can be tested before quotienting by augmentation. Condition 13 compares two linearized incidence presentations; it neither asserts nor uses equality of their deformation rings.

## 3. Two-term algebra for level change

### 3.1 Conventions for complexes

Complexes are cohomological. A two-term complex

$$
C=[P^0\xrightarrow{d}P^1]
$$

has $P^0$ in degree $0$ and $P^1$ in degree $1$. Thus

$$
H^0(C)=\ker d,
\qquad
H^1(C)=\operatorname{coker}d.
$$

If $P^0$ and $P^1$ are finite projective over a ring $A$, then $C$ is perfect of Tor amplitude contained in $[0,1]$. Its determinant line is

$$
\operatorname{Det}_A(C)
=\det(P^0)\otimes_A\det(P^1)^{-1}.
\tag{3.1}
$$

This convention is the inverse of the determinant of a complex placed in degrees $-1,0$. It is chosen so that the degeneracy map has its source in degree zero and its new quotient in degree one.

If $C$ is generically acyclic and the ranks of $P^0,P^1$ agree, the determinant of $d$ is a generic trivialization $\operatorname{Det}(C)\to A$, equivalently a rational section of $\operatorname{Det}(C)^{-1}$. Its integral divisor measures failure of acyclicity. This dual-line convention makes a cokernel of positive length contribute a positive divisor. If the ranks differ, there is no scalar determinant of $d$; one retains the determinant line and the appropriate maximal minors.

### 3.2 The universal coefficient sequence

The first calculation identifies exactly what specialization can change.

**Proposition 3.1 (injective two-term base change).** Let $A$ be a ring, let $C=[P^0\xrightarrow d P^1]$ with $P^0,P^1$ finite projective, and suppose $d$ is injective. For every $A$-algebra $B$ there are natural identifications

$$
H^0(C\otimes_A B)
\simeq\operatorname{Tor}_1^A(H^1(C),B)
\tag{3.2}
$$

and

$$
H^1(C\otimes_AB)\simeq H^1(C)\otimes_AB.
\tag{3.3}
$$

**Proof strategy.** Injectivity makes the displayed complex a projective presentation of its degree-one cohomology. Tensor that presentation and read its kernel and cokernel.

**Proof.** Put $H=\operatorname{coker}d$. There is an exact sequence

$$
0\longrightarrow P^0\xrightarrow dP^1\longrightarrow H\longrightarrow0.
$$

Tensor it with $B$. Since $P^1$ is projective, the long Tor sequence gives

$$
0\to\operatorname{Tor}_1^A(H,B)
\to P^0\otimes_AB\to P^1\otimes_AB
\to H\otimes_AB\to0.
\tag{3.4}
$$

The middle kernel is $H^0(C\otimes_A B)$ and the final cokernel is $H^1(C\otimes_A B)$. This proves both assertions. $\square$

The injectivity hypothesis cannot be dropped. For example, take

$$
A=k[x]/(x^2),\qquad C=[A\xrightarrow{x}A],\qquad B=A/(x).
$$

Then $H^0(C)=(x)$, but the natural map $H^0(C)\otimes_A B\to H^0(C\otimes_A B)$ is zero, not injective. A general two-term complex is governed by the full hyper-Tor filtration rather than the short sequence falsely suggested by this example. In the applications below the original differential is injective, so Proposition 3.1 applies exactly as stated. Degree-one cohomology then always commutes with ordinary scalar extension, while every new degree-zero class is a first Tor class of the quotient.

### 3.3 Saturation and concentration

Let $A=\mathcal O$ be a DVR. If $P^0,P^1$ are finite free and $d\bmod\varpi$ is injective, the saturated residual criterion gives

$$
H^0(C)=0,
\qquad
H^1(C)\text{ finite free over }\mathcal O.
\tag{3.5}
$$

Consequently, for every $\mathcal O$-algebra $B$,

$$
C\otimes_{\mathcal O}^LB
\simeq H^1(C)\otimes_{\mathcal O}B[-1]
$$

whenever $B$ is flat over $\mathcal O$. For $B=\mathcal O/\varpi^n$, the same formula holds because $H^1(C)$ is $\mathcal O$-free, so the Tor group in (3.2) vanishes.

The assertion changes when $C$ carries an action of a larger ring $A'$. It may be concentrated after forgetting to $\mathcal O$ while $H^1(C)$ is not flat over $A'$. Specialization along $A'\to B'$ can then create the Tor group

$$
\operatorname{Tor}_1^{A'}(H^1(C),B').
$$

This is the fixed-prime phenomenon. Coefficient saturation is already known; deformation- or type-direction flatness must still be proved.

### 3.4 Minimal models over local rings

Let $(A,\mathfrak m,k)$ be local, and let $C$ be perfect of amplitude $[0,1]$. A minimal finite free representative has differential with entries in $\mathfrak m$. Its ranks are determined by the special fiber:

$$
\operatorname{rank}P^i
=\dim_kH^i(C\otimes_A^Lk).
\tag{3.6}
$$

**Proposition 3.2 (amplitude shortening).** If $H^0(C\otimes_A^Lk)=0$, then $C$ is represented by a finite free module in degree $1$. If $H^1(C\otimes_A^Lk)=0$, it is represented by a finite free module in degree $0$.

**Proof.** Choose a minimal representative $[P^0\to P^1]$. Its differential becomes zero modulo $\mathfrak m$. Therefore

$$
H^0(C\otimes_A^Lk)=P^0\otimes_Ak,
\qquad
H^1(C\otimes_A^Lk)=P^1\otimes_Ak.
$$

Vanishing of the first group gives $P^0=0$ by Nakayama; vanishing of the second gives $P^1=0$. $\square$

This proposition will be used componentwise. At a generic point where the selected type does not occur, both cohomology groups vanish and the complex is acyclic. At a selected generic point, exactly one survives. The support statement is therefore visible on the fibers of the complex, without choosing a rational idempotent.

## 4. The fixed-prime degeneracy complex

### 4.1 The two degeneracy maps

Let $X_U$ be the proper Shimura curve at lower level and $X_{U_0(v)}$ its Iwahori-level curve. The two maps

$$
\pi_0,\pi_1:X_{U_0(v)}\longrightarrow X_U
$$

induce

$$
d=(\pi_0^*,\pi_1^*):
M^{\oplus2}\longrightarrow N,
\tag{4.1}
$$

where $M=H^1(X_U,\mathcal O)$ and $N=H^1(X_{U_0(v)},\mathcal O)$, localized at the fixed non-Eisenstein maximal ideal. At auxiliary level $Q$, the same notation is decorated by $Q$.

Saturated Ihara theory proves that (4.1) is injective and primitive. The proof uses the local tree, identifies the full residual kernel as Eisenstein, and then uses the DVR residual criterion. It does not use the Gram determinant. This distinction remains decisive because the Gram determinant is a nonunit precisely at a level-changing congruence.

Define

$$
C_v^{\mathrm{deg}}=[M^{\oplus2}\xrightarrow{d}N]
\tag{4.2}
$$

in degrees $0,1$. Then

$$
H^0(C_v^{\mathrm{deg}})=0,
\qquad
H^1(C_v^{\mathrm{deg}})=Q^{\mathrm{new}}.
\tag{4.3}
$$

Both terms of (4.2) and the cohomology in (4.3) are finite free over $\mathcal O$.

### 4.2 The cone and its cohomology

The complex (4.2) is the shifted cone of $d$. It lies in the exact triangle

$$
M^{\oplus2}\xrightarrow{d}N
\longrightarrow C_v^{\mathrm{deg}}
\longrightarrow M^{\oplus2}[1].
\tag{4.4}
$$

Because $d$ is primitive, (4.4) is quasi-isomorphic over $\mathcal O$ to the free quotient in degree one. Nevertheless, the two-term representative is retained. It carries the old map, its adjoint, the Hecke action at $v$, and the transition maps at finite auxiliary precision. A quotient module alone does not remember the chain homotopies needed to compare different presentations.

There is also a geometric reason to keep the cone. The semistable filtration on $N$ has graph terms in its bottom and top degrees. The good-reduction old image lies in the middle. Passing through the cone leaves the graph extremes and their monodromy map intact. Thus the cone simultaneously records the cohomological new quotient and the map by which old classes were removed.

### 4.3 Adjoints and the Gram operator

The perfect Poincaré pairings make the adjoint of $d$ equal to the column of norm maps

$$
d^*=\binom{\pi_{0,*}}{\pi_{1,*}}.
\tag{4.5}
$$

In the trivial-central normalization,

$$
G_v=d^*d=
\begin{pmatrix}
q_v+1&T_v\\
T_v&q_v+1
\end{pmatrix}.
\tag{4.6}
$$

Before central specialization the lower-left entry is $S_v^{-1}T_v$. The invariant formula is always the matrix of the two pull--norm composites; the symmetric display is a specialization, not a definition.

On a rank-one lower eigenbranch with $T_v$-eigenvalue $a_v$, the signed vectors

$$
x_\varepsilon=(x,-\varepsilon x)
$$

have Gram eigenvalues

$$
c_v^\varepsilon=q_v+1-\varepsilon a_v.
\tag{4.7}
$$

The companion vector has factor $c_v^{-\varepsilon}$. Under the clean sign-separation hypothesis, divisibility of $c_v^\varepsilon$ and invertibility of $c_v^{-\varepsilon}$ isolate one elementary divisor. The map $d$ remains injective modulo $\varpi$; it is the restricted pairing that degenerates.

### 4.4 What the cone remembers

Four statements are encoded in different parts of the cone.

1. The differential $d$ remembers the integral old lattice and its saturation.
2. The cohomology $H^1$ remembers the quotient-new lattice.
3. The dual differential $d^*$ remembers the orthogonal-new lattice.
4. The composite $d^*d$ remembers the old lattice's self-duality defect and its signed congruence factors.

None can replace another. A primitive old image can have a nonunimodular Gram form. A free quotient-new lattice need not be canonically equal to its orthogonal dual. A determinant of $d^*d$ can be nonzero while the image of $d$ is nonsaturated in an unrelated example. The fixed-prime type complex will retain all four structures.

## 5. Primary and companion type lattices

### 5.1 Occurrence and adjunction are different tasks

A primary type lattice answers an occurrence question: which characteristic-zero local packets contribute? Its companion answers an adjunction question: against which integral lattice is the primary multiplicity paired perfectly? These questions coincide over $E$ more often than they coincide over $\mathcal O$.

For the conductor-two special family, let $\sigma_v^{(2)}$ be the primary type and $\sigma_v^{(2),\dagger}$ its companion. The type Hom modules are

$$
\mathscr M^{\mathrm{pri}}
=\operatorname{Hom}_{J_v}(\sigma_v^{(2)},\mathscr M),
\qquad
\mathscr M^{\mathrm{cmp}}
=\operatorname{Hom}_{J_v}(\sigma_v^{(2),\dagger},\mathscr M).
\tag{5.1}
$$

Here $J_v$ is the selected compact or compact-mod-center subgroup, and $\mathscr M$ is the ambient automorphic lattice. The Hom is taken in the category carrying the fixed central character and tame coefficient action.

The primary lattice can be a quotient model while the companion is an augmentation submodule. They span dual generic types but need not be equal sublattices. Replacing both by one convenient rational model can alter the pairing determinant by a power of $\varpi$.

### 5.2 Primitive multiplicity lattices

The raw image of a type map is replaced by its primitive image inside the ambient finite free module. Explicitly, if

$$
u:L\longrightarrow\mathscr M
$$

is the integral type map, define

$$
\operatorname{im}^{\mathrm{pri}}(u)
=\mathscr M\cap(\operatorname{im}(u)\otimes_{\mathcal O}E).
\tag{5.2}
$$

The quotient by (5.2) is torsion free. This operation does not change the generic packet support, but it removes a possible coefficient-lattice index.

**Lemma 5.1 (uniqueness of the primitive type lattice).** Let $V$ be a finite-dimensional $E$-space and $L\subset V$ an $\mathcal O$-lattice. For an $E$-subspace $W\subset V$, the intersection $L\cap W$ is the unique saturated submodule of $L$ with generic fiber $W$.

**Proof.** The quotient $L/(L\cap W)$ embeds into $V/W$, so it is torsion free; hence the intersection is saturated. If $A\subset L$ is saturated and $A\otimes E=W$, then $A\subseteq L\cap W$. The quotient $(L\cap W)/A$ is torsion because the generic fibers agree, while it injects into the torsion-free module $L/A$. It is therefore zero. $\square$

Thus once the ambient lattice and generic type subspace are fixed, there is no scalar ambiguity in the primitive submodule. The remaining unit ambiguity concerns a choice of basis, not the lattice itself.

### 5.3 The companion pairing

The primary--companion pairing is a perfect bilinear map

$$
\langle\ ,\ \rangle:
\mathscr M^{\mathrm{pri}}\times
\mathscr M^{\mathrm{cmp}}\longrightarrow A,
\tag{5.3}
$$

where $A$ is the acting coefficient or group algebra. The second variable is semilinear for the involution sending a tame character to its inverse. Hecke operators are adjoint under inverse double cosets.

Perfectness means

$$
\mathscr M^{\mathrm{cmp}}
\xrightarrow{\sim}
\operatorname{Hom}_A(\mathscr M^{\mathrm{pri}},A).
\tag{5.4}
$$

It does not mean the two modules are equal. It also does not force either to have rank one over the Hecke algebra. At auxiliary level they are free of a fixed positive rank over the diamond group ring; after patching they may have a larger automorphic multiplicity.

The pairing is included in every finite shadow later used for patching. Otherwise a basis change could preserve the abstract modules and all Hecke eigenvalues while rescaling the determinant comparison by a nontrivial unit or, worse, by a nonunit if saturation had not been fixed.

### 5.4 Why rational projectors are forbidden

Let $e\in\operatorname{End}_E(V)$ be an idempotent preserving a generic packet subspace. If $e$ does not lie in $\operatorname{End}_{\mathcal O}(L)$, the intersection $eV\cap L$ remains a valid primitive lattice, but the image $eL$ is not even defined inside $L$. Multiplying $e$ by a denominator produces a map with the right generic image and a nonprimitive integral image.

The elementary matrix

$$
e=\frac1\varpi
\begin{pmatrix}
\varpi&1\\0&0
\end{pmatrix}
$$

illustrates the problem: its generic image is the first coordinate line, but it does not preserve $\mathcal O^2$. Any integral multiple of it has image of positive index in the primitive first-coordinate lattice.

The construction below uses integral type Hom, primitive intersection, and the primary--companion pairing. It never defines the selected complex as the image of a fraction-field idempotent. Integral sign idempotents such as $(1\pm W_v)/2$ are allowed when $2$ is a unit and $W_v$ is an integral involution.

## 6. Construction of the one-prime type complex

### 6.1 The type functors

Let $A$ be a complete local $\mathcal O$-algebra carrying the fixed-prime tame character. On the category of finite free ambient automorphic modules define

$$
\mathcal T_v^{\mathrm{pri}}(L)
=\operatorname{Hom}_{J_v}(\sigma_v^{(2)},L)^{\mathrm{sat}},
\tag{6.1}
$$

and define $\mathcal T_v^{\mathrm{cmp}}$ with the companion lattice. The saturation is taken in the common generic type subspace. In the clean range these functors have three properties:

1. they carry finite free ambient modules to finite projective $A$-modules;
2. they commute with the named degeneracy and Hecke correspondences;
3. primary--companion duality gives
   $$
   \mathcal T_v^{\mathrm{cmp}}(L^\dagger)
   \simeq\mathcal T_v^{\mathrm{pri}}(L)^\vee.
   \tag{6.2}
   $$

These are not formal properties of every compact type. They come from the integral primary--companion package and the assumed extension of the selected special type over the fixed-prime incidence construction. The prime-to-$\ell$ finite stabilizer condition ensures that passage from a neat cover remains exact.

Here is the local calculation behind projectivity and augmentation. Write the minimal special lattice as $\sigma_v^{\min}$ and let

$$
\boldsymbol\chi_v:J_v\longrightarrow\Lambda_v^\times
$$

be the universal tame character, inflated from the chosen finite quotient. The universal conductor-two lattice is

$$
\sigma_v^{(2)}
=\sigma_v^{\min}\otimes_{\mathcal O}\Lambda_v,
\qquad
j(s\otimes a)=(js)\otimes\boldsymbol\chi_v(j)a.
\tag{6.2a}
$$

As a $\Lambda_v$-module it is free, and augmentation gives

$$
\sigma_v^{(2)}\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\simeq\sigma_v^{\min}.
\tag{6.2b}
$$

The companion is obtained from the dual minimal lattice and $\boldsymbol\chi_v^{-1}$. Its evaluation pairing with (6.2a) is perfect over $\Lambda_v$ and augments to the minimal pairing.

**Lemma 6.1 (projective type terms).** Under the clean extension and stabilizer hypotheses, the primary and companion Hom modules occurring in the incidence diagram are finite projective over $A$, and (6.2b) commutes with every incidence map.

**Proof.** On a neat cover, choose orbit representatives for the finite set on which the compact type acts. Formula (6.2a) identifies the corresponding cochain group with a finite direct sum of modules of the form $A\otimes_{\mathcal O}L$, where $L$ is a finite free minimal multiplicity lattice. Hence it is finite free over $A$. Descent from the neat cover is obtained by the normalized trace idempotent for each stabilizer. Its denominator is a unit by cleanliness, so the descended module is a direct summand of a finite free module and is finite projective. Pullback and norm act on the geometric factor and commute with the scalar twist $\boldsymbol\chi_v$; evaluation at $\boldsymbol\chi_v=1$ therefore commutes with them. The companion assertion follows from the inverse-character pairing. $\square$

It is useful to distinguish the functor in (6.1) from a Hecke localization. A type functor selects a local representation-theoretic multiplicity. A Hecke localization selects a global residual system. They commute because the away-from-$v$ Hecke action commutes with $J_v$, but one cannot replace either operation by the other.

### 6.2 The primary complex

Apply the primary type functor termwise to the fixed-prime incidence chain. At an auxiliary level $Q$ this gives

$$
C_{Q,v}^{\mathrm{pri}}
=\left[
P_{Q,v}^0\xrightarrow{d_{Q,v}^{\mathrm{pri}}}P_{Q,v}^1
\right],
\tag{6.3}
$$

where

$$
P_{Q,v}^0
=\mathcal T_v^{\mathrm{pri}}((M_Q^{\min})^{\oplus2}),
\qquad
P_{Q,v}^1
=\mathcal T_v^{\mathrm{pri}}(N_Q).
\tag{6.4}
$$

The differential is induced by the two degeneracy pullbacks with the selected sign and tame character. The construction is made before taking cohomology. It therefore retains any failure of the type functor to carry the short exact sequence (2.1) to a short exact sequence.

At a characteristic-zero point $x$, local newvector theory gives a simple description:

$$
C_{Q,v}^{\mathrm{pri}}\otimes_AE_x\simeq
\begin{cases}
0,&\Pi_{x,v}\text{ is outside the selected special family},\\
L_x[-1],&\chi_{v,x}\ne1\text{ and }\Pi_{x,v}\text{ has the selected conductor-two type},\\
L_x^{\min}[-1],&\chi_{v,x}=1\text{ and }\Pi_{x,v}\text{ lies on the named minimal-special face},
\end{cases}
\tag{6.5}
$$

Here $L_x$ and $L_x^{\min}$ are the corresponding multiplicity spaces. The first line includes lower-conductor packets on a nontrivial tame-character factor and packets on the trivial factor that do not belong to the named minimal-special datum. The last two lines use the distinguished type multiplicity line; if global automorphic multiplicity is $m_x$, its dimension is $m_x$. The third line is forced by exact augmentation and must not be deleted from the generic support statement.

The shift in (6.5) is not a convention hiding an old kernel. It follows because saturated Ihara injectivity kills degree zero and the selected new quotient is degree one.

### 6.3 The companion complex

The companion construction gives

$$
C_{Q,v}^{\mathrm{cmp}}
=\left[
P_{Q,v}^{0,\dagger}
\xrightarrow{d_{Q,v}^{\mathrm{cmp}}}
P_{Q,v}^{1,\dagger}
\right].
\tag{6.6}
$$

The degree labels are deliberately reversed relative to the geometric source and target:

$$
P_{Q,v}^{0,\dagger}=(P_{Q,v}^1)^\vee,
\qquad
P_{Q,v}^{1,\dagger}=(P_{Q,v}^0)^\vee,
\qquad
d_{Q,v}^{\mathrm{cmp}}=-\bigl(d_{Q,v}^{\mathrm{pri}}\bigr)^\vee.
$$

Thus the companion is the norm complex from the dual upper type lattice to the dual old source. It is not a second pullback complex written in the same geometric direction. This reversal is what makes quotient-new primary classes correspond to kernel-type companion classes.

Termwise primary--companion pairings and pull--norm adjunction define a perfect pairing of complexes

$$
C_{Q,v}^{\mathrm{pri}}
\otimes_A^LC_{Q,v}^{\mathrm{cmp}}
\longrightarrow A[-1].
\tag{6.7}
$$

Equivalently,

$$
C_{Q,v}^{\mathrm{cmp}}
\simeq
R\operatorname{Hom}_A(C_{Q,v}^{\mathrm{pri}},A)[-1].
\tag{6.8}
$$

The shift reflects the fact that the differential and its adjoint occupy opposite ends of a two-term complex.

**Proof of (6.8).** A cochain complex in degrees $0,1$ has its ordinary dual in degrees $-1,0$. Shifting that dual by $[-1]$ places $(P^1)^\vee$ in degree $0$ and $(P^0)^\vee$ in degree $1$. The dual differential is $-d^\vee$ with the standard cochain sign. Consequently the degree-zero primary term pairs with the degree-one companion term, and the degree-one primary term pairs with the degree-zero companion term, in both cases landing in the copy of $A$ in degree $1$ of $A[-1]$. Pullback is adjoint to norm, so these cross-pairings respect the differentials. They are termwise perfect, and hence induce the asserted isomorphism to the derived dual. $\square$

It follows that primary and companion complexes have reflected fiber cohomology:

$$
H^i(C^{\mathrm{cmp}}\otimes k(x))
\simeq
H^{1-i}(C^{\mathrm{pri}}\otimes k(x))^\vee.
\tag{6.9}
$$

This identity is the correct integral form of self-adjoint old--new duality. It does not identify primary and companion lattices.

### 6.4 Independence of auxiliary presentations

The incidence construction can be represented by different fine covers, different cellular resolutions, or different finite free models. The resulting type complex is nevertheless well defined in the derived category.

**Proposition 6.1 (independence).** Any two clean finite projective constructions of $C_{Q,v}^{\mathrm{pri}}$ are joined by a Hecke-equivariant quasi-isomorphism compatible with the tame character, augmentation, and primary--companion pairing. The induced determinant-line isomorphism is canonical.

**Proof strategy.** Both constructions calculate the same cone of the same pair of geometric degeneracy correspondences after applying the same primitive type functor. A common fine cover gives a third model mapping to both. Prime-to-$\ell$ descent and projectivity make the comparison exact.

**Proof.** Pass to a common neat refinement of the two levels. Pullback followed by normalized trace is multiplication by a stabilizer index, which is a unit by cleanliness. Hence each original complex is a direct summand of the refined complex. The two summands are cut out by the same integral descent idempotent and the same primitive generic type subspace, so Lemma 5.1 identifies them. Cellular or resolution choices are related by chain homotopy because they resolve the same finite correspondence diagram. Applying the projective type functor preserves the homotopies. Thus the induced maps are quasi-isomorphisms. Determinant invariance for quasi-isomorphic perfect complexes and coherence for the common refinement give the last assertion. $\square$

## 7. Amplitude and the Tor terms

### 7.1 Perfect amplitude in two adjacent degrees

**Theorem 7.1 (one-prime amplitude).** For every clean auxiliary level $Q$, the primary and companion type complexes are perfect over the coefficient algebra $A_Q$ and have Tor amplitude contained in $[0,1]$. Their cohomology is finite, and after forgetting to $\mathcal O$ one has

$$
H^0(C_{Q,v}^{\mathrm{pri}})=0,
\qquad
H^1(C_{Q,v}^{\mathrm{pri}})
\text{ is }\mathcal O\text{-free}.
\tag{7.1}
$$

The same holds for the companion complex with the degrees reflected by (6.9).

**Proof.** By construction each term in (6.3) is finite projective over $A_Q$, so the complex is perfect with amplitude $[0,1]$. Forgetting the $A_Q$-action gives the primary direct summand of the geometric degeneracy complex. Residual Ihara injectivity remains injective on an integral direct summand, hence its degree-zero cohomology vanishes. The image is primitive in the ambient $\mathcal O$-lattice, and primitive intersection with the selected generic type subspace remains primitive. Therefore the degree-one quotient is $\mathcal O$-torsion free and finite, hence free. Companion duality proves the corresponding statement for (6.6). $\square$

The theorem deliberately stops short of saying that $H^1$ is $A_Q$-flat. A perfect two-term presentation and coefficient freeness do not imply flatness over a possibly singular character or diamond algebra. It makes no projectivity assertion over the faithful Hecke order.

### 7.2 Specialization without a flatness assumption

Let $A_Q\to B$ be any local specialization. Proposition 3.1 gives

$$
0\to H^0(C_{Q,v}^{\mathrm{pri}})\otimes_{A_Q}B
\to H^0(C_{Q,v}^{\mathrm{pri}}\otimes_{A_Q}^LB)
\to\operatorname{Tor}_1^{A_Q}(H^1(C_{Q,v}^{\mathrm{pri}}),B)
\to0.
\tag{7.2}
$$

Using (7.1), this becomes the canonical identification

$$
H^0(C_{Q,v}^{\mathrm{pri}}\otimes_{A_Q}^LB)
\simeq
\operatorname{Tor}_1^{A_Q}(H^1(C_{Q,v}^{\mathrm{pri}}),B).
\tag{7.3}
$$

Meanwhile

$$
H^1(C_{Q,v}^{\mathrm{pri}}\otimes_{A_Q}^LB)
\simeq
H^1(C_{Q,v}^{\mathrm{pri}})\otimes_{A_Q}B.
\tag{7.4}
$$

Equations (7.3)--(7.4) are the exact amplitude statement required later. Every newly appearing degree-zero class has one source: it is a first Tor class of the new quotient. There are no higher Tor contributions because the complex itself has length one.

### 7.3 The obstruction module

For a specialization $A_Q\to B$, define

$$
\mathscr E_{Q,v}(B)
=H^0(C_{Q,v}^{\mathrm{pri}}\otimes_{A_Q}^LB).
\tag{7.5}
$$

We call this the **specialization obstruction module**. By (7.3),

$$
\mathscr E_{Q,v}(B)
=\operatorname{Tor}_1^{A_Q}
(H^1(C_{Q,v}^{\mathrm{pri}}),B).
\tag{7.6}
$$

This module must not be called an Ihara kernel. The original integral differential is injective. The obstruction arises only after a possibly nonflat change of the acting base. Nor is it a component group: it exists before any semistable monodromy lattice is introduced.

If $B=A_Q/I$ and $I$ is generated by a nonzerodivisor $t$, the standard resolution of $B$ gives

$$
\mathscr E_{Q,v}(B)
\simeq H^1(C_{Q,v}^{\mathrm{pri}})[t],
\tag{7.7}
$$

the $t$-torsion submodule. Thus exact specialization along $t=0$ is equivalent to $t$ acting injectively on the new type module.

### 7.4 Criteria for ordinary base change

**Corollary 7.2 (base-change criteria).** In the preceding setting, each of the following conditions implies $\mathscr E_{Q,v}(B)=0$:

1. $B$ is flat over $A_Q$;
2. $H^1(C_{Q,v}^{\mathrm{pri}})$ is flat over $A_Q$;
3. $B=A_Q/(t_1,\ldots,t_r)$ and the sequence $t_1,\ldots,t_r$ is regular on $H^1$;
4. $B=A_Q/(t)$ and $H^1$ is $t$-torsion free.

**Proof.** The first two assertions are the defining Tor vanishings for flatness. For the third, the Koszul resolution of $B$ computes Tor; regularity on $H^1$ makes its positive homology vanish. The fourth is the one-element case (7.7). $\square$

The fixed-prime augmentation generally does not fall under these formal criteria. For a finite tame character group, elements $\delta-1$ in $\mathcal O[\Delta_v]$ are zero divisors, since they annihilate the corresponding norm sums. Thus the augmentation ideal is not silently treated as a regular sequence. Chapter 13 proves the required first-Tor vanishing directly by identifying the augmented differential and using its arithmetic injectivity.

## 8. Old, new, primary, and companion lattices

### 8.1 Four objects and two dualities

At the fixed prime there are four integral lattices:

$$
\begin{array}{c|c}
\text{notation}&\text{meaning}\cr\hline
O&\operatorname{im}(d),\text{ the saturated old lattice}\cr
Q&N/O,\text{ the quotient-new lattice}\cr
Q^\perp&\ker(d^*),\text{ the orthogonal-new lattice}\cr
X_v&H_1(\Gamma,\mathcal O),\text{ the monodromy multiplicity lattice.}
\end{array}
\tag{8.1}
$$

Type selection produces primary versions and adjoint companion versions of each object. Poincaré duality identifies

$$
Q^\perp\simeq Q^\vee,
\tag{8.2}
$$

while monodromy gives

$$
q_\Gamma:X_v\longrightarrow X_v^\vee.
\tag{8.3}
$$

These are different dualities. The cokernel of (8.2) is zero because old saturation makes restriction of functionals surjective. The cokernel of (8.3) can be nonzero and is the Néron component group.

### 8.2 Quotient-new versus orthogonal-new

**Proposition 8.1.** Let $N$ be finite free over a DVR with a perfect pairing, and let $O\subset N$ be saturated. Then the pairing induces a canonical isomorphism

$$
\ker(N\to O^\vee)\xrightarrow{\sim}(N/O)^\vee.
\tag{8.4}
$$

**Proof.** Since $N/O$ is free, dualizing

$$
0\to O\to N\to N/O\to0
$$

is exact. The kernel of $N^\vee\to O^\vee$ is $(N/O)^\vee$. Identify $N$ with $N^\vee$ by the perfect pairing. $\square$

There need not be an integral splitting $N=O\oplus Q^\perp$. Such a splitting would require the Gram map $O\to O^\vee$ to be an isomorphism. At a congruence point its cokernel is deliberately nonzero.

### 8.3 Type selection commutes with the saturated quotient

The primitive type functor carries (2.1) to an exact sequence on the selected generic component and then takes primitive closure. This gives

$$
0\longrightarrow O^{\mathrm{pri}}
\longrightarrow N^{\mathrm{pri}}
\longrightarrow Q^{\mathrm{pri}}
\longrightarrow0
\tag{8.5}
$$

as $\mathcal O$-lattices. The quotient $Q^{\mathrm{pri}}$ is $H^1(C_v^{\mathrm{pri}})$.

**Proof of exactness.** The first arrow is injective because it is a restriction of the injective old map. Its image is the intersection of the ambient old generic subspace with the primitive selected lattice. If $\varpi x$ belongs to this intersection, old saturation places $x$ in the ambient old lattice and type primitivity places it in the selected lattice. Thus the intersection is saturated. Its quotient is torsion free, proving exactness with a free final term. $\square$

This argument uses both saturations. Old saturation alone does not prove that a rational type subspace has been intersected primitively, and type saturation alone does not repair a defective old image.

### 8.4 A lattice diagram with no hidden finite term

The primary and companion sequences fit into

$$
\begin{array}{ccccccccc}
0&\to&O^{\mathrm{pri}}&\to&N^{\mathrm{pri}}&\to&Q^{\mathrm{pri}}&\to&0\\
&&\downarrow&&\downarrow&&\downarrow&&\\
0&\to&(O^{\mathrm{cmp}})^\vee&\to&(N^{\mathrm{cmp}})^\vee&\to&(Q^{\mathrm{cmp}})^\vee&\to&0,
\end{array}
\tag{8.6}
$$

where the vertical maps come from the primitive pairings. The middle and left maps are isomorphisms by the type package and adjunction; the right map is therefore an isomorphism by the short five lemma.

There is no finite cokernel in the right square. Any such cokernel would be a type-lattice index. It has been removed by primitive intersection and perfect companion duality. The Gram cokernel and the component cokernel remain elsewhere; they are not hidden in (8.6).

## 9. Determinant lines of the type complex

### 9.1 The determinant line and its canonical generic section

For

$$
C_v^{\mathrm{pri}}=[P^0\xrightarrow dP^1],
$$

define

$$
\mathscr L_v^{\mathrm{pri}}
=\operatorname{Det}(C_v^{\mathrm{pri}})
=\det(P^0)\otimes\det(P^1)^{-1}.
\tag{9.1}
$$

On a generic component where the complex is acyclic, $d$ gives a canonical trivialization

$$
\tau_d:\mathscr L_v^{\mathrm{pri}}\longrightarrow A.
$$

Equivalently, $\tau_d$ is a rational section of $(\mathscr L_v^{\mathrm{pri}})^{-1}$. On a selected component where its degree-one multiplicity survives, the determinant line is instead identified with the inverse determinant of that multiplicity space. These descriptions are compatible through determinant functoriality; they should not be forced into one scalar without choosing bases.

If source and target ranks agree on a torsion block, write

$$
s_v=\det(d)
\tag{9.2}
$$

for the corresponding rational section of $(\mathscr L_v^{\mathrm{pri}})^{-1}$. It vanishes precisely where the specialized map fails to be an isomorphism. At a height-one DVR, the order of vanishing equals the length of the cokernel minus the length of the kernel. This alternating formula remains valid when specialization produces the Tor kernel of (7.3).

### 9.2 Primary--companion duality of determinants

From (6.8) and the determinant rules for duals and shifts, there is an isomorphism of underlying lines

$$
\mathscr L_v^{\mathrm{cmp}}
\simeq\mathscr L_v^{\mathrm{pri}}.
\tag{9.3}
$$

The gradings and factor order are determined by the virtual ranks. Dualizing this isomorphism identifies the companion section of $(\mathscr L_v^{\mathrm{cmp}})^{-1}$ with the transpose of the primary section. Therefore they define the same Fitting divisor.

**Proof.** For a strict two-term model, the companion differential is the transpose of the primary differential under perfect pairings. The determinant of a transpose equals the determinant of the original map after the ordered identifications of the source and target determinant lines. Changing perfect bases multiplies both sides by inverse units, so the section agrees intrinsically. The general statement follows from the quasi-isomorphism invariance of determinants. $\square$

### 9.3 The signed Gram factor

On a primitive rank-one lower branch, choose a primary generator $x$ and its companion dual $x^\dagger$. The signed old vector is $(x,-\varepsilon x)$, and its companion is defined by the adjoint sign. The restriction of the old pairing is multiplication by

$$
c_v^\varepsilon=q_v+1-\varepsilon a_v.
\tag{9.4}
$$

If the companion factor $c_v^{-\varepsilon}$ is a unit, Smith reduction of the full two-by-two Gram matrix gives one nonunit elementary divisor, namely $c_v^\varepsilon$. Hence the signed determinant section and the Gram congruence section agree up to a unit.

The phrase “up to a unit” is unavoidable for chosen generators, but the principal ideal is intrinsic:

$$
\operatorname{Fitt}_0(\operatorname{coker}G_v)^\varepsilon
=(c_v^\varepsilon).
\tag{9.5}
$$

If both signed factors are nonunits, (9.5) is not a statement about the unprojected determinant. One must retain the full Smith module or first prove an integral sign projector.

### 9.4 Fitting ideals and exact lengths

Let $\mathfrak p$ be a height-one prime of a normal component ring and let $A_{\mathfrak p}$ be its DVR. Suppose the localized type complex is generically acyclic and has a square finite free presentation. Then

$$
\operatorname{ord}_{\mathfrak p}(s_v)
=\operatorname{length}_{A_{\mathfrak p}}H^1(C_v)_{\mathfrak p}
-\operatorname{length}_{A_{\mathfrak p}}H^0(C_v)_{\mathfrak p}.
\tag{9.6}
$$

**Proof.** Put the differential in Smith normal form

$$
\operatorname{diag}(\pi^{a_1},\ldots,\pi^{a_r})
$$

after deleting generic zero-rank pieces. If it is generically an isomorphism, there is no free kernel or cokernel. The cokernel length is $\sum a_i$, the kernel is zero, and the determinant valuation is the same sum. More generally, apply the statement to a strict torsion representative of the generically acyclic part; moving a finite kernel across the triangle contributes with the opposite sign. $\square$

Formula (9.6) explains why the Tor term cannot be discarded in a numerical comparison. After a nonflat specialization it contributes in degree zero and subtracts from the determinant length.

## 10. The local deformation component

### 10.1 The enhanced special closure

We now describe the local ring on which the type complex is meant to live. Let $K=F_v$, let $q=q_v$, choose arithmetic Frobenius $\phi$, and choose a tame generator $t$ whose chosen $\ell$-adic tame coordinate is $1$. After removing the fixed scalar finite inertia character $\xi_v$ and the universal scalar twist, a special lift has

$$
\rho(t)=I+N.
$$

The enhanced special closure is defined by the polynomial relations

$$
N^2=0,
\qquad \operatorname{tr}N=0,
\qquad \det N=0,
\qquad \rho(\phi)N\rho(\phi)^{-1}=qN,
\tag{10.1}
$$

together with the fixed determinant, the invariant line, the sign, the scalar finite inertia character, and the chosen tame character $\chi_v$. In geometric-Frobenius notation the factor $q$ in (10.1) is inverted.

The condition $N\ne0$ is not included among the equations. It is open, whereas a deformation condition stable under quotienting coefficients must be closed. The ring $R_v^{\mathrm{sp},2}$ represents the closure containing the conductor-two generic points. Its monodromy-zero boundary is part of the component and has arithmetic meaning.

The line enhancement is necessary at $N=0$. When monodromy is nonzero, its kernel is the invariant line. When $N=0$, the kernel is the whole rank-two module and no line can be recovered from the matrix alone. Retaining the line makes the closure a named component rather than an unlabelled union.

### 10.2 The monodromy-zero boundary

Over the universal enhanced special ring, choose a frame adapted to the invariant line. Then

$$
N^{\mathrm{univ}}=
\begin{pmatrix}0&n_v\\0&0\end{pmatrix}
\tag{10.2}
$$

for an element $n_v$ well defined up to multiplication by a unit. The ideal

$$
\mathfrak n_v=I_1(N^{\mathrm{univ}})=(n_v)
\tag{10.3}
$$

cuts out the monodromy-zero boundary.

At a characteristic-zero special point, $n_v\ne0$. At an Artinian quotient it can vanish. Consequently conductor exponent is not constant on the closed component. The generic points have special conductor, while the boundary can have smaller conductor. This is exactly what permits congruence and level lowering.

The ideal (10.3) is independent of the adapted basis. Conjugation changes the matrix entries by invertible row and column combinations, and $I_1$ is a Fitting ideal. Rescaling the tame coordinate rescales $N$ by a unit and leaves the ideal unchanged.

### 10.3 The conductor-two locus

Let $\chi_v$ be the tautological tame character with values in the fixed-prime character algebra $\Lambda_v$. On a characteristic-zero point $x$, the local special representation is

$$
\operatorname{St}\otimes((\mu_v\chi_{v,x})\circ\det).
\tag{10.4}
$$

If $\chi_{v,x}$ is ramified of conductor one and $N_x\ne0$, its conductor exponent is

$$
a_v=2a(\mu_v\chi_{v,x})=2
\tag{10.5}
$$

in the selected case. If $\chi_{v,x}=1$ and $\mu_v$ is unramified, the exponent is one. Formula (10.5) uses the prepared special-conductor rule; it is not the maximum of two conductors.

After enlarging $E$ so that the character algebra splits, the condition $\chi_{v,x}\ne1$ means the union of the nontrivial-character factors of $\Lambda_v[1/\varpi]$. This union is open and closed in the finite generic character space. The **conductor-two locus** is therefore the open subset

$$
D(n_v)\cap
\{x:\chi_{v,x}\ne1\}
\subseteq\operatorname{Spec}R_v^{\mathrm{sp},2}[1/\varpi].
\tag{10.6}
$$

Let $Z_v^{(2)}$ be the closure of this locus. The universal selected special family also has the augmentation face $Z_v^{(1)}$, on which $\chi_v=1$ and the local datum is the named conductor-one special component. At a finite split character algebra these can be distinct horizontal components meeting in the special fiber; at an Iwasawa limit they are faces of the same relative incidence family. Accordingly, the generic support of the universal type complex is

$$
Z_v^{(2)}[1/\varpi]\cup Z_v^{(1)}[1/\varpi],
\tag{10.6a}
$$

with conductor exponent two on the first part and one on the second. The support theorem concerns the closure of this selected family. Its nontrivial-character open is exactly the conductor-two locus (10.6).

### 10.4 The augmentation point

The augmentation $\epsilon_v:\Lambda_v\to\mathcal O$ sends $\chi_v$ to $1$. By the clean local comparison, it induces a cartesian specialization of represented enhanced conditions

$$
R_v^{\mathrm{sp},2}
\widehat\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\xrightarrow{\sim}
R_v^{\mathrm{sp},1}.
\tag{10.7}
$$

The sign, invariant line, determinant, and scalar finite inertia character survive. The monodromy parameter does not have to vanish: augmentation removes the ramified tame twist and returns the conductor-one special component, whose generic monodromy is still nonzero.

This is why the minimal datum at $v$ was chosen to be minimal special rather than arbitrary unramified. An arbitrary spherical deformation does not lie in the augmented special closure. Without (10.7) there is no well-typed local map and no exact global augmentation theorem.

## 11. Component support

### 11.1 Support of a perfect complex

For a bounded complex $C$ with finitely generated cohomology over a noetherian ring $A$, define

$$
\operatorname{Supp}_A(C)
=\bigcup_i\operatorname{Supp}_A H^i(C).
\tag{11.1}
$$

This is closed. If $C$ is perfect, derived Nakayama gives the equivalent fiber description

$$
\operatorname{Supp}_A(C)
=\{\mathfrak p:C\otimes_A^L\kappa(\mathfrak p)\not\simeq0\}.
$$

A strict finite projective representative is acyclic precisely where suitable minors of its differentials become units, so acyclicity is open.

For a perfect complex, formation of support commutes with arbitrary scalar extension in the following set-theoretic sense:

$$
\operatorname{Supp}_B(C\otimes_A^LB)
=\{\mathfrak q\in\operatorname{Spec}B:
\mathfrak q\cap A\in\operatorname{Supp}_A(C)}.
\tag{11.2}
$$

To prove (11.2), tensor further with $\kappa(\mathfrak q)$. Associativity gives the fiber of $C$ at the contracted prime followed by field extension. A finite-dimensional complex over a field is acyclic if and only if it remains acyclic after a field extension.

### 11.2 Generic support from local type occurrence

Let $A^{\mathrm{aut}}$ be the faithful acting order on the one-prime automorphic complex, and let

$$
A_E^{\mathrm{aut}}=\prod_xE_x
$$

be its reduced generic algebra. Every factor corresponds to a characteristic-zero automorphic packet. By (6.5),

$$
C_v^{\mathrm{pri}}\otimes E_x\not\simeq0
\quad\Longleftrightarrow\quad
\Pi_{x,v}\text{ belongs to the selected special family}.
\tag{11.3}
$$

**Proposition 11.1 (generic support).** The generic support of the primary type complex is exactly the set of selected special automorphic branches: the conductor-two branches on nontrivial tame-character factors together with the named minimal-special branches on the augmentation factor. On each such branch its only cohomology is the appropriate type multiplicity space in degree one.

**Proof.** Integral type occurrence gives the local packet label on every generic branch. Full local--global compatibility identifies that label with the enhanced special Weil--Deligne parameter, including its tame character and nonzero monodromy. Local type multiplicity says the primary Hom is zero off the selected label and is the distinguished multiplicity space on it. Saturated Ihara injectivity eliminates degree zero. This is precisely (11.3) with the asserted concentration. $\square$

This theorem uses every generic factor of the faithful order. Checking one eigenpacket would prove only that one point lies in the support.

### 11.3 Closure and full selected-component support

Let $Z_v^{\mathrm{aut}}$ be the union, inside $\operatorname{Spec}A^{\mathrm{aut}}$, of the closures of the selected generic branches.

**Theorem 11.2 (component support).** One has

$$
\operatorname{Supp}_{A^{\mathrm{aut}}}(C_v^{\mathrm{pri}})
=Z_v^{\mathrm{aut}}.
\tag{11.4}
$$

The same equality holds for the companion complex.

**Proof strategy.** The support is closed, so it contains the closure of every selected generic point. Conversely, coefficient freeness of the surviving cohomology rules out a component supported only in the special fiber. Thus every generic point of the support is visible in characteristic zero.

**Proof.** Proposition 11.1 shows that every selected generic point belongs to the support. Closedness gives

$$
Z_v^{\mathrm{aut}}\subseteq\operatorname{Supp}(C_v^{\mathrm{pri}}).
$$

For the reverse inclusion, take an irreducible component $W$ of the support and its generic point $\eta$. By Theorem 7.1 the support is the support of the $\mathcal O$-free module $H^1(C_v^{\mathrm{pri}})$. Multiplication by $\varpi$ is injective on this module, so $\varpi$ belongs to none of its associated primes. In particular, $\varpi\notin\eta$, because the generic points of the irreducible components of a finite module's support are associated primes. Hence $\eta$ lies in the generic fiber. Proposition 11.1 makes it a selected branch, so $W$ lies in $Z_v^{\mathrm{aut}}$. This proves equality. Companion duality identifies its surviving cohomology with the $\mathcal O$-dual of the primary cohomology, which is again $\mathcal O$-free, and gives the companion assertion. $\square$

If a local deformation ring $R$ maps finitely to the acting order, the support viewed in $\operatorname{Spec}R$ is the closed image, under contraction, of the selected automorphic component union. If one subsequently makes a scalar extension of a perfect $R$-model, (11.2) gives its inverse image on the new spectrum. These directions are different. The theorem does not claim that every component of the unrestricted local deformation ring is automorphic.

### 11.4 Topological support is not faithfulness

Equation (11.4) is a statement about underlying closed sets. It gives

$$
\sqrt{\operatorname{Ann}_{A^{\mathrm{aut}}}H^*(C_v)}
=I(Z_v^{\mathrm{aut}})_{\mathrm{red}}.
\tag{11.5}
$$

It does not identify the annihilator itself. If the selected component ring is nonreduced, a nilpotent element can annihilate the complex while vanishing at every generic point.

The example

$$
A=k[\epsilon]/(\epsilon^2),
\qquad C=k[0]
$$

has full support but annihilator $(\epsilon)$. Thus no argument in this chapter calls full support “faithfulness.” In the later one-prime patch, depth and a sharp dimension comparison must eliminate nilpotent annihilators. The present theorem supplies the component coverage needed to make that later argument possible.

## 12. Saturation on the selected component

### 12.1 Height-one tests

Let $A$ be a reduced noetherian ring whose selected components are normal in codimension one. Let $L\subset V$ be two finite $A$-modules that become equal after tensoring with the total quotient ring, with $L$ and $V$ torsion free. The quotient $V/L$ is supported in codimension at least one. It vanishes if and only if it vanishes at every height-one prime and has no codimension-at-least-two contribution under an additional reflexivity hypothesis.

For the present lattice comparison we need only the height-one statement.

**Lemma 12.1.** If $A_{\mathfrak p}$ is a DVR and $L_{\mathfrak p}\subset V_{\mathfrak p}$ are lattices with the same generic fiber, then the following are equivalent:

1. $L_{\mathfrak p}=V_{\mathfrak p}$;
2. the inclusion has determinant valuation zero;
3. $(V/L)_{\mathfrak p}=0$;
4. the inclusion remains injective with full rank modulo the height-one uniformizer.

**Proof.** Smith normal form writes the inclusion as $\operatorname{diag}(\pi^{a_1},\ldots,\pi^{a_r})$. The four conditions all say $a_i=0$ for every $i$. $\square$

The lemma is applied to compare the geometric primitive type lattice with any lattice produced by a chosen presentation. It is not applied to the Gram map, whose nonzero valuations encode genuine congruences.

### 12.2 Elimination of type-lattice indices

Let $L^{\mathrm{geom}}$ be the primitive type lattice obtained from the incidence geometry and let $L^{\mathrm{alg}}$ be the lattice obtained from an integral type presentation. The primary--companion pairing puts both inside the same generic multiplicity space and their duals inside the companion space.

**Proposition 12.2 (no type index).** Under the clean primitive pairing hypotheses,

$$
L^{\mathrm{geom}}=L^{\mathrm{alg}}
$$

on the selected component.

**Proof.** Both lattices are saturated submodules of the same ambient finite free module and have the same generic type subspace by local type occurrence. Lemma 5.1 already gives equality. To see the determinant content, localize at a height-one prime. Perfect primary--companion pairing makes the determinant of one inclusion the inverse of the determinant of its companion inclusion. Both inclusions are integral, so both valuations are nonnegative; their sum is zero. Each is therefore zero, and Lemma 12.1 gives equality. The global primitive-intersection argument removes any possible codimension-two discrepancy. $\square$

The proof explains why the companion lattice is more than bookkeeping. Without it, one inclusion could have a positive determinant valuation with no integral inverse comparison.

### 12.3 Component groups remain separate

The semistable graph lattice has its own injection

$$
q_\Gamma:X_v\longrightarrow X_v^\vee.
\tag{12.1}
$$

Its cokernel is

$$
\Phi_v[\ell^\infty]\otimes_{\mathbf Z_\ell}\mathcal O.
\tag{12.2}
$$

Proposition 12.2 does not make (12.2) vanish. The type lattice and graph lattice have been identified with the same primitive scale, but the monodromy pairing can remain nonunimodular on that scale.

Likewise the signed Gram cokernel

$$
\operatorname{coker}(G_v)^\varepsilon
$$

can remain nonzero. It measures the old lattice against its dual, not the type lattice against its saturation. The three finite modules are therefore:

$$
\begin{array}{c|c}
\text{module}&\text{meaning}\cr\hline
L^{\mathrm{sat}}/L&\text{type or old saturation defect}\cr
\operatorname{coker}(G_v)&\text{old--new congruence}\cr
\operatorname{coker}(q_\Gamma)&\text{Néron component group.}
\end{array}
\tag{12.3}
$$

The first vanishes in the clean theorem. The other two need not.

### 12.4 The saturation theorem

**Theorem 12.3 (selected-component saturation).** For the clean one-prime datum:

1. the old primary image in the upper primary type lattice is saturated over $\mathcal O$;
2. the quotient-new primary lattice is finite free over $\mathcal O$;
3. primary and companion quotient-new lattices are perfect duals;
4. the geometric, type-theoretic, and inner-form multiplicity lattices have no mutual finite index;
5. after localization at every height-one point of the selected component, the only possible nonunit determinant factors are the signed Gram factor, the local monodromy factor, and the graph component factor explicitly displayed above.

**Proof.** The first two assertions are (8.5). The third is the right vertical isomorphism in (8.6). The fourth combines Proposition 12.2 with the integral graph-to-definite lattice comparison, which identifies faithful orders and primitive edge bases. At height one, any additional index would appear as a positive elementary-divisor valuation of one of these inclusions. Perfect companion duality supplies an integral inverse inclusion, forcing that valuation to be both nonnegative and nonpositive. It is zero. The remaining factors arise from maps to dual lattices rather than from competing choices of the same lattice, so the argument does not remove them. $\square$

## 13. Exact augmentation

### 13.1 Derived augmentation

Let $\epsilon_v:\Lambda_v\to\mathcal O$ be the fixed-prime tame augmentation. The correct specialization is

$$
C_{Q,v}^{\mathrm{pri}}
\otimes_{\Lambda_v,\epsilon_v}^L\mathcal O.
\tag{13.1}
$$

Termwise type compatibility supplies a morphism

$$
\alpha_Q:
C_{Q,v}^{\mathrm{pri}}
\otimes_{\Lambda_v}^L\mathcal O
\longrightarrow C_Q^{\min,\mathrm{sp}},
\tag{13.2}
$$

where the target is the minimal conductor-one special degeneracy/type complex. The map preserves the away Hecke action, the sign, the invariant line, and the determinant.

The terms of $C_{Q,v}^{\mathrm{pri}}$ are projective over $\Lambda_v$, so the left side of (13.2) is represented by ordinary termwise tensor product. This does not yet imply that its cohomology is the tensor product of the original cohomology.

### 13.2 Vanishing of the augmentation Tor term

**Theorem 13.1 (augmentation Tor vanishing).** One has

$$
\operatorname{Tor}_1^{\Lambda_v}
\left(H^1(C_{Q,v}^{\mathrm{pri}}),\mathcal O\right)=0.
\tag{13.3}
$$

**Proof strategy.** The universal coefficient sequence identifies this Tor group with the degree-zero cohomology after augmentation. The augmented chain map is the minimal special degeneracy map, which is injective by the established saturated theorem.

**Proof.** Since $H^0(C_{Q,v}^{\mathrm{pri}})=0$, equation (7.3) gives

$$
H^0(C_{Q,v}^{\mathrm{pri}}
\otimes_{\Lambda_v}^L\mathcal O)
\simeq
\operatorname{Tor}_1^{\Lambda_v}
(H^1(C_{Q,v}^{\mathrm{pri}}),\mathcal O).
\tag{13.4}
$$

Termwise augmentation of the conductor-two type and its companion is the minimal conductor-one special type. Under this identification, the specialized differential is the minimal special degeneracy differential. Its residual map is injective by saturated Ihara theory in the retained non-Eisenstein localization. Hence its integral kernel is zero. The left side of (13.4) vanishes, proving (13.3). $\square$

The proof does not assume that $H^1$ is flat over $\Lambda_v$. It proves exactly the Tor vanishing needed for this augmentation. Nor does it use a nonminimal deformation--Hecke equality.

### 13.3 Recovery of the minimal complex

**Theorem 13.2 (exact augmentation).** The map (13.2) is a quasi-isomorphism. Consequently

$$
H^1(C_{Q,v}^{\mathrm{pri}})
\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\xrightarrow{\sim}
H^1(C_Q^{\min,\mathrm{sp}}),
\tag{13.5}
$$

and no degree-zero correction occurs.

**Proof.** The termwise augmentation theorem for primary type lattices identifies the two terms and differential of the source of (13.2) with those of the target. Thus (13.2) is an isomorphism of the displayed two-term models. Theorem 13.1 shows that its source has no unexpected degree-zero cohomology. Equation (7.4) identifies degree-one cohomology with the ordinary tensor product, giving (13.5). $\square$

This theorem is stronger than equality after inverting $\varpi$ and stronger than equality of residual semisimplifications. It identifies the full integral generalized eigenspaces and the chain map that produces them.

### 13.4 Ring, module, pairing, and determinant control

Let $\mathbb T_{Q,v}^{(2)}$ be the faithful image acting on the conductor-two type complex, defined as the image on total cohomology, and let $\mathfrak a_v=\ker\epsilon_v$. Exact augmentation gives

$$
\mathbb T_{Q,v}^{(2)}/\mathfrak a_v\mathbb T_{Q,v}^{(2)}
\xrightarrow{\sim}\mathbb T_Q^{\min,\mathrm{sp}}.
\tag{13.6}
$$

The point requiring proof is injectivity: exact specialization of a faithful module does not by itself imply exact specialization of its image algebra.

**Lemma 13.3 (base change of a saturated acting image).** Let $\Lambda\to B=\Lambda/\mathfrak a$ be a quotient, let $P$ be a finite $\Lambda$-module, and let $T\subseteq\operatorname{End}_\Lambda(P)$ be a finite subalgebra. If

$$
T\cap
\ker\bigl(\operatorname{End}_\Lambda(P)
\to\operatorname{End}_B(P/\mathfrak aP)\bigr)
=\mathfrak aT,
\tag{13.6a}
$$

then the natural map

$$
T/\mathfrak aT\longrightarrow\operatorname{End}_B(P/\mathfrak aP)
$$

is injective, and its image is the algebra generated by the specialized operators.

**Proof.** The kernel of the displayed map from $T/\mathfrak aT$ consists exactly of the classes of elements in the intersection on the left side of (13.6a). The hypothesis identifies that intersection with $\mathfrak aT$, so the kernel is zero. Every element of the image is visibly the specialization of an element of $T$, and every specialized generator occurs, proving the final assertion. $\square$

Apply the lemma to the direct sum of the surviving primary and companion cohomology modules. Condition (2.2) supplies (13.6a). Theorems 13.1 and 13.2 and companion duality identify its specialization with the corresponding minimal direct sum. Lemma 6.1 identifies the specialized named Hecke operators with their minimal-special operators, and the latter generate $\mathbb T_Q^{\min,\mathrm{sp}}$ by definition of the faithful image. This proves (13.6). Notice that acting-image saturation, rather than Tor vanishing alone, is the ingredient that rules out an extra algebra kernel.

Primary--companion pairings specialize perfectly:

$$
\left(
H^1(C_{Q,v}^{\mathrm{pri}}),
H^0(C_{Q,v}^{\mathrm{cmp}}),
\langle\ ,\ \rangle^{(2)}
\right)
\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\simeq
\left(
H^1(C_Q^{\min,\mathrm{sp}}),
H^0(C_Q^{\min,\mathrm{sp},\mathrm{cmp}}),
\langle\ ,\ \rangle^{\min}
\right).
\tag{13.7}
$$

Determinant lines commute with the derived base change:

$$
\operatorname{Det}(C_{Q,v}^{\mathrm{pri}})
\otimes_{\Lambda_v}\mathcal O
\xrightarrow{\sim}
\operatorname{Det}(C_Q^{\min,\mathrm{sp}}).
\tag{13.8}
$$

Because the Tor group vanishes, the determinant of cohomology calculated from (13.8) has no extra degree-zero factor. This is the determinant form of exact augmentation.

## 14. Compatibility with Taylor--Wiles patching

### 14.1 Fixed-prime complexes at varying auxiliary level

Let $Q_N$ be the Taylor--Wiles sets used in the minimal comparison. They are disjoint from $v$. At every $N$ the fixed-prime construction gives

$$
C_{N,v}^{\mathrm{pri}}
=[P_{N,v}^0\to P_{N,v}^1]
\tag{14.1}
$$

over the auxiliary group ring $\Lambda_N$ and the fixed-prime character algebra $\Lambda_v$. Each term is finite free of a rank independent of $N$ over $\Lambda_N$ after primary localization. The fixed-prime amplitude remains $[0,1]$.

The two group algebras play different roles:

$$
\begin{array}{c|c|c}
\text{algebra}&\text{origin}&\text{augmentation}\cr\hline
\Lambda_N&\text{Taylor--Wiles primes }Q_N&\epsilon_Q:\Lambda_N\to\mathcal O\cr
\Lambda_v&\text{fixed conductor-two prime }v&\epsilon_v:\Lambda_v\to\mathcal O.
\end{array}
\tag{14.2}
$$

Auxiliary augmentation changes no local condition at $v$. Fixed-prime augmentation changes conductor two to conductor one and changes no Taylor--Wiles condition. The two derived tensor products commute because they act through different coefficient factors.

### 14.2 Finite shadows and coherent limits

The sets $Q_N$ are not nested. Therefore the complexes (14.1) have no arithmetic transition maps. Patch them through finite marked shadows. At every precision retain:

- both terms and the differential;
- bases over the finite auxiliary group ring;
- the fixed-prime character action;
- primary and companion idempotent data;
- the pairing of complexes;
- away and fixed-prime Hecke operators;
- both augmentation diagrams;
- determinant-line generators and transition isomorphisms.

Only finitely many such diagrams exist at fixed precision because every ring and module involved is finite. A diagonal infinite path produces compatible shadow transitions. Inverse limits then give a patched perfect complex

$$
C_{\infty,v}^{\mathrm{pri}}
=[P_{\infty,v}^0\to P_{\infty,v}^1]
\tag{14.3}
$$

over the patched auxiliary power-series ring $S_\infty$ together with the fixed-prime algebra.

Marking the differential is essential. Patching $H^1$ alone would discard the extension class and would provide no object from which to recover the Tor term after fixed-prime augmentation.

### 14.3 Patched amplitude and support

**Theorem 14.1 (patched one-prime complex).** The complex (14.3) is perfect of Tor amplitude $[0,1]$. Its primary--companion duality, Hecke adjunction, determinant line, and selected-component support are the inverse limits of the finite-level structures. Its support is the pullback of the selected fixed-prime component union to the patched spectrum.

**Proof.** The marked finite shadows have two finite free terms of uniformly bounded, eventually constant ranks. Compatible bases lift to finite free $S_\infty$-modules, so (14.3) is a strict perfect two-term complex. Pairing matrices invert at every finite precision and hence in the limit. The determinant construction commutes with inverse limits of the chosen finite free models.

For support, take a prime of the patched ring and specialize to its residue field. The fiber of (14.3) is the stable fiber of sufficiently precise finite shadows. Type occurrence makes it nonzero exactly when the contracted fixed-prime point lies on the selected component. Equation (11.2) gives the asserted pullback description. $\square$

### 14.4 Augmentation after patching

There are canonical quasi-isomorphisms

$$
C_{\infty,v}^{\mathrm{pri}}
\otimes_{\Lambda_v,\epsilon_v}^L\mathcal O
\simeq C_\infty^{\min,\mathrm{sp}},
\tag{14.4}
$$

and

$$
C_{\infty,v}^{\mathrm{pri}}
\otimes_{S_\infty,\epsilon_Q}^L\mathcal O
\simeq C_v^{\mathrm{pri}}.
\tag{14.5}
$$

The two augmentations commute:

$$
\left(C_{\infty,v}^{\mathrm{pri}}
\otimes_{\Lambda_v}^L\mathcal O\right)
\otimes_{S_\infty}^L\mathcal O
\simeq
\left(C_{\infty,v}^{\mathrm{pri}}
\otimes_{S_\infty}^L\mathcal O\right)
\otimes_{\Lambda_v}^L\mathcal O.
\tag{14.6}
$$

**Proof.** Both quasi-isomorphisms hold at every finite shadow by exact augmentation and group-ring freeness. The transition maps are surjective, so kernels satisfy the Mittag--Leffler condition and inverse limits preserve the exact triangles. Associativity of derived tensor product gives (14.6). No ordinary-cohomology interchange is used until Theorem 13.1 has killed the fixed-prime Tor term. $\square$

Equation (14.4) is the exact compatibility needed in the next patching argument. It says that adding the fixed conductor-two component and then augmenting returns the already understood minimal patched complex, with no hidden cohomological degree.

## 15. Exact numerical comparisons

### 15.1 The determinant divisor

Let $B$ be a normal domain occurring as a selected component of the fixed-prime acting ring, and assume the type complex is generically acyclic after removing its surviving multiplicity line. Its determinant trivialization, viewed as the section $s_v$ of the dual determinant line as in Section 9.1, defines a height-one divisor

$$
\operatorname{div}(s_v)
=\sum_{\operatorname{ht}\mathfrak p=1}
\operatorname{ord}_{\mathfrak p}(s_v)[\mathfrak p].
\tag{15.1}
$$

At each height-one point, (9.6) calculates the coefficient as an alternating cohomology length. Because selected-component saturation removes every lattice index, the coefficient has only two possible sources: degeneration of the signed old pairing and degeneration of the enhanced special local equation.

To make this precise, let $\mathscr L_v^{\mathrm{loc}}$ be the determinant of the relative cotangent complex of the enhanced conductor-two component over its tame character base. The local equations (10.1), together with the line and determinant constraint, give a perfect two-term cotangent model. Local--global compatibility differentiates the same inertia, Frobenius, line, and monodromy relations on the automorphic type complex. Hence there is a determinant comparison

$$
\iota_v:\mathscr L_v^{\mathrm{loc}}
\xrightarrow{\sim}
\bigl(\mathscr L_v^{\mathrm{pri}}\bigr)^{-1}
\otimes\mathscr L_v^{\min}.
\tag{15.2}
$$

The inverse on the primary line is essential. The local cotangent complex lies in degrees $-1,0$, so its Jacobian is a section of its determinant line. The automorphic type complex lies in degrees $0,1$, so its differential is a section of the dual determinant line. The factor order is then fixed by the transitivity triangle for conductor-two to minimal augmentation.

We justify the word “hence.” At a selected characteristic-zero branch $x$, let

$$
D_x^{\mathrm{loc}}=[U_x\xrightarrow{J_x}V_x]
$$

be the linearization of the fixed-determinant equations in (10.1), including the chosen line and tame character, after quotienting the framing directions. Let $D_x^{\mathrm{aut}}$ be the relative automorphic incidence complex obtained by dividing the conductor-two type complex by its augmented minimal multiplicity line. A first-order deformation of an automorphic eigenpacket supplies a matrix $\rho_x+\epsilon A$, a line $L_x+\epsilon L'_x$, a tame character $\chi_x(1+\epsilon\kappa)$, and a monodromy matrix $N_x+\epsilon N'_x$. Differentiating the four relations in (10.1) gives

$$
NN'+N'N=0,qquad
\operatorname{tr}N'=0,qquad
d(\det)_N(N')=0,
$$

and

$$
A(\phi)N-N A(\phi)
+\rho(\phi)N'\rho(\phi)^{-1}
-qN'=0,
\tag{15.2a}
$$

after transporting tangent matrices to the chosen frame. These are exactly the linear relations imposed by the two degeneracy correspondences and their norm adjoints on the selected type multiplicity. Thus local--global compatibility gives a chain isomorphism

$$
D_x^{\mathrm{loc}}\xrightarrow{\sim}D_x^{\mathrm{aut}}
\tag{15.2b}
$$

on every selected generic branch.

To descend (15.2b) integrally, localize the component ring at a height-one prime. Clean condition 13 places the two complexes in the same generic tangent and relation spaces as primitive lattices. Lemma 5.1 identifies the corresponding term lattices. Equivalently, the determinant of the comparison has nonnegative valuation from the primary incidence map, while the adjoint companion incidence map gives its inverse and hence the opposite inequality. Its valuation is zero. The determinant comparison therefore extends across every height-one point. Both sides of (15.2) are reflexive rank-one modules on the normal component, so they are the intersection of their height-one localizations inside the common generic line. The height-one maps consequently glue uniquely to (15.2). This proves the determinant-line comparison without assuming an equality of nonminimal deformation and Hecke rings.

**Proposition 15.1 (integral section comparison).** Under (15.2), the local Jacobian section maps to the quotient of the conductor-two type section by the minimal type section, up to a unit. No additional height-one divisor occurs.

**Proof strategy.** The equality holds on every characteristic-zero branch by the explicit special parameter and pull--norm Gram calculation. Their ratio is therefore a rational unit. Height-one saturation proves that it has valuation zero everywhere.

**Proof.** Choose a height-one prime $\mathfrak p$ of $B$. The localization $B_{\mathfrak p}$ is a DVR. On its fraction field, the linearized enhanced special equations and the type multiplicity complex describe the same one-dimensional local deformation direction, so their determinant sections differ by a scalar $u\in\operatorname{Frac}(B_{\mathfrak p})^\times$. The primary comparison makes $u$ integral. Applying the companion comparison gives the inverse scalar and makes $u^{-1}$ integral. Therefore $u$ is a unit in $B_{\mathfrak p}$. This holds at every height-one prime. Normality identifies a rational function with nonnegative valuations for it and its inverse as a global unit on the local component. $\square$

This proof is the determinant version of Proposition 12.2. It is invalid without the companion lattice: one would know only that the ratio is integral, not that its inverse is integral.

### 15.2 Cotangent, type, and congruence modules

Fix a generically isolated integral augmentation

$$
\lambda:B\longrightarrow\mathcal O
$$

on the selected component. Let $\mathfrak p_\lambda=\ker\lambda$. Define

$$
\Phi_B=\mathfrak p_\lambda/\mathfrak p_\lambda^2
\tag{15.3}
$$

and let $\Psi_v^{\mathrm{type}}$ be the finite module measuring failure of the primary and companion branch lattices to split from the other generic branches. If the generic algebra splits with selected idempotent $e_\lambda$, the ring congruence ideal is

$$
\eta_\lambda
=\{a\in\mathcal O:a e_\lambda\in B\}.
\tag{15.4}
$$

The three modules have different definitions:

$$
\Phi_B\text{ linearizes equations},
\qquad
\Psi_v^{\mathrm{type}}\text{ linearizes a lattice splitting},
\qquad
\mathcal O/\eta_\lambda\text{ linearizes a branch splitting}.
$$

They agree numerically only under square-presentation, primitive multiplicity, and determinant-comparison hypotheses.

Suppose locally at $\lambda$ the selected component has a square complete-intersection presentation

$$
B\simeq
\mathcal O[[X_1,\ldots,X_g]]/(f_1,\ldots,f_g),
\qquad \lambda(X_i)=0.
\tag{15.5}
$$

Let

$$
J_\lambda=
\left(\lambda\left(\frac{\partial f_i}{\partial X_j}\right)\right)_{i,j}.
\tag{15.6}
$$

Then

$$
\operatorname{Fitt}_0^{\mathcal O}(\Phi_B)
=(\det J_\lambda).
\tag{15.7}
$$

If $B$ is finite flat over $\mathcal O$, generically étale at the isolated branch, and the displayed complete-intersection presentation is valid at $\lambda$, then the branch congruence ideal satisfies the sharper identity

$$
\eta_\lambda
=\operatorname{Fitt}_0^{\mathcal O}(\Phi_B)
=(\det J_\lambda).
\tag{15.7a}
$$

This equality is not true for an arbitrary finite flat ring without the complete-intersection duality hypothesis.

**Lemma 15.2 (complete-intersection congruence identity).** Under the hypotheses just stated, (15.7a) holds.

**Proof.** Put $\mathfrak p=\ker\lambda$. Because the generic branch is isolated, the selected idempotent $e_\lambda$ exists in $B_E$. Multiplication identifies

$$
\eta_\lambda
=\lambda(\operatorname{Ann}_B\mathfrak p).
\tag{15.7b}
$$

Indeed, if $b\mathfrak p=0$, then $b$ vanishes on every generic branch other than $\lambda$, so $b=\lambda(b)e_\lambda$ in $B_E$ and $\lambda(b)\in\eta_\lambda$. Conversely, $ae_\lambda\in B$ annihilates $\mathfrak p$ and has augmentation $a$.

It remains to calculate the right side. The conormal sequence of (15.5), evaluated at $\lambda$, is

$$
\mathcal O^g\xrightarrow{J_\lambda}\mathcal O^g
\longrightarrow\mathfrak p/\mathfrak p^2\longrightarrow0.
\tag{15.7c}
$$

The Koszul complex on $f_1,\ldots,f_g$ is a self-dual resolution because the sequence is regular. After applying $\operatorname{Hom}(-,\mathcal O)$ along $\lambda$, its top differential is the top exterior power of (15.7c), hence multiplication by $\det J_\lambda$. Self-duality identifies the resulting top annihilator with $\lambda(\operatorname{Ann}_B\mathfrak p)$. Therefore

$$
\lambda(\operatorname{Ann}_B\mathfrak p)=(\det J_\lambda).
$$

Together with (15.7b), this gives (15.7a). The same Koszul presentation gives $\operatorname{Fitt}_0(\Phi_B)=(\det J_\lambda)$, so all three ideals agree. $\square$

The determinant comparison identifies $(\det J_\lambda)$ with the intrinsic type determinant ideal. If the automorphic multiplicity on the branch is $m$ and the primary and companion multiplicity lattices are primitive, then

$$
\operatorname{Fitt}_0^{\mathcal O}(\Psi_v^{\mathrm{type}})
=(\det J_\lambda)^m
=\eta_\lambda^m.
\tag{15.8}
$$

**Proof.** The conormal sequence for (15.5) gives the presentation

$$
\mathcal O^g\xrightarrow{J_\lambda}\mathcal O^g
\to\Phi_B\to0,
$$

which proves (15.7). Proposition 15.1 identifies the determinant of this presentation with the type determinant. A primitive multiplicity-$m$ branch is a direct sum of $m$ copies after passing to the selected generic factor, and the primary--companion pairing makes the integral determinant the $m$th tensor power without another discriminant. Fitting ideals of the resulting block presentation multiply, giving (15.8). $\square$

Equation (15.8) does not assert $B$ equals a deformation ring. It compares intrinsic determinants on the already selected acting component. The later one-prime comparison must still prove that the universal deformation ring acts faithfully on that component.

### 15.3 A discrete-valuation calculation

Let $\mathcal O_\lambda$ be a DVR dominating the branch and suppose the lower multiplicity is one. Put

$$
a_v=\lambda(T_v),
\qquad
c_v^\varepsilon=q_v+1-\varepsilon a_v.
$$

Assume $c_v^{-\varepsilon}$ is a unit. Then the signed old Gram module is

$$
\mathcal C_v^\varepsilon
\simeq\mathcal O_\lambda/(c_v^\varepsilon),
\tag{15.9}
$$

and

$$
\operatorname{length}_{\mathcal O_\lambda}
\mathcal C_v^\varepsilon
=v_\lambda(c_v^\varepsilon).
\tag{15.10}
$$

If the augmented local presentation is square and generically isolated, Proposition 15.1 gives

$$
v_\lambda(\det J_\lambda)
=v_\lambda(c_v^\varepsilon).
\tag{15.11}
$$

If the automorphic multiplicity is $m$, then

$$
\operatorname{length}_{\mathcal O_\lambda}
\Psi_v^{\mathrm{type}}
=m\,v_\lambda(c_v^\varepsilon).
\tag{15.12}
$$

Under the finite-flat complete-intersection hypotheses of Lemma 15.2, the full comparison can be written in one line:

$$
\operatorname{length}_{\mathcal O_\lambda}\Phi_B
=\operatorname{length}_{\mathcal O_\lambda}(\mathcal O_\lambda/\eta_\lambda)
=v_\lambda(c_v^\varepsilon),
\qquad
\operatorname{length}_{\mathcal O_\lambda}\Psi_v^{\mathrm{type}}
=m\,v_\lambda(c_v^\varepsilon).
\tag{15.12a}
$$

**Proof of (15.9)--(15.12a).** Since $2$ is a unit, the signed basis diagonalizes the symmetric Gram matrix. Its two diagonal entries are $c_v^\varepsilon$ and $c_v^{-\varepsilon}$. The second is a unit, so Smith normal form leaves the first as the only nontrivial elementary divisor. This proves (15.9)--(15.10). Determinant comparison proves (15.11), and the $m$-copy determinant calculation proves (15.12). Finally, (15.7a) identifies the same principal ideal with the Fitting ideals of $\Phi_B$ and $\mathcal O_\lambda/\eta_\lambda$; length over a DVR is the valuation of that ideal. This proves (15.12a). $\square$

The calculation is exact, not only an inequality. Its hypotheses explain every possible correction:

- a nonprimitive old lattice would add a saturation length;
- a nonprimitive type lattice would add a type index;
- a nonunit companion factor would add another elementary divisor;
- a nonzero augmentation Tor module would subtract its length in the determinant Euler characteristic;
- a nonprimitive multiplicity pairing would add its discriminant.

All but the companion-factor exception have been eliminated by the clean theorem.

### 15.4 Multiplicity and companion discriminants

At higher multiplicity one must not infer elementary divisors from a determinant alone. Let $A$ be the matrix of the signed pairing on a rank-$m$ branch. Then

$$
\operatorname{Fitt}_0(\operatorname{coker}A)=(\det A),
$$

and the valuation of $\det A$ is the sum of the elementary-divisor valuations. It does not say the cokernel is cyclic or a direct sum of $m$ equal cyclic modules.

The scalar formula (15.12) requires the pairing matrix to be equivalent to $c_v^\varepsilon I_m$. Primitive primary--companion multiplicity and a free rank-$m$ module over the common branch order give this form. Without that freeness, the correct statement is

$$
\operatorname{length}\Psi_v^{\mathrm{type}}
=m\,v(c_v^\varepsilon)+v(\mathfrak d_{\mathrm{mult}}),
\tag{15.13}
$$

where $\mathfrak d_{\mathrm{mult}}$ is the determinant ideal of the residual companion pairing. The clean primitive multiplicity hypothesis says $\mathfrak d_{\mathrm{mult}}=(1)$.

This distinction mirrors the minimal theorem: freeness of an automorphic module may have rank $m>1$, while the Gorenstein dualizing module has rank one. Nothing in the one-prime determinant calculation forces automorphic multiplicity one.

## 16. Exceptional cases and theorem boundaries

### 16.1 Eisenstein and reducible systems

At an Eisenstein maximal ideal the tree character module can survive. The residual degeneracy map can then have a genuine kernel, the old image can be nonsaturated, and the quotient can contain coefficient torsion. In that situation the degree-zero cohomology of the type complex exists before any base change and cannot be identified with the augmentation Tor term alone.

If $\bar\rho$ is reducible, good Frobenius traces do not determine an integral rank-two family or its extension class. The Hecke-valued reciprocity map used to place the type complex on a deformation component is unavailable in the stated form. A pseudorepresentation or an ordinary filtered deformation problem may still be possible, but its type complex has different support and duality.

The words “non-Eisenstein” and “absolutely irreducible” are not interchangeable. Non-Eisensteinness kills the geometric tree kernel. Absolute irreducibility constructs and controls the global Galois representation. The clean theorem assumes both where each is needed.

### 16.2 Colliding roots and signs

If $q_v\equiv1\pmod\ell$, the two old Frobenius roots coincide. The full two-map degeneracy image can remain saturated, but an ordered root is not recovered by integral idempotents. A primary type requiring that ordering is extra structure, and augmentation need not forget it uniquely.

If $q_v\equiv-1\pmod\ell$, the two signed Gram factors can both be nonunits. The full Gram matrix and type complex remain valid, but (15.9) is false without a separately proved integral sign block. The determinant valuation is then the sum of at least two elementary-divisor valuations.

If $\ell=2$, the signs agree and $(1\pm W_v)/2$ is unavailable. Branch reversal also loses its sign on graph chains. The present construction begins at $\ell\geq7$ and makes no two-adic assertion.

### 16.3 Small coefficient primes and stabilizers

The bound $\ell\geq7$ is inherited for two independent reasons. First, the minimal global theorem uses adequacy and regular-semisimple detection in that range. Second, the available saturated level-change and type-lattice packages use prime-to-$\ell$ stabilizers and clean sign separation.

At $\ell=3$ or $5$, a fine-level version of some local statements can remain true. Nevertheless stabilizer orders, tame normalizers, type reductions, and the exceptional icosahedral image at five require separate verification. No statement here lowers the global prime bound merely because the two-term homological algebra works at smaller primes.

If a neat cover has deck group $\Delta$ with $\ell\mid|\Delta|$, invariants are not exact. A primitive image upstairs can become nonprimitive downstairs, and group cohomology of $\Delta$ can enter degree zero. The exact-augmentation proof then needs a stack-level replacement; averaging is not available.

### 16.4 Nonreduced components and wild types

The support theorem remains a topological statement over a nonreduced selected component. It cannot kill a nilpotent annihilator. Generic-point determinant comparison also cannot see a nilpotent generic direction if the generic fiber itself is nonreduced. The clean theorem therefore assumes a reduced generic acting algebra and leaves scheme-theoretic faithfulness to patching.

Primitive wild supercuspidal types and ramified dyadic positive-depth types are outside the selected local range. Their compact type lattices, companion adjunctions, and incidence models have not been supplied by the dependencies. Conductor equality does not place them in the tame-dihedral or special component.

The theorem also excludes coefficient characteristic equal to the residue characteristic at $v$. Then the coefficient sheaf is not an étale constant lattice on the semistable model, connected finite flat group schemes can contribute, and the prime-to-$v$ monodromy and Ihara arguments do not give the asserted complex.

Finally, exact augmentation of cohomology and exact augmentation of the acting order are logically distinct. If condition (2.2) fails, Theorems 13.1 and 13.2 can still identify the augmented complex and kill its Tor term, while the map from the augmented faithful image to the minimal image has an extra kernel. Likewise, failure of primitive local incidence comparison does not alter the type complex, but it inserts a height-one determinant index between the type section and the cotangent section. These two failures are listed explicitly because neither can be detected from characteristic-zero packet support alone.

## 17. The one-prime component-support theorem

### 17.1 Statement

We now collect the reusable result.

**Theorem 17.1 (one-prime type complex, component support, and exact augmentation).** Let $F$, $\ell$, $\mathcal O$, $\bar\rho$, $\delta$, the minimal datum, the fixed place $v$, the enhanced special components, the type lattices, and the automorphic localization satisfy the clean hypotheses of Chapter 2. In particular, the minimal comparison theorem holds, $v\nmid\ell$, the minimal local datum at $v$ is the named conductor-one special component, the nonminimal datum is its tamely twisted conductor-two enhanced component, and the localization is non-Eisenstein and adjoint stable.

Then at every auxiliary level there are primary and companion perfect complexes, and their marked finite shadows produce compatible patched perfect complexes,

$$
C_v^{\mathrm{pri}}=[P^0\to P^1],
\qquad
C_v^{\mathrm{cmp}}=[P^{0,\dagger}\to P^{1,\dagger}]
$$

with the following properties.

1. Both have Tor amplitude $[0,1]$ and are perfect duals up to the shift in (6.8).
2. At every finite auxiliary level, before changing the acting base,
   $$
   H^0(C_v^{\mathrm{pri}})=0,
   \qquad H^1(C_v^{\mathrm{pri}})
   \text{ is finite free over }\mathcal O.
   $$
   The patched complex has finite free terms over the patched power-series base; no claim that a patched module is finite over $\mathcal O$ is intended.
3. At finite auxiliary level, for every specialization $A_Q\to B$ of the coefficient base,
   $$
   H^0(C_v^{\mathrm{pri}}\otimes_A^LB)
   \simeq\operatorname{Tor}_1^A(H^1(C_v^{\mathrm{pri}}),B),
   $$
   while degree-one cohomology is ordinary base change.
4. The old image and the primary and companion type lattices are saturated; quotient-new and orthogonal-new are perfect duals; no type-lattice or inner-form index remains.
5. As a complex with faithful-order action, its support is exactly the closure of the selected special family: conductor-two automorphic branches on the nontrivial tame-character factors and the named conductor-one special branches on the augmentation factor. Under a finite local deformation-ring action, its support is the closed contraction of that selected automorphic component union; inverse images occur only after scalar extension of a perfect model.
6. Its determinant line is canonically compatible with primary--companion duality, the signed old Gram determinant, the enhanced-special cotangent determinant, finite coefficient extension, and auxiliary patching.
7. Fixed-prime derived augmentation is exact:
   $$
   C_v^{\mathrm{pri}}
   \otimes_{\Lambda_v,\epsilon_v}^L\mathcal O
   \simeq C^{\min,\mathrm{sp}},
   $$
   and the corresponding $\operatorname{Tor}_1$ group vanishes.
8. Augmentation recovers the minimal acting Hecke algebra, primary and companion modules, pairing, adjoints, and determinant line, not merely their generic fibers.
9. On a primitive rank-one, generically isolated, square complete-intersection branch with unit companion factor, the exact type congruence length is
   $$
   v_\lambda(q_v+1-\varepsilon a_v);
   $$
   at automorphic multiplicity $m$ it is multiplied by $m$.
10. The old Gram cokernel and the graph monodromy component group remain distinct explicit modules. Neither is erased by saturation or exact augmentation.

The theorem proves component support but not scheme-theoretic faithfulness over the universal nonminimal deformation ring. It prepares, but does not prove, the one-prime nonminimal deformation--Hecke equality.

### 17.2 Proof

**Proof strategy.** The proof has six stages. Saturated degeneracy maps construct the cone. Integral type lattices cut it without denominators. Two-term homological algebra exposes every Tor term. Generic type occurrence determines support. Companion duality removes determinant indices. Minimal injectivity kills the augmentation Tor term.

**Proof.** The fixed-prime degeneracy map is injective with primitive image by saturated Ihara theory. Forming its cone gives (4.2), with zero degree-zero cohomology and free degree-one quotient over $\mathcal O$. Apply the primitive primary and companion type functors termwise. Their finite projectivity proves amplitude $[0,1]$, and pull--norm adjunction proves the shifted duality (6.8). This proves clauses 1--2.

Proposition 3.1 applied over the coefficient base $A_Q$ gives (7.3)--(7.4), proving clause 3. Intersecting the saturated old image with the primitive generic type subspace proves the primary short exact sequence (8.5). Perfect companion duality proves the quotient--orthogonal identification and removes every competing lattice index. The graph-to-definite integral comparison removes an inner-form index while retaining its monodromy discriminant. This proves clause 4 and the distinction in clause 10.

At every generic factor, local type occurrence and full local--global compatibility show that the complex is nonzero exactly on the selected special family described in (6.5). Its surviving finite-level cohomology is $\mathcal O$-free, so no irreducible component of its support is confined to the special fiber. Closedness of cohomological support then gives Theorem 11.2 and clause 5.

Determinants of perfect complexes commute with base change and exact triangles. Termwise companion pairings identify the primary and companion determinant lines. Pull--norm composition gives the Gram matrix, while differentiation of the enhanced special equations gives the local cotangent determinant. Their generic sections agree. At height one, primitive primary comparison makes their ratio integral and primitive companion comparison makes its inverse integral. The ratio is therefore a unit. This proves clause 6 and the exact numerical statement of clause 9 by Smith normal form.

Finally apply the fixed-prime augmentation. Termwise type compatibility identifies the specialized differential with the minimal special degeneracy differential. That differential is injective. Proposition 3.1 identifies its kernel with the sole possible $\operatorname{Tor}_1$ group, so the Tor group vanishes. Degree-one cohomology therefore specializes ordinarily, proving clause 7. Acting-image saturation (2.2) and Lemma 13.3 prove that the faithful acting order has no larger augmentation kernel. The augmented primary--companion diagram and determinant base change give the remaining assertions in clause 8. The finite-shadow argument carries all constructions to and from the patched complex. $\square$

### 17.3 Dependency ledger

Every substantial imported result has the following prior source and retained hypothesis.

| Source | Result used | Hypotheses retained | New work here |
|---|---|---|---|
| Book 17, Chapters 9--11 and 14 | perfect two-term complexes, Tor amplitude, derived base change, determinant lines, duals, triangles, and specialization | finite projective models; ordered graded determinant conventions; derived rather than ordinary tensor product | construction of the fixed-prime determinant square and its type interpretation |
| Book 70, Chapters 12--14 | saturation, Fitting ideals, support versus faithfulness, DVR lengths, regular sequences, cotangent and congruence modules | finite presentation; DVR or normal height-one localization where lengths are used; reducedness when support is promoted | separation of type, Gram, component, and Tor defects; exact height-one comparison |
| Book 158, Theorems 7.1, 10.2, 12.1, and 14.1 | residual Ihara injectivity, primitive old image, free new quotient, quotient--orthogonal duality, Gram matrix, and monodromy--component sequence | proper clean Shimura curve; constant coefficients; $v\nmid\ell$; neat or prime-to-$\ell$ descent; non-Eisenstein localization | insertion of primary and companion types into the degeneracy cone |
| Book 159, Theorems 6.1, 8.1, 9.1, and 15.1 | integral graph-to-definite multiplicity lattice, equality of faithful inner-form orders, signed Gram factors, exact congruence depth | selected special or tame range; primitive lattices; sign separation for scalar formulas; no hidden inner-form index | compatibility of that lattice with the one-prime type determinant and augmentation |
| Book 161, Theorem 6.1, Chapters 10--12, and Theorems 13.2 and 16.1 | enhanced special local condition, primary and companion package as used in the Hecke-valued family, universal monodromy, nonminimal reciprocity map | absolute irreducibility; reduced generic Hecke order; represented local conditions; controlled principal, special, or tame-dihedral range | component support and Tor-exact specialization of the automorphic complex |
| Book 164, Theorem 1.1 and Chapters 6, 8, 11, and 13 | minimal $R=T$, minimal module freeness, exact auxiliary augmentation, primary--companion patching, determinant normalization | totally real clean datum; adequate cyclotomic restriction; $\ell\ge7$; exact minimal-special local component | use of the minimal theorem as the exact augmented endpoint, never as a nonminimal conclusion |

The primary and companion notions enter through the exact package already used and audited in Book 161. No later book supplies a proof input. In particular, the one-prime nonminimal patching theorem is not used to prove support, determinant comparison, or exact augmentation here.

### 17.4 Hostile audit

The argument survives the following checks.

**Typing.** The fixed-prime augmentation maps conductor-two special twists to the named conductor-one special component. It does not claim that an arbitrary unramified component is special. The global determinant, central character, sign, and invariant line agree on both sides.

**Amplitude.** The complex is retained in degrees $0,1$. Concentration over $\mathcal O$ is not confused with flatness over the acting ring. Every nonflat specialization displays its $\operatorname{Tor}_1$ term.

**Saturation.** Old saturation, type saturation, and inner-form lattice equality are proved by different inputs. The Gram cokernel and component group are not called saturation defects.

**Support.** Every generic factor of the faithful order is checked. Closed component support is proved from generic occurrence and $\mathcal O$-flatness. It is not promoted to faithfulness over a nonreduced deformation ring.

**Determinants.** Scalar determinants are used only for square presentations. Higher multiplicity retains the full pairing matrix. Primary comparison gives integrality of a determinant ratio; companion comparison gives integrality of its inverse. No determinant equality is obtained from generic equality alone.

**Augmentation.** Termwise specialization is distinguished from cohomology specialization. The only possible correction is identified before it is killed. Its vanishing follows from minimal injectivity, not from an assumed flatness or the desired nonminimal equality.

**Patching.** Auxiliary levels are not treated as a tower. The differential, pairing, both augmentations, and determinant data are retained in finite shadows. Inverse limits are used only along surjective shadow transitions.

**Numerics.** Exact length uses a DVR, a primitive isolated branch, a unit companion factor, and primitive multiplicity. If any hypothesis fails, the correction term is displayed rather than suppressed.

**Exceptional cases.** Eisenstein systems, reducible residual representations, colliding roots, small coefficient primes, $\ell$-divisible stabilizers, coefficient characteristic equal to the fixed residue characteristic, nonreduced generic fibers, and primitive wild types are excluded explicitly.

## 18. Conclusion

### 18.1 The established package

Changing one prime from a minimal special condition to a conductor-two special condition is governed by a two-term object. Its degree-zero term is the old source, its degree-one term is the upper type lattice, and its cohomology is the quotient-new multiplicity. Saturated Ihara theory makes the original old map primitive, but the complex remains essential because specialization over a larger acting ring can create a first Tor group.

Primary and companion type lattices put the selected special packet into this cone at an integral scale. The primary lattice detects occurrence; the companion supplies adjunction. Their perfect pairing proves that no rational projector denominator or inner-form comparison index survives. It also compares determinant sections in both directions, forcing their ratio to be a unit rather than merely an integral scalar.

The resulting perfect complex has amplitude $[0,1]$. For every base change its new degree-zero cohomology is exactly

$$
\operatorname{Tor}_1(\text{quotient-new type module},\text{new base}).
$$

Its support is the closure of the selected special family. The nontrivial tame-character part is conductor two, and the augmentation face is the named conductor-one special part. This is full component coverage as a closed set, not a premature claim of scheme-theoretic faithfulness. Its determinant is simultaneously compatible with the old signed Gram factor, the enhanced-special cotangent determinant, and the primary--companion pairing.

At the fixed-prime tame augmentation, the specialized chain map is the minimal conductor-one special degeneracy map. Minimal injectivity kills the displayed Tor group. Hence augmentation is exact on the complex, its cohomology, the faithful acting algebra, the primary and companion lattices, their pairing, and the determinant line. The same assertion survives the nonnested Taylor--Wiles levels through coherent finite shadows.

The finite modules now have unambiguous meanings. The old and type saturation defects vanish. The signed Gram cokernel measures old--new congruence. The graph monodromy cokernel is the Néron component group. The specialization Tor module measures nonflat base change and vanishes at the clean augmentation. No one of these modules is used as a name for another.

This is the complete one-prime type-complex and component-support package. It supplies the amplitude, support, determinant, saturation, and exact augmentation data needed to combine the minimal theorem with nonminimal reciprocity in a subsequent one-prime patch. The remaining task is a new patching and faithfulness argument on the selected component; it is not assumed here.
