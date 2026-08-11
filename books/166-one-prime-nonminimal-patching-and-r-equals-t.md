# One-Prime Nonminimal Patching and R=T

## Contents

- [1. From component support to equality](#1-from-component-support-to-equality)
  - [1.1 The remaining mathematical problem](#11-the-remaining-mathematical-problem)
  - [1.2 Why the minimal theorem is not enough](#12-why-the-minimal-theorem-is-not-enough)
  - [1.3 The decisive idea](#13-the-decisive-idea)
  - [1.4 The route through the book](#14-the-route-through-the-book)
- [2. The clean one-prime datum](#2-the-clean-one-prime-datum)
  - [2.1 Global coefficients and residual representation](#21-global-coefficients-and-residual-representation)
  - [2.2 The coefficient-prime conditions](#22-the-coefficient-prime-conditions)
  - [2.3 Minimal conditions away from the coefficient prime](#23-minimal-conditions-away-from-the-coefficient-prime)
  - [2.4 The selected conductor-two place](#24-the-selected-conductor-two-place)
  - [2.5 Automorphic and integral hypotheses](#25-automorphic-and-integral-hypotheses)
  - [2.6 The clean hypothesis ledger](#26-the-clean-hypothesis-ledger)
- [3. The theorem to be proved](#3-the-theorem-to-be-proved)
  - [3.1 Universal and fixed-character formulations](#31-universal-and-fixed-character-formulations)
  - [3.2 The ring equality](#32-the-ring-equality)
  - [3.3 The modularity-lifting conclusion](#33-the-modularity-lifting-conclusion)
  - [3.4 What is not asserted](#34-what-is-not-asserted)
- [4. The nonminimal deformation ring](#4-the-nonminimal-deformation-ring)
  - [4.1 The global functor](#41-the-global-functor)
  - [4.2 The enhanced special local relation](#42-the-enhanced-special-local-relation)
  - [4.3 Tame character space and augmentation](#43-tame-character-space-and-augmentation)
  - [4.4 The minimal quotient](#44-the-minimal-quotient)
  - [4.5 Reducedness of the selected source](#45-reducedness-of-the-selected-source)
- [5. The nonminimal Hecke algebra](#5-the-nonminimal-hecke-algebra)
  - [5.1 The automorphic carrier](#51-the-automorphic-carrier)
  - [5.2 Faithful image algebras](#52-faithful-image-algebras)
  - [5.3 Nonminimal reciprocity](#53-nonminimal-reciprocity)
  - [5.4 Exact fixed-prime augmentation](#54-exact-fixed-prime-augmentation)
  - [5.5 Normalizations](#55-normalizations)
- [6. The finite Taylor--Wiles system](#6-the-finite-taylor--wiles-system)
  - [6.1 Auxiliary primes and ordered roots](#61-auxiliary-primes-and-ordered-roots)
  - [6.2 The two independent group algebras](#62-the-two-independent-group-algebras)
  - [6.3 Deformation rings at auxiliary level](#63-deformation-rings-at-auxiliary-level)
  - [6.4 Type complexes at auxiliary level](#64-type-complexes-at-auxiliary-level)
  - [6.5 Exact auxiliary augmentation](#65-exact-auxiliary-augmentation)
- [7. Patching complexes rather than quotients](#7-patching-complexes-rather-than-quotients)
  - [7.1 Why cohomology alone loses information](#71-why-cohomology-alone-loses-information)
  - [7.2 Finite marked shadows](#72-finite-marked-shadows)
  - [7.3 Construction of the patched complex](#73-construction-of-the-patched-complex)
  - [7.4 Pairings, determinants, and support in the limit](#74-pairings-determinants-and-support-in-the-limit)
- [8. The amplitude-collapse theorem](#8-the-amplitude-collapse-theorem)
  - [8.1 A local algebra lemma](#81-a-local-algebra-lemma)
  - [8.2 The augmented fiber](#82-the-augmented-fiber)
  - [8.3 Collapse to a finite free module](#83-collapse-to-a-finite-free-module)
  - [8.4 Consequences for every tame specialization](#84-consequences-for-every-tame-specialization)
- [9. Support becomes faithfulness](#9-support-becomes-faithfulness)
  - [9.1 Topological support and annihilators](#91-topological-support-and-annihilators)
  - [9.2 Flat generic reducedness implies reducedness](#92-flat-generic-reducedness-implies-reducedness)
  - [9.3 The patched source acts faithfully](#93-the-patched-source-acts-faithfully)
  - [9.4 Why no numerical equality is used](#94-why-no-numerical-equality-is-used)
- [10. The patched R=T theorem](#10-the-patched-rt-theorem)
  - [10.1 The three patched rings](#101-the-three-patched-rings)
  - [10.2 Equality by faithfulness](#102-equality-by-faithfulness)
  - [10.3 Scheme-theoretic component coverage](#103-scheme-theoretic-component-coverage)
  - [10.4 Primary and companion modules](#104-primary-and-companion-modules)
- [11. Descent through the auxiliary augmentation](#11-descent-through-the-auxiliary-augmentation)
  - [11.1 Regularity of the auxiliary variables](#111-regularity-of-the-auxiliary-variables)
  - [11.2 Recovery of finite level](#112-recovery-of-finite-level)
  - [11.3 The conductor-two ring--Hecke equality](#113-the-conductor-two-ring--hecke-equality)
  - [11.4 The minimal face as a consistency check](#114-the-minimal-face-as-a-consistency-check)
- [12. Fixed tame characters and coefficient extension](#12-fixed-tame-characters-and-coefficient-extension)
  - [12.1 Character specialization](#121-character-specialization)
  - [12.2 Why specialization has no Tor correction](#122-why-specialization-has-no-tor-correction)
  - [12.3 Extension of coefficient DVRs](#123-extension-of-coefficient-dvrs)
  - [12.4 Faithfully flat descent of equality](#124-faithfully-flat-descent-of-equality)
- [13. Structural and numerical consequences](#13-structural-and-numerical-consequences)
  - [13.1 Finite flatness and complete intersections](#131-finite-flatness-and-complete-intersections)
  - [13.2 Congruence and cotangent ideals](#132-congruence-and-cotangent-ideals)
  - [13.3 The signed one-prime factor](#133-the-signed-one-prime-factor)
  - [13.4 Multiplicity and component groups](#134-multiplicity-and-component-groups)
- [14. From a deformation point to an automorphic representation](#14-from-a-deformation-point-to-an-automorphic-representation)
  - [14.1 A point of the common ring](#141-a-point-of-the-common-ring)
  - [14.2 Occurrence in the automorphic carrier](#142-occurrence-in-the-automorphic-carrier)
  - [14.3 Equality of Galois representations](#143-equality-of-galois-representations)
  - [14.4 Integral lattices and finite-flat quotients](#144-integral-lattices-and-finite-flat-quotients)
- [15. The finite-flat modularity-lifting theorem](#15-the-finite-flat-modularity-lifting-theorem)
  - [15.1 Exact statement](#151-exact-statement)
  - [15.2 Proof](#152-proof)
  - [15.3 Local hypotheses in reusable form](#153-local-hypotheses-in-reusable-form)
  - [15.4 Coefficient-field independence](#154-coefficient-field-independence)
- [16. Solvable ascent and descent](#16-solvable-ascent-and-descent)
  - [16.1 Why descent is a separate theorem](#161-why-descent-is-a-separate-theorem)
  - [16.2 Restriction of the local conditions](#162-restriction-of-the-local-conditions)
  - [16.3 Descent selected by the extending representation](#163-descent-selected-by-the-extending-representation)
  - [16.4 The solvable modularity corollary](#164-the-solvable-modularity-corollary)
- [17. Exceptional cases and exact boundaries](#17-exceptional-cases-and-exact-boundaries)
  - [17.1 Coefficient characteristic five](#171-coefficient-characteristic-five)
  - [17.2 Colliding roots and signs](#172-colliding-roots-and-signs)
  - [17.3 Reducible, Eisenstein, and scalar systems](#173-reducible-eisenstein-and-scalar-systems)
  - [17.4 Stabilizers, wild types, and nonreduced sources](#174-stabilizers-wild-types-and-nonreduced-sources)
  - [17.5 Ground-field extension at the selected place](#175-ground-field-extension-at-the-selected-place)
- [18. Dependency and logical audit](#18-dependency-and-logical-audit)
  - [18.1 Direct prerequisite ledger](#181-direct-prerequisite-ledger)
  - [18.2 Closure of every imported step](#182-closure-of-every-imported-step)
  - [18.3 Circularity audit](#183-circularity-audit)
  - [18.4 Normalization audit](#184-normalization-audit)
- [19. Conclusion](#19-conclusion)
  - [19.1 The established package](#191-the-established-package)

## 1. From component support to equality

### 1.1 The remaining mathematical problem

Minimal modularity lifting begins with a residual automorphic representation and proves that every lift satisfying the same local conditions is automorphic. Its algebraic core is an equality between a universal deformation ring and a faithful Hecke algebra. The word *minimal* means that no new ramification is allowed away from the coefficient prime beyond the named residual components.

The first genuinely nonminimal problem is to change the condition at one place $v\nmid\ell$. The residual representation is already on a special boundary. At minimal level it has conductor exponent one. We allow a tamely ramified scalar twist of conductor exponent one while retaining nonzero rank-one monodromy; the corresponding special representation then has conductor exponent two. The desired equality is

$$
R^{(2)}\xrightarrow{\sim}\mathbb T^{(2)}.
\tag{1.1}
$$

This is not merely a second application of the minimal theorem. The local deformation ring has acquired a tame-character direction, the automorphic module has acquired a fixed-prime old--new comparison, and specialization back to the minimal point can create a first Tor group. The purpose of this book is to show that the one-prime type complex controls all three changes and that patching turns its component support into scheme-theoretic faithfulness.

### 1.2 Why the minimal theorem is not enough

Suppose one knows $R^{\min}=\mathbb T^{\min}$. A tempting argument says that the nonminimal ring and Hecke algebra have the same generic points and the same minimal quotient, so they must be equal. Neither implication is valid. Two finite flat orders can have the same generic fiber and different integral lattices. A quotient can also contain a nilpotent ideal invisible at every generic point and invisible after one augmentation.

There is a second temptation. If

$$
C=[P^0\longrightarrow P^1]
$$

is the fixed-prime type complex and $H^1(C)$ is free over $\mathcal O$, one might patch $H^1(C)$ and discard $P^0$. That loses the extension class that measures failure of flat base change. Under a specialization $A\to B$, the missing group is

$$
H^0(C\otimes_A^LB)
\simeq\operatorname{Tor}_1^A(H^1(C),B).
\tag{1.2}
$$

The complex must therefore survive until flatness in the tame direction has actually been proved.

A one-variable model shows the defect without geometry. Let $A=\mathcal O[[t]]$ and

$$
C=[A\xrightarrow{t}A].
$$

The differential is injective and $H^1(C)=A/(t)$. Specialize to $B=A/(t)$. The specialized differential is zero, so

$$
H^0(C\otimes_A B)=B
=\operatorname{Tor}_1^A(A/(t),B).
$$

Tensoring the quotient alone would retain only degree one and would miss an equally large degree-zero term. The fixed-prime complex is an arithmetic version of this elementary presentation.

Finally, equality of congruence lengths is not an adequate substitute for equality of rings. Lengths are codimension-one invariants. They do not see a nilpotent annihilator or an embedded component. The proof below establishes faithfulness first and derives numerical identities afterward.

### 1.3 The decisive idea

The decisive observation is that the augmented patched complex is already understood. Fixed-prime augmentation sends the conductor-two type to the named conductor-one special type. The exact-augmentation theorem for the one-prime complex identifies the resulting complex with the minimal patched object, which is a finite free module in one degree.

Let

$$
B_\infty=\Lambda_v[[z_1,\ldots,z_q]]
$$

be the combined tame-character and auxiliary patching base. The patched type complex is perfect of amplitude $[0,1]$ over the local ring $B_\infty$. Its fiber at the maximal ideal has no degree-zero cohomology. A minimal-complex argument therefore removes its degree-zero term altogether:

$$
C_\infty^{(2)}\simeq M_\infty^{(2)}[-1],
\qquad
M_\infty^{(2)}\text{ finite free over }B_\infty.
\tag{1.3}
$$

Thus the tame direction, initially visible only through a complex, becomes flat as a consequence of exact augmentation.

Book 165 proves that the support of this complex is confined to, and componentwise primitive on, the selected special family. Freeness over the combined base makes the fiber nonzero on every generic tame-character factor; the clean enhanced-special chart has one selected component over each such factor. The support is therefore the entire patched selected source. That source is flat over $\mathcal O$ with reduced generic fiber, hence reduced. On a reduced ring, a module with full support has zero annihilator. Consequently the patched deformation source acts faithfully on $M_\infty^{(2)}$. Nonminimal reciprocity gives the opposite comparison, a surjection to the Hecke image. Faithfulness forces both kernels to vanish and gives the patched equality.

### 1.4 The route through the book

Chapters 2 and 3 state the datum and theorem without abbreviating the exceptional cases. Chapters 4 and 5 construct the deformation and Hecke sides and identify both augmentation maps. Chapters 6 and 7 build and patch the finite-level type complexes. Chapters 8 through 10 prove amplitude collapse, faithfulness, and the patched equality. Chapters 11 and 12 descend through auxiliary and tame specializations.

The equality then becomes an arithmetic theorem. Chapter 13 records its structural and numerical consequences. Chapters 14 and 15 pass from a point of the common ring to an automorphic representation and prove the finite-flat lifting corollary. Chapter 16 treats solvable ascent and descent. Chapters 17 and 18 audit exceptional cases, dependencies, logic, and normalizations.

## 2. The clean one-prime datum

### 2.1 Global coefficients and residual representation

Let $F$ be a totally real field. Let $\ell\geq7$, and let

$$
(\mathcal O,\varpi,k,E)
$$

be a complete discrete valuation ring, a uniformizer, its finite residue field of characteristic $\ell$, and its fraction field. Fix a continuous representation

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{2.1}
$$

that is absolutely irreducible and totally odd. Assume

$$
\bar\rho|_{G_{F(\zeta_\ell)}}
\quad\text{is absolutely irreducible}.
\tag{2.2}
$$

Fix a continuous minimal determinant lift

$$
\delta^{\min}:G_F\longrightarrow\mathcal O^\times
\tag{2.3}
$$

compatible with a parallel-weight-two central character. Put $\operatorname{ad}^0\bar\rho$ for the trace-zero adjoint representation and assume

$$
H^0\bigl(F,\operatorname{ad}^0\bar\rho(1)\bigr)=0.
\tag{2.4}
$$

The cyclotomic irreducibility assumption is the image hypothesis used to select Taylor--Wiles primes in the range $\ell\geq7$. It is not replaced by absolute irreducibility over $F$. Condition (2.4) is recorded separately because it controls a global dual invariant in the exact tangent calculation.

### 2.2 The coefficient-prime conditions

For every place $w\mid\ell$, assume $F_w/\mathbf Q_\ell$ is unramified and that $\bar\rho|_{G_{F_w}}$ belongs to the low-weight finite-flat range with weights $\{0,1\}$. The fixed-determinant framed local deformation condition is the represented clean finite-flat condition. A lift belongs to it only when every Artinian quotient has a compatible finite-flat model. Rational Hodge--Tate weights alone do not imply this integral condition.

The unramified-base and weight hypotheses are not decorative. They are precisely the range in which the integral finite-flat category supplies exact base change, duality, and compatible quotient models. A ramified extension of $F_w$ or a larger weight interval requires a different local theorem and is not included here.

### 2.3 Minimal conditions away from the coefficient prime

Choose a finite controlling set $S$ containing the places above $\ell$, the places where $\bar\rho$ or the determinant family is ramified, and the selected place $v$ introduced below. At each $w\in S$ with $w\nmid\ell$ and $w\ne v$, impose one of the clean minimal conditions used in minimal modularity lifting:

- the unramified condition;
- a fixed prime-to-$\ell$ integral inertial type with every required label;
- the schematic closure of a named minimal-special component, retaining its invariant line, sign, determinant, and monodromy relation.

At places outside $S$, deformations are unramified. These conditions are component data, not conductor bounds. In particular, zero monodromy and nonzero monodromy can have the same inertial semisimplification but lie on different loci.

Assume that $\bar\rho$ is residually automorphic in the exact parallel-weight-two quaternionic realization attached to this minimal datum. The localization is non-Eisenstein, and its local factors and determinant agree with the chosen conditions.

### 2.4 The selected conductor-two place

Fix a finite place $v\nmid\ell$, and write $q_v$ for the cardinality of its residue field. At $v$, retain the enhanced special data

$$
(\bar\xi_v,L_v,\varepsilon_v,\Delta_v),
\tag{2.5}
$$

where $\bar\xi_v$ is a scalar finite inertial character of order prime to $\ell$, $L_v$ is the chosen invariant residual line, $\varepsilon_v\in\{1,-1\}$ is the sign in the fixed central normalization, and $\Delta_v$ is a finite tame $\ell$-power quotient. Put

$$
\Lambda_v=\mathcal O[\Delta_v],
\qquad
\epsilon_v:\Lambda_v\longrightarrow\mathcal O
\tag{2.6}
$$

for the group algebra and its augmentation.

The universal tame problem includes a continuous determinant family

$$
\delta_{\Lambda_v}:G_F\longrightarrow\Lambda_v^\times
\tag{2.6a}
$$

whose augmentation is $\delta^{\min}$ and whose restriction at $v$ has the determinant forced by the tautological scalar tame twist. At a character $\chi$, write $\delta_\chi$ for its specialization. Thus every individual deformation problem has a fixed determinant, while the determinant varies compatibly across the universal tame family. If the selected tame parameter is determinant-neutral, this family is constant. The clean datum includes existence of the compatible global central-character family; a local scalar twist cannot be varied while incorrectly keeping its square out of the determinant.

The local deformation problem is the represented fixed-determinant enhanced special closure $R_v^{\mathrm{sp},2}$. On a nontrivial tame-character generic factor, inertia acts through the scalar character $\xi_v\chi_v$, monodromy has rank one, and the special representation has conductor exponent two. On the augmentation factor $\chi_v=1$, one obtains the named conductor-one minimal-special component $R_v^{\mathrm{sp},1}$.

Thus the superscript $2$ names the nontrivial-character locus of a relative incidence family. It does not claim that every point of its augmentation face has conductor two. The equality proved in this book respects this normalization.

Assume

$$
q_v\not\equiv1\pmod\ell,
\qquad
q_v\not\equiv-1\pmod\ell.
\tag{2.7}
$$

The first congruence separates the two old Frobenius roots. The second makes the companion signed Gram factor a unit. Full two-map saturation is available without these exclusions, but the selected sign theorem and scalar numerical formula require them.

### 2.5 Automorphic and integral hypotheses

Choose primary and companion lattices for the minimal and conductor-two special types. They are required to be primitive, finite free over their coefficient algebras, and perfectly paired with inverse-character semilinearity. The two degeneracy maps at $v$ must have saturated image after localization. Fine level is neat, or descent from a neat cover uses stabilizers of order invertible in $\mathcal O$.

The localized Hecke image must be finite flat over $\mathcal O$ with reduced generic fiber, and its faithful order must equal the trace order generated by good Frobenius traces, the fixed determinant, and the structural tame action. Every characteristic-zero branch must lie in the principal, special, or tame-dihedral range for which full local--global compatibility is available. At $v$, that compatibility records inertia, monodromy, the invariant line, Frobenius return, and sign, so that the primary type selects exactly the enhanced special family.

At every Taylor--Wiles level, the automorphic terms are free over the auxiliary diamond group ring. Auxiliary augmentation is exact on deformation rings, modules, Hecke images, pairings, and determinant lines. The fixed-prime type complex satisfies the component-support, saturation, determinant, and exact-augmentation theorem of Book 165, including augmentation-saturation of the acting image.

Finally, require the patched selected deformation source described in Chapter 6 to be $\mathcal O$-flat, equidimensional of the same dimension as the combined patching base, and to have reduced generic fiber. After decomposing the generic tame algebra into character factors, require exactly one named selected generic component over each factor. These properties follow in the standard clean charts from the formally smooth minimal factors, the enhanced-special incidence chart, and the retained component choice. We state them because the dimension and uniqueness assertions promote nonvanishing on every tame factor to full component support, while reducedness promotes full support to faithfulness.

### 2.6 The clean hypothesis ledger

We call the preceding collection a **clean one-prime nonminimal datum**. For later reference, its conditions are:

1. $F$ is totally real and $\ell\geq7$.
2. The representation (2.1) is absolutely irreducible, totally odd, cyclotomically absolutely irreducible as in (2.2), and satisfies (2.4).
3. The determinant family (2.6a), its minimal specialization (2.3), and all local central characters agree; each fixed-character problem has determinant $\delta_\chi$.
4. Every coefficient-prime condition is finite flat of type $\{0,1\}$ over an unramified local base.
5. Every other minimal condition is a represented named clean component.
6. The place $v\nmid\ell$ carries the enhanced conductor-two special datum (2.5), not merely a conductor number.
7. The sign separation (2.7) holds.
8. Residual automorphy occurs in the exact non-Eisenstein, adjoint-stable quaternionic localization.
9. Degeneracy images and primary and companion type lattices are saturated; stabilizer descent is prime to $\ell$.
10. Branchwise Galois attachment and full local--global compatibility hold on a reduced generic Hecke order, and the faithful order equals its trace order.
11. Nonminimal reciprocity and the one-prime type-complex theorem apply at every auxiliary level.
12. Taylor--Wiles modules are group-ring free, both augmentations are exact, and all finite shadow data are compatible.
13. The selected patched deformation source is $\mathcal O$-flat and equidimensional of the expected dimension, has reduced generic fiber, and has one named selected generic component over each generic tame-character factor.

No later argument silently adds a hypothesis to this list. When a specialization or solvable extension is used, its additional conditions will be stated at that point.

## 3. The theorem to be proved

### 3.1 Universal and fixed-character formulations

There are two related deformation problems. The **universal tame problem** allows the tautological character of $\Delta_v$ and is defined over $\Lambda_v$. Its rings are denoted

$$
R^{(2)}_{\Lambda_v},
\qquad
\mathbb T^{(2)}_{\Lambda_v}.
\tag{3.1}
$$

If $\chi:\Delta_v\to\mathcal O_\chi^\times$ is a chosen nontrivial character after finite coefficient extension, the **fixed-character problem** is obtained by

$$
\Lambda_v\longrightarrow\mathcal O_\chi,
\qquad [g]\longmapsto\chi(g).
\tag{3.2}
$$

It is denoted $R^{(2)}_\chi$ and $\mathbb T^{(2)}_\chi$. Because $\chi$ is nontrivial and tame of conductor exponent one, the corresponding special twist has conductor exponent two. The augmentation character gives the minimal conductor-one face, not another conductor-two problem.

### 3.2 The ring equality

**Theorem 3.1 (one-prime nonminimal $R=T$).** For a clean one-prime nonminimal datum, nonminimal reciprocity induces an isomorphism of complete local $\Lambda_v$-algebras

$$
\boxed{
R^{(2)}_{\Lambda_v}\xrightarrow{\sim}
\mathbb T^{(2)}_{\Lambda_v}.
}
\tag{3.3}
$$

The equality is compatible with fixed-prime augmentation, auxiliary augmentation, the determinant family, primary--companion adjunction, and finite extension of coefficients. For every nontrivial tame character $\chi$ satisfying the retained clean local hypotheses,

$$
\boxed{
R^{(2)}_\chi\xrightarrow{\sim}\mathbb T^{(2)}_\chi.
}
\tag{3.4}
$$

The universal patched type complex is concentrated in degree one and its surviving module is finite free over the combined tame and auxiliary patching base. Consequently all tame-character specializations are Tor-independent.

The proof occupies Chapters 6 through 12. Notice that (3.3) is stronger than equality of generic fibers, equality of reduced spectra, or equality after augmentation.

### 3.3 The modularity-lifting conclusion

The ring equality has the following arithmetic meaning. Let $\mathcal O'/\mathcal O$ be a finite extension of coefficient DVRs, and let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{3.5}
$$

lift $\bar\rho$. Suppose its determinant is the fixed specialization $\delta_\chi$, every $w\mid\ell$ restriction is finite flat of weights $\{0,1\}$ on all Artinian quotients, every $w\ne v$ satisfies the named minimal condition, and $\rho|_{G_{F_v}}$ lies on the chosen nontrivial-character enhanced special component. Then $\rho$ is attached, with its integral lattice, to a cuspidal parallel-weight-two automorphic representation having the prescribed central character and local types.

If this conclusion is first obtained after a finite solvable totally real extension, it descends under the precise irreducibility, cuspidality, compatibility, and local-parameter hypotheses of Chapter 16.

### 3.4 What is not asserted

The theorem does not derive an image theorem at coefficient characteristic five. It does not say that absolute irreducibility over $F$ implies the Taylor--Wiles image hypotheses at five. It does not cover a reducible or Eisenstein residual system, an $\ell$-divisible stabilizer, a primitive wild type, coefficient characteristic equal to the residue characteristic at $v$, or a local branch specified only by conductor.

Nor does it assert that the conductor-two module is rank one over the common Hecke algebra. Automorphic multiplicity may exceed one. Ring equality and module freeness over the patching base are the conclusions needed for modularity lifting.

## 4. The nonminimal deformation ring

### 4.1 The global functor

Let $\mathcal C$ be the category of complete noetherian local $\mathcal O$-algebras with residue field $k$. For $A\in\mathcal C$, a deformation is a strict-equivalence class of continuous lifts

$$
\rho_A:G_F\longrightarrow\operatorname{GL}_2(A)
$$

with determinant $\delta_{\Lambda_v}$, unramified outside $S$, and satisfying the local conditions of Chapter 2. At $v$ the lift includes the enhanced line and tame character. Forgetting the line would merge branches at the residual scalar point, so it is part of the represented functor.

Absolute irreducibility gives the global Schur condition. The represented local conditions are stable under base change and fiber product. The global deformation theory therefore supplies a complete local ring $R^{(2)}_{\Lambda_v}$ and a universal strict-equivalence class. Its variance is fixed by the rule that a homomorphism from the ring to $A$ produces an $A$-valued deformation.

### 4.2 The enhanced special local relation

Choose a tame inertia generator $\tau$ and a geometric Frobenius lift $\phi$ with

$$
\phi\tau\phi^{-1}=\tau^{q_v^{-1}},
\tag{4.1}
$$

where $q_v^{-1}$ is interpreted in the prime-to-residue-character profinite units. With arithmetic Frobenius the exponent is $q_v$ and every monodromy factor below is inverted.

On the selected local chart, after removing the fixed scalar inertial character, the universal representation has an invariant direct summand $L$ and a rank-one nilpotent operator $N$ satisfying

$$
N^2=0,
\qquad
\operatorname{im}N\subseteq L\subseteq\ker N,
\qquad
\rho(\phi)N\rho(\phi)^{-1}=q_v^{-1}N.
\tag{4.2}
$$

The inertia action is

$$
\rho(\sigma)=\xi_v(\sigma)\chi_v(\sigma)
\exp\bigl(t_\ell(\sigma)N\bigr)
\tag{4.3}
$$

on the special family, with the determinant condition removing the redundant scalar variable. The closure permits $N=0$ on the boundary because the condition $N\ne0$ is open and cannot itself define a quotient-stable deformation functor. The named component and line distinguish the closure from unrelated monodromy-zero components.

At a characteristic-zero point with $\chi_v\ne1$ and $N\ne0$, the Weil--Deligne representation is a special twist. If $a(\chi_v)=1$, then

$$
a\bigl(\operatorname{St}\otimes(\mu\chi_v)\bigr)=2.
\tag{4.4}
$$

At $\chi_v=1$ with $\mu$ unramified, the conductor exponent is one. This proves the normalization asserted in Chapter 2 rather than assuming it from the superscript.

### 4.3 Tame character space and augmentation

The group algebra $\Lambda_v$ remembers all congruent tame characters simultaneously. Because $\Delta_v$ is an $\ell$-group, distinct characteristic-zero characters meet in the special fiber. Decomposing the generic fiber into characters and then taking an arbitrary lattice would obscure how they meet. The integral incidence family over $\Lambda_v$ records that meeting canonically.

For example, if $\Delta_v$ is cyclic of order $\ell$ with generator $g$ and $X=g-1$, then

$$
\Lambda_v\simeq
\mathcal O[X]/\bigl((1+X)^\ell-1\bigr).
\tag{4.4a}
$$

After adjoining the $\ell$th roots of unity and inverting $\varpi$, its factors are indexed by $X=\zeta-1$. Modulo $\varpi$, all $\ell$-power roots of unity reduce to $1$, so all factors meet at $X=0$. This is why the augmentation face and nontrivial-character faces cannot be treated as disjoint integral modules even though they are disjoint generically.

The augmentation ideal

$$
\mathfrak a_v=\ker(\epsilon_v:\Lambda_v\to\mathcal O)
\tag{4.5}
$$

sets the tautological tame character equal to $1$. Exact local augmentation gives

$$
R_v^{\mathrm{sp},2}/\mathfrak a_vR_v^{\mathrm{sp},2}
\simeq R_v^{\mathrm{sp},1}.
\tag{4.6}
$$

This is an equality of represented enhanced local conditions. It retains the invariant line, determinant, sign, and monodromy relation. Equality only after inverting $\varpi$ would be insufficient for patching.

### 4.4 The minimal quotient

Applying (4.6) at $v$ and leaving every other local condition unchanged yields a canonical surjection

$$
R^{(2)}_{\Lambda_v}\longrightarrow R^{\min}.
\tag{4.7}
$$

Under the exact deformation-augmentation hypothesis, its kernel is exactly $\mathfrak a_vR^{(2)}_{\Lambda_v}$, so

$$
R^{(2)}_{\Lambda_v}/\mathfrak a_vR^{(2)}_{\Lambda_v}
\simeq R^{\min}.
\tag{4.8}
$$

Book 155 gives

$$
R^{\min}\simeq\mathbb T^{\min},
\tag{4.9}
$$

and says that the common ring is finite free and a relative complete intersection over $\mathcal O$. Equation (4.9) is used only as the augmented endpoint. It is not used to infer (3.3) by Nakayama, since a kernel can be contained in $\mathfrak a_v$ without vanishing.

### 4.5 Reducedness of the selected source

The patching proof needs one elementary fact that will later eliminate nilpotent annihilators.

**Lemma 4.1 (flat reduced-generic criterion).** Let $A$ be an $\mathcal O$-flat algebra. If $A[1/\varpi]$ is reduced, then $A$ is reduced.

**Proof.** Let $x\in A$ be nilpotent. Its image in $A[1/\varpi]$ is nilpotent and therefore zero. Hence $\varpi^n x=0$ for some $n$. Flatness over the DVR makes multiplication by $\varpi$ injective on $A$, and iteration gives $x=0$. $\square$

The lemma applies to the selected local tensor and to its power-series extensions under the clean hypothesis. It does not say that an arbitrary quotient of that source is reduced. The quotient will instead be proved equal to the source by faithful action.

## 5. The nonminimal Hecke algebra

### 5.1 The automorphic carrier

Use the compact weight-two quaternionic realization of the minimal theorem. At $v$, replace the minimal special type by the conductor-two primary lattice over $\Lambda_v$ and retain its companion. At all other places use the fixed types of the clean datum. Localize at the non-Eisenstein maximal ideal determined by $\bar\rho$ and simultaneously retain the adjoint companion block.

The fixed-prime object is not initially one automorphic module. It is the primary two-term type complex

$$
C_v^{\mathrm{pri}}=[P_v^0\xrightarrow{d_v}P_v^1]
\tag{5.1}
$$

and its companion. The differential is induced by the two degeneracy maps. Its degree-one cohomology is the saturated quotient-new type lattice, while its possible specialized degree-zero cohomology measures a Tor defect.

### 5.2 Faithful image algebras

The Hecke algebra is defined as an image, not as a polynomial algebra with conjectural relations. Away from $S$, use unnormalized right-double-coset operators $T_w,S_w$. The named local operators and tame action are retained on the carrier, but the ring used for reciprocity is the faithful trace order generated by the good traces together with the fixed determinant and structural $\Lambda_v$-action. Under the clean trace-generation hypothesis of Book 161 this trace order is the entire faithful order denoted below. Let

$$
\mathbb T^{(2)}_{\Lambda_v}
\subseteq
\operatorname{End}_{\Lambda_v}\bigl(H^*(C_v^{\mathrm{pri}})\oplus H^*(C_v^{\mathrm{cmp}})\bigr)
\tag{5.2}
$$

be their faithful image.

This definition prevents a formal generator from surviving when it acts as zero. It does not by itself imply good base change: the image of an algebra in an endomorphism ring can acquire a larger kernel after specialization. The augmentation-saturation condition retained from Book 165 is exactly what controls this issue at the minimal face.

### 5.3 Nonminimal reciprocity

Branchwise Galois attachment, order-valued trace descent, and full local--global compatibility construct a continuous Hecke-valued representation

$$
\rho_{\mathbb T}:G_F\longrightarrow
\operatorname{GL}_2(\mathbb T^{(2)}_{\Lambda_v})
\tag{5.3}
$$

with determinant $\delta_{\Lambda_v}$ and, for $w\notin S$,

$$
\det\bigl(1-X\rho_{\mathbb T}(\Phi_w)\bigr)
=1-T_wX+q_wS_wX^2,
\tag{5.4}
$$

where $\Phi_w$ is geometric Frobenius. At every controlled bad place the representation factors through the named local condition, including the enhanced special condition at $v$ and the finite-flat condition at places above $\ell$.

The universal property gives a canonical homomorphism

$$
R^{(2)}_{\Lambda_v}\longrightarrow
\mathbb T^{(2)}_{\Lambda_v}.
\tag{5.5}
$$

It is surjective because the target is the trace order: (5.4) sends the universal traces to every good $T_w$, the determinant is fixed, and the structural tame character is part of the represented local point. The clean trace-generation hypothesis identifies this image with $\mathbb T^{(2)}_{\Lambda_v}$. If a genuinely new nontrace operator were adjoined, this argument would reach only the trace suborder unless a separate integral generation result were supplied. This is the only direction supplied by reciprocity. Injectivity is the new patching theorem.

### 5.4 Exact fixed-prime augmentation

Termwise augmentation of the conductor-two primary and companion types gives the minimal conductor-one special types. Book 165 proves

$$
C_v^{\mathrm{pri}}
\otimes_{\Lambda_v,\epsilon_v}^L\mathcal O
\simeq C^{\min,\mathrm{sp}}
\tag{5.6}
$$

and

$$
\operatorname{Tor}_1^{\Lambda_v}
\bigl(H^1(C_v^{\mathrm{pri}}),\mathcal O\bigr)=0.
\tag{5.7}
$$

It also identifies the augmented acting image:

$$
\mathbb T^{(2)}_{\Lambda_v}/\mathfrak a_v
\mathbb T^{(2)}_{\Lambda_v}
\simeq\mathbb T^{\min}.
\tag{5.8}
$$

The Tor vanishing comes from injectivity of the augmented minimal degeneracy map. The ring statement additionally uses augmentation-saturation of the faithful image. These are distinct inputs and will remain distinct after patching.

### 5.5 Normalizations

All comparisons use geometric Frobenius and unnormalized right-double-coset operators. At a good place the polynomial is (5.4), and adjunction is

$$
T_w^*=S_w^{-1}T_w.
\tag{5.9}
$$

At $v$, after trivial-central specialization, the old Gram matrix is

$$
G_v=
\begin{pmatrix}
q_v+1&T_v\\
T_v&q_v+1
\end{pmatrix},
\tag{5.10}
$$

and its selected signed factor is

$$
c_v^{\varepsilon_v}=q_v+1-\varepsilon_v a_v.
\tag{5.11}
$$

Before trivial-central specialization, the lower-left entry of (5.10) is $S_v^{-1}T_v$. The sign, invariant line, and companion normalization are transported through every patching shadow. Changing Frobenius or coset convention would change (5.4), (5.9), and (5.10) together.

## 6. The finite Taylor--Wiles system

### 6.1 Auxiliary primes and ordered roots

Patching removes the global dual Selmer obstruction by changing the deformation problem at carefully chosen auxiliary primes. For each sufficiently large integer $N$, choose a set $Q_N$ disjoint from $S$ and $v$ such that

$$
q_w\equiv1\pmod{\ell^N}
\qquad(w\in Q_N),
\tag{6.1}
$$

the residual Frobenius at $w$ has two distinct eigenvalues, and the resulting local classes detect a basis of the dual Selmer group. The cyclotomic irreducibility and coefficient-prime bound in Chapter 2 are precisely the hypotheses used for this selection.

Choose an ordering of the two residual roots at every $w\in Q_N$. The ordered local condition is a smooth branch and carries a diamond quotient $\Delta_w$. Put

$$
\Delta_{Q_N}=\prod_{w\in Q_N}\Delta_w,
\qquad
\Lambda_{Q_N}=\mathcal O[\Delta_{Q_N}].
\tag{6.2}
$$

The number $q=|Q_N|$ is independent of $N$ and equals the sharp number of auxiliary variables in the global tangent calculation. Adding unused variables would destroy the later dimension comparison, while choosing too few primes would leave a dual Selmer obstruction.

### 6.2 The two independent group algebras

The fixed-prime and auxiliary algebras must never be conflated:

$$
\begin{array}{c|c|c}
\text{algebra}&\text{arithmetic meaning}&\text{augmentation}\\ \hline
\Lambda_v&\text{tame character at the fixed place }v&
\epsilon_v:\Lambda_v\to\mathcal O\\
\Lambda_{Q_N}&\text{diamond characters at auxiliary primes}&
\epsilon_{Q_N}:\Lambda_{Q_N}\to\mathcal O.
\end{array}
\tag{6.3}
$$

Fixed-prime augmentation changes the local conductor-one/conductor-two incidence datum. Auxiliary augmentation removes Taylor--Wiles level without changing the condition at $v$. Since the actions come from separate tensor factors, the two derived specializations commute.

Let

$$
A_N=\Lambda_v\widehat\otimes_{\mathcal O}\Lambda_{Q_N}.
\tag{6.4}
$$

The terms of the finite-level primary and companion type complexes are finite free over $\Lambda_{Q_N}$ and finite projective over $A_N$ in the fixed-prime direction. No freeness over a Hecke algebra is assumed.

### 6.3 Deformation rings at auxiliary level

Let $R_N^{(2)}$ be the global deformation ring with the clean local conditions and the ordered auxiliary conditions. Its local tangent calculation is the minimal calculation plus the same fixed-prime relative incidence direction on both the deformation and coefficient sides. Consequently there is a sharp presentation from a fixed selected local source $P_N^{(2)}$ with $q$ auxiliary variables. At finite precision these presentations can be chosen compatibly with both augmentations.

We explain the dimension balance. At a clean special point, the framed enhanced local ring is a power-series ring over the tame-character base with one monodromy coordinate and two strict framing coordinates. The two framing coordinates cancel the corresponding change-of-basis directions in the global framed tensor. The monodromy coordinate belongs to the local condition itself and appears on both the deformation source and automorphic type complex. Thus adding the fixed place changes neither the excess number of global generators nor the number $q$ of Taylor--Wiles variables. The global Euler characteristic and the auxiliary local tangent lines give the same sharp relative dimension as in the minimal problem, now over $\Lambda_v$ instead of $\mathcal O$.

More concretely, after retaining harmless framing variables until the local tensor product is formed, one has a surjection

$$
P_N^{(2)}\twoheadrightarrow R_N^{(2)}.
\tag{6.5}
$$

The source is obtained from the completed tensor product of the named local rings by adjoining the exact number of global variables supplied by the Selmer calculation. Framing variables occur equally on both sides and are removed by a regular sequence. The clean charts show that the selected source is $\mathcal O$-flat and generically reduced.

**Proposition 6.1 (geometry of the selected source).** Under the clean local charts, the patched source $P_\infty^{(2)}$ is $\mathcal O$-flat and equidimensional of the expected dimension. After a finite coefficient extension splitting $\Lambda_v[1/\varpi]$, it has one selected generic component over each tame character factor, and every such component is reduced.

**Proof strategy.** Separate framing directions from genuine local deformation coordinates, use the explicit enhanced-special chart at $v$, and then pass through completed tensor products and power-series extensions.

**Proof.** The coefficient-prime and clean minimal framed rings are formally smooth or relative complete intersections with the dimensions used in the minimal tangent calculation. At $v$, the enhanced-special chart has the form

$$
\Lambda_v[[m,y,z]],
\tag{6.5a}
$$

where $m$ is monodromy and $y,z$ are strict framing coordinates. Removing the balanced framing directions preserves flatness and equidimensionality. The global variables supplied by the Selmer presentation and the auxiliary variables are power-series variables, so they preserve both properties.

After splitting the generic character algebra, (6.5a) becomes one power-series chart for each character. The named invariant line and sign choose one chart rather than its Weyl conjugate. Each chart is a domain, and the other named local generic factors are the reduced factors already used in the minimal theorem. Their selected completed tensor is reduced under the clean geometric-reducedness hypothesis, and adjoining power-series variables preserves reducedness. Hence there is exactly one selected reduced generic component over every tame character factor. $\square$

The proposition proves the source properties later used in Proposition 9.1. If a local tensor ceases to be geometrically reduced after coefficient extension, the last sentence fails; this is why geometric reducedness is part of the clean chart rather than a consequence of dimension alone.

Auxiliary augmentation is exact:

$$
R_N^{(2)}\otimes_{\Lambda_{Q_N},\epsilon_{Q_N}}\mathcal O
\simeq R^{(2)}_{\Lambda_v}.
\tag{6.6}
$$

This is an equality of represented deformation problems. The ordered auxiliary characters become trivial and the chosen roots recover the original unramified local conditions.

### 6.4 Type complexes at auxiliary level

At level $Q_N$, Book 165 supplies a primary complex

$$
C_{N,v}^{\mathrm{pri}}
=[P_{N,v}^0\longrightarrow P_{N,v}^1]
\tag{6.7}
$$

and a companion complex. They are perfect of amplitude $[0,1]$ over $A_N$. After forgetting to $\mathcal O$, the differential is injective and the degree-one quotient is free. Under an arbitrary $A_N$-algebra $B$, however,

$$
H^0(C_{N,v}^{\mathrm{pri}}\otimes_{A_N}^LB)
\simeq
\operatorname{Tor}_1^{A_N}
\bigl(H^1(C_{N,v}^{\mathrm{pri}}),B\bigr).
\tag{6.8}
$$

The support of (6.7), viewed under the deformation action, is the pullback of the full selected enhanced special component. Primary--companion duality identifies the determinant line with the local enhanced-special determinant and removes every hidden type-lattice index.

Nonminimal reciprocity gives a surjection

$$
R_N^{(2)}\twoheadrightarrow\mathbb T_N^{(2)}
\tag{6.9}
$$

onto the faithful Hecke image on the total primary and companion cohomology. We do not assume that (6.9) is an isomorphism.

### 6.5 Exact auxiliary augmentation

The auxiliary module theorem identifies derived coinvariants with the fixed finite-level complex:

$$
C_{N,v}^{\mathrm{pri}}
\otimes_{\Lambda_{Q_N},\epsilon_{Q_N}}^L\mathcal O
\simeq C_v^{\mathrm{pri}}.
\tag{6.10}
$$

Because the terms are free over $\Lambda_{Q_N}$, the left side is computed termwise. Acting-image saturation identifies the corresponding Hecke quotient. Pairings, adjoints, deformation actions, and determinant generators descend with (6.10).

Fixed-prime augmentation similarly gives

$$
C_{N,v}^{\mathrm{pri}}
\otimes_{\Lambda_v,\epsilon_v}^L\mathcal O
\simeq C_N^{\min,\mathrm{sp}}.
\tag{6.11}
$$

Associativity of derived tensor product makes the two routes from (6.7) to minimal finite level canonically quasi-isomorphic. This commutative square is retained in the patch; otherwise the limit could not distinguish the two augmentation ideals.

## 7. Patching complexes rather than quotients

### 7.1 Why cohomology alone loses information

The sets $Q_N$ are selected independently and do not form a nested tower. There are no natural maps from the arithmetic module at level $Q_{N+1}$ to the one at level $Q_N$. Patching therefore proceeds through finite quotients with marked structures, not through a literal inverse limit of levels.

It is also essential to patch the differential. Two two-term complexes can have isomorphic degree-one cohomology but different extension classes. Those classes give different kernels after nonflat specialization. If only $H^1$ were retained, equation (6.8) could not be reconstructed and fixed-prime exactness would have no chain-level meaning.

### 7.2 Finite marked shadows

Fix a coefficient precision and bounds on the auxiliary variables. Reduce all rings, modules, matrices, and operators modulo those bounds. Mark the following finite data:

- both terms of the primary and companion complexes and their differentials;
- bases over the finite auxiliary group algebra;
- the $\Lambda_v$-action and both augmentation maps;
- the selected local deformation action and the map to the Hecke image;
- primary--companion pairings and every adjoint operator;
- away and fixed-prime Hecke operators;
- determinant-line generators and the local determinant comparison;
- the support label naming the enhanced special component.

Only finitely many isomorphism classes of such finite diagrams occur at fixed precision. Successive diagonal selection produces a subsequence whose shadows are compatible at every earlier precision. The transition maps between the chosen shadows are surjective.

To justify finiteness, at a fixed precision every coefficient ring is finite, the term ranks are bounded, and a differential or operator is a matrix with entries in a finite set. There are therefore only finitely many marked matrices and commutative diagrams. Choose an infinite subsequence constant at the first precision, then an infinite subsequence of it constant at the second, and continue. The diagonal subsequence is eventually constant at every fixed precision. Choosing representatives and transition isomorphisms gives a projective system.

Surjectivity matters. It implies the Mittag--Leffler condition, so inverse limits preserve the short exact sequences of kernels and images that define the finite shadows. Without it, a derived inverse-limit term could create an extra cohomological degree unrelated to the fixed-prime Tor group.

### 7.3 Construction of the patched complex

Let

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]],
\qquad
B_\infty=\Lambda_v\widehat\otimes_{\mathcal O}S_\infty.
\tag{7.1}
$$

Taking inverse limits of the marked finite free terms gives

$$
C_\infty^{(2)}
=[P_\infty^0\xrightarrow{d_\infty}P_\infty^1],
\tag{7.2}
$$

a strict perfect complex of amplitude $[0,1]$ over $B_\infty$. The fixed-prime algebra is included in $B_\infty$; it is not absorbed into the auxiliary variables.

Finite freeness of the limiting terms can be seen directly. Compatible bases at every finite precision give continuous maps from finite free $B_\infty$-modules to the inverse limits. They are isomorphisms modulo every open ideal. Completeness and the topological form of Nakayama's lemma make them isomorphisms. The differentials are the inverse limits of their marked matrices, so no choice of a cohomology splitting enters the construction.

The deformation presentations patch to a surjection

$$
P_\infty^{(2)}\twoheadrightarrow R_\infty^{(2)},
\tag{7.3}
$$

and nonminimal reciprocity patches to

$$
R_\infty^{(2)}\twoheadrightarrow
\mathbb T_\infty^{(2)}.
\tag{7.4}
$$

Here $\mathbb T_\infty^{(2)}$ is the image of the marked Hecke operators on the total cohomology of (7.2) and its companion. The composite action of $P_\infty^{(2)}$ on the complex is the limit of the finite deformation actions.

The source $P_\infty^{(2)}$ is a power-series extension of the selected completed local tensor after the balanced framing variables are removed. By the clean hypothesis it is $\mathcal O$-flat with reduced generic fiber. Lemma 4.1 therefore makes it reduced.

### 7.4 Pairings, determinants, and support in the limit

Invertibility of each finite primary--companion pairing matrix persists in the inverse limit. Thus there is a perfect duality

$$
C_\infty^{\mathrm{cmp}}
\simeq
R\!\operatorname{Hom}_{B_\infty}
(C_\infty^{\mathrm{pri}},B_\infty)[1]
\tag{7.5}
$$

with the prescribed inverse-double-coset adjoints. Determinants commute with the chosen finite free limits, so the local type, old Gram, and enhanced-special sections remain identified up to a unit.

Support is checked fiberwise. A prime of $P_\infty^{(2)}$ contracts to a fixed-prime point. Book 165's type-occurrence theorem says that a nonzero fiber lies exactly on the selected special family, and its closure theorem says that every component which occurs does so at the primitive integral scale. Thus

$$
\operatorname{Supp}_{P_\infty^{(2)}}
H^*(C_\infty^{(2)})
\subseteq\operatorname{Spec}P_\infty^{(2)}
\tag{7.6}
$$

with no component outside the named source and no hidden height-one lattice index. The displayed inclusion is deliberately not called equality yet. After amplitude collapse proves freeness over $B_\infty$, Chapter 9 will show that the support dominates every generic tame factor. The one-component-per-factor property will then give equality, and reducedness will turn that equality into a zero annihilator.

## 8. The amplitude-collapse theorem

### 8.1 A local algebra lemma

The central homological step is elementary but powerful.

**Lemma 8.1 (fiber concentration shortens amplitude).** Let $(A,\mathfrak m,k)$ be a local ring and let $C$ be a perfect complex of amplitude contained in $[0,1]$. If

$$
H^0(C\otimes_A^Lk)=0,
\tag{8.1}
$$

then there is a finite free $A$-module $M$ and a quasi-isomorphism

$$
C\simeq M[-1].
\tag{8.2}
$$

**Proof strategy.** Replace the complex by a minimal finite free model. Its differential is zero after reduction, so the degree-zero term is visible directly in the special fiber.

**Proof.** Split off every contractible direct summand on which the differential has a unit entry. This process terminates and produces a two-term finite free model

$$
[F^0\xrightarrow dF^1]
$$

with $d(F^0)\subseteq\mathfrak mF^1$. After tensoring with $k$, the differential is zero. Hence

$$
H^0(C\otimes_A^Lk)=F^0\otimes_Ak.
$$

Condition (8.1) and Nakayama's lemma give $F^0=0$. Put $M=F^1$. Then $C$ is $M$ in degree one, which is (8.2). $\square$

The conclusion is stronger than ordinary concentration of cohomology: it proves that the surviving cohomology is finite free over the whole base $A$.

### 8.2 The augmented fiber

Let $\mathfrak m_{B_\infty}$ be the maximal ideal generated by $\varpi$, the auxiliary variables, and the augmentation ideal $\mathfrak a_v$. First apply fixed-prime augmentation. The marked quasi-isomorphism (6.11) passes to the limit and gives

$$
C_\infty^{(2)}
\otimes_{\Lambda_v,\epsilon_v}^L\mathcal O
\simeq C_\infty^{\min,\mathrm{sp}}.
\tag{8.3}
$$

The minimal patched theorem identifies the right side with a nonzero finite free $S_\infty$-module placed in degree one. Tensoring further with $S_\infty/(\varpi,z_1,\ldots,z_q)$ therefore gives

$$
H^0(C_\infty^{(2)}\otimes_{B_\infty}^Lk)=0.
\tag{8.4}
$$

Every equality here is derived. Thus no unproved flatness of $H^1(C_\infty^{(2)})$ has been used.

### 8.3 Collapse to a finite free module

Apply Lemma 8.1 to (7.2) over $B_\infty$. We obtain the main intermediate theorem.

**Theorem 8.2 (patched amplitude collapse).** There is a nonzero finite free $B_\infty$-module $M_\infty^{(2)}$ and a Hecke- and deformation-equivariant quasi-isomorphism

$$
C_\infty^{(2)}\simeq M_\infty^{(2)}[-1].
\tag{8.5}
$$

The companion complex is the $B_\infty$-dual module in the complementary degree, and the primary--companion pairing is perfect.

**Proof.** Equation (8.4) verifies Lemma 8.1. Nonzeroness follows after fixed-prime augmentation, because the minimal patched module has positive rank. The finite shadow construction makes the quasi-isomorphism equivariant for every retained operator. Dualizing (8.5) in (7.5) gives the companion statement. $\square$

This is the point at which the one-prime complex has completed its task. It was indispensable before (8.5), because it displayed the possible Tor term. After (8.5), that term vanishes for every base change of $B_\infty$.

### 8.4 Consequences for every tame specialization

Let $B$ be any $B_\infty$-algebra. From (8.5),

$$
C_\infty^{(2)}\otimes_{B_\infty}^LB
\simeq
(M_\infty^{(2)}\otimes_{B_\infty}B)[-1].
\tag{8.6}
$$

Therefore

$$
H^0(C_\infty^{(2)}\otimes_{B_\infty}^LB)=0
\tag{8.7}
$$

and degree-one cohomology is ordinary base change. In particular, the fixed-prime augmentation, every nontrivial character specialization, auxiliary augmentation, coefficient reduction, and every composite of these operations has no higher Tor correction.

This conclusion was not available at finite level merely from $\mathcal O$-freeness. It is a theorem about flatness over the combined tame and auxiliary base.

## 9. Support becomes faithfulness

### 9.1 Topological support and annihilators

For a finite module $M$ over a noetherian ring $A$,

$$
\operatorname{Supp}_A(M)=V(\operatorname{Ann}_A(M)).
\tag{9.1}
$$

Consequently full support gives only

$$
\sqrt{\operatorname{Ann}_A(M)}=\sqrt{(0)}.
\tag{9.2}
$$

If $A$ has nilpotents, (9.2) need not imply faithfulness. For example, $A=k[\epsilon]/(\epsilon^2)$ acts on $k$ with full support and annihilator $(\epsilon)$. This is why Book 165 stopped at component support.

### 9.2 Flat generic reducedness implies reducedness

The clean patched source $P_\infty^{(2)}$ is $\mathcal O$-flat and has reduced generic fiber. Lemma 4.1 gives

$$
\sqrt{(0)}=(0)
\quad\text{in }P_\infty^{(2)}.
\tag{9.3}
$$

Power-series variables do not introduce nilpotents, and the selected local tensor was required to remain generically reduced. Thus (9.3) applies to the precise ring acting on the patched complex, not merely to each local factor separately.

### 9.3 The patched source acts faithfully

**Proposition 9.1 (support-to-faithfulness).** The action of $P_\infty^{(2)}$ on $M_\infty^{(2)}$ is faithful.

**Proof strategy.** Freeness over the combined base forces a nonzero fiber at every generic tame character. The selected local chart has only one generic component above each such character, so the component-support theorem forces every component of the patched source into the module support. Reducedness then removes the annihilator.

**Proof.** By (8.5), $M_\infty^{(2)}$ is nonzero and free over $B_\infty$. Decompose

$$
B_\infty[1/\varpi]=\prod_\chi B_{\infty,\chi}
$$

over the generic tame characters after a harmless finite coefficient extension. For every $\chi$, the fiber

$$
M_\infty^{(2)}\otimes_{B_\infty}
\operatorname{Frac}(B_{\infty,\chi})
$$

is nonzero. Let $A_{\infty,\chi}$ be the image of $P_\infty^{(2)}$ on this fiber before passing to the fraction field. It is finite over $B_{\infty,\chi}$ because it lies in the endomorphism ring of a finite free module. The scalar action of $B_{\infty,\chi}$ is faithful, so

$$
B_{\infty,\chi}\hookrightarrow A_{\infty,\chi}.
$$

Consequently

$$
\dim A_{\infty,\chi}
=\dim B_{\infty,\chi}
=\dim P_{\infty,\chi}^{(2)}.
$$

Thus the module support is a closed subset of full dimension in $P_{\infty,\chi}^{(2)}$. Book 165's support theorem places its generic points on the named enhanced-special family. The clean local chart has exactly one selected generic component above that character factor, so a full-dimensional closed subset contains that entire component. Running through all $\chi$ accounts for every irreducible component of $P_\infty^{(2)}$.

Consequently

$$
V\bigl(\operatorname{Ann}_{P_\infty^{(2)}}M_\infty^{(2)}\bigr)
=\operatorname{Spec}P_\infty^{(2)}.
$$

The annihilator is contained in every prime ideal and hence in the nilradical. By (9.3) the nilradical is zero. Thus the annihilator is zero. The temporary coefficient extension does not affect this conclusion, by faithful flatness. $\square$

The argument kills a scheme-theoretic kernel. It is not merely a statement that every irreducible component contains an automorphic point.

### 9.4 Why no numerical equality is used

The determinant comparison of Book 165 is needed to establish primitive support and to rule out height-one type indices. It is not used here in the form “two lengths are equal, hence two rings are equal.” Proposition 9.1 rests on three independently proved facts: full support, reducedness of the source, and amplitude collapse to a finite module.

This order avoids a circle. Cotangent and congruence modules are invariants of the deformation and Hecke rings. They can be canonically identified only after the ring map is known to be an isomorphism. Chapter 13 will therefore treat their equality as a consequence.

## 10. The patched R=T theorem

### 10.1 The three patched rings

We have surjections

$$
P_\infty^{(2)}
\twoheadrightarrow R_\infty^{(2)}
\twoheadrightarrow\mathbb T_\infty^{(2)}.
\tag{10.1}
$$

The first comes from the sharp global deformation presentation. The second comes from the Hecke-valued representation. Their composite is exactly the action of the selected deformation source on $M_\infty^{(2)}$ retained in the finite shadows.

### 10.2 Equality by faithfulness

**Theorem 10.1 (patched one-prime $R=T$).** Both arrows in (10.1) are isomorphisms:

$$
\boxed{
P_\infty^{(2)}
=R_\infty^{(2)}
=\mathbb T_\infty^{(2)}.
}
\tag{10.2}
$$

**Proof.** Let $J$ be the kernel of the composite map from $P_\infty^{(2)}$ to $\mathbb T_\infty^{(2)}$. By definition of the faithful Hecke image, $J$ is the annihilator of the action of $P_\infty^{(2)}$ on the direct sum of primary and companion cohomology. The primary summand $M_\infty^{(2)}$ already has zero annihilator by Proposition 9.1. Hence $J=0$.

The composite in (10.1) is both surjective and injective, so it is an isomorphism. If a composite of two surjections is injective, the first kernel and the inverse image of the second kernel are zero. Thus each arrow in (10.1) is an isomorphism. $\square$

The proof is short because the difficult work has been isolated: reciprocity supplies surjectivity, the type complex supplies full component support and exact augmentation, and the clean local charts supply reducedness.

### 10.3 Scheme-theoretic component coverage

Equation (10.2) says more than every generic deformation branch is automorphic. Every infinitesimal deformation in the selected global ring acts nontrivially unless it is zero. Thus no nilpotent thickening, embedded selected-direction kernel, or hidden congruence quotient remains between deformation theory and the faithful Hecke order.

The selected qualifier remains essential. The theorem does not say that components excluded by the primary type are automorphic. The ring $P_\infty^{(2)}$ was built from the named enhanced special component, and Book 165 identifies support precisely on that component.

### 10.4 Primary and companion modules

The primary patched module is finite free over $B_\infty$, not automatically rank one over the common ring in (10.2). Its companion is its perfect $B_\infty$-dual with the prescribed adjoints. Since the common ring acts faithfully, both modules have full scheme-theoretic support over it.

If an additional regularity hypothesis makes the common ring regular and finite over $B_\infty$, Auslander--Buchsbaum can promote a maximal Cohen--Macaulay module to a free module over the common ring. That extra conclusion is not required for (10.2) and is not built into the main theorem. Avoiding it keeps automorphic multiplicity separate from ring faithfulness.

## 11. Descent through the auxiliary augmentation

### 11.1 Regularity of the auxiliary variables

Let

$$
\mathfrak a_\infty=(z_1,\ldots,z_q)\subset S_\infty.
\tag{11.1}
$$

Because $M_\infty^{(2)}$ is finite free over
$B_\infty=\Lambda_v\widehat\otimes S_\infty$, the sequence $z_1,\ldots,z_q$ is regular on the module. Therefore

$$
\operatorname{Tor}_i^{S_\infty}
(M_\infty^{(2)},\mathcal O)=0
\qquad(i>0).
\tag{11.2}
$$

The marked deformation presentations identify quotienting by $\mathfrak a_\infty$ with removal of the Taylor--Wiles local conditions. The same is true on the faithful Hecke image because auxiliary acting-image augmentation was retained in every shadow.

### 11.2 Recovery of finite level

Taking the quotient of (10.2) by the corresponding auxiliary ideals gives a commutative diagram

$$
\begin{array}{ccc}
R_\infty^{(2)}&\xrightarrow{\sim}&\mathbb T_\infty^{(2)}\\
\downarrow&&\downarrow\\
R^{(2)}_{\Lambda_v}&\longrightarrow&\mathbb T^{(2)}_{\Lambda_v}.
\end{array}
\tag{11.3}
$$

The bottom arrow is the canonical nonminimal reciprocity map, not an abstract isomorphism: good Frobenius traces, determinant, local operators, and both augmentation maps were marked before taking limits.

### 11.3 The conductor-two ring--Hecke equality

**Theorem 11.1 (finite-level universal equality).** The bottom arrow in (11.3) is an isomorphism.

**Proof.** Under the exact augmentation identifications,

$$
R^{(2)}_{\Lambda_v}
\simeq R_\infty^{(2)}/\mathfrak a_\infty R_\infty^{(2)}
$$

and

$$
\mathbb T^{(2)}_{\Lambda_v}
\simeq\mathbb T_\infty^{(2)}/\mathfrak a_\infty
\mathbb T_\infty^{(2)}.
$$

Quotienting the isomorphism (10.2) by corresponding ideals gives the result. Regularity (11.2) additionally shows that the specialized automorphic complex has no hidden cohomology, but the ring isomorphism itself follows from the marked quotient identifications. $\square$

This proves (3.3).

### 11.4 The minimal face as a consistency check

Now quotient (3.3) by $\mathfrak a_v$. Equations (4.8) and (5.8) give

$$
R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.
\tag{11.4}
$$

This agrees with the minimal theorem used in the amplitude-collapse argument. The logic is not circular: the prior minimal equality establishes the augmented fiber of the complex; full support and reducedness establish the universal nonminimal equality; quotienting that new equality returns the same minimal map.

## 12. Fixed tame characters and coefficient extension

### 12.1 Character specialization

Let $\chi:\Delta_v\to\mathcal O_\chi^\times$ be a nontrivial character, where $\mathcal O_\chi$ is the ring of integers in a finite extension of $E$. Define

$$
R_\chi^{(2)}=
R^{(2)}_{\Lambda_v}
\widehat\otimes_{\Lambda_v,\chi}\mathcal O_\chi.
\tag{12.1}
$$

Define the Hecke algebra by the corresponding fixed-character automorphic carrier. The universal module theorem (8.5) shows that its patched carrier is the ordinary character specialization of $M_\infty^{(2)}$.

### 12.2 Why specialization has no Tor correction

Since $M_\infty^{(2)}$ is free over $B_\infty$,

$$
\operatorname{Tor}_i^{\Lambda_v}
(M_\infty^{(2)},\mathcal O_\chi)=0
\qquad(i>0).
\tag{12.2}
$$

Thus the fixed-character complex is concentrated in degree one. Its support is the pullback of the selected nontrivial-character component and remains full on that source. Repeating the faithful-action proof after specialization, or simply base changing the marked equality and faithful image, gives

$$
R_\chi^{(2)}\xrightarrow{\sim}\mathbb T_\chi^{(2)}.
\tag{12.3}
$$

Because $\chi\ne1$, the local special representation has conductor exponent two. Equation (12.3) is the fixed-character conductor-two equality stated in (3.4).

### 12.3 Extension of coefficient DVRs

Let $\mathcal O'/\mathcal O$ be a finite extension with residue field containing the image of $k$. Enlarge the local ring if necessary to make the residual representation and all type labels scalar. Every primary and companion lattice, local deformation equation, pairing, and finite-level free module commutes with this flat extension. Therefore

$$
R^{(2)}_{\Lambda_v}\widehat\otimes_{\mathcal O}\mathcal O'
\simeq R^{(2)}_{\Lambda_v'},
\qquad
\mathbb T^{(2)}_{\Lambda_v}\otimes_{\mathcal O}\mathcal O'
\simeq\mathbb T^{(2)}_{\Lambda_v'}.
\tag{12.4}
$$

Here $\Lambda_v'=\mathcal O'[\Delta_v]$. The equality (3.3) base changes to the corresponding equality over $\mathcal O'$. Primitive lattices remain primitive because the extension is flat, and perfect pairings remain perfect because their determinant stays a unit.

Fitting and congruence ideals extend under this base change. Raw uniformizer-normalized lengths do not remain numerically fixed under ramified coefficient extension: if the ramification index is $e$ and $N$ has finite $\mathcal O$-length, then

$$
\operatorname{length}_{\mathcal O'}(N\otimes_{\mathcal O}\mathcal O')
=e\,\operatorname{length}_{\mathcal O}(N).
\tag{12.5}
$$

The ideal equality, rather than an unscaled numerical valuation, is the invariant statement.

### 12.4 Faithfully flat descent of equality

Coefficient enlargement is often used to contain tame character values or split generic Hecke factors. The resulting theorem descends.

**Lemma 12.1 (descent of an isomorphism).** Let $A\to B$ be a homomorphism of finite $\mathcal O$-modules, and let $\mathcal O'/\mathcal O$ be faithfully flat. If

$$
A\otimes_{\mathcal O}\mathcal O'
\longrightarrow B\otimes_{\mathcal O}\mathcal O'
$$

is an isomorphism, then $A\to B$ is an isomorphism.

**Proof.** Tensor the kernel and cokernel exact sequences with the flat module $\mathcal O'$. Both kernel and cokernel become zero. Faithfulness of tensor product then makes the original kernel and cokernel zero. $\square$

Thus the equality is independent of a harmless coefficient field chosen to realize types. This statement concerns coefficient extension. It must not be confused with extension of the ground number field, which changes local Weil groups and conductors.

## 13. Structural and numerical consequences

### 13.1 Finite flatness and complete intersections

The equality of rings preserves whatever commutative-algebra structure was built into the selected deformation source and its regular augmentations. At fixed nontrivial character, the clean enhanced-special chart is formally smooth over the character coefficient ring after the fixed determinant and line have been imposed. The remaining minimal local factors are the clean factors of Book 155. The patched source is therefore a relative complete intersection over the combined patching base, and auxiliary augmentation is by a regular sequence.

It follows that the finite-level fixed-character common ring

$$
R_\chi^{(2)}=\mathbb T_\chi^{(2)}
\tag{13.1}
$$

is finite flat over $\mathcal O_\chi$ and is a relative complete intersection whenever the clean chart has the stated complete-intersection form. In particular it is Cohen--Macaulay and Gorenstein.

Here is the regular-sequence argument. A finite free $B_\infty$-basis remains a basis after quotienting by the auxiliary variables. Since these variables are nonzerodivisors successively on a free module, their quotient has no higher Tor. If the patched source has a presentation by a regular sequence over a regular or complete-intersection local tensor, adjoining and then removing the auxiliary variables preserves the complete-intersection property. Finite flatness over the DVR follows from torsion-freeness and finiteness.

For the universal group-algebra family, $\Lambda_v$ itself can be a ramified complete intersection rather than a regular ring. The correct assertion is relative complete-intersection structure over $\Lambda_v$, not absolute regularity.

### 13.2 Congruence and cotangent ideals

Let $\lambda:R_\chi^{(2)}\to\mathcal O_\lambda$ be a generically isolated integral branch. Put $I_\lambda=\ker\lambda$. Its cotangent module is

$$
\Phi_\lambda=I_\lambda/I_\lambda^2.
\tag{13.2}
$$

The ring equality identifies this module with the Hecke cotangent module. If locally

$$
R_\chi^{(2)}\simeq
\mathcal O_\lambda[[X_1,\ldots,X_r]]/
(f_1,\ldots,f_r),
\tag{13.3}
$$

then the conormal sequence presents $\Phi_\lambda$ by the Jacobian

$$
D_\lambda=
\left(\frac{\partial f_i}{\partial X_j}\right)_\lambda.
\tag{13.4}
$$

Therefore

$$
\operatorname{Fitt}_0(\Phi_\lambda)=(\det D_\lambda).
\tag{13.5}
$$

The Koszul resolution of the regular sequence identifies the relative dualizing generator. Evaluating it at the branch multiplies the generator by $\det D_\lambda$. The same scalar generates the intrinsic Hecke congruence ideal $\eta_\lambda$. Hence

$$
\operatorname{Fitt}_0(\Phi_\lambda)=\eta_\lambda.
\tag{13.6}
$$

This proof uses (13.1) before identifying the two sides. Equation (13.6) is a consequence and numerical audit of $R=T$, not an ingredient in its proof.

### 13.3 The signed one-prime factor

On a primitive rank-one branch in the trivial-central normalization, let $a_v=\lambda(T_v)$. Pull--norm adjunction gives the Gram matrix (5.10). The selected signed vector has eigenvalue

$$
c_v^{\varepsilon_v}=q_v+1-\varepsilon_v a_v,
\tag{13.7}
$$

while its companion has eigenvalue

$$
c_v^{-\varepsilon_v}=q_v+1+\varepsilon_v a_v.
\tag{13.8}
$$

If the level-changing congruence is

$$
a_v\equiv\varepsilon_v(q_v+1)\pmod{\varpi},
\tag{13.9}
$$

then (2.7) makes (13.8) a unit. Smith normal form therefore shows that the selected old--new congruence module has length

$$
\operatorname{length}_{\mathcal O_\lambda}
\Psi_v^{\mathrm{type}}
=v_\lambda(q_v+1-\varepsilon_v a_v).
\tag{13.10}
$$

The local enhanced-special determinant comparison of Book 165 identifies the same factor in the relative cotangent line. Because primary and companion type lattices are primitive, no lattice index multiplies (13.7). Because the integral Jacquet--Langlands comparison identifies faithful orders, no inner-form index occurs either.

### 13.4 Multiplicity and component groups

If the automorphic multiplicity on the branch is $m$, the relevant signed pairing matrix is equivalent to $c_v^{\varepsilon_v}I_m$ only when the multiplicity pairing is primitive and unimodular. Under that hypothesis,

$$
\operatorname{length}\Psi_{v,m}^{\mathrm{type}}
=m\,v_\lambda(c_v^{\varepsilon_v}).
\tag{13.11}
$$

Without it, one must retain the determinant ideal $\mathfrak d_{\mathrm{mult}}$ of the companion pairing:

$$
\operatorname{length}\Psi_{v,m}^{\mathrm{type}}
=m\,v_\lambda(c_v^{\varepsilon_v})
+v_\lambda(\mathfrak d_{\mathrm{mult}}).
\tag{13.12}
$$

The Néron component module is different. If $X_v$ is the graph lattice and

$$
q_\Gamma:X_v\longrightarrow X_v^\vee
$$

is the monodromy pairing, then

$$
\operatorname{coker}(q_\Gamma)
=\Phi_v[\ell^\infty]\otimes_{\mathbf Z_\ell}\mathcal O.
\tag{13.13}
$$

Neither $R=T$ nor saturation makes (13.13) vanish. The old Gram cokernel measures a congruence, the graph cokernel measures a component group, and the specialization Tor group measures nonflat base change. The last vanishes in the patched clean problem; the first two need not.

## 14. From a deformation point to an automorphic representation

### 14.1 A point of the common ring

Let $\rho$ be a lift over a finite coefficient DVR $\mathcal O'$ satisfying the clean global conditions and a fixed nontrivial tame character $\chi$ at $v$. The universal property gives a local homomorphism

$$
x_\rho:R_\chi^{(2)}\longrightarrow\mathcal O'.
\tag{14.1}
$$

Through (12.3), this is a character of the faithful Hecke algebra. After passing to fraction fields, it selects a generic Hecke factor, possibly after a further finite coefficient extension. The selected factor occurs in the automorphic carrier because the Hecke algebra was defined as the image on that carrier.

### 14.2 Occurrence in the automorphic carrier

The primary type at $v$ detects the chosen enhanced special representation; it does not merely detect scalar inertia. The line and sign distinguish the selected branch, and nonzero monodromy at the characteristic-zero point gives the Steinberg twist. At the other bad places, the fixed primary types detect the named principal, minimal-special, or tame-dihedral packets. At places above $\ell$, the integral finite-flat condition supplies the correct weight-two lattice.

Transfer from the compact quaternionic realization gives a cuspidal automorphic representation

$$
\pi=\bigotimes_w'\pi_w
$$

of $\operatorname{GL}_2(\mathbf A_F)$ of parallel weight two and the prescribed central character. Cuspidality comes from the noncharacter quaternionic localization and its transfer, not from a conclusion that every irreducible Galois representation is cuspidal.

At $v$,

$$
\pi_v\simeq
\operatorname{St}\otimes((\mu_v\chi_v)\circ\det),
\qquad a(\pi_v)=2.
\tag{14.2}
$$

This uses $a(\chi_v)=1$ and the fixed normalization of special conductors.

### 14.3 Equality of Galois representations

Let $\rho_\pi$ be the representation attached to $\pi$. For every $w\notin S$,

$$
\det(1-X\rho(\Phi_w))
=1-x_\rho(T_w)X+x_\rho(q_wS_w)X^2
=\det(1-X\rho_\pi(\Phi_w)).
\tag{14.3}
$$

Density of geometric Frobenius conjugacy classes and Brauer--Nesbitt identify the semisimplifications over the coefficient field. A lift of an absolutely irreducible residual representation is irreducible: if its generic fiber had a stable line, intersecting that line with a stable lattice and saturating would give a nonzero proper residual stable subspace. Thus the generic representations are isomorphic.

There is also an integral identification. The Hecke-valued representation is the pushforward of the universal deformation under the isomorphism (12.3). Specializing both by $x_\rho$ gives the same strict-equivalence class. Hence, after a change of basis,

$$
\rho\simeq\rho_\pi
\quad\text{over }\mathcal O'.
\tag{14.4}
$$

The local behavior at bad places is not recovered from (14.3). It was imposed on both universal families before the ring map was constructed.

### 14.4 Integral lattices and finite-flat quotients

The passage from a generic isomorphism to (14.4) deserves emphasis. Let $L,L'$ be stable lattices in the same irreducible two-dimensional coefficient-field representation, both reducing to $\bar\rho$. Scale so that $L'\subseteq L$ but $L'\nsubseteq\varpi L$. The image of $L'$ in $L/\varpi L$ is a nonzero stable subspace, hence the whole space. Nakayama's lemma gives $L'=L$. Thus the lattices are homothetic.

At $w\mid\ell$, the canonical finite-flat lattice theorem supplies compatible finite-flat models for every quotient $L/\varpi^nL$ in weights $\{0,1\}$. The hypothesis on $\rho$ places its quotients in the same represented local functor. Homothety and full faithfulness of the finite-flat realization identify the two quotient systems. This is why the lifting theorem concludes integral automorphy rather than only automorphy after inverting $\ell$.

## 15. The finite-flat modularity-lifting theorem

### 15.1 Exact statement

We can now state the arithmetic result in a form suitable for later use.

**Theorem 15.1 (one-prime finite-flat modularity lifting).** Let $F$, $\ell$, $\mathcal O$, $\bar\rho$, $\delta^{\min}$, the determinant family, and $v$ satisfy the clean one-prime nonminimal datum of Chapter 2. Fix a nontrivial tame character $\chi$, let $\delta_\chi$ be the resulting fixed determinant, let $\mathcal O'/\mathcal O$ be finite, and let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
$$

be a continuous lift of $\bar\rho$. Assume:

1. $\det\rho=\delta_\chi$ after scalar extension.
2. For every $w\mid\ell$, $F_w/\mathbf Q_\ell$ is unramified and every Artinian quotient of $\rho|_{G_{F_w}}$ belongs to the finite-flat weight-$\{0,1\}$ condition.
3. At every $w\nmid\ell$ with $w\ne v$, the restriction belongs to the represented named minimal condition used by the residual automorphic datum.
4. At $v$, the restriction lies on the fixed nontrivial-character enhanced special component with the chosen scalar inertial character, invariant line, sign, determinant, and rank-one monodromy; the tame character has conductor exponent one.
5. The automorphic realization, saturation, stabilizer, reducedness, local--global compatibility, and Taylor--Wiles hypotheses listed in Section 2.6 hold after the required coefficient extension.

Then there is a cuspidal parallel-weight-two automorphic representation $\pi$ of $\operatorname{GL}_2(\mathbf A_F)$ with the prescribed central character and local types such that its attached integral representation is isomorphic to $\rho$. At $v$, $\pi_v$ is the selected special twist of conductor exponent two.

### 15.2 Proof

**Proof strategy.** Place the lift on the represented nonminimal deformation ring, use $R=T$ to turn that point into a Hecke eigensystem, use type occurrence to identify every local packet, and then compare the two integral Galois representations.

**Proof.** Conditions 1--4 give, by the universal property, a point

$$
x_\rho:R_\chi^{(2)}\to\mathcal O'.
$$

Theorem 11.1 and character specialization give

$$
R_\chi^{(2)}\simeq\mathbb T_\chi^{(2)}.
$$

Thus $x_\rho$ occurs in the faithful characteristic-zero automorphic carrier. Integral local type detection identifies the selected packets away from $\ell$; at $v$ it retains the special line, sign, and nonzero monodromy and therefore gives conductor exponent two. The compact realization transfers to a cuspidal parallel-weight-two representation $\pi$.

At good places, (14.3) identifies characteristic polynomials. The argument of Section 14.3 identifies generic representations, and the lattice argument of Section 14.4 upgrades the identification to $\mathcal O'$. The represented finite-flat condition identifies all coefficient-prime quotient models. Hence $\rho\simeq\rho_\pi$ with every asserted local property. $\square$

### 15.3 Local hypotheses in reusable form

The theorem's local conditions can be checked place by place:

$$
\begin{array}{c|l}
\text{place}&\text{required condition}\\ \hline
w\mid\ell&
F_w/\mathbf Q_\ell\text{ unramified; compatible finite-flat quotients; weights }\{0,1\}\\
w\nmid\ell,\ w\ne v&
\text{the exact represented minimal component, with every finite label}\\
v&
\text{enhanced special closure, chosen line and sign, }N\ne0,
\ a(\chi_v)=1\\
w\notin S&\text{unramified.}
\end{array}
\tag{15.1}
$$

The determinant and central character must agree in every row. A conductor inequality does not replace a row. At $v$, scalar inertia without the line and sign is insufficient; at $w\mid\ell$, rational weight information without compatible integral quotients is insufficient.

### 15.4 Coefficient-field independence

If the values of $\chi_v$, a type label, or a generic Hecke character do not lie in $\mathcal O$, enlarge coefficients. Sections 12.3 and 12.4 show that the deformation condition, type lattices, pairings, equality of rings, and resulting representation commute with this operation and descend faithfully. The automorphic representation may be described over the enlarged eigenvalue field, while the given integral Galois representation remains defined over $\mathcal O'$.

This coefficient operation does not change $F$, its places, residue degrees, or conductors. It is therefore harmless for the local table (15.1).

## 16. Solvable ascent and descent

### 16.1 Why descent is a separate theorem

In applications, the clean quaternionic datum may become available only over a finite solvable totally real extension $L/F$. The lifting theorem over $L$ produces an automorphic representation $\Pi_L$. It does not automatically produce one over $F$. Automorphic descent through a noncyclic solvable extension requires compatible choices at successive cyclic steps; invariance of the endpoint as an isomorphism class is not by itself a coherence theorem.

The crucial additional datum is that the arithmetic representation already extends to $G_F$. That extension selects the twisting correction at each cyclic descent step. Book 97 proves that, under its admissibility and irreducibility hypotheses, these corrections form a compatible chain.

### 16.2 Restriction of the local conditions

Let $L/F$ be finite solvable Galois and totally real. Before applying Theorem 15.1 over $L$, every local condition must be checked after restriction. For $u\mid w$, the Weil--Deligne parameter restricts from $W_{F_w}$ to $W_{L_u}$ and retains its monodromy operator. This can change a conductor, split a dihedral induction, or alter the unramified normalization. Solvability alone preserves none of these labels.

At places above $\ell$, require the local fields used in the finite-flat theorem to remain in its unramified low-weight range. At the selected place, it is safest to require complete splitting, in which case the local field and enhanced special datum are unchanged. More generally, one must verify directly that the restricted parameter remains on a clean conductor-two enhanced special component with separated sign.

If a quaternion algebra is used over $L$, its split-side transfer must remain cuspidal. On descent, the selected representation over $F$ must be discrete series at every place where the downstairs quaternion algebra is ramified.

### 16.3 Descent selected by the extending representation

Suppose

$$
\rho:G_F\to\operatorname{GL}_2(\mathcal O')
$$

has irreducible restriction to $G_L$, and Theorem 15.1 over $L$ attaches $\Pi_L$ to $\rho|_{G_L}$. Equality of good-place polynomials makes $\Pi_L$ invariant under $\operatorname{Gal}(L/F)$ by strong multiplicity one.

Choose a prime cyclic composition tower

$$
F=F_0\subset F_1\subset\cdots\subset F_r=L.
\tag{16.1}
$$

At one cyclic step, an arbitrary automorphic descent can differ from the desired arithmetic restriction by a quotient character. Since the arithmetic representation extends one step farther down and has scalar endomorphisms, the extension-comparison lemma identifies the unique character correction. Twisting by its inverse produces a descent attached to $\rho|_{G_{F_{r-1}}}$. Repeat down the tower. The corrections are compatible because they are selected by one representation defined on $G_F$.

### 16.4 The solvable modularity corollary

**Corollary 16.1 (solvable descent of one-prime modularity).** Let $L/F$ be a finite solvable Galois totally real extension admitting a descent-admissible prime cyclic tower. Let $\rho:G_F\to\operatorname{GL}_2(\mathcal O')$ be continuous and suppose:

1. $\rho|_{G_L}$ is irreducible and satisfies a clean one-prime datum over $L$;
2. Theorem 15.1 attaches to it a cuspidal regular algebraic representation $\Pi_L$;
3. cyclic base change, twisting, Galois attachment, and strong multiplicity one apply at every step;
4. the local parameters, central character, weights, and any inner-form discreteness conditions descend to the prescribed downstairs data.

Then there is a cuspidal parallel-weight-two automorphic representation $\pi$ over $F$ attached to $\rho$, and

$$
\operatorname{BC}_{L/F}(\pi)\simeq\Pi_L.
\tag{16.2}
$$

**Proof.** Section 16.3 constructs a compatible cuspidal descent chain selected by the restrictions of $\rho$. The solvable descent theorem of Book 97 gives $\pi$ and (16.2). At good places its attached representation has the same characteristic polynomials as $\rho$; irreducibility and density identify them. The local extension selected by $\rho$ has the determinant, type, sign, and Frobenius data required in condition 4, so the descended packet has the prescribed local behavior. $\square$

The corollary does not construct $L$, prove that base change remains cuspidal, or infer downstairs conductor from the ideal $v\mathcal O_L$. Those are separate hypotheses and computations.

## 17. Exceptional cases and exact boundaries

### 17.1 Coefficient characteristic five

The main theorem assumes $\ell\geq7$. At $\ell=5$, absolute irreducibility over $F$ and even some large-looking projective images do not automatically supply the adequacy statement used in the Taylor--Wiles prime selection. Exceptional icosahedral behavior must be analyzed separately. Stabilizers, reductions of types, and sign blocks may also require new checks.

No small-image theorem at five is asserted here. In particular, Theorem 15.1 must not be invoked at $\ell=5$ by replacing $\ell\geq7$ with absolute irreducibility. A separately established five-adic patching package could satisfy analogous hypotheses, but it would be an additional theorem, not a consequence of this book.

### 17.2 Colliding roots and signs

If $q_v\equiv1\pmod\ell$, the two old Frobenius roots coincide. The full two-map degeneracy image can remain saturated, but an ordered old root cannot be selected by an integral idempotent. The enhanced component would need additional integral line data beyond the clean theorem.

If $q_v\equiv-1\pmod\ell$, both signed Gram factors can be nonunits. The full Gram matrix and type complex still make sense, but the scalar length formula (13.10) no longer isolates one sign. A refined integral sign block would have to be proved before the same theorem could be stated.

At $\ell=2$, the signs coincide; at $\ell=3$ the global image and stabilizer packages lie outside the uniform range. Neither case is covered.

### 17.3 Reducible, Eisenstein, and scalar systems

If $\bar\rho$ is reducible, traces do not determine a unique rank-two family or its extension class. The Hecke-valued representation used in nonminimal reciprocity is then unavailable in the stated form. A pseudorepresentation or ordinary filtered problem would have different deformation and support theories.

At an Eisenstein localization, the local tree character module can survive. The degeneracy map may have a genuine residual kernel, its image may fail to be saturated, and the type complex can have degree-zero cohomology before any base change. The amplitude-collapse proof then has the wrong augmented fiber.

A residual scalar system is more singular than an absolutely irreducible system whose local restriction happens to have scalar inertia. The latter is allowed only with the global Schur condition and the enhanced local line. The former is excluded globally.

### 17.4 Stabilizers, wild types, and nonreduced sources

If a deck or stabilizer group has order divisible by $\ell$, invariants are not exact. A primitive lattice upstairs can become nonprimitive downstairs, and group cohomology can contribute an additional degree. Prime-to-$\ell$ descent or a neat level is therefore essential.

Primitive wild supercuspidal types and ramified dyadic types do not have the integral primary--companion and incidence packages used here. Equality of conductor exponents does not place them in the selected tame range.

If the selected patched source is not reduced, full topological support gives only a nilpotent annihilator. Proposition 9.1 then fails at precisely one line: the nilradical need not vanish. Generic equality and determinant divisors cannot repair this scheme-theoretic gap. One would need a separate depth or nilpotent-control theorem.

### 17.5 Ground-field extension at the selected place

Restriction from $F_v$ to a finite extension can change tame conductor and Frobenius normalization. A special representation retains nonzero monodromy under restriction, but its twisting character can become unramified, and the conductor can drop. Conversely, ramification can change the edge thickness in a semistable model and enlarge the component group.

Therefore Corollary 16.1 checks the actual restricted Weil--Deligne parameter at every place above $v$. Complete splitting is a sufficient clean condition because it leaves the local field, residue cardinality, sign, and tame character unchanged.

## 18. Dependency and logical audit

### 18.1 Direct prerequisite ledger

Every substantial imported result comes from a direct prerequisite with its retained hypotheses.

| Book | Result used here | Hypotheses retained | Role in this book |
|---|---|---|---|
| 97, *Solvable Base Change and Descent* | solvable base change, compatible cyclic descent selected by an extending irreducible arithmetic representation, local-parameter and inner-form compatibility | admissible cyclic steps, cuspidal endpoint, irreducible restriction with scalar endomorphisms, compatible weights, centers, twists, and local parameters | Corollary 16.1 only; no patching input |
| 155, *Minimal Modularity Lifting* | $R^{\min}=\mathbb T^{\min}$, minimal patched module freeness, finite-flat lifting, coefficient change, exact auxiliary augmentation | totally real clean datum, $\ell\geq7$, cyclotomic absolute irreducibility, $H^0(F,\operatorname{ad}^0\bar\rho(1))=0$, unramified weight-$\{0,1\}$ finite-flat places, exact integral automorphic realization | identifies the augmented patched fiber and supplies the minimal endpoint |
| 157, *Integral Local Types and Type Lattices* | primary and companion special lattices, perfect pairing, primitive saturation, enhanced special local chart, familywise type detection | $v\nmid\ell$, unit-valued labels, named component, line and sign, $q_v\not\equiv\pm1\pmod\ell$ for the selected scalar refinement, no primitive wild type | defines the fixed local datum and proves exact characteristic-zero occurrence |
| 158, *Ihara Theory and Saturated Degeneracy Maps on Shimura Curves* | residual Ihara injectivity, primitive old image, free new quotient, quotient--orthogonal duality, Gram and monodromy--component sequences | proper clean Shimura curve, constant coefficients, $v\nmid\ell$, neat or prime-to-$\ell$ descent, non-Eisenstein localization | makes the two-term complex integral and removes old-quotient torsion |
| 159, *Integral Level Change and Jacquet--Langlands Comparison* | equality of faithful curve and definite orders, no hidden integral transfer index, signed Gram factor, exact level-change depth | clean selected special range, primitive lattices, sign separation for scalar formulas, $\ell\geq7$ | identifies the automorphic carrier and the numerical factor without an inner-form index |
| 161, *Hecke-Valued Galois Representations and Nonminimal Reciprocity* | order-valued rank-two representation and the surjection from the global conditioned deformation ring to the faithful Hecke order | residual absolute irreducibility, complete finite-flat order with reduced generic fiber, represented local conditions, full local--global compatibility in the controlled range | supplies (5.5), (6.9), and (7.4) |
| 165, *One-Prime Type Complexes and Component Support* | perfect primary and companion complexes, Tor formula, selected-family component support and primitive closure, determinant comparison, exact fixed-prime augmentation, augmentation-saturated acting image, compatibility with finite-shadow patching | the clean one-prime datum, minimal theorem, primitive type lattices, reduced generic acting order, exact named augmentation, $\ell\geq7$ | supplies the complex whose amplitude collapses and locates its generic fibers; base freeness and the unique selected charts then give full source support |

No theorem from a later book is used.

### 18.2 Closure of every imported step

The imported hypotheses match the present uses as follows.

The minimal theorem is applied only after the datum of Sections 2.1--2.3 has repeated its coefficient-prime, image, determinant, adjoint-invariant, and automorphic hypotheses. Its module freeness is used over $S_\infty$ only on the fixed-prime augmentation face.

The local-type theorem is applied at $v\nmid\ell$ with a unit-valued tame label, a named enhanced special component, and explicit primary and companion lattices. It is not applied to a wild type or at a coefficient-prime place.

The Ihara and integral level-change theorems are applied to a proper clean Shimura curve at a non-Eisenstein localization with prime-to-$\ell$ stabilizer descent. Full-map saturation is kept distinct from the sign separation needed in (13.10).

Nonminimal reciprocity is applied to a finite flat faithful order with reduced generic fiber and branchwise local--global compatibility at every generic factor. The resulting map is used only as a surjection until Chapter 10.

The one-prime complex theorem is applied with both primary and companion objects, the fixed-prime and auxiliary algebras kept separate, and the exact augmentation of the acting image retained. Its support statement is not called faithfulness until reducedness is proved.

Solvable descent is used only after automorphy over the top field is known and an extending irreducible representation selects compatible twists. Local conductor and type behavior are checked on restricted parameters rather than inferred from solvability.

### 18.3 Circularity audit

The proof order is:

1. Minimal $R=T$ gives the augmented patched module.
2. The prior one-prime theorem gives a perfect complex, exact augmentation, and topological component support.
3. The augmented residue fiber kills degree zero in a minimal free model.
4. The resulting module is free over the combined patching base.
5. Reducedness of the selected source turns full support into faithfulness.
6. Nonminimal reciprocity's surjection becomes an isomorphism.
7. Auxiliary and tame augmentations descend the equality.
8. Cotangent, congruence, and lifting conclusions are derived afterward.

No step assumes nonminimal faithfulness, a nonminimal ring equality, or a cotangent-length equality before Chapter 10. Residual automorphy is used to make the minimal and augmented modules nonzero, not to declare every nonminimal component automorphic. Generic support is not promoted across nilpotents without Lemma 4.1.

### 18.4 Normalization audit

The normalization ledger is:

| datum | convention |
|---|---|
| Frobenius | geometric |
| good polynomial | $1-T_wX+q_wS_wX^2$ |
| Hecke operators | unnormalized right double cosets |
| adjoint | $T_w^*=S_w^{-1}T_w$ |
| determinant | fixed as $\delta_\chi$ on each character problem; universal family $\delta_{\Lambda_v}$ augments to $\delta^{\min}$ |
| trivial-central old Gram matrix | diagonal $q_v+1$, off-diagonal $T_v$ |
| selected signed factor | $q_v+1-\varepsilon_v a_v$ |
| fixed-prime augmentation | tame character $\chi_v\mapsto1$ |
| auxiliary augmentation | diamond characters at $Q_N$ map to $1$ |
| special conductor | one for unramified twist, two when the scalar twist has conductor exponent one |
| monodromy | $\rho(\phi)N\rho(\phi)^{-1}=q_v^{-1}N$ for geometric Frobenius |

The determinant, central character, line, and sign agree on the deformation and automorphic sides. The two augmentations commute because they act through different coefficient factors. Equation numbers and theorem references above refer only to statements already established when used.

## 19. Conclusion

### 19.1 The established package

The one-prime nonminimal problem begins with a genuine derived obstruction. The saturated degeneracy map produces a two-term type complex whose degree-zero cohomology after base change is exactly a first Tor group. Primary and companion lattices put the selected conductor-two special family into that complex at a primitive integral scale. Its support is the full selected component, but before patching this is only a statement about closed sets.

Patching preserves the differential, both group algebras, both augmentations, the deformation and Hecke actions, the companion pairing, and the determinant comparison. Fixed-prime augmentation recovers the minimal patched module exactly. The residue fiber consequently has no degree-zero cohomology, and minimal-complex theory collapses the universal patched type complex to a finite free module over

$$
\Lambda_v\widehat\otimes_{\mathcal O}
\mathcal O[[z_1,\ldots,z_q]].
$$

This proves, rather than assumes, flatness in every tame and auxiliary direction.

The selected patched deformation source is flat over $\mathcal O$ and generically reduced, hence reduced. Full component support of the surviving module then gives a zero annihilator. Nonminimal reciprocity supplies a surjection from the deformation ring to the faithful Hecke image, and the faithful action kills its kernel. Thus

$$
R_\infty^{(2)}=\mathbb T_\infty^{(2)}.
$$

Exact auxiliary augmentation descends this equality to the universal tame finite-level problem, and character specialization gives the conductor-two equality

$$
\boxed{R_\chi^{(2)}=\mathbb T_\chi^{(2)}}
$$

for every retained nontrivial tame character. Fixed-prime augmentation returns the named conductor-one minimal theorem. Coefficient extension introduces no lattice or congruence index and descends faithfully.

After the equality is known, complete-intersection algebra identifies cotangent and congruence ideals. On a primitive isolated sign branch their one-prime factor is

$$
q_v+1-\varepsilon_v a_v,
$$

with automorphic multiplicity and companion discriminant treated explicitly. The old Gram cokernel, graph component group, and specialization Tor module retain distinct meanings.

Finally, every fixed-determinant lift satisfying the compatible finite-flat weight-$\{0,1\}$ conditions at places above $\ell$, the named minimal conditions away from $v$, and the enhanced conductor-two special condition at $v$ determines a point of the common ring and hence a cuspidal parallel-weight-two automorphic representation with the same integral Galois lattice. Under the stated compatibility and irreducibility hypotheses, this automorphy descends through solvable totally real extensions. The theorem remains in the uniform range $\ell\geq7$ and makes no small-image assertion at five.
