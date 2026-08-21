# Hecke Algebras and Congruences

## Contents

1. [From operators to an integral algebra](#1-from-operators-to-an-integral-algebra)
   - [The comparison problem](#11-the-comparison-problem)
   - [The integral automorphic module](#12-the-integral-automorphic-module)
   - [Abstract and acting algebras](#13-abstract-and-acting-algebras)
   - [The specified away-from-bad-set algebra](#14-the-specified-away-from-bad-set-algebra)
2. [Finite integral Hecke algebras](#2-finite-integral-hecke-algebras)
   - [Finiteness from faithful action](#21-finiteness-from-faithful-action)
   - [Torsion-freeness and finite flatness](#22-torsion-freeness-and-finite-flatness)
   - [Where commutativity comes from](#23-where-commutativity-comes-from)
   - [Base change and the image trap](#24-base-change-and-the-image-trap)
3. [Eigensystems over fields](#3-eigensystems-over-fields)
   - [Characters rather than chosen vectors](#31-characters-rather-than-chosen-vectors)
   - [Coefficient-field enlargement](#32-coefficient-field-enlargement)
   - [Simultaneous generalized eigenspaces](#33-simultaneous-generalized-eigenspaces)
   - [Eigenvectors, characters, and multiplicity](#34-eigenvectors-characters-and-multiplicity)
4. [Residual eigensystems](#4-residual-eigensystems)
   - [Why maximal ideals are the right integral points](#41-why-maximal-ideals-are-the-right-integral-points)
   - [Residue fields and reductions of eigencharacters](#42-residue-fields-and-reductions-of-eigencharacters)
   - [Enlarging the coefficient DVR](#43-enlarging-the-coefficient-dvr)
   - [What lifts, and what does not](#44-what-lifts-and-what-does-not)
5. [Localization and finite-level decomposition](#5-localization-and-finite-level-decomposition)
   - [Localizing the algebra and the module](#51-localizing-the-algebra-and-the-module)
   - [Support and faithfulness](#52-support-and-faithfulness)
   - [Idempotents and generalized residual summands](#53-idempotents-and-generalized-residual-summands)
   - [Localization versus quotienting](#54-localization-versus-quotienting)
6. [Completion at a residual system](#6-completion-at-a-residual-system)
   - [Two meanings of completion in practice](#61-two-meanings-of-completion-in-practice)
   - [Finite local algebras over a complete DVR](#62-finite-local-algebras-over-a-complete-dvr)
   - [Genuine inverse-limit constructions](#63-genuine-inverse-limit-constructions)
   - [Completed localized modules](#64-completed-localized-modules)
7. [Congruences of characteristic-zero eigensystems](#7-congruences-of-characteristic-zero-eigensystems)
   - [Congruence through a common residual maximal ideal](#71-congruence-through-a-common-residual-maximal-ideal)
   - [Depth measured by valuations](#72-depth-measured-by-valuations)
   - [Basis-independent congruence ideals](#73-basis-independent-congruence-ideals)
   - [Eigencharacters without congruent eigenvectors](#74-eigencharacters-without-congruent-eigenvectors)
8. [Normalization and branches](#8-normalization-and-branches)
   - [Generic packets and integral branches](#81-generic-packets-and-integral-branches)
   - [Normalization of a finite Hecke algebra](#82-normalization-of-a-finite-hecke-algebra)
   - [Crossings in the special fiber](#83-crossings-in-the-special-fiber)
   - [Nilpotents and what they record](#84-nilpotents-and-what-they-record)
   - [Exact criteria for reducedness](#85-exact-criteria-for-reducedness)
9. [Pairings, adjoints, and dual Hecke modules](#9-pairings-adjoints-and-dual-hecke-modules)
   - [The pairing problem](#91-the-pairing-problem)
   - [Adjoint-stable Hecke algebras](#92-adjoint-stable-hecke-algebras)
   - [Dual modules and self-duality](#93-dual-modules-and-self-duality)
   - [When Gorenstein-like duality follows](#94-when-gorenstein-like-duality-follows)
10. [Old submodules at a new prime](#10-old-submodules-at-a-new-prime)
    - [Degeneracy maps and the old image](#101-degeneracy-maps-and-the-old-image)
    - [Hecke stability and the changed prime](#102-hecke-stability-and-the-changed-prime)
    - [Adjoint trace maps and the Gram operator](#103-adjoint-trace-maps-and-the-gram-operator)
    - [Old submodule and old quotient conventions](#104-old-submodule-and-old-quotient-conventions)
11. [New modules and integral orthogonality](#11-new-modules-and-integral-orthogonality)
    - [Kernel-of-adjoints definition](#111-kernel-of-adjoints-definition)
    - [Orthogonal complements under perfectness](#112-orthogonal-complements-under-perfectness)
    - [Saturation and torsion caveats](#113-saturation-and-torsion-caveats)
    - [When old plus new is a decomposition](#114-when-old-plus-new-is-a-decomposition)
12. [Control under change of level](#12-control-under-change-of-level)
    - [Comparison maps after localization](#121-comparison-maps-after-localization)
    - [Formal injectivity and surjectivity criteria](#122-formal-injectivity-and-surjectivity-criteria)
    - [The deeper input in an Ihara-type lemma](#123-the-deeper-input-in-an-ihara-type-lemma)
    - [Comparing acting Hecke algebras](#124-comparing-acting-hecke-algebras)
13. [Congruence modules and congruence ideals](#13-congruence-modules-and-congruence-ideals)
    - [Failure of two lattices to split](#131-failure-of-two-lattices-to-split)
    - [An elementary finite-module construction](#132-an-elementary-finite-module-construction)
    - [Fitting and annihilator ideals](#133-fitting-and-annihilator-ideals)
    - [The degeneracy determinant](#134-the-degeneracy-determinant)
14. [Freeness and projectivity: exact criteria](#14-freeness-and-projectivity-exact-criteria)
    - [Over the coefficient ring](#141-over-the-coefficient-ring)
    - [Over the Hecke algebra](#142-over-the-hecke-algebra)
    - [Multiplicity and rank-one criteria](#143-multiplicity-and-rank-one-criteria)
    - [Counterexamples to automatic freeness](#144-counterexamples-to-automatic-freeness)
15. [Brandt matrices and visible congruences](#15-brandt-matrices-and-visible-congruences)
    - [A two-class calculation](#151-a-two-class-calculation)
    - [Two packets meeting modulo a prime](#152-two-packets-meeting-modulo-a-prime)
    - [A nonsemisimple special fiber](#153-a-nonsemisimple-special-fiber)
    - [A three-class weighted check](#154-a-three-class-weighted-check)
16. [Augmentations, cotangent modules, and congruence ideals](#16-augmentations-cotangent-modules-and-congruence-ideals)
    - [Why one branch must be distinguished](#161-why-one-branch-must-be-distinguished)
    - [The congruence ideal of an augmentation](#162-the-congruence-ideal-of-an-augmentation)
    - [The cotangent module at the branch](#163-the-cotangent-module-at-the-branch)
    - [A complete-intersection determinant calculation](#164-a-complete-intersection-determinant-calculation)
    - [Gorenstein duality and congruence functionals](#165-gorenstein-duality-and-congruence-functionals)
    - [Several branches and nonprincipal congruence data](#166-several-branches-and-nonprincipal-congruence-data)
17. [Comparison with deformation-theoretic numerical invariants](#17-comparison-with-deformation-theoretic-numerical-invariants)
    - [The comparison problem without a constructed map](#171-the-comparison-problem-without-a-constructed-map)
    - [The conormal comparison for a surjection](#172-the-conormal-comparison-for-a-surjection)
    - [Tangent dimensions and relation bounds](#173-tangent-dimensions-and-relation-bounds)
    - [The exact numerical chain](#174-the-exact-numerical-chain)
    - [A safe numerical forcing theorem](#175-a-safe-numerical-forcing-theorem)
    - [What equality does and does not prove](#176-what-equality-does-and-does-not-prove)
    - [Old--new congruence numbers in the comparison](#177-old--new-congruence-numbers-in-the-comparison)
18. [The complete local Hecke pair](#18-the-complete-local-hecke-pair)
    - [Construction of the pair](#181-construction-of-the-pair)
    - [Its exact structural properties](#182-its-exact-structural-properties)
    - [Its augmented numerical package](#183-its-augmented-numerical-package)
    - [What remains for later comparison](#184-what-remains-for-later-comparison)
    - [The algebra--congruence--localization dictionary](#185-the-algebra--congruence--localization-dictionary)
    - [Conclusion](#186-conclusion)

## 1. From operators to an integral algebra

### 1.1 The comparison problem

The preceding construction ended with a finite integral module carrying many commuting correspondences. That is not yet the algebraic object needed in arithmetic comparison. A list of operators does not say which polynomial relations they satisfy on the chosen space, which residual eigensystem one intends to study, or how information supported at all the other eigensystems should be discarded. The task of this book is to perform those passages without losing the integral lattice that makes congruence meaningful.

There are three scales. Over the fraction field, commuting operators have characters and generalized eigenspaces. Over the residue field, systems that were distinct can merge. Over the coefficient ring, localization isolates one merger and completion remembers it to every order. The same operator family appears at all three scales, but its algebra changes by scalar extension, localization, reduction, and completion. These operations do not commute without hypotheses.

Our setting is deliberately finite. Fix a totally real field $F$, a totally definite quaternion algebra $D/F$, a compact-open level $U\subset D_f^\times$, an algebraic weight lattice, and compatible central data as established earlier. Fix also a finite set $\Sigma$ of bad places. It contains every place where $D$ is ramified, every nonhyperspecial level place, the coefficient place, every place where the lattice or character is ramified, and any additional place excluded from the comparison. At $v\notin\Sigma$ we retain the unnormalized spherical operators $T_v$ and $S_v$, with polynomial

$$
P_v(X)=1-T_vX+q_vS_vX^2.
$$

We will not attach any new object to this polynomial. Its role here is to keep the operator normalization fixed. Later comparison theories will need precisely its two coefficients, but nothing in the present algebra requires a representation of an absolute Galois group.

### 1.2 The integral automorphic module

Let $\mathcal O$ be a complete discrete valuation ring with uniformizer $\varpi$, fraction field $E$, and residue field $k$. A finite extension of $E$ will always be given its extended valuation, and its valuation ring will be denoted by a primed or indexed version of $\mathcal O$.

Write, using the representative-value integral lattice of Book 83,

$$
M=M_{\mathcal O}(U;W,\chi).
$$

This is the exact integral module of quaternionic forms, not a globally $D^\times$-stable weight lattice and not the possibly larger module formed directly after reduction. We assume throughout Chapters 1--8 that:

1. $M$ is a finite torsion-free $\mathcal O$-module;
2. every specified $T_v,S_v$ preserves $M$;
3. the specified operators commute on $M$.

Because $\mathcal O$ is a DVR, the first condition makes $M$ finite free. It follows, for example, when the finite stabilizer construction produces a torsion-free submodule of a finite free weight lattice. Clean base change to $k$ is a separate matter: $M/\varpi M$ need not equal the automorphic module formed directly over $k$ at a bad stabilizer prime.

This distinction is essential. Our Hecke algebra is initially the algebra acting on $M$. Its special fiber acts on $M/\varpi M$. If a larger directly formed mod-$\varpi$ space exists, its additional operators and eigensystems are not automatically represented by this lattice Hecke algebra.

### 1.3 Abstract and acting algebras

The formal away-from-$\Sigma$ algebra is

$$
\mathbb T^{\Sigma,\mathrm{abs}}_{\mathcal O}
=\mathcal O[T_v,S_v,S_v^{-1}:v\notin\Sigma],
$$

understood as the restricted tensor product: each element is a polynomial in finitely many places. If the central character has already specialized $S_v$ to a known unit, one may quotient by the corresponding relations or simply omit $S_v$ from the chosen generating family. The choice must be stated once and retained.

The action gives a homomorphism

$$
\rho_M:\mathbb T^{\Sigma,\mathrm{abs}}_{\mathcal O}
\longrightarrow\operatorname{End}_{\mathcal O}(M).
$$

The **acting**, **image**, or **faithful Hecke algebra** is

$$
\boxed{
\mathbb T=\mathbb T^{\Sigma}(M)
=\operatorname{im}(\rho_M)
\subseteq\operatorname{End}_{\mathcal O}(M).}
$$

Thus $M$ is faithful as a $\mathbb T$-module by definition. It need not be faithful over the abstract algebra. An abstract relation can vanish on this weight and level while remaining nonzero on another module. Conversely, passing to the image can identify formally distinct operators.

This choice is not cosmetic. Localization of the abstract algebra at a maximal ideal outside the support of $M$ produces a nonzero local ring acting on the zero module. Localization of the image algebra never has that pathology: every prime of $\mathbb T$ belongs to the support of its faithful module. The downstream algebra is therefore the image.

**Example.** Let the abstract algebra be $\mathcal O[X]$ and let $M=\mathcal O^2$, with $X$ acting as $\operatorname{diag}(0,1)$. The image is

$$
\mathcal O[X]/(X(X-1))\cong\mathcal O\times\mathcal O.
$$

The abstract maximal ideal $(\varpi,X-2)$ can exist when $2$ has a residue in $k$, but if that residue is neither $0$ nor $1$, localizing $M$ there gives zero. It is not a residual eigensystem occurring in the chosen automorphic module. The image has retained exactly the occurring support.

### 1.4 The specified away-from-bad-set algebra

An acting algebra depends on its generating family. We write

$$
\mathbb T=\mathcal O[T_v,S_v^{\pm1}:v\notin\Sigma]
\subseteq\operatorname{End}_{\mathcal O}(M)
$$

only after declaring that the symbols on the right mean their images. Operators at places in $\Sigma$ are excluded unless explicitly adjoined. A $U_v$ at a level prime, an involution, or a central ray-class operator may enlarge the algebra and refine its maximal ideals. Two eigensystems equal away from $\Sigma$ can differ at an omitted place; the present algebra intentionally does not distinguish them.

There is no need for infinitely many algebra generators in the image. For each finite subset $J$ of the specified Hecke family, let $\mathbb T_J$ be the $\mathcal O$-subalgebra of $\operatorname{End}_{\mathcal O}(M)$ generated by $J$. The directed union of the $\mathbb T_J$ is $\mathbb T$. Since $\operatorname{End}_{\mathcal O}(M)$ is a finite module over the Noetherian ring $\mathcal O$, its submodule $\mathbb T$ is generated by finitely many elements $b_1,\ldots,b_s$. Each $b_i$ belongs to some $\mathbb T_{J_i}$, so the union $J_1\cup\cdots\cup J_s$ is a finite subset whose generated algebra contains every $b_i$ and therefore equals $\mathbb T$. Thus finitely many specified operators generate $\mathbb T$ as an $\mathcal O$-algebra. This finite generation is a consequence of finite action, not of a claim that only finitely many places exist. Notice that the chosen Hecke operators need not themselves span $\mathbb T$ as an $\mathcal O$-module: their products can be needed for that.

The first chapter has therefore made the decisive transition:

$$
\text{commuting correspondences}
\longrightarrow
\text{a finite faithful integral image algebra}.
$$

Every localization and congruence below refers to that image unless the label “abstract” explicitly appears.

## 2. Finite integral Hecke algebras

### 2.1 Finiteness from faithful action

The image construction immediately gives the finiteness needed for local algebra.

**Proposition 2.1.** If $M$ is a finite $\mathcal O$-module, then $\mathbb T\subseteq\operatorname{End}_{\mathcal O}(M)$ is a finite $\mathcal O$-module.

**Proof strategy.** A submodule of a finite module over the Noetherian ring $\mathcal O$ is finite. It remains only to see that the endomorphism module is finite.

**Proof.** Choose a finite presentation $\mathcal O^a\to\mathcal O^b\to M\to0$. Applying $\operatorname{Hom}_{\mathcal O}(-,M)$ embeds $\operatorname{End}_{\mathcal O}(M)$ into $M^b$, so it is finite. The submodule $\mathbb T$ is therefore finite. $\square$

When $M$ is free of rank $r$, this is more concrete:

$$
\mathbb T\subseteq M_r(\mathcal O),
$$

so $\mathbb T$ has $\mathcal O$-rank at most $r^2$. Commutativity can improve this bound after passing to a splitting field, but no sharper uniform rank is needed here.

Finiteness has several immediate consequences. The ring $\mathbb T$ is Noetherian, every maximal ideal has finite residue field extension of $k$, and $\mathbb T_E=\mathbb T\otimes_{\mathcal O}E$ is a finite-dimensional commutative $E$-algebra. None of these conclusions says that $\mathbb T$ is reduced, local, or generated by one operator.

### 2.2 Torsion-freeness and finite flatness

The coefficient ring is a domain, and $M$ is torsion-free. Hence $\operatorname{End}_{\mathcal O}(M)$ is torsion-free: if $0\ne a\in\mathcal O$ and $af=0$, then $af(x)=0$ for every $x$, so $f(x)=0$. Every submodule, including $\mathbb T$, is torsion-free.

**Corollary 2.2.** Under the standing hypotheses, $\mathbb T$ is finite free over $\mathcal O$. In particular it is finite flat.

**Proof.** It is finite and torsion-free over a DVR, hence free. $\square$

The exact hypotheses matter. If the coefficient ring is a general complete Noetherian local ring, finite torsion-free need not imply flat or free. If $M$ contains coefficient torsion, the endomorphism ring can contain torsion as an $\mathcal O$-module. If one defines a quotient of the abstract algebra without identifying it with an image in a torsion-free endomorphism module, flatness does not follow.

Finite flatness over $\mathcal O$ is one of the durable properties of the image algebra. It implies that no whole characteristic-zero branch disappears under multiplication by $\varpi$, although branches may meet and the special fiber may acquire nilpotents.

### 2.3 Where commutativity comes from

Commutativity is not a formal consequence of being a Hecke algebra. It comes from the chosen operators. At distinct places the operators commute because the adelic factors commute. At each split hyperspecial place the spherical algebra is commutative. Therefore the algebra generated solely by the away-from-$\Sigma$ family is commutative.

By contrast, adjoining a full Iwahori algebra at a level place can destroy commutativity. Even a single operator and its adjoint need not commute at oriented level. The phrase “the Hecke algebra” is thus incomplete until the generating family is specified.

In this book $\mathbb T$ is always commutative. If selected level-prime operators are adjoined later, we assume and verify that they commute with the current algebra and with one another on the chosen module. Otherwise one has a noncommutative module theory in which maximal ideals and characters no longer organize the action in the same way.

### 2.4 Base change and the image trap

There is a canonical map

$$
\mathbb T\otimes_{\mathcal O}A
\longrightarrow
\operatorname{End}_A(M\otimes_{\mathcal O}A)
$$

for any $\mathcal O$-algebra $A$. Its image is generated by the base-changed Hecke operators. It need not identify the source with that image: tensoring an injection need not remain injective when $A$ is not flat.

If $A$ is flat over $\mathcal O$, then

$$
\mathbb T\otimes_{\mathcal O}A
\hookrightarrow
\operatorname{End}_{\mathcal O}(M)\otimes_{\mathcal O}A.
$$

When $M$ is finite free, the right side is canonically $\operatorname{End}_A(M\otimes A)$, so the base-changed algebra remains the faithful image. This applies to $A=E$ and to finite extensions of $\mathcal O$ that are torsion-free.

Reduction $A=k$ is not flat. The map

$$
\mathbb T/\varpi\mathbb T
\longrightarrow
\operatorname{End}_k(M/\varpi M)
$$

can have a kernel. An integral endomorphism may be nonzero and not divisible by $\varpi$ inside $\mathbb T$, yet have all matrix entries divisible by $\varpi$ relative to $M$. This happens precisely when the inclusion $\mathbb T\subseteq\operatorname{End}_{\mathcal O}(M)$ is not saturated.

Accordingly, there are two special-fiber algebras:

$$
\mathbb T\otimes k
\quad\text{and}\quad
\overline{\mathbb T}^{\,\mathrm{act}}
=\operatorname{im}\bigl(\mathbb T\to\operatorname{End}_k(M/\varpi M)\bigr).
$$

The second is a quotient of the first. Maximal ideals of $\mathbb T$ containing $\varpi$ still organize the integral algebra, even when its special-fiber action is not faithful. If a later argument needs faithfulness after reduction, it must prove saturation or replace the special fiber by its acting image.

Here is a small model of the image trap. Let $M=\mathcal O^2$ and let $u$ be the endomorphism with matrix $\varpi E_{12}$. The algebra

$$
A=\mathcal O[u]\cong\mathcal O[X]/(X^2)
$$

is more transparently described as $\mathcal O\oplus\mathcal O u$ with $u^2=0$. It is free of rank two as an abstract $\mathcal O$-module and acts faithfully on $M$. On $M/\varpi M$, however, $u$ acts as zero. Hence

$$
A/\varpi A\cong k[\bar u]/(\bar u^2)
$$

maps onto the scalar algebra $k$ with kernel $(\bar u)$. The nilpotent in the tensor special fiber records an integral endomorphism divisible in the ambient matrix algebra, while the actual reduced action cannot see it. This example also explains why one should not infer the geometry of $\operatorname{Spec}(\mathbb T/\varpi)$ solely from its representation on $M/\varpi M$ unless the inclusion of algebras is saturated.

There is a useful sufficient condition for saturation. If the quotient

$$
\operatorname{End}_{\mathcal O}(M)/\mathbb T
$$

is $\mathcal O$-torsion-free, then tensoring the inclusion with $k$ remains injective. Equivalently, whenever an endomorphism $t\in\mathbb T$ has all matrix entries divisible by $\varpi$, the divided endomorphism $\varpi^{-1}t$ already lies in $\mathbb T$. This is a strong condition on the order $\mathbb T$ inside its generic algebra; it is not forced by finite flatness.

## 3. Eigensystems over fields

### 3.1 Characters rather than chosen vectors

Over a field, simultaneous eigenvalues are best recorded by a homomorphism from the acting algebra. Let $L/E$ be a field extension. An **$L$-valued eigensystem** of $\mathbb T$ is an $E$-algebra homomorphism

$$
\lambda:\mathbb T_E\longrightarrow L.
$$

Equivalently, it is an $\mathcal O$-algebra homomorphism $\mathbb T\to L$, where $\mathcal O$ acts through $E\subseteq L$. The eigenvalue at $v\notin\Sigma$ is $\lambda(T_v)$, and similarly for $S_v$.

The character defines a one-dimensional $\mathbb T_E$-module $L_\lambda$. It occurs in $M_L=M\otimes_{\mathcal O}L$ when

$$
M_L[\lambda]
=\{x\in M_L:tx=\lambda(t)x\text{ for all }t\in\mathbb T\}
$$

is nonzero. Since $\mathbb T$ was defined as the image on $M$, every character of $\mathbb T_E$ occurs after extending to an algebraic closure. Indeed, a maximal ideal of the finite-dimensional algebra acts noninvertibly on the faithful module; the corresponding simple module occurs in a composition series.

The character is intrinsic; an eigenvector is not. Scaling a vector, choosing a basis in a multiplicity space, or replacing it by another vector with the same eigenvalues changes no character.

There is also an economical tensor description. Regard $L$ as a $\mathbb T_E$-algebra through $\lambda$. Then

$$
M_L[\lambda]
\cong
\operatorname{Hom}_{\mathbb T_L}(L_\lambda,M_L),
$$

while the maximal semisimple quotient on which $\mathbb T$ acts through $\lambda$ is

$$
M_L\otimes_{\mathbb T_L,\lambda}L
=M_L/\mathfrak p_\lambda M_L.
$$

The first is a subspace and the second a quotient. They have equal dimension when the local algebra acts semisimply and a perfect duality identifies the relevant multiplicities, but not in general. Confusing them is the field-level version of confusing an old submodule with an old quotient.

### 3.2 Coefficient-field enlargement

A finite-dimensional commutative $E$-algebra need not split over $E$. For example, multiplication by a root of an irreducible quadratic polynomial can have no $E$-eigenvector. If $\overline E$ is an algebraic closure, then

$$
\mathbb T_{\overline E}
=\mathbb T_E\otimes_E\overline E
$$

has finitely many characters $\lambda:\mathbb T_E\to\overline E$. Their values generate finite extensions of $E$ because $\mathbb T_E$ is finite-dimensional. Thus every eigensystem is defined over some finite extension $L/E$.

It is useful to distinguish three enlargements:

- enlarge $E$ enough to contain the eigenvalues;
- enlarge further so every factor of $\mathbb T_E$ splits;
- enlarge the valuation ring to the integral closure $\mathcal O_L$ so reductions of integral eigenvalues are defined.

The first two are field operations. The third remembers a chosen place above $\varpi$. Different embeddings of the same eigenvalue field into $\overline E$ can lead to different primes and hence different residual systems.

Because each $t\in\mathbb T$ is integral over $\mathcal O$, every $\lambda(t)$ is integral over $\mathcal O$. Therefore an $L$-valued eigencharacter maps

$$
\lambda:\mathbb T\longrightarrow\mathcal O_L
$$

after replacing $L$ by a finite extension containing its values. No choice of normalized eigenvector is required for this integrality statement; it follows from the finite algebra.

**Worked nonsplit example.** Let $f(X)\in\mathcal O[X]$ be monic with irreducible generic fiber and let

$$
\mathbb T=\mathcal O[X]/(f).
$$

Let $M=\mathbb T$ with the regular action. Over $E$, there is no $E$-valued character if $f$ has no root in $E$, even though $M_E$ is a faithful nonzero module. If $L$ contains a root $\alpha$, evaluation $X\mapsto\alpha$ is an eigensystem. In the basis $1,X,\ldots,X^{d-1}$, multiplication by $X$ has the companion matrix of $f$; an eigenvector appears only after extension to $L$. The system was present over $E$ as a closed point with residue field $E(\alpha)$, not as a vector with $E$-valued eigenvalues.

### 3.3 Simultaneous generalized eigenspaces

Commuting operators need not be diagonalizable. For a character $\lambda:\mathbb T_L\to L$, let

$$
\mathfrak p_\lambda=\ker(\lambda)\subset\mathbb T_L.
$$

The generalized $\lambda$-eigenspace is

$$
M_L[\lambda]^\mathrm{gen}
=\{x\in M_L:\mathfrak p_\lambda^N x=0
\text{ for some }N\ge1\}.
$$

One exponent can be chosen for all $x$ because $M_L$ is finite-dimensional. If $L$ splits the semisimple residue fields of $\mathbb T_E$, then Artinian ring theory gives a canonical decomposition

$$
M_L=\bigoplus_\lambda M_L[\lambda]^\mathrm{gen}.
$$

**Proof strategy.** A finite-dimensional commutative algebra is Artinian and is the product of its localizations at maximal ideals. The corresponding central idempotents split every module.

**Proof.** Write

$$
\mathbb T_L\cong\prod_\lambda(\mathbb T_L)_{\mathfrak p_\lambda}.
$$

Let $e_\lambda$ be the identity of the $\lambda$th factor. Then $1=\sum e_\lambda$, the idempotents are pairwise orthogonal, and

$$
M_L=\bigoplus e_\lambda M_L.
$$

In the local Artinian factor the maximal ideal is nilpotent, so $e_\lambda M_L$ is exactly the generalized eigenspace. $\square$

Ordinary eigenvectors form the socle of this generalized module with respect to the maximal ideal. They may be much smaller than it.

**Example.** Let $T$ act on $L^2$ by

$$
\begin{pmatrix}a&1\\0&a\end{pmatrix}.
$$

There is one character $T\mapsto a$, one-dimensional ordinary eigenspace, and two-dimensional generalized eigenspace. The character records the packet; the Jordan block records a nonsemisimple action invisible in the list of eigenvalues.

### 3.4 Eigenvectors, characters, and multiplicity

Four notions must remain separate.

1. A character $\lambda$ is a ring homomorphism.
2. An eigenvector is a nonzero vector on which every operator acts through $\lambda$.
3. The eigenspace $M_L[\lambda]$ can have dimension greater than one.
4. The generalized eigenspace can strictly contain the eigenspace.

Faithfulness of $M$ does not imply multiplicity one. Nor does commutativity imply semisimplicity. If $\mathbb T_E$ is reduced, then it is a product of finite field extensions and becomes a product of copies of a splitting field after scalar extension; in that case every $\mathbb T$-module is semisimple. But reducedness of $\mathbb T_E$ is an additional assertion, often proved from a positive-definite self-adjoint realization, not from commutativity alone.

Even if $\mathbb T_E$ is reduced, an eigencharacter can occur with multiplicity $d>1$ in $M_E$. The algebra acts by the same scalars on a $d$-dimensional space. A theorem asserting that the localized automorphic module is rank one over a local Hecke algebra requires a genuine multiplicity statement.

## 4. Residual eigensystems

### 4.1 Why maximal ideals are the right integral points

Characteristic-zero characters can become indistinguishable after reduction. The intrinsic record of a residual eigensystem is not a chosen list of residues in a preselected field but a maximal ideal of the integral Hecke algebra containing the coefficient uniformizer.

**Definition 4.1.** A **residual system of Hecke eigenvalues** occurring in $M$ is a maximal ideal

$$
\mathfrak m\subset\mathbb T,
\qquad\varpi\in\mathfrak m.
$$

Its residue field is

$$
k(\mathfrak m)=\mathbb T/\mathfrak m,
$$

a finite extension of $k$. The associated residual character is the quotient map

$$
\bar\lambda_{\mathfrak m}:\mathbb T\longrightarrow k(\mathfrak m).
$$

Maximal, rather than merely prime, ideals are used because a system of scalar eigenvalues lands in a field. Since $\mathbb T/\varpi\mathbb T$ is Artinian, every prime containing $\varpi$ is maximal, but the conceptual distinction remains useful when generic-fiber primes are discussed.

The definition is independent of generators. Writing the residues $\bar t_v$ and $\bar s_v$ is shorthand for evaluating the quotient map on $T_v$ and $S_v$. If the specified family generates $\mathbb T$, those values determine $\mathfrak m$; otherwise a partial list may fail to do so.

### 4.2 Residue fields and reductions of eigencharacters

Let $\lambda:\mathbb T\to\mathcal O_L$ be an integral characteristic-zero eigencharacter, and let $\mathfrak p_L$ be the maximal ideal of $\mathcal O_L$. Reduction gives

$$
\bar\lambda:\mathbb T\longrightarrow k_L=\mathcal O_L/\mathfrak p_L.
$$

Its kernel

$$
\mathfrak m_\lambda=\lambda^{-1}(\mathfrak p_L)
$$

is maximal and contains $\varpi$. The image field of $\bar\lambda$ is canonically isomorphic to $k(\mathfrak m_\lambda)$, possibly a proper subfield of the chosen $k_L$ only if $L$ was enlarged after the eigenvalues were already defined.

Two characters with values in different finite extensions can therefore be compared without first identifying their ambient residue fields: they are intrinsically residually congruent when their kernels in $\mathbb T$ are the same maximal ideal $\mathfrak m$. Their image fields are then both identified with the quotient $k(\mathfrak m)$. If one wants literal equality of values in a common finite residue extension, one chooses embeddings of the two ambient residue fields whose restrictions to these identified copies of $k(\mathfrak m)$ agree. Arbitrary embeddings need not do so; they can differ by an automorphism of the finite residue field.

Suppose the image algebra is generated by $t_1,\ldots,t_r$. Then a residual maximal ideal may be written

$$
\mathfrak m=(\varpi,
t_1-\bar a_1,\ldots,t_r-\bar a_r)
$$

after enlarging $k$ enough to contain $k(\mathfrak m)$ and choosing lifts of the residues. This notation is computationally useful but noncanonical: a different generating family gives different displayed generators for the same ideal. The ideal itself also remembers all algebraic relations among the $\bar a_i$, so an arbitrary tuple in $k^r$ need not define a residual eigensystem.

For example, if $\mathbb T=\mathcal O[X]/(X^2-X)$, the only residual values of $X$ are $0$ and $1$ unless the two coincide in the residue field. A proposed residual value $c$ with $c^2\ne c$ violates the relation and defines no homomorphism. Lists of eigenvalues are always constrained points of the image algebra.

### 4.3 Enlarging the coefficient DVR

Suppose $k(\mathfrak m)\ne k$. If $k(\mathfrak m)/k$ is separable and the usual unramified lifting theorem applies to $\mathcal O$—in particular, when $k$ is finite—choose a finite unramified extension $\mathcal O'/\mathcal O$ whose residue field contains $k(\mathfrak m)$. Then the residual character can be viewed as $k'$-valued, and

$$
\mathbb T'=\mathbb T\otimes_{\mathcal O}\mathcal O'
$$

has one or more maximal ideals above $\mathfrak m$. A choice of embedding $k(\mathfrak m)\hookrightarrow k'$ selects one of them. Without the separability or lifting hypothesis, one should retain the canonical residue field $k(\mathfrak m)$ rather than assert that it comes from an unramified coefficient extension.

Ramified enlargement may be needed to contain characteristic-zero eigenvalues, but it does not enlarge the residue field. These roles should not be conflated. Unramified extension separates residual embeddings; ramified extension can separate characteristic-zero branches by adjoining integral eigenvalues.

Under finite flat scalar extension, $M'=M\otimes\mathcal O'$ remains faithful for $\mathbb T'$. If one then localizes at a chosen maximal ideal $\mathfrak m'$, the resulting summand corresponds to one chosen residual embedding. This is often convenient, but the original $\mathfrak m$-localized object over $\mathcal O$ is more canonical.

### 4.4 What lifts, and what does not

Lifting a residual system has three different meanings: lifting its maximal ideal to a generic algebra character, realizing that character on a primitive integral eigenvector after extending coefficients, and lifting a prescribed residual eigenvector. The first two do hold in the present finite flat image algebra after a suitable finite coefficient extension. The third is not formal.

**Proposition 4.2 (generic and primitive lifting).** Let $\mathfrak m\supset(\varpi)$ be a maximal ideal of $\mathbb T$. Then there are a finite extension $L/E$, a valuation ring $\mathcal O_L$ above $\mathcal O$ with residue field $k_L$, and a character

$$
\lambda:\mathbb T\longrightarrow\mathcal O_L
$$

whose residual kernel is $\mathfrak m$. Moreover, after enlarging $L$ if necessary, there is a simultaneous $\lambda$-eigenvector in $M\otimes_{\mathcal O}\mathcal O_L$ whose reduction is nonzero and on which $\mathbb T$ acts through the scalar extension of $\bar\lambda_{\mathfrak m}$ to the residue field of $\mathcal O_L$.

**Proof strategy.** Finite flatness prevents a residual point from lying only on a vertical component. A minimal prime below $\mathfrak m$ therefore gives a characteristic-zero branch. After normalizing that branch at a prime above $\mathfrak m$, its character is integral. Faithfulness supplies an eigenvector on the generic fiber, and intersection of its eigenspace with the lattice is saturated, so a primitive vector has nonzero reduction.

**Proof.** Choose a minimal prime $\mathfrak p\subseteq\mathfrak m$. Since $\mathbb T$ is finite and $\mathcal O$-torsion-free, multiplication by $\varpi$ is injective; a nonzerodivisor in a Noetherian ring belongs to no minimal prime. Thus $\mathfrak p$ survives in $\mathbb T_E$. The domain $\mathbb T/\mathfrak p$ is finite over $\mathcal O$, and its fraction field $L$ is a finite extension of $E$. Take the integral closure of $\mathcal O$ in $L$ and choose a maximal ideal above $\mathfrak m/\mathfrak p$. Localizing there gives a valuation ring $\mathcal O_L$ and an integral character $\lambda:\mathbb T\to\mathcal O_L$. The chosen maximal ideal contracts to $\mathfrak m/\mathfrak p$, so the kernel of the reduction of $\lambda$ is exactly $\mathfrak m$.

By Section 3.1, the character $\lambda$ occurs on $M_L$. Let $V_\lambda=M_L[\lambda]$, which is nonzero, and put

$$
\Lambda_\lambda
=V_\lambda\cap(M\otimes_{\mathcal O}\mathcal O_L).
$$

After enlarging $L$ so that the eigenvalues and one nonzero eigenvector are defined, this intersection is a nonzero $\mathcal O_L$-lattice in $V_\lambda$. It is saturated in $M\otimes\mathcal O_L$: if $\pi_Lx\in V_\lambda$, then $x\in V_\lambda$ because $V_\lambda$ is an $L$-subspace. It therefore contains an element outside $\pi_L(M\otimes\mathcal O_L)$; otherwise saturation would permit division by $\pi_L$ indefinitely, contradicting the finite valuation of a nonzero lattice element. Such an element is an integral simultaneous eigenvector with nonzero reduction. Reducing its eigenvalue equations gives the scalar extension of $\bar\lambda_{\mathfrak m}$ along the residue embedding $k(\mathfrak m)\hookrightarrow k_L$ selected by the chosen prime. $\square$

The limitations are now exact. The lift may require both an unramified extension to realize the residue embedding and a ramified extension to contain characteristic-zero eigenvalues; it need not be $\mathcal O$-valued. A prescribed vector in the ordinary residual eigenspace need not be the reduction of an eigenvector on a chosen branch. Several primitive eigenvectors can reduce to the same line, and the full generalized residual summand can be larger than the reductions of any eigenbasis. Nonreduced special fiber records this merging, but finite flatness rules out a component supported only in the special fiber.

## 5. Localization and finite-level decomposition

### 5.1 Localizing the algebra and the module

A residual maximal ideal identifies one packet among all packets occurring at the chosen level. Localization discards every element on which some Hecke operator outside that maximal ideal acts invertibly.

Fix $\mathfrak m\subset\mathbb T$ with $\varpi\in\mathfrak m$. Define

$$
\mathbb T_{\mathfrak m}
=(\mathbb T\setminus\mathfrak m)^{-1}\mathbb T,
\qquad
M_{\mathfrak m}
=(\mathbb T\setminus\mathfrak m)^{-1}M.
$$

Then $\mathbb T_{\mathfrak m}$ is a finite local $\mathcal O$-algebra with maximal ideal $\mathfrak m\mathbb T_{\mathfrak m}$, and

$$
M_{\mathfrak m}\cong M\otimes_{\mathbb T}\mathbb T_{\mathfrak m}.
$$

Localization is exact. Thus a short exact sequence of Hecke-stable modules remains exact after localization. This formal fact is the principal reason to organize congruence classes by maximal ideals rather than by manually imposing infinitely many eigenvalue equations.

An element $x\in M$ maps to zero in $M_{\mathfrak m}$ exactly when some $s\notin\mathfrak m$ annihilates it. Since $M$ is finite, one may choose a single such $s$ for any finitely generated submodule supported away from $\mathfrak m$.

### 5.2 Support and faithfulness

For a finite module $N$ over a commutative ring $A$,

$$
\operatorname{Supp}_A(N)
=\{\mathfrak p:N_{\mathfrak p}\ne0\}
=V(\operatorname{Ann}_A(N)).
$$

Since $M$ is faithful over $\mathbb T$,

$$
\operatorname{Ann}_{\mathbb T}(M)=0,
\qquad
\operatorname{Supp}_{\mathbb T}(M)=\operatorname{Spec}\mathbb T.
$$

Therefore $M_{\mathfrak m}\ne0$ for every maximal ideal $\mathfrak m$ of the image algebra.

More is true.

**Proposition 5.1.** The localized module $M_{\mathfrak m}$ is faithful over $\mathbb T_{\mathfrak m}$.

**Proof strategy.** Annihilators commute with localization for finite modules.

**Proof.** If $a/s\in\mathbb T_{\mathfrak m}$ annihilates $M_{\mathfrak m}$, finite generation of $M$ gives $u\notin\mathfrak m$ with $uaM=0$. Faithfulness of $M$ gives $ua=0$, hence $a/s=0$ after localization. $\square$

The image convention is doing real work. For an abstract algebra $A^{\mathrm{abs}}$ acting through $A^{\mathrm{abs}}/I$, the support of $M$ is only $V(I)$. Localizations outside it vanish, and local faithfulness fails until one takes the image quotient.

Faithful does not mean free. The ideal $(x,y)$ is a faithful finite module over the local domain $k[x,y]_{(x,y)}$ but is not free. A Hecke module can similarly detect every element of its local algebra without being a rank-one copy of that algebra.

### 5.3 Idempotents and generalized residual summands

The algebra $\mathbb T/\varpi^n\mathbb T$ is Artinian for every $n\ge1$. Its maximal ideals are precisely the images of maximal ideals of $\mathbb T$ containing $\varpi$. The Chinese remainder theorem produces orthogonal idempotents

$$
1=\sum_{\mathfrak n\mid\varpi}e_{\mathfrak n,n}
\quad\text{in }\mathbb T/\varpi^n\mathbb T,
$$

and hence

$$
M/\varpi^nM
=\bigoplus_{\mathfrak n\mid\varpi}
e_{\mathfrak n,n}(M/\varpi^nM).
$$

The $\mathfrak m$-summand is canonically

$$
(M/\varpi^nM)_{\mathfrak m}
\cong M_{\mathfrak m}/\varpi^nM_{\mathfrak m}.
$$

At $n=1$ it is the generalized residual eigenspace:

$$
(M/\varpi M)_{\mathfrak m}
=\{x\in M/\varpi M:\mathfrak m^N x=0
\text{ for some }N\geq1\}.
$$

This need not equal the ordinary simultaneous eigenspace annihilated by $\mathfrak m$. The latter is the socle of the local Artinian action; the localized summand includes all nilpotent extensions of that residual character.

The idempotents at successive $n$ are compatible and lift uniquely through nilpotent ideals. Thus the finite-level decomposition is not a sequence of unrelated choices. It is the shadow of a product decomposition of the finite complete algebra itself.

One can see the decomposition through annihilating polynomials. Suppose a single $t\in\mathbb T$ has characteristic polynomial on $M$

$$
F(X)=F_1(X)F_2(X)
$$

with $F_1,F_2\in\mathcal O[X]$ whose reductions are coprime. Bézout gives $A(X)F_1(X)+B(X)F_2(X)=1$. The operators

$$
e_1=B(t)F_2(t),
\qquad
e_2=A(t)F_1(t)
$$

act as complementary idempotents after correcting them modulo the annihilating polynomial. They split the two residual clusters integrally. If the reductions of $F_1$ and $F_2$ share a root, no such Bézout identity exists modulo $\varpi$; the clusters meet at a common residual maximal ideal and localization deliberately keeps them together.

This calculation also shows why generalized rather than ordinary eigenspaces occur. Inside one factor $F_i$, repeated roots or several roots with the same residue cannot be separated by an idempotent integral at $\mathfrak m$. Their differences are nonunits, so the required projector has denominators.

### 5.4 Localization versus quotienting

Localization at $\mathfrak m$ keeps all infinitesimal neighborhoods and every generic branch passing through $\mathfrak m$. Quotienting by $\mathfrak m$ keeps only the residual character:

$$
\mathbb T_{\mathfrak m}\longrightarrow
k(\mathfrak m)=\mathbb T_{\mathfrak m}/\mathfrak m\mathbb T_{\mathfrak m}.
$$

These operations solve different problems. If two characteristic-zero branches cross at $\mathfrak m$, localization keeps both; reduction identifies their closed point. If the special fiber is nonreduced, localization keeps its nilpotent thickness; passage to the residue field erases it.

Nor is localization the same as an ordinary eigenspace. The module $M_{\mathfrak m}$ is the largest direct summand supported at $\mathfrak m$ in the finite coefficient direction. It can contain several characteristic-zero eigensystems and nontrivial generalized eigenspaces. This richness is precisely what a congruence argument needs.

## 6. Completion at a residual system

### 6.1 Two meanings of completion in practice

For a local ring $(A,\mathfrak n)$, its $\mathfrak n$-adic completion is

$$
\widehat A=\varprojlim_r A/\mathfrak n^r.
$$

Applied to $A=\mathbb T_{\mathfrak m}$, this gives

$$
\widehat{\mathbb T_{\mathfrak m}}
=\varprojlim_r
\mathbb T_{\mathfrak m}/(\mathfrak m\mathbb T_{\mathfrak m})^r.
$$

In the present finite-level setting, however, localization is already complete. Calling it “the completed local Hecke algebra” is correct but can conceal why. At varying or infinite levels one encounters a genuine inverse limit of distinct finite Hecke algebras, and completion then adds information. The two situations must be distinguished.

### 6.2 Finite local algebras over a complete DVR

**Theorem 6.1.** Let $A$ be a finite $\mathcal O$-algebra and let $\mathfrak n$ be a maximal ideal containing $\varpi$. Then $A_{\mathfrak n}$ is complete and separated for its maximal-ideal-adic topology.

**Proof strategy.** First use finiteness over the complete DVR to obtain $\varpi$-adic completeness. Then show that powers of $\varpi$ and powers of the maximal ideal are cofinal.

**Proof.** The finite $\mathcal O$-module $A_{\mathfrak n}$ is $\varpi$-adically complete. The quotient $A_{\mathfrak n}/\varpi A_{\mathfrak n}$ is Artinian local, so its maximal ideal is nilpotent. Hence for some $c$,

$$
(\mathfrak nA_{\mathfrak n})^c
\subseteq\varpi A_{\mathfrak n}.
$$

Conversely $\varpi\in\mathfrak nA_{\mathfrak n}$. Thus the $\varpi$-adic and maximal-ideal-adic topologies are equivalent. Completeness and separation transfer between cofinal filtrations. $\square$

Consequently we set

$$
\boxed{\mathbb T_{\mathfrak m}^{\wedge}
=\widehat{\mathbb T_{\mathfrak m}}
\cong\mathbb T_{\mathfrak m}.}
$$

Later we will abbreviate this ring to $\mathbb T_{\mathfrak m}$ while explicitly remembering that it carries its complete local topology. The completion symbol is valuable when matching conventions with genuinely completed objects, but it does not create a larger finite-level ring.

### 6.3 Genuine inverse-limit constructions

Suppose instead that one has compatible finite-level algebras $\mathbb T_r$ acting on modules $M_r$, with transition maps and increasing level, weight, or coefficient precision. A completed algebra might be

$$
\mathbb T_\infty=\varprojlim_r(\mathbb T_r)_{\mathfrak m_r}.
$$

This object need not be finite over $\mathcal O$ and need not equal the completion of any one $\mathbb T_r$. Noetherianity, surjectivity of transitions, and faithfulness on a limit module require proofs. One cannot import Theorem 6.1 merely because every finite stage is complete.

There is another genuine inverse limit already inside one local ring:

$$
\mathbb T_{\mathfrak m}
\cong\varprojlim_n
\mathbb T_{\mathfrak m}/\varpi^n\mathbb T_{\mathfrak m}.
$$

This limit reconstructs a ring known to be finite complete; it does not define a new infinite-level algebra. The distinction is between reconstruction from coefficient precision and construction from changing automorphic level.

### 6.4 Completed localized modules

Define

$$
\widehat M_{\mathfrak m}
=\varprojlim_r M_{\mathfrak m}/(\mathfrak m\mathbb T_{\mathfrak m})^rM_{\mathfrak m}.
$$

Since $M_{\mathfrak m}$ is finite over the complete Noetherian local ring $\mathbb T_{\mathfrak m}$,

$$
\widehat M_{\mathfrak m}\cong M_{\mathfrak m}.
$$

It is also complete for the $\varpi$-adic topology. The action

$$
\mathbb T_{\mathfrak m}\longrightarrow
\operatorname{End}_{\mathcal O}(M_{\mathfrak m})
$$

is continuous and faithful. Continuity is automatic from locality; faithfulness was proved before completion and is preserved because no ring or module changed.

The pair $(\mathbb T_{\mathfrak m},M_{\mathfrak m})$ is now a complete local algebra with a faithful finite module. It is not yet known that the module is free over the algebra, that the algebra is Gorenstein, or that a residual character lifts uniquely. Those are separate properties, not components of the definition.

The finite-level Artinian quotients have a concrete operator interpretation. Put

$$
A_n=\mathbb T_{\mathfrak m}/\mathfrak m^n,
\qquad
N_n=M_{\mathfrak m}/\mathfrak m^nM_{\mathfrak m}.
$$

Then $A_n$ is the algebra of Hecke operators remembered to $n$th-order residual precision, while $N_n$ is the corresponding generalized packet. The transition maps are surjective, and

$$
(\mathbb T_{\mathfrak m},M_{\mathfrak m})
\cong\varprojlim_n(A_n,N_n).
$$

At $n=1$, all elements of $\mathfrak m$ act by zero on the semisimple quotient $M_{\mathfrak m}/\mathfrak mM_{\mathfrak m}$, though not on the larger $M_{\mathfrak m}/\varpi M_{\mathfrak m}$. Higher $n$ retain successively deeper differences among congruent eigenpackets. This is exactly the two-scale passage from residual character to complete local neighborhood.

## 7. Congruences of characteristic-zero eigensystems

### 7.1 Congruence through a common residual maximal ideal

Let

$$
\lambda_i:\mathbb T\longrightarrow\mathcal O_i
\qquad(i=1,2)
$$

be characteristic-zero eigencharacters, where $\mathcal O_i$ are valuation rings of finite extensions of $E$. Choose a finite extension $L/E$ containing both value fields and embeddings $\mathcal O_i\hookrightarrow\mathcal O_L$ compatible with chosen places above $\varpi$. When the two characters have the same residual maximal ideal, choose the residue embeddings so that their induced copies of $k(\mathfrak m)$ in $k_L$ agree.

The characters are **congruent modulo the maximal ideal of $\mathcal O_L$** when

$$
\lambda_1(t)\equiv\lambda_2(t)\pmod{\mathfrak p_L}
\qquad(t\in\mathbb T).
$$

With this residue-embedding convention, equivalently,

$$
\lambda_1^{-1}(\mathfrak p_L)
=\lambda_2^{-1}(\mathfrak p_L)=\mathfrak m.
$$

Thus congruence means that the two generic points specialize to the same residual maximal ideal. This formulation is independent of a generating set. It also makes transitivity clear after all residue embeddings are placed in a common field.

It is enough to check equality on any algebra-generating family. It is not enough to check finitely many arbitrarily selected Hecke operators unless they are known to generate the image algebra. Agreement away from a larger bad set defines congruence for the correspondingly smaller Hecke algebra and may identify more packets.

### 7.2 Depth measured by valuations

Normalize the valuation $v_L$ by $v_L(\pi_L)=1$. The **congruence depth** of $\lambda_1$ and $\lambda_2$ relative to $L$ is

$$
c_L(\lambda_1,\lambda_2)
=\min_{t\in\mathbb T}v_L(\lambda_1(t)-\lambda_2(t)),
$$

with value $\infty$ if the characters are equal. Since $\mathbb T$ is finite over $\mathcal O$, the minimum may be taken over any finite $\mathcal O$-algebra generating set together with coefficients. Equivalently, define the difference ideal

$$
I(\lambda_1,\lambda_2)
=\bigl(\lambda_1(t)-\lambda_2(t):t\in\mathbb T\bigr)
\subseteq\mathcal O_L.
$$

Because $\mathcal O_L$ is a DVR,

$$
I(\lambda_1,\lambda_2)=(\pi_L^{c_L})
$$

for distinct characters. They are congruent modulo $\pi_L^n$ exactly when $c_L\ge n$.

The integer depends on normalization and ramification. If $L'/L$ has ramification index $e$, then

$$
c_{L'}(\lambda_1,\lambda_2)=e\,c_L(\lambda_1,\lambda_2).
$$

The invariant statement is therefore the ideal $I(\lambda_1,\lambda_2)$ or, after normalizing valuations by $v(\varpi)=1$, a rational coefficient-prime valuation. Raw integers from different coefficient fields should not be compared without this adjustment.

### 7.3 Basis-independent congruence ideals

After base-changing the algebra to $\mathcal O_L$, the map

$$
(\lambda_1,\lambda_2):\mathbb T\otimes_{\mathcal O}\mathcal O_L
\longrightarrow\mathcal O_L\times\mathcal O_L
$$

has image $A_{12}$. The failure of $A_{12}$ to equal the product is the congruence between the two branches. The exact sequence

$$
0\longrightarrow A_{12}
\longrightarrow\mathcal O_L\times\mathcal O_L
\xrightarrow{(a,b)\mapsto a-b\bmod I}
\mathcal O_L/I(\lambda_1,\lambda_2)
\longrightarrow0
$$

shows that

$$
A_{12}
=\{(a,b):a\equiv b\pmod{I(\lambda_1,\lambda_2)}\}.
$$

This description depends only on the two algebra maps. It is unchanged by changing a basis of $M$, replacing eigenvectors, or choosing a different finite generating set for $\mathbb T$.

**Worked example.** Let

$$
A=\mathcal O[X]/((X-a)(X-b))
$$

with $a\ne b\in\mathcal O$. Evaluation gives two characters. The image of $A$ in $\mathcal O\times\mathcal O$ is

$$
\{(u,v):u\equiv v\pmod{a-b}\}.
$$

Their congruence ideal is $(a-b)$. If $v(a-b)=n$, the two characters agree modulo $\varpi^n$ but not modulo $\varpi^{n+1}$.

### 7.4 Eigencharacters without congruent eigenvectors

Congruence of eigencharacters does not canonically produce congruent eigenvectors. Even when two eigenspaces are lines, their integral lattices have no preferred generators. Rescaling one primitive vector by a unit changes its reduction, and the two lines may occupy different positions inside $M$.

Consider $M=\mathcal O^2$ and

$$
T=
\begin{pmatrix}a&1\\0&b\end{pmatrix},
\qquad a-b\in\varpi\mathcal O.
$$

The two generic eigencharacters are $a$ and $b$. An eigenvector for $a$ is $(1,0)$, while an eigenvector for $b$ can be $(1,b-a)$. Both reduce to the same line modulo $\varpi$, but if the off-diagonal entry or lattice is changed, the primitive reductions can behave differently even though the two character values have the same congruence ideal.

The robust object is the localized module $M_{\mathfrak m}$ together with its algebra action. Statements about congruent normalized eigenforms require an independent normalization functional or a chosen perfect pairing. This finite quaternionic setting has no distinguished first expansion coefficient, so characters are the primary definition.

There is nevertheless a useful criterion when a normalization functional is available. Let $\ell:M\to\mathcal O$ be linear and suppose each relevant eigenline contains a unique vector $f_\lambda$ with $\ell(f_\lambda)=1$. This requires $\ell$ to be a unit on the primitive eigenline. If $M$ is generated by the Hecke orbit of a vector dual to $\ell$, then congruence of characters modulo $\pi_L^n$ forces

$$
\ell(t f_{\lambda_1})
\equiv
\ell(t f_{\lambda_2})
\pmod{\pi_L^n}
$$

for every $t$. Recovering congruence of the vectors themselves requires these Hecke translates to separate vectors integrally. This is an additional cyclicity or perfect-duality hypothesis. The argument explains why normalized eigenforms can be compared coefficientwise in settings with a distinguished coefficient functional, and why no such conclusion is automatic here.

The valuation definition is also stable under changing Hecke coordinates. Suppose $u_1,\ldots,u_s$ is another generating family and every $t_i$ is an integral polynomial in the $u_j$, while every $u_j$ is an integral polynomial in the $t_i$. If the two characters agree on all $u_j$ modulo $\pi_L^n$, polynomial substitution shows that they agree on every $t_i$, and conversely. No condition number or change-of-basis determinant enters: the comparison occurs in the algebra, not in a vector-space basis.

## 8. Normalization and branches

### 8.1 Generic packets and integral branches

Assume for this chapter that $\mathbb T_E$ is reduced. Then

$$
\mathbb T_E\cong\prod_{i=1}^s E_i
$$

for finite field extensions $E_i/E$. Each factor is a characteristic-zero branch, or conjugacy class of eigenpackets. A residual maximal ideal can lie below several factors: those packets are congruent.

Reducedness of the generic fiber is not automatic. It follows, for instance, if after an embedding into $\mathbf C$ the algebra is generated by commuting normal operators on a positive-definite space. In a merely bilinear or integral pairing, self-adjointness need not imply diagonalizability. We will state reducedness whenever branches are interpreted as fields.

### 8.2 Normalization of a finite Hecke algebra

Let $\widetilde{\mathbb T}$ be the integral closure of $\mathbb T$ in $\mathbb T_E$. Since $\mathcal O$ is excellent and $\mathbb T$ is finite, $\widetilde{\mathbb T}$ is finite over $\mathbb T$. Under the product decomposition,

$$
\widetilde{\mathbb T}
=\prod_{i=1}^s\mathcal O_i,
$$

where $\mathcal O_i$ is the integral closure of $\mathcal O$ in $E_i$.

The inclusion

$$
\mathbb T\hookrightarrow\widetilde{\mathbb T}
$$

separates branches integrally. Its cokernel is a finite torsion $\mathcal O$-module, killed by the conductor

$$
\mathfrak f
=\{x\in\widetilde{\mathbb T}:x\widetilde{\mathbb T}\subseteq\mathbb T\}.
$$

Away from primes dividing this conductor, the branches split. At primes dividing it, elements on different branches must satisfy congruence conditions.

Normalization does not manufacture new eigenpackets: it separates the generic factors already present. It can enlarge the integral algebra because coordinates that are integral on each branch need not be expressible by one polynomial in the original Hecke operators with integral coefficients.

### 8.3 Crossings in the special fiber

The basic crossing is

$$
A_n=\{(x,y)\in\mathcal O\times\mathcal O:
x\equiv y\pmod{\varpi^n}\}.
$$

It is finite free of rank two, its normalization is $\mathcal O\times\mathcal O$, and its two generic branches are distinct. Modulo $\varpi$, however,

$$
A_n/\varpi A_n
$$

has only one maximal ideal when $n\ge1$. Both branches specialize to the same residual system.

For $n=1$, set $\epsilon=(0,\varpi)$ inside $A_1$. Then $\epsilon^2=\varpi\epsilon$, so

$$
A_1\cong\mathcal O[\epsilon]/(\epsilon^2-\varpi\epsilon).
$$

The generic roots $0$ and $\varpi$ are distinct, while the special fiber is

$$
k[\epsilon]/(\epsilon^2).
$$

Thus a reduced generic fiber can have a nonreduced special fiber. The nilpotent is the infinitesimal memory of two branches colliding.

### 8.4 Nilpotents and what they record

There are two sources of nilpotents and they should not be confused.

First, $\mathbb T_E$ itself may be nonreduced, reflecting a genuinely nonsemisimple characteristic-zero action. Its nilpotents persist after inverting $\varpi$.

Second, $\mathbb T_E$ may be reduced while $\mathbb T/\varpi\mathbb T$ is nonreduced because distinct integral branches meet. Such nilpotents disappear after inverting $\varpi$.

The special-fiber nilradical does not by itself count branches. The ring $k[x]/(x^3)$ has one minimal prime and higher infinitesimal thickness; the crossing above has two generic branches but one residual point. Normalization of the generic fiber, the conductor, and the local algebra together distinguish these situations.

Nor should one replace the special fiber by its reduction too early. Passing from $k[\epsilon]/(\epsilon^2)$ to $k$ preserves the unique residual character but erases the first-order congruence. Congruence modules and deformation comparisons are sensitive to precisely this thickness.

The conductor can be calculated directly in the two-branch model. For

$$
A_n=\{(x,y):x\equiv y\pmod{\varpi^n}\}
\subseteq\widetilde A=\mathcal O\times\mathcal O,
$$

one has

$$
\mathfrak f
=\varpi^n\mathcal O\times\varpi^n\mathcal O.
$$

Indeed, multiplying $(a,b)$ by both $(1,0)$ and $(0,1)$ must produce pairs lying in $A_n$, forcing $a,b\in\varpi^n\mathcal O$; that condition is also sufficient. The normalization quotient is

$$
\widetilde A/A_n\cong\mathcal O/(\varpi^n),
$$

so its length is the congruence depth of the two characters. For more than two branches or with multiplicity, the conductor need not be principal and its colength combines several intersections. The elementary calculation remains the local model behind the terminology.

One can also have branches that are distinct over $E$ but conjugate over the original coefficient field. If $\mathbb T_E$ contains a field factor $E_i/E$, normalization contributes its integer ring $\mathcal O_i$, not a product of copies of $\mathcal O$. Only after passing to a splitting extension does that field factor separate into embedding-indexed packets. Congruence between conjugate embeddings then depends on the selected primes above $\varpi$. “Branch” therefore refers first to a factor of the reduced generic algebra over the stated coefficient field.

### 8.5 Exact criteria for reducedness

Reducedness enters twice: it decides whether generic packets really are branches, and it decides whether nilpotents in the integral algebra carry information already present in characteristic zero. The coefficient-flatness established in Chapter 2 makes the first decision unusually clean.

**Proposition 8.1 (generic detection of nilpotents).** Let $A$ be a finite torsion-free algebra over the DVR $\mathcal O$. Then

$$
A\text{ is reduced}
\quad\Longleftrightarrow\quad
A_E=A\otimes_{\mathcal O}E\text{ is reduced}.
$$

**Proof strategy.** Localization preserves reducedness in one direction. In the other, a nilpotent that vanishes after inverting $\varpi$ is coefficient torsion, which torsion-freeness excludes.

**Proof.** If $A$ is reduced, every localization of $A$ is reduced, so $A_E$ is reduced. Conversely, let $a\in A$ be nilpotent. Its image in the reduced algebra $A_E$ is zero. Hence $\varpi^na=0$ for some $n$. Torsion-freeness gives $a=0$. $\square$

Thus generic reducedness is enough for the integral Hecke algebra. It is not enough for the special fiber: the crossing algebra of Section 8.3 is reduced and finite flat, but its special fiber contains a nonzero nilpotent.

There is a useful criterion in the opposite direction.

**Proposition 8.2 (reduced special fiber).** Let $A$ be a finite flat algebra over the complete DVR $\mathcal O$. If $A/\varpi A$ is reduced, then $A$ and $A_E$ are reduced.

**Proof strategy.** A nilpotent reduces to zero, hence is divisible by $\varpi$. Dividing and repeating places it in every coefficient power; completeness and separation then force it to vanish.

**Proof.** If $a^N=0$, the image of $a$ in the reduced special fiber is zero, so $a=\varpi a_1$. Flatness gives $a_1^N=0$: from $\varpi^Na_1^N=0$ and absence of coefficient torsion, one gets $a_1^N=0$. Repeating shows $a\in\varpi^rA$ for every $r$. A finite module over the complete DVR is separated, so $\bigcap_r\varpi^rA=0$. Hence $a=0$. Proposition 8.1 then gives reducedness of $A_E$. $\square$

The converse fails, again by the crossing algebra. Reduced special fiber is therefore a strong transversality condition: it says that generic branches neither carry nilpotents nor collide infinitesimally modulo $\varpi$.

For the acting algebra, generic reducedness often comes from adjoints.

**Normal-operator criterion.** Suppose there is a field extension $L/E$ and a positive-definite Hermitian form on $M_L$ such that every generator of $\mathbb T_L$ is normal and the generators commute. Then $\mathbb T_L$, hence $\mathbb T_E$, is reduced.

Indeed commuting normal operators are simultaneously diagonalizable. The image algebra embeds into a finite product of copies of $L$ by recording their joint eigenvalues, and a subalgebra of a reduced product has no nonzero nilpotent. The positivity and normality hypotheses are essential. Commuting operators preserving a nondegenerate bilinear form can still have Jordan blocks, and a self-adjoint operator for an indefinite form need not be diagonalizable.

A second test uses the trace form. Assume $A_E$ is a finite-dimensional commutative algebra over $E$, and define

$$
(x,y)_{\mathrm{tr}}
=\operatorname{Tr}_{A_E/E}(xy).
$$

If $E$ is perfect, this form is nondegenerate exactly when $A_E$ is reduced. More generally, nondegeneracy is equivalent to $A_E$ being a product of finite separable field extensions of $E$. To see the obstruction, a nilpotent ideal acts by nilpotent multiplication and lies in the radical of the trace form. Conversely a product of separable fields has nondegenerate field-trace pairing. Over an imperfect field a reduced inseparable field extension can have degenerate trace form, so perfectness or separability cannot be omitted.

Choose an $\mathcal O$-basis of the finite free algebra $A$. The determinant of its integral trace matrix is nonzero precisely when the generic trace form is nondegenerate. Its valuation measures failure of that particular integral pairing to be perfect; it does not by itself measure the Gorenstein defect, because a different generator of the dual module may give a perfect $A$-duality. Reducedness, trace self-duality, and Gorenstein duality are three distinct assertions.

## 9. Pairings, adjoints, and dual Hecke modules

### 9.1 The pairing problem

A pairing converts geometric reversal of correspondences into algebraic adjoints. It can also relate a Hecke algebra to its linear dual. These are powerful conclusions, but they require more than the existence of a finite-sum formula.

Let $M$ and $M'$ be finite free $\mathcal O$-modules with a perfect bilinear pairing

$$
\langle\ ,\ \rangle:M\times M'\longrightarrow\mathcal O.
$$

Perfect means that the induced maps

$$
M\xrightarrow{\sim}(M')^\vee,
\qquad
M'\xrightarrow{\sim}M^\vee
$$

are isomorphisms. In the automorphic construction, $M'$ normally uses the dual weight and inverse central character. A self-pairing $M=M'$ requires an actual identification of those data.

The mass pairing gives the clean inverse-correspondence adjoint after stabilizer denominators are units. The unweighted integral pairing may be perfect in situations where the mass pairing is not integral, but its adjoint can contain stabilizer matrices or level-volume factors. We therefore assume a specified integral perfect pairing and record its exact adjoint normalization rather than calling every standard operator self-adjoint.

For $t\in\operatorname{End}_{\mathcal O}(M)$, an adjoint $t^*\in\operatorname{End}_{\mathcal O}(M')$ satisfies

$$
\langle tx,y\rangle=\langle x,t^*y\rangle.
$$

Perfectness makes $t^*$ unique. For an unnormalized double coset it is the inverse double coset under compatible mass conventions. At a spherical place it can be $S_v^{-1}T_v$ rather than $T_v$; at oriented level $U_v^*=V_v$ is generally a different operator.

### 9.2 Adjoint-stable Hecke algebras

Let $\mathbb T\subseteq\operatorname{End}_{\mathcal O}(M)$ and $\mathbb T'\subseteq\operatorname{End}_{\mathcal O}(M')$ be the image algebras generated by paired operator families. Suppose the adjoint of every generator of $\mathbb T$ lies in $\mathbb T'$, and conversely. Then adjunction gives an anti-isomorphism

$$
\mathbb T\xrightarrow{\sim}\mathbb T'.
$$

Because the rings are commutative, it is an ordinary isomorphism after remembering the reversal of products.

If $M=M'$ and the generating algebra is stable under $*$, maximal ideals are carried to maximal ideals. A residual ideal $\mathfrak m$ may or may not be fixed by this involution. For inverse central characters, localization pairs the $\mathfrak m$-part of $M$ with the $\mathfrak m^*$-part of $M'$.

**Proposition 9.1.** If the global pairing is perfect and $*$ identifies $\mathfrak m$ with $\mathfrak m'$, then it restricts to a perfect pairing

$$
M_{\mathfrak m}\times M'_{\mathfrak m'}\longrightarrow\mathcal O.
$$

**Proof strategy.** Use the product idempotents of the finite algebra. Adjunction carries the idempotent for $\mathfrak m$ to the idempotent for $\mathfrak m'$, so all other local blocks are orthogonal.

**Proof.** Because $\mathcal O$ is complete and $\mathbb T$ is finite, the compatible idempotents in the quotients $\mathbb T/\varpi^n\mathbb T$ lift to a product decomposition of $\mathbb T$ into its local factors. Let $e_{\mathfrak m}$ be the idempotent projecting onto the $\mathfrak m$-factor. Adjunction sends it to $e_{\mathfrak m'}$. If $\mathfrak n'\ne\mathfrak m'$, then for $x\in e_{\mathfrak m}M$ and $y\in e_{\mathfrak n'}M'$,

$$
\langle x,y\rangle
=\langle e_{\mathfrak m}x,y\rangle
=\langle x,e_{\mathfrak m'}y\rangle
=0.
$$

Thus the isomorphism $M\simeq(M')^\vee$ supplied by the perfect pairing is block diagonal for the two product decompositions. Each diagonal block is therefore an isomorphism, which is exactly perfectness on $M_{\mathfrak m}\times M'_{\mathfrak m'}$. $\square$

### 9.3 Dual modules and self-duality

The $\mathcal O$-dual

$$
M^\vee=\operatorname{Hom}_{\mathcal O}(M,\mathcal O)
$$

becomes a $\mathbb T$-module by

$$
(t\cdot\phi)(x)=\phi(tx).
$$

The adjoint-compatible pairing identifies $M'$ with $M^\vee$ when $M'$ is regarded as a $\mathbb T$-module by transporting the action through $t\mapsto t^*$. Indeed, the functional attached to $y\in M'$ is $x\mapsto\langle x,y\rangle$, and

$$
\langle tx,y\rangle=\langle x,t^*y\rangle
$$

is exactly equivariance for these actions. A self-pairing gives an isomorphism $M\simeq M^\vee$ for the ordinary $\mathbb T$-action only when the transported action on the second copy agrees with the stated action on $M$; this holds, for example, when the chosen Hecke generators are self-adjoint. More generally, ordinary $\mathbb T$-equivariant self-duality must be included as a separate hypothesis. This is **self-duality of the module**. It does not imply that the ring is self-dual as a module over itself.

The ring dual is

$$
\mathbb T^\vee=\operatorname{Hom}_{\mathcal O}(\mathbb T,\mathcal O),
$$

with $(a\phi)(b)=\phi(ab)$. A finite flat local $\mathcal O$-algebra is Gorenstein in the relative zero-dimensional sense when $\mathbb T^\vee$ is free of rank one as a $\mathbb T$-module. This is a property of the algebra, not a synonym for perfectness of $M$.

There is a natural way a module functional can connect the two. Given $x\in M$ and $\ell\in M^\vee$, define

$$
\Phi_{x,\ell}:\mathbb T\longrightarrow\mathcal O,
\qquad t\longmapsto\ell(tx).
$$

If $M$ is free of rank one over $\mathbb T$ with generator $x$, and if $M\cong M^\vee$ as $\mathbb T$-modules, then evaluating the corresponding dual generator on $tx$ identifies $\mathbb T^\vee$ with $\mathbb T$. The rank-one hypothesis is decisive.

### 9.4 When Gorenstein-like duality follows

**Theorem 9.2.** Let $(\mathbb T,\mathfrak m)$ be finite flat local over $\mathcal O$. Suppose:

1. $M$ is free of rank one over $\mathbb T$;
2. $M$ has a perfect $\mathbb T$-equivariant self-duality $M\cong M^\vee$.

Then $\mathbb T^\vee\cong\mathbb T$ as $\mathbb T$-modules.

**Proof.** Choose a $\mathbb T$-basis $x$ of $M$. Then $M\cong\mathbb T$ by $t\mapsto tx$. Dualizing over $\mathcal O$ gives $M^\vee\cong\mathbb T^\vee$. The assumed self-duality and the first identification yield

$$
\mathbb T\cong M\cong M^\vee\cong\mathbb T^\vee.
$$

All maps are $\mathbb T$-linear by hypothesis. $\square$

The theorem is a criterion, not a default. Perfect automorphic pairing alone does not give (1). Multiplicity one on the generic fiber alone does not give integral rank-one freeness. A finite flat local algebra can fail to be Gorenstein, and its faithful self-dual module can have higher rank.

**Counterexample.** Let

$$
A=k[x,y]/(x,y)^2.
$$

Its socle is the two-dimensional space $(x,y)$, so $A$ is not Gorenstein. The regular module is faithful and free of rank one over $A$, but its $k$-dual is not isomorphic to $A$ as an $A$-module. Thus faithfulness and rank one do not replace self-duality.

The trace pairing gives another useful diagnostic. For a finite flat $\mathcal O$-algebra $A$ with generically separable fiber, define

$$
(a,b)_{\mathrm{tr}}
=\operatorname{Tr}_{A_E/E}(ab).
$$

It is nondegenerate over $E$, and its integral dual lattice is

$$
A^{\sharp}
=\{x\in A_E:\operatorname{Tr}(xA)\subseteq\mathcal O\}.
$$

The trace pairing is perfect on $A$ exactly when $A=A^{\sharp}$. This is stronger than relative Gorenstein duality: Gorenstein requires $A^{\sharp}$ to be a principal fractional $A$-ideal, not necessarily equal to $A$ under the trace functional. A different generator of $A^\vee$ can produce the self-duality. Thus failure of the raw trace discriminant to be a unit does not by itself prove non-Gorensteinness.

In the crossing algebra $A_1$, the normalization has a perfect coordinatewise trace pairing, while the restricted trace discriminant is divisible by a power of $\varpi$. This divisibility reflects branch collision. Whether $A_1$ is Gorenstein is decided by the principality of its dual, not by the unit status of that particular discriminant. Indeed $A_1\cong\mathcal O[\epsilon]/(\epsilon^2-\varpi\epsilon)$ is a hypersurface and is Gorenstein, despite its nonreduced special fiber.

## 10. Old submodules at a new prime

### 10.1 Degeneracy maps and the old image

Let $U$ be a level and let $U'$ introduce one new $K_0(\mathfrak q)$ condition at a prime $\mathfrak q$ not previously in the level. Keep the same coefficient and central data. Write

$$
M=M(U),\qquad N=M(U').
$$

There are two standard degeneracy maps

$$
\delta_0,\delta_1:M\longrightarrow N,
$$

one from pullback and one from a translated pullback. Their exact diagonal representatives depend on the established right-translation convention; their defining property is the required subgroup inclusion.

Package them as

$$
\delta:M\oplus M\longrightarrow N,
\qquad(x,y)\longmapsto\delta_0x+\delta_1y.
$$

The **old submodule from level $U$** is

$$
N^{\mathrm{old}}=\operatorname{im}(\delta).
$$

This definition is integral and canonical once the degeneracy maps are fixed. It does not say that $\delta$ is injective, that its image is saturated, or that it is a direct summand.

If several lower levels contribute, one sums their degeneracy images. The phrase “the old space” must then specify which lower levels and which degeneracy family are included.

### 10.2 Hecke stability and the changed prime

Every away-from-$\Sigma\cup\{\mathfrak q\}$ Hecke operator commutes with both degeneracy maps. Hence $N^{\mathrm{old}}$ is stable under the common away-from-$\mathfrak q$ Hecke algebra.

At $\mathfrak q$, stability is a separate local calculation. The $U_{\mathfrak q}$ operator generally acts on the ordered pair of degeneracy images through a $2\times2$ matrix with entries involving the lower-level $T_{\mathfrak q}$, $S_{\mathfrak q}$, and powers of $q_{\mathfrak q}$ determined by normalization. It is unsafe to quote a matrix without deriving it from the chosen $\delta_i$ and the unnormalized double cosets.

For the congruence theory away from the changed prime, no such formula is needed. We use the common abstract algebra

$$
\mathbb T^{(\mathfrak q),\mathrm{abs}}
=\mathcal O[T_v,S_v^{\pm1}:v\notin\Sigma\cup\{\mathfrak q\}]
$$

and its possibly different images on $M$ and $N$. The degeneracy map is linear for the common abstract algebra.

### 10.3 Adjoint trace maps and the Gram operator

Assume perfect pairings on $M$ and $N$ with compatible level normalizations. Let

$$
\delta_i^*:N\longrightarrow M
$$

be the adjoint of $\delta_i$. It is an inverse translation followed by a trace, possibly multiplied by the explicitly chosen level-volume factor. Define

$$
\delta^*:N\longrightarrow M\oplus M,
\qquad z\longmapsto(\delta_0^*z,\delta_1^*z).
$$

The composite

$$
G=\delta^*\delta\in\operatorname{End}_{\mathcal O}(M\oplus M)
$$

is the **degeneracy Gram operator**:

$$
G=
\begin{pmatrix}
\delta_0^*\delta_0&\delta_0^*\delta_1\\
\delta_1^*\delta_0&\delta_1^*\delta_1
\end{pmatrix}.
$$

Each entry is an explicit lower-level correspondence. The diagonal terms often contain a level index, while the off-diagonal terms contain $T_{\mathfrak q}$ or its adjoint normalization. The abstract matrix is safer and more general than a memorized numerical version.

For the standard one-prime convention fixed in the preceding volume, the calculation is exact. Put $q=q_{\mathfrak q}$, let $T=T_{\mathfrak q}$ and $S=S_{\mathfrak q}$ at the lower hyperspecial level, and take the two degeneracy maps defined by $1$ and $\operatorname{diag}(1,\pi_{\mathfrak q})$. Assume, exactly as in that calculation, that the coefficient ring has the needed involution, the weight lattice has a perfect invariant Hermitian pairing, and the central character is unitary. These hypotheses identify the dual coefficient systems, so the separately normalized perfect mass pairings make all four entries endomorphisms of the same lower-level module. Then

$$
\boxed{
G=
\begin{pmatrix}
q+1&T\\
S^{-1}T&q+1
\end{pmatrix}.}
$$

The upper-left and lower-right entries are the degree $q+1$ of the level covering. The upper-right composition is the spherical correspondence $T$, and adjunction gives the lower-left entry $T^*=S^{-1}T$. Since $S$ is a central unit and commutes with $T$, the determinant is

$$
\boxed{D_{\mathfrak q}=(q+1)^2-S^{-1}T^2.}
$$

This formula belongs to this convention. If the second degeneracy element, the forward level operator, the pairing measure, or the central normalization changes, the displayed matrix must be recomputed. The invariant construction is always $G=\delta^*\delta$.

If $G$ becomes invertible after localization at $\mathfrak m$, then $\delta_{\mathfrak m}$ is split injective with retraction

$$
G^{-1}\delta^*.
$$

Indeed $(G^{-1}\delta^*)\delta=1$. This is a formal linear-algebra criterion. Proving invertibility can require arithmetic information about residual eigenvalues.

In the standard convention, $G_{\mathfrak m}$ is invertible exactly when $D_{\mathfrak q}\notin\mathfrak m$. One direction follows from the adjugate formula. For the other, the determinant of an invertible matrix is a unit. Hence a residual old--new congruence can occur only on the locus

$$
(q+1)^2\equiv S^{-1}T^2\pmod{\mathfrak m}.
$$

After evaluating a lower-level eigencharacter with $T\mapsto t$ and $S\mapsto s$, this becomes $(q+1)^2\equiv s^{-1}t^2$. It is a necessary degeneracy condition for the chosen one-prime old lattice. It is not, by itself, an existence theorem for a new characteristic-zero packet.

Suppose for illustration that, under a chosen normalization, the localized Gram operator acts on a simultaneous lower-level eigenspace through a scalar matrix

$$
G_\lambda=
\begin{pmatrix}d&a_\lambda\\a_\lambda^*&d'
\end{pmatrix}.
$$

Then

$$
\det G_\lambda=dd'-a_\lambda a_\lambda^*.
$$

If this determinant is a unit, the two degeneracy vectors form an integrally split old plane. If it is nonzero but divisible by $\varpi$, they remain independent generically but their span can meet the new lattice modulo $\varpi$. If it is zero generically, the degeneracy maps are already dependent on that characteristic-zero eigensystem. The entries $d,d',a_\lambda$ depend on level-volume and adjoint conventions; the trichotomy by determinant does not.

### 10.4 Old submodule and old quotient conventions

Two constructions are both called old in the literature:

$$
N^{\mathrm{old}}_{\mathrm{sub}}=\operatorname{im}(\delta)
\subseteq N,
$$

and

$$
N^{\mathrm{old}}_{\mathrm{quot}}
=(M\oplus M)/\ker(\delta).
$$

They are canonically isomorphic as abstract $\mathcal O$-modules by the first isomorphism theorem. The distinction matters because the first carries an embedded lattice in $N$, while the second remembers its presentation from lower level. Pairings, saturation, and reduction refer to the embedded lattice; kernel calculations refer naturally to the quotient presentation.

A third object is the saturated old lattice

$$
N^{\mathrm{old,sat}}
=N\cap(N^{\mathrm{old}}\otimes_{\mathcal O}E)
\subseteq N_E.
$$

It contains $N^{\mathrm{old}}$ with finite torsion quotient. Replacing old by saturated old can improve torsion-freeness of the quotient $N/N^{\mathrm{old,sat}}$, but it changes the integral degeneracy image and can erase the congruence module measuring the failure of saturation.

## 11. New modules and integral orthogonality

### 11.1 Kernel-of-adjoints definition

The old image records vectors coming from lower level. A vector should be new relative to that level when every trace back to lower level vanishes. This motivates the integral definition

$$
\boxed{
N^{\mathrm{new}}_{\ker}
=\ker(\delta^*)
=\ker(\delta_0^*)\cap\ker(\delta_1^*).}
$$

It is stable under the common away-from-$\mathfrak q$ Hecke algebra because the trace maps intertwine those operators with their adjoints. Stability under operators at $\mathfrak q$ again requires the appropriate local relations.

The kernel definition does not require $\delta$ to be injective. It does require the adjoints to have been defined with a stated pairing and normalization. Multiplying an adjoint by a nonzerodivisor does not change its generic kernel but can change its integral kernel if the target has torsion; our finite free targets avoid that particular ambiguity.

### 11.2 Orthogonal complements under perfectness

If the pairing on $N$ is perfect and $\delta^*$ is genuinely adjoint to $\delta$, then

$$
\ker(\delta^*)=(\operatorname{im}\delta)^\perp.
$$

**Proof.** A vector $z\in N$ lies in $(\operatorname{im}\delta)^\perp$ exactly when

$$
0=\langle\delta(x,y),z\rangle
=\langle(x,y),\delta^*z\rangle
$$

for every $(x,y)\in M\oplus M$. Perfectness on $M\oplus M$ makes this equivalent to $\delta^*z=0$. $\square$

Without perfectness, orthogonality only says that $\delta^*z$ lies in the radical of the lower-level pairing. Thus the kernel and orthogonal-complement definitions can differ. At stabilizer primes where the mass form has denominators or the invariant pairing degenerates, one must use the integral map actually available.

### 11.3 Saturation and torsion caveats

Because the target $N$ of $\delta$ is torsion-free, $\ker(\delta)$ is saturated in $M\oplus M$. Because the target $M\oplus M$ of $\delta^*$ is torsion-free, $N^{\mathrm{new}}_{\ker}$ is saturated in $N$. Indeed, if $\varpi x$ lies in either kernel, then $\varpi$ times the image of $x$ is zero in a torsion-free target, so the image of $x$ is already zero.

The old image need not be saturated. The elementary map

$$
\mathcal O\longrightarrow\mathcal O,
\qquad x\longmapsto\varpi x
$$

has image $\varpi\mathcal O$, whose quotient is $k$. Its generic image is the whole line, so the saturated image is $\mathcal O$. This is exactly the shape of an integral congruence: generically the contribution fills a direct summand, but integrally it sits with finite index.

Even when both old and new submodules are saturated, their sum need not be all of $N$. The quotient

$$
N/(N^{\mathrm{old}}+N^{\mathrm{new}})
$$

is a finite torsion module when the generic fiber decomposes. It measures failure of integral splitting.

### 11.4 When old plus new is a decomposition

Assume $\delta$ is injective and the Gram operator $G=\delta^*\delta$ is invertible. Define

$$
e_{\mathrm{old}}=\delta G^{-1}\delta^*
\in\operatorname{End}_{\mathcal O}(N).
$$

Then $e_{\mathrm{old}}^2=e_{\mathrm{old}}$, its image is $N^{\mathrm{old}}$, and its kernel is $N^{\mathrm{new}}_{\ker}$. Therefore

$$
N=N^{\mathrm{old}}\oplus N^{\mathrm{new}}_{\ker}.
$$

This proof exposes the exact obstruction: the inverse of the Gram operator must be integral. If $G$ is invertible only over $E$, the decomposition holds generically, while denominators in $G^{-1}$ measure an integral congruence between old and new lattices.

Thus an orthogonal decomposition is a theorem under perfect-pairing, injectivity, and unit-determinant hypotheses. It is not part of the definitions of oldness or newness.

There is a dual exact sequence that clarifies the quotient convention. Assume $\delta$ is injective and all pairings are perfect. Dualizing

$$
0\longrightarrow M^{\oplus2}
\xrightarrow{\delta}N
\longrightarrow Q\longrightarrow0
$$

over $\mathcal O$ gives

$$
0\longrightarrow Q^\vee
\longrightarrow N
\xrightarrow{\delta^*}M^{\oplus2}
\longrightarrow\operatorname{Ext}^1_{\mathcal O}(Q,\mathcal O)
\longrightarrow0.
$$

Here we used the pairings to identify the duals of $M$ and $N$ with themselves. The new kernel is $Q^\vee$. If $Q$ is torsion-free, it is free and the Ext term vanishes, so $\delta^*$ is surjective. If $Q$ has torsion, the Ext term records precisely the failure of the adjoint traces to be onto. Thus torsion in the old quotient obstructs the clean dual old/new picture.

## 12. Control under change of level

### 12.1 Comparison maps after localization

Let $\mathbb T_U$ and $\mathbb T_{U'}$ be the image algebras of the common away-from-$\mathfrak q$ operator family on $M$ and $N$. The abstract common algebra maps onto both. A residual eigensystem is first an ideal $\mathfrak m^{\mathrm{abs}}$ of that abstract algebra occurring in one or both modules; its images give maximal ideals $\mathfrak m_U$ and $\mathfrak m_{U'}$ when they occur.

After localizing, the degeneracy map becomes

$$
\delta_{\mathfrak m}:
M_{\mathfrak m_U}^{\oplus2}
\longrightarrow N_{\mathfrak m_{U'}}.
$$

Its image is the localized old submodule. Exactness of localization gives

$$
(\ker\delta)_{\mathfrak m}
=\ker(\delta_{\mathfrak m}),
\qquad
(\operatorname{coker}\delta)_{\mathfrak m}
=\operatorname{coker}(\delta_{\mathfrak m}).
$$

This is formal control: localization neither creates nor hides kernels supported at the chosen maximal ideal. It can annihilate kernels supported only at other systems.

### 12.2 Formal injectivity and surjectivity criteria

Several useful criteria require no deep automorphic input.

**Injectivity from a left inverse.** If $G_{\mathfrak m}=\delta^*\delta$ is invertible, then $\delta_{\mathfrak m}$ is split injective.

**Surjectivity from residue level.** If $N_{\mathfrak m}$ is finite over the local ring $\mathbb T_{U',\mathfrak m}$ and the reduction of $\delta_{\mathfrak m}$ modulo its maximal ideal is surjective, then $\delta_{\mathfrak m}$ is surjective by Nakayama.

**Injectivity from torsion-free cokernel and generic injectivity.** Let $f:P\to Q$ be a map of finite free $\mathcal O$-modules. Generic injectivity implies $\ker f$ is torsion, hence zero. No cokernel hypothesis is needed in this DVR setting. By contrast, generic surjectivity gives only a torsion cokernel; it does not give integral surjectivity.

**Isomorphism from determinant.** If $P,Q$ have the same finite rank and a matrix of $f$ has determinant a unit, then $f$ is an isomorphism. A nonzero nonunit determinant gives a generic isomorphism with a finite congruence cokernel.

These are module-theoretic consequences. They do not prove that a particular degeneracy map has the required generic rank or residual injectivity.

### 12.3 The deeper input in an Ihara-type lemma

An Ihara-type lemma typically asserts that a degeneracy map is injective after localizing at a suitable nonexceptional residual maximal ideal, often with torsion-free or controlled cokernel. Such a statement is not a consequence of double-coset algebra, commutativity, or localization alone.

Its role can be isolated axiomatically:

> **Level-injectivity input.** For the chosen $\mathfrak m$, the map
> $$
>
>> M_{\mathfrak m}^{\oplus2}\longrightarrow N_{\mathfrak m}
>> $$
>
> is injective, and possibly its cokernel is $\mathcal O$-torsion-free.

Once supplied, formal algebra gives a faithful embedded old lattice, identifies its quotient presentation, and allows pairings to measure the old/new intersection. But proving the input can use arithmetic of stabilizers, strong approximation, group cohomology, or geometric irreducibility. None belongs to the formal Hecke-algebra construction.

Likewise, excluding an Eisenstein or character-like residual system is not empty terminology here. One must formulate the exclusion using only available Hecke data or postpone it until another theory provides a sharper definition. We will simply state any needed residual hypothesis as part of a level-injectivity theorem rather than assume such a theorem universally.

A typical level-control argument has three logically different layers.

1. At the correspondence layer, construct $\delta_0,\delta_1$, prove away-from-$\mathfrak q$ intertwining, and compute $\delta_i^*\delta_j$ with exact normalization.
2. At the arithmetic layer, prove level injectivity at the chosen residual maximal ideal and determine whether the cokernel has coefficient torsion.
3. At the commutative-algebra layer, localize exact sequences, apply Nakayama or a determinant criterion, and compare faithful image algebras.

Only the first and third layers are formal consequences of the present setup. The second is the bridge that depends on the arithmetic situation. Keeping the layers separate prevents a deep injectivity assertion from being hidden inside the phrase “by degeneracy maps.”

There is also a distinction between controlling forms and controlling characters. A surjective map of localized Hecke algebras makes every lower-level character pull back to a deeper-level character. It does not say that a lower-level eigenvector maps injectively under a chosen degeneracy map. Conversely, an injective equivariant map of modules yields a surjection of image algebras in the deeper-to-shallower direction, but the deeper module can contain additional characters.

### 12.4 Comparing acting Hecke algebras

A common abstract algebra $A$ acts on $M$ and $N$, giving quotients

$$
\mathbb T_U=A/I_U,
\qquad
\mathbb T_{U'}=A/I_{U'}.
$$

There is a surjection $\mathbb T_U\to\mathbb T_{U'}$ exactly when

$$
I_U\subseteq I_{U'}.
$$

No direction follows merely from $U'\subset U$. The deeper-level module is larger, so it can detect more of $A$, suggesting $I_{U'}\subseteq I_U$ and hence a surjection $\mathbb T_{U'}\to\mathbb T_U$ when the lower-level module embeds equivariantly. This suggestion becomes a proof if $M$ is an $A$-stable submodule of $N$: any element annihilating $N$ annihilates $M$.

After localization at compatible maximal ideals, one obtains

$$
(\mathbb T_{U'})_{\mathfrak m'}
\twoheadrightarrow(\mathbb T_U)_{\mathfrak m}
$$

provided the equivariant inclusion exists. It is an isomorphism only if the localized deeper module detects no additional away-from-$\mathfrak q$ relations. Equality of residual eigenvalues, equality of generic dimensions, or injectivity of a degeneracy map alone does not prove this.

If a new operator $U_{\mathfrak q}$ is adjoined at deeper level, the full deeper Hecke algebra is generally larger. A relation such as a quadratic equation over the old algebra may give a finite map from an old algebra with an adjoined root, but the exact relation and surjectivity must be established from local correspondences. Formal control begins after that computation, not before it.

For example, suppose a computed action on an old plane gives an operator $U$ satisfying

$$
U^2-aU+b=0,
\qquad a,b\in(\mathbb T_U)_{\mathfrak m}.
$$

There is then a map

$$
(\mathbb T_U)_{\mathfrak m}[X]/(X^2-aX+b)
\longrightarrow\operatorname{End}(N^{\mathrm{old}}_{\mathfrak m}),
\qquad X\longmapsto U.
$$

It need not be injective if the old plane degenerates, and it need not generate the full deeper-level image on $N_{\mathfrak m}$. When the polynomial has two distinct roots generically but a double root residually, the two refinements at $\mathfrak q$ become congruent. This is the branch-crossing algebra of Chapter 8 arising from a level computation; all conclusions begin with the proved quadratic relation.

## 13. Congruence modules and congruence ideals

### 13.1 Failure of two lattices to split

Suppose a finite-dimensional $E$-space has a direct decomposition

$$
V=V_1\oplus V_2
$$

and $L\subset V$ is an $\mathcal O$-lattice. Put

$$
L_i=L\cap V_i.
$$

The sum $L_1\oplus L_2$ injects into $L$, but it need not be all of $L$. The quotient

$$
C(L;V_1,V_2)
=L/(L_1+L_2)
$$

is finite torsion. It is the elementary **congruence module** of the two generic summands.

Why is it finite? Both $L$ and $L_1+L_2$ are full lattices in $V$: the projections of a basis of $L$ have bounded denominators, so multiplying by a power of $\varpi$ places $L$ inside $L_1+L_2$. Thus some $\varpi^n$ kills the quotient.

The module vanishes exactly when the generic splitting is integral. A nonzero class is represented by a vector of $L$ whose two generic components are individually nonintegral although their sum is integral. This is the lattice-theoretic essence of a congruence.

**Worked lattice calculation.** Let $V=Ee_1\oplus Ee_2$ and

$$
L=\mathcal Oe_1+\mathcal Oe_2
+\mathcal O\frac{e_1+e_2}{\varpi^n}.
$$

Then $L\cap Ee_i=\mathcal Oe_i$ for $i=1,2$. For example, cancellation of the $e_2$-coordinate forces the coefficient of $(e_1+e_2)/\varpi^n$ to be divisible by $\varpi^n$. The class of this fractional diagonal vector generates the congruence module, and

$$
C(L;Ee_1,Ee_2)\cong\mathcal O/(\varpi^n).
$$

Its two generic components have denominator $\varpi^n$, but their sum was deliberately placed in the ambient lattice. This is the module analogue of two characters agreeing modulo $\varpi^n$.

### 13.2 An elementary finite-module construction

Apply the construction to a generic old/new decomposition

$$
N_E=N_E^{\mathrm{old}}\oplus N_E^{\mathrm{new}}.
$$

Define the saturated lattices

$$
L_{\mathrm{old}}=N\cap N_E^{\mathrm{old}},
\qquad
L_{\mathrm{new}}=N\cap N_E^{\mathrm{new}}.
$$

Then

$$
C_{\mathrm{old,new}}
=N/(L_{\mathrm{old}}+L_{\mathrm{new}})
$$

measures failure of the rational old/new decomposition to split integrally. This definition is symmetric and basis independent.

There is a related module that retains the actual degeneracy image:

$$
C_{\mathrm{sat}}
=L_{\mathrm{old}}/N^{\mathrm{old}}.
$$

It measures failure of the old image to be saturated. The two modules answer different questions. $C_{\mathrm{sat}}$ compares two old lattices; $C_{\mathrm{old,new}}$ compares the sum of saturated old and new lattices with the ambient lattice.

If a perfect pairing identifies $N_E^{\mathrm{new}}$ with the orthogonal complement of $N_E^{\mathrm{old}}$, one can express the first congruence module through discriminants of the restricted pairing. Without perfectness, the lattice quotient definition remains valid and should be preferred.

### 13.3 Fitting and annihilator ideals

For a finite torsion $\mathcal O$-module $C$, the annihilator

$$
\operatorname{Ann}_{\mathcal O}(C)
$$

records the smallest power of $\varpi$ killing every class, while the zeroth Fitting ideal

$$
\operatorname{Fitt}_{\mathcal O}(C)
$$

records total length. If

$$
C\cong\bigoplus_i\mathcal O/(\varpi^{a_i}),
$$

then

$$
\operatorname{Ann}_{\mathcal O}(C)
=(\varpi^{\max_i a_i}),
\qquad
\operatorname{Fitt}_{\mathcal O}(C)
=(\varpi^{\sum_i a_i}).
$$

Thus the ideals generally differ.

When $C$ is a finite module over a local Hecke algebra $\mathbb T_{\mathfrak m}$, one may likewise take

$$
\operatorname{Ann}_{\mathbb T_{\mathfrak m}}(C)
\quad\text{or}\quad
\operatorname{Fitt}_{\mathbb T_{\mathfrak m}}(C).
$$

Either may be called a congruence ideal, so the convention must be stated. The Fitting ideal has better multiplicativity in presentations; the annihilator states the exact operator congruence killing the module. They coincide for every cyclic module $C\cong\mathbb T_{\mathfrak m}/I$, when both equal $I$, but not in general.

Length supplies a numerical summary over a DVR:

$$
\ell_{\mathcal O}(C)
=v_{\varpi}(\operatorname{Fitt}_{\mathcal O}(C)).
$$

If a square matrix $A$ presents $C$, this becomes $v_{\varpi}(\det A)$. For a rectangular presentation, the zeroth Fitting ideal is generated by the maximal minors. Determinant formulas are therefore special cases of a basis-independent presentation ideal.

Under a finite flat coefficient extension $\mathcal O\to\mathcal O'$, Fitting ideals extend:

$$
\operatorname{Fitt}_{\mathcal O'}(C\otimes_{\mathcal O}\mathcal O')
=\operatorname{Fitt}_{\mathcal O}(C)\mathcal O'.
$$

Uniformizer-normalized lengths scale with ramification in the same way as congruence depths of eigencharacters. This compatibility is one reason Fitting ideals are preferable to an unnormalized numerical exponent.

### 13.4 The degeneracy determinant

Suppose $\delta:P\to N$ is injective, $P$ and its image have a perfect induced generic pairing, and $G=\delta^*\delta$ is represented on the free module $P$ by a square matrix. The cokernel of

$$
G:P\longrightarrow P
$$

has Fitting ideal generated by $\det G$. If $G$ is generically invertible, this cokernel is finite.

The determinant detects denominators of the orthogonal projector

$$
e=\delta G^{-1}\delta^*.
$$

If $\det G$ is a unit, $e$ is integral and old splits from new. If $\det G$ is divisible by $\varpi$, the generic projector can acquire denominators, permitting an old/new congruence. One should not conclude that the exact congruence module is always $\operatorname{coker}G$: identifying it requires unimodularity of the ambient pairing and precise comparison of the image lattice with its dual. What is always true is that $G$ supplies an elementary finite module whose support contains the failure of splitting.

**Rank-one example.** Let $P=\mathcal O$, $N=\mathcal O^2$ with the standard pairing, and $\delta(1)=(1,a)$. Then

$$
G=(1+a^2).
$$

If $1+a^2$ is a unit, the line and its orthogonal complement split integrally. If $1+a^2$ is a nonzero element of $\varpi\mathcal O$, the two primitive vectors $(1,a)$ and $(-a,1)$ have determinant $1+a^2$, so their sum has index measured exactly by that element. Here the congruence module is $\mathcal O/(1+a^2)$. If $1+a^2=0$, the two generic lines coincide rather than forming an old/new direct sum, so no finite congruence module is defined by this decomposition.

For higher rank, the elementary divisors of $G$ retain more information than its determinant. If invertible matrices over $\mathcal O$ put $G$ in the form

$$
\operatorname{diag}(\varpi^{a_1},\ldots,\varpi^{a_r}),
$$

then

$$
\operatorname{coker}G
\cong\bigoplus_i\mathcal O/(\varpi^{a_i}).
$$

The largest $a_i$ is the maximum depth of a direction in which splitting fails, while their sum is the determinant valuation. A single principal congruence ideal retains only part of this structure. The full finite module is preferable when several packets or multiplicity spaces meet.

## 14. Freeness and projectivity: exact criteria

### 14.1 Over the coefficient ring

The automorphic module $M$ is finite free over $\mathcal O$ under the standing torsion-free hypothesis. Earlier stabilizer theory supplies common sufficient conditions:

- the weight lattice is finite free and the automorphic module is a torsion-free submodule;
- projective stabilizer orders are units, so invariants are idempotent summands;
- the level is sufficiently small that projective stabilizers are trivial;
- central-character equations cut out a saturated submodule.

Over a DVR, finite torsion-free is enough for freeness; averaging is not necessary. Averaging gives stronger conclusions such as arbitrary base change and split invariants.

The finite class-set realization makes this point concrete. If the weight lattice $W_{\mathcal O}$ is free, every stabilizer invariant module $W_{\mathcal O}^{\Gamma_i}$ is a submodule of a free module and hence free over the DVR. The central-character space is the kernel of finitely many maps between finite free modules, so it too is torsion-free. This proves coefficient freeness even at bad stabilizer primes. What can fail there is clean reduction, direct-summand status, and perfectness of the restricted pairing—not DVR-freeness itself.

Over a Dedekind coefficient domain, finite torsion-free modules are projective but need not be free. Localizing or completing at a coefficient prime recovers the DVR conclusion. This is why a global integral automorphic module can be naturally projective while every local coefficient incarnation is free.

Localization with respect to the Hecke algebra preserves $\mathcal O$-torsion-freeness. Since $M_{\mathfrak m}$ is an $\mathcal O$-direct summand of $M$ through the finite product idempotent decomposition, it is finite free over $\mathcal O$. If the reduced generic algebra on this local factor is $\prod_iE_i$ and $e_iM_E$ has dimension $d_i$ over $E_i$, then

$$
\operatorname{rank}_{\mathcal O}M_{\mathfrak m}
=\sum_i[E_i:E]d_i.
$$

Thus the coefficient rank counts generic multiplicities with the residue degrees of their branches; it is not an unweighted count of eigencharacters over $E$.

If one forms the automorphic module directly over a non-DVR coefficient ring, none of these statements should be transported without checking projectivity. Finite submodules of finite free modules can fail to be projective over higher-dimensional local rings.

### 14.2 Over the Hecke algebra

The action makes $M_{\mathfrak m}$ a finite faithful $\mathbb T_{\mathfrak m}$-module. Finite generation follows because it is already finite over $\mathcal O$ and $\mathcal O\subseteq\mathbb T_{\mathfrak m}$. Projectivity or freeness over $\mathbb T_{\mathfrak m}$ is not formal.

Over a local ring, finite projective modules are free. Thus one may prove Hecke-freeness by proving projectivity. Useful sufficient criteria include:

1. exhibit an explicit $\mathbb T_{\mathfrak m}$-basis;
2. show $M_{\mathfrak m}$ is flat and finite over $\mathbb T_{\mathfrak m}$;
3. use a presentation and a depth or Fitting-ideal criterion appropriate to the local algebra;
4. construct a surjection $\mathbb T_{\mathfrak m}^{\oplus r}\to M_{\mathfrak m}$ and compare $\mathcal O$-ranks.

The last step needs care. Equal generic dimensions plus surjectivity gives an $\mathcal O$-torsion kernel, which vanishes if the source is $\mathcal O$-torsion-free. Equal dimensions without a surjection does not produce a basis.

### 14.3 Multiplicity and rank-one criteria

Suppose $\mathbb T_E$ is reduced. The generic fiber of the local factor then has a product decomposition

$$
\mathbb T_{\mathfrak m}\otimes_{\mathcal O}E
\cong\prod_iE_i,
\qquad
d_i=\dim_{E_i}(e_iM_E),
$$

where $e_i$ is the idempotent of the factor $E_i$. If $M_{\mathfrak m}$ is free of rank $r$ over $\mathbb T_{\mathfrak m}$, then

$$
d_i=r
$$

for every branch $i$ through $\mathfrak m$. This is a necessary generic multiplicity condition. After passing to a splitting field, the same assertion says that every embedding-indexed eigencharacter on those branches occurs with multiplicity $r$.

The converse is false in general: constant generic multiplicity proves that $M_{\mathfrak m}$ is locally free on the generic fiber, not at the closed point. Integral extensions between branch lattices can obstruct projectivity.

A practical rank-one criterion is the following.

**Proposition 14.1.** Suppose $M_{\mathfrak m}$ is generated by one element as a $\mathbb T_{\mathfrak m}$-module and

$$
\operatorname{rank}_{\mathcal O}M_{\mathfrak m}
=\operatorname{rank}_{\mathcal O}\mathbb T_{\mathfrak m}.
$$

Then $M_{\mathfrak m}\cong\mathbb T_{\mathfrak m}$.

**Proof.** A generator gives a surjection $\mathbb T_{\mathfrak m}\twoheadrightarrow M_{\mathfrak m}$. Its kernel has $\mathcal O$-rank zero. Since $\mathbb T_{\mathfrak m}$ is $\mathcal O$-torsion-free, the kernel is zero. $\square$

The generator hypothesis can sometimes be checked modulo the local maximal ideal by Nakayama:

$$
\dim_{k(\mathfrak m)}
M_{\mathfrak m}/\mathfrak mM_{\mathfrak m}=1.
$$

That is a residual multiplicity-one statement. It must be proved, not inferred from the commutativity of $\mathbb T$.

More generally, if

$$
r=\dim_{k(\mathfrak m)}
M_{\mathfrak m}/\mathfrak mM_{\mathfrak m},
$$

Nakayama gives a surjection

$$
\mathbb T_{\mathfrak m}^{\oplus r}
\twoheadrightarrow M_{\mathfrak m}.
$$

If the two sides have equal $\mathcal O$-rank, the map is an isomorphism by the same torsion-free kernel argument. The criterion separates two inputs: residual multiplicity computes the minimum number of generators, while a generic rank formula decides whether relations among those generators remain.

A module may be free over every generic field factor and still fail to be projective at a branch crossing. The obstruction is supported on the conductor of $\mathbb T$ in its normalization. Away from that conductor, the algebra equals its normalization locally, and branchwise freeness descends. At the crossing itself, gluing data among the branch lattices must be controlled.

### 14.4 Counterexamples to automatic freeness

Let

$$
A=\mathcal O[\epsilon]/(\epsilon^2)
$$

and let $M=(\varpi,\epsilon)\subset A$. The module is finite and faithful: an element annihilating both $\varpi$ and $\epsilon$ is zero because $A$ is $\mathcal O$-torsion-free and $\epsilon^2=0$. But $M$ is not free of rank one. Its reduction needs two generators, while a free rank-one module needs one.

This shows that finite flatness of the algebra over $\mathcal O$ and faithfulness of the module do not imply Hecke-freeness.

For another example, take the crossing algebra

$$
A=\{(x,y)\in\mathcal O^2:x\equiv y\pmod\varpi\}
$$

and its normalization $M=\mathcal O^2$. It is a finite faithful $A$-module. Generically it has rank one on each branch, but it is not free of rank one over $A$. Indeed, $A$ is local with maximal ideal

$$
\mathfrak n=\varpi\mathcal O\times\varpi\mathcal O,
$$

and

$$
M/\mathfrak nM\cong k^2.
$$

Thus $M$ needs two generators over $A$ by Nakayama, whereas a free rank-one module needs one. The extra integral separation in $M$ obstructs freeness.

Gorenstein hypotheses can help turn duality and multiplicity information into freeness, but only through an explicit theorem. They should not be inserted as an adjective whose consequences are used without proof.

## 15. Brandt matrices and visible congruences

### 15.1 A two-class calculation

Small Brandt matrices make the preceding algebra visible. Consider a scalar two-class module

$$
M=\mathcal O e_1\oplus\mathcal O e_2
$$

and the degree-three matrix

$$
B=
\begin{pmatrix}1&2\\2&1\end{pmatrix}.
$$

Every row sums to $3$, so this has the shape of a split $q=2$ neighbor operator with equal stabilizer masses. The vectors

$$
f_+=e_1+e_2,
\qquad
f_-=e_1-e_2
$$

have eigenvalues

$$
3\quad\text{and}\quad-1.
$$

The image algebra generated by $B$ is

$$
\mathbb T=\mathcal O[B]
\cong\mathcal O[X]/((X-3)(X+1)),
$$

provided the displayed representation is faithful. Evaluation on the two eigenpackets embeds it in $\mathcal O\times\mathcal O$ with image

$$
\{(a,b):a\equiv b\pmod4\}.
$$

Thus the two packets are congruent precisely at coefficient primes dividing $4$. At an odd coefficient prime they lie in different local factors.

This example should not be overinterpreted as a claim about a particular quaternion order. It is a toy Brandt pattern satisfying the elementary audits of nonnegative integral entries, correct degree, and mass symmetry; those necessary conditions are not asserted to prove that a quaternion order realizes it. The calculation isolates the algebra of any realization having this matrix.

### 15.2 Two packets meeting modulo a prime

Take $\mathcal O=\mathbf Z_2$. The eigenvalues $3$ and $-1$ are congruent modulo $2$, indeed modulo $4$. The unique residual maximal ideal is

$$
\mathfrak m=(2,B-1),
$$

because both eigenvalues reduce to $1$. The two characteristic-zero characters

$$
\lambda_+(B)=3,
\qquad
\lambda_-(B)=-1
$$

have difference ideal $(4)$ and congruence depth $2$ in the $2$-adic normalization.

The eigenvectors themselves behave differently. Modulo $2$,

$$
\bar f_+=\bar f_-=e_1+e_2.
$$

The two eigenlines merge into one ordinary eigenspace. Yet

$$
B\bmod2=
\begin{pmatrix}1&0\\0&1\end{pmatrix},
$$

so on the full reduced module every vector is an eigenvector with eigenvalue $1$. The reduced action has forgotten which two generic lines met. The integral local algebra retains their depth of contact.

Adding another commuting Brandt matrix can shrink this accidental residual eigenspace while preserving the common maximal ideal. This illustrates why a residual system is defined by the whole image algebra, not by one operator.

### 15.3 A nonsemisimple special fiber

Use instead the integral matrix

$$
C=
\begin{pmatrix}0&1\\0&\varpi\end{pmatrix}
$$

on $\mathcal O^2$. Its characteristic-zero eigenvalues are $0$ and $\varpi$, so the generic algebra is reduced. The acting algebra is

$$
\mathcal O[C]\cong
\mathcal O[X]/(X(X-\varpi)).
$$

Modulo $\varpi$,

$$
\bar C=
\begin{pmatrix}0&1\\0&0\end{pmatrix},
$$

and the special-fiber algebra is $k[X]/(X^2)$. There is one ordinary eigenline $ke_1$ but a two-dimensional generalized eigenspace. The nilpotent operator is not evidence that the generic fiber was nonreduced; it records the collision of the two eigenvalues modulo $\varpi$.

This matrix need not have nonnegative entries and is therefore not itself a scalar Brandt matrix in the standard characteristic basis. It can arise after an integral change of basis inside a Hecke-stable lattice. Nonnegativity is coordinate-specific; the local algebra and its nilpotent special fiber are basis independent.

### 15.4 A three-class weighted check

Let a scalar class module have effective stabilizer orders

$$
(e_1,e_2,e_3)=(1,2,1)
$$

and consider

$$
B=
\begin{pmatrix}
1&1&1\\
2&1&0\\
1&0&2
\end{pmatrix}.
$$

Every row sums to $3$. With mass matrix

$$
H=\operatorname{diag}(1,1/2,1),
$$

one checks

$$
HB=B^{\mathsf t}H.
$$

Thus $B$ is self-adjoint for the mass pairing even though it is not symmetric in the characteristic basis. Its characteristic polynomial is

$$
(X-3)(X^2-X-1).
$$

The eigenvalue $3$ is rational, while the other two lie in the quadratic field cut out by $X^2-X-1$. The discriminant $5$ shows that the two quadratic packets meet at primes above $5$. Their common residual eigenvalue is the double root of $X^2-X-1$ modulo $5$. Substituting $3$ into the quadratic factor also gives $5$, so all three eigenvalues have the same residue at the prime above $5$.

The last clause is the important audit: congruence for one Brandt matrix is only necessary for congruence of full Hecke eigensystems. Every other generator must also agree. A computed matrix can exhibit a possible congruence prime, but the image algebra decides whether the congruence actually occurs.

## 16. Augmentations, cotangent modules, and congruence ideals

### 16.1 Why one branch must be distinguished

The congruence modules of Chapter 13 compare two summands symmetrically. Numerical comparison with a deformation problem is usually asymmetric: one characteristic-zero eigensystem has been selected, and one wants to measure how that branch meets all the others. An augmentation is the algebraic device that singles out the branch while retaining the whole local algebra around it.

Let $A$ be a finite flat local $\mathcal O$-algebra and let

$$
\lambda:A\longrightarrow\mathcal O
$$

be a surjective $\mathcal O$-algebra homomorphism. Since $\lambda$ is the identity on the structural copy of $\mathcal O$, it is automatically surjective. Put

$$
I_\lambda=\ker\lambda.
$$

The pair $(A,\lambda)$ is an **augmented local coefficient algebra**. In the Hecke setting, $\lambda$ is an integral eigencharacter on a chosen local factor. Such a character need not exist over the original coefficient ring. One may first enlarge $E$ to contain its values, replace $\mathcal O$ by the corresponding valuation ring, and choose the prime through which the residual system is obtained. Every invariant below is relative to that choice.

After inverting $\varpi$, assume for intuition that $A_E$ is reduced and that $\lambda_E$ is one of its field-valued factors. Then

$$
A_E\cong E\times B,
$$

with $\lambda_E$ the first projection. The ideal $I_{\lambda,E}$ is $0\times B$. The integral algebra need not contain the projector $(1,0)$: a denominator may be required to separate the chosen branch from $B$. The size of that denominator is the congruence invariant.

The local and augmentation hypotheses both matter. If $A$ were a product already, the chosen branch would be an integral direct factor and there would be no congruence. If $A_E$ were nonreduced, the complement would not be a product of genuine branches. If $\lambda$ took values only in a larger valuation ring, replacing it by a fictitious $\mathcal O$-valued map would change the ideal being measured.

### 16.2 The congruence ideal of an augmentation

The elements supported entirely on the chosen branch are exactly those annihilating its kernel. Define

$$
A[I_\lambda]
=\operatorname{Ann}_A(I_\lambda)
=\{a\in A:aI_\lambda=0\}.
$$

The **congruence ideal** and **congruence module** of the augmentation are

$$
\boxed{
\eta_\lambda=\lambda(A[I_\lambda])\subseteq\mathcal O,
\qquad
\Psi_\lambda=\mathcal O/\eta_\lambda.}
$$

Because $\mathcal O$ is a DVR, $\eta_\lambda$ is principal, but no generator is canonical: multiplying a generator by a unit changes nothing. The quotient module, its Fitting ideal, and its length are canonical.

Suppose $A_E$ is reduced. Then $A[I_\lambda]\otimes E$ is the one-dimensional $E$-space $E\times0$. Consequently $\eta_\lambda$ is nonzero. Indeed a nonzero element of that line can be cleared of denominators to lie in $A[I_\lambda]$, and its first coordinate is nonzero. Hence $\Psi_\lambda$ has finite length. The ideal is the denominator required to place a multiple of the generic projector $(1,0)$ inside $A$.

Two extremes clarify the definition. If $A=\mathcal O\times B$ and $\lambda$ is first projection, then $(1,0)\in A[I_\lambda]$, so $\eta_\lambda=\mathcal O$ and $\Psi_\lambda=0$. The branch splits integrally. At the other extreme, take

$$
A_n=\{(x,y)\in\mathcal O^2:x\equiv y\pmod{\varpi^n}\}
$$

and let $\lambda(x,y)=x$. Then

$$
I_\lambda=0\times\varpi^n\mathcal O,
\qquad
A_n[I_\lambda]=\varpi^n\mathcal O\times0.
$$

Therefore

$$
\eta_\lambda=(\varpi^n),
\qquad
\Psi_\lambda\cong\mathcal O/(\varpi^n).
$$

This is exactly the pairwise congruence depth computed in Chapter 8. The augmented definition extends it to any number of complementary branches without first choosing them individually.

### 16.3 The cotangent module at the branch

The congruence ideal measures separation of branches. The first infinitesimal neighborhood of the chosen branch is measured by a different object:

$$
\boxed{\Phi_\lambda=I_\lambda/I_\lambda^2.}
$$

It is an $\mathcal O=A/I_\lambda$-module. It is the conormal module of the section defined by $\lambda$, or equivalently the pullback of relative differentials:

$$
\Phi_\lambda
\cong
\Omega_{A/\mathcal O}\otimes_{A,\lambda}\mathcal O.
$$

To prove the identity, use the conormal sequence for $A\twoheadrightarrow A/I_\lambda=\mathcal O$:

$$
I_\lambda/I_\lambda^2
\longrightarrow
\Omega_{A/\mathcal O}\otimes_{A,\lambda}\mathcal O
\longrightarrow
\Omega_{\mathcal O/\mathcal O}
\longrightarrow0.
$$

The last term is zero, and the first arrow is an isomorphism because the quotient map is an $\mathcal O$-algebra retraction: every relative differential is generated by $da$ with $a-\lambda(a)\in I_\lambda$, and the only relations are precisely the square terms killed in $I_\lambda/I_\lambda^2$.

If $A_E$ is a product of finite separable fields, then $\Omega_{A_E/E}=0$. It follows that $\Phi_\lambda\otimes E=0$, so $\Phi_\lambda$ is a finite torsion $\mathcal O$-module. Its zeroth Fitting ideal

$$
\mathfrak d_\lambda
=\operatorname{Fitt}_{\mathcal O}(\Phi_\lambda)
$$

is the branchwise different or cotangent ideal. The length

$$
\ell_{\mathcal O}(\Phi_\lambda)
=v_\varpi(\mathfrak d_\lambda)
$$

measures first-order ramification of the integral branch. It need not agree with the congruence length without a structural hypothesis on $A$.

For the crossing algebra $A_n$, one has

$$
I_\lambda^2=0\times\varpi^{2n}\mathcal O,
$$

and hence

$$
\Phi_\lambda
\cong\varpi^n\mathcal O/\varpi^{2n}\mathcal O
\cong\mathcal O/(\varpi^n).
$$

Here cotangent and congruence modules have the same length. The equality is not an accident: $A_n$ is a hypersurface.

### 16.4 A complete-intersection determinant calculation

We now prove the equality that makes congruence ideals numerically useful. The theorem is local at the selected branch and retains every necessary hypothesis.

**Theorem 16.1 (cotangent--congruence equality).** Let $(A,\lambda)$ be a finite flat augmented local $\mathcal O$-algebra. Assume:

1. $A$ is a complete intersection over $\mathcal O$;
2. $A_E$ is a product of finite separable field extensions of $E$.

Then $\Phi_\lambda$ and $\Psi_\lambda$ have finite length and

$$
\boxed{
\operatorname{Fitt}_{\mathcal O}(\Phi_\lambda)
=\eta_\lambda,
\qquad
\ell_{\mathcal O}(\Phi_\lambda)
=\ell_{\mathcal O}(\Psi_\lambda).}
$$

**Proof strategy.** Choose coordinates centered at the augmentation. Finiteness and the complete-intersection hypothesis give equally many variables and equations. The coefficient matrix expressing the equations in the augmentation ideal presents the cotangent module. Its determinant also generates the annihilator of the augmentation ideal, by the determinant transition lemma for two regular sequences.

**Proof.** There is a presentation

$$
P=\mathcal O[[X_1,\ldots,X_r]]
\twoheadrightarrow A=P/(f_1,\ldots,f_r)
$$

in which $X_j$ maps into $I_\lambda$ and $\lambda(X_j)=0$. The equality of the number of variables and equations follows because $A$ is finite flat of dimension one and the equations form a regular sequence in the regular ring $P$ of dimension $r+1$. Since every $f_i$ vanishes under $X_j\mapsto0$, write

$$
f_i=\sum_{j=1}^r a_{ij}X_j,
\qquad a_{ij}\in P.
$$

Let $A_0=(\lambda(a_{ij}))\in M_r(\mathcal O)$. Reducing the conormal relations modulo $(X_1,\ldots,X_r)^2$ gives a presentation

$$
\mathcal O^r\xrightarrow{A_0}\mathcal O^r
\longrightarrow\Phi_\lambda\longrightarrow0.
$$

Generic separability makes $\Phi_\lambda$ torsion, so $\det A_0\ne0$, and

$$
\operatorname{Fitt}_{\mathcal O}(\Phi_\lambda)
=(\det A_0).
$$

It remains to identify the congruence ideal. Put $\Delta=\det(a_{ij})\in P$. The adjugate identity gives

$$
\Delta X_j\in(f_1,\ldots,f_r)
$$

for every $j$, so the image $\bar\Delta\in A$ annihilates $I_\lambda$. Hence $(\det A_0)\subseteq\eta_\lambda$.

For the reverse inclusion use the determinant transition lemma: if two length-$r$ regular sequences $f_1,\ldots,f_r$ and $X_1,\ldots,X_r$ in a local Cohen--Macaulay ring satisfy $f_i=\sum_j a_{ij}X_j$, then

$$
((f_1,\ldots,f_r):(X_1,\ldots,X_r))
=(f_1,\ldots,f_r,\Delta).
$$

Here is the decisive argument. The Koszul complexes of the two regular sequences resolve their quotients. The matrix $(a_{ij})$ gives a chain map between those complexes; on the top exterior power it is multiplication by $\Delta$. Dualizing the two resolutions and using exactness in every lower degree shows that an element carrying every $X_j$ into $(f_1,\ldots,f_r)$ differs modulo $(f_1,\ldots,f_r)$ from a multiple of $\Delta$. This is exactly the displayed colon identity.

After quotienting by the $f_i$, the colon identity says

$$
\operatorname{Ann}_A(I_\lambda)=A\bar\Delta.
$$

Applying $\lambda$ gives

$$
\eta_\lambda=(\lambda(\bar\Delta))
=(\det A_0).
$$

The Fitting-ideal identity follows, and equality of lengths follows by valuation in the DVR. $\square$

The theorem is exact but one-directional. A complete intersection gives equality. Equality for one augmentation does not, by itself, prove that an arbitrary algebra is a complete intersection; that converse is a deeper numerical criterion requiring additional hypotheses and belongs to the later structural comparison theory.

### 16.5 Gorenstein duality and congruence functionals

Complete intersections are Gorenstein, so Theorem 16.1 has a dual interpretation. This interpretation is also useful when Gorensteinness is known by another route.

Assume $A$ is finite flat local over $\mathcal O$ and

$$
A^\vee=\operatorname{Hom}_{\mathcal O}(A,\mathcal O)
$$

is free of rank one as an $A$-module. Choose a generator $\theta$. The augmentation $\lambda$ is an element of $A^\vee$, so there is a unique $c_\lambda\in A$ with

$$
\lambda=c_\lambda\theta.
$$

For $x\in I_\lambda$ and $a\in A$,

$$
(x\lambda)(a)=\lambda(xa)=\lambda(x)\lambda(a)=0.
$$

Thus $I_\lambda c_\lambda=0$, so $c_\lambda\in A[I_\lambda]$. Conversely, a functional in $A^\vee$ annihilated by $I_\lambda$ factors through $A/I_\lambda=\mathcal O$ and is therefore an $\mathcal O$-multiple of $\lambda$. Transporting this statement through the basis $\theta$ gives

$$
A[I_\lambda]=\mathcal O c_\lambda.
$$

Consequently

$$
\boxed{\eta_\lambda=(\lambda(c_\lambda)).}
$$

Changing $\theta$ by an $A$-unit changes $c_\lambda$ by the inverse unit and changes $\lambda(c_\lambda)$ only by an $\mathcal O$-unit. Hence the ideal is independent of the chosen duality generator.

In an automorphic application, a perfect module pairing and rank-one Hecke freeness can supply $A^\vee\cong A$ by Theorem 9.2. A normalized coefficient functional then becomes a congruence functional. But every arrow is conditional:

$$
\text{perfect pairing + rank-one Hecke freeness}
\Longrightarrow A\text{ Gorenstein}
\Longrightarrow A[I_\lambda]\text{ is a line}.
$$

Generic multiplicity one alone gives neither integral freeness nor Gorensteinness. A perfect coefficient pairing on a higher-rank module gives neither statement. The dual formula is an interface, not an automatic feature of a Hecke algebra.

### 16.6 Several branches and nonprincipal congruence data

The augmentation ideal compares one branch with all others at once. If

$$
A_E\cong E\times E_2\times\cdots\times E_s,
$$

then $A[I_\lambda]\otimes E$ is the first coordinate line. The single ideal $\eta_\lambda$ measures the denominator of its projector against the union of the remaining branches. It generally does not decompose as the product of all pairwise difference ideals without additional transversality.

Pairwise congruence depths can overlap. Three branches may meet at one residual point with relations that are not determined by the three pairwise valuations. A higher-dimensional generalized eigenspace can also carry extensions among the branches. The finite modules

$$
\widetilde A/A,
\qquad
I_\lambda/I_\lambda^2,
\qquad
\mathcal O/\eta_\lambda
$$

retain different parts of that structure: normalization records all gluing, the cotangent module records first-order ramification at the chosen branch, and the augmented congruence module records the denominator of its generic projector.

Over the DVR every ideal is principal, but the full Hecke-valued congruence module need not be cyclic. Likewise the old--new congruence module of Chapter 13 may have several elementary divisors even when its Fitting ideal is principal. A single valuation records their sum, not their distribution. Numerical comparison should therefore begin with modules and Fitting ideals and pass to lengths only after finiteness has been proved.

## 17. Comparison with deformation-theoretic numerical invariants

### 17.1 The comparison problem without a constructed map

The complete local Hecke algebra is intended to be compared with a ring representing a deformation problem. At this point no arithmetic construction supplies such a map. Nevertheless the algebraic comparison can be developed exactly in conditional form: if a continuous augmented surjection is later constructed, which modules compare, in which direction do the inequalities go, and which extra hypotheses turn equality into structure?

Let $(R,\lambda_R)$ be a complete Noetherian local augmented $\mathcal O$-algebra and let $(A,\lambda_A)$ be a finite flat local augmented $\mathcal O$-algebra. Suppose there is a continuous surjection

$$
\phi:R\twoheadrightarrow A
$$

such that

$$
\lambda_A\circ\phi=\lambda_R.
$$

Put

$$
\mathfrak p_R=\ker\lambda_R,
\qquad
\mathfrak p_A=\ker\lambda_A,
\qquad
J=\ker\phi.
$$

The letter $\mathfrak p$ here denotes an augmentation ideal, not necessarily the maximal ideal; the local maximal ideal is generated by $\mathfrak p_R$ together with the coefficient maximal ideal. Since $\phi$ is augmented, $J\subseteq\mathfrak p_R$ and $\phi(\mathfrak p_R)=\mathfrak p_A$.

### 17.2 The conormal comparison for a surjection

The first exact comparison is elementary and fundamental.

**Proposition 17.1 (augmentation conormal sequence).** Under the preceding hypotheses there is a short exact sequence of $\mathcal O$-modules

$$
\boxed{
0\longrightarrow
\frac{J}{J\cap\mathfrak p_R^2}
\longrightarrow
\frac{\mathfrak p_R}{\mathfrak p_R^2}
\longrightarrow
\frac{\mathfrak p_A}{\mathfrak p_A^2}
\longrightarrow0.}
$$

**Proof strategy.** Surjectivity carries the augmentation ideal onto the augmentation ideal. The kernel on cotangent quotients consists exactly of classes represented by elements of $J$.

**Proof.** The induced map on the two middle modules is surjective because $\phi(\mathfrak p_R)=\mathfrak p_A$. Its kernel is

$$
\frac{J+\mathfrak p_R^2}{\mathfrak p_R^2},
$$

which is canonically $J/(J\cap\mathfrak p_R^2)$. $\square$

Write

$$
\Phi_R=\mathfrak p_R/\mathfrak p_R^2,
\qquad
\Phi_A=\mathfrak p_A/\mathfrak p_A^2.
$$

If these modules have finite length, then

$$
\ell_{\mathcal O}(\Phi_R)
=\ell_{\mathcal O}(\Phi_A)
+\ell_{\mathcal O}\left(J/(J\cap\mathfrak p_R^2)\right).
$$

Thus the cotangent module of the source is at least as large as that of the target. The difference measures relation directions visible at the selected augmentation to first order. It does not measure every element of $J$: a kernel lying inside $\mathfrak p_R^2$ is invisible in this quotient.

Dualizing after reduction gives the tangent-space injection

$$
\operatorname{Hom}_{\mathcal O}(\Phi_A,k)
\hookrightarrow
\operatorname{Hom}_{\mathcal O}(\Phi_R,k).
$$

This is the expected variance: a quotient ring imposes equations, so its space of first-order points embeds into that of the source.

### 17.3 Tangent dimensions and relation bounds

Suppose $R$ represents a deformation problem over $\mathcal O$. Then the dual of

$$
\frac{\mathfrak m_R}{\mathfrak m_R^2+\varpi R}
$$

is its residual tangent space. Its dimension is the exact number of variables in a minimal relative power-series presentation. If a complete, functorial, additive, effective obstruction theory takes values in a finite-dimensional space $V$, then a minimal presentation

$$
R\cong\mathcal O[[X_1,\ldots,X_g]]/(f_1,\ldots,f_s)
$$

may be chosen with

$$
g=\dim_k t_R,
\qquad
s\leq\dim_kV.
$$

This generator--relation information and the augmentation cotangent module answer different questions. The residual tangent dimension counts directions modulo both $\mathfrak m_R^2$ and $\varpi$. The finite module $\Phi_R=\mathfrak p_R/\mathfrak p_R^2$ measures the entire coefficient-adic thickness of the chosen characteristic-zero augmentation. Its length can be finite even when its reduction is nonzero, and it records more than the tangent dimension.

In arithmetic applications the tangent space is often calculated by a Selmer condition and the effective obstruction bound by a dual condition. The exact algebraic export is therefore:

$$
\begin{array}{c|c}
\text{deformation datum}&\text{local algebra datum}\\ \hline
\dim_k t_R&\text{minimal relative variables}\\
\dim_k V&\text{upper bound for minimal relations}\\
\Phi_R&\text{cotangent thickness at a chosen lift}\\
J/(J\cap\mathfrak p_R^2)&\text{first-order kernel of }R\twoheadrightarrow A.
\end{array}
$$

No obstruction dimension is automatically the length of a congruence module. The two become numerically adjacent only after a comparison map and the complete-intersection identity on the target have both been established.

### 17.4 The exact numerical chain

Assume now that $A$ is a complete intersection and that $A_E$ is a product of finite separable fields. Theorem 16.1 gives

$$
\ell_{\mathcal O}(\Phi_A)
=\ell_{\mathcal O}(\Psi_{\lambda_A}).
$$

Proposition 17.1 therefore gives the exact identity

$$
\boxed{
\ell_{\mathcal O}(\Phi_R)
=\ell_{\mathcal O}(\Psi_{\lambda_A})
+\ell_{\mathcal O}
\left(J/(J\cap\mathfrak p_R^2)\right).}
$$

In particular,

$$
\ell_{\mathcal O}(\Psi_{\lambda_A})
\leq\ell_{\mathcal O}(\Phi_R).
$$

This is the exact direction of the basic inequality. A deformation calculation that supplies the reverse inequality

$$
\ell_{\mathcal O}(\Phi_R)
\leq\ell_{\mathcal O}(\Psi_{\lambda_A})
$$

forces equality everywhere and gives

$$
J\subseteq\mathfrak p_R^2.
$$

The reverse inequality is not a consequence of Hecke theory. It normally comes from a separate numerical calculation that compares a deformation cotangent module with an automorphic congruence ideal. The achievement of the present chapter is to identify the exact endpoints and the exact error term.

The same statement can be phrased through Fitting ideals. If $C$ is a finite torsion $\mathcal O$-module, write $\operatorname{Fitt}(C)=(\varpi^{\ell(C)})$. The short exact sequence gives

$$
\operatorname{Fitt}(\Phi_R)
=\operatorname{Fitt}(\Phi_A)\,
\operatorname{Fitt}\left(J/(J\cap\mathfrak p_R^2)\right),
$$

and the complete-intersection theorem replaces $\operatorname{Fitt}(\Phi_A)$ by $\eta_{\lambda_A}$. The ideal formula is stable under finite flat coefficient extension; the numerical valuation scales with ramification.

### 17.5 A safe numerical forcing theorem

The following theorem states exactly what the elementary numerical comparison proves, and adds a transparent hypothesis when an isomorphism is desired.

**Theorem 17.2 (numerical forcing with visible kernel).** Let

$$
\phi:(R,\lambda_R)\twoheadrightarrow(A,\lambda_A)
$$

be a surjective augmented map as above. Assume:

1. $A$ is finite flat and a complete intersection over $\mathcal O$;
2. $A_E$ is a product of finite separable fields;
3. $\Phi_R$ has finite length;
4. $\ell_{\mathcal O}(\Phi_R)\leq\ell_{\mathcal O}(\mathcal O/\eta_{\lambda_A})$.

Then

$$
\Phi_R\xrightarrow{\sim}\Phi_A,
\qquad
\ell_{\mathcal O}(\Phi_R)
=\ell_{\mathcal O}(\mathcal O/\eta_{\lambda_A}),
\qquad
J\subseteq\mathfrak p_R^2.
$$

If, in addition,

$$
J\cap\mathfrak p_R^2=\mathfrak p_RJ,
$$

then $\phi$ is an isomorphism.

**Proof strategy.** The exact numerical identity of Section 17.4 forces the conormal error term to vanish. The final intersection hypothesis turns this vanishing into the Nakayama equation $J=\mathfrak p_RJ$.

**Proof.** Theorem 16.1 and Proposition 17.1 give

$$
\ell(\Phi_R)
=\ell(\mathcal O/\eta_{\lambda_A})
+\ell\left(J/(J\cap\mathfrak p_R^2)\right).
$$

Hypothesis 4 forces the last length to be zero and all preceding lengths to be equal. Hence the cotangent map is an isomorphism and $J\subseteq\mathfrak p_R^2$. Under the additional intersection identity,

$$
J=J\cap\mathfrak p_R^2=\mathfrak p_RJ.
$$

The ideal $J$ is finite over the Noetherian ring $R$, and $\mathfrak p_R$ lies in the Jacobson radical. Nakayama gives $J=0$. Since $\phi$ was surjective, it is an isomorphism. $\square$

The extra intersection condition is deliberately visible. Stronger numerical criteria can derive kernel vanishing from complete-intersection and duality hypotheses without assuming this identity separately, but their proof requires the full structure theory of complete intersections, congruence modules, and finite maps. The present theorem records the portion that follows directly from the objects built in this volume.

### 17.6 What equality does and does not prove

An equality of two integers can carry substantial information only after their definitions and finiteness are secured. The comparison above requires an integral augmentation, a surjective augmented map, finite cotangent length, generic separability of the target, and the complete-intersection identity. Removing any hypothesis changes the conclusion.

If the generic target is not separable, $\Phi_A$ can have positive rank and no finite length. If the target is not a complete intersection, cotangent and congruence lengths need not agree. If the comparison map is not surjective, the conormal sequence has a different form. If the characters take values in different valuation rings, their ideals must first be transported by a specified coefficient extension.

Even an isomorphism on cotangent modules does not in general imply an isomorphism of complete local rings. The maps

$$
k[[X]]/(X^3)\twoheadrightarrow k[[X]]/(X^2)
$$

and

$$
k[[X,Y]]/(X^2,Y^3)\twoheadrightarrow
k[[X,Y]]/(X^2,Y^2)
$$

are isomorphisms on suitable first-order cotangent spaces while having nonzero higher-order kernels. They fall outside the finite-flat generically separable setting above, but they show exactly why the last kernel argument cannot be replaced by the phrase “same tangent space.”

Likewise equal Krull dimensions do not kill a height-zero kernel, and equal generic ranks do not produce a map. A valid ring equality needs separate mechanisms for existence of the map, surjectivity, and injectivity. Numerical congruence data are designed to supply one of those mechanisms, not all three by terminology alone.

### 17.7 Old--new congruence numbers in the comparison

The old--new Gram operator supplies a concrete automorphic source for the abstract ideal $\eta_\lambda$. At one new prime, localize the lower-level module at a maximal ideal and assume the standard Gram matrix

$$
G=
\begin{pmatrix}
q+1&T\\
S^{-1}T&q+1
\end{pmatrix}
$$

is generically invertible. On a lower-level eigencharacter $\lambda$ its determinant is

$$
D_{\mathfrak q}(\lambda)
=(q+1)^2-\lambda(S)^{-1}\lambda(T)^2.
$$

If the localized lower-level eigenspace is free of rank one, the pairings are perfect, the degeneracy image is saturated on the generic fiber, and the old and new generic summands are complementary, then

$$
\operatorname{Fitt}_{\mathcal O}(\operatorname{coker}G_\lambda)
=(D_{\mathfrak q}(\lambda)).
$$

Under the additional unimodularity identification from Section 13.4, this is also the Fitting ideal of the corresponding old--new congruence module. It therefore gives an explicit candidate for the augmented congruence ideal on that branch.

Without those hypotheses one has only containment of supports: divisibility of $D_{\mathfrak q}(\lambda)$ is necessary for failure of integral orthogonal splitting, but $\operatorname{coker}G$ need not be the full congruence module. Higher multiplicity produces several elementary divisors; failure of saturation contributes another module; an imperfect pairing changes the dual lattice; and a deeper-level new packet need not exist merely because the old projector has a denominator.

This is the precise interface with change of level. Correspondence calculations produce $G$ and its determinant. Level-injectivity and saturation theorems identify the relevant lattices. Perfect duality converts indices to congruence functionals. Only after those steps may the resulting ideal be placed beside the deformation cotangent module in Section 17.4.

## 18. The complete local Hecke pair

### 18.1 Construction of the pair

We now assemble the endpoint in the exact form needed for later comparison. The input is:

1. a complete DVR $(\mathcal O,\varpi,k)$;
2. a finite free integral quaternionic automorphic module in the representative-value sense of Book 83
   $$
   M=M_{\mathcal O}(U;W,\chi);
   $$
3. a finite bad set $\Sigma$;
4. the specified commuting integral family $T_v,S_v^{\pm1}$ for $v\notin\Sigma$;
5. a maximal ideal $\mathfrak m$ containing $\varpi$ in the image algebra.

Form the faithful image

$$
\mathbb T=\mathcal O[T_v,S_v^{\pm1}:v\notin\Sigma]
\subseteq\operatorname{End}_{\mathcal O}(M),
$$

and first form the ordinary localization

$$
\mathbb T_{\mathfrak m}^{\mathrm{loc}}
=(\mathbb T\setminus\mathfrak m)^{-1}\mathbb T,
\qquad
M_{\mathfrak m}^{\mathrm{loc}}
=M\otimes_{\mathbb T}\mathbb T_{\mathfrak m}^{\mathrm{loc}}.
$$

If $\mathfrak n=\mathfrak m\mathbb T_{\mathfrak m}^{\mathrm{loc}}$, define the final pair by

$$
\boxed{
\mathbb T_{\mathfrak m}
=\varprojlim_r\mathbb T_{\mathfrak m}^{\mathrm{loc}}/\mathfrak n^r,
\qquad
M_{\mathfrak m}
=\varprojlim_rM_{\mathfrak m}^{\mathrm{loc}}/\mathfrak n^rM_{\mathfrak m}^{\mathrm{loc}}.}
$$

Theorem 6.1 and finite-module completeness give canonical maps

$$
\mathbb T_{\mathfrak m}^{\mathrm{loc}}
\xrightarrow{\sim}\mathbb T_{\mathfrak m},
\qquad
M_{\mathfrak m}^{\mathrm{loc}}
\xrightarrow{\sim}M_{\mathfrak m}.
$$

Thus completion changes neither object at this finite level. The superscript on the intermediate objects distinguishes ordinary localization from the completed pair, while the inverse-limit construction declares the maximal-adic topology and places the pair in the category of complete local coefficient algebras and complete finite modules.

The operator polynomial remains

$$
P_v(X)=1-T_vX+q_vS_vX^2
\in\mathbb T_{\mathfrak m}[X]
\qquad(v\notin\Sigma).
$$

If the central character has already made $S_v$ a scalar, that scalar is retained in the constant coefficient. These polynomials are the only local comparison data packaged here.

### 18.2 Its exact structural properties

The constructed pair has the following properties, with no hidden multiplicity or duality assumptions.

**The algebra.** The ring $\mathbb T_{\mathfrak m}$ is commutative, complete Noetherian local, finite free over $\mathcal O$, and has residue field $k(\mathfrak m)$. It is generated topologically—and in fact algebraically—by the images of finitely many members of the specified Hecke family. Its generic fiber may have several branches through $\mathfrak m$. Its special fiber may be nonreduced.

**The module.** The module $M_{\mathfrak m}$ is finite free over $\mathcal O$, finite over $\mathbb T_{\mathfrak m}$, complete for both equivalent adic topologies, and faithful over $\mathbb T_{\mathfrak m}$. Its residual quotient

$$
M_{\mathfrak m}/\mathfrak mM_{\mathfrak m}
$$

need not be one-dimensional. It is not asserted to be free or projective over the Hecke algebra.

**The residual system.** The quotient map

$$
\mathbb T_{\mathfrak m}\longrightarrow k(\mathfrak m)
$$

is the selected residual eigensystem. Every characteristic-zero eigensystem in this localization reduces to it after a suitable coefficient extension, and every generic branch through it is retained.

**Pairing and level structures.** If a perfect integral adjoint-compatible pairing has been proved, it localizes perfectly and supplies dual Hecke modules. If degeneracy maps have been chosen, their old images, adjoint-kernel new modules, Gram operators, and congruence modules all localize exactly. None is part of the bare pair unless included in the data.

### 18.3 Its augmented numerical package

Choose a characteristic-zero eigencharacter on this local factor and enlarge the coefficient DVR so that it becomes an augmentation

$$
\lambda:\mathbb T_{\mathfrak m}\longrightarrow\mathcal O.
$$

The complete local pair then carries three additional finite objects whenever the generic algebra is separable:

$$
I_\lambda=\ker\lambda,
\qquad
\Phi_\lambda=I_\lambda/I_\lambda^2,
\qquad
\Psi_\lambda=
\mathcal O/\lambda(\operatorname{Ann}_{\mathbb T_{\mathfrak m}}I_\lambda).
$$

The first is the ideal of the selected branch, the second is its cotangent module, and the third is its congruence module against the complementary generic branches. Their Fitting ideals are invariant under changing generators of the Hecke algebra. Under finite flat coefficient extension they extend as ideals; their uniformizer-normalized lengths scale by the ramification index.

If $\mathbb T_{\mathfrak m}$ is a complete intersection and its generic fiber is separable, then

$$
\operatorname{Fitt}_{\mathcal O}(\Phi_\lambda)
=\lambda(\operatorname{Ann}I_\lambda),
$$

so cotangent and congruence lengths agree. If a future augmented surjection $R\twoheadrightarrow\mathbb T_{\mathfrak m}$ is constructed, its first-order kernel is exactly the error term

$$
\frac{\ker(R\to\mathbb T_{\mathfrak m})}
{\ker(R\to\mathbb T_{\mathfrak m})\cap(\ker\lambda_R)^2}
$$

in the numerical identity of Chapter 17. This is the promised exact comparison interface: the Hecke side is fully defined before the map exists, while every conclusion about the source remains conditional on the later construction and its hypotheses.

### 18.4 What remains for later comparison

The notation $\mathbb T_{\mathfrak m}$ is now ready to be the target of a continuous local homomorphism from another complete local ring. The topology, residue field, distinguished closed point, and dense family of operator coefficients have all been fixed.

What has not been constructed is equally important. We have not attached a Galois representation to an eigensystem, produced a pseudorepresentation, defined a deformation condition, or built a universal deformation ring. Consequently there is not yet a map from such a ring to $\mathbb T_{\mathfrak m}$. There is also no claim that a future map is surjective or an isomorphism.

The present endpoint supplies only the receiving side:

$$
(\mathbb T_{\mathfrak m},M_{\mathfrak m};
T_v,S_v,P_v(X))_{v\notin\Sigma}.
$$

Later theory may construct a map by matching trace-like and determinant-like coefficients with $T_v$ and $q_vS_v$. Any equality of rings will require hypotheses and arguments beyond Hecke algebra and congruence theory.

### 18.5 The algebra--congruence--localization dictionary

| Concept                       | Exact algebraic object                                                  | What it remembers                                              | What it does not imply                                                |
| ----------------------------- | ----------------------------------------------------------------------- | -------------------------------------------------------------- | --------------------------------------------------------------------- |
| abstract Hecke algebra        | $\mathbb T^{\Sigma,\mathrm{abs}}_{\mathcal O}$                          | formal away-from-$\Sigma$ correspondences                      | faithful action at fixed weight and level                             |
| acting Hecke algebra          | $\mathbb T=\operatorname{im}(\rho_M)$                                   | exact relations on $M$                                         | reducedness or locality                                               |
| residual eigensystem          | $\mathfrak m\supset(\varpi)$                                            | one field-valued special-fiber character                       | an $\mathcal O$-valued lift or a lift of a prescribed residual vector |
| residue field                 | $k(\mathfrak m)=\mathbb T/\mathfrak m$                                  | minimal field of residual eigenvalues                          | equality with the original $k$                                        |
| localization                  | $\mathbb T_{\mathfrak m},M_{\mathfrak m}$                               | every branch and generalized vector supported at $\mathfrak m$ | quotient by $\mathfrak m$                                             |
| completion                    | $\varprojlim\mathbb T_{\mathfrak m}/\mathfrak m^n$                      | all infinitesimal orders                                       | a larger ring at finite level                                         |
| ordinary eigenspace           | $M_L[\lambda]$                                                          | vectors killed by $t-\lambda(t)$                               | the full local summand                                                |
| generalized eigenspace        | $M_L[\lambda]^{\mathrm{gen}}$                                           | nilpotent extensions of one character                          | semisimplicity                                                        |
| congruent characters          | common residual $\mathfrak m$                                           | equality of every Hecke value modulo a prime                   | congruent chosen eigenvectors                                         |
| congruence depth              | $I(\lambda_1,\lambda_2)$                                                | valuation of all character differences                         | coefficient-field-independent raw integer                             |
| normalization                 | $\widetilde{\mathbb T}=\prod\mathcal O_i$ when generic fiber is reduced | separated generic branches                                     | splitting of the original integral algebra                            |
| conductor                     | $(\mathbb T:\widetilde{\mathbb T})$                                     | where separated branches glue                                  | the entire congruence module in every multiplicity                    |
| nilpotent special fiber       | nilradical of $\mathbb T/\varpi$                                        | infinitesimal collision or residual nonsemisimplicity          | nonreduced generic fiber                                              |
| old submodule                 | $\operatorname{im}\delta\subset N$                                      | actual degeneracy lattice                                      | saturation or direct summand                                          |
| old quotient                  | $(M^{\oplus2})/\ker\delta$                                              | lower-level presentation of the old image                      | its embedding index in $N$                                            |
| new kernel                    | $\ker\delta^*$                                                          | vectors with zero adjoint traces                               | orthogonal complement without perfectness                             |
| saturated old lattice         | $N\cap N_E^{\mathrm{old}}$                                              | full integral lattice in generic old space                     | equality with degeneracy image                                        |
| congruence module             | $N/(L_{\mathrm{old}}+L_{\mathrm{new}})$                                 | failure of integral splitting                                  | a canonical principal ideal over every ring                           |
| faithful module               | $\operatorname{Ann}_{\mathbb T}M=0$                                     | every algebra element is detected                              | free or rank one                                                      |
| coefficient freeness          | finite torsion-free over the DVR                                        | a stable integral lattice                                      | Hecke freeness                                                        |
| Hecke freeness                | $M_{\mathfrak m}\cong\mathbb T_{\mathfrak m}^{\oplus r}$                | constant integral multiplicity                                 | automatic Gorenstein property                                         |
| relative Gorenstein duality   | $\mathbb T_{\mathfrak m}^\vee\cong\mathbb T_{\mathfrak m}$              | rank-one dualizing module                                      | automatic from a mass pairing                                         |
| augmentation ideal            | $I_\lambda=\ker\lambda$                                                 | functions vanishing on one chosen branch                       | a canonical branch over the original coefficient ring                 |
| augmentation cotangent module | $I_\lambda/I_\lambda^2$                                                 | infinitesimal thickness at that branch                         | equality with a congruence module without hypotheses                  |
| augmented congruence ideal    | $\lambda(\operatorname{Ann}I_\lambda)$                                  | denominator of the generic branch projector                    | a complete-intersection criterion by itself                           |
| comparison conormal module    | $J/(J\cap\mathfrak p_R^2)$                                              | first-order kernel of an augmented surjection                  | the entire higher-order kernel                                        |

The dictionary is a sequence of safeguards. Each row identifies an object by a construction, not by a slogan. In particular, “localized eigenform” can mean an ordinary eigenvector, a generalized eigenspace, or the entire localized module; these are different levels of information.

### 18.6 Conclusion

An integral Hecke algebra is best understood as the coordinate ring of all eigensystems visible in one finite automorphic module. The abstract correspondence algebra supplies operators, but the faithful image supplies the actual arithmetic space: it is finite and torsion-free over the coefficient DVR, commutative for the specified spherical family, and supported exactly where its module is supported. Passing to a maximal ideal containing the uniformizer selects a residual system without discarding the characteristic-zero branches that meet there.

This viewpoint explains congruence geometrically and algebraically. A characteristic-zero eigensystem is a generic branch. Reduction sends it to a closed residual point. Two branches are congruent when they meet at that point, and the valuation of their difference ideal measures how long they remain indistinguishable. Normalization pulls branches apart; the conductor measures the obstruction to putting them back together integrally. A nilpotent in the special fiber may be the first-order shadow of a perfectly reduced pair of generic branches crossing.

The module is indispensable. It distinguishes a formal maximal ideal from an occurring eigensystem, retains generalized eigenvectors when semisimplicity fails, and makes faithfulness exact after localization. Pairings transport correspondences to adjoints, but perfectness and normalization must be stated. Old forms are an image of degeneracy maps; new forms are kernels of adjoint traces only after those adjoints exist; orthogonal decompositions require an integral inverse to the Gram operator. Congruence modules live precisely in the finite index between rational decomposition and integral splitting.

Selecting one integral eigencharacter turns this geometry into an exact numerical package. Its augmentation ideal has cotangent module $I_\lambda/I_\lambda^2$, while the image of its annihilator is the congruence ideal measuring the denominator of the branch projector. For a generically separable complete intersection the two have the same Fitting ideal. A future augmented surjection onto the Hecke algebra then fits into a short exact conormal sequence, whose error term records the first-order kernel. This identifies, without anticipating the later comparison map, exactly where deformation-theoretic tangent and obstruction calculations must meet automorphic congruence data.

The endpoint is therefore not merely a ring bearing the letter $\mathbb T$. It is the complete local pair

$$
\boxed{(\mathbb T_{\mathfrak m},M_{\mathfrak m})}
$$

together with the specified coefficients $T_v$ and $q_vS_v$ of the unramified polynomials. The algebra is complete local and finite flat over $\mathcal O$; the module is finite free over $\mathcal O$ and faithful over the local Hecke algebra. Freeness over the Hecke algebra, multiplicity one, self-duality, Gorenstein structure, level-control lemmas, and integral old/new splitting remain conditional statements with exact hypotheses. This disciplined package is strong enough to receive future comparison maps and restrained enough not to assume the conclusions those maps are meant to prove.
