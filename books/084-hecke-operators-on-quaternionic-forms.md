# Hecke Operators on Quaternionic Forms

## Contents

1. [From translations to operators](#1-from-translations-to-operators)
   - [The problem solved by a double coset](#11-the-problem-solved-by-a-double-coset)
   - [Finite right-coset sums](#12-finite-right-coset-sums)
   - [Independence and equivariance](#13-independence-and-equivariance)
   - [A convention audit](#14-a-convention-audit)
   - [Standing data and the central constraint](#15-standing-data-and-the-central-constraint)
2. [The double-coset algebra](#2-the-double-coset-algebra)
   - [Haar measure and convolution](#21-haar-measure-and-convolution)
   - [Integral and finite-sum formulas](#22-integral-and-finite-sum-formulas)
   - [Composition and structure constants](#23-composition-and-structure-constants)
   - [Semigroups and coefficient lattices](#24-semigroups-and-coefficient-lattices)
   - [Degree, augmentation, and inversion](#25-degree-augmentation-and-inversion)
3. [The finite class-set calculation](#3-the-finite-class-set-calculation)
   - [Transition data](#31-transition-data)
   - [The block-matrix algorithm](#32-the-block-matrix-algorithm)
   - [Multiplicity and stabilizers](#33-multiplicity-and-stabilizers)
   - [Brandt matrices and graph intuition](#34-brandt-matrices-and-graph-intuition)
4. [Adjoints and mass](#4-adjoints-and-mass)
   - [Why counting measure is not enough](#41-why-counting-measure-is-not-enough)
   - [The inverse-kernel theorem](#42-the-inverse-kernel-theorem)
   - [Central factors and self-adjointness](#43-central-factors-and-self-adjointness)
   - [Weighted matrix symmetry](#44-weighted-matrix-symmetry)
5. [The split hyperspecial local algebra](#5-the-split-hyperspecial-local-algebra)
   - [Choosing the split model](#51-choosing-the-split-model)
   - [Cartan decomposition](#52-cartan-decomposition)
   - [The first double coset](#53-the-first-double-coset)
   - [Multiplication recursion and commutativity](#54-multiplication-recursion-and-commutativity)
6. [Standard unramified operators](#6-standard-unramified-operators)
   - [$T_v$ and $S_v$](#61-t_v-and-s_v)
   - [Normalized versus unnormalized operators](#62-normalized-versus-unnormalized-operators)
   - [The local Hecke polynomial](#63-the-local-hecke-polynomial)
   - [An elementary integral Satake description](#64-an-elementary-integral-satake-description)
7. [From local to global](#7-from-local-to-global)
   - [Restricted tensor operators](#71-restricted-tensor-operators)
   - [Commuting at distinct places](#72-commuting-at-distinct-places)
   - [The Hecke algebra away from bad places](#73-the-hecke-algebra-away-from-bad-places)
   - [Elementary eigensystems](#74-elementary-eigensystems)
   - [A commutativity ledger](#75-a-commutativity-ledger)
8. [Primes in the level](#8-primes-in-the-level)
   - [$K_0$ and Iwahori geometry](#81-k_0-and-iwahori-geometry)
   - [The $U_v$ decomposition](#82-the-u_v-decomposition)
   - [Opposite operators and adjoints](#83-opposite-operators-and-adjoints)
   - [What fails beyond hyperspecial level](#84-what-fails-beyond-hyperspecial-level)
   - [Diamond operators at $K_1$-level](#85-diamond-operators-at-k_1-level)
   - [$U_v$ and diamond relations](#86-u_v-and-diamond-relations)
9. [Ramified quaternionic places](#9-ramified-quaternionic-places)
   - [The valuation filtration](#91-the-valuation-filtration)
   - [Uniformizers and the maximal compact](#92-uniformizers-and-the-maximal-compact)
   - [The surviving operators](#93-the-surviving-operators)
   - [Smaller division-algebra levels](#94-smaller-division-algebra-levels)
10. [Centers, characters, and twists](#10-centers-characters-and-twists)
    - [The center before imposing a character](#101-the-center-before-imposing-a-character)
    - [Central-character quotients](#102-central-character-quotients)
    - [Twisting forms and operators](#103-twisting-forms-and-operators)
    - [Uniformizer dependence revisited](#104-uniformizer-dependence-revisited)
11. [Change of level and old images](#11-change-of-level-and-old-images)
    - [Pullback and trace as correspondences](#111-pullback-and-trace-as-correspondences)
    - [Degeneracy maps](#112-degeneracy-maps)
    - [Intertwining relations](#113-intertwining-relations)
    - [The elementary old submodule](#114-the-elementary-old-submodule)
    - [Adjoint degeneracy maps and the new kernel](#115-adjoint-degeneracy-maps-and-the-new-kernel)
    - [The exact two-by-two Gram matrix](#116-the-exact-two-by-two-gram-matrix)
    - [The level operator on the old image](#117-the-level-operator-on-the-old-image)
    - [Old, saturated old, and new](#118-old-saturated-old-and-new)
    - [Several new primes](#119-several-new-primes)
12. [Coefficients, reduction, and torsion](#12-coefficients-reduction-and-torsion)
    - [When the action is integral](#121-when-the-action-is-integral)
    - [Base change](#122-base-change)
    - [Bad stabilizer primes](#123-bad-stabilizer-primes)
    - [Reduction of eigendata](#124-reduction-of-eigendata)
    - [Stable lattices for an operator family](#125-stable-lattices-for-an-operator-family)
    - [The base-change obstruction](#126-the-base-change-obstruction)
    - [Abstract and acting algebras under base change](#127-abstract-and-acting-algebras-under-base-change)
13. [A ledger of relations](#13-a-ledger-of-relations)
    - [Why every relation carries hypotheses](#131-why-every-relation-carries-hypotheses)
    - [Local relations in one table](#132-local-relations-in-one-table)
    - [Global polynomial families](#133-global-polynomial-families)
    - [Relations in the abstract and acting algebras](#134-relations-in-the-abstract-and-acting-algebras)
14. [Examples over $\mathbf Q$](#14-examples-over-mathbf-q)
    - [The one-class Hurwitz order](#141-the-one-class-hurwitz-order)
    - [A two-class level-three model](#142-a-two-class-level-three-model)
    - [General Brandt matrices](#143-general-brandt-matrices)
    - [A non-self-adjoint level operator](#144-a-non-self-adjoint-level-operator)
15. [The canonical action](#15-the-canonical-action)
    - [The exact module and its operators](#151-the-exact-module-and-its-operators)
    - [An operator dictionary](#152-an-operator-dictionary)
    - [Boundaries of the present theory](#153-boundaries-of-the-present-theory)
    - [Conclusion](#154-conclusion)

## 1. From translations to operators

### 1.1 The problem solved by a double coset

Books 77 and 82 supplied a totally definite quaternion algebra $D/F$ and compact-open levels in its finite adelic unit group. Book 83 turned those data into the finite module

$$
S(U,W)=\{f:D_f^\times\to W:f(\gamma gu)=\rho(\gamma)f(g)\},
$$

where $\gamma\in D^\times$, $u\in U$, and $W$ carries the algebraic weight. The present problem is to move a form through the finite adelic group without losing its level.

Put $G=D_f^\times$ and $\Gamma=D^\times$. Pure right translation by $a\in G$ is

$$
(R_af)(g)=f(ga).
$$

As Book 83 showed, this has level $aUa^{-1}$, not usually level $U$. Thus a single translation is generally a map between two different automorphic modules. An endomorphism at fixed level must average all the ways in which the translate meets the original level. The double coset $UaU$ records exactly those ways.

This is the first guiding idea of Hecke theory: a double coset is not merely a subset of a group. It is a finite correspondence between two copies of a quotient by $U$. Its left $U$-symmetry makes the output $U$-invariant, while its decomposition into right $U$-cosets tells us which translations must be added.

### 1.2 Finite right-coset sums

Because $U$ is compact and open, the intersection

$$
U\cap aUa^{-1}
$$

is open of finite index in $U$. Consequently $UaU/U$ is finite. Choose a disjoint decomposition into **right** cosets

$$
UaU=\coprod_{r=1}^{d}a_rU.
$$

The number of summands is

$$
d=[U:U\cap aUa^{-1}].
$$

Indeed, $u\mapsto uaU$ identifies the quotient of $U$ by the stabilizer of $aU$ with $UaU/U$, and the stabilizer is $U\cap aUa^{-1}$.

**Definition 1.1.** The unnormalized double-coset operator attached to $UaU$ is

$$
\boxed{
(T_{UaU}f)(g)=\sum_{r=1}^{d}f(ga_r).}
$$

The use of right cosets is forced by the transformation law of $f$. Replacing $a_r$ by $a_ru_r$ with $u_r\in U$ does not change $f(ga_r)$. A decomposition into left cosets would not have this property: a replacement $a_r\mapsto u_ra_r$ inserts $u_r$ between $g$ and $a_r$, where right $U$-invariance cannot remove it.

The sum, rather than one chosen translation, solves the level problem. For $u\in U$, left multiplication by $u$ permutes the right cosets of $UaU$, so

$$
(T_{UaU}f)(gu)
=\sum_r f(gua_r)
=\sum_r f(ga_r)
=(T_{UaU}f)(g).
$$

This permutation argument is the elementary heart of the construction.

### 1.3 Independence and equivariance

**Proposition 1.2.** The operator $T_{UaU}$ is independent of the chosen right-coset representatives and preserves automorphy, weight, level, and every central-character subspace.

**Proof strategy.** Each assertion comes from a different symmetry. Right $U$-invariance removes changes of representatives; left $U$-stability of the double coset gives the output level; rational left covariance passes term by term; centrality lets central translation commute through every summand.

**Proof.** If $a'_r=a_{\sigma(r)}u_r$ for a permutation $\sigma$ and elements $u_r\in U$, then

$$
\sum_r f(ga'_r)=\sum_r f(ga_{\sigma(r)}u_r)
=\sum_r f(ga_{\sigma(r)}),
$$

so the sum is choice-free. The preceding permutation calculation proves right $U$-invariance. For $\gamma\in\Gamma$,

$$
(T_{UaU}f)(\gamma g)
=\sum_r f(\gamma ga_r)
=\rho(\gamma)\sum_r f(ga_r).
$$

Thus the same weight representation occurs. Finally, for $z\in Z_f=\mathbf A_{F,f}^\times$,

$$
R_zT_{UaU}f(g)
=\sum_r f(gza_r)
=\sum_r f(ga_rz)
=T_{UaU}R_zf(g),
$$

because $z$ is central. Hence the operator preserves the $\chi_f$-eigenspace for every compatible central character $\chi_f$. $\square$

The proof also handles a finite $A$-linear combination of double cosets. No analytic convergence is hidden: compact support modulo $U$ means that only finitely many right cosets occur.

### 1.4 A convention audit

Four nearby formulas are easily confused, so we record the complete convention in one place.

1. Forms transform on the left by $f(\gamma g)=\rho(\gamma)f(g)$.
2. The level acts on the right by $f(gu)=f(g)$.
3. Translation is $R_af(g)=f(ga)$.
4. A double coset is decomposed as $UaU=\coprod a_rU$.

With these choices, ordinary composition satisfies

$$
R_aR_b=R_{ab},
$$

since $(R_aR_bf)(g)=f(gab)$. Notice that this statement uses the convention that operators act on the left of functions: $R_b$ is applied first.

A useful counterexample shows why no piece can be changed in isolation. Suppose $a$ does not normalize $U$ and define the false operator $f\mapsto f(ga)$. Choose $u\in U$ with $a^{-1}ua\notin U$. Then

$$
f(gua)=f(ga(a^{-1}ua))
$$

need not equal $f(ga)$. The output has lost level $U$. Summing the complete double coset repairs precisely this defect.

There is also a correspondence factorization that connects the present definition with the pullback and trace maps of Book 83. Set

$$
U_a=U\cap aUa^{-1}.
$$

Start with a level-$U$ form, translate it by $a$, pull the result back from its conjugate level to the common level $U_a$, and trace to $U$:

$$
S(U,W)\xrightarrow{R_a}S(aUa^{-1},W)
\longrightarrow S(U_a,W)
\xrightarrow{\operatorname{Tr}_{U_a}^{U}}S(U,W).
$$

This composite is $T_{UaU}$. Indeed, representatives for $U/U_a$ turn the trace into $\sum_u f(gua)$, and the elements $ua$ represent $UaU/U$. Thus the right-coset formula and the finite-span construction are the same correspondence written in two languages.

### 1.5 Standing data and the central constraint

The operator formula is short enough to hide which hypotheses make it meaningful. We therefore fix the standing datum once, and later weaken it only explicitly. Let $F$ be totally real, let $D/F$ be totally definite, and put

$$
G=D_f^\times,\qquad \Gamma=D^\times,\qquad Z_f=\mathbf A_{F,f}^\times.
$$

Let $A$ be a commutative coefficient ring, let $W_A$ be a finite $A$-module with the rational weight action $\rho$, and let $U\subset G$ be compact open. If a finite central character is prescribed, it is a homomorphism

$$
\chi_f:Z_f\longrightarrow A^\times
$$

satisfying the two descent conditions

$$
\chi_f(a)=\rho(a)\quad(a\in F^\times),
\qquad
\chi_f|_{U\cap Z_f}=1,
$$

where $\rho(a)$ is scalar on the weight. The form module is

$$
M_A(U,\chi_f)=
\{f:G\to W_A:f(\gamma guz)=\rho(\gamma)\chi_f(z)f(g)\}.
$$

The first condition reconciles rational scalar multiplication on the left with finite scalar multiplication on the right; the second reconciles the level and character laws. Without them the displayed rule may force the space to vanish or, over a ring with torsion, may leave a misleading torsion submodule.

**Proposition 1.3.** Every double-coset operator $T_{UaU}$ preserves $M_A(U,\chi_f)$ whenever its finite sums preserve the lattice $W_A$.

**Proof strategy.** Proposition 1.2 already gives rational covariance and level invariance. The only additional point is the central equation, and centrality lets the scalar pass through every summand.

**Proof.** For $z\in Z_f$,

$$
(T_{UaU}f)(gz)
=\sum_r f(gza_r)
=\sum_r f(ga_rz)
=\chi_f(z)(T_{UaU}f)(g).
$$

All other transformation laws were proved in Proposition 1.2. The stated lattice hypothesis ensures that the sum lies in $W_A$, rather than merely in $W_A\otimes_A\operatorname{Frac}(A)$ when a fraction field is available. $\square$

This formulation separates existence from integrality. Over a field every finite sum is defined. Over a lattice, the correspondence may carry a value through rational weight matrices with denominators. The group-theoretic double coset still exists, but it belongs to the chosen integral operator family only after lattice preservation has been checked.

There is also a useful variance test. If one replaces $a$ by $u_1au_2$ with $u_1,u_2\in U$, the double coset and its operator do not change. If one replaces $a$ by $z a$ with $z\in Z_f$, then

$$
T_{UzaU}=R_zT_{UaU},
$$

and hence on $M_A(U,\chi_f)$ it becomes $\chi_f(z)T_{UaU}$. Thus a central multiple is generally not the same operator before a central character is imposed and is generally a nontrivial scalar multiple afterward.

## 2. The double-coset algebra

### 2.1 Haar measure and convolution

The finite sum is concrete, but an algebra of operators needs a multiplication that remembers multiplicities. Haar measure provides it without case-by-case bookkeeping.

Let $H(G,U;A)$ be the $A$-module of compactly supported, bi-$U$-invariant functions $\phi:G\to A$. Choose a left Haar measure $dx$ normalized by

$$
\operatorname{vol}(U)=1.
$$

The group $G$ is unimodular: each local factor is the group of units of a finite-dimensional central simple algebra, hence is unimodular, and restricted products preserve this property. Define convolution by

$$
\boxed{
(\phi*\psi)(x)=\int_G\phi(y)\psi(y^{-1}x)\,dy.}
$$

Compact support modulo the open subgroup $U$ turns this integral into a finite sum. Associativity follows from Fubini and the substitution $x=yz$. The identity is the characteristic function $\mathbf1_U$, because $\operatorname{vol}(U)=1$.

When $A$ is an arbitrary ring, the integral sign in this formula is algebraic notation rather than an attempt to integrate $A$-valued functions against a real measure. For fixed $x$, the integrand is constant on right $U$-cosets and has finite support, so the normalized integral means the finite sum of its values over those cosets. This defines convolution over $A$ directly. When the coefficients admit ordinary Haar integration, the algebraic sum agrees with the displayed integral.

Every bi-$U$-invariant compactly supported function is a finite $A$-linear combination of characteristic functions $\mathbf1_{UaU}$. Thus the convolution algebra and the free module on compact-open double cosets are the same object after the volume normalization has been fixed.

Bi-invariance is needed on both sides. Right invariance makes the integral a finite sum on right-$U$-invariant functions. Left invariance makes its output right-$U$-invariant: replacing $g$ by $gu$ and then $x$ by $u^{-1}x$ leaves the kernel unchanged. A merely right-$U$-invariant kernel would define a finite integral but not generally an endomorphism of fixed level.

### 2.2 Integral and finite-sum formulas

For $\phi\in H(G,U;A)$ define

$$
(T_\phi f)(g)=\int_G\phi(x)f(gx)\,dx.
$$

If $\phi=\mathbf1_{UaU}$ and $UaU=\coprod_r a_rU$, then

$$
\int_{UaU}f(gx)\,dx
=\sum_r\int_{a_rU}f(gx)\,dx
=\sum_r f(ga_r),
$$

because every right coset has volume $1$. This recovers Definition 1.1 exactly; there is no missing factor of $\operatorname{vol}(U)$.

If instead one chooses Haar measure with $\operatorname{vol}(U)=c$, the same integral is $c$ times the finite sum. When $c$ is represented by a unit in the coefficient ring, one may either divide the integral by $c$ or retain the scaled basis $c^{-1}\mathbf1_{UaU}$. Over an integral ring where that division is unavailable, the finite right-coset sum is the normalization to keep. Confusion between these choices is the common source of apparently contradictory Hecke relations.

The finite-sum definition makes sense over any coefficient ring $A$, without placing a real-valued measure in $A$. Haar integration is a conceptual packaging: every bi-$U$-invariant support occurring here is a finite union of right $U$-cosets, each of normalized volume one. Rational stabilizer factors arise later from quotient mass, not from the integral Hecke action itself.

### 2.3 Composition and structure constants

**Theorem 2.1.** With the preceding convolution convention,

$$
\boxed{T_\phi T_\psi=T_{\phi*\psi}.}
$$

**Proof strategy.** Expand the two integrals and use $z=xy$. The order of $\phi$ and $\psi$ is the point of the calculation.

**Proof.** One has

$$
T_\phi T_\psi f(g)
=\int_G\phi(x)\int_G\psi(y)f(gxy)\,dy\,dx.
$$

For fixed $x$, put $z=xy$. Unimodularity gives $dy=dz$, and the coefficient of $f(gz)$ becomes

$$
\int_G\phi(x)\psi(x^{-1}z)\,dx
=(\phi*\psi)(z).
$$

This proves the formula. $\square$

For double cosets $C=UaU$ and $D=UbU$, write

$$
\mathbf1_C*\mathbf1_D
=\sum_E m(C,D;E)\mathbf1_E.
$$

The nonnegative integers $m(C,D;E)$ count, with the Haar normalization already incorporated, the pairs of right-coset translations whose product lands in a specified right coset of $E$. They are not merely indicators that $E\subset CD$: several pairs may lead to the same output. The operator relation is therefore

$$
T_C T_D=\sum_E m(C,D;E)T_E.
$$

This is why multiplying subsets and then discarding multiplicity gives the wrong Hecke algebra.

For a concrete structure-constant formula, fix $e\in E$. Then

$$
m(C,D;E)
=(\mathbf1_C*\mathbf1_D)(e)
=\operatorname{vol}\{x\in C:x^{-1}e\in D\}.
$$

The set on the right is a union of right $U$-cosets, so its normalized volume is a nonnegative integer. This proves directly that the integral algebra is closed under convolution and that the constant does not depend on the representative $e$.

### 2.4 Semigroups and coefficient lattices

Often one uses only double cosets drawn from a subsemigroup $\Delta\subset G$ containing $U$. The corresponding integral Hecke algebra is the $A$-span of $U\backslash\Delta/U$, provided convolution stays inside $\Delta$. This restriction is useful when a weight lattice is stable under a prescribed collection of transition maps but not under every rational element that could arise from all of $G$.

Over a field $E$, the action above is automatic. Over a ring $A$ with lattice $W_A\subset W_E$, integrality requires more: after rewriting translated class representatives, the rational weight matrices that occur must preserve $W_A$, or their total sums must preserve the automorphic lattice. Book 83 guaranteed stability under the class stabilizers; that alone does not guarantee stability under every Hecke transition. An **integral Hecke datum** therefore consists of $U$, $W_A$, and a double-coset semigroup for which all correspondence maps preserve $S(U,W_A)$.

For the standard operators away from the coefficient characteristic, natural polynomial lattices have this stability. At a coefficient place or for a lattice with denominators, it must be checked rather than inferred from the characteristic-zero action.

### 2.5 Degree, augmentation, and inversion

Three elementary maps on the double-coset algebra anticipate later spectral and adjoint formulas. They are best isolated now because each uses a different operation: counting right cosets, multiplying kernels, and reversing a correspondence.

For a double coset $C=UaU$, define its right degree by

$$
\deg_R(C)=|C/U|=[U:U\cap aUa^{-1}].
$$

The constant function $1$ satisfies

$$
T_C1=\deg_R(C)\,1.
$$

Consequently the map

$$
\varepsilon_R:H(G,U;A)\longrightarrow A,
\qquad
\varepsilon_R(\phi)=\sum_{xU\subset\operatorname{supp}(\phi)}\phi(x)
$$

is an algebra homomorphism. Indeed, applying $T_\phi T_\psi=T_{\phi*\psi}$ to the constant function gives

$$
\varepsilon_R(\phi*\psi)
=\varepsilon_R(\phi)\varepsilon_R(\psi).
$$

For a nonunimodular group, right and left degrees need not agree, and inversion carries one to the other with a modular factor. Here $G$ is unimodular, so inversion preserves the normalized Haar measure and

$$
\deg_R(UaU)=\deg_R(Ua^{-1}U).
$$

One may also prove this by comparing indices:

$$
[U:U\cap aUa^{-1}]
=[U:U\cap a^{-1}Ua],
$$

because conjugation by $a^{-1}$ identifies the first intersection with $a^{-1}Ua\cap U$, while the two indices are related by the equal Haar volumes of $U$ and $aUa^{-1}$.

Define the linear reversal

$$
\phi^\iota(x)=\phi(x^{-1}).
$$

**Proposition 2.2.** Reversal is an involutive anti-automorphism:

$$
(\phi*\psi)^\iota=\psi^\iota*\phi^\iota,
\qquad
(\phi^\iota)^\iota=\phi.
$$

**Proof strategy.** Invert the product variable in convolution and use unimodularity to avoid a modular correction.

**Proof.** At $x$ the left side is

$$
\int_G\phi(y)\psi(y^{-1}x^{-1})\,dy.
$$

Put $z=xy$. Then $y=x^{-1}z$, and left translation preserves measure. The integral becomes

$$
\int_G\psi(z^{-1})\phi(x^{-1}z)\,dz
=\int_G\psi^\iota(z)\phi^\iota(z^{-1}x)\,dz,
$$

which is $(\psi^\iota*\phi^\iota)(x)$. The second identity is immediate. $\square$

Thus degree is the eigencharacter seen by constants, while reversal is the algebraic precursor of adjunction. They should not be conflated: a correspondence can have the same degree as its reverse without being equal to it. The level-prime operators below give the basic counterexample.

## 3. The finite class-set calculation

### 3.1 Transition data

The abstract integral formula becomes a finite matrix on the exact module of Book 83. Choose

$$
G=\coprod_{i=1}^h\Gamma g_iU,
\qquad
\Gamma_i=\Gamma\cap g_iUg_i^{-1},
$$

so that

$$
S(U,W)\cong\bigoplus_{i=1}^hW^{\Gamma_i},
\qquad f\longmapsto(w_i),\quad w_i=f(g_i).
$$

For $UaU=\coprod_{r=1}^d a_rU$, reduce every product $g_i a_r$ back to the chosen class decomposition:

$$
\boxed{
g_i a_r=\gamma_{i,r}g_{j(i,r)}u_{i,r},
\quad
\gamma_{i,r}\in\Gamma,
\quad u_{i,r}\in U.}
$$

Then

$$
(T_{UaU}f)(g_i)
=\sum_{r=1}^d\rho(\gamma_{i,r})w_{j(i,r)}.
$$

Although individual $\gamma_{i,r}$ depend on reductions, the sum does not. If the same product is rewritten using $\gamma'_{i,r}$, the ratio between the two rational factors belongs to the stabilizer of the source component $g_{j(i,r)}$, which fixes $w_{j(i,r)}$.

### 3.2 The block-matrix algorithm

Assume each $W^{\Gamma_i}$ is free and choose an admissible basis. The following algorithm produces the operator matrix.

1. Decompose $UaU$ into right $U$-cosets.
2. For each row index $i$ and each coset representative $a_r$, reduce $g_i a_r$ to $\gamma_{i,r}g_jU$.
3. Apply $\rho(\gamma_{i,r})$ to the $j$th invariant fiber inside the ambient weight module.
4. Add all contributions with output row $i$, and then express their sum in the chosen basis of $W^{\Gamma_i}$.

The total image automatically lies in $W^{\Gamma_i}$ because the correspondence is $U$-invariant; an individual summand need not do so. No averaging projector is needed. If one performs computations in the ambient $W$, invariance of the completed row sum is a useful check on the result. At good stabilizer primes one may project that total with the averaging idempotent, but projecting summands separately changes the correspondence, and inserting the denominator at a bad prime can destroy an otherwise integral calculation.

Changing $g_i$ to $b_i g_i u_i$ conjugates the whole matrix by the block-diagonal change of coordinates $\rho(b_i)$. Changing right-coset representatives changes none of its blocks. Thus the linear endomorphism is canonical while its displayed matrix is not.

At block level, suppose the same product is reduced in two ways:

$$
g_i a_r=\gamma g_j u=\gamma' g_j u'.
$$

Then

$$
\gamma'^{-1}\gamma=g_j u'u^{-1}g_j^{-1}\in\Gamma_j.
$$

It follows that $\rho(\gamma)w_j=\rho(\gamma')w_j$. This is the exact point at which stabilizer invariance in the module of Book 83 enters the Hecke calculation.

### 3.3 Multiplicity and stabilizers

For trivial coefficients, write $B(a)=(b_{ij})$ with column vectors and the convention

$$
(T_{UaU}w)_i=\sum_jb_{ij}w_j.
$$

Then

$$
b_{ij}=\#\{r:j(i,r)=j\},
$$

so every row sum is $d$:

$$
\sum_jb_{ij}=d.
$$

Repeated arrival at the same class is a multiplicity, not a duplicate to be discarded.

An ideal-neighbor calculation often enumerates orbits under $\Gamma_i$ instead of all right cosets. One orbit can contain several translations. If $x$ is a representative point and $H_x\subset\overline\Gamma_i$ is its effective stabilizer, its orbit contributes

$$
[\overline\Gamma_i:H_x]
$$

to the appropriate matrix entry. Counting one per orbit would undercount whenever $H_x\ne\overline\Gamma_i$.

There is a second stabilizer issue. Two distinct translations can give isomorphic target ideals but different rational identifications of their weight fibers. For scalar weight their contributions coincide; for nontrivial $W$ the matrices $\rho(\gamma_{i,r})$ must still be added separately. Thus a weighted Brandt matrix is generally a block matrix, not the scalar neighbor matrix tensored with the identity.

### 3.4 Brandt matrices and graph intuition

When $U=\widehat{\mathcal O}^{\times}$ and $W$ is trivial, $B(a)$ is a **Brandt matrix**. At a split prime with hyperspecial level and $a=\operatorname{diag}(\pi,1)$, its directed edges record index-$q$ neighbors of right ideal classes. Each vertex has $q+1$ outgoing edges, counted with loops and parallel edges.

The graph picture is valuable but incomplete. Stabilizers make the quotient an orbifold graph, so incoming and outgoing raw counts need not match. Central translation can identify the reversed edge with a scalar multiple of the original operator. At level primes, the reverse edge may belong to a different double coset altogether. The mass pairing of the next chapter is what states the correct symmetry.

A toy calculation illustrates multiplicity. Suppose a two-class scalar module receives three translations from every class and reduction gives

$$
g_1a_r\leadsto(g_1,g_2,g_2),
\qquad
g_2a_r\leadsto(g_1,g_1,g_2).
$$

Then

$$
B(a)=
\begin{pmatrix}1&2\\2&1\end{pmatrix},
$$

not the $0$--$1$ adjacency matrix $\bigl(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\bigr)$. Hecke operators count correspondences, not merely incidence.

## 4. Adjoints and mass

### 4.1 Why counting measure is not enough

Reversing a finite correspondence should produce its adjoint. On an honest finite set with no automorphisms, this is ordinary matrix transpose. The quaternionic class set has stabilizers, however, and a class with many automorphisms represents less quotient volume than one with few. The correct pairing must remember that discrepancy.

Let $W$ and $W^\vee$ carry a perfect $\Gamma$-invariant pairing $\langle\ ,\ \rangle_W$. If central characters are present, pair character $\chi$ with $\chi^{-1}$. After removing the common central subgroup, let $e_i=|\overline\Gamma_i|$ be the effective stabilizer order. The mass pairing is

$$
\langle f,h\rangle_U
=\sum_{i=1}^h\frac1{e_i}
\langle f(g_i),h(g_i)\rangle_W.
$$

It is interpreted over a coefficient ring in which the $e_i$ are invertible, or after a common denominator has been cleared. More intrinsically it is quotient integration with compatible Haar measures. The unweighted pairing remains useful integrally, but it does not give the clean inverse-correspondence formula when stabilizers vary.

### 4.2 The inverse-kernel theorem

For a compactly supported kernel define

$$
\phi^\iota(x)=\phi(x^{-1}).
$$

**Theorem 4.1 (adjoint correspondence).** With compatible quotient Haar measure,

$$
\boxed{
\langle T_\phi f,h\rangle_U
=\langle f,T_{\phi^\iota}h\rangle_U.}
$$

In particular,

$$
T_{UaU}^{\,*}=T_{Ua^{-1}U}
$$

between dual coefficient systems and inverse central characters.

**Proof strategy.** Regard the mass sum as integration over the finite quotient groupoid, or equivalently over the full adelic quotient after the common center has been removed and compatible measures have been chosen. Move the translation from the first variable to the second by $g\mapsto gx$. The inverse appears because undoing right translation by $x$ means right translation by $x^{-1}$.

**Proof.** Write $[G]$ for the central or projective quotient just described and express the pairing as quotient integration. Then

$$
\langle T_\phi f,h\rangle
=\int_{[G]}
\int_G\phi(x)\langle f(gx),h(g)\rangle_W,dx,dg.
$$

For fixed $x$, substitute $k=gx$. Right invariance of Haar measure, valid because $G$ is unimodular, gives

$$
\int_{[G]}
\langle f(k),h(kx^{-1})\rangle_W,dk.
$$

Now put $y=x^{-1}$. Inversion preserves Haar measure on a unimodular group, so the inner integral is the action of $\phi^\iota$ on $h$. This proves the claim. $\square$

The orbit--stabilizer formula converts this quotient integral back into the displayed finite mass sum, so no unstated measure on the generally ill-behaved finite-adelic quotient $\Gamma\backslash G$ is being used. With central characters, the factors in the two coefficient systems must cancel. Pairing two forms with the same nonquadratic character bilinearly is not well defined on the quotient.

### 4.3 Central factors and self-adjointness

The phrase “$T_v$ is self-adjoint” is true only after its central normalization is specified. Suppose

$$
Ua^{-1}U=z\,UaU
$$

for a central $z\in Z_f$. Since $z$ commutes with every representative,

$$
T_{Uz aU}=R_zT_{UaU}.
$$

On a central-character subspace with character $\eta$ this becomes

$$
T_{Ua^{-1}U}=\eta(z)T_{UaU}.
$$

Thus on a Hermitian $\chi_f$-space the adjoint factor is $\chi_f(z)$. For the bilinear pairing between $\chi_f$ and $\chi_f^{-1}$, the adjoint acts on the second space and its scalar factor is instead $\chi_f^{-1}(z)$. Exact self-adjointness on one space holds if the inverse double coset equals the original one, or if the intervening central scalar acts trivially there. A rescaled operator may be self-adjoint over a field containing an appropriate square root, but that rescaling changes the integral normalization.

For a Hermitian pairing on one complex character space, the same argument includes complex conjugation. If $\chi$ is unitary, inversion changes $\chi(z)$ to its conjugate inverse as expected. We will state bilinear adjoints between $\chi$ and $\chi^{-1}$ unless a Hermitian structure is explicitly chosen.

At a split hyperspecial place, $a=\operatorname{diag}(\pi,1)$ satisfies

$$
Ka^{-1}K=\pi^{-1}KaK,
$$

because the Weyl matrix in $K$ interchanges the two diagonal entries. Hence

$$
T_v^*=S_v^{-1}T_v,
$$

where $S_v$ is translation by the central scalar $\pi$. On a fixed Hermitian central-character space this is $\chi_f(\pi)^{-1}T_v$. In a bilinear duality the abstract formula is the same, but $S_v^{-1}$ specializes using the inverse character on the second space. On the projective quotient, or after the corresponding unitary normalization, this is the familiar symmetric adjacency operator.

To summarize the exact hypotheses, a characteristic-double-coset operator is self-adjoint on one space when that space carries a nondegenerate invariant Hermitian pairing represented by the mass measure, the inverse double coset equals the original double coset after any central quotient being used, and every central scalar introduced by that equality acts as $1$. If the scalar acts nontrivially, the displayed character factor remains. If the inverse coset is genuinely different, as at Iwahori level, no scalar normalization alone gives self-adjointness.

### 4.4 Weighted matrix symmetry

Let $B=(b_{ij})$ be a scalar Brandt matrix, and suppose the inverse correspondence agrees with the original after a central scalar that acts trivially. Self-adjointness for the mass pairing gives

$$
\boxed{
\frac{b_{ij}}{e_i}=\frac{b_{ji}}{e_j}.}
$$

This is detailed balance for the finite quotient groupoid. It explains why a raw Brandt matrix can fail to be symmetric even though the correspondence is geometrically reversible.

For nontrivial weights, replace $b_{ij}$ by the block $B_{ij}$ and ordinary transpose by the adjoint relative to the weight pairing:

$$
\frac1{e_i}B_{ij}
=\frac1{e_j}B_{ji}^{\dagger}.
$$

If the inverse differs by $z$, the right side receives the corresponding central-character factor. These formulas are powerful audits of a computed matrix. Failure can signal a missing multiplicity, an incorrect stabilizer order, an inverse double coset used on the wrong side, or a Haar normalization changed halfway through.

## 5. The split hyperspecial local algebra

### 5.1 Choosing the split model

Let $v$ be a finite place of $F$ at which $D$ is split and the level is hyperspecial. Write

$$
L=F_v,\qquad \mathcal O=\mathcal O_v,
\qquad \mathfrak p=(\pi),\qquad q=|\mathcal O/\mathfrak p|.
$$

A chosen splitting

$$
\iota_v:D_v^\times\xrightarrow{\sim}\operatorname{GL}_2(L)
$$

is required before matrix notation makes sense. We require it to carry the chosen maximal-order units onto

$$
K=\operatorname{GL}_2(\mathcal O).
$$

Book 77 proved that every automorphism of a quaternion algebra is inner, so two such integral splittings differ by conjugation through the normalizer of $K$. That normalizer is exactly $L^\times K$. Indeed, the elementary-divisor theorem writes a normalizing element as

$$
g=k_1\operatorname{diag}(\pi^a,\pi^b)k_2.
$$

The factors $k_i$ already normalize $K$. Conjugating the upper and lower unipotent matrices with entries in $\mathcal O$ by the diagonal factor shows respectively that $a-b\ge0$ and $b-a\ge0$. Hence $a=b$, so $g\in L^\times K$; the reverse inclusion is immediate. Conjugation by this normalizer preserves all $K$-double cosets used below. Therefore the resulting operators are independent of the compatible splitting, even though their diagonal matrix representatives are not meaningful before a splitting is chosen.

This distinction matters. An arbitrary isomorphism $D_v\cong M_2(L)$ can send the given maximal order to a conjugate maximal order rather than to $M_2(\mathcal O)$. Silently retaining the old $K$ after such a change produces a different level.

### 5.2 Cartan decomposition

The elementary-divisor theorem for pairs of lattices gives

$$
\operatorname{GL}_2(L)
=\coprod_{a\ge b}K
\begin{pmatrix}\pi^a&0\\0&\pi^b\end{pmatrix}K.
$$

**Proof strategy.** Associate to $g$ the lattice $g\mathcal O^2$. Left and right multiplication by $K$ change bases of the target and source lattices. Elementary divisors put their relative position in diagonal form, uniquely up to ordering.

Every diagonal representative factors as

$$
\begin{pmatrix}\pi^a&0\\0&\pi^b\end{pmatrix}
=(\pi I)^b
\begin{pmatrix}\pi^{a-b}&0\\0&1\end{pmatrix}.
$$

Define

$$
A_n=\mathbf1_{K\operatorname{diag}(\pi^n,1)K}
\quad(n\ge0),
\qquad
S=\mathbf1_{K\pi I K}.
$$

Then $A_0=\mathbf1_K$, $S$ is central and invertible under convolution, and every spherical double coset has the form $S^bA_{a-b}$. The spherical algebra is therefore spanned by $S^bA_n$ with $b\in\mathbf Z$ and $n\ge0$.

Uniqueness of $(a,b)$ is visible from two invariants. The determinant valuation is $a+b$, while the distance between the homothety classes of $\mathcal O^2$ and $g\mathcal O^2$ is $a-b$. These determine $a$ and $b$, so the Cartan union is disjoint. The same two invariants will distinguish outward and inward terms in the multiplication recursion.

### 5.3 The first double coset

Put $T=A_1$. A direct row-reduction calculation gives the disjoint right-coset decomposition

$$
K\begin{pmatrix}\pi&0\\0&1\end{pmatrix}K
=
\coprod_{u\in\mathcal O/\pi\mathcal O}
\begin{pmatrix}\pi&u\\0&1\end{pmatrix}K
\;\coprod\;
\begin{pmatrix}1&0\\0&\pi\end{pmatrix}K.
$$

There are $q+1$ terms. Geometrically, they are the $q+1$ index-$q$ sublattices between $\pi\mathcal O^2$ and $\mathcal O^2$, or equivalently the lines in the two-dimensional residue space.

Thus the unnormalized operator is

$$
(T_vf)(g)
=\sum_{u\bmod\pi}
f\left(g\begin{pmatrix}\pi&u\\0&1\end{pmatrix}\right)
+f\left(g\begin{pmatrix}1&0\\0&\pi\end{pmatrix}\right).
$$

On constant functions its eigenvalue is $q+1$. This numerical test distinguishes the unnormalized operator from the common normalization $(q+1)^{-1}T_v$ and from the spectral normalization $q^{-1/2}T_v$.

### 5.4 Multiplication recursion and commutativity

The lattice tree gives the multiplication law. A step of type $A_1$ followed by a radial displacement of type $A_n$ either moves one unit farther from the starting vertex or turns toward it. For $n\ge2$, there is one outward choice along a fixed terminal geodesic and $q$ choices producing the inward relative position. At $n=1$, every one of the $q+1$ backtracks returns to the central homothety class.

Translating this path count into convolution yields

$$
\boxed{T*T=A_2+(q+1)S,}
$$

and, for $n\ge2$,

$$
\boxed{T*A_n=A_{n+1}+qS*A_{n-1}.}
$$

The multiplicities can be read without a slogan. Fix an endpoint at distance $n+1$ from the base vertex. Exactly one first edge lies on its geodesic from the base, so the coefficient of $A_{n+1}$ is one. Fix instead an endpoint of determinant valuation $n+1$ and projective distance $n-1$. There are $q$ first edges that turn toward it when $n\ge2$. For $n=1$, the projective endpoint is the base itself and all $q+1$ first edges backtrack. Determinant valuation two shows that the return term is $S$, not $A_0$.

One can also prove these formulas directly by multiplying the $q+1$ right-coset representatives and sorting the products by elementary divisors. The tree proof explains the coefficients; the matrix proof verifies that central scaling is $S$, not the identity.

These recursions prove commutativity without importing any classification. First,

$$
A_2=T^2-(q+1)S.
$$

Inductively,

$$
A_{n+1}=T A_n-qS A_{n-1}
$$

expresses every $A_n$ as a polynomial in the commuting elements $T$ and $S$. Since every basis element is $S^bA_n$, the whole algebra is generated by $T,S,S^{-1}$ and is commutative.

In fact there is no polynomial relation among these three generators beyond $SS^{-1}=1$. This follows from triangularity with respect to the Cartan basis: the highest Cartan term of $T^nS^b$ is $A_nS^b$ with coefficient one. Hence

$$
H(\operatorname{GL}_2(L),K;A)
\cong A[T,S,S^{-1}]
$$

for every coefficient ring $A$ in this unnormalized integral basis.

## 6. Standard unramified operators

### 6.1 $T_v$ and $S_v$

Return to the global level $U=\prod_wU_w$. At a split hyperspecial place $v$, insert the two local double cosets into the $v$-factor and use $U_w$ elsewhere. We write

$$
T_v=[U\,\iota_v^{-1}(\operatorname{diag}(\pi_v,1))\,U],
$$

$$
S_v=[U\,\pi_v I\,U].
$$

The brackets denote their unnormalized operators as well as the corresponding characteristic functions; context distinguishes them. The scalar operator has one right coset, so

$$
(S_vf)(g)=f(gz_v),
$$

where $z_v$ is the finite idele equal to $\pi_v$ at $v$ and $1$ elsewhere.

Replacing $\pi_v$ by $u\pi_v$ with $u\in\mathcal O_v^\times$ does not change either double coset: $\operatorname{diag}(u,1)$ and $uI$ lie in $K$. Thus $T_v$ and $S_v$ depend on the place and its chosen hyperspecial level, but not on the uniformizer or on the compatible splitting used to display that level as $K$. The idele $z_v$ itself changes by an element of $U\cap Z_f$, which acts trivially for a compatible central character.

### 6.2 Normalized versus unnormalized operators

Our $T_v$ is integral and has degree $q_v+1$. Three rescalings appear naturally:

$$
T_v^{\mathrm{avg}}=(q_v+1)^{-1}T_v,
\qquad
T_v^{\mathrm{sp}}=q_v^{-1/2}T_v,
\qquad
T_v^{(c)}=c_vT_v.
$$

The first preserves constants with eigenvalue $1$ but requires $q_v+1$ to be invertible. The second is adapted to unitary spectral bounds but requires a choice of square root and is rarely integral. The third represents weight-dependent conventions used to match other normalizations.

All relations must be rescaled with the operator. For example, replacing $T$ by $q^{-1/2}T$ changes the recursion coefficients. In this book an undecorated $T_v$ is always the characteristic-double-coset sum with $\operatorname{vol}(K)=1$.

### 6.3 The local Hecke polynomial

The spherical recursion singles out the polynomial

$$
\boxed{
P_v(X)=1-T_vX+q_vS_vX^2.}
$$

Equivalently one may use the monic form

$$
X^2-T_vX+q_vS_v.
$$

On a simultaneous eigenvector $f$ with

$$
T_vf=t_vf,
\qquad S_vf=s_vf,
$$

the scalar polynomial is

$$
1-t_vX+q_vs_vX^2.
$$

Over a splitting extension, write its reciprocal roots as $\alpha_v,\beta_v$:

$$
\alpha_v+\beta_v=t_v,
\qquad
\alpha_v\beta_v=q_vs_v.
$$

These are merely a convenient encoding of two scalars. No local representation or classification is being attached to them here.

If $\chi_f$ is imposed, then $S_v$ acts by $\chi_f(z_v)$. The polynomial becomes

$$
1-t_vX+q_v\chi_f(z_v)X^2.
$$

Forgetting this central-character value changes the determinant term and usually breaks twisting and adjoint formulas later.

The factor $q_v$ comes from the inward multiplicity in the spherical recursion, not from analogy alone. If one replaces $T_v$ by $T_v^{\mathrm{sp}}=q_v^{-1/2}T_v$ and rescales the root variable, the monic polynomial becomes

$$
X^2-T_v^{\mathrm{sp}}X+S_v.
$$

Over a ring containing $q_v^{1/2}$ this carries the same information. The unnormalized polynomial is preferable integrally because neither its operator nor its root variable requires a square-root choice.

### 6.4 An elementary integral Satake description

The recursion can be packaged in a generating series without adjoining $q^{1/2}$. Put $A_0=1$ and $A_1=T$. Then

$$
\boxed{
\sum_{n\ge0}A_nX^n
=\frac{1-SX^2}{1-TX+qSX^2}.}
$$

Indeed, the coefficient of $X^2$ reproduces $A_2=T^2-(q+1)S$, and every higher coefficient reproduces $A_n=TA_{n-1}-qSA_{n-2}$.

This identity is an integral form of the information usually carried by the Satake transform. If a character $\lambda$ of the spherical algebra is given, then all radial eigenvalues are determined from

$$
t=\lambda(T),\qquad s=\lambda(S)
$$

by

$$
\sum_{n\ge0}\lambda(A_n)X^n
=\frac{1-sX^2}{1-tX+qsX^2}.
$$

After adjoining roots $\alpha+\beta=t$ and $\alpha\beta=qs$, this gives a closed formula for every $\lambda(A_n)$. The description explains eigenvalues as two symmetric parameters while remaining valid integrally and without importing the irreducible representation theory reserved for later books.

The commonly normalized Satake transform sends $T$ to $q^{1/2}(X+Y)$ and $S$ to $XY$. Our integral description has absorbed the half-power into the relation $\alpha\beta=qs$. It therefore keeps the operator lattice visible and avoids pretending that $q^{1/2}$ belongs to the coefficient ring.

## 7. From local to global

### 7.1 Restricted tensor operators

The finite adelic group and level are restricted products:

$$
G=\prod_{v<\infty}'D_v^\times,
\qquad U=\prod_{v<\infty}U_v.
$$

A pure tensor kernel $\phi=\otimes_v\phi_v$ has $\phi_v=\mathbf1_{U_v}$ at almost every place. Its global support is compact, and with product measures normalized by $\operatorname{vol}(U_v)=1$ one has

$$
T_\phi=\prod_vT_{\phi_v},
$$

where only finitely many factors differ from the identity. More generally, finite linear combinations of such tensors give the restricted tensor product Hecke algebra.

This construction is canonical before any matrix splitting is chosen. At a split place a compatible splitting merely supplies the familiar names $T_v$ and $S_v$ for intrinsic local double cosets relative to the maximal order.

### 7.2 Commuting at distinct places

If $v\ne w$, an element supported at $v$ commutes in $G$ with an element supported at $w$. Their local Haar integrals also separate. Therefore

$$
T_{v}T_{w}=T_{w}T_{v},
\qquad
T_vS_w=S_wT_v,
\qquad
S_vS_w=S_wS_v.
$$

This argument does not require either local algebra to be commutative. Operators from disjoint factors commute because the restricted product is componentwise. At the same place, commutativity must be proved from the local double-coset algebra and can fail at deeper level.

In kernel notation, if $a_v$ is trivial away from $v$ and $b_w$ is trivial away from $w$, then $a_vb_w=b_wa_v$, and the products of their global double cosets have the same right-coset multiplicities in either order. Thus their kernels commute already in the global convolution algebra; commutation is not merely an accident in its action on one finite module.

### 7.3 The Hecke algebra away from bad places

Choose a finite set $\Sigma$ containing

- every finite place where $D$ is ramified;
- every place where $U_v$ is not hyperspecial;
- every place at which the chosen coefficient lattice or central character is ramified;
- any additional places intentionally excluded from the comparison problem.

The abstract Hecke algebra away from $\Sigma$ is

$$
\mathbb T^{\Sigma,\mathrm{abs}}_A
=A[T_v,S_v,S_v^{-1}:v\notin\Sigma],
$$

interpreted as the restricted tensor product of the local spherical algebras: each element involves only finitely many places. Its canonical action on $S(U,W_A,\chi)$ may have a kernel. The **acting Hecke algebra** is its image in

$$
\operatorname{End}_A(S(U,W_A,\chi)).
$$

Keeping abstract algebra and image distinct prevents an unjustified claim that infinitely many formal generators remain algebraically independent on a fixed finite module.

Central character often makes every $S_v$ a known scalar. One may then generate the acting algebra using the $T_v$ alone together with the coefficient-ring values $\chi_f(z_v)$. Before imposing a central character, the $S_v$ retain genuine information about the finite central action.

### 7.4 Elementary eigensystems

Let $E$ be algebraically closed and let $M=S(U,W_E,\chi)$. A **Hecke eigenvector away from $\Sigma$** is a nonzero $f\in M$ that is a simultaneous eigenvector for all $T_v$ and $S_v$, $v\notin\Sigma$. Its eigensystem is the homomorphism

$$
\lambda_f:\mathbb T^{\Sigma,\mathrm{abs}}_E\longrightarrow E
$$

defined by operator eigenvalues.

For any finite set of commuting operators on a nonzero finite-dimensional space over an algebraically closed field, a common eigenvector exists: take an eigenspace for the first operator, note that all later operators preserve it, and continue. For the infinite commuting family, the finite-dimensional algebra it generates has a common eigenvector by the same argument applied to finitely many algebra generators of its image.

This elementary statement is all we need. Generalized eigenspaces may occur because commuting matrices need not be semisimple. Over a non-algebraically closed field, eigenvectors may appear only after scalar extension. Over an integral ring, an eigensystem is not the same as a direct summand. Localization, congruences, residual systems, and integral generalized eigenspaces belong to Book 85.

### 7.5 A commutativity ledger

The word “commutative” enters at several logically different levels. Recording the source of each instance prevents a spherical theorem from being applied at a level prime.

**Theorem 7.1.** Let $\mathcal P$ be a set of finite places. For each $v\in\mathcal P$, let $\mathcal A_v\subset H(D_v^\times,U_v;A)$ be a commutative subalgebra. Then the subalgebra of the global convolution algebra generated by the embedded $\mathcal A_v$ is commutative. If $\mathcal P$ is infinite, every element still involves only finitely many nonidentity local factors.

**Proof strategy.** Elements at one place commute by hypothesis; elements at different places commute because their coordinates live in different direct factors. Bilinearity then handles finite sums.

**Proof.** It is enough to compare pure local generators. Two from the same $\mathcal A_v$ commute by assumption. If $x_v$ is supported only at $v$ and $y_w$ only at $w\ne v$, then $x_vy_w=y_wx_v$ componentwise, product Haar measure separates their convolutions, and their global kernels commute. Every product contains only finitely many such generators, so reordering is legitimate. $\square$

At a split hyperspecial place we may take

$$
\mathcal A_v=A[T_v,S_v,S_v^{-1}].
$$

At a ramified quaternionic place with maximal compact level we may take the Laurent algebra generated by the valuation step. At a $K_0$-place the entire local algebra is generally unavailable for this theorem because it need not be commutative; one must select and prove commutativity for the particular subalgebra being used.

There are four useful consequences.

1. The spherical operators away from a finite bad set form a commuting family.
2. Any chosen level operator commutes with every operator supported at a different place.
3. Central translations commute with every local algebra, whether or not that algebra itself is commutative.
4. Commutativity in the acting algebra can be larger than commutativity in the abstract algebra, because a commutator may act by zero on a particular module.

The last point is a warning rather than a shortcut. If two noncommuting Iwahori kernels happen to act by commuting matrices on a one-dimensional invariant space, that does not turn the local convolution algebra into a commutative algebra. Abstract relations are proved before passing to an action; extra relations in the action are recorded as kernel relations.

## 8. Primes in the level

### 8.1 $K_0$ and Iwahori geometry

Now let $D_v$ be split but suppose the local level is

$$
I_r=K_0(\mathfrak p^r)
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{GL}_2(\mathcal O):c\in\mathfrak p^r
\right\},
\qquad r\ge1.
$$

For $r=1$, this is an Iwahori subgroup: modulo $\mathfrak p$ it stabilizes the line spanned by the first basis vector. The hyperspecial group remembers one vertex of the lattice tree; the Iwahori remembers an oriented edge; deeper $I_r$ remembers a longer directed lattice chain. Direction is therefore built into level structure before any operator is defined.

The Weyl matrix

$$
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}
$$

lies in $K$ but not in $I_r$. Consequently it can no longer be used inside the level to identify $\operatorname{diag}(\pi,1)$ with $\operatorname{diag}(1,\pi)$. This is the elementary reason that forward and backward operators separate at a level prime.

### 8.2 The $U_v$ decomposition

Put $\alpha=\operatorname{diag}(\pi,1)$. The index calculation

$$
[I_r:I_r\cap\alpha I_r\alpha^{-1}]=q
$$

gives

$$
\boxed{
I_r\alpha I_r
=\coprod_{u\in\mathcal O/\pi\mathcal O}
\begin{pmatrix}\pi&u\\0&1\end{pmatrix}I_r.}
$$

The missing $(q+1)$st hyperspecial coset is not lost accidentally: it points against the orientation fixed by the chain. Define the unnormalized level operator

$$
U_v=[I_r\alpha I_r],
$$

so

$$
(U_vf)(g)
=\sum_{u\bmod\pi}
f\left(g\begin{pmatrix}\pi&u\\0&1\end{pmatrix}\right).
$$

It has degree $q$, and constants have eigenvalue $q$. Some conventions use $\operatorname{diag}(1,\pi)$ instead, or multiply by a weight and norm factor. Those choices define the opposite or a normalized operator; they must not be substituted into the displayed formula without changing every later relation.

The index is visible directly. Conjugating a matrix in $I_r$ by $\alpha$ multiplies its upper-right entry by $\pi$ and divides its lower-left entry by $\pi$. Intersecting again with $I_r$ imposes the one new condition $b\in\pi\mathcal O$; the lower-left condition remains $c\in\pi^r\mathcal O$. Hence the quotient is parametrized by $b\bmod\pi$, producing exactly the $q$ displayed representatives.

For a character on the diagonal of $I_r$ or a more refined $K_0$-type, a double-coset operator is defined only if the character agrees on the two intersection subgroups transported by $\alpha$. Otherwise the translated coefficient system does not descend through the correspondence. In the present scalar level structure, this compatibility is automatic.

### 8.3 Opposite operators and adjoints

The inverse double coset is

$$
I_r\alpha^{-1}I_r.
$$

Multiplying by the central scalar $\pi$ turns $\alpha^{-1}$ into $\operatorname{diag}(1,\pi)$, but the Weyl element needed to return this to $\alpha$ is not in $I_r$. Hence

$$
I_r\alpha^{-1}I_r
\ne \pi^{-1}I_r\alpha I_r
$$

in general. Define

$$
V_v=[I_r\alpha^{-1}I_r].
$$

The mass adjoint relation is exactly

$$
U_v^*=V_v.
$$

Thus $U_v$ is not generally self-adjoint, even after fixing a central character. A Hermitian normalization cannot repair a geometric mismatch between two distinct double cosets; it can only remove a scalar when the cosets already agree up to the center.

The products $U_vV_v$ and $V_vU_v$ need not agree with each other or with a scalar. They count two differently oriented length-two correspondences. Their precise expansions depend on the chosen level subgroup and form part of its local double-coset algebra.

### 8.4 What fails beyond hyperspecial level

The full Iwahori Hecke algebra is already noncommutative. Its two elementary reflection cosets remember the two ends of an oriented edge. If $Q_0,Q_1$ denote their characteristic functions, each satisfies a quadratic relation of the form

$$
(Q_i+1)(Q_i-q)=0,
$$

but $Q_0Q_1$ and $Q_1Q_0$ correspond to different directed galleries. The affine Weyl group is not abelian, and the double-coset algebra retains that order.

This provides a counterexample to the careless slogan “Hecke operators commute.” Operators at distinct places commute. The spherical algebra at one hyperspecial split place is commutative. A selected subalgebra at level may also happen to commute. But the entire local algebra attached to $K_0(\mathfrak p^r)$ need not.

Self-adjointness also changes. Spherical reversal uses an element of $K$ that exchanges endpoints. Iwahori level excludes that element, so reversal produces another operator. Finally, $U_v$ depends more sensitively on orientation and on whether $\alpha$ or $\alpha^{-1}$ was chosen. These are structural changes caused by level, not inconsistent notation.

For $r=1$, the displayed quadratic relation admits a direct count. Let $s$ be either simple affine reflection and put $Q=\mathbf1_{IsI}$. The double coset $IsI$ has $q$ right $I$-cosets. On reducing the finite reflection calculation modulo $\mathfrak p$, multiplication by a second reflection either backtracks or remains in the same nontrivial cell. For a prescribed identity coset there are $q$ backtracking pairs. For a prescribed right coset in $IsI$, there are $q-1$ pairs: all choices except the unique one that backtracks. Therefore

$$
Q^2=q\mathbf1_I+(q-1)Q,
$$

or equivalently

$$
\boxed{(Q+1)(Q-q)=0.}
$$

The reduction is legitimate because the relevant quotient of $I$ is the upper triangular subgroup of $\operatorname{GL}_2(k)$, and the two-cell decomposition consists of that subgroup and its reflection cell. Lifting representatives preserves the number of right cosets. The same count applies to the other affine wall after conjugating the edge and retaining its orientation. The relation does not imply that the two reflection generators commute; alternating products record distinct directed galleries.

### 8.5 Diamond operators at $K_1$-level

The $K_0$ subgroup remembers an oriented residue line but not a chosen generator of its quotient. To retain a residue character one passes to

$$
K_1(\mathfrak p^r)
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K_0(\mathfrak p^r):
d\equiv1\pmod{\mathfrak p^r}
\right\}.
$$

For $r=1$, which is the case used below, lower-right reduction gives an exact sequence

$$
1\longrightarrow K_1(\mathfrak p)
\longrightarrow I
\xrightarrow{\ d\bmod\mathfrak p\ }
k^\times
\longrightarrow1.
$$

Multiplicativity follows because the lower-left entry of either factor vanishes modulo $\mathfrak p$; surjectivity follows from diagonal matrices. The kernel is exactly the displayed $K_1$ subgroup. In particular $K_1(\mathfrak p)$ is normal in $I$.

For $a\in k^\times$, choose a lift $\widetilde a\in\mathcal O^\times$ and set

$$
h_a=\begin{pmatrix}1&0\\0&\widetilde a\end{pmatrix}.
$$

**Definition 8.1.** On forms of local level $K_1(\mathfrak p)$, the diamond operator in our right-translation convention is

$$
\boxed{\langle a\rangle=R_{h_a}.}
$$

This does not depend on the lift. Two lifts differ by an element congruent to $1$ in the lower-right entry, hence by right multiplication with an element of $K_1(\mathfrak p)$. Normality shows that $R_{h_a}$ preserves the level.

**Proposition 8.2.** The diamond operators give a genuine action of $k^\times$:

$$
\langle a\rangle\langle b\rangle=\langle ab\rangle,
\qquad
\langle1\rangle=1,
\qquad
\langle a\rangle^{-1}=\langle a^{-1}\rangle.
$$

They commute with every operator away from $v$, and their mass adjoints are

$$
\langle a\rangle^*=\langle a^{-1}\rangle.
$$

**Proof.** The products $h_ah_b$ and $h_{ab}$ have the same class modulo $K_1(\mathfrak p)$, so the first identity follows from the composition law for right translations. The next two follow formally. Disjoint-place commutativity is Theorem 7.1. The adjoint formula is the inverse-translation theorem of Chapter 4. $\square$

The quotient also explains the relation with central character. The class of $h_a$ modulo $K_1(\mathfrak p)$ is the same as the class of the central matrix $\widetilde a I$, because

$$
h_a^{-1}(\widetilde a I)
=\begin{pmatrix}\widetilde a&0\\0&1\end{pmatrix}
\in K_1(\mathfrak p).
$$

Thus on a fixed central-character space,

$$
\langle a\rangle=\chi_v(\widetilde a)\operatorname{id}.
$$

If no such local character has been imposed, the diamonds retain the finite $k^\times$-action. When $q-1$ is invertible in $A$ and $A$ contains the values of a character $\eta:k^\times\to A^\times$, its eigensummand is cut out by

$$
e_\eta=\frac1{q-1}
\sum_{a\in k^\times}\eta(a)^{-1}\langle a\rangle.
$$

At a coefficient prime dividing $q-1$, this idempotent need not exist; invariants still make sense, but a direct diamond-character decomposition can fail.

### 8.6 $U_v$ and diamond relations

The level operator should preserve every diamond-character block. That assertion depends on our diagonal representatives and is therefore proved, not assumed.

At $K_1(\mathfrak p)$ level retain

$$
\alpha=\begin{pmatrix}\pi&0\\0&1\end{pmatrix}
$$

and define $U_v$ by the double coset $K_1\alpha K_1$. Conjugation by $\alpha$ preserves the lower-right residue, and the same upper-right index calculation as for $I$ gives $q$ right cosets. Moreover $\alpha$ commutes with every $h_a$. Hence

$$
\boxed{U_v\langle a\rangle=\langle a\rangle U_v.}
$$

To verify the equality at kernel level, multiply the support $K_1\alpha K_1$ on either side by $h_a$. Normality gives

$$
h_aK_1\alpha K_1
=K_1h_a\alpha K_1
=K_1\alpha h_aK_1
=K_1\alpha K_1h_a,
$$

and the right-coset multiplicities agree term by term. Consequently $U_v$ restricts to every diamond eigensummand whenever that summand exists.

This commutation does not make the entire $K_1$ algebra commutative. Reflection operators still remember oriented galleries, and coefficient characters can permit some double cosets while excluding others through the intersection compatibility condition. What has been proved is the precise commutative family normally retained at this level: diamonds, the chosen forward $U_v$, central translations, and all operators away from $v$.

## 9. Ramified quaternionic places

### 9.1 The valuation filtration

Let $v$ be a finite place where $D_v$ is the quaternion division algebra over $L=F_v$. There is no matrix splitting. The reduced norm defines a valuation

$$
w_D(x)=\frac12v_L(\operatorname{Nrd}(x)),
$$

whose value group is $\frac12\mathbf Z$. Its nonnegative part is the unique maximal order $\mathcal O_D$, and

$$
K_D=\mathcal O_D^\times=\ker(w_D)
$$

is the unique maximal compact subgroup.

Choose a division uniformizer $\Pi$ with $w_D(\Pi)=1/2$. Then

$$
D_v^\times=\coprod_{n\in\mathbf Z}\Pi^nK_D.
$$

Conjugation preserves the unique maximal order and its unit group, so $K_D$ is normal in $D_v^\times$. Therefore every maximal-level double coset is a single right coset:

$$
K_D\Pi^nK_D=\Pi^nK_D.
$$

This local geometry is a valuation line, not the branching lattice tree of the split algebra.

### 9.2 Uniformizers and the maximal compact

Any two division uniformizers differ by a unit on the right, so their $K_D$-double cosets agree. Let

$$
R_{\Pi}=[K_D\Pi K_D].
$$

It is an invertible one-coset operator, with inverse $R_{\Pi^{-1}}$. The local maximal-level Hecke algebra is therefore

$$
H(D_v^\times,K_D;A)\cong A[Z,Z^{-1}],
$$

where $Z$ represents the valuation step $\Pi K_D$. It is commutative for the elementary reason that $D_v^\times/K_D\cong\frac12\mathbf Z$.

One can choose a cyclic presentation in which $\Pi^2=\pi$, a central uniformizer, although this equality of elements depends on the presentation. Intrinsically, $\Pi^2$ and $\pi$ have the same valuation and therefore differ by an element of $K_D$. Since forms have right level $K_D$, this already gives the choice-free operator identity

$$
R_\Pi^2=S_v.
$$

The stronger element equality $\Pi^2=\pi$ needs the cyclic choice; the double-coset equality does not.

The qualifier matters because $\Pi$ is not central. Although $K_D\Pi K_D$ has one coset, right translation by $\Pi$ can conjugate finer level or coefficient data. Only its square becomes central after the compatible cyclic choice. The maximal-level group-algebra description does not make the half-step itself a central scalar.

### 9.3 The surviving operators

The central scalar operator

$$
S_v=[K_D\pi K_D]
$$

always exists. On a fixed central-character space it acts by $\chi_f(z_v)$. The half-step $R_\Pi$ also exists at maximal compact level and squares to the central step independently of the representative of its valuation coset.

There is no $q+1$-neighbor operator analogous to the split $T_v$. The absence is not a convention: the division algebra has a unique maximal order, so there is no residue projective line of neighboring maximal orders. Attempting to define $T_v$ by silently identifying $D_v^\times$ with $\operatorname{GL}_2(L)$ invents a splitting that does not exist.

If the global central character is fixed, the relation $R_\Pi^2=\chi_f(z_v)$ leaves at most a square-root choice for an eigenvalue of $R_\Pi$. Whether that operator is retained in a chosen global Hecke algebra depends on the arithmetic comparison being made. The central $S_v$ is canonical; a named half-step requires the maximal compact and a uniformizer double coset.

### 9.4 Smaller division-algebra levels

For a smaller compact open $J\subset K_D$, the normality argument can fail: $\Pi J\Pi^{-1}$ need not equal $J$. Then $J\Pi J$ may contain several right cosets, and the local Hecke algebra can become noncommutative. Congruence subgroups defined from two-sided powers of the maximal ideal are normalized by $D_v^\times$, while subgroups carrying additional residue-field character data need not be.

Accordingly, three assertions must be kept separate:

- maximal order gives one valuation coset at each step;
- a normal congruence level retains a group-algebra description;
- an arbitrary smaller level has a genuine correspondence algebra that must be computed from intersections.

The later classification of representations of $D_v^\times$ will explain which invariant spaces these levels detect. Here the double-coset construction needs only the group, its compact open, and finite-index intersections.

## 10. Centers, characters, and twists

### 10.1 The center before imposing a character

On $S(U,W)$ without a fixed central character, every finite idele $z\in Z_f$ gives a translation $R_z$. Since $z$ is central,

$$
R_zT_\phi=T_\phi R_z
$$

for every Hecke kernel. The central translations therefore form a commuting algebra of permutations and weight-compatible scalar maps on the finite class model.

Two central ideles give the same operator when their quotient lies in $F^\times(U\cap Z_f)$, after the rational scalar has been accounted for by the weight action. Thus the central action factors through the finite ray-class-type quotient already isolated in Book 83. Before selecting a character, $S_v$ should be viewed as one of these central permutation operators, not as an unexplained formal variable.

### 10.2 Central-character quotients

On $S(U,W,\chi_f)$ one has

$$
R_z=\chi_f(z)\operatorname{id}.
$$

This turns all central double cosets into known scalars. In particular,

$$
S_v=\chi_f(z_v)
$$

and the unramified polynomial has constant coefficient $q_v\chi_f(z_v)$.

Compatibility with level remains essential. If $z\in U\cap Z_f$, then the double coset $UzU$ is $U$, whose operator is the identity. Therefore the character formula is consistent only when $\chi_f(z)=1$, exactly the condition from Book 83.

Adjoints connect inverse characters. Under the bilinear duality between $\chi_f$ and $\chi_f^{-1}$, $S_v^*=S_v^{-1}$. If one first replaces $S_v$ by the scalar $\chi_f(z_v)$ and then forgets that the other side has inverse character, the adjoint factor appears to have the wrong sign. The operator identity should be established before scalar specialization.

### 10.3 Twisting forms and operators

Let $\psi:F^\times\backslash\mathbf A_F^\times\to E^\times$ be an idele-class character such that $\psi_f\circ\operatorname{Nrd}$ is trivial on the chosen finite level. Define

$$
(\operatorname{Tw}_\psi f)(g)
=\psi_f(\operatorname{Nrd}(g))f(g).
$$

Right level invariance follows from the hypothesis on $\operatorname{Nrd}(U)$. Rational left covariance requires an archimedean check. For $\gamma\in D^\times$, triviality of the global character on the principal idele $\operatorname{Nrd}(\gamma)$ gives

$$
\psi_f(\operatorname{Nrd}(\gamma))
=\psi_\infty(\operatorname{Nrd}(\gamma))^{-1}.
$$

Thus twisting replaces the weight action $\rho$ by

$$
\rho_\psi(\gamma)
=\psi_\infty(\operatorname{Nrd}(\gamma))^{-1}\rho(\gamma).
$$

If $\psi_\infty$ is trivial, the weight is unchanged; otherwise the norm character at infinity must be included. On a central scalar $z$,

$$
\operatorname{Nrd}(z)=z^2,
$$

so twisting changes the central character from $\chi$ to

$$
\chi\psi^2.
$$

For the twisted form to remain in the algebraic category, the archimedean factor used in $\rho_\psi$ must itself have the required algebraic type and the coefficient lattice must be adjusted if necessary. Finite-order twists trivial at infinity avoid this extra issue.

If $UaU$ is a double coset and $\psi_f$ is trivial on $\operatorname{Nrd}(U)$, every right-coset representative has the same $\psi_f$-value $\psi_f(\operatorname{Nrd}(a))$. Hence

$$
T_{UaU}\operatorname{Tw}_\psi
=\psi_f(\operatorname{Nrd}(a))
\operatorname{Tw}_\psi T_{UaU}.
$$

Equivalently, after identifying the two twisted spaces, eigenvalues scale by this factor. At a split unramified place,

$$
t_v\longmapsto\psi_v(\pi_v)t_v,
\qquad
s_v\longmapsto\psi_v(\pi_v)^2s_v.
$$

Thus the two roots of the local Hecke polynomial scale by $\psi_v(\pi_v)$. This is a complete elementary verification of twist compatibility.

### 10.4 Uniformizer dependence revisited

For unramified $\psi_v$, replacing $\pi_v$ by $u\pi_v$ does not change $\psi_v(\pi_v)$ because $\psi_v(u)=1$. At a ramified character place, the hyperspecial operator may not preserve the character type at all; one must refine the level and its coefficient character before speaking of a local $T_v$.

Central idele notation also prevents a global mistake. The element $z_v$ equal to $\pi_v$ at $v$ and $1$ elsewhere is not the diagonal rational element $\pi_v$—a local uniformizer need not even lie in $F$. Its class in

$$
F^\times\backslash\mathbf A_{F,f}^\times/(U\cap Z_f)
$$

is what the character evaluates. Product-formula identities apply only after a genuine global scalar has been inserted at every place.

## 11. Change of level and old images

### 11.1 Pullback and trace as correspondences

Let $U'\subset U$. Pullback and trace are

$$
\operatorname{res}_U^{U'}:S(U,W)\longrightarrow S(U',W),
$$

$$
\operatorname{Tr}_{U'}^Uf(g)
=\sum_{u\in U/U'}f(gu),
$$

where $U/U'$ means right cosets. These maps are the two directions of the finite correspondence

$$
X_{U'}\longrightarrow X_U.
$$

They satisfy

$$
\operatorname{Tr}_{U'}^U\operatorname{res}_U^{U'}
=[U:U']\operatorname{id}.
$$

The map $X_{U'}\to X_U$ need not have constant set-theoretic fiber size because arithmetic stabilizers identify elements of $U/U'$. The trace still has $[U:U']$ summands before passing to classes. Multiplicity along a stabilizer orbit compensates for the smaller visible fiber; this is the level-change analogue of multiplicity in a Brandt matrix.

With separately normalized mass measures at the two levels, pullback and trace are adjoint. With one fixed ambient Haar measure, the ratio $\operatorname{vol}(U')/\operatorname{vol}(U)=[U:U']^{-1}$ must be inserted. We use the separately normalized convention when writing an unadorned adjoint relation.

### 11.2 Degeneracy maps

Right translation creates further maps between levels. If

$$
U'\subset aUa^{-1},
$$

then $R_a f$ has level $aUa^{-1}$ and hence level $U'$. Define

$$
\delta_a=\operatorname{res}_{aUa^{-1}}^{U'}\circ R_a:
S(U,W)\longrightarrow S(U',W).
$$

This inclusion condition is the exact well-definedness test. It is unsafe to declare $R_a$ a degeneracy map merely because $U'$ is “deeper” than $U$; the conjugation direction matters.

For example, let $K=\operatorname{GL}_2(\mathcal O)$ and $I=K_0(\mathfrak p)$. Put

$$
\beta=\operatorname{diag}(1,\pi).
$$

Then

$$
I\subset \beta K\beta^{-1},
$$

so the two standard elementary degeneracy maps are

$$
\delta_0f=f,
\qquad
\delta_1f=R_\beta f.
$$

Choosing $\alpha=\operatorname{diag}(\pi,1)$ instead changes the required translation to an inverse or a central multiple. Both conventions are legitimate; mixing their inclusion tests is not.

### 11.3 Intertwining relations

There is no unconditional same-place commutation law between pullback or trace and arbitrarily chosen double cosets at the two levels. Such an intertwining holds when the two correspondences are obtained by base change from the same local kernel; it can then be proved by expanding both sides into finite right-coset sums. The case used most often is cleaner: away from the places where $U$ and $U'$ differ, the level-change representatives and the Hecke representatives separate as a direct product.

In particular, if $U$ and $U'$ differ only at a place $v$, then for $w\ne v$,

$$
\delta_aT_w=T_w\delta_a,
\qquad
\operatorname{Tr}_{U'}^UT_w
=T_w\operatorname{Tr}_{U'}^U.
$$

At $v$, the relation is computed by composing spans, not by assuming commutation. If $\delta_a$ is viewed as translation followed by pullback, its mass adjoint is trace followed by inverse translation:

$$
\delta_a^*
=R_{a^{-1}}\circ
\operatorname{Tr}_{U'}^{aUa^{-1}},
$$

with the evident interpretation of the target and with a volume factor if one fixed the same Haar measure at both levels.

The compositions $\delta_b^*\delta_a$ are therefore explicit double-coset operators at level $U$. This single identity produces the usual Gram matrix of degeneracy maps and is safer than memorizing formulas whose $q$, central, and index factors vary with normalization.

### 11.4 The elementary old submodule

Given a collection of admissible degeneracy elements $a_1,\ldots,a_m$, define the elementary old image at level $U'$ by

$$
S(U',W)^{\mathrm{old},U}
=\sum_{j=1}^m\delta_{a_j}S(U,W).
$$

For one newly introduced $K_0(\mathfrak p)$ condition, the standard choice is the span of $\delta_0$ and $\delta_1$. This submodule is stable under all Hecke operators away from the changed place by the intertwining relations.

No direct-sum claim is automatic. The two degeneracy images may intersect, their sum may fail to be saturated over an integral ring, and the mass-orthogonal complement may fail to split at primes dividing the determinant of the degeneracy Gram matrix. Defining a new quotient or proving an old/new decomposition requires more algebra than the elementary correspondence construction. The present result is the canonical old **image**, which is all that later integral control arguments may safely use before Book 85.

### 11.5 Adjoint degeneracy maps and the new kernel

An old image points from lower level to higher level. To define newness one needs maps in the reverse direction. A pairing supplies them, but only after its coefficient and measure hypotheses have been fixed.

Let $W_A'$ be paired perfectly with $W_A$ by a $\Gamma$-invariant bilinear form, and pair central characters $\chi_f^{-1}$ and $\chi_f$. Normalize the mass pairing independently at every level, as in Chapter 4. If

$$
U'\subset aUa^{-1},
$$

define

$$
\delta_a^\dagger
=R_{a^{-1}}\circ
\operatorname{Tr}_{U'}^{aUa^{-1}}.
$$

Its domain is the level-$U'$ space with coefficient system $W_A'$ and character $\chi_f^{-1}$; its target is the corresponding level-$U$ space. With one fixed Haar measure at every level, this formula must be multiplied by the relevant volume ratio. The separately normalized mass convention is what makes the displayed formula unscaled.

**Theorem 11.1 (degeneracy adjunction).** Under the preceding hypotheses,

$$
\langle\delta_af,h\rangle_{U'}
=\langle f,\delta_a^\dagger h\rangle_U.
$$

**Proof strategy.** First move pullback across the pairing as trace. Then move translation across as inverse translation.

**Proof.** Put $V=aUa^{-1}$. Since $\delta_a=\operatorname{res}_V^{U'}R_a$, level adjunction gives

$$
\langle\delta_af,h\rangle_{U'}
=\langle R_af,\operatorname{Tr}_{U'}^Vh\rangle_V.
$$

The inverse-translation theorem gives

$$
\langle R_af,k\rangle_V
=\langle f,R_{a^{-1}}k\rangle_U.
$$

Substitution proves the formula. The inverse central characters ensure that central factors cancel in both changes of variables. $\square$

For a family $a_1,\ldots,a_m$, let

$$
\Delta(f_1,\ldots,f_m)=\sum_j\delta_{a_j}f_j,
$$

and define

$$
\Delta^\dagger h
=(\delta_{a_1}^\dagger h,\ldots,
\delta_{a_m}^\dagger h).
$$

The **new kernel relative to this degeneracy family** is

$$
\boxed{M(U')^{\mathrm{new},U}_{\ker}
=\ker(\Delta^\dagger)
=\bigcap_j\ker(\delta_{a_j}^\dagger).}
$$

It lies naturally in the dual coefficient system. If a self-duality identifies the two systems, it is a submodule of the same named form space. Perfectness then gives

$$
\ker(\Delta^\dagger)=(\operatorname{im}\Delta)^\perp.
$$

Without perfectness, orthogonality only forces $\Delta^\dagger h$ into the radical of the lower-level pairing; equality can fail. This is why “new” must name either an adjoint kernel, an orthogonal complement, or a quotient, rather than leaving the choice implicit.

Every operator supported away from the changed places preserves the new kernel. Indeed it commutes with every $\delta_{a_j}$ and with their adjoints, so it carries their common kernel into itself. This conclusion uses only disjoint-place commutativity and therefore remains valid even when the local algebra at the changed place is noncommutative.

### 11.6 The exact two-by-two Gram matrix

The standard one-prime pair is rigid enough that every entry of its Gram matrix can be calculated. Let $v$ be split, let

$$
K=\operatorname{GL}_2(\mathcal O),
\qquad I=K_0(\mathfrak p),
\qquad \beta=\begin{pmatrix}1&0\\0&\pi\end{pmatrix},
$$

and write $q=|k|$. Globally the levels agree away from $v$. Let

$$
\delta_0=\operatorname{res}_K^I,
\qquad
\delta_1=\operatorname{res}_{\beta K\beta^{-1}}^I R_\beta.
$$

To regard adjoints as endomorphisms of the same modules, assume now that $A$ carries an involution, that the weight lattice has a perfect invariant Hermitian pairing, and that the central character is unitary. These hypotheses identify each coefficient system with its Hermitian dual. The mass pairings are again normalized separately at the two levels.

Let $T=T_v$ and $S=S_v$ at the hyperspecial level. Then

$$
T^*=S^{-1}T,
\qquad S^*=S^{-1}.
$$

**Theorem 11.2 (one-prime Gram matrix).** For

$$
\Delta=(\delta_0,\delta_1):M(K)^{\oplus2}\longrightarrow M(I),
$$

one has

$$
\boxed{
\Delta^*\Delta
=
\begin{pmatrix}
q+1&T\\
S^{-1}T&q+1
\end{pmatrix}.}
$$

**Proof strategy.** The diagonal entries are covering degrees. Each off-diagonal composition traces one translated endpoint of the local edge back to the hyperspecial vertex, producing the spherical double coset or its inverse.

**Proof.** Since $[K:I]=q+1$,

$$
\delta_0^*\delta_0
=\operatorname{Tr}_I^K\operatorname{res}_K^I
=(q+1)\operatorname{id}.
$$

Translation identifies $K$ with $\beta K\beta^{-1}$, and $[\beta K\beta^{-1}:I]=q+1$, so the same calculation gives

$$
\delta_1^*\delta_1=(q+1)\operatorname{id}.
$$

For the first cross term,

$$
\delta_0^*\delta_1
=\operatorname{Tr}_I^K R_\beta.
$$

Representatives for $K/I$ give the $q+1$ right $K$-cosets of $K\beta K$, because

$$
K\cap\beta K\beta^{-1}=I.
$$

Thus $\delta_0^*\delta_1=T_{K\beta K}=T$. Taking adjoints gives

$$
\delta_1^*\delta_0=T^*=S^{-1}T.
$$

These are the four entries. $\square$

On a simultaneous lower-level eigenspace with $T=t$ and $S=s$, the Gram matrix specializes to

$$
\begin{pmatrix}
q+1&t\\s^{-1}t&q+1
\end{pmatrix}
$$

and has determinant

$$
\boxed{d_v=(q+1)^2-s^{-1}t^2.}
$$

If $d_v$ is a unit, the old map is split injective on that eigensummand and the old projector is

$$
e_{\mathrm{old}}
=\Delta(\Delta^*\Delta)^{-1}\Delta^*.
$$

The inverse Gram matrix is

$$
(\Delta^*\Delta)^{-1}
=d_v^{-1}
\begin{pmatrix}
q+1&-t\\-s^{-1}t&q+1
\end{pmatrix}.
$$

If $A$ is a domain and $d_v$ is nonzero but not a unit, the generic old space splits while the integral old image need not. If $d_v=0$, the Gram operator is singular, but this alone does not force the two degeneracy maps to be dependent: for an indefinite Hermitian form, their image can contain a nonzero vector orthogonal to the whole old image. Dependence follows when the specialized mass pairing is positive definite, because then

$$
\ker(\Delta^*\Delta)=\ker(\Delta).
$$

Thus invertibility of $d_v$, integral noninvertibility of $d_v$, and vanishing of $d_v$ are distinct phenomena; in the last case one must record the definiteness hypothesis before inferring dependence.

When the central scalar acts trivially, $S=1$ and the Gram matrix becomes the familiar symmetric matrix

$$
\begin{pmatrix}q+1&T\\T&q+1\end{pmatrix}.
$$

Removing $S^{-1}$ without that hypothesis is an error, not a harmless simplification.

### 11.7 The level operator on the old image

The Gram matrix controls splitting. A different two-by-two matrix explains the local Hecke polynomial. Retain the same $K$, $I$, and $\beta$, and put

$$
\alpha=\begin{pmatrix}\pi&0\\0&1\end{pmatrix}.
$$

Let $U_v=[I\alpha I]$ be the forward level operator of Chapter 8. The spherical double coset has right-coset decomposition

$$
K\alpha K
=\coprod_{u\in k}
\begin{pmatrix}\pi&u\\0&1\end{pmatrix}K
\;\coprod\;\beta K.
$$

The first $q$ representatives are exactly those of $I\alpha I$.

**Theorem 11.3 (old-space companion matrix).** The intertwining identity

$$
\boxed{
U_v\Delta
=\Delta
\begin{pmatrix}
T&qS\\
-1&0
\end{pmatrix}}
$$

holds as an equality of maps $M(K)^{\oplus2}\to M(I)$. Equivalently,

$$
U_v\delta_0=\delta_0T-\delta_1,
\qquad
U_v\delta_1=q\delta_0S.
$$

**Proof strategy.** The first identity separates the missing backward coset from the spherical sum. In the second, multiplying every forward representative by $\beta$ collapses it to the same central translation modulo $K$.

**Proof.** For $f\in M(K)$, the spherical decomposition gives

$$
\delta_0Tf
=U_v\delta_0f+\delta_1f,
$$

which is the first formula. Write

$$
r_u=\begin{pmatrix}\pi&u\\0&1\end{pmatrix}.
$$

Then

$$
r_u\beta
=\begin{pmatrix}\pi&u\pi\\0&\pi\end{pmatrix}
=\pi I\begin{pmatrix}1&u\\0&1\end{pmatrix}.
$$

The final matrix lies in $K$. Since $f$ has right level $K$, every one of the $q$ summands in $U_v\delta_1f$ equals $Sf$. Hence

$$
U_v\delta_1f=q\delta_0Sf.
$$

Combining the two column identities gives the matrix formula. $\square$

Because $T$ and $S$ commute, the companion matrix satisfies

$$
\begin{pmatrix}T&qS\\-1&0\end{pmatrix}^2
-T\begin{pmatrix}T&qS\\-1&0\end{pmatrix}
+qS I_2=0.
$$

Consequently

$$
\boxed{U_v^2\Delta-U_v\Delta T+q\Delta S=0,}
$$

where $T$ and $S$ act diagonally on the two source copies.

This formula is well typed precisely because $T$ and $S$ act on the two lower-level source copies, while $U_v$ acts on the higher-level target. For a lower-level eigenvector $f$ with eigenvalues $t,s$, the span of $\delta_0f$ and $\delta_1f$ is $U_v$-stable. If those two vectors are independent, the characteristic polynomial on that two-dimensional span is

$$
X^2-tX+qs.
$$

More generally, if the simultaneous $(t,s)$-eigenspace has dimension $d$ and $\Delta$ is injective on its double copy, the characteristic polynomial is $(X^2-tX+qs)^d$.

Thus the same polynomial that encodes the unramified spherical data becomes the actual companion polynomial for the two old directions at Iwahori level. No classification theorem is needed; it is a finite double-coset calculation.

The sign $-1$ and the position $qS$ depend on the chosen forward operator $\alpha$, the second degeneracy element $\beta$, and right translation. Replacing either diagonal matrix by its inverse conjugates or rescales the matrix and changes these entries. The theorem is therefore a convention anchor, not a formula to transplant into another convention unchanged.

### 11.8 Old, saturated old, and new

Over a field, image and span cause few difficulties. Over an integral ring they separate into several objects, each answering a different question. Let $A$ be a domain with fraction field $E$, let $L=M_A(U)$, let $M=M_A(U')$, and let

$$
\Delta:L^{\oplus m}\longrightarrow M.
$$

Define

$$
O=\operatorname{im}(\Delta),
\qquad
O^{\mathrm{sat}}=M\cap(O\otimes_AE),
$$

where the intersection is taken in $M\otimes_AE$. Then $O^{\mathrm{sat}}/O$ is torsion and $M/O^{\mathrm{sat}}$ is torsion-free. The first quotient measures the integral defect of the natural degeneracy lattice; replacing $O$ by its saturation removes precisely that information.

Assume now that $M$ is paired perfectly with its dual partner and let

$$
N=\ker(\Delta^\dagger).
$$

Then $N=O^\perp$. If $A$ is a discrete valuation ring and all modules are finite free, $N$ is saturated because it is the kernel of a map between torsion-free modules. Perfectness identifies $N$ with the dual of $M/O^{\mathrm{sat}}$: a functional represented by $n\in N$ vanishes on $O$, hence on $O^{\mathrm{sat}}$, and every functional on the torsion-free quotient extends after choosing a free splitting. Thus the adjoint kernel is the dual of the saturated new quotient, not generally a complement to the unsaturated old image.

**Theorem 11.4 (integral splitting criterion).** Suppose $L^{\oplus m}$ and $M$ are finite projective, the pairings are perfect, the coefficient systems are self-dually identified, and

$$
\mathcal G=\Delta^*\Delta
$$

is an automorphism. Then

$$
M=O\oplus N,
$$

$O$ is saturated, and

$$
e_O=\Delta\mathcal G^{-1}\Delta^*
$$

is the projector onto $O$.

**Proof.** The map $\mathcal G^{-1}\Delta^*$ is a left inverse to $\Delta$, so $\Delta$ is split injective and $O$ is a direct summand, hence saturated. The displayed endomorphism is idempotent because

$$
e_O^2
=\Delta\mathcal G^{-1}(\Delta^*\Delta)
\mathcal G^{-1}\Delta^*=e_O.
$$

Its image is $O$. Its kernel is $N$: one inclusion is immediate, and if $e_Om=0$, applying $\Delta^*$ gives $\Delta^*m=0$. $\square$

The converse need not hold in this form: an old summand may admit some complement even when the complement is not the adjoint kernel, and the chosen Gram operator may fail to be invertible because the restricted pairing on the old summand is imperfect. The theorem characterizes the canonical orthogonal splitting supplied by the chosen pairing.

### 11.9 Several new primes

Adding several pairwise distinct split primes produces no new variance, but it amplifies the bookkeeping. Let $Q=\{v_1,\ldots,v_r\}$ be disjoint from the original level and ramification, and impose $I_{v_i}=K_0(\mathfrak p_{v_i})$ at every $v_i$. For each function

$$
\epsilon:Q\longrightarrow\{0,1\},
$$

take the product of the local degeneracy elements $1$ and $\beta_v$. Distinct local factors commute, so this product is independent of ordering. The resulting $2^r$ maps assemble into

$$
\Delta_Q:M(U)^{\oplus2^r}\longrightarrow M(U_0(Q)).
$$

Every entry of $\Delta_Q^*\Delta_Q$ factors as the product of its one-prime entries. More precisely, if $\epsilon,\eta\in\{0,1\}^Q$, then

$$
(\Delta_Q^*\Delta_Q)_{\epsilon,\eta}
=\prod_{v\in Q}g_v(\epsilon(v),\eta(v)),
$$

where

$$
g_v=
\begin{pmatrix}
q_v+1&T_v\\
S_v^{-1}T_v&q_v+1
\end{pmatrix}.
$$

**Proof strategy.** Compose the two global degeneracy correspondences, then reorder all local factors so that equal places are adjacent. Disjoint-place commutativity separates the result into the product of the one-prime compositions of Theorem 11.2.

**Proof.** The $(\epsilon,\eta)$ entry is $\delta_\epsilon^*\delta_\eta$. Both maps are products of their local factors. Inversion reverses the product in the adjoint, but factors at distinct places commute, so they may be reordered place by place. The factor at $v$ is exactly the $(\epsilon(v),\eta(v))$ entry of the one-prime Gram matrix. Multiplying these commuting factors gives the displayed formula. $\square$

The same factorization gives commuting companion matrices for the $U_v$ on the multi-prime old image. On a simultaneous eigensystem, the possible old refinements are obtained by choosing, at each $v\in Q$, one root of

$$
X^2-t_vX+q_vs_v.
$$

Repeated roots or zero Gram determinants can make the $2^r$ degeneracy directions dependent. Thus the expected count $2^r$ is a generic conclusion under the injectivity hypotheses, not part of the definition of the old image.

## 12. Coefficients, reduction, and torsion

### 12.1 When the action is integral

Let $A$ be a domain, $E$ its fraction field, and $W_A\subset W_E$ a stable weight lattice. The characteristic functions of double cosets have integer structure constants, but that fact alone does not prove that they preserve $S(U,W_A)$. In the class-set formula the operator uses matrices

$$
\rho(\gamma_{i,r}):W_E^{\Gamma_{j(i,r)}}\longrightarrow W_E.
$$

Only the completed sum for a fixed output row is forced to land in $W_E^{\Gamma_i}$. The action is integral precisely when these resulting sums carry the source lattices into the target invariant lattices. A sufficient, stronger condition is that each displayed transition matrix preserve $W_A$; target invariance is still checked after summing.

Clearing denominators proves only that finitely many operators carry one chosen lattice into a common larger lattice; it does not automatically produce a lattice stable under all their iterates. For example, on a one-dimensional $\mathbf Q$-space, multiplication by $p^{-1}$ preserves no lattice commensurable with $\mathbf Z$. A stable Hecke lattice is therefore genuine arithmetic data. For an infinite away-from-$\Sigma$ family, one needs a uniform model, usually supplied by polynomial coefficient lattices and by excluding the coefficient place from the spherical family.

Once stability holds, the matrix algorithm shows that all entries lie in $A$. The trace construction, not division by stabilizer orders, is the primitive integral operation. Mass pairings and averaging projectors may require localizing $A$, but the unnormalized Hecke action itself can remain integral at those primes.

### 12.2 Base change

Suppose an integral Hecke datum is fixed and $A\to B$ is a ring map. There is a natural comparison

$$
S(U,W_A,\chi)\otimes_AB
\longrightarrow S(U,W_A\otimes_AB,\chi_B).
$$

If it is an isomorphism, then every Hecke matrix base-changes entry by entry. Sufficient hypotheses were established in Book 83: flatness for finite effective stabilizers, or invertibility of all stabilizer and central quotient orders for arbitrary base change.

More explicitly, let $M_A=S(U,W_A,\chi)$ and suppose $M_A\otimes_AB\cong M_B$. For any integral double coset $C$, the square

$$
\begin{array}{ccc}
M_A\otimes_AB&\xrightarrow{T_C\otimes1}&M_A\otimes_AB\\
\downarrow&&\downarrow\\
M_B&\xrightarrow{T_C}&M_B
\end{array}
$$

commutes because both routes are given by the same finite right-coset sum. The compatibility is formal once the module itself commutes with base change; the hard point is formation of stabilizer invariants.

### 12.3 Bad stabilizer primes

Let $A$ be a discrete valuation ring with residue field $k$ of characteristic $\ell$. If $\ell$ divides some effective stabilizer order, reduction can create new invariant vectors. Consequently

$$
M_A\otimes_Ak\longrightarrow M_k
$$

may fail to be surjective. The Hecke action on $M_k$ is still canonically defined by the same correspondences, but it can act on vectors that have no integral lift.

This creates two distinct reductions:

1. reduce the characteristic-zero or integral automorphic module and its Hecke matrices;
2. form the automorphic module directly over $k$ and then act by reduced correspondences.

The first maps into the second, but equality requires a base-change theorem. Confusing them can invent a lift of a torsion eigenvector that does not exist.

Mass adjoints are also delicate at bad primes. The denominators $e_i^{-1}$ may not lie in $A$, and the invariant pairing can become degenerate. One may clear a common mass denominator to retain an integral bilinear identity, but clearing denominators can turn a perfect pairing into a nonperfect one. The inverse-double-coset formula remains true on the generic fiber; its integral interpretation must state which scaled pairing is being used.

### 12.4 Reduction of eigendata

Suppose $f\in M_A$ is a simultaneous eigenvector with eigenvalues $t_v,s_v\in A$ and has nonzero reduction $\bar f$. Then

$$
T_v\bar f=\bar t_v\bar f,
\qquad
S_v\bar f=\bar s_v\bar f.
$$

Thus its local polynomial reduces coefficientwise:

$$
1-t_vX+q_vs_vX^2
\longmapsto
1-\bar t_vX+\overline{q_vs_v}X^2.
$$

The converse is false. A mod-$\ell$ eigenvector can arise from new stabilizer invariants or from a generalized eigenspace that does not lift to an eigenline. Even when the module base-changes cleanly, lifting a common eigenvector is subtler than lifting its ambient vector space.

If $q_v=0$ in $k$, the reduced polynomial loses its quadratic term. This does not mean the integral $S_v$ operator vanished; it means the chosen polynomial normalization contains the scalar $q_v$. At a coefficient place one often uses a different local level and a $U_v$ operator instead of putting that place into the away-from-$\Sigma$ spherical family.

These observations locate the boundary of this book. We have a well-defined reduced action and can compare it with integral reduction. Organizing residual eigensystems into maximal ideals, localizing the Hecke algebra, and studying congruences among different characteristic-zero systems are the subject of Book 85.

### 12.5 Stable lattices for an operator family

One stable operator is not the same as a stable algebra. Powers and mixed products can introduce unbounded denominators even when a finite initial list has been cleared individually. The right criterion is boundedness of the whole generated orbit.

Let $A$ be a discrete valuation ring with fraction field $E$, let $V$ be finite-dimensional over $E$, and let $\mathcal B\subset\operatorname{End}_E(V)$ be an $A$-subalgebra. Fix one lattice $L_0\subset V$.

**Proposition 12.1 (stable-lattice criterion).** The following are equivalent.

1. There is an $A$-lattice $L\subset V$ stable under $\mathcal B$.
2. The $A$-module $\mathcal B L_0$ is contained in $\varpi^{-N}L_0$ for some $N$.
3. The $A$-module generated by every word in any fixed generating set of $\mathcal B$, applied to a basis of $L_0$, is bounded in $V$.

When these conditions hold, $L=L_0+\mathcal B L_0$ is a stable lattice.

**Proof strategy.** Commensurability of lattices turns stability into a uniform denominator bound. Conversely, a bounded submodule of a finite-dimensional space over a DVR lies in a finite lattice and is therefore finite.

**Proof.** If $L$ is stable, choose integers $r,s$ with

$$
\varpi^rL_0\subset L\subset\varpi^{-s}L_0.
$$

Then

$$
\mathcal BL_0
\subset\varpi^{-r}\mathcal BL
\subset\varpi^{-r}L
\subset\varpi^{-r-s}L_0,
$$

proving boundedness. Conditions 2 and 3 are the same statement after expanding $\mathcal B$ in words. Conversely, if $\mathcal BL_0\subset\varpi^{-N}L_0$, then

$$
L=L_0+\mathcal BL_0
$$

lies between $L_0$ and $\varpi^{-N}L_0$, so it is a lattice. Since $\mathcal B$ is an algebra, $\mathcal B L\subset L$. $\square$

For the away-from-$\Sigma$ quaternionic action, the natural integral weight model supplies this uniform bound simultaneously at all permitted places. Merely checking the first few Hecke matrices does not. At a coefficient place, a spectral normalization involving $q^{-1/2}$ can fail the criterion even though the unnormalized characteristic-coset action satisfies it.

If two stable lattices $L,L'$ are chosen in the same generic module, they are commensurable. Their reductions can nevertheless differ. The operator algebra therefore acts on a specified lattice, not on an abstract generic vector space with a unique integral structure.

### 12.6 The base-change obstruction

Flat scalar extension behaves well because it preserves the simultaneous kernels defining stabilizer invariants. Reduction does not, and the failure has an exact measure.

Let $A$ be a discrete valuation ring with uniformizer $\varpi$, let $\Gamma_0$ be a finite effective stabilizer, and let $W_A$ be finite free. From

$$
0\longrightarrow W_A
\xrightarrow{\ \varpi\ }W_A
\longrightarrow W_A/\varpi W_A
\longrightarrow0
$$

one obtains

$$
\boxed{
0\longrightarrow
W_A^{\Gamma_0}/\varpi W_A^{\Gamma_0}
\longrightarrow
(W_A/\varpi W_A)^{\Gamma_0}
\longrightarrow
H^1(\Gamma_0,W_A)[\varpi]
\longrightarrow0.}
$$

The connecting map sends a residual invariant $\bar w$ to the cocycle

$$
\gamma\longmapsto
\frac{\gamma w-w}{\varpi},
$$

for any lift $w$. Changing the lift changes this cocycle by a coboundary. Its class vanishes exactly when $\bar w$ lifts, after correction, to an integral invariant. This proves exactness and identifies every new residual invariant.

Summing over class representatives and adjoining the finite central equations gives the same description for the automorphic module. In particular, the cokernel of

$$
M_A/\varpi M_A\longrightarrow M_k
$$

is assembled from stabilizer and central-relation cohomology. If all relevant finite group orders are units in $A$, averaging annihilates positive-degree cohomology and the obstruction vanishes.

Hecke operators act on this exact sequence. They commute with the defining group actions and carry lifts to lifts, so they induce maps on the cohomology terms. A residual eigensystem supported only in the rightmost term is a genuinely new residual system for the chosen lattice; it cannot be declared the reduction of a generic eigenvector.

### 12.7 Abstract and acting algebras under base change

Coefficient change affects the carrier module and the image algebra in different ways. Let $\mathcal H_A$ be an abstract integral double-coset algebra acting on a finite $A$-module $M_A$, and let

$$
\mathbb T_A=\operatorname{im}
(\mathcal H_A\to\operatorname{End}_A(M_A)).
$$

For an $A$-algebra $B$, first consider the base-changed module $M_A\otimes_AB$, whether or not it equals the module formed directly over $B$. The same kernels act, and there is a natural surjection

$$
\mathbb T_A\otimes_AB
\twoheadrightarrow
\operatorname{im}
(\mathcal H_A\otimes_AB
\to\operatorname{End}_B(M_A\otimes_AB)).
$$

It is an isomorphism if $B$ is flat and $M_A$ is finite projective. Flatness preserves the injection $\mathbb T_A\hookrightarrow\operatorname{End}_A(M_A)$, while finite projectivity gives

$$
\operatorname{End}_A(M_A)\otimes_AB
\cong\operatorname{End}_B(M_A\otimes_AB).
$$

Thus no additional kernel appears after extension. For nonflat $B$, a relation among matrices can acquire torsion, so injectivity may fail. Without finite projectivity, scalar extension of the endomorphism module itself requires a separate hypothesis; flatness alone is not being asserted to settle it.

Now compare with the directly formed module $M_B$. If

$$
M_A\otimes_AB\xrightarrow{\sim}M_B,
$$

the preceding statement describes its acting algebra. If this comparison is not an isomorphism, the direct module may contain extra invariant vectors. An abstract kernel that annihilated $M_A$ can act nontrivially on those new vectors, so there need not be a map from $\mathbb T_A\otimes_AB$ onto the direct acting algebra at all. The common abstract double-coset algebra still maps to both, and it is the safe object through which they are compared.

This distinction explains why polynomial identities proved in the abstract local algebra survive every coefficient change, whereas accidental matrix identities on one lattice need not survive passage to a larger residual module.

## 13. A ledger of relations

### 13.1 Why every relation carries hypotheses

The theory now contains several kinds of relation: group-theoretic relations among translations, convolution relations among kernels, matrix relations on old images, and scalar relations after choosing an eigensystem. They are compatible, but they are not interchangeable.

A relation in an abstract local convolution algebra acts on every module of that level. A relation in the global restricted tensor algebra follows from local relations and disjoint supports. A relation in an acting algebra may be stronger because the representation has a kernel. Finally, a scalar eigenvalue relation is only the specialization of one of these operator relations on a simultaneous eigenspace.

The hypotheses attached to a relation answer four questions:

1. Is the place split or division?
2. Is the level hyperspecial, $K_0$, $K_1$, or smaller?
3. Is the operator unnormalized, averaged, or spectrally rescaled?
4. Has a central character already replaced $S_v$ by a scalar?

Changing any answer changes at least one displayed coefficient. The ledger below consolidates the exact versions proved in this book.

### 13.2 Local relations in one table

| Local setting | Generators retained | Exact unnormalized relations | Source of the relation |
|---|---|---|---|
| split, hyperspecial $K$ | $T,S,S^{-1}$ | $SS^{-1}=1$, $T^2=A_2+(q+1)S$, $TA_n=A_{n+1}+qSA_{n-1}$ for $n\ge2$ | lattice distance and path counting |
| split, hyperspecial $K$ | $T,S,S^{-1}$ | $H(G,K;A)=A[T,S,S^{-1}]$ | triangular Cartan support |
| split, Iwahori $I$ | a simple reflection $Q$ | $(Q+1)(Q-q)=0$ | two-cell reflection count |
| split, $K_0(\mathfrak p^r)$ | forward $U$ | $\deg(U)=q$, $U^*=V$ | oriented-chain cosets and inversion |
| split, $K_1(\mathfrak p)$ | $U,\langle a\rangle$ | $\langle a\rangle\langle b\rangle=\langle ab\rangle$, $U\langle a\rangle=\langle a\rangle U$ | normal quotient and diagonal commutation |
| division, maximal $K_D$ | $R_\Pi,R_\Pi^{-1}$ | $R_\Pi R_\Pi^{-1}=1$, $R_\Pi^2=S$ | normality of $K_D$ and valuation |

Every row has a boundary. The spherical polynomial algebra does not describe an Iwahori algebra. The reflection quadratic does not assert commutativity between the two affine reflections. The formula $R_\Pi^2=S$ uses maximal division level; a smaller nonnormal level can split the one-coset translation into a genuine correspondence.

The adjoint ledger is similarly short:

$$
[UaU]^*=[Ua^{-1}U],
\qquad
T^*=S^{-1}T,
\qquad
U^*=V,
\qquad
\langle a\rangle^*=\langle a^{-1}\rangle.
$$

All four formulas use compatible mass measure. The first is universal in the unimodular setting; the remaining three are its specializations. Only after a self-dual Hermitian coefficient system has been fixed do they become adjoints on one named space.

### 13.3 Global polynomial families

At every split hyperspecial place outside $\Sigma$, define

$$
P_v(X)=1-T_vX+q_vS_vX^2.
$$

The coefficients for different $v$ commute, so for any finite set $Q$ the product

$$
P_Q(X)=\prod_{v\in Q}P_v(X)
$$

is unambiguous. This product is merely a convenient simultaneous package; it is not a claim that places share one root variable in a deeper local theory.

On an eigensystem $\lambda$, one obtains

$$
P_{v,\lambda}(X)
=1-\lambda(T_v)X
+q_v\lambda(S_v)X^2.
$$

If a central character is fixed, $\lambda(S_v)=\chi_f(z_v)$. If the eigensystem is twisted by an unramified character $\psi$, then

$$
\lambda(T_v)\mapsto\psi_v(\pi_v)\lambda(T_v),
\qquad
\lambda(S_v)\mapsto\psi_v(\pi_v)^2\lambda(S_v),
$$

so the reciprocal roots are both multiplied by $\psi_v(\pi_v)$. This verifies compatibility of the linear and quadratic coefficients with their respective degrees.

At a newly imposed Iwahori level, Theorem 11.3 gives the well-typed correspondence relation

$$
U_v^2\Delta_v-U_v\Delta_vT_v
+q_v\Delta_vS_v=0.
$$

This is a relation of correspondences from the lower-level double copy to the higher-level space. It becomes a polynomial identity on the old image when the lower-level coefficients are specialized or when the commuting source action has been transported through an injective $\Delta_v$. It is not asserted on the entire higher-level space.

### 13.4 Relations in the abstract and acting algebras

Let

$$
\rho:\mathbb T_A^{\Sigma,\mathrm{abs}}
\longrightarrow\operatorname{End}_A(M_A)
$$

be the canonical action. The abstract algebra has exactly the universal local and disjoint-place relations used in its construction. The acting algebra is

$$
\mathbb T_A^{\Sigma}=\rho(\mathbb T_A^{\Sigma,\mathrm{abs}})
\cong
\mathbb T_A^{\Sigma,\mathrm{abs}}/\ker\rho.
$$

Since $M_A$ is finite, the acting algebra is finite as an $A$-module whenever $A$ is Noetherian and $M_A$ is finite. The infinitely many abstract generators therefore satisfy additional relations in this particular action. Those relations may depend on the weight, level, central character, and coefficient ring.

**Proposition 13.1.** Suppose $A$ is a domain, $M_A$ is torsion-free, and an abstract operator $h$ acts as zero on $M_A$. Then it acts as zero on the generic fiber. The converse holds if $M_A$ is an $A$-lattice in the generic module. It need not act as zero on a directly formed residual module when base change fails.

**Proof.** The first statement follows by tensoring the zero map with the fraction field. For the converse, if $h$ vanishes after tensoring, then $h(m)$ is torsion for every $m\in M_A$; torsion-freeness forces $h(m)=0$. The final warning is the phenomenon of Section 12.7: a direct residual module may contain vectors outside the reduction of $M_A$. $\square$

Thus a proof of commutativity or a polynomial identity should be placed as high as its evidence permits. A double-coset count proves an abstract relation. A finite matrix calculation proves an acting relation. An eigenvalue calculation proves only a scalar specialization. Keeping this hierarchy visible makes later congruence arguments dependable.

## 14. Examples over $\mathbf Q$

### 14.1 The one-class Hurwitz order

Let

$$
D=(-1,-1)_{\mathbf Q}
$$

and let $\mathcal H$ be the Hurwitz maximal order. Its finite ramification is $\{2\}$ and its right ideal class set has one element. At maximal level

$$
U=\widehat{\mathcal H}^{\times},
\qquad
S(U,A)=A
$$

for trivial weight. For every odd prime $p$, choose an integral splitting

$$
D_p^\times\cong\operatorname{GL}_2(\mathbf Q_p),
\qquad U_p\cong\operatorname{GL}_2(\mathbf Z_p).
$$

The operator $T_p$ has $p+1$ right cosets. Since there is only one global class and the coefficient is trivial, every translate returns to the same basis vector. Hence its Brandt matrix is

$$
B_p=(p+1).
$$

Similarly $S_p=(1)$ on the unrestricted scalar one-class space. With a specified central character it is the scalar $\chi_f(z_p)$; the trivial scalar space has the compatible trivial value.

The local polynomial on the constant vector is therefore

$$
1-(p+1)X+pX^2=(1-X)(1-pX).
$$

This factorization is an elementary consequence of neighbor counting. It also reminds us that the one-dimensional norm-character part has not disappeared merely because the algebra is definite.

For a nontrivial weight $W$, the space is $W^{\mathcal H^\times}$ rather than one-dimensional. Each of the $p+1$ returns carries a rational transition matrix, so $T_p$ need not act as $(p+1)$ times the identity. Class number one simplifies the class index, not the weight action.

### 14.2 A two-class level-three model

Keep the Hurwitz algebra, but at $3$ take the principal congruence subgroup

$$
U(3)_3=\ker(\operatorname{GL}_2(\mathbf Z_3)
\to\operatorname{GL}_2(\mathbf F_3))
$$

and maximal level elsewhere. Book 83 identified

$$
X_{U(3)}\cong\mathbf F_3^\times=\{1,-1\}.
$$

For trivial coefficients the module is $A^2$. Let $\ell\ne2,3$ be prime. Every right-coset representative of $T_\ell$ has determinant idele in the ray class represented by $\ell$ modulo $3$. Thus it sends both source classes through the same multiplication by $\ell$ in $\mathbf F_3^\times$, and there are $\ell+1$ representatives. In the ordered basis $(1,-1)$,

$$
B_\ell=
\begin{cases}
(\ell+1)
\begin{pmatrix}1&0\\0&1\end{pmatrix},
&\ell\equiv1\pmod3,\\
(\ell+1)
\begin{pmatrix}0&1\\1&0\end{pmatrix},
&\ell\equiv-1\pmod3.
\end{cases}
$$

For example,

$$
B_5=6\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad
B_7=8\begin{pmatrix}1&0\\0&1\end{pmatrix}.
$$

The vectors $(1,1)$ and $(1,-1)$ are simultaneous eigenvectors. For $\ell\equiv-1\pmod3$, their eigenvalues are $\ell+1$ and $-(\ell+1)$ respectively. This is a complete elementary eigensystem calculation on a low-level finite class set.

The example also exposes what determinant data can and cannot do. Here determinant distinguishes all classes, so it determines the entire permutation. In a larger quaternionic class set, several ideal classes can have the same reduced-norm class. Norm then predicts only the central or abelian block structure; ideal-neighbor reduction is still needed inside each fiber.

### 14.3 General Brandt matrices

Let $\mathcal O$ be a maximal order in a definite rational quaternion algebra, with right ideal representatives $I_1,\ldots,I_h$. For a prime $p$ away from the discriminant, the $(i,j)$ entry of the scalar Brandt matrix may be computed as the number of index-$p$ right $\mathcal O$-sublattices in the local neighbor family of $I_i$ that are globally equivalent to $I_j$, with all automorphism-orbit sizes restored.

Equivalently, choose adelic representatives $g_i$ and reduce the $p+1$ products $g_i a_r$. This second procedure automatically gets left and right orders correct:

- $g_i\widehat{\mathcal O}$ represents the right ideal;
- rational multiplication on the left gives ideal equivalence;
- $a_r$ acts on the right because the operator is right translation;
- the target stabilizer is the unit group of the target left order.

For trivial central action every row sum is $p+1$. If the projective stabilizer orders are $e_i$, reversibility gives

$$
\frac{b_{ij}}{e_i}=\frac{b_{ji}}{e_j}
$$

after central homothety has been removed. These two tests—row degree and weighted symmetry—catch most enumeration errors.

**Worked three-class pattern.** Suppose $p=2$ is split in a hypothetical definite example with three classes, effective stabilizer orders

$$
(e_1,e_2,e_3)=(1,2,1),
$$

and a self-adjoint projective neighbor operator. Consider

$$
B=
\begin{pmatrix}
1&2&0\\
1&1&1\\
0&2&1
\end{pmatrix}.
$$

Every row sums to $3=p+1$, and

$$
\frac{b_{12}}{e_1}=2
=\frac{b_{21}}{e_2},
$$

would be false: the right side is $1/2$. Thus this cannot be the matrix under our row-output convention. The corrected weighted-reversible matrix

$$
B'=
\begin{pmatrix}
1&1&1\\
2&1&0\\
1&0&2
\end{pmatrix}
$$

has row degree $3$ and satisfies $b'_{ij}/e_i=b'_{ji}/e_j$. The calculation shows why plausible-looking neighbor counts are not enough; stabilizer weights impose additional arithmetic constraints.

### 14.4 A non-self-adjoint level operator

At a split prime $p$ with $K_0(p)$ level, the operator

$$
U_p=[K_0(p)\operatorname{diag}(p,1)K_0(p)]
$$

has $p$ forward cosets. Its adjoint is the inverse double coset

$$
V_p=[K_0(p)\operatorname{diag}(p^{-1},1)K_0(p)].
$$

Although multiplication by $p$ converts the inverse diagonal matrix to $\operatorname{diag}(1,p)$, this is not the original double coset because the Weyl matrix does not preserve the oriented level. Hence no central-character scalar turns $V_p$ into $U_p$ in general.

On a finite class model, $U_p$ gives a directed $p$-regular correspondence and $V_p$ gives its mass-weighted reverse. A raw matrix can therefore be triangular or otherwise visibly nonsymmetric without error. Demanding ordinary symmetry would erase the orientation that $K_0(p)$ was introduced to remember.

## 15. The canonical action

### 15.1 The exact module and its operators

We now assemble the construction on precisely the modules produced in Book 83. Fix:

- a totally real field $F$;
- a totally definite quaternion algebra $D/F$;
- a compact open $U=\prod_vU_v\subset D_f^\times$;
- an algebraic weight lattice $W_A$;
- a compatible central character $\chi$;
- an integral double-coset semigroup $\Delta$ preserving the lattice.

The exact automorphic module is

$$
M_A=S(U,W_A,\chi_f)
\subset
\bigoplus_{i=1}^hW_A^{\Gamma_i},
$$

with the finite central equations from Book 83 imposed. For every $a\in\Delta$, the canonical action is

$$
\boxed{
[UaU]f(g)=
\sum_{a_rU\subset UaU}f(ga_r).}
$$

It is independent of all representatives, respects the central equations, composes by convolution, and becomes an explicit finite block matrix through

$$
g_i a_r=\gamma_{i,r}g_{j(i,r)}u_{i,r}.
$$

This formula is the promised endpoint. It defines the global Hecke action before eigenvectors are chosen and before the image algebra is localized. At unramified split hyperspecial places it supplies commuting $T_v,S_v$ and the polynomial $1-T_vX+q_vS_vX^2$. At level and division places it supplies exactly the double-coset operators permitted by the local group and compact open.

### 15.2 An operator dictionary

| Symbol or construction | Exact correspondence | Essential convention | Later comparison datum |
|---|---|---|---|
| $R_a$ | $f(g)\mapsto f(ga)$ | level becomes $aUa^{-1}$ | translation or degeneracy map |
| $[UaU]$ | sum over $UaU/U$ | right cosets, no averaging | integral Hecke operator |
| $\phi*\psi$ | $\int\phi(y)\psi(y^{-1}x)dy$ | $\operatorname{vol}(U)=1$ | composition law |
| class matrix | $g_i a_r=\gamma_{i,r}g_j u$ | row $i$ is output | Brandt or weighted Brandt matrix |
| adjoint | $[UaU]^*=[Ua^{-1}U]$ | mass pairing, dual character | duality relation |
| $T_v$ | $K\operatorname{diag}(\pi,1)K$ | unnormalized, degree $q_v+1$ | trace-like coefficient |
| $S_v$ | central $K\pi I K$ | one coset | central-character or determinant coefficient |
| $P_v(X)$ | $1-T_vX+q_vS_vX^2$ | integral spherical normalization | unramified comparison polynomial |
| $U_v$ | $K_0(\mathfrak p^r)\operatorname{diag}(\pi,1)K_0(\mathfrak p^r)$ | oriented, degree $q_v$ | level-prime operator |
| $V_v$ | inverse double coset of $U_v$ | generally distinct from $U_v$ | mass adjoint |
| $\langle a\rangle$ | right translation by $\operatorname{diag}(1,\widetilde a)$ at $K_1$-level | genuine $k_v^\times$-action | diamond character |
| $R_\Pi$ | division-uniformizer coset | maximal compact, one coset | ramified-place valuation step |
| $\operatorname{res}$ | forget some invariance | deeper group is smaller | level pullback |
| $\operatorname{Tr}$ | sum over $U/U'$ | unnormalized right-coset trace | level corestriction |
| $\delta_a$ | $R_a$ then pullback | require $U'\subset aUa^{-1}$ | degeneracy map and old image |
| $\Delta^*\Delta$ | matrix of adjoint degeneracy compositions | mass pairing and self-duality fixed | old/new splitting obstruction |
| old $U_v$ matrix | $\left(\begin{smallmatrix}T_v&q_vS_v\\-1&0\end{smallmatrix}\right)$ | $\alpha=\operatorname{diag}(\pi,1)$ and $\beta=\operatorname{diag}(1,\pi)$ | old refinement polynomial |
| twist by $\psi$ | multiply by $\psi_f\circ\operatorname{Nrd}$ | adjust the infinite weight; trivial on level norm | $t_v\mapsto\psi_v(\pi_v)t_v$ |

Several entries deliberately retain both an operator and its normalization. In deformation comparisons, $T_v$ and $S_v$ will be matched with two coefficients of a degree-two characteristic polynomial. The factor $q_v$ in $P_v$ is part of that dictionary. Changing $T_v$ by $q_v^{-1/2}$ without changing the polynomial would change the comparison problem.

### 15.3 Boundaries of the present theory

The construction gives simultaneous eigenvalues but does not classify the local objects they might encode. Principal series, special representations, supercuspidal representations, conductors, and newvectors require the local representation theory developed later. Likewise, the half-step at a division place has been described as a double coset, not classified through irreducible representations of $D_v^\times$.

The acting integral Hecke algebra has also been defined but not localized. We have not asserted that an eigensystem lifts, that two eigenvectors are congruent, that an old quotient splits, or that the module is free after localization. Those are precisely the integral questions of Book 85.

What has been proved is independent of those later structures:

- every permitted compact-open double coset acts canonically;
- its action is computable on the finite stabilizer model;
- convolution gives composition with exact multiplicity;
- inverse double cosets give mass adjoints;
- spherical split places give a direct, integral, commutative algebra;
- distinct places give commuting operators;
- level and ramified places retain their genuine asymmetry;
- central characters, twists, level change, and coefficient change obey explicit formulas.

### 15.4 Conclusion

A Hecke operator is the algebraic shadow of a finite correspondence. Starting from a single right translation reveals why the correspondence is needed: translation usually changes level. The compact-open double coset collects every translate required to return to the original level, and its finite right-coset decomposition turns that collection into an integral sum. Haar convolution then records how correspondences compose, including the multiplicities that set-theoretic multiplication forgets.

On a totally definite quaternion algebra, this action is completely finite. Class representatives turn an operator into reductions

$$
g_i a_r=\gamma_{i,r}g_j u,
$$

so every entry is an explicit weight map and every scalar matrix entry is a neighbor count. Stabilizers are not a nuisance to be suppressed: they dictate orbit multiplicities, mass denominators, and weighted adjoint symmetry. At primes dividing their orders they also explain why reduction can produce genuinely new vectors.

The local geometries are now sharply separated. A split hyperspecial place sees the regular lattice tree; its radial correspondences satisfy

$$
T^2=A_2+(q+1)S,
\qquad
TA_n=A_{n+1}+qSA_{n-1},
$$

and these relations prove commutativity directly. They package every spherical eigenvalue into

$$
1-T_vX+q_vS_vX^2.
$$

A $K_0$ level remembers orientation, replacing $q+1$ undirected neighbors by $q$ forward ones and separating an operator from its adjoint. A ramified quaternionic place has no lattice tree at all: maximal level sees a valuation line and a one-coset uniformizer step. These differences are mathematical structure, not notational variation.

Globally, restricted products make operators at distinct places commute. Central characters specialize scalar translations, norm twists rescale the two polynomial coefficients in the expected degrees, and pullback, trace, and translated degeneracy maps build old-level images by finite correspondences. The result is a canonical Hecke action on the exact integral quaternionic modules of Book 83, with every choice and normalization exposed. This is the operator language needed for the next comparison: a finite automorphic module, an integral commuting family away from bad places, precise operators at the remaining places, and a local polynomial whose coefficients can be placed beside deformation-theoretic trace and determinant data.

At one new split prime, the two endpoints of the local edge produce a completely explicit old module. Its Gram matrix records whether the natural integral image splits, while the forward level operator acts through the companion matrix of $X^2-T_vX+q_vS_v$. Passing from $K_0$ to $K_1$ exposes the finite diamond action and its possible failure to decompose at primes dividing $q_v-1$. These facts connect the spherical algebra, level orientation, adjunction, and integral coefficient theory in one calculation.

The final lesson is that no single adjective replaces the hypotheses. “Commuting” depends on the place and selected local subalgebra; “self-adjoint” depends on inversion, central scalars, pairing, and measure; “old” depends on a degeneracy family; “new” depends on a kernel, complement, or quotient; and “reduction” depends on whether invariants commute with base change. Once those choices are stated, every operator is a finite correspondence, every relation is a finite count, and every integral defect is visible in an explicit kernel, cokernel, or matrix determinant.
