# Cyclic Base Change for $\mathrm{GL}_2$

## Contents

1. [The global restriction problem](#1-the-global-restriction-problem)
   - [From prescribed local representations to an automorphic object](#11-from-prescribed-local-representations-to-an-automorphic-object)
   - [Standing notation](#12-standing-notation)
   - [The theorem we are trying to earn](#13-the-theorem-we-are-trying-to-earn)
   - [A first counterexample to placewise reasoning](#14-a-first-counterexample-to-placewise-reasoning)
2. [Norm characters and the expected lift](#2-norm-characters-and-the-expected-lift)
   - [Why a finite group of characters controls the fibers](#21-why-a-finite-group-of-characters-controls-the-fibers)
   - [Localization of norm characters](#22-localization-of-norm-characters)
   - [The expected components over a decomposed place](#23-the-expected-components-over-a-decomposed-place)
   - [Central characters and the norm direction](#24-central-characters-and-the-norm-direction)
   - [The unramified prediction](#25-the-unramified-prediction)
3. [Galois action and twisted conjugacy](#3-galois-action-and-twisted-conjugacy)
   - [Why an ordinary trace over $E$ sees the wrong symmetry](#31-why-an-ordinary-trace-over-e-sees-the-wrong-symmetry)
   - [Twisted conjugacy and its norm](#32-twisted-conjugacy-and-its-norm)
   - [Local twisted conjugacy when a place splits](#33-local-twisted-conjugacy-when-a-place-splits)
   - [Centralizers and measures](#34-centralizers-and-measures)
4. [Matching functions and local traces](#4-matching-functions-and-local-traces)
   - [The problem solved by matching](#41-the-problem-solved-by-matching)
   - [Central covariance](#42-central-covariance)
   - [The unramified fundamental function](#43-the-unramified-fundamental-function)
   - [The local matching trace identity](#44-the-local-matching-trace-identity)
   - [Existence of matching functions](#45-existence-of-matching-functions)
5. [The twisted trace formula in rank two](#5-the-twisted-trace-formula-in-rank-two)
   - [The kernel and the inserted automorphism](#51-the-kernel-and-the-inserted-automorphism)
   - [Why norm characters label identical comparisons](#52-why-norm-characters-label-identical-comparisons)
   - [The geometric expansion](#53-the-geometric-expansion)
   - [The spectral expansion](#54-the-spectral-expansion)
   - [Factorization of a twisted automorphic trace](#55-factorization-of-a-twisted-automorphic-trace)
6. [Comparing the geometric and spectral sides](#6-comparing-the-geometric-and-spectral-sides)
   - [The global matching identity](#61-the-global-matching-identity)
   - [Annihilation of the induced spectrum](#62-annihilation-of-the-induced-spectrum)
   - [Isolating one Hecke eigensystem](#63-isolating-one-hecke-eigensystem)
   - [Recovering a ramified or archimedean component](#64-recovering-a-ramified-or-archimedean-component)
7. [Construction and uniqueness of the lift](#7-construction-and-uniqueness-of-the-lift)
   - [The global existence theorem](#71-the-global-existence-theorem)
   - [Uniqueness needs less data than existence](#72-uniqueness-needs-less-data-than-existence)
   - [Galois invariance](#73-galois-invariance)
   - [Twists, duals, and central characters](#74-twists-duals-and-central-characters)
8. [Unramified Hecke data and global factors](#8-unramified-hecke-data-and-global-factors)
   - [Residue-degree formulas](#81-residue-degree-formulas)
   - [A worked unramified quadratic calculation](#82-a-worked-unramified-quadratic-calculation)
   - [Standard $L$-functions](#83-standard-l-functions)
   - [Conductors are local, not a norm of ideals](#84-conductors-are-local-not-a-norm-of-ideals)
9. [Archimedean components and local types](#9-archimedean-components-and-local-types)
   - [Why infinity belongs in the all-place theorem](#91-why-infinity-belongs-in-the-all-place-theorem)
   - [Real places that stay real](#92-real-places-that-stay-real)
   - [Principal, special, and supercuspidal types at finite places](#93-principal-special-and-supercuspidal-types-at-finite-places)
   - [Local $L$-packets are not an extra ambiguity](#94-local-l-packets-are-not-an-extra-ambiguity)
10. [The cuspidality criterion](#10-the-cuspidality-criterion)
    - [Why self-twists are the only obstruction](#101-why-self-twists-are-the-only-obstruction)
    - [Odd degree](#102-odd-degree)
    - [Quadratic degree and the exceptional isobaric sum](#103-quadratic-degree-and-the-exceptional-isobaric-sum)
    - [Why local splitting is not the criterion](#104-why-local-splitting-is-not-the-criterion)
    - [Self-twist order and orbit size](#105-self-twist-order-and-orbit-size)
11. [Descent, image, and fibers](#11-descent-image-and-fibers)
    - [The global image problem](#111-the-global-image-problem)
    - [Descent of the central character](#112-descent-of-the-central-character)
    - [Descent theorem](#113-descent-theorem)
    - [The precise condition for a prescribed central character](#114-the-precise-condition-for-a-prescribed-central-character)
    - [Fibers of base change](#115-fibers-of-base-change)
    - [A counterexample involving only central characters](#116-a-counterexample-involving-only-central-characters)
12. [Algebraic weights and fields of rationality](#12-algebraic-weights-and-fields-of-rationality)
    - [Why algebraicity is a local restriction statement](#121-why-algebraicity-is-a-local-restriction-statement)
    - [Real-to-complex weight conversion](#122-real-to-complex-weight-conversion)
    - [Cohomological compatibility](#123-cohomological-compatibility)
    - [Algebraic conjugation commutes with base change](#124-algebraic-conjugation-commutes-with-base-change)
    - [Fields of rationality can shrink](#125-fields-of-rationality-can-shrink)
13. [Level and local ramification](#13-level-and-local-ramification)
    - [The level problem is placewise but not degreewise](#131-the-level-problem-is-placewise-but-not-degreewise)
    - [Split and unramified places](#132-split-and-unramified-places)
    - [Ramified places](#133-ramified-places)
    - [Preservation and change of standard types](#134-preservation-and-change-of-standard-types)
    - [A level counterexample](#135-a-level-counterexample)
14. [The exact range of the comparison](#14-the-exact-range-of-the-comparison)
    - [Why the hypotheses belong in the proof](#141-why-the-hypotheses-belong-in-the-proof)
    - [The local representation input](#142-the-local-representation-input)
    - [Three independent global inputs](#143-three-independent-global-inputs)
    - [The strongly cuspidal selector](#144-the-strongly-cuspidal-selector)
    - [A reusable admissibility test](#145-a-reusable-admissibility-test)
15. [Four extended examples](#15-four-extended-examples)
    - [Unramified quadratic base change](#151-unramified-quadratic-base-change)
    - [Real-to-CM behavior](#152-real-to-cm-behavior)
    - [A dihedral representation becoming Eisenstein](#153-a-dihedral-representation-becoming-eisenstein)
    - [An odd-degree cuspidal lift](#154-an-odd-degree-cuspidal-lift)
16. [The cyclic theorem package](#16-the-cyclic-theorem-package)
    - [The complete theorem](#161-the-complete-theorem)
    - [The data passed to cyclic towers](#162-the-data-passed-to-cyclic-towers)
    - [Conclusion](#163-conclusion)

## 1. The global restriction problem

### 1.1 From prescribed local representations to an automorphic object

Let $E/F$ be a cyclic extension of number fields of prime degree $\ell$. At every finite
place, Book 81 attaches to a representation $\pi_v$ in its selected local range and every
$w\mid v$ a local representation

$$
\operatorname{BC}_{E_w/F_v}(\pi_v)
$$

whose parameter is obtained by restriction; Book 107 supplies the real-to-complex and split
archimedean counterparts for the cohomological types used here. The global problem begins where that
local construction ends. If

$$
\pi=\bigotimes_v'\pi_v
$$

is cuspidal automorphic, one can form the formal restricted tensor product

$$
\Pi^{\mathrm{cand}}
=\bigotimes_{w}'\operatorname{BC}_{E_w/F_v}(\pi_v),
\qquad w\mid v.
$$

Nothing in the definition of a restricted tensor product says that it occurs in the
automorphic spectrum over $E$. Automorphy is a global relation among all places, and
cuspidality is the vanishing of a global constant term. This is the central problem
of cyclic base change: prove that the prescribed local tensor is automorphic, decide
whether it is cuspidal or isobaric, and then determine exactly which representations
over $E$ arise in this way.

The solution compares two global trace formulas. On $\mathrm{GL}_2(\mathbb A_F)$ one
uses ordinary conjugacy. On $\mathrm{GL}_2(\mathbb A_E)$ one inserts a generator of
$\operatorname{Gal}(E/F)$ into the trace, so ordinary conjugacy is replaced by twisted
conjugacy. The norm of a twisted class is an ordinary class over $F$. Books 81 and 107 supply
the candidate local representations by restriction of complete parameters. Book 107
proves the matching twisted-character identity in exactly the selected range, and the
geometric and spectral theorems of Books 105--106 turn those local identities into a
global comparison. The present book performs the final automorphic construction and records
precisely where the selected hypothesis is used.

This order is important. We shall not assume global cyclic base change in order to prove its
own trace identity. We recall the already proved geometric, spectral, and local matching
packages with all their hypotheses, compare the two simple trace formulas, and only afterward
name the representation that the comparison produces.

### 1.2 Standing notation

Put

$$
C_K=K^\times\backslash\mathbb A_K^\times
$$

for the idele class group of a number field $K$. Fix a generator
$\sigma$ of

$$
\Gamma=\operatorname{Gal}(E/F),\qquad |\Gamma|=\ell.
$$

For a place $v$ of $F$, choose one place $w\mid v$. Let

$$
g_v=\#\{w:w\mid v\},\qquad
e_v=e(E_w/F_v),\qquad f_v=f(E_w/F_v),
$$

so that

$$
\ell=g_ve_vf_v.
$$

The decomposition group $\Gamma_w$ has order $e_vf_v$. If
$w,\sigma w,\ldots,\sigma^{g_v-1}w$ are the places over $v$, then
$\sigma^{g_v}$ generates $\Gamma_w$. Thus the automorphism used after one circuit
through the local factors is fixed by the global choice of $\sigma$; no independent
local generator is being smuggled into the notation.

Local reciprocity is geometrically normalized: a uniformizer maps to geometric Frobenius,
as in Books 81 and 107. Thus pullback of a Hecke character $\chi$ of $C_F$ to $C_E$ is

$$
\chi_E=\chi\circ N_{E/F},
$$

and corresponds to restriction of the associated one-dimensional Weil character. We call
$\{\alpha_v,\beta_v\}$ the normalized Satake pair of Book 95; when interpreted through
reciprocity it is the geometric-Frobenius pair. Passing to arithmetic Frobenius inverts both
entries and changes no norm direction. Normalized parabolic induction is used throughout.

For a Hecke character $\chi$ of $F$, the twist $\pi\otimes\chi$ means
$\chi\circ\det$. Its central character is $\omega_\pi\chi^2$. The symbol
$\boxplus$ denotes an isobaric sum, not a direct sum inside the cuspidal spectrum.

The word **selected** has a fixed technical meaning. At every finite place, $\pi_v$ is a
determinant character, principal series, special representation, or one of the depth-zero or
tame dihedral supercuspidals constructed in the local theory, and its restricted parameter is
again in that range. Primitive wild supercuspidals and ramified dyadic wild packets are not
included. At infinity we use the real and complex cohomological parameters and selectors of
Book 107. Finally, the packet is **trace-comparable** if it can be detected by the
restricted-tensor matching category defined in Section 4.5, with one factor satisfying the
actual strongly cuspidal hypothesis of the ordinary and twisted simple trace formulas. This
holds for the cohomological packets used in the route whenever a real discrete-series factor
survives at a split real place, or when the cited finite-place simple formula admits the
selected square-integrable factor. The phrase does not mean that an arbitrary smooth local
function has a transfer.

The spectral comparison needs one further, genuinely local boundary condition. At a
nonsplit place put $\Phi_v=\operatorname{rec}_{E_w}(\Pi_w)$ and fix the source central
character $\omega_v$ in the comparison, so
$\det\Phi_v=\operatorname{rec}(\omega_v)|_{W_{E_w}}$. Retain Book 81's
$\operatorname{Ext}^{\mathrm{sel}}$ and write $\operatorname{Ext}^{\mathrm{adm}}$ for its
corresponding set with ``selected'' omitted. The fixed-central-character slices are

$$
\operatorname{Ext}^{\mathrm{sel}}_{F_v/E_w}(\Phi_v;\omega_v)
\subseteq
\operatorname{Ext}^{\mathrm{adm}}_{F_v/E_w}(\Phi_v;\omega_v),
$$

where the right side is the finite set of conjugacy classes of admissible solutions of the
cyclic extension equation $A^{[E_w:F_v]}=r(s^{[E_w:F_v]})$, with the monodromy covariance
included and determinant $\operatorname{rec}(\omega_v)$, and the left side consists of the
classes represented in the selected dictionary. An invariant target parameter with the
chosen norm antecedent $\omega$ is **extension-complete selected** when

$$
\operatorname{Ext}^{\mathrm{sel}}_{F_v/E_w}(\Phi_v;\omega_v)
=\operatorname{Ext}^{\mathrm{adm}}_{F_v/E_w}(\Phi_v;\omega_v)
\tag{1.1}
$$

at every nonsplit place; at a split place the cyclic tensor has one underlying factor and this
condition is automatic. Equality (1.1) permits reducible restricted parameters and all of
their distinct semisimple cyclic operators. It merely excludes a fiber containing an
unconstructed primitive-wild or ramified-dyadic row. Requiring only that one selected
extension exist would not be enough either for forward isolation or for reverse descent,
since matching functions cannot distinguish two extensions after their restrictions have
become isomorphic. A source packet is called extension-complete when each of its restricted
local parameters has this property for its own central character $\omega_\pi$.
For an invariant target with central character $\Omega$, call the packet
**antecedent-complete selected** if (1.1) holds for every
$\omega\in\operatorname{Ant}(\Omega)$, where

$$
\operatorname{Ant}(\Omega)
=\{\omega:C_F\to\mathbb C^\times:\omega\circ N_{E/F}=\Omega\}.
\tag{1.2}
$$

This is the exact reverse-comparison hypothesis when no descent central character is known in
advance. Forward comparison uses only the slice belonging to $\omega_\pi$.

Unless explicitly discussing an isobaric boundary, $\pi$ will mean a unitary cuspidal,
selected, trace-comparable automorphic representation. An essentially unitary cohomological
normalization is reduced to this one by a common real norm twist. No assertion below silently
includes a local packet outside the selected range. Every spectral construction below uses the
extension-complete condition just stated. Statements about the **full** twisting fiber assume
$X(E/F)$-saturation: every $\pi\otimes\chi$ that occurs remains selected and
trace-comparable. Without saturation the formulas describe the ambient automorphic fiber, but
the book asserts only those members lying in its declared test category.

### 1.3 The theorem we are trying to earn

For such a $\pi$, the desired object is denoted

$$
\operatorname{BC}_{E/F}(\pi).
$$

It should satisfy, for every $v$ and every $w\mid v$,

$$
\operatorname{BC}_{E/F}(\pi)_w
\cong \operatorname{BC}_{E_w/F_v}(\pi_v).
$$

It should be invariant under $\Gamma$, unique, and compatible with all operations
visible on local parameters. Its output need not be cuspidal. This last warning is
not a technical blemish: if $E$ contains the quadratic field from which a dihedral
$\pi$ was automorphically induced, restriction exposes two distinct inducing
characters, and the global lift becomes their isobaric sum. The distinctness is a
cyclic Clifford-theory consequence proved in Section 10.3; it is not an extra
regularity assumption on the lifted characters.

There are therefore three distinct assertions to prove:

1. the formal local tensor is automorphic;
2. it is either cuspidal or a precisely described isobaric sum;
3. its isomorphism class and every local component are forced by $\pi$.

The completed split/quaternion simple trace formula proves the first assertion on free
norm-character orbits.
The quadratic theta construction proves the exceptional isobaric case. Strong multiplicity
one proves the third only after automorphic existence has been established.

### 1.4 A first counterexample to placewise reasoning

Take a quadratic field $M/F$ and a Hecke character $\theta$ of $M$ with
$\theta\ne\theta^\tau$, chosen so that its local inductions lie in the selected range, and

$$
\pi=\operatorname{AI}_{M/F}(\theta).
$$

At almost every place, $\pi_v$ is an irreducible spherical principal series. If
$E=M$, its local base change is still an admissible representation at every place,
usually an irreducible principal series. Globally, however,

$$
\operatorname{BC}_{M/F}(\pi)
=\theta\boxplus\theta^\tau,
$$

whose two constituents are distinct because $\theta\ne\theta^\tau$. It is Eisenstein
rather than cuspidal. No inspection of generic unramified local components alone
detects this failure of cuspidality. The global self-twist
$\pi\otimes\eta_{M/F}\cong\pi$ does.

## 2. Norm characters and the expected lift

### 2.1 Why a finite group of characters controls the fibers

Two representations over $F$ can have the same restricted local parameters over $E$.
The simplest reason is that one may twist by a character that becomes trivial after
norm pullback. This makes a finite character group unavoidable from the beginning.

Define

$$
X(E/F)=\{\chi:C_F\to\mathbb C^\times:
\chi\circ N_{E/F}=1\}.
$$

Global class field theory and the norm theorem identify

$$
C_F/N_{E/F}(C_E)\cong\Gamma,
$$

canonically after reciprocity, and hence

$$
X(E/F)\cong\widehat\Gamma.
$$

In particular, $X(E/F)$ is cyclic of order $\ell$. Its members are finite-order unitary
Hecke characters. If $\chi\in X(E/F)$, then local compatibility gives

$$
\operatorname{BC}_{E_w/F_v}(\pi_v\otimes\chi_v)
\cong\operatorname{BC}_{E_w/F_v}(\pi_v)
$$

at every $w\mid v$. Thus any global lift must satisfy

$$
\operatorname{BC}_{E/F}(\pi\otimes\chi)
\cong\operatorname{BC}_{E/F}(\pi).
$$

The norm quotient measures ambiguity downstairs, not a choice of character upstairs.
Writing $C_E/N(C_F)$ would reverse the norm and has no role here.

### 2.2 Localization of norm characters

For each place $v$, localization sends $\chi\in X(E/F)$ to a character of $F_v^\times$.
Its pullback to every $E_w^\times$ above $v$ is trivial. The converse is not a free
choice at each place: a tuple of local norm-trivial characters globalizes only if its
product is trivial on $F^\times$. This is the first local--global compatibility in the
theory.

If $v$ splits completely, $E_w=F_v$ and every localized norm character is trivial at
$v$. If $v$ is unramified and inert of degree $\ell$, the unramified local quotient
$F_v^\times/N(E_w^\times)$ is cyclic of order $\ell$; a generator sends a uniformizer to
a primitive $\ell$th root of unity. At a ramified place the character can be ramified,
and the unit filtration records its conductor.

The global product formula forces compensation. For example, one cannot prescribe a
single nontrivial unramified norm character at one inert place and the trivial
character everywhere else: its value on a suitable principal idele would fail to be
one.

### 2.3 The expected components over a decomposed place

The notation $\operatorname{BC}_{E_w/F_v}$ is literal only after a place $w$ has been
chosen. Globally one must include every place above $v$:

$$
\Pi_v^E:=\bigotimes_{w\mid v}
\operatorname{BC}_{E_w/F_v}(\pi_v),
$$

viewed as a representation of

$$
\mathrm{GL}_2(E\otimes_FF_v)
\cong\prod_{w\mid v}\mathrm{GL}_2(E_w).
$$

The factors are carried into one another by $\Gamma$. At a completely split place there are
$\ell$ factors, each equal to $\pi_v$. Otherwise there is one factor and the local extension
has degree $\ell$: it is unramified inert when $f_v=\ell$, and totally ramified when
$e_v=\ell$. Prime degree leaves no intermediate decomposition type.

This formula prevents a frequent degree error. The Frobenius exponent at one $w$ is
$f_v$, not $\ell$ and not $e_vf_v$. The number $g_v$ counts how many such local factors
occur.

### 2.4 Central characters and the norm direction

If $\omega_\pi$ is the central character of $\pi$, the only possible central
character of a lift is

$$
\boxed{\omega_{\operatorname{BC}\pi}
=\omega_\pi\circ N_{E/F}.}
$$

Indeed, at $w\mid v$ this is exactly the determinant of the restricted local
parameter. On a scalar idele $z\in\mathbb A_E^\times$, the center acts by
$\omega_\pi(N_{E/F}z)$. The diagonal embedding $C_F\to C_E$ is a different map and
does not define this character.

Consequently twists and duals are expected to obey

$$
\operatorname{BC}(\pi\otimes\mu)
\cong\operatorname{BC}(\pi)\otimes(\mu\circ N_{E/F}),
$$

$$
\operatorname{BC}(\pi^\vee)
\cong\operatorname{BC}(\pi)^\vee.
$$

These formulas will follow globally because they hold at every place and strong
multiplicity one identifies the resulting isobaric representations.

### 2.5 The unramified prediction

Suppose $v$ is finite, $\pi_v$ is spherical with Satake pair
$\{\alpha_v,\beta_v\}$, and $w\mid v$. Then the predicted component at $w$ is
spherical with pair

$$
\{\alpha_v^{f_v},\beta_v^{f_v}\}.
$$

Thus its normalized Hecke trace and determinant are

$$
A_w=\alpha_v^{f_v}+\beta_v^{f_v},
\qquad B_w=(\alpha_v\beta_v)^{f_v}.
$$

If $A_v=\alpha_v+\beta_v$ and $B_v=\alpha_v\beta_v$, define

$$
P_0=2,\qquad P_1=A_v,\qquad
P_m=A_vP_{m-1}-B_vP_{m-2}.
$$

Then $A_w=P_{f_v}$. In particular,

$$
A_w=A_v^2-2B_v
$$

at an unramified quadratic inert place. At a split place $f_v=1$, so the parameter is
unchanged on every factor. Ramification index never replaces residue degree in these
formulas.

## 3. Galois action and twisted conjugacy

### 3.1 Why an ordinary trace over $E$ sees the wrong symmetry

Base change predicts a representation $\Pi$ satisfying $\Pi^\sigma\cong\Pi$. An
ordinary trace formula over $E$ sums over all automorphic representations and cannot
distinguish invariant ones from noninvariant Galois orbits. Inserting the field
automorphism into the trace solves this problem: a noninvariant orbit contributes zero
after cyclic permutation, while an invariant representation contributes a twisted
trace.

For a representation $\Pi$ of $G_E=\mathrm{GL}_2(\mathbb A_E)$ define

$$
\Pi^\sigma(g)=\Pi(\sigma^{-1}g).
$$

If $\Pi^\sigma\cong\Pi$, choose an intertwiner

$$
A_\sigma:\Pi\longrightarrow\Pi^\sigma.
$$

For a generic automorphic representation there is a canonical normalization: realize
$\Pi$ in its global Whittaker model for
$\psi_E=\psi_F\circ\operatorname{Tr}_{E/F}$ and require $A_\sigma$ to preserve the
factorizable Whittaker functional. Then

$$
A_\sigma^\ell=1.
$$

Without this normalization, multiplying $A_\sigma$ by an $\ell$th root of unity would
multiply every twisted trace and destroy the global comparison.

### 3.2 Twisted conjugacy and its norm

For $\delta,x\in\mathrm{GL}_2(E)$, define

$$
\delta^x=x^{-1}\delta\sigma(x).
$$

This is $\sigma$-conjugacy. Its ordered norm is

$$
N_\sigma(\delta)
=\delta\,\sigma(\delta)\cdots\sigma^{\ell-1}(\delta).
$$

If $\delta$ is replaced by $\delta^x$, its norm is replaced by
$x^{-1}N_\sigma(\delta)x$. Moreover $\sigma(N_\sigma(\delta))$ is conjugate to
$N_\sigma(\delta)$. Hence the ordinary conjugacy class of the norm is defined over
$F$, although the displayed matrix need not itself have entries in $F$.

For regular semisimple classes in $\mathrm{GL}_2$, rational and stable conjugacy agree
in the needed norm correspondence. The centralizer is a torus, and Hilbert 90 removes
the cohomological ambiguity. Thus regular semisimple $\sigma$-classes in
$\mathrm{GL}_2(E)$ whose norm is defined correspond to regular semisimple classes in
$\mathrm{GL}_2(F)$.

The order in $N_\sigma(\delta)$ matters at the level of representatives, although a
different cyclic starting point gives a conjugate product. Reversing the norm or using
$\sigma^{-1}$ is permissible only if every convention in the twisted action is
changed at the same time.

### 3.3 Local twisted conjugacy when a place splits

At a place $v$, put

$$
G(E_v)=\prod_{w\mid v}\mathrm{GL}_2(E_w).
$$

The generator $\sigma$ permutes the factors. Write
$\delta=(\delta_w)_{w\mid v}$. Following one orbit of places and multiplying the
components with the appropriate field automorphisms reduces the $\sigma$-norm to the
$\sigma^{g_v}$-norm in the chosen factor $E_w/F_v$.

At a completely split place, identify
$G(E_v)$ with $G(F_v)^\ell$ so that $\sigma$ cyclically permutes factors. Then

$$
(g_0,\ldots,g_{\ell-1})\longmapsto g_0g_1\cdots g_{\ell-1}
$$

describes the norm class. A product test function
$\phi_0\otimes\cdots\otimes\phi_{\ell-1}$ transfers to the convolution

$$
f=\phi_0*\phi_1*\cdots*\phi_{\ell-1}
$$

on $G(F_v)$. This elementary split calculation is the local model for the general
twisted trace identity.

### 3.4 Centralizers and measures

The twisted centralizer of $\delta$ is

$$
G_{\delta,\sigma}(F)
=\{x\in G(E):x^{-1}\delta\sigma(x)=\delta\}.
$$

If $\gamma$ is the norm of $\delta$, this group is an $F$-form of the ordinary
centralizer $G_\gamma$. For regular semisimple classes of $\mathrm{GL}_2$ the two are
naturally the same torus after the norm identification. This equality is why their
global volume coefficients can match.

Choose adelic measures from invariant differential forms, and quotient measures by Weil's
formula. At almost every finite place normalize the hyperspecial subgroup to have volume one.
The same measure on the identified ordinary and twisted centralizer must be used in the two
quotient formulas. There are two twisted tangent determinants in the preceding books, and they
must not be conflated. Book 105 uses the full determinant

$$
D_{\mathrm{full}}^\sigma(\delta)
=\det_{F_v}\left(1-\operatorname{Ad}(\delta)\sigma
\mathbin{\big|}\mathfrak h/\mathfrak i_\delta\right).
$$

It contains the nonfixed tangent directions of the norm centralizer. If
$T=G_\gamma\cong G_{\delta,\sigma}$ and $E_w/F_v$ is nonsplit of degree $d_v$, put

$$
D_T^\sigma
=\det_{F_v}\left(1-\sigma
\mathbin{\big|}\operatorname{Lie}T(E_w)/\operatorname{Lie}T(F_v)\right)
=d_v^2.
$$

Book 107's base-change-relative determinant is

$$
D_{\mathrm{bc}}^\sigma(\delta)
=D_{\mathrm{full}}^\sigma(\delta)/D_T^\sigma,
$$

and its relative-root calculation gives the exact identity

$$
D_{\mathrm{bc}}^\sigma(\delta)=D_G(\gamma).
$$

Consequently the transfer factor is $+1$ for raw orbital integrals when the shared centralizer
measure and complementary quotient measures are used. If one instead uses Book 105's full
normalization, the additional factor is $|D_T^\sigma|_v^{1/2}$. This toral factor can be
nonunit when the residue characteristic divides $d_v$. At a completely split place the cyclic
convolution calculation replaces this field-extension determinant calculation.

## 4. Matching functions and local traces

### 4.1 The problem solved by matching

A global trace comparison can be factored place by place only if test functions on
the two groups encode the same conjugacy data. Equality of point values is meaningless
because the groups are different. Orbital integrals are the correct invariant.

Let $f_v$ be a smooth compactly supported function on $G(F_v)$, compact modulo the
center when a central character is fixed, and let $\phi_v$ be such a function on
$G(E_v)$. For regular semisimple $\gamma\in G(F_v)$ set

$$
O_\gamma(f_v)
=\int_{G_\gamma(F_v)\backslash G(F_v)}
f_v(x^{-1}\gamma x)\,dx.
$$

For $\delta\in G(E_v)$ set

$$
TO_{\delta,\sigma}(\phi_v)
=\int_{G_{\delta,\sigma}(F_v)\backslash G(E_v)}
\phi_v(x^{-1}\delta\sigma(x))\,dx.
$$

Put

$$
I_\gamma(f_v)=|D_G(\gamma)|_v^{1/2}O_\gamma(f_v),\qquad
I^{\sigma,\mathrm{bc}}_\delta(\phi_v)
=|D_{\mathrm{bc}}^\sigma(\delta)|_v^{1/2}
TO_{\delta,\sigma}(\phi_v).
$$

The pair $(f_v,\phi_v)$ is **matching** if

$$
I_\gamma(f_v)=I^{\sigma,\mathrm{bc}}_\delta(\phi_v)
$$

whenever $\gamma$ is the norm of $\delta$, and the ordinary normalized orbital integral
vanishes on regular classes that are not norms. Equivalently,

$$
O_\gamma(f_v)=TO_{\delta,\sigma}(\phi_v).
$$

This raw equality uses the shared centralizer and complementary quotient measures. With Book
105's full tangent normalization, the twisted side acquires the factor
$|D_T^\sigma|_v^{1/2}$. Singular germs and central distributions must also obey their
separately stated matching rules; regular matching alone is insufficient for the simple trace
formula.

### 4.2 Central covariance

Fix a unitary Hecke character $\omega$ of $C_F$ and put

$$
\Omega=\omega\circ N_{E/F}.
$$

On the $F$-side require

$$
f_v(zg)=\omega_v(z)^{-1}f_v(g),
$$

and on the $E$-side

$$
\phi_v(zg)=\Omega_v(z)^{-1}\phi_v(g).
$$

These conditions make convolution well defined on the quotient by the adelic center.
They are also compatible under the norm of scalar matrices. If one starts with an
ordinary compactly supported function, central averaging produces the required
covariance.

The choice of $\omega$ is essential in a fixed-central comparison. A Galois-invariant central
character $\Omega$ over $E$ may have several norm antecedents. Forward comparison uses the
known $\omega_\pi$; reverse comparison first uses the determinant-one formula, lets a source
central character emerge, and only then returns to a fixed-central block. Chapter 11 explains
which other antecedents can occur as central characters of descents.

### 4.3 The unramified fundamental function

Suppose $v$ is unramified in $E$, all central characters are unramified, and hyperspecial
subgroups have volume one. The unit elements of the spherical Hecke algebras match.
More generally, the base-change homomorphism of spherical Hecke algebras is the map
whose Satake transform evaluates a symmetric Laurent polynomial on

$$
(X_1,X_2)\longmapsto(X_1^{f_v},X_2^{f_v})
$$

in each local factor, with the cyclic convolution rule across the $g_v$ factors.
Equivalently, a spherical $\pi_v$ with parameter $\{\alpha_v,\beta_v\}$ satisfies

$$
\operatorname{tr}\pi_v(f_v)
=\operatorname{tr}\bigl(\Pi_v^E(\phi_v)A_{\sigma,v}\bigr).
$$

This is the fundamental lemma in rank two. Its content is not merely the equality for
the unit: it identifies the entire spherical Hecke algebra and hence all powers of
Frobenius.

### 4.4 The local matching trace identity

Book 81 gives the finite-place local base-change representation by restriction of the full
Weil--Deligne parameter, and Book 107 treats the archimedean selected types. The extra assertion
needed globally is a theorem of local harmonic analysis, not a consequence of parameter
restriction alone.

**Theorem 4.1 (selected local matching and twisted characters).** For a matching pair
$(f_v,\phi_v)$ and an irreducible $\pi_v$ in the selected local base-change domain,

$$
\boxed{
\operatorname{tr}\pi_v(f_v)
=\operatorname{tr}\left(
\left(\bigotimes_{w\mid v}\operatorname{BC}_{E_w/F_v}\pi_v\right)
(\phi_v)A_{\sigma,v}
\right).
}
$$

Here $A_{\sigma,v}$ cyclically permutes the factors and uses the normalized local
intertwiner on returning to the chosen place. At a split place this is the elementary
identity

$$
\operatorname{tr}\bigl(\pi_v(\phi_0)\cdots\pi_v(\phi_{\ell-1})\bigr)
=\operatorname{tr}\pi_v(\phi_0*\cdots*\phi_{\ell-1}).
$$

At a nonsplit place the assertion is the twisted character identity for restriction of the
local parameter. It includes determinant, principal, special, selected dihedral, and the
archimedean representations treated in Book 107. It does not include primitive wild or
ramified dyadic wild packets.

**Proof strategy.** Establish the identity first on regular split and elliptic classes, match
the two nilpotent germs and scalar distributions, and then use Weyl integration to pass from
orbital identities to character traces.

**Proof.** Book 107 proves this statement without using global base change. Principal-series
characters are unfolded to diagonal-torus integrals; the special case retains nonzero
monodromy at the reducibility boundary; and selected dihedral characters are compared on
elliptic tori. Weighted lattice descent proves the unramified unit identity, gallery descent
proves the spherical algebra identity, and segment and finite Fourier calculations prove the
selected ramified type identities. The two nilpotent germs and quadratic scalar channel are
audited separately. At split places the cyclic tensor trace is the displayed convolution
identity, and at infinity Cartan descent gives the required cohomological selectors. Weyl
integration then converts normalized orbital matching into the trace identity. $\square$

This is stronger than equality of local $L$-factors. The latter would not allow test
functions to vary enough to recover a ramified or archimedean representation.

### 4.5 Existence of matching functions

The transfer theorem needed here has a directed and finite scope. We record it instead of
silently replacing it by surjectivity on the whole Hecke algebra.

Let $L_v=E\otimes_FF_v$, with the cyclic permutation induced by $\sigma$. On the twisted
side let $\mathscr T_v^{\mathrm{sel}}$ be the algebraic span, with the central covariance of
Section 4.2, of the following functions. Each individual test uses only a
finite-dimensional subspace.

1. at a split algebra, finite tensors whose cyclic convolution is defined;
2. at an unramified field place, the full spherical Hecke algebra;
3. on any nonarchimedean regular region separated from the discriminant, the compact
   regular-slice functions of Book 107, Theorem 8.1;
4. at a ramified finite place, selected invariant finite-level, finite Iwahori,
   $K_0/K_1$, and normalized selected type functions, including the two germ rows of
   Books 102 and 107;
5. at infinity, the cohomological Euler--Poincare and Schwartz selectors constructed in
   Book 107.

The span is closed under the finitely many central translates, inversions, determinant/norm
twists, and convolutions for which the cited constructions prove compatibility. A function
which meets the scalar divisor is admitted only together with its complete zero-orbit,
regular-nilpotent, and central prescription. Thus an arbitrary noninvariant wild coset, or an
arbitrary smooth function with uncontrolled singular germ, is not in
$\mathscr T_v^{\mathrm{sel}}$.

**Theorem 4.2 (directed local matching category).** For
$\phi_v\in\mathscr T_v^{\mathrm{sel}}$ there is a compact-mod-center ordinary companion
$f_v^0$ on $\mathrm{GL}_2(F_v)$ with the following properties.

1. Regular norm orbital integrals match, regular nonnorm orbital integrals of $f_v^0$ vanish,
   and the two split germs match.
2. The split scalar distribution satisfies the separately imposed central identity of
   Book 107, Section 12.5.
3. If $E_w/F_v$ is a nonsplit quadratic field extension, there is in addition a function
   $f_v^{\mathrm{div}}$ on the quaternion division group. Its central value is the relative
   twisted orbital integral on the nontrivial scalar-obstruction stratum (possibly zero), and
   its neighboring elliptic orbital data are those prescribed in Book 107, Section 12.4.
4. On every finite selected spectral window, the twisted traces of functions in
   $\mathscr T_v^{\mathrm{sel}}$ separate invariant selected representations with their
   normalized cyclic intertwiners. Their ordinary traces separate precisely the equivalence
   classes defined by isomorphic restricted parameters. They are not asserted to separate
   two different extension operators whose restrictions are already isomorphic.

The companion is unique only modulo regular orbital-null functions after its germ and central
coordinates have been fixed. No assertion is made that every $f_v\in C_c^\infty$ has a
twisted partner.

**Proof.** The split row is cyclic convolution. The unramified row is the spherical
fundamental lemma. Book 107, Theorem 8.1, gives both realizations for compact regular orbital
data bounded away from the discriminant, while Theorems 9.1, 10.1, and 11.1 give the stated
finite-level and type rows. Its Theorem 12.1 supplies exactly the two split germs. Sections
12.4 and 12.5 construct, rather than merely prescribe, the division and split central
companions. Chapter 13 gives the archimedean rows. All these constructions start with
$\phi_v$ (or with a compact regular orbital datum); none proves surjectivity from the full
ordinary Hecke algebra.

For the separation assertion, first fix the finite window. Selected type Schur
orthogonality gives the diagonal trace coordinates for distinct types. Representations left
in one type row have linearly independent regular character distributions; hence finitely many
regular neighborhoods give a full-rank evaluation matrix. The regular-slice construction
realizes its inverse matrix. At a scalar boundary the zero-orbit coordinate (the central point
value) and the regular-nilpotent germ form the triangular system of Book 107, equation (9.6), so the
same interpolation remains possible there. Twisted character independence proves target
separation. On the source, a norm-trivial quotient twist has the same character on every norm
class, and more general reducible extension classes can also have the same restriction; the
matching algebra therefore separates exactly the stated restriction classes and no more.
$\square$

The local companions genuinely globalize, including their central terms.

**Theorem 4.3 (restricted tensors and coherent quaternion channels).** Let

$$
\phi=\sum_{j=1}^r\bigotimes_v\phi_{j,v}
$$

be a finite sum of tensors with $\phi_{j,v}\in\mathscr T_v^{\mathrm{sel}}$, the
hyperspecial unit almost everywhere, and one common matching strongly cuspidal row. Then the
split companions form a finite sum of restricted tensors

$$
f^0=\sum_{j=1}^r\bigotimes_v f^0_{j,v}.
$$

If $\ell=2$, there is also a finite set $\mathcal Q(\phi)$ of nonsplit quaternion algebras
$B/F$, each split by $E$, and for every $B\in\mathcal Q(\phi)$ a restricted tensor

$$
f^B=\sum_{j=1}^r\bigotimes_v f^B_{j,v}
\quad\text{on }B^\times(\mathbb A_F).
$$

At a split place of $B$ use $f^0_{j,v}$; at a division place use the companion
$f^{\mathrm{div}}_{j,v}$. These functions simultaneously compare the neighboring regular
terms and the complete scalar terms. With the global quotient measures of Books 105 and 107,
the split scalar channel is the central distribution of $f^0$, and the scalar classes whose
cyclic algebra is $B$ give the central distribution of $f^B$. No local scalar value or
projective stabilizer index remains to be supplied after tensoring.

The same assertion holds on the determinant-one trace quotients used in Book 105. In that
version no Fourier averaging by a chosen $\omega$ is made: one retains each rational scalar
$a$ and its arithmetic quotient volume, and the local central prescriptions tensor with that
actual $a$. We denote the resulting companion by
$\mathbf f^1=(f^{0,1},\{f^{B,1}\})$. This version is essential
when the central character of a reverse descent is not known beforehand.

**Proof.** Choose a finite set $S$ containing the archimedean places, the places where
$E/F$, the central character, or a tensor factor is ramified, and every place at which a
nonunit germ row is used. Outside $S$ the extension is unramified and the twisted function is
the hyperspecial unit. A projective scalar class with quaternion division centralizer has odd
determinant valuation there, whereas the unit row has even projective determinant valuation;
its twisted orbital integral is therefore zero. Hence a contributing $B$ is split outside
$S$. Its local invariants are $0$ or $1/2$, have even total parity, and determine one global
quaternion algebra. There are only finitely many such patterns, proving finiteness of
$\mathcal Q(\phi)$.

There is a small linearity point here which is essential for globalization. For each
$v\in S$, take the finite-dimensional span of the finitely many factors $\phi_{j,v}$ together
with the germ and central rows they use. The slice, finite-level, and two-germ constructions
in the proof of Theorem 4.2 are linear maps on their orbital-coordinate spaces. Choose a
right inverse once on this finite-dimensional span, sending the unramified unit to the unit,
and use it for every $j$. This gives linear sections

$$
s_v^0:\phi_{j,v}\longmapsto f^0_{j,v},
\qquad
s_v^{\mathrm{div}}:\phi_{j,v}\longmapsto f^{\mathrm{div}}_{j,v}
$$

with the central and both germ coordinates included in the same linear system. No choice is
made separately for each rational scalar. For each coherent pattern these sections supply
the finitely many exceptional local factors; all other factors are the common unit. This
proves the restricted-product assertion, including compatibility with the finite sum over
$j$. The local central constructions are uniform on compact-open scalar strata, so one tensor encodes
all rational scalar representatives in that stratum, not merely one chosen $a$. Their local
covariances tensor to a genuine adelic fixed-central-character function because
$\prod_v\omega_v(z)=1$ for $z\in F^\times$; compactness modulo the center is inherited from
the finitely many local supports. Their local point values multiply, and the common global centralizer measure disintegrates into the same
local quotient measures. Book 105's global projective stabilizer index is consequently the
one already present on both sides. On the determinant-one quotient omit central averaging;
the restricted tensor is compact on each retained determinant shell, and the same
disintegration gives the coefficient of the actual scalar $a$. The cyclic-algebra classification
$F^\times/N_{E/F}(E^\times)\to\operatorname{Br}(E/F)$, the Hasse norm theorem, and the
Albert--Brauer--Hasse--Noether parity relation say that precisely the coherent patterns just
listed come from global scalar classes.

Finally, the primary local identity is equality of raw orbital integrals, equivalently equality
with Book 107's relative discriminant. If Book 105's full twisted tangent determinant is
used, each local equality acquires $|D_T^\sigma|_v^{1/2}$; these factors are the localizations
of one rational determinant and their global product is one. Thus globalization changes
neither the full-versus-relative discriminant ledger nor its scalar normalization. $\square$

## 5. The twisted trace formula in rank two

### 5.1 The kernel and the inserted automorphism

We now pass from local matching to the global spectral construction proved in Book 106. Write
$G_K=\mathrm{GL}_2(\mathbb A_K)$. Let $\phi=\bigotimes_v\phi_v$ be admissible, spherical
almost everywhere, of finite level and compact type, and strongly cuspidal at one place. On
the fixed-central-character quotient define

$$
K_\phi(x,y)=\sum_{\delta\in Z(E)\backslash\mathrm{GL}_2(E)}
\phi(x^{-1}\delta y).
$$

The twisted operator is $R(\phi)I_\sigma$, where

$$
(I_\sigma h)(x)=h(\sigma^{-1}x).
$$

Strong cuspidality means that the left and right integrals of the distinguished local factor
along the unipotent radical vanish. That one local vanishing propagates to the global constant
terms in both kernel variables. The kernel is therefore rapidly decreasing on the noncompact
quotient, the operator is trace class, and Book 106 proves the genuine diagonal identity

$$
I_E^\sigma(\phi)
=\operatorname{tr}(R(\phi)I_\sigma)
=\int_{Z(\mathbb A_E)\mathrm{GL}_2(E)\backslash G_E}
K_\phi(x,\sigma x)\,dx.
$$

This is the **twisted simple trace formula**. No truncation or constant-term extraction occurs
in the comparison used here. The strong-cuspidality hypothesis is what makes that simplification
legitimate, and it is why the trace-comparability condition was stated in Chapter 1.

### 5.2 Why norm characters label identical comparisons

The lift cannot distinguish $\pi$ from $\pi\otimes\chi$ for $\chi\in X(E/F)$. If $\omega$
is the central character on the source, then the target character is
$\Omega=\omega\circ N_{E/F}$. For
$\chi\in X(E/F)$ put

$$
f^\chi(g)=\chi(\det g)^{-1}f(g).
$$

Then $f^\chi$ has inverse covariance $(\omega\chi^2)^{-1}$ and

$$
\operatorname{tr}(\pi\otimes\chi)(f^\chi)=\operatorname{tr}\pi(f).
$$

Moreover $f$ and $f^\chi$ have the same transfer: if $\gamma=N_\sigma(\delta)$, then
$\chi(\det\gamma)=1$. Thus the collection of fixed-character comparisons is constant along
the $X(E/F)$-orbit, which is exactly the source of the descent ambiguity.

For odd $\ell$, squaring is an automorphism of $X(E/F)$, so a fixed source central-character
block meets a twisting orbit in exactly one member. Quadratic degree is different:
$\chi^2=1$, the two members of a free orbit have the same central character, and every matching
function has the same trace on them. It is therefore impossible to isolate either member by
the matching algebra. The coherent split/quaternion completion of Section 6.1, after its
finite Brauer-pattern inclusion--exclusion, realizes the two spectral coordinates for the
global group $X(E/F)=\{1,\eta_{E/F}\}$. The inverse order-two Fourier matrix gives one common
trace for a free orbit and removes a fixed cuspidal orbit from the cuspidal comparison. The factor $1/2$ occurring in that inverse
matrix is forced by Fourier inversion, not assigned ad hoc to an individual automorphic
representation. Section 6.1 proves this completion before it is used for existence.

The fixed orbit is treated by the independent quadratic theta identity of Lemma 10.1. Its
base change is an isobaric character sum, and the strongly cuspidal target operator kills that
sum. Thus stabilizer size, orbit size, and spectral multiplicity remain distinct throughout.

### 5.3 The geometric expansion

The geometric side of the simple formula is the absolutely convergent distribution proved in
Book 105. In prime degree it has three, not four, surviving channels:

$$
I_{E,\mathrm{geom}}^\sigma(\phi)
=I_{\mathrm{sc,sp}}^\sigma(\phi)
+I_{\mathrm{reg,ell}}^\sigma(\phi)
+\mathbf1_{\ell=2}I_{\mathrm{sc,div}}^\sigma(\phi).
$$

The first term is the split scalar-norm channel. The second is the sum over regular elliptic
norms satisfying the full torus norm condition. The last occurs only when $\ell=2$: a nonnorm
scalar has quaternion division centralizer and is elliptic even though its stable norm is
central. Split regular and noncentral repeated-norm classes lie in the parabolic channel;
strong cuspidality kills that combined distribution before the cutoff is removed. There is no
surviving hyperbolic or unipotent summand of the simple formula.

For a regular class $[\delta]_\sigma$ with norm $[\gamma]$, the term is

$$
a(\delta,\sigma)TO_{\delta,\sigma}(\phi),
$$

where

$$
a(\delta,\sigma)
=\operatorname{vol}\bigl(
Z(\mathbb A_F)G_{\delta,\sigma}(F)
\backslash G_{\delta,\sigma}(\mathbb A_F)
\bigr).
$$

Under the norm correspondence this is the same torus volume as the coefficient $a(\gamma)$
on the $F$-side. With complementary measures, the raw adelic orbital terms factor:

$$
TO_{\delta,\sigma}(\phi)
=\prod_vTO_{\delta_v,\sigma}(\phi_v),
\qquad
O_\gamma(f)=\prod_vO_{\gamma_v}(f_v).
$$

Matching at every place therefore identifies every regular elliptic term. If the geometric
formula is written with Book 105's full tangent normalization, the conversion contributes the
local toral factors $|D_T^\sigma|_v^{1/2}$; their adelic product is one because they localize
one rational determinant. Thus no degree factor survives globally, although it cannot be
discarded in an individual local identity.

The scalar terms require separate matching and cannot be inferred by taking a limit of regular
orbital integrals. Book 107 matches the two nilpotent germs, the projective split-scalar
distribution, and, in quadratic degree, the family of quaternion division-centralizer terms.
The local inner-form signs satisfy the global product constraint. These results, together with
the common centralizer measures, leave no unrecorded discriminant, sign, or scalar index in the
global comparison.

### 5.4 The spectral expansion

The spectral side contains only the cuspidal term:

$$
I_E^\sigma(\phi)
=\sum_{\Pi\simeq\Pi^\sigma}
\operatorname{tr}\bigl(\Pi(\phi)A_\sigma\bigr).
$$

Cuspidal representations in nontrivial $\Gamma$-orbits contribute zero because
$I_\sigma$ cyclically permutes their isotypic spaces. Multiplicity one allows us to
write no additional multiplicity factor. Book 106 proves absolute convergence of this series
by a cuspidal Sobolev factorization, not by formal rearrangement.

Why are there no other terms? The strongly cuspidal local factor has zero operator on every
normalized induced representation. The global tensor operator is therefore zero on every
Eisenstein packet. The residual spectrum of rank two consists of determinant-character lines,
and the same vanishing kills those lines. Density of pseudo-Eisenstein series then proves

$$
R(\phi)I_\sigma\bigm|_{L^2_{\mathrm{cusp}}{}^\perp}=0.
$$

Thus the continuous and residual distributions vanish as operators; they are not matched and
subtracted afterward. This fact is decisive for the later cuspidality discussion: the simple
trace formula constructs cuspidal lifts in the free case, while the exceptional isobaric lift
must be established by the explicit quadratic argument of Chapter 10.

### 5.5 Factorization of a twisted automorphic trace

Suppose $\Pi=\bigotimes_w'\Pi_w$ is invariant and generic. The global Whittaker
normalization factors the intertwiner:

$$
A_\sigma=\bigotimes_vA_{\sigma,v}.
$$

For a pure tensor $\phi=\bigotimes_v\phi_v$ with spherical units almost everywhere,

$$
\operatorname{tr}\bigl(\Pi(\phi)A_\sigma\bigr)
=\prod_v
\operatorname{tr}\bigl(\Pi_v^E(\phi_v)A_{\sigma,v}\bigr).
$$

This factorization is the spectral bridge to Book 81. A different scalar normalization
at one place would alter one factor and hence the global product. Requiring the local
Whittaker functionals to multiply to the global one makes the product canonical.

## 6. Comparing the geometric and spectral sides

### 6.1 The global matching identity

Let $\phi$ be a global test in Theorem 4.3 and write

$$
\mathbf f=\left(f^0,\{f^B:B\in\mathcal Q(\phi)\}\right)
$$

for its complete source companion. The symbol $\mathbf f$ is important: in quadratic degree
the source of the comparison is not one function on one group.

For a fixed level, compact type, central character, and bounded infinitesimal-character window,
let $\mathcal O_\omega^{\mathrm{fr}}$ be the set of free $X(E/F)$-orbits of selected,
extension-complete cuspidal $\mathrm{GL}_2(\mathbb A_F)$ representations meeting the
central-character block $\omega$.
If $\ell$ is odd, such an orbit has one member in that block. If $\ell=2$, its two members
have the same central character and matching functions have the same trace on both; denote this
common value by

$$
\operatorname{tr}_{\mathcal O}(f^0).
$$

Write $\mathscr W$ for the finite selected, extension-complete spectral window generated by
this nonempty source matching class and its possible target constituents.
A test is **$\mathscr W$-projected** if it contains the exact compact-type projectors and the
bounded archimedean multiplier defining $\mathscr W$, and if the finite regular-slice/Hecke
interpolation of Theorem 4.2 makes every other selected restriction class in that bounded
window have trace zero. The multiplier is understood as the trace-norm limit used in Book 96.
Thus this adjective describes an actual finite test construction; it does not discard terms
from a trace formula after it has been written. Put
$\mathcal A_{\mathrm{cusp}}(E,\Omega;\mathscr W)$ for the resulting finite target set. This
fixed-central form is source-directed; the target-directed reverse comparison is the
determinant-one identity proved after Theorem 6.1.

**Theorem 6.1 (geometric comparison and spectral completion).** For the complete companion
of a $\mathscr W$-projected test there is a canonically completed source distribution
$I_{F,\omega}^{\mathrm{bc,sel}}(\mathbf f)$ such that

$$
\boxed{
I_{F,\omega}^{\mathrm{bc,sel}}(\mathbf f)
=\sum_{\mathcal O\in\mathcal O_\omega^{\mathrm{fr}}}
\operatorname{tr}_{\mathcal O}(f^0)
=\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E,\Omega;\mathscr W)\\
\Pi^\sigma\simeq\Pi}}
\operatorname{tr}\bigl(\Pi(\phi)A_\Pi^{\mathrm{aut}}\bigr).
}
\tag{6.1}
$$

The first equality includes, rather than discards, every noncharacter quaternionic spectral
block occurring in the scalar completion. Quaternionic norm characters are removed only by
the character-clean interpolation described below. The identity is compatible as
$\mathscr W$ is enlarged through the declared selected, extension-complete category. When the
corresponding selected multiplier has a trace-class limit, that limit is the absolutely
convergent selected distribution in (6.1); no assertion is made about constituents outside
this directed category.

**Proof strategy.** First globalize all three geometric channels by Theorem 4.3. In quadratic
degree complete each quaternionic central term by its compact trace formula, retaining the
regular terms introduced by that completion. Finite Fourier inversion on the coherent local
Brauer-invariant patterns cancels those extra regular rows. Transfer every surviving
quaternionic noncharacter block to a split cuspidal block by the character-clean trace argument
of Book 96. Only after this step regroup by split Hecke characters. The resulting order-two
Fourier projector has one common trace on a free twisting orbit and zero on a fixed cuspidal
orbit.

**Proof.** For a regular norm class, Theorem 4.3 gives equality of the raw local orbital
integrals. The ordinary and twisted centralizers are the same global torus, with the same
arithmetic volume. A regular nonnorm class has a zero local ordinary factor. For split scalar
norms, the complete central prescription of Theorem 4.2 identifies the relative twisted
distribution with the ordinary central distribution, including the projective stabilizer
index. When $\ell=2$, the remaining scalar classes are partitioned by their cyclic quaternion
algebra $B=(E/F,a)$ and are the central distributions of the restricted tensors $f^B$.
Theorem 4.3 proves that only finitely many $B$ occur.

We now justify the word _completed_. Enlarge the actual scalar family
$\mathcal Q(\phi)$ to the finite set $\mathcal B_S$ of all quaternion algebras split outside
$S$. For $B=M_2(F)$ retain $f^0$ and its split scalar coordinate. If $B$ is division and
$B\notin\mathcal Q(\phi)$, give it an **auxiliary** restricted tensor as follows. At a
division place prescribe on $B_v^\times$ the neighboring elliptic orbital function obtained
from $f_v^0$, with the local inner-form sign of Books 102--103, and prescribe central value zero; the ordinary orbit map is a submersion on the
regular set and the division algebra has only the zero germ, so the regular-slice and central
bump argument of Books 102--103 realizes these two coordinates simultaneously. At split
places use the corresponding split factor, and use units almost everywhere. These auxiliary
forms carry no scalar channel; they are introduced only in pairs of complete trace formulas
whose regular rows cancel below.

Choose a strongly cuspidal selector place $v_*\in S$; in the declared category it is finite or
real. Every regular class which survives there
has a quadratic **field** centralizer. Let $S_0\subset S$ be the finite and real places at
which a quaternion algebra can ramify; complex places carry no Brauer coordinate. Put

$$
\mathcal A_S=
\left\{\epsilon=(\epsilon_v)_{v\in S_0}\in(\mathbb Z/2\mathbb Z)^{S_0}:
\sum_{v\in S_0}\epsilon_v=0\right\};
$$

these are exactly the coherent ramification patterns of quaternion algebras split outside
$S$. The actual scalar obstruction patterns form the subgroup

$$
\mathcal A_S^E
=\{\epsilon\in\mathcal A_S:\epsilon_v=0
\text{ whenever }E\otimes_FF_v\text{ is split}\};
\tag{6.2a}
$$

the other patterns label the zero-central auxiliary forms introduced above. For a regular quadratic torus put $q_v(T)=1$ if $T_v$ is a field and $q_v(T)=0$ if it is
split. The embedding criterion is the explicit Boolean monomial

$$
m_{\epsilon}(T)
=\prod_{\{v:\epsilon_v=1\}}q_v(T).
\tag{6.2}
$$

Indeed a split quaternion algebra admits both quadratic étale types, whereas a division
quaternion algebra admits precisely the field type. Since $q_{v_*}(T)=1$ and parity determines
$\epsilon_{v_*}$ from the other coordinates, the rows of (6.2) are all square-free monomials
in the variables $q_v$, $v\in S_0\setminus\{v_*\}$. Weak approximation for quadratic
polynomials realizes every such local split/field pattern by a global quadratic field, since
the condition at $v_*$ keeps the polynomial irreducible globally. Their values on the Boolean cube form the
zeta matrix of the subset lattice. Its inverse is the Möbius matrix

$$
(M^{-1})_{A,C}=
\begin{cases}
(-1)^{|C\setminus A|},&A\subseteq C,\\
0,&A\not\subseteq C.
\end{cases}
\tag{6.3}
$$

after indexing a monomial and a Boolean point by their supports.

This matrix is applied to functions, not separately to infinitely many rational orbits. On
the regular invariant support, split versus field at every $v\in S_0$ is an open-and-closed
condition after the discriminant-zero locus has been removed. A finite invariant partition
of unity therefore decomposes the compact regular orbital datum as
$R=\sum_C R_C$ by its Boolean pattern $C$; at a real place use the two smooth components of
the regular quotient. The germ rows handle the omitted discriminant-zero boundary. The
regular-slice theorem realizes every $R_C$, so the constant row $(M^{-1})_{A,C}$ can be
applied to that whole slice at once. Weak approximation above proves that no column of this
finite functional matrix is merely formal.

To include the scalar rows, use two independently variable families of test functions. Here a
``regular coordinate'' at a scalar boundary means the regular orbital transform after the
universal zero-orbit germ $\Gamma_0f(z)$ has been removed; the coefficient $f(z)$ itself is
the scalar coordinate. This is the direct-sum coordinate system of Book 107, Sections
12.3--12.5, not an assertion that a smooth central bump is pointwise supported on the center.
The regular-slice family has incidence matrix $M$. In the zero-orbit/central-bump family,
subtracting the second germ function kills the regular-nilpotent coordinate, and subtracting
the prescribed $\Gamma_0$ multiple leaves the reduced regular coordinate zero. Its remaining
central-value matrix is diagonal. Thus, on the finite orbital-coordinate module generated by
the test, and with reduced regular coordinates first and scalar coordinates second, the
complete matrix is block triangular:

$$
\begin{pmatrix}M&0\\ *&I\end{pmatrix}.
\tag{6.3a}
$$

Its inverse exists by (6.3). Apply it to the vector consisting of the original regular norm
rows, the split scalar row, the actual $\mathcal A_S^E$ quaternion rows, and zeros in every
auxiliary scalar row. This expresses that exact vector as a finite linear combination of
**complete** inner-form geometric traces. Equivalently, it cancels every neighboring regular
row introduced while retaining all prescribed central rows. This finite
inclusion--exclusion is the inner-form completion; no partial central term is called a spectral
trace and no regular quaternionic orbit is lost.

The scalar obstruction itself is the finite subgroup $\mathcal A_S^E$; its nonzero
elements are the distinct quaternion channels and must not be collapsed to one ``nonnorm''
class. The larger $\mathcal A_S$ supplies the auxiliary regular rows needed for the invertible
incidence matrix. After (6.3) has completed them and Book 96 has regrouped their spectra on the
split group, the remaining global spectral symmetry is
$X(E/F)=\{1,\eta_{E/F}\}$. Its character table is

$$
H_2=\begin{pmatrix}1&1\\1&-1\end{pmatrix},
\qquad H_2^{-1}=\frac12H_2.
\tag{6.4}
$$

Apply (6.4) to the regrouped spectral coordinates after the inner-form completion. This is the
canonical order-two operation which defines the orbit coordinate of
$I_{F,\omega}^{\mathrm{bc,sel}}(\mathbf f)$. The Brauer-pattern inclusion--exclusion (6.3),
which retains every rational scalar obstruction class, and the global norm-character Fourier
inversion (6.4) must not be conflated.
The character calculation proving that exactly these two global coordinates survive is given
below in (6.4a).

This definition is independent of $S$ and of the slice representatives. Enlarging $S$ tensors
the incidence matrix with the two-element zeta matrix and appends zero scalar coordinates;
Möbius inversion sends that enlarged vector back to the old one. Two auxiliary tensors with
the same regular data and zero central coordinate differ by an orbital-null, scalar-null
function, whose trace is zero by Weyl integration. Hence the completed distribution depends
only on the original companion $\mathbf f$.

For completeness, we pass from this geometric completion to its spectrum without assuming
global Jacquet--Langlands. If $B_\epsilon$ is division, Book 96 proves compactness modulo the center
and the spectral formula

$$
I_{B_\epsilon}(f^{B_\epsilon})
=\sum_\rho\operatorname{tr}\rho(f^{B_\epsilon}).
$$

Let $g^{B_\epsilon}$ denote the split transfer used in Book 96's comparison. It has the prescribed
regular orbital data and the separately normalized scalar coordinate; it is not asserted to be
pointwise equal to the original $f^0$. The matrices (6.3)--(6.4) act on these complete
distributions. Once their extra regular and scalar rows have canceled, Weyl integration says
that the surviving split cocenter coordinate is precisely that of $f^0$; changing a
representative by a regular orbital-null function changes no irreducible trace.

At the outset of the fixed-window interpolation, use at every ramified finite place the exact
compact-type idempotent, and at infinity the bounded selected multiplier, occurring in the
definition of the global test category. Schur orthogonality makes every constituent outside
those selected type blocks have trace zero; we do not try to separate an arbitrary wild
constituent by an unproved matching character identity. Inside the resulting finite selected
block, regular-character independence separates coordinates with different restricted trace
functionals. A constituent with the same functional would be another extension of that
restricted parameter, and extension-completeness says that it too is one of the selected
indices retained in the block. Thus this is an actual finite spectral projection, not notation
suppressing an unwanted summand.

Book 96, Proposition 7.2, then interpolates against all global norm characters
and against the scalar point mass. The two-germ triangular system preserves the required
central value while making those character traces zero. It then compares every remaining
noncharacter block with a split cuspidal trace. This argument applies to every global
quaternion division algebra, even one split at a real place: Book 96 uses anisotropic
compactness and its two ramified transfer places, not the totally-definite hypothesis of the
packaged theorem in Book 104. Its Bessel inequality and strong determination show that a
surviving quaternionic block has one unique split cuspidal completion. At selected division
places Books 80 and 102--103 identify the local component and the two local signs; the global
number of ramified places is even, so their product is $+1$.

The word ``then'' denotes an order of proof, not a later alteration of an already matched
function. Append the finitely many norm-character trace equations and prescribed
noncharacter coordinates to the orbital matrix (6.3a) before taking its inverse. Proposition
7.2 says that the character distributions and scalar point mass are independent of the chosen
regular-slice coordinates; its central bump supplies the last diagonal entry. The augmented
matrix is therefore again block triangular with invertible diagonal blocks. Solving it once
imposes character-cleanliness, scalar values, and cancellation of auxiliary regular rows
simultaneously. Thus the Book 96 interpolation cannot reopen a geometric row canceled by
(6.3a).

We record the finite character calculation which connects this completed inner-form spectrum
to (6.4). Let $V_S=(\mathbb F_2)^{S_0}$ and let
$\mathcal A_S=\mathbf1^\perp\subset V_S$ be the even-parity Brauer patterns. On a selected
noncharacter block, the local elliptic character identity of Books 80 and 103 says that
changing the local inner-form coordinate $\epsilon_v$ multiplies its elliptic extension
coordinate $x_v$ by $(-1)^{\epsilon_vx_v}$. If the block has no division member at $v$, its
$\epsilon_v=1$ coefficient is zero; that is the vanishing of a principal-series character on
elliptic classes, not the deletion of a quaternionic representation. Tensoring the local
tables gives $(-1)^{\langle\epsilon,x\rangle}$, and therefore

$$\frac1{|\mathcal A_S|}\sum_{\epsilon\in\mathcal A_S}(-1)^{\langle\epsilon,x\rangle}=

\begin{cases}
1,&x=0\ \text{or}\ x=\mathbf1,\\
0,&\text{otherwise}.
\end{cases}
\tag{6.4a}
$$

This is character orthogonality, since
$\mathcal A_S^\perp=\{0,\mathbf1\}$. The auxiliary rows in
$\mathcal A_S\setminus\mathcal A_S^E$ are exactly what makes the full sum in (6.4a)
available: their scalar coordinates are zero, while (6.3a) cancels their regular
coordinates. At places split in $E$, cyclic convolution identifies the two formal columns.
At nonsplit places the two remaining coherent cyclic-extension columns differ by the local
quotient character. Global reciprocity thus identifies the surviving columns with $1$ and
$\eta_{E/F}$, giving exactly $H_2$ and proving the norm-character Fourier step in (6.1).

The calculation acts only on the split/division sign coordinate. Additional classes in a
reducible local extension fiber remain as separate finite indices; none is declared a local
twisting torsor. Extension-completeness ensures that every such index is included in the
interpolation, and the global trace argument of Sections 6.3 and 11.3, rather than (6.4a),
determines which compatible global assembly occurs.

We may therefore regroup all completed blocks by their split good-place Hecke character.
Strong multiplicity one is used here only after the preceding trace argument has produced the
split cusp. The order-two Fourier orthogonality in (6.4) is orthogonality for the
norm-character action. For odd $\ell$, a fixed central-character block contains one member of each orbit.
For $\ell=2$, the two global $X(E/F)$ spectral coordinates give the order-two inverse Fourier matrix. On a free pair
$\{\pi,\pi\otimes\eta_{E/F}\}$ it changes the sum of two equal matching traces into their one
common value. More explicitly, on the sum of the two free isotypic spaces the normalized
twisting operator $U_\eta$ exchanges the summands, and hence

$$
\operatorname{tr}_{\mathcal H_\pi\oplus\mathcal H_{\pi\otimes\eta}}
R(f^0)=2\operatorname{tr}_{\mathcal O}(f^0),
\qquad
\operatorname{tr}_{\mathcal H_\pi\oplus\mathcal H_{\pi\otimes\eta}}
(R(f^0)U_\eta)=0.
\tag{6.5}
$$

Multiplication by $H_2^{-1}$ takes (6.5) to the single common trace. On an
$\eta_{E/F}$-stable cuspidal block, $U_\eta$ acts within the isotypic space and the second
coordinate is instead the genuine quadratic twisting distribution
$\operatorname{tr}(R(f^0)U_\eta)$. The independent theta-kernel identity proved in Lemma 10.1 identifies that
distribution with the two-character isobaric channel, on which the strongly cuspidal target
operator is zero. Hence precisely the free orbits in the middle term of (6.1) remain. This is
the promised scalar/quaternion spectral calculation; no inner-form block has been annihilated
by a local pseudo-coefficient.

Finally, Books 105--106 give absolute convergence of the twisted geometric and spectral
distributions. The ordinary trace formula gives the same for the split companion. Book 96's
bounded-window projectors are trace-norm limits of admissible multipliers, and all distributions
used above are continuous in that limit. We can therefore remove the smoothing approximation
to the projector and obtain (6.1) for $\mathscr W$; compatible directed limits are only those
stated immediately after the theorem. The relative discriminant identity and the full toral
product-one conversion are exactly those retained in Theorem 4.3. $\square$

The fixed-central identity is the right forward tool because $\omega_\pi$ is then known. For
reverse comparison we need the following genuinely different form.

**Proposition 6.2 (target-directed determinant-one comparison).** Fix a finite projected
window containing an antecedent-complete selected invariant target block of central character
$\Omega$, but do not choose a member of $\operatorname{Ant}(\Omega)$. On the
determinant-one trace quotients let $\mathcal O_\Omega^{\mathrm{fr},1}$ be the set of free
$X(E/F)$-orbits of selected cuspidal source representations whose central character belongs
to $\operatorname{Ant}(\Omega)$, each orbit counted once. For the determinant-one companion
$\mathbf f^1$ of Theorem 4.3,

$$
\boxed{
I_F^{\mathrm{bc,sel},1}(\mathbf f^1)
=\sum_{\mathcal O\in\mathcal O_\Omega^{\mathrm{fr},1}}
\operatorname{tr}_{\mathcal O}(f^{0,1})
=\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E;\mathscr W^1)\\
\Pi^\sigma\simeq\Pi}}
\operatorname{tr}\bigl(\Pi(\phi^1)A_\Pi^{\mathrm{aut}}\bigr).
}
\tag{6.6}
$$

Here the unitary normalization fixes the otherwise invisible common real norm twist on the
determinant-one group. In odd degree one $X(E/F)$-orbit meets all antecedent blocks because
squaring is bijective; in quadratic degree its members have one common central character, so
different antecedent blocks remain distinct in the displayed union.

**Proof.** Use Book 105's determinant-one geometric expansion, Book 106, Theorem 11.1, and the
determinant-one clause of Theorem 4.3; use the ordinary determinant-one simple trace formula
on the source groups. Regular classes and their full/relative discriminants compare exactly as in
Theorem 6.1. For a split scalar retain its rational value $a$ and quotient volume instead of
Fourier-projecting by $\omega$; for a nonsplit quadratic scalar retain the complete
$B_a^\times$ channel. Consequently the restricted-tensor globalization loses no central
coordinate and makes no choice of a norm antecedent.

Apply the same block inversion (6.3a), Book 96 character-clean comparison, and Brauer-sign
orthogonality (6.4a). These operations use complete inner-form trace formulas, so every
quaternionic noncharacter block is carried to the split cuspidal spectrum and no such block is
annihilated. Formally, Book 96 is applied after Fourier disintegration along the compact
norm-one center. Take the Fourier coefficient defined by the restriction of $\Omega$; its
source lifts are precisely the finite torsor $\operatorname{Ant}(\Omega)$. Applying Book 96
to those finitely many fixed-central summands and adding them reconstructs the required
determinant-one coordinate. Finally apply the full character table of
$X(E/F)$ to the compact determinant
quotient. On the direct sum of an $X$-orbit the nonidentity twisting operators permute the
isotypic summands without fixed diagonal blocks, so character orthogonality changes the sum of
$|X|$ equal traces into their one common orbit trace. For $\ell=2$ this is the
$H_2^{-1}$ calculation (6.5); for odd $\ell$ it is the same cyclic Fourier calculation of
order $\ell$. This is a transform on the source $X(E/F)$-orbit, not on the set of
central-character antecedents. The distinction is why (6.6) counts every source orbit once
while allowing its central character to emerge from the trace.

Exact target type/Hecke interpolation gives the projected right side. On the source, the
compact-type projectors remove rows outside the selected category, and
antecedent-completeness retains every admissible extension in every determinant slice which
can contribute. The determinant character identity in the local matching theorem, followed
by Fourier orthogonality on the compact idele-class determinant quotient, makes precisely the
slices with $\omega_\pi\circ N=\Omega$ survive. The finite-window and trace-norm limiting
arguments of Theorem 6.1 then give
(6.6). This proof uses only geometric matching and the independent Book 96 comparison; it
does not assume descent. $\square$

The strongly cuspidal row is indispensable. If a packet admits no such row in
$\mathscr T^{\mathrm{sel}}$, the simple comparison proved here does not transfer it. Likewise,
quadratic degree requires the complete family $\mathbf f$; omitting the quaternion terms would
invalidate the completed identities (6.1) and (6.6).

### 6.2 Annihilation of the induced spectrum

Normalized induction does commute with norm pullback:

$$
\mathcal I_F(\mu_1,\mu_2)
\longmapsto
\mathcal I_E(\mu_1\circ N_{E/F},\mu_2\circ N_{E/F}).
$$

This identity is useful for describing an isobaric output, but no induced term occurs in the
simple spectral equality of Section 6.1. The strongly cuspidal local factor acts by zero on
every induced representation, and hence on the continuous and residual spectra. The title of
this section therefore means operator annihilation, not cancellation of two meromorphic
integrals.

The distinction prevents a circular proof. A quadratic self-twist cannot be detected by
claiming that a half-weight cusp term moves into an Eisenstein integral that the test operator
has already killed. Chapter 10 instead constructs the two inducing characters, proves their
distinctness, and verifies their local restrictions directly.

### 6.3 Isolating one Hecke eigensystem

Fix a cuspidal $\pi$ over $F$ and choose a finite set $S$ containing the archimedean
places, all places ramified in $E/F$, and all places where $\pi$ or its central
character is ramified. Outside $S$, the spherical Hecke algebra is commutative. Its
characters attached to distinct cuspidal representations are linearly independent.

Place $\pi$ and all source and quaternionic constituents meeting its level, compact types, and
bounded archimedean window in one finite list. At the distinguished place choose a strongly
cuspidal row in $\mathscr T_v^{\mathrm{sel}}$. At the remaining places of $S$ use the type and
regular-slice rows of Theorem 4.2. At finitely many good places apply Lagrange interpolation
in the spherical base-change algebra. This isolates the finite **matching-trace class**
$\mathfrak C$ containing the free $X(E/F)$-orbit of $\pi$. We do not assume that matching
functions already distinguish two global orbits having identical restricted local data.

Normalize the common orbit trace to one. Let $n$ be the number of free source orbits in
$\mathfrak C$. The middle term of (6.1) is then $n\ge1$. On the target side, the corresponding
type and Hecke interpolation normalizes each surviving twisted trace to one, while strong
multiplicity one permits at most one invariant cuspidal representation with the complete
good-place character. Hence the right side is either zero or one. Equality (6.1) forces it
to be one and simultaneously forces $n=1$. Thus the comparison itself proves that the selected
source orbit is not accompanied by a second global orbit with the same matching data. The
quaternionic terms which occur before completion have already been transferred and regrouped
by Theorem 6.1, so they cannot cancel the positive integer $n$ invisibly.

Thus, provided $\pi$ has no quadratic norm-character self-twist, there exists a cuspidal
automorphic representation $\Pi$ over $E$ such that at every
unramified $w\mid v$ outside $S$,

$$
\operatorname{Sat}(\Pi_w)
=\{\alpha_v^{f_v},\beta_v^{f_v}\}.
$$

The no-self-twist condition is exactly what places the source in
$\mathcal O_\omega^{\mathrm{fr}}$; a quadratic fixed orbit has zero coefficient in (6.1) and is
handled by Chapter 10. This is the first existence statement. At this stage the components at
$S$ have not yet been identified. Notice that the argument used only the finite matching
category, not an unsupported transfer for an arbitrary smooth source function.

### 6.4 Recovering a ramified or archimedean component

Fix $v_0\in S$. At every other place choose rows whose trace on the already isolated orbit and
target representation is nonzero, and normalize their product to one. Now vary
$\phi_{v_0}$ through $\mathscr T_{v_0}^{\mathrm{sel}}$ and construct its companions by Theorem
4.2. The direction is important: we do not vary an arbitrary $f_{v_0}$ and assert that it has
a partner. Factorization of (6.1) gives

$$
\operatorname{tr}\pi_{v_0}(f^0_{v_0})
=\operatorname{tr}\bigl(
\Pi_{v_0}^E(\phi_{v_0})A_{\sigma,v_0}
\bigr)
$$

for every row of the matching category. Theorem 4.1 gives the same left side as the twisted
trace of the already constructed local candidate
$\bigotimes_{w\mid v_0}\operatorname{BC}_{E_w/F_{v_0}}(\pi_{v_0})$. Subtracting the two
identities and applying the finite-window separation clause of Theorem 4.2 gives

$$
\Pi_w\cong\operatorname{BC}_{E_w/F_{v_0}}(\pi_{v_0})
\qquad(w\mid v_0).
$$

This remains valid when the restricted parameter is reducible: separation is performed on the
two representations over $E_{v_0}$, not by pretending that the set of its extensions is a
torsor. The argument applies at a selected ramified finite place and for the cohomological
infinity types matched in Book 107. Therefore the global construction has the prescribed local
component at **every** place in the declared range, not merely at almost every place.

## 7. Construction and uniqueness of the lift

### 7.1 The global existence theorem

We can now name the object produced by the comparison.

**Theorem 7.1 (prime cyclic base change in the free selected case).** Let $E/F$ be cyclic of
prime degree $\ell$, and let $\pi$ be a selected, trace-comparable cuspidal representation of
$\mathrm{GL}_2(\mathbb A_F)$ whose restricted local parameters are extension-complete
selected relative to $\omega_\pi$. Assume

$$
\pi\otimes\chi\not\simeq\pi
\qquad(1\ne\chi\in X(E/F)).
$$

There is a unique cuspidal automorphic representation

$$
\operatorname{BC}_{E/F}(\pi)
$$

of $\mathrm{GL}_2(\mathbb A_E)$ such that for every place $v$ of $F$ and every
$w\mid v$,

$$
\operatorname{BC}_{E/F}(\pi)_w
\cong\operatorname{BC}_{E_w/F_v}(\pi_v).
$$

It is invariant under $\Gamma$.

**Proof strategy.** The completed identity (6.1) gives the free source orbit coefficient one
common trace after every quaternionic block has been carried through the Book 96 comparison.
It therefore constructs a cuspidal target with the expected good-place Hecke data. Directed
variation inside $\mathscr T_v^{\mathrm{sel}}$ identifies every component, and strong
multiplicity one gives uniqueness.

**Proof.** Sections 6.3 and 6.4 give cuspidal existence and the all-place local identities.
The Galois action permutes the local factors of the
candidate exactly as in Section 2.3; hence $\Pi^\sigma$ has the same components as
$\Pi$ at every place, and strong multiplicity one gives invariance. If two cuspidal
representations have the required local components, they agree outside a finite set, so the
strong multiplicity-one theorem of Book 95 gives their isomorphism. $\square$

Chapter 10 proves that the hypothesis is automatic for odd $\ell$. When $\ell=2$ it also
constructs the excluded self-twist case directly as an isobaric sum of two distinct Hecke
characters. Combining that construction with Theorem 7.1 yields the complete prime-degree
theorem stated in Chapter 16. Repeated isobaric sums can occur when the source is already
isobaric; that reducible input is a different case.

### 7.2 Uniqueness needs less data than existence

Once automorphy is known, it is enough to know the Satake parameters at all but
finitely many places. Thus one could characterize the lift by

$$
\operatorname{Sat}(\Pi_w)
=\{\alpha_v^{f_v},\beta_v^{f_v}\}
$$

at good places. This characterization proves uniqueness but not all-place local
compatibility: the conductor, monodromy, and archimedean component are invisible in
the omitted set. The trace-formula variation in Section 6.4 is what proves those data.

This distinction is useful in applications. To recognize an already constructed
candidate, compare its good Hecke eigenvalues. To calculate its level or local type,
return to the local restriction theorem.

### 7.3 Galois invariance

For $\tau\in\Gamma$, define

$$
\Pi^\tau(g)=\Pi(\tau^{-1}g).
$$

If $w\mid v$, then

$$
(\Pi^\tau)_w\cong\Pi_{\tau^{-1}w}^{\tau}.
$$

Both this representation and $\Pi_w$ have the restriction of the same
$F_v$-parameter to $E_w$. Therefore

$$
\boxed{\operatorname{BC}_{E/F}(\pi)^\tau
\cong\operatorname{BC}_{E/F}(\pi).}
$$

The isomorphism class is canonical; an intertwiner is not. Whittaker normalization
chooses intertwiners satisfying the cyclic relation and is the normalization used in
the twisted trace formula.

### 7.4 Twists, duals, and central characters

The all-place theorem and the corresponding local identities immediately yield

$$
\omega_{\operatorname{BC}\pi}=\omega_\pi\circ N_{E/F},
$$

$$
\operatorname{BC}(\pi\otimes\mu)
\cong\operatorname{BC}(\pi)\otimes(\mu\circ N_{E/F}),
$$

$$
\operatorname{BC}(\pi^\vee)
\cong\operatorname{BC}(\pi)^\vee.
$$

where the twisting formula is asserted whenever $\pi\otimes\mu$ remains in the theorem's
selected, extension-complete, trace-comparable range. The proof is not a new trace comparison. Each pair has identical local components by the
finite and archimedean restriction theory of Books 81 and 107, and global uniqueness
identifies them. In particular, a norm character
$\chi\in X(E/F)$ acts trivially after base change.

## 8. Unramified Hecke data and global factors

The existence proof becomes useful only after its spectral output is translated back into
arithmetic data. This chapter performs that translation for the cuspidal lift of Theorem 7.1.
Every formula also holds for the quadratic isobaric lift constructed in Chapter 10, because
there it reduces to the corresponding identity for its two character constituents. Nothing in
the calculations below is used to manufacture that exceptional lift, so the order is not
circular.

### 8.1 Residue-degree formulas

Let $v$ be a finite place where $E/F$ and $\pi_v$ are unramified, and let
$w\mid v$. Write

$$
P_v(X)=(1-\alpha_vX)(1-\beta_vX).
$$

Then

$$
P_w^{\mathrm{BC}}(X)
=(1-\alpha_v^{f_v}X)(1-\beta_v^{f_v}X).
$$

For the raw double-coset operator

$$
T_w=\mathbf1_{K_w\operatorname{diag}(\varpi_w,1)K_w},
\qquad \operatorname{vol}(K_w)=1,
$$

the eigenvalue is

$$
q_w^{1/2}(\alpha_v^{f_v}+\beta_v^{f_v}),
\qquad q_w=q_v^{f_v}.
$$

The central scalar operator has eigenvalue $(\alpha_v\beta_v)^{f_v}$. When $v$
splits completely, $f_v=1$ and the same polynomial occurs at each of the $\ell$ places.
When $v$ is inert and unramified, $f_v=\ell$ and there is one polynomial with the
$\ell$th powers. If $v$ has $g_v$ primes and local residue degree $f_v$, there are
$g_v$ identical conjugate polynomials with $f_v$th powers.

### 8.2 A worked unramified quadratic calculation

Assume $v$ is inert in a quadratic unramified extension and

$$
P_v(X)=1-A_vX+B_vX^2.
$$

Then

$$
P_w^{\mathrm{BC}}(X)
=1-(A_v^2-2B_v)X+B_v^2X^2.
$$

If one incorrectly raised $A_v$ itself to the second power, the middle term
$-2B_v$ would be lost. If one used the total degree at a ramified quadratic place,
one would also square the roots there, although $f_v=1$. Both mistakes come from
forgetting that Frobenius, not field dimension, acts on the unramified parameter.

### 8.3 Standard $L$-functions

Let $S$ contain the ramified places. Multiplying the local induction--restriction
identity of Book 81 over all places gives

$$
\boxed{
L_E^S(s,\operatorname{BC}_{E/F}\pi)
=\prod_{\chi\in X(E/F)}L_F^S(s,\pi\otimes\chi).
}
$$

The formula remains valid for completed $L$-functions when every local factor,
including the archimedean factors, is included in the same normalization. It is
compatible with the unramified residue-degree calculation because the Euler factors
on the right sort the primes of $E$ through the character orthogonality relations of
$\Gamma$.

For epsilon factors one must choose an additive character
$\psi_F:F\backslash\mathbb A_F\to\mathbb C^\times$ and set

$$
\psi_E=\psi_F\circ\operatorname{Tr}_{E/F}.
$$

The local lambda constants in Book 81 multiply globally to one. Hence

$$
\epsilon_E(s,\operatorname{BC}\pi,\psi_E)
=\prod_{\chi\in X(E/F)}
\epsilon_F(s,\pi\otimes\chi,\psi_F).
$$

Choosing conductor-zero additive characters independently at every place would
generally violate trace compatibility at ramified places and would introduce
spurious different factors.

### 8.4 Conductors are local, not a norm of ideals

The global conductor is

$$
\mathfrak f_E(\operatorname{BC}\pi)
=\prod_{w<\infty}\mathfrak p_w^{a_w(\operatorname{BC}\pi)}.
$$

There is no universal identity saying that this ideal is simply
$\mathfrak f_F(\pi)\mathcal O_E$ or its norm. At each $w\mid v$, the exact exponent is
the conductor of the restricted Weil--Deligne parameter. Put

$$
\Delta_{w/v}=v_v(\mathfrak d_{E_w/F_v})
=f_v\,v_w(\mathfrak D_{E_w/F_v}),
$$

the exponent downstairs of the local discriminant, equivalently the residue-degree
multiple of the upstairs different exponent, and put

$$
X(E_w/F_v)=\operatorname{Hom}
\bigl(F_v^\times/N_{E_w/F_v}(E_w^\times),\mathbb C^\times\bigr).
$$

Book 81 expresses conductor change
through upper ramification breaks and, in aggregate, through

$$
f(E_w/F_v)a_w(\operatorname{BC}\pi_v)
=\sum_{\eta\in X(E_w/F_v)}a_v(\pi_v\otimes\eta)
-2\Delta_{w/v}.
$$

For an unramified local extension, the exponent is unchanged. At a ramified extension
it can increase, stay fixed, or decrease: restriction can erase an inertial character,
Herbrand reindexing can change positive breaks, and monodromy contributes separately.

For example, an unramified Steinberg twist always remains Steinberg and has exponent
$1$, even under a totally ramified extension of large degree. By contrast, a
supercuspidal induced from a quadratic field contained in $E_w$ can become principal
series; its conductor is then the sum of the two restricted character conductors.

## 9. Archimedean components and local types

### 9.1 Why infinity belongs in the all-place theorem

An assertion about base change that records only finite Hecke eigenvalues is
insufficient for arithmetic applications. Holomorphicity, cohomological degree,
parity, and algebraic weight are encoded at infinity. A real place of $F$ may remain
real at every place above it, or it may become complex. A complex place can only split
into complex places. These alternatives must be treated through local parameters just
like finite decomposition types.

At a real place $v$, the local Weil group is

$$
W_{\mathbb R}=\mathbb C^\times\sqcup j\mathbb C^\times,
\qquad j^2=-1,\qquad jzj^{-1}=\bar z,
$$

whereas $W_{\mathbb C}=\mathbb C^\times$. If a real place becomes complex, local base
change is restriction from $W_{\mathbb R}$ to $W_{\mathbb C}$. Thus a discrete-series
parameter

$$
\operatorname{Ind}_{W_{\mathbb C}}^{W_{\mathbb R}}
(z^p\bar z^q),\qquad p\ne q,
$$

becomes

$$
z^p\bar z^q\oplus z^q\bar z^p.
$$

On $\mathrm{GL}_2(\mathbb C)$ this is a principal-series parameter. The representation
has not lost regularity: the two characters remain distinct. It has changed from a
real discrete series to a complex principal series because the complex group has no
discrete series modulo center.

### 9.2 Real places that stay real

If $E_w=F_v=\mathbb R$, the local extension is trivial and the component is unchanged.
In a cyclic extension, a real place either splits into real places or has decomposition
group of order two and becomes complex. Hence there is no higher-degree archimedean
field extension to consider.

Suppose $v$ splits into $\ell$ real places. Each factor of the lift is the same real
representation $\pi_v$, transported by the embeddings. If $v$ becomes complex, there
are $\ell/2$ complex places above it, each with the restricted parameter described above.
The equality

$$
\ell=g_v[ E_w:F_v]
$$

therefore remains valid at infinity with local degree one or two.

Finite-order sign characters illustrate what restriction forgets. The sign character
of $\mathbb R^\times$ is trivial after pullback along
$N_{\mathbb C/\mathbb R}(z)=|z|^2$. Thus two real representations differing by the
quadratic character associated with $\mathbb C/\mathbb R$ have the same complex base
change. This is the archimedean shadow of the global twisting fiber.

### 9.3 Principal, special, and supercuspidal types at finite places

At a finite place, every local type is computed before it is named upstairs. If

$$
\pi_v=I(\chi_{1,v},\chi_{2,v})
$$

is an irreducible principal series, then

$$
\operatorname{BC}_{E_w/F_v}(\pi_v)
=I(\chi_{1,v}\circ N_{E_w/F_v},
\chi_{2,v}\circ N_{E_w/F_v}),
$$

with the correct irreducible constituent taken if the inducing ratio reaches the
reducibility boundary. One must inspect the monodromy operator to distinguish a
determinant character from a Steinberg constituent at that boundary.

For a special representation,

$$
\operatorname{BC}_{E_w/F_v}
(\operatorname{St}_{F_v}\otimes\mu_v)
=\operatorname{St}_{E_w}\otimes
(\mu_v\circ N_{E_w/F_v}).
$$

Nonzero monodromy survives every restriction, so a special representation never
becomes principal merely because its semisimplification splits.

For a selected dihedral supercuspidal $\pi_v$, the lift remains supercuspidal exactly when the
restricted two-dimensional Weil representation remains irreducible. If it splits as
$\xi_1\oplus\xi_2$, cyclic Clifford theory says $\xi_1\ne\xi_2$, and the lift is the
principal-series representation attached to those characters. A repeated character
can arise by restricting an already split local parameter, but never by restricting
this irreducible two-dimensional parameter through the cyclic decomposition quotient.
In particular, “base change preserves supercuspidality” is false even for unramified
extensions.

### 9.4 Local $L$-packets are not an extra ambiguity

Within the selected local dictionary for $\mathrm{GL}_2$, a parameter determines a single
irreducible admissible representation. There is no packet choice to coordinate globally. This singleton
property is one reason the trace formula can recover the component at a ramified place
from its twisted character.

The inner-form situation is different: a discrete parameter may also label a representation
of a quaternion division group. Quadratic inner forms enter this book only as the scalar
geometric correction required by the completed trace comparison. The fact that a quaternion
algebra occurs as a twisted centralizer is not a second choice inside a $\mathrm{GL}_2$ packet.

## 10. The cuspidality criterion

### 10.1 Why self-twists are the only obstruction

The completed source comparison of Theorem 6.1 constructs a cuspidal lift on a free
norm-character orbit. When a quadratic self-twist is present, its coherent quaternionic scalar
completion prevents that source term from being mistaken for a cuspidal target. To identify what replaces it, we need a
global monomiality statement. We include the required quadratic construction and its proof here
so that the cuspidality argument has no hidden automorphic-induction premise.

We first record the global monomiality input rather than conceal it inside the
cuspidality proof.

**Lemma 10.1 (quadratic self-twists in the selected range).** Let $\eta$ be a nontrivial
quadratic Hecke character of $F$, and let $M/F$ be the quadratic extension it cuts out. A
selected trace-comparable cuspidal representation $\pi$ satisfies
$\pi\otimes\eta\cong\pi$ if and only if

$$
\pi\cong\operatorname{AI}_{M/F}(\theta)
$$

for a Hecke character $\theta$ of $M$ with $\theta\ne\theta^\tau$.

**Proof strategy.** We first construct quadratic induction from a Hecke character by a theta
kernel and calculate its local parameter. For the converse, we compare the trace of the
quadratic twisting operator with the theta trace by unfolding both kernels along the norm
torus. Exact selectors force a theta constituent with the same Hecke data as the given
self-twisted representation, and strong multiplicity one identifies them.

**Proof.** Fix a nontrivial additive character $\psi$ of $F\backslash\mathbb A_F$ and regard
$M$ as the two-dimensional quadratic space with form $N_{M/F}$. Use the similitude Weil
representation for $\operatorname{GSO}(M)\simeq\operatorname{Res}_{M/F}\mathbf G_m$ and
$\mathrm{GL}_2$. For a Hecke character $\theta$ of $C_M$ and a Schwartz function $\Phi$, it
gives the centrally covariant theta integral

$$
\Theta_{\theta,\Phi}(g)
=\int_{M^\times\mathbb A_F^\times\backslash\mathbb A_M^\times}
\theta(t)K_\Phi(g,t)\,dt.
$$

Here the central covariance built into $K_\Phi$ cancels the value of $\theta$ on the displayed
$\mathbb A_F^\times$; equivalently one may define the integral on the matched-similitude
quotient before dividing by the common center. The quotient torus is compact. The zero vector
in the theta kernel gives the constant term. Poisson summation proves automorphy, and removing
that zero-vector term makes the remaining kernel rapidly decreasing. Unfolding along the upper
unipotent gives its Whittaker coefficient as the product of the local Fourier transforms of
$\Phi$. Hence the span of these theta integrals is a nonzero generic automorphic
representation. At a place $v$, the same unfolding separates the two embeddings of $M_v$ and
gives the local Weil parameter

$$
\operatorname{Ind}_{W_{M_v}}^{W_{F_v}}\theta_v.
$$

If $M_v=F_v\times F_v$, this says normalized induction from the two local characters; if
$M_v$ is a field, it is the usual quadratic induced parameter. The constant term vanishes for
all $\Phi$ exactly when $\theta\ne\theta^\tau$. Thus in that case the representation, denoted
$\operatorname{AI}_{M/F}(\theta)$, is cuspidal. If $\theta=\theta^\tau$, Hilbert 90 extends
$\theta$ to a character $\mu$ of $C_F$ and the theta space is the isobaric sum
$\mu\boxplus\mu\eta$; it is not cuspidal. This proves the construction and its cuspidality
criterion without presupposing base change.

It remains to prove that every self-twist is obtained this way. This is the quadratic
monomiality comparison, whose short rank-two proof we now give. Let $U_\eta$ multiply an
automorphic function by $\eta(\det g)$. Then $U_\eta$ carries the $\pi'$-isotypic subspace to
the $\pi'\otimes\eta$-subspace. For a strongly cuspidal test function $f$, the trace of
$R(f)U_\eta$ is therefore a sum only over $\eta$-stable cuspidal representations, with the
self-intertwiner normalized in the Whittaker model.

Unfold the diagonal kernel of this operator along the index-two determinant subgroup
$N_{M/F}(C_M)$. Regular orbits are classified by the two eigenlines over $M$; the two choices
are exchanged by $\tau$. On such an orbit, change variables from the eigenline to
$M^\times\mathbb A_F^\times\backslash\mathbb A_M^\times$. The orbital integral becomes the
Fourier coefficient of the theta kernel $K_\Phi(g,t)$ constructed above. Nonsplit scalar
orbits give the zero-vector constant term, and strong cuspidality removes them. Split and
nonsemisimple orbits lie in the single parabolic channel and vanish for the same reason.
Poisson summation on the two-dimensional space $M$ identifies the remaining geometric sum with
the theta trace. Thus

$$
\operatorname{tr}(R(f)U_\eta)
=\sum_{\{\theta,\theta^\tau\}}
\operatorname{tr}\bigl(\operatorname{AI}_{M/F}(\theta)(f)\bigr),
$$

where the sum runs over non-$\tau$-invariant Hecke characters having the fixed central
character and selected local types imposed by $f$. Both sides are absolutely convergent: the
strongly cuspidal factor makes the kernels rapidly decreasing, and the remaining torus
quotient is compact. This proves the quadratic monomiality identity directly from the same
kernel-unfolding principles used in Chapters 5 and 6.

Now assume $T:\pi\to\pi\otimes\eta$ is an isomorphism. Scale $T$ so that $T^2=1$ and transport
it to the global Whittaker model. Since

$$
T\pi\!\begin{pmatrix}y&0\\0&1\end{pmatrix}
=\eta(y)\pi\!\begin{pmatrix}y&0\\0&1\end{pmatrix}T,
$$

finite compact-type and good-place Hecke interpolation in a bounded archimedean window gives a
strongly cuspidal tensor for which the normalized contribution of $\pi$ to the left side is
one and every other self-twisted constituent in that window has trace zero. This uses only
compact-type Schur orthogonality, the bounded multipliers of Books 95--96, and finitely many
spherical Hecke operators; it is not an idempotent for an arbitrary isolated point of the full
automorphic dual. The monomiality identity forces a character $\theta$ on
the right. Varying the unramified Hecke factors shows that the theta representation and $\pi$
have the same Hecke polynomial outside a finite set; varying the selected ramified factors
gives the matching local types as well.

At every unramified place, the local theta unfolding gives

$$
P_v(\pi;X)
=\det\!\left(1-X\operatorname{Ind}_{W_{M_v}}^{W_{F_v}}\theta_v(\operatorname{Fr}_v)
\right).
$$

The theta representation constructed above therefore has the same unramified Hecke polynomial
as $\pi$ outside a finite set. Strong multiplicity one from Book 95 yields
$\pi\simeq\operatorname{AI}_{M/F}(\theta)$. Since $\pi$ is cuspidal, the preceding constant-
term calculation forces $\theta\ne\theta^\tau$. Conversely, induction from the index-two Weil
subgroup is unchanged after tensoring with its quotient character $\eta$, so the local
components of $\operatorname{AI}_{M/F}(\theta)$ and its $\eta$-twist agree everywhere; strong
multiplicity one gives the self-twist. $\square$

The lemma is global: a collection of local quadratic symmetries would not by itself
produce the single Hecke character $\theta$.

**Theorem 10.2 (cuspidality criterion).** Let $E/F$ have prime degree $\ell$, and let $\pi$
be selected and trace-comparable as in Chapter 1. Then the automorphic base change constructed
in Theorem 7.1 and below is cuspidal if and only if

$$
\pi\otimes\chi\not\cong\pi
$$

for every nontrivial $\chi\in X(E/F)$.

**Proof strategy.** A self-twist has order two by comparison of central characters. Prime
degree then forces $\ell=2$ and the quadratic field is $E$ itself. Lemma 10.1 writes $\pi$ as
quadratic induction, whose restriction is the sum of its two character lines. If there is no
self-twist, Theorem 7.1 constructs a cuspidal lift. These two cases exhaust the theorem.

**Proof.** Suppose $\pi\otimes\chi\cong\pi$. Equality of central characters gives

$$
\omega_\pi\chi^2=\omega_\pi,
$$

so $\chi^2=1$. Since $\chi$ is nontrivial, it is quadratic. Let $M/F$ be the quadratic
extension cut out by $\chi$. Lemma 10.1 gives

$$
\pi\cong\operatorname{AI}_{M/F}(\theta)
$$

for a Hecke character $\theta$ of $C_M$ with $\theta\ne\theta^\tau$. Since
$\chi\in X(E/F)$, class field theory says $M\subseteq E$. Prime degree forces
$\ell=2$ and $M=E$. Restriction to $E$ then splits the induced parameter into the two
character lines

$$
\theta,\qquad\theta^\tau.
$$

Therefore

$$
\operatorname{BC}_{E/F}(\pi)
=\theta\boxplus\theta^\tau,
$$

which is not cuspidal. Its local component at every $w$ is the restriction of the induced
local parameter, so this is the required automorphic isobaric base change; its two constituents
are distinct by Lemma 10.1.

If there is no nontrivial self-twist, Theorem 7.1 constructs a cuspidal lift. Conversely, the
explicit self-twist case just constructed is noncuspidal. These alternatives exhaust
$X(E/F)$ and prove the equivalence. Finally, the exceptional isobaric sum is unique: if
$\xi_1\boxplus\xi_2$ has the same unramified polynomials as
$\theta\boxplus\theta^\tau$, comparison of the degree-one Euler factors after twisting by
$\xi_i^{-1}$ shows that one $\xi_i$ equals one of $\theta,\theta^\tau$; equality of
determinants gives the other. This is the elementary $\mathrm{GL}_1$ multiplicity-one
argument, so no isobaric uniqueness theorem is being silently imported. $\square$

The proof shows more than noncuspidality: it constructs the only Eisenstein output and proves
that its two constituents are distinct and have multiplicity one. The distinctness is also the
global cyclic analogue of Book 81, Section 9.1.

### 10.2 Odd degree

If the prime $\ell$ is odd, the cyclic group $X(E/F)$ has no nontrivial quadratic character. Since
every self-twist of a cuspidal rank-two representation lying in $X(E/F)$ would have to
be quadratic, no such self-twist exists. Therefore

$$
\boxed{[E:F]\text{ odd}\quad\Longrightarrow\quad
\operatorname{BC}_{E/F}(\pi)\text{ is cuspidal}.}
$$

This conclusion is special to rank two. In rank $m$, a cuspidal representation can
have a self-twist of order dividing $m$, so oddness of the extension alone would not
give the same statement for arbitrary $m$.

An odd-degree local restriction may still change a principal-series reducibility
boundary, but a two-dimensional irreducible Weil representation cannot split upon
restriction to an odd-index normal subgroup. The global and local parity phenomena
therefore reinforce each other.

### 10.3 Quadratic degree and the exceptional isobaric sum

The only even prime degree is $\ell=2$. Now $E/F$ itself is quadratic and $X(E/F)$ has the
single nontrivial character $\eta_{E/F}$. The criterion
becomes

$$
\operatorname{BC}_{E/F}(\pi)\text{ noncuspidal}
\quad\Longleftrightarrow\quad
\pi\otimes\eta_{E/F}\cong\pi.
$$

Equivalently,

$$
\pi\cong\operatorname{AI}_{E/F}(\theta)
$$

for a non-$\tau$-invariant Hecke character $\theta$ of $E$. There is no higher-order
self-twist hiding elsewhere: central characters force the square of every self-twist to be
trivial, and $X(E/F)$ has order two.

The output is exactly

$$
\boxed{
\operatorname{BC}_{E/F}(\operatorname{AI}_{E/F}\theta)
=\theta\boxplus\theta^\tau.
}
$$

The two displayed characters are necessarily distinct. Indeed, regularity
$\theta\ne\theta^\tau$ makes the two-dimensional induced parameter
$\operatorname{Ind}_{W_E}^{W_F}\theta$ irreducible. Its restriction to the normal
subgroup $W_E$ has cyclic quotient $\operatorname{Gal}(E/F)$. By the Clifford-theory
argument of Book 81, Section 9.1, a reducible restriction of such an irreducible
two-dimensional parameter is a sum of two distinct characters, never two copies of
one character. Thus

$$
\theta\ne\theta^\tau.
$$

Equivalently, the nontrivial member of $\Gamma$ exchanges the two constituents. Their
$\Gamma$-orbit has size two, and each occurs with multiplicity one.

This conclusion uses both irreducibility downstairs and cyclicity of the total
quotient. It does not say that distinct characters in reducible data always remain
distinct. If $\Sigma=\mu_1\boxplus\mu_2$ is already isobaric over $F$, then

$$
\operatorname{BC}_{E/F}(\Sigma)
=(\mu_1\circ N_{E/F})\boxplus(\mu_2\circ N_{E/F}),
$$

and its two constituents are equal exactly when
$\mu_1\mu_2^{-1}\in X(E/F)$. A repeated sum is allowed in that reducible-source
case. This distinction persists in tower arguments: noncyclic total restriction may have a
projective multiplicity phenomenon, but a single prime cyclic base change of a cuspidal
rank-two source cannot.

### 10.4 Why local splitting is not the criterion

A supercuspidal component of $\pi$ may become principal series at one place without
destroying global cuspidality. Conversely, the noncuspidal dihedral lift may have
irreducible principal-series components at almost every place. Cuspidality is governed
by the global character $\eta_{E/F}$ and the global isomorphism
$\pi\otimes\eta_{E/F}\cong\pi$, not by the type at any single place.

For instance, choose $v$ splitting in $E/F$. Then
$\pi_v$ attached to an automorphic induction is already principal series. At an inert
place it may be supercuspidal if the local inducing character is noninvariant. Both
local behaviors belong to the same cuspidal $\pi$ over $F$, and both become the two
distinct global character lines after global base change to $E$.

### 10.5 Self-twist order and orbit size

Let

$$
\operatorname{Stab}_X(\pi)
=\{\chi\in X(E/F):\pi\otimes\chi\cong\pi\}.
$$

For cuspidal $\pi$ this group is either trivial or the order-two group generated by
$\eta_{E/F}$. Hence the orbit has size

$$\frac \ell{|\operatorname{Stab}_X(\pi)|}=

\begin{cases}
\ell,&\operatorname{BC}\pi\text{ cuspidal},\\
1,&\operatorname{BC}\pi\text{ noncuspidal}.
\end{cases}
$$

In the quadratic noncuspidal case the source twisting orbit has one isomorphism class, whereas
the constituent orbit upstairs has two elements and each character occurs once. No ad hoc
$1/2$ is assigned to that source representation. The only factor $1/2$ is the inverse Fourier
coefficient in (6.4), which turns a free pair of equal traces into one orbit trace; the
quadratic division-centralizer terms enter that completed distribution before the fixed orbit
is sent to the theta channel.
This separates three notions that should never be conflated: stabilizer size, number of source
isomorphism classes, and multiplicity of isobaric constituents.

## 11. Descent, image, and fibers

### 11.1 The global image problem

Every base-change lift is $\Gamma$-invariant. Within the selected trace-comparable range, the
converse asks whether a $\Gamma$-invariant cuspidal representation $\Pi$ of
$\mathrm{GL}_2(\mathbb A_E)$ comes from $F$. Local invariance is not by itself a
global proof: local descents could fail to have compatible central characters, and an
abstract collection of local representations need not be automorphic. The reverse
twisted trace comparison supplies automorphy.

There are two layers of obstruction to state accurately:

1. the central character $\Omega=\omega_\Pi$ must factor through the global norm;
2. if a particular norm antecedent $\omega$ is prescribed, its square class must
   agree with the determinant of a representation descent.

For cyclic number-field extensions the first obstruction vanishes for an invariant
Hecke character, but it is useful to see why rather than omit it.

### 11.2 Descent of the central character

A character $\Omega$ of $C_E$ has the form

$$
\Omega=\omega\circ N_{E/F}
$$

if and only if it is trivial on $\ker(N_{E/F}:C_E\to C_F)$. For cyclic extensions,
the idele-class form of the cyclic norm theorem gives the exact identity

$$
\ker N_{E/F}=(1-\sigma)C_E.
$$

This is stronger than the elementwise Hasse norm theorem: it is the vanishing of the
negative cyclic cohomology group of $C_E$. If $\Omega$ is $\Gamma$-invariant, then

$$
\Omega(x/\sigma x)=1,
$$

so it is trivial on the kernel. It factors through $N(C_E)$, and because this subgroup
is open of finite index in $C_F$, the resulting continuous character extends to a
Hecke character $\omega$ of $C_F$. If $\Omega$ is unitary, choose the finitely many required
roots on the unit circle, so $\omega$ is unitary as well. Therefore every invariant central character has at
least one norm antecedent.

The antecedent is not unique. If $\omega$ and $\omega'$ have the same norm pullback,
then

$$
\omega'/\omega\in X(E/F).
$$

This ambiguity will interact with the square in the central character of a twist.

### 11.3 Descent theorem

**Theorem 11.1 (selected cuspidal descent).** Let $E/F$ have prime degree and let $\Pi$ be a
selected, trace-comparable cuspidal automorphic representation of
$\mathrm{GL}_2(\mathbb A_E)$. Assume its central character has a norm antecedent and its local
parameters are antecedent-complete selected in the sense of Section 1.2. Then the following
are equivalent:

1. $\Pi^\sigma\cong\Pi$;
2. there is a selected, trace-comparable, extension-complete cuspidal automorphic
   representation $\pi$ of $\mathrm{GL}_2(\mathbb A_F)$ such that
   $\operatorname{BC}_{E/F}(\pi)\cong\Pi$.

Every such descent is cuspidal.

**Proof strategy.** Necessity is Galois invariance of base change. For sufficiency,
choose a Whittaker-normalized cyclic intertwiner on $\Pi$ and insert $\Pi$ into the
determinant-one twisted spectral distribution, where no norm antecedent is chosen. The global
trace count forces one free split cuspidal orbit and lets its central character emerge
over $F$; a quaternionic block is first transported through Book 96 and is never declared
zero. The already proved fixed-central forward theorem then recovers the component at every
place.

**Proof.** If $\Pi=\operatorname{BC}(\pi)$, Theorem 7.1 gives invariance. Conversely,
assume invariance and normalize $A_\sigma$ in the global Whittaker model. Section 11.2 proves
that $\operatorname{Ant}(\Omega)$ is nonempty and is an $X(E/F)$-torsor. Choose a
determinant-one test $\phi^1$ having nonzero twisted
trace on $\Pi$. Put it in a fixed level, compact-type, and bounded archimedean window and use
Theorem 4.2 plus finitely many good Hecke operators to make its twisted trace one and the trace
of every other invariant target constituent in that window zero.
Form the determinant-one complete companion $\mathbf f^1$ and apply Proposition 6.2. Its
right side is one. Antecedent-completeness and Theorem 4.1 make the common normalized trace of
every source orbit in the determinant-one matching class equal to one. The middle term of
(6.6) is therefore the number of global free source orbits in that class. Equality with the
isolated target coefficient one proves at once that this number is exactly one. In
particular, the comparison produces both a cuspidal representation $\pi$ and its actual
central character $\omega_\pi\in\operatorname{Ant}(\Omega)$; it does not guess an antecedent
before running the trace. This is the global trace argument which selects a compatible
determinant slice and rules out incompatible global assemblies of the larger reducible local
extension fibers. The defining projectors make $\pi$ selected and trace-comparable, and
antecedent-completeness makes its $\omega_\pi$-slice extension-complete.

Before completion, a nonzero source coordinate can lie either on the split group or on a
quaternion group $B^\times$. A global quaternion norm character has already been removed by
the character-clean scalar interpolation in Theorem 6.1 and Proposition 6.2. A noncharacter block is
not removed: Book 96, Proposition 7.2 and Theorem 7.3, carry it by a global trace comparison to
a unique split cuspidal block with the same good Hecke data. This applies even if $B$ is not
totally definite. The inverse norm-character Fourier matrix then regroups all such blocks into a
free $X(E/F)$-orbit of cuspidal representations $\pi$ on
$\mathrm{GL}_2(\mathbb A_F)$. Thus automorphic existence is a consequence of a global trace
identity, not of assembling local extensions.

Now use the fixed-central forward theorem on this source. The slice for
$\omega_\pi$ is selected by antecedent-completeness, so Theorem 7.1 constructs
$\Pi'=\operatorname{BC}(\pi)$ with every prescribed local restriction. Return to (6.6), keep
the factors isolating the now unique source and target, and vary one determinant-one local row;
at an auxiliary unramified place insert the inverse determinant shell so that the adelic
module remains one. Theorem 4.1 and target separation then show that $\Pi'$ and $\Pi$ have
the same representation on $\mathrm{GL}_2(\mathbb A_E)^1$.

Every $g\in\mathrm{GL}_2(\mathbb A_E)$ can be written $g=zg^1$ with
$z\in Z(\mathbb A_E)$ and $g^1$ of determinant module one: choose an idele $z$ whose squared
module is $|\det g|$. The ambiguity in this decomposition lies in the norm-one center. Since
$\Pi'$ and $\Pi$ agree on the module-one group and both central characters equal
$\omega_\pi\circ N=\Omega$, their extensions to the full adelic group agree. Hence

$$
\Pi'=\operatorname{BC}_{E/F}(\pi)\cong\Pi.
$$

This equality and Theorem 7.1 recover the component at every place, including reducible
restricted parameters. The source in (6.6) is already the cuspidal spectrum, so $\pi$ is
cuspidal; no noncuspidal tensor has been promoted to a cusp form. $\square$

Thus, within the selected trace-comparable range, the global image among cuspidal
representations is exactly the invariant spectrum whose local parameters admit selected
extension-complete fibers for every norm antecedent. Existence of central-character
antecedents is automatic from invariance because $E/F$ is cyclic; antecedent-completeness of
their fixed-determinant slices is a separate selected-range hypothesis. Merely possessing one selected local
extension is insufficient at the wild boundary: the trace algebra sees the entire restriction
class, so that weaker assertion is deliberately not made.

### 11.4 The precise condition for a prescribed central character

Assume the source fiber is $X(E/F)$-saturated. Fix one descent $\pi_0$ of $\Pi$, and write
$\omega_0=\omega_{\pi_0}$. By Theorem 11.2 below, whose proof does not use the present
central-character calculation, every other descent has the form $\pi_0\otimes\chi$, with
central character

$$
\omega_0\chi^2,
\qquad \chi\in X(E/F).
$$

Now let $\omega$ be a specified character of $C_F$ satisfying
$\omega\circ N=\Omega$. Then $\omega/\omega_0\in X(E/F)$, and there is a descent with
central character exactly $\omega$ if and only if

$$
\boxed{\omega/\omega_0\in X(E/F)^2.}
$$

This is the determinant square-class obstruction. It is independent of the reference
descent: replacing $\pi_0$ by $\pi_0\otimes\chi_0$ multiplies $\omega_0$ by the square
$\chi_0^2$.

If $\ell$ is odd, squaring is an automorphism of the cyclic group $X(E/F)$, so every norm
antecedent $\omega$ occurs. If $\ell=2$, $X/X^2$ has order two. Exactly one of the
two square classes of norm antecedents occurs as a descent central character. Thus
the statement “$\Omega$ descends” is weaker than “a descent exists with this chosen
$\omega$.”

### 11.5 Fibers of base change

**Theorem 11.2 (selected cuspidal fibers).** Let $\pi$ and $\pi'$ satisfy the selected
prime-degree hypotheses of Chapter 1. If their base changes are isomorphic, then

$$
\pi'\cong\pi\otimes\chi
$$

for some $\chi\in X(E/F)$. Conversely every such twist that stays in the selected range has
the same base change. Under the $X(E/F)$-saturation hypothesis, this describes the full fiber.

**Proof strategy.** At almost every unramified place, equality after restriction says
that the two restricted Frobenius classes agree. We do **not** choose a quotient character at
each place: for a reducible restricted parameter the local extension fiber need not be one
twisting orbit. Instead, the reverse trace comparison gives global automorphic descents, and a
global Rankin--Selberg/induction identity forces any two of them to differ by one global member
of $X(E/F)$.

**Proof.** The converse is norm pullback compatibility. For the forward direction,
first suppose that the common lift $\Pi$ is cuspidal. The lifts of $\pi$ and $\pi'$ were
globally constructed by Theorem 7.1, so no tuple of local extensions is being promoted to an
automorphic representation in this argument.

Choose a finite set $S$ containing all ramified and archimedean places, and let $S_E$ be the
places of $E$ above it. Artin formalism for
the cyclic quotient gives, at every $v\notin S$, the local identity obtained from

$$
\operatorname{Ind}_{W_E}^{W_F}\mathbf1
=\bigoplus_{\chi\in X(E/F)}\chi.
$$

Multiplying the unramified factors gives the global incomplete identity

$$
L_E^{S_E}\!\left(s,\operatorname{BC}(\pi)\times
\operatorname{BC}(\pi')^\vee\right)
=\prod_{\chi\in X(E/F)}
L_F^S\!\left(s,\pi\times(\pi'\otimes\chi)^\vee\right).
\tag{11.1}
$$

This is a finite Euler-factor calculation, not an appeal to the fiber theorem: restriction of
the tensor-product parameter followed by induction is tensoring with
$\operatorname{Ind}_{W_E}^{W_F}\mathbf1$. Book 95 supplies meromorphic continuation and the
Rankin--Selberg pole criterion for every factor. Since the two base changes are the same
cuspidal $\Pi$, the left side of (11.1) has a pole at $s=1$. If no
$\pi'\otimes\chi$ were isomorphic to $\pi$, every factor on the right would be holomorphic at
$1$, and their finite product would be holomorphic, a contradiction. Hence

$$
\pi\cong\pi'\otimes\chi
$$

for some $\chi\in X(E/F)$, which is the assertion after replacing $\chi$ by its inverse.
No nonvanishing of a cross Rankin--Selberg value is needed.

If the common lift is noncuspidal, Theorem 10.2 makes the extension quadratic and writes every
cuspidal source as $\operatorname{AI}_{E/F}(\theta)$ for one of the two constituents of the
common sum $\theta\boxplus\theta^\tau$. Interchanging the constituents gives the same
automorphic induction, so there is one source isomorphism class; it is fixed by
$\eta_{E/F}$. This proves the theorem in the remaining case. $\square$

This proof is compatible with the larger local fibers in Book 81. For example,
$1\oplus1$ and $1\oplus\eta_v$ can have the same quadratic restriction without being common
local twists, and an invariant split parameter can have both principal and induced extension
classes. Theorem 11.1 uses the completed trace formula to prove that a reverse source exists,
while (11.1) says that any already automorphic **global cuspidal** sources form one
$X(E/F)$-orbit. No tuple of local quotient characters is patched, and no scalar-endomorphism
hypothesis is imposed.

Assume now that the source fiber is $X(E/F)$-saturated. If the common lift is cuspidal, the
$X$-action is free: a nontrivial stabilizer would
make the lift noncuspidal by Theorem 10.2. Hence the set of descents of a cuspidal
$\Pi$ is an $X(E/F)$-torsor and has exactly $\ell$ elements.

If the common lift is noncuspidal, the source $\pi$ has the quadratic stabilizer
$\{1,\eta_{E/F}\}$. The common lift has two distinct multiplicity-one character
constituents by Section 10.3, while its twisting fiber has one cuspidal member.
Saying that every fiber has $\ell$ elements, or confusing constituent
multiplicity with the number of sources, would therefore be false.

### 11.6 A counterexample involving only central characters

Assume $\ell=2$ and let $\eta$ be the unique quadratic member of $X(E/F)$. If the
common lift is cuspidal, then $\eta$ cannot stabilize a descent. Consequently
$\pi$ and $\pi\otimes\eta$ are two **distinct** descents, while $\eta^2=1$ shows that
they have the same central character as well as the same base change. Thus fixing the
central character does not remove all descent ambiguity in quadratic degree. At the
noncuspidal dihedral boundary the same quadratic character is instead the stabilizer,
so the two displayed twists are one isomorphism class; this is exactly why that fiber
has one rather than two elements.

Conversely, if $\chi$ generates $X(E/F)$ and $\ell$ is odd, the central characters
$\omega_\pi\chi^{2j}$ are all distinct as $j$ varies. Fixing one norm antecedent then
selects exactly one descent. This contrast is the concrete effect of the square-class
condition.

## 12. Algebraic weights and fields of rationality

### 12.1 Why algebraicity is a local restriction statement

The analytic construction of base change does not by itself say that algebraic
automorphic representations remain algebraic. That conclusion comes from the
archimedean local theorem. An algebraic parameter is described by integral characters
on $\mathbb C^\times$; restricting from a real Weil group or transporting between
complex embeddings preserves those exponents.

Suppose $\pi$ is regular algebraic and cohomological. At an embedding
$\tau:F\hookrightarrow\mathbb C$, write its algebraic weight as

$$
(a_\tau,b_\tau),\qquad a_\tau\ge b_\tau.
$$

For every embedding $\widetilde\tau:E\hookrightarrow\mathbb C$ extending $\tau$, the
base-change weight is

$$
(a_{\widetilde\tau},b_{\widetilde\tau})
=(a_\tau,b_\tau).
$$

Thus weights are pulled back along the restriction map on embeddings. They are
repeated at split archimedean places, while at a real place becoming complex the two
conjugate exponents become the two characters of the complex parameter.

If $a_\tau+b_\tau=w$ is independent of $\tau$, then the same purity weight $w$
occurs at every embedding of $E$. Regularity $a_\tau>b_\tau$ is preserved. The
cohomological coefficient system over $E$ is obtained by applying the corresponding
algebraic representation at every embedding above $\tau$.

### 12.2 Real-to-complex weight conversion

Take a holomorphic discrete series at a real place with lowest weight $k\ge2$ and an
algebraic determinant exponent $b$. Its coefficient-system pair is

$$
(a,b),\qquad a-b=k-2.
$$

After base change to $\mathbb C$, the parameter is the sum of conjugate characters.
The exponent difference is $k-1$ in the analytic Weil normalization and $k-2$ in the
algebraic coefficient normalization. Both encode the same infinitesimal character
after the standard half-sum shift.

Mixing these normalizations causes a false change of weight. Base change repeats the
algebraic pair $(a,b)$; it does not replace $k$ by $2k$, nor insert the extension
degree. The shift from $k-2$ to $k-1$ belongs to the passage between coefficient and
Weil parameters, not to base change.

### 12.3 Cohomological compatibility

**Proposition 12.1.** If $\pi$ is regular algebraic and cohomological, then every
cuspidal base change $\operatorname{BC}_{E/F}(\pi)$ is regular algebraic and
cohomological with weights pulled back along embeddings. If the base change is the
isobaric sum $\xi_1\boxplus\xi_2$, its two algebraic Hecke characters have the
corresponding pulled-back infinity types; for the noncuspidal lift of a cuspidal
source they are globally distinct, even if some of their local infinity types agree.

**Proof.** The local component at infinity is obtained by restricting the local Weil
parameter. Restriction preserves the integral exponents and their multiset. The
classification of cohomological representations of real and complex
$\mathrm{GL}_2$ translates this restricted parameter into the pulled-back coefficient
system. In the noncuspidal case the two character lines themselves carry those
exponents. $\square$

The qualifier “regular algebraic” matters. A general Maass representation can be base
changed, but the trace formula does not turn arbitrary complex spectral parameters
into algebraic integers.

### 12.4 Algebraic conjugation commutes with base change

Let $\iota\in\operatorname{Aut}(\mathbb C)$ act on algebraically normalized Hecke
eigenvalues and coefficient systems. At an unramified place, the base-change trace is
the integral polynomial

$$
P_{f_v}(A_v,B_v)=\alpha_v^{f_v}+\beta_v^{f_v}.
$$

Applying $\iota$ before or after this polynomial gives the same result. Strong
multiplicity one yields

$$
\boxed{
\operatorname{BC}_{E/F}(\pi^\iota)
\cong\operatorname{BC}_{E/F}(\pi)^\iota
}
$$

for cohomological representations, with the infinity type transported through its
algebraic coefficient system. The statement does not apply $\iota$ to an analytic
square root $q_v^{1/2}$: algebraically normalized Hecke polynomials carry the
number-field structure.

### 12.5 Fields of rationality can shrink

Let $\mathbb Q(\pi)$ denote the field of rationality of the finite part. Since every
lifted Hecke coefficient is a polynomial in the original trace and determinant,

$$
\mathbb Q(\operatorname{BC}\pi)\subseteq\mathbb Q(\pi)
$$

after the common algebraic normalization. Equality need not hold. If an automorphism
$\iota$ of the coefficient field satisfies

$$
\pi^\iota\cong\pi\otimes\chi
$$

for nontrivial $\chi\in X(E/F)$, then
$\operatorname{BC}(\pi)^\iota\cong\operatorname{BC}(\pi)$ even though
$\pi^\iota\not\cong\pi$.

More precisely, the stabilizer of the base-changed eigensystem consists of coefficient
automorphisms carrying $\pi$ into its $X(E/F)$-twisting orbit. The field upstairs is
the fixed field attached to this larger stabilizer. If no nontrivial coefficient
conjugate of $\pi$ is such a twist, the two fields agree.

This concerns fields of rationality, not fields of definition. A representation model,
a chosen local type, or a Whittaker normalization may require a larger splitting
field even when the Hecke eigensystem is defined over the smaller field.

## 13. Level and local ramification

### 13.1 The level problem is placewise but not degreewise

The finite conductor of the lift is assembled from exact local exponents. One cannot
predict it by multiplying the old level by the discriminant of $E/F$, nor by extending
the old conductor ideal to $\mathcal O_E$. Both guesses fail because conductor
restriction depends on the inertia representation, not merely on the extension.

For every $w\mid v$, put

$$
c_w=a(\operatorname{BC}_{E_w/F_v}\pi_v).
$$

Then the exact global level is

$$
\mathfrak f_E(\operatorname{BC}\pi)
=\prod_{v<\infty}\prod_{w\mid v}\mathfrak p_w^{c_w}.
$$

All subtlety is localized in the conductor rules of Book 81; no extra global
correction is introduced.

### 13.2 Split and unramified places

If $v$ splits completely, $E_w=F_v$ and $c_w=a(\pi_v)$ at each of the $\ell$ places.
The local type and newvector dimension are unchanged in every factor. If
$E_w/F_v$ is unramified, restriction preserves inertia and its upper breaks, so again

$$
c_w=a(\pi_v).
$$

This includes ramified representations. A supercuspidal may become principal series
under unramified base change, but its conductor exponent is unchanged. Sphericality is
preserved. An unramified Steinberg twist keeps exponent one, and the two character
conductors of a principal series are unchanged.

### 13.3 Ramified places

If $E_w/F_v$ is ramified, an unramified $\pi_v$ remains unramified: its parameter was
already trivial on $I_{F_v}$. Field ramification does not itself insert level into the
base-changed representation.

For ramified $\pi_v$, three effects compete:

- the smaller inertia group can kill a finite inertial character;
- positive upper breaks are reindexed by the Herbrand function;
- the monodromy operator is retained unchanged.

Accordingly $c_w$ can be less than, equal to, or greater than $a(\pi_v)$. For wildly
ramified supercuspidals, two representations with the same downstairs conductor may
have different upstairs conductors because their inertial constituents restrict
differently.

### 13.4 Preservation and change of standard types

The local parameter gives the reliable dictionary:

| component over $F_v$            | component over $E_w$                   | condition                                  |
| ------------------------------- | -------------------------------------- | ------------------------------------------ |
| spherical                       | spherical                              | always                                     |
| $I(\chi_1,\chi_2)$              | $I(\chi_1\circ N,\chi_2\circ N)$       | interpret the reducible boundary           |
| $\operatorname{St}\otimes\mu$   | $\operatorname{St}\otimes(\mu\circ N)$ | monodromy persists                         |
| selected dihedral supercuspidal | supercuspidal                          | restricted Weil representation irreducible |
| selected dihedral supercuspidal | principal series                       | restricted Weil representation splits      |

For a newvector level, $K_1(\mathfrak p_w^{c_w})$ is minimal. If a more refined type
is prescribed, restrict its inertial parameter and identify the target type. Conductor
equality alone does not imply equality of types or fixed-vector dimensions for
arbitrary compact open subgroups.

### 13.5 A level counterexample

Let $E_w/F_v$ be ramified quadratic and let $\eta_v$ be its local norm character.
Choose

$$
\pi_v=I(\mu,\mu\eta_v)
$$

away from the reducibility boundary. Both inducing characters may be ramified. After
norm pullback, $\eta_v$ becomes trivial, so the two inducing characters coincide. The
upstairs conductor is twice the conductor of $\mu\circ N$, which can be strictly
smaller than the original sum.

There is no conflict with the distinctness assertion for a restricted supercuspidal
or for the global automorphic-induction exception. The parameter of this principal
series is already reducible,
$\mu\oplus\mu\eta_v$, before restriction. Its two distinct character lines are
allowed to coalesce because their ratio is the local norm character. Cyclic Clifford
theory forbids a repeated restriction only when the two-dimensional parameter
downstairs is irreducible.

Another character of the same conductor exponent but nontrivial on local norms need
not cancel. Equal downstairs levels have produced different upstairs levels. No
formula depending only on $a(\pi_v)$, $e_v$, and $f_v$ can therefore be exact at all
ramified places.

## 14. The exact range of the comparison

### 14.1 Why the hypotheses belong in the proof

A transfer theorem is only as strong as the local correspondence and trace comparison that
construct it. The prime-degree and selected qualifiers have mathematical content: prime degree
controls the global scalar-norm geometry, while selectedness controls which ramified type
functions and twisted characters have actually been matched. This chapter gathers those
conditions in one place before the examples and final theorem.

### 14.2 The local representation input

Book 81 proves parameter restriction for determinant characters, principal series, special
representations, and selected tame dihedral packets. Its image theorem says that invariance is
sufficient for extension as an abstract admissible parameter, but a smooth selected descent
exists only when an extension remains inside the constructed range. The matching trace algebra
sees every extension of the same restriction. Forward isolation uses the extension-complete
slice for $\omega_\pi$; determinant-one reverse descent uses the antecedent-complete union of
such slices from Section 1.2. Consequently the global theorem may use

$$
\operatorname{rec}_{E_w}(\Pi_w)
=\operatorname{rec}_{F_v}(\pi_v)|_{W_{E_w}}
$$

only under that complete-fiber clause. Primitive wild packets and the ramified
dyadic wild boundary are excluded, not inferred by continuity or by equality of $L$-factors.

### 14.3 Three independent global inputs

The construction uses three independent theorems. Book 105 classifies prime-degree twisted
classes, fixes their measures, and proves absolute convergence of the geometric distribution.
Book 106 proves trace class, factorization of the automorphic intertwiner, annihilation of the
noncuspidal spectrum, and the twisted simple spectral expansion. Book 107 proves normalized
orbital matching, the spherical fundamental lemma, selected ramified and archimedean matching,
and the quadratic scalar correction. Book 96 supplies the character-clean compact trace and
split completion of every global quaternion division block, including algebras which are not
totally definite. None of these statements implies either of the other three.

The logical chain is therefore

```text
local parameter restriction        local orbital matching
             |                              |
             v                              v
candidate local tensor       matching global geometric terms
             |                              |
             +------------ spectral comparison ------------+
                                            |
                                            v
                         automorphic existence and all-place compatibility.
```

Strong multiplicity one from Book 95 supplies recognition and uniqueness only after the
automorphic spectral term has been constructed.

### 14.4 The strongly cuspidal selector

The simple formula requires one place at which the global tensor has a matching strongly
cuspidal factor. A surviving real discrete series or a selected finite square-integrable
component provides such a factor through a pseudo-coefficient. At a split place the cyclic
tensor of coefficients has twisted trace one; at a nonsplit invariant place the coefficient is
rescaled by the eigenvalue of the normalized intertwiner. The remaining local factors may be
spherical or selected type functions.

If no such place exists, Books 105--107 do not provide the required comparison for this packet.
One would need a nonsimple trace formula with its continuous terms and a matching theorem in
the missing local range. This book makes no assertion in that situation.

### 14.5 A reusable admissibility test

Before applying the theorem to a packet, verify the following finite list:

1. $E/F$ is cyclic of prime degree and a generator has been fixed consistently.
2. Every finite local component and every restriction lies in the selected range.
3. The archimedean components are the cohomological parameters matched in Book 107.
4. One place supplies matching strongly cuspidal selectors.
5. Fixed-central forward comparison uses $\Omega=\omega\circ N_{E/F}$; reverse comparison
   uses the determinant-one form until $\omega$ emerges. The same centralizer measures are
   used in normalized orbital integrals.
6. Every local factor belongs to $\mathscr T_v^{\mathrm{sel}}$ and the global companions are
   the restricted tensors of Theorem 4.3; no arbitrary smooth source variation is used.
7. In quadratic degree the entire coherent quaternion family is retained and completed through
   its noncharacter spectrum; it is not killed by a pseudo-coefficient.
8. Every local extension fiber used in forward or reverse comparison is extension-complete
   selected in the central-character slice being compared; reverse comparison without a
   pre-existing descent uses every antecedent slice. Reducible fibers are allowed and need not
   be local torsors.

Under these conditions Chapters 5--7 prove existence and local compatibility. Chapter 10
settles the sole isobaric boundary, and Chapter 11 proves selected descent and global fibers.
This list is also the reason the final theorem does not claim arbitrary cyclic degree,
arbitrary local test functions, or primitive-wild local compatibility.

## 15. Four extended examples

### 15.1 Unramified quadratic base change

Let $E/F$ be quadratic and unramified at a finite place $v$. Suppose $v$ is inert and
$\pi_v$ is spherical with normalized Hecke polynomial

$$
1-A_vX+B_vX^2.
$$

There is one place $w$ above $v$, with $q_w=q_v^2$, and

$$
P_w(X)=1-(A_v^2-2B_v)X+B_v^2X^2.
$$

The raw $T_w$-eigenvalue is

$$
q_w^{1/2}(A_v^2-2B_v)=q_v(A_v^2-2B_v).
$$

If instead $v$ splits, there are two places $w_1,w_2$, each with $q_{w_i}=q_v$ and
polynomial $1-A_vX+B_vX^2$. The Euler factor over $E$ is the product of those two
identical factors.

Now let $\pi_v$ be ramified of conductor exponent $c$. Since the field extension is
unramified, the upstairs exponent is also $c$. Type can nevertheless change: a
depth-zero dihedral supercuspidal induced from the unramified quadratic extension
becomes principal series when that inducing field is $E_w$. This separates conductor
preservation from type preservation.

Globally, if $\pi$ has no self-twist by $\eta_{E/F}$, the lift is cuspidal. If it has
that self-twist, it is induced from $E$ and the global output splits.

### 15.2 Real-to-CM behavior

Let $F$ be totally real and let $E/F$ have prime degree with $E$ a CM field. Complex
conjugation has order two, so necessarily $\ell=2$ and $E/F$ itself is the quadratic CM
extension. Thus the same character $\eta_{E/F}$ controls both the real-to-complex local change
and the possible global failure of cuspidality, though those are logically different effects.
Assume the packet has a selected finite square-integrable component that remains discrete, so
the strongly cuspidal selector required by Chapter 14 is available; the complex archimedean
components alone do not provide one.

Suppose $\pi$ is cohomological with real component at $\tau$ described by
$(a_\tau,b_\tau)$ and holomorphic weight
$k_\tau=a_\tau-b_\tau+2$. For every complex embedding
$\widetilde\tau:E\hookrightarrow\mathbb C$ above $\tau$, the component of the lift is
the complex principal series whose parameter has characters with exponent pairs

$$
(a_\tau,b_\tau)\quad\text{and}\quad(b_\tau,a_\tau).
$$

The lift is regular algebraic with the same purity weight. There is no holomorphic
discrete series over $\mathbb C$, so calling this component “weight-$k$ discrete
series” would be wrong; the weight persists as an infinitesimal and cohomological
parameter.

If $\pi$ has no self-twist by $\eta_{E/F}$, its
lift is cuspidal. If it is dihedral from $E/F$, the lift is Eisenstein.
Real-to-CM behavior alone does not decide cuspidality.

### 15.3 A dihedral representation becoming Eisenstein

Let $E/F$ be quadratic and choose a Hecke character $\theta$ of $E$ with
$\theta\ne\theta^\tau$. Put

$$
\pi=\operatorname{AI}_{E/F}(\theta).
$$

Then $\pi$ is cuspidal and $\pi\otimes\eta_{E/F}\cong\pi$. Its base change is
noncuspidal. Direct restriction gives

$$
\operatorname{BC}_{E/F}(\pi)
=\theta\boxplus\theta^\tau.
$$

The two displayed characters are distinct by Section 10.3. Thus this is a
multiplicity-free Eisenstein sum: regularity of $\theta$ makes the induced
two-dimensional datum over $F$ irreducible, and cyclic restriction cannot turn it
into a repeated character.

Its central character is the product of these two characters. Meanwhile

$$
\omega_\pi=\eta_{E/F}\,\theta|_{C_F}.
$$

Pullback by $N_{E/F}$ kills $\eta_{E/F}$ and gives the same product. This checks the
often missed quadratic determinant factor.

At a place inert in $E$, a supercuspidal component can split after base change to $E_w$.
At a split place the component was already principal
series. These different local histories assemble into the same isobaric sum.

### 15.4 An odd-degree cuspidal lift

Let $E/F$ be cyclic of degree three and let $\pi$ satisfy the selected cohomological and
selector hypotheses of Chapter 1. The
group $X(E/F)$ has order three. If $\pi\otimes\chi\cong\pi$ for a nontrivial member,
central characters would give $\chi^2=1$, a contradiction. Hence the lift is
cuspidal.

At an unramified inert place with Satake trace $A$ and determinant $B$, the lifted
trace is

$$
A^3-3AB,
$$

and the determinant is $B^3$. At a completely split place there are three unchanged
components. At a place with ramification index three and residue degree one, the
unramified Satake roots are not cubed: $f=1$.

If $\pi_v$ is supercuspidal, its irreducible two-dimensional Weil parameter remains
irreducible on the index-three subgroup. If $\pi_v$ is Steinberg, it remains
Steinberg. The fiber above the global lift consists of

$$
\pi,\qquad\pi\otimes\chi,\qquad\pi\otimes\chi^2.
$$

Their central characters are distinct because squaring permutes the order-three
group. Prescribing one norm antecedent selects one descent.

## 16. The cyclic theorem package

### 16.1 The complete theorem

**Theorem 16.1 (prime cyclic base change and descent for selected cohomological
$\mathrm{GL}_2$ packets).** Let $E/F$ be cyclic of prime degree $\ell$, and put

$$
X(E/F)=\widehat{C_F/N_{E/F}(C_E)}.
$$

Let $\pi$ be a unitary cuspidal automorphic representation on
$\mathrm{GL}_2(\mathbb A_F)$ satisfying the selected local, extension-complete relative to
$\omega_\pi$, and strongly cuspidal selector hypotheses of Chapter 1. Then there is a unique
automorphic isobaric $\Pi=\operatorname{BC}_{E/F}(\pi)$ on
$\mathrm{GL}_2(\mathbb A_E)$ with these properties.

1. For every $v$ and $w\mid v$,

   $$
   \Pi_w\cong\operatorname{BC}_{E_w/F_v}(\pi_v),
   $$

   by restriction of the full local Weil--Deligne parameter.

2. It is $\Gamma$-invariant, has
   $\omega_\Pi=\omega_\pi\circ N_{E/F}$, and commutes with duals and with twists that remain
   in the selected, extension-complete, trace-comparable range.

3. At an unramified $w\mid v$, its Satake pair is
   $\{\alpha_v^{f(w/v)},\beta_v^{f(w/v)}\}$. Conductors, local types,
   archimedean parameters, and local factors are those of parameter restriction.

4. It is cuspidal exactly when $\pi$ has no nontrivial self-twist in $X(E/F)$. Such a
   self-twist is quadratic. Every odd-prime-degree lift is cuspidal. In quadratic degree,
   failure occurs precisely for $\pi=\operatorname{AI}_{E/F}(\theta)$, and then

   $$
   \Pi=\theta\boxplus\theta^\tau.
   $$

   The two displayed characters are distinct and each occurs with multiplicity one.

5. A selected trace-comparable cuspidal representation over $E$ with antecedent-complete
   selected local fibers lies in the image exactly when it is $\Gamma$-invariant. If its
   source fiber is $X(E/F)$-saturated, its descents form an $X(E/F)$-torsor. Reducible local
   extension sets may contain several local twisting orbits; the global cuspidal fiber is still
   the single torsor just stated.

6. For cuspidal sources, two base changes agree exactly when the sources differ by a
   member of $X(E/F)$. When their common lift is noncuspidal, the quadratic
   self-twist is the stabilizer and the fiber of cuspidal sources has one member.

7. Under the source-fiber saturation hypothesis, if $\Omega$ is the central character of an
   invariant cuspidal $\Pi$, then $\Omega=\omega\circ N$ for some $\omega$. Relative to one
   descent of central character $\omega_0$, a descent with prescribed central character
   $\omega$ exists exactly when $\omega/\omega_0\in X(E/F)^2$.

8. Regular algebraic and cohomological weights pull back along embeddings, algebraic
   conjugation commutes with base change, and the field of rationality can shrink
   precisely because coefficient conjugation can move $\pi$ in its norm-character
   twisting orbit.

9. The construction uses the directed finite matching category, its complete split and
   quaternion scalar companions, and the corrected relative/full discriminant conversion. It
   makes no claim for an arbitrary smooth test function, a target fiber containing an
   unconstructed primitive-wild or ramified-dyadic extension, a packet without a strongly
   cuspidal selector, or composite cyclic degree.

**Proof strategy.** Separate the free twisting orbit, where the completed split/quaternion
trace identity constructs a cusp form, from the quadratic fixed orbit, where the theta kernel
constructs the isobaric sum. Then read every invariant from the all-place local identity and
run the completed comparison backward for descent. Use the global Rankin--Selberg identity
(11.1), rather than local extension torsors, to determine the fiber.

**Proof.** Chapters 5 and 6 construct the lift by comparing ordinary and twisted trace
formulas. The directed local matching trace identity identifies all components, and strong
multiplicity one gives uniqueness. Chapters 8 and 9 give the Hecke, factor, conductor,
type, and archimedean formulas. Chapter 10 constructs quadratic automorphic induction and proves
the self-twist criterion. Chapter 11 proves selected descent by the global completed trace and
proves fibers by the quotient-character Rankin--Selberg product, while retaining reducible
local extensions and the central square class. Chapters 12--14 establish algebraic and level
compatibility and audit every comparison hypothesis. $\square$

### 16.2 The data passed to cyclic towers

The theorem concerns one cyclic extension, and we stop there. Its durable inputs for
a later tower argument are nevertheless clear:

- every local component is characterized by parameter restriction;
- norm directions and central characters are functorial;
- the kernel of a cyclic step is its finite norm-character group;
- cuspidality can fail only at a quadratic self-twist, with an explicit
  multiplicity-free two-character isobaric sum;
- invariant cuspidal representations with antecedent-complete selected local fibers descend,
  with controlled global fibers and central square classes;
- conductors, weights, coefficient fields, and selector conditions are checked one
  place at a time.

No composite or solvable extension has been treated here. Compatibility among different cyclic
factorizations, accumulation of twisting ambiguity, and descent through a solvable tower are
later questions. A repeated-character endpoint can arise from already-isobaric data, but not
from the quadratic restriction of the cuspidal rank-two source treated here.

### 16.3 Conclusion

Cyclic base change begins with a reversal of arrows. The field extension points from
$F$ to $E$, local parameters restrict from the Weil group of $F$ to that of $E$, and
idele-class characters follow the same arithmetic operation by pulling back along the
norm from $E$ to $F$. Once this direction is fixed, central characters, twists,
Frobenius powers, and local factors all follow from one restriction principle.

The global theorem requires more. Twisted conjugacy turns
$\delta\sigma(\delta)\cdots\sigma^{\ell-1}(\delta)$ into an ordinary norm class. Matching
normalized orbital integrals identifies regular tori, while singular germs and scalar
distributions control the boundary. Whittaker-normalized cyclic intertwiners make
the spectral trace factor locally. The resulting identity constructs an automorphic
object with the prescribed component at every place in the selected range; strong multiplicity one then
makes it unique.

The exceptional spectrum is informative. A cuspidal rank-two representation can be
stabilized by a norm character only when that character is quadratic. It is then
dihedral, induced from the quadratic extension itself, and restriction exposes its two
characters as an isobaric Eisenstein sum.
Those two characters are distinct and occur once each. Odd-degree cyclic base change
is therefore always cuspidal.

In the reverse direction, Galois invariance is the image condition for cuspidal
representations inside the antecedent-complete selected scope. Norm characters measure the full global fiber, while their squares measure
which prescribed central characters occur. This distinction survives at infinity and in fields
of rationality. The result is a complete prime-degree transfer theorem in the selected
cohomological range: globally constructed, locally exact, explicit at its cuspidal boundary,
and honest about the wild and nonsimple-trace boundaries it does not cross.
