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
   - [Why the source trace is normalized by norm characters](#52-why-the-source-trace-is-normalized-by-norm-characters)
   - [The geometric expansion](#53-the-geometric-expansion)
   - [The spectral expansion](#54-the-spectral-expansion)
   - [Factorization of a twisted automorphic trace](#55-factorization-of-a-twisted-automorphic-trace)
6. [Comparing the geometric and spectral sides](#6-comparing-the-geometric-and-spectral-sides)
   - [The global matching identity](#61-the-global-matching-identity)
   - [Cancellation of the induced spectrum](#62-cancellation-of-the-induced-spectrum)
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
    - [Even degree and the unique quadratic subextension](#103-even-degree-and-the-unique-quadratic-subextension)
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
14. [Compatibility with global Jacquet--Langlands](#14-compatibility-with-global-jacquet--langlands)
    - [The comparison to be justified](#141-the-comparison-to-be-justified)
    - [Local Brauer invariants](#142-local-brauer-invariants)
    - [The global commuting square](#143-the-global-commuting-square)
    - [The noncuspidal boundary](#144-the-noncuspidal-boundary)
    - [Levels and weights through the square](#145-levels-and-weights-through-the-square)
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

Let $E/F$ be a cyclic extension of number fields. Book 46 attached to every place
$v$ of $F$, every place $w$ of $E$ above $v$, and every irreducible admissible
representation $\pi_v$ of $\mathrm{GL}_2(F_v)$ a local representation

$$
\operatorname{BC}_{E_w/F_v}(\pi_v)
$$

whose parameter is obtained by restriction. The global problem begins where that
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
conjugacy. The norm of a twisted class is an ordinary class over $F$. Book 46 supplies
the candidate local representation by restriction of its complete parameter. The
local harmonic analysis developed below proves the matching twisted-character
identity, and the global trace formula proves that those local identities assemble
into an automorphic representation.

This order is important. We shall not assume global cyclic base change in order to
prove its own trace identity. We first construct matching geometric distributions,
then compare their spectral expansions, and only afterward name the representation
that the comparison produces.

### 1.2 Standing notation

Put

$$
C_K=K^\times\backslash\mathbb A_K^\times
$$

for the idele class group of a number field $K$. Fix a generator
$\sigma$ of

$$
\Gamma=\operatorname{Gal}(E/F),\qquad |\Gamma|=n.
$$

For a place $v$ of $F$, choose one place $w\mid v$. Let

$$
g_v=\#\{w:w\mid v\},\qquad
e_v=e(E_w/F_v),\qquad f_v=f(E_w/F_v),
$$

so that

$$
n=g_ve_vf_v.
$$

The decomposition group $\Gamma_w$ has order $e_vf_v$. If
$w,\sigma w,\ldots,\sigma^{g_v-1}w$ are the places over $v$, then
$\sigma^{g_v}$ generates $\Gamma_w$. Thus the automorphism used after one circuit
through the local factors is fixed by the global choice of $\sigma$; no independent
local generator is being smuggled into the notation.

All reciprocity maps are arithmetically normalized: a uniformizer maps to arithmetic
Frobenius. Thus pullback of a Hecke character $\chi$ of $C_F$ to $C_E$ is

$$
\chi_E=\chi\circ N_{E/F},
$$

and corresponds to restriction of the associated one-dimensional arithmetic
character. At an unramified finite place, Satake parameters are eigenvalues of
arithmetic Frobenius in the normalization of Book 42. Normalized parabolic induction
is used throughout.

For a Hecke character $\chi$ of $F$, the twist $\pi\otimes\chi$ means
$\chi\circ\det$. Its central character is $\omega_\pi\chi^2$. The symbol
$\boxplus$ denotes an isobaric sum, not a direct sum inside the cuspidal spectrum.

### 1.3 The theorem we are trying to earn

The desired object is denoted

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
$\pi$ was automorphically induced, restriction exposes the two inducing characters,
and the global lift becomes their isobaric sum.

There are therefore three distinct assertions to prove:

1. the formal local tensor is automorphic;
2. it is either cuspidal or a precisely described isobaric sum;
3. its isomorphism class and every local component are forced by $\pi$.

The trace formula proves the first assertion and detects the exceptional part of the
second. Strong multiplicity one proves the third only after existence has been
established.

### 1.4 A first counterexample to placewise reasoning

Take a quadratic field $M/F$, a Hecke character $\theta$ of $M$ with
$\theta\ne\theta^\tau$, and

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

which is Eisenstein rather than cuspidal. No inspection of generic unramified local
components alone detects this failure of cuspidality. The global self-twist
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

In particular, $X(E/F)$ is cyclic of order $n$. Its members are finite-order unitary
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
$v$. If $v$ is unramified and inert of degree $n$, the unramified local quotient
$F_v^\times/N(E_w^\times)$ is cyclic of order $n$; a generator sends a uniformizer to
a primitive $n$th root of unity. At a ramified place the character can be ramified,
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

The factors are carried into one another by $\Gamma$. At a completely split place
there are $n$ factors, each equal to $\pi_v$. At an inert place there is one factor and
the local extension has degree $n$. At an intermediate decomposition type there are
$g_v$ factors, each attached to a local extension of degree $e_vf_v$.

This formula prevents a frequent degree error. The Frobenius exponent at one $w$ is
$f_v$, not $n$ and not $e_vf_v$. The number $g_v$ counts how many such local factors
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
A_\sigma^n=1.
$$

Without this normalization, multiplying $A_\sigma$ by an $n$th root of unity would
multiply every twisted trace and destroy the global comparison.

### 3.2 Twisted conjugacy and its norm

For $\delta,x\in\mathrm{GL}_2(E)$, define

$$
\delta^x=x^{-1}\delta\sigma(x).
$$

This is $\sigma$-conjugacy. Its ordered norm is

$$
N_\sigma(\delta)
=\delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta).
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
$G(E_v)$ with $G(F_v)^n$ so that $\sigma$ cyclically permutes factors. Then

$$
(g_0,\ldots,g_{n-1})\longmapsto g_0g_1\cdots g_{n-1}
$$

describes the norm class. A product test function
$\phi_0\otimes\cdots\otimes\phi_{n-1}$ transfers to the convolution

$$
f=\phi_0*\phi_1*\cdots*\phi_{n-1}
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

Choose adelic measures from invariant differential forms, and quotient measures by
Weil's formula. At almost every finite place normalize the hyperspecial subgroup to
have volume one. When a local Hecke normalization rescales a group measure, rescale
the matching function so that its orbital integral is unchanged. There is no
nontrivial transfer factor for cyclic base change on $\mathrm{GL}_2$ with these
conventions: the factor is $+1$.

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

The pair $(f_v,\phi_v)$ is **matching** if

$$
O_\gamma(f_v)=TO_{\delta,\sigma}(\phi_v)
$$

whenever $\gamma$ is the norm of $\delta$, and the ordinary orbital integral vanishes
on regular classes that are not norms. Singular germs at central and unipotent classes
must match as well; regular matching alone is insufficient for the full trace formula.

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

The choice of $\omega$ is essential on descent. A Galois-invariant central character
$\Omega$ over $E$ may have several norm antecedents $\omega$; the trace formula is run
with one chosen antecedent, and Chapter 11 will explain which of them can occur as the
central character of a particular descent.

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

Book 46 gives the local base-change representation by restriction of the full
Weil--Deligne parameter. The extra assertion needed globally is a theorem of local
harmonic analysis, not a consequence of parameter restriction alone.

**Theorem 4.1 (local matching and twisted characters).** For a matching pair
$(f_v,\phi_v)$ and an irreducible admissible $\pi_v$,

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
\operatorname{tr}\bigl(\pi_v(\phi_0)\cdots\pi_v(\phi_{n-1})\bigr)
=\operatorname{tr}\pi_v(\phi_0*\cdots*\phi_{n-1}).
$$

At a nonsplit place the assertion is the twisted character identity for restriction
of the local parameter. It includes principal, special, supercuspidal, ramified, and
archimedean representations.

**Proof strategy.** On the regular set, unfold normalized induction for principal
series and compare the two diagonal-torus integrals under the norm. The special case
is obtained by retaining the nonzero monodromy constituent at the reducibility
boundary. For discrete parameters, compare characters on elliptic tori and use the
cyclic orthogonality relation on the parameter restricted to $W_{E_w}$. In the split
case the asserted identity is the convolution calculation above. These calculations
give equality on every regular semisimple class. Matching the central and unipotent
germs extends the equality across the singular set, and density of regular character
distributions proves the trace identity for all test functions. The archimedean proof
uses the same division into Cartan classes and the corresponding smooth character
formula. $\square$

This is stronger than equality of local $L$-factors. The latter would not allow test
functions to vary enough to recover a ramified or archimedean representation.

### 4.5 Existence of matching functions

At nonarchimedean places, regular semisimple orbital integrals determine the transfer
on a dense subspace, and matching of singular germs completes it. At unramified places
the spherical transfer just described supplies canonical matching functions. At the
finitely many ramified places, one constructs transfer first on regular tori and then
adjusts functions near the center and unipotent set. For $\mathrm{GL}_2$, the only
proper Levi is the diagonal torus, so there is a single family of parabolic germs to
control.

At archimedean places, smooth rapidly decreasing test functions replace compactly
supported locally constant ones. Matching is characterized by the same twisted
character identity on regular semisimple classes, together with compatible central
and infinitesimal-character projectors.

The germ construction also gives enough transfer in the reverse direction: while a
matching partner is not unique, transferred functions separate irreducible ordinary
characters and invariant twisted characters. These assertions are local harmonic
analysis, not the global theorem. Their role is to ensure that every sufficiently
flexible $f_v$ has a matching $\phi_v$, and that the trace equality of Section 4.4 is
valid before any global lift has been constructed.

## 5. The twisted trace formula in rank two

### 5.1 The kernel and the inserted automorphism

We now pass from local matching to a global spectral construction. Write
$G_K=\mathrm{GL}_2(\mathbb A_K)$. For a factorizable test function
$\phi=\bigotimes_v\phi_v$ on $G_E$, define the automorphic kernel

$$
K_\phi(x,y)=\sum_{\delta\in Z(E)\backslash\mathrm{GL}_2(E)}
\phi(x^{-1}\delta y).
$$

The twisted operator is $R(\phi)I_\sigma$, where

$$
(I_\sigma h)(x)=h(\sigma^{-1}x).
$$

Formally its trace is the diagonal integral

$$
\int_{Z(\mathbb A_E)\mathrm{GL}_2(E)\backslash G_E}
K_\phi(x,\sigma x)\,dx.
$$

The quotient is not compact, so this expression is not automatically convergent.
This is where the rank-two trace formula, rather than a formal character sum, is
needed. Truncate the quotient at height $T$ in the single positive chamber of the
diagonal Borel. The truncated trace is a polynomial-exponential function of $T$;
its constant term defines the invariant twisted distribution

$$
I_E^\sigma(\phi).
$$

The same truncation on the ordinary $F$-side defines $I_F(f)$. Since
$\mathrm{GL}_2$ has semisimple rank one, there is only one truncation parameter, one
proper standard Levi, and one scattering operator. We can therefore display every
kind of term without hiding higher-rank combinatorics.

### 5.2 Why the source trace is normalized by norm characters

The lift cannot distinguish $\pi$ from $\pi\otimes\chi$ for
$\chi\in X(E/F)$. Consequently the geometric comparison naturally sees an orbit,
not a labeled member of that orbit. Let $\mathcal C(\omega)$ be the finite set of
central characters

$$
\mathcal C(\omega)=\{\omega\chi^2:\chi\in X(E/F)\}.
$$

The normalization is made on **distinct isomorphism classes**, not on a list retaining
repetitions indexed by $\chi$. For a cuspidal $\pi$, write

$$
\mathcal O_X(\pi)
=\{[\pi\otimes\chi]:\chi\in X(E/F)\}.
$$

The normalized source distribution assigns to this orbit the total mass

$$
\frac{|\mathcal O_X(\pi)|}{n}
=\frac1{|\operatorname{Stab}_X(\pi)|}.
$$

It can be realized by taking the fixed-central-character trace formulas for the
distinct members of $\mathcal C(\omega)$, twisting their test functions by

$$
f^\chi(g)=\chi(\det g)^{-1}f(g).
$$

Thus $f^\chi$ has inverse central covariance $(\omega\chi^2)^{-1}$, and
$\operatorname{tr}(\pi\otimes\chi)(f^\chi)=\operatorname{tr}\pi(f)$. Within a
central-character block, determinant twists separate the distinct representations;
only after that separation are equal isomorphism classes identified. We denote the
resulting orbit-normalized invariant distribution by $I_F^{\mathrm{norm}}(f)$.

The functions $f$ and $f^\chi$ transfer to the same $\phi$: on a norm class
$\gamma=N_\sigma(\delta)$ one has $\chi(\det\gamma)=1$. Thus orbit normalization
changes neither the local transfer factor nor the twisted orbital integral. Writing
$n^{-1}\sum_{\chi\in X}I_{F,\omega\chi^2}(f^\chi)$ while also retaining repeated
copies of an isomorphic representation would be wrong in the stabilized case: it
would count the same source constituent twice.

A free $X(E/F)$-orbit contributes once. If a cuspidal representation
has a quadratic stabilizer, the orbit contributes with coefficient $1/2$; that is
exactly the Weyl stabilizer appearing in the associated Eisenstein term upstairs.

This factor is sometimes hidden by fixing a descent datum or by summing over central
characters. We keep it visible. It is not a local transfer factor, which remains
$+1$, and it does not change the local trace identity.

### 5.3 The geometric expansion

The geometric side of $I_E^\sigma(\phi)$ is organized by rational twisted conjugacy
classes. In rank two it has four kinds of contributions:

$$
I_{E,\mathrm{geom}}^\sigma(\phi)
=I_{\mathrm{cent}}^\sigma(\phi)
+I_{\mathrm{ell}}^\sigma(\phi)
+I_{\mathrm{hyp}}^\sigma(\phi)
+I_{\mathrm{unip}}^\sigma(\phi).
$$

The central term comes from scalar classes. The elliptic term is a sum over regular
twisted classes whose norm has anisotropic centralizer modulo the center. The
hyperbolic term comes from split regular norm classes. The unipotent term includes the
identity germ and the nontrivial unipotent orbit, together with the logarithmic weight
produced by truncation.

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

Under the norm correspondence this is the same torus volume as the coefficient
$a(\gamma)$ on the $F$-side. Product measures give

$$
TO_{\delta,\sigma}(\phi)
=\prod_vTO_{\delta_v,\sigma}(\phi_v),
\qquad
O_\gamma(f)=\prod_vO_{\gamma_v}(f_v).
$$

Matching at every place therefore identifies every regular term.

The singular terms require more care. The scalar norm map on centers is
$N_{E/F}:C_E\to C_F$; its finite cokernel has order $n$. The orbit normalization in
Section 5.2 exactly compensates for this volume. The unipotent weighted orbital
integrals are identified by matching their Shalika germs and by using trace-compatible
additive characters. The hyperbolic logarithmic weights agree because the modulus of
the Borel and the norm of its diagonal torus satisfy the product formula. Thus no
unrecorded discriminant or sign remains in the global comparison.

### 5.4 The spectral expansion

The spectral side also has four visible pieces:

$$
I_{E,\mathrm{spec}}^\sigma(\phi)
=I_{\mathrm{cusp}}^\sigma(\phi)
+I_{\mathrm{res}}^\sigma(\phi)
+I_{\mathrm{cont}}^\sigma(\phi)
+I_{\mathrm{sing}}^\sigma(\phi).
$$

The cuspidal term is

$$
I_{\mathrm{cusp}}^\sigma(\phi)
=\sum_{\Pi\simeq\Pi^\sigma}
\operatorname{tr}\bigl(\Pi(\phi)A_\sigma\bigr).
$$

Cuspidal representations in nontrivial $\Gamma$-orbits contribute zero because
$I_\sigma$ cyclically permutes their isotypic spaces. Multiplicity one allows us to
write no additional multiplicity factor.

The continuous spectrum is induced from characters $\xi_1\boxtimes\xi_2$ of the
diagonal torus. If

$$
\mathcal I_E(\xi_1|\cdot|^{it},\xi_2|\cdot|^{-it})
$$

denotes normalized induction, its contribution is an integral over $t\in\mathbb R$
of the trace of $\phi$ composed with the normalized standard intertwining operator
and $A_\sigma$. Poles of that intertwining operator give the residual term. Its
logarithmic derivative supplies the singular spectral correction. This is the
spectral counterpart of the weighted hyperbolic and unipotent terms.

In formulas, suppressing the finite sum over unitary character data, the continuous
part has the shape

$$
-\frac1{4\pi}\int_{-\infty}^{\infty}
\operatorname{tr}\left(
M_E(-it)M_E'(it)
\mathcal I_E(it)(\phi)A_\sigma
\right)\,dt.
$$

The sign, the factor $1/4\pi$, the derivative, and normalized induction are tied to
the same Haar and truncation conventions; endpoint terms at $t=0$ are included in the
residual and singular pieces already displayed. Replacing normalized by unnormalized
induction would move modulus characters into both this formula and the local Satake
parameters.

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

This factorization is the spectral bridge to Book 46. A different scalar normalization
at one place would alter one factor and hence the global product. Requiring the local
Whittaker functionals to multiply to the global one makes the product canonical.

## 6. Comparing the geometric and spectral sides

### 6.1 The global matching identity

Let $f=\bigotimes_vf_v$ and $\phi=\bigotimes_v\phi_v$ be matching, with spherical
units almost everywhere and the central covariance of Chapter 4. The regular norm
correspondence, equality of torus volumes, matching of singular germs, and the explicit
central norm index give

$$
\boxed{I_F^{\mathrm{norm}}(f)=I_E^\sigma(\phi).}
$$

This is the cyclic twisted trace identity for $\mathrm{GL}_2$. It is a conclusion of
the geometric comparison, not an assumed statement about automorphic representations.

**Proof strategy.** Truncate both kernels at corresponding heights. First compare
regular elliptic and split terms using norm conjugacy and local orbital matching. Then
compare the scalar and unipotent germs, where the norm index and additive-character
normalization enter. Finally compare the coefficients of every power and exponential
in the truncation parameter. Equality of the constant terms is the displayed identity.

**Proof.** Every regular global class contributes a product of local orbital
integrals. If the $F$-class is not a norm, one local orbital integral is zero. If it is
a norm, the twisted centralizer and ordinary centralizer are the same $F$-torus, so
the volume coefficients agree and local matching identifies the products. Matching
of central germs gives equality of scalar terms after division by the order $n$ of
the norm-character group. Matching of unipotent germs identifies the nontrivial
unipotent distributions. The diagonal torus norm and the product formula identify the
logarithmic weights in the split regular terms. Hence the truncated geometric
polynomial-exponential functions agree. Taking constant terms proves the identity.
$\square$

The proof uses all geometric terms. One may choose special test functions that make
the continuous and unipotent terms vanish, but that simplification is a consequence of
the full identity and is not adequate as the sole construction for representations
having no convenient square-integrable local component.

### 6.2 Cancellation of the induced spectrum

Normalized induction commutes with norm pullback of the two inducing characters. The
standard intertwining operator is a product of local operators, and its normalizing
factor is a quotient of Hecke $L$-functions. Character induction and the norm identity
give the corresponding factorization over $E$. Therefore the continuous terms on the
two sides match, including logarithmic derivatives and residues.

More concretely, if $\mu_1,\mu_2$ are Hecke characters of $F$, then the expected
transfer of
$\mathcal I_F(\mu_1,\mu_2)$ is

$$
\mathcal I_E(\mu_1\circ N_{E/F},\mu_2\circ N_{E/F}).
$$

The local matching trace identity holds on these induced representations, and the
global normalizing factors satisfy the product identity obtained from cyclic character
factorization. Subtracting the equal continuous and residual contributions from the
full trace identity leaves an equality of cuspidal distributions, except when a
quadratic stabilizer turns a source cusp form into precisely such an induced term.

That exception is not lost in subtraction. It appears with coefficient $1/2$, the
order of the Weyl stabilizer, matching the $1/2$ contributed by the source
$X(E/F)$-orbit with a quadratic stabilizer.

### 6.3 Isolating one Hecke eigensystem

Fix a cuspidal $\pi$ over $F$ and choose a finite set $S$ containing the archimedean
places, all places ramified in $E/F$, and all places where $\pi$ or its central
character is ramified. Outside $S$, the spherical Hecke algebra is commutative. Its
characters attached to distinct cuspidal representations are linearly independent.

Choose at places in $S$ compactly supported operators having nonzero trace on
$\pi_v$, and vary the spherical factors outside $S$. If no invariant automorphic
representation over $E$ had the predicted transformed Hecke character, the
$\pi$-orbit term on the normalized source side could not be matched on the twisted
side for all such variations. Linear independence gives a contradiction.

Thus there exists an automorphic representation $\Pi$ over $E$, cuspidal unless its
term is absorbed by the explicitly matched induced spectrum, such that at every
unramified $w\mid v$ outside $S$,

$$
\operatorname{Sat}(\Pi_w)
=\{\alpha_v^{f_v},\beta_v^{f_v}\}.
$$

This is the first existence statement. At this stage the components at $S$ have not
yet been identified; that requires varying one local transfer factor while holding the
others fixed.

### 6.4 Recovering a ramified or archimedean component

Fix $v_0\in S$. At every other place choose matching functions whose trace on the
already isolated representation is nonzero. Vary $f_{v_0}$ through the local Hecke
algebra and choose matching $\phi_{v_0}$. Factorization of the global trace gives

$$
\operatorname{tr}\pi_{v_0}(f_{v_0})
=\operatorname{tr}\bigl(
\Pi_{v_0}^E(\phi_{v_0})A_{\sigma,v_0}
\bigr)
$$

for all matching pairs. By the local character identity and independence of twisted
characters,

$$
\Pi_w\cong\operatorname{BC}_{E_w/F_{v_0}}(\pi_{v_0})
\qquad(w\mid v_0).
$$

The argument applies equally at a ramified finite place and at infinity. Therefore
the global construction has the prescribed local component at **every** place, not
merely at almost every place.

## 7. Construction and uniqueness of the lift

### 7.1 The global existence theorem

We can now name the object produced by the comparison.

**Theorem 7.1 (cyclic base change, existence and local compatibility).** Let $E/F$ be
a cyclic extension of number fields and let $\pi$ be a cuspidal automorphic
representation of $\mathrm{GL}_2(\mathbb A_F)$. There is a unique automorphic isobaric
representation

$$
\operatorname{BC}_{E/F}(\pi)
$$

of $\mathrm{GL}_2(\mathbb A_E)$ such that for every place $v$ of $F$ and every
$w\mid v$,

$$
\operatorname{BC}_{E/F}(\pi)_w
\cong\operatorname{BC}_{E_w/F_v}(\pi_v).
$$

It is either cuspidal or an isobaric sum of two Hecke characters. It is invariant
under $\Gamma$.

**Proof strategy.** The trace formula first constructs an automorphic spectral term
with the expected good-place Hecke data. Variation of one local matching pair at a
time identifies every component. The continuous-spectrum calculation confines any
noncuspidal output to a two-character isobaric sum. Finally strong multiplicity one
for isobaric representations gives uniqueness.

**Proof.** Sections 6.3 and 6.4 give existence and the all-place local identities.
The only proper Levi of $\mathrm{GL}_2$ is $\mathrm{GL}_1\times\mathrm{GL}_1$, so an
automorphic noncuspidal term with the prescribed generic local parameters is an
isobaric sum of two characters. The Galois action permutes the local factors of the
candidate exactly as in Section 2.3; hence $\Pi^\sigma$ has the same components as
$\Pi$ at every place, and strong multiplicity one gives invariance. If two isobaric
representations have the required local components, they agree outside a finite set,
so strong multiplicity one gives their isomorphism. $\square$

The theorem does not claim that the lift is always cuspidal. Chapter 10 will identify
the exact exception and will show that odd-degree cyclic base change has no exception
for a cuspidal rank-two source.

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

The proof is not a new trace comparison. Each pair has identical local components by
Book 46, and global uniqueness identifies them. In particular, a norm character
$\chi\in X(E/F)$ acts trivially after base change.

## 8. Unramified Hecke data and global factors

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
splits completely, $f_v=1$ and the same polynomial occurs at each of the $n$ places.
When $v$ is inert and unramified, $f_v=n$ and there is one polynomial with the
$n$th powers. If $v$ has $g_v$ primes and local residue degree $f_v$, there are
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
identity of Book 46 over all places gives

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

The local lambda constants in Book 46 multiply globally to one. Hence

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
multiple of the upstairs different exponent. Book 46 expresses conductor change
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

Suppose $v$ splits into $n$ real places. Each factor of the lift is the same real
representation $\pi_v$, transported by the embeddings. If $v$ becomes complex, there
are $n/2$ complex places above it, each with the restricted parameter described above.
The equality

$$
n=g_v[ E_w:F_v]
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

For a supercuspidal $\pi_v$, the lift remains supercuspidal exactly when the restricted
two-dimensional Weil representation remains irreducible. If it splits as
$\xi_1\oplus\xi_2$, the lift is the principal-series representation attached to those
characters. In particular, “base change preserves supercuspidality” is false even for
unramified extensions.

### 9.4 Local $L$-packets are not an extra ambiguity

For $\mathrm{GL}_2$, a local parameter determines a single irreducible admissible
representation. There is no packet choice to coordinate globally. This singleton
property is one reason the trace formula can recover the component at a ramified place
from its twisted character.

The inner-form situation is different but compatible: a discrete parameter may also
label a representation of a quaternion division group. Chapter 14 will use the common
parameter to compare base change with Jacquet--Langlands. The fact that a quaternion
algebra may split over $E_w$ is a change of target group, not a second choice inside a
$\mathrm{GL}_2$ packet.

## 10. The cuspidality criterion

### 10.1 Why self-twists are the only obstruction

The source trace formula was normalized by $X(E/F)$-orbits. A free orbit contributes
to a cuspidal invariant representation upstairs. If the orbit has a stabilizer, its
coefficient changes, and the matching spectral term lies on the induced boundary.
This observation suggests the exact criterion.

We first record the global monomiality input rather than conceal it inside the
cuspidality proof.

**Lemma 10.1 (quadratic self-twists).** Let $\eta$ be a nontrivial quadratic Hecke
character of $F$, and let $M/F$ be the quadratic extension it cuts out. A cuspidal
representation $\pi$ satisfies $\pi\otimes\eta\cong\pi$ if and only if

$$
\pi\cong\operatorname{AI}_{M/F}(\theta)
$$

for a Hecke character $\theta$ of $M$ with $\theta\ne\theta^\tau$.

**Proof strategy.** The reverse implication follows at once from the two cosets in
quadratic induction. For the forward implication, normalize the self-intertwiner in
the Whittaker model. Since $\eta$ is trivial on $N_{M/F}(C_M)$, the Whittaker
coefficients split according to the two cosets of that norm subgroup. Mellin
transform on the diagonal torus identifies one summand with a character $\theta$ of
$C_M$; the other summand is its conjugate $\theta^\tau$. At every unramified place
the two resulting character values have sum and product equal to the Satake trace and
determinant of $\pi_v$. The all-place construction of quadratic automorphic induction
in Book 45 therefore produces $\operatorname{AI}_{M/F}(\theta)$ with the same
components as $\pi$ outside a finite set. Strong multiplicity one identifies the two
representations. Finally $\theta=\theta^\tau$ would make that induction noncuspidal,
contrary to the hypothesis on $\pi$. $\square$

The lemma is global: a collection of local quadratic symmetries would not by itself
produce the single Hecke character $\theta$.

**Theorem 10.2 (cuspidality criterion).** Let $\pi$ be cuspidal on
$\mathrm{GL}_2(\mathbb A_F)$. Then $\operatorname{BC}_{E/F}(\pi)$ is cuspidal if and
only if

$$
\pi\otimes\chi\not\cong\pi
$$

for every nontrivial $\chi\in X(E/F)$.

**Proof strategy.** If a self-twist exists, compare central characters to prove that
it is quadratic, identify $\pi$ as automorphic induction from the corresponding
quadratic subfield, and restrict the induced parameter to $E$; the result splits.
Conversely, if the lift is not cuspidal, write it as a two-character isobaric sum. Its
cyclic descent datum permutes the two characters, producing an index-two subgroup and
hence a quadratic character downstairs. Spectral descent then gives the corresponding
self-twist.

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
$\chi\in X(E/F)$, class field theory says $M\subseteq E$. Restriction to $E$ then
splits the induced parameter into the two character lines

$$
\theta_E=\theta\circ N_{E/M},
\qquad
\theta_E^\tau=\theta^\tau\circ N_{E/M}.
$$

Therefore

$$
\operatorname{BC}_{E/F}(\pi)
=\theta_E\boxplus\theta_E^\tau,
$$

which is not cuspidal.

Conversely, suppose the lift is noncuspidal. By Theorem 7.1 it has the form
$\xi_1\boxplus\xi_2$. The cyclic descent datum preserves the unordered pair
$\{\xi_1,\xi_2\}$. If it fixed each character through the whole group, both would
descend to $F$, and the source parameter would be reducible at almost every place;
strong multiplicity one would contradict cuspidality of $\pi$. Hence $\Gamma$ acts
transitively on the two characters. The stabilizer has index two, defining a quadratic
subextension $M/F$ contained in $E$. Descent of one character to $M$ gives $\theta$,
and automorphic induction gives
$\pi\cong\operatorname{AI}_{M/F}(\theta)$. Thus
$\pi\otimes\eta_{M/F}\cong\pi$, and
$\eta_{M/F}\in X(E/F)$. $\square$

The proof shows more than noncuspidality: it determines the only possible Eisenstein
output and the unique quadratic field responsible for it.

### 10.2 Odd degree

If $n$ is odd, the cyclic group $X(E/F)$ has no nontrivial quadratic character. Since
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

### 10.3 Even degree and the unique quadratic subextension

Suppose $n$ is even. A cyclic extension has a unique quadratic subextension

$$
F\subset M\subset E,
$$

and $X(E/F)$ has a unique character of order two, namely $\eta_{M/F}$. The criterion
becomes

$$
\operatorname{BC}_{E/F}(\pi)\text{ noncuspidal}
\quad\Longleftrightarrow\quad
\pi\otimes\eta_{M/F}\cong\pi.
$$

Equivalently,

$$
\pi\cong\operatorname{AI}_{M/F}(\theta)
$$

for a non-$\tau$-invariant Hecke character $\theta$ of $M$. There cannot be a
self-twist of order four hiding elsewhere in $X(E/F)$: central characters already
force the square of any self-twist to be trivial.

The output is exactly

$$
\boxed{
\operatorname{BC}_{E/F}(\operatorname{AI}_{M/F}\theta)
=(\theta\circ N_{E/M})
\boxplus
(\theta^\tau\circ N_{E/M}).
}
$$

The two displayed characters may become equal after pullback to $E$. In that case the
output is the repeated isobaric sum $\xi\boxplus\xi$. It is still an Eisenstein
isobaric representation and is not to be called cuspidal.

### 10.4 Why local splitting is not the criterion

A supercuspidal component of $\pi$ may become principal series at one place without
destroying global cuspidality. Conversely, the noncuspidal dihedral lift may have
irreducible principal-series components at almost every place. Cuspidality is governed
by the global character $\eta_{M/F}$ and the global isomorphism
$\pi\otimes\eta_{M/F}\cong\pi$, not by the type at any single place.

For instance, choose $v$ splitting in $M/F$. Then
$\pi_v$ attached to an automorphic induction is already principal series. At an inert
place it may be supercuspidal if the local inducing character is noninvariant. Both
local behaviors belong to the same cuspidal $\pi$ over $F$, and both become the two
character lines after global base change to a field containing $M$.

### 10.5 Self-twist order and orbit size

Let

$$
\operatorname{Stab}_X(\pi)
=\{\chi\in X(E/F):\pi\otimes\chi\cong\pi\}.
$$

For cuspidal $\pi$ this group is either trivial or the order-two group generated by
$\eta_{M/F}$. Hence the orbit has size

$$
\frac n{|\operatorname{Stab}_X(\pi)|}
=
\begin{cases}
n,&\operatorname{BC}\pi\text{ cuspidal},\\
n/2,&\operatorname{BC}\pi\text{ noncuspidal}.
\end{cases}
$$

After the $1/n$ trace normalization these contribute respectively $1$ and $1/2$.
This numerical check ties the cuspidality theorem back to the twisted trace formula.

## 11. Descent, image, and fibers

### 11.1 The global image problem

Every base-change lift is $\Gamma$-invariant. The converse asks whether a
$\Gamma$-invariant cuspidal representation $\Pi$ of
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
Hecke character $\omega$ of $C_F$. Therefore every invariant central character has at
least one norm antecedent.

The antecedent is not unique. If $\omega$ and $\omega'$ have the same norm pullback,
then

$$
\omega'/\omega\in X(E/F).
$$

This ambiguity will interact with the square in the central character of a twist.

### 11.3 Descent theorem

**Theorem 11.1 (cuspidal descent).** Let $\Pi$ be a cuspidal automorphic
representation of $\mathrm{GL}_2(\mathbb A_E)$. Then the following are equivalent:

1. $\Pi^\sigma\cong\Pi$;
2. there is a cuspidal automorphic representation $\pi$ of
   $\mathrm{GL}_2(\mathbb A_F)$ such that
   $\operatorname{BC}_{E/F}(\pi)\cong\Pi$.

Every such descent is cuspidal.

**Proof strategy.** Necessity is Galois invariance of base change. For sufficiency,
choose a Whittaker-normalized cyclic intertwiner on $\Pi$ and a norm antecedent of its
central character. Insert $\Pi$ into the twisted spectral distribution and vary
matching source functions. Linear independence forces an ordinary automorphic
constituent over $F$. Local matching recovers its component at every place. Because a
noncuspidal source has noncuspidal base change, this constituent is cuspidal.

**Proof.** If $\Pi=\operatorname{BC}(\pi)$, Theorem 7.1 gives invariance. Conversely,
assume invariance and normalize $A_\sigma$ in the global Whittaker model. Section 11.2
supplies $\omega$ with $\Omega=\omega\circ N$. Choose $\phi$ having nonzero twisted
trace on $\Pi$ and vary its matching functions $f$. In the identity
$I_F^{\mathrm{norm}}(f)=I_E^\sigma(\phi)$, linear independence of Hecke characters
forces an automorphic representation $\pi$ on the source side with the predicted
unramified parameters. Varying one place at a time and applying the local twisted
character identity gives

$$
\operatorname{BC}_{E_w/F_v}(\pi_v)\cong\Pi_w
$$

for every $w\mid v$. Hence $\operatorname{BC}(\pi)\cong\Pi$ by uniqueness. If $\pi$
were noncuspidal, it would be an isobaric sum of characters and its base change would
remain such a sum, contradicting cuspidality of $\Pi$. $\square$

Thus the global image among cuspidal representations is exactly the invariant
cuspidal spectrum. The central-character condition is present in the proof but is
automatic from invariance because $E/F$ is cyclic.

### 11.4 The precise condition for a prescribed central character

Fix one descent $\pi_0$ of $\Pi$, and write $\omega_0=\omega_{\pi_0}$. Every other
descent in its twisting fiber has the form $\pi_0\otimes\chi$, with central character

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

If $n$ is odd, squaring is an automorphism of the cyclic group $X(E/F)$, so every norm
antecedent $\omega$ occurs. If $n$ is even, $X/X^2$ has order two. Exactly one of the
two square classes of norm antecedents occurs as a descent central character. Thus
the statement “$\Omega$ descends” is weaker than “a descent exists with this chosen
$\omega$.”

### 11.5 Fibers of base change

**Theorem 11.2 (cuspidal fibers).** Let $\pi$ and $\pi'$ be cuspidal automorphic
representations of $\mathrm{GL}_2(\mathbb A_F)$. If their base changes are isomorphic,
then

$$
\pi'\cong\pi\otimes\chi
$$

for some $\chi\in X(E/F)$. Conversely every such twist has the same base change.

**Proof strategy.** At almost every unramified place, equality after restriction says
that the two Frobenius conjugacy classes differ by a character of the cyclic quotient.
The twisted trace formula makes these local choices global and constant across places.
Strong multiplicity one then identifies the twist.

**Proof.** The converse is norm pullback compatibility. For the forward direction,
compare the two source contributions to the same invariant twisted character. The
spectral orbit decomposition in Section 5.2 shows that they lie in one
$X(E/F)$-orbit. Equivalently, local descent data differ by quotient characters, and
the product formula globalizes the quotient character to a member of $X(E/F)$.
Strong multiplicity one gives the asserted global isomorphism. $\square$

If the common lift is cuspidal, the $X$-action is free: a nontrivial stabilizer would
make the lift noncuspidal by Theorem 10.2. Hence the set of descents of a cuspidal
$\Pi$ is an $X(E/F)$-torsor and has exactly $n$ elements.

If the common lift is noncuspidal, the source $\pi$ has the quadratic stabilizer
$\{1,\eta_{M/F}\}$. Its twisting fiber has $n/2$ distinct cuspidal members. Saying
that every fiber has $n$ elements would therefore be false.

### 11.6 A counterexample involving only central characters

Assume $n$ is even and let $\eta$ be the unique quadratic member of $X(E/F)$. If the
common lift is cuspidal, then $\eta$ cannot stabilize a descent. Consequently
$\pi$ and $\pi\otimes\eta$ are two **distinct** descents, while $\eta^2=1$ shows that
they have the same central character as well as the same base change. Thus fixing the
central character does not remove all descent ambiguity in even degree. At the
noncuspidal dihedral boundary the same quadratic character is instead the stabilizer,
so the two displayed twists are one isomorphism class; this is exactly why that fiber
has $n/2$ rather than $n$ elements.

Conversely, if $\chi$ generates $X(E/F)$ and $n$ is odd, the central characters
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
corresponding pulled-back infinity types.

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

All subtlety is localized in the conductor rules of Book 46; no extra global
correction is introduced.

### 13.2 Split and unramified places

If $v$ splits completely, $E_w=F_v$ and $c_w=a(\pi_v)$ at each of the $n$ places.
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

| component over $F_v$ | component over $E_w$ | condition |
|---|---|---|
| spherical | spherical | always |
| $I(\chi_1,\chi_2)$ | $I(\chi_1\circ N,\chi_2\circ N)$ | interpret the reducible boundary |
| $\operatorname{St}\otimes\mu$ | $\operatorname{St}\otimes(\mu\circ N)$ | monodromy persists |
| supercuspidal | supercuspidal | restricted Weil representation irreducible |
| supercuspidal | principal series | restricted Weil representation splits |

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

Another character of the same conductor exponent but nontrivial on local norms need
not cancel. Equal downstairs levels have produced different upstairs levels. No
formula depending only on $a(\pi_v)$, $e_v$, and $f_v$ can therefore be exact at all
ramified places.

## 14. Compatibility with global Jacquet--Langlands

### 14.1 The comparison to be justified

Let $D$ be a quaternion algebra over $F$, let $\rho$ be a noncharacter automorphic
representation of $D^\times(\mathbb A_F)$, and put

$$
\pi=\operatorname{JL}_{D/F}(\rho).
$$

Scalar extension gives $D_E=D\otimes_FE$. It is tempting simply to write
$\operatorname{BC}(\rho)$ and assert that Jacquet--Langlands commutes with base
change. That notation is meaningful only after two checks: the local restricted
parameter must belong to the correct inner-form image at every ramified place of
$D_E$, and the split-side base change must be cuspidal if it is to come from a
noncharacter representation of a nonsplit inner form.

### 14.2 Local Brauer invariants

If $v$ ramifies in $D$ and $w\mid v$, then

$$
\operatorname{inv}_w(D_E)
=[E_w:F_v]\operatorname{inv}_v(D)
=\frac{[E_w:F_v]}2\pmod{\mathbb Z}.
$$

Thus $D_E$ ramifies at $w$ exactly when $D$ ramifies at $v$ and
$[E_w:F_v]$ is odd. A place where $D$ is split never becomes ramified after scalar
extension.

At odd local degree, restriction of an irreducible two-dimensional Weil parameter
remains irreducible, while a special parameter remains special. Hence a discrete
parameter downstairs remains discrete wherever $D_E$ is division. At even local
degree the quaternion algebra splits, and the restricted parameter is allowed to
become principal series. This is exactly the local compatibility of Books 41 and 46.

### 14.3 The global commuting square

Assume first that $\operatorname{BC}_{E/F}(\pi)$ is cuspidal. Its component is discrete
series at every place where $D_E$ ramifies. The image theorem for global
Jacquet--Langlands gives a unique noncharacter automorphic representation $\rho_E$ of
$D_E^\times(\mathbb A_E)$ satisfying

$$
\operatorname{JL}_{D_E/E}(\rho_E)
=\operatorname{BC}_{E/F}(\pi).
$$

Define $\operatorname{BC}_{E/F}^D(\rho)=\rho_E$. Then

$$
\begin{array}{ccc}
\rho&\xrightarrow{\operatorname{JL}_{D/F}}&\pi\\
\downarrow\operatorname{BC}^D&&\downarrow\operatorname{BC}\\
\rho_E&\xrightarrow{\operatorname{JL}_{D_E/E}}&
\operatorname{BC}(\pi)
\end{array}
$$

commutes by construction, and its local components commute because both routes
restrict the same Weil--Deligne parameter. This derivation proves compatibility of
central characters, duals, twists, conductors, local factors, and algebraic weights
wherever both inner forms are meaningful.

### 14.4 The noncuspidal boundary

If $\operatorname{BC}(\pi)$ is a two-character isobaric sum, it is not the global
Jacquet--Langlands transfer of a noncharacter automorphic representation on a division
inner form. No $\rho_E$ of the preceding kind exists when $D_E$ is nonsplit. This is a
global boundary even though each local restricted parameter exists.

If $D_E\cong M_2(E)$ globally, the lower inner form is the split group itself and the
isobaric representation remains meaningful. The lower horizontal arrow is then the
identity; there is no claim that the output is cuspidal.

For odd $[E:F]$, base change of a cuspidal $\pi$ is cuspidal, so the global square
always exists. For even degree, one must test the unique quadratic self-twist before
placing a cuspidal representation in the lower-left corner.

### 14.5 Levels and weights through the square

Where both $D$ and $D_E$ are division, the division-side level change is computed by
restricting the common parameter and applying the local Jacquet--Langlands conductor
dictionary. Where $D$ is division but $D_E$ splits, one obtains directly the split
representation over $E_w$; it may be Steinberg, supercuspidal, or principal series.
Multiplying an old quaternionic level by an extension discriminant does not encode
these alternatives.

At a ramified real place of $D$, scalar extension to a complex place splits the
quaternion algebra. The compact highest-weight representation first transfers to the
real discrete series and then restricts to its complex principal-series parameter.
The same result comes from scalar-extending the common parameter. Thus the
highest-weight-to-lowest-weight shift of Jacquet--Langlands and the real-to-complex
rule of Chapter 9 are compatible.

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

Let $F$ be totally real and let $E/F$ be cyclic with $E$ a CM field. Since complex
conjugation has order two, the extension has even degree. It has a unique quadratic
subextension $M/F$. If $[E:F]\equiv2\pmod4$, then $M$ is CM; if $4\mid[E:F]$,
complex conjugation lies in $\operatorname{Gal}(E/M)$ and $M$ is totally real. Thus
the quadratic field controlling cuspidality need not be the visibly complex layer.

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

If $\pi$ has no self-twist by the character of the unique quadratic subextension, its
lift is cuspidal. If it is dihedral from that subextension, the lift is Eisenstein.
Real-to-CM behavior alone does not decide cuspidality.

### 15.3 A dihedral representation becoming Eisenstein

Let $M/F$ be quadratic, let $E/F$ be cyclic with $M\subset E$, and choose a Hecke
character $\theta$ of $M$ with $\theta\ne\theta^\tau$. Put

$$
\pi=\operatorname{AI}_{M/F}(\theta).
$$

Then $\pi$ is cuspidal and $\pi\otimes\eta_{M/F}\cong\pi$. Since
$\eta_{M/F}\in X(E/F)$, its base change is noncuspidal. Direct restriction gives

$$
\operatorname{BC}_{E/F}(\pi)
=(\theta\circ N_{E/M})
\boxplus
(\theta^\tau\circ N_{E/M}).
$$

Its central character is the product of these two characters. Meanwhile

$$
\omega_\pi=\eta_{M/F}\,\theta|_{C_F}.
$$

Pullback by $N_{E/F}$ kills $\eta_{M/F}$ and gives the same product. This checks the
often missed quadratic determinant factor.

At a place inert in $M$, a supercuspidal component can split after base change to a
place of $E$ containing $M_v$. At a split place the component was already principal
series. These different local histories assemble into the same isobaric sum.

### 15.4 An odd-degree cuspidal lift

Let $E/F$ be cyclic of degree three and let $\pi$ be any cuspidal representation. The
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

**Theorem 16.1 (global cyclic base change and descent for $\mathrm{GL}_2$).** Let
$E/F$ be cyclic of degree $n$, and put

$$
X(E/F)=\widehat{C_F/N_{E/F}(C_E)}.
$$

For every cuspidal automorphic $\pi$ on $\mathrm{GL}_2(\mathbb A_F)$ there is a
unique automorphic isobaric $\Pi=\operatorname{BC}_{E/F}(\pi)$ on
$\mathrm{GL}_2(\mathbb A_E)$ with these properties.

1. For every $v$ and $w\mid v$,

   $$
   \Pi_w\cong\operatorname{BC}_{E_w/F_v}(\pi_v),
   $$

   by restriction of the full local Weil--Deligne parameter.

2. It is $\Gamma$-invariant, has
   $\omega_\Pi=\omega_\pi\circ N_{E/F}$, and commutes with twists and duals.

3. At an unramified $w\mid v$, its Satake pair is
   $\{\alpha_v^{f(w/v)},\beta_v^{f(w/v)}\}$. Conductors, local types,
   archimedean parameters, and local factors are those of parameter restriction.

4. It is cuspidal exactly when $\pi$ has no nontrivial self-twist in $X(E/F)$. Such a
   self-twist is quadratic. Every odd-degree lift is cuspidal. In even degree, with
   quadratic subfield $M/F$, failure occurs precisely for
   $\pi=\operatorname{AI}_{M/F}(\theta)$, and then

   $$
   \Pi=(\theta\circ N_{E/M})
   \boxplus(\theta^\tau\circ N_{E/M}).
   $$

5. A cuspidal representation over $E$ lies in the image exactly when it is
   $\Gamma$-invariant. Its descents form an $X(E/F)$-torsor.

6. For cuspidal sources, two base changes agree exactly when the sources differ by a
   member of $X(E/F)$. When their common lift is noncuspidal, the quadratic
   self-twist is the stabilizer and the fiber of cuspidal sources has $n/2$ distinct
   members.

7. If $\Omega$ is the central character of an invariant cuspidal $\Pi$, then
   $\Omega=\omega\circ N$ for some $\omega$. Relative to one descent of central
   character $\omega_0$, a descent with prescribed central character $\omega$ exists
   exactly when $\omega/\omega_0\in X(E/F)^2$.

8. Regular algebraic and cohomological weights pull back along embeddings, algebraic
   conjugation commutes with base change, and the field of rationality can shrink
   precisely because coefficient conjugation can move $\pi$ in its norm-character
   twisting orbit.

9. If $D/F$ is quaternionic and the split-side lift is cuspidal, global
   Jacquet--Langlands commutes with base change to $D\otimes_FE$. At each place this is
   restriction of the common parameter; the assertion stops at the isobaric boundary
   when no cuspidal inner-form representation exists.

**Proof.** Chapters 5 and 6 construct the lift by comparing ordinary and twisted trace
formulas. The local matching trace identity identifies all components, and strong
multiplicity one gives uniqueness. Chapters 8 and 9 give the Hecke, factor, conductor,
type, and archimedean formulas. Chapter 10 proves the self-twist criterion through
automorphic induction. Chapter 11 proves descent and fibers while retaining the
central square class. Chapters 12--14 establish algebraic, level, and inner-form
compatibilities. $\square$

### 16.2 The data passed to cyclic towers

The theorem concerns one cyclic extension, and we stop there. Its durable inputs for
a later tower argument are nevertheless clear:

- every local component is characterized by parameter restriction;
- norm directions and central characters are functorial;
- the kernel of a cyclic step is its finite norm-character group;
- cuspidality can fail only at a quadratic self-twist, with an explicit isobaric sum;
- invariant cuspidal representations descend, with controlled fibers and central
  square classes;
- conductors, weights, coefficient fields, and inner-form conditions are checked one
  place at a time.

No solvable extension has been treated here. Compatibility among different cyclic
factorizations, accumulation of twisting ambiguity, and descent through a solvable
tower belong to Book 48.

### 16.3 Conclusion

Cyclic base change begins with a reversal of arrows. The field extension points from
$F$ to $E$, local parameters restrict from the Weil group of $F$ to that of $E$, and
idele-class characters follow the same arithmetic operation by pulling back along the
norm from $E$ to $F$. Once this direction is fixed, central characters, twists,
Frobenius powers, and local factors all follow from one restriction principle.

The global theorem requires more. Twisted conjugacy turns
$\delta\sigma(\delta)\cdots\sigma^{n-1}(\delta)$ into an ordinary norm class. Matching
orbital integrals identifies regular tori, while singular germs control the center,
unipotent orbit, and continuous spectrum. Whittaker-normalized cyclic intertwiners make
the spectral trace factor locally. The resulting identity constructs an automorphic
object with the prescribed component at every place; strong multiplicity one then
makes it unique.

The exceptional spectrum is informative. A cuspidal rank-two representation can be
stabilized by a norm character only when that character is quadratic. It is then
dihedral, induced from the unique quadratic subfield of an even-degree cyclic
extension, and restriction exposes its two characters as an isobaric Eisenstein sum.
Odd-degree cyclic base change is therefore always cuspidal.

In the reverse direction, Galois invariance is the image condition for cuspidal
representations. Norm characters measure the full fiber, while their squares measure
which prescribed central characters occur. This distinction survives at infinity, in
fields of rationality, and through global Jacquet--Langlands. The result is a complete
one-step transfer theorem: globally constructed, locally exact, explicit at its
cuspidal boundary, and ready to serve as the indivisible cyclic unit of the later
solvable theory.
