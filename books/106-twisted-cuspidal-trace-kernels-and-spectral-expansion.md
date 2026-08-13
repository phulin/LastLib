# Twisted Cuspidal Trace Kernels and Spectral Expansion

## Contents

- [Introduction](#introduction)
- [1. The twisted spectral problem](#1-the-twisted-spectral-problem)
  - [1.1 From a field automorphism to a trace](#11-from-a-field-automorphism-to-a-trace)
  - [1.2 Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
  - [1.3 Determinant-one and central-character realizations](#13-determinant-one-and-central-character-realizations)
  - [1.4 The theorem to be proved](#14-the-theorem-to-be-proved)
- [2. The twisting operator and twisted convolution](#2-the-twisting-operator-and-twisted-convolution)
  - [2.1 The unitary field-automorphism operator](#21-the-unitary-field-automorphism-operator)
  - [2.2 Convolution followed by twisting](#22-convolution-followed-by-twisting)
  - [2.3 Kernel conventions and the diagonal](#23-kernel-conventions-and-the-diagonal)
  - [2.4 Adjoints and cyclic powers](#24-adjoints-and-cyclic-powers)
- [3. Test functions that close the cusp](#3-test-functions-that-close-the-cusp)
  - [3.1 The admissible global test space](#31-the-admissible-global-test-space)
  - [3.2 Two-sided strong cuspidality](#32-two-sided-strong-cuspidality)
  - [3.3 Why one local zero is global](#33-why-one-local-zero-is-global)
  - [3.4 Sources of strongly cuspidal factors](#34-sources-of-strongly-cuspidal-factors)
- [4. Construction and decay of the twisted kernel](#4-construction-and-decay-of-the-twisted-kernel)
  - [4.1 Absolute convergence before taking a trace](#41-absolute-convergence-before-taking-a-trace)
  - [4.2 Cuspidality in both variables](#42-cuspidality-in-both-variables)
  - [4.3 Simultaneous rapid decay](#43-simultaneous-rapid-decay)
  - [4.4 The diagonal distribution](#44-the-diagonal-distribution)
- [5. Trace class and the diagonal trace theorem](#5-trace-class-and-the-diagonal-trace-theorem)
  - [5.1 Why integrability of the diagonal is not enough](#51-why-integrability-of-the-diagonal-is-not-enough)
  - [5.2 A cuspidal Sobolev factorization](#52-a-cuspidal-sobolev-factorization)
  - [5.3 Trace-norm continuity](#53-trace-norm-continuity)
  - [5.4 Equality of operator trace and kernel diagonal](#54-equality-of-operator-trace-and-kernel-diagonal)
- [6. The automorphism on the cuspidal spectrum](#6-the-automorphism-on-the-cuspidal-spectrum)
  - [6.1 Permutation of isotypic summands](#61-permutation-of-isotypic-summands)
  - [6.2 Stable representations and intertwiners](#62-stable-representations-and-intertwiners)
  - [6.3 The automorphic normalization](#63-the-automorphic-normalization)
  - [6.4 Multiplicity spaces and the general block trace](#64-multiplicity-spaces-and-the-general-block-trace)
- [7. Factorization of twisted traces](#7-factorization-of-twisted-traces)
  - [7.1 Local packets over a place of the base field](#71-local-packets-over-a-place-of-the-base-field)
  - [7.2 Coherent local intertwiners](#72-coherent-local-intertwiners)
  - [7.3 A finite tensor trace lemma](#73-a-finite-tensor-trace-lemma)
  - [7.4 The cyclic trace lemma at a split place](#74-the-cyclic-trace-lemma-at-a-split-place)
- [8. The cuspidal twisted spectral expansion](#8-the-cuspidal-twisted-spectral-expansion)
  - [8.1 Blockwise computation](#81-blockwise-computation)
  - [8.2 Absolute convergence](#82-absolute-convergence)
  - [8.3 The factored cuspidal formula](#83-the-factored-cuspidal-formula)
  - [8.4 Dependence on normalization](#84-dependence-on-normalization)
- [9. The continuous channel and its annihilation](#9-the-continuous-channel-and-its-annihilation)
  - [9.1 Eisenstein data over the extension field](#91-eisenstein-data-over-the-extension-field)
  - [9.2 How the field automorphism acts on inducing data](#92-how-the-field-automorphism-acts-on-inducing-data)
  - [9.3 Vanishing before regularization](#93-vanishing-before-regularization)
  - [9.4 Scattering terms and derivatives](#94-scattering-terms-and-derivatives)
- [10. Residues and the exhaustion of the noncuspidal spectrum](#10-residues-and-the-exhaustion-of-the-noncuspidal-spectrum)
  - [10.1 The residual determinant characters](#101-the-residual-determinant-characters)
  - [10.2 Two proofs of residual vanishing](#102-two-proofs-of-residual-vanishing)
  - [10.3 No hidden fourth channel](#103-no-hidden-fourth-channel)
  - [10.4 The full noncuspidal annihilation theorem](#104-the-full-noncuspidal-annihilation-theorem)
- [11. The twisted simple trace formula](#11-the-twisted-simple-trace-formula)
  - [11.1 The geometric distribution recalled](#111-the-geometric-distribution-recalled)
  - [11.2 Equality of spectral and geometric traces](#112-equality-of-spectral-and-geometric-traces)
  - [11.3 The fixed-central-character formula](#113-the-fixed-central-character-formula)
  - [11.4 Measures and change of generator](#114-measures-and-change-of-generator)
- [12. Twisted pseudo-coefficients and exact selection](#12-twisted-pseudo-coefficients-and-exact-selection)
  - [12.1 Why an ordinary selector needs adjustment](#121-why-an-ordinary-selector-needs-adjustment)
  - [12.2 Construction at an invariant field place](#122-construction-at-an-invariant-field-place)
  - [12.3 Selection on a cyclic orbit of places](#123-selection-on-a-cyclic-orbit-of-places)
  - [12.4 Level and Hecke factors](#124-level-and-hecke-factors)
- [13. Application to cyclic base change](#13-application-to-cyclic-base-change)
  - [13.1 Local base change and invariance](#131-local-base-change-and-invariance)
  - [13.2 Descent ambiguity and cyclic normalization](#132-descent-ambiguity-and-cyclic-normalization)
  - [13.3 The unramified power map in the spectral sum](#133-the-unramified-power-map-in-the-spectral-sum)
  - [13.4 The trace-comparison mechanism](#134-the-trace-comparison-mechanism)
  - [13.5 What the application proves at this stage](#135-what-the-application-proves-at-this-stage)
- [14. Examples and boundary phenomena](#14-examples-and-boundary-phenomena)
  - [14.1 A split place](#141-a-split-place)
  - [14.2 An inert unramified place](#142-an-inert-unramified-place)
  - [14.3 A quadratic invariant discrete representation](#143-a-quadratic-invariant-discrete-representation)
  - [14.4 Failure modes](#144-failure-modes)
- [15. Final synthesis](#15-final-synthesis)
  - [15.1 The complete implication chain](#151-the-complete-implication-chain)
  - [15.2 The reusable theorem package](#152-the-reusable-theorem-package)
  - [15.3 Conclusion](#153-conclusion)

## Introduction

A cyclic extension $E/F$ carries two kinds of symmetry at once.  The group
$\mathrm{GL}_2(\mathbf A_E)$ acts by right translation on automorphic functions, while a
generator $\sigma$ of $\operatorname{Gal}(E/F)$ acts by applying $\sigma$ to every matrix
entry and every adelic coordinate.  Ordinary harmonic analysis studies convolution by a test
function.  Cyclic base change asks for the trace of convolution followed by this field
automorphism.

That trace is not obtained by placing a decorative superscript $\sigma$ on the ordinary trace
formula.  On the geometric side, the diagonal kernel groups rational matrices by
$\sigma$-conjugacy,

$$
\delta\sim x^{-1}\delta\sigma(x).
$$

On the spectral side, the automorphism permutes irreducible automorphic representations.  A
noninvariant representation contributes no diagonal block.  An invariant representation does
contribute, but only after an intertwining operator has been chosen and normalized.  Multiplying
that intertwiner by a root of unity changes every twisted character value.  The normalization
must therefore come from the automorphic action itself, not from an arbitrary local choice.

There is also an analytic issue.  The automorphic quotient is noncompact, and twisting does not
remove its Eisenstein spectrum.  We select test functions with one strongly cuspidal local
factor.  Its two-sided unipotent transform is zero.  This makes the kernel cuspidal in both
variables, gives rapid decay in the cusp, and makes the associated operator trace class.  At the
same time, the same local zero annihilates every parabolically induced representation as an
operator.  Consequently continuous scattering expressions vanish before traces or derivatives
of intertwiners have to be evaluated.  Residual determinant characters vanish by a direct
constant-term calculation; Laurent coefficients give a second proof when the selected factor
is compactly supported modulo the center.

The main theorem is an honest twisted simple trace formula.  Its left side is the trace of a
trace-class operator and an absolutely convergent sum of twisted traces on $\sigma$-stable
cuspidal representations.  Its right side is the convergent twisted geometric distribution:
the scalar channel, regular elliptic projective twisted classes whose actual norms satisfy the
torus condition, and, in quadratic degree, the exceptional scalar-norm classes with quaternion
division centralizer.  Split regular and nonsemisimple classes have already cancelled together
in the parabolic channel.

The final chapters explain precisely how this formula serves cyclic base change.  Local base
change produces $\sigma$-invariant representations over $E$ and prescribes the unramified power
map on Satake parameters.  Twisted pseudo-coefficients isolate invariant local types, while
spherical functions record the power map.  Comparing the twisted formula over $E$ with an
ordinary formula over $F$ then has a completely specified spectral meaning.  The local equality
of orbital integrals is a separate local theorem, and global comparison additionally requires
the projective norm-fiber and centralizer-coefficient identity recorded in Chapter 13; we
isolate those boundaries rather than building them into the present argument.

## 1. The twisted spectral problem

The first task is to state the trace problem in a form in which actions, centers, and measures
cannot drift apart.  Twisted formulas are especially sensitive to inverse conventions: changing
$\sigma$ to $\sigma^{-1}$ in one place reverses the intertwining relation and changes the
ordered norm on the geometric side.

### 1.1 From a field automorphism to a trace

Let $E/F$ be cyclic of prime degree $\ell$, and fix a generator
$\sigma\in\operatorname{Gal}(E/F)$.  Put

$$
H=\operatorname{Res}_{E/F}\mathrm{GL}_2,
\qquad
H(F)=\mathrm{GL}_2(E),
\qquad
H(\mathbf A_F)=\mathrm{GL}_2(\mathbf A_E).
$$

Applying $\sigma$ entrywise is an $F$-automorphism of $H$.  If $R(f)$ denotes right
convolution, the operator of interest is

$$
T_\sigma(f)=R(f)U_\sigma,
$$

where $U_\sigma$ transports an automorphic function by the field automorphism.  The order is
part of the definition.  Its kernel will contain $x^{-1}\delta\sigma(y)$; reversing the two
operators would instead produce a conjugate convention.

The spectral question is now concrete.  Which irreducible automorphic summands are preserved by
$U_\sigma$?  What is the trace of $T_\sigma(f)$ on such a summand?  Why is the total series
absolutely convergent?  Why do induced and residual summands contribute zero?  The answers must
be established before the symbol $\operatorname{tr}T_\sigma(f)$ is treated as a trace formula.

### 1.2 Standing hypotheses and notation

Write $\mathbf A_E$ for the adeles of $E$, $G_E=\mathrm{GL}_{2/E}$, and $Z_E$ for its scalar
center.  The standard Borel is $B_E=T_EN_E$, with

$$
N_E=\left\{n(u)=\begin{pmatrix}1&u\\0&1\end{pmatrix}:u\in\mathbf G_a\right\}.
$$

At a finite place $w$ of $E$, $|\varpi_w|_w=q_w^{-1}$; at a complex place, the normalized
absolute value is the square of the usual modulus.  Maximal compact subgroups have probability
measure.  Additive measures are self-dual for the standard trace character, so

$$
\operatorname{vol}(E\backslash\mathbf A_E)=1.
$$

Group measures are the corresponding Iwasawa measures, and all quotient measures are induced
by quotient integration.  These are the conventions already used for the untwisted cuspidal
spectral formula and the twisted geometric distribution.

The prime-degree hypothesis is needed for the clean geometric classification.  The spectral
construction of $T_\sigma(f)$ works for an arbitrary finite cyclic extension, but the final
geometric formula invoked in Chapter 11 has the prime-degree scalar-norm classification.  We
state hypotheses where they are used rather than allowing prime degree to masquerade as an
analytic requirement.

### 1.3 Determinant-one and central-character realizations

The determinant-one quotient is

$$
X_E^1=G_E(E)\backslash G_E(\mathbf A_E)^1,
\qquad
G_E(\mathbf A_E)^1=\{g:|\det g|_{\mathbf A_E}=1\}.
\tag{1.1}
$$

It has finite volume.  Since rational points have determinant module one and $\sigma$ preserves
the module, $U_\sigma$ acts unitarily on $L^2(X_E^1)$.

For spectral applications it is often preferable to fix a unitary Hecke character

$$
\Omega:E^\times\backslash\mathbf A_E^\times\longrightarrow\mathbf C^\times
$$

satisfying $\Omega\circ\sigma=\Omega$.  Automorphic functions then obey

$$
\phi(zg)=\Omega(z)\phi(g)
$$

and are realized as $\Omega$-equivariant sections over

$$
X_{E,\Omega}=Z_E(\mathbf A_E)G_E(E)\backslash G_E(\mathbf A_E).
\tag{1.2}
$$

A test function has inverse central covariance

$$
f(zg)=\Omega(z)^{-1}f(g).
\tag{1.3}
$$

The condition $\Omega\circ\sigma=\Omega$ is necessary: otherwise $U_\sigma$ carries the
$\Omega$-space to a different central-character space and there is no endomorphism whose trace
could be taken.  The two realizations (1.1) and (1.2) are related by Fourier decomposition along
the compact norm-one idele-class center.  We prove analytic statements in either realization
and state the final base-change formula with fixed central character.

### 1.4 The theorem to be proved

Let $\mathcal A_{\mathrm{cusp}}(E,\Omega)$ be the set of irreducible cuspidal automorphic
representations with central character $\Omega$.  For a $\sigma$-stable representation $\Pi$,
let $A_\Pi$ denote the intertwiner normalized by its automorphic realization, as constructed in
Chapter 6.  Define

$$
\operatorname{tr}_\sigma\Pi(f)
=\operatorname{tr}\bigl(\Pi(f)A_\Pi\bigr).
\tag{1.4}
$$

The goal is the identity

$$
\operatorname{tr}T_\sigma(f)
=\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E,\Omega)\\
                  \Pi^\sigma\simeq\Pi}}
\operatorname{tr}_\sigma\Pi(f)
=J_{\mathrm{geom},\Omega}^\sigma(f),
\tag{1.5}
$$

with absolute convergence on both sides and no continuous or residual term.  If multiplicities
are retained rather than using global multiplicity one, the first sum acquires the finite
multiplicity-space trace described in Section 6.4.  Formula (1.5) is not asserted for an
arbitrary Schwartz function.  The decisive hypothesis is one strongly cuspidal local factor,
together with finite level and finite compact type.

Three established interfaces enter with exactly these hypotheses.  Rank-one constant-term
theory over the number field $E$ says that the noncuspidal space at fixed unitary central
character, level, and compact type is generated by unitary Eisenstein packets and the
determinant characters $\eta\circ\det$ with $\eta^2=\Omega$.  The untwisted cuspidal spectral
theory supplies the discrete finite-multiplicity decomposition, restricted tensor products,
finite-rank local convolution operators, and the cuspidal eigenvalue estimate used in the
trace-class proof.  The prime-degree twisted geometric theory supplies the canonical kernel
diagonal and its absolutely convergent orbit expansion for the same strongly cuspidal test
class.  We prove every new step created by inserting $U_\sigma$: trace class of the twisted
operator, normalization and factorization of its intertwiners, its spectral expansion, and the
annihilation of all noncuspidal twisted terms.

## 2. The twisting operator and twisted convolution

The field automorphism must be made into an operator before it can be inserted into a trace.
This chapter fixes the convention and derives the elementary identities used throughout the
book.  They also explain why the kernel in the geometric theory has exactly its displayed
ordering.

### 2.1 The unitary field-automorphism operator

For an automorphic function $\phi$, define

$$
(U_\sigma\phi)(x)=\phi(\sigma^{-1}(x)).
\tag{2.1}
$$

The inverse in (2.1) is chosen so that $\sigma\mapsto U_\sigma$ is a left action:

$$
U_\sigma U_\tau=U_{\sigma\tau}.
$$

Haar measure is invariant under the finite-order automorphism $\sigma$, so $U_\sigma$ is
unitary.  Moreover $U_\sigma^\ell=1$.

Let $R(g)$ be right translation.  A direct calculation gives

$$
U_\sigma R(g)U_\sigma^{-1}=R(\sigma(g)).
\tag{2.2}
$$

Indeed,

$$
(U_\sigma R(g)U_\sigma^{-1}\phi)(x)
=\phi(x\sigma(g)).
$$

Thus $U_\sigma$ carries a representation $\Pi$ to the transported representation

$$
\Pi^\sigma(g)=\Pi(\sigma^{-1}(g)).
\tag{2.3}
$$

The placement of the inverse differs between (2.2) and (2.3) because one formula describes
conjugation of the group action and the other describes transport of the representation.  With
these definitions, $U_\sigma$ sends the $\Pi$-isotypic subspace to the
$\Pi^\sigma$-isotypic subspace.

### 2.2 Convolution followed by twisting

For a test function satisfying (1.3), set

$$
(R_\Omega(f)\phi)(x)
=\int_{Z_E(\mathbf A_E)\backslash G_E(\mathbf A_E)}
f(g)\phi(xg)\,d\bar g.
\tag{2.4}
$$

The product $f(g)\phi(xg)$ is independent of the central representative.  Define

$$
T_{\sigma,\Omega}(f)=R_\Omega(f)U_\sigma.
\tag{2.5}
$$

Because $U_\sigma$ is unitary,

$$
\|T_{\sigma,\Omega}(f)\|
\leq\|f\|_1.
$$

If $f^\sigma(g)=f(\sigma^{-1}g)$, then (2.2), integrated against $f$, gives

$$
U_\sigma R(f)U_\sigma^{-1}=R(f^\sigma).
\tag{2.6}
$$

Consequently

$$
T_\sigma(f_1)T_\sigma(f_2)
=R(f_1*f_2^\sigma)U_\sigma^2.
\tag{2.7}
$$

Twisted convolution is therefore not a representation of the ordinary convolution algebra;
it belongs naturally to the crossed product by $\langle\sigma\rangle$.

### 2.3 Kernel conventions and the diagonal

The ordinary automorphic kernel of $R(f)$ is

$$
K_f(x,y)=\sum_{\delta\in G_E(E)}f(x^{-1}\delta y)
\tag{2.8}
$$

in the determinant-one realization, with the corresponding projective sum in the
central-character realization.  Since

$$
K_f^\sigma(x,y):=K_f(x,\sigma(y))
=\sum_{\delta\in G_E(E)}f(x^{-1}\delta\sigma(y)),
\tag{2.9}
$$

a change of variable $z=\sigma(y)$ shows that (2.9) is the kernel of $R(f)U_\sigma$:

$$
\int K_f^\sigma(x,y)\phi(y)\,dy
=R(f)(\phi\circ\sigma^{-1})(x).
$$

On the diagonal,

$$
K_f^\sigma(x,x)
=\sum_{\delta}f(x^{-1}\delta\sigma(x)).
\tag{2.10}
$$

Replacing $x$ by $\gamma x$, with $\gamma\in G_E(E)$, changes the index by

$$
\delta\longmapsto\gamma^{-1}\delta\sigma(\gamma).
$$

This proves invariance and explains the geometric orbit relation.  It also shows that the
ordered norm and the spectral intertwiner are governed by the same generator $\sigma$.

### 2.4 Adjoints and cyclic powers

Let $f^*(g)=\overline{f(g^{-1})}$.  From (2.5) and (2.6),

$$
T_\sigma(f)^*
=U_\sigma^{-1}R(f^*)
=R((f^*)^{\sigma^{-1}})U_{\sigma^{-1}}.
\tag{2.11}
$$

Iterating (2.7) gives

$$
T_\sigma(f)^\ell
=R\bigl(f*f^\sigma*\cdots*f^{\sigma^{\ell-1}}\bigr).
\tag{2.12}
$$

Equation (2.12) is an operator analogue of the ordered norm
$\delta\sigma(\delta)\cdots\sigma^{\ell-1}(\delta)$.  It is also a useful consistency
check: any convention that produced the conjugates in the reverse order would be describing a
different twisted kernel.

## 3. Test functions that close the cusp

The noncompact quotient has one parabolic escape direction for each cusp.  Twisting permutes
these directions but does not eliminate them.  The right test condition must annihilate the
parabolic channel as an operator, not merely make one induced trace vanish.

### 3.1 The admissible global test space

At a nonarchimedean place $w$ of $E$, use smooth functions compactly supported modulo the
center with inverse central covariance.  At an archimedean place, use smooth functions that are
finite under left and right maximal compact actions and satisfy the geometric Schwartz
estimates used in the preceding twisted-kernel theory.  Explicitly, for every invariant
differential operator $D$, every $A>0$, and a fixed proper submultiplicative projective height,

$$
|Df_w(g)|\leq C_{D,A}\|g\|_w^{-A}.
$$

This is stronger than mere membership in the Harish--Chandra Schwartz algebra and is the
hypothesis that licenses both the rational-point summation in Chapter 4 and the global orbital
estimates in Chapter 11.  A global admissible function is a finite sum of restricted tensors

$$
f=\bigotimes_w f_w,
\tag{3.1}
$$

spherical almost everywhere.  In the determinant-one realization the same functions are
restricted to $G_E(\mathbf A_E)^1$ after choosing a harmless compact cutoff in the scalar
module direction.

Finite compact type is not cosmetic.  It makes every local operator have finite-dimensional
range on an admissible irreducible representation, and it reduces a global tensor trace to a
finite tensor calculation.  Rapid decrease controls the rational-point sum and all its
derivatives.  The finite sum of tensors permits arbitrary prescribed data at finitely many
places while retaining these two properties.

### 3.2 Two-sided strong cuspidality

Let $k$ be a local field and $G_k=\mathrm{GL}_2(k)$.  A local test function $h$ is
**strongly cuspidal** if

$$
\int_{N(k)}h(x^{-1}tny)\,dn=0
\tag{3.2}
$$

for every $x,y\in G_k$ and $t\in T(k)$.  Absolute convergence is included at an
archimedean place.

The two translations are indispensable.  In the compact picture of normalized induction

$$
I_k(\chi_1,\chi_2;s)
=\operatorname{Ind}_{B(k)}^{G_k}
(\chi_1\otimes\chi_2)|\alpha|^s,
$$

the kernel of the integrated operator between compact-picture points $x$ and $y$ is

$$
\int_{Z(k)\backslash T(k)}\chi_1(a)\chi_2(d)|a/d|^s\delta_B(t)^{1/2}
\left(\int_{N(k)}h(x^{-1}tny)\,dn\right)dt.
\tag{3.3}
$$

The quotient by $Z(k)$ is forced by the fixed central character and removes the otherwise
infinite central factor.  On the unitary axis the integral is the kernel of the honest bounded
induced action, so (3.2) implies

$$
I_k(\chi_1,\chi_2;it)(h)=0
\tag{3.4}
$$

for every genuine unitary principal series with the prescribed central character.  If $k$ is
nonarchimedean and $h$ is compactly supported modulo the center, the compact-picture matrix
entries are Laurent transforms of compactly supported data.  In that case (3.4) extends as the
zero meromorphic family in $s$, including every regular parameter and every Laurent
coefficient at a reducibility point.  No such off-unitary specialization is asserted for a
general archimedean Schwartz coefficient: formal continuation there need not equal honest
convolution on a nonunitary subquotient.  The unitary-axis operator zero is already stronger
than trace zero and is exactly what genuine Eisenstein wave packets require.

### 3.3 Why one local zero is global

Assume one factor $f_{w_0}$ in (3.1) is strongly cuspidal.  For a factorizable global induced
representation,

$$
I_E(\chi_1,\chi_2;it)(f)
=\bigotimes_w I_w(\chi_{1,w},\chi_{2,w};it)(f_w)=0.
\tag{3.5}
$$

The $w_0$-factor is zero by (3.4), so the honest global unitary induced operator is zero.  If
that factor is nonarchimedean and compactly supported modulo the center, the same tensor
identity is meromorphically zero in $s$.  The same assertion can be
grouped by places $v$ of $F$.  If $E_v=\prod_{w\mid v}E_w$ and the local function is a tensor
over $w\mid v$, one zero component makes its integral over
$N(E_v)=\prod_{w\mid v}N(E_w)$ vanish.  Hence the test also satisfies the strong-cuspidality
hypothesis used by the twisted geometric distribution.

For a finite sum of tensors we require a common cuspidal place, or a finite partition into
subfamilies with a common place.  Linearity then reduces all conclusions to the tensor case.
Merely knowing that the total sum has zero parabolic trace would not give the pointwise kernel
cancellation used below.

### 3.4 Sources of strongly cuspidal factors

At a nonarchimedean place, a compactly supported matrix coefficient of a supercuspidal
representation is strongly cuspidal.  Its two-sided unipotent integral factors through the
Jacquet module, which is zero.  After formal-degree normalization, such a coefficient is also
an exact spectral selector.

At a real place, a compact-finite discrete-series coefficient is rapidly decreasing modulo the
center and has zero proper constant term.  Such a coefficient is usable here when it also
satisfies the explicit projective-height estimates of Section 3.1; compactly supported
modulo-center pseudo-coefficients satisfy them automatically.  At a complex place
$\mathrm{GL}_2(\mathbf C)$ has no discrete series modulo center, so an archimedean selector of
this kind is unavailable; a finite supercuspidal place supplies the needed zero instead.  This
is why the twisted theorem is stated with a strongly cuspidal place, not with a real place.

If a place $v$ of $F$ splits completely in $E$, then

$$
H(F_v)=\prod_{j=0}^{\ell-1}\mathrm{GL}_2(F_v).
$$

A tensor with a supercuspidal coefficient on one component and arbitrary admissible factors on
the others is strongly cuspidal on the product.  The automorphism cyclically permutes the
components, a phenomenon treated spectrally in Section 7.4.

## 4. Construction and decay of the twisted kernel

Before a trace can be taken, the rational-point series must define a genuine smooth kernel.
The safe order is: prove local uniform convergence, prove vanishing of both constant terms,
deduce rapid decay, and only then restrict to the diagonal.

Write $X$ for $X_E^1$ in the determinant-one realization and for the central-character
quotient, with its $\Omega$-equivariant line bundle, in the fixed-central-character realization.

### 4.1 Absolute convergence before taking a trace

For an admissible $f$, define $K_f^\sigma$ by (2.9).  The finite support of $f$ confines the
entries of a contributing rational matrix $\delta$ and $\det(\delta)^{-1}$ to fixed fractional
ideals in the determinant-one realization.  In the fixed-central-character realization,
choose a primitive representative of each projective class; only finitely many ideal classes
occur, and the same assertion holds in one fixed fractional lattice for each of them.  On
compact sets of $x$ and $y$, the archimedean estimates of Section 3.1 give, for every $A$,

$$
|f(x^{-1}\delta\sigma(y))|
\leq C_A(1+H(\delta))^{-A},
\tag{4.1}
$$

where $H$ is a matrix height.  Rational matrices of height at most $R$ in the fixed fractional
lattice are $O(R^C)$ for some $C$.  Summing (4.1) over dyadic shells with $A>C+2$ proves
absolute and locally uniform convergence.

Invariant differentiation in $x$ or $y$ replaces $f$ by an invariant derivative, possibly
transported by $\sigma$.  It satisfies the same estimates.  We have therefore proved:

**Proposition 4.1.** The series $K_f^\sigma(x,y)$ and every invariant derivative converge
absolutely and locally uniformly.  The resulting kernel is smooth and of moderate growth.

For later use, it is also the distribution kernel of $T_\sigma(f)$.  If $\phi$ is a smooth
automorphic vector compactly supported modulo the relevant rational and central quotient,
local normal convergence and that compact support permit unfolding:

$$
\int_XK_f^\sigma(x,y)\phi(y)\,dy
=\int_{Z_E(\mathbf A_E)\backslash G_E(\mathbf A_E)}
f(g)\phi(\sigma^{-1}(xg))\,d\bar g
=T_\sigma(f)\phi(x),
\tag{4.1a}
$$

with the center omitted in the determinant-one realization.  Haar invariance under $\sigma$
gives the second equality.  Density and the $L^1$ bound for convolution extend this identity
to the automorphic Hilbert space.

The proof takes place before setting $x=y$.  A diagonal estimate alone would not justify
convolution against an arbitrary $L^2$ function or differentiation in two independent
variables.

### 4.2 Cuspidality in both variables

Fix $y$ and average in the first variable over
$N_E(E)\backslash N_E(\mathbf A_E)$.  Group rational matrices by
$B_E(E)\backslash G_E(E)$ and unfold the rational unipotent sum.  Absolute local uniform
convergence and a preliminary compact truncation justify the grouping.  Each resulting term is
of the form

$$
\int_{N_E(\mathbf A_E)}
f(x_1^{-1}tnx_2)\,dn,
$$

which vanishes by the global form of (3.2).  Hence

$$
\int_{N_E(E)\backslash N_E(\mathbf A_E)}
K_f^\sigma(nx,y)\,dn=0.
\tag{4.2}
$$

For the second variable, use the adjoint kernel.  Define

$$
f^{\sigma,*}(g)=\overline{f(\sigma(g)^{-1})}.
$$

Inversion of $N_E$, conjugation by $T_E$, and (3.2) show that $f^{\sigma,*}$ is strongly
cuspidal.  Moreover

$$
K_{f^{\sigma,*}}^{\sigma^{-1}}(y,x)
=\overline{K_f^\sigma(x,y)}.
$$

Indeed, applying $\sigma$ inside $f^{\sigma,*}$ and reindexing the rational sum by
$\delta\mapsto(\sigma\delta)^{-1}$ gives the displayed identity.  Applying the first-variable
calculation with the generator $\sigma^{-1}$ to this kernel proves vanishing of the second
constant term.  Thus the kernel is cuspidal in both variables, not merely on the diagonal.

### 4.3 Simultaneous rapid decay

The usual rapid-decay theorem is often stated for automorphic vectors finite under the
archimedean infinitesimal center.  Our Schwartz kernel need not satisfy that hypothesis, so we
use the underlying rank-one Fourier argument directly.  Fix the finite level and the finitely
many cusp charts meeting the finite support.  On a compact unipotent cross-section in either
variable, Section 4.2 says that the zero Fourier coefficient vanishes.  The restriction of the
kernel to a product of two such cross-sections is therefore a double Fourier series indexed by
nonzero points of two fixed fractional lattices.

At cusp heights $H_x$ and $H_y$, invariant differentiation in the two unipotent directions
multiplies a nonzero Fourier mode by positive powers of $H_x$ and $H_y$.  Integrate by parts
$r$ times in each set of unipotent variables, and apply Sobolev embedding on the two compact
cross-sections.  The differentiated Poincare series is locally normally convergent by
Proposition 4.1, while the all-orders projective estimates of Section 3.1 bound the required
Sobolev norms by one continuous Schwartz seminorm of $f$.  Taking $r$ larger than the two
lattice ranks plus the desired decay exponent makes the two nonzero-frequency sums absolutely
convergent and gives, for every $A>0$,

$$
|D_xD_yK_f^\sigma(x,y)|
\leq C_{A,D_x,D_y}
\operatorname{ht}(x)^{-A}\operatorname{ht}(y)^{-A}.
\tag{4.3}
$$

The compact parts of the cusp charts and the finitely many charts change only the constant.
This proves simultaneous, rather than merely separate, decay uniformly in both variables.  For
each prescribed $A,D_x,D_y$, only finitely many derivatives of $f$ occur.

The estimate is stable under bounded variation of $f$ in a sufficiently high admissible
Schwartz seminorm.  This uniformity will give continuity of the trace distribution and allow
finite sums of tensors without new convergence arguments.

### 4.4 The diagonal distribution

The cusp volume density grows at most polynomially in height.  Taking $A$ large in (4.3) gives

$$
\int_{X_E^1}|K_f^\sigma(x,x)|\,dx<\infty.
\tag{4.4}
$$

Thus

$$
J_{\mathrm{diag}}^\sigma(f)
=\int_{X_E^1}K_f^\sigma(x,x)\,dx
\tag{4.5}
$$

is an honest continuous distribution.  The fixed-central-character version is obtained by the
same estimate after central disintegration.

Equation (4.4) does not yet prove that (4.5) is the operator trace.  There are integral
operators with an integrable displayed diagonal that are not trace class, and a measurable
kernel is defined only up to a null set.  The smooth automorphic kernel gives a canonical
diagonal, but trace class still requires a separate Sobolev argument.

## 5. Trace class and the diagonal trace theorem

The twisted operator differs from ordinary convolution by a unitary factor, so one expects the
same smoothing mechanism to work.  The complication is the noncompact quotient: a global
elliptic resolvent need not be compact on the continuous spectrum.  Strong cuspidality has
already removed that spectrum from both the range and the adjoint range, allowing a cuspidal
Sobolev factorization.

### 5.1 Why integrability of the diagonal is not enough

Let $P_{\mathrm{cusp}}$ be the orthogonal projection onto the cuspidal subspace.  Equations
(4.2) and its second-variable analogue imply

$$
T_\sigma(f)
=P_{\mathrm{cusp}}T_\sigma(f)P_{\mathrm{cusp}}.
\tag{5.1}
$$

This identity follows first on smooth automorphic forms by unfolding constant terms.  Density
and boundedness extend it to $L^2$.  It is stronger than the assertion that the trace of the
noncuspidal block is zero: the entire operator vanishes there.

On the cuspidal space, a positive elliptic operator $\Delta$ built from archimedean invariant
differentiation and finite-level compact projectors has discrete spectrum with finite
multiplicities.  For fixed level and compact type its eigenvalue counting function satisfies

$$
N_\Delta(R)=O(R^d)
\tag{5.2}
$$

for some $d$.  This is the cuspidal compactness theorem: truncation gives ordinary elliptic
compactness on a compact core, while rapid decay makes the tail uniformly small.  The estimate
(5.2) follows from the usual local Weyl bound on the compact core.  We recall it here to make
clear that no continuous resolvent is being treated as compact.

### 5.2 A cuspidal Sobolev factorization

Choose an even integer $m>d$, increasing it whenever a prescribed finite number of kernel
derivatives is needed.  From (5.2),

$$
S=(1+\Delta)^{-m/2}P_{\mathrm{cusp}}
\tag{5.3}
$$

is Hilbert--Schmidt, because

$$
\|S\|_2^2
=\sum_j(1+\lambda_j)^{-m}<\infty.
$$

Apply $(1+\Delta)^{m/2}$ in both variables to $K_f^\sigma$.  Estimate (4.3) shows that the
resulting differentiated kernel belongs to $L^2(X\times X)$, hence defines a Hilbert--Schmidt,
in particular bounded, operator $B$.  On smooth cuspidal vectors, integration by parts gives

$$
T_\sigma(f)=SBS.
\tag{5.4}
$$

No boundary term occurs: (4.3) gives arbitrary decay, and the invariant measure has only
polynomial cusp growth.  The identity extends by density.

The product of two Hilbert--Schmidt operators with a bounded operator between them is trace
class.  Therefore

$$
\|T_\sigma(f)\|_1
\leq\|S\|_2^2\|B\|.
\tag{5.5}
$$

**Theorem 5.1 (twisted trace class).** Every finite-level, finite-type admissible test function
with one strongly cuspidal local factor defines a trace-class operator $T_\sigma(f)$ on the
determinant-one or invariant fixed-central-character automorphic Hilbert space.

The proof works with a finite supercuspidal place even when $E$ has no real place.  The
archimedean operator $\Delta$ supplies smoothing and eigenvalue control; the finite factor
supplies cuspidality.

### 5.3 Trace-norm continuity

Only finitely many derivatives of $f$ enter the kernel defining $B$ in (5.4).  The lattice
count of Section 4.1 and rapid-decay estimate (4.3) bound its Hilbert--Schmidt norm by a
Schwartz seminorm $q_M(f)$.  Hence

$$
\|T_\sigma(f)\|_1\leq Cq_M(f).
\tag{5.6}
$$

Thus $f\mapsto T_\sigma(f)$ is continuous into the trace-class ideal on every fixed finite-level,
finite-type block.  In particular,

$$
|\operatorname{tr}T_\sigma(f)|\leq Cq_M(f).
\tag{5.7}
$$

This continuity permits approximation by compactly supported archimedean functions provided
the approximants remain uniformly finite-type and strongly cuspidal.  An arbitrary cutoff is
not allowed: it can create a nonzero constant term and destroy (5.1).

### 5.4 Equality of operator trace and kernel diagonal

An $L^2$ kernel cannot simply be restricted to the diagonal, which has product measure zero.
We therefore identify the canonical smooth kernel with the Hilbert--Schmidt contraction
provided by (5.4).  Take $m$ large enough that $S$ has a smooth rapidly decreasing kernel
$H_m(x,y)$, as supplied by cuspidal Sobolev theory, and write

$$
h_x(y)=\overline{H_m(x,y)},
\qquad
(Su)(x)=\langle u,h_x\rangle.
\tag{5.8}
$$

The map $x\mapsto h_x$ and all of its required derivatives are continuous as $L^2$-valued
maps and rapidly decreasing in the cusp.  Since $B$ is bounded, $U=SB$ and $V=S$ are
Hilbert--Schmidt and $T_\sigma(f)=UV$.  Their contraction kernel is

$$
L_f(x,y)=\langle h_y,B^*h_x\rangle.
\tag{5.9}
$$

Cauchy--Schwarz and the $L^2$-valued derivative bounds make $L_f$ smooth and rapidly decreasing
in both variables.  It represents $SBS=T_\sigma(f)$.  The canonical Poincare kernel
$K_f^\sigma$ represents the same operator by Section 2.3.  Pairing their difference against
compactly supported smooth functions in both variables shows that it is the zero distribution.
Because the difference is continuous and the quotient measure has full support,

$$
L_f(x,y)=K_f^\sigma(x,y)
\quad\text{for every }x,y.
\tag{5.9a}
$$

The Hilbert--Schmidt product theorem now gives an $L^1$ diagonal contraction:

$$
\int_X\left|\int_XK_U(x,y)K_V(y,x)\,dy\right|dx
\leq\|U\|_2\|V\|_2.
\tag{5.9b}
$$

By (5.8)--(5.9a), the inner contraction is $L_f(x,x)=K_f^\sigma(x,x)$.  The same product
theorem identifies its integral with $\operatorname{tr}(UV)$.  Hence

$$
\operatorname{tr}T_\sigma(f)
=\int_XK_f^\sigma(x,x)\,dx,
\tag{5.9c}
$$

and the integral is absolutely convergent.  Only finitely many source and target level-type
blocks occur, so their finite direct sum introduces no additional limit.

**Theorem 5.2 (diagonal trace theorem).** Under the hypotheses of Theorem 5.1,

$$
\boxed{
\operatorname{tr}T_\sigma(f)
=\int_XK_f^\sigma(x,x)\,dx.}
\tag{5.10}
$$

The integral is absolutely convergent and uses the canonical smooth kernel (2.9).  This theorem
is the analytic bridge between the spectral trace and the geometric distribution.

## 6. The automorphism on the cuspidal spectrum

Trace class answers whether a trace exists; it does not compute it.  The field automorphism
permutes cuspidal isotypic summands, so the next task is elementary but delicate block linear
algebra.  Only fixed blocks contribute, and their intertwiners must be normalized without an
arbitrary scalar.

### 6.1 Permutation of isotypic summands

The cuspidal Hilbert space has a discrete decomposition

$$
L^2_{\mathrm{cusp}}(E,\Omega)
=\widehat\bigoplus_{\Pi}
M_\Pi\otimes\mathcal H_\Pi,
\tag{6.1}
$$

where $M_\Pi$ is finite-dimensional.  Equation (2.2) sends the summand indexed by $\Pi$ to the
summand indexed by $\Pi^\sigma$.  Right convolution preserves each isotypic summand.  Hence
$T_\sigma(f)=R(f)U_\sigma$ maps

$$
M_\Pi\otimes\mathcal H_\Pi
\longrightarrow
M_{\Pi^\sigma}\otimes\mathcal H_{\Pi^\sigma}.
\tag{6.2}
$$

If a $\sigma$-orbit of isomorphism classes has length greater than one, the matrix of
$T_\sigma(f)$ on their orthogonal sum has zero diagonal blocks.  Its trace is therefore zero.
This remains true for trace-class operators: compress to a finite orbit, take the ordinary
block trace, and then sum over orbits.

### 6.2 Stable representations and intertwiners

Suppose $\Pi^\sigma\simeq\Pi$.  An intertwiner in the convention convenient for twisted traces
is a unitary operator $A_\Pi$ satisfying

$$
A_\Pi\Pi(g)A_\Pi^{-1}=\Pi(\sigma(g)).
\tag{6.3}
$$

Schur's lemma shows that $A_\Pi^\ell$ is scalar.  Multiplying $A_\Pi$ by an $\ell$th root makes

$$
A_\Pi^\ell=1.
\tag{6.4}
$$

There remain $\ell$ possible scalings by $\ell$th roots of unity.  Thus (6.4) alone does not
canonically define the twisted character
$\operatorname{tr}(\Pi(f)A_\Pi)$.  A trace formula cannot ignore this ambiguity.

### 6.3 The automorphic normalization

Choose an isometric automorphic embedding

$$
j_\Pi:\mathcal H_\Pi\longrightarrow
L^2_{\mathrm{cusp}}(E,\Omega).
$$

When global multiplicity one is used, its image is the entire $\Pi$-isotypic summand.  Define

$$
A_\Pi^{\mathrm{aut}}
=j_\Pi^{-1}U_\sigma j_\Pi.
\tag{6.5}
$$

Equation (2.2) proves (6.3), and $U_\sigma^\ell=1$ proves (6.4).  Replacing $j_\Pi$ by a scalar
does not change (6.5).  Hence the automorphic realization removes the root-of-unity ambiguity.

This normalization is global.  A product of locally normalized intertwiners may differ from
$A_\Pi^{\mathrm{aut}}$ by a scalar; that scalar must be retained or absorbed into one declared
local factor.  The automorphic trace is

$$
\operatorname{tr}_\sigma\Pi(f)
=\operatorname{tr}\bigl(\Pi(f)A_\Pi^{\mathrm{aut}}\bigr).
\tag{6.6}
$$

It is independent of all embeddings and bases.

### 6.4 Multiplicity spaces and the general block trace

It is useful to record the formula without multiplicity one.  Choose any unitary $A_\Pi$
satisfying (6.3).  On a stable isotypic summand, $U_\sigma$ has the form

$$
U_\sigma|_{M_\Pi\otimes\mathcal H_\Pi}
=B_\Pi\otimes A_\Pi,
\tag{6.7}
$$

for an operator $B_\Pi$ on $M_\Pi$.  This follows because
$(1\otimes A_\Pi^{-1})U_\sigma$ commutes with $1\otimes\Pi(g)$, so it lies in
$\operatorname{End}(M_\Pi)\otimes1$.

Right convolution is $1\otimes\Pi(f)$.  Therefore the block trace is

$$
\operatorname{tr}(B_\Pi)
\operatorname{tr}(\Pi(f)A_\Pi).
\tag{6.8}
$$

If $A_\Pi$ is multiplied by $c$, then $B_\Pi$ is multiplied by $c^{-1}$; the product (6.8) is
unchanged.  Under multiplicity one, choosing the automorphic normalization makes
$B_\Pi=1$ and recovers (6.6).  Formula (6.8) is the correct replacement for an unexplained
factor $m(\Pi)$ in a twisted trace.

## 7. Factorization of twisted traces

Automorphic representations and test functions are restricted tensor products, but a twisted
trace does not factor until the intertwiner has also been factored coherently.  Places of $E$
lying over one place of $F$ must be treated together because $\sigma$ permutes them.

### 7.1 Local packets over a place of the base field

For a place $v$ of $F$, write

$$
E_v=E\otimes_FF_v=\prod_{w\mid v}E_w,
\qquad
H_v=\prod_{w\mid v}\mathrm{GL}_2(E_w).
$$

Regroup a cuspidal representation as

$$
\Pi=\bigotimes_v'\Pi_v,
\qquad
\Pi_v=\bigotimes_{w\mid v}\Pi_w.
\tag{7.1}
$$

The automorphism acts on $H_v$ and transports $\Pi_v$.  Global $\sigma$-stability implies
$\Pi_v^\sigma\simeq\Pi_v$ for every $v$: restrict a global intertwiner to the local Hecke
algebra and use uniqueness of the restricted tensor factors.  Conversely, coherent local
isomorphisms whose restricted tensor product exists produce a global isomorphism.

At almost every $v$, the group and representation are unramified and the spherical line is
one-dimensional.  There is a unique local intertwiner fixing the normalized spherical vector.
This provides the tail needed for a restricted tensor product of intertwiners.

### 7.2 Coherent local intertwiners

For every $v$, choose

$$
A_{\Pi_v}:\mathcal H_{\Pi_v}\longrightarrow\mathcal H_{\Pi_v}
$$

satisfying

$$
A_{\Pi_v}\Pi_v(g)A_{\Pi_v}^{-1}=\Pi_v(\sigma(g)).
\tag{7.2}
$$

Normalize it to fix the spherical vector outside a finite set.  Then

$$
A_\Pi^{\mathrm{loc}}=\bigotimes_v'A_{\Pi_v}
\tag{7.3}
$$

is defined and is a global intertwiner.  By Schur's lemma,

$$
A_\Pi^{\mathrm{aut}}=c(\Pi)A_\Pi^{\mathrm{loc}}
\tag{7.4}
$$

for a scalar $c(\Pi)$ of absolute value one.  The cyclic relation makes
$c(\Pi)^\ell$ the inverse of the scalar cyclic product of (7.3).  We may absorb
$c(\Pi)$ into the intertwiner at one place $v_*$; after declaring that place, the local tensor
equals the automorphic normalization exactly.

This is not an artificial defect.  Local intertwiners are defined only up to scalar, whereas
the automorphic action couples all places.  Equation (7.4) is the precise local-global
normalization ledger.

### 7.3 A finite tensor trace lemma

Let $f=\otimes_vf_v$, with spherical projectors outside a finite set $S$ containing every
ramified place and the normalization place $v_*$.  Each $\Pi_v(f_v)A_{\Pi_v}$ has finite rank
for $v\in S$, and outside $S$ it is the identity on the spherical line.  Hence

$$
\Pi(f)A_\Pi^{\mathrm{aut}}
=\bigotimes_v\bigl(\Pi_v(f_v)A_{\Pi_v}\bigr)
$$

has finite-dimensional range canonically identified with a finite tensor product.

**Lemma 7.1 (finite twisted tensor trace).** With coherent intertwiners as above,

$$
\boxed{
\operatorname{tr}_\sigma\Pi(f)
=\prod_{v\in S}
\operatorname{tr}\bigl(\Pi_v(f_v)A_{\Pi_v}\bigr).}
\tag{7.5}
$$

**Proof.** Restrict the operator to the tensor product of its finite-dimensional local ranges
and the spherical lines outside $S$.  The ordinary identity
$\operatorname{tr}(\otimes_iC_i)=\prod_i\operatorname{tr}(C_i)$ applies.  Enlarging $S$
inserts factors equal to one, so the result is independent of $S$. $\square$

Absolute convergence of the global spectral sum will come from global trace class, not from
multiplying estimates for the local factors.

### 7.4 The cyclic trace lemma at a split place

Suppose $v$ splits completely, so $E_v\simeq F_v^\ell$.  After identifying all factor fields
with $F_v$, a $\sigma$-stable irreducible representation has, after cyclic indexing, the form

$$
\Pi_v=\rho_0\otimes\rho_1\otimes\cdots\otimes\rho_{\ell-1},
\qquad
\rho_j\simeq\rho
\quad\text{for every }j,
$$

where the last equality reflects that every factor field is $F_v$ and $\sigma$ permutes
positions.  After fixed identifications, the local intertwiner is the cyclic permutation

$$
A(v_0\otimes\cdots\otimes v_{\ell-1})
=v_{\ell-1}\otimes v_0\otimes\cdots\otimes v_{\ell-2}.
\tag{7.6}
$$

Let $C_j$ be finite-rank operators on the factors.  Then

$$
\operatorname{tr}\bigl((C_0\otimes\cdots\otimes C_{\ell-1})A\bigr)
=\operatorname{tr}(C_0C_{\ell-1}\cdots C_1),
\tag{7.7}
$$

with the order determined by (7.6).

**Proof.** Choose a basis $e_a$ of the common finite-dimensional range.  A diagonal matrix
entry is

$$
\prod_{j=0}^{\ell-1}(C_j)_{a_j,a_{j-1}},
\qquad a_{-1}=a_{\ell-1}.
$$

Summing all indices is exactly the matrix expansion of the trace on the right of (7.7).
$\square$

Thus a twisted trace on a split product becomes an ordinary trace of a cyclic convolution on
one copy of $\mathrm{GL}_2(F_v)$.  This is the spectral counterpart of the geometric fact that
a split local twisted orbit reduces to ordinary conjugacy of the product of its components.

## 8. The cuspidal twisted spectral expansion

All analytic and representation-theoretic ingredients are now in place.  Trace class makes the
global sum unconditional; the action of $\sigma$ deletes nonstable orbits; and coherent local
intertwiners expose each surviving weight as a finite product.

### 8.1 Blockwise computation

Let $P_\Pi$ be the orthogonal projection onto the $\Pi$-isotypic summand.  From (6.2),

$$
P_\Pi T_\sigma(f)P_\Pi=0
$$

unless $\Pi^\sigma\simeq\Pi$.  For a stable $\Pi$, equation (6.8) gives

$$
\operatorname{tr}\bigl(P_\Pi T_\sigma(f)P_\Pi\bigr)
=\operatorname{tr}(B_\Pi)
 \operatorname{tr}(\Pi(f)A_\Pi).
\tag{8.1}
$$

With multiplicity one and the automorphic normalization, this is simply
$\operatorname{tr}_\sigma\Pi(f)$.

It is important that a nonstable orbit contributes zero rather than being omitted by
definition.  On the orthogonal sum of an orbit of length $r>1$, the operator has a cyclic
off-diagonal block matrix.  Its ordinary finite-orbit trace is zero.  This remains true after
summing infinitely many orbits because the total operator is trace class.

### 8.2 Absolute convergence

For a finite family of mutually orthogonal projections $P_i$, the block-diagonal pinching

$$
\mathcal E(T)=\sum_iP_iTP_i
$$

is contractive in trace norm.  One proof averages $T$ over the finite group of unitaries that
independently change signs on the ranges of the $P_i$; convexity of the trace norm gives
$\|\mathcal E(T)\|_1\leq\|T\|_1$.  Passing through an increasing sequence of finite families
and using lower semicontinuity gives

$$
\sum_\Pi\|P_\Pi T_\sigma(f)P_\Pi\|_1
\leq\|T_\sigma(f)\|_1.
\tag{8.2}
$$

Therefore

$$
\sum_{\Pi^\sigma\simeq\Pi}
\left|
\operatorname{tr}(B_\Pi)
\operatorname{tr}(\Pi(f)A_\Pi)
\right|<\infty.
\tag{8.3}
$$

No ordering of the cuspidal representations is involved.  The sum may be regrouped by local
type, Hecke eigenvalue, descent datum, or any other countable label.

### 8.3 The factored cuspidal formula

Combining Theorem 5.2, the block computation, and Lemma 7.1 proves the main spectral result.

**Theorem 8.1 (cuspidal twisted spectral expansion).** Let $E/F$ be cyclic, let $\Omega$ be a
$\sigma$-invariant unitary central character, and let $f$ be finite-level, finite-type,
spherical almost everywhere, with one strongly cuspidal local factor.  Then

$$
\boxed{
\operatorname{tr}\bigl(R_\Omega(f)U_\sigma
\mathbin{|}L^2_{\mathrm{cusp}}(E,\Omega)\bigr)
=\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E,\Omega)\\
                  \Pi^\sigma\simeq\Pi}}
\operatorname{tr}_\sigma\Pi(f).}
\tag{8.4}
$$

The series converges absolutely.  For a tensor $f=\otimes_vf_v$ and coherent local
intertwiners,

$$
\operatorname{tr}_\sigma\Pi(f)
=\prod_{v\in S}
\operatorname{tr}\bigl(\Pi_v(f_v)A_{\Pi_v}\bigr),
\tag{8.5}
$$

where $S$ is any sufficiently large finite set.  Without multiplicity one, replace each term
by (8.1).

**Proof.** Theorem 5.1 gives trace class.  Decompose the cuspidal Hilbert space into
$\sigma$-orbits of isotypic summands.  Nonfixed orbits have zero block trace, while (8.1)
computes a fixed block.  Inequality (8.3) permits summation.  The finite tensor trace lemma
gives (8.5). $\square$

### 8.4 Dependence on normalization

If a local intertwiner is replaced by $c_vA_{\Pi_v}$, its local twisted trace is multiplied by
$c_v$.  The product (8.5) represents the automorphic trace only when

$$
\prod_{v\in S}c_v=1
\tag{8.6}
$$

after the unchanged spherical tail is included.  Equivalently, all local choices together must
equal $A_\Pi^{\mathrm{aut}}$.  This is the spectral analogue of complementary choices of
centralizer and quotient measures on the geometric side.

Changing Haar measure at a local place rescales formal degrees and normalized matrix
coefficients inversely, leaving the integrated operator unchanged.  Changing an intertwiner
scalar is different: it changes the operator itself.  Haar covariance cannot correct an
intertwiner-normalization error.

## 9. The continuous channel and its annihilation

The cuspidal formula is not yet the full spectral formula until the orthogonal complement has
been addressed.  Over $E$, rank-one constant-term theory classifies that complement by
Eisenstein wave packets and their residues.  Strong cuspidality kills the inducing operator
before the field automorphism or scattering matrix can create a trace.

### 9.1 Eisenstein data over the extension field

Choose unitary Hecke characters $\chi_1,\chi_2$ of $E$ with
$\chi_1\chi_2=\Omega$.  Normalized induction is

$$
I_E(\chi,s)=
\operatorname{Ind}_{B_E(\mathbf A_E)}^{G_E(\mathbf A_E)}
(\chi_1\otimes\chi_2)|\alpha|^s,
\tag{9.1}
$$

where a section transforms by

$$
\chi_1(a)\chi_2(d)|a/d|_{\mathbf A_E}^{s+1/2}.
$$

The unitary axis is $s=it$.  The Eisenstein series

$$
E(g,h_s)=\sum_{\gamma\in B_E(E)\backslash G_E(E)}h_s(\gamma g)
\tag{9.2}
$$

converges initially for $\operatorname{Re}(s)>1/2$ and continues meromorphically.  Genuine
$L^2$ vectors in the continuous channel are rapidly decreasing wave packets in $t$, together
with a discrete sum over compact idele-class characters.

### 9.2 How the field automorphism acts on inducing data

Transport by $U_\sigma$ carries (9.1) to

$$
I_E(\chi^\sigma,s),
\qquad
\chi_i^\sigma(a)=\chi_i(\sigma^{-1}a).
\tag{9.3}
$$

Indeed, substituting $\sigma^{-1}g$ in the transformation law transports both diagonal
characters and preserves the normalized absolute value.  On Eisenstein series,

$$
U_\sigma E(g,h_s)
=E(g,U_\sigma h_s),
\tag{9.4}
$$

first in the convergence chamber and then by continuation.  The global standard intertwining
operator is natural for this action:

$$
U_\sigma M(\chi,s)U_\sigma^{-1}
=M(\chi^\sigma,s).
\tag{9.5}
$$

This follows directly by applying $\sigma$ to the adelic unipotent integral; the self-dual
product measure is invariant.

### 9.3 Vanishing before regularization

There are two legitimate routes, depending on the selected local factor.  If the strongly
cuspidal factor is nonarchimedean and compactly supported modulo the center, convolution passes
through (9.2) in the convergence chamber:

$$
R(f)E(g,h_s)
=E(g,I_E(\chi,s)(f)h_s).
\tag{9.6}
$$

Section 3.3 makes the induced operator a zero meromorphic family in this case.  Hence

$$
R(f)E(g,h_s)=0.
\tag{9.7}
$$

Taking meromorphic continuation proves (9.7) throughout the required strip.

For a general allowed archimedean strongly cuspidal Schwartz factor, no off-unitary argument is
needed or valid.  Let

$$
W_a(g)=\sum_\chi\int_{\mathbf R}a_\chi(t)E(g,h_{\chi,it})\,dt
$$

be a smooth wave packet with finitely many character and compact-type data and rapidly
decreasing amplitudes.  First truncate the $t$-integral and the finite character sum.  The
Schwartz estimates for $f$, rapid decrease of $a_\chi$, and the polynomial vertical bounds for
finite-type Eisenstein series justify Fubini.  Convolution acts fiberwise by
$I_E(\chi,it)(f)$, which is the zero operator by (3.5).  Removing the truncations by the same
majorant gives $R(f)W_a=0$.  Such packets are dense in the continuous subspace, and boundedness
of $R(f)$ extends the zero to its closure.

In either case, composing with $U_\sigma$ only transports the inducing data and does not change
the conclusion:

$$
T_\sigma(f)W_a=0.
\tag{9.8}
$$

When the compact-support continuation argument applies, (9.8) also holds with $W_a$ replaced
by the meromorphic Eisenstein family in (9.7).

### 9.4 Scattering terms and derivatives

A regularized twisted spectral formula could contain finite-dimensional expressions of the
shape

$$
\int_{\mathbf R}
\operatorname{tr}\left(
Q_\sigma(\chi,it)
I_E(\chi,it)(f)
\right)dt,
\tag{9.9}
$$

where $Q_\sigma$ is built from field-automorphism intertwiners, normalized scattering
operators, and logarithmic derivatives.  Equation (3.5) makes the final factor in (9.9) the
zero operator.  Hence the integrand is identically zero, independently of how the scattering
operator is normalized.

Even expressions in which a tangential parameter derivative appears on the test operator
vanish.  The honest family $t\mapsto I_E(\chi,it)(f)$ is identically zero and differentiable on
the unitary axis, so all of its $t$-derivatives are zero.  If the selected factor is
nonarchimedean and compactly supported modulo the center, the stronger meromorphic statement
from Section 3.3 also makes every off-axis Laurent coefficient zero.  We do not infer that
stronger statement for a general archimedean Schwartz factor.  Operator zero, rather than trace
zero, is what annihilates the product with $Q_\sigma$ in all cases.

## 10. Residues and the exhaustion of the noncuspidal spectrum

Moving an Eisenstein contour to the unitary axis can cross poles.  Killing the continuous
integral without checking these Laurent coefficients would leave a discrete but noncuspidal
gap.  Rank-one residue theory makes the gap explicit and then removes it.

### 10.1 The residual determinant characters

The only square-integrable residues over $E$ are one-dimensional functions

$$
r_\eta(g)=\eta(\det g),
\qquad
\eta^2=\Omega,
\tag{10.1}
$$

with $\eta$ unitary.  They arise from the simple pole characterized by

$$
\chi_1\chi_2^{-1}|\cdot|^{2s_0}=|\cdot|.
$$

They lie in $L^2$ because the central quotient has finite volume, but their unipotent constant
term is themselves, so they are not cuspidal.

The field automorphism sends $r_\eta$ to $r_{\eta^\sigma}$.  A nonstable orbit of residual
characters would have zero twisted block trace, but we shall prove the stronger assertion that
$R(f)$ annihilates every residual line, stable or not.

### 10.2 Two proofs of residual vanishing

If the strongly cuspidal factor is nonarchimedean and compactly supported modulo the center, we
may first take the residue of the meromorphic identity (9.7).  Bounded convolution commutes
with a finite Laurent coefficient, so

$$
R(f)\operatorname*{Res}_{s=s_0}E(g,h_s)=0.
\tag{10.2}
$$

Every line (10.1) occurs as a nonzero residue for a suitable section, proving the assertion in
that case.  This proof is not used for a general archimedean Schwartz factor.

The direct local proof works in every case and is the required argument at an archimedean
selected place.  On the residual line, local convolution is a scalar.  In compact-picture
order that scalar is

$$
\lambda_{w_0}
=\int_{Z(k)\backslash T(k)}\xi_{\eta,w_0}(t)f_{w_0}^B(t)\,dt,
\tag{10.2a}
$$

where $\xi_{\eta,w_0}$ is the normalized torus character whose one-dimensional quotient is
$\eta_{w_0}\circ\det$, and $f_{w_0}^B$ is the corresponding $K$-averaged parabolic transform.
It is assembled from the functions

$$
\delta_B(t)^{1/2}\int_{N(k)}
f_{w_0}(k_1^{-1}tnk_2)\,dn
$$

with the compact-picture character weights in $k_1$ and $k_2$.  Formula (10.2a) is obtained by
performing these $K$- and $N$-averages first and
only then taking the outer torus Mellin integral.  This ordering is essential at an
archimedean Schwartz place, where the undissected group integral need not be absolutely
convergent; it is precisely the Schwartz-algebra action.  Strong cuspidality makes
$f_{w_0}^B$ identically zero before the outer integral is taken.  Tensor factorization then
gives one zero local scalar, so $R(f)$, and therefore $T_\sigma(f)$, annihilates every residual
line.

### 10.3 No hidden fourth channel

The earlier global constant-term theory proves, at fixed level and compact type,

$$
L^2_{\mathrm{cusp}}(E,\Omega)^\perp
=\overline{\{
\text{unitary Eisenstein wave packets and the lines }\eta\circ\det
\}}.
\tag{10.3}
$$

The proof uses pseudo-Eisenstein generators, Mellin inversion in the single height variable,
and contour motion.  There is no complementary-series interval left as a separate automorphic
summand: nonunitary parameters occur during contour motion, but only their poles leave an
$L^2$ term.  Thus Sections 9.3 and 10.2 exhaust the noncuspidal space.

### 10.4 The full noncuspidal annihilation theorem

**Theorem 10.1.** Under the hypotheses of Theorem 8.1,

$$
T_\sigma(f)|_{L^2_{\mathrm{cusp}}(E,\Omega)^\perp}=0.
\tag{10.4}
$$

Consequently the continuous and residual twisted trace distributions both vanish.

**Proof.** The automorphism $\sigma$ preserves $B_E$, $N_E$, and their quotient measures, so
$U_\sigma$ preserves the continuous, residual, and cuspidal subspaces.  Equation (9.8) gives
zero on every Eisenstein packet, and (10.2) gives zero on every residual line.  Their span is
dense in (10.3).  Since $T_\sigma(f)$ is bounded, it vanishes on the closure. $\square$

Combining Theorems 5.1 and 10.1, the trace on the full automorphic Hilbert space equals the
cuspidal trace (8.4).  The noncuspidal terms are absent because the operator is zero there, not
because a formal expansion has discarded them.

## 11. The twisted simple trace formula

The diagonal trace theorem and the cuspidal spectral expansion meet the convergent geometric
distribution constructed from twisted conjugacy.  No new rearrangement of rational or spectral
sums is needed: both sides have already been proved absolutely convergent.

### 11.1 The geometric distribution recalled

Return first to the determinant-one realization and assume $E/F$ has prime degree $\ell$.  For
a twisted semisimple rational element $\delta$, let $I_\delta$ be its twisted centralizer,

$$
I_\delta(R)=
\{x\in\mathrm{GL}_2(E\otimes_FR):
x^{-1}\delta\sigma(x)=\delta\},
$$

and set

$$
a(\delta)=
\operatorname{vol}\bigl(I_\delta(F)\backslash I_\delta(\mathbf A_F)^1\bigr).
\tag{11.1}
$$

With complementary quotient measure, define

$$
O_\delta^\sigma(f)=
\int_{I_\delta(\mathbf A_F)\backslash H(\mathbf A_F)}
f(h^{-1}\delta\sigma(h))\,d\dot h.
\tag{11.2}
$$

For strongly regular classes this factors into local orbital integrals.  The global coefficient
does not generally factor.

The convergent geometric theorem gives

$$
J_{\mathrm{geom}}^\sigma(f)
=J_{\mathrm{sc,sp}}^\sigma(f)
+J_{\mathrm{reg,ell}}^\sigma(f)
+\mathbf1_{\ell=2}J_{\mathrm{sc,div}}^\sigma(f).
\tag{11.3}
$$

The middle term is indexed by regular elliptic $\gamma\in\mathrm{GL}_2(F)$ satisfying the
exact torus norm condition

$$
\gamma\in N_{E/F}^{T_\gamma}(T_\gamma(E));
\tag{11.4}
$$

its fiber contains one rational twisted class $\delta_\gamma$.  The first term contains split
scalar-norm classes.  In quadratic degree the last term contains scalar norms whose descent
algebra $(E/F,a)$ is quaternion division.  Split regular and noncentral repeated-norm classes
cancel in the combined parabolic distribution.

### 11.2 Equality of spectral and geometric traces

The distribution used to define the left side of (11.3) is precisely the diagonal integral

$$
\int_{X_E^1}K_f^\sigma(x,x)\,dx.
$$

Theorem 5.2 identifies it with the operator trace, and Theorems 8.1 and 10.1 identify that trace
with the cuspidal spectral sum.  We obtain the central theorem of the book.

**Theorem 11.1 (twisted simple trace formula, determinant-one form).** Let $E/F$ be cyclic of
prime degree, fix a generator $\sigma$, and let $f$ be an admissible finite-level, finite-type
test function with one strongly cuspidal local factor.  Then

$$
\boxed{
\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E)\\
                  \Pi^\sigma\simeq\Pi}}
\operatorname{tr}_\sigma\Pi(f)
=J_{\mathrm{sc,sp}}^\sigma(f)
+J_{\mathrm{reg,ell}}^\sigma(f)
+\mathbf1_{\ell=2}J_{\mathrm{sc,div}}^\sigma(f).}
\tag{11.5}
$$

The spectral series and every geometric series converge absolutely and continuously in the
admissible Schwartz topology.  The continuous and residual spectral distributions are zero.

**Proof.** The diagonal trace theorem gives the equality of the operator trace and diagonal
kernel distribution.  The convergent twisted geometric theorem expands that diagonal as the
right side.  The cuspidal spectral theorem and noncuspidal annihilation theorem expand the same
operator trace as the left side. $\square$

### 11.3 The fixed-central-character formula

Let $\Omega$ be $\sigma$-invariant and unitary, and impose (1.3).  Fourier projection along the
compact norm-one idele-class center converts Theorem 11.1 into a projective formula.  Write
$[\delta]_{\sigma,Z}$ for a projective twisted class and $\overline I_\delta$ for its projective
stabilizer.  The corresponding term is

$$
a_\Omega(\delta)O_{\delta,\Omega}^\sigma(f),
\tag{11.6}
$$

where quotient integration includes any finite enlargement of
$I_\delta/F^\times$ inside the projective stabilizer, and the central Fourier coefficient
supplies the $\Omega$-weight.  This definition avoids choosing a scalar representative and then
forgetting its stabilizer index.

**Theorem 11.2 (twisted simple trace formula with central character).** Under the hypotheses
above,

$$
\boxed{
\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E,\Omega)\\
                  \Pi^\sigma\simeq\Pi}}
\operatorname{tr}_\sigma\Pi(f)
=J_{\mathrm{geom},\Omega}^\sigma(f),}
\tag{11.7}
$$

where the geometric side is the absolutely convergent projective version of the three channels
in (11.3).  All noncuspidal terms vanish.

The split scalar classes combine into one projective scalar channel.  In quadratic degree the
division scalar classes are indexed projectively by
$F^\times/N_{E/F}(E^\times)$ with the central weight included.  Regular elliptic terms are
indexed by projective twisted classes

$$
\{[\delta]_\sigma:\delta\text{ regular elliptic}\}/E^\times.
\tag{11.7a}
$$

Equivalently, one may use norm pairs modulo the scalar relation actually induced by a lift.
Indeed, replacing $\delta$ by $z\delta$ changes its actual norm $\gamma$ to
$N_{E/F}(z)\gamma$.  Central projection therefore identifies lift norms only through
$N_{E/F}(E^\times)$, not through every scalar in $F^\times$.  Two lifts can have the same
image in $\mathrm{PGL}_2(F)$ while remaining distinct projective twisted classes.  Thus the
regular channel must not be indexed merely by ordinary projective norm classes unless a
separate scalar-fiber theorem has removed this obstruction.

**Proof.** Work first on the determinant-one quotient.  Its norm-one idele-class center is
compact, and $\sigma$ acts on it.  Choose a compactly supported scalar-module lift of the
central-covariant test and take its $\Omega$-Fourier coefficient along this compact center.
The corresponding orthogonal projector commutes with $U_\sigma$ because
$\Omega\circ\sigma=\Omega$, and central Fourier inversion identifies the projected convolution
operator with $R_\Omega(f)$.  Apply the same Fourier coefficient to the trace-class identity
(11.5).  Trace-norm continuity permits projection of the spectral series term by term, leaving
exactly the representations of central character $\Omega$.  Changing the auxiliary
scalar-module lift changes a function with zero $\Omega$-coefficient and hence does not change
the projected identity.

On the geometric side, absolute convergence permits the same Fourier projection term by term.
Integrating the scalar orbit of a representative identifies representatives differing by
$E^\times$ and inserts the character weight.  Quotient integration identifies the resulting
stabilizer with the full projective stabilizer; if it is a finite enlargement of
$I_\delta/F^\times$, its finite index appears automatically in both the volume and quotient
measure.  The three determinant-one channels consequently become the three projective channels
described above.  This proves (11.7). $\square$

### 11.4 Measures and change of generator

Rescale the Haar measure on $I_\delta(F_v)$ by $c_v$.  Then $a(\delta)$ is multiplied by
$\prod_vc_v$, while $O_\delta^\sigma(f)$ is multiplied by its inverse.  Thus every geometric
term is unchanged.  On the spectral side, a consistent rescaling of convolution measure and
formal-degree-normalized selectors also leaves integrated operators unchanged.  These are the
measure covariances required in a comparison.

If $\tau=\sigma^r$ is another generator, $1\leq r<\ell$, then the twisting operator becomes
$U_\tau=U_\sigma^r$, not $U_\sigma$.  If

$$
\delta^{(r)}=\delta\sigma(\delta)\cdots\sigma^{r-1}(\delta),
$$

then

$$
N_\tau(\delta^{(r)})=N_\sigma(\delta)^r.
\tag{11.8}
$$

Thus changing generators changes both spectral intertwiners and geometric norms.  Theorems
11.1 and 11.2 remain valid after every occurrence of $\sigma$ is changed coherently; they do
not assert equality of the traces for two different generators.

## 12. Twisted pseudo-coefficients and exact selection

The abstract spectral formula becomes useful when local test functions impose exact conditions
on $\Pi_v$.  An ordinary pseudo-coefficient selects an isomorphism class, but its twisted trace
also sees the chosen intertwiner.  A one-dimensional adjustment gives a selector of twisted
trace one.

### 12.1 Why an ordinary selector needs adjustment

Let $L/k$ be a cyclic extension of nonarchimedean local fields occurring at a nonsplit place
$v$ of $F$, and let
$D$ be an irreducible unitary representation of $\mathrm{GL}_2(L)$ square-integrable modulo
the center.  Assume $D^\sigma\simeq D$ and choose a unitary intertwiner

$$
A D(g)A^{-1}=D(\sigma(g))\qquad(g\in\mathrm{GL}_2(L)),
\qquad A^d=1,
\tag{12.1}
$$

where $d$ is the order of the local decomposition group.

For a compact-finite unit vector $u$, the formal-degree-normalized coefficient

$$
f_{D,u}(g)=d(D)\overline{\langle D(g)u,u\rangle}
\tag{12.2}
$$

satisfies

$$
D(f_{D,u})=P_u,
\tag{12.3}
$$

the rank-one orthogonal projection onto $\mathbf Cu$.  Its twisted trace is

$$
\operatorname{tr}(P_uA)=\langle Au,u\rangle,
\tag{12.4}
$$

which need not equal one and can even vanish if $u$ is not an eigenvector.  Thus ordinary trace
normalization is not automatically twisted trace normalization.

For completeness, (12.3) follows directly from Schur orthogonality.  With the Hilbert inner
product linear in the first variable, formal degree is characterized by

$$
\int_{Z(L)\backslash\mathrm{GL}_2(L)}
\langle D(g)v,w\rangle
\overline{\langle D(g)u,u\rangle}\,d\bar g
=d(D)^{-1}\langle v,u\rangle\overline{\langle w,u\rangle}.
\tag{12.4a}
$$

Multiplication by $d(D)$ shows that

$$
\langle D(f_{D,u})v,w\rangle
=\langle v,u\rangle\overline{\langle w,u\rangle},
$$

which is exactly the matrix coefficient of $P_u$.  This calculation also shows why changing
the quotient Haar measure rescales the formal degree and the selector inversely.

### 12.2 Construction at an invariant field place

Since $A$ has finite order, its eigenspaces span $D$.  The smooth compact-finite vectors are
stable under $A$, so some eigenspace contains a unit vector $u$ of this kind.  Write
$Au=\zeta u$, with $\zeta^d=1$, and define

$$
f_{D,A,u}^{\mathrm{tw}}=\zeta^{-1}f_{D,u}.
\tag{12.5}
$$

Then

$$
\operatorname{tr}\bigl(D(f_{D,A,u}^{\mathrm{tw}})A\bigr)=1.
\tag{12.6}
$$

**Proposition 12.1 (twisted pseudo-coefficient).** For every $\sigma$-stable irreducible unitary
$\rho$ with the same central character and a declared compatible $\sigma$-intertwiner,

$$
\operatorname{tr}\bigl(\rho(f_{D,A,u}^{\mathrm{tw}})A_\rho\bigr)
=\begin{cases}
1,&\rho\simeq D\text{ with the declared normalization},\\
0,&\rho\not\simeq D.
\end{cases}
\tag{12.7}
$$

Moreover the test is strongly cuspidal.

**Proof.** Equation (12.6) gives the first value.  If $\rho$ is inequivalent and
square-integrable, mixed Schur orthogonality makes $\rho(f_{D,u})$ the zero operator.  If
$\rho$ is nonsquare-integrable, it is a subquotient of normalized induction and strong
cuspidality makes the induced operator zero.  Scalar multiplication by $\zeta^{-1}$ preserves
these conclusions and strong cuspidality. $\square$

The selector depends on the intertwiner normalization, as every twisted character must.  Once
the local intertwiner is part of a coherent tensor equal to the automorphic intertwiner, the
global contribution is unambiguous.

### 12.3 Selection on a cyclic orbit of places

At a completely split place, $\sigma$ cyclically permutes $\ell$ copies of
$\mathrm{GL}_2(F_v)$.  Choose a square-integrable $\rho$ and normalized coefficients $f_j$
on all components, each acting as the same rank-one projection $P_u$.  For

$$
f_v=f_0\otimes\cdots\otimes f_{\ell-1},
$$

the cyclic trace lemma gives

$$
\operatorname{tr}\bigl(\Pi_v(f_v)A_{\Pi_v}\bigr)
=\operatorname{tr}(P_u^\ell)=1
\tag{12.8}
$$

when every component is the cyclically compatible copy of $\rho$, and zero if one component is
not selected.  Thus exact selection works on an orbit of places even though no individual
component is fixed by $\sigma$.

One selected coefficient is already enough for strong cuspidality of the product function, but
coefficients on every component are needed for the symmetric exact selection rule (12.8).  The
two roles should not be confused.

### 12.4 Level and Hecke factors

Let $J_v\subset H_v$ be a $\sigma$-stable compact open subgroup and let $e_{J_v}$ be its
probability idempotent.  If the local intertwiner preserves $\Pi_v^{J_v}$, then

$$
\operatorname{tr}\bigl(\Pi_v(e_{J_v})A_{\Pi_v}\bigr)
=\operatorname{tr}\bigl(A_{\Pi_v}|\Pi_v^{J_v}\bigr).
\tag{12.9}
$$

Unlike the untwisted trace, this is not generally $\dim\Pi_v^{J_v}$; it is the character of the
cyclic action on the fixed-vector space.

At an unramified nonsplit place, a $\sigma$-invariant spherical representation has a
one-dimensional spherical line.  Normalize $A_{\Pi_v}$ to fix it.  Then the spherical
idempotent contributes one.  A spherical Hecke function $h_v$ contributes its normalized
Satake polynomial evaluated on the Satake parameters, because $A_{\Pi_v}$ is the identity on
that line.  These factors make the base-change power map visible in Chapter 13.

## 13. Application to cyclic base change

The twisted formula is the spectral instrument required by cyclic base change.  This chapter
shows exactly what it detects and how a trace comparison uses it.  It does not assume that an
arbitrary tensor of local base changes is automorphic, and it does not assume a local orbital
matching theorem that has not yet been proved.

### 13.1 Local base change and invariance

At a nonarchimedean place $v$ of $F$, local cyclic base change in the established selected
range is characterized on Weil--Deligne parameters by

$$
\operatorname{rec}_{E_w}(\operatorname{BC}_{E_w/F_v}\pi_v)
=\operatorname{rec}_{F_v}(\pi_v)|_{W_{E_w}}.
\tag{13.1}
$$

Here the selected range consists of principal series, determinant characters, special
representations, and the constructed tame-dihedral supercuspidals, with every restricted
parameter required to remain in those families.  Primitive wild supercuspidals and the stated
ramified dyadic boundary are not silently included.

Restriction is invariant under conjugation by the local Galois group.  Hence

$$
(\operatorname{BC}\pi_v)^\sigma\simeq\operatorname{BC}\pi_v.
\tag{13.2}
$$

Conversely, a selected irreducible representation over $E_w$ is in the selected local image
precisely when its parameter admits a selected extension to $W_{F_v}$.  Galois invariance is
necessary and is sufficient for extension as an unrestricted admissible parameter; at the
declared wild boundary, the extension may lie outside the selected local correspondence.

Thus the stability condition appearing naturally in (11.7) is exactly the first local descent
test.  It is stronger than invariance of the central character or equality of one Hecke
eigenvalue.

### 13.2 Descent ambiguity and cyclic normalization

Let

$$
X_{E_w/F_v}
=\operatorname{Hom}
(F_v^\times/N_{E_w/F_v}(E_w^\times),\mathbf C^\times).
\tag{13.3}
$$

Characters in this group become trivial after local base change.  If the restricted parameter
has scalar endomorphisms, all descents form a torsor under $X_{E_w/F_v}$.  For reducible
parameters, different cyclic actions on a multiplicity space can create more than one twisting
orbit; extension data, not a slogan of uniqueness up to twist, give the exact fiber.

The same cyclic action supplies an intertwiner $A_v$ on the base-changed representation.  Its
$d$th power is scalar and can be normalized to one, but a root-of-unity ambiguity remains.
When a global automorphic representation $\Pi$ occurs, the product of the local intertwiners is
normalized by $A_\Pi^{\mathrm{aut}}$.  Twisted pseudo-coefficients must use this coherent
normalization.  Different local descents may have the same underlying $\Pi_v$ but different
extension data; twisted traces are designed to see that cyclic data.

For a unitary Hecke character $\omega$ of $F$, the expected central character over $E$ is

$$
\Omega=\omega\circ N_{E/F}.
\tag{13.4}
$$

It is $\sigma$-invariant, so (11.7) applies.

### 13.3 The unramified power map in the spectral sum

Suppose $E_w/F_v$ is unramified of residue degree $f_v$ and $\pi_v$ is spherical with normalized
Satake parameters $\{\alpha_v,\beta_v\}$.  Local base change has parameters

$$
\{\alpha_v^{f_v},\beta_v^{f_v}\}.
\tag{13.5}
$$

Therefore a normalized spherical Hecke function with Satake polynomial $P(X,Y)$ contributes on
the twisted side

$$
P(\alpha_v^{f_v},\beta_v^{f_v}).
\tag{13.6}
$$

For the power sums

$$
p_n=\alpha_v^n+\beta_v^n,
$$

the recurrence

$$
p_0=2,
\qquad
p_1=\alpha_v+\beta_v,
\qquad
p_n=(\alpha_v+\beta_v)p_{n-1}-\alpha_v\beta_v p_{n-2}
\tag{13.7}
$$

expresses the base-change eigenvalue as a polynomial in the ordinary trace and determinant.
Thus compatible spherical tests can be constructed spectrally without choosing an order of
the two Satake parameters.

At a completely split place $f_v=1$, and Section 7.4 reduces the twisted local trace to the
ordinary trace of the cyclic product of the component tests.  The split and inert calculations
are therefore two manifestations of the same norm direction.

### 13.4 The trace-comparison mechanism

Assume $F$ has a real place, and let $\varphi=\otimes_v\varphi_v$ lie in the exact ordinary
simple-trace-formula class: it satisfies the all-orders projective Schwartz estimates, is finite
under both compact actions, and has a strongly cuspidal factor at a real place.  Let
$f=\otimes_vf_v$ be a twisted admissible test on $\mathrm{GL}_2(\mathbf A_E)$.  Suppose the
following local matching statement holds at every place, with the same centralizer and
discriminant measures.  Here $SO$ denotes the stable sum of local orbital integrals over the
rational classes in the indicated stable fiber, with the declared projective stabilizer
multiplicities:

$$
SO_{\gamma_v}(\varphi_v)
=SO_{\gamma_v}^\sigma(f_v)
\tag{13.8}
$$

for every regular norm class.  This local identity is only the first part of the comparison
contract.  We also require the global projective fiber and coefficient identity

$$
\kappa(\gamma)a_F(\gamma)\prod_vO_{\gamma_v}(\varphi_v)
=\sum_{[\delta]_{\sigma,Z}\mapsto[\gamma]}
a_\Omega(\delta)\prod_vO_{\delta_v}^\sigma(f_v),
\tag{13.8a}
$$

where $\kappa(\gamma)$ is the ordinary projective stabilizer factor and the sum retains every
projective twisted class in the scalar fiber described in (11.7a).  If $[\gamma]$ is not in the
twisted norm image, the right side is empty and (13.8a) requires the ordinary orbital product
to vanish.  Finally, the ordinary central term must equal the aggregate of the twisted split
scalar channel and, in quadratic degree, the division scalar channels, with their character
weights and projective stabilizer indices.  Assume the functions are units and the measures are
the compatible unramified ones almost everywhere.  In applications, (13.8a) is deduced from
(13.8) together with a separate global norm-fiber and centralizer-volume calculation; it does
not follow from local orbital matching by itself.

**Theorem 13.1 (trace-comparison principle).** Under (13.8), (13.8a), and the stated scalar
channel identity, the ordinary simple trace formula over $F$ and the twisted simple trace
formula over $E$ have equal geometric sides.  Hence their cuspidal spectral sides are equal:

$$
\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(F,\omega)}
m(\pi)\operatorname{tr}\pi(\varphi)
=
\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E,\Omega)\\
                  \Pi^\sigma\simeq\Pi}}
\operatorname{tr}_\sigma\Pi(f),
\tag{13.9}
$$

with the local selection conditions imposed by the chosen pseudo-coefficients.  Both sums are
absolutely convergent.

**Proof.** Equation (13.8) supplies the local analytic matching on every stable norm fiber.
Identity (13.8a) is the separate globalization statement that assembles those local identities
into a complete rational projective term: it includes the ordinary factor $\kappa(\gamma)$,
every projective twisted class above the norm, and the global centralizer volumes, which do not
themselves factor into local volumes.  It also sets the ordinary non-norm terms equal to the
empty twisted fiber.  The scalar identity matches
the remaining ordinary central term with the full twisted scalar aggregate, including the
quadratic division terms.  Complementary centralizer measures make each volume-orbit product
invariant under rescaling.  Absolute convergence permits summation of these classwise
identities.  The ordinary and twisted simple trace formulas then turn equality of geometric
sides into (13.9). $\square$

The hypothesis (13.8) is substantial.  The present theorem proves the global implication once
local matching is known; it does not prove the local fundamental lemma by comparing spectral
formulas backward.

### 13.5 What the application proves at this stage

Even before (13.8) is supplied, the twisted formula establishes four facts needed for cyclic
base change.

First, only $\sigma$-stable cuspidal representations of $\mathrm{GL}_2(\mathbf A_E)$ occur on
the twisted spectral side.  Second, in the selected local range their components satisfy the
exact parameter-extension criterion for local descent.  Third, twisted pseudo-coefficients and
spherical Hecke functions isolate those components with the correct cyclic and Satake weights.
Fourth, every continuous and residual term is rigorously zero, so a future comparison has no
unmatched spectral remainder.

What is not yet proved is that every prescribed global tensor
$\otimes_v\operatorname{BC}(\pi_v)$ occurs automorphically, or that every globally stable
$\Pi$ has an automorphic descent.  Those global existence and exhaustion assertions follow
from a trace comparison only after local matching, the global coefficient and projective-fiber
identity (13.8a), separation by sufficiently many test functions, and the descent-fiber
analysis have all been supplied.  The twisted simple trace formula is the complete spectral
half of that argument.

## 14. Examples and boundary phenomena

Examples reveal which parts of the formula are normalization and which encode real arithmetic.
They also expose shortcuts that would make a twisted comparison false.

### 14.1 A split place

Let $v$ split completely and take $\ell=3$.  Then

$$
H_v\simeq G_v\times G_v\times G_v,
\qquad
\sigma(g_0,g_1,g_2)=(g_2,g_0,g_1).
$$

For $\Pi_v=\rho^{\otimes3}$ and $f_v=f_0\otimes f_1\otimes f_2$, the twisted trace is

$$
\operatorname{tr}
\bigl((\rho(f_0)\otimes\rho(f_1)\otimes\rho(f_2))A\bigr)
=\operatorname{tr}\bigl(\rho(f_0)\rho(f_2)\rho(f_1)\bigr).
\tag{14.1}
$$

The order agrees with the chosen cyclic permutation.  On the geometric side, a twisted element
$(\delta_0,\delta_1,\delta_2)$ reduces to the ordinary conjugacy class of the corresponding
ordered product.  Thus (14.1) is not an accidental tensor identity; it is the local spectral
shadow of the norm.

If one $f_j$ is a supercuspidal coefficient, the product test is strongly cuspidal.  If all
three are normalized coefficients of $\rho$, the selected twisted trace is one.  These are
distinct uses of the local factors.

### 14.2 An inert unramified place

Let $E_w/F_v$ be unramified cubic and let $\pi_v$ have Satake parameters
$\{\alpha,\beta\}$.  Its base change has parameters $\{\alpha^3,\beta^3\}$.  If
$t=\alpha+\beta$ and $d=\alpha\beta$, then

$$
\alpha^3+\beta^3=t^3-3dt.
\tag{14.2}
$$

A spherical test with Satake transform $X^3+Y^3$ therefore evaluates to $t^3-3dt$.  No choice
of eigenvalue ordering enters.  Geometrically, the same cubic degree appears because the norm
multiplies valuations by three.  It would be wrong to use the ordinary eigenvalue $t$ at this
inert place.

### 14.3 A quadratic invariant discrete representation

Let $L/k$ be quadratic and let $D$ be a $\sigma$-invariant supercuspidal representation of
$\mathrm{GL}_2(L)$.  Choose $A^2=1$.  The smooth space decomposes into the $+1$ and $-1$
eigenspaces of $A$.  A normalized coefficient based on a unit vector $u_+$ in the first has
twisted trace $+1$.  A coefficient based on $u_-$ has twisted trace $-1$; multiplying it by
$-1$ restores trace $+1$.

Before the final multiplication by $-1$, the two normalized coefficient functions have the
same ordinary character values on irreducible representations but opposite twisted traces;
the scalar adjustment that restores twisted trace $+1$ also changes the ordinary trace to
$-1$.  This is a concrete warning that an ordinary
pseudo-coefficient does not determine a twisted pseudo-coefficient until $A$ is fixed.

If the local parameter has scalar endomorphisms, its descents differ by the quadratic character
of $k^\times/N(L^\times)$.  The underlying invariant representation $D$ does not distinguish
the two descents; the chosen extension operator does.  Twisted character normalization records
that extra datum.

### 14.4 Failure modes

Several plausible simplifications are invalid.

**Using $\phi(\sigma x)$ in (2.1) without changing the rest.**  This reverses (2.2), the local
intertwining relation, and the ordered product on the geometric side.

**Normalizing only by $A^\ell=1$.**  There are still $\ell$ root-of-unity choices.  The
automorphic normalization or an equivalent declared global product is necessary.

**Replacing strong cuspidality by induced trace zero.**  A scattering operator can turn a
trace-zero test operator into a nonzero product trace.  Equation (3.4), not merely its trace,
is required.

**Inferring trace class from (4.4).**  An integrable displayed diagonal is not a trace-class
criterion.  The cuspidal Sobolev factorization proves trace class independently.

**Writing $m(\Pi)\operatorname{tr}(\Pi(f)A)$ without a multiplicity action.**  In general the
correct factor is (6.8).  Multiplicity one and automorphic normalization reduce it to (6.6).

**Factoring a global intertwiner place by place without a scalar ledger.**  The product can
differ from the automorphic intertwiner by a root of unity, changing every spectral term.

**Calling every stable local representation a selected base change.**  Invariance guarantees
an unrestricted parameter extension, but the declared wild boundary can lie outside the
selected local correspondence.

**Deducing global automorphy from local restriction.**  Local parameters specify a candidate
restricted tensor product.  A global trace comparison is needed to prove that the candidate
occurs automorphically.

**Omitting quadratic scalar-norm terms.**  A nonnorm scalar can have quaternion division
centralizer and is elliptic for the twisted geometric formula even though its stable norm is
central.

**Treating local orbital matching as a consequence of the global trace identity.**  Global
cancellation can hide local discrepancies.  The local identities in (13.8) require their own
proof with exact measures.

**Collapsing regular projective twisted classes to $\mathrm{PGL}_2(F)$ norm classes.**  Scalar
projection changes an actual norm only by $N_{E/F}(E^\times)$.  The larger quotient by all of
$F^\times$ can merge distinct geometric terms and lose their stabilizer indices.

## 15. Final synthesis

The theory can now be compressed without concealing any of the analytic or normalization
steps.  This final chapter records both the logical chain and the package exported to cyclic
comparison.

### 15.1 The complete implication chain

The construction proceeds as follows:

$$
\begin{aligned}
&\text{finite support and archimedean rapid decrease}\\
&\qquad\Longrightarrow
\text{a smooth, locally absolutely convergent twisted kernel},\\[2mm]
&\text{one two-sided strongly cuspidal local factor}\\
&\qquad\Longrightarrow
\text{zero constant terms in both kernel variables},\\[2mm]
&\text{two-variable cuspidality and finite compact type}\\
&\qquad\Longrightarrow
\text{simultaneous rapid decay and cuspidal Sobolev factorization},\\[2mm]
&\text{Sobolev factorization}\\
&\qquad\Longrightarrow
T_\sigma(f)\text{ trace class and }
\operatorname{tr}T_\sigma(f)=\int K_f^\sigma(x,x)\,dx,\\[2mm]
&U_\sigma\text{ permutes cuspidal isotypic summands}\\
&\qquad\Longrightarrow
\text{only }\sigma\text{-stable }\Pi\text{ contribute},\\[2mm]
&\text{automorphic normalization and restricted tensors}\\
&\qquad\Longrightarrow
\operatorname{tr}_\sigma\Pi(f)
=\prod_v\operatorname{tr}(\Pi_v(f_v)A_{\Pi_v}),\\[2mm]
&\text{zero induced operator and rank-one residue classification}\\
&\qquad\Longrightarrow
I_{\mathrm{cont}}^\sigma(f)=I_{\mathrm{res}}^\sigma(f)=0,\\[2mm]
&\text{convergent twisted orbit expansion}\\
&\qquad\Longrightarrow
\text{the twisted simple trace formula},\\[2mm]
&\text{local orbital matching and global coefficient--fiber matching}\\
&\qquad\Longrightarrow
\text{ordinary--twisted spectral comparison}.
\end{aligned}
\tag{15.1}
$$

Each arrow has its own hypothesis.  In particular, local cuspidality proves operator vanishing;
trace class proves absolute spectral summability; automorphic normalization fixes cyclic
scalars; and local matching together with the global coefficient--fiber identity identifies
geometric sides.

### 15.2 The reusable theorem package

The individual conclusions are most useful when exported as one interface: later comparison
arguments should not have to reconstruct trace class, intertwiner normalization, noncuspidal
vanishing, and geometric convergence separately.  The following theorem gathers exactly the
hypotheses under which all four features coexist.

**Theorem 15.1 (twisted cuspidal kernel and spectral package).** Let $E/F$ be cyclic of prime
degree $\ell$, fix a generator $\sigma$, and let $\Omega$ be a $\sigma$-invariant unitary Hecke
character of $E$.  Let $f$ be a finite sum of factorizable test functions with inverse central
character, finite level, finite left and right compact type, spherical almost everywhere, and
one strongly cuspidal local factor in every tensor summand.  Using the established global
multiplicity-one theorem for $\mathrm{GL}_2$, the following conclusions hold:

1. The kernel

   $$
   K_f^\sigma(x,y)=
   \sum_{\delta\in Z_E(E)\backslash G_E(E)}
   f(x^{-1}\delta\sigma(y))
   $$

   is smooth, cuspidal in both variables, and rapidly decreasing with every invariant
   derivative.
2. $T_{\sigma,\Omega}(f)=R_\Omega(f)U_\sigma$ is trace class, depends continuously on $f$ in
   trace norm, and

   $$
   \operatorname{tr}T_{\sigma,\Omega}(f)
   =\int_{X_{E,\Omega}}K_f^\sigma(x,x)\,dx.
   $$
3. It annihilates the full continuous and residual spectrum.
4. Its spectral expansion is the absolutely convergent sum

   $$
   \operatorname{tr}T_{\sigma,\Omega}(f)
   =\sum_{\substack{\Pi\in\mathcal A_{\mathrm{cusp}}(E,\Omega)\\
                     \Pi^\sigma\simeq\Pi}}
   \operatorname{tr}\bigl(\Pi(f)A_\Pi^{\mathrm{aut}}\bigr).
   $$

5. For coherent local intertwiners this twisted trace is a finite product of local twisted
   traces, and at a split place it reduces to the ordinary trace of the cyclic product.
6. The same trace equals the absolutely convergent projective geometric distribution consisting
   of the split scalar channel, the regular elliptic projective twisted classes in (11.7a),
   whose actual norms satisfy the torus norm condition, and, when $\ell=2$, the quaternion
   division scalar channel.  No split regular, nonsemisimple, continuous, or residual term
   remains.
7. A twisted pseudo-coefficient attached to a normalized invariant square-integrable local
   representation has twisted trace one on that representation and zero on every other
   $\sigma$-stable unitary irreducible representation with its declared intertwiner.

**Proof.** Chapters 3--5 prove items 1 and 2.  Chapters 9 and 10 prove item 3.  Chapters 6--8
prove items 4 and 5, including absolute convergence and normalization.  Theorems 11.1 and 11.2
prove item 6.  Proposition 12.1 proves item 7. $\square$

### 15.3 Conclusion

The field automorphism has now been incorporated into the trace formula at every level where it
matters.  On the operator side it is the unitary map $U_\sigma$; on the kernel side it replaces
$y$ by $\sigma(y)$; on the geometric side it creates $\sigma$-conjugacy and the ordered norm;
and on the spectral side it permutes automorphic representations and supplies cyclic
intertwiners.

One strongly cuspidal local factor controls all noncompact phenomena.  Its two-sided constant
term makes the twisted kernel cuspidal in both variables, from which rapid decay and trace class
follow.  The same local condition makes every induced test operator zero.  It therefore removes
unitary Eisenstein packets, every scattering expression built from them, and every residual
determinant character.  The final spectral sum is genuinely cuspidal.

The surviving blocks are exactly the $\sigma$-stable cuspidal representations.  Their weights
are not ordinary characters but automorphically normalized twisted characters.  Coherent local
intertwiners factor those weights into finitely many local traces; cyclic permutation at split
places becomes an ordinary trace of a product, while invariant field places admit twisted
pseudo-coefficients of trace one.  Global trace class makes the resulting sum absolutely
convergent and permits every later regrouping.

Finally, the canonical diagonal identifies this spectral sum with the convergent twisted
geometric distribution.  The scalar, regular elliptic, and quadratic quaternionic channels are
all present with compatible measures, while the parabolic classes have cancelled before the
truncation is removed.  The twisted simple trace formula is therefore complete on both sides.
It supplies cyclic base change with its exact spectral mechanism: invariance, descent data,
unramified power maps, selectors, and no noncuspidal remainder.  Once corresponding local
orbital integrals and the global projective coefficient--fiber identities are matched, the
ordinary and twisted formulas can be compared without a hidden scalar, missing class, or
unsupported spectral term.
