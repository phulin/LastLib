# The Cuspidal Spectral Side of the $\mathrm{GL}_2$ Trace Formula

## Contents

- [Introduction](#introduction)
- [1. The spectral question after the kernel theorem](#1-the-spectral-question-after-the-kernel-theorem)
  - [1.1 What remains to be computed](#11-what-remains-to-be-computed)
  - [1.2 Standing global hypotheses](#12-standing-global-hypotheses)
  - [1.3 The three spectral channels](#13-the-three-spectral-channels)
  - [1.4 Main result in preliminary form](#14-main-result-in-preliminary-form)
- [2. Measures, centers, and convolution](#2-measures-centers-and-convolution)
  - [2.1 Absolute values and Haar measures](#21-absolute-values-and-haar-measures)
  - [2.2 Fixed central character](#22-fixed-central-character)
  - [2.3 Local and global convolution](#23-local-and-global-convolution)
  - [2.4 The normalization ledger](#24-the-normalization-ledger)
- [3. Local trace operators](#3-local-trace-operators)
  - [3.1 Why local traces need finite analytic support](#31-why-local-traces-need-finite-analytic-support)
  - [3.2 Compact projectors](#32-compact-projectors)
  - [3.3 Traces on admissible representations](#33-traces-on-admissible-representations)
  - [3.4 Tensor products and traces](#34-tensor-products-and-traces)
- [4. Strongly cuspidal functions](#4-strongly-cuspidal-functions)
  - [4.1 The two-sided constant term](#41-the-two-sided-constant-term)
  - [4.2 Vanishing on induced representations](#42-vanishing-on-induced-representations)
  - [4.3 The trace-level parabolic transform](#43-the-trace-level-parabolic-transform)
  - [4.4 Why operator vanishing is the decisive condition](#44-why-operator-vanishing-is-the-decisive-condition)
- [5. Pseudo-coefficients of square-integrable representations](#5-pseudo-coefficients-of-square-integrable-representations)
  - [5.1 Formal degree and Schur orthogonality](#51-formal-degree-and-schur-orthogonality)
  - [5.2 Construction of the selector](#52-construction-of-the-selector)
  - [5.3 The pseudo-coefficient theorem](#53-the-pseudo-coefficient-theorem)
  - [5.4 Dependence on the vector and the measure](#54-dependence-on-the-vector-and-the-measure)
  - [5.5 Discrete series at a real place](#55-discrete-series-at-a-real-place)
- [6. The global cuspidal decomposition](#6-the-global-cuspidal-decomposition)
  - [6.1 The Hilbert direct sum](#61-the-hilbert-direct-sum)
  - [6.2 The action on an isotypic summand](#62-the-action-on-an-isotypic-summand)
  - [6.3 Absolute convergence of the cuspidal trace](#63-absolute-convergence-of-the-cuspidal-trace)
  - [6.4 What the multiplicity means](#64-what-the-multiplicity-means)
- [7. Factorization of the cuspidal weights](#7-factorization-of-the-cuspidal-weights)
  - [7.1 Restricted tensor products](#71-restricted-tensor-products)
  - [7.2 A finite tensor trace lemma](#72-a-finite-tensor-trace-lemma)
  - [7.3 The factored trace formula](#73-the-factored-trace-formula)
  - [7.4 Spherical factors and Satake normalization](#74-spherical-factors-and-satake-normalization)
- [8. Eisenstein wave packets and the continuous channel](#8-eisenstein-wave-packets-and-the-continuous-channel)
  - [8.1 Normalized induction recalled](#81-normalized-induction-recalled)
  - [8.2 Convolution on genuine wave packets](#82-convolution-on-genuine-wave-packets)
  - [8.3 Vanishing on the unitary axis](#83-vanishing-on-the-unitary-axis)
  - [8.4 Vanishing of the continuous trace distribution](#84-vanishing-of-the-continuous-trace-distribution)
- [9. Residues and their annihilation](#9-residues-and-their-annihilation)
  - [9.1 The residual characters](#91-the-residual-characters)
  - [9.2 Why residues require a separate proof](#92-why-residues-require-a-separate-proof)
  - [9.3 Direct constant-term proof](#93-direct-constant-term-proof)
  - [9.4 No omitted discrete noncuspidal term](#94-no-omitted-discrete-noncuspidal-term)
- [10. The selected cuspidal spectral formula](#10-the-selected-cuspidal-spectral-formula)
  - [10.1 One local discrete-series selector](#101-one-local-discrete-series-selector)
  - [10.2 Several selector places](#102-several-selector-places)
  - [10.3 Finite linear combinations](#103-finite-linear-combinations)
  - [10.4 The complete spectral theorem](#104-the-complete-spectral-theorem)
- [11. Spectral computations with finite-place tests](#11-spectral-computations-with-finite-place-tests)
  - [11.1 Level projectors](#111-level-projectors)
  - [11.2 Spherical Hecke operators](#112-spherical-hecke-operators)
  - [11.3 Ramified matrix coefficients](#113-ramified-matrix-coefficients)
  - [11.4 A weight and level example](#114-a-weight-and-level-example)
- [12. Compatibility with local transfer](#12-compatibility-with-local-transfer)
  - [12.1 What compatibility requires](#121-what-compatibility-requires)
  - [12.2 Measure rescaling](#122-measure-rescaling)
  - [12.3 Spectral normalization of matching functions](#123-spectral-normalization-of-matching-functions)
  - [12.4 A transfer-ready ledger](#124-a-transfer-ready-ledger)
- [13. Continuity, regrouping, and stability](#13-continuity-regrouping-and-stability)
  - [13.1 Continuity of the distribution](#131-continuity-of-the-distribution)
  - [13.2 Legitimate regrouping](#132-legitimate-regrouping)
  - [13.3 Independence from the chosen coefficient](#133-independence-from-the-chosen-coefficient)
  - [13.4 Change of central realization](#134-change-of-central-realization)
- [14. Failure modes and exact boundaries](#14-failure-modes-and-exact-boundaries)
  - [14.1 Trace zero is not operator zero](#141-trace-zero-is-not-operator-zero)
  - [14.2 A pseudo-coefficient is not a central idempotent](#142-a-pseudo-coefficient-is-not-a-central-idempotent)
  - [14.3 Finite multiplicity is not multiplicity one](#143-finite-multiplicity-is-not-multiplicity-one)
  - [14.4 The limits of the present computation](#144-the-limits-of-the-present-computation)
- [15. Final synthesis](#15-final-synthesis)
  - [15.1 The implication chain](#151-the-implication-chain)
  - [15.2 The reusable spectral package](#152-the-reusable-spectral-package)
  - [15.3 Conclusion](#153-conclusion)

## Introduction

The kernel theorem for the simple trace formula produces an honest trace-class convolution
operator. Its trace is already known to be the integral of a canonical automorphic kernel and
to equal an absolutely convergent sum over cuspidal automorphic representations. That theorem
settles existence. It does not yet explain which representations a chosen local test function
detects, how its global trace breaks into local factors, or why the symbols usually called the
continuous and residual spectral terms are exactly zero rather than merely absent from the
notation.

Those questions form the spectral computation carried out here. The decisive local object is a
pseudo-coefficient of a square-integrable representation. After the Haar measure is fixed, the
kernel-admissible normalized coefficient used here gives trace one on the chosen representation
and zero on every other irreducible unitary representation. More importantly for the global
argument, it is strongly cuspidal: its two-sided unipotent constant terms vanish. Tensor
factorization then makes the global test operator zero on every unitary parabolically induced
representation. This kills unitary Eisenstein wave packets before integration and kills every
expression involving a scattering operator. Residual determinant characters are killed
separately by the vanishing parabolic transform. Keeping those arguments separate is essential
at an archimedean selector: its Schwartz coefficient has an honest convolution action on the
unitary axis, but need not admit the same off-axis meromorphic action at a reducibility point.

What survives is concrete. If the factor at a real place $v_0$ selects a discrete series
$D$, then

$$
I_{\mathrm{spec},\omega}(f)
=\sum_{\substack{\pi\ \mathrm{cuspidal}\\
                  \omega_\pi=\omega,\ \pi_{v_0}\simeq D}}
m(\pi)\operatorname{tr}\pi^{v_0}(f^{v_0}).
$$

The multiplicity $m(\pi)$ is retained. The analytic theory available here proves that it is a
positive finite integer; it does not prove multiplicity one. Keeping that factor visible is
both logically necessary and useful in later comparisons.

Every normalization in this formula matters. The test function transforms by the inverse of
the automorphic central character. Formal degrees use the same quotient Haar measures as
local convolution. Maximal compact subgroups have probability measure, so their idempotents
are genuine projectors. The global trace of a tensor product is the product of local traces on
the finite-dimensional range selected by the test. These conventions are recorded in a form
that can be carried unchanged into local transfer: later matching may change the group and the
orbital integrals, but it must not introduce an invisible spectral scalar.

The argument is deliberately arranged in the order in which the infinite operations become
legitimate. We first construct and compute local trace operators, then pass to the discrete
cuspidal Hilbert sum, then eliminate the continuous and residual channels, and only afterward
write the fully selected formula. Thus no formal trace of an individual Eisenstein series and
no conditionally convergent rearrangement enters the proof.

## 1. The spectral question after the kernel theorem

### 1.1 What remains to be computed

A trace formula has a geometric and a spectral face. The preceding kernel theory establishes
their equality for a class of test functions with one strongly cuspidal real factor. On the
spectral side it gives

$$
\operatorname{tr}R_\omega(f)
=\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
m(\pi)\operatorname{tr}\pi(f),
\tag{1.1}
$$

with absolute convergence. Formula (1.1) is already a theorem, but it is not yet a
computation of the chosen test. The term $\operatorname{tr}\pi(f)$ still hides all local
selection rules.

The problem is therefore to answer four questions.

1. Which local representations have nonzero trace against the cuspidal factor?
2. How does the global trace split into local traces without an infinite-product ambiguity?
3. Why do the continuous Eisenstein contribution and the residual contribution vanish in every
   standard spectral expansion?
4. Which multiplicity and measure factors remain after the local selector has been normalized?

The answer to the first question is Schur orthogonality, but only after the formal degree and
central quotient have been fixed. The answer to the second is a finite tensor-product lemma,
not a formal multiplication of infinitely many traces. The third uses the two-sided constant
term of the test function. The fourth requires us to resist two tempting simplifications:
formal degree is not automorphic multiplicity, and finite multiplicity is not multiplicity one.

### 1.2 Standing global hypotheses

Let $F$ be a number field with a real place $v_0$, and let $\mathbf A=\mathbf A_F$. Put

$$
G=\mathrm{GL}_2,\qquad
Z=\{zI_2:z\in\mathbf G_m\},\qquad
B=TN,
$$

where $T$ is the diagonal torus and

$$
N=\left\{n(u)=
\begin{pmatrix}1&u\\0&1\end{pmatrix}:u\in\mathbf G_a\right\}.
$$

Fix a unitary idele class character

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times.
\tag{1.2}
$$

Automorphic functions obey

$$
\phi(zg)=\omega(z)\phi(g)
\tag{1.3}
$$

and are squared-integrated on

$$
[\overline G]=Z(\mathbf A)G(F)\backslash G(\mathbf A).
\tag{1.4}
$$

We use exactly the test class for which the preceding kernel theorem applies: finite sums of
factorizable functions $f=\otimes_v f_v$, compactly supported modulo the center at finite
places, finite under left and right maximal compact actions, and strongly cuspidal at the fixed
real place $v_0$. At each archimedean place the factor is not merely Harish--Chandra Schwartz:
it is kernel-admissible for the fixed heights and exponent of the kernel theorem. Thus, if
$A_F$ dominates its volume-growth and rational-point exponents and $Q>A_F+1$ is fixed, every
left-right invariant differential operator $D_1$ satisfies

$$
|D_1f_v(g)|\leq C_{D_1}\|g\|_v^{-Q}.
\tag{1.5a}
$$

Every factor also satisfies

$$
f_v(zg)=\omega_v(z)^{-1}f_v(g).
\tag{1.5}
$$

The inverse in (1.5) is forced: $f_v(g)\pi_v(g)$ must descend to $Z(F_v)\backslash G(F_v)$ when
$\pi_v$ has central character $\omega_v$.

We choose $Q$ once and for all large enough also to dominate the fixed Iwasawa exponents in the
bounded complementary-series strip $|\operatorname{Re}(s)|\leq1/2$; increasing $Q$ preserves
the kernel theorem. Kernel admissibility is a genuine extra hypothesis. That theorem proves that
compact-finite real discrete-series coefficients of sufficiently high lowest weight satisfy it
for the fixed $Q$; it does not assert this for every lowest weight merely from membership in the
Harish--Chandra Schwartz space. All trace-class statements below retain this threshold.

The restriction to a real $v_0$ is the exact hypothesis of the kernel theorem used here. The
purely spectral annihilation argument works equally well with a strongly cuspidal
nonarchimedean factor, for example a supercuspidal coefficient. We distinguish that broader
local fact from the narrower global kernel theorem rather than silently enlarging the latter.

### 1.3 The three spectral channels

The fixed-central-character automorphic space has three relevant kinds of contribution.

The **cuspidal channel** is a Hilbert direct sum of irreducible unitary representations with
finite multiplicities. It is the only channel on which the selected trace will survive.

The **continuous channel** is generated by wave packets of Eisenstein series obtained from
normalized induction

$$
I(\chi,s)
=\operatorname{Ind}_{B(\mathbf A)}^{G(\mathbf A)}
\bigl(\chi_1\otimes\chi_2\bigr)|\alpha|^{s},
\qquad \chi_1\chi_2=\omega,
\tag{1.6}
$$

where normalized induction includes the factor $\delta_B^{1/2}$ and the unitary axis is
$s\in i\mathbf R$.

The **residual channel** consists in rank one of the one-dimensional representations

$$
g\longmapsto\eta(\det g),
\qquad \eta^2=\omega.
\tag{1.7}
$$

They arise as residues of the Eisenstein families. They are discrete in $L^2$ but are not
cuspidal. Thus “discrete spectral term” and “cuspidal spectral term” are not synonyms. A
correct proof must eliminate (1.7) separately.

### 1.4 Main result in preliminary form

Choose an irreducible square-integrable representation $D$ of $G(F_{v_0})$ modulo its center,
with central character $\omega_{v_0}$. A normalized pseudo-coefficient $f_D$ will be constructed
in Chapter 5. For the global trace-class formula we assume that its chosen compact-finite
coefficient is kernel-admissible in the sense of (1.5a). Let

$$
f=f_D\otimes f^{v_0}.
\tag{1.8}
$$

Then the results proved below give

$$
\begin{aligned}
I_{\mathrm{cont},\omega}(f)&=0,\\
I_{\mathrm{res},\omega}(f)&=0,\\
I_{\mathrm{cusp},\omega}(f)
&=\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_{v_0}\simeq D}}
m(\pi)\operatorname{tr}\pi^{v_0}(f^{v_0}).
\end{aligned}
\tag{1.9}
$$

The last series is absolutely convergent. Its equality with the kernel trace follows from the
preceding kernel theorem; its explicit selection rule is proved here. Formula (1.9) is the
basic spectral side used in trace comparison.

Three direct dependency interfaces are used. Reduction theory supplies the closed
cuspidal space and its countable irreducible decomposition with finite multiplicities, for an
arbitrary number field and a unitary central character. Global constant-term theory supplies the
classification of the orthogonal complement into normalized Eisenstein wave packets and the
characters $\eta\circ\det$ with $\eta^2=\omega$, as well as the theorem that a strongly cuspidal
local factor kills that complement. The cuspidal kernel theorem supplies trace class, the
canonical diagonal trace, and absolute convergence of the sum in (1.1) for the test class stated
in Section 1.2. We apply these results with exactly their fixed central character, quotient Haar
measures, finite level, finite compact type, and real cuspidal place. Local admissibility,
Schur orthogonality for square-integrable representations, and the rank-one classification of
the local unitary dual are the ordinary local representation theory used to compute the new
local traces. We also use the previously established restricted tensor decomposition of a
cuspidal automorphic representation and its distinguished unramified lines. No global
multiplicity-one, newvector, transfer, or later comparison theorem enters the argument.

## 2. Measures, centers, and convolution

### 2.1 Absolute values and Haar measures

At a finite place $v$, normalize absolute value by

$$
|\varpi_v|_v=q_v^{-1},
$$

and at a complex place use the square of the ordinary modulus. Then the product formula holds
on $F^\times$. Give every maximal compact subgroup $K_v$ probability Haar measure. The Haar
measure $dg_v$ on $G(F_v)$ is the Iwasawa measure already fixed by

$$
dg_v=\delta_B(t)^{-1}\,dn_v\,d^\times a_v\,d^\times d_v\,dk_v,
\qquad t=\operatorname{diag}(a_v,d_v),
\tag{2.1}
$$

with

$$
\delta_B(t)=|a_v/d_v|_v.
$$

On the global unipotent quotient $F\backslash\mathbf A$, use probability measure. Equivalently,
one may take the product of self-dual local additive measures for the standard global additive
character; its quotient covolume is one. This compatibility is what allows a global unipotent
integral to factor with no discriminant scalar.

Quotient measures are always induced by iterated integration. In particular, $d\bar g_v$ on
$Z(F_v)\backslash G(F_v)$ and $d\bar g$ on $Z(\mathbf A)\backslash G(\mathbf A)$ are not chosen
afresh. The global quotient measure on (1.4) is complementary to the same $d\bar g$. Every
formal degree below refers to $d\bar g_v$.

### 2.2 Fixed central character

Let $\pi_v$ have central character $\omega_v$. For a function satisfying (1.5), define

$$
\pi_v(f_v)
=\int_{Z(F_v)\backslash G(F_v)}f_v(g)\pi_v(g)\,d\bar g.
\tag{2.2}
$$

The integrand is independent of the representative of the central coset, since

$$
f_v(zg)\pi_v(zg)
=\omega_v(z)^{-1}f_v(g)\omega_v(z)\pi_v(g)
=f_v(g)\pi_v(g).
$$

This calculation is small but indispensable. Using the same central character on the test and
the representation would make (2.2) fail to descend.

Globally,

$$
(R_\omega(f)\phi)(x)
=\int_{Z(\mathbf A)\backslash G(\mathbf A)}
f(g)\phi(xg)\,d\bar g.
\tag{2.3}
$$

Young's inequality gives $\|R_\omega(f)\|\leq\|f\|_1$. Its adjoint is convolution by

$$
f^*(g)=\overline{f(g^{-1})}.
\tag{2.4}
$$

Because $\omega$ is unitary, $f^*$ again has inverse central character.

### 2.3 Local and global convolution

If $f_1,f_2$ have the compatible central transformation, define convolution on the central
quotient by

$$
(f_1*f_2)(g)
=\int_{Z\backslash G}f_1(h)f_2(h^{-1}g)\,d\bar h.
\tag{2.5}
$$

Absolute convergence and Fubini give

$$
\pi(f_1*f_2)=\pi(f_1)\pi(f_2),
\qquad
R_\omega(f_1*f_2)=R_\omega(f_1)R_\omega(f_2).
\tag{2.6}
$$

At a finite place compact support modulo $Z_v$ makes these integrals ordinary finite-volume
integrals. At infinity the kernel-admissible estimates of Section 1.2 make them absolutely
convergent with every invariant derivative. Globally those estimates, finite support, and the
restricted-product normalization give an integrable function on
$Z(\mathbf A)\backslash G(\mathbf A)$.

The order convention in (2.2) is right convolution. Replacing $g$ by $g^{-1}$ or omitting the
complex conjugation in a matrix-coefficient selector would replace a projection by its adjoint.
The trace might remain the same in a special case, but local character formulas would no longer
match term by term. We keep (2.2)--(2.4) fixed throughout.

### 2.4 The normalization ledger

The conventions can be summarized as follows.

| Object                     | Convention                                                       |
| -------------------------- | ---------------------------------------------------------------- |
| Finite absolute value      | $\lvert\varpi_v\rvert_v=q_v^{-1}$                                |
| Complex absolute value     | Square of ordinary modulus                                       |
| Maximal compact measure    | $\operatorname{vol}(K_v)=1$                                      |
| Unipotent quotient         | Probability measure on $F\backslash\mathbf A$                    |
| Group measure              | Iwasawa measure (2.1)                                            |
| Central quotient measure   | Induced by quotient integration                                  |
| Automorphic central action | $\phi(zg)=\omega(z)\phi(g)$                                      |
| Test central action        | $f(zg)=\omega(z)^{-1}f(g)$                                       |
| Local operator             | $\pi_v(f_v)=\int_{Z_v\backslash G_v}f_v(g)\pi_v(g)d\bar g$       |
| Compact idempotent         | Normalized central-character average (3.1)                       |
| Normalized induction       | Includes $\delta_B^{1/2}$; unitary axis $\operatorname{Re}(s)=0$ |
| Formal degree              | Relative to the displayed local quotient measure                 |
| Automorphic multiplicity   | $m(\pi)=\dim M_\pi$, independent of formal degree                |

Changing a Haar measure changes several entries together. A later comparison is compatible
only if it transports the whole ledger, not one isolated formula.

## 3. Local trace operators

### 3.1 Why local traces need finite analytic support

An irreducible unitary representation of $G(F_v)$ is usually infinite-dimensional. The trace
of $\pi_v(f_v)$ therefore needs justification. Compact support alone gives a bounded smoothing
operator, but an arbitrary smoothing operator on a noncompact representation space need not be
trace class.

The test functions used here are finite under left and right maximal compact actions. At a
finite place they are bi-invariant under compact open subgroups after passing to a finite sum of
translates. At an archimedean place only finitely many left and right $K_v$-types occur. Local
admissibility then confines the range to a finite-dimensional space. This is the elementary
source of the local trace.

### 3.2 Compact projectors

Let $J\subset G(F_v)$ be compact open and assume that $\omega_v$ is trivial on $J\cap Z_v$.
Write $\overline J$ for the image of $J$ in $Z_v\backslash G(F_v)$. The central-character
extension of its normalized characteristic function is

$$
e_{J,\omega_v}(zj)
=\frac{\omega_v(z)^{-1}}{\operatorname{vol}(\overline J)}
\quad(z\in Z_v,\ j\in J),
\qquad
e_{J,\omega_v}(g)=0\quad(g\notin Z_vJ).
\tag{3.1}
$$

The condition on $J\cap Z_v$ makes this definition independent of the decomposition $zj$.
For a representation with central character $\omega_v$, quotient convolution gives

$$
\pi_v(e_{J,\omega_v})u
=\frac1{\operatorname{vol}(\overline J)}
  \int_{\overline J}\pi_v(j)u\,d\bar j.
$$

We abbreviate $e_{J,\omega_v}$ to $e_J$ when the central character is fixed.

**Proposition 3.1.** The operator $\pi_v(e_J)$ is the orthogonal projection onto
$\mathcal H_{\pi_v}^J$.

**Proof.** Haar invariance gives $\pi_v(j_0)\pi_v(e_J)=\pi_v(e_J)$ for $j_0\in J$, so the range is
$J$-fixed. If $u$ is $J$-fixed, the integral equals $u$. Finally
$e_J^*=e_J$, hence the idempotent is self-adjoint. It is therefore the orthogonal projection.
$\square$

In particular,

$$
\operatorname{tr}\pi_v(e_J)=\dim\mathcal H_{\pi_v}^J<\infty.
\tag{3.2}
$$

The final inequality is admissibility. At an archimedean place, character averaging over
$K_v$ gives the analogous projector $e_\tau$ onto a $K_v$-isotypic space. That whole isotypic
space can contain several copies of $\tau$, but admissibility makes its multiplicity finite.

### 3.3 Traces on admissible representations

**Proposition 3.2.** Let $\pi_v$ be an irreducible admissible representation with the prescribed
unitary central character. If $f_v$ is left finite under $K_v$ and right invariant under a
compact open subgroup at a finite place, or left and right $K_v$-finite at an archimedean place,
then $\pi_v(f_v)$ has finite rank. Consequently its trace is defined and basis-independent.

**Proof.** At a finite place choose a compact open subgroup $J_L$ under which the finite span of
left translates of $f_v$ is fixed. Then

$$
\pi_v(e_{J_L})\pi_v(f_v)=\pi_v(f_v),
$$

so the range lies in $\mathcal H_{\pi_v}^{J_L}$, which is finite-dimensional. At infinity,
decompose the finite left $K_v$-span into finitely many irreducible compact types. The range of
$\pi_v(f_v)$ lies in their isotypic sum, finite-dimensional by admissibility. A finite-rank
operator has a well-defined trace. $\square$

Right finiteness is not needed merely for finite rank, but it makes the adjoint range finite and
is used by the global trace-class kernel theorem. It also makes tensor factorizations symmetric
between source and target.

### 3.4 Tensor products and traces

For finite-dimensional vector spaces $V_i$ and endomorphisms $A_i$, one has

$$
\operatorname{tr}(A_1\otimes\cdots\otimes A_r)
=\prod_{i=1}^r\operatorname{tr}(A_i).
\tag{3.3}
$$

Choose bases and compute the diagonal entries: a tensor basis vector contributes the product of
the corresponding diagonal entries, and summing independently gives (3.3).

The same assertion holds when the $A_i$ act on infinite-dimensional Hilbert spaces but have
finite-dimensional ranges contained in finite-dimensional subspaces $V_i$: restrict to
$V_1\otimes\cdots\otimes V_r$, where the ordinary proof applies, and note that the operator is
zero on a complementary source after the appropriate right projectors. This finite lemma is
the only tensor-trace assertion needed globally. We will reduce every adelic product to it by
using the distinguished spherical line outside a finite set of places.

## 4. Strongly cuspidal functions

### 4.1 The two-sided constant term

The constant term of an automorphic function averages one variable over the global unipotent
quotient. For an operator kernel, both source and target variables remain. This leads to the
local condition

$$
\mathcal C_{f_v}(x,y;t)
=\int_{N(F_v)}f_v(x^{-1}tny)\,dn,
\qquad x,y\in G(F_v),\ t\in T(F_v).
\tag{4.1}
$$

**Definition 4.1.** The function $f_v$ is **strongly cuspidal** if (4.1) is zero for every
$x,y,t$. At an archimedean place absolute convergence is included in the definition.

The quantifiers in this definition are essential. The value with $x=y=1$ does not control the
kernel between arbitrary compact-picture vectors. The condition is stable under left and
right translation and under adjoint. For the adjoint this follows by inversion, replacement of
$n$ by $n^{-1}$, and conjugation by $t$; the modular factor introduced in the measure change is
nonzero and therefore preserves vanishing.

### 4.2 Vanishing on induced representations

Let

$$
I_v(\xi_1,\xi_2;s)
=\operatorname{Ind}_{B(F_v)}^{G(F_v)}
(\xi_1\otimes\xi_2)|\alpha|_v^s
\tag{4.2}
$$

be normalized induction, so a section transforms by
$\xi_1(a)\xi_2(d)|a/d|_v^{s+1/2}$.

**Theorem 4.2.** If $f_v$ is strongly cuspidal, then

$$
I_v(\xi_1,\xi_2;s)(f_v)=0
\tag{4.3}
$$

on the unitary principal axis. The same conclusion holds at any other parameter for which the
compact-picture integral below is an absolutely convergent honest convolution operator. If
$f_v$ is compactly supported modulo the center, it holds for every parameter as a meromorphic
finite-type operator identity.

**Proof strategy.** Write the operator in the compact picture. Its kernel is a Mellin transform
of the two-sided constant term (4.1), so it vanishes before a trace is taken.

**Proof.** For compact-picture points $x,y$, Iwasawa integration gives the matrix kernel

$$
K_{f_v,s}(x,y)
=\int_{Z_v\backslash T(F_v)}\xi_1(a)\xi_2(d)|a/d|_v^s\delta_B(t)^{1/2}
\left(\int_{N(F_v)}f_v(x^{-1}tny)\,dn\right)dt.
\tag{4.4}
$$

The quotient by $Z_v$ is required: the central transformations make the integrand descend, but
an integral over all of $T(F_v)$ would contain an infinite central factor. On the unitary axis
the Schwartz algebra acts honestly on tempered induction and Fubini is valid, so the inner
integral is zero and hence so is the kernel. Exactly the same proof applies whenever (4.4) is
absolutely convergent as an honest action. For compact-mod-center $f_v$, each fixed compact-type
matrix entry is a Laurent or Mellin transform of compactly supported data, so the zero identity
continues meromorphically to every parameter. $\square$

For a general archimedean Schwartz coefficient, the last continuation is not available. At a
nonunitary reducibility point a formal regularized principal-series action can contain the very
discrete series from which the coefficient was formed. We therefore use (4.3) only for honest
unitary-axis actions, and for absolutely convergent complementary-series actions when they
occur in the local unitary-dual argument. Residual characters will be killed directly by the
parabolic transform, not by specializing an off-axis zero family.

### 4.3 The trace-level parabolic transform

Average (4.1) over the diagonal compact action and insert the half-density:

$$
f_v^B(t)
=\delta_B(t)^{1/2}
\int_{K_v}\int_{N(F_v)}f_v(k^{-1}tnk)\,dn\,dk.
\tag{4.5}
$$

Taking the compact-picture trace in (4.4) gives

$$
\operatorname{tr}I_v(\xi_1,\xi_2;s)(f_v)
=\int_{Z_v\backslash T(F_v)}\xi_1(a)\xi_2(d)|a/d|_v^s f_v^B(t)\,dt.
\tag{4.6}
$$

Thus $f_v^B=0$ annihilates the trace of every induced representation. Strong cuspidality
implies $f_v^B=0$, but the converse can fail because the $K_v$-average may cancel a nonzero
operator kernel.

Formula (4.6) can also be reversed under the usual Mellin uniqueness hypotheses. If the trace
vanishes for every unitary pair and every imaginary $s$, then Fourier inversion on the compact
part of $T_v/Z_v$ and Mellin inversion on its split part give $f_v^B=0$. This equivalence is
useful for trace distributions, but it still does not recover the unaveraged two-sided
condition.

### 4.4 Why operator vanishing is the decisive condition

In a regularized spectral formula the continuous term can contain a scattering operator and
its logarithmic derivative next to $I(\chi,it)(f)$. Knowing only
$\operatorname{tr}I(\chi,it)(f)=0$ does not imply

$$
\operatorname{tr}\bigl(M(\chi,it)^{-1}M'(\chi,it)
I(\chi,it)(f)\bigr)=0.
$$

Two matrices can have zero trace while their product has nonzero trace. Equation (4.3), by
contrast, makes the final factor itself zero. Every continuous expression containing it then
vanishes without a commutation or diagonalization argument.

The preceding kernel theorem also needs operator vanishing in order to prove cuspidality in both
variables and trace class before taking a trace. Weaker trace-level cancellation is adequate
only after a trace formula with all regularized terms has independently been constructed. The
selected pseudo-coefficients below satisfy the stronger condition, so no such distinction is
hidden in the main theorem.

## 5. Pseudo-coefficients of square-integrable representations

### 5.1 Formal degree and Schur orthogonality

Let $k$ be a local field of characteristic zero, $G_k=\mathrm{GL}_2(k)$, and let $D$ be an
irreducible unitary representation that is square-integrable modulo $Z_k$. Write $\omega_D$
for its central character. The formal degree $d(D)>0$, relative to the fixed measure on
$Z_k\backslash G_k$, is characterized by Schur orthogonality:

$$
\int_{Z_k\backslash G_k}
\langle D(g)u_1,v_1\rangle
\overline{\langle D(g)u_2,v_2\rangle}\,d\bar g
=d(D)^{-1}\langle u_1,u_2\rangle
\overline{\langle v_1,v_2\rangle}.
\tag{5.1}
$$

We take the Hilbert inner product to be linear in its first variable. Formula (5.1) is
well-defined on the central quotient because the two matrix coefficients have cancelling
central characters.

For completeness, the form of Schur orthogonality needed here follows from irreducibility.
Fix $u_2,v_2$ and define the sesquilinear expression in $u_1,v_1$ by the left side. Translation
in $g$ shows that the associated operator commutes with $D$. Schur's lemma makes it scalar.
Polarization shows that the scalar is a positive constant times the two inner products displayed
in (5.1). Square-integrability makes the constant finite and nonzero. Its reciprocal is, by
definition, the formal degree. Orthogonality between inequivalent square-integrable
representations follows in the same way: the corresponding operator intertwines inequivalent
irreducibles and is therefore zero.

Formal degree is a density attached to a measure. It is not the dimension of $D$, which is
usually infinite, and it is not an automorphic multiplicity.

### 5.2 Construction of the selector

Choose a unit vector $u\in D$ that is smooth and compact-finite. Define

$$
f_{D,u}(g)=d(D)\,\overline{\langle D(g)u,u\rangle}.
\tag{5.2}
$$

Since $D(z)=\omega_D(z)$,

$$
f_{D,u}(zg)=\omega_D(z)^{-1}f_{D,u}(g),
$$

so (5.2) has exactly the inverse central character required by convolution. At a
nonarchimedean place a supercuspidal coefficient is compactly supported modulo the center. At
a real place a compact-finite discrete-series coefficient belongs to the invariant Schwartz
space modulo the center. In either case the constant-term theory proves that (5.2) is strongly
cuspidal.

At a real place, Schwartz membership alone does not imply the kernel-admissible bound (1.5a).
For the global theorems we choose $D$ and $u$ so that this additional bound holds. The explicit
Cartan decay of discrete-series coefficients proves that every sufficiently high lowest weight
in the required parity supplies such a choice.

Apply $D(f_{D,u})$ to $v$ and pair with $w$. By (5.1),

$$
\begin{aligned}
\langle D(f_{D,u})v,w\rangle
&=d(D)\int_{Z_k\backslash G_k}
\overline{\langle D(g)u,u\rangle}
\langle D(g)v,w\rangle\,d\bar g\\
&=\langle v,u\rangle\overline{\langle w,u\rangle}.
\end{aligned}
\tag{5.3}
$$

Thus $D(f_{D,u})$ is the orthogonal rank-one projection onto $\mathbf C u$, and

$$
\operatorname{tr}D(f_{D,u})=1.
\tag{5.4}
$$

The factor $d(D)$ in (5.2) is forced by (5.4). Omitting it would give trace $d(D)^{-1}$.

### 5.3 The pseudo-coefficient theorem

**Theorem 5.1 (matrix-coefficient pseudo-coefficient).** Let $D$ and $f_{D,u}$ be as above. For
every irreducible tempered unitary representation $\sigma$ of $G_k$ with central character
$\omega_D$,

$$
\operatorname{tr}\sigma(f_{D,u})=
\begin{cases}
1,&\sigma\simeq D,\\
0,&\sigma\not\simeq D.
\end{cases}
\tag{5.5}
$$

If $k$ is nonarchimedean, or if $k=\mathbf R$ and $f_{D,u}$ is kernel-admissible for the standing
choice of $Q$, the same formula holds for every irreducible unitary $\sigma$. Moreover
$f_{D,u}$ is strongly cuspidal and acts by zero, not merely trace zero, on every unitary
principal-series representation on which its compact-picture convolution is honest.

**Proof strategy.** Separate the unitary dual into square-integrable representations and
representations obtained from normalized induction. Schur orthogonality handles the first
class; the two-sided constant term handles the second.

**Proof.** Equation (5.4) gives the value for $D$. If $\sigma$ is square-integrable modulo the
center and inequivalent to $D$, mixed Schur orthogonality makes every matrix coefficient of
$\sigma(f_{D,u})$ zero, hence the operator and its trace are zero.

Every irreducible tempered unitary representation that is not square-integrable modulo the
center is an irreducible unitary principal series, including a limit representation at its
tempered boundary. The unitary-axis part of Theorem 4.2 kills its honest convolution operator.

For the strengthened assertion, the remaining infinite-dimensional unitary representations are
complementary series. Their normalized-induction parameters satisfy
$|\operatorname{Re}(s)|<1/2$. At a finite place compact support makes (4.4) an honest finite
Laurent integral. At the real place, the kernel-admissible estimate (1.5a), with $Q$ chosen as
in Section 1.2, dominates the Iwasawa Jacobian, the inducing factor throughout this bounded
strip, and every fixed compact-type matrix entry. Fubini and dominated convergence therefore
make (4.4) an absolutely convergent honest action; its inner constant term is zero.

The only remaining unitary representations are one-dimensional characters $\eta\circ\det$.
Their operator is the scalar obtained by averaging first over $K_k$ and $N_k$ and then taking
the torus Mellin integral. This is the Mellin transform of $f_{D,u}^B=0$, so the scalar is zero.
At a real reducibility point we have not specialized a formal meromorphic induced operator: we
have computed its honest unitary quotient directly. This proves (5.5). $\square$

### 5.4 Dependence on the vector and the measure

Different unit vectors $u$ produce different test functions, but (5.5) gives the same trace on
every irreducible unitary representation. Their difference is spectrally invisible to the
unitary dual at the level of characters. It need not be the zero function, and its individual
orbital integrals need not vanish. A pseudo-coefficient is a selector in the trace quotient of
the test algebra, not a pointwise canonical function.

Now rescale quotient Haar measure by

$$
d\bar g'=c\,d\bar g,
\qquad c>0.
$$

Equation (5.1) shows that

$$
d'(D)=c^{-1}d(D).
\tag{5.6}
$$

Therefore $f'_{D,u}=c^{-1}f_{D,u}$, while the operator is unchanged:

$$
\int f'_{D,u}(g)D(g)\,d\bar g'
=\int f_{D,u}(g)D(g)\,d\bar g.
\tag{5.7}
$$

This covariance is the measure check needed for local transfer. A formal degree cannot be
moved from one Haar convention into another without rescaling the function.

### 5.5 Discrete series at a real place

Take $k=\mathbf R$. For each allowed lowest weight and unitary central twist, the corresponding
discrete-series representation $D$ of $\mathrm{GL}_2(\mathbf R)$ is square-integrable modulo
the center. We use the irreducible representation of the full, disconnected group, rather than
choosing only a holomorphic representation of the identity component. Its restriction to the
positive-determinant component packages the two orientations exchanged by an element of
negative determinant.

This convention prevents a factor of two from appearing later. The local trace in (5.5) is one
on the full representation $D$. If one instead works on the identity component and lists its
holomorphic and antiholomorphic constituents separately, one must also split the local group,
its Haar measure, and the global automorphic representations consistently. Mixing the two
descriptions would double-count the selector.

For the quotient measure inherited from the global ledger, the formal degree is whatever
Schur orthogonality (5.1) assigns. A familiar numerical formula for a differently normalized
$\mathrm{PGL}_2(\mathbf R)$ measure must not be inserted without first comparing measures.
The abstract normalization (5.2) is exact and is all the global spectral proof needs.

## 6. The global cuspidal decomposition

### 6.1 The Hilbert direct sum

Reduction theory and cuspidal compactness give

$$
L^2_{\mathrm{cusp},\omega}
\simeq
\widehat\bigoplus_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
M_\pi\otimes\mathcal H_\pi,
\qquad
m(\pi)=\dim M_\pi<\infty.
\tag{6.1}
$$

The index set consists of equivalence classes, not of repeated copies. The group acts trivially
on $M_\pi$ and irreducibly on $\mathcal H_\pi$. The sum is countable, and on fixed finite level,
fixed archimedean compact type, and bounded elliptic spectral window only finitely many summands
contribute.

This theorem is stronger than the statement that individual cusp forms are eigenfunctions. It
asserts completeness, orthogonality of isotypic summands, and finite multiplicity. It is weaker
than multiplicity one, which is neither assumed nor proved here.

### 6.2 The action on an isotypic summand

On the summand indexed by $\pi$, right convolution has the form

$$
R_\omega(f)|_{M_\pi\otimes\mathcal H_\pi}
=I_{M_\pi}\otimes\pi(f).
\tag{6.2}
$$

Indeed, take the integrated right regular representation. Each copy of $\pi$ receives the same
integrated operator, while the multiplicity coordinate is untouched. Approximation in $L^1$
extends the identity from finite linear combinations of translations to the present test class.

Whenever $\pi(f)$ is trace class,

$$
\operatorname{tr}(I_{M_\pi}\otimes\pi(f))
=m(\pi)\operatorname{tr}\pi(f).
\tag{6.3}
$$

The multiplicity is thus forced by linear algebra. It is not a convention that can be absorbed
into a local factor.

### 6.3 Absolute convergence of the cuspidal trace

For the admissible global tests of Chapter 1, the kernel theorem proves that $R_\omega(f)$ is
trace class and zero on the orthogonal complement of the cuspidal space. Let $P_\pi$ be the
orthogonal isotypic projection. Since the operator is block diagonal,

$$
\sum_\pi\|P_\pi R_\omega(f)P_\pi\|_1
=\|R_\omega(f)\|_1.
\tag{6.4}
$$

To prove this, take finite sums of the mutually orthogonal $P_\pi$, apply the trace to the
positive operator $|R_\omega(f)|$, and pass to the increasing strong limit. Normality of the
trace gives monotone convergence. It follows that

$$
\sum_\pi m(\pi)|\operatorname{tr}\pi(f)|
\leq\sum_\pi m(\pi)\|\pi(f)\|_1
=\|R_\omega(f)\|_1<\infty.
\tag{6.5}
$$

Consequently

$$
I_{\mathrm{cusp},\omega}(f)
:=\sum_\pi m(\pi)\operatorname{tr}\pi(f)
\tag{6.6}
$$

is an ordinary absolutely convergent series. It can be reordered or regrouped by a local type
without changing its value.

### 6.4 What the multiplicity means

The number $m(\pi)$ counts mutually orthogonal automorphic embeddings of the abstract
irreducible representation $\pi$ into $L^2_{\mathrm{cusp},\omega}$. Local admissibility instead
controls dimensions such as $\dim\pi_v^{J_v}$ or the multiplicity of a compact type inside
$\pi_v$. Formal degree controls an $L^2$ norm of local matrix coefficients. These are three
different quantities:

$$
\begin{array}{c|c|c}
\text{quantity}&\text{where it lives}&\text{role}\\ \hline
m(\pi)&\text{global automorphic Hilbert space}&\text{number of copies}\\
\dim\pi_v^{J_v}&\text{local representation}&\text{level multiplicity}\\
d(\pi_v)&\text{local Plancherel normalization}&\text{matrix-coefficient scale}.
\end{array}
\tag{6.7}
$$

The pseudo-coefficient uses $d(D)$ so that its local trace is one. It does not remove
$m(\pi)$ from (6.6). Any formula lacking $m(\pi)$ would be using an additional multiplicity-one
theorem.

## 7. Factorization of the cuspidal weights

### 7.1 Restricted tensor products

Every cuspidal automorphic representation in (6.1) has a restricted tensor decomposition

$$
\pi\simeq\bigotimes_v'\pi_v.
\tag{7.1}
$$

Outside a finite set, $\pi_v$ is unramified and has a distinguished one-dimensional
$K_v$-fixed line. The global test has the form $f=\otimes_v f_v$, with $f_v$ equal outside a
finite set to the normalized spherical idempotent. That idempotent is the identity on the
distinguished line.

Thus the infinite tensor product operator is supported on a finite tensor of nontrivial local
operators. The phrase “product of local traces” is shorthand for this reduction; it is not an
Euler product whose convergence must be separately proved.

### 7.2 A finite tensor trace lemma

**Lemma 7.1.** Let $S$ contain every place where $f_v$ is not the distinguished spherical
idempotent and every place where $\pi_v$ is ramified. Suppose $\pi_v(f_v)$ has finite rank for
$v\in S$. Then $\pi(f)$ has finite rank and

$$
\operatorname{tr}\pi(f)
=\prod_{v\in S}\operatorname{tr}\pi_v(f_v).
\tag{7.2}
$$

**Proof.** Outside $S$, $\pi_v(f_v)$ is the identity on the chosen spherical line. The range of
$\pi(f)$ is therefore the tensor product of the finite-dimensional ranges at $v\in S$ and the
distinguished lines outside $S$. It is canonically a finite-dimensional tensor product.
Restricting to it and applying (3.3) gives (7.2). If a spherical projector meets a representation
without fixed vectors, the local operator and hence the global operator are zero. $\square$

The set $S$ may be enlarged at will: each newly inserted unramified factor contributes trace
one. Therefore (7.2) is independent of the auxiliary choice of $S$.

### 7.3 The factored trace formula

Combining (6.6) and Lemma 7.1 yields

$$
I_{\mathrm{cusp},\omega}(f)
=\sum_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
m(\pi)\prod_{v\in S}\operatorname{tr}\pi_v(f_v),
\tag{7.3}
$$

where the product is finite for each $\pi$. Absolute convergence follows from (6.5); it is not
proved by multiplying absolute local estimates.

If $f_{v_0}=f_D$, Theorem 5.1 replaces the $v_0$ factor by the indicator of
$\pi_{v_0}\simeq D$. Hence

$$
I_{\mathrm{cusp},\omega}(f_D\otimes f^{v_0})
=\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
                  \pi_{v_0}\simeq D}}
m(\pi)\prod_{v\in S\setminus\{v_0\}}
\operatorname{tr}\pi_v(f_v).
\tag{7.4}
$$

Equivalently, the product on the right is $\operatorname{tr}\pi^{v_0}(f^{v_0})$. Formula (7.4)
is the desired local computation of the cuspidal weights.

### 7.4 Spherical factors and Satake normalization

Let $v$ be nonarchimedean, $K_v=\mathrm{GL}_2(\mathcal O_v)$, and suppose $\omega_v$ is
unramified. The normalized spherical idempotent $e_{K_v,\omega_v}$ acts as the identity on
$\pi_v^{K_v}$. Therefore

$$
\operatorname{tr}\pi_v(e_{K_v,\omega_v})
=\begin{cases}
1,&\pi_v\text{ unramified},\\
0,&\pi_v^{K_v}=0.
\end{cases}
\tag{7.5}
$$

For a spherical Hecke function $h_v$, its trace is its scalar on the spherical line. We fix the
Satake normalization by declaring that if the unramified representation has normalized Satake
parameters $(\alpha_v,\beta_v)$ and the Satake transform of $h_v$ is the symmetric Laurent
polynomial $P_v(X,Y)$, then

$$
\operatorname{tr}\pi_v(h_v)=P_v(\alpha_v,\beta_v).
\tag{7.6}
$$

This declaration incorporates the $\delta_B^{1/2}$ normalization. For the standard generator
whose Satake transform is $X+Y$, the eigenvalue is $\alpha_v+\beta_v$. Writing a raw double
coset without specifying its $q_v^{1/2}$ factor would leave (7.6) ambiguous.

## 8. Eisenstein wave packets and the continuous channel

### 8.1 Normalized induction recalled

Choose unitary idele class characters $\chi_1,\chi_2$ satisfying $\chi_1\chi_2=\omega$. A section
of $I(\chi,s)$ obeys

$$
f_s\!\left(n(x)\begin{pmatrix}a&0\\0&d\end{pmatrix}g\right)
=\chi_1(a)\chi_2(d)
\left|\frac ad\right|_{\mathbf A}^{s+1/2}f_s(g).
\tag{8.1}
$$

The half-density makes $s=it$ the unitary axis. The associated Eisenstein series is initially

$$
E(g,f_s)=\sum_{\gamma\in B(F)\backslash G(F)}f_s(\gamma g)
\tag{8.2}
$$

for $\operatorname{Re}(s)>1/2$ and continues meromorphically to the axis. Its constant term is

$$
E_N(g,f_s)=f_s(g)+M(\chi,s)f_s(g),
\tag{8.3}
$$

where $M(\chi,s):I(\chi,s)\to I(w\chi,-s)$ is the global intertwining operator. An individual
$E(g,f_{it})$ is not square-integrable. The actual continuous $L^2$ vectors are wave packets

$$
W_a(g)=\int_{\mathbf R}E(g,f_{it})a(t)\,dt
\tag{8.4}
$$

with rapidly decreasing amplitude, together with the corresponding discrete sum over compact
idele-class characters.

### 8.2 Convolution on genuine wave packets

The strongly cuspidal place in the main theorem is archimedean and its coefficient is Schwartz,
not compactly supported modulo the center. We must therefore begin on the unitary axis with
genuine $L^2$ wave packets, rather than convolving an individual Eisenstein series in its
off-axis convergence chamber. Truncate the Eisenstein sum and the outer $t$-integral in (8.4).
On these finite truncations, the Harish--Chandra Schwartz estimates, the kernel-admissible
majorant (1.5a), and the polynomial vertical bounds for Eisenstein series justify Fubini. After
the truncations are removed by dominated convergence, one obtains

$$
R_\omega(f)W_a(g)
=\int_{\mathbf R}
E\bigl(g,I(\chi,it)(f)f_{it}\bigr)a(t)\,dt.
\tag{8.5}
$$

For factorizable data, restricted tensor factorization gives the honest unitary operator

$$
I(\chi,it)(f)=\bigotimes_v I_v(\chi_v,it)(f_v).
\tag{8.6}
$$

The $v_0$ factor is zero by the unitary-axis assertion of Theorem 4.2. Hence

$$
I(\chi,it)(f)=0
\quad\text{for every }t\in\mathbf R,
\qquad
R_\omega(f)W_a=0.
\tag{8.7}
$$

This proof uses neither a regularized nonunitary local action nor pointwise convolution of a
non-square-integrable Eisenstein family. If the strongly cuspidal factor were compactly
supported modulo the center, convolution in the initial chamber and meromorphic continuation
would give the same unitary-axis conclusion, but that stronger route is not available for the
archimedean coefficient used here.

### 8.3 Vanishing on the unitary axis

Equation (8.7) says directly that every rapidly decreasing unitary wave packet is killed:

$$
R_\omega(f)W_a=0.
\tag{8.8}
$$

Finite sums of such packets are dense in the nonresidual continuous subspace at each fixed level
and finite compact type. Since $R_\omega(f)$ is bounded, it vanishes on the closure. Exhausting
the finite data shows that it vanishes on the whole continuous subspace met by the test.

The repetition of the zero in (8.8) emphasizes the topology: (8.7) proves the identity on a
dense set of packets, and boundedness passes it to their closed span. No trace or Hilbert-space
operator is assigned to a single Eisenstein series.

### 8.4 Vanishing of the continuous trace distribution

A rank-one regularized spectral formula packages its continuous part using the scattering
operator. Depending on parametrization, its terms have the schematic form

$$
\int_{\mathbf R}
\operatorname{tr}\!\left(
Q(\chi,it)I(\chi,it)(f)
\right)dt,
\tag{8.9}
$$

where $Q$ is assembled from the normalized intertwiner, its derivative, and finite Weyl-group
symmetries. Fixed level and type make the displayed trace finite-dimensional.

Equation (8.7) makes $I(\chi,it)(f)$ the zero operator, so the integrand in (8.9) is identically
zero. Therefore

$$
I_{\mathrm{cont},\omega}(f)=0.
\tag{8.10}
$$

This conclusion is independent of the scalar used to normalize $M$: changing that scalar changes
$Q$ but leaves its product with the zero induced operator equal to zero. Normalized induction is
nevertheless retained because it fixes the unitary axis and the residual pole locations.

## 9. Residues and their annihilation

### 9.1 The residual characters

The rank-one constant-term analysis shows that every pole crossed in moving an Eisenstein
family from the convergence chamber to the unitary axis is simple and satisfies

$$
\chi_1\chi_2^{-1}|\cdot|^{2s_0}=|\cdot|.
\tag{9.1}
$$

Writing $\chi_1\chi_2^{-1}=|\cdot|^{i\tau}$ gives $s_0=(1-i\tau)/2$. The residue is a scalar
multiple of

$$
r_\eta(g)=\eta(\det g),
\qquad
\eta=\chi_1|\cdot|^{-i\tau/2}
=\chi_2|\cdot|^{i\tau/2},
\tag{9.2}
$$

and $\eta^2=\omega$. Since $\eta$ is unitary and $[\overline G]$ has finite volume, $r_\eta$
belongs to $L^2_\omega$. Its unipotent constant term is itself, so it is not cuspidal. The
residual space is the Hilbert sum of the lines $\mathbf C(\eta\circ\det)$.

### 9.2 Why residues require a separate proof

If the strongly cuspidal factor were compactly supported modulo the center, convolution would
give a zero meromorphic Eisenstein family and one could take its Laurent coefficient at $s_0$.
That is not the argument available here. For an archimedean Schwartz coefficient, (8.7) is an
identity only for honest unitary-axis operators on wave packets; it is not an identity of
off-axis meromorphic automorphic families. Formally specializing it at a nonunitary
reducibility point would be especially dangerous, because the corresponding principal series
can contain the discrete series from which the coefficient was formed.

Thus unitary-axis vanishing alone does not dispose of poles crossed in the contour motion. The
residual lines must be evaluated directly. This is not a loss of strength: they are
one-dimensional, so their convolution operators are explicit scalars.

### 9.3 Direct constant-term proof

A residual character $r_\eta=\eta\circ\det$ is one-dimensional. Its global convolution
operator is multiplication by the restricted product of its local scalars. At the selected
place the scalar is computed in the compact-picture order

$$
\lambda_{v_0}
=\int_{Z_{v_0}\backslash T_{v_0}}
\xi_{\eta,v_0}(t) f_{v_0}^B(t)\,dt,
\tag{9.3}
$$

where $\xi_{\eta,v_0}$ is the normalized torus character whose one-dimensional quotient is
$\eta_{v_0}\circ\det$. To obtain (9.3), average first over $K_{v_0}$ and $N_{v_0}$ in the order
used in (4.5), and only then take the outer torus Mellin integral. This order is the definition
of the Schwartz-algebra action if an absolute group integral is unavailable; for the
kernel-admissible tests of Theorem 10.1 it also agrees with ordinary absolutely convergent
convolution. Strong cuspidality gives $f_{v_0}^B=0$, so $\lambda_{v_0}=0$ before the outer
integral is taken.

The central transformations are compatible because $\eta_{v_0}^2=\omega_{v_0}$, so the
integrand descends to $Z_{v_0}\backslash T_{v_0}$. Restricted tensor factorization now supplies
one zero local factor and hence

$$
R_\omega(f)|_{L^2_{\mathrm{res},\omega}}=0,
\qquad
I_{\mathrm{res},\omega}(f)=0.
\tag{9.4}
$$

### 9.4 No omitted discrete noncuspidal term

The classification of the noncuspidal spectrum is essential. Orthogonality to continuous
unitary-axis packets alone would not rule out an isolated noncuspidal summand. In rank one every
such square-integrable summand is one of the determinant characters (9.2). Once (8.10) and (9.4)
are proved, there is no fourth spectral channel hidden between the continuous and cuspidal
pieces.

This conclusion uses exactly the global constant-term theorem: pseudo-Eisenstein series span the
orthogonal complement of cusp forms, Mellin inversion produces unitary Eisenstein packets, and
contour motion adds only the residues (9.2). No general spectral measure for the whole quotient
is required.

## 10. The selected cuspidal spectral formula

### 10.1 One local discrete-series selector

Let $D$ be an irreducible discrete-series representation of $G(F_{v_0})$ with central character
$\omega_{v_0}$, and let $f_D$ be the normalized pseudo-coefficient (5.2). Put
$f=f_D\otimes f^{v_0}$, with $f^{v_0}$ satisfying the finite-level and finite-type hypotheses of
the kernel theorem.

For a cuspidal automorphic representation $\pi$,

$$
\operatorname{tr}\pi(f)
=\operatorname{tr}\pi_{v_0}(f_D)\,
\operatorname{tr}\pi^{v_0}(f^{v_0}).
\tag{10.1}
$$

The first factor is $1$ if $\pi_{v_0}\simeq D$ and $0$ otherwise. Therefore

$$
I_{\mathrm{cusp},\omega}(f)
=\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_{v_0}\simeq D}}
m(\pi)\operatorname{tr}\pi^{v_0}(f^{v_0}).
\tag{10.2}
$$

Absolute convergence of the unrestricted series implies absolute convergence of the selected
subseries. Selection is literal deletion of zero terms, not a conditionally convergent
projection.

### 10.2 Several selector places

Suppose $S_{\mathrm{sel}}$ is a finite set of places and, for each $v\in S_{\mathrm{sel}}$, choose
a square-integrable representation $D_v$ and its normalized coefficient $f_{D_v}$. Assume at
least one of these places is the real place required by the global kernel theorem, and that all
archimedean factors are kernel-admissible. Then

$$
I_{\mathrm{spec},\omega}(f)
=\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_v\simeq D_v\ \text{for every }v\in S_{\mathrm{sel}}}}
m(\pi)\prod_{w\notin S_{\mathrm{sel}}}
\operatorname{tr}\pi_w(f_w).
\tag{10.3}
$$

The product means the finite product obtained after suppressing distinguished spherical lines.
Each additional selector imposes one exact local isomorphism condition. The continuous and
residual terms were already killed by any one strongly cuspidal factor.

### 10.3 Finite linear combinations

Let

$$
f_{v_0}=\sum_{j=1}^r c_j f_{D_j,u_j}
\tag{10.4}
$$

for pairwise inequivalent discrete series $D_j$ with the prescribed central character. Then

$$
\operatorname{tr}\sigma(f_{v_0})
=\begin{cases}
c_j,&\sigma\simeq D_j,\\
0,&\sigma\not\simeq D_j\text{ for all }j.
\end{cases}
\tag{10.5}
$$

Linearity gives

$$
I_{\mathrm{spec},\omega}(f)
=\sum_{j=1}^r c_j
\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_{v_0}\simeq D_j}}
m(\pi)\operatorname{tr}\pi^{v_0}(f^{v_0}).
\tag{10.6}
$$

Every summand in (10.4) is strongly cuspidal, so the noncuspidal terms still vanish at operator
level.

### 10.4 The complete spectral theorem

**Theorem 10.1 (cuspidal spectral side with a pseudo-coefficient).** Let $F$ be a number field
with real place $v_0$, let $\omega$ be a unitary idele class character, and let $D$ be an
irreducible discrete-series representation of $\mathrm{GL}_2(F_{v_0})$ with central character
$\omega_{v_0}$. Form its pseudo-coefficient $f_D$ by (5.2), using the local quotient measure
induced from the global ledger. Assume $f_D$, and every other archimedean factor, satisfies the
kernel-admissible estimate (1.5a) for the standing $Q$. Let $f=f_D\otimes f^{v_0}$ be a
finite-level, left-right compact-finite test function, spherical almost everywhere. Then:

1. $R_\omega(f)$ is trace class on $L^2_\omega$.
2. It acts by zero on the continuous and residual subspaces.
3. Its spectral distribution is

   $$
   \boxed{
   I_{\mathrm{spec},\omega}(f)
   =\operatorname{tr}R_\omega(f)
   =\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
                     \pi_{v_0}\simeq D}}
   m(\pi)\operatorname{tr}\pi^{v_0}(f^{v_0}).}
   \tag{10.7}
   $$

4. The series in (10.7) converges absolutely.
5. For factorizable $f^{v_0}$, each summand factors into the finite product of local traces in
   (7.2), with spherical factors normalized by (7.6).

**Proof.** The pseudo-coefficient is compact-finite and strongly cuspidal by Chapter 5, and the
explicit kernel-admissibility hypothesis supplies the extra decay required by the kernel
theorem. That theorem gives
trace class and the absolutely convergent cuspidal expansion. Chapters 8 and 9 prove operator
vanishing on the continuous and residual subspaces. The local trace identity (5.5) and the
finite tensor trace lemma turn the cuspidal expansion into (10.7). $\square$

The theorem computes the spectral side without using a geometric expansion. The equality of
(10.7) with central and elliptic orbital distributions is supplied by the kernel theorem, while
evaluation and matching of those orbital integrals belong to the geometric and local-transfer
stages.

## 11. Spectral computations with finite-place tests

### 11.1 Level projectors

The archimedean pseudo-coefficient fixes the infinite component. Finite-place factors refine the
remaining sum by level and Hecke data. Let $J_v\subset G(F_v)$ be compact open, compatible with
the local central character, and use the normalized idempotent $e_{J_v}$. Proposition 3.1 gives

$$
\operatorname{tr}\pi_v(e_{J_v})=\dim\pi_v^{J_v}.
\tag{11.1}
$$

Consequently, if $S$ is a finite set containing $v_0$ and

$$
f=f_D\otimes\bigotimes_{v\in S\setminus\{v_0\}}e_{J_v}
\otimes\bigotimes_{v\notin S}e_{K_v},
\tag{11.2}
$$

then

$$
I_{\mathrm{spec},\omega}(f)
=\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_{v_0}\simeq D\\
\pi_v\text{ unramified for every }v\notin S}}
m(\pi)
\prod_{v\in S\setminus\{v_0\}}\dim\pi_v^{J_v},
\tag{11.3}
$$

where representations ramified outside $S$ contribute zero through a spherical projector.

Formula (11.3) counts automorphic copies with the dimension of their chosen level subspace. It
does not count representations merely once. Even when $m(\pi)=1$, an old representation can
have $\dim\pi_v^{J_v}>1$ at deeper level. The automorphic multiplicity and the level dimension
must both remain visible.

The proof is immediate from (10.7) and (11.1), but its interpretation is worth emphasizing.
An idempotent is a projector, not a primitive selector. It selects all representations with
$J_v$-fixed vectors and weights each by the dimension of that fixed space.

### 11.2 Spherical Hecke operators

At an unramified finite place, insert a spherical Hecke function $h_v$ with Satake transform
$P_v$. For an unramified local component with normalized Satake parameters
$(\alpha_v,\beta_v)$, equation (7.6) gives

$$
\operatorname{tr}\pi_v(h_v)=P_v(\alpha_v,\beta_v).
\tag{11.4}
$$

If $h_v$ is the standard generator normalized to have Satake transform $X+Y$, let $S$ contain
$v_0$, $v$, and every place where the remaining test is not spherical, and put
$S'=S\setminus\{v_0,v\}$. The global distribution becomes

$$
\sum_{\substack{\pi\ \mathrm{cuspidal}\\
\pi_{v_0}\simeq D\\
\pi_w\text{ unramified for every }w\notin S}}
m(\pi)(\alpha_v(\pi)+\beta_v(\pi))
\prod_{w\in S'}\operatorname{tr}\pi_w(f_w),
\tag{11.5}
$$

Thus the trace formula computes a weighted sum of Hecke eigenvalues in the selected
archimedean packet; components ramified where the test is spherical contribute zero.

If several spherical Hecke factors are inserted, their eigenvalues multiply. A finite linear
combination of such tests therefore evaluates any polynomial in finitely many normalized Hecke
eigenvalues. There is no convergence issue in this multiplication: only finitely many places
have been changed from their identity projectors.

One must not identify $\alpha_v+\beta_v$ with the eigenvalue of an unnormalized characteristic
function without calculating the Satake transform. Depending on the chosen double-coset measure,
a power of $q_v^{1/2}$ can intervene. Equation (11.4) is the normalization-safe statement.

### 11.3 Ramified matrix coefficients

At a nonarchimedean place $w$, let $\sigma_w$ be supercuspidal with central character
$\omega_w$, choose a unit vector $u_w$, and form $f_{\sigma_w,u_w}$ as in (5.2). Then a global
test containing both $f_D$ at $v_0$ and $f_{\sigma_w,u_w}$ at $w$ has spectral side

$$
\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_{v_0}\simeq D,\ \pi_w\simeq\sigma_w}}
m(\pi)\prod_{v\notin\{v_0,w\}}
\operatorname{tr}\pi_v(f_v).
\tag{11.6}
$$

This provides exact type selection at $w$, rather than the coarser condition that a compact type
or level occur. The finite-place coefficient is itself strongly cuspidal, but the global kernel
theorem still uses the real selector $f_D$ to meet its stated hypotheses.

If one uses an arbitrary matrix coefficient without the formal-degree factor, the same set of
representations is selected but every surviving global term is multiplied by
$d(\sigma_w)^{-1}$. This scalar would be especially damaging in a comparison of two groups.
The normalized coefficient removes it at the source.

### 11.4 A weight and level example

Take $F=\mathbf Q$, trivial central character, and let $D_k$ be the full real discrete series of
compatible even lowest weight. Choose $k$ sufficiently high that its normalized compact-finite
coefficient $f_{D_k}$ satisfies the standing kernel-admissible estimate. (The local selector
identity itself holds already for every $k\geq2$; the high-weight condition is what licenses the
global trace-class formula used in this example.)
Choose the full-level spherical projector at every finite prime. Then

$$
I_{\mathrm{spec}}(f)
=\sum_{\substack{\pi\ \mathrm{cuspidal}\\
\pi_\infty\simeq D_k\\
\pi_p\text{ unramified for every }p}}
m(\pi).
\tag{11.7}
$$

If a normalized spherical Hecke generator is inserted at a prime $p$, this becomes

$$
\sum_{\substack{\pi\ \mathrm{cuspidal}\\
\pi_\infty\simeq D_k\\
\pi_q\text{ unramified for every }q}}
m(\pi)(\alpha_p(\pi)+\beta_p(\pi)).
\tag{11.8}
$$

At a congruence level, replacing some full-level projectors by $e_{J_p}$ weights a representation
by the dimension of its local invariant space. Formula (11.8) is therefore a spectral count
with precisely declared weight, level, and Hecke normalization. It should not be paraphrased as
“the number of modular forms” until one also specifies the relationship between adelic
representations, classical components, old spaces, and any multiplicity-one input.

The example also illustrates why the full real group convention matters. The chosen $D_k$
already packages the two orientations of the connected symmetric space. No additional factor
of two belongs in (11.7).

## 12. Compatibility with local transfer

### 12.1 What compatibility requires

A later trace comparison will place a test function $f_v$ on $G(F_v)$ beside a function on an
inner form. Spectral compatibility is not merely the assertion that both functions are called
pseudo-coefficients. Four pieces of data must agree:

1. the identification of central characters;
2. the Haar measures used in local convolution and formal degree;
3. the sign convention in the local character or orbital-integral identity;
4. the normalization of traces on the representations paired by transfer.

The present book fixes the source side. Its normalized selector always has trace $+1$ on the
chosen $G(F_v)$ representation. If a later transfer convention contains a sign, that sign must
be recorded in the matching relation or in the target test function. It must not be silently
inserted into the definition of $m(\pi)$ or into the global trace.

No existence theorem for matching functions is needed for the spectral result proved here. The
purpose of this chapter is to specify the interface that such a theorem must satisfy.

### 12.2 Measure rescaling

Let $G'_v$ be a local inner form with quotient measure $d\bar g'_v$, and let $D'$ be the
representation intended to correspond to $D$. Suppose both pseudo-coefficients are normalized by
their respective formal degrees. Then

$$
\operatorname{tr}D(f_D)=1,
\qquad
\operatorname{tr}D'(f_{D'})=1.
\tag{12.1}
$$

If either Haar measure is rescaled, its formal degree and pseudo-coefficient rescale inversely by
(5.6), so (12.1) remains true. Thus unit spectral trace is invariant under a consistent measure
change.

Orbital integrals behave differently: rescaling a centralizer measure rescales the centralizer
volume and orbital quotient measure inversely, whereas rescaling the ambient group measure also
changes the convolution measure. A matching theorem must therefore state both ambient and
centralizer measures. The spectral normalization (12.1) alone cannot repair a mismatch on the
geometric side.

### 12.3 Spectral normalization of matching functions

Let $\mathcal T_v$ be a proposed local correspondence between selected irreducible
representations of $G_v$ and $G'_v$. A transfer convention is spectrally normalized if matched
test functions satisfy

$$
\operatorname{tr}\pi_v(f_v)
=\operatorname{tr}\mathcal T_v(\pi_v)(f'_v)
\tag{12.2}
$$

for every representation in the range under consideration. If the geometric matching convention
naturally yields a sign $\epsilon_v(\pi_v)\in\{\pm1\}$, one may instead define the target test
so that

$$
\operatorname{tr}\mathcal T_v(\pi_v)(f'_v)
=\epsilon_v(\pi_v)\operatorname{tr}\pi_v(f_v).
\tag{12.3}
$$

The choice between (12.2) and (12.3) is harmless only when it is declared and used on both the
spectral and geometric sides. Our source pseudo-coefficient contributes $+1$; hence the local
factor on the right of (12.2) is $+1$, while in (12.3) it is the displayed sign.

For a finite set $S$ of transfer places, the global tensor trace then picks up the product of the
local signs:

$$
\operatorname{tr}\pi'(f')
=\left(\prod_{v\in S}\epsilon_v(\pi_v)\right)
\operatorname{tr}\pi(f),
\tag{12.4}
$$

provided the remaining local traces agree. This is just Lemma 7.1. There is no further global
formal-degree factor.

### 12.4 A transfer-ready ledger

The data exported from the spectral formula are therefore these.

| Feature                             | Transfer-ready convention                            |
| ----------------------------------- | ---------------------------------------------------- |
| Central character of representation | $\omega_v$                                           |
| Central character of test           | $\omega_v^{-1}$                                      |
| Local convolution domain            | $Z_v\backslash G_v$                                  |
| Selector                            | $d(D)\overline{\langle D(g)u,u\rangle}$              |
| Selector trace on $D$               | $+1$                                                 |
| Trace on other unitary irreducibles | $0$ for the kernel-admissible selector used globally |
| Induced operator                    | Zero on every unitary-axis principal series          |
| Spherical projector trace           | $1$ on the spherical line                            |
| Hecke eigenvalue                    | Normalized Satake polynomial                         |
| Global weight                       | $m(\pi)\prod_v\operatorname{tr}\pi_v(f_v)$           |
| Transfer sign                       | Explicit local factor, never hidden in $m(\pi)$      |
| Haar change                         | Compensated by inverse formal-degree scaling         |

This ledger is the sense in which (10.7) is compatible with local transfer. It supplies an exact
spectral input to a later matching theorem while making no premature assertion about orbital
integrals or the existence of matching functions.

## 13. Continuity, regrouping, and stability

### 13.1 Continuity of the distribution

On a fixed finite-level, finite-type kernel-admissible space with the standing strongly
cuspidal real block, the kernel theorem provides a seminorm $\nu$ such that

$$
\|R_\omega(f)\|_1\leq C\nu(f).
\tag{13.1}
$$

Therefore

$$
|I_{\mathrm{spec},\omega}(f)|
\leq\|R_\omega(f)\|_1
\leq C\nu(f).
\tag{13.2}
$$

The selected cuspidal spectral side is a continuous distribution. If $f_n\to f$ in that
Schwartz topology, then $R_\omega(f_n)\to R_\omega(f)$ in trace norm and

$$
I_{\mathrm{spec},\omega}(f_n)
\longrightarrow I_{\mathrm{spec},\omega}(f).
\tag{13.3}
$$

This continuity statement applies to a net that already remains inside the same
kernel-admissible, strongly cuspidal block. It does not construct compactly supported
approximants to an archimedean discrete-series coefficient: arbitrary cutoffs can create a
nonzero constant term, and no cuspidal projection with the required topology has been assumed
or constructed here.

### 13.2 Legitimate regrouping

Absolute convergence (6.5) permits the spectral sum to be partitioned by any countable local
label: the isomorphism class of $\pi_{v_0}$, a finite-place inertial type, a compact type, or the
eigenvalue of a chosen finite collection of Hecke operators. For a partition
$\mathcal A_{\mathrm{cusp}}=\bigsqcup_j\mathcal A_j$,

$$
I_{\mathrm{cusp},\omega}(f)
=\sum_j\sum_{\pi\in\mathcal A_j}
m(\pi)\operatorname{tr}\pi(f),
\tag{13.4}
$$

and both the inner sums and the outer sum converge absolutely.

This justifies packetwise regrouping once a packet relation has been defined. It does not
identify distinct terms or prove that their multiplicities agree. Regrouping is analytic;
comparison of coefficients is arithmetic or representation-theoretic.

### 13.3 Independence from the chosen coefficient

Let $u,u'$ be two compact-finite unit vectors in the same square-integrable $D$. For every
cuspidal automorphic $\pi$,

$$
\operatorname{tr}\pi_{v_0}(f_{D,u}-f_{D,u'})=0
\tag{13.5}
$$

by Theorem 5.1. Both functions are strongly cuspidal, so both kill the noncuspidal space. Hence,
for every fixed $f^{v_0}$,

$$
I_{\mathrm{spec},\omega}
\bigl((f_{D,u}-f_{D,u'})\otimes f^{v_0}\bigr)=0.
\tag{13.6}
$$

Thus the selected spectral distribution depends only on $D$, not on the unit vector used to
realize its selector. This does not imply equality of the two automorphic kernels or of their
individual orbital integrals. Their geometric expansions have equal total value, with possible
cancellation among classes.

### 13.4 Change of central realization

The norm-one quotient

$$
G(F)\backslash G(\mathbf A)^1
$$

contains the compact central group $F^\times\backslash\mathbf A^1$. Fourier decomposition under
that compact center gives character spaces equivalent to the fixed-$\omega$ realization on
$[\overline G]$. Probability measure on the compact central fiber makes the equivalence unitary.

Under this equivalence, convolution by an inverse-central-character test, cuspidality, the
automorphic multiplicities, and every local trace in (10.7) remain unchanged. Only the removed
scalar module direction is described differently. Therefore the selected formula may be read in
either realization, but its central Haar measure must not be counted a second time.

## 14. Failure modes and exact boundaries

### 14.1 Trace zero is not operator zero

The equation

$$
\operatorname{tr}I_v(\chi_v,s)(f_v)=0
$$

does not imply $I_v(\chi_v,s)(f_v)=0$. It therefore does not by itself kill scattering terms,
or the constant term of a two-variable automorphic kernel. The repair for the continuous
channel is the two-sided condition (4.1), which gives the zero unitary induced operator through
(4.4). Residual one-dimensional operators are then killed separately by the transform
$f_v^B=0$ as in (9.3).

Conversely, if a trace formula has already been regularized and every continuous summand is
known to involve only the ordinary induced trace, then $f_v^B=0$ can suffice. That weaker
situation is not used in Theorem 10.1.

### 14.2 A pseudo-coefficient is not a central idempotent

The operator $D(f_{D,u})$ is a rank-one projector, but the function $f_{D,u}$ is generally not
an idempotent under convolution and is not central in the test algebra. On another copy of $D$
it selects the corresponding line determined by $u$; on the character quotient it has trace one.

A central pseudo-coefficient, when available in a suitable quotient of the test algebra, is a
different object. Nothing in the global trace computation requires centrality. Confusing the
two notions can lead to the false claim that $f_D$ acts as the identity on the whole
infinite-dimensional representation $D$.

### 14.3 Finite multiplicity is not multiplicity one

The established decomposition proves

$$
1\leq m(\pi)<\infty,
$$

not $m(\pi)=1$. The pseudo-coefficient identifies a local component but says nothing about the
number of global embeddings with that component. Schur orthogonality is local and cannot remove
a global multiplicity space.

Accordingly every theorem in this book retains $m(\pi)$. If a later result proves multiplicity
one under matching hypotheses, it may specialize the formulas by replacing $m(\pi)$ with one.
Doing so here would create a dependency on an unproved later theorem.

### 14.4 The limits of the present computation

The present spectral theorem assumes the exact test class of the simple kernel formula: finite
sums of factorizable, finite-level, compact-finite functions, kernel-admissible at every
archimedean place, with a strongly cuspidal real factor. It does not claim trace class for every
Harish--Chandra Schwartz function on the full group. Without the fixed algebraic decay power,
the periodization estimate used by the kernel theorem is unavailable; without finite compact
type, an additional summation over types is needed; without a cuspidal factor, continuous terms
require truncation and regularization.

The book also does not evaluate local orbital integrals, prove existence of transfers, classify
rational elliptic conjugacy classes, or establish a global comparison with an inner form. Those
are geometric and local-matching problems. What is complete here is the source spectral
distribution, including all multiplicities, local trace factors, and zero noncuspidal terms.

Several boundary cases deserve explicit mention.

- A limit of discrete series need not be square-integrable modulo the center, so construction
  (5.2) and Schur orthogonality do not apply unchanged.
- A low-weight discrete-series coefficient is a valid local tempered pseudo-coefficient but may
  fail the fixed kernel-admissibility threshold. The global trace-class theorem includes it
  only if (1.5a) is verified independently; sufficiently high weights are supplied by the
  preceding kernel analysis.
- At a complex place $\mathrm{GL}_2(\mathbf C)$ has no discrete series modulo center. Such a
  place cannot supply the real pseudo-coefficient used by the kernel theorem.
- A nonunitary central character does not define the unitary Hilbert-space decomposition used in
  (6.1).
- An infinite sum of pseudo-coefficients requires its own convergence theorem; only finite sums
  are included here.
- A raw double-coset characteristic function has no intrinsic Satake eigenvalue until its Haar
  and half-density normalization are stated.

These are genuine hypothesis boundaries, not missing cases concealed by notation.

## 15. Final synthesis

### 15.1 The implication chain

The spectral computation is one continuous chain:

$$
\begin{aligned}
&\text{square-integrability modulo the center}
+\text{fixed quotient Haar measure}\\
&\qquad\Longrightarrow
\text{Schur orthogonality and formal degree},\\[2mm]
&\text{formal-degree-normalized coefficient}
+\text{zero Jacquet module}\\
&\qquad\Longrightarrow
\text{trace-one pseudo-coefficient and strong cuspidality},\\[2mm]
&\text{strong local cuspidality}
+\text{restricted tensor factorization}\\
&\qquad\Longrightarrow
I(\chi,it)(f)=0,\\[2mm]
&I(\chi,it)(f)=0
+\text{unitary wave-packet density}\\
&\qquad\Longrightarrow
I_{\mathrm{cont},\omega}(f)=0,\\[2mm]
&f_{v_0}^B=0
+\text{residual-character classification}\\
&\qquad\Longrightarrow
I_{\mathrm{res},\omega}(f)=0,\\[2mm]
&\text{cuspidal kernel trace class}
+\text{discrete finite-multiplicity decomposition}\\
&\qquad\Longrightarrow
\sum_\pi m(\pi)\operatorname{tr}\pi(f)
\text{ absolutely convergent},\\[2mm]
&\text{local selector identity}
+\text{finite tensor trace lemma}\\
&\qquad\Longrightarrow
\sum_{\pi_{v_0}\simeq D}
m(\pi)\operatorname{tr}\pi^{v_0}(f^{v_0}).
\end{aligned}
\tag{15.1}
$$

Each arrow uses a different theorem. Formal degree fixes a local scalar; strong cuspidality kills
operators; Eisenstein theory identifies every noncuspidal vector; trace class supplies absolute
global summability; and restricted tensor products expose the local weights.

### 15.2 The reusable spectral package

**Theorem 15.1 (transfer-ready cuspidal spectral package).** Under the hypotheses of Theorem
10.1, let $S$ contain every archimedean place and every finite place where the test is not the
normalized spherical projector. Then

$$
\boxed{
I_{\mathrm{spec},\omega}(f)
=I_{\mathrm{cusp},\omega}(f)
=\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_{v_0}\simeq D\\
\pi_v\text{ unramified for every }v\notin S}}
m(\pi)
\prod_{v\in S\setminus\{v_0\}}
\operatorname{tr}\pi_v(f_v),}
\tag{15.2}
$$

and

$$
I_{\mathrm{cont},\omega}(f)=0,
\qquad
I_{\mathrm{res},\omega}(f)=0.
\tag{15.3}
$$

Representations ramified outside $S$ have already contributed zero through an outside spherical
projector, which is why the displayed restriction is necessary. The sum in (15.2) is
absolutely convergent and is unchanged if $S$ is enlarged. The local
selector has trace $+1$, spherical projectors have trace one on spherical lines, Hecke traces are
normalized Satake polynomials, and all automorphic multiplicities remain explicit. A consistent
Haar rescaling changes the formal degree and the selector inversely, leaving every local and
global trace unchanged.

**Proof.** Equations (8.10) and (9.4) prove (15.3). Theorem 10.1 gives the selected absolutely
convergent cuspidal sum. An outside spherical projector kills every representation ramified
outside $S$; for each survivor, $S$ now contains every ramified place, so Lemma 7.1 factors the
term and proves invariance under enlarging $S$. The measure,
spherical, and Satake assertions are (5.6), (7.5), and (7.6). $\square$

### 15.3 Conclusion

The cuspidal spectral side of the simple $\mathrm{GL}_2$ trace formula is now an explicitly
weighted and absolutely convergent distribution. Its construction begins locally. A
formal-degree-normalized square-integrable matrix coefficient is simultaneously a spectral
selector and a strongly cuspidal test function. Schur orthogonality gives trace one on the chosen
discrete series and zero on every other discrete representation; the vanished two-sided
constant term gives the zero operator on every unitary principal-series representation, and on
the honest complementary-series actions needed for the local selector theorem.

That local zero propagates through the global tensor product on the unitary axis and kills every
genuine Eisenstein wave packet. Independently, the vanishing parabolic transform kills every
residual determinant character by a direct one-dimensional calculation. The constant-term
classification proves that these exhaust the noncuspidal spectrum, so their disappearance is a
theorem rather than an omission from the final notation.

On the surviving cuspidal Hilbert sum, trace class justifies absolute summation and preserves the
finite automorphic multiplicity $m(\pi)$. Restricted tensor products reduce each adelic trace to
a finite product of local traces. The real pseudo-coefficient becomes an indicator of the chosen
discrete series, compact idempotents contribute dimensions of fixed spaces, and spherical Hecke
functions contribute their normalized Satake polynomials.

The final formula is consequently ready for comparison: central characters are inverse on tests,
formal degrees use the convolution measures, selector traces equal $+1$, transfer signs must be
displayed locally, and no hidden scalar or unproved multiplicity-one assertion remains. This is
the complete cuspidal spectral package needed to place the $\mathrm{GL}_2$ side beside an inner
form once the geometric orbital integrals and matching functions have been constructed.
