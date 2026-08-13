# One-Prime Nonminimal Patching and R=T

## Contents

1. [The exact one-prime problem](#1-the-exact-one-prime-problem)
   - [What changes at the fixed prime](#11-what-changes-at-the-fixed-prime)
   - [Why a minimal equality does not settle the problem](#12-why-a-minimal-equality-does-not-settle-the-problem)
   - [What the available inputs prove](#13-what-the-available-inputs-prove)
2. [Arithmetic datum and conventions](#2-arithmetic-datum-and-conventions)
   - [Global deformation data](#21-global-deformation-data)
   - [The scalar tame place](#22-the-scalar-tame-place)
   - [Automorphic and patching hypotheses](#23-automorphic-and-patching-hypotheses)
   - [The one-prime boundary](#24-the-one-prime-boundary)
3. [The exact output of the type-complex theorem](#3-the-exact-output-of-the-type-complex-theorem)
   - [The conductor-one line-special boundary](#31-the-conductor-one-line-special-boundary)
   - [The represented scalar-twist identities](#32-the-represented-scalar-twist-identities)
   - [Complexes, duality, and support](#33-complexes-duality-and-support)
   - [The Hecke-valued representation](#34-the-hecke-valued-representation)
4. [From support to the reduced comparison](#4-from-support-to-the-reduced-comparison)
   - [A kernel detected by a faithful carrier](#41-a-kernel-detected-by-a-faithful-carrier)
   - [The reduced one-prime theorem](#42-the-reduced-one-prime-theorem)
   - [The exact obstruction to full R=T](#43-the-exact-obstruction-to-full-rt)
   - [Why the tame direction cannot kill the obstruction](#44-why-the-tame-direction-cannot-kill-the-obstruction)
5. [What patching and augmentation do prove](#5-what-patching-and-augmentation-do-prove)
   - [The two-term complex and its Tor term](#51-the-two-term-complex-and-its-tor-term)
   - [Amplitude after Book 174](#52-amplitude-after-book-174)
   - [The conditional patched R=T criterion](#53-the-conditional-patched-rt-criterion)
   - [Fixed-prime and auxiliary augmentation](#54-fixed-prime-and-auxiliary-augmentation)
   - [Fixed characters and coefficient extension](#55-fixed-characters-and-coefficient-extension)
6. [Scalar and vexing branches](#6-scalar-and-vexing-branches)
   - [Why the scalar family forces q congruent to one](#61-why-the-scalar-family-forces-q-congruent-to-one)
   - [The line and sign at the colliding root](#62-the-line-and-sign-at-the-colliding-root)
   - [The signed Gram factor](#63-the-signed-gram-factor)
   - [The q congruent to minus one branch](#64-the-q-congruent-to-minus-one-branch)
7. [Automorphy of characteristic-zero points](#7-automorphy-of-characteristic-zero-points)
   - [Factoring a point through the reduced order](#71-factoring-a-point-through-the-reduced-order)
   - [Exact local type and the integral lattice](#72-exact-local-type-and-the-integral-lattice)
   - [Solvable descent](#73-solvable-descent)
8. [Dependency, circularity, and normalization audit](#8-dependency-circularity-and-normalization-audit)
   - [Direct prerequisite ledger](#81-direct-prerequisite-ledger)
   - [The first unsupported step in the full theorem](#82-the-first-unsupported-step-in-the-full-theorem)
   - [No finite-set or hidden-support argument](#83-no-finite-set-or-hidden-support-argument)
   - [Frobenius, determinant, and variance](#84-frobenius-determinant-and-variance)
9. [Conclusion](#9-conclusion)

## 1. The exact one-prime problem

### 1.1 What changes at the fixed prime

Let $F$ be totally real, let $\ell\geq 7$, and let

$$
\bar\rho:G_F\longrightarrow \operatorname{GL}_2(k)
\tag{1.1}
$$

be an absolutely irreducible, totally odd residual representation. The fixed-prime problem
studied here starts with a named conductor-one line-special condition at one place
$v\nmid\ell$. It then varies a scalar tame character of $\ell$-power order while preserving
the invariant line and the special monodromy relation. The represented closure includes the
zero-monodromy boundary; the characteristic-zero points to which the conductor statement is
applied have rank-one monodromy. The augmentation character is trivial and its special
parameter has conductor one. Every
retained nontrivial tame character has conductor one, and its scalar twist of a special
parameter has conductor two.

There are therefore two global deformation rings:

$$
R^{\mathrm{sp},1}
\quad\text{and}\quad
R_{\Lambda_v}^{\mathrm{sp},2},
\tag{1.2}
$$

where the first represents the conductor-one line-special problem and the second represents
the scalar-twist family over the tame group algebra $\Lambda_v$. The corresponding faithful
Hecke orders are

$$
\mathbb T^{\mathrm{sp},1}
\quad\text{and}\quad
\mathbb T_{\Lambda_v}^{\mathrm{sp},2}.
\tag{1.3}
$$

The superscript $2$ describes the nontrivial character fibers. It does not say that the
augmentation fiber has conductor two.

The task is not to patch an arbitrary collection of ramified primes. It is to compare these
four rings at one fixed scalar-twist place, using the one-prime type complex and its exact
augmentation.

### 1.2 Why a minimal equality does not settle the problem

The conductor-one ring in (1.2) is not the neutral minimal deformation ring. Its local datum
retains a special line, a sign, and the schematic closure of nonzero monodromy. At the scalar
residual point it also retains the unramified and tame Kummer directions in the base of the
line chart. Book 173's minimal theorem does not identify this ring with a Hecke algebra.

This distinction is structural. Book 170 shows that there is no automatic morphism between
an arbitrary unramified minimal condition and a sign-selected special condition. Such a map
exists only when an actual inclusion or intersection of represented deformation functors
provides it. Renaming the conductor-one line-special boundary as $R^{\min}$ does not create
that map.

Even if one had an equality at a genuine quotient, equality at one quotient would not kill a
kernel in the relative ring. For example, the surjection

$$
\mathcal O[[x]]/(x^2)\longrightarrow \mathcal O
\tag{1.4}
$$

becomes an isomorphism after quotienting by $(x)$, while its kernel is nonzero and nilpotent.
Generic points and one augmentation do not detect such a kernel.

### 1.3 What the available inputs prove

Under the explicitly named hypotheses recorded in Section 2.3, Book 174 proves full
topological support of the primary and companion type complexes on the named conductor-one
and conductor-two deformation rings. Book 170, under its separate clean trace-order
hypotheses, supplies the compatible Hecke-valued representation and hence the canonical
surjections to faithful Hecke images. These two conditional facts determine the finite-level
kernels up to nilpotents.

The result proved below is

$$
\bigl(R^{\mathrm{sp},1}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T^{\mathrm{sp},1},
\qquad
\bigl(R_{\Lambda_v}^{\mathrm{sp},2}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T_{\Lambda_v}^{\mathrm{sp},2}.
\tag{1.5}
$$

The same conclusion holds on every retained fixed-character fiber. Consequently every
characteristic-zero point on either the conductor-one face or a nontrivial conductor-two
fiber is automorphic, because a homomorphism to a discrete valuation ring kills nilpotents.

A full finite-level scheme-theoretic equality follows if the relevant global line-special
deformation ring is reduced. Likewise, the patched comparison is a full equality if the
actual patched deformation ring is reduced, or if an independent theorem kills the
annihilator scheme-theoretically. No prior book proves either nilpotent-control statement for
this scalar line-special global problem. The full $R=T$ assertion is therefore isolated as a
conditional criterion, not presented as an unconditional consequence of minimal patching.

## 2. Arithmetic datum and conventions

### 2.1 Global deformation data

Let $(\mathcal O,\varpi,k,E)$ be a complete discrete valuation ring, a uniformizer, its
finite residue field of characteristic $\ell$, and its fraction field. Assume

$$
\bar\rho|_{G_{F(\zeta_\ell)}}
\quad\text{is absolutely irreducible},
\tag{2.1}
$$

and

$$
H^0\bigl(F,\operatorname{ad}^0\bar\rho(1)\bigr)=0.
\tag{2.2}
$$

These are the image and dual-invariant hypotheses used by the preceding Taylor--Wiles
construction. Absolute irreducibility over $F$ alone is not substituted for (2.1).
Fix a totally odd determinant lift $\delta^{\mathrm{sp},1}$ compatible with the weight-two
central character and all named local conditions.

Fix a finite set $S$ containing the places above $\ell$, the places where $\bar\rho$ or the
determinant is ramified, and the selected place $v$. At every $w\mid\ell$, assume
$F_w/\mathbf Q_\ell$ is unramified and use the represented finite-flat condition of weights
$\{0,1\}$. Membership means membership on every Artinian quotient, not merely the presence
of the expected Hodge--Tate weights after inverting $\ell$.

At every $w\in S$ with $w\nmid\ell$ and $w\ne v$, choose one named represented condition for
which the preceding local type and reciprocity theorems apply. Outside $S$, impose the
unramified condition. Residual automorphy is required in the exact non-Eisenstein compact
parallel-weight-two realization used by Book 174. All global rings below use this fixed datum
and the same framing convention; changing that convention on only one side is not allowed.

### 2.2 The scalar tame place

Write $q_v$ for the residue cardinality at $v$. The augmentation face is an unramified
Steinberg twist: no additional ramified prime-to-$\ell$ scalar character is hidden in its
inertial label. The selected residual datum consists of an invariant line $L_v$, a sign
$\varepsilon_v\in\{1,-1\}$, and a nontrivial finite cyclic tame $\ell$-power quotient
$\Delta_v$. Put

$$
\Lambda_v=\mathcal O[\Delta_v],
\qquad
\epsilon_v:\Lambda_v\longrightarrow\mathcal O
\tag{2.3}
$$

for the group algebra and augmentation.

The scalar character must be part of a global ray character, not merely a formal local
symbol. Let $\boldsymbol\chi_v$ denote the resulting tautological character. A scalar twist
changes a two-dimensional determinant by its square, so the universal family has a determinant

$$
\delta_{\Lambda_v}:G_F\longrightarrow\Lambda_v^\times,
\qquad
\delta_{\Lambda_v}
=\delta^{\mathrm{sp},1}\boldsymbol\chi_v^2.
\tag{2.4}
$$

Each character specialization again has a fixed determinant. The determinant is not held
artificially constant while the scalar twist varies.

Use geometric Frobenius $\Phi_v$. If $\tau$ is a tame generator, then

$$
\Phi_v\tau\Phi_v^{-1}=\tau^{q_v^{-1}},
\qquad
\rho(\Phi_v)N\rho(\Phi_v)^{-1}=q_v^{-1}N.
\tag{2.5}
$$

Book 174 writes the corresponding calculation with arithmetic Frobenius. Passing from its
notation to (2.5) inverts Frobenius and the displayed $q_v$-power simultaneously.

The scalar-twist theorem is the branch

$$
q_v\equiv1\pmod\ell.
\tag{2.6}
$$

This congruence is forced by the existence of a nontrivial tame $\ell$-power scalar character.
It is not an exceptional case that can be removed while retaining the same family.

### 2.3 Automorphic and patching hypotheses

The words *clean*, *supported*, and *faithful* are conclusions or separately checkable
hypotheses in the preceding books; they are not abbreviations for residual automorphy. We use
the following named ledger.

**$({\rm AUT}_v)$ (the actual automorphic localization).** There is a nonzero,
non-Eisenstein, compact parallel-weight-two localization with the declared determinant,
central block, enhanced line, and $W_v$-sign. Its primary coefficient is the quotient
Steinberg lattice and its companion is the inverse-character augmentation lattice. Both are
finite free over $\mathcal O$, the pairing between them is perfect, and stabilizer descent is
either avoided by neatness or has order prime to $\ell$. Every characteristic-zero factor
used below is a noncharacter packet in the verified Galois-attachment and local--global
compatibility range. If the carrier is moved from the curve-new lattice to a switched definite
lattice, impose $({\rm AIH}_{\mathscr F})$, $({\rm PRI}_{\rm type})$, and
$({\rm NU}_{\rm type})$ for the actual type coefficients, together with Book 140's
node-uniformization, generic-support, and common-kernel hypotheses. These inputs identify the
two faithful orders; the normalized-branch Smith correction remains distinct from the Néron
component group. Equality of good residual traces is not a substitute for this datum.

**$({\rm AIH}_{\mathscr F})$ (constant-coefficient Ihara).** At every constant-coefficient
curve in the actual finite flag diagram, including all tame and auxiliary spectator levels,
Book 139's localized group

$$
\left(H^1_{\rm nc}(\Gamma_D^v,k)^{\Delta_D}\right)_{\mathfrak m_D}
\tag{2.7}
$$

vanishes. Book 139 proves saturation and its corrected component filtration only after these
vanishings are supplied. Non-Eisenstein localization and strong approximation do not prove
them.

**$({\rm TYPE}_v)$ (the typed complex).** Book 174's independent hypotheses
$({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$ hold on every retained finite shadow.
The first says that the quotient-primary and augmentation-companion sheaves extend through the
actual incidence model, their flag resolutions and component routing are exact, and pull and
norm have the declared inverse-character adjunction. The second says that, for every actual
crossed-coefficient object $\overline W$ in the flag diagram,

$$
\ker\!\left(
H^1(\Gamma_{D,0}^v,\overline W)\oplus
H^1(\Gamma_{D,1}^v,\overline W)
\longrightarrow H^1(\Gamma_{D,e}^v,\overline W)
\right)_{\mathfrak m_D}^{\Delta_D}=0.
\tag{2.8}
$$

Book 174 then proves that the primary and companion pull maps are split injections over the
combined fixed-prime and auxiliary coefficient algebra. The constant-coefficient hypothesis
(2.7) does not imply (2.8).

**$({\rm SUP}_v)$ (the one-boundary support datum).** Every one of the five clauses called
$({\rm SUP}_v)$ in Book 174, Section 8.2, holds: (1) the Taylor--Wiles sets are disjoint from
$v$, kill the dual Selmer group, satisfy Book 141's split-regular detector input, and retain
both maps, both type rows, the flag, sign, determinant, and companion pairing in every finite
shadow; (2) the lower clean minimal problem has a nonzero patched module free over its regular
scalar source; (3) the full same-coefficient Gram block is singular at each declared boundary
prime; (4), after removing
the same frame variables on both sides, the completed selected boundary chart is precisely the
lower chart with the monodromy, flag, and Kummer coordinates retained, and the chosen boundary
prime on each global component lies over the generic point of its lower component and on no
other component; and (5) the scalar source and selected patched ring have the same local
dimension there. This is the precise hypothesis of Book 174's support theorem. It is not
inferred from the existence of a reciprocity surjection or from a characteristic-zero packet
count.

**$({\rm REC}_v)$ (reciprocity and the correct order).** On the direct sum of the actual
primary and companion new modules, let $\mathbb T$ be the image of the declared good trace
operators, the fixed determinant scalars, and, in the scalar family, the structural
$\Lambda_v$-action; at auxiliary level also retain the effective diamond algebra and only
those ordered auxiliary operators already proved to lie in the trace/structural image. It is
therefore faithful by definition. Require the clean hypotheses of
Book 170: the module is $\mathcal O$-free, its characteristic-zero Hecke action is semisimple,
every generic factor has the required integral Galois realization and exact local--global
compatibility, the represented finite-flat condition holds on every Artinian quotient above
$\ell$, every generic factor satisfies the other named local conditions, and the
trace/structural generators listed above generate this entire image. Book 170 then constructs
the order-valued representation and a surjection from the represented deformation ring. If
line, sign, or orientation operators outside this trace/structural order are adjoined,
surjectivity onto the larger image is an additional generation hypothesis and is not assumed
silently.

**$({\rm RAY}_v)$ (strict scalar twisting).** The effective global ray quotient of
Section 2.2 exists, and Book 174's twisting identities hold for represented deformation rings,
strict complexes, new modules, pairings, and faithful acting images. This is what proves
fixed-prime augmentation. A merely local tame character does not suffice.

**$({\rm AUG}_Q)$ (auxiliary control).** The Taylor--Wiles modules are free over their
effective diamond group rings, the marked finite-shadow patch exists, and auxiliary
augmentation recovers the represented rings, complexes, deformation actions, and pairings.
In addition, augmentation of the *acting image* is exact. Book 151 proves the torsor, module,
and pairing assertions under its clean hypotheses; it does not formally deduce the last
acting-image assertion from module augmentation. That final assertion is retained here as a
separate hypothesis, just as it is in clean minimal patching.

On the curve-new carrier, the corrected normalized-branch filtration and primitive extreme
residues are needed only if one also invokes their component or lowering consequences. Then
$({\rm AIH}_{\mathscr F})$ and $({\rm PRI}_{\rm type})$ must be added exactly as in Book 174;
$({\rm NU}_{\rm type})$ is additionally required for the switched graph--definite comparison,
as already recorded in $({\rm AUT}_v)$. None is used to identify a Galois cotangent determinant
in this book. The formal reduced comparison below uses
$({\rm AUT}_v)$, $({\rm TYPE}_v)$, $({\rm SUP}_v)$, and $({\rm REC}_v)$; the scalar-family
conclusions add $({\rm RAY}_v)$, while descent from an auxiliary patch adds
$({\rm AUG}_Q)$. Hypothesis $({\rm AIH}_{\mathscr F})$ remains part of the richer level-change
realization just stated, but it never supplies the independent typed Ihara or support
hypotheses by itself.

Finally, reducedness of the global conductor-one deformation ring, or of its patched analogue,
is **not** in this ledger. It will be named separately when a full scheme-theoretic $R=T$
statement is desired. Full-Iwahori saturation alone does not select an ordered old Frobenius
root when the roots collide modulo $\ell$ and does not kill a nilpotent global kernel.

### 2.4 The one-prime boundary

Only the place $v$ varies. Taylor--Wiles primes are auxiliary and are removed by their own
augmentation; they are not additional fixed nonminimal primes. No tensor product of
fixed-prime type complexes is used.

The theorem excludes the following cases:

- the $q_v\equiv-1\pmod\ell$ two-sign branch;
- a place with no nontrivial tame $\ell$-power scalar quotient;
- a primitive wild or ramified dyadic type;
- an Eisenstein localization or an $\ell$-divisible stabilizer;
- a component specified only by conductor or inertial semisimplification;
- coefficient characteristic five; and
- two or more fixed nonminimal places.

These exclusions identify different mathematical problems. They are not treated by enlarging
the meaning of the one-prime datum.

## 3. The exact output of the type-complex theorem

### 3.1 The conductor-one line-special boundary

Book 174 computes the scalar local incidence chart. With $m$ the monodromy parameter, $u$ and
$c$ the two incidence coordinates, and $R_0$ the complete base containing the line-character,
determinant, frame, unramified, and tame Kummer directions, the ambient chart is

$$
A_{\mathrm{inc}}
=R_0[[m,u,c]]/(mu,mc).
\tag{3.1}
$$

The schematic closure of the nonzero-monodromy locus is

$$
A_{\mathrm{sp}}=A_{\mathrm{inc}}/(u,c)
\simeq R_0[[m]].
\tag{3.2}
$$

The condition $m\ne0$ is open and cannot itself define a deformation functor on all Artinian
coefficient rings. Thus the represented special condition contains the $m=0$ boundary. A
characteristic-zero point claimed to have conductor one or two must separately have $m\ne0$.

The monodromy-zero boundary of (3.2) is
$A_{\mathrm{sp}}/(m)\simeq R_0$. The neutral minimal ring used to begin the support argument
is obtained by imposing further boundary equations on that base. It is not the ring (3.2).
Under $({\rm SUP}_v)$, Book 174 uses the neutral minimal patched module only to produce a
nonzero boundary carrier and then spreads that carrier across the line-special component. It
does not identify the two deformation problems.

### 3.2 The represented scalar-twist identities

Assume $({\rm RAY}_v)$. Let $R_{Q,v}^{\mathrm{sp},1}$ denote the conductor-one line-special
global deformation ring at an auxiliary level $Q$. Twisting by the recorded global ray
character and untwisting by its inverse give inverse transformations of represented functors.
Book 174 therefore proves

$$
R_{Q,v}^{\mathrm{sp},2}
\simeq
R_{Q,v}^{\mathrm{sp},1}
\widehat\otimes_{\mathcal O}\Lambda_v
\tag{3.3}
$$

and

$$
R_{Q,v}^{\mathrm{sp},2}
\widehat\otimes_{\Lambda_v,\epsilon_v}\mathcal O
\simeq R_{Q,v}^{\mathrm{sp},1}.
\tag{3.4}
$$

These are identities of represented deformation problems with their determinant families,
line, sign, and monodromy relation. They are stronger than an agreement of characteristic-zero
points.

On the primary--companion direct sum, global twisting also gives

$$
M_{Q,v}^{(2)}\simeq
\Lambda_v\otimes_{\mathcal O}M_{Q,v}^{(1)}.
\tag{3.5}
$$

Coefficient extraction in the group basis of $\Lambda_v$ proves the faithful acting-order
identity

$$
\mathbb T_{Q,v}^{\mathrm{sp},2}
\simeq
\Lambda_v\otimes_{\mathcal O}
\mathbb T_{Q,v}^{\mathrm{sp},1},
\tag{3.6}
$$

together with exact augmentation

$$
\mathbb T_{Q,v}^{\mathrm{sp},2}/\ker(\epsilon_v)
\mathbb T_{Q,v}^{\mathrm{sp},2}
\simeq\mathbb T_{Q,v}^{\mathrm{sp},1}.
\tag{3.7}
$$

Thus both sides of the scalar family are obtained from the same conductor-one line-special
problem. This observation determines exactly what a later $R=T$ argument must prove.

### 3.3 Complexes, duality, and support

Under $({\rm TYPE}_v)$, at auxiliary level $Q$ Book 174 constructs a primary complex

$$
C_{Q,v}^{\mathrm{pri}}
=\bigl[P_{Q,v}^0\xrightarrow{d_{Q,v}}P_{Q,v}^1\bigr]
\tag{3.8}
$$

in degrees zero and one. Write $A_Q$ for the combined fixed-prime and auxiliary coefficient
algebra. The terms of (3.8) are finite projective over $A_Q$, the differential is split
injective over $A_Q$, and its cokernel is finite projective over $A_Q$. The companion complex
satisfies

$$
C_{Q,v}^{\mathrm{cmp}}
\simeq
R\!\operatorname{Hom}
\bigl(C_{Q,v}^{\mathrm{pri}},A_Q\bigr)[-1].
\tag{3.9}
$$

The shift is $[-1]$: a two-term complex in degrees zero and one is dualized and returned to
the same cohomological placement by this shift.

After the marked finite-shadow patch, the same statements hold over the one-prime scalar
source. More importantly, Book 174 constructs the deformation-side action rather than
inferring it from generic Hecke eigenvalues. Under the separate hypothesis $({\rm SUP}_v)$ it
proves, with $({\rm RAY}_v)$ also imposed when $i=2$,

$$
\operatorname{Supp}_{R_{Q,v}^{\mathrm{sp},i}}
H^*\bigl(C_{Q,v}^{\mathrm{pri}}\bigr)
=\operatorname{Spec}R_{Q,v}^{\mathrm{sp},i},
\qquad i=1,2.
\tag{3.10}
$$

The patched complexes have the analogous full support. This is support on every named
component, deduced in Book 174 from the five explicit boundary and depth clauses recalled
above. It is not a generic packet count. In the present theorem it is a conditional imported
conclusion, because $({\rm SUP}_v)$ is not established by the residual datum alone.

Equation (3.10) is topological. If $I$ is the annihilator of the total cohomology, it says

$$
\sqrt I=\sqrt{(0)}.
\tag{3.11}
$$

It does not say $I=0$ when the global deformation ring has nilpotents.

### 3.4 The Hecke-valued representation

Under $({\rm REC}_v)$, Book 170 constructs a continuous representation over the faithful
trace/structural order, with good-place characteristic polynomial

$$
X^2-T_wX+q_wS_w
\tag{3.12}
$$

for geometric Frobenius. Equivalently,
$\det(1-X\rho(\Phi_w))=1-T_wX+q_wS_wX^2$. Full local--global compatibility places its
restriction at $v$ on the line-special quotient and records the scalar character, monodromy,
line, and sign. The universal property therefore gives surjections

$$
f_i:R_{Q,v}^{\mathrm{sp},i}
\twoheadrightarrow\mathbb T_{Q,v}^{\mathrm{sp},i},
\qquad i=1,2.
\tag{3.13}
$$

Surjectivity uses the generation clause in $({\rm REC}_v)$. Faithfulness of an action alone
would not prove that every chosen Hecke generator lies in the image of the deformation ring,
and Book 170 reaches only its trace order when unrelated local operators have been adjoined.

The map $f_i$ acts on the primary--companion carrier through its faithful Hecke image. Hence

$$
\ker(f_i)
=\operatorname{Ann}_{R_{Q,v}^{\mathrm{sp},i}}
H^*\bigl(C_{Q,v}^{\mathrm{pri}}\oplus
C_{Q,v}^{\mathrm{cmp}}\bigr).
\tag{3.14}
$$

This equality, together with (3.10), is the algebraic core of the comparison.

## 4. From support to the reduced comparison

### 4.1 A kernel detected by a faithful carrier

We isolate the elementary commutative algebra needed to use (3.10).

**Lemma 4.1 (full support and a reduced faithful image).** Let $R$ be a noetherian ring, let
$M$ be a finite $R$-module, and let $T$ be the image of $R$ in
$\operatorname{End}(M)$. Assume

$$
\operatorname{Supp}_R(M)=\operatorname{Spec}R
\tag{4.1}
$$

and $T$ is reduced. Then the kernel of $R\twoheadrightarrow T$ is the nilradical of $R$, and

$$
R_{\mathrm{red}}\xrightarrow{\sim}T.
\tag{4.2}
$$

**Proof.** Let $I=\operatorname{Ann}_R(M)$. Full support gives

$$
V(I)=\operatorname{Spec}R,
$$

so $I$ is contained in every prime ideal and hence $I\subseteq\sqrt{(0)}$. Conversely, every
nilpotent element of $R$ maps to a nilpotent element of the reduced ring $T$, hence maps to
zero. Thus $\sqrt{(0)}\subseteq I$. Since $I$ is the kernel of the faithful-image map, (4.2)
follows. $\square$

**Lemma 4.1a (torsion-free reduced-generic criterion).** Let $\mathcal O$ be a DVR with
uniformizer $\varpi$, and let $A$ be an $\mathcal O$-torsion-free algebra. If
$A[1/\varpi]$ is reduced, then $A$ is reduced.

**Proof.** If $a^n=0$, then $a/1$ is nilpotent and hence zero in $A[1/\varpi]$. Thus
$\varpi^m a=0$ for some $m$. Torsion-freeness gives $a=0$. $\square$

The target's reducedness is not a consequence of the word *faithful*. In this application it
follows from the separate semisimplicity clause in $({\rm REC}_v)$. Indeed, the acting order
is an actual submodule of the endomorphisms of a finite free $\mathcal O$-module, so it is
$\mathcal O$-torsion-free. After inverting $\varpi$, simultaneous packet decomposition embeds
its action into a product of characteristic-zero eigensystem fields. Lemma 4.1a therefore
makes the finite-level order reduced. This argument is not automatically available for an
abstract patched inverse-limit algebra.

### 4.2 The reduced one-prime theorem

**Theorem 4.2 (reduced one-prime nonminimal comparison).** Assume the global and local datum
of Sections 2.1--2.2 together with $({\rm AUT}_v)$, $({\rm TYPE}_v)$,
$({\rm SUP}_v)$, and $({\rm REC}_v)$. Then nonminimal reciprocity induces a canonical
isomorphism

$$
\boxed{
\bigl(R^{\mathrm{sp},1}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T^{\mathrm{sp},1}}
\tag{4.3}
$$

If $({\rm RAY}_v)$ also holds, it induces a canonical isomorphism

$$
\boxed{
\bigl(R_{\Lambda_v}^{\mathrm{sp},2}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T_{\Lambda_v}^{\mathrm{sp},2}}.
\tag{4.4}
$$

The same two assertions hold at every retained **finite** auxiliary level for which the named
hypotheses hold.

**Proof strategy.** Use Book 174's conditional full-support theorem, identify the kernel with
the carrier annihilator, and use reducedness of the finite faithful Hecke order. No uniqueness
of a generic component is required.

**Proof.** At each retained finite auxiliary level, equations (3.10) and (3.14) verify the
support and kernel hypotheses of Lemma 4.1. The corresponding faithful Hecke order is reduced
by the torsion-free semisimple-generic argument above. Lemma 4.1 gives the reduced comparison
there. Taking the empty auxiliary set gives (4.3), and the scalar twist gives (4.4).

The marked Frobenius traces, determinant family, line, sign, and tame character show that
these are the canonical reciprocity maps, not unmarked abstract isomorphisms. No claim that
reduction commutes with an auxiliary quotient is needed. $\square$

The proof uses every named component because Book 174 proves support on every named component
under $({\rm SUP}_v)$. It does not infer support from the equality of dimensions of one
component, and it does not assume that a tame character factor has only one global component.

At patched level, full topological support still gives

$$
\operatorname{Ann}_{R_\infty}H^*(C_\infty)\subseteq\sqrt{(0)}.
\tag{4.4a}
$$

It gives a patched reduced comparison only if the patched acting image is independently known
to be reduced. Since no preceding book establishes that assertion for the present inverse
limit, Theorem 4.2 deliberately makes no patched reducedness claim. Section 5.3 gives the
different sufficient condition actually needed for a full patched equality: reducedness of
the patched deformation ring itself.

### 4.3 The exact obstruction to full R=T

**Corollary 4.3 (full equality criterion).** Under the hypotheses of Theorem 4.2 and
$({\rm RAY}_v)$, the following are equivalent:

1. $R^{\mathrm{sp},1}$ is reduced;
2. $R^{\mathrm{sp},1}\xrightarrow{\sim}\mathbb T^{\mathrm{sp},1}$;
3. $R_{\Lambda_v}^{\mathrm{sp},2}\xrightarrow{\sim}\mathbb T_{\Lambda_v}^{\mathrm{sp},2}$.

When these conditions hold, every fixed-character comparison obtained from (3.3) and (3.6)
by the coefficient changes of Chapter 5 is also a full equality. An auxiliary-level full
equality requires reducedness of its own conductor-one deformation ring, unless it is instead
obtained as a quotient of an independently established patched equality.

**Proof.** The equivalence of the first two statements is (4.3), because the target is
reduced. Equations (3.3) and (3.6) identify the third map with

$$
f_1\widehat\otimes_{\mathcal O}\operatorname{id}_{\Lambda_v}.
\tag{4.5}
$$

The group algebra $\Lambda_v$ is finite free and nonzero, hence faithfully flat, over
$\mathcal O$. Because it is finite, the completed tensor in (4.5) is the usual finite tensor
for this kernel calculation. Flatness gives

$$
\ker(f_1\widehat\otimes 1)
=\ker(f_1)\widehat\otimes_{\mathcal O}\Lambda_v,
$$

and faithful flatness says that this module vanishes exactly when $\ker(f_1)$ vanishes.
Surjectivity is already known.
$\square$

The missing condition is global reducedness. The local ring $R_0[[m]]$ in (3.2) is reduced
when $R_0$ is reduced, but a global quotient of a reduced power-series source can be
nonreduced. Equidimensionality and a reduced generic Hecke algebra do not rule out such a
nilpotent thickening. No prior theorem proves that the global ring
$R^{\mathrm{sp},1}$ is reduced.

Consequently Corollary 4.3 is a reusable criterion, not a proof of the catalog's full
scheme-theoretic $R=T$ assertion.

### 4.4 Why the tame direction cannot kill the obstruction

Let $K=\ker(f_1)$. Theorem 4.2 says more precisely that $K$ is the nilradical of the
noetherian ring $R^{\mathrm{sp},1}$; in particular, $K$ is a nilpotent ideal. Indeed, choose
finite generators $x_1,\ldots,x_r$ of $K$, choose $n_j$ with $x_j^{n_j}=0$, and note that
$K^{1+\sum_j(n_j-1)}=0$. Exactness of tensoring with the $\mathcal O$-free algebra
$\Lambda_v$ gives

$$
\ker(f_2)=K\widehat\otimes_{\mathcal O}\Lambda_v.
\tag{4.6}
$$

Theorem 4.2, using Book 174's support theorem together with the reduced finite Hecke order,
says that $K$ is nilpotent; support alone does not say $K=0$. Formula (4.6) shows that adding
the scalar tame variable transports the possible nilpotent kernel rather than removing it.
Fixed-prime augmentation transports it back.

This is the decisive circularity check. An argument cannot prove $K=0$ by passing to the
scalar family, proving only topological support there, and then augmenting to the same
conductor-one problem. Nor can it replace that conductor-one problem by the neutral minimal
ring used as a boundary anchor in Book 174.

## 5. What patching and augmentation do prove

### 5.1 The two-term complex and its Tor term

Let $A$ be one of the fixed-prime or combined auxiliary coefficient algebras. For a two-term
complex of projective $A$-modules

$$
C=[P^0\xrightarrow{d}P^1]
\tag{5.1}
$$

with $H^0(C)=0$, an $A$-algebra $B$ gives

$$
H^0(C\otimes_A^LB)
\simeq
\operatorname{Tor}_1^A(H^1(C),B)
\tag{5.2}
$$

and

$$
H^1(C\otimes_A^LB)
\simeq H^1(C)\otimes_A B.
\tag{5.3}
$$

Indeed, $H^0(C)=0$ makes

$$
0\longrightarrow P^0\xrightarrow{d}P^1
\longrightarrow H^1(C)\longrightarrow0
$$

a length-one projective resolution. Tensoring it proves (5.2)--(5.3), and also gives
$\operatorname{Tor}_j^A(H^1(C),B)=0$ for $j>1$. Thus degree-zero cohomology after
specialization is exactly the first Tor group. Patching only $H^1(C)$ would discard this
obstruction.

For instance, if $A=\mathcal O[[t]]$ and $C=[A\xrightarrow{t}A]$, then specialization at
$t=0$ produces a zero differential and a nonzero degree-zero group. Freeness over
$\mathcal O$ before specialization does not imply flatness over $A$.

### 5.2 Amplitude after Book 174

The following elementary lemma is useful, but its hypothesis must be checked on the actual
fiber.

**Lemma 5.1 (fiber concentration).** Let $(A,\mathfrak m,k)$ be local and let $C$ be perfect
of amplitude contained in $[0,1]$. If

$$
H^0(C\otimes_A^Lk)=0,
\tag{5.4}
$$

then $C\simeq M[-1]$ for a finite free $A$-module $M$.

**Proof.** Remove every contractible summand on which the differential has a unit entry. In
the resulting minimal free model $[F^0\to F^1]$, the differential is zero modulo
$\mathfrak m$. Hence the degree-zero special-fiber cohomology is $F^0\otimes_Ak$.
Condition (5.4) and Nakayama's lemma give $F^0=0$, leaving the finite free module $F^1$ in
degree one. $\square$

The augmentation of the scalar family is

$$
C_{\infty,v}^{\mathrm{sp},2}
\otimes_{\Lambda_v,\epsilon_v}^{L}\mathcal O
\simeq C_{\infty,v}^{\mathrm{sp},1},
\tag{5.5}
$$

not the neutral minimal complex. Book 173 therefore cannot be used to verify (5.4) for the
right side of (5.5).

There is nevertheless no amplitude gap: under $({\rm TYPE}_v)$ and the retained
finite-shadow patching data in $({\rm SUP}_v)$, with $({\rm RAY}_v)$ also imposed for the
scalar-twisted family, Book 174 proves directly that the patched differential is split
injective and its cokernel is finite projective over the one-prime scalar patching source
$S_\infty$. Since that source is local, the cokernel is finite free. Consequently

$$
C_{\infty,v}^{\mathrm{sp},i}
\simeq M_{\infty,v}^{\mathrm{sp},i}[-1],
\qquad i=1,2,
\tag{5.6}
$$

with $M_{\infty,v}^{\mathrm{sp},i}$ finite free over the corresponding scalar base. This is an
output of Book 174's one-prime patching, not a new consequence of minimal $R=T$.

### 5.3 The conditional patched R=T criterion

The finite-level reduced comparison did not require a reduced patched algebra. For a full
patched equality, the correct nilpotent-sensitive statement is the following.

**Proposition 5.2 (conditional patched one-prime $R=T$).** Let $S_\infty$ be the local scalar
patching source, let $R_\infty^{\mathrm{sp},i}$ be the noetherian patched deformation ring,
and let $M_\infty^{\mathrm{sp},i}$ be the nonzero module in (5.6). Assume the marked
deformation action has full topological support:

$$
\operatorname{Supp}_{R_\infty^{\mathrm{sp},i}}
M_\infty^{\mathrm{sp},i}
=\operatorname{Spec}R_\infty^{\mathrm{sp},i}.
\tag{5.6a}
$$

Let $\mathbb T_\infty^{\mathrm{sp},i}$ be the actual image of
$R_\infty^{\mathrm{sp},i}$ on the total primary--companion patched carrier. If

$$
({\rm RED}_\infty^i):
\qquad R_\infty^{\mathrm{sp},i}\text{ is reduced},
\tag{5.6b}
$$

then the canonical map is an isomorphism:

$$
R_\infty^{\mathrm{sp},i}
\xrightarrow{\sim}\mathbb T_\infty^{\mathrm{sp},i}.
\tag{5.6c}
$$

If $({\rm AUG}_Q)$ identifies the auxiliary quotients of the two sides with the represented
finite-level deformation ring and its faithful acting order, then (5.6c) descends to a full
finite-level $R=T$ equality.

**Proof strategy.** Patching is used to produce a genuine module and the support statement.
Reducedness is then used once, at the annihilator.

**Proof.** Because $S_\infty$ acts through the structural map to
$R_\infty^{\mathrm{sp},i}$ and $M_\infty^{\mathrm{sp},i}$ is finite over $S_\infty$, it is
finite over $R_\infty^{\mathrm{sp},i}$. Equation (5.6a) gives

$$
\operatorname{Ann}_{R_\infty^{\mathrm{sp},i}}
M_\infty^{\mathrm{sp},i}
\subseteq\sqrt{(0)}.
$$

Hypothesis (5.6b) makes the right side zero. Thus the primary summand is faithful, so the
action on the larger primary--companion carrier is faithful as well. The kernel of the map to
its actual image is therefore zero, proving (5.6c). Quotienting an isomorphism by the marked
auxiliary ideal remains an isomorphism; $({\rm AUG}_Q)$ identifies those quotients with the
claimed finite objects. $\square$

Under $({\rm RAY}_v)$, the patched conductor-two comparison is the tensor product of the
conductor-one comparison with $\Lambda_v$. Hence a patched equality for $i=1$ implies one for
$i=2$ without separately proving that $R_\infty^{\mathrm{sp},2}$ is reduced; conversely,
faithful flatness of $\Lambda_v/\mathcal O$ detects the conductor-one kernel. The tame variable
transports whatever answer holds on the line-special face.

The proposition does not prove $({\rm RED}_\infty^i)$. Local reducedness of the enhanced chart,
equidimensionality, Cohen--Macaulayness, and reducedness of a finite Hecke order do not imply
reducedness of a global patched quotient. One may replace (5.6b) by an independent theorem
that the displayed annihilator is zero, but calling that theorem “support” would hide the
nilpotent issue. Lemma 4.1a gives one concrete way to verify (5.6b): prove that the actual
patched ring is $\mathcal O$-torsion-free and that its generic fiber is reduced. Neither
property is imported here merely from the local chart or the dimension calculation.

### 5.4 Fixed-prime and auxiliary augmentation

There are two independent augmentations. The fixed-prime map is $\epsilon_v$ from (2.3). The
auxiliary map sends every Taylor--Wiles diamond operator to one. Book 174 proves the
fixed-prime statements under $({\rm RAY}_v)$ from the genuine global twist and coefficient
extraction.
Hypothesis $({\rm AUG}_Q)$ supplies the separately required auxiliary statements. Both maps
are marked on the finite complexes, their pairings, deformation actions, represented rings,
and faithful acting images before passing to the patch.

The two augmentation ideals lie in independent coefficient factors. The strict projective
terms compute derived specialization termwise, and the projective new module supplied by
$({\rm TYPE}_v)$ has zero positive coefficient-algebra Tor. Thus fixed-prime augmentation
gives (3.4), (3.7), and (5.5), while auxiliary augmentation removes the Taylor--Wiles
conditions and returns the finite-level objects. The marked twist and auxiliary diagrams make
the two orders of specialization canonically identical.

Exact acting-image augmentation is separate from exact module augmentation. The image of an
algebra in an endomorphism ring can acquire a larger kernel after specialization. Equation
(3.7) is valid because Book 174 proves it by global twisting and coefficient extraction, not
because cohomology happens to specialize exactly.

Reduced comparison can be applied directly at every finite auxiliary level, where full support
is already known. It is therefore unnecessary, and generally unsafe, to assume that reduction
commutes with quotienting by an augmentation ideal.

### 5.5 Fixed characters and coefficient extension

Let $\mathcal O'/\mathcal O$ be a finite extension of coefficient discrete valuation rings and
let

$$
\chi:\Delta_v\longrightarrow(\mathcal O')^\times
\tag{5.7}
$$

be a character, possibly the augmentation character. Define

$$
R_\chi^{\mathrm{sp},2}
=R_{\Lambda_v}^{\mathrm{sp},2}
\widehat\otimes_{\Lambda_v,\chi}\mathcal O',
\qquad
\mathbb T_\chi^{\mathrm{sp},2}
=\mathbb T_{\Lambda_v}^{\mathrm{sp},2}
\otimes_{\Lambda_v,\chi}\mathcal O'.
\tag{5.8}
$$

The character map $\Lambda_v\to\mathcal O'$ is usually not flat, so (5.9) must not be
obtained by blindly tensoring (4.4). Strict twisting gives the stronger identities

$$
R_\chi^{\mathrm{sp},2}
\simeq R^{\mathrm{sp},1}\widehat\otimes_{\mathcal O}\mathcal O',
\qquad
\mathbb T_\chi^{\mathrm{sp},2}
\simeq\mathbb T^{\mathrm{sp},1}\otimes_{\mathcal O}\mathcal O',
\tag{5.8a}
$$

with determinant changed by $\chi^2$. Let
$K=\ker(R^{\mathrm{sp},1}\to\mathbb T^{\mathrm{sp},1})$. Theorem 4.2 identifies $K$ with
the nilradical. Since the source is noetherian, $K$ is nilpotent. The extension
$\mathcal O'/\mathcal O$ is finite free, so tensoring the comparison sequence is exact and
gives kernel $K\otimes_{\mathcal O}\mathcal O'$ in (5.8a).

The target in (5.8a) is reduced. It is $\mathcal O'$-torsion-free, and its generic fiber is
the tensor product of finite separable characteristic-zero algebras, hence is reduced. The
torsion-free reduced-generic criterion of Lemma 4.1a then kills every nilpotent in the
integral target. Therefore
$K\otimes\mathcal O'$ is exactly the nilradical of the source in (5.8a), proving

$$
\boxed{
\bigl(R_\chi^{\mathrm{sp},2}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}\mathbb T_\chi^{\mathrm{sp},2}}.
\tag{5.9}
$$

On modules, (3.5) gives

$$
M_\chi^{(2)}
\simeq M^{(1)}\otimes_{\mathcal O}\mathcal O',
\qquad
\operatorname{Tor}^{\Lambda_v}_j(M^{(2)},\mathcal O')=0
\quad(j>0),
\tag{5.10}
$$

because $M^{(2)}\simeq\Lambda_v\otimes_{\mathcal O}M^{(1)}$ is free over $\Lambda_v$.
Thus the nonflat character quotient creates no hidden cohomology in this particular family.
For $\chi=1$, (5.9) is the conductor-one comparison after coefficient extension. For
$\chi\ne1$, it is the conductor-two comparison. A ramified coefficient extension scales
uniformizer-normalized lengths by its ramification index; the ideals and ring comparisons,
not raw lengths, are the invariant statements.

## 6. Scalar and vexing branches

### 6.1 Why the scalar family forces q congruent to one

Let $K=F_v$. For a scalar tame character $\chi$ to extend from inertia to $G_K$, the tame
relation gives

$$
\chi(\tau)^{q_v}=\chi(\tau).
\tag{6.1}
$$

Hence the order of $\chi(\tau)$ divides $q_v-1$. A nontrivial character of $\ell$-power order
therefore exists only if

$$
\ell\mid(q_v-1).
\tag{6.2}
$$

This is exactly (2.6). Conversely, the clean datum does not infer a global ray character from
the local divisibility alone; the effective global determinant and ray-character torsor are
part of Book 174's hypotheses.

For a nontrivial conductor-one character $\chi$ and an unramified character $\mu$, the
conductor formula is

$$
a(\operatorname{St}\otimes\mu\chi)
=2a(\chi)=2.
\tag{6.3}
$$

At augmentation, $\chi=1$ and nonzero rank-one monodromy contributes conductor one.

### 6.2 The line and sign at the colliding root

At $q_v\equiv1\pmod\ell$, the two residual old Frobenius roots coincide. No integral
idempotent formed from their difference can select one root. The scalar theorem instead uses
the retained invariant line and the independently constructed normalized sign involution
$\widetilde W_v$.

Because $\ell$ is odd, the projectors

$$
e_{\pm}=\frac{1\pm\widetilde W_v}{2}
\tag{6.4}
$$

are integral whenever the typed normalized involution has actually been constructed. If one
has only an unnormalized operator whose square is the central scalar $S_v$, this formula is
not available before a compatible integral normalization has been supplied. In either case the
sign does not follow from the old $U_v$-root decomposition. Books 138 and 174 construct the
enhanced line and primary--companion lattices that make the independently retained sign
meaningful at the colliding root. Book 139's full two-map saturation alone would not suffice.

The two Kummer tangent directions at the scalar point remain in $R_0$ in (3.1)--(3.2). They
cancel only virtually in the global Euler-characteristic calculation. Omitting them would
replace the scalar local ring by the clean distinct-root chart and would silently change the
deformation problem.

### 6.3 The signed Gram factor

The same-coefficient pull--norm Gram block, in Book 174's standard central orientation, is

$$
G_v=
\begin{pmatrix}
q_v+1&T_v\\
S_v^{-1}T_v&q_v+1
\end{pmatrix}.
\tag{6.5}
$$

If a central square root $s_v^2=S_v$ has been chosen and the second basis vector is rescaled,
put $a_v=s_v^{-1}T_v$. Only in this rescaled block is the matrix symmetric. On an
independently constructed integral $W_v$-sign $\varepsilon_v$, its two factors are

$$
c_v^{\varepsilon_v}=q_v+1-\varepsilon_va_v,
\qquad
c_v^{-\varepsilon_v}=q_v+1+\varepsilon_va_v.
\tag{6.6}
$$

Suppose the level-raising congruence is

$$
a_v\equiv\varepsilon_v(q_v+1)\pmod\varpi.
\tag{6.7}
$$

The companion factor is then

$$
q_v+1+\varepsilon_va_v
\equiv2(q_v+1)\equiv4\pmod\varpi,
\tag{6.8}
$$

where the final congruence uses $q_v\equiv1\pmod\ell$. It is a unit for
$\ell\geq7$. Thus, once the integral sign block exists, the Smith module of this automorphic
Gram block has only the selected nonunit factor in that block even though the two old
Frobenius roots collide.

This calculation is not a branch-determinant theorem. Book 174 proves only that the Galois
line-incidence equation and the automorphic determinant have the same image as principal
equations in the faithful Hecke order:

$$
T_v^2-(q_v+1)^2S_v=-S_v\det(G_v).
\tag{6.9}
$$

It explicitly constructs no pre-$R=T$ chain map from a Galois cotangent complex to the
automorphic Gram complex. Consequently (6.6) is not called a local cotangent determinant,
an augmented congruence ideal, or a determinant-line comparison here. Any such conclusion
requires the additional primitive rank-one, isolation, and cross-determinant hypotheses of
the relevant numerical theorem. Independently, the normalized-branch Smith module and the
Néron graph component group remain distinct and need not vanish merely because the full
degeneracy image is saturated.

### 6.4 The q congruent to minus one branch

If $q_v\equiv-1\pmod\ell$, equation (6.1) admits no nontrivial scalar tame character of
$\ell$-power order. The scalar residual special chart of (3.1) does not exist. Instead the two
special diagonal entries are distinct, while both signed Gram factors can be nonunits.

Book 174 retains the full two-map complex, the two extension orientations, and the full Smith
matrix in this branch. Its extreme residue is primitive only under
$({\rm PRI}_{\rm type})$, and its switched graph--definite comparison additionally requires
$({\rm NU}_{\rm type})$. It does not produce a scalar-twist augmentation or a one-sign $R=T$
theorem. A type-specific theorem at this vexing branch would need an independently
constructed integral signed direct factor and support for its named deformation component.

For $q_v\not\equiv1\pmod\ell$, the ordinary distinct-root special chart may still be useful,
but it is not the conductor-two scalar family of this book. Combining its smoothness with the
group algebra $\Lambda_v$ would combine mutually incompatible hypotheses.

## 7. Automorphy of characteristic-zero points

### 7.1 Factoring a point through the reduced order

Let $\mathcal O'/\mathcal O$ be finite and let

$$
\rho:G_F\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{7.1}
$$

be a lift satisfying the datum of Chapter 2 on a fixed character
$\chi:\Delta_v\to(\mathcal O')^\times$, which may be trivial. Assume its monodromy at $v$ is
nonzero. The local conductor is then one for the augmentation character and two for a
nontrivial character. Universality gives a point

$$
x_\rho:R_\chi^{\mathrm{sp},2}\longrightarrow\mathcal O'.
\tag{7.2}
$$

The target is a domain, so $x_\rho$ kills the nilradical. Equation (5.9) therefore factors it
canonically through the faithful Hecke order:

$$
R_\chi^{\mathrm{sp},2}
\longrightarrow
\bigl(R_\chi^{\mathrm{sp},2}\bigr)_{\mathrm{red}}
\xrightarrow{\sim}
\mathbb T_\chi^{\mathrm{sp},2}
\longrightarrow\mathcal O'.
\tag{7.3}
$$

Thus the reduced comparison is enough for characteristic-zero modularity. Full equality would
add information about infinitesimal nilpotent deformations, but it is not needed to place the
point (7.2) on an automorphic eigensystem.

### 7.2 Exact local type and the integral lattice

After a finite coefficient extension, the Hecke character in (7.3) selects a
parallel-weight-two cuspidal automorphic constituent. The primary type lattice records the
scalar tame character, invariant line, $W_v$-sign, and special monodromy. At the other places,
the named local type and finite-flat hypotheses identify the required packets.

At every good place, (3.12) agrees with the characteristic polynomial of $\rho$. Density and
Brauer--Nesbitt identify the characteristic-zero representations. To identify their integral
lattices, scale an intertwiner so that one stable lattice maps into the other but not into its
$\varpi'$-multiple. Its reduction has nonzero image. Residual absolute irreducibility makes
that image the whole residual representation, and Nakayama's lemma makes the lattice map an
isomorphism.

We obtain the following pointwise theorem.

**Theorem 7.1 (one-prime characteristic-zero modularity).** Assume the global and local datum
of Sections 2.1--2.2 together with $({\rm AUT}_v)$, $({\rm TYPE}_v)$,
$({\rm SUP}_v)$, $({\rm REC}_v)$, and $({\rm RAY}_v)$. Let
$\chi:\Delta_v\to(\mathcal O')^\times$ be either the augmentation character or a retained
nontrivial character. Every lift (7.1) on the $\chi$-fiber, finite flat of weights $\{0,1\}$
above $\ell$, on the named conditions away from $v$, and with nonzero rank-one monodromy at
$v$, is attached integrally to a cuspidal
parallel-weight-two automorphic representation with the same determinant and named local
data. Its local conductor at $v$ is one when $\chi=1$ and two when $\chi\ne1$.

For the conductor-one statement alone, one may omit $({\rm RAY}_v)$ and start directly with
$R^{\mathrm{sp},1}$; then (4.3), rather than fixed-character specialization of the scalar
family, gives the same conclusion.

**Proof.** Use (5.8a)--(5.9) to factor the deformation point through the appropriate reduced
faithful order, as in (7.3). In the direct conductor-one variant use (4.3) instead. Choose the
resulting automorphic constituent and apply the characteristic-zero and lattice comparisons
above. Nonzero monodromy contributes conductor one on the untwisted face, while formula (6.3)
gives conductor two on a nontrivial conductor-one tame-character fiber. $\square$

The theorem proves automorphy of points without asserting that the source has no nilpotent
thickening.

### 7.3 Solvable descent

Suppose Theorem 7.1 is first applied over a finite solvable Galois totally real extension
$L/F$. Automorphy over $L$ does not descend from invariance alone. Book 109 applies only when
there is a descent-admissible prime cyclic tower, the restricted problem still has exactly one
fixed nonminimal place (all other places above $v$ carry verified spectator conditions), and
all of the following are checked:

1. $\rho|_{G_L}$ is irreducible, so the associated automorphic representation is cuspidal and
   has scalar endomorphisms;
2. cyclic base change, twisting, Galois attachment, and strong multiplicity one are available
   at every step;
3. the full restricted local parameters, not merely conductors, lie in the selected
   antecedent-complete range;
4. centers, weights, and inner-form discrete-series conditions are compatible; and
5. the representation $\rho$ is already defined on $G_F$, so it selects the quotient-character
   correction at each cyclic descent step.

Under these hypotheses, the extension-comparison lemma identifies the correction at the top
step. Twisting by its inverse produces a descent attached to the next restriction of $\rho$.
Repeating gives a compatible chain down to $F$. Local monodromy is transported by restriction
and extension of the full Weil--Deligne parameter; it is not recovered by extending or
contracting a conductor ideal.

## 8. Dependency, circularity, and normalization audit

### 8.1 Direct prerequisite ledger

The declared dependency row is $109,173,138,139,140,170,174$. Their exact roles after the
audit are as follows.

| Book | Result used | Boundary retained |
|---|---|---|
| 109, *Solvable Base Change and Descent* | recursive cyclic descent selected by an extending irreducible arithmetic representation | used only after top-field automorphy; invariance under a noncyclic solvable group is not enough |
| 173, *Minimal Modularity Lifting* | comparison point for the neutral minimal theorem and its finite-flat range | its equality is not applied to $R^{\mathrm{sp},1}$; the scalar Kummer and line-special directions do not satisfy that identification |
| 138, *Integral Local Types and Type Lattices* | enhanced special line, primary and companion lattices, primitive type occurrence, Frobenius conventions | at $q_v\equiv1$ a line enhancement replaces old-root separation; local lattices alone do not prove global support |
| 139, *Ihara Theory and Saturated Degeneracy Maps on Shimura Curves* | residual two-map Ihara injectivity and primitive saturation | conditional on the abelian Ihara hypothesis; full-map saturation does not create a scalar selected summand |
| 140, *Integral Level Change and Jacquet--Langlands Comparison* | node, graph, component-group, and normalized Smith comparisons | node-uniformization and generic support remain hypotheses; branch correction and the Néron component group are distinct |
| 170, *Hecke-Valued Galois Representations and Nonminimal Reciprocity* | the order-valued representation, named local factorization, trace generation, and the surjections (3.13) | every generic branch and every structural generator must be accounted for; a pseudorepresentation alone is insufficient |
| 174, *One-Prime Type Complexes and Component Support* | scalar chart, twist identities, projective primary--companion complexes, conditional full named-component support, and exact fixed-prime module and acting-image augmentation | $({\rm TIC}_v)$, $({\rm TIH}_{\mathscr F})$, $({\rm SUP}_v)$, and the effective ray quotient are separate hypotheses; its determinant result is only the scalar equation (10.7), with no cross-complex map; no global reducedness or nonminimal $R=T$ is asserted |

The proof of Theorem 4.2 uses Books 170 and 174 directly, with Books 138--140 supplying the
hypotheses built into Book 174. Book 173 is not an augmented-fiber $R=T$ input. Book 109 is used
only for the final descent statement. Book 151's torsor and module augmentation enter
transitively through Book 174; exact auxiliary *acting-image* augmentation remains the
separate hypothesis $({\rm AUG}_Q)$ and is not attributed to Book 151.
Books 141 and 171--172 likewise enter transitively through Book 174's Taylor--Wiles and lower-boundary
support datum; none is used here to manufacture nonminimal support or reducedness.

### 8.2 The first unsupported step in the full theorem

The original full-equality route first fails at the assertion

$$
C_{\infty,v}^{\mathrm{sp},2}
\otimes_{\Lambda_v,\epsilon_v}^{L}\mathcal O
\simeq C_\infty^{\min}
\quad\text{with}\quad
R^{\min}=\mathbb T^{\min}.
\tag{8.1}
$$

Book 174 proves the left side of (8.1) is $C_{\infty,v}^{\mathrm{sp},1}$, not the neutral
minimal complex. Book 173 does not prove an equality for the scalar conductor-one line-special
ring with its Kummer directions. Book 170 independently warns that minimal and sign-selected
special functors need not be related by a ring map.

After replacing (8.1) by the correct augmentation (5.5), Book 174 supplies amplitude under
$({\rm TYPE}_v)$ and full support under $({\rm SUP}_v)$. Once
$({\rm AUT}_v)$, $({\rm TYPE}_v)$, $({\rm SUP}_v)$, and $({\rm REC}_v)$ have actually been
verified, together with $({\rm RAY}_v)$ for the scalar family, the remaining gap in a full
finite-level $R=T$ proof is

$$
R^{\mathrm{sp},1}\text{ is reduced}.
\tag{8.2}
$$

Local reducedness of (3.2), expected dimension, Cohen--Macaulayness, and reducedness of the
Hecke image do not prove (8.2) for the global quotient. Theorems 4.2 and 7.1 are the strongest
conclusions available without it.

There are earlier blockers to an unconditional arithmetic application. For the finite reduced
comparison itself, they are the actual localization $({\rm AUT}_v)$; the independent type
hypotheses $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$; the five boundary-and-depth clauses
$({\rm SUP}_v)$; branchwise reciprocity and exact generation in $({\rm REC}_v)$; and the
effective ray quotient $({\rm RAY}_v)$ when the scalar family is used. The finite family
$({\rm AIH}_{\mathscr F})$ is additionally required whenever the constant-coefficient
level-change or normalized-residue package is invoked; it does not replace the typed
hypotheses. Exact auxiliary acting-image augmentation $({\rm AUG}_Q)$ is not needed to apply
Lemma 4.1 directly at a retained finite level, but it is required to descend an equality from
the patched level. Books 139 and 174 give precise conditional implications after the
applicable inputs are supplied; they do not prove those inputs from the bare residual
representation.

### 8.3 No finite-set or hidden-support argument

No theorem about two fixed nonminimal primes enters this book. In particular, no tensor
product of one-prime complexes, exchange of two fixed-prime quotient-new functors, joint
product support, or multi-prime Tor-independence is assumed. No later finite-set construction
is used to repair the one-prime argument.

Nor is component support hidden in a uniqueness hypothesis. The proof of Theorem 4.2 uses the
full support equality (3.10), already proved in Book 174 for every named component. It does not
argue that a full-dimensional subset must equal a chosen component, and it does not assume one
global component above each character factor.

The scalar twist identity also prevents a finite-set conclusion from being smuggled in one
prime at a time. A chain of separate one-prime theorems would require an automorphic lower
packet and the complete clean datum at every intermediate stage; it is not a simultaneous
several-prime theorem.

The downstream interfaces respect this boundary. Book 177's generic distinct-root
level-raising place is not the scalar family treated here, and its potential-modularity
argument separately records every active place. Book 178 uses precisely Theorem 7.1 on the
augmentation character: its semistable Tate-module point has conductor one, kills the
nilradical, and therefore needs no full scheme-theoretic equality. Book 181 studies a dyadic
signed-special condition with nonzero residual monodromy; it is a different local deformation
problem and cannot import the scalar Kummer family of this book. None of these consumers is
used backwards in the proof.

### 8.4 Frobenius, determinant, and variance

The normalization ledger is fixed as follows.

- Geometric Frobenius satisfies (2.5), and good Hecke polynomials are written as (3.12).
- Book 174's arithmetic-Frobenius equations are translated by $\Phi_v=\varphi_v^{-1}$; the
  monodromy factor changes from $q_v$ to $q_v^{-1}$ at the same time.
- A scalar automorphic twist changes the central character by $\chi^2$, and the corresponding
  two-dimensional Galois twist changes the determinant by $\chi^2$, as in (2.4).
- A stronger deformation condition gives a quotient of the ring for a weaker condition. The
  augmentation maps in (3.4) and (3.7) therefore point from the relative scalar family to its
  conductor-one face.
- The primary--companion duality shift is $[-1]$, as in (3.9).
- Nonzero monodromy is imposed on characteristic-zero points, while the represented schematic
  closure necessarily includes its zero-monodromy boundary.

These conventions are preserved under coefficient extension and solvable restriction.

## 9. Conclusion

The scalar one-prime problem lives at $q_v\equiv1\pmod\ell$. The coincident old roots require
an invariant line and an integral $W_v$-sign; they cannot be separated by the clean-root
idempotent used when $q_v\not\equiv1$. The branch $q_v\equiv-1$ has no nontrivial scalar
$\ell$-power tame character and retains a full two-sign Smith problem instead.

Under $({\rm AUT}_v)$, $({\rm TYPE}_v)$, and $({\rm SUP}_v)$, and with
$({\rm RAY}_v)$ for the scalar family, Book 174 supplies the exact mathematical heart of the
one-prime comparison: the local chart with its Kummer directions, projective primary and
companion complexes, full topological support on every named conductor-one and conductor-two
component, and exact fixed-prime augmentation of modules and faithful acting images. Under
$({\rm REC}_v)$, Book 170 supplies the surjection
from each deformation ring to its faithful finite reduced Hecke order. These inputs prove that
the finite-level kernel is exactly the nilradical, yielding the reduced comparisons (4.3),
(4.4), and (5.9).

Every characteristic-zero deformation point kills that nilradical, so the reduced theorem
proves the one-prime finite-flat modularity statement needed by the arithmetic application.
What the imported source chain does not prove is global reducedness. The scalar family is the
tensor product of the conductor-one line-special problem with $\Lambda_v$ on both deformation
and Hecke sides, so it carries any nilpotent kernel with it. At finite level,
$R^{\mathrm{sp},1}$ is reduced if and only if the canonical comparison is a full equality.
At patched level, Proposition 5.2 gives the full equality under the separately named
$({\rm RED}_\infty)$ hypothesis, and $({\rm AUG}_Q)$ then descends it.

Accordingly, this book's bounded conditional theorem is **READY**: under the exact named
arithmetic hypotheses it proves the reduced one-prime comparisons, strict character
specialization, pointwise conductor-one and conductor-two modularity, and the precise
conditional full $R=T$ criterion. The stronger unconditional catalog assertion remains
unproved, first at the arithmetic localization/type/support inputs above and, even after those
are granted, at global nilpotent control.
