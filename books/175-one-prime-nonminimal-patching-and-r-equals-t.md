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
   - [Generic rigidity: flatness and the exact remaining theorem](#45-generic-rigidity-flatness-and-the-exact-remaining-theorem)
5. [What patching and augmentation do prove](#5-what-patching-and-augmentation-do-prove)
   - [The two-term complex and its Tor term](#51-the-two-term-complex-and-its-tor-term)
   - [Amplitude after Book 174](#52-amplitude-after-book-174)
   - [Balanced patched rigidity](#53-balanced-patched-rigidity)
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
8. [Dependency, circularity, and normalization checks](#8-dependency-circularity-and-normalization-checks)
   - [Direct prerequisite ledger](#81-direct-prerequisite-ledger)
   - [The original circular step and its repair](#82-the-original-circular-step-and-its-repair)
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
kernels up to nilpotents. Book 174 already constructs the simultaneous marked common-boundary
quotient diagram. The support hypothesis still contains the narrower $({\rm BCD}_v)$:
regularity of the named lower boundary block and relative formal smoothness of the special
relaxation, as stated in Section 2.4. Those transversality assertions are not consequences of
the other inputs in this book.

Without using an auxiliary patch, the first result proved below is

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
deformation ring is reduced. Section 4.5 proves vertical torsion-freeness from the balanced
enhanced obstruction presentation and the already established finiteness of the ring. It then
identifies reducedness exactly with the remaining generic-rigidity theorem: vanishing of the
enhanced fixed-condition tangent--Selmer group at every characteristic-zero point. The line is
essential in the residual complex. At a characteristic-zero monodromy-zero point, however,
the two line characters differ by the nonzero scalar $q_v-1$, so the flag tangent is uniquely
determined by the cocycle rather than supplying an additional direction.
Section 5.3 then proves that vanishing, rather than assuming it, when a coherent unpadded
$({\rm AUX}_Q)$ system is separately retained at every depth. The balanced enhanced
calculation gives an absolute deformation source with $q$ variables; the $q$ ordered diamond
directions give a scalar source of the same dimension. The nonzero module is free over the
diamond source, so the equal-variable argument injects the regular deformation source into its
action image. It follows that

$$
R_\infty^{\mathrm{sp},1}=\mathbb T_\infty^{\mathrm{sp},1},
\qquad
R^{\mathrm{sp},1}=\mathbb T^{\mathrm{sp},1},
\tag{1.6}
$$

and hence every characteristic-zero enhanced tangent--Selmer group vanishes. This proof does
not identify the conductor-one augmentation with the neutral minimal problem and does not
assume a reduced patched ring. Under $({\rm RAY}_v)$ it transports to the scalar family and
all fixed-character fibers. It also makes auxiliary acting-order augmentation exact by the
diagram of surjections in Corollary 4.5. If no coherent auxiliary system is available, the
branchwise cross-cotangent condition of Corollary 4.4a remains the exact alternative input;
flatness and topological support alone do not imply it.

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
$\varepsilon_v\in\{1,-1\}$, and the strict tame quotient
$\Delta_v=C_{\ell^{\operatorname{ord}_\ell(q_v-1)}}$ of Book 174, (2.2a)--(2.2d). Put

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
node-uniformization hypothesis and Book 125 component-routing source condition. Relative to
the separate abelian Ihara vanishing, Book 140 proves constant-coefficient generic support.
After the typed integral filtration is available, Book 174, Proposition 6.3 proves the typed
generic-residue kernel equality from the same component-routed Book 125 decomposition; it is
not an additional hypothesis. Torsion-free contraction gives equality of the integral faithful
image orders, and $({\rm NU}_{\rm type})$ transports that equality to the switched typed
lattice. The normalized-branch Smith correction remains distinct from the Néron component
group. Equality of good residual traces is not a substitute for this datum.

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

**$({\rm TYPE}_v)$ (the typed complex).** Use the typed parahoric theorem
$({\rm TPE}_v)$ proved in Book 174 from Book 122's actual-row calculation and strict ray
choice.  The accompanying $({\rm TIC}_v)$ hypothesis and the independent hypothesis
$({\rm TIH}_{\mathscr F})$ hold on every retained finite shadow. The theorem and the first
hypothesis supply the
actual typed incidence diagram, exact flag resolutions and component routing, and the declared
pull--norm inverse-character adjunction. The last says that, for every actual
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
$({\rm SUP}_v)$ in Book 174, Section 8.2, holds. Clauses 1--3 are its boundary-carrier datum,
while clauses 4--5 are the separate relative Cartier-switch theorem $({\rm BCD}_v)$:
(1) the Taylor--Wiles sets are disjoint from
$v$, kill the dual Selmer group, satisfy Book 141's split-regular detector input, and retain
both maps, both type rows, the flag, sign, determinant, and companion pairing in every finite
shadow; (2) the lower clean minimal problem has a nonzero patched module free over its regular
scalar source; (3) the full same-coefficient Gram block is singular at each declared boundary
prime; (4) in Book 174's already constructed common completed quotient diagram, the lower
boundary block is transverse and the special relaxation is relatively formally smooth at
every selected completion; and (5) the resulting local dimension equality and one-component
routing hold there. Section 2.4 gives the exact completed-ring formulation and proves that
clause (5) follows from clause (4). Thus the unresolved mathematical input is the
regular-sequence and formal-smoothness assertions in clause (4), including their full
scalar-block form. The common quotient diagram is a proved marked-patching output, not part of
that remainder. Transversality is not inferred from a reciprocity surjection
or a characteristic-zero packet count. The dual group in clause (1) is the one recomputed from
the enhanced local condition complex (4.7f''), with its exact homotopy orthogonal; it is not
the ordinary dual Selmer group obtained by forgetting the flag.

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

**$({\rm RAY}_v)$ (strict scalar twisting).** Use the quotient
$\Delta_v=C_{\ell^{\operatorname{ord}_\ell(q_v-1)}}$ constructed in Book 174,
(2.2a)--(2.2d), by its odd-exponent local--global construction.  Its conductor places are
included in the fixed spectator datum and the local field is
$F_v(\pi_v^{1/|\Delta_v|})$ with vertical unit $1$.  Book 174's twisting identities then hold
for represented deformation rings, strict complexes, new modules, pairings, and faithful
acting images. This is what proves fixed-prime augmentation. A merely local tame character or
an unspecified cyclic quotient does not suffice.

**$({\rm AUX}_Q)$ (clean auxiliary control).** The Taylor--Wiles set is disjoint from $v$,
its residual Frobenius roots are distinct and ordered, its effective diamond cover is a genuine
torsor, and every retained generic branch has the old--new decomposition, newvector relation,
Galois realization, and exact local compatibility used in the chosen localization. The marked
finite-shadow patch retains the represented rings, both adjoint complexes, their deformation
actions, and their pairings. Under precisely these hypotheses, Book 174, Proposition 9.1
proves that auxiliary augmentation recovers the
represented rings, primary and companion complexes, new modules, actions, and pairings, with
zero positive diamond-algebra Tor. It gives a canonical surjection on faithful acting images,
not injectivity of that surjection. Section 4.5 derives the missing injectivity from generic
rigidity; it is not assumed here and is not inferred formally from module augmentation.
In Proposition 5.2 an **unpadded system** means that at depth $N$ there is a clean auxiliary
shadow with exactly $q$, the common dimension in (5.6b), rather than a padded larger number,
of ordered primes killing the recomputed enhanced dual group. These shadows must satisfy
$({\rm AUX}_Q)$, carry uniformly bounded free ranks and all of the marked action and
augmentation diagrams used below, and exist at every depth. Once that arithmetic family is
given, Book 174's finite-shadow patching and Book 172's diagonal stabilization retain the
complete quotient ideals, module bases, structural diamond maps, deformation actions,
pairings, and exact ring/module augmentation sequences in one coherent subsequence. Thus
coherence of the finite shadows is a formal output; existence of the clean exactly-$q$ shadows
is an additional arithmetic hypothesis, not a transition manufactured between unrelated
prime sets. In particular, the common boundary patch used to prove $({\rm SUP}_v)$ may be
padded. It is not automatically the unpadded system of Proposition 5.2. If one insists on a
single system serving both purposes, one must separately require exactly $q$ common primes at
every depth that kill every relevant dual group and retain the full boundary diagram.
Isolated instances of Proposition 9.1 do not by themselves supply either family.

On the curve-new carrier, the corrected normalized-branch filtration and primitive extreme
residues are needed only if one also invokes their component or lowering consequences. Then
$({\rm AIH}_{\mathscr F})$ and $({\rm PRI}_{\rm type})$ must be added exactly as in Book 174;
$({\rm NU}_{\rm type})$ is additionally required for the switched graph--definite comparison,
as already recorded in $({\rm AUT}_v)$. None is used to identify a Galois cotangent determinant
in this book. The formal reduced comparison below uses
$({\rm AUT}_v)$, $({\rm TYPE}_v)$, $({\rm SUP}_v)$, and $({\rm REC}_v)$; the scalar-family
conclusions add $({\rm RAY}_v)$, while an auxiliary patch uses $({\rm AUX}_Q)$.
Hypothesis $({\rm AIH}_{\mathscr F})$ remains part of the richer level-change
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

We now isolate the exact geometric content of $({\rm BCD}_v)$. Fix one of the boundary points
selected by the boundary-carrier datum. Separate the same formally smooth frame factors in all
three problems, localize at the compatible primes, and complete; the notation below suppresses
only these identical factors. Write

$$
A=\widehat{(R_\infty^{\mathrm{low}})_{\mathfrak r}},
\qquad
D=\widehat{(R_\infty^{\partial})_{\mathfrak p}},
\qquad
B=\widehat{(R_\infty^{\mathrm{sp},1})_{\mathfrak q}}.
\tag{2.9}
$$

At finite level, the represented inclusions of conditions give quotient maps. Book 174,
(8.2d)--(8.2e), places the lower, boundary, and special problems in one marked finite-shadow
patch and proves that the two quotient maps survive in the compatible completed diagram

$$
A\twoheadrightarrow D\twoheadleftarrow B.
\tag{2.10}
$$

There is no asserted map from $A$ to $B$. The diagram is a proved common-quotient statement;
it supplies neither a reverse section nor transversality. Let $S$ be the corresponding
completed regular scalar source for the lower problem. The lower theorem makes $A$ a regular
local domain finite flat over $S$. The same marked quotient construction identifies the
kernel of $A\twoheadrightarrow D$ with the named lower boundary block. The remaining relative
Cartier-switch assertion at this completion is the conjunction of the following two
statements.

1. The named boundary block has length $s\geq1$ and its displayed generators
   $\mathbf u=(u_1,\ldots,u_s)$ form an $A$-regular sequence. The already proved quotient
   identification has the form

   $$
   D\simeq A/(u_1,\ldots,u_s).
   \tag{2.11}
   $$

   In the distinct-line chart $s=1$, so this says in particular that the image of the lower
   boundary equation is a nonzero element $u\in A$. Nonvanishing in the isolated local model
   is not enough: its image must remain nonzero in this completed global lower ring. In a
   scalar chart, every successive $u_i$ must remain a non-zero-divisor after quotienting by
   its predecessors.
2. The quotient $B\twoheadrightarrow D$ admits a continuous section $D\to B$ for which $B$ is
   relatively formally smooth over $D$ of relative dimension $s$. Equivalently, after choosing
   parameters $\mathbf m=(m_1,\ldots,m_s)$ in the kernel of the quotient, the formal inverse
   theorem gives a noncanonical isomorphism

   $$
   B\simeq D[[m_1,\ldots,m_s]]
   \tag{2.12}
   $$

   carrying the boundary quotient to $m_1=\cdots=m_s=0$. This assertion includes vanishing of
   the relative obstruction map. Equality of tangent dimensions without that vanishing does
   not imply (2.12), and the quotient $B\twoheadrightarrow D$ by itself does not supply the
   required section.

For a distinct residual line, equations (2.11)--(2.12) read

$$
D\simeq A/(u),
\qquad
u\ne0,
\qquad
B\simeq D[[m]].
\tag{2.13}
$$

At a scalar residual point, $\mathbf u$ and $\mathbf m$ are equal-length blocks. The
isomorphisms are taken over the whole retained scalar base: the invariant line, unramified and
tame Kummer directions, determinant, sign, and the common frame variables all remain present.
The frame factors suppressed in (2.9) are carried identically and may be restored on both
sides. The blocks are not replaced by one signed Gram factor. The strict scalar ray family is then obtained
by the finite flat base change along $\mathcal O\to\Lambda_v$; regular sequences and formal
smoothness persist under that base change.

**Proposition 2.1 (formal consequences of relative Cartier-switch transversality).** Assume
(2.11)--(2.12) at a selected boundary completion. Let
$\mathfrak d_1,\ldots,\mathfrak d_t$ be the minimal primes of $D$, let
$\widetilde{\mathfrak d}_i\subset A$ be their inverse images, and put

$$
\mathfrak q_i
=\mathfrak d_iB+(m_1,\ldots,m_s),
\qquad
\mathfrak s_i=\widetilde{\mathfrak d}_i\cap S.
\tag{2.14}
$$

Then the irreducible components of $B$ are precisely
$V(\mathfrak d_iB)$. The prime $\mathfrak q_i$ lies on only
$V(\mathfrak d_iB)$, and

$$
\dim B=\dim A,
\qquad
\dim B_{\mathfrak q_i}=s
=\dim S_{\mathfrak s_i}.
\tag{2.15}
$$

Thus every special component has a boundary point with unique component routing, and the
localized special ring and lower scalar source have the dimension equality required by the
one-boundary support argument. The same conclusion holds for the scalar block of any length
$s$.

**Proof.** Since $A$ is regular, it is Cohen--Macaulay. The regular sequence $\mathbf u$ has
height $s$, so every prime $\widetilde{\mathfrak d}_i$ minimal over
$(\mathbf u)$ has height $s$. The finite flat map $S\to A$ has zero-dimensional fibers and
satisfies the dimension formula. Hence $\mathfrak s_i$ also has height $s$, and the regularity
of $S$ gives

$$
\dim S_{\mathfrak s_i}=s.
\tag{2.16}
$$

Equation (2.12) shows that the minimal primes of $B$ are exactly the extensions
$\mathfrak d_iB$. If $\mathfrak d_jB\subseteq\mathfrak q_i$, contraction to $D$ gives
$\mathfrak d_j\subseteq\mathfrak d_i$; minimality forces $j=i$. Thus
$\mathfrak q_i$ lies on exactly one irreducible component. Moreover

$$
B/\mathfrak d_iB\simeq
(D/\mathfrak d_i)[[m_1,\ldots,m_s]],
$$

and the image of $\mathfrak q_i$ is the prime generated by the $s$ power-series variables.
Those variables form a regular sequence, so $\dim B_{\mathfrak q_i}=s$. Finally, quotienting
$A$ by $s$ regular elements lowers dimension by $s$, and adjoining $s$ formal variables
restores it:

$$
\dim B=\dim D+s=\dim A.
$$

This proves (2.15) and the routing assertion. The argument uses only the length of the two
blocks, so it also proves the scalar-block statement. $\square$

The proposition proves the local dimension equality and component routing once the two
transversality statements are known. It does not prove those statements from the other named
hypotheses. Book 174 supplies the compatible completed quotient diagram (2.10) and the named
quotient ideals. General deformation theory supplies a criterion for relative formal
smoothness. No cited result proves that $\mathbf u$ remains regular in $A$ or that the actual
relative obstruction map vanishes and a section exists. Accordingly $({\rm BCD}_v)$, and
hence every support or comparison theorem that assumes $({\rm SUP}_v)$, remains conditional
on the regularity assertion in (2.11) and on (2.12), not on the existence of (2.10).

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
conclusion, because $({\rm SUP}_v)$ is not established by the residual datum alone and its
$({\rm BCD}_v)$ clause remains exactly the regularity assertion in (2.11) together with
(2.12), over the proved quotient diagram (2.10).

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
to be reduced. Theorem 4.2 deliberately makes no patched reducedness claim from support.
Section 5.3 instead retains the coherent unpadded auxiliary system and proves a full patched
equality
from the sharp absolute generator count and the faithful diamond-scalar action; it assumes
neither reducedness of the patched acting image nor reducedness of the patched deformation
ring.

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

At this stage the missing condition is global reducedness. The local ring $R_0[[m]]$ in (3.2) is reduced
when $R_0$ is reduced, but a global quotient of a reduced power-series source can be
nonreduced. Equidimensionality and a reduced generic Hecke algebra do not rule out such a
nilpotent thickening. No prior theorem proves that the global ring
$R^{\mathrm{sp},1}$ is reduced.

Consequently Corollary 4.3 by itself is a reusable criterion. Proposition 5.2 proves its
hypothesis from the coherent unpadded balanced auxiliary patch; without that patch, reducedness
is not
a consequence of the local chart or of the reduced comparison.

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

### 4.5 Generic rigidity: flatness and the exact remaining theorem

The phrase *global reducedness* can be replaced by a precise arithmetic statement. Put

$$
R=R^{\mathrm{sp},1},
\qquad
T=\mathbb T^{\mathrm{sp},1},
\qquad
K=\ker(R\twoheadrightarrow T).
$$

Under Theorem 4.2, $K=\sqrt{(0)}$. Since $R$ is noetherian, $K$ is nilpotent. Moreover $R$ is
finite over $\mathcal O$. Indeed, $T$ is a finite $\mathcal O$-module and, for $K^n=0$, every
quotient $K^j/K^{j+1}$ is a finite module over $R/K=T$. Induction through

$$
0\longrightarrow K^j/K^{j+1}
\longrightarrow R/K^{j+1}
\longrightarrow R/K^j\longrightarrow0
\tag{4.7}
$$

proves the assertion. Thus $R_E=R[1/\varpi]$ is an Artinian $E$-algebra.

The coefficient-torsion part of generic rigidity is already forced by this finiteness and the
balanced enhanced obstruction calculation.  We first isolate the commutative algebra.  This is
the finite-flat endpoint of the balanced Böckle-presentation argument; it is included here
because it is sensitive to the coefficient parameter and does not use $R=T$.

**Lemma 4.3a (a finite balanced presentation is coefficient-flat).** Let $A$ be a nonzero
complete noetherian local $\mathcal O$-algebra with residue field finite over $k$.  Suppose
$A$ is finite over $\mathcal O$ and has a presentation

$$
A\simeq
\mathcal O[[X_1,\ldots,X_h]]/(f_1,\ldots,f_r),
\qquad r\leq h.
\tag{4.7a}
$$

Then $r=h$, the sequence

$$
f_1,\ldots,f_h,\varpi
\tag{4.7b}
$$

is regular in $\mathcal O[[X_1,\ldots,X_h]]$, and $A$ is finite free over $\mathcal O$.

**Proof.** Put $P=\mathcal O[[X_1,\ldots,X_h]]$ and
$J=(f_1,\ldots,f_r,\varpi)$.  Since $A/\varpi A$ is a nonzero finite local algebra over the
residue field, $J$ is $\mathfrak m_P$-primary.  Hence

$$
h+1=\operatorname{ht}(\mathfrak m_P)
\leq r+1
$$

by the generalized principal ideal theorem.  Thus $h\leq r$, and the assumed opposite
inequality gives $r=h$.  The regular local ring $P$ is Cohen--Macaulay, so the
$\mathfrak m_P$-primary list (4.7b), whose length is $\dim P=h+1$, is a system of parameters
and hence a regular sequence.  In particular $\varpi$ is a nonzerodivisor on
$P/(f_1,\ldots,f_h)=A$.  A finite torsion-free module over a DVR is free. $\square$

We now verify that the presentation hypothesis is the one belonging to the represented
line-special problem, rather than to a coarse condition that forgets the flag.

**Proposition 4.3b (vertical torsion-freeness of the conductor-one ring).** Under the
hypotheses of Theorem 4.2, the structural map

$$
R^{\mathrm{sp},1}\longrightarrow R^{\mathrm{sp},1}[1/\varpi]
\tag{4.7c}
$$

is injective.  More precisely, $R^{\mathrm{sp},1}$ is a finite free relative complete
intersection over $\mathcal O$.

**Proof.** The clean lower problem used in $({\rm SUP}_v)$ has the effective local condition
complexes and balanced global obstruction calculation of Books 69 and 171--172.  Replacing its
condition at $v$ by the represented scalar line-special condition does not change the virtual
local defect, but this must be checked on the enhanced complex.

Use the scalar chart of Book 174, equations (7.6)--(7.8), and fix the two line characters and
the determinant branch.  The latter determines the common unramified scalar $a$, because
$2a$ is a unit.  In the fixed ambient frame every enhanced special lift is then described by
three freely liftable parameters

$$
b\quad\text{(unramified upper extension)},\qquad
m\quad\text{(tame monodromy)},\qquad
z\quad\text{(the line)},
\tag{4.7d}
$$

through

$$
N(z)=
\begin{pmatrix}-mz&m\\-mz^2&mz\end{pmatrix},
\qquad
F(z)=
\begin{pmatrix}
q_va-bz&b\\
z((q_v-1)a-bz)&a+bz
\end{pmatrix}.
\tag{4.7e}
$$

Here $F=\rho(\phi_v)$ is arithmetic Frobenius, as in Book 174's local chart; the
geometric-Frobenius convention (2.5) is obtained by inversion.

These formulas satisfy the tame relation identically, and conversely an adapted generator of
the retained line puts every lift uniquely in this form.  Thus this framed enhanced local
condition is formally smooth of relative dimension three.  It also supplies the complete
small-extension lifting and difference-torsor data required in Book 69: lift $b,m,z$
arbitrarily, and compare two lifts coordinatewise.  No tangent-subspace shortcut is being used.
The reductions of $b$ and $m$ are exactly the exceptional unramified and tame Kummer
directions mentioned in Book 174, (7.10); neither has been deleted. In that residual tangent
calculation the displayed relation $(1-q_v)x=0$ is zero in $k$ because
$q_v\equiv1\pmod\ell$. It is not an integral equation $(q_v-1)m=0$: the integral
Frobenius eigenratio in (4.7e) is exactly $q_v$, so the tame relation holds identically for
every $m$. Integrally, an upper strict change of adapted vector changes $b$ by a multiple of
$q_v-1$, but this is a gauge action on the smooth framed chart, not an additional local
equation.

At the scalar residual point, trace-zero infinitesimal conjugation has dimension three.  Its
map to the three coordinates in (4.7d) has rank one: the lower-left entry moves $z$, while a
commutator with the scalar residual representation is zero. In particular, the integral
$(q_v-1)$-multiple just noted has zero residual derivative and is correctly retained in this
complex. Its kernel is the two-dimensional
trace-zero parabolic preserving the residual line.  Consequently the enhanced local condition
complex has

$$
\dim_k H^0(\mathcal U_v^\bullet)=2,
\qquad
\dim_k H^1(\mathcal U_v^\bullet)=2,
\qquad
\chi(\mathcal U_v^\bullet)=0.
\tag{4.7f}
$$

The pure residual flag direction is present before quotienting, but it is accompanied by the
corresponding change in the infinitesimal automorphism term.  Deleting the flag would therefore
give the wrong complex even though the virtual number in (4.7f) happens to be zero. Equivalently,
in Book 69's partially framed convention the contribution is computed before local quotienting:

$$
\dim_k t_v^{\square,\mathrm{enh}}-\dim_k\operatorname{ad}^0\bar\rho
=3-3=0.
\tag{4.7f'}
$$

This form keeps the full comparison frame and is the one used in the Taylor--Wiles generator
count.

For clarity, form the enhanced deformation complex before taking cohomology. At $v$ its local
condition term is the two-term complex

$$
\mathcal U_v^\bullet=
[\operatorname{ad}^0\bar\rho\longrightarrow
k\!\cdot b\oplus k\!\cdot m\oplus k\!\cdot z],
\tag{4.7f''}
$$

whose arrow is infinitesimal conjugation of the representation and line. Insert this term,
with the effective condition complexes at the other places, into Book 69's mapping fiber from
global cochains to the forbidden local quotients. Its degree-one cohomology is the tangent of
the represented global pair $(\rho,L)$ modulo simultaneous strict conjugation. The explicit
coordinate lifting above proves the required small-extension lifting and difference-torsor
axioms at $v$; hence degree two is a complete effective obstruction space, rather than a
formal tangent-subspace surrogate.
The dual local condition is the homotopy orthogonal of (4.7f'') under the local Tate pairing,
not the annihilator of a prematurely chosen subspace of ordinary $H^1$. Because
$\mathcal U_v^\bullet$ is a finite perfect two-term complex, Book 69's perfect cone duality
applies and identifies the dual of the global degree-two term with the recomputed enhanced
dual group used in $({\rm SUP}_v)$.

All other finite places retain the neutral effective complexes of the clean lower datum. The
finite-flat places above $\ell$ contribute $+[F:\mathbf Q]$, the odd real places contribute
$-[F:\mathbf Q]$, and (2.1)--(2.2) remove degree-zero global automorphisms and the dual
degree-three endpoint. The Euler characteristic of this mapping fiber is therefore zero,
because (4.7f) contributes zero at $v$. Thus, writing it as $C_{\mathcal E}^\bullet$,

$$
0=\chi(C_{\mathcal E}^\bullet)
=-\dim_kH^1(C_{\mathcal E}^\bullet)
+\dim_kH^2(C_{\mathcal E}^\bullet).
\tag{4.7f'''}
$$

Poitou--Tate duality for the complex consequently makes its tangent and complete-obstruction
spaces have the same dimension, say $h$. Book 69's
effective relation-obstruction map gives a presentation

$$
R\simeq\mathcal O[[X_1,\ldots,X_h]]/(f_1,\ldots,f_r),
\qquad r\leq h.
\tag{4.7g}
$$

This is the enhanced problem: the local term used to obtain (4.7g) is (4.7f), not an ordinary
subspace of $H^1(F_v,\operatorname{ad}^0\bar\rho)$.

The paragraph preceding Lemma 4.3a proved that $R$ is finite over $\mathcal O$.  Apply that
lemma to (4.7g).  It makes $\varpi$ a nonzerodivisor and proves the asserted finite freeness and
complete-intersection statement. $\square$

Let $x$ be any maximal point of $R_E$, with residue field $E_x$, and let $\rho_x$ and
$L_x\subset V_x$ be the corresponding representation and retained line at $v$. The line must
remain in the tangent problem. Define

$$
H^{1,\mathrm{enh}}_{\mathcal E_x}
\!\left(F,\operatorname{ad}^0\rho_x\right)
$$

to be the following exact enhanced tangent--Selmer space. Its cocycles are pairs
$(c,\lambda)$ with

$$
c\in Z^1\!\left(G_{F,S},\operatorname{ad}^0\rho_x\right),
\qquad
\lambda\in\operatorname{Hom}_{E_x}(L_x,V_x/L_x).
$$

Away from $v$, the localization of $c$ must lie in the actual tangent of the base-changed
represented local condition. At $v$, the pair $(c|_{G_{F_v}},\lambda)$ must satisfy the full
linearization of the enhanced line, character, determinant, and monodromy-incidence equations
of Book 174, Chapter 7. Divide these pairs by infinitesimal global strict conjugation, acting
simultaneously on the cocycle and on the line. This is a kernel modulo coboundaries, as an
ordinary Selmer group is, but it retains the possible pure flag direction. Book 67, Section
8.4 explains why that direction cannot be discarded when the line characters coincide.

The dual-number cocycle-and-line calculation, applied over $E_x$, gives a canonical
identification

$$
\operatorname{Hom}_{E_x}
\left(\mathfrak m_x/\mathfrak m_x^2,E_x\right)
\xrightarrow{\sim}
H^{1,\mathrm{enh}}_{\mathcal E_x}
\!\left(F,\operatorname{ad}^0\rho_x\right).
\tag{4.8}
$$

Here $\mathfrak m_x$ is the maximal ideal in the local Artin factor of $R_E$ at $x$.
Because $R$ is finite over $\mathcal O$, no convergence or integral scalar-extension issue is
hidden here. The extension $E_x/E$ is finite separable, so the relative cotangent of the
residue field vanishes and a tangent vector is exactly an $E$-derivation from the local factor
of $R_E$ to $E_x$, equivalently a functional on $\mathfrak m_x/\mathfrak m_x^2$. Evaluate such
a derivation on the universal representation and retained line.
Multiplicativity gives the cocycle $c$, moving the line gives $\lambda$, and differentiating
the represented local equations gives precisely the conditions just stated. Conversely a pair
satisfying those linearized equations defines a derivation of a matrix-and-line presentation
of the represented global ring. These constructions are inverse. The representation $\rho_x$
is absolutely irreducible: Theorem 4.2 makes the point factor through the noncharacter
automorphic order in $({\rm AUT}_v)$, whose generic packet representation has scalar
endomorphisms. Consequently infinitesimal changes of representative are exactly global
coboundaries, so the identification is independent of the chosen presentation. This is Book
69's tangent--Selmer calculation with Book 67's enhanced-line term retained.

The enhancement cannot be deleted in the residual presentation, but it introduces no
independent characteristic-zero tangent, even at the monodromy-zero boundary. Indeed the two
line characters at every point $x$ are $q_va_x$ and $a_x$. Since $q_v>1$ is an integer and
$a_x$ is a unit,

$$
(q_v-1)a_x\in E_x^\times.
\tag{4.8a}
$$

Let $F_x$ act by $q_va_x$ on $L_x$ and by $a_x$ on $V_x/L_x$. Projecting the linearized
eigenline equation to $V_x/L_x$ gives

$$
((q_v-1)a_x)\lambda
=u_x\operatorname{pr}_{V_x/L_x}\bigl(c(\phi_v)|_{L_x}\bigr),
\qquad u_x\in E_x^\times,
\tag{4.8b}
$$

where $u_x=q_va_x$ for the convention
$\rho_\epsilon(g)=(1+\epsilon c(g))\rho_x(g)$; the inverse convention changes this harmless
unit and its sign. Thus
$\lambda$ is uniquely determined by the local cocycle. When $N_x\ne0$, the same conclusion
also follows from $L_x=\operatorname{im}N_x=\ker N_x$; when $N_x=0$, equation (4.8b) supplies
the missing argument. Hence forgetting $\lambda$ identifies the enhanced group with the
ordinary adjoint Selmer group for the **exact closed special tangent at every
characteristic-zero point**. This does not justify forgetting the line integrally or
residually: modulo $\varpi$, $q_v-1=0$ and (4.8b) no longer determines $\lambda$.

Define the remaining arithmetic assertion as

$$
({\rm ASV}_v):\qquad
H^{1,\mathrm{enh}}_{\mathcal E_x}
(F,\operatorname{ad}^0\rho_x)=0
\quad\text{for every maximal point }x\text{ of }R_E.
\tag{4.8c}
$$

For compatibility with the intrinsic formulation, put

$$
({\rm GR}_v):
\quad
\begin{cases}
R\longrightarrow R[1/\varpi]\text{ is injective};\\[2mm]
H^{1,\mathrm{enh}}_{\mathcal E_x}
(F,\operatorname{ad}^0\rho_x)=0
\text{ for every maximal point }x\text{ of }R_E.
\end{cases}
\tag{4.9}
$$

The first clause is vertical torsion-freeness and is now Proposition 4.3b. It remains in the
definition so that $({\rm GR}_v)$ keeps its intrinsic ring-theoretic meaning under base change.
The second clause is $({\rm ASV}_v)$, the exact remaining arithmetic assertion. It is rigidity
of every generic enhanced fixed-condition point; by (4.8b) it may equivalently be computed
with the ordinary cocycle for the exact closed special tangent, including at $m=0$, but not
with a condition specified only by conductor.

**Theorem 4.4 (generic rigidity is exactly full $R=T$).** Under the hypotheses of
Theorem 4.2, the following are equivalent:

1. $({\rm ASV}_v)$ holds;
2. $({\rm GR}_v)$ holds;
3. $R^{\mathrm{sp},1}$ is reduced;
4. the canonical map
   $R^{\mathrm{sp},1}\xrightarrow{\sim}\mathbb T^{\mathrm{sp},1}$ is an isomorphism.

If $({\rm RAY}_v)$ also holds, these are equivalent to the full scalar-family equality in
Corollary 4.3.

**Proof.** Proposition 4.3b makes statements 1 and 2 equivalent. Assume $({\rm ASV}_v)$.
By (4.8), every local Artin factor $A_x$ of $R_E$ has
zero Zariski tangent space. If $\mathfrak n_x$ is its maximal ideal, then
$\mathfrak n_x/\mathfrak n_x^2=0$. Nakayama's lemma gives $\mathfrak n_x=0$, so every
$A_x$ is its residue field. Hence $R_E$ is a product of finite field extensions of $E$ and is
reduced. Proposition 4.3b and Lemma 4.1a now show that $R$ is reduced.

The equivalence of statements 3 and 4 is Theorem 4.2. If statement 4 holds, then $R=T$ is
$\mathcal O$-torsion-free. Its generic fiber is a finite reduced algebra in characteristic
zero, hence a product of finite separable fields and has zero tangent space at every maximal
point. Equation (4.8) gives $({\rm ASV}_v)$, completing the cycle of implications. The
scalar-family assertion is Corollary 4.3. $\square$

There is an equivalent integral formulation that identifies the precise output required from
any automorphic adjoint-Selmer or cross-determinant theorem.  For a maximal point $x$, enlarge
coefficients so that its field $E_x$ has valuation ring $\mathcal O_x$ and let

$$
\lambda_x:R\widehat\otimes_{\mathcal O}\mathcal O_x
\longrightarrow\mathcal O_x
$$

be the integral branch map.  Put $\mathfrak p_x=\ker\lambda_x$ and

$$
\Phi_x^{\rm Gal}=\mathfrak p_x/\mathfrak p_x^2.
\tag{4.9a}
$$

**Corollary 4.4a (the exact branchwise cotangent target).** Under the hypotheses of
Theorem 4.2, the following are equivalent:

1. $({\rm ASV}_v)$;
2. $\Phi_x^{\rm Gal}$ is a torsion $\mathcal O_x$-module for every $x$;
3. $\operatorname{Fitt}_{\mathcal O_x}^0(\Phi_x^{\rm Gal})\ne0$ for every $x$.

Consequently it is enough to construct, before using $R=T$, an injection of
$\Phi_x^{\rm Gal}$ into a finite automorphic congruence module, or a determinant comparison
that makes its zeroth Fitting ideal nonzero. This is the exact reusable
**cross-cotangent theorem** needed by a proof that does not retain the coherent auxiliary
patch. Proposition 5.2 supplies the same vanishing simultaneously at all branches by a
different, global equal-variable argument.

**Proof.** Finite scalar extension and separability give

$$
\Phi_x^{\rm Gal}\otimes_{\mathcal O_x}E_x
\simeq\mathfrak m_x/\mathfrak m_x^2.
\tag{4.9b}
$$

Equations (4.8) and (4.9b) identify the dual of this generic fiber with the enhanced
tangent--Selmer group.  Thus it vanishes exactly when $\Phi_x^{\rm Gal}$ is torsion.  For a
finite module over a DVR, torsion is equivalent to a nonzero zeroth Fitting ideal. $\square$

Theorem 4.4 and Proposition 4.3b identify the exact additional theorem required before the
coherent auxiliary patch is invoked: prove the characteristic-zero exact-condition adjoint
Selmer vanishing in (4.9) at every point. It cannot be recovered from support, local
reducedness, adequacy, or generic packet semisimplicity alone. Nor can one replace vanishing at
every maximal point by generic smoothness on a dense open: a finite Artin algebra is reduced
only when the maximal ideal in every local factor vanishes. The maps

$$
\mathcal O[\eta]/(\eta^2)\twoheadrightarrow\mathcal O,
\qquad
\mathcal O[\eta]/(\eta^2,\varpi\eta)\twoheadrightarrow\mathcal O
\tag{4.10}
$$

show the two logically independent failures before Proposition 4.3b is used. The first source
is a finite flat balanced complete intersection but has a nonreduced generic fiber; it proves
that the remaining Selmer theorem needs genuinely global input. The second has reduced generic
fiber but nonzero vertical torsion; its presentation has one variable and needs two relations, so it is excluded
precisely by the balanced relation bound. In both examples the kernel is nilpotent and the
target carrier has full topological support over the source. Neither example carries the
equal-dimensional faithful diamond action used in Proposition 5.2.

**Corollary 4.5 (exact auxiliary acting-order augmentation).** Assume $({\rm AUX}_Q)$ and
$({\rm GR}_v)$. For $i=2$, assume $({\rm RAY}_v)$ as well. Let
$\mathfrak a_Q\subset\Lambda_Q$ be the auxiliary augmentation ideal and let
$\mathbb T_{Q,v}^{\mathrm{sp},i}$ be the faithful auxiliary acting order. Then

$$
\boxed{
\mathbb T_{Q,v}^{\mathrm{sp},i}/
\mathfrak a_Q\mathbb T_{Q,v}^{\mathrm{sp},i}
\xrightarrow{\sim}
\mathbb T_v^{\mathrm{sp},i}.}
\tag{4.11}
$$

**Proof.** Book 174, Proposition 9.1 gives represented-ring augmentation and exact
primary--companion module augmentation. Compatible trace and structural generators give the
two surjections

$$
R_v^{\mathrm{sp},i}
\simeq R_{Q,v}^{\mathrm{sp},i}/\mathfrak a_QR_{Q,v}^{\mathrm{sp},i}
\twoheadrightarrow
B_{Q,v}^{i}:=
\mathbb T_{Q,v}^{\mathrm{sp},i}/
\mathfrak a_Q\mathbb T_{Q,v}^{\mathrm{sp},i}
\twoheadrightarrow
\mathbb T_v^{\mathrm{sp},i}.
\tag{4.12}
$$

Their composite is the base reciprocity map. It is an isomorphism by Theorem 4.4 for $i=1$
and by Corollary 4.3 for $i=2$. A composite of two surjections can be injective only if both
maps are injective, so both arrows in (4.12) are isomorphisms. This proves (4.11). $\square$

Consequently

$$
R_{Q,v}^{\mathrm{sp},i}/\mathfrak a_QR_{Q,v}^{\mathrm{sp},i}
\simeq R_v^{\mathrm{sp},i}
\simeq B_{Q,v}^i
\simeq\mathbb T_v^{\mathrm{sp},i}
\tag{4.13}
$$

is reduced, and Proposition 9.1 of Book 174 identifies the augmented primary--companion
carrier with the base carrier. The common ring in (4.13) acts faithfully on that carrier, so
its annihilator is zero and its support is the whole spectrum scheme-theoretically. This is
the required reduced-source support. Thus faithful Hecke-order equality,
primary/companion augmentation, and auxiliary acting-order augmentation introduce no further
theorem once $({\rm GR}_v)$ is known under the already stated $({\rm AUX}_Q)$ and, for the
scalar family, $({\rm RAY}_v)$ hypotheses. Fixed-prime acting-order augmentation was already proved
by the global twist, and minimal acting-order augmentation is derived after patched
faithfulness in Book 172.

There is one different use of the phrase *faithful-order equality*. Equality between the
curve-new and switched definite image orders is already the conditional conclusion of Book
140, Theorem 8.1, after its localized abelian Ihara, node-uniformization, and Book 125 routing
inputs are supplied in the constant block. For the typed block, Book 174, Proposition 6.3
proves the generic kernel equality after its typed filtration, contracts it to equality of
integral faithful image orders, and uses $({\rm NU}_{\rm type})$ to transport the equality to
the switched lattice. That realization comparison enters here through $({\rm AUT}_v)$ and is
not another consequence or requirement of $({\rm GR}_v)$.

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

### 5.3 Balanced patched rigidity

The balanced calculation used for Proposition 4.3b supplies more than coefficient flatness
when the separately hypothesized coherent unpadded auxiliary system is retained. It gives an
absolute regular source with exactly as many variables as the diamond source. The
equal-variable argument of Book 172 can therefore be run on the one-prime new module itself;
it never identifies the conductor-one augmentation with the neutral minimal problem.

**Proposition 5.2 (balanced patched one-prime $R=T$).** Assume the hypotheses of Theorem 4.2
on the base problem. At every Taylor--Wiles depth, assume $({\rm TYPE}_v)$ and
$({\rm AUX}_Q)$ for the unpadded system specified in Section 2.3, including the represented
deformation actions and auxiliary local--global compatibility retained there. This unpadded
system need not be the potentially padded common-boundary system used to establish
$({\rm SUP}_v)$.
Let $\mathbb T_\infty^{\mathrm{sp},1}$ be the actual image of the patched deformation action
on the primary new module (equivalently, after the proof, on the primary--companion sum). Then,
for the conductor-one problem,

$$
R_\infty^{\mathrm{sp},1}
=\mathbb T_\infty^{\mathrm{sp},1},
\qquad
R^{\mathrm{sp},1}=\mathbb T^{\mathrm{sp},1}.
\tag{5.6a}
$$

The patched ring is regular and finite free over its diamond source, the patched primary
module is nonzero finite free over it, and
the finite conductor-one ring is a finite free complete intersection over $\mathcal O$.
Consequently $({\rm ASV}_v)$ and $({\rm GR}_v)$ hold.  If $({\rm RAY}_v)$ also holds, the
same full equalities hold for the patched and finite scalar family and every retained
fixed-character fiber, and every characteristic-zero enhanced fixed-condition tangent space
on those fibers vanishes.

**Proof.** Let

$$
q=\dim_k H^1_{\mathcal E}^{\mathrm{enh}}
(F,\operatorname{ad}^0\bar\rho)
=\dim_k H^2_{\mathcal E}^{\mathrm{enh}}
(F,\operatorname{ad}^0\bar\rho)
\tag{5.6b}
$$

be the common tangent and complete-obstruction dimension from the balanced calculation in the
proof of Proposition 4.3b; the notation refers to the enhanced mapping fiber constructed after
(4.7f''). The unpadded-system clause of $({\rm AUX}_Q)$ supplies a set $Q_N$ of exactly $q$
Taylor--Wiles primes at every depth killing the recomputed enhanced dual group, while
retaining the flag and the two type rows.
In particular, applicability of Book 143's split detector to this exact enhanced dual group is
part of the stated auxiliary hypothesis; it is not inferred by forgetting the flag. Each
ordered auxiliary condition contributes one local diamond direction.
The enhanced Poitou--Tate count of Proposition 4.3b, combined with Book 143's
one-dimensional local auxiliary change and the killed enhanced dual group, then makes the
auxiliary tangent dimension exactly $q$. Topological Nakayama therefore gives, after the
common coordinates have been marked, a surjection from the regular domain

$$
P=\mathcal O[[X_1,\ldots,X_q]]
\twoheadrightarrow R_{Q_N,v}^{\mathrm{sp},1}
\tag{5.6c}
$$

at every retained depth.  As in Book 172, patch the complete quotient ideals rather than an
unjustified fixed list of equations.  This gives

$$
R_\infty^{\mathrm{sp},1}=P/I_\infty.
\tag{5.6d}
$$

The auxiliary diamond source is

$$
S_\infty=\mathcal O[[Z_1,\ldots,Z_q]].
\tag{5.6e}
$$

Write $\mathfrak a_\infty=(Z_1,\ldots,Z_q)\subset S_\infty$, and use the same symbol
below for the ideal generated by its image under the structural map to a patched ring. It need
not be the ideal $(X_1,\ldots,X_q)$ in the absolute source $P$.

Book 174's split-amplitude theorem, its marked finite-shadow construction, and
$({\rm AUX}_Q)$ patch the primary new modules, their bases, and their deformation actions.
Equation (5.6) becomes

$$
M_\infty^{\mathrm{sp},1}\simeq S_\infty^{\oplus r}
\qquad(r>0).
\tag{5.6f}
$$

Here $r>0$ follows from exact auxiliary module augmentation: the unpadded module specializes
to the nonzero base primary module in $({\rm AUT}_v)$, so its free rank cannot be zero. Let

$$
A_\infty=\operatorname{im}\left(
P\longrightarrow R_\infty^{\mathrm{sp},1}
\longrightarrow
\operatorname{End}_{S_\infty}(M_\infty^{\mathrm{sp},1})
\right).
\tag{5.6g}
$$

It is finite over $S_\infty$.  Auxiliary local--global compatibility identifies the composite
$S_\infty\to P\to A_\infty$ with scalar multiplication on (5.6f), so it is injective.  Hence

$$
\dim A_\infty=\dim S_\infty=q+1=\dim P.
\tag{5.6h}
$$

The ring $P$ is a noetherian local domain. Any nonzero kernel of
$P\twoheadrightarrow A_\infty$ would have positive height and make the quotient have dimension at most $q$,
contradicting (5.6h).  Therefore

$$
P\xrightarrow{\sim}A_\infty,
\qquad I_\infty=0,
\qquad R_\infty^{\mathrm{sp},1}=P.
\tag{5.6i}
$$

This kills nilpotents directly from the regular source; topological component support is not
being promoted to faithfulness.

Since $A_\infty=P$ is finite and local over $S_\infty$, the ideal
$\mathfrak m_{S_\infty}P$ is $\mathfrak m_P$-primary, so depth of a finite $P$-module may be
computed over either local ring. The regular ring $P$ therefore has depth $q+1$ over
$S_\infty$, and Auslander--Buchsbaum over the regular ring $S_\infty$ makes $P$ finite free
over $S_\infty$. Equation (5.6f) has depth $q+1$ over $P$, and Auslander--Buchsbaum over the
regular ring $P$ makes $M_\infty^{\mathrm{sp},1}$ finite free of positive rank over $P$. The
exact finite-level augmentations in $({\rm AUX}_Q)$, retained in the marked inverse-limit
quotient sequences as in Book 172, give

$$
R_\infty^{\mathrm{sp},1}/\mathfrak a_\infty
R_\infty^{\mathrm{sp},1}\simeq R^{\mathrm{sp},1},
\qquad
M_\infty^{\mathrm{sp},1}/\mathfrak a_\infty
M_\infty^{\mathrm{sp},1}\simeq M^{\mathrm{sp},1}.
\tag{5.6j}
$$

Quotienting the free $R_\infty^{\mathrm{sp},1}$-module therefore makes
$M^{\mathrm{sp},1}$ a nonzero free $R^{\mathrm{sp},1}$-module. Its deformation action is
faithful. The order in $({\rm REC}_v)$ is defined on the primary--companion sum, but its
kernel is the intersection of the two summand kernels and is therefore already zero on the
primary summand. Hence the canonical surjection
$R^{\mathrm{sp},1}\twoheadrightarrow\mathbb T^{\mathrm{sp},1}$ is injective and hence an isomorphism. Notice that no acting-image
augmentation was used in this descent; its injectivity follows afterward from Corollary 4.5.

The action image in (5.6g) is therefore the declared
$\mathbb T_\infty^{\mathrm{sp},1}$. Theorem 4.4 now gives $({\rm ASV}_v)$ and
$({\rm GR}_v)$. Under $({\rm RAY}_v)$, equations (3.3), (3.5), and (3.6), at every finite
shadow and hence after patching, tensor these equalities with $\Lambda_v$; strict character
specialization then gives every fixed-character equality. The generic fiber of each resulting
faithful order is reduced, so the fixed-character version of (4.8) also gives the asserted
enhanced tangent--Selmer vanishing. $\square$

Without a coherent unpadded balanced auxiliary system, full support plus an independently
reduced patched ring would still make the patched action faithful. That support-only criterion is
valid but weaker: local reducedness, Cohen--Macaulayness, or a reduced finite Hecke order alone
does not prove reducedness of an abstract patched quotient. Proposition 5.2 avoids that gap by
starting with the regular domain $P$ and proving that its action kernel is zero by the exact
variable count.

### 5.4 Fixed-prime and auxiliary augmentation

There are two independent augmentations. The fixed-prime map is $\epsilon_v$ from (2.3). The
auxiliary map sends every Taylor--Wiles diamond operator to one. Book 174 proves the
fixed-prime statements under $({\rm RAY}_v)$ from the genuine global twist and coefficient
extraction.
Under $({\rm AUX}_Q)$, Book 174, Proposition 9.1 proves the auxiliary statements for represented
rings, primary and companion complexes, new modules, deformation actions, and pairings. Both
maps are marked on the finite complexes and their actions before passing to the patch.

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

For auxiliary augmentation, Proposition 9.1 therefore stops at the canonical surjection on
acting images. Corollary 4.5 proves that this surjection is an isomorphism under
$({\rm GR}_v)$, with $({\rm RAY}_v)$ also retained for the scalar family: the augmented
deformation ring surjects onto the augmented acting order and then onto the faithful base
order, while the composite is the full base $R=T$ isomorphism. Proposition 5.2 supplies
$({\rm GR}_v)$ whenever the coherent unpadded balanced $({\rm AUX}_Q)$ system is retained, so
exact
acting-image augmentation is a conclusion in that range, not an additional patching
hypothesis. This also proves the augmented acting order reduced; no separate reduced-source
hypothesis is needed. For an isolated auxiliary level not belonging to such a coherent system,
Corollary 4.5 still requires $({\rm GR}_v)$ or another proof that the base deformation action
is faithful.

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
the relevant numerical theorem. Corollary 4.4a states the minimal exact output: it is enough
to make the zeroth Fitting ideal of every branchwise Galois cotangent nonzero. Equality (6.9)
inside the reduced Hecke order does not do that. Independently, the normalized-branch Smith module and the
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

## 8. Dependency, circularity, and normalization checks

### 8.1 Direct prerequisite ledger

The declared dependency row is
$67,69,109,138,139,140,143,170,171,172,173,174$. Their exact roles are as follows.

| Book | Result used | Boundary retained |
|---|---|---|
| 67, *Local Deformation Conditions Away from $\ell$* | the enhanced-line tangent term and the linearized special equations used in (4.7d)--(4.7f) and (4.8b) | the flag cannot be replaced residually by an ordinary local $H^1$ subspace; it becomes determined by Frobenius only after inverting $\varpi$ |
| 69, *Global Deformation Problems* | the global mapping-fiber obstruction presentation, cocycle--coboundary tangent assembly, and general relative formal-smoothness criterion | the enhanced local complex must be inserted with both its degree-zero automorphisms and degree-one tangent; the criterion does not prove vanishing of the relative obstruction map in (2.12) or any characteristic-zero tangent group |
| 109, *Solvable Base Change and Descent* | recursive cyclic descent selected by an extending irreducible arithmetic representation | used only after top-field automorphy; invariance under a noncyclic solvable group is not enough |
| 173, *Minimal Modularity Lifting* | comparison point for the neutral minimal theorem and its finite-flat range | its equality is not applied to $R^{\mathrm{sp},1}$; the scalar Kummer and line-special directions do not satisfy that identification |
| 138, *Integral Local Types and Type Lattices* | enhanced special line, primary and companion lattices, primitive type occurrence, Frobenius conventions | at $q_v\equiv1$ a line enhancement replaces old-root separation; local lattices alone do not prove global support |
| 139, *Ihara Theory and Saturated Degeneracy Maps on Shimura Curves* | residual two-map Ihara injectivity and primitive saturation | conditional on the abelian Ihara hypothesis; full-map saturation does not create a scalar selected summand |
| 140, *Integral Level Change and Jacquet--Langlands Comparison* | node, graph, component-group, normalized Smith comparisons, and constant-coefficient generic support in the clean special block | datum-specific node uniformization remains separate; the actual-row typed extension is supplied by Books 122 and 174 rather than Book 140; branch correction and the Néron component group are distinct; typed generic support is derived in Book 174 after its typed filtration |
| 143, *Taylor--Wiles Primes* | the split-detector and prime-selection mechanism, the sharp auxiliary tangent count, and represented-ring augmentation | applicability to the recomputed enhanced dual group and the resulting exactly $q$ ordered killing primes are retained explicitly in the unpadded $({\rm AUX}_Q)$ hypothesis; prime selection alone supplies no automorphic module |
| 170, *Hecke-Valued Galois Representations and Nonminimal Reciprocity* | the order-valued representation, named local factorization, trace generation, and the surjections (3.13) | every generic branch and every structural generator must be accounted for; a pseudorepresentation alone is insufficient |
| 171--172, *Minimal Deformation--Hecke Problem* and *Minimal Patching* | the unchanged clean local balance ledger, marked finite-shadow quotient patching, and equal-variable rigidity over the regular absolute and diamond sources | the minimal $R=T$ equality is not applied to the conductor-one ring; the enhanced local defect and the nonminimal module are recomputed here and in Book 174 |
| 174, *One-Prime Type Complexes and Component Support* | proved actual-row typed parahoric extension, scalar chart, twist identities, projective primary--companion complexes, conditional full named-component support, Proposition 6.3 typed generic-kernel and integral faithful-order equality, exact fixed-prime augmentation, and Proposition 9.1 auxiliary augmentation on both adjoint sides | $({\rm TIC}_v)$, type-Ihara, primitive-residue, switched node uniformization, Book 125 routing, and $({\rm BCD}_v)$ retain their stated roles; auxiliary acting-image augmentation is only a surjection there and becomes injective here only after base faithfulness; no global reducedness or nonminimal $R=T$ is asserted |

The proof of Theorem 4.2 uses Books 170 and 174 directly, with Books 138--140 supplying the
hypotheses built into Book 174. Books 67 and 69 enter both the balanced enhanced presentation
of Proposition 4.3b and the tangent equivalence of Theorem 4.4. Book 173
is not an augmented-fiber $R=T$ input, and Book 109 is used only for the final descent
statement. Book 152's torsor and module augmentation enter transitively through Book 174;
Proposition 9.1 turns them into exact primary--companion augmentation, while Corollary 4.5
derives acting-image injectivity after $({\rm GR}_v)$. Book 143 and Books 171--172 are direct
sources for Proposition 5.2's sharp auxiliary count and equal-variable argument. Their
mechanics are applied to the enhanced problem only after (4.7f)--(4.7f') recompute its local
defect and Book 174 supplies its nonzero free module. No minimal nonminimal ring map and no
minimal $R=T$ equality is imported. Book 141 still enters transitively through the detector
clause of Book 143 and $({\rm SUP}_v)$.

### 8.2 The original circular step and its repair

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

After replacing (8.1) by the correct augmentation (5.5), Book 174 supplies a nonzero module
free over the diamond source under $({\rm TYPE}_v)$ and $({\rm SUP}_v)$. The balanced enhanced
calculation (4.7f)--(4.7g), rather than the neutral minimal equality, supplies the regular
absolute source of the same dimension. With the coherent unpadded $({\rm AUX}_Q)$ system retained,
Proposition 5.2 applies equal-variable rigidity to those two sources and proves the full
patched and finite equalities.

If that coherent auxiliary system is not available, then after
$({\rm AUT}_v)$, $({\rm TYPE}_v)$, $({\rm SUP}_v)$, and $({\rm REC}_v)$ have actually been
verified, together with $({\rm RAY}_v)$ for the scalar family, the exact alternative input for
a full finite-level $R=T$ proof is

$$
({\rm GR}_v),
\quad\text{equivalently}\quad
R^{\mathrm{sp},1}\text{ is reduced}.
\tag{8.2}
$$

Local reducedness of (3.2), expected dimension, Cohen--Macaulayness, and reducedness of the
Hecke image do not prove (8.2) for the global quotient. Proposition 4.3b separately proves
vertical torsion-freeness from the balanced enhanced presentation and finiteness. Theorem 4.4
therefore reduces (8.2) to one exact external arithmetic theorem: vanishing of every
characteristic-zero tangent--Selmer group with the represented local equations. The enhanced
line is retained in forming that group. At nonzero monodromy it is determined by $N_x$, and at
a zero-monodromy point (4.8b) shows that it is determined by the distinct characteristic-zero
Frobenius eigenvalues. Corollary 4.4a is the exact branchwise cross-cotangent formulation of
this alternative. The flat dual-number example (4.10) shows why balance, finite flatness, and
support without the coherent scalar action cannot replace it.

There are earlier blockers to an unconditional arithmetic application. For the finite reduced
comparison itself, they are the actual localization $({\rm AUT}_v)$; the independent type
hypotheses $({\rm TIC}_v)$ and $({\rm TIH}_{\mathscr F})$; the five boundary-and-depth clauses
$({\rm SUP}_v)$, including the unresolved regular-sequence and formal-smoothness statements
in (2.11)--(2.12), but not the already proved common quotient diagram (2.10); branchwise
reciprocity and exact generation in $({\rm REC}_v)$; and the
effective ray quotient $({\rm RAY}_v)$ when the scalar family is used. The finite family
$({\rm AIH}_{\mathscr F})$ is additionally required whenever the constant-coefficient
level-change or normalized-residue package is invoked; it does not replace the typed
hypotheses. Under a coherent unpadded $({\rm AUX}_Q)$ system, auxiliary primary and companion
augmentation is Proposition 9.1 of Book 174 and Proposition 5.2 supplies $({\rm GR}_v)$;
Corollary 4.5 then makes the acting-image quotient exact. At an isolated auxiliary level the
acting-image quotient is not needed to apply Lemma 4.1 directly, but its injectivity still
requires base faithfulness. Books 139 and 174 give precise conditional implications after the
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
component, exact fixed-prime augmentation of modules and faithful acting images, and, under
$({\rm AUX}_Q)$, exact auxiliary augmentation of represented rings, primary and companion
complexes, modules, and pairings. Under
$({\rm REC}_v)$, Book 170 supplies the surjection
from each deformation ring to its faithful finite reduced Hecke order. These inputs prove that
the finite-level kernel is exactly the nilradical, yielding the reduced comparisons (4.3),
(4.4), and (5.9).

Here $({\rm SUP}_v)$ still includes the conditional relative Cartier-switch input
$({\rm BCD}_v)$. Book 174 supplies the compatible completed quotient diagram (2.10). The
unproved content is exactly regularity of the named lower boundary block and the formally
smooth section of the special relaxation in (2.11)--(2.12). Proposition 2.1 proves the local
dimension equality, component routing, and the full scalar-block analogue from those
transversality assertions; it does not remove them as hypotheses.

Every characteristic-zero deformation point kills that nilradical, so the reduced theorem
proves the one-prime finite-flat modularity statement needed by the arithmetic application.
Proposition 4.3b proves the vertical torsion-freeness clause of $({\rm GR}_v)$. The enhanced
definition checks the line at every point, while (4.8b) proves that no independent
flag direction survives at the monodromy-zero boundary. Theorem 4.4 identifies vanishing of
all exact fixed-condition adjoint tangent--Selmer groups with global reducedness and full
$R=T$.

Proposition 5.2 proves that vanishing under the separately supplied coherent, unpadded,
balanced $({\rm AUX}_Q)$ system. Its regular source
$P=\mathcal O[[X_1,\ldots,X_q]]$ and diamond source
$S_\infty=\mathcal O[[Z_1,\ldots,Z_q]]$ have the same dimension; the nonzero
$S_\infty$-free primary module makes the scalar map faithful, so any nonzero action kernel in
the domain $P$ would lower dimension. Hence the patched ring is $P$, the module is free over
it, and exact marked augmentation makes the finite conductor-one action faithful. This proves
full patched and finite $R=T$ without assuming patched reducedness, acting-image augmentation,
or the desired Selmer vanishing. The scalar family is then the tensor product with
$\Lambda_v$ on both deformation and Hecke sides. Corollary 4.5 consequently forces exact
auxiliary acting-order augmentation, so no separate reduced-source or faithful-order
hypothesis remains in the coherent range.

Without a coherent auxiliary system, Corollary 4.4a remains the precise alternative: a
branchwise Galois cotangent must be shown torsion, for example by an independent automorphic
cross-cotangent theorem. The flat dual-number countermodel proves that finite flatness and
topological support alone cannot give this conclusion.

Accordingly, this book's bounded theorem is **CONDITIONAL**: under the exact named
arithmetic hypotheses it proves the reduced one-prime comparisons, vertical finite flatness,
strict character specialization, and pointwise conductor-one and conductor-two modularity.
When the separate coherent unpadded $({\rm AUX}_Q)$ system is retained, it also proves full
patched and finite one-prime $R=T$, every characteristic-zero enhanced tangent--Selmer
vanishing, and exact auxiliary acting-order augmentation. Here the additional arithmetic
input is the existence at every depth of clean exactly-$q$ shadows killing the enhanced dual
group, with effective diamond torsors, ordered-root local compatibility, uniformly bounded
free modules, and the marked ring/action/augmentation diagrams; diagonal compactness supplies
coherence only after those shadows exist. The unconditional arithmetic application remains
blocked at the separately named localization, type-incidence, type-Ihara, relative
Cartier-switch transversality and support, reciprocity, and effective ray/auxiliary inputs; no
finite-set theorem is asserted here.
