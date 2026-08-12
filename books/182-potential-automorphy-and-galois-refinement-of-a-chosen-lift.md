# Potential Automorphy and Galois Refinement of a Chosen Lift

## Contents

1. [The exact question and the honest answer](#1-the-exact-question-and-the-honest-answer)
2. [The signed-special chosen lift](#2-the-signed-special-chosen-lift)
3. [The seed that minimal modularity lifting requires](#3-the-seed-that-minimal-modularity-lifting-requires)
4. [The controlled Galois seed package](#4-the-controlled-galois-seed-package)
5. [What follows conditionally from that package](#5-what-follows-conditionally-from-that-package)
6. [Where the attempted construction stops](#6-where-the-attempted-construction-stops)
7. [The missing theorem, stated without concealment](#7-the-missing-theorem-stated-without-concealment)
8. [Dependency, circularity, and downstream audit](#8-dependency-circularity-and-downstream-audit)
9. [Verdict](#9-verdict)

## 1. The exact question and the honest answer

### 1.1 One task

Fix a characteristic-zero lift

$$
\rho:G_{\mathbf Q}\longrightarrow \operatorname{GL}_2(\mathcal O)
\tag{1.1}
$$

on the signed-special, or **SP**, branch at $2$.  The task of this volume is to make this
*chosen point* automorphic after restriction to a controlled totally real Galois field, with
enough arithmetic certificates for Book 183 to construct its elementary-subfield packet array.
The task is not merely to prove that the residual representation becomes automorphic somewhere.
Nor is it to choose a different automorphic lift of the same residual representation.

There are three logically distinct objects:

1. an automorphic representation whose reduction is $\bar\rho|_{G_F}$;
2. an exact automorphic realization of the same represented minimal deformation problem as
   $\rho|_{G_F}$; and
3. automorphy of the particular characteristic-zero point $\rho|_{G_F}$.

Book 173 passes from item 2 to item 3.  It does not pass from item 1 to item 2.  Book 181 now
proves, under its exact hypothesis $(\mathrm{Seed}_{\mathrm{SP}})$, that the balanced global SP
ring is finite flat and has a normalized characteristic-zero point.  Thus the chosen lift used
here is a genuine conclusion of Book 181, not an unexplained input.  The conditionality has not
disappeared.  At the automorphic lifting boundary of the audited seed-construction routes, the
first unresolved constant-row input is the localized abelian Ihara family identified in Book
181, Section 4.3.  Its vanishing would still leave the independent type, localization, support,
reciprocity, ray, augmentation, and faithful-order clauses.  On the current Book 178 route there
are also a separate pre-specialization relative-ray compatibility hypothesis, the literal
post-specialization singleton condition of its item 7, and, for closure control, a supplied
moduli-specific Galois approximation datum.  None is a consequence of Book 181.  A controlled
Galois version must discharge the applicable clauses while also controlling the normal closure.

### 1.2 Verdict at the start

This book proves the following conditional implication:

$$
\begin{array}{c}
\text{controlled exact SP residual seed over a point field }F
\\[-2pt]
\text{plus the required transfer and attachment certificates}
\\ \Downarrow \\
\text{Book 181 constructs a normalized primitive SP lift }\rho
\\[-2pt]
\text{using that same seed}
\\ \Downarrow \\
\rho|_{G_F}\text{ is automorphic by the exact minimal }R=\mathbb T\text{ theorem}
\\ \Downarrow \\
\rho|_{G_M}\text{ gives the controlled SP top datum of Book 183}.
\end{array}
\tag{1.2}
$$

No earlier unconditional theorem constructs the first line of (1.2) for the Frey datum with
all of the required local support, normal-closure control, and transfer certificates.  In
particular, Book 181 proves the chosen-lift implication conditional on its seed; it does not
construct either that seed or its controlled refinement.  This volume therefore cannot assert
the desired potential-automorphy theorem.  Its status is **NOT READY**.

The obstruction is not local deformation theory.  Books 163--164 give the primitive
signed-special residual chart and its represented minimal deformation condition.  Books 165--166 give the supported cohomology and balanced presentation.  Those results do not make
the required automorphic module nonzero.  Patching begins only after that module exists.

### 1.3 The chosen lift supplied by Book 181

Let $\ell\geq 7$, let $E/\mathbf Q_\ell$ be finite, and write
$(\mathcal O,(\varpi),k)$ for its ring of integers, maximal ideal, and residue field.  We use
covariant representations and arithmetic Frobenius.  Assume the residual and local hypotheses
of Book 181, Theorem 1.1, together with its exact signed-special seed hypothesis
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$.  Select one normalized horizontal point produced by
that theorem and denote it by (1.1).  Replace $(E,\mathcal O,k)$ by the finite coefficient and
residue-field extension produced there.  In this notation its stable lattice satisfies

$$
\det\rho=\chi_\ell,
\qquad
\rho\text{ is unramified outside }\{2,\ell\},
\tag{1.3}
$$

$$
\bar\rho\text{ is absolutely irreducible and odd},
\qquad
\bar\rho|_{G_{\mathbf Q(\zeta_\ell)}}\text{ is absolutely irreducible},
\tag{1.4}
$$

and the lattice is coefficient-linearly finite flat of weights $\{0,1\}$ at $\ell$ in the
integral pro-Artinian sense.  At $2$ it has the primitive SP record of Section 2.  These are
exactly Book 181, equations (10.1)--(10.5), not new hypotheses invented here.

There can a priori be two seed fields to distinguish.  The hypothesis
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$ contains an even-degree totally real field $F_0$ on
which the restricted residual problem has the exact clean Book 173 realization.  Book 181
uses it to prove finiteness of the global ring and construct (1.1).  Because the resulting
$\rho|_{G_{F_0}}$ is a point of the same represented restricted problem, Book 173 also makes
that restriction automorphic.  But Book 181 neither asserts that $F_0$ has a controlled normal
closure nor supplies a solvable bridge, an admissible ascent to a Galois top, or Book 183's
finite descent and attachment ledger.

Book 182 therefore begins with the *conditional theorem output* of Book 181 and asks for a
controlled refinement, not for a second construction of the lift.  The lift may not be used
backwards to prove $(\mathrm{Seed}_{\mathrm{SP}}^{181})$ or the stronger controlled seed below.
For the dependency-closed conditional chain, the controlled seed of Section 4 may itself be
used as $(\mathrm{Seed}_{\mathrm{SP}}^{181})$, so one takes $F_0=F$ and does not assume two
independent automorphic carriers.

## 2. The signed-special chosen lift

### 2.1 Integral local record at two

Choose an $\ell$-primary tame character

$$
t_\ell:I_2\twoheadrightarrow\mathbf Z_\ell
$$

and arithmetic Frobenius $\phi_2$ so that

$$
t_\ell(\phi_2\sigma\phi_2^{-1})=2t_\ell(\sigma).
\tag{2.1}
$$

The chosen lattice has trivial wild inertia and matrices

$$
\rho(\sigma)=1+t_\ell(\sigma)N,
\qquad
N^2=0,
\qquad
\bar N:=N\bmod\varpi\ne0,
\tag{2.2}
$$

for $\sigma\in I_2$, together with

$$
FNF^{-1}=2N,
\qquad F=\rho(\phi_2).
\tag{2.3}
$$

The primitive condition $\bar N\ne0$ is part of the lattice datum.  It is stronger than
nonzero monodromy after inverting $\varpi$ and prevents an invisible factor of $\varpi$ from
appearing in the tame extension class.

Put

$$
\mathscr L=\ker N=\operatorname{im}N.
\tag{2.4}
$$

The chosen sign $\varepsilon_2\in\{1,-1\}$ is also part of the local label.  After choosing a
basis with $N=e_{12}$, the Frobenius semisimplification is

$$
F^{\mathrm{ss}}=
\begin{pmatrix}
2\varepsilon_2&0\\0&\varepsilon_2
\end{pmatrix}.
\tag{2.5}
$$

Thus Frobenius acts on $\mathscr L$ by $2\varepsilon_2$ and on the quotient by
$\varepsilon_2$.  The datum is the tuple

$$
(N,\mathscr L,\varepsilon_2,FNF^{-1}=2N),
\tag{2.6}
$$

not the conductor alone.

### 2.2 The local invariants

**Lemma 2.1 (primitive SP invariants).**  The rational Weil--Deligne representation of
$\rho|_{G_{\mathbf Q_2}}$ has nonzero rank-one monodromy.  Its unique inertia-invariant line is
$\mathscr L$, its sign is $\varepsilon_2$, and its Artin conductor exponent is one.

**Proof.**  Since $\bar N\ne0$, the endomorphism $N$ is nonzero.  A nonzero square-zero
endomorphism of a two-dimensional characteristic-zero vector space has rank one.  Hence its
kernel and image both have dimension one, and $N^2=0$ makes them equal.

The image of $t_\ell$ is dense in $\mathbf Z_\ell$.  A vector fixed by inertia is therefore
killed by $N$, so the invariant space is exactly $\mathscr L$.  Wild inertia is trivial, and
the tame conductor is

$$
2-\dim \mathscr L=1.
$$

Equation (2.3) makes $\mathscr L$ Frobenius-stable, while (2.5) records the named sign.  The
conductor computation by itself would remember neither the line nor the sign. $\square$

### 2.3 Restriction to a split field

**Lemma 2.2 (literal preservation under complete splitting).**  Let $K/\mathbf Q$ be a number
field in which $2$ splits completely.  At every $w\mid2$, restriction of the chosen lattice to
$G_{K_w}$ preserves (2.2)--(2.6), including primitivity of $N$, the line, the sign, and
conductor exponent one.

**Proof.**  Complete splitting gives $K_w=\mathbf Q_2$.  After compatible choices of
decomposition groups, restriction is the identity on the local representation and its lattice.
Lemma 2.1 applies without a change of tame parameter. $\square$

Complete splitting cannot be weakened silently.  Under ramified restriction the tame
parameter is multiplied by the ramification index.  An index divisible by $\ell$ may kill
$\bar N$ even while rational monodromy remains nonzero.  This is the lattice-thickness issue
isolated again in Book 186.

The same argument applies at $\ell$: if $\ell$ splits completely, the selected integral
finite-flat condition is literally unchanged.  If $M/\mathbf Q$ is Galois and $2$ and $\ell$
split completely in $M$, they split completely in every intermediate field.

### 2.4 The represented minimal problem

Let $K$ be totally real with complete splitting at $2$ and $\ell$.  Write
$\mathcal D_K^{\mathrm{SP}}$ for the fixed-cyclotomic-determinant deformation problem whose
local conditions are:

* the schematic closure of the named minimal-special component, with its line, sign, and
  monodromy relation, at every $w\mid2$;
* the restriction of the selected coefficient-linear finite-flat lattice condition at every
  $w\mid\ell$; and
* the unramified condition at every other finite place.

This is the SP condition of Books 163--164, transported by the split local
identifications.  It is represented.  One does not define it by the open generic-fibre
condition $N\ne0$; nonvanishing for the chosen point follows from the integral equation
$\bar N\ne0$.

Let $R_K^{\mathrm{SP}}$ be its universal ring.  The chosen restriction
$\rho|_{G_K}$ is an $\mathcal O$-point of this ring whenever the full residual image and the
chosen lattice remain identified after restriction.

## 3. The seed that minimal modularity lifting requires

### 3.1 Residual modularity is too weak

An isomorphism

$$
\bar r_{\pi,\lambda}^{\mathrm{ss}}simeq\bar\rho|_{G_K}
\tag{3.1}
$$

does not say that $\pi$ occurs at the minimal level or on the named SP component.  It may have
an auxiliary special prime where the target deformation problem is unramified, the wrong
dyadic sign, a nonsaturated type lattice, or no verified integral local--global comparison.
Any of these failures prevents the canonical map

$$
R_K^{\mathrm{SP}}\longrightarrow\mathbb T_K^{\mathrm{SP}}
\tag{3.2}
$$

from being the map to which Book 173 applies.

Patching cannot repair this.  The localized automorphic module, its type factors, and the
Hecke-valued Galois representation are inputs to the patching construction.  If the minimal
localization has not been shown nonzero and exact, patching has no module on which to act.

### 3.2 Exact SP automorphic seed

An **exact SP automorphic seed over $K$** means that the hypotheses of Book 173, Theorem 1.1,
have actually been verified for $\mathcal D_K^{\mathrm{SP}}$.  Expanded, this includes:

1. $K$ is totally real, $\ell\geq7$, the residual representation is totally odd and
   absolutely irreducible, and its restriction to $G_{K(\zeta_\ell)}$ is absolutely
   irreducible;
2. the determinant is the parallel-weight-two cyclotomic determinant;
3. every coefficient-prime condition is the clean integral finite-flat condition over the
   unramified local field;
4. every prime-to-$\ell$ condition is precisely unramified or is the schematic closure of the
   named SP component with its line, sign, and monodromy relation;
5. $\bar\rho|_{G_K}$ occurs in the corresponding non-Eisenstein parallel-weight-two
   definite-quaternionic localization;
6. the minimal and auxiliary automorphic modules have the required finite freeness,
   stabilizer and diamond-torsor control, saturated type and degeneracy maps, perfect
   primary--companion pairing, and exact augmentation;
7. the relevant Hecke orders are generically reduced, the named Hecke and diamond actions
   commute with augmentation and specialize onto the full faithful minimal Hecke image, and a
   branchwise Hecke-valued Galois representation has integral local--global compatibility on
   every named quotient.

This phrase abbreviates a previously proved theorem's hypotheses.  It is not an existence
definition.  In particular, declaring a datum to be “clean” does not verify items 5--7.

### 3.3 Image preservation

Let $D/\mathbf Q$ be a finite Galois avoidance field containing the full matrix cutout field
of $\bar\rho$, the joint residual--cyclotomic cutout, and the finite adjoint and self-twist
detection fields needed by the lifting and transfer ledgers.  It may also contain the finite
orientation, component, and coefficient fields which have to remain disjoint from a field
specialization.

**Lemma 3.1 (closure-level disjointness preserves the residual hypotheses).**  If
$M/\mathbf Q$ is finite Galois and $M\cap D=\mathbf Q$, then for every intermediate field
$K\subseteq M$,

$$
\bar\rho(G_K)=\bar\rho(G_{\mathbf Q}),
\qquad
\bar\rho(G_{K(\zeta_\ell)})
=\bar\rho(G_{\mathbf Q(\zeta_\ell)}).
\tag{3.3}
$$

**Proof.**  If $D_\rho$ is the full matrix cutout, then $K\cap D_\rho=\mathbf Q$ and restriction
identifies

$$
\operatorname{Gal}(KD_\rho/K)
\simeq \operatorname{Gal}(D_\rho/\mathbf Q).
$$

Apply the same argument to the joint residual--cyclotomic cutout contained in $D$. $\square$

Thus the absolute and cyclotomic absolute irreducibility hypotheses needed by Book 173 survive
on the whole fixed-field diagram.  Disjointness only from a projective cutout would not prove
(3.3).

### 3.4 What the Book 181 seed already gives

**Proposition 3.2 (automorphy over the uncontrolled seed field).**  Let $F_0$ be the field in
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$ and let $\rho$ be the Book 181 point selected in Section
1.3.  Then, after a common finite coefficient extension, there is a parallel-weight-two
cuspidal representation $\pi_{F_0}$ such that

$$
r_{\pi_{F_0},\lambda_0}\simeq\rho|_{G_{F_0}}
\tag{3.4}
$$

as integral representations, with the named SP line, sign, primitive monodromy, conductor
one, and finite-flat coefficient-prime lattice retained.

**Proof.**  Book 181 constructs $\rho$ as a point of its global represented SP problem.
Restriction to $G_{F_0}$ is therefore a point of the exact restricted problem occurring in
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$.  Book 181, Proposition 4.1, applies Book 173 to identify
that restricted deformation ring with its faithful minimal Hecke algebra.  The final clause of
Book 173, Theorem 1.1, makes every characteristic-zero point automorphic with a matching stable
lattice.  This gives (3.4).  Complete splitting at $2$ and $\ell$ preserves the full local
records by Lemma 2.2. $\square$

Proposition 3.2 is genuine progress, but it is not the controlled-top theorem.  Nothing in
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$ makes the normal closure of $F_0$ controlled or the
extension from $F_0$ to such a top solvable and transfer-admissible.  Passing to an arbitrary
normal closure would lose exactly the group and arithmetic certificates needed downstream.

## 4. The controlled Galois seed package

### 4.1 Field geometry

The field part of the desired package consists of a finite totally real Galois extension

$$
M/\mathbf Q,
\qquad \Gamma=\operatorname{Gal}(M/\mathbf Q),
\tag{4.1}
$$

and a subgroup $J\leq\Gamma$ such that, for $F=M^J$:

1. $J$ is solvable, so $M/F$ admits a prime-cyclic refinement;
2. $J$ is core-free, so $M$ is the normal closure of the point field $F$;
3. $[F:\mathbf Q]=[\Gamma:J]$ is even, as required by the intended FLT bridge;
4. $2$ and $\ell$, and every other sensitive rational place named in advance, split completely
   in $M$;
5. $M\cap D=\mathbf Q$; and
6. all other prescribed real and finite completion conditions hold simultaneously on the
   full fixed-field diagram.

A convenient group-theoretic template is

$$
\Gamma=S_5\times C_2,
\qquad
J=S_4\times\{1\}.
\tag{4.2}
$$

Then $[\Gamma:J]=10$, $J$ is solvable, and its core is trivial.  This calculation supplies a
useful target for a Galois approximation datum; it does not construct such a datum for the
Hilbert--Blumenthal moduli space.

### 4.2 Arithmetic seed at the point field

Over $F$ the package must contain an exact SP automorphic seed in the sense of Section 3.2.
It must be minimal away from $\{2,\ell\}$.  If Book 178 is used in an attempt to construct it,
the current interface is its seven-item two-prime-admissibility witness.  Items 1--6 are
pre-specialization clauses and item 7 is verified on one fixed specialized output.  That last
item requires the literal equality

$$
P_{\mathrm{nm}}=\{w_0\};
\tag{4.3}
$$

after every required saturated integral lowering of superfluous dihedral conductor in the
lower residual carrier, with each intermediate carrier recorded; at every other bad place the
carrier and the auxiliary-adic Tate module must lie on the same named minimal spectator
component.  Item 7 does not offer a finite-clean-chain alternative for extra nonminimal
Tate-module places.  Moreover, Book 178's residual potential-modularity conclusion is still
weaker than an exact SP seed: the resulting target residual packet must be shown to occur in
the precise minimal Book 173 localization with all the integral clauses of Section 3.2.

The phrase “the residual representation is potentially modular over $F$” is not a substitute
for this item.  Neither is the existence of an automorphic residual representation at a larger
level.

### 4.3 Transfer certificates are arithmetic data

Solvability of $J$ gives a group-theoretic prime-cyclic series; it does not put the packets in
the transfer range of Books 108--109.  The package must therefore include an
**ascent-admissible** prime-cyclic chain from $F$ to $M$ in the sense of Book 109.  At each
cuspidal source step the packet must be selected and trace-comparable; its finite local
components and restricted parameters must lie in the selected range; at every nonsplit place
the full fixed-determinant extension fiber must be selected; its archimedean components must be
in the proved cohomological range; and matching test tensors must have the required strongly
cuspidal factor.  The package must also supply the distinguished-coefficient compatibility of
attachment with those base-change steps.  Antecedent-completeness and quotient-character fiber
saturation belong to the downward descent ledger below, not to this upward definition.

The top packet eventually delivered to Book 183 needs a second, finite ledger.  For every
elementary subgroup $H\leq\Gamma$, at least one prime-cyclic descent chain from $M$ to $M^H$
must satisfy Book 109's descent-admissibility and fiber-saturation hypotheses.  Every corrected
packet along those chains must lie in the all-coefficient weight-two attachment range of Books 127--128 and 168.  At the dyadic places, their special-scalar and raw-to-semisimple local-preservation
hypotheses must be verified uniformly.  Those conditions are exactly why Book 183 calls its
top packet “selected.”

This volume does not construct the elementary packets.  That is the subject of Book 183.  It
only identifies the certificates which must accompany $\pi_M$ so that Book 183 may construct
them without replacing arithmetic admissibility by group solvability.

### 4.4 Two interfaces which must not be conflated

A **controlled exact SP residual seed** consists of the field diagram
$(M,\Gamma,J,F)$ of Section 4.1 and an exact SP automorphic seed for
$\bar\rho|_{G_F}$.  Its automorphic clauses are the controlled analogue of
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$; the new content is that the seed field is embedded in
the prescribed normal-closure diagram.  Since $[F:\mathbf Q]$ is even and $2$ and $\ell$
split completely, forgetting the top diagram gives precisely a permissible
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$.  Thus this single controlled seed both enables Book 181
to construct the chosen lift and enables Book 173 to make its restriction automorphic.  This
is the first missing object.

A **controlled SP bridge package for the chosen lift** consists of that residual seed together
with the ascent ledger and all of the downstream-readiness certificates in Section 4.3.  The
ascent certificate must apply to the exact eigenpacket obtained by evaluating the minimal
Hecke algebra at the chosen point.  It may, for example, be verified uniformly on that Hecke
family; it may not assume in advance that an unrelated packet will represent $\rho|_{G_F}$.

These are exact hypotheses, not theorems of the present dependency graph.  Separating them is
important: constructing minimal residual support does not automatically prove automorphic
transfer admissibility, while a transfer ledger has no packet to transfer until the residual
support and minimal lifting argument have produced one.

## 5. What follows conditionally from that package

### 5.1 Automorphy of the chosen point over the point field

**Theorem 5.1 (exact seed to the chosen lift).**  Assume the residual and local hypotheses of
Book 181 and a controlled exact SP residual seed.  Use that seed as
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$, and select any normalized Book 181 output $\rho$ as in
Section 1.3.  Then there is a parallel-weight-two cuspidal
automorphic representation $\pi_F$ and a coefficient place $\lambda_F\mid\ell$ such that,
after one finite coefficient extension,

$$
r_{\pi_F,\lambda_F}\simeq\rho|_{G_F}
\tag{5.1}
$$

as integral representations.  At every $w\mid2$, the local representation retains nonzero
rank-one monodromy, the intrinsic line $\mathscr L$, the sign $\varepsilon_2$, and conductor
exponent one.  It retains the chosen finite-flat lattice at $w\mid\ell$ and is unramified at
every other finite place.

**Proof.**  The finite coefficient and residue-field extension used to normalize the Book 181
point merely scalar-extends the controlled seed: Book 164's represented local conditions and
Book 173's clean comparison are stable under that coefficient change.  It does not require a
second carrier.  Lemma 3.1 supplies the full and cyclotomic image hypotheses over $F$.  Complete
splitting gives the clean coefficient-prime condition and, by Lemma 2.2, the exact named SP
condition.  The exact seed supplies every automorphic-module, saturation, pairing,
augmentation, generic-reducedness, and integral local--global hypothesis of Book 173, Theorem
1.1.
That theorem gives

$$
R_F^{\mathrm{SP}}\xrightarrow{\sim}\mathbb T_F^{\mathrm{SP}}
\tag{5.2}
$$

and states that every characteristic-zero point of the represented minimal problem is
automorphic with a matching stable lattice.

The restriction $\rho|_{G_F}$ is such a point, so (5.1) follows directly.  Because the
integral local conditions on both sides factor through the same represented quotients, the
line, sign, primitive monodromy, finite-flat lattice, and unramified conditions are retained.
$\square$

The theorem uses $R=\mathbb T$ only after the exact residual localization has been constructed.
It therefore does not argue circularly from the desired automorphy of $\rho$.

### 5.2 Passage to the controlled top

**Theorem 5.2 (conditional controlled-top theorem).**  Assume in addition that the controlled
residual seed has been extended to a controlled SP bridge package as in Section 4.4.  Then there is a
parallel-weight-two cuspidal automorphic representation $\pi_M$ such that

$$
r_{\pi_M,\lambda_M}\simeq\rho|_{G_M}.
\tag{5.3}
$$

Together with $M$, $\rho$, and the certificates included in the bridge package, this is the
controlled SP top datum assumed by Book 183.

**Proof.**  Starting with $\pi_F$ from Theorem 5.1, apply Book 109's prime-cyclic ascent theorem
along the supplied ascent-admissible chain.  It produces an automorphic isobaric endpoint and
identifies every local parameter by restriction.  The distinguished-coefficient attachment and
base-change compatibility included in the bridge package identify its semisimple Galois
realization with $\rho|_{G_M}$, giving (5.3).

The endpoint is cuspidal.  Indeed, Lemma 3.1 makes
$\bar\rho|_{G_M}$ absolutely irreducible, hence $\rho|_{G_M}$ is absolutely irreducible,
whereas the attached representation of a rank-two noncuspidal isobaric endpoint would be
reducible.  Complete splitting and Lemma 2.2 preserve the full SP pair at every dyadic place.
The remaining certificates in Section 4.3 are already part of the package, so
$(M,\rho,\pi_M)$ satisfies precisely the input ledger of Book 183.
$\square$

It would be invalid to replace the supplied ascent-admissibility by the sentence “$J$ is
solvable.”  Book 109 explicitly separates the prime-cyclic group tower from the automorphic
selector and fiber hypotheses.

### 5.3 Exact handoff and stopping point

The output of Theorem 5.2 is:

$$
\left(
M/\mathbf Q,\ \Gamma,\ \rho,\ \pi_M,\
\mathscr D_2,\ \mathscr L,\ \varepsilon_2,\
\text{the finite descent and attachment ledger}
\right),
\tag{5.4}
$$

where

$$
N_2\ne0,
\qquad \operatorname{rank}N_2=1,
\qquad \ker N_2=\operatorname{im}N_2=\mathscr L,
\qquad F_2N_2F_2^{-1}=2N_2,
\tag{5.5}
$$

and the Artin conductor exponent is one.  The primes $2$ and $\ell$ split completely in $M$,
and $\rho|_{G_M}$ remains absolutely irreducible.

Book 182 stops here.  It does not select packets over every elementary fixed field, prove
overlap identities, form a Brauer class, prove effectivity, or construct a compatible system.
Those are respectively the jobs of Books 183--185.

## 6. Where the attempted construction stops

### 6.1 The carrier obstruction and its first constant row

The seed hypothesis consumed by Book 181 and the controlled seed required here both need an
exact nonzero localization on the inherited SP component.  Book 181, Section 4.3, audits the
level-change part of the attempted construction in proof order.  Its first unresolved
constant-row assertion is the finite localized abelian Ihara family retained by the integral
comparison:

$$
({\rm AIH}_{\mathscr F}):\qquad
\left(H^1_{\mathrm{nc}}(\Gamma_D^v,k)^{\Delta_D}\right)_{\mathfrak m_D}=0
\qquad(D\in\mathscr F_v(Q)).
\tag{6.1}
$$

The tree calculation and strong approximation do not prove (6.1).  The later support and
minimal-comparison books retain it as a hypothesis.  Finite-level diamond freeness,
Hecke-valued Galois attachment, and the conditional $R=\mathbb T$ theorem all begin after the
localized module and its saturated maps exist; none can be invoked to construct them.  Even
after (6.1), the independent type-incidence, typed-Ihara, automorphic-localization, support,
reciprocity, ray, augmentation, and faithful-order clauses still have to be verified on the
actual localization.

Consequently the first missing object required by Book 181 is the **clean Frey-SP carrier**
specified in its missing-theorem statement: over an even-degree totally real split field, a
nonzero minimal SP localization satisfying every clean integral hypothesis of Book 173.  Within
the audited constant-row construction, (6.1) is the smallest presently isolated missing
assertion, not the whole carrier theorem.  Book 182 needs a stronger controlled form in which
that field is the quotient field of a prescribed Galois top.  Normal-closure control does not
repair the missing localized support.

### 6.2 Book 178's literal one-prime boundary

Even if (6.1) is supplied in the required generality, the current two-prime route has a separate
post-specialization obstruction.  Book 178 proves its
Hilbert--Blumenthal implication only for a **two-prime admissible** datum with exactly seven
witness items.  Items 1--6 are pre-specialization clauses.  Item 7 is verified on one fixed
output $(F,A)$ after its actual bad set and a lower residual automorphic carrier have been
listed.  Following every proved saturated lowering needed only for superfluous dihedral
conductor in that lower carrier, it requires

$$
P_{\mathrm{nm}}=\{w_0\}
$$

literally, and it requires the carrier and the auxiliary-adic Tate module to lie on the same
named minimal spectator component at every other bad place.  There is no alternative in the
current theorem saying that the Tate module may instead admit a finite clean chain, and there is
no item 8.  Here $w_0$ is Book 178's distinguished one-prime lifting place.

After specialization, an auxiliary Hilbert--Blumenthal abelian variety $A/F$ may acquire a
finite set $B(A)$ of extra semistable primes which was not known before the point was chosen.
At $x\in B(A)$ the auxiliary residual representation can be unramified while the
characteristic-zero auxiliary-adic representation is special.  Residual unramifiedness yields
the familiar level-raising congruence

$$
\bigl(\operatorname{tr}\bar r(\operatorname{Frob}_x)\bigr)^2
=(q_x+1)^2q_x^{-1}\det\bar r(\operatorname{Frob}_x),
\tag{6.2}
$$

but (6.2) does not construct a class in the hyperspecial automorphic module.

To remove $x$ while retaining an exact lifting datum one needs, on the actual localized
automorphic modules:

1. the lower-face automorphic class at the unramified level;
2. an ordered integral Frobenius flag and the correct special sign;
3. saturated old/new or type-changing maps;
4. compatible perfect pairings and Hecke actions;
5. an integral vanishing-cycle nullhomotopy or the equivalent exact augmentation; and
6. preservation of the non-Eisenstein support and local--global Galois comparison.

When the residual Frobenius is scalar, or $q_x\equiv\pm1\pmod\ell$, a banal idempotent does
not even recover the ordered root and sign automatically.  Book 175 can change one previously
named place when its exact clean hypotheses are already verified.  It does not construct the
six items above simultaneously at the unknown set $B(A)$.

The current route therefore needs a specialization with no additional nonminimal Tate-module
place: the literal singleton above must hold.  A future acyclic finite-set theorem constructing
the six rows simultaneously could support a different admissibility route, but Book 178 does
not claim that theorem.  Conversely, once item 7 succeeds, Book 178 itself proves eligibility
of the final compact curve carrier from even absolute degree and the retained selected
Steinberg place $w_0$, and then invokes Books 104 and 127.  Curve-carrier eligibility is not an
eighth witness item or an additional blocker.

Even a complete seven-item Book 178 witness gives its stated residual potential-modularity
output.  To obtain the seed of Section 3.2 one must still prove that the target residual packet
occurs in the exact minimal SP localization with every integral hypothesis of Book 173.

### 6.3 Independent ray and normal-closure inputs

Book 178 also retains a pre-specialization boundary which is logically earlier than its
specialization.  Its inverse-branch lemma cancels the ray-unit obstruction, but its dihedral
seed theorem still assumes a fully compatible corrected relative ray datum, including every
diagonal ideal intersection and capitulation relation.  That compatibility is item 2 of the
seven-item witness; it is not proved merely by the inverse-branch unit calculation.

Book 154 proves Galois-refined approximation after a **Galois approximation datum** for the
given variety has been supplied.  Its $S_5/S_4$ calculation proves that such a datum would have
a solvable point stabilizer.  Its universal symmetric family supplies a datum for an affine
coefficient space.  Neither result constructs the required full-monodromy presentation and
local top torsors for the paired-frame Hilbert--Blumenthal moduli space used in Book 178.

Consequently the current Book 178 route to the controlled seed has the following distinct
unmet tasks:

$$
\begin{array}{ll}
\text{dihedral input:}&
\text{construct the fully compatible corrected relative ray datum;}\\
\text{lifting support:}&
\text{prove (6.1) and all remaining exact one-prime localization clauses;}\\
\text{field geometry:}&
\text{construct the moduli-specific Galois approximation datum;}\\
\text{specialized shape:}&
\text{produce a seven-item witness with }P_{\mathrm{nm}}=\{w_0\};\\
\text{target support:}&
\text{prove occurrence in the exact minimal Book 173 SP localization.}
\end{array}
\tag{6.3}
$$

The order inside the route is exact.  The ray datum, Galois presentation, and any general
lifting-support theorems must exist before the controlled specialization.  The remaining
one-prime clauses and the singleton condition are then verified on its actual localization and
bad set as item 7.  Only after that does Book 178 produce the target residual packet, whose
exact Book 173 localization is a still stronger subsequent obligation.  Within the
lifting-support row, (6.1) is the first unresolved constant-row input, not a substitute for the
later independent clauses.  Ordinary Moret--Bailly approximation cannot be promoted to
normal-closure control, and a controlled normal closure forces none of the arithmetic support
rows.

### 6.4 Why no formal workaround is available

Several tempting shortcuts fail for precise reasons.

* **Pass to a normal closure.**  The normal closure of an uncontrolled point field need not
  have a solvable stabilizer over that field and need not preserve the avoidance ledger.
* **Use group solvability alone.**  It gives a prime-cyclic series, not the selected arithmetic
  fibers and comparisons required by Book 109.
* **Invoke minimal patching.**  Book 173 needs the exact minimal automorphic module before
  patching; it cannot prove that module nonzero.
* **Accept a nonminimal residual packet.**  It does not give the exact
  $\mathcal D_F^{\mathrm{SP}}$ localization, so Theorem 5.1 does not apply to the chosen minimal
  lift.
* **Use a later simultaneous-carrier theorem.**  Any later theorem which takes Book 182 or
  the compatible system of Book 185 as input would make the argument circular.

Thus the gap cannot be absorbed into the words “admissible,” “potentially modular,” or
“solvable.”

## 7. The missing theorem, stated without concealment

### 7.1 Required controlled-SP seed theorem

The following theorem, placed strictly before Book 182, would remove the first missing object.
Together with the bridge-readiness result of Section 7.3, it would make the conditional
argument dependency-closed.

**Required Theorem 7.1 (controlled exact SP residual seed).**  Let $\ell\geq7$ and let
$\bar\rho:G_{\mathbf Q}\to\operatorname{GL}_2(k)$ be the primitive signed-special Frey
residual representation of Book 163, satisfying the determinant, finite-flat, absolute
irreducibility, cyclotomic absolute irreducibility, and other global image hypotheses required
by Book 173.  Given a finite Galois avoidance field $D$, finitely many prescribed split places, and an
even-index solvable-bridge group datum $(\Gamma,J)$, construct a controlled exact SP residual
seed as in Section 4.4.

Any proof must produce the exact output of Section 4.4 rather than merely a residually
automorphic packet.  A proof through the current Book 178 route must in particular prove rather
than assume:

1. every applicable localized abelian Ihara family (6.1), and every independent type,
   localization, support, reciprocity, augmentation, faithful-order, and saturated integral
   comparison used on the actual automorphic localizations in the construction;
2. the fully compatible corrected relative ray datum required by Book 178's dihedral seed;
3. a Galois approximation datum for the actual paired-frame moduli space, with full top group
   $\Gamma$, point stabilizer $J$, all required local top fibers, and closure-level
   disjointness from $D$;
4. a totally real specialized output satisfying all seven witness items and, in particular,
   the literal equality $P_{\mathrm{nm}}=\{w_0\}$ after every recorded saturated lowering of
   superfluous dihedral conductor, with minimal spectator matching everywhere else; and
5. exact occurrence of $\bar\rho|_{G_F}$ in the minimal SP localization, including every
   saturation, pairing, augmentation, generic-reducedness, and integral local--global hypothesis
   of Book 173.

The proof must be acyclic: it may not use Book 182, the elementary packet array of Book 183,
the effectivity theorem of Book 184, the compatible system of Book 185, or any later theorem
whose hypotheses include those outputs.

No theorem with this conclusion occurs among the audited prerequisites.  Required Theorem 7.1
is therefore a specification of the first missing result, not a result proved in this volume.

### 7.2 Smallest presently isolated subtheorem

The first missing assertion in the audited constant-row proof order is (6.1).  The smallest
honest direct repair is a localized Ihara theorem proving that finite family at the Frey
non-Eisenstein maximal ideals and deriving the saturated integral level maps needed for the
exact signed-SP carrier.  It must apply at the inherited nontrivial-unipotent dyadic component;
a scalar-boundary comparison for another local deformation ring does not suffice.  The
independent type, localization, support, reciprocity, ray, augmentation, and faithful-order
clauses remain after that repair.

For Book 178's post-specialization boundary, the next obligation on the current route is not a
finite-clean-chain theorem.  It is the existential singleton assertion:

> Produce at least one specialized two-prime Hilbert--Blumenthal output, list its actual bad
> set and lower residual carrier, perform every required proved saturated lowering of
> superfluous dihedral conductor, and verify
> $P_{\mathrm{nm}}=\{w_0\}$ with named minimal spectator matching everywhere else.

That is the literal content of Book 178, Section 2.5, item 7.  A genuine prior finite-set theorem
could instead justify a newly enlarged route, but it is not the current item 7.  Once item 7
holds, Book 178 proves the final compact carrier itself.  Neither alternative would by itself
supply the independent Galois presentation, the exact target SP localization, or Book 183's
transfer and attachment certificates.

### 7.3 The later bridge-readiness obligation

After Required Theorem 7.1, Book 181, and Theorem 5.1 have produced the chosen point and its
selected eigenpacket, a separate prior argument must verify that this packet satisfies the
ascent ledger and that the resulting top packet carries
Book 183's finite descent and attachment ledger.  This may be packaged with Required Theorem
7.1 if it is genuinely proved there, but it is not part of the residual seed and does not
follow from $J$ being solvable.  It is a later obligation; it must not obscure the earlier
failure to construct the minimal residual seed itself.

## 8. Dependency, circularity, and downstream audit

### 8.1 What each prior book really supplies

| Source | Legitimate use here | What it does not supply |
|---|---|---|
| Book 109 | prime-cyclic ascent on an exhibited extension-complete selected chain, and descent on exhibited antecedent-complete selected chains with the required fiber saturation | either direction from solvability alone |
| Books 127--128 and 168 | weight-two coefficient attachment and the SP local comparison in their explicitly stated range | an automatic all-coefficient SP comparison for an arbitrary packet |
| Book 163 | the primitive residual Frey SP tuple, intrinsic line, sign, and conductor-one record used in the FLT specialization | a characteristic-zero chosen lift or automorphic seed |
| Book 173 | exact minimal $R=\mathbb T$ and automorphy of every point of a clean minimal deformation problem | existence of the exact residual automorphic localization |
| Book 175 | a local change at a previously named place under its exact clean augmentation hypotheses | simultaneous lowering at the unknown extra bad primes of a specialization |
| Book 177 | a conditional two-prime potential-modularity route and point-field control in its admitted range | an unconditional clean seed or controlled normal closure |
| Book 154 | Galois-refined approximation from a supplied Galois approximation datum | that datum for the paired-frame moduli problem |
| Book 178 | conditional residual potential modularity for a fixed seven-item two-prime-admissible witness; after lifting, proof of final compact-carrier eligibility | construction of the corrected relative ray datum, a specialization satisfying item 7's literal singleton condition, or the exact minimal Book 173 SP seed |
| Books 164--166 | the SP local deformation problem, supported cohomology, and balanced presentation | a horizontal point or a nonzero exact automorphic module |
| Book 181 | under $(\mathrm{Seed}_{\mathrm{SP}}^{181})$, finite-flatness of the balanced global SP ring and the normalized primitive SP point used here | construction of its seed, normal-closure control, or the controlled seed required in Section 4 |

Book 181 now genuinely supplies the chosen point conditional on its exact seed; this volume no
longer treats that point as a free-standing assumption.  Proposition 3.2 also extracts its
automorphy over Book 181's seed field.  The controlled seed remains stronger and unproved.

### 8.2 Direct dependency recommendation

For the conditional theorem actually proved here, the honest direct dependency row is

$$
\boxed{
182\mid 109,127,128,168,163,173,154,178,164,181.}
\tag{8.1}
$$

Books 175 and 177 are background to the seed-construction audit inherited through Books 178 and 181 and need not be direct edges here.  Books 165--166 are direct inputs to Book 181, but
transitive for this volume.  Book 164 is retained because this volume directly identifies the
represented local SP problem; it could be made transitive by treating all local identifications
as part of the Book 181 export.

Equation (8.1) does not make the result unconditional.  To mark Book 182 **READY**, a new
strictly prior result proving Required Theorem 7.1, and a prior proof of the bridge-readiness
ledger of Section 7.3, must be added as direct dependencies.  They may be two results in one
new volume, but no existing book number may be put in either slot merely because it states the
conclusion conditionally.

### 8.3 Proof-order audit

The acyclic order is

$$
\begin{array}{c}
\text{primitive residual SP datum}
\\ \Downarrow \\
\text{Required Theorem 7.1: controlled exact residual seed}
\\ \Downarrow \\
\text{the controlled seed supplies }(\mathrm{Seed}_{\mathrm{SP}}^{181})
\\ \Downarrow \\
\text{Book 181: a normalized primitive chosen SP lift }\rho
\\ \Downarrow \\
\text{Book 173: }R_F^{\mathrm{SP}}=\mathbb T_F^{\mathrm{SP}}
\\ \Downarrow \\
\rho|_{G_F}\text{ is automorphic}
\\ \Downarrow \\
\text{the bridge-readiness ledger is verified for the selected packet}
\\ \Downarrow \\
\text{Book 109 along the supplied ascent-admissible chain}
\\ \Downarrow \\
(M,\rho,\pi_M,\text{certificates})\text{ is the controlled SP top datum}
\\ \Downarrow \\
\text{Books 183--185}.
\end{array}
\tag{8.2}
$$

Neither patching nor transfer may be moved above the missing-seed line.

### 8.4 The actual downstream contract

The committed downstream books already use the SP branch:

* Book 183 assumes the controlled SP top datum with $N_2\ne0$ of rank one, the intrinsic line,
  sign, and conductor exponent one.  It constructs the elementary packets and their overlap
  identities.  Its own dependency audit states that Book 182 has not unconditionally
  constructed the seed.
* Book 184 proves effectivity from Book 183's packet array and retains the same SP record.  Any
  phrase there saying that Book 183 exports an “unconditional package” is read relative to its
  controlled-top hypothesis, not as a proof of that hypothesis.
* Book 185 assumes the controlled SP top datum and the effective array.  It again retains
  nonzero rank-one monodromy, line, sign, and conductor exponent one, and explicitly records
  the upstream conditionality.

No downstream replacement by a zero-monodromy local type is required or permitted.  The only
Book 182 handoff consistent with the committed texts is (5.4)--(5.5).

Book 186 is not a source of the missing seed.  It starts from a compatible family and changes
coefficient prime while preserving the rational SP pair.  It also warns that rational nonzero
monodromy does not force primitive residual monodromy for an arbitrary lattice.  The primitive
condition in (2.2) is therefore essential, but Book 186 lies after the compatible-family input
and cannot repair the gap found here.

## 9. Verdict

Book 181 now genuinely constructs the chosen primitive SP lift under its explicit
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$ hypothesis, and Proposition 3.2 makes that lift automorphic
over Book 181's uncontrolled seed field.  Given the stronger controlled residual seed, Book
173 makes the same *chosen* lift automorphic over the solvable-bridge point field, and a
supplied Book 109 transfer ledger carries it to the controlled top.  This conditional argument
exports precisely the datum consumed by Book 183 and does not duplicate Book 183's
elementary-packet construction.

The first missing object at the interface is the controlled exact SP residual automorphic seed
of Section 4.  At the lifting boundary of the available routes, the first unresolved
constant-row blocker is the localized abelian Ihara family (6.1); the remaining exact carrier
clauses do not follow from it.  On the current Book 178 route, the fully compatible corrected
relative ray datum, a controlled specialization satisfying the literal singleton
$P_{\mathrm{nm}}=\{w_0\}$, the exact target minimal localization, and the independent
moduli-specific Galois presentation are also unproved.  Book 178 does prove final
compact-carrier eligibility once its seven-item witness is supplied, so that is not an
additional blocker.  Independently, the bridge-readiness theorem of Section 7.3 must still
verify the ascent chain and Book 183's finite descent-and-attachment ledger for the exact packet
selected by the chosen point.

Accordingly,

$$
\boxed{\text{NOT READY}.}
$$
