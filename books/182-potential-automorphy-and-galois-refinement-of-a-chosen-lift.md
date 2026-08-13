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
are also the literal post-specialization singleton condition of its item 7 and the stronger
target-prime minimal localization required here.  Book 178 retains relative-ray compatibility
over a general totally real base, but Section 6.3 proves it from the inverse-branch correction
in the rational-base case used here.  Its local geometry usually constructs paired-frame seeds
only after a finite completion extension; complete splitting in the controlled top instead
requires actual paired-frame seeds over $\mathbf Q_2$ and $\mathbf Q_\ell$.  The mixed exact
local packets must also occur in one simultaneous moving presentation, as retained in Book
178, item 6.  Once that presentation exists, Section 4 reduces closure control to one exact
field-geometric certificate: the constant field of its Galois closure must be disjoint from the
avoidance field.  After that, adjoin an independent ordered-quintic torsor and use the normal
top as the field of definition.
The resulting arithmetic problem has a finite active set over that top and still requires
actual lower-face automorphic support.

### 1.2 Verdict at the start

This book proves the following conditional implication:

$$
\begin{array}{c}
\text{constant-compatible normal-top exact SP residual seed over }M
\\ \Downarrow \\
\text{Book 181 constructs a normalized primitive SP lift }\rho
\\[-2pt]
\text{using that same seed}
\\ \Downarrow \\
\rho|_{G_M}\text{ is automorphic by the exact minimal }R=\mathbb T\text{ theorem}
\\ \Downarrow \\
\text{the distinguished attachment-and-descent and all-coefficient SP certificates remain}.
\end{array}
\tag{1.2}
$$

No earlier unconditional theorem constructs the first line of (1.2) for the Frey datum with
all of the required post-specialization lower faces and clean minimal support.  Proposition 4.1
constructs its normal-closure field diagram from a compatible moving cover and the stated
constant-field certificate, and Section 7.3 reduces the local and group-theoretic part of the
elementary descent ledger.  Actual corrected descents still require distinguished-coefficient
Galois attachment for the candidate packets before Book 109 can select the quotient-character
correction; all-coefficient attachment remains a stronger separate requirement.  Book 181
still proves the chosen-lift implication only conditional on the arithmetic seed.  This volume
therefore cannot assert the desired potential-automorphy theorem.  Its status is **NOT READY**.

The obstruction is not local deformation theory.  Books 164--165 give the primitive
signed-special residual chart and its represented minimal deformation condition.  Books 166--167 give the supported cohomology and balanced presentation.  Those results do not make
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

This is the SP condition of Books 164--165, transported by the split local
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
\bar r_{\pi,\lambda}^{\mathrm{ss}}\simeq\bar\rho|_{G_K}
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

There is no need to force a quintic quotient presentation on the Hilbert--Blumenthal moduli
space.  The ordinary moving family already has a Galois closure, and one may use that closure
itself as the field of definition.  The following reduction removes the previously apparent
moduli-specific $S_5/S_4$ obstruction.

**Proposition 4.1 (normal-top refinement with controlled constants).**  Let $X/K$ be a smooth
geometrically connected positive-dimensional variety over a totally real field.  Suppose the
local packets under consideration admit one simultaneous moving presentation

$$
T_0\longrightarrow H_0,
\qquad T_0\longrightarrow X,
\tag{4.1a}
$$

as in Book 154, Lemma 5.2, with $H_0$ an open of affine space and $T_0/H_0$ finite étale and
geometrically integral.  Let $E_0/K(H_0)$ be its Galois closure, let $C$ be the algebraic
closure of $K$ in $E_0$, and let $D/K$ be a finite Galois avoidance field.  Assume

$$
C\cap D=K.
\tag{4.1b}
$$

Suppose also that the displayed fiber is split with its labeled evaluated packet at every real
place and at every finite place required to split.  At each remaining controlled finite place,
assume that the fiber of the normalized Galois closure and its pulled-back evaluated packet have
the required local behavior.  Then there is a specialization for $X$ with

$$
J=1,
\qquad
\Gamma=G_0\times S_5,
\tag{4.1c}
$$

where $G_0=\operatorname{Gal}(E_0/K(H_0))$ is the arithmetic Galois group.  Its
specialization field $M$ is itself the quotient field $F=M^J$, is totally real and Galois over
$K$, has even degree, is disjoint from $D$, and realizes all the prescribed
evaluated local packets.  Every prescribed split place splits completely in $M$.

**Proof.**  Normalize $H_0$ in the Galois closure of $K(T_0)/K(H_0)$ and shrink off the branch
locus.  The resulting integral cover $\widetilde T_0\to H_0$ is a finite étale
$G_0$-torsor with constant field $C$; it need not be geometrically connected.  The original
evaluation map pulls back to $\widetilde T_0\to X$.  Independently take the geometrically
connected ordered-root $S_5$-torsor over the discriminant complement in the coefficient space
of monic quintics from Book 155, Proposition 13.1.  Over the product of the two parameter
spaces, the ordered-root function field is regular over $K$ and its parameter coordinates are
algebraically independent from those of $H_0$.  It is therefore linearly disjoint from $E_0$
over the product rational function field.  Their product is consequently an integral torsor
with group $G_0\times S_5$, constant field $C$, and an evaluation map to $X$.  Take $J=1$.

At a prescribed split place the local homomorphism into $G_0$ acts trivially on the faithful
sheet set of the normal closure and hence is trivial.  Choose a split quintic there, using the
local coefficient neighborhoods of Book 155, Proposition 13.2.  The product top torsor is
therefore split at every prescribed real or finite split place.  Its evaluation is the pullback
of the labeled split packet on $T_0$; labels may repeat on the sheets of the normal closure and
on the independent $S_5$ factor, but no new local field extension is introduced.  At a
nonsplit controlled place, use the assumed local normal-closure fiber and again choose the
quintic factor split.  Equivariant local constancy for all these top torsors and evaluated
packets is Book 155, Proposition 5.2.

Condition (4.1b) makes the product torsor's function field linearly disjoint from $D$ over the
rational function field.  Indeed, because $D/K$ is Galois, every intermediate field of its
constant extension is $L(H_0,H_5)$ for an intermediate field $L/K$ of $D/K$; containment in
the product top field forces $L\subseteq C$.  Hence the intersection is the base rational
function field exactly when $C\cap D=K$.  Thus both the product top cover and its base change
by $D$ are integral.
Apply Book 153, Theorem 5.1, simultaneously to those two covers inside the prescribed local
boxes.  Connectedness of the top fiber gives a Galois field $M/K$ with group
$G_0\times S_5$; connectedness after base change says $M\otimes_KD$ is a field.  The split
real fibers make $M$ totally real, and the split finite fibers give the stated completion data.
Since $J=1$, the quotient field equals the Galois top and its upper bridge is trivial.  The
factor $S_5$ makes its degree even. $\square$

The evaluated object may descend to the root field of $T_0/H_0$.  This causes no
field-theoretic problem: Book 155's definition does not require the evaluated point to have
minimal residue field, and all deformation and automorphic conditions may be restricted
further to $G_M$.  What changes is the lifting problem.  Pullback through the normal-closure
sheets and the independent $S_5$ factor repeats a distinguished root-place condition at a
finite set of places over $M$.  Thus the arithmetic argument over the normal top must use an
honest ordered chain or the finite-set interface of Book 176.  This is an arithmetic
post-specialization obligation, not a missing normal-closure presentation.

For a Book 178 packet already given over a nonsplit completion factor, the nonsplit clause of
Proposition 4.1 adds no new local existence theorem.  Passing to that factor's local Galois
closure only base-changes the chosen moduli point.  Good, ordinary, local--local, semistable,
torsion-frame, and component-open conditions used there persist under that finite base change.
This observation does **not** create a split local fiber.  Book 157, Theorem 13.1, generally
produces the simultaneous coefficient-prime frames only after a finite local extension, and
Section 13.3 explicitly forbids descending such a point to the original completion.  Since the
controlled top must split completely at $2$ and $\ell$, Proposition 4.1 therefore needs actual
paired-frame points over $\mathbf Q_2$ and $\mathbf Q_\ell$, not points over recorded proper
extensions.  Book 178 constructs its distinguished special seed over its base completion, but
no audited prerequisite proves these two simultaneous base-field frame assertions for the
Frey and auxiliary systems.

Geometric integrality of $T_0$ does not force $C=K$: a regular non-Galois function-field
extension can acquire constants in its Galois closure.  Full regularity of the closure is a
sufficient special case of (4.1b), but it is stronger than necessary.  Book 154 constructs
$T_0/H_0$ in its flexible split range.  For the exact nonsplit completion algebras used by Book
178, it instead retains the simultaneous presentation as a hypothesis.  Once such a
presentation is supplied, neither source computes $C$ or its intersection with the avoidance
field.  Thus the two field-geometric obligations are to construct the actual mixed moving
presentation and to prove $C\cap D=K$ for its closure.  Full symmetric geometric monodromy would
imply $C=K$ and suffice for the second obligation, but it has not been proved for the
paired-frame moving family.  Once both inputs are supplied, Proposition 4.1 proves every other
normal-closure and upward-bridge assertion.

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

For a general quotient presentation, solvability of $J$ gives a group-theoretic prime-cyclic
series; it does not put the packets in Book 109's transfer range.  The package must therefore
include an **ascent-admissible** prime-cyclic chain from $F$ to $M$ in the sense of Book 109.  At each
cuspidal source step the packet must be selected and trace-comparable; its finite local
components and restricted parameters must lie in the selected range; at every nonsplit place
the full fixed-determinant extension fiber must be selected; its archimedean components must be
in the proved cohomological range; and matching test tensors must have the required strongly
cuspidal factor.  The package must also supply the distinguished-coefficient compatibility of
attachment with those base-change steps.  Antecedent-completeness and quotient-character fiber
saturation belong to the downward descent ledger below, not to this upward definition.

For the normal-top construction of Proposition 4.1, $F=M$ and this entire upward ledger is
empty.  Once the compatible moving cover, its constant-field certificate, and the exact seed
exist over $M$, Book 173 makes the chosen point automorphic there directly.  Thus all
normal-closure and upward-bridge assertions after those inputs are proved reductions; they are
not part of the post-specialization theorem below.

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
to construct the chosen lift and enables Book 173 to make its restriction automorphic.
Proposition 4.1 constructs the field diagram with $F=M$ once Required Local Theorem 6.2 has
supplied the split base-completion packets, Required Moving Input 6.3a supplies the presentation,
and that presentation satisfies (4.1b).  After those pre-specialization inputs, the missing
object is its arithmetic part: exact post-specialization occurrence in the clean minimal SP
localization.

A **controlled SP bridge package for the chosen lift** consists of that residual seed together
with the ascent ledger and all of the downstream-readiness certificates in Section 4.3.  The
ascent certificate must apply to the exact eigenpacket obtained by evaluating the minimal
Hecke algebra at the chosen point.  It may, for example, be verified uniformly on that Hecke
family; it may not assume in advance that an unrelated packet will represent $\rho|_{G_F}$.
For the normal-top construction the ascent certificate is vacuous.  The elementary-subfield
descent and all-coefficient attachment certificates remain a later, nonvacuous interface.

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
point merely scalar-extends the controlled seed: Book 165's represented local conditions and
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

In the normal-top case of Proposition 4.1, take $F=M$ in Theorem 5.1.  Its output is already a
cuspidal packet $\pi_M$ satisfying

$$
r_{\pi_M,\lambda_M}\simeq\rho|_{G_M}.
\tag{5.2a}
$$

No cyclic base change, solvable ascent, or attachment comparison is used to obtain (5.2a).
Absolute irreducibility follows from closure-level avoidance, and the full SP record is literal
because $2$ splits completely in $M$.  This proves the controlled-top automorphy assertion as
soon as the post-specialization exact seed has been constructed over the normal top.

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
the carrier is constructed after restriction to the normal Galois top of Proposition 4.1.
That proposition supplies normal-closure control, but it does not repair the missing localized
support.

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

### 6.3 The rational ray datum and the normal-top reduction

Book 178 correctly retains a separate relative-ray compatibility hypothesis over a general
totally real base: its inverse-branch lemma cancels the ray-unit obstruction but does not in
general settle capitulation from the base ideal class group.  The present application has base
$K=\mathbf Q$, where that additional obstruction disappears.

**Lemma 6.1 (rational-base relative-ray compatibility).**  In the setup of Book 178,
Section 4, take $K=\mathbf Q$ and write $L/\mathbf Q$ for the CM quadratic field called $M$
there.  Include the conductor of $\eta_{L/\mathbf Q}$ and the real sign in the modulus, and use
the determinant-compatible paired local factors prescribed there.
Then the inverse-branch correction of Book 178, Lemma 4.1, is compatible on the full subgroup
$R$ of Book 178, Section 4.3.  Hence its controlled dihedral seed theorem has an actual
compatible corrected relative ray datum in this rational-base case.

**Proof.**  The diagonal fractional-ideal group of $\mathbf Q$ is principal.  After extension
to $L$, a relation between a diagonal ideal and a ray-principal $L$-ideal is therefore a
relation between two generators of the same principal $L$-ideal; their quotient is a global
unit.  Equivalently, the diagonal map $C_{\mathbf Q}\to C_L$ has trivial kernel: if a rational
idele is the principal $L$-idele of $a\in L^\times$, applying the nontrivial automorphism of
$L/\mathbf Q$ gives $a=a^\sigma$, so $a\in\mathbf Q^\times$.  In the ray exact sequence,
changing either ideal generator changes the relation by a ray unit.
The corrected principal and local rules agree on every ray unit by Book 178, Lemma 4.1.  On a
rational principal idele they agree with the diagonal rule because the original branch factors
were chosen to satisfy (4.4), the modulus contains the conductor of $\eta_{L/\mathbf Q}$, and
the real sign fixes the only rational-unit ambiguity.  Every auxiliary inverse pair introduced
by Lemma 4.1 is trivial on the diagonal copy of $\mathbf Q_v^\times$, so the correction does
not alter this agreement.  The ray exact sequence now shows that these are all relations among
the principal, diagonal, and local-unit subgroups.  Thus the proposed values define a character
of $R$; the finite ray-group extension in Book 178 extends it to the required Hecke character.
$\square$

The class-number-one step is load-bearing.  Over a general $K$, a nonprincipal $K$-ideal can
become principal over its CM quadratic extension and impose a relation not represented by a
rational principal idele or a ray unit, which is why Book 178's general hypothesis remains
correct.

The first unresolved Frey-specific input now occurs in the local completion policy.

**Required Local Theorem 6.2 (split paired-frame seeds).**  Let $Y^{\mathrm{ten}}$ be Book 178's
determinant-compatible two-prime twist for the Frey representation $\bar\rho$ at $\ell$ and the
auxiliary dihedral representation $\bar r$ at $q$, and remove the prescribed degeneracy locus
$Z$.  Construct points

$$
y_2\in(Y^{\mathrm{ten}}\setminus Z)(\mathbf Q_2),
\qquad
y_\ell\in(Y^{\mathrm{ten}}\setminus Z)(\mathbf Q_\ell)
\tag{6.2a}
$$

on the one tensor component, with the corrected auxiliary level and both exact paired frames.
At $2$, the first point must be a semistable tensor point over $\mathbf Q_2$ realizing the
primitive Frey SP Kummer class, intrinsic line, and prescribed split or nonsplit sign.  At
$\ell$, the second must realize the selected ordinary or local--local finite-flat model of
$\bar\rho$ integrally.  In both cases the
auxiliary $q$-frame must occur on that same abelian variety.  The points must admit the
point-centered open neighborhoods of Book 157, Theorem 12.1.  More generally, the same
base-completion assertion is required at every rational place declared completely split in
the controlled top.

Book 157 proves the required openness once the points in (6.2a) exist.  Its coefficient-prime
existence theorem instead allows a finite splitting extension, and its completion-policy audit
states that such a point need not descend.  Book 178 likewise records those extensions in its
ordinary completion algebra.  Thus neither source proves Required Local Theorem 6.2.  A tensor
construction from the Frey curve would still have to solve the auxiliary frame on the same
seed and verify the exact integral and component labels; merely noting that the individual
representations become trivial after extension does not do so.

**Required Moving Input 6.3a (one compatible moving family).**  Starting from the split points
of Required Local Theorem 6.2 and the other extension-valued local packets of Book 178, choose
one common degree, with repetitions or auxiliary good packets only where the assigned arithmetic
condition is stable under that enlargement.  Construct an open $H_0$ of affine space and a
geometrically integral finite étale cover $T_0/H_0$, with evaluation to
$Y^{\mathrm{ten}}\setminus Z$, whose local fibers and point-centered neighborhoods realize all
those cycles simultaneously.  At every place declared split the fiber must be split with all
its evaluated sheets in the assigned open; at every remaining controlled place the pulled-back
normal-closure sheets must retain their assigned local behavior.

Book 154, Lemma 5.2, constructs this presentation automatically for flexible split packets.  In
the exact nonsplit range it says that equality of local ranks is insufficient and retains the
common presentation as a hypothesis.  Book 178 does the same in item 6 and Theorem 8.2.  The
audited sources do not verify Required Moving Input 6.3a for the actual mixture used here.

The nontrivial-stabilizer version of Book 155 would additionally require a special
$S_5/S_4$ evaluation presentation on the paired-frame moduli space.  Proposition 4.1 replaces
that demand.  Once Required Moving Input 6.3a supplies the actual cover, the smaller exact
certificate is $C\cap D=K$ for the constant field $C$ of its Galois closure.  Given that
certificate, multiply the top cover by the universal ordered-quintic torsor, set $J=1$, and
evaluate on the top.  Books 153 and 155 then supply closure-level disjointness and all local top
torsors.  No upward solvable-transfer problem remains.  Neither Required Moving Input 6.3a nor
the constant-field certificate is proved.

The price is exact and arithmetic.  Over the normal top, the distinguished local condition
and every accidental bad place occur on their full finite conjugate sets.  Book 178's literal
one-prime item 7 over its root field does not prove modularity over that top.  One must verify an
ordered clean chain or all seven hypotheses of Book 176, Theorem 9.1, for the actual active set,
and then lower the target residual eigensystem to the exact minimal SP face.  Book 176 proves the
formal implication from those data but does not construct its face modules, global cube, mixed
exactness, product residue, joint support, simultaneous augmentation, or finite-set
reciprocity.

Consequently the current Book 178 route to the controlled seed has the following distinct
unmet tasks:

$$
\begin{array}{ll}
\text{split local input:}&
\text{prove Required Local Theorem 6.2 over }\mathbf Q_2\text{ and }\mathbf Q_\ell;\\
\text{moving-family input:}&
\text{prove Required Moving Input 6.3a for the actual mixed local packets;}\\
\text{field certificate:}&
\text{prove }C\cap D=K\text{ for the paired-frame moving Galois closure;}\\
\text{root-field route:}&
\text{prove (6.1), the remaining one-prime clauses, and }P_{\mathrm{nm}}=\{w_0\};\\
\text{normal-top route:}&
\text{construct the actual finite-set faces and every joint hypothesis of Book 176;}\\
\text{target support:}&
\text{construct the bottom exact minimal Book 173 SP localization.}
\end{array}
\tag{6.3}
$$

The order inside either route is exact.  Lemma 6.1 closes the rational-base ray datum.  Required
Local Theorem 6.2, Required Moving Input 6.3a, and the constant-field certificate remain
pre-specialization.  The one-prime or finite-set data are verified only after the actual bad
set is known.  The target residual eigensystem must then be placed on the bottom minimal SP
face.  Within a face construction, (6.1) is the first unresolved constant row, not a substitute
for the later independent clauses.  Proposition 4.1 proves the remaining field geometry from
the two moving-cover inputs, but a controlled normal closure forces none of these arithmetic
support rows.

### 6.4 Why no formal workaround is available

Several tempting shortcuts fail for precise reasons.

* **Pass to a normal closure afterward.**  The normal closure of an already chosen point field
  need not preserve the avoidance ledger, and automorphy over the root field need not ascend
  through its nonsolvable stabilizer.  Proposition 4.1 avoids both errors by specializing the
  top cover itself and requiring the arithmetic lifting and lowering over that top.
* **Use the local frame point only after extension.**  A proper extension of $\mathbf Q_2$ or
  $\mathbf Q_\ell$ cannot be a completion of any subfield of a top in which that rational prime
  splits completely.  Specializing over such an extension and descending automorphy to a
  separate split top would require a new solvable Galois evaluation and selected-descent datum;
  none is supplied by the ordinary Moret--Bailly field.
* **Force the constant-field intersection by unnamed split primes.**  If split fibers were
  available at primes whose Frobenius classes normally generate $\operatorname{Gal}(D/K)$,
  then their splitting in $C$ would indeed force $C\cap D=K$.  For Book 178's fixed-rank
  nonsplit packets, however, Book 154 assumes one common moving presentation and does not prove
  that it can be enlarged by those extra split packets.  For a fixed presentation, a split
  fiber at a prime acting nontrivially on $C$ is impossible.  Thus this observation is a useful
  certificate test, not an existence theorem for the required presentation.  A fresh
  all-split application of Book 154 would make the argument valid: include such Frobenius
  primes before constructing the flexible split presentation.  But that route requires
  base-completion paired-frame points for every controlled packet and every added prime, not
  merely the two points in (6.2a); no audited local theorem supplies that stronger input.
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

### 7.1 Required post-specialization theorem

After the earlier pre-specialization arithmetic inputs and the constant-field certificate have
been supplied, the field-theoretic part is Proposition 4.1.  The remaining seed theorem should
therefore be stated at the post-specialization boundary and should not demand an arbitrary
prescribed group which the geometry may not realize.

**Required Theorem 7.1 (post-specialization top-clean SP occurrence).**  Let $\ell\geq7$ and
let $\bar\rho:G_{\mathbf Q}\to\operatorname{GL}_2(k)$ be the primitive signed-special Frey
residual representation of Book 164 with the image and local hypotheses required by Book 173.
Fix a finite Galois avoidance field $D$.  Assume that the pre-specialization two-prime package
of Book 178 has actually been constructed, with the rational-base corrected relative ray datum
of Lemma 6.1, the split packets of Required Local Theorem 6.2, its other local packets, Required
Moving Input 6.3a, and a Galois-closure constant field satisfying (4.1b), with the induced local
top packets of Proposition 4.1.  Form its normal-top datum.

Then there is a specialization in the prescribed local and closure-level Hilbert set, with
totally real Galois top $M/\mathbf Q$, for which

$$
\bar\rho|_{G_M}
\tag{7.1}
$$

occurs in the exact nonzero minimal SP localization for $M$ and that localization satisfies
every clean integral hypothesis of Book 173, Theorem 1.1.

The word *occurs* in this statement includes the post-specialization proof record.  A proof by
the two-prime route must list the actual bad sets, construct the required lower-face
automorphic classes, and give either a verified ordered clean chain or the genuine global
finite-set carriers needed to make the auxiliary-adic Tate module automorphic over $M$.  It
must then attach the target-prime residual eigensystem and give saturated lowering maps all the
way to the bottom minimal SP face.  On that bottom face it must verify finite freeness,
stabilizer and diamond control, saturated type and degeneracy maps, the primary--companion
pairing, exact augmentation, generic reducedness, faithful Hecke action, and branchwise integral
local--global compatibility.  Merely producing the auxiliary abelian variety, its torsion
frames, a nonminimal automorphic packet, or numerical level-lowering congruences does not prove
the theorem.

The constant-field certificate, Proposition 4.1, and Required Theorem 7.1 immediately give a
controlled exact SP residual seed: take $F=M$ and $J=1$.  The degree is even, $2$ and $\ell$
split completely, closure-level avoidance gives (3.3), and (7.1) supplies the entire arithmetic
seed.  Thus no additional
normal-closure or upward-transfer theorem is hidden in this implication.

The proof of the automorphic-support assertion must be acyclic.  It may use the independent
ray and field-geometric reductions of Lemma 6.1 and Proposition 4.1, but it may not use Book
181's characteristic-zero output, Proposition 3.2 or Theorem 5.1 of this volume, the elementary
packet array of Book 183, the effectivity theorem of Book 184, the compatible system of Book
185, or any later theorem whose hypotheses include those outputs.  Book 173 may be applied only
after the bottom localization and all of its hypotheses have been independently constructed.

No theorem with this conclusion occurs among the audited prerequisites.  Required Theorem 7.1
is therefore the exact post-specialization theorem needed to close the seed, not a result proved
in this volume.

### 7.2 Smallest presently isolated subtheorem

For a general totally real base, Book 178's first unproved arithmetic input remains its
compatible corrected relative ray datum.  For the Frey application over $\mathbf Q$, Lemma 6.1
proves that compatibility.  Required Local Theorem 6.2 is then the first unresolved
pre-specialization arithmetic assertion: the prior local theorem supplies the needed paired
frames only after a finite extension, whereas the controlled top requires split base-completion
points.  Required Moving Input 6.3a is the next field-geometric assertion: the prior
approximation theorem retains rather than constructs a common presentation for the exact
nonsplit packets.  After that presentation and its constant-field certificate, the first
unresolved constant-row assertion in the actual lifting comparison is (6.1).  A localized
Ihara theorem proving that finite family does not produce the
independent type, localization, support, reciprocity, ray, augmentation, and faithful-order
clauses.

For Book 178's post-specialization boundary, the next obligation on the current route is not a
finite-clean-chain theorem.  It is the existential singleton assertion:

> Produce at least one specialized two-prime Hilbert--Blumenthal output, list its actual bad
> set and lower residual carrier, perform every required proved saturated lowering of
> superfluous dihedral conductor, and verify
> $P_{\mathrm{nm}}=\{w_0\}$ with named minimal spectator matching everywhere else.

That is the literal content of Book 178, Section 2.5, item 7 over its root field.  On the
normal-top route it is replaced by an actual finite-set verification over $M$; citing the
conditional conclusion of Book 176 without constructing its faces does not do this.

After the auxiliary-prime lift is automorphic, the first irreducible target-prime assertion is
the existence of the bottom lower-face class itself.  Book 176 compares a supplied global cube
and proves pointwise modularity from its hypotheses; it does not manufacture the minimal face
from the upper packet.  The exact missing assertion is therefore that the specialized target
eigensystem has a saturated path to a nonzero clean minimal SP localization.  Once that is
proved with all Book 173 clauses, Required Theorem 7.1 is complete.  After the separately stated
constant-field certificate, normal-closure geometry is no longer an additional blocker.

### 7.3 The later bridge-readiness obligation

For the normal-top seed, there is no ascent ledger: $F=M$.  At the distinguished coefficient,
the local and group-theoretic part of the downward ledger reduces once Theorem 5.1 has produced
the minimal packet.
Every place above $2$ or $\ell$ splits at every intermediate step; the dyadic special factor is
therefore unchanged.  Every other finite factor is spherical.  In a nonsplit cyclic step, the
extensions of such a spherical parameter are principal-series or selected tame-dihedral
factors.  Indeed, local Clifford theory makes every irreducible rank-two extension across a
prime cyclic quotient dihedral, and it can occur only across a quadratic step; away from two a
ramified quadratic step is tame.  The only omitted rank-two boundary is therefore ramified
dyadic, which complete splitting excludes.  This proves extension-completeness for the whole
fixed-determinant fiber, not merely for the extension selected by $\rho$.
Quotient-character twists remain in the same selected families.  The real weight-two discrete
series supplies the strongly cuspidal comparison factor.  Closure-level avoidance preserves
absolute irreducibility of $\bar\rho|_{G_M}$; the stable lattice therefore forces
$\rho|_{G_M}$ to be irreducible.  Finally, $\rho$ is defined on $G_{\mathbf Q}$, so it supplies
the coherent extension that would select the quotient-character correction in Book 109,
Theorem 13.3.

That last selection is not yet a descent theorem in the present source range.  Book 109 also
assumes that the arbitrary cuspidal descent at each cyclic step has an attached arithmetic
representation and that attachment commutes with cyclic base change and finite-order twisting.
The extending representation $\rho$ compares two such attached extensions; it does not attach
the arbitrary descent in the first place.  Consequently the distinguished-coefficient descent
array still requires a Galois-attachment certificate for every candidate cyclic descent, in
addition to the admissibility and fiber-saturation checks above.

The full Book 183 interface is stronger still.  Each corrected packet must have a curve-attached
family at every coefficient embedding and the same algebraic dyadic SP pair must survive the
raw-to-semisimple passage uniformly.  The present sources do not prove this.  First, some
elementary fixed fields necessarily have odd degree in the normal-top construction: a Sylow
$2$-subgroup $P\leq\Gamma$ is elementary, $[\Gamma:P]$ is odd, and the $S_5$ quotient makes
that index greater than one.  More generally, every even-order top group has an elementary
Sylow $2$-subgroup of odd index, so changing the auxiliary even group cannot remove the parity
boundary.  Book 127's one-split carrier and attachment theorem is proved in the required inverse
range only for even degree.  This already prevents the presently cited attachment theorem from
supplying the distinguished realization needed to run Book 109 at every elementary fixed field,
and a fortiori prevents the all-coefficient interface.
Second, already for the trivial elementary subgroup $H=1$, the top minimal packet $\pi_M$ is
spherical away from the dyadic SP factors and the clean coefficient-prime factor is not
supplied as a selected special or tame-dihedral place.  Downward extension fibers can acquire
selected tame-dihedral factors, but that does not furnish an away-from-two factor for this top
packet.  A dyadic special factor gives a general curve carrier in the even-degree range, but a
carrier ramified at any dyadic factor fails the dyadically tensor-split ledger recorded in Book 168,
Corollary 12.2.  Its raw SP construction instead requires an odd nonempty eligible ramification
set away from $2$, and this minimal packet has no such place.  Third, even if that
raw carrier were supplied, Book 168 passes the raw SP pair to the globally semisimplified
member from absolute residual irreducibility only coefficient place by coefficient place; the
current argument proves it at the distinguished coefficient, not at every coefficient place.

Consequently the exact later bridge theorem is an **all-elementary attachment, descent, and
uniform-SP theorem**.  It must supply distinguished-coefficient attachment, with cyclic
base-change and twist compatibility, for the candidate descent packets so that Book 109 can
select the corrections; provide the missing odd-degree carriers; construct a raw dyadic SP
carrier without a pre-existing eligible place away from $2$ (or give another attachment
construction); and prove raw-to-semisimple local preservation at every
coefficient place.  This later theorem must not be bundled into Required Theorem 7.1 or used to
obscure the earlier failure to construct the minimal residual seed itself.  It must also be
strictly prior to Book 183: the elementary packet array, its effectivity, and the descended
compatible system cannot be used backward to prove the attachment or uniform-SP hypotheses
which that array consumes.

## 8. Dependency, circularity, and downstream audit

### 8.1 What each prior book really supplies

| Source | Legitimate use here | What it does not supply |
|---|---|---|
| Book 109 | prime-cyclic ascent on an exhibited extension-complete selected chain, and descent on exhibited antecedent-complete selected chains with the required fiber saturation and attached arithmetic representations | attachment of candidate cyclic descents, or either direction from solvability alone |
| Books 127--128 and 168 | weight-two coefficient attachment and the SP local comparison in their explicitly stated range | an automatic all-coefficient SP comparison for an arbitrary packet |
| Book 164 | the primitive residual Frey SP tuple, intrinsic line, sign, and conductor-one record used in the FLT specialization | a characteristic-zero chosen lift or automorphic seed |
| Book 173 | exact minimal $R=\mathbb T$ and automorphy of every point of a clean minimal deformation problem | existence of the exact residual automorphic localization |
| Book 175 | a local change at a previously named place under its exact clean augmentation hypotheses | simultaneous lowering at the unknown extra bad primes of a specialization |
| Book 176 | a conditional finite-set reduced comparison and pointwise modularity from one supplied global cube and all its joint hypotheses | the face classes, cube, mixed exactness, product residue, joint support, augmentation, or reciprocity for an actual specialization |
| Book 177 | a conditional two-prime potential-modularity route and point-field control in its admitted range | an unconditional clean seed or controlled normal closure |
| Book 153 | simultaneous connected specialization for the integral top cover and its avoidance-field base change | the constant-field disjointness certificate or any automorphic support |
| Book 154 | construction of a simultaneous moving presentation in the flexible split range and globalization from a supplied presentation in the exact local-algebra range | the common presentation for Book 178's actual mixed nonsplit packets, the constant field of its Galois closure, its intersection with $D$, or post-specialization automorphic support |
| Book 155 | equivariant local constancy and the regular ordered-quintic torsor | the paired-frame constant-field certificate or any automorphic lifting and lowering on the specialized top |
| Book 157 | point-centered opens around simultaneous paired-frame seeds and persistence after permitted extension | descent of coefficient-prime or semistable frame points from a proper completion extension to $\mathbf Q_2$ or $\mathbf Q_\ell$ as required by complete splitting |
| Book 178 | conditional residual potential modularity for a fixed seven-item two-prime-admissible witness; after lifting, proof of final compact-carrier eligibility; its inverse-branch lemma, completed over $\mathbf Q$ by Lemma 6.1 here | over a general base, the capitulation part of the corrected relative ray datum; a specialization satisfying item 7's literal singleton condition; or the exact minimal Book 173 SP seed |
| Book 180 | integral Brauer and Clifford identities for supplied representations, characters, and packet data | construction or attachment of any elementary fixed-field packet, or the all-embedding SP comparison |
| Books 165--167 | the SP local deformation problem, supported cohomology, and balanced presentation | a horizontal point or a nonzero exact automorphic module |
| Book 181 | under $(\mathrm{Seed}_{\mathrm{SP}}^{181})$, finite-flatness of the balanced global SP ring and the normalized primitive SP point used here | construction of its seed, normal-closure control, or the controlled seed required in Section 4 |

Book 181 now genuinely supplies the chosen point conditional on its exact seed; this volume no
longer treats that point as a free-standing assumption.  Proposition 3.2 also extracts its
automorphy over Book 181's seed field.  The controlled seed remains stronger and unproved.

### 8.2 Direct dependency recommendation

For the conditional theorem actually proved here, the honest direct dependency row is

$$
\boxed{
182\mid 109,127,128,153,154,155,157,164,165,168,173,176,178,181.}
\tag{8.1}
$$

Book 175 is a transitive input through Book 178.  Books 177 and 180 are comparative background
for the seed and downstream bridge audits; Book 180's abstract machinery is consumed by Book
183 only after the packets exist.  Neither is used in the conditional proof, so neither is a
direct edge here.  Books 166--167 are direct inputs to Book 181, but transitive for this volume.
Book 165 is retained because this volume directly identifies the represented local SP problem;
it could be made transitive by treating all local identifications as part of the Book 181
export.

Equation (8.1) does not make the result unconditional.  To mark Book 182 **READY**, a new
strictly prior result must prove Required Local Theorem 6.2, Required Moving Input 6.3a, the
constant-field certificate, and Required Theorem 7.1; a prior all-elementary attachment,
descent, and uniform-SP theorem of Section 7.3 is also required.  Those results belong in their natural
prior owners; no book number may be put in a slot merely because it states the conclusion
conditionally.

### 8.3 Proof-order audit

The acyclic order is

$$
\begin{array}{c}
\text{primitive residual SP datum}
\\ \Downarrow \\
\text{Lemma 6.1, Required Local Theorem 6.2, Required Moving Input 6.3a, and }C\cap D=\mathbf Q
\\ \Downarrow \\
\text{Proposition 4.1: normal Galois top with }F=M\text{ and }J=1
\\ \Downarrow \\
\text{Required Theorem 7.1: post-specialization top-clean residual seed}
\\ \Downarrow \\
\text{the controlled seed supplies }(\mathrm{Seed}_{\mathrm{SP}}^{181})
\\ \Downarrow \\
\text{Book 181: a normalized primitive chosen SP lift }\rho
\\ \Downarrow \\
\text{Book 173: }R_M^{\mathrm{SP}}=\mathbb T_M^{\mathrm{SP}}
\\ \Downarrow \\
\rho|_{G_M}\text{ is automorphic, with no upward base change}
\\ \Downarrow \\
\text{distinguished attachment and cyclic compatibility for candidate descents}
\\ \Downarrow \\
\text{Book 109: distinguished-coefficient elementary descents selected by }\rho
\\ \Downarrow \\
\text{all-coefficient attachment and uniform-SP completion}
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
over Book 181's uncontrolled seed field.  Proposition 4.1 now proves the field-theoretic
refinement needed here from two sharply isolated inputs: Required Moving Input 6.3a supplies
the actual mixed local moving cover, and its Galois-closure constant field $C$ must satisfy
$C\cap D=\mathbf Q$.  Multiplying that closure by an independent ordered-quintic torsor and
specializing the top together with its $D$-base change then gives an even-degree totally real
normal top with $F=M$, $J=1$, split sensitive places, and closure-level avoidance.
Consequently no moduli-specific $S_5/S_4$ presentation and no upward solvable base change
remain after those inputs.  The prerequisites construct the flexible split presentation, but
not the actual mixed one; they also do not compute $C$ or prove the required intersection.

Over a general base Book 178 still correctly retains full relative-ray compatibility.  For the
rational Frey application, Lemma 6.1 proves that compatibility from its inverse-branch
correction and the determinant-compatible local choices.  The first remaining
pre-specialization arithmetic assertion is Required Local Theorem 6.2: simultaneous paired-frame
seeds must exist over $\mathbf Q_2$ and $\mathbf Q_\ell$ themselves, since points obtained only
after proper local extension are incompatible with complete splitting in the top.  Required
Moving Input 6.3a and the constant-field intersection are the subsequent pre-specialization
geometric obligations.  The localized abelian Ihara family (6.1) is then the first missing
constant row in the lifting comparison, and it does not imply the other faces or the bottom
carrier.  After those earlier inputs, Required Theorem 7.1 is the exact remaining seed theorem:
among the normal-top specializations, construct one whose target eigensystem reaches a nonzero
bottom minimal SP localization satisfying every clean hypothesis of Book 173.  The irreducible
post-specialization obstruction is that clean bottom minimal-SP occurrence itself; Book 176
consumes such face data and does not construct it.

After that seed exists, Books 181 and 173 make the chosen lift automorphic directly over $M$.
Section 7.3 reduces the local and group-theoretic descent checks using the extension of $\rho$
and the split minimal local support, but Book 109 still needs distinguished Galois attachment
for each candidate cyclic descent before $\rho$ can select its correction.  The remaining later
bridge blocker is therefore the all-elementary attachment, descent, and uniform-SP theorem:
current sources do not cover every
odd-degree fixed field in the needed one-split curve range, do not construct the dyadically
split raw SP carrier from a minimal packet with no eligible place away from $2$, and do not
preserve the raw SP pair at every coefficient embedding.  This is separate from Required
Theorem 7.1 and from the normal-closure construction.

Accordingly,

$$
\boxed{\text{NOT READY}.}
$$
