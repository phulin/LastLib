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
over a general totally real base, but Book 178, Lemma 4.1A proves it from the inverse-branch correction
in the rational-base case used here.  Theorem 6.2 applies Book 178's protected
anti-cyclotomic Grunwald correction to prescribe the exact unramified Frobenius values at the
three retained small completions.  Proposition 6.2A then constructs paired-frame seeds over
$\mathbf Q_2$, $\mathbf Q_3$, and $\mathbf Q_\ell$ themselves by adapting the local elliptic
seeds and neat source.  Proposition 4.2
forces constant-field disjointness by adding large split Chebotarev certificate primes.  The
next pre-specialization issue is Book 178, item 6's one-special, all-other-good packet: it must
occur in one simultaneous moving presentation and satisfy the full allowed-good Abel condition
(6.3a'), or the restricted norm--Abel congruence (6.3a).  After that, adjoin an independent
ordered-quintic torsor and use the normal top as the field of definition.
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
\text{the raw local-geometry and prime-to-two preservation certificates remain}.
\end{array}
\tag{1.2}
$$

No earlier unconditional theorem constructs the first line of (1.2) for the Frey datum with
all of the required post-specialization lower faces and clean minimal support.  Propositions
4.1--4.2 construct its normal-closure field diagram from a compatible moving cover, and Section
7.3 reduces the local and group-theoretic part of the
elementary descent ledger.  Proposition 7.2A now supplies basic all-coefficient attachment for
every candidate packet and its cyclic compatibility, so Book 109 can select the
quotient-character correction once the candidate is automorphic.  The raw SP geometry,
auxiliary-place return data, and uniform raw-to-global preservation remain separate.  Book 181
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
4. $2$, $3$, and $\ell$, and every other sensitive rational place named in advance, split completely
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
controlled top must split completely at $2$, $3$, and $\ell$, Proposition 4.1 therefore needs actual
paired-frame points over $\mathbf Q_2$, $\mathbf Q_3$, and $\mathbf Q_\ell$, not points over recorded proper
extensions.  Book 178 constructs its distinguished special seed over its base completion, but
no earlier moduli theorem proves these three simultaneous base-field frame assertions for the
Frey and auxiliary systems.  Theorem 6.2 first repairs the exact auxiliary Frobenius branches
by Book 178's character-theoretic correction.  Proposition 6.2A then repairs the local geometry
by changing the local elliptic seeds and neat source; it does not contradict Book 157's
no-descent warning.

Geometric integrality of $T_0$ does not force $C=K$: a regular non-Galois function-field
extension can acquire constants in its Galois closure.  Full regularity of the closure is a
sufficient special case of (4.1b), but it is stronger than necessary.  Book 154 constructs
$T_0/H_0$ for flexible split packets, and Lemma 5.2A extends this to exact packets which may be
repeated wholesale.  It does not construct Book 178's singleton special packet.  Full symmetric
geometric monodromy would imply $C=K$, but it is unnecessary: Proposition 4.2 below forces only
the required intersection.  Thus the sole surviving field-geometric obligation is the actual
mixed moving presentation.  Once it is supplied, Propositions 4.1--4.2 prove every other
normal-closure and upward-bridge assertion.

The constant-field input can be forced without computing the generic permutation group.  It
must be imposed while the moving presentation is constructed, not after its Galois closure has
been fixed.

**Proposition 4.2 (split-prime certificate for the constant field).**  Let $U/K$ be a fixed
smooth geometrically connected positive-dimensional variety, let $D/K$ be finite Galois, and
suppose a simultaneous moving presentation for the required packets is still to be chosen.
There is a finite set $S_{\mathrm{cert}}$ of additional finite places with
$U(K_v)\ne\varnothing$ such that every presentation having a split evaluated fiber at all
$v\in S_{\mathrm{cert}}$ satisfies

$$
C\cap D=K
\tag{4.1d}
$$

for the constant field $C$ of the Galois closure of its incidence cover.

**Proof.**  Choose elements $g_1,\ldots,g_t$ whose conjugacy classes normally generate
$\operatorname{Gal}(D/K)$.  Book 157, Proposition 9.3 gives $U(K_v)\ne\varnothing$ at every
sufficiently large good place.  Book 142's Chebotarev theorem therefore lets us choose
pairwise distinct, sufficiently large unramified places $v_i$, outside every previously
protected set, whose
Frobenius classes in $D/K$ are the classes of the $g_i$.  Put
$S_{\mathrm{cert}}=\{v_1,\ldots,v_t\}$.  Small neighborhoods of the chosen $U(K_{v_i})$-points
give flexible split packets for the moving problem.

Let $E_0/K(H_0)$ be the Galois closure of a presentation containing those split fibers.  Its
action on the roots of the incidence cover is faithful, and its field of constants $C$ is
Galois over $K$ because $E_0/K(H_0)$ is normal.  At $v_i$ the split incidence fiber has trivial
local splitting field, so the specialized homomorphism from $G_{K_{v_i}}$ to that faithful
permutation group is trivial.  Its constant quotient is therefore trivial as well, and $v_i$
splits completely in $C/K$.  Put
$I=C\cap D$.  The image of $g_i$ in $\operatorname{Gal}(I/K)$ is the Frobenius at $v_i$, hence
is trivial.  Since the conjugacy classes of the $g_i$ normally generate the Galois group of
$D/K$, they generate every quotient; consequently $\operatorname{Gal}(I/K)=1$.  This proves
(4.1d). $\square$

The order of choices is important but noncircular:

$$
U,D\ ;\quad S_{\mathrm{cert}}\ ;\quad
\text{one moving presentation including the certificate packets}\ ;\quad C.
\tag{4.1e}
$$

The Hasse--Weil argument in Book 157 supplies points only at large good places, which is exactly
what Chebotarev permits here.  It does not supply any of the three small base-completion points in
Proposition 6.2A or the exact auxiliary branches required by Theorem 6.2.

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
empty.  Once the compatible moving cover and the exact seed exist over $M$, Proposition 4.2
supplies the constant-field certificate and Book 173 makes the chosen point automorphic there
directly.  Thus all
normal-closure and upward-bridge assertions after those inputs are proved reductions; they are
not part of the post-specialization theorem below.

The top packet eventually delivered to Book 183 needs a second, finite ledger.  For every
elementary subgroup $H\leq\Gamma$, at least one prime-cyclic descent chain from $M$ to $M^H$
must satisfy Book 109's descent-admissibility and fiber-saturation hypotheses.  Every corrected
packet along those chains must lie in the all-coefficient weight-two attachment range of Books 127--128 and 168.  At the dyadic places, their special-scalar and raw-to-semisimple local-preservation
hypotheses must be verified uniformly.  Book 168, Proposition 7.6 reduces the latter
requirement to $(\mathrm{SS}_{\mathrm{array}})$, semisimplicity of the ambient $H^1$ of each
actual curve carrier in every relevant coefficient characteristic.  The rational Tate-module
theorem $(\mathrm{TS})$ for their Jacobians is sufficient, but the current dependency chain
does not prove it.  These conditions are exactly why Book 183 calls its top packet “selected.”

At every retained auxiliary prime, the same certificate must be strict enough for the later
finite support test.  A spherical row includes the complete good model and hyperspecial
comparison.  A principal or tame-dihedral row includes the actual descended finite
nearby-cycle complex, type and exchange lines, the proof that $N=0$, every Frobenius return map,
at the distinguished coefficient and at each auxiliary coefficient later retained. Book 128,
Lemma 3.2 then gives raw-to-global passage formally from $N=0$. These are the data called $(\mathrm{AUX}_\nu)$ and
$(\mathrm{AUX}_{\mathrm{all}})$ after assembly in Book 185.  Books 128 and 168 recognize the
local parameter from such data but do not construct the geometric complex, lines, or return
maps.  They therefore belong to this
controlled attachment interface before Book 183, not to a new theorem derived from the Brauer
complement afterward.

This volume does not construct the elementary packets.  That is the subject of Book 183.  It
only identifies the certificates which must accompany $\pi_M$ so that Book 183 may construct
them without replacing arithmetic admissibility by group solvability.

### 4.4 Two interfaces which must not be conflated

A **controlled exact SP residual seed** consists of the field diagram
$(M,\Gamma,J,F)$ of Section 4.1 and an exact SP automorphic seed for
$\bar\rho|_{G_F}$.  Its automorphic clauses are the controlled analogue of
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$; the new content is that the seed field is embedded in
the prescribed normal-closure diagram.  Since $[F:\mathbf Q]$ is even and $2$ and $\ell$
split completely, forgetting the additional split-three condition in the top diagram gives precisely a permissible
$(\mathrm{Seed}_{\mathrm{SP}}^{181})$.  Thus this single controlled seed both enables Book 181
to construct the chosen lift and enables Book 173 to make its restriction automorphic.
Proposition 4.1 constructs the field diagram with $F=M$ once Theorem 6.2 and Proposition 6.2A
have supplied the split base-completion packets, Required Moving Theorem
6.3 supplies the presentation, and Proposition 4.2 verifies (4.1b).  After those
pre-specialization inputs, the missing
object is its arithmetic part: exact post-specialization occurrence in the clean minimal SP
localization.

A **controlled SP bridge package for the chosen lift** consists of that residual seed together
with the ascent ledger and all of the downstream-readiness certificates in Section 4.3.  The
ascent certificate must apply to the exact eigenpacket obtained by evaluating the minimal
Hecke algebra at the chosen point.  It may, for example, be verified uniformly on that Hecke
family; it may not assume in advance that an unrelated packet will represent $\rho|_{G_F}$.
For the normal-top construction the ascent certificate is vacuous.  The elementary-subfield
descent remains a later, nonvacuous interface.  Proposition 7.2A supplies its candidate packets
with basic all-coefficient attachment; raw local geometry and uniform preservation remain.

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

**Lemma 6.1 (rational-base relative-ray compatibility; alias).**  In the setup of Book 178,
Section 4, take $K=\mathbf Q$ and write $L/\mathbf Q$ for the CM quadratic field called $M$
there.  Include the conductor of $\eta_{L/\mathbf Q}$ and the real sign in the modulus, and use
the determinant-compatible paired local factors prescribed there.
Then the inverse-branch correction of Book 178, Lemma 4.1, is compatible on the full subgroup
$R$ of Book 178, Section 4.3.  Hence its controlled dihedral seed theorem has an actual
compatible corrected relative ray datum in this rational-base case.

**Proof.**  This is Book 178, Lemma 4.1A. $\square$

The class-number-one step is load-bearing.  Over a general $K$, a nonprincipal $K$-ideal can
become principal over its CM quadratic extension and impose a relation not represented by a
rational principal idele or a ray unit, which is why Book 178's general hypothesis remains
correct.

The freedom to choose the auxiliary dihedral character does solve the apparent
local-completion problem, but not by the ray-class extension inside Book 178, Theorem 4.2.
One first constructs that character and then applies the protected anti-cyclotomic
Grunwald correction of Book 178, Lemma 4.3.

**Theorem 6.2 (exact protected Frobenius branches).**  Let $E_F/\mathbf Q$ be the Frey curve.
Choose $q\geq7$ outside Book 178's finite exclusion set and outside $\{\ell\}$.  For every
$v\in\{3,\ell\}$ at which $E_F$ has good reduction, require also

$$
q\nmid a_v(E_F)^2-4v.
\tag{6.2a}
$$

Then there is a CM quadratic field split at $2$, $3$, $\ell$, and $q$, and a Book 178 controlled
dihedral character with actual residual coefficient field $k_q$, retaining its independent
cyclotomic-irreducibility witness and all finite-flat conditions, for which

$$
\bar r|_{G_{\mathbf Q_v}}\simeq
\begin{cases}
(\eta_v\oplus\eta_v\bar\chi_q)\otimes_{\mathbf F_q}k_q,
 &E_F\text{ multiplicative at }v,\\
E_F[q]\otimes_{\mathbf F_q}k_q,&v\in\{3,\ell\}\text{ and }E_F\text{ good at }v,
\end{cases}
\qquad(v=2,3,\ell),
\tag{6.2b}
$$

including the displayed unramified Frobenius values, not only the restrictions to inertia.
Book 164's semistability theorem makes the two displayed reduction cases exhaustive at $3$ and
$\ell$; the signed Frey condition supplies the multiplicative row at $2$.

**Proof.**  Choose $q$ with the displayed exclusions and all of Book 178's independent
exclusions.  At each good place in $\{3,\ell\}$, the extra condition makes the two Frobenius roots of
$E_F[q]$ distinct, so after extending the residual coefficient field they give two unramified
characters.  Choose the CM quadratic field split at $2$, $3$, $\ell$, and $q$ by Book 178, Section
4.7.  Lemma 6.1 supplies the compatible rational-base relative ray datum.  Book 178, Theorem
4.2 then constructs a controlled dihedral character with its auxiliary-prime finite-flat
behavior and protected cyclotomic-irreducibility witness.

At each of $2$, $3$, and $\ell$, the desired pair in (6.2b) has the same determinant as the
constructed induced representation.  At a multiplicative place this is
$\eta_v^2\bar\chi_q=\bar\chi_q$; at a good place it follows from the Weil pairing
on $E_F[q]$.  Apply Book 178, Lemma 4.3 with these three places as $S$ and put every place above
$q$, the independent conjugate-ratio witness, and all earlier protected local factors away from
$2$, $3$, and $\ell$ in its set $P$.  Equations (4.19)--(4.20) there correct one branch by the required quotient and the
conjugate branch by its inverse.  Hence the residual branch pairs become exactly (6.2b).

The anti-cyclotomic correcting character is trivial on $C_{\mathbf Q}$, so the determinant and
infinity type are unchanged.  It is exactly trivial at $P$, so finite flatness at $q$ and the
cyclotomic-irreducibility witness survive.  Book 6's Wang exception may double the order of the
correcting character, but that order remains prime to the odd prime $q$, so reduction retains
all prescribed values.  Enlarge the character field after the correction and call its actual
residue field $k_q$.  This proves the theorem. $\square$

The distinction between the two stages is load-bearing.  Book 178, Theorem 4.2 alone protects
inertia and Section 4.6 correctly warns that its ray-class extension can change a uniformizer
value.  Book 178, Lemma 4.3 repairs the full local character afterward using Book 6's exact
Grunwald--Wang theorem.  Smooth-point and Hensel arguments still cannot choose these
unramified values; the character-theoretic correction is what does so.

This is not cosmetic for the dyadic tensor construction.  A semistable elliptic seed carrying
the nonzero Frey $\ell$-Kummer class has splitting character $\eta_2$.  Since the CM field is
split at $2$, $\bar r|_{G_{\mathbf Q_2}}$ is semisimple.  Book 44's Tate sequence then says that
a paired $q$-frame on the same seed forces its Tate parameter to be a $q$th power and forces the
two diagonal characters to be
$\eta_2$ and $\eta_2\bar\chi_q$.  Thus the first line of (6.2b) is necessary for the available
tensor-Tate route.  A non-tensor Hilbert--Blumenthal construction avoiding that condition would
itself be a new base-field simultaneous-frame theorem, not an output of smoothness or Hensel
lifting.

The local geometry after Theorem 6.2 is completely constructible.

**Proposition 6.2A (exact base-completion seeds from exact branches).**  After choosing the
neat source, let $Z\subsetneq Y^{\mathrm{ten}}$ be the prescribed proper closed degeneracy
locus.  Book 178's
determinant-compatible two-prime twist $Y^{\mathrm{ten}}$ has points

$$
y_2\in(Y^{\mathrm{ten}}\setminus Z)(\mathbf Q_2),
\qquad
y_3\in(Y^{\mathrm{ten}}\setminus Z)(\mathbf Q_3),
\qquad
y_\ell\in(Y^{\mathrm{ten}}\setminus Z)(\mathbf Q_\ell)
\tag{6.2c}
$$

on one tensor component, with both exact paired frames and one common auxiliary level.  The
dyadic point is semistable over $\mathbf Q_2$, with the prescribed unramified splitting
character, and realizes the primitive Frey SP Kummer class, intrinsic line, and sign.  The
$3$-adic point realizes the exact Frey $\ell$-frame and corrected auxiliary $q$-frame.  The
$\ell$-adic point realizes the selected finite-flat Frey model integrally.  All three points
have the point-centered neighborhoods of Book 157, Theorem 12.1.

**Proof.**  Let $u_v$ be the Frey Tate parameter at a multiplicative place $v$.  Apply Book
178, Theorem 2.1 to the representation furnished by Theorem 6.2 and choose
its neat integer $N$ prime to $6\ell q$.  We now construct
elliptic seeds $B_v/\mathbf Q_v$ for $v\in\{2,3,\ell\}$.  At a good place put $B_v=E_F$.  At any
multiplicative place put $K=\mathbf Q_v$.  Since
$K^\times/(K^\times)^\ell$ has exponent $\ell$ and $(qN,\ell)=1$, raising to the $qN$th power
is an automorphism of that quotient.  Choose $b_v\in K^\times$ with

$$
[b_v^{qN}]=[u_v]\quad\text{in }K^\times/(K^\times)^\ell.
\tag{6.2d}
$$

Multiplying $b_v$ by a sufficiently large positive $\ell$th power of a uniformizer makes
$t_v=b_v^{qN}$ have positive valuation without changing (6.2d).  Let $B_v$ be the Tate curve
with parameter $t_v$, descended by the same unramified quadratic character $\eta_v$ in the
nonsplit case.  The Frey/Tate Kummer calculations of Book 164, Sections 5.2, 6.2, and 7.1 give
paired isomorphisms

$$
B_v[\ell]\simeq E_F[\ell],
\qquad
B_v[q]\otimes_{\mathbf F_q}k_q\simeq
(\eta_v\oplus\eta_v\bar\chi_q)\otimes_{\mathbf F_q}k_q,
\tag{6.2e}
$$

because the first extension classes agree by (6.2d) and the second splits because
$t_v\in(K^\times)^q$.  At a good place in $\{3,\ell\}$, the choice $B_v=E_F$ and the second
line of (6.2b) give the same two paired frames tautologically.  At $v=2$, the first isomorphism preserves the canonical multiplicative
line, the nonzero primitive Kummer class, and $\eta_2$, hence the exact Frey sign and SP datum.
At $v=\ell$, if reduction is multiplicative, both $B_\ell[\ell]$ and $E_F[\ell]$ have finite-flat
models over $\mathbf Z_\ell$ and the generic isomorphism in (6.2e) extends uniquely by Raynaud
full faithfulness in ramification index $1<\ell-1$; it therefore identifies the selected
integral model and its pairing.  In the good case the equality $B_\ell=E_F$ already gives that
identification.  Thus ordinary, local--local, and multiplicative finite-flat cases are all
covered over $\mathbf Q_\ell$ itself.  Choose Book 178, Theorem 2.1's determinant-line
orientations from these canonical Weil pairings; the displayed isomorphisms are then paired at
all three base completions, rather than merely unpaired module isomorphisms.

At $q$, and at every other finite place where the completion policy requires the auxiliary
$N$-source to remain unramified, choose an arbitrary good elliptic curve and a sufficiently
small good-reduction neighborhood.  Book 157, Lemma 4.1B now chooses one elliptic curve
$E_*/\mathbf Q$ meeting those neighborhoods and with paired local isomorphisms

$$
E_*[N]|_{G_{\mathbf Q_v}}\simeq B_v[N]
\qquad(v=2,3,\ell).
\tag{6.2f}
$$

Thus the new source is unramified at every unramified-only auxiliary place; after the permitted
unramified enlargement there, it can be paired with the chosen local seed.  This extra
goodness condition is independent of the exact base-completion matching in (6.2f).

Use the elliptic-source level of Book 157, Proposition 4.1A.  The tensor points
$B_v\otimes_{\mathbf Z}\mathcal O_E$, equipped with (6.2b), (6.2e), and (6.2f), therefore lie
on the same $\mathbf Q$-defined tensor component and carry the auxiliary level and both exact
paired frames at all three base completions.  The local models just verified give the required integral labels.  The frame
isomorphism schemes are finite etale on the characteristic-zero neighborhoods, while the good,
finite-flat-type, sign, valuation, and Kummer-shell conditions are open in the forms proved in
Book 157.  Finally a proper closed subset of a smooth geometrically integral component has
empty interior in its $\mathbf Q_v$-analytic manifold.  Perturbing inside the resulting
point-centered neighborhoods removes $Z$ and gives (6.2c). $\square$

This proof does not descend a point produced over a local extension.  It adapts the auxiliary
neat source to elliptic curves whose $\ell$-torsion is the fixed Frey module.  No automorphy of
the Frey representation is used.

**Required Moving Theorem 6.3 (the singleton mixed packet).**  Starting from the split points
of Proposition 6.2A, the flexible split certificate packets selected in Proposition 4.2, and
the other extension-valued local packets of Book 178, choose
one common degree, with repetitions or auxiliary good packets only where the assigned arithmetic
condition is stable under that enlargement.  Construct an open $H_0$ of affine space and a
geometrically integral finite étale cover $T_0/H_0$, with evaluation to
$Y^{\mathrm{ten}}\setminus Z$, whose local fibers and point-centered neighborhoods realize all
those cycles simultaneously.  At every place declared split the fiber must be split with all
its evaluated sheets in the assigned open; at every remaining controlled place the pulled-back
normal-closure sheets must retain their assigned local behavior.

Book 154, Lemma 5.2 constructs the flexible split packets, and Lemma 5.2A now constructs every
exact nonsplit packet which may be repeated wholesale.  Repeating a complete Book 178 packet
preserves its factorwise assigned neighborhoods and algebra.  The remaining case is precisely
item 6's completion algebra at $v_0$: it must contain one distinguished degree-one special
factor, while all added factors must be good minimal.  On the local curve used by the moving
proof, write $V_{\mathrm{sp}}$ for the assigned degree-one special neighborhood,
$S\in V_{\mathrm{sp}}$ for a chosen representative, $P$ for a good point, $\mathcal A$ for the
pencil line bundle of degree $e$, and put

$$
b=[\mathcal A]-e[P],
\qquad c=[S-P].
$$

For each $d$, let $\mathscr R^{\mathrm{good}}_{v_0,d}$ be Book 154, (5.4e)'s set of classes
$[D-dP]$, where $D$ is reduced of degree $d$, disjoint from $S$, and every residue-field
factor of $D$ carries an allowed good minimal point of the two-prime twist.  Book 154, Lemma
5.2B shows that the exact fixed-slice assertion is

$$
nb\in\{[T-P]:T\in V_{\mathrm{sp}}\}
+\mathscr R^{\mathrm{good}}_{v_0,ne-1}
\tag{6.3a'}
$$

for one exponent which is simultaneously allowed at all the other places.  This formulation
already permits arbitrary compensating good factors and their norm divisors; it is weaker than
requiring every added factor to remain in one chosen good tube.  Freezing the special factor at
$S$ gives the sufficient condition

$$
nb-c\in\mathscr R^{\mathrm{good}}_{v_0,ne-1}.
$$

If the construction uses only repetitions near $P$, let $G_{v_0}$ be the open subgroup of the
Jacobian generated by differences of points in that tube.  Since $G_{v_0}$ is open, shrink
$V_{\mathrm{sp}}$ so that $[T-S]\in G_{v_0}$ throughout it.  For sufficiently large degree,
Book 154, Step 2 identifies the degree-indexed one-tube Abel image with $G_{v_0}$.  Then
(6.3a') specializes to

$$
n([\mathcal A]-e[P])-[S-P]\in G_{v_0}
\tag{6.3a}
$$

for one common allowed $n$.  It is necessary and sufficient for that restricted one-tube
presentation.  A genuinely different repair would be a finite collection of allowed good
divisors whose classes cover $J_{v_0}(\mathbf Q_{v_0})/G_{v_0}$, as in Book 154, (5.4h); then
(6.3a') would hold for every sufficiently large $n$ and the congruences at the other places
could be imposed afterward.  Book 154, Lemma 5.2D gives another complete repair: construct the
same local slice with a smooth proper integral model and prove that the permitted good factors
contain all tubes over a nonempty special-fiber Zariski open.  Relative Riemann--Roch then makes
the degree-indexed allowed-good Abel image the whole Jacobian in every sufficiently large
degree.  Book 154, Corollary 5.2E proves that either repair, once verified on the actual slice,
would give the required common moving presentation.  No audited source verifies the
integral-slice hypotheses for the actual special packet, proves the coset-complete good-packet
statement, proves (6.3a) for the restricted route, or constructs a different evaluation
presentation.  This is the first remaining
pre-specialization moduli theorem.

The obstruction is not removed merely by taking $n$ highly divisible.  Divisibility kills
$n([\mathcal A]-e[P])$ in the finite quotient $J_{v_0}(\mathbf Q_{v_0})/G_{v_0}$, but it leaves
the fixed class $[S-P]$.  Hensel lifting only moves points inside their existing tubes;
restriction of scalars retains their residue algebras; and smoothness makes the norm--Abel
image open.  None says that the special and good tubes have the same class in that finite
quotient.  Moret--Bailly approximation starts only after a common presentation has been
constructed, so invoking it here would be circular.  Book 154, Counterexample 5.2C gives an
explicit elliptic-curve residue-disk counterexample for the whole special tube which persists
after arbitrary finite-degree good factors drawn from the chosen good tube: their norm classes
stay in the reduction kernel while every special point has nonzero reduction.  Thus the missing
assertion cannot be inferred from local realizability or high degree alone.

Changing the line bundle does not make the issue formal.  It replaces $b$ in the finite
congruence, and choosing it by prescribed local Picard classes would require a new finite weak
approximation theorem for the diagonal group of a global Jacobian.  Books 40--41 prove weak
Mordell--Weil and Mordell--Weil, not surjectivity onto these finite local quotients.  A
generalized Jacobian still maps to the ordinary Jacobian, so any relation there projects to
(6.3a').  Finally, choosing a base divisor already containing $S$ once and otherwise good is
the $n=1$ case of (6.3a'), hence is the desired construction rather than a prior input.

The elliptic-source twist does not silently provide a rational curve workaround.  Book 157,
Proposition 4.1A puts the unperturbed tensor seeds on the image of one twisted modular curve,
but Proposition 6.2A must perturb them in the full Hilbert component to avoid the prescribed
closed set $Z$.  The tensor locus may itself lie in $Z$, and no audited theorem produces a
rational or weak-approximation subvariety through all of the resulting point-centered tubes.
Book 157's good residue tubes and full-dimensional Mumford boundary chart are separate local
neighborhood results; they do not construct one smooth proper integral slice whose special
fiber has the dense allowed-good open required by Book 154, Lemma 5.2D.  Likewise, choosing a
smaller neat level does not make arbitrary extension-valued packets share one source torsion
module.  Thus the elliptic-source device aligns the arithmetic component and auxiliary level;
it does not prove the singleton moving presentation.

The nontrivial-stabilizer version of Book 155 would additionally require a special
$S_5/S_4$ evaluation presentation on the paired-frame moduli space.  Proposition 4.1 replaces
that demand.  Once Required Moving Theorem 6.3 supplies the actual cover, Proposition 4.2
forces $C\cap D=K$ for the constant field $C$ of its Galois closure.  Multiply the top cover by
the universal ordered-quintic torsor, set $J=1$, and
evaluate on the top.  Books 153 and 155 then supply closure-level disjointness and all local top
torsors.  No upward solvable-transfer problem remains.  The constant-field certificate is no
longer an independent hypothesis.

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
\text{moving-family input:}&
\text{prove Required Moving Theorem 6.3; on a fixed slice, prove (6.3a'); }\\
\text{root-field route:}&
\text{prove (6.1), the remaining one-prime clauses, and }P_{\mathrm{nm}}=\{w_0\};\\
\text{normal-top route:}&
\text{construct the actual finite-set faces and every joint hypothesis of Book 176;}\\
\text{target support:}&
\text{construct the bottom exact minimal Book 173 SP localization.}
\end{array}
\tag{6.3}
$$

The order inside either route is exact.  Lemma 6.1 closes the rational-base ray datum, Theorem
6.2 supplies the exact unramified branches, and Proposition 6.2A closes the three small-place paired
frames.  Proposition 4.2
closes the constant-field certificate once Required Moving Theorem 6.3 supplies the
presentation.  The one-prime or finite-set data are verified only after the actual bad
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
* **Use the local frame point only after extension.**  A proper extension of $\mathbf Q_2$,
  $\mathbf Q_3$, or $\mathbf Q_\ell$ cannot be a completion of any subfield of a top in which
  that rational prime
  splits completely.  Specializing over such an extension and descending automorphy to a
  separate split top would require a new solvable Galois evaluation and selected-descent datum;
  none is supplied by the ordinary Moret--Bailly field.  Theorem 6.2 changes the freely chosen
  auxiliary character by a protected anti-cyclotomic twist, and Proposition 6.2A then changes
  the local elliptic seeds and neat source and constructs points over the base completions
  directly.
* **Force the constant-field intersection after constructing the cover.**  For a fixed
  presentation, a split fiber at a prime acting nontrivially on $C$ is impossible.  Proposition
  4.2 avoids this order error: it chooses large Chebotarev primes first, obtains base points from
  Book 157, Proposition 9.3, and includes their flexible split packets in the still-unbuilt
  presentation.  This closes the constant-field issue but does not prove the unrelated
  singleton Abel condition (6.3a') at $v_0$.
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

After Theorem 6.2, Proposition 6.2A, and Required Moving Theorem 6.3 have supplied the
pre-specialization inputs, Propositions 4.1--4.2 prove the field-theoretic part.
The remaining seed theorem should therefore be stated at the post-specialization boundary and
should not demand an arbitrary prescribed group which the geometry may not realize.

**Required Theorem 7.1 (post-specialization top-clean SP occurrence).**  Let $\ell\geq7$ and
let $\bar\rho:G_{\mathbf Q}\to\operatorname{GL}_2(k)$ be the primitive signed-special Frey
residual representation of Book 164 with the image and local hypotheses required by Book 173.
Fix a finite Galois avoidance field $D$.  Assume that the pre-specialization two-prime package
of Book 178 has actually been constructed, with the rational-base corrected relative ray datum
of Lemma 6.1, the exact auxiliary branches of Theorem 6.2, the split packets
of Proposition 6.2A, its other local packets, Required Moving Theorem 6.3, and the certificate
primes of Proposition 4.2, with the induced local top packets of Proposition 4.1.  Form its
normal-top datum.

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

Propositions 4.1--4.2 and Required Theorem 7.1 immediately give a
controlled exact SP residual seed: take $F=M$ and $J=1$.  The degree is even, $2$ and $\ell$
split completely, the additional retained prime $3$ also splits completely, closure-level
avoidance gives (3.3), and (7.1) supplies the entire arithmetic
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
imports that compatibility.  Book 178, Theorem 4.2 by itself protects inertia but does not
prescribe the unramified uniformizer values needed in (6.2b); Theorem 6.2 supplies them by
Book 178, Lemma 4.3, and Proposition 6.2A constructs the three small base-completion points.
Required Moving Theorem 6.3 is therefore the first unresolved pre-specialization assertion.
Book
154's norm--Abel extension handles every packet which may be repeated wholesale, but the
one-special-factor condition leaves the degree-indexed Abel condition (6.3a'); (6.3a) is its
one-tube specialization.  Proposition 4.2 then makes the
constant-field certificate automatic.  After that presentation, the first unresolved
constant-row assertion in the actual lifting comparison is (6.1).  A localized
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
proved with all Book 173 clauses, Required Theorem 7.1 is complete.  Normal-closure geometry is
no longer an additional blocker after Required Moving Theorem 6.3.

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

That last selection is not by itself a descent theorem.  Book 109 also
assumes that the arbitrary cuspidal descent at each cyclic step has an attached arithmetic
representation and that attachment commutes with cyclic base change and finite-order twisting.
The extending representation $\rho$ compares two such attached extensions; it does not attach
the arbitrary descent in the first place.  Under the former even-degree-only carrier statement
this was an additional gap.  Proposition 7.2A below closes it using the parity-complete
one-split theorem; the admissibility and fiber-saturation checks above remain the inputs to
Book 109.

The full Book 183 interface is stronger still.  Each corrected packet must have a curve-attached
family at every coefficient embedding and, at embeddings of residue characteristic different
from two, the same algebraic dyadic SP pair must survive the raw-to-semisimple passage
uniformly.  The old parity obstruction to the **basic** carrier is removable inside the
existing trace-formula range.

**Proposition 7.2A (basic carriers for every elementary candidate).**  Let $H\leq\Gamma$ be
elementary, or let $H'$ be a subgroup occurring in a prime-cyclic refinement inside such an
$H$.  Suppose the selected candidate packet over $F_{H'}=M^{H'}$ has the local behavior proved
above: it is special at every dyadic place, spherical at the retained split places above $3$
and $\ell$, and selected at every other nonspherical place.  Then it has a compact one-split
basic quaternionic carrier, and Books 127 and 168 attach its semisimple family at every
coefficient place.  These attachments commute with the candidate cyclic base changes and
finite-order quotient twists.

**Proof.**  Every elementary group is solvable, whereas $\Gamma=G_0\times S_5$ has the
nonsolvable quotient $S_5$.  Thus $H'\ne\Gamma$ and
$d=[F_{H'}:\mathbf Q]=[\Gamma:H']\ge2$.  Complete splitting of two makes every dyadic
completion equal to $\mathbf Q_2$ and leaves the special factor and all quotient-character
corrections unchanged.  If $d$ is even, choose one dyadic special place and put
$W=\{w_2\}$.  If $d$ is odd, put $W=\varnothing$.  In both cases

$$
(d-1)+|W|\equiv0\pmod2,
$$

and the ramification set contains at least two places: for $d=2$ they are the inactive real
place and $w_2$, while for $d\ge3$ two inactive real places suffice.  The generalized compact
one-split inverse theorem of Book 104, imported through Book 127, therefore constructs the
basic quaternionic packet.  The carrier is split at every place above $3\ell$, and the packet
is spherical there, so hyperspecial level may be chosen at those places.  Book 127, Theorem
8.1 and Book 168, Theorem 12.1 attach the full semisimple coefficient family.

For a candidate cyclic base change or quotient twist, compare the two attached semisimple
representations at the density-one set of unramified places.  The automorphic Hecke identities
give respectively restriction or tensoring by the finite character.  Chebotarev and
Brauer--Nesbitt identify the representations, proving the required compatibility. $\square$

This proposition closes the former odd-degree and no-eligible-away-from-two obstruction for
rational attachment.  It does **not** turn the basic curve into a good abelian PEL carrier, and
it does not construct the raw local geometry.  In odd degree the choice $W=\varnothing$ clears
the automorphic and complete finite-splitting parts of Book 168, Proposition 7.2, but a
PEL-exact parahoric realization and component ledger still have to be constructed.  The direct
common-norm candidate cannot supply them in mixed one-split signature by Book 118, Proposition
8.2.  In even degree the only automatic
choice for the minimal packet is a dyadic singleton; that carrier is ramified at one dyadic
factor and cannot satisfy the dyadically tensor-split ledger.  A raw SP carrier therefore still
requires an eligible odd set away from two and a non-common-norm parahoric comparison, or a
different geometric construction.

The same controlled geometric theorem must cover the retained auxiliary primes.  At a
principal or tame-dihedral auxiliary place, Books 128 and 168 provide recognition theorems,
not construction theorems.  For every actual carrier they require the descended finite
nearby-cycle complex, the relevant type lines, the proof that $N=0$, the exchange maps, and
every Frobenius return map.  They also require the raw-to-global comparison at the
distinguished coefficient and, for the final all-place statement, at each retained auxiliary
coefficient.  Book 128, Lemma 3.2 now proves that comparison automatically once the displayed
zero-monodromy calculation exists.  The remaining geometric clauses are precisely the auxiliary-local part of the controlled
all-elementary attachment datum already needed before Book 183; they are not a new theorem
that may first be introduced after Brauer assembly.

**Required Theorem 7.3 (controlled auxiliary tame geometry).** For the finite list of actual
basic carriers and every retained nonspherical auxiliary place $v\nmid2\ell$, construct a fine
tame-level model which becomes strict semistable over a named finite tame extension and carries
the finite descent action, full component routing, packet projector, and selected local type
projector on its equivariant nearby-cycle complex. Prove that wild inertia acts trivially on
the selected rank-two packet part, and on that part prove:

1. in the principal row, the two lines carry the prescribed tame inertia characters, with an
   ordered Frobenius-stable splitting when those characters coincide;
2. in the dihedral row, the prescribed quadratic cover and the two distinct lines carrying
   $\theta$ and $\theta^\sigma$ occur, and the nontrivial descent element exchanges them;
3. the restriction--Gysin operator is zero; and
4. every normalized Frobenius-orbit return map is the value prescribed by the selected
   automorphic character.

The construction and all four identities must be algebraic over one packet field, compatible
with the candidate cyclic base changes and quotient twists, and stable under scalar extension
to the distinguished coefficient, the selected coefficient above three, and every retained
coefficient place whenever its residue characteristic differs from that of $v$. Book 128,
Theorems 7.1 and 8.1 and
Lemma 3.2 then identify the same principal or dihedral pair on the globally semisimplified
attachment at all those coefficient places.

The first unresolved clause is the fine tame-level model with its equivariant extension of the
packet and type projectors. Book 122 constructs the signed descent formalism after such a model
exists, while Books 128 and 168 reconstruct the parameter after its lines, zero monodromy, and
return maps have been computed; none constructs this model for the actual retained carrier.
Thus Required Theorem 7.3 is controlled attachment geometry, not an AUX theorem created after
Book 185 and not a consequence of integral Brauer cancellation.

Finally, once an actual raw carrier is supplied, the uniform preservation problem has no further
packet-theoretic reduction hidden inside it.  Book 128, Proposition 9.4 and Book 168,
Proposition 7.6 prove that $(\mathrm{SS}_{\mathrm{array}})$ makes every raw multiplicity
representation globally semisimple after every displayed coefficient embedding.  Hence the
global semisimplification is the raw representation itself, and restriction preserves the
entire signed special Weil--Deligne pair, including nonzero $N$. At the zero-monodromy auxiliary
rows this global input is unnecessary by Book 128, Lemma 3.2. The sufficient universal input for
the SP row is rational Tate-module
semisimplicity $(\mathrm{TS})$ for the Jacobians of the actual carriers.  Book 179 invokes that
theorem for abelian-variety examples but does not prove it or include a prior source for it;
the present source chain therefore does not close this arithmetic input.  At coefficient
characteristic two, global semisimplicity still follows from the same input, but the
prime-to-coefficient local comparison does not produce a dyadic Weil--Deligne pair.

Consequently the exact later bridge theorem is now a **controlled raw-carrier,
auxiliary-local-geometry, and ambient-semisimplicity theorem**.  Basic all-coefficient
attachment and its cyclic compatibility are supplied by Proposition 7.2A.  The missing theorem
must construct the raw dyadic SP carriers in the cases just isolated; construct, at every
retained principal or dihedral auxiliary prime, the actual descent/type/return-map data and
the zero-monodromy calculation required by Books 128 and 168; and supply
$(\mathrm{SS}_{\mathrm{array}})$, or directly the weaker interface-level conclusion that all
raw packet multiplicity spaces are globally semisimple.  The last clause proves
raw-to-semisimple preservation for the nonzero-monodromy SP pair at every coefficient embedding
of residue characteristic different from two; it is not needed for the zero-monodromy AUX rows
and is not supplied by abstract Brauer descent.  This theorem must not be
bundled into Required Theorem 7.1 or used to obscure the earlier failure to construct the
minimal residual seed itself.  It must also be strictly prior to Book 183: the elementary
packet array, its effectivity, and the descended compatible system cannot be used backward to
prove the local geometry or ambient semisimplicity hypotheses which that array consumes.

## 8. Dependency, circularity, and downstream audit

### 8.1 What each prior book really supplies

| Source | Legitimate use here | What it does not supply |
|---|---|---|
| Book 6 | the exact Grunwald--Wang alternative, including preservation of prescribed local characters after the possible exponent doubling | the protected anti-cyclotomic construction or its determinant calculation |
| Book 44 | the Tate-curve torsion sequence and Kummer extension class | a simultaneous paired-frame point on the Hilbert--Blumenthal twist |
| Book 109 | prime-cyclic ascent on an exhibited extension-complete selected chain, and descent on exhibited antecedent-complete selected chains with the required fiber saturation and attached arithmetic representations | attachment of candidate cyclic descents, or either direction from solvability alone |
| Books 127--128 and 168 | parity-complete basic one-split attachment in degree at least two; the SP and tame local recognition criteria; automatic zero-monodromy raw-to-global passage; reduction of uniform nonzero-monodromy preservation to $(\mathrm{SS}_{\mathrm{array}})$ for the actual carriers | the non-common-norm PEL-exact parahoric comparison needed for any raw SP carrier, the additional away-from-two ramification set in the even-degree minimal case, construction of auxiliary descent/type/return maps, the ambient semisimplicity input needed for SP, or a comparison at the coefficient residue characteristic |
| Book 164 | the primitive residual Frey SP tuple, intrinsic line, sign, and conductor-one record used in the FLT specialization | a characteristic-zero chosen lift or automorphic seed |
| Book 173 | exact minimal $R=\mathbb T$ and automorphy of every point of a clean minimal deformation problem | existence of the exact residual automorphic localization |
| Book 175 | a local change at a previously named place under its exact clean augmentation hypotheses | simultaneous lowering at the unknown extra bad primes of a specialization |
| Book 176 | a conditional finite-set reduced comparison and pointwise modularity from one supplied global cube and all its joint hypotheses | the face classes, cube, mixed exactness, product residue, joint support, augmentation, or reciprocity for an actual specialization |
| Book 177 | a conditional two-prime potential-modularity route and point-field control in its admitted range | an unconditional clean seed or controlled normal closure |
| Book 142 | Chebotarev classes at arbitrarily large primes | base-field points on the twist or a moving presentation containing their split packets |
| Book 153 | simultaneous connected specialization for the integral top cover and its avoidance-field base change | the local seed, singleton moving presentation, or any automorphic support |
| Book 154 | construction of a simultaneous moving presentation for flexible split packets and for exact packets repeatable wholesale; the exact allowed-good criterion and coset-complete or integral-open sufficient repairs | one repair hypothesis or (6.3a') for Book 178's actual one-special packet, or post-specialization automorphic support |
| Book 155 | equivariant local constancy and the regular ordered-quintic torsor | the singleton moving presentation or any automorphic lifting and lowering on the specialized top |
| Book 157 | elliptic-source rigidification, one global neat source matching finitely many local seeds, large-good-place base points, point-centered opens, and persistence after permitted extension | descent of an arbitrary preassigned coefficient-prime or semistable frame point; Theorem 6.2 and Proposition 6.2A instead alter the freely chosen auxiliary character, local elliptic seeds, and neat source |
| Book 178 | conditional residual potential modularity for a fixed seven-item two-prime-admissible witness; after lifting, proof of final compact-carrier eligibility; its inverse-branch lemma, completed over $\mathbf Q$ by Lemma 6.1 here; and the protected anti-cyclotomic Grunwald correction imposing exact split residual branch values | over a general base, the capitulation part of the corrected relative ray datum; a specialization satisfying item 7's literal singleton condition; or the exact minimal Book 173 SP seed |
| Book 180 | integral Brauer and Clifford identities for supplied representations, characters, and packet data | construction or attachment of any elementary fixed-field packet, a raw SP carrier, or the ambient semisimplicity theorem needed before the all-embedding SP comparison |
| Books 165--167 | the SP local deformation problem, supported cohomology, and balanced presentation | a horizontal point or a nonzero exact automorphic module |
| Book 181 | under $(\mathrm{Seed}_{\mathrm{SP}}^{181})$, finite-flatness of the balanced global SP ring and the normalized primitive SP point used here | construction of its seed, normal-closure control, or the controlled seed required in Section 4 |

Book 181 now genuinely supplies the chosen point conditional on its exact seed; this volume no
longer treats that point as a free-standing assumption.  Proposition 3.2 also extracts its
automorphy over Book 181's seed field.  The controlled seed remains stronger and unproved.

### 8.2 Direct dependency recommendation

For the conditional theorem actually proved here, the honest direct dependency row is

$$
\boxed{
182\mid 6,44,109,127,128,142,153,154,155,157,164,165,168,173,176,178,181.}
\tag{8.1}
$$

Book 175 is a transitive input through Book 178.  Books 177, 179, and 180 are comparative
background for the seed and downstream bridge audits.  Book 179 names $(\mathrm{TS})$ as an
external input but does not prove it; Book 180's abstract machinery is consumed by Book 183
only after the packets exist.  None is used in the conditional proof, so none is a direct edge
here.  Books 166--167 are direct inputs to Book 181, but transitive for this volume.
Book 165 is retained because this volume directly identifies the represented local SP problem;
it could be made transitive by treating all local identifications as part of the Book 181
export.

Equation (8.1) does not make the result unconditional.  To mark Book 182 **READY**, a new
strictly prior result must prove Required Moving Theorem 6.3 and Required Theorem 7.1; a prior
controlled raw-carrier, auxiliary-local-geometry, and ambient-semisimplicity theorem of Section
7.3 is also required.  Those results belong in their natural
prior owners; no book number may be put in a slot merely because it states the conclusion
conditionally.

### 8.3 Proof-order audit

The acyclic order is

$$
\begin{array}{c}
\text{primitive residual SP datum}
\\ \Downarrow \\
\text{Lemma 6.1; Theorem 6.2; Proposition 6.2A;}\\
\text{Book 154 Lemma 5.2A; Required Moving Theorem 6.3; Proposition 4.2}
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
\text{Proposition 7.2A: basic all-coefficient attachment and cyclic compatibility}
\\ \Downarrow \\
\text{Book 109: distinguished-coefficient elementary descents selected by }\rho
\\ \Downarrow \\
\text{raw SP/AUX carriers, return maps, and }(\mathrm{SS}_{\mathrm{array}})
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
over Book 181's uncontrolled seed field.  Proposition 4.1 proves the field-theoretic
refinement once Required Moving Theorem 6.3 supplies the actual mixed local moving cover;
Proposition 4.2 then forces its Galois-closure constant field to satisfy
$C\cap D=\mathbf Q$.  Multiplying that closure by an independent ordered-quintic torsor and
specializing the top together with its $D$-base change then gives an even-degree totally real
normal top with $F=M$, $J=1$, split sensitive places, and closure-level avoidance.
Consequently no moduli-specific $S_5/S_4$ presentation and no upward solvable base change
remain after that input.  Book 154 constructs flexible split and wholesale-repeatable exact
packets, but it does not prove the allowed-good Abel condition (6.3a'), coset completeness, the
integral-open slice hypothesis, or the restricted fixed-offset congruence (6.3a) for the actual
singleton special packet.

Over a general base Book 178 still correctly retains full relative-ray compatibility.  For the
rational Frey application, Lemma 6.1 imports that compatibility from its inverse-branch
correction and the determinant-compatible local choices.  Book 178, Theorem 4.2 alone does not
prescribe the unramified uniformizer values of the auxiliary residual character, but its Lemma
4.3 supplies the protected anti-cyclotomic Grunwald correction.  Theorem 6.2 consequently
constructs the exact branches, and Proposition 6.2A constructs simultaneous paired-frame seeds
over $\mathbf Q_2$, $\mathbf Q_3$, and $\mathbf Q_\ell$ themselves without local extension or potential
modularity.  Proposition 4.2 closes constant-field avoidance.  Required Moving Theorem 6.3 is
the first remaining pre-specialization assertion; its precise form in the existing curve--pencil
construction is the full singleton Abel condition (6.3a'), with (6.3a) only for a one-tube
good packet and Book 154's two geometric saturation criteria as sufficient repairs.  The
localized abelian Ihara family (6.1) is then the first missing
constant row in the lifting comparison, and it does not imply the other faces or the bottom
carrier.  After those earlier inputs, Required Theorem 7.1 is the exact remaining seed theorem:
among the normal-top specializations, construct one whose target eigensystem reaches a nonzero
bottom minimal SP localization satisfying every clean hypothesis of Book 173.  The irreducible
post-specialization obstruction is that clean bottom minimal-SP occurrence itself; Book 176
consumes such face data and does not construct it.

After that seed exists, Books 181 and 173 make the chosen lift automorphic directly over $M$.
Section 7.3 reduces the local and group-theoretic descent checks using the extension of $\rho$
and the split minimal local support.  Proposition 7.2A supplies the basic carrier and
distinguished/all-coefficient attachment for every candidate cyclic descent, including the
odd-degree elementary fields, and proves cyclic base-change and twist compatibility.  The
remaining later bridge blocker is therefore the controlled raw-carrier,
auxiliary-local-geometry, and ambient-semisimplicity theorem: current sources do not construct
the non-common-norm PEL-exact parahoric comparison needed for the raw SP carrier (and in the
even-degree minimal case also lack an eligible ramification set away from two), do not construct
the actual principal/dihedral descent complexes, type lines, exchange and Frobenius return maps
at every retained auxiliary prime, and do not prove $(\mathrm{SS}_{\mathrm{array}})$ for the
actual carrier Jacobians.  Books 128 and 168 recognize the auxiliary parameters from those
data; Book 128, Lemma 3.2 proves their zero-monodromy raw-to-global passage without the last
input. Ambient semisimplicity remains needed to preserve the nonzero-monodromy SP pair at each
allowed coefficient embedding. This controlled local-geometry clause is part of the attachment theorem already
needed before Book 183, not a new topic after assembly.  It is separate from Required Theorem
7.1 and from the normal-closure construction.

Accordingly,

$$
\boxed{\text{NOT READY}.}
$$
