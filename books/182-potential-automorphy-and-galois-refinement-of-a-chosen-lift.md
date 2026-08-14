# Potential Automorphy and Galois Refinement of a Chosen Lift

## Contents

1. [The problem after the chosen lift exists](#1-the-problem-after-the-chosen-lift-exists)
   - [The output inherited from Book 181](#11-the-output-inherited-from-book-181)
   - [Automorphy over the original seed field](#12-automorphy-over-the-original-seed-field)
   - [The new question](#13-the-new-question)
2. [The signed-special local record](#2-the-signed-special-local-record)
   - [Primitive monodromy, line, and sign](#21-primitive-monodromy-line-and-sign)
   - [Local invariants](#22-local-invariants)
   - [Restriction through completely split places](#23-restriction-through-completely-split-places)
3. [Controlled Galois refinement data](#3-controlled-galois-refinement-data)
   - [The field diagram](#31-the-field-diagram)
   - [The exact automorphic datum at the point field](#32-the-exact-automorphic-datum-at-the-point-field)
   - [Ascent admissibility](#33-ascent-admissibility)
   - [Residual image on the fixed-field diagram](#34-residual-image-on-the-fixed-field-diagram)
4. [The earlier seed boundary](#4-the-earlier-seed-boundary)
   - [What is assumed and what is not reconstructed here](#41-what-is-assumed-and-what-is-not-reconstructed-here)
   - [Split local data and the coefficient-prime correction](#42-split-local-data-and-the-coefficient-prime-correction)
   - [Auxiliary active sets and target paths](#43-auxiliary-active-sets-and-target-paths)
   - [Branch corrections and bottom occurrence](#44-branch-corrections-and-bottom-occurrence)
   - [The direct definite split-top boundary](#45-the-direct-definite-split-top-boundary)
5. [Potential automorphy of the chosen lift](#5-potential-automorphy-of-the-chosen-lift)
   - [Automorphy at the point field](#51-automorphy-at-the-point-field)
   - [Passage to the Galois top](#52-passage-to-the-galois-top)
   - [The direct-top case](#53-the-direct-top-case)
6. [Elementary fixed fields and basic carriers](#6-elementary-fixed-fields-and-basic-carriers)
   - [Descent candidates](#61-descent-candidates)
   - [Parity-complete compact carriers](#62-parity-complete-compact-carriers)
   - [Compatibility of attachment](#63-compatibility-of-attachment)
7. [Raw signed-special carriers and semisimplicity](#7-raw-signed-special-carriers-and-semisimplicity)
   - [Raw multiplicity spaces](#71-raw-multiplicity-spaces)
   - [Why nonzero monodromy is different](#72-why-nonzero-monodromy-is-different)
   - [The exact raw-carrier boundary](#73-the-exact-raw-carrier-boundary)
8. [Auxiliary Galois comparisons](#8-auxiliary-galois-comparisons)
   - [The distinguished unramified anchor](#81-the-distinguished-unramified-anchor)
   - [Twisting, induction, and clean support](#82-twisting-induction-and-clean-support)
   - [Why automorphic type is a stronger question](#83-why-automorphic-type-is-a-stronger-question)
9. [The controlled-top theorem and conclusion](#9-the-controlled-top-theorem-and-conclusion)

## 1. The problem after the chosen lift exists

### 1.1 The output inherited from Book 181

Let $\ell\geq 7$, let $E/\mathbf Q_\ell$ be finite, and write
$(\mathcal O,(\varpi),k)$ for its integer ring, maximal ideal, and residue field. We use
covariant representations and arithmetic Frobenius.

Book 181 begins with a residual representation

$$
\bar\rho:G_{\mathbf Q}\longrightarrow \operatorname{GL}_2(k)
\tag{1.1}
$$

having the primitive signed-special, or **SP**, local condition at $2$, the selected coefficient-linear
finite-flat condition at $\ell$, cyclotomic determinant, and the required irreducibility. Its
balanced presentation does not by itself produce a characteristic-zero point. Under the
explicit hypothesis $(\mathrm{Seed}_{\mathrm{SP}}^{181})$, Book 181 first applies the minimal
comparison theorem over a totally real seed field, then proves finite scalar image, descends
the traces, proves that the whole global ring is finite flat, and finally chooses a horizontal
point.

Fix one such point. After the finite coefficient extension made in Book 181, it is a continuous
representation

$$
\rho:G_{\mathbf Q}\longrightarrow \operatorname{GL}_2(\mathcal O)
\tag{1.2}
$$

with

$$
\det\rho=\chi_\ell,
\qquad
\rho\text{ unramified outside }\{2,\ell\},
\tag{1.3}
$$

$$
\bar\rho\text{ absolutely irreducible and odd},
\qquad
\bar\rho|_{G_{\mathbf Q(\zeta_\ell)}}\text{ absolutely irreducible}.
\tag{1.4}
$$

Its stable lattice is coefficient-linearly finite flat of weights $\{0,1\}$ at $\ell$. At
$2$ it carries the primitive signed-special record developed in Chapter 2.

The hypothesis of Book 181 remains a hypothesis. The existence of the chosen point does not
turn that hypothesis into a theorem, and the point may not be used backward to construct the
residual automorphic localization from which Book 181 began. This volume starts after the
point has been obtained and asks what controlled potential automorphy can be deduced for this
particular point.

### 1.2 Automorphy over the original seed field

The seed hypothesis in Book 181 contains an even-degree totally real field $F_0$ over which
the restricted signed-special deformation problem satisfies the exact hypotheses of Book 173.
The chosen point is already automorphic after restriction to that field.

**Proposition 1.1 (the original potential-automorphy field).** After one finite coefficient
extension, there is a parallel-weight-two cuspidal representation $\pi_{F_0}$ such that

$$
r_{\pi_{F_0},\lambda_0}\simeq \rho|_{G_{F_0}}
\tag{1.5}
$$

as integral representations. The isomorphism retains the selected finite-flat lattice at
places above $\ell$ and the complete signed-special record at places above $2$.

**Proof.** Book 181 constructs $\rho$ as a point of its represented global signed-special
problem. Its restriction to $G_{F_0}$ is therefore a point of the exact restricted problem
appearing in $(\mathrm{Seed}_{\mathrm{SP}}^{181})$. Book 173 identifies that restricted
deformation ring with its faithful minimal Hecke algebra and makes every characteristic-zero
point automorphic with a matching stable lattice. Evaluating at the restricted point gives
(1.5). Complete splitting at $2$ and $\ell$, which is part of the seed, preserves the local
lattices literally. $\square$

This proposition is stronger than residual potential automorphy: it identifies the chosen
characteristic-zero point. It is weaker than the controlled theorem needed later. The seed
field $F_0$ need not have a suitable normal closure, and Book 181 supplies neither a selected
solvable ascent from $F_0$ nor a finite descent ledger for the elementary fixed fields of a
Galois top.

### 1.3 The new question

The single question of this volume is therefore:

> Under which exact additional hypotheses can the chosen representation $\rho$ be made
> automorphic over a controlled totally real Galois extension $M/\mathbf Q$, and which
> Galois-theoretic certificates can then be supplied for the later finite family of elementary
> fixed fields?

Three assertions must be kept separate:

1. $\bar\rho|_{G_F}$ occurs in some automorphic representation;
2. the exact represented signed-special problem over $F$ has a clean minimal automorphic
   realization;
3. the particular point $\rho|_{G_F}$ is automorphic.

Book 173 proves the passage from the second assertion to the third. It does not prove the
passage from the first to the second. Likewise, solvability of a field extension provides a
group-theoretic cyclic series but not the packet selectors and local comparisons required to
move automorphy along that series.

The main result of Chapter 5 is consequently conditional on a controlled refinement datum.
Chapters 6--8 then separate three later issues: existence of basic compact carriers, existence
of raw signed-special carriers, and passage from a raw carrier to its globally semisimplified
packet representation. The first and third are already formal in the selected array: Book 104
gives a parity-complete compact carrier, and Book 168 reduces the third uniformly to
$(\mathrm{HT}_1)$. The genuinely new carrier input is the second, geometric one. Auxiliary
unramified comparisons require still less and are proved independently in Chapter 8.

## 2. The signed-special local record

### 2.1 Primitive monodromy, line, and sign

Choose an $\ell$-primary tame character

$$
t_\ell:I_2\twoheadrightarrow \mathbf Z_\ell
$$

and arithmetic Frobenius $\phi_2$ satisfying

$$
t_\ell(\phi_2\sigma\phi_2^{-1})=2t_\ell(\sigma).
\tag{2.1}
$$

On the chosen lattice, wild inertia is trivial and

$$
\rho(\sigma)=1+t_\ell(\sigma)N,
\qquad
N^2=0,
\qquad
\bar N:=N\bmod\varpi\ne0
\tag{2.2}
$$

for $\sigma\in I_2$. If $F_2=\rho(\phi_2)$, then

$$
F_2NF_2^{-1}=2N.
\tag{2.3}
$$

The condition $\bar N\ne0$ is a statement about the integral lattice. It is stronger than
$N\ne0$ after inverting $\varpi$: it says that the monodromy extension class is primitive and
has not acquired an invisible factor of $\varpi$.

Put

$$
\mathscr L=\ker N=\operatorname{im}N.
\tag{2.4}
$$

The equality in (2.4) will follow from the rank calculation below. The chosen sign
$\varepsilon_2\in\{1,-1\}$ is determined by the Frobenius-semisimplified action. In a basis
with $N=e_{12}$,

$$
F_2^{\mathrm{ss}}=
\begin{pmatrix}
2\varepsilon_2&0\\
0&\varepsilon_2
\end{pmatrix}.
\tag{2.5}
$$

Thus Frobenius acts on $\mathscr L$ by $2\varepsilon_2$ and on the quotient by
$\varepsilon_2$. The local datum is the full tuple

$$
(N,\mathscr L,\varepsilon_2,F_2NF_2^{-1}=2N),
\tag{2.6}
$$

not merely its conductor exponent.

### 2.2 Local invariants

**Lemma 2.1 (primitive signed-special invariants).** The rational Weil--Deligne
representation of $\rho|_{G_{\mathbf Q_2}}$ has nonzero rank-one monodromy. Its unique
inertia-invariant line is $\mathscr L$, its sign is $\varepsilon_2$, and its Artin conductor
exponent is one.

**Proof.** Since $\bar N\ne0$, the endomorphism $N$ is nonzero. A nonzero square-zero
endomorphism of a two-dimensional characteristic-zero vector space has rank one. Its kernel
and image are therefore one-dimensional, and $N^2=0$ gives
$\operatorname{im}N\subseteq\ker N$, proving (2.4).

The image of $t_\ell$ is dense in $\mathbf Z_\ell$. A vector fixed by inertia is consequently
killed by $N$, so the invariant subspace is exactly $\mathscr L$. Wild inertia is trivial,
and the tame conductor is

$$
2-\dim\mathscr L=1.
$$

Equation (2.3) makes the line Frobenius-stable, and (2.5) gives its named sign. Neither the
line nor the sign can be recovered from the conductor alone. $\square$

### 2.3 Restriction through completely split places

**Lemma 2.2 (literal preservation at a split place).** Let $K/\mathbf Q$ be a number field in
which $2$ splits completely. At every $w\mid2$, restriction of the chosen lattice to
$G_{K_w}$ preserves (2.2)--(2.6), including primitivity, the intrinsic line, the sign, and
conductor exponent one.

**Proof.** Complete splitting gives $K_w=\mathbf Q_2$. With compatible decomposition groups,
restriction is the identity on the local representation and its lattice. $\square$

Complete splitting is a convenient integral condition, not a cosmetic one. Under a ramified
extension, the tame parameter is multiplied by the ramification index. If that index is
divisible by $\ell$, the reduction of the new monodromy operator may vanish even though its
rational value does not. This is why a rational nonzero-monodromy statement cannot replace
the primitive lattice condition.

The same literal argument applies to the selected coefficient-prime lattice when $\ell$
splits completely. If $M/\mathbf Q$ is Galois and $2$ and $\ell$ split completely in $M$,
then they split completely in every intermediate field.

## 3. Controlled Galois refinement data

### 3.1 The field diagram

Fix a finite Galois avoidance field $D/\mathbf Q$. It contains the full matrix cutout field of
$\bar\rho$, the joint residual--cyclotomic cutout, and the finite adjoint, self-twist,
orientation, component, and coefficient fields which must remain independent of the chosen
specialization.

A **controlled field diagram** consists of

$$
M/\mathbf Q\text{ finite totally real Galois},
\qquad
\Gamma=\operatorname{Gal}(M/\mathbf Q),
\qquad
J\leq\Gamma,
\qquad
F=M^J,
\tag{3.1}
$$

with the following properties:

1. $J$ is solvable and core-free in $\Gamma$;
2. $[F:\mathbf Q]$ is even;
3. $2$, $3$, $\ell$, and every other sensitive rational place named in advance split
   completely in $M$;
4. $M\cap D=\mathbf Q$;
5. the prescribed real and finite completion conditions hold on the entire fixed-field
   diagram.

Core-freeness says that $M$ is the normal closure of $F$. It is useful for indexing the later
fixed fields, but it does not imply that automorphy ascends from $F$ to $M$. The latter is an
arithmetic assertion recorded separately in Section 3.3.

The direct-top case $J=1$ is especially clean: then $F=M$, and no upward transfer is needed.
Nothing in the definition asserts that such a diagram exists with the automorphic data of the
next section.

### 3.2 The exact automorphic datum at the point field

Let $\mathcal D_F^{\mathrm{SP}}$ be the fixed-cyclotomic-determinant deformation problem whose
local conditions are:

- the schematic closure of the named minimal-special component, with its intrinsic line, sign,
  and monodromy relation, at every place above $2$;
- the restriction of the selected coefficient-linear finite-flat lattice condition at every
  place above $\ell$;
- the unramified condition at every other finite place.

An **exact signed-special automorphic datum over $F$** means that every hypothesis of Book 173
has been verified for this represented problem. In particular, it includes a nonzero
non-Eisenstein localization in the exact definite-quaternionic module, the required
finite-freeness and stabilizer control, saturated type and degeneracy maps, the perfect
primary--companion pairing, exact augmentation, generically reduced faithful Hecke orders, and
branchwise integral Galois attachment with the stated local compatibility.

This terminology is deliberately stronger than residual automorphy. An automorphic residual
representation at a larger level, with an auxiliary special prime or an unverified type
lattice, does not define the minimal comparison map required by Book 173. Nor does the phrase
“clean datum” prove any item in the preceding list.

The controlled field diagram together with this exact datum will be called a **controlled
residual seed**. In the present volume it is an input to the chosen-lift argument, not an
output.

### 3.3 Ascent admissibility

Choose a prime-cyclic series

$$
F=K_0\subset K_1\subset\cdots\subset K_s=M.
\tag{3.2}
$$

Solvability of $J$ guarantees the existence of an abstract series of this form. A
**selected ascent ledger** requires more. At every step:

1. the cuspidal source packet is selected and trace-comparable;
2. every finite local component and restricted parameter remains in the proved cyclic
   transfer range;
3. every nonsplit place carries the full selected fixed-determinant extension fiber;
4. the archimedean component remains in the cohomological range;
5. a comparison tensor has the required strongly cuspidal factor;
6. attachment at the distinguished coefficient commutes with base change.

These conditions are exactly what allows Book 109 to move a particular packet along (3.2).
They are not consequences of the group $J$ being solvable. In the direct-top case the list is
empty.

A controlled residual seed plus a selected ascent ledger is the **controlled chosen-lift
refinement datum** used in Chapter 5.

### 3.4 Residual image on the fixed-field diagram

**Lemma 3.1 (closure-level disjointness).** If $M\cap D=\mathbf Q$, then for every
intermediate field $K\subseteq M$,

$$
\bar\rho(G_K)=\bar\rho(G_{\mathbf Q}),
\qquad
\bar\rho(G_{K(\zeta_\ell)})
=\bar\rho(G_{\mathbf Q(\zeta_\ell)}).
\tag{3.3}
$$

**Proof.** Let $D_\rho\subseteq D$ be the full matrix cutout field. Since
$K\cap D_\rho=\mathbf Q$, restriction identifies

$$
\operatorname{Gal}(KD_\rho/K)
\simeq \operatorname{Gal}(D_\rho/\mathbf Q),
$$

which proves the first equality. Apply the same argument to the joint
residual--cyclotomic cutout contained in $D$ to obtain the second. $\square$

Thus the absolute and cyclotomic absolute irreducibility hypotheses required by Book 173
survive throughout the diagram. Disjointness from a projective cutout alone would not prove
(3.3).

## 4. The earlier seed boundary

### 4.1 What is assumed and what is not reconstructed here

The controlled residual seed precedes the finite-image argument logically: it is the
arithmetic input from which Book 181 can construct a chosen lift. No preceding volume
presently proves its existence for the Frey signed-special datum with all of the required
localizations and integral comparisons. Accordingly, this volume never treats that seed as an
unconditional conclusion.

The seed is recorded here only to delimit the hypothesis of the post-181 theorem. On the
preferred split route its proposed construction has four distinct layers:

1. Book 158's simultaneous point-centered opens and split Galois-top specialization;
2. an auxiliary-$q$ finite-set lifting problem on the actual post-specialization active set;
3. a target-coefficient lowering path to the signed-special minimal problem;
4. the structural minimal ledger required by Book 173.

Collapsing these layers into “residual potential modularity” loses essential information. The
rest of this chapter states the boundary precisely, without making it part of the chosen-lift
argument.

### 4.2 Split local data and the coefficient-prime correction

Book 158 puts every sheet above a controlled place into one point-centered open and specializes
a regular symmetric Galois top with that place split completely. For the Frey Tate open at $2$,
every dyadic place is special for $V_{\mathfrak q}(A)$ and therefore belongs to
$P_{\mathrm{aux}}(A)$. This is the geometric handoff used by the FLT route.

No later step requires a unique exceptional sheet. The retired singleton moving construction
and Book 157's conditional toroidal joining chain are not part of the seed boundary. Book 157
is used here only for the reusable coefficient-prime ordinary seed below.


There is a separate coefficient-prime correction when the Frey curve is multiplicative at
$\ell$. A Tate seed can realize the selected finite-flat residual $\ell$-torsion while its full
$\ell$-adic Tate module has nonzero semistable monodromy. It is therefore not a
characteristic-zero point of the finite-flat deformation condition. The selected residual
model has a multiplicative connected line and an étale quotient, so a good replacement must
be ordinary, not local--local. Book 157 constructs the required one-prime ordinary seed over
$\mathbf Q_\ell$; only after that seed is fixed may the auxiliary prime $q$ and its unramified
branch at $\ell$ be reselected. This produces the corrected two-frame finite-flat point.

Write the arithmetic-Frobenius polynomial of this fixed good ordinary seed as

$$
P_\ell(X)=X^2-a_\ell(\mathcal B_\ell)X+\ell,
\qquad
\Delta_\ell=a_\ell(\mathcal B_\ell)^2-4\ell.                 \tag{4.1a}
$$

The selection of $q$ includes $q\nmid\Delta_\ell$. Hence the two roots of $P_\ell$ are
distinct modulo $q$ and may be ordered before the protected dihedral branch correction is
made. If a fixed good seed at another place, such as $3$, participates in the same paired
frame, the corresponding discriminant is excluded at the same stage. This is a finite
Chebotarev exclusion because the good seeds are fixed first.

The order is load-bearing:

$$
\text{ordinary one-prime seed}
\Longrightarrow
\text{choice of }q\text{ and corrected branch}
\Longrightarrow
\text{paired finite-flat point}
\Longrightarrow
\text{Book 158 split local open}.
\tag{4.2}
$$

A frozen multiplicative auxiliary branch can be incompatible with every good replacement by
the Weil bound. Thus the corrected point cannot be obtained by merely relabelling the original
Tate seed.

### 4.3 Auxiliary active sets and target paths

After specialization, let $A$ be the auxiliary abelian variety and let
$V_{\mathfrak q}(A)$ be its auxiliary-$q$ representation. Two finite sets of places occur,
and they have different meanings.

| Ledger | Definition | Forced examples | Purpose |
|---|---|---|---|
| $P_{\mathrm{aux}}(A)$ | places where the auxiliary-$q$ characteristic-zero representation has more level than its residual lifting problem | every dyadic place in the Frey-adapted Tate construction, the full conjugate distinguished set $W_0(M)$, some places above $3$, and accidental semistable places | make $V_{\mathfrak q}(A)$ automorphic |
| $P_{\mathrm{tar}}$ | places where the resulting target-coefficient packet has more level than $\mathcal D_M^{\mathrm{SP}}$ | $W_0(M)$ and any retained multiplicative place above $3$ | lower the target packet to the exact signed-special minimal problem |

The dyadic places lie in $P_{\mathrm{aux}}(A)$ because the auxiliary residual branch is
unramified there while the Tate seed has nonzero characteristic-zero monodromy. They do not lie
in $P_{\mathrm{tar}}$, because the target problem retains its signed-special condition at
$2$. A multiplicative place above $3$ may lie in both sets. An unrepaired multiplicative place
above $\ell$ is not a target edge at all: it violates the coefficient-prime finite-flat
condition and stops the target path before lowering begins.

The retired one-active-place route is impossible already before accidental bad places are
counted, because every dyadic place lies in $P_{\mathrm{aux}}(A)$. The preferred auxiliary
step is Book 176's direct $({\rm IAV}_{P_{\mathrm{aux}}(A)})$ comparison; its stronger ordered,
all-point, or pointed alternatives may be used only with their full stated hypotheses. Only
after that step has produced an automorphic target packet does one form $P_{\mathrm{tar}}$ and
begin the second path.

### 4.4 Branch corrections and bottom occurrence

At each target edge $x\in P_{\mathrm{tar}}$, the one-step lowering theorem requires more than
a numerical conductor congruence or a saturated old map. Its hypotheses include localized
abelian Ihara, residual duality, vanishing of the full residual monodromy operator, the
component obstruction, the exact two-branch normalization term, and the branch-Smith
correction.

The component obstruction and the branch-Smith correction are independent. A model may have a
clean component group while the bottom branch inclusion still has cokernel
$\mathcal O/(\varpi)$. In that case monodromy vanishes modulo $\varpi$ without producing a
lower class. Conversely, a clean branch inclusion does not remove torsion from the component
map. Both conditions must be checked on the current edge, with all previously lowered places
retained as spectators.

Bottom occurrence is different again. Suppose an actual upper packet is placed on a compact
carrier split at every target place, its integral packet lattice is primitive, and the target
places are ordered so that every current lower block is exactly the next current new block.
If every one-step hypothesis just listed is verified, nonvanishing propagates inductively down
the path. The final rational packet can then be transferred to the totally definite carrier,
where a primitive saturated packet lattice gives nonzero residual occurrence. Thus bottom
occurrence need not be assumed separately from a genuinely certified path.

The bottom **structural** ledger is nevertheless still an input. Finite freeness, type
saturation, pairings, augmentation, faithful Hecke orders, and integral Galois attachment do
not follow merely from nonzero occurrence. No preceding theorem constructs the entire
auxiliary-active finite-set certificate, target path, branch corrections, and bottom-structural
package for the Frey datum. This is the exact conditional boundary inherited by the present
volume; it contains no singleton moving presentation.

### 4.5 The direct definite split-top boundary

The preferred split-top route permits a sharper audit than an ordered curve-lowering path.
Assume Book 178's split specialization and its direct
$({\rm IAV}_{P_{\rm aux}(A)})$ certificate. Its finite-set transfer makes the auxiliary Tate
module automorphic, and the cross-prime comparison gives a parallel-weight-two upper target
packet $\Pi^{\rm up}/F$ with residual representation $\bar\rho|_{G_F}$. The upper localization
is nonzero.

Because $F$ has positive even degree, there is a quaternion algebra $B^{\rm def}/F$ ramified
at every real place and at no finite place. The weight-two archimedean packet is discrete
series, so global Jacquet--Langlands transfers $\Pi^{\rm up}$ to $B^{\rm def,\times}$. Choose
neat finite level containing its finite vector. The resulting definite class-set module is
finite free. Scale a simultaneous eigenvector to be primitive; its reduction is nonzero and is
localized at the residual maximal ideal of $\bar\rho|_{G_F}$. Thus:

**Proposition 4.1 (direct upper definite occurrence).** Conditional on the preferred split
Book 178 handoff, the upper target residual system occurs nontrivially on a totally definite
quaternionic module. This construction uses rational packet transfer followed by a fresh
primitive definite lattice. It uses no integral comparison with the compact curve carrier,
no node uniformization, and no constant-row abelian-Ihara hypothesis.

**Proof.** The parity and local transfer assertions give the definite packet. A function
module on a finite definite class set is finite free once the stabilizers are made prime to the
coefficient characteristic. A nonzero eigenline in its generic fiber meets that lattice in a
rank-one fractional ideal. Scaling its generator to be primitive gives a nonzero reduction.
The good Hecke character reduces to that of $\bar\rho|_{G_F}$ by Book 178's cross-prime stable-
lattice comparison; absolute irreducibility and Brauer--Nesbitt identify the residual global
representation. $\square$

This proposition removes the curve-switch step, but not target minimalization. Let
$P_{\rm tar}$ be the actual finite set where $\Pi^{\rm up}$ has more level than the exact
signed-special minimal problem. The required direct theorem is the following finite-set
interface.

**Missing theorem $({\rm DMS}_{P_{\rm tar}})$ (definite minimal-support transfer).** Starting
from the upper definite localization of Proposition 4.1 and the represented signed-special
minimal local problem, construct paired upper and minimal local rings and synchronized definite
Taylor--Wiles systems whose common residual support transfers to the minimal side. Recover at
finite level a nonzero minimal localization and verify the precise saturation,
primary--companion pairing, stabilizer, generic-reducedness, branchwise integral attachment,
diamond-torsor, and module-augmentation hypotheses of Book 173.

The statement is finite-set and uses the actual $P_{\rm tar}$; no singleton reduction is
allowed. It is also not a second invocation of Book 176's $({\rm IAV}_S)$. That theorem proves
automorphy of an already existing named characteristic-zero desired point. Before Book 181,
the minimal signed-special problem has no known characteristic-zero point. Here the conclusion
is instead residual occurrence and the exact clean minimal datum from which Book 173 can prove
the restricted $R=\mathbb T$ theorem.

Book 176, Theorem 1.2 proves the definite two-map Ihara and saturation statement needed at
each scalar weight-two changed place.  Its Section 1.6 also isolates the remaining content:
$({\rm DMS}_{P_{\rm tar}})=({\rm DLO}_{P_{\rm tar}})+({\rm CLN}_{\min})$.  The first term is
the simultaneous or fully reverified ordered implication from upper residual occurrence to
nonzero exact minimal occurrence; the second is the Book 173 structural ledger on that
minimal carrier.  Finite class sets remove the curve-switch Ihara hypothesis, but neither
their finiteness nor upper-side Taylor--Wiles patching proves $({\rm DLO}_{P_{\rm tar}})$.

Consequently the preferred construction has the exact form

$$
({\rm IAV}_{P_{\rm aux}})
\Longrightarrow \Pi^{\rm up}
\Longrightarrow \text{upper definite occurrence}
\xRightarrow{({\rm DMS}_{P_{\rm tar}})}
(\mathrm{Seed}_{\mathrm{SP}}^{181}).
\tag{4.3}
$$

The first implication is Book 178's conditional finite-set theorem and the middle implication
is Proposition 4.1. Only the last arrow is missing after those hypotheses. This route uses
neither the retired one-exceptional-sheet geometry nor the indefinite curve-switch
$({\rm AIH}_{\mathscr F})$ family. Book 181 further shows that its lift-existence argument
would need only the weaker restricted-special-fibre certificate
$(\mathrm{SF}_{\mathrm{SP}})$, but the present volume uses the full seed to make the chosen
point automorphic over $F$.

## 5. Potential automorphy of the chosen lift

### 5.1 Automorphy at the point field

**Theorem 5.1 (exact seed to the chosen point).** Let $\rho$ be the chosen lift of (1.2), and
assume a controlled chosen-lift refinement datum as in Chapter 3. Then, after one finite
coefficient extension, there is a parallel-weight-two cuspidal representation $\pi_F$ with

$$
r_{\pi_F,\lambda_F}\simeq\rho|_{G_F}
\tag{5.1}
$$

as integral representations. At every $w\mid2$, it retains nonzero rank-one monodromy, the
line $\mathscr L$, the sign $\varepsilon_2$, and conductor exponent one. It retains the chosen
finite-flat lattice at every $w\mid\ell$ and is unramified at every other finite place.

**Proof.** Lemma 3.1 supplies the full residual and residual--cyclotomic image hypotheses over
$F$. Complete splitting and Lemma 2.2 identify the dyadic local problem literally, and complete
splitting at $\ell$ identifies the selected coefficient-prime lattice condition. Hence
$\rho|_{G_F}$ is a characteristic-zero point of the represented problem
$\mathcal D_F^{\mathrm{SP}}$.

The exact automorphic datum supplies every hypothesis of Book 173. Therefore

$$
R_F^{\mathrm{SP}}\xrightarrow{\sim}\mathbb T_F^{\mathrm{SP}},
\tag{5.2}
$$

and every characteristic-zero point of the represented problem is automorphic with a matching
stable lattice. Evaluation at $\rho|_{G_F}$ gives (5.1). Because the local conditions on both
sides factor through the same represented quotients, the primitive monodromy, line, sign,
finite-flat lattice, and unramified conditions are retained. $\square$

The proof uses the chosen point only after the exact residual localization and the minimal
comparison have been supplied. It does not use automorphy of the point to prove the comparison
which makes the point automorphic.

### 5.2 Passage to the Galois top

**Theorem 5.2 (controlled potential automorphy of the chosen lift).** Under the hypotheses of
Theorem 5.1 and the selected ascent ledger of Section 3.3, there is a parallel-weight-two
cuspidal representation $\pi_M$ such that

$$
r_{\pi_M,\lambda_M}\simeq\rho|_{G_M}.
\tag{5.3}
$$

The representation $\rho|_{G_M}$ remains absolutely irreducible. At every dyadic place it has
the primitive signed-special tuple (2.6), and at every place above $\ell$ it has the selected
finite-flat lattice.

**Proof.** Apply Book 109 successively along (3.2), using the selected packet and local fiber
at each step. The result is an automorphic isobaric endpoint whose attached semisimple Galois
representation is $\rho|_{G_M}$ by distinguished-coefficient compatibility.

Lemma 3.1 makes $\bar\rho|_{G_M}$ absolutely irreducible. Hence $\rho|_{G_M}$ is absolutely
irreducible: a stable proper subspace in characteristic zero would yield, after intersecting
with a stable lattice and reducing, a proper residual constituent. A rank-two noncuspidal
isobaric endpoint has reducible attached representation, so the endpoint is cuspidal. Complete
splitting and Lemma 2.2 retain the full dyadic record, and the coefficient-prime record is
literal for the same reason. $\square$

This theorem cannot be obtained by replacing the selected ascent ledger with the word
“solvable.” The cyclic base-change theorem acts on selected packets satisfying its local and
global hypotheses, not on an abstract group series.

### 5.3 The direct-top case

If $J=1$, then $F=M$ and Theorem 5.1 already gives

$$
r_{\pi_M,\lambda_M}\simeq\rho|_{G_M}.
\tag{5.4}
$$

No cyclic ascent occurs. This is the cleanest form of the chosen-lift theorem: a controlled
exact seed on the Galois top makes the chosen point automorphic by evaluation of the same
minimal equality.

The direct-top simplification concerns only upward transfer. It does not prove the earlier
controlled seed, the later descent of packets to elementary fixed fields, the existence of raw
signed-special carriers, or the smooth-proper source of $(\mathrm{HT}_1)$.

## 6. Elementary fixed fields and basic carriers

### 6.1 Descent candidates

Let $H\leq\Gamma$ be elementary and put $F_H=M^H$. A prime-cyclic refinement inside $H$
gives a sequence of candidate automorphic descents from $M$ toward $F_H$. At a single cyclic
step, an arbitrary descent is determined only up to a quotient character. The global
representation $\rho$ supplies a coherent extension across every step and therefore selects
the quotient-character correction once an attached candidate descent exists.

For every selected candidate below, distinguished-coefficient attachment identifies its
global semisimplification with $\rho|_{G_{F_H}}$. Proposition 6.1 shows that this attachment
is a theorem once the candidate packet has been constructed; it is not an additional
all-elementary hypothesis.

This selection does not construct the candidate. Book 109 still requires an antecedent-complete
packet, saturation of the relevant extension fiber, and compatibility of attachment with base
change and finite-order twisting. These are finite arithmetic conditions, separate from the
group-theoretic existence of the cyclic series.

For the carrier statements below, assume the controlled top has a nonsolvable quotient, as in
the standard normal-top construction with a factor $S_5$. Then no elementary subgroup equals
$\Gamma$. Consequently

$$
[F_H:\mathbf Q]=[\Gamma:H]\geq2.
\tag{6.1}
$$

The same is true for every subgroup occurring in a prime-cyclic refinement inside $H$.

### 6.2 Parity-complete compact carriers

**Proposition 6.1 (basic carrier for every elementary candidate).** Let $H'\leq\Gamma$ be an
elementary subgroup or a subgroup in a prime-cyclic refinement inside one. Suppose a selected
parallel-weight-two candidate packet $\Pi_{H'}$ over $F_{H'}=M^{H'}$ is selected special at
every dyadic place. Then $\Pi_{H'}$ has a compact one-split quaternionic carrier, and its
semisimple compatible family is attached at every coefficient place. If the packet is
spherical at the retained places above $3$ and $\ell$, the carrier may be chosen hyperspecial
there.

**Proof.** Put $d=[F_{H'}:\mathbf Q]$, so $d\geq2$ by (6.1). If $d$ is even, choose one
dyadic special place and set $W=\{w_2\}$. If $d$ is odd, set $W=\varnothing$. In either case

$$
(d-1)+|W|\equiv0\pmod2.
\tag{6.2}
$$

The proposed ramification set has at least two places. For $d=2$, it consists of the inactive
real place and $w_2$; for $d\geq3$, there are already at least two inactive real places when
$W$ is empty. Book 104 therefore gives a compact quaternionic inner form split at one real
place and carrying the packet. Its inverse theorem imposes a selected-type hypothesis only at
the finite places in $W$; it requires no principal/dihedral classification at the other finite
places, where the inner form is split and the packet is unchanged. In particular the algebra
is split at every place above $3\ell$, and spherical packet factors there admit hyperspecial
level. Book 125 realizes the packet in the full component-routed curve block; Books 126--127
extract and attach its rank-two family, and Book 168 organizes the coefficient system.
$\square$

The parity choice is important. In odd degree one must not insist on adding a dyadic finite
ramification place: the inactive real places already have even cardinality. In even degree the
dyadic special place corrects parity. This gives a basic carrier in all degrees at least two,
but it does not yet give the particular integral geometry needed to read nonzero dyadic
monodromy before global semisimplification.

### 6.3 Compatibility of attachment

**Proposition 6.2 (cyclic and twisting compatibility).** The semisimple attachments in
Proposition 6.1 commute with every selected prime-cyclic base change and every finite-order
quotient twist occurring in the elementary descent diagram.

**Proof.** At the density-one set of places where the packets, field extensions, and
characters are unramified, the Hecke polynomials of cyclic base change are obtained by
restriction of the local parameter, while those of a quotient twist are obtained by tensoring
with the finite character. The attached semisimple representations satisfy the same
polynomial identities. Chebotarev density and Brauer--Nesbitt identify the resulting
representations. $\square$

There is also a good-prime comparison at the old coefficient prime $\ell$. For each of the
finitely many basic carriers, choose the imaginary quadratic field in Book 118 nonsplit at the
finite ramification of the quaternion algebra and split at $\ell$. The unitary
common-multiplier cover then gives, after an extension unramified above $\ell$, a finite
surjective map

$$
Y\longrightarrow X
\tag{6.3}
$$

from a proper good curve to the basic carrier, with hyperspecial level on both sides. Pullback
and trace satisfy $f_*f^*=(\deg f)$, so $H^1(X)$ is a rational direct summand of $H^1(Y)$.
It follows that the basic carrier is unramified at places above $\ell$ for coefficients of
different residue characteristic. The unramified base change used to construct $Y$ does not
alter inertia, so this conclusion descends to the original local field.

## 7. Raw signed-special carriers and semisimplicity

### 7.1 Raw multiplicity spaces

Let $X/F_H$ be one of the compact carriers of Chapter 6, and let $C_H$ be the finite
semisimple rational Hecke image cutting out a rank-two packet multiplicity space. Before any
global semisimplification, write

$$
W^{\mathrm{raw}}_{H,\tau}
$$

for the rank-two representation extracted from $H^1(X)$ at a coefficient embedding $\tau$.
Write

$$
r_{H,\tau}=(W^{\mathrm{raw}}_{H,\tau})^{\mathrm{ss}}
\tag{7.1}
$$

for its global semisimplification.

The adjective “raw” records the order of operations. Local monodromy and its distinguished
line live on the geometric multiplicity space. Global semisimplification may change the
restriction to a decomposition group. Therefore a local calculation on
$W^{\mathrm{raw}}_{H,\tau}$ is not automatically a local calculation on $r_{H,\tau}$.

A **raw signed-special carrier**, or **raw SP carrier**, is a carrier for which the dyadic semistable geometry, packet
projector, component routing, and rank-two extraction are all available before the passage in
(7.1), and for which that raw multiplicity space has the tuple

$$
(N,\mathscr L,\varepsilon_2,F_2NF_2^{-1}=2N)
\tag{7.2}
$$

with $N\ne0$.

This is stronger than a basic carrier. Proposition 6.1 proves rational packet occurrence and
semisimple attachment. It does not construct the required parahoric integral model or identify
the raw dyadic monodromy operator.

### 7.2 Why nonzero monodromy is different

When the raw local monodromy is zero, passage to the global semisimplification is formal: the
unramified Frobenius pair is determined by the invariant polynomial, and Book 128's
zero-monodromy comparison identifies the same local pair on $r_{H,\tau}$.

Nonzero monodromy behaves differently. A nonsplit extension of global representations can
carry a nonzero local monodromy operator even though its global semisimplification is a direct
sum on which that operator disappears. Thus good Frobenius polynomials and equality of global
semisimplifications do not preserve the signed-special extension.

One sufficient uniform hypothesis is

$$
(\mathrm{SS}_{\mathrm{array}}):qquad
H^1(X_{\overline{F_H}},\mathbf Q_p)
\text{ is semisimple as a }G_{F_H}\text{-module}
\tag{7.3}
$$

for every actual carrier $X$ in the finite packet array and every relevant coefficient
characteristic $p$. Under (7.3), every Hecke summand and every Morita multiplicity space is
globally semisimple. Hence

$$
W^{\mathrm{raw}}_{H,\tau}\simeq r_{H,\tau},
\tag{7.4}
$$

and the complete signed-special pair survives, including nonzero $N$, its line, and its
Frobenius sign, whenever the local comparison is prime to the coefficient residue
characteristic. This is stronger than is needed here.

Book 41 reduces (7.3) to finiteness of the relevant carrier Jacobians' isogeny classes. Its
uniform route to those finite isogeny classes retains explicit geometric and metric
hypotheses. It must not be replaced by purity or by semisimplicity of the Hecke algebra.
However, it is also unnecessary for the selected cuspidal packet array. If
$(\mathrm{HT}_1)$ holds for its raw rank-two factors, Book 168, Theorem 7.6 proves that every
semisimple packet realization is absolutely irreducible. Book 128, Lemma 9.1 then identifies
the raw multiplicity representation with that semisimplification. Thus

$$
(\mathrm{HT}_1)\quad\Longrightarrow\quad
W^{\mathrm{raw}}_{H,\tau}\simeq r_{H,\tau}
\tag{7.5}
$$

for every selected packet and coefficient place. Books 6 and 47 close the rank-one
local-algebraicity and subquotient reductions; the only unsupplied source of
$(\mathrm{HT}_1)$ is the smooth-proper comparison
$(\mathrm{HT}_{\mathrm{curve}})$ of Book 47, (9.7). Consequently ambient
$(\mathrm{SS}_{\mathrm{array}})$ is only an optional stronger certificate, not a second
clause of the preferred raw-carrier theorem.

At coefficient residue characteristic $2$, even global semisimplicity does not create a
prime-to-coefficient Weil--Deligne comparison at the dyadic base place. That is a separate
boundary and is not repaired by (7.3).

### 7.3 The exact raw-carrier boundary

The remaining carrier theorem has only the following geometric output:

$$
(\mathrm{RSP}_{2}):\qquad
\text{each selected elementary packet and dyadic target has a raw carrier satisfying (7.2),}
\tag{7.6}
$$

with the packet projector, component orbit, oriented dyadic branches, raw unnormalized
$U_2$ correspondence, and the rank-two multiplicity extraction all defined on that same
carrier. The output must be algebraic before completion;
it need not prescribe principal, dihedral, or other automorphic types away from two. Once
(7.6) is supplied, (7.5) transports its special pair uniformly from
$(\mathrm{HT}_1)$; no ambient Tate-semisimplicity theorem belongs to this interface.

The searched attachment books already prove everything before (7.6). Book 104, Theorem 9.2
puts each selected split packet on the parity-correct one-split inner form, Book 125 realizes
that packet in curve cohomology, and Books 126--127 extract and attach its raw and semisimple
rank-two representations. Books 80--84 and 92--109 supply the local and global automorphic
transfers used in that argument, but none constructs a parahoric integral model or a graph
monodromy line. Thus a stronger theorem asserting automorphic occurrence or every elementary
automorphic type would duplicate proved work without supplying (7.6).

For a carrier already split at every dyadic factor, the first missing geometry on the existing
route is recorded exactly in Book 122, Sections 10.3--10.5. Its Proposition 10.2 constructs a
non-common-norm unitary dyadic parahoric source. To make that source the raw carrier of the
basic packet one still needs the finite
integral common-adjoint comparison (10.5): an extension unramified at two, finite locally
free maps at the good and Iwahori vertices, effective component descent, Hecke and degeneracy
compatibility, expansion-one strict-node maps, and equality of the selected packet planes.
Generic equality of adjoint groups and rational Jacquet--Langlands do not imply this integral
statement.

There is an additional parity boundary before that comparison can be applied. Book 122's
unitary source assumes that the quaternion algebra is split at every dyadic factor. In odd
degree the Book 104 choice $W=\varnothing$ clears this automorphic condition. In even degree
the basic carrier of Proposition 6.1 uses a dyadic singleton to correct parity, so it fails the
complete dyadic-splitting ledger. Another dyadic special place does not help. The present
corpus supplies neither an odd eligible ramification set away from two nor a mixed-dyadic
parahoric theorem for that carrier. Hence an honest proof of (7.6) must supply, packet by
packet, either

1. a parity-compatible eligible carrier ramified only away from two together with Book 122's
   finite integral comparison (10.5); or
2. a new mixed-dyadic geometric comparison which applies directly to the parity carrier of
   Proposition 6.1.

This is the smallest remaining raw SP hypothesis. Abstract ambient semisimplicity cannot
construct it, and a broad principal/dihedral type package is irrelevant to it.

## 8. Auxiliary Galois comparisons

### 8.1 The distinguished unramified anchor

The auxiliary comparison away from two requires less than the raw signed-special theorem.

**Proposition 8.1 (common unramified algebraic pair).** For every actual basic carrier of
Proposition 6.1, let $W^{\mathrm{raw}}_{H,\tau}$ and $r_{H,\tau}$ be as in (7.1). Let $w$ lie
above a rational prime $p\ne2$, and assume that the residue characteristic of $\tau$ differs
from $p$. Then both

$$
W^{\mathrm{raw}}_{H,\tau}|_{G_{(F_H)_w}}
\quad\text{and}\quad
r_{H,\tau}|_{G_{(F_H)_w}}
\tag{8.1}
$$

are unramified. Over the common packet field there is an unramified algebraic
Frobenius-semisimple pair $D_{H,w}$ satisfying

$$
\operatorname{WD}_w(r_{H,\tau})^{\mathrm{F\text{-}ss}}
\simeq D_{H,w}\otimes_\tau\Omega.
\tag{8.2}
$$

**Proof.** First suppose $p\ne\ell$. At the distinguished embedding $\iota_0$, the global
semisimplification of $W^{\mathrm{raw}}_{H,\iota_0}$ is
$\rho|_{G_{F_H}}$. The latter is absolutely irreducible because its restriction to $G_M$ is
absolutely irreducible. Since the raw multiplicity space has dimension two, a
semisimplification which is irreducible of the same dimension has only one Jordan--Hölder
factor. Therefore

$$
W^{\mathrm{raw}}_{H,\iota_0}\simeq\rho|_{G_{F_H}}.
\tag{8.3}
$$

The right side is unramified at $w$ by (1.3).

Let $J_H$ be the Jacobian of the carrier. Generic Hecke correspondences act on $J_H$ up to
isogeny, and the selected raw representation is the corresponding multiplicity factor. Book
61 proves that the Artin conductor and inertia-invariant Frobenius polynomial of such a factor
are independent of the coefficient place. Equation (8.3) makes the conductor zero at
$\iota_0$, so it is zero at every $\tau$ whose residue characteristic differs from $p$. The
raw factor is therefore unramified. The common invariant Frobenius polynomial defines
$D_{H,w}$. Since monodromy is zero, the zero-monodromy comparison of Book 128 passes this pair
to the global semisimplification and proves (8.2).

If $p=\ell$, use the good unitary cover (6.3). Its proper smooth cohomology is unramified above
$\ell$ for every coefficient of different residue characteristic. Rational direct summands,
Hecke multiplicity spaces, and their global semisimplifications remain unramified. The same
coefficient-independent Frobenius polynomial again defines $D_{H,w}$. $\square$

The proposition identifies a Galois Frobenius return polynomial. It does not identify a
ramified automorphic inertial type.

### 8.2 Twisting, induction, and clean support

If an elementary term is twisted by a finite quotient character $\theta$, its local algebraic
pair is

$$
D_{H,w}\otimes\theta_w.
\tag{8.4}
$$

The conductor is twice the conductor of $\theta_w$ when the underlying rank-two factor is
unramified. Weil induction of (8.4) is again algebraic. Hence every local Mackey object used
in the elementary Brauer array exists at every prime away from two and every coefficient place
away from that prime.

These common pairs are exactly the input needed for the later positive--negative direct-sum
identity. After effectivity is known, Krull--Schmidt cancellation compares the actual Galois
summands and yields the auxiliary comparison and clean support. Neither a principal type
projector nor a dihedral nearby-cycle calculation is required for this Galois conclusion.

This is why the raw-to-global input has a role only at nonzero monodromy. The preferred
certificate there is $(\mathrm{HT}_1)$, with ambient semisimplicity only a stronger
alternative. Neither is needed in Proposition 8.1: the distinguished irreducible raw member
anchors conductor zero, coefficient independence carries that fact to all coefficients, and
the zero-monodromy comparison passes it to the global semisimplification.

### 8.3 Why automorphic type is a stronger question

A statement prescribing principal or dihedral automorphic types at retained auxiliary places
requires additional geometry. One must first prove that the relevant local cyclic quotient is
tame. A cyclic principal quotient can be wildly ramified even when its restriction upstairs
is spherical: if $L/K$ is wildly ramified cyclic and $\psi$ is a nontrivial quotient
character, then

$$
(\alpha\psi)\oplus(\beta\psi^{-1})
\tag{8.5}
$$

restricts to the spherical pair $\alpha\oplus\beta$ over $L$ while retaining wild inertia
over $K$. Local Clifford theory controls irreducible dihedral extensions but does not exclude
the principal example (8.5).

After tameness, a full type theorem still needs a fine semistable model, extension of the
packet and type projectors, component routing, the two type lines, the exchange action in the
dihedral case, vanishing of the restriction--Gysin monodromy, and normalized Frobenius return
maps. The general principal/dihedral branch calculation is stronger than the strict-ray
quotient and augmentation rows already established in the earlier semistable geometry.

Moreover, a genuinely ramified type cannot describe the same factor for which Proposition 8.1
proves the unramified pair (8.2). Any such claim must either concern a different factor or be
relabelled before its geometric proof is attempted. Thus the stronger automorphic-type theorem
is neither proved here nor required for the auxiliary Galois comparison and clean-support
argument.

## 9. The controlled-top theorem and conclusion

We can now state the exact post-181 result in the form needed downstream.

**Theorem 9.1 (chosen-lift Galois refinement).** Let $\rho$ be a chosen primitive
signed-special lift supplied by Book 181 under its explicit seed hypothesis. Assume:

1. a controlled chosen-lift refinement datum as in Chapter 3;
2. a selected elementary descent ledger for the finite fixed-field diagram;
3. the local hypotheses of Proposition 6.1 for every candidate packet;
4. $(\mathrm{RSP}_{2})$ of (7.6), and either $(\mathrm{HT}_1)$ for the selected packet
   factors or a direct local-preservation certificate; the stronger
   $(\mathrm{SS}_{\mathrm{array}})$ may be used instead.

Then:

1. there is a parallel-weight-two cuspidal packet $\pi_M$ with
   $r_{\pi_M,\lambda_M}\simeq\rho|_{G_M}$;
2. every elementary descent candidate has a parity-correct compact basic carrier and a
   semisimple attachment at every coefficient place;
3. attachment commutes with the selected cyclic base changes and quotient twists;
4. at every place away from two, the elementary packet factors have the common unramified
   algebraic Galois pairs of Proposition 8.1;
5. at coefficient embeddings of residue characteristic different from two, the raw
   signed-special pair survives global semisimplification on every carrier covered by item 4
   of the hypotheses.

**Proof.** The first assertion is Theorem 5.2. Propositions 6.1 and 6.2 give the second and
third. Proposition 8.1 and the twisting and induction operations of Section 8.2 give the
fourth. Finally, $(\mathrm{RSP}_{2})$ places the tuple (7.2) on the geometric multiplicity
space. Under the preferred hypothesis, (7.5) identifies that space with its global
semisimplification; a direct certificate or (7.4) gives the stated alternatives. This proves
the fifth assertion. $\square$

The theorem has two exact conditional boundaries. The earlier one is the controlled residual
seed summarized in Chapter 4. On the preferred split route, after the separate
$({\rm IAV}_{P_{\rm aux}})$ certificate, Proposition 4.1 supplies upper definite occurrence
and the smallest remaining package is $({\rm DMS}_{P_{\rm tar}})$, beginning with the
unproved occurrence theorem $({\rm DLO}_{P_{\rm tar}})$; no preceding volume proves that
target-minimal support theorem and its clean bottom ledger. The later one is the
geometric $(\mathrm{RSP}_{2})$ hypothesis of Chapter 7, together with the already isolated
smooth-proper source of $(\mathrm{HT}_1)$. Basic carrier existence does not close the former,
while Proposition 8.1 shows that neither input is needed for the auxiliary unramified pairs.

The mathematical progression is therefore linear:

$$
\begin{array}{c}
\text{Book 181 chosen primitive signed-special lift}\\
\Downarrow\\
\text{controlled exact datum over }F\text{ and selected ascent to }M\\
\Downarrow\\
\rho|_{G_M}\text{ is automorphic}\\
\Downarrow\\
\text{elementary candidate packets and parity-complete basic carriers}\\
\Downarrow\\
\text{common auxiliary unramified Galois pairs away from two}.
\end{array}
\tag{9.1}
$$

On a separate final branch, raw signed-special geometry together with $(\mathrm{HT}_1)$
preserves the nonzero monodromy line and sign across all relevant coefficient embeddings.
Ambient semisimplicity is a stronger alternative. That branch cannot be moved earlier and
cannot be replaced by good Frobenius traces.

Thus this volume does not reconstruct the residual seed used before Book 181, and it does not
claim an unconditional controlled top. It proves the chosen-point potential-automorphy and
Galois-refinement implications from their exact hypotheses, proves the parity-complete basic
attachment and auxiliary Galois comparisons, and isolates precisely the additional geometric
raw-carrier input and the separate $(\mathrm{HT}_1)$ comparison needed to retain the
signed-special local record in the later family.

There is a final source-record distinction. The pre-point finite-image record in the FLT
formalization asks for a module-finite Hecke coefficient model of the scalar-reduced universal
representation over one finite totally real field, including its local conditions,
cyclotomic-degree inequality, rigidified totally definite quaternion algebra,
Frobenius-compatible surjective eigenform, coefficient map, and factorization through the
restricted representation up to a recorded conjugating matrix. That record is consumed in
Book 181 and cannot be obtained backward from the chosen point fixed in (1.2).

The post-point compatible-family arithmetic core exposes four arithmetic fields:

1. independent automorphic Brauer summands, their genuine rank-two realization, common traces,
   and common unramifiedness;
2. the original-prime realization of the common Frobenius trace coefficient;
3. support of the common bad-place set at $2$; and
4. finite-flat and tame integral models at every other odd coefficient prime and every other
   embedding above the original prime.

This book supplies only the controlled potential-automorphy and packet-refinement input from
which the first two fields are later constructed. Brauer assembly and effectivity belong to
Books 183--185; the fourth field remains a separate integral-model theorem and is not implied
by compactness of an arbitrary stable lattice. In particular, none of the finite-set
level-change or bottom-carrier ledgers of Chapter 4 is silently promoted to a fifth field of
the compatible-family core.

These four fields are again only the formal handoff. Their construction still requires the
mathematics suppressed by the record: a controlled potential-automorphy field for the chosen
lift; selected solvable packet descent on every elementary fixed field; local--global
compatibility on every summand and overlap; an integral Brauer relation with termwise
original-prime comparison; genuineness and coefficient descent of the signed virtual class to
one rank-two family; proof that the common bad set is supported at $2$, rather than merely
finite; and stable lattices carrying the exact tame quotient at $2$ and finite-flat model at
each coefficient prime. Arbitrary compact stable lattices, rational Frobenius compatibility,
or equality of conductors do not supply the last assertion. Books 183--187 separate these
steps, and their remaining hypotheses—not the four-field packaging—are the true blockers for
inhabiting the arithmetic core.
