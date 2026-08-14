# Moduli Constructions for Potential Modularity

## Contents

1. [The application problem](#1-the-application-problem)
   - [One object, two residual systems](#11-one-object-two-residual-systems)
   - [Why a moving presentation is the real output](#12-why-a-moving-presentation-is-the-real-output)
   - [The exact boundary of the construction](#13-the-exact-boundary-of-the-construction)
2. [The paired-frame Hilbert--Blumenthal space](#2-the-paired-frame-hilbert--blumenthal-space)
   - [Arithmetic input](#21-arithmetic-input)
   - [Determinant lines and paired frames](#22-determinant-lines-and-paired-frames)
   - [The corrected tensor component](#23-the-corrected-tensor-component)
   - [The realization space](#24-the-realization-space)
3. [The local packet ledger](#3-the-local-packet-ledger)
   - [Five kinds of local seed](#31-five-kinds-of-local-seed)
   - [The singleton place](#32-the-singleton-place)
   - [Wholesale-repeatable packets](#33-wholesale-repeatable-packets)
   - [Flexible split packets](#34-flexible-split-packets)
   - [Realized normal sheets](#35-realized-normal-sheets)
4. [The fixed-offset obstruction](#4-the-fixed-offset-obstruction)
   - [The Abel-class calculation](#41-the-abel-class-calculation)
   - [Why divisibility is insufficient](#42-why-divisibility-is-insufficient)
   - [Integral-open saturation](#43-integral-open-saturation)
5. [The toroidal joining boundary](#5-the-toroidal-joining-boundary)
   - [What is already constructed](#51-what-is-already-constructed)
   - [The exact remaining hypotheses](#52-the-exact-remaining-hypotheses)
   - [From toroidal gluing to a stable slice](#53-from-toroidal-gluing-to-a-stable-slice)
   - [The finite-residue distinction](#54-the-finite-residue-distinction)
6. [Constructing the singleton moving presentation](#6-constructing-the-singleton-moving-presentation)
   - [Admissible moving data](#61-admissible-moving-data)
   - [The common-degree argument](#62-the-common-degree-argument)
   - [The conditional construction theorem](#63-the-conditional-construction-theorem)
   - [What the theorem proves unconditionally](#64-what-the-theorem-proves-unconditionally)
7. [The generic normal closure](#7-the-generic-normal-closure)
   - [The Galois top and its root quotient](#71-the-galois-top-and-its-root-quotient)
   - [Propagation of the local conditions](#72-propagation-of-the-local-conditions)
   - [Exact conditions that do not propagate formally](#73-exact-conditions-that-do-not-propagate-formally)
8. [Normal-closure avoidance](#8-normal-closure-avoidance)
   - [The avoidance field](#81-the-avoidance-field)
   - [The constant-field obstruction](#82-the-constant-field-obstruction)
   - [Split certificate packets](#83-split-certificate-packets)
   - [The closure-level avoidance datum](#84-the-closure-level-avoidance-datum)
9. [The complete export package](#9-the-complete-export-package)
   - [The moving presentation](#91-the-moving-presentation)
   - [The local equivariant data](#92-the-local-equivariant-data)
   - [The conditional application theorem](#93-the-conditional-application-theorem)
   - [Sharp exclusions](#94-sharp-exclusions)
10. [Conclusion](#10-conclusion)

## 1. The application problem

### 1.1 One object, two residual systems

Let $K$ be a totally real number field. The geometric problem considered here begins with two
continuous rank-two residual systems over distinct odd characteristics. They are to occur as
two torsion factors of one abelian variety with real multiplication. The point is not merely to
find separate abelian varieties carrying the two systems. One object must carry both systems,
both polarization pairings, one auxiliary neat level, and every prescribed local reduction
condition.

The preceding two books provide the natural ambient space. Book 156 constructs the fine
Hilbert--Blumenthal moduli problem and its determinant-compatible two-prime paired-frame cover.
Book 157 constructs the corrected tensor component, its real and nonarchimedean local points,
and the open neighborhoods on which the exact local conditions persist. This book applies
those constructions to a moving problem with one exceptional local factor.

The exceptional factor is the source of the main difficulty. At one finite place $v_0$, the
local fiber must contain exactly one degree-one semistable factor. Every other factor at that
place must have good minimal reduction. At other places an entire nonsplit packet may be
repeated, or a split packet may be enlarged freely. A single finite etale family must realize
all these local cycles in one common degree.

### 1.2 Why a moving presentation is the real output

Local points on the paired-frame moduli space are not yet an arithmetic approximation datum.
To apply irreducible-cycle approximation one needs a common affine parameter space and a
geometrically integral incidence family

$$
T\longrightarrow H,
\qquad
e:T\longrightarrow Y,
\tag{1.1}
$$

where $H$ is a nonempty open of affine space, $T/H$ is finite etale of one degree $d$, and the
fibers over selected local parameters are the prescribed local cycles. The family must remember
the two frames on every sheet. At the singleton place its fiber must have the form

$$
\text{one special factor}
\quad+\quad
\text{a reduced good divisor of degree }d-1.
\tag{1.2}
$$

It must also be compatible with any required divisibility of $d$, avoid a prescribed proper
closed subset, and retain the local behavior after passage from the root sheets to the sheets
of the generic normal closure.

This is stronger than the existence of nonempty local opens. It is also stronger than a list
of local zero-cycles of equal degree. Equal degrees do not imply that the cycles lie in fibers
of one global pencil, and a normal closure taken only after specialization does not remember the
equivariant local sheet data.

### 1.3 The exact boundary of the construction

The toroidal input needed for (1.2) is not fully available from the preceding books. Book 157
constructs the paired-frame Kummer normalization, a simultaneous regular projective
equivariant fan, the inverse over complete traits, the completed deformation ring on the
already-Mumford-presented side, and the stable relative slicing theorem. It does not prove the
full fan-dependent framed toroidal gluing theorem.

Accordingly the central construction in this book is conditional on the exact toroidal
hypotheses isolated in Chapter 5. Under those hypotheses, the presentation (1.1) is genuinely
constructed and its properties are proved. Without them, the theorem remains a conditional
implication. No projective closure, formal chart, or bare fan is treated as a substitute.

Even after (1.1) has been constructed, this book does not select a global parameter
$h\in H(K)$. It therefore produces no global specialization field, no global abelian variety,
and no automorphic starting datum. Its endpoint is the moduli-theoretic moving presentation,
its generic normal-closure diagram, and the exact avoidance data to be imposed by arithmetic
specialization.

## 2. The paired-frame Hilbert--Blumenthal space

### 2.1 Arithmetic input

Fix a totally real coefficient field $E$ of degree $g$, an ordered polarization module with
positive cone, and the corrected tensor lattice and auxiliary level of Book 157. Let
$\mathfrak p$ and $\mathfrak q$ be distinct monodromy-admissible odd primes of $E$, away from
the different, polarization degree, and auxiliary level.

Let

$$
V_{\mathfrak p},\qquad V_{\mathfrak q}
\tag{2.1}
$$

be rank-two finite Galois modules over the corresponding residue fields. Each module is supplied
with a chosen identification of its determinant line with the coefficient line coming from the
Hilbert--Blumenthal polarization. These are isomorphisms of Galois modules, not equalities of
characters written without a chosen map.

The local packet data will be imposed only in the ranges constructed in Book 157: real paired
frames, good reduction away from the level primes, ordinary or local--local finite-flat
coefficient-prime points, and tensor-Tate semistable points with compatible Kummer classes.
Every extension of a completion used to produce a frame is part of the input.

### 2.2 Determinant lines and paired frames

For a polarized abelian scheme $A$ with real multiplication, the polarization induces, at
$\mathfrak r\in\{\mathfrak p,\mathfrak q\}$, a perfect alternating pairing

$$
A[\mathfrak r]\times A[\mathfrak r]
\longrightarrow L_{\mathfrak r}.
\tag{2.2}
$$

A paired frame is an isomorphism

$$
\alpha_{\mathfrak r}:V_{\mathfrak r}
\xrightarrow{\sim}A[\mathfrak r]
\tag{2.3}
$$

whose determinant is the chosen identification with $L_{\mathfrak r}$. Fixing this determinant
reduces the frame group from a general linear or similitude group to the corresponding special
linear group. If the determinant line is wrong, the fixed-pairing twist is empty. A scalar
quadratic twist cannot repair an arbitrary determinant because its square is trivial in the
determinant ratio.

The two frames are imposed on one Hilbert--Blumenthal object. Taking a product of two
independently twisted spaces would not force the torsion systems onto the same abelian scheme
and would not give compatible component or descent data.

### 2.3 The corrected tensor component

Book 157 selects a tensor component defined over $K$ and a cyclotomic-split neat auxiliary
level. Its correction is essential at the real places and at the local tensor seeds. It ensures
that the ordered polarization, the auxiliary level, and both paired-frame systems occur on one
arithmetic component.

Write $Y$ for the determinant-compatible two-prime twist of this corrected component. By Books
156--157, $Y$ is a smooth quasi-projective geometrically connected fine $K$-scheme of pure
dimension $g$. It carries a universal Hilbert--Blumenthal abelian scheme

$$
\mathcal A\longrightarrow Y
\tag{2.4}
$$

with real multiplication, ordered polarization, auxiliary level, and universal paired frames

$$
V_{\mathfrak p}\simeq\mathcal A[\mathfrak p],
\qquad
V_{\mathfrak q}\simeq\mathcal A[\mathfrak q].
\tag{2.5}
$$

The geometric connectedness here uses full product monodromy. Separate surjectivity to the two
special-linear factors would not exclude a diagonal coupling through a common quotient.

### 2.4 The realization space

Let $Z\subsetneq Y$ be a proper closed subset containing every degeneracy locus that the
specialized object must avoid. We work on

$$
U=Y\setminus Z.
\tag{2.6}
$$

Since $Y$ is fine, a point of $U$ is an actual tuple, not merely an isomorphism class on a
coarse space. Pulling back (2.4)--(2.5) along a field-valued point gives one abelian variety with
both exact frames. The condition of belonging to $U$ is stable under extension of the point
field.

The purpose of the remaining chapters is to construct, conditionally on the exact toroidal
joining input, a finite etale moving family evaluated in $U$ whose local fibers realize the
full packet ledger.

## 3. The local packet ledger

### 3.1 Five kinds of local seed

Let $S$ be a finite set of places of $K$. At every $v\in S$, Book 157 supplies a nonempty local
open on $Y$ once the corresponding compatibility conditions have been checked. The five
available rows are:

1. a real paired-frame component, requiring oddness of both systems;
2. a good point away from the two coefficient primes and the auxiliary level;
3. an ordinary finite-flat point at a coefficient prime;
4. a nonordinary local--local finite-flat point at a coefficient prime; and
5. a tensor-Tate semistable point with the prescribed toric rank, splitness, Kummer class,
   enhanced line, and sign.

At a coefficient prime, finite flatness of the given residual system does not by itself realize
a named finite-flat model inside a chosen PEL object. The exact seed and every permitted frame
field remain part of the local datum. At a tensor-Tate place, two nontrivial residual Kummer
classes can be imposed simultaneously only when they come from the same tensor Tate parameter
in the sense of Book 157.

### 3.2 The singleton place

Choose one finite place $v_0$, away from the coefficient and auxiliary-level primes, at which
both residual frame systems are unramified over the assigned completion. Fix:

- a degree-one semistable point $y_{\mathrm{sp}}\in U(K_{v_0})$ in the selected tensor-cusp
  branch;
- a point-centered open $V_{\mathrm{sp}}$ retaining its valuation shell, Kummer class,
  enhanced line, sign, component, and both frames; and
- an allowed good-minimal condition on all other factors of the local cycle.

The local cycle must contain exactly one point in $V_{\mathrm{sp}}$. Repetition of that special
factor is forbidden. The remaining $d-1$ points may have arbitrary finite etale residue fields,
but each of their closures must meet the allowed good part of one common integral slice.

This is the singleton mixed packet. It is not a wholesale-repeatable packet with one chosen
copy marked afterward: repeating the packet would repeat the special factor and change the
local deformation problem.

### 3.3 Wholesale-repeatable packets

At a place $v\ne v_0$, let

$$
A_v=\prod_iE_{v,i}
\tag{3.1}
$$

be a finite etale $K_v$-algebra and let

$$
\Omega_v\subset U(A_v)
\tag{3.2}
$$

be an open containing a geometrically injective reduced packet. Call this packet
**wholesale-repeatable** if the arithmetic condition permits any sufficiently large number of
pairwise disjoint copies of the entire packet. Each copy retains every factor of $A_v$ and every
assigned local condition.

Book 157, through the norm--Abel moving result used in its Proposition 13.2A, places every such
packet in a sufficiently large arithmetic progression of allowed exponents. One may not repeat
only a favorable factor of $A_v$ while discarding the others.

### 3.4 Flexible split packets

At a split place, fix a nonempty open

$$
\Omega_v\subset U(K_v).
\tag{3.3}
$$

A flexible split fiber is a reduced sum of $d$ distinct $K_v$-points in $\Omega_v$, with $d$
chosen sufficiently large. The local curve-and-pencil construction permits $d$ to vary through
a sufficiently large progression. These packets provide room for total-reality conditions,
complete splitting at sensitive finite places, and the certificate places of Chapter 8.

Flexibility is a hypothesis about the allowed arithmetic condition. A condition requiring one
fixed field factor, one fixed number of special factors, or one exact valuation is not flexible
merely because its local locus is open.

### 3.5 Realized normal sheets

The incidence family constructed later has a generic Galois closure. At each nonsplit
controlled place, every sheet of the local top fiber maps to a root sheet after a finite
separable scalar extension. The **realized normal-sheet condition** requires that these
pullbacks have the intended local behavior.

This book calls the normal-sheet clause admissible only when the intended behavior is the
scalar extension of an already chosen root-sheet condition and that condition persists under
finite extension. Good, ordinary, local--local, semistable, toric-rank, finite-flat,
paired-frame, component, and open-avoidance conditions have this persistence in Book 157.

The construction does not cover an independently prescribed decomposition homomorphism,
persistence of nonsplitness, a nonzero Kummer class that may become trivial, or a normalized
valuation required to keep the same integer. Such requirements need a separately supplied
Galois presentation whose actual top local fiber has the requested behavior. The phrase
"normal sheets" never creates those local extensions or descends a frame to a smaller
completion.

## 4. The fixed-offset obstruction

### 4.1 The Abel-class calculation

The singleton obstruction is already visible on the local curve used to construct a pencil.
Let $k=K_{v_0}$, let $C/k$ be the smooth projective local slice, and let $\mathcal L$ be the
pencil line bundle of degree $e>0$. Choose a special representative

$$
S\in V_{\mathrm{sp}}
\tag{4.1}
$$

and a good base point $P\in C(k)$. Put

$$
b=[\mathcal L]-e[P],
\qquad
c=[S-P]
\quad\text{in }J_C(k).
\tag{4.2}
$$

For $m\ge0$, let $\mathscr R_m^{\mathrm{good}}$ be the set of classes

$$
[D-mP]
\tag{4.3}
$$

where $D$ is a reduced effective divisor of degree $m$, disjoint from the special point, and
every residue-field factor of $D$ is allowed good minimal. A divisor in the class of
$\mathcal L^n$ with one varying special point $T\in V_{\mathrm{sp}}$ and all other factors
good exists exactly when

$$
nb\in
\{[T-P]:T\in V_{\mathrm{sp}}\}
+\mathscr R_{ne-1}^{\mathrm{good}}.
\tag{4.4}
$$

Freezing the special point at $S$ gives the sufficient condition

$$
nb-c\in\mathscr R_{ne-1}^{\mathrm{good}}.
\tag{4.5}
$$

This is the fixed-offset condition. It allows arbitrary good residue-field factors; it is not
restricted to repeated points in one residue disk.

### 4.2 Why divisibility is insufficient

Suppose, more restrictively, that every added good point lies in one good tube about $P$. Let
$G_P\subset J_C(k)$ be the open subgroup generated by differences of points in that tube. For
large $n$, condition (4.5) becomes

$$
nb-c\in G_P.
\tag{4.6}
$$

Making $n$ divisible by the exponent of $J_C(k)/G_P$ kills the image of $nb$, but it does not
kill the fixed class $c$. Thus high degree and divisibility alone do not solve the singleton
problem.

The obstruction is geometric. On an elliptic curve with good reduction, take the good tube to
reduce to the origin and the special tube to reduce to a nonzero residue point. Norms of points
from the good tube remain in the reduction kernel, whereas the special offset does not. Then
(4.4) fails in every degree even after allowing arbitrary finite residue extensions inside
that one tube.

Consequently smoothness of $Y$, Hensel lifting of its local points, and openness of the
norm--Abel image do not prove the moving theorem. They supply local room inside the subgroup
that is actually reached; they do not move the special offset into a missing coset.

### 4.3 Integral-open saturation

The obstruction disappears if the local slice has a smooth proper integral model
$\mathcal C/R$, where $R$ is the valuation ring of $k$, and if there is a nonempty open

$$
W\subset\mathcal C_{\kappa}
\tag{4.7}
$$

such that every closed point of $C$ whose closure specializes into $W$ is allowed good minimal.
Relative Riemann--Roch then proves, for every sufficiently large $m$, that

$$
\mathscr R_m^{\mathrm{good}}=J_C(k).
\tag{4.8}
$$

Indeed every degree-$m$ line bundle extends to the regular relative curve. For $m$ large, a
special-fiber section can be chosen nonzero on the finite complement of $W$, lifted to the
integral model, and perturbed away from the nonreduced-divisor and marked-point loci. Its zero
divisor is reduced and all its factors specialize into $W$. Varying the degree-zero class of
the line bundle realizes every element of the Jacobian.

Equation (4.8) makes (4.5) automatic for every sufficiently large $n$. The singleton place then
imposes no arithmetic progression beyond largeness, so its degree can be synchronized with the
progressions coming from wholesale-repeatable and flexible packets.

The load-bearing issue is therefore not the divisor argument but the construction of the same
integral slice inside one projective model that joins the good interior to the selected framed
tensor-cusp branch. The next chapter records exactly what is known about that joining problem.

## 5. The toroidal joining boundary

### 5.1 What is already constructed

Book 157 proves the following parts of the boundary geometry.

First, the two paired frames enlarge the unframed Fourier lattice
$\mathfrak M_b^0$ at a cusp branch $b$ to a finite-index framed lattice

$$
\mathfrak M_b^{\mathrm{fr}}
=\mathfrak M_b^0+
\sum_j\mathbf Z\frac{\xi_j}{n_j}.
\tag{5.1}
$$

After the recorded finite etale extension containing the constant Kummer roots, the
normalization of a toric chart is

$$
R'[\sigma^\vee\cap\mathfrak M_b^{\mathrm{fr}}].
\tag{5.2}
$$

Normalization commutes with completion, and the division monomials in (5.2) recover the two
paired frames of the boundary one-motive.

Second, Book 157 constructs a simultaneous regular projective fan $\Sigma_b$ for the refined
cocharacter lattice. The collection is equivariant for the cusp, deck, and descent actions;
contains every marked valuation ray; has trivial nonzero-cone stabilizers at neat level; and
carries compatible strictly convex integral support functions after one common positive
multiple.

Third, the complete-trait inverse is proved: after a finite splitting extension, a semistable
Hilbert--Blumenthal object is either good or totally toric and is recovered from its positive
one-motive. The completed deformation ring is computed for the logarithmic one-motive and for
a degeneration already known to be Mumford-presented. The periodic theta line and the toric
support-function calculation are also proved on that side.

Fourth, once a smooth projective joining model is supplied, finite-field Bertini with imposed
first jets and relative lifting over a complete DVR construct a smooth proper geometrically
connected complete-intersection curve. The construction is stable in a congruence neighborhood
of the cutting tuple, exactly as required by the global weak-approximation step.

### 5.2 The exact remaining hypotheses

The proved statements in Section 5.1 do not construct the framed toroidal compactification.
The exact missing chain is as follows.

1. **Infinitesimal toroidal recognition $({\rm IIT})$.** For every square-zero logarithmic
   lifting of a labelled boundary degeneration, the PEL structure must force each smoothing
   coefficient and overlap translation to equal the prescribed logarithmic monomial times a
   unit. Labelled reduction and flatness do not force this: the local algebra
   $$
   k[\epsilon]/(\epsilon^2)[X,Y]/(XY-\epsilon)
   \tag{5.3}
   $$
   reduces to the labelled node with external logarithmic parameter zero but has a nonzero
   infinitesimal smoothing.
2. **Relative Mumford--PEL equivalence $({\rm MPE})$.** This follows conditionally from
   $({\rm IIT})$ by the square-zero induction in Book 157, but is not available without that
   antecedent.
3. **Bounded conductor presentation $({\rm BCP})$ and single-chart effectivity
   $({\rm AEC}_0)$.** These must algebraize the nonnormal conductor pushout, all structure
   graphs, and the prescribed saturated log chart with bounded finite-presentation data.
4. **Ramified conductor descent $({\rm RCD})$.** Componentwise descent on the normalization
   must agree on the conductor square and lift across nilpotents. Full faithfulness on the
   normalized components gives uniqueness after such an agreement exists, not its existence.
5. **Theta--determinant compatibility $({\rm TDC})$.** The family theta cocycle must be
   compared with a positive power of the ample interior moduli line, with algebraic transition
   maps and horizontal, vertical, and mixed positivity on the global gluing.

The conjunction of the last three algebraic and descent requirements with the algebraized
overlap relation is Book 157's required algebraic cusp-effectivity package $({\rm ACE})$. The
fan-dependent framed toroidal gluing theorem

$$
({\rm TCG})_{\Sigma}
\tag{5.4}
$$

is conditional on $({\rm MPE})$ and $({\rm ACE})$. Book 157 proves that, once this complete
unframed package is supplied, finite normalization and finite etale twist descent yield the
paired-frame compactification without a second compactification hypothesis. This reduction does
not remove any of the antecedents just listed.

### 5.3 From toroidal gluing to a stable slice

Assume $({\rm TCG})_{\Sigma}$ for the corrected component, the two-prime twist, the selected
cusp branch, and the fan of Section 5.1. Book 157 then constructs the finite-type framed joining
datum $({\rm FTJ})_{v_0,Z}$. Its essential outputs are:

- one projective compactification of the global paired-frame space and one smooth projective
  model over the valuation ring of $K_{v_0}$ containing the good interior;
- a relatively ample line extending a power of the global ample line used for the moving
  pencil;
- an identification of the completed selected boundary branch with the normalized framed
  Mumford chart; and
- extension of the chosen tensor-ray point to that branch without changing its completion
  field, valuation shell, Kummer class, enhanced line, sign, or frames.

The relative slicing theorem then produces the weaker stable integral connecting-slice datum
$({\rm ICS})_{v_0,Z}$ needed for (4.8). The resulting curve has a nonempty special-fiber open
$W$ mapping into the good interior and avoiding the closure of $Z$. It also contains a generic
point in the assigned special neighborhood. The entire construction persists when the global
cutting tuple is perturbed in its prescribed congruence class.

Thus the implication actually available is

$$
({\rm IIT})
\Longrightarrow({\rm MPE}),
\qquad
({\rm MPE})+({\rm ACE})
\Longrightarrow({\rm TCG})_{\Sigma}
\Longrightarrow({\rm FTJ})_{v_0,Z}
\Longrightarrow({\rm ICS})_{v_0,Z}.
\tag{5.5}
$$

Book 157 proves every displayed arrow as a conditional implication: $({\rm IIT})$ gives
$({\rm MPE})$; supplied $({\rm MPE})$ and $({\rm ACE})$ give $({\rm TCG})_{\Sigma}$ through
the conditional gluing and normalization argument; and $({\rm TCG})_{\Sigma}$ gives
$({\rm FTJ})_{v_0,Z}$ and then $({\rm ICS})_{v_0,Z}$. It proves neither $({\rm IIT})$ nor
$({\rm ACE})$, so Formula (5.5) is not an unconditional compactification theorem.

### 5.4 The finite-residue distinction

The weaker form of $({\rm ICS})_{v_0,Z}$ requires only that $W$ be nonempty. A closed point of
$W$ may have residue degree greater than one. This is sufficient for integral-open saturation
and for the moving theorem below.

A stronger formulation marks a good $K_{v_0}$-point whose reduction lies in $W$. That form
requires the additional condition

$$
(\mathcal Y^{\mathrm{good}}_{\kappa}
\setminus\overline Z_{\kappa})(\kappa)\ne\varnothing.
\tag{5.6}
$$

Properness of $Z$ does not imply (5.6) over a finite field. The present application uses the
weaker form and therefore does not assume (5.6). If a later use insists on the marked-good-point
version, condition (5.6) must be restored explicitly.

## 6. Constructing the singleton moving presentation

### 6.1 Admissible moving data

An **admissible singleton moving datum** consists of the following information.

1. The corrected paired-frame realization space $U=Y\setminus Z$ of Chapter 2.
2. One singleton place $v_0$ with the data of Section 3.2.
3. A finite family of wholesale-repeatable packets as in Section 3.3.
4. A finite family of flexible split packets as in Section 3.4, including every real place and
   every finite place that is required to split in the generic normal-closure diagram.
5. A positive integer $m_0$ dividing the desired common degree.
6. Normal-sheet requirements obtained by scalar extension from root-sheet conditions in the
   persistence range of Section 3.5.
7. The fan-dependent toroidal gluing hypothesis $({\rm TCG})_{\Sigma}$ of Chapter 5 for the
   selected singleton branch.

All local packets live on the same paired-frame component. Every completion extension, residue
algebra, Kummer parameter, component label, and permitted persistence condition is fixed before
the common degree is chosen.

### 6.2 The common-degree argument

Under $({\rm TCG})_{\Sigma}$, the stable slice at $v_0$ gives (4.8). Hence every sufficiently
large exponent is allowed at the singleton place. At a wholesale-repeatable place, the
norm--Abel calculation gives a sufficiently large arithmetic progression of allowed exponents.
At a flexible split place, the split moving-divisor calculation gives another sufficiently
large progression.

Replace the global ample line by a power whose degree is divisible by the degrees of all
wholesale packets and by $m_0$. The finitely many repeatable and split progressions then have a
common sufficiently large exponent after the compatibility of their residue classes, which is
part of admissibility, has been checked. The singleton place imposes no new residue class.

For that common exponent, choose at each place a reduced local divisor in the required class:
one special point plus an allowed good divisor at $v_0$, complete repeated packets at the
wholesale places, and split divisors in the assigned opens at the flexible places. Approximate
the two pencil sections globally. Simple-root stability preserves every factorwise open and
keeps the unique special root disjoint from the good divisor.

Removing the branch values and the images of the finite complement of the curve open gives a
nonempty open $H\subset\mathbf A_K^N$. The incidence scheme $T$ is geometrically integral and
finite etale over $H$. Its evaluation map lands in $U$, because the complement containing the
boundary failures and $Z$ was removed before the parameter space was fixed.

### 6.3 The conditional construction theorem

**Theorem 6.1 (singleton paired-frame moving presentation).** Let an admissible singleton
moving datum be given. Then there exist an integer $d$ divisible by $m_0$, a nonempty open
$H\subset\mathbf A_K^N$, a geometrically integral finite etale morphism of degree $d$,

$$
\pi:T\longrightarrow H,
\tag{6.1}
$$

and an evaluation map

$$
e:T\longrightarrow U
\tag{6.2}
$$

with the following properties.

1. For every controlled place $v$, there is a parameter $b_v\in H(K_v)$ and a nonempty open
   neighborhood $B_v\subset H(K_v)$ on which the finite etale fiber algebra and all evaluated
   paired-frame conditions are constant in the assigned sense.
2. At $v_0$, the fiber $T_{b_{v_0}}$ has exactly one degree-one factor evaluated in
   $V_{\mathrm{sp}}$; every other factor is reduced, disjoint from it, and good minimal with
   closure specializing into the open $W$ of the stable integral slice.
3. Every wholesale-repeatable fiber is a disjoint union of complete copies of its assigned
   packet. No factor is discarded or repeated independently.
4. Every flexible split fiber is split of degree $d$, and all its sheets evaluate in its
   assigned open. This includes the real, sensitive finite, and certificate packets.
5. Both paired frames, the ordered polarization, the corrected auxiliary level, the arithmetic
   component, and avoidance of $Z$ hold on every evaluated sheet.
6. After passage to the generic normal closure, every top sheet has the scalar extension of
   its root-sheet conditions in the persistence range of Section 3.5. No independently
   prescribed decomposition homomorphism or other exceptional top-fiber behavior is asserted.

**Proof.** Assumption $({\rm TCG})_{\Sigma}$ gives $({\rm FTJ})_{v_0,Z}$ and then the weaker
$({\rm ICS})_{v_0,Z}$ by Book 157's framed joining and stable-slicing reductions. Integral-open
saturation gives (4.8), so the singleton fixed offset is soluble in every sufficiently large
degree. The common-degree construction of Section 6.2 combines that factor with all
wholesale-repeatable and flexible split packets. The curve-and-pencil incidence family gives
(6.1)--(6.2) and properties 1--4.

The evaluation map takes values in the fine paired-frame space, so the two universal frame
identities and the polarization and level structures pull back to every sheet. Removing the
preimage of $Z$ and the finite curve complement gives property 5. For property 6, take the
Galois closure of the generic finite etale algebra. Every top sheet maps to a root sheet after
finite separable extension. The persistence theorem of Book 157 gives precisely the
scalar-extension cases. Equivariant local constancy makes these statements stable after
shrinking the $B_v$. $\square$

The theorem is a genuine construction from its stated hypotheses. Its conditional status is
concentrated in $({\rm TCG})_{\Sigma}$ and the separate arithmetic packet hypotheses. The
normalization and fan results of Book 157 do not remove $({\rm IIT})$, $({\rm ACE})$, or their
constituent requirements.

### 6.4 What the theorem proves unconditionally

Several implications used in Theorem 6.1 do not depend on the missing toroidal gluing theorem.
The corrected paired-frame interior is already smooth and geometrically connected. All five
kinds of point-centered local open are already constructed in their stated ranges. Paired-frame
Kummer normalization, the refined equivariant fan, finite-field Bertini, stable relative
slicing inside a supplied model, persistence under finite extension, and equivariant local
constancy are also available.

What remains conditional is the existence of the projective finite-type model that joins the
good interior to the normalized selected cusp branch with its universal object and ample line.
Without that model the stable slice cannot be inserted into the global coefficient space, so
integral-open saturation cannot be invoked on the curve actually chosen by the moving proof.
Consequently the singleton presentation itself remains conditional.

## 7. The generic normal closure

### 7.1 The Galois top and its root quotient

Let $F=K(H)$ and $L=K(T)$. Since $T/H$ is geometrically integral and finite etale, $L/F$ is a
finite separable field extension of degree $d$. Let $E^{\mathrm{gal}}/F$ be its normal closure
and put

$$
G=\operatorname{Gal}(E^{\mathrm{gal}}/F),
\qquad
J=\operatorname{Gal}(E^{\mathrm{gal}}/L).
\tag{7.1}
$$

The subgroup $J$ is core-free. Indeed, the fixed field of the core of $J$ is the compositum of
all conjugates of $L$, which is $E^{\mathrm{gal}}$ by definition. Thus the action of $G$ on
$G/J$ is faithful and the root quotient remembers the entire generic normal closure.

Normalize $H$ in $E^{\mathrm{gal}}$. Since $H$ is smooth and $T/H$ is finite etale, the
Galois closure in the finite etale category gives, after replacing $H$ by a nonempty open if
necessary, a finite etale $G$-cover

$$
\widetilde T\longrightarrow H
\tag{7.2}
$$

with

$$
T\simeq\widetilde T/J.
\tag{7.3}
$$

The evaluation map on $T$ pulls back to $\widetilde T$. Equations (7.1)--(7.3) are the generic
normal-closure control attached to the moving presentation; they are fixed before any global
parameter is selected.

### 7.2 Propagation of the local conditions

Fix a controlled place $v$ and a local parameter $b_v$. The finite $G$-scheme
$\widetilde T_{b_v}$ determines, up to conjugacy, a local homomorphism

$$
\phi_v:G_{K_v}\longrightarrow G.
\tag{7.4}
$$

Its action on $G/J$ recovers the root algebra $T_{b_v}$. Its regular action on $G$ records the
top local algebra, and its action on every $G/H'$ records the local algebra of every
intermediate fixed field.

For a top sheet lying above a field factor $E_{v,i}$ of the root algebra, the evaluated point is
the scalar extension of the selected point in $U(E_{v,i})$. Therefore the following data
restrict to the top sheet without a new existence theorem:

- the two paired-frame isomorphisms and their determinant identities;
- the ordered polarization and auxiliary level;
- good, ordinary, local--local, semistable, toric-rank, and finite-flat properties in the
  persistence ranges of Book 157;
- membership in the chosen arithmetic component; and
- avoidance of $Z$.

After shrinking $B_v$, the $G$-scheme $\widetilde T_h$ and all its evaluated points are
equivariantly locally constant for $h\in B_v$. Thus the whole local fixed-field diagram, not
only the factorization type of $T_h$, is retained.

### 7.3 Exact conditions that do not propagate formally

Finite extension can change arithmetic information. A nonsplit torus may become split, a
nonzero Kummer class may become zero, and normalized valuations are multiplied by ramification
indices. A frame defined only after a proper extension of $K_v$ does not descend to $K_v$.

Accordingly Theorem 6.1 does not assert any of the following:

$$
\begin{array}{c}
\text{a prescribed decomposition homomorphism not arising from the chosen packet},\\
\text{persistence of nonsplitness},\\
\text{persistence of a nonzero Kummer class},\\
\text{an unchanged normalized valuation},\\
\text{or descent of a frame to a smaller completion.}
\end{array}
\tag{7.5}
$$

This distinction is why the theorem confines normal sheets to the stated persistence range.
Any item in (7.5) requires a separate existence theorem for a presentation with that actual
top-fiber behavior.

## 8. Normal-closure avoidance

### 8.1 The avoidance field

Let $D/K$ be a finite Galois extension containing every field whose intersection with a future
normal closure must be trivial. It may include the kernel fields of the two residual systems,
component and descent fields, and any finite auxiliary field whose disjointness is required.
The field $D$ is chosen before the certificate places and before the moving presentation.

Disjointness from $D$ at the root-field level is insufficient. A nonnormal root field can be
disjoint from $D$ while its normal closure contains a subfield of $D$. The generic top
(7.2), rather than the root cover alone, must therefore remain connected after base change to
$D$.

### 8.2 The constant-field obstruction

Let $C$ be the algebraic closure of $K$ in $E^{\mathrm{gal}}$. Because
$E^{\mathrm{gal}}/K(H)$ is normal, $C/K$ is Galois. The cover $\widetilde T/H$ is geometrically
connected exactly when $C=K$. Geometric integrality of the root cover $T$ does not force this:
a regular nonnormal extension can acquire constants in its Galois closure.

For avoidance of the fixed field $D$, the necessary generic condition is the weaker equality

$$
C\cap D=K.
\tag{8.1}
$$

Under (8.1), the function field of the top cover and $D(H)$ are linearly disjoint over $K(H)$.
Hence

$$
\widetilde T_D=\widetilde T\times_KD
\tag{8.2}
$$

is connected. Connectedness of a future specialization of both (7.2) and (8.2) would then give
closure-level disjointness. This book exports those two connected-cover conditions but does not
choose the specialization.

### 8.3 Split certificate packets

Condition (8.1) can be certified without computing $C$. Suppose finite places

$$
v_1,\ldots,v_t
\tag{8.3}
$$

are unramified in $D$, their Frobenius conjugacy classes normally generate
$\operatorname{Gal}(D/K)$, and each is included among the flexible split packets of the moving
datum. Thus the incidence fiber at every $v_i$ is split and all its sheets lie in the assigned
paired-frame open.

**Lemma 8.1 (split certificate for the constant field).** Under these hypotheses, the constant
field of the generic Galois closure satisfies (8.1).

**Proof.** Since the root fiber at $v_i$ is split, the local Galois action on the sheet set
$G/J$ is trivial. This action is faithful because $J$ is core-free. Hence the local action on
$G$ is trivial and $v_i$ splits completely in $C/K$.

Put $I=C\cap D$. The image in $\operatorname{Gal}(I/K)$ of the Frobenius class at every
$v_i$ is trivial. But those classes normally generate $\operatorname{Gal}(D/K)$, so their
images normally generate every quotient, including $\operatorname{Gal}(I/K)$. Therefore that
quotient is trivial and $I=K$. $\square$

The lemma is an implication from a supplied certificate set. The existence and selection of
places satisfying (8.3) is a separate prime-selection input. Once such places have been
supplied, their local moduli points are flexible split packets at sufficiently large
good primes, and Theorem 6.1 incorporates them into the same presentation.

### 8.4 The closure-level avoidance datum

The correct order of construction is

$$
U,D;
\quad
\{v_i\}_{i=1}^t;
\quad
\text{one presentation containing the split certificate fibers};
\quad
E^{\mathrm{gal}},C.
\tag{8.4}
$$

Lemma 8.1 then proves (8.1). Reversing this order is invalid: choosing a root field first and
taking its normal closure afterward gives no reason for that closure to avoid $D$.

The exported avoidance datum is therefore

$$
\widetilde T\longrightarrow H,
\qquad
\widetilde T_D\longrightarrow H_D,
\tag{8.5}
$$

both connected, together with the core-free quotient $T=\widetilde T/J$ and the equivariant
local neighborhoods. A later Hilbert specialization may impose connectedness of both fibers in
one parameter. No such parameter is asserted here.

## 9. The complete export package

### 9.1 The moving presentation

Under the hypotheses of Theorem 6.1, the primary output is

$$
\boxed{
H\subset\mathbf A_K^N,
\quad
T\xrightarrow{\mathrm{finite\ etale}}H,
\quad
e:T\longrightarrow U,
\quad
\deg(T/H)=d\equiv0\pmod{m_0}.}
\tag{9.1}
$$

The scheme $T$ is geometrically integral. Every local fiber lies in one of the prescribed
packet classes, and the singleton fiber has exactly one special factor and an allowed good
complement. Pullback of the universal family on $U$ gives a family on $T$ with both exact paired
frames.

### 9.2 The local equivariant data

The generic Galois closure adds

$$
\widetilde T\longrightarrow H,
\qquad
G,
\qquad
J\le G,
\qquad
T=\widetilde T/J,
\tag{9.2}
$$

where $J$ is core-free. At each controlled place, a local parameter and its neighborhood retain
the $G$-torsor, every quotient algebra, and all evaluated moduli conditions. At certificate
places the top fiber is split. At nonsplit places the theorem asserts exactly the
scalar-extension behavior in the persistence range of Section 3.5.

If the certificate hypotheses of Lemma 8.1 are included, the package also contains the two
connected covers in (8.5). This is the normal-closure avoidance input needed by a later
specialization theorem.

### 9.3 The conditional application theorem

**Theorem 9.1 (moduli package for the singleton potential-modularity construction).** Fix the
two determinant-compatible residual systems, the corrected Hilbert--Blumenthal tensor datum,
the local packet ledger, the proper closed subset $Z$, a degree divisor $m_0$, and a finite
Galois avoidance field $D/K$. Assume:

1. every local seed lies in the exact range of Book 157 and all completion extensions are
   recorded;
2. the nonsingleton exact packets are wholesale-repeatable;
3. the split packets, including the real and certificate packets, are flexible;
4. every normal-sheet requirement is obtained by scalar extension from a root-sheet condition
   in the persistence range of Section 3.5;
5. the residue-class progressions of the repeatable packets are compatible with the degree
   divisor $m_0$;
6. the fan-dependent framed toroidal gluing theorem $({\rm TCG})_{\Sigma}$ holds for the
   selected singleton branch; concretely, retain $({\rm IIT})$, the resulting conditional
   $({\rm MPE})$, and the full $({\rm ACE})$ package, including $({\rm BCP})$,
   $({\rm AEC}_0)$, $({\rm RCD})$, $({\rm TDC})$, and the algebraized overlap relation, exactly
   as stated in Chapter 5; and
7. the supplied split certificate Frobenius classes normally generate
   $\operatorname{Gal}(D/K)$.

Then the moving presentation (9.1), the core-free normal-closure diagram (9.2), the equivariant
local neighborhoods, and the connected avoidance pair (8.5) are constructed. The presentation
has repeatability, flexibility, both paired frames, exactly one special factor at $v_0$, good
minimal complementary factors, realized normal sheets, normal-closure control, and avoidance of
$Z$ and $D$ in the precise generic senses above.

**Proof.** Theorem 6.1 constructs (9.1) from hypotheses 1--6. Chapter 7 constructs (9.2) and
proves the root quotient core-free. Equivariant local constancy gives the local normal-sheet
diagram. Hypothesis 7 and Lemma 8.1 give $C\cap D=K$, hence connectedness after base change to
$D$. These are exactly the asserted outputs. $\square$

The theorem deliberately keeps hypothesis 6 visible. The paired-frame normalization and fan
are proved, but the complete toroidal joining theorem is not. Therefore Theorem 9.1 does not
give an unconditional singleton presentation from the current geometric sources.

### 9.4 Sharp exclusions

The output of Theorem 9.1 is a family over an affine parameter space, not a selected arithmetic
fiber. In particular it does not produce:

- a $K$-rational parameter of $H$;
- a finite totally real point field or a Galois top field;
- an abelian variety over such a field;
- an automorphic auxiliary system or automorphic starting datum;
- a comparison with a characteristic-zero lift; or
- any modularity or descent conclusion.

If a later arithmetic theorem supplies a parameter whose root and top fibers are connected and
which lies in every local neighborhood, then evaluation produces the expected specialized
Hilbert--Blumenthal object. That is a conditional interpretation of a future fiber, not an
existence assertion of this book.

The theorem also makes no claim for dyadic coefficient primes, externally fixed polarization
classes outside the corrected tensor range, incompatible tensor-Tate Kummer classes, or an
unramified-only frame that is known only after ramified extension. The literal marked-good-point
slice requires (5.6), although the weaker slice used here does not. Finally, the normal-closure
diagram does not make its sheet stabilizer solvable; any solvable-bridge demand is an additional
group-theoretic condition on the chosen presentation.

## 10. Conclusion

The potential-modularity moduli problem has one geometric center: a corrected fine
Hilbert--Blumenthal space on which two residual systems occur as determinant-compatible paired
torsion frames of one universal abelian scheme. Its smoothness, product monodromy, component
control, local seeds, and point-centered opens are supplied by the preceding two books.

Turning those opens into one moving family is subtler. Wholesale-repeatable packets and
flexible split packets can be synchronized in high degree. A singleton special factor carries
a fixed Abel-class offset, so high divisibility alone does not help. A stable integral slice
with a dense allowed-good special-fiber open removes that offset by representing every
Jacobian class with a good divisor.

Book 157 proves the framed Kummer normalization, the refined equivariant fan, the complete-trait
inverse, the Mumford-side completed ring, and stable slicing inside a supplied joining model.
The missing bridge is the full framed toroidal gluing theorem. Its exact antecedents are
infinitesimal toroidal recognition, relative Mumford--PEL equivalence, bounded conductor and
single-chart effectivity, ramified conductor descent, and theta--determinant compatibility.
The singleton presentation remains conditional on that package and on the separate
repeatability, flexibility, and persistence-range normal-sheet hypotheses.

Under those hypotheses, the construction yields one geometrically integral finite etale moving
family with both frames, one special factor, good complementary sheets, prescribed divisibility,
and avoidance of the chosen closed locus. Its generic Galois closure gives a core-free top
diagram. Split certificate packets force the constant field of that top to be disjoint from the
chosen avoidance field, so closure-level avoidance is present before specialization.

That is the exact endpoint: a linear, condition-correct moduli presentation ready for arithmetic
specialization. No global fiber or arithmetic conclusion is asserted before such a
specialization is separately supplied.
