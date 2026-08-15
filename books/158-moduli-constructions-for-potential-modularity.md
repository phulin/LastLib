# Moduli Constructions for Potential Modularity

## Contents

1. [The exact FLT interface](#1-the-exact-flt-interface)
2. [The paired-frame realization space](#2-the-paired-frame-realization-space)
3. [The local-open datum](#3-the-local-open-datum)
4. [A regular symmetric moving presentation](#4-a-regular-symmetric-moving-presentation)
5. [The Galois-refined specialization](#5-the-galois-refined-specialization)
6. [The specialized Hilbert--Blumenthal object](#6-the-specialized-hilbert--blumenthal-object)
7. [Handoff to potential modularity](#7-handoff-to-potential-modularity)
8. [Scope and boundaries](#8-scope-and-boundaries)
9. [Conclusion](#9-conclusion)

## 1. The exact FLT interface

The FLT blueprint uses Hilbert--Blumenthal geometry for one bounded purpose.  Given a
rank-two residual representation in characteristic $\ell$ and a separately constructed
dihedral residual representation in an auxiliary odd characteristic $q$, it needs one
abelian variety with real multiplication on which both representations occur as paired
torsion modules.  The field of definition must be totally real, preserve the relevant finite
images, and support the local conditions used by the selected modularity-lifting theorem.

The later compatible-family construction additionally requires potential modularity, Brauer
induction, solvable base change, local--global compatibility, and stable lattices.  The moduli
construction supplies only the potential-modularity field and the two-prime geometric object.
It does not supply the automorphic or lattice parts of that arithmetic construction.

This division of labor is important.  The blueprint does not require a local cycle with
exactly one semistable factor, a compactification of the Hilbert--Blumenthal space, or a
several-parameter family joining a cusp to a good-reduction locus.  Those are useful in
stronger controlled-seed constructions, but they are not antecedents of the split
Moret--Bailly step used here.

The geometric chain proved in this book is

$$
\begin{gathered}
\text{fine connected two-prime twist with simultaneous local opens}\\
\Longrightarrow
\text{regular }S_d\text{-moving presentation}\\
\Longrightarrow
\text{totally real Galois top, disjoint from a prescribed finite field}\\
\Longrightarrow
\text{one Hilbert--Blumenthal object carrying both residual systems}.
\end{gathered}
\tag{1.1}
$$

No boundary compactification occurs in (1.1).

## 2. The paired-frame realization space

Let $K$ be a totally real number field.  Let $E$ be a totally real coefficient field,
and let $\mathfrak p$ and $\mathfrak q$ be distinct monodromy-admissible primes of $E$
above distinct odd rational primes $\ell$ and $q$.  Fix rank-two finite Galois modules

$$
V_{\mathfrak p},\qquad V_{\mathfrak q}
\tag{2.1}
$$

over their residue fields.  Each is supplied with a chosen determinant identification with
the cyclotomic coefficient line.  An equality of determinant characters without an actual
identification is not enough to define the paired-frame twist.

Choose the ordered polarization module, PEL lattice, and neat auxiliary level in the corrected
tensor range of Books 156--157.  Book 156, Theorem 12.1 constructs the fine two-prime
paired-frame cover.  Its Theorem 11.2 and Corollary 11.3 give full product geometric monodromy
and geometric connectedness on the selected determinant-compatible twist.  Book 157,
Proposition 3.2 supplies a component defined over the working field in the corrected tensor
range.

Write the resulting twist as $Y$.  It is a smooth quasi-projective geometrically connected
$K$-scheme of positive dimension, and it carries a universal Hilbert--Blumenthal abelian
scheme

$$
\mathcal A\longrightarrow Y
\tag{2.2}
$$

with real multiplication, ordered polarization, auxiliary neat level, and universal paired
frames

$$
V_{\mathfrak p}\simeq \mathcal A[\mathfrak p],
\qquad
V_{\mathfrak q}\simeq \mathcal A[\mathfrak q].
\tag{2.3}
$$

The two frames live on the same object.  A product of two independently twisted moduli spaces
would not imply (2.3), and separate surjectivity to the two special-linear monodromy factors
would not imply that $Y$ is geometrically connected.

**Theorem 2.1 (paired interior package).**  Under the determinant, component, neat-level, and
monodromy hypotheses just stated, the scheme $Y$ and universal tuple (2.2)--(2.3) exist and
have the asserted fineness, smoothness, quasi-projectivity, and geometric connectedness.

**Proof.**  Representability and the universal tuple are Book 156, Theorems 4.2 and 12.1.
Determinant compatibility is Book 156, Proposition 8.1.  Full simultaneous monodromy and
geometric connectedness are Book 156, Theorem 11.2 and Corollary 11.3.  The corrected tensor
component and its arithmetic descent are Book 157, Propositions 3.1--3.2.  These are interior
statements; none invokes a compactification. $\square$

## 3. The local-open datum

Let $S$ be a finite set of places of $K$, containing every real place and every finite
place at which a local condition must be retained.  A **split FLT local datum** on $Y$
consists, for each $v\in S$, of one point

$$
y_v\in Y(K_v)
\tag{3.1}
$$

which simultaneously realizes both frames and every required local model.  At a finite place
this may be a good, ordinary, local--local finite-flat, or tensor-Tate semistable point in the
range of Book 157, Theorem 13.1.  At a real place it is a point on the chosen orientation
component realizing both odd involutions.

The word *simultaneously* is essential.  A target frame on one local abelian variety and an
auxiliary frame on another do not define an intersecting pair of conditions on $Y(K_v)$.
Likewise, residual finite flatness does not by itself produce the named coefficient-linear
finite locally free group scheme required by a lifting problem; that exact model belongs to
the datum.

Book 157, Theorem 13.1 and Corollary 13.2 give a point-centered nonempty open

$$
\Omega_v\subset Y(K_v)
\tag{3.2}
$$

on which the chosen condition, the component, the level, and both paired frames persist.  The
split datum requires (3.1) over $K_v$ itself.  If a seed exists only after a nontrivial
extension of $K_v$, one has an exact-local-algebra problem of Book 154, Theorem 7.1; the
common moving-presentation hypothesis in that theorem must then be verified separately.  The
FLT route treated here uses the split form and does not need that stronger assertion.

Let $Z\subsetneq Y$ be a proper closed locus to be avoided.  Shrink around a simultaneous
witness so that

$$
\Omega_v\subset U(K_v),
\qquad U=Y\setminus Z.
\tag{3.3}
$$

The variety $U$ remains smooth and geometrically connected.

**Theorem 3.1 (FLT local-open package).**  In the unramified odd-prime and corrected tensor
ranges of Book 157, every split FLT local datum gives the opens (3.2)--(3.3).  The exact
finite-flat model, ordinary or local--local type, semistable toric rank, splitness, Kummer
class, component, level, and frames persist precisely to the extent stated in Book 157,
Theorems 10.2, 12.1, and 13.1.

This theorem makes no assertion for a dyadic coefficient prime, incompatible tensor-Tate
Kummer classes, an externally fixed polarization class outside the corrected tensor range, or
a frame known only over a forbidden ramified extension.

## 4. A regular symmetric moving presentation

Ordinary Moret--Bailly approximation gives a root field.  The compatible-family construction
benefits from retaining its Galois closure before specialization, so that the closure can be
made disjoint from every residual cutout field.  The needed refinement is available for split
local opens without any boundary geometry.

**Lemma 4.1 (regular symmetric split presentation).**  Let $X/K$ be a smooth
quasi-projective geometrically connected variety of positive dimension, and let
$\Omega_v\subset X(K_v)$ be nonempty opens at finitely many places.  There are an integer
$d\ge2$, a nonempty open $H\subset\mathbf A^1_K$, a geometrically integral finite etale
cover

$$
T\longrightarrow H
\tag{4.1}
$$

of degree $d$, and an evaluation map $e:T\to X$, with the following properties.

1. At every controlled place there is $b_v\in H(K_v)$ such that $T_{b_v}$ is split and
   every evaluated sheet lies in $\Omega_v$.  This remains true in a neighborhood of
   $b_v$.
2. The generic normal closure $\widetilde T\to H$ is geometrically connected and has group
   $S_d$.
3. If $J=S_{d-1}$ is a point stabilizer, then $T=\widetilde T/J$, and $J$ is core-free.

**Proof.**  Follow Book 154, Lemma 5.2.  Slice $X$ by sufficiently positive general
hyperplanes to obtain a smooth projective geometrically integral curve $C$ whose open
embedded part meets every $\Omega_v$.  On $C$, the norm--Abel argument of that lemma gives,
for one sufficiently large common degree, split reduced divisors supported in all the local
opens.  Choose the degree also large enough that the relevant line bundle separates every
subscheme of length at most four.

Pairs of global sections near the local divisor pairs form open boxes in a finite-dimensional
coefficient space.  Basepoint freeness, avoidance of the finite complement of the embedded
curve, simple ramification, and distinct branch values are Zariski-open conditions on this
space.  The last two conditions are nonempty in characteristic zero: length-three separation
shows that higher ramification imposes an additional independent jet equation, and two
ramification points having the same image imposes another independent incidence equation.
Equivalently, this is the general simply-branched projection theorem for a smooth curve.  The
monodromy calculation is the one proved in Book 153, Section 8.4.  Every finite branch inertia
group is generated by a transposition; connectedness of $C$ makes the action transitive; and
a transitive group generated by transpositions is $S_d$.

Weak approximation in the coefficient space chooses one global pair in the local boxes and
outside all the bad Zariski-closed loci.  It defines a simply branched finite map

$$
f:C\longrightarrow\mathbf P^1_K.
$$

Remove the branch values and the images of the finite curve complement.  The remaining
restriction is (4.1), and simple-root stability gives item 1.  The geometric monodromy is
$S_d$, hence the arithmetic monodromy is also $S_d$ and the normal closure has no enlarged
constant field.  The natural action of $S_d$ on its $d$ sheets identifies the root cover
with the quotient by $S_{d-1}$.  The intersection of all conjugates of a point stabilizer is
trivial, proving core-freeness.  At a local parameter where all root sheets are rational, the
local specialization homomorphism acts trivially on $S_d/S_{d-1}$.  Faithfulness of this
core-free action forces that homomorphism to be trivial, so the normal-top fiber is split as
well. $\square$

The lemma does not claim that $S_{d-1}$ is solvable.  It need not be when the divisor degree
forced by the local Abel problems is large.  No solvable bridge is needed for the geometric
handoff below: potential modularity is established directly after base change to the Galois
top.  Any argument that instead transports automorphy from the root field to the top must add
the appropriate solvable-base-change hypothesis.

## 5. The Galois-refined specialization

Let $D/K$ be a finite Galois field containing all residual cutout, cyclotomic, pairing,
component, and self-twist fields whose intersection would damage the later argument.  Apply
Lemma 4.1 to $U$ and the opens $\Omega_v$.  Its normal closure gives a Galois
approximation datum in the sense of Book 155, Chapter 6.  Geometric connectedness of
$\widetilde T$ makes its function field regular over $K$, so the base-changed top remains
connected over $D$.

**Theorem 5.1 (Galois-refined paired specialization).**  From the data of Chapters 2--3 and
the avoidance field $D$, there exist fields

$$
K\subset L\subset M,
\tag{5.1}
$$

and a point $x\in U(L)$ such that:

1. $M/K$ is Galois, totally real, and linearly disjoint from $D/K$;
2. $\operatorname{Gal}(M/K)\simeq S_d$, $L=M^{S_{d-1}}$, and $M$ is the normal closure
   of $L/K$;
3. every $v\in S$ splits completely in both $M$ and $L$;
4. every localized conjugate of $x$ evaluates in $\Omega_v$; and
5. after base change, $x_M\in U(M)$ has the same local property at every place of $M$
   above $v$.

If $K=\mathbf Q$, then $M/\mathbf Q$ is the totally real Galois field demanded in the FLT
blueprint.  Since $d\ge2$, its degree is even.

**Proof.**  Apply Book 155, Theorem 7.1 to the datum of Lemma 4.1, including connectedness
after base change to $D$ among the Hilbert conditions.  Prescribe the trivial local
homomorphism at each finite controlled place and at every real place.  Lemma 4.1 supplies the
required split local top fibers.  Book 155, Theorem 8.1 makes the specialized top and all its
subfields totally real; Corollary 8.2 gives complete splitting; and Theorem 7.1 gives
closure-level disjointness, the fixed-field description, and the evaluated point.  Complete
splitting identifies each completion with $K_v$, so the open conditions propagate to every
place above $v$. $\square$

It would be incorrect to apply ordinary Moret--Bailly and assert afterward that the normal
closure is disjoint from $D$.  The normal closure is retained in the regular moving family
before specialization; that is exactly what makes clause 1 a Hilbert condition.

## 6. The specialized Hilbert--Blumenthal object

Pull back the universal tuple (2.2)--(2.3) along $x$.  This gives an abelian variety
$A/L$ with real multiplication and

$$
V_{\mathfrak p}|_{G_L}\simeq A[\mathfrak p],
\qquad
V_{\mathfrak q}|_{G_L}\simeq A[\mathfrak q]
\tag{6.1}
$$

as paired Galois modules.  Base change to $M$ gives

$$
V_{\mathfrak p}|_{G_M}\simeq A_M[\mathfrak p],
\qquad
V_{\mathfrak q}|_{G_M}\simeq A_M[\mathfrak q].
\tag{6.2}
$$

Because $M\cap D=K$, every finite image whose cutout field was placed in $D$ is preserved
under restriction to $G_M$.  This is the elementary image-preservation lemma recorded in
Book 155, Lemma 2.5.  In particular, the target and auxiliary residual irreducibility or
adequacy condition is preserved whenever its detecting field was included in $D$.

At every controlled finite place, complete splitting and membership in $\Omega_v$ retain
the named local finite-flat or semistable model.  At every real place all embeddings of $M$
land in the selected real component.  No assertion is made about new bad-reduction places of
$A$; those are known only after specialization and must be handled by the later lifting
ledger.

**Corollary 6.1 (geometric potential-modularity handoff).**  Under the hypotheses of Theorem
5.1, the totally real Galois field $M$ and the object $A_M$ satisfy the two-prime geometric,
image-preservation, and preselected local-model clauses needed by the potential-modularity
argument.

This is an existence theorem for the geometric handoff.  It is not an automorphy theorem.

There is a load-bearing consequence in the Frey signed-special specialization. Choose at
$2$ the split Tate neighborhood which realizes the Frey residual frame and the unramified
auxiliary residual $q$-frame. Clause 3 of Theorem 5.1 makes $2$ split completely in
$M$, and clause 5 puts every sheet in that same neighborhood. Hence
$V_{\mathfrak q}(A_M)$ has nonzero rank-one monodromy at every $w\mid2$, while its
dihedral residual automorphic reference is unramified there. Thus

$$
\{w:w\mid2\}\subseteq P_{\mathrm{aux}}(A_M).                \tag{6.3}
$$

When $K=\mathbf Q$, complete splitting gives
$\#\{w:w\mid2\}=[M:\mathbf Q]\ge2$. The split construction therefore cannot satisfy a
singleton active-place hypothesis. This is not a defect in Theorem 5.1: it is the finite-set
arithmetic problem which the split geometry deliberately leaves to modularity lifting.

## 7. Handoff to potential modularity

For the FLT route under consideration, the remaining steps after Corollary 6.1 are arithmetic.

1. Construct the auxiliary characteristic-$q$ representation so that its restriction to
   $G_M$ is modular, normally by automorphic induction from a character.  Disjointness from
   its quadratic and character cutout fields must be included in $D$.
2. Apply the selected modularity-lifting theorem over $M$ to the $q$-adic Tate factor of
   $A_M$, with every actual local condition and every new bad place checked. In the Frey
   signed-special case (6.3) rules out the one-place theorem. One must supply an exact
   finite-set modularity-lifting result for the actual set $P_{\mathrm{aux}}(A_M)$: a constructed
   direct $(\mathrm{IAV}_S)$ comparison, a fully reverified ordered chain, the all-point
   hypotheses of a suitable finite-set theorem, or the actual-cube, simultaneous-branch,
   reciprocity, and pointed occurrence hypotheses of a simultaneous theorem.
3. Read the same automorphic packet at $\mathfrak p$ and identify its residual member with
   the target representation by (6.2).
4. For the compatible-family construction, carry the resulting potential automorphy through Brauer
   induction, solvable base change on the elementary fixed-field towers, local--global
   compatibility, and stable lattices.

Corollary 6.1 supplies none of steps 1--4 merely by producing $A_M$.  In particular, a smooth
moduli space does not imply that an automorphic Hecke module meets the local deformation
component of the specialized Tate-module point.  That carrier-support problem belongs to the
modularity-lifting books, not to the compactification of the moduli space.

Nor does complete splitting reduce the finite-set problem to one place. It does the opposite
for the Frey Tate condition: it reproduces the same nonminimal special lift at every dyadic
place. Separate one-place occurrence proves none of the finite-set alternatives just listed.
Their actual joint or ordered occurrence assertion remains an arithmetic blocker.

Within the full compatible-family construction, this book contributes only the
potential-automorphy field used to build the automorphic Brauer data. Original-prime Frobenius
comparison, conductor control, and integral models at the other coefficient primes remain
separate arithmetic inputs.

## 8. Scope and boundaries

The following requirements are live in the FLT geometric route and are retained here:

- one fine smooth geometrically connected paired-frame twist;
- one simultaneous local witness for both torsion systems at every controlled place;
- point-centered local opens preserving the exact named integral conditions;
- a totally real specialization;
- a Galois top chosen before specialization;
- disjointness of that top from the full finite avoidance field; and
- the specialized object with both frame identities and image preservation.

The following stronger topics are not used by this route and are not hypotheses of any theorem
in this book:

- a general toroidal compactification of Hilbert--Blumenthal moduli;
- intrinsic recognition of every semiabelic boundary degeneration;
- conductor-root descent and global theta extension across every cusp;
- a finite-type joining model between one cusp branch and the good locus;
- a stable integral connecting slice;
- one exceptional local factor accompanied by good complementary factors; and
- exact normal-sheet conditions not obtained from split local fibers.

The split restriction is deliberate.  If a future argument genuinely needs a nonsplit exact
completion algebra or exactly one exceptional factor, Book 154's common moving-presentation
condition must be proved for that new datum.  Such a future need does not enlarge the FLT
blueprint retroactively.

The Galois-top construction also does not make the root stabilizer solvable.  The FLT route
uses potential modularity directly over $M$.  A proof that first establishes automorphy only
over $L$ and then transports it to $M$ must supply a solvable bridge or reprove automorphy
over $M$.

## 9. Conclusion

The necessary geometry is an interior theorem.  Books 156--157 give one connected fine
two-prime twist and its simultaneous local opens.  The split moving argument of Book 154 can
be chosen simply branched; the symmetric monodromy calculation of Book 153 then makes its
generic Galois closure regular.  Book 155 specializes that closure with total reality,
complete splitting, and closure-level avoidance.  Pullback of the universal family gives one
Hilbert--Blumenthal object carrying both residual systems over the totally real Galois top.

This closes the geometric Moret--Bailly input needed by the blueprint without importing a
general toroidal compactification.  The remaining obstacles are the explicitly arithmetic
ones: construction of the auxiliary automorphic seed, the finite-set modularity-lifting and
carrier-support input for the actual active set (necessarily including
every dyadic place in the Frey split route), and the Brauer/local--global/stable-lattice
assembly of the compatible family.
