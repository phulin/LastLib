# Solvable Base Change and Descent

## Contents

1. [From cyclic steps to solvable transfer](#1-from-cyclic-steps-to-solvable-transfer)
   - [Why iteration is a theorem rather than notation](#11-why-iteration-is-a-theorem-rather-than-notation)
   - [Solvable towers and prime refinements](#12-solvable-towers-and-prime-refinements)
   - [The normalization ledger](#13-the-normalization-ledger)
   - [The admissibility ledger](#14-the-admissibility-ledger)
   - [Existence, uniqueness, cuspidality, and descent](#15-existence-uniqueness-cuspidality-and-descent)
2. [Constructing solvable base change](#2-constructing-solvable-base-change)
   - [Base change of an isobaric representation](#21-base-change-of-an-isobaric-representation)
   - [Induction along a prime cyclic tower](#22-induction-along-a-prime-cyclic-tower)
   - [Transitivity and independence of the tower](#23-transitivity-and-independence-of-the-tower)
   - [Strong multiplicity one as the rigidity input](#24-strong-multiplicity-one-as-the-rigidity-input)
   - [Refinement across the isobaric boundary](#25-refinement-across-the-isobaric-boundary)
   - [Galois invariance of the endpoint](#26-galois-invariance-of-the-endpoint)
3. [The local representation at the top](#3-the-local-representation-at-the-top)
   - [One place, all paths](#31-one-place-all-paths)
   - [Split, inert, and decomposed finite places](#32-split-inert-and-decomposed-finite-places)
   - [Ramified places, monodromy, and conductors](#33-ramified-places-monodromy-and-conductors)
   - [Archimedean places](#34-archimedean-places)
   - [Local factors and the tower law](#35-local-factors-and-the-tower-law)
   - [Decomposition groups and solvable local towers](#36-decomposition-groups-and-solvable-local-towers)
4. [Norm characters, twists, and central characters](#4-norm-characters-twists-and-central-characters)
   - [The character group at one step](#41-the-character-group-at-one-step)
   - [The endpoint group in the Galois case](#42-the-endpoint-group-in-the-galois-case)
   - [Twists, contragredients, and centers](#43-twists-contragredients-and-centers)
   - [Fixed-central-character refinements](#44-fixed-central-character-refinements)
   - [How stepwise characters assemble](#45-how-stepwise-characters-assemble)
   - [Counting fixed-center fibers](#46-counting-fixed-center-fibers)
5. [Cuspidality and its precise failure](#5-cuspidality-and-its-precise-failure)
   - [The first bad step](#51-the-first-bad-step)
   - [Quadratic self-twists and automorphic induction](#52-quadratic-self-twists-and-automorphic-induction)
   - [The exact solvable criterion is stepwise](#53-the-exact-solvable-criterion-is-stepwise)
   - [Bottom-field self-twists and the projective exception](#54-bottom-field-self-twists-and-the-projective-exception)
   - [Isobaric decomposition and stabilizers](#55-isobaric-decomposition-and-stabilizers)
   - [Odd order and the location of quadratic steps](#56-odd-order-and-the-location-of-quadratic-steps)
6. [Compatibility with automorphic induction](#6-compatibility-with-automorphic-induction)
   - [Restriction after induction](#61-restriction-after-induction)
   - [Proof of the commuting formula](#62-proof-of-the-commuting-formula)
   - [Cuspidality in the disjoint and contained cases](#63-cuspidality-in-the-disjoint-and-contained-cases)
   - [Iteration through solvable towers](#64-iteration-through-solvable-towers)
   - [Conductors, weights, and twists under the comparison](#65-conductors-weights-and-twists-under-the-comparison)
7. [Descent through one cyclic step](#7-descent-through-one-cyclic-step)
   - [Invariance is the admissible image condition for a cusp form](#71-invariance-is-the-admissible-image-condition-for-a-cusp-form)
   - [Descent of the central character](#72-descent-of-the-central-character)
   - [Fibers and the exact twisting group](#73-fibers-and-the-exact-twisting-group)
   - [Descent of a two-character isobaric sum](#74-descent-of-a-two-character-isobaric-sum)
   - [What the cyclic theorem does and does not guarantee](#75-what-the-cyclic-theorem-does-and-does-not-guarantee)
   - [Existence, uniqueness, and a prescribed descent datum](#76-existence-uniqueness-and-a-prescribed-descent-datum)
8. [Solvable descent and its obstructions](#8-solvable-descent-and-its-obstructions)
   - [The recursive descent criterion](#81-the-recursive-descent-criterion)
   - [The fixed-point obstruction on a descent torsor](#82-the-fixed-point-obstruction-on-a-descent-torsor)
   - [Parameter extension and the projective obstruction](#83-parameter-extension-and-the-projective-obstruction)
   - [Twisting ambiguity after full descent](#84-twisting-ambiguity-after-full-descent)
   - [Tower dependence of the criterion, not of the answer](#85-tower-dependence-of-the-criterion-not-of-the-answer)
   - [Prime-step cohomology in concrete cases](#86-prime-step-cohomology-in-concrete-cases)
   - [Central characters inside the obstruction calculation](#87-central-characters-inside-the-obstruction-calculation)
   - [A finite descent protocol](#88-a-finite-descent-protocol)
9. [Local-to-global rigidity in recognition and descent](#9-local-to-global-rigidity-in-recognition-and-descent)
   - [Recognizing an ascent at good places](#91-recognizing-an-ascent-at-good-places)
   - [Recovering bad local components](#92-recovering-bad-local-components)
   - [Why separate local invariance is insufficient](#93-why-separate-local-invariance-is-insufficient)
   - [Density, conjugation, and Galois invariance](#94-density-conjugation-and-galois-invariance)
   - [The Rankin--Selberg reason for rigidity](#95-the-rankin--selberg-reason-for-rigidity)
10. [Arithmetic and representation-theoretic compatibilities](#10-arithmetic-and-representation-theoretic-compatibilities)
    - [Conductors, levels, and newvectors](#101-conductors-levels-and-newvectors)
    - [Algebraic and cohomological weights](#102-algebraic-and-cohomological-weights)
    - [Algebraic conjugation and rationality fields](#103-algebraic-conjugation-and-rationality-fields)
    - [Local types and normalized induction](#104-local-types-and-normalized-induction)
    - [Standard factors and contragredients](#105-standard-factors-and-contragredients)
    - [Three conductor profiles](#106-three-conductor-profiles)
11. [Compatibility with Jacquet--Langlands](#11-compatibility-with-jacquet--langlands)
    - [Scalar extension of the inner form](#111-scalar-extension-of-the-inner-form)
    - [The commuting square](#112-the-commuting-square)
    - [The isobaric boundary](#113-the-isobaric-boundary)
    - [Descent on an inner form](#114-descent-on-an-inner-form)
12. [Four solvable patterns and one local calculation](#12-four-solvable-patterns-and-one-local-calculation)
    - [A quadratic--cubic tower](#121-a-quadratic--cubic-tower)
    - [An $S_3$-extension](#122-an-s_3-extension)
    - [An $A_4$-extension](#123-an-a_4-extension)
    - [A biquadratic extension](#124-a-biquadratic-extension)
    - [One place through a decomposed ramified tower](#125-one-place-through-a-decomposed-ramified-tower)
13. [Totally real ascent and descent in modularity arguments](#13-totally-real-ascent-and-descent-in-modularity-arguments)
    - [Why totally real towers are especially clean at infinity](#131-why-totally-real-towers-are-especially-clean-at-infinity)
    - [The automorphic ascent criterion](#132-the-automorphic-ascent-criterion)
    - [Descent selected by an extending arithmetic representation](#133-descent-selected-by-an-extending-arithmetic-representation)
    - [A practical solvable modularity descent theorem](#134-a-practical-solvable-modularity-descent-theorem)
    - [Local conditions in ascent and descent](#135-local-conditions-in-ascent-and-descent)
    - [Descent from automorphic data alone](#136-descent-from-automorphic-data-alone)
14. [The final theorem package](#14-the-final-theorem-package)
    - [Solvable base change: existence and normalization](#141-solvable-base-change-existence-and-normalization)
    - [Cuspidality, isobaric failure, and fibers](#142-cuspidality-isobaric-failure-and-fibers)
    - [Solvable descent: existence and obstruction](#143-solvable-descent-existence-and-obstruction)
    - [Totally real and inner-form refinements](#144-totally-real-and-inner-form-refinements)
    - [Failure modes at a glance](#145-failure-modes-at-a-glance)
15. [Conclusion: one canonical ascent, compatible choices downward](#15-conclusion-one-canonical-ascent-compatible-choices-downward)

## 1. From cyclic steps to solvable transfer

### 1.1 Why iteration is a theorem rather than notation

Cyclic base change solves one indivisible transfer problem. If $L/K$ is cyclic and
$\pi$ is cuspidal automorphic on $\mathrm{GL}_2(\mathbb A_K)$, it constructs an
automorphic isobaric representation $\operatorname{BC}_{L/K}(\pi)$ whose local
parameters are obtained by restriction. A solvable extension is built from such
steps, so it is natural to write a string such as

$$
\operatorname{BC}_{F_r/F_{r-1}}\cdots
\operatorname{BC}_{F_1/F_0}(\pi).
$$

That string conceals nearly every issue studied in this book. A cuspidal
representation can cease to be cuspidal at an even step. A different solvable tower
can contain different quadratic layers. Characters trivial after one norm pullback
need not themselves descend through the rest of the tower. An invariant
representation at the top can have many descents at the first step, and only some of
them, or none of them, may be invariant at the next step. Conductors do not transform
by multiplying an ideal by a discriminant, and at an unramified place Satake roots
are raised to a residue degree rather than to the degree of the whole extension.

The purpose of solvable base change is to prove that the upward operation nevertheless
has a canonical endpoint. Its local component is restriction of the original local
parameter all the way to the top field. Transitivity of restriction and strong
multiplicity one then erase the chosen tower. The downward problem is subtler. It is
an existence problem for compatible descent data, with twisting torsors and genuine
cohomological obstructions. We shall develop both directions without allowing the
clean ascent theorem to hide the qualifications required for descent.

The central picture is

$$
\begin{array}{ccccc}
F=F_0&\subset&F_1&\subset\cdots\subset&F_r=E,\\
\pi_0&\longmapsto&\pi_1&\longmapsto\cdots\longmapsto&\pi_r,
\end{array}
$$

where every $F_i/F_{i-1}$ is cyclic and every arrow on the second line is cyclic
base change. Within the selected, trace-comparable range inherited from cyclic base
change, upward arrows exist. A downward arrow for a cuspidal representation exists
when it is invariant under the cyclic group, its local parameters have the required
antecedent-complete selected extension fibers, and the reverse comparison has the
required cuspidal selector. A
downward path through the entire diagram exists only when these hypotheses and the
choices can be made compatibly.

### 1.2 Solvable towers and prime refinements

A **cyclic tower** from $F$ to $E$ is a chain of number fields

$$
\mathcal T:\qquad
F=F_0\subset F_1\subset\cdots\subset F_r=E
$$

such that $F_i/F_{i-1}$ is cyclic for every $i$. We call the endpoint extension
**tower-solvable** when at least one such chain exists. We may refine every cyclic
step into cyclic extensions of prime degree. Indeed, if $L/K$ is cyclic of order
$m$ and

$$
1=H_s\subset H_{s-1}\subset\cdots\subset H_0=\operatorname{Gal}(L/K)
$$

is a composition series, the fixed fields reverse it to a prime-degree cyclic
tower. Thus we shall normally assume

$$
[F_i:F_{i-1}]=p_i
$$

with $p_i$ prime. This loses no generality and makes the first possible failure of
cuspidality completely visible: it can occur only when $p_i=2$.

If $E/F$ is finite Galois with solvable group $G$, choose a subnormal composition
series

$$
G=G_0\triangleright G_1\triangleright\cdots\triangleright G_r=1,
\qquad G_{i-1}/G_i\cong\mathbb Z/p_i\mathbb Z.
$$

Putting $F_i=E^{G_i}$ gives a prime cyclic tower. Notice that $G_i$ need only be
normal in $G_{i-1}$. Consequently $F_i/F$ need not be Galois. This small group-theoretic
point matters in descent arguments: an automorphism of one layer is not automatically
an automorphism of every higher layer.

There is a second convention in the literature: an extension is sometimes called
solvable when its Galois closure has solvable group. Such an extension need not itself
admit a chain of intermediate cyclic extensions. Our construction applies directly
to an exhibited cyclic tower and, in particular, to every solvable Galois extension.
For a nonnormal subfield of a solvable Galois closure, one must either supply a cyclic
tower to that field or formulate a separate descent from the closure. We will not
silently identify these two meanings.

### 1.3 The normalization ledger

All statements use the same conventions as the cyclic theory. For a number field
$K$, write

$$
C_K=K^\times\backslash\mathbb A_K^\times.
$$

Reciprocity is geometrically normalized, as in the cyclic theorem: a uniformizer at
an unramified finite place maps to geometric Frobenius. If $L/K$ is finite and
$\chi$ is a Hecke character of $K$, restriction of its one-dimensional Weil
character corresponds to norm pullback

$$
\chi_L=\chi\circ N_{L/K}:C_L\longrightarrow\mathbb C^\times.
$$

The map here is the norm $C_L\to C_K$, not the inclusion of $K^\times$ into
$L^\times$. Norms are transitive:

$$
N_{M/K}=N_{L/K}\circ N_{M/L}
$$

for $K\subset L\subset M$. Parameters go in the opposite-looking but compatible
direction: $W_M\subset W_L\subset W_K$, and base change restricts a parameter along
these inclusions.

At a finite place $v$ of $K$ and $w\mid v$ of $L$, let

$$
e(w/v)=e_{w/v},\qquad f(w/v)=f_{w/v},\qquad
[L_w:K_v]=e_{w/v}f_{w/v}.
$$

Geometric Frobenius over $L_w$ maps to the $f_{w/v}$-th power of geometric
Frobenius over $K_v$, up to inertia. Thus the geometric-Frobenius Satake roots used
here are raised to $f_{w/v}$. They are not raised to $e_{w/v}f_{w/v}$. Readers who
use arithmetic Frobenius must invert every root consistently; the norm direction is
unchanged.

The quadratic automorphic-induction theory was formulated in an arithmetic
reciprocity convention. Whenever we use it here, we translate by inverting the
unramified Frobenius element. This inverts the displayed unramified character values
but changes neither norm pullback, induction, the conjugation criterion for
cuspidality, determinant characters, nor Artin conductors. Thus the induction and
cyclic base-change inputs meet in one geometric-Frobenius ledger rather than in a
mixture of conventions.

We use normalized parabolic induction. If $I_K(\chi_1,\chi_2)$ denotes normalized
induction from the upper triangular Borel, no unannounced factors of
$|\cdot|_K^{1/2}$ are inserted into base change. The symbol $\boxplus$ denotes an
isobaric sum. It is not a direct sum inside the cuspidal spectrum. A twist
$\pi\otimes\chi$ means $\chi\circ\det$, so

$$
\omega_{\pi\otimes\chi}=\omega_\pi\chi^2.
$$

These conventions will be recalled where a calculation is especially vulnerable to
variance, but they will never be changed.

### 1.4 The admissibility ledger

Iteration cannot enlarge the range of the cyclic theorem from which it starts. We
therefore make the word **admissible** precise before stating any solvable result.
For a prime cyclic step $L/K$ and a unitary cuspidal representation $\rho$ over
$K$, the triple $(L/K,\rho)$ is **cyclically admissible** when all of the following
hold:

1. every finite component of $\rho$ and its restricted parameter belong to the
   selected local range of the cyclic theorem: determinant characters, principal
   series, special representations, and the constructed depth-zero or tame
   dihedral packets, with the primitive wild and ramified dyadic boundaries
   excluded; moreover, at every nonsplit place, the full admissible extension
   fiber of the restricted parameter with determinant prescribed by
   $\omega_\rho$ is selected. This is the extension-complete condition, and it is
   stronger than the existence of the known source extension;
2. its archimedean components are among the cohomological parameters for which the
   local twisted comparison is established;
3. matching global test tensors can be chosen with a strongly cuspidal factor.

An essentially unitary cohomological representation is admitted after a common real
norm twist. A prime cyclic tower with source $\pi$ is **ascent-admissible** when each
cuspidal intermediate representation satisfies these conditions at the next step.
If a quadratic step produces a two-character isobaric sum, later steps
are defined by norm pullback of the characters and need no further cuspidal trace
comparison.

For descent, a cyclically invariant cusp form is **descent-admissible** at a step if
it is selected and trace-comparable, the reverse comparison has a strongly cuspidal
factor, and its local parameters are **antecedent-complete selected**: at every
nonsplit place and for every norm antecedent of the invariant central character, the
entire admissible fixed-determinant extension fiber is selected. Mere existence of
one selected local extension is not enough, because the matching algebra cannot
separate it from an unselected extension with the same restriction. A descent chain
is admissible when this holds at every chosen step. When we describe an entire
twisting fiber, we additionally assume **fiber saturation**: every norm-character
twist that occurs remains selected and trace-comparable. Without saturation, the
formulas describe the ambient parameter fiber, while the theorem constructs only its
admissible members.

These conditions are stable under changing a cyclic generator but need not be stable
under changing a tower. Accordingly, “solvable base change exists” below always
means that at least one ascent-admissible cyclic tower has been exhibited. Tower
independence then compares any two admissible towers. We never infer a theorem for an
excluded local packet merely from formal restriction of its parameter.

### 1.5 Existence, uniqueness, cuspidality, and descent

Four questions must be kept separate.

**Existence upward.** Does iterating admissible cyclic base change produce an automorphic object
over $E$ even if an intermediate lift is no longer cuspidal? We shall extend cyclic
base change to rank-two isobaric representations and prove that it does.

**Uniqueness upward.** Does the answer depend on the tower or its prime refinement?
It does not. All towers produce the same restricted local parameters, and strong
multiplicity one identifies their endpoints.

**Cuspidality.** Is the endpoint a cusp form? Not always. The first failure is caused
by a quadratic self-twist, equivalently by automorphic induction from a quadratic
field exposed by that layer. Once the representation becomes isobaric, it never
becomes cuspidal again under further base change.

**Descent.** Which representations over $E$ come from $F$? For one admissible cyclic
step, a cuspidal representation descends exactly when it is Galois invariant and has
the antecedent-complete local extension fibers required by the cyclic theorem.
Through a solvable tower, one must choose a descent at each stage that is invariant at
the next stage. Full invariance of the top is necessary in the Galois case, but it
need not by itself provide coherent choices for a noncyclic group.

The proofs use cyclic base change as an input, but the solvable assertions will be
proved by induction rather than cited as a black box. The repeated local restriction,
the moment at which cuspidality fails, the accumulated character ambiguity, and the
descent obstructions will all remain visible.

## 2. Constructing solvable base change

### 2.1 Base change of an isobaric representation

The output of one cyclic step may be noncuspidal, so iteration requires an operation
on the rank-two isobaric spectrum. There are only two relevant forms. An isobaric
automorphic representation of rank two is either a cuspidal representation of
$\mathrm{GL}_2$ or an isobaric sum

$$
\Pi=\xi_1\boxplus\xi_2
$$

of Hecke characters. Repetition is allowed. At a reducibility boundary the notation
means the standard Langlands quotient in normalized induction; the full local
Weil--Deligne parameter, rather than the semisimplified inducing pair alone, fixes the
constituent.

For a cyclic extension $L/K$, define

$$
\operatorname{BC}_{L/K}(\xi_1\boxplus\xi_2)
=(\xi_1\circ N_{L/K})\boxplus(\xi_2\circ N_{L/K}).
$$

For a cuspidal input use the cyclic base-change theorem. This definition is forced at
every place: it restricts the direct sum of two one-dimensional parameters. It also
shows immediately that a noncuspidal isobaric representation cannot become cuspidal
after another base change. Its two characters can become equal, but a repeated
isobaric sum is still not cuspidal.

This extension is compatible with localization. If $v$ is a place of $K$, then

$$
L\otimes_KK_v\cong\prod_{w\mid v}L_w,
$$

and the component at $w$ is obtained by restricting the $K_v$-parameter to $W_{L_w}$.
At a split place this merely repeats the old component. At a field place it is the
local base-change representation. Thus the same rule covers cuspidal and Eisenstein
data, and all ramified and archimedean data inside the selected range of Section 1.4.

### 2.2 Induction along a prime cyclic tower

Let

$$
\mathcal T:F=F_0\subset F_1\subset\cdots\subset F_r=E
$$

be an ascent-admissible prime cyclic tower, and let $\pi_0=\pi$ be cuspidal
automorphic on $\mathrm{GL}_2(\mathbb A_F)$. Define recursively

$$
\pi_i=\operatorname{BC}_{F_i/F_{i-1}}(\pi_{i-1}).
$$

If $\pi_{i-1}$ is cuspidal, the cyclic theorem makes $\pi_i$ automorphic isobaric.
If $\pi_{i-1}$ is already an isobaric sum, the preceding section pulls its two
characters through the norm. Induction on $i$ therefore proves existence of every
$\pi_i$.

**Proposition 2.1 (existence along an admissible tower).** The endpoint

$$
\operatorname{BC}_{\mathcal T}(\pi):=\pi_r
$$

is an automorphic isobaric representation of
$\mathrm{GL}_2(\mathbb A_E)$. For each place $v$ of $F$, each $w\mid v$ of $E$, and
each path of places

$$
v=v_0\mid v_1\mid\cdots\mid v_r=w,
$$

its local parameter is

$$
\operatorname{rec}_{E_w}(\pi_{r,w})
=\operatorname{rec}_{F_v}(\pi_v)|_{W_{E_w}}.
$$

**Proof.** At the $i$-th step, all-place compatibility in cyclic base change says
that the local parameter is restricted from $W_{F_{i-1,v_{i-1}}}$ to
$W_{F_{i,v_i}}$. Restriction of representations and retention of the monodromy
operator are transitive. Hence the iterated local parameter is restriction directly
from $W_{F_v}$ to $W_{E_w}$. Automorphy and the isobaric alternative follow by the
induction just given. $\square$

The proposition proves considerably more than equality of good Hecke eigenvalues. It
identifies monodromy, ramification, archimedean parameters, and every local type at
the endpoint.

### 2.3 Transitivity and independence of the tower

Suppose $F\subset L\subset E$ and both pieces admit compatible admissible cyclic
towers. Concatenating the
towers and applying Proposition 2.1 gives

$$
\operatorname{BC}_{E/L}(\operatorname{BC}_{L/F}(\pi))
\cong\operatorname{BC}_{E/F}(\pi),
$$

where the expression on the right denotes the tower-independent object about to be
proved. At a place $w\mid u\mid v$, both sides have parameter

$$
\operatorname{rec}_{F_v}(\pi_v)|_{W_{E_w}}.
$$

Now let $\mathcal T$ and $\mathcal T'$ be two ascent-admissible cyclic towers from
$F$ to the same field $E$. Proposition 2.1 shows that their endpoints have isomorphic local
components at every place. Even almost-everywhere equality would suffice: strong
multiplicity one for isobaric representations of $\mathrm{GL}_2$ gives

$$
\operatorname{BC}_{\mathcal T}(\pi)
\cong\operatorname{BC}_{\mathcal T'}(\pi).
$$

**Theorem 2.2 (tower independence).** Solvable base change

$$
\operatorname{BC}_{E/F}(\pi)
$$

is well defined for every tower-solvable extension $E/F$ equipped with an
ascent-admissible tower. It is independent of the admissible cyclic tower, its prime
refinement, the generators of the cyclic Galois groups, and the chosen paths of
places. It is characterized by restriction of the full local parameter at every
place in the selected range.

**Proof.** Existence comes from Proposition 2.1. Two constructions restrict the same
parameter at every $w$, because both subgroup chains end at the intrinsic subgroup
$W_{E_w}\subset W_{F_v}$. Strong multiplicity one identifies the resulting global
isobaric representations. Changing a generator changes a cyclic intertwiner used in
the construction, not the isomorphism class characterized by its local components.
$\square$

This theorem is the reason one may omit $\mathcal T$ from the notation on ascent. It
does not assert existence along a tower that leaves the proved local or
trace-comparable range, and it does not say that intermediate representations or
descent choices are independent of the tower.

### 2.4 Strong multiplicity one as the rigidity input

The logical role of strong multiplicity one deserves emphasis. Cyclic trace formulas
or their equivalent global constructions prove that each step is automorphic and has
the prescribed components at all places. Local restriction proves transitivity of the
candidate. Strong multiplicity one then turns agreement outside a finite set into a
global isomorphism.

More precisely, if $\Pi$ and $\Pi'$ are rank-two isobaric automorphic representations
over $E$ and

$$
\Pi_w\cong\Pi'_w
$$

at all but finitely many $w$, then $\Pi\cong\Pi'$. For cuspidal representations this
follows from the Rankin--Selberg pole argument; for two-character sums it follows from
uniqueness of isobaric decomposition together with the corresponding statement for
Hecke characters. The mixed case cannot occur: a cuspidal representation and a
two-character sum have different Rankin--Selberg analytic behavior.

Strong multiplicity one proves uniqueness, not existence. Nor does it recover a
ramified conductor or an archimedean weight from omitted places. Those data are known
here because each cyclic step has all-place local compatibility. This division of
labor will recur in descent: good-place data recognize a candidate globally, while
the cyclic local theorem supplies the exact component at a bad place.

### 2.5 Refinement across the isobaric boundary

There is one subtle point in the refinement argument. Suppose $L/K$ is cyclic of
composite degree and two prime refinements cross the cuspidal boundary at possibly
different intermediate fields. The prerequisite cyclic theorem is only a
prime-degree theorem, so there is no unproved composite-degree transfer to invoke.
Instead, each refinement is a construction, and the two constructions must be
compared.

At every place both constructions restrict the same parameter from $W_K$ to $W_L$.
If the restriction is reducible, its two one-dimensional constituents are the
characters displayed by the first bad prime step in either refinement. Thus the two
outputs have the same isobaric constituents at almost every place. Uniqueness of
isobaric decomposition and strong multiplicity one identify them. This comparison,
not a separate composite cyclic theorem, defines $\operatorname{BC}_{L/K}$.

This proves that refining a cyclic step does not postpone or manufacture
noncuspidality. It merely reveals the smallest layer at which an irreducible
two-dimensional parameter first splits into two character lines. In a cyclic
extension that layer lies over the unique quadratic subfield when the total degree is
even. In a general solvable tower, the revealing quadratic layer can occur only after
several earlier base changes.

There is an important cyclic qualification. If an irreducible two-dimensional
parameter is restricted through a cyclic quotient and becomes reducible, its two
characters are distinct. A repeated restriction $\xi\oplus\xi$ would leave a
two-dimensional projective representation of the cyclic quotient on the multiplicity
space; after rescaling a generator that projective action becomes an ordinary action
of a cyclic group and splits into lines, contradicting irreducibility downstairs.
Repeated constituents can occur only after a later *noncyclic* total restriction (or
from an already isobaric source), where a genuine projective multiplicity phenomenon
is possible. Strong multiplicity one for isobaric representations remembers the
multiplicity when it does occur.

### 2.6 Galois invariance of the endpoint

Suppose $E/F$ is Galois, not necessarily cyclic, and put
$\Pi=\operatorname{BC}_{E/F}(\pi)$. For $g\in\operatorname{Gal}(E/F)$, define
$\Pi^g(x)=\Pi(g^{-1}x)$. If $w\mid v$, then

$$
(\Pi^g)_w\cong(\Pi_{g^{-1}w})^g.
$$

Both sides are obtained by transporting the restriction of the same $F_v$-parameter
to $W_{E_w}$. Hence their local components agree, and strong multiplicity one gives

$$
\boxed{\Pi^g\cong\Pi\qquad(g\in\operatorname{Gal}(E/F))}.
$$

This proves invariance of the isomorphism class. It does not choose a coherent family
of intertwiners. Under transport of a Weil--Deligne parameter, a chosen Frobenius lift
can rescale the displayed monodromy operator according to the Weil norm; the
covariance relation gives an isomorphic parameter. Ignoring that scale is harmless
for the isomorphism class but not when normalizing an intertwiner.

For a cyclic step, the global Whittaker model normalizes an intertwiner so that its
cyclic product is one. For a noncyclic $G$, Whittaker normalization can likewise make
the field operators on a generic automorphic realization coherent. This fact must not
be confused with membership in the image of iterated base change: one must still find
compatible members of the intermediate descent fibers. When the next quotient acts
on such a fiber this becomes a fixed-point problem; in a merely subnormal tower the
adjacent composite need not be Galois, so no such action on one fiber is automatic.
The projective obstruction of Chapter 8 is attached only to extension of a supplied
compatible parameter. It is not an $H^2$-class canonically attached to an automorphic
isomorphism class. Thus Galois invariance is automatic on ascent and necessary on
descent, but is not by itself the complete recursive image criterion.

## 3. The local representation at the top

### 3.1 One place, all paths

Fix a place $v$ of $F$. The finite étale $F_v$-algebra at the top is

$$
E\otimes_FF_v\cong\prod_{w\mid v}E_w.
$$

Accordingly, the collection of components above $v$ is a representation of

$$
\prod_{w\mid v}\mathrm{GL}_2(E_w),
$$

namely

$$
\bigotimes_{w\mid v}
\operatorname{BC}_{E_w/F_v}(\pi_v).
$$

The notation on the right means restriction of the local Weil--Deligne parameter even
when $E_w/F_v$ is not cyclic. A cyclic tower inside the global extension gives a
tower of local field extensions, interspersed with split étale factors. Transitivity
of restriction proves that all local paths give the same result.

If $E/F$ is Galois of degree $n$, the numbers

$$
g_v=\#\{w:w\mid v\},\qquad e_v=e(w/v),\qquad f_v=f(w/v)
$$

are independent of $w$ and satisfy

$$
n=g_ve_vf_v.
$$

For a non-Galois tower the local degrees can vary with $w$, and the correct identity
is

$$
\sum_{w\mid v}[E_w:F_v]=[E:F].
$$

Using the Galois formula in the non-Galois setting is an easy source of false
multiplicities.

### 3.2 Split, inert, and decomposed finite places

Suppose first that $v$ splits completely. Then there are $[E:F]$ places above $v$,
each $E_w=F_v$, and every component equals $\pi_v$. Base change has not applied a
norm power to one representation; it has repeated the same representation in several
local factors.

Suppose that $E/F$ is Galois and $v$ is unramified and inert. There is one place $w$,
$e_v=1$, and $f_v=[E:F]$. If $\pi_v$ is spherical with geometric-Frobenius Satake
pair $\{\alpha_v,\beta_v\}$, then

$$
\operatorname{Sat}(\Pi_w)
=\{\alpha_v^{[E:F]},\beta_v^{[E:F]}\}.
$$

At a general decomposed place at which both the extension and $\pi_v$ are unramified,
there are $g_v$ components and each has pair

$$
\{\alpha_v^{f_v},\beta_v^{f_v}\}.
$$

Writing $A_v=\alpha_v+\beta_v$ and $B_v=\alpha_v\beta_v$, define

$$
P_0=2,\qquad P_1=A_v,\qquad
P_m=A_vP_{m-1}-B_vP_{m-2}.
$$

Then the lifted normalized Hecke trace is $P_{f_v}$. For example,

$$
P_2=A_v^2-2B_v,
\qquad
P_3=A_v^3-3A_vB_v.
$$

These formulas survive arbitrary solvable refinements because residue degrees
multiply in local towers:

$$
f(w/v)=\prod_i f(v_i/v_{i-1}).
$$

Raising roots successively therefore gives $\alpha_v^{f(w/v)}$, while raising the
trace at each step would give the wrong polynomial.

The same Satake-root formula holds when $E_w/F_v$ is ramified but $\pi_v$ is
spherical. Restriction of an unramified parameter is still unramified; a Frobenius
over $E_w$ maps to the $f(w/v)$-th power of Frobenius over $F_v$ modulo inertia, and
that inertial correction acts trivially. In this case $e(w/v)$ changes the field but
still does not enter the roots.

The raw spherical double-coset operator has eigenvalue

$$
q_w^{1/2}(\alpha_v^{f_v}+\beta_v^{f_v}),
\qquad q_w=q_v^{f_v}.
$$

This factor $q_w^{1/2}$ belongs to the Hecke-operator normalization. It should not be
inserted into the normalized Satake roots.

### 3.3 Ramified places, monodromy, and conductors

At a ramified place, a Frobenius-power recipe is insufficient. Let
$\Phi_v=(r_v,N_v)$ be the parameter of $\pi_v$. Then

$$
\Phi_w=(r_v|_{W_{E_w}},N_v).
$$

The inertia subgroup becomes smaller, positive ramification breaks are reindexed, and
the monodromy operator is left unchanged. Three consequences follow.

First, an unramified representation remains unramified even if $E_w/F_v$ is wildly
ramified. Field ramification does not create inertial action in a parameter that had
none. Second, a finite inertial character can disappear on restriction, so conductor
can fall. Third, positive breaks can move under the Herbrand function, so conductor
can also rise. There is no formula depending only on the old conductor and the local
degree.

The exact cyclic-step identity is useful for auditing a tower. For a cyclic local
step $L/K$, put

$$
X_{\mathrm{loc}}(L/K)
=\widehat{K^\times/N_{L/K}(L^\times)}
$$

and let $\Delta_{L/K}$ be the exponent in $K$ of the discriminant. For a
two-dimensional parameter $\Phi$,

$$
f(L/K)a_L(\Phi|_{W_L})
=\sum_{\eta\in X_{\mathrm{loc}}(L/K)}
a_K(\Phi\otimes\eta)-2\Delta_{L/K}.
$$

Applying this identity at every field step along a path calculates the endpoint
conductor. The direct answer is intrinsic:

$$
\mathfrak f_E(\operatorname{BC}_{E/F}\pi)
=\prod_{w<\infty}\mathfrak p_w^{a(\Phi_v|_{W_{E_w}})}.
$$

It is generally neither $\mathfrak f_F(\pi)\mathcal O_E$ nor an ideal obtained by
multiplying by the discriminant.

The familiar local types illustrate the same rule. Let
$J_K(\chi_1,\chi_2)$ denote the irreducible representation attached to
$(\chi_1\oplus\chi_2,0)$. It is the normalized principal series
$I_K(\chi_1,\chi_2)$ away from the reducibility boundary and the appropriate
Langlands quotient at the boundary. Then

$$
\operatorname{BC}_{E_w/F_v}J_{F_v}(\chi_1,\chi_2)
=J_{E_w}(\chi_1\circ N_{E_w/F_v},
\chi_2\circ N_{E_w/F_v}),
$$

with no ambiguity about a reducible induced module. Also

$$
\operatorname{BC}_{E_w/F_v}
(\operatorname{St}_{F_v}\otimes\mu)
=\operatorname{St}_{E_w}\otimes(\mu\circ N_{E_w/F_v}).
$$

Nonzero monodromy persists, so Steinberg never turns into a character merely because
the semisimple characters coincide. A supercuspidal remains supercuspidal exactly
when the restricted two-dimensional Weil representation remains irreducible; if it
splits, the target is principal series.

### 3.4 Archimedean places

Archimedean base change is also parameter restriction. A complex place only produces
complex places, with trivial local field extension. A real place can extend to real
or complex places. If $r_v$ and $s_v$ count the real and complex places above it,
then

$$
r_v+2s_v=[E:F].
$$

For a Galois extension of degree $n$, either $(r_v,s_v)=(n,0)$ or
$(r_v,s_v)=(0,n/2)$. If $E$ is totally real over a totally real $F$, every real
embedding of $F$ has $[E:F]$ real extensions, so each real local component is simply
repeated.

When a real place becomes complex, restriction uses
$W_{\mathbb C}=\mathbb C^\times\subset W_{\mathbb R}$. A real discrete-series
parameter

$$
\operatorname{Ind}_{W_{\mathbb C}}^{W_{\mathbb R}}
(z^p\bar z^q),\qquad p\ne q,
$$

becomes

$$
z^p\bar z^q\oplus z^q\bar z^p.
$$

The representation over $\mathrm{GL}_2(\mathbb C)$ is principal series, but it
remains regular algebraic when $p$ and $q$ have the required integral form. The
change of local representation class does not double the weight. It exposes the two
characters already present in the induced real Weil parameter.

The sign character of $\mathbb R^\times$ is trivial on
$N_{\mathbb C/\mathbb R}(\mathbb C^\times)=\mathbb R_{>0}$. Thus two real
representations differing by this sign twist have the same complex base change. This
is the local archimedean instance of the global twisting ambiguity.

### 3.5 Local factors and the tower law

Local standard factors, epsilon factors, and conductors are attached to the complete
restricted parameter. At an unramified place,

$$
L(s,\Pi_w)
=\frac1{(1-\alpha_v^{f_v}q_w^{-s})
(1-\beta_v^{f_v}q_w^{-s})}.
$$

For epsilon factors choose one global additive character
$\psi_F:F\backslash\mathbb A_F\to\mathbb C^\times$ and put

$$
\psi_E=\psi_F\circ\operatorname{Tr}_{E/F}.
$$

Trace is transitive in towers, just as norm is. Choosing conductor-zero local
characters independently at each layer changes epsilon factors by different and
determinant terms and obscures transitivity.

For one cyclic step $L/K$, induction and restriction give

$$
L_L(s,\operatorname{BC}_{L/K}\pi)
=\prod_{\chi\in X(L/K)}L_K(s,\pi\otimes\chi),
$$

with the analogous completed epsilon identity under trace-compatible additive
characters. In a solvable tower this product can be iterated, but the resulting list
of characters lives on several intermediate fields. Unless the endpoint extension is
abelian, it should not be rewritten as a product over characters of one cyclic group.
The local restricted parameter is the invariant formulation that works in every
tower.

### 3.6 Decomposition groups and solvable local towers

When $E/F$ is Galois, choose $w\mid v$ and let $D_w\subset G$ be its decomposition
group. The local extension $E_w/F_v$ has group $D_w$, even when the global group is
much larger. Intersecting a subnormal series for $G$ with $D_w$ and removing repeated
terms gives a subnormal series for $D_w$. The corresponding local tower is precisely
the sequence encountered by following $w$ down the global fields.

Some global steps split at $v$. At such a step the chosen local field does not change,
although the number of conjugate places changes. Other steps contribute a nontrivial
cyclic local extension whose degree divides the global prime degree and hence is
either that prime or one. This explains why local base change along a global
prime-degree cyclic step is again a cyclic field base change or a split repetition.

Inertia and residue degree fit into

$$
1\longrightarrow I_w\longrightarrow D_w
\longrightarrow\operatorname{Gal}(k_w/k_v)\longrightarrow1.
$$

The residue quotient is cyclic, generated by geometric Frobenius. Ramification can
make $D_w$ noncyclic even in a solvable global extension, but restriction along the
chosen prime tower still defines the local transfer. Tower independence says that
the result depends only on $W_{E_w}\subset W_{F_v}$, not on a composition series of
$D_w$.

At a decomposed ramified place, all three numbers have separate roles. The number
$g_v$ counts tensor factors, $e_v$ measures how inertia changes, and $f_v$ controls
unramified Frobenius powers. The identity $[E:F]=g_ve_vf_v$ records their product in
the Galois case but does not permit one factor to substitute for another in a local
formula.

## 4. Norm characters, twists, and central characters

### 4.1 The character group at one step

For a cyclic extension $L/K$, define

$$
X(L/K)=\{\chi:C_K\to\mathbb C^\times:
\chi\circ N_{L/K}=1\}.
$$

Class field theory identifies it with

$$
\widehat{C_K/N_{L/K}(C_L)}
\cong\widehat{\operatorname{Gal}(L/K)}.
$$

It is a cyclic group of order $[L:K]$. If $\chi\in X(L/K)$, twist compatibility gives

$$
\operatorname{BC}_{L/K}(\pi\otimes\chi)
\cong\operatorname{BC}_{L/K}(\pi).
$$

This group measures ambiguity downstairs. The quotient is formed from $C_K$ by the
image of the norm from $C_L$. Reversing the quotient to $C_L/N(C_K)$ is not a
variance convention; it is an undefined or different construction.

For the tower $\mathcal T$, put

$$
X_i=X(F_i/F_{i-1}).
$$

At the $i$-th descent, $X_i$ acts on representations over $F_{i-1}$. The groups
$X_i$ do not all live on $C_F$, so their product is not automatically the ambiguity
group of the complete descent. Compatibility across the intervening field
automorphisms decides which tuples of stepwise twists reach the bottom.

### 4.2 The endpoint group in the Galois case

Assume now that $E/F$ is finite Galois with solvable group $G$. Define

$$
X(E/F)=\{\chi:C_F\to\mathbb C^\times:
\chi\circ N_{E/F}=1\}.
$$

Norm limitation identifies

$$
N_{E/F}(C_E)=N_{E^{\mathrm{ab}}/F}(C_{E^{\mathrm{ab}}}),
$$

where $E^{\mathrm{ab}}$ is the maximal abelian subextension of $E/F$. Hence

$$
X(E/F)\cong\widehat{G^{\mathrm{ab}}}.
$$

For a nonabelian solvable group this group can be much smaller than $G$ and much
smaller than the product of the orders of the cyclic steps. It records one-dimensional
characters of the whole quotient, not all characters that appear temporarily at
intermediate levels.

Whenever $\pi\otimes\chi$ remains in the admissible range, every
$\chi\in X(E/F)$ becomes trivial after solvable base change. Indeed,

$$
\operatorname{BC}_{E/F}(\pi\otimes\chi)
\cong\operatorname{BC}_{E/F}(\pi)
$$

follows locally from restriction or globally from norm transitivity. The converse
fiber statement will require cuspidality, because reducible restricted parameters
can have extra automorphisms.

If a tower is not Galois over its bottom field, the displayed norm-kernel group still
makes sense, but there is no general identification with the character group of an
endpoint Galois group. Stepwise groups $X_i$ are then the exact and safe way to
describe descent choices.

### 4.3 Twists, contragredients, and centers

All compatibilities are consequences of operations on local parameters. For a Hecke
character $\mu$ of $F$,

$$
\operatorname{BC}_{E/F}(\pi\otimes\mu)
\cong\operatorname{BC}_{E/F}(\pi)
\otimes(\mu\circ N_{E/F}),
$$

and

$$
\operatorname{BC}_{E/F}(\pi^\vee)
\cong\operatorname{BC}_{E/F}(\pi)^\vee.
$$

The central character is

$$
\boxed{
\omega_{\operatorname{BC}_{E/F}(\pi)}
=\omega_\pi\circ N_{E/F}}.
$$

To see the square in the twisting formula, evaluate $\chi\circ\det$ on the scalar
matrix $zI_2$:

$$
(\chi\circ\det)(zI_2)=\chi(z^2)=\chi(z)^2.
$$

Thus two descents $\pi$ and $\pi\otimes\chi$ have central characters
$\omega_\pi$ and $\omega_\pi\chi^2$. A character can be invisible after base change
without being invisible on the center downstairs.

These identities hold whether the endpoint is cuspidal or isobaric. In the latter
case they are checked on each character constituent. Strong multiplicity one then
turns the local identities into global ones.

### 4.4 Fixed-central-character refinements

Suppose a cuspidal representation $\Pi$ over $E$ has at least one descent $\pi_0$ to
$F$, and assume fiber saturation, so that its complete admissible descent fiber is a
torsor under $X=X(E/F)$. Put $\omega_0=\omega_{\pi_0}$ and
$\Omega=\omega_\Pi$. Every other
descent is $\pi_0\otimes\chi$ and has central character

$$
\omega_0\chi^2.
$$

Let $\omega$ be a specified character of $C_F$ with
$\omega\circ N_{E/F}=\Omega$. Then $\omega/\omega_0\in X$, and a descent with central
character $\omega$ exists exactly when

$$
\boxed{\omega/\omega_0\in X^2}.
$$

When it exists, the descents with that fixed central character form a torsor under

$$
X[2]=\{\chi\in X:\chi^2=1\}.
$$

For a cyclic extension of odd degree, squaring on $X$ is bijective and $X[2]$ is
trivial. Every norm antecedent occurs and selects one descent. For a cyclic extension
of even degree, $X/X^2$ and $X[2]$ both have order two. For a noncyclic solvable
Galois group, $X/X^2$ can have larger $2$-rank, so several independent square-class
obstructions can occur.

There are two distinct questions here. An invariant central character $\Omega$ may
factor through the norm, while a chosen antecedent $\omega$ may fail the square-class
test. Moreover, for a noncyclic endpoint, factorization of the center does not remove
the coherence obstruction to descending the representation itself. Central character
descent is necessary bookkeeping, not a substitute for representation descent.

### 4.5 How stepwise characters assemble

It is useful to see explicitly why the groups $X_i$ do not simply multiply. Consider
two normal cyclic layers $K\subset L\subset M$, and let $\eta$ be a character of
$C_L$ trivial after norm pullback from $M$. Twisting a representation over $L$ by
$\eta$ does not change its base change to $M$. For this twist to come from a character
$\chi$ over $K$, however, one needs

$$
\eta=\chi\circ N_{L/K}.
$$

In particular, $\eta$ must be invariant under $\operatorname{Gal}(L/K)$ and must
satisfy the character-descent condition. An arbitrary member of $X(M/L)$ need not do
so.

On the Galois side, a compatible complete twist is a homomorphism

$$
G=\operatorname{Gal}(E/F)\longrightarrow\mathbb C^\times.
$$

It kills the commutator subgroup and hence factors through $G^{\mathrm{ab}}$.
Restricting it along the successive subgroups produces the visible step characters.
Conversely, a tuple of step characters comes from the bottom exactly when the
successive conjugation and extension relations make it one character of $G$. Global
reciprocity translates this group-theoretic statement into the norm formula for
$X(E/F)$.

For example, in an $A_4$-extension the two quadratic composition factors contribute
quadratic characters at intermediate fields, yet $A_4^{\mathrm{ab}}$ has order three.
Neither quadratic character assembles into a bottom-field character. This is not a
failure of class field theory; it is precisely what abelianization records.

The same reasoning clarifies localization. A global $\chi\in X(E/F)$ has local
components trivial after every local norm, but a separately chosen collection of
local norm-trivial characters need not globalize. It must be trivial on the diagonal
$F^\times$. Thus global fibers are character groups of idele-class norm quotients,
not unrestricted products of local character groups.

### 4.6 Counting fixed-center fibers

Let the finite abelian group $X=X(E/F)$ have decomposition

$$
X\cong C_{n_1}\times\cdots\times C_{n_t}.
$$

The square map has kernel

$$
X[2]\cong\prod_{2\mid n_j}C_2
$$

and image of index $|X[2]|$. Thus, for a cuspidal endpoint with a nonempty descent
fiber, exactly $|X|/|X[2]|$ of the norm antecedents of the top central character occur
as central characters of descents. Every occurring central character is shared by
$|X[2]|$ descents.

In odd order, $X[2]=1$, so the center labels the descents bijectively. If
$X\cong C_2\times C_2$, every element squares to one: all four descents have the same
central character, and the other three norm antecedents do not occur at all. If
$X\cong C_4\times C_2$, there are four square classes and four fixed-center descents
above each attainable character.

These counts assume fiber saturation and that the top representation is cuspidal, so
the $X$-action is free.
At an isobaric endpoint one must quotient by the source stabilizer and account for
possible repeated-constituent extension data. The square map alone cannot perform
that bookkeeping.

## 5. Cuspidality and its precise failure

### 5.1 The first bad step

Let $\pi_i$ be the successive base changes along a prime cyclic tower. If some
$\pi_i$ is noncuspidal, every later $\pi_j$ is a two-character isobaric sum. Hence the
endpoint is cuspidal if and only if every intermediate representation is cuspidal.

Assume $\pi_{i-1}$ is cuspidal. The cyclic criterion says that $\pi_i$ is noncuspidal
if and only if

$$
\pi_{i-1}\otimes\eta\cong\pi_{i-1}
$$

for some nontrivial $\eta\in X_i$. Comparing central characters gives

$$
\omega_{\pi_{i-1}}\eta^2=\omega_{\pi_{i-1}},
$$

so $\eta^2=1$. Since $X_i$ has prime order $p_i$, this forces $p_i=2$. Every
odd-prime step preserves cuspidality.

This observation is stronger than the slogan that odd-degree base change preserves
cuspidality. In an arbitrary prime refinement of a solvable tower, the first failure
is located at a definite quadratic step. Different refinements may expose the same
quadratic phenomenon at different stages, but tower independence guarantees the same
isobaric endpoint.

### 5.2 Quadratic self-twists and automorphic induction

Let $L/K$ be quadratic, let $\eta_{L/K}$ be its norm character, and let $\rho$ be
cuspidal on $\mathrm{GL}_2(\mathbb A_K)$. The following are equivalent:

1. $\rho\otimes\eta_{L/K}\cong\rho$;
2. $\rho\cong\operatorname{AI}_{L/K}(\theta)$ for a Hecke character $\theta$ of
   $L$ with $\theta\ne\theta^\tau$;
3. $\operatorname{BC}_{L/K}(\rho)$ is noncuspidal.

In this case

$$
\operatorname{BC}_{L/K}(\rho)
=\theta\boxplus\theta^\tau.
$$

The equivalence is the global form of Clifford theory. The self-twist splits the
Whittaker coefficients into the two cosets of the norm subgroup. Their Mellin
transforms give $\theta$ and $\theta^\tau$. Conversely, inducing from two cosets makes
the quadratic quotient character act trivially on the isomorphism class. Restriction
to $W_L$ exposes the two character lines. Strong multiplicity one identifies the
automorphic representations after this parameter calculation at almost every place.

At the first bad step $F_i/F_{i-1}$ we therefore have

$$
\pi_{i-1}=\operatorname{AI}_{F_i/F_{i-1}}(\theta)
$$

and

$$
\pi_i=\theta\boxplus\theta^\tau.
$$

For the remaining tower $F_i\subset E$,

$$
\operatorname{BC}_{E/F}(\pi)
=(\theta\circ N_{E/F_i})
\boxplus(\theta^\tau\circ N_{E/F_i}).
$$

The two characters can coincide after norm pullback. This increases symmetry but
does not restore cuspidality. Such coincidence cannot occur if the total restriction
from $F_{i-1}$ to the endpoint has cyclic quotient: cyclic Clifford theory rules out
a repeated scalar restriction of an irreducible two-dimensional parameter. It is a
genuinely noncyclic endpoint phenomenon.

### 5.3 The exact solvable criterion is stepwise

For a noncyclic solvable extension, the cyclic self-twist criterion must be applied at
each layer, not replaced by a self-twist test over the bottom field. This distinction
is essential.

**Theorem 5.1 (solvable cuspidality criterion).** Let

$$
F=F_0\subset F_1\subset\cdots\subset F_r=E
$$

be an ascent-admissible prime cyclic tower, and put
$\pi_i=\operatorname{BC}_{F_i/F}(\pi)$. Then the following are equivalent:

1. $\operatorname{BC}_{E/F}(\pi)$ is cuspidal;
2. every $\pi_i$ is cuspidal;
3. whenever $\pi_{i-1}$ is cuspidal, it has no nontrivial self-twist in
   $X(F_i/F_{i-1})$.

If these conditions fail and $i$ is the first bad index, then $p_i=2$ and there is a
Hecke character $\theta$ of $F_i$ such that

$$
\pi_{i-1}=\operatorname{AI}_{F_i/F_{i-1}}(\theta),
\qquad \theta\ne\theta^\tau,
$$

and

$$
\boxed{
\operatorname{BC}_{E/F}(\pi)
=(\theta\circ N_{E/F_i})
\boxplus(\theta^\tau\circ N_{E/F_i})}.
$$

**Proof.** A noncuspidal isobaric sum remains noncuspidal after every later norm
pullback, so conditions 1 and 2 are equivalent. At a cuspidal step, cyclic base change
is cuspidal precisely when no nontrivial step norm character stabilizes the source,
which proves the equivalence with condition 3. Central characters force a stabilizing
step character to be quadratic, so the first bad step has degree two. The cyclic
self-twist theorem identifies $\pi_{i-1}$ as the displayed automorphic induction and
computes its base change as $\theta\boxplus\theta^\tau$. Pulling both characters
through the remaining norms gives the endpoint formula. $\square$

Although its statement uses a tower, the truth of condition 1 is intrinsic. Thus the
stepwise tests in any other tower give the same final answer, even though the first
bad index and the inducing field at that stage can look different.

### 5.4 Bottom-field self-twists and the projective exception

Assume now that $E/F$ is solvable Galois with group $G$. A bottom-field self-twist is
still a completely explicit sufficient mechanism for failure. If

$$
\pi\otimes\chi\cong\pi
$$

for nontrivial $\chi\in X(E/F)$, then $\chi^2=1$. It cuts out a quadratic subfield
$M/F$ of $E$, and

$$
\pi=\operatorname{AI}_{M/F}(\vartheta)
$$

for a noninvariant Hecke character $\vartheta$ of $M$. Consequently

$$
\operatorname{BC}_{E/F}(\pi)
=(\vartheta\circ N_{E/M})
\boxplus(\vartheta^\tau\circ N_{E/M}).
$$

For a cyclic endpoint this is also necessary. For a noncyclic endpoint the stepwise
criterion need not produce a character of the bottom abelianization. The only
rank-two shape in which that can happen is a repeated final pair:

$$
\operatorname{BC}_{E/F}(\pi)=\xi\boxplus\xi.
$$

The automorphic isomorphism class alone does **not** canonically carry an action of
$G$ on a two-dimensional multiplicity space. The precise projective explanation
requires a compatible global Weil or arithmetic parameter. Suppose such a parameter
$R_F$ is supplied and its restriction $R_E$ satisfies

$$
R_E\cong R_\xi\otimes \mathbf 1_2.
$$

The invariant character $R_\xi$ has an extension factor set
$a\in Z^2(G,k^\times)$, where $k=\mathbb C$ for a complex Weil parameter and
$k=\overline{\mathbb Q}_\ell$ for an $\ell$-adic arithmetic parameter. A
two-dimensional projective representation of $G$
with inverse factor set can cancel $a$ and make $R_F$ an honest irreducible
representation even though its restriction is scalar. Thus a nonzero class in
$H^2(G,k^\times)$ can explain the absence of a bottom quadratic self-twist.
This is a parameter-level statement, not a class attached by fiat to $\pi$.

Projective tetrahedral data give the group-theoretic model: $A_4$ has a
two-dimensional projective representation although
$A_4^{\mathrm{ab}}\cong C_3$ has no quadratic character. If compatible automorphic
and parameter data realizing this model are available, base change to the field
killing the projective action has repeated character parameter. This book neither
asserts that every Schur-multiplier class is automorphic nor invokes a solvable Artin
or lifting theorem to manufacture such an example. Unconditionally on the
automorphic side, Theorem 5.1 says exactly what is available: along a composition
tower an ordinary quadratic self-twist occurs at the first bad intermediate step.

If the two endpoint characters are distinct, the compatible descent datum supplied
by the bottom representation permutes them transitively. Otherwise each line would
descend separately and the source would be isobaric. The kernel of the permutation
map to $S_2$ has index two, and descent of one line to its fixed field identifies the
source with quadratic automorphic induction over $F$. The repeated case is the only
one in which this constituent-permutation argument produces no bottom quadratic
character.

### 5.5 Isobaric decomposition and stabilizers

Rank two permits no more complicated endpoint: solvable base change of a cusp form is
either cuspidal or an isobaric sum of two Hecke characters. Theorem 5.1 computes that
sum from the first bad step. Its unordered pair is independent of the tower, although
the intermediate character $\theta$ used to describe it is not unique.

For a Galois endpoint define

$$
S_E(\pi)=\{\chi\in X(E/F):\pi\otimes\chi\cong\pi\}.
$$

Every nontrivial member is quadratic and describes a bottom-field automorphic-
induction mechanism. The absence of such a member is necessary for cuspidality but
is not a replacement for the stepwise criterion: at a repeated endpoint the
intermediate quadratic symmetry need not assemble into a bottom character. When a
compatible parameter is supplied, Section 5.4 describes that failure projectively.

The stabilizer controls the size of a source fiber. If two cuspidal sources over $F$
are in the same $X(E/F)$-orbit, they have the same base change. The number of distinct
members in the orbit of $\pi$ is

$$
\frac{|X(E/F)|}{|S_E(\pi)|}.
$$

When the common endpoint is cuspidal, $S_E(\pi)$ is trivial, so the action is free.
At an isobaric endpoint the stabilizer need not be trivial, and simply claiming that
the fiber has $|X(E/F)|$ elements overcounts it.

Local reducibility is not the cuspidality criterion. A supercuspidal component can
become principal series at one place while the global lift remains cuspidal. A
globally noncuspidal dihedral lift can have irreducible principal-series components at
almost every place. The exact global test is the cyclic self-twist test at every
tower layer. Projective language for a repeated-character endpoint is used only when
a compatible global parameter makes it meaningful.

### 5.6 Odd order and the location of quadratic steps

If $G$ has odd order, then $G^{\mathrm{ab}}$ has odd order and $X(E/F)$ contains no
quadratic character. Hence every cusp form admitting the required cyclic comparisons
remains cuspidal after base change to $E$. This applies even when the chosen
composition tower has many steps: all of them have odd prime degree.

The converse numerical statement is false. Even order only says that a composition
tower contains a quadratic step. It does not say that $G$ has an index-two quotient.
The group $A_4$ has even order but abelianization $C_3$, so an $A_4$-extension has no
quadratic subfield over $F$. Its composition series nevertheless has quadratic
layers, and the parameter-level model of Section 5.4 shows how a symmetry there can
fail to assemble over $F$.

When the final pair is distinct, failure does require a quadratic quotient and
induction from its field. When the final pair is repeated, bottom-field induction is
possible, while a compatible parameter may instead carry the primitive projective
pattern of Section 5.4. In all cases the prime-tower test of Theorem 5.1 is the exact
automorphic statement.

The first bad step in a chosen tower can involve an intermediate quadratic extension
$F_i/F_{i-1}$ not itself obtained by base-changing a fixed quadratic layer over $F$.
If the stage symmetry assembles into an index-two quotient of $G$, it becomes a
bottom-field self-twist. If it does not, a supplied compatible parameter can instead
assemble its conjugates projectively. In a nonnormal tower there is no endpoint group
in which to make this distinction, and the stepwise criterion remains the correct
statement.

## 6. Compatibility with automorphic induction

### 6.1 Restriction after induction

The self-twist criterion becomes transparent when base change is compared directly
with automorphic induction. Let $M/F$ be quadratic and let $\theta$ be a Hecke
character of $M$. Its automorphic induction has parameter

$$
\operatorname{Ind}_{W_M}^{W_F}\theta.
$$

For a finite extension $E/F$, Mackey restriction studies

$$
\operatorname{Res}_{W_E}^{W_F}
\operatorname{Ind}_{W_M}^{W_F}\theta.
$$

There are two geometric possibilities because $M/F$ is quadratic. If
$M\not\subset E$ and $M\cap E=F$, the compositum $ME$ is quadratic over $E$. If
$M\subset E$, the étale algebra $M\otimes_FE$ is $E\times E$ and induction splits
into two characters. These are not separate coincidences; they are the two cases of
one Mackey formula.

Define the base-changed character on the nonsplit compositum by

$$
\theta_{ME}=\theta\circ N_{ME/M}.
$$

Then, when $M\cap E=F$,

$$
\boxed{
\operatorname{BC}_{E/F}
(\operatorname{AI}_{M/F}\theta)
\cong\operatorname{AI}_{ME/E}(\theta_{ME})}.
$$

When $M\subset E$,

$$
\boxed{
\operatorname{BC}_{E/F}
(\operatorname{AI}_{M/F}\theta)
=(\theta\circ N_{E/M})
\boxplus(\theta^\tau\circ N_{E/M})}.
$$

Here $\tau$ is the nontrivial element of $\operatorname{Gal}(M/F)$. These formulas
include the case in which automorphic induction downstairs is already noncuspidal:
if $\theta=\theta^\tau$, both sides are interpreted isobarically.

### 6.2 Proof of the commuting formula

**Proposition 6.1 (base change commutes with quadratic induction).** The two formulas
above hold at every place in the selected local range and globally for every
ascent-admissible tower-solvable $E/F$ for which the displayed automorphic inductions
belong to that range.

**Proof strategy.** Prove the parameter identity for one cyclic step, translate it
locally, and use strong multiplicity one. Iteration and tower independence then give
the general result.

**Proof.** In the disjoint case, $W_{ME}=W_M\cap W_E$ and there is one relevant
double coset. Mackey's formula gives

$$
\operatorname{Res}_{W_E}^{W_F}
\operatorname{Ind}_{W_M}^{W_F}\theta
\cong
\operatorname{Ind}_{W_{ME}}^{W_E}
(\theta|_{W_{ME}}).
$$

Arithmetic reciprocity identifies $\theta|_{W_{ME}}$ with
$\theta\circ N_{ME/M}$. In the contained case $W_E\subset W_M$, and restriction of
the two-coset induction is

$$
(\theta|_{W_E})\oplus(\theta^\tau|_{W_E}),
$$

which reciprocity turns into the two norm-pulled Hecke characters displayed above.
These identities commute with localization, including at ramified and archimedean
places. The local correspondence gives identical components on both automorphic
sides; strong multiplicity one gives the global isomorphisms. $\square$

The proof also checks determinant signs. The central character of quadratic
automorphic induction is

$$
\omega_{\operatorname{AI}_{M/F}\theta}
=\eta_{M/F}\,\theta|_{C_F},
$$

with the restriction of $\theta$ to scalar ideles understood. If $M\subset E$, the
quadratic character $\eta_{M/F}$ becomes trivial under norm pullback, and the product
of the two characters upstairs is exactly the norm pullback of the displayed central
character.

### 6.3 Cuspidality in the disjoint and contained cases

Assume $\theta\ne\theta^\tau$, so
$\operatorname{AI}_{M/F}(\theta)$ is cuspidal. If $M\subset E$, its base change is
the explicit two-character sum and is noncuspidal. If $M\cap E=F$, the induced
representation over $E$ is cuspidal precisely when

$$
\theta_{ME}\ne\theta_{ME}^{\widetilde\tau},
$$

where $\widetilde\tau$ is the nontrivial automorphism of $ME/E$.

Usually the inequality follows from the original one, but it should be checked rather
than assumed: two distinct characters of $M$ can become equal after norm pullback to
$ME$. If equality occurs, $\theta/\theta^\tau$ is trivial on
$N_{ME/M}(C_{ME})$, and class field theory identifies the extra symmetry responsible
for failure at a quadratic layer of a tower. This equality is impossible when the
total quotient through which the original irreducible two-dimensional parameter is
being restricted is cyclic, by the cyclic Clifford-theory argument of Section 2.5.
For a noncyclic Galois endpoint it can instead fit the repeated parameter pattern of
Section 5.4.

This example shows why the exact criterion is stepwise rather than a test involving
only the original inducing field or only $X(E/F)$. Linear disjointness controls the
Mackey shape, but character restriction can acquire additional stabilizers.

### 6.4 Iteration through solvable towers

Return to the quadratic extension $M/F$ of the preceding sections. Apply Proposition
6.1 at each prime cyclic step of an ascent-admissible tower from $F$ to $E$. Before
$M$ enters the current field, the disjoint-case formula carries the same quadratic
induction to the compositum. At the first field containing $M$, the contained-case
formula exposes the two conjugate character lines. Every later step pulls those two
characters through its norm.

Restriction and the quadratic Mackey decomposition are transitive. Consequently the
iterated formula is independent of the chosen solvable tower and is exactly the
quadratic formula of Section 6.1 over the endpoint: the answer is determined by the
quadratic étale $E$-algebra $M\otimes_FE$. This uses only the rank-two quadratic
automorphic induction proved in the preceding book; no higher-rank automorphic
induction theorem is being assumed.

### 6.5 Conductors, weights, and twists under the comparison

The commuting formula is an equality of complete automorphic representations, so it
retains more than cuspidality. At a place $v$ of $F$, quadratic induction has local
conductor

$$
a_{F_v}(\operatorname{AI}_{M/F}\theta)
=d_v+\sum_{u\mid v}f(u/v)a_u(\theta_u),
$$

where

$$
M\otimes_FF_v=\prod_{u\mid v}M_u,
\qquad
d_v=v(\mathfrak d_{M/F}).
$$

In the split case $d_v=0$ and both degree-one factors occur in the sum.
Base-changing this parameter to $E_w$ gives the same conductor as first pulling
$\theta$ to the relevant factor of $M\otimes_FE$ and then inducing. This equality
follows from induction--restriction of Weil representations; it is not obtained by
separately multiplying two global conductor ideals.

At infinity, the two routes also agree. A quadratic character with algebraic infinity
type induces the real or complex parameter determined by its two conjugates.
Restriction to an extension of the base field pulls back those exponents. Hence
regularity, purity, and cohomological weight are identical on both sides of the
commuting formula.

For a Hecke character $\mu$ of $F$,

$$
\operatorname{AI}_{M/F}(\theta)\otimes\mu
\cong
\operatorname{AI}_{M/F}
(\theta(\mu\circ N_{M/F})).
$$

Base change then pulls $\mu$ to $E$, while the compositum route pulls it to $ME$.
Norm transitivity makes the two character twists equal. This calculation is a useful
variance check: the character on $M$ is multiplied by $\mu\circ N_{M/F}$, not by a
restriction of the function $\mu$ along an inclusion.

## 7. Descent through one cyclic step

### 7.1 Invariance is the admissible image condition for a cusp form

Let $L/K$ be cyclic of prime degree with group $\Gamma$, and let $\Pi$ be a
descent-admissible cuspidal automorphic representation on
$\mathrm{GL}_2(\mathbb A_L)$ in the sense of Section 1.4. Thus $\Pi$ is selected and
trace-comparable, its local parameters are antecedent-complete selected, and the
reverse comparison has the required strongly cuspidal factor. For
$\sigma\in\Gamma$, define

$$
\Pi^\sigma(g)=\Pi(\sigma^{-1}g).
$$

Every base change is invariant. The cyclic descent theorem proves the converse:

**Theorem 7.1 (admissible cyclic cuspidal descent).** The following are equivalent:

1. $\Pi^\sigma\cong\Pi$ for every $\sigma\in\Gamma$;
2. there is a selected, trace-comparable, extension-complete cuspidal automorphic
   representation $\pi$ on $\mathrm{GL}_2(\mathbb A_K)$ such that
   $\operatorname{BC}_{L/K}(\pi)\cong\Pi$.

Every descent of a cuspidal $\Pi$ is cuspidal.

The necessity follows by conjugating restricted local parameters. For sufficiency,
choose a Whittaker-normalized cyclic intertwiner on $\Pi$. The reverse twisted trace
comparison produces an automorphic representation downstairs, and varying one local
test function at a time proves that every local parameter restricts to the prescribed
one. If the descent were an isobaric character sum, its base change would remain a
character sum, contrary to cuspidality of $\Pi$.

The theorem concerns the isomorphism class of $\Pi$. A chosen intertwiner
$A_\sigma:\Pi\to\Pi^\sigma$ is additional descent data. It can be multiplied by a
root of unity. Whittaker normalization makes the cyclic relation
$A_\sigma^{|\Gamma|}=1$ coherent for the trace comparison, but no such choice is part
of the notation $\Pi^\sigma\cong\Pi$.

### 7.2 Descent of the central character

Let $\Omega=\omega_\Pi$. If $\Pi$ is invariant, then $\Omega$ is invariant. For a
cyclic extension,

$$
\ker(N_{L/K}:C_L\to C_K)=(1-\sigma)C_L.
$$

Hence

$$
\Omega(x/\sigma x)=1
$$

shows that $\Omega$ is trivial on the norm kernel. It factors through
$N_{L/K}(C_L)$, and a continuous character on this open finite-index subgroup extends
to $C_K$. Thus

$$
\Omega=\omega\circ N_{L/K}
$$

for at least one Hecke character $\omega$ of $K$.

The antecedent is not unique: all antecedents form a torsor under $X(L/K)$. Nor does
every antecedent occur as the central character of a representation descent. Relative
to one descent of central character $\omega_0$, precisely the characters

$$
\omega_0X(L/K)^2
$$

occur. This is why a trace comparison with fixed central character must choose the
correct square class.

For a noncyclic extension, invariance of $\Omega$ under the whole Galois group still
makes it trivial on all elements $x/\sigma x$, but the relation between those
elements and the global norm kernel is no longer the cyclic identity above.
Invariance need not by itself extend the corresponding one-dimensional parameter:
its factor set can define an $H^2(G,\mathbb C^\times)$ obstruction. Norm limitation
describes the **kernel** of norm pullback from $C_K$ once an antecedent exists; it
does not prove that an invariant character lies in the image. Even an actual central
character descent would still not settle representation descent.

### 7.3 Fibers and the exact twisting group

Assume the source fiber is saturated. If $\pi$ and $\pi'$ are admissible cuspidal
representations over $K$ and have isomorphic cyclic base changes,
then

$$
\pi'\cong\pi\otimes\chi
$$

for some $\chi\in X(L/K)$. Conversely every such twist has the same base change.
When the common lift is cuspidal, this action is free, so its descents form an
$X(L/K)$-torsor.

If the common lift is noncuspidal, the action has the self-twist stabilizer

$$
S_L(\pi)=\{\chi\in X(L/K):\pi\otimes\chi\cong\pi\}.
$$

For a noncuspidal cyclic base change of a cuspidal rank-two source, this is precisely
the order-two group generated by the quadratic character responsible for automorphic
induction. The set of distinct cuspidal sources in that orbit has

$$
\frac{[L:K]}{|S_L(\pi)|}
$$

members.

This fiber theorem is global. Equality of restricted local parameters may suggest a
different quotient character at each place. The twisted trace comparison and the
product formula force those local choices to be the localizations of one Hecke
character. Strong multiplicity one then identifies the global twist.

### 7.4 Descent of a two-character isobaric sum

Solvable descent sometimes encounters a noncuspidal representation, so we also need
the cyclic image criterion for

$$
\Pi=\xi_1\boxplus\xi_2.
$$

Assume the unordered multiset $\{\xi_1,\xi_2\}$ is $\Gamma$-stable. There are two
cases.

If each $\xi_j$ is individually invariant, cyclic character descent gives

$$
\xi_j=\mu_j\circ N_{L/K}
$$

for characters $\mu_j$ of $K$. Then

$$
\mu_1\boxplus\mu_2
$$

is an isobaric descent. The choices of $\mu_1$ and $\mu_2$ are separate torsors under
$X(L/K)$, modulo permutation and coincidences.

If $\Gamma$ acts transitively on the two constituents, its action on the pair has an
index-two stabilizer. Thus $[L:K]$ is even and there is a quadratic intermediate
field $M/K$. One constituent descends through $L/M$ to a character $\theta$ of $M$,
and

$$
\operatorname{AI}_{M/K}(\theta)
$$

is a cuspidal descent when $\theta\ne\theta^\tau$. Its base change to $L$ is the
given pair. Thus a noncuspidal representation upstairs can have a cuspidal descent
downstairs; this is exactly the reverse of the quadratic failure of cuspidality.

If the unordered pair is not invariant, there is no descent. If it is the repeated
pair $\xi\boxplus\xi$, cyclic character descent gives antecedents of $\xi$, and every
cyclic-quotient action on the two-dimensional multiplicity space can be linearized
and diagonalized. Hence a repeated pair has only isobaric descents through this
single cyclic step; it cannot be the base change of a cusp form. Its fiber is
nevertheless not one free character torsor: one must choose two character
antecedents, with permutation and coincidences taken into account.

### 7.5 What the cyclic theorem does and does not guarantee

For a single cyclic step, invariance of a cuspidal isomorphism class is both necessary
and sufficient. This unusually clean statement rests on cyclicity: a normalized
generator gives one relation, and the scalar discrepancy can be removed by taking an
$n$-th root in $\mathbb C^\times$.

The conclusion does not say that a preferred descent exists. It gives a finite
twisting fiber. It also does not say that a chosen descent will be invariant under
automorphisms arising from a larger extension. That question is the new content of
solvable descent.

At the local level the same warning appears through endomorphisms. If the restricted
parameter has scalar endomorphisms, extensions form a torsor under the character group
of the cyclic quotient. For a repeated reducible parameter, different cyclic actions
on the multiplicity space can give fibers not obtained from a common twist. The
global cuspidal hypothesis suppresses this extra ambiguity because multiplicity one
and genericity leave scalar automorphisms.

### 7.6 Existence, uniqueness, and a prescribed descent datum

It is useful to summarize the one-step logic in the order in which it is used.
Invariance of a cuspidal $\Pi$ proves that at least one descent exists. The cyclic
fiber theorem proves that all descents are obtained by $X(L/K)$-twists. A specified
central character cuts this torsor by the square map. A specified collection of local
components may cut it further, possibly to the empty set.

Suppose, for example, that a local component $\pi_v$ is prescribed at one place
$v$ of $K$. Fix a global descent $\pi_0$. A twist $\pi_0\otimes\chi$ has the desired
component exactly when

$$
\pi_{0,v}\otimes\chi_v\cong\pi_v.
$$

The set of global $\chi\in X(L/K)$ satisfying this equation can be smaller than the
corresponding local norm-character set because localization is constrained by the
product formula. Prescriptions at several places impose simultaneous conditions on
one finite global group.

A **descent datum** is stronger still: it chooses intertwiners compatible with the
cyclic action. Different scalar normalizations can give the same representation
descent. In a later tower, however, the action of the next quotient on those choices
can matter. This is why solvable descent begins with the torsor of isomorphism classes
but ultimately keeps track of coherent actions.

## 8. Solvable descent and its obstructions

### 8.1 The recursive descent criterion

Fix a prime cyclic tower

$$
F=F_0\subset F_1\subset\cdots\subset F_r=E
$$

and a cuspidal representation $\Pi_r$ over $E$. Throughout this chapter all cyclic
descent steps are assumed descent-admissible in the sense of Section 1.4. A
**descent chain** is a sequence of
cuspidal representations $\Pi_i$ over $F_i$ such that

$$
\operatorname{BC}_{F_i/F_{i-1}}(\Pi_{i-1})
\cong\Pi_i
$$

for $1\le i\le r$.

**Theorem 8.1 (recursive solvable descent).** The representation $\Pi_r$ descends to
$F$ along the chosen tower if and only if one can choose recursively
$\Pi_{r-1},\ldots,\Pi_0$ so that, for every $i$,

$$
\Pi_i^{\sigma_i}\cong\Pi_i
\qquad
(\sigma_i\in\operatorname{Gal}(F_i/F_{i-1})).
$$

When these conditions hold, every $\Pi_i$ is cuspidal and

$$
\operatorname{BC}_{E/F}(\Pi_0)\cong\Pi_r.
$$

**Proof.** If a chain exists, every $\Pi_i$ is a cyclic base change and is therefore
invariant under the group of that step. Conversely, invariance of $\Pi_r$ under
$\operatorname{Gal}(F_r/F_{r-1})$ gives a cuspidal $\Pi_{r-1}$ by Theorem 7.1.
Choose one. If it is invariant under the next cyclic group, descend again. Repeating
constructs $\Pi_0$. Transitivity and tower independence identify its endpoint with
$\Pi_r$. Cuspidality propagates downward because a noncuspidal source cannot have a
cuspidal base change. $\square$

The criterion is exact but deliberately recursive. Invariance of $\Pi_r$ provides
the first downward arrow. It does not assert that every possible $\Pi_{r-1}$ provides
the second.

### 8.2 The fixed-point obstruction on a descent torsor

The first new obstruction already appears in two consecutive normal layers. Let

$$
K\subset L\subset M
$$

with $M/L$ cyclic, $L/K$ cyclic, and $M/K$ Galois. Put

$$
H=\operatorname{Gal}(M/L),\qquad Q=\operatorname{Gal}(L/K).
$$

Suppose $\Pi_M$ is cuspidal and stable under $\operatorname{Gal}(M/K)$, and suppose
the $M/L$ source fiber is saturated. Its admissible descents to $L$ form a torsor
$D$ under

$$
X_H=X(M/L)=\widehat{C_L/N_{M/L}(C_M)}.
$$

Conjugation in $\operatorname{Gal}(M/K)$ gives $Q$ an action on $X_H$ and on $D$.
Choose one descent $\Pi_L\in D$. For $q\in Q$, the representations
$\Pi_L^q$ and $\Pi_L$ have the same base change to $M$, so there is a unique
$c_q\in X_H$ with

$$
\Pi_L^q\cong\Pi_L\otimes c_q.
$$

Uniqueness uses freeness of the fiber, which follows from cuspidality of $\Pi_M$.
The associativity of conjugation makes $q\mapsto c_q$ a $1$-cocycle. Replacing
$\Pi_L$ by $\Pi_L\otimes\eta$ changes $c$ by the coboundary of $\eta$. Consequently

$$
[c]\in H^1(Q,X_H)
$$

is independent of the chosen descent.

**Proposition 8.2 (two-layer obstruction).** A descent of $\Pi_M$ to $L$ can be
chosen $Q$-invariant if and only if $[c]=0$. When the class vanishes, the invariant
choices form a torsor under the fixed subgroup $X_H^Q$.

**Proof.** A twist $\Pi_L\otimes\eta$ is $Q$-invariant precisely when its displacement
cocycle is trivial. The new cocycle is $c$ times the coboundary of $\eta$, so such an
$\eta$ exists exactly when $[c]$ is zero. The remaining choices are the twists whose
coboundary is trivial, namely the $Q$-fixed part. $\square$

This class is the precise form of the warning that an invariant top representation
need not have an invariant first descent. The hypothesis that $M/K$ is Galois is
essential: it makes $Q$ act on the *same* field $M$ and hence on the one torsor $D$.
In a longer subnormal tower, two adjacent cyclic layers need not have Galois
composite. Then an automorphism of the lower layer can carry the upper field to a
conjugate field, so it transports one descent fiber to another rather than acting on
one $X_H$-torsor. The recursive criterion of Section 8.1 remains valid, but it is not
represented by a class in $H^1(Q,X_H)$ until an actual action on one torsor has been
constructed.

### 8.3 Parameter extension and the projective obstruction

There is an intrinsic parameter-side model for the accumulated obstruction. Suppose
$E/F$ is Galois with group $G$ and an irreducible Weil or arithmetic datum $R_E$ over
$E$ is invariant under $G$, with scalar endomorphisms. Let $k=\mathbb C$ in the
complex Weil case and $k=\overline{\mathbb Q}_\ell$ in the $\ell$-adic arithmetic
case. Choose parameter intertwiners

$$
A_g:R_E\longrightarrow R_E^g.
$$

There are scalars $a(g,h)\in k^\times$ such that

$$
A_{gh}=a(g,h)\,A_g^hA_h
$$

after the natural identifications. Associativity makes $a$ a $2$-cocycle. Rescaling
the $A_g$ changes it by a coboundary, so

$$
[a]\in H^2(G,k^\times)
$$

is the obstruction to extending $R_E$ to the group over $F$. For a cyclic group it
vanishes: the scalar discrepancy of a generator can be removed by an $n$-th root.
For a general solvable group the Schur multiplier can be nonzero.

The qualification “parameter-side” matters. A generic automorphic representation has
Whittaker-normalized field intertwiners, and those normalizations themselves can be
made coherent on its automorphic Whittaker model. Their factor set is not the
obstruction asserted here. The automorphic descent problem asks whether the invariant
representation belongs to the image of iterated base change. Its exact general test
in this book is the recursive existence of a compatible cyclic descent chain. The
$H^1$ class of Section 8.2 represents one transition precisely when the next quotient
acts on the same cyclic descent torsor.

When a compatible global Weil or arithmetic parameter is available, the projective
$H^2$ class explains the aggregate extension problem behind those stagewise choices.
When no such parameter has been supplied, one should not attach an $H^2$ class to an
automorphic isomorphism class by fiat. Nor should one infer that every abstract class
is realized automorphically. Unconditionally, one uses the recursive automorphic
criterion, supplemented by the finite $H^1$ calculation only at transitions satisfying
the hypotheses of Section 8.2.

### 8.4 Twisting ambiguity after full descent

Assume $E/F$ is solvable Galois, $\Pi$ is cuspidal over $E$, at least one
admissible cuspidal descent $\pi_0$ to $F$ exists, and the source fiber is saturated
through the chosen towers. Then the complete admissible fiber is

$$
\{\pi_0\otimes\chi:\chi\in X(E/F)\},
\qquad
X(E/F)\cong\widehat{G^{\mathrm{ab}}}.
$$

The action is free, so the fiber is an $X(E/F)$-torsor.

**Proof.** Every $\chi\in X(E/F)$ is invisible after norm pullback, so all displayed
twists are descents. For the converse, argue by induction on $|G|$. Choose
$H\triangleleft G$ with cyclic prime quotient $Q$, put $K=E^H$, and let $\pi,\pi'$
be two descents over $F$. Their base changes $\pi_K,\pi'_K$ are cuspidal because
their further base change is the cuspidal representation $\Pi$. By induction for the
solvable Galois extension $E/K$,

$$
\pi'_K\cong\pi_K\otimes\eta
\qquad
(\eta\in\widehat{H^{\mathrm{ab}}}=X(E/K)).
$$

Both $\pi_K$ and $\pi'_K$ are $Q$-invariant because they come from $F$. Therefore,
for $q\in Q$,

$$
\pi_K\otimes\eta^q\cong\pi'_K{}^q
\cong\pi'_K\cong\pi_K\otimes\eta.
$$

The inductive fiber action over $E/K$ is free, so $\eta^q=\eta$. An invariant
character of $H$ extends to $G$ when $G/H$ is cyclic: if $t$ lifts a generator, choose
an appropriate root of $\eta(t^{|Q|})$ for the value at $t$. Let
$\chi\in\widehat{G^{\mathrm{ab}}}=X(E/F)$ be such an extension. Then
$\operatorname{BC}_{K/F}(\pi\otimes\chi)\cong\pi'_K$. The cyclic fiber theorem for
$K/F$ gives

$$
\pi'\cong\pi\otimes\chi\delta
$$

for some $\delta\in X(K/F)$, viewed by inflation as a member of $X(E/F)$. This proves
exhaustivity. Finally, a nontrivial stabilizer in $X(E/F)$ would be a bottom-field
self-twist and Section 5.4 would make the endpoint noncuspidal. Thus the action is
free. $\square$

This argument explains why the ambiguity is not the unrestricted product
$\prod_iX_i$. Most tuples of intermediate twists destroy invariance at a lower step.
Exactly the compatible tuples assemble into characters of $G^{\mathrm{ab}}$.

If the common endpoint is isobaric, the $X(E/F)$-action can have the stabilizer
$S_E(\pi)$, and reducible extension data may create additional descriptions. The
clean torsor assertion should therefore always be paired with the hypothesis that the
representation at the top is cuspidal.

### 8.5 Tower dependence of the criterion, not of the answer

Different composition series of $G$ give different lists of cyclic invariance tests
and, at normal two-layer transitions, different intermediate obstruction groups.
Nevertheless, the existence of an $F$-descent is intrinsic. If a descent $\pi$
exists, its base changes along every tower provide compatible descent chains.
Conversely, a chain along any one tower ends in a representation $\pi$ whose
tower-independent base change is $\Pi$.

Thus the recursive criterion may be checked in the tower best adapted to local
conditions. The result does not depend on that choice. What can depend on the tower
is the presentation of a failed attempt: one tower may encounter a nonzero
fixed-point class, while another may fail a direct invariance test at a nonnormal
transition. The intrinsic statement is that no coherent descent datum, equivalently
no compatible chain, has been produced.

For a merely tower-solvable non-Galois extension, there may be no endpoint group acting
on $\Pi$. The recursive criterion is then primary: one asks for invariance under the
cyclic group at the current step after choosing a descent from above. It is misleading
to replace these successive actions by a nonexistent group $\operatorname{Gal}(E/F)$.

### 8.6 Prime-step cohomology in concrete cases

The group $H^1(Q,X_H)$ is finite and often elementary to compute. Write both groups
additively for this discussion. If $Q=C_p$ acts trivially on $X_H$, a $1$-cocycle is
a homomorphism $C_p\to X_H$, and there are no nonzero coboundaries. Thus

$$
H^1(C_p,X_H)=X_H[p].
$$

An obstruction can occur only in the $p$-torsion of the first descent group.

If $|Q|$ and $|X_H|$ are coprime, averaging shows that $H^1(Q,X_H)=0$. Concretely,
multiplication by $|Q|$ is an automorphism of the finite group $X_H$. Averaging the
orbit of any chosen origin and then applying its inverse produces a fixed origin for
the affine action. Thus every affine $Q$-action on the torsor has a fixed point. This
often makes an odd step harmless after a quadratic one, or conversely, but only when
the action and group orders satisfy the coprimality condition.

When $Q=C_2$ acts on $X_H=C_m$ by inversion, an affine action has the form

$$
x\longmapsto a-x.
$$

A fixed point solves $2x=a$. If $m$ is odd, there is a unique solution. If $m$ is
even, there is a solution precisely when $a$ lies in $2C_m$, and then there are two.
This elementary equation is the torsor version of the square-class obstruction that
reappears for central characters.

These calculations do not replace the automorphic input: one must first know the
actual cocycle $c$ produced by conjugating descents. They show how a finite
cohomology computation converts that input into an exact yes-or-no descent test.

### 8.7 Central characters inside the obstruction calculation

The displacement cocycle has a visible effect on centers. If

$$
\Pi_L^q\cong\Pi_L\otimes c_q,
$$

then

$$
\omega_{\Pi_L}^q=\omega_{\Pi_L}c_q^2.
$$

Thus invariance of the central character forces $c_q^2=1$, but it need not force
$c_q=1$. A quadratic displacement is invisible to the center. This is the same reason
that two distinct descents can share a fixed central character.

Consequently, checking only that $\omega_{\Pi_L}$ is $Q$-invariant can at best show
that the obstruction cocycle lands in $X_H[2]$. It does not prove that its class
vanishes. When $X_H$ has odd order, squaring is injective and central invariance does
force $c_q=1$; in that special situation the center detects the whole displacement.

If a central character downstairs is prescribed throughout a tower, one must solve
two compatible finite problems at every step: choose a representation descent that
is invariant at the next step, and require its central character to lie in the
prescribed square class. Where a quotient acts on the same torsor, the first problem
is a fixed-point problem. Solving either condition independently need not solve the
other.

### 8.8 A finite descent protocol

The abstract criterion can be organized as a finite sequence of checks. Begin with a
cuspidal $\Pi_r$ over $F_r$.

1. Test invariance under $\operatorname{Gal}(F_r/F_{r-1})$ using good-place Hecke
   polynomials. If it fails, no descent along the tower exists.

2. Use cyclic descent to obtain one $\Pi_{r-1}$ and record its torsor under $X_r$.
   If a central character or local types are prescribed, retain only the twists
   satisfying those finite conditions.

3. Test every retained $\Pi_{r-1}$ for invariance under
   $\operatorname{Gal}(F_{r-1}/F_{r-2})$. If the two-layer composite
   $F_r/F_{r-2}$ is Galois, this test is the fixed-point calculation of Section 8.2:
   the quotient acts on the remaining torsor and its displacement cocycle must be a
   coboundary. Without that normality, there is no canonical action on this single
   torsor; direct enumeration and the cyclic invariance test are the valid procedure.

4. Repeat until reaching $F$. Because the starting representation is cuspidal, every
   successful descent remains cuspidal: a character sum cannot acquire a cuspidal
   base change. If one starts instead with an isobaric top representation, this
   protocol must from the outset be replaced by the constituent analysis of
   Section 7.4.

5. Finally compare good-place data with any independently specified bottom candidate.
   Strong multiplicity one supplies the global identification, and local parameter
   extension supplies the bad-place assertions.

Every set in this protocol is finite. The character groups are finite norm-quotient
duals, the prescribed-center condition is a square-class calculation, and every
defined fixed-point obstruction lies in finite group cohomology. The difficult input
is not an infinite search but the automorphic invariance and, at normal transitions,
the action on the descent torsor.

If two different towers are available, either may be used. A successful chain on one
proves intrinsic descent. Failure of one particular choice of intermediate descent is
not failure of the tower; one must test the entire cyclic fiber. At a normal
transition this is equivalent to absence of a fixed point, or to a nonzero
displacement class. At a nonnormal transition, the decisive fact is simply that no
member of the fiber passes the next cyclic invariance test.

## 9. Local-to-global rigidity in recognition and descent

### 9.1 Recognizing an ascent at good places

Let $\pi$ be cuspidal over $F$ and let $\Pi$ be an already constructed isobaric
representation over a tower-solvable $E$. To prove

$$
\Pi\cong\operatorname{BC}_{E/F}(\pi),
$$

it is enough to compare unramified components outside a finite set. If $v$ is such a
place and $w\mid v$, the test is

$$
\operatorname{Sat}(\Pi_w)
=\{\alpha_v^{f(w/v)},\beta_v^{f(w/v)}\}.
$$

Strong multiplicity one then gives the global isomorphism. It is not necessary to
reconstruct the chosen cyclic tower.

Equality of only the traces is enough when determinants are already known from the
central character; otherwise compare the full degree-two Hecke polynomial. A single
trace can vanish for unrelated Satake pairs, so omitting determinants without a
central-character hypothesis is unsafe.

### 9.2 Recovering bad local components

Recognition at good places does not by itself prove a statement about conductors,
Steinberg monodromy, or infinity type. Once the global isomorphism with solvable base
change is known, however, Theorem 2.2 supplies the component at every place:

$$
\operatorname{rec}_{E_w}(\Pi_w)
=\operatorname{rec}_{F_v}(\pi_v)|_{W_{E_w}}.
$$

This order of reasoning is often efficient. Use unramified data at all but finitely
many places and strong multiplicity one to identify the global object, then invoke
all-place local compatibility to read off the bad places. Do not try to infer a
ramified parameter from an unramified Euler product alone.

In descent the same method works in reverse. A cyclic trace comparison constructs a
descent with the prescribed local components. If another arithmetic construction
produces a candidate downstairs with matching good-place polynomials, strong
multiplicity one identifies it with the automorphic descent and thereby transports
the exact bad-place data.

### 9.3 Why separate local invariance is insufficient

Suppose for every $w$ over $v$ one can find some local parameter over $F_v$ whose
restriction is the parameter of $\Pi_w$. These choices need not be conjugate across
places, need not have a common central character, and need not be automorphic. Even
if each local parameter is invariant under a decomposition group, the scalar choices
in their descent intertwiners may fail the global product relation.

The cyclic global descent theorem solves precisely this globalization problem for one
step. For a solvable tower, the torsor obstruction solves the compatibility problem
between steps. Local descent is necessary evidence, but it is neither the global
automorphy theorem nor the coherence theorem.

Similarly, local loss of supercuspidality does not imply global loss of cuspidality.
Cuspidality is detected by a global self-twist. Strong multiplicity one is what turns
the equality $\pi\otimes\eta\cong\pi$ at almost every place into a global
isomorphism; no single completion can replace it.

### 9.4 Density, conjugation, and Galois invariance

Let $E/F$ be Galois and $\Pi$ be cuspidal over $E$. To show
$\Pi^g\cong\Pi$, it suffices to compare good-place Hecke polynomials at all but
finitely many places. At a place $w$ where both sides are unramified,

$$
P_w(\Pi^g,X)=P_{g^{-1}w}(\Pi,X).
$$

If these polynomials agree with a system arising by restriction from $F$, they are
constant on $G$-orbits, and strong multiplicity one yields invariance.

This is the principal local-to-global rigidity input in modularity descent. A global
Galois representation over $F$ has conjugate restrictions at primes above the same
place, so its Frobenius polynomials force invariance of the automorphic representation
over $E$. The Galois representation then does more: it selects compatible twists in
the cyclic descent fibers, as we shall prove in Chapter 13.

### 9.5 The Rankin--Selberg reason for rigidity

Strong multiplicity one is not a formal property of restricted tensor products. Its
analytic source is the pole of a Rankin--Selberg $L$-function. For a cuspidal $\pi$,

$$
L^S(s,\pi\times\pi^\vee)
$$

has a simple pole at $s=1$. If $\pi'$ is a distinct cusp form, then

$$
L^S(s,\pi'\times\pi^\vee)
$$

is holomorphic there. If $\pi$ and $\pi'$ agree outside $S$, these two partial Euler
products are equal, a contradiction. The ramified factors have already been omitted
and cannot cancel the distinction.

For isobaric sums, the locations and orders of Rankin--Selberg poles recover the
cuspidal constituents with multiplicity. Thus the same analytic rigidity proves that
two tower constructions with equal good-place restriction data have identical
isobaric decompositions.

The theorem also explains why a positive-density but incomplete comparison requires
care. Equality on all but finitely many places is sufficient. Weaker density
hypotheses need refined multiplicity-one theorems and are not silently used here. In
the arithmetic descent criterion below, equality of characteristic polynomials at all
unramified places outside a finite set is imposed as part of the association
hypothesis, which is exactly the safe range.

## 10. Arithmetic and representation-theoretic compatibilities

### 10.1 Conductors, levels, and newvectors

Let $\Phi_v$ be the local parameter of $\pi_v$. The conductor exponent at
$w\mid v$ after solvable base change is exactly

$$
a_w=a(\Phi_v|_{W_{E_w}}).
$$

The global conductor and minimal $K_1$-level are

$$
\mathfrak f_E(\operatorname{BC}_{E/F}\pi)
=\prod_{w<\infty}\mathfrak p_w^{a_w}.
$$

At a completely split place the old exponent is repeated. At an unramified field
extension the exponent is unchanged even if type changes. At a ramified extension it
can rise, stay fixed, or fall. Spherical representations remain spherical;
Steinberg twists remain Steinberg twists; supercuspidals are governed by irreducibility
of the restricted Weil representation.

The minimal newvector subgroup over $E_w$ is determined by $a_w$. A more refined
level structure, such as an inertial type or an Iwahori condition, must be transported
through the entire restricted parameter. Equal conductor exponents do not imply equal
types or equal fixed-vector dimensions for arbitrary compact open subgroups.

Descent reverses this calculation only after a descent is chosen. Different members
of a twisting fiber can have different conductors downstairs because the characters
in $X(E/F)$ may be ramified. Consequently the conductor upstairs does not determine
a unique minimal level downstairs.

### 10.2 Algebraic and cohomological weights

Suppose $\pi$ is regular algebraic and cohomological. At an embedding
$\tau:F\hookrightarrow\mathbb C$, write its algebraic weight as

$$
(a_\tau,b_\tau),\qquad a_\tau>b_\tau.
$$

For every embedding $\widetilde\tau:E\hookrightarrow\mathbb C$ extending $\tau$,
solvable base change has weight

$$
(a_{\widetilde\tau},b_{\widetilde\tau})
=(a_\tau,b_\tau).
$$

This follows one archimedean restriction at a time, and hence is independent of the
tower. Purity weight, regularity, and cohomological parity are preserved. At a split
real place the representation is repeated. At a real place becoming complex the two
conjugate Weil characters carry the same algebraic coefficient data.

Conversely, an algebraic representation over $E$ can descend only if its weights are
constant on the embeddings identified by every cyclic step. This orbit-constancy is
necessary but not sufficient: one still needs automorphic invariance and coherent
descent. In a totally real tower, a parallel weight remains parallel in both
directions whenever descent exists.

### 10.3 Algebraic conjugation and rationality fields

For an algebraically normalized cohomological representation and
$\iota\in\operatorname{Aut}(\mathbb C)$, the unramified lifted trace is the integral
polynomial

$$
P_{f(w/v)}(A_v,B_v).
$$

Applying $\iota$ commutes with this polynomial, and strong multiplicity one gives

$$
\operatorname{BC}_{E/F}(\pi^\iota)
\cong\operatorname{BC}_{E/F}(\pi)^\iota.
$$

It follows that

$$
\mathbb Q(\operatorname{BC}_{E/F}\pi)
\subseteq\mathbb Q(\pi)
$$

for fields of rationality in the common algebraic normalization. Equality can fail.
An automorphism $\iota$ may carry $\pi$ to $\pi\otimes\chi$ with
$\chi\in X(E/F)$; base change kills the twist and makes $\iota$ fix the endpoint.

More precisely, when the endpoint is cuspidal, its coefficient stabilizer consists
of the $\iota$ for which $\pi^\iota$ lies in the $X(E/F)$-fiber of $\pi$. In a
non-Galois tower the same statement is expressed by the compatible stepwise fiber.
This concerns fields of rationality. A model of the representation, a chosen
Whittaker functional, or a local type can require a larger field of definition.

Descent has no canonical reverse equality. Different twists in a descent fiber can
have different character fields, so the field of rationality downstairs may grow
after a choice of descent.

### 10.4 Local types and normalized induction

The safest type calculation begins with the Weil--Deligne parameter. For a principal
series, pull both inducing characters through the norm and then inspect the
reducibility boundary. For a special representation, retain nonzero monodromy. For a
supercuspidal, restrict the irreducible Weil representation and test whether it stays
irreducible. This procedure commutes with every tower refinement.

Normalized induction is essential for the literal formulas. If unnormalized
induction were used, the modulus character of the Borel would change between $F_v$
and $E_w$ because $q_w=q_v^{f(w/v)}$. The apparent extra powers would be artifacts of
normalization rather than base change. Our convention keeps the operation equal to
parameter restriction.

At archimedean places, infinitesimal characters and algebraic weights are likewise
read from the restricted parameter. A real discrete series becoming a complex
principal series is not a loss of regularity. A finite sign twist becoming trivial is
a real-to-complex norm phenomenon and contributes to the descent fiber.

### 10.5 Standard factors and contragredients

Restriction commutes with duals and determinants, so

$$
(\operatorname{BC}_{E/F}\pi)^\vee
\cong\operatorname{BC}_{E/F}(\pi^\vee)
$$

and central characters pull through $N_{E/F}$. Local $L$- and epsilon factors are
those of the restricted parameter. Their global products inherit functional
equations from the automorphic endpoint, whether it is cuspidal or isobaric.

At a good place the degree-two polynomial is

$$
(1-\alpha_v^{f(w/v)}X)(1-\beta_v^{f(w/v)}X).
$$

At a bad place one must retain the inertia invariants and monodromy in the definition
of the local factor. Semisimplifying away $N$ would confuse a Steinberg component with
the neighboring character parameter and could give the wrong conductor and epsilon
factor.

These compatibilities also constrain descent. If a proposed descent has the wrong
central character, dual, or local factor at even one place, it is not the desired
member of the twisting fiber. In arithmetic applications these invariants are often
what select the correct descent.

### 10.6 Three conductor profiles

Three examples keep the conductor rules honest.

First, let $E_w/F_v$ be totally ramified and let $\pi_v$ be spherical. Its inertia
action and monodromy are both trivial. Restriction remains trivial on inertia, so
$a_w=0$. The discriminant of the field extension does not appear as automorphic level.

Second, let

$$
\pi_v=\operatorname{St}_{F_v}\otimes\mu_v
$$

with $\mu_v$ unramified. Every base change is
$\operatorname{St}_{E_w}\otimes(\mu_v\circ N)$ and has conductor exponent one.
Even a highly ramified extension does not erase the nonzero monodromy operator.

Third, let $E_w/F_v$ be quadratic with norm character $\eta_v$, and take an
irreducible normalized principal series

$$
I_{F_v}(\mu_v,\mu_v\eta_v).
$$

After base change the two inducing characters coincide because
$\eta_v\circ N_{E_w/F_v}=1$. The conductor upstairs is twice the conductor of
$\mu_v\circ N$. Depending on cancellation and ramification of $\mu_v$, this can be
smaller than the sum of the two original conductors. Another character of the same
downstairs conductor but nontrivial on local norms need not cancel. Hence old
conductor, $e$, and $f$ alone do not determine the new exponent.

These profiles propagate through solvable towers by restriction. They also show why
descent can increase level: selecting a different norm-character twist downstairs can
reintroduce ramification that the top parameter cannot see.

## 11. Compatibility with Jacquet--Langlands

### 11.1 Scalar extension of the inner form

This chapter stays inside the global Jacquet--Langlands theorem already established:
$F$ is totally real, $D/F$ is totally definite, $\rho$ is a selected noncharacter
automorphic representation in the prescribed parallel-weight-two range, and every
finite packet used after restriction remains selected. The split case
$D=M_2(F)$ is included as the identity boundary. We take $E/F$ to be totally real,
so $D_E$ is again totally definite when $D$ is. No global inner-form existence
statement outside this range is used here.

Let

$$
\pi=\operatorname{JL}_{D/F}(\rho)
$$

be the cuspidal transfer to $\mathrm{GL}_2(\mathbb A_F)$. Scalar extension gives

$$
D_E=D\otimes_FE.
$$

At a place $w\mid v$, local Brauer invariants satisfy

$$
\operatorname{inv}_w(D_E)
=[E_w:F_v]\operatorname{inv}_v(D)
\quad\text{in }\mathbb Q/\mathbb Z.
$$

Since a ramified quaternion algebra has invariant $1/2$, $D_E$ is ramified at $w$
exactly when $D$ is ramified at $v$ and $[E_w:F_v]$ is odd. A split place of $D$
never becomes ramified after scalar extension.

This parity rule is transitive. Multiplying local degrees one cyclic step at a time
gives the same invariant as multiplying by $[E_w:F_v]$ directly. Thus the inner form
at the top is independent of the chosen solvable tower for exactly the same local
reason as the split-side base change.

### 11.2 The commuting square

Assume now that $E/F$ is solvable Galois and that
$\Pi=\operatorname{BC}_{E/F}(\pi)$ is cuspidal. At every place where $D_E$ is
division, the local degree over a ramified place of $D$ is odd. Restriction of a
two-dimensional irreducible Weil representation to the corresponding odd-index
normal subgroup remains irreducible. Indeed, Clifford theory would otherwise give
either an orbit of two distinct lines, impossible for an odd quotient, or a repeated
line carrying an irreducible two-dimensional projective action of an odd-order
solvable quotient. The latter is impossible because a finite odd-order subgroup of
$\operatorname{PGL}_2(\mathbb C)$ is cyclic, and a cyclic projective action can be
lifted and diagonalized. A special parameter retains nonzero monodromy. Hence
$\Pi_w$ is discrete series at every ramified place of $D_E$.

The selected global Jacquet--Langlands theorem over $E$ therefore gives a unique
noncharacter automorphic
representation $\rho_E$ of $D_E^\times(\mathbb A_E)$ with

$$
\operatorname{JL}_{D_E/E}(\rho_E)=\Pi.
$$

Define $\operatorname{BC}_{E/F}^D(\rho)=\rho_E$. Then

$$
\begin{array}{ccc}
\rho&\xrightarrow{\operatorname{JL}_{D/F}}&\pi\\
\downarrow\operatorname{BC}^D&&\downarrow\operatorname{BC}\\
\rho_E&\xrightarrow{\operatorname{JL}_{D_E/E}}&\Pi
\end{array}
$$

commutes. At each place both routes restrict the same Weil--Deligne parameter. This
proves compatibility with central characters, twists, contragredients, conductors,
local factors, levels, and algebraic weights wherever both sides are defined.

**Proposition 11.1 (solvable inner-form compatibility).** Within the selected,
totally definite parallel-weight-two range fixed in Section 11.1, the commuting square
is independent of the cyclic tower. It can be formed step by step whenever the
split-side endpoint is cuspidal, and its endpoint agrees with the direct construction
above.

**Proof.** At every cyclic step, local Jacquet--Langlands and local base change commute
through the common parameter. Global Jacquet--Langlands is unique by its local
components. Iteration therefore produces $\rho_E$ with split transfer $\Pi$.
Theorem 2.2 and strong multiplicity one on the split side make the endpoint
independent of the tower, and injectivity of global Jacquet--Langlands does the same
on the inner-form side. $\square$

For a non-Galois cyclic tower, the same conclusion holds if the restricted parameter
is discrete at every place where $D_E$ is division. Odd local degree alone is then
not sufficient: restriction to an odd-index nonnormal Weil subgroup can be reducible.
The discrete-series condition is the exact local hypothesis replacing normality.

### 11.3 The isobaric boundary

If $\operatorname{BC}_{E/F}(\pi)$ is a two-character isobaric sum, it is not the
global Jacquet--Langlands transfer of a noncharacter automorphic representation on a
nonsplit quaternion algebra. The commuting square stops at this boundary. This is a
global failure caused at some quadratic tower layer, whether by a bottom-field
dihedral self-twist or, when compatible parameter data exist, by the primitive
projective pattern described in Chapter 5. It is not a defect in local parameter
restriction.

In the split boundary $D=M_2(F)$, also $D_E=M_2(E)$, so the isobaric endpoint remains
meaningful and the lower horizontal arrow is the identity. It must still not be
called cuspidal. For a nonsplit totally definite $D_E$, there is no lower-left
cuspidal representation corresponding to that isobaric sum.

There is no need to test cuspidality separately at every intermediate layer. Once a
cyclic step becomes isobaric, later steps remain isobaric. Hence a cuspidal endpoint
implies that every stepwise square lies in the cuspidal range.

### 11.4 Descent on an inner form

Suppose an automorphic representation $\rho_E$ on $D_E^\times$ has cuspidal split
transfer $\Pi_E$, and suppose $\Pi_E$ admits a solvable descent $\pi$ to $F$. For
$\pi$ to come from $D^\times$, it must be discrete series at every place where $D$
is ramified. At places $w$ where $D_E$ remains division, this is forced by the local
transfer. At a ramified $v$ of $D$ for which every relevant local degree is even,
$D_E$ can split and the upstairs representation may no longer remember discreteness
of a chosen descent. The local descent parameter must then be checked.

If the check holds, global Jacquet--Langlands produces $\rho$ and the square commutes.
Twisting by a Hecke character preserves discreteness. Therefore all determinant
twists in a given global character fiber satisfy the discrete-series condition at a
fixed $v$ simultaneously; a twist cannot turn a discrete parameter into a
nondiscrete one. What the upstairs split algebra may fail to determine is which
extension of the top local parameter occurs downstairs before twisting.

## 12. Four solvable patterns and one local calculation

### 12.1 A quadratic--cubic tower

Let

$$
F\subset K\subset E,
\qquad [K:F]=2,\qquad [E:K]=3,
$$

with both steps cyclic. Start with a cuspidal $\pi$ over $F$. If
$\pi\otimes\eta_{K/F}\not\cong\pi$, the quadratic lift $\pi_K$ is cuspidal. The
cubic step is automatically cuspidal because a self-twist stabilizing a rank-two
cusp form must be quadratic. Hence $\pi_E$ is cuspidal.

If instead

$$
\pi=\operatorname{AI}_{K/F}(\theta),
$$

then

$$
\pi_K=\theta\boxplus\theta^\tau
$$

and

$$
\pi_E=(\theta\circ N_{E/K})
\boxplus(\theta^\tau\circ N_{E/K}).
$$

The later odd step does not restore cuspidality.

At a finite place $v$ that is inert unramified in both steps, the residue degree is
$6$. A Satake pair $\{\alpha,\beta\}$ becomes
$\{\alpha^6,\beta^6\}$. Computing in stages gives cubes of the quadratic-stage roots,
or squares of the cubic-stage roots, with the same answer. The trace is

$$
\alpha^6+\beta^6=P_6(A,B),
$$

not $A^6$. If the quadratic step is totally ramified and the cubic step unramified
inert, the residue degree is only $3$, illustrating again that ramification index is
not a Frobenius exponent.

### 12.2 An $S_3$-extension

Let $E/F$ be Galois with group $S_3$. The normal series

$$
S_3\triangleright A_3\triangleright1
$$

gives

$$
F\subset K=E^{A_3}\subset E,
\qquad [K:F]=2,\quad [E:K]=3.
$$

The maximal abelian quotient of $S_3$ is of order two, so

$$
X(E/F)\cong\widehat{S_3^{\mathrm{ab}}}
\cong\mathbb Z/2\mathbb Z.
$$

Thus a cuspidal endpoint, when it has a descent, has exactly two descents to $F$,
differing by the quadratic character of $K/F$. The cubic character group appearing
at the upper step is not an additional independent endpoint ambiguity; a cubic twist
chosen over $K$ must satisfy conjugation compatibility to descend through $K/F$.

Cuspidality fails precisely when

$$
\pi\cong\operatorname{AI}_{K/F}(\theta).
$$

There is only one quadratic subfield because $S_3$ has only one index-two normal
subgroup. The cubic upper step itself cannot be the first bad step.

This example also displays the descent obstruction. A fully $S_3$-invariant cusp form
over $E$ descends to a three-element torsor of representations over $K$. Conjugation
by the nontrivial element of $\operatorname{Gal}(K/F)$ acts on that torsor. An
$F$-descent requires a fixed point, but in this example the fixed point always exists.
Indeed the action on the cubic step group $C_3$ is inversion, and

$$
H^1(C_2,C_3)=0.
$$

Equivalently, every affine involution $x\mapsto a-x$ of a three-element torsor has the
unique fixed point $x=a/2$. Thus full $S_3$-invariance is sufficient here, although it
does not itself name the distinguished descent.

### 12.3 An $A_4$-extension

Let $E/F$ be Galois with group $A_4$. A composition series can be refined through

$$
A_4\triangleright V_4\triangleright C_2\triangleright1,
$$

so the cyclic step degrees are $3,2,2$. Their product is $12$, but

$$
A_4^{\mathrm{ab}}\cong C_3.
$$

Therefore

$$
X(E/F)\cong\widehat{C_3}
$$

has no quadratic character. It follows that no **bottom-field** quadratic self-twist
can be killed by base change to $E$. It does not follow that every base change is
cuspidal, because the exact test still takes place at the two intermediate quadratic
steps. Parameter-side tetrahedral data are the important model: a two-dimensional
projective $A_4$-action becomes scalar over the field cutting out that action, so a
compatible automorphic realization would have repeated endpoint
$\xi\boxplus\xi$. No assertion that such a realization follows from the preceding
books is being made here.

Along the displayed composition series, such a compatible realization remains
cuspidal at the cubic step and acquires an ordinary quadratic self-twist at one of the
later steps. The quadratic character exists over that intermediate field, but its
conjugates do not assemble into a quadratic character of $A_4^{\mathrm{ab}}$. Their
failure to assemble is measured by the nontrivial projective factor set when the
compatible parameter is present.

This tower also illustrates the exact range of the $H^1$ language. The composite of
the two upper quadratic layers is the Galois $V_4$-extension, so the corresponding
two-layer calculation has trivial action and

$$
H^1(C_2,C_2)\cong C_2.
$$

At the following cubic transition, however, the relevant $C_2$ subgroup is not normal
in $A_4$; the adjacent composite field is not Galois over $F$. There is then no
canonical action of the cubic quotient on one quadratic descent torsor. One must use
the recursive invariance test, not write down an $H^1(C_3,C_2)$ obstruction by
analogy.

Apart from the repeated-character shape, the absence of a quadratic quotient rules
out the distinct-character dihedral failure. Thus the $A_4$ pattern is precisely why
the general theorem states a stepwise criterion and does not promote the cyclic
bottom self-twist test to all solvable groups.

The example sharply separates stepwise choice groups from the endpoint fiber. The
orders of the step groups multiply to $12$, whereas a cuspidal endpoint with a
descent has only three descents over $F$. The missing tuples are precisely those
failing the compatibility conditions in Chapter 8.

### 12.4 A biquadratic extension

Let $E/F$ be biquadratic with group $V_4$. There are three quadratic subfields
$M_1,M_2,M_3$, and

$$
X(E/F)\cong\widehat{V_4}\cong V_4.
$$

If $\pi$ has no self-twist by any of the three nontrivial characters, its base change
is cuspidal. The four twists $\pi\otimes\chi$ give four distinct descents of the
common cusp form. Since every $\chi\in X$ has $\chi^2=1$, all four descents have the
same central character. Fixing the center removes none of the ambiguity.

If

$$
\pi=\operatorname{AI}_{M_1/F}(\theta),
$$

then base change to $E$ is

$$
(\theta\circ N_{E/M_1})
\boxplus(\theta^\tau\circ N_{E/M_1}).
$$

The self-twist by $\eta_{M_1/F}$ stabilizes $\pi$, so its $X$-orbit has at most two
distinct elements. In special monomial cases further quadratic self-twists can enlarge
the stabilizer. The correct count is always $|X|/|S_E(\pi)|$.

A tower $F\subset M_1\subset E$ and a tower $F\subset M_2\subset E$ yield the same
endpoint. In the first, the inducing field is exposed immediately. In the second,
the first base change may remain cuspidal and the failure appears only at the upper
quadratic step. This is a concrete demonstration that the first bad *stage* depends
on a tower even though the quadratic mechanism and final isobaric representation are
intrinsic.

### 12.5 One place through a decomposed ramified tower

Consider a degree-six solvable Galois extension and a finite place $v$ with

$$
g_v=2,\qquad e_v=3,\qquad f_v=1.
$$

There are two places $w_1,w_2$ above $v$, and each local field extension has degree
three and is totally ramified. If $\pi_v$ is spherical with Satake pair
$\{\alpha,\beta\}$, then both components upstairs have the same pair
$\{\alpha,\beta\}$: the residue degree is one. The component occurs twice because
$g_v=2$. Neither the ramification index three nor the global degree six raises the
roots.

If instead $\pi_v$ is a selected supercuspidal, the two components are conjugate
restrictions of its Weil representation to $W_{E_{w_j}}$. Each remains
supercuspidal: restriction through this cyclic extension of odd degree preserves
irreducibility in dimension two. Their conductor exponents are equal in the Galois
setting, but are not determined by the downstairs exponent alone.

Follow $w_1$ through a prime tower. One global step may split the chosen place, while
another supplies the totally ramified cubic local extension. Reversing the order in a
different tower changes this history but not the final subgroup $W_{E_{w_1}}$.
Transitivity therefore gives the same component, conductor, and local type.

At an archimedean place of a totally real degree-six extension, the corresponding
decomposition data are $g_v=6$ and local degree one. The real component is repeated
six times. This contrast with the ramified finite place shows why a global degree is
only an accounting identity, not a local transfer rule.

## 13. Totally real ascent and descent in modularity arguments

### 13.1 Why totally real towers are especially clean at infinity

Let $F$ and $E$ be totally real and let $E/F$ be solvable Galois. Every intermediate
field is totally real. At each archimedean place the local extension is split:
$E_w=F_v=\mathbb R$. Consequently a cohomological real component is repeated without
a real-to-complex conversion, and algebraic weights simply pull back along embeddings.

This makes the finite places the only source of changing local type. It does not make
cuspidality automatic: a totally real extension can contain quadratic fields from
which $\pi$ is automorphically induced. Nor does it remove descent ambiguity. Finite
order norm characters can be ramified at finite places and can change the downstairs
level while leaving the upstairs representation fixed.

The usefulness of solvable base change in modularity arguments comes from combining
three facts: regular algebraic weights survive ascent, all local parameters are
controlled, and strong multiplicity one recognizes invariance and the correct twist
from Frobenius data.

### 13.2 The automorphic ascent criterion

**Theorem 13.1 (totally real solvable ascent).** Let $E/F$ be a finite solvable
Galois extension of totally real number fields equipped with an ascent-admissible
composition tower, and let $\pi$ be a regular algebraic selected,
trace-comparable cuspidal automorphic representation of
$\mathrm{GL}_2(\mathbb A_F)$. Then
$\operatorname{BC}_{E/F}(\pi)$ is regular algebraic automorphic and is characterized
at every place by restriction of local parameters. Its weights are the pullbacks of
those of $\pi$, its central character is $\omega_\pi\circ N_{E/F}$, and its finite
level is given by the restricted conductor exponents.

It is cuspidal if and only if no intermediate cuspidal lift has the quadratic
norm self-twist belonging to the next layer of a prime cyclic tower. If it is
noncuspidal, Theorem 5.1 gives its explicit two-character decomposition from the
first bad step. A bottom-field quadratic self-twist is one sufficient failure
mechanism but is not the only one for a noncyclic Galois group.

**Proof.** Choose the given ascent-admissible prime cyclic composition tower. Cyclic base change at the first
step preserves algebraicity and pulls back the archimedean weights. Iterate. The
local parameter at the top is direct restriction, so the central character,
conductor, and local-type assertions follow. Theorem 5.1 gives the exact stepwise cusp
criterion and failure formula. Tower independence removes the composition series
from the resulting representation, although the criterion may be checked along any
chosen series. $\square$

If a two-dimensional arithmetic representation attached to $\pi$ is available and
local--global compatibility holds, its restriction to the arithmetic group of $E$
has the same good-place polynomials as $\operatorname{BC}_{E/F}(\pi)$. Thus
automorphy ascends by restriction. If that restricted arithmetic representation is
irreducible, the automorphic endpoint must be cuspidal, because an isobaric sum has a
reducible two-character parameter.

### 13.3 Descent selected by an extending arithmetic representation

The most useful descent situation contains more information than abstract Galois
invariance. Let $\ell$ be a prime, let

$$
r:G_F\longrightarrow\mathrm{GL}_2(\overline{\mathbb Q}_\ell)
$$

be a continuous semisimple representation, and suppose $r|_{G_E}$ is irreducible.
Assume a regular algebraic cuspidal representation $\Pi_E$ is associated with
$r|_{G_E}$ in the sense that their characteristic polynomials agree at all but
finitely many places. We also assume that the top representation and every downward
cyclic step are descent-admissible, as well as the standard compatibilities needed
in this criterion: the arithmetic representations associated with regular algebraic cusp
forms commute with cyclic base change and finite-order twisting, and equality of
their Frobenius polynomials implies equality after semisimplification.

The global representation $r$ supplies coherent extension data that abstract
invariance lacks. For $g\in\operatorname{Gal}(E/F)$, the representations
$r|_{G_E}$ and its conjugate are isomorphic. Hence the good-place polynomials of
$\Pi_E$ and $\Pi_E^g$ agree, and strong multiplicity one gives

$$
\Pi_E^g\cong\Pi_E.
$$

Descend through the top cyclic step to some $\Pi_{r-1}$. Its associated arithmetic
representation $r_{r-1}$ and $r|_{G_{F_{r-1}}}$ have isomorphic restrictions to
$G_E$. The following elementary form of Clifford theory selects the correct twist.

**Lemma 13.2 (extension comparison).** Let $H\triangleleft J$ with finite abelian
quotient. If two irreducible representations $V,V'$ of $J$ have isomorphic
irreducible restrictions to $H$, then

$$
V'\cong V\otimes\chi
$$

for a character $\chi$ of $J/H$.

**Proof.** The space $\operatorname{Hom}_H(V,V')$ is one-dimensional by Schur's
lemma. Conjugation by $J$ acts on this line through a character trivial on $H$.
An $H$-intertwiner, adjusted by that character, becomes a $J$-intertwiner. $\square$

Apply the lemma with the arithmetic groups belonging to the cyclic step. The quotient
character corresponds by class field theory to an element of the step group $X_r$.
Twisting $\Pi_{r-1}$ by its inverse gives a descent whose associated arithmetic
representation is $r|_{G_{F_{r-1}}}$. This chosen descent is invariant under the next
cyclic action because $r$ extends farther down. Repeat.

### 13.4 A practical solvable modularity descent theorem

**Theorem 13.3 (descent with a compatible extension).** Under the hypotheses of
Section 13.3, there is a regular algebraic cuspidal automorphic representation
$\pi$ of $\mathrm{GL}_2(\mathbb A_F)$ such that

$$
\operatorname{BC}_{E/F}(\pi)\cong\Pi_E
$$

and the arithmetic representation associated with $\pi$ is isomorphic to $r$ after
semisimplification. The algebraic weights of $\Pi_E$ must, and then do, descend to
those of $\pi$.

**Proof strategy.** Strong multiplicity one turns the conjugation symmetry of $r|_{G_E}$
into automorphic invariance. Cyclic descent gives an arbitrary preimage. The extension
comparison lemma finds the unique quotient-character correction making its arithmetic
representation equal to the restriction of $r$. That correction forces invariance at
the next layer. Induct down the solvable tower.

**Proof.** Choose a prime cyclic composition tower. The argument of Section 13.3
produces a corrected cuspidal descent $\Pi_{r-1}$ associated with
$r|_{G_{F_{r-1}}}$. Irreducibility of $r|_{G_E}$ implies irreducibility of its
restriction viewed at every larger arithmetic group, so the extension comparison
lemma remains applicable. Inductively construct $\Pi_i$ associated with
$r|_{G_{F_i}}$. At the bottom put $\pi=\Pi_0$. Transitivity gives the asserted base
change, and equality of good-place characteristic polynomials plus semisimplicity
identifies its associated representation with $r$. Finite-order quotient twists do
not alter algebraic weights, so the weights descend throughout. $\square$

The irreducibility hypothesis is structural. If $r|_{G_E}$ is reducible, the top
automorphic representation can be isobaric and extension fibers can have non-scalar
endomorphisms. The one-character correction in Lemma 13.2 may no longer describe all
choices. Such cases require the explicit two-character and automorphic-induction
analysis of Section 7.4.

### 13.5 Local conditions in ascent and descent

Suppose a modularity argument prescribes behavior at a finite set $S$ of places of
$F$. On ascent, for every $w\mid v\in S$, restrict the full local parameter. This
preserves sphericality and Steinberg monodromy, can split a supercuspidal, and changes
conductor according to ramification restriction. A place that splits completely is
especially useful because the local representation is unchanged at every $w$.

On descent, the top local parameter usually admits several extensions. The compatible
global arithmetic representation in Theorem 13.3 selects the extension with the
desired determinant, inertial type, and Frobenius eigenvalues. Twisting by a norm
character can change the downstairs conductor, so a claim about minimal level must
identify the selected twist rather than merely assert existence of some descent.

If a quaternion algebra is used to impose or remove discrete-series conditions,
Chapter 11 applies within its selected, totally definite parallel-weight-two range.
The split-side solvable base change must remain cuspidal, and the descent selected at
the bottom must be discrete at every place ramified in the chosen quaternion algebra.
These are explicit local and self-twist checks, not automatic consequences of
solvability.

This theorem is the precise amount of solvable descent needed in many modularity
arguments: it moves an already identified automorphic system down a solvable totally
real extension. It does not construct auxiliary fields, prove potential automorphy,
or establish a modularity lifting theorem.

### 13.6 Descent from automorphic data alone

An extending arithmetic representation is a powerful sufficient source of coherence,
but it is not part of the definition of solvable descent. One can work purely
automorphically when the necessary torsor actions are known.

Let $\Pi_E$ be regular algebraic cuspidal over a totally real solvable Galois
extension. First compare its conjugates at good places to prove the invariance needed
for the top cyclic step. Enumerate the finite cyclic descent fiber. Archimedean weights
eliminate descents with the wrong algebraic normalization, the desired central
character imposes the square-class condition, and prescribed finite local types
eliminate twists with the wrong localization. Test the retained descents for
invariance under the next cyclic group and descend again. When the adjacent composite
is Galois, this can be organized as the fixed-point calculation on one torsor from
Section 8.2.

This process can prove descent without mentioning an arithmetic representation. What
it cannot do is infer coherence merely from the equality of top Hecke eigenvalues.
One must establish an invariant choice at each stage, using a quotient action only
where it is actually defined. The arithmetic representation in Theorem 13.3 packages
exactly those extra choices into a single object over $F$.

If the top is isobaric, descend the unordered character multiset. Constituentwise
invariance gives an isobaric descent; transitive exchange across a quadratic layer
gives a cuspidal automorphic induction. Repeated constituents require their
multiplicity action. These are the same cases as in cyclic descent, iterated with the
coherence checks of Chapter 8.

## 14. The final theorem package

### 14.1 Solvable base change: existence and normalization

**Theorem 14.1 (solvable base change for $\mathrm{GL}_2$).** Let $F$ be a number
field, let $E/F$ admit an ascent-admissible tower of cyclic extensions, and let
$\pi$ be a selected, trace-comparable cuspidal automorphic representation of
$\mathrm{GL}_2(\mathbb A_F)$. Use geometric reciprocity, geometric Frobenius,
normalized parabolic induction, and the convention
that twists act through the determinant. Then there exists a unique automorphic
isobaric representation

$$
\Pi=\operatorname{BC}_{E/F}(\pi)
$$

with the following properties.

1. For every place $v$ of $F$ and $w\mid v$ of $E$,

   $$
   \operatorname{rec}_{E_w}(\Pi_w)
   =\operatorname{rec}_{F_v}(\pi_v)|_{W_{E_w}},
   $$

   with the monodromy operator unchanged.

2. The construction is independent of the admissible cyclic tower, its prime
   refinement, local paths of places, and cyclic generators. It is transitive in
   intermediate fields.
   Here transitivity means that for $F\subset L\subset E$ it applies whenever
   $L/F$ and $E/L$ admit compatible admissible cyclic towers defining both sides. If $E/F$ is
   Galois, $\Pi$ is invariant under $\operatorname{Gal}(E/F)$ as an isomorphism
   class.

3. It satisfies

   $$
   \omega_\Pi=\omega_\pi\circ N_{E/F}.
   $$

   Whenever the twisted source remains admissible,

   $$
   \operatorname{BC}(\pi\otimes\mu)
   =\Pi\otimes(\mu\circ N_{E/F}),
   \qquad
   \operatorname{BC}(\pi^\vee)=\Pi^\vee.
   $$

4. At a good finite place its Satake pair is

   $$
   \{\alpha_v^{f(w/v)},\beta_v^{f(w/v)}\}.
   $$

   Conductors, levels, local types, and local factors are computed from the complete
   restricted parameter, not from the total extension degree.

5. Algebraic and cohomological weights pull back along embeddings. Algebraic
   conjugation commutes with base change, and
   $\mathbb Q(\Pi)\subseteq\mathbb Q(\pi)$ in algebraic normalization.

6. Base change commutes with quadratic automorphic induction by the Mackey formulas
   of Chapter 6. In the selected, totally real, totally definite
   parallel-weight-two range of Chapter 11, if $D/F$ is quaternionic,
   $\pi=\operatorname{JL}_{D/F}(\rho)$, and the endpoint is cuspidal, then it is
   discrete at every place ramified in $D_E=D\otimes_FE$ and is the
   Jacquet--Langlands transfer of the inner-form base change defined in Chapter 11.
   In a non-Galois cyclic tower, the corresponding commuting statement requires the
   restricted parameter to remain discrete at every ramified place of $D_E$.

**Proof.** Refine the given admissible cyclic tower to prime steps. Extend the cyclic operation to
two-character isobaric sums and iterate, proving existence. Transitivity of local
parameter restriction gives the component in part 1. Strong multiplicity one gives
uniqueness and tower independence. Determinants, tensor products, duals, conductors,
and archimedean exponents commute with restriction, proving parts 3--5. Mackey theory
and the common local parameter for the split and inner forms prove part 6. $\square$

### 14.2 Cuspidality, isobaric failure, and fibers

**Theorem 14.2 (cuspidality and ambiguity).** Assume in addition that $E/F$ is
solvable Galois with group $G$, that the displayed composition towers are
ascent-admissible, and, for assertions about complete fibers, that source fibers are
saturated. Put

$$
X(E/F)=\widehat{C_F/N_{E/F}(C_E)}
\cong\widehat{G^{\mathrm{ab}}}.
$$

Then:

1. Along any ascent-admissible prime cyclic composition tower, the endpoint is
   cuspidal if and only if every intermediate cuspidal representation has no
   nontrivial self-twist belonging
   to the next step group. The first failure occurs at a quadratic step and gives

   $$
   \operatorname{BC}_{E/F}(\pi)
   =(\theta\circ N_{E/F_i})
   \boxplus(\theta^\tau\circ N_{E/F_i})
   $$

   for the inducing character at that first bad step.

2. A nontrivial bottom-field self-twist in $X(E/F)$ is quadratic and is sufficient
   for failure. It cuts out a quadratic $M/F$ inside $E$, gives
   $\pi=\operatorname{AI}_{M/F}(\vartheta)$, and yields

   $$
   (\vartheta\circ N_{E/M})
   \boxplus(\vartheta^\tau\circ N_{E/M}).
   $$

   For a noncyclic $G$ the converse need not follow from the bottom character group
   when the endpoint is a repeated pair. If a compatible global Weil or arithmetic
   parameter is supplied, a nontrivial projective multiplicity action measured in
   $H^2(G,k^\times)$, for its algebraically closed coefficient field $k$, explains
   how the bottom parameter can remain irreducible. Without such a parameter, the
   unconditional assertion is only the stepwise criterion in part 1.

3. If two cuspidal sources have the same cuspidal endpoint, they differ by a unique
   member of $X(E/F)$. Thus a nonempty descent fiber of a cuspidal endpoint is an
   $X(E/F)$-torsor.

4. At a noncuspidal endpoint the twisting orbit has stabilizer

   $$
   S_E(\pi)=\{\chi\in X(E/F):\pi\otimes\chi\cong\pi\},
   $$

   and contains $|X(E/F)|/|S_E(\pi)|$ distinct sources. Reducible extension data must
   be retained if one asks for the entire fiber beyond that orbit.

5. Relative to one descent with central character $\omega_0$, a prescribed norm
   antecedent $\omega$ occurs exactly when
   $\omega/\omega_0\in X(E/F)^2$. If it occurs, fixed-central-character descents form
   a torsor under $X(E/F)[2]$.

**Proof.** The first bad step in a prime tower must be quadratic. Quadratic self-twist
theory identifies it with automorphic induction and gives the isobaric formula.
If a bottom self-twist exists, the same cyclic argument can be applied directly to its
quadratic fixed field. In the other direction, a repeated endpoint need not produce
a bottom character; a supplied parameter can account for this through a projective
$G$-action. Compatible cyclic fiber characters assemble exactly into characters of
$G^{\mathrm{ab}}$; strong multiplicity one identifies the global twists. Central
characters change by squares.
$\square$

### 14.3 Solvable descent: existence and obstruction

**Theorem 14.3 (solvable cuspidal descent).** Let

$$
F=F_0\subset F_1\subset\cdots\subset F_r=E
$$

be a prime cyclic tower and let $\Pi$ be a selected, trace-comparable cuspidal
automorphic representation over $E$. Assume every step under consideration is
descent-admissible. Then $\Pi$ descends admissibly to $F$ if and only if there is a
chain of admissible cuspidal representations $\Pi_i$
with $\Pi_r=\Pi$ such that

$$
\Pi_i^\sigma\cong\Pi_i
\qquad
(\sigma\in\operatorname{Gal}(F_i/F_{i-1}))
$$

and

$$
\operatorname{BC}_{F_i/F_{i-1}}(\Pi_{i-1})\cong\Pi_i
$$

at every step. Each invariant step has a nonempty cyclic descent fiber; the condition
is that one can choose a member invariant at the next step.

For two consecutive cyclic layers whose composite $M/K$ is Galois and whose first
descent fiber is saturated, the obstruction
to such a choice is the class

$$
[c]\in H^1(Q,X(M/L))
$$

constructed from the action of the next quotient $Q$ on the first descent torsor. If
an invariant irreducible global Weil or arithmetic parameter with scalar
endomorphisms is supplied, its extension problem also has the projective class

$$
[a]\in H^2(\operatorname{Gal}(E/F),k^\times),
$$

where $k$ is its algebraically closed coefficient field. An extension of that
parameter makes this class vanish. For the automorphic representation alone, the
unconditional criterion is recursive choice of a compatible chain. The displayed
$H^1$ fixed-point class applies only when the stated quotient action on one torsor
exists; a general subnormal tower need not provide such an action at every
transition. At one step, cyclic invariance together with the antecedent-complete
selected local extension fibers and comparison hypotheses is sufficient. Full
invariance under a noncyclic solvable group should not be substituted for the
compatible-chain condition.

If one descent of a cuspidal $\Pi$ exists, $E/F$ is Galois, and the source fiber is
saturated, all admissible descents form an $X(E/F)$-torsor. The existence statement
is independent of the tower, although the recursive tests, and any obstruction
classes that are defined, present it differently.

**Proof.** Apply cyclic descent recursively. Whenever the next quotient acts on a
free cyclic descent fiber, that action produces the displacement cocycle and a fixed
point is exactly a vanishing cohomology class. Without such an action, directly test
the finitely many cyclic descents for invariance at the next step. When a compatible
parameter is present, its scalar intertwiners produce the stated $H^2$ factor set.
Conversely, a compatible chain composes by transitivity to an $F$-descent. Comparing
two complete chains forces their compatible step twists to assemble into a character
of the endpoint abelianization. $\square$

### 14.4 Totally real and inner-form refinements

**Theorem 14.4 (arithmetic refinements).** Let $E/F$ be solvable Galois and totally
real, and impose the ascent- or descent-admissibility hypotheses of Section 1.4 on
every cyclic step used below.

1. Regular algebraic cuspidal automorphy ascends to $E$, with pulled-back weights and
   exact local restriction. Its exact cusp criterion is the stepwise condition of
   Theorem 14.2. A repeated-character endpoint is handled unconditionally by that
   criterion and admits the projective interpretation only when a compatible
   parameter is supplied.

2. A regular algebraic cuspidal representation over $E$ descends automorphically if
   it admits a compatible cyclic descent chain. If it is associated with the
   irreducible restriction of a two-dimensional arithmetic representation already
   defined over $F$, and the standard base-change and twisting compatibilities hold,
   that arithmetic extension selects the compatible twists and hence supplies such a
   chain.

3. If $D/F$ is quaternionic and the split-side solvable base change is cuspidal,
   Jacquet--Langlands commutes with base change to $D_E$ in the selected, totally
   definite parallel-weight-two range of Chapter 11. On descent, the selected split
   representation must be discrete series at every place ramified in $D$.

4. Prescribed levels and local conditions must be checked on restricted or extended
   local parameters. Solvability alone does not preserve minimal conductor, prevent a
   supercuspidal from splitting, choose a fixed central character, or remove the
   noncuspidal automorphic-induction boundary.

**Proof.** Part 1 is Theorems 13.1 and 14.2, with weights and local components
carried by parameter restriction. Part 2 combines Theorem 13.3 with the recursive
criterion of Theorem 14.3. Part 3 is Proposition 11.1 together with Section 11.4.
The placewise assertions in part 4 are the calculations of Chapters 3, 4, 10, and
12. $\square$

The theorem is a transfer tool, not a construction of auxiliary extensions or a
modularity lifting argument. Its hypotheses isolate exactly what later applications
must verify.

### 14.5 Failure modes at a glance

The theory has a short list of precise failure modes.

- **Wrong variance.** Characters pull back by $N_{E/F}$ while parameters restrict
  from $W_F$ to $W_E$. Scalar inclusion is not a replacement for the norm.

- **Wrong Frobenius power.** At an unramified $w\mid v$, the geometric-Frobenius
  Satake roots are raised to $f(w/v)$. Ramification index and total global degree do
  not replace the residue degree.

- **Hidden noncuspidality.** At the first bad quadratic tower step, a self-twist turns
  the intermediate cusp form into an explicit two-character isobaric sum. For a
  noncyclic endpoint this symmetry need not descend to a bottom-field character; a
  repeated pair can have a projective multiplicity interpretation when a compatible
  parameter is supplied. Local supercuspidality is not the criterion.

- **Overcounted fibers.** The endpoint ambiguity for a cuspidal Galois descent is
  $\widehat{G^{\mathrm{ab}}}$, not the product of all cyclic-step groups. At an
  isobaric endpoint one must divide by self-twist stabilizers and retain reducible
  extension data.

- **Center mistaken for descent.** An invariant central character can have several
  norm antecedents, only one square class of which may occur. Even the correct center
  does not remove a noncyclic coherence obstruction.

- **Invariance mistaken for coherence.** In the admissible cyclic range, invariance
  is sufficient for one descent step. For a noncyclic solvable group, compatible choices in the successive
  descent fibers are additionally required. These are fixed points only at
  transitions where the next quotient acts on the same torsor.

- **Level guessed from ideals.** Conductors are Artin conductors of restricted local
  parameters. They are not obtained uniformly by extending an ideal or multiplying
  by a discriminant.

- **Inner-form boundary ignored.** In the selected, totally definite
  parallel-weight-two range, Jacquet--Langlands commutes with solvable base change
  while the split endpoint remains cuspidal. A two-character endpoint does not come
  from a noncharacter representation on a nonsplit quaternion algebra.

Each failure has appeared as the negation of a proved hypothesis. None is an
unspecified exceptional case.

## 15. Conclusion: one canonical ascent, compatible choices downward

Solvable base change is constructed from cyclic base change, but its final form is not
an arbitrary composite. At every place it restricts one Weil--Deligne parameter from
$W_{F_v}$ to $W_{E_w}$. Restriction is transitive, norm pullback is transitive, and
strong multiplicity one turns those local identities into a tower-independent global
representation. This proves a canonical ascent through every admissible cyclic tower.

The decomposition of places remains visible in the answer. Split places repeat a
component. At an unramified field place geometric Frobenius raises Satake roots to
the residue degree. At ramified places the inertia group shrinks, breaks are
reindexed, and monodromy persists. Real places either repeat real components or expose
the two characters of a real parameter over $\mathbb C$. Conductors, levels, local
types, epsilon factors, weights, and rationality fields all follow from these exact
local operations rather than from the degree of the global extension.

Cuspidality has one rank-two mechanism of failure. At the first bad cyclic step a
quadratic norm character stabilizes the cusp form. Quadratic automorphic induction
then identifies that intermediate source and restriction exposes two character lines.
For a noncyclic Galois endpoint the symmetry need not descend to a quadratic character
of the bottom field. A repeated pair can carry a nontrivial projective multiplicity
action when a compatible global parameter is present; without one, the prime-tower
criterion is the exact automorphic formulation. The final isobaric decomposition is
explicit, and once this boundary is crossed no later base change returns to the
cuspidal spectrum.

Descent reverses the arrows but not the logic. An admissible cyclic invariant cusp form descends,
and its descents form a norm-character torsor. Through a solvable tower, one must pick
a member of each cyclic descent fiber that is invariant at the next layer. When the
next quotient acts on the same torsor, its displacement gives an $H^1$ obstruction;
otherwise the finite recursive invariance test remains primary. Intertwiners of a
supplied compatible parameter reveal its projective $H^2$ extension obstruction.
When a full descent exists, the compatible stepwise ambiguities collapse to the
characters of the endpoint abelianization. Their squares, not the characters
themselves, control prescribed central characters.

These distinctions make the theory usable. Strong multiplicity one recognizes an
ascent or an invariant conjugate from good-place data. A compatible arithmetic
representation over the bottom field selects the correct twists and makes solvable
descent effective over totally real fields. Automorphic induction explains the exact
cuspidal boundary, while in the selected totally definite parallel-weight-two range
Jacquet--Langlands commutes wherever that boundary has not been crossed. The resulting
package moves automorphy upward canonically and downward under explicit, checkable
coherence conditions, with every ambiguity and failure mode accounted for.
