# Cyclic Base Change: Local Theory

## Contents

1. [The local transfer problem](#1-the-local-transfer-problem)
   - [Why extension of scalars is not literal](#11-why-extension-of-scalars-is-not-literal)
   - [Standing notation and the normalization ledger](#12-standing-notation-and-the-normalization-ledger)
   - [The shape of the answer](#13-the-shape-of-the-answer)
2. [Weil groups and their linear representations](#2-weil-groups-and-their-linear-representations)
   - [From the absolute Galois group to the Weil group](#21-from-the-absolute-galois-group-to-the-weil-group)
   - [Inertia and geometric Frobenius](#22-inertia-and-geometric-frobenius)
   - [Restriction along a finite extension](#23-restriction-along-a-finite-extension)
   - [Characters and the norm direction](#24-characters-and-the-norm-direction)
3. [Weil--Deligne representations in dimension two](#3-weil--deligne-representations-in-dimension-two)
   - [Why monodromy must be retained](#31-why-monodromy-must-be-retained)
   - [Classification of the two-dimensional shapes](#32-classification-of-the-two-dimensional-shapes)
   - [Duals, twists, and determinants](#33-duals-twists-and-determinants)
   - [Conductors and local factors](#34-conductors-and-local-factors)
4. [The rank-two local parameter dictionary](#4-the-rank-two-local-parameter-dictionary)
   - [What the dictionary must distinguish](#41-what-the-dictionary-must-distinguish)
   - [Principal series and determinant characters](#42-principal-series-and-determinant-characters)
   - [Special representations and monodromy](#43-special-representations-and-monodromy)
   - [Selected supercuspidals and irreducible Weil representations](#44-selected-supercuspidals-and-irreducible-weil-representations)
   - [The selected theorem and normalization checks](#45-the-selected-theorem-and-normalization-checks)
5. [Definition and canonicity of local base change](#5-definition-and-canonicity-of-local-base-change)
   - [Restriction is the construction](#51-restriction-is-the-construction)
   - [Independence of embeddings and representatives](#52-independence-of-embeddings-and-representatives)
   - [Central characters, twists, and contragredients](#53-central-characters-twists-and-contragredients)
   - [Transitivity in towers](#54-transitivity-in-towers)
6. [Unramified base change and spherical calculations](#6-unramified-base-change-and-spherical-calculations)
   - [Frobenius is raised to the residue degree](#61-frobenius-is-raised-to-the-residue-degree)
   - [Satake parameters and Hecke operators](#62-satake-parameters-and-hecke-operators)
   - [A recursive Hecke formula](#63-a-recursive-hecke-formula)
   - [What unramified base change does not preserve](#64-what-unramified-base-change-does-not-preserve)
7. [Principal, character, and special representations](#7-principal-character-and-special-representations)
   - [Restriction of a split parameter](#71-restriction-of-a-split-parameter)
   - [The reducibility boundary after base change](#72-the-reducibility-boundary-after-base-change)
   - [Steinberg twists and preserved monodromy](#73-steinberg-twists-and-preserved-monodromy)
   - [Three counterexamples to naive rules](#74-three-counterexamples-to-naive-rules)
8. [Dihedral supercuspidals and Mackey restriction](#8-dihedral-supercuspidals-and-mackey-restriction)
   - [Admissible quadratic pairs](#81-admissible-quadratic-pairs)
   - [The disjoint case](#82-the-disjoint-case)
   - [The contained quadratic field](#83-the-contained-quadratic-field)
   - [The exact cuspidality criterion](#84-the-exact-cuspidality-criterion)
9. [Discrete parameters and cyclic parity](#9-discrete-parameters-and-cyclic-parity)
   - [Clifford theory under a cyclic subgroup](#91-clifford-theory-under-a-cyclic-subgroup)
   - [The selected cuspidality criterion](#92-the-selected-cuspidality-criterion)
   - [The discrete-to-principal boundary](#93-the-discrete-to-principal-boundary)
10. [Ramification and conductor change](#10-ramification-and-conductor-change)
    - [Inertia restriction and upper numbering](#101-inertia-restriction-and-upper-numbering)
    - [Exact break formulas and inequalities](#102-exact-break-formulas-and-inequalities)
    - [The different and the induction formula](#103-the-different-and-the-induction-formula)
    - [Unramified, tame, and monodromic cases](#104-unramified-tame-and-monodromic-cases)
11. [Local factors under cyclic base change](#11-local-factors-under-cyclic-base-change)
    - [Factors of a restricted parameter](#111-factors-of-a-restricted-parameter)
    - [Induction, restriction, and the product formula](#112-induction-restriction-and-the-product-formula)
    - [Epsilon factors and additive characters](#113-epsilon-factors-and-additive-characters)
    - [Consequences for conductors and root numbers](#114-consequences-for-conductors-and-root-numbers)
12. [Galois invariance, descent, fibers, and image](#12-galois-invariance-descent-fibers-and-image)
    - [Why every lift is Galois invariant](#121-why-every-lift-is-galois-invariant)
    - [Extending an invariant parameter](#122-extending-an-invariant-parameter)
    - [The twisting ambiguity and its limit](#123-the-twisting-ambiguity-and-its-limit)
    - [The exact image and fiber criterion](#124-the-exact-image-and-fiber-criterion)
13. [Compatibility with local Jacquet--Langlands](#13-compatibility-with-local-jacquet--langlands)
    - [One parameter for two inner forms](#131-one-parameter-for-two-inner-forms)
    - [The quaternion invariant after scalar extension](#132-the-quaternion-invariant-after-scalar-extension)
    - [Odd degree, even degree, and the boundary](#133-odd-degree-even-degree-and-the-boundary)
    - [Verification of the compatibility square](#134-verification-of-the-compatibility-square)
14. [Explicit calculations](#14-explicit-calculations)
    - [An unramified cubic lift](#141-an-unramified-cubic-lift)
    - [A ramified quadratic collapse](#142-a-ramified-quadratic-collapse)
    - [A Steinberg calculation](#143-a-steinberg-calculation)
    - [A dihedral supercuspidal that splits](#144-a-dihedral-supercuspidal-that-splits)
    - [A dihedral supercuspidal that remains cuspidal](#145-a-dihedral-supercuspidal-that-remains-cuspidal)
15. [The local theorem package](#15-the-local-theorem-package)
    - [The cyclic base-change theorem](#151-the-cyclic-base-change-theorem)
    - [A calculation protocol](#152-a-calculation-protocol)
    - [Conclusion](#153-conclusion)

## 1. The local transfer problem

### 1.1 Why extension of scalars is not literal

Let $L/K$ be a finite cyclic extension of nonarchimedean local fields. A matrix in
$\mathrm{GL}_2(K)$ can of course be regarded as a matrix in $\mathrm{GL}_2(L)$, but a
smooth representation of the first group cannot simply be extended coefficient by
coefficient to a representation of the second. The second group is much larger, and
restriction of a group action goes in the opposite direction. Local base change solves
this directional problem: it transports the arithmetic information carried by an
irreducible smooth representation of $\mathrm{GL}_2(K)$ to the corresponding
information over $L$.

The right intermediate object is a two-dimensional representation of a local Weil
group, sometimes equipped with a nilpotent operator. Weil groups do admit a natural
inclusion

$$
W_L\hookrightarrow W_K.
$$

Thus the desired transfer becomes ordinary restriction. This does not trivialize the
theory. One must invoke the local parameter correspondence that canonically attaches a
selected parameter to a smooth representation, check that restriction preserves the
relation defining monodromy, prove that the restricted parameter remains in the
selected range, and then use the correspondence over $L$ to return to one and only one irreducible
representation of $\mathrm{GL}_2(L)$. One must also translate
restriction back into visible
representation theory: Frobenius eigenvalues, principal-series inducing characters,
Steinberg monodromy, supercuspidality, conductors, epsilon factors, and inner-form
transfer.

There are two reasons to develop all of this locally. First, the ramified places are
exactly where a list of good-place Hecke eigenvalues says least. Second, a global
base-change construction must know in advance what its local components are supposed
to be. No global theorem will be used to justify the construction in this book.

### 1.2 Standing notation and the normalization ledger

Write

$$
\mathcal O_K,\quad \mathfrak p_K=(\varpi_K),\quad k_K,
\quad q_K=|k_K|,
$$

and normalize $v_K(\varpi_K)=1$ and $|x|_K=q_K^{-v_K(x)}$. Put
$n=[L:K]$, $e=e(L/K)$, and $f=f(L/K)$, so $n=ef$ and
$q_L=q_K^f$. The Galois group $\Gamma=\operatorname{Gal}(L/K)$ is
cyclic. Representations and parameters have complex coefficients. This is the
coefficient field of the selected correspondence established earlier and keeps the
analytic local factors in the same category. The restriction, Mackey, and Clifford
arguments remain valid over any algebraically closed characteristic-zero field
containing the required values and square roots, but no coefficient-extension theorem
is needed here.

We use normalized parabolic induction. Thus

$$
I_K(\chi_1,\chi_2)
=\operatorname{Ind}_{B(K)}^{\mathrm{GL}_2(K)}
(\chi_1\boxtimes\chi_2)
$$

includes the factor $\delta_B^{1/2}$ in its covariance law. Local reciprocity is
geometrically normalized:

$$
\operatorname{rec}_K(\varpi_K)=\operatorname{Fr}_K,
$$

where $\operatorname{Fr}_K$ is a lift of geometric Frobenius, the inverse of the
$q_K$-power automorphism on the residue algebraic closure. If $w$ maps to
$\operatorname{Fr}_K^m$ modulo inertia, define

$$
\lVert w\rVert_K=q_K^{-m}.
$$

Consequently $\lVert\operatorname{Fr}_K\rVert_K=q_K^{-1}$. This is the convention in
which the tame-monodromy relation has the factor $q_K^{-1}$ and an unramified
character takes $\operatorname{Fr}_K$ to its value on $\varpi_K$.

For a character $\chi$ of $K^\times$, the same symbol $\chi$ will denote the Weil
character $\chi\circ\operatorname{rec}_K^{-1}$. Context always determines the side.
Twisting a representation of $\mathrm{GL}_2(K)$ by $\chi$ means twisting by
$\chi\circ\det$. Additive characters are displayed in epsilon factors; none is
silently fixed.

This matches the normalized induction and Whittaker conventions of Book 78, the selected
parameter dictionary of Book 81, and the local inner-form conventions of Book 85. Book 5 states local class field theory with
arithmetic Frobenius; inverting both horizontal reciprocity maps converts its
norm--inclusion square to the geometric convention used here. The norm direction and
all kernels are unchanged by this simultaneous inversion.

### 1.3 The shape of the answer

Let $\operatorname{Irr}_{\mathrm{sel}}\mathrm{GL}_2(K)$ consist of determinant
characters, irreducible principal series, special representations, and the tame
dihedral supercuspidals covered by the selected local correspondence. The smooth
transfer constructed in this book will be denoted

$$
\operatorname{BC}_{L/K}:
\operatorname{Irr}_{\mathrm{sel}}\mathrm{GL}_2(K)
\longrightarrow
\operatorname{Irr}_{\mathrm{sel}}\mathrm{GL}_2(L).
$$

Its definition has only three symbols. If $\operatorname{rec}_K(\pi)$ is the
Weil--Deligne parameter of $\pi$, then

$$
\operatorname{rec}_L(\operatorname{BC}_{L/K}\pi)
=\operatorname{Res}^{W_K}_{W_L}\operatorname{rec}_K(\pi).
$$

Every principal, character, and special parameter remains selected. For a tame
dihedral parameter, a quadratic field either splits after scalar extension or remains
an unramified or tamely ramified quadratic field. The evident norm-pulled character
can fail the chosen-pair admissibility condition even when it remains regular. That
does not make the parameter unselected: in precisely that exceptional ramified case
its projective image is Klein four, and the same irreducible parameter has an
admissible presentation from the unramified quadratic extension. Chapter 8 proves
this relabeling instead of mistaking failure of one label for failure of the local
correspondence.

The substance lies in making every term and every consequence precise. Restriction can
turn an irreducible two-dimensional Weil representation into a sum of characters, so
a selected supercuspidal representation can become principal series. It cannot erase
a nonzero monodromy operator, so a Steinberg twist remains special. For an unramified
extension, geometric Frobenius is raised to the residue degree. For a ramified extension, inertia
gets smaller and its numbering changes; conductor behavior therefore involves both
new fixed vectors and the Herbrand reindexing.

Two further phenomena will matter later. The lifted representation is invariant under
$\Gamma$, but descent is not unique: characters of $K^\times/N_{L/K}L^\times$ act on
the set of descents. And local Jacquet--Langlands is compatible with the same
restriction operation, although a quaternion division algebra can split after scalar
extension. These are not decorative compatibilities. They are the local bookkeeping
needed to assemble global cyclic base change.

## 2. Weil groups and their linear representations

### 2.1 From the absolute Galois group to the Weil group

The absolute Galois group $G_K$ remembers too much topology for local harmonic
analysis. Its quotient by inertia is the profinite group $\widehat{\mathbf Z}$, whereas
unramified characters of $K^\times$ vary freely with the value assigned to a
uniformizer. The Weil group replaces this profinite quotient by the dense discrete
subgroup generated by Frobenius.

Choose a separable closure $\overline K$ and write $K^{\mathrm{nr}}$ for the maximal
unramified extension inside it. The **local Weil group** is

$$
W_K=\{g\in G_K:g|_{K^{\mathrm{nr}}}
\text{ is an integral power of }\operatorname{Fr}_K\}.
$$

It fits into

$$
1\longrightarrow I_K\longrightarrow W_K
\xrightarrow{\deg_K}\mathbf Z\longrightarrow0,
$$

with $\deg_K(\operatorname{Fr}_K)=1$. Its topology makes inertia open with its profinite
topology and makes each coset of inertia open. A Weil representation is required to be
continuous and to have open kernel on inertia. Its Frobenius action need not have
finite order; this is precisely what permits arbitrary unramified quasicharacters.

Changing a lift of Frobenius multiplies it by inertia. No formula depending on the
conjugacy class of Frobenius on inertia invariants is affected. This is why local
$L$-factors use that invariant space rather than the whole representation.

It is useful to keep three groups distinct. The absolute Galois group $G_K$ is
profinite. The Weil group $W_K$ is dense in it but is not given the subspace topology;
its Frobenius quotient is discrete. The Weil--Deligne group is not a further field-
theoretic subgroup: it is a linear package that records the unipotent part of a
potentially nonsemisimple inertia action by the operator $N$. Confusing any two of
these objects leads to a different error. Continuity on $G_K$ would artificially force
unramified eigenvalues into a compact set, while forgetting $N$ would identify
Steinberg with a determinant character.

For example, choose $c\in C^\times$ of infinite order. The rule
$I_K\mapsto1$ and $\operatorname{Fr}_K\mapsto c$ is a perfectly good continuous character
of $W_K$. It extends continuously to $G_K$ only under strong topological restrictions
on $c$. This elementary example is why the Weil group, rather than the full Galois
group, is the natural recipient of arbitrary smooth unramified characters.

### 2.2 Inertia and geometric Frobenius

The exact sequence separates depth from unramified motion. The subgroup $I_K$ detects
ramification. Its wild subgroup $P_K$ and its upper-numbered filtration $I_K^u$ for
$u\ge0$ measure progressively finer depth. Geometric Frobenius conjugates tame
inertia by the inverse of the $q_K$-power action.

The normalization can be checked on a character. If $\chi$ is unramified, then

$$
\chi(\operatorname{Fr}_K)=\chi(\varpi_K).
$$

In particular, the Weil character attached to $|\cdot|_K$ takes Frobenius to
$q_K^{-1}$. Under arithmetic reciprocity the associated Weil character is inverted
when the same multiplicative label is transported. We will not switch conventions
inside a calculation.

If $V$ is a Weil representation, its Frobenius semisimplification replaces the action
of one Frobenius lift by its semisimple part while leaving inertia unchanged. Local
parameters are taken Frobenius-semisimple. This loses extension data invisible to the
irreducible smooth correspondence but retains every eigenvalue entering a local
factor.

Arithmetic and geometric Frobenius are inverses. Under the geometric reciprocity map
used here, an unramified character with value $a$ on $\varpi_K$ has value $a$ on
$\operatorname{Fr}_K$. Under arithmetic reciprocity the Weil character attached to
the same multiplicative label is its inverse. All Frobenius polynomials in this book
use $\operatorname{Fr}_K$.

### 2.3 Restriction along a finite extension

Embed $L$ in $\overline K$. Then $G_L$ and $W_L$ are subgroups of $G_K$ and $W_K$.
The key numerical compatibility is

$$
\deg_K(w)=f\deg_L(w),\qquad w\in W_L.
$$

Indeed geometric Frobenius over $L$ is the inverse $q_L$-power automorphism, hence
maps to $\operatorname{Fr}_K^f$ modulo $I_K$. It follows that

$$
\lVert w\rVert_K=q_K^{-f\deg_L(w)}
=q_L^{-\deg_L(w)}=\lVert w\rVert_L.
$$

This equality is the small calculation on which restriction of monodromy rests.

When $L/K$ is Galois, $W_L$ is normal in $W_K$ and

$$
W_K/W_L\simeq\operatorname{Gal}(L/K).
$$

For an unramified extension of degree $n$, one may choose
$\operatorname{Fr}_L=\operatorname{Fr}_K^n$. For a ramified extension only the equality modulo
inertia is canonical. An unramified parameter cannot see the inertial correction, but
a ramified one can; this is why ramified base change is not obtained merely by raising
all matrices to a power.

As a concrete ramified warning, let $L/K$ be totally ramified. Then $f=1$, so a lift
of $\operatorname{Fr}_L$ maps to the same generator as $\operatorname{Fr}_K$ modulo inertia.
Nevertheless $I_L$ is a proper subgroup of $I_K$. An unramified parameter is unchanged,
but a tamely ramified character can become trivial on the smaller inertia group. The
Frobenius exponent alone detects none of this change.

### 2.4 Characters and the norm direction

The most common directional error in base change is to use inclusion of multiplicative
groups where the norm is required. The functoriality square for geometric reciprocity
is

$$
\begin{array}{ccc}
L^\times&\xrightarrow{\operatorname{rec}_L}&W_L^{\mathrm{ab}}\\
\downarrow N_{L/K}&&\downarrow\text{inclusion}\\
K^\times&\xrightarrow{\operatorname{rec}_K}&W_K^{\mathrm{ab}}.
\end{array}
$$

Therefore restriction of the Weil character attached to $\chi:K^\times\to C^\times$
corresponds to

$$
\chi_L=\chi\circ N_{L/K}:L^\times\longrightarrow C^\times.
$$

For example,

$$
|N_{L/K}x|_K=|x|_L,
$$

so $\nu_K=|\cdot|_K$ restricts to $\nu_L$. By contrast, restricting a character as a
function from $K^\times$ to $L^\times$ is not even meaningful because the containment
goes the other way.

The norm direction also explains the finite group of descent twists. A character
$\eta$ of $K^\times$ becomes trivial after base change precisely when
$\eta(N_{L/K}x)=1$ for every $x\in L^\times$. Thus the kernel of character base change
is the dual of $K^\times/N_{L/K}L^\times$, which local class field theory identifies
with the character group of $\Gamma$.

## 3. Weil--Deligne representations in dimension two

### 3.1 Why monodromy must be retained

A Weil representation alone distinguishes principal series from supercuspidals, but it
does not distinguish the determinant character at a reducibility boundary from the
Steinberg constituent beside it. Both have the same semisimple pair of Weil
characters. The missing datum is monodromy.

A **Weil--Deligne representation** over $C$ is a pair $\Phi=(r,N)$, where $r$ is a
finite-dimensional Frobenius-semisimple representation of $W_K$, $N$ is nilpotent,
and

$$
r(w)Nr(w)^{-1}=\lVert w\rVert_K N.
$$

Equivalently, $N:r\to r\otimes\lVert\cdot\rVert_K^{-1}$ is equivariant. Because the
Weil norms agree on $W_L$, the same $N$ satisfies the defining relation after
restriction. This explains why base change restricts $r$ and leaves $N$ untouched.

The adjective **admissible** will mean that $r$ is continuous with open inertial kernel
and Frobenius-semisimple. We consider parameters up to simultaneous isomorphism of
$r$ and $N$.

The covariance relation has a useful geometric reading. Monodromy lowers Weil weight
by one norm character. In dimension two a nonzero $N$ therefore joins two lines whose
characters differ by exactly $\lVert\cdot\rVert$. An arbitrary nilpotent matrix placed
beside an arbitrary pair of characters would not define a parameter. The special
half-powers are forced by centering this ratio around the twisting character $\mu$.

Restriction does not rescale $N$. What changes under a field automorphism is the
coordinate description of Weil--Deligne data, a distinction treated in Chapter 12.
For the inclusion $W_L\subset W_K$, equality of the two Weil norms makes the original
operator satisfy the new covariance relation verbatim.

### 3.2 Classification of the two-dimensional shapes

Dimension two is small enough for an exhaustive linear-algebra classification.
The semisimplicity used here really follows from our hypotheses: inertia has finite
image, some positive power of Frobenius centralizes that image, and Frobenius
semisimplicity then decomposes the representation into irreducibles for the group
generated by the two. Thus no hidden nonsplit Weil extension supplies a fourth case.

**Proposition 3.1.** Every two-dimensional admissible Weil--Deligne representation is
of exactly one of the following forms:

1. $r=\chi_1\oplus\chi_2$ and $N=0$;
2. $r=\mu\lVert\cdot\rVert^{1/2}\oplus\mu\lVert\cdot\rVert^{-1/2}$ and $N\ne0$, with
   $N$ carrying the second line isomorphically to the first;
3. $r$ is irreducible and $N=0$.

**Proof strategy.** First split according to whether $N$ vanishes. If it does, the
semisimple Weil representation is either irreducible or a sum of characters. If it
does not, a rank-one nilpotent operator supplies a canonical flag, and the covariance
relation determines the ratio of the two characters.

**Proof.** Suppose $N\ne0$. Then $N^2=0$, while
$\ker N=\operatorname{im}N$ is a one-dimensional $W_K$-stable subspace. Let the
character on it be $\mu\lVert\cdot\rVert^{1/2}$. The quotient character is forced by
the covariance relation to be $\mu\lVert\cdot\rVert^{-1/2}$. Frobenius
semisimplicity splits $r$ into these two characters, and rescaling a basis makes the
nonzero $N$ standard. If $N=0$, semisimplicity gives the other two cases. They are
mutually exclusive by reducibility of $r$ and the vanishing of $N$. $\square$

Write $\operatorname{Sp}_2(\mu)$ for the second parameter. In a basis $e_1,e_2$,

$$
r(w)e_1=\mu(w)\lVert w\rVert^{1/2}e_1,
\quad
r(w)e_2=\mu(w)\lVert w\rVert^{-1/2}e_2,
\quad Ne_2=e_1.
$$

Notice that the direct sum with the same two characters but $N=0$ is a different
parameter. This single distinction will separate a character of the determinant from
a Steinberg twist.

The proposition also explains why monodromy never appears in a supercuspidal
parameter. If $r$ were irreducible and $N\ne0$, the nonzero proper line $\ker N$ would
be $W_K$-stable. Conversely, every nonzero-monodromy two-dimensional parameter is
indecomposable as a Weil--Deligne object even though its underlying Weil representation
is a direct sum.

### 3.3 Duals, twists, and determinants

The dual of $(r,N)$ is

$$
(r,N)^\vee=(r^\vee,-{}^tN).
$$

The minus sign makes evaluation equivariant; it has no effect on the isomorphism class
of a nonzero rank-one monodromy operator. Twisting by a character $\chi$ gives

$$
(r,N)\otimes\chi=(r\otimes\chi,N\otimes1).
$$

Both operations commute with restriction. So does determinant:

$$
\det(\operatorname{Res}_{W_L}^{W_K}r)
=(\det r)|_{W_L}.
$$

For $\operatorname{Sp}_2(\mu)$ the determinant is $\mu^2$. For a split parameter it
is $\chi_1\chi_2$. These formulas anticipate the central-character identities on
$\mathrm{GL}_2$.

### 3.4 Conductors and local factors

Let $a_K(r)$ be the Artin conductor exponent of the Weil representation. Monodromy
adds a correction invisible to $r$ alone:

$$
a_K(r,N)=a_K(r)+\dim V^{I_K}
-\dim(\ker N)^{I_K}.
$$

For an unramified $\operatorname{Sp}_2(\mu)$ this gives $1$, even though $a_K(r)=0$.
If $a_K(\mu)>0$, both character lines have no inertial invariants and
$a_K(\operatorname{Sp}_2(\mu))=2a_K(\mu)$. Thus the formula already reproduces the
special-representation conductor.

For a split parameter the conductor is additive:

$$
a_K(\chi_1\oplus\chi_2,0)=a_K(\chi_1)+a_K(\chi_2).
$$

For an irreducible $r$ it is the ordinary two-dimensional Artin conductor. These
three computations exhaust dimension two. They also show why a central character
cannot determine the conductor: $\chi_1\chi_2$ may have cancellations even while the
sum of the two conductor exponents remains large.

The standard local factor is

$$
L_K(s,(r,N))=
\det\left(1-q_K^{-s}r(\operatorname{Fr}_K)\mathbin{\big|}
(\ker N)^{I_K}\right)^{-1}.
$$

It is independent of the Frobenius lift. For a split parameter it is the product of
the character factors. For $\operatorname{Sp}_2(\mu)$ it is

$$
L_K(s+1/2,\mu),
$$

because Frobenius acts on $\ker N$ through
$\mu(\operatorname{Fr}_K)q_K^{-1/2}$. For irreducible two-dimensional $r$, inertia
invariants vanish unless $r$ is reducible, so the factor is $1$.

Given a nontrivial additive character $\psi_K$, the epsilon factor
$\epsilon_K(s,(r,N),\psi_K)$ is characterized by the local functional equation. Its
monomial exponent, when $\psi_K$ has conductor zero, is $a_K(r,N)$. We postpone the
induction and scaling formulas until Chapter 11, where the additive character can no
longer safely remain implicit.

Already one caution is worth recording. The conductor of an additive character is a
lattice index, and composing with a trace changes that lattice by the inverse
different. Consequently “take conductor-zero additive characters on both fields” and
“take trace-compatible additive characters” are generally incompatible in a ramified
extension. Local $L$-factors do not see this choice; epsilon factors do.

## 4. The rank-two local parameter dictionary

### 4.1 What the dictionary must distinguish

The classification of irreducible smooth representations of $\mathrm{GL}_2(K)$ has
four rows: determinant characters, irreducible principal series, special
representations, and supercuspidals. Proposition 3.1 has three rows because its split
row contains both the generic principal series and the nongeneric determinant
characters. Matching the two classifications requires care exactly at normalized
induction's reducibility points.

We use the selected rank-two local parameter correspondence proved in Book 81,

$$
\operatorname{rec}_K:
\operatorname{Irr}_{\mathrm{sel}}\mathrm{GL}_2(K)
\xrightarrow{\sim}
\{\text{selected two-dimensional Weil--Deligne parameters}\}.
$$

It is normalized so that geometric reciprocity identifies a character on
$K^\times$ with the same-valued Weil character and normalized principal induction
corresponds to direct sum. This formulation determines rather than conceals the
half-powers.

Here **selected** has its literal earlier meaning: split parameters, special
parameters, and irreducible inductions from tame admissible quadratic pairs. The
smooth theory from Books 78 and 79 supplies the representation-theoretic families;
Book 81 constructs this correspondence and proves its invariant and local-factor
compatibilities. Primitive wild parameters and ramified dyadic positive-depth pairs
are not smuggled into the word “selected.” What will be proved from the established
local correspondence is the local base-change theorem in exactly this range; no
global base-change theorem is being assumed.

The correspondence preserves determinant and central character, contragredients,
character twists, conductors, and standard local factors. These compatibilities are
part of the parameter dictionary, but they are not independent decorations. The four
families below show that, in rank two, they force every normalization.

Here $a_K(\pi)$ denotes the analytic conductor exponent supplied by the parameter (or,
equivalently, by the epsilon factor). For an infinite-dimensional generic
representation it agrees with the selected newvector conductor of Book 81. For a
one-dimensional representation $\mu\circ\det$, whose literal fixed-vector minimum is
not the appropriate definition, it means the parameter conductor: it is $0$ for
unramified $\mu$ and $2a_K(\mu)$ for ramified $\mu$.

One should not read $\operatorname{rec}_K$ as a recipe that replaces a representation
by a convenient list of invariants. It is a bijection of isomorphism classes with enough
structure to recover the original representation. In particular, equal $L$-factors do
not imply equal parameters: all supercuspidals have standard factor $1$, yet their
inertial actions and epsilon factors vary widely. Base change uses the full parameter.

### 4.2 Principal series and determinant characters

If

$$
\chi_1\chi_2^{-1}\ne\nu_K^{\pm1},
$$

then normalized induction is irreducible and

$$
\operatorname{rec}_K(I_K(\chi_1,\chi_2))
=(\chi_1\oplus\chi_2,0).
$$

The unordered pair of characters determines the representation. Equality
$\chi_1=\chi_2$ is harmless; the exceptional ratios are $\nu_K$ and
$\nu_K^{-1}$, not $1$.

At an exceptional ratio the induced representation has two irreducible constituents.
The semisimple parameter with zero monodromy belongs to the one-dimensional
constituent:

$$
\operatorname{rec}_K(\mu\circ\det)
=\left(
\mu\nu_K^{-1/2}\oplus\mu\nu_K^{1/2},0
\right).
$$

Thus a direct sum of characters at the boundary never denotes the reducible induced
representation itself. The correspondence is between irreducible objects.

This rule passes three immediate tests. The determinant is $\mu^2$, which is the
central character of $\mu\circ\det$. The parameter conductor is zero when $\mu$ is
unramified. And its local factor is the product of the two character factors, as
required for the spherical constituent at the boundary.

The two normalized-induction exact sequences make the boundary concrete:

$$
0\to\mu\circ\det\to
I_K(\mu\nu_K^{-1/2},\mu\nu_K^{1/2})
\to\operatorname{St}_K\otimes\mu\to0,
$$

and the reversed ordering reverses subrepresentation and quotient. The parameter
correspondence assigns parameters to the two irreducible ends, not to this nonsplit
middle object. Since swapping the inducing characters does not change the unordered
semisimple parameter, the location as subobject or quotient has no role in base
change.

### 4.3 Special representations and monodromy

The other constituent is distinguished by nonzero monodromy:

$$
\operatorname{rec}_K(\operatorname{St}_K\otimes\mu)
=\operatorname{Sp}_2(\mu).
$$

The semisimple Weil representation is the same pair of characters as above, but
$N\ne0$. Consequently an unramified Steinberg twist has conductor one and only one
Euler-factor line. This is precisely why base change must restrict a Weil--Deligne
parameter rather than only its semisimplification.

The placement of half-powers can be recovered rather than memorized. Since
$\ker N$ carries $\mu\nu_K^{1/2}$ and
$\nu_K(\operatorname{Fr}_K)=q_K^{-1}$, one obtains

$$
L_K(s,\operatorname{St}_K\otimes\mu)
=L_K(s+1/2,\mu).
$$

Reversing geometric and arithmetic Frobenius without also reversing reciprocity would
give the wrong shift.

### 4.4 Selected supercuspidals and irreducible Weil representations

In the selected correspondence, an irreducible two-dimensional Weil representation
has $N=0$ and is induced from a tame admissible quadratic pair; it corresponds to a
selected supercuspidal representation. If $E/K$ is quadratic and $\theta$ is a
character of $E^\times$ with
$\theta\ne\theta^\tau$, then

$$
r=\operatorname{Ind}_{W_E}^{W_K}\theta
$$

is irreducible and its corresponding representation is the supercuspidal attached to
the admissible pair $(E/K,\theta)$, with the usual rectification understood in the
passage between a raw compact type and the Weil character. Parameter notation avoids
mistaking a choice-dependent torus label for canonical data.

This statement is exhaustive only in the selected range. Primitive wild
supercuspidals need not have tame quadratic labels, and the prior correspondence does
not construct their parameters. Formal restriction of an arbitrary two-dimensional
Weil--Deligne representation still makes sense, but this book translates that formal
operation back to smooth representations only for the selected parameters just
listed.

For a quadratic induction the determinant includes the permutation sign:

$$
\det\operatorname{Ind}_{W_E}^{W_K}\theta
=\eta_{E/K}\,\theta|_{K^\times},
$$

where $\eta_{E/K}$ is the quadratic character attached to $E/K$ and the restriction
of $\theta$ to $K^\times$ is interpreted through reciprocity. Depending on the compact
type convention, this sign is one place where a rectifying character appears. Working
with the canonical Weil parameter ensures that the central character is its determinant
exactly, rather than the unrectified torus restriction by accident.

### 4.5 The selected theorem and normalization checks

**Theorem 4.1 (selected local parameter correspondence).** The preceding assignments
give a bijection between selected representations and selected parameters. For every
selected irreducible $\pi$,

$$
\det\operatorname{rec}_K(\pi)=\omega_\pi,
\qquad
\operatorname{rec}_K(\pi^\vee)=\operatorname{rec}_K(\pi)^\vee,
$$

$$
\operatorname{rec}_K(\pi\otimes\chi)
=\operatorname{rec}_K(\pi)\otimes\chi,
\qquad
a_K(\pi)=a_K(\operatorname{rec}_K(\pi)).
$$

The standard $L$- and epsilon factors agree on the two sides.

**Dependence on the Frobenius convention.** This is the selected theorem of Book 81
in its geometric normalization. In particular, one must not invert a Frobenius root
without also changing reciprocity and the attached Weil character. The direct-sum,
special, induction, determinant, conductor, and local-factor statements therefore
have exactly the normalization displayed here.

**Normalization check.** The elementary rows determine the convention. At
$\chi_1/\chi_2=\nu_K^{\pm1}$ the two possibilities with the same semisimple Weil
representation are $N=0$ and $N\ne0$; the spherical character constituent has
$N=0$, while the generic special constituent has $N\ne0$. Determinants, twists, and
duals are then visible in the displayed formulas, and the conductor and $L$-factor
computations agree with the newvector normalization of Book 81 and the zeta-integral normalizations of Books 78 and 79.
For an induced quadratic parameter, the permutation sign gives the correct central
character and the conductor--discriminant formula gives the correct conductor.

These checks fix which normalization of the local theorem is being used; the
existence, uniqueness, and epsilon-factor compatibility in the tame dihedral row are
the substantive results recalled from Book 81. Nothing here asserts the corresponding
claims for primitive wild packets. Since the input is wholly local, using it to define
restriction involves no circular appeal to a global base-change theorem.

## 5. Definition and canonicity of local base change

### 5.1 Restriction is the construction

We can now define the transfer promised in Chapter 1.

**Definition 5.1.** For
$\pi\in\operatorname{Irr}_{\mathrm{sel}}\mathrm{GL}_2(K)$ with
$\operatorname{rec}_K(\pi)=(r,N)$, its **local base change to $L$** is

$$
\operatorname{BC}_{L/K}(\pi)
=\operatorname{rec}_L^{-1}(r|_{W_L},N).
$$

Before accepting the definition, observe why its form is forced. Scalar extension of
one-dimensional multiplicative characters is norm pullback, and local reciprocity turns
norm pullback into Weil restriction. Direct sums, induction, determinants, and
monodromy then demand the same operation in dimension two. Any competing construction
compatible with the local parameter dictionary would give the same answer.

The defining relation for $N$ remains true because
$\lVert\cdot\rVert_K|_{W_L}=\lVert\cdot\rVert_L$. Restriction preserves open
inertial kernel. Whenever necessary, its Frobenius semisimplification is understood;
this does not change inertia, monodromy, or any local factor used here. Split and
special restrictions are visibly selected. Section 8.4 proves the only remaining
point, namely that restriction of a selected tame-dihedral parameter is again
selected even when its most obvious quadratic label is not admissible.

### 5.2 Independence of embeddings and representatives

The subgroup $W_L\subset W_K$ was obtained from an embedding
$L\hookrightarrow\overline K$. A different embedding is carried to the first by an
element $g\in W_K$ because $L/K$ is Galois. It replaces $W_L$ by
$gW_Lg^{-1}$ and the restricted parameter by

$$
w\longmapsto r(gwg^{-1}).
$$

The operator $r(g)$ intertwines this parameter with $r|_{W_L}$ and also commutes with
the transported monodromy in the required twisted sense. Hence the isomorphism class
is unchanged.

Likewise, replacing $(r,N)$ by an isomorphic parameter gives an isomorphic
restriction. The inverse parameter correspondence depends only on isomorphism class.
Thus base change is canonical as a map on isomorphism classes. It does not require a
chosen Frobenius lift, a basis, a generator of $\Gamma$, or a torus model for a
supercuspidal.

**Uniqueness consequence.** Suppose a rule from irreducible representations over $K$
to those over $L$ is compatible with the rank-two parameter correspondence and with
restriction on characters. Then it is $\operatorname{BC}_{L/K}$. Canonicity is
therefore stronger than independence of auxiliary choices: the requested
compatibility characterizes the operation.

### 5.3 Central characters, twists, and contragredients

Restriction commutes with determinant, tensor product, and dual. Translating each
operation gives three basic identities:

$$
\boxed{\ \omega_{\operatorname{BC}_{L/K}(\pi)}
=\omega_\pi\circ N_{L/K}.\ }
$$

For every character $\chi$ of $K^\times$,

$$
\boxed{\ \operatorname{BC}_{L/K}(\pi\otimes\chi)
\cong\operatorname{BC}_{L/K}(\pi)
\otimes(\chi\circ N_{L/K}).\ }
$$

And

$$
\boxed{\ \operatorname{BC}_{L/K}(\pi^\vee)
\cong\operatorname{BC}_{L/K}(\pi)^\vee.\ }
$$

The first formula is sometimes written with the norm arrow reversed. The reciprocity
square of Section 2.4 rules that out. A scalar $zI_2$ over $L$ acts on the lift through
$\omega_\pi(N_{L/K}z)$.

Twist compatibility is arbitrary, not merely unramified. It consequently includes all
possible conductor cancellation at equal depth; there is no need for a separate
minimality assumption in the identity itself.

### 5.4 Transitivity in towers

Let $K\subset L\subset M$ be finite extensions, with the relevant cyclic hypotheses
when one wants Galois invariance. In the selected families considered here every
displayed restriction remains selected by Section 8.4. Since restriction of
Weil--Deligne representations is
transitive,

$$
\boxed{\ \operatorname{BC}_{M/L}
(\operatorname{BC}_{L/K}\pi)
\cong\operatorname{BC}_{M/K}\pi.\ }
$$

On central characters this becomes the norm identity

$$
N_{M/K}=N_{L/K}\circ N_{M/L}.
$$

This tower law will later allow cyclic steps to be composed. Its proof is entirely
local and contains no assertion that a corresponding global automorphic object already
exists.

## 6. Unramified base change and spherical calculations

### 6.1 Frobenius is raised to the residue degree

Assume first that $L/K$ is unramified of degree $n$. Then $e=1$, $f=n$, inertia is
unchanged, and we may choose

$$
\operatorname{Fr}_L=\operatorname{Fr}_K^n.
$$

If $r$ is unramified with geometric-Frobenius eigenvalues $\alpha$ and $\beta$, then
$r|_{W_L}$ is unramified with eigenvalues

$$
\alpha^n,\qquad\beta^n.
$$

This is the fundamental good-place calculation. It is a power operation on
eigenvalues, not multiplication by $n$, and it uses the residue degree rather than the
ramification index.

For an unramified character $\chi$, norm pullback gives

$$
(\chi\circ N_{L/K})(\varpi_L)=\chi(\varpi_K)^n,
$$

after choosing compatible uniformizers. This is exactly the same Frobenius-power
formula in multiplicative language.

The residue degree, rather than the total degree, is the general exponent. If $L/K$
is arbitrary but $r$ is unramified, an inertial correction in a lift of
$\operatorname{Fr}_L$ is invisible to $r$, so the eigenvalues upstairs are
$\alpha^f$ and $\beta^f$. The specialization $f=n$ in this chapter occurs because
the extension itself is assumed unramified.

### 6.2 Satake parameters and Hecke operators

Let $\pi$ be spherical with Satake pair $\{\alpha,\beta\}$. Then its base change is
spherical with pair

$$
\{\alpha^n,\beta^n\}.
$$

Normalize Haar measure so
$\operatorname{vol}(\mathrm{GL}_2(\mathcal O_L))=1$, and write

$$
T_L=\mathbf1_{\mathcal K_L
\operatorname{diag}(\varpi_L,1)\mathcal K_L},
\qquad
S_L=\mathbf1_{\mathcal K_L(\varpi_LI_2)\mathcal K_L}.
$$

On the spherical line of the lift,

$$
T_L\longmapsto q_L^{1/2}(\alpha^n+\beta^n),
\qquad
S_L\longmapsto(\alpha\beta)^n.
$$

For the normalized operator $\mathsf T_L=q_L^{-1/2}T_L$, the eigenvalue is simply
$\alpha^n+\beta^n$. The lifted Hecke polynomial is

$$
P_{\operatorname{BC}\pi,L}(X)
=(1-\alpha^nX)(1-\beta^nX).
$$

The factor $q_L^{1/2}=q_K^{n/2}$ belongs to the raw double-coset operator, not to the
Satake parameters.

**Derivation.** Over $K$, the normalized Satake transform sends the standard double
coset to the symmetric function $X_1+X_2$, while the central scalar coset maps to
$X_1X_2$. Restriction replaces the geometric-Frobenius conjugacy class
$\operatorname{diag}(\alpha,\beta)$ by its $n$th power. Evaluation of the same two
symmetric functions over $L$ gives $\alpha^n+\beta^n$ and $(\alpha\beta)^n$.
Undoing normalized Satake multiplies the first by $q_L^{1/2}$. Thus the formula uses
both a parameter-side power map and a group-side change of residue cardinality.

As a sanity check, take the trivial representation. Its Satake pair is
$\{q_K^{1/2},q_K^{-1/2}\}$. After degree-$n$ unramified base change this becomes
$\{q_L^{1/2},q_L^{-1/2}\}$, the pair for the trivial representation over $L$. The raw
$T_L$ eigenvalue is $q_L+1$, exactly the number of right cosets in the standard
double coset.

### 6.3 A recursive Hecke formula

Often one knows only

$$
A=\alpha+\beta,\qquad B=\alpha\beta.
$$

Define $P_0=2$, $P_1=A$, and

$$
P_m=AP_{m-1}-BP_{m-2}\qquad(m\ge2).
$$

Then $P_m=\alpha^m+\beta^m$. Thus normalized Hecke eigenvalues under unramified
degree-$n$ base change can be calculated without choosing an ordering or adjoining
the individual roots:

$$
\mathsf T_L\longmapsto P_n(A,B),
\qquad S_L\longmapsto B^n.
$$

For example,

$$
P_2=A^2-2B,\qquad P_3=A^3-3AB.
$$

This recursion is the local algebra behind the familiar polynomial transformation at
unramified places.

### 6.4 What unramified base change does not preserve

Sphericality is preserved for spherical inputs, and conductor is unchanged for every
parameter under an unramified extension. Irreducibility need not be preserved.
Suppose $\eta$ is a nontrivial unramified character of $K^\times$ whose restriction to
$W_L$ is trivial; equivalently $\eta$ is a character of
$K^\times/N_{L/K}L^\times$. The irreducible principal series with ratio
$\nu_K\eta$ is away from the reducibility boundary over $K$, but its restricted ratio
is $\nu_L$. Its base change is therefore a determinant character, not an irreducible
principal series.

Likewise, a ramified irreducible Weil representation can become reducible even though
an unramified extension leaves inertia unchanged. A depth-zero dihedral parameter
induced from the unramified quadratic extension is the basic example: base change to
that quadratic field exposes its two ramified character lines. The lift is principal
series but not spherical. Thus an unramified extension preserves the inertia action and
the conductor, not irreducibility. “Unramified extension” describes the fields, not
the representation.

## 7. Principal, character, and special representations

### 7.1 Restriction of a split parameter

Put $\chi_{i,L}=\chi_i\circ N_{L/K}$. If
$\pi=I_K(\chi_1,\chi_2)$ is irreducible, restriction gives

$$
(\chi_1\oplus\chi_2)|_{W_L}
=\chi_{1,L}\oplus\chi_{2,L}.
$$

When
$\chi_{1,L}\chi_{2,L}^{-1}\ne\nu_L^{\pm1}$, translation through the dictionary yields

$$
\boxed{\ \operatorname{BC}_{L/K}I_K(\chi_1,\chi_2)
\cong I_L(\chi_{1,L},\chi_{2,L}).\ }
$$

The formula allows $\chi_{1,L}=\chi_{2,L}$; the resulting principal series is still
irreducible. Thus coalescing two characters is not itself a reducibility phenomenon.

For determinant characters one obtains directly

$$
\boxed{\ \operatorname{BC}_{L/K}(\mu\circ\det)
=(\mu\circ N_{L/K})\circ\det.\ }
$$

Indeed the two boundary characters and their half-powers restrict in the required
way because $\nu_K|_{W_L}=\nu_L$.

### 7.2 The reducibility boundary after base change

The subtle case occurs when the original principal series is irreducible but

$$
\chi_{1,L}\chi_{2,L}^{-1}=\nu_L^{\pm1}.
$$

Write, after ordering,

$$
\chi_{1,L}=\mu_L\nu_L^{-1/2},
\qquad
\chi_{2,L}=\mu_L\nu_L^{1/2}.
$$

The restricted parameter has $N=0$. Therefore

$$
\boxed{\ \operatorname{BC}_{L/K}(\pi)=\mu_L\circ\det,\ }
$$

not the reducible induced representation and not its Steinberg constituent. This
collapse can occur only because the quotient

$$
(\chi_1\chi_2^{-1})\nu_K^{\mp1}
$$

is a nontrivial character killed by restriction, hence a character of
$K^\times/N_{L/K}L^\times$.

This gives an exact representation-theoretic description of “reducible behavior.” A
split parameter stays split, but the irreducible representation assigned to it may
cross the normalized-induction boundary.

### 7.3 Steinberg twists and preserved monodromy

Let $\pi=\operatorname{St}_K\otimes\mu$. Restriction gives

$$
\operatorname{Sp}_2(\mu)|_{W_L}
=\operatorname{Sp}_2(\mu\circ N_{L/K}),
$$

because the norm character and both half-powers restrict while $N$ remains nonzero.
Hence

$$
\boxed{\ \operatorname{BC}_{L/K}
(\operatorname{St}_K\otimes\mu)
=\operatorname{St}_L\otimes(\mu\circ N_{L/K}).\ }
$$

No extension of fields can make a nonzero linear map zero. Special representations
therefore never become principal series under base change. This sharp contrast with
supercuspidals is one of the most useful type tests in the theory.

The formula also proves compatibility with arbitrary twists, including ramified ones.
Its conductor is $1$ if $\mu\circ N_{L/K}$ is unramified and otherwise
$2a_L(\mu\circ N_{L/K})$. It need not be a simple multiple of the original
conductor.

### 7.4 Three counterexamples to naive rules

First, base change is not obtained by restricting functions on groups. There is no
canonical way to turn a function in a model of $I_K(\chi_1,\chi_2)$ into a function
on $\mathrm{GL}_2(L)$; the norm acts on inducing characters, not on matrix entries.

Second, a split parameter does not always translate to an irreducible principal
series. Section 7.2 gives a genuine irreducible principal series over $K$ whose lift is
one dimensional.

Third, the semisimplified Weil representation does not determine the lift. The
parameters of $\mu\circ\det$ and $\operatorname{St}\otimes\mu$ have the same two
semisimple characters, but one has $N=0$ and the other $N\ne0$. Base change preserves
that distinction at every stage.

## 8. Dihedral supercuspidals and Mackey restriction

### 8.1 Admissible quadratic pairs

The most calculable supercuspidals arise from a quadratic extension $E/K$. Let
$\tau$ be its nontrivial automorphism and let $(E/K,\theta)$ be a tame admissible
pair in the sense of Book 81.
Via geometric reciprocity, form

$$
r(E,\theta)=\operatorname{Ind}_{W_E}^{W_K}\theta.
$$

It is irreducible because $\theta\ne\theta^\tau$, and the associated selected smooth
representation $\pi_K(E,\theta)$ is supercuspidal. In tame constructions the
compact inducing datum may use a rectified character; throughout this chapter
$\theta$ means the canonical Weil-side character, so the formulas contain no hidden
rectifier.

Let $M=EL$ inside $\overline K$. Because $L/K$ is Galois, either $E\subset L$ or
$E\cap L=K$. Mackey theory computes the restriction of $r(E,\theta)$ in both cases.
This is not merely a convenient example: it identifies exactly when a dihedral
supercuspidal loses cuspidality.

The underlying calculation starts from

$$
\operatorname{Res}_{W_L}^{W_K}\operatorname{Ind}_{W_E}^{W_K}\theta
\cong
\bigoplus_{g\in W_L\backslash W_K/W_E}
\operatorname{Ind}_{W_L\cap gW_Eg^{-1}}^{W_L}\theta^g.
$$

Because $W_E$ has index two, the double-coset set and the intersection subgroup are
controlled entirely by whether $E$ lies in $L$. This formula is the proof engine for
the next two sections; the field diagrams merely make its subgroups readable.

### 8.2 The disjoint case

Assume $E\cap L=K$. Then $M/L$ is quadratic and $M/E$ is cyclic of degree $n$.
There is one relevant double coset, and Mackey restriction gives

$$
\operatorname{Res}_{W_L}^{W_K}
\operatorname{Ind}_{W_E}^{W_K}\theta
\cong
\operatorname{Ind}_{W_M}^{W_L}(\theta|_{W_M}).
$$

Under local reciprocity,

$$
\theta|_{W_M}
\longleftrightarrow
\theta_M=\theta\circ N_{M/E}:M^\times\to C^\times.
$$

Let $\tau_M$ denote the nontrivial automorphism of $M/L$. If
$\theta_M\ne\theta_M^{\tau_M}$, the induced parameter remains irreducible. If in
addition $(M/L,\theta_M)$ is a selected admissible pair, then in particular the
restricted parameter is selected and

$$
\boxed{\ \operatorname{BC}_{L/K}\pi_K(E,\theta)
=\pi_L(M,\theta_M).\ }
$$

Thus the quadratic torus itself base-changes from $E/K$ to $M/L$, and its character
pulls back through the norm in the opposite leg of the square.

Regularity and selected admissibility are different tests. If after base change
$\theta_M/\theta_M^{\tau_M}$ is nontrivial but is trivial on principal units while
$M/L$ is ramified, the induced Weil representation is irreducible, but the pair is
not itself one of the admissible tame labels constructed in Book 81. Section 8.4
shows that the parameter then has a second presentation using the unramified
quadratic extension of $L$. Thus the displayed parameter computation remains valid,
but the smooth supercuspidal must be named using that alternative admissible pair
rather than the raw pair $(M/L,\theta_M)$.

It can happen that $\theta\ne\theta^\tau$ but
$\theta_M=\theta_M^{\tau_M}$. The difference character

$$
\delta=\theta/\theta^\tau
$$

is then nontrivial on $W_E$ but trivial on $W_M$. Equivalently, $\delta$ factors
through $\operatorname{Gal}(M/E)$. In this exceptional case the restricted induction
is reducible. This possibility is sometimes missed when “linearly disjoint” is
mistaken for “automatically regular after pullback.”

If regularity fails, the invariant character $\theta_M$ extends in two ways from
$W_M$ to $W_L$, differing by the quadratic character of $M/L$. Call these extensions
$\xi$ and $\xi\eta_{M/L}$. Then

$$
\operatorname{Ind}_{W_M}^{W_L}\theta_M
=\xi\oplus\xi\eta_{M/L}.
$$

In this reducible case the lifted smooth representation is consequently
$I_L(\xi,\xi\eta_{M/L})$. The ratio has finite order and cannot be
$\nu_L^{\pm1}$, so this principal series is irreducible.

### 8.3 The contained quadratic field

Assume $E\subset L$. Then $W_L\subset W_E$, and the two Mackey summands are already
characters:

$$
\operatorname{Res}_{W_L}^{W_K}
\operatorname{Ind}_{W_E}^{W_K}\theta
\cong
\theta|_{W_L}\oplus\theta^\tau|_{W_L}.
$$

On multiplicative groups these are

$$
\theta_L=\theta\circ N_{L/E},
\qquad
\theta_L^\tau=\theta^\tau\circ N_{L/E}.
$$

They are distinct. Indeed equality would make the restriction to $W_L$ a repeated
character. Since $W_L$ is normal and $W_K/W_L$ is cyclic, that character extends
after removing a scalar cyclic obstruction, and the remaining two-dimensional action
of the cyclic quotient diagonalizes. The original $W_K$-representation would then be
reducible, a contradiction. More concretely, in the quadratic base change $L=E$,
regularity already says the two characters differ.

An element of $\Gamma$ exchanges the two characters and sends their ratio to its
inverse. Since $\nu_L^{\pm1}$ is $\Gamma$-fixed and is not quadratic, the ratio cannot
equal $\nu_L^{\pm1}$. Hence the lifted representation is an irreducible principal series:

$$
\boxed{\ \operatorname{BC}_{L/K}\pi_K(E,\theta)
=I_L(\theta_L,\theta_L^\tau).\ }
$$

This is the basic discrete-to-principal transition. The original representation is
supercuspidal because the two lines are exchanged by $W_K$; after passing to $W_L$ the
group no longer exchanges them.

For $L=E$ this is especially transparent. In a basis indexed by the two cosets of
$W_E$ in $W_K$, restriction simply removes the matrix that exchanges the basis
vectors. What was an irreducible two-dimensional action becomes diagonal. Nothing
singular has happened to either character; the ambient group has lost the element that
tied them together.

### 8.4 The exact cuspidality criterion

The two field configurations can be summarized without imposing an extra ramification
hypothesis on $L/K$.

**Theorem 8.1 (dihedral restriction criterion).** Let
$\pi=\pi_K(E,\theta)$ come from a selected tame admissible pair, and put $M=EL$.
The restricted parameter is irreducible if and only if

$$
E\not\subset L
\quad\text{and}\quad
(\theta/\theta^\tau)|_{W_M}\ne1.
$$

When the condition holds, the smooth base change is supercuspidal. It is
$\pi_L(M,\theta_M)$ if this evident pair is admissible; otherwise the same parameter
has the admissible unramified presentation constructed in the proof below. When the
condition fails, the restricted parameter is a sum of two characters and the smooth
lift is an irreducible principal series. The two characters are distinct, and an
element of the cyclic quotient exchanges them. Their ratio goes to its inverse, so it
cannot be the $\Gamma$-fixed nonquadratic character $\nu_L^{\pm1}$; the
determinant-character boundary cannot occur here. In particular, every restriction
of a selected tame-dihedral parameter is again selected.

**Proof strategy.** Mackey restriction supplies the formulas in Sections 8.2 and 8.3.
An induction from an index-two subgroup is irreducible exactly when its inducing
character is not fixed by the nontrivial coset. The only extra point is to prove that
failure of admissibility for the evident regular ramified pair changes the label, not
the selected status of the parameter.

**Proof.** In the disjoint case, Mackey gives
$\operatorname{Ind}_{W_M}^{W_L}\theta_M$. Its two restricted characters on $W_M$
are $\theta_M$ and $\theta_M^{\tau_M}$, so the index-two irreducibility criterion is
exactly the displayed nontriviality of $\theta/\theta^\tau$ on $W_M$. In the contained
case Mackey gives two characters directly.

It remains to justify selectedness in the regular disjoint case. The ramification
index of $M/L$ divides that of $E/K$, so $M/L$ is unramified or tame; in residue
characteristic two it is necessarily unramified. An unramified regular quadratic pair
is admissible. Suppose therefore that $M/L$ is ramified tame and that the regular
pair $(M/L,\theta_M)$ is not admissible. Put

$$
\delta_M=\theta_M/\theta_M^{\tau_M}.
$$

Then $\delta_M$ is nontrivial but trivial on $U_M^1$. The ramified quadratic
automorphism acts trivially on the residue field and sends a uniformizer to its
negative modulo $U_M^1$; since $-1$ is fixed, $\delta_M(-1)=1$. Hence it acts
trivially on every value seen by $\delta_M$. On the other hand
$\delta_M^{\tau_M}=\delta_M^{-1}$, so $\delta_M^2=1$. The projective image of
$\operatorname{Ind}_{W_M}^{W_L}\theta_M$ is consequently the Klein four group: one
involution is represented by the two diagonal character lines and another exchanges
them.

The three index-two subgroups of that projective image give three quadratic
presentations of the same irreducible Weil representation. Besides the ramified field
$M$, one of the corresponding quadratic extensions $M'/L$ is unramified. Restriction
to $W_{M'}$ gives two distinct characters, say $\xi$ and $\xi^{\tau'}$, and therefore

$$
\operatorname{Ind}_{W_M}^{W_L}\theta_M
\cong\operatorname{Ind}_{W_{M'}}^{W_L}\xi.
$$

The pair $(M'/L,\xi)$ is regular and unramified, hence selected admissible. This is
exactly the exceptional multiple-presentation analysis in the injectivity proof of
the selected correspondence. Thus every irreducible restriction has a selected
label, while every reducible restriction is already a selected split parameter.
Chapter 4 now gives all the asserted smooth translations. $\square$

The criterion involves the character, not just the fields. Two supercuspidals built
from the same quadratic $E/K$ can behave differently after the same disjoint cyclic
base change.

The conductor of the restricted parameter supplies a useful check but not the criterion. In the
regular disjoint case it is computed from the quadratic induction formula over $L$:

$$
a_L(\operatorname{BC}\pi)
=\Delta_{M/L}+f(M/L)a_M(\theta\circ N_{M/E}).
$$

In the split case it is the sum of the two character conductors. Equality of these
numbers across a degeneration does not force cuspidality; the presence or absence of
an invariant line does.

## 9. Discrete parameters and cyclic parity

### 9.1 Clifford theory under a cyclic subgroup

The Mackey calculation settles selected dihedral parameters directly. A short
Clifford-theoretic argument explains why odd cyclic degree forces the regular outcome
without inspecting the inducing character. Let $r$ be an irreducible
two-dimensional representation of $W_K$ and restrict it to the normal finite-index
subgroup $W_L$. Frobenius semisimplification makes the restriction semisimple.
Clifford theory says that its irreducible constituents form a single $\Gamma$-orbit,
each with the same multiplicity.

Dimension two leaves only two possibilities:

$$
r|_{W_L}\text{ is irreducible},
$$

or

$$
r|_{W_L}=\xi\oplus\xi^\sigma
$$

for two distinct characters and some $\sigma\in\Gamma$. A repeated character would
make the quotient act projectively on a two-dimensional multiplicity space. Since the
quotient is cyclic and coefficients are algebraically closed of characteristic zero,
that projective action diagonalizes after rescaling, contradicting irreducibility of
$r$.

The second possibility can occur only when $\Gamma$ has an orbit of size two, hence
only when $n$ is even. In particular, restriction of an irreducible two-dimensional
parameter through an odd-degree cyclic extension remains irreducible.

This parity statement uses cyclicity in an essential way. For a noncyclic quotient of
odd order the same orbit-size argument still rules out an orbit of size two, but
projective multiplicity phenomena in higher rank require more care. Here the quotient
is cyclic and the representation has dimension two, so no additional case survives.

### 9.2 The selected cuspidality criterion

**Theorem 9.1 (selected cuspidality criterion).** If $\pi$ is a selected tame
dihedral supercuspidal representation of $\mathrm{GL}_2(K)$, then

$$
\operatorname{BC}_{L/K}\pi\text{ is supercuspidal}
\quad\Longleftrightarrow\quad
\operatorname{rec}_K(\pi)|_{W_L}\text{ is irreducible}.
$$

If the restriction is reducible, it is a sum of two distinct characters and the lift
is an irreducible principal series.

**Proof.** The selected supercuspidal has the irreducible Weil representation attached
to its tame admissible pair and has zero monodromy. Restriction cannot create
monodromy. Clifford theory gives the two alternatives of Section 9.1, and the selected
parameter dictionary translates them respectively into a selected supercuspidal or a
split-parameter representation. An element of $\Gamma$ exchanges the two
constituents, so it carries their ratio to its inverse. The characters
$\nu_L^{\pm1}$ are $\Gamma$-fixed and are not quadratic; hence the split case is an
irreducible principal series rather than a boundary character. $\square$

For a dihedral label, Theorem 8.1 is the sharper form because it tests irreducibility
by the explicit character $\theta/\theta^\tau$. The present theorem supplies the
structural explanation and the parity consequence. It makes no assertion about a
primitive wild smooth representation, since no full wild parameter correspondence is
among the established prerequisites.

### 9.3 The discrete-to-principal boundary

The selected essentially square-integrable representations of $\mathrm{GL}_2(K)$ are
the Steinberg twists and selected tame dihedral supercuspidals. Their behavior now has
a complete description:

- a Steinberg twist remains Steinberg because $N$ remains nonzero;
- a selected supercuspidal remains supercuspidal exactly when its Weil representation
  stays irreducible;
- a selected supercuspidal that loses irreducibility becomes an irreducible principal
  series.

Thus base change need not preserve discrete series. What it preserves is the restricted
parameter. The loss of discreteness is not caused by a conductor accident; it is caused
by the appearance of invariant lines after passage to a subgroup.

For odd $[L:K]$, Clifford theory rules out that appearance, so every selected
supercuspidal parameter remains irreducible and its smooth lift remains selected
supercuspidal. For even degree, the
quadratic subextension of $L/K$ is the only possible field across which the two
constituents can be exchanged. This observation will align perfectly with splitting
of a quaternion algebra in Chapter 13.

## 10. Ramification and conductor change

### 10.1 Inertia restriction and upper numbering

Unramified base change leaves inertia unchanged. Ramified base change replaces
$I_K$ by the smaller subgroup $I_L=I_K\cap W_L$, so fixed spaces may grow. It also
changes the numerical label placed on the same deep ramification subgroup. Any exact
conductor discussion must keep these two effects separate.

For $u\ge0$, let $W_K^u$ and $W_L^v$ denote the upper-numbered ramification groups.
Define the increasing reindexing function $\Phi_{L/K}$ by the subgroup identity

$$
W_L^v=W_L\cap W_K^{\Phi_{L/K}(v)}.
$$

Its inverse is denoted $\Psi_{L/K}$. This definition fixes the direction regardless of
competing notational conventions for Herbrand functions. If $L/K$ is unramified,
$\Phi(v)=v$. If it is tamely totally ramified of degree $e$, then
$\Phi(v)=v/e$ for $v>0$, so positive upper breaks are multiplied by $e$ on restriction.

For a finite-inertia Weil representation $V$,

$$
a_K(V)=\operatorname{codim}V^{I_K}
+\operatorname{Sw}_K(V),
$$

where the Swan term is the upper-numbering integral of
$\operatorname{codim}V^{W_K^u}$ over $u>0$. Restriction changes both the codimension
at $u=0$ and the integrand through the displayed subgroup identity.

Suppose $V$ has an upper-break decomposition

$$
V=V(-1)\oplus\bigoplus_{b\ge0}V(b),
$$

where $V(-1)=V^{I_K}$ and $V(b)$ is pure of break $b$. Then

$$
a_K(V)=\sum_{b\ge0}(b+1)\dim V(b).
$$

Restriction can do two things to a summand $V(b)$: some vectors may become invariant,
and each surviving positive break is carried through $\Psi_{L/K}$. Thus knowledge of
the total sum $a_K(V)$ alone discards exactly the information required upstairs. The
break decomposition, not merely its weighted dimension, is the natural input.

### 10.2 Exact break formulas and inequalities

Let a one-dimensional character $\chi$ of $W_K$ have positive upper break $b$; its
conductor is $a_K(\chi)=b+1$ when Hasse--Arf applies, as it does for characters. The
restricted character may become trivial, or its highest ramification layer may vanish
on $W_L$. In all cases its largest surviving break $b_L$ satisfies

$$
b_L\le\Psi_{L/K}(b).
$$

Equality holds if $\chi$ remains nontrivial on
$W_L\cap W_K^b$. Under that survival hypothesis,

$$
\boxed{\ a_L(\chi\circ N_{L/K})
=\Psi_{L/K}(a_K(\chi)-1)+1.\ }
$$

If the restricted character is trivial, its conductor is $0$, not the right side of
this formula. This is the essential hypothesis that a bare “Herbrand formula” often
suppresses.

For a tame totally ramified extension and a character of conductor $m>0$ whose top
break survives,

$$
a_L(\chi\circ N_{L/K})=e(m-1)+1.
$$

A tame character has $m=1$ and stays of conductor $1$ when nontrivial; a positive-depth
character has its depth stretched by $e$. For a general finite-dimensional $V$, the
same break-by-break rule gives an exact conductor after one records which fixed spaces
grow. There is no formula depending only on $a_K(V)$, $e$, and $f$: two representations
with the same original conductor may lose different top constituents on $W_L$.

Here is a simple counterexample at break zero. Let $L/K$ be tamely totally ramified
cyclic and let $\eta$ be a nontrivial character of
$K^\times/N_{L/K}L^\times$. It has conductor one, but
$\eta\circ N_{L/K}=1$ has conductor zero. Another tame character $\chi$ with the
same conductor exponent need not vanish on the smaller inertia group, and then
$\chi\circ N_{L/K}$ still has conductor one.
Equal downstairs conductors have produced different upstairs conductors because one
top character was killed and the other survived.

### 10.3 The different and the induction formula

The different packages all ramification layers of the field extension itself. To keep
the ideal upstairs separate from its norm downstairs, put

$$
\Delta_{L/K}=v_K(\mathfrak d_{L/K})
=f\,v_L(\mathfrak D_{L/K}),
$$

the exponent of the discriminant ideal in $K$; the same notation will be used for
other finite extensions. For an $m$-dimensional Weil--Deligne
representation $U$ of $W_L$, the conductor induction formula is

$$
\boxed{\ a_K(\operatorname{Ind}_{W_L}^{W_K}U)
=f\,a_L(U)+m\,\Delta_{L/K}.\ }
$$

The case $U=1$ says that the permutation representation on the embeddings of $L$ has
conductor $\Delta_{L/K}$. The general formula separates this field-theoretic cost, repeated
$m$ times, from the intrinsic conductor over $L$, weighted by residue degree.

**Proof strategy.** Realize all inertia actions through a common finite Galois
extension. On each lower ramification group, the codimension of invariants in an
induced representation is computed by the orbit decomposition of cosets. Summing with
the Artin weights separates the ramification of the coset permutation action from the
ramification internal to $U$. The former is the different exponent; changing normalized
valuations from $L$ to $K$ supplies the factor $f$ in the latter.

**Justification.** The Artin-conductor induction theorem and the
conductor--discriminant identity were established in Book 3 for finite inertial image;
an arbitrary semisimple Frobenius operator does not change the ramification
codimensions, so the same proof applies to the underlying Weil representation. They
give the displayed formula, including the residue-degree factor and exactly one
discriminant contribution per dimension. The monodromy
correction is compatible with induction because
$\ker(\operatorname{Ind}N)=\operatorname{Ind}(\ker N)$,
and the $I_K$-invariants of an induced space consist of $f$ copies of the corresponding
$I_L$-invariants. Thus the correction itself is multiplied by $f$, and the same
identity holds for Weil--Deligne representations. This reduces the claim to the
established conductor theorem rather than treating a break-counting sketch as a new
proof.

Apply the projection formula

$$
\operatorname{Ind}_{W_L}^{W_K}(\operatorname{Res}_{W_L}V)
\cong V\otimes\operatorname{Ind}_{W_L}^{W_K}1.
$$

For a two-dimensional parameter $\Phi$ this gives the exact restriction identity

$$
\boxed{
f\,a_L(\Phi|_{W_L})
=a_K\!\left(\Phi\otimes
\operatorname{Ind}_{W_L}^{W_K}1\right)-2\Delta_{L/K}.
}
$$

This formula remains valid with monodromy. It is often more useful than a rough
inequality because the permutation representation decomposes explicitly when $L/K$
is cyclic.

Let

$$
X_{L/K}=\{\eta:K^\times/N_{L/K}L^\times\to C^\times\}.
$$

Local class field theory gives

$$
\operatorname{Ind}_{W_L}^{W_K}1
=\bigoplus_{\eta\in X_{L/K}}\eta.
$$

Hence

$$
\boxed{
f\,a_L(\operatorname{BC}_{L/K}\pi)
=\sum_{\eta\in X_{L/K}}a_K(\pi\otimes\eta)-2\Delta_{L/K}.
}
$$

This is an exact conductor formula for every selected irreducible $\pi$.
Cancellation inside individual twists is not ignored; it is included in the terms on
the right. The displayed identity itself is also a valid parameter identity beyond the
selected range, but no smooth wild correspondence is inferred from it here.

The formula is also an integrality check. Its right side must be divisible by $f$ after
subtracting $2\Delta_{L/K}$. A proposed table of twist conductors that violates this
divisibility cannot be the conductor table of a restricted two-dimensional parameter.

### 10.4 Unramified, tame, and monodromic cases

If $L/K$ is unramified, $\Delta_{L/K}=0$, every $\eta\in X_{L/K}$ is unramified, and
unramified twisting preserves conductor. Since $f=n$,

$$
\boxed{\ a_L(\operatorname{BC}_{L/K}\pi)=a_K(\pi).\ }
$$

If $L/K$ is tamely totally ramified, positive Swan breaks are multiplied by $e$.
More precisely, for a Weil representation $V$,

$$
a_L(V|_{W_L})
=\operatorname{codim}V^{I_L}+e\operatorname{Sw}_K(V).
$$

If no new inertial invariants appear, this is

$$
a_L(V|_{W_L})
=\operatorname{codim}V^{I_K}+e\operatorname{Sw}_K(V).
$$

The hypothesis cannot be discarded: tame inertia characters can become trivial on
$I_L$.

For a two-dimensional representation with no new inertia invariants and Swan conductor
$s$, the last display reads $a_L=2+es$. If one inertia line becomes fixed after
restriction, the tame term drops from $2$ to $1$; if both become fixed, it drops to
$0$. Under a tame extension the wild inertia subgroup is unchanged, so a
positive-break constituent cannot die and the Swan term really is $es$. Under a wild
extension, by contrast, positive-break constituents can disappear and the full
Herbrand calculation must be repeated. This makes precise the two independent
phenomena announced at the beginning of the chapter.

For $\operatorname{St}\otimes\mu$, monodromy contributes after restriction exactly as
before. If $\mu_L=\mu\circ N_{L/K}$ is unramified, the lifted conductor is $1$. If it
is ramified,

$$
a_L(\operatorname{BC}(\operatorname{St}\otimes\mu))=2a_L(\mu_L).
$$

In particular an unramified Steinberg twist does not acquire conductor $e$ under a
totally ramified extension: its conductor comes from the one-dimensional monodromy
correction, not from a positive ramification break.

For wild extensions the graph of $\Psi_{L/K}$ has several slopes. A parameter with
breaks $b_i$ must be treated break by break, testing survival on each intersection
$W_L\cap W_K^{b_i}$. The different identity above provides a reliable global check on
the result.

## 11. Local factors under cyclic base change

### 11.1 Factors of a restricted parameter

The factors of the lift are those of the restricted parameter:

$$
L_L(s,\operatorname{BC}_{L/K}\pi)
=L_L(s,\operatorname{rec}_K(\pi)|_{W_L}),
$$

$$
\epsilon_L(s,\operatorname{BC}_{L/K}\pi,\psi_L)
=\epsilon_L(s,\operatorname{rec}_K(\pi)|_{W_L},\psi_L).
$$

These equalities are substantive because factors on the smooth side are defined by
local zeta integrals and functional equations, while those on the parameter side are
defined by inertia, Frobenius, and finite Gauss sums. The rank-two dictionary proves
their equality before base change; restriction then gives the displayed compatibility.

There is generally no equality
$L_L(s,\operatorname{BC}\pi)=L_K(s,\pi)$. In the spherical unramified case the left
factor contains $\alpha^n$ and $\beta^n$, not $\alpha$ and $\beta$. The correct
comparison is a product over twists.

The family-by-family formulas are worth making explicit. For a principal series away
from the boundary,

$$
L_L(s,\operatorname{BC}I_K(\chi_1,\chi_2))
=L_L(s,\chi_1\circ N_{L/K})L_L(s,\chi_2\circ N_{L/K}).
$$

The same product remains valid at the determinant-character boundary because the
parameter still has $N=0$. For a special representation,

$$
L_L(s,\operatorname{BC}(\operatorname{St}_K\otimes\mu))
=L_L(s+1/2,\mu\circ N_{L/K}).
$$

A supercuspidal factor downstairs is $1$, but the lifted factor need not remain $1$.
If restriction exposes unramified character lines, the resulting principal series has
nontrivial Euler factors. Thus even the statement “supercuspidal factors are one” does
not permit the factor of base change to be guessed without restricting the parameter.

### 11.2 Induction, restriction, and the product formula

For any Weil--Deligne representation $U$ of $W_L$, induction preserves the standard
factor:

$$
L_K(s,\operatorname{Ind}_{W_L}^{W_K}U)=L_L(s,U).
$$

Apply this to $U=\operatorname{Res}_{W_L}\Phi$ and use the projection formula and the
character decomposition of the cyclic permutation representation. One obtains

$$
\boxed{
L_L(s,\operatorname{BC}_{L/K}\pi)
=\prod_{\eta\in X_{L/K}}L_K(s,\pi\otimes\eta).
}
$$

**Proof strategy.** The induction identity can be checked directly on inertia
invariants. Choose coset representatives for $W_K/W_L$; Frobenius permutes the induced
blocks, and the determinant of its cyclic block matrix is the determinant over $L$
with the variable $q_L^{-s}=q_K^{-fs}$. Then distribute tensor product over the
character decomposition of the regular representation of $\Gamma$.

This proof explains why the residue-degree power appears correctly. It also works for
monodromy because the induced nilpotent operator acts blockwise and its kernel induces
from $\ker N$.

For a quadratic extension, $X_{L/K}=\{1,\eta\}$ and the identity reads

$$
L_L(s,\operatorname{BC}\pi)
=L_K(s,\pi)L_K(s,\pi\otimes\eta).
$$

If $\pi$ is spherical and $L/K$ is unramified quadratic, the two factors on the right
have parameters $\{\alpha,\beta\}$ and $\{-\alpha,-\beta\}$. Their product is

$$
\frac1{(1-\alpha^2q_K^{-2s})(1-\beta^2q_K^{-2s})},
$$

which is the factor over $L$ because $q_L^{-s}=q_K^{-2s}$. This direct calculation
checks both the twist product and the Frobenius-square rule.

### 11.3 Epsilon factors and additive characters

Fix a nontrivial additive character $\psi_K$ and put

$$
\psi_L=\psi_K\circ\operatorname{Tr}_{L/K}.
$$

Write $n_K(\psi_K)$ for the integer such that $\psi_K$ is trivial on
$\mathfrak p_K^{-n_K(\psi_K)}$ but not on
$\mathfrak p_K^{-n_K(\psi_K)-1}$. Thus conductor zero means triviality on
$\mathcal O_K$ and nontriviality on $\mathfrak p_K^{-1}$. If
$d(L/K)=v_L(\mathfrak D_{L/K})$, trace duality gives

$$
\boxed{\ n_L(\psi_K\circ\operatorname{Tr}_{L/K})
=e(L/K)n_K(\psi_K)+d(L/K).\ }
$$

Indeed, the largest fractional $\mathcal O_L$-ideal on which the trace character is
trivial is

$$
\mathfrak p_K^{-n_K(\psi_K)}\mathfrak D_{L/K}^{-1}
=\mathfrak p_L^{-en_K(\psi_K)-d(L/K)}.
$$

This is the exact different shift that will reappear in the conductor identity.

Use the standard self-dual Haar measure for each displayed additive character. With
this convention the induction formula below contains all measure and different
normalizations in one constant.

Define the induction constant

$$
\lambda(L/K,\psi_K)
=\frac{\epsilon_K(s,\operatorname{Ind}_{W_L}^{W_K}1,\psi_K)}
{\epsilon_L(s,1,\psi_L)}.
$$

With the standard normalization this ratio is independent of $s$; the conductor and
different contributions make the two monomial exponents cancel in the displayed
quotient.
The induction formula is

$$
\epsilon_K(s,\operatorname{Ind}U,\psi_K)
=\lambda(L/K,\psi_K)^{\dim U}
\epsilon_L(s,U,\psi_L).
$$

For the two-dimensional parameter of $\pi$, projection and cyclic character
decomposition give

$$
\boxed{
\epsilon_L(s,\operatorname{BC}_{L/K}\pi,\psi_K\circ\operatorname{Tr}_{L/K})
=\lambda(L/K,\psi_K)^{-2}
\prod_{\eta\in X_{L/K}}
\epsilon_K(s,\pi\otimes\eta,\psi_K).
}
$$

The exponent is $-2$: the induction formula first contributes $\lambda^2$ on the
left-hand induced parameter, and solving for the factor over $L$ inverts it.

The lambda factor cannot simply be discarded even when one cares only about root
numbers. It is the normalized Gauss sum of the permutation representation and measures
the Fourier-theoretic cost of changing fields. In a split étale algebra it is $1$; for
a ramified field extension it can be a nontrivial root of unity together with the
normalization forced by the different.

Every nontrivial additive character of $L$ is $\psi_{L,a}(x)=\psi_L(ax)$ for a unique
$a\in L^\times$. Scaling changes epsilon factors by

$$
\boxed{
\epsilon_L(s,\Pi,\psi_{L,a})
=\omega_\Pi(a)|a|_L^{2(s-1/2)}
\epsilon_L(s,\Pi,\psi_L).
}
$$

For the lift, $\omega_\Pi=\omega_\pi\circ N_{L/K}$. Thus using an additive character
of conductor zero over each field without checking whether it is trace-compatible can
insert both a central-character value and a power of $q_L$.

The scaling formula follows by replacing $x$ with $ax$ in the Fourier transform that
defines the functional equation. The determinant of the parameter supplies
$\omega_\Pi(a)$, while the change of self-dual measure and the degree-two norm power
supply $|a|_L^{2(s-1/2)}$. This proof also shows why the dimension is two in the
exponent and why contragredience does not introduce an unadvertised inverse.

### 11.4 Consequences for conductors and root numbers

When $\psi_K$ has conductor zero, $\psi_K\circ\operatorname{Tr}_{L/K}$ generally does
not: its conductor is shifted by the inverse different. The epsilon product formula is
therefore the primary statement; conductor exponents should be extracted only after
accounting for this shift. Doing so recovers exactly

$$
f\,a_L(\operatorname{BC}\pi)
=\sum_{\eta\in X_{L/K}}a_K(\pi\otimes\eta)-2\Delta_{L/K}.
$$

At $s=1/2$, absolute-value scaling disappears, but the determinant value
$\omega_\Pi(a)$ remains. Root numbers are consequently sensitive to the additive
character unless the central character makes that value trivial.

For a dihedral parameter the induction formula specializes to

$$
\epsilon_K(s,\pi_K(E,\theta),\psi_K)
=\lambda(E/K,\psi_K)
\epsilon_E(s,\theta,\psi_K\circ\operatorname{Tr}_{E/K}).
$$

Its conductor exponent is

$$
a_K(\pi_K(E,\theta))
=\Delta_{E/K}+f(E/K)a_E(\theta),
$$

provided $\theta$ is the canonical parameter character. For the smooth
representations treated here this includes unramified and tamely ramified quadratic
extensions. The parameter identity itself remains valid for a wild quadratic
extension, but the corresponding ramified dyadic smooth packet is outside the
selected correspondence.

## 12. Galois invariance, descent, fibers, and image

### 12.1 Why every lift is Galois invariant

The group $\Gamma$ acts on representations of $\mathrm{GL}_2(L)$ by transport of
structure. For $\sigma\in\Gamma$, define $\Pi^\sigma$ by

$$
\Pi^\sigma(g)=\Pi(\sigma^{-1}g),
$$

where $\sigma$ acts entrywise on matrices. On parameters, choose a lift
$\widetilde\sigma\in W_K$; conjugation sends

$$
(r_L,N)\quad\text{to}\quad
\left(w\mapsto r_L(\widetilde\sigma^{-1}w\widetilde\sigma),
\lVert\widetilde\sigma\rVert_K^{-1}N\right).
$$

**Proposition 12.1 (naturality in the selected range).** The selected parameter
correspondence carries $\Pi^\sigma$ to the displayed conjugate parameter.

**Proof.** For a principal series, transport of structure applies $\sigma$ to both
inducing characters, and naturality of local reciprocity gives the two conjugated
Weil characters. At the reducibility boundary the zero operator stays zero. For a
special representation, the same calculation transports the twisting character;
the nonzero monodromy operator is rescaled as displayed, and every nonzero rescaling
of the rank-one special operator is isomorphic to it. For a tame dihedral pair,
transport sends the quadratic field and its character to their $\sigma$-conjugates.
Induction of Weil representations and the admissible-pair construction are both
natural under this conjugation, and the equivalence relation on pairs removes the
choice of embedding. These are all selected rows. $\square$

The scale on $N$ is essential when $\sigma$ has a Frobenius component. It reflects the
change of tame logarithm involved in forming Weil--Deligne data. If $(r_L,N)$ is
restricted from $(r,N)$ over $K$, then $r(\widetilde\sigma)$ supplies an intertwiner,
because

$$
r(\widetilde\sigma)
(\lVert\widetilde\sigma\rVert_K^{-1}N)
r(\widetilde\sigma)^{-1}=N.
$$

Consequently

$$
\boxed{\ (\operatorname{BC}_{L/K}\pi)^\sigma
\cong\operatorname{BC}_{L/K}\pi\quad(\sigma\in\Gamma).\ }
$$

The isomorphism need not be canonically chosen. Multiplying an intertwiner by a scalar
changes the descent datum without changing the isomorphism class over $L$. That scalar
freedom is the source of twisting ambiguity.

The action just described is independent of the chosen lift. Replacing
$\widetilde\sigma$ by $u\widetilde\sigma$ with $u\in W_L$ changes the conjugated
parameter by the internal isomorphism $r_L(u)$. The corresponding scaling of $N$ is
absorbed by the covariance relation. Thus “$\Gamma$-invariant parameter” is an
intrinsic condition, even though its displayed intertwiner uses choices.

For $N=0$ the scaling is invisible. For a special parameter, all nonzero scalar
multiples of $N$ are isomorphic: in the standard basis, a diagonal change of basis
rescales the map $e_2\mapsto e_1$. This elementary fact is why every Steinberg twist is
indeed fixed by the field-automorphism action.

Galois invariance is therefore necessary for descent. It is stronger than invariance of
the central character and stronger than equality of unramified Hecke eigenvalues. The
entire smooth representation, equivalently the entire Weil--Deligne parameter, must be
invariant.

### 12.2 Extending an invariant parameter

Let $\Phi_L=(r_L,N)$ be a two-dimensional parameter of $W_L$. To descend it, one must
extend both $r_L$ and the covariance action on $N$ to $W_K$. Choose a generator
$\sigma$ of $\Gamma$ and a lift $s\in W_K$. Galois invariance gives an intertwiner
$A$ satisfying

$$
A r_L(w)A^{-1}=r_L(sws^{-1}),
\qquad
ANA^{-1}=\lVert s\rVert_K N.
$$

After iterating $n$ times, $A^n$ and $r_L(s^n)$ differ by an automorphism of
$\Phi_L$. An extension is exactly a choice of $A$ for which

$$
A^n=r_L(s^n),
$$

after the natural identification, modulo conjugation by
$\operatorname{Aut}_{W_L,N}(\Phi_L)$. Over the algebraically closed characteristic-zero
field $C$, the scalar obstruction for a cyclic group can be removed by taking an
$n$th root. Equivalently, the relevant cyclic projective obstruction vanishes because
every element of $C^\times$ has an $n$th root. Case-by-case on the three rank-two
shapes, the remaining automorphism group produces no further obstruction. Hence every
$\Gamma$-invariant admissible two-dimensional parameter extends.

The case analysis is short enough to record. If $r_L$ is irreducible, Schur's lemma
makes the discrepancy scalar, and an $n$th root removes it. If
$r_L=\xi_1\oplus\xi_2$ with distinct characters, invariance either fixes both lines or
permutes them; extend each character in the first case and use orbit induction in the
second. If the two characters coincide, the problem reduces to choosing a semisimple
cyclic operator on the two-dimensional multiplicity space. Finally, if $N\ne0$, its
kernel flag is invariant and the covariance relation forces the extension operator on
the quotient once it is chosen on the kernel. These are all the shapes of Proposition
3.1.

**Theorem 12.2 (selected local image criterion).** A selected irreducible smooth
representation $\Pi$ of $\mathrm{GL}_2(L)$ lies in the image of the selected map
$\operatorname{BC}_{L/K}$ if and only if its parameter has a selected extension to
$W_K$. Such an extension can exist only if

$$
\Pi^\sigma\cong\Pi\qquad\text{for every }\sigma\in\Gamma.
$$

This invariance is sufficient for extension as an admissible Weil--Deligne parameter.
The additional word “selected” excludes those invariant parameters whose extensions
exist only in an unconstructed wild row.

**Proof strategy.** Necessity was proved in Section 12.1. For the parameter statement,
choose a cyclic intertwiner, normalize its cyclic product, and extend to $W_K$. The
inverse selected dictionary gives a smooth descent exactly when one such extension is
selected.

**Proof.** Parameter compatibility with field automorphisms turns invariance of $\Pi$
into invariance of $\Phi_L$. The preceding cyclic extension argument produces an
admissible $\Phi_K$ with $\Phi_K|_{W_L}\cong\Phi_L$. If a selected extension exists,
let $\pi=\operatorname{rec}_K^{-1}(\Phi_K)$ for such a choice. By definition,
$\operatorname{BC}_{L/K}\pi\cong\Pi$. Conversely, the parameter of every selected
descent is itself a selected extension. $\square$

The qualification is real. If the residue characteristic is two and $L/K$ has a
ramified quadratic subextension, a split parameter over $L$ whose character lines are
exchanged by $\Gamma$ may extend only as induction from that wild quadratic field.
Galois invariance then proves parameter descent, but the selected correspondence does
not turn that extension into a smooth representation covered by this book.

The algebraic closedness of coefficients matters here. Over a smaller coefficient
field, the required root or an extension of a constituent may exist only after scalar
extension.

The theorem is a statement about isomorphism classes, not about a preferred descent
datum. To descend an actual vector space with action one must choose the intertwiners
and verify their cocycle relation. Different choices can lead to different
representations over $K$ even when they become isomorphic over $L$.

### 12.3 The twisting ambiguity and its limit

Every $\eta\in X_{L/K}$ is trivial on $W_L$. Hence

$$
\operatorname{BC}_{L/K}(\pi\otimes\eta)
\cong\operatorname{BC}_{L/K}(\pi).
$$

If the lifted parameter $\Phi_L$ has only scalar automorphisms—for example, if its Weil
representation is irreducible—then all extensions differ in exactly this way. The set
of descents is a torsor under

$$
X_{L/K}\simeq
\operatorname{Hom}(K^\times/N_{L/K}L^\times,C^\times).
$$

This is the clean descent ambiguity used most often.

To prove transitivity in the scalar-endomorphism case, let $A$ and $A'$ be the cyclic
operators defining two extensions. Their quotient commutes with $W_L$ and $N$, hence
is a scalar $c$. The cyclic relations imply $c^n=1$. Sending the chosen generator of
$W_K/W_L$ to $c$ defines a character $\eta$ of the quotient, and the second extension
is the first tensored with $\eta$. Freeness follows because a nontrivial quotient
character changes the extension operator. This proof identifies the ambiguity rather
than merely counting it.

It is false without a hypothesis on endomorphisms that every fiber is one twisting
orbit. Consider a quadratic extension and its quotient character $\eta$. The two
parameters

$$
1\oplus1,
\qquad
1\oplus\eta
$$

have isomorphic restrictions $1\oplus1$ to $W_L$, but no common twist turns one into
the other: a twist of the first has two equal characters. Reducible parameters have a
larger automorphism group, and distinct cyclic actions on their multiplicity spaces can
produce additional descent classes.

Thus the phrase “unique up to a character trivial on norms” is exact for scalar-
endomorphism parameters and can fail at reducible or scalar restrictions. The correct
general statement uses extension data.

### 12.4 The exact image and fiber criterion

For a parameter $\Phi_L$, let $\operatorname{Ext}^{\mathrm{sel}}_{K/L}(\Phi_L)$ be
the set of isomorphism classes of **selected** Weil--Deligne parameters $\Phi_K$
equipped only with an isomorphism
$\Phi_K|_{W_L}\cong\Phi_L$, with the chosen isomorphism then forgotten. The complete
fiber statement is

$$
\boxed{
\operatorname{BC}_{L/K}^{-1}(\Pi)
\longleftrightarrow
\operatorname{Ext}^{\mathrm{sel}}_{K/L}(\operatorname{rec}_L(\Pi)).
}
$$

The corresponding set of all admissible parameter extensions is empty exactly when
$\Pi$ is not $\Gamma$-invariant. Its selected subset can also be empty for the wild
boundary described after Theorem 12.2. When the selected subset is nonempty,
$X_{L/K}$ acts on it by twisting. If
$\operatorname{End}_{W_L,N}(\operatorname{rec}_L(\Pi))=C$, this action is simply
transitive. In general, choose $s$ and an intertwiner as in Section 12.2; the fiber is
the set of conjugacy classes of admissible solutions to the cyclic relation
$A^n=r_L(s^n)$ inside the relevant automorphism torsor. This is both an exact criterion
and a practical finite-dimensional calculation.

For split parameters the criterion can be made elementary. A multiset
$\{\xi_1,\xi_2\}$ of characters of $L^\times$ descends precisely when it is stable
under $\Gamma$; cyclicity and the divisibility of $C^\times$ remove the extension
obstruction. Either each
$\xi_i$ descends individually, producing pairs of character extensions, or the two
characters form one orbit of size two, producing an irreducible induced parameter over
$K$. That induced descent belongs to the present smooth theory precisely when its
quadratic pair is selected. This explains why one invariant principal series over $L$
may have both principal and selected supercuspidal descents, while also locating the
ramified dyadic boundary.

At a special parameter the nonzero operator $N$ singles out its kernel line, so its
endomorphisms as a Weil--Deligne object are scalar. Its descents are therefore exactly
the twists $\operatorname{St}_K\otimes\mu\eta$ as $\eta$ runs over $X_{L/K}$, once
one descent $\operatorname{St}_K\otimes\mu$ is fixed. At an irreducible parameter the
same torsor statement holds once one selected supercuspidal descent exists. The
exceptional larger fibers belong to the split semisimple row.

## 13. Compatibility with local Jacquet--Langlands

### 13.1 One parameter for two inner forms

For this chapter assume in addition that $K$ has characteristic zero, and let $D$ be
the quaternion division algebra over $K$. This is exactly the field hypothesis under
which Book 85 proves local Jacquet--Langlands in the selected range: special twists
and tame dihedral packets. If
$\rho$ is a selected representation of $D^\times$ and

$$
\rho\longleftrightarrow\pi=\operatorname{JL}_K(\rho),
$$

both sides have the same indecomposable two-dimensional Weil--Deligne parameter
$\Phi$. A norm character $\mu\circ\operatorname{Nrd}$ corresponds to
$\operatorname{St}_K\otimes\mu$ and hence to $\operatorname{Sp}_2(\mu)$; a
selected higher-dimensional dihedral division representation corresponds to its
quadratically induced Weil parameter and selected supercuspidal.

This common parameter is the correct object to restrict. Defining two unrelated
transfers and comparing their characters afterward would obscure what happens when the
inner form changes under scalar extension.

The phrase “common parameter” also fixes the special boundary. The division character
$\mu\circ\operatorname{Nrd}$ does not share its parameter with the split character
$\mu\circ\det$; it shares it with $\operatorname{St}\otimes\mu$. Their elliptic
characters differ by the Jacquet--Langlands sign, and nonzero monodromy records which
split constituent belongs to the discrete spectrum. Restricting only the two
semisimple character lines would select the wrong constituent after scalar extension.

### 13.2 The quaternion invariant after scalar extension

The Brauer invariant of $D$ is

$$
\operatorname{inv}_K(D)=\frac12\in\mathbf Q/\mathbf Z.
$$

Scalar extension multiplies the invariant by the field degree:

$$
\operatorname{inv}_L(D\otimes_KL)
=n\operatorname{inv}_K(D)=\frac n2\pmod{\mathbf Z}.
$$

Therefore

$$
D\otimes_KL\cong
\begin{cases}
\text{the quaternion division algebra over }L,&n\text{ odd},\\
M_2(L),&n\text{ even}.
\end{cases}
$$

Ramification and residue degree separately do not decide this question; only the total
degree multiplies the Brauer invariant. A ramified quadratic extension splits $D$ just
as an unramified quadratic extension does.

### 13.3 Odd degree, even degree, and the boundary

If $n$ is odd, restriction of the irreducible parameter of a selected dihedral packet
remains irreducible by Clifford theory, while $\operatorname{Sp}_2$ remains special.
Thus $\Phi|_{W_L}$ is still indecomposable. Section 8.4 shows that it remains in the
selected range, so it corresponds to a selected discrete-series representation of
$\mathrm{GL}_2(L)$.
Since $D_L=D\otimes_KL$ is again division, there is then a unique selected $\rho_L$
with

$$
\operatorname{JL}_L(\rho_L)
=\operatorname{BC}_{L/K}(\operatorname{JL}_K\rho).
$$

This defines division-side base change in odd degree.

If $n$ is even, $D_L$ is split, so its multiplicative group is already
$\mathrm{GL}_2(L)$. The restricted common parameter directly defines the parameter-
level scalar-extension transfer from the inner form; this terminology does not mean tensoring the
original representation space from $K$ to $L$. The restricted parameter is selected
and the result may be discrete or
principal. Steinberg parameters
stay special. A selected dihedral supercuspidal parameter may split into two
characters, and then the result is an irreducible principal series. There is no division algebra
over $L$ on the scalar-extension side whose Jacquet--Langlands image could force the
result to remain discrete.

For example, let $E/K$ be quadratic, take a dihedral division representation with
common parameter $\operatorname{Ind}_{W_E}^{W_K}\theta$, and extend scalars to $E$.
The algebra $D\otimes_KE$ splits, while the parameter becomes
$\theta\oplus\theta^\tau$. The scalar-extended transfer is therefore the principal
series $I_E(\theta,\theta^\tau)$. Insisting on applying the division-to-discrete
Jacquet--Langlands bijection over $E$ would be meaningless because the scalar-extended
algebra is no longer division.

This is the precise discrete-versus-principal boundary: it occurs only for a
selected supercuspidal parameter that becomes reducible, necessarily across even
degree, and it coincides with the parity at which the original quaternion algebra splits.

### 13.4 Verification of the compatibility square

When $n$ is odd and the restricted common parameter is selected, the compatibility
square is

$$
\begin{array}{ccc}
\operatorname{Irr}_{\mathrm{sel}}(D^\times)&\xrightarrow{\operatorname{JL}_K}
&\operatorname{Disc}_{\mathrm{sel}}(\mathrm{GL}_2(K))\\
\downarrow\operatorname{BC}^{D}_{L/K}&&
\downarrow\operatorname{BC}_{L/K}\\
\operatorname{Irr}_{\mathrm{sel}}(D_L^\times)&\xrightarrow{\operatorname{JL}_L}
&\operatorname{Disc}_{\mathrm{sel}}(\mathrm{GL}_2(L)).
\end{array}
$$

It commutes because every route restricts the same parameter $\Phi$. This also verifies
central characters, twists, contragredients, conductors, and local factors: each is
already a function of the common restricted parameter, and local Jacquet--Langlands
preserves it.

More explicitly, the upper route first identifies $\rho$ and $\pi$ through equality
of their elliptic parameter. The right vertical route restricts it. The left vertical
route is defined by that same restriction and the lower Jacquet--Langlands inverse.
The two outputs therefore have identical parameters, and injectivity of the local
dictionary makes them isomorphic. The conclusion is exactly as broad as Book 85: it
covers special and selected tame-dihedral division representations, not primitive
wild packets.

When $n$ is even, replace the lower-left corner by the selected part of
$\operatorname{Irr}(\mathrm{GL}_2(L))$ through the chosen splitting
$D_L\simeq M_2(L)$. The result is independent of that splitting up to inner
automorphism, hence up to isomorphism of representations. The lower horizontal arrow
is then the identity on the common parameter. If a supercuspidal becomes principal,
this is not a failure of compatibility; it is the necessary consequence of the split
inner form having a larger full dual than the discrete image of a division group.

For a norm character, both parities give the explicit check

$$
\mu\circ\operatorname{Nrd}
\quad\rightsquigarrow\quad
\operatorname{Sp}_2(\mu)|_{W_L}
=\operatorname{Sp}_2(\mu\circ N_{L/K}),
$$

whose split-side representation is
$\operatorname{St}_L\otimes(\mu\circ N_{L/K})$. For higher-dimensional $\rho$, the
selected dihedral criterion is irreducibility of the restricted common Weil
representation, equivalently the Mackey test of Theorem 8.1.

## 14. Explicit calculations

### 14.1 An unramified cubic lift

Let $L/K$ be unramified cubic and let
$\pi=I_K(\chi_1,\chi_2)$ be spherical with

$$
\chi_1(\varpi_K)=\alpha,\qquad
\chi_2(\varpi_K)=\beta,\qquad
\alpha/\beta\notin\{q_K,q_K^{-1}\}.
$$

Then

$$
\operatorname{BC}_{L/K}\pi
=I_L(\chi_1\circ N_{L/K},\chi_2\circ N_{L/K})
$$

unless the powered ratio reaches an exceptional value; its Satake pair is
$\{\alpha^3,\beta^3\}$. The normalized and raw Hecke eigenvalues are

$$
\alpha^3+\beta^3=(\alpha+\beta)^3-3\alpha\beta(\alpha+\beta),
$$

and

$$
q_L^{1/2}(\alpha^3+\beta^3)=q_K^{3/2}(\alpha^3+\beta^3).
$$

The central scalar operator has eigenvalue $(\alpha\beta)^3$. The conductor remains
zero, while

$$
L_L(s,\operatorname{BC}\pi)
=\frac1{(1-\alpha^3q_L^{-s})(1-\beta^3q_L^{-s})}.
$$

If $(\alpha/\beta)^3=q_L^{\pm1}$, the restricted parameter lies at the boundary and
the lift is the corresponding spherical determinant character. The formula for the
Hecke polynomial remains correct.

### 14.2 A ramified quadratic collapse

Let $L/K$ be ramified quadratic and let $\eta$ be its quadratic class-field character,
so $\eta\circ N_{L/K}=1$. Choose a character $\mu$ of $K^\times$ and set

$$
\chi_1=\mu\nu_K^{-1/2},
\qquad
\chi_2=\mu\eta\nu_K^{1/2}.
$$

The ratio $\chi_1/\chi_2=\eta\nu_K^{-1}$ is not $\nu_K^{\pm1}$, so
$I_K(\chi_1,\chi_2)$ is irreducible. After norm pullback,

$$
\chi_{1,L}=\mu_L\nu_L^{-1/2},
\qquad
\chi_{2,L}=\mu_L\nu_L^{1/2}.
$$

The restricted monodromy is zero, and therefore

$$
\operatorname{BC}_{L/K}I_K(\chi_1,\chi_2)
=\mu_L\circ\det.
$$

This example is ramified, nonspherical in general, and genuinely crosses the
reducibility wall. Choosing the Steinberg constituent over $L$ would introduce
monodromy that was absent over $K$.

Assume now that the residue characteristic is odd and $L/K$ is tamely ramified. Then
$a_K(\eta)=\Delta_{L/K}=1$. If $\mu$ is unramified, the original principal series has
conductor one: one inducing character is unramified and the other has conductor one.
Its $\eta$-twist also has conductor one, with the roles reversed. The exact restriction
formula gives

$$
a_L(\operatorname{BC}\pi)
=a_K(\pi)+a_K(\pi\otimes\eta)-2\Delta_{L/K}=1+1-2=0,
$$

as required for the unramified determinant character $\mu_L\circ\det$. The different
term is not an error correction appended after the fact; without it the conductor
would contradict the explicit lifted representation.

### 14.3 A Steinberg calculation

Let $L/K$ be any cyclic extension and let $\mu$ be unramified with
$\mu(\varpi_K)=c$. Then

$$
\operatorname{BC}_{L/K}(\operatorname{St}_K\otimes\mu)
=\operatorname{St}_L\otimes\mu_L,
$$

where $\mu_L(\varpi_L)=c^f$. Both conductors equal $1$, and

$$
L_L(s,\operatorname{BC}\pi)
=\left(1-c^f q_L^{-s-1/2}\right)^{-1}.
$$

If instead $L/K$ is tamely totally ramified of degree $e$ and $\mu$ has conductor
$m>0$ with surviving top break, then

$$
a_L(\mu_L)=e(m-1)+1,
$$

so

$$
a_L(\operatorname{BC}\pi)=2e(m-1)+2.
$$

For $m=1$ this is $2$, not $2e$. For unramified $\mu$ it is $1$, not $0$ and not
$e$. These three values exhibit separately the tame break, character ramification, and
monodromy contribution.

### 14.4 A dihedral supercuspidal that splits

Let $E/K$ be quadratic, let $\theta\ne\theta^\tau$, and take $L=E$. Put

$$
\pi=\pi_K(E,\theta),
\qquad
\theta_1=\theta,\quad\theta_2=\theta^\tau
$$

as characters of $L^\times$. Mackey restriction gives

$$
\operatorname{BC}_{E/K}\pi=I_E(\theta,
\theta^\tau).
$$

The central character check is instructive. On $K^\times$, the determinant of the
induced parameter is the quadratic sign times $\theta|_{K^\times}$ in the usual
induction determinant formula. After restriction to $E^\times$, the determinant is
$\theta\theta^\tau$, which equals
$\omega_\pi\circ N_{E/K}$ by class-field functoriality. The apparently missing
quadratic sign dies on the norm subgroup.

If $E/K$ is unramified and $a_E(\theta)=m$, then
$a_K(\pi)=2m$. The principal-series conductor upstairs is

$$
a_E(\theta)+a_E(\theta^\tau)=2m,
$$

so unramified conductor invariance is visible directly. If $E/K$ is ramified, the
conductor over $E$ is instead checked by the restriction/different formula; one must
not transplant the unramified equality without its hypothesis.

For instance, if $E/K$ is tamely ramified quadratic and $a_E(\theta)=m$, then
$\Delta_{E/K}=1$ and

$$
a_K(\pi)=m+1,
\qquad
a_E(\operatorname{BC}\pi)
=a_E(\theta)+a_E(\theta^\tau)=2m.
$$

The conductor can increase, stay fixed, or decrease under ramified base change in
other families; here its exact change is dictated by the two exposed character lines.

### 14.5 A dihedral supercuspidal that remains cuspidal

Let $E/K$ be quadratic and let $L/K$ be cyclic of odd degree, so $E\cap L=K$. Put
$M=EL$, and let $\theta$ be a selected admissible character. Its restricted parameter
remains irreducible: if it split, Clifford theory would produce an orbit of size two
inside the odd group $\Gamma$. If the evident pair
$(M/L,\theta\circ N_{M/E})$ is admissible, then

$$
\operatorname{BC}_{L/K}\pi_K(E,\theta)
=\pi_L(M,\theta\circ N_{M/E}).
$$

For an even-degree disjoint extension the same conclusion holds precisely when

$$
(\theta/\theta^\tau)|_{W_M}\ne1.
$$

Here as well, the displayed pair label requires its admissibility. If the restricted
parameter is irreducible but this evident ramified label is not admissible, the
unramified relabeling proved in Theorem 8.1 names the same selected supercuspidal.

Choose, for instance, a character whose quotient with its conjugate has order prime to
$[M:E]$; then it cannot become trivial on $W_M$. Conversely, if that quotient factors
nontrivially through $\operatorname{Gal}(M/E)$, the lift becomes principal series.
This pair of examples shows why the exact criterion needs both the compositum and the
character.

## 15. The local theorem package

### 15.1 The cyclic base-change theorem

We collect the results in a form ready for local use in a later global construction.

**Theorem 15.1 (local cyclic base change for $\mathrm{GL}_2$).** Let $L/K$ be a finite
cyclic extension of nonarchimedean local fields. On the principal, character,
special, and selected tame-dihedral range there is a unique transfer

$$
\operatorname{BC}_{L/K}:
\operatorname{Irr}_{\mathrm{sel}}\mathrm{GL}_2(K)
\longrightarrow\operatorname{Irr}_{\mathrm{sel}}\mathrm{GL}_2(L)
$$

characterized by

$$
\operatorname{rec}_L(\operatorname{BC}_{L/K}\pi)
=\operatorname{rec}_K(\pi)|_{W_L}.
$$

It has the following properties.

1. It is canonical, independent of embeddings and Frobenius lifts, and transitive in
   towers.
2. Its central character is $\omega_\pi\circ N_{L/K}$; it commutes with arbitrary
   character twists and contragredients.
3. For a spherical input it raises Satake parameters to their $f$th powers and sends
   the raw spherical Hecke eigenvalue to
   $q_L^{1/2}(\alpha^f+\beta^f)$. In particular, for an unramified extension of
   degree $n$, one has $f=n$.
4. It sends principal-series inducing characters through norm pullback, with the
   determinant-character interpretation if the restricted ratio reaches
   $\nu_L^{\pm1}$.
5. It sends $\operatorname{St}_K\otimes\mu$ to
   $\operatorname{St}_L\otimes(\mu\circ N_{L/K})$ and preserves nonzero monodromy.
6. A selected dihedral supercuspidal remains supercuspidal exactly when its restricted
   Weil representation is irreducible; otherwise it becomes irreducible principal
   series.
   This is the Mackey criterion of Theorem 8.1. Primitive wild supercuspidals are
   outside the theorem.
7. Its conductor is governed exactly by upper-numbering restriction and by

   $$
   f\,a_L(\operatorname{BC}\pi)
   =\sum_{\eta\in X_{L/K}}a_K(\pi\otimes\eta)-2\Delta_{L/K}.
   $$

8. Its local factors satisfy

   $$
   L_L(s,\operatorname{BC}\pi)
   =\prod_{\eta\in X_{L/K}}L_K(s,\pi\otimes\eta),
   $$

   and, for $\psi_L=\psi_K\circ\operatorname{Tr}_{L/K}$,

   $$
   \epsilon_L(s,\operatorname{BC}\pi,\psi_L)
   =\lambda(L/K,\psi_K)^{-2}
   \prod_{\eta\in X_{L/K}}
   \epsilon_K(s,\pi\otimes\eta,\psi_K).
   $$

9. Its image consists of the selected representations whose parameters admit a
   selected extension to $W_K$. Galois invariance is necessary and is sufficient for
   extension as an unrestricted admissible parameter. Fibers are selected extension
   classes; $X_{L/K}$ acts by twisting and acts simply transitively when the parameter
   has scalar endomorphisms and one selected extension exists.
10. When $K$ has characteristic zero, it is compatible with the selected local
    Jacquet--Langlands correspondence through restriction of the common parameter.
    If $D/K$ is quaternion division,
    $D\otimes_KL$ remains division for odd $n$ and splits for even $n$; in the even
    case a restricted selected supercuspidal parameter may lie on the principal-series
    side.

**Proof.** Given the selected local parameter correspondence of Theorem 4.1,
existence, uniqueness, and canonicity follow from Chapter 5.
Chapters 6--9 prove the type-by-type assertions and their exhaustivity. Chapter 10
proves the conductor identities, Chapter 11 proves factor compatibility with its
additive-character normalization, Chapter 12 proves image and fiber statements, and
Chapter 13 proves inner-form compatibility. No step invokes a global base-change
theorem. $\square$

This package prescribes the local components required in Book 96. It does not assert
that independently chosen local descents globalize, nor that local invariance alone is
the global image criterion: those are global automorphic statements and require the
global cyclic base-change theorem.

### 15.2 A calculation protocol

For a concrete local representation, the following order prevents normalization errors.

First identify its complete Weil--Deligne parameter, including $N$. Restrict the Weil
action to $W_L$ and retain $N$. Translate characters by norm pullback, never by an
imagined restriction from $K^\times$ to $L^\times$. Test the restricted Weil action
for irreducibility before naming the lifted representation. Only then calculate
conductors, using upper breaks or the different formula, and epsilon factors, recording
the additive character.

At an unramified place, use geometric Frobenius and raise its eigenvalues to the
residue degree. At a principal-series boundary, inspect $N$: zero selects the
determinant character, nonzero selects Steinberg. For a dihedral supercuspidal, form the
compositum and apply Mackey restriction. Do not assign a tame quadratic label to a
primitive wild representation outside the selected domain. For a selected
quaternionic input,
multiply the Brauer invariant by $[L:K]$ before deciding what the target inner form is.

This protocol is short because the preceding theory has made each decision exact.

### 15.3 Conclusion

Local cyclic base change is extension of arithmetic information, but its mechanism is
restriction of symmetry. The Weil group makes that reversal of direction visible:
$W_L$ lies inside $W_K$, while local reciprocity turns the same inclusion into the norm
$L^\times\to K^\times$. Once geometric Frobenius and the Weil norm are normalized
together, spherical eigenvalues, central characters, and twists all follow from this
single diagram.

Monodromy and reducibility supply the genuinely rank-two content. A Steinberg
representation remains special because its nilpotent operator survives. A
selected supercuspidal can become principal because an irreducible Weil action can
acquire two lines on a subgroup. Mackey theory makes this transition explicit for
quadratic pairs, while Clifford theory explains the odd-degree parity constraint.
Conductors then record not just a
change of field degree but the new inertia subgroup, Herbrand's reindexing, and the
different. Epsilon factors add one last sensitivity: the trace-compatible additive
character is part of the formula.

Finally, Galois invariance identifies the parameter-level image, selected extension
data describe the smooth fibers,
and norm-trivial characters measure the clean twisting ambiguity whenever the
restricted parameter has scalar endomorphisms. The common parameter also explains
Jacquet--Langlands compatibility, including the moment when a quaternion algebra
splits and a discrete representation is allowed to cross to principal series. The
result is a complete selected local transfer operation: canonical in construction,
explicit in the principal, special, and tame-dihedral families, honest at the wild
boundary, and precise enough to be used one place at a time in cyclic global base
change.
