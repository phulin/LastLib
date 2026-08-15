# Twisted Conjugacy and Geometric Trace Distributions

## Contents

- [Introduction](#introduction)
- [1. The geometric problem created by cyclic base change](#1-the-geometric-problem-created-by-cyclic-base-change)
  - [1.1 Why ordinary conjugacy is no longer the right orbit relation](#11-why-ordinary-conjugacy-is-no-longer-the-right-orbit-relation)
  - [1.2 Standing notation and hypotheses](#12-standing-notation-and-hypotheses)
  - [1.3 The three ledgers: actions, centers, and measures](#13-the-three-ledgers-actions-centers-and-measures)
  - [1.4 The scope and destination of the book](#14-the-scope-and-destination-of-the-book)
- [2. Twisted conjugacy as semilinear algebra](#2-twisted-conjugacy-as-semilinear-algebra)
  - [2.1 The semilinear operator attached to a matrix](#21-the-semilinear-operator-attached-to-a-matrix)
  - [2.2 The ordered norm and its invariant polynomial](#22-the-ordered-norm-and-its-invariant-polynomial)
  - [2.3 Stable norms in degree two](#23-stable-norms-in-degree-two)
  - [2.4 Regular, singular, split, and elliptic types](#24-regular-singular-split-and-elliptic-types)
  - [2.5 Examples that separate the notions](#25-examples-that-separate-the-notions)
- [3. Regular norm fibers](#3-regular-norm-fibers)
  - [3.1 Centralizers of regular matrices](#31-centralizers-of-regular-matrices)
  - [3.2 Reduction of a twisted class to its norm torus](#32-reduction-of-a-twisted-class-to-its-norm-torus)
  - [3.3 The exact image of the regular norm map](#33-the-exact-image-of-the-regular-norm-map)
  - [3.4 Uniqueness in a regular fiber](#34-uniqueness-in-a-regular-fiber)
  - [3.5 Split and quadratic formulas](#35-split-and-quadratic-formulas)
- [4. Twisted centralizers and stable classes](#4-twisted-centralizers-and-stable-classes)
  - [4.1 The twisted centralizer as an algebraic group](#41-the-twisted-centralizer-as-an-algebraic-group)
  - [4.2 Identification in the regular case](#42-identification-in-the-regular-case)
  - [4.3 Stable versus rational twisted conjugacy](#43-stable-versus-rational-twisted-conjugacy)
  - [4.4 The nonsemisimple boundary](#44-the-nonsemisimple-boundary)
  - [4.5 The twisted Weyl discriminant](#45-the-twisted-weyl-discriminant)
- [5. Scalar norms and the quadratic inner-form phenomenon](#5-scalar-norms-and-the-quadratic-inner-form-phenomenon)
  - [5.1 Descent of the matrix algebra](#51-descent-of-the-matrix-algebra)
  - [5.2 Why odd prime degree is split](#52-why-odd-prime-degree-is-split)
  - [5.3 The quadratic cyclic algebra](#53-the-quadratic-cyclic-algebra)
  - [5.4 Classification of scalar-norm fibers](#54-classification-of-scalar-norm-fibers)
  - [5.5 Local and global consequences](#55-local-and-global-consequences)
- [6. Local twisted orbital integrals](#6-local-twisted-orbital-integrals)
  - [6.1 Local cyclic algebras, including split places](#61-local-cyclic-algebras-including-split-places)
  - [6.2 Haar and quotient measures](#62-haar-and-quotient-measures)
  - [6.3 Definition and absolute convergence](#63-definition-and-absolute-convergence)
  - [6.4 Invariance, scaling, and local constancy](#64-invariance-scaling-and-local-constancy)
  - [6.5 Normalized and stable distributions](#65-normalized-and-stable-distributions)
- [7. Adelic measures and coefficients](#7-adelic-measures-and-coefficients)
  - [7.1 The determinant-one realization](#71-the-determinant-one-realization)
  - [7.2 Tamagawa-compatible quotient measures](#72-tamagawa-compatible-quotient-measures)
  - [7.3 Volumes of twisted centralizers](#73-volumes-of-twisted-centralizers)
  - [7.4 Factorization of adelic orbital integrals](#74-factorization-of-adelic-orbital-integrals)
  - [7.5 Independence under rescaling](#75-independence-under-rescaling)
- [8. Test functions and the twisted automorphic kernel](#8-test-functions-and-the-twisted-automorphic-kernel)
  - [8.1 The admissible Schwartz class](#81-the-admissible-schwartz-class)
  - [8.2 Strong cuspidality at one place](#82-strong-cuspidality-at-one-place)
  - [8.3 The twisted kernel](#83-the-twisted-kernel)
  - [8.4 Convergence and smoothness before taking the diagonal](#84-convergence-and-smoothness-before-taking-the-diagonal)
  - [8.5 The diagonal geometric distribution](#85-the-diagonal-geometric-distribution)
- [9. Twisted parabolic geometry](#9-twisted-parabolic-geometry)
  - [9.1 Semilinear invariant lines](#91-semilinear-invariant-lines)
  - [9.2 Incidence multiplicities](#92-incidence-multiplicities)
  - [9.3 Truncation in the unique cusp](#93-truncation-in-the-unique-cusp)
  - [9.4 Unfolding the parabolic channel](#94-unfolding-the-parabolic-channel)
  - [9.5 Cancellation of split and nonsemisimple terms](#95-cancellation-of-split-and-nonsemisimple-terms)
- [10. Elliptic and scalar-norm unfolding](#10-elliptic-and-scalar-norm-unfolding)
  - [10.1 Closed twisted orbits](#101-closed-twisted-orbits)
  - [10.2 Orbit-by-orbit unfolding](#102-orbit-by-orbit-unfolding)
  - [10.3 The split scalar-norm distribution](#103-the-split-scalar-norm-distribution)
  - [10.4 Quadratic exceptional terms](#104-quadratic-exceptional-terms)
  - [10.5 The provisional geometric expansion](#105-the-provisional-geometric-expansion)
- [11. Absolute convergence of the geometric expansion](#11-absolute-convergence-of-the-geometric-expansion)
  - [11.1 Heights on twisted classes](#111-heights-on-twisted-classes)
  - [11.2 Counting norm classes](#112-counting-norm-classes)
  - [11.3 Decay of twisted orbital integrals](#113-decay-of-twisted-orbital-integrals)
  - [11.4 Bounds for centralizer volumes](#114-bounds-for-centralizer-volumes)
  - [11.5 Summability](#115-summability)
- [12. The convergent geometric distributions](#12-the-convergent-geometric-distributions)
  - [12.1 The main geometric theorem](#121-the-main-geometric-theorem)
  - [12.2 Continuity and independence of cutoffs](#122-continuity-and-independence-of-cutoffs)
  - [12.3 Central-character realization](#123-central-character-realization)
  - [12.4 Change of generator](#124-change-of-generator)
- [13. Local-global norm bookkeeping](#13-local-global-norm-bookkeeping)
  - [13.1 Localization of a global twisted class](#131-localization-of-a-global-twisted-class)
  - [13.2 The regular Hasse norm condition](#132-the-regular-hasse-norm-condition)
  - [13.3 Quaternionic obstruction data](#133-quaternionic-obstruction-data)
  - [13.4 Product constraints and measures](#134-product-constraints-and-measures)
- [14. Worked geometric models](#14-worked-geometric-models)
  - [14.1 A split regular norm](#141-a-split-regular-norm)
  - [14.2 An elliptic quadratic norm](#142-an-elliptic-quadratic-norm)
  - [14.3 An unramified cubic example](#143-an-unramified-cubic-example)
  - [14.4 A quadratic scalar norm with division centralizer](#144-a-quadratic-scalar-norm-with-division-centralizer)
  - [14.5 A nonsemisimple norm and its disappearance](#145-a-nonsemisimple-norm-and-its-disappearance)
- [15. The geometric package for cyclic comparison](#15-the-geometric-package-for-cyclic-comparison)
  - [15.1 The classification and measure ledger](#151-the-classification-and-measure-ledger)
  - [15.2 What remains local](#152-what-remains-local)
  - [15.3 Conclusion](#153-conclusion)

## Introduction

Changing a number field changes the group on which automorphic functions live. If $E/F$ is
cyclic and $\sigma$ generates its Galois group, the natural symmetry on
$\mathrm{GL}_2(\mathbf A_E)$ is not ordinary conjugation but the operation

$$
x:\delta\longmapsto x^{-1}\delta\sigma(x).
$$

This small alteration changes every geometric ingredient of a trace formula. A conjugacy
class becomes a twisted conjugacy class. The usual centralizer becomes the fixed group of a
semilinear transformation. The product

$$
\delta\sigma(\delta)\cdots\sigma^{\ell-1}(\delta)
$$

is not usually fixed entry by entry by $\sigma$, yet its characteristic polynomial is defined
over $F$. That polynomial supplies the stable norm class over $F$. The purpose of this book
is to make this geometry exact and then to prove that the geometric distributions built from
it genuinely converge.

There are two reasons not to treat the construction as a formal variant of ordinary
conjugacy. First, the norm map is restricted. A regular matrix $\gamma$ over $F$ occurs as a
norm only when it is a norm from its own centralizer torus. For a split regular matrix this
means that both eigenvalues are field norms; for an elliptic matrix it is a norm condition in
a quadratic field. Second, scalar norms hide an exceptional phenomenon. In odd prime degree
they have split twisted centralizer, but in degree two a nonnorm scalar produces a quaternion
division algebra. These exceptional classes are not errors at the singular boundary. They
are genuine elliptic terms and must appear in the global distribution.

The analytic problem is equally real. The diagonal of a twisted automorphic kernel is an
infinite rational-point sum on a noncompact quotient. It cannot first be regrouped into
orbits and justified afterward. We truncate the unique rank-one cusp, regroup only on the
truncated domain, and use one strongly cuspidal local factor to annihilate the twisted
parabolic channel. We then prove separate height, counting, orbital-decay, and volume bounds
for the surviving terms. The result is an absolutely convergent sum, not a notation for a
regularized expression.

The background needed from the preceding theory is deliberately small and explicit. The
automorphic-representation input supplies the adelic quotient, right-action convention,
quotient measures, rank-one reduction theory, and the rapid-decay argument for a vanishing
constant term. The local cyclic-base-change input fixes geometric Frobenius and, more
importantly here, the direction $E_v^\times\to F_v^\times$ of the field norm. We use no local
character identity from that theory and no global base-change theorem. Hilbert 90, descent for
finite-dimensional algebras, the cyclic-algebra norm criterion, and global Brauer reciprocity
are ordinary algebraic and number-theoretic inputs already available in the preceding
foundation; whenever a matrix or torus norm depends on them, the reduction to the precise
input is written out below. Thus the norm geometry developed here is an input to a later
comparison, not a consequence of it.

## 1. The geometric problem created by cyclic base change

### 1.1 Why ordinary conjugacy is no longer the right orbit relation

Let $E/F$ be cyclic of prime degree $\ell$, and choose a generator
$\sigma\in\operatorname{Gal}(E/F)$. Applying $\sigma$ entrywise defines an automorphism of
$G(E)$ and $G(\mathbf A_E)$, where $G=\mathrm{GL}_2$. A twisted trace pairs right convolution
with this field automorphism. If

$$
K_f(x,y)=\sum_{\delta\in G(E)}f(x^{-1}\delta y),
$$

then inserting $y=\sigma(x)$ gives

$$
K_f^\sigma(x,x)=\sum_{\delta\in G(E)}
f(x^{-1}\delta\sigma(x)).
\tag{1.1}
$$

Replacing $x$ by $gx$ conjugates the rational index by

$$
\delta\longmapsto g^{-1}\delta\sigma(g).
\tag{1.2}
$$

Thus (1.2), not $g^{-1}\delta g$, is the orbit relation forced by the kernel. Two elements
$\delta,\delta'\in G(E)$ are **$\sigma$-conjugate** if

$$
\delta'=g^{-1}\delta\sigma(g)
$$

for some $g\in G(E)$. The same definition over an $F$-algebra $R$ uses
$E\otimes_FR$. Stable $\sigma$-conjugacy permits $g$ after extension to an algebraic closure
of $F$.

The ordering in (1.2) matters. With our right-action convention, the twisted kernel contains
$x^{-1}\delta\sigma(x)$. Replacing it by $x\delta\sigma(x)^{-1}$ would invert several later
norm identities. Nothing is gained by switching conventions midstream, so all twisted
centralizers and orbital integrals below use (1.2).

### 1.2 Standing notation and hypotheses

Throughout the book:

- $F$ is a number field;
- $E/F$ is cyclic of prime degree $\ell$;
- $\sigma$ is a fixed generator of $\operatorname{Gal}(E/F)$;
- $G=\mathrm{GL}_{2/F}$ and
  $H=\operatorname{Res}_{E/F}(G_E)$, so $H(F)=G(E)$ and
  $H(\mathbf A_F)=G(\mathbf A_E)$;
- $\theta$ is the $F$-automorphism of $H$ induced by $\sigma$.

At a place $v$ of $F$, write

$$
E_v=E\otimes_FF_v=\prod_{w\mid v}E_w.
$$

The automorphism $\sigma$ permutes the factors and acts within each field factor when the
decomposition group is nontrivial. Every local definition is made for this étale algebra, so
split places are included rather than silently discarded.

Absolute values have the product-formula normalization. At a finite place
$|\varpi_v|_v=q_v^{-1}$, and at a complex place the absolute value is the square of the usual
complex modulus. Haar measures are fixed explicitly in Chapters 6 and 7. Until then, all
algebraic statements are independent of measure.

We write $Z$ for the scalar center of $G$. The main analytic realization uses

$$
H(\mathbf A_F)^1
=\{h\in G(\mathbf A_E):|\det h|_{\mathbf A_E}=1\}.
\tag{1.3}
$$

Every rational point of $G(E)$ lies in this group by the product formula. The quotient

$$
[H]^1=G(E)\backslash H(\mathbf A_F)^1
\tag{1.4}
$$

has finite invariant volume. Working on (1.4) removes the one real determinant direction
without imposing a central character. Section 12.3 translates the result to the equivalent
fixed-central-character realization.

### 1.3 The three ledgers: actions, centers, and measures

Three kinds of bookkeeping recur.

First is the action ledger. Functions are translated on the right, $\sigma$ acts entrywise,
and the twisted orbit is $g^{-1}\delta\sigma(g)$. The associated ordered norm is

$$
N_\sigma(\delta)=
\delta\sigma(\delta)\cdots\sigma^{\ell-1}(\delta).
\tag{1.5}
$$

Changing the generator changes the ordered product, the twisting operator, and generally the
distribution itself. Section 12.4 gives the exact conversion rule. What does not change is
the construction: actions, norms, and measures transform together.

Second is the center ledger. A scalar $z\in E^\times$ changes the norm by

$$
N_\sigma(z\delta)=N_{E/F}(z)N_\sigma(\delta).
\tag{1.6}
$$

Thus ordinary norms and projective norms carry different information. We retain actual
matrices through the classification and only pass to central characters after the orbit
coefficients are defined. This is what makes the quadratic scalar obstruction visible.

Third is the measure ledger. A Haar measure on a twisted centralizer and the quotient measure
on its orbit are complementary. Multiplying the former by $c$ divides the latter by $c$.
The trace-formula term is the product of a centralizer volume and an orbital integral, so the
two changes cancel. Any formula that specifies these measures independently is incomplete.

### 1.4 The scope and destination of the book

The goal is geometric. We shall:

1. classify rational and stable twisted classes through semilinear algebra;
2. determine the precise image and fibers of the regular norm map;
3. identify all twisted centralizers, including the quadratic quaternionic exception;
4. define compatible local and adelic orbital measures;
5. construct the twisted diagonal distribution for a strongly cuspidal test class;
6. prove parabolic cancellation and absolute convergence of the surviving orbit sum.

We do not prove a spectral expansion or a global cyclic base-change theorem. Nor do we prove
explicit unit, Iwahori, ramified, or level fundamental lemmas. The local orbital distributions
are defined here with the exact normalizations needed for those later calculations, but their
evaluation is a separate problem.

The prime-degree hypothesis is used at two decisive points. It keeps the intermediate-field
geometry rigid, and it makes the scalar obstruction either trivial for odd $\ell$ or purely
quaternionic for $\ell=2$. The regular norm-fiber arguments themselves work more generally,
but the clean global classification stated here is tailored to prime degree.

The dependency boundary is equally sharp. The adelic topology, quotient measures, reduction
theory, and rapid decay of cuspidal automorphic forms are the global analytic background. The
local cyclic-base-change theory fixes the direction of the field norm and the geometric
Frobenius convention, but none of its representation-theoretic transfer assertions is used to
deduce an orbit identity. Hilbert 90, cyclic algebras, and the cyclic Hasse norm theorem are
used in their classical algebraic forms, and the relevant norm arguments are reproduced where
they enter. No later trace comparison is a premise of this book.

## 2. Twisted conjugacy as semilinear algebra

### 2.1 The semilinear operator attached to a matrix

Twisted conjugacy becomes ordinary similarity once matrices are interpreted as semilinear
operators. Let $V=E^2$. For $\delta\in G(E)$ define

$$
T_\delta:V\longrightarrow V,
\qquad T_\delta(v)=\delta\sigma(v).
\tag{2.1}
$$

It is $\sigma$-semilinear:

$$
T_\delta(av)=\sigma(a)T_\delta(v).
$$

If $\delta'=g^{-1}\delta\sigma(g)$, then

$$
T_{\delta'}=g^{-1}T_\delta g.
\tag{2.2}
$$

Conversely, every $E$-linear similarity between $T_\delta$ and $T_{\delta'}$ gives (2.2) and
hence twisted conjugacy. We have therefore proved the first classification principle.

**Proposition 2.1.** Twisted conjugacy classes in $G(E)$ are exactly $E$-linear similarity
classes of invertible $\sigma$-semilinear operators on $E^2$.

This reformulation explains why invariant subspaces will matter. A line in $E^2$ stabilized by
$T_\delta$ is the twisted analogue of an eigenline. Split and nonsemisimple geometric terms
will be organized by these lines, while elliptic terms are precisely those for which no such
line descends from the norm over $F$.

### 2.2 The ordered norm and its invariant polynomial

Iterating (2.1) $\ell$ times produces an $E$-linear operator:

$$
T_\delta^\ell=N_\sigma(\delta).
\tag{2.3}
$$

The ordered norm need not lie in $G(F)$. Instead,

$$
\sigma(N_\sigma(\delta))
=\delta^{-1}N_\sigma(\delta)\delta.
\tag{2.4}
$$

Indeed, applying $\sigma$ cyclically moves the first factor of (1.5) to the end, and conjugation
by $\delta$ moves it back. Taking trace and determinant in (2.4) gives

$$
\operatorname{tr}N_\sigma(\delta)\in F,
\qquad
\det N_\sigma(\delta)=N_{E/F}(\det\delta)\in F^\times.
\tag{2.5}
$$

Thus

$$
p_\delta(X)=
X^2-s_\delta X+d_\delta,
\quad
s_\delta=\operatorname{tr}N_\sigma(\delta),
\quad
d_\delta=\det N_\sigma(\delta),
\tag{2.6}
$$

belongs to $F[X]$.

Twisted conjugation changes $N_\sigma(\delta)$ by ordinary conjugation:

$$
N_\sigma(g^{-1}\delta\sigma(g))
=g^{-1}N_\sigma(\delta)g.
\tag{2.7}
$$

This follows by multiplying the $\ell$ twisted factors and observing that all intermediate
$\sigma^i(g)\sigma^i(g)^{-1}$ terms telescope. Consequently $p_\delta$ is constant on
twisted classes.

Two further identities are useful normalization checks. On the top exterior power,
$T_\delta$ acts as the semilinear map

$$
\bigwedge^2T_\delta=(\det\delta)\sigma,
$$

so its $\ell$th power is multiplication by $N_{E/F}(\det\delta)$. This recovers the determinant
formula in (2.5) without multiplying $2\times2$ matrices. Also, scalar multiplication changes
the semilinear operator by $T_{z\delta}=zT_\delta$, whence

$$
(T_{z\delta})^\ell=N_{E/F}(z)T_\delta^\ell.
\tag{2.7a}
$$

This is the operator explanation for (1.6). It shows at once why the projective stable norm is
well defined only modulo the scalar norm subgroup.

One should not confuse (2.3) with taking an ordinary $\ell$th power of a matrix. If $\delta$
has coefficients outside $F$, the intermediate Galois conjugates are essential. Nor can the
ordered factors be cyclically permuted as equal matrices; a cyclic permutation changes the
product by conjugation, which is exactly why trace and determinant descend while the matrix
itself need not.

### 2.3 Stable norms in degree two

The polynomial (2.6) determines a matrix over $F$ up to rational conjugacy except at the scalar
versus Jordan distinction. This produces the stable norm.

**Definition 2.2.** The **stable norm** of $\delta$ is the $G(F)$-conjugacy class of a matrix
$\gamma_\delta\in G(F)$ defined as follows.

- If $N_\sigma(\delta)$ is noncentral, take the companion matrix

  $$
  \gamma_\delta=
  \begin{pmatrix}0&-d_\delta\\1&s_\delta\end{pmatrix}.
  \tag{2.8}
  $$

- If $N_\sigma(\delta)=aI$, take $\gamma_\delta=aI$.

Why is this a stable norm rather than merely a matrix with the same polynomial? If the norm is
noncentral, its minimal polynomial has degree two. A cyclic-vector basis over $E$ conjugates it
to (2.8). If it is central, it already equals the scalar matrix over $F$ because (2.4) forces
$a\in F$. Hence $N_\sigma(\delta)$ and $\gamma_\delta$ are conjugate over $E$ in every case.

**Proposition 2.3.** The stable norm depends only on the twisted conjugacy class. Two
noncentral ordered norms have the same stable norm if and only if they have the same
characteristic polynomial. A scalar ordered norm is never identified with a noncentral Jordan
norm, even though both can have the same repeated characteristic polynomial.

**Proof.** The first assertion follows from (2.7). For noncentral $2\times2$ matrices, the
minimal and characteristic polynomials agree, and the cyclic-vector argument conjugates both
matrices to the same companion matrix. A scalar matrix remains scalar after every field
extension, whereas a Jordan matrix remains noncentral, proving the final assertion. $\square$

The last clause is essential. The discriminant

$$
\Delta_\delta=s_\delta^2-4d_\delta
\tag{2.9}
$$

detects regular semisimplicity, but $\Delta_\delta=0$ does not by itself distinguish the central
and nonsemisimple strata.

### 2.4 Regular, singular, split, and elliptic types

We call $\delta$ **strongly $\sigma$-regular** when $N_\sigma(\delta)$ is regular semisimple,
equivalently when $\Delta_\delta\ne0$. It is **$\sigma$-elliptic** when its stable norm has
irreducible characteristic polynomial over $F$. It is **$\sigma$-split regular** when that
polynomial has two distinct roots in $F$.

There are two singular strata. A **nonsemisimple twisted class** has noncentral ordered norm
with repeated root. A **scalar-norm class** has ordered norm $aI$. Scalar-norm classes are
twisted semisimple because the corresponding semilinear operator has semisimple image in the
disconnected group $H\rtimes\langle\theta\rangle$, but their centralizers need not be split.
Chapter 5 determines them.

For a strongly regular class, let

$$
K_\delta=F[X]/(p_\delta(X)).
\tag{2.10}
$$

If the class is split, $K_\delta\simeq F\times F$; if it is elliptic,
$K_\delta/F$ is quadratic. The centralizer of the stable norm is the induced torus

$$
T_\delta=\operatorname{Res}_{K_\delta/F}\mathbf G_m.
\tag{2.11}
$$

Modulo the scalar $\mathbf G_m$, this torus is split in the first case and anisotropic in the
second. This is the geometric reason the split terms belong to the parabolic channel and the
elliptic terms have compact centralizer quotient.

### 2.5 Examples that separate the notions

If $b\in E^\times$ and $\delta=bI$, then

$$
N_\sigma(\delta)=N_{E/F}(b)I.
$$

This is the split scalar-norm model. Its twisted orbit is not a point: the elements
$x^{-1}b\sigma(x)$ generally are not scalar. What is central is the stable norm, not every
member of the twisted orbit.

If $\delta=\operatorname{diag}(b_1,b_2)$, then

$$
N_\sigma(\delta)=
\operatorname{diag}(N_{E/F}(b_1),N_{E/F}(b_2)).
$$

Distinct norms give a split regular class. This example already shows that the determinant
condition is not sufficient for a prescribed split norm: each eigenvalue, not merely their
product, must be a field norm.

Let $\ell=2$ and take $a\in F^\times$. The matrix

$$
\delta_a=\begin{pmatrix}0&a\\1&0\end{pmatrix}
\tag{2.12}
$$

has entries in $F$, so

$$
N_\sigma(\delta_a)=\delta_a^2=aI.
$$

If $a$ is not a norm from $E^\times$, this class cannot be twisted conjugate to a scalar matrix,
even though its ordered norm is scalar. Its twisted centralizer is the multiplicative group of
the quaternion algebra $(E/F,a)$. This is the exceptional class developed in Chapter 5.

Finally, take

$$
\delta=\begin{pmatrix}b&c\\0&b\end{pmatrix}.
$$

Its ordered norm is upper triangular with repeated diagonal entry $N_{E/F}(b)$. Depending on
the twisted trace of $c/b$, the upper-right entry may vanish or not. The two outcomes lie in
the scalar-norm and nonsemisimple strata respectively. Equal discriminant and determinant do
not identify them.

## 3. Regular norm fibers

### 3.1 Centralizers of regular matrices

Let $\gamma\in G(F)$ be regular semisimple and put $K=F[\gamma]$. Then $K$ is the étale
quadratic algebra determined by the characteristic polynomial of $\gamma$.

**Lemma 3.1.** The commutant of $\gamma$ in $M_2(F)$ is $F[\gamma]$, and

$$
G_\gamma=\operatorname{Cent}_G(\gamma)
\simeq\operatorname{Res}_{K/F}\mathbf G_m.
\tag{3.1}
$$

The identity remains valid after every scalar extension.

**Proof.** Choose a cyclic vector $v$, so $(v,\gamma v)$ is a basis. If $A$ commutes with
$\gamma$ and $Av=av+b\gamma v$, commutation determines
$A(\gamma v)=a\gamma v+b\gamma^2v$. Thus $A=a+b\gamma$. Conversely every polynomial in
$\gamma$ commutes with it. Taking units gives (3.1), and the same basis argument works after
scalar extension. $\square$

The induced nature of this torus will remove a possible cohomological ambiguity: Hilbert's
Theorem 90 applies to the multiplicative group of the quadratic étale algebra.

### 3.2 Reduction of a twisted class to its norm torus

Suppose $\delta$ is strongly $\sigma$-regular with stable norm $\gamma\in G(F)$. Choose
$y\in G(E)$ such that

$$
y^{-1}N_\sigma(\delta)y=\gamma
$$

and replace $\delta$ by the twisted conjugate

$$
\delta'=y^{-1}\delta\sigma(y).
$$

Then $N_\sigma(\delta')=\gamma$. Applying (2.4) to $\delta'$ and using
$\sigma(\gamma)=\gamma$ gives

$$
\delta'^{-1}\gamma\delta'=\gamma.
$$

Hence

$$
\delta'\in G_\gamma(E)=T_\gamma(E).
\tag{3.2}
$$

Inside this commutative torus the ordered matrix norm is the ordinary torus norm. We have
proved:

**Proposition 3.2 (torus reduction).** Every strongly regular twisted class can be represented
by $t\in T_\gamma(E)$ satisfying

$$
N_{E/F}^{T_\gamma}(t)=\gamma.
\tag{3.3}
$$

Conversely, any $t$ satisfying (3.3), viewed in $G(E)$, has stable norm $\gamma$.

This is the decisive reduction. A nonlinear-looking norm problem in matrices has become an
abelian norm equation in the centralizer of the desired norm.

### 3.3 The exact image of the regular norm map

The preceding proposition gives both necessity and sufficiency.

**Theorem 3.3 (regular norm criterion).** Let $\gamma\in G(F)$ be regular semisimple and let
$T_\gamma$ be its centralizer. There exists a strongly regular $\delta\in G(E)$ with stable
norm $\gamma$ if and only if

$$
\gamma\in N_{E/F}^{T_\gamma}(T_\gamma(E)).
\tag{3.4}
$$

**Proof.** Necessity is Proposition 3.2. For sufficiency, choose
$t\in T_\gamma(E)$ with torus norm $\gamma$ and set $\delta=t$. Since $\sigma$ acts on the
$E$-points of the $F$-torus and the torus is commutative, its ordered product is exactly
$N_{E/F}^{T_\gamma}(t)=\gamma$. The norm is regular, so $t$ is strongly regular. $\square$

The determinant condition

$$
\det\gamma\in N_{E/F}(E^\times)
\tag{3.5}
$$

is necessary, because it follows from (2.5), but it is generally weaker than (3.4). A trace
formula comparison must use the torus norm condition, not replace it by (3.5).

### 3.4 Uniqueness in a regular fiber

Existence does not yet show that a stable norm determines one rational twisted class. In rank
two it does.

**Theorem 3.4 (regular fiber theorem).** If $\delta_1$ and $\delta_2$ are strongly regular and
have the same stable norm $\gamma$, then they are $\sigma$-conjugate by an element of $G(E)$.
Thus every regular norm fiber is either empty or one rational twisted conjugacy class.

**Proof strategy.** Move both classes into $T_\gamma(E)$. Their quotient has torus norm one.
The torus is the multiplicative group of an étale quadratic algebra, so Hilbert 90 writes that
quotient as a twisted coboundary.

**Proof.** By Proposition 3.2, twisted-conjugate $\delta_i$ to elements
$t_i\in T_\gamma(E)$ with $N(t_i)=\gamma$. Then $u=t_2t_1^{-1}$ has norm one. Write
$K=F[\gamma]$. The algebra

$$
K\otimes_FE
$$

is finite étale over $K$, with cyclic semilinear action induced by $\sigma$. Hilbert 90 for
this étale algebra gives $x\in(K\otimes_FE)^\times=T_\gamma(E)$ such that

$$
u=x^{-1}\sigma(x).
$$

Since the torus is commutative,

$$
x^{-1}t_1\sigma(x)=t_1u=t_2.
$$

Undoing the initial conjugations proves the theorem. $\square$

The theorem is stronger than stable conjugacy. No hidden rational classes split off inside a
regular stable fiber. The scalar-norm boundary is exactly where this simple statement must be
replaced by the inner-form analysis of Chapter 5.

### 3.5 Split and quadratic formulas

If $\gamma$ is split regular with eigenvalues $a\ne b$ in $F^\times$, then

$$
T_\gamma\simeq\mathbf G_m\times\mathbf G_m.
$$

The criterion (3.4) becomes

$$
a\in N_{E/F}(E^\times),
\qquad b\in N_{E/F}(E^\times).
\tag{3.6}
$$

If $a=N(u)$ and $b=N(v)$, the representative
$\delta=\operatorname{diag}(u,v)$ has norm $\gamma$.

If $\gamma$ is elliptic and $K=F[\gamma]$ is a quadratic field, regard $\gamma$ as an element
of $K^\times$ through the regular representation $K\hookrightarrow M_2(F)$. Then

$$
T_\gamma(E)=(K\otimes_FE)^\times
$$

and (3.4) reads

$$
\gamma\in
N_{K\otimes_FE/K}((K\otimes_FE)^\times).
\tag{3.7}
$$

When $K$ and $E$ are linearly disjoint, $K\otimes_FE=KE$ and this is the ordinary field norm
from $KE$ to $K$. If $\ell=2$ and $K=E$, then
$K\otimes_FE\simeq E\times E$ as a $K$-algebra, and the norm is surjective. Thus every
$\gamma\in E^\times$ in that elliptic torus is a twisted norm in this exceptional contained
case.

The possibilities can be kept in one ledger:

| stable norm $\gamma$                 | centralizer algebra $K$          | norm condition                       | twisted centralizer                   |
| ------------------------------------ | -------------------------------- | ------------------------------------ | ------------------------------------- |
| split regular with eigenvalues $a,b$ | $F\times F$                      | $a,b\in N(E^\times)$                 | $\mathbf G_m^2$                       |
| elliptic regular                     | quadratic field $K$              | $\gamma\in N((K\otimes E)^\times)$   | $\operatorname{Res}_{K/F}\mathbf G_m$ |
| noncentral repeated root             | $F[\varepsilon]/(\varepsilon^2)$ | unit norm in the dual-number algebra | its unit group                        |
| scalar $aI$                          | degree-two descent algebra       | Chapter 5                            | an inner form of $\mathrm{GL}_2$      |

The first two rows are reductive and strongly regular. The third is nonreductive and belongs to
the parabolic boundary. The fourth is semisimple but singular and is controlled by a Brauer
class. This table is not merely taxonomy: each row dictates a different convergence argument.

There is also a useful functorial consequence of the regular fiber theorem. If $F\subset F'$
is any extension, a global regular twisted class localizes to the unique class over $F'$ above
the localized norm. Conversely, if the torus norm equation already has a solution over $F$,
choosing a different solution after scalar extension cannot create a new rational fiber. Thus
all ambiguity in local-global comparison lies in existence and in measures, not in a hidden
choice among regular representatives.

## 4. Twisted centralizers and stable classes

### 4.1 The twisted centralizer as an algebraic group

For $\delta\in H(F)=G(E)$ define the **twisted centralizer** $I_\delta$ by

$$
I_\delta(R)=
\{x\in G(E\otimes_FR):x^{-1}\delta\sigma(x)=\delta\}
\tag{4.1}
$$

for every $F$-algebra $R$. It is a closed $F$-subgroup of $H$. In semilinear language,
$I_\delta$ is the group of $E\otimes_FR$-linear automorphisms commuting with $T_\delta$.

Its Lie algebra is

$$
\mathfrak i_\delta(R)=
\{X\in M_2(E\otimes_FR):
X=\delta\sigma(X)\delta^{-1}\}.
\tag{4.2}
$$

If $\delta'=g^{-1}\delta\sigma(g)$, conjugation by $g$ identifies $I_{\delta'}$ with
$I_\delta$. Thus the isomorphism class and its Haar-volume term are invariants of the twisted
class.

Every $x\in I_\delta$ commutes with $N_\sigma(\delta)$. Indeed, iterate the relation in (4.1)
$\ell$ times to obtain

$$
x=N_\sigma(\delta)xN_\sigma(\delta)^{-1}.
\tag{4.3}
$$

For regular norm, this forces $x$ into the norm torus and makes the centralizer transparent.

### 4.2 Identification in the regular case

Choose the torus representative $t\in T_\gamma(E)$ supplied by Proposition 3.2. If
$x\in I_t(R)$, equation (4.3) puts $x$ in $T_\gamma(E\otimes_FR)$. Since this torus is
commutative, (4.1) reduces to

$$
\sigma(x)=x.
$$

The fixed points are precisely $T_\gamma(R)$. Hence:

**Theorem 4.1.** For a strongly regular twisted class with stable norm $\gamma$,

$$
I_\delta\simeq T_\gamma=G_\gamma.
\tag{4.4}
$$

The isomorphism is canonical up to conjugacy, which is exactly the ambiguity already present in
choosing a representative of $\gamma$.

If $\gamma$ is split regular, $I_\delta\simeq\mathbf G_m^2$. If $\gamma$ is elliptic,
$I_\delta\simeq\operatorname{Res}_{K/F}\mathbf G_m$ for a quadratic field $K/F$. In the
second case $I_\delta/Z$ is anisotropic, and

$$
I_\delta(F)\backslash I_\delta(\mathbf A_F)^1
$$

is compact. This compactness will justify elliptic unfolding.

### 4.3 Stable versus rational twisted conjugacy

Over an algebraic closure, every quadratic étale torus is split and Hilbert 90 again shows that
a regular stable norm has one stable twisted fiber. The rational fiber theorem says more: the
fiber does not split over $F$.

This can also be expressed cohomologically without using it as a black box. Fix a representative
$\delta$. If $g$ stably conjugates it to an $F$-rational twisted element, the cocycle measuring
the failure of $g$ to be rational takes values in $I_\delta$. Rational classes in the stable
class would therefore be measured by

$$
\ker\bigl(H^1(F,I_\delta)\longrightarrow H^1(F,H)\bigr).
\tag{4.5}
$$

Here $I_\delta\simeq\operatorname{Res}_{K/F}\mathbf G_m$, so Hilbert 90 gives
$H^1(F,I_\delta)=1$. Also $H^1(F,H)=H^1(E,\mathrm{GL}_2)=1$. Thus (4.5) is trivial, agreeing
with Theorem 3.4.

The argument records its hypotheses. It depends on the induced torus structure particular to
regular elements of $\mathrm{GL}_2$. For another reductive group, a stable twisted class may
contain several rational twisted classes. Even for $\mathrm{GL}_2$, scalar norms can have
non-toral centralizer and require separate analysis.

### 4.4 The nonsemisimple boundary

Suppose the ordered norm is noncentral with repeated eigenvalue $a$. Its centralizer algebra is

$$
A=F[\varepsilon]/(\varepsilon^2),
$$

embedded by $\varepsilon\mapsto\gamma-aI$. The same torus-reduction calculation, with the word
``torus'' replaced by the unit group $A^\times$, shows that $\delta$ can be represented in
$(A\otimes_FE)^\times$ and that

$$
I_\delta\simeq A^\times.
\tag{4.6}
$$

For completeness, the norm-one fiber in this nonreduced algebra is still a coboundary. The
exact sequence

$$
1\longrightarrow1+\varepsilon E
\longrightarrow(A\otimes_FE)^\times
\longrightarrow E^\times\longrightarrow1
$$

has additive kernel $1+\varepsilon E\simeq(E,+)$. Multiplicative Hilbert 90 handles the
quotient, and additive Hilbert 90 handles the kernel. Therefore two representatives with the
same nonsemisimple norm are twisted conjugate.

The group $A^\times$ is not reductive: modulo scalars it has a one-dimensional unipotent
radical. Its adelic quotient is noncompact in exactly the direction associated with a Borel.
Consequently these classes cannot be unfolded as isolated elliptic orbital terms. They are
part of the parabolic cancellation in Chapter 9.

### 4.5 The twisted Weyl discriminant

The tangent map to the twisted orbit at $\delta$ is

$$
\mathfrak h\longrightarrow\mathfrak h,
\qquad
X\longmapsto\operatorname{Ad}(\delta)\sigma(X)-X,
\tag{4.7}
$$

whose kernel is $\mathfrak i_\delta$. For a twisted semisimple element, choose an
$I_\delta$-stable complement and define the **twisted Weyl discriminant** by

$$
D^\sigma(\delta)=
\det_F\left(1-\operatorname{Ad}(\delta)\sigma
\mathbin{\big|}\mathfrak h/\mathfrak i_\delta\right).
\tag{4.8}
$$

The determinant is independent of the chosen complement. Changing $\delta$ within its twisted
class conjugates the operator and leaves (4.8) unchanged.

**Proposition 4.2.** A twisted semisimple element is strongly $\sigma$-regular if and only if
$D^\sigma(\delta)\ne0$ and $\dim I_\delta=2$.

**Proof.** The kernel of (4.7) is the twisted centralizer Lie algebra. For a regular norm,
Theorem 4.1 makes it two-dimensional, and semisimplicity makes the induced tangent operator on
the quotient invertible. Conversely, invertibility on a quotient with two-dimensional kernel
means that the commutant of $T_\delta^\ell$ has dimension two. A $2\times2$ matrix has
two-dimensional commutant exactly when it is noncentral and cyclic; semisimplicity then forces
two distinct eigenvalues, so the norm is regular semisimple. $\square$

At a local place, $|D^\sigma(\delta)|_v^{1/2}$ is the normalization that removes the first-order
singularity of an orbital integral near the regular boundary. We shall keep ordinary and
normalized orbital integrals distinct; a transfer identity must specify which one it uses.

## 5. Scalar norms and the quadratic inner-form phenomenon

### 5.1 Descent of the matrix algebra

Assume now that

$$
N_\sigma(\delta)=aI,
\qquad a\in F^\times.
\tag{5.1}
$$

The semilinear automorphism

$$
\alpha_\delta:M_2(E)\longrightarrow M_2(E),
\qquad
\alpha_\delta(X)=\delta\sigma(X)\delta^{-1}
\tag{5.2}
$$

satisfies $\alpha_\delta^\ell=\operatorname{Ad}(aI)=1$. It is therefore a Galois descent
datum on the matrix algebra. Its fixed algebra

$$
B_\delta=M_2(E)^{\alpha_\delta}
\tag{5.3}
$$

is a central simple algebra of degree two over $F$, and scalar extension recovers the original
matrix algebra:

$$
B_\delta\otimes_FE\simeq M_2(E).
\tag{5.4}
$$

The descent assertion follows directly from Galois descent for finite-dimensional vector
spaces, applied compatibly to multiplication and the identity. Centrality can also be checked
without invoking a general theorem. The center of $B_\delta$ becomes the center $E$ of
$M_2(E)$ after extension, and its fixed scalars are exactly $F$. Its dimension over $F$ is
four, so it has degree two.

Taking units in (5.3) identifies the centralizer:

$$
I_\delta\simeq B_\delta^\times.
\tag{5.5}
$$

Indeed, the fixed equation $\alpha_\delta(x)=x$ is exactly
$x^{-1}\delta\sigma(x)=\delta$. Thus the scalar norm has converted a twisted centralizer into
an inner form of $\mathrm{GL}_2$.

### 5.2 Why odd prime degree is split

The Brauer class $[B_\delta]$ is killed by extension to $E$, hence by the degree $\ell$ under
restriction followed by corestriction. On the other hand, a central simple algebra of degree
two has Brauer exponent dividing two. If $\ell$ is odd, these two annihilators are coprime, so

$$
[B_\delta]=0.
$$

Therefore $B_\delta\simeq M_2(F)$ and $I_\delta\simeq\mathrm{GL}_2$.

There is an elementary norm check behind the same conclusion. Taking determinants in (5.1)
gives

$$
N_{E/F}(\det\delta)=a^2.
\tag{5.6}
$$

The group $F^\times/N_{E/F}(E^\times)$ is killed by $\ell$: for $c\in F^\times$, its
$\ell$th power is the norm of $c$ viewed in $E^\times$. Equation (5.6) says that the class of
$a$ is also killed by two. For odd $\ell$ it is trivial, so choose $b\in E^\times$ with
$N_{E/F}(b)=a$. Then $c=b^{-1}\delta$ has ordered norm one. Nonabelian Hilbert 90 for
$\mathrm{GL}_2$ supplies $x\in G(E)$ such that

$$
c=x^{-1}\sigma(x).
$$

Consequently

$$
\delta=x^{-1}(bI)\sigma(x),
\tag{5.7}
$$

so the class is twisted conjugate to a scalar. This proves directly that for odd prime degree
there is no hidden scalar-norm inner form.

### 5.3 The quadratic cyclic algebra

Let $\ell=2$. The two annihilators in the preceding argument now coincide, and a genuine
obstruction can survive. For $a\in F^\times$, the cyclic algebra

$$
(E/F,a)=E\oplus Ej,
\qquad
j^2=a,\qquad jz=\sigma(z)j
\tag{5.8}
$$

is a quaternion algebra over $F$. It is split if and only if $a$ is a norm from $E^\times$.

We recall the proof of the last assertion because it is exactly the boundary needed here.
If $a=N(b)$, replace $j$ by $b^{-1}j$; the new generator has square one in the semilinear
sense, and the algebra acts on the two-dimensional $F$-space $E$ by multiplication from $E$
and by the map $z\mapsto b\sigma(z)$. This realizes the algebra as $M_2(F)$. Conversely, if
the algebra is split, it acts on $F^2$. After extension to $E$, the idempotents associated with
the two embeddings of $E$ give a vector $v$ for which $jv=b\sigma(v)$; applying $j$ twice yields
$a=N(b)$. Thus splitness is equivalent to the norm equation.

For the matrix $\delta_a$ of (2.12), the fixed algebra (5.3) is precisely $(E/F,a)$. One sees
this by embedding $E$ as the diagonal algebra

$$
z\longmapsto\begin{pmatrix}z&0\\0&\sigma(z)\end{pmatrix}
$$

and taking $j=\delta_a$; the relations in (5.8) are immediate.

### 5.4 Classification of scalar-norm fibers

**Theorem 5.1 (scalar-norm classification).** Suppose
$N_\sigma(\delta)=aI$.

1. If $\ell$ is odd, $\delta$ is twisted conjugate to $bI$ for any chosen
   $b\in E^\times$ with $N(b)=a$, and $I_\delta\simeq\mathrm{GL}_2$.
2. If $\ell=2$, the fixed algebra is Brauer-equivalent, and in fact isomorphic, to
   $(E/F,a)$. The twisted centralizer is its unit group.
3. For fixed $a$, there is one rational twisted conjugacy class with scalar norm $aI$.
4. Multiplying $\delta$ by $z\in E^\times$ changes $a$ by $N(z)$ and does not change the
   projective obstruction. Hence projective scalar-norm classes are indexed by

   $$
   F^\times/N_{E/F}(E^\times)
   \tag{5.9}
   $$

   in quadratic degree, while the odd-degree scalar obstruction is trivial.

**Proof strategy.** The odd case was proved in Section 5.2. In the quadratic case the descent
datum determines a degree-two central simple algebra split by $E$. Its relative Brauer class
is the cyclic class of $a$. Skolem--Noether and Hilbert 90 then remove all ambiguity left after
the algebra is fixed.

**Proof.** Only assertions 2 and 3 remain. Choose an $E$-algebra isomorphism
$B_\delta\otimes_FE\simeq M_2(E)$. Comparing the descent operator with the standard descent
operator defined by $\delta_a$ gives an $E$-algebra automorphism of $M_2(E)$, hence conjugation
by an element of $G(E)$ by Skolem--Noether. The residual scalar in this comparison has norm
one and is removed by ordinary Hilbert 90. It follows that $\delta$ is twisted conjugate to
$\delta_a$ and that $B_\delta\simeq(E/F,a)$. The same comparison for two elements with norm
$aI$ proves uniqueness. Formula (1.6) proves assertion 4. $\square$

The fixed algebra is split when $a$ is a norm and is a quaternion division algebra when $a$ is
not. There is no third possibility for a degree-two central simple algebra.

It is helpful to see why the determinant detects exactly the parity that appears here but not
the entire class. In quadratic degree, (5.6) is automatic for every $a$, because $a^2=N(a)$
with $a$ viewed in $E^\times$. Thus determinants impose no restriction at all on a scalar
norm. The obstruction resides in the projective semilinear action, or equivalently in the
Brauer class of the descended matrix algebra. This is the sharpest possible counterexample to
the claim that determinant norms control matrix norms.

Stable conjugacy also behaves differently on this stratum. Over an algebraic closure every
degree-two central simple algebra splits, so all scalar-norm descent data with the same scalar
$a$ become conjugate. Over $F$, their rational form is remembered by $(E/F,a)$. For fixed
actual $a$, Theorem 5.1 gives one rational class, but after passing projectively and allowing
$a$ to change by $N(E^\times)$ the stable central point can contain the family (5.9). This is
the precise rational splitting that regular induced tori avoid.

For $\ell=2$, one may verify the centralizer directly from (2.12). Write an element of
$M_2(E)$ as

$$
X=\begin{pmatrix}r&s\\t&u\end{pmatrix}.
$$

The equation $X\delta_a=\delta_a\sigma(X)$ gives

$$
u=\sigma(r),\qquad s=a\sigma(t).
$$

Thus the fixed matrices have the form

$$
\begin{pmatrix}r&a\sigma(t)\\t&\sigma(r)\end{pmatrix},
\qquad r,t\in E.
\tag{5.10}
$$

Their determinant is $N(r)-aN(t)$, the reduced norm form of $(E/F,a)$. It is anisotropic
exactly when $a$ is not a field norm: a nonzero zero of this form would give
$a=N(r/t)$. This calculation simultaneously identifies the algebra, its unit group, and the
split-versus-division criterion.

### 5.5 Local and global consequences

At a local place $v$, the quadratic norm quotient

$$
F_v^\times/N(E_v^\times)
$$

is trivial at a split place and has order two at a nonsplit place. The nontrivial class gives
the unique quaternion division algebra over $F_v$ split by $E_v$. Thus a local scalar stable
norm can have either split or division twisted centralizer.

Globally, $(E/F,a)$ is determined by its local invariants. It is split at $v$ exactly when
$a$ is a local norm from $E_v^\times$. The sum of its local invariants is zero, so the set of
division places is finite and has even cardinality. Conversely, a compatible even set of
nonsplit places determines such a quaternion algebra. These assertions follow from the local
invariant classification of quaternion algebras and the global reciprocity law for their Brauer
classes.

If $(E/F,a)$ is division over $F$, then

$$
B_\delta^\times/F^\times
$$

is anisotropic. The resulting scalar-norm class is elliptic for trace-formula purposes even
though its stable norm $aI$ is central. This is why ``elliptic equals regular elliptic norm''
would be false in quadratic degree. The surviving geometric terms consist of regular elliptic
norms together with these exceptional division-centralizer classes and the split scalar-norm
channel.

## 6. Local twisted orbital integrals

### 6.1 Local cyclic algebras, including split places

Fix a place $v$ of $F$, write $k=F_v$ and $L=E_v$, and put

$$
H_v=\mathrm{GL}_2(L)=\prod_{w\mid v}\mathrm{GL}_2(E_w).
$$

The generator $\sigma$ acts on this product. If $v$ is inert or ramified, $L/k$ is a field
and the preceding definitions apply verbatim. If $v$ splits completely, then
$L\simeq k^\ell$, $\sigma$ cyclically permutes the factors, and a twisted element
$\delta=(\delta_0,\ldots,\delta_{\ell-1})$ has norm conjugate to

$$
\delta_0\delta_1\cdots\delta_{\ell-1}\in\mathrm{GL}_2(k).
\tag{6.1}
$$

Indeed, successive twisted conjugations can make all but one factor equal to the identity.
Thus at a split place every ordinary class is a local twisted norm and its twisted centralizer
is the ordinary centralizer of (6.1). This is an important normalization check: a theory of
local twisted classes must specialize to ordinary conjugacy when the cyclic algebra splits.

For a general local étale algebra, define $N_\sigma$, stable norm, and $I_\delta$ exactly as in
Chapters 2--5. All proofs were algebraic and remain valid. In particular, a regular local
norm fiber is empty or a singleton, and its image is governed by the norm from its local
centralizer torus.

### 6.2 Haar and quotient measures

Choose Haar measure $dh_v$ on $H_v$. At almost every finite place we impose

$$
\operatorname{vol}(\mathrm{GL}_2(\mathcal O_{E_v}),dh_v)=1,
\tag{6.2}
$$

where the notation means the product of the hyperspecial subgroups over $w\mid v$. For a
twisted semisimple $\delta$, choose Haar measure $di_{\delta,v}$ on $I_\delta(k)$. Define the
quotient measure $d\dot h_v$ by Weil integration:

$$
\int_{H_v}\Phi(h)\,dh_v
=\int_{I_\delta(k)}
\int_{I_\delta(k)\backslash H_v}
\Phi(ih)\,d\dot h_v\,di_{\delta,v}.
\tag{6.3}
$$

Equation (6.3), rather than an independent choice, is the definition of orbital measure. If
$di_{\delta,v}$ is multiplied by $c_v>0$, then $d\dot h_v$ is divided by $c_v$.

For regular classes, the identification $I_\delta\simeq T_\gamma$ lets us use multiplicative
measure on the quadratic étale algebra $K_v^\times$. For a scalar-norm class, we use the group
measure on $\mathrm{GL}_2(k)$ or on the appropriate quaternion multiplicative group. At almost
all unramified places these choices are normalized by maximal compact volume one. The finitely
many remaining choices are recorded rather than presumed canonical.

### 6.3 Definition and absolute convergence

Let $f_v$ be locally constant and compactly supported if $v$ is nonarchimedean, and smooth
Schwartz if $v$ is archimedean. For a twisted semisimple $\delta$, define

$$
O_{\delta,v}^\sigma(f_v)
=\int_{I_\delta(k)\backslash H_v}
f_v(h^{-1}\delta\sigma(h))\,d\dot h_v.
\tag{6.4}
$$

**Proposition 6.1.** The integral (6.4) is absolutely convergent.

**Proof strategy.** The twisted orbit is closed and its stabilizer is reductive. The orbit map
identifies the homogeneous space with that closed orbit. Compact support gives convergence at
nonarchimedean places; at infinity, Cartan coordinates turn the orbit map into exponential
functions of the noncentral Cartan variables, and Schwartz decay dominates the polynomial
Jacobian.

**Proof.** Twisted semisimplicity of $\delta$ means semisimplicity of the element
$\delta\rtimes\sigma$ in the semidirect product. Its algebraic orbit is closed. Over a local
field the map

$$
I_\delta(k)\backslash H_v\longrightarrow H_v,
\qquad h\longmapsto h^{-1}\delta\sigma(h)
\tag{6.5}
$$

is a homeomorphism onto that orbit; this follows by applying the local closed-orbit criterion
in matrix coordinates and using that the stabilizer is closed. At a nonarchimedean place, the
inverse image in the quotient of a compact subset of the orbit is compact, so a compactly
supported integrand has compact support.

At an archimedean place, choose maximal compact subgroups and write $h=iak$ modulo $I_\delta$.
On every cone of the Cartan space complementary to $I_\delta$, at least one matrix coefficient
of $h^{-1}\delta\sigma(h)$ grows like $e^{c\|\log a\|}$ for some $c>0$; otherwise a nonzero
Cartan direction would centralize the semisimple element and belong to $I_\delta$. Haar measure
has at most exponential density $e^{C\|\log a\|}$. Schwartz decay of arbitrarily high order in
the matrix norm therefore makes the integral finite after choosing the decay order greater than
$C/c$. $\square$

Nonsemisimple classes are excluded from Proposition 6.1 because their individual orbit
integrals are not the geometric objects used globally. They are combined with the parabolic
channel before the truncation is removed.

### 6.4 Invariance, scaling, and local constancy

If $\delta'=g^{-1}\delta\sigma(g)$, right translation $h\mapsto gh$ and the conjugate
identification of centralizers give

$$
O_{\delta',v}^\sigma(f_v)=O_{\delta,v}^\sigma(f_v).
\tag{6.6}
$$

Thus (6.4) is a distribution on twisted classes. It is linear and continuous on the local test
space: on a fixed compact support, (6.5) reduces it to integration over a compact subset; at
infinity the proof of Proposition 6.1 bounds it by finitely many Schwartz seminorms.

At a nonarchimedean place, $O_{\delta,v}^\sigma(f_v)$ is locally constant as a function of a
strongly regular class away from the discriminant locus. To prove this, choose a transversal
to the orbit at $\delta$. The tangent map (4.7) is invertible on the quotient because
$D^\sigma(\delta)\ne0$. The nonarchimedean inverse function theorem gives an orbit-times-slice
chart. Local constancy of $f_v$ and compactness of the contributing quotient then make the
integral constant on a sufficiently small slice.

Rescaling $di_{\delta,v}$ by $c_v$ rescales the orbital integral by $c_v^{-1}$. This is not a
defect: the global coefficient will rescale by $c_v$.

### 6.5 Normalized and stable distributions

For a strongly regular class define

$$
I_{\delta,v}^\sigma(f_v)
=|D^\sigma(\delta)|_v^{1/2}O_{\delta,v}^\sigma(f_v).
\tag{6.7}
$$

The factor in (6.7) is omitted for scalar-norm classes, where the regular discriminant
vanishes and the correct normalization comes from their inner-form centralizer.

If $\gamma\in G(k)$ is regular semisimple, define the local stable twisted distribution

$$
SO_{\gamma,v}^\sigma(f_v)
=\sum_{\substack{[\delta]_\sigma\\N^{\rm st}(\delta)=\gamma}}
I_{\delta,v}^\sigma(f_v).
\tag{6.8}
$$

The regular fiber theorem makes the sum either empty or a single term. We nevertheless retain
the notation because it states the correct comparison variable: matching is indexed by a stable
ordinary norm class, not by a chosen matrix representative. The sum notation also continues
to make sense for groups where stable fibers split.

The distribution in (6.8) is zero unless

$$
\gamma\in N_{L/k}^{T_\gamma}(T_\gamma(L)).
\tag{6.9}
$$

At a split place this condition is automatic and (6.8) becomes the corresponding ordinary
normalized orbital integral after the reduction leading to (6.1).

The discriminant normalization can be recovered from a slice calculation. Choose an
$I_\delta$-stable complement $\mathfrak q$ to $\mathfrak i_\delta$. Near the identity coset,
the map

$$
X\longmapsto\exp(-X)\delta\sigma(\exp X)
$$

has derivative $\operatorname{Ad}(\delta)\sigma-1$ on $\mathfrak q$. Change of variables
therefore contributes $|D^\sigma(\delta)|_v^{-1}$ to the full orbit density. Passing from
volume density to the conventional half-density used in invariant harmonic analysis explains
the square root in (6.7). This calculation also shows why normalized orbital integrals have
better behavior near a regular singular limit, although they need not extend continuously
without additional germ terms.

At a nonarchimedean place the local-constancy argument can be made uniform on a compact regular
set. The inverse-function neighborhoods may be chosen with a common radius once
$|D^\sigma(\delta)|_v$ is bounded below. Consequently a compactly supported $f_v$ produces a
locally constant function of the stable coefficients $(s_\delta,d_\delta)$ on every region
where the norm condition is fixed and the discriminant has fixed valuation. Jumps can occur
when the torus changes from split to field, when the norm image changes, or when the
discriminant approaches zero. These are genuine geometric walls, not failures of smoothness
of $f_v$.

## 7. Adelic measures and coefficients

### 7.1 The determinant-one realization

Define

$$
\nu_H(h)=|\det h|_{\mathbf A_E},
\qquad H(\mathbf A_F)^1=\ker\nu_H.
$$

For every reductive twisted centralizer used in the surviving expansion, restrict the same
modulus:

$$
I_\delta(\mathbf A_F)^1
=I_\delta(\mathbf A_F)\cap H(\mathbf A_F)^1.
\tag{7.1}
$$

The map $\nu_H$ on $I_\delta(\mathbf A_F)$ is onto $\mathbf R_{>0}$. For a regular torus this
follows by varying one archimedean component of $K^\times$; for $\mathrm{GL}_2$ or a quaternion
multiplicative group it follows by varying an archimedean reduced norm. Consequently the
natural map

$$
I_\delta(\mathbf A_F)^1\backslash H(\mathbf A_F)^1
\longrightarrow
I_\delta(\mathbf A_F)\backslash H(\mathbf A_F)
\tag{7.2}
$$

is an isomorphism of measured homogeneous spaces once the modulus measures are chosen
compatibly. Surjectivity is obtained by multiplying $h$ by an element of $I_\delta$ with the
same modulus; injectivity follows because any element relating two determinant-one
representatives has modulus one.

This observation gives both finite-volume coefficients and factorizable orbital integrals. It
is the main advantage of the determinant-one realization.

### 7.2 Tamagawa-compatible quotient measures

Choose restricted-product measures

$$
dh=\prod_vdh_v,
\qquad di_\delta=\prod_vdi_{\delta,v},
\tag{7.3}
$$

with maximal compact volume one at almost every finite place. The product quotient measure on
$I_\delta(\mathbf A_F)\backslash H(\mathbf A_F)$ is defined by the adelic version of (6.3).
Choose Lebesgue measure $dt/t$ on the common modulus group $\mathbf R_{>0}$; disintegration then
defines measures on the two determinant-one groups and makes (7.2) measure preserving.

On the rational quotients we use the measures induced by these choices. Rational points have
modulus one by the product formula, so the coefficient

$$
a(\delta)=
\operatorname{vol}\bigl(
I_\delta(F)\backslash I_\delta(\mathbf A_F)^1
\bigr)
\tag{7.4}
$$

is defined without another quotient by $\mathbf R_{>0}$.

The adjective ``Tamagawa-compatible'' means precisely (7.3), quotient integration, and the
common modulus disintegration. It does not assert that every displayed volume has been
normalized to a particular conventional integer. The geometric term is invariant under the
remaining choices, as Section 7.5 proves.

### 7.3 Volumes of twisted centralizers

The coefficient (7.4) is finite for every twisted semisimple class used below.

**Proposition 7.1.** If $I_\delta$ is an elliptic regular centralizer torus,
$\mathrm{GL}_2$, or the multiplicative group of a quaternion algebra, then
$I_\delta(F)\backslash I_\delta(\mathbf A_F)^1$ has finite volume. It is compact modulo the
norm-one scalar center when $I_\delta/Z$ is anisotropic.

**Proof.** For an elliptic torus
$I_\delta=\operatorname{Res}_{K/F}\mathbf G_m$, the algebra $K$ is a quadratic field and the
quotient is the norm-one idele-class quotient of $K$. It is compact by the idele-class
compactness theorem.

For $\mathrm{GL}_2$, finite volume is the reduction theorem for
$\mathrm{GL}_2(F)\backslash\mathrm{GL}_2(\mathbf A_F)^1$. For a quaternion algebra $B$, the
same reduction argument applies to $B^\times$ through reduced norm. If $B$ is division,
$B^\times/F^\times$ is anisotropic, so the quotient modulo the compact norm-one center is
compact. $\square$

The split regular torus is deliberately absent. If $K=F\times F$, the condition on the product
of the two idele moduli leaves their ratio in $\mathbf R_{>0}$, and the resulting $dt/t$
direction has infinite volume. Thus a split class has no coefficient of the form (7.4).
Those classes must be combined in the truncated parabolic distribution, exactly as Chapter 9
does. The scalar split channel is different: its centralizer is $\mathrm{GL}_2$, whose
determinant-one arithmetic quotient has finite volume by reduction theory.

### 7.4 Factorization of adelic orbital integrals

For a restricted tensor $f=\otimes_vf_v$ and a twisted semisimple rational element define

$$
O_\delta^\sigma(f)=
\int_{I_\delta(\mathbf A_F)\backslash H(\mathbf A_F)}
f(h^{-1}\delta\sigma(h))\,d\dot h.
\tag{7.5}
$$

By (7.2) the same integral can be taken over determinant-one quotients. Absolute convergence
is not inferred from unrelated local convergence statements. For a rational twisted
semisimple $\delta$, all but finitely many local data extend to smooth integral models,
$f_v$ is the hyperspecial unit there, and the local quotient has one integral orbit of volume
one. Thus the absolute adelic integral is a finite product of the remaining local absolute
integrals. Proposition 6.1 handles those factors, including the archimedean ones.

**Proposition 7.2 (factorization).** With the restricted-product measures of Section 7.2,

$$
O_\delta^\sigma(f)=\prod_vO_{\delta,v}^\sigma(f_v).
\tag{7.6}
$$

At almost every place the factor equals one when $f_v$ is the hyperspecial unit and $\delta$ is
integral with unramified regular reduction, after the compatible unramified centralizer measure
is used.

**Proof.** Quotient integration identifies the adelic homogeneous-space measure with the
restricted product of the local quotient measures. For a nonnegative pure tensor, Tonelli's
theorem gives the product. Apply this to the absolute value to obtain absolute convergence;
then Fubini gives (7.6). At almost every place, smooth integral descent identifies the orbit
of an unramified regular element with a hyperspecial quotient whose integral model has volume
one, so the unit orbital integral is one. $\square$

The final unramified assertion is a measure normalization, not the cyclic fundamental lemma.
It concerns the twisted orbit of a fixed integral element against the local unit. Comparing it
with an ordinary orbital integral of a transferred function is a further theorem.

### 7.5 Independence under rescaling

Suppose $di_{\delta,v}$ is replaced by $c_vdi_{\delta,v}$ at finitely many places. Then

$$
a(\delta)\longmapsto
\left(\prod_vc_v\right)a(\delta),
\qquad
O_\delta^\sigma(f)\longmapsto
\left(\prod_vc_v^{-1}\right)O_\delta^\sigma(f).
$$

Therefore

$$
a(\delta)O_\delta^\sigma(f)
\tag{7.7}
$$

is unchanged. This product, not either factor separately, is the canonical geometric term.
The same calculation applies when a torus is identified with a quadratic field by another
$F$-basis: the induced measure change cancels between volume and orbit.

## 8. Test functions and the twisted automorphic kernel

### 8.1 The admissible Schwartz class

At a nonarchimedean place, let $f_v\in C_c^\infty(H_v)$. At an archimedean place, require
$f_v$ to be smooth, finite under the left and right maximal compact actions, and rapidly
decreasing with every invariant derivative: for every differential operator $D$ and $A>0$,

$$
|Df_v(h)|\le C_{D,A}\|h\|_v^{-A}
\tag{8.1}
$$

for a proper submultiplicative matrix height. An **admissible global test function** is a finite
sum of restricted tensors $f=\otimes_vf_v$ with hyperspecial units at almost every finite
place, restricted to $H(\mathbf A_F)^1$.

The finite sum condition is harmless analytically and indispensable algebraically: convolution,
adjoints, and prescribed local projectors naturally produce such sums. All statements below
are first proved for a tensor and then extended by linearity and the triangle inequality.

### 8.2 Strong cuspidality at one place

Let $B=TN$ be the standard Borel of $\mathrm{GL}_2$ over the local étale algebra $E_v$. A local
factor $f_v$ is **strongly cuspidal** if

$$
\int_{N(E_v)}f_v(x^{-1}tny)\,dn=0
\tag{8.2}
$$

for every $x,y\in H_v$ and $t\in T(E_v)$. The integral must be absolutely convergent. We
require every tensor summand to have one strongly cuspidal factor, at a common place $v_0$.

Both translations in (8.2) are necessary. Twisted unfolding produces independently varying
elements on the left and right of the unipotent variable. Vanishing of the unshifted constant
term, or merely vanishing of traces on principal series, would not imply the pointwise
cancellation needed in Chapter 9.

The condition is nonempty. At a nonarchimedean field place, a compactly induced
supercuspidal representation has matrix coefficients compactly supported modulo the center,
and vanishing of its Jacquet module makes every two-sided integral (8.2) zero. Multiplying in
the central direction by a compact cutoff gives a compactly supported strongly cuspidal
function. If $E_v$ is a product, take such a factor on one component and arbitrary compact
factors on the others; the product unipotent integral still has a zero factor. At a real
field place, a compact-finite discrete-series pseudo-coefficient with a rapidly decreasing
central factor gives the archimedean analogue. Thus every number-field extension admits
admissible tensors after choosing a suitable finite place, without imposing a real-place
hypothesis.

For a tensor, the global two-sided parabolic transform factors into local transforms. Its
$v_0$-factor vanishes, so

$$
\int_{N(\mathbf A_E)}f(x^{-1}tny)\,dn=0
\tag{8.3}
$$

for all adelic $x,y,t$ for which the expression is formed. This single local zero is the
mechanism that removes the global nonelliptic channel.

### 8.3 The twisted kernel

For an admissible $f$, define

$$
K_f^\sigma(x,y)
=\sum_{\delta\in G(E)}
f(x^{-1}\delta\sigma(y)),
\qquad x,y\in H(\mathbf A_F)^1.
\tag{8.4}
$$

The diagonal is invariant under $G(E)$. Indeed, replacing $x$ by $\gamma x$ changes the index
$\delta$ to $\gamma^{-1}\delta\sigma(\gamma)$. Hence
$K_f^\sigma(x,x)$ descends to $[H]^1$.

The two-variable kernel itself is the ordinary automorphic kernel with its second variable
composed with $\sigma$. It is the integral kernel of right convolution followed by the unitary
field automorphism on automorphic functions, but no spectral consequence of that observation is
used in this book.

### 8.4 Convergence and smoothness before taking the diagonal

**Proposition 8.1.** The series (8.4), and every series obtained by invariant differentiation in
$x$ and $y$, converges absolutely and locally uniformly. It defines a smooth automorphic
kernel of moderate growth.

**Proof strategy.** Finite-adelic compact support confines rational matrices to a fixed
fractional lattice. On a compact set of $x,y$, archimedean Schwartz decay bounds the summand
by an arbitrarily high inverse power of the matrix height. Lattice points of bounded height
grow only polynomially.

**Proof.** Choose a finite set $S$ containing all archimedean and ramified places and every
place where $f_v$ is not the hyperspecial unit. For $x,y$ in a fixed compact set, the condition
that the finite part of $x^{-1}\delta\sigma(y)$ meet the support of $f_f$ puts the four entries
of $\delta$ and $\det(\delta)^{-1}$ in fixed fractional ideals depending only on $S$. The
number of such matrices of archimedean height at most $R$ is $O(R^C)$ for some $C$, by counting
points in a rank-$4[F:\mathbf Q]$ lattice and then imposing the determinant condition.

For every $A$, (8.1) bounds the corresponding summand by $O(R^{-A})$. Taking $A>C+2$ and
summing over dyadic height shells proves absolute local uniform convergence. Differentiating
only replaces $f$ by one of its invariant derivatives, which satisfies the same estimate.
Moderate growth follows by the same argument after allowing $x,y$ to vary in a Siegel set and
using the submultiplicativity of the height. $\square$

### 8.5 The diagonal geometric distribution

Strong cuspidality makes the kernel cuspidal in each automorphic variable. For example, its
constant term in $x$ is obtained by integrating over
$N(E)\backslash N(\mathbf A_E)$, unfolding the rational sum along $B(E)\backslash G(E)$, and
then applying (8.3). Absolute local uniform convergence from Proposition 8.1 justifies the
interchange. The same argument in the second variable uses the freedom in both $x$ and $y$ in
(8.2).

The usual rapid-decay theorem is stated for finite automorphic vectors. A kernel obtained from
an arbitrary Schwartz function need not be finite under the archimedean infinitesimal center,
so applying that theorem to the whole two-variable family without comment would leave a
hypothesis gap. Its rank-one Fourier proof does, however, apply uniformly to this family.

**Proposition 8.2 (two-variable rapid decay).** For every $A>0$ and every pair of
right-invariant differential operators $D_1,D_2$, there is a continuous Schwartz seminorm
$q_{A,D_1,D_2}$ such that, on products of Siegel sets,

$$
|D_1^xD_2^yK_f^\sigma(x,y)|
\le q_{A,D_1,D_2}(f)
\operatorname{ht}(x)^{-A}\operatorname{ht}(y)^{-A}
\tag{8.5}
$$

after the determinant direction has been removed.

**Proof.** Fix the finite level and the finitely many cusp charts meeting the finite support of
$f$. On a unipotent cross-section in the first variable, the calculation preceding the
proposition says that the zero Fourier coefficient is zero. The same is true in the second
variable. The restriction of the kernel to a product of two cross-sections is therefore a
double Fourier series indexed by nonzero elements of two fixed fractional lattices.

At height $H_x$, an invariant unipotent derivative multiplies each nonzero first Fourier mode
by at least $cH_x^{1/[E:\mathbf Q]}$ in one archimedean direction; the analogous assertion
holds with $H_y$ in the second variable. Integrating by parts $r$ times in each set of
unipotent coordinates and applying Sobolev embedding on the two fixed compact tori gives

$$
|D_1^xD_2^yK_f^\sigma(x,y)|
\le C_rH_x^{-r/[E:\mathbf Q]}H_y^{-r/[E:\mathbf Q]}
\max_{|I|,|J|\le r+s}|X^IY^JK_f^\sigma(x',y')|,
\tag{8.5a}
$$

where $s$ is a fixed Sobolev loss and $x',y'$ range over the corresponding compact
cross-sections. Proposition 8.1, applied to the finitely many derivatives in (8.5a), bounds the
last maximum by a Schwartz seminorm times a polynomial in $H_xH_y$. The polynomial exponent
can be chosen independently of $r$: differentiating the rational-point series replaces $f$ by
an invariant derivative, and every such derivative has arbitrary Schwartz decay. Choose $r$
so that the two Fourier gains dominate that common polynomial and the prescribed exponent $A$.
The compact parts of the finitely many Siegel sets are absorbed into the seminorm. $\square$

Since $[H]^1$ has finite-volume cusp regions of polynomial density, (8.5) makes the diagonal
absolutely integrable. We may therefore define

$$
J_{\mathrm{geom}}^\sigma(f)
=\int_{[H]^1}K_f^\sigma(x,x)\,dx.
\tag{8.6}
$$

This is already an honest continuous distribution on the strongly cuspidal test class. What
remains is to express it as a convergent sum of twisted orbital distributions. Directly
interchanging the integral and rational sum in (8.6) is not justified; the next three chapters
provide the safe argument.

Here is the constant-term calculation in more detail. For fixed $y$, begin with

$$
\int_{N(E)\backslash N(\mathbf A_E)}
\sum_{\delta\in G(E)}
f(x^{-1}n^{-1}\delta\sigma(y))\,dn.
\tag{8.7}
$$

Group $G(E)$ by the rational line carried to the standard line, that is, by
$B(E)\backslash G(E)$. Within one coset, write the Borel factor as $tu$ with
$t\in T(E)$ and $u\in N(E)$. The sum over $u$ and the quotient integral unfold by (9.7) to

$$
\int_{N(\mathbf A_E)}
f(x_1^{-1}tnx_2)\,dn
$$

for translated $x_1,x_2$. This is zero by (8.3). Truncate (8.7) first to justify the grouping;
Proposition 8.1 and Schwartz decay give a dominating function as the truncation is removed.
Thus the constant term vanishes pointwise, not merely in an $L^2$ sense.

For the second variable, apply the same calculation to

$$
f^{\sigma,*}(h)=\overline{f(\sigma(h)^{-1})}.
$$

This function has the same Schwartz bounds, and strong cuspidality follows from (8.2) after
inverting the unipotent variable and conjugating it by the torus. The identity

$$
K_{f^{\sigma,*}}^\sigma(y,x)=\overline{K_f^\sigma(x,y)}
$$

then transfers the first-variable proof to the second. Applying the first-variable Sobolev
estimate to the finitely many derivatives needed for a second-variable Sobolev embedding gives
the simultaneous estimate (8.5). This explains why separate one-variable decay estimates can
be multiplied with a uniform constant.

## 9. Twisted parabolic geometry

### 9.1 Semilinear invariant lines

A noncentral ordinary matrix is nonelliptic exactly when it preserves a rational line. The
twisted replacement is a line $L\subset E^2$ satisfying

$$
T_\delta(L)=L.
\tag{9.1}
$$

Because $T_\delta$ is semilinear, (9.1) is meaningful for an $E$-line. Iterating shows that
$L$ is an eigenline of $N_\sigma(\delta)$. Conversely, if the norm has a simple eigenvalue in
$F$, its $E$-eigenline is preserved by $T_\delta$, since $T_\delta$ commutes with its $\ell$th
power. For a noncentral Jordan norm, the unique generalized eigenspace line is likewise
preserved.

**Proposition 9.1.** Let $N_\sigma(\delta)$ be noncentral.

1. If the stable norm is split regular, $T_\delta$ preserves exactly two $E$-lines.
2. If the stable norm is nonsemisimple, $T_\delta$ preserves exactly one $E$-line.
3. If the stable norm is elliptic, $T_\delta$ preserves no $E$-line whose norm descent is
   defined over $F$; equivalently, $\delta$ is not twisted conjugate into an $F$-rational
   parabolic of $H$ fixed by $\theta$.

**Proof.** In the first two cases the invariant lines are the eigenlines of the norm, as just
explained. There are respectively two and one. In the elliptic case, an invariant line would
give a one-dimensional semilinear subobject. Its $\ell$th power would give an $F$-rational
eigenvalue and hence a root of the norm polynomial in $F$, contradicting irreducibility. The
parabolic reformulation follows because parabolics of $\mathrm{GL}_2$ are stabilizers of lines.
$\square$

Scalar norms are excluded from this incidence count. A split scalar representative $bI$ has
many semilinear invariant lines, just as an ordinary scalar matrix fixes every rational line,
but its contribution is a separate scalar channel. A division-centralizer scalar norm has no
rational parabolic descent and is elliptic. Mixing scalar classes into the finite incidence
multiplicity would therefore destroy the count.

### 9.2 Incidence multiplicities

Let $\mathscr L_\delta$ be the set of semilinear invariant lines for a noncentral nonelliptic
$\delta$, and put

$$
e(\delta)=|\mathscr L_\delta|.
$$

Proposition 9.1 gives

$$
e(\delta)=
\begin{cases}
2,&\text{split regular norm},\\
1,&\text{nonsemisimple norm}.
\end{cases}
\tag{9.2}
$$

An invariant line can be moved to the standard line by $G(E)$. In that basis,
$\delta$ belongs to $B(E)$ in the twisted sense: $T_\delta$ preserves the standard flag. For
every finitely supported function $\Phi$ on the noncentral nonelliptic rational elements,

$$
\sum_\delta\Phi(\delta)
=\sum_{L}
\sum_{\substack{\delta:T_\delta L=L\\
\text{noncentral nonelliptic}}}
e(\delta)^{-1}\Phi(\delta).
\tag{9.3}
$$

The outer sum is over the rational semilinear flags, equivalently the relevant
$B(E)\backslash G(E)$ incidence set. Each element is counted once for each invariant line and
then divided by (9.2). Formula (9.3) will be used only after truncation, where the support is
finite. It is not asserted as an unconditional rearrangement of the diagonal kernel.

### 9.3 Truncation in the unique cusp

Reduction theory for $\mathrm{GL}_2/E$ gives a height function $H_B$ on $[H]^1$ associated with
the standard Borel. Normalize it so that in Iwasawa coordinates

$$
x=nmak,
\qquad
H_B(x)=\log|a_1/a_2|_{\mathbf A_E}
$$

up to a bounded function on the chosen Siegel set. For $T>0$, choose a smooth cutoff
$\Lambda_T(x)$ which is one on $H_B(x)\le T$, zero on $H_B(x)\ge T+1$, and has uniformly
bounded derivatives after translation to the height coordinate.

The truncated quotient has compact image modulo the compact norm-one center. Hence

$$
J_T^\sigma(f)=
\int_{[H]^1}\Lambda_T(x)K_f^\sigma(x,x)\,dx
\tag{9.4}
$$

permits termwise integration and every regrouping made below: on the compact core, finite
adelic support and discreteness of $G(E)$ leave only finitely many rational matrices meeting a
fixed support enlargement.

Rapid decay (8.5) gives

$$
\lim_{T\to\infty}J_T^\sigma(f)=J_{\mathrm{geom}}^\sigma(f).
\tag{9.5}
$$

Indeed, the complement of the truncation has polynomial volume density in $e^T$, while the
kernel has arbitrarily high inverse powers of the same height. Dominated convergence then
proves (9.5).

### 9.4 Unfolding the parabolic channel

Apply the finite incidence identity (9.3) inside (9.4). Move each invariant line to the
standard line and unfold the sum over $B(E)\backslash G(E)$. Write an upper triangular
representative as $tn(u)$, with $t\in T(E)$ and $u\in E$. The rational sum over $u$ and the
integration over $N(E)\backslash N(\mathbf A_E)$ combine into an integral over
$N(\mathbf A_E)$. The noncentral nonelliptic part becomes a finite sum of expressions of the
shape

$$
\int \Lambda_T(nx)
\left(
\int_{N(\mathbf A_E)}
f(x_1^{-1}tnx_2)\,dn
\right)d\mu,
\tag{9.6}
$$

where $x_1$ and $x_2$ are adelic translates depending on the remaining variables and on
$\sigma$. Their exact form is immaterial to cancellation but explains why strong cuspidality
was required with arbitrary translations on both sides.

For clarity, the unfolding uses three justified operations. The truncated rational sum is
finite. The quotient integral over the compact core is finite. The unipotent rational sum is
converted to an adelic integral by the ordinary identity

$$
\sum_{u\in E}\int_{E\backslash\mathbf A_E}\phi(u+n)\,dn
=\int_{\mathbf A_E}\phi(n)\,dn,
\tag{9.7}
$$

valid for an absolutely integrable $\phi$. Compact finite support and archimedean Schwartz
decay supply that integrability.

### 9.5 Cancellation of split and nonsemisimple terms

If $\Lambda_T$ were constant along the unipotent unfolding, the inner integral in (9.6) would
vanish immediately by (8.3). Truncation introduces a boundary discrepancy because
$\Lambda_T(nx)$ need not equal $\Lambda_T(x)$. We must show that this discrepancy tends to
zero.

In a Siegel set, conjugation by $a=\operatorname{diag}(a_1,a_2)$ sends $n(u)$ to
$n((a_2/a_1)u)$. The cutoff changes only when $H_B(x)$ lies in a bounded strip around $T$.
On that strip the unipotent coordinate that can change the cutoff has size at least a fixed
multiple of $e^T$. Repeated integration by parts at archimedean places, together with compact
support in the nonarchimedean unipotent coordinates, gives for every $A$

$$
|\text{boundary discrepancy}|\le C_Ae^{-AT}.
\tag{9.8}
$$

The remaining diagonal and compact variables have at most polynomial density $e^{CT}$.
Choosing $A>C$ makes their integral tend to zero. This is the same rank-one mechanism as rapid
decay of a cusp form: the zero constant term removes the leading cusp asymptotic, and every
remaining Fourier mode decays faster than the boundary expands.

We have proved the parabolic cancellation theorem.

**Theorem 9.2.** In the limit $T\to\infty$, the combined contribution of all noncentral classes
with split regular or nonsemisimple stable norm is zero. The assertion concerns their combined
truncated distribution; it does not assert that every individual nonelliptic orbital integral
vanishes or converges.

This distinction prevents a common false shortcut. Strong cuspidality kills a parabolic
distribution after incidence unfolding. It need not make $O_\delta^\sigma(f)$ zero for a
single split class under an independently chosen, noncompact orbital regularization.

The boundary estimate (9.8) can be made independent of the particular matrix representative.
On the truncated support, finite places restrict $t$ and the unipotent denominator to finitely
many lattice cosets. At infinity, differentiation in the compact quotient
$E\backslash\mathbf A_E$ multiplies a nonzero Fourier mode by its archimedean frequency. After
diagonal conjugation this frequency is multiplied by $|a_1/a_2|$, which is comparable to
$e^T$ on the boundary strip. Integrating by parts $r$ times contributes $e^{-rT}$, while all
derivatives of the cutoff and of $f$ are uniformly bounded by fixed Schwartz seminorms. The
number of finite lattice modes of size at most $e^{cT}$ is $O(e^{c'T})$. Choosing
$r>c'+C$ proves (9.8) after integration over every remaining variable. The decisive gain is
therefore quantitative and can be made arbitrarily large.

The factor $e(\delta)^{-1}$ creates no residual coefficient. A split regular element enters
once through each of its two invariant lines, while a Jordan element enters once. After the
incidence sum is unfolded, these multiplicities exactly restore the original rational sum.
Strong cuspidality then annihilates the whole Borel expression. There is no separate factor of
two on the geometric side.

## 10. Elliptic and scalar-norm unfolding

### 10.1 Closed twisted orbits

The surviving rational elements fall into three families:

1. strongly regular classes with elliptic stable norm;
2. scalar-norm classes with split centralizer;
3. when $\ell=2$, scalar-norm classes whose centralizer is a quaternion division group.

All three are twisted semisimple, so their orbits are closed. In the first and third families,
$I_\delta/Z$ is anisotropic. The second family has $I_\delta\simeq\mathrm{GL}_2$ and is kept as
a distinguished scalar channel, just as the central class is separated in the ordinary trace
formula.

Let $\mathcal C_{\mathrm{reg,ell}}$ denote the rational twisted classes of the first family,
$\mathcal C_{\mathrm{sc,sp}}$ those of the second, and, only for $\ell=2$,
$\mathcal C_{\mathrm{sc,div}}$ those of the third. The classification theorems show that these
sets are disjoint and exhaust the semisimple terms not removed by Theorem 9.2.

### 10.2 Orbit-by-orbit unfolding

Fix a surviving class $[\delta]_\sigma$. Its rational orbit is

$$
I_\delta(F)\backslash H(F).
$$

On the truncated quotient, unfold this orbit before removing the cutoff. Quotient integration
gives

$$
\int_{I_\delta(F)\backslash H(\mathbf A_F)^1}
\Lambda_T(h)f(h^{-1}\delta\sigma(h))\,dh.
\tag{10.1}
$$

Insert the intermediate quotient by $I_\delta(\mathbf A_F)^1$. When
$I_\delta/Z$ is anisotropic, its rational adelic quotient is compact, so dominated convergence
removes $\Lambda_T$ and yields

$$
a(\delta)O_\delta^\sigma(f).
\tag{10.2}
$$

For the split scalar channel the centralizer quotient is not compact, but the integrand is a
relative semisimple orbital function. Strong cuspidality makes it rapidly decreasing in the
one remaining parabolic direction by the same constant-term argument used for the full kernel.
Thus the quotient integral is absolutely convergent and the same dominated-convergence step
produces (10.2).

No sum over classes has yet been interchanged with the limit. Equation (10.2) is an
orbit-by-orbit statement. Absolute summability, proved in Chapter 11, will justify the final
global interchange.

### 10.3 The split scalar-norm distribution

A split scalar-norm class is twisted conjugate to $bI$ with $b\in E^\times$. Two such scalars
are twisted conjugate if and only if they have the same field norm. One implication follows
from invariance of the ordered norm. Conversely, if $N(b'/b)=1$, Hilbert 90 gives
$b'/b=x^{-1}\sigma(x)$ for a scalar $x$, which is the required twisted conjugation.

Hence these classes are indexed by

$$
a\in N_{E/F}(E^\times).
\tag{10.3}
$$

Choose $b_a$ with $N(b_a)=a$ and define

$$
J_{\mathrm{sc,sp}}^\sigma(f)
=\sum_{a\in N(E^\times)}
a(b_aI)O_{b_aI}^\sigma(f).
\tag{10.4}
$$

The summand is independent of the choice of $b_a$ by twisted invariance. The centralizer is
$G/F$, so its volume coefficient is independent of $a$ with our transported measures. The
orbital integral is not generally $f(b_aI)$: its orbit is the relative space

$$
G(\mathbf A_F)^1\backslash G(\mathbf A_E)^1,
$$

through $h\mapsto h^{-1}b_a\sigma(h)$. It reduces to an ordinary central value only when the
extension is split trivially.

### 10.4 Quadratic exceptional terms

Suppose $\ell=2$. For $a\notin N(E^\times)$, let $\delta_a$ be (2.12). Its centralizer is

$$
I_{\delta_a}\simeq(E/F,a)^\times,
$$

and this quaternion algebra is division. Define

$$
J_{\mathrm{sc,div}}^\sigma(f)
=\sum_{a\in F^\times\setminus N(E^\times)}
a(\delta_a)O_{\delta_a}^\sigma(f).
\tag{10.5}
$$

Although (10.5) is written with elements $a$, its terms group naturally by the actual scalar
norm, not merely by the projective class. Multiplication by a norm changes the rational matrix
$aI$ and hence moves to another term in the determinant-one realization. In the central-
character realization these terms combine into projective obstruction classes; see Section
12.3.

The quotient of $I_{\delta_a}$ by its center is anisotropic, so each unfolding is elliptic and
needs no parabolic regularization. This is the precise sense in which a central stable norm can
produce a noncentral elliptic geometric term.

### 10.5 The provisional geometric expansion

For regular elliptic classes set

$$
J_{\mathrm{reg,ell}}^\sigma(f)
=\sum_{[\delta]_\sigma\in\mathcal C_{\mathrm{reg,ell}}}
a(\delta)O_\delta^\sigma(f).
\tag{10.6}
$$

The norm-fiber theorem permits an equivalent indexing by regular elliptic
$G(F)$-conjugacy classes $[\gamma]$ satisfying

$$
\gamma\in N_{E/F}^{T_\gamma}(T_\gamma(E)).
\tag{10.7}
$$

For each such $\gamma$, there is exactly one $[\delta]_\sigma$.

The orbitwise truncated calculation and Theorem 9.2 suggest

$$
J_{\mathrm{geom}}^\sigma(f)
=J_{\mathrm{sc,sp}}^\sigma(f)
+J_{\mathrm{reg,ell}}^\sigma(f)
+\mathbf1_{\ell=2}J_{\mathrm{sc,div}}^\sigma(f).
\tag{10.8}
$$

At this stage (10.8) is provisional: each summand is defined, and each individual orbit has
been unfolded, but the infinite series and the passage from truncated sums to their union still
require uniform estimates.

The classification of possible limiting terms may be summarized as follows.

| norm type                   | projective centralizer          | treatment                          | survives?             |
| --------------------------- | ------------------------------- | ---------------------------------- | --------------------- |
| split regular               | split torus                     | invariant-line parabolic unfolding | no                    |
| noncentral repeated         | unipotent extension of a torus  | invariant-line parabolic unfolding | no                    |
| regular elliptic            | anisotropic torus               | closed-orbit unfolding             | yes                   |
| scalar, split descent       | split $\mathrm{PGL}_2$          | relative scalar channel            | yes                   |
| scalar, quaternion division | anisotropic $\mathrm{PGL}_1(B)$ | closed-orbit unfolding             | yes, only if $\ell=2$ |

There is no omitted regular unipotent type: an invertible $2\times2$ matrix with repeated root
is either scalar or one Jordan block. There is no omitted scalar inner form of higher degree:
the descended algebra has degree two. Finally, prime degree rules out intermediate cyclic
strata. The table is therefore exhaustive.

## 11. Absolute convergence of the geometric expansion

### 11.1 Heights on twisted classes

Choose multiplicative heights $H_F$ on $F$ and $H_E$ on $E$. For a regular class with stable
norm polynomial $X^2-sX+d$, define

$$
H([\delta]_\sigma)=
H_F(s)H_F(d)H_F(d^{-1})H_F(\Delta^{-1}),
\qquad \Delta=s^2-4d.
\tag{11.1}
$$

For a scalar-norm class with norm $aI$, put

$$
H([\delta]_\sigma)=H_F(a)H_F(a^{-1}).
\tag{11.2}
$$

Different standard multiplicative heights are polynomially comparable, so convergence does
not depend on this choice. The factor $H_F(\Delta^{-1})$ records approach to the singular
locus; omitting it would make uniform orbit estimates false.

Finite-adelic support supplies bounded denominators. More precisely, for a fixed admissible
$f$, if $O_\delta^\sigma(f)\ne0$, then $s,d,d^{-1}$ lie in fixed fractional ideals outside a
finite set, and in the scalar case the same is true of $a,a^{-1}$. This follows by taking trace
and determinant of an element in the support of $f$ and using invariance under twisted
conjugacy.

### 11.2 Counting norm classes

**Lemma 11.1 (polynomial counting).** For fixed finite-adelic support, the number of regular or
scalar twisted classes with $H([\delta]_\sigma)\le R$ is $O(R^C)$ for some $C$ depending only
on $F,E$, and the support.

**Proof.** Bounded denominators place $s$ and $d$ in fixed fractional lattices of $F$. Under
the Minkowski embedding, height at most $R$ confines each coordinate to a box whose side lengths
are powers of $R$. Lattice-point counting is therefore polynomial. The regular norm
condition (10.7) selects a subset and cannot increase the count. For scalar classes the same
argument uses the one lattice coordinate $a$. The fiber theorems show that each admissible
invariant pair contributes at most one twisted class. $\square$

The lemma is deliberately coarse. No asymptotic formula for norm classes is needed; any fixed
polynomial exponent will be dominated by Schwartz decay.

### 11.3 Decay of twisted orbital integrals

**Proposition 11.2 (uniform orbital decay).** For every $N>0$ there are a Schwartz seminorm
$q_M$ and a constant $C_N$ such that every surviving rational twisted class satisfies

$$
|O_\delta^\sigma(f)|
\le C_N q_M(f)H([\delta]_\sigma)^{-N}.
\tag{11.3}
$$

The order $M$ may increase with $N$ but is independent of $\delta$.

**Proof strategy.** The coefficients $s,d$ are polynomial functions of an orbit point and its
Galois conjugates, so large invariant height forces large matrix height somewhere. Quotient
coordinates can lose powers of the discriminant near the singular locus, but only powers. The
height in (11.1) records exactly that loss. Arbitrary Schwartz decay then dominates both the
polynomial quotient volume and the polynomial loss of coordinates.

**Proof.** On the strongly regular locus, choose finitely many cyclic-vector charts for the norm
matrix and finitely many complementary minors of the tangent map (4.7). These charts cover the
whole locus, including diagonal representatives: a regular $2\times2$ matrix always has a
cyclic vector, although a fixed coordinate vector need not be cyclic. Cramer's rule expresses
the orbit and slice coordinates with denominators among the chosen tangent minors. The common
zero set of those minors is the locus where the twisted centralizer dimension jumps. By
Proposition 4.2 this is the inverse image of $\Delta=0$. Clearing denominators on the finite
affine cover therefore gives constants $m,C_v$ such that the quotient Jacobian and the volume
of every unit matrix-height box are bounded by

$$
C_v\max(1,|\Delta|_v^{-1})^m
$$

times a fixed power of the box height. Outside a finite set of places the charts, measures,
and class are integral with regular reduction, so $C_v=1$ and no loss occurs.

Let $Y_v=h_v^{-1}\delta\sigma(h_v)$ be an orbit point. Trace and determinant of
$N_\sigma(Y_v)$ are polynomials of degree at most $2\ell$ in the entries of the Galois
conjugates of $Y_v$ and their inverses. The elementary height inequality for a polynomial map,
multiplied over all places, gives

$$
H_F(s)H_F(d)H_F(d^{-1})
\le C\prod_v\max(1,\|Y_v\|_v,\|Y_v^{-1}\|_v)^c.
\tag{11.3a}
$$

The finite support bounds the factors on the right at every finite place. A small local
discriminant can enlarge a quotient chart, but the product formula and the factor
$H_F(\Delta^{-1})$ in (11.1) bound the product of all such enlargements by a fixed power of
$H([\delta]_\sigma)$. Consequently, on the part of the orbit where the integrand is not
already $O(H^{-N})$, (11.3a) forces an archimedean matrix height at least a fixed positive power
of $H$, after a fixed discriminant power is removed.

Divide each archimedean quotient into unit Cartan boxes. Their volumes grow at most
exponentially in Cartan distance, whereas matrix height grows exponentially away from the
stabilizer. A Schwartz estimate of order $M$ therefore makes the sum of the boxes converge and
contributes an arbitrarily large inverse power of $H$ once $M$ is chosen large enough. The
finitely many bad finite-place Jacobian factors cost only the fixed height power already
recorded above. This proves (11.3) for regular classes.

For scalar semisimple classes, use the explicit representatives $b_aI$ and $\delta_a$. Their
matrix norms and inverse norms control $H_F(a)H_F(a^{-1})$ by the same polynomial-height
inequality. On the split relative orbit, the only neutral Cartan direction lies in the
stabilizer $G(F_v)$; for a division centralizer the quotient has fewer escaping directions.
The identical box estimate therefore gives arbitrary inverse powers in the scalar height. $\square$

The proposition is a bound for the global orbital integral, not a claim that each local
orbital integral decays independently in a global height. At one place a class can approach
the singular set; the product formula is what restores global control.

To make the finite-place part of the proof more concrete, fix a lattice $\Lambda$ in the
four-dimensional matrix algebra. On a regular orbit, solving

$$
h^{-1}\delta\sigma(h)\in\Lambda
$$

modulo $I_\delta$ amounts in an orbit chart to solving finitely many linear congruences whose
coefficient determinant is a minor of (4.7). The index of the solution lattice is therefore
bounded by a power of $|D^\sigma(\delta)|_v^{-1}$. Haar measure of the solution set satisfies
the same bound. Only primes dividing a fixed denominator or the discriminant contribute.
Multiplying those indices produces a power of the norm of an integral discriminant ideal.

At infinity, divide the orbit quotient into unit Cartan boxes. In a box at distance $r$ from
the stabilizer, the orbit has matrix height at least $e^{cr}$ divided by a fixed power of the
coefficient height, and the box has volume at most $e^{Cr}$. A Schwartz bound of order $M$
makes its contribution at most $e^{-(cM-C)r}$ times that coefficient power. Summing boxes and
then choosing $M$ larger still yields any prescribed $H^{-N}$. This is the quantitative
content hidden by the phrase “Schwartz decay wins.”

For scalar division classes, reduced-norm anisotropy makes the Cartan quotient smaller, not
larger. For the split scalar relative orbit, the only potentially neutral Cartan direction is
the diagonal $G(F_v)$ direction already divided out by the stabilizer. Every remaining
direction changes $h^{-1}\sigma(h)$ exponentially. Thus the same box argument covers both
scalar channels uniformly.

### 11.4 Bounds for centralizer volumes

**Proposition 11.3 (polynomial volume bound).** There are constants $C,A>0$ such that for every
surviving class

$$
a(\delta)\le C H([\delta]_\sigma)^A.
\tag{11.4}
$$

**Proof.** For a regular elliptic norm, $I_\delta$ is the multiplicative group of the quadratic
field $K=F[\gamma]$. A fundamental domain for its norm-one idele-class quotient is built from
an ideal-class representative and a logarithmic fundamental parallelepiped for the units.
Minkowski's theorem bounds the norm of an ideal-class representative by a fixed power of the
absolute discriminant of $K$, while a basis chosen from successive minima bounds the regulator
and the covolume of the unit lattice by another fixed power. The discriminant of $K$ divides,
up to fixed denominators, the discriminant of $X^2-sX+d$, and is therefore bounded by a power
of (11.1).

For the split scalar channel the centralizer is fixed, so its volume is constant. For a
quadratic exceptional class, the quaternion algebra $(E/F,a)$ is ramified only at places where
$a$ fails the local norm condition. Finite support and the height of $a$ bound the product of
the residue norms of these places by a power of (11.2). A reduction-domain construction for
the norm-one units of a maximal order gives volume bounded by a fixed power of that ramification
product. Changing from maximal-order measures at the finitely many support places contributes
only a fixed constant. This proves (11.4). $\square$

Only an upper bound is required. Exact class-number, regulator, or mass formulas would add
normalization detail without improving convergence.

### 11.5 Summability

Combine Lemma 11.1 and Propositions 11.2--11.3. Divide the classes into dyadic shells

$$
2^m\le H([\delta]_\sigma)<2^{m+1}.
$$

The number of terms is $O(2^{mC})$, the volume is $O(2^{mA})$, and the orbital integral is
$O(2^{-mN})$ for arbitrary $N$. Taking $N>A+C+1$ makes

$$
\sum_{[\delta]}
|a(\delta)O_\delta^\sigma(f)|
\tag{11.5}
$$

converge geometrically.

The same bounds hold uniformly when $f$ ranges over a bounded set for the Schwartz seminorm
$q_M$. Thus every series in (10.8) is absolutely convergent and defines a continuous
distribution. Absolute convergence also permits regrouping the regular sum by stable norm and
the quadratic scalar sum by local obstruction data.

Finally, the tail estimate is uniform in the truncation parameter. Therefore the orbitwise
limit of Chapter 10 can be interchanged with the class sum. This closes the only remaining gap
in (10.8).

## 12. The convergent geometric distributions

### 12.1 The main geometric theorem

We can now state the result toward which the algebraic, measure-theoretic, and analytic threads
have been directed.

**Theorem 12.1 (twisted geometric expansion in prime degree).** Let $E/F$ be cyclic of prime
degree $\ell$, let $\sigma$ generate its Galois group, and let $f$ be an admissible test function
with a strongly cuspidal factor at one place. Then the diagonal distribution (8.6) is
absolutely convergent and

$$
\boxed{
J_{\mathrm{geom}}^\sigma(f)
=J_{\mathrm{sc,sp}}^\sigma(f)
+J_{\mathrm{reg,ell}}^\sigma(f)
+\mathbf1_{\ell=2}J_{\mathrm{sc,div}}^\sigma(f).}
\tag{12.1}
$$

More explicitly,

$$
J_{\mathrm{reg,ell}}^\sigma(f)
=\sum_{\substack{[\gamma]\ \mathrm{regular\ elliptic}\\
\gamma\in N_{E/F}^{T_\gamma}(T_\gamma(E))}}
a(\delta_\gamma)O_{\delta_\gamma}^\sigma(f),
\tag{12.2}
$$

where $\delta_\gamma$ is the unique twisted class with stable norm $\gamma$;
$J_{\mathrm{sc,sp}}^\sigma$ is (10.4); and the quadratic exceptional distribution is (10.5).
All displayed series converge absolutely and continuously in the admissible Schwartz topology.

No split regular or nonsemisimple term remains.

**Proof strategy.** Truncate first. On the compact core, regroup noncentral nonelliptic
elements by semilinear invariant lines and unfold them into the global parabolic transform.
Strong cuspidality kills its main term, and rapid decay kills the truncation boundary. Unfold
each remaining closed orbit through its reductive centralizer. Finally use the independent
height estimates to remove the cutoff and sum the orbit terms.

**Proof.** Propositions 8.1--8.2 define the diagonal distribution and prove (9.5).
Sections 9.1--9.4 justify every finite truncated rearrangement, and Theorem 9.2 removes the
split regular and nonsemisimple channels. Sections 10.1--10.4 give the orbitwise limits for the
three surviving families with the coefficient and orbital measures of Chapter 7. Chapter 11
proves absolute, locally uniform summability and permits the orbitwise limits to pass through
the class sums. The resulting identity is exactly (12.1). $\square$

### 12.2 Continuity and independence of cutoffs

The proof gives more than pointwise convergence. For a sufficiently high Schwartz seminorm
$q_M$,

$$
|J_{\mathrm{geom}}^\sigma(f)|\le Cq_M(f).
\tag{12.3}
$$

Indeed, the shell estimate in Section 11.5 is uniform on the $q_M$-unit ball. Thus the
geometric side is a continuous distribution.

Suppose $\Lambda_T'$ is another family of rank-one cutoffs with the same compact-core and cusp-
strip properties. The difference of the two truncated integrals is supported where the height
tends to infinity. Rapid decay (8.5) makes this difference tend to zero. On the geometric
expansion, absolute summability makes the same conclusion termwise and then uniformly. Hence
(12.1) is independent of the truncation, the Siegel set, and the auxiliary height within the
usual polynomially comparable class.

It is also independent of rescaling centralizer measures, by (7.7). These independence
statements are logically separate: cutoff independence comes from analytic decay, while measure
independence comes from quotient integration.

### 12.3 Central-character realization

Many trace comparisons fix a $\sigma$-invariant unitary Hecke character

$$
\Omega:E^\times\backslash\mathbf A_E^\times\longrightarrow\mathbf C^\times,
\qquad \Omega\circ\sigma=\Omega.
$$

Use smooth test functions that are compactly supported modulo the center at finite places,
Schwartz modulo the center at archimedean places, and satisfy inverse central covariance

$$
f(zg)=\Omega(z)^{-1}f(g).
\tag{12.4}
$$

Then convolution is taken over $Z(\mathbf A_E)\backslash G(\mathbf A_E)$ and the kernel sum is
indexed by $Z(E)\backslash G(E)$. The diagonal is well defined: replacing $x$ by $zx$ changes
the argument by the central factor $z^{-1}\sigma(z)$, on which $\Omega$ is trivial by
$\sigma$-invariance.

Disintegrate the determinant-one formula along the norm-one idele-class center and apply its
$\Omega$-Fourier coefficient. Absolute convergence from Theorem 12.1 justifies this operation.
The result has the same three channels as (12.1), but it is indexed by projective twisted
classes, namely the $E^\times$-orbits of actual twisted classes.

There is an important restriction on how the regular channel may be reindexed. Replacing a
lift $\delta$ by $z\delta$ changes its actual stable norm $\gamma$ to
$N_{E/F}(z)\gamma$. It follows that two lift norms are identified by central projection only
through a scalar in $N_{E/F}(E^\times)$, not automatically through every scalar in
$F^\times$. Their images in $\mathrm{PGL}_2(F)$ can therefore coincide while the projective
twisted classes remain distinct. The safe regular indexing is

$$
\{[\delta]_\sigma:\delta\text{ regular elliptic}\}/E^\times,
\tag{12.4a}
$$

or, equivalently, norm pairs $(\gamma,[c])$ modulo the norm-scalar relation actually induced
by a lift. One may replace (12.4a) by projective stable norms only after proving that the
resulting fiber has no extra scalar obstruction. No such unwarranted collapse is made here.

All split scalar norms do combine into one scalar projective channel, with $\Omega$ supplying
the scalar weight. In quadratic degree the exceptional scalar channels are indexed by the
nontrivial classes in $F^\times/N(E^\times)$. These two scalar assertions follow directly
from Theorem 5.1 and do not imply the stronger, false assertion that every regular projective
fiber is a singleton.

For a chosen projective class, the projective twisted stabilizer is

$$
\overline I_\delta(F)=
\{h\in G(E):h^{-1}\delta\sigma(h)=z\delta
\text{ for some }z\in E^\times\}/E^\times,
\tag{12.5}
$$

and quotient integration defines its orbital measure. Formula (12.5) can have a finite
enlargement over $I_\delta/F^\times$ when a projective norm has a scalar symmetry; the central
disintegration automatically includes the corresponding finite index. This is safer than
silently replacing the projective stabilizer by the ordinary twisted centralizer.

Thus the determinant-one and central-character formulas are two realizations of the same
distribution, not rival normalizations. The first keeps the scalar-norm classification most
transparent; the second is often best suited to a fixed automorphic central character.

More explicitly, let

$$
C_E^1=E^\times\backslash\{z\in\mathbf A_E^\times:|z|_{\mathbf A_E}=1\}.
$$

This is compact. Restriction of a central-covariant function to $H(\mathbf A_F)^1$ has
$\Omega^{-1}$-covariance under $C_E^1$, and the corresponding isotypic projector is integration
against $\Omega$ over this compact group. Conversely, choose a central section $z(t)$ of the
positive determinant modulus. An $\Omega^{-1}$-covariant function on the determinant-one group
extends uniquely modulo the center by

$$
f(z(t)h^1)=\Omega(z(t))^{-1}f(h^1).
$$

If an integrable function on the full determinant direction is desired before taking the
central quotient, multiply this extension by a smooth compactly supported $\rho(t)$ with
$\int\rho(t)\,dt/t=1$. Apply Theorem 12.1 first and then the compact $C_E^1$-projector.
Absolute convergence permits the projector to pass through the class sum and groups precisely
the scalar multiples described above. A different normalized $\rho$ has the same central
quotient integral, so the resulting distribution is independent of the auxiliary lift.

The hypothesis $\Omega\circ\sigma=\Omega$ is necessary. Without it, the field automorphism
sends the $\Omega$-central-character space to the distinct
$\Omega\circ\sigma^{-1}$ space. One can then form a twisted kernel between two different line
bundles, but it has no diagonal trace on a single fixed-central-character Hilbert space. The
geometric orbit theory remains meaningful; the trace-distribution interpretation changes.

### 12.4 Change of generator

Let $1\le r<\ell$ and put $\tau=\sigma^r$. Define

$$
\delta^{(r)}=\delta\sigma(\delta)\cdots\sigma^{r-1}(\delta).
\tag{12.6}
$$

In the semidirect product,

$$
(\delta\rtimes\sigma)^r
=\delta^{(r)}\rtimes\sigma^r.
\tag{12.7}
$$

Consequently

$$
N_\tau(\delta^{(r)})=N_\sigma(\delta)^r.
\tag{12.8}
$$

Equations (12.6)--(12.8) are the exact conversion rule between generator conventions. They
show that changing the generator is not a harmless relabeling of the same twisted trace: the
twisting operator changes from $\sigma$ to $\sigma^r$, and stable norms are carried through the
$r$th-power operation. What is invariant is the method and its measure normalization. After
replacing every occurrence of $\sigma$ consistently by $\tau$, Theorem 12.1 applies verbatim.

This corrects two tempting mistakes. One must not keep the old ordered norm while changing the
twist, and one must not claim that traces of two different field automorphisms are automatically
equal.

## 13. Local-global norm bookkeeping

### 13.1 Localization of a global twisted class

A global element $\delta\in G(E)$ determines a local twisted class in
$G(E_v)$ at every place $v$ of $F$. Its stable norm localizes compatibly:

$$
\gamma_{\delta,v}\sim
N_{\sigma,v}(\delta)
\qquad\text{in }G(E_v),
\tag{13.1}
$$

and its twisted centralizer satisfies

$$
I_\delta\otimes_FF_v\simeq I_{\delta,v}.
\tag{13.2}
$$

Both assertions follow from the fact that ordered multiplication, trace, determinant, fixed
algebras, and centralizers commute with scalar extension. In particular, a global regular norm
class lies in the local torus-norm image at every place.

The converse requires more care. Arbitrarily chosen local twisted classes need not arise from
one global matrix: their stable norm polynomials must be localizations of one polynomial over
$F$, their scalar obstruction invariants must satisfy a product relation, and their measures
must be induced from a common global choice. Local existence is therefore one part of a
globalization problem, not a substitute for it.

At almost every place a global class is unramified integral. Choose integral models of $E/F$,
$G$, and the centralizer away from a finite set. Then $\delta\in G(\mathcal O_{E_v})$, its norm
has regular reduction whenever the global discriminant is a unit, and the local centralizer is
the corresponding smooth integral torus. These are exactly the places at which the unit
orbital factor in Proposition 7.2 is normalized to one.

### 13.2 The regular Hasse norm condition

Let $\gamma\in G(F)$ be regular semisimple and put $K=F[\gamma]$. The global criterion is

$$
\gamma\in N_{K\otimes_FE/K}((K\otimes_FE)^\times).
\tag{13.3}
$$

It can be checked locally.

**Theorem 13.1 (local-global criterion for regular norms).** A regular semisimple
$\gamma\in G(F)$ is a stable norm from $G(E)$ if and only if it is a stable local norm from
$G(E_v)$ at every place $v$ of $F$.

**Proof strategy.** By Theorem 3.3 the problem is a norm equation in the quadratic étale algebra
$K$. After base change from $F$ to $K$, the extension is cyclic or split. The cyclic Hasse
norm theorem turns local solvability into global solvability.

**Proof.** If $K=F\times F$, condition (13.3) is the pair of norm equations for the two
eigenvalues. For each component, the cyclic Hasse norm theorem for $E/F$ says that an element
is a global norm exactly when it is a norm at every completion.

Suppose $K$ is a quadratic field. If $K$ and $E$ are linearly disjoint, $KE/K$ is cyclic of
degree $\ell$, and (13.3) is the norm equation from $KE$ to $K$. Localizing over every place
of $K$ is equivalent to localizing the torus equation over every place of $F$, and the cyclic
Hasse norm theorem applies. If $K=E$, which can occur only when $\ell=2$, then
$K\otimes_FE\simeq K\times K$ and the norm is multiplication, hence is surjective globally and
locally. These cases exhaust the possibilities. $\square$

For reference, the cyclic Hasse norm theorem used in the proof follows from cyclic algebras.
For a cyclic extension $L/K$ and $c\in K^\times$, $c$ is a local norm at a place $u$ exactly
when the local cyclic algebra $(L_u/K_u,c)$ is split, equivalently when its local Brauer
invariant is zero. If this holds for every $u$, the global cyclic algebra has zero localization
everywhere. Injectivity of the global Brauer group into the direct sum of local Brauer groups
makes it split globally, and the cyclic-algebra criterion then gives $c=N_{L/K}(b)$. This also
shows why cyclicity is essential; the Hasse norm principle can fail for noncyclic extensions.

The theorem does not say that any arbitrary collection of local representatives globalizes.
Once the global stable norm $\gamma$ exists, however, the regular fiber is a singleton globally
and locally. Thus no further rational conjugacy invariant remains to be patched.

### 13.3 Quaternionic obstruction data

Now let $\ell=2$ and consider scalar norm $aI$. At each place define

$$
\epsilon_v(a)=
\begin{cases}
0,&a\in N(E_v^\times),\\
\tfrac12,&a\notin N(E_v^\times).
\end{cases}
\tag{13.4}
$$

This is the local Brauer invariant of $(E/F,a)$. It vanishes at split places and at almost all
places. Global reciprocity gives

$$
\sum_v\epsilon_v(a)=0\quad\text{in }\mathbf Q/\mathbf Z.
\tag{13.5}
$$

Thus the number of division places is even.

Conversely, the local invariants determine the global quaternion algebra. If all vanish, the
cyclic Hasse norm theorem makes $a$ a global norm and the scalar class is split. If some are
nonzero, the global algebra is division and the class contributes to the exceptional
distribution. Projectively, the map

$$
F^\times/N(E^\times)
\longrightarrow
\bigoplus_vF_v^\times/N(E_v^\times)
\tag{13.6}
$$

is injective, and its image consists of finite-support families satisfying (13.5). Injectivity
is again the Hasse norm theorem; the description of the image is the existence theorem for
global quaternion algebras with prescribed local invariants.

This is the complete local-global obstruction ledger for scalar norms. There is no analogous
odd-degree term because a degree-two central simple algebra cannot carry a nonzero Brauer class
killed by an odd prime.

### 13.4 Product constraints and measures

For a rational strongly regular $\delta$, the algebraic discriminant
$D^\sigma(\delta)$ lies in $F^\times$. The product formula gives

$$
\prod_v|D^\sigma(\delta)|_v=1.
\tag{13.7}
$$

Consequently the product of normalized local orbital integrals equals the product of ordinary
local orbital integrals whenever both use the same rational discriminant convention:

$$
\prod_v I_{\delta,v}^\sigma(f_v)
=\prod_v O_{\delta,v}^\sigma(f_v).
\tag{13.8}
$$

This does not make the local normalization irrelevant. A local transfer identity is stated
place by place and sees the factor $|D^\sigma(\delta)|_v^{1/2}$; only the global product cancels.

Likewise, local centralizer measures cannot be chosen independently if their product is to
represent a global coefficient. Given global invariant differential forms on $H$ and
$I_\delta$, their local absolute values define measures whose restricted product satisfies
quotient integration. Replacing the form on $I_\delta$ multiplies local measures by constants
$c_v$ with a convergent product; (7.7) then preserves the global term.

For a factorizable $f$, the complete local-global formula for one surviving class is

$$
a(\delta)O_\delta^\sigma(f)
=a(\delta)\prod_vO_{\delta,v}^\sigma(f_v).
\tag{13.9}
$$

The coefficient is global. It must not be factored into a naïve product of local volumes:
rational points couple the local centralizer quotients through class groups, units, and the
product formula. Orbital integrals factor; arithmetic centralizer volumes generally do not.

## 14. Worked geometric models

### 14.1 A split regular norm

Let $E/F$ be cyclic of prime degree and choose $u,v\in E^\times$ with
$N(u)\ne N(v)$. Put

$$
\delta=\begin{pmatrix}u&0\\0&v\end{pmatrix}.
$$

Then

$$
N_\sigma(\delta)=
\begin{pmatrix}N(u)&0\\0&N(v)\end{pmatrix}=\gamma.
\tag{14.1}
$$

The two semilinear invariant lines are the coordinate axes. The twisted centralizer equation
for $x=\operatorname{diag}(x_1,x_2)$ becomes $\sigma(x_i)=x_i$, so

$$
I_\delta\simeq\mathbf G_m^2.
$$

Conversely, if a split regular matrix has eigenvalues $a,b$, it can be a norm only if both are
field norms. For example, determinant $ab$ can be a norm while neither $a$ nor $b$ is a norm:
take a nontrivial class $c$ in $F^\times/N(E^\times)$ and eigenvalues representing $c$ and
$c^{-1}$. Their product is one, but (3.6) fails in both coordinates. This gives a concrete
counterexample to a determinant-only norm criterion.

In the global geometric expansion, the class (14.1) belongs to the nonelliptic channel. Its
two invariant lines account for the factor $e(\delta)^{-1}=1/2$ in incidence unfolding. It
does not survive as an individual term after the strongly cuspidal parabolic transform is
applied.

### 14.2 An elliptic quadratic norm

Let $K/F$ be a quadratic field and embed $K$ into $M_2(F)$ by its regular representation.
Choose $c\in K^\times$ that generates $K$ over $F$. Assume first that $K$ and $E$ are linearly
disjoint. If

$$
c=N_{KE/K}(t)
$$

for some $t\in(KE)^\times$, view $t$ as an element of
$T_c(E)=(K\otimes_FE)^\times$ and as a matrix $\delta\in G(E)$. Then

$$
N_\sigma(\delta)=c=\gamma.
$$

The characteristic polynomial of $c$ over $F$ is irreducible, so the class is strongly regular
elliptic. Its centralizer is $K^\times$, and the coefficient is the volume of the norm-one
idele-class quotient of $K$ in the chosen measures.

If $c$ is not a norm from $KE/K$, there is no twisted class above $\gamma$, even if
$N_{K/F}(c)=\det\gamma$ happens to be a norm from $E/F$. The obstruction lives in the full
torus, not its determinant character.

When $\ell=2$ and $K=E$, the tensor product $K\otimes_FE$ is split and every $c\in K^\times$
is a torus norm. This does not contradict the preceding obstruction: the extension of the
centralizer algebra has changed from the field $KE/K$ to the split algebra $K\times K/K$.

### 14.3 An unramified cubic example

Let $L/k$ be an unramified cubic extension of nonarchimedean local fields, with common
uniformizer $\varpi$. The norm is surjective on units and satisfies

$$
v_k(N_{L/k}x)=3v_L(x).
\tag{14.2}
$$

Therefore a split regular matrix $\gamma=\operatorname{diag}(a,b)$ is a local twisted norm if
and only if

$$
v_k(a)\equiv v_k(b)\equiv0\pmod3.
\tag{14.3}
$$

The unit parts create no further obstruction. If
$a=\varpi^{3m}u$ and $b=\varpi^{3n}v$, choose units $u',v'$ with norms $u,v$ and take

$$
\delta=\operatorname{diag}(\varpi^m u',\varpi^n v').
$$

Its ordered norm is $\gamma$.

This geometric calculation matches the direction of local cyclic base change. Characters
pull back by $N_{L/k}$, while geometric eigenvalues that are to be norms must lie in the image
of the same map. It also shows why ``unramified'' does not mean that every element is a norm:
the norm is surjective on units but multiplies valuations by the residue degree.

For an unramified elliptic torus $K^\times$, the same statement is applied after replacing
$k$ by $K$ and $L$ by $K\otimes_kL$. The valuation obstruction is controlled by the residue
degree of that étale extension, which can differ when $K$ and $L$ intersect.

### 14.4 A quadratic scalar norm with division centralizer

Take

$$
F=\mathbf Q,
\qquad E=\mathbf Q(i),
\qquad a=-1.
$$

The number $-1$ is not a norm from $E^\times$, already because every norm is positive at the
real place. Set

$$
\delta=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

Since $\delta$ has rational entries,

$$
N_\sigma(\delta)=\delta^2=-I.
$$

The fixed algebra is

$$
(\mathbf Q(i)/\mathbf Q,-1)=(-1,-1)_{\mathbf Q},
$$

the Hamilton quaternion algebra over $\mathbf Q$. It is division, ramified at the real place
and at $2$. The two ramified places satisfy the even-cardinality rule (13.5).

Thus a stable norm lying at the central point $-I$ has anisotropic projective twisted
centralizer. Its global orbit term is

$$
\operatorname{vol}\bigl(B^\times(\mathbf Q)\backslash
B^\times(\mathbf A)^1\bigr)
\int_{B^\times(\mathbf A)^1\backslash
\mathrm{GL}_2(\mathbf A_E)^1}
f(h^{-1}\delta\sigma(h))\,d\dot h.
$$

There is no regular Weyl discriminant factor, and there is no parabolic cancellation: the
division quotient is elliptic. Omitting this term would make every quadratic twisted geometric
formula incomplete.

### 14.5 A nonsemisimple norm and its disappearance

Let $N_0=\begin{psmallmatrix}0&1\\0&0\end{psmallmatrix}$ and choose $c\in E$. Put

$$
\delta=I+cN_0.
$$

Because $N_0^2=0$, multiplication of the conjugates has no cross terms:

$$
N_\sigma(\delta)
=\prod_{j=0}^{\ell-1}(I+\sigma^j(c)N_0)
=I+\operatorname{Tr}_{E/F}(c)N_0.
\tag{14.4}
$$

If $\operatorname{Tr}_{E/F}(c)\ne0$, the norm is noncentral Jordan. It has exactly one
invariant line and centralizer the unit group of the dual-number algebra. Its geometric
contribution enters the one-line incidence channel and disappears by Theorem 9.2.

If $\operatorname{Tr}_{E/F}(c)=0$, additive Hilbert 90 gives $c=\sigma(u)-u$ for some $u\in E$.
Since $N_0^2=0$,

$$
(I+uN_0)^{-1}\sigma(I+uN_0)
=I+(\sigma(u)-u)N_0=\delta.
$$

Thus $\delta$ is twisted conjugate to the identity and belongs to the split scalar-norm
channel. The calculation displays the sharp boundary: the same triangular family is
nonsemisimple when the trace is nonzero and a scalar twisted cocycle when the trace vanishes.

## 15. The geometric package for cyclic comparison

### 15.1 The classification and measure ledger

The complete result can be compressed into a theorem without suppressing its hypotheses.

**Theorem 15.1 (prime-degree twisted geometric package for $\mathrm{GL}_2$).** Let $E/F$ be a
cyclic extension of number fields of prime degree and fix a generator $\sigma$.

1. Twisted classes are similarity classes of invertible $\sigma$-semilinear operators on
   $E^2$. Their ordered norms have characteristic polynomial over $F$ and hence a stable norm
   class in $G(F)$.
2. A regular semisimple $\gamma\in G(F)$ is a stable norm exactly when

   $$
   \gamma\in N_{E/F}^{T_\gamma}(T_\gamma(E)).
   $$

   If the fiber is nonempty, it contains one rational twisted class, and its twisted
   centralizer is $T_\gamma$.
3. For split $\gamma$ the norm criterion is componentwise on the two eigenvalues. For elliptic
   $\gamma$, it is the norm equation from $K\otimes_FE$ to the quadratic field
   $K=F[\gamma]$. This global condition is equivalent to all its local conditions.
4. A noncentral repeated norm has dual-number centralizer and belongs to the parabolic channel.
5. A scalar norm has centralizer $B^\times$ for a degree-two central simple algebra $B$ split
   by $E$. For odd prime degree $B$ is split and the class is twisted conjugate to a scalar.
   For quadratic degree, $B=(E/F,a)$; it is split precisely when $a$ is a norm and otherwise is
   quaternion division.
6. Local twisted orbital integrals are defined using quotient measures complementary to the
   centralizer measures. They converge on twisted semisimple classes, factor adelically for
   tensor test functions, and their product with the global centralizer volume is independent
   of measure rescaling.
7. For an admissible test function with one strongly cuspidal local factor, the twisted diagonal
   kernel is rapidly decreasing and integrable. Its geometric distribution is the absolutely
   convergent sum (12.1): split scalar norms, regular elliptic norms, and, in quadratic degree,
   division-centralizer scalar norms. Split regular and nonsemisimple classes cancel in the
   combined parabolic distribution.

**Proof.** Items 1--4 are Chapters 2--4 and Theorems 3.3--3.4. Item 5 is Theorem 5.1. Local
and global measure assertions are Propositions 6.1, 7.1, and 7.2 together with (7.7). The
kernel construction is Chapter 8, parabolic cancellation is Theorem 9.2, orbit unfolding is
Chapter 10, and absolute convergence is Chapter 11. These combine in Theorem 12.1. $\square$

The theorem is intentionally generator-sensitive and measure-explicit. It does not replace
$N_\sigma$ by an unordered product, does not identify projective and actual scalar norms, and
does not hide the quadratic inner form under the word ``singular.''

### 15.2 What remains local

The global distribution is now an honest receptacle for local comparison. At every place, a
matching problem may ask for a function on $G(F_v)$ whose ordinary stable orbital integral at
$\gamma_v$ equals the twisted stable orbital integral (6.8). The present book supplies:

- the exact set of norm classes on which such an identity can be nonzero;
- the centralizer identification needed to compare quotient measures;
- the discriminant normalization;
- the split-place reduction to ordinary conjugacy;
- the scalar quaternionic boundary;
- the global product and summability that permit local identities to be multiplied.

What it does not supply is the value of those integrals for hyperspecial units, Iwahori
functions, ramified level functions, or archimedean selectors. Those require lattice counts,
descent near singular elements, and explicit harmonic analysis. Nor does the present geometric
identity identify a spectral representation. A twisted spectral expansion must construct the
field-automorphism intertwiner on each invariant automorphic representation and prove that the
noncuspidal spectrum vanishes for the selected test functions.

This boundary is logical rather than stylistic. Geometry says which rational orbits can
contribute and proves that their sum converges. Local matching says that two groups assign the
same values to corresponding orbits. Spectral theory says which representations those values
count. None of the three statements proves either of the others.

### 15.3 Conclusion

Twisted conjugacy is ordinary similarity viewed through a semilinear lens. That observation
turns the ordered product of Galois conjugates into the $\ell$th power of one semilinear
operator and explains why its characteristic polynomial descends to the base field. In rank
two, the polynomial leads directly to a split torus, a quadratic torus, a dual-number algebra,
or a scalar descent algebra. Hilbert 90 then makes every regular norm fiber exact: existence is
the norm equation in the centralizer torus, and uniqueness leaves no missing rational class.

The scalar boundary contains the one genuinely prime-degree surprise. Odd degree cannot
support a nontrivial degree-two Brauer obstruction. Quadratic degree can, and a nonnorm scalar
creates a quaternion division centralizer. These classes are elliptic even though their stable
norm is central. Their local invariants, global reciprocity constraint, and adelic volumes fit
the same measure ledger as the regular elliptic tori.

On the analytic side, the safe order of operations is now fixed. The twisted kernel is first
shown to converge as a rational-point sum. The quotient is truncated before classes are
regrouped. Semilinear invariant lines turn the nonelliptic portion into the unique parabolic
transform, one strongly cuspidal local factor kills its main term, and rapid decay removes its
boundary. Closed elliptic and scalar-norm orbits are then unfolded through their actual
centralizers. Independent height estimates prove that the resulting series is absolutely
summable, so the final formula is a continuous geometric distribution rather than a formal
regularization.

The resulting package is ready for cyclic comparison: exact norm image, unique regular fibers,
all centralizers, compatible local and global measures, the quadratic inner-form exception, and
a convergent central-plus-elliptic geometric expansion. It is precisely the geometry needed
before local orbital matching and a twisted spectral trace can be joined into a global cyclic
base-change argument.
