# Integral Fontaine--Laffaille Equivalence and Base Change

## Contents

1. [The missing integral equivalence](#1-the-missing-integral-equivalence)
   - [From faithful realization to classification](#11-from-faithful-realization-to-classification)
   - [Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
   - [The three categories](#13-the-three-categories)
   - [The proof architecture](#14-the-proof-architecture)
2. [Exact categories and variance](#2-exact-categories-and-variance)
   - [The Fontaine--Laffaille side](#21-the-fontaine--laffaille-side)
   - [The finite-flat side](#22-the-finite-flat-side)
   - [The generic side](#23-the-generic-side)
   - [Why two reversals give covariance](#24-why-two-reversals-give-covariance)
3. [The filtered crystal of a finite-flat group](#3-the-filtered-crystal-of-a-finite-flat-group)
   - [Crystalline extensions and the Hodge step](#31-crystalline-extensions-and-the-hodge-step)
   - [Frobenius divided on the Hodge step](#32-frobenius-divided-on-the-hodge-step)
   - [Strong divisibility](#33-strong-divisibility)
   - [Torsion presentations and exactness](#34-torsion-presentations-and-exactness)
4. [The finite-flat solution functor](#4-the-finite-flat-solution-functor)
   - [Solutions as a sheaf](#41-solutions-as-a-sheaf)
   - [Normal coordinates](#42-normal-coordinates)
   - [The integral coordinate lemma](#43-the-integral-coordinate-lemma)
   - [Descent and independence of choices](#44-descent-and-independence-of-choices)
5. [Representability and exactness](#5-representability-and-exactness)
   - [Finite local freeness](#51-finite-local-freeness)
   - [The group law and generic fiber](#52-the-group-law-and-generic-fiber)
   - [Exact sequences](#53-exact-sequences)
   - [Length and order](#54-length-and-order)
6. [The integral period comparison](#6-the-integral-period-comparison)
   - [Evaluation on a geometric point](#61-evaluation-on-a-geometric-point)
   - [The two endpoints](#62-the-two-endpoints)
   - [The local--local calculation](#63-the-local--local-calculation)
   - [The comparison theorem](#64-the-comparison-theorem)
7. [Essential surjectivity and the anti-equivalence](#7-essential-surjectivity-and-the-anti-equivalence)
   - [The two comparison morphisms](#71-the-two-comparison-morphisms)
   - [No circular use of full faithfulness](#72-no-circular-use-of-full-faithfulness)
   - [The equivalence theorem](#73-the-equivalence-theorem)
   - [Uniqueness and reconstruction](#74-uniqueness-and-reconstruction)
8. [Which torsion representations are finite flat](#8-which-torsion-representations-are-finite-flat)
   - [The intrinsic essential image](#81-the-intrinsic-essential-image)
   - [Subobjects and quotients](#82-subobjects-and-quotients)
   - [Extensions](#83-extensions)
   - [Examples and nonexamples](#84-examples-and-nonexamples)
9. [Duality, pairings, and coefficients](#9-duality-pairings-and-coefficients)
   - [Cartier duality](#91-cartier-duality)
   - [Perfect pairings](#92-perfect-pairings)
   - [Coefficient actions](#93-coefficient-actions)
   - [Determinants in height two](#94-determinants-in-height-two)
10. [Unramified change of the ground field](#10-unramified-change-of-the-ground-field)
    - [Base change of divided filtered modules](#101-base-change-of-divided-filtered-modules)
    - [Base change of finite-flat groups](#102-base-change-of-finite-flat-groups)
    - [Base change of generic realization](#103-base-change-of-generic-realization)
    - [Transitivity and infinite residue extensions](#104-transitivity-and-infinite-residue-extensions)
11. [Unramified descent](#11-unramified-descent)
    - [Semilinear descent data](#111-semilinear-descent-data)
    - [Effectivity](#112-effectivity)
    - [Galois descent and invariants](#113-galois-descent-and-invariants)
    - [Why ramified descent is excluded](#114-why-ramified-descent-is-excluded)
12. [Integral change of coefficient rings](#12-integral-change-of-coefficient-rings)
    - [Restriction and coextension](#121-restriction-and-coextension)
    - [The dual scalar operation](#122-the-dual-scalar-operation)
    - [Finite flat coefficient change](#123-finite-flat-coefficient-change)
    - [Trace self-duality and the different](#124-trace-self-duality-and-the-different)
13. [Nonflat coefficient quotients](#13-nonflat-coefficient-quotients)
    - [The admissible annihilator](#131-the-admissible-annihilator)
    - [The compatible-quotient theorem](#132-the-compatible-quotient-theorem)
    - [Successive ideals and exact sequences](#133-successive-ideals-and-exact-sequences)
    - [Comparison with naive annihilators](#134-comparison-with-naive-annihilators)
14. [Stable lattices and all finite quotients](#14-stable-lattices-and-all-finite-quotients)
    - [Compatible Fontaine--Laffaille systems](#141-compatible-fontaine--laffaille-systems)
    - [Recovering a stable lattice](#142-recovering-a-stable-lattice)
    - [Arbitrary open ideals](#143-arbitrary-open-ideals)
    - [Changing the stable lattice](#144-changing-the-stable-lattice)
15. [The height-two package](#15-the-height-two-package)
    - [Rank two and Hodge type zero--one](#151-rank-two-and-hodge-type-zero--one)
    - [Ordinary and local--local fibers](#152-ordinary-and-local--local-fibers)
    - [Stable lines and reducible representations](#153-stable-lines-and-reducible-representations)
    - [A height-two equivalence theorem](#154-a-height-two-equivalence-theorem)
16. [Boundaries and failure modes](#16-boundaries-and-failure-modes)
    - [The prime two boundary](#161-the-prime-two-boundary)
    - [Ramified bases](#162-ramified-bases)
    - [Rational data do not select a lattice](#163-rational-data-do-not-select-a-lattice)
    - [A hypothesis ledger](#164-a-hypothesis-ledger)
17. [The integral classification package](#17-the-integral-classification-package)
    - [The main theorem](#171-the-main-theorem)
    - [Dependency closure](#172-dependency-closure)
    - [A calculation protocol](#173-a-calculation-protocol)
    - [Conclusion](#174-conclusion)

## 1. The missing integral equivalence

Book 53 constructed a contravariant functor from divided filtered torsion modules to finite Galois modules and proved that it is exact and fully faithful. Those are strong statements, but they answer only questions about objects already known to lie on the filtered side. The decisive remaining question is existence: does every divided filtered module describe an actual finite-flat group, and does every finite-flat group yield one of these modules? This book proves that both answers are yes over an absolutely unramified mixed-characteristic base in the low-weight range.

### 1.1 From faithful realization to classification

Full faithfulness reconstructs a morphism $M\to N$ once both $M$ and $N$ have been supplied. It cannot manufacture an object representing a Galois-stable subgroup of $T_{\mathrm{FL}}(M)$. Using it that way would assume essential surjectivity in the step intended to prove essential surjectivity.

There are therefore two constructions to make. Starting from a finite-flat group $\mathcal G$, its crystalline extension module must be equipped with a Hodge step and divided Frobenius. Starting from a divided filtered module $M$, the syntomic solutions of a free presentation must first be represented by finite locally free groups; the subgroup cut out on the generic fiber must then be extended by schematic closure. The two constructions will be compared by actual natural morphisms.

The desired chain has two contravariant arrows:

$$
\mathcal G
\longmapsto \mathbf D_{\mathrm{FL}}(\mathcal G)
\longmapsto T_{\mathrm{FL}}(\mathbf D_{\mathrm{FL}}(\mathcal G)).
\tag{1.1}
$$

The composite is covariant and will be identified with $\mathcal G(\overline K_0)$. This fixes every later variance convention.

### 1.2 Standing hypotheses and notation

Unless a theorem explicitly changes the data, assume

$$
p>2,\qquad k\text{ perfect of characteristic }p,\qquad
W=W(k),\qquad K_0=W[1/p].
\tag{1.2}
$$

Write $\sigma$ for Witt Frobenius, fix an algebraic closure $\overline K_0$, and write $G_{K_0}$ for its absolute Galois group. The valuation is normalized by $v_W(p)=1$. Thus the absolute ramification index is $e=1$, and

$$
e=1<p-1.
\tag{1.3}
$$

This last strict inequality is what makes generic fiber fully faithful on finite-flat commutative $p$-groups. It is also compatible with the Fontaine--Laffaille weight condition $[0,1]\subset[0,p-2]$.

All group schemes are commutative. A finite-flat group means finite locally free over $W$ and of $p$-power order. All divided filtered modules have weights in $[0,1]$ and all their exact sequences are strict on the first filtered step. Galois modules are finite discrete $p$-primary modules with continuous action.

### 1.3 The three categories

We use the following notation.

- $\mathrm{FF}_W$ is the exact category of finite locally free commutative $p$-power-order group schemes over $W$. An exact sequence is exact as fppf sheaves, with a finite locally free kernel and faithfully flat quotient.
- $\mathrm{MF}^{[0,1]}_{\mathrm{tor}}(W)$ is the exact category of admissible torsion divided filtered modules defined in Book 53.
- $\mathrm{Rep}^{\mathrm{ff}}_{\mathbf Z_p}(G_{K_0})$ is the full subcategory of finite continuous $p$-primary representations admitting a finite-flat model over $W$.

The superscript “ff” is an existence condition, not a chosen model. Book 42 emphasized that distinction over a general DVR. Under (1.3), however, Raynaud rigidity makes a marked model unique up to unique isomorphism. Existence and choice still remain logically different, but the choice becomes contractible once it exists.

### 1.4 The proof architecture

Chapters 3--6 establish the two constructions independently. Chapter 3
forms $\mathbf D_{\mathrm{FL}}(\mathcal G)$ from crystalline extensions.
Chapters 4--5 represent the solution sheaf for free reductions and then
use saturated schematic closure to construct the unique finite-flat
model $\mathcal G(M)$ of every geometric solution module. Chapter 6
proves that evaluation identifies the generic points of the group-crystal
construction with the realization of Book 53.

Only after those steps does Chapter 7 prove the anti-equivalence. Chapters 8--9 identify its essential image and transport exactness, duality, pairings, and coefficient actions. Chapters 10--13 prove ground-field base change and the coefficient statements at the correct variance. Chapters 14--15 package compatible finite quotients of stable lattices, especially rank two and Hodge type $(0,1)$.

The order matters. Representability precedes essential surjectivity; essential surjectivity precedes closure under arbitrary Galois subquotients; and the integral equivalence precedes the compatible-quotient theorem.

## 2. Exact categories and variance

An equivalence between integral categories must preserve more than isomorphism classes. Later applications take kernels, quotients, duals, coefficient actions, and inverse systems. This chapter recalls exactly which sequences are admitted and determines the arrow directions before any construction is made.

### 2.1 The Fontaine--Laffaille side

An object $M$ consists of a finite-length $W$-module, a submodule $F_M$, and $\sigma$-semilinear maps

$$
\varphi _0:M\to M,\qquad \varphi _1:F_M\to M,\qquad
\varphi _0|_{F_M}=p\varphi _1,
\tag{2.1}
$$

admitting a strict two-term presentation by finite free strongly divisible objects. For a free object, $F_M$ is a direct summand and, after choosing $M=C\oplus F_M$, the normal map

$$
\sigma^*C\oplus\sigma^*F_M\longrightarrow M,\qquad
(c,f)\longmapsto\varphi _0(c)+\varphi _1(f)
\tag{2.2}
$$

is an isomorphism.

A short sequence is admissible precisely when it is exact on underlying modules and on first filtered steps. The qualification is essential: without it, a filtered solution on a subobject need not extend. Book 53 proved that $T_{\mathrm{FL}}$ reverses admissible exact sequences and preserves length.

### 2.2 The finite-flat side

For finite-flat groups, kernels and quotients are interpreted in the fppf topology. A sequence

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0
\tag{2.3}
$$

is admitted when the first map identifies $\mathcal G'$ with the scheme-theoretic kernel and the second map is faithfully flat. Its coordinate-algebra sequence need not be a short exact sequence in the same order, since affine schemes reverse arrows. Fppf exactness is the invariant formulation.

Book 42 proved that the geometric generic-point functor is exact on (2.3). It also proved that a stable generic subgroup has a finite-flat schematic closure inside a supplied model. Over $W$ and $p>2$, Raynaud full faithfulness strengthens ambient uniqueness to abstract uniqueness of marked models.

### 2.3 The generic side

The generic fiber of a finite-flat $W$-group is finite étale because $K_0$ has characteristic zero. Hence

$$
\mathcal G\longmapsto\mathcal G(\overline K_0)
\tag{2.4}
$$

is a covariant exact functor to finite continuous $G_{K_0}$-modules. The finite étale--Galois correspondence recovers the generic group scheme from this module.

The functor of Book 53 is instead

$$
T_{\mathrm{FL}}(M)=
\operatorname{Hom}_{\mathrm{Fil},\varphi}
(M,\mathscr A_{\mathrm{cris},\infty}),
\tag{2.5}
$$

and is contravariant. Its normalization is

$$
T_{\mathrm{FL}}(\mathbf1_n)=\mathbf Z/p^n,\qquad
T_{\mathrm{FL}}(\mathbf1_n(1))=\mu_{p^n}(\overline K_0).
\tag{2.6}
$$

### 2.4 Why two reversals give covariance

Crystalline Dieudonné theory is contravariant: a group map $\mathcal G\to\mathcal H$ induces

$$
\mathbf D_{\mathrm{FL}}(\mathcal H)
\longrightarrow
\mathbf D_{\mathrm{FL}}(\mathcal G).
\tag{2.7}
$$

Applying $T_{\mathrm{FL}}$ reverses the arrow again. Thus the comparison sought in Chapter 6 has the type

$$
\mathcal G(\overline K_0)
\xrightarrow{\sim}
T_{\mathrm{FL}}(\mathbf D_{\mathrm{FL}}(\mathcal G)).
\tag{2.8}
$$

For the inverse construction, a map $M\to N$ must produce

$$
\mathcal G(N)\longrightarrow\mathcal G(M).
\tag{2.9}
$$

These directions will be checked first on the constant and multiplicative lines. They prevent a later quotient from being mistaken for a subgroup.

## 3. The filtered crystal of a finite-flat group

The special fiber of a finite-flat group has a Dieudonné crystal, but the special fiber alone does not determine its mixed-characteristic lift. The missing datum is a Hodge step inside the crystalline evaluation. This chapter constructs that step and proves that the resulting torsion module satisfies the strong-divisibility conditions of Book 53.

### 3.1 Crystalline extensions and the Hodge step

Let $\mathcal G/W$ be killed by $p^n$, and put $G=\mathcal G\times_Wk$. The contravariant crystalline Dieudonné crystal of $G$ assigns to a divided-power thickening $(U,T,\delta)$ the group of rigidified extensions of $G_U$ by the additive crystalline structure group. Book 52 established crystallinity, exactness, PD base change, and Cartier duality for this construction.

Evaluate on the canonical compatible thickenings $W_m\to k$, with $m\ge n$, and pass to the stable $p^n$-torsion quotient. Denote the resulting finite-length $W$-module by

$$
D(\mathcal G).
\tag{3.1}
$$

The lift $\mathcal G/W$ supplies a Hodge map from its own invariant
differentials:

$$
\omega_{\mathcal G}\longrightarrow D(\mathcal G).
\tag{3.2}
$$

Its image is denoted $F_{\mathcal G}$. Equivalently,
$F_{\mathcal G}$ is the kernel of the evaluation map to the Lie algebra
of the Cartier dual in the universal-extension sequence

$$
0\longrightarrow F_{\mathcal G}\longrightarrow D(\mathcal G)
\longrightarrow\operatorname{Lie}(\mathcal G^D)\longrightarrow0.
\tag{3.3}
$$

For a torsion group the terms need not be free. Formula (3.3) is the
degree-zero sequence of the conormal complex obtained from a smooth
two-term resolution; it is a strict sequence of finite $W$-modules, not
a claim that the displayed submodule is always a direct summand. This
variance is forced by the two endpoints. For
$\underline{\mathbf Z/p^n}$ one has $\omega_{\mathcal G}=0$, so the
Hodge step is zero. For $\mu_{p^n}$ one has
$\omega_{\mathcal G}=W/p^n$, so the Hodge step is the whole module.
Using $\omega_{\mathcal G^D}$ would interchange the constant and
multiplicative lines and would contradict (2.6).

We record why the conormal description supplies the free presentations
required in Book 53. Fppf locally on $W$, resolve the rigidified
extension functor defining the crystal by two smooth commutative formal
groups. On coordinate rings this is obtained by choosing finite sets of
generators for the augmentation ideals of the Hopf algebra of
$\mathcal G$ and of its dual, adjoining free primitive coordinates,
and then adjoining generators for the multiplication and
comultiplication relations. The first stage is formally smooth; the
second records the relations. Finite projectivity of the original Hopf
algebra makes the two resulting conormal modules finite projective.
Over the local ring $W$ they are free.

Applying rigidified crystalline extensions to this resolution gives a
strict two-term complex of finite free crystalline modules. Applying
the conormal functor gives its first filtered subcomplex. Its kernel is
$\omega_{\mathcal G}$, while Cartier duality identifies the quotient
with $\operatorname{Lie}(\mathcal G^D)$, proving (3.3). If the chosen
generators are enlarged, the added primitive coordinates form a split
contractible summand. Two choices are therefore dominated by their
union and give canonically isomorphic filtered cokernels. This is the
smooth-resolution calculation used below; it does not assume a
classification of mixed-characteristic lifts.

The construction is contravariant. A map $u:\mathcal G\to\mathcal H$ pulls rigidified extensions back and carries $F_{\mathcal H}$ into $F_{\mathcal G}$.

### 3.2 Frobenius divided on the Hodge step

The relative Frobenius of $G$ induces a $\sigma$-semilinear map

$$
\varphi _0:D(\mathcal G)\longrightarrow D(\mathcal G).
\tag{3.4}
$$

Its reduction kills invariant differentials. Consequently

$$
\varphi _0(F_{\mathcal G})\subset pD(\mathcal G)
\tag{3.5}
$$

at the free crystalline levels. Division before passage to the torsion quotient defines a second map

$$
\varphi _1:F_{\mathcal G}\longrightarrow D(\mathcal G),\qquad
\varphi _0|_{F_{\mathcal G}}=p\varphi _1.
\tag{3.6}
$$

One must define $\varphi _1$ at a torsion-free level. Cancelling $p$ directly in $D(\mathcal G)$ would not determine it. Independence of the chosen lift follows from the modified first filtration of Book 50: two lifts differ by an element whose Frobenius is divisible by one additional $p$, so their quotients agree modulo $p^n$.

### 3.3 Strong divisibility

The key point is that the two divided Frobenius images generate. This is the mixed-characteristic reflection of the special-fiber relations between Frobenius and Verschiebung.

**Proposition 3.1 (strong divisibility of the group crystal).** The quadruple

$$
\mathbf D_{\mathrm{FL}}(\mathcal G)
=(D(\mathcal G),F_{\mathcal G},\varphi _0,\varphi _1)
\tag{3.7}
$$

is an admissible torsion divided filtered module of weights $[0,1]$.

**Proof strategy.** Resolve the crystalline extension sheaf locally by
smooth commutative formal groups, so that it is represented by a
two-term complex of finite free crystalline modules. The conormal
sequences identify the reduction of the Hodge step with
$\operatorname{im}V=\ker F_{\mathrm D}$. The relation
$F_{\mathrm D}V=p$ then proves surjectivity of the normal map modulo
$p$; equal ranks and Nakayama finish the argument.

**Proof.** The smooth-resolution construction of the crystalline
Dieudonné crystal gives finite free modules $L_1,L_0$ and a strict map
$L_1\to L_0$ on their Hodge submodules; its cokernel is (3.1).
Changing the smooth resolution gives a canonically quasi-isomorphic
strict presentation by crystallinity and PD descent.

On a free term $L$, the conormal sequence for relative Frobenius
identifies the reduction of the Hodge submodule with the Verschiebung
direction. Thus, for the liftable free presentation,

$$
\overline F=\operatorname{im}V=\ker F_{\mathrm D}.
\tag{3.8}
$$

This equality comes from the Hodge conormal sequence of the supplied
finite-flat lift; it is not asserted for an arbitrary filtration on a
finite Dieudonné module. The relation
$F_{\mathrm D}V=VF_{\mathrm D}=p$ before reduction controls the divided
map on this Hodge direction.

Choose a complement $L=C\oplus F$ and reduce the normal map

$$
\Psi:\sigma^*C\oplus\sigma^*F\to L,\qquad
(c,f)\mapsto\varphi _0(c)+\varphi _1(f)
\tag{3.9}
$$

modulo $p$. Let $\bar y\in L/pL$, choose a lift $y\in L$, and choose
$f\in F$ lifting $V\bar y\in\overline F$. At the torsion-free
crystalline level there is a $z\in L$ with

$$
f=Vy+pz.
$$

Applying Frobenius and dividing on $F$ gives

$$
\overline{\varphi _1(f)}
=\bar y+\overline{\varphi _0(z)}.
$$

Write $z=c+f_0$ with $c\in C$ and $f_0\in F$. Since
$\varphi _0(F)\subset pL$, the last term is
$\overline{\varphi _0(c)}$. Hence every $\bar y$ is in the image of
$\overline\Psi$. Source and target have the same dimension, so
$\overline\Psi$ is an isomorphism. Nakayama makes $\Psi$ an isomorphism
over $W$.

The local free resolutions glue because crystalline extensions and the Hodge map satisfy fppf descent. They give a strict two-term free presentation of (3.7). Equations (3.5)--(3.6) descend through it, proving admissibility. $\square$

The proof also shows why an arbitrary filtration on the special-fiber Dieudonné module is not enough. It must be the Hodge filtration of a lift for (3.5) and the normal-map calculation to hold.

### 3.4 Torsion presentations and exactness

**Proposition 3.2.** A faithfully flat exact sequence of finite-flat groups

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0
\tag{3.10}
$$

induces an admissibly exact sequence

$$
0\to\mathbf D_{\mathrm{FL}}(\mathcal G'')
\to\mathbf D_{\mathrm{FL}}(\mathcal G)
\to\mathbf D_{\mathrm{FL}}(\mathcal G')\to0.
\tag{3.11}
$$

Moreover

$$
\ell_WD(\mathcal G)=\log_p|\mathcal G|.
\tag{3.12}
$$

**Proof.** Crystalline Dieudonné extensions are exact contravariantly
by Book 52. Apply the conormal complexes to (3.10), and simultaneously
apply them to its Cartier dual. The resulting two exact rows, joined by
(3.3), show that the underlying crystalline sequence and its Hodge
steps are exact in the displayed reversed order. Thus (3.11) is strict;
using invariant differentials of the dual alone would give the wrong
filtration. The length formula holds on the special fiber by finite
Dieudonné classification. Finite local freeness preserves group order
under specialization, so the same order is that of $\mathcal G$.
$\square$

The proposition implies compatibility with multiplication by $p^r$, kernels, and level reduction whenever the corresponding group sequence is faithfully flat exact.

The Cartier pairing is already compatible with the added Hodge step.
Indeed Book 52 identifies the crystals of $\mathcal G$ and
$\mathcal G^D$ by the crystalline evaluation pairing. The annihilator
of $\omega_{\mathcal G}$ under that pairing is the step complementary
to $\omega_{\mathcal G^D}$, and the conormal sequences show that the
two steps have complementary weights. The adjoint identities for
relative Frobenius and Verschiebung become the two divided-Frobenius
identities of Book 53. Consequently there is a functorial isomorphism

$$
\mathbf D_{\mathrm{FL}}(\mathcal G^D)
\simeq\mathbf D_{\mathrm{FL}}(\mathcal G)^\vee,
\tag{3.13}
$$

and the corresponding evaluation pairing is perfect. This fact is
proved here, before it is used to test injectivity of the period map in
Chapter 6.

## 4. The finite-flat solution functor

The generic realization of Book 53 takes solutions in a geometric
period ring. Essential surjectivity requires an integral model of that
finite solution module. We first represent the full solution sheaf for
free reductions, where normal coordinates control every equation, and
then use saturated closure for a general torsion object. The construction
is integral from the start.

### 4.1 Solutions as a sheaf

Let $M$ be an admissible torsion divided filtered module killed by
$p^n$. For a syntomic $W$-algebra $R$, let $\mathscr A_n(R)$ denote
the finite crystalline divided-power envelope attached to $R/pR$,
equipped with the modified first filtration and divided Frobenius of
Book 50. Define the solution sheaf

$$
\mathscr S_M(R)=
\operatorname{Hom}_{\mathrm{Fil},\varphi}
(M,\mathscr A_n(R)).
\tag{4.1}
$$

Addition in the target makes this an abelian-group-valued sheaf. A morphism $M\to N$ induces $\mathscr S_N\to\mathscr S_M$. The construction is independent of $n$ once $p^nM=0$, because the transition maps on the modified filtered period terms are surjective and the equations commute with reduction.

At a geometric generic point, (4.1) is precisely
$T_{\mathrm{FL}}(M)$. For free reductions we represent this whole
sheaf by coordinates. For a general torsion object we construct the
unique finite-flat model of its geometric solution module by schematic
closure. This distinction avoids the false inference that a raw kernel
of finite-flat groups is automatically flat.

### 4.2 Normal coordinates

First take $M=L/p^nL$ with $L$ free. Choose $L=C\oplus F$ and bases $e_1,\ldots,e_d$ adapted to the two summands. Put $\epsilon_i=0$ on $C$ and $\epsilon_i=1$ on $F$. The normal map has an invertible matrix $U\in\operatorname{GL}_d(W)$:

$$
(\varphi _{\epsilon_1}e_1,\ldots,
\varphi _{\epsilon_d}e_d)
=(e_1,\ldots,e_d)U.
\tag{4.2}
$$

A solution is a row vector $x=(x_i)$ with $x_i$ in the $\epsilon_i$th filtered period term and satisfying

$$
(\varphi _{\epsilon_i}x_i)_i=xU.
\tag{4.3}
$$

The matrix $U$ is invertible integrally. This is what permits simultaneous solution of all coordinates. Changing a complement multiplies (4.3) by an integral block-unipotent matrix, so the sheaf does not depend on the normal decomposition.

### 4.3 The integral coordinate lemma

The following lemma is the representability engine. It is the scheme-theoretic refinement of the small-weight lifting calculation in Book 53.

**Lemma 4.1 (integral coordinate lemma).** Let
$U\in\operatorname{GL}_d(W)$ and let $\epsilon_i\in\{0,1\}$. The
sheaf of solutions of (4.3) for the free reduction $L/p^nL$ is
represented by a finite locally free commutative $W$-group
$\mathcal H_n(L)$ of rank $p^{nd}$. Its coordinate algebra has,
syntomically locally, a basis indexed by

$$
X_1^{a_1}\cdots X_d^{a_d},\qquad 0\le a_i<p^n.
\tag{4.4}
$$

The construction commutes with reduction in $n$, with an integral change of normal basis, and with unramified extension of $W$.

**Proof strategy.** At level one, filter the coefficient and
divided-power layers and use the invertibility of $U$ to obtain a
coupled monic system. Weight-zero rows have Artin--Schreier-type linear
parts; weight-one rows allow a purely inseparable root initial form. In
either case the leading monomial in row $i$ is $Z_i^p$. Those relatively
prime leading monomials make the relations a monic Gröbner basis, so
they reduce every monomial to (4.4), and the associated graded proves
independence. Lift one $p$-adic digit at a time. The weight-one
coordinate is formed in the modified divided-power term before
reduction, so no division in a torsion algebra occurs.

**Proof.** Modulo $p$, choose additive coordinates on the weight-zero
terms and modified divided-power coordinates on the weight-one terms.
After the invertible change of relation generators given by $U$, and
after filtering the finite regular-immersion generators and their
divided monomials, the equations have the schematic forms

$$
Z_i^p+\ell_i(Z)=P_i(Z),
\qquad
Z_i^p+\ell_i'(Z)=Q_i(Z),
\tag{4.5}
$$

Here $Z=(Z_1,\ldots,Z_d)$, the $\ell_i$ and $\ell_i'$ are coupled
linear forms, and every term on the right has filtered degree strictly
below the leading term $Z_i^p$. In a weight-zero row the combined
linear part is the Artin--Schreier part determined by the invertible
normal matrix. In a weight-one row its relevant coefficient may
vanish; the atomic initial equation is then $Z_i^p=0$, exactly as in
the weight-one lifting calculation of Book 50. Thus (4.5) does not
claim that the special fiber of a weight-one factor is étale.
The logarithmic notation is used only inside the divided-power chart;
the descended atomic group is $\mu_p$, whose special fiber is
nonreduced.

Choose a monomial order refining the filtered degree. Each relation is
monic with leading monomial $Z_i^p$. These leading monomials are
pairwise relatively prime, so every $S$-polynomial reduces to zero;
the monic Buchberger argument works over the chart ring because no
leading coefficient is inverted. Thus the relations form a monic
Gröbner basis. Division expresses the chart algebra uniquely in the
monomials with $0\le a_i<p$, so those monomials are a basis. This
argument permits arbitrary coupling among the $Z_j$; it does not
triangularize $U$. The Hopf addition formulas respect the relations
because the Frobenius equations are additive in weight zero and
multiplicative before logarithm in weight one.

Suppose the chart algebra $A_r$ has been constructed through the first
$r$ digits. Write the next universal lift as $z+p^rw$. Substitution
into (4.3), division of the defect by $p^r$ at the torsion-free
crystalline level, and reduction modulo $p$ give the same coupled monic
system (4.5) in the new variables $w_1,\ldots,w_d$, with coefficients
in $A_r$. Therefore

$$
A_{r+1}=A_r[w_1,\ldots,w_d]/(R_{r,1},\ldots,R_{r,d}),
$$

where the $R_{r,i}$ have pairwise relatively prime leading monomials
$w_i^p$. The same monic Gröbner argument makes $A_{r+1}$ free of rank
$p^d$ over $A_r$, with basis
$w_1^{a_1}\cdots w_d^{a_d}$ for $0\le a_i<p$. Induction, followed by
the usual recombination of the $p$-adic digit variables into
$X_1,\ldots,X_d$, produces exactly the basis (4.4) and rank $p^{nd}$.

The group law is obtained by adding filtered Frobenius solutions; in a
weight-one chart this is the divided-power logarithm of multiplication.
The equations are stable under that law, so the descended algebra is a
Hopf algebra.

The transition algebra from one crystalline chart to another is
obtained by divided-power Taylor transport. On the associated graded
reduced-monomial basis its transition matrix is block triangular with
unit diagonal. Hence the finite free chart algebras, their Hopf maps,
and their identity sections satisfy effective syntomic descent. A
normal-basis change conjugates the equations and preserves the
reduced-monomial filtration. Witt base change carries $U$ and all the
divided-power polynomials to their scalar extensions. $\square$

The proof establishes local freeness, not just equality of geometric cardinalities. That distinction is indispensable for multiplicative and local--local special fibers.

### 4.4 Descent and independence of choices

For a general admissible torsion object killed by $p^n$, choose a strict
presentation

$$
0\to L_1\xrightarrow{a}L_0\to M\to0.
\tag{4.6}
$$

The quotient map factors strictly through $L_0/p^nL_0\twoheadrightarrow M$.
Its kernel is admissible: it is the strict quotient
$a(L_1)/p^nL_0$, with the induced filtered structure, and the closure
properties of the admissible category proved in Book 53 apply. Exactness
from that book therefore gives an injection of geometric
solution modules

$$
T_{\mathrm{FL}}(M)\lhook\joinrel\longrightarrow
T_{\mathrm{FL}}(L_0/p^nL_0).
\tag{4.7}
$$

The finite étale subgroup on the left therefore sits in the generic
fiber of the finite-flat group $\mathcal H_n(L_0)$ from Lemma 4.1.
Define

$$
\mathcal G(M)=
\overline{T_{\mathrm{FL}}(M)}^{\,\mathcal H_n(L_0)},
\tag{4.8}
$$

where the bar is schematic closure of the corresponding generic finite
étale subgroup. Book 42 proves that this closure is a finite locally
free closed subgroup.

At this point (4.8) appears to depend on the presentation. It does not:
two choices have the same marked generic group
$T_{\mathrm{FL}}(M)$, and Raynaud full faithfulness over $W$ applies
because $1<p-1$. The generic identity extends uniquely in both
directions, and the extensions are inverse by generic-fiber
faithfulness. The same argument extends every map induced on generic
solutions and proves the cocycle condition. Thus (4.8) is a functor,
well defined up to the unique isomorphisms appropriate to an
anti-equivalence. The closure construction, rather than the raw kernel
of a morphism between two finite-flat groups, is essential: Book 42
shows that a raw scheme-theoretic kernel can have vertical torsion.

## 5. Representability and exactness

The coordinate lemma handles free reductions. For a general torsion
object, taking the raw kernel attached to a strict presentation would be
unsafe: a generically correct kernel of finite-flat groups can have
vertical torsion. This chapter instead uses schematic closure and
Raynaud rigidity to prove finite local freeness, independence, and exactness
in the reversed direction.

### 5.1 Finite local freeness

**Theorem 5.1 (integral model of the solution module).** For every
$M\in\mathrm{MF}^{[0,1]}_{\mathrm{tor}}(W)$, the construction
$\mathcal G(M)$ is a finite locally free commutative $W$-group scheme
whose geometric generic points are canonically $T_{\mathrm{FL}}(M)$.
Moreover

$$
|\mathcal G(M)|=p^{\ell_W(M)}.
\tag{5.1}
$$

**Proof strategy.** Embed the generic solution module in the free
finite-flat solution group supplied by Lemma 4.1 and take schematic
closure. Saturation over the DVR proves flatness; Book 53's independent
length calculation computes the rank.

**Proof.** Construction (4.8) and the closure theorem of Book 42 give
finite local freeness. By definition its generic fiber is the finite
étale group attached to $T_{\mathrm{FL}}(M)$. Book 53 proves

$$
|T_{\mathrm{FL}}(M)|=p^{\ell_W(M)}.
\tag{5.2}
$$

A finite locally free group and its characteristic-zero generic fiber
have the same rank, so (5.1) follows. Independence of the embedding and
functoriality were proved after (4.8) by Raynaud full faithfulness. No
raw kernel has been declared flat, and the size formula is not being
used as a substitute for saturation: flatness comes first from
schematic closure. $\square$

### 5.2 The group law and generic fiber

Addition of filtered Frobenius morphisms defines the group law. In weight one, this additive law is the logarithm of multiplication in the period thickening, so the atomic object $\mathbf1_n(1)$ gives $\mu_{p^n}$, not an additive infinitesimal group. The inverse is negation in the logarithmic coordinate, corresponding to multiplicative inversion.

By the generic marking in (4.8), evaluation gives

$$
\mathcal G(M)(\overline K_0)
=T_{\mathrm{FL}}(M).
\tag{5.3}
$$

Both sides carry the same $G_{K_0}$-action because crystalline Taylor transport commutes with Galois. Since $\mathcal G(M)_{K_0}$ is finite étale, (5.3) identifies its entire generic fiber with the finite étale group attached to $T_{\mathrm{FL}}(M)$.

### 5.3 Exact sequences

**Theorem 5.2 (exactness of the finite-flat solution functor).** If

$$
0\to M'\to M\to M''\to0
\tag{5.4}
$$

is admissibly exact, then

$$
0\to\mathcal G(M'')\to\mathcal G(M)\to\mathcal G(M')\to0
\tag{5.5}
$$

is faithfully flat exact.

**Proof.** Book 53 gives the reversed exact sequence of generic
solution modules. Functoriality of (4.8) extends its two maps uniquely
to the three finite-flat models. Close the generic first term inside
$\mathcal G(M)$. Its marked model is uniquely isomorphic to
$\mathcal G(M'')$, so the first map in (5.5) is a finite-flat closed
immersion. The represented quotient by this closure has generic module
$T(M')$. Raynaud uniqueness identifies that quotient with
$\mathcal G(M')$, and the quotient map is faithfully flat. Hence (5.5)
is finite-flat exact. $\square$

### 5.4 Length and order

The equality (5.1) is the integral form of the generic calculation

$$
|T_{\mathrm{FL}}(M)|=p^{\ell_W(M)}
\tag{5.6}
$$

from Book 53. For free reductions, Lemma 4.1 independently gives the
same reduced-monomial rank. For a general object, saturation supplies
flatness and (5.6) supplies the rank. Thus no connected component is
lost, and no geometric special-fiber point count is used.

For the two atomic lines,

$$
\mathcal G(\mathbf1_n)=\underline{\mathbf Z/p^n},\qquad
\mathcal G(\mathbf1_n(1))=\mu_{p^n}.
\tag{5.7}
$$

For a local--local rank-two object killed by $p$, the group has order $p^2$ although its geometric special fiber may have only the identity point. Formula (5.1), not point counting, controls the order.

## 6. The integral period comparison

We now have two ways to begin with a finite-flat group: take its geometric generic points directly, or take its filtered crystal and then solve the divided Frobenius equations. The comparison between them is the bridge that makes the classification geometric. It must include connected special fibers; checking only the constant and multiplicative endpoints would leave the local--local case open.

### 6.1 Evaluation on a geometric point

Let $\mathcal G/W$ be killed by $p^n$. A point $x\in\mathcal G(\overline K_0)$ pulls a rigidified crystalline extension of the special fiber back to the extension attached to the section $x$. Evaluation of its rigidification in the universal period thickening gives a map

$$
\operatorname{per}_{\mathcal G}(x):
\mathbf D_{\mathrm{FL}}(\mathcal G)
\longrightarrow\mathscr A_{\mathrm{cris},\infty}.
\tag{6.1}
$$

The Hodge part lands in $\operatorname{Fil}^1$, and naturality of crystalline Frobenius gives compatibility with $\varphi _0$ and $\varphi _1$. Thus (6.1) is an element of $T_{\mathrm{FL}}(\mathbf D_{\mathrm{FL}}(\mathcal G))$.

This construction is additive in $x$, Galois equivariant, contravariantly functorial in the crystal, and hence covariantly functorial in $\mathcal G$. It defines

$$
\operatorname{per}_{\mathcal G}:
\mathcal G(\overline K_0)
\longrightarrow
T_{\mathrm{FL}}(\mathbf D_{\mathrm{FL}}(\mathcal G)).
\tag{6.2}
$$

### 6.2 The two endpoints

For $\underline{\mathbf Z/p^n}$, the filtered crystal is the weight-zero line $\mathbf1_n$. Evaluation is the kernel identification

$$
\ker(1-\varphi:\mathscr A_n\to\mathscr A_n)
=\mathbf Z/p^n
\tag{6.3}
$$

of Book 50. Hence (6.2) is the identity after the standard normalization.

For $\mu_{p^n}$, the filtered crystal is $\mathbf1_n(1)$. A root of unity maps to its divided-power logarithm, and

$$
\ker(1-\varphi _1:\operatorname{Fil}^1\mathscr A_n
\to\mathscr A_n)=\mu_{p^n}.
\tag{6.4}
$$

Thus (6.2) is again an isomorphism. These calculations fix the Tate twist and exclude its inverse.

### 6.3 The local--local calculation

Over an algebraic closure of $k$, a local--local BT$_1$ factor of height two has a basis in which both Frobenius and Verschiebung are nilpotent and the Hodge step is neither an étale nor a multiplicative direct factor. Point counting on the special fiber is useless. Instead choose a normal basis of its lifted filtered module. Its solutions satisfy the coupled level-one system from Lemma 4.1.

**Lemma 6.1 (local--local period calculation).** Let $\mathcal H/W$ be a finite-flat group killed by $p$ whose special-fiber Dieudonné module is a local--local BT$_1$ of height two. Then (6.2) is an isomorphism.

**Proof.** After a faithfully flat unramified extension, choose a normal
basis of $D(\mathcal H)$ and a basis of its BT$_1$ Dieudonné module.
Evaluation sends a geometric generic point to the solution vector obtained
from its universal crystalline extension. Suppose this vector is zero.
For every $y\in\mathcal H^D(\overline K_0)$, compatibility of crystalline
evaluation with Cartier duality identifies

$$
\log_{\mathrm{PD}}\langle x,y\rangle_{\mathrm{Cart}}
$$

with the filtered period pairing of
$\operatorname{per}_{\mathcal H}(x)$ and
$\operatorname{per}_{\mathcal H^D}(y)$. It is therefore zero. The
weight-one fundamental sequence injects $\mu_p$ into the logarithmic
period kernel, so $\langle x,y\rangle_{\mathrm{Cart}}=1$ for every $y$.
The generic Cartier pairing is perfect, and hence $x=0$. Thus the period
map is injective.

The source has $|\mathcal H|=p^{\ell_WD(\mathcal H)}$ elements on the characteristic-zero geometric fiber. The target has the same number by the length formula of Book 53. Hence the injection is bijective. This cardinality argument is legitimate only after injectivity has been proved without counting special-fiber points. Faithfully flat descent removes the auxiliary residue-field extension. $\square$

The same pairing argument does not use the height-two hypothesis. The
lemma isolates the first case in which special-fiber points cannot test
injectivity, whereas Cartier duality on the characteristic-zero generic
fiber still can.

### 6.4 The comparison theorem

**Theorem 6.2 (integral period comparison for finite-flat groups).** For every finite-flat commutative $p$-group $\mathcal G/W$, the map

$$
\operatorname{per}_{\mathcal G}:
\mathcal G(\overline K_0)
\xrightarrow{\sim}
T_{\mathrm{FL}}(\mathbf D_{\mathrm{FL}}(\mathcal G))
\tag{6.5}
$$

is a functorial isomorphism of finite continuous $G_{K_0}$-modules. It commutes with exact sequences, Cartier duality, coefficient actions, and unramified base change.

**Proof strategy.** Prove injectivity through the perfect Cartier pairing
and the integral weight-one logarithm. Then compare orders using two
independently established length formulas. This treats étale,
multiplicative, mixed, and local--local groups uniformly.

**Proof.** Let $x$ lie in the kernel of (6.5). For every
$y\in\mathcal G^D(\overline K_0)$, compatibility of (6.2) with the
crystalline Cartier pairing gives

# $$\log_{\mathrm{PD}}\langle x,y\rangle_{\mathrm{Cart}}

\bigl\langle\operatorname{per}_{\mathcal G}(x),
\operatorname{per}_{\mathcal G^D}(y)\bigr\rangle_{\mathrm{FL}}
=0.
\tag{6.6}
$$

The injective first arrow in the weight-one fundamental sequence of
Book 50 now gives
$\langle x,y\rangle_{\mathrm{Cart}}=1$. The generic fibers are finite
étale and Cartier duality gives a perfect pairing on their geometric
points, so $x=0$. Thus (6.5) is injective.

By Proposition 3.2, the source has

$$
|\mathcal G(\overline K_0)|
=|\mathcal G|=p^{\ell_WD(\mathcal G)}.
$$

The target has the same order by the length theorem of Book 53.
Therefore (6.5) is bijective. The endpoint computations (6.3)--(6.4)
fix its normalization. Every operation used to define (6.2) is natural,
and the crystalline evaluation pairing is compatible with duality,
coefficients, and PD base change. Exact sequences commute by naturality;
unramified base change commutes with the evaluation construction. This
proves all stated compatibilities. $\square$

No classification of mixed-characteristic lifts is used in this proof.
The local--local case is covered by the same pairing argument rather than
by pretending that its special fiber has enough geometric points.

## 7. Essential surjectivity and the anti-equivalence

The two constructions are now available, and their generic realizations agree with the expected Galois modules. This chapter proves that they are quasi-inverse. The key rigidity input is specific and visible: over $W$, $e=1<p-1$, so a generic isomorphism of finite-flat $p$-groups extends uniquely and is integrally invertible.

### 7.1 The two comparison morphisms

For a finite-flat group $\mathcal G$, Theorem 6.2 and (5.3) identify the generic fibers of

$$
\mathcal G
\quad\text{and}\quad
\mathcal G(\mathbf D_{\mathrm{FL}}(\mathcal G)).
\tag{7.1}
$$

The identity under that identification is a generic isomorphism. Raynaud full faithfulness extends it uniquely to

$$
\eta_{\mathcal G}:\mathcal G
\xrightarrow{\sim}
\mathcal G(\mathbf D_{\mathrm{FL}}(\mathcal G)).
\tag{7.2}
$$

It is an isomorphism because its generic inverse extends as well, and the composites equal the identity by generic-fiber faithfulness.

For $M$ on the filtered side, apply $\mathbf D_{\mathrm{FL}}$ to $\mathcal G(M)$. Equations (5.3) and (6.5) give

$$
T_{\mathrm{FL}}(M)
\simeq
T_{\mathrm{FL}}(\mathbf D_{\mathrm{FL}}(\mathcal G(M))).
\tag{7.3}
$$

Full faithfulness of $T_{\mathrm{FL}}$ now applies legitimately because both objects in (7.3) have already been constructed. It produces a unique isomorphism

$$
\epsilon_M:
\mathbf D_{\mathrm{FL}}(\mathcal G(M))
\xrightarrow{\sim}M,
\tag{7.4}
$$

with the direction dictated by contravariance.

### 7.2 No circular use of full faithfulness

The logical order deserves explicit verification.

1. Lemma 4.1 constructs integral coordinate algebras for free reductions
   directly from the divided Frobenius equations.
2. Theorem 5.1 embeds every $T(M)$ in such a free solution group and
   takes its saturated finite-flat closure, producing $\mathcal G(M)$
   without declaring a raw kernel flat.
3. Theorem 6.2 compares an independently supplied group with its filtered crystal.
4. Only then does (7.3) place two existing filtered objects in the domain of Book 53's full-faithfulness theorem.

Thus full faithfulness proves that one already constructed comparison is integral; it is not used to assert the existence of $\mathcal G(M)$.

### 7.3 The equivalence theorem

**Theorem 7.1 (integral Fontaine--Laffaille equivalence).** Under (1.2), the functors

$$
\mathbf D_{\mathrm{FL}}:\mathrm{FF}_W^{\mathrm{op}}
\longrightarrow\mathrm{MF}^{[0,1]}_{\mathrm{tor}}(W)
\tag{7.5}
$$

and

$$
\mathcal G:\mathrm{MF}^{[0,1]}_{\mathrm{tor}}(W)^{\mathrm{op}}
\longrightarrow\mathrm{FF}_W
\tag{7.6}
$$

are quasi-inverse exact anti-equivalences. The unit and counit are (7.2) and (7.4). They satisfy

$$
\mathcal G(M)(\overline K_0)=T_{\mathrm{FL}}(M),\qquad
\ell_W(M)=\log_p|\mathcal G(M)|.
\tag{7.7}
$$

**Proof.** Propositions 3.2 and Theorem 5.2 prove exactness. The natural isomorphisms (7.2) and (7.4) prove that the composites are isomorphic to the identity. Their triangle identities may be checked after generic realization, where every map is the identity on the same solution module; faithfulness of generic fiber and of $T_{\mathrm{FL}}$ then proves the identities integrally. Formula (7.7) is (5.3) and (5.1). $\square$

### 7.4 Uniqueness and reconstruction

The theorem yields three distinct uniqueness statements.

- A divided filtered module determines a finite-flat group uniquely up to unique isomorphism.
- A finite-flat group determines its divided filtered module uniquely and functorially.
- A finite-flat generic representation over $K_0$ has a unique marked finite-flat model because $e<p-1$.

The third statement uses Raynaud rigidity and is stronger than the first two categorical assertions. Over a ramified base at the boundary, an equivalence with a richer linear category might still classify models while a generic representation admits several of them.

## 8. Which torsion representations are finite flat

The anti-equivalence can now identify the generic essential image without choosing matrices. This is the promised answer to the finite-flat torsion question: a representation is finite flat exactly when it is a low-weight Fontaine--Laffaille realization.

### 8.1 The intrinsic essential image

**Theorem 8.1 (finite-flat representation criterion).** For a finite continuous $p$-primary $G_{K_0}$-module $V$, the following are equivalent.

1. $V$ admits a finite-flat commutative model over $W$.
2. There exists $M\in\mathrm{MF}^{[0,1]}_{\mathrm{tor}}(W)$ with

   $$
   V\simeq T_{\mathrm{FL}}(M).
   $$

3. The finite étale $K_0$-group attached to $V$ extends to $\mathcal G(M)$ for a unique $M$ up to unique isomorphism.

**Proof.** If $V=\mathcal H(\overline K_0)$ for a finite-flat $\mathcal H$, Theorem 6.2 gives $V=T(\mathbf D_{\mathrm{FL}}(\mathcal H))$. Conversely, if $V=T(M)$, Theorem 5.1 and (5.3) make $\mathcal G(M)$ a model. Uniqueness follows from Theorem 7.1, or from Raynaud full faithfulness followed by filtered full faithfulness. $\square$

We denote this essential image by $\mathrm{Rep}^{\mathrm{ff}}_{\mathbf Z_p}(G_{K_0})$. Combining Theorems 7.1 and 8.1 gives an anti-equivalence

$$
\mathrm{MF}^{[0,1]}_{\mathrm{tor}}(W)^{\mathrm{op}}
\simeq
\mathrm{Rep}^{\mathrm{ff}}_{\mathbf Z_p}(G_{K_0}).
\tag{8.1}
$$

### 8.2 Subobjects and quotients

Let $U\subset T(M)$ be a $G_{K_0}$-stable subgroup. Close the corresponding finite étale subgroup inside $\mathcal G(M)$. Book 42 gives a finite-flat subgroup $\mathcal H$ and a finite-flat quotient. Applying $\mathbf D_{\mathrm{FL}}$ gives an admissible quotient

$$
M\twoheadrightarrow Q,\qquad T(Q)=U,
\tag{8.2}
$$

and an admissible subobject whose realization is $T(M)/U$. Both are unique.

This proves the converse that Book 53 deliberately did not claim: every stable subrepresentation of a realized object is realized by an admissible quotient, and every stable quotient is realized by an admissible subobject. The proof uses schematic closure and essential surjectivity, not full faithfulness alone.

### 8.3 Extensions

An extension of two finite-flat representations need not be finite flat merely because its endpoints are. The correct statement is exact.

**Proposition 8.2.** Let

$$
0\to V'\to V\to V''\to0
\tag{8.3}
$$

be a short exact sequence of finite $G_{K_0}$-modules. Then $V$ is finite flat if and only if there is an admissibly exact sequence

$$
0\to M''\to M\to M'\to0
\tag{8.4}
$$

with $T(M')=V'$ and $T(M'')=V''$ which realizes (8.3).

**Proof.** If $M$ exists, exactness of $T$ gives (8.3). If $V$ is finite flat, choose its unique model and close $V'$ inside it. The quotient sequence is finite-flat exact. Applying $\mathbf D_{\mathrm{FL}}$ yields (8.4). $\square$

Thus the category is closed under subquotients of a supplied middle object, but it is not asserted that every abstract class in $\operatorname{Ext}^1_G(V'',V')$ lies in the finite-flat subcategory.

### 8.4 Examples and nonexamples

The trivial module $\mathbf Z/p^n$ corresponds to $\mathbf1_n$ and the constant group. The cyclotomic module $\mu_{p^n}(\overline K_0)$ corresponds to $\mathbf1_n(1)$ and $\mu_{p^n}$. A nonsplit filtered extension between these lines gives a genuinely mixed finite-flat group and a nonsplit generic Galois extension in the reversed order.

A Kummer class of a unit of $W$ can give a finite-flat extension because its root torsor extends over $W$. The Kummer class of the uniformizer $p$ does not extend as a $\mu_{p^n}$-torsor: the equation $X^{p^n}=p$ is ramified and its total space is not a torsor under a finite-flat model over the closed fiber. Book 50 identified this as the elementary failure of surjectivity for the integral period map. Theorem 8.1 therefore does not say that every representation with the correct rational Hodge--Tate labels is finite flat.

## 9. Duality, pairings, and coefficients

An equivalence is useful in arithmetic only if it transports Cartier duality and endomorphisms integrally. The contravariant normalizations from Books 34 and 52--53 now meet in one commuting dictionary.

### 9.1 Cartier duality

For $M$ killed by $p^n$, let $M^\vee$ be the Cartier-normalized filtered Matlis dual of Book 53. Then

$$
T(M^\vee)=T(M)^\vee(1).
\tag{9.1}
$$

**Theorem 9.1.** There is a natural isomorphism

$$
\mathcal G(M^\vee)\simeq\mathcal G(M)^D.
\tag{9.2}
$$

**Proof.** Both groups have generic module $T(M)^\vee(1)$ by (9.1) and the generic Cartier-pairing formula of Book 42. Their marked generic fibers are therefore isomorphic. Raynaud full faithfulness extends the isomorphism uniquely. Equivalently, apply Theorem 7.1 to the crystalline Cartier-duality isomorphism $\mathbf D(\mathcal H^D)=\mathbf D(\mathcal H)^\vee$. $\square$

The atomic weights are exchanged: the constant group and the multiplicative group are Cartier dual.

### 9.2 Perfect pairings

A bilinear pairing of finite-flat groups into $\mu_{p^n}$ is the same as a map to a Cartier dual. Hence Theorem 7.1 gives a bijection between such pairings and divided filtered pairings

$$
M\times N\longrightarrow E_W(1).
\tag{9.3}
$$

Perfectness can be checked on any of the three sides. The adjoint map is an isomorphism integrally if and only if it is an isomorphism on generic points, by Raynaud's isomorphism lemma; it is an isomorphism on filtered modules if and only if its realization is, by Book 53.

Alternating means $\langle x,x\rangle=0$, not merely skew-symmetric. Although $p>2$ makes the two conditions equivalent for bilinear forms, retaining the intrinsic definition keeps polarization statements stable under change of coefficients.

### 9.3 Coefficient actions

Let $A$ be a finite commutative $\mathbf Z_p$-algebra. An $A$-action on any one of $M$, $\mathcal G(M)$, or $T(M)$ determines a unique action on the other two.

For $M$, this follows because $\mathcal G$ is a functor. For a generic action on a finite-flat group, each scalar endomorphism extends uniquely by Raynaud full faithfulness, and the ring identities extend because they hold generically. For an action on $T(M)$, Book 53's full faithfulness lifts each endomorphism to $M$. Commutativity removes the distinction between the right action produced by precomposition and a left action. For a noncommutative algebra, the opposite algebra must be retained.

Thus Theorem 7.1 restricts to coefficient-linear anti-equivalences without replacing the chosen model.

### 9.4 Determinants in height two

Let $A$ be finite local and let $V$ be free of rank two over $A$. A perfect alternating pairing

$$
V\times V\to A(1)
\tag{9.4}
$$

forces $\det V$ to be cyclotomic. If the pairing comes from the filtered side, it extends to a perfect Cartier pairing on $\mathcal G(M)$ by Section 9.2. Conversely, a perfect group-scheme pairing gives a self-duality $M\simeq M^\vee$ and the same determinant formula generically.

The determinant conclusion should not be obtained by invoking an unspecified exterior-power group scheme. It follows from the actual perfect pairing, whose integral representability has just been proved.

## 10. Unramified change of the ground field

The base $W(k)$ may be enlarged by extending the perfect residue field. Book 53 constructed a comparison map but deliberately did not assert that it was always an isomorphism. Essential surjectivity now supplies the missing integral control.

### 10.1 Base change of divided filtered modules

Let $k\subset k'$ be an extension of perfect fields, put

$$
W'=W(k'),\qquad K_0'=W'[1/p].
\tag{10.1}
$$

For $M$ with a strict free presentation, define

$$
M_{W'}=W'\otimes_WM,\qquad
F_{M_{W'}}=W'\otimes_WF_M,
\tag{10.2}
$$

and

$$
\varphi_i'(a\otimes m)=\sigma'(a)\otimes\varphi_i(m).
\tag{10.3}
$$

Flatness of $W'/W$ preserves the presentation and the normal isomorphism, so $M_{W'}$ is admissible. The construction is independent of the presentation and is exact.

### 10.2 Base change of finite-flat groups

**Theorem 10.1 (integral ground-field base change).** There is a canonical natural isomorphism

$$
\mathcal G(M)\times_WW'
\xrightarrow{\sim}
\mathcal G(M_{W'}).
\tag{10.4}
$$

Equivalently, for every finite-flat $\mathcal H/W$,

$$
\mathbf D_{\mathrm{FL},W'}(\mathcal H_{W'})
\simeq W'\otimes_W\mathbf D_{\mathrm{FL},W}(\mathcal H).
\tag{10.5}
$$

**Proof.** Crystalline Dieudonné theory commutes with PD base change, and the Hodge exact sequence commutes with flat base change. This proves (10.5), including both divided Frobenius maps. Apply the quasi-inverse $\mathcal G$ over $W'$ to obtain (10.4). Alternatively, Lemma 4.1 shows directly that the integral coordinate algebra and its reduced-monomial basis scalar-extend to $W'$, and schematic closure commutes with this flat extension of DVRs. $\square$

No tensor formula for Frobenius fixed points is used in this proof.

### 10.3 Base change of generic realization

Assume in this subsection that $k'/k$ is finite. Then $K_0'/K_0$ is
a finite unramified extension. Choose compatible embeddings of
algebraic closures, so $G_{K_0'}\subset G_{K_0}$. The map left open in
Book 53 is now an isomorphism:

**Corollary 10.2.** There is a natural $G_{K_0'}$-equivariant isomorphism

$$
T_{\mathrm{FL},K_0}(M)|_{G_{K_0'}}
\xrightarrow{\sim}
T_{\mathrm{FL},K_0'}(M_{W'}).
\tag{10.6}
$$

**Proof.** The left side is the geometric generic-point module of $\mathcal G(M)_{W'}$. By (10.4), that group is $\mathcal G(M_{W'})$, whose points are the right side by (5.3). $\square$

This proof explains why (10.6) is integral: it compares two finite-flat groups before taking points. It does not claim that the kernel of $1-\varphi_i$ commutes formally with scalar tensor product.

### 10.4 Transitivity and infinite residue extensions

For $k\subset k'\subset k''$, the base-change isomorphisms satisfy the
cocycle identity. It holds on crystalline evaluations by associativity
of tensor product and hence on groups by the anti-equivalence.

The integral formulas (10.4)--(10.5) remain valid for an arbitrary
extension of perfect fields, including an infinite one. Their proof is
the direct PD base-change proof of Theorem 10.1; it does not require the
false assertion that every Witt vector in $W(k')$ descends to a finite
residue subextension. By contrast, (10.6) is a restriction statement
for absolute Galois groups and is asserted here only for finite
unramified extensions. For a general infinite perfect extension,
$W(k')[1/p]$ need not embed in the chosen algebraic closure of $K_0$,
so there need not be a subgroup $G_{K_0'}\subset G_{K_0}$ to which one
could restrict.

In the finite case the Galois subgroup in (10.6) depends on compatible
embeddings, but a different choice conjugates both sides in the same
way.

## 11. Unramified descent

Base change is only half of functoriality. Arithmetic arguments often construct an object after an unramified extension and then descend it. The equivalence makes the descent datum visible on filtered modules, groups, and generic representations at once.

### 11.1 Semilinear descent data

Suppose $k'/k$ is finite Galois with group $\Delta$, and put $W'=W(k')$. A descent datum on $M'\in\mathrm{MF}_{\mathrm{tor}}^{[0,1]}(W')$ consists of isomorphisms

$$
c_\delta:\delta^*M'\xrightarrow{\sim}M'
\tag{11.1}
$$

preserving $F$, $\varphi_0$, and $\varphi_1$, and satisfying

$$
c_{\delta\epsilon}=c_\delta\circ\delta^*c_\epsilon.
\tag{11.2}
$$

Because $\delta$ commutes with Witt Frobenius, these conditions are type-correct. A datum on a finite-flat group or on its generic representation is defined analogously.

### 11.2 Effectivity

**Theorem 11.1 (unramified descent).** Descent data are effective on all three categories. More precisely:

1. a divided filtered $W'$-module with datum (11.1) is $W'\otimes_WM$ for a unique $M$;
2. a finite-flat $W'$-group with descent datum descends to a unique finite-flat $W$-group;
3. a finite-flat generic representation with compatible generic descent datum descends together with its integral model.

**Proof.** Affine faithfully flat descent applies to the finite Hopf
algebra of a group and preserves finite projectivity. The multiplication,
coproduct, unit, counit, antipode, and cocycle identities all descend.
This proves assertion 2.

For assertion 1, apply $\mathcal G$ over $W'$ to the filtered descent
datum. Contravariance reverses each arrow but not the cocycle after the
standard reindexing by $\delta^{-1}$, so it gives a descent datum on
$\mathcal G(M')$. Descend that group by assertion 2 to a finite-flat
group $\mathcal H/W$ and put $M=\mathbf D_{\mathrm{FL}}(\mathcal H)$.
The base-change isomorphism (10.5) and the upstairs anti-equivalence
identify $W'\otimes_WM$ with $M'$, including the original datum.
Uniqueness follows from faithful flatness. This argument also proves
that admissibility descends; it does not assume that an arbitrarily
chosen free presentation already carries compatible descent data.

For assertion 3, begin with an upstairs finite-flat model. Raynaud full
faithfulness over $W'$ extends every generic comparison in the descent
datum uniquely to the group. The cocycle holds integrally because it
holds generically and generic fiber is faithful. Apply assertion 2.
$\square$

### 11.3 Galois descent and invariants

When $|\Delta|$ is divisible by $p$, taking ordinary invariants is not exact. The descended module is the equalizer furnished by faithfully flat descent, not an assertion that every exact sequence remains exact after applying $(-)^\Delta$. If $|\Delta|$ is prime to $p$, averaging makes invariants exact and one may write

$$
M=(M')^\Delta
\tag{11.3}
$$

with the descended structures. In the general case, (11.3) still describes the underlying equalizer, but exactness must be checked after faithfully flat base change rather than by averaging.

### 11.4 Why ramified descent is excluded

If $K'/K_0$ is ramified, its valuation ring is not a Witt-vector scalar extension of $W$. The new absolute ramification index may satisfy $e'\ge p-1$. Generic morphisms between new upstairs models may then fail to extend, and the clean divided Frobenius category (2.1) no longer records the required ramification data.

Base-changing a supplied downstairs finite-flat group to a ramified extension is harmless as a group operation, but it does not identify all upstairs models with scalar extensions of Fontaine--Laffaille modules. No ramified essential-surjectivity or descent statement is made.

## 12. Integral change of coefficient rings

Ground-field extension changes the Witt base and its Frobenius. Coefficient extension is different: it enlarges a commuting endomorphism ring while leaving $W$ and $G_{K_0}$ fixed. Because the realization is contravariant, ordinary tensor product on filtered modules produces coextension of generic scalars. This chapter derives the correct formula rather than hiding the dual.

### 12.1 Restriction and coextension

Let $A\to B$ be a homomorphism of finite commutative $\mathbf Z_p$-algebras, and let $M$ carry an $A$-action commuting with its divided filtered structure. Restriction of scalars is literal: forget part of the action. It changes neither $M$, $\mathcal G(M)$, nor $T(M)$ as underlying objects.

Suppose now that $B$ is finite projective over $A$ and that $B\otimes_AM$ remains admissible. Currying gives

$$
T(B\otimes_AM)
\simeq\operatorname{Hom}_A(B,T(M)).
\tag{12.1}
$$

Indeed a filtered Frobenius map $B\otimes_AM\to\mathscr A_\infty$ is the same as an $A$-linear family, indexed by $B$, of maps from $M$. Frobenius acts trivially on the coefficient index. Formula (12.1) is canonical.

The right side is coinduction. There is no canonical isomorphism from it to $B\otimes_AT(M)$ unless $B$ has been identified with its $A$-dual.

### 12.2 The dual scalar operation

Put

$$
B^\vee=\operatorname{Hom}_A(B,A).
\tag{12.2}
$$

It is finite projective as an $A$-module and carries the natural
$B$-action $(b\lambda)(x)=\lambda(bx)$. It need not be projective as a
$B$-module unless the finite flat algebra has an additional Gorenstein
hypothesis. Define the **contravariant scalar extension** of $M$ by

$$
B\boxtimes_AM=B^\vee\otimes_AM.
\tag{12.3}
$$

The filtration and divided Frobenius act on the $M$ factor. Finite projectivity preserves strict presentations and normal decompositions.

**Proposition 12.1 (correct coefficient extension formula).** If $B$
is finite projective over $A$ and $B^\vee\otimes_AM$ is admissible,
then

$$
T(B\boxtimes_AM)
\xrightarrow{\sim}B\otimes_AT(M)
\tag{12.4}
$$

naturally as $B[G_{K_0}]$-modules.

**Proof.** By currying,

$$
T(B^\vee\otimes_AM)
=\operatorname{Hom}_A(B^\vee,T(M)).
$$

For the finite projective $A$-module $B$, evaluation gives the
canonical isomorphism

$$
B\otimes_AT(M)\xrightarrow{\sim}
\operatorname{Hom}_A(B^\vee,T(M)),\qquad
b\otimes t\mapsto(\lambda\mapsto\lambda(b)t).
$$

It commutes with Galois and coefficients. $\square$

Thus extension of a stable Galois lattice corresponds to dual scalar extension on the contravariant filtered side.

### 12.3 Finite flat coefficient change

**Theorem 12.2 (integral coefficient base change).** Let $A\to B$ be
finite flat, let $M$ be an admissible $A$-object, and assume that $M$
has a strict presentation whose free $W$-terms and filtered summands are
finite projective as $A$-modules. Then:

1. $B\boxtimes_AM$ is admissible and exact in $M$;
2. its finite-flat group has generic points $B\otimes_AT(M)$;
3. for a further finite flat $B\to C$, there is a canonical transitivity isomorphism

   $$
   C\boxtimes_B(B\boxtimes_AM)
   \simeq C\boxtimes_AM;
   \tag{12.5}
   $$

4. the construction commutes with unramified ground-field base change,
   while Cartier duality exchanges tensor extension and contravariant
   scalar extension:

   $$
   (B\boxtimes_AM)^\vee\simeq B\otimes_AM^\vee,
   \qquad
   (B\otimes_AM)^\vee\simeq B\boxtimes_AM^\vee.
   \tag{12.6}
   $$

**Proof.** A finite flat algebra is finite projective. As an
$A$-module, $B^\vee$ is therefore finite projective. It is a direct
summand of a finite free $A$-module, so tensoring the chosen presentation
with $B^\vee$ preserves its injections, its filtered exact sequences,
and finite $W$-freeness of its terms. The normal map is the tensor
product of an isomorphism with a projective module and remains an
isomorphism. This proves admissibility and exactness. The projectivity
hypothesis is what prevents a hidden Tor term; finite flatness of
$A\to B$ alone would not control an unrelated presentation of $M$.

Part 2 is Proposition 12.1 followed by Theorem 8.1. For transitivity, finite-projective duality gives

$$
C^\vee_A\simeq C^\vee_B\otimes_BB^\vee_A
\tag{12.7}
$$

as the adjoint form of
$\operatorname{Hom}_A(C,A)\simeq\operatorname{Hom}_B(C,\operatorname{Hom}_A(B,A))$.
Tensor with $M$.
Ground-field base change commutes because all coefficient modules are
constant for Witt Frobenius. Finally, tensor--Hom adjunction and
finite-projective biduality give

$$
\operatorname{Hom}_W(B^\vee\otimes_AM,E_W)
\simeq B\otimes_A\operatorname{Hom}_W(M,E_W),
$$

and the same calculation with $B$ and $B^\vee$ interchanged gives the
second identity in (12.6). The filtrations and divided Frobenius maps
are the adjoint ones of Book 53, so these underlying-module
isomorphisms are isomorphisms of divided filtered objects. $\square$

The theorem is fully integral. No rational trace pairing is used to erase $B^\vee$.

### 12.4 Trace self-duality and the different

If $B/A$ is finite étale, the trace pairing

$$
B\times B\to A,\qquad (x,y)\mapsto\operatorname{Tr}_{B/A}(xy)
\tag{12.8}
$$

is perfect and canonically identifies $B\simeq B^\vee$. In that case

$$
B\boxtimes_AM\simeq B\otimes_AM,
\tag{12.9}
$$

so the familiar tensor formula is correct.

For a ramified extension of coefficient DVRs, the trace dual is the inverse different:

$$
B^\vee\simeq\mathfrak D_{B/A}^{-1}.
\tag{12.10}
$$

It is an invertible $B$-module but need not equal $B$ as a distinguished lattice inside $B\otimes_A\operatorname{Frac}(A)$. Choosing a generator of the inverse different gives a noncanonical identification; changing the generator rescales the integral lattice by a unit. Formula (12.3) retains the canonical object and prevents a hidden different from entering coefficient base change.

## 13. Nonflat coefficient quotients

Arithmetic deformation problems reduce a stable lattice modulo open ideals. Such a quotient map is usually not flat, so Theorem 12.2 does not apply. Essential surjectivity supplies a different operation: the quotient on the generic side corresponds to a distinguished admissible subobject on the contravariant filtered side.

### 13.1 The admissible annihilator

Let $A$ be a finite commutative $\mathbf Z_p$-algebra acting on $M$, and let $I\subset A$ be an ideal. Define $M[I]_{\mathrm{adm}}$ by the requirement

$$
T(M[I]_{\mathrm{adm}})=T(M)/IT(M),
\tag{13.1}
$$

with the quotient map corresponding contravariantly to an admissible monomorphism

$$
M[I]_{\mathrm{adm}}\hookrightarrow M.
\tag{13.2}
$$

Existence is concrete. Take the finite-flat group $\mathcal G(M)$, form the schematic closure of $IT(M)$ in its generic fiber, and take the represented finite-flat quotient $\mathcal Q_I$. Then

$$
M[I]_{\mathrm{adm}}=\mathbf D_{\mathrm{FL}}(\mathcal Q_I).
\tag{13.3}
$$

The inclusion (13.2) comes from the quotient $\mathcal G(M)\to\mathcal Q_I$. Raynaud rigidity makes the construction independent of every presentation.

The notation is chosen deliberately. The object is killed by $I$, but it need not equal the set-theoretic submodule

$$
M[I]=\{m\in M:Im=0\}
\tag{13.4}
$$

with its induced filtration. The latter may fail to be admissible or to have the correct length.

### 13.2 The compatible-quotient theorem

**Theorem 13.1 (integral compatible quotients).** With the notation above:

1. $M[I]_{\mathrm{adm}}$ exists uniquely and is functorial in $A$-linear morphisms;
2. it is the terminal admissible $I$-killed subobject of $M$;
3. its generic realization and group are

   $$
   T(M[I]_{\mathrm{adm}})=T(M)/IT(M),
   \qquad
   \mathcal G(M[I]_{\mathrm{adm}})=\mathcal Q_I;
   \tag{13.5}
   $$

4. if $J\subset I$, the quotient map $T(M)/JT(M)\to T(M)/IT(M)$ corresponds to a canonical admissible monomorphism

   $$
   M[I]_{\mathrm{adm}}\hookrightarrow M[J]_{\mathrm{adm}};
   \tag{13.6}
   $$

5. formation of these objects commutes with unramified ground-field base change.

**Proof.** Construction (13.3) proves existence and (13.5). Uniqueness follows from the anti-equivalence. Let $N\hookrightarrow M$ be an admissible subobject killed by $I$. Contravariance gives a quotient $T(M)\twoheadrightarrow T(N)$. Since $I$ kills $T(N)$, this quotient factors uniquely through $T(M)/IT(M)$. Full faithfulness, now applied to the existing objects, gives a unique factorization

$$
N\longrightarrow M[I]_{\mathrm{adm}}\longrightarrow M,
$$

proving the terminal property. The same argument gives functoriality and (13.6). Schematic closure and finite-flat quotient commute with the faithfully flat unramified extension $W'/W$; alternatively apply Theorem 10.1 to the unique object characterized by (13.5). $\square$

This is the compatible-quotient statement missing from Book 53. It is not a claim that nonflat tensor product preserves a strict presentation.

### 13.3 Successive ideals and exact sequences

Let $J\subset I\subset A$. There is an exact generic sequence

$$
0\to IT(M)/JT(M)
\to T(M)/JT(M)
\to T(M)/IT(M)\to0.
\tag{13.7}
$$

All terms are finite flat as representations because they are subquotients of the supplied finite-flat middle term. Under the anti-equivalence, (13.7) becomes an admissibly exact sequence in reverse order. The first term is not generally $T(M)\otimes_A(I/J)$ without a flatness or Tor-vanishing hypothesis.

If $I=(a)$ is principal and multiplication by $a$ has constant kernel and cokernel on the relevant finite projective coefficient module, the admissible annihilator can often be computed as the ordinary kernel of $a$ on $M$. For $A=\mathbf Z/p^n$ and $I=(p^r)$, the strict level sequences of Book 53 give precisely this familiar calculation. The theorem, however, does not require principality.

### 13.4 Comparison with naive annihilators

An example explains the distinction. Let $A$ be a finite local ring with nonprincipal socle and let $M$ be free of rank one as an $A$-module before the divided filtered structure is imposed. The $A$-module $M[I]$ is the annihilator ideal $\operatorname{Ann}_A(I)$, while the generic quotient has underlying coefficient module $A/I$. These modules can have different presentations and need not be isomorphic.

The correct relation is dual. For the injective cogenerator

$$
E_A=\operatorname{Hom}_{\mathbf Z_p}(A,\mathbf Q_p/\mathbf Z_p),
\tag{13.8}
$$

one has

$$
\operatorname{Hom}_A(A/I,E_A)=E_A[I].
\tag{13.9}
$$

Contravariant Fontaine--Laffaille theory behaves like this Matlis duality. When $A$ is Gorenstein and a self-duality $A\simeq E_A$ has been fixed, annihilator and quotient may be identified; without that hypothesis and choice, (13.3) is the canonical construction.

## 14. Stable lattices and all finite quotients

A single torsion level is not a $p$-adic lattice. A lattice is an inverse system with exact transition maps, and compatible quotients by every open coefficient ideal must agree with one another. This chapter extracts the integral system supplied by the equivalence.

### 14.1 Compatible Fontaine--Laffaille systems

A **compatible Fontaine--Laffaille system** is a sequence $(M_n)_{n\ge1}$ with $p^nM_n=0$, together with admissibly exact sequences

$$
0\to M_n\xrightarrow{p^m}M_{m+n}\to M_m\to0
\tag{14.1}
$$

whose maps satisfy the evident associativity in three levels. Because $T$ is contravariant, (14.1) realizes as

$$
0\to T(M_m)\to T(M_{m+n})\to T(M_n)\to0.
\tag{14.2}
$$

After choosing the customary level labels, this is the coefficient sequence for reductions of one free $\mathbf Z_p$-lattice.

A finite free strongly divisible module $L$ supplies the system
$M_n=L/p^nL$. Conversely, use in (14.1) the quotient maps
$M_{n+1}\twoheadrightarrow M_n$ obtained by taking the first index to
be $1$. They are surjective, and associativity makes them an inverse
system. Put

$$
L=\varprojlim_nM_n
\tag{14.3}
$$

Choose a $k$-basis of $M_1$ and lift it successively through the
surjections. Exactness of (14.1) shows by induction that
$\ell_W(M_n)=n\dim_kM_1$ and that the resulting map
$W^{\dim_kM_1}\to L$ is an isomorphism modulo every $p^n$. Completeness
and separatedness make it an isomorphism. In particular $L$ is finite
free and $L/p^nL=M_n$; no unrelated choice of a free presentation at
each level is involved.

Strictness gives the same inverse system on $F_{M_n}$. Its limit $F_L$
and the limit of the quotients $M_n/F_{M_n}$ are finite free, and

$$
0\longrightarrow F_L\longrightarrow L\longrightarrow
\varprojlim_n(M_n/F_{M_n})\longrightarrow0
$$

is exact. Hence $F_L$ is a direct summand. The maps $\varphi_0$ and
$\varphi_1$ pass to the limit. After choosing a compatible complement,
their normal maps are inverse systems of isomorphisms; their limit is
therefore an isomorphism. Thus $L$ is strongly divisible and recovers
the original system.

### 14.2 Recovering a stable lattice

Define

$$
T_p(L)=\varprojlim_nT_{\mathrm{FL}}(L/p^nL)
\tag{14.4}
$$

where the transition $T(L/p^{n+1}L)\twoheadrightarrow T(L/p^nL)$ is
contravariantly induced by the strict injection
$L/p^nL\xrightarrow{p}L/p^{n+1}L$. The exact sequences (14.2) show
inductively that the inverse limit is $p$-torsion-free and complete,
with a free rank-$\operatorname{rank}_WL$ reduction modulo every
$p^n$. Topological Nakayama therefore makes $T_p(L)$ finite free of
that rank, and

$$
T_p(L)/p^nT_p(L)
\simeq T_{\mathrm{FL}}(L/p^nL).
\tag{14.5}
$$

Continuity follows because every finite quotient is continuous and the action on the inverse limit is continuous for the $p$-adic topology.

Conversely, suppose $T$ is a finite free $\mathbf Z_p$-module with
continuous $G_{K_0}$-action and every $T/p^nT$ is finite flat. Theorem
8.1 gives a unique $M_n$ realizing each quotient. The injection and
quotient maps in

$$
0\longrightarrow T/p^mT\xrightarrow{p^n}
T/p^{m+n}T\longrightarrow T/p^nT\longrightarrow0
$$

lift uniquely by full faithfulness. Theorem 8.1 applied to the supplied
finite-flat middle term, followed by exactness of the anti-equivalence,
turns these into (14.1); the identities among three levels lift because
$T_{\mathrm{FL}}$ is faithful. The preceding inverse-limit argument
then gives a unique free strongly divisible $L$, and (14.5) identifies
$T$ with $T_p(L)$.

**Theorem 14.1 (stable-lattice equivalence).** Finite free strongly divisible $W$-modules of weights $[0,1]$ are anti-equivalent to finite free $\mathbf Z_p$-lattices $T$ for which every quotient $T/p^nT$ is finite flat. The equivalence commutes with duality and unramified ground-field base change.

**Proof.** The constructions above are inverse at every finite level. A morphism of inverse systems is determined levelwise; full faithfulness at each level and completeness of finite free modules lift it uniquely to $L$. Duality and base change commute levelwise and hence after inverse limits. $\square$

The rank-one consequence needed later can be read without introducing a
$\mathbf C_p$ comparison theorem.

**Proposition 14.2 (finite-flat rank-one characters are locally algebraic).**
Let $\mathcal O$ be the integers of a finite extension of $\mathbf Q_p$, and let

$$
T=\mathcal O(\xi)
$$

be a free rank-one $\mathcal O$-representation of $G_{K_0}$. Suppose that the quotients
$T/\varpi^nT$ admit one coefficient-linear compatible finite-flat tower over $W$ for all
$n$. Then $\xi$ is locally algebraic. More precisely, after enlarging the coefficient
field so that all embeddings $\tau:K_0\hookrightarrow\overline{\mathbf Q}_p$ are visible,
there are $h_\tau\in\{0,1\}$ such that on an open subgroup of $\mathcal O_{K_0}^{\times}$
the character $u\mapsto\xi(\operatorname{rec}_{K_0}(u))$ attached to $\xi$ by arithmetic
local reciprocity is

$$
u\longmapsto\prod_\tau\tau(u)^{-h_\tau}.                 \tag{14.6a}
$$

The exponents are negative, not positive: arithmetic reciprocity sends a unit $u$ to the
automorphism acting on the Lubin--Tate torsion tower by $[u^{-1}]$, by Book 5,
Proposition 10.1. This is the whole of the convention freedom in (14.6a). The integers
$h_\tau$ are read off the Hodge steps and are themselves convention-free; only the overall
sign of the exponents depends on the normalization of reciprocity, and it changes for all
$\tau$ at once if one replaces $\operatorname{rec}_{K_0}$ by the geometric normalization
$\operatorname{rec}_{K_0}^{-1}$. Book 5 fixes the arithmetic normalization, and (14.6a) is
stated in it.

In particular, if $K_0/\mathbf Q_p$ is unramified and $\xi$ is the restriction of a
character of $G_{\mathbf Q_p}$, all the $h_\tau$ are equal; on inertia it is therefore, up
to finite order, either the trivial character, when every $h_\tau=0$, or the cyclotomic
character, when every $h_\tau=1$. The second identification is exactly the negative sign in
(14.6a): the right-hand side becomes $N_{K_0/\mathbf Q_p}(u)^{-1}$, which is the value of
the $p$-adic cyclotomic character on $\operatorname{rec}_{K_0}(u)$ in the arithmetic
normalization of Book 5.

**Proof.** Theorem 14.1, with the coefficient action retained as in Chapter 13, gives a
coefficient-linear strongly divisible lattice $L$. Enlarge the coefficient field so that
$R_{\mathcal O}[1/p]$ splits, and write its idempotent factors as $L_\tau$. Each $L_\tau$ is
a line, Frobenius carries $L_\tau$ to $L_{\varphi\tau}$, and the first Hodge step on that
line is either zero or the whole line; call the alternative $h_\tau=0$ or $1$. Choose
generators $e_\tau$. The divided Frobenius equations then have the form

$$
\varphi_{h_\tau}(e_\tau)=a_\tau e_{\varphi\tau},
\qquad a_\tau\in\mathcal O^\times.                 \tag{14.6b}
$$

The product of the $a_\tau$ around the Frobenius cycle changes only the value on a
uniformizer, hence is an unramified character. After dividing by it, (14.6b) is the tensor
product, over those $\tau$ with $h_\tau=1$, of the cyclic rank-one display having one
weight-one factor and weight zero at the other embeddings.

The generic points of that one-step display can be calculated at every finite level from the
two atomic lines of Book 53, Sections 4.1--4.2, together with the two fundamental syntomic
sequences of Book 53, Section 5.3, namely (5.6) and (5.7) there,

$$
0\to\mathbf Z/p^n\to\mathscr A_n\xrightarrow{\ 1-\varphi\ }\mathscr A_n\to0,
\qquad
0\to\mu_{p^n}\to\mathscr F^1_n\xrightarrow{\ \iota_n-\varphi _1\ }\mathscr A_n\to0 :
$$

one iterates the ordinary Frobenius equation of (5.6) through the weight-zero factors and
applies the divided Frobenius equation of (5.7) at the single weight-one factor. This step
is the heart of the proposition, and it is the only place where the embedding is actually
pinned down, so we carry it out in full.

_Strategy._ Three things must happen. First, the level-$n$ solution system of the one-step
display is a chain: the value of a solution at one embedding determines its value at the
next through the Frobenius equation there, and running once around the Frobenius cycle
returns to the embedding one started from. Eliminating the intermediate values leaves a
single equation in the single unknown attached to the weight-one embedding, and that
equation iterates Frobenius $f$ times against exactly one division by $p$. For $f=1$ it is
literally the weight-one equation of (5.7), whose solutions are $\mu_{p^n}$; in general it
is the height-$f$ analogue, which is the torsion equation of a one-dimensional formal
$\mathcal O_{K_0}$-module of height $f$. Second, the surviving equation does not remember
which embedding carried the weight: the equation, its solution module, and the Galois action
on that module are literally the same for all choices, and the chosen embedding enters only
through the formula relating the coefficient action to multiplication inside the period
module. This reduces the whole question to one universal character. Third, that character is
computed by exhibiting a single display of the required shape whose realization is known
independently, namely the $p$-power torsion of the Lubin--Tate formal
$\mathcal O_{K_0}$-module of Book 5, Chapter 6, whose Hodge step is read off its cotangent
module and turns out to sit at the identity embedding. The three steps together give the
identification for every embedding, with no period decomposition and no Sen operator.

_Notation, and the direction of the cycle._ The proposition concerns a $K_0$ with finitely
many embeddings, so $k$ is finite; write

$$
f=[K_0:\mathbf Q_p],\qquad q=|k|=p^f,\qquad \sigma^f=\operatorname{id}\ \text{on}\ W.
$$

Two actions of $W$ are in play, and it is worth separating them notationally for the length
of this computation: write $a\cdot x$ for the structural action of $a\in W$ on the filtered
module and $c\ast x$ for the action of $c\in W$ through the coefficients. By definition
$L_\tau$ is the summand on which

$$
a\cdot x=\tau(a)\ast x
\qquad(a\in W).
$$

For $x\in L_\tau$, semilinearity of $\varphi$ over the structural action and its linearity
over the coefficients give

$$
a\cdot\varphi(x)=\varphi\bigl(\sigma^{-1}(a)\cdot x\bigr)
=\varphi\bigl(\tau(\sigma^{-1}(a))\ast x\bigr)
=\tau\bigl(\sigma^{-1}(a)\bigr)\ast\varphi(x),
$$

so $\varphi(L_\tau)\subseteq L_{\tau\circ\sigma^{-1}}$. The symbol $\varphi\tau$ in (14.6b)
therefore means

$$
\varphi\tau=\tau\circ\sigma^{-1},
\tag{14.6c}
$$

and, since $\sigma$ generates $\operatorname{Gal}(K_0/\mathbf Q_p)$, the $f$ embeddings form
a single $\varphi$-cycle: $\varphi^j\tau=\tau$ exactly when $f\mid j$.

Because $K_0/\mathbf Q_p$ is unramified it is Galois, so every $\tau$ has image $K_0$ and
each atomic factor of the tensor decomposition is already defined over the coefficient ring
$W$ itself. By Theorem 12.2(2), its realization over the larger $\mathcal O$ is
$\mathcal O\otimes_W(-)$ applied to its realization over $W$, which does not change the
character, only the ring in which its values are read. We may therefore compute one atomic
factor with $\mathcal O=W$. Then each line $L_\tau=W\cdot e_\tau$ is free of rank one for the
structural action as well, because $\tau$ is an automorphism of $W$, and the two actions are
related by $c\ast e_\tau=\tau^{-1}(c)\cdot e_\tau$.

Finally, replacing $e_\tau$ by $c_\tau e_\tau$ with $c_\tau\in W^\times$ replaces $a_\tau$ by
$c_\tau a_\tau c_{\varphi\tau}^{-1}$, so the product $\prod_\tau a_\tau$ around the cycle is
the only invariant of the collection $(a_\tau)$. That product is the unramified character
already divided out, so we may and do take $a_\tau=1$ for every $\tau$.

_The level-$n$ equations._ Fix the atomic factor whose weight-one embedding is $\tau_0$ and
list the cycle as $\tau_j=\varphi^j\tau_0$, so that $\tau_f=\tau_0$ and
$\tau_1,\dots,\tau_{f-1}$ are the weight-zero embeddings. The display is

$$
F_L=W\cdot e_{\tau_0},
\qquad
\varphi _1(e_{\tau_0})=e_{\tau_1},
\qquad
\varphi _0(e_{\tau_j})=e_{\tau_{j+1}}\quad(1\le j\le f-1),
$$

together with $\varphi _0(e_{\tau_0})=p\varphi _1(e_{\tau_0})=pe_{\tau_1}$. Put
$M_n=L/p^nL$. By Book 53, Section 5.2, a solution is a pair of $W$-linear maps
$s_0:M_n\to\mathscr A_n$ and $s_1:F_{M_n}\to\mathscr F^1_n$ subject to $\iota_ns_1=s_0|_{F_{M_n}}$
and to the two Frobenius identities of (5.5), written there with the letter $f$, which we
have reserved for the degree. Write

$$
x_j=s_0(e_{\tau_j})\in\mathscr A_n,
\qquad
y=s_1(e_{\tau_0})\in\mathscr F^1_n .
$$

The structural equation, the divided Frobenius equation at $\tau_0$, and the ordinary
Frobenius equations at the weight-zero embeddings become, in that order,

$$
x_0=\iota_n(y),
\qquad
x_1=\varphi _1(y),
\qquad
x_{j+1}=\varphi(x_j)\quad(1\le j\le f-1).
\tag{14.6d}
$$

The one remaining condition, $s_0\varphi _0=\varphi s_0$ at $\tau_0$ itself, reads
$p\,x_1=\varphi(x_0)$; it is automatic, being the finite-level form
$\varphi\circ\iota_n=p\varphi _1$ of the relation (5.4). Nothing else is imposed.

Now iterate. The last group of equations in (14.6d) is the weight-zero equation of (5.6)
written as a transition, and running it from $j=1$ to $j=f-1$ carries $x_1$ around the
weight-zero part of the cycle back to $x_f=x_0$:

$$
x_0=x_f=\varphi^{f-1}(x_1)=\varphi^{f-1}\bigl(\varphi _1(y)\bigr).
$$

Comparing with $x_0=\iota_n(y)$ leaves a single equation in a single unknown:

$$
\iota_n(y)=\varphi^{f-1}\bigl(\varphi _1(y)\bigr),
\qquad y\in\mathscr F^1_n .
\tag{14.6e}
$$

Conversely every $y$ satisfying (14.6e) defines a solution: put $x_1=\varphi _1(y)$, define
$x_2,\dots,x_{f-1}$ by the transitions, and put $x_0=\iota_n(y)$; all the conditions above
then hold. The Galois action on solutions is $(gs)(m)=g(s(m))$ by Book 53, (6.3), and
$\iota_n,\varphi,\varphi _1$ commute with $G_{K_0}$, so evaluation at $e_{\tau_0}$ is an
isomorphism of $G_{K_0}$-modules

$$
T_{\mathrm{FL}}(M_n)\xrightarrow{\ \sim\ }
\Sigma_n:=\ker\bigl(\iota_n-\varphi^{f-1}\varphi _1:
\mathscr F^1_n\to\mathscr A_n\bigr),
\qquad
s\longmapsto s_1(e_{\tau_0}).
\tag{14.6f}
$$

Equation (14.6e) is what the two fundamental sequences deliver, and it has exactly the shape
of the level-$n$ torsion equation of a one-dimensional formal $\mathcal O_{K_0}$-module of
height $f$. Three features show this; the identification itself is completed below.

It is the height-$f$ analogue of the weight-one equation. For $f=1$ it is literally
$\iota_n(y)=\varphi _1(y)$, whose kernel is $\mu_{p^n}$ by (5.7), so that (14.6f) recovers
(4.3) and the normalization (2.6); and $\mu_{p^\infty}$ is the torsion tower of the
Lubin--Tate module of $\mathbf Q_p$ for the uniformizer $p$.

Next, combining (14.6e) with $\varphi\circ\iota_n=p\varphi _1$ gives

$$
\varphi^f(x_0)=\varphi^{f-1}\bigl(\varphi\iota_n(y)\bigr)
=p\,\varphi^{f-1}\bigl(\varphi _1(y)\bigr)=p\,x_0 .
$$

One trip around the Frobenius cycle multiplies the solution by $p$: the single factor $p$ is
contributed by the one division performed by divided Frobenius at $\tau_0$, and the $f-1$
undivided steps are contributed by the weight-zero factors. For $f=1$ this is the period
relation $\varphi(t)=pt$ of Book 53, Section 5.2, so $\varphi^f=p$ is its height-$f$ form,
and it is the same bookkeeping as in Book 5's series for the uniformizer $p$ over
$\mathcal O_{K_0}=W$,

$$
\lambda(T)=pT+T^{q},
$$

in which the exponent $q=p^f$ is the $f$-fold iterate of the $p$-power map and the linear
term $pT$ is the single correction by $p$: at level one the torsion equation of Book 5,
Section 6.3 reads $T^{q}=-pT$, one $q$-power against one factor of $p$. Since $\varphi$
reduces to the $p$-power map modulo $p$, that is the same balance which (14.6e) exhibits.
The identification is not asserted from this resemblance; it is proved below.

Finally the count agrees: Book 53, Proposition 6.1 gives
$|\Sigma_n|=p^{\ell_W(M_n)}=p^{nf}=q^n$, which is exactly the order of the $p^n$-torsion of
that formal module, by the parametrization of its torsion by $W/p^n$ in Book 5,
Section 6.3.

_The module structure, and where $\tau_0$ enters._ The map $\iota_n$ is $W$-linear and
$\varphi$ and $\varphi _1$ are $\sigma$-semilinear, so $\varphi^{f-1}\varphi _1$ is
$\sigma^f$-semilinear, that is, $W$-linear, because $\sigma^f=\operatorname{id}$ on $W$.
Hence $\Sigma_n$ is a $G_{K_0}$-stable $W/p^n$-submodule of $\mathscr F^1_n$ for
multiplication inside the period module. The coefficient action transported by (14.6f) is a
twist of that multiplication: writing $c\ast s$ for the coefficient action on solutions,
which is precomposition with $c\ast(-)$ on $M_n$,

$$
(c\ast s)_1(e_{\tau_0})=s_1\bigl(c\ast e_{\tau_0}\bigr)
=s_1\bigl(\tau_0^{-1}(c)\cdot e_{\tau_0}\bigr)
=\tau_0^{-1}(c)\,s_1(e_{\tau_0}),
$$

since $s_1$ is linear for the structural action. Thus, under (14.6f),

$$
c\ast y=\tau_0^{-1}(c)\,y
\qquad(c\in W),
\tag{14.6g}
$$

the right-hand side being multiplication inside the $W$-algebra $\mathscr F^1_n$.

This is the decisive point. Neither the equation (14.6e), nor the module $\Sigma_n$, nor the
Galois action on it, nor the transition maps of (14.4), which become $y\mapsto py$, mention
$\tau_0$ anywhere: they are the same for every choice of the weight-one embedding. The
embedding enters only through (14.6g), which says that the coefficient action is the natural
multiplication composed with $\tau_0^{-1}$. Moreover $T_p(L)=\varprojlim_n\Sigma_n$ is free
of rank $f$ over $\mathbf Z_p$ by (14.5), is $p$-torsion free, and carries an action of the
discrete valuation ring $W$ whose uniformizer is $p$; a finitely generated torsion-free
module over a discrete valuation ring is free, so $T_p(L)$ is free of rank one over $W$ and
Galois acts on it through a character

$$
\psi:G_{K_0}\longrightarrow W^\times,
\qquad g(y)=\psi(g)\,y ,
$$

for multiplication inside the period module. By the preceding paragraph $\psi$ does not
depend on $\tau_0$. Comparing multiplication with the coefficient action through (14.6g),
the character realized by the atomic factor whose weight-one embedding is $\tau_0$ is

$$
\xi_{\tau_0}=\tau_0\circ\psi .
$$

The question of which embedding indexes the answer has thereby been reduced to the
computation of the single character $\psi$, and one instance settles it.

_Identification of $\psi$._ Apply Book 5, Chapter 6 to the field $K_0$, its ring of integers
$\mathcal O_{K_0}=W$, and the uniformizer $p$, with the same series
$\lambda(T)=pT+T^{q}$ of Section 6.3 there. Let $F_\lambda$ be the resulting formal $W$-module of Book 5,
Theorem 6.1, let $\omega_n$ be a compatible system of primitive $p^n$-torsion points, and
let $\chi_{\mathrm{LT}}:G_{K_0}\to W^\times$ be the Lubin--Tate character, defined by
$g(\omega_n)=[\chi_{\mathrm{LT}}(g)]_\lambda(\omega_n)$; Book 5, Section 6.3 identifies
$W/p^n$ with $F_\lambda[p^n]$ by $a\mapsto[a]_\lambda(\omega_n)$, and Theorem 6.3 there shows
that this character is well defined and compatible in $n$.

That torsion is a finite-flat group over $W$. The polynomial $\lambda^{\circ n}(T)$ is monic
of degree $q^n$, so $B_n=W[T]/(\lambda^{\circ n}(T))$ is finite free of rank $q^n$ over $W$.
Since $\lambda^{\circ n}(T)\equiv T^{q^n}$ modulo $p$, the ideal $(T)$ is nilpotent modulo
$p$ in $B_n$, and $B_n$, being finite over $W$ and hence $p$-adically complete, is complete
and separated for the $(T)$-adic topology; the power series $F_\lambda(X,Y)$ and
$[a]_\lambda(T)$ therefore converge in the relevant completed tensor products. Because
$[p^n]_\lambda$ is an endomorphism,

$$
\lambda^{\circ n}\bigl(F_\lambda(X,Y)\bigr)
=F_\lambda\bigl(\lambda^{\circ n}(X),\lambda^{\circ n}(Y)\bigr)
$$

lies in the ideal generated by $\lambda^{\circ n}(X)$ and $\lambda^{\circ n}(Y)$, and
likewise $\lambda^{\circ n}([a]_\lambda(T))=[a]_\lambda(\lambda^{\circ n}(T))$ lies in
$(\lambda^{\circ n}(T))$. So $T\mapsto F_\lambda(X,Y)$ and $T\mapsto[a]_\lambda(T)$ define a
comultiplication and a $W$-action on $\mathcal G_n=\operatorname{Spec}B_n$, whose geometric
points are $F_\lambda[p^n]\simeq W/p^n$ with $G_{K_0}$ acting by $\chi_{\mathrm{LT}}$.

Consequently the lattice $T^{\mathrm{LT}}=W(\chi_{\mathrm{LT}})$ is free of rank one over
$W$, all of its quotients $T^{\mathrm{LT}}/p^nT^{\mathrm{LT}}$ are finite flat, and it
carries a coefficient action of $W$. Theorem 14.1, together with Section 9.3, supplies a
coefficient-linear strongly divisible lattice $L^{\mathrm{LT}}$ with
$L^{\mathrm{LT}}/p^nL^{\mathrm{LT}}=\mathbf D_{\mathrm{FL}}(\mathcal G_n)$. Here $a\in W$
acts on $\mathbf D_{\mathrm{FL}}(\mathcal G_n)$ by $[a]_\lambda^{*}$ and on solutions by
precomposition, which under the covariant identification (2.8) is the map induced by
$[a]_\lambda$ on geometric points, namely multiplication by $a$ on $F_\lambda[p^n]$. So the
character realized by $L^{\mathrm{LT}}$ is $\chi_{\mathrm{LT}}$ itself rather than its
inverse.

The opening paragraph of this proof, applied to $\chi_{\mathrm{LT}}$ with the coefficient
ring $W$, splits $L^{\mathrm{LT}}$ into lines $L^{\mathrm{LT}}_\tau$ with equations of the
form (14.6b). Its Hodge steps can now be read off. By (3.2) the Hodge step of
$\mathbf D_{\mathrm{FL}}(\mathcal G_n)$ is the image of the invariant differentials
$\omega_{\mathcal G_n}=I/I^2$, where $I=(T)$ is the augmentation ideal of $B_n$. Since
$\lambda^{\circ n}(T)\equiv p^nT$ modulo $T^2$,

$$
\omega_{\mathcal G_n}=(W/p^n)\,T,
$$

free of rank one, while the coefficient action of $a\in W$, namely $[a]_\lambda^*$, sends $T$
to $[a]_\lambda(T)\equiv aT$ modulo $T^2$ and so acts by multiplication by $a$. On
$\omega_{\mathcal G_n}$ the coefficient action therefore agrees with the structural action of
$W$, which is to say that $\omega_{\mathcal G_n}$, and hence the Hodge step, lies entirely in
the component indexed by the identity embedding. The Hodge step is not zero: otherwise
$L^{\mathrm{LT}}$ would be a unit-root object and its realization unramified by Book 53,
Section 4.1, whereas Book 5, Section 6.3 shows that $K_0(\omega_1)/K_0$ is totally ramified
of degree $q-1>1$. Hence

$$
h^{\mathrm{LT}}_{\operatorname{id}}=1,
\qquad
h^{\mathrm{LT}}_\tau=0\quad(\tau\ne\operatorname{id}),
$$

so that $L^{\mathrm{LT}}$ is, up to its own unramified factor $\prod_\tau a_\tau$, exactly
the atomic one-step display with weight one at $\tau_0=\operatorname{id}$. For that display
$\xi_{\tau_0}=\tau_0\circ\psi$ reads $\chi_{\mathrm{LT}}=\psi$, up to an unramified
character. Therefore, for every embedding $\tau$, the atomic display with weight one at
$\tau$ and weight zero elsewhere realizes $\tau\circ\chi_{\mathrm{LT}}$ up to an unramified
character, and its level-$n$ equation (14.6e) is the level-$n$ torsion equation of the
Lubin--Tate formal $\mathcal O_{K_0}$-module read through $\tau$.

Two things have been bought. The exponent $h_\tau$ is now visibly the number of times the
embedding $\tau$ carries a division by $p$ around the Frobenius cycle, so the exponents in
(14.6a) are read off the Hodge steps and nothing else; and the index of the resulting formal
module is forced rather than chosen, since it is fixed by the single computation of
$\omega_{\mathcal G_n}$ above. Relabelling the embeddings permutes the atomic factors among
themselves and therefore leaves the product over $\{\tau:h_\tau=1\}$, in particular the case
of (14.6a) in which every $h_\tau=1$, unchanged.

Consequently the inverse-limit character of that display is the $\tau$-conjugate
Lubin--Tate character $\tau\circ\chi_{\mathrm{LT}}$, and not its inverse. The contravariance
of $T_{\mathrm{FL}}$ is already accounted for by the normalization (2.6), in which the
weight-one line realizes $\mu_{p^n}$ rather than its dual, and the transition maps in (14.4)
are the ones induced by the strict injections $L/p^nL\xrightarrow{p}L/p^{n+1}L$, which on
torsion points are the standard $p$-power maps of the tower. So the passage to the inverse
limit introduces no further reversal.

It remains to convert this Galois-side statement into a statement about units. Book 5,
Proposition 10.1 evaluates arithmetic reciprocity on the torsion tower as
$\operatorname{rec}_{K_0}(u)(\omega_n)=[u^{-1}](\omega_n)$, so
$\chi_{\mathrm{LT}}(\operatorname{rec}_{K_0}(u))=u^{-1}$, and the $\tau$-conjugate character
is therefore

$$
u\longmapsto\tau(u)^{-1}
$$

on a sufficiently small principal-unit group. Multiplying the factors over those $\tau$ with
$h_\tau=1$ and restoring the unramified scalar gives (14.6a) directly. As a check on the
sign, taking $h_\tau=1$ for every $\tau$ makes the product $N_{K_0/\mathbf Q_p}(u)^{-1}$,
which is the value of the cyclotomic character on $\operatorname{rec}_{K_0}(u)$ in the
arithmetic normalization; that is the same character as the one produced by the weight-one
line through (2.6), as it must be. No Sen operator or $\mathbf C_p$ period decomposition has
entered the argument. Thus $\xi$ is locally algebraic.

If $\xi$ descends to $G_{\mathbf Q_p}$, conjugation by arithmetic Frobenius fixes its
inertial character. Frobenius cyclically permutes the embeddings $\tau$ of the unramified
field. Uniqueness of the exponents in the $p$-adic logarithm on principal units therefore
forces $h_{\varphi\tau}=h_\tau$ for every $\tau$, hence all $h_\tau$ are equal. $\square$

### 14.3 Arbitrary open ideals

Let $\mathcal O$ be the ring of integers in a finite extension of $\mathbf Q_p$, and let $T$ be finite free over $\mathcal O$ with an integral coefficient action on its associated system. For an open ideal $I\subset\mathcal O$, choose $n$ with $p^n\in I$. Then $T/IT$ is a quotient of $T/p^nT$, hence is finite flat by Book 42's schematic-closure calculus or by Theorem 13.1.

Let $M_n$ correspond to $T/p^nT$. Define

$$
M_I=M_n[I]_{\mathrm{adm}}.
\tag{14.6}
$$

Theorem 13.1 shows that $M_I$ is independent of $n$, because it is uniquely characterized by

$$
T(M_I)=T/IT.
\tag{14.7}
$$

For $J\subset I$, the maps $M_I\hookrightarrow M_J$ satisfy transitivity. Hence all open-ideal quotients of one stable lattice form a single compatible integral system, not unrelated choices of finite-flat models.

### 14.4 Changing the stable lattice

Two $G_{K_0}$-stable $\mathcal O$-lattices $T$ and $T'$ in one rational representation need not be equal or isomorphic. Their rational spans therefore do not determine a common integral Fontaine--Laffaille module. If both have finite-flat quotients at every level, Theorem 14.1 attaches separate strongly divisible lattices $L$ and $L'$.

If $p^aT\subset T'\subset p^{-b}T$, the induced maps of rational representations give maps between sufficiently shifted finite quotients. Full faithfulness reconstructs the corresponding filtered maps, and saturation measures the difference of the two lattices. It does not force equality. The compatible-quotient theorem says that each chosen stable lattice behaves well under all coefficient quotients; it does not say that a rational representation selects a preferred lattice.

## 15. The height-two package

The general equivalence applies in every finite height, but the later arithmetic use is concentrated in rank two with one Hodge direction. In that case the filtration, determinant, ordinary boundary, and stable lines admit an especially concrete description.

### 15.1 Rank two and Hodge type zero--one

Let $\mathcal O$ be the ring of integers in a finite extension of
$\mathbf Q_p$, and put
$R_{\mathcal O}=W\otimes_{\mathbf Z_p}\mathcal O$. A coefficient-linear
strongly divisible module $L$ has **height two and Hodge type $(0,1)$**
when it is finite projective of rank two over $R_{\mathcal O}$ and

$$
\operatorname{rank}F_L=1,\qquad
\operatorname{rank}(L/F_L)=1
\tag{15.1}
$$

as $R_{\mathcal O}$-modules. Locally on
$\operatorname{Spec}R_{\mathcal O}$ choose
$L=R_{\mathcal O}e_0\oplus R_{\mathcal O}e_1$ with
$F_L=R_{\mathcal O}e_1$. With Frobenius $\sigma\otimes1$ on the
coefficient ring, strong divisibility says that

$$
\varphi_0(e_0)=ae_0+ce_1,\qquad
\varphi_1(e_1)=be_0+de_1,\qquad
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{GL}_2(R_{\mathcal O}).
\tag{15.2}
$$

The individual entries depend on the basis; invertibility of the normal matrix and the rank of the Hodge step do not.

The associated stable Galois lattice has rank two over $\mathcal O$, and every finite quotient has a finite-flat model of order equal to the cardinality of that quotient.

### 15.2 Ordinary and local--local fibers

Let $\kappa$ be the residue field of $\mathcal O$. After extending $k$
so that $k\otimes_{\mathbf F_p}\kappa$ splits, the residual coefficient
idempotents decompose the special-fiber Dieudonné module into
two-dimensional BT$_1$ factors of dimension one. Each factor has two
geometric possibilities.

- In the ordinary case it has an étale line and a multiplicative line. The filtered module may still be a nonsplit extension; ordinary does not mean that the mixed-characteristic group or its generic representation splits.
- In the local--local case both Frobenius and Verschiebung are nilpotent on that plane. There is no étale or multiplicative direct factor, but the normal matrix (15.2) remains invertible and the generic representation still has two independent torsion directions.

These cases are stable under algebraic extension of the residue field.
Different coefficient factors can have different types; the unqualified
word **ordinary** means that every factor is ordinary, while
**local--local** means that every factor is local--local. Over a
nonalgebraically closed perfect field, forms carry semilinear descent
data and should not be collapsed to one chosen normal form.

### 15.3 Stable lines and reducible representations

Let a finite coefficient quotient of $T$ contain a stable **line**
$U$, meaning a rank-one direct summand over that quotient coefficient
ring. Theorem 8.1 constructs the unique admissible quotient

$$
M_n\twoheadrightarrow Q_U,\qquad T(Q_U)=U.
\tag{15.3}
$$

The kernel realizes $(T/p^nT)/U$. Thus a reducible finite-flat representation carries not only finite-flat diagonal characters but also an admissible extension class. Conversely, two finite-flat characters and an arbitrary generic cocycle need not give a finite-flat middle term; the cocycle must arise from an admissible extension.

If the stable lines are compatible in $n$, uniqueness makes the quotients $Q_{U,n}$ compatible. Their inverse limits give a saturated filtered quotient of $L$. If they exist only after reduction at one level, no integral stable line in $T$ is implied.

### 15.4 A height-two equivalence theorem

**Theorem 15.1 (height-two integral package).** Let $p>2$, let
$K_0=W(k)[1/p]$ with $k$ perfect, and let $\mathcal O$ be the ring of
integers in a finite extension of $\mathbf Q_p$. The following data are
equivalent, with arrows reversed on the filtered side:

1. a height-two strongly divisible $W\otimes\mathcal O$-lattice of Hodge type $(0,1)$;
2. a rank-two $\mathcal O$-stable $G_{K_0}$-lattice whose every
   open-ideal quotient is finite flat and whose uniquely attached
   divided filtered objects have a rank-one Hodge step and rank-one
   quotient over the corresponding coefficient ring;
3. a compatible system of coefficient-linear finite-flat group schemes
   representing $T/IT$ for all open ideals $I\subset\mathcal O$, whose
   contravariant filtered crystals have that same Hodge type.

The equivalence preserves unramified base change, duality, perfect
alternating pairings, stable lines, and each coefficientwise ordinary
or local--local special-fiber type. A supplied perfect alternating
pairing forces the cyclotomic determinant as in Section 9.4.

**Proof.** The equivalence of the first two data is Theorem 14.1 with
the commuting $\mathcal O$-action transported by full faithfulness as
in Section 9.3. No trace self-duality of $\mathcal O/\mathbf Z_p$ is
needed merely to retain an existing action. The second datum gives the
third by Theorem 13.1, and the groups recover the filtered objects
through $\mathbf D_{\mathrm{FL}}$. Compatibility in $I$ is (13.6), so
the construction is independent of choices. Duality and pairings are
Chapter 9, base change is Chapter 10, and each special-fiber factor is
read from Frobenius and Verschiebung on the crystalline module.
$\square$

The Hodge-number condition in item 2 means that the associated integral filtered object has (15.1); it is not inferred from the abstract mod-$p$ representation alone.

## 16. Boundaries and failure modes

The clean theorem depends simultaneously on a weight bound, an unramified base, perfect residue field, and integral presentations. This chapter records what breaks when one of those conditions is removed.

### 16.1 The prime two boundary

At $p=2$, the interval $[0,1]$ reaches length $p-1$. The endpoint syntomic sequences still exist with the modified first filtration, but the mixed successive-approximation estimate used for full faithfulness and the coordinate lemma no longer improves the error strictly. Independently, the Raynaud inequality $e<p-1$ becomes $1<1$, which is false over an unramified dyadic base.

Thus neither endpoint calculation implies the mixed anti-equivalence at $p=2$. Order-two groups already exhibit distinct models of the same generic group. No theorem in this book includes $p=2$.

### 16.2 Ramified bases

Let $R$ be a mixed-characteristic DVR with $v_R(p)=e$. If $e\ge p-1$, Oort--Tate rescaling can produce two nonisomorphic order-$p$ groups with isomorphic generic fibers. Generic fiber is then not fully faithful, so the reconstruction step (7.2) fails.

Even when $e<p-1$, a ramified base has no canonical Witt Frobenius with the simple divisibility rule (3.5). A more elaborate linear category may classify its groups, but it is not the category used here. Replacing $W$ by $R$ in the formulas without adding ramification data is invalid.

### 16.3 Rational data do not select a lattice

Inverting $p$ forgets the integral Hodge submodule, the divided map $\varphi_1$, and the position of every coefficient lattice. Two strongly divisible lattices can span the same rational filtered Frobenius module. Likewise two stable Galois lattices can span the same rational representation while having different reductions.

Theorem 14.1 begins with a chosen stable lattice whose all reductions are finite flat. It does not assert that every stable lattice in a crystalline rational representation is finite flat, nor that the rational representation has a canonical one.

### 16.4 A hypothesis ledger

| Assertion                         | Hypotheses used                                              | Failure prevented                             |
| --------------------------------- | ------------------------------------------------------------ | --------------------------------------------- |
| divided filtered category         | $W=W(k)$, $k$ perfect                                        | missing canonical semilinear Frobenius        |
| mixed weight $[0,1]$              | $p>2$                                                        | loss of strict small-weight contraction       |
| group-crystal strong divisibility | actual finite-flat lift and Hodge step                       | arbitrary special-fiber filtration            |
| free solution representability    | free reduction and invertible normal matrix                  | lost solutions in a coordinate chart          |
| general integral solution model   | strict presentation, saturated closure, and $e<p-1$ rigidity | nonflat raw kernel or presentation dependence |
| integral period comparison        | all étale, multiplicative, and local--local factors          | proof by endpoint factors only                |
| reconstruction from generic fiber | $e=1<p-1$                                                    | multiple integral models                      |
| unramified base change            | Witt extension of perfect fields                             | changed ramification and divisibility         |
| naïve coefficient tensor formula  | specified self-duality $B\simeq B^\vee$                      | confusing extension with coextension          |
| nonflat coefficient quotient      | admissible annihilator construction                          | Tor and failure of strictness                 |
| lattice from finite levels        | compatible exact transition maps                             | unrelated choices at each level               |
| height-two determinant            | actual perfect pairing                                       | unjustified exterior-power model              |

## 17. The integral classification package

All three integral languages are now interchangeable in the safe range. This final chapter states the package in one theorem, records its precise prior inputs, and ends with a protocol that keeps variance and base change visible.

### 17.1 The main theorem

**Theorem 17.1 (integral Fontaine--Laffaille classification and base change).** Let $p>2$, let $k$ be perfect of characteristic $p$, put $W=W(k)$ and $K_0=W[1/p]$. Then:

1. Crystalline extensions with their Hodge step define an exact anti-equivalence

   $$
   \mathrm{FF}_W^{\mathrm{op}}
   \simeq\mathrm{MF}^{[0,1]}_{\mathrm{tor}}(W).
   \tag{17.1}
   $$

2. On free reductions the quasi-inverse represents the syntomic
   solution sheaf; for every admissible torsion object it is the unique
   finite-flat model of the geometric solution module, and

   $$
   \mathcal G(M)(\overline K_0)=T_{\mathrm{FL}}(M),
   \qquad |\mathcal G(M)|=p^{\ell_W(M)}.
   \tag{17.2}
   $$

3. The essential image of $T_{\mathrm{FL}}$ is exactly the finite-flat finite $p$-primary $G_{K_0}$-modules. Stable submodules and quotients correspond to admissible quotients and subobjects in reversed order.
4. The equivalence preserves exactness, Cartier duality, Tate twist, perfect pairings, and arbitrary commuting finite coefficient actions.
5. For every perfect extension $k'/k$,

   $$
   \mathcal G(M)_{W(k')}\simeq
   \mathcal G(W(k')\otimes_WM),
   \tag{17.3}
   $$

   For finite $k'/k$, generic realization also commutes with restriction
   to $G_{W(k')[1/p]}$.
6. Finite unramified descent data are effective and are detected equally
   on groups, filtered modules, or generic representations with a
   supplied upstairs model.
7. For a finite projective coefficient extension $A\to B$, whenever
   the displayed scalar object is admissible, the operation
   corresponding to $B\otimes_A-$ on Galois modules is

   $$
   B\boxtimes_AM=B^\vee\otimes_AM.
   \tag{17.4}
   $$

8. If a finite commutative $\mathbf Z_p$-algebra $A$ acts on $M$, then for every ideal $I\subset A$ the quotient $T(M)/IT(M)$ is represented by the unique admissible subobject $M[I]_{\mathrm{adm}}\hookrightarrow M$. These objects are functorial and compatible for nested ideals and unramified base change.
9. Finite free strongly divisible lattices are anti-equivalent to stable
   $\mathbf Z_p$-lattices all of whose finite reductions are finite
   flat. If the lattice is finite free over the ring of integers
   $\mathcal O$ in a finite extension of $\mathbf Q_p$, every
   open-ideal quotient belongs to one canonical compatible system.
10. In rank two and Hodge type $(0,1)$, the equivalence preserves
    coefficientwise ordinary and local--local type, stable lines, and
    perfect alternating pairings. When such a pairing is supplied, it
    forces the cyclotomic determinant.

**Proof.** Parts 1--2 are Theorems 7.1, 5.1, and 6.2. Part 3 is Theorem 8.1 and Section 8.2. Duality and coefficients are Chapter 9. Ground-field base change and descent are Theorems 10.1 and 11.1. Coefficient extension is Theorem 12.2. Nonflat quotients are Theorem 13.1. Stable lattices are Theorem 14.1, and height two is Theorem 15.1. $\square$

### 17.2 Dependency closure

The proof uses the direct prerequisites in the following exact forms.

- Book 5 supplies the arithmetic-reciprocity labeling of the Lubin--Tate
  torsion tower used to identify the rank-one Lubin--Tate factors in the
  height-two local test.
- Book 34 supplies schematic Cartier duality, its exactness, the
  perfect evaluation pairing, and the Tate-twisted formula on an étale
  generic fiber.
- Book 42 supplies the finite étale--Galois correspondence, the definition of a marked finite-flat model, exactness of generic points, schematic closure of stable subgroups, represented finite-flat quotients, coefficient actions on models, and the warning that existence and uniqueness differ.
- Book 50 supplies the modified first filtration, integral divided Frobenius, the weight-zero and weight-one fundamental exact sequences, divided-power logarithm and exponential, syntomic descent, coefficient-level exact sequences, and unramified pullback of period constructions.
- Book 53 supplies the category of admissible torsion divided filtered modules, normal decompositions, the small-weight lifting lemma, exactness and full faithfulness of $T_{\mathrm{FL}}$, its length formula, duality, coefficients, and the comparison map under unramified ground-field extension.

A transitive source is also explicitly reused in Proposition 3.2 and therefore remains a
direct graph edge. Book 52
proves finite Dieudonné classification over a perfect field, exactness,
Cartier duality, and PD base change of crystalline Dieudonné theory,
the Hodge description for abelian degree-one crystals, and Raynaud full
faithfulness when $e<p-1$. Over $W$ this inequality is (1.3). The
Hodge step for an arbitrary finite-flat lift and its strong divisibility
are constructed in Chapter 3 of this book; they are not attributed to
the abelian comparison of Book 52. Ordinary background supplies finite
projective descent, Nakayama's lemma, tensor--Hom adjunction, inverse
limits of finite free modules, and the finite locally free criterion for
Hopf algebras.

No later book, ramified classification theorem, or rational comparison theorem is used to prove (17.1).

### 17.3 A calculation protocol

For a finite torsion representation or a stable lattice, the following order avoids every variance and base-change trap.

1. Verify $p>2$ and that the local base is the absolutely unramified $W(k)$ with $k$ perfect.
2. State whether a finite-flat model, a divided filtered module, or only a generic representation is initially supplied.
3. On the filtered side, retain $\varphi_1$ as structure and check strictness of every exact sequence.
4. Use Theorem 8.1, not rational Hodge labels, to identify the finite-flat essential image.
5. Translate a generic stable subgroup into an admissible quotient, and a generic quotient into an admissible subobject.
6. For unramified ground-field extension, tensor the Witt module and then use (10.6); do not tensor Frobenius fixed points formally.
7. For a finite projective coefficient extension, use $B^\vee\otimes_A-$ unless a perfect trace self-duality has been specified.
8. For a nonflat coefficient quotient, use $M[I]_{\mathrm{adm}}$, not a naïve tensor product or annihilator.
9. Before passing to a stable lattice, check compatible exact transition maps at every finite level.
10. Check duality and determinants through an actual perfect pairing.

### 17.4 Conclusion

In the absolutely unramified low-weight range, divided filtered modules
are not merely a faithful linear shadow of finite-flat geometry. The
syntomic equations of free reductions possess finite locally free
integral coordinate algebras; saturated closure inside those groups
gives every torsion object its unique finite-flat model. Conversely,
every finite-flat group supplies a divided filtered module through its
crystalline extensions and its correctly oriented Hodge step
$\omega_{\mathcal G}$. The integral period comparison identifies the
geometric generic points with the solutions of divided Frobenius.
Raynaud rigidity then turns that comparison into mutually inverse
constructions.

The resulting anti-equivalence explains every arrow. A finite-flat subgroup becomes a filtered quotient; a finite-flat quotient becomes a filtered subobject; Cartier duality exchanges weights zero and one; and two contravariant functors recover the covariant generic-point representation. Local--local groups are retained because rank is proved on the coordinate algebra rather than guessed from special-fiber points.

Base change is equally integral. Extending the perfect residue field commutes with the group and its filtered crystal. For a finite residue extension, the generic realization is the restriction to the corresponding enlarged unramified Galois group. Extending a coefficient ring follows a different rule: contravariance inserts the finite-projective dual. Nonflat coefficient reduction is controlled by the admissible annihilator, constructed from an actual finite-flat quotient and characterized by its generic module.

Finally, a stable lattice is recovered from all its finite levels, and every open-ideal quotient belongs to one compatible system. In height two with Hodge type $(0,1)$, this system records coefficientwise ordinary and local--local specialization, reducible lines and their extension classes, duality, and the cyclotomic determinant forced by a supplied perfect alternating pairing. These are precisely the integral classification, base-change, and compatible-quotient tools needed to carry finite flatness through changes of coefficients without pretending that rational data determine a lattice.
