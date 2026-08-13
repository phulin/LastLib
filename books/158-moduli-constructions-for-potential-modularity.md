# Moduli Constructions for Potential Modularity

## Contents

1. [The realization problem](#1-the-realization-problem)
   - [From a representation to a moving abelian variety](#11-from-a-representation-to-a-moving-abelian-variety)
   - [The determinant obstruction comes first](#12-the-determinant-obstruction-comes-first)
   - [Why one elliptic curve is often too small](#13-why-one-elliptic-curve-is-often-too-small)
   - [The construction in one diagram](#14-the-construction-in-one-diagram)
2. [Symplectic modules and twisted frames](#2-symplectic-modules-and-twisted-frames)
   - [Alternating lines and multipliers](#21-alternating-lines-and-multipliers)
   - [Galois modules with a fixed pairing](#22-galois-modules-with-a-fixed-pairing)
   - [The isomorphism torsor and its cocycle](#23-the-isomorphism-torsor-and-its-cocycle)
   - [A counterexample from forgetting the multiplier](#24-a-counterexample-from-forgetting-the-multiplier)
3. [Twisted modular curves](#3-twisted-modular-curves)
   - [Why the one-prime case is the model](#31-why-the-one-prime-case-is-the-model)
   - [Descent from the standard full-level curve](#32-descent-from-the-standard-full-level-curve)
   - [Worked example: a quadratic twist of level five](#33-worked-example-a-quadratic-twist-of-level-five)
   - [Coarse level is not enough](#34-coarse-level-is-not-enough)
4. [Why two primes lead to real multiplication](#4-why-two-primes-lead-to-real-multiplication)
   - [The naive fiber product](#41-the-naive-fiber-product)
   - [The Hilbert--Blumenthal alternative](#42-the-hilbert--blumenthal-alternative)
   - [Choosing the coefficient field and its primes](#43-choosing-the-coefficient-field-and-its-primes)
   - [A two-prime datum in degree two](#44-a-two-prime-datum-in-degree-two)
5. [The Hilbert--Blumenthal moduli datum](#5-the-hilbert--blumenthal-moduli-datum)
   - [Why an action alone is insufficient](#51-why-an-action-alone-is-insufficient)
   - [Hilbert--Blumenthal abelian schemes](#52-hilbert--blumenthal-abelian-schemes)
   - [Polarization pairings at coefficient primes](#53-polarization-pairings-at-coefficient-primes)
   - [Neat auxiliary level](#54-neat-auxiliary-level)
   - [The untwisted fine space](#55-the-untwisted-fine-space)
6. [Imposing the two twisted levels](#6-imposing-the-two-twisted-levels)
   - [The target data](#61-the-target-data)
   - [Descent as a product cocycle](#62-descent-as-a-product-cocycle)
   - [Representability and the universal object](#63-representability-and-the-universal-object)
7. [Deformations, smoothness, and dimension](#7-deformations-smoothness-and-dimension)
   - [The tangent problem](#71-the-tangent-problem)
   - [Formal smoothness](#72-formal-smoothness)
   - [Why there is room](#73-why-there-is-room)
8. [Geometric components and monodromy](#8-geometric-components-and-monodromy)
   - [Three notions that must be separated](#81-three-notions-that-must-be-separated)
   - [The monodromy criterion](#82-the-monodromy-criterion)
   - [Verifying the hypothesis](#83-verifying-the-hypothesis)
   - [Determinants and component stability](#84-determinants-and-component-stability)
9. [Local points as comparison objects](#9-local-points-as-comparison-objects)
   - [The local design principle](#91-the-local-design-principle)
   - [Good places](#92-good-places)
   - [Archimedean places](#93-archimedean-places)
   - [Places above the target characteristic](#94-places-above-the-target-characteristic)
   - [Places above the auxiliary characteristic](#95-places-above-the-auxiliary-characteristic)
   - [Ramified primes and primes of the datum](#96-ramified-primes-and-primes-of-the-datum)
   - [A worked pair of residual places](#97-a-worked-pair-of-residual-places)
10. [Local conditions are open](#10-local-conditions-are-open)
   - [From a point to a neighborhood](#101-from-a-point-to-a-neighborhood)
   - [Good reduction](#102-good-reduction)
   - [Semistable reduction](#103-semistable-reduction)
   - [Constancy of finite-flat comparison](#104-constancy-of-finite-flat-comparison)
   - [The finite local set](#105-the-finite-local-set)
11. [Explicit local seeds](#11-explicit-local-seeds)
   - [The Serre tensor construction](#111-the-serre-tensor-construction)
   - [Real and good seeds](#112-real-and-good-seeds)
   - [Ordinary and nonordinary seeds](#113-ordinary-and-nonordinary-seeds)
   - [Semistable seeds from Tate curves](#114-semistable-seeds-from-tate-curves)
12. [Persistence and simultaneous local conditions](#12-persistence-and-simultaneous-local-conditions)
   - [Persistence under finite extension](#121-persistence-under-finite-extension)
   - [Intersections must have a witness](#122-intersections-must-have-a-witness)
   - [Components and degeneracy loci](#123-components-and-degeneracy-loci)
   - [The simultaneous-neighborhood theorem](#124-the-simultaneous-neighborhood-theorem)
13. [The complete geometric package](#13-the-complete-geometric-package)
   - [Admissible two-prime moduli data](#131-admissible-two-prime-moduli-data)
   - [The smooth connected cover theorem](#132-the-smooth-connected-cover-theorem)
   - [The local-open theorem](#133-the-local-open-theorem)
   - [Examples and counterexamples](#134-examples-and-counterexamples)
14. [Disjointness and the exact handoff](#14-disjointness-and-the-exact-handoff)
   - [The avoidance datum](#141-the-avoidance-datum)
   - [What disjointness would preserve](#142-what-disjointness-would-preserve)
   - [Root fields and normal closures](#143-root-fields-and-normal-closures)
   - [The output boundary](#144-the-output-boundary)
15. [Failure audit](#15-failure-audit)
   - [Empty twists and false components](#151-empty-twists-and-false-components)
   - [Generic frames and integral models](#152-generic-frames-and-integral-models)
   - [Separate local solutions](#153-separate-local-solutions)
   - [Smoothness, nonemptiness, and automorphy](#154-smoothness-nonemptiness-and-automorphy)
16. [Conclusion](#16-conclusion)

## 1. The realization problem

### 1.1 From a representation to a moving abelian variety

Let $F$ be a totally real number field, let $p$ be an odd prime, let $k$ be a finite field of characteristic $p$, and let

$$
\bar\rho:G_F\longrightarrow \operatorname{GL}_2(k)
$$

be continuous and absolutely irreducible. Potential modularity begins with a reversal of the usual direction of thought. Torsion on an abelian variety gives a Galois representation; here the representation is given first, and one asks for an abelian variety whose torsion is that representation.

The desired construction must do much more than match two abstract vector spaces. It must preserve the alternating form forced by a polarization, behave correctly at places above $p$, meet specified reduction conditions at other places, and coexist with a second torsion representation. Finally, all these requirements must define open local conditions on one smooth geometrically connected variety, for only then can a later arithmetic approximation theorem turn local models into a global point over a finite totally real extension.

This book constructs precisely that variety and its local-open package. It does not produce the global point and does not prove modularity. Our task is geometric and local-arithmetic at once: design a moduli problem that remembers enough information to realize both representations conditionally at a future point, but remains smooth and connected enough for later approximation.

### 1.2 The determinant obstruction comes first

If $E/F$ is an elliptic curve, its Weil pairing gives a perfect alternating, Galois-equivariant map

$$
e_p:E[p]\times E[p]\longrightarrow \mu_p.
$$

Taking an ordered basis shows

$$
\det E[p]=\bar\chi_p,
$$

where $\bar\chi_p$ is the mod-$p$ cyclotomic character. Consequently an isomorphism $\bar\rho\simeq E[p]$ cannot exist unless

$$
\det\bar\rho=\bar\chi_p. \tag{1.1}
$$

More generally, a polarization with coefficient or polarization module may replace $\mu_p$ by a one-dimensional pairing module $L_p$. Then the necessary condition is an identification

$$
\det V_{\bar\rho}=L_p \tag{1.2}
$$

of Galois modules, not merely equality of their dimensions. This is the first design constraint, not a cosmetic normalization. A quadratic twist does not repair an arbitrary determinant: in dimension two, twisting by $\eta$ multiplies the determinant by $\eta^2$. One must arrange determinant compatibility in the input, often after a controlled scalar twist whose square has the required ratio.

An odd representation satisfies $\det\bar\rho(c)=-1$ for every complex conjugation $c$. Since $\bar\chi_p(c)=-1$, condition (1.1) implies oddness. The converse is false: oddness tests only complex conjugations and says nothing about the determinant at finite Frobenius elements.

### 1.3 Why one elliptic curve is often too small

Suppose a second odd representation

$$
\bar\rho_{\mathrm{aux}}:G_F\longrightarrow\operatorname{GL}_2(k')
$$

of characteristic $q\ne p$ is prescribed. Asking for an elliptic curve $E$ with

$$
E[p]\simeq\bar\rho,
\qquad
E[q]\simeq\bar\rho_{\mathrm{aux}}
\tag{1.3}
$$

is a condition on a one-dimensional moduli space. The simultaneous level scheme is not literally the fiber product of two independently twisted modular curves over their $j$-lines unless their descent data and pairing coordinates agree. Even when it is correctly formed as one twist of full $pq$-level, it is still a curve. A finite list of local open conditions is not prohibited on a curve, but there may be no convenient local points, and the two residual requirements leave little geometric freedom for arranging additional PEL and reduction data.

The remedy is not to take a product of unrelated elliptic curves. It is to enlarge the endomorphism structure. A Hilbert--Blumenthal abelian variety with real multiplication by an order of degree $g$ has dimension $g$, yet each prime $\lambda$ of the coefficient order cuts out a two-dimensional torsion module. Distinct primes $\lambda$ and $\lambda'$ can therefore carry the two representations while all $g$ real directions remain available in the moduli space.

### 1.4 The construction in one diagram

The argument will have the following shape:

$$
\begin{array}{c}
(\bar\rho,\bar\rho_{\mathrm{aux}})
\ +\ \text{pairings and local models}
\\ \downarrow \\
X=X(\bar\rho,\bar\rho_{\mathrm{aux}})
\quad\text{smooth, geometrically connected, }\dim X=g
\\ \downarrow\ \text{local points and open neighborhoods} \\
x\in X(F')\quad(F'/F\text{ finite totally real and disjoint})
\\ \downarrow \\
(A,\iota,\lambda_A,\eta;\alpha,\alpha_{\mathrm{aux}})/F'.
\end{array} \tag{1.4}
$$

Every downward arrow has a separate possible failure. Pairings may be incompatible; the moduli functor may retain automorphisms; the chosen geometric component may not descend; local models may not exist at level primes; or the extension $F'$ may meet a residual fixed field and shrink an image. Keeping these obstructions visible is the governing method of the book.

## 2. Symplectic modules and twisted frames

Chapters 2--13 are an import-and-application layer. Book 156 owns the two-prime
Hilbert--Blumenthal moduli space, paired-frame twists, components, and product monodromy; Book
157 owns its integral local geometry, corrected tensor component, simultaneous local opens, and
persistence. This book does not reprove either package.

### 2.1 Alternating lines and multipliers

For each target module $V_{\mathfrak p}$ we require a chosen $G_F$-equivariant determinant-line
isomorphism with the pairing line in Book 156, Theorem 5.1. Equality of determinant characters
without this chosen isomorphism is insufficient to define the paired frame.

### 2.2 Galois modules with a fixed pairing

Fix distinct monodromy-admissible odd primes $\mathfrak p,\mathfrak q$ of a totally real
coefficient field $M$, and rank-two modules $V_{\mathfrak p},V_{\mathfrak q}$ with the exact
cyclotomic pairing-line identifications required in Book 156, Theorem 12.1.

### 2.3 The isomorphism torsor and its cocycle

The two isomorphism sheaves and their determinant-one descent cocycles are the paired-frame
torsors of Book 156, Chapters 6--8. Their product is formed over one Hilbert--Blumenthal base; it
is not a product of independently descended moduli problems.

### 2.4 A counterexample from forgetting the multiplier

If either multiplier is wrong, the fixed-pairing twist is empty. Twisting the union of all
pairing components can instead produce a scheme connected over $F$ but geometrically
disconnected. This is why the chosen determinant-line data remain visible in every theorem.

## 3. Twisted modular curves

### 3.1 Why the one-prime case is the model

The modular-curve twist is only a model for the descent cocycle. The application uses the
higher-dimensional Hilbert--Blumenthal space of Book 156.

### 3.2 Descent from the standard full-level curve

Descent is imported from Book 156, Proposition 8.1 and its moduli interpretation. No coarse
space is used before neat level has removed automorphisms.

**Proposition 3.1 (twisted modular curve; compatibility alias).** In the specialization
$M=\mathbf Q$, Book 156's determinant-compatible paired-frame construction represents the twist
by a smooth geometrically connected fine curve with its universal elliptic curve.

### 3.3 Worked example: a quadratic twist of level five

The example is subsumed by the rank-two determinant obstruction: a quadratic scalar twist
changes a two-dimensional determinant by a square and cannot repair an arbitrary multiplier.

### 3.4 Coarse level is not enough

The universal abelian scheme and its two exact frames live on the fine corrected-level scheme of
Book 157, Theorem 4.1. A coarse point alone does not furnish the tuple used later.

## 4. Why two primes lead to real multiplication

### 4.1 The naive fiber product

Two independently twisted modular curves do not force both torsion systems onto one abelian
variety and need not have compatible descent data.

### 4.2 The Hilbert--Blumenthal alternative

Real multiplication supplies a rank-two torsion factor at each coefficient prime on one abelian
scheme, while retaining relative dimension $[M:\mathbf Q]$.

### 4.3 Choosing the coefficient field and its primes

The primes must be distinct, odd, away from the different, polarization, and auxiliary level,
and monodromy-admissible in the precise sense of Book 156, Theorem 12.1.

### 4.4 A two-prime datum in degree two

When $M$ is real quadratic and both primes have residue degree one, the output is a surface with
deck group $\operatorname{SL}_2(k_{\mathfrak p})\times\operatorname{SL}_2(k_{\mathfrak q})$;
it is not a product of modular curves.

## 5. The Hilbert--Blumenthal moduli datum

### 5.1 Why an action alone is insufficient

We take the exact tensor datum of Book 157, Theorem 3.3: ordered polarization module, positive
cone, PEL lattice, corrected cyclotomic-split neat level, and the $F$-defined tensor component.

### 5.2 Hilbert--Blumenthal abelian schemes

Representability, the determinant condition, and the universal tuple are imported from Book
Book 156, Theorem 4.2 and Book 157, Theorem 4.1.

### 5.3 Polarization pairings at coefficient primes

The perfect alternating pairings and their coefficient lines are exactly Book 156, Theorem 5.1.

### 5.4 Neat auxiliary level

The corrected principal level is at least three and obeys the local cyclotomic-splitting ledger
in Book 157, Theorem 4.1; neatness is not inferred from a generic rigidification.

### 5.5 The untwisted fine space

The selected tensor component is smooth, quasi-projective, fine, defined over $F$, and carries
the universal Hilbert--Blumenthal tuple. These are imported conclusions, not new results here.

## 6. Imposing the two twisted levels

### 6.1 The target data

The target and auxiliary residual representations, their coefficient primes, and their chosen
pairing-line isomorphisms are inserted into Book 156's paired-frame functor.

### 6.2 Descent as a product cocycle

The cocycle lands in the product of the two special-linear groups because both determinant
lines have been fixed. Book 156, Corollary 11.3 shows that twisting preserves geometric
monodromy.

### 6.3 Representability and the universal object

Book 156, Theorem 12.1 represents the product twist by a finite étale cover of the fine base and
provides its universal two-frame tuple.

**Theorem 6.1 (fine twisted PEL space; compatibility alias).** This is the representability and
smoothness part of Book 156, Theorem 12.1 on the corrected component of Book 157, Theorem 4.1.

## 7. Deformations, smoothness, and dimension

### 7.1 The tangent problem

The Hilbert determinant deformation calculation is owned by Book 156, Chapters 2--4.

### 7.2 Formal smoothness

Book 156, Theorem 4.2 proves smoothness of relative dimension $[M:\mathbf Q]$; finite étale
paired levels preserve it.

**Proposition 7.1 (compatibility alias).** The characteristic-zero base and its two-prime twist
are smooth of dimension $[M:\mathbf Q]$ by those imported theorems.

### 7.3 Why there is room

Positive dimension supplies local room around a supplied point. It does not establish local or
global nonemptiness.

## 8. Geometric components and monodromy

### 8.1 Three notions that must be separated

Arithmetic connectedness, geometric connectedness, and transitivity of each factor projection
are distinct assertions.

### 8.2 The monodromy criterion

Book 156, Theorem 11.2 requires full product monodromy, not two separate surjections.

**Theorem 8.1 (connectedness criterion; compatibility alias).** Under full product geometric
monodromy, Book 156, Theorem 11.2 and Corollary 11.3 make the paired-frame cover and every
determinant-compatible twist geometrically connected.

### 8.3 Verifying the hypothesis

Simultaneous congruence approximation and the finite exceptional set are imported from Book
156, Lemma 11.1 and Theorem 12.1.

### 8.4 Determinants and component stability

The corrected tensor component and determinant-compatible twist are supplied by Book 157,
Theorems 3.3 and 4.1. No Galois orbit of components is silently called geometrically connected.

## 9. Local points as comparison objects

### 9.1 The local design principle

Every conjunction must first be witnessed by one point of the same two-prime twist. Book 157,
Theorem 13.1 is the imported local existence package.

### 9.2 Good places

Use Book 157, Theorem 9.1, including its unramifiedness and good-base exclusions.

### 9.3 Archimedean places

Oddness is matched to paired real frames by Book 157, Proposition 4.2.

### 9.4 Places above the target characteristic

Use Book 157, Theorem 9.2 with its unramified odd-prime, prime-to-polarization, seed, and
permitted completion-extension hypotheses.

### 9.5 Places above the auxiliary characteristic

The same theorem is applied with the two coefficient primes exchanged; both frames remain on
one point.

### 9.6 Ramified primes and primes of the datum

Places outside Book 157's good, ordinary, nonordinary, or tensor-Tate ranges remain explicit
local-solvability hypotheses.

### 9.7 A worked pair of residual places

An ordinary factor at one coefficient prime and a local--local factor at the other are allowed
only when one PEL point with both exact generic frames witnesses the combined condition.

## 10. Local conditions are open

### 10.1 From a point to a neighborhood

The openness theorem is Book 157, Theorem 10.2.

### 10.2 Good reduction

Good residue tubes are imported from Book 157, Theorem 5.1.

### 10.3 Semistable reduction

The full-dimensional tensor-cusp chart and valuation shells are Book 157, Theorems 8.1--8.2.

### 10.4 Constancy of finite-flat comparison

Generic frames are locally constant on the finite étale generic cover; integral finite-flat
models remain separate marked objects.

### 10.5 The finite local set

Only finitely many local requirements are passed to arithmetic approximation, each with the
completion extension actually used to construct its witness.

## 11. Explicit local seeds

### 11.1 The Serre tensor construction

Book 157, Chapter 3 constructs the tensor seeds and proves they lie on the selected component.

### 11.2 Real and good seeds

These are Book 157, Chapters 4--5.

**Proposition 11.1 (real frame criterion; compatibility alias).** This is Book 157,
Proposition 4.2: at an odd coefficient prime a paired real frame exists exactly when complex
conjugation has determinant $-1$.

### 11.3 Ordinary and nonordinary seeds

These are Book 157, Chapters 6--7, with exact finite-flat admissibility retained.

### 11.4 Semistable seeds from Tate curves

These are Book 157, Chapter 8. Compatible nontrivial Kummer requirements must come from one Tate
class unless arbitrary finite splitting is explicitly permitted.

## 12. Persistence and simultaneous local conditions

### 12.1 Persistence under finite extension

We import Book 157, Proposition 11.1 and its warnings: good, ordinary, local--local, and finite
flat properties persist in the stated ranges, while exact valuation, nonsplitness, and a
nonzero Kummer class can change.

### 12.2 Intersections must have a witness

Nonempty opens around different points or on different components need not intersect.

### 12.3 Components and degeneracy loci

Book 157, Theorem 12.1 retains the selected component and avoids a proper closed degeneracy
locus only after a point outside it has been found.

### 12.4 The simultaneous-neighborhood theorem

**Theorem 12.1 (simultaneous local neighborhood; compatibility alias).** Book 157, Theorem 12.1 gives one nonempty open neighborhood carrying
all witnessed conditions. This locator is an interface alias and contains no new local proof.

## 13. The complete geometric package

### 13.1 Admissible two-prime moduli data

An admissible potential-modularity datum is the corrected tensor datum of Book 157, Theorem 3.3,
two monodromy-admissible primes satisfying Book 156, Theorem 12.1, two rank-two residual modules
with chosen pairing-line isomorphisms, and for each controlled place one local condition inside
the exact range of Book 157, Theorem 13.1. It also records all permitted completion extensions
and every proper degeneracy locus to be avoided.

### 13.2 The smooth connected cover theorem

**Theorem 13.1 (potential-modularity realization space).** An admissible datum determines a
smooth quasi-projective geometrically connected fine $F$-scheme $X$ of pure dimension
$[M:\mathbf Q]$, carrying a universal Hilbert--Blumenthal abelian scheme and pairing-preserving
isomorphisms

$$
V_{\mathfrak p}\simeq A[\mathfrak p],\qquad
V_{\mathfrak q}\simeq A[\mathfrak q].
\tag{13.1}
$$

**Proof.** Apply Book 157, Theorem 3.3 to select the corrected $F$-defined tensor component and
level. Book 156, Theorem 12.1 represents the determinant-compatible two-prime twist and proves
full product geometric monodromy. Book 157, Theorem 4.1 identifies the corrected fine model.
The product torsor is therefore smooth of the claimed dimension and geometrically connected.
$\square$

This is the genuinely application-specific construction: the two imported general packages are
instantiated with the target and auxiliary representations and their exact determinant data.

### 13.3 The local-open theorem

**Theorem 13.2 (potential-modularity specialization datum).** Under the local hypotheses in the
definition above, for every controlled place $v$ there is an explicitly permitted finite
extension $F'_v/F_v$ and a nonempty open

$$
\Omega_v\subset X(F'_v)
\tag{13.2}
$$

on which both frames, the corrected tensor component, the requested reduction behavior, and
every marked finite-flat or Kummer condition hold simultaneously. These opens, together with
the smooth geometrically connected $X$, form the exact geometric input for arithmetic
approximation.

**Proof.** This is Book 157, Theorem 13.1 and Corollary 13.2 applied to the $X$ of Theorem 13.1.
Every local extension and compatibility restriction in that theorem is retained. $\square$

### 13.4 Examples and counterexamples

Wrong determinant lines make the twist empty; factorwise monodromy can lie in a diagonal
subgroup; and a finite-flat representation need not be the torsion of a prescribed PEL seed.
Theorems 13.1--13.2 exclude none of these failures by terminology: each is ruled out by its
corresponding displayed hypothesis.

## 14. Disjointness and the exact handoff

### 14.1 The avoidance datum

Although this book does not construct a global point, it must state what a later field construction has to preserve. Let $L_V/F$ and $L_{V'}/F$ be the finite Galois extensions fixed by the kernels of the two representations. Let $D/F$ be a finite Galois extension containing both, together with every finite field used to define a component, detect an image, or carry descent data that must remain independent.

The geometric construction neither chooses $D$ nor proves the existence of a field disjoint from it. It exports $D$ as an avoidance input alongside the variety $X$ and the local opens $\Omega_v$. This ordering matters: all component and image fields must be entered before specialization, not discovered afterward.

### 14.2 What disjointness would preserve

**Lemma 14.1.** Let $r:G_F\to G$ have finite image, and let $L/F$ be the fixed field of its kernel. If a finite extension $F'/F$ satisfies $F'\cap L=F$, then

$$
r(G_{F'})=r(G_F). \tag{14.1}
$$

**Proof.** Since $L/F$ is Galois, the intersection condition gives

$$
\operatorname{Gal}(F'L/F')\simeq\operatorname{Gal}(L/F).
$$

The restriction map from $G_{F'}$ onto the group on the left is surjective. Identifying the group on the right with $r(G_F)$ proves that every element of the original image is attained after restriction. The reverse inclusion is immediate. $\square$

Consequently disjointness from $D$ would preserve the two residual images, hence absolute irreducibility and any projective-image property determined by those finite images. It would not by itself preserve a chosen local field. If a place $v$ splits completely in $F'$, every completion above it equals $F_v$ and the exact local representation and finite-flat model remain unchanged. More general completion extensions use the persistence ledger imported in Section 12.1 from Book 157, Chapter 11.

### 14.3 Root fields and normal closures

A closed point has a residue field $F'$ that need not be Galois over $F$. The condition $F'\cap D=F$ concerns that root field. Its normal closure $\widetilde F'$ may intersect $D$ even when $F'$ does not. Therefore (14.1) over $F'$ cannot be carried automatically to $\widetilde F'$.

Likewise, total reality of $F'$ says that every embedding of $F'$ is real; it gives no prescribed Galois group for the normal closure. Any later demand for a Galois or solvable extension is a stronger arithmetic problem, not an unnoticed consequence of the present moduli construction.

### 14.4 The output boundary

The exact output of this book is

$$
\boxed{
X/F\text{ smooth, quasi-projective, geometrically connected, fine};
\quad
\Omega_v\subset X(F_v')\text{ nonempty and condition-correct};
\quad
D/F\text{ recorded for avoidance}.}
\tag{14.2}
$$

It does not output a finite totally real extension, a rational point on $X$, an auxiliary representation of automorphic origin, an abelian variety over a global extension, an automorphic representation, or a modularity-lifting conclusion. If a later arithmetic theorem supplies a closed point $x$ with residue field $F'$ satisfying the prescribed local-algebra and avoidance conditions, pulling back the universal family would give

$$
A[\lambda]\simeq V|_{G_{F'}},
\qquad
A[\lambda']\simeq V'|_{G_{F'}}. \tag{14.3}
$$

Equation (14.3) is a conditional interpretation of a future point, not an existence assertion made here. Even then, it identifies residual torsion only. It does not identify an arbitrary lift of $V$ with a Tate module and does not transfer automorphy between primes.

## 15. Failure audit

### 15.1 Empty twists and false components

The paired twist is empty if either determinant line in (13.1) is wrong. Equality of characters without a chosen line isomorphism does not specify a paired frame. If the cocycle has nontrivial determinant relative to the universal multiplier, it permutes pairing components and cannot twist a single one.

Arithmetic connectedness is not geometric connectedness. A Galois orbit of geometric components may descend to a connected $F$-scheme. The cure is full product monodromy or an explicitly descended geometric component. Separate surjections to each special-linear factor do not suffice until common quotient couplings have been excluded.

### 15.2 Generic frames and integral models

In characteristic zero, $A[\lambda]$ and $A[\lambda']$ are finite étale, including over $p$-adic and $q$-adic fields. Their integral closures over the valuation ring need not be étale, and a generic basis does not determine a finite flat model. Ordinary, local--local, and Tate-extension claims must therefore be stated for actual finite locally free group schemes.

Finite flatness of a representation is also not an integral PEL-realization theorem: it does not identify a named finite-flat model with the kernel on a chosen abelian scheme. For the catalog's generic frame, the corrected tensor seed and a permitted common splitting extension suffice, while the original model continues to witness finite flatness after base change. An exact integral comparison, an unramified-only frame policy, or an externally fixed polarization class requires the stronger data imported in Chapters 9 and 11 from Book 157.

### 15.3 Separate local solutions

One HBAV realizing $V$ and another realizing $V'$ do not give a point of the two-prime cover. An ordinary seed and a separate nonordinary seed do not prove a common neighborhood. Nonempty opens on different components do not intersect. Every conjunction of local requirements must first be witnessed by one point carrying the whole tuple.

Local solvability after an unramified extension is not solvability over the original field. A later completion datum must contain the extension actually used. Exact valuations rescale under ramification, Kummer classes may split, and nonsplit tori may become split. These changes are limits on persistence, not defects in openness.

### 15.4 Smoothness, nonemptiness, and automorphy

Smoothness says infinitesimal deformations lift. It does not produce a rational point. Positive dimension supplies local room around an existing point; it does not prove that the selected twist has a point over a given completion. Geometric connectedness controls components of the cover; it does not establish local nonemptiness.

Finally, none of these geometric properties implies automorphy. The moduli space relates two residual torsion factors on one future abelian variety. Constructing auxiliary arithmetic data, producing the global point, applying modularity lifting, and transporting automorphy are later tasks. Keeping this boundary explicit is part of the theorem's correctness.

## 16. Conclusion

A residual representation enters the construction as a twisted paired-frame torsor. Its determinant identifies the Weil-pairing line on which the torsor can live. The Hilbert determinant condition, ordered polarization module, and neat auxiliary level then turn the ambient classification problem into a fine smooth variety with a universal abelian scheme.

Distinct coefficient primes provide two rank-two torsion factors on the same abelian variety without consuming deformation dimension. Full product monodromy, rather than two unrelated factorwise surjections, makes the simultaneous cover geometrically connected. Twisting changes arithmetic descent but leaves that geometric connectedness intact.

The corrected cyclotomic-split level, tensor component, local seeds, residue tubes, and tensor-cusp chart are the imported Book 157 package. This book's contribution is to place the two prescribed residual systems into that one package, verify the determinant and component match, and retain the permitted completion extensions in the exported specialization datum.

The final package is deliberately geometric: one smooth geometrically connected fine variety, its universal two-prime tuple, and component-correct nonempty local opens with precise persistence properties. Avoidance fields and completion requirements are exported as inputs to a later arithmetic construction. No global point, automorphy statement, or lifting conclusion has been smuggled across that boundary.
