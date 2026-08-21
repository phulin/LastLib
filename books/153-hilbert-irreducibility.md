# Hilbert Irreducibility and Arithmetic Approximation

## Contents

1. [Specialization as an arithmetic problem](#1-specialization-as-an-arithmetic-problem)
   - [From a moving equation to a field](#11-from-a-moving-equation-to-a-field)
   - [Good fibers and the discriminant boundary](#12-good-fibers-and-the-discriminant-boundary)
   - [Covers are the coordinate-free form](#13-covers-are-the-coordinate-free-form)
   - [Three failures to keep in view](#14-three-failures-to-keep-in-view)
2. [Thin sets and Hilbert subsets](#2-thin-sets-and-hilbert-subsets)
   - [Why a second notion of smallness is necessary](#21-why-a-second-notion-of-smallness-is-necessary)
   - [Basic Hilbert subsets](#22-basic-hilbert-subsets)
   - [Stability and its limits](#23-stability-and-its-limits)
   - [The Hilbert property](#24-the-hilbert-property)
   - [The thin--Hilbert dictionary](#25-the-thin--hilbert-dictionary)
3. [Hilbertian fields and equivalent forms](#3-hilbertian-fields-and-equivalent-forms)
   - [The field-level definition](#31-the-field-level-definition)
   - [One parameter, many parameters](#32-one-parameter-many-parameters)
   - [Polynomial, cover, and rational-point formulations](#33-polynomial-cover-and-rational-point-formulations)
   - [Regular extensions and constants](#34-regular-extensions-and-constants)
4. [Why number fields are Hilbertian](#4-why-number-fields-are-hilbertian)
   - [The proof in one view](#41-the-proof-in-one-view)
   - [Derangements detect proper subgroups](#42-derangements-detect-proper-subgroups)
   - [Frobenius classes on finite-field covers](#43-frobenius-classes-on-finite-field-covers)
   - [Good reduction and congruence tubes](#44-good-reduction-and-congruence-tubes)
   - [The specialization group](#45-the-specialization-group)
   - [The Hilbert irreducibility theorem](#46-the-hilbert-irreducibility-theorem)
   - [What the proof actually gives](#47-what-the-proof-actually-gives)
5. [Simultaneous specialization and Galois groups](#5-simultaneous-specialization-and-galois-groups)
   - [Finite intersections are the natural scale](#51-finite-intersections-are-the-natural-scale)
   - [The specialization group sits inside the generic group](#52-the-specialization-group-sits-inside-the-generic-group)
   - [Resolvents as subgroup detectors](#53-resolvents-as-subgroup-detectors)
   - [Decomposition groups in a specialized field](#54-decomposition-groups-in-a-specialized-field)
   - [A quadratic laboratory](#55-a-quadratic-laboratory)
   - [Symmetric-group specializations](#56-symmetric-group-specializations)
   - [Factorization, orbits, and intermediate fields](#57-factorization-orbits-and-intermediate-fields)
6. [Local constancy and arithmetic approximation](#6-local-constancy-and-arithmetic-approximation)
   - [Weak approximation](#61-weak-approximation)
   - [Why local conditions are open](#62-why-local-conditions-are-open)
   - [Krasner's lemma and factor stability](#63-krasners-lemma-and-factor-stability)
   - [From local algebras to global fields](#64-from-local-algebras-to-global-fields)
   - [Splitting, inertness, and ramification avoidance](#65-splitting-inertness-and-ramification-avoidance)
   - [Prescribed decomposition behavior](#66-prescribed-decomposition-behavior)
   - [Worked local factorization in a symmetric-group family](#67-worked-local-factorization-in-a-symmetric-group-family)
   - [Hilbert density versus thin-set density](#68-hilbert-density-versus-thin-set-density)
   - [Why this is not an unrestricted local-global theorem](#69-why-this-is-not-an-unrestricted-local-global-theorem)
7. [Linear disjointness and avoidance](#7-linear-disjointness-and-avoidance)
   - [Why irreducibility after base change is the right test](#71-why-irreducibility-after-base-change-is-the-right-test)
   - [Descent of a Hilbert condition from L to K](#72-descent-of-a-hilbert-condition-from-l-to-k)
   - [Galois closures and regular generic splitting fields](#73-galois-closures-and-regular-generic-splitting-fields)
   - [Avoiding finitely many extensions](#74-avoiding-finitely-many-extensions)
   - [Infinite extensions: the finite-subextension criterion](#75-infinite-extensions-the-finite-subextension-criterion)
   - [Structural infinite avoidance](#76-structural-infinite-avoidance)
   - [Preserving finite Galois images](#77-preserving-finite-galois-images)
   - [Intersection pitfalls in towers](#78-intersection-pitfalls-in-towers)
8. [Degree, signature, and Galois closure](#8-degree-signature-and-galois-closure)
   - [Degree is generic; signature is local](#81-degree-is-generic-signature-is-local)
   - [Archimedean connected components](#82-archimedean-connected-components)
   - [Constructing degree-n totally real fields](#83-constructing-degree-n-totally-real-fields)
   - [Full symmetric Galois closure](#84-full-symmetric-galois-closure)
   - [Prescribed signatures](#85-prescribed-signatures)
   - [Total reality with finite local conditions and disjointness](#86-total-reality-with-finite-local-conditions-and-disjointness)
9. [The geometric Hilbert property](#9-the-geometric-hilbert-property)
   - [Normal varieties and function fields](#91-normal-varieties-and-function-fields)
   - [Hilbert subsets on a variety](#92-hilbert-subsets-on-a-variety)
   - [What geometric irreducibility buys](#93-what-geometric-irreducibility-buys)
   - [Pulling back covers](#94-pulling-back-covers)
   - [The boundary before variety-point theorems](#95-the-boundary-before-variety-point-theorems)
10. [Worked arithmetic constructions](#10-worked-arithmetic-constructions)
    - [A thin-set failure made explicit](#101-a-thin-set-failure-made-explicit)
    - [A totally real cubic with symmetric Galois group](#102-a-totally-real-cubic-with-symmetric-galois-group)
    - [Prescribing several local partitions](#103-prescribing-several-local-partitions)
    - [A ramified local prescription](#104-a-ramified-local-prescription)
    - [An infinite sequence of independent fields](#105-an-infinite-sequence-of-independent-fields)
11. [Specializing finite étale covers](#11-specializing-finite-étale-covers)
    - [From a rational point to a finite algebra](#111-from-a-rational-point-to-a-finite-algebra)
    - [Local constancy in families](#112-local-constancy-in-families)
    - [The cover-specialization theorem](#113-the-cover-specialization-theorem)
    - [Galois covers and specialization homomorphisms](#114-galois-covers-and-specialization-homomorphisms)
    - [Prescribed decomposition and inertia](#115-prescribed-decomposition-and-inertia)
    - [Several covers and one point](#116-several-covers-and-one-point)
    - [Bounded-degree local data](#117-bounded-degree-local-data)
    - [Examples and boundary cases](#118-examples-and-boundary-cases)
12. [A simultaneous-conditions theorem](#12-a-simultaneous-conditions-theorem)
    - [Setting up compatible data](#121-setting-up-compatible-data)
    - [The packaged theorem](#122-the-packaged-theorem)
    - [Reading the local conclusions](#123-reading-the-local-conclusions)
    - [Finite and infinite avoidance in the package](#124-finite-and-infinite-avoidance-in-the-package)
    - [Existential and effective content](#125-existential-and-effective-content)
13. [The arithmetic freedom of specialization](#13-the-arithmetic-freedom-of-specialization)
    - [The hierarchy of conditions](#131-the-hierarchy-of-conditions)
    - [The roles of decomposition and inertia](#132-the-roles-of-decomposition-and-inertia)
    - [The roles of regularity and normality](#133-the-roles-of-regularity-and-normality)
    - [Conclusion](#134-conclusion)

## 1. Specialization as an arithmetic problem

### 1.1 From a moving equation to a field

Let $K$ be a number field. A polynomial

$$
f(T,X)\in K[T,X]
$$

may be viewed in two quite different ways. Over the rational function field $K(T)$ it defines one algebraic extension, obtained by adjoining a root of $f$. At a value $a\in K$ it gives an ordinary polynomial $f(a,X)$ and, when that polynomial is irreducible, a number field. The first object is geometric and generic; the second is arithmetic and concrete. Hilbert irreducibility is the bridge between them.

The bridge is needed because specialization can destroy nearly every feature one cares about. Degrees can fall when the leading coefficient vanishes. Distinct roots can collide when the discriminant vanishes. An irreducible polynomial can become reducible. Even if it remains irreducible, the Galois group of its splitting field can shrink. The elementary example

$$
X^2-T
$$

already shows the central issue: it is irreducible over $K(T)$, but its specialization at $a$ is reducible precisely when $a$ is a square in $K$. There are infinitely many good and bad values, and neither Zariski topology on the affine line separates them.

The aim of this book is not merely to prove that a good value exists. Arithmetic applications ask for one value satisfying many demands at once: prescribed neighborhoods in several completions, specified factorization patterns, avoidance of old fields, full generic Galois group, and real-root conditions. The decisive fact is that Hilbert conditions are compatible with finite local approximation. Once that compatibility has been proved, auxiliary extensions can be selected without pretending that independent local demands automatically glue.

Throughout, a specialization is taken only where all displayed coefficients are defined. When a polynomial in $K(T)[X]$ is used, we first clear denominators and then exclude their zeros. We also exclude zeros of the leading coefficient and, for separable questions, zeros of the discriminant. This finite exceptional set is never silently absorbed into the notation.

### 1.2 Good fibers and the discriminant boundary

Suppose

$$
f(T,X)=c_n(T)X^n+\cdots+c_0(T)
$$

is irreducible in $K(T)[X]$ and separable in $X$. There is a nonzero polynomial $d(T)\in K[T]$ such that, whenever $d(a)\ne0$, the specialization has degree $n$ and no repeated root. One may take $d$ to include the cleared denominators, $c_n$, and the $X$-discriminant of $f$.

Avoiding $d(a)=0$ solves only the geometric degeneration problem. It does not ensure irreducibility. For example, every $a=b^2\ne0$ avoids the discriminant of $X^2-T$ but gives two distinct rational roots. Nor does nonzero field discriminant imply that a finite-place extension is unramified: $X^2-p$ has distinct roots over characteristic zero but defines a ramified extension of $\mathbf Q_p$. The first discriminant cuts out the branch locus of a cover over a field; integral ramification asks whether its valuation is zero.

For a good value $a$, choose a root $\alpha_a$ and write

$$
K_a=K(\alpha_a).
$$

If $f(a,X)$ is irreducible, then $[K_a:K]=n$. This field need not be Galois. Its normal closure will be denoted $\widetilde K_a$. Confusing $K_a$ with $\widetilde K_a$ loses precisely the distinction between a transitive permutation representation and its full Galois group.

### 1.3 Covers are the coordinate-free form

The polynomial picture depends on a chosen primitive element. The underlying object is a finite cover. Let $X$ be an integral $K$-variety and let

$$
\pi:Y\longrightarrow X
$$

be dominant and generically finite of degree $n$. On function fields this means that $K(Y)/K(X)$ is finite of degree $n$. In characteristic zero it is automatically separable. After replacing $X$ by a nonempty open subset and $Y$ by its inverse image, one may arrange that $\pi$ is finite étale.

For $x\in X(K)$ in this open subset, the fiber $Y_x$ is the spectrum of a finite étale $K$-algebra of dimension $n$. It is connected exactly when that algebra is a field. Thus

$$
\text{irreducible specialized polynomial}
\quad\longleftrightarrow\quad
\text{connected specialized fiber}.
$$

The adjective _connected_ is important. A rational point of $Y_x$ is a degree-one component, but its absence does not imply connectedness when $n>2$. For example, a fiber could be the product of fields of degrees $2$ and $3$, with no rational factor and still not be a field.

Normality will later let us speak cleanly about decomposition groups of valuations in function fields. Geometric irreducibility serves a different purpose: it says that a variety stays irreducible after extending the constant field to an algebraic closure. An integral cover can fail to be geometrically integral because it secretly contains a constant extension. These hypotheses must not be exchanged.

### 1.4 Three failures to keep in view

Three examples locate the theorem's boundary.

First, specialization need not preserve degree at branch points. The cover $X\mapsto X^2$ has degree two, but the fiber over $0$ is nonreduced. Separability away from the branch locus does not repair the fiber at the branch locus.

Second, Zariski density is too weak. The squares in $\mathbf Q$ are Zariski dense in $\mathbf A^1$, because every proper closed subset is finite, yet every square is a bad specialization for $X^2-T$. The exceptional set is arithmetically small in a sense that the Zariski topology cannot see.

Third, a statement about $K$-rational points cannot be transferred indiscriminately to closed points. A closed point $x$ has residue field $k(x)$, and its fiber is an algebra over $k(x)$, not over $K$. Hilbert irreducibility selects rational parameters and thereby produces extensions through the fiber; it is not a theorem that all closed fibers over all residue fields behave alike.

These failures motivate thin sets, the language designed to measure exceptional rational points.

## 2. Thin sets and Hilbert subsets

### 2.1 Why a second notion of smallness is necessary

On affine space over an infinite field, every infinite subset of a line can be Zariski dense. Reducible specializations often form infinite images of algebraic maps, as the squares do under $u\mapsto u^2$. The right notion of exceptional set must therefore remember not just algebraic equations on the base, but also rational points arriving from nontrivial finite covers.

Let $X$ be an integral variety over a field $K$. A subset $A\subset X(K)$ is **thin** if it is contained in a finite union of sets of the following two kinds.

- A set of **type I** is $Z(K)$ for a proper closed subvariety $Z\subsetneq X$.

- A set of **type II** is $\pi(Y(K))$, where $Y$ is an integral $K$-variety and $\pi:Y\to X$ is a dominant generically finite separable morphism of degree at least two.

It is harmless to shrink both varieties to dense opens when discussing type II sets: the discarded rational points lie in type I sets. The separability condition rules out a purely inseparable phenomenon that has no relevance over number fields but matters over general fields. The degree condition prevents the identity map from making every subset thin.

The image need not itself be Zariski closed or locally nowhere dense. Squares in $K$ are the type II image of $u\mapsto u^2$. Over $\mathbf Q$, positive rational squares are dense in $\mathbf R_{>0}$. Thinness measures failure of generic arithmetic freedom, not ordinary topological sparseness.

### 2.2 Basic Hilbert subsets

The complement of bad specialization sets is packaged positively. Let

$$
f_1(\mathbf T,X),\ldots,f_r(\mathbf T,X)\in K(\mathbf T)[X]
$$

be irreducible and separable in $X$, where $\mathbf T=(T_1,\ldots,T_m)$. Let $g(\mathbf T)\in K[\mathbf T]$ be nonzero and include all denominators, leading coefficients, and discriminants that must be avoided. The associated **basic Hilbert subset** is

$$
H_K(f_1,\ldots,f_r;g)
=\left\{\mathbf a\in K^m:
g(\mathbf a)\ne0,
f_i(\mathbf a,X)\text{ is irreducible for every }i
\right\}.
$$

The definition contains several polynomials from the beginning because arithmetic constructions rarely impose just one generic connectedness condition. Intersections behave exactly as hoped:

$$
H_K(f_1,\ldots,f_r;g)\cap
H_K(h_1,\ldots,h_s;q)
=H_K(f_1,\ldots,f_r,h_1,\ldots,h_s;gq).
$$

A **Hilbert subset** is any subset that contains a set of the form $H_K(f_1,\ldots,f_r;g)\setminus Z(K)$ for some proper closed subset $Z\subsetneq\mathbf A^m_K$. On a variety $X$, one makes the same definition using finitely many dominant generically finite separable covers, asks that their fibers be connected on a common finite étale locus, and may again remove a proper closed subset. This upward-closed convention is convenient: enlarging a Hilbert subset cannot destroy the existence statements for which it is used.

Why does irreducibility correspond to avoiding a thin image? If $f(\mathbf T,X)$ has degree $n$ and a good specialization factors with a factor of degree $d$, then the coefficients of that factor define a rational point on a finite cover parameterizing degree-$d$ factors. There are only finitely many $d$, so reducible specializations lie in a finite union of type II images, together with the type I degeneration locus. Conversely, the image of a degree-$n$ cover can be detected by a primitive-element polynomial whose specialization has a linear factor. Applying the same construction to suitable intermediate covers gives the general dictionary.

### 2.3 Stability and its limits

Thin sets are closed under taking subsets and finite unions. A proper closed subset is thin, and removing one from a Hilbert subset leaves a Hilbert subset. A birational map between integral varieties carries thin sets to thin sets after the indeterminacy and exceptional loci are placed into type I sets. Consequently, the Hilbert property is birationally invariant.

Finite separable base change requires more care. If $L/K$ is finite and $A\subset\mathbf A^m(K)$ is cut out by finitely many Hilbert conditions over $L$, the set of $K$-points at which those conditions fail is thin over $K$. One sees this by taking all $K$-conjugates, using norms to descend the excluded divisors, and viewing the relevant finite $L$-covers through restriction of scalars. This descent principle will be the mechanism behind linear disjointness.

Several tempting stability statements are false without hypotheses. The image of a type I set under a projection can fill the target: the proper closed subset $\{0\}\times\mathbf A^1\subset\mathbf A^2$ maps onto $\mathbf A^1$. Thus arbitrary morphisms do not preserve thinness. Likewise, inverse images under a constant map say nothing. Dominance and the comparison of generic dimensions are essential whenever thinness is transported.

Products behave in the direction most often needed, but the constant fields must not change under the product. If $A\subset X(K)$ is thin and $Y$ is geometrically integral, then $A\times Y(K)$ is thin in $(X\times Y)(K)$. Indeed, after base change by $Y$, each dominant degree-at-least-two cover used to define $A$ remains generically integral of the same degree. A finite union of such coordinatewise exceptional sets remains thin. Without geometric integrality a constant extension in a type II cover can split after forming the product, so the unqualified assertion is unsafe. This gives a quick reduction from several parameters to one generic condition, although later we will use a sharper specialization argument that also retains local neighborhoods.

### 2.4 The Hilbert property

An integral $K$-variety $X$ has the **Hilbert property** if $X(K)$ is not thin in $X$. Equivalently, every finite collection of type II covers leaves a rational point outside their images and outside any prescribed proper closed subset. Affine $m$-space has the Hilbert property precisely when its rational points cannot be exhausted by finitely many nontrivial covers and closed subsets.

This is not a formal consequence of Zariski density. Nor does every variety over a Hilbertian field have the Hilbert property. A curve with only finitely many rational points plainly does not. Rational varieties do have it once affine space does, by birational invariance. This distinction will matter in the geometric formulation: Hilbert irreducibility supplies a powerful theorem on affine space and rational varieties, not an automatic source of rational points on every variety.

### 2.5 The thin--Hilbert dictionary

The two languages are exact complements on affine space.

**Proposition 2.1.** Let $K$ be a field of characteristic zero and let $A\subset\mathbf A^m(K)$.

1. The complement of a basic Hilbert subset is thin.
2. If $A$ is thin, there is a basic Hilbert subset disjoint from $A$.

**Proof strategy.** For the first direction, parameterize factors of each specialized polynomial. For the second, replace every type II map by a finite cover on a dense open and force its fiber to be connected. A connected fiber of degree greater than one has no rational point, so the chosen base point cannot lie in the image.

**Proof.** Consider first a polynomial $f(\mathbf T,X)$ of degree $n$. Away from its discriminant and leading coefficient, a reducible specialization has a factor of some degree $d$ with $1\le d<n$. Write a hypothetical monic factor and cofactor with unknown coefficients and equate coefficients in their product. The resulting factor scheme is finite over a dense open of parameter space: a separable polynomial has only finitely many subsets of roots. Each irreducible component that dominates the base has generic degree greater than one because $f$ is generically irreducible. Components that do not dominate and all deleted loci contribute type I sets. Taking the finite union over $d$ and over finitely many polynomials proves part 1.

For part 2, write $A$ inside a finite union of type I sets $Z_j(K)$ and images $\pi_i(Y_i(K))$. Remove the $Z_j$ and shrink the base so that every $\pi_i$ is finite étale. Normalize $Y_i$ and discard nondominating components. Impose the Hilbert condition that every remaining generic component have connected fiber. Since its degree is at least two, a connected fiber is the spectrum of a field of degree at least two and has no $K$-rational point. Hence the selected base point is outside every $\pi_i(Y_i(K))$. The common connected-fiber locus is a basic Hilbert subset disjoint from $A$. $\square$

This proposition explains why finite unions are essential. The factor schemes and the list of covers are finite. For a countable union of thin sets there need not be one basic Hilbert subset avoiding all of them.

## 3. Hilbertian fields and equivalent forms

### 3.1 The field-level definition

An infinite field $K$ is **Hilbertian** if, for every irreducible polynomial

$$
f(T,X)\in K(T)[X]
$$

that is separable in $X$, there are infinitely many $a\in K$ for which $f(a,X)$ is defined and irreducible of the same degree.

Infinitude is included to eliminate a nuisance rather than add strength. Once one good specialization theorem is known with avoidance of a nonzero polynomial, any finite set of parameters may be included among the zeros to avoid. For number fields we will prove much more: good parameters are dense in every finite product of nonempty local open sets.

Separability is indispensable over imperfect fields. A purely inseparable polynomial can have behavior controlled by $p$th powers rather than by finite étale covers. Number fields have characteristic zero, so every irreducible polynomial is separable; we retain the word because it identifies the geometry doing the work.

### 3.2 One parameter, many parameters

The one-parameter definition implies the corresponding assertion for $K(T_1,\ldots,T_m)$, but a naive induction would be circular: applying Hilbert irreducibility to $T_m$ while leaving the other parameters transcendental would assume that $K(T_1,\ldots,T_{m-1})$ is already Hilbertian. The bridge is a line-selection lemma whose proof is algebraic rather than Hilbertian.

We first place the approximation input before any use of it.

**Theorem 3.1 (weak approximation).** Let $K$ be a number field and let $S$ be a finite set of
pairwise distinct places. The diagonal map

$$
K\longrightarrow\prod_{v\in S}K_v
$$

has dense image, and the same is true coordinatewise for $K^m$.

**Proof.** At the finite places, shrink the prescribed neighborhoods to congruence classes
modulo powers of the corresponding distinct prime ideals. After clearing one common
denominator, the Chinese remainder theorem gives a class $c+I$, where $I$ is a nonzero
fractional ideal, all of whose elements satisfy those congruences. Under the Archimedean
embedding $K\hookrightarrow K_\infty$, the image of $I$ is a full lattice $\Lambda$.

Let $M$ be the product of the rational primes below the selected finite places. Choose arbitrarily
large integers $N\equiv1\pmod M$. Then $N$ is a unit at every selected finite place, so every
element of $c+N^{-1}I$ still satisfies the finite congruences. If $P$ is a bounded fundamental
parallelepiped for $\Lambda$ and $t\in K_\infty$ is the tuple of Archimedean targets, choose
$\lambda\in\Lambda$ with $N(t-c)-\lambda\in P$. The point $c+\lambda/N$ differs from $t$ by an
element of $N^{-1}P$, which lies in every prescribed Archimedean neighborhood once $N$ is large.
This proves density; applying the argument in each coordinate proves the assertion for $K^m$.
$\square$

Chapter 6 will restate this theorem and develop the refinements needed for local algebras. We
have proved it here so that neither the line-selection argument nor the proof of Hilbert
irreducibility depends on a later section.

**Lemma 3.2 (affine-line specialization).** Let $K$ be an infinite field of characteristic zero, and let

$$
E_1,\ldots,E_r/K(T_1,\ldots,T_m)
$$

be finite separable field extensions. There is a nonempty Zariski-open set of affine lines

$$
T_i=a_i+b_iU
$$

with the following property. Choose a primitive-element equation for each $E_j$, clear its
denominators, and restrict that equation to the line. The resulting polynomial is irreducible
over $K(U)$ and has its generic degree. Equivalently, if the extensions are represented by
finite integral covers of a common open of $\mathbf A^m_K$, the inverse image of the generic
point of the line is integral. If $K$ is a number field, the coefficients
$(\mathbf a,\mathbf b)$ may simultaneously be chosen in any prescribed finite product of
nonempty local open sets.

The formulation through equations or covers is essential. When $m>1$, substitution along a
line is not a homomorphism from the entire field $K(T_1,\ldots,T_m)$ to $K(U)$, because a line
satisfies algebraic relations. It becomes a legitimate pullback only after one chooses a model
on an open subset and excludes lines on which a required denominator vanishes identically.

**Proof strategy.** First remove the constant field of each extension. The resulting cover is
geometrically integral. A special case of Bertini irreducibility says that its inverse image over
a general line is geometrically integral. The conjugate geometric components then descend to an
integral cover over $K$.

**Proof.** We first prove the Bertini statement being used. Let $k$ be algebraically closed of
characteristic zero, and let $Z$ be a geometrically integral $d$-fold with a dominant
generically finite map to $\mathbf P^d_k$. If $d\ge2$, the inverse image of a general hyperplane
is geometrically integral. Indeed, pass to the normalization of a projective graph of the map
and choose a general pencil of hyperplanes. Its codimension-two base locus meets the smooth
étale locus of the map. After blowing up the base ideal and normalizing, the pencil gives a
proper morphism

$$
p:\widetilde Z\longrightarrow\mathbf P^1_k.
$$

At a smooth transverse base point, the exceptional line maps isomorphically to $\mathbf P^1$,
so $p$ has a section. In the Stein factorization

$$
\widetilde Z\longrightarrow C\longrightarrow\mathbf P^1,
$$

the finite map $C\to\mathbf P^1$ consequently has a section. Since $C$ is integral, the induced
finite extension of function fields admits a retraction and must have degree one. Thus the
generic fiber of $p$ is connected. It is also normal, being obtained by localizing the normal
scheme $\widetilde Z$, so it is integral. The equality $C=\mathbf P^1$ says exactly that
$k(\mathbf P^1)$ is algebraically closed in $k(\widetilde Z)$. In characteristic zero the
resulting function-field extension is separable and therefore regular, which makes the generic
fiber geometrically integral. Geometric integrality is open in this proper family after deleting
the nonflat locus. Hence a general member of the pencil is geometrically integral, and the same
is true of a general hyperplane. Repeating the argument $d-1$ times proves that the inverse image
of a general projective line is geometrically integral. Removing its point at infinity gives the
corresponding assertion for affine lines.

Now represent $E_j$ by the normalization $Y_j$ of a common nonempty open of
$\mathbf A^m_K$. Let $C_j$ be the algebraic closure of $K$ in $E_j$. A component of
$(Y_j)_{C_j}$ has a geometrically integral function field, because $C_j$ is algebraically closed
in $E_j$ and the extension is separable. Apply the proved line statement to that component.
The good lines form a nonempty open over $C_j$. Intersect all its conjugates in a normal closure
of $C_j/K$ and descend the intersection; this produces a nonempty open of the line-parameter
space over $K$. Also exclude lines contained in the boundary of the chosen model or on which
two conjugate components coalesce.

On any remaining line, every geometric component stays integral and the components are still
permuted transitively by the constant-field embeddings. Their descent is therefore integral:
a decomposition over $K(U)$ would base change to a nonempty proper union of components stable
under the transitive action. A primitive-element equation consequently remains irreducible of
its generic degree.

Finally, over a number field a proper algebraic subset has empty interior in every product of
finitely many local open sets. Choose a local point of the box off one nonzero defining
polynomial and shrink around it; Theorem 3.1 then supplies a $K$-point in that smaller box, still
off the closed subset. Thus the
line coefficients can retain all prescribed local restrictions. $\square$

Once such a line is chosen, form the compositum of the finitely many pulled-back extensions in
one algebraic closure of $K(U)$. It is a finite separable field extension. Applying the
one-variable definition to a primitive-element polynomial for that compositum supplies $u\in K$
for which the compositum fiber, and hence every subextension fiber, is connected. Then
$(a_i+b_iu)_i$ is the desired point of $K^m$. To retain a prescribed local box, choose each local
$\mathbf a_v$ inside that box and choose line coefficients in small neighborhoods of these data
using the final clause of the lemma. Then $\mathbf a+\mathbf b u$ stays in the box for $u$ in a
sufficiently small neighborhood of $0$ at every prescribed place. The one-variable approximation
theorem can impose those neighborhoods on $u$.

This compositum argument also proves the simultaneous-polynomial formulation used in the
definition of a basic Hilbert subset. Together with the factor-cover dictionary of Section 2.5,
it shows without circularity that a finite union of thin sets cannot exhaust affine space over a
Hilbertian field.

### 3.3 Polynomial, cover, and rational-point formulations

For an infinite field $K$, the following statements are equivalent.

1. $K$ is Hilbertian.
2. Every basic Hilbert subset of $\mathbf A^m(K)$ is nonempty, for every $m\ge1$.
3. For every integral finite separable cover $Y\to U$ of degree at least two, with $U$ a nonempty open of affine space, there is $u\in U(K)$ for which the fiber is connected.
4. Affine space has the Hilbert property.

Here “integral cover” means that the total function field is a field. It need not be geometrically integral; constant extensions are permitted. In formulation 3 a connected fiber has residue algebra a field of full degree, not merely no rational point.

The implications from polynomials to covers and back use primitive elements on a dense affine open. The passage between connected fibers and thin images uses the factor-parameter spaces described in Section 2.2. Finally, a finite union of covers may be replaced by the simultaneous connectedness conditions; it should not be replaced blindly by their fiber product, because the fiber product can be disconnected even when each individual cover is connected.

### 3.4 Regular extensions and constants

A finite extension $E/K(\mathbf T)$ is **regular over $K$** if $E\cap\overline K=K$ inside a common algebraic closure and $E/K(\mathbf T)$ is separable. Equivalently in characteristic zero, the corresponding normal variety is geometrically integral over $K$.

Regularity solves a future problem: it guarantees that the generic extension is linearly disjoint from every finite constant extension $L/K$. It is not required merely to state Hilbert irreducibility. For instance, if $C/K$ is a finite extension, the constant cover

$$
\operatorname{Spec}C\times\mathbf A^1\longrightarrow\mathbf A^1
$$

is integral but not geometrically integral over $K$. Every fiber is $\operatorname{Spec}C$, hence connected. A proof of Hilbert irreducibility that silently assumes geometric connectedness would fail to cover this elementary case.

Let $E/K(T)$ be finite Galois, let

$$
C=E\cap\overline K,\qquad
G=\operatorname{Gal}(E/K(T)),\qquad
N=\operatorname{Gal}(E/C(T)).
$$

Then $C/K$ is finite Galois, $N$ is the geometric Galois group, and restriction gives an exact sequence

$$
1\longrightarrow N\longrightarrow G\longrightarrow
\operatorname{Gal}(C/K)\longrightarrow1.
$$

Thus $G/N\cong\operatorname{Gal}(C/K)$. The proof for number fields must preserve both layers. Auxiliary primes splitting in $C$ will detect elements of $N$, while every good specialization automatically retains the constant quotient.

## 4. Why number fields are Hilbertian

### 4.1 The proof in one view

We now prove the main theorem rather than treating it as an existence oracle. The argument combines four ideas.

1. Replace an irreducible polynomial by its Galois closure over $K(T)$.
2. List the maximal subgroups in which a smaller specialization group could lie.
3. At one auxiliary finite place for each such subgroup, use a reduction of the cover to force a Frobenius element that cannot lie in that subgroup.
4. Use weak approximation to choose one parameter meeting all auxiliary congruences and any previously prescribed local neighborhoods.

The proof is simultaneously geometric and valuation-theoretic. Geometry turns a polynomial into a finite étale cover. Reduction over finite residue fields supplies Frobenius classes. Valuations make those classes stable under congruent lifts. Group theory then converts finitely many local witnesses into equality of the global specialization group with the generic group.

Two input lemmas will be developed first. The first says that a proper subgroup can be detected by an element with no fixed point on a coset space. The second is finite-field Chebotarev for a curve. Its square-root error is used only to guarantee existence once the residue field is large.

### 4.2 Derangements detect proper subgroups

**Lemma 4.1 (derangement lemma).** Let a finite group $H$ act transitively on a finite set $\Omega$ with $|\Omega|>1$. Some $h\in H$ fixes no point of $\Omega$.

**Proof strategy.** Count fixed pairs in two orders. Transitivity makes the average number of fixed points equal to one, while the identity fixes more than one point. Some other element must therefore contribute fewer than one.

**Proof.** Let

$$
P=\{(h,\omega)\in H\times\Omega:h\omega=\omega\}.
$$

For each $\omega$, exactly $|H|/|\Omega|$ elements fix it, so $|P|=|H|$. Hence

$$
\frac1{|H|}\sum_{h\in H}|\Omega^h|=1.
$$

The identity contributes $|\Omega|>1$. If every element fixed at least one point, the average would exceed one. Thus some element has no fixed point. $\square$

Apply the lemma to $G$ acting on $G/M$. An element fixes a coset $gM$ exactly when it belongs to $gMg^{-1}$. Thus, for each proper subgroup $M\subsetneq G$, there exists an element outside the union of the conjugates of that particular $M$. No single element is being asserted to avoid the conjugates of all proper subgroups simultaneously.

We need a relative version. Let $N\triangleleft G$ and suppose $MN=G$. Then $N$ acts transitively on $G/M$: the equality $G=NM$ says every coset has a representative in $N$. Lemma 4.1 therefore supplies

$$
\gamma_M\in N
\quad\text{with}\quad
\gamma_M\notin\bigcup_{g\in G}gMg^{-1}.
$$

This relative form is what allows the geometric group $N$ to detect all proper subgroups of $G$ that still surject onto the constant quotient $G/N$.

### 4.3 Frobenius classes on finite-field covers

Let $k=\mathbf F_q$, let $U$ be a nonempty open subset of the affine line, and let $V\to U$ be a connected finite étale Galois cover with group $H$. Assume $V$ is geometrically connected over $k$. For $u\in U(k)$ and a geometric point $v$ above it, arithmetic Frobenius $x\mapsto x^q$ acts on the fiber. Relative to $v$ it determines an element of $H$, well defined up to conjugacy. We denote its conjugacy class by $\operatorname{Frob}_u$.

**Theorem 4.2 (finite-field Chebotarev for a curve).** For every conjugacy class $\mathcal C\subset H$,

$$
\#\{u\in U(k):\operatorname{Frob}_u=\mathcal C\}
=\frac{|\mathcal C|}{|H|}q+O_{V/U}(q^{1/2}).
$$

In particular, if $q$ is sufficiently large in terms of a fixed integral model of the cover, every conjugacy class occurs.

**Proof strategy.** Twist the cover so that rational points on the twist correspond to points downstairs with the chosen Frobenius class. A geometrically connected curve has $q+O(q^{1/2})$ rational points after smooth projective completion. Divide by the number of points in a fiber and restore the finitely many omitted branch points.

**Proof.** Choose $c\in\mathcal C$. Over $\bar k$, the cover has deck group $H$, and the $H$-action is defined over $k$. Twist the descent datum by the cocycle that sends arithmetic Frobenius to $c^{-1}$. This produces a $k$-form $V^{(c)}$ of the same geometric curve. With this choice of inverse, a point of $V^{(c)}(k)$ is a geometric point $v$ satisfying

$$
\operatorname{Frob}_q(v)=c\cdot v.
$$

Its image $u$ has Frobenius conjugate to $c$. Conversely, if $\operatorname{Frob}_u$ is conjugate to $c$, exactly $|C_H(c)|$ choices in the geometric fiber satisfy the displayed equation. Consequently, the count on the étale opens is exact:

$$
|V^{(c)}(k)|
=|C_H(c)|\,\#\{u\in U(k):\operatorname{Frob}_u=\mathcal C\}.
$$

The twist is geometrically isomorphic to $V$, hence geometrically connected. If its smooth projective completion has genus $g$, the Hasse--Weil bound for curves, proved earlier in the local library from Jacobian Frobenius and Rosati positivity, gives

$$
|\overline {V^{(c)}}(k)|=q+1+O(2gq^{1/2}).
$$

Removing the bounded set of points outside the étale open changes this estimate by $O_{V/U}(1)$. Since $|\mathcal C|=|H|/|C_H(c)|$, division gives the stated main term. The genera and the number of omitted points are bounded in a fixed model, so the error is uniform for its good reductions. This Hasse--Weil estimate is the only weight-theoretic input in the proof of Hilbert irreducibility; everything else in the argument is finite-cover geometry, local-field theory, elementary group theory, and weak approximation. $\square$

The arithmetic Frobenius convention agrees with the earlier local convention: it acts on the residue field by $x\mapsto x^q$. Replacing it by geometric Frobenius would invert every class. Since inversion preserves the property of avoiding a subgroup, the Hilbertian conclusion is convention-independent, but local Galois prescriptions are not.

### 4.4 Good reduction and congruence tubes

Let $E/K(T)$ be a finite Galois extension. Normalize an open subset $U\subset\mathbf A^1_K$ in $E$ and remove the branch locus. This gives a finite étale Galois cover

$$
V\longrightarrow U
$$

with group $G$. After inverting finitely many primes of $\mathcal O_K$, the cover spreads out to a finite étale cover of a smooth relative curve. At every remaining finite place $v$, reduction gives a finite étale cover over the residue field $k_v$ with the same degree and group action.

Suppose $v$ splits completely in the constant field $C$. Then the reduction of the geometric component has constant field exactly $k_v$ for all but finitely many $v$; geometric connectedness is preserved by good reduction. Theorem 4.2 therefore realizes every desired conjugacy class in $N=\operatorname{Gal}(E/C(T))$ once $|k_v|$ is large enough.

There are infinitely many suitable split places, and the special case needed here has an
elementary proof. Choose an integral primitive element $\theta$ for the Galois extension $C/K$
and let $h\in\mathcal O_K[X]$ be its monic minimal polynomial. We first recall Schur's elementary
lemma over $\mathbf Z$: a nonconstant polynomial $H\in\mathbf Z[X]$ has values divisible by
infinitely many rational primes. If only $p_1,\ldots,p_s$ occurred, choose $b$ with
$d=H(b)\ne0$ and enlarge the list by the prime divisors of $d$. For $a=b+d^2t$ one has

$$
H(a)=d(1+dq_t),\qquad q_t\in\mathbf Z.
$$

For a sufficiently large integer $t$, the second factor is an integer of absolute value greater
than one and is congruent to $1$ modulo every prime dividing $d$. It has a prime divisor outside
the list, a contradiction.

Apply this lemma to the integer polynomial

$$
H(T)=N_{K/\mathbf Q}(h(T))
=\prod_{\sigma:K\hookrightarrow\mathbf C}\sigma(h)(T).
$$

It is nonconstant and lies in $\mathbf Z[T]$. Every rational prime dividing a nonzero value
$H(t)$ lies below a prime ideal of $\mathcal O_K$ dividing $h(t)$. Hence the values of $h$ are
divisible by infinitely many prime ideals. This norm argument is necessary: in a number ring,
large Archimedean size does not imply that an element is a nonunit.

Discard the finitely many primes dividing the discriminant of $h$ or the index of
$\mathcal O_K[\theta]$ in $\mathcal O_C$. If such a remaining prime $v$ divides a value $h(a)$,
then $h$ has a simple linear factor modulo $v$, so there is a prime of $C$ above $v$ with residue
degree one. Because $C/K$ is Galois and $v$ is unramified, all primes above $v$ have the same
residue degree and ramification index. They therefore all have $e=f=1$, and $v$ splits
completely. This supplies infinitely many split places outside every prescribed finite set, with
arbitrarily large residue fields.

Now choose $\bar a\in U(k_v)$ having Frobenius class $\mathcal C$. Every $a\in K$ sufficiently close to a chosen lift of $\bar a$ has the same reduction. The specialized finite étale algebra then has an unramified local factor whose arithmetic Frobenius is in $\mathcal C$. In valuation language, the coefficients are integral, the discriminant is a unit, and Hensel lifting identifies the factorization of the residue polynomial with the unramified factors upstairs. Thus a residue class modulo $v$ is an open **congruence tube** on which the required Frobenius witness persists.

### 4.5 The specialization group

Take $a\in U(K)$. The fiber $V_a$ is a finite étale $G$-algebra. Choose one connected component, with residue field $F_a$. Its stabilizer $D_a\subset G$ acts faithfully on $F_a$, and

$$
\operatorname{Gal}(F_a/K)\cong D_a.
$$

The notation is deliberately reminiscent of a decomposition group: $D_a$ is the decomposition group of a place of $E$ above the valuation $T-a$ of $K(T)$. Because $a$ lies off the branch locus, its inertia group is trivial. The number of connected components is $[G:D_a]$.

Constants cannot disappear. The component field contains a copy of $C$, and restriction gives a surjection

$$
D_a\longrightarrow G/N.
$$

Indeed, the valuation $T-a$ is trivial on $C$, so reduction embeds $C$ into the residue field
$F_a$. The unramified residue extension $F_a/K$ is Galois with group $D_a$. Since $C/K$ is
Galois, every $K$-automorphism of $C$ extends to $F_a$, and the restriction map is surjective.
Equivalently, $D_aN=G$. When $E/K(T)$ is regular, $N=G$ and this assertion is empty; in the
nonregular case it is the step that retains the constant quotient.

If a finite place $v$ belongs to one of the congruence tubes constructed above, the decomposition group at a place of $F_a$ above $v$ is a subgroup of $D_a$. Its unramified Frobenius, transported into $G$, belongs to the prescribed conjugacy class. Different choices of the component or the prime above $v$ conjugate the element, which is why classes rather than individual elements are the invariant data.

### 4.6 The Hilbert irreducibility theorem

**Theorem 4.3 (Hilbert irreducibility with local approximation).** Let $K$ be a number field. Let $S$ be a finite set of places, and for each $v\in S$ let $\Omega_v\subset K_v$ be nonempty and open. If

$$
f_1(T,X),\ldots,f_r(T,X)\in K(T)[X]
$$

are irreducible and separable in $X$, and $g(T)\in K[T]$ is nonzero, then there exists $a\in K$ such that

$$
a\in\Omega_v\quad(v\in S),\qquad g(a)\ne0,
$$

and every $f_i(a,X)$ is irreducible of its generic degree. In fact the set of such $a$ is dense in $\prod_{v\in S}K_v$ and infinite.

**Proof strategy.** It suffices to handle one common Galois closure, because finitely many conditions can be encoded by the compositum and by the maximal subgroups relevant to each permutation action. For that Galois cover, force elements excluding every possible proper specialization group. Auxiliary places are chosen outside $S$, so weak approximation can meet their congruence tubes without disturbing the original local opens.

**Proof.** Begin with one finite Galois extension $E/K(T)$ containing the splitting fields of all the $f_i$. Let $G$, $C$, and $N$ have the meanings of Section 3.4. For each $i$, $G$ acts transitively on the roots of $f_i$. A subgroup $D\subset G$ preserves irreducibility of every $f_i$ exactly when it is transitive in each of these actions.

For the stronger conclusion $D=G$, choose representatives $M_1,\ldots,M_s$ for the $G$-conjugacy classes of maximal proper subgroups satisfying $M_jN=G$. By the relative derangement lemma choose

$$
\gamma_j\in N\setminus\bigcup_{g\in G}gM_jg^{-1}.
$$

For each $j$, choose a distinct large finite place $w_j\notin S$ that splits completely in $C$, is a place of good reduction, and whose residue cover realizes the conjugacy class of $\gamma_j$. Section 4.4 supplies a nonempty congruence tube $\Theta_j\subset K_{w_j}$ on which that class occurs.

Weak approximation, proved in Theorem 3.1, gives

$$
a\in K\cap
\left(\prod_{v\in S}\Omega_v\right)
\cap\left(\prod_{j=1}^s\Theta_j\right),
$$

and we may simultaneously avoid the finitely many zeros of $g$ and all branch and denominator loci. Let $D_a$ be a specialization group. We know $D_aN=G$. If $D_a\ne G$, it lies in a maximal proper subgroup $M$. Necessarily $MN=G$, so $M$ is conjugate to some $M_j$. But $D_a$ contains an element conjugate to $\gamma_j$, while the entire conjugacy class of $\gamma_j$ avoids every conjugate of $M_j$. This is impossible. Hence $D_a=G$.

The fiber of the Galois cover is therefore connected, and the specialized action on the roots of each $f_i$ is the full generic action. Each $f_i(a,X)$ is irreducible. To obtain density, start with arbitrary smaller open neighborhoods inside the $\Omega_v$ and repeat. To obtain infinitely many values, add any finite set of previous values to the zero set of $g$. $\square$

**Corollary 4.4.** Every number field is Hilbertian. More strongly, every basic Hilbert subset of affine space over a number field is dense in the product of any finitely many local nonempty opens.

**Proof.** The one-parameter assertion is Theorem 4.3, and allowing a further nonzero polynomial
to vanish on any finite set of old parameters makes the good set infinite. For several
parameters, apply Lemma 3.2 simultaneously to the finite extensions defined by all the
primitive-element polynomials. Choose the line coefficients in local neighborhoods for which
$\mathbf a+\mathbf b u$ remains in the prescribed box whenever $u$ is sufficiently close to
$0$. On the selected line every generic polynomial remains irreducible over $K(U)$. Theorem 4.3,
with those local neighborhoods of $u$, then proves the stated affine-space form. $\square$

### 4.7 What the proof actually gives

The proof gives more than irreducibility. For a finite Galois cover it produces specializations whose Galois group is the whole generic group. It also shows why Hilbert conditions coexist with finitely many local conditions: the proof itself uses only finitely many additional places, all chosen away from the prescribed set.

The theorem is existential in the form proved. The finite-field estimate gives an explicit residue-field threshold once equations, genera, and bad-reduction data are bounded. Turning the entire proof into a numerical height bound would additionally require effective bounds for split auxiliary primes, effective construction of integral models, and quantitative weak approximation. None of those bounds has been established here, so no algorithmic size claim will be made.

The result does not handle infinitely many independent local opens. A global parameter has only finite approximation freedom. Nor does it manufacture rational points on an arbitrary variety. Both limitations will remain visible throughout the applications.

## 5. Simultaneous specialization and Galois groups

### 5.1 Finite intersections are the natural scale

Potential applications normally present a finite list of covers: one controls a field of definition, another forces an auxiliary residual representation to remain large, and a third prevents an unwanted intersection. Theorem 4.3 was stated simultaneously because finite intersection is the stable scale of the subject.

**Theorem 5.1 (simultaneous covers).** Let $U\subset\mathbf A^m_K$ be nonempty and let

$$
Y_i\longrightarrow U\qquad(1\le i\le r)
$$

be dominant generically finite maps with $Y_i$ integral and $K(Y_i)/K(U)$ separable. After restricting to their common finite étale locus, the set of $u\in U(K)$ for which every fiber $(Y_i)_u$ is connected is a Hilbert subset. It is dense in every finite product of nonempty local opens contained in $U(K_v)$.

**Proof.** Shrink $U$ so that all maps are finite étale. On a further dense affine open, choose a
primitive element for each field extension $K(Y_i)/K(U)$. Its minimal polynomial is irreducible
and separable over $K(U)$, and the fiber of $Y_i$ is connected exactly when its specialization is
irreducible. The simultaneous connectedness locus is therefore a basic Hilbert subset, up to the
proper closed set removed while choosing the presentations. Corollary 4.4 makes it dense in
every stated local box. $\square$

The total spaces need not be geometrically integral. If they are, their regularity becomes useful for disjointness, but connected specialization alone requires only integrality. The fiber product $Y_1\times_UY_2$ may be disconnected because the two generic fields can intersect; simultaneous connectedness of the two individual fibers does not assert that their compositum has product degree.

The theorem is finite. A countable intersection of Hilbert subsets need not be covered by the proof, and weak approximation cannot encode countably many new congruences. Any later infinite-avoidance statement must reduce the infinite family to finitely many subextensions for an independent reason.

### 5.2 The specialization group sits inside the generic group

Let $f(T,X)$ be separable, let $E/K(T)$ be its splitting field, and put $G=\operatorname{Gal}(E/K(T))$. At a good specialization $a$, the splitting field $\widetilde K_a$ has Galois group isomorphic to a subgroup

$$
G_a\hookrightarrow G,
$$

well defined up to conjugacy in $G$. This injection comes from the decomposition group of a place above $T-a$; trivial inertia at a good fiber identifies the decomposition group with the residue Galois group.

The injection explains why specialization can shrink a Galois group but cannot create a group larger than the generic one. Its permutation action on the specialized roots is the restriction of the generic action. Accordingly,

$$
f(a,X)\text{ irreducible}
\quad\Longleftrightarrow\quad
G_a\text{ acts transitively on the generic root set}.
$$

Equality $G_a=G$ is stronger. A transitive proper subgroup may exist: $A_n$ is transitive inside $S_n$, and a cyclic group generated by an $n$-cycle is transitive as well. Thus preservation of irreducibility alone does not preserve the full Galois group.

### 5.3 Resolvents as subgroup detectors

The subgroup obstruction can be encoded by polynomials. For a subgroup $M\subset G$, let $E^M$ be its fixed field. Choose a primitive element $z_M$ for $E^M/K(T)$ and let

$$
R_M(T,Z)\in K(T)[Z]
$$

be its minimal polynomial. Its roots correspond to the cosets $G/M$. At a good specialization, $R_M(a,Z)$ is irreducible exactly when $G_a$ acts transitively on $G/M$. In particular, if $G_a$ were contained in a conjugate of $M$, it would fix a coset and $R_M(a,Z)$ would have a linear factor.

Choose one representative of each conjugacy class of maximal proper subgroups of $G$. If all the corresponding resolvents specialize irreducibly, then $G_a$ is contained in no maximal proper subgroup and hence

$$
G_a=G.
$$

This is a convenient criterion, though stronger than necessary: irreducibility of every resolvent asks for transitivity on each coset space, whereas merely having no fixed point would already rule out containment. The auxiliary-Frobenius proof of Chapter 4 uses the weaker and more flexible condition.

**Theorem 5.2 (preservation of the full Galois group).** Outside a thin subset of $K^m$, a separable polynomial has specialized Galois group isomorphic, in its given permutation action, to its generic Galois group. The same conclusion holds for finitely many polynomials at once and inside any finite product of prescribed nonempty local opens.

**Proof.** Remove the degeneration locus and choose the finitely many maximal-subgroup resolvents
above. Each resolvent is generically irreducible. Corollary 4.4 supplies a Hilbert subset on which
all of them remain irreducible, so the specialized group lies in no maximal proper subgroup and
equals $G$. The complement of that basic Hilbert subset is thin by Proposition 2.1. For finitely
many polynomials, take all their resolvents at once; Corollary 4.4 also retains the prescribed local
opens. $\square$

The qualification “in its given permutation action” prevents an ambiguity. Two abstractly isomorphic groups can act differently on the roots, and factorization data depends on the action, not only on the abstract group.

### 5.4 Decomposition groups in a specialized field

Let $F_a/K$ be a finite Galois specialization with group $G_a=G$. At a finite place $v$ of $K$, choose $w\mid v$. The decomposition group

$$
D_w=\{\sigma\in G:\sigma w=w\}
$$

identifies with $\operatorname{Gal}((F_a)_w/K_v)$. Its inertia subgroup $I_w$ is the kernel of reduction, and

$$
1\longrightarrow I_w\longrightarrow D_w
\longrightarrow\operatorname{Gal}(k_w/k_v)\longrightarrow1.
$$

At an unramified place, $I_w=1$ and $D_w$ is cyclic, generated by arithmetic Frobenius. The factorization of a non-Galois defining polynomial modulo $v$ records the cycle lengths of this Frobenius on the roots. A factorization into degrees

$$
n_1+\cdots+n_r=n
$$

corresponds to a permutation with cycles of lengths $n_1,\ldots,n_r$, provided the discriminant is a unit.

At a ramified place, a residue factorization records only the action of $D_w/I_w$. There is no canonical Frobenius element in $D_w$, only an arithmetic Frobenius coset modulo inertia. Prescribing a decomposition group therefore requires more local information than prescribing a residue factorization.

### 5.5 A quadratic laboratory

Take $K=\mathbf Q$ and $f(T,X)=X^2-T$. The generic splitting field is $\mathbf Q(T)(\sqrt T)$ with group $C_2$. The good specializations are $a\ne0$, and the full group is preserved exactly when $a$ is not a square.

Let $S$ be a finite set of odd primes. For each $p\in S$, choose a nonzero residue $a_p\bmod p$. If $a_p$ is a square, then $p$ splits in $\mathbf Q(\sqrt a)$ for every $a$ sufficiently close to $a_p$ in $\mathbf Q_p$; if it is a nonsquare, $p$ is inert and unramified. Weak approximation chooses one rational $a$ meeting all these residue conditions, and Hilbert irreducibility lets us require that $a$ remain a global nonsquare. Sign at the real place independently chooses a real quadratic field when $a>0$ and an imaginary one when $a<0$.

This example also exposes an exact limit. Asking an odd unramified prime to be both split and inert is locally inconsistent, so no approximation theorem can help. Asking $p$ to ramify is not an open condition on nonzero residue classes; it requires $v_p(a)$ to be odd, an open condition inside $\mathbf Q_p^\times$ once that valuation is fixed. Local compatibility precedes global selection.

### 5.6 Symmetric-group specializations

Consider the universal monic polynomial

$$
F(\mathbf T,X)=X^n+T_1X^{n-1}+\cdots+T_n
$$

over $K(\mathbf T)$. Its roots are algebraically independent subject to the elementary symmetric relations, and its generic Galois group is $S_n$. The same calculation holds after extending $K$ to an algebraic closure, so the generic splitting field is regular over $K$. Theorem 5.2 shows that outside a thin subset of $K^n$, the specialized polynomial is irreducible and its splitting field has group $S_n$.

For $n\ge3$, the root field $K(\alpha)$ is generally not Galois. Indeed its stabilizer in $S_n$ is $S_{n-1}$, which is not normal. Its Galois closure has degree $n!$, while the field itself has degree $n$. Saying that an “$S_n$ extension of degree $n$” is Galois is therefore contradictory unless one means a degree-$n$ field whose Galois closure has group $S_n$.

The universal coefficient space is especially useful locally. At each of finitely many places choose a monic separable polynomial of degree $n$ with a desired factorization. A sufficiently small neighborhood of its coefficient vector has the same local étale algebra. Hilbert density then supplies one global polynomial with all those local patterns and global Galois group $S_n$.

### 5.7 Factorization, orbits, and intermediate fields

Let $G$ act transitively on the roots $\Omega$ of an irreducible generic polynomial, and let $G_a\subset G$ be a good specialization group. The irreducible factors of the specialized polynomial correspond to the $G_a$-orbits on $\Omega$; their degrees are the orbit sizes. This simple observation unifies several criteria.

- The specialization is irreducible exactly when there is one orbit.
- It has a linear factor exactly when $G_a$ fixes a root.
- A factor of degree $d$ is an orbit of size $d$, not merely an element of order $d$.
- Full Galois group requires excluding every proper subgroup, not merely every intransitive subgroup.

If a root $\alpha$ has stabilizer $H\subset G$, the generic root field is $E^H$. A specialized factor of degree $d$ corresponds to an orbit of $G_a$ on $G/H$ of size $d$. When $G_a=G$, the root field has degree $[G:H]$ and the lattice of its intermediate fields is controlled by subgroups between $H$ and $G$. Since $H$ need not be normal, those intermediate extensions need not be Galois.

At an unramified finite place of a full-group specialization, the local decomposition group is generated by one Frobenius element $\sigma$. Local factor degrees are therefore the orbit lengths of the cyclic group $\langle\sigma\rangle$, equivalently the cycle lengths of $\sigma$. At a ramified place, the entire decomposition group $D$ gives the factorization over $K_v$, while $D/I$ gives only the residue factorization. Replacing $D$ by a chosen Frobenius lift loses inertia and can change orbit data.

Resolvents perform the same orbit bookkeeping on coset spaces $G/M$. If a maximal-subgroup resolvent has a rational specialized root, then $G_a$ fixes a coset and lies in a conjugate of $M$. If it merely becomes reducible without a linear factor, $G_a$ has several larger orbits but need not lie in $M$. This is why “no rational root” is the precise containment test and full resolvent irreducibility is a convenient stronger test.

## 6. Local constancy and arithmetic approximation

### 6.1 Weak approximation

Hilbert conditions are global and algebraic. Completion conditions are local and topological.
Weak approximation is the mechanism that lets one parameter carry finitely many local
instructions, and its finiteness hypothesis is the first boundary to remember.

**Theorem 6.1 (weak approximation for a number field).** Let $K$ be a number field and let $S$ be
a finite set of pairwise distinct places. The diagonal map

$$
K\longrightarrow\prod_{v\in S}K_v
$$

has dense image. Equivalently, for $a_v\in K_v$ and $\epsilon_v>0$, there is $a\in K$ such that

$$
|a-a_v|_v<\epsilon_v\qquad(v\in S).
$$

The same assertion holds coordinatewise for $K^m$.

**Proof strategy.** At the finite places, neighborhoods contain congruence classes modulo powers
of distinct prime ideals, so the Chinese remainder theorem produces one global congruence
class. The elements in that class form a translate of a fractional ideal. After division by a
large integer that is a unit at the selected finite places, the embedded ideal becomes a lattice
with arbitrarily fine archimedean mesh. A lattice point then supplies the remaining real and
complex approximations without changing the finite congruences.

**Proof.** Shrink each prescribed neighborhood. At a finite place $v$ corresponding to a prime
$\mathfrak p_v$, it is enough to require

$$
a-a_v'\in\mathfrak p_v^{n_v}\mathcal O_{K_v}
$$

for some $a_v'\in K$ close to $a_v$ and some integer $n_v$. After multiplying all data by one
nonzero element of $K$, these become congruences in a common fractional ideal. The Chinese
remainder theorem for the pairwise coprime powers $\mathfrak p_v^{n_v}$ gives $c\in K$ satisfying
all of them. There is a nonzero fractional ideal $I$ such that every element of $c+I$ satisfies
the same finite-place requirements.

Embed $K$ diagonally in

$$
K_\infty=\prod_{v\mid\infty}K_v.
$$

The image of $I$ is a full lattice $\Lambda$ in the finite-dimensional real vector space
$K_\infty$. Choose a bounded fundamental parallelepiped $P$ for $\Lambda$. Let $M$ be the product
of the rational primes below the finite places in $S$, with repeated factors omitted. There are
arbitrarily large positive integers $N$ satisfying $N\equiv1\pmod M$; every such $N$ is a unit in
$\mathcal O_{K_v}$ for $v\in S$ finite. Therefore every element of

$$
c+N^{-1}I
$$

still satisfies the finite congruences.

Let $t\in K_\infty$ be the tuple of desired archimedean targets, with arbitrary coordinates at
archimedean places not in $S$. Choose $\lambda\in\Lambda$ so that

$$
N(t-c)-\lambda\in P.
$$

Then $a=c+\lambda/N$ satisfies

$$
t-a\in N^{-1}P.
$$

Since $P$ is bounded, $N^{-1}P$ lies in every prescribed archimedean neighborhood of zero once
$N$ is large. This gives all required approximations. Repeating the argument in each coordinate
proves the assertion for $K^m$. $\square$

Two useful refinements are immediate. Every nonempty finite local box contains infinitely many
diagonal points, and one may avoid any prescribed finite subset of $K^m$. To prove both claims at
once, choose a finite place $w\notin S$ and a small $w$-adic open ball containing none of the
finitely many points to be avoided. Apply the theorem with this extra place. Repeating after
enlarging the forbidden finite set constructs as many distinct points as desired. This justifies
the repeated removal of branch points, denominator zeros, and previously chosen parameters.

The theorem fails for an unrestricted infinite product. A nonzero number field element has
nonzero valuation at only finitely many primes, so one cannot independently prescribe positive
valuation at infinitely many distinct primes. Every later approximation statement is therefore
explicitly finite.

### 6.2 Why local conditions are open

Weak approximation can combine local conditions only after they have been expressed as open subsets. A statement such as “the polynomial has the same factorization over $K_v$” is not visibly open from its wording. Its openness rests on the rigidity of finite separable algebras over a complete field.

Let $k$ be a local field of characteristic zero and let

$$
p(X)=X^n+c_1X^{n-1}+\cdots+c_n\in k[X]
$$

be separable. Put $A=k[X]/(p)$. The claim is that every coefficient vector sufficiently close to $(c_1,\ldots,c_n)$ defines a $k$-algebra isomorphic to $A$. This includes products of fields, ramified fields, and unramified fields.

The separability hypothesis is the whole reason for stability. At $X^2$ the arbitrarily close polynomials $X^2-\epsilon$ can split, remain irreducible, or become ramified in different ways. Multiple roots sit precisely on the boundary across which the algebra changes.

### 6.3 Krasner's lemma and factor stability

**Lemma 6.2 (Krasner).** Let $k$ be complete with a nonarchimedean absolute value, let $\alpha$ be separable over $k$, and let $\beta$ be algebraic over $k$. If

$$
|\beta-\alpha|<|\alpha-\sigma(\alpha)|
$$

for every $k$-embedding $\sigma:k(\alpha)\hookrightarrow\bar k$ other than the identity, then $k(\alpha)\subset k(\beta)$.

**Proof strategy and proof.** Extend the absolute value to a finite Galois field containing $\alpha$ and $\beta$. If an automorphism fixes $\beta$, then

$$
|\sigma(\alpha)-\alpha|
\le\max\{|\sigma(\alpha)-\sigma(\beta)|,|\beta-\alpha|\}
=|\beta-\alpha|.
$$

The strict hypothesis forces $\sigma(\alpha)=\alpha$. Thus the stabilizer of $\beta$ is contained in the stabilizer of $\alpha$. Reversing inclusions under Galois correspondence gives $k(\alpha)\subset k(\beta)$. $\square$

Roots of a separable polynomial vary continuously, as an unordered multiset, with its coefficients. Choose disjoint small neighborhoods around the roots of $p$ in a splitting field. Hensel's lemma, or a Newton estimate applied in each neighborhood, shows that a nearby polynomial has exactly one root in each neighborhood. Krasner's lemma then identifies the fields generated by corresponding roots. Comparing degrees forces equality rather than just inclusion. Grouping conjugate roots proves the following.

**Proposition 6.3 (local constancy of finite étale algebras).** The isomorphism class of $k[X]/(p)$ is locally constant on the open coefficient locus where the discriminant is nonzero.

**Proof.** Factor $p$ into distinct irreducibles and choose one root of every factor. Put disjoint
small balls around all conjugate roots in one finite splitting field. The simple-root stability
argument places exactly one root of every nearby polynomial in each ball. If $\beta$ is matched
with $\alpha$, Lemma 6.2 gives $k(\alpha)\subseteq k(\beta)$. Every $k$-conjugate of $\beta$ lies in
the ball attached to a $k$-conjugate of $\alpha$, because field automorphisms preserve distance
and the nearby polynomial has coefficients in $k$. Hence $[k(\beta):k]\le[k(\alpha):k]$, so the
inclusion is equality. Conjugacy groups the matched roots into the same factor blocks, and the
product of all factor fields is unchanged. $\square$

Over $\mathbf R$, the corresponding statement says that the number of real roots of a separable polynomial is locally constant. Complex conjugate pairs cannot become real without first colliding on the discriminant locus. Over $\mathbf C$, every separable degree-$n$ algebra is $\mathbf C^n$.

### 6.4 From local algebras to global fields

Let $F(\mathbf T,X)$ be a polynomial family and choose $b_v\in K_v^m$ at finitely many places such that $F(b_v,X)$ is separable. Proposition 6.3 gives a neighborhood $\Omega_v$ on which

$$
K_v[X]/(F(\mathbf t,X))
\cong K_v[X]/(F(b_v,X)).
$$

Corollary 4.4 then finds $\mathbf a\in K^m$ in all the $\Omega_v$ while retaining global irreducibility and any finite collection of Hilbert conditions. If $M=K[X]/(F(\mathbf a,X))$, then

$$
M\otimes_KK_v\cong K_v[X]/(F(b_v,X)).
$$

This tensor product is generally a product over the places of $M$ above $v$. It is a field exactly when there is one place above $v$. Calling it “the completion of $M$ at $v$” when it is a product would obscure the splitting data.

### 6.5 Splitting, inertness, and ramification avoidance

For a degree-$n$ field $M/K$, the following local patterns have precise algebraic meanings.

- **Complete splitting at $v$** means $M\otimes_KK_v\cong K_v^n$.

- **One-place behavior**, often called inertness when unramified, means $M\otimes_KK_v$ is a field of degree $n$.

- **Unramified factorization of type $(n_1,\ldots,n_r)$** means the tensor product is a product of unramified field extensions of those degrees.

- **Ramification avoidance** means every field factor is unramified. It can be forced by choosing an unramified local model, or integrally by requiring a monic integral polynomial with unit discriminant.

For a Galois extension with group $G$, a completely split place has $D_w=1$. A one-place unramified place has $D_w=G$, but an unramified local Galois group is cyclic. Consequently, a noncyclic Galois extension cannot have an unramified place that is literally inert with a single prime. By contrast, a degree-$n$ non-Galois field with $S_n$ Galois closure may have an inert unramified prime because an $n$-cycle acts transitively on its $n$ roots.

Ramified local behavior is also constrained. Any proposed pair $(I,D)$ in a global Galois group must satisfy

$$
I\triangleleft D\subset G,\qquad D/I\text{ cyclic},
$$

with the quotient generated by arithmetic Frobenius. Further tame and wild restrictions depend on the residue characteristic. Hilbert irreducibility does not prove that every abstract pair occurs. It globalizes a local behavior only when the family already has a local fiber realizing it.

For a nonarchimedean local field with finite residue field, these restrictions are already substantial: wild inertia is a $p$-group, tame inertia is cyclic of order prime to $p$, and the residue quotient is cyclic. In particular, every finite local Galois group is solvable. A nonsolvable subgroup of $G$ can therefore never be a decomposition group at a finite place, even though it may occur as the global Galois group.

### 6.6 Prescribed decomposition behavior

Suppose a regular Galois cover $V\to U$ has group $G$, and at $b_v\in U(K_v)$ its fiber contains a Galois field factor $L_v/K_v$ with decomposition group $D_v$ and inertia $I_v$. Finite étale local constancy over the field preserves the $K_v$-algebra $L_v$ in a small neighborhood. Therefore a global specialization in that neighborhood has a completion isomorphic to $L_v$ and realizes the same $D_v$ and $I_v$, up to conjugacy in $G$.

The words “up to conjugacy” are unavoidable: changing the chosen prime above $v$ conjugates the decomposition and inertia groups. At an unramified place, specifying a Frobenius **element** likewise means specifying a conjugacy class unless a prime and an identification of the global group have been rigidified.

This local method can prescribe ramification rather than merely avoid it, but only on an open Krasner neighborhood of an existing separable local extension. Integral discriminant exponent and higher ramification filtration are then preserved because the local field algebra itself is preserved. Merely staying off the field discriminant locus would not suffice.

### 6.7 Worked local factorization in a symmetric-group family

Fix distinct finite places $v_1,\ldots,v_s$ of $K$ and partitions

$$
n=n_{i1}+\cdots+n_{ir_i}.
$$

For each $i$, choose pairwise distinct monic irreducible polynomials over the residue field $k_{v_i}$ of degrees $n_{i1},\ldots,n_{ir_i}$. Such polynomials exist over every finite field. Lift their product to a monic polynomial $p_i(X)\in\mathcal O_{K_{v_i}}[X]$. Its discriminant is a unit, and its $K_{v_i}$-algebra is the product of unramified extensions of the desired degrees.

Apply weak approximation to the coefficients in the universal family of Section 5.6, while imposing the Hilbert conditions that give generic group $S_n$. The resulting global polynomial $p(X)\in K[X]$ is irreducible, has Galois closure group $S_n$, and has the prescribed unramified factorization at every $v_i$.

There is one group-theoretic compatibility hidden in this statement: every partition of $n$ is a cycle type in $S_n$, so it can occur. For a proper generic group $G\subset S_n$, a partition whose cycle type misses $G$ cannot occur at an unramified good place of a full-$G$ specialization.

### 6.8 Hilbert density versus thin-set density

The complement of a thin set is dense in every finite product of local opens over a number field. This does not imply that the thin set is topologically small. Squares in $\mathbf Q$ are dense in $\mathbf R_{>0}$ and, in suitable $p$-adic square-class opens, fill the rational points that happen to be squares. Both a thin set and its Hilbertian complement may meet the same large real interval densely.

The correct conclusion is an avoidance theorem: no finite local box can force a rational point to lie in a given thin set unless the box is incompatible with the Hilbert condition through an algebraic degeneration already built into the family. Hilbert subsets supply arithmetic freedom inside local topology; they are not complements of measure-zero sets in every completion.

### 6.9 Why this is not an unrestricted local-global theorem

The universal polynomial family can realize arbitrary degree-$n$ finite étale algebras at finitely many completions, because its parameters are all coefficients and every such algebra is monogenic over a local field. The resulting global object is a degree-$n$ field, usually non-Galois. This flexibility should not be confused with the assertion that arbitrary local **Galois** extensions can be assembled into a global Galois extension with a preassigned group.

For a fixed finite group $G$, the specialization method needs a regular $G$-cover and, at every prescribed place, a local parameter whose fiber realizes the desired $G$-algebra. Either requirement can fail. Even when abstract subgroups $I\triangleleft D\subset G$ pass the condition that $D/I$ be cyclic, they may fail local ramification constraints or may not occur in the chosen cover. Global reciprocity imposes further restrictions in abelian problems, and exceptional prime-power phenomena show that naive prescriptions of cyclic local extensions are not always simultaneously globalizable.

There is no contradiction with Theorem 4.3 or its affine-space Corollary 4.4. Those results say
that **existing nonempty local opens in one global family** can be met simultaneously while
retaining a Hilbert condition. They do not say that every list of abstract local extensions
arises as fibers of such a family. The family supplies the compatibility certificate.

A similar caution applies to ramification avoidance. Given a finite list of places, choosing unramified local models avoids ramification there. One cannot conclude that the specialization is unramified at every other place. The coefficients and discriminant of the chosen global polynomial have only finitely many bad primes, but which additional primes occur depends on the specialization. Imposing infinitely many unit-discriminant conditions lies beyond weak approximation.

## 7. Linear disjointness and avoidance

### 7.1 Why irreducibility after base change is the right test

Let $M/K$ and $L/K$ be finite extensions. They are **linearly disjoint over $K$** if the natural map

$$
M\otimes_KL\longrightarrow ML
$$

is injective, equivalently if the tensor product is a field, or equivalently

$$
[ML:L]=[M:K].
$$

If one of the extensions is Galois, this is also equivalent to $M\cap L=K$ inside a common algebraic closure. Without a Galois hypothesis, trivial intersection alone need not imply linear disjointness, so degree is the safer criterion.

Suppose $M_a=K(\alpha_a)$ is defined by an irreducible degree-$n$ specialization $f(a,X)$. If $f(a,X)$ remains irreducible over $L$, then

$$
[LM_a:L]=n=[M_a:K],
$$

and $M_a$ is linearly disjoint from $L$. Thus disjointness is itself a Hilbert irreducibility condition, but imposed after the constant-field base change $K\subset L$.

The generic prerequisite is exact:

$$
f(T,X)\text{ must be irreducible in }L(T)[X].
$$

If it already factors there, no specialization theorem can promise irreducibility over $L$ generically. For a regular extension this obstruction disappears for every finite $L/K$.

### 7.2 Descent of a Hilbert condition from $L$ to $K$

There is a small logical gap to close: Hilbert irreducibility over $L$ produces parameters in $L$, whereas we need $a\in K$. The bad $K$-parameters for which $f(a,X)$ factors over $L$ form a thin subset of $\mathbf A^1(K)$.

To see this concretely, for each possible factor degree $d$, the coefficient equations for a monic degree-$d$ factor define a finite scheme $Z_d$ over a dense open of $\mathbf A^1_L$; finiteness follows because a separable polynomial has only finitely many subsets of roots. Form the restriction of scalars

$$
\operatorname{Res}_{L/K}Z_d
\longrightarrow
\operatorname{Res}_{L/K}\mathbf A^1_L
$$

and pull it back along the diagonal map $\mathbf A^1_K\to\operatorname{Res}_{L/K}\mathbf A^1_L$. A $K$-point of this pullback over $a$ is exactly an $L$-point of $Z_d$ over the same parameter $a$, hence exactly a degree-$d$ factor over $L$. Normalize every component that dominates the diagonal line. Such a component cannot have generic degree one: a degree-one component would give an $L(T)$-rational factor of $f$, contrary to the assumed irreducibility over $L(T)$. Therefore every dominating component has degree at least two over $K(T)$. The nondominating components and all deleted loci are type I, while the dominating components give finitely many type II images. Thus the bad $K$-parameters form a thin set over $K$.

Theorem 4.3 therefore gives the following.

**Theorem 7.1 (disjoint specialization).** Let $f(T,X)\in K(T)[X]$ be irreducible and separable of degree $n$, and let $L/K$ be finite. If $f$ remains irreducible over $L(T)$, then the parameters $a\in K$ for which $f(a,X)$ is irreducible over $L$ form a Hilbert subset of $K$. They are dense in every finite product of local opens. For each such $a$, the root field $M_a/K$ is linearly disjoint from $L/K$.

**Proof.** Section 7.2 shows that failure of irreducibility over $L$ on a $K$-parameter is thin
over $K$; equivalently, its complement contains a basic Hilbert subset. Theorem 4.3 makes that
subset dense in every finite local box. If $\alpha_a$ is a root, irreducibility over $L$ gives

$$
[L(\alpha_a):L]=n=[K(\alpha_a):K].
$$

The degree criterion of Section 7.1 then says that $K(\alpha_a)$ and $L$ are linearly disjoint.
$\square$

### 7.3 Galois closures and regular generic splitting fields

Disjointness of a root field does not automatically give disjointness of its Galois closure. A degree-three field $M$ may meet $L$ trivially while its $S_3$ closure shares the quadratic discriminant field with $L$.

Let $E/K(T)$ be the generic splitting field of $f$. If $E/K(T)$ is regular, then

$$
E\cap L(T)=K(T)
$$

for every finite $L/K$. Apply full-group Hilbert irreducibility to the compositum $EL(T)/L(T)$, descended to parameters in $K$. One obtains specializations for which

$$
\operatorname{Gal}(\widetilde M_aL/L)\cong
\operatorname{Gal}(E/K(T)).
$$

Since the same group occurs over $K$, degrees give

$$
\widetilde M_a\cap L=K.
$$

Here $\widetilde M_a/K$ is Galois, so intersection and linear disjointness are equivalent. This is the form most useful when later Galois representations are to retain their image after restriction to $G_L$.

If the generic splitting field has constant field $C\ne K$, every good specialized splitting field contains a copy of $C$. Disjointness from an $L$ containing a nontrivial part of $C$ is then impossible. Regularity is not decoration; it removes a genuine fixed intersection.

### 7.4 Avoiding finitely many extensions

Given finite extensions $L_1,\ldots,L_r$ of $K$, let $L$ be the compositum of their normal closures. A specialization whose Galois closure is linearly disjoint from $L$ is linearly disjoint from each $L_i$. Thus finitely many avoidance demands cost only one Hilbert condition.

Several weaker phrases should be distinguished.

- $M$ is **not contained** in $L_i$ is weaker than $M\cap L_i=K$.
- $M\cap L_i=K$ is equivalent to linear disjointness if $M/K$ or $L_i/K$ is Galois, but not in complete generality.
- Disjointness of $M$ from each $L_i$ separately need not imply disjointness from their compositum. For example, three distinct quadratic subfields of a biquadratic extension have pairwise trivial intersection, while any two generate the third.

Passing to the compositum of normal closures avoids all these traps and is usually inexpensive because only finitely many fields are involved.

### 7.5 Infinite extensions: the finite-subextension criterion

Let $\Omega/K$ be an algebraic extension, possibly infinite, and let $M/K$ be finite. Then

$$
M\cap\Omega=K
$$

if and only if $M$ has trivial intersection with every finite subextension of $\Omega/K$. Indeed, $M\cap\Omega$ is itself finite over $K$, and every one of its elements lies in some finite subextension of $\Omega$.

This criterion is exact but not by itself constructive: it appears to impose infinitely many Hilbert conditions. A finite reduction is available when, for a given degree bound $n$, the extension $\Omega$ has only finitely many subfields of degree at most $n$. Let $L_n$ be their compositum. If $[M:K]\le n$ and $M$ is linearly disjoint from a normal closure of $L_n$, then $M\cap\Omega=K$.

One useful sufficient condition is that the profinite group $\operatorname{Gal}(\Omega/K)$ be topologically finitely generated. Such a group has only finitely many open subgroups of any bounded index: a subgroup of index at most $n$ yields a transitive homomorphism to some $S_d$, and finitely many choices for the images of a fixed finite set of topological generators give finitely many homomorphisms. Hence there are only finitely many subextensions of bounded degree.

The Galois hypothesis on $\Omega/K$ is convenient for translating subfields into open subgroups but is not needed for the elementary intersection criterion itself.

### 7.6 Structural infinite avoidance

Sometimes group structure makes every finite reduction unnecessary. Suppose $\widetilde M/K$ is finite Galois with a nonabelian simple group $G$, and $\Omega/K$ is Galois with prosolvable Galois group. Then

$$
\widetilde M\cap\Omega=K.
$$

Indeed, the intersection is Galois over $K$. Its Galois group is both a quotient of $G$ and a finite solvable quotient of $\operatorname{Gal}(\Omega/K)$. Simplicity leaves only the trivial quotient, since $G$ itself is not solvable.

More generally, the intersection corresponds to a common finite quotient of the two Galois groups. Proving that no nontrivial common quotient exists proves disjointness. This applies, for example, when all nontrivial quotients of one specialized group have a composition factor excluded from every finite quotient of the infinite extension.

Ramification can give another limited criterion. If $M/K$ has prime degree and is ramified at a place where every finite subextension of $\Omega/K$ is unramified, then $M$ cannot be contained in $\Omega$. Since a prime-degree field has no intermediate fields, $M\cap\Omega=K$. For composite degree, ramification of $M$ at one new place need not prevent a proper unramified subfield from lying in the intersection.

These are reductions of an infinite condition to finite structure. Hilbert irreducibility alone does not assert simultaneous avoidance of an arbitrary infinite algebraic extension.

### 7.7 Preserving finite Galois images

Linear disjointness is often used not for its own sake but to keep a Galois action from shrinking after base change. Let

$$
\rho:G_K\longrightarrow\Gamma
$$

be a continuous homomorphism with finite image, and let $E/K$ be the finite Galois extension fixed by $\ker\rho$. For a finite extension $M/K$, the image of the restricted representation $\rho|_{G_M}$ corresponds to

$$
\operatorname{Gal}(EM/M)\cong\operatorname{Gal}(E/E\cap M).
$$

Thus the restricted image equals the original image precisely when $E\cap M=K$, equivalently when $E$ and $M$ are linearly disjoint. Choosing an auxiliary specialization disjoint from $E$ preserves the finite image.

For finitely many representations, take the compositum of their fixed fields. For a representation with infinite image, no single finite fixed field captures the whole condition. One can preserve a specified finite quotient by avoiding its fixed field, or preserve all quotients of bounded order when their fixed fields have finite compositum. Claims about the full infinite image require additional group-theoretic information of the kind discussed in Sections 7.5 and 7.6.

If the auxiliary field $M/K$ is not Galois, restriction still corresponds to the compositum $EM/M$, and $E\cap M=K$ is enough because $E/K$ is Galois. If one later passes to the Galois closure $\widetilde M$, disjointness must have been imposed for $\widetilde M$ itself; disjointness of $M$ alone may be lost on taking the closure.

### 7.8 Intersection pitfalls in towers

Intersections become most treacherous after composita. Let

$$
L=K(\sqrt a,\sqrt b)
$$

be biquadratic. Its three quadratic subfields

$$
K(\sqrt a),\qquad K(\sqrt b),\qquad K(\sqrt{ab})
$$

have pairwise intersection $K$. Nevertheless, the first two together contain the third. A field can therefore be disjoint from each member of a list and fail to be disjoint from their compositum. This is why finite avoidance is always imposed against one normal compositum.

Another failure occurs on taking normal closures. Let $M/K$ be a non-Galois cubic with $S_3$ closure $\widetilde M$, and let $L$ be the quadratic field fixed by $A_3\subset S_3$. Then $[M:K]=3$ and $[L:K]=2$, so $M\cap L=K$ and $M,L$ are linearly disjoint. But $L\subset\widetilde M$. Any construction that needs the full Galois closure to remain disjoint must impose that stronger condition from the start.

In towers, the degree test remains reliable. If $E/K$ is Galois and $M/K$ finite, then

$$
[EM:M]=[E:E\cap M].
$$

Thus equality with $[E:K]$ is exactly trivial intersection. For two arbitrary non-Galois fields, tensor-product irreducibility or the degree $[EM:K]=[E:K][M:K]$ is the correct test; drawing conclusions from a visibly trivial set-theoretic overlap of chosen generators is unsafe.

## 8. Degree, signature, and Galois closure

### 8.1 Degree is generic; signature is local

Irreducibility preserves the generic degree. Signature asks how the embeddings of that degree distribute between $\mathbf R$ and $\mathbf C$. It is controlled independently at the archimedean completions.

Let $M=K(\alpha)$ have degree $n$, and suppose $K$ has $r_1(K)$ real places and $r_2(K)$ complex places. For a real place $v$, let $r_v$ be the number of real roots of the minimal polynomial of $\alpha$ over $K_v$. Then

$$
r_v\equiv n\pmod 2,\qquad 0\le r_v\le n.
$$

The remaining roots occur in $(n-r_v)/2$ conjugate pairs. Counting embeddings gives

$$
r_1(M)=\sum_{v\text{ real}}r_v,
$$

and

$$
r_2(M)=n\,r_2(K)+
\sum_{v\text{ real}}\frac{n-r_v}{2}.
$$

Every complex place of $K$ contributes $n$ complex pairs. At a real place, only signature patterns with the displayed parity can occur. These are unavoidable constraints, not defects of approximation.

### 8.2 Archimedean connected components

The discriminant-nonzero locus in the real coefficient space has connected components indexed more finely than just the discriminant sign, but the number of real roots is constant on each component. To prescribe $r_v$, one must choose a base polynomial with exactly $r_v$ simple real roots and then stay in a sufficiently small connected neighborhood.

At a complex place there is only one degree-$n$ étale algebra, $\mathbf C^n$, and no real-root condition. A number field $M$ is **totally real** if every embedding $M\hookrightarrow\mathbf C$ has image in $\mathbf R$. If $M$ contains $K$, this is possible only if $K$ itself is totally real. Assuming $K$ totally real, total reality of $M$ is equivalent to

$$
M\otimes_KK_v\cong\mathbf R^n
$$

at every real place $v$ of $K$.

Total positivity of a discriminant is not enough. A real polynomial of degree four can have zero or four real roots while its discriminant is positive. The correct open condition is complete real splitting, not a sign test on one invariant.

### 8.3 Constructing degree-n totally real fields

Let $K$ be totally real and let $n\ge2$. Choose distinct rational numbers

$$
c_1<\cdots<c_n
$$

and put

$$
P(X)=\prod_{i=1}^n(X-c_i),\qquad F(T,X)=P(X)-T.
$$

The polynomial $F$ is irreducible over $K(T)$. One way to see this is to regard $X$ as transcendental: the rational function $P(X)$ defines an extension

$$
K(X)/K(P(X))
$$

of degree $n$, so $P(X)-T$ is the minimal polynomial of $X$ over $K(T)$ after identifying $T=P(X)$. It is separable in characteristic zero.

At $T=0$, all roots are the simple real numbers $c_i$. Therefore, at each real completion of $K$, there is an interval $I_v$ around $0$ such that $P(X)-t$ has $n$ real roots for every $t\in I_v$. Hilbert irreducibility with weak approximation chooses

$$
a\in K\cap\bigcap_{v\mid\infty}I_v
$$

for which $P(X)-a$ is irreducible. If $\alpha$ is a root, then $M=K(\alpha)$ has degree $n$ and is totally real.

This proof works in every degree. It also makes the parity constraints automatic: complete real splitting has $r_v=n$ at each real place.

### 8.4 Full symmetric Galois closure

The preceding construction can be refined so that the Galois closure has group $S_n$. Choose the $c_i$ so that the critical points of $P$ are simple and their critical values are distinct. These requirements are the nonvanishing of finitely many discriminants and resultants in the coefficients of $P$. They define a Zariski-open condition, and it is nonempty: the polynomial $X^n-X$ has simple critical points, and at a critical point $z$ its value is $-(n-1)z/n$, so distinct critical points have distinct critical values. The finite dominant map from ordered roots to monic polynomial coefficients has dense image. Consequently the inverse image of this nonempty coefficient open meets the open locus of distinct ordered roots, and density of $\mathbf Q$ in affine space supplies a tuple of distinct rational $c_i$ with the required property.

The cover $P:\mathbf P^1\to\mathbf P^1$ then has simple finite branch points. Local monodromy around each is a transposition. The inertia element at infinity is the inverse of the product of the finite branch cycles, so the finite transpositions generate the entire geometric monodromy group. The cover is connected, hence this group acts transitively. A transitive subgroup of $S_n$ generated by transpositions is $S_n$: draw a graph with vertices the roots and an edge for every generating transposition; transitivity says the graph is connected, and edge transpositions of a connected graph generate all of $S_n$.

Thus the geometric monodromy group is $S_n$. The arithmetic monodromy group is a subgroup of
$S_n$ containing the geometric group, so it too is $S_n$; their quotient, which measures the
constant field, is trivial. Hence the generic splitting field of $P(X)-T$ is regular over $K$
with group $S_n$. Imposing the full-group Hilbert conditions while keeping $a$ in all the real
intervals produces a totally real degree-$n$ field whose Galois closure has group $S_n$.

For $n\ge3$, the degree-$n$ field is not itself Galois. Its Galois closure is totally real, however, because every conjugate of every root of $P(X)-a$ is real under every real embedding of $K$; a compositum of totally real fields is totally real.

### 8.5 Prescribed signatures

The same method gives any signature pattern that is locally realizable by the chosen family. For each real $v$, choose $b_v\in K_v^m$ such that $F(b_v,X)$ has exactly $r_v$ real roots, where $r_v\equiv n\pmod 2$. Local constancy supplies an open neighborhood. Hilbert density then gives a global irreducible specialization with

$$
r_1(M)=\sum_v r_v,\qquad
r_2(M)=n r_2(K)+\sum_v(n-r_v)/2.
$$

In the universal coefficient family every parity-compatible $r_v$ is realizable: multiply $r_v$ distinct real linear factors by $(n-r_v)/2$ distinct irreducible real quadratic factors. In a one-parameter family, some patterns may never occur. Approximation preserves available local components; it does not create missing ones.

### 8.6 Total reality with finite local conditions and disjointness

Let $K$ be totally real, let $L/K$ be finite, and fix finitely many finite places. Use a polynomial $P(X)-T$ as in Section 8.4, with regular $S_n$ splitting field. At each finite prescribed place choose a parameter $b_v$ whose local fiber has the desired realizable étale algebra, and choose a Krasner neighborhood $\Omega_v$. At every real place choose the complete-real-splitting interval around $0$.

The intersection of the following conditions is a Hilbert subset inside this local box:

- irreducibility of $P(X)-a$;
- preservation of the full group $S_n$;
- irreducibility and full group after base change to a normal closure of $L$;
- any further finite list of cover conditions.

Hence there is a totally real degree-$n$ field $M/K$ satisfying all prescribed local fibers and whose Galois closure is linearly disjoint from $L$. Complete splitting at selected finite places is always locally available by taking $a$ sufficiently close to $0$, since the simple roots $c_i$ lie in $K_v$. Other patterns require a local parameter realizing them.

This theorem does not claim that $M/K$ is Galois. If a Galois totally real auxiliary field is required, one may use the Galois closure, whose degree is generally $n!$ and whose local behavior must be recomputed in the Galois action. Passing to the closure is not degree-neutral.

## 9. The geometric Hilbert property

### 9.1 Normal varieties and function fields

Polynomial coordinates are excellent for calculations but poor at expressing invariance. Let $X$ be a normal integral variety over $K$, and let $K(X)$ be its function field. A finite separable extension $L/K(X)$ has a normalization $Y$ over $X$. After deleting the branch locus and the locus where finiteness fails, one obtains a finite étale map

$$
\pi:Y_U\longrightarrow U
$$

over a nonempty open $U\subset X$.

Normality matters here because integral closure recovers the cover uniquely from the function-field extension and codimension-one valuations have unambiguous centers. It is not needed in order to write a polynomial, and it does not imply geometric irreducibility. If $X$ is geometrically integral, then $K$ is algebraically closed in $K(X)$; this removes constant components from the base. If $Y$ is also geometrically integral, then $K(Y)/K(X)$ is regular over $K$ in the relevant sense.

At $x\in U(K)$, the fiber is

$$
Y_x=\operatorname{Spec}A_x,
$$

where $A_x$ is a finite étale $K$-algebra of rank $[L:K(X)]$. The point belongs to the Hilbert subset attached to $Y$ when $A_x$ is a field. If $x$ is merely a closed point, $A_x$ is instead an algebra over $k(x)$. The distinction between rational and closed points is therefore built into the definition, not a matter of terminology.

### 9.2 Hilbert subsets on a variety

Given finitely many dominant generically finite separable maps

$$
\pi_i:Y_i\longrightarrow X
$$

with integral total spaces, choose a common open $U$ on which all are finite étale. Their **geometric Hilbert subset** is

$$
H=\{x\in U(K):(Y_i)_x\text{ is connected for every }i\}.
$$

Changing $U$ changes $H$ only by points in a proper closed subset. Normalizing the $Y_i$ likewise does not change the generic condition. A type II set is the shadow of failure for an intermediate cover, while a Hilbert subset asks for maximal connectedness of the whole fiber.

If $X$ has a dense open $W$ isomorphic to a dense open of $\mathbf A^m$, Corollary 4.4 applies in those coordinates. Hence every geometric Hilbert subset meets $W(K)$ and is Zariski dense in $X$. More precisely, it is dense in every finite product of local opens that meet $W(K_v)$.

**Theorem 9.1 (rational-variety form).** Let $X$ be a $K$-rational geometrically integral variety over a number field. For finitely many integral generically finite separable covers of $X$, their common connected-fiber locus is a Hilbert subset. On a common rational chart it is dense in products of finitely many local nonempty opens.

**Proof.** Choose dense opens $W\subset X$ and $W'\subset\mathbf A^m_K$ that are isomorphic.
Restrict every cover to $W$ and transport it to $W'$. The function fields have not changed, so
integrality and separability of every generic cover remain true. After removing the finite and
branch loci, Theorem 5.1 gives a Hilbert subset of $W'(K)$ with connected fibers and makes it
dense in each local box contained in the chart. Transporting back proves the assertion on $W$.
All discarded points lie in a proper closed subset of $X$, which is allowed in the definition of
a Hilbert subset. $\square$

If $X$ is smooth, a proper closed subset has empty interior in $X(K_v)$ at every local smooth point. Thus any local open containing a smooth point may be shrunk to meet the rational chart. For singular spaces or opens supported on exceptional local loci, it is safer to state explicitly that the chosen local opens meet the chart.

### 9.3 What geometric irreducibility buys

Suppose $Y\to X$ is generically finite and both $X$ and $Y$ are geometrically integral. Then the function-field extension has no nontrivial constant subextension. After any finite extension $L/K$, the base change $Y_L$ remains integral. This yields two useful consequences.

First, the connected-fiber Hilbert condition can be imposed after base change to $L$ and descended to parameters in $K$. Specialized fibers can therefore be made linearly disjoint from $L$ when interpreted as field extensions.

Second, the geometric monodromy group agrees with the arithmetic monodromy group when the Galois closure is also geometrically integral. Full monodromy after specialization then means exactly that no constant quotient has intervened.

If $Y$ is integral but not geometrically integral, the cover is still legitimate. Its constants must simply be tracked as in Chapter 4. Removing geometric irreducibility from a theorem about disjointness, while retaining its conclusion unchanged, is generally false.

### 9.4 Pulling back covers

Let $\phi:X'\to X$ be dominant. Pulling back $Y\to X$ replaces $K(Y)/K(X)$ by the tensor product with $K(X')$. The pullback is generically connected exactly when

$$
K(Y)\otimes_{K(X)}K(X')
$$

is a field. If the tensor product splits, connected fibers of the original cover cannot be recovered by simply applying a Hilbert theorem to one component of the pullback.

This is the geometric version of irreducibility after base change. A regular cover remains generically connected under constant extensions, but not under every dominant map. For example, pulling $X\mapsto X^2$ back along $T=S^2$ makes the equation $X^2=S^2$ split. Dominance alone does not preserve a Hilbert condition.

### 9.5 The boundary before variety-point theorems

Hilbert irreducibility begins with rational points on an affine parameter space and retains generic properties while imposing finitely many local opens. It does not start with an arbitrary variety that has local points and produce a rational point, even after changing the ground field. A high-genus curve can have local points everywhere and only finitely many global points; a variety can have none.

Accordingly, the theorems in this book apply directly to rational parameter spaces, rational varieties on suitable charts, and field extensions arising by specialization of their covers. The deeper problem of obtaining points on general varieties after a controlled finite extension requires the Moret--Bailly existence theorem. That theorem, including its totally real form, is reserved for the next book and is deliberately not smuggled into the geometric language here.

## 10. Worked arithmetic constructions

### 10.1 A thin-set failure made explicit

Return to the map

$$
\pi:\mathbf A^1\longrightarrow\mathbf A^1,\qquad u\longmapsto u^2.
$$

Its image $K^2$ is thin of type II. The cover is finite of degree two and étale away from $0$. For $a\ne0$, the fiber is connected exactly when $a\notin K^2$, because its coordinate algebra is $K[X]/(X^2-a)$.

Over $K=\mathbf Q$, the set $\mathbf Q^2$ is Zariski dense and is dense in the positive real half-line. Thus neither algebraic closure nor real topology detects the failure. Nevertheless, given finitely many local opens, Hilbert irreducibility finds a nonsquare in their product. If every real open is contained in $\mathbf R_{>0}$, this says positive nonsquares remain dense; the sign condition does not force squareness.

The image becomes all of the rational points after the base change $T=S^2$. This is a concrete warning that a thin map can lose its degree under pullback and that generic connectedness must be checked anew.

### 10.2 A totally real cubic with symmetric Galois group

Consider

$$
f_a(X)=X^3-X-a.
$$

Its discriminant is

$$
\Delta(a)=4-27a^2.
$$

The generic polynomial $X^3-X-T$ is irreducible over $\mathbf Q(T)$, and its discriminant is not a square there, so its generic Galois group is $S_3$. For

$$
a=\frac14,
$$

the polynomial is irreducible over $\mathbf Q$: the rational-root test applied to $4X^3-4X-1$ rules out the possible rational roots. Its discriminant is $37/16$, a positive nonsquare. Hence it has three real roots and its Galois closure is a totally real $S_3$-extension.

This one specialization also illustrates local cycle types. Modulo $5$, the polynomial has the factorization

$$
X^3-X-4=(X-3)(X^2+3X+3),
$$

and the quadratic factor is irreducible, giving cycle type $(1,2)$. Modulo $7$, the reduction $X^3-X-2$ has no root and is irreducible, giving a $3$-cycle. At $37$ the discriminant is not a unit, so the unramified cycle-type reading is unavailable and ramification occurs in the splitting field.

The two unramified cycle types generate enough subgroup information to certify $S_3$: a transposition and a $3$-cycle cannot lie together in a proper subgroup of $S_3$. This is the smallest visible model of the auxiliary-prime proof.

### 10.3 Prescribing several local partitions

Let $n=5$, and suppose we want a degree-five field $M/K$ with Galois closure $S_5$, completely split at $v_1$, inert and unramified at $v_2$, and with unramified factor degrees $(2,3)$ at $v_3$.

In the universal coefficient space choose local monic polynomials as follows:

- at $v_1$, a product of five distinct linear factors;
- at $v_2$, one irreducible polynomial of degree five over the residue field;
- at $v_3$, a product of distinct irreducibles of degrees two and three.

Lift them with unit discriminant and take small coefficient neighborhoods. The simultaneous theorem gives a global irreducible polynomial with full $S_5$ group and these local algebras. In the root field $M$, the three places have respectively five primes of degree one, one prime of degree five, and two primes of residue degrees two and three. In the Galois closure, their decomposition groups are cyclic groups generated by permutations of types $1^5$, $5$, and $(2)(3)$.

The last permutation has order six, so its decomposition group in the unramified Galois closure is cyclic of order six, not $C_2\times C_3$ presented as independent local choices. The cycle decomposition describes one Frobenius element; it does not make separate decomposition groups for the two factors of the root field.

### 10.4 A ramified local prescription

Fix an odd finite place $v$ with uniformizer $\pi_v$. The Eisenstein polynomial

$$
p_v(X)=X^n+\pi_v X+\pi_v
$$

is separable in characteristic zero and defines a totally ramified degree-$n$ local field when it is Eisenstein. A sufficiently small Krasner neighborhood of its coefficient vector defines the same local field, including the same ramification index, residue degree, discriminant exponent, and Galois closure decomposition data.

Place this neighborhood into the universal coefficient space and impose unramified models at other selected places. Hilbert irreducibility produces a global degree-$n$ field with this completion and with full $S_n$ Galois closure, provided the local Galois closure embeds with a subgroup structure compatible with $S_n$—which it automatically does through the action on the $n$ embeddings of the local field. What is not automatic is that the local degree-$n$ extension itself be Galois, or that its decomposition group equal all of $S_n$.

If the residue characteristic divides some relevant ramification index, the extension may be wild. Local constancy preserves that given wild extension, but this book makes no claim that arbitrary wild inertia filtrations can be designed from abstract group data.

### 10.5 An infinite sequence of independent fields

Let $K$ be totally real and fix $n\ge2$ and finitely many local algebra conditions, with complete real splitting at all real places. Construct $M_1$ by the totally real $S_n$ method. Having constructed $M_1,\ldots,M_r$, let $L_r$ be the compositum of their Galois closures and apply the disjoint specialization theorem with $L=L_r$.

This yields $M_{r+1}$ with the same local conditions and with Galois closure disjoint from $L_r$. Induction produces infinitely many totally real degree-$n$ fields whose Galois closures are pairwise linearly disjoint. The argument imposes only finitely many disjointness conditions at each stage; it does not take a countable intersection of Hilbert subsets.

The distinction is more than logical. Each new field is selected after the previous finite compositum is known. No uniform bound on the heights of the defining polynomials follows from this recursive existential construction.

## 11. Specializing finite étale covers

### 11.1 From a rational point to a finite algebra

The polynomial language is efficient when a single primitive element has already been chosen.
Many arithmetic constructions, however, begin with a cover whose sheets carry symmetries and
whose defining equations change from chart to chart. The intrinsic specialization problem is
therefore the following. Given a finite étale cover over a rational parameter space, can one
choose a rational parameter for which the fiber is connected while its fibers over selected
completions have prescribed, already realizable forms?

Let $X$ be a normal integral $K$-variety and let

$$
\pi:Y\longrightarrow X
$$

be finite étale of constant degree $n$. For $x\in X(K)$, the Cartesian fiber is

$$
Y_x=Y\times_X\operatorname{Spec}K=\operatorname{Spec}A_x,
$$

where $A_x$ is a finite étale $K$-algebra of dimension $n$. Thus

$$
A_x\cong F_{x,1}\times\cdots\times F_{x,r}
$$

for finite separable fields $F_{x,j}/K$ whose degrees sum to $n$. The fiber is connected exactly
when $r=1$, or equivalently when $A_x$ is a field. After completing at a place $v$,

$$
A_x\otimes_KK_v
\cong\prod_{w\mid v}(F_x)_w
$$

when $A_x=F_x$ is a field. Consequently the local fiber records all places above $v$ and all
their completions at once. A single chosen factor records only one place.

The generic hypothesis needed for connected specialization is equally exact. Since $X$ is
normal and integral, the finite étale scheme $Y$ is normal; its connected components are its
irreducible components. Hence $Y$ is connected if and only if its generic fiber is the spectrum
of a field. If $Y$
is disconnected, every fiber inherits a nontrivial open-and-closed decomposition after shrinking
$X$ if necessary, so no theorem can make all of $Y_x$ connected. We shall therefore assume that
each cover whose fiber is required to be connected has integral total space.

For a generically finite separable map that is not everywhere étale, one first removes the
branch locus and the locus where finiteness fails. This is not a loss of information: the
discarded parameters are precisely those at which degree, reducedness, or the covering
interpretation can degenerate.

### 11.2 Local constancy in families

Weak approximation can preserve a local fiber only if its isomorphism class is open in the
parameter. Chapter 6 proved this for one polynomial. The same phenomenon is intrinsic to finite
étale covers.

**Proposition 11.1 (local constancy of fibers).** Let $k$ be a completion of a number field, let
$X$ be a $k$-variety, and let $\pi:Y\to X$ be finite étale. For every $b\in X(k)$ there is an
open neighborhood $\Omega$ of $b$ in $X(k)$ such that

$$
Y_x\cong Y_b
$$

as finite étale $k$-schemes for every $x\in\Omega$. If a finite group acts on $Y$ over $X$, the
isomorphisms may be required to respect that action.

**Proof strategy.** Near $b$, choose one element that generates the fiber algebra and lift it to
the finite locally free algebra of the cover. Generation is detected by a determinant. Once that
determinant stays nonzero, the cover is described by the characteristic polynomial of the lifted
element, so the polynomial form of local constancy applies.

**Proof.** Work after base change to $k$ and replace $X$ by an affine neighborhood of $b$. Write
$X=\operatorname{Spec}R$ and $Y=\operatorname{Spec}B$, with $B$ finite locally free over $R$.
The fiber

$$
B_b=B\otimes_{R,b}k
$$

is a product of finite separable extensions of the infinite field $k$. Such a product has a
primitive element. Indeed, choose primitive elements in the field factors and translate them by
distinct scalars of $k$ so that their minimal polynomials are pairwise coprime; the tuple of the
translated elements then generates the product.

Lift a primitive element $\bar z\in B_b$ to a section $z$ of $B$ after shrinking the affine
neighborhood. The powers $1,z,\ldots,z^{n-1}$ form a basis at $b$. The determinant comparing these
powers with a local basis of $B$ is nonzero at $b$, so it remains invertible on a Zariski
neighborhood. There

$$
B\cong R[Z]/(p),
$$

where $p$ is the characteristic polynomial of multiplication by $z$. Its discriminant is
invertible because $B/R$ is étale. Evaluation of the coefficients of $p$ is continuous on
$X(k)$. At a nonarchimedean place, Proposition 6.3 gives a neighborhood on which the specialized
algebra is constant. At a real place, the numbers of real and complex factors are constant away
from the discriminant; over the complex numbers every finite étale algebra of rank $n$ is a
product of $n$ copies of the base field.

If a finite group acts, choose in a splitting field disjoint small balls around all roots of
$p_b$. Match each root of $p_x$ with the unique root in the corresponding ball. Every given group
element permutes the roots of every fiber. For $x$ sufficiently close to $b$, its image of the
root in one labeled ball must lie in the ball labeled by the image at $b$, because the finitely
many balls have positive mutual distance and the action maps are continuous. The resulting root
matching therefore intertwines every group element. Galois descent turns that equivariant root
matching into an equivariant isomorphism of the finite étale $k$-algebras. $\square$

The proposition preserves more than factor degrees. At a nonarchimedean place it preserves each
field factor up to $k$-isomorphism, hence its ramification index, residue degree, discriminant
exponent, normal closure, and ramification filtration. Reduction modulo the maximal ideal would
preserve only the unramified shadow; constancy of the full local algebra preserves the ramified
information as well.

### 11.3 The cover-specialization theorem

We can now state the intrinsic form of Hilbert irreducibility with local conditions. Its
hypotheses separate the global source of connectedness from the local source of the prescribed
fibers.

**Theorem 11.2 (finite-cover specialization with local conditions).** Let $K$ be a number field,
let $X$ be a nonempty open subvariety of $\mathbf A^m_K$, and let

$$
\pi_i:Y_i\longrightarrow X\qquad(1\le i\le r)
$$

be finite étale covers with each $Y_i$ integral. Let $S$ be a finite set of places. For every
$v\in S$, choose $b_v\in X(K_v)$ and an open neighborhood $\Omega_v$ of $b_v$ on which every
fiber $(Y_i)_x$ is isomorphic to $(Y_i)_{b_v}$ over $K_v$. Let $Z\subset X(K)$ be thin. Then
there exists $x\in X(K)\setminus Z$ such that

1. $x\in\Omega_v$ for every $v\in S$;
2. every global fiber $(Y_i)_x$ is connected;
3. for every $i$ and $v$,
   $$
   (Y_i)_x\times_KK_v\cong(Y_i)_{b_v}
   $$
   as finite étale $K_v$-schemes.

The set of such $x$ is dense in $\prod_{v\in S}\Omega_v$ and is not thin in $X(K)$.

**Proof strategy.** Connectedness of each generic cover gives one Hilbert condition. Avoidance of
$Z$ gives finitely many more. Local constancy has already converted every desired local fiber
into an ordinary open condition. The simultaneous Hilbert theorem then meets all of them at one
rational point.

**Proof.** Choose primitive elements on dense affine charts of the $Y_i$ and remove the finitely
many loci on which their denominators, leading coefficients, or discriminants vanish. The
condition that $(Y_i)_x$ be connected is the irreducibility of the resulting primitive-element
polynomial. Since $Y_i$ is integral, that polynomial is irreducible over $K(X)$. Thus the common
connected-fiber locus is a Hilbert subset of $X(K)$.

By Proposition 2.1, there is a basic Hilbert subset disjoint from the given thin set $Z$.
Intersect it with the finitely many connected-fiber conditions. Corollary 4.4
meets this intersection inside the local box $\prod_v\Omega_v$. Proposition 11.1 gives the local
fiber isomorphisms. Repeating the argument in every smaller local box proves density.

If the resulting set were thin, Proposition 2.1 would provide a further basic Hilbert subset
disjoint from it. Intersecting that further condition with all the preceding ones and applying
Corollary 4.4 would produce a point both in and outside the resulting set, a contradiction. Hence
the set is not thin. $\square$

The same theorem holds on a $K$-rational geometrically integral variety after restricting to a
rational chart. The local neighborhoods must meet that chart. On an arbitrary variety, local
points and Hilbert conditions do not themselves create a rational point; this is exactly the
boundary described in Section 9.5.

### 11.4 Galois covers and specialization homomorphisms

When a cover has a group of deck transformations, connectedness of a fiber admits a sharper
description. It becomes surjectivity of a homomorphism, and local fibers become restrictions of
that homomorphism.

Let $Y\to X$ be a connected finite étale Galois cover with deck group $G$. Choose a right action
of $G$ on $Y$. For $x\in X(K)$, choose a geometric point $y$ of $Y_x$. The absolute Galois group
of $K$ acts on the geometric fiber and commutes with the right $G$-action. There is therefore a
unique continuous homomorphism

$$
\rho_x:G_K\longrightarrow G
$$

such that

$$
\sigma(y)=y\cdot\rho_x(\sigma).
$$

Replacing $y$ by $y\cdot g$ conjugates $\rho_x$ by $g$. Thus its conjugacy class is intrinsic.
The image $D_x=\rho_x(G_K)$ is the specialization group introduced in Section 4.5.

**Proposition 11.3.** With this notation, the following are equivalent.

1. $Y_x$ is connected.
2. The action of $G_K$ on the geometric fiber is transitive.
3. $\rho_x$ is surjective.

If these conditions hold, $Y_x=\operatorname{Spec}F_x$ for a finite Galois extension $F_x/K$
whose group is identified with $G$ up to the chosen left-right convention.

**Proof.** Connected components of a finite étale $K$-scheme correspond to orbits of $G_K$ on
its geometric points. The geometric fiber of a Galois cover is a simply transitive $G$-set.
Starting at $y$, the $G_K$-orbit is

$$
\{y\cdot\rho_x(\sigma):\sigma\in G_K\}=y\cdot D_x.
$$

It is the whole fiber exactly when $D_x=G$. In that case the connected finite étale algebra is
a field. Its automorphisms arise from the deck transformations, and their number is its degree,
so the extension is Galois with group $G$. $\square$

For a place $v$ and an embedding of a separable closure of $K$ into one of $K_v$, restriction
gives

$$
\rho_{x,v}:G_{K_v}\longrightarrow G.
$$

Changing the embedding conjugates its image. If $F_x/K$ is the connected specialization, then
the image is the decomposition group $D_w$ of the corresponding place $w\mid v$. At a finite
place, the image of inertia is $I_w$, and the quotient $D_w/I_w$ is generated by arithmetic
Frobenius. Hence the global specialization homomorphism stores all local decomposition data by
restriction.

### 11.5 Prescribed decomposition and inertia

The preceding description makes the exact local theorem almost tautological, but it is worth
stating because it prevents a common loss of information between a local algebra and an abstract
subgroup.

**Theorem 11.4 (Galois specialization with prescribed local fibers).** Let $K$, $X$, and $S$ be
as in Theorem 11.2, and let $Y\to X$ be a connected finite étale Galois cover with group $G$.
For each $v\in S$, choose $b_v\in X(K_v)$ and let

$$
\rho_{b_v}:G_{K_v}\longrightarrow G
$$

be the homomorphism attached to the local fiber, defined up to conjugacy. Then there exists
$x\in X(K)$, arbitrarily close to all the $b_v$, such that

1. $\rho_x:G_K\to G$ is surjective;
2. for every $v\in S$, the restriction $\rho_x|_{G_{K_v}}$ is conjugate to $\rho_{b_v}$.

One may simultaneously avoid a thin subset and impose finitely many further connected-cover
conditions.

**Proof.** Proposition 11.1, with the $G$-action retained, gives an open neighborhood $\Omega_v$
of $b_v$ on which the local fibers are isomorphic as $G$-torsors. Such an isomorphism identifies
the associated local homomorphisms up to the conjugacy caused by choosing a point of the torsor.
Apply Theorem 11.2 to the cover $Y\to X$ and the neighborhoods $\Omega_v$. Connectedness of the
global fiber makes $\rho_x$ surjective by Proposition 11.3, and equivariant local constancy gives
the restrictions. $\square$

At a nonarchimedean $v$, write $D_v$ and $I_v$ for the image of $G_{K_v}$ and its inertia
subgroup under $\rho_{b_v}$. The resulting Galois field satisfies

$$
F_x\otimes_KK_v\cong\prod_{G/D_v}L_v,
$$

where every factor is a conjugate of one finite Galois extension $L_v/K_v$ with group $D_v$ and
inertia $I_v$. In particular, the theorem prescribes the pair

$$
I_v\triangleleft D_v\subseteq G
$$

only when that pair is realized by the chosen local fiber. This hypothesis automatically
contains the conditions that $D_v/I_v$ be cyclic and that the ramification be possible in the
residue characteristic. An abstract pair of subgroups is not enough.

At a real place, the local group has order at most two. Its nontrivial element is the conjugacy
class of complex conjugation. Prescribing a real local fiber therefore prescribes the orbit
structure of a complex conjugation element on every permutation representation of $G$. At a
complex place the local group is trivial.

For a connected non-Galois cover of degree $n$, pass on a dense open to a connected Galois
closure $\widetilde Y\to X$. A connected specialization of $\widetilde Y$ preserves the full
generic monodromy group. The original local algebra is obtained by taking the associated coset
set, so its field factors are the orbits of each local decomposition group. This recovers the
factorization--orbit dictionary of Section 5.7 without choosing a global polynomial.

### 11.6 Several covers and one point

Applications often require one parameter to specialize several covers, preserve a Galois group,
and keep a different fiber disjoint from a fixed extension. These are not separate approximation
problems. Each is a connectedness demand on a finite cover, so they belong in one finite
intersection.

Let $Y_i\to X$ be connected finite étale covers. Their fiber product need not be connected: two
generic function fields may intersect. Requiring each $(Y_i)_x$ to be connected is therefore
weaker than requiring the whole fiber product to be connected, and it is usually the intended
condition. If independence is intended, take a connected component of the generic fiber product
corresponding to the compositum and explicitly require that component to have the product degree.

For disjointness from a finite extension $L/K$, base change a regular generic cover to $L$ and
descend the resulting connectedness condition to $K$ as in Chapter 7. For preservation of several
finite Galois images, take the compositum of their fixed fields. For prescribed local behavior,
intersect the equivariant constancy neighborhoods supplied by Proposition 11.1. All of these
operations remain finite, so Theorem 11.2 applies.

This explains why the theorem is robust under adding conditions but not under taking an
uncontrolled infinite list. Every new cover contributes finitely much monodromy data. Infinitely
many covers can have infinitely many independent finite quotients, and no one application of
weak approximation can encode them all.

### 11.7 Bounded-degree local data

Some applications do not name one local extension. They ask that every local field arising in a
construction of bounded degree belong to an allowed class, or that a condition be checked after
all extensions of bounded degree. At first sight this is an infinite list. Over a
nonarchimedean completion of a number field, local finiteness turns it into a finite problem.

**Proposition 11.5 (finite reduction of bounded local conditions).** Let $k$ be a finite
extension of $\mathbf Q_p$ and let $n\ge1$.

1. There are only finitely many $k$-isomorphism classes of field extensions of degree at most
   $n$.
2. There are only finitely many $k$-isomorphism classes of finite étale $k$-algebras of dimension
   $n$.
3. If $Y\to X$ is finite étale of degree $n$, any condition on $Y_x$ that depends only on its
   $k$-algebra isomorphism class cuts out an open-and-closed subset of $X(k)$.

**Proof.** The first assertion is the bounded-degree finiteness theorem for characteristic-zero
local fields: write an extension as its unique unramified stage followed by a totally ramified
stage, parameterize the latter by Eisenstein polynomials, and use compactness together with
Krasner local constancy. For the second assertion, a finite étale algebra is a product of finite
separable fields. There are finitely many partitions of $n$, and the first assertion gives only
finitely many choices for every factor in a fixed partition.

For the third assertion, Proposition 11.1 says that the map

$$
X(k)\longrightarrow
\{\text{isomorphism classes of rank-$n$ finite étale $k$-algebras}\}
$$

is locally constant. The target is finite by part 2. The inverse image of any collection of its
points is therefore open, and so is its complement; hence it is open and closed. $\square$

For a finite set of places and one common degree bound, the union of all local isomorphism types
is still finite. A simultaneous demand quantified over those types may therefore be expanded
into finitely many local clauses before Theorem 11.2 is applied. This is the precise use of
bounded-degree local finiteness: it reduces the number of conditions, but it does not say that
one fiber can have mutually incompatible types.

The characteristic-zero hypothesis is decisive. Over $\mathbf F_q((t))$ there are infinitely
many separable extensions of degree $p$ in characteristic $p$, supplied by Artin--Schreier
equations with different pole breaks. A bounded-degree quantifier there need not collapse to a
finite list. The present global theory concerns number fields, so all their nonarchimedean
completions lie in the finite regime.

### 11.8 Examples and boundary cases

The power cover gives the simplest model. Over

$$
X=\mathbf G_m,
$$

the equation

$$
Z^n=T
$$

defines a finite étale cover in characteristic zero. Its fiber at $a\in K^\times$ is
$K[Z]/(Z^n-a)$. Connectedness means that $Z^n-a$ is irreducible. A local neighborhood of
$b_v\in K_v^\times$ preserves the entire local algebra, not merely whether $b_v$ is an $n$th
power. If $K$ contains the $n$th roots of unity, the Galois closure is visible directly through
the multiplicative deck action; otherwise the constant cyclotomic extension must be tracked.

For the double cover

$$
Z^2=T(T-1)
$$

of $\mathbf A^1\setminus\{0,1\}$, a real interval among the three components
$(-\infty,0)$, $(0,1)$, and $(1,\infty)$ fixes the real splitting type. At an odd finite place,
a sufficiently small neighborhood fixes the square class of $b_v(b_v-1)$ and hence the local
quadratic algebra. Theorem 11.2 chooses one rational $a$ meeting all these local choices while
keeping the global quadratic fiber a field.

Four failures delineate the theorem.

First, if the generic cover is disconnected, connected specializations cannot be demanded.
Second, a prescribed local algebra must occur at some local point of the given family; local
constancy preserves an existing fiber but does not invent one. Third, points on the branch locus
are excluded because their fibers need not be reduced or have the generic degree. Fourth, if the
base is not rational and has no suitable rational points, a Hilbert condition supplies no point
from which to start.

These are exact failures, not technical blemishes. Once generic connectedness, local
realizability, the good locus, and a rational parameter space are present, specialization of a
finite cover is as flexible as specialization of one polynomial: its global monodromy can remain
maximal while finitely many local fibers remain fixed.

## 12. A simultaneous-conditions theorem

### 12.1 Setting up compatible data

We now package the book's tools in the form most useful for choosing auxiliary fields. Let $K$ be a number field, let $n\ge2$, and write $\mathcal P_n\cong\mathbf A^n_K$ for the coefficient space of monic degree-$n$ polynomials. Its universal polynomial is

$$
F(\mathbf T,X)=X^n+T_1X^{n-1}+\cdots+T_n.
$$

Let $S$ be a finite set of places. For each $v\in S$, choose a degree-$n$ finite étale $K_v$-algebra $A_v$. Since $K_v$ is infinite and $A_v$ is a finite product of separable fields, a primitive-element argument writes

$$
A_v\cong K_v[X]/(p_v)
$$

for a monic separable polynomial $p_v$. Local constancy gives a nonempty open neighborhood $\Omega_v\subset\mathcal P_n(K_v)$ on which the fiber algebra is $A_v$.

At a real place, $A_v$ is of the form

$$
\mathbf R^{r_v}\times\mathbf C^{(n-r_v)/2},
$$

with $r_v\equiv n\pmod 2$. If total reality is demanded, $K$ must be totally real, every real place must be included in $S$, and one must choose $A_v=\mathbf R^n$ there. These are compatibility assumptions, not conclusions of the theorem.

Finally, let $L/K$ be a finite extension, let $Z\subset\mathcal P_n(K)$ be thin, and let $H_1,\ldots,H_r$ be finitely many additional Hilbert conditions arising from integral generically finite separable covers of open subsets of $\mathcal P_n$. All data are finite.

### 12.2 The packaged theorem

**Theorem 12.1 (simultaneous arithmetic specialization).** With the data of Section 12.1, there exists a coefficient vector

$$
\mathbf a\in\mathcal P_n(K)\setminus Z
$$

such that:

1. $\mathbf a\in\Omega_v$ for every $v\in S$;
2. $p_{\mathbf a}(X)=F(\mathbf a,X)$ is irreducible, so $M=K[X]/(p_{\mathbf a})$ has degree $n$;
3. $M\otimes_KK_v\cong A_v$ for every $v\in S$;
4. the Galois closure $\widetilde M/K$ has group $S_n$ in its natural degree-$n$ action;
5. $\widetilde M$ is linearly disjoint from $L$;
6. every additional Hilbert condition $H_i$ holds;
7. if $K$ is totally real, $S$ contains every real place, and $A_v=\mathbf R^n$ there, then $M$ and $\widetilde M$ are totally real.

The set of such coefficient vectors is dense in $\prod_{v\in S}\Omega_v$ and is not thin.

**Proof strategy.** Each conclusion will be identified either as a local open condition or as a Hilbert condition on the rational coefficient space. Their finite intersection is then handled by Corollary 4.4.

**Proof.** Conditions 1 and 3 are equivalent by the construction of the Krasner neighborhoods. At real places the same local constancy proves condition 7. The universal polynomial is generically irreducible, and its regular generic splitting field has group $S_n$. For completeness, if $x_1,\ldots,x_n$ are algebraically independent and $e_i$ are their elementary symmetric functions, the fundamental theorem on symmetric rational functions gives

$$
K(x_1,\ldots,x_n)^{S_n}=K(e_1,\ldots,e_n).
$$

The extension on the left has degree $n!$ over the fixed field. Thus $\prod_i(X-x_i)$ is the universal polynomial after identifying its coefficients with the $e_i$, its splitting field has group $S_n$, and the algebraically independent variables introduce no algebraic constants. The splitting field is therefore regular over $K$. Apply the full-group resolvent conditions over $K$ to obtain conditions 2 and 4.

Base change the regular generic splitting field to a normal closure $L'/K$ of $L$. It remains a field with group $S_n$. Descending the full-group Hilbert condition from $L'$ to parameters in $K$ gives

$$
[\widetilde M L':L'] = |S_n|=[\widetilde M:K],
$$

so $\widetilde M\cap L'=K$ and condition 5 follows. Add the finitely many covers defining the $H_i$. The thin set $Z$ is contained in the failure locus of another finite collection of cover conditions and a proper closed subset. The finite intersection is therefore a Hilbert subset.

Corollary 4.4 makes this Hilbert subset dense in the product of the local opens. To prove the stronger assertion, suppose that the set of coefficient vectors satisfying all seven conclusions were thin. Proposition 2.1 would supply finitely many further Hilbert conditions avoiding that thin set. Appending them to the conditions already imposed and applying Corollary 4.4 inside the same local box would produce a coefficient vector satisfying all seven conclusions but lying outside the alleged set of all such vectors, a contradiction. Thus the set is not thin. $\square$

### 12.3 Reading the local conclusions

The theorem contains several familiar prescriptions as choices of $A_v$.

- Take $A_v=K_v^n$ to force complete splitting.
- Take $A_v$ to be the unramified degree-$n$ field to force one unramified prime in the degree-$n$ root field.
- Take a product of unramified fields to impose a factorization partition.
- Take a specified ramified separable field or product to impose its decomposition and inertia behavior.
- At real places, choose the number of $\mathbf R$ and $\mathbf C$ factors to impose a signature.

In the $S_n$ Galois closure, an unramified local partition must be read as one cycle type. For ramified models, decomposition and inertia are determined only up to conjugacy. No incompatible abstract data are asserted to exist: the local algebra $A_v$ is the certificate that the desired condition is realizable.

### 12.4 Finite and infinite avoidance in the package

To avoid finitely many prescribed extensions, take $L$ to be the compositum of their normal closures. If an infinite Galois extension $\Omega/K$ has only finitely many subfields of degree at most $n!$, include their normal closures in $L$. Since $[\widetilde M:K]=n!$, any nontrivial intersection $\widetilde M\cap\Omega$ would be among these bounded-degree subfields, contradicting disjointness from $L$.

The bound $n!$ is needed when avoiding intersection with the Galois closure. If only the degree-$n$ root field matters, degree $n$ bounds its intersection, but trivial intersection may still be weaker than linear disjointness unless a Galois hypothesis is present. Using the closure produces the cleanest statement at the cost of the larger bound.

For an arbitrary infinite extension with infinitely many bounded-degree subfields, Theorem 12.1 makes no avoidance promise. That exact limit prevents a finite Hilbert argument from being mistaken for an infinite approximation theorem.

This is the specialization interface used for later Moret--Bailly and automorphy fields. Put in
$L$ the finite extensions cut out by the residual representations whose images must survive;
when $K$ is totally real and total reality is required, include every real place, and also include
every finite place carrying a deformation or automorphic local type in $S$; choose the algebras
$A_v$ to encode the required completions; and put the finitely many
monodromy or level-structure demands among the covers $H_i$. Theorem 12.1 then gives an auxiliary
field of the chosen degree whose Galois closure is disjoint from $L$, whose local completions have
the prescribed realizable types, and on which all the listed finite covers stay connected; under
the stated totally real hypotheses, the field and its Galois closure are totally real. This
conclusion is conditional only on the explicit compatibility of those local
models. It does not manufacture a point on a nonrational moduli variety: the later
Moret--Bailly theorem supplies that geometric existence step, after which the specialization and
disjointness controls proved here apply.

### 12.5 Existential and effective content

The proof identifies all exceptional conditions algebraically: discriminants and denominators define closed loci, factorization and subgroup failures define finite covers, and local algebras define explicit Krasner neighborhoods. In that qualitative sense the construction is concrete.

It is not accompanied by a bound for the height of $\mathbf a$ or the discriminant of $M$. The proof of number-field Hilbert irreducibility used large split auxiliary primes and a finite-field point estimate; an effective version would have to bound those primes and then quantify simultaneous approximation. Such refinements are possible only after supplying analytic and height estimates absent from the present argument. Every theorem above should therefore be read as existential unless an explicit example has actually been calculated.

## 13. The arithmetic freedom of specialization

### 13.1 The hierarchy of conditions

The theory assembled here has a useful order. First remove degeneration: denominators, leading coefficients, and branch discriminants. Next translate each desired completion into a nonempty local open through Hensel lifting or Krasner's lemma. Then express global requirements—irreducibility, full Galois group, connected fibers after base change—as Hilbert conditions. Finally combine the finite local opens by weak approximation while auxiliary Frobenius congruences keep the parameter in the Hilbert subset.

The dependencies run in one direction:

$$
\begin{array}{c}
\text{realizable local fibers and good locus}\\
\downarrow\\
\text{local open conditions}\\
\downarrow\\
\text{weak approximation compatible with Hilbert conditions}\\
\downarrow\\
\text{global field, full monodromy, and disjointness}.
\end{array}
$$

Hilbert irreducibility does not repair an empty local open, an impossible inertia quotient, a parity-violating signature, or a constant field already shared with an extension to be avoided. Once these obstructions are removed, it says that finitely many remaining demands do not compete for a scarce set of rational parameters.

### 13.2 The roles of decomposition and inertia

At a good unramified finite place, one Frobenius conjugacy class records the residue factorization. Arithmetic Frobenius acts by $x\mapsto x^{|k_v|}$, in agreement with the global convention. In a ramified specialization, inertia records what reduction loses and Frobenius lives canonically only in $D/I$. Local constancy of the entire completion, rather than reduction alone, is what preserves a prescribed ramified structure.

Globally, specialization groups are decomposition groups for the valuation $T-a$ in a function-field Galois extension. This is the conceptual hinge of the proof: local Frobenius elements at auxiliary arithmetic primes lie inside one global specialization subgroup. Choosing enough of them rules out every proper maximal subgroup.

### 13.3 The roles of regularity and normality

Normality makes a cover recoverable from its function field and makes specialization groups honest decomposition groups. Geometric irreducibility removes hidden constant extensions. Regularity of a generic splitting field then permits base change to every prescribed finite extension without losing connectedness. These properties solve different problems and none may silently substitute for another.

For a nonregular cover, Hilbert irreducibility remains valid, but the constant quotient must survive every specialization. For a regular cover, disjointness from fixed constant extensions becomes available. For a non-Galois specialized root field, full generic monodromy describes its Galois closure and does not turn the root field itself into a Galois extension.

### 13.4 Conclusion

Specialization begins with a moving equation and ends with an arithmetic field. Between those endpoints lie two kinds of rigidity. Finite étale geometry keeps degree and separability stable away from the branch locus; local field rigidity keeps a chosen completion unchanged in a sufficiently small neighborhood. Hilbert irreducibility supplies the complementary freedom: after those rigid local neighborhoods are fixed, rational parameters retaining generic connectedness and monodromy remain dense.

For number fields this freedom is not mysterious. A finite list of auxiliary reductions places carefully chosen Frobenius classes inside the specialization group. Derangements ensure that those classes escape every possible proper maximal subgroup, and weak approximation merges their congruences with the local conditions that arithmetic applications actually care about. The same mechanism preserves several covers, detects full Galois groups through resolvents, and enforces irreducibility after base change.

In the intrinsic language, a rational point turns a finite étale cover into a finite algebra and
a Galois cover into a specialization homomorphism. Connectedness is surjectivity of that
homomorphism; restriction to a completion gives its decomposition and inertia groups. Equivariant
local constancy therefore preserves prescribed local torsors exactly, while bounded-degree
finiteness over nonarchimedean completions reduces quantified local requirements to a finite list.
This is why polynomial equations, field extensions, and finite covers obey one specialization
theorem rather than three parallel principles.

The resulting toolkit has exact boundaries. It handles finitely many local and global conditions; infinite avoidance requires a separate finite-subextension argument. It preserves only locally realizable decomposition and inertia data. Total reality requires a totally real base and complete real splitting at every archimedean place. Disjointness requires regularity or an explicit generic intersection calculation. Within those boundaries, one may construct extensions of prescribed degree and signature, with controlled completions, full symmetric Galois closure, and no unwanted intersection with a prescribed finite extension. That is the arithmetic strength of Hilbert irreducibility: generic behavior can be made concrete without surrendering finite local control.
