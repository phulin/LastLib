# Rigid Analytic Curves and Formal Models

## Contents

1. [Why nonarchimedean geometry is rigid](#1-why-nonarchimedean-geometry-is-rigid)
   - [Convergence must be built into geometry](#11-convergence-must-be-built-into-geometry)
   - [Standing conventions](#12-standing-conventions)
   - [Three kinds of fiber](#13-three-kinds-of-fiber)
2. [Tate algebras](#2-tate-algebras)
   - [Functions on a closed polydisc](#21-functions-on-a-closed-polydisc)
   - [The Gauss norm and completeness](#22-the-gauss-norm-and-completeness)
   - [Evaluation and the maximum principle](#23-evaluation-and-the-maximum-principle)
   - [Units and geometric series](#24-units-and-geometric-series)
   - [Division, preparation, and noetherianity](#25-division-preparation-and-noetherianity)
   - [Finite residue fields and the nullstellensatz](#26-finite-residue-fields-and-the-nullstellensatz)
3. [Affinoid algebras and their spaces](#3-affinoid-algebras-and-their-spaces)
   - [Quotients as bounded analytic sets](#31-quotients-as-bounded-analytic-sets)
   - [Points and residue fields](#32-points-and-residue-fields)
   - [Spectral size and power-bounded elements](#33-spectral-size-and-power-bounded-elements)
   - [Products, nilpotents, and dimension](#34-products-nilpotents-and-dimension)
4. [Rational localization](#4-rational-localization)
   - [Inequalities as coordinate rings](#41-inequalities-as-coordinate-rings)
   - [The universal property](#42-the-universal-property)
   - [Weierstrass and Laurent domains](#43-weierstrass-and-laurent-domains)
   - [Flatness and transitivity](#44-flatness-and-transitivity)
   - [Why ordinary localization is insufficient](#45-why-ordinary-localization-is-insufficient)
5. [Admissible opens and gluing](#5-admissible-opens-and-gluing)
   - [The topology is a Grothendieck topology](#51-the-topology-is-a-grothendieck-topology)
   - [Tate acyclicity](#52-tate-acyclicity)
   - [The structure sheaf](#53-the-structure-sheaf)
   - [Gluing affinoid spaces](#54-gluing-affinoid-spaces)
   - [Separatedness and intersections](#55-separatedness-and-intersections)
6. [Coherent sheaves](#6-coherent-sheaves)
   - [Finite modules are the local objects](#61-finite-modules-are-the-local-objects)
   - [Acyclicity and exactness](#62-acyclicity-and-exactness)
   - [Gluing and pullback](#63-gluing-and-pullback)
   - [Proper direct images](#64-proper-direct-images)
7. [Admissible formal schemes and generic fibers](#7-admissible-formal-schemes-and-generic-fibers)
   - [Integral coordinates before inversion](#71-integral-coordinates-before-inversion)
   - [The affine generic fiber](#72-the-affine-generic-fiber)
   - [Formal opens become analytic domains](#73-formal-opens-become-analytic-domains)
   - [Gluing the generic fiber](#74-gluing-the-generic-fiber)
   - [Morphisms and base change](#75-morphisms-and-base-change)
8. [Specialization and reduction](#8-specialization-and-reduction)
   - [The center of an analytic point](#81-the-center-of-an-analytic-point)
   - [Fibers of specialization](#82-fibers-of-specialization)
   - [Reduction of an affinoid algebra](#83-reduction-of-an-affinoid-algebra)
   - [Anticontinuity and functoriality](#84-anticontinuity-and-functoriality)
9. [Admissible blowups and invariance](#9-admissible-blowups-and-invariance)
   - [Blowing up only the special fiber](#91-blowing-up-only-the-special-fiber)
   - [Affine charts](#92-affine-charts)
   - [Invariance of the generic fiber](#93-invariance-of-the-generic-fiber)
   - [Common refinements and the model theorem](#94-common-refinements-and-the-model-theorem)
10. [Tubes](#10-tubes)
    - [Analytic neighborhoods cut out by reduction](#101-analytic-neighborhoods-cut-out-by-reduction)
    - [Discs above smooth points](#102-discs-above-smooth-points)
    - [Annuli above nodes](#103-annuli-above-nodes)
    - [Strict neighborhoods and excision](#104-strict-neighborhoods-and-excision)
11. [Curves in rigid geometry](#11-curves-in-rigid-geometry)
    - [Dimension one and local parameters](#111-dimension-one-and-local-parameters)
    - [Smooth, normal, and regular curves](#112-smooth-normal-and-regular-curves)
    - [Finite maps and normalization](#113-finite-maps-and-normalization)
    - [Boundary and wide-open curves](#114-boundary-and-wide-open-curves)
12. [Proper rigid curves](#12-proper-rigid-curves)
    - [The valuative meaning of properness](#121-the-valuative-meaning-of-properness)
    - [Finite-dimensional cohomology](#122-finite-dimensional-cohomology)
    - [Meromorphic functions and divisors](#123-meromorphic-functions-and-divisors)
    - [Projectivity and algebraization](#124-projectivity-and-algebraization)
13. [Formal models of proper curves](#13-formal-models-of-proper-curves)
    - [Existence from algebraic models](#131-existence-from-algebraic-models)
    - [Extension of analytic data](#132-extension-of-analytic-data)
    - [Semistable formal curves](#133-semistable-formal-curves)
    - [Components, annuli, and the reduction graph](#134-components-annuli-and-the-reduction-graph)
14. [Comparison with algebraic curves](#14-comparison-with-algebraic-curves)
    - [Analytification of a finite-type curve](#141-analytification-of-a-finite-type-curve)
    - [Proper comparison for coherent objects](#142-proper-comparison-for-coherent-objects)
    - [Maps, finite covers, and divisors](#143-maps-finite-covers-and-divisors)
    - [Exactly where comparison fails](#144-exactly-where-comparison-fails)
15. [A reusable dictionary](#15-a-reusable-dictionary)
    - [Hypothesis ledger](#151-hypothesis-ledger)
    - [The model-independence principle](#152-the-model-independence-principle)
    - [Conclusion](#153-conclusion)

## 1. Why nonarchimedean geometry is rigid

### 1.1 Convergence must be built into geometry

Algebraic geometry permits every polynomial and excludes every genuinely infinite series. Analysis permits infinite series, but only on regions where they converge. Over a complete nonarchimedean field the convergence condition is exceptionally sharp: a series converges exactly when its terms tend to zero. The geometry developed here begins by encoding that condition in its coordinate rings.

There is an immediate obstacle. If one puts the usual topology on the set of points of a closed unit disc, many natural finite decompositions are not open covers. For example, the conditions $|T|\leq |a|$ and $|T|\geq |a|$ define closed pieces whose union is the disc. Analytic functions nevertheless glue across such decompositions. The correct notion of cover must therefore remember which systems of inequalities permit finite algebraic descent, not merely which subsets are open in a point-set topology.

The word _rigid_ reflects the outcome. A function on a connected disc cannot be prescribed independently on arbitrarily many residue classes; convergent coefficients tie those values together. A compact analytic curve is even more constrained: it comes from a projective algebraic curve, and its coherent sheaves and cohomology are algebraic. Formal models reveal where this rigidity comes from. They record integral functions before a uniformizer is inverted, so reduction of those functions organizes the analytic space into discs and annuli.

### 1.2 Standing conventions

Throughout Chapters 1--6, $K$ is a complete field with a nontrivial nonarchimedean absolute value $|\cdot|$. Its valuation ring, maximal ideal, and residue field are

$$
K^\circ=\{a:|a|\leq1\},\qquad
K^{\circ\circ}=\{a:|a|<1\},\qquad
\widetilde K=K^\circ/K^{\circ\circ}.
$$

A finite extension of $K$ carries the unique extended absolute value. Whenever formal models enter, beginning in Chapter 7, $K$ is assumed discretely valued, $R=K^\circ$, and $\pi\in R$ is a uniformizer. Then $R$ is complete and $K=R[1/\pi]$. The residue field need not be finite or perfect unless a statement explicitly says so.

We use the classical strict theory: coordinate radii belong to $|K^\times|$. Closed polydiscs of arbitrary positive radii can be handled by weighted norms, and after adjoining elements having the required absolute values they reduce to the strict case. Nothing below silently assumes that $K$ is algebraically closed. A _point_ of an affinoid space means a maximal ideal, whose residue field is a finite extension of $K$; geometric points over larger complete fields may be used when base change is relevant.

All rings are commutative. Analytic spaces are assumed quasi-separated when intersections or coherent descent are discussed, and formal schemes are locally noetherian and topologically of finite type over $R$ unless stated otherwise.

The dependency boundary is as follows. Book 1 supplies completeness, extensions of the
absolute value to finite fields, valuation rings, and Hensel lifting. Book 11 supplies finite
normalization and regular proper models of algebraic curves over the excellent DVR $R$; it
explicitly does not supply semistable reduction. Book 58 supplies adic rings, formal spectra,
formal completion, coherent formal sheaves, and proper formal algebraization, but constructs
no nonarchimedean generic fiber. The Tate-algebra, rigid-space, generic-fiber, and rigid GAGA
theorems used below are therefore proved in this book rather than attributed to those
prerequisites.

### 1.3 Three kinds of fiber

Let $\mathfrak X$ be a flat formal scheme over $\operatorname{Spf}R$. It has two honest fibers and mediates between two geometries:

$$
\mathfrak X_s
\xleftarrow{\ \mathrm{red}\ }
\mathfrak X
\xrightarrow{\ \mathrm{gen}\ }
\mathfrak X_\eta.
$$

The special fiber $\mathfrak X_s$ is obtained by setting $\pi=0$. The generic fiber $\mathfrak X_\eta$ is obtained by inverting $\pi$ and retaining convergence. The formal scheme itself is not a third ordinary fiber: it is the compatible system of all thickenings modulo $\pi^{n+1}$.

For an algebraic $R$-scheme $\mathcal X$, one must distinguish its algebraic generic fiber $\mathcal X_K$, its completion $\widehat{\mathcal X}$ along the special fiber, and the analytic generic fiber of that completion. When $\mathcal X$ is proper, the last space is exactly the analytification of $\mathcal X_K$. When $\mathcal X$ is not proper, completion sees only the analytic region specializing to the chosen special fiber. The affine line illustrates the boundary: completing $\mathbf A^1_R$ along its entire special fiber produces the closed unit disc, not the whole analytic affine line.

This distinction is the organizing theme of the book. Algebraic generic fibers control global curves; formal generic fibers control bounded regions; admissible blowups change integral coordinates while leaving the analytic generic fiber unchanged.

## 2. Tate algebras

### 2.1 Functions on a closed polydisc

The closed unit polydisc should admit exactly those power series that converge whenever every coordinate has absolute value at most one. For a multi-index $\nu=(\nu_1,\ldots,\nu_n)\in\mathbf N^n$, write $T^\nu=T_1^{\nu_1}\cdots T_n^{\nu_n}$. The **Tate algebra** is

$$K\langle T_1,\ldots,T_n\rangle

\left\{\sum_{\nu\in\mathbf N^n}a_\nu T^\nu:
|a_\nu|\longrightarrow0\text{ as }|\nu|\longrightarrow\infty\right\}.
$$

If $x_i$ lie in any complete extension of $K$ and $|x_i|\leq1$, then $|a_\nu x^\nu|\leq|a_\nu|\to0$. Hence the sum converges. Conversely, testing at the universal bounded coordinates forces the coefficients to tend to zero; unrestricted formal series are therefore too large.

For radii $r_i>0$, the weighted algebra consists of series satisfying $|a_\nu|r^\nu\to0$, with $r^\nu=\prod r_i^{\nu_i}$. If $r_i=|c_i|$, substitution $T_i=c_iU_i$ identifies it with a unit-radius algebra. The strict theory keeps these radii inside the value group so that changes of scale remain defined over $K$.

**Example.** The geometric series $\sum_{m\geq0}T^m$ is not in $K\langle T\rangle$, because its coefficients do not tend to zero. It does define a function on every smaller closed disc $|T|\leq r<1$. Thus one analytic function may live on an open disc without extending to its closed boundary.

### 2.2 The Gauss norm and completeness

The coefficient condition is captured by the **Gauss norm**

$$
\left\|\sum_\nu a_\nu T^\nu\right\|_G=\max_\nu|a_\nu|.
$$

The maximum exists because the coefficients tend to zero. The ultrametric inequality is immediate. More importantly,

$$
\|fg\|_G=\|f\|_G\|g\|_G.
$$

To see why cancellation cannot lower the largest coefficient, scale so both norms are one and reduce coefficients modulo $K^{\circ\circ}$. The reductions $\widetilde f$ and $\widetilde g$ are nonzero polynomials over the field $\widetilde K$, because only finitely many coefficients have absolute value one. Their product is nonzero. Some coefficient of $fg$ therefore remains a unit, proving multiplicativity. This argument also explains why a field of residues, rather than an arbitrary quotient ring, is decisive.

The Tate algebra is complete for this norm. If $(f_m)$ is Cauchy, every coefficient sequence is Cauchy in $K$ and has a limit. Uniform control on the tails shows that the limiting coefficients still tend to zero and that $f_m$ converges in Gauss norm. Polynomials are dense: truncating a restricted series gives polynomial approximations.

Completeness permits geometric-series inversion. It also makes bounded homomorphisms the natural maps. In the strict affinoid setting every algebra homomorphism between affinoid algebras is automatically continuous, but continuity is proved from finite presentation and should not be presumed for arbitrary complete topological rings.

### 2.3 Evaluation and the maximum principle

For $x=(x_1,\ldots,x_n)$ in the closed unit polydisc over a complete extension,

$$
|f(x)|\leq\|f\|_G.
$$

This inequality is just the strong triangle inequality. Equality need not hold at a $K$-rational point; there may be too few such points. It does hold after allowing all maximal points in the following spectral form: the Gauss norm of the Tate algebra equals the supremum of $|f(x)|$ over its maximal ideals, with the uniquely extended absolute value on each finite residue field.

The proof uses a generic point rather than a lucky rational value. If $c=\|f\|_G$, scale when possible so $c=1$. The nonzero reduction $\widetilde f$ avoids some maximal ideal after a suitable finite residue extension. Lifting that point gives an evaluation of size one. The general value follows by scaling or passage to a valued extension. This is the nonarchimedean maximum principle for a closed polydisc.

A crucial warning is that the maximum principle does not say a nonconstant analytic function has no interior maximum. The function $T$ has absolute value one on the entire boundary and smaller values inside; ultrametric geometry allows large clopen level sets. The useful conclusion is algebraic: a function vanishing at every maximal point is nilpotent in a general affinoid algebra, and is zero when that algebra is reduced.

### 2.4 Units and geometric series

Suppose

$$
f=a_0+h,\qquad \|h\|_G<|a_0|.
$$

Then

$$
f^{-1}=a_0^{-1}\sum_{m\geq0}(-a_0^{-1}h)^m
$$

converges in the Tate algebra. Thus a dominant constant term makes a unit. In one variable the converse holds: $f=\sum a_mT^m$ is a unit precisely when $|a_0|>|a_m|$ for every $m>0$. In several variables the same condition with all nonconstant coefficients is again necessary and sufficient.

This criterion separates analytic from formal invertibility. The series $1-T$ has constant coefficient one, but its other coefficient has equal size; it is not a unit on the closed disc because it vanishes at $T=1$. It is a unit on every smaller disc. Domain matters.

An element $u$ with $\|u\|<1$ is topologically nilpotent, because $u^m\to0$. Such elements play the role of infinitesimals. Elements of norm at most one are power bounded. Later, reduction will retain the latter modulo the former.

### 2.5 Division, preparation, and noetherianity

Finite presentation is indispensable for geometry, so the analytic coordinate ring must be noetherian. The proof is an analytic form of polynomial division.

Write $g=\sum_{j\geq0}g_jT_n^j$ with
$g_j\in K\langle T_1,\ldots,T_{n-1}\rangle$. Call $g$ **distinguished in
$T_n$ of degree $d$** if $g_d=1$, every $g_j$ with $j>d$ has norm less than one,
and every $g_j$ with $j<d$ has norm at most one. More generally one may allow $g_d$
to be a unit of norm one whose inverse also has norm one, and then divide by $g_d$. Merely
requiring $\|g_d\|=1$ would be insufficient: $g_d$ need not be a unit in the smaller Tate
algebra.

For distinguished $g$, every $f$ admits unique elements

$$
q\in K\langle T_1,\ldots,T_n\rangle,\qquad
r\in K\langle T_1,\ldots,T_{n-1}\rangle[T_n],\quad \deg_{T_n}r<d,
$$

such that $f=qg+r$. The quotient and remainder are obtained by repeatedly canceling the leading $T_n$-term. The error norms tend to zero, so completeness supplies the limit; the distinguished inequalities prevent the process from increasing norms. Uniqueness follows by comparing the highest surviving term.

Preparation factors a distinguished series as a unit times a monic polynomial of degree $d$
whose lower coefficients lie in the smaller Tate algebra. To make a nonzero series
distinguished, first scale it to Gauss norm one and reduce it to a nonzero polynomial. A
triangular substitution

$$
T_i\longmapsto T_i+T_n^{N_i}\quad(i<n),\qquad T_n\longmapsto T_n,
$$

with rapidly increasing $N_i$, makes the image of one chosen extremal monomial the unique
highest power of $T_n$ in the reduction. Its coefficient is a nonzero scalar; after scaling,
the transformed series is distinguished. This argument works over finite as well as infinite
residue fields because it separates monomials rather than choosing a generic residue value.

Induction on $n$, followed by division, now proves:

**Theorem 2.1 (Tate).** For every $n\geq0$, $K\langle T_1,\ldots,T_n\rangle$ is noetherian. Every ideal is closed for the Gauss topology, and every finite module is complete for a quotient norm.

Here is the finite-generation step. Given an ideal $I$, choose a nonzero element of $I$,
make it distinguished, and replace it by its prepared monic factor. Division identifies every
class modulo that element with a polynomial of degree less than $d$ in $T_n$. The image of
$I$ is therefore a submodule of a finite module over
$K\langle T_1,\ldots,T_{n-1}\rangle$; the induction hypothesis makes it finite, and lifting
generators makes $I$ finite. The same normal form gives a uniform estimate for the
coefficients of the quotient and remainder. Applied to a convergent sequence in $I$, that
estimate shows its limit remains in $I$. Thus every ideal is closed. Presenting a finite module
as a quotient of a finite free module and applying the same closed-submodule argument proves
its completeness.

### 2.6 Finite residue fields and the nullstellensatz

Points of an affine algebraic variety correspond to maximal ideals with finite residue extensions. The same finiteness survives analytically.

**Theorem 2.2 (analytic nullstellensatz).** If $A$ is a quotient of a Tate algebra and $\mathfrak m\subset A$ is maximal, then $A/\mathfrak m$ is a finite field extension of $K$.

**Proof.** It is enough to treat
$A=K\langle T_1,\ldots,T_n\rangle/\mathfrak m$. Put $L=A/\mathfrak m$. The analytic
form of Zariski's lemma says that if a field $F$ is finite over a Tate algebra
$K\langle S_1,\ldots,S_r\rangle$, then $r=0$ and $F/K$ is finite. To prove it, make a
nonzero relation distinguished in the last variable. Preparation makes that coordinate
integral over the preceding Tate algebra, and iteration reduces to the assertion that no field
can be finite over $K\langle S\rangle$ when at least one variable remains. In that case the
inverses of $S_r-a$ in the finite module would have denominators bounded by finitely many
coefficient norms. Choosing coefficients recursively with strictly decreasing norms produces
a restricted series whose successive division remainders require unbounded denominators, a
contradiction. The division estimates from Section 2.5 ensure that this is an equality of
convergent series rather than a merely formal construction.

Now use the same triangular changes of variables as in Section 2.5 to make $L$ finite over a
Tate algebra on a maximal algebraically independent family among the coordinate images. The
analytic lemma says that this family is empty. Thus all coordinate images are algebraic over
$K$, and the finitely many of them generate a finite extension. $\square$

The theorem implies that maximal ideals are closed and that evaluation at a point always
lands in a complete valued field. It does not say every point is $K$-rational.

## 3. Affinoid algebras and their spaces

### 3.1 Quotients as bounded analytic sets

A **strictly $K$-affinoid algebra** is a $K$-algebra isomorphic to

$$
A=K\langle T_1,\ldots,T_n\rangle/I.
$$

Its associated affinoid space is written $X=\operatorname{Sp}A$. As a set, $X$ is the set of maximal ideals of $A$. If $A$ is presented as above, it is the common zero locus of $I$ in the closed unit polydisc after allowing finite extensions of $K$.

The quotient seminorm is

$$
\|a\|_q=\inf\{\|f\|_G:f\mapsto a\}.
$$

Because $I$ is closed, it is a norm. Different presentations give equivalent norms, not usually identical ones. Thus boundedness and convergence are intrinsic even when numerical norms depend on coordinates.

Contravariance is essential: a bounded homomorphism $A\to B$ induces $\operatorname{Sp}B\to\operatorname{Sp}A$. The image of a point $y$ is the inverse image of its maximal ideal. The induced embedding of residue fields respects their absolute values.

**Example.** The algebra $K\langle T,U\rangle/(TU-1)$ is not the whole multiplicative line. Since both $T$ and $U$ are bounded by one, the equation forces $|T|=1$. It is the unit circle. To describe an annulus $r\leq|T|\leq1$, use $K\langle T,U\rangle/(TU-a)$ with $|a|=r$.

### 3.2 Points and residue fields

For $x\in\operatorname{Sp}A$, let $\mathfrak m_x$ be its maximal ideal and $K(x)=A/\mathfrak m_x$. The analytic nullstellensatz makes $K(x)/K$ finite, so it has a unique absolute value extending that of $K$. Define

$$
|f(x)|=|f\bmod\mathfrak m_x|.
$$

This notation turns algebraic inequalities into subsets of $X$. It also hides a useful distinction. Two embeddings of the same finite field into an algebraic closure may give different geometric points but the same maximal point. The strict affinoid space records the closed point and its residue field, which is enough for coherent geometry.

If $L/K$ is a complete extension, the base change is

$$
A_L=A\widehat\otimes_K L,
$$

formed by completing the algebraic tensor product for compatible quotient norms. A point over $L$ maps to a point over $K$, but a point over $K$ can split after base change. Geometric connectedness and geometric reducedness must therefore be tested after extensions, not inferred from the visible $K$-points.

### 3.3 Spectral size and power-bounded elements

The intrinsic size of $f\in A$ is the **spectral seminorm**

$$
\rho_A(f)=\sup_{x\in\operatorname{Sp}A}|f(x)|.
$$

It also satisfies the spectral-radius formula

$$
\rho_A(f)=\lim_{m\to\infty}\|f^m\|_q^{1/m}.
$$

The limit is independent of the chosen affinoid presentation. Its kernel is the nilradical. Hence it is a norm exactly when $A$ is reduced, and on a reduced affinoid algebra it is equivalent to every quotient norm.

Define

$$
A^\circ=\{f:\{f^m:m\geq0\}\text{ is bounded}\},\qquad
A^{\circ\circ}=\{f:f^m\to0\}.
$$

Then

$$
A^\circ=\{f:\rho_A(f)\leq1\},\qquad
A^{\circ\circ}=\{f:\rho_A(f)<1\}.
$$

The quotient $\widetilde A=A^\circ/A^{\circ\circ}$ is the canonical reduction of $A$. If the value group is discrete and $A$ is reduced, $A^\circ$ is a topologically finite-type $R$-algebra. Without discreteness it need not be noetherian; this is one reason the formal-model chapters impose discrete valuation.

### 3.4 Products, nilpotents, and dimension

Products of algebras correspond to disjoint unions:

$$
\operatorname{Sp}(A_1\times A_2)=\operatorname{Sp}A_1\sqcup\operatorname{Sp}A_2.
$$

Nilpotents do not alter points but do alter coherent sheaves and infinitesimal intersections. Passing silently from $A$ to $A_{\mathrm{red}}$ therefore loses information. The function $\varepsilon$ on $K\langle T,\varepsilon\rangle/(\varepsilon^2)$ vanishes at every point but defines a nonzero endomorphism of the structure sheaf.

The dimension of $\operatorname{Sp}A$ is the Krull dimension of $A$. The Tate algebra in $n$ variables has dimension $n$; finite integral extensions preserve dimension; rational localization does not increase it. For a reduced pure one-dimensional affinoid algebra, maximal ideals are the closed points and minimal primes are the irreducible components. Local rings at smooth points are discrete valuation rings, but local rings at maximal points of a singular curve need not be normal.

## 4. Rational localization

### 4.1 Inequalities as coordinate rings

Analytic geometry needs to cut out regions where one function is no larger than another. Let $A$ be affinoid, and let $f_0,f_1,\ldots,f_m\in A$ generate the unit ideal. The associated **rational domain** is

$$
U=\left\{x\in\operatorname{Sp}A:
|f_i(x)|\leq|f_0(x)|\text{ for }1\leq i\leq m\right\}.
$$

The unit-ideal condition prevents $f_0$ and all numerators from vanishing simultaneously. Its coordinate algebra is

# $$A\left\langle\frac{f_1}{f_0},\ldots,\frac{f_m}{f_0}\right\rangle

A\langle S_1,\ldots,S_m\rangle/
(f_0S_1-f_1,\ldots,f_0S_m-f_m).
$$

The notation is suggestive but the displayed quotient is the definition. In that quotient
$f_0$ does become invertible: if $\sum a_if_i=1$, the relations give

$$
f_0\left(a_0+\sum_{i=1}^ma_iS_i\right)=1.
$$

At a point of the quotient, $S_i$ has size at most one, so the required inequalities hold.
Conversely, those ratios exist in the residue field of every point of $U$, giving a unique
lifted point.

### 4.2 The universal property

The coordinate algebra of $U$ is characterized without reference to points.

**Proposition 4.1.** Let $B$ be a $K$-affinoid algebra and $\varphi:A\to B$ a bounded homomorphism. It factors uniquely through the rational localization above if and only if there are elements $b_i\in B^\circ$ satisfying

$$
\varphi(f_0)b_i=\varphi(f_i).
$$

Equivalently, the induced map $\operatorname{Sp}B\to\operatorname{Sp}A$ has image in $U$.

**Proof.** A factorization must send $S_i$ to a power-bounded solution $b_i$, giving necessity. Conversely, the universal property of the Tate algebra sends $S_i$ to $b_i$; the displayed equations kill the defining ideal. Choose $a_i\in A$ with $\sum_{i=0}^m a_if_i=1$. Then

$$
\varphi(f_0)\left(\varphi(a_0)+\sum_{i=1}^m\varphi(a_i)b_i\right)=1,
$$

so $\varphi(f_0)$ is a unit. It follows both that each $b_i$ is forced to equal $\varphi(f_i)/\varphi(f_0)$ and that the factorization is unique. $\square$

For the pointwise equivalence, if the image lies in $U$, then $\varphi(f_0)$ vanishes at no
maximal point of $B$ and is therefore a unit. The ratios
$b_i=\varphi(f_i)/\varphi(f_0)$ have spectral seminorm at most one, so they are power
bounded by Section 3.3. The converse follows by evaluating the displayed equations at every
point.

This property proves that the algebra depends only on the subset $U$, not on the chosen rational presentation, up to unique bounded isomorphism. It also makes rational localization compatible with base change.

### 4.3 Weierstrass and Laurent domains

Two elementary domains generate the useful examples. A **Weierstrass domain** has the form

$$
\{x:|f_i(x)|\leq1\},\qquad
A\langle f_1,\ldots,f_m\rangle
=A\langle S_1,\ldots,S_m\rangle/(S_i-f_i).
$$

This notation becomes nontrivial when the bound is $|a|$: adjoining $f_i/a$ cuts out $|f_i|\leq|a|$.

A **Laurent domain** imposes both upper and lower bounds:

$$
|f_i|\leq1,\qquad |g_j|\geq1.
$$

Its algebra adjoins the $f_i$ and inverses $g_j^{-1}$ as bounded coordinates. For example,

$$
\{r\leq|T|\leq1\}
=\operatorname{Sp}K\langle T,U\rangle/(TU-a),\qquad |a|=r.
$$

The two closed subdomains $|T|\leq|a|$ and $|T|\geq|a|$ cover the unit disc. They are not open in the ordinary topology at the circle $|T|=|a|$, but they form an admissible cover. This is the simplest evidence that the analytic topology must be more flexible than point-set openness.

### 4.4 Flatness and transitivity

**Theorem 4.2.** If $U\subset\operatorname{Sp}A$ is a rational domain with algebra $A_U$, then $A\to A_U$ is flat. Rational localization is transitive: if $V$ is rational in $U$, then $V$ is rational in $\operatorname{Sp}A$, and its algebra is the corresponding completed base change.

**Proof.** We first record the elementary strictness argument. If $M'\subset M$ are finite
$A$-modules, choose quotient norms from finite free presentations. Closedness of submodules,
together with the division estimates of Section 2.5, gives

$$
M'\langle S\rangle\cap(S-f)M\langle S\rangle
=(S-f)M'\langle S\rangle.
$$

The proof recursively compares coefficients of a putative relation, uses the noetherian
stabilization of the colon modules $(M':f^n)$ to bound the recursion uniformly, and then takes
the convergent limit. Replacing $S-f$ by $gS-a$ gives the same equality for a Laurent
relation. After quotienting, these intersection equalities say exactly that
$M'\otimes_AA_U\to M\otimes_AA_U$ is injective for a single Weierstrass or Laurent
inequality. The ideal criterion for flatness therefore makes both elementary localization
maps flat.

For the rational domain defined by $f_0,\ldots,f_m$, choose
$1=\sum a_if_i$. On the domain one has

$$
1\leq\max_i\|a_i\|\,|f_0|.
$$

Choose $0\ne c\in K$ with $|c|\max_i\|a_i\|\leq1$. First pass to the Laurent domain
$|f_0|\geq|c|$ and then impose the Weierstrass inequalities
$|f_i/f_0|\leq1$. The universal property identifies the composite algebra with $A_U$.
Flatness is preserved by composition. If a second rational localization is made inside $U$,
substitution clears the finitely many displayed denominators; the universal property then
gives one rational presentation in $A$ and identifies its algebra with the completed base
change. This proves transitivity. $\square$

The map need not be faithfully flat: a nonempty rational domain can miss an entire component. Faithfulness is recovered from a finite rational cover $X=\bigcup U_i$; then

$$
A\longrightarrow\prod_i A_{U_i}
$$

is faithfully flat. This local-to-global detection is one algebraic source of sheaf theory.

### 4.5 Why ordinary localization is insufficient

Ordinary localization $A[1/f]$ remembers only the condition $f\ne0$. It contains no bound on $f^{-1}$ and is generally incomplete. The analytic domains

$$
\{|f|\geq|a|\},\qquad 0<|a|<1,
$$

all lie inside $f\ne0$ but have different rings of bounded functions. Their coordinate rings are completions of $A[a/f]$, not merely $A[1/f]$.

The punctured closed disc makes the failure visible. It is the union of annuli $|a|\leq|T|\leq1$ as $|a|$ tends to zero. Its analytic functions may have Laurent expansions whose negative coefficients satisfy radius-dependent convergence conditions. No single algebraic localization of $K\langle T\rangle$ captures all of them. Geometry must retain both invertibility and quantitative size.

## 5. Admissible opens and gluing

### 5.1 The topology is a Grothendieck topology

Rational domains are the coordinate patches, but unions and gluing require a notion of admissibility. An **affinoid subdomain** $U\subset X=\operatorname{Sp}A$ is a subset represented by an affinoid algebra $A_U$ with the universal property that maps from affinoid spaces into $X$ whose point images lie in $U$ factor uniquely through $U$. Rational domains are affinoid subdomains. A fundamental refinement theorem says that every affinoid subdomain admits a finite cover by rational domains of $X$.

An admissible open in an affinoid $X$ is a subset $V$ that has a covering by affinoid subdomains such that every map from an affinoid $Y$ to $X$ with image in $V$ pulls that covering back to one admitting a finite affinoid refinement. A family $(V_i)$ covers $V$ **admissibly** if the same finiteness condition holds after every affinoid test map. This definition is designed so that quasi-compact analytic pieces see only finitely many coordinates at a time.

The admissible opens and admissible coverings satisfy the axioms of a Grothendieck topology: isomorphisms cover, coverings survive base change, and composites of coverings cover. There need be no useful topology on the underlying set having precisely these covers. Sheaves will be defined directly for this covering theory.

The finiteness condition is genuine. If the residue field is algebraically closed and infinite, the closed unit disc is the set-theoretic union of its residue tubes

$$
\{x:|T(x)-a|<1\},\qquad \widetilde a\in\widetilde K.
$$

Each tube is an admissible open, but the family has no finite subcover and is not an admissible cover of the affinoid disc. Were it admissible, a function could be prescribed independently on every residue class, contradicting analytic convergence.

### 5.2 Tate acyclicity

The definition of admissibility earns its keep through one exact sequence. Let $X=\operatorname{Sp}A$ and let $X=U_1\cup\cdots\cup U_r$ be a finite rational cover. Write $A_{i_0\cdots i_p}$ for the affinoid algebra of the intersection. Then the augmented Čech complex

$$
0\longrightarrow A
\longrightarrow\prod_i A_i
\longrightarrow\prod_{i<j}A_{ij}
\longrightarrow\cdots
$$

is exact.

**Proof strategy.** A rational cover can be refined into elementary two-piece covers associated with an inequality $|f|\leq|g|$ and its reverse. For such a cover, convergent division gives the equalizer assertion and a bounded contracting homotopy on the augmented Čech complex. Repeating this construction proves exactness for Laurent covers. A finite rational cover has a Laurent refinement; the double Čech complex for the cover and its refinement transfers the contraction, and hence exactness, to the original cover.

The decisive analytic detail is bounded division. Algebraic equality on overlaps alone would not control whether the glued series converges. The norm estimates in division give a global element of $A$, not merely an element of a completion chosen after the fact.

**Theorem 5.1 (Tate acyclicity).** The preceding Čech complex is exact for every finite admissible covering of an affinoid space by affinoid subdomains. The same is true after tensoring with any finite $A$-module.

The bounded division operators act coefficientwise on a finite module. Choosing a finite
presentation and using flatness shows that the resulting homotopy is independent of the
chosen lifts, proving the module statement. This stronger argument is needed: tensoring an
arbitrary exact complex with a module would not by itself preserve exactness. The theorem will
turn finite modules into coherent sheaves and make higher cohomology vanish on affinoids.

### 5.3 The structure sheaf

For an affinoid subdomain $U\subset X$, define

$$
\mathcal O_X(U)=A_U.
$$

For a general admissible open, define sections by compatible sections on an admissible affinoid cover. Tate acyclicity proves independence of the cover and the sheaf equalizer condition. The resulting locally ringed object $(X,\mathcal O_X)$ is an affinoid rigid space.

Stalks are less useful here than in ordinary scheme theory because an analytic point has many nested inequality neighborhoods and the admissible topology is not determined by points. Nevertheless the local ring $\mathcal O_{X,x}$ is the filtered colimit over affinoid neighborhoods of $x$, is local, and has residue field containing $K(x)$. Properties such as smoothness are best checked on affinoid neighborhoods through differentials or completed residue fields rather than solely through point-set topology.

The identity theorem is an immediate consequence of reducedness and the spectral norm. If $X$ is reduced and $f\in\mathcal O_X(X)$ vanishes on an admissible open meeting every irreducible component in a nonempty domain, then $f=0$. The condition on components is necessary: a function may vanish identically on one component and not on another.

### 5.4 Gluing affinoid spaces

Suppose affinoid spaces $X_i$ have admissible opens $U_{ij}\subset X_i$ and isomorphisms

$$
\varphi_{ij}:U_{ij}\xrightarrow{\sim}U_{ji}
$$

which are identities for $i=j$, inverse in pairs, and satisfy the cocycle condition on triple overlaps. If the overlaps and their inverse images are admissible and the resulting diagonal is quasi-compact, the $X_i$ glue to a rigid space $X$.

The construction glues the underlying point sets and the sheaves simultaneously. The cocycle condition makes the equivalence relation transitive; admissibility ensures that sections descend; quasi-compactness of overlaps gives quasi-separatedness. Morphisms out of $X$ are exactly compatible morphisms out of the $X_i$.

Projective space is obtained by gluing $n+1$ unit polydiscs along Laurent domains. In dimension one, two discs with coordinates $T$ and $S$ glue by $S=T^{-1}$ along $|T|=1$. The result is the analytic projective line. The overlap is an affinoid unit circle even though it is not an ordinary open annulus. This example shows why affinoid domains, not only point-set opens, are legitimate gluing pieces.

### 5.5 Separatedness and intersections

A rigid space $X$ is **separated** when its diagonal $X\to X\times_KX$ is a closed immersion. It is **quasi-separated** when the diagonal is quasi-compact. If $X$ is separated and $U,V\subset X$ are affinoid subdomains, then $U\cap V$ is affinoid. If $X$ is only quasi-separated, the intersection is a finite union of affinoids.

These statements are analytic analogues of the affine-intersection criterion for schemes, but separatedness is stronger than Hausdorffness of the point set. Doubling the origin in an analytic line produces a nonseparated rigid space exactly as in algebraic geometry: two copies of the line are glued away from the origin. Analytic functions still glue, yet the two origins cannot be separated by the diagonal.

Quasi-separatedness is the correct standing hypothesis for coherent descent. Without it, an intersection may require infinitely many affinoids, products may fail to preserve finite presentation, and cohomology need not be controlled by finite Čech complexes.

## 6. Coherent sheaves

### 6.1 Finite modules are the local objects

Geometry needs more than functions. Vector bundles, ideals, differentials, and direct images must also glue. On an affinoid space $X=\operatorname{Sp}A$, a finite $A$-module $M$ defines a sheaf by

$$
\widetilde M(U)=M\otimes_AA_U
$$

for affinoid subdomains $U$. No completion symbol is necessary: a finite module over a noetherian affinoid algebra is already complete, and ordinary tensor product with $A_U$ carries the required complete topology.

A sheaf $\mathcal F$ on a rigid space is **coherent** if every point has an affinoid neighborhood $\operatorname{Sp}A$ on which $\mathcal F\simeq\widetilde M$ for a finite $A$-module $M$. It is locally free of rank $r$ when $M$ can locally be chosen free of rank $r$. Coherent ideal sheaves define closed analytic subspaces.

Finite generation is essential. For an infinite module, tensor product need not commute with the products occurring in Čech descent, and the natural topology may not be complete. Coherence is the finiteness condition that makes analytic and algebraic localization agree.

### 6.2 Acyclicity and exactness

**Theorem 6.1 (affinoid coherence).** If $X=\operatorname{Sp}A$, the functors

$$
M\longmapsto\widetilde M,\qquad
\mathcal F\longmapsto\Gamma(X,\mathcal F)
$$

are quasi-inverse equivalences between finite $A$-modules and coherent sheaves on $X$. Moreover

$$
H^q(X,\mathcal F)=0\qquad(q>0).
$$

**Proof strategy.** Module acyclicity gives exact descent on every finite rational cover. A locally finite presentation of $\mathcal F$ descends to a finite module because relations agree on overlaps. The same Čech resolution computes cohomology and is exact in positive degrees. The global-section functor is consequently exact on coherent sheaves over an affinoid.

The theorem is the analytic affine dictionary. It does not say every sheaf has vanishing higher cohomology, nor does it apply to arbitrary non-affinoid opens. The analytic projective line has nonzero first cohomology for sufficiently negative line bundles, just as its algebraic counterpart does.

### 6.3 Gluing and pullback

On a quasi-separated rigid space, coherent sheaves glue effectively across finite admissible affinoid covers. Concretely, finite modules $M_i$ on $U_i$ together with isomorphisms

$$
M_i\otimes A_{ij}\simeq M_j\otimes A_{ij}
$$

satisfying the cocycle condition determine a unique coherent sheaf. Kernels, cokernels, tensor products, and finite internal homomorphisms remain coherent because they can be computed over noetherian affinoid algebras.

For a morphism $f:X\to Y$, pullback is

$$
f^*\mathcal F=\mathcal O_X\otimes_{f^{-1}\mathcal O_Y}f^{-1}\mathcal F.
$$

On affinoids induced by $A\to B$, it corresponds to $M\mapsto M\otimes_AB$. Flatness of $f$ means exactness of this operation and can be tested affinoid-locally. A rational-domain immersion is flat, but a closed immersion is flat only in exceptional cases.

Vector bundles correspond to finite projective modules on affinoids. An invertible sheaf may be trivial on every member of a cover yet globally nontrivial; transition units carry the missing information. Local triviality without a chosen cocycle is not descent data.

### 6.4 Proper direct images

Affinoid acyclicity gives local control; properness gives global finiteness.

**Theorem 6.2 (proper mapping theorem).** Let $f:X\to Y$ be a proper morphism of rigid spaces, with $Y$ quasi-separated. For every coherent $\mathcal F$ on $X$, each $R^qf_*\mathcal F$ is coherent. If every fiber of $f$ has dimension at most $d$, then $R^qf_*\mathcal F=0$ for $q>d$.

**Proof strategy.** Work over an affinoid in $Y$. Properness supplies a finite affinoid cover of
$X$ together with relatively compact rational subdomains; after refining, every multiple
intersection is a finite union of affinoids and each boundary piece is described by finitely
many Laurent inequalities. Tate acyclicity replaces $\mathcal F$ by a finite Čech complex.
On a Laurent boundary piece, expansion splits a section into an interior part and parts whose
coefficients tend uniformly to zero toward the boundary. The latter form finite modules
modulo arbitrarily small powers of a topologically nilpotent scalar. The noetherian and
completeness results of Chapter 2 then show that the kernels and cokernels of the Čech
differentials are finite over the base affinoid algebra. Repeating the construction after
rational localization on the base identifies these finite modules with the sheaves
$R^qf_*\mathcal F$, proving coherence.

For the cohomological bound, use induction on the dimension of the support in the fibers.
The zero-dimensional case is finite over the base and hence affinoid. In positive dimension,
analytic Noether normalization supplies a parameter finite on a dense part of each support;
the exact sequences for multiplication by that parameter reduce the kernel and cokernel to
smaller-dimensional supports. The long exact cohomology sequence then gives vanishing above
the relative support dimension, hence above $d$.

Properness is decisive: the open unit disc has an enormous ring of global analytic functions,
not a finite module over $K$.

If $Y=\operatorname{Sp}K$ and $X$ is proper, every $H^q(X,\mathcal F)$ is a finite-dimensional $K$-vector space. For a proper curve only degrees $0$ and $1$ occur. These finiteness statements make possible a genuine comparison with projective algebraic curves.

## 7. Admissible formal schemes and generic fibers

### 7.1 Integral coordinates before inversion

From now on $K$ is complete discretely valued, $R=K^\circ$, and $\pi$ is a uniformizer. The restricted power-series algebra

$$
R\langle T_1,\ldots,T_n\rangle
=\left\{\sum a_\nu T^\nu:a_\nu\to0\text{ in the }\pi\text{-adic topology}\right\}
$$

is the $\pi$-adic completion of $R[T_1,\ldots,T_n]$. After inverting $\pi$ it becomes $K\langle T_1,\ldots,T_n\rangle$.

An **admissible $R$-algebra** is a $\pi$-adically complete, topologically finite-type $R$-algebra with no $\pi$-torsion. Equivalently it is a quotient of some $R\langle T\rangle$ by a closed ideal and is flat over $R$. An **admissible formal $R$-scheme** is locally $\operatorname{Spf}A$ for such algebras.

Flatness cannot be omitted if the formal scheme is meant to model its generic fiber faithfully. The algebra $R\langle T\rangle/(\pi T)$ becomes $K$ after inverting $\pi$, so the nonzero class of $T$ disappears. Removing $\pi$-torsion gives the same generic fiber with cleaner integral geometry.

### 7.2 The affine generic fiber

For $\mathfrak X=\operatorname{Spf}A$, define

$$
\mathfrak X_\eta=\operatorname{Sp}(A_K),\qquad A_K=A\otimes_RK=A[1/\pi].
$$

If $A=R\langle T\rangle/J$, then $A_K=K\langle T\rangle/(J)$, so this is affinoid. The points of $\mathfrak X_\eta$ are precisely the bounded solutions of the integral equations defining $\mathfrak X$.

**Examples.** The generic fiber of $\operatorname{Spf}R\langle T\rangle$ is the closed unit disc. The generic fiber of

$$
\operatorname{Spf}R\langle X,Y\rangle/(XY-\pi^e)
$$

is the closed annulus $|\pi|^e\leq|X|\leq1$, because $|X|,|Y|\leq1$ and $|X||Y|=|\pi|^e$. The formal equation already encodes both boundary radii.

The algebra $A$ is a ring of definition inside $A_K$, but it need not equal $(A_K)^\circ$ unless the model is appropriately normalized. Enlarging the integral ring can change the special fiber without changing the analytic algebra. Admissible blowups organize precisely this nonuniqueness.

### 7.3 Formal opens become analytic domains

A formal principal open is formed by completed localization. If $f\in A$, then

$$
\mathfrak D(f)=\operatorname{Spf}\bigl(A\langle S\rangle/(fS-1)\bigr)
$$

when the reduction of $f$ is inverted. Its generic fiber is the rational domain $|f|\geq1$ inside $\operatorname{Sp}A_K$. Since $f\in A$ already satisfies $|f|\leq1$, this is the locus $|f|=1$.

More generally, the affine chart of the formal blowup of an open ideal
$(f_0,\ldots,f_m)$ on which $f_0$ generates the transformed ideal becomes the rational
domain $|f_i|\leq|f_0|$ for all $i$. Thus the odd-looking analytic inequalities are the
generic shadows of ordinary affine charts on a formal blowup.

Not every analytic admissible open comes from an open formal subscheme of a fixed model. It may become formal only after an admissible blowup. Model changes are therefore part of localization, not a nuisance to be eliminated.

### 7.4 Gluing the generic fiber

Let $\mathfrak X$ be an admissible formal scheme with a finite affine cover $\mathfrak U_i$. The intersections have affine formal covers whose generic fibers are rational domains in $(\mathfrak U_i)_\eta$. Glue the affinoids $(\mathfrak U_i)_\eta$ along these domains. The result is a quasi-compact, quasi-separated rigid space $\mathfrak X_\eta$, independent of the chosen affine cover.

Separatedness and properness pass in the expected direction:

$$
\mathfrak X\text{ separated}\Longrightarrow\mathfrak X_\eta\text{ separated},
$$

$$
\mathfrak X\text{ proper over }\operatorname{Spf}R
\Longrightarrow\mathfrak X_\eta\text{ proper over }K.
$$

The converses require a change of model. A proper rigid space may begin with a nonproper formal model; after admissible modification it admits a proper one in the curve cases considered later.

### 7.5 Morphisms and base change

A continuous $R$-homomorphism $A\to B$ induces $A_K\to B_K$ and hence a morphism of generic fibers. Gluing makes $\mathfrak X\mapsto\mathfrak X_\eta$ functorial. Closed formal immersions become closed analytic immersions after removing any $\pi$-torsion. Fiber products commute with generic fibers:

$$
(\mathfrak X\times_{\mathfrak S}\mathfrak Y)_\eta
\simeq
\mathfrak X_\eta\times_{\mathfrak S_\eta}\mathfrak Y_\eta.
$$

If $R'/R$ is the valuation ring extension attached to a finite extension $K'/K$, then formal base change followed by removal of $\pi'$-torsion has generic fiber $\mathfrak X_\eta\widehat\otimes_KK'$. Normality or reducedness of the special fiber need not survive ramified base change, so normalization after base change is often necessary. The analytic base change itself remains well defined.

## 8. Specialization and reduction

### 8.1 The center of an analytic point

An analytic point of a formal generic fiber has integral values on every formal function. Let $\mathfrak X=\operatorname{Spf}A$ and $x\in\mathfrak X_\eta$. Evaluation gives

$$
A\longrightarrow K(x)^\circ\longrightarrow\widetilde{K(x)}.
$$

Its kernel modulo $\pi$ is a prime ideal of $A/\pi A$. This defines the **specialization map**

$$
\operatorname{sp}:\mathfrak X_\eta\longrightarrow\mathfrak X_s.
$$

Equivalently,

$$
\operatorname{sp}(x)=\{\widetilde f\in A/\pi A:|f(x)|<1\}.
$$

The center records which integral functions become infinitesimal at $x$. It forgets their exact absolute values, so many analytic points specialize to the same algebraic point.

For admissible formal schemes topologically of finite type, every closed point of the special fiber has a preimage after allowing the finite residue extensions already built into analytic points. One lifts a finite set of residue coordinates and applies the analytic nullstellensatz to the resulting nonzero affinoid algebra. Surjectivity onto nonclosed scheme points is not asserted at the level of maximal analytic points.

### 8.2 Fibers of specialization

If $Z\subset\mathfrak X_s$ is locally closed, its **tube** is

$$
]Z[_\mathfrak X=\operatorname{sp}^{-1}(Z).
$$

For a closed subscheme cut out locally by $\widetilde f_1,\ldots,\widetilde f_r$, the tube of its underlying closed set is

$$
\{x:|f_i(x)|<1\text{ for every }i\}.
$$

The tube depends only on the reduced locally closed subset, not on its nilpotent thickening. Formal completions retain thickenings; specialization fibers do not.

If $U=\mathfrak X_s\setminus Z$, then $]U[$ is described by requiring at least one $|f_i(x)|=1$. It is a finite union of rational domains. The tube $]Z[$ is usually not affinoid because strict inequalities are increasing unions of closed rational inequalities.

### 8.3 Reduction of an affinoid algebra

For any affinoid algebra $B$, canonical reduction is

$$
\widetilde B=B^\circ/B^{\circ\circ}.
$$

There is a reduction map

$$
\operatorname{red}:\operatorname{Sp}B\longrightarrow\operatorname{Spec}\widetilde B,
\qquad
x\longmapsto\{\widetilde f:|f(x)|<1\}.
$$

If $B=A_K$ and $A=B^\circ$ is an admissible ring of definition, this is the specialization map for $\operatorname{Spf}A$. For a smaller ring of definition $A\subset B^\circ$, the ring map

$$
A/\pi A\longrightarrow\widetilde B
$$

induces a morphism $\operatorname{Spec}\widetilde B\to\operatorname{Spec}(A/\pi A)$, and
specialization factors as canonical reduction followed by this morphism. The direction is
contravariant: the formal special fiber does not map canonically to the canonical reduction.

**Example.** For $B=K\langle T\rangle$, one has $B^\circ=R\langle T\rangle$ and $\widetilde B=\widetilde K[T]$. The inverse image of the closed point $(T-\widetilde a)$ is the open residue disc $|T-a|<1$. The generic point of the affine line is not the image of a maximal rigid point, which again explains the target distinction.

### 8.4 Anticontinuity and functoriality

Specialization reverses the feel of topology. The inverse image of a Zariski closed subset is defined by strict inequalities and is analytically open; the inverse image of a principal Zariski open is defined by an equality $|f|=1$ and is a rational domain. This property is often called **anticontinuity**.

For a morphism $\mathfrak f:\mathfrak X\to\mathfrak Y$, reduction and generic fiber form a commutative square:

$$
\begin{array}{ccc}
\mathfrak X_\eta&\xrightarrow{\mathfrak f_\eta}&\mathfrak Y_\eta\\
\downarrow\operatorname{sp}&&\downarrow\operatorname{sp}\\
\mathfrak X_s&\xrightarrow{\mathfrak f_s}&\mathfrak Y_s.
\end{array}
$$

This follows directly by contracting kernels of residue maps. It makes tubes functorial:

$$
\mathfrak f_\eta^{-1}(]Z[_\mathfrak Y)
=]\mathfrak f_s^{-1}(Z)[_\mathfrak X.
$$

## 9. Admissible blowups and invariance

### 9.1 Blowing up only the special fiber

Formal models are not unique. The controlled changes are blowups along ideals that become the unit ideal after inverting $\pi$.

An ideal $\mathcal I\subset\mathcal O_\mathfrak X$ is **open** if locally it contains a power of $\pi$. The formal blowup of $\mathfrak X$ along $\mathcal I$ is the $\pi$-adic completion of the ordinary blowup, with $\pi$-torsion removed to remain admissible. It is denoted

$$
\operatorname{Bl}_{\mathcal I}(\mathfrak X)\longrightarrow\mathfrak X.
$$

Because $\mathcal I[1/\pi]=\mathcal O_{\mathfrak X}[1/\pi]$, the center is invisible on the generic fiber. This is the exact sense in which the blowup modifies only integral reduction data.

Blowing up a nonopen horizontal ideal is different: it can change the generic analytic space. Openness is therefore a mathematical hypothesis, not terminology.

### 9.2 Affine charts

Let $\mathfrak X=\operatorname{Spf}A$ and let $I=(f_0,\ldots,f_m)$ contain $\pi^N$. The chart on which $f_i$ generates the transformed ideal has algebra

$$
A_i=
\left(A\left\langle\frac{f_0}{f_i},\ldots,\frac{f_m}{f_i}\right\rangle\right)
\big/\{\pi\text{-torsion}\}.
$$

Its generic fiber is the rational domain

$$
U_i=\{x:|f_j(x)|\leq|f_i(x)|\text{ for all }j\}.
$$

Since one of the $f_j$ is a power of $\pi$, the functions cannot all vanish at an analytic point. The $U_i$ form a finite rational cover of $\mathfrak X_\eta$. Thus a rational covering is literally the generic shadow of blowup charts.

As a concrete case, blow up $(\pi,T)$ in the formal unit disc. The chart where $\pi$ dominates gives $|T|\leq|\pi|$ with coordinate $T/\pi$; the chart where $T$ dominates gives $|T|\geq|\pi|$ with coordinate $\pi/T$. Their generic fibers cover the same disc but separate its small central disc from the surrounding annulus in the special fiber.

### 9.3 Invariance of the generic fiber

**Theorem 9.1 (blowup invariance).** If $\mathfrak X'\to\mathfrak X$ is an admissible formal blowup, then

$$
\mathfrak X'_\eta\xrightarrow{\sim}\mathfrak X_\eta.
$$

**Proof.** Work on an affine formal open and use the charts of the preceding section. Their generic fibers are rational domains $U_i$ covering $\mathfrak X_\eta$. On overlaps, the chart relations are exactly the transition relations among ratios $f_j/f_i$. Hence the generic fibers glue back to $\mathfrak X_\eta$. Removing $\pi$-torsion changes nothing after $\pi$ is inverted. $\square$

The isomorphism is canonical. The specialization maps are not preserved as maps to a fixed special fiber; instead they fit into

# $$\operatorname{sp}_{\mathfrak X}

(\mathfrak X'_s\to\mathfrak X_s)\circ\operatorname{sp}_{\mathfrak X'}.
$$

Thus the analytic space is fixed while its reduction is refined.

### 9.4 Common refinements and the model theorem

Blowup invariance has a converse strong enough to make formal models intrinsic.

**Theorem 9.2 (formal model theorem).** The generic-fiber functor induces an equivalence between:

- the category of quasi-compact quasi-separated admissible formal $R$-schemes localized by
  inverting all admissible formal blowup morphisms; and
- quasi-compact quasi-separated rigid $K$-spaces.

In particular, every such rigid space has an admissible formal model. Two formal models of the same rigid space are dominated by a third after admissible blowups, and every analytic morphism extends to a morphism after admissibly blowing up the source.

**Proof strategy.** For essential surjectivity, choose a finite affinoid cover and, in each
affinoid algebra, the $R$-subalgebra generated by finitely many bounded coordinates. Remove
$\pi$-torsion and complete; this gives an admissible affine model. On an overlap, rational
localization expresses every coordinate as one of finitely many bounded fractions. Clearing
their denominators by a power of $\pi$ produces an open ideal. The charts of its admissible
blowup are exactly the rational domains on which those fractions become formal functions.
Blowing up all finitely many overlap ideals and then their pullbacks on triple overlaps makes
the transition maps formal and makes the cocycle identities literal. The affine models then
glue.

For fullness, apply the same denominator-clearing process to the coordinate functions of a
morphism on a finite affinoid cover of its source. One admissible blowup of the source makes
all of them formal. For faithfulness, two formal maps inducing the same analytic map agree
after inverting $\pi$; their finitely many differences are killed by powers of $\pi$, and an
admissible blowup followed by removal of $\pi$-torsion kills those differences. Thus the maps
become equal in the localized formal category. Finally, applying fullness to an analytic
isomorphism and its inverse and taking a common blowup makes both composites identities.
This proves the equivalence and the common-refinement assertion.

The theorem does not identify a preferred model. Statements about special-fiber components, intersections, or reduction points are model-dependent. Statements invariant under admissible blowup belong to the analytic space.

## 10. Tubes

### 10.1 Analytic neighborhoods cut out by reduction

Tubes translate a stratum of the special fiber into its analytic neighborhood. If $Z\subset\mathfrak X_s$ is closed and locally defined by $\widetilde f_1,\ldots,\widetilde f_r$, then

$$
]Z[_\mathfrak X=\{x:|f_i(x)|<1\text{ for all }i\}.
$$

This is an admissible open, expressed as the increasing union of affinoids

$$
\{x:|f_i(x)|^{N}\leq|\pi|\text{ for all }i\},\qquad N=1,2,\ldots.
$$

The union need not stabilize and hence need not be affinoid. A tube is best thought of as an analytic germ around a reduction stratum, not a closed algebraic neighborhood.

If $Z_1$ and $Z_2$ are disjoint locally closed strata, their tubes are disjoint. If $Z=Z_1\cup Z_2$, then $]Z[=]Z_1[\cup]Z_2[$. Intersections behave similarly. These equalities concern underlying reduced strata; embedded nilpotents are invisible.

### 10.2 Discs above smooth points

Let $\mathfrak C$ be a smooth formal curve over $R$, and let $z$ be a closed point of its
special fiber with residue field $k(z)$. Smoothness makes $k(z)/\widetilde K$ separable. Choose
a finite unramified extension $K'/K$, with valuation ring $R'$, whose residue field contains $k(z)$, and choose a
$k(z)$-embedding that gives a rational point $z'$ of the base-changed special fiber above
$z$. After choosing an étale coordinate carrying the lifted section through $z'$ to $T=0$,
the completed neighborhood of that section is the one-variable formal disc. Hensel lifting on
the étale coordinate therefore gives

$$
]z'[_{\mathfrak C_{R'}}
\simeq\{x:|T(x)|<1\},
$$

the open unit disc.

Formal smoothness lifts the residue point and its parameter through every power of $\pi$.
Completeness turns the compatible lifts into a formal coordinate, while étaleness and Hensel's
lemma identify the whole tube, not merely its completed local ring, with the open disc. The
strict inequality expresses specialization to $T=0$.

This is a statement about a chosen component after residue-field extension. The full base
change of $]z[$ can be a disjoint union of such discs, indexed by the points above $z$; it
should not be identified with one disc without choosing $z'$. Over $K$ itself the tube is the
corresponding descended residue disc with constant residue field $k(z)$. Smooth reduction
decomposes a proper curve into residue discs attached to the closed points of its special
fiber, but the family of all such discs is generally not an admissible cover when the residue
field is infinite.

### 10.3 Annuli above nodes

The standard semistable node has completed local equation

$$
XY=\pi^e
$$

with $e\geq1$. Its entire affine generic fiber is the closed annulus $|\pi|^e\leq|X|\leq1$. The node itself is cut out in the special fiber by $X=Y=0$, so its tube requires

$$
|X|<1,\qquad |Y|<1.
$$

Using $|X||Y|=|\pi|^e$, this becomes the open annulus

$$
|\pi|^e<|X|<1.
$$

The two boundary circles specialize to the two branches rather than to the node. The exponent $e$ is the thickness of the node; after a ramified extension and suitable modification it may subdivide into several edges of smaller thickness.

An analytic function on a closed annulus has a Laurent expansion

$$
f=\sum_{n\in\mathbf Z}a_nT^n
$$

such that $|a_n|\to0$ as $n\to+\infty$ and $|a_{-n}|r^{-n}\to0$ as $n\to+\infty$, where $r$ is the inner radius. These two tail conditions encode convergence at both boundaries. On an open annulus they must hold on every smaller closed subannulus.

### 10.4 Strict neighborhoods and excision

Let $Z$ be closed in a special fiber and $U$ its complement. A **strict neighborhood** of $]Z[$ is an admissible open $V$ containing $]Z[$ such that $V$ together with $]U[$ covers the whole generic fiber admissibly. In coordinates, strict neighborhoods replace $|f_i|<1$ by slightly weaker bounded inequalities that still leave an overlap with the complementary tube.

Strict neighborhoods allow analytic data to be compared without choosing one exact boundary circle. If a formal blowup refines $Z$, the tube of its inverse image identifies with the original tube under generic-fiber invariance. Consequently constructions defined on a cofinal system of strict neighborhoods are independent of the chosen formal model.

A warning is useful. Removing a tube is not the same as deleting the corresponding algebraic subset from the generic fiber: $Z$ lies only in the special fiber. The complement $]U[$ consists of points whose reductions avoid $Z$, which is a bounded condition. This distinction underlies analytic excision around bad reduction.

## 11. Curves in rigid geometry

### 11.1 Dimension one and local parameters

A **rigid analytic curve** over $K$ is a separated rigid space, locally of finite type, all of whose irreducible components have dimension one. Reducedness, smoothness, and geometric connectedness are additional hypotheses, not part of the word _curve_. This convention permits singular and nonreduced fibers to appear without changing language.

On an affinoid curve $X=\operatorname{Sp}A$, a nonconstant analytic function $t$ often gives a finite map to a disc. Algebraically this means that $A$ is finite over $K\langle t\rangle$. Near a point $x$ where $dt$ does not vanish, $t-t(x)$ is a local parameter after a finite residue-field extension. The completed local ring is then

$$
\widehat{\mathcal O}_{X,x}\simeq K(x)[[t]]
$$

in the smooth case, where completion is with respect to the maximal ideal. The formal power series describe germs; their convergence radius need not be uniform on an entire affinoid neighborhood.

Zeros of an analytic function on an affinoid smooth curve are finite provided the function is
not identically zero on any connected component. Indeed, each connected component of a
smooth affinoid curve is normal and irreducible, so on it $f$ is a nonzerodivisor. Hence
$A/(f)$ has dimension zero and is an affinoid algebra, therefore an artinian $K$-algebra. If
$f$ vanishes on a whole component, that component is of course part of its zero locus. On a
non-affinoid curve isolated zeros can accumulate only toward the analytic boundary. A
function with infinitely many zeros on an open disc therefore does not contradict finiteness
on every closed subdisc on which it is nonzero.

### 11.2 Smooth, normal, and regular curves

A morphism $X\to\operatorname{Sp}K$ is smooth of relative dimension one if locally it admits an étale map to a disc. Equivalently, for every point $x$, the local ring is regular of dimension one and the residue extension is separable in the relevant differential criterion. Over a nonperfect field, regularity alone does not imply smoothness: purely inseparable residue phenomena must be excluded.

For a reduced analytic curve, normality is equivalent to all local rings being discrete valuation rings. Thus a normal curve is regular. Over a perfect base, a geometrically reduced normal curve is smooth; over an imperfect base one must retain geometric regularity as a separate condition.

The nodal annulus model shows another distinction. The formal total space $XY=\pi$ is regular, and its analytic generic fiber is smooth because $\pi\ne0$ there, although the special fiber is singular. Smoothness of the analytic curve does not demand smooth reduction.

Differentials detect ramification. If $f:X\to Y$ is a finite morphism of smooth curves and $t$ is a parameter at $f(x)$, then in the completed local DVR at $x$

$$
f^*t=u s^e
$$

with $u$ a unit and $s$ a parameter at $x$. There is no additional higher-order term: it is
absorbed into the unit. The map is étale at $x$ precisely when $e=1$ and the residue extension
is separable. In positive residue characteristic, $e$ prime to the characteristic is not by
itself enough unless the residue condition is also checked.

### 11.3 Finite maps and normalization

If $A\to B$ is a finite homomorphism of affinoid algebras, the induced map $\operatorname{Sp}B\to\operatorname{Sp}A$ is finite. Conversely, a finite morphism is affinoid over affinoids and arises from a finite algebra. Finite morphisms are proper, have finite fibers, and preserve affinoid domains under inverse image.

The finiteness needed for normalization is an analytic theorem, not a consequence of
noetherianity alone.

**Theorem 11.1 (finite analytic normalization).** If $A$ is a reduced $K$-affinoid algebra
of dimension one, its integral closure in its total ring of fractions is a finite $A$-module.

**Proof strategy.** Treat the irreducible components separately. Analytic Noether
normalization, proved by the same distinguished-coordinate induction as Theorem 2.1, gives a
finite injection

$$
K\langle T_1,\ldots,T_d\rangle\longrightarrow A
$$

when $A$ has dimension $d$. In dimension one the base $D=K\langle T\rangle$ is a regular
one-dimensional noetherian domain: Weierstrass division makes it a principal ideal domain,
and hence every localization at a nonzero maximal ideal is a DVR. The integral closure of
$D$ in a finite extension $F/K(T)$ is
finite. For the separable part, choose a full $D$-lattice and use the nondegenerate trace
pairing to place every integral element inside its finite trace-dual lattice, exactly as for a
Dedekind domain. For a purely inseparable part of exponent $q$, raise an integral element to
the $q$th power. It lies in the preceding normal ring. Choose the field basis from finitely
many purely inseparable generators, scaled to be integral away from a finite set of
height-one primes of $D$. Expansion in this basis and the Gauss valuation bound control the
coefficients at every remaining prime; at the finitely many exceptional DVRs, take the
maximum of the finitely many denominator bounds. Multiplication by the product of the
corresponding prime elements to those powers therefore puts the entire integral closure in
one finite lattice. Thus it lies between two finite lattices. Applying these two steps in the
separable--purely-inseparable tower proves the one-variable assertion.

The total fraction ring of $A$ is finite over that of $D$. Its integral closure is finite over
$D$ by the preceding paragraph and contains $A$; being a submodule of a finite $D$-module,
it is finite over the noetherian ring $D$, hence also finite as an $A$-module. The same argument
after rational localization shows compatibility on overlaps. This proves the theorem.

Let $X$ be a reduced affinoid curve. Its normalization is obtained by taking the integral closure $A^{\mathrm{nor}}$ of $A$ in its total ring of fractions. This algebra is finite over $A$, so

$$
X^{\mathrm{nor}}=\operatorname{Sp}A^{\mathrm{nor}}\longrightarrow X
$$

is finite. Gluing gives normalization for quasi-separated curves. It is an isomorphism over
the normal locus and separates analytic branches at singular points. The proof above supplies
the required finiteness directly; no unproved excellence assertion is being imported.

For the node $A=K\langle X,Y\rangle/(XY)$, the normalization is $K\langle X\rangle\times K\langle Y\rangle$ and separates the two branches. In contrast, the annulus algebra $K\langle X,Y\rangle/(XY-a)$ with $a\ne0$ is already smooth and normal. Equations that look identical before and after setting $a=0$ have different generic geometry.

### 11.4 Boundary and wide-open curves

An affinoid curve behaves like a compact curve with finitely many boundary directions. A **wide-open curve** is, in the situations needed here, a smooth rigid curve obtained from a smooth proper curve by removing finitely many disjoint closed discs. Equivalently, it admits an exhaustion whose complement consists of finitely many annular ends. The precise equivalence assumes the curve is quasi-smooth and has finitely many ends.

Open discs and open annuli are not affinoid. Each is an increasing union of closed affinoids, and analytic functions must converge on every member of the exhaustion. Boundary explains why their function rings are much larger than finite-type algebras.

The distinction between removing points and removing discs is characteristically nonarchimedean. Removing one algebraic point from a proper curve leaves a punctured neighborhood modeled on an annulus with inner radius tending to zero. Removing a closed residue disc leaves an actual annular boundary of positive modulus. Formal models see the latter as deleting a component or a tube, while algebraic open curves naturally produce the former.

## 12. Proper rigid curves

### 12.1 The valuative meaning of properness

Properness is the condition that eliminates analytic boundary. A separated rigid space $X$ is proper over $K$ if it is quasi-compact and universally closed in the analytic sense; equivalently in the finite-type setting, maps from punctured valuation discs extend uniquely across the missing center after every complete extension.

For curves, this criterion has a concrete interpretation. An affinoid or wide-open end supplies a bounded parameter tending toward a missing boundary point, so the associated punctured-disc map fails to extend inside the space. A quasi-compact smooth curve admitting a proper formal model has no boundary and satisfies the extension property; conversely, the absence of boundary together with quasi-compactness is the curve form of the valuative properness criterion.

Properness is stable under finite extension of $K$, composition, and closed immersion. A finite morphism is proper. The analytic affine line and every nonempty affinoid curve of positive dimension are not proper: a positive-dimensional space cannot be both affinoid and proper over $K$, because properness makes global functions algebraic over $K$, whereas a reduced affinoid curve has a transcendental function.

The last claim can be made exact. If $X$ is connected and proper, then $H^0(X,\mathcal O_X)$ is a finite field extension of $K$ when $X$ is reduced. If it is geometrically connected and geometrically reduced, the global functions are exactly $K$. Thus a nonconstant global analytic function on a proper geometrically connected smooth curve cannot exist.

### 12.2 Finite-dimensional cohomology

Let $X$ be a proper rigid curve and $\mathcal F$ coherent. The proper mapping theorem gives

$$
\dim_KH^0(X,\mathcal F)<\infty,\qquad
\dim_KH^1(X,\mathcal F)<\infty,\qquad
H^q(X,\mathcal F)=0\quad(q\geq2).
$$

The vanishing follows from the cohomological-dimension part of the proper mapping theorem;
finiteness uses properness. For the positive line bundles used in algebraization, the stronger
vanishing and global-generation statements are proved analytically below by successively
allowing poles at a finite divisor.

For a smooth proper geometrically connected curve, duality gives a perfect pairing

$$
H^0(X,\Omega_X^1)\times H^1(X,\mathcal O_X)
\longrightarrow K.
$$

Its common dimension is the genus. Exact base change holds for a complete extension $L/K$:

$$
H^q(X,\mathcal F)\otimes_KL
\xrightarrow{\sim}
H^q(X_L,\mathcal F_L).
$$

Choose a finite affinoid cover whose nonempty intersections are affinoid. Its finite-module
Čech complex has strict differentials, and its cohomology is finite-dimensional by the
proper mapping theorem. Completed scalar extension is therefore exact on this complex and
agrees with ordinary tensor product on its cohomology. The scalar-extended cover is the
corresponding cover of $X_L$, which proves the displayed isomorphism.

Properness and coherence are essential; global functions on an open disc do not arise by a finite-dimensional scalar extension.

The vanishing needed for algebraization must be obtained analytically, since algebraic
Riemann--Roch is not yet available. More generally, a reduced proper rigid curve has a
coherent dualizing sheaf $\omega_X$ and, for coherent $\mathcal F$, a perfect pairing

$$
H^1(X,\mathcal F)\times
\operatorname{Hom}_X(\mathcal F,\omega_X)\longrightarrow K.
$$

On a normal curve the pairing is constructed by choosing a finite affinoid cover, writing a
Čech $1$-class as principal parts on the boundary annuli, and summing the residues of their
products with differentials. Laurent expansion on an annulus makes the residue the
coefficient of $T^{-1}dT$; the two orientations on an overlap give opposite signs. Tate
acyclicity proves independence of the representative, while division with prescribed finite
principal parts proves nondegeneracy. For a reduced singular curve, apply this construction
to its finite normalization and impose the finite conductor matching conditions. The
annihilator of those conditions is the dualizing sheaf, and finite-dimensional linear duality
gives the displayed pairing.

Let $D$ be an effective Cartier divisor in the normal locus meeting every irreducible
component. Then

$$
H^1(X,\mathcal O_X(nD))=0\qquad(n\gg0).
$$

Indeed, duality identifies its dual with
$H^0(X,\omega_X(-nD))$. These spaces form a descending sequence inside the finite-dimensional
space $H^0(X,\omega_X)$, and their intersection is zero: a section vanishing to every order at
one regular point of each component is zero by the identity theorem. The sequence therefore
eventually vanishes. For finite subschemes of length at most two, the maps to principal parts
are controlled on a finite affinoid cover by finitely many Laurent coefficients; the same
descending-chain argument gives one bound independent of the chosen subscheme. After also
including the fixed conductor subscheme, a sufficiently large $nD$ therefore separates
closed points, tangent directions, and the finite conductor branches. This is the
nonarchimedean curve form of Serre vanishing, established without using algebraization.

### 12.3 Meromorphic functions and divisors

On a smooth connected rigid curve, the sheaf of meromorphic functions is the total quotient sheaf of $\mathcal O_X$. At each point $x$, the local ring is a DVR, so a nonzero meromorphic function has an order $\operatorname{ord}_x(f)\in\mathbf Z$. On a proper curve only finitely many orders are nonzero, and the principal divisor is

$$
\operatorname{div}(f)=\sum_x \operatorname{ord}_x(f)[x].
$$

The degree convention is $\deg[x]=[K(x):K]$, so

$$
\deg\operatorname{div}(f)
=\sum_x[K(x):K]\operatorname{ord}_x(f).
$$

The degree of a principal divisor is zero. One proof uses a finite map to the projective line induced by $f$ and compares the fibers over zero and infinity. Another uses residues of $df/f$. Properness is again decisive: on a disc, a coordinate has a zero without a compensating pole inside the disc; the missing pole lies beyond the boundary.

Cartier divisors correspond to invertible sheaves with meromorphic sections. For a divisor $D$, the space $H^0(X,\mathcal O_X(D))$ consists of meromorphic functions whose poles are bounded by $D$. Riemann--Roch takes its usual form

$$
h^0(D)-h^0(K_X-D)=\deg D+1-g.
$$

In this book it is used as a comparison consequence from the established theory of algebraic curves, once algebraization has been proved; it is not an independent foundation for that algebraization.

### 12.4 Projectivity and algebraization

The central rigidity theorem for curves is the following.

**Theorem 12.1 (algebraization of proper curves).** Let $X$ be a proper rigid analytic space over $K$, pure of dimension one. Assume $X$ is reduced. Then $X$ is the analytification of a unique proper algebraic curve $C/K$. If $X$ is smooth, normal, or geometrically connected, $C$ has the corresponding property. In the smooth case $C$ is projective.

**Proof.** The finite analytic normalization theorem gives
$\nu:X^{\mathrm{nor}}\to X$. Its components are normal proper curves; they are regular, though
over an imperfect field they need not be smooth. Choose an effective divisor $D$ in their
regular loci meeting every component. The analytic vanishing proved in Section 12.2 shows
that $\mathcal O(nD)$ is globally generated and separates points and tangent directions for
$n$ sufficiently large. Its finitely many sections therefore give a closed immersion

$$
X^{\mathrm{nor}}\hookrightarrow\mathbf P^N_K.
$$

For projective space, use the standard finite affinoid cover. Laurent division computes the
cohomology of every twist in the analytic and algebraic categories by the same homogeneous
terms. The same bounded Čech calculation shows that, after a sufficiently large twist, a
coherent analytic ideal is generated by finitely many global sections; applying it again to
the coherent kernel gives a finite presentation by twists. The identical homogeneous
presentation is algebraic, so every coherent analytic ideal on $\mathbf P^N_K$ is algebraic.
Applying this projective comparison to the ideal of the image produces a projective
algebraic normalization $C^{\mathrm{nor}}$ whose analytification is $X^{\mathrm{nor}}$.

It remains to restore the singularities. The conductor ideals in $X$ and
$X^{\mathrm{nor}}$ have finite support, and the two conductor quotients are finite analytic
$K$-spaces, hence spectra of finite $K$-algebras. The quotient maps and their algebra
structures are algebraic by the same projective comparison on graphs. Forming the finite
conductor pushout in affine neighborhoods and gluing produces a reduced proper algebraic
curve $C$ with $C^{\mathrm{an}}\simeq X$. This construction also shows that normality is
preserved. Smoothness and geometric connectedness may be checked after analytic scalar
extension and on completed local rings, so they too agree.

For uniqueness, embed two candidate curves projectively. The analytic graph of an
isomorphism is a coherent closed subspace of the analytification of their projective product;
the projective comparison just proved algebraizes it. Its two projections are isomorphisms
because this can be checked after analytification. Thus the algebraic curve is unique. Every
proper algebraic curve over a field is projective, so in particular the smooth curve obtained
above is projective. $\square$

This order of proof is important: analytic duality supplies the positive divisor before any
algebraic comparison is invoked, and only the directly computed projective-space comparison
is used to algebraize the resulting image. The later proper comparison theorem is therefore a
consequence, not an input.

Reducedness in the statement avoids a separate discussion of nilpotent conductor data. Proper nonreduced one-dimensional spaces are also algebraizable under the same finite-type hypotheses by algebraizing their coherent nilpotent ideals, but that strengthening is not needed below.

As a consequence, a smooth proper rigid curve is not a new kind of global curve. Its distinctively analytic information lies in its affinoid domains, formal models, reductions, and tubes.

## 13. Formal models of proper curves

### 13.1 Existence from algebraic models

Let $C/K$ be a smooth proper geometrically connected curve. Choose a proper flat $R$-model $\mathcal C$ with generic fiber $C$; normalization and resolution provide regular models under the excellence hypotheses already established for $R$. Complete $\mathcal C$ along its special fiber:

$$
\widehat{\mathcal C}=\varprojlim_n
\mathcal C\times_RR/\pi^{n+1}.
$$

Then

$$
(\widehat{\mathcal C})_\eta\simeq C^{\mathrm{an}}.
$$

**Proof strategy.** Cover $\mathcal C$ by affine opens and compare their completed coordinate rings after inverting $\pi$. These give the bounded analytic regions specializing to the chosen affine pieces of the special fiber. Properness says every analytic point of $C^{\mathrm{an}}$ extends uniquely to an integral point after passing to its valuation ring, so it specializes somewhere on $\mathcal C_s$. The local regions therefore cover the entire analytification. Their overlap maps agree by separatedness.

For a nonproper model, the same completion generally yields only a domain in $C^{\mathrm{an}}$. Properness is exactly what prevents points from escaping to infinity.

Conversely, every proper smooth rigid curve algebraizes by Theorem 12.1 and hence has a proper admissible formal model. Thus algebraic models and formal models are two integral presentations of the same analytic curve.

### 13.2 Extension of analytic data

An analytic morphism need not extend to fixed formal models: its coordinate functions may have denominators along the special fiber. The model theorem supplies the exact remedy.

**Proposition 13.1.** Let $f:X\to Y$ be a morphism of quasi-compact quasi-separated rigid spaces, and choose admissible formal models $\mathfrak X,\mathfrak Y$. There is an admissible blowup $\mathfrak X'\to\mathfrak X$ and a formal morphism $\mathfrak X'\to\mathfrak Y$ inducing $f$. If $f$ is an isomorphism, the two models admit a common admissible refinement.

For proper algebraic curves there is a sharper graph construction. Take the schematic closure of the generic graph in a product of proper models, then normalize or resolve it. The two projections give a model dominating the source and a morphism to the target. Analytically this is the same denominator-clearing process as admissible blowup.

Coherent sheaves behave similarly. Given a coherent sheaf $\mathcal F$ on $X$ and a formal model $\mathfrak X$, after an admissible blowup there is a coherent $R$-flat sheaf $\mathfrak F$ with $\mathfrak F_\eta\simeq\mathcal F$. Quotienting a chosen lattice by its $\pi$-torsion ensures flatness. Two lattices become comparable after multiplying by powers of $\pi$ and passing to a common refinement.

Indeed, choose finite presentations of $\mathcal F$ on a finite affinoid cover and clear the
finitely many denominators in their matrices to obtain local formal lattices. On overlaps,
the two comparison maps become integral after admissible blowups that principalize those
denominators. A common refinement makes the cocycle integral, so the lattices glue; removing
their $\pi$-torsion gives the asserted $R$-flat model.

### 13.3 Semistable formal curves

A proper admissible formal curve $\mathfrak C/R$ is **semistable** if its special fiber is reduced, its irreducible components are smooth away from ordinary double points, and étale-locally at every node the formal equation is

$$
XY=\pi^e
$$

for some $e\geq1$. If every $e=1$, the total space is regular at the nodes. Marked sections are required to lie in the smooth locus and remain disjoint.

Semistability is an additional property of a model, not a consequence of the regular-model
theorem. Resolution can make the total surface regular while leaving a cuspidal or multiple
special fiber, and a finite extension followed by normalization does not by itself remove all
such defects. Accordingly, the discussion below is conditional on a semistable model being
given. It proves the rigid geometry attached to that model, which is the part required for
tubes and reduction; it does not import a general semistable-reduction theorem.

Elementary semistable modifications can nevertheless be controlled here. Blowing up a
smooth closed point by the open ideal generated by its parameter and $\pi$ replaces one
residue disc by two disc regions joined along an annular collar; after removing $\pi$-torsion,
the special fiber remains reduced and nodal. On an annular chart $XY=\pi^e$, admissible
modifications at an integral intermediate radius split the annulus into adjacent annuli whose
thicknesses add to $e$. The chart calculation of Section 9.2 proves these assertions and shows
that their generic fibers are unchanged. Arbitrary blowups of the closed node are not covered
by this statement: their total transform can acquire a multiple exceptional component.

### 13.4 Components, annuli, and the reduction graph

Let $\mathfrak C$ be semistable. The smooth locus of each irreducible component of $\mathfrak C_s$ has a tube built from residue discs. Every node contributes an open annulus. These pieces form an admissible covering after finitely many affinoid neighborhoods are grouped appropriately:

# $$C^{\mathrm{an}}

\bigcup_v ]C_v^\circ[\;\cup\;
\bigcup_e ]z_e[.
$$

The **reduction graph** has a vertex for each irreducible component and an edge for each node, joining the components containing its two branches; a self-node gives a loop. With
$v(\pi)=1$, the thickness $e$ of $XY=\pi^e$ gives edge length $e$; in logarithmic absolute-value
coordinates the length is $-e\log|\pi|$. A semistable annular refinement subdivides an edge
and preserves the sum of its lengths. A semistable blowup at a smooth point can instead attach
a rational tree. Consequently the whole reduction graph is not model-independent, even after
one suppresses valence-two vertices. What is invariant under annular subdivision is the old
metric skeleton, and what survives arbitrary semistable refinement is the core obtained by
contracting the newly attached unstable rational trees. When a stable model is available, its
weighted graph is the canonical such core.

This graph is not the curve. Each vertex carries the smooth projective normalization of a residue component, and the tubes attached to it contain infinitely many analytic points. Nevertheless it records how annuli connect the good-reduction pieces and controls the first Betti contribution of degeneration:

$$
g(C)=\sum_v g(C_v)+b_1(\Gamma)
$$

for a split semistable model with geometrically irreducible components, with the appropriate geometric interpretation after extending the residue field. The formula follows from the normalization exact sequence of the nodal special fiber and constancy of arithmetic genus in a proper flat family.

Within this setting, the supplied semistable model is a good-reduction model exactly when its
special fiber is one smooth component and has no edges. A curve may have a tree-shaped graph
and still have bad reduction because its components or attaching data differ from a single
smooth fiber. The graph detects nodes, not every arithmetic defect.

## 14. Comparison with algebraic curves

### 14.1 Analytification of a finite-type curve

Let $C$ be a finite-type algebraic curve over $K$. Its analytification $C^{\mathrm{an}}$ is built by covering $C$ with affine pieces, replacing polynomial coordinate rings by convergent coordinate domains of varying radii, and gluing. It represents the same finite-extension points:

$$
C^{\mathrm{an}}(L)=C(L)
$$

for every finite extension $L/K$, while enriching their neighborhoods with convergent functions.

Analytification preserves fiber products, open and closed immersions, finite morphisms, smoothness, étaleness, separatedness, and properness. For a coherent algebraic sheaf $\mathcal F$, there is a coherent analytic sheaf $\mathcal F^{\mathrm{an}}$ obtained locally by analytic tensor product.

The algebraic affine line is not one affinoid. It is the increasing union of closed discs of radii tending to infinity after finite changes of scale. This is why replacing $K[T]$ by the single algebra $K\langle T\rangle$ would analytify only the integral unit region, not the whole line.

### 14.2 Proper comparison for coherent objects

**Theorem 14.1 (proper comparison).** Let $C$ be a proper algebraic curve over $K$ and $\mathcal F$ a coherent sheaf on $C$. Then

$$
H^q(C,\mathcal F)\xrightarrow{\sim}
H^q(C^{\mathrm{an}},\mathcal F^{\mathrm{an}})
$$

for every $q$. The functor $\mathcal F\mapsto\mathcal F^{\mathrm{an}}$ is an equivalence from coherent algebraic sheaves on $C$ to coherent analytic sheaves on $C^{\mathrm{an}}$.

**Proof strategy.** For projective space, compute both sides with the same finite cover by standard charts and the same homogeneous localization complex; convergent division shows the analytic complex has the algebraic cohomology. Resolve a coherent sheaf by finite sums of twists. A proper curve is projective, so a finite morphism to projective space or an ample line bundle reduces it to that calculation. Full faithfulness follows by applying cohomology to internal homomorphisms. Essential surjectivity uses enough negative twists to present any analytic coherent sheaf by algebraizable bundles, then algebraizes the kernel.

Exact hypotheses matter. Properness is needed both for finite-dimensional cohomology and for essential surjectivity. Coherence is needed for finite presentations. The theorem does not equate arbitrary analytic sheaves with algebraic sheaves.

For a proper flat algebraic model $\mathcal C/R$ and a coherent sheaf $\mathcal F$ on
$\mathcal C$, this theorem is compatible with formal completion:

$$
\mathcal F
\longmapsto
\widehat{\mathcal F}
\longmapsto
(\widehat{\mathcal F})_\eta
\simeq
(\mathcal F_K)^{\mathrm{an}}.
$$

The first passage remembers all infinitesimal special-fiber neighborhoods; the second inverts $\pi$; the result agrees with analytifying the algebraic generic fiber because properness covers every analytic point.

### 14.3 Maps, finite covers, and divisors

If $C$ is proper and $Y$ is a separated quasi-projective algebraic $K$-scheme, every analytic morphism

$$
C^{\mathrm{an}}\longrightarrow Y^{\mathrm{an}}
$$

comes from a unique algebraic morphism $C\to Y$. Choose an open immersion of $Y$ into a
projective scheme $\overline Y$. The analytic graph is the proper image of $C^{\mathrm{an}}$ in
$C^{\mathrm{an}}\times\overline Y^{\mathrm{an}}$, hence is closed. Its coherent ideal
algebraizes by proper comparison. The first projection is an isomorphism after analytification
and therefore algebraically. The algebraic graph cannot meet
$C\times(\overline Y\setminus Y)$, since that proper intersection would have nonempty
analytification. Thus its second projection lands in $Y$. Separatedness makes the graph, and
hence the morphism, unique.

The same conclusion holds for a separated finite-type target when a proper compactification
is supplied. No compactification theorem for an arbitrary target is being used implicitly.

Consequently finite analytic maps between proper algebraic curves are algebraic, and finite analytic covers correspond to finite algebraic covers. Normalization commutes with analytification. Ramification indices and residue degrees at closed points agree because the completed local DVR extensions agree.

Analytic and algebraic divisors also coincide on a smooth proper curve. The comparison of meromorphic function fields is

$$
K(C)\xrightarrow{\sim}\mathcal M(C^{\mathrm{an}}),
$$

and orders at corresponding points agree. Hence degree, linear equivalence, Picard groups, canonical divisors, Riemann--Roch spaces, and Jacobian constructions have the same values in both categories.

These conclusions extend to correspondences: a finite analytic correspondence on proper curves is algebraic. This fact is crucial whenever an operator is first visible on formal tubes but must act on global algebraic cohomology.

### 14.4 Exactly where comparison fails

Nonproper spaces admit more analytic functions than algebraic ones. On the closed unit disc,

$$
\sum_{n\geq0}\pi^{n^2}T^n
$$

is analytic and is not a polynomial. Thus algebraic functions on $\mathbf A^1_K$ and analytic
functions on bounded subdomains cannot be identified term by term without specifying the
domain. The displayed series in fact converges on every closed disc, since the quadratic
decay of $|\pi|^{n^2}$ dominates every fixed exponential radius. Hence even on the entire
analytic affine line, global analytic functions need not be polynomials when the valuation is
nontrivial.

Analytic domains also need not be algebraic opens. A closed annulus inside the multiplicative line is cut out by absolute-value inequalities, not by nonvanishing of polynomials. Its two boundary circles have no algebraic-open analogue.

Formal completion can fail to recover a nonproper analytification. Completing $\mathbf A^1_R$ gives only the closed unit disc. Completing $\mathbf G_{m,R}$ gives the unit circle $|T|=1$. Properness is what forces every generic point to acquire a center on the special fiber and makes completion exhaustive.

Finally, a special fiber is not an invariant of the analytic curve. Admissible blowups can add components and subdivide nodes while preserving the generic fiber. Only statements stable under common refinement—such as tubes viewed through the induced analytic isomorphism, annular lengths under subdivision, or the stable core after unstable trees have been contracted—are intrinsic. The existence of a semistable model is itself an additional reduction theorem, not a consequence of blowup invariance.

## 15. A reusable dictionary

### 15.1 Hypothesis ledger

The main results of the book can be used safely by keeping their hypotheses visible.

**Analytic algebras.** The base field is complete, nontrivially valued, and nonarchimedean. Strict affinoid algebras use radii in $|K^\times|$. Tate algebras and their affinoid quotients are noetherian; maximal residue fields are finite over $K$. The spectral seminorm is a norm only after removing nilpotents.

**Localization and sheaves.** Rational domains require numerators together with the denominator to generate the unit ideal. Rational localization is flat, not necessarily faithfully flat. Faithfulness comes from a finite cover. Tate acyclicity concerns admissible finite affinoid covers and finite modules. Coherent descent on general spaces uses quasi-separatedness.

**Formal models.** The formal chapters assume a complete discrete valuation ring $R$ with fraction field $K$. Admissible formal schemes are topologically of finite type and $R$-flat. The admissible-blowup invariance theorem requires an open center, equivalently one supported on the special fiber; a nonopen center has no such invariance guarantee. Generic fibers forget $\pi$-torsion.

**Reduction and tubes.** Specialization sends maximal analytic points to scheme points by reduction of bounded values. It is naturally surjective onto closed points in the finite-type setting, not asserted onto every nonclosed point at this level. Tubes depend on reduced strata and are often non-affinoid. Their descriptions by discs and annuli may require finite residue-field extension or étale coordinates.

**Curves.** Normality, regularity, and smoothness coincide only under the stated separability or perfection assumptions. A proper reduced rigid curve is algebraizable; smooth proper curves are projective. Proper comparison applies to coherent sheaves and cohomology. If a semistable model is supplied, its nodes give annular tubes; the graph genus formula uses the split and geometric-irreducibility hypotheses stated in Section 13.4. General existence of a semistable model is not assumed here.

### 15.2 The model-independence principle

The theory can be summarized by one sequence of translations:

$$
\begin{array}{ccccc}
\text{integral formal model}
&\xrightarrow{\text{invert }\pi}&
\text{rigid analytic space}
&\xleftarrow{\text{analytify}}&
\text{proper algebraic curve},\\
\downarrow\text{reduce}&&\downarrow\text{specialize}&&\\
\text{special fiber}
&\xleftarrow{\text{centers}}&
\text{tubes, discs, and annuli}.&&
\end{array}
$$

Moving right from a formal model forgets which integral functions were chosen. Moving left by specialization recovers centers only relative to that choice. An admissible blowup changes the lower row and leaves the upper analytic space fixed. Any claim made from a special fiber must therefore be checked under blowup.

For calculations, one deliberately chooses a useful model. Smooth models turn residue fibers into discs. Semistable models isolate degeneration in annuli. Blowups refine inequalities into rational domains. Proper algebraic models bring finite cohomology and algebraization. Common refinements guarantee that results agreeing after these changes belong to the analytic curve rather than to the chosen coordinates.

### 15.3 Conclusion

Nonarchimedean analytic geometry begins with a small convergence condition: coefficients of a restricted series tend to zero. From it follow multiplicative norms, division, noetherianity, and finite residue extensions. Rational localization then turns absolute-value inequalities into coordinate rings. Tate acyclicity identifies exactly which covers permit functions and finite modules to glue, producing rigid spaces and coherent sheaves.

Formal geometry explains the shape of that analytic topology. Integral coordinates reduce to a special fiber; inverting the uniformizer produces the generic fiber; formal blowup charts become rational domains. Specialization gathers analytic points into tubes. Above a smooth point lies a disc and above a node an annulus; when a semistable proper model is given, its analytic curve is assembled from these pieces according to its reduction graph.

Properness closes every analytic end. It makes coherent cohomology finite, forces divisors to balance, and supplies enough global sections for projective embedding. Consequently a proper rigid curve returns uniquely to algebraic geometry, with its coherent sheaves, maps, finite covers, functions, divisors, and cohomology unchanged. What remains distinctively analytic is not a rival class of proper curves, but a precise language for their bounded regions and reduction. Formal models provide that language, and admissible blowups ensure that its conclusions do not depend on how the integral picture was drawn.
