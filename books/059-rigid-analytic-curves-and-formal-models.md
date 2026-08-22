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
   - [Coherence of direct images](#95-coherence-of-direct-images)
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

$$
K\langle T_1,\ldots,T_n\rangle =
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

**Lemma 2.3 (field descent under integral extensions).** Let $B\to C$ be an injective
integral ring homomorphism into a field $C$. Then $B$ is a field.

**Proof.** Identify $B$ with its image. Take $b\in B$, $b\neq0$. Its inverse $b^{-1}\in C$
is integral over $B$, so for some $d\geq1$ there are $c_1,\ldots,c_d\in B$ with

$$
(b^{-1})^{d}+c_1(b^{-1})^{d-1}+\cdots+c_d=0.
$$

Multiplying by $b^{d-1}$ turns the leading term into $b^{-1}$ and every other term into an
element of $B$, so $b^{-1}=-(c_1+c_2b+\cdots+c_db^{d-1})\in B$. $\square$

**Proof (of Theorem 2.2).** We argue by induction on $n$ for
$A_n=K\langle T_1,\ldots,T_n\rangle$; the case $n=0$ gives $A_0/\mathfrak m=K$.

Let $n\geq1$ and let $\mathfrak m\subset A_n$ be a maximal ideal. The zero ideal is not maximal because
$A_n$ is not a field: indeed $T_1$ has no inverse, since $T_1g=1$ with $g=\sum_J b_JT^J$
would force the constant coefficient of the left side, namely $0$, to equal the constant
coefficient $1$ of the right side. So we may choose $g\in\mathfrak m$, $g\neq0$. As a
convergent series, $g$ involves at least one variable: if all coefficients of nonconstant
monomials vanished, then $g$ would be a nonzero scalar, hence a unit of $K$ embedded in
$A_n$, forcing $\mathfrak m=A_n$. Permute the variables so that $T_n$ occurs among
them; this permutation is an automorphism of $A_n$, and it carries maximal ideals to maximal
ideals with isomorphic residue fields, so the induction step may be performed after it.

Scale $g$ to Gauss norm one. Its reduction modulo topologically nilpotent coefficients is a
nonzero polynomial involving $T_n$, so by the triangular substitution and preparation theorem
of Section 2.5 there is a $K$-algebra automorphism $\sigma$ of $A_n$ such that $\sigma(g)$
factors as a unit of $A_n$ times a monic polynomial

$$
P=T_n^{d}+p_{d-1}T_n^{d-1}+\cdots+p_0,\qquad p_j\in A_{n-1}.
$$

Replacing $\mathfrak m$ by $\sigma(\mathfrak m)$ changes nothing: $\sigma$ induces a
$K$-isomorphism $A_n/\mathfrak m\cong A_n/\sigma(\mathfrak m)$ of the residue fields, so we
may assume from the start that $\mathfrak m$ contains such a monic polynomial $P$.

Division by $P$ (Section 2.5) expresses every element of $A_n$ as
$qP+r$ with $\deg_{T_n}r<d$, hence every element of $L:=A_n/\mathfrak m$ as a polynomial in
$t_n:=T_n\bmod\mathfrak m$ of degree less than $d$ with coefficients in
$B:=A_{n-1}/\mathfrak m'$, where $\mathfrak m'=\mathfrak m\cap A_{n-1}$. Thus $L$ is
generated as a $B$-algebra by the single element $t_n$, and $P(t_n)=0$ exhibits $t_n$ as
integral over $B$. In particular $B\to L$ is injective and integral, so $L$ a field forces
$B$ to be a field by Lemma 2.3; therefore $\mathfrak m'$ is a maximal ideal of $A_{n-1}$.
The induction hypothesis makes $B/K$ a finite extension, and $L$ is generated over $B$ by one
integral element, so $[L:B]<\infty$ and finally $L/K$ is finite.

For a general affinoid algebra $A=K\langle T_1,\ldots,T_n\rangle/I$, a maximal ideal
$\mathfrak m\subset A$ pulls back to a maximal ideal $M\supset I$ of the Tate algebra,
because the surjection $T_n/I\twoheadrightarrow A/\mathfrak m$ exhibits the target as a
field. Then $A/\mathfrak m\cong A_n/M$, already treated. $\square$

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

This section proves the spectral-radius formula

$$
\rho_A(f)=\lim_{m\to\infty}\|f^m\|_q^{1/m},
$$

together with the consequences that the limit is independent of the chosen affinoid
presentation, that its kernel is the nilradical, and that on a reduced affinoid algebra it is
a norm equivalent to every quotient norm.

Everything rests on two elementary comparisons between point values and quotient norms. The
first is the evaluation bound. If $F$ lifts $f$ to a presentation $A=T_n/I$, then for every
$x\in\operatorname{Sp}A$ the maximum principle of Section 2.3 gives
$|f(x)|=|F(x)|\leq\|F\|_G$, and taking the infimum over all lifts yields

$$
|f(x)|\leq\|f\|_q.
$$

The second is power-multiplicativity of $\rho_A$. Since absolute values are nonnegative,
the supremum of $m$-th powers is the $m$-th power of the supremum:

$$
\rho_A(f^m)=\sup_x|f(x)|^m=\Big(\sup_x|f(x)|\Big)^{m}=\rho_A(f)^m .
$$

Combining both, $\rho_A(f)^m=\rho_A(f^m)\leq\|f^m\|_q$, so the limit inferior of
$\|f^m\|_q^{1/m}$ is at least $\rho_A(f)$. All the work lies in the reverse inequality.

**Proposition 3.1 (nonzero affinoid algebras have points).** If $B$ is a nonzero affinoid
algebra, then $\operatorname{Sp}B\neq\emptyset$.

**Proof.** The ring $B$ is noetherian by Theorem 2.1 and nonzero, so Zorn's lemma applied to
the nonempty family of proper ideals, ordered by inclusion and chained by unions, produces a
maximal ideal. Its residue field is finite over $K$ by Theorem 2.2. $\square$

**Lemma 3.2 (convergence above a strict bound).** If $c\in K^\times$ satisfies
$\rho_A(f)<|c|$, then there is $N$ with $\|f^m\|_q<|c|^m$ for all $m\geq N$. In particular
$\limsup_{m}\|f^m\|_q^{1/m}\leq|c|$.

**Proof.** Consider the affinoid algebra

$$
B=A\langle V\rangle/(Vf-c),
$$

where $V$ is a new bounded variable. Suppose $B\neq0$. By Proposition 3.1 it has a maximal ideal,
and evaluating the images of $V$ and $f$ in its residue field gives a point $y$ of
$\operatorname{Sp}B$ whose contraction $x$ lies in $\operatorname{Sp}A$. The coordinate $V$
has quotient norm at most one in $A\langle V\rangle$, hence satisfies $|V(y)|\leq1$ by the
evaluation bound. Since $Vf=c$ holds in $B$,

$$
|f(x)|=|c|/|V(y)|\geq|c|>\rho_A(f),
$$

contradicting the definition of $\rho_A$. Therefore $B=0$: the single relation $Vf-c$
generates the unit ideal of $A\langle V\rangle$. Write

$$
1=\Big(\sum_{j\geq0}h_jV^{j}\Big)(Vf-c),\qquad h_j\in A,\quad \|h_j\|_q\to0,
$$

an identity of convergent series. Comparing coefficients: the constant term forces
$h_0=-1/c$, and the coefficient of $V^{j+1}$ forces $h_jf-ch_{j+1}=0$. Induction gives

$$
h_j=-\frac{f^{j}}{c^{\,j+1}},
$$

so convergence means exactly that $\|f^{j}\|_q/|c|^{j+1}\to0$. For all large $j$ this says
$\|f^{j}\|_q<|c|^{j}$. $\square$

The hypothesis $\rho_A(f)<|c|$ requires an element with value strictly larger than the
spectral radius, which the value group $|K^\times|$ need not contain. This is where the
standing convention on auxiliary absolute values (Section 1.2) enters: after adjoining an
element of any prescribed positive real value and completing, one obtains complete extensions
$K'/K$ with elements of value arbitrarily close to $\rho_A(f)$ from above. Base change
preserves both sides of the formula: if $x$ is a point of $\operatorname{Sp}A$ with residue
field the finite extension $K(x)$, then $K'\otimes_KK(x)$ is a nonzero finite $K'$-algebra,
hence has a maximal ideal whose residue field is finite over $K'$; contracting it recovers
$x$, so every point of $\operatorname{Sp}A$ lifts to $\operatorname{Sp}A_{K'}$ and the
suprema agree. On the other side, completed base change carries any presentation of $A$ to a
presentation of $A_{K'}$ by the same generating ideal, and the quotient norm of $A_{K'}$
restricts to the original quotient norm on the image of $A$, because both are infima over the
same family of lifts; so the limits coincide by the presentation-independence proved below.

**Theorem 3.3 (spectral-radius formula).** For every $f\in A$,

$$
\rho_A(f)=\lim_{m\to\infty}\|f^m\|_q^{1/m}.
$$

**Proof.** Fix $\varepsilon>0$. Choose a complete extension $K'/K$ containing an element
$c'$ with $\rho_A(f)<|c'|<\rho_A(f)+\varepsilon$, where the absolute value is computed in any
residue field of $A_{K'}$ containing it; Lemma 3.2 applied over $K'$ bounds the limsup there
by $|c'|$, and since
the limsup is independent of the extension, $\limsup_m\|f^m\|_q^{1/m}<\rho_A(f)+\varepsilon$.
Letting $\varepsilon\to0$ and combining with the lower bound above gives the limit.
$\square$

Two structural consequences follow. First, the limit is independent of the presentation:
any two quotient norms coming from presentations of $A$ are equivalent, say
$d^{-1}\|\,\cdot\,\|_1\leq\|\,\cdot\,\|_2\leq d\|\,\cdot\,\|_1$, and raising to the $m$-th
power and taking $m$-th roots makes the constant $d^{1/m}$ tend to one. Second, the kernel of
$\rho_A$ is the nilradical: $\rho_A(f)=0$ implies $\|f^m\|_q\to0$ by the formula, while the
function vanishing at every maximal point is nilpotent by the maximum principle discussion of
Section 2.3; conversely a nilpotent evaluates to zero everywhere. Hence $\rho_A$ is a norm
exactly when $A$ is reduced.

On a reduced affinoid algebra, $\rho_A$ is even equivalent to each quotient norm. The upper
bound $\rho_A(f)\leq\|f\|_q$ is the evaluation bound. For the lower bound, write
$U_c=\{f:\rho_A(f)<c\}$ for $c>0$. By the spectral-radius formula,
$f\in U_c$ exactly when $\|f^{M}\|_q<c^{M}$ for some $M$, so $A$ is the union of the closed
sets $\overline{U}_{M,c}=\{\|f^{M}\|_q\leq c^{M}\}$, one for each $M$. The space $A$ is
complete for the quotient norm by Theorem 2.1, and Baire's theorem makes some
$\overline{U}_{M,c}$ contain a ball $\{\|g\|_q\leq r\}$: then $\|g\|_q\leq r$ implies
$\rho_A(g)\leq\|g^{M}\|_q^{1/M}<c$. Scaling $g$
arbitrarily converts the ball into a global estimate

$$
\rho_A(g)\leq(c/r)\,\|g\|_q ,
$$

which is the required equivalence, with constant $(c/r)$ depending on the auxiliary choice
of $c$ alone. $\square$

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

$$
A\left\langle\frac{f_1}{f_0},\ldots,\frac{f_m}{f_0}\right\rangle =
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

The proof rests on three lemmas: a comparison theorem for module norms, the strictness of the
Tate adjunction, and an algebraic identity that exhibits every rational localization as an
ordinary localization at one element.

**Lemma 4.3 (norms on finite modules).** Let $M$ be a finite module over the affinoid
algebra $A$. Any two complete norms on $M$ for which multiplication by each fixed element of
$A$, and addition, are contractive in the sense that

$$
\|a m+a'm'\|\leq\max(\|a\|_q\|m\|,\|a'\|_q\|m'\|)
$$

are equivalent. In particular all quotient norms arising from finite free presentations of
$M$ are equivalent, every submodule $M'\subset M$ is closed, and the norm induced on $M'$ by
a quotient norm of $M$ is equivalent to any quotient norm of $M'$ itself.

**Proof.** The argument is the Baire argument of Section 3.3, run one level up from algebras
to modules. Let $x_1,\ldots,x_s$ generate $M$. The displayed inequality shows that for either
norm, say $\|\cdot\|_j$, the map $\varphi_j:A^s_q\to(M,\|\cdot\|_j)$ sending a tuple to
$\sum b_ix_i$ is continuous; here $A^s_q$ carries the max of quotient norms. Both sides are
complete metric groups: completeness of $(M,\|\cdot\|_j)$ holds by hypothesis for one norm
and by Theorem 2.1 for a quotient norm, and closedness of the image is not needed because
$\varphi_j$ is surjective by choice of the generators. Surjectivity writes $M$ as the union
of the closed sets $\varphi_j(\{b:\|b\|\leq n\})$, and Baire's theorem makes one of them
contain a ball around some point; translating and scaling as in Section 3.3 produces a
constant $c_j>0$ such that every $m\in M$ admits a representation $m=\sum b_ix_i$ with

$$
\max_k\|b_k\|_q\leq c_j\|m\|_j .
$$

Given this for both norms, any $m$ satisfies
$\|m\|_1\leq c_2(\max_i\|x_i\|_1)\,\|m\|_2$ by expanding in the $x_i$ and applying the
displayed inequality, and symmetrically with the indices exchanged. Hence the norms are
equivalent. Equivalence of quotient norms follows because both are complete and contractive
for the $A$-action. Closedness of $M'$ is Theorem 2.1 applied to the presentation of $M'$ as
a quotient of a finite free module, whose map into $M$ is continuous. Finally, the restricted
norm on $M'$ is again complete, because $M'$ is closed inside the complete space $M$, and it
is contractive for the $A$-action; equivalence with a quotient norm of $M'$ is therefore the
already-proved comparison. $\square$

**Lemma 4.4 (strictness of the Tate adjunction).** For finite $A$-modules
$M'\subset M$, the natural map $M'\langle S_1,\ldots,S_n\rangle\to M\langle S_1,\ldots,S_n\rangle$
is injective, and consequently $A\langle S_1,\ldots,S_n\rangle$ is a flat $A$-algebra.

**Proof.** Since the monomials $S^J$ have Gauss norm one, an element of $M\langle S\rangle$
is exactly a family $(m_J)$, indexed by multi-indices, with $m_J\to0$, and its norm is the
supremum of $\|m_J\|$. By Lemma 4.3 the norm on $M'$ induced from $M$ is equivalent to a
quotient norm of $M'$, so a family in $M'$ converges to zero in $M'$ exactly when it does in
$M$. An element of the kernel of $M'\langle S\rangle\to M\langle S\rangle$ is thus a
zero-convergent $M'$-family, hence vanishes in $M'\langle S\rangle$: the map is injective,
and this identifies $M'\langle S\rangle$ with its image inside $M\langle S\rangle$.

For flatness, recall that over a noetherian ring exactness of a functor on finite modules
implies exactness, because every finitely generated ideal or submodule occurs as the image in
a finite free module of a finite submodule. The functor $M\mapsto M\otimes_AA\langle S\rangle$
is right exact, and so is $M\mapsto M\langle S\rangle$; the two agree canonically on finite
free modules, where both produce finite direct sums of copies of $A\langle S\rangle$, and
hence they are canonically isomorphic on all finite modules, which are finitely presented.
The first paragraph applied to the inclusion of an arbitrary finite submodule therefore gives
injectivity after tensoring, which proves flatness. $\square$

**Lemma 4.5 (principal localization).** Let $R=A\langle T_1,\ldots,T_m\rangle$ over the
affinoid algebra $D$, let $g,h_1,\ldots,h_m\in D$ generate the unit ideal, and put
$J=(gT_1-h_1,\ldots,gT_m-h_m)$. Then the class of $g$ is invertible in $R/J$, and the
natural map induces a canonical isomorphism

$$
R[1/g]\;\cong\; R/J .
$$

**Proof.** Choose $d_0,d_1,\ldots,d_m\in D$ with $\sum_{i=0}^md_ih_i=1$, where $h_0:=g$, and
set $u=d_0+d_1T_1+\cdots+d_mT_m\in R$. Modulo $J$,

$$
gu=d_0g+\sum_{i=1}^md_igT_i\equiv d_0g+\sum_{i=1}^md_ih_i=1,
$$

so the class of $u$ is an inverse of the class of $g$ in $R/J$. Hence the surjection
$R\twoheadrightarrow R/J$ inverts $g$ and factors uniquely through $R[1/g]$, giving a
surjective map $R[1/g]\to R/J$. Conversely the universal property of the Tate algebra gives a
$D$-algebra homomorphism $R\to R[1/g]$ sending $T_i$ to $h_i/g$; it kills $J$, since
$g\cdot(h_i/g)-h_i=0$, so it descends to a map $R/J\to R[1/g]$. The two maps are mutually
inverse because each composite fixes the generators $T_i$ and the elements of $D$, and these
generate the source algebras. $\square$

**Proof (of Theorem 4.2).** _Flatness._ Let $U$ be cut out by $f_0,f_1,\ldots,f_m$
generating the unit ideal, and write $R=A\langle T_1,\ldots,T_m\rangle$,
$A_U=R/(f_0T_i-f_i)$. By Lemma 4.5, applied with $g=f_0$ and $h_i=f_i$,

$$
A_U\cong R[1/f_0].
$$

Now $R=A\langle T_1,\ldots,T_m\rangle$ is flat over $A$ by Lemma 4.4, and localization
$R\mapsto R[1/f_0]$ is exact and flat. The composite $A\to A_U$ is therefore flat.

_Transitivity._ Let $V\subset U$ be rational in $U$, presented by
$g_0,g_1,\ldots,g_r\in A_U$ generating the unit ideal:

$$
A_V=A_U\langle S_1,\ldots,S_r\rangle/(\gamma_0S_i-\gamma_i).
$$

First apply Lemma 4.5 over the affinoid algebra $D=A_U$, with $g=\gamma_0$ and
$h_i=\gamma_i$, using that the $\gamma_i$ generate the unit ideal of $A_U$ by hypothesis:

$$
A_V\cong A_U\langle S_1,\ldots,S_r\rangle[1/\gamma_0].
$$

Now unwind $A_U$. Choose lifts $\gamma'_i\in R$ of the $\gamma_i$; since $(-)\langle S\rangle$
is right exact as a functor of algebras over $A$, the identification $A_U=R/J$ with
$J=(f_0T_j-f_j)$ gives $A_U\langle S\rangle=R\langle S\rangle/JR\langle S\rangle$, and so,
localizing at the image of $\gamma'_0$,

$$
A_V\cong R\langle S\rangle[1/\gamma'_0]/JR\langle S\rangle[1/\gamma'_0].
$$

In the ring $R\langle S\rangle[1/\gamma'_0]$ the identity $\sum a_if_i=1$ remains valid, so
the argument of Lemma 4.5 trades the relations $J$ for inversion of $f_0$:

$$
A_V\cong R\langle S\rangle[1/\gamma'_0][1/f_0]
\cong R\langle S,U\rangle/(\gamma'_0f_0U-1).
$$

The last display presents $A_V$ as obtained from $A$ by the flat steps of Lemmas 4.4 and 4.5
only: adjoining Tate variables, quotienting by a principal relation whose constant combination
is trivial, and inverting one element. Each step is flat, so $A\to A_V$ is flat as a
composition of flat maps. Moreover the universal properties used along the way identify
maps from affinoid spaces into $V$ with maps into $\operatorname{Sp}A$ factoring through this
one-element localization, which is precisely the affinoid-subdomain universal property for
the set of points where $|\gamma_0'(x)f_0(x)|\geq|c|$ for any chosen $c\neq0$; hence
$V$ is an affinoid subdomain of $\operatorname{Sp}A$, presented rationally, and its algebra
is the corresponding completed base change. $\square$

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

Rational domains are the coordinate patches, but unions and gluing require a notion of admissibility. An **affinoid subdomain** $U\subset X=\operatorname{Sp}A$ is a subset represented by an affinoid algebra $A_U$ with the universal property that maps from affinoid spaces into $X$ whose point images lie in $U$ factor uniquely through $U$. Rational domains are affinoid subdomains. The refinement
statements used in this book concern finite unions of rational domains; they are proved
here. The refinement theorem for arbitrary affinoid subdomains is recorded immediately
afterwards as a standing input, together with an account of exactly which arguments would
consume it.

**Proposition (rational-subdomain refinements).** Let $X=\operatorname{Sp}A$ be affinoid.

1. If $U$ and $V$ are rational domains of $X$, then $U\cap V$ is a rational domain of $U$,
   of $V$, and of $X$, and

$$
A_{U\cap V}=A_U\widehat\otimes_AA_V .
$$

2. A finite union $U=U_1\cup\cdots\cup U_r$ of rational domains of $X$ is an admissible
   open of $X$, the family $(U_i)$ is an admissible cover of $U$, and the same holds after
   pulling back along every morphism of affinoid spaces $\operatorname{Sp}B\to X$ whose point
   image lies in $U$: the preimages $\varphi^{-1}(U_i)$ form a finite cover of
   $\operatorname{Sp}B$ admitting the finite refinement by the pairwise intersections
   $\varphi^{-1}(U_i)\cap\varphi^{-1}(U_j)$.

3. Two finite families of finite unions of rational domains that cover the same subset of
   $X$ admit a common finite refinement by rational domains of $X$, namely the family of all
   pairwise intersections of members of the two families.

**Proof.** Statement 1 is the transitivity part of Theorem 4.2, read set-theoretically
through the universal property: the coordinate algebra of the intersection is the completed
base change of either rational localization by the other, and the resulting algebra
represents the intersection because a map from an affinoid space into $X$ factors through
$U\cap V$ exactly when it factors through both $U$ and $V$, and unique factorizations
compose.

For statement 2, admissibility is checked against test maps, so let
$\varphi:\operatorname{Sp}B\to X$ be a morphism of affinoid spaces whose point image lies
in $U$. Each preimage $\varphi^{-1}(U_i)$ is a rational domain of
$\operatorname{Sp}B$: if $U_i$ is cut out by $f_{i0},\ldots,f_{im}$ generating the unit
ideal, the pullbacks $\varphi^\sharp(f_{ij})$ generate the unit ideal of $B$, and the
substitution homomorphism presents the preimage by the same relations; this is the base
change compatibility of rational localization recorded after Proposition 4.1. The preimages
cover $\operatorname{Sp}B$ because their point images cover the point image of
$\varphi$, and by statement 1 every pairwise intersection is a rational domain of each
factor, hence of $\operatorname{Sp}B$. Being finite and rational, the refinement qualifies
under the definition of admissible cover.

Statement 3 is statement 1 applied to all pairs. $\square$

**Standing Input (Gerritzen--Grauert refinement).** The general refinement theorem asserts
that every affinoid subdomain $U$ of an affinoid space $X=\operatorname{Sp}A$ is a finite
union of rational domains of $X$. Its proof rests on a local classification of affinoid
subdomains: around every point of $U$ one produces a neighborhood presented by finitely many
inequalities, using multivariable division preparation and a boundary argument on the
functions defining $U$. Neither the classification nor the boundary argument is developed in
this book, and the statement is therefore consumed nowhere below. Every cover constructed in
Chapters 6 through 14 consists of Laurent or rational domains produced directly from
inequalities, to which Theorem 5.1 applies without refinement; the tube decompositions of
Chapter 10 and the uniformization theory built on this book likewise enter through annular
and rational charts, and the refinement proposition above closes the finite-union cases. A
reader extending the theory to covers by arbitrary affinoid subdomains should import this
standing input and combine it with the transfer lemma of Section 5.2, which converts a
rational refinement into equality of Čech cohomology.

An admissible open in an affinoid $X$ is a subset $V$ that has a covering by affinoid subdomains such that every map from an affinoid $Y$ to $X$ with image in $V$ pulls that covering back to one admitting a finite affinoid refinement. A family $(V_i)$ covers $V$ **admissibly** if the same finiteness condition holds after every affinoid test map. This definition is designed so that quasi-compact analytic pieces see only finitely many coordinates at a time.

The admissible opens and admissible coverings satisfy the axioms of a Grothendieck topology: isomorphisms cover, coverings survive base change, and composites of coverings cover. There need be no useful topology on the underlying set having precisely these covers. Sheaves will be defined directly for this covering theory.

The finiteness condition is genuine. If the residue field is algebraically closed and infinite, the closed unit disc is the set-theoretic union of its residue tubes

$$
\{x:|T(x)-a|<1\},\qquad \widetilde a\in\widetilde K.
$$

Each tube is an admissible open, but the family has no finite subcover and is not an admissible cover of the affinoid disc. Were it admissible, a function could be prescribed independently on every residue class, contradicting analytic convergence.

### 5.2 Tate acyclicity

The definition of admissibility earns its keep through one exact sequence. Let $X=\operatorname{Sp}A$ and let $X=U_1\cup\cdots\cup U_r$ be a finite cover by Laurent domains of $X$. Write $A_{i_0\cdots i_p}$ for the affinoid algebra of the intersection. Then the augmented Čech complex

$$
0\longrightarrow A
\longrightarrow\prod_i A_i
\longrightarrow\prod_{i<j}A_{ij}
\longrightarrow\cdots
$$

is exact.

We prove the theorem by routing the analytic content through the flatness theorem of Section 4.4. Classical proofs begin with an explicit contracting homotopy for a two-piece cover $|f|\leq|c|$, $|f|\geq|c|$, obtained from convergent division; the norm estimates that force the glued series to converge are precisely the estimates behind flatness, so once Theorem 4.2 is available the remaining argument is a descent along faithful flatness.

**Lemma 5.2 (faithful flatness of finite rational covers).** Let $X=\operatorname{Sp}A$ and let $X=U_1\cup\cdots\cup U_r$ be a finite cover by rational domains. Then

$$
A\longrightarrow\prod_i A_{U_i}
$$

is faithfully flat: a finite $A$-module $M$ is zero exactly when all its restrictions
$M\otimes_AA_{U_i}$ are zero.

**Proof.** Each $A\to A_{U_i}$ is flat by Theorem 4.2, hence so is the map into the product.
For faithfulness, let $M\neq0$ be finite and suppose first that some element $\xi$ of $M$ is
nonzero; its annihilator is a proper ideal, contained in a maximal ideal
$\mathfrak m$, and $\xi_{\mathfrak m}\neq0$: if it vanished, some $s\notin\mathfrak m$ would
kill $\xi$, putting $s$ in the annihilator and contradicting
$\operatorname{Ann}(\xi)\subseteq\mathfrak m$. The point $\mathfrak m$ lies in some $U_i$
because the cover is finite and set-theoretic, and localization at the image of
$\mathfrak m$ identifies $(M\otimes_AA_{U_i})_{\mathfrak m}=M_{\mathfrak m}\neq0$. Hence
$M\otimes_AA_{U_i}\neq0$. Conversely each restriction of the zero module is zero. $\square$

**Lemma 5.3 (inequality descent).** Let $W=\operatorname{Sp}B$ be an affinoid space, let
$h_1,\ldots,h_s\in B$ and $0\neq c_1,\ldots,c_s\in K$, and write

$$
W_\nu^{+}=\{x\in W:|h_\nu(x)|\leq|c_\nu|\},\qquad
W_\nu^{-}=\{x\in W:|h_\nu(x)|\geq|c_\nu|\},
$$

and let $\mathfrak U$ be a finite cover of $W$ whose members have the form
$W\cap\bigcap_{\nu\in S}W_\nu^{\varepsilon_\nu}$ for some set of indices
$S\subseteq\{1,\ldots,s\}$ and signs $\varepsilon_\nu$. Then for every finite
$B$-module $M$ the augmented Čech complex of $\mathfrak U$ with values in the completed
tensor products of $M$ is exact:

$$
0\longrightarrow M\longrightarrow\prod_U(M\widehat\otimes_BB_U)
\longrightarrow\prod_{U<V}(M\widehat\otimes_BB_{UV})
\longrightarrow\cdots .
$$

**Proof.** We argue by induction on $s$. For $s=0$ the only member is $W$ itself and the
complex is $0\to M\to M\to0$. Assume $s\geq1$. For each sign vector
$\sigma\in\{\pm\}^s$ put

$$
P_\sigma=W\cap\bigcap_{\nu=1}^{s}W_\nu^{\sigma_\nu},
$$

discard the empty ones, and note that the survivors form a finite cover of $W$ by Laurent,
hence rational, domains: every point satisfies each inequality in one direction. By Lemma
5.2 and the flatness part of Theorem 4.2, the algebra $B\to\prod_\sigma B_{P_\sigma}$ is
faithfully flat. Since each $B_{P_\sigma}$ is flat over $B$, cohomology of our bounded
complex commutes with tensoring by $B_{P_\sigma}$; and an element $\xi\neq0$ of any
cohomology group survives at some maximal ideal, whose point lies in some $P_\sigma$, where
flat localization keeps it nonzero. It therefore suffices to prove exactness after
tensoring by each $B_{P_\sigma}$ in turn.

Fix $\sigma$. Termwise,

$$
(M\widehat\otimes_BB_U)\otimes_BB_{P_\sigma}
=M\widehat\otimes_BB_{U\cap P_\sigma},
$$

because completed base changes compose by the transitivity statement of Theorem 4.2, and the
differentials agree under this identification. So the tensor is the augmented Čech complex
of the induced cover $\mathfrak U|_{P_\sigma}=\{U\cap P_\sigma\}$ of the affinoid space
$P_\sigma$. Its members with $s\in S$ and $\varepsilon_s=-\sigma_s$ are empty and are
discarded; every survivor equals

$$
P_\sigma\cap\bigcap_{\nu\in S\setminus\{s\}}W_\nu^{\varepsilon_\nu},
$$

because every point of $P_\sigma$ satisfies the inequality defining
$W_s^{\sigma_s}$ identically. Thus
$\mathfrak U|_{P_\sigma}$ is a finite cover of $P_\sigma$ of exactly the form treated by the
induction hypothesis, cut out by the $s-1$ inequalities $h_1,\ldots,h_{s-1}$ restricted to
$P_\sigma$. Exactness follows. $\square$

**Theorem 5.1 (Tate acyclicity).** Let $X=\operatorname{Sp}A$ and let
$X=U_1\cup\cdots\cup U_r$ be a finite cover by Laurent domains of $X$. Then the augmented
Čech complex above is exact, and it remains exact after replacing every term by its
completed tensor product with any finite $A$-module.

**Proof.** Each $U_i$, being Laurent, is presented by finitely many elementary inequalities
of the form $|f|\leq1$ and $|g|\geq1$; constants are folded into the functions by scaling.
Collect all inequalities occurring in the presentations of the $U_i$ into one list
$h_1,\ldots,h_s$ with constants $c_1,\ldots,c_s$, so that every $U_i$ has the form treated
by Lemma 5.3. The lemma gives exactness for every finite module, which is the assertion.
$\square$

Two remarks place the theorem in its natural range. First, the induction proves more than it
states: nothing about the pieces was used beyond their presentation by elementary
inequalities, so the same complex is exact for any finite cover whose members are cut out
from a fixed finite list of such inequalities.

**Lemma (Čech transfer under common rational refinement).** Let $X=\operatorname{Sp}A$, let
$\mathfrak U=(U_1,\ldots,U_r)$ and $\mathfrak V=(V_1,\ldots,V_s)$ be finite covers of $X$ by
affinoid subdomains, with $\mathfrak V$ refining $\mathfrak U$, and fix a finite
$A$-module $M$. Assume that every nonempty intersection of members of either family is an
affinoid space, that each $U_I\cap V_J$ is a rational domain of $U_I$ and of $V_J$, and that
the induced covers of each affinoid intersection $U_I$ and $V_J$ by intersections with
members of the other family are cut out, after collecting inequality lists as in Theorem
5.1, from finitely many elementary inequalities. Then the natural map from the augmented
Čech complex of $\mathfrak V$ to that of $\mathfrak U$, both with coefficients in $M$,
induces isomorphisms on cohomology. In particular, if the complex of $\mathfrak V$ is exact,
so is the complex of $\mathfrak U$.

**Proof.** Form the double complex whose term of bidegree $(p,q)$ is

$$
D^{p,q}=\bigoplus_{\substack{i_0<\cdots<i_p\\ j_0<\cdots<j_q}}
M\widehat\otimes_AA_{U_{i_0}\cap\cdots\cap U_{i_p}\cap V_{j_0}\cap\cdots\cap V_{j_q}},
$$

with horizontal differentials induced by insertion of $V$-indices and vertical ones by
insertion of $U$-indices. Fix a tuple $I$. The $I$-th row is the augmented Čech complex of
the cover of the affinoid space $U_I$ by the rational domains $U_I\cap V_j$, with
coefficients in the finite module $M\otimes_AA_{U_I}$; by hypothesis it has the form treated
by Lemma 5.3, so its positive cohomology vanishes and its degree-zero cohomology is
$M\otimes_AA_{U_I}$. Dually, fixing a tuple $J$, the $J$-th column is the analogous complex
for the cover of $V_J$ by the rational domains $U_i\cap V_J$, likewise exact. Consider the
associated total complex together with the augmentation column given by the Čech complexes
of $\mathfrak U$ and $\mathfrak V$ themselves, which embed as the sub-double-complex with at
least one index list empty. Filtering the total complex by rows exhibits each graded piece
as a shifted exact row, so the positive cohomology of the total complex vanishes and its
degree-zero cohomology, computed through the augmentation, is that of the Čech complex of
$\mathfrak U$. Filtering instead by columns shows, by the same argument with the roles
exchanged, that it is also the Čech cohomology of $\mathfrak V$, compatibly with the natural
map between the two complexes induced by the diagonal refinement. Hence the map induces
isomorphisms on cohomology. $\square$

Second, the passage from Laurent covers to arbitrary finite admissible covers by affinoid
subdomains now decomposes into two explicitly controlled pieces: the existence of a common
finite rational refinement is exactly the standing input of Section 5.1, valid for covers by
finite unions of rational domains by the refinement proposition there and for arbitrary
affinoid subdomains only under the Gerritzen--Grauert input; and once such a refinement
$\mathfrak V$ of $\mathfrak U$ exists, the transfer lemma above hands exactness from
$\mathfrak V$ to $\mathfrak U$, because every hypothesis of the lemma holds when the members
of both families are Laurent or rational domains. This refinement step is the one standing
input used below whenever a general admissible cover, rather than a Laurent or rational
cover, enters an argument; the covers arising from inequalities in Chapters 6 through 14 are
Laurent or rational covers, to which the theorem applies directly.

The module statement deserves emphasis because it is not formal. Tensoring an arbitrary
exact complex with a module would not preserve exactness; here exactness was proved
simultaneously for all finite modules, the flatness theorem supplying the uniform control.
The theorem will turn finite modules into coherent sheaves and make higher cohomology vanish
on affinoids.

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

**Theorem 6.2 (proper mapping theorem).** Let $f:X\to Y$ be a proper morphism of rigid spaces, with $Y$ quasi-separated. For every coherent $\mathcal F$ on $X$, each $R^qf_*\mathcal F$ is coherent. If every fiber of $f$ has dimension at most $d$, then, under the model-dimension hypothesis recorded in Section 9.5 and satisfied in every application below, $R^qf_*\mathcal F=0$ for $q>d$.

**Proof; see Section 9.5.** The proof cannot be given with the tools available so far: finiteness statements of this strength are exactly what formal models supply. Once admissible blowups and the model theorem are available, the argument runs as follows. One extends $f$ to a proper morphism of admissible formal models after an admissible blowup of the source, extends $\mathcal F$ to a coherent sheaf on the model by clearing denominators in finite presentations, compares analytic cohomology with formal cohomology inverted by $\pi$ through Tate acyclicity on generic fibers of principal opens, and reads coherence off Book 58's finiteness theorem for direct images under proper formal morphisms. The full details occupy Section 9.5, which may be read immediately after Chapter 9; no result between this section and that one uses Theorem 6.2.

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

$$
\operatorname{sp}_{\mathfrak X} =
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

**Lemma (integral models of affinoid algebras).** Let $B$ be a $K$-affinoid algebra,
presented as a quotient $K\langle T_1,\ldots,T_n\rangle/J$, and let $A\subset B$ be the image
of $R\langle T_1,\ldots,T_n\rangle$. Then $A$ is $\pi$-adically complete, topologically of
finite type over $R$, has no $\pi$-torsion, and the natural map

$$
A[1/\pi]\longrightarrow B
$$

is an isomorphism.

**Proof.** The ideal $J$ is finitely generated because the Tate algebra is noetherian, hence
closed, so the image $A$ is a quotient of the complete ring $R\langle T\rangle$ by a closed
ideal and is complete; it is topologically of finite type by construction. For
$\pi$-torsion-freeness, suppose the class of $r\in R\langle T\rangle$ in $A$ is killed by
$\pi^n$. Then the image of $\pi^nr$ in $B$ is zero. But $\pi$ acts invertibly on the
$K$-vector space $B$, so the image of $r$ is zero, and the class of $r$ was already zero.
For the last assertion, note first that every element of $K\langle T\rangle$ has bounded
coefficients, since they tend to zero, so some scalar multiple by a power of $\pi$ lies in
$R\langle T\rangle$; hence $A[1/\pi]$ equals the image of $K\langle T\rangle$, which is all
of $B$. If $t\in K\langle T\rangle$ maps to zero in $B$, scale it so that $t'\in R\langle
T\rangle$; then $t'$ also maps to zero, so its class in $A$ vanishes, and since
$t=\pi^{-m}t'$ for some $m$, the class of $t$ vanishes in $A[1/\pi]$. $\square$

Thus $\operatorname{Spf}A$ is an admissible affine model of the affinoid space
$\operatorname{Sp}B$: this proves essential surjectivity when $X$ is affinoid.

**Proof (of Theorem 9.2).** _Essential surjectivity._ Let $X$ be quasi-compact and
quasi-separated. Cover it by finitely many affinoids $X_i=\operatorname{Sp}B_i$, choose
models $\mathfrak X_i=\operatorname{Spf}A_i$ as in the lemma, and refine the cover so that
every pairwise overlap $X_{ij}$ is a finite union of rational domains both of $X_i$ and of
$X_j$; this refinement exists by quasi-compactness of the overlaps and the
rational-subdomain refinement proposition of Section 5.1. Fix one rational domain $V$ of the
overlap decomposition inside $X_i$, presented by $f_0,\ldots,f_m$ generating the unit ideal
of $B_i$. Each ratio $f_j/f_0$ extends analytically to $V$. Enlarge the model by replacing
$A_i$ with the complete admissible subalgebra of $B_i$ generated by $A_i$ together with the
finitely many numerators and denominators occurring in these expressions; the lemma applies
to this enlarged image construction verbatim, the generic fiber stays $B_i$, and models are
only ever compared up to blowup, so nothing below is affected. We may therefore assume
$f_j\in A_i$ and that the products $f_0g_j$ with $g_j\in A_i$
re-express every coordinate function of $A_j$ restricted to $V$. Let
$I_{ij}\subset A_i$ be the ideal generated by $f_0$ and all such $g_j$, so that on the
generic fiber $I_{ij}$ cuts out precisely the locus where all the fractions become
regular; because the fractions are bounded on $V$, each relevant ratio is integral after
multiplication by a suitable power of $\pi$, and consequently $I_{ij}$ contains a power of
$\pi$ and is open. On the chart
of the admissible blowup of $\operatorname{Spf}A_i$ along $I_{ij}$ on which $f_0$ generates
the transformed ideal, Section 9.2 identifies the generic fiber with exactly the rational
domain where $|f_j|\leq|f_0|$, namely $V$; there the cleared fractions are integral, so this
chart is a formal open modeling $V$ inside $\mathfrak X'_i$, the blowup. Performing this for
every member of the overlap decomposition, and symmetrically for the models $\mathfrak
X_j$, replaces each $\mathfrak X_i$ by an admissible blowup whose formal opens model every
overlap piece. On triple overlaps the two ways of restricting the transition isomorphisms
agree on generic fibers; the differences between corresponding integral transition matrices
are killed by powers of $\pi$, and blowing up the finitely many ideals generated by those
matrices' nonintegral entries, once more by the denominator-clearing mechanism just used,
makes the cocycle identities literal identities of formal morphisms. The blown-up affine
models therefore glue as admissible formal schemes, and by construction their generic fibers
glue back to $X$ by Section 7.4. This gives an admissible formal model of $X$.

_Common domination._ Given two models $\mathfrak X$ and $\mathfrak X'$ of the same $X$,
apply the essential-surjectivity construction to the identity of $X$ read against both
models: the overlap analysis produces blowups of each whose formal opens model the same
pieces, and the identity transitions become integral after blowing up the finitely many
denominator ideals, giving a third model dominating both.

_Fullness._ Let $f:X\to Y$ be a morphism of qcqs rigid spaces with models chosen. Cover
$X$ by finitely many affinoids mapping into affinoids of $Y$. The coordinate functions of
$f$ on each piece are analytic functions on a rational domain of the target model; clearing
their denominators by powers of $\pi$ and blowing up the resulting open ideals of the source
model, exactly as above, turns them into morphisms of formal schemes on the charts, and the
cocycle condition on overlaps is arranged by the common-refinement step. Hence some
admissible blowup of the source model admits a formal morphism inducing $f$. This proves
Proposition 13.1 in advance, and no later argument needs to reprove it.

_Faithfulness and fullness on the localized category._ Two formal morphisms inducing the
same analytic map have coordinate differences vanishing after inverting $\pi$; each such
difference is killed by a power of $\pi$ on the noetherian source, and blowing up the ideal
generated by the finitely many relevant entries followed by removal of $\pi$-torsion makes
the difference literally zero. Thus the two morphisms become equal in the category localized
at admissible blowups. Conversely, given a formal morphism after localization, the
construction of the fullness paragraph reconstructs it from its generic fiber, so the
localized Hom sets inject into analytic Hom sets, and fullness supplies the reverse:
analytic morphisms lift, compatibly with composition because lifts can be compared after a
common further blowup. Finally, applying fullness to an analytic isomorphism and its inverse
and taking a common blowup of the source makes both composites defined and equal to the
identity in the localized category, which is precisely the statement that the two models are
isomorphic after localization. This proves the equivalence and the common-refinement
assertion. $\square$

The theorem does not identify a preferred model. Statements about special-fiber components, intersections, or reduction points are model-dependent. Statements invariant under admissible blowup belong to the analytic space.

### 9.5 Coherence of direct images

The proper mapping theorem of Section 6.4 was stated there but not proved there, because its proof requires formal models. This section carries out the proof. The route is the one the model theorem makes natural: compare analytic cohomology with formal cohomology on a model, and read finiteness off Book 58's formal-function theory.

Throughout, $K$ is discretely valued with ring $R$ and uniformizer $\pi$, and all rigid spaces are quasi-compact and quasi-separated.

**Lemma (generic-fiber comparison).** Let $\mathfrak X$ be an admissible formal scheme admitting a finite cover by formal principal opens whose pairwise intersections are again such opens, and let $\mathfrak F$ be coherent. Then for every $q\geq0$ the natural map

$$
H^q(\mathfrak X,\mathfrak F)\otimes_RK
\longrightarrow
H^q(\mathfrak X_\eta,\mathfrak F_\eta)
$$

is an isomorphism.

**Proof.** Cover $\mathfrak X$ by finitely many formal principal opens $\mathfrak U_i=\mathfrak D(f)$ with all intersections of the same form; quasi-compactness makes this possible, since finite intersections of principal opens are principal. By Section 7.3 each generic fiber $(\mathfrak U_i)_\eta$ is the rational domain $|f_i|\geq1$ inside $\mathfrak X_\eta$ locally, and every intersection
$(\mathfrak U_{i_0}\cap\cdots\cap\mathfrak U_{i_p})_\eta$
is cut out from the fixed finite list of inequalities $|f_i|\geq1$. Collecting that list, Lemma 5.3 applies: the augmented Čech complex of this cover, with coefficients in $\mathfrak F_\eta$, computes the analytic cohomology $H^q(\mathfrak X_\eta,\mathfrak F_\eta)$.

On the other side, Book 58, Section 7.3 identifies coherent sheaves on affine formal schemes with complete finite modules and shows these are acyclic; hence the Čech complex of the same cover with values in $\mathfrak F$ computes $H^q(\mathfrak X,\mathfrak F)$. Termwise, the identification of Section 7.3 gives

# $$\Gamma(\mathfrak U_{i_0}\cap\cdots\cap\mathfrak U_{i_p},\mathfrak F)\otimes_RK

\Gamma\bigl((\mathfrak U_{i_0}\cap\cdots\cap\mathfrak U_{i_p})_\eta,\mathfrak F_\eta\bigr),
$$

because inverting $\pi$ commutes with the completed localization defining a principal open: both algebras impose the single relation $fS-1$, and $\pi$ is already invertible in $K$. So the analytic Čech complex is the tensor of the formal one with $K$. Since $R\to K$ is flat, cohomology of a complex commutes with this tensor:

$$
H^q(\mathfrak X,\mathfrak F)\otimes_RK=H^q\bigl(C^\bullet\otimes_RK\bigr)
=H^q(\mathfrak X_\eta,\mathfrak F_\eta),
$$

and the maps are the natural ones. $\square$

**Lemma (properness descends to models).** Let $f:X\to Y$ be a proper morphism of rigid spaces and let $\mathfrak f:\mathfrak X\to\mathfrak Y$ be an extension to admissible models supplied by Theorem 9.2 after an admissible blowup of the source. Then $\mathfrak f$ is a proper morphism of formal schemes.

**Proof.** Properness of a finite-type morphism of quasi-compact quasi-separated formal schemes is a valuative statement: given a valuation ring $V$ with fraction field $L$, a morphism $\operatorname{Sp}V\to\mathfrak Y$, and an $L$-point of $\mathfrak X$ over it, one must extend the latter across the closed point, uniquely up to the separatedness already at hand. Read the same data through generic fibers. The generic point supplies an $L$-valued point of the generic fiber of $\mathfrak Y$, that is, a point of $Y_L$, and an $L$-point of $X_L$ above it, because the generic fiber functor converts the square into the corresponding analytic square by Section 8.4. Since $f$ is proper, this analytic point extends uniquely over the valuation, giving a compatible family of integral points. Each integral level lands in $\mathfrak X$, and specialization, which reaches every closed point of a topologically finite-type formal scheme by Section 8.1, produces the required extension point. Uniqueness follows because two extensions agree on the dense generic fiber, and the diagonal of a morphism whose generic fiber is separated is itself separated. Hence $\mathfrak f$ is proper. $\square$

**Lemma (lattice extension).** In the situation above, after replacing $\mathfrak X$ by a further admissible blowup, the coherent sheaf $\mathcal F$ extends to a coherent sheaf $\mathfrak F$ on $\mathfrak X$ with

$$
\mathfrak F_\eta\simeq\mathcal F .
$$

**Proof.** Cover $X$ by finitely many affinoids $X_i=\operatorname{Sp}A_i$ mapping into affinoid patches of $Y$, choose rings of definition, and present $\mathcal F|_{X_i}$ by finite matrices with entries in $A_i$. Multiplying the matrices by a common power of $\pi$ brings the entries into the chosen rings of definition, producing coherent formal modules $\mathfrak F_i$ on the affine models with $(\mathfrak F_i)_\eta\simeq\mathcal F|_{X_i}$. On overlaps, the two identifications differ by matrices with analytic entries; clearing denominators once more and passing to a common admissible refinement, which Theorem 9.2 provides for the finitely many overlaps, makes the transition isomorphisms integral, so they define gluing data for the $\mathfrak F_i$. Quotienting the glued module by its $\pi$-torsion preserves the generic fiber, because inverting $\pi$ kills torsion, and yields an admissible coherent sheaf with the required property. $\square$

**Theorem 9.3 (coherence part of Theorem 6.2).** Let $f:X\to Y$ be a proper morphism of quasi-compact quasi-separated rigid spaces and let $\mathcal F$ be coherent on $X$. Then each $R^qf_*\mathcal F$ is coherent.

**Proof.** Coherence is local on $Y$, so take $Y=\operatorname{Sp}B$ affinoid. Choose a ring of definition $A\subset B$, topologically of finite type over $R$ with $A[1/\pi]=B$, and set $\mathfrak Y=\operatorname{Spf}A$. Choose, by Theorem 9.2, an admissible blowup $\mathfrak X'\to\mathfrak X$ of an admissible model $\mathfrak X$ of $X$ together with a formal morphism $\mathfrak f:\mathfrak X'\to\mathfrak Y$ extending $f$; replace $\mathfrak X$ by $\mathfrak X'$. The previous two lemmas make $\mathfrak f$ proper and extend $\mathcal F$ to a coherent sheaf $\mathfrak F$ with $\mathfrak F_\eta\simeq\mathcal F$. For an affinoid open $V=\operatorname{Sp}B'$ of $Y$, presented rationally without loss of generality, the comparison lemma applied over the induced formal base change identifies

# $$H^q(f^{-1}(V),\mathcal F)

H^q(\mathfrak X_V,\mathfrak F)\otimes_RK,
$$

where $\mathfrak X_V$ is the inverse image of the corresponding formal open and $K$ enters because $A'[1/\pi]=B'$ for the ring of definition $A'$ of the rational domain. By Book 58, Section 8.2, applied to the proper formal morphism $\mathfrak f$, the sheaf $R^q\mathfrak f_*\mathfrak F$ is coherent, so $H^q(\mathfrak X_V,\mathfrak F)$ is a finite module over $A'$, and hence $H^q(f^{-1}(V),\mathcal F)$ is finite over $B'=A'[1/\pi]$ for every affinoid open $V$. These finitenesses glue: over a finite rational cover of $Y$, the restrictions of $R^qf_*\mathcal F$ are the sheaves attached to finite modules, and the descent data are inherited from those of $\mathcal F$, so Chapter 6's gluing produces a coherent sheaf on $Y$ whose sections over affinoids are exactly these groups. That sheaf is $R^qf_*\mathcal F$. $\square$

**Vanishing above fiber dimension.** The second clause of Theorem 6.2 holds under one additional hypothesis, satisfied in every application made below: there is a model $\mathfrak f:\mathfrak X\to\mathfrak Y$ as above whose special fibers have dimension at most $d$. Indeed, formal functions identify $R^q\mathfrak f_*\mathfrak F$ with the inverse limit of the direct images at finite levels, each of which vanishes for $q>d$ by Grothendieck's dimension vanishing on the noetherian schemes $\mathfrak X_n$ of dimension at most $d+\dim\mathfrak Y_s$ together with the corresponding statement fiberwise; the Mittag--Leffler condition is automatic for quotients of a finite module, and Nakayama then kills the limit. Tensoring with $K$ and using the comparison lemma gives $R^qf_*\mathcal F=0$ for $q>d$. The hypothesis holds automatically when $f$ is a curve over a point or when the model can be taken flat of the expected relative dimension: for an admissible model, flatness ties special-fiber dimension to generic-fiber dimension by the dimension formula, and blowing up along the special fiber never raises it. In particular, if $X$ is a proper rigid curve over $K$ and $\mathcal F$ is coherent, then $H^q(X,\mathcal F)=0$ for $q\geq2$ and both $H^0$ and $H^1$ are finite-dimensional $K$-vector spaces. These are precisely the finiteness statements used in Chapter 12.

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

**Proof.** This is the fullness and common-domination parts of Theorem 9.2, applied to the chosen models: its proof clears the denominators of the coordinate functions of $f$ on a finite affinoid cover and blows up the resulting open ideals. $\square$

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

$$
C^{\mathrm{an}} =
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

**Localization and sheaves.** Rational domains require numerators together with the denominator to generate the unit ideal. Rational localization is flat, not necessarily faithfully flat. Faithfulness comes from a finite cover. Tate acyclicity concerns admissible finite affinoid covers and finite modules; covers by arbitrary affinoid subdomains additionally consume the Gerritzen--Grauert standing input of Section 5.1, which is not used elsewhere in this book. Coherent descent on general spaces uses quasi-separatedness.

**Formal models.** The formal chapters assume a complete discrete valuation ring $R$ with fraction field $K$. Admissible formal schemes are topologically of finite type and $R$-flat. The admissible-blowup invariance theorem requires an open center, equivalently one supported on the special fiber; a nonopen center has no such invariance guarantee. Generic fibers forget $\pi$-torsion. Coherence of higher direct images is unconditional (Section 9.5); its vanishing clause consumes the model-dimension hypothesis recorded there, automatic for proper curves and for flat models of the expected dimension.

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
