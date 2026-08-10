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

The word *rigid* reflects the outcome. A function on a connected disc cannot be prescribed independently on arbitrarily many residue classes; convergent coefficients tie those values together. A compact analytic curve is even more constrained: it comes from a projective algebraic curve, and its coherent sheaves and cohomology are algebraic. Formal models reveal where this rigidity comes from. They record integral functions before a uniformizer is inverted, so reduction of those functions organizes the analytic space into discs and annuli.

### 1.2 Standing conventions

Throughout Chapters 1--6, $K$ is a complete field with a nontrivial nonarchimedean absolute value $|\cdot|$. Its valuation ring, maximal ideal, and residue field are

$$
K^\circ=\{a:|a|\leq1\},\qquad
K^{\circ\circ}=\{a:|a|<1\},\qquad
\widetilde K=K^\circ/K^{\circ\circ}.
$$

A finite extension of $K$ carries the unique extended absolute value. Whenever formal models enter, beginning in Chapter 7, $K$ is assumed discretely valued, $R=K^\circ$, and $\pi\in R$ is a uniformizer. Then $R$ is complete and $K=R[1/\pi]$. The residue field need not be finite or perfect unless a statement explicitly says so.

We use the classical strict theory: coordinate radii belong to $|K^\times|$. Closed polydiscs of arbitrary positive radii can be handled by weighted norms, and after adjoining elements having the required absolute values they reduce to the strict case. Nothing below silently assumes that $K$ is algebraically closed. A *point* of an affinoid space means a maximal ideal, whose residue field is a finite extension of $K$; geometric points over larger complete fields may be used when base change is relevant.

All rings are commutative. Analytic spaces are assumed quasi-separated when intersections or coherent descent are discussed, and formal schemes are locally noetherian and topologically of finite type over $R$ unless stated otherwise.

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
K\langle T_1,\ldots,T_n\rangle
=
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
f=a_0+h,qquad \|h\|_G<|a_0|.
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

Call $g\in K\langle T_1,\ldots,T_n\rangle$ **distinguished in $T_n$ of degree $d$** if, viewed as a series in $T_n$, its coefficient of $T_n^d$ has norm one, all higher coefficients have norm less than one, and lower coefficients have norm at most one. Then every $f$ admits unique elements

$$
q\in K\langle T_1,\ldots,T_n\rangle,qquad
r\in K\langle T_1,\ldots,T_{n-1}\rangle[T_n],quad \deg_{T_n}r<d,
$$

such that $f=qg+r$. The quotient and remainder are obtained by repeatedly canceling the leading $T_n$-term. The error norms tend to zero, so completeness supplies the limit; the distinguished inequalities prevent the process from increasing norms. Uniqueness follows by comparing the highest surviving term.

Preparation factors a distinguished series as a unit times a monic polynomial of degree $d$ whose lower coefficients lie in the smaller Tate algebra. A change of variables can make a chosen nonzero series distinguished in the last variable. Induction on $n$, followed by division, proves:

**Theorem 2.1 (Tate).** For every $n\geq0$, $K\langle T_1,\ldots,T_n\rangle$ is noetherian. Every ideal is closed for the Gauss topology, and every finite module is complete for a quotient norm.

The closedness assertion is not decorative. If an ideal were merely dense, quotienting would erase analytic information. Division supplies bounded normal forms, which show that limits of elements of an ideal remain in it.

### 2.6 Finite residue fields and the nullstellensatz

Points of an affine algebraic variety correspond to maximal ideals with finite residue extensions. The same finiteness survives analytically.

**Theorem 2.2 (analytic nullstellensatz).** If $A$ is a quotient of a Tate algebra and $\mathfrak m\subset A$ is maximal, then $A/\mathfrak m$ is a finite field extension of $K$.

**Proof strategy.** Choose the smallest number of coordinates needed to generate the residue field. If one coordinate were transcendental over those before it, analytic division and a rapidly convergent series would construct an element that cannot lie in the finitely generated quotient, contradicting maximality. Thus every coordinate is algebraic, and finite generation makes the extension finite.

The decisive point is convergence: coefficients can be chosen recursively with rapidly decreasing size, so the obstruction is an actual restricted series rather than a formal expression. The theorem implies that maximal ideals are closed and that evaluation at a point always lands in a complete valued field. It does not say every point is $K$-rational.

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
A^\circ=\{f:\{f^m:m\geq0\}\text{ is bounded}\},qquad
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
A\left\langle\frac{f_1}{f_0},\ldots,\frac{f_m}{f_0}\right\rangle
=
A\langle S_1,\ldots,S_m\rangle/
(f_0S_1-f_1,\ldots,f_0S_m-f_m).
$$

The notation is suggestive but the displayed quotient is the definition; $f_0$ need not become invertible when some $f_i$ is $1$ only after imposing the relations and using the unit-ideal identity. At a point of the quotient, $S_i$ has size at most one, so the required inequalities hold. Conversely, those ratios exist in the residue field of every point of $U$, giving a unique lifted point.

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

This property proves that the algebra depends only on the subset $U$, not on the chosen rational presentation, up to unique bounded isomorphism. It also makes rational localization compatible with base change.

### 4.3 Weierstrass and Laurent domains

Two elementary domains generate the useful examples. A **Weierstrass domain** has the form

$$
\{x:|f_i(x)|\leq1\},qquad
A\langle f_1,\ldots,f_m\rangle
=A\langle S_1,\ldots,S_m\rangle/(S_i-f_i).
$$

This notation becomes nontrivial when the bound is $|a|$: adjoining $f_i/a$ cuts out $|f_i|\leq|a|$.

A **Laurent domain** imposes both upper and lower bounds:

$$
|f_i|\leq1,qquad |g_j|\geq1.
$$

Its algebra adjoins the $f_i$ and inverses $g_j^{-1}$ as bounded coordinates. For example,

$$
\{r\leq|T|\leq1\}
=\operatorname{Sp}K\langle T,U\rangle/(TU-a),qquad |a|=r.
$$

The two closed subdomains $|T|\leq|a|$ and $|T|\geq|a|$ cover the unit disc. They are not open in the ordinary topology at the circle $|T|=|a|$, but they form an admissible cover. This is the simplest evidence that the analytic topology must be more flexible than point-set openness.

### 4.4 Flatness and transitivity

**Theorem 4.2.** If $U\subset\operatorname{Sp}A$ is a rational domain with algebra $A_U$, then $A\to A_U$ is flat. Rational localization is transitive: if $V$ is rational in $U$, then $V$ is rational in $\operatorname{Sp}A$, and its algebra is the corresponding completed base change.

**Proof strategy.** For a single Weierstrass inequality, division by the new coordinate gives normal forms and proves exactness after tensoring. A Laurent inequality is treated by the relation $gS-1$ and the same division argument. General rational domains admit finite refinements by composites of these elementary cases. Flatness descends across the finite faithfully flat comparison supplied by the refinement.

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

**Proof strategy.** A rational cover can be refined into elementary two-piece covers associated with an inequality $|f|\leq|g|$ and its reverse. For such a cover, convergent division gives the equalizer assertion and explicitly splits the higher Čech terms. Repeating this construction proves exactness for Laurent covers. A finite rational cover has a Laurent refinement, and a comparison of the two Čech complexes transfers exactness.

The decisive analytic detail is bounded division. Algebraic equality on overlaps alone would not control whether the glued series converges. The norm estimates in division give a global element of $A$, not merely an element of a completion chosen after the fact.

**Theorem 5.1 (Tate acyclicity).** The preceding Čech complex is exact for every finite admissible covering of an affinoid space by affinoid subdomains. The same is true after tensoring with any finite $A$-module.

The module statement follows by a finite presentation and flatness of rational localizations. It will turn finite modules into coherent sheaves and make higher cohomology vanish on affinoids.

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
M\longmapsto\widetilde M,qquad
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

The proof embeds suitable pieces into projective space over $Y$, resolves coherent sheaves by twists, and uses finite Čech complexes together with the projective calculation. Properness is decisive: the open unit disc has an enormous ring of global analytic functions, not a finite module over $K$.

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

More generally, formal affine opens arising from generators $f_0,\ldots,f_m$ become the rational domains $|f_i|\leq|f_0|$. Thus the odd-looking analytic inequalities are the generic shadows of ordinary affine charts on a formal blowup.

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

If $B=A_K$ and $A=B^\circ$ is an admissible ring of definition, this is the specialization map for $\operatorname{Spf}A$. For a smaller ring of definition $A\subset B^\circ$, the special fiber maps to $\operatorname{Spec}\widetilde B$, and specialization factors through it.

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
\mathfrak f_\eta^{-1}(]Z[_\mathfrak Y)=],\mathfrak f_s^{-1}(Z),[_\mathfrak X.
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
\left(A\left\langle\frac{f_0}{f_i},\ldots,\frac{f_m}{f_i}\right\rangle\right)ig/\{\pi\text{-torsion}\}.
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
\operatorname{sp}_{\mathfrak X}
=
(\mathfrak X'_s\to\mathfrak X_s)\circ\operatorname{sp}_{\mathfrak X'}.
$$

Thus the analytic space is fixed while its reduction is refined.

### 9.4 Common refinements and the model theorem

Blowup invariance has a converse strong enough to make formal models intrinsic.

**Theorem 9.2 (formal model theorem).** The generic-fiber functor induces an equivalence between:

- quasi-compact admissible formal $R$-schemes, with admissible blowups inverted; and
- quasi-compact quasi-separated rigid $K$-spaces.

In particular, every such rigid space has an admissible formal model. Two formal models of the same rigid space are dominated by a third after admissible blowups, and every analytic morphism extends to a morphism after admissibly blowing up the source.

**Proof strategy.** Choose a finite affinoid cover of the analytic space and rings of definition in the affinoid algebras. On overlaps, bounded denominators can be cleared by powers of $\pi$. Blowing up the resulting open ideals turns the analytic overlap maps into formal maps. A simultaneous refinement enforces the cocycle condition and permits gluing. For a morphism, the closure of its graph supplies the same denominator-clearing construction.

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

Let $\mathfrak C$ be a smooth formal curve over $R$, and let $z$ be a closed point of its special fiber with residue field $k(z)$. After a finite unramified extension that lifts $k(z)$ and an étale change of coordinate, a neighborhood of $z$ is formally isomorphic to $\operatorname{Spf}R'\langle T\rangle$ near $T=0$. Therefore

$$
]z[_\mathfrak C\widehat\otimes_RR'
\simeq\{x:|T(x)|<1\},
$$

the open unit disc.

The proof uses formal smoothness to lift a residue parameter through every power of $\pi$. Completeness turns the compatible lifts into a formal coordinate. The strict inequality expresses specialization to $T=0$.

This is a local statement after residue-field extension; a point with nontrivial residue field need not have a disc coordinate over $K$ itself. Its tube is a descended form of a disc. Smooth reduction decomposes a proper curve into residue discs attached to the points of its special fiber, but the family of all such discs is generally not an admissible cover when the residue field is infinite.

### 10.3 Annuli above nodes

The standard semistable node has completed local equation

$$
XY=\pi^e
$$

with $e\geq1$. Its entire affine generic fiber is the closed annulus $|\pi|^e\leq|X|\leq1$. The node itself is cut out in the special fiber by $X=Y=0$, so its tube requires

$$
|X|<1,qquad |Y|<1.
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

A **rigid analytic curve** over $K$ is a separated rigid space, locally of finite type, all of whose irreducible components have dimension one. Reducedness, smoothness, and geometric connectedness are additional hypotheses, not part of the word *curve*. This convention permits singular and nonreduced fibers to appear without changing language.

On an affinoid curve $X=\operatorname{Sp}A$, a nonconstant analytic function $t$ often gives a finite map to a disc. Algebraically this means that $A$ is finite over $K\langle t\rangle$. Near a point $x$ where $dt$ does not vanish, $t-t(x)$ is a local parameter after a finite residue-field extension. The completed local ring is then

$$
\widehat{\mathcal O}_{X,x}\simeq K(x)[[t]]
$$

in the smooth case, where completion is with respect to the maximal ideal. The formal power series describe germs; their convergence radius need not be uniform on an entire affinoid neighborhood.

Zeros of a nonzero analytic function on an affinoid smooth curve are finite. Indeed $A/(f)$ has dimension zero and is an affinoid algebra, hence an artinian $K$-algebra. On a non-affinoid curve zeros can accumulate only toward the analytic boundary. The function with infinitely many zeros on an open disc therefore does not contradict local finiteness on closed subdiscs.

### 11.2 Smooth, normal, and regular curves

A morphism $X\to\operatorname{Sp}K$ is smooth of relative dimension one if locally it admits an étale map to a disc. Equivalently, for every point $x$, the local ring is regular of dimension one and the residue extension is separable in the relevant differential criterion. Over a nonperfect field, regularity alone does not imply smoothness: purely inseparable residue phenomena must be excluded.

For a reduced analytic curve, normality is equivalent to all local rings being discrete valuation rings. Thus a normal curve is regular. Over a perfect base, a geometrically reduced normal curve is smooth; over an imperfect base one must retain geometric regularity as a separate condition.

The nodal annulus model shows another distinction. The formal total space $XY=\pi$ is regular, and its analytic generic fiber is smooth because $\pi\ne0$ there, although the special fiber is singular. Smoothness of the analytic curve does not demand smooth reduction.

Differentials detect ramification. If $f:X\to Y$ is a finite morphism of smooth curves and $t$ is a parameter at $f(x)$, then locally

$$
f^*t=u s^e
$$

up to higher terms, with $u$ a unit and $s$ a parameter at $x$. The map is étale at $x$ precisely when $e=1$ and the residue extension is separable. In positive residue characteristic, $e$ prime to the characteristic is not by itself enough unless the residue condition is also checked.

### 11.3 Finite maps and normalization

If $A\to B$ is a finite homomorphism of affinoid algebras, the induced map $\operatorname{Sp}B\to\operatorname{Sp}A$ is finite. Conversely, a finite morphism is affinoid over affinoids and arises from a finite algebra. Finite morphisms are proper, have finite fibers, and preserve affinoid domains under inverse image.

Let $X$ be a reduced affinoid curve. Its normalization is obtained by taking the integral closure $A^{\mathrm{nor}}$ of $A$ in its total ring of fractions. This algebra is finite over $A$, so

$$
X^{\mathrm{nor}}=\operatorname{Sp}A^{\mathrm{nor}}\longrightarrow X
$$

is finite. The finiteness follows from excellence of affinoid algebras. Gluing gives normalization for quasi-separated curves. It is an isomorphism over the normal locus and separates analytic branches at singular points.

For the node $A=K\langle X,Y\rangle/(XY)$, the normalization is $K\langle X\rangle\times K\langle Y\rangle$ and separates the two branches. In contrast, the annulus algebra $K\langle X,Y\rangle/(XY-a)$ with $a\ne0$ is already smooth and normal. Equations that look identical before and after setting $a=0$ have different generic geometry.

### 11.4 Boundary and wide-open curves

An affinoid curve behaves like a compact curve with finitely many boundary directions. A **wide-open curve** is, in the situations needed here, a smooth rigid curve obtained from a smooth proper curve by removing finitely many disjoint closed discs. Equivalently, it admits an exhaustion whose complement consists of finitely many annular ends. The precise equivalence assumes the curve is quasi-smooth and has finitely many ends.

Open discs and open annuli are not affinoid. Each is an increasing union of closed affinoids, and analytic functions must converge on every member of the exhaustion. Boundary explains why their function rings are much larger than finite-type algebras.

The distinction between removing points and removing discs is characteristically nonarchimedean. Removing one algebraic point from a proper curve leaves a punctured neighborhood modeled on an annulus with inner radius tending to zero. Removing a closed residue disc leaves an actual annular boundary of positive modulus. Formal models see the latter as deleting a component or a tube, while algebraic open curves naturally produce the former.

## 12. Proper rigid curves

### 12.1 The valuative meaning of properness

Properness is the condition that eliminates analytic boundary. A separated rigid space $X$ is proper over $K$ if it is quasi-compact and universally closed in the analytic sense; equivalently in the finite-type setting, maps from punctured valuation discs extend uniquely across the missing center after every complete extension.

For curves, this criterion has a concrete interpretation. An affinoid or wide-open end supplies a bounded parameter tending toward a missing boundary point, so the associated punctured-disc map fails to extend inside the space. Conversely, a quasi-compact smooth curve with no boundary admits a proper formal model and satisfies the extension property.

Properness is stable under finite extension of $K$, composition, and closed immersion. A finite morphism is proper. The analytic affine line and every nonempty affinoid curve of positive dimension are not proper: a positive-dimensional space cannot be both affinoid and proper over $K$, because properness makes global functions algebraic over $K$, whereas a reduced affinoid curve has a transcendental function.

The last claim can be made exact. If $X$ is connected and proper, then $H^0(X,\mathcal O_X)$ is a finite field extension of $K$ when $X$ is reduced. If it is geometrically connected and geometrically reduced, the global functions are exactly $K$. Thus a nonconstant global analytic function on a proper geometrically connected smooth curve cannot exist.

### 12.2 Finite-dimensional cohomology

Let $X$ be a proper rigid curve and $\mathcal F$ coherent. The proper mapping theorem gives

$$
\dim_KH^0(X,\mathcal F)<\infty,qquad
\dim_KH^1(X,\mathcal F)<\infty,qquad
H^q(X,\mathcal F)=0\quad(q\geq2).
$$

The vanishing follows from the one-dimensional affinoid cover and its Čech complex; finiteness uses properness. If $\mathcal L$ is an invertible sheaf of sufficiently large degree, then $H^1(X,\mathcal L)=0$ and its global sections generate it. The proof may be transported from the algebraic curve after algebraization, or obtained analytically by successively allowing poles at a finite divisor.

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

Properness and coherence are essential; global functions on an open disc do not arise by a finite-dimensional scalar extension.

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

**Proof strategy.** First normalize, reducing to a disjoint union of smooth curves after controlling finite singular data. Choose a finite nonempty divisor $D$. For sufficiently large $n$, proper cohomology and one-dimensional vanishing make $\mathcal O_X(nD)$ globally generated and separate points and tangent directions. Its sections embed $X$ as a closed analytic subspace of projective space. Proper projective comparison algebraizes the coherent ideal of the image. Singular curves are recovered by descending the finite conductor diagram from the normalization.

The decisive steps are finiteness of cohomology, which supplies finitely many projective coordinates, and properness, which makes the analytic closed subspace of projective space algebraic. Uniqueness follows because analytic morphisms between proper algebraic curves are algebraic.

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

### 13.3 Semistable formal curves

A proper admissible formal curve $\mathfrak C/R$ is **semistable** if its special fiber is reduced, its irreducible components are smooth away from ordinary double points, and étale-locally at every node the formal equation is

$$
XY=\pi^e
$$

for some $e\geq1$. If every $e=1$, the total space is regular at the nodes. Marked sections are required to lie in the smooth locus and remain disjoint.

**Semistable model theorem for curves.** Let $C/K$ be a smooth proper geometrically connected curve. After a finite separable extension $K'/K$, the curve $C_{K'}$ admits a proper semistable formal model over $R'$. If $C$ has genus at least two, contracting unstable rational components gives a stable model, unique after the extension; any two semistable models are dominated by a common semistable refinement.

The theorem requires finite extension: an elliptic curve with additive reduction need not have semistable reduction over $K$. Separability is enough; no perfection of the residue field is silently used, though geometric descriptions of components are cleanest after residue extension.

The proof proceeds by taking a regular proper model, resolving singularities, and modifying the special fiber until it has normal crossings; a finite extension removes multiplicities. In dimension two, blowups and normalization keep this process within proper models. Stability then contracts exactly the rational components meeting the rest and the markings in fewer than three points, with the genus-one analogue requiring at least one marked or attaching point.

### 13.4 Components, annuli, and the reduction graph

Let $\mathfrak C$ be semistable. The smooth locus of each irreducible component of $\mathfrak C_s$ has a tube built from residue discs. Every node contributes an open annulus. These pieces form an admissible covering after finitely many affinoid neighborhoods are grouped appropriately:

$$
C^{\mathrm{an}}
=
\bigcup_v ]C_v^\circ[\;\cup\;
\bigcup_e ]z_e[.
$$

The **reduction graph** has a vertex for each irreducible component and an edge for each node, joining the components containing its two branches; a self-node gives a loop. The thickness $e$ of $XY=\pi^e$ supplies an edge length proportional to $e$. Blowing up a node subdivides an edge without changing the underlying analytic curve. Thus the metric realization is model-independent after suppressing valence-two vertices introduced by refinement.

This graph is not the curve. Each vertex carries the smooth projective normalization of a residue component, and the tubes attached to it contain infinitely many analytic points. Nevertheless it records how annuli connect the good-reduction pieces and controls the first Betti contribution of degeneration:

$$
g(C)=\sum_v g(C_v)+b_1(\Gamma)
$$

for a split semistable model with geometrically irreducible components, with the appropriate geometric interpretation after extending the residue field. The formula follows from the normalization exact sequence of the nodal special fiber and constancy of arithmetic genus in a proper flat family.

Good reduction is the special case of one smooth component and no edges. A curve may have a tree-shaped graph and still have bad reduction because its components or attaching data differ from a single smooth fiber. The graph detects nodes, not every arithmetic defect.

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

For a proper flat algebraic model $\mathcal C/R$, this theorem is compatible with formal completion:

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

If $C$ is proper and $Y$ is a separated finite-type algebraic $K$-scheme, every analytic morphism

$$
C^{\mathrm{an}}\longrightarrow Y^{\mathrm{an}}
$$

comes from a unique algebraic morphism $C\to Y$. Embed $Y$ locally into affine or projective space; the graph is a closed analytic subspace of the proper source times a compactification, and its coherent ideal algebraizes. Separatedness ensures the algebraic graph lands in $Y$ rather than identifying distinct limits.

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

is analytic and is not a polynomial. Thus $H^0(\mathbf A^1_K,\mathcal O)$ and analytic functions on bounded subdomains cannot be identified term by term without specifying the domain. On the entire analytic affine line, global analytic functions are series converging on every closed disc; they still need not be polynomials when the valuation is nontrivial.

Analytic domains also need not be algebraic opens. A closed annulus inside the multiplicative line is cut out by absolute-value inequalities, not by nonvanishing of polynomials. Its two boundary circles have no algebraic-open analogue.

Formal completion can fail to recover a nonproper analytification. Completing $\mathbf A^1_R$ gives only the closed unit disc. Completing $\mathbf G_{m,R}$ gives the unit circle $|T|=1$. Properness is what forces every generic point to acquire a center on the special fiber and makes completion exhaustive.

Finally, a special fiber is not an invariant of the analytic curve. Admissible blowups can add components and subdivide nodes while preserving the generic fiber. Only statements stable under common refinement—such as the existence of semistable reduction, the resulting metric graph up to subdivision, or tubes viewed through the induced analytic isomorphism—are intrinsic.

## 15. A reusable dictionary

### 15.1 Hypothesis ledger

The main results of the book can be used safely by keeping their hypotheses visible.

**Analytic algebras.** The base field is complete, nontrivially valued, and nonarchimedean. Strict affinoid algebras use radii in $|K^\times|$. Tate algebras and their affinoid quotients are noetherian; maximal residue fields are finite over $K$. The spectral seminorm is a norm only after removing nilpotents.

**Localization and sheaves.** Rational domains require numerators together with the denominator to generate the unit ideal. Rational localization is flat, not necessarily faithfully flat. Faithfulness comes from a finite cover. Tate acyclicity concerns admissible finite affinoid covers and finite modules. Coherent descent on general spaces uses quasi-separatedness.

**Formal models.** The formal chapters assume a complete discrete valuation ring $R$ with fraction field $K$. Admissible formal schemes are topologically of finite type and $R$-flat. A formal blowup preserves the generic fiber only when its center is open, equivalently supported on the special fiber. Generic fibers forget $\pi$-torsion.

**Reduction and tubes.** Specialization sends maximal analytic points to scheme points by reduction of bounded values. It is naturally surjective onto closed points in the finite-type setting, not asserted onto every nonclosed point at this level. Tubes depend on reduced strata and are often non-affinoid. Their descriptions by discs and annuli may require finite residue-field extension or étale coordinates.

**Curves.** Normality, regularity, and smoothness coincide only under the stated separability or perfection assumptions. A proper reduced rigid curve is algebraizable; smooth proper curves are projective. Proper comparison applies to coherent sheaves and cohomology. Semistable reduction may require a finite separable extension of $K$.

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

Nonarchimedean analytic geometry begins with a small convergence condition: coefficients of a restricted series tend to zero. From it follow multiplicative norms, division, noetherianity, and finite residue fields. Rational localization then turns absolute-value inequalities into coordinate rings. Tate acyclicity identifies exactly which covers permit functions and finite modules to glue, producing rigid spaces and coherent sheaves.

Formal geometry explains the shape of that analytic topology. Integral coordinates reduce to a special fiber; inverting the uniformizer produces the generic fiber; formal blowup charts become rational domains. Specialization gathers analytic points into tubes. Above a smooth point lies a disc, above a node an annulus, and a semistable proper curve is assembled from these pieces according to its reduction graph.

Properness closes every analytic end. It makes coherent cohomology finite, forces divisors to balance, and supplies enough global sections for projective embedding. Consequently a proper rigid curve returns uniquely to algebraic geometry, with its coherent sheaves, maps, finite covers, functions, divisors, and cohomology unchanged. What remains distinctively analytic is not a rival class of proper curves, but a precise language for their bounded regions and reduction. Formal models provide that language, and admissible blowups ensure that its conclusions do not depend on how the integral picture was drawn.
