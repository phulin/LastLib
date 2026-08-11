# Divisors, Riemann--Roch, and Duality on Relative Curves

## Contents

1. [Curves and the questions divisors answer](#1-curves-and-the-questions-divisors-answer)
   - [The absolute and relative settings](#11-the-absolute-and-relative-settings)
   - [Dimension one as a meeting point](#12-dimension-one-as-a-meeting-point)
   - [Standing conventions and hypotheses](#13-standing-conventions-and-hypotheses)
2. [Cartier divisors](#2-cartier-divisors)
   - [Local equations modulo units](#21-local-equations-modulo-units)
   - [Effective Cartier divisors](#22-effective-cartier-divisors)
   - [Pullback, restriction, and flatness](#23-pullback-restriction-and-flatness)
   - [Orders along a curve](#24-orders-along-a-curve)
3. [Weil divisors and regularity](#3-weil-divisors-and-regularity)
   - [Codimension-one cycles](#31-codimension-one-cycles)
   - [From Cartier to Weil](#32-from-cartier-to-weil)
   - [Normal curves and regular models](#33-normal-curves-and-regular-models)
   - [Where the dictionaries fail](#34-where-the-dictionaries-fail)
4. [Line bundles, rational sections, and Picard groups](#4-line-bundles-rational-sections-and-picard-groups)
   - [The bundle attached to a divisor](#41-the-bundle-attached-to-a-divisor)
   - [Rational sections recover divisors](#42-rational-sections-recover-divisors)
   - [Principal divisors and linear equivalence](#43-principal-divisors-and-linear-equivalence)
   - [The divisor--Picard correspondence](#44-the-divisor--picard-correspondence)
5. [Degree and intersection with fibers](#5-degree-and-intersection-with-fibers)
   - [Degree over a field](#51-degree-over-a-field)
   - [Euler characteristic and degree](#52-euler-characteristic-and-degree)
   - [Degree in a proper flat family](#53-degree-in-a-proper-flat-family)
   - [Horizontal divisors and fibers](#54-horizontal-divisors-and-fibers)
6. [Effective relative divisors and symmetric powers](#6-effective-relative-divisors-and-symmetric-powers)
   - [The correct relative notion](#61-the-correct-relative-notion)
   - [Smooth curves turn points into divisors](#62-smooth-curves-turn-points-into-divisors)
   - [Universal divisors and addition](#63-universal-divisors-and-addition)
   - [Nodal fibers and the boundary](#64-nodal-fibers-and-the-boundary)
7. [Differentials on curves](#7-differentials-on-curves)
   - [Kähler differentials and local parameters](#71-kähler-differentials-and-local-parameters)
   - [Canonical divisors on smooth curves](#72-canonical-divisors-on-smooth-curves)
   - [Differentials at singular points](#73-differentials-at-singular-points)
8. [Residues](#8-residues)
   - [The local residue](#81-the-local-residue)
   - [Independence of parameter](#82-independence-of-parameter)
   - [The global residue theorem](#83-the-global-residue-theorem)
   - [Finite maps and trace](#84-finite-maps-and-trace)
9. [Dualizing sheaves](#9-dualizing-sheaves)
   - [Why ordinary differentials are not enough](#91-why-ordinary-differentials-are-not-enough)
   - [Dualizing sheaves on proper curves](#92-dualizing-sheaves-on-proper-curves)
   - [The relative dualizing sheaf](#93-the-relative-dualizing-sheaf)
   - [Smooth and Gorenstein families](#94-smooth-and-gorenstein-families)
10. [Nodes, normalization, and opposite residues](#10-nodes-normalization-and-opposite-residues)
    - [The local node](#101-the-local-node)
    - [Functions under normalization](#102-functions-under-normalization)
    - [Rosenlicht differentials](#103-rosenlicht-differentials)
    - [Families of nodal curves](#104-families-of-nodal-curves)
11. [Riemann--Roch over a field](#11-riemann--roch-over-a-field)
    - [The theorem and its meaning](#111-the-theorem-and-its-meaning)
    - [Proof by adding points](#112-proof-by-adding-points)
    - [Consequences and examples](#113-consequences-and-examples)
    - [Gorenstein and nodal curves](#114-gorenstein-and-nodal-curves)
12. [Serre duality](#12-serre-duality)
    - [The residue pairing](#121-the-residue-pairing)
    - [Perfectness](#122-perfectness)
    - [Duality for line bundles and vector bundles](#123-duality-for-line-bundles-and-vector-bundles)
    - [Functoriality](#124-functoriality)
13. [Relative Riemann--Roch and cohomology in families](#13-relative-riemann--roch-and-cohomology-in-families)
    - [A two-term model](#131-a-two-term-model)
    - [Semicontinuity and base change](#132-semicontinuity-and-base-change)
    - [Relative Riemann--Roch](#133-relative-riemann--roch)
    - [Useful vanishing ranges](#134-useful-vanishing-ranges)
14. [Relative duality and base change](#14-relative-duality-and-base-change)
    - [Trace and the relative pairing](#141-trace-and-the-relative-pairing)
    - [The base-change theorem](#142-the-base-change-theorem)
    - [The Hodge bundle in smooth and nodal families](#143-the-hodge-bundle-in-smooth-and-nodal-families)
    - [Failure modes](#144-failure-modes)
15. [Divisor and differential tools for later geometry](#15-divisor-and-differential-tools-for-later-geometry)
    - [Abel maps before the Picard scheme](#151-abel-maps-before-the-picard-scheme)
    - [The infinitesimal Abel map](#152-the-infinitesimal-abel-map)
    - [A formal-immersion criterion](#153-a-formal-immersion-criterion)
    - [A reusable theorem package](#154-a-reusable-theorem-package)
    - [Conclusion](#155-conclusion)

## 1. Curves and the questions divisors answer

### 1.1 The absolute and relative settings

A function on a curve carries two kinds of information. Away from finitely many points it is a unit; at the exceptional points it has zeros or poles, each with an integer order. A differential carries similar local information, but its coefficient of $dt/t$ survives every change of parameter and produces a residue. Divisor theory extracts the first pattern, while duality explains why the second pattern controls global cohomology.

The relative problem is subtler. If a curve varies over a base $S$, a point of one fiber need not extend to a section, and a closed subscheme of constant length can collide or acquire nilpotents. Degrees should nevertheless remain constant in a flat proper family. Spaces of functions and differentials may jump, yet their Euler characteristic should not. At a nodal specialization the sheaf of ordinary differentials develops torsion, while the differentials relevant to duality remain well behaved.

This book develops one language that survives all these changes. Its central objects are

$$
\text{divisors}\longleftrightarrow\text{line bundles},
\qquad
\text{residues}\longleftrightarrow\text{duality},
$$

and its central numerical identity is Riemann--Roch. Book 8 constructed projective families, Hilbert polynomials, finite flat length-$d$ subschemes, and symmetric powers. We now explain why those parameter spaces are divisor spaces and how their infinitesimal geometry is read by differentials.

### 1.2 Dimension one as a meeting point

Codimension one is where a single equation ought to define a subspace. On a regular curve every closed point has codimension one and its local ring is a discrete valuation ring. Thus an integer at each closed point is simultaneously a cycle, a collection of local equations, and a prescription for allowing poles. This coincidence is special. On a singular curve a codimension-one cycle need not be locally principal; on a higher-dimensional normal space a codimension-one prime can fail to be Cartier.

Dimension one also forces coherent cohomology into degrees $0$ and $1$. A proper curve has no higher coherent cohomology. Consequently an Euler characteristic is a difference of two dimensions, and duality can exchange the two. These elementary-looking facts are the reason the theory is both computable and powerful.

There is also a useful tension between local and global reasoning. Orders of vanishing, Cartier equations, and residues are checked in one-dimensional local rings. Degree, linear equivalence, and the existence of a differential with prescribed poles are global matters. Completeness is what joins the two scales: on an affine curve a rational function may have one uncompensated pole at the missing boundary, whereas on a proper curve every local contribution participates in a global balance. Throughout the book, exact sequences are the mechanism that makes this passage visible. Their quotient terms are supported at finitely many points, so a global change can be measured by a finite sum of local lengths or residues.

The relative dimension-one condition retains this two-term character. Locally on a noetherian base, the cohomology of a line bundle in a proper flat family can be represented by a map between two finite free modules. Kernels may jump, cokernels may jump, but their rank difference does not. This is the algebra beneath semicontinuity, base change, and relative Riemann--Roch.

### 1.3 Standing conventions and hypotheses

A **proper curve over a field** $k$ means a proper $k$-scheme of finite type, pure of dimension one. When integrality, reducedness, geometric connectedness, smoothness, or the Gorenstein property is needed, it will be stated. For a field extension $K/k$, write $X_K=X\times_k K$.

A **relative curve** is a proper, flat, finitely presented morphism

$$
f:X\longrightarrow S
$$

whose geometric fibers are pure of dimension one. We generally assume $S$ locally noetherian when using finiteness or duality. A smooth relative curve has smooth geometric fibers. A nodal relative curve is a relative curve whose geometric fibers are reduced and have only ordinary double points; for the strongest relative statements we additionally require the morphism to be Gorenstein. Standard nodal families, locally cut out by one equation in a smooth surface over $S$, are Gorenstein.

For a coherent sheaf $\mathcal F$ on a proper $k$-curve,

$$
h^i(X,\mathcal F)=\dim_k H^i(X,\mathcal F),
\qquad
\chi(X,\mathcal F)=h^0(X,\mathcal F)-h^1(X,\mathcal F).
$$

If $X$ is geometrically connected and proper over $k$, then $H^0(X,\mathcal O_X)=k$ when $X$ is geometrically reduced. Its arithmetic genus is

$$
p_a(X)=1-\chi(X,\mathcal O_X)=h^1(X,\mathcal O_X).
$$

No algebraic closure is silently assumed. Degrees of closed points always include residue-field degrees.

We use the elementary noetherian facts that a one-dimensional normal local domain is a discrete
valuation ring, that a regular local ring is factorial, and that coherent cohomology on a proper
curve is finite-dimensional and vanishes above degree one. Valuations are normalized by
$\operatorname{ord}_x(t)=1$, and finite local lengths are module lengths. The substantial
projective inputs are the results of Book 8: Serre vanishing, polynomiality and constancy of Euler
characteristics in flat projective families, and the universal-divisor description of symmetric
powers of smooth relative curves.
Whenever a relative statement needs projectivity rather than properness alone, that hypothesis is
stated in the theorem.

## 2. Cartier divisors

### 2.1 Local equations modulo units

A zero of a function is not determined by the function: multiplying by a nowhere-vanishing function changes no zero or multiplicity. This suggests recording local meromorphic equations only modulo regular units.

Let $X$ be a locally noetherian scheme. Its sheaf of total quotient rings $\mathcal K_X$ is obtained on each open set by inverting regular elements, meaning non-zero-divisors. A **Cartier divisor** is a global section of

$$
\mathcal K_X^\times/\mathcal O_X^\times.
$$

Concretely it is an open cover $X=\bigcup U_i$ with $f_i\in\mathcal K_X^\times(U_i)$ such that $f_i/f_j\in\mathcal O_X^\times(U_i\cap U_j)$. Addition multiplies equations, the negative replaces each equation by its inverse, and zero is represented by units.

This definition works on reducible and nonreduced schemes because regular elements, rather than merely nonzero elements, are inverted. On an integral scheme $\mathcal K_X$ is the constant sheaf of the function field. On a reduced scheme with finitely many irreducible components, it is generically a product of their function fields.

The support of a Cartier divisor $D$ is the locus where no local equation is a unit. It is closed when $X$ is noetherian. A Cartier divisor may have positive and negative parts only under additional hypotheses; the definition itself is signed local data, not a closed subscheme.

### 2.2 Effective Cartier divisors

A Cartier divisor $D$ is **effective** if it has local equations $f_i\in\mathcal O_X(U_i)$ that are regular elements. Then the ideals $(f_i)$ agree on overlaps and define an invertible ideal sheaf

$$
\mathcal I_D=\mathcal O_X(-D)\subseteq\mathcal O_X.
$$

The associated closed subscheme has structure sheaf fitting into

$$
0\longrightarrow\mathcal O_X(-D)
\longrightarrow\mathcal O_X
\longrightarrow\mathcal O_D
\longrightarrow0. \tag{2.1}
$$

Conversely, a closed subscheme whose ideal is locally generated by one regular element is an effective Cartier divisor. The regular-element condition is decisive: if $f$ is a zero-divisor, multiplication by $f$ is not injective, (2.1) is not exact on the left, and the putative hypersurface can contain an entire component.

For example, on $X=\operatorname{Spec}k[x,y]/(xy)$, the function $x$ vanishes on one irreducible component and is a zero-divisor. Its zero scheme is not an effective Cartier divisor. The function $x+y$, however, avoids both minimal primes and does define one.

If $D$ and $E$ are effective Cartier divisors, their sum is defined by $\mathcal I_D\mathcal I_E$. Multiplicities are built in: $nD$ has local equation $f^n$. Scheme structure is therefore essential even when the support is a single point.

### 2.3 Pullback, restriction, and flatness

Given $g:Y\to X$, one would like to pull back local equations of $D$. This is possible precisely when every pulled-back equation remains a regular element of $\mathcal O_Y$. In particular, flat morphisms preserve regular elements, so every Cartier divisor pulls back along a flat morphism. An arbitrary morphism can fail: pulling a divisor back along a map whose image lies inside its support turns its equation into zero.

If $D$ is effective and $g$ is flat, then

$$
0\to\mathcal O_Y(-g^*D)\to\mathcal O_Y\to\mathcal O_{D\times_XY}\to0
$$

is the pullback of (2.1). Thus effective Cartier divisors commute with flat base change as closed subschemes.

A useful refinement concerns a relative curve $X\to S$. Suppose $D\subset X$ is an effective Cartier divisor and $D\to S$ is flat. For every $s\in S$, the fiber $D_s$ is an effective Cartier divisor on $X_s$: tensoring (2.1) with $\kappa(s)$ preserves injectivity. Without flatness of $D$ over $S$, the equation may become a zero-divisor or even zero on a special fiber. The divisor cut out by a parameter of the base is the simplest warning: it is Cartier on $X$ but contains a whole fiber and is not a divisor on that fiber.

### 2.4 Orders along a curve

Let $X$ be a regular integral noetherian curve and $x$ a closed point. The local ring $\mathcal O_{X,x}$ is a discrete valuation ring. Its normalized valuation

$$
\operatorname{ord}_x:k(X)^\times\longrightarrow\mathbf Z
$$

measures the exponent of a uniformizer. For a Cartier divisor represented near $x$ by $f$, define $\operatorname{ord}_x(D)=\operatorname{ord}_x(f)$. A unit changes this by zero.

Only finitely many orders are nonzero. Indeed the support is closed and omits the generic point; on a noetherian one-dimensional scheme it is a finite set. Thus

$$
D=\sum_{x\in X^{(1)}}\operatorname{ord}_x(D)[x].
$$

If $f\in k(X)^\times$, its **principal divisor** is

$$
\operatorname{div}(f)=\sum_x\operatorname{ord}_x(f)[x].
$$

The valuation law immediately gives $\operatorname{div}(fg)=\operatorname{div}(f)+\operatorname{div}(g)$. This innocent identity is the algebraic source of linear equivalence.

## 3. Weil divisors and regularity

### 3.1 Codimension-one cycles

Local equations are excellent for tensor products and pullback, but sometimes one first sees only irreducible subspaces with multiplicities. On a noetherian scheme $X$, a **prime divisor** is an integral closed subscheme of codimension one. A **Weil divisor** is a finite formal sum

$$
Z=\sum_{\xi\in X^{(1)}}n_\xi[\overline{\{\xi\}}],
\qquad n_\xi\in\mathbf Z.
$$

Here $X^{(1)}$ denotes codimension-one points. Effectivity means $n_\xi\geq0$. Weil divisors remember generic multiplicity along codimension-one components but generally forget embedded points and detailed scheme structure.

If $X$ is normal and integral, every local ring at a codimension-one point is a discrete valuation ring. Hence a rational function has a well-defined order there, and

$$
\operatorname{div}(f)=\sum_{\xi\in X^{(1)}}\operatorname{ord}_\xi(f)[\overline{\{\xi\}}].
$$

Finiteness follows by writing $f=a/b$ on an affine open and using that a noetherian ring has only finitely many minimal primes over $(a)$ and $(b)$.

### 3.2 From Cartier to Weil

On a normal integral noetherian scheme, a Cartier divisor $D$ determines a Weil divisor by taking the valuation of a local equation at each codimension-one point. This gives a homomorphism

$$
\operatorname{CaDiv}(X)\longrightarrow\operatorname{Div}(X).
$$

It is injective if $X$ is locally noetherian, normal, and integral. The key fact is the intersection description

$$
\mathcal O_X(U)=\bigcap_{\xi\in U^{(1)}}\mathcal O_{X,\xi}
\quad\text{inside }k(X)
$$

for every open $U$: a rational function with no codimension-one zero or pole is a unit after applying the statement to it and its inverse. Normality is doing real work here; codimension-two defects would otherwise be invisible to valuations.

Surjectivity is equivalent to local factoriality. A prime divisor is Cartier exactly when its height-one prime ideal becomes principal locally. Regular noetherian local rings are factorial, so on a regular noetherian integral scheme every Weil divisor is Cartier. The inverse is constructed by choosing a local generator for each height-one prime and multiplying powers.

### 3.3 Normal curves and regular models

For a noetherian integral curve, normality and regularity are equivalent. Indeed every non-generic local ring has dimension one; a one-dimensional noetherian normal local domain is a discrete valuation ring and hence regular. Therefore on a normal integral curve

$$
\operatorname{CaDiv}(X)\simeq\operatorname{Div}(X).
$$

This is the cleanest divisor dictionary in the book. It applies to smooth curves over any field, because smoothness implies regularity. It also applies to regular total spaces of relative curves, even when the total space is a surface or higher-dimensional: regularity makes every codimension-one cycle Cartier.

There is a particularly useful picture over a Dedekind scheme. Let $S$ be integral, regular, noetherian, and one-dimensional, and let $X\to S$ be an integral normal proper flat relative curve. Every prime divisor on the surface $X$ is of one of two kinds. A **horizontal** prime dominates $S$; it is the closure of a closed point of the generic fiber. It is proper and quasi-finite over $S$, hence finite, and its integral coordinate algebra is torsion-free over the Dedekind base, hence flat. Its finite-flat rank is its degree over the generic fiber. A **vertical** prime is an irreducible component of a closed fiber. Normality supplies an order valuation at either kind of prime, so rational functions have horizontal and vertical orders simultaneously.

If $X$ is regular, every such prime is Cartier. If $X$ is only normal, its Weil divisor is still defined but need not be locally principal at closed points of the surface. Horizontal degree can be read by intersecting with a fiber, while vertical components require a component pairing and self-intersection theory not yet available. This separation prevents two common mistakes: treating an entire fiber component as a divisor on that same fiber, and assuming that normality of a surface makes every horizontal closure Cartier.

There is an important distinction between regular and smooth over an imperfect field. A regular curve can fail to be smooth after a purely inseparable field extension. Its divisor theory is still controlled by discrete valuation rings, but statements involving geometric fibers or ordinary differentials require the stronger smoothness hypothesis.

### 3.4 Where the dictionaries fail

On the nodal affine curve $xy=0$, each component is a codimension-zero component, while the node is codimension one but its local ring is not a domain. Weil divisors in the normal-integral sense are unavailable, although Cartier divisors and dualizing differentials remain meaningful.

On the integral cusp $y^2=x^3$, the singular point defines a Weil divisor but its maximal ideal $(x,y)$ is not principal in the local ring. Thus the point is not an effective Cartier divisor. After normalization $x=t^2$, $y=t^3$, the inverse image is the Cartier point $t=0$, but descending it loses information. This explains why symmetric powers classify relative effective Cartier divisors on smooth curves, not on arbitrary singular curves.

In dimension at least two, normality alone also does not suffice. A normal surface may possess a nontrivial divisor class group, so a height-one prime can be Weil without being Cartier. Later intersection theory must therefore state regularity or a suitable Cartier hypothesis rather than silently converting cycles into equations.

## 4. Line bundles, rational sections, and Picard groups

### 4.1 The bundle attached to a divisor

Let $D$ have local equations $f_i$. The ratios $f_i/f_j$ are units and hence transition functions. Define the invertible subsheaf of $\mathcal K_X$

$$
\mathcal O_X(D)(U)=
\{g\in\mathcal K_X(U): gf_i\in\mathcal O_X(U\cap U_i)\text{ for every }i\}.
$$

Locally it is generated by $f_i^{-1}$. Its dual is $\mathcal O_X(-D)$, and multiplication gives

$$
\mathcal O_X(D+E)\simeq
\mathcal O_X(D)\otimes\mathcal O_X(E).
$$

If $D$ is effective, $\mathcal O_X(-D)$ is its ideal and the constant rational function $1$ is a regular section of $\mathcal O_X(D)$ vanishing exactly along $D$. This apparent reversal of signs is worth remembering: allowing a pole along $D$ produces $\mathcal O(D)$, while functions forced to vanish along $D$ form $\mathcal O(-D)$.

On a regular integral curve the description becomes

$$
\mathcal O_X(D)(U)=
\{g\in k(X):\operatorname{ord}_x(g)+n_x\geq0
\text{ for all }x\in U\}.
$$

Thus $H^0(X,\mathcal O_X(D))$ is the space of rational functions whose poles are bounded by $D$.

### 4.2 Rational sections recover divisors

Let $X$ be integral and $\mathcal L$ a line bundle. A nonzero **rational section** is a generator of the one-dimensional $k(X)$-space $\mathcal L_\eta$ at the generic point. Trivialize $\mathcal L$ on $U_i$ by $e_i$ and write $s=f_i e_i$. The ratios of the $f_i$ differ by the inverse transition functions, hence define a Cartier divisor $\operatorname{div}(s)$.

There is a canonical isomorphism

$$
\mathcal O_X(\operatorname{div}(s))\simeq\mathcal L
$$

carrying the canonical rational section to $s$. On a reduced scheme with several components, the same construction works for a rational section that is a basis at every generic point. A line bundle need not possess such a section on a scheme with infinitely many components, but on a noetherian scheme one chooses local generators at finitely many generic points and clears denominators.

A regular section $s\in H^0(X,\mathcal L)$ defines an effective Cartier divisor precisely when multiplication

$$
\mathcal L^{-1}\xrightarrow{s}\mathcal O_X
$$

is injective, equivalently when $s$ is regular at every associated point. On an integral scheme every nonzero section has this property. On a reducible curve, a section vanishing identically on one component does not.

### 4.3 Principal divisors and linear equivalence

Two Cartier divisors are **linearly equivalent**, written $D\sim E$, if

$$
D-E=\operatorname{div}(f)
$$

for a global rational unit $f$. Multiplication by $f$ gives $\mathcal O_X(D)\simeq\mathcal O_X(E)$. Conversely, an isomorphism between these line bundles compares their canonical rational sections and produces such an $f$. Hence linear equivalence is exactly the equivalence relation that forgets a chosen rational trivialization while retaining the line bundle.

For a proper integral curve over a field, every global regular unit is constant if the curve is geometrically connected and reduced. Principal divisors therefore remember nonconstant rational functions, not arbitrary global regular functions. Their total degree will be zero; geometrically, zeros and poles balance on a complete curve.

### 4.4 The divisor--Picard correspondence

The Picard group $\operatorname{Pic}(X)$ is the group of isomorphism classes of line bundles under tensor product. The preceding construction gives

$$
\operatorname{CaDiv}(X)/\operatorname{Prin}(X)
\longrightarrow\operatorname{Pic}(X). \tag{4.1}
$$

If every line bundle has a rational section that generates it at all associated points, (4.1) is an isomorphism. This holds for integral noetherian schemes and, more generally, for many noetherian schemes without embedded associated points. For a regular integral curve it yields the familiar identity

$$
\operatorname{Pic}(X)\simeq
\operatorname{Div}(X)/\{\operatorname{div}(f):f\in k(X)^\times\}.
$$

On a relative curve the distinction between absolute and relative Picard information matters. Tensoring by $f^*\mathcal M$ for a line bundle $\mathcal M$ on $S$ changes the line bundle on $X$ but not its class after restricting to any fiber. The relative Picard functor will eventually quotient by these pullbacks. For now, divisor constructions are made on every base change $X_T$ and are compatible with further base change; this functorial viewpoint is enough to prepare that theory without assuming its representability.

## 5. Degree and intersection with fibers

### 5.1 Degree over a field

Let $X$ be a proper regular integral curve over $k$. For

$$
D=\sum_x n_x[x],
$$

define

$$
\deg_k D=\sum_x n_x[\kappa(x):k]. \tag{5.1}
$$

The residue-field factor makes degree invariant under extending scalars and then summing geometric points with multiplicity. A $k$-rational point has degree one; a closed point cut out by an irreducible polynomial of degree $r$ on $\mathbf P^1_k$ has degree $r$.

Principal divisors have degree zero. A constant function is immediate. A nonconstant $f$ gives a
finite morphism $X\to\mathbf P^1_k$: properness makes the quasi-finite rational-function map
finite. Its direct image is torsion-free over every local discrete valuation ring of
$\mathbf P^1$, hence is flat. The zero and pole divisors are the fibers over $0$ and $\infty$,
and finite flat fibers have the same length. If $f$ is inseparable, length still records
inseparable multiplicity, so no separability assumption is needed. Consequently degree descends
to $\operatorname{Pic}(X)$.

For a possibly singular proper curve, define the degree of a line bundle by

$$
\deg\mathcal L=\chi(X,\mathcal L)-\chi(X,\mathcal O_X). \tag{5.2}
$$

On a regular integral curve this agrees with (5.1). Formula (5.2) is especially robust on reducible and nodal curves, where a line bundle has a multidegree on components but also a well-defined total degree.

### 5.2 Euler characteristic and degree

The equality between (5.1) and (5.2) begins with one effective point. For an effective Cartier divisor $D$ on a proper curve, tensoring (2.1) by $\mathcal O_X(D)$ gives

$$
0\longrightarrow\mathcal O_X
\longrightarrow\mathcal O_X(D)
\longrightarrow\mathcal O_D(D)
\longrightarrow0. \tag{5.3}
$$

Since $D$ is zero-dimensional, it has no $H^1$, and its Euler characteristic is the $k$-dimension of its global sections. Locally an effective divisor $n[x]$ has length $n$ over $\mathcal O_{X,x}$, so

$$
\chi(\mathcal O_X(D))-\chi(\mathcal O_X)=\deg D.
$$

Differences of effective divisors give the general case. On a proper Cohen--Macaulay curve, every
line bundle has a rational section generating it at all associated points, because there are no
embedded associated points. Its divisor represents the bundle. After adding a sufficiently
positive effective Cartier divisor, that divisor becomes a difference of effective Cartier
divisors, so the same length calculation applies. It also proves additivity:

$$
\deg(\mathcal L\otimes\mathcal M)
=\deg\mathcal L+\deg\mathcal M
$$

for all line bundles on such a curve. Thus the Euler-characteristic definition is a homomorphism
$\operatorname{Pic}(X)\to\mathbf Z$, not merely a numerical convention.

### 5.3 Degree in a proper flat family

Let $f:X\to S$ be a projective flat relative curve and $\mathcal L$ a line bundle. Define

$$
\deg_s\mathcal L=
\chi(X_s,\mathcal L_s)-\chi(X_s,\mathcal O_{X_s}).
$$

Book 8 showed that the Hilbert polynomial of a flat projective family is locally constant. Apply
that result to $\mathcal L\otimes\mathcal A^n$ and $\mathcal A^n$, where $\mathcal A$ is
relatively ample. Its Euler-characteristic polynomial lemma says that tensoring by $\mathcal L$
changes the polynomial on a curve by a constant: the first difference is supported in dimension
zero. Evaluating that constant at $n=0$ identifies it with
$\chi(\mathcal L_s)-\chi(\mathcal O_{X_s})=\deg_s\mathcal L$. Both Hilbert polynomials are
locally constant in $s$, so $s\mapsto\deg_s\mathcal L$ is locally constant on $S$.

The conclusion uses flatness of $X$ and invertibility of $\mathcal L$, hence flatness of $\mathcal L$ over $S$. In a nonflat family the arithmetic genus can jump. For a coherent sheaf that is not flat over the base, torsion supported on a special fiber can change the Euler characteristic. Constancy is a theorem with hypotheses, not a property of notation.

The projective hypothesis loses none of the promised smooth or nodal cases. Section 9.3 proves,
without using Riemann--Roch, that a proper flat finitely presented family with geometrically
reduced fibers is projective after an fpqc cover of the base. Apply the preceding argument there.
Fiber degree is unchanged by that cover, and local constancy descends, so the same conclusion
holds for every proper smooth or nodal relative curve in the standing conventions.

If fibers are reducible, total degree is locally constant but degree on an individual component need not even be globally labelable because components can permute. After a base change that labels components, one obtains a multidegree, and specialization can redistribute it. Later component-group theory measures precisely this extra information.

### 5.4 Horizontal divisors and fibers

Suppose $D\subset X$ is a relative effective Cartier divisor, meaning that $D$ is Cartier on $X$ and $D\to S$ is finite flat of rank $d$. Then every fiber $D_s$ is a length-$d$ effective Cartier divisor on $X_s$, and

$$
\deg_s\mathcal O_X(D)=d. \tag{5.4}
$$

Indeed (5.3) remains exact after base change, and $\dim_{\kappa(s)}H^0(D_s,\mathcal O_{D_s}(D_s))=d$ because twisting by a line bundle does not change the length of a zero-dimensional scheme.

When the total space is a regular surface over a one-dimensional regular base, (5.4) is written as an intersection number

$$
(D\cdot X_s)=d.
$$

This notation should not conceal the elementary content: it is the length of the scheme-theoretic intersection with the fiber. More generally, if a Cartier divisor $D$ meets $X_s$ properly, then

$$
(D\cdot X_s)=
\sum_{x\in D\cap X_s}
\operatorname{length}_{\mathcal O_{X,x}}
\frac{\mathcal O_{X,x}}{(f_D,f_s)}[\kappa(x):\kappa(s)],
$$

provided $f_D,f_s$ form the expected regular sequence. A vertical divisor containing $X_s$ does not meet it properly, and this length formula is not defined. Self-intersections and component pairings require the surface intersection theory developed later.

## 6. Effective relative divisors and symmetric powers

### 6.1 The correct relative notion

A collection of $d$ points in each fiber should form a family even when the points collide. Ordered sections are too rigid, and a reduced union discards multiplicity. The right object is a closed subscheme

$$
D\hookrightarrow X_T
$$

that is an effective Cartier divisor on $X_T$ and finite flat of rank $d$ over $T$. We call this a **relative effective divisor of degree $d$**. Both clauses matter. Cartier says that $D$ is cut out by one regular equation in the curve; finite flat of rank $d$ says that no point disappears or turns into a vertical component under specialization.

The construction is stable under every base change $T'\to T$. Flatness of $D/T$ preserves the Cartier property on fibers, while finite locally free modules remain finite locally free after tensor product. Its associated line bundle $\mathcal O_{X_T}(D)$ has fiberwise degree $d$ and a canonical section whose zero scheme is $D$.

If $T$ is connected, finite flat rank cannot jump. By contrast, the closed subscheme of $\mathbf A^1_T$ cut out by $tx=0$ over $T=\operatorname{Spec}k[t]$ is not flat: away from $t=0$ it is one point, while at $t=0$ it is the entire affine line. This is exactly the degeneration excluded by the definition.

### 6.2 Smooth curves turn points into divisors

Let $f:X\to S$ be smooth of relative dimension one. Every closed subscheme $Z\subset X_T$ finite flat of rank $d$ over $T$ is an effective Cartier divisor. This is the key curve-specific result behind the identification of the length-$d$ Hilbert space with the symmetric power.

The assertion is local on $X_T$ and $T$. Take a point $z\in Z$ above $t\in T$. Because $X_T/T$ is smooth of relative dimension one, it is locally modeled by a smooth algebra with one relative parameter. The ideal of a finite flat quotient has fiberwise codimension one. On the fiber, the local ring is regular of dimension one and the ideal is generated by a non-zero-divisor. Lifting a generator and applying Nakayama shows that the ideal is locally principal; flatness of both ambient ring and quotient over the base makes the generator regular. Thus $Z$ is Cartier.

Smoothness cannot simply be replaced by nodality. At a node with local ring $k[[x,y]]/(xy)$, the reduced point has ideal $(x,y)$, which needs two generators and is not Cartier. It is a length-one subscheme but not a divisor. The Hilbert space of points on a singular curve is therefore larger than its Cartier-divisor locus.

### 6.3 Universal divisors and addition

Book 8 constructed the symmetric power

$$
X^{(d)}=\operatorname{Sym}^d_S(X)
$$

for a smooth projective relative curve and identified it with the space of length-$d$ finite flat subschemes. By the preceding theorem it therefore represents relative effective Cartier divisors of degree $d$. There is a universal divisor

$$
\Delta_d\subset X\times_S X^{(d)}
$$

finite flat of rank $d$ over $X^{(d)}$. A map $T\to X^{(d)}$ is equivalent to pulling back $\Delta_d$ to a degree-$d$ divisor on $X_T$.

Addition of divisors produces a morphism

$$
X^{(d)}\times_S X^{(e)}
\longrightarrow X^{(d+e)}.
$$

Scheme-theoretically, it multiplies the two invertible ideals. If two sections meet in a special fiber, their sum specializes to a nonreduced divisor of length two rather than losing a point. On geometric points the map is the familiar concatenation

$$
(p_1+\cdots+p_d,\ q_1+\cdots+q_e)
\longmapsto p_1+\cdots+p_d+q_1+\cdots+q_e.
$$

For a section $p:S\to X$, repeated addition gives the diagonal divisor $dp$. Locally, if $p$ has equation $t$, then $dp$ has equation $t^d$ and structure sheaf $\mathcal O_X/(t^d)$. Multiplicity is thus a genuine infinitesimal thickening.

### 6.4 Nodal fibers and the boundary

For a nodal relative curve, the functor of relative effective Cartier divisors is still open inside the length-$d$ Hilbert space. Being locally principal by a regular element is an open condition in a flat finite presentation. But the open subset need not be proper: a Cartier point approaching a node may have a non-Cartier limit.

The failure appears after a ramified base change of the standard smoothing. Let $R$ be a discrete
valuation ring with uniformizer $\pi$ and consider

$$
C=\operatorname{Spec}R[x,y]/(xy-\pi^2).
$$

Its generic fiber is smooth and its special fiber is nodal. The generic-fiber point $(x,y)=(\pi,\pi)$
extends to a section through the node, with ideal $(x-\pi,y-\pi)$. At the local ring of the node
the two displayed generators have independent images in $\mathfrak m/\mathfrak m^2$; the relation
$xy-\pi^2$ has no linear term. Since $\mathfrak mI\subseteq\mathfrak m^2$, they remain independent
in $I/\mathfrak mI$. Nakayama therefore says that $I$ needs two generators. Hence this
height-one ideal is not principal, and the section is
not Cartier on the total space. The Hilbert compactification remembers the limit, while the
Cartier-divisor space omits it. This boundary distinction is essential when constructing
compactified Jacobians; it is not present for smooth families.

On the smooth locus $X^{\mathrm{sm}}\subset X$, symmetric powers still give Cartier divisors supported away from nodes. Many later arguments deliberately choose cusps or marked points in this locus so that their divisor and Abel constructions remain ordinary even when the fiber is nodal.

## 7. Differentials on curves

### 7.1 Kähler differentials and local parameters

Divisors measure multiplicative change. Differentials measure first-order additive change. For a morphism $X\to S$, the sheaf $\Omega^1_{X/S}$ is generated locally by symbols $da$ subject to

$$
d(a+b)=da+db,\qquad d(ab)=a\,db+b\,da,\qquad d(c)=0
$$

for functions $c$ pulled back from $S$. It represents derivations: maps $\Omega^1_{X/S}\to\mathcal M$ correspond naturally to $S$-derivations $\mathcal O_X\to\mathcal M$.

If $f:X\to S$ is smooth of relative dimension one, $\Omega^1_{X/S}$ is a line bundle. At a geometric point one may choose an étale local parameter $t$, and $dt$ is a basis. Under a new parameter $u$, one has

$$
du=\frac{du}{dt}\,dt
$$

with $du/dt$ a unit. Thus the line spanned by differentials is intrinsic even though a parameter is not.

The conormal sequence explains equations. If $X$ is cut out in a smooth $S$-scheme $P$ by an ideal $\mathcal I$, then

$$
\mathcal I/\mathcal I^2
\longrightarrow \Omega^1_{P/S}|_X
\longrightarrow \Omega^1_{X/S}
\longrightarrow0. \tag{7.1}
$$

When $X$ is a relative hypersurface $F=0$, the first map sends the class of $F$ to $dF$. Smoothness means that the partial derivatives do not vanish simultaneously on a fiber.

### 7.2 Canonical divisors on smooth curves

Let $X$ be a smooth proper geometrically connected curve over $k$. The line bundle

$$
\omega_X=\Omega^1_{X/k}
$$

is the **canonical bundle**. A nonzero rational differential $\eta$ is a rational section and defines its canonical divisor

$$
K_X=\operatorname{div}(\eta).
$$

Changing $\eta$ to $f\eta$ adds $\operatorname{div}(f)$, so the canonical divisor class is independent of the differential. After Riemann--Roch and duality we will prove

$$
\deg\omega_X=2g-2.
$$

Examples calibrate the sign. On $\mathbf P^1$ with affine coordinate $t$, the differential $dt$ has no finite zero or pole. At infinity put $u=t^{-1}$; then $dt=-u^{-2}du$, so

$$
\operatorname{div}(dt)=-2[\infty].
$$

Thus $\omega_{\mathbf P^1}\simeq\mathcal O_{\mathbf P^1}(-2)$. On a smooth plane curve of degree $n$, the conormal sequence together with the determinant of the cotangent bundle of $\mathbf P^2$ yields

$$
\omega_X\simeq\mathcal O_X(n-3).
$$

For a smooth cubic this is trivial, foreshadowing genus one.

### 7.3 Differentials at singular points

Ordinary differentials cease to be the right canonical sheaf at singularities. At the node

$$
A=k[[x,y]]/(xy),
$$

the conormal sequence gives

$$
\Omega^1_{A/k}=
(A\,dx\oplus A\,dy)/(y\,dx+x\,dy).
$$

This module is not locally free. It has torsion: the nonzero element $x\,dy=-y\,dx$ is killed by
the regular element $x+y$, since $x^2dy=-xy\,dx=0$. A family can therefore have an invertible
differential bundle on smooth fibers but a noninvertible $\Omega^1$ on the nodal fiber.

At the cusp $k[[t^2,t^3]]$, the image of ordinary differentials inside $k[[t]]dt$ is generated by $2t\,dt$ and $3t^2dt$. In characteristic not two, it misses $dt$; in small characteristic its behavior changes further. The singularity is visible in the failure of ordinary differentials to capture all regular differentials on the normalization.

Duality calls for a different object: a sheaf that is allowed controlled poles on the normalization and whose residues cancel across branches. This dualizing sheaf is invertible at a node even though $\Omega^1$ is not.

## 8. Residues

### 8.1 The local residue

Let $X$ be a smooth integral curve over $k$ and let $x$ be a closed point. A subtlety matters over an
imperfect field: although $X/k$ is smooth, the finite extension $\kappa(x)/k$ need not be
separable. The residue must therefore be defined before invoking a field trace.

The point $x$ is an effective Cartier divisor. For every $n\geq1$, adjunction for the finite
Cartier subscheme $nx$ identifies the principal-part quotient with its finite dualizing module:

$$
\Omega^1_{X/k}(nx)/\Omega^1_{X/k}
\simeq \omega_{nx/k}
=\operatorname{Hom}_k(\mathcal O_{nx},k). \tag{8.1}
$$

Here the sheaves are supported at $x$, and the last Hom is understood on global sections of the
finite scheme. The isomorphism is the one-equation Koszul calculation: dualize
$0\to\mathcal O_X(-nx)\to\mathcal O_X\to\mathcal O_{nx}\to0$ against
$\Omega^1_{X/k}$ and use the conormal determinant to identify the resulting Ext module with the
$k$-linear dual of $\mathcal O_{nx}$. This is local algebra and does not use global duality.
Under the inclusions for increasing $n$, the right side
restricts along $\mathcal O_{(n+1)x}\twoheadrightarrow\mathcal O_{nx}$. Evaluation at $1$ is
therefore compatible. Passing to the direct limit defines the canonical $k$-linear residue

$$
\operatorname{Res}_x:
\Omega^1_{k(X)/k}\longrightarrow k, \tag{8.2}
$$

which kills regular differentials. The parameter calculation below shows directly that it also
kills exact differentials.

When $\kappa(x)/k$ is separable, choose a coefficient field in the completion and a uniformizer
$t$. Then

$$
\eta=\left(\sum_{n\gg-\infty}a_nt^n\right)dt,
\qquad a_n\in\kappa(x),
$$

and (8.1) identifies $a\,dt/t$ with the functional
$b\mapsto\operatorname{Tr}_{\kappa(x)/k}(ab)$. Hence in this case

$$
\operatorname{Res}_x(\eta)
=\operatorname{Tr}_{\kappa(x)/k}(a_{-1}). \tag{8.3}
$$

For an inseparable residue extension, (8.1)--(8.2), not the possibly zero field trace, is the
definition.

### 8.2 Independence of parameter

The adjunction definition (8.1) is parameter-free. In the separable coefficient-field
description, its independence is also visible directly. If $u$ is another parameter, write
$u=tv$ with $v$ a unit. Then

$$
\frac{du}{u}=\frac{dt}{t}+\frac{dv}{v},
$$

and $dv/v$ is regular. More generally, termwise differentiation of a Laurent series gives

$$
d\!\left(\sum a_nt^n\right)=\sum n a_nt^{n-1}dt,
$$

whose $t^{-1}dt$ coefficient is zero: it could only come from $n=0$. This calculation is valid
in every characteristic. Any change of parameter is a composition of multiplication by a unit
and formal substitution, and the chain rule now shows that the residue is unchanged.

Thus coefficient extraction gives the same $k$-valued functional in every parameter. Termwise
differentiation proves $\operatorname{Res}_x(db)=0$ in the separable coefficient-field case. In
general the same identity is the elementary Koszul calculation behind (8.1): the functional
corresponding to $db$ evaluates to zero on $1$.

### 8.3 The global residue theorem

If $X$ is a smooth proper geometrically connected curve over $k$ and $\eta$ a rational differential, then

$$
\sum_{x\in X^{(1)}}\operatorname{Res}_x(\eta)=0. \tag{8.4}
$$

Only finitely many terms are nonzero. Properness is essential: $dt/t$ on $\mathbf G_m$ has residues visible at the omitted points $0$ and $\infty$, and discarding either boundary destroys the cancellation.

A proof first treats $\mathbf P^1$. Write the differential as $h(T)dT$ and perform partial
fractions over $k[T]$, without splitting the irreducible denominators. For a power $P(T)^n$, the
adjunction isomorphism (8.1) identifies its principal part with the $k$-dual of
$k[T]/(P^n)$; evaluation at $1$ is exactly the coefficient contributed by that partial fraction.
Euclidean division shows that the sum of these finite evaluations is the negative of the
$T^{-1}dT$ coefficient after putting $T=U^{-1}$ at infinity. This proves the formula over an
arbitrary field, including inseparable closed points.

For a general $X$, smoothness makes $k(X)/k$ a separably generated function field of
transcendence degree one. A separating element $z\in k(X)$ therefore gives a finite generically
separable morphism $\pi:X\to\mathbf P^1_k$. Apply the local trace formula (8.5) below to $\eta$
and sum first over points above each point of $\mathbf P^1$. The result is the residue sum of
$\operatorname{Tr}_{k(X)/k(z)}\eta$ on $\mathbf P^1$, hence is zero. This proves (8.4) without
using Riemann--Roch or duality.

The conceptual consequence is more important than the chosen proof. A collection of local polar parts can be the polar part of a global rational differential only if its total residue is zero; duality will show that this is the only obstruction when the allowed poles are sufficiently specified.

### 8.4 Finite maps and trace

Let $\pi:Y\to X$ be a finite generically separable morphism of smooth proper integral curves. The field trace induces a trace on rational differentials

$$
\operatorname{Tr}_{k(Y)/k(X)}:
\Omega^1_{k(Y)/k}\longrightarrow\Omega^1_{k(X)/k}.
$$

For every closed point $x\in X$,

$$
\operatorname{Res}_x(\operatorname{Tr}_\pi\eta)
=\sum_{y\mapsto x}\operatorname{Res}_y(\eta). \tag{8.5}
$$

This local trace formula remains valid when residue extensions are inseparable. To prove it,
complete at $x$ and decompose the finite algebra into the branches at the points $y$. For finite
Cartier thickenings of those branches, finite duality is the elementary identity

$$
\omega_{B/A}=\operatorname{Hom}_A(B,\omega_A),
$$

and trace is evaluation at $1\in B$. Under the adjunction identifications (8.1), evaluation at
$1$ on the product algebra is the sum of evaluation at $1$ on its factors. Passing through the
compatible thickenings proves (8.5). When the function-field extension is separable, this finite
duality trace is the usual trace on rational differentials. If the residue extensions are also
separable, (8.3) rewrites (8.5) as the familiar formula with residue-field traces of Laurent
coefficients.

For a purely inseparable map, ordinary field trace can be zero and does not define the required
map on Kähler differentials. The finite-duality trace remains meaningful for every finite map
between Cohen--Macaulay curves. This is why later functoriality is formulated through dualizing
sheaves rather than only through field traces.

## 9. Dualizing sheaves

### 9.1 Why ordinary differentials are not enough

On a smooth curve, regular differentials serve two roles: they are first-order forms and they are dual to $H^1(\mathcal O_X)$. At a node the first role is played by $\Omega^1$, but that sheaf is not invertible and does not give the correct duality. The second role persists under degeneration and singles out the dualizing sheaf.

The guiding requirement is a trace functional

$$
\operatorname{tr}:H^1(X,\omega_X)\longrightarrow k
$$

such that multiplication followed by trace makes

$$
H^i(X,\mathcal F)\times
\operatorname{Ext}^{1-i}_X(\mathcal F,\omega_X)
\longrightarrow k
$$

a perfect pairing for coherent $\mathcal F$. For a vector bundle $\mathcal E$, the second factor becomes the cohomology of $\mathcal E^\vee\otimes\omega_X$. This property determines $\omega_X$ uniquely up to unique isomorphism compatible with trace.

### 9.2 Dualizing sheaves on proper curves

Let $X$ be a proper Cohen--Macaulay curve over $k$. Then $X$ has a dualizing sheaf $\omega_X$, a coherent maximal Cohen--Macaulay sheaf characterized, for every zero-dimensional coherent sheaf $\mathcal T$, by

$$
\operatorname{Ext}^1_X(\mathcal T,\omega_X)
\simeq H^0(X,\mathcal T)^\vee, \tag{9.1}
$$

together with the global trace and the full perfect pairing described above. Here is a
construction and not merely an existence assertion. A proper curve over a field is projective;
choose a closed immersion $i:X\hookrightarrow\mathbf P^N_k$. Since $X$ is Cohen--Macaulay of
codimension $N-1$, a finite locally free resolution of $i_*\mathcal O_X$ has dual cohomology
against $\omega_{\mathbf P^N}$ in only that codimension. Put

$$
i_*\omega_X=
\mathcal Ext^{N-1}_{\mathbf P^N}
(i_*\mathcal O_X,\omega_{\mathbf P^N}).
$$

The projective-space calculation is explicit. Laurent monomials in the standard Cech complex pair
the degree-$q$ term for $\mathcal O(m)$ perfectly with the degree-$(N-q)$ term for
$\mathcal O(-m-N-1)$ by taking the coefficient of
$(x_0\cdots x_N)^{-1}$. Resolving $i_*\mathcal F$ by finite sums of twists extends this pairing,
by exactness, to every coherent $\mathcal F$. The change-of-rings calculation for the
codimension-$(N-1)$ Cohen--Macaulay immersion identifies the resulting complex on $\mathbf P^N$
with the Ext sheaf just defined on $X$. Thus one obtains the natural quasi-isomorphism

$$
R\operatorname{Hom}_k(R\Gamma(X,\mathcal F),k)
\simeq
R\operatorname{Hom}_X(\mathcal F,\omega_X[1]). \tag{9.2}
$$

For $\mathcal F=\mathcal O_X$, the image of $1$ under (9.2) is the trace
$H^1(X,\omega_X)\to k$. For a zero-dimensional $\mathcal T$, taking degree zero in (9.2) gives
(9.1); taking cohomology for general $\mathcal F$ gives the full pairing. If a second embedding
is chosen, the two sheaves represent the same functor in (9.2), so the representing isomorphism
is unique and respects trace. This proves independence of all choices.

The Cohen--Macaulay hypothesis excludes embedded zero-dimensional components. Without it, duality is represented by more than one sheaf degree; a single $\omega_X$ cannot encode the whole theory. Pure reduced curves are Cohen--Macaulay because every local ring has dimension one and a function avoiding the finitely many minimal primes is a non-zero-divisor.

A curve is **Gorenstein** if its dualizing sheaf is invertible. Smooth curves, local complete-intersection curves, and nodal curves are Gorenstein. A reduced curve need not be Gorenstein; at a non-Gorenstein singularity $\omega_X$ is torsion-free of rank one but not a line bundle. Divisor formulas involving a canonical Cartier divisor then require modification.

### 9.3 The relative dualizing sheaf

We first remove a possible projectivity ambiguity. If a proper flat finitely presented family of
curves has geometrically reduced fibers, then it is projective fpqc-locally on the base. Indeed,
after an étale extension around a chosen geometric fiber, choose sections through smooth points on
every irreducible component of that fiber. Their sum is a relative effective Cartier divisor
$D$. Its restriction has positive degree on every component, hence $\mathcal O(D)$ is ample on
that fiber. The curve criterion used here is elementary: on a proper reduced curve, positivity
on every component is equivalent to ampleness; it follows by passing to the finite normalization
and applying the affine-nonvanishing criterion componentwise. A finite set of affine
nonvanishing witnesses persists after shrinking the base, so $\mathcal O(D)$ is relatively ample
there. Book 8 then supplies a projective embedding. This applies in particular to smooth and
nodal families and does not use Riemann--Roch.

Let $f:X\to S$ be a proper flat finitely presented Cohen--Macaulay morphism of pure relative
dimension one with geometrically reduced fibers, with $S$ locally noetherian. There is a relative
dualizing sheaf $\omega_{X/S}$ and a trace

$$
\operatorname{tr}_f:R^1f_*\omega_{X/S}\longrightarrow\mathcal O_S. \tag{9.3}
$$

Its defining property is relative duality. For every vector bundle $\mathcal E$ on $X$, cup
product and (9.3) give a quasi-isomorphism

$$
R f_*(\mathcal E^\vee\otimes\omega_{X/S})[1]
\simeq
R\mathcal Hom_S(Rf_*\mathcal E,\mathcal O_S). \tag{9.4}
$$

We give the construction because base change is part of the theorem. By the preceding paragraph
we may pass to a faithfully flat cover of $S$ and choose
$i:X\hookrightarrow P=\mathbf P^N_S$. Relative Cohen--Macaulayness says that the finite locally
free resolution of $i_*\mathcal O_X$ is perfect of pure codimension $N-1$. Define

$$
i_*\omega_{X/S}=
\mathcal Ext^{N-1}_{P}
(i_*\mathcal O_X,\omega_{P/S}).
$$

The same Laurent-monomial pairing works over the base ring and commutes with tensor product.
Apply it to a finite locally free resolution of $i_*\mathcal E$ and then use the
pure-codimension change-of-rings calculation. This gives (9.4) and its evaluation-at-one trace.
The same pure-codimension assertion after tensoring with an arbitrary
$\mathcal O_S$-algebra shows that this Ext sheaf, the trace, and (9.4) commute with that tensor
product. Two embeddings give the same representing object in (9.4); the unique comparison
satisfies the cocycle condition, so the local sheaves and traces descend. Thus the construction
also covers a proper family not supplied with a global projective embedding.

The formation of $\omega_{X/S}$ commutes with arbitrary base change $S'\to S$ under these hypotheses:

$$
\omega_{X/S}|_{X_{S'}}
\simeq\omega_{X_{S'}/S'}. \tag{9.5}
$$

Flatness and the relative Cohen--Macaulay property are the decisive assumptions. Formula (9.5)
includes specialization to every fiber, and (9.4) specializes to (9.2).

### 9.4 Smooth and Gorenstein families

If $f$ is smooth of relative dimension one, then

$$
\omega_{X/S}\simeq\Omega^1_{X/S}.
$$

This is checked on an étale coordinate chart, where both are freely generated by $dt$, and the residue description identifies their traces. Thus relative duality genuinely extends the familiar calculus of differentials.

The morphism $f$ is **Gorenstein** when it is flat and its fibers have Gorenstein local rings, equivalently in this setting when $\omega_{X/S}$ is invertible. A relative local complete intersection of pure dimension one is Gorenstein. In particular, a family locally given inside a smooth relative surface by one regular equation has an invertible dualizing sheaf.

For a relative hypersurface $X=(F=0)$ in a smooth $S$-scheme $P$ of relative dimension two, adjunction gives

$$
\omega_{X/S}\simeq
\left(\omega_{P/S}\otimes\mathcal O_P(X)\right)|_X. \tag{9.6}
$$

Unlike $\Omega^1_{X/S}$, the right side stays invertible when a smooth fiber acquires a node. Formula (9.6) is the practical construction of invariant differentials on many modular and plane-curve families.

## 10. Nodes, normalization, and opposite residues

### 10.1 The local node

Over an algebraically closed field, a node has completed local ring

$$
A=k[[x,y]]/(xy).
$$

Its normalization is

$$
\widetilde A=k[[x]]\oplus k[[y]],
$$

corresponding to two branches. The dualizing module of $A$ is free of rank one. Inside meromorphic differentials on the branches, a generator is represented by

$$
\theta=\left(\frac{dx}{x},-\frac{dy}{y}\right). \tag{10.1}
$$

The two residues are $1$ and $-1$. This is the origin of the opposite-residue rule.

For the smoothing $xy=a$ over a base ring, relative differentiation gives

$$
y\,dx+x\,dy=0.
$$

On the locus where $x$ or $y$ is invertible,

$$
\frac{dx}{x}=-\frac{dy}{y}.
$$

The common expression extends as a generator of the relative dualizing sheaf through the node, although neither $dx/x$ nor $dy/y$ is an ordinary regular differential there.

### 10.2 Functions under normalization

Let $C$ be a reduced proper nodal curve over $k$, and $\nu:\widetilde C\to C$ its normalization. For simplicity first assume every node and both branches are $k$-rational. If a node $q$ has inverse images $q',q''$, a regular function on $\widetilde C$ descends exactly when its values at $q'$ and $q''$ agree. Therefore

$$
0\longrightarrow\mathcal O_C
\longrightarrow\nu_*\mathcal O_{\widetilde C}
\longrightarrow\bigoplus_{q\in\operatorname{Sing}C}k_q
\longrightarrow0, \tag{10.2}
$$

where the last map is $(f',f'')\mapsto f'(q')-f''(q'')$.

Over a nonclosed field, put
$B_q=H^0(\nu^{-1}(q),\mathcal O_{\nu^{-1}(q)})$; this is a degree-two étale algebra over
$\kappa(q)$. The intrinsic discrepancy line is

$$
Q_q=B_q/\kappa(q),
$$

where $\kappa(q)$ is embedded diagonally. Thus the last term in (10.2) must in general be
replaced by $\bigoplus_q i_{q*}Q_q$. It is a one-dimensional $\kappa(q)$-vector space, but it is
not canonically the residue field: ordering two split branches identifies it with
$\kappa(q)$ and reversing the order changes the sign. This formulation is Galois invariant.

Taking Euler characteristics is now unambiguous. If $C$ is connected and $\widetilde C$ has
connected components $\widetilde C_1,\ldots,\widetilde C_r$, then

$$
p_a(C)=\sum_i p_a(\widetilde C_i)
+\sum_q[\kappa(q):k]-r+1.
$$

In the split case, when the normalization components are smooth of genera $g_i$ and there are
$\delta$ nodes, this becomes

$$
p_a(C)=\sum_i g(\widetilde C_i)+\delta-r+1. \tag{10.3}
$$

The term $\delta-r+1$ is the first Betti number of the connected dual graph. The preceding general
formula shows explicitly that residue-field degrees are not lost before splitting.

### 10.3 Rosenlicht differentials

The dualizing sheaf of a nodal curve has an explicit normalization description. After splitting
the branches, write $\operatorname{res}$ for the Laurent coefficient of $dt/t$ on a branch. Then

$$
\omega_C=
\left\{
\eta\in\nu_*\Omega^1_{\widetilde C}
\Big(\sum(q'+q'')\Big):
\operatorname{res}_{q'}(\eta)+\operatorname{res}_{q''}(\eta)=0
\text{ for every node }q
\right\}. \tag{10.4}
$$

When the nodes and branches are rational, the residues in (10.4) are the literal Laurent
coefficients of Section 8. In general, (10.4) means the same condition after a field extension
that splits the branches; it is invariant under descent. Intrinsically it says

$$
\sum_{p\mapsto q}\operatorname{Res}_p(f\eta)=0
\quad\text{for every }f\in\mathcal O_{C,q},
$$

where the residues are the canonical $k$-valued functionals (and the condition may equivalently
be tested after scalar extension). Thus sections are regular differentials on the normalization
allowed simple poles over nodes, with opposite residues on the two geometric branches. At a
node, (10.1) shows that this module is free of rank one. Away from the nodes, normalization is an
isomorphism and (10.4) is the ordinary canonical bundle.

The local calculation proves equality with the dualizing sheaf. In the completed split local ring,
write a pair with at most simple poles as

$$
\left(a(x)\frac{dx}{x},\,b(y)\frac{dy}{y}\right).
$$

The residue condition is $a(0)+b(0)=0$. Put $g(y)=-b(y)$; then
$a(0)=g(0)$, so $(a(x),g(y))$ is an element of
$k[[x,y]]/(xy)\subset k[[x]]\oplus k[[y]]$, and the displayed pair is that element times
$\theta$ from (10.1). Conversely every multiple of $\theta$ has opposite residues. Hence the
right side of (10.4) has the completed dualizing stalk at every node and the ordinary canonical
stalk elsewhere. Coherent sheaves on a noetherian curve are detected by these completed stalks,
which proves (10.4); descent gives the nonsplit case.

In the split situation there is an exact sequence

$$
0\longrightarrow\nu_*\omega_{\widetilde C}
\longrightarrow\omega_C
\xrightarrow{\operatorname{res}}
\bigoplus_q k_q
\longrightarrow0, \tag{10.5}
$$

where the displayed residue may be taken on either branch, the other being its negative. Surjectivity is local: multiples of (10.1) realize any residue. Globally, the individual component residue theorems impose relations on global sections, exactly matching cycles in the dual graph.

Without a chosen splitting, replace $k_q$ in (10.5) by the one-dimensional residue line obtained
by descending the anti-diagonal branch residues. It is dual, under finite local duality, to the
discrepancy line $Q_q$ above. No orientation of the branches is needed for the descended exact
sequence; only an identification of its last line with $\kappa(q)$ requires such a choice.

The description also works for a reduced curve with more general singularities if one replaces
opposite residues by the condition

$$
\sum_{p\mapsto q}\operatorname{Res}_p(f\eta)=0
\quad\text{for every }f\in\mathcal O_{C,q}.
$$

This is the Rosenlicht description of the dualizing sheaf; it need not be invertible when the
curve is not Gorenstein. At a split rational node, testing $f=1$ gives the opposite-residue rule
and the other tests enforce no additional condition.

### 10.4 Families of nodal curves

Let $f:C\to S$ be a proper flat nodal curve that is a relative local complete intersection. Then $\omega_{C/S}$ is a line bundle, commutes with arbitrary base change, and restricts on every geometric fiber to the sheaf in (10.4). This is the stable replacement for $\Omega^1_{C/S}$.

A simultaneous normalization need not exist over an arbitrary base: normalizing the total space can fail to normalize every fiber after base change. Consequently the branch-and-residue description should be used fiberwise unless a simultaneous normalization is part of the hypotheses. Étale locally around a node, however, the family has the form

$$
xy=a
$$

in a smooth relative surface, and $dx/x=-dy/y$ gives a local frame for $\omega_{C/S}$. These frames glue because adjunction is canonical.

If sections mark smooth points $p_1,\ldots,p_n$, then

$$
\omega_{C/S}(p_1+\cdots+p_n)
$$

allows simple poles at the markings as well as the implicit branch poles at nodes. A global section has total residue zero on each geometric fiber, with node residues cancelling internally. This is the differential package used for degenerating pointed curves.

## 11. Riemann--Roch over a field

### 11.1 The theorem and its meaning

Let $X$ be a smooth proper geometrically connected curve of genus $g$ over $k$, and let $\mathcal L$ be a line bundle of degree $d$. Riemann--Roch states

$$
\chi(X,\mathcal L)=d+1-g. \tag{11.1}
$$

Equivalently, after choosing a canonical divisor $K$ and a divisor $D$ for $\mathcal L$,

$$
\ell(D)-\ell(K-D)=\deg D+1-g, \tag{11.2}
$$

where $\ell(D)=\dim_k H^0(X,\mathcal O_X(D))$. The second form uses Serre duality to identify $h^1(\mathcal O(D))$ with $\ell(K-D)$. The first form is logically more elementary and remains valid for proper Gorenstein curves.

Riemann--Roch says that each unit of degree contributes one unit to the Euler characteristic. It does not say that $h^0$ itself always grows by one: a new allowed pole can instead remove an obstruction in $H^1$. The correction term $\ell(K-D)$ measures this **speciality**. Once $d>2g-2$, its degree is negative, it vanishes, and the naive count becomes exact:

$$
h^0(X,\mathcal L)=d+1-g.
$$

### 11.2 Proof by adding points

We first prove the Euler-characteristic form without duality. Every line bundle is represented by a divisor. If $D$ is an effective Cartier divisor, (5.3) gives

$$
\chi(\mathcal O_X(D))-\chi(\mathcal O_X)
=\chi(\mathcal O_D(D)).
$$

The sheaf $\mathcal O_D(D)$ is invertible as an $\mathcal O_D$-module, so its $k$-dimension is the length of $D$:

$$
\chi(\mathcal O_D(D))
=\sum_x n_x[\kappa(x):k]=\deg D.
$$

For a general divisor write $D=D_+-D_-$ with disjoint effective parts. Apply the effective calculation first to $D_+$ and then to the exact sequence obtained by subtracting $D_-$. Additivity of Euler characteristic gives

$$
\chi(\mathcal O_X(D))=\deg D+\chi(\mathcal O_X).
$$

Since $\chi(\mathcal O_X)=1-g$, this is (11.1).

This proof reveals why regularity was convenient: it represented every line bundle by a difference of effective point divisors. On a singular Gorenstein curve one can instead use the definition (5.2), for which (11.1) is immediate once degree is defined. The nontrivial content then shifts to identifying degree with Cartier divisors and proving duality.

### 11.3 Consequences and examples

A line bundle of negative degree has no nonzero section. Indeed a nonzero section defines an effective divisor and hence has nonnegative degree. This uses integrality; on a reducible curve a line bundle of negative total degree can have a section supported on components where its degree is positive.

Using the duality theorem proved independently in Chapter 12, apply (11.2) to $D=0$. Since
$\ell(0)=1$,

$$
h^0(X,\omega_X)=g. \tag{11.3}
$$

Applying it to $D=K$ gives

$$
\deg K=2g-2. \tag{11.4}
$$

For $X=\mathbf P^1$, $g=0$ and

$$
h^0(\mathcal O(n))=
\begin{cases}
n+1,&n\geq0,\\
0,&n<0,
\end{cases}
$$

while $h^1(\mathcal O(n))=\max\{-n-1,0\}$. This realizes every term in (11.2). For genus one, $\omega_X$ has degree zero and a nonzero section, hence is trivial. For $g\geq2$, the canonical bundle has positive degree and its sections define the canonical linear system.

If $\deg\mathcal L\geq2g$, then $\mathcal L$ is globally generated. For any closed geometric point $p$, duality applied to $\mathcal L(-p)$ gives

$$
H^1(X,\mathcal L(-p))^\vee
\simeq H^0(X,\omega_X\otimes\mathcal L^{-1}(p))=0
$$

because the latter degree is at most $-1$. The evaluation map at $p$ is therefore surjective. If $\deg\mathcal L\geq2g+1$, the same argument with every length-two divisor proves that sections separate points and tangent directions, so $\mathcal L$ is very ample. These bounds connect Riemann--Roch to the projective embeddings of Book 8.

### 11.4 Gorenstein and nodal curves

Let $C$ be a proper geometrically connected Gorenstein curve over $k$, pure of dimension one, and let $g=p_a(C)$. For every line bundle $\mathcal L$,

$$
\chi(C,\mathcal L)=\deg\mathcal L+1-g, \tag{11.5}
$$

and duality gives

$$
h^0(C,\mathcal L)-h^0(C,\omega_C\otimes\mathcal L^{-1})
=\deg\mathcal L+1-g. \tag{11.6}
$$

Moreover $\deg\omega_C=2g-2$. Indeed duality exchanges $H^0(\omega_C)$ with
$H^1(\mathcal O_C)^\vee$ and $H^1(\omega_C)$ with $H^0(\mathcal O_C)^\vee$, so
$\chi(\omega_C)=-\chi(\mathcal O_C)$; the Euler-characteristic definition of degree gives the
formula. For a connected nodal curve, normalization makes the formula visible. Tensor (10.2) by
$\mathcal L$ and take Euler characteristics. Each node subtracts one from $\chi$, while gluing
component constants produces the graph contribution in (10.3). Applying ordinary
Riemann--Roch on normalized components and adding yields (11.5). The opposite-residue description
yields the dual term.

On a reducible curve, negative total degree does not force vanishing. A section may vanish identically on some components, so its zero is a zero-divisor rather than a Cartier divisor. A safe vanishing criterion is componentwise: if $\mathcal L$ has negative degree on every irreducible component of a reduced connected curve, then $H^0(C,\mathcal L)=0$. More refined inequalities must account for nodes where a nonzero componentwise section is forced to vanish.

## 12. Serre duality

### 12.1 The residue pairing

Riemann--Roch counts the difference between functions and obstructions. Serre duality identifies those obstructions as linear functionals given by differentials. Let $X$ be a smooth proper geometrically connected curve and $D$ a divisor. Choose an affine cover $X=U\cup V$ such that the relevant poles lie in $U\setminus V$. A class in $H^1(X,\mathcal O_X(D))$ is represented by a rational function $g$ on $U\cap V$, modulo functions extending to either side.

For $\eta\in H^0(X,\omega_X(-D))$, define

$$
\langle[g],\eta\rangle
=\sum_{x\in X\setminus V}\operatorname{Res}_x(g\eta). \tag{12.1}
$$

Changing $g$ by a function regular on $U$ contributes residues of a regular differential. Changing it by a function on $V$ changes the chosen partial sum by the negative of its complement; the global residue theorem makes the total zero. Thus (12.1) is well defined. In sheaf language it is cup product followed by trace:

$$
H^1(X,\mathcal O_X(D))
\times H^0(X,\omega_X(-D))
\longrightarrow H^1(X,\omega_X)
\xrightarrow{\operatorname{tr}}k. \tag{12.2}
$$

### 12.2 Perfectness

The pairing is perfect:

$$
H^1(X,\mathcal O_X(D))^\vee
\simeq H^0(X,\omega_X(-D)). \tag{12.3}
$$

This is now a theorem rather than a dimension count. In the construction of Section 9.2, the
dualizing sheaf on a smooth curve is identified with $\Omega^1_{X/k}$ by the local generator
$dt$. Under this identification, local duality for the skyscraper sheaf at a closed point sends
the class of $t^{-1}$ paired with $dt$ to $1$. Consequently the trace furnished by (9.2) is
exactly the residue trace of (12.2): both are compatible with restriction and connecting maps,
and they agree on these local generators. Formula (9.2), applied to
$\mathcal F=\mathcal O_X(D)$ and then read in degree zero, is therefore precisely (12.3).

For completeness, the usual divisor devissage makes the mechanism explicit. For a closed point
$p$, compare

$$
0\to\mathcal O_X(D)\to\mathcal O_X(D+p)\to\mathcal Q_p\to0
$$

with its dual triangle against $\omega_X[1]$. Local duality identifies the dual of the
zero-dimensional quotient $\mathcal Q_p$ with its principal-part residue functional. The two
long exact cohomology sequences are therefore transposes. The finite resolution on projective
space supplies the initial calculation; adding or removing closed points one at a time and using
the two-out-of-three property recovers the same pairing in divisor language. This argument
proves both cohomological degrees together and does not assume Riemann--Roch.

The decisive local calculation, over a rational point, is

$$
\left(t^{-1}k\right)\times(k\,dt)\longrightarrow k,
\qquad (a/t,b\,dt)\longmapsto ab.
$$

At a nonrational point the local principal-part quotient is paired with
$\operatorname{Hom}_k(\kappa(p),k)$ as in (8.1), and evaluation supplies the perfect $k$-pairing.
When $\kappa(p)/k$ is separable this is the familiar field-trace formula; in the inseparable case
the finite dualizing module replaces the degenerate field trace. Thus no perfection assumption on
$k$ is hidden.

### 12.3 Duality for line bundles and vector bundles

For a line bundle $\mathcal L$,

$$
H^1(X,\mathcal L)^\vee
\simeq H^0(X,\mathcal L^{-1}\otimes\omega_X),
\qquad
H^0(X,\mathcal L)^\vee
\simeq H^1(X,\mathcal L^{-1}\otimes\omega_X). \tag{12.4}
$$

For a vector bundle $\mathcal E$,

$$
H^i(X,\mathcal E)^\vee
\simeq H^{1-i}(X,\mathcal E^\vee\otimes\omega_X),
\qquad i=0,1. \tag{12.5}
$$

These formulas are the two cohomology degrees of (9.2). For a vector bundle, internal Hom into
$\omega_X$ is $\mathcal E^\vee\otimes\omega_X$ and its higher sheaf Ext groups vanish. For an
arbitrary coherent sheaf $\mathcal F$, the precise form is instead

$$
H^i(X,\mathcal F)^\vee
\simeq \operatorname{Ext}^{1-i}_X(\mathcal F,\omega_X).
$$

The Ext term cannot generally be replaced by cohomology of a sheaf dual when $\mathcal F$ has torsion. On a proper Cohen--Macaulay curve the same statement holds with its dualizing sheaf; if the curve is Gorenstein, (12.4)--(12.5) retain their line-bundle form.

### 12.4 Functoriality

If $\pi:Y\to X$ is finite between proper Cohen--Macaulay curves, there is a trace

$$
\pi_*\omega_Y\longrightarrow\omega_X
$$

characterized, in the finite case, by

$$
\pi_*\omega_Y\simeq
\mathcal Hom_X(\pi_*\mathcal O_Y,\omega_X).
$$

Evaluation at $1$ gives the trace. On smooth generically separable curves this recovers the trace of rational differentials and (8.5). Pullback of functions and trace of differentials are adjoint:

$$
\langle \pi^*\alpha,\eta\rangle_Y
=\langle\alpha,\operatorname{Tr}_\pi\eta\rangle_X.
$$

Likewise, maps of vector bundles induce transpose maps on cohomology after dualizing and twisting by $\omega$. This transposition principle later controls correspondences on curves.

## 13. Relative Riemann--Roch and cohomology in families

### 13.1 A two-term model

Let $f:X\to S$ be a projective flat relative curve with $S$ locally noetherian, and let $\mathcal E$ be a vector bundle on $X$. After restricting to an affine open $U=\operatorname{Spec}A\subset S$, there are finite free $A$-modules $K^0,K^1$ and a map

$$
d:K^0\longrightarrow K^1 \tag{13.1}
$$

such that, for every $A$-algebra $B$, the cohomology of $\mathcal E_B$ on $X_B$ is computed by

$$
K^0\otimes_A B\longrightarrow K^1\otimes_A B. \tag{13.2}
$$

Here is why one matrix really suffices. Proper coherence makes $Rf_*\mathcal E$ a
pseudo-coherent complex on $S$. Resolve after a projective embedding by finite sums of twists of
a relatively very ample bundle, using Book 8's relative Serre vanishing to make every sufficiently
high twisted pushforward finite locally free and base-change compatible. Because $X$ and
$\mathcal E$ are flat over $S$, tensoring this resolution with any $A$-algebra computes the
corresponding resolution on the base-changed curve. Every such curve has coherent cohomology only
in degrees zero and one. The finite-complex criterion therefore splits off contractible finite
projective summands and shortens the resolution to $K^0\to K^1$. Shrinking $U$ makes the two
projective modules free. This proves (13.2) for every $A$-algebra, not only for residue fields.

The model is stronger than a fiberwise dimension statement. It records every specialization by one matrix with entries in $A$. It is exactly the cohomological amount demanded by dimension one.

### 13.2 Semicontinuity and base change

From (13.2),

$$
H^0(X_B,\mathcal E_B)=\ker(d\otimes B),\qquad
H^1(X_B,\mathcal E_B)=\operatorname{coker}(d\otimes B). \tag{13.3}
$$

The function $s\mapsto h^0(X_s,\mathcal E_s)$ is upper semicontinuous because a bound on matrix rank is cut out by minors. Since

$$
\chi(X_s,\mathcal E_s)=\operatorname{rank}K^0-\operatorname{rank}K^1,
$$

$h^1$ is upper semicontinuous as well.

There are natural maps

$$
(f_*\mathcal E)\otimes\kappa(s)\longrightarrow
H^0(X_s,\mathcal E_s), \tag{13.4}
$$

$$
(R^1f_*\mathcal E)\otimes\kappa(s)\longrightarrow
H^1(X_s,\mathcal E_s). \tag{13.5}
$$

In the present perfect two-term situation, (13.5) is an isomorphism because cokernels commute with tensor product. The first can fail because kernels need not commute with tensor product. Near $s$, the following conditions are equivalent: (13.4) is universally an isomorphism; $R^1f_*\mathcal E$ is locally free; and $h^1(X_t,\mathcal E_t)$ is locally constant. Then $f_*\mathcal E$ is also locally free and both terms commute with arbitrary base change.

In particular, if $H^1(X_s,\mathcal E_s)=0$ for every $s$, then $R^1f_*\mathcal E=0$ and $f_*\mathcal E$ is locally free with arbitrary base change. This is the workhorse that turns fiberwise vanishing into a vector bundle of sections.

### 13.3 Relative Riemann--Roch

Assume that the geometric fibers are connected and reduced of constant arithmetic genus $g$. For
a line bundle $\mathcal L$ of relative degree $d$,

$$
\chi(X_s,\mathcal L_s)=d+1-g \tag{13.6}
$$

for every $s$. Both $d$ and $g$ are locally constant, so the formula is interpreted component by component on $S$.

For a vector bundle $\mathcal E$ of rank $r$, put $\deg\mathcal E=\deg\det\mathcal E$. Then

$$
\chi(X_s,\mathcal E_s)=\deg(\mathcal E_s)+r(1-g). \tag{13.7}
$$

We include the reduction to line bundles. It is enough to extend the fiber field to an algebraic
closure, since cohomology dimensions, determinant, and degree are unchanged by that extension.
Choose an effective divisor $D$ so positive on every component that $\mathcal E(D)$ is generated
by global sections. If $r>1$, a section can be chosen nonzero at every point. Indeed, in the
incidence variety of pairs $(s,x)$ with $s(x)=0$, the fibers over $x$ have codimension $r$ in the
section space; since the curve has dimension one, its image is a proper closed subset. Such a
section is a subbundle inclusion. After untwisting, it gives

$$
0\longrightarrow\mathcal O_X(-D)
\longrightarrow\mathcal E
\longrightarrow\mathcal E'\longrightarrow0,
$$

where $\mathcal E'$ is a vector bundle of rank $r-1$ and
$\det\mathcal E'=\det\mathcal E\otimes\mathcal O_X(D)$. Induction on $r$, additivity of Euler
characteristic, and the line-bundle formula give

$$
\begin{aligned}
\chi(\mathcal E)
&=(-\deg D+1-g)
 +(\deg\det\mathcal E+\deg D+(r-1)(1-g))\\
&=\deg\det\mathcal E+r(1-g).
\end{aligned}
$$

The incidence argument works component by component on any reduced projective curve, so it covers every
fiber considered here. The finite free model has virtual rank equal to the right side. Neither
$h^0$ nor $h^1$ need be constant separately; their jumps cancel.

### 13.4 Useful vanishing ranges

Let $f:X\to S$ be a smooth proper curve with geometrically connected fibers of genus $g$. Work
locally on $S$, where Section 9.3 supplies a projective embedding. If
$\deg(\mathcal L_s)>2g-2$ on every geometric fiber, duality and negative-degree vanishing give

$$
R^1f_*\mathcal L=0.
$$

Consequently $f_*\mathcal L$ is locally free of rank $d+1-g$ and commutes with arbitrary base change. Degree at least $2g$ makes the evaluation map $f^*f_*\mathcal L\to\mathcal L$ surjective; degree at least $2g+1$ separates every length-two divisor and gives a relative projective embedding.

For nodal or reducible fibers, a total-degree bound alone is insufficient. A bundle may be very
negative on one component and very positive on another. A useful sufficient condition is

$$
\deg(\mathcal L_s|_Z)>
2p_a(Z)-2
$$

for every nonempty connected union $Z$ of irreducible components of every geometric fiber,
including the whole fiber. To prove the claim, suppose a nonzero section of
$\omega_{X_s}\otimes\mathcal L_s^{-1}$ exists and let $Z$ be a connected component of the union
of components on which it is not identically zero. At every boundary branch of $Z$, gluing to
the zero section on the complementary component forces one zero. Since

$$
\deg(\omega_{X_s}|_Z)=2p_a(Z)-2+\#\partial Z,
$$

the induced nonzero section on $Z$ has degree
$2p_a(Z)-2-\deg(\mathcal L_s|_Z)$ after those boundary zeros are removed. The displayed
inequality makes this negative, a contradiction. Duality gives $H^1=0$. Any application using
reducible fibers must verify such componentwise control or prove vanishing separately.

## 14. Relative duality and base change

### 14.1 Trace and the relative pairing

Let $f:X\to S$ be a proper flat finitely presented Gorenstein relative curve with geometrically
reduced fibers over a locally noetherian scheme. This includes the smooth and nodal families of
the standing conventions. Relative duality supplies

$$
\operatorname{tr}_f:R^1f_*\omega_{X/S}\longrightarrow\mathcal O_S.
$$

For a vector bundle $\mathcal E$, multiplication and trace give

$$
R^1f_*\mathcal E\ \times\
f_*(\mathcal E^\vee\otimes\omega_{X/S})
\longrightarrow\mathcal O_S. \tag{14.1}
$$

This identifies

$$
f_*(\mathcal E^\vee\otimes\omega_{X/S})
\simeq(R^1f_*\mathcal E)^\vee. \tag{14.2}
$$

Locally, if $K^0\to K^1$ computes $\mathcal E$, then the transpose dual map with degrees reversed computes $\mathcal E^\vee\otimes\omega_{X/S}$. This is the precise algebra beneath relative Serre duality.

If the cohomology sheaves are locally free, (14.1) is a perfect pairing of vector bundles and also

$$
(f_*\mathcal E)^\vee
\simeq R^1f_*(\mathcal E^\vee\otimes\omega_{X/S}). \tag{14.3}
$$

Fiberwise these are the pairings of Chapter 12.

### 14.2 The base-change theorem

Under these hypotheses, the dualizing sheaf and trace commute with arbitrary base change. For $T\to S$,

$$
\omega_{X/S}|_{X_T}\simeq\omega_{X_T/T},
$$

and the pullback of $\operatorname{tr}_f$ is the trace for $X_T/T$. The finite free model explains compatibility: its matrix pulls back by tensoring, its dual matrix is the transpose, and transposition and evaluation commute with tensor product.

Suppose all geometric fibers are connected and reduced. Then $f_*\mathcal O_X\simeq\mathcal O_S$, compatibly with base change. Duality yields

$$
R^1f_*\omega_{X/S}\simeq\mathcal O_S, \tag{14.4}
$$

through the trace, and

$$
f_*\omega_{X/S}\simeq(R^1f_*\mathcal O_X)^\vee. \tag{14.5}
$$

Indeed, fiberwise $h^0(\mathcal O)=1$, while constancy of Euler characteristic makes $h^1$
locally constant. Section 13.2 therefore makes both pushforwards locally free and base-change
compatible; the unit $\mathcal O_S\to f_*\mathcal O_X$ is an isomorphism on every fiber and hence
an isomorphism. When the genus is constant, both sides of (14.5) are locally free of rank $g$ and
commute with arbitrary base change.

### 14.3 The Hodge bundle in smooth and nodal families

For a proper smooth family with geometrically connected fibers of genus $g$, the **Hodge bundle** is

$$
\mathbb E=f_*\Omega^1_{X/S}=f_*\omega_{X/S}.
$$

It is locally free of rank $g$, with fiber $H^0(X_s,\Omega^1_{X_s/\kappa(s)})$. For a proper
nodal Gorenstein family with geometrically connected fibers of constant arithmetic genus $g$,
the correct definition is still

$$
\mathbb E=f_*\omega_{X/S}.
$$

Its fiber consists of normalization differentials with opposite residues at the branches of each node. Its rank is the arithmetic genus, not merely the sum of the genera of normalized components. Differential forms with node poles account for cycles in the dual graph.

In a smoothing, $f_*\Omega^1_{X/S}$ can acquire torsion or fail base change, whereas $f_*\omega_{X/S}$ is the locally free extension selected by duality. This is why integral families use dualizing differentials.

### 14.4 Failure modes

Each hypothesis has a visible role.

- Without properness, cohomology need not be finite and residue traces acquire boundary terms.

- Without flatness, fiber dimension and arithmetic genus may jump, and specialization of the dualizing sheaf can fail.

- Without the Cohen--Macaulay condition, duality need not be concentrated in one sheaf.

- Without the Gorenstein condition, the dualizing sheaf may not be invertible; canonical Cartier divisors then need not exist.

- Without geometric connectedness, $f_*\mathcal O_X$ has more than one geometric summand, so (14.4) must be replaced by its dual.

- Without locally constant cohomology dimensions, individual pushforwards may fail to be locally free even though the two-term object stays perfect.

These are not technical decorations. The cusp exposes non-smooth differentials, a curve with an embedded point exposes failure of Cohen--Macaulayness, and a reducible curve with unbalanced multidegree exposes failure of total-degree vanishing.

## 15. Divisor and differential tools for later geometry

### 15.1 Abel maps before the Picard scheme

The universal divisor on $X\times_S X^{(d)}$ defines, functorially in $T$,

$$
D\longmapsto\mathcal O_{X_T}(D).
$$

Once the degree-$d$ relative Picard functor is represented, this becomes the Abel map

$$
a_d:X^{(d)}\longrightarrow\operatorname{Pic}^d_{X/S}. \tag{15.1}
$$

Even before representability, its fibers are concrete. On a smooth integral fiber, two divisors have the same image exactly when they are linearly equivalent. With the quotient convention for projective bundles fixed in Book 8, the fiber over $\mathcal L$ is $\mathbf P(H^0(X,\mathcal L)^\vee)$ when sections exist: it parametrizes one-dimensional subspaces of sections. For $d>2g-2$, this dimension is constantly $d-g$, preparing the projective-bundle description used in Picard theory.

### 15.2 The infinitesimal Abel map

Let $X$ be a smooth proper curve over $k$ and $D$ an effective divisor of degree $d$. First-order deformations of $D$ inside $X$ are sections of its normal bundle:

$$
T_DX^{(d)}\simeq H^0(D,\mathcal O_D(D)). \tag{15.2}
$$

Indeed an embedded deformation of the quotient
$\mathcal O_X\twoheadrightarrow\mathcal O_D$ over $k[\epsilon]/(\epsilon^2)$ is obtained by
changing its ideal through an $\mathcal O_X$-linear map
$\mathcal I_D\to\mathcal O_D$. Two changes give the same deformation exactly when the maps
agree. Since $\mathcal I_D=\mathcal O_X(-D)$, this Hom group is
$H^0(D,\mathcal O_D(D))$. Book 8 identifies the length-$d$ Hilbert functor with $X^{(d)}$, so
this calculation also covers nonreduced divisors.

The tangent space to the degree-zero Picard object at the identity is $H^1(X,\mathcal O_X)$.
Indeed a line bundle on $X\times\operatorname{Spec}k[\epsilon]/(\epsilon^2)$ reducing to the
trivial bundle has transition functions $1+\epsilon f_{ij}$. The cocycle condition says that the
$f_{ij}$ form an additive Cech $1$-cocycle, and changing trivializations adds a coboundary. The
differential of (15.1) is the connecting map in

$$
0\longrightarrow\mathcal O_X
\longrightarrow\mathcal O_X(D)
\longrightarrow\mathcal O_D(D)
\longrightarrow0:
$$

$$
da_D:
H^0(D,\mathcal O_D(D))
\xrightarrow{\delta_D}H^1(X,\mathcal O_X). \tag{15.3}
$$

To check the sign, trivialize $\mathcal O_X(D)$ and lift the infinitesimal normal section on each
member of an affine cover. On an overlap, the difference of two lifts is a regular function; the
Cech cocycle of these differences is exactly the displayed boundary. It is also the first-order
change of the transition functions of $\mathcal O_X(D)$, so the convention
$D\mapsto\mathcal O_X(D)$ introduces no minus sign.

Under Serre duality, its transpose is restriction:

$$
H^0(X,\omega_X)
\longrightarrow H^0(D,\omega_X|_D). \tag{15.4}
$$

The proof pairs a principal part representing the displacement with a differential and takes its residue. At $D=dp$, the source of (15.3) and target of (15.4) retain jets through order $d-1$.

### 15.3 A formal-immersion criterion

For a finite-type morphism $\varphi:Y\to Z$ and a $k$-rational point $x$ mapping to $z$, call $\varphi$ a **formal immersion at $x$** if

$$
\widehat{\mathcal O}_{Z,z}\longrightarrow
\widehat{\mathcal O}_{Y,x}
$$

is surjective. This implies surjectivity on cotangent spaces, equivalently injectivity on tangent
spaces. Conversely, suppose the residue fields agree and the cotangent map is surjective. Choose
lifts in $\mathfrak m_{Z,z}$ of generators of
$\mathfrak m_{Y,x}/\mathfrak m_{Y,x}^2$. Nakayama says their images generate
$\mathfrak m_{Y,x}$. Induction on $n$ then shows that
$\mathcal O_{Z,z}\to\mathcal O_{Y,x}/\mathfrak m_{Y,x}^n$ is surjective for every $n$: degree
$n$ monomials in the chosen lifts generate the next associated-graded piece. Taking inverse
limits and using noetherian completeness gives the required surjection of completed local rings.

For the Abel map at $D$, the following are therefore equivalent:

1. its tangent map is injective;
2. the boundary map $\delta_D$ is injective;
3. the restriction map

   $$
   H^0(X,\omega_X)\longrightarrow H^0(D,\omega_X|_D)
   $$

   is surjective.

When the Picard target exists with the stated tangent space, these conditions give a formal immersion. Necessarily $d\leq g$. For distinct rational points, restriction evaluates differentials at them; for $D=dp$, it evaluates their first $d$ power-series coefficients.

The same statement holds on a nodal fiber when $D$ lies in the smooth locus and $\omega_X$ is the dualizing sheaf. Opposite node residues ensure that the residue proof has no extra boundary term. This is the exact criterion later used to turn equality of Abel images into equality in a formal neighborhood.

### 15.4 A reusable theorem package

**Divisors.** On a regular noetherian integral scheme, Cartier and Weil divisors agree. On a proper regular integral curve, divisor classes equal line-bundle classes, principal divisors have degree zero, and

$$
\deg D=\sum_x n_x[\kappa(x):k]
=\chi(\mathcal O(D))-\chi(\mathcal O).
$$

On singular or reducible curves, Cartier divisors remain valid, while conversion from cycles requires separate justification.

**Families.** For a projective flat relative curve and a line bundle, fiberwise degree and Euler characteristic are locally constant. A relative effective Cartier divisor finite flat of rank $d$ has degree $d$ on every fiber. For a smooth projective relative curve these divisors are represented by $X^{(d)}$, with a universal divisor compatible with base change.

**Differentials and duality.** Smooth families have $\omega_{X/S}=\Omega^1_{X/S}$. Proper flat Gorenstein nodal families have invertible, base-change-compatible $\omega_{X/S}$; on a nodal fiber its sections are normalization differentials with simple branch poles and opposite residues. For a vector bundle,

$$
f_*(\mathcal E^\vee\otimes\omega_{X/S})
\simeq(R^1f_*\mathcal E)^\vee,
$$

with perfect fiberwise Serre duality.

**Cohomology and infinitesimals.** Cohomology is locally a two-term finite free model. Fiber dimensions are upper semicontinuous, and fiberwise $H^1$-vanishing gives a locally free pushforward with arbitrary base change. At an effective divisor,

$$
T_DX^{(d)}=H^0(D,\mathcal O_D(D));
$$

the Abel differential is a cohomology boundary, and its transpose restricts dualizing differentials to $D$.

### 15.5 Conclusion

Divisors begin as local equations, but on curves they become a global organizing principle. Regularity converts equations into codimension-one cycles. Rational sections convert cycles into line bundles. Properness forces principal divisors to have degree zero, while flatness makes degree survive specialization. Smoothness identifies finite flat points with Cartier divisors and lets symmetric powers carry their universal family.

Differentials reveal the second half of the story. Residues are invariant local coefficients whose global sum vanishes. At a node, the two branches contribute opposite residues, producing an invertible dualizing sheaf even when ordinary differentials fail. That sheaf turns $H^1$ into the dual of global differentials and gives Riemann--Roch its symmetric form. In a family, the same pairing is encoded by a two-term finite model, so it respects specialization and base change.

Moving a divisor produces a principal part; its Abel class is the resulting cohomology boundary; a global differential tests that boundary by a residue. Thus Picard maps and formal neighborhoods reduce to an explicit restriction map on differentials. The chain

$$
\text{points and jets}
\longrightarrow\text{divisors}
\longrightarrow\text{line bundles}
\longrightarrow\text{cohomology}
\longleftrightarrow\text{differentials}
$$

is the divisor-and-duality toolkit carried forward to Picard schemes, modular curves, and formal-immersion arguments.
