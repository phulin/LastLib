# Blowups and Intersection Theory on Arithmetic Surfaces

## Contents

1. [Why surfaces need a numerical birational language](#1-why-surfaces-need-a-numerical-birational-language)
   - [From models to comparisons](#11-from-models-to-comparisons)
   - [The two dimensions in an arithmetic surface](#12-the-two-dimensions-in-an-arithmetic-surface)
   - [Standing conventions and a hypothesis ledger](#13-standing-conventions-and-a-hypothesis-ledger)
2. [The Rees algebra](#2-the-rees-algebra)
   - [Recording all powers of an ideal](#21-recording-all-powers-of-an-ideal)
   - [Generators, relations, and the symmetric algebra](#22-generators-relations-and-the-symmetric-algebra)
   - [Localization, powers, and integral closure](#23-localization-powers-and-integral-closure)
3. [Blowups from relative Proj](#3-blowups-from-relative-proj)
   - [Construction and projectivity](#31-construction-and-projectivity)
   - [Affine charts](#32-affine-charts)
   - [The universal property](#33-the-universal-property)
   - [Base change and its limits](#34-base-change-and-its-limits)
4. [Exceptional divisors and transforms](#4-exceptional-divisors-and-transforms)
   - [The exceptional ideal and normal directions](#41-the-exceptional-ideal-and-normal-directions)
   - [Total and strict transforms](#42-total-and-strict-transforms)
   - [Multiplicity at a regular point](#43-multiplicity-at-a-regular-point)
   - [Transforming a boundary](#44-transforming-a-boundary)
5. [Blowing up regular surfaces](#5-blowing-up-regular-surfaces)
   - [Regularity of the new surface](#51-regularity-of-the-new-surface)
   - [The exceptional curve and its normal bundle](#52-the-exceptional-curve-and-its-normal-bundle)
   - [Factorization and contraction](#53-factorization-and-contraction)
6. [Resolution steps in arithmetic geometry](#6-resolution-steps-in-arithmetic-geometry)
   - [What resolution must preserve](#61-what-resolution-must-preserve)
   - [Thickness singularities](#62-thickness-singularities)
   - [Embedded resolution of special fibers and sections](#63-embedded-resolution-of-special-fibers-and-sections)
   - [What blowups do not accomplish](#64-what-blowups-do-not-accomplish)
7. [Local intersection multiplicity](#7-local-intersection-multiplicity)
   - [Length of a proper intersection](#71-length-of-a-proper-intersection)
   - [Symmetry, positivity, and transversality](#72-symmetry-positivity-and-transversality)
   - [Branches, tangency, and examples](#73-branches-tangency-and-examples)
   - [A homological interpretation](#74-a-homological-interpretation)
8. [Global intersections on an arithmetic surface](#8-global-intersections-on-an-arithmetic-surface)
   - [Zero-cycles and fiberwise numbers](#81-zero-cycles-and-fiberwise-numbers)
   - [Intersecting a divisor with a vertical curve](#82-intersecting-a-divisor-with-a-vertical-curve)
   - [Common components and self-intersection](#83-common-components-and-self-intersection)
   - [Horizontal self-intersection and the base](#84-horizontal-self-intersection-and-the-base)
9. [Cartier divisors, cycles, and rational equivalence](#9-cartier-divisors-cycles-and-rational-equivalence)
   - [The regular-surface dictionary](#91-the-regular-surface-dictionary)
   - [Intersection with principal divisors](#92-intersection-with-principal-divisors)
   - [Moving only as far as necessary](#93-moving-only-as-far-as-necessary)
10. [Proper maps and the projection formula](#10-proper-maps-and-the-projection-formula)
    - [Pushforward of curves and points](#101-pushforward-of-curves-and-points)
    - [Pullback of divisors](#102-pullback-of-divisors)
    - [The projection formula](#103-the-projection-formula)
    - [Finite maps and degree](#104-finite-maps-and-degree)
11. [The calculus of a point blowup](#11-the-calculus-of-a-point-blowup)
    - [The four fundamental formulas](#111-the-four-fundamental-formulas)
    - [Intersections of strict transforms](#112-intersections-of-strict-transforms)
    - [Infinitely near points and proximity](#113-infinitely-near-points-and-proximity)
12. [Canonical divisors, adjunction, and genus](#12-canonical-divisors-adjunction-and-genus)
    - [Relative canonical divisors](#121-relative-canonical-divisors)
    - [Adjunction](#122-adjunction)
    - [Arithmetic genus and blowup](#123-arithmetic-genus-and-blowup)
    - [The numerical test for exceptional curves](#124-the-numerical-test-for-exceptional-curves)
13. [Special fibers and their intersection matrices](#13-special-fibers-and-their-intersection-matrices)
    - [The fiber relation](#131-the-fiber-relation)
    - [The weighted Laplacian identity](#132-the-weighted-laplacian-identity)
    - [Negativity and its exact kernel](#133-negativity-and-its-exact-kernel)
    - [Examples of fiber matrices](#134-examples-of-fiber-matrices)
14. [Vertical corrections and component pairings](#14-vertical-corrections-and-component-pairings)
    - [Solving the balancing equations](#141-solving-the-balancing-equations)
    - [Integral data and rational corrections](#142-integral-data-and-rational-corrections)
    - [The corrected local pairing](#143-the-corrected-local-pairing)
    - [Functoriality and base change](#144-functoriality-and-base-change)
15. [A reusable intersection package](#15-a-reusable-intersection-package)
    - [The theorem package](#151-the-theorem-package)
    - [A calculation protocol](#152-a-calculation-protocol)
    - [Failure modes](#153-failure-modes)
    - [Conclusion](#154-conclusion)

## 1. Why surfaces need a numerical birational language

### 1.1 From models to comparisons

Book 10 constructed regular proper models of smooth curves over excellent Dedekind schemes. Existence is only the beginning. A model can be blown up at any closed point, producing another regular model with the same generic curve. Sections that met in the old model may separate in the new one; two components that met may cease to meet; a new rational component appears. To decide whether this change improves the geometry, and to compare constructions made from different equations, one needs numbers that remember contact and transform predictably.

Intersection theory provides those numbers. At its most local, it answers a concrete question: if two curves on a regular surface meet at a point, with what multiplicity do they meet? At its most global in this book, it turns a special fiber into a symmetric matrix. That matrix detects redundant exceptional components, governs vertical corrections of horizontal divisors, and prepares the component pairings used in the study of semistable curves and their Jacobians.

Blowups and intersections are inseparable. A blowup replaces a point by its tangent directions. Intersection multiplicity that was concentrated at the point is redistributed among the exceptional curve and the intersections of strict transforms. The central calculation is

$$
(\widetilde D\mathbin{\cdot}\widetilde G)
=(D\mathbin{\cdot}G)-m_x(D)m_x(G)[\kappa(x):\kappa(s)],
$$

when a regular arithmetic surface is blown up at a closed point $x$ of the fiber over $s$. Every factor and sign in this formula will be derived rather than guessed.

### 1.2 The two dimensions in an arithmetic surface

An arithmetic surface has absolute dimension two and relative dimension one. The distinction controls which numerical constructions are canonical. A vertical component is a proper curve over a residue field, so a line bundle on it has an integer degree. Its self-intersection is therefore an integer. A horizontal curve is finite over the Dedekind base, not a proper curve over a field. Its normal bundle has a class on that horizontal arithmetic curve, but there is no canonical integer degree over an arbitrary base.

This explains an apparent tension. Local intersections at a closed fiber are honest nonnegative integers. Vertical component intersections and self-intersections are also integers, possibly negative. But a global pairing of two arbitrary divisors on an arithmetic surface naturally takes values in zero-cycles or divisor classes on the base. It becomes a single integer only after the base carries a specified degree map. We will never silently turn the latter data into an integer.

The special fiber itself illustrates the relative nature of the theory. If $\pi$ is a uniformizer at $s$, then

$$
X_s=\operatorname{div}(\pi)=\sum_i m_i\Gamma_i.
$$

As a Cartier divisor it is principal, and its associated line bundle is trivial. Consequently $(X_s\mathbin{\cdot}\Gamma_i)=0$ for every vertical component. Yet a horizontal section meets $X_s$ once. There is no contradiction: the restriction of a principal divisor to the proper vertical curve has degree zero, whereas its divisor on a horizontal arithmetic curve records a valuation at the boundary point $s$.

### 1.3 Standing conventions and a hypothesis ledger

Throughout, $S$ is an excellent connected Dedekind scheme with generic point $\eta$ and function field $K$. A **regular arithmetic surface** is an integral regular scheme $X$, proper and flat over $S$, of relative dimension one. Its generic fiber $X_K$ is normally assumed smooth and geometrically connected. Results local at a closed point of $S$ are stated after replacing $S$ by the spectrum of the discrete valuation ring $R=\mathcal O_{S,s}$, with uniformizer $\pi$ and residue field $k=\kappa(s)$.

A curve on $X$ means an integral closed subscheme of codimension one. It is horizontal if it dominates $S$ and vertical if it lies in a closed fiber. Since $X$ is regular, every Weil divisor is Cartier. For a divisor $D$ and a vertical integral curve $C$ over $k$, our convention is

$$
(D\mathbin{\cdot}C)=\deg_k\mathcal O_X(D)|_C.
$$

Thus residue-field degrees are built into every global fiberwise intersection. If $x$ is a closed point of $C$, a length at $x$ contributes its length multiplied by $[\kappa(x):k]$.

Regularity is essential for the clean Cartier--Weil dictionary and for finite free resolutions at intersections. Properness of vertical curves is essential for degree. Flatness makes fibers effective Cartier divisors and relates their multiplicities to the base valuation. Excellence is used for finite normalization, resolution, and contraction, but not for elementary blowup charts. When a statement needs only a noetherian scheme or a regular local surface, it will say so.

Book 9 supplies Cartier divisors, line bundles, degree, dualizing sheaves, and Riemann--Roch on proper curves. Book 10 supplies normalization, resolution of excellent surfaces, regular proper models, and the existence of contractions of exceptional curves. We recall these inputs only where their conventions matter and prove the intersection calculations that were deliberately deferred.

## 2. The Rees algebra

### 2.1 Recording all powers of an ideal

An ideal $I$ describes a center, but the first power alone does not record how functions vanish to higher order there. A blowup must remember every order simultaneously. Introduce a variable $T$ of degree one and form the graded algebra

$$
\mathcal R_A(I)=A[IT]
=\bigoplus_{n\geq0}I^nT^n\subseteq A[T].
$$

This is the **Rees algebra**. Multiplication works because $I^mI^n=I^{m+n}$. The degree-zero part is $A$, while degree one is a copy of $I$. If $I=(f_0,\ldots,f_r)$, the algebra is generated over $A$ by $f_0T,\ldots,f_rT$ and is therefore of finite type. For a coherent ideal sheaf $\mathcal I$ on a noetherian scheme $X$, the sheafified construction

$$
\mathcal R(\mathcal I)=\bigoplus_{n\geq0}\mathcal I^n
$$

is a quasi-coherent graded algebra of finite type.

Two related graded objects answer different questions. The associated graded algebra

$$
\operatorname{gr}_I(A)=\bigoplus_{n\geq0}I^n/I^{n+1}
$$

records the successive normal layers of the center. The Rees algebra records the modification away from and above the center. Algebraically,

$$
\mathcal R_A(I)/I\mathcal R_A(I)\simeq\operatorname{gr}_I(A).
$$

This identity will identify the exceptional fiber with the projectivized tangent cone.

**Example.** If $I=(f)$ is principal and $f$ is a non-zero-divisor, then

$$
\mathcal R_A(I)\simeq A[U],\qquad U\longmapsto fT.
$$

Its projective spectrum over $A$ is just $\operatorname{Spec}A$. This is the first indication that blowup does nothing to an already invertible center.

### 2.2 Generators, relations, and the symmetric algebra

The symmetric algebra $\operatorname{Sym}_A(I)$ is the freest graded algebra generated by the module $I$. Multiplication inside $A$ can impose additional relations, so there is a natural surjection

$$
\operatorname{Sym}_A(I)\twoheadrightarrow\mathcal R_A(I).
$$

It need not be an isomorphism. Confusing the two replaces the blowup by a possibly larger projective bundle containing spurious torsion. If $I=(f_0,\ldots,f_r)$, there is a presentation

$$
A[U_0,\ldots,U_r]\twoheadrightarrow\mathcal R_A(I),
\qquad U_i\longmapsto f_iT.
$$

The evident equations $f_iU_j-f_jU_i$ lie in the kernel, but they do not always generate it. On a chart where $f_i$ is inverted, all relations are captured by $U_j/U_i=f_j/f_i$; globally, torsion supported where the chosen generator vanishes can add equations.

For $A=k[x,y]$ and $I=(x,y)$, the only essential homogeneous relation is

$$
xU_1-yU_0=0.
$$

Thus the blowup sits inside $\mathbf A^2_k\times\mathbf P^1_k$ as the incidence surface $xU_1=yU_0$. Above a nonzero point $(x,y)$, the projective coordinate is forced to be $[x:y]$; above the origin, every direction $[U_0:U_1]$ occurs.

The construction is unchanged by multiplying the ideal by an invertible ideal. Locally such a multiplication only shifts each graded piece by a tensor power of a line bundle, and relative projective spectrum ignores that twist. It is also unchanged by replacing $I$ with $I^q$ for $q>0$, because

$$
\bigoplus_{n\geq0}I^{qn}
$$

is the $q$-th Veronese subalgebra of the Rees algebra, and a graded algebra and its positive Veronese have the same projective spectrum. Hence $(x^2,xy,y^2)$ and $(x,y)$ define the same blowup, although their Rees algebras are not the same graded algebra.

### 2.3 Localization, powers, and integral closure

Rees algebras localize exactly:

$$
W^{-1}\mathcal R_A(I)\simeq
\mathcal R_{W^{-1}A}(W^{-1}I).
$$

Indeed localization commutes with finite products of ideals. Consequently blowup is local on the target and is an isomorphism wherever $I$ is invertible. This permits point-by-point modifications on a surface.

If $A$ is a normal domain, the Rees algebra need not be normal. Its normalization inside $A[T]$ has degree-$n$ piece $\overline{I^n}T^n$, where $\overline{I^n}$ is the integral closure of the ideal $I^n$. The resulting normalized blowup is

$$
\operatorname{Proj}\bigoplus_{n\geq0}\overline{I^n}T^n.
$$

Over an excellent finite-type surface this normalization is finite. It follows that the normalized blowup remains projective and birational. This construction is needed when one starts from a normal singular surface. When one blows up a regular surface at a regular closed point, the ordinary blowup is already regular, so normalization adds nothing.

Integral closure also explains why different ideals can determine the same normalized blowup. Divisorial valuations $v$ centered on $A$ test integral dependence by inequalities $v(f)\geq v(I)$. The exceptional prime divisors of the normalized blowup are precisely the finite collection of valuations needed to record the asymptotic orders of powers of $I$. In this book that viewpoint is used only to understand resolution steps; no higher-dimensional theory of Rees valuations is required.

## 3. Blowups from relative Proj

### 3.1 Construction and projectivity

Let $X$ be noetherian and $\mathcal I$ a coherent ideal. Its blowup is

$$
b:Y=\operatorname{Bl}_{\mathcal I}(X)
=\operatorname{Proj}_X\mathcal R(\mathcal I)\longrightarrow X.
$$

Because the Rees algebra is generated in degree one by a coherent module, $b$ is projective. If the center $Z=V(\mathcal I)$ is nowhere dense in an integral $X$, then $b$ is an isomorphism over $X\setminus Z$ and is birational. Projectivity, rather than mere properness, is useful: composites of blowups remain projective, and ample line bundles keep track of the modification.

There is a conventional sign that must be settled once. On $Y$, the extended ideal is invertible and

$$
\mathcal I\mathcal O_Y=\mathcal O_Y(1)=\mathcal O_Y(-E),
$$

where $E$ is the effective exceptional Cartier divisor when the center is nowhere dense and $X$ is integral. Thus the relatively ample tautological bundle $\mathcal O_Y(1)$ is $\mathcal O_Y(-E)$, not $\mathcal O_Y(E)$. Restricted to an exceptional projective line, $\mathcal O_Y(-E)$ has degree $1$, so $\mathcal O_Y(E)$ has degree $-1$.

### 3.2 Affine charts

Suppose $X=\operatorname{Spec}A$ and $I=(f_0,\ldots,f_r)$. The standard open set on which $f_iT$ is nonzero has coordinate ring

$$
A[I/f_i]
=A[f_0/f_i,\ldots,f_r/f_i]\subseteq A_{f_i},
$$

when $A$ is a domain and $f_i\neq0$. The notation means the subalgebra generated by the indicated fractions; it does not mean a polynomial algebra with unrelated new variables.

For the origin in $\mathbf A^2_k$, take $I=(x,y)$. The $x$-chart has coordinates $x,t$ with $y=xt$; the $y$-chart has coordinates $s,y$ with $x=sy$. On their overlap $s=t^{-1}$. The exceptional divisor is $x=0$ in the first chart and $y=0$ in the second, and these affine lines glue to $\mathbf P^1_k$.

For a less transverse example, blow up $I=(x,y)$ in the plane curve equation $y^2=x^3$. On the $x$-chart, substitution $y=xt$ gives

$$
x^2(t^2-x)=0.
$$

The factor $x^2$ is the exceptional part of the total transform; the strict transform is $t^2=x$. It is smooth, but it is tangent to the exceptional curve $x=0$. Thus resolving a curve and making the total boundary normal crossing are different tasks.

### 3.3 The universal property

The blowup is characterized by the problem it solves.

**Theorem 3.1 (universal property).** Let $g:T\to X$ be a morphism such that $\mathcal I\mathcal O_T$ is an invertible ideal generated locally by a non-zero-divisor. Then there is a unique factorization

$$
T\longrightarrow\operatorname{Bl}_{\mathcal I}(X)
\longrightarrow X.
$$

**Proof strategy.** Where one pullback $g^*f_i$ generates $\mathcal I\mathcal O_T$, every ratio $g^*f_j/g^*f_i$ is regular. These ratios should define the map into the $i$-th blowup chart.

Choose the open cover of $T$ on which $g^*f_i$ generates. The relations in $A[I/f_i]$ hold for the corresponding ratios, giving maps to the standard charts. On overlaps the ratios agree, so the maps glue. The opens cover because an invertible ideal is locally generated by any member whose image generates its one-dimensional fiber. Uniqueness follows chartwise. $\square$

The non-zero-divisor condition prevents the entire source from lying in the center. A more general formulation uses an invertible quotient of $g^*\mathcal I$; for the integral surfaces and dominant maps used here, the ideal formulation is sufficient.

Two consequences are immediate. Blowing up an invertible ideal is an isomorphism. And if $h:X'\to X$ makes $\mathcal I\mathcal O_{X'}$ invertible, then every further map with the same property factors through the blowup. This canonical factorization is why blowups resolve rational maps defined by ratios of generators.

### 3.4 Base change and its limits

Let $X'\to X$ be flat. Flatness preserves products and injections sufficiently to give

$$
\mathcal R(\mathcal I)\otimes_{\mathcal O_X}\mathcal O_{X'}
\simeq\mathcal R(\mathcal I\mathcal O_{X'}).
$$

Relative Proj then yields

$$
\operatorname{Bl}_{\mathcal I}(X)\times_XX'
\simeq\operatorname{Bl}_{\mathcal I\mathcal O_{X'}}(X').
$$

Arbitrary base change is not safe: tensoring can introduce torsion, and the natural map $I^n\otimes B\to(IB)^n$ need not be injective. The fiber of a blowup over a point is therefore best computed through the associated graded algebra, not by an unqualified base-change slogan.

For a regular closed immersion $Z\hookrightarrow X$, the normal cone is a vector bundle and

$$
b^{-1}(Z)=\mathbf P(N_{Z/X}).
$$

For a singular center it is instead $\operatorname{Proj}\operatorname{gr}_{\mathcal I}(\mathcal O_X)$, the projectivized normal cone, which may be nonreduced or reducible. This distinction explains why exceptional loci of normalized blowups of singular surfaces can be more complicated than projective spaces.

## 4. Exceptional divisors and transforms

### 4.1 The exceptional ideal and normal directions

Assume $X$ is integral and the coherent ideal $\mathcal I$ is nonzero. Its pullback to $Y=\operatorname{Bl}_{\mathcal I}X$ defines an effective Cartier divisor $E$ by

$$
\mathcal O_Y(-E)=\mathcal I\mathcal O_Y.
$$

Set-theoretically, $E$ is the inverse image of the center, though its scheme structure records multiplicity. If the center is a regular closed subscheme, then

$$
E\simeq\mathbf P(N_{Z/X}),
\qquad
\mathcal O_E(-E)\simeq\mathcal O_{\mathbf P(N_{Z/X})}(1).
$$

At a regular closed point $x$ of a surface, $N_{x/X}$ is a two-dimensional vector space over $\kappa(x)$, so $E\simeq\mathbf P^1_{\kappa(x)}$. Its points are one-dimensional tangent directions. A curve through $x$ meets $E$ in the projectivized tangent cone of that curve; a smooth curve chooses one direction, while a curve of multiplicity $m$ meets $E$ in a divisor of degree $m$.

### 4.2 Total and strict transforms

Several objects called “the transform” must be separated.

For a Cartier divisor $D$ on $X$, the **total transform** is the Cartier pullback $b^*D$. If $D$ is effective with local equation $f$, it is cut out on $Y$ by the same rational function $f$. It includes every exceptional factor acquired by $f$.

For an integral closed subscheme $W\not\subseteq Z$, the **strict transform** $\widetilde W$ is the closure in $Y$ of

$$
b^{-1}(W\setminus Z).
$$

For a general closed subscheme, the scheme-theoretic strict transform is obtained from the inverse image by removing sections killed by a power of the exceptional ideal; algebraically this is saturation. Simply taking the inverse image gives the total transform and usually adds an unwanted exceptional component.

If an effective Cartier divisor $D$ has multiplicity $m$ along the center, then

$$
b^*D=\widetilde D+mE. \tag{4.1}
$$

Here “multiplicity along the center” means that a local equation lies in $I^m$ but not generically in $I^{m+1}$. At a regular point with maximal ideal $\mathfrak m_x$, it is the order

$$
m_x(D)=\max\{m:f\in\mathfrak m_x^m\}.
$$

The equality follows on each chart by dividing the pulled-back equation by the largest common exceptional factor. It is an equality of Cartier divisors, not merely supports.

### 4.3 Multiplicity at a regular point

Let $(A,\mathfrak m,k)$ be a two-dimensional regular local ring and let $f\in\mathfrak m^m\setminus\mathfrak m^{m+1}$. Its initial form

$$
\operatorname{in}_m(f)\in\mathfrak m^m/\mathfrak m^{m+1}
\simeq\operatorname{Sym}^m_k(\mathfrak m/\mathfrak m^2)
$$

is a homogeneous polynomial of degree $m$ on the tangent plane. On the exceptional projective line it cuts out $\widetilde D\cap E$. Consequently

$$
(\widetilde D\mathbin{\cdot}E)=m[\kappa(x):k_0], \tag{4.2}
$$

when the surface is over a residue field $k_0$ and $x$ has residue field $k$. Repeated tangent directions appear with multiplicity. Thus the exceptional curve does more than separate curves: it displays their leading homogeneous terms.

If $D$ is smooth at $x$, then $m=1$ and its strict transform meets $E$ at one $k$-rational direction over $k$. If two smooth curves have distinct tangent directions, their strict transforms are disjoint above $x$. If they share a tangent direction, they still meet on $E$, and another blowup measures the next term of contact.

### 4.4 Transforming a boundary

Suppose $B=\sum a_iB_i$ is a divisor marking a special fiber together with horizontal sections. Blowing up a point where several $B_i$ meet replaces the reduced boundary by

$$
B'_{\mathrm{red}}=E+\sum_i\widetilde B_i,
$$

while the total transform is

$$
b^*B=\sum_i a_i\widetilde B_i+
\left(\sum_i a_i m_x(B_i)\right)E.
$$

The reduced boundary tracks normal crossings; the total transform tracks divisor multiplicities. They answer different questions and must not be interchanged.

For example, if two smooth components of multiplicities $a$ and $b$ meet transversely at $x$, then the new exceptional component has multiplicity $a+b$ in the total fiber. It meets each strict transform once. If $x$ lies smoothly on just one component of multiplicity $a$, the exceptional component also has multiplicity $a$. This elementary rule drives the multiplicity labels in resolution graphs.

## 5. Blowing up regular surfaces

### 5.1 Regularity of the new surface

Let $X$ be a regular noetherian surface and $x$ a closed point. Choose a regular system of parameters $(u,v)$ in $A=\mathcal O_{X,x}$. The blowup of $\mathfrak m_x=(u,v)$ has two charts. On the $u$-chart set $v=ut$; its local coordinate algebra is $A[t]/(v-ut)$, viewed in $A_u$. On the $v$-chart set $u=sv$.

On the first chart, points of the exceptional divisor have $u=0$ and a chosen value of $t$. If the value is represented by an irreducible polynomial $q(t)$ over $\kappa(x)$, then $u$ together with a lift of $q(t)$ generates the maximal ideal of the local ring, whose dimension is two. Thus the local ring is regular. The second chart is identical. This proves:

**Theorem 5.1.** The blowup of a regular surface at a closed point is regular. It is projective and birational, is an isomorphism away from the point, and its exceptional divisor is $\mathbf P^1_{\kappa(x)}$.

No algebraic closure of the residue field is needed. The exceptional curve may acquire more closed points after extending the residue field, but it is already a projective line over $\kappa(x)$.

Blowing up a nonreduced zero-dimensional center on a regular surface need not remain regular. Nor does blowing up the reduced singular point of a singular surface automatically resolve it. Resolution in Book 10 permits chosen ideals and intermediate normalization precisely because the simple regular-point theorem has narrower hypotheses.

### 5.2 The exceptional curve and its normal bundle

Let $b:Y\to X$ be the blowup at $x$. The tautological sign convention gives

$$
\mathcal O_E(-E)\simeq\mathcal O_{\mathbf P^1_{\kappa(x)}}(1),
$$

so

$$
\mathcal O_E(E)\simeq\mathcal O_{\mathbf P^1_{\kappa(x)}}(-1).
$$

If $x$ lies over $s$ and $d_x=[\kappa(x):\kappa(s)]$, the degree over $\kappa(s)$ is therefore

$$
E^2=-d_x. \tag{5.1}
$$

The frequently written formula $E^2=-1$ assumes the center is rational over the ground residue field, or measures degree over $\kappa(x)$. Formula (5.1) is the correct integral convention on an arithmetic surface.

The negative normal degree says that $E$ cannot move in a family inside $Y$. Infinitesimal deformations of $E$ are sections of its normal bundle, and $H^0(\mathbf P^1,\mathcal O(-1))=0$. This rigidity is the geometric reason an exceptional curve can be contracted.

### 5.3 Factorization and contraction

Book 10 established that a vertical projective line with normal degree $-1$ can be contracted to a regular point, and that the contraction is inverse to a point blowup. Intersection theory sharpens the criterion. Over an algebraically closed residue field, a vertical integral curve $E$ on a regular surface is exceptional of the first kind precisely when

$$
E\simeq\mathbf P^1,\qquad E^2=-1.
$$

Over a nonclosed field one must retain the actual form of the curve and its normal bundle; the numerical equality over the smaller field becomes $E^2=-[H^0(E,\mathcal O_E):k]$ when $E$ is a projective line over its constant field. A negative self-intersection alone is not enough: a $(-2)$-curve cannot be contracted to a regular point, and a curve of positive genus remains nonexceptional regardless of negativity.

A proper birational morphism between regular surfaces that is an isomorphism on a dense open can, in the surface situations used here, be factored into point blowups and inverse contractions after resolving its graph. This reduces comparison questions to the formulas for one point blowup. Factorization is not claimed for arbitrary higher-dimensional birational maps.

## 6. Resolution steps in arithmetic geometry

### 6.1 What resolution must preserve

The resolution theorem of Book 10 starts from a normal excellent surface and produces a regular one by projective modifications supported on the singular locus. Here our concern is more focused: what do the individual steps do to curves, fibers, and their multiplicities?

For a model over a discrete valuation ring, every center used to repair the bad fiber should be vertical. Then the generic curve is unchanged. If a chosen open is already regular with a normal-crossing boundary, the centers should avoid it. After the total space becomes regular, further point blowups may be required to make the reduced special fiber and marked sections meet with normal crossings. This second process is **embedded resolution of the boundary**, not resolution of the surface.

Three quantities guide a local step:

1. the multiplicity of the surface equation or boundary at the center;
2. the number and tangent directions of branches;
3. the multiplicities carried by fiber components.

The first two decide where another blowup is needed. The third must be transported by total transform, because the whole special fiber remains the divisor of the same uniformizer.

### 6.2 Thickness singularities

The standard normal surface singularity arising after ramified base change of a node is

$$
X_n:\quad xy=\pi^n,\qquad n>1.
$$

Its total space is singular at $(x,y,\pi)$, although the punctured surface is regular. Blowing up a suitable ideal such as $(x,\pi)$ and taking the strict transform produces one regular chart and one chart with equation

$$
x_1y=\pi^{n-1}.
$$

Thus the thickness decreases. Iteration ends at $xy=\pi$, whose total space is regular and whose special fiber has two components crossing transversely.

Over an algebraically closed residue field, the minimal resolution of $xy=\pi^n$ inserts a chain of $n-1$ smooth rational curves between the strict transforms of $x=0$ and $y=0$. Consecutive curves meet once and no other pair meets. Each exceptional curve has self-intersection $-2$. This can be checked directly on the recursive charts; it also follows from the fiber relation of Chapter 13, since every inserted component has multiplicity one and meets its two neighbors transversely. The local intersection matrix of the exceptional chain is therefore the negative Cartan matrix of a chain.

The exact shape depends on whether one resolves the singular surface, the marked boundary, or both. A nonminimal sequence can add $(-1)$-vertices without changing the generic curve. Intersection numbers distinguish these choices.

### 6.3 Embedded resolution of special fibers and sections

On a regular surface a special fiber can still have a cusp, a tangency, or three components through one point. Point blowups repair these boundary defects.

Consider a cusp $y^2=x^3$ in a special fiber of a regular total space. The first blowup gives strict transform $t^2=x$, smooth but tangent to the exceptional divisor. Blowing up their tangency separates the tangent directions, but at the new point the reduced total transform can have three branches; a further blowup is needed for a strict normal-crossing divisor, where at most two components meet at any point. Thus “the curve is smooth after one blowup” does not imply “the boundary has normal crossings after one blowup.”

If two smooth sections meet in a closed fiber with local equations $v=0$ and $v-u^r=0$, their local intersection multiplicity is $r$. Blowing up their common point decreases the remaining contact by one: on the $u$-chart their strict transforms are $t=0$ and $t=u^{r-1}$. After $r$ blowups the strict transforms are separated. The successive exceptional curves remember every order of coincidence.

At every blowup, the multiplicity of the exceptional component in the total fiber is the sum of the multiplicities of the components through the center, counted with their local orders. Therefore the identity

$$
\operatorname{div}_Y(\pi)=b^*\operatorname{div}_X(\pi)
$$

is preserved automatically. This is the safest way to label a resolution graph: compute the total transform of the fiber, never infer multiplicities from the reduced picture.

### 6.4 What blowups do not accomplish

Resolution of a model is not semistable reduction. A regular total space can have a nonreduced special fiber, and point blowups do not in general remove its multiplicities. A finite extension of the base may be necessary before a reduced nodal fiber exists. Conversely, ramified base change can turn a regular node $xy=\pi$ into the singular surface $xy=\pi'^e$, requiring resolution again.

Normalization and blowup also play different roles. Normalization separates integral branches and repairs failure of integral closure; blowup changes birational geometry and tangent directions. The normalization of a curve cusp resolves the curve, but normalization alone does not generally resolve a two-dimensional surface singularity. A normalized blowup deliberately combines both operations.

Finally, resolution is not minimality. Blowing up a perfectly regular point creates a new exceptional curve and makes the model less minimal. The numerical theory below tells when a component is the artificial $(-1)$-curve of such a step and when a negative component is intrinsic to the fiber.

## 7. Local intersection multiplicity

### 7.1 Length of a proper intersection

Let $(A,\mathfrak m,k(x))$ be the regular local ring of a surface at a closed point $x$. Let $C$ and $D$ be effective Cartier curves through $x$, with local equations $f$ and $g$. Suppose they have no common irreducible component through $x$. Then $(f,g)$ is $\mathfrak m$-primary, and the **local intersection multiplicity** is

$$
i_x(C,D)=\operatorname{length}_A A/(f,g). \tag{7.1}
$$

The quotient is the scheme-theoretic intersection near $x$. Its length counts a transverse point once, a tangency more than once, and nilpotent thickness exactly. Multiplying either equation by a unit does not change the quotient, so the number depends only on the Cartier divisors.

Why is the length finite? A two-dimensional regular local ring is Cohen--Macaulay. The assumption of no common curve component means $(f,g)$ has height two. Hence $f,g$ form a regular sequence, and the quotient has dimension zero. A noetherian local ring of dimension zero is artinian and has finite length.

For signed Cartier divisors with no common components, extend (7.1) bilinearly. Local values can then be negative because divisor coefficients may be negative; positivity applies to effective curves.

### 7.2 Symmetry, positivity, and transversality

The formula is symmetric:

$$
i_x(C,D)=i_x(D,C),
$$

because the ideals $(f,g)$ and $(g,f)$ agree. It is additive in each divisor. For example, if $D=D_1+D_2$ locally has equation $g_1g_2$, then the exact sequence induced by multiplication, or equivalently additivity of orders on the one-dimensional ring $A/(f)$, gives

$$
i_x(C,D)=i_x(C,D_1)+i_x(C,D_2),
$$

provided no common component occurs.

For effective curves, $i_x(C,D)>0$ exactly when both pass through $x$. Moreover

$$
i_x(C,D)\geq m_x(C)m_x(D). \tag{7.2}
$$

One proof passes to the blowup and uses the transform formula of Chapter 11: the product of multiplicities is the contribution already visible on the first exceptional divisor, while all remaining intersections are nonnegative. Equality holds when the initial forms have no common point on the exceptional projective line, equivalently when the tangent cones share no tangent direction.

If both curves are smooth at $x$, then $i_x(C,D)=1$ precisely when their tangent lines are distinct. Algebraically, their equations form a regular system of parameters, so $A/(f,g)\simeq k(x)$. Tangency makes the images of $f$ and $g$ dependent in $\mathfrak m/\mathfrak m^2$ and forces length at least two.

### 7.3 Branches, tangency, and examples

In $k[[u,v]]$, the curves $v=0$ and $v-u^r=0$ have

$$
i_0(v,v-u^r)
=\operatorname{length}k[[u]]/(u^r)=r.
$$

Thus intersection multiplicity is the order of contact. The axes $u=0$ and $v=0$ meet with multiplicity one. The line $v=0$ and cusp $v^2-u^3=0$ have quotient $k[[u]]/(u^3)$ and multiplicity three, whereas the line $u=0$ meets the cusp with multiplicity two. The tangent line sees the larger number.

Residue fields matter globally but not in (7.1): length is an integer intrinsic to the local ring. If the point lies over $s$ with residue extension $\kappa(x)/\kappa(s)$, its contribution to the intersection number over the base field is

$$
i_x(C,D)[\kappa(x):\kappa(s)]. \tag{7.3}
$$

Omitting this factor makes intersection fail to agree with degree after a non-rational point splits over a field extension.

There is also a useful one-branch interpretation. If $C$ is integral and its normalization has points $q$ above $x$, then, under the proper-intersection hypothesis,

$$
i_x(C,D)=
\sum_{q\mapsto x}
\operatorname{ord}_q(g|_C)[\kappa(q):\kappa(x)]
$$

when the normalization is finite and the orders are computed in its discrete valuation rings. This formula reveals separate branches, but the length definition remains valid without first normalizing.

### 7.4 A homological interpretation

The length formula works because two Cartier equations meeting properly form a regular sequence. More generally, the intersection of coherent sheaves on a regular surface is measured by the Euler characteristic

$$
\chi_x(\mathcal F,\mathcal G)
=\sum_{j\geq0}(-1)^j
\operatorname{length}
\operatorname{Tor}^{A}_j(\mathcal F_x,\mathcal G_x).
$$

For $\mathcal F=A/(f)$ and $\mathcal G=A/(g)$ with no common component, the resolution

$$
0\longrightarrow A\xrightarrow{f}A\longrightarrow A/(f)\longrightarrow0
$$

shows that the first torsion group is the elements of $A/(g)$ killed by $f$. Since $f$ is a non-zero-divisor modulo $g$, this group vanishes. Hence the Euler characteristic reduces to $\operatorname{length}A/(f,g)$.

This viewpoint explains both the regularity hypothesis and the danger of improper intersections. If $C$ and $D$ share a component, the tensor product is supported in dimension one and has infinite local length; the elementary formula is not defined. Self-intersection must instead be defined through the normal line bundle or by moving within a rational-equivalence class.

## 8. Global intersections on an arithmetic surface

### 8.1 Zero-cycles and fiberwise numbers

Let $D$ and $G$ be Cartier divisors on a regular arithmetic surface $X/S$ with no common irreducible component. Their scheme-theoretic intersections form a finite set of closed points if their horizontal generic divisors are disjoint. The intersection zero-cycle is

$$
D\mathbin{\cdot}G
=\sum_x i_x(D,G)[x].
$$

For a closed point $s\in S$, push the part supported on $X_s$ to $s$:

$$
(D\mathbin{\cdot}G)_s
=\sum_{x\in X_s}i_x(D,G)[\kappa(x):\kappa(s)]. \tag{8.1}
$$

This is an integer. It is nonnegative for effective divisors without common components. Only finitely many $s$ contribute when the generic divisors are disjoint and $X$ is proper.

If the generic divisors meet on $X_K$, their closures contain horizontal intersection data rather than a finite vertical zero-cycle; for a relative curve, two distinct horizontal prime divisors have disjoint generic points, so the main arithmetic applications are in the finite situation above. The collection $\sum_s(D\cdot G)_s[s]$ is a divisor on $S$, not canonically a single integer. A specified degree on divisors of $S$ may be applied afterward.

### 8.2 Intersecting a divisor with a vertical curve

Let $C$ be an integral component of $X_s$. It is a proper curve over $k=\kappa(s)$. For any Cartier divisor $D$, including one that contains $C$, define

$$
(D\mathbin{\cdot}C)=\deg_k\mathcal O_X(D)|_C. \tag{8.2}
$$

If $D$ and $C$ meet properly, (8.2) equals the sum of local lengths in (8.1). To prove this, restrict the rational section defining $D$ to $C$. Its zero divisor has local order equal to the length $\mathcal O_{X,x}/(f_D,f_C)$, and degree sums these orders with residue-field weights.

Definition (8.2) is additive in $D$ and in vertical one-cycles. It depends only on the line bundle class of $D$ near $C$. It also handles self-intersection: since $C$ is Cartier on the regular surface,

$$
C^2=\deg_k\mathcal O_X(C)|_C
=\deg_k N_{C/X}. \tag{8.3}
$$

Thus self-intersection is the degree of the normal bundle. It may be negative because a normal bundle need not have an effective section.

### 8.3 Common components and self-intersection

Suppose $V=\sum a_iC_i$ and $W=\sum b_jC_j$ are vertical divisors in one fiber. Define

$$
(V\mathbin{\cdot}W)=
\sum_{i,j}a_ib_j(C_i\mathbin{\cdot}C_j),
$$

using (8.2), even when $i=j$. Symmetry is not automatic from the definition but follows from Cartier divisor theory. If $i\neq j$, both sides are the same local-length sum. For $i=j$ symmetry is tautological; bilinearity completes the argument.

For a vertical curve $C$ and a principal divisor $\operatorname{div}(f)$,

$$
(\operatorname{div}(f)\mathbin{\cdot}C)=0. \tag{8.4}
$$

Indeed $\mathcal O_X(\operatorname{div}(f))$ is trivial, so its restriction has degree zero. This is the rational-equivalence invariance needed for the vertical pairing.

Self-intersection is not the number of points at which a curve meets itself. It is a deformation-theoretic degree. A fiber component often has negative self-intersection even when it is smooth. For example, the exceptional curve of a rational point blowup has normal bundle $\mathcal O(-1)$ and hence square $-1$.

### 8.4 Horizontal self-intersection and the base

Let $H$ be a horizontal Cartier curve. Its normal bundle $N_{H/X}=\mathcal O_X(H)|_H$ is a line bundle on the finite $S$-scheme $H$, or on its normalization when needed. This is the intrinsic self-intersection datum. Taking its norm produces a line-bundle class on $S$ under the usual finite-flat hypotheses.

There is no canonical integer $H^2$ over an arbitrary Dedekind scheme. Over a proper base curve over a field, one may take the degree of the norm. Over the spectrum of a discrete valuation ring, a rational trivialization gives a local order, but changing the trivialization changes that order by a principal divisor on the base. In arithmetic intersection theory one adds archimedean or metric data to obtain a global real number; that theory lies outside our scope.

Whenever a formula below uses $D^2$ numerically, either $D$ is vertical, the ambient surface is proper over a field, or a degree map on the base has been explicitly fixed. Blowup identities also hold before taking degrees, as identities of intersection zero-cycles or line-bundle classes. This convention prevents a local calculation from masquerading as an absolute global invariant.

## 9. Cartier divisors, cycles, and rational equivalence

### 9.1 The regular-surface dictionary

On a regular noetherian integral surface, every codimension-one local ring is a discrete valuation ring and every Weil divisor is Cartier. Thus a divisor may be viewed in three compatible ways:

$$
\text{prime curves with integer coefficients}
\longleftrightarrow
\text{rational local equations modulo units}
\longleftrightarrow
\text{line bundles with rational sections}.
$$

The cycle picture makes pushforward transparent. The Cartier picture makes pullback and local intersection transparent. The line-bundle picture handles common components and self-intersection. Regularity is what permits movement among all three without a class-group obstruction.

A zero-cycle is a finite sum $z=\sum n_x[x]$ of closed points. If all points lie over $s$, its degree over $k(s)$ is

$$
\deg_{k(s)}z=\sum_xn_x[\kappa(x):\kappa(s)].
$$

This is the final step from a scheme-theoretic intersection to the integer convention used throughout.

### 9.2 Intersection with principal divisors

Rational equivalence for divisors is generated by $\operatorname{div}(f)$. On a proper curve over a field, a principal divisor has degree zero. Therefore for every vertical proper curve $C$,

$$
(D+\operatorname{div}(f)\mathbin{\cdot}C)
=(D\mathbin{\cdot}C).
$$

This proves that the vertical intersection pairing depends only on the line bundle class of its first argument. Symmetry gives the same for the second vertical argument.

One must not overextend this statement. A horizontal curve over a local Dedekind base has a missing generic boundary from the viewpoint of the residue field, and the divisor of a base uniformizer on it is its closed fiber, of positive local degree. Thus local intersections of a principal fiber with a horizontal curve need not vanish. The correct global assertion is that principal intersection zero-cycles are rationally trivial after every boundary contribution is retained.

### 9.3 Moving only as far as necessary

On a projective regular surface over a field, one can move a divisor within its linear equivalence class so that it shares no components with a fixed divisor, then define the intersection by local lengths. Independence follows from degree zero of principal divisors on proper curves. This recovers the line-bundle definition.

For arithmetic surfaces, a full moving lemma is unnecessary for the component calculations of this book. We use three controlled cases:

1. divisors with no common components, treated by local lengths;
2. a Cartier divisor against a vertical curve, treated by restriction and degree;
3. two vertical divisors, treated bilinearly from component degrees.

These cases include exceptional curves, special-fiber matrices, adjunction, and vertical corrections. Avoiding an unnecessarily general intersection ring keeps the hypotheses visible and prevents hidden choices at horizontal infinity.

## 10. Proper maps and the projection formula

### 10.1 Pushforward of curves and points

Let $f:Y\to X$ be a proper morphism of integral regular surfaces. For an integral curve $C\subset Y$, define

$$
f_*[C]=
\begin{cases}
[k(C):k(f(C))][f(C)],&\dim f(C)=1,\\
0,&\dim f(C)=0.
\end{cases} \tag{10.1}
$$

The field degree is finite because the map of curves is proper and generically finite onto its image. A curve contracted to a point contributes no divisor on $X$; its information reappears when intersected before pushforward.

For a closed point $y$, properness gives a closed point $x=f(y)$ and

$$
f_*[y]=[\kappa(y):\kappa(x)][x]. \tag{10.2}
$$

These definitions are forced by compatibility of degrees in towers. They extend linearly to divisors and zero-cycles.

For a birational morphism, the strict transform of a noncontracted prime curve pushes forward to the original curve with coefficient one, while exceptional curves push forward to zero. For a finite morphism, no curve is contracted.

### 10.2 Pullback of divisors

If $f:Y\to X$ is dominant between integral schemes and $D$ is Cartier, pull back its rational local equations. Nonzero equations remain nonzero in the larger function field, so $f^*D$ is defined. For an effective divisor, effectivity is preserved when the pulled-back local equation remains regular; this holds for morphisms of integral schemes because local homomorphisms send the equation into the local ring, though multiplicities may appear.

At a prime curve $C\subset Y$ mapping onto a prime curve $B\subset X$, the coefficient of $C$ in $f^*B$ is the ramification index of the corresponding discrete valuations:

$$
\operatorname{ord}_C(f^*t_B)=e(C/B).
$$

For a finite flat map, the pullback of an effective Cartier divisor agrees with the scheme-theoretic inverse image. For a point blowup, pullback is the total transform, not the strict transform.

### 10.3 The projection formula

**Theorem 10.1 (projection formula).** Let $f:Y\to X$ be proper, with $X$ and $Y$ regular surfaces, let $D$ be a Cartier divisor on $X$, and let $C$ be an integral proper curve on $Y$ for which the indicated degrees are defined. Then

$$
(f^*D\mathbin{\cdot}C)
=(D\mathbin{\cdot}f_*C). \tag{10.3}
$$

**Proof strategy.** Restrict the pulled-back line bundle to $C$ and compare its degree with the norm along $C\to f(C)$.

If $C$ is contracted, $f|_C$ maps to a point. The restriction of $f^*\mathcal O_X(D)$ to $C$ is pulled back from a one-dimensional vector space and is therefore trivial; both sides are zero. If $C$ maps generically finitely of degree $r$ to $B=f(C)$, then

$$
\deg_C(f|_C)^*\mathcal O_X(D)|_B
=r\deg_B\mathcal O_X(D)|_B.
$$

This is exactly (10.3), including constant-field degrees. $\square$

For divisors $G$ on $Y$, bilinearity gives

$$
f_*(f^*D\mathbin{\cdot}G)=D\mathbin{\cdot}f_*G
$$

as zero-cycles in every proper-intersection case. This form is often the safest because it remembers residue extensions point by point.

For a birational morphism and an exceptional curve $E$, the formula gives

$$
(f^*D\mathbin{\cdot}E)=0. \tag{10.4}
$$

Orthogonality of pullbacks to exceptional curves is the engine behind all blowup formulas.

### 10.4 Finite maps and degree

Let $f:Y\to X$ be finite dominant of generic degree $n$. For a prime divisor $B$ on $X$,

$$
f^*B=\sum_{C\mapsto B}e(C/B)C,
$$

and the fundamental equality for the corresponding discrete valuations gives

$$
f_*f^*B=nB
$$

when the function-field extension is separable or, more generally, when inseparable degrees are included in the residue degrees. Hence

$$
f_*f^*D=nD. \tag{10.5}
$$

If $D$ and $G$ are divisors on $X$ with proper intersection, projection gives

$$
(f^*D\mathbin{\cdot}f^*G)
=n(D\mathbin{\cdot}G) \tag{10.6}
$$

after pushing to the same base and taking the appropriate degrees. Flatness ensures that scheme-theoretic inverse images have the expected lengths; without flatness, (10.5) at the cycle level may still hold under suitable normality, but naive tensor-product lengths can acquire torsion.

Under a finite extension of discrete valuation rings, ramification changes the scheme-theoretic fiber: $\pi=u(\pi')^e$. Consequently pullback multiplies the total fiber divisor by $e$. Residue extension multiplies degrees in the other direction. Formulas (10.3)--(10.6), rather than visual counting of geometric components, keep both effects consistent.

## 11. The calculus of a point blowup

### 11.1 The four fundamental formulas

Let $X$ be a regular arithmetic surface, let $x\in X_s$ be a closed point, and let

$$
b:Y\longrightarrow X
$$

be its blowup. Write $E$ for the exceptional curve and $d_x=[\kappa(x):\kappa(s)]$. Let $D$ be a Cartier curve through $x$ with multiplicity $m=m_x(D)$. Then four formulas control the entire calculation:

$$
b^*D=\widetilde D+mE, \tag{11.1}
$$

$$
E^2=-d_x, \tag{11.2}
$$

$$
(b^*D\mathbin{\cdot}E)=0, \tag{11.3}
$$

$$
(\widetilde D\mathbin{\cdot}E)=md_x. \tag{11.4}
$$

We have already seen the geometric reasons, but it is worth proving their compatibility. Formula (11.1) is the exceptional-factor calculation. Formula (11.2) is the degree of $\mathcal O_E(-1)$ over $\kappa(s)$. Formula (11.3) is projection: $E$ is contracted, so the restriction to $E$ of a line bundle pulled back from $X$ is trivial. Intersecting (11.1) with $E$ gives

$$
0=(\widetilde D\mathbin{\cdot}E)+mE^2,
$$

which yields (11.4). Thus the sign of $E^2$ and the positive tangent-cone degree force one another.

If $D$ is vertical, all four are numerical identities over $\kappa(s)$. If $D$ is horizontal, (11.1) is an identity of divisors and (11.3)--(11.4) are still well-defined because the second argument is vertical.

### 11.2 Intersections of strict transforms

Let $D$ and $G$ be divisors with multiplicities $m$ and $n$ at $x$. Their total transforms satisfy the projection identity

$$
(b^*D\mathbin{\cdot}b^*G)=(D\mathbin{\cdot}G)
$$

in any context where both sides have a numerical degree. Expanding with (11.1) and using orthogonality to $E$ gives

$$
(\widetilde D\mathbin{\cdot}\widetilde G)
=(D\mathbin{\cdot}G)-mnd_x. \tag{11.5}
$$

Locally, this says

$$
i_x(D,G)=m_x(D)m_x(G)
+\sum_{y\in E}i_y(\widetilde D,\widetilde G)
[\kappa(y):\kappa(x)]. \tag{11.6}
$$

Formula (11.6) is the separation theorem for intersection multiplicity. The first blowup extracts the product of the leading multiplicities; common tangent directions carry the remaining contact to points infinitely near $x$.

Taking $D=G$ in the global or vertical setting yields

$$
\widetilde D^{,2}=D^2-m^2d_x. \tag{11.7}
$$

If $x$ is a smooth point of $D$, then $m=1$: blowing up a point on a curve lowers its self-intersection by $d_x$. If $x\notin D$, the strict transform is the pullback and its self-intersection is unchanged.

**Example.** Two smooth curves tangent to order $r$ at a rational point have intersection $r$. Each blowup at their successive common point has $m=n=1$ and subtracts one. After $r$ steps their strict transforms are disjoint. The original intersection number has been decomposed into $r$ unit contributions at a chain of infinitely near points.

### 11.3 Infinitely near points and proximity

A point on an exceptional curve created by a blowup is **infinitely near** to the original point. A sequence

$$
X_r\longrightarrow X_{r-1}\longrightarrow\cdots\longrightarrow X_0
$$

of point blowups turns local intersection into a sum over the centers:

$$
i_x(D,G)=
\sum_{j=0}^{r-1}m_{x_j}(D_j)m_{x_j}(G_j)
[\kappa(x_j):\kappa(x)]
+i_{\mathrm{res}}. \tag{11.8}
$$

Here $D_j,G_j$ are strict transforms, and $i_{\mathrm{res}}$ is the remaining intersection after the chosen sequence. Once the transforms are disjoint, the residual term is zero.

Exceptional curves also transform. If $E_i$ is created with square $-d_i$ and a later point of residue degree $e$ on its strict transform is blown up, its square decreases by $e$. If the later center lies at the intersection of two components, both squares decrease and the new exceptional curve meets both. These **proximity rules** allow an entire resolution matrix to be computed without returning to local equations at every stage.

One caution is decisive: self-intersections belong to a particular surface. The label $-1$ attached when a curve is created changes after subsequent blowups on that curve. A resolution graph must therefore record the final strict transforms, not the creation-time labels.

## 12. Canonical divisors, adjunction, and genus

### 12.1 Relative canonical divisors

Let $X\to S$ be a regular arithmetic surface. It is a flat local complete-intersection morphism of relative dimension one locally over each discrete valuation ring, hence Gorenstein. Its relative dualizing sheaf $\omega_{X/S}$ is invertible. A **relative canonical divisor** $K_{X/S}$ is any Cartier divisor with

$$
\mathcal O_X(K_{X/S})\simeq\omega_{X/S}.
$$

It is determined only up to a principal divisor, which is enough for intersection with proper vertical curves.

Under a point blowup $b:Y\to X$, the canonical bundle changes by

$$
K_{Y/S}=b^*K_{X/S}+E. \tag{12.1}
$$

To see the coefficient, use regular parameters $(u,v)$ at the center. On the chart $v=ut$, a local generator $du\wedge dv$ of the absolute two-dimensional canonical module transforms as

$$
du\wedge d(ut)=u\,du\wedge dt.
$$

It vanishes once along $E=(u=0)$. Dividing out the base differential gives the same relative formula. The other chart agrees. The coefficient is $+1$; a minus sign would contradict adjunction on $E$.

By projection and (11.2),

$$
(K_{Y/S}\mathbin{\cdot}E)=E^2=-d_x. \tag{12.2}
$$

Over $\kappa(x)$ this is $-1$, as expected for an exceptional projective line.

### 12.2 Adjunction

Let $C$ be an effective integral Cartier curve on $X$ that is proper over $k=\kappa(s)$; in particular, a vertical component qualifies. The conormal sequence and duality for a Cartier immersion give

$$
\omega_{C/k}simeq
\left(\omega_{X/S}\otimes\mathcal O_X(C)\right)|_C. \tag{12.3}
$$

Taking degrees yields the **adjunction formula**

$$
2p_a(C)-2=(K_{X/S}+C\mathbin{\cdot}C), \tag{12.4}
$$

where

$$
p_a(C)=1-\chi(C,\mathcal O_C)
$$

and Euler characteristic and degree are taken over $k$. Indeed Riemann--Roch and duality on the proper Gorenstein curve give

$$
\deg_k\omega_{C/k}=-2\chi(C,\mathcal O_C)=2p_a(C)-2.
$$

This convention remains valid if the constant field of $C$ is a finite extension of $k$; all dimensions and degrees then acquire the same residue-field factor.

The proof requires $C$ to be Cartier and the ambient surface to have an invertible dualizing sheaf. On a singular non-Gorenstein surface, a correction term can appear and (12.4) must not be used unchanged.

Adjunction also holds for a relative effective Cartier divisor $H$ finite and flat over $S$ as an isomorphism of dualizing line bundles:

$$
\omega_{H/S}simeq
(\omega_{X/S}\otimes\mathcal O_X(H))|_H.
$$

It is then line-bundle information on $H$ rather than an automatic integer.

### 12.3 Arithmetic genus and blowup

Let $D$ be a proper Cartier curve on a regular surface in a context with a numerical intersection pairing, and suppose it has multiplicity $m$ at the blowup center $x$. Combine

$$
\widetilde D=b^*D-mE,
\qquad
K_Y=b^*K_X+E,
$$

with $E^2=-d_x$ and orthogonality of pullbacks. Adjunction gives

$$
2p_a(\widetilde D)-2
=2p_a(D)-2-m(m-1)d_x.
$$

Therefore

$$
p_a(\widetilde D)
=p_a(D)-\frac{m(m-1)}2d_x. \tag{12.5}
$$

For a smooth branch, $m=1$ and genus is unchanged. For a singular curve, the decrease measures part of the singularity defect resolved at that point. A double point can lower arithmetic genus by one per rational center, but whether it does so depends on how the strict transform and exceptional divisor meet.

The arithmetic genus of the entire surface fiber is unchanged by point blowups. More precisely, a point blowup satisfies

$$
b_*\mathcal O_Y=\mathcal O_X,
\qquad R^1b_*\mathcal O_Y=0.
$$

The second assertion follows by covering the exceptional projective line and using $H^1(\mathbf P^1,\mathcal O(n))=0$ for $n\geq-1$ on successive infinitesimal neighborhoods. Thus Euler characteristics of the total fibers agree. The strict transform of one component may change genus, but the exceptional component and new incidence data restore the genus of the whole fiber.

### 12.4 The numerical test for exceptional curves

If $E\simeq\mathbf P^1_k$ is a rational vertical curve, then $p_a(E)=0$, and adjunction says

$$
K_{X/S}\mathbin{\cdot}E+E^2=-2. \tag{12.6}
$$

For a $(-1)$-curve, $K\cdot E=-1$. For a $(-2)$-curve, $K\cdot E=0$. This distinction is ubiquitous: $(-1)$-curves are removable artifacts of regular point blowups, while chains of $(-2)$-curves often occur in minimal resolutions of rational double points.

The converse contraction criterion needs geometry as well as numbers. A curve satisfying $E^2=-1$ and $K\cdot E=-1$ is contractible to a regular point when it is a projective line with the correct constant field and normal bundle. Numerical equalities alone do not prove that a non-geometrically integral curve is a projective line.

## 13. Special fibers and their intersection matrices

### 13.1 The fiber relation

Fix a closed point $s\in S$ and write the scheme-theoretic fiber as

$$
F=X_s=\sum_{i=1}^r m_i\Gamma_i,
\qquad m_i>0.
$$

Because $F=\operatorname{div}(\pi)$ near $s$, the line bundle $\mathcal O_X(F)$ is trivial. Restricting to each proper component gives

$$
(F\mathbin{\cdot}\Gamma_i)
=\sum_{j=1}^r m_j(\Gamma_j\mathbin{\cdot}\Gamma_i)=0. \tag{13.1}
$$

Thus the multiplicity vector

$$
m=(m_1,\ldots,m_r)^t
$$

lies in the kernel of the symmetric intersection matrix

$$
M=((\Gamma_i\mathbin{\cdot}\Gamma_j))_{i,j}. \tag{13.2}
$$

For $i\neq j$, the entry is a sum of nonnegative local intersection multiplicities. It is positive precisely when the components meet after accounting for residue fields. Equation (13.1) then forces the diagonal entries to be nonpositive.

The equality also recovers generic degree. For any Cartier divisor $D$ on $X$,

$$
(D\mathbin{\cdot}F)
=\sum_i m_i(D\mathbin{\cdot}\Gamma_i)
=\deg(D|_{X_K}). \tag{13.3}
$$

The last equality is constancy of degree in the proper flat family. For a horizontal section, it is $1$. For a divisor of degree zero on the generic fiber, it is $0$; this is exactly the compatibility condition for vertical correction.

### 13.2 The weighted Laplacian identity

Let

$$
V=\sum_i a_i\Gamma_i,
\qquad b_i=\frac{a_i}{m_i}.
$$

Use (13.1) to eliminate every diagonal entry:

$$
m_i\Gamma_i^2
=-\sum_{j\neq i}m_j(\Gamma_i\mathbin{\cdot}\Gamma_j).
$$

Substitution and grouping unordered pairs gives the decisive identity

$$
V^2
=-\sum_{i<j}m_im_j
(\Gamma_i\mathbin{\cdot}\Gamma_j)
\left(\frac{a_i}{m_i}-\frac{a_j}{m_j}\right)^2. \tag{13.4}
$$

Every term on the right is nonpositive. The special-fiber intersection matrix is therefore a negative weighted graph Laplacian. Multiplicities rescale vertex potentials, while intersection numbers are edge conductances.

Formula (13.4) is more informative than an abstract eigenvalue argument. It shows the sign, identifies equality, and remains valid over nonclosed residue fields because the edge weights already include residue degrees.

### 13.3 Negativity and its exact kernel

Assume the support of $F$ is connected. This holds, for example, when $X\to S$ has geometrically connected generic fiber and $f_*\mathcal O_X=\mathcal O_S$, by connectedness of fibers. Then the graph with vertices $\Gamma_i$ and an edge whenever $(\Gamma_i\cdot\Gamma_j)>0$ is connected.

By (13.4), $V^2\leq0$. Equality holds precisely when $b_i=b_j$ across every edge, hence when all $b_i$ are equal. Therefore

$$
\ker(M\otimes\mathbf Q)=\mathbf Q(m_1,\ldots,m_r), \tag{13.5}
$$

and the pairing is negative definite on

$$
\left(\bigoplus_i\mathbf Q\Gamma_i\right)/\mathbf QF. \tag{13.6}
$$

This is the **negativity theorem for a fiber**. The quotient by the whole fiber is essential; the unreduced matrix is never negative definite because $F$ is in its radical.

If the fiber support is disconnected, each connected component supplies a kernel vector. If properness or flatness is dropped, the fiber relation can fail. If the total space is not regular, individual components need not be Cartier and the matrix may require a rational or resolution-dependent definition.

A useful consequence is that, when $r>1$, every component meeting the rest has negative self-intersection. Indeed (13.1) gives

$$
\Gamma_i^2
=-\frac1{m_i}\sum_{j\neq i}m_j
(\Gamma_i\mathbin{\cdot}\Gamma_j)<0. \tag{13.7}
$$

The quotient negativity is the numerical foundation for uniqueness of vertical corrections and for contraction arguments.

### 13.4 Examples of fiber matrices

For a smooth irreducible fiber $F=\Gamma$, equation (13.1) gives $\Gamma^2=0$. The matrix $(0)$ has radical spanned by the fiber and no negative quotient.

Suppose a reduced connected fiber has two components meeting transversely in $r$ rational points. Then

$$
M=
\begin{pmatrix}
-r&r\\
r&-r
\end{pmatrix}.
$$

Its eigenvalues are $0$ and $-2r$; the kernel is spanned by $(1,1)$. If the intersection points have residue degrees $d_1,\ldots,d_q$, replace $r$ by $\sum d_j$.

For a reduced normal-crossing fiber whose dual graph is a chain and whose edge intersections are rational and transverse, $M$ is the negative graph Laplacian: the diagonal entry is minus the valency and adjacent off-diagonal entries are $1$. A component at the end has square $-1$ in the total fiber configuration. Such an end component is contractible only if it is also a projective line and contraction is compatible with the desired model; after contraction the remaining fiber multiplicities and intersections must be recomputed.

For a multiple irreducible fiber $F=m\Gamma$, relation (13.1) gives $m\Gamma^2=0$, hence $\Gamma^2=0$. The matrix alone does not detect the multiplicity $m$; the labeled fiber divisor is part of the data.

## 14. Vertical corrections and component pairings

### 14.1 Solving the balancing equations

Let $D$ be a horizontal divisor whose restriction to the generic fiber has degree zero. Set

$$
d_i=(D\mathbin{\cdot}\Gamma_i).
$$

Equation (13.3) gives the necessary compatibility

$$
\sum_i m_id_i=0. \tag{14.1}
$$

We seek a rational vertical divisor

$$
\Phi_s(D)=\sum_i v_i\Gamma_i
$$

such that the corrected divisor is balanced on every component:

$$
(D+\Phi_s(D)\mathbin{\cdot}\Gamma_i)=0
\quad\text{for all }i. \tag{14.2}
$$

In matrix form, $Mv=-d$. Since $M$ is symmetric with kernel $\mathbf Qm$, its image is the hyperplane orthogonal to $m$. Compatibility (14.1) therefore proves existence. Any two solutions differ by a rational multiple of $F$. We have proved:

**Theorem 14.1 (vertical correction).** For a connected special fiber and a generic degree-zero divisor $D$, a rational vertical correction satisfying (14.2) exists and is unique modulo $\mathbf QF$.

A normalization such as $\sum_i m_iv_i=0$, or the requirement that one chosen coefficient vanish, selects a unique representative. The resulting representative depends on the normalization; its class modulo $F$ does not.

### 14.2 Integral data and rational corrections

The intersection vector $d$ is integral, but the solution $v$ need not be. This is not a defect. The lattice map

$$
M:\mathbf Z^r/\mathbf Zm
\longrightarrow
\{d\in\mathbf Z^r:m\cdot d=0\}
$$

usually has finite cokernel, and its failure to be surjective forces denominators.

For the two-component matrix

$$
M=
\begin{pmatrix}-r&r\\r&-r\end{pmatrix},
$$

an intersection vector $(a,-a)$ is corrected by coefficients satisfying

$$
v_1-v_2=\frac{a}{r}.
$$

If $r\nmid a$, no integral correction exists. Thus component pairings naturally take rational values even though every original local intersection is integral.

The finite cokernel of the integral matrix on the degree-zero lattice is the first shadow of the component group developed later. Here we need only its elementary consequence: denominators are controlled by a nonzero cofactor of $M$, equivalently by a weighted spanning-tree determinant after a vertex normalization.

### 14.3 The corrected local pairing

Let $D$ and $G$ be generic degree-zero horizontal divisors with disjoint generic supports, so their raw local intersection $(D\cdot G)_s$ is defined. Choose vertical corrections $\Phi_s(D)$ and $\Phi_s(G)$. Define

$$
\langle D,G\rangle_s
=(D+\Phi_s(D)\mathbin{\cdot}G)_s. \tag{14.3}
$$

This is independent of adding a rational multiple of $F$ to either correction because $(F\cdot G)=\deg G_K=0$. It is symmetric. Indeed balancedness gives

$$
(D+\Phi_s(D)\mathbin{\cdot}\Phi_s(G))=0,
$$

and hence

$$
\langle D,G\rangle_s
=(D\mathbin{\cdot}G)_s
-(\Phi_s(D)\mathbin{\cdot}\Phi_s(G)). \tag{14.4}
$$

The right side is visibly symmetric. It also equals the intersection of the two fully corrected divisors.

The sign in (14.4) matters. The vertical matrix is negative semidefinite, so the quadratic **component energy**

$$
q_s(D)=-\Phi_s(D)^2 \tag{14.5}
$$

is nonnegative. Thus the correction term on the diagonal is positive. Reversing the sign of the vertical matrix without also changing (14.4) produces an inconsistent convention.

The raw self-intersection of a horizontal divisor may not be a canonical local integer, as Section 8.4 explained. Formula (14.5), however, is a canonical nonnegative rational number determined solely by the component intersection vector. For two vectors $d,e$ satisfying (14.1), the bilinear component pairing is

$$
q_s(d,e)=-v^tMw,
\qquad Mv=-d,\quad Mw=-e. \tag{14.6}
$$

Changing $v$ or $w$ by a multiple of $m$ changes nothing. This finite-dimensional pairing is the precise component datum needed later.

### 14.4 Functoriality and base change

Let $f:Y\to X$ be a finite morphism of regular arithmetic surfaces over the same Dedekind scheme $S$. Pullback sends horizontal degree-zero divisors to degree-zero divisors after multiplying generic degree appropriately, and pushforward sends vertical components with residue-field degrees. Projection gives

$$
(f^*D\mathbin{\cdot}C)=(D\mathbin{\cdot}f_*C).
$$

Therefore the component intersection vector upstairs is obtained from the downstairs vector by the transpose of the pushforward matrix on components. The vertical correction equations commute with these linear maps after tensoring with $\mathbf Q$.

If $f$ has generic degree $n$ and the models are chosen so that the relevant pullbacks and pushforwards are defined without unresolved singularities, the corrected pairing satisfies the expected projection relation

$$
\langle f^*D,H\rangle
=\langle D,f_*H\rangle,
$$

and in particular pullback against pullback scales by $n$. This follows from the ordinary projection formula plus uniqueness of balanced corrections modulo fibers.

Base change deserves caution. An unramified residue extension may split components and closed intersection points; residue-degree weights ensure their total contribution is preserved. A ramified extension changes fiber multiplicities and can make the base-changed total space singular. One must normalize and resolve before forming its regular component matrix. The new matrix is related to the old one through pullback and pushforward on a common regular domination, not by simply copying the old graph.

Birational invariance is similarly controlled. If $b:Y\to X$ is a point blowup, adding the exceptional component enlarges the vertical matrix by one negative direction, while pullbacks remain orthogonal to it. Degree-zero corrected pairings of divisors pulled back from $X$ are unchanged: the new correction is the total pullback of the old one, adjusted by the forced exceptional coefficient. This is the numerical reason component pairings depend on the underlying curve and chosen fiber data rather than on superfluous regular point blowups.

## 15. A reusable intersection package

### 15.1 The theorem package

We can now collect the results in the form used by subsequent geometry.

**Theorem 15.1 (blowup and intersection package).** Let $X\to S$ be a regular proper flat arithmetic surface over an excellent Dedekind scheme, with smooth geometrically connected generic fiber.

1. For every nonzero coherent ideal $\mathcal I$, the blowup is $\operatorname{Proj}_X\bigoplus_{n\geq0}\mathcal I^n$. It is universal for making $\mathcal I$ invertible, local on the target, and compatible with flat base change.
2. Blowing up a closed regular point preserves regularity. If $x\in X_s$, its exceptional curve is $\mathbf P^1_{\kappa(x)}$ and has square $-[\kappa(x):\kappa(s)]$.
3. If a Cartier divisor has multiplicity $m$ at $x$, then $b^*D=\widetilde D+mE$, $(\widetilde D\cdot E)=m[\kappa(x):\kappa(s)]$, and $\widetilde D^2=D^2-m^2[\kappa(x):\kappa(s)]$ whenever the square is numerical.
4. Effective curves meeting properly at $x$ have local intersection $\operatorname{length}\mathcal O_{X,x}/(f,g)$. Global fiberwise intersections multiply this length by $[\kappa(x):\kappa(s)]$.
5. For a vertical integral curve $C$, $(D\cdot C)=\deg\mathcal O_X(D)|_C$. This extends intersection to common vertical components and makes it symmetric and bilinear.
6. Proper pushforward and Cartier pullback satisfy $(f^*D\cdot C)=(D\cdot f_*C)$. For a finite map of generic degree $n$, pullback intersections scale by $n$ after degrees are taken on the same base.
7. Relative canonical divisors obey $K_Y=b^*K_X+E$, and every proper Cartier curve satisfies $2p_a(C)-2=(K_X+C)\cdot C$.
8. For a connected fiber $F=\sum m_i\Gamma_i$, the component matrix is negative semidefinite with rational kernel exactly $\mathbf Q(m_i)$. It is negative definite modulo the whole fiber.
9. Every generic degree-zero divisor has a rational vertical correction balanced on all components, unique modulo $\mathbf QF$. The induced component energy is nonnegative and the corrected pairing is symmetric and rational.

Every adjective in the theorem has a job. Regularity supplies Cartier components and regular sequences. Properness supplies degrees on vertical curves. Flatness makes the fiber Cartier and gives degree constancy. Connectedness makes the radical one-dimensional. Excellence supports the resolution and contraction operations around the numerical theory.

### 15.2 A calculation protocol

A complicated model calculation becomes reliable when performed in a fixed order.

First write the scheme-theoretic fiber, including every multiplicity. At a proposed blowup center, choose regular parameters and compute the order of each local equation. Use total transform to label the exceptional component, and strict transform to determine the new incidence graph.

Second record residue fields. A transverse intersection at a point $x$ contributes $[\kappa(x):\kappa(s)]$, not automatically one. The exceptional curve has square the negative of the same degree.

Third compute off-diagonal component intersections by local lengths. Obtain diagonal entries from the fiber equations

$$
\sum_jm_j(\Gamma_i\cdot\Gamma_j)=0,
$$

rather than guessing them from a picture. Check that the multiplicity vector lies in the kernel and that the matrix is negative semidefinite.

Fourth, when canonical divisors occur, test the answer by adjunction. A rational $(-1)$-curve must satisfy $K\cdot E=-1$ over its constant field; a rational $(-2)$-curve must satisfy $K\cdot E=0$.

Finally, for a degree-zero horizontal divisor, form its component intersection vector and verify its weighted sum is zero. Solve the correction equations over $\mathbf Q$, state the normalization used, and remember that only the class modulo the full fiber is intrinsic.

This protocol supplies independent checks on signs and multiplicities. A wrong exceptional sign breaks adjunction; a missing residue degree breaks projection; a wrong fiber multiplicity removes the kernel vector; an unjustified integral solution hides genuine component denominators.

### 15.3 Failure modes

Several plausible shortcuts are false.

The blowup chart $A[I/f]$ is not generally a free polynomial ring, and the Rees algebra is not generally the symmetric algebra. Blowup is guaranteed to commute with flat base change, not with arbitrary nonflat base change. The strict transform is not the scheme-theoretic inverse image; exceptional torsion must be removed.

Normality is not regularity. A normalized blowup of a singular surface may still require further blowups. Conversely, resolving a surface does not make its fiber reduced or nodal. Semistable reduction may require a ramified field extension, after which resolution may have to be repeated.

Local length does not define the intersection of curves sharing a component. Self-intersection comes from the normal bundle. Horizontal self-intersection over an arbitrary Dedekind base is not canonically an integer. Principal divisors have degree zero on proper vertical curves, but a base uniformizer still meets a horizontal section in the closed fiber.

The special-fiber matrix is not negative definite: the full multiplicity vector is always in its kernel. It becomes negative definite only after quotienting by the fiber, and only a connected fiber gives a one-dimensional kernel. Integral intersection vectors can require rational vertical corrections.

Finally, a negative rational curve is not automatically contractible to a regular point. The first-kind criterion requires the projective-line geometry and normal degree $-1$. Contracting a $(-2)$-curve creates a singularity rather than reversing a regular point blowup.

### 15.4 Conclusion

A regular arithmetic surface turns codimension-one geometry into arithmetic linear algebra. Local equations yield lengths; lengths assemble into degrees; degrees form a symmetric component matrix; and the fiber equation turns that matrix into a negative weighted Laplacian. Blowups are the transformations under which every stage remains computable.

The exceptional divisor is the bridge. Geometrically it is the space of tangent directions. Divisor-theoretically it is the correction between total and strict transform. Numerically it has negative normal degree and is orthogonal to pullbacks. Canonically it contributes once to the transformed dualizing divisor. These four descriptions force the blowup formulas and make their signs inevitable.

The resulting vertical theory is both integral and rational in exactly the right places. Local multiplicities, residue-weighted intersections, and component matrices are integral. Balancing a degree-zero divisor requires inverting the component matrix modulo its fiber kernel, so rational coefficients naturally appear. Their denominators retain finite information that later becomes component-group and monodromy data.

We have stayed within the geometry of regular relative curves over Dedekind schemes. No general higher-dimensional intersection ring was needed. The tools established here—transform formulas, projection, adjunction, fiber negativity, and corrected component pairings—are precisely the numerical language in which semistable dual graphs, relative Picard geometry, and component groups can now be developed.
