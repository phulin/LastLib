# Elliptic Curves over DVRs

## Contents

1. [From a curve over a field to arithmetic at a place](#1-from-a-curve-over-a-field-to-arithmetic-at-a-place)
   - [Why an equation should remember a valuation](#11-why-an-equation-should-remember-a-valuation)
   - [Elliptic curves and the marked point](#12-elliptic-curves-and-the-marked-point)
   - [The chord-and-tangent law](#13-the-chord-and-tangent-law)
   - [General and short equations](#14-general-and-short-equations)
   - [Pole orders as a reconstruction principle](#15-pole-orders-as-a-reconstruction-principle)
   - [Hypotheses and the boundary of the book](#16-hypotheses-and-the-boundary-of-the-book)
2. [Coordinates, weights, and invariant quantities](#2-coordinates-weights-and-invariant-quantities)
   - [Why the coordinate changes are constrained](#21-why-the-coordinate-changes-are-constrained)
   - [The b-quantities and completing the square](#22-the-b-quantities-and-completing-the-square)
   - [The fundamental invariants](#23-the-fundamental-invariants)
   - [The invariant differential](#24-the-invariant-differential)
   - [A warning about equal j](#25-a-warning-about-equal-j)
   - [Deriving the identities rather than memorizing them](#26-deriving-the-identities-rather-than-memorizing-them)
3. [Discriminant and smoothness](#3-discriminant-and-smoothness)
   - [The discriminant as a collision detector](#31-the-discriminant-as-a-collision-detector)
   - [Node or cusp](#32-node-or-cusp)
   - [The smooth locus of a singular cubic](#33-the-smooth-locus-of-a-singular-cubic)
   - [Worked singular fibers](#34-worked-singular-fibers)
   - [Discriminant valuation as collision thickness](#35-discriminant-valuation-as-collision-thickness)
4. [Integral Weierstrass models](#4-integral-weierstrass-models)
   - [What integrality accomplishes](#41-what-integrality-accomplishes)
   - [Integral coordinate changes](#42-integral-coordinate-changes)
   - [Integral equations are not all equivalent](#43-integral-equations-are-not-all-equivalent)
   - [The differential lattice](#44-the-differential-lattice)
   - [What a Weierstrass model forgets](#45-what-a-weierstrass-model-forgets)
5. [Minimal equations and the minimal discriminant](#5-minimal-equations-and-the-minimal-discriminant)
   - [Existence by well-ordering](#51-existence-by-well-ordering)
   - [Essential uniqueness](#52-essential-uniqueness)
   - [Immediate valuation criteria](#53-immediate-valuation-criteria)
   - [The short-form criterion away from 2 and 3](#54-the-short-form-criterion-away-from-2-and-3)
   - [A minimality calculation](#55-a-minimality-calculation)
   - [Minimal discriminant versus equation discriminant](#56-minimal-discriminant-versus-equation-discriminant)
   - [A practical minimization strategy](#57-a-practical-minimization-strategy)
   - [Minimal differentials and uniqueness revisited](#58-minimal-differentials-and-uniqueness-revisited)
6. [Reading the special fiber](#6-reading-the-special-fiber)
   - [Reduction of a minimal equation](#61-reduction-of-a-minimal-equation)
   - [Good reduction](#62-good-reduction)
   - [Multiplicative reduction and splitting](#63-multiplicative-reduction-and-splitting)
   - [Additive reduction](#64-additive-reduction)
   - [A reduction decision procedure](#65-a-reduction-decision-procedure)
   - [Three nearby curves with different reduction](#66-three-nearby-curves-with-different-reduction)
   - [A characteristic-free splitness polynomial](#67-a-characteristic-free-splitness-polynomial)
7. [Local points and the reduction filtration](#7-local-points-and-the-reduction-filtration)
   - [Extending a point to a section](#71-extending-a-point-to-a-section)
   - [The formal parameter at the origin](#72-the-formal-parameter-at-the-origin)
   - [The formal group law](#73-the-formal-group-law)
   - [Components and the missing quotient](#74-components-and-the-missing-quotient)
   - [Coordinate tests for the formal neighborhood](#75-coordinate-tests-for-the-formal-neighborhood)
   - [Topology and successive approximation](#76-topology-and-successive-approximation)
8. [Smooth models, semistability, and intrinsic criteria](#8-smooth-models-semistability-and-intrinsic-criteria)
   - [Why resolve a minimal cubic](#81-why-resolve-a-minimal-cubic)
   - [Semistable reduction](#82-semistable-reduction)
   - [The valuation of j](#83-the-valuation-of-j)
   - [Néron-type criteria without representations](#84-néron-type-criteria-without-representations)
   - [Resolving a node and a cusp](#85-resolving-a-node-and-a-cusp)
   - [Multiplicative components and rational component classes](#86-multiplicative-components-and-rational-component-classes)
   - [The conductor statement justified by this geometry](#87-the-conductor-statement-justified-by-this-geometry)
   - [What additive data remain invisible](#88-what-additive-data-remain-invisible)
9. [Change of the ground DVR](#9-change-of-the-ground-dvr)
   - [How valuations rescale](#91-how-valuations-rescale)
   - [Unramified base change](#92-unramified-base-change)
   - [Ramified base change](#93-ramified-base-change)
   - [Descent and persistence](#94-descent-and-persistence)
   - [Two base-change calculations](#95-two-base-change-calculations)
10. [Residue characteristics two and three](#10-residue-characteristics-two-and-three)
    - [Why short form is dangerous](#101-why-short-form-is-dangerous)
    - [Testing an improvement by congruences](#102-testing-an-improvement-by-congruences)
    - [A two-adic integral improvement](#103-a-two-adic-integral-improvement)
    - [Small-characteristic counterexamples to shortcuts](#104-small-characteristic-counterexamples-to-shortcuts)
    - [A three-adic hidden dilation](#105-a-three-adic-hidden-dilation)
    - [Exact coarse criteria in characteristics two and three](#106-exact-coarse-criteria-in-characteristics-two-and-three)
11. [Worked local calculations](#11-worked-local-calculations)
    - [The Legendre family](#111-the-legendre-family)
    - [Root differences and full rational two-torsion](#112-root-differences-and-full-rational-two-torsion)
    - [Cancellation and unequal valuations](#113-cancellation-and-unequal-valuations)
    - [A splitness calculation from the tangent cone](#114-a-splitness-calculation-from-the-tangent-cone)
    - [What the coarse data do and do not determine](#115-what-the-coarse-data-do-and-do-not-determine)
    - [Quadratic twists as a reduction experiment](#116-quadratic-twists-as-a-reduction-experiment)
    - [A dyadic tangent-cone calculation](#117-a-dyadic-tangent-cone-calculation)
12. [A Frey-type local laboratory](#12-a-frey-type-local-laboratory)
    - [The equation and its visible torsion](#121-the-equation-and-its-visible-torsion)
    - [Complete invariant calculation](#122-complete-invariant-calculation)
    - [Odd primes dividing one factor](#123-odd-primes-dividing-one-factor)
    - [Splitness at the odd bad primes](#124-splitness-at-the-odd-bad-primes)
    - [Common factors and weighted normalization](#125-common-factors-and-weighted-normalization)
    - [The prime above two](#126-the-prime-above-two)
    - [The exponentiated three-term specialization](#127-the-exponentiated-three-term-specialization)
    - [The primitive integral Frey curve](#128-the-primitive-integral-frey-curve)
    - [Conclusion](#129-conclusion)

## 1. From a curve over a field to arithmetic at a place

### 1.1 Why an equation should remember a valuation

An elliptic curve over a field is a geometric object, but arithmetic questions about it are almost never indifferent to a chosen place. A point may have integral or nonintegral coordinates. A coefficient may be a unit or may vanish to high order. Most importantly, a smooth curve over the fraction field may acquire a singularity after its coefficients are reduced to the residue field. The purpose of an integral model is to retain all of this information in one object.

Fix throughout a discrete valuation ring $R$, with fraction field $K$, maximal ideal $\mathfrak m=(\pi)$, normalized valuation

$$
v:K^\times\longrightarrow\mathbf Z,
$$

and residue field $k=R/\mathfrak m$. A bar denotes reduction modulo $\mathfrak m$. We use the valuation, filtration, completion, and Hensel results established in the preceding volume. Completeness will be assumed only when an analytic limit is genuinely needed; for lifting smooth residue points, henselianity is enough.

Suppose a cubic equation has coefficients in $R$. It defines both a generic fiber over $K$ and a special fiber over $k$:

$$
\mathcal E_K \longleftarrow \mathcal E \longrightarrow \mathcal E_k.
$$

The left-hand curve is the elliptic curve of interest. The right-hand cubic is its first-order shadow at the chosen place. A unit discriminant means that smoothness survives reduction. A positive discriminant valuation means that points of the generic fiber have collided in the special fiber. The manner of collision—into a node or a cusp—governs the first approximation to the local group of points.

There is an immediate difficulty. The same curve has many equations, and their discriminants can differ by twelfth powers. Thus an arbitrary integral equation carries both arithmetic information and avoidable coordinate noise. Minimal models remove exactly that noise. Their discriminant valuation is intrinsic, and their special fiber gives the reduction type.

### 1.2 Elliptic curves and the marked point

An **elliptic curve** over a field $F$ is a smooth, proper, geometrically connected curve $E/F$ of genus one together with a specified point $O\in E(F)$. The point is not decoration. It supplies the identity for a unique algebraic group law on $E$, and it selects the linear systems that produce a Weierstrass equation.

The pole spaces $L(nO)$ have dimension $n$ for $n\geq1$. Here is the exact genus-one argument needed for that count. Since a function with a single simple pole would define a degree-one map to $\mathbf P^1$, it would make the curve rational; hence $L(O)=F$. For $n\geq1$, the principal-parts sequence at the rational point $O$ is

$$
0\longrightarrow F\longrightarrow L(nO)\longrightarrow P_n
\xrightarrow{\partial}H^1(E,\mathcal O_E)
\longrightarrow H^1(E,\mathcal O_E(nO))\longrightarrow0,
$$

where $P_n$ is the $n$-dimensional space spanned in a local parameter by $z^{-1},\ldots,z^{-n}$. The genus-one definition gives $\dim_FH^1(E,\mathcal O_E)=1$. For $n=1$, the equality $L(O)=F$ says that $\partial:P_1\to H^1(E,\mathcal O_E)$ is injective and hence an isomorphism. The map for every $n$ restricts to this one, so it is surjective. Exactness now gives

$$
\dim_F L(nO)=1+n-1=n,
\qquad H^1(E,\mathcal O_E(nO))=0. \tag{1.1}
$$

Thus no general Riemann--Roch formula is being imported. Choose

$$
x\in L(2O)\setminus L(O),\qquad
y\in L(3O)\setminus L(2O).
$$

Then $1,x,y,x^2,xy,x^3,y^2$ lie in spaces of controlled dimensions. Since $L(6O)$ has dimension $6$, these seven functions satisfy one relation. After scaling and replacing $x$ and $y$ by lower-order terms, the relation takes the form

$$
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6. \tag{1.2}
$$

Its projective closure is

$$
Y^2Z+a_1XYZ+a_3YZ^2
=X^3+a_2X^2Z+a_4XZ^2+a_6Z^3. \tag{1.3}
$$

The line $Z=0$ meets this cubic only at $O=[0:1:0]$. At that point the partial derivative with respect to $Z$ is $Y^2$, hence is nonzero. Thus $O$ is always smooth, whatever the other coefficients may be.

Conversely, a smooth projective cubic with a rational point becomes a curve of the form (1.3) after choosing that point as $O$ and a tangent-adapted projective coordinate system. Therefore general Weierstrass equations are not an arbitrary normal form: their weights reflect pole orders at the marked point.

### 1.3 The chord-and-tangent law

On a smooth plane cubic, a line meets the curve in three points counted with intersection multiplicity. Declare three collinear points $P,Q,R$ to satisfy

$$
P+Q+R=O
$$

after the usual identification of the cubic with its degree-zero divisor classes. Tangency handles the case $P=Q$, and a tangent of multiplicity three handles flexes. This construction is independent of the chosen line equations because a line section has divisor linearly equivalent to $3O$.

The divisor-class description is the conceptual proof of associativity: the map

$$
P\longmapsto [(P)-(O)]
$$

identifies the cubic with its degree-zero Picard group. The familiar ruler-and-compass picture is a computational realization of addition, not the foundation of the group axioms.

The inverse of $(x,y)$ on (1.2) is

$$
-(x,y)=(x,-y-a_1x-a_3).
$$

Indeed, the two points lie on the same vertical line, whose third intersection is $O$. This formula already warns against silently using $y\mapsto-y$: that simplification is valid only after $a_1=a_3=0$.

### 1.4 General and short equations

Over an arbitrary field, (1.2) is the correct equation. If $2$ is invertible, completing the square removes the $xy$ and $y$ terms. If $3$ is also invertible, translating $x$ removes the quadratic term. Thus when $\operatorname{char}F\ne2,3$, every elliptic curve has a **short Weierstrass equation**

$$
y^2=x^3+Ax+B. \tag{1.4}
$$

The hypotheses are exact. In characteristic $2$, the terms $a_1xy$ and $a_3y$ can contain essential information; dividing by $2$ is impossible. In characteristic $3$, completing the square is harmless but the translation needed to eliminate $x^2$ requires division by $3$. Even in characteristic zero, short form may be unsuitable over a DVR of residue characteristic $2$ or $3$, because the required denominators are not integral. A short equation over $K$ can therefore destroy the local integral information that this book is designed to measure.

For (1.4), partial differentiation gives

$$
F_x=-3x^2-A,\qquad F_y=2y
$$

for $F=y^2-x^3-Ax-B$. When the characteristic is not $2$ or $3$, a singular affine point must have $y=0$ and $3x^2+A=0$, and substitution says that $x$ is a repeated root of $x^3+Ax+B$. Thus smoothness is controlled by the discriminant of the cubic. The general equation has the same principle, but its symmetric formulas require the invariant combinations developed next.

### 1.5 Pole orders as a reconstruction principle

The functions $x$ and $y$ do more than produce one equation. They reconstruct the pointed curve from its function field together with the filtration by allowed poles at $O$:

$$
F=L(0)\subset L(O)\subset L(2O)\subset L(3O)\subset\cdots.
$$

For a genus-one curve, $L(O)=F$, $L(2O)=F\oplus Fx$, and $L(3O)=F\oplus Fx\oplus Fy$. Multiplication respects the filtration. The degree-six relation is therefore the first relation that can occur, and comparing pole orders rules out terms such as $x^2y$, which has order $7$, from a normalized relation of weight $6$.

This description proves the shape of every pointed isomorphism. Let $(x',y')$ be coordinates on another Weierstrass equation. An isomorphism fixing $O$ carries $L(2O)$ to itself, so

$$
x=\alpha x'+r
$$

with $\alpha\ne0$. It also carries $L(3O)$ to itself, so

$$
y=\beta y'+\gamma x'+t
$$

with $\beta\ne0$. Comparing the coefficients of $y'^2$ and $x'^3$ in the transformed equation gives $\beta^2=\alpha^3$. The ratio of invariant differentials supplies $u\in F^\times$ with $\alpha=u^2$ and $\beta=u^3$; then write $\gamma=u^2s$. This recovers (2.1) without assuming that arbitrary roots can be extracted in $F$.

The same filtration explains why an unpointed isomorphism is not the right notion here. Translating the group law by a rational point moves the origin and changes the spaces $L(nO)$. Elliptic-curve isomorphisms are understood to preserve $O$, and all admissible coordinate changes in this book do so.

### 1.6 Hypotheses and the boundary of the book

The basic equation theory needs only a DVR. Minimal equations likewise exist without completeness, perfection of the residue field, or characteristic-zero assumptions. When sections are lifted from the special fiber, we assume that $R$ is henselian; when inverse limits of points are discussed, we assume completeness. The construction and uniqueness of a minimal proper regular model will use the additional hypothesis that $R$ is excellent, exactly as in the regular-model theorem recalled from Book 11. Assertions about the number of rational component classes will explicitly require a finite residue field. This ledger matters because those hypotheses solve different problems and should not be bundled under the vague phrase “local field.”

Three earlier bodies of results will be used, exactly matching the dependency ledger. The valuation theory of DVRs supplies normalized valuations, unit filtrations, henselian lifting, and behavior under finite extensions. The structure theory of finite extensions supplies ramification indices, residue extensions, and the finite-étale description of unramified extensions. The theory of regular models in Book 11 supplies resolution over an excellent DVR and uniqueness of the relatively minimal regular model. The genus-one pole-space count and cubic reconstruction needed here are proved directly in Sections 1.2 and 6.2. Everything else special to elliptic cubics—the admissible coordinates, invariants, minimality tests, tangent cones, and the Frey calculation—is developed here.

There are also deliberate limits. A complete classification of every additive fiber requires a long case analysis whose small-characteristic branches depend on successively deeper congruences. We will not cite that classification as a black box. Instead, we prove the coarse trichotomy in all residue characteristics, give exact one-step minimization congruences, determine all semistable component information needed here, and say precisely where additive component or conductor data require more input. Likewise, analytic uniformization is not used to prove multiplicative reduction statements: the node, its tangent cone, and its resolution already provide the required geometry.

The convention for signs is fixed by (2.7) below. In particular, the short equation has

$$
\Delta=-16(4A^3+27B^2).
$$

Changing this sign convention would alter several mnemonic formulas, especially those involving $c_6$ and tangent square classes. It would not alter valuations or reduction types, but consistency is essential in the direct calculations.

## 2. Coordinates, weights, and invariant quantities

### 2.1 Why the coordinate changes are constrained

A change of coordinates between Weierstrass equations must fix $O$ and preserve pole orders there. The function $x$ has a double pole at $O$, while $y$ has a triple pole. Consequently a new $x$ may be scaled and shifted, but cannot contain $y$; a new $y$ may be scaled, shifted, and modified by a multiple of $x$. Every isomorphism of pointed Weierstrass cubics has the form

$$
x=u^2x'+r,\qquad
y=u^3y'+u^2s x'+t, \tag{2.1}
$$

with $u\in F^\times$ and $r,s,t\in F$.

The exponents $2$ and $3$ are forced by the pole orders. They are also forced by homogeneity: $y^2$ and $x^3$ must both scale by $u^6$. It is useful to assign weights

$$
\operatorname{wt}(x)=2,\quad \operatorname{wt}(y)=3,\quad
\operatorname{wt}(a_i)=i.
$$

Then every term in the equation has weight $6$. Later, the basic invariants will have weights $4$, $6$, and $12$. Minimality is ultimately the arithmetic consequence of these weights.

Substitution into (1.2) yields

$$
\begin{aligned}
u a_1'&=a_1+2s,\\
u^2a_2'&=a_2-sa_1+3r-s^2,\\
u^3a_3'&=a_3+ra_1+2t,\\
u^4a_4'&=a_4-sa_3+2ra_2-(t+rs)a_1+3r^2-2st,\\
u^6a_6'&=a_6+ra_4+r^2a_2+r^3-ta_3-rta_1-t^2.
\end{aligned} \tag{2.2}
$$

These formulas deserve more than rote memorization. The parameters $r,s,t$ change the chosen representatives of functions in $L(2O)$ and $L(3O)$; $u$ changes their leading terms. Translations alter coefficients but do not alter the intrinsic curve. Scaling changes a quantity of weight $w$ by $u^{-w}$ when it is expressed in the primed equation.

### 2.2 The $b$-quantities and completing the square

Define

$$
\begin{aligned}
b_2&=a_1^2+4a_2,\\
b_4&=a_1a_3+2a_4,\\
b_6&=a_3^2+4a_6,\\
b_8&=a_1^2a_6+4a_2a_6-a_1a_3a_4+a_2a_3^2-a_4^2.
\end{aligned} \tag{2.3}
$$

The first three appear by multiplying the equation by $4$ and completing the square:

$$
(2y+a_1x+a_3)^2
=4x^3+b_2x^2+2b_4x+b_6. \tag{2.4}
$$

The last is linked to them by

$$
b_2b_6-b_4^2=4b_8. \tag{2.5}
$$

Identity (2.5) can be checked by expansion, but (2.4) explains why these particular combinations occur. They package the branch polynomial of the double cover to the $x$-line without requiring division by $2$.

Under (2.1), they transform according to

$$
\begin{aligned}
u^2b_2'&=b_2+12r,\\
u^4b_4'&=b_4+rb_2+6r^2,\\
u^6b_6'&=b_6+2rb_4+r^2b_2+4r^3,\\
u^8b_8'&=b_8+3rb_6+3r^2b_4+r^3b_2+3r^4.
\end{aligned} \tag{2.6}
$$

Notice that $s$ and $t$ disappear. Completing the square has absorbed them. Translation in $x$ remains visible through $r$, so the $b_i$ are useful covariants rather than absolute invariants.

### 2.3 The fundamental invariants

Set

$$
\begin{aligned}
c_4&=b_2^2-24b_4,\\
c_6&=-b_2^3+36b_2b_4-216b_6,\\
\Delta&=-b_2^2b_8-8b_4^3-27b_6^2+9b_2b_4b_6.
\end{aligned} \tag{2.7}
$$

They satisfy the decisive identity

$$
c_4^3-c_6^2=1728\Delta. \tag{2.8}
$$

Direct substitution in (2.6) shows that all $r$-terms cancel and gives

$$
u^4c_4'=c_4,\qquad
u^6c_6'=c_6,\qquad
u^{12}\Delta'=\Delta. \tag{2.9}
$$

Thus $c_4,c_6,\Delta$ have exactly the weights predicted by the pole-order calculation. Translation changes none of them. Scaling changes them homogeneously.

When $\Delta\ne0$, define

$$
j=\frac{c_4^3}{\Delta}. \tag{2.10}
$$

The weights cancel, so $j$ is unchanged by every admissible coordinate change. Over an algebraically closed field, two elliptic curves are isomorphic if and only if they have the same $j$-invariant, with the usual understanding that the automorphism groups at $j=0$ and $1728$ are larger. Over a nonclosed field, equal $j$ need not mean isomorphic: twists become isomorphic only after extending scalars.

For the short equation $y^2=x^3+Ax+B$, the formulas reduce to

$$
c_4=-48A,\qquad c_6=-864B,\qquad
\Delta=-16(4A^3+27B^2), \tag{2.11}
$$

and hence

$$
j=1728\frac{4A^3}{4A^3+27B^2}. \tag{2.12}
$$

For example, $y^2=x^3-x$ has $\Delta=64$ and $j=1728$, while $y^2=x^3+1$ has $\Delta=-432$ and $j=0$. These values signal extra geometric symmetries; they do not by themselves determine those symmetries over the ground field.

### 2.4 The invariant differential

The regular differential attached to a Weierstrass equation is

$$
\omega=\frac{dx}{2y+a_1x+a_3}. \tag{2.13}
$$

Although the denominator may vanish at some affine points, the equation and the alternative expression

$$
\omega=\frac{dy}{3x^2+2a_2x+a_4-a_1y}
$$

show that these local formulas glue on a smooth curve. At $O$, a local-parameter calculation shows that $\omega$ is regular and nonzero. Hence it spans the one-dimensional space of regular differentials.

Under (2.1), differentiation and substitution give

$$
\omega=u^{-1}\omega'. \tag{2.14}
$$

This is the source of all the weights. If $I$ has weight $w$, then $I\omega^{\otimes w}$ is independent of the chosen Weierstrass coordinates. In particular, the discriminant determines a section of the twelfth tensor power of the Hodge line. Over a DVR, choosing a Weierstrass equation chooses a generator of that line; changing the generator changes the coefficient of this section by the inverse twelfth power.

### 2.5 A warning about equal $j$

Let $F$ have characteristic different from $2$ and let $d\in F^\times$. The quadratic twist of

$$
E:y^2=x^3+Ax+B
$$

may be written

$$
E^{(d)}:y^2=x^3+d^2Ax+d^3B.
$$

It has the same $j$-invariant, but the isomorphism uses a square root of $d$. If $d$ is not a square in $F$, the curves need not be $F$-isomorphic. Locally, twisting by a uniformizer can change good reduction into additive reduction while preserving $j$. This counterexample is crucial: $j$ measures the geometric isomorphism class, whereas an integral model also records how that class is situated over the valued field.

### 2.6 Deriving the identities rather than memorizing them

There are two efficient routes to the invariant identities. The first starts from the completed-square cubic

$$
G(X)=4X^3+b_2X^2+2b_4X+b_6.
$$

Translation $X=X'-b_2/12$ depresses this cubic when $6$ is invertible. Its resulting linear and constant coefficients are scalar multiples of $-c_4$ and $-c_6$, and its polynomial discriminant is a scalar multiple of $\Delta$. This derivation explains simultaneously why $c_4,c_6$ are translation invariant and why (2.8) has the shape of a cubic-square relation.

The second route works integrally. Treat $a_1,a_2,a_3,a_4,a_6,r,s,t,u$ as independent variables. Substitute (2.2) into (2.3), simplify successively using (2.5), and obtain (2.6) and (2.9). Because all formulas are polynomial identities over $\mathbf Z[u,u^{-1}]$, checking them where $6$ is invertible proves them universally. This principle is legitimate for identities, though not for performing a nonintegral coordinate change on a particular model.

Identity (2.8) imposes useful valuation restrictions. If $c_4$ is a unit and $\Delta\in\mathfrak m$, then $c_6$ is a unit and

$$
\overline{c_6}^{\,2}=\overline{c_4}^{\,3}.
$$

If $\Delta$ is a unit, $c_4$ may or may not be a unit in residue characteristics $2$ and $3$, because $1728$ is then nonunit or zero in $k$. This is another reason not to infer good reduction from $c_4$ alone.

The weights also provide a dimensional check on calculations. Every monomial in $c_4$ must have total weight $4$, every monomial in $c_6$ weight $6$, and every monomial in $\Delta$ weight $12$. A term of the wrong weight certifies an algebraic error before any expansion is completed.

## 3. Discriminant and smoothness

### 3.1 The discriminant as a collision detector

For a monic polynomial, the discriminant vanishes exactly when two roots collide. A Weierstrass cubic is slightly more elaborate because $y$ participates, but equation (2.4) reduces the issue to the same phenomenon whenever $2$ is invertible. The invariant formula remains valid in every characteristic.

**Theorem 3.1 (smoothness criterion).** A projective Weierstrass cubic over a field $F$ is smooth if and only if $\Delta\ne0$.

**Proof strategy.** Smoothness and the condition $\Delta\ne0$ are unchanged by field extension, so one may pass to an algebraic closure. When $2$ is invertible, complete the square and use the ordinary discriminant of a cubic; this includes characteristic $3$ and requires no depressed cubic. In characteristic $2$, the cases $a_1\ne0$ and $a_1=0$ can be read directly from the partial derivatives. This avoids specializing an elimination argument across primes where its leading coefficients could vanish.

**Proof.** First suppose that $2$ is invertible. Completing the square gives

$$
(2y+a_1x+a_3)^2=4x^3+b_2x^2+2b_4x+b_6.
$$

A singular point has $2y+a_1x+a_3=0$, and its $x$-coordinate is a common root of the cubic on the right and its derivative. The polynomial discriminant of that cubic is $16\Delta$. Hence a singular point exists exactly when $\Delta=0$. This argument includes characteristic $3$. When $3$ is invertible as well, it reduces to the familiar short-form calculation: for $y^2=x^3+Ax+B$, a singular point must satisfy

$$
y=0,\qquad 3x^2+A=0,\qquad x^3+Ax+B=0.
$$

The last two conditions say that $x$ is a common root of $X^3+AX+B$ and its derivative. This happens exactly when

$$
4A^3+27B^2=0,
$$

which by (2.11) is equivalent to $\Delta=0$.

It remains to treat characteristic $2$. Write the affine defining polynomial as

$$
F=y^2+a_1xy+a_3y-x^3-a_2x^2-a_4x-a_6.
$$

Here $F_y=a_1x+a_3$. If $a_1\ne0$, this equation fixes $x_0=a_3/a_1$, and $F_x=0$ then fixes $y_0=(x_0^2+a_4)/a_1$. Direct substitution, using the characteristic-$2$ expression for $\Delta$, gives

$$
a_1^6F(x_0,y_0)=\Delta.
$$

Thus a singular point exists exactly when $\Delta=0$. If $a_1=0$ but $a_3\ne0$, then $F_y$ never vanishes, while $\Delta=a_3^4\ne0$. Finally, if $a_1=a_3=0$, then $F_y=0$ identically. Over the algebraic closure the equation $F_x=0$ has a solution $x_0$, and $F(x_0,y)=0$ then has a solution $y_0$ because it is a square equation. The cubic is singular, in agreement with $\Delta=0$ in this case. The point $O$ is always smooth, so these affine calculations handle the whole projective cubic. $\square$

### 3.2 Node or cusp

Assume now that $\Delta=0$, so the cubic is singular. An irreducible plane cubic has exactly one singular point. Its lowest-degree nonzero part in local coordinates is the **tangent cone**. If that quadratic part is a product of two distinct lines over an algebraic closure, the singularity is a node. If it is a repeated line, the singularity is a cusp.

The invariant $c_4$ distinguishes them:

$$
\begin{array}{c|c}
\Delta=0,\ c_4\ne0 & \text{node},\\
\Delta=0,\ c_4=0 & \text{cusp}.
\end{array} \tag{3.1}
$$

To see the geometry when $2$ is invertible, complete the square and translate a repeated root to $0$. A nodal equation becomes

$$
y^2=x^2(x+\lambda),\qquad \lambda\ne0,
$$

whose tangent cone is $y^2-\lambda x^2$. A cuspidal equation becomes $y^2=x^3$, whose tangent cone is $y^2$. In the first case $c_4$ is nonzero; in the second it vanishes. In characteristic $3$, $c_4=b_2^2$, and the completed-square cubic has a double root when $b_2\ne0$ and a triple root when $b_2=0$. In characteristic $2$, $c_4=a_1^4$. At a singular point the quadratic tangent cone has cross term $a_1XY$; if $a_1\ne0$, its slope polynomial is separable and has two distinct roots over an algebraic closure, while if $a_1=0$ the quadratic is a square. This proves (3.1) in every characteristic.

A reducible cubic can also occur in a nonminimal or badly chosen family, but the special fiber of a minimal Weierstrass equation for an elliptic curve has the singular behavior relevant to reduction encoded by the same criterion. Passing later to a regular model may separate components that the plane cubic has contracted.

### 3.3 The smooth locus of a singular cubic

The smooth points of a singular cubic still form an algebraic group with identity $O$. For a nodal cubic this group is a one-dimensional torus; after the two tangent directions are defined, it is isomorphic to $\mathbf G_m$. For a cuspidal cubic it is isomorphic to $\mathbf G_a$.

These statements can be seen by normalization. The normalization of a singular cubic is $\mathbf P^1$. In the nodal case two points of $\mathbf P^1$ map to the node. Removing them leaves $\mathbf P^1\setminus\{0,\infty\}\cong\mathbf G_m$ after a suitable coordinate choice. In the cuspidal case one point lies over the cusp; removing it leaves $\mathbf A^1\cong\mathbf G_a$. The chord-and-tangent law agrees with multiplication or addition under these parametrizations.

The nodal torus need not split over $F$. Its two tangent directions may be exchanged by the quadratic Galois action. It is split precisely when both directions are defined over $F$. This elementary tangent criterion will become the definition of split multiplicative reduction. No analytic parametrization is needed for it.

The normalization can be made explicit. For

$$
C:y^2=x^2(x+\lambda),\qquad \lambda\ne0,
$$

put $t=y/x$ away from the node. Then

$$
x=t^2-\lambda,\qquad y=t(t^2-\lambda). \tag{3.2}
$$

This extends to a normalization map $\mathbf P^1\to C$. The two points $t=\pm\sqrt\lambda$ lie above the node, while $t=\infty$ maps to $O$. If $\alpha^2=\lambda$, the rational function

$$
q=\frac{t-\alpha}{t+\alpha}
$$

identifies the complement of the two preimages with $\mathbf G_m$ and sends $O$ to $1$. A direct substitution into the chord formula shows

$$
q(P+Q)=q(P)q(Q).
$$

If $\alpha\notin F$, the nontrivial automorphism of $F(\alpha)/F$ sends $q$ to $q^{-1}$. Thus the descended group is the one-dimensional torus whose points become multiplicative after the quadratic extension. Splitness is exactly the rationality of $\alpha$.

For the cusp $C:y^2=x^3$, normalization is

$$
t\longmapsto (t^2,t^3).
$$

The point $t=0$ maps to the cusp and $t=\infty$ to $O$. On the smooth locus, $s=t^{-1}$ is an affine coordinate with $O$ at $s=0$. The tangent construction gives $s(P+Q)=s(P)+s(Q)$. This supplies an explicit additive parametrization and confirms that the distinction between node and cusp is a distinction between multiplication and addition.

### 3.4 Worked singular fibers

Consider

$$
C_\lambda:y^2=x^2(x+\lambda)
$$

over a field of characteristic different from $2$, with $\lambda\ne0$. At $(0,0)$ the tangent cone is

$$
y^2-\lambda x^2.
$$

The node is split if and only if $\lambda$ is a square. Thus the equations with $\lambda=1$ and with a nonsquare $\lambda$ are geometrically the same nodal cubic but have different rational smooth-locus groups: one is $\mathbf G_m$, the other a nonsplit one-dimensional torus.

By contrast,

$$
C:y^2=x^3
$$

has a cusp. The parametrization $t\mapsto(t^{-2},t^{-3})$ describes the normalization away from the point at infinity, and a reciprocal parameter identifies the smooth locus with an additive line. Multiplicative and additive reduction are therefore not merely names borrowed from group theory; they are visible in the normalization of the reduced cubic.

Finally, the family

$$
y^2=x^3+x+t
$$

over $k[[t]]$, with $\operatorname{char}k\ne2,3$, has

$$
\Delta=-16(4+27t^2),
$$

which is a unit. Its special fiber is smooth. The family $y^2=x^3+x^2+t$ may have a singular special fiber even though its generic fiber is smooth. The valuation of $\Delta$, not the apparent complexity of the coefficients, detects the collision.

### 3.5 Discriminant valuation as collision thickness

The equation $\Delta=0$ detects collision on a single fiber. Over a DVR, the positive integer $v(\Delta)$ measures how closely the branches approach before colliding. The simplest illustration is a monic polynomial with roots in an extension field: its discriminant is the product of squared root differences. Every pair that becomes congruent contributes twice the valuation of its difference.

For a Weierstrass equation with $2$ invertible, (2.4) makes the same interpretation available. If

$$
4x^3+b_2x^2+2b_4x+b_6=4(x-e_1)(x-e_2)(x-e_3),
$$

then, up to a unit depending only on the leading coefficient,

$$
\Delta=16\prod_{i<j}(e_i-e_j)^2. \tag{3.3}
$$

The roots may live in a splitting field, but the product lies in $K$. If exactly one pair has difference of valuation $n$ and all other differences are units, then $v(\Delta)=2n$ and the reduction is nodal. If all three pairwise differences have positive valuation, the visible special fiber is cuspidal, although a common weighted scaling may show that the equation was not minimal.

The word “thickness” must be used with the minimality qualification. Replacing $x,y$ by $\pi^2x',\pi^3y'$ adds $12$ to the equation discriminant without changing the curve. Only $v(\Delta_{\min})$ measures intrinsic degeneration. In a nodal minimal model, that exponent also measures the thickness of the node in the total space and later becomes the number of components after regular resolution in the split case.

Consider two families over a DVR of odd residue characteristic:

$$
y^2=x(x-1)(x-1-\pi^n)
$$

and

$$
y^2=x(x-\pi^{2m})(x-2\pi^{2m}).
$$

In the first, one pair of roots approaches to order $n$, $c_4$ remains a unit, and the minimal discriminant exponent is $2n$. In the second, all roots share the scale $\pi^{2m}$; scaling it away lowers the discriminant by $12m$. These are respectively genuine collision and artificial magnification.

## 4. Integral Weierstrass models

### 4.1 What integrality accomplishes

An equation over $K$ has no special fiber until its coefficients are made integral. An **integral Weierstrass equation** has $a_1,a_2,a_3,a_4,a_6\in R$. Its projective equation defines a flat proper cubic $\mathcal W\to\operatorname{Spec}R$ with section $O$. Flatness follows because the homogeneous cubic is primitive and monic in the appropriate affine sense; more concretely, its coordinate ring has no $R$-torsion. The generic fiber is the original elliptic curve when $\Delta\ne0$.

Every elliptic curve over $K$ has an integral equation. Begin with any Weierstrass equation. Choose $n$ large enough that

$$
v(a_i)+in\geq0
$$

for every $i$. In (2.1), take $u=\pi^{-n}$ and $r=s=t=0$. Formula (2.2) gives

$$
a_i'=\pi^{in}a_i\in R.
$$

The new discriminant is $\Delta'=\pi^{12n}\Delta$. Thus denominators can always be cleared, but doing so may insert an arbitrarily large twelfth-power factor into the discriminant. Integrality is existence; minimality will be normalization.

### 4.2 Integral coordinate changes

If

$$
u\in R^\times,\qquad r,s,t\in R,
$$

then (2.1) is an **integral admissible change of coordinates**. Both it and its inverse are defined over $R$, so it gives an isomorphism of integral Weierstrass models. Formula (2.9) shows that it changes $\Delta$ by a unit twelfth power and hence preserves $v(\Delta)$.

If $u\in R$ is a nonunit, the primed coefficients in (2.2) require divisibility by $u^i$. When those divisibilities hold, the new equation is integral and

$$
v(\Delta')=v(\Delta)-12v(u). \tag{4.1}
$$

This is a contraction of the chosen integral lattice of functions. It improves the discriminant. Conversely, choosing $u$ of negative valuation always worsens it. The translation parameters matter because they may expose hidden divisibility before the scaling is performed.

This last point is especially important in residue characteristics $2$ and $3$. An equation can have each $a_i$ apparently insufficiently divisible, yet after a carefully chosen $r,s,t$ all transformed numerators in (2.2) become divisible by the appropriate powers of $\pi$. Looking only at the original coefficients can therefore miss nonminimality.

### 4.3 Integral equations are not all equivalent

Over $K$, the equations

$$
y^2=x^3+Ax+B
$$

and

$$
y^2=x^3+\pi^4Ax+\pi^6B
$$

define isomorphic curves by $x=\pi^2x',y=\pi^3y'$. If $A,B\in R$, both are integral. Their discriminant valuations differ by $12$. The second equation creates an unnecessarily singular special fiber: modulo $\pi$ it becomes $y^2=x^3$, regardless of the reduction of the first equation.

This example explains why reduction type cannot be read from an arbitrary integral equation. An artificially enlarged equation can turn a smooth reduction into a cusp. Minimality removes exactly such artificial dilations.

There is a converse subtlety. Translation can improve an equation before scaling. Over a DVR in which $6$ is a unit, consider

$$
y^2=(x-r)^3+\pi^4A(x-r)+\pi^6B
$$

with $r\in R$. Expanded coefficients may include units. Translating $x$ by $r$ reveals the common weights and allows division by the appropriate powers of $\pi$. Minimality is a property of the entire admissible coordinate orbit, not of a coefficient list viewed in isolation.

### 4.4 The differential lattice

An integral equation supplies an invariant differential $\omega$. Replacing the equation integrally with unit $u$ replaces $\omega$ only by a unit. A nonunit improvement with parameter $u$ satisfies $\omega=u^{-1}\omega'$, so $\omega'$ is more divisible as a generator of the differential lattice.

This viewpoint turns the discriminant calculation into a lattice calculation. If an equation is improved by one valuation step, its new differential is $\pi$ times the old one and its discriminant valuation drops by twelve. Thus, among the lattices $R\omega$ supplied by integral equations, a minimal equation supplies the smallest lattice, or equivalently the most divisible generator. Worsening an equation produces arbitrarily larger lattices and arbitrarily larger discriminant valuations, so reversing “smallest” and “largest” here would make the statement visibly impossible.

The differential language is also coordinate-independent. It will explain why two minimal equations differ integrally even when coefficient manipulation is unpleasant in small residue characteristic.

### 4.5 What a Weierstrass model forgets

An integral Weierstrass model is proper and flat, but three desirable properties must be distinguished.

- It is **smooth** exactly when its discriminant is a unit.
- It is **regular** when every local ring of the two-dimensional total space is regular.
- It is **minimal as a Weierstrass equation** when its discriminant valuation cannot be lowered.

A minimal equation can have singular special fiber, so it need not be smooth. Its total space can also be singular at the singular point of that fiber, so it need not be regular. Blowing up repairs regularity but usually produces several special-fiber components and leaves the category of plane cubic equations. Conversely, an arbitrary blowup of a smooth point remains regular but is no longer minimal as a regular model.

These distinctions organize the later constructions:

$$
\begin{array}{c}
\text{minimal Weierstrass model}\\
\downarrow\ \text{resolve singularities}\\
\text{minimal proper regular model}\\
\downarrow\ \text{take smooth locus}\\
\text{smooth component strata met by sections}.
\end{array}
$$

The first object is computational, the second exposes components and intersections, and the third records where sections can specialize. In good reduction all three coincide. In bad reduction their difference is precisely the geometry created by degeneration. A full smooth-model mapping property is a stronger theorem and will not be assumed here.

There is also a warning about terminology. “Minimal model” in this book means a minimal Weierstrass equation unless “regular” is explicitly inserted. The two minimality notions are compatible but not identical: one minimizes discriminant weight among cubic equations, the other contracts exceptional curves among regular surfaces.

## 5. Minimal equations and the minimal discriminant

### 5.1 Existence by well-ordering

An integral Weierstrass equation for $E/K$ is **minimal** if its discriminant valuation is least among all integral Weierstrass equations for $E$. The set of such valuations is a nonempty subset of $\mathbf Z_{\geq0}$: nonempty by denominator clearing, and nonnegative because the discriminant of an integral equation lies in $R$. Therefore it has a least element.

**Theorem 5.1 (existence of a minimal equation).** Every elliptic curve over the fraction field of a DVR has a minimal integral Weierstrass equation.

This proof is short because discreteness has done the work. Over a nondiscrete valuation ring, an infimum of discriminant values need not be attained. The theorem is therefore genuinely about DVRs, not merely about valuation rings.

If $\mathcal E$ is minimal, its **minimal discriminant ideal** is

$$
\mathfrak D_{E/K}=(\Delta_{\min})=\mathfrak m^{v(\Delta_{\min})}. \tag{5.1}
$$

The element $\Delta_{\min}$ is determined only up to a unit twelfth power, but its principal ideal and valuation are intrinsic. We write

$$
\delta(E/K)=v(\Delta_{\min}).
$$

### 5.2 Essential uniqueness

Minimal equations are not literally unique: integral translations and unit scalings produce many of them. They are, however, unique in exactly the sense arithmetic requires.

**Theorem 5.2 (integral uniqueness).** Let two minimal integral Weierstrass equations over $R$ define isomorphic elliptic curves over $K$, with the isomorphism carrying origin to origin. Then the isomorphism is given by (2.1) with

$$
u\in R^\times,\qquad r,s,t\in R.
$$

Consequently their discriminants differ by a unit twelfth power, their invariant differentials generate the same $R$-lattice, and their special fibers are isomorphic as pointed cubics.

**Proof strategy.** Equality of the two minimal discriminant valuations first forces $u$ to be a unit. Integrality of $r$ is then detected by the $x$-coordinates of prime-to-residue-characteristic torsion: the two-division cubic works when $2$ is a unit, and the explicit three-division quartic works in residue characteristic $2$. Once $r$ is integral, the first, second, third, and sixth coefficient identities force $s$ and $t$ to be integral by unequal-valuation arguments.

**Proof.** Any pointed isomorphism between the generic fibers has the form (2.1). Formula (2.9) gives

$$
v(\Delta')=v(\Delta)-12v(u).
$$

Both discriminant valuations are minimal and hence equal, so $v(u)=0$. Thus $u$ is a unit.

We first prove $r\in R$. If $2$ is a unit, the polynomial

$$
x^3+\frac{b_2}{4}x^2+\frac{b_4}{2}x+\frac{b_6}{4}
$$

is monic and integral, and its roots are the affine $x$-coordinates of the nonzero points killed by $2$. If $2$ is not a unit, then $3$ is a unit and the chord-and-tangent calculation for tripling gives the three-division polynomial

$$
\psi_3(x)=3x^4+b_2x^3+3b_4x^2+3b_6x+b_8.
$$

After division by the unit $3$, this too is monic and integral, and its roots are the $x$-coordinates of the nonzero points killed by $3$. Choose a root in an algebraic closure and transport the corresponding torsion point through the isomorphism. Its two $x$-coordinates, say $\alpha$ and $\alpha'$, are integral over $R$, while (2.1) gives

$$
r=\alpha-u^2\alpha'.
$$

Thus $r$ is integral over $R$. Since $r\in K$ and a DVR is integrally closed in $K$, $r\in R$.

Set $A_1'=ua_1'\in R$. The first identity gives $a_1=A_1'-2s$. Substitution in the second identity yields

$$
u^2a_2'=a_2-sA_1'+s^2+3r.
$$

If $v(s)<0$, the term $s^2$ has strictly smaller valuation than every other term on the right, which is impossible because the left side is integral. Hence $s\in R$.

Finally set $A_3'=u^3a_3'\in R$. The third identity gives $a_3=A_3'-ra_1-2t$. Substitute this in the sixth identity of (2.2). All terms not displayed below are integral because $r,s$ and the coefficients are integral, while the terms involving $t$ combine as

$$
-t a_3-rta_1-t^2=-tA_3'+t^2.
$$

If $v(t)<0$, the term $t^2$ again has uniquely least valuation, a contradiction. Therefore $t\in R$. The change is integral, and all stated consequences follow. $\square$

The torsion polynomials are used only as monic integrality detectors for the translation $r$; no structure theorem about torsion is being imported.

### 5.3 Immediate valuation criteria

Suppose an integral equation is not minimal. Comparing it with a minimal equation and using (2.9), the original invariants necessarily satisfy

$$
v(c_4)\geq4,\qquad v(c_6)\geq6,\qquad v(\Delta)\geq12. \tag{5.2}
$$

We obtain useful one-way tests.

**Proposition 5.3 (quick minimality tests).** An integral equation is minimal if any one of the following holds:

$$
v(\Delta)<12,\qquad v(c_4)<4,\qquad v(c_6)<6. \tag{5.3}
$$

These tests require no hypothesis on residue characteristic. Their converses are false in general: the three divisibilities in (5.2) do not always produce integral $r,s,t$ that permit a scaling. This failure is most visible in residue characteristics $2$ and $3$.

For example, $v(\Delta)=12$ alone does not prove nonminimality. The discriminant may genuinely vanish to order $12$ on a minimal model. One must exhibit an improving admissible change or use a criterion with stronger hypotheses.

### 5.4 The short-form criterion away from $2$ and $3$

Assume $2,3\in R^\times$. Completing the square and depressing the cubic are integral operations, so every integral general equation is integrally equivalent to a short equation

$$
y^2=x^3+Ax+B,\qquad A,B\in R.
$$

Moreover, an isomorphism between two short equations has no translation terms: equations (2.2) force $s=t=r=0$ because $2$ and $3$ are units. It follows that such an equation is nonminimal exactly when one can scale by a positive power of $\pi$ while retaining integrality.

**Proposition 5.4 (short minimality criterion).** If the residue characteristic is neither $2$ nor $3$, an integral short equation is minimal if and only if

$$
v(A)<4\quad\text{or}\quad v(B)<6. \tag{5.4}
$$

Equivalently, it is nonminimal precisely when $\pi^4\mid A$ and $\pi^6\mid B$.

**Proof.** If both divisibilities hold, write $A=\pi^4A'$ and $B=\pi^6B'$ and make the change $x=\pi^2x',y=\pi^3y'$. The new equation is integral and its discriminant valuation is lower by $12$. Conversely, if the equation is nonminimal, compare it with a minimal short equation. The preceding observation makes the isomorphism a pure scaling, so (2.2) forces exactly these divisibilities. $\square$

The hypothesis concerns the residue characteristic, not merely $\operatorname{char}K$. Over a $2$-adic or $3$-adic field, the fraction field has characteristic zero but division by $2$ or $3$ can destroy integrality.

### 5.5 A minimality calculation

Let $R$ have residue characteristic at least $5$, and consider

$$
E:y^2=x^3+\pi^4ux+\pi^5w,\qquad u,w\in R^\times.
$$

Although $A$ is divisible by $\pi^4$, $B$ is not divisible by $\pi^6$, so the equation is minimal. Its discriminant is

$$
\Delta=-16\bigl(4\pi^{12}u^3+27\pi^{10}w^2\bigr).
$$

The two terms have unequal valuations, so they cannot cancel and $v(\Delta)=10$. This also proves minimality by the first test in (5.3).

If instead $B=\pi^6w$, both coefficients can be scaled down. The equation is not minimal and becomes $y^2=x^3+ux+w$. Its apparently cuspidal special fiber was an artifact of the nonminimal coordinates. This pair of examples separates genuine discriminant vanishing from artificial weighted divisibility.

### 5.6 Minimal discriminant versus equation discriminant

For any integral equation of $E$,

$$
v(\Delta)=\delta(E/K)+12n
$$

for some integer $n\geq0$. Indeed, compare it with a minimal equation; equality of invariant weights shows the difference is a multiple of $12$, and minimality fixes its sign. Thus the residue class of $v(\Delta)$ modulo $12$ is curve-invariant, but it is much weaker than the minimal valuation itself.

This explains a common computational error. Reducing a discriminant exponent modulo $12$ does not find the minimal exponent: both $2$ and $14$ have residue $2$, but a curve can genuinely have minimal exponent $14$. Only an admissible integral improvement justifies subtracting $12$.

### 5.7 A practical minimization strategy

The existence proof by well-ordering does not tell us how to reach a minimal equation. In practice, the following loop mirrors its logic.

Begin with an integral equation and compute $c_4,c_6,\Delta$. If one of the inequalities (5.3) holds, stop. Otherwise reduce the equation and find its singular point. A one-step improvement must contract the entire special fiber toward that point, so use integral $r,t$ to move it to $(0,0)$ and use $s$ to normalize the tangent direction. Test the weighted congruences (10.1). If they hold, divide coefficients by $\pi^i$ according to their weights and repeat.

Why must the singular point be rational if a one-step improvement exists? Start with the improved equation and reverse the scaling $x=\pi^2x',y=\pi^3y'$, including translations. Modulo $\pi$, every affine point is contracted to the residue of $(r,t)$, and the reduced cubic has its cusp there. Thus the needed center and repeated tangent are already defined over $k$. Failure to find such a residue point rules out a one-step improvement over $K$, though an unramified extension might make a geometrically defined center rational only if one has not begun with the actual contraction data.

At residue characteristic at least $5$, integral short form makes the loop almost trivial: after translation to short form, test $v(A)\geq4$ and $v(B)\geq6$ and scale whenever both hold. At $2$ and $3$, the $a_1,a_3$ or $a_2$ terms retain information and the full congruence test is essential.

Termination is automatic. Every successful step decreases the nonnegative integer $v(\Delta)$ by $12$. The process therefore stops after at most $\lfloor v(\Delta)/12\rfloor$ improvements. What requires thought is not termination but finding the translations that expose weighted divisibility.

A useful certificate of minimality is consequently one of three kinds:

1. a low invariant valuation as in (5.3);
2. the short-form criterion under the exact unit hypotheses on $6$;
3. a proof that the congruence system for every possible singular center has no solution.

Merely reporting that a finite search found no change would not explain the arithmetic. A mathematical proof identifies why the necessary center, tangent, or higher divisibility fails.

### 5.8 Minimal differentials and uniqueness revisited

The invariant differential gives a coordinate-free formulation of minimality. Let $\Omega(E/K)$ be the one-dimensional $K$-space of regular differentials on $E$. Every integral Weierstrass equation supplies an $R$-lattice $R\omega\subset\Omega(E/K)$. If two equations are related by (2.1), then (2.14) says

$$
R\omega=Ru^{-1}\omega'.
$$

The lattices arising from integral equations are totally ordered because all lattices in a one-dimensional $K$-space over a DVR are of the form $\pi^mR\omega_0$.

More precisely, an improvement with parameter of valuation $n$ has $\omega'=\pi^n\varepsilon\omega$ for a unit $\varepsilon$ and therefore replaces $R\omega$ by the smaller lattice $\pi^nR\omega$. There is a smallest lattice arising from an integral Weierstrass equation. Existence follows from the same well-ordering argument as minimal discriminants: shrinking by one step lowers the nonnegative discriminant valuation by $12$, so indefinite shrinking is impossible. An equation is minimal exactly when its differential generates this smallest lattice.

This statement sharpens essential uniqueness. By Theorem 5.2, two minimal equations yield the same differential lattice and also the same pole lattices. For any one minimal equation these are

$$
\mathcal L_2=R\oplus Rx,\qquad
\mathcal L_3=R\oplus Rx\oplus Ry.
$$

Indeed, an integral unit change sends $x$ to a unit multiple of $x'$ plus an element of $R$, and sends $y$ to a unit multiple of $y'$ plus an $R$-linear combination of $1$ and $x'$. Thus Theorem 5.2 makes these lattices independent of the chosen minimal equation. This consequence, rather than a second proof of integral uniqueness, is what is used in the unramified descent argument of Proposition 9.1.

The formulation also explains base change. Under an unramified extension, the value group does not acquire fractional steps, so the smallest differential lattice simply tensors with the new DVR. Under ramified extension, new intermediate lattices appear. An additive equation may cease to be minimal because one of those smaller lattices supports an integral equation; a multiplicative equation cannot, because its unit $c_4$ prevents any further shrinking.

Finally, the differential perspective clarifies the twelfth power. It is not an accidental feature of a complicated polynomial. The discriminant is a weight-$12$ object on a one-dimensional differential line. Changing the integral generator by one uniformizer must change its valuation by twelve.

## 6. Reading the special fiber

### 6.1 Reduction of a minimal equation

Fix a minimal equation $\mathcal W$ for $E/K$. Reducing its coefficients gives a projective Weierstrass cubic $\widetilde E/k$. Essential uniqueness makes this pointed cubic independent, up to $k$-isomorphism, of the chosen minimal equation. We may therefore use its geometry to define the reduction type.

Because reduction commutes with the invariant polynomials, $\overline\Delta=0$ if and only if the special fiber is singular. The $c_4$ criterion then separates node from cusp. This yields the trichotomy:

$$
\begin{array}{c|c|c}
\text{condition on a minimal equation} & \text{special fiber} & \text{reduction}\\ \hline
v(\Delta)=0 & \text{smooth cubic} & \text{good}\\
v(\Delta)>0,\ v(c_4)=0 & \text{nodal cubic} & \text{multiplicative}\\
v(\Delta)>0,\ v(c_4)>0 & \text{cuspidal cubic} & \text{additive}.
\end{array} \tag{6.1}
$$

In the second row, identity (2.8) implies $v(c_6)=0$ as well. The conditions are conditions on a minimal equation; on a nonminimal equation they need not describe the curve.

### 6.2 Good reduction

The curve has **good reduction** when its minimal special fiber is smooth. Equivalently,

$$
\delta(E/K)=0. \tag{6.2}
$$

In this case the integral Weierstrass model itself is smooth and proper over $R$. Its fibers form an elliptic curve family, and the group law extends over $R$. Every section may be reduced, and smoothness makes the local structure uniform from generic to special fiber.

There is an intrinsic criterion that does not mention a chosen equation.

**Theorem 6.1 (good-reduction criterion).** The following are equivalent:

1. $E$ has good reduction.
2. The pointed curve $(E,O)$ extends to a smooth proper relative curve of genus one over $R$ with geometrically connected fibers and a section extending $O$.
3. Some integral Weierstrass equation for $E$ has unit discriminant.

**Proof.** Conditions 1 and 3 are equivalent by definition and minimality. A unit-discriminant Weierstrass model is smooth by the fiberwise discriminant criterion and proper by construction, giving 2. Conversely, let $f:\mathcal E\to\operatorname{Spec}R$ be as in 2. We spell out the relative pole-space step. For every $n>0$, formula (1.1) on the generic and special fibers gives

$$
H^1(\mathcal E_s,\mathcal O_{\mathcal E_s}(nO_s))=0,
\qquad
\dim H^0(\mathcal E_s,\mathcal O_{\mathcal E_s}(nO_s))=n.
$$

For clarity, the needed base-change step is only the following two-term calculation. Cohomology of a line bundle on a proper flat relative curve is represented over the affine base by a map $C^0\to C^1$ of finite free $R$-modules; one obtains such a complex from a finite affine Cech resolution and finite presentations, and relative dimension one removes higher terms. Reduction of its cokernel is $H^1$ on the special fiber. The displayed fiberwise vanishing therefore makes $C^0\to C^1$ surjective modulo $\mathfrak m$, hence split surjective over the local ring by Nakayama's lemma. Its cokernel vanishes and its kernel is finite free, with formation commuting with every residue-field base change. Applied to $\mathcal O(nO)$, this shows that $f_*\mathcal O(nO)$ is free of rank $n$ and commutes with reduction.

Choose compatible bases $1,x$ and $1,x,y$ in ranks two and three. The seven monomials

$$
1,x,y,x^2,xy,x^3,y^2
$$

lie in the rank-six module $f_*\mathcal O(6O)$. Fiberwise, the pole-order argument of Section 1.2 says that the first six appropriate leading terms span and that there is one relation, uniquely normalized to be monic in $y^2$ and $x^3$. Reduction and Nakayama lift that relation over $R$, giving a general integral Weierstrass equation. On each geometric fiber, $x$ has pole divisor $2O$ and $y$ has pole divisor $3O$, so they generate the function field and the relation is the irreducible cubic equation of the image. If that cubic were singular, Section 3.3 would make its normalization $\mathbf P^1$, contradicting that its function field has genus one. Thus every geometric fiber of the equation is smooth. Theorem 3.1 says that its discriminant vanishes in no residue field; over the local ring $R$ it is therefore a unit. $\square$

The properness in condition 2 matters. A smooth open model can discard the singular point of a bad special fiber and therefore exists in bad reduction as well.

### 6.3 Multiplicative reduction and splitting

The curve has **multiplicative reduction** when the minimal special fiber is nodal. Its smooth locus is a one-dimensional $k$-torus. The reduction is **split multiplicative** when that torus is $k$-isomorphic to $\mathbf G_m$, and **nonsplit multiplicative** otherwise.

Equivalently, inspect the tangent cone at the node. If its two lines are defined over $k$, the reduction is split. If they become defined only over a separable quadratic extension and are exchanged by its nontrivial automorphism, it is nonsplit. This definition works in every characteristic and does not depend on a chosen normal form.

When $\operatorname{char}k\ne2$, a commonly useful invariant test is

$$
\text{split multiplicative}\quad\Longleftrightarrow\quad
-\overline{c_6}\text{ is a square in }k^\times. \tag{6.3}
$$

The criterion follows by translating the node to the origin and comparing the discriminant of its tangent cone with $-c_6$. In characteristic $2$, one should use the tangent cone directly; phrasing the test as an ordinary square condition can lose the separable quadratic information.

Over a finite residue field, every one-dimensional torus splits over the unramified quadratic extension. Hence nonsplit multiplicative reduction becomes split after that extension. The curve remains multiplicative: unramified base change changes the rationality of tangent directions, not the node itself.

### 6.4 Additive reduction

The curve has **additive reduction** when the minimal special fiber is cuspidal. The smooth locus of that cubic is $\mathbf G_a$. The word “additive” describes this first smooth quotient; it does not claim that the entire local point group is the additive group of $K$.

Additive reduction is the least stable member of the trichotomy. After a finite extension it may become good or multiplicative. Twisting gives simple examples. If $E$ has good reduction and $d=\pi$, then a quadratic twist often has positive valuations of $c_4$ and $\Delta$, and hence additive reduction, even though it returns to good reduction after adjoining $\sqrt\pi$. Thus the same geometric $j$-invariant can support distinct integral behaviors.

The label “additive” intentionally suppresses the finer configurations that appear after resolving the cusp and the singularities of the total space. Those configurations are important for exact component groups and systematic conductor formulas, but the foundational trichotomy requires only the minimal cubic and its smooth locus.

### 6.5 A reduction decision procedure

For a concrete curve over $K$, the reliable procedure is:

1. Find an integral Weierstrass equation.
2. Prove it minimal, either by an explicit criterion or by ruling out every improving change.
3. Compute $c_4$ and $\Delta$.
4. If $v(\Delta)=0$, reduction is good.
5. If $v(\Delta)>0$ and $v(c_4)=0$, reduction is multiplicative; inspect the tangent cone for splitting.
6. If both valuations are positive, reduction is additive.

The ordering is essential. Applying steps 3--6 before step 2 can assign the wrong type. For the nonminimal equation

$$
y^2=x^3+\pi^4Ax+\pi^6B
$$

with $4A^3+27B^2$ a unit, the special fiber is cuspidal and both displayed invariants have positive valuation. After scaling down, the minimal equation has good reduction. The apparent additive fiber was coordinate noise.

### 6.6 Three nearby curves with different reduction

Assume the residue characteristic is at least $5$ and choose units $u,w\in R^\times$.

First consider

$$
E_g:y^2=x^3+ux+w
$$

with $4u^3+27w^2$ a unit. Its discriminant is a unit, so it has good reduction.

Next choose $w$ so that $4u^3+27w^2\in\mathfrak m$ but $u$ remains a unit. Then $c_4=-48u$ is a unit and $\Delta$ is not. The equation is minimal and reduction is multiplicative. Algebraically, two roots of the cubic have become congruent; geometrically, the special fiber has a node.

Finally consider

$$
E_a:y^2=x^3+\pi^2ux+\pi^3w
$$

with $4u^3+27w^2$ a unit. Its invariant valuations are

$$
v(c_4)=2,\qquad v(c_6)=3,\qquad v(\Delta)=6.
$$

It is minimal because $v(\Delta)<12$, and it has additive reduction. All three roots meet at the special fiber, producing a cusp. After a ramified quadratic extension the common fractional scale can be removed, as seen in Section 9.3.

These examples show that “bad reduction” has two independent aspects. The vanishing of $\Delta$ says that smoothness is lost. The unit or nonunit status of $c_4$ says whether the limiting cubic retains two tangent directions. The size of $v(\Delta)$ says how thick the degeneration is, not whether it is nodal or cuspidal by itself.

There is no contradiction in a minimal additive equation having $v(\Delta)=2$ or a minimal multiplicative equation having $v(\Delta)=100$. Minimality asks whether $12$ can be removed by an integral coordinate change; reduction type asks what the minimal special fiber looks like. These are related questions, but not the same question.

### 6.7 A characteristic-free splitness polynomial

The square test (6.3) is convenient in odd characteristic, but the tangent cone admits a formula that works without excluding characteristic $2$. Let the equation be minimal and multiplicative. Since $c_4$ is a unit, reduction of

$$
x_0=\frac{18b_6-b_2b_4}{c_4}
$$

defines an element of $k$. Direct substitution in the equation and its two partial derivatives shows that $x_0$ is the $x$-coordinate of the node. We do not need to divide by $2$ to find its other coordinate. Translate the node to the origin by writing $X=x-x_0$ and $Y=y-y_0$. The quadratic part is

$$
Y^2+\overline{a_1}XY-(3\overline{x_0}+\overline{a_2})X^2. \tag{6.4}
$$

A line $Y=TX$ is a tangent precisely when its slope is a root of this quadratic. Clearing the unit $\overline{c_4}$ gives the **splitness polynomial**

$$
Q(T)=\overline{c_4}T^2+
\overline{a_1c_4}T-
\overline{54b_6-3b_2b_4+a_2c_4}. \tag{6.5}
$$

**Proposition 6.2.** Multiplicative reduction is split if and only if $Q(T)$ is a product of two linear factors over $k$.

**Proof.** A nodal tangent cone has two distinct lines over a separable closure. Formula (6.4) identifies those lines with the roots of $Q$. The smooth locus of the cubic is split multiplicative exactly when both points above the node on the normalization are rational, and these two points are exactly the two tangent directions. Thus rational factorization of $Q$ is equivalent to splitness. $\square$

In odd characteristic the discriminant of the slope quadratic has the same square class as $-c_6$. Completing the square therefore recovers (6.3). In characteristic $2$, however, (6.4) has the form

$$
Y^2+\alpha XY+\beta X^2,\qquad \alpha\ne0,
$$

and division by $\alpha^2$ turns the slope equation into an Artin--Schreier equation $U^2+U=d$. Its solvability, not the square class of one coefficient, decides splitness. This is the exact reason for retaining (6.5).

## 7. Local points and the reduction filtration

### 7.1 Extending a point to a section

Let $R$ now be henselian, and fix a minimal Weierstrass model $\mathcal W$. Properness gives every point $P\in E(K)$ a unique extension to an $R$-section of $\mathcal W$. Its closed point can therefore be reduced to a point $\widetilde P\in\widetilde E(k)$, even when its affine coordinates are not integral: a point with a pole in $x$ approaches the section $O$ in projective coordinates.

If the special fiber is singular, reduction to the whole cubic is not a group homomorphism, because the singular point does not belong to a smooth algebraic group. The correct domain is the set of points reducing to the smooth locus. Define

$$
E_0(K)=\{P\in E(K):\widetilde P\in\widetilde E_{\mathrm{ns}}(k)\}, \tag{7.1}
$$

and

$$
E_1(K)=\{P\in E(K):\widetilde P=\widetilde O\}. \tag{7.2}
$$

The chord-and-tangent law extends on the smooth locus of the model, so $E_0(K)$ is a subgroup and reduction is a homomorphism there. Its kernel is $E_1(K)$.

**Theorem 7.1 (smooth reduction sequence).** If $R$ is henselian, reduction gives an exact sequence

$$
0\longrightarrow E_1(K)\longrightarrow E_0(K)
\longrightarrow\widetilde E_{\mathrm{ns}}(k)\longrightarrow0. \tag{7.3}
$$

**Proof strategy.** Only surjectivity is not immediate. A smooth residue point is a simple solution of local defining equations, so henselian lifting produces a section through it.

**Proof.** The kernel statement follows from the definitions. For a smooth affine residue point, at least one partial derivative of the Weierstrass equation is nonzero. Fixing one coordinate and applying the simple-root form of Hensel's lemma to the other lifts the point, after an integral linear change if necessary. The point $O$ already lifts. Each lift belongs to $E_0(K)$ and reduces to the prescribed point. $\square$

Consequently the first quotient in the local group filtration is geometric:

$$
E_0(K)/E_1(K)\cong
\begin{cases}
\widetilde E(k),&\text{good reduction},\\
T(k),&\text{multiplicative reduction},\\
k^+,&\text{additive reduction},
\end{cases} \tag{7.4}
$$

where $T$ is the split or nonsplit torus arising from the node.

### 7.2 The formal parameter at the origin

The subgroup $E_1(K)$ is local in the literal geometric sense: all its points lie in the formal neighborhood of $O$. On the affine chart $Y\ne0$, use

$$
z=-\frac{x}{y},\qquad w=-\frac1y.
$$

Then $x=z/w$ and $y=-1/w$, and the Weierstrass equation becomes

$$
w=z^3+a_1zw+a_2z^2w+a_3w^2+a_4zw^2+a_6w^3. \tag{7.5}
$$

The derivative of the right side with respect to $w$ at $(0,0)$ contributes no obstruction, while the left derivative is $1$. Formal substitution therefore determines a unique series $w(z)\in R[[z]]$ beginning with $z^3$. Substitution gives Laurent expansions

$$
x(z)=z^{-2}-a_1z^{-1}-a_2+\cdots,\qquad
y(z)=-z^{-3}+a_1z^{-2}+\cdots. \tag{7.6}
$$

Thus a point approaches $O$ exactly when $z$ has positive valuation. The parameter gives a bijection

$$
E_1(K)\longleftrightarrow\mathfrak m, \tag{7.7}
$$

as sets. Completeness makes this immediate by convergence of $w(z)$. Under henselianity alone, fix $z\in\mathfrak m$ in (7.5) and view the equation as a polynomial in $w$: at $w=0$ its value lies in $\mathfrak m$ and its derivative is a unit, so Hensel's lemma gives the unique $w\in\mathfrak m$ directly.

### 7.3 The formal group law

Expressing the sum of two points in the parameter $z$ produces a power series

$$
F(X,Y)\in R[[X,Y]]
$$

with

$$
F(X,Y)=X+Y-a_1XY+\text{terms of total degree at least }3. \tag{7.8}
$$

Associativity, commutativity, the zero law, and inversion follow from the elliptic-curve group law. This is the **formal group** of the Weierstrass equation. An integral admissible change replaces $z$ by a power series with unit linear coefficient, so the resulting filtered group is intrinsic.

For $n\geq1$, define

$$
E_n(K)=\{P\in E_1(K):v(z(P))\geq n\}. \tag{7.9}
$$

Because all nonlinear terms of $F$ have degree at least $2$,

$$
F(X,Y)\equiv X+Y\pmod{\mathfrak m^{n+1}}
$$

when $X,Y\in\mathfrak m^n$. Hence

$$
E_n(K)/E_{n+1}(K)
\cong\mathfrak m^n/\mathfrak m^{n+1}
\cong k^+. \tag{7.10}
$$

The formal filtration therefore repeats the additive residue field at every depth, just as the principal-unit filtration does. The first quotient $E_0/E_1$ detects the geometry of the special fiber; all deeper quotients see only its one-dimensional smooth tangent direction at $O$.

If $K$ has characteristic zero, the formal logarithm gives, sufficiently deep in the filtration, an isomorphism between the formal group and the additive group of $\mathfrak m^n$. Denominators in the logarithm prevent a uniform shallow statement, especially at $2$ and $3$. For the foundational exact sequences, the integral first-order congruence (7.10) is all that is needed.

The inverse and multiplication series carry additional information without requiring any division. There is a unique

$$
\iota(T)=-T-a_1T^2+\cdots\in R[[T]]
$$

such that $F(T,\iota(T))=0$. For every integer $m$, repeated formal addition defines

$$
[m](T)=mT+\text{terms of degree at least }2. \tag{7.11}
$$

If the residue characteristic does not divide $m$, the linear coefficient is a unit. Multiplication by $m$ is then étale at the identity, and the henselian inverse-function property gives, for every $Z\in\mathfrak m$, a unique $T\in\mathfrak m$ with $[m](T)=Z$. Thus multiplication by $m$ is an automorphism of $E_1(K)$. Over a complete ring the same solution can be seen by successive correction modulo powers of $\mathfrak m$. If the residue characteristic divides $m$, the linear term vanishes after reduction and the higher terms matter; this is the beginning of the much subtler small-prime behavior of torsion.

The formal differential is

$$
\frac{dT}{\partial F(T,Y)/\partial Y\vert_{Y=0}}.
$$

It has constant term $1$ and agrees with the invariant differential (2.13) after expressing $x,y$ as Laurent series in $T=z$. In characteristic zero, integrate it term by term to obtain

$$
\log_E(T)=T+\sum_{n\geq2}\ell_nT^n\in K[[T]].
$$

Invariance gives

$$
\log_E(F(X,Y))=\log_E(X)+\log_E(Y).
$$

The denominators of the $\ell_n$ may prevent convergence or integrality on all of $\mathfrak m$, but sufficiently deep arguments gain enough valuation from $T^n$ to compensate. This proves the earlier statement that the deep formal group is additively linear in characteristic zero.

There is no comparable characteristic-zero logarithm argument in equal positive characteristic: division by some $n$ is impossible. The integral formal law and its filtration remain valid, however. This separation between integral structure and logarithmic linearization mirrors the earlier separation between general and short Weierstrass equations.

### 7.4 Components and the missing quotient

Assume in this section that $R$ is excellent and henselian. Book 11 then supplies the unique minimal proper regular model $\mathcal X/R$. Properness extends each $P\in E(K)$ uniquely to a section. Such a section meets the smooth locus of $\mathcal X/R$: in the two-dimensional regular local ring at its closed point, the retraction to $R$ makes the base parameter part of a regular parameter system, so the fiber is regular along the section.

Let $\Gamma_0$ be the geometric component met by $O$. A section meets $\Gamma_0$ exactly when its image on the minimal cubic lies in the smooth locus: the resolution is an isomorphism over that locus, while the points of $\Gamma_0$ lying above the contracted singularity lie in the nonsmooth locus of the special fiber and cannot be met by a section. Thus this component condition is exactly membership in $E_0(K)$ as defined in (7.1).

Translation by $P$ on the generic curve extends to an automorphism of $\mathcal X$: apply the uniqueness of the minimal regular model to the generic automorphism and then to its inverse. It therefore permutes the geometric components. The components actually met by $K$-sections form a finite group

$$
\Phi_E^{\mathrm{sec}}=\{\tau_P(\Gamma_0):P\in E(K)\},
$$

with $\tau_P(\Gamma_0)+\tau_Q(\Gamma_0)=\tau_{P+Q}(\Gamma_0)$. This is well defined because two sections meet the same identity translate exactly when their difference lies in $E_0(K)$. Consequently reduction gives the exact sequence

$$
0\longrightarrow E_0(K)\longrightarrow E(K)
\longrightarrow\Phi_E^{\mathrm{sec}}\longrightarrow0. \tag{7.12}
$$

This formulation deliberately records only component classes represented by sections. Over an arbitrary residue field, a Galois-fixed geometric component need not contain a rational smooth point, so it must not automatically be identified with an element of (7.12). For the multiplicative polygons used below, rational representability over a finite field will be checked directly on the rational components.

For good reduction the smooth proper model already has connected special fiber, so $E(K)=E_0(K)$. The converse “trivial component group implies good reduction” is false: some additive fibers have trivial component group. Existence of a smooth proper model, not merely connectedness of a special fiber, is the intrinsic good-reduction criterion.

In split multiplicative reduction the resolved special fiber is a polygon of rational components. Its number of geometric components equals $v(\Delta_{\min})$; consequently the geometric component group is cyclic of that order. This numerical statement can be proved by successively blowing up the nodal total space. A full analytic description of the curve and of its points will be developed only when multiplicative uniformization is introduced.

The three layers may be summarized as

$$
E(K)\supset E_0(K)\supset E_1(K)\supset E_2(K)\supset\cdots.
$$

The outer quotient records components, the next quotient records the smooth special-fiber group, and the deeper quotients record infinitesimal additive directions.

### 7.5 Coordinate tests for the formal neighborhood

The Laurent expansions (7.6) translate the formal filtration into coordinate valuations. For $P\in E_1(K)$,

$$
v(x(P))=-2v(z(P)),\qquad
v(y(P))=-3v(z(P)), \tag{7.13}
$$

because the leading terms have strictly lower valuation than all later terms. Hence

$$
P\in E_n(K)
\quad\Longleftrightarrow\quad
v(x(P))\leq-2n
$$

for points in the formal neighborhood, with the equivalent condition on $y$. Negative affine coordinate valuations do not mean that the point fails to extend integrally to the projective model. They mean that the section approaches $O$.

Conversely, suppose an affine point on an integral equation has $v(x)<0$. Compare valuations in the equation. The least value on the right is normally $3v(x)$, while the left is controlled by $2v(y)$; the equality forces

$$
2v(y)=3v(x).
$$

Since the valuations are integers, $v(x)=-2n$ and $v(y)=-3n$ for some $n>0$, and $z=-x/y$ has valuation $n$. A careful unequal-value argument verifies that the lower-weight coefficient terms cannot interfere. Thus such a point lies in $E_n(K)$.

For example, on $y^2=x^3+Ax+B$ with $A,B\in R$, any point with $v(x)<0$ satisfies the displayed $2:3$ ratio. Set $x=\pi^{-2n}u$ and $y=\pi^{-3n}w$ with units $u,w$. Multiplying the equation by $\pi^{6n}$ gives

$$
w^2=u^3+\pi^{4n}Au+\pi^{6n}B,
$$

so $\overline w^{\,2}=\overline u^{\,3}$. The leading unit data describe the tangent direction at $O$, while $n$ records the depth in the formal group.

The filtration is separated:

$$
\bigcap_{n\geq1}E_n(K)=\{O\}.
$$

Indeed, a nonzero parameter has finite valuation. If $K$ is complete, the filtration is also complete: compatible points modulo every $E_n$ determine a unique point in $E_1(K)$, just as compatible residues modulo $\mathfrak m^n$ determine an element of $R$.

### 7.6 Topology and successive approximation

When $K$ is complete, the filtration $E_n(K)$ is a neighborhood basis of $O$ in the analytic topology on $E(K)$. Translation gives a neighborhood basis at every point. The reduction subgroup $E_1(K)$ is open, and so are $E_0(K)$ and every $E_n(K)$. If the residue field is finite, the quotients at each displayed level are finite; compactness of the valuation ring then makes $E(K)$ compact because $E$ is proper.

The formal law gives an explicit lifting procedure. Suppose a partial point is known through a parameter

$$
z_n\in\mathfrak m/\mathfrak m^n.
$$

Choosing one more residue digit lifts it to $z_{n+1}$ modulo $\mathfrak m^{n+1}$. Equation (7.5) uniquely determines $w$ to the same required precision, and hence determines the projective point. Addition of two such approximate points uses $F(z_1,z_2)$; modulo $\mathfrak m^{n+1}$ its new digit is the sum of the old digits plus correction terms already determined at lower precision.

This triangular structure is why the quotient (7.10) is additive even though the full group law is nonlinear. Nonlinearity affects carries into deeper layers, not the leading residue digit. For instance, if $X,Y\in\mathfrak m^n$, then

$$
F(X,Y)-(X+Y)\in\mathfrak m^{2n}\subseteq\mathfrak m^{n+1}.
$$

If $Y=-X$ in the first quotient, their sum lands at least one layer deeper. Repeated cancellation can be analyzed exactly as cancellation of leading terms in the valuation filtration.

The formal group also makes the role of henselianity precise. A compatible finite-order formal solution is algebraic at every stage; henselian lifting realizes it locally. Completeness is needed to identify an arbitrary infinite compatible sequence with a limit in $K$. Thus exact reduction modulo one power uses henselianity, while completeness controls the entire inverse-limit topology.

No choice of minimal equation affects this structure. An integral change sends $z$ to

$$
z'=\varepsilon z+O(z^2),\qquad \varepsilon\in R^\times,
$$

so it preserves $v(z)$ and every subgroup $E_n(K)$. The formal filtration is therefore an invariant of the elliptic curve over the valued field, not an artifact of coordinates.

## 8. Smooth models, semistability, and intrinsic criteria

### 8.1 Why resolve a minimal cubic

A minimal Weierstrass equation minimizes a weighted arithmetic invariant, but its total space need not be regular. Assume from now through Section 8.6 that $R$ is excellent. At a singular point of the special fiber, the resolution theorem of Book 11 separates tangent directions and reveals components hidden by the plane cubic. Contracting vertical exceptional curves then yields the unique relatively minimal proper regular model.

The minimal cubic and the minimal regular model answer different questions. The cubic is best for calculating $c_4,c_6,\Delta$ and deciding the coarse reduction type. The regular model is best for intersection theory and component groups. The resolution morphism back to the minimal Weierstrass model contracts the exceptional configuration that it created. Thus the two descriptions are complementary rather than competing.

**Theorem 8.1 (minimal regular model in genus one).** Let $R$ be an excellent DVR. The curve $E/K$ has a unique relatively minimal proper regular model $\mathcal X/R$. Every $K$-automorphism of $E$ extends uniquely to an automorphism of $\mathcal X$. In particular, translations by $K$-points act on the components of $\mathcal X_k$.

**Proof.** Existence, relative minimality, and uniqueness are the positive-genus minimal-model theorem of Book 11. For a generic automorphism $g:E\to E$, apply that theorem to $\mathcal X$ with generic identification changed by $g$. It gives a morphism $\widetilde g:\mathcal X\to\mathcal X$ inducing $g$. Applying the same construction to $g^{-1}$ and using uniqueness shows that the two extensions are inverse. $\square$

This is exactly the regular-model input needed for component calculations. We do not assert here the stronger extension property for maps from every smooth test scheme; that requires an additional smooth-model theorem. Removing only the singular point of a Weierstrass cubic is insufficient for components, because resolution creates further smooth points that the contracted cubic does not display.

### 8.2 Semistable reduction

An elliptic curve has **semistable reduction** over $K$ if its reduction is good or multiplicative. Geometrically, the special fiber is already smooth or has only an ordinary double point; cusps are excluded. In terms of a minimal equation,

$$
E\text{ is semistable}
\quad\Longleftrightarrow\quad
v(\Delta)=0\ \text{or}\ v(c_4)=0. \tag{8.1}
$$

This formula is deliberately a disjunction. In small residue characteristic a good fiber may have $\overline c_4=0$, for example when its $j$-invariant reduces to $0$. Thus “$c_4$ is a unit” characterizes multiplicative bad reduction, not all semistable reduction.

Semistability is exactly the condition that the minimal regular special fiber have only reduced normal crossings after passing to a strict henselian unramified base. For elliptic curves, good and multiplicative fibers are the two possible semistable shapes. Additive fibers acquire extra multiplicities or more complicated intersections upon resolution.

### 8.3 The valuation of $j$

From $j=c_4^3/\Delta$,

$$
v(j)=3v(c_4)-v(\Delta). \tag{8.2}
$$

For multiplicative reduction, $c_4$ is a unit, so

$$
v(j)=-\delta(E/K)<0. \tag{8.3}
$$

Thus a nonintegral $j$-invariant is an unmistakable sign of degeneration. It does not imply that reduction over $K$ is already multiplicative: additive examples with $v(j)<0$ exist.

The transformation laws give two unconditional potential-reduction obstructions. If $E$ acquires good reduction over a finite extension, then $v(j)\geq0$. If it acquires multiplicative reduction, then $v(j)<0$. Indeed, the extended valuation merely multiplies $v(j)$ by the ramification index, while good reduction has integral $j$ and multiplicative reduction satisfies (8.3).

The converses—integral $j$ gives potentially good reduction and nonintegral $j$ gives potentially multiplicative reduction—form the genus-one potential-reduction theorem. They require a separate stable-reduction or uniformization argument and are not used here. This exact boundary is important: equations prove the obstructions immediately, but they do not by themselves construct the finite extension or the resulting semistable model.

### 8.4 Néron-type criteria without representations

The preceding results give geometric tests independent of a choice among minimal coordinates.

**Theorem 8.2 (geometric reduction criteria).** Let $R$ be excellent and henselian, and use the minimal cubic together with its minimal regular resolution.

1. $E$ has good reduction if and only if the minimal cubic itself is a smooth proper genus-one model.
2. $E$ has multiplicative reduction if and only if the smooth locus of the contracted special cubic is a one-dimensional torus.
3. $E$ has additive reduction if and only if the smooth locus of the contracted special cubic is $\mathbf G_a$.
4. $E$ is semistable if and only if the contracted special cubic is smooth or nodal; equivalently, its smooth locus is an elliptic curve or a torus rather than an additive group.

**Proof.** The first assertion is Theorem 6.1. Normalization of a node removes two points from $\mathbf P^1$ and gives a torus, split according to the tangent directions. Normalization of a cusp removes one point and gives $\mathbf G_a$, as proved in Section 3.3. Resolution changes the visible component arrangement but not whether the contracted singularity has two tangent branches or one. The last assertion is therefore precisely the good-or-multiplicative definition of semistability. $\square$

This is the Néron-type content justified here: proper smooth genus-one, toric, and additive geometry are separated intrinsically. Criteria phrased through torsion modules or inertia require later theories and are intentionally not used.

### 8.5 Resolving a node and a cusp

Local equations clarify why nodes are semistable and cusps are not. Pass to the strict henselization so that a nodal tangent cone splits. The completed local ring at the node of a minimal multiplicative Weierstrass model has the form

$$
R^{\mathrm{sh}\,\wedge}[[U,V]]/(UV-\varepsilon\pi^n),
\qquad \varepsilon\in (R^{\mathrm{sh}\,\wedge})^\times. \tag{8.4}
$$

The unit can be absorbed into one parameter. The generic fiber is smooth. When $n=1$, the total space is regular and the special fiber has two local branches crossing transversely; globally those branches may belong to the same irreducible component. When $n>1$, the total space is singular at $U=V=\pi=0$. Blowing up the ideal $(U,\pi)$ has one regular chart and one unresolved chart $U_1V=\pi^{n-1}$, exactly as in the surface calculation of Book 11. Repetition inserts a chain of $n-1$ rational curves. Globally the two branches of the original cubic join its ends, producing a polygon with $n$ components, every one of multiplicity one.

The exponent $n$ is $v(\Delta_{\min})$. Indeed, a one-parameter deformation of an ordinary node is formally $UV-a$ up to units and changes of regular parameters; its discriminant divisor is $(a)$. Applying this to the minimal cubic gives $v(a)=v(\Delta_{\min})$. This agrees with the explicit two-root collision, where the square of the root difference is the smoothing parameter up to a unit. The component polygon retains all $n$ units of collision that the plane cubic compressed into one node.

A cusp has local shape resembling

$$
Y^2=X^3
$$

on the special fiber. It has only one tangent direction, so the first blowup does not produce a pair of transverse reduced branches. Further blowups can create components with multiplicities or configurations whose identity component contains an additive group. This failure of reduced normal crossing geometry is what additive reduction records.

These local pictures explain why the minimal discriminant and the coarse reduction type complement each other. The type says node or cusp; the exponent measures thickness. In the nodal case that pair determines the geometric polygon size. In the cuspidal case additional coefficient and ramification data are needed to determine the resolved configuration.

They also explain why a full list of fiber symbols is not needed for the present endpoint. Direct equation calculations of integrality, minimality, good or multiplicative reduction, and minimal discriminant use only the contracted cubic. The finer list refines additive reduction and component groups but does not change those foundational steps.

### 8.6 Multiplicative components and rational component classes

Write $n=\delta(E/K)>0$ and suppose that $E$ has multiplicative reduction. After strict henselization and resolution, the special fiber is conventionally called a fiber of type $I_n$. When $n=1$, it is one irreducible rational curve with a node, and the total surface is already regular there. For $n\geq2$, it is a cycle of $n$ smooth rational curves, with adjacent components meeting transversely in a polygon.

The assertion follows from the local equation $UV=\pi^n$. Blow up the closed singular point. On one chart the new equation has the same form with exponent $n-1$; the other chart records one exceptional rational component. Repeating reduces the exponent to $1$. The global two branches of the original cubic then join the ends of the chain, closing it into a cycle. No component has multiplicity greater than one. This calculation proves simultaneously that there are $n$ geometric components and that the reduction is semistable.

Choose the component meeting the identity section as $0$ and number successive components around the polygon. Over the strict henselization, every component contains a smooth residue point and hence is met by a section. The translation action of Theorem 8.1 therefore turns the component set into the geometric component group

$$
\Phi_E(\overline k)\cong\mathbf Z/n\mathbf Z. \tag{8.5}
$$

In split multiplicative reduction both orientations of the polygon are defined over $k$, so the residue action on (8.5) is trivial. In nonsplit multiplicative reduction the quadratic splitting automorphism reverses the polygon and acts by

$$
i\longmapsto-i. \tag{8.6}
$$

This gives more precise information than the statement that the identity component is a torus. If, in addition, $R$ is henselian and $k$ is finite, write $\Phi_E(k)$ for the fixed classes in $\Phi_E(\overline k)$. They are all represented by sections. In the split case, each rational component is a $\mathbf P^1$ with at most two rational nodes removed, so it has a rational smooth point, even over $\mathbf F_2$, and henselian lifting supplies a section. In the nonsplit case, the identity class is represented by $O$; when $n$ is even, the opposite class $n/2$ is also fixed, and its two boundary points are exchanged by the splitting involution, while the normalized blowup chart supplies a rational smooth point. Thus $\Phi_E(k)=\Phi_E^{\mathrm{sec}}$, reduction onto these classes is surjective, and the local component number

$$
c(E/K)=\#\Phi_E(k)
$$

satisfies

$$
c(E/K)=
\begin{cases}
n,&\text{split multiplicative},\\
1,&\text{nonsplit multiplicative and $n$ odd},\\
2,&\text{nonsplit multiplicative and $n$ even}.
\end{cases} \tag{8.7}
$$

The displayed values now follow because the fixed elements of inversion on $\mathbf Z/n\mathbf Z$ are the solutions of $2i=0$. This calculation also reveals a useful counterexample: the number of rational component classes does not determine the geometric number of components. A nonsplit $I_{101}$ fiber has $101$ geometric components but only the identity component class is rational.

Under a ramified extension of index $e$, multiplicative reduction remains multiplicative and its geometric polygon has $en$ components. Under an unramified quadratic extension, a nonsplit polygon becomes split but retains $n$ components. These are the component-theoretic versions of the valuation and tangent statements in Chapter 9.

### 8.7 The conductor statement justified by this geometry

There are several objects called a conductor. The one relevant to the present equation theory is the geometric local conductor count for a semistable genus-one curve. Let $m$ be the number of geometric irreducible components of the minimal regular special fiber and define

$$
f_{\mathrm{geom}}=\delta(E/K)+1-m. \tag{8.8}
$$

For the semistable fibers just analyzed, this is not an unexplained formula. In good reduction, the discriminant has no zero and the special fiber has one component, so $f_{\mathrm{geom}}=0$. In multiplicative reduction, resolving a node of thickness $n$ produces $m=n$ components while $\delta=n$, so

$$
f_{\mathrm{geom}}=
\begin{cases}
0,&\text{good reduction},\\
1,&\text{multiplicative reduction}.
\end{cases} \tag{8.9}
$$

The count measures loss of smoothness after subtracting the components created merely by resolving thickness. One node contributes one; a smooth fiber contributes none. Thus a semistable global elliptic curve has squarefree geometric conductor support: its bad primes occur to exponent one, regardless of the possibly large exponents in its minimal discriminant.

This conclusion is exactly the conductor information justified by the present geometry. The standard ramification-theoretic conductor is defined from an inertia action and includes a wild term. Identifying it with (8.8) is a comparison theorem, not a consequence of manipulating Weierstrass coefficients. If that comparison is supplied, (8.9) gives the standard semistable values $0$ and $1$; nothing in the direct Frey calculation below needs it. We therefore record the squarefree geometric count and do not pretend to compute wild additive exponents.

The contrast with the discriminant is worth emphasizing. At a multiplicative prime,

$$
f_{\mathrm{geom}}=1,\qquad \delta=-v(j)=n,
$$

and $n$ can be arbitrarily large. The conductor records the presence of a nodal defect; the discriminant records its thickness. Confusing them would erase precisely the divisibility information for which Frey curves are constructed.

### 8.8 What additive data remain invisible

For additive reduction, the pair $(v(c_4),\delta)$ gives only a cusp on the contracted cubic. Resolution can produce several different configurations with the same coarse data, and in residue characteristics $2$ and $3$ wild behavior can alter the conductor without changing the first tangent cone. It follows that none of the following is valid without further hypotheses:

$$
\text{additive type}\Longrightarrow
\text{a fixed component group},
$$

$$
v(\Delta)\Longrightarrow
\text{a fixed additive fiber configuration},
$$

or

$$
\delta+1-m\Longrightarrow
\text{the complete wild conductor calculation}.
$$

One can determine those data by repeatedly blowing up and tracking multiplicities, singular points, and residue extensions. That process is finite, but its branching is especially delicate at $2$ and $3$. Because the applications in this volume establish semistability directly, importing the full classification would obscure the shorter argument. The honest endpoint is stronger than a vague omission: good and multiplicative components are completely determined here, while additive component and wild-conductor assertions are made only when an explicit resolution supplies them.

## 9. Change of the ground DVR

### 9.1 How valuations rescale

Let $L/K$ be a finite extension equipped with an extension of the valuation, and let $S$ be the corresponding DVR. Write $e=e(L/K)$ for the ramification index, with both valuations normalized. For every $x\in K^\times$,

$$
v_L(x)=e\,v_K(x). \tag{9.1}
$$

Base-changing an integral equation from $R$ to $S$ therefore gives

$$
v_L(c_4)=e\,v_K(c_4),\quad
v_L(c_6)=e\,v_K(c_6),\quad
v_L(\Delta)=e\,v_K(\Delta). \tag{9.2}
$$

The base-changed equation need not be minimal. If an $S$-admissible change lowers its discriminant by $12m$, then

$$
\delta(E/L)=e\,\delta(E/K)-12m,\qquad m\geq0. \tag{9.3}
$$

This formula is the basic accounting law for extension. Ramification multiplies the old collision order; new coordinate changes can then remove weighted twelfth powers that were unavailable over $K$.

### 9.2 Unramified base change

Suppose $S/R$ is a finite unramified extension of DVRs; equivalently here, it is finite étale and local. Then $e=1$, a uniformizer of $R$ remains a uniformizer of $S$, and minimality is preserved.

**Proposition 9.1.** A minimal Weierstrass equation over $R$ remains minimal after unramified extension to $S$. In particular,

$$
\delta(E/L)=\delta(E/K),
$$

and good, multiplicative, or additive reduction remains of the same coarse type.

**Proof strategy.** Completion reduces the descent issue to a complete DVR, where an unramified extension has a finite unramified Galois closure. Essential uniqueness makes the minimal differential and pole lattices stable under that Galois action. Finite-étale descent brings their degree-six relation downstairs, and finite-precision approximation then returns it from the completion to $R$.

**Proof.** Suppose the equation became nonminimal over $S$. Complete. The completed finite étale algebra $S\otimes_R\widehat R$ is a product of finite unramified complete DVRs; choose a factor through which the improving change maps. A finite unramified Galois extension $T/\widehat R$ contains that factor. Choose a minimal equation over $T$.

Every Galois conjugate is again minimal. Theorem 5.2 says that any two conjugates differ by an integral admissible change with unit scaling. Consequently they have the same differential lattice

$$
T\omega_{\min}\subset\Omega(E/K)\otimes_K\operatorname{Frac}(T)
$$

and the same pole lattices $T+Tx$ and $T+Tx+Ty$: the formulas $x=u^2x'+r$ and $y=u^3y'+u^2sx'+t$ make this equality explicit. These three lattices are stable under the semilinear Galois action. Finite Galois descent, expressed by the equalizer

$$
\widehat R\longrightarrow T\rightrightarrows T\otimes_{\widehat R}T,
$$

descends them to free $\widehat R$-lattices. Multiplication among the descended pole lattices gives the unique degree-six relation; choosing bases adapted to $1$ puts it in integral Weierstrass form. Since the original equation was nonminimal after extension, the descended differential lattice is strictly smaller than $\widehat R\omega$, so the new discriminant valuation is lower by a positive multiple of $12$.

It remains only to return from $\widehat R$ to $R$. The isomorphism from the original equation to this improved completed equation has parameters $u,r,s,t\in\operatorname{Frac}(\widehat R)$. Integrality of the five expressions in (2.2) is a finite list of valuation inequalities, and $v(u)>0$ is fixed. Approximate the four parameters by elements of $K$ closely enough that all five inequalities and the value of $u$ are unchanged. Formula (2.2) then gives an integral equation over $R$, while (2.9) lowers its discriminant by the same positive multiple of $12$. This contradicts minimality over $R$. Hence the base-changed equation is minimal. Equation (9.2) with $e=1$ preserves the invariant valuations and the coarse type. $\square$

The residue geometry may nevertheless become more explicit. A nonsplit node can acquire its two tangent directions after an unramified quadratic extension, turning nonsplit multiplicative reduction into split multiplicative reduction. The special fiber remains nodal throughout.

### 9.3 Ramified base change

Ramified extension can change minimality and reduction type. Good reduction is stable under every extension: a unit discriminant remains a unit, so the base-changed equation stays minimal and smooth. Multiplicative reduction is also stable as a coarse type. Indeed, a minimal multiplicative equation has $c_4$ a unit; after extension it remains a unit, which proves minimality by (5.3), while $\Delta$ retains positive valuation. Thus

$$
\delta(E/L)=e\,\delta(E/K) \tag{9.4}
$$

for multiplicative reduction.

Additive reduction can change. For a concrete weighted example, assume $2,3$ are units and let

$$
E:y^2=x^3+\pi^2Ax+\pi^3B,\qquad A,B\in R^\times,
$$

with $4A^3+27B^2$ a unit. This equation is minimal and additive. After adjoining an element $\varpi$ with $\varpi^2=\pi$, one has

$$
\pi^2=\varpi^4,\qquad \pi^3=\varpi^6.
$$

Scaling by $x=\varpi^2x',y=\varpi^3y'$ gives

$$
y'^2=x'^3+Ax'+B,
$$

which has good reduction. Here (9.3) subtracts exactly $12$ from the extension-scaled discriminant valuation.

This example is the model for potential good reduction: a ramified extension makes fractional weights integral, after which a dilation removes them.

### 9.4 Descent and persistence

Good reduction descends through finite unramified extensions: Proposition 9.1 gives $\delta(E/L)=\delta(E/K)$, so vanishing upstairs is equivalent to vanishing downstairs. The same proposition shows that multiplicative versus additive type descends unramifiedly, though splitness may not.

Semistability persists under every finite extension. Good reduction stays good. Multiplicative reduction stays multiplicative because $c_4$ remains a unit. Thus once the only singularity is a node, further extension never turns it into a cusp.

The converse assertion that every elliptic curve becomes semistable after a suitable finite extension is a separate semistable-reduction theorem. It is not needed for the persistence statements just proved. If that theorem is supplied, the valuation of $j$ forces the eventual outcome: good when $j$ is integral and multiplicative when it is not. The present equation calculus neither assumes this existence result nor uses it in the Frey calculation.

### 9.5 Two base-change calculations

First let

$$
E:y^2=x^3+\pi x
$$

over a DVR of residue characteristic at least $5$. Here

$$
c_4=-48\pi,\qquad \Delta=-64\pi^3.
$$

The equation is minimal and additive. Let $L/K$ have ramification index $4$, with $\pi=u\varpi^4$ for a unit $u$. Scaling by $x=\varpi^2x',y=\varpi^3y'$ gives

$$
y'^2=x'^3+ux',
$$

whose discriminant is the unit $-64u^3$. Thus the curve has good reduction without any assumption that $u$ has a fourth root. This example exhibits potential good reduction with $j=1728$.

Second, let

$$
E:y^2=x^3+x^2+\pi^n
$$

and assume its displayed equation is minimal with $c_4$ a unit and $v(\Delta)>0$. It has multiplicative reduction. Under an extension of ramification index $e$, $c_4$ remains a unit, so no improvement is possible, and the new minimal discriminant exponent is exactly $e\,v(\Delta)$. The node becomes thicker rather than smoother. This contrasts sharply with the additive example.

Unramified extension produces a third kind of change. Suppose the first curve is already multiplicative but nonsplit. Its discriminant exponent remains fixed, while a quadratic residue extension can split the tangent cone. Nothing about minimality or collision thickness changes. Thus ramified base change acts on scale, whereas unramified base change acts primarily on residue geometry.

The three behaviors can be remembered as follows:

$$
\begin{array}{c|c|c}
\text{initial type}&\text{finite extension}&\text{possible outcome}\\ \hline
\text{good}&\text{any}&\text{good},\\
\text{multiplicative}&\text{any}&\text{multiplicative, possibly newly split},\\
\text{additive}&\text{ramified allowed}&\text{additive, good, or multiplicative}.
\end{array}
$$

Only the last row requires genuinely new minimal coordinates.

## 10. Residue characteristics two and three

### 10.1 Why short form is dangerous

Suppose $K$ has characteristic zero and residue characteristic $2$. Algebraically one can replace

$$
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6
$$

by completing the square. But the replacement uses

$$
y'=y+\frac{a_1x+a_3}{2}.
$$

If $a_1$ or $a_3$ is a unit, the new coefficients acquire denominators. The resulting short equation may still describe $E/K$, yet it is not an integral model and its visible special fiber has no arithmetic meaning over $R$.

At residue characteristic $3$, translating $x$ to remove $x^2$ uses division by $3$. The same problem occurs. General equations are therefore essential precisely at the small primes where local arithmetic is most delicate.

The invariant formulas (2.3)--(2.8), by contrast, are integral polynomial identities. They remain valid without dividing by $2$ or $3$. This is why a correct calculation begins with $a_i,b_i,c_4,c_6,\Delta$, not with an unjustified short form.

### 10.2 Testing an improvement by congruences

To test for an improvement of one valuation step, search for an admissible change with $u=\pi$. Equations (2.2) require

$$
\begin{aligned}
a_1+2s&\equiv0\pmod\pi,\\
a_2-sa_1+3r-s^2&\equiv0\pmod{\pi^2},\\
a_3+ra_1+2t&\equiv0\pmod{\pi^3},\\
a_4-sa_3+2ra_2-(t+rs)a_1+3r^2-2st&\equiv0\pmod{\pi^4},\\
a_6+ra_4+r^2a_2+r^3-ta_3-rta_1-t^2&\equiv0\pmod{\pi^6}.
\end{aligned} \tag{10.1}
$$

This finite congruence system is an exact criterion for an improvement with $v(u)=1$. A general nonminimality search must also allow $v(u)>1$, although after each successful integral improvement one naturally repeats the one-step test. The system displays where small characteristic intervenes. When $2$ is a unit, the first and third congruences solve freely for $s,t$; when $3$ is a unit, the second gives control of $r$. At $2$ or $3$, those variables are constrained by residue equations rather than solved by division.

The search can be organized geometrically. Reduction of a nonminimal equation must have $c_4=c_6=\Delta=0$ and hence a cusp. Translate its singular point to $(0,0)$, choose $s$ to align the repeated tangent, and then test the higher divisibilities in (10.1). If they hold, scale by $\pi$ and repeat. If they fail, the cusp is genuine and the equation is minimal.

This is the conceptual core of a full reduction algorithm: locate the singularity, normalize its tangent cone, test weighted divisibility, and either improve or identify the resolved fiber configuration. We need only the minimality and coarse-type portions here.

### 10.3 A two-adic integral improvement

Let $R$ be a DVR with uniformizer $2$, and consider

$$
y^2=x^3+(B-A)x^2-ABx, \tag{10.2}
$$

where $A,B\in R$, $v(A)\geq4$, $B$ is a unit, and

$$
B-A\equiv1\pmod4.
$$

The change

$$
x=4x',\qquad y=8y'+4x' \tag{10.3}
$$

has $u=2,s=1,r=t=0$. Formula (2.2) gives the integral equation

$$
y'^2+x'y'=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x'. \tag{10.4}
$$

Its discriminant is the old discriminant divided by $2^{12}$, while its $c_4$ is the old $c_4$ divided by $2^4$. A short-form glance at (10.2) would not suggest the $xy$ term in (10.4), yet that term is exactly what permits an integral improvement at $2$.

This calculation is not a universal two-adic recipe: if the congruence on $B-A$ changes, a different translation or a different ordering of the roots may be needed. It is a model of the correct method—use the general coordinate formulas and verify every divisibility.

### 10.4 Small-characteristic counterexamples to shortcuts

The implications

$$
v(c_4)\geq4,\quad v(c_6)\geq6,\quad v(\Delta)\geq12
$$

are necessary for nonminimality, not sufficient. They record only invariant divisibility. Improvement additionally requires the coordinate congruences (10.1). In small residue characteristic, invariant cancellations can occur even when no integral singular point and tangent choice lift with the needed precision.

Likewise, $v(j)\geq0$ does not mean good reduction over $K$; it is only a necessary condition for potentially good reduction at the level proved here. A ramified twist of a good curve supplies a counterexample to good reduction over the original field. Finally, a singular reduction of an arbitrary integral equation does not mean bad reduction: a nonminimal dilation of a good equation supplies the simplest counterexample.

These warnings all have the same source. Invariants describe the generic curve together with a weighted differential, while reduction depends on a maximal integral choice of that differential. At $2$ and $3$, the passage between convenient algebraic normal forms and integral choices is especially nontrivial.

### 10.5 A three-adic hidden dilation

Let $R$ have uniformizer $3$. Begin with the good equation

$$
E':y'^2=x'^3+x'^2+1. \tag{10.5}
$$

Its discriminant is $-496$, a $3$-adic unit. Apply

$$
x=9x'+1,\qquad y=27y'.
$$

After expansion, the same curve has the integral equation

$$
E:y^2=x^3+6x^2-15x+737. \tag{10.6}
$$

None of the visible coefficients suggests the simple pattern $3^i\mid a_i$. Nevertheless, translating $x$ by $1$ exposes

$$
x^3+6x^2-15x+737
=729\left(x'^3+x'^2+1\right).
$$

The discriminant of (10.6) has valuation $12$, and the displayed equation is nonminimal. Its special fiber is

$$
y^2=(x-1)^3
$$

in characteristic $3$, a cusp centered at $x=1$. The coefficient $3r$ in the transformation of $a_2$ is exactly what hides the dilation before translation.

This example makes two points. First, the quick implication $v(\Delta)\geq12$ does not itself produce the improvement; the singular center does. Second, depressing the original cubic by dividing its quadratic coefficient by $3$ is the wrong integral operation. One should instead translate to the singular residue point and use the general weighted formulas.

At residue characteristic $2$, the corresponding hidden data live especially in $a_1$ and $a_3$; at residue characteristic $3$, they live especially in $a_2$. The general equation keeps precisely the coefficients needed to see these phenomena integrally.

### 10.6 Exact coarse criteria in characteristics two and three

Although minimization is delicate at the small primes, classification of the special fiber is simple once minimality has been proved. Reduction of the universal invariant formulas gives the exact identities

$$
\operatorname{char}k=2:\qquad
\overline{c_4}=\overline{a_1}^{\,4},\qquad
\overline{c_6}=\overline{a_1}^{\,6}, \tag{10.7}
$$

and

$$
\operatorname{char}k=3:\qquad
\overline{c_4}=\overline{b_2}^{\,2},\qquad
\overline{c_6}=-\overline{b_2}^{\,3}. \tag{10.8}
$$

Consequently a minimal equation satisfies the following tables.

$$
\begin{array}{c|c|c|c}
\operatorname{char}k&\overline\Delta&\text{additional condition}&\text{reduction}\\ \hline
2&\ne0&&\text{good}\\
2&=0&\overline{a_1}\ne0&\text{multiplicative}\\
2&=0&\overline{a_1}=0&\text{additive}\\
3&\ne0&&\text{good}\\
3&=0&\overline{b_2}\ne0&\text{multiplicative}\\
3&=0&\overline{b_2}=0&\text{additive}.
\end{array} \tag{10.9}
$$

**Proof strategy.** The discriminant criterion decides smooth versus singular. For a singular cubic, $c_4\ne0$ decides node versus cusp. Identities (10.7) and (10.8) merely express that condition in coefficients that remain meaningful in the indicated characteristic.

**Proof.** In characteristic $2$, the numerical multiples in $b_2=a_1^2+4a_2$ and $c_4=b_2^2-24b_4$ vanish, leaving $c_4=a_1^4$. In characteristic $3$, $c_4=b_2^2-24b_4=b_2^2$. Apply the trichotomy (6.1). $\square$

These are classification criteria, not minimality criteria. A nonminimal dilation of a good equation can reduce to a cusp with $a_1=0$ or $b_2=0$. The logical order remains: first prove minimality, then apply (10.9).

For minimization itself, (10.1) has an exact but deliberately limited scope: it is necessary and sufficient for a chosen quadruple $(u,r,s,t)$ with $u=\pi$ to produce an integral equation whose discriminant is smaller by $12$. It does not claim that the three invariant inequalities alone are sufficient, nor does it classify the additive configuration when the congruences fail. This is enough for a direct argument whenever one exhibits the change, as in Sections 10.3 and 12.6, or certifies minimality by one of (5.3).

Finally, the word “dyadic” does not mean that $2$ is always a uniformizer. In a mixed-characteristic DVR one has

$$
2=\varepsilon\pi^{e_2},\qquad \varepsilon\in R^\times,
$$

and the explicit change (10.3) assumes $e_2=1$ and chooses the uniformizer $2$. For $e_2>1$, its denominators and congruences must be measured with $v(2)=e_2$. The invariant identities and the criterion (10.1) remain valid, but the numerical exponent $-8$ in the Frey calculation is specific to the unramified dyadic base.

## 11. Worked local calculations

### 11.1 The Legendre family

Assume first that $2$ is a unit and let $\lambda\in K\setminus\{0,1\}$. The Legendre equation

$$
E_\lambda:y^2=x(x-1)(x-\lambda) \tag{11.1}
$$

displays all three nonzero points of order two. In general Weierstrass form,

$$
a_1=a_3=a_6=0,\qquad a_2=-(1+\lambda),\qquad a_4=\lambda.
$$

Substitution in the invariant formulas gives

$$
\begin{aligned}
c_4&=16(\lambda^2-\lambda+1),\\
c_6&=32(\lambda+1)(\lambda-2)(2\lambda-1),\\
\Delta&=16\lambda^2(1-\lambda)^2,\\
j&=256\frac{(\lambda^2-\lambda+1)^3}{\lambda^2(1-\lambda)^2}.
\end{aligned} \tag{11.2}
$$

The discriminant is the square of the product of pairwise root differences, multiplied by $16$. It vanishes at $\lambda=0,1,\infty$, exactly when two branch points collide. The six transformations

$$
\lambda,\quad1-\lambda,\quad\lambda^{-1},\quad(1-\lambda)^{-1},
\quad\frac{\lambda}{\lambda-1},\quad\frac{\lambda-1}{\lambda}
$$

permute the three finite branch points and give geometrically isomorphic curves. This symmetry is useful for putting a local parameter into an integral range.

Suppose $v(\lambda)=n>0$ and the residue characteristic is odd. Then $1-\lambda$ is a unit and

$$
v(c_4)=0,\qquad v(\Delta)=2n.
$$

The displayed equation is minimal by the $c_4$ test and has multiplicative reduction. Its reduced cubic is

$$
y^2=x^2(x-1).
$$

At the node $(0,0)$ the tangent cone is $y^2+x^2$. Thus the reduction is split precisely when $-1$ is a square in $k$. Formula (6.3) agrees: at $\lambda=0$, $-c_6=-64$, whose square class is that of $-1$.

If $\lambda$ and $1-\lambda$ are both units, then $\Delta$ is a unit and the curve has good reduction. If $v(1-\lambda)>0$, the same argument after exchanging $0$ and $1$ gives multiplicative reduction with exponent $2v(1-\lambda)$. These calculations make the geometric slogan exact: one pair of branch points colliding gives a node, while three distinct residue branch points give a smooth fiber.

### 11.2 Root differences and full rational two-torsion

More generally, assume $2$ is a unit and write

$$
E:y^2=(x-e_1)(x-e_2)(x-e_3),\qquad e_i\in K. \tag{11.3}
$$

Then

$$
\Delta=16\prod_{i<j}(e_i-e_j)^2. \tag{11.4}
$$

This formula follows either from the polynomial discriminant or by translating one root to zero and using (2.7). It is a powerful first estimate, but not automatically a minimal discriminant formula. A common translation of the $e_i$ does nothing to their differences, while a common scaling $e_i=\pi^{2m}e_i'$ contributes $\pi^{12m}$ and may reveal nonminimality.

Suppose $e_i\in R$, and exactly two roots coincide modulo $\pi$ while the third remains distinct. After translating the double root to $0$, the reduction has form

$$
y^2=x^2(x-u),\qquad \overline u\ne0,
$$

which is nodal. The corresponding $c_4$ is a unit, so the equation is minimal and reduction is multiplicative. The minimal discriminant exponent is twice the valuation of the difference of the colliding roots, provided the other differences remain units.

If all three roots coincide modulo $\pi$, the reduced cubic is cuspidal, but the equation may or may not be minimal. Translate their common residue to $0$. If all roots are divisible by $\pi^2$, the scaling $x=\pi^2x',y=\pi^3y'$ lowers the discriminant by $12$. If their pairwise differences are divisible only by $\pi$, such a scaling need not be integral. The cluster picture suggests the correct transformations, while the weighted coefficient test decides them.

### 11.3 Cancellation and unequal valuations

Invariant calculations frequently reduce to sums whose valuations must be determined. The nonarchimedean rule is exact when the least valuation occurs once. For

$$
E:y^2=x^3+Ax+B,
$$

if $3v(A)\ne2v(B)$ and the residue characteristic is at least $5$, then

$$
v(\Delta)=\min\{3v(A),2v(B)\}, \tag{11.5}
$$

because $4$ and $27$ are units and the two summands in $4A^3+27B^2$ have unequal values. If $3v(A)=2v(B)$, cancellation may increase the discriminant valuation. One must reduce the leading unit combination.

Take $A=-3$ and $B=2+\pi^n$ over a DVR where $6$ is a unit. Then

$$
4A^3+27B^2=-108+27(4+4\pi^n+\pi^{2n})
=108\pi^n+27\pi^{2n}.
$$

For a residue characteristic not dividing $108$, this has valuation $n$. The coefficients are units, yet the discriminant can have arbitrarily large positive valuation because the limiting cubic $x^3-3x+2=(x-1)^2(x+2)$ has a double root. High discriminant valuation can measure extremely close roots rather than large coefficients.

The equation is still minimal, since $c_4=144$ is a unit. It has multiplicative reduction for every $n>0$, with minimal discriminant exponent $n$. This is a useful counterexample to the intuition that a large minimal discriminant exponent must come from visibly divisible coefficients.

### 11.4 A splitness calculation from the tangent cone

Let the residue characteristic be odd and consider a minimal equation whose reduction, after translating its node, is

$$
y^2=x^2(x+u),\qquad u\in k^\times.
$$

The tangent cone factors over an algebraic closure as

$$
(y-\sqrt u\,x)(y+\sqrt u\,x).
$$

Its two lines are $k$-rational exactly when $u$ is a square. If $u$ is not a square, the lines are defined over $k(\sqrt u)$ and exchanged by its nontrivial automorphism. The normalization removes the node and deletes these two conjugate points. The resulting smooth locus is the norm-one form of a multiplicative group rather than the split multiplicative group.

This computation also explains why splitness is residue-field data. Ramified extension may rescale the collision order, but an unramified residue extension is what makes the tangent directions rational. It is therefore natural that nonsplit multiplicative reduction becomes split over an unramified quadratic extension when the residue field is finite.

### 11.5 What the coarse data do and do not determine

The pair

$$
\bigl(v(c_4),v(\Delta_{\min})\bigr)
$$

determines good, multiplicative, or additive reduction. In the multiplicative case it also gives $v(\Delta_{\min})=-v(j)$ and, after geometric resolution, the number of polygonal components. It does not determine splitness; that requires a square class or tangent-cone calculation.

In additive reduction the pair does not determine the entire resolved fiber, the component group, or the effect of wild ramification. Likewise, the minimal discriminant exponent is not a conductor exponent. Even in multiplicative reduction, the plane cubic has a single nodal defect while the discriminant exponent can be any positive integer. A systematic definition and computation of conductors requires ramification actions and lies beyond the present geometric development. The distinction already visible here prevents the two local invariants from being conflated.

### 11.6 Quadratic twists as a reduction experiment

Assume the residue characteristic is at least $5$ and let

$$
E:y^2=x^3+Ax+B
$$

be minimal. For $d\in K^\times$, a quadratic twist has equation

$$
E^{(d)}:y^2=x^3+d^2Ax+d^3B. \tag{11.6}
$$

Its invariants are

$$
c_4(E^{(d)})=d^2c_4(E),\quad
c_6(E^{(d)})=d^3c_6(E),\quad
\Delta(E^{(d)})=d^6\Delta(E), \tag{11.7}
$$

while $j$ is unchanged. Multiplying $d$ by a square produces an isomorphic twist, so locally only the square class of $d$ matters.

Suppose $E$ has good reduction and $d=\pi$. If $A$ and $B$ are units and the original discriminant is a unit, the twisted equation has

$$
v(c_4)=2,\qquad v(c_6)=3,\qquad v(\Delta)=6.
$$

It is minimal by $v(\Delta)<12$ and has additive reduction. After adjoining $\sqrt\pi$, the twist becomes isomorphic to $E$ and therefore acquires good reduction. This is the simplest example of additive but potentially good reduction.

If $d$ is a nonsquare unit, all three invariant valuations remain unchanged. Good, multiplicative, or additive type is preserved, but splitness can change. In multiplicative reduction, the value of $-c_6$ is multiplied by the cube of $d$, which has the same square class as $d$. A nonsquare unit twist therefore interchanges split and nonsplit multiplicative reduction in odd residue characteristic.

If $E$ already has additive reduction, the displayed twist equation may fail to be minimal after the six-step change in discriminant. For example, twisting twice by $\pi$ multiplies coefficients by $\pi^4$ and $\pi^6$, after which a weighted scaling returns to the original square class. This illustrates again that raw invariant changes must be followed by minimization.

Twists separate three kinds of information particularly clearly. The $j$-invariant retains the geometric curve over an algebraic closure. The twist class records descent to $K$. The minimal discriminant and tangent cone record how that descent meets the valuation ring.

### 11.7 A dyadic tangent-cone calculation

Return to the integral improvement (10.4), assume $v(2)=1$, and strengthen $v(A)\geq4$ to $v(A)\geq5$. Put

$$
D=\frac{B-A-1}{4}.
$$

Because $a_1'=1$ and $a_4'=-AB/16$ has positive valuation, reduction gives

$$
y^2+xy=x^3+\overline D x^2. \tag{11.8}
$$

The partial derivatives in characteristic $2$ show that the unique singular point is $(0,0)$. Its tangent cone is

$$
y^2+xy+\overline D x^2. \tag{11.9}
$$

Putting $y=Tx$ shows that the two tangent directions are defined over $k$ exactly when

$$
T^2+T+\overline D
$$

has a root in $k$. This is the dyadic form of the characteristic-free criterion (6.5). It is separable because its derivative is $1$, so a root automatically gives two distinct tangent lines.

If $k$ is finite of characteristic $2$, the image of $T\mapsto T^2+T$ is the kernel of the absolute trace to $\mathbf F_2$. Hence

$$
\text{split multiplicative}\quad\Longleftrightarrow\quad
\operatorname{Tr}_{k/\mathbf F_2}(\overline D)=0. \tag{11.10}
$$

For $K=\mathbf Q_2$, the residue field is $\mathbf F_2$ and this says simply that $D$ is even. Since $v(A)\geq5$, the congruence becomes

$$
B\equiv1\pmod8. \tag{11.11}
$$

Thus the normalization $B-A\equiv1\pmod4$ suffices for integrality and minimality, but one further binary digit decides splitness. This is a clean example of three logically different precisions: divisibility through $2^4$ permits the coordinate change, positivity of the new discriminant detects a node, and a congruence modulo $8$ chooses between its two rationality forms.

## 12. A Frey-type local laboratory

### 12.1 The equation and its visible torsion

Let $A,B\in K^\times$ and put

$$
C=A+B\ne0.
$$

Consider the Frey-type equation

$$
E_{A,B}:y^2=x(x-A)(x+B). \tag{12.1}
$$

Its three nonzero two-torsion points are visible at $x=0,A,-B$. The equation is suited to local analysis because every invariant factors in terms of the three quantities $A,B,C$, which are also the pairwise root differences up to sign.

Expanding gives

$$
y^2=x^3+(B-A)x^2-ABx,
$$

so

$$
a_1=a_3=a_6=0,\qquad a_2=B-A,\qquad a_4=-AB. \tag{12.2}
$$

It is integral whenever $A,B\in R$.

### 12.2 Complete invariant calculation

From (2.3),

$$
\begin{aligned}
b_2&=4(B-A),\\
b_4&=-2AB,\\
b_6&=0,\\
b_8&=-A^2B^2.
\end{aligned} \tag{12.3}
$$

Therefore

$$
c_4=16(A^2+AB+B^2), \tag{12.4}
$$

and

$$
c_6=-32(B-A)(2A^2+5AB+2B^2). \tag{12.5}
$$

For the discriminant,

$$
\begin{aligned}
\Delta
&=-b_2^2b_8-8b_4^3\\
&=16A^2B^2(B-A)^2+64A^3B^3\\
&=16A^2B^2(A+B)^2.
\end{aligned} \tag{12.6}
$$

The factorization in the last line is the root-difference formula. It is the central reason for choosing (12.1): local discriminant calculations become valuation bookkeeping on $A$, $B$, and $C$.

The $j$-invariant is

$$
j=256\frac{(A^2+AB+B^2)^3}{A^2B^2C^2}. \tag{12.7}
$$

All these identities are polynomial identities over the integers. They remain valid at $2$ and $3$, although their valuation consequences change because the numerical factors are no longer units.

### 12.3 Odd primes dividing one factor

Let the residue characteristic be odd. Suppose exactly one of $A,B,C$ has positive valuation. If $v(A)=m>0$, then $B$ and $C$ are units and

$$
A^2+AB+B^2\equiv B^2\not\equiv0\pmod{\mathfrak m}.
$$

Thus $c_4$ is a unit, the equation is minimal, and

$$
\delta(E_{A,B}/K)=v(\Delta)=2m. \tag{12.8}
$$

The reduction is multiplicative. The same argument gives

$$
\delta(E_{A,B}/K)=
\begin{cases}
2v(A),&v(A)>0,\ B,C\in R^\times,\\
2v(B),&v(B)>0,\ A,C\in R^\times,\\
2v(C),&v(C)>0,\ A,B\in R^\times.
\end{cases} \tag{12.9}
$$

At a prime not dividing $2ABC$, the discriminant is a unit, so reduction is good. Hence, under pairwise-coprimality hypotheses, all odd bad primes are immediately seen to be multiplicative.

The proof has four logically separate steps: integrality comes from $A,B\in R$; the formula for $c_4$ proves minimality; the discriminant factorization gives the exact exponent; and the pair $(v(c_4),v(\Delta))=(0,>0)$ gives multiplicative reduction. Keeping these steps separate makes the calculation robust.

### 12.4 Splitness at the odd bad primes

The reduced equations also determine splitness.

If $v(A)>0$, reduction gives

$$
y^2=x^2(x+B),
$$

whose tangent cone at $(0,0)$ is $y^2-Bx^2$. The reduction is split if and only if $\overline B$ is a square.

If $v(B)>0$, reduction gives $y^2=x^2(x-A)$, with tangent cone $y^2+Ax^2$. It is split if and only if $-\overline A$ is a square.

If $v(C)>0$, then $B\equiv-A$. The double root is $x=A$, and after writing $X=x-A$ the tangent cone is $y^2-AX^2$. It is split if and only if $\overline A$ is a square.

These tests agree with $-c_6$. Reducing (12.5) in the three cases gives square classes represented respectively by $B$, $-A$, and $A$. Thus both the geometric tangent calculation and the invariant test lead to the same answer.

### 12.5 Common factors and weighted normalization

If $A$ and $B$ share a common factor, then $C$ shares it as well. Write

$$
A=\pi^{2r}A',\qquad B=\pi^{2r}B'
$$

when a common even valuation $2r$ can be extracted. The coordinate change

$$
x=\pi^{2r}x',\qquad y=\pi^{3r}y'
$$

turns (12.1) into

$$
y'^2=x'(x'-A')(x'+B').
$$

The discriminant drops by $12r$, exactly matching (12.6). If the common valuation is odd, a single scaling over $K$ cannot remove all of it while respecting the weights; a ramified quadratic extension may make the half-integral scaling available.

This is why primitive hypotheses matter in global applications. They are not merely a convenience for factorization: they ensure that, at each odd prime, at most one root difference vanishes and hence that the visible integral equation is already minimal and nodal.

### 12.6 The prime above two

At residue characteristic $2$, the factors $16$ and $32$ in (12.4)--(12.6) prevent the odd-prime argument. For the following explicit normalization, assume that $2$ itself is a uniformizer. Suppose, after possibly interchanging the roles of the roots, that

$$
v(A)\geq4,\qquad B,C\in R^\times,\qquad B-A\equiv1\pmod4.
$$

Apply the change from (10.3). The resulting integral equation is

$$
y'^2+x'y'=x'^3+\frac{B-A-1}{4}x'^2-\frac{AB}{16}x'. \tag{12.10}
$$

Its invariants satisfy

$$
c_4'=A^2+AB+B^2,\qquad
\Delta'=2^{-8}A^2B^2C^2. \tag{12.11}
$$

Since $A$ is even and $B$ is a unit, $c_4'$ is a unit. Thus (12.10) is minimal. If $v(A)>4$, it has multiplicative reduction and

$$
\delta(E_{A,B}/K)=2v(A)-8. \tag{12.12}
$$

If $v(A)=4$, the displayed discriminant is a unit and the reduction is good. Splitness must be read from the characteristic-$2$ tangent cone of (12.10), not from an odd-characteristic square shortcut.

For the common specialization $A=a^n$ with $n\geq5$ and $a$ even, one has $v(A)=n\,v(a)\geq5$, so the outcome under the stated congruence normalization is multiplicative with exponent

$$
2n\,v(a)-8.
$$

Other parity and congruence patterns require a different permutation of the three roots or a different integral change. No single formula should be asserted until the corresponding version of (10.1) has been checked. This is exactly where careless use of short equations most often corrupts a local argument.

### 12.7 The exponentiated three-term specialization

Let $a,b,c$ lie in a domain with

$$
a^n+b^n=c^n,
$$

and set $A=a^n$, $B=b^n$, $C=c^n$. Without drawing any global conclusion from this relation, the local equation calculus gives

$$
\Delta=16(abc)^{2n}. \tag{12.13}
$$

Assume the triple is primitive at an odd prime $\mathfrak p$. If $\mathfrak p$ divides none of $abc$, the curve has good reduction there. If it divides exactly one, say $a$, then

$$
v_{\mathfrak p}(c_4)=0,\qquad
\delta_{\mathfrak p}=2n\,v_{\mathfrak p}(a),
$$

and the reduction is multiplicative. The analogous statements hold for $b$ and $c$. Thus every odd bad prime has a minimal discriminant exponent divisible by $2n$, and the curve is semistable at every odd prime.

At primes above $2$, one first normalizes the parity of the triple and then performs an explicit general Weierstrass change such as (12.10). Under the hypotheses of Section 12.6, the exponent is $2n\,v(a)-8$ rather than the naive $4+2n\,v(a)$. The difference is $12$, the signature of one genuine minimality improvement.

For a concrete symbolic table, suppose $n\geq5$, the odd-prime valuations of $a,b,c$ are pairwise disjoint, $a$ is even, and the two-adic normalization of Section 12.6 applies. Then the local outcomes are

$$
\begin{array}{c|c|c|c}
\text{place}&\text{hypothesis}&\delta&\text{reduction}\\ \hline
\mathfrak p\nmid2abc& &0&\text{good}\\
\mathfrak p\mid a,\ \mathfrak p\nmid2bc
&\operatorname{char}k_{\mathfrak p}\ne2
&2n\,v_{\mathfrak p}(a)&\text{multiplicative}\\
\mathfrak p\mid b,\ \mathfrak p\nmid2ac
&\operatorname{char}k_{\mathfrak p}\ne2
&2n\,v_{\mathfrak p}(b)&\text{multiplicative}\\
\mathfrak p\mid c,\ \mathfrak p\nmid2ab
&\operatorname{char}k_{\mathfrak p}\ne2
&2n\,v_{\mathfrak p}(c)&\text{multiplicative}\\
\mathfrak p\mid2
&v_{\mathfrak p}(2)=1\text{ and Section 12.6 applies}
&2n\,v_{\mathfrak p}(a)-8&\text{multiplicative}.
\end{array} \tag{12.14}
$$

Every exponent in the odd rows comes directly from one squared root difference. The two-adic row begins with the same root-difference discriminant but subtracts $12$ after the integral $xy$-coordinate change. This is a compact record of the entire argument, not a substitute for it: each row rests on a separate integrality and minimality proof.

For example, take $n=5$ and an odd prime $q$ with $v_q(a)=2$ and $q\nmid bc$. Then $v_q(A)=10$, $c_4$ is a unit, and

$$
\delta_q=20.
$$

The fact that $20\geq12$ does not permit a decrease to $8$: the unit $c_4$ proves the equation minimal. This numerical instance is a useful final warning against reducing discriminant exponents modulo $12$ without an admissible change.

This symbolic analysis reaches the intended local endpoint. Starting only from the equation, it determines where the model is integral, proves minimality, computes the exact minimal discriminant, classifies reduction, and tests splitness. It does not use a uniformization, a torsion representation, or a conductor calculation, and it makes no claim about a global Diophantine contradiction.

### 12.8 The primitive integral Frey curve

The preceding symbolic calculation now yields a single concrete theorem over the integers. Let $p\geq5$ be odd and suppose that nonzero pairwise coprime integers $a,b,c$ satisfy

$$
a^p+b^p=c^p. \tag{12.15}
$$

Exactly one of $a,b,c$ is even: reducing $a^p+b^p-c^p=0$ modulo $2$ forces an even number of odd entries, and primitivity rules out zero odd entries. Signed permutation of the three terms preserves an equation of the form (12.15). For example, if $c$ is even, replace $(a,b,c)$ by $(-c,a,-b)$. We may therefore arrange that $a$ is even. Because $p$ is odd, simultaneously replacing $(a,b,c)$ by $(-a,-b,-c)$ also preserves (12.15); make this replacement if necessary so that

$$
b\equiv1\pmod4. \tag{12.16}
$$

Set $A=a^p$ and $B=b^p$. Then $v_2(A)\geq p\geq5$ and $B-A\equiv1\pmod4$. Applying (10.3) globally gives the integral equation

$$
\mathcal F_{a,b}:
y^2+xy=x^3+
\frac{b^p-a^p-1}{4}x^2-
\frac{a^pb^p}{16}x. \tag{12.17}
$$

Its discriminant and fourth invariant are

$$
\Delta(\mathcal F_{a,b})
=2^{-8}(abc)^{2p},\qquad
c_4(\mathcal F_{a,b})
=a^{2p}+a^pb^p+b^{2p}. \tag{12.18}
$$

The first expression is an integer because $a^p$ contains at least $2^5$. The sign is fixed by our convention; no unspecified unit is hidden in (12.18).

**Theorem 12.1 (minimal discriminant and reduction of the primitive Frey curve).** The equation (12.17) is minimal at every prime. Its local minimal discriminant exponents are

$$
\delta_q=
\begin{cases}
0,&q\nmid abc,\\
2p\,v_q(abc),&q\ne2\text{ and }q\mid abc,\\
2p\,v_2(a)-8,&q=2.
\end{cases} \tag{12.19}
$$

It has good reduction away from $abc$ and multiplicative reduction at every prime dividing $abc$. In particular it is semistable, and its global minimal discriminant is the integer in (12.18).

**Proof strategy.** At odd primes, primitivity makes exactly one root difference vanish, so $c_4$ stays a unit and the discriminant factorization gives the exact thickness. At $2$, the displayed $xy$-equation has $a_1=1$, so its $c_4$ is a unit; the division by $2^{12}$ has already removed the unique artificial weighted factor.

**Proof.** Let $q$ be odd. Because $a,b,c$ are pairwise coprime, at most one is divisible by $q$. If none is, (12.18) makes $\Delta$ a unit. If $q\mid a$, then

$$
c_4\equiv b^{2p}\not\equiv0\pmod q,
$$

so the equation is minimal and multiplicative, while (12.18) gives $\delta_q=2p\,v_q(a)$. The cases $q\mid b$ and $q\mid c$ are identical; in the last case $a^p\equiv-b^p$ and

$$
a^{2p}+a^pb^p+b^{2p}\equiv a^{2p}\not\equiv0\pmod q.
$$

At $2$, equation (12.17) has $a_1=1$. Hence $c_4$ is odd by (10.7), proving minimality. Formula (12.18) gives the last row of (12.19), which is positive because $p\,v_2(a)\geq5$. The reduced cubic is therefore nodal, so reduction is multiplicative. These cases exhaust the primes. $\square$

The tangent calculations sharpen the theorem. At an odd bad prime,

$$
\begin{array}{c|c}
q\mid a&\text{split exactly when $b$ is a square modulo $q$},\\
q\mid b&\text{split exactly when $-a$ is a square modulo $q$},\\
q\mid c&\text{split exactly when $a$ is a square modulo $q$}.
\end{array} \tag{12.20}
$$

Indeed, raising to the odd power $p$ does not change a square class. At $2$, write

$$
D=\frac{b^p-a^p-1}{4}.
$$

The tangent polynomial is $T^2+T+\overline D$. Over $\mathbf F_2$, the reduction is split exactly when $D$ is even, equivalently

$$
b\equiv1\pmod8; \tag{12.21}
$$

the alternative allowed by (12.16), $b\equiv5\pmod8$, is nonsplit.

Finally, the component and conductor information is now direct. At every bad prime the geometric fiber is $I_{\delta_q}$ and has $\delta_q$ geometric components. The geometric conductor count of Section 8.7 is one at each such prime and zero elsewhere. Thus its global support is the squarefree integer

$$
\prod_{q\mid abc}q. \tag{12.22}
$$

This is the characteristic Frey separation visible here: the minimal discriminant remembers the large multiples $2p\,v_q(abc)$, while the geometric semistable conductor count remembers each bad prime only once.

### 12.9 Conclusion

The arithmetic of an elliptic curve at a discrete valuation is the arithmetic of choosing the right integral scale. Pole orders at the marked point force the weights $2$ and $3$ on coordinates; those weights force the degrees $4$, $6$, and $12$ of $c_4,c_6$, and $\Delta$. An integral equation places the curve over the valuation ring, while a minimal equation removes every avoidable weighted dilation. What remains—the minimal discriminant ideal and the special-fiber geometry—is intrinsic.

The special fiber then turns algebra into geometry. A unit discriminant gives a smooth elliptic curve. A node gives a torus, split or nonsplit according to its tangent directions. A cusp gives an additive smooth quotient. The local group reflects the same sequence of ideas: components form the outer quotient, the smooth special fiber forms $E_0/E_1$, and the formal parameter makes every deeper layer an additive residue-field direction.

Finite extensions rescale valuations and may unlock new minimal coordinates, but good and multiplicative reduction persist, while additive reduction is the place where potential improvement occurs. The Frey-type calculation shows the practical strength of the theory: factorized root differences turn the discriminant into exact valuation data, the unit status of $c_4$ proves minimality and semistability, and the tangent cone decides splitness. Integral models therefore do more than preserve an equation modulo a prime. Once minimized, they convert a curve over a field into a precise record of its local arithmetic degeneration.
