# Nearby Cycles and Monodromy in Dimensions One and Two

## Contents

1. [Degeneration as an action](#1-degeneration-as-an-action)
   - [1.1 The missing information in the special fiber](#11-the-missing-information-in-the-special-fiber)
   - [1.2 Conventions and normalizations](#12-conventions-and-normalizations)
   - [1.3 Strictly semistable curves and surfaces](#13-strictly-semistable-curves-and-surfaces)
2. [The nearby-cycle construction](#2-the-nearby-cycle-construction)
   - [2.1 The oriented specialization space](#21-the-oriented-specialization-space)
   - [2.2 Nearby and vanishing cycles](#22-nearby-and-vanishing-cycles)
   - [2.3 Stalks, proper comparison, and base change](#23-stalks-proper-comparison-and-base-change)
   - [2.4 Duality and functoriality](#24-duality-and-functoriality)
3. [The semistable local calculation](#3-the-semistable-local-calculation)
   - [3.1 The punctured normal-crossings chart](#31-the-punctured-normal-crossings-chart)
   - [3.2 The exterior-algebra theorem](#32-the-exterior-algebra-theorem)
   - [3.3 Curves: smooth points and nodes](#33-curves-smooth-points-and-nodes)
   - [3.4 Surfaces: double curves and triple points](#34-surfaces-double-curves-and-triple-points)
   - [3.5 What fails outside strict semistability](#35-what-fails-outside-strict-semistability)
4. [Inertia: tame, wild, and finite parts](#4-inertia-tame-wild-and-finite-parts)
   - [4.1 The tame character](#41-the-tame-character)
   - [4.2 Unipotence in a strict semistable model](#42-unipotence-in-a-strict-semistable-model)
   - [4.3 Descent from a semistable extension](#43-descent-from-a-semistable-extension)
   - [4.4 Invariant cycles](#44-invariant-cycles)
5. [The monodromy operator and its filtration](#5-the-monodromy-operator-and-its-filtration)
   - [5.1 Logarithm of tame inertia](#51-logarithm-of-tame-inertia)
   - [5.2 The canonical filtration of a nilpotent operator](#52-the-canonical-filtration-of-a-nilpotent-operator)
   - [5.3 Centers, twists, and Frobenius](#53-centers-twists-and-frobenius)
   - [5.4 Integral qualifications](#54-integral-qualifications)
6. [The weight spectral sequence](#6-the-weight-spectral-sequence)
   - [6.1 Strata and the incidence operators](#61-strata-and-the-incidence-operators)
   - [6.2 The general low-dimensional formula](#62-the-general-low-dimensional-formula)
   - [6.3 Curves on the first page](#63-curves-on-the-first-page)
   - [6.4 Surfaces on the first page](#64-surfaces-on-the-first-page)
   - [6.5 Degeneration and the weight qualification](#65-degeneration-and-the-weight-qualification)
7. [Semistable curves](#7-semistable-curves)
   - [7.1 The three graded pieces of first cohomology](#71-the-three-graded-pieces-of-first-cohomology)
   - [7.2 The specialization exact sequence](#72-the-specialization-exact-sequence)
   - [7.3 The graph monodromy pairing](#73-the-graph-monodromy-pairing)
   - [7.4 Model calculations](#74-model-calculations)
8. [Picard--Lefschetz theory for curves](#8-picard--lefschetz-theory-for-curves)
   - [8.1 Thimbles and vanishing classes](#81-thimbles-and-vanishing-classes)
   - [8.2 The transvection formula](#82-the-transvection-formula)
   - [8.3 Several nodes and relations](#83-several-nodes-and-relations)
   - [8.4 Separating and nonseparating nodes](#84-separating-and-nonseparating-nodes)
9. [Strictly semistable surfaces](#9-strictly-semistable-surfaces)
   - [9.1 The five possible monodromy levels in degree two](#91-the-five-possible-monodromy-levels-in-degree-two)
   - [9.2 The dual complex at the extremes](#92-the-dual-complex-at-the-extremes)
   - [9.3 Double-curve and component terms](#93-double-curve-and-component-terms)
   - [9.4 Degree one, degree three, and duality](#94-degree-one-degree-three-and-duality)
   - [9.5 Two instructive degenerations](#95-two-instructive-degenerations)
10. [Picard--Lefschetz theory for surfaces](#10-picard--lefschetz-theory-for-surfaces)
   - [10.1 An isolated ordinary double point](#101-an-isolated-ordinary-double-point)
   - [10.2 The reflection formula](#102-the-reflection-formula)
   - [10.3 From a reflection to semistable monodromy](#103-from-a-reflection-to-semistable-monodromy)
   - [10.4 Why a double curve is different](#104-why-a-double-curve-is-different)
11. [Component pairings and geometric correspondences](#11-component-pairings-and-geometric-correspondences)
   - [11.1 Restriction and Gysin as adjoints](#111-restriction-and-gysin-as-adjoints)
   - [11.2 The curve component group](#112-the-curve-component-group)
   - [11.3 Surface intersection complexes](#113-surface-intersection-complexes)
   - [11.4 Pull--push actions](#114-pull--push-actions)
12. [Conductors and local type](#12-conductors-and-local-type)
   - [12.1 The conductor formula](#121-the-conductor-formula)
   - [12.2 Curves](#122-curves)
   - [12.3 Surfaces](#123-surfaces)
   - [12.4 Tame type, wild type, and what the conductor forgets](#124-tame-type-wild-type-and-what-the-conductor-forgets)
13. [Base change, descent, and diagnostic examples](#13-base-change-descent-and-diagnostic-examples)
   - [13.1 Ramified base change](#131-ramified-base-change)
   - [13.2 Residue extension and nonsplit strata](#132-residue-extension-and-nonsplit-strata)
   - [13.3 Good reduction and false converses](#133-good-reduction-and-false-converses)
   - [13.4 A calculation protocol](#134-a-calculation-protocol)
14. [The local memory of a degeneration](#14-the-local-memory-of-a-degeneration)
   - [14.1 The curve package](#141-the-curve-package)
   - [14.2 The surface package](#142-the-surface-package)
   - [14.3 Conclusion](#143-conclusion)

## 1. Degeneration as an action

### 1.1 The missing information in the special fiber

A smooth proper variety over the fraction field of a discrete valuation ring may have a singular special fiber. Ordinary cohomology of that special fiber remembers its components and their intersections, but it does not remember how the components were smoothed. The simplest warning is a nodal elliptic degeneration. The nodal rational special fiber has one-dimensional first cohomology, whereas the smooth elliptic generic fiber has dimension two. One class survives on the singular fiber; a second class collapses into the node. Neither the normalization nor the dual graph alone displays the action produced by circling the degeneration.

Nearby cycles solve this comparison problem by placing the generic cohomology on the special fiber while retaining the action of inertia. Vanishing cycles measure the difference between this transported object and the ordinary special-fiber coefficient. The resulting structure has three simultaneous faces:

$$
\begin{array}{c}
\text{local normal-crossings equations}\\
\text{incidence of special-fiber strata}\\
\text{inertia acting on generic cohomology}
\end{array}
\quad\longleftrightarrow\quad
\begin{array}{c}
\text{vanishing-cycle stalks}\\
\text{a spectral sequence}\\
\text{a nilpotent monodromy operator}.
\end{array}
$$

In relative dimensions one and two these objects are sparse enough to calculate. For curves, nodes, component genera, and the first homology of the dual graph give the complete rational picture in degree one. For surfaces, components, double curves, triple points, and the two-dimensional dual complex govern the five possible monodromy levels in middle cohomology. The aim of this book is to construct this package, prove its low-dimensional form, and turn it into formulas for conductors and local types.

The geometry of semistable curves, graph lattices, thicknesses, component groups, derived cohomology, base change, trace, low-dimensional duality, and the finite-image Artin--Swan formalism is assumed. We recall notation when it enters a formula, but we do not rebuild those foundations. Nearby cycles, their local semistable calculation, the passage from finite tame inertia to a nilpotent logarithm, and the resulting weight spectral sequence are proved here.

### 1.2 Conventions and normalizations

Let $R$ be a henselian discrete valuation ring with fraction field $K$, residue field $k$ of characteristic exponent $p$, and uniformizer $\pi$. Choose separable closures $\bar K/K$ and $\bar k/k$ and a specialization from the geometric generic point $\bar\eta$ to the geometric closed point $\bar s$. Write

$$
G_K=\operatorname{Gal}(\bar K/K),\qquad
I_K\subset G_K
$$

for the absolute group and inertia. Wild inertia is $P_K$, and tame inertia is $I_K/P_K$. Fix a prime $\ell\ne p$. The principal coefficient fields and rings are

$$
E=\mathbf Q_\ell,\qquad
\Lambda=\mathbf Z_\ell,\qquad
\Lambda_n=\mathbf Z/\ell^n\mathbf Z.
$$

Finite-level statements are made with $\Lambda_n$; integral statements require a normalized inverse system; linear-algebraic monodromy filtrations are over $E$ unless explicitly declared integral.

All cohomology is geometric. Thus $H^m(X_{\bar\eta},E)$ carries a continuous $G_K$-action. The Tate twist is normalized so that geometric Frobenius over $\mathbf F_q$ acts on $E(1)$ by $q^{-1}$. Whenever Frobenius eigenvalues occur, $F$ means geometric Frobenius. The monodromy operator is written as an equivariant map

$$
N:V\longrightarrow V(-1).
\tag{1.1}
$$

After suppressing the target twist, it satisfies

$$
FNF^{-1}=q^{-1}N.
\tag{1.2}
$$

Complexes are cohomologically graded. For a proper morphism $f:X\to S=\operatorname{Spec}R$, nearby cohomology satisfies

$$
R\Gamma(X_{\bar s},R\Psi_fE)
\simeq R\Gamma(X_{\bar\eta},E).
\tag{1.3}
$$

This is a global comparison theorem, not part of the definition of $R\Psi_f$. The distinction will matter for nonproper examples.

### 1.3 Strictly semistable curves and surfaces

Let $f:X\to S$ be proper and flat of relative dimension $d\in\{1,2\}$, with smooth generic fiber. It is **strictly semistable** if $X$ is regular and, étale locally at every geometric point of the special fiber, $f$ has the form

$$
\operatorname{Spec}
R[t_1,\ldots,t_{d+1}]/(t_1\cdots t_r-\pi)
\longrightarrow \operatorname{Spec}R
\tag{1.4}
$$

for some $1\le r\le d+1$, with any remaining coordinates smooth. Its special fiber

$$
Y=X_{\bar s}=\bigcup_{i\in I}Y_i
$$

is a reduced strict normal-crossings divisor; every $Y_i$ is smooth, and every multiple intersection has the expected codimension. Put

$$
Y^{(r)}=\coprod_{i_1<\cdots<i_r}
Y_{i_1}\cap\cdots\cap Y_{i_r},
\qquad Y^{(0)}=\varnothing.
\tag{1.5}
$$

Empty intersections are simply omitted. For a curve, $Y^{(1)}$ is the disjoint union of normalized components and $Y^{(2)}$ is the set of nodes. For a surface, $Y^{(2)}$ is the disjoint union of double curves and $Y^{(3)}$ is the set of triple points. There are no fourfold intersections.

Strictness is doing real work. It makes every component geometrically defined after the displayed base change and makes the local smoothing parameter have multiplicity one. A semistable model with equation $xy=\pi^a$ has the same reduced special fiber but a different integral monodromy pairing. A normal-crossings divisor with multiplicities has finite tame characters in addition to unipotent monodromy. We will return to both warnings rather than hiding them in terminology.

The definition is insensitive to mixed versus equal characteristic as long as $\ell\ne p$. Thus $R$ may be the integers of a mixed-characteristic local field or a power-series ring $k[[\pi]]$. What matters for the local calculation is the prime-to-$p$ Kummer tower around the divisor. Equal characteristic does not make wild phenomena disappear: it is strict semistability, not the shape of the coefficient field, that kills wild inertia in the calculation below.

Two global examples locate the range. A regular model of a curve with reduced nodal fiber is strictly semistable because its node equations have thickness one. A regular threefold whose special divisor is a union of smooth surfaces meeting pairwise in smooth curves and three at a time transversely is a strictly semistable surface family. By contrast, a special divisor whose three components meet along one common curve is not strict normal crossings in relative dimension two: three components should meet in codimension three in the total space, hence at isolated points in the special surface.

## 2. The nearby-cycle construction

### 2.1 The oriented specialization space

The generic and special fibers are disjoint subschemes of $X$. Consequently no ordinary restriction map can carry a sheaf directly from $X_{\bar\eta}$ to $X_{\bar s}$. What relates them is a chosen specialization: a geometric point near the special fiber together with a path from the geometric generic direction. The corresponding oriented specialization space records precisely that data.

Denote by

$$
X_{\bar\eta}\xrightarrow{\bar j}X_{\bar S}
\xleftarrow{\bar i}X_{\bar s}
$$

the generic and special directions after strict localization and geometric base change. For a bounded constructible complex $K$ on $X_{\bar\eta}$ define

$$
R\Psi_fK=\bar i^*R\bar j_*K.
\tag{2.1}
$$

The right side is a complex on $Y$, but it is not merely a complex of sheaves: changing the generic geometric point through inertia acts on it. Thus $R\Psi_fK$ carries a continuous $I_K$-action.

The stalk has a useful geometric description. If $\bar x\to Y$ is a geometric point and $X_{(\bar x)}$ is the strict localization of $X$ at $\bar x$, then

$$
(R\Psi_fK)_{\bar x}
\simeq R\Gamma\bigl((X_{(\bar x)})_{\bar\eta},K\bigr).
\tag{2.2}
$$

Nearby cycles are therefore local cohomology of the punctured smoothing near $\bar x$. Formula (2.2) is the bridge from the abstract construction to the equations $t_1\cdots t_r=\pi$.

### 2.2 Nearby and vanishing cycles

Suppose $L$ is a bounded constructible complex on $X$. Adjunction supplies a specialization morphism

$$
\operatorname{sp}:\bar i^*L
\longrightarrow R\Psi_f(\bar j^*L).
\tag{2.3}
$$

The **vanishing-cycle complex** is its cone:

$$
R\Phi_fL=\operatorname{Cone}(\operatorname{sp}).
\tag{2.4}
$$

Hence there is a distinguished triangle

$$
\bar i^*L\longrightarrow R\Psi_f\bar j^*L
\longrightarrow R\Phi_fL
\longrightarrow \bar i^*L[1].
\tag{2.5}
$$

This definition makes the conceptual role exact. Nearby cycles are what the generic coefficient looks like from the special fiber; vanishing cycles are the defect of local constancy. If $f$ is smooth near the support of a lisse coefficient, local acyclicity makes (2.3) an isomorphism, so $R\Phi_fL=0$. Conversely, vanishing of (2.4) is the derived local-acyclicity condition for $L$.

Applying hypercohomology to (2.5) gives the global specialization sequence

$$
\cdots\longrightarrow H^m(Y,\bar i^*L)
\longrightarrow H^m(Y,R\Psi\bar j^*L)
\longrightarrow H^m(Y,R\Phi L)
\longrightarrow H^{m+1}(Y,\bar i^*L)
\longrightarrow\cdots.
\tag{2.5a}
$$

When $f$ is proper, the middle nearby term is generic-fiber cohomology. The third term is therefore not simply “the classes that vanish”: its image and kernel are controlled by the adjacent specialization maps. A nonzero local vanishing-cycle sheaf can have zero contribution to a given global degree, and a global defect can be represented by a relation among many local stalks. This exact sequence is the first place where local generators meet global incidence.

For constant coefficients on a strictly semistable family, $R^0\Psi E=E_Y$ and the degree-zero specialization is an isomorphism. It follows that

$$
R^0\Phi E=0,
\qquad
R^q\Phi E\cong R^q\Psi E\quad(q>0).
\tag{2.6}
$$

This convenient equality is not a definition and need not hold for an arbitrary coefficient with nontrivial local monodromy.

### 2.3 Stalks, proper comparison, and base change

Local construction and global comparison must be kept separate. Applying hypercohomology on $Y$ gives

$$
E_2^{a,b}=H^a(Y,R^b\Psi_fK)
\Longrightarrow \mathbb H^{a+b}(Y,R\Psi_fK).
\tag{2.7}
$$

When $f$ is proper, the right side is canonically $H^{a+b}(X_{\bar\eta},K)$, producing the nearby-cycle spectral sequence for generic cohomology. Without properness, cohomology may escape through the boundary. One must then use compact support and a controlled compactification, or retain the right side of (2.7) without replacing it by generic global cohomology.

Nearby cycles commute with extension of the strictly henselian trait and with smooth change in $X$. Proper pushforward satisfies the crucial comparison

$$
R\Psi_f(Rg_{\bar\eta *}K)
\simeq Rg_{\bar s *}(R\Psi_{f\circ g}K)
\tag{2.8}
$$

when $g$ is proper and all complexes are in the bounded constructible prime-to-$p$ range. The proof compares stalks by (2.2), applies proper base change on the local generic fibers, and then glues the stalkwise isomorphisms. This identity explains why resolution, normalization of strata, and proper correspondences can be inserted into calculations.

Finite coefficient systems pass to $\Lambda$ only after the derived inverse limit. Uniform cohomological amplitude and finite stalks make the relevant towers Mittag--Leffler in the present dimensions. Tensoring the resulting perfect complex with $E$ gives the rational nearby-cycle complex used for monodromy filtrations.

### 2.4 Duality and functoriality

Nearby cycles preserve more than groups. Cup product on the generic fiber induces

$$
R\Psi K\otimes^L R\Psi L
\longrightarrow R\Psi(K\otimes^L L).
\tag{2.9}
$$

At finite level, Verdier duality on the strict-local generic fibers identifies the Verdier dual of $R\Psi K$ with nearby cycles of the generic-fiber dual. The dual on $Y$ is taken with respect to its actual dualizing complex; at a singular fiber it is not obtained by replacing that complex with a shifted constant sheaf. The identification is checked on the stalks (2.2), where it is local duality, and then glues because geometric stalks detect isomorphisms. Passing through a normalized inverse system gives the integral statement, and rationalization gives the $E$-statement. For a proper family, proper comparison and the generic trace consequently yield a perfect pairing

$$
H^m(X_{\bar\eta},E)\times
H^{2d-m}(X_{\bar\eta},E(d))\longrightarrow E
\tag{2.10}
$$

that is invariant under inertia. Consequently $N$ is skew-adjoint in the twisted sense:

$$
\langle Nx,y\rangle+\langle x,Ny\rangle=0,
\tag{2.11}
$$

after placing twists so both terms have the same target.

If $X\xleftarrow{a}Z\xrightarrow{b}X$ extends over $S$ and the pull--push $b_*a^*$ is oriented and degree-preserving in the sense of low-dimensional duality—for example, for the finite flat lci legs used below—then it acts on nearby cycles and commutes with inertia. Properness of $b$ alone does not create an untwisted pushforward: the orientation fixes its shift and twist. A correspondence existing only on the generic fiber need not act on a chosen semistable complex by its naive closure, because that closure may acquire vertical components. Those components contribute genuine restriction or Gysin maps.

## 3. The semistable local calculation

### 3.1 The punctured normal-crossings chart

Every calculation begins with one geometric point $x\in Y$. Suppose exactly $r$ components pass through it. In a strict semistable chart the equation is

$$
t_1\cdots t_r=\pi.
$$

On the geometric generic fiber all $t_i$ are nonzero. Their tame Kummer classes are not independent, because their product is the fixed parameter $\pi$. Thus the local first cohomology has $r-1$, not $r$, generators. The relation is encoded by the quotient

$$
C_x=\operatorname{coker}
\left(E\xrightarrow{1\mapsto(1,\ldots,1)}E^r\right).
\tag{3.1}
$$

Equivalently, after choosing the dual basis, one may use the kernel of the summation map. The quotient form is natural for logarithmic differentials; the kernel form is natural for cycles. They are dual, not canonically identical over an integral ring without choosing the standard pairing.

The punctured local fiber is tamely equivalent, for prime-to-$p$ cohomology, to a torus of rank $r-1$ times an acyclic polydisc. Its cohomology is therefore the exterior algebra on $C_x(-1)$. This is the decisive local fact from which both the vanishing-cycle sheaves and the global spectral sequence are built.

### 3.2 The exterior-algebra theorem

**Semistable local theorem.** Let $f:X\to S$ be strictly semistable of relative dimension $d$, let $x$ lie on exactly $r$ geometric components of $Y$, and let coefficients have order prime to $p$. Then

$$
(R^q\Psi_f\Lambda_n)_x
\cong \bigwedge^q C_{x,n}(-q),
\qquad 0\le q\le r-1,
\tag{3.2}
$$

where $C_{x,n}=\operatorname{coker}(\Lambda_n\to\Lambda_n^r)$. The stalk vanishes for $q\ge r$. These identifications respect cup product. Wild inertia acts trivially, and the action induced on each cohomology sheaf $R^q\Psi$ is trivial; nontrivial tame monodromy survives in the extension structure of the full complex.

**Proof.** By strict-local invariance, the stalk is the cohomology of the geometric generic fiber of the strict localization of the chart. The extra smooth coordinates form an étale polydisc and contribute no positive-degree cohomology. Adjoining compatible prime-to-$p$ roots of $t_1,\ldots,t_r$ gives a cofinal tame Kummer tower. Its maximal pro-$\ell$ deck group is

$$
G_x=\ker\left[
\mathbf Z_\ell(1)^r\xrightarrow{\mathrm{sum}}\mathbf Z_\ell(1)
\right],
$$

because compatible roots must be multiplied to the chosen root of $\pi$. Dualizing this exact sequence identifies the degree-one character module of $G_x$ with $C_{x,n}(-1)$; this is precisely the kernel-versus-cokernel distinction noted after (3.1). The continuous cochain complex of the free rank-$(r-1)$ pro-$\ell$ group $G_x$ is the Koszul complex on those characters. With trivial coefficients its differential is zero, so its degree-$q$ cohomology is $\bigwedge^q C_{x,n}(-q)$. This also proves vanishing above degree $r-1$ and identifies multiplication with exterior product.

When $p>1$, wild inertia is pro-$p$ and acts trivially on this prime-to-$p$ Kummer tower and its cohomology; when $p=1$, there is no wild inertia. Tame deck transformations translate chosen Kummer roots by roots of unity; they fix the corresponding degree-one Kummer classes, hence the exterior algebra that they generate. This proves the stated action on every $R^q\Psi$ as well as compatibility with cup product. $\square$

The theorem says more than a rank calculation. It fixes the degree, the twist, the product, and the source of inertia. A common error is to conclude from trivial action on every $R^q\Psi$ that inertia acts trivially on global cohomology. An action can be nontrivial on a filtered object while acting trivially on all associated graded pieces; the logarithm $N$ measures precisely that extension.

For a lisse coefficient $\mathcal L$ that extends across $X$, the same chart calculation gives

$$
(R^q\Psi\mathcal L)_x
\cong \mathcal L_x\otimes
\bigwedge^q C_x(-q).
\tag{3.2a}
$$

If the coefficient is lisse only on the generic fiber and is ramified along one of the branches, this tensor formula is false. Its local inertia complex must be combined with the toric Kummer complex. For example, a nontrivial tame character around $t_1=0$ can kill degree-zero invariants and shift the dimensions of higher stalks. Strict semistability controls the morphism; it does not make every coefficient locally constant across the boundary.

The integral version of (3.2) is free over $\Lambda_n$ in every degree. Consequently reduction from $\Lambda_{n+1}$ to $\Lambda_n$ introduces no local torsion correction. Global torsion may nevertheless arise as the cohomology of restriction and Gysin maps between free lattices. This is the source of component terms: they are failures of saturation in gluing, not torsion in the local annulus itself.

### 3.3 Curves: smooth points and nodes

For a curve only $r=1$ and $r=2$ occur. At a smooth point of $Y$, the nearby-cycle stalk is $E$ in degree zero and zero above it. At a node, (3.2) gives

$$
R^0\Psi E=E_Y,
\qquad
R^1\Psi E=\bigoplus_{e\in Y^{(2)}}E_e(-1),
\qquad
R^q\Psi E=0\quad(q\ge2).
\tag{3.3}
$$

Here $E_e$ denotes the skyscraper sheaf at the geometric node $e$. By (2.6), $R\Phi E$ has exactly the degree-one skyscraper term. Thus each node supplies one local vanishing direction, but it need not supply a nonzero global vanishing class. Relations among nodes appear only after the component incidence maps are taken into account.

For the local family $xy=\pi$, the Milnor fiber is an annulus. Its one-dimensional $H^1$ is $E(-1)$. If instead the total space is smooth over $S$, the local fiber is a disc and there is no $H^1$. This elementary contrast is the local origin of the global rank jump in a nodal elliptic degeneration.

### 3.4 Surfaces: double curves and triple points

For a surface there are three local patterns. At a point on one component, no higher nearby cycle occurs. At a point of a double curve, $r=2$ and

$$
(R^1\Psi E)_x=E(-1),
\qquad (R^q\Psi E)_x=0\quad(q\ge2).
$$

At a triple point, $r=3$ and

$$
(R^1\Psi E)_x=E(-1)^2,
\qquad
(R^2\Psi E)_x=E(-2).
\tag{3.4}
$$

The rank-two first group is generated by three branch classes subject to their sum being zero. Their exterior product gives the rank-one second group.

Globally, $R^1\Psi$ is not simply the direct sum of constant sheaves on the double curves: the three branches meeting at a triple point impose compatibility maps. Similarly, $R^2\Psi$ is supported at triple points but is tied to $R^1\Psi$ by the extension class of $R\Psi$. The weight spectral sequence is the organized form of these gluings.

A useful counterexample to point-counting is a special fiber with many double curves arranged as a tree and no triple points. Local $R^1\Phi$ is nonzero along every double curve, yet some global degrees can have $N=0$ because the restriction and Gysin maps cancel all candidate classes. Local vanishing cycles are raw generators, not the final global monodromy.

### 3.5 What fails outside strict semistability

Three nearby local equations should not be confused. The equation $xy=\pi^a$ has reduced nodal special fiber but singular total space for $a>1$; resolving it replaces one weighted edge by a chain of $a$ unit edges. Rationally the shape of monodromy is unchanged, but the integral operator is multiplied by $a$. The equation $x_1^{m_1}\cdots x_r^{m_r}=\pi$ has a normal-crossings support with multiplicities. Its inertia action can have a nontrivial finite tame semisimple part determined by the $m_i$. Finally, an arbitrary singularity may carry wild vanishing cycles and need not be described by an exterior algebra.

Strict semistability excludes all three complications: the total space is regular, component multiplicities are one, and wild inertia is trivial. Later descent statements recover finite and wild parts only by explicitly recording the extension over which strict semistability appears.

## 4. Inertia: tame, wild, and finite parts

### 4.1 The tame character

Choose compatible prime-to-$p$ roots of a uniformizer. For $\sigma\in I_K$, their ratios define the tame character

$$
t_\ell:I_K\longrightarrow\mathbf Z_\ell(1).
\tag{4.1}
$$

It kills wild inertia and projects the maximal pro-$\ell$ quotient of tame inertia isomorphically onto $\mathbf Z_\ell(1)$. A choice of compatible roots changes the coordinate on this rank-one module but not the equivariant map (1.1).

If $F$ is geometric Frobenius, then

$$
t_\ell(F\sigma F^{-1})=q^{-1}t_\ell(\sigma).
\tag{4.2}
$$

This identity forces (1.2). It also explains why a Tate twist accompanies every application of $N$: monodromy is one tame character lighter than the representation on which it acts.

### 4.2 Unipotence in a strict semistable model

**Semistable inertia theorem.** Let $X/S$ be proper and strictly semistable of relative dimension at most two. For every $m$, wild inertia acts trivially on $H^m(X_{\bar\eta},E)$ and inertia acts unipotently. There is a unique nilpotent operator $N$ such that, on an open subgroup of inertia,

$$
\rho(\sigma)=\exp\bigl(t_\ell(\sigma)N\bigr).
\tag{4.3}
$$

Moreover $N^{d+1}=0$ on all cohomology; in particular $N^2=0$ for curves and $N^3=0$ for surfaces.

**Proof.** Filter $R\Psi E$ by the Postnikov filtration. By the local theorem its only nonzero cohomology sheaves have degrees $0,\ldots,d$, wild inertia acts trivially on them, and tame inertia acts trivially on each of them. Thus $\rho(\sigma)-1$ lowers this filtration. Every product of $d+1$ such lowering operators is zero, so inertia acts unipotently and $(\rho(\sigma)-1)^{d+1}=0$. When $p>1$, the continuous image of wild inertia is at once pro-$p$ and, after choosing a stable lattice, contained in a pro-$\ell$ unipotent group; because $p\ne\ell$, that image is trivial. In residue characteristic zero wild inertia is already trivial. Proper comparison transports these conclusions to $H^m(X_{\bar\eta},E)$.

On a sufficiently small tame subgroup, $t_\ell$ identifies the pro-$\ell$ quotient with an open submodule of $\mathbf Z_\ell(1)$. The logarithm is additive on the resulting commuting unipotent operators, so $\log\rho(\sigma)=t_\ell(\sigma)N$ for one nilpotent $N$. The density of the image of $t_\ell$ gives uniqueness. Conjugating this identity by Frobenius and using (4.2) gives (1.2). Since the logarithm is a polynomial in $\rho(\sigma)-1$, the same filtration argument gives $N^{d+1}=0$. $\square$

The exponent bound is coarse in degrees away from the middle. Duality and the spectral sequence give $N^2=0$ on $H^1$ of a surface and, dually, on $H^3$. Only $H^2$ can contain a Jordan block of length three.

### 4.3 Descent from a semistable extension

A variety over $K$ may become strictly semistable only over a finite extension $L/K$. Let $I_L\subset I_K$ be the corresponding open subgroup. On $I_L$ the action has the form (4.3). The action of $I_K$ then separates into

$$
\text{a finite inertial action}\quad r|_{I_K}
\qquad\text{and}\qquad
\text{the nilpotent operator }N.
$$

For $\sigma\in I_K$, put

$$
r(\sigma)=\rho(\sigma)\exp\bigl(-t_\ell(\sigma)N\bigr).
$$

The two factors commute on inertia, and additivity of $t_\ell$ makes $r$ a representation. After shrinking to $I_L$, (4.3) shows that $r$ is trivial there, so $r(I_K)$ is finite. When $k$ is finite, extend $t_\ell$ compatibly to the Weil group with $t_\ell(F)=0$ and use the same formula for $w\in W_K$. The resulting Weil--Deligne pair $(r,N)$ satisfies

$$
r(w)Nr(w)^{-1}=|w|N,
\tag{4.4}
$$

where $|F|=q^{-1}$ for geometric Frobenius. A different compatible extension changes the presentation by the usual isomorphism but not the underlying Weil--Deligne representation. Over a general residue field, the finite inertial representation and $N$ still exist; only this Frobenius presentation is omitted.

The finite part may permute components, reverse edges, act on component cohomology, or arise from multiplicities before semistable reduction. Wild inertia can occur in this finite part. Thus potential semistability implies quasi-unipotence, not that wild inertia was already trivial over $K$.

The distinction is visible in conductors. The nilpotent term records the loss from a semistable smoothing. The finite inertial representation records descent. The Swan term records genuinely wild variation. Two representations can have the same $N$ and different wild conductors, or the same conductor and different finite tame types.

### 4.4 Invariant cycles

For a unipotent inertia action of the form (4.3),

$$
V^{I_K}=\ker N.
\tag{4.5}
$$

Indeed, if $Nv=0$, every exponential fixes $v$. Conversely, choose $\sigma$ with nonzero tame parameter sufficiently small. The polynomial $(\exp(tN)-1)/(tN)$ has constant term one and is invertible, so $\exp(tN)v=v$ implies $Nv=0$.

The local invariant-cycle morphism comes from specialization:

$$
H^m(Y,E)\longrightarrow H^m(X_{\bar\eta},E)^{I_K}.
\tag{4.6}
$$

For a proper semistable curve it is an isomorphism in degree one. In higher dimension, surjectivity is a separate local invariant-cycle theorem, not a formal consequence of nearby cycles. When that theorem is available, the kernel can still contain component classes that vanish after smoothing. The surface calculations below therefore use the $E_\infty$ filtration directly; they invoke an $E_2$ description only under the explicit degeneration hypotheses stated there.

Even for curves, (4.6) does not identify all generic cohomology. Its cokernel before taking invariants is precisely where the monodromy partner of a graph class lives.

## 5. The monodromy operator and its filtration

### 5.1 Logarithm of tame inertia

Once the action is unipotent, choose $\tau\in I_K$ whose tame parameter generates an open submodule. Then

$$
N=t_\ell(\tau)^{-1}\log\rho(\tau),
\qquad
\log(1+U)=U-\frac{U^2}{2}+\frac{U^3}{3}-\cdots.
\tag{5.1}
$$

The series is finite because $U$ is nilpotent. Independence from $\tau$ follows from additivity of the logarithm on the one-parameter unipotent group. Formula (5.1) should be viewed as recovery, not definition without hypotheses: for an action with a nontrivial finite semisimple part, one first restricts to an open subgroup on which the action is unipotent.

For a curve, $N^2=0$ and

$$
\rho(\sigma)=1+t_\ell(\sigma)N.
\tag{5.2}
$$

For a surface, $N^3=0$ and

$$
\rho(\sigma)=1+t_\ell(\sigma)N+
\frac{t_\ell(\sigma)^2}{2}N^2.
\tag{5.3}
$$

The quadratic term is the signature of a length-three Jordan block and is geometrically tied to the extreme triple-intersection terms.

### 5.2 The canonical filtration of a nilpotent operator

A nilpotent operator contains more information than its rank. Its canonical increasing monodromy filtration $L_\bullet V$, centered at zero, is characterized by

$$
N(L_aV)\subset L_{a-2}V(-1)
\tag{5.4}
$$

and isomorphisms

$$
N^a:\operatorname{gr}_a^L V
\xrightarrow{\sim}
\operatorname{gr}_{-a}^L V(-a)
\qquad(a\ge0).
\tag{5.5}
$$

Existence is elementary from Jordan blocks. For a block of length $r$, assign indices $-(r-1),-(r-3),\ldots,r-1$ along a basis on which $N$ moves downward. Direct sums give the filtration. Conversely, primitive vectors in positive graded degrees recover the initial vectors of all blocks, proving uniqueness.

For $N^2=0$ the filtration is

$$
0\subset \operatorname{im}N\subset\ker N\subset V,
\tag{5.6}
$$

placed at indices $-1,0,1$. For $N^3=0$, the five indices $-2,-1,0,1,2$ can occur. The extreme pieces are

$$
\operatorname{gr}_{-2}^L=\operatorname{im}N^2,
\qquad
\operatorname{gr}_{2}^L=V/(\ker N^2+\operatorname{im}N),
$$

and $N^2$ identifies them with the appropriate twist.

### 5.3 Centers, twists, and Frobenius

For $H^m$ it is often preferable to center the filtration at $m$:

$$
M_{m+a}V=L_aV.
\tag{5.7}
$$

Then

$$
N^a:\operatorname{gr}_{m+a}^M V
\xrightarrow{\sim}
\operatorname{gr}_{m-a}^M V(-a).
\tag{5.8}
$$

This indexing anticipates weights: in a semistable family over a finite residue field, the graded piece indexed by $w$ is expected to have Frobenius weight $w$. The assertion that the filtration delivered geometrically by strata equals the canonical filtration (5.7) is the monodromy--weight statement. In dimensions one and two, the spectral sequence supplies the candidate and reduces the statement to nondegeneracy of explicit restriction--Gysin pairings.

The Tate twist in (5.8) is indispensable. If geometric Frobenius eigenvalues on the upper piece have size corresponding to weight $m+a$, twisting the lower piece by $(-a)$ raises its weight by $2a$, so the weights match. Omitting the twist makes (5.8) incompatible with (1.2).

### 5.4 Integral qualifications

The filtration of a rational vector space is canonical. On a lattice, intersections $L_aV\cap T$ give an integral filtration, but the induced maps on graded lattices need not be isomorphisms: their finite cokernels contain arithmetic information. For curves that cokernel is governed by the graph monodromy pairing and is closely related to the component group.

There is also a denominator issue. When $N^2=0$, $N=\rho(\tau)-1$ after normalizing $t_\ell(\tau)=1$, so the operator preserves a stable lattice. When $N^3=0$, the logarithm contains $1/2$. For $\ell\ne2$ it remains integral on a suitably chosen semistable lattice; at $\ell=2$ rational monodromy is still canonical, but integral preservation needs a separate check. No integral conclusion below is inferred merely from the rational logarithm.

## 6. The weight spectral sequence

### 6.1 Strata and the incidence operators

The local exterior algebra must now be glued across $Y$. The gluing is controlled by two elementary maps between cohomology of the strata. If one drops a component from an intersection, one obtains a closed immersion between strata. Alternating sums of pullbacks give restriction maps $\rho$; alternating sums of codimension-one pushforwards give Gysin maps $\gamma$. Signs are fixed by ordering the component set $I$.

The identities

$$
\rho^2=0,\qquad \gamma^2=0,\qquad
\rho\gamma+\gamma\rho=0
\tag{6.1}
$$

follow by pairing the two orders in which components can be dropped. The last identity uses the self-intersection formula. It is the geometric analogue of cancellation in an incidence complex. Duality makes $\rho$ and $\gamma$ adjoint, up to the displayed alternating signs and Tate twists.

Filtering nearby cycles by the number of components through a point produces a spectral object whose first differential is $d_1=\rho+\gamma$. This construction is functorial for maps respecting the ordered strata; changing the order changes individual signs but gives an isomorphic spectral sequence.

### 6.2 The general low-dimensional formula

**Weight spectral sequence theorem.** Let $X/S$ be proper and strictly semistable of relative dimension $d\le2$. Then there is an inertia- and residue-Galois-equivariant spectral sequence

$$
E_1^{-r,w+r}=
\bigoplus_{k\ge\max(0,-r)}
H^{w-r-2k}\bigl(Y^{(r+2k+1)},E\bigr)(-r-k)
\Longrightarrow H^w(X_{\bar\eta},E).
\tag{6.2}
$$

Terms with meaningless intersection index or cohomological degree are zero. The differential $d_1$ is the signed sum of restriction and Gysin maps. The induced filtration is finite and stable under all arithmetic actions. Monodromy acts on the first page by identity maps between matching copies of stratum cohomology, with the necessary twists, and has bidegree $(2,-2)$ in the $(p,q)$ notation.

**Proof.** Order the components and form the alternating restriction complex of all their intersections. At a point on $s$ components, its stalk is the augmented simplex complex on those $s$ vertices. Tensoring it with the exterior-algebra description (3.2) and sorting by exterior degree gives a Koszul complex for the diagonal relation in (3.1); hence it resolves the filtered nearby-cycle complex stalkwise. Because geometric stalks detect isomorphisms, these local resolutions glue.

For every inclusion obtained by deleting one component, purity identifies the boundary in one direction with restriction and the boundary in the dual direction with the codimension-one Gysin map, including its shift by two and twist by one. Filtering this finite double complex by intersection depth gives

$$
\bigoplus_{k\ge\max(0,-r)}
H^{w-r-2k}\bigl(Y^{(r+2k+1)},E\bigr)(-r-k)
$$

in bidegree $(-r,w+r)$, which is (6.2). The simplicial sign rule and the self-intersection formula give $d_1=\rho+\gamma$ and $d_1^2=0$ as in (6.1). Only $1\le r+2k+1\le d+1$ occurs, so the filtration is finite and the spectral sequence converges strongly. Proper comparison identifies its abutment with $H^w(X_{\bar\eta},E)$.

On the local exterior algebra, the tame logarithm is contraction by the diagonal relation. In the resolved complex this is the identity from each stratum summand to its matching copy two columns to the right, with one Tate twist; it therefore has bidegree $(2,-2)$. All constructions are canonical under inertia and residue Galois. When the residue field is finite, this includes Frobenius equivariance. $\square$

Formula (6.2) fixes a frequent indexing ambiguity. The total degree is $w=(-r)+(w+r)$. A twist $(-a)$ raises Frobenius weight by $2a$ under our geometric-Frobenius convention.

### 6.3 Curves on the first page

For a curve only $Y^{(1)}$ and $Y^{(2)}$ occur. The nonzero part relevant to $H^1$ has graded pieces

$$
E_2^{1,0}=H^1(\Gamma,E),
\qquad
E_2^{0,1}=\bigoplus_i H^1(Y_i,E),
\qquad
E_2^{-1,2}=H_1(\Gamma,E)(-1),
\tag{6.3}
$$

where $\Gamma$ is the geometric dual graph. To see the outer terms, the row $q=0$ is the vertex-to-edge cochain complex

$$
H^0(Y^{(1)},E)\xrightarrow{\rho}H^0(Y^{(2)},E),
$$

whose cokernel is $H^1(\Gamma,E)$. The row $q=2$ is its dual Gysin complex

$$
H^0(Y^{(2)},E)(-1)
\xrightarrow{\gamma}H^2(Y^{(1)},E),
$$

whose kernel is $H_1(\Gamma,E)(-1)$. The middle row has no neighboring term and is the sum of the component $H^1$ groups.

No higher differential can connect these three terms in total degree one, so the curve sequence degenerates at $E_2$ without a weight argument. Degeneration gives a filtration, not a canonical direct sum. The extension between the two graph pieces is exactly where nontrivial inertia lives.

### 6.4 Surfaces on the first page

For a surface it is clearest to write $E_1^{p,q}$ by columns:

$$
\begin{array}{c|c}
p& E_1^{p,q}\\ \hline
-2&H^{q-4}(Y^{(3)},E)(-2)\\
-1&H^{q-2}(Y^{(2)},E)(-1)\\
0&H^q(Y^{(1)},E)\oplus H^{q-2}(Y^{(3)},E)(-1)\\
1&H^q(Y^{(2)},E)\\
2&H^q(Y^{(3)},E).
\end{array}
\tag{6.4}
$$

The total degree is $p+q$. The horizontal $d_1$ mixes restriction and Gysin. For middle cohomology, the five relevant positions are

$$
\begin{array}{c|c}
(p,q)&\text{term contributing before }d_1\text{-cohomology}\\ \hline
(-2,4)&H^0(Y^{(3)})(-2)\\
(-1,3)&H^1(Y^{(2)})(-1)\\
(0,2)&H^2(Y^{(1)})\oplus H^0(Y^{(3)})(-1)\\
(1,1)&H^1(Y^{(2)})\\
(2,0)&H^0(Y^{(3)}).
\end{array}
\tag{6.5}
$$

The $E_2$ groups are the cohomology of the entire horizontal rows, not of the five entries viewed diagonally. For example, $E_2^{-2,4}$ is the kernel of the Gysin map from triple points into the top cohomology of double curves. Dually, $E_2^{2,0}$ is the cokernel of the restriction map from connected components of double curves to triple points. These are the homology and cohomology of the dual complex at the two extremes.

Writing the shortest rows explicitly makes the incidence visible. The bottom row is

$$
H^0(Y^{(1)})\xrightarrow{\rho}
H^0(Y^{(2)})\xrightarrow{\rho}
H^0(Y^{(3)}),
\tag{6.5a}
$$

placed in columns $0,1,2$. The top row is its twisted dual

$$
H^0(Y^{(3)})(-2)\xrightarrow{\gamma}
H^2(Y^{(2)})(-1)\xrightarrow{\gamma}
H^4(Y^{(1)}),
\tag{6.5b}
$$

placed in columns $-2,-1,0$. Between them, the odd row containing $H^1(Y^{(2)})$ maps by Gysin to $H^3(Y^{(1)})$, while its dual row maps by restriction from $H^1(Y^{(1)})$ to $H^1(Y^{(2)})$. The middle row contains

$$
H^0(Y^{(2)})(-1)\longrightarrow
H^2(Y^{(1)})\oplus H^0(Y^{(3)})(-1)
\longrightarrow H^2(Y^{(2)}).
\tag{6.5c}
$$

The two arrows in (6.5c) contain both Gysin and restriction components. Their composite vanishes because the normal-bundle self-intersections cancel the two ways through a triple point.

The middle entry contains both component divisor classes and an extra triple-point term. Treating it as only $\bigoplus H^2(Y_i)$ loses the self-intersection correction needed for $d_1^2=0$ and for monodromy duality.

### 6.5 Degeneration and the weight qualification

Suppose $k$ is finite and every smooth proper stratum satisfies purity: $H^a$ has geometric-Frobenius weight $a$. Every term $E_1^{p,q}$ in (6.4) then has weight $q$. A differential

$$
d_r:E_r^{p,q}\longrightarrow E_r^{p+r,q-r+1}
$$

with $r\ge2$ would map a pure object of weight $q$ to one of weight $q-r+1$. Frobenius equivariance forces it to vanish. Hence the spectral sequence degenerates at $E_2$ under this purity hypothesis.

This is a proof of degeneration from purity, not a proof of purity. Over an arbitrary residue field there is no numerical weight argument. In the curve case sparsity already suffices. For surfaces, one must either assume the needed purity, prove the relevant differentials vanish geometrically, or retain the $E_\infty$ notation. A first-page display alone never licenses an $E_2$ decomposition.

Even after degeneration, the result is a filtered representation. Frobenius may split the filtration rationally when its graded eigenvalues have disjoint spectra, but no canonical splitting exists in general, and integral extensions can remain when rational eigenvalues separate.

## 7. Semistable curves

### 7.1 The three graded pieces of first cohomology

Let $C/K$ be a smooth proper geometrically connected curve with proper regular strictly semistable model $X/R$. Let $Y_i$ be the normalized geometric components and $\Gamma$ the geometric dual graph. The spectral sequence gives an increasing filtration

$$
0\subset M_0\subset M_1\subset M_2=H^1(C_{\bar K},E)
\tag{7.1}
$$

with

$$
\operatorname{gr}_0^M\cong H^1(\Gamma,E),
\qquad
\operatorname{gr}_1^M\cong\bigoplus_iH^1(Y_i,E),
\qquad
\operatorname{gr}_2^M\cong H_1(\Gamma,E)(-1).
\tag{7.2}
$$

Thus

$$
\dim H^1(C_{\bar K},E)
=2\sum_i g(Y_i)+2b_1(\Gamma).
\tag{7.3}
$$

This recovers the genus formula $g(C)=\sum_i g(Y_i)+b_1(\Gamma)$ and explains it cohomologically: every graph loop contributes a surviving special-fiber class and a vanishing partner.

Monodromy kills the component piece and induces

$$
N:\operatorname{gr}_2^M
\xrightarrow{\sim}\operatorname{gr}_0^M(-1)
\tag{7.4}
$$

rationally. Hence (7.1) is the monodromy filtration centered at one. The rank of $N$ is $b_1(\Gamma)$.

### 7.2 The specialization exact sequence

The ordinary cohomology of the nodal special fiber has the normalization sequence

$$
0\longrightarrow H^1(\Gamma,E)
\longrightarrow H^1(Y,E)
\longrightarrow\bigoplus_iH^1(Y_i,E)
\longrightarrow0.
\tag{7.5}
$$

On the generic side, $\ker N$ fits into the same extension. The specialization map therefore gives an isomorphism

$$
H^1(Y,E)\xrightarrow{\sim}
H^1(C_{\bar K},E)^{I_K}=\ker N.
\tag{7.6}
$$

One proof compares the filtrations on both sides: the graph term and component term map identically, and dimensions agree by (7.3). The theorem does not assert that the generic space equals special-fiber cohomology; its quotient by invariants has dimension $b_1(\Gamma)$.

Equivalently, there is an exact sequence

$$
0\longrightarrow H^1(Y,E)
\longrightarrow H^1(C_{\bar K},E)
\longrightarrow H_1(\Gamma,E)(-1)
\longrightarrow0,
\tag{7.7}
$$

where the last arrow is the projection to the upper graded piece. Its extension class encodes the transvections around the nodes.

### 7.3 The graph monodromy pairing

Give every edge $e$ of $\Gamma$ its thickness $n_e$; in a regular strict model $n_e=1$. On the cycle lattice

$$
H_1(\Gamma,\mathbf Z)=\ker
\bigl(\partial:\mathbf Z^{E}\to\mathbf Z^{V}\bigr)
$$

define

$$
\langle a,b\rangle_{\mathrm{mon}}
=\sum_e n_ea_eb_e.
\tag{7.8}
$$

It induces an injective map

$$
H_1(\Gamma,\mathbf Z_\ell)
\longrightarrow H^1(\Gamma,\mathbf Z_\ell).
\tag{7.9}
$$

Under (7.2), the integral map induced by $N$ is (7.9), with twist $(-1)$. Positivity of (7.8) makes it an isomorphism after tensoring with $E$, proving (7.4). Its finite cokernel is the $\ell$-primary discriminant group of the graph lattice; for the Jacobian model it is the corresponding part of the geometric component group.

This statement explains why a weighted stable model and its regular resolution give the same answer. Resolving an edge of length $n$ into $n$ unit edges preserves the cycle lattice with its total length pairing. It also explains ramified base change: replacing $\pi$ by a parameter of ramification index $e$ multiplies every edge length, and hence $N$, by $e$ before saturation.

### 7.4 Model calculations

If $Y$ is smooth, $\Gamma$ has one vertex and no edges. Then $N=0$, specialization is an isomorphism, and inertia is trivial. This is good reduction.

If $Y$ consists of two smooth components meeting at one point, $\Gamma$ is a tree. Again $b_1(\Gamma)=0$ and $N=0$, although the special fiber is reducible. The generic genus is the sum of the component genera. Reducibility by itself does not imply a positive conductor.

If two components meet at $r$ nodes, then $b_1(\Gamma)=r-1$. For unit thicknesses, $N$ has rank $r-1$ and the graph discriminant has order $r$. With thicknesses $n_1,\ldots,n_r$, the cycle lattice consists of tuples of sum zero and the discriminant changes with the $n_i$; for $r=2$ it has order $n_1+n_2$.

For example, take two elliptic components meeting at two nodes. Then the generic genus is three. The component term in (7.2) has dimension four, and the two graph terms each have dimension one. Thus $H^1$ has one length-two monodromy block and four unramified dimensions. The conductor exponent is one, not two, although two singular points are visible. The component group has order two in the unit-thickness case.

As another example, let a genus-two curve degenerate to two elliptic curves meeting at one point. The dual graph is an interval. All four dimensions of $H^1$ come from the components and $N=0$. This degeneration shows simultaneously that singular reduction need not create a conductor and that the invariant-cycle space can contain the whole generic cohomology.

If $Y$ is an irreducible rational curve with one self-node, $\Gamma$ is one vertex with one loop. Then $H^1(C_{\bar K})$ has dimension two, $N$ has rank one, and inertia is a single unipotent block. This is the prototype of multiplicative elliptic reduction.

Finally, a polygon of $m$ rational components also has $b_1=1$. Its rational monodromy type is the same single length-two block, while its integral graph pairing has value $m$ on a primitive cycle. Rational local type therefore forgets the component-group order.

## 8. Picard--Lefschetz theory for curves

### 8.1 Thimbles and vanishing classes

The spectral sequence describes graded pieces; Picard--Lefschetz theory describes the action itself. Locally at a node $xy=\pi$, a small loop in the generic annulus collapses when $\pi$ tends to zero. Its cohomological dual is a vanishing class $\delta_e\in H^1(C_{\bar K},E)$. A path filling the loop is a thimble. The boundary of the thimble is the vanishing cycle, which is why intersection with the thimble controls the change under monodromy.

Individual $\delta_e$ depend on local orientations and paths, but the rank-one operator

$$
v\longmapsto\langle v,\delta_e\rangle\delta_e
$$

does not change when $\delta_e$ is replaced by $-\delta_e$. Here the alternating cup-product pairing takes values in $E(-1)$, so the displayed operator naturally maps $H^1$ to $H^1(-1)$.

### 8.2 The transvection formula

Fix the intersection convention for which the general Picard--Lefschetz sign is

$$
\varepsilon_d=(-1)^{(d+1)(d+2)/2}
\tag{8.1}
$$

in relative dimension $d$. Thus $\varepsilon_1=-1$. For a curve degeneration with one effective nonseparating node,

$$
N(v)=-\langle v,\delta\rangle\delta,
\tag{8.2}
$$

and

$$
\rho(\sigma)v
=v-t_\ell(\sigma)\langle v,\delta\rangle\delta.
\tag{8.3}
$$

Changing the convention for the ordered intersection pairing reverses both displayed signs and no geometric conclusion changes.

**Proof.** Away from the node the family is locally acyclic, so the variation is supported in the annulus. Its vanishing group is one-dimensional, generated after choosing an orientation by the boundary $\delta$ of a thimble. The canonical map to that vanishing group evaluates a class $v$ on the thimble boundary. Local duality identifies this functional, with convention (8.1), as $v\mapsto-\langle v,\delta\rangle$. The variation map sends the chosen local generator back to $\delta$. Their composite is therefore

$$
v\longmapsto-\langle v,\delta\rangle\delta,
$$

which is (8.2). The pairing on $H^1$ is alternating, so $\langle\delta,\delta\rangle=0$ and the square of this operator is zero. The exponential in (4.3) consequently truncates after its linear term and gives (8.3). Reversing the thimble replaces both occurrences of $\delta$ by their negatives and leaves the operator unchanged. $\square$

The formula is a transvection: it fixes the hyperplane orthogonal to $\delta$ and also fixes $\delta$ itself, but it is not the identity if $\delta\ne0$.

### 8.3 Several nodes and relations

For several nodes, local classes assemble through the edge space. The correct formula is

$$
N=\beta\circ\alpha,
\tag{8.4}
$$

where

$$
\alpha:H^1(C_{\bar K},E)
\longrightarrow H_1(\Gamma,E)(-1)
$$

is the quotient in (7.7), and

$$
\beta:H_1(\Gamma,E)(-1)
\longrightarrow H^1(C_{\bar K},E)(-1)
$$

is induced by the graph monodromy pairing. In a choice of edge generators this becomes a sum of local transvections, but only cycle combinations satisfying the vertex incidence relations survive.

If the nodes have disjoint vanishing cycles, the local nilpotent operators commute and

$$
\rho(\sigma)=\prod_e
\left(1-t_\ell(\sigma)
\langle -,\delta_e\rangle\delta_e\right),
$$

with relations imposed by $\partial$. Cross-products vanish in a semistable curve, so this product equals $1+t_\ell(\sigma)N$.

### 8.4 Separating and nonseparating nodes

A node is separating if deleting its edge disconnects the dual graph. Such an edge lies in no graph cycle. Its local vanishing class is zero in global $H^1$, and its transvection is trivial. The degeneration is singular, but first cohomology is unramified at that node.

A nonseparating node lies on a graph cycle and can contribute to $N$. Yet the rank is not the number of nonseparating edges: several edges on one cycle contribute only one independent direction. The exact count is $b_1(\Gamma)$.

This provides a useful counterexample to a naive local conductor formula. Two components meeting in three points have three local nodal vanishing groups but only two independent global vanishing cycles. Summing local stalk dimensions gives three; the conductor contribution is two. The incidence relations are indispensable.

## 9. Strictly semistable surfaces

### 9.1 The five possible monodromy levels in degree two

Let $X/S$ now have relative dimension two and let $V=H^2(X_{\bar\eta},E)$. Under $E_2$-degeneration, the weight spectral sequence gives a filtration

$$
0\subset M_0\subset M_1\subset M_2
\subset M_3\subset M_4=V.
\tag{9.1}
$$

The five graded pieces are

$$
\operatorname{gr}_a^M V\cong E_2^{2-a,a}
\qquad(0\le a\le4).
\tag{9.2}
$$

Monodromy satisfies

$$
N:\operatorname{gr}_a^M\to
\operatorname{gr}_{a-2}^M(-1),
\qquad
N^2:\operatorname{gr}_4^M\to
\operatorname{gr}_0^M(-2).
\tag{9.3}
$$

If the maps in (9.3) are isomorphisms in the symmetric degrees, (9.1) is the monodromy filtration centered at two. The possible Jordan blocks then have lengths one, two, and three. Triple intersections are necessary for an extreme piece and hence for $N^2\ne0$, but their mere presence is not sufficient: the triple-point zero-cycles must survive the adjacent incidence maps.

### 9.2 The dual complex at the extremes

The dual complex $\Delta(Y)$ has a vertex for each component, an edge for each connected component of a double curve, and a two-simplex for each triple point, with the evident attaching maps. Its cochain complex begins

$$
H^0(Y^{(1)},E)
\xrightarrow{\rho}H^0(Y^{(2)},E)
\xrightarrow{\rho}H^0(Y^{(3)},E).
\tag{9.4}
$$

Therefore

$$
E_2^{2,0}\cong H^2(\Delta(Y),E).
\tag{9.5}
$$

The dual Gysin row identifies

$$
E_2^{-2,4}\cong H_2(\Delta(Y),E)(-2).
\tag{9.6}
$$

Under these identifications $N^2$ is the natural pairing from cellular homology to cellular cohomology, corrected by local intersection multiplicities. For a strict model all local simplex multiplicities are one. Rational nondegeneracy yields the extreme monodromy isomorphism.

If $\Delta(Y)$ is a tree, both extreme groups vanish. If it is a triangulated two-sphere, both are one-dimensional and a length-three block can occur. A contractible dual complex can still support nonzero $N$ through double-curve cohomology; $N^2=0$ does not imply $N=0$.

### 9.3 Double-curve and component terms

The odd graded pieces come from $H^1$ of the double curves, modulo restriction and Gysin relations. Reading the rows of (6.4) gives the exact formulas

$$
\operatorname{gr}_3^M V
=E_2^{-1,3}
=\ker\left[
H^1(Y^{(2)},E)(-1)
\xrightarrow{\gamma}H^3(Y^{(1)},E)
\right]
$$

and

$$
\operatorname{gr}_1^M V
=E_2^{1,1}
=\operatorname{coker}\left[
H^1(Y^{(1)},E)
\xrightarrow{\rho}H^1(Y^{(2)},E)
\right].
$$

There are no additional adjacent terms because $Y^{(3)}$ is zero-dimensional. Duality makes

$$
N:\operatorname{gr}_3^M
\xrightarrow{\sim}\operatorname{gr}_1^M(-1)
\tag{9.7}
$$

when the monodromy--weight property holds.

The middle piece $\operatorname{gr}_2^M$ contains classes from $H^2(Y_i)$ subject to compatibility along double curves, together with the triple-point correction $H^0(Y^{(3)})(-1)$. Its length-one, monodromy-primitive quotient is killed by $N$; the middle vectors of length-three blocks need not be. This piece contains divisor classes on components and may also contain transcendental component cohomology. The spectral sequence does not assert that it is algebraic.

An important counterexample is obtained by replacing each component with another smooth surface having the same incidence divisor but different middle cohomology. The dual complex and all local crossing equations remain unchanged, while $\operatorname{gr}_2^M$ changes. Combinatorics determines the extremes, not the whole middle cohomology.

### 9.4 Degree one, degree three, and duality

For $H^1(X_{\bar\eta},E)$, only three levels can occur, just as for a curve, although $Y^{(2)}$ now consists of curves. The extreme combinatorial terms come from the first cohomology of the dual complex, and the central terms come from $H^1(Y_i)$ with compatibility along intersections. One has $N^2=0$.

Poincaré duality identifies $H^3$ with the twisted dual of $H^1$. Consequently its monodromy filtration is the dual reflected filtration, and $\operatorname{rank}N$ is the same in degrees one and three. Degrees zero and four have trivial monodromy for a geometrically connected proper surface: they are generated by the unit and fundamental class.

Thus all semistable ramification of a proper surface is concentrated in degrees one, two, and three, with degree two carrying the only possible length-three blocks.

### 9.5 Two instructive degenerations

First let $Y=Y_1\cup Y_2$ with smooth components meeting transversely along a smooth curve $D$ and no triple points. The dual complex is an interval, so the extreme degree-two pieces vanish and $N^2=0$. Nevertheless $H^1(D)$ may survive the Gysin maps and create length-two blocks in $H^2$. If $D$ is rational and the component restriction--Gysin maps account for its entire cohomology, $N$ can vanish in degree two even though the family is singular.

Second, suppose the components and double curves form the boundary pattern of a triangulated sphere and the component and double-curve odd cohomology vanish. Then the extreme pieces are each one-dimensional. Provided the incidence pairing is nondegenerate, $H^2$ contains one length-three block. The quadratic term in (5.3) is nonzero. Counting only double curves would miss this phenomenon; it is created by their two-dimensional pattern of attachment.

A product gives a third calculation and a check on all indices. Let $\mathcal C/S$ be a semistable curve and let $D/S$ be a smooth proper curve. After resolving the product strata, the generic surface is $C\times D$. The Künneth decomposition gives

$$
H^2(C_{\bar K}\times D_{\bar K})
\cong H^2(C)\oplus
\bigl(H^1(C)\otimes H^1(D)\bigr)\oplus H^2(D).
\tag{9.8}
$$

Monodromy is zero on the outer summands and is $N_C\otimes1$ on the middle summand. Hence

$$
\operatorname{rank}N_{H^2}=2g(D)b_1(\Gamma_C),
\qquad N^2=0.
\tag{9.9}
$$

The double curves inherited from the nodes of $\mathcal C$ are copies of $D$, and their $H^1$ produces exactly the same number of length-two blocks on the spectral-sequence side. There are no essential triple-point extreme terms. This verifies that positive-genus double curves can create monodromy even when the dual complex is one-dimensional and contractible in each local piece.

## 10. Picard--Lefschetz theory for surfaces

### 10.1 An isolated ordinary double point

Strict semistable crossings are not the only controlled surface singularities. A one-parameter surface degeneration may have one isolated ordinary quadratic singularity, étale locally

$$
x_0^2+x_1^2+x_2^2=\pi
\tag{10.1}
$$

when $2$ is invertible. Its vanishing cohomology is rank one in degree two. Normalize middle cohomology by

$$
W=H^2(X_{\bar\eta},E(1)).
$$

The cup-product trace is then an $E$-valued symmetric form on $W$. The normalized vanishing class $\delta\in W$ has self-intersection

$$
\langle\delta,\delta\rangle=-2
\tag{10.2}
$$

under the orientation convention (8.1).

Unlike a curve vanishing class, $\delta$ lies in an even-degree symmetric pairing and has nonzero square. This changes a unipotent transvection into a reflection. The local monodromy is finite of order two on the vanishing line before semistable base change. Untwisting $W$ recovers the same inertia action on $H^2$; the normalization is needed only to make the pairing and formula scalar-valued.

### 10.2 The reflection formula

Since $\varepsilon_2=+1$, Picard--Lefschetz gives, for $v\in W$,

$$
T(v)=v+\langle v,\delta\rangle\delta.
\tag{10.3}
$$

In particular, (10.2) gives $T(\delta)=-\delta$, while $T$ fixes $\delta^\perp$. Thus $T$ is the orthogonal reflection in the root $\delta$.

**Proof.** Local acyclicity away from the singular point confines variation to the rank-one vanishing group generated by $\delta$. For the diagonal quadratic singularity, the vanishing thimble has boundary the middle-dimensional quadric sphere; its normal Euler number is $-2$. Purity identifies this local intersection calculation with $\langle\delta,\delta\rangle=-2$ in $W$. The canonical and variation maps are adjoint under local duality, so with $\varepsilon_2=+1$ their composite sends $v$ to $\langle v,\delta\rangle\delta$. Adding this variation to the identity gives (10.3). It sends $\delta$ to $-\delta$ and fixes $\delta^\perp$, so its square is the identity. $\square$

For several disjoint ordinary double points with mutually orthogonal vanishing classes, the monodromy is the product of their commuting reflections. If vanishing paths are changed so that the classes are not orthogonal, braid relations replace commutativity. A count of singular points alone does not determine the global reflection group.

### 10.3 From a reflection to semistable monodromy

After the quadratic base change $\pi=u^2$, the sign on the vanishing line is killed. Resolving the resulting total space produces a semistable model. The finite tame reflection has then moved into the descent datum of that model. On this rank-one vanishing line the restricted action is trivial, so the unipotent logarithm is $N=0$.

This is an essential distinction. Potential strict semistability packages the original action as a finite part $r$ together with $N$. For an isolated surface ordinary double point, $r$ can contain the quadratic character and $N=0$ on its rank-one vanishing line. For a double-curve semistable degeneration, the finite part is trivial and $N$ can be nonzero. Both are called monodromy in informal speech, but they contribute differently to local type.

In residue characteristic two, equation (10.1) and the quadratic base change need modification, and wild vanishing cycles may occur. The reflection theorem above assumes $2$ invertible and does not extend by deleting that hypothesis.

### 10.4 Why a double curve is different

A strict semistable surface near a double curve has equation $xy=\pi$ with one additional smooth coordinate. Its local vanishing cohomology is a rank-one system along the entire curve, not a skyscraper at one point. Global $H^2$ receives the cohomology of that curve through both restriction and Gysin maps. The resulting tame action is unipotent and described by $N$.

By contrast, the ordinary quadratic point has a skyscraper vanishing group in middle degree and a finite reflection. Resolving both singularities and looking only at the final reduced special fiber can obscure this difference unless multiplicities and descent are retained. Nearby cycles remember it automatically.

## 11. Component pairings and geometric correspondences

### 11.1 Restriction and Gysin as adjoints

The first differential of the weight spectral sequence is geometric, not merely combinatorial. If $i:Z\hookrightarrow W$ is a smooth divisor inclusion, restriction

$$
i^*:H^a(W,E)\to H^a(Z,E)
$$

and Gysin

$$
i_*:H^a(Z,E)\to H^{a+2}(W,E)(1)
$$

are adjoint under Poincaré duality. Alternating across the components gives $\rho$ and $\gamma$. This adjunction proves the symmetry of the $E_2$ page around the middle and makes the monodromy maps compatible with global duality.

The composite $i^*i_*$ is cup product with the normal-bundle class. At a double curve inside a component surface, these self-intersection classes supply the diagonal terms of the intersection matrix. Omitting them produces an incidence matrix with the wrong square and usually violates $d_1^2=0$.

### 11.2 The curve component group

For curves, the restriction--Gysin pairing reduces to the weighted edge-length pairing (7.8). Let

$$
\mu:H_1(\Gamma,\mathbf Z)\to H^1(\Gamma,\mathbf Z)
$$

be its adjoint map. Then

$$
\operatorname{coker}\mu
$$

is the graph discriminant group. In a proper regular semistable curve model it identifies with the geometric component group of the Jacobian's separated degree-zero model. The same map is the integral shadow of $N$ between the outer graded lattices.

This gives three interpretations of one finite group:

$$
\begin{array}{c}
\text{discriminant of the cycle lattice}\\
\text{failure of integral monodromy to be an isomorphism}\\
\text{components of the Jacobian model}.
\end{array}
$$

The identifications are equivariant under residue-field descent. At a nonsplit node, inertia or residue Galois may reverse an edge orientation, acting by $-1$ on the corresponding cycle. Passing first to an unoriented quotient graph would lose that action.

### 11.3 Surface intersection complexes

For surfaces there is no single finite graph Jacobian controlling all middle cohomology. Instead one obtains a complex of lattices built from component divisor groups, double-curve cohomology, triple-point zero-cycles, restriction, Gysin, and their intersection forms. Its rational cohomology gives the $E_2$ terms in (6.4); its torsion measures failure of the integral monodromy maps to be saturated.

At the extreme combinatorial levels this complex reduces to cellular chains and cochains of $\Delta(Y)$. In the middle it also sees the Néron--Severi lattices and primitive second cohomology of the $Y_i$. Consequently two semistable surfaces with homeomorphic dual complexes can have different integral cokernels, different conductor contributions from double curves, and different local types.

When a later application needs a finite component term, it must specify which cohomological degree and which lattice complex is meant. The curve phrase “the component group” has no automatic surface analogue.

### 11.4 Pull--push actions

Suppose a correspondence

$$
X\xleftarrow{a}Z\xrightarrow{b}X
$$

extends over $S$. Assume that its pull--push is oriented and degree-preserving—for instance, both legs are finite flat lci—and that the maps meet the semistable strata transversely. Then $b_*a^*$ acts on every $Y^{(r)}$, commutes with $\rho$, $\gamma$, $N$, and the spectral sequence, and preserves the monodromy filtration. The orientation supplies the required shift and twist; properness of $b$ by itself would not. Its transpose is adjoint under the pairings above.

If transversality fails, refined intersection multiplicities must be included. If the closure of a generic correspondence gains a vertical component, that component contributes a map on the $E_1$ page. Therefore equality of generic correspondences does not by itself imply equality of their actions on a chosen integral semistable complex.

For finite maps of semistable curves, these statements recover adjunction between pullback and norm on graph cycle lattices. For surfaces, they permit projectors to isolate a cohomological summand, provided the projector denominators are invertible in the coefficient ring. Rational splitting never guarantees an integral direct summand.

## 12. Conductors and local type

### 12.1 The conductor formula

In this chapter assume that the residue field is perfect, so the classical upper-numbering break decomposition and its integrality theorem apply. The strict semistable identities involving only $N$ do not require this added hypothesis, but the Artin--Swan packaging does.

Let $V$ be a finite-dimensional quasi-unipotent $E$-representation of $G_K$. Its Artin conductor exponent is

$$
a(V)=\dim V-\dim V^{I_K}+\operatorname{Sw}(V),
\tag{12.1}
$$

where $\operatorname{Sw}(V)$ is the Swan conductor. This normalization assigns conductor zero to an unramified representation and counts tame loss of invariants with coefficient one.

If $V$ is described after quasi-unipotent reduction by $(r,N)$, then

$$
V^{I_K}=(\ker N)^{r(I_K)},
$$

and hence

$$
a(V)=\dim V-\dim(\ker N)^{r(I_K)}+\operatorname{Sw}(r).
\tag{12.2}
$$

Indeed, invariance under the open subgroup on which $r$ is trivial is equivalent to membership in $\ker N$; on that kernel the exponential term disappears, leaving precisely invariance under the finite group $r(I_K)$. Moreover the tame character vanishes on every positive ramification group, so the wild break decomposition of $V$ is the one carried by $r$ and $\operatorname{Sw}(V)=\operatorname{Sw}(r)$. This proves (12.2). In a strict semistable model over $K$, $r|_{I_K}=1$ and $\operatorname{Sw}=0$, so

$$
a(V)=\dim V-\dim\ker N=\operatorname{rank}N.
\tag{12.3}
$$

The simplicity of (12.3) depends on both strictness and descent over the original field.

For later numerical use, let

$$
V=\bigoplus_{u\ge0}V(u)
$$

be the upper-break decomposition for the finite inertial representation, with $V(0)$ the tame part. Then

$$
\operatorname{Sw}(V)=\sum_{u>0}u\,\dim V(u).
\tag{12.3a}
$$

The sum is an integer although the breaks may be rational. Formula (12.1) follows by adding the tame codimension of invariants to this weighted wild loss. In the strict semistable case every $V(u)$ with $u>0$ is zero, explaining geometrically why no Swan term remains.

### 12.2 Curves

For a proper strictly semistable curve,

$$
a\bigl(H^1(C_{\bar K},E)\bigr)=b_1(\Gamma).
\tag{12.4}
$$

The proof combines (7.4), (4.5), and (12.1). Component genera contribute unramified middle blocks; each independent graph cycle contributes one length-two special block and one unit to the conductor.

Over a field where the model is not split, let the finite inertial part act on

$$
H^1(\Gamma,E),\qquad
\bigoplus_iH^1(Y_i,E),\qquad
H_1(\Gamma,E)(-1).
$$

Formula (12.2) then computes the conductor from its invariants and Swan term. A nonsplit multiplicative elliptic curve and a split multiplicative elliptic curve both have conductor exponent one, but their finite unramified quadratic characters and Frobenius signs distinguish the local types. The conductor is not the type.

For a weighted node, thickness changes the integral monodromy pairing but not the rational rank of $N$, so it does not change (12.4). It can change the component group. This is a clean example of arithmetic information invisible to the rational conductor.

### 12.3 Surfaces

For a proper strictly semistable surface,

$$
a(H^m)=\operatorname{rank}N_m
\qquad(0\le m\le4).
\tag{12.5}
$$

The values for $m=0,4$ are zero, and duality gives equal values for $m=1,3$. In degree two, let

$$
r_1=\operatorname{rank}N,
\qquad r_2=\operatorname{rank}N^2.
$$

If $n_j$ is the number of Jordan blocks of length $j$, then

$$
n_3=r_2,\qquad
n_2=r_1-2r_2,\qquad
n_1=\dim H^2-2r_1+r_2.
\tag{12.6}
$$

Thus the conductor $r_1$ alone does not distinguish length-three blocks from two length-two blocks. The extra invariant $r_2$, controlled by the extreme dual-complex terms, is part of the local monodromy type.

Under $E_2$-degeneration and the monodromy--weight isomorphisms, $r_2$ equals the dimension of $E_2^{-2,4}$, while the number of length-two primitive blocks is read from the primitive part of $E_2^{-1,3}$. The remaining dimension belongs to length-one blocks. This turns the low-degree spectral sequence into an explicit local-type calculation.

### 12.4 Tame type, wild type, and what the conductor forgets

The local type consists of more than the integer $a(V)$. In the present setting it includes the finite inertial representation $r|_{I_K}$, the nilpotent operator $N$, and their compatibility. Frobenius adds further unramified information. The conductor compresses all of this into the codimension of invariants plus a weighted sum of wild breaks.

Three examples show the loss. A surface reflection and a one-dimensional nontrivial tame character both have tame conductor one, but one is an orthogonal Picard--Lefschetz reflection and the other need not come from geometry of a node. A length-three unipotent block and two length-two blocks both have $\operatorname{rank}N=2$, but their $N^2$ differ. Finally, two wild representations can have the same Swan conductor while having different break decompositions and different inertia characters.

Accordingly a reliable local description reports at least

$$
\bigl(r|_{I_K},\ N,\ \operatorname{rank}N^2,\
\operatorname{Sw},\ \text{Frobenius on }(\ker N)^{r(I_K)}\bigr)
$$

in degree two. The last term controls the local Euler factor; it is not determined by the conductor.

When the residue field is finite, with geometric Frobenius $F$, the local Euler polynomial in this normalization is

$$
P(V,T)=\det\left(1-FT\mid(\ker N)^{r(I_K)}\right).
\tag{12.7}
$$

For a strict semistable curve, (7.6) computes this polynomial on $H^1(Y,E)$, but its filtration still separates graph Frobenius from component Frobenius. For a surface, it must be computed on the kernel of the explicit spectral-sequence monodromy map, not on all $H^m(Y)$. Two local representations with equal conductor and equal Jordan block sizes can still have different polynomials because Frobenius acts differently on their invariant pieces.

The alternating conductor of a proper surface is also constrained by duality. Degrees one and three have equal monodromy ranks, while zero and four contribute none. Thus the total alternating Artin conductor of the cohomology complex reduces, in the strict case, to

$$
a(H^2)-2a(H^1).
\tag{12.8}
$$

This identity is bookkeeping rather than a positivity statement; the alternating quantity can have either sign before a geometric conductor theorem relates it to singularities.

## 13. Base change, descent, and diagnostic examples

### 13.1 Ramified base change

Let $K'/K$ have ramification index $e$ and choose compatible tame parameters. Restriction gives

$$
t_{\ell,K}|_{I_{K'}}=e\,t_{\ell,K'}.
$$

Hence the monodromy operator measured with the normalized parameter of $K'$ is

$$
N_{K'}=eN_K.
\tag{13.1}
$$

This matches the geometric equation: $xy=\pi$ becomes $xy=u(\pi')^e$, so an edge acquires length $e$ before resolution. The rational monodromy filtration is unchanged because multiplying $N$ by a nonzero scalar does not change its Jordan blocks. Integral cokernels and component groups can change.

If a curve base change leaves the geometric graph and descent action unchanged and merely multiplies every edge length by $e$, then the graph pairing is multiplied by $e$. On a cycle lattice of rank $b_1(\Gamma)$ its discriminant, and hence the geometric component-group order, is multiplied by $e^{b_1(\Gamma)}$. This is the exact fixed-graph scaling law.

After normalization, resolution, or contraction of unstable chains, however, the graph or its saturated cycle lattice may change and the fixed-graph hypothesis must be checked again. The operator still scales as in (13.1), but no component-group order should be scaled before that comparison.

### 13.2 Residue extension and nonsplit strata

An unramified residue extension does not scale $N$, but it can split components, nodes, and double curves. The geometric dual graph or dual complex carries an action of the residue Galois group. Local type over the original field is obtained by descent from this action, not by taking the topology of a quotient complex.

For curves, an element can fix a geometric edge and reverse its orientation, acting by $-1$ on the associated cycle. For surfaces, it can permute the vertices of a two-simplex or reverse its orientation, changing the action on $H_2(\Delta(Y))$. Quotienting the complex first can erase stabilizers and orientation characters. The safe order is: construct the full geometric strata, form the incidence and monodromy complexes equivariantly, then take invariants or descend.

### 13.3 Good reduction and false converses

Good reduction implies $R\Phi E=0$, $N=0$, and unramified cohomology. The converse “$N=0$ implies good reduction” is false. A curve whose special fiber has two components meeting in one separating node has $N=0$ on $H^1$ but is not smooth. An isolated ordinary double point on a surface can have $N=0$ after the quadratic finite part is separated, while the original inertia still acts by a reflection.

Even trivial action on one cohomological degree need not imply smooth reduction. A rational surface degeneration may have no interesting $H^1$ while $H^2$ detects vanishing cycles. Conversely, a singular degeneration can be cohomologically invisible to a chosen projector. Reduction criteria require enough cohomology plus a geometric theorem; monodromy vanishing alone is only a necessary condition in the standard good-reduction direction.

Another false inference is that a tree-like dual complex forces all monodromy to vanish. It kills the extreme combinatorial terms, but positive-genus double curves can still create length-two blocks in surface middle cohomology.

### 13.4 A calculation protocol

A local calculation in dimension one or two is reliable when performed in the following order.

1. Pass to a finite extension on which a strict semistable model exists, but retain the finite descent group.
2. List the geometric strata $Y^{(1)},Y^{(2)}$, and, for surfaces, $Y^{(3)}$, including residue actions, orientations, and thicknesses.
3. Compute cohomology of each smooth proper stratum with its Frobenius and finite inertial actions.
4. Write the restriction and Gysin maps, including self-intersection and local multiplicities.
5. Take horizontal cohomology to obtain the $E_2$ terms; do not read them off from the diagonal entries alone.
6. Justify degeneration by dimension, purity, or a direct differential calculation.
7. Determine $N$ from the matching stratum terms and test the monodromy isomorphisms.
8. Reinsert the finite inertial action and any Swan term.
9. Compute conductor, Jordan block counts, invariant Frobenius, and integral cokernels as separate outputs.

Each stage answers a different question. Skipping from the special-fiber picture directly to a conductor discards the maps that impose global relations. Skipping descent discards tame or wild finite type. Passing immediately to rational coefficients discards component and saturation data.

## 14. The local memory of a degeneration

### 14.1 The curve package

For a proper strictly semistable curve, nearby cycles have only two nonzero cohomology sheaves: the constant degree-zero sheaf and one degree-one skyscraper at each node. The weight spectral sequence turns those local generators into three global pieces: graph cohomology, component $H^1$, and twisted graph homology. Monodromy identifies the two graph pieces through the edge-length pairing, while specialization identifies ordinary special-fiber $H^1$ with inertia invariants.

The consequences are exact and reusable:

$$
\operatorname{rank}N=b_1(\Gamma),
\qquad
a(H^1)=b_1(\Gamma)
$$

in the split strict case; the integral cokernel of $N$ is the graph discriminant and component term; separating nodes contribute no global transvection; and finite or wild descent is added through $(r,N)$ rather than concealed in the graph.

### 14.2 The surface package

For a strictly semistable surface, local nearby cycles are exterior algebras of ranks zero, one, or two according as one, two, or three components meet. Globally, the first page consists of component, double-curve, and triple-point cohomology joined by restriction and Gysin. Middle cohomology can have five monodromy levels and Jordan blocks of lengths at most three. The extreme levels are the second homology and cohomology of the dual complex; odd levels are governed by double-curve $H^1$; the middle retains component $H^2$ and triple-point corrections.

Under the stated degeneration and monodromy--weight hypotheses, these terms determine $N$, $N^2$, the Jordan block counts, and hence the tame semistable conductor. Isolated ordinary double points form a complementary local model: their middle vanishing class gives a finite reflection, not a unipotent transvection, until base change and descent separate the finite part from $N$.

### 14.3 Conclusion

A degeneration is not remembered by its reduced special fiber alone. It is remembered by the cohomology of every stratum, the maps among strata, the thickness and orientation of their incidence, and the inertia action tying the resulting graded pieces together. Nearby cycles are the object in which all of that information coexists. Vanishing cycles locate the failure of local constancy. The weight spectral sequence arranges the local data globally. The logarithm of tame inertia converts the hidden extension into a nilpotent operator, and the monodromy filtration records its exact Jordan geometry.

In dimension one this memory becomes a weighted graph pairing. In dimension two it becomes a three-level incidence geometry of components, curves, and points, with a five-step middle filtration. Picard--Lefschetz formulas show the action at its most concrete: a curve node gives a transvection, while an isolated surface double point gives a reflection. Conductors then measure only the loss of invariants and wild breaks; local type retains the finite action, the nilpotent operator, its higher ranks, and Frobenius.

The guiding discipline is therefore to preserve structure until the final numerical step. Local stalks must be glued before they are counted, $E_2$ must be justified before it is read as graded cohomology, finite descent must be restored after semistable base change, and integral lattices must be retained when component terms matter. With those distinctions in place, semistable curves and surfaces admit a precise and computable theory of specialization, monodromy, and local arithmetic.
