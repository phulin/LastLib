# Nearby Cycles and Monodromy for Semistable Curves

## Contents

[1. Degeneration as an action](#1-degeneration-as-an-action)

- [1.1 The missing information in the special fiber](#11-the-missing-information-in-the-special-fiber)
- [1.2 Conventions and normalizations](#12-conventions-and-normalizations)
- [1.3 Strictly semistable curves](#13-strictly-semistable-curves)
  [2. The nearby-cycle construction](#2-the-nearby-cycle-construction)
- [2.1 The oriented fiber site](#21-the-oriented-fiber-site)
- [2.2 Nearby and vanishing cycles](#22-nearby-and-vanishing-cycles)
- [2.3 Stalks, proper comparison, and base change](#23-stalks-proper-comparison-and-base-change)
- [2.4 Duality and functoriality](#24-duality-and-functoriality)
- [2.5 Convergence of the nearby-cycle spectral sequence](#25-convergence-of-the-nearby-cycle-spectral-sequence)
- [2.6 Inertia invariants and iterated spectral sequences](#26-inertia-invariants-and-iterated-spectral-sequences)
- [2.7 A specialization checklist](#27-a-specialization-checklist)
  [3. The semistable local calculation](#3-the-semistable-local-calculation)
- [3.1 The punctured normal-crossings chart](#31-the-punctured-normal-crossings-chart)
- [3.2 The exterior-algebra theorem](#32-the-exterior-algebra-theorem)
- [3.3 Curves: smooth points and nodes](#33-curves-smooth-points-and-nodes)
- [3.4 What fails outside strict semistability](#34-what-fails-outside-strict-semistability)
- [3.5 Tame ramified coefficients at a strict node](#35-tame-ramified-coefficients-at-a-strict-node)
- [3.6 Finite wild image before the tame complex](#36-finite-wild-image-before-the-tame-complex)
  [4. Inertia: tame, wild, and finite parts](#4-inertia-tame-wild-and-finite-parts)
- [4.1 The tame character](#41-the-tame-character)
- [4.2 Unipotence in a strict semistable model](#42-unipotence-in-a-strict-semistable-model)
- [4.3 Descent from a semistable extension](#43-descent-from-a-semistable-extension)
- [4.4 Invariant cycles](#44-invariant-cycles)
  [5. The monodromy operator and its filtration](#5-the-monodromy-operator-and-its-filtration)
- [5.1 Logarithm of tame inertia](#51-logarithm-of-tame-inertia)
- [5.2 The canonical filtration of a nilpotent operator](#52-the-canonical-filtration-of-a-nilpotent-operator)
- [5.3 Centers, twists, and Frobenius](#53-centers-twists-and-frobenius)
- [5.4 Integral qualifications](#54-integral-qualifications)
  [6. The weight spectral sequence](#6-the-weight-spectral-sequence)
- [6.1 Strata and the incidence operators](#61-strata-and-the-incidence-operators)
- [6.2 The semistable curve formula](#62-the-semistable-curve-formula)
- [6.3 Curves on the first page](#63-curves-on-the-first-page)
- [6.4 Degeneration and the weight qualification](#64-degeneration-and-the-weight-qualification)
  [7. Semistable curves](#7-semistable-curves)
- [7.1 The three graded pieces of first cohomology](#71-the-three-graded-pieces-of-first-cohomology)
- [7.2 The specialization exact sequence](#72-the-specialization-exact-sequence)
- [7.3 The graph monodromy pairing](#73-the-graph-monodromy-pairing)
- [7.4 Model calculations](#74-model-calculations)
  [8. Picard--Lefschetz theory for curves](#8-picard--lefschetz-theory-for-curves)
- [8.1 Thimbles and vanishing classes](#81-thimbles-and-vanishing-classes)
- [8.2 The transvection formula](#82-the-transvection-formula)
- [8.3 Several nodes and relations](#83-several-nodes-and-relations)
- [8.4 Separating and nonseparating nodes](#84-separating-and-nonseparating-nodes)
  [9. Component pairings and geometric correspondences](#9-component-pairings-and-geometric-correspondences)
- [9.1 Restriction and Gysin as adjoints](#91-restriction-and-gysin-as-adjoints)
- [9.2 The curve component group](#92-the-curve-component-group)
- [9.3 Pull--push actions](#93-pull--push-actions)
  [10. Conductors and local type](#10-conductors-and-local-type)
- [10.1 The conductor formula](#101-the-conductor-formula)
- [10.2 Curves](#102-curves)
- [10.3 Tame type, wild type, and what the conductor forgets](#103-tame-type-wild-type-and-what-the-conductor-forgets)
  [11. Base change, descent, and diagnostic examples](#11-base-change-descent-and-diagnostic-examples)
- [11.1 Ramified base change](#111-ramified-base-change)
- [11.2 Residue extension and nonsplit strata](#112-residue-extension-and-nonsplit-strata)
- [11.3 Good reduction and false converses](#113-good-reduction-and-false-converses)
- [11.4 A calculation protocol](#114-a-calculation-protocol)
  [12. The local memory of a degeneration](#12-the-local-memory-of-a-degeneration)
- [12.1 The curve package](#121-the-curve-package)
- [12.2 Conclusion](#122-conclusion)

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

For semistable curves these objects are sparse enough to calculate: nodes, component genera, and the first homology of the dual graph give the complete rational picture in degree one. The aim of this book is to construct that package and turn it into formulas for conductors and local types.

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

### 1.3 Strictly semistable curves

Let $f:X\to S$ be proper and flat of relative dimension one, with smooth generic fiber. It is **strictly semistable** if $X$ is regular and, étale locally at every geometric point of the special fiber, $f$ has the form

$$
\operatorname{Spec}
R[t_1,t_2]/(t_1\cdots t_r-\pi)
\longrightarrow \operatorname{Spec}R
\tag{1.4}
$$

for some $1\le r\le2$. Its special fiber

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

Empty intersections are simply omitted. Here $Y^{(1)}$ is the disjoint union of normalized components and $Y^{(2)}$ is the set of nodes; no higher intersection occurs.

Strictness is doing real work. It makes every component geometrically defined after the displayed base change and makes the local smoothing parameter have multiplicity one. A semistable model with equation $xy=\pi^a$ has the same reduced special fiber but a different integral monodromy pairing. A normal-crossings divisor with multiplicities has finite tame characters in addition to unipotent monodromy. We will return to both warnings rather than hiding them in terminology.

The definition is insensitive to mixed versus equal characteristic as long as $\ell\ne p$. Thus $R$ may be the integers of a mixed-characteristic local field or a power-series ring $k[[\pi]]$. What matters for the local calculation is the prime-to-$p$ Kummer tower around the divisor. Equal characteristic does not make wild phenomena disappear: it is strict semistability, not the shape of the coefficient field, that kills wild inertia in the calculation below.

A regular model of a curve with reduced nodal fiber is strictly semistable precisely when its node equations have thickness one. An equation $xy=\pi^a$ with $a>1$ has the same reduced nodal fiber but is not strict in this sense until the model and base are modified.

## 2. The nearby-cycle construction

### 2.1 The oriented fiber site

The generic and special fibers are disjoint subschemes of $X$. There is in particular no honest inclusion $X_{\bar\eta}\hookrightarrow X_{\bar s}$, and consequently no ordinary restriction map can carry a sheaf directly from one to the other. What relates them is a chosen specialization: a geometric point near the special fiber together with a path from the geometric generic direction. The **oriented fiber site** $X_{\overleftarrow S}$ is the site whose objects record precisely that data — a geometric point of $X$ above the special fiber, together with a specialization from the geometric generic direction — and whose topology is the one making that data descend along étale maps. It is the oriented product of $X$ with the geometric trait over $S$; the associated topos is also called the vanishing topos, since it is the ambient object on which the comparison between the two fibers becomes an actual morphism of sheaves.

There are morphisms of sites

$$
X_{\bar\eta}\xrightarrow{\bar j}X_{\overleftarrow S}
\xleftarrow{\bar i}X_{\bar s}
$$

realizing the generic and special directions after strict localization and geometric base change. Write $j_0:X_{\bar\eta}\to X$ and $i_0:X_{\bar s}\to X$ for the two ordinary fiber morphisms. The point of the construction is that the composite $\bar i^*R\bar j_*$ is meaningful and retains the inertia action, whereas $j_0^*$ and $i_0^*$ merely restrict a complex on $X$ to its two geometric fibers and remember nothing that connects them. When $L$ is a complex on $X$ itself we abbreviate $j_0^*L$ and $i_0^*L$ to $\bar j^*L$ and $\bar i^*L$; the intended functor is determined by where its argument lives, so no ambiguity arises.

For a bounded constructible complex $K$ on $X_{\bar\eta}$ define

$$
R\Psi_fK=\bar i^*R\bar j_*K.
\tag{2.1}
$$

The right side is a complex on $Y$, but it is not merely a complex of sheaves: changing the generic geometric point through inertia acts on it. Thus $R\Psi_fK$ carries a continuous $I_K$-action.

For the prime-to-$p$ torsion and $\ell$-adic coefficients fixed in Section 1.2 the inverse image $\bar i^*$ is exact, so no derived pullback is needed in (2.1). In a coefficient category where the structure sheaf varies, $\bar i^*$ must be replaced by $L\bar i^*$ and every statement below read on the cohomology sheaves of that derived pullback. We keep the notation $R\Psi_f$ in both cases.

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

This definition makes the conceptual role exact. Nearby cycles are what the generic coefficient looks like from the special fiber; vanishing cycles are the defect of local constancy. If $f$ is smooth near the support of a lisse coefficient, local acyclicity makes (2.3) an isomorphism, so $R\Phi_fL=0$.

The converse must be stated with care. For the fixed trait and the fixed specialization, vanishing of (2.4) says exactly that no local vanishing cycles occur here. Full local acyclicity is a stronger condition: it demands the corresponding vanishing after every permitted base change of the trait and at every geometric specialization, and it is not inferred from a single vanishing calculation. Chapter 11 returns to this point, where a ramified base change is precisely what exposes the difference.

Because $\bar j$ is defined over the geometric generic direction, $I_K$ acts on $R\Psi_f\bar j^*L$, and the specialization morphism (2.3) is $I_K$-equivariant when the special-fiber term carries the trivial action. Nothing at this stage asserts unipotence or produces a monodromy filtration; those are the work of Chapters 4 and 5.

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

### 2.5 Convergence of the nearby-cycle spectral sequence

The hypercohomology sequence (2.7) becomes usable only after two logically separate questions are answered: whether it converges, and whether its abutment may be replaced by generic-fiber cohomology. Neither is automatic, and conflating them is the commonest error in a specialization argument.

The second question is the one already raised at (1.3). If the comparison morphism

$$
R\Gamma(Y,R\Psi_fK)
\longrightarrow R\Gamma(X_{\bar\eta},K)
\tag{2.12}
$$

is an isomorphism, then the abutment of (2.7) is $H^{a+b}(X_{\bar\eta},K)$. This comparison is a separate geometric hypothesis, not a formal consequence of the definition of nearby cycles. A geometric application must establish it by an appropriate properness or compact-support argument before invoking the generic-fiber abutment. For proper $f$ it is exactly (1.3); Section 2.3 records what has to replace it otherwise.

The first question is settled by a finite-diagonal criterion.

**Nearby-cycle convergence theorem.** Suppose the page (2.7) has only finitely many nonzero terms on each total diagonal $a+b=m$. This holds in particular when $R\Psi_fK$ is bounded below, as it is for bounded constructible $K$ with the exact inverse image of Section 2.1. Then the nearby-cycle spectral sequence converges strongly. If in addition (2.12) is an isomorphism, it induces a finite, functorial, inertia-stable filtration on $H^m(X_{\bar\eta},K)$ whose graded pieces are the terms $E_\infty^{a,m-a}$.

**Proof.** The hypothesis makes the truncation spectral object finite along each total diagonal, and the standard finite-diagonal convergence criterion for a filtered complex, part of the derived-cohomology background assumed in Section 1.1, then gives strong convergence. In the bounded-below case $a\ge0$ and $b$ is bounded below, so a fixed equation $a+b=m$ admits only finitely many solutions. Every truncation map is compatible with the inertia action of (2.1), so each page and the limiting filtration are $I_K$-stable. Transporting the filtration across (2.12) gives the last assertion. $\square$

The sparse case is the one that governs curves. If $R^b\Psi_fK=0$ unless $b=0,1$, only two rows occur, and the sole possible nonzero higher differential is

$$
d_2:E_2^{a,1}\longrightarrow E_2^{a+2,0}.
\tag{2.13}
$$

The associated five-term exact sequence then isolates the obstruction for a global section of $R^1\Psi_fK$ to lift to a class in generic-fiber cohomology. Chapter 3 shows that constant coefficients on a strictly semistable curve fall into precisely this two-row situation, with $R^1\Psi E$ a sum of skyscrapers at the nodes; the weight spectral sequence of Chapter 6 is the refinement that keeps track of weights as well as degrees.

### 2.6 Inertia invariants and iterated spectral sequences

Taking continuous inertia cohomology after nearby cycles produces a second spectral sequence

$$
E_2^{c,d}=H^c_{\mathrm{cts}}
\bigl(I_K,H^d(Y,R\Psi_fK)\bigr)
\Longrightarrow
H^{c+d}_{\mathrm{cts}}
\bigl(I_K,R\Gamma(Y,R\Psi_fK)\bigr).
\tag{2.14}
$$

It converges under finite cohomological dimension and boundedness, both of which hold for the coefficients fixed in Section 1.2. Combining (2.14) with (2.7) means comparing two filtrations on one triple complex. One may filter first by nearby-cycle degree and then by group-cochain degree, or in the reverse order; the two totalizations agree whenever each total diagonal is finite, so the two resulting spectral sequences compute the same object.

This observation dictates the order of work in a degeneration problem. First compute the local nearby-cycle sheaves, then their cohomology on $Y$, and only then take inertia cohomology. At every step an edge map records a concrete obstruction. Collapsing the three stages into an unqualified equality loses extension data, and with integral coefficients it can also lose a derived inverse-limit term. Trivial inertia action on a page is likewise not trivial inertia action on the target, since a hidden extension may carry one.

### 2.7 A specialization checklist

A nearby-cycle calculation has four logically distinct stages, and they should not be collapsed. First, construct $R\Psi_f$ on the oriented fiber site and record its inertia action. Second, bound its cohomological amplitude; without this the local-to-global sequence may fail to converge strongly. Third, compute or compare the sheaves $R^b\Psi_fK$ on the special fiber. Fourth, justify the global comparison (2.12) between special-fiber nearby cohomology and generic-fiber cohomology, through a properness or compact-support theorem suited to the situation at hand.

Each stage answers a different question. Local acyclicity proves $R\Phi_f=0$ and identifies $\bar i^*L$ with $R\Psi_f\bar j^*L$, but says nothing by itself about global cohomology when global base change is unavailable. Properness may supply the global comparison while local singularities keep higher $R^b\Psi_f$ nonzero. A vanishing computed at one specialization is not local acyclicity, as Section 2.2 already warned.

Suppose, for illustration, that $R^b\Psi_fK$ vanishes except for $b=0,1$, that $R^1\Psi_fK$ is supported on finitely many closed points and acyclic there, and that $Y$ has cohomological dimension one. Then $H^a(Y,R^1\Psi_fK)=0$ for $a>0$ and $H^a(Y,R^0\Psi_fK)=0$ for $a>1$. No nonzero $d_2$ of the shape (2.13) is possible, so the sequence degenerates and generic cohomology receives a two-step inertia-stable filtration. Even here the extension between the two graded pieces remains to be determined; that extension is where the monodromy operator of Chapter 5 lives, and it is the reason a degeneration is not remembered by its special fiber alone.

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

**Semistable local theorem.** Let $f:X\to S$ be a strictly semistable curve, let $x$ lie on exactly $r\in\{1,2\}$ geometric components of $Y$, and let coefficients have order prime to $p$. Then

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

### 3.4 What fails outside strict semistability

Three nearby local equations should not be confused. The equation $xy=\pi^a$ has reduced nodal special fiber but singular total space for $a>1$; resolving it replaces one weighted edge by a chain of $a$ unit edges. Rationally the shape of monodromy is unchanged, but the integral operator is multiplied by $a$. The equation $x_1^{m_1}\cdots x_r^{m_r}=\pi$ has a normal-crossings support with multiplicities. Its inertia action can have a nontrivial finite tame semisimple part determined by the $m_i$. Finally, an arbitrary singularity may carry wild vanishing cycles and need not be described by an exterior algebra.

Strict semistability excludes all three complications: the total space is regular, component multiplicities are one, and wild inertia is trivial. Later descent statements recover finite and wild parts only by explicitly recording the extension over which strict semistability appears.

### 3.5 Tame ramified coefficients at a strict node

The warning after (3.2) has an exact replacement. It is useful precisely when a coefficient
system comes from residue-prime level and therefore does not extend lisse across the model.
Let $\Lambda$ be the integers in a finite extension of $\mathbf Q_\ell$. At a strict geometric
node $x$, choose an orientation of

$$
\widehat{\mathcal O}_{X,x}^{\rm sh}\simeq
\widehat{R^{\rm sh}}[[u,v]]/(uv-\pi)                       \tag{3.4}
$$

from the $u$-branch to the $v$-branch. The maximal pro-$\ell$ quotient of the geometric tame
fundamental group of the generic annulus is $\Gamma_x\simeq\mathbf Z_\ell(1)$. Choose a
topological generator $\gamma_x$; the branch orientation fixes the convention under which
reversal replaces it by $\gamma_x^{-1}$, but does not by itself trivialize
$\mathbf Z_\ell(1)$. Let $\mathcal L$ be a finite-free lisse $\Lambda$-sheaf on the
generic fiber whose geometric monodromy on this annulus is tame. After taking the exact
invariants of the prime-to-$\ell$ kernel $H_x$ on its fiber $W_x$, put
$M_x=W_x^{H_x}$ and let $T_x$ be the action of $\gamma_x$.

**Theorem 3.2 (full tame strict-node complex).** Relative to the chosen generator, there is a
canonical, functorial quasi-isomorphism

$$
(R\Psi\mathcal L)_x
\simeq
K_x(\mathcal L):=
[M_x\xrightarrow{\ T_x-1\ }M_x],                          \tag{3.5}
$$

in degrees zero and one. The second copy of $M_x$ carries the conjugation action, not a
silently chosen copy of the first. More precisely, if $g$ acts on $M_x$ by $A_g$ and

$$
g\gamma_xg^{-1}=\gamma_x^{a(g)},
\qquad a(g)\in\mathbf Z_\ell^\times,
$$

then $g$ acts in the two degrees of (3.5) by

$$
A_g,\qquad A_g[a(g)^{-1}]_{T_x},                            \tag{3.6}
$$

where $[a]_T=(T^a-1)/(T-1)$ in the completed group algebra. Consequently

$$
(R^0\Psi\mathcal L)_x=\ker(T_x-1),
\qquad
(R^1\Psi\mathcal L)_x=\operatorname{coker}(T_x-1),         \tag{3.7}
$$

with the action induced by (3.6). When $T_x=1$, the second term is
$M_x(-1)$ and (3.5) recovers (3.3). In general the cohomology in (3.7) may have
$\ell$-torsion even though both terms of the strict complex are finite free.

**Proof.** Formula (2.2) identifies the stalk with cohomology of the geometric generic annulus.
The tame $K(\pi,1)$ comparison in the prime-to-$p$ coefficient range identifies the cohomology
of this tame local system with continuous cohomology of the tame fundamental group, which is
the prime-to-$p$ procyclic Kummer group. The kernel of its
maximal pro-$\ell$ quotient acts through a finite group of order prime to $\ell$ on $W_x$:
the image is finite because $\operatorname{GL}(W_x)$ has an open pro-$\ell$ subgroup. Averaging
therefore takes its invariants exactly, producing $M_x$, and leaves the procyclic group
$\Gamma_x$. Its completed
group algebra is $\Lambda[[\Gamma_x]]\simeq\Lambda[[X]]$, with $\gamma_x-1=X$, so
$0\to\Lambda[[X]]\xrightarrow{X}\Lambda[[X]]\to\Lambda\to0$ is the length-one topologically
free augmentation resolution. Applying continuous equivariant Hom gives (3.5). Identity
$A_g[a(g)^{-1}]_{T_x}(T_x-1)=(T_x-1)A_g$ proves (3.6). This calculation is compatible at every finite coefficient quotient;
the transition maps on the two finite-free terms are surjective, so the derived inverse limit
introduces no $\varprojlim^1$ term. $\square$

Three pieces of functoriality will be used later. Consider a finite admissible map of strict
annuli of expansion index $e$. If pullback does not enlarge the prime-to-$\ell$ invariant
summand, identify that common summand with $M_x$ and choose generators so that the source action
is $T_x^e$. Pull and trace on (3.5) are then respectively

$$
(1,[e]_{T_x})
\quad\text{and}\quad
([e]_{T_x},1).                                              \tag{3.8}
$$

They are adjoint for the evaluation pairing with the contragredient coefficient after the
canonical orientation identification of the dual strict complex; this is not termwise matrix
transposition. At expansion index one the extreme maps have coefficient $1$, not the global
degree of the finite map.
Reversing the node orientation replaces the degree-one term by $-T_x^{-1}$ times itself. These
statements follow from the chain identity
$T_x^e-1=[e]_{T_x}(T_x-1)$; hence they commute with the full inertia and
residue-Galois actions in (3.6), not merely with their semisimplifications.

The invariant-summand qualification cannot be omitted. In general the target and source terms
are $W_x^{H_x}$ and $W_x^{eH_x}$, where $eH_x$ denotes the image of $H_x$ under multiplication by $e$, and
pull and trace include the corresponding inclusion and transfer;
they are not maps between two copies of one $M_x$. For example, in residue characteristic
different from two and three, over $\mathbf Z_3$ a rank-one tame character of order two has
zero prime-to-$3$ invariants, whereas its pullback by a
degree-two annular map is trivial and has rank-one invariants. The same-module display (3.8)
therefore does not apply to that map. It always applies at expansion index one, which is the
case used for the node-to-node sheets below.

The stalk complex is only one part of the normalization filtration. Let
$\nu:\widetilde Y\to Y$ be the normalization near $x$, let $i:x\hookrightarrow Y$, and let
$\mathcal C_{\rm br}$ be the full nearby-cycle complex on the two normalized branches. Write
$C_u,C_v$ for its two conductor fibers. A constructible complex has generization chain maps

$$
g_u:K_x(\mathcal L)\longrightarrow C_u,
\qquad
g_v:K_x(\mathcal L)\longrightarrow C_v.                  \tag{3.9}
$$

On the local nodal star it is recovered by the normalization--conductor homotopy fiber

$$
\operatorname{Fib}\!\left(
 R\nu_*\mathcal C_{\rm br}\oplus i_*K_x(\mathcal L)
 \xrightarrow{\ (\operatorname{res}_u,\operatorname{res}_v)-(g_u,g_v)\ }
 i_*(C_u\oplus C_v)
\right).                                                   \tag{3.10}
$$

Indeed, away from the conductor both $i_*$-terms vanish, so the fiber is
$R\nu_*\mathcal C_{\rm br}$, which is the original complex because $\nu$ is an isomorphism
there. At $x$ the displayed arrow is the split surjection

$$
C_u\oplus C_v\oplus K_x(\mathcal L)\longrightarrow C_u\oplus C_v,
\qquad (c_u,c_v,k)\longmapsto(c_u-g_u(k),c_v-g_v(k)).
$$

Its kernel is the graph of $(g_u,g_v)$ and is canonically $K_x(\mathcal L)$. Hence the natural
map from the constructible complex to (3.10) is a quasi-isomorphism on every geometric stalk.
This proves the recollement formula and shows that it is equivariant for every action preserving
the two generization maps.

This formula fixes both variance and cohomological degree. For constant coefficients,
$C_u=C_v=M_x$ and each $g_i$ is the identity in degree zero and zero in degree one. Formula
(3.10) then gives the usual normalization resolution in degree zero and the independent
node term $M_x(-1)$ in degree one. Thus the oriented cellular boundary and the ramified
coefficient differential $T_x-1$ are different arrows in one derived totalization; the latter
is not placed one degree beyond the geometric vanishing term. If a branch itself retains
monodromy, its full complex remains inside $\mathcal C_{\rm br}$ rather than being replaced by
an underived module.

With a finite tower, $C_u,C_v,K_x$ and the maps $g_i$ are formed from the actual branch and
node decomposition groups. Formula (3.10) therefore retains stabilizers rather than replacing
them by the cardinality of a flag orbit. Pull, trace, and branch reversal act on (3.10)
through (3.8) when the invariant summand is unchanged, and otherwise through the general
inclusion/transfer maps just described, together with the corresponding branch maps. Thus the
normalization filtration is functorial before taking invariants or Hecke quotients.

There is one important geometrically constant exception to the warning. Let $A$ be a finite
free $\Lambda$-algebra and let $A(\chi)$ be a rank-one $A$-module with a continuous character of
$G_K$, pulled back from the generic point of the trait. For every bounded constructible
$\mathcal K$ on $X_{\bar\eta}$ there is a canonical projection-formula isomorphism

$$
R\Psi(\mathcal K\otimes_A A(\chi))
\simeq R\Psi(\mathcal K)\otimes_A A(\chi),                 \tag{3.11}
$$

with diagonal inertia and residue-Galois action. Indeed $A(\chi)$ is constant on the
geometric generic fiber used in (2.2), and it is finite free, so tensoring commutes with that
stalk cohomology and with gluing. The projection formula makes (3.11) compatible with proper
pushforward, pull, and trace. A global ray character is of this form. A local system obtained
from a residue-prime principal-level cover is generally not: its geometric annular monodromy is
$T_x$, and (3.5), not (3.11) with $T_x$ suppressed, is the required calculation.

### 3.6 Finite wild image before the tame complex

There is one extension of Theorem 3.2 which is formal but must be stated separately. It does
not make a wild cover tame. Let $P_x$ be the wild geometric annular group and let $W$ be a
finite-free $\Lambda$-module with continuous annular action. Since $P_x$ is pro-$p$ and
$p\ne\ell$, its image in $\operatorname{GL}(W)$ is finite: an open subgroup of
$\operatorname{GL}(W)$ is pro-$\ell$, so its intersection with a pro-$p$ image is trivial.
Every finite quotient of $P_x$ has unit order in $\Lambda$. Averaging on the finite quotients,
compatibly through the inverse system, therefore gives

$$
R\Gamma(P_x,W)=W^{P_x}                                    \tag{3.12}
$$

in degree zero. The continuous Hochschild--Serre complex for

$$
1\longrightarrow P_x\longrightarrow\Pi_x
\longrightarrow\Pi_x/P_x\longrightarrow1
$$

then gives a functorial identity

$$
R\Gamma(\Pi_x,W)
\simeq R\Gamma(\Pi_x/P_x,W^{P_x}).                        \tag{3.13}
$$

Now take the exact invariants of the prime-to-$\ell$ kernel $H_x$ in the tame quotient and put

$$
M_x=(W^{P_x})^{H_x}.
$$

If $T_x$ denotes the remaining pro-$\ell$ generator, the full annular complex is

$$
R\Gamma(\Pi_x,W)
\simeq[M_x\xrightarrow{\ T_x-1\ }M_x].                  \tag{3.14}
$$

All residue-Galois actions in (3.6) preserve $W^{P_x}$ because wild inertia is
characteristic in inertia. Pull and trace preserve (3.13) provided the corresponding wild
groups and invariant summands are carried to one another; after that reduction their entries
are exactly those of (3.8), with the same invariant-summand qualification. In particular, if
$W^{P_x}=0$, the node-annular complex is zero. This does not discard $W$: its
non-wild-invariant part has no ordinary node-annular cohomology, while the full branch
complexes and their generization maps in (3.10) are still retained. Formula (3.14) by itself
does not compute a Swan conductor or identify the geometric stratum carrying a routed
summand. Thus
(3.12)--(3.14) are a derived wild-invariant reduction, not permission to call the principal
cover, its normalization, or its branch geometry tame.

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

**Semistable inertia theorem.** Let $X/S$ be a proper strictly semistable curve. For every $m$, wild inertia acts trivially on $H^m(X_{\bar\eta},E)$ and inertia acts unipotently. There is a unique nilpotent operator $N$ such that, on an open subgroup of inertia,

$$
\rho(\sigma)=\exp\bigl(t_\ell(\sigma)N\bigr).
\tag{4.3}
$$

For a semistable curve, $N^2=0$ on all cohomology.

**Proof.** Filter $R\Psi E$ by the Postnikov filtration. By the local theorem its only nonzero cohomology sheaves have degrees zero and one, wild inertia acts trivially on them, and tame inertia acts trivially on each of them. Thus $\rho(\sigma)-1$ lowers this filtration. Every product of two such lowering operators is zero, so inertia acts unipotently and $(\rho(\sigma)-1)^{d+1}=0$. When $p>1$, the continuous image of wild inertia is at once pro-$p$ and, after choosing a stable lattice, contained in a pro-$\ell$ unipotent group; because $p\ne\ell$, that image is trivial. In residue characteristic zero wild inertia is already trivial. Proper comparison transports these conclusions to $H^m(X_{\bar\eta},E)$.

On a sufficiently small tame subgroup, $t_\ell$ identifies the pro-$\ell$ quotient with an open submodule of $\mathbf Z_\ell(1)$. The logarithm is additive on the resulting commuting unipotent operators, so $\log\rho(\sigma)=t_\ell(\sigma)N$ for one nilpotent $N$. The density of the image of $t_\ell$ gives uniqueness. Conjugating this identity by Frobenius and using (4.2) gives (1.2). Since the logarithm is a polynomial in $\rho(\sigma)-1$, the same filtration argument gives $N^2=0$. $\square$

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

For a proper semistable curve it is an isomorphism in degree one. This is a theorem about the curve comparison map, not a formal consequence of the definition of nearby cycles.

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

placed at indices $-1,0,1$.

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

This indexing anticipates weights: in a semistable family over a finite residue field, the graded piece indexed by $w$ is expected to have Frobenius weight $w$. The assertion that the filtration delivered geometrically by strata equals the canonical filtration (5.7) is the monodromy--weight statement. For semistable curves, the spectral sequence supplies the candidate and reduces the statement to nondegeneracy of the graph restriction--Gysin pairing.

The Tate twist in (5.8) is indispensable. If geometric Frobenius eigenvalues on the upper piece have size corresponding to weight $m+a$, twisting the lower piece by $(-a)$ raises its weight by $2a$, so the weights match. Omitting the twist makes (5.8) incompatible with (1.2).

### 5.4 Integral qualifications

The filtration of a rational vector space is canonical. On a lattice, intersections $L_aV\cap T$ give an integral filtration, but the induced maps on graded lattices need not be isomorphisms: their finite cokernels contain arithmetic information. For curves that cokernel is governed by the graph monodromy pairing and is closely related to the component group.

There is also an integrality point. Because $N^2=0$, one has $N=\rho(\tau)-1$ after normalizing $t_\ell(\tau)=1$, so the operator preserves a stable lattice. Saturation of its image and kernel remains a separate issue, measured by the graph pairing.

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

### 6.2 The semistable curve formula

**Weight spectral sequence theorem.** Let $X/S$ be a proper strictly semistable curve. Then there is an inertia- and residue-Galois-equivariant spectral sequence

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

in bidegree $(-r,w+r)$, which is (6.2). The simplicial sign rule and the self-intersection formula give $d_1=\rho+\gamma$ and $d_1^2=0$ as in (6.1). Only $1\le r+2k+1\le2$ occurs, so the filtration is finite and the spectral sequence converges strongly. Proper comparison identifies its abutment with $H^w(X_{\bar\eta},E)$.

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

### 6.4 Degeneration and the weight qualification

Suppose $k$ is finite and every smooth proper stratum satisfies purity: $H^a$ has geometric-Frobenius weight $a$. Every term $E_1^{p,q}$ in (6.2) then has weight $q$. A differential

$$
d_r:E_r^{p,q}\longrightarrow E_r^{p+r,q-r+1}
$$

with $r\ge2$ would map a pure object of weight $q$ to one of weight $q-r+1$. Frobenius equivariance forces it to vanish. Hence the spectral sequence degenerates at $E_2$ under this purity hypothesis.

This is a proof of degeneration from purity, not a proof of purity. Over an arbitrary residue field there is no numerical weight argument. For curves the sparsity of the first page already gives the stated degeneration, but in general a first-page display alone never licenses an $E_2$ decomposition.

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

## 9. Component pairings and geometric correspondences

### 9.1 Restriction and Gysin as adjoints

The first differential of the weight spectral sequence is geometric, not merely combinatorial. If $i:Z\hookrightarrow W$ is a smooth divisor inclusion, restriction

$$
i^*:H^a(W,E)\to H^a(Z,E)
$$

and Gysin

$$
i_*:H^a(Z,E)\to H^{a+2}(W,E)(1)
$$

are adjoint under Poincaré duality. Alternating across the components gives $\rho$ and $\gamma$. This adjunction proves the symmetry of the $E_2$ page around the middle and makes the monodromy maps compatible with global duality.

The composite $i^*i_*$ is cup product with the normal-bundle class. At a node of a semistable curve, the two branch normal directions supply the local thickness in the graph pairing; omitting it gives the wrong integral monodromy map.

### 9.2 The curve component group

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

### 9.3 Pull--push actions

Suppose a correspondence

$$
X\xleftarrow{a}Z\xrightarrow{b}X
$$

extends over $S$. Assume that its pull--push is oriented and degree-preserving—for instance, both legs are finite flat lci—and that the maps meet the semistable strata transversely. Then $b_*a^*$ acts on every $Y^{(r)}$, commutes with $\rho$, $\gamma$, $N$, and the spectral sequence, and preserves the monodromy filtration. The orientation supplies the required shift and twist; properness of $b$ by itself would not. Its transpose is adjoint under the pairings above.

If transversality fails, refined intersection multiplicities must be included. If the closure of a generic correspondence gains a vertical component, that component contributes a map on the $E_1$ page. Therefore equality of generic correspondences does not by itself imply equality of their actions on a chosen integral semistable complex.

For finite maps of semistable curves, these statements recover adjunction between pullback and norm on graph cycle lattices. A rational projector can isolate a curve-cohomology summand, but it does not guarantee an integral direct summand unless its denominators are invertible and the projected lattice is saturated.

## 10. Conductors and local type

### 10.1 The conductor formula

In this chapter assume that the residue field is perfect, so the classical upper-numbering break decomposition and its integrality theorem apply. The strict semistable identities involving only $N$ do not require this added hypothesis, but the Artin--Swan packaging does.

Let $V$ be a finite-dimensional quasi-unipotent $E$-representation of $G_K$. Its Artin conductor exponent is

$$
a(V)=\dim V-\dim V^{I_K}+\operatorname{Sw}(V),
\tag{10.1}
$$

where $\operatorname{Sw}(V)$ is the Swan conductor. This normalization assigns conductor zero to an unramified representation and counts tame loss of invariants with coefficient one.

If $V$ is described after quasi-unipotent reduction by $(r,N)$, then

$$
V^{I_K}=(\ker N)^{r(I_K)},
$$

and hence

$$
a(V)=\dim V-\dim(\ker N)^{r(I_K)}+\operatorname{Sw}(r).
\tag{10.2}
$$

Indeed, invariance under the open subgroup on which $r$ is trivial is equivalent to membership in $\ker N$; on that kernel the exponential term disappears, leaving precisely invariance under the finite group $r(I_K)$. Moreover the tame character vanishes on every positive ramification group, so the wild break decomposition of $V$ is the one carried by $r$ and $\operatorname{Sw}(V)=\operatorname{Sw}(r)$. This proves (10.2). In a strict semistable model over $K$, $r|_{I_K}=1$ and $\operatorname{Sw}=0$, so

$$
a(V)=\dim V-\dim\ker N=\operatorname{rank}N.
\tag{10.3}
$$

The simplicity of (10.3) depends on both strictness and descent over the original field.

For later numerical use, let

$$
V=\bigoplus_{u\ge0}V(u)
$$

be the upper-break decomposition for the finite inertial representation, with $V(0)$ the tame part. Then

$$
\operatorname{Sw}(V)=\sum_{u>0}u\,\dim V(u).
\tag{10.3a}
$$

The sum is an integer although the breaks may be rational. Formula (10.1) follows by adding the tame codimension of invariants to this weighted wild loss. In the strict semistable case every $V(u)$ with $u>0$ is zero, explaining geometrically why no Swan term remains.

### 10.2 Curves

For a proper strictly semistable curve,

$$
a\bigl(H^1(C_{\bar K},E)\bigr)=b_1(\Gamma).
\tag{10.4}
$$

The proof combines (7.4), (4.5), and (10.1). Component genera contribute unramified middle blocks; each independent graph cycle contributes one length-two special block and one unit to the conductor.

Over a field where the model is not split, let the finite inertial part act on

$$
H^1(\Gamma,E),\qquad
\bigoplus_iH^1(Y_i,E),\qquad
H_1(\Gamma,E)(-1).
$$

Formula (10.2) then computes the conductor from its invariants and Swan term. A nonsplit multiplicative elliptic curve and a split multiplicative elliptic curve both have conductor exponent one, but their finite unramified quadratic characters and Frobenius signs distinguish the local types. The conductor is not the type.

For a weighted node, thickness changes the integral monodromy pairing but not the rational rank of $N$, so it does not change (10.4). It can change the component group. This is a clean example of arithmetic information invisible to the rational conductor.

### 10.3 Tame type, wild type, and what the conductor forgets

The local type consists of more than the integer $a(V)$. In the present setting it includes the finite inertial representation $r|_{I_K}$, the nilpotent operator $N$, and their compatibility. Frobenius adds further unramified information. The conductor compresses all of this into the codimension of invariants plus a weighted sum of wild breaks.

Two examples show the loss. Split and nonsplit multiplicative curve degenerations can have the same conductor exponent while differing by a finite quadratic character and Frobenius sign. Two wild representations can have the same Swan conductor while having different break decompositions and inertia characters.

Accordingly a reliable local description reports at least

$$
\bigl(r|_{I_K},\ N,\
\operatorname{Sw},\ \text{Frobenius on }(\ker N)^{r(I_K)}\bigr).
$$

The last term controls the local Euler factor; it is not determined by the conductor.

When the residue field is finite, with geometric Frobenius $F$, the local Euler polynomial in this normalization is

$$
P(V,T)=\det\left(1-FT\mid(\ker N)^{r(I_K)}\right).
\tag{10.7}
$$

For a strict semistable curve, (7.6) computes this polynomial on $H^1(Y,E)$, but its filtration still separates graph Frobenius from component Frobenius. Two local representations with equal conductor and equal Jordan block sizes can still have different polynomials because Frobenius acts differently on their invariant pieces.

## 11. Base change, descent, and diagnostic examples

### 11.1 Ramified base change

Let $K'/K$ have ramification index $e$ and choose compatible tame parameters. Restriction gives

$$
t_{\ell,K}|_{I_{K'}}=e\,t_{\ell,K'}.
$$

Hence the monodromy operator measured with the normalized parameter of $K'$ is

$$
N_{K'}=eN_K.
\tag{11.1}
$$

This matches the geometric equation: $xy=\pi$ becomes $xy=u(\pi')^e$, so an edge acquires length $e$ before resolution. The rational monodromy filtration is unchanged because multiplying $N$ by a nonzero scalar does not change its Jordan blocks. Integral cokernels and component groups can change.

If a curve base change leaves the geometric graph and descent action unchanged and merely multiplies every edge length by $e$, then the graph pairing is multiplied by $e$. On a cycle lattice of rank $b_1(\Gamma)$ its discriminant, and hence the geometric component-group order, is multiplied by $e^{b_1(\Gamma)}$. This is the exact fixed-graph scaling law.

After normalization, resolution, or contraction of unstable chains, however, the graph or its saturated cycle lattice may change and the fixed-graph hypothesis must be checked again. The operator still scales as in (11.1), but no component-group order should be scaled before that comparison.

### 11.2 Residue extension and nonsplit strata

An unramified residue extension does not scale $N$, but it can split components and nodes. The geometric dual graph carries an action of the residue Galois group. Local type over the original field is obtained by descent from this action, not by taking the topology of a quotient complex.

An element can fix a geometric edge and reverse its orientation, acting by $-1$ on the associated cycle. Quotienting the graph first can erase stabilizers and orientation characters. The safe order is: construct the full geometric strata, form the incidence and monodromy complexes equivariantly, then take invariants or descend.

### 11.3 Good reduction and false converses

Good reduction implies $R\Phi E=0$, $N=0$, and unramified cohomology. The converse “$N=0$ implies good reduction” is false: a curve whose special fiber has two components meeting in one separating node has $N=0$ on $H^1$ but is not smooth. Even trivial action on a chosen cohomological summand need not imply smooth reduction. Reduction criteria require enough cohomology plus a geometric theorem; monodromy vanishing alone is only a necessary condition in the standard good-reduction direction.

### 11.4 A calculation protocol

The four stages of Section 2.7 apply to any nearby-cycle calculation. For a semistable curve they refine into the following order, which is the one to follow in practice.

1. Pass to a finite extension on which a strict semistable model exists, but retain the finite descent group.
2. List the geometric strata $Y^{(1)}$ and $Y^{(2)}$, including residue actions, edge orientations, and thicknesses.
3. Compute cohomology of each smooth proper stratum with its Frobenius and finite inertial actions.
4. Write the restriction and Gysin maps, including self-intersection and local multiplicities.
5. Take horizontal cohomology to obtain the $E_2$ terms; do not read them off from the diagonal entries alone.
6. Justify degeneration by dimension, purity, or a direct differential calculation.
7. Determine $N$ from the matching stratum terms and test the monodromy isomorphisms.
8. Reinsert the finite inertial action and any Swan term.
9. Compute conductor, Jordan block counts, invariant Frobenius, and integral cokernels as separate outputs.

Each stage answers a different question. Skipping from the special-fiber picture directly to a conductor discards the maps that impose global relations. Skipping descent discards tame or wild finite type. Passing immediately to rational coefficients discards component and saturation data.

## 12. The local memory of a degeneration

### 12.1 The curve package

For a proper strictly semistable curve, nearby cycles have only two nonzero cohomology sheaves: the constant degree-zero sheaf and one degree-one skyscraper at each node. The weight spectral sequence turns those local generators into three global pieces: graph cohomology, component $H^1$, and twisted graph homology. Monodromy identifies the two graph pieces through the edge-length pairing, while specialization identifies ordinary special-fiber $H^1$ with inertia invariants.

The consequences are exact and reusable:

$$
\operatorname{rank}N=b_1(\Gamma),
\qquad
a(H^1)=b_1(\Gamma)
$$

in the split strict case; the integral cokernel of $N$ is the graph discriminant and component term; separating nodes contribute no global transvection; and finite or wild descent is added through $(r,N)$ rather than concealed in the graph.

### 12.2 Conclusion

A degeneration is not remembered by its reduced special fiber alone. It is remembered by the cohomology of every stratum, the maps among strata, the thickness and orientation of their incidence, and the inertia action tying the resulting graded pieces together. Nearby cycles are the object in which all of that information coexists. Vanishing cycles locate the failure of local constancy. The weight spectral sequence arranges the local data globally. The logarithm of tame inertia converts the hidden extension into a nilpotent operator, and the monodromy filtration records its exact Jordan geometry.

For a curve this memory becomes a weighted graph pairing, and the Picard--Lefschetz formula makes a node act by a transvection. Conductors then measure only the loss of invariants and wild breaks; local type retains the finite action, the nilpotent operator, and Frobenius.

The guiding discipline is therefore to preserve structure until the final numerical step. Local stalks must be glued before they are counted, $E_2$ must be justified before it is read as graded cohomology, finite descent must be restored after semistable base change, and integral lattices must be retained when component terms matter. With those distinctions in place, semistable curves admit a precise and computable theory of specialization, monodromy, and local arithmetic.
